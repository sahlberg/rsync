/*
 * Incremental transfers using the Linux dm-era target (--era).
 *
 * For a source file on a filesystem that sits (directly or through
 * partition, linear or crypt layers) on a dm-era device, work out which
 * byte ranges may have changed since the destination was last synced.
 *
 * Each destination file carries an xattr (ERA_XATTR).  The first record,
 * "<era> <time> <device-id>", names a line of the source device's log:
 * every source write the destination lacks was made in that era or a later
 * one.  A second record names the destination era device and the era after
 * which a write on that device means something else changed the copy.  The
 * receiver removes the xattr before changing a file, stores the source
 * record the sender gives once the file is complete, and appends a new
 * destination record at the end of the run, after one more snapshot, so
 * rsync's own destination writes are older than the recorded era.
 *
 * Each era device gets a log, /var/lib/rsync/era/<device-id>, of
 * "<era> <time>" lines.  Every metadata snapshot we take starts a new era,
 * which is appended to the log.  Only logged eras are recorded in, or
 * accepted from, the xattr, so deleting the log invalidates them all.  The
 * log file is also flock()ed while the snapshot is held, since dm-era
 * allows only one metadata snapshot per device.
 *
 * The era metadata is read with era_invalidate (thin-provisioning-tools).
 * It is a hard requirement: without it --era cannot work.
 *
 * Copyright (C) 2026 Ronnie Sahlberg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License along
 * with this program; if not, visit the http://fsf.org website.
 */

#include "rsync.h"
#include "ifuncs.h"

#ifdef SUPPORT_ERA
#include <sys/ioctl.h>
#include <sys/file.h>
#include <sys/sysmacros.h>
#include <linux/fs.h>
#include <linux/fiemap.h>
#include <linux/dm-ioctl.h>
#include <sys/xattr.h>

#define SECTOR		512ULL
#define LOG_DIR		"/var/lib/rsync/era"
#define LOCK_TIMEOUT	600	/* seconds to wait for another run */
#define SNAP_WAIT	10	/* seconds to wait for someone else's snapshot */
#define MTIME_MARGIN	1	/* seconds; covers coarse kernel timestamps */
#define MAX_ERAS	16

static NORETURN void era_fatal(int code, const char *fmt, ...) __attribute__((format(printf, 2, 3)));

static void *era_alloc(size_t n, size_t sz)
{
	void *p = calloc(n ? n : 1, sz);

	if (!p)
		out_of_memory("era");
	return p;
}

static double era_now(void)
{
	struct timespec ts;

	clock_gettime(CLOCK_REALTIME, &ts);
	return ts.tv_sec + ts.tv_nsec / 1e9;
}

/* ------------------------------------------------------------------ */
/* device-mapper ioctls                                                */
/* ------------------------------------------------------------------ */

static int dm_fd = -1;

/* fatal_on_fail is for the sender. The destination side skips detection
 * when device-mapper cannot be opened (not root, or no dm). */
static int dm_ensure(int fatal_on_fail)
{
	if (dm_fd >= 0)
		return 0;
	if ((dm_fd = open("/dev/mapper/control", O_RDWR | O_CLOEXEC)) >= 0)
		return 0;
	if (fatal_on_fail)
		era_fatal(RERR_UNSUPPORTED, "--era: cannot open /dev/mapper/control: %s (the sender must run as root)",
			  strerror(errno));
	return -1;
}

static struct dm_ioctl *dm_call(unsigned long cmd, dev_t dev, uint32_t flags,
				const void *payload, size_t plen)
{
	size_t size = 16384 + plen;

	if (dm_ensure(1) < 0)
		return NULL;
	for (;;) {
		struct dm_ioctl *io = era_alloc(1, size);

		io->version[0] = DM_VERSION_MAJOR;
		io->data_size = size;
		io->data_start = sizeof *io;
		/* the kernel decodes this with huge_decode_dev() */
		io->dev = (minor(dev) & 0xff) | ((uint64_t)major(dev) << 8) |
			  ((uint64_t)(minor(dev) & ~0xffU) << 12);
		io->flags = flags;
		if (payload)
			memcpy((char *)io + io->data_start, payload, plen);
		if (ioctl(dm_fd, cmd, io) < 0) {
			int e = errno;

			free(io);
			errno = e;
			return NULL;
		}
		if (!(io->flags & DM_BUFFER_FULL_FLAG))
			return io;
		free(io);
		size *= 4;
	}
}

struct dm_tgt {
	uint64_t start, len;
	char type[DM_MAX_TYPE_NAME + 1];
	char *params;
};

struct dm_table {
	dev_t dev;
	char id[DM_UUID_LEN + DM_NAME_LEN + 8];
	int n;
	struct dm_tgt *t;
};

/* table=1: the table lines; table=0: the status lines */
static struct dm_table *dm_get_table(dev_t dev, int table)
{
	struct dm_ioctl *io = dm_call(DM_TABLE_STATUS, dev, table ? DM_STATUS_TABLE_FLAG : 0, NULL, 0);
	struct dm_table *tab;
	char *base;
	uint32_t off = 0;
	int i;

	if (!io)
		return NULL;
	if (!(io->flags & DM_ACTIVE_PRESENT_FLAG)) {
		free(io);
		return NULL;
	}
	tab = era_alloc(1, sizeof *tab);
	tab->dev = dev;
	if (io->uuid[0])
		snprintf(tab->id, sizeof tab->id, "uuid-%s", io->uuid);
	else
		snprintf(tab->id, sizeof tab->id, "name-%s", io->name);
	tab->n = io->target_count;
	tab->t = era_alloc(tab->n + 1, sizeof *tab->t);
	base = (char *)io + io->data_start;
	for (i = 0; i < tab->n; i++) {
		struct dm_target_spec *sp = (struct dm_target_spec *)(base + off);

		tab->t[i].start = sp->sector_start;
		tab->t[i].len = sp->length;
		memcpy(tab->t[i].type, sp->target_type, DM_MAX_TYPE_NAME);
		tab->t[i].params = strdup((char *)(sp + 1));
		off = sp->next;
	}
	free(io);
	return tab;
}

static void dm_free_table(struct dm_table *tab)
{
	int i;

	if (!tab)
		return;
	for (i = 0; i < tab->n; i++)
		free(tab->t[i].params);
	free(tab->t);
	free(tab);
}

static int dm_message(dev_t dev, const char *msg)
{
	size_t plen = sizeof (struct dm_target_msg) + strlen(msg) + 1;
	struct dm_target_msg *m = era_alloc(1, plen);
	struct dm_ioctl *io;

	strcpy(m->message, msg);
	io = dm_call(DM_TARGET_MSG, dev, 0, m, plen);
	free(m);
	if (!io)
		return -1;
	free(io);
	return 0;
}

/* Cached table lines, keyed by device. */
static struct dm_table *get_table(dev_t dev)
{
	static struct dm_table *cache[64];
	static int n;
	int i;

	for (i = 0; i < n; i++)
		if (cache[i]->dev == dev)
			return cache[i];
	if (n == 64)
		return NULL;
	return (cache[n] = dm_get_table(dev, 1)) ? cache[n++] : NULL;
}

/* ------------------------------------------------------------------ */
/* era devices                                                         */
/* ------------------------------------------------------------------ */

struct era_bitmap {
	uint64_t since_era;	/* blocks written in an era >= this are set */
	double snap_time;	/* the syncfs before the snapshot started here */
	char new_stamp[64];	/* "<era> <time>": the era the snapshot started */
	uint64_t *bits;
};

struct era_dev {
	dev_t dev;		/* the era dm device */
	dev_t meta;		/* its metadata device */
	uint64_t block_sectors;
	uint64_t nr_blocks;
	char id[DM_UUID_LEN + DM_NAME_LEN + 8];
	char log[MAXPATHLEN];
	char last_stamp[64];	/* "<era> <time>" logged by the latest era_cycle */
	int end_stamped;	/* cleanup has rolled this device for the final watermark */
	int lock_fd;
	int nbm;
	struct era_bitmap bm[8];
};

static struct era_dev *eras[MAX_ERAS];
static int n_eras;
static struct era_dev *snap_era;	/* holds a metadata snapshot right now */
static pid_t child_pid;

static struct era_dev *get_era(dev_t dev, struct dm_table *tab, const char *params)
{
	unsigned mma, mmi;
	unsigned long long bs;
	struct era_dev *e;
	uint64_t sectors = 0;
	char *p;
	int i;

	for (i = 0; i < n_eras; i++)
		if (eras[i]->dev == dev)
			return eras[i];
	if (sscanf(params, "%u:%u %*u:%*u %llu", &mma, &mmi, &bs) != 3 || !bs || n_eras == MAX_ERAS)
		return NULL;
	e = era_alloc(1, sizeof *e);
	e->dev = dev;
	e->meta = makedev(mma, mmi);
	e->block_sectors = bs;
	for (i = 0; i < tab->n; i++)
		sectors += tab->t[i].len;
	e->nr_blocks = (sectors + bs - 1) / bs;
	e->lock_fd = -1;
	strlcpy(e->id, tab->id, sizeof e->id);
	for (p = e->id; *p; p++)
		if (*p == '/')
			*p = '_';
	snprintf(e->log, sizeof e->log, LOG_DIR "/%s", e->id);
	return eras[n_eras++] = e;
}

/* Walk state for map_range(). */
struct walk {
	struct era_dev *era;	/* the era device reached */
	const char *err;
	/* per-piece processing (optional) */
	struct era_ranges *dirty;
	struct era_bitmap *bm;
	OFF_T lend;
};

static void on_piece(struct walk *w, uint64_t sector, uint64_t nsect, OFF_T logical);

static int sysfs_read(dev_t dev, const char *attr, char *buf, size_t len)
{
	char path[128];
	FILE *f;
	int ok;

	snprintf(path, sizeof path, "/sys/dev/block/%u:%u/%s", major(dev), minor(dev), attr);
	if (!(f = fopen(path, "r")))
		return 0;
	ok = fgets(buf, len, f) != NULL;
	fclose(f);
	return ok;
}

/*
 * Map [sector, sector+nsect) on dev down to the era device, through
 * partitions and linear/crypt targets, calling on_piece() for each piece
 * if w->dirty is set.  Returns 0, or -1 with w->err set.
 */
static int map_range(struct walk *w, dev_t dev, uint64_t sector, uint64_t nsect,
		     OFF_T logical, int depth)
{
	struct dm_table *tab;
	char buf[64];

	if (depth > 16)
		return w->err = "device stack too deep", -1;

	if (!sysfs_read(dev, "dm/name", buf, sizeof buf)) {
		unsigned ma, mi;

		/* a partition: continue on the parent disk */
		if (sysfs_read(dev, "partition", buf, sizeof buf)
		 && sysfs_read(dev, "start", buf, sizeof buf)) {
			uint64_t start = strtoull(buf, NULL, 10);

			if (sysfs_read(dev, "../dev", buf, sizeof buf)
			 && sscanf(buf, "%u:%u", &ma, &mi) == 2)
				return map_range(w, makedev(ma, mi), sector + start, nsect, logical, depth + 1);
		}
		return w->err = "not on a dm-era device", -1;
	}

	if (!(tab = get_table(dev)))
		return w->err = "cannot read device-mapper table", -1;

	while (nsect) {
		struct dm_tgt *t = NULL;
		uint64_t off, n;
		unsigned ma, mi;
		unsigned long long lower;
		int i;

		for (i = 0; i < tab->n && !t; i++) {
			if (sector >= tab->t[i].start && sector < tab->t[i].start + tab->t[i].len)
				t = &tab->t[i];
		}
		if (!t)
			return w->err = "sector outside device-mapper table", -1;
		off = sector - t->start;
		n = t->len - off < nsect ? t->len - off : nsect;

		if (strcmp(t->type, "era") == 0) {
			struct era_dev *e = get_era(dev, tab, t->params);

			if (!e)
				return w->err = "cannot parse era table", -1;
			if (w->era && w->era != e)
				return w->err = "file spans more than one dm-era device", -1;
			w->era = e;
			/* dm-era numbers blocks by device-relative sector */
			if (w->dirty)
				on_piece(w, sector, n, logical);
		} else if ((strcmp(t->type, "linear") == 0
			 && sscanf(t->params, "%u:%u %llu", &ma, &mi, &lower) == 3)
			|| (strcmp(t->type, "crypt") == 0
			 && sscanf(t->params, "%*s %*s %*s %u:%u %llu", &ma, &mi, &lower) == 3)) {
			if (map_range(w, makedev(ma, mi), lower + off, n, logical, depth + 1) < 0)
				return -1;
		} else
			return w->err = "unsupported device-mapper target", -1;
		sector += n;
		nsect -= n;
		logical += n * SECTOR;
	}
	return 0;
}

/* The era device under a filesystem, or NULL with *why set. */
static struct era_dev *era_for_dev(dev_t dev, const char **why)
{
	static struct { dev_t dev; struct era_dev *era; const char *why; } cache[64];
	static int n;
	struct walk w;
	int i;

	for (i = 0; i < n; i++) {
		if (cache[i].dev == dev) {
			*why = cache[i].why;
			return cache[i].era;
		}
	}
	memset(&w, 0, sizeof w);
	if (major(dev) == 0)
		w.err = "filesystem has no single backing block device";
	else
		map_range(&w, dev, 0, 1, 0, 0);
	if (w.err)
		w.era = NULL;
	if (n < 64) {
		cache[n].dev = dev;
		cache[n].era = w.era;
		cache[n++].why = w.err;
	}
	*why = w.err;
	return w.era;
}

/* Current era and held snapshot (0 = none) from the status line. */
static uint32_t era_status(struct era_dev *e, uint64_t *snap)
{
	struct dm_table *tab = dm_get_table(e->dev, 0);
	unsigned cur;
	char s[32];

	if (!tab || tab->n != 1
	 || sscanf(tab->t[0].params, "%*u %*u/%*u %u %31s", &cur, s) != 2)
		era_fatal(RERR_FILEIO, "--era: cannot read status of era device %s", e->id);
	dm_free_table(tab);
	if (snap)
		*snap = strcmp(s, "-") ? strtoull(s, NULL, 10) : 0;
	return cur;
}

/* ------------------------------------------------------------------ */
/* per-device log + lock, snapshot, era_invalidate                     */
/* ------------------------------------------------------------------ */

static void era_lock(struct era_dev *e)
{
	double give_up = era_now() + LOCK_TIMEOUT;

	mkdir("/var/lib/rsync", 0755);
	mkdir(LOG_DIR, 0700);
	if ((e->lock_fd = open(e->log, O_RDWR | O_CREAT | O_APPEND | O_CLOEXEC, 0600)) < 0)
		era_fatal(RERR_FILEIO, "--era: cannot open %s: %s", e->log, strerror(errno));
	while (flock(e->lock_fd, LOCK_EX | LOCK_NB) < 0) {
		if (errno != EWOULDBLOCK)
			era_fatal(RERR_FILEIO, "--era: flock %s: %s", e->log, strerror(errno));
		if (era_now() > give_up)
			era_fatal(RERR_TIMEOUT, "--era: timed out waiting for another run on era device %s", e->id);
		if (DEBUG_GTE(DELTASUM, 1))
			rprintf(FINFO, "era: waiting for another run on %s\n", e->id);
		sleep(1);
	}
}

static void era_unlock(struct era_dev *e)
{
	close(e->lock_fd);
	e->lock_fd = -1;
}

/*
 * Whether the log has the line `want` ("<era> <time>").  An era number alone
 * is not enough: after the era metadata (and so the log) is recreated, era
 * numbers start over.  Also sets newest (if not NULL) to the newest line,
 * or "" if there is none.
 */
static int log_scan(struct era_dev *e, const char *want, char *newest)
{
	FILE *f = fopen(e->log, "r");
	unsigned long long era, best = 0;
	uint32_t cur = era_status(e, NULL);
	char when[32], line[64];
	int found = 0;

	if (newest)
		*newest = '\0';
	if (!f)
		return 0;
	while (fscanf(f, "%llu %31s", &era, when) == 2) {
		if (era > cur) {
			fclose(f);
			era_fatal(RERR_FILEIO, "--era: %s mentions era %llu but %s is at era %u: the era "
				  "metadata was recreated; remove the log", e->log, era, e->id, cur);
		}
		snprintf(line, sizeof line, "%llu %s", era, when);
		if (want && strcmp(line, want) == 0)
			found = 1;
		if (newest && era > best) {
			best = era;
			strlcpy(newest, line, sizeof line);
		}
	}
	fclose(f);
	return found;
}

static void snap_take(struct era_dev *e)
{
	double give_up = era_now() + SNAP_WAIT;
	uint64_t held;

	/* We hold the lock, so a held snapshot is not another run's: it is
	 * another tool's (wait a little) or left by a crashed run. */
	for (;;) {
		era_status(e, &held);
		if (!held && dm_message(e->dev, "take_metadata_snap") == 0)
			break;
		if (!held && errno != EINVAL)
			era_fatal(RERR_FILEIO, "--era: take_metadata_snap on %s: %s", e->id, strerror(errno));
		if (era_now() > give_up)
			era_fatal(RERR_FILEIO, "--era: era device %s has a metadata snapshot held that is not "
				  "ours: another tool is using it, or a previous run crashed.  If it is stale, "
				  "release it with 'dmsetup message <device> 0 drop_metadata_snap'", e->id);
		usleep(200000);
	}
	snap_era = e;
}

static void snap_drop(void)
{
	if (child_pid > 0) {
		int status;

		kill(child_pid, SIGKILL);
		wait_process(child_pid, &status, 0);
		child_pid = 0;
	}
	if (snap_era && dm_message(snap_era->dev, "drop_metadata_snap") < 0)
		rsyserr(FERROR, errno, "--era: drop_metadata_snap on %s", snap_era->id);
	snap_era = NULL;
}

static const char *era_invalidate_path(void)
{
	static const char *dirs[] = { "/usr/sbin", "/sbin", "/usr/bin", "/bin", NULL };
	static char path[64];
	int i;

	for (i = 0; dirs[i]; i++) {
		snprintf(path, sizeof path, "%s/era_invalidate", dirs[i]);
		if (access(path, X_OK) == 0)
			return path;
	}
	return NULL;
}

/*
 * Set bm->bits for every era block written in an era >= since, using the
 * held snapshot.  era_invalidate prints (range ends are exclusive):
 *   <blocks>
 *     <block block="9"/>
 *     <range begin="100" end="108"/>
 *   </blocks>
 */
static void read_dirty_blocks(struct era_dev *e, struct era_bitmap *bm, uint64_t since)
{
	const char *tool = era_invalidate_path();
	char meta[32], arg[32], line[256];
	int pfd[2], status;
	FILE *f;

	if (!tool)
		era_fatal(RERR_UNSUPPORTED, "--era: era_invalidate not found");
	snprintf(meta, sizeof meta, "/dev/block/%u:%u", major(e->meta), minor(e->meta));
	snprintf(arg, sizeof arg, "%llu", (unsigned long long)since);
	if (pipe(pfd) < 0 || (child_pid = fork()) < 0)
		era_fatal(RERR_IPC, "--era: pipe/fork: %s", strerror(errno));
	if (child_pid == 0) {
		close(pfd[0]);
		dup2(pfd[1], STDOUT_FILENO);
		execl(tool, tool, "--metadata-snapshot", "--written-since", arg, meta, (char *)NULL);
		_exit(127);
	}
	close(pfd[1]);
	if (!(f = fdopen(pfd[0], "r")))
		era_fatal(RERR_IPC, "--era: fdopen: %s", strerror(errno));
	while (fgets(line, sizeof line, f)) {
		unsigned long long a, b;

		if (sscanf(line, " <block block=\"%llu\"", &a) == 1)
			b = a + 1;
		else if (sscanf(line, " <range begin=\"%llu\" end=\"%llu\"", &a, &b) != 2)
			continue;
		if (a >= b || b > e->nr_blocks) {
			fclose(f);
			era_fatal(RERR_FILEIO, "--era: era_invalidate reported bad block range %llu-%llu", a, b);
		}
		for (; a < b; a++)
			bm->bits[a / 64] |= 1ULL << (a % 64);
	}
	fclose(f);
	if (wait_process(child_pid, &status, 0) != child_pid)
		status = -1;
	child_pid = 0;
	if (!WIFEXITED(status) || WEXITSTATUS(status))
		era_fatal(RERR_FILEIO, "--era: era_invalidate failed on %s (status %d)", e->id, status);
}

/*
 * One cycle: syncfs, snapshot (which starts a new era; log it), read the
 * blocks written since `since` (0: just log), drop the snapshot.
 */
static struct era_bitmap *era_cycle(struct era_dev *e, int fd, uint64_t since)
{
	struct era_bitmap *bm = NULL;
	double t;
	uint32_t cur;
	char buf[64];
	int n;

	if (since) {
		if (e->nbm == (int)(sizeof e->bm / sizeof e->bm[0]))
			return NULL;
		bm = &e->bm[e->nbm];
	}
	era_lock(e);
	/* era only sees blocks that reached the device */
	t = era_now();
	if (syncfs(fd) < 0)
		era_fatal(RERR_FILEIO, "--era: syncfs: %s", strerror(errno));
	snap_take(e);
	cur = era_status(e, NULL);
	n = snprintf(buf, sizeof buf, "%u %.9f\n", cur, era_now()) - 1;
	buf[n++] = '\n';
	if (write(e->lock_fd, buf, n) != n || fsync(e->lock_fd) < 0)
		era_fatal(RERR_FILEIO, "--era: cannot write %s: %s", e->log, strerror(errno));
	memcpy(e->last_stamp, buf, n - 1);
	e->last_stamp[n - 1] = '\0';
	if (bm) {
		bm->since_era = since;
		bm->snap_time = t;
		memcpy(bm->new_stamp, buf, n - 1);
		bm->new_stamp[n - 1] = '\0';
		bm->bits = era_alloc((e->nr_blocks + 63) / 64, sizeof *bm->bits);
		read_dirty_blocks(e, bm, since);
		e->nbm++;
	}
	snap_drop();
	era_unlock(e);
	if (DEBUG_GTE(DELTASUM, 1))
		rprintf(FINFO, "era: %s: snapshot, now era %u%s\n", e->id, cur, bm ? ", read dirty blocks" : "");
	return bm;
}

/*
 * A bitmap of the blocks written since era `since`.  Files carry different
 * eras, and each new bitmap costs a snapshot, so once there are as many as
 * we keep, use the one from the newest older era instead: it is a superset.
 */
static struct era_bitmap *get_bitmap(struct era_dev *e, int fd, uint64_t since)
{
	struct era_bitmap *bm, *best = NULL;
	int i;

	for (i = 0; i < e->nbm; i++) {
		if (e->bm[i].since_era == since)
			return &e->bm[i];
		if (e->bm[i].since_era < since && (!best || e->bm[i].since_era > best->since_era))
			best = &e->bm[i];
	}
	if ((bm = era_cycle(e, fd, since)) != NULL)
		return bm;
	return best;
}

/* ------------------------------------------------------------------ */
/* file ranges                                                         */
/* ------------------------------------------------------------------ */

static void on_piece(struct walk *w, uint64_t sector, uint64_t nsect, OFF_T logical)
{
	uint64_t bs = w->era->block_sectors, s = sector, end = sector + nsect;

	while (s < end) {
		uint64_t b = s / bs;
		uint64_t e = (b + 1) * bs < end ? (b + 1) * bs : end;
		OFF_T lo = logical + (OFF_T)(s - sector) * SECTOR;

		if (b >= w->era->nr_blocks || (w->bm->bits[b / 64] >> (b % 64)) & 1) {
			OFF_T len = (OFF_T)(e - s) * SECTOR;

			if (lo < w->lend)
				era_add_range(w->dirty, lo, MIN(len, w->lend - lo));
		}
		s = e;
	}
}

/* Extents we cannot reason about, or that may share blocks (reflink). */
#define ALWAYS_DIRTY (FIEMAP_EXTENT_UNKNOWN | FIEMAP_EXTENT_DELALLOC | FIEMAP_EXTENT_ENCODED \
		    | FIEMAP_EXTENT_DATA_ENCRYPTED | FIEMAP_EXTENT_NOT_ALIGNED \
		    | FIEMAP_EXTENT_DATA_INLINE | FIEMAP_EXTENT_DATA_TAIL | FIEMAP_EXTENT_SHARED \
		    | FIEMAP_EXTENT_UNWRITTEN)

/* Map fd's extents through bm. holes: also mark holes, as the source side
 * does, because a hole in the source must replace destination bytes. */
static const char *extents_to_dirty(int fd, OFF_T size, dev_t dev, struct era_dev *e,
				     struct era_bitmap *bm, struct era_ranges *dirty, int holes)
{
	enum { NEXT = 256 };
	struct fiemap *fm;
	OFF_T pos = 0;
	int last = 0;

	fm = era_alloc(1, sizeof *fm + NEXT * sizeof (struct fiemap_extent));
	while (!last && pos < size) {
		unsigned i;

		memset(fm, 0, sizeof *fm);
		fm->fm_start = pos;
		fm->fm_length = size - pos;
		fm->fm_flags = FIEMAP_FLAG_SYNC;
		fm->fm_extent_count = NEXT;
		if (ioctl(fd, FS_IOC_FIEMAP, fm) < 0) {
			free(fm);
			return "FIEMAP not supported";
		}
		if (fm->fm_mapped_extents == 0)
			break;
		for (i = 0; i < fm->fm_mapped_extents; i++) {
			struct fiemap_extent *fe = &fm->fm_extents[i];
			OFF_T ls = MAX((OFF_T)fe->fe_logical, pos);
			OFF_T le = MIN((OFF_T)(fe->fe_logical + fe->fe_length), size);
			OFF_T phys = fe->fe_physical + (ls - fe->fe_logical);

			last = fe->fe_flags & FIEMAP_EXTENT_LAST;
			if (ls >= le)
				continue;
			if (holes)
				era_add_range(dirty, pos, ls - pos);
			if ((fe->fe_flags & ALWAYS_DIRTY) || phys % SECTOR)
				era_add_range(dirty, ls, le - ls);
			else {
				struct walk w;

				memset(&w, 0, sizeof w);
				w.era = e;
				w.dirty = dirty;
				w.bm = bm;
				w.lend = le;
				if (map_range(&w, dev, phys / SECTOR,
					      (le - ls + SECTOR - 1) / SECTOR, ls, 0) < 0) {
					free(fm);
					return w.err;
				}
			}
			pos = le;
		}
		if (fm->fm_mapped_extents < NEXT)
			break;
	}
	if (holes)
		era_add_range(dirty, pos, size - pos);
	free(fm);
	return NULL;
}

/*
 * Fill *dirty with the sorted byte ranges of the open file fd that may
 * differ from the destination, whose ERA_XATTR is `state`.  Holes count as
 * dirty.  mtime is the file-list mtime.  Returns NULL, sets new_state to the
 * source record of the destination's next ERA_XATTR, and sets *mtime_ok to
 * whether the destination may be given that mtime; or returns the reason the
 * file must use the normal algorithm.  Only the first record of state is the
 * source watermark.
 */
const char *era_file_ranges(int fd, STRUCT_STAT *st, time_t mtime, uint32 mtime_nsec,
			    const char *state, struct era_ranges *dirty, char *new_state,
			    int *mtime_ok)
{
	struct era_bitmap *bm;
	struct era_dev *e;
	const char *why;
	unsigned long long since;
	char when[32], stamp[64], id[ERA_STATE_LEN];

	dirty->n = 0;
	if (!S_ISREG(st->st_mode))
		return "not a regular file";
	if (!(e = era_for_dev(st->st_dev, &why)))
		return why;
	if (sscanf(state, "%llu %31s %335s", &since, when, id) != 3 || !since || strcmp(id, e->id) != 0)
		return "destination was last synced from a different era device";
	snprintf(stamp, sizeof stamp, "%llu %s", since, when);
	if (!log_scan(e, stamp, NULL))
		return "destination's era is not in the era log";
	if (!(bm = get_bitmap(e, fd, since)))
		return "too many different reference eras";
	/* Writes that reached the device after the snapshot are not in the
	 * bitmap, but are in its new era or later, which is what the
	 * destination will record.  If the file-list mtime may include such a
	 * write, the destination must get an mtime the next run's quick check
	 * sees as different, or that run could skip the file. */
	*mtime_ok = mtime + mtime_nsec / 1e9 < bm->snap_time - MTIME_MARGIN;
	if ((why = extents_to_dirty(fd, st->st_size, st->st_dev, e, bm, dirty, 1)) != NULL)
		return why;
	/* The clean blocks are as of the snapshot; later writes are in its
	 * new era or after.  The destination era is appended on the receiver
	 * after its own writes. */
	snprintf(new_state, ERA_STATE_LEN, "%s %s", bm->new_stamp, e->id);
	return NULL;
}

/*
 * The ERA_XATTR for a destination about to be sent all of fd (read after
 * this call): the newest logged era, which has already started.  Logs an
 * era first if the device has none.  "" when fd is not on a dm-era device.
 */
void era_sync_state(int fd, STRUCT_STAT *st, char *new_state)
{
	struct era_dev *e;
	const char *why;
	char newest[64];

	new_state[0] = '\0';
	if (!S_ISREG(st->st_mode) || !(e = era_for_dev(st->st_dev, &why)))
		return;
	log_scan(e, NULL, newest);
	if (!*newest) {
		era_cycle(e, fd, 0);
		log_scan(e, NULL, newest);
	}
	if (*newest)
		snprintf(new_state, ERA_STATE_LEN, "%s %s", newest, e->id);
}

/* Generator: read the destination's ERA_XATTR; 0 if it has one. */
int era_get_state(const char *fname, char *state)
{
	ssize_t n = lgetxattr(fname, ERA_XATTR, state, ERA_STATE_LEN - 1);

	if (n <= 0)
		return -1;
	state[n] = '\0';
	return 0;
}

/* Files whose source record was stored this run. The destination record is
 * appended from era_cleanup(), after one snapshot that follows the writes. */
struct era_note {
	char *path;
	char *state;
	dev_t dev;
};
static struct era_note *notes;
static int n_notes, alloc_notes;

static void era_note_file(int fd, const char *fname, const char *state)
{
	struct era_note *note;
	STRUCT_STAT st;
	char path[MAXPATHLEN], link[64];
	ssize_t n;

	if (do_fstat(fd, &st) < 0 || !S_ISREG(st.st_mode))
		return;
	snprintf(link, sizeof link, "/proc/self/fd/%d", fd);
	n = readlink(link, path, sizeof path - 1);
	if (n < 0 || n >= (ssize_t)sizeof path - 1)
		strlcpy(path, fname, sizeof path);
	else
		path[n] = '\0';
	if (n_notes == alloc_notes) {
		struct era_note *nn;
		int nalloc = alloc_notes ? alloc_notes * 2 : 64;

		if (!(nn = realloc(notes, (size_t)nalloc * sizeof *notes)))
			out_of_memory("era");
		notes = nn;
		alloc_notes = nalloc;
	}
	note = &notes[n_notes];
	if (!(note->path = strdup(path)) || !(note->state = strdup(state)))
		out_of_memory("era");
	note->dev = st.st_dev;
	n_notes++;
}

static void era_forget_notes(void)
{
	int i;

	for (i = 0; i < n_notes; i++) {
		free(notes[i].path);
		free(notes[i].state);
	}
	free(notes);
	notes = NULL;
	n_notes = alloc_notes = 0;
}

/* Receiver: set the ERA_XATTR of an open destination file, or remove it
 * when state is "".  A destination that cannot hold it is fatal.  A
 * non-empty state is the source record; the destination record is added
 * once the run's writes are done. */
void era_put_state(int fd, const char *fname, const char *state)
{
	if (*state ? fsetxattr(fd, ERA_XATTR, state, strlen(state), 0) == 0
		   : fremovexattr(fd, ERA_XATTR) == 0 || errno == ENODATA) {
		if (*state)
			era_note_file(fd, fname, state);
		return;
	}
	era_fatal(RERR_FILEIO, "--era: cannot %s xattr " ERA_XATTR " on %s: %s%s",
		  *state ? "set" : "remove", full_fname(fname), strerror(errno),
		  errno == ENOTSUP ? " (--era needs a destination filesystem with user xattrs)" : "");
}

static int bitmap_empty(struct era_dev *e, struct era_bitmap *bm)
{
	uint64_t words = (e->nr_blocks + 63) / 64, i;

	for (i = 0; i < words; i++)
		if (bm->bits[i])
			return 0;
	return 1;
}

static void mark_all(struct era_ranges *d, OFF_T size)
{
	era_free_ranges(d);
	if (size > 0)
		era_add_range(d, 0, size);
}

static void era_dest_msg(const char *fname, const char *why)
{
	if (INFO_GTE(NAME, 1))
		rprintf(FINFO, "--era: %s: %s; updating from the source\n", fname, why);
}

/* Second record of an era xattr, or 0 if there is only a source record. */
static int dest_record(const char *state, unsigned long long *era, char *when, char *id)
{
	unsigned long long src_era, dst_era;
	char src_when[32], src_id[ERA_STATE_LEN], dst_when[32], dst_id[ERA_STATE_LEN];

	if (sscanf(state, "%llu %31s %335s %llu %31s %335s",
		   &src_era, src_when, src_id, &dst_era, dst_when, dst_id) != 6
	 || !dst_era)
		return 0;
	*era = dst_era;
	strlcpy(when, dst_when, 32);
	strlcpy(id, dst_id, ERA_STATE_LEN);
	return 1;
}

/*
 * Generator: byte ranges of fname written on its destination era device
 * after the destination record in the xattr.  No record, or a destination
 * that is not on dm-era (or not readable as root), leaves *dirty empty:
 * the copy is not treated as changed, and a later completed run starts
 * watching.  A record this device's log does not contain marks the whole
 * file, so the source is sent again.
 */
void era_dest_ranges(const char *fname, STRUCT_STAT *st, struct era_ranges *dirty)
{
	unsigned long long era;
	char state[ERA_STATE_LEN], when[32], id[ERA_STATE_LEN], stamp[64];
	struct era_dev *e;
	struct era_bitmap *bm;
	const char *why;
	int fd;

	dirty->n = 0;
	if (!S_ISREG(st->st_mode) || st->st_size <= 0)
		return;
	if (era_get_state(fname, state) < 0 || !dest_record(state, &era, when, id))
		return;
	if (!era_invalidate_path() || dm_ensure(0) < 0)
		return;
	if (!(e = era_for_dev(st->st_dev, &why)))
		return;
	if (strcmp(id, e->id) != 0) {
		era_dest_msg(fname, "destination era device changed");
		mark_all(dirty, st->st_size);
		return;
	}
	snprintf(stamp, sizeof stamp, "%llu %s", era, when);
	if (!log_scan(e, stamp, NULL)) {
		era_dest_msg(fname, "destination era is not in the era log");
		mark_all(dirty, st->st_size);
		return;
	}
	/* An exact empty bitmap from an earlier file needs no open or FIEMAP. */
	{
		int i;

		for (i = 0; i < e->nbm; i++) {
			if (e->bm[i].since_era == era && bitmap_empty(e, &e->bm[i]))
				return;
		}
	}
	if ((fd = open(fname, O_RDONLY | O_NOFOLLOW | O_CLOEXEC)) < 0) {
		era_dest_msg(fname, "cannot read destination extents");
		mark_all(dirty, st->st_size);
		return;
	}
	bm = get_bitmap(e, fd, era);
	if (!bm || bitmap_empty(e, bm)) {
		close(fd);
		if (!bm) {
			era_dest_msg(fname, "too many destination eras to tell which blocks changed");
			mark_all(dirty, st->st_size);
		}
		return;
	}
	why = extents_to_dirty(fd, st->st_size, st->st_dev, e, bm, dirty, 0);
	close(fd);
	if (why) {
		era_dest_msg(fname, why);
		mark_all(dirty, st->st_size);
		return;
	}
	if (dirty->n)
		era_dest_msg(fname, "destination was written after its recorded era");
}

/* An unchanged file that has a source era but no destination era yet.
 * Remember it so the generator can append a destination era at the end of
 * the run, without sending the file again.  Watching starts on the next run. */
void era_arm_dest(const char *fname, STRUCT_STAT *st)
{
	unsigned long long src_era, dst_era;
	char state[ERA_STATE_LEN];
	char src_when[32], src_id[336], dst_when[32], dst_id[ERA_STATE_LEN];
	const char *why;
	int fd, end = -1;

	if (!S_ISREG(st->st_mode))
		return;
	if (era_get_state(fname, state) < 0)
		return;
	/* Already watching, or not a single source triple with nothing after it. */
	if (dest_record(state, &dst_era, dst_when, dst_id))
		return;
	if (sscanf(state, "%llu %31s %335s %n", &src_era, src_when, src_id, &end) != 3
	 || !src_era || end < 0 || state[end] != '\0')
		return;
	if (!era_invalidate_path() || dm_ensure(0) < 0)
		return;
	if (!era_for_dev(st->st_dev, &why))
		return;
	if ((fd = open(fname, O_RDONLY | O_NOFOLLOW | O_CLOEXEC)) < 0)
		return;
	era_note_file(fd, fname, state);
	close(fd);
}

/* After the receiver's writes: roll each destination era device once and
 * append that era to the files this run updated.  Writes in the same era
 * as rsync's own, before this snapshot, are not distinguishable from them. */
static void era_stamp_dest(void)
{
	int i;

	if (dm_ensure(0) < 0 || !era_invalidate_path()) {
		era_forget_notes();
		return;
	}
	for (i = 0; i < n_notes; i++) {
		const char *why;
		struct era_dev *e = era_for_dev(notes[i].dev, &why);
		int fd;

		if (!e || e->end_stamped)
			continue;
		if ((fd = open(notes[i].path, O_RDONLY | O_CLOEXEC)) < 0)
			era_fatal(RERR_FILEIO, "--era: cannot open %s to record the destination era: %s",
				  notes[i].path, strerror(errno));
		era_cycle(e, fd, 0);
		close(fd);
		e->end_stamped = 1;
		if (DEBUG_GTE(DELTASUM, 1))
			rprintf(FINFO, "era: %s: destination watermark %s\n", e->id, e->last_stamp);
	}
	for (i = 0; i < n_notes; i++) {
		const char *why;
		struct era_dev *e = era_for_dev(notes[i].dev, &why);
		char final[ERA_STATE_LEN];
		int fd, nw;

		if (!e || !e->end_stamped || !e->last_stamp[0])
			continue;
		nw = snprintf(final, sizeof final, "%s %s %s", notes[i].state, e->last_stamp, e->id);
		if (nw < 0 || nw >= (int)sizeof final)
			era_fatal(RERR_FILEIO, "--era: destination era state for %s is too long", notes[i].path);
		if ((fd = open(notes[i].path, O_RDONLY | O_NOFOLLOW | O_CLOEXEC)) < 0)
			era_fatal(RERR_FILEIO, "--era: cannot open %s to record the destination era: %s",
				  notes[i].path, strerror(errno));
		if (fsetxattr(fd, ERA_XATTR, final, (size_t)nw, 0) < 0) {
			int saved = errno;

			close(fd);
			era_fatal(RERR_FILEIO, "--era: cannot set xattr " ERA_XATTR " on %s: %s",
				  notes[i].path, strerror(saved));
		}
		close(fd);
	}
	era_forget_notes();
}

/* Fail now, rather than half-way through, if --era cannot work here. */
void era_check(void)
{
	if (!era_invalidate_path())
		era_fatal(RERR_UNSUPPORTED, "--era: era_invalidate not found: install thin-provisioning-tools "
			  "(device-mapper-persistent-data); --era cannot work without it");
}

void era_cleanup(void)
{
	snap_drop();
	if (n_notes)
		era_stamp_dest();
}

static NORETURN void era_fatal(int code, const char *fmt, ...)
{
	char buf[1024];
	va_list ap;

	va_start(ap, fmt);
	vsnprintf(buf, sizeof buf, fmt, ap);
	va_end(ap);
	rprintf(FERROR, "%s\n", buf);
	exit_cleanup(code);
}

#else /* !SUPPORT_ERA */

const char *era_file_ranges(UNUSED(int fd), UNUSED(STRUCT_STAT *st), UNUSED(time_t mtime),
			    UNUSED(uint32 mtime_nsec), UNUSED(const char *state),
			    struct era_ranges *dirty, UNUSED(char *new_state),
			    UNUSED(int *mtime_ok))
{
	dirty->n = 0;
	return "dm-era is only supported on standard Linux";
}

void era_sync_state(UNUSED(int fd), UNUSED(STRUCT_STAT *st), char *new_state)
{
	new_state[0] = '\0';
}

int era_get_state(UNUSED(const char *fname), UNUSED(char *state))
{
	return -1;
}

void era_put_state(UNUSED(int fd), UNUSED(const char *fname), UNUSED(const char *state))
{
}

void era_dest_ranges(UNUSED(const char *fname), UNUSED(STRUCT_STAT *st), struct era_ranges *dirty)
{
	dirty->n = 0;
}

void era_arm_dest(UNUSED(const char *fname), UNUSED(STRUCT_STAT *st))
{
}

void era_check(void)
{
	rprintf(FERROR, "--era is only supported on standard Linux (not Android or other systems)\n");
	exit_cleanup(RERR_UNSUPPORTED);
}

void era_cleanup(void)
{
}

#endif

void era_add_range(struct era_ranges *d, OFF_T off, OFF_T len)
{
	if (len <= 0)
		return;
	if (d->n && d->off[d->n - 1] + d->len[d->n - 1] >= off) {
		OFF_T end = off + len;

		if (end > d->off[d->n - 1] + d->len[d->n - 1])
			d->len[d->n - 1] = end - d->off[d->n - 1];
		return;
	}
	if (d->n == d->alloc) {
		d->alloc = d->alloc ? d->alloc * 2 : 64;
		if (!(d->off = realloc(d->off, d->alloc * sizeof (OFF_T)))
		 || !(d->len = realloc(d->len, d->alloc * sizeof (OFF_T))))
			out_of_memory("era");
	}
	d->off[d->n] = off;
	d->len[d->n++] = len;
}

void era_merge_ranges(struct era_ranges *d, const struct era_ranges *extra, OFF_T limit)
{
	struct era_ranges out;
	int i = 0, j = 0;

	if (!extra || !extra->n)
		return;
	memset(&out, 0, sizeof out);
	while (i < d->n || j < extra->n) {
		OFF_T off, len;
		int use_d = j >= extra->n || (i < d->n && d->off[i] <= extra->off[j]);

		if (use_d) {
			off = d->off[i];
			len = d->len[i];
			i++;
		} else {
			off = extra->off[j];
			len = extra->len[j];
			j++;
		}
		if (off < 0 || len <= 0)
			continue;
		if (off >= limit)
			continue;
		if (len > limit - off)
			len = limit - off;
		era_add_range(&out, off, len);
	}
	free(d->off);
	free(d->len);
	*d = out;
}

void era_free_ranges(struct era_ranges *d)
{
	free(d->off);
	free(d->len);
	memset(d, 0, sizeof *d);
}
