/* mergebox.c -- disk-backed, layer-by-layer exploration of the twelve-move
 * Andrews-Curtis component of a rank-2 pair inside the total-length box
 * |u| + |v| <= T, with a target list, written for the round-5 direction H4
 * (class-merge certification of the 66 undecided length-14 resisters).
 *
 * It is derived from directions/cap21/rawbox4.c (round 4, direction G3): the
 * layer files, the chunked radix sort, the k-way merge and the anti-join are
 * that program's method.  Code taken over: the sort, the merge, the anti-join,
 * the reader/writer structs and the driver shape.  Changes:
 *   - the state encoding is 6 bits per length and 2 bits per letter (acx.c's
 *     convention), so a total length of 26 fits in 64 bits;
 *   - only the twelve restricted moves are generated (both inversions, both
 *     right multiplications, conjugation of either relator by one letter),
 *     so the component is exactly the one directions/resisters/round4/acx.c
 *     explores;
 *   - the start pair is a command-line argument and a target file is checked
 *     at every new state;
 *   - every layer is kept as a file, so a hitting path can be reconstructed
 *     backwards;
 *   - the class-key machinery of rawbox4 is dropped.
 *
 * Usage: mergebox T WORKDIR START [TARGETS] [--resume] [--maxlayers N] [-v]
 *   T         total-length cap (at most 26)
 *   WORKDIR   directory for the frontier, visited and layer files
 *   START     pair "word,word" over a A b B
 *   TARGETS   file of 8-byte keys to watch for (optional)
 * Prints one line per layer and, at the end, NEW <layer> <key> <pair> for each
 * target met, or EXHAUSTED <layers> <states>.
 */
#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXL 27
#define MAXW (MAXL + 8)

static int Tcap, verbose = 0;
static double MAXSEC = 1e18;
static int NOFINAL = 0, RESUME = 0;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + 1e-9 * ts.tv_nsec;
}

static inline int code(int8_t a) { return a == 1 ? 0 : a == -1 ? 1 : a == 2 ? 2 : 3; }
static inline int8_t uncode(int c) { return c == 0 ? 1 : c == 1 ? -1 : c == 2 ? 2 : -2; }

/* 6-bit lengths, letters from bit 12 */
static inline uint64_t enc(int n1, int n2, const int8_t *u, const int8_t *v) {
    uint64_t k = (uint64_t)(unsigned)n1 | ((uint64_t)(unsigned)n2 << 6);
    int pos = 12;
    for (int i = 0; i < n1; i++) { k |= ((uint64_t)code(u[i])) << pos; pos += 2; }
    for (int i = 0; i < n2; i++) { k |= ((uint64_t)code(v[i])) << pos; pos += 2; }
    return k;
}
static inline void dec(uint64_t k, int *n1, int *n2, int8_t *u, int8_t *v) {
    *n1 = (int)(k & 63); *n2 = (int)((k >> 6) & 63);
    int pos = 12;
    for (int i = 0; i < *n1; i++) { u[i] = uncode((int)((k >> pos) & 3)); pos += 2; }
    for (int i = 0; i < *n2; i++) { v[i] = uncode((int)((k >> pos) & 3)); pos += 2; }
}
static int parse_word(const char *s, int8_t *out) {
    int n = 0;
    for (const char *p = s; *p; p++) {
        int8_t v;
        switch (*p) {
            case 'a': v = 1; break;
            case 'A': v = -1; break;
            case 'b': v = 2; break;
            case 'B': v = -2; break;
            default: return -1;
        }
        out[n++] = v;
    }
    return n;
}
static void show_word(const int8_t *w, int n, char *out) {
    if (n == 0) { strcpy(out, "e"); return; }
    for (int i = 0; i < n; i++)
        out[i] = w[i] == 1 ? 'a' : w[i] == -1 ? 'A' : w[i] == 2 ? 'b' : 'B';
    out[n] = 0;
}
static int parse_pair(const char *s, int8_t *r1, int *n1, int8_t *r2, int *n2) {
    char buf[512];
    snprintf(buf, sizeof buf, "%s", s);
    char *comma = strchr(buf, ',');
    if (!comma) return -1;
    *comma = 0;
    *n1 = parse_word(buf, r1);
    *n2 = parse_word(comma + 1, r2);
    return (*n1 < 0 || *n2 < 0) ? -1 : 0;
}
static void print_pair(uint64_t k) {
    int n1, n2; int8_t u[MAXL], v[MAXL];
    dec(k, &n1, &n2, u, v);
    char a[3 * MAXL], b[3 * MAXL];
    show_word(u, n1, a); show_word(v, n2, b);
    printf("%s,%s", a, b);
}

static int reduce_into(const int8_t *a, int na, int8_t *out) {
    int n = 0;
    for (int i = 0; i < na; i++) { if (n > 0 && out[n - 1] == -a[i]) n--; else out[n++] = a[i]; }
    return n;
}

static const int8_t CONJ1[4] = {1, -1, 2, -2};

/* the twelve restricted moves; only neighbours inside the box are returned */
static int expand(uint64_t k, uint64_t *out) {
    int n1, n2; int8_t u[MAXL], v[MAXL], w1[MAXL], w2[MAXL], t[MAXW], o[MAXW];
    dec(k, &n1, &n2, u, v);
    int m = 0;
    for (int i = 0; i < n1; i++) w1[i] = -u[n1 - 1 - i];
    if (n1 + n2 <= Tcap) out[m++] = enc(n1, n2, w1, v);
    for (int i = 0; i < n2; i++) w2[i] = -v[n2 - 1 - i];
    if (n1 + n2 <= Tcap) out[m++] = enc(n1, n2, u, w2);
    memcpy(t, u, n1); memcpy(t + n1, v, n2);
    { int mm = reduce_into(t, n1 + n2, o); if (mm + n2 <= Tcap) out[m++] = enc(mm, n2, o, v); }
    memcpy(t, v, n2); memcpy(t + n2, u, n1);
    { int mm = reduce_into(t, n2 + n1, o); if (n1 + mm <= Tcap) out[m++] = enc(n1, mm, u, o); }
    for (int j = 0; j < 4; j++) {
        int8_t g = CONJ1[j];
        t[0] = g; memcpy(t + 1, u, n1); t[1 + n1] = -g;
        { int mm = reduce_into(t, n1 + 2, o); if (mm + n2 <= Tcap) out[m++] = enc(mm, n2, o, v); }
        t[0] = g; memcpy(t + 1, v, n2); t[1 + n2] = -g;
        { int mm = reduce_into(t, n2 + 2, o); if (n1 + mm <= Tcap) out[m++] = enc(n1, mm, u, o); }
    }
    return m;
}

/* ---------- in-memory radix sort of 64-bit keys (LSD, 8 bits per pass) ------ */
static void radix_sort(uint64_t *a, uint64_t *tmp, size_t n) {
    if (n < 2) return;
    size_t cnt[256];
    for (int sh = 0; sh < 64; sh += 8) {
        memset(cnt, 0, sizeof cnt);
        for (size_t i = 0; i < n; i++) cnt[(a[i] >> sh) & 255]++;
        int nz = 0;
        for (int d = 1; d < 256; d++) if (cnt[d]) { nz = 1; break; }
        if (!nz) continue;
        size_t sum = 0;
        for (int d = 0; d < 256; d++) { size_t c = cnt[d]; cnt[d] = sum; sum += c; }
        for (size_t i = 0; i < n; i++) tmp[cnt[(a[i] >> sh) & 255]++] = a[i];
        memcpy(a, tmp, n * sizeof(uint64_t));
    }
}

typedef struct { FILE *f; uint64_t cur; int live; } rd_t;
static rd_t rd_open(const char *path) {
    rd_t r; r.f = fopen(path, "rb");
    if (!r.f) { fprintf(stderr, "cannot read %s\n", path); exit(1); }
    r.live = (fread(&r.cur, 8, 1, r.f) == 1);
    return r;
}
static inline void rd_next(rd_t *r) { r->live = (fread(&r->cur, 8, 1, r->f) == 1); }
static void rd_close(rd_t *r) { if (r->f) fclose(r->f); r->f = NULL; }

typedef struct { FILE *f; char path[4096]; size_t n; } wr_t;
static wr_t wr_open(const char *path) {
    wr_t w; snprintf(w.path, sizeof w.path, "%s", path);
    w.f = fopen(path, "wb"); w.n = 0;
    if (!w.f) { fprintf(stderr, "cannot write %s\n", path); exit(1); }
    return w;
}
static inline void wr_put(wr_t *w, uint64_t k) { fwrite(&k, 8, 1, w->f); w->n++; }
static void wr_close(wr_t *w) { fclose(w->f); w->f = NULL; }

static size_t merge_unique(char **paths, int npaths, const char *out) {
    rd_t *r = malloc(sizeof(rd_t) * npaths);
    for (int i = 0; i < npaths; i++) r[i] = rd_open(paths[i]);
    wr_t w = wr_open(out);
    for (;;) {
        int best = -1; uint64_t bv = 0;
        for (int i = 0; i < npaths; i++) if (r[i].live && (best < 0 || r[i].cur < bv)) { best = i; bv = r[i].cur; }
        if (best < 0) break;
        wr_put(&w, bv);
        for (int i = 0; i < npaths; i++) if (r[i].live && r[i].cur == bv) rd_next(&r[i]);
    }
    wr_close(&w);
    for (int i = 0; i < npaths; i++) rd_close(&r[i]);
    free(r);
    return w.n;
}

static void anti_join(const char *A, const char *B, const char *pnew, const char *puni,
                      size_t *nnew, size_t *nuni) {
    rd_t a = rd_open(A), b = rd_open(B);
    wr_t wn = wr_open(pnew), wu = wr_open(puni);
    while (a.live || b.live) {
        if (!b.live) { wr_put(&wn, a.cur); wr_put(&wu, a.cur); rd_next(&a); continue; }
        if (!a.live) { wr_put(&wu, b.cur); rd_next(&b); continue; }
        if (a.cur < b.cur) { wr_put(&wn, a.cur); wr_put(&wu, a.cur); rd_next(&a); }
        else if (a.cur == b.cur) { wr_put(&wu, b.cur); rd_next(&a); rd_next(&b); }
        else { wr_put(&wu, b.cur); rd_next(&b); }
    }
    *nnew = wn.n; *nuni = wu.n;
    wr_close(&wn); wr_close(&wu);
    rd_close(&a); rd_close(&b);
}

/* ---------------- target set: sorted array + binary search ---------------- */
static uint64_t *tgt = NULL; static size_t ntgt = 0;
static int cmp64(const void *x, const void *y) {
    uint64_t a = *(const uint64_t *)x, b = *(const uint64_t *)y;
    return a < b ? -1 : (a > b ? 1 : 0);
}
static int tgt_has(uint64_t k) {
    if (!ntgt) return 0;
    return bsearch(&k, tgt, ntgt, 8, cmp64) != NULL;
}

int main(int argc, char **argv) {
    if (argc < 4) {
        fprintf(stderr, "usage: mergebox T WORKDIR START [TARGETS] [--resume] [-v]\n");
        return 1;
    }
    Tcap = atoi(argv[1]);
    const char *wd = argv[2];
    const char *start = argv[3];
    const char *tfile = NULL;
    for (int i = 4; i < argc; i++) {
        if (!strcmp(argv[i], "--resume")) RESUME = 1;
        else if (!strcmp(argv[i], "-v")) verbose = 1;
        else if (!strcmp(argv[i], "--maxsec") && i + 1 < argc) MAXSEC = atof(argv[++i]);
        else if (argv[i][0] != '-') tfile = argv[i];
    }
    if (Tcap > 26) { fprintf(stderr, "T must be at most 26\n"); return 1; }
    int8_t r1[MAXL], r2[MAXL]; int n1, n2;
    if (parse_pair(start, r1, &n1, r2, &n2)) { fprintf(stderr, "bad start\n"); return 1; }
    if (n1 + n2 > Tcap) { fprintf(stderr, "start outside the box\n"); return 1; }
    if (tfile) {
        FILE *ft = fopen(tfile, "rb");
        if (!ft) { fprintf(stderr, "cannot read %s\n", tfile); return 1; }
        size_t cap = 16; tgt = malloc(cap * 8);
        while (fread(&tgt[ntgt], 8, 1, ft) == 1) {
            ntgt++;
            if (ntgt == cap) { cap *= 2; tgt = realloc(tgt, cap * 8); }
        }
        fclose(ft);
        qsort(tgt, ntgt, 8, cmp64);
    }

    char p_front[4096], p_cand[4096], p_vis[4096], p_visnew[4096], p_new[4096];
    char p_layer[4096], p_state[4096];
    snprintf(p_front, sizeof p_front, "%s/frontier.bin", wd);
    snprintf(p_cand, sizeof p_cand, "%s/cand.bin", wd);
    snprintf(p_vis, sizeof p_vis, "%s/visited.bin", wd);
    snprintf(p_visnew, sizeof p_visnew, "%s/visited_new.bin", wd);
    snprintf(p_new, sizeof p_new, "%s/frontier_new.bin", wd);
    snprintf(p_state, sizeof p_state, "%s/state.txt", wd);

    int depth0 = 0; size_t cumulative0 = 0;
    if (RESUME) {
        FILE *fs = fopen(p_state, "r");
        if (!fs) { fprintf(stderr, "--resume but %s missing\n", p_state); return 1; }
        long long c;
        if (fscanf(fs, "depth %d\ncumulative %lld\n", &depth0, &c) != 2) { fprintf(stderr, "bad state\n"); return 1; }
        fclose(fs);
        cumulative0 = (size_t)c;
        char cmd[4200];
        snprintf(cmd, sizeof cmd, "rm -f %s/chunk_*.bin %s/cand.bin %s/visited_new.bin %s/frontier_new.bin",
                 wd, wd, wd, wd);
        if (system(cmd) != 0) { fprintf(stderr, "cleanup failed\n"); return 1; }
        fprintf(stderr, "resuming at depth %d with cumulative %zu\n", depth0, cumulative0);
    } else {
        wr_t w = wr_open(p_front);
        wr_put(&w, enc(n1, n2, r1, r2));
        wr_close(&w);
        w = wr_open(p_vis);          /* the root is the first visited state */
        wr_put(&w, enc(n1, n2, r1, r2));
        wr_close(&w);
        cumulative0 = 1;
    }

    const size_t BUF = (size_t)1 << 24;   /* 16M keys = 128 MB */
    uint64_t *buf = malloc(BUF * 8), *tmp = malloc(BUF * 8);
    if (!buf || !tmp) { fprintf(stderr, "oom buffers\n"); return 2; }
    size_t cumulative = cumulative0;
    double t0 = now();

    for (int depth = depth0; depth < 4096; depth++) {
        FILE *f = fopen(p_front, "rb");
        if (!f) { fprintf(stderr, "missing frontier at depth %d\n", depth); return 1; }
        size_t nfront = 0;
        { size_t got; while ((got = fread(buf, 8, BUF, f)) > 0) nfront += got; }
        fclose(f);
        if (nfront == 0) {
            printf("EXHAUSTED %d %zu\n", depth, cumulative);
            break;
        }
        f = fopen(p_front, "rb");
        snprintf(p_layer, sizeof p_layer, "%s/layer_%05d.bin", wd, depth);
        {   /* copy the frontier to its layer file and check the root */
            static const size_t CB = (size_t)1 << 20;
            uint64_t *cb = malloc(CB * 8);
            if (!cb) { fprintf(stderr, "oom copy buffer\n"); return 2; }
            wr_t w = wr_open(p_layer);
            size_t got2, first = 1;
            while ((got2 = fread(cb, 8, CB, f)) > 0) {
                if (first && depth == 0 && tgt_has(cb[0])) {
                    printf("HIT 0 "); print_pair(cb[0]); printf("\n");
                }
                for (size_t i = 0; i < got2; i++) wr_put(&w, cb[i]);
                first = 0;
            }
            wr_close(&w);
            free(cb);
        }
        fclose(f);

        int nchunks = 0; size_t nbuf = 0;
        char **chunk = NULL;
        size_t nhit = 0;
        f = fopen(p_front, "rb");
        if (!f) { fprintf(stderr, "missing frontier at depth %d\n", depth); return 1; }
        static const size_t FB = (size_t)1 << 20;
        uint64_t *fbb = malloc(FB * 8);
        if (!fbb) { fprintf(stderr, "oom frontier buffer\n"); return 2; }
        size_t fgot;
        while ((fgot = fread(fbb, 8, FB, f)) > 0) {
        for (size_t i = 0; i < fgot; i++) {
            if (nbuf + 16 > BUF) {
                radix_sort(buf, tmp, nbuf);
                size_t m = 0;
                for (size_t j = 0; j < nbuf; j++) if (j == 0 || buf[j] != buf[j - 1]) buf[m++] = buf[j];
                char *nm = malloc(4096);
                snprintf(nm, 4096, "%s/chunk_%05d_%03d.bin", wd, depth, nchunks);
                wr_t w = wr_open(nm); for (size_t j = 0; j < m; j++) wr_put(&w, buf[j]); wr_close(&w);
                chunk = realloc(chunk, sizeof(char *) * (nchunks + 1)); chunk[nchunks++] = nm;
                nbuf = 0;
            }
            int cnt = expand(fbb[i], buf + nbuf);
            if (ntgt) for (int q = 0; q < cnt; q++) if (tgt_has(buf[nbuf + q])) {
                printf("HIT %d ", depth + 1); print_pair(buf[nbuf + q]); printf("\n");
                nhit++;
            }
            nbuf += cnt;
        }
        }
        free(fbb); fclose(f);
        if (nbuf) {
            radix_sort(buf, tmp, nbuf);
            size_t m = 0;
            for (size_t j = 0; j < nbuf; j++) if (j == 0 || buf[j] != buf[j - 1]) buf[m++] = buf[j];
            char *nm = malloc(4096);
            snprintf(nm, 4096, "%s/chunk_%05d_%03d.bin", wd, depth, nchunks);
            wr_t w = wr_open(nm); for (size_t j = 0; j < m; j++) wr_put(&w, buf[j]); wr_close(&w);
            chunk = realloc(chunk, sizeof(char *) * (nchunks + 1)); chunk[nchunks++] = nm;
        }
        merge_unique(chunk, nchunks, p_cand);
        for (int i = 0; i < nchunks; i++) { remove(chunk[i]); free(chunk[i]); }
        free(chunk);

        size_t nnew;
        { size_t nuni;
          anti_join(p_cand, p_vis, p_new, p_visnew, &nnew, &nuni);
          if (nuni != cumulative + nnew)
              fprintf(stderr, "warning: union %zu vs cumulative %zu + new %zu\n", nuni, cumulative, nnew);
          remove(p_vis); rename(p_visnew, p_vis);
        }
        remove(p_front); rename(p_new, p_front);
        cumulative += nnew;
        printf("layer %d: frontier %zu, new %zu, cumulative %zu, %.1fs\n",
               depth, nfront, nnew, cumulative, now() - t0);
        fflush(stdout);
        { FILE *fs = fopen(p_state, "w");
          fprintf(fs, "depth %d\ncumulative %zu\n", depth + 1, cumulative);
          fclose(fs); }
        if (MAXSEC < 1e17 && now() - t0 > MAXSEC) { printf("MAXSEC reached\n"); break; }
    }
    printf("DONE states %zu layers %d\n", cumulative, depth0);
    return 0;
}
