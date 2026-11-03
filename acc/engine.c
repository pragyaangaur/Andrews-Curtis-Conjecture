/* Fast search engine for the ac-r2-v1 move set.
 *
 * Two searches:
 *   complete  exact BFS of radius r from the instance, meeting a precomputed
 *             ball of radius D around the target.  Finds every solution of
 *             length <= D + r and proves there is none within that bound.
 *   beam      breadth-limited guided search for the ones the exact search
 *             cannot reach.
 *
 * Modes:
 *   sizes  D                print the ball size at each depth up to D
 *   ball   D FILE           build the depth-D ball and save it
 *   exact  FILE r INFILE OUTFILE
 *   beam   FILE W S INFILE OUTFILE SEED WS WM WA NOISE
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

#ifndef MAXLEN
#define MAXLEN 128
#endif
#ifndef MAXTOT
#define MAXTOT (2 * MAXLEN)
#endif

typedef struct { int16_t l0, l1; int8_t w0[MAXLEN]; int8_t w1[MAXLEN]; } State;

static int fred(int8_t *w, int n) {
    int t = 0;
    for (int i = 0; i < n; i++) {
        int c = w[i];
        if (t > 0 && w[t - 1] == -c) t--;
        else w[t++] = (int8_t)c;
    }
    return t;
}

static long g_cap_hits = 0;   /* moves rejected because the result would exceed MAXLEN */

static const int8_t INV_MOVE[14] = {0, 1, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12};
static const int8_t GENS[4] = {1, -1, 2, -2};

/* apply move m to s, writing the result to o.  returns 0 if the result would
 * exceed MAXLEN. */
static int apply(const State *s, int m, State *o) {
    int8_t b[MAXTOT];
    int n = 0;
    if (m == 0 || m == 1) {
        const int8_t *src = (m == 0) ? s->w0 : s->w1;
        int L = (m == 0) ? s->l0 : s->l1;
        for (int i = 0; i < L; i++) b[i] = (int8_t)(-src[L - 1 - i]);
        *o = *s;
        if (m == 0) { memcpy(o->w0, b, (size_t)L); }
        else { memcpy(o->w1, b, (size_t)L); }
        return 1;
    }
    if (m >= 2 && m <= 5) {
        int tgt0 = (m <= 3);
        const int8_t *x = tgt0 ? s->w0 : s->w1;
        int lx = tgt0 ? s->l0 : s->l1;
        const int8_t *y = tgt0 ? s->w1 : s->w0;
        int ly = tgt0 ? s->l1 : s->l0;
        int neg = (m == 3 || m == 5);
        if (lx + ly > MAXTOT) return 0;
        memcpy(b, x, (size_t)lx);
        if (!neg) memcpy(b + lx, y, (size_t)ly);
        else for (int i = 0; i < ly; i++) b[lx + i] = (int8_t)(-y[ly - 1 - i]);
        n = fred(b, lx + ly);
        if (n > MAXLEN) { g_cap_hits++; return 0; }
        *o = *s;
        if (tgt0) { memcpy(o->w0, b, (size_t)n); o->l0 = (int16_t)n; }
        else { memcpy(o->w1, b, (size_t)n); o->l1 = (int16_t)n; }
        return 1;
    }
    {
        int g = GENS[(m - 6) % 4];
        int tgt0 = (m < 10);
        const int8_t *x = tgt0 ? s->w0 : s->w1;
        int lx = tgt0 ? s->l0 : s->l1;
        b[0] = (int8_t)g;
        memcpy(b + 1, x, (size_t)lx);
        b[1 + lx] = (int8_t)(-g);
        n = fred(b, lx + 2);
        if (n > MAXLEN) { g_cap_hits++; return 0; }
        *o = *s;
        if (tgt0) { memcpy(o->w0, b, (size_t)n); o->l0 = (int16_t)n; }
        else { memcpy(o->w1, b, (size_t)n); o->l1 = (int16_t)n; }
        return 1;
    }
}

static inline uint64_t hashstate(const State *s) {
    uint64_t h = 1469598103934665603ULL;
    h = (h ^ (uint64_t)((uint16_t)s->l0)) * 1099511628211ULL;
    h = (h ^ (uint64_t)((uint16_t)s->l1)) * 1099511628211ULL;
    const int8_t *p = s->w0;
    for (int i = 0; i < s->l0; i++) { h = (h ^ (uint64_t)(uint8_t)(p[i] + 3)) * 1099511628211ULL; }
    p = s->w1;
    for (int i = 0; i < s->l1; i++) { h = (h ^ (uint64_t)(uint8_t)(p[i] + 3)) * 1099511628211ULL; }
    return h;
}

static inline int is_goal(const State *s, int8_t *cm, int *cmlen) {
    static const int8_t T[8][5] = {
        {0,0,0,0,0},                  /* ( 1, 2) -> empty */
        {1,0,0,0,0},                  /* ( 1,-2) -> [1] */
        {0,0,0,0,0},                  /* (-1, 2) -> [0] */
        {0,1,0,0,0},                  /* (-1,-2) -> [0,1] */
        {2,5,2,8,0},                  /* (-2, 1) -> [2,5,2,8] */
        {3,4,3,10,0},                 /* ( 2,-1) -> [3,4,3,10] */
        {2,0,4,3,0},                  /* (-2,-1) -> [2,0,4,3] */
        {0,2,5,2,8}                   /* ( 2, 1) -> [0,2,5,2,8] */
    };
    static const int8_t TL[8] = {0, 1, 1, 2, 4, 4, 4, 5};
    if (s->l0 != 1 || s->l1 != 1) return 0;
    int a = s->w0[0], b = s->w1[0];
    if (a * b == 0) return 0;
    int aa = a < 0 ? -a : a, bb = b < 0 ? -b : b;
    if (aa == bb) return 0;
    int idx = -1;
    if (aa == 1) { idx = (a == 1) ? (b == 2 ? 0 : 1) : (b == 2 ? 2 : 3); }
    else { idx = (a == -2) ? (b == 1 ? 4 : 6) : (b == -1 ? 5 : 7); }
    *cmlen = TL[idx];
    memcpy(cm, T[idx], 5);
    return 1;
}

/* ---------------- open addressing table: fingerprint -> record index ------- */
typedef struct { uint64_t *fp; int32_t *val; size_t cap, mask, count; } Map;

static void map_init(Map *m, size_t cap) {
    m->fp = (uint64_t *)calloc(cap, sizeof(uint64_t));
    m->val = (int32_t *)malloc(cap * sizeof(int32_t));
    if (!m->fp || !m->val) { fprintf(stderr, "oom map %zu\n", cap); exit(1); }
    for (size_t i = 0; i < cap; i++) m->val[i] = -1;
    m->cap = cap; m->mask = cap - 1; m->count = 0;
}
static void map_clear(Map *m) {
    memset(m->val, 0xff, m->cap * sizeof(int32_t));
    m->count = 0;
}
static inline int32_t map_get(const Map *m, uint64_t k) {
    size_t i = (size_t)k & m->mask;
    while (m->val[i] >= 0) {
        if (m->fp[i] == k) return m->val[i];
        i = (i + 1) & m->mask;
    }
    return -1;
}
static void map_grow(Map *m);
static inline int32_t map_put(Map *m, uint64_t k, int32_t v) {
    /* returns previous value, or -1 after inserting v */
    size_t i = (size_t)k & m->mask;
    while (m->val[i] >= 0) {
        if (m->fp[i] == k) return m->val[i];
        i = (i + 1) & m->mask;
    }
    m->fp[i] = k; m->val[i] = v; m->count++;
    if (m->count * 10 > m->cap * 7) map_grow(m);
    return -1;
}
static void map_grow(Map *m) {
    size_t oc = m->cap;
    uint64_t *ofp = m->fp; int32_t *ov = m->val;
    size_t nc = oc * 2;
    map_init(m, nc);
    for (size_t i = 0; i < oc; i++) if (ov[i] >= 0) map_put(m, ofp[i], ov[i]);
    free(ofp); free(ov);
}

/* ------------------------------- ball ---------------------------------- */
typedef struct { uint64_t fp; int32_t par; int8_t mv; int16_t dep; } Rec;

static Rec *recs = NULL;
static int32_t nrec = 0, caprec = 0;
static Map ballmap;
static int32_t *lstart = NULL;   /* layer boundaries */
static int balldepth = 0;

static void rec_push(uint64_t fp, int32_t par, int8_t mv, int16_t dep) {
    if (nrec == caprec) { caprec = caprec ? caprec * 2 : (1 << 20); recs = (Rec *)realloc(recs, (size_t)caprec * sizeof(Rec)); if (!recs) { fprintf(stderr, "oom recs\n"); exit(1);} }
    recs[nrec].fp = fp; recs[nrec].par = par; recs[nrec].mv = mv; recs[nrec].dep = dep;
    nrec++;
}

static void build_ball(int D, int report) {
    map_init(&ballmap, 1 << 22);
    lstart = (int32_t *)calloc((size_t)D + 2, sizeof(int32_t));
    State *cur = (State *)malloc(sizeof(State));
    int32_t *curnode = (int32_t *)malloc(sizeof(int32_t));
    /* target */
    cur[0].l0 = 1; cur[0].w0[0] = 1; cur[0].l1 = 1; cur[0].w1[0] = 2;
    curnode[0] = 0;
    rec_push(hashstate(&cur[0]), -1, -1, 0);
    map_put(&ballmap, recs[0].fp, 0);
    int32_t ncur = 1;
    lstart[0] = 0; lstart[1] = 1;
    for (int d = 1; d <= D; d++) {
        int32_t capn = ncur * 18 + 1024;
        State *nxt = (State *)malloc((size_t)capn * sizeof(State));
        int32_t *nxtnode = (int32_t *)malloc((size_t)capn * sizeof(int32_t));
        if (!nxt || !nxtnode) { fprintf(stderr, "oom layer d=%d\n", d); exit(1); }
        int32_t nn = 0;
        for (int32_t i = 0; i < ncur; i++) {
            for (int m = 0; m < 14; m++) {
                State t;
                if (!apply(&cur[i], m, &t)) continue;
                uint64_t fp = hashstate(&t);
                if (map_get(&ballmap, fp) >= 0) continue;
                if (nrec == caprec) { caprec = caprec ? caprec * 2 : (1 << 20); recs = (Rec *)realloc(recs, (size_t)caprec * sizeof(Rec)); if (!recs) { fprintf(stderr,"oom\n"); exit(1);} }
                recs[nrec].fp = fp; recs[nrec].par = curnode[i]; recs[nrec].mv = (int8_t)m; recs[nrec].dep = (int16_t)d;
                map_put(&ballmap, fp, nrec);
                nrec++;
                if (nn == capn) { capn *= 2; nxt = (State *)realloc(nxt, (size_t)capn * sizeof(State)); nxtnode = (int32_t *)realloc(nxtnode, (size_t)capn * sizeof(int32_t)); if (!nxt || !nxtnode) { fprintf(stderr,"oom\n"); exit(1);} }
                nxt[nn] = t; nxtnode[nn] = nrec - 1; nn++;
            }
        }
        free(cur); free(curnode);
        cur = nxt; curnode = nxtnode; ncur = nn;
        lstart[d + 1] = nrec;
        if (report) fprintf(stderr, "depth %d: layer %d total %d\n", d, nn, nrec);
    }
    free(cur); free(curnode);
    balldepth = D;
}

static void save_ball(const char *path) {
    FILE *f = fopen(path, "wb");
    if (!f) { perror("save_ball"); exit(1); }
    fwrite(&balldepth, sizeof(int), 1, f);
    fwrite(&nrec, sizeof(int32_t), 1, f);
    fwrite(lstart, sizeof(int32_t), (size_t)balldepth + 2, f);
    /* store fp, par, mv, dep compactly */
    for (int32_t i = 0; i < nrec; i++) {
        fwrite(&recs[i].fp, 8, 1, f);
        fwrite(&recs[i].par, 4, 1, f);
        fwrite(&recs[i].mv, 1, 1, f);
        fwrite(&recs[i].dep, 2, 1, f);
    }
    fclose(f);
}

static void load_ball(const char *path) {
    FILE *f = fopen(path, "rb");
    if (!f) { perror("load_ball"); exit(1); }
    if (fread(&balldepth, sizeof(int), 1, f) != 1) { fprintf(stderr, "bad ball\n"); exit(1); }
    if (fread(&nrec, sizeof(int32_t), 1, f) != 1) { fprintf(stderr, "bad ball\n"); exit(1); }
    lstart = (int32_t *)malloc(((size_t)balldepth + 2) * sizeof(int32_t));
    if (fread(lstart, sizeof(int32_t), (size_t)balldepth + 2, f) != (size_t)balldepth + 2) { fprintf(stderr, "bad ball\n"); exit(1); }
    recs = (Rec *)malloc((size_t)nrec * sizeof(Rec));
    if (!recs) { fprintf(stderr, "oom load\n"); exit(1); }
    for (int32_t i = 0; i < nrec; i++) {
        if (fread(&recs[i].fp, 8, 1, f) != 1) { fprintf(stderr, "bad ball rec\n"); exit(1); }
        if (fread(&recs[i].par, 4, 1, f) != 1) { fprintf(stderr, "bad ball rec\n"); exit(1); }
        if (fread(&recs[i].mv, 1, 1, f) != 1) { fprintf(stderr, "bad ball rec\n"); exit(1); }
        if (fread(&recs[i].dep, 2, 1, f) != 1) { fprintf(stderr, "bad ball rec\n"); exit(1); }
    }
    fclose(f);
    size_t cap = 1 << 12;
    while (cap < (size_t)nrec * 2) cap <<= 1;
    map_init(&ballmap, cap);
    for (int32_t i = 0; i < nrec; i++) map_put(&ballmap, recs[i].fp, i);
}

/* path reconstruction: append backward moves from ball node idx to target.
 * recs[] is built outwards from the target, so walking up from idx collects
 * undoing moves in exactly the order they must be applied. */
static int backward(int32_t idx, int8_t *out) {
    int n = 0;
    while (idx > 0) {
        if (n >= 4000) { fprintf(stderr, "backward too long\n"); exit(1); }
        out[n++] = INV_MOVE[(int)recs[idx].mv];
        idx = recs[idx].par;
    }
    return n;
}

/* ---------------------------- instance parsing -------------------------- */
typedef struct { char id[64]; State st; } Inst;

static int parse_word(const char *s, int8_t *w) {
    int n = 0;
    const char *p = s;
    while (*p && *p != '\t' && *p != '\n' && *p != '|') {
        while (*p == ' ' || *p == ',') p++;
        if (!*p || *p == '\t' || *p == '\n' || *p == '|') break;
        char *e;
        long v = strtol(p, &e, 10);
        if (e == p) return -1;
        w[n++] = (int8_t)v;
        p = e;
    }
    return n;
}

static int read_insts(const char *path, Inst **out) {
    FILE *f = fopen(path, "r");
    if (!f) { perror(path); exit(1); }
    char line[8192];
    int cap = 1024, n = 0;
    Inst *arr = (Inst *)malloc((size_t)cap * sizeof(Inst));
    while (fgets(line, sizeof line, f)) {
        char *tab1 = strchr(line, '\t');
        if (!tab1) continue;
        *tab1 = 0;
        char *tab2 = strchr(tab1 + 1, '\t');
        if (!tab2) continue;
        *tab2 = 0;
        char *nl = strchr(tab2 + 1, '\n');
        if (nl) *nl = 0;
        if (n == cap) { cap *= 2; arr = (Inst *)realloc(arr, (size_t)cap * sizeof(Inst)); }
        memset(&arr[n], 0, sizeof(Inst));
        snprintf(arr[n].id, sizeof arr[n].id, "%s", line);
        int a = parse_word(tab1 + 1, arr[n].st.w0);
        int b = parse_word(tab2 + 1, arr[n].st.w1);
        if (a < 0 || b < 0) { fprintf(stderr, "bad line %s\n", line); continue; }
        arr[n].st.l0 = (int16_t)a; arr[n].st.l1 = (int16_t)b;
        n++;
    }
    fclose(f);
    *out = arr;
    return n;
}

/* ------------------------------- search -------------------------------- */
typedef struct { int32_t *par; int8_t *mv; int32_t n, cap; } Nodes;
static void nodes_push(Nodes *nd, int32_t par, int8_t mv, int32_t *idx) {
    if (nd->n == nd->cap) { nd->cap = nd->cap ? nd->cap * 2 : (1 << 16); nd->par = (int32_t *)realloc(nd->par, (size_t)nd->cap * 4); nd->mv = (int8_t *)realloc(nd->mv, (size_t)nd->cap); if (!nd->par || !nd->mv) { fprintf(stderr, "oom nodes\n"); exit(1);} }
    nd->par[nd->n] = par; nd->mv[nd->n] = mv; *idx = nd->n; nd->n++;
}
static int node_path(const Nodes *nd, int32_t idx, int8_t *out) {
    int8_t tmp[100000]; int n = 0;
    while (idx > 0) { tmp[n++] = nd->mv[idx]; idx = nd->par[idx]; }
    for (int i = 0; i < n; i++) out[i] = tmp[n - 1 - i];
    return n;
}

/* Exact search: breadth first from the instance, meeting the precomputed ball.
 *
 * Every vertex lies at instance distance k.  The ball stores the exact target
 * distance j of each of its vertices.  So a path through a ball vertex has
 * length k + j, and the minimum of k + j over all ball vertices is the true
 * distance, provided the ball is deep enough: any path of length L has a
 * vertex at instance distance k = max(0, L - balldepth), so exploring to
 * radius r certifies every L <= balldepth + r.
 *
 * Returns 1 if a path was stored in path/plen, and sets *proved to 1 when
 * the radius bound established that no shorter path exists. */
static int search_exact(const State *init, int r, int8_t *path, int *plen, int *proved) {
    Nodes nd = {0};
    int32_t root; nodes_push(&nd, -1, -1, &root);
    Map vis; map_init(&vis, 1 << 20);
    State *cur = (State *)malloc(sizeof(State));
    int32_t *curidx = (int32_t *)malloc(4);
    cur[0] = *init; curidx[0] = root;
    int32_t ncur = 1;
    map_put(&vis, hashstate(init), 1);
    int8_t cm[5]; int cmlen;
    int best = 1 << 30;
    int8_t bestpath[4096];
    int bestlen = 0;
    *proved = 0;

    if (is_goal(init, cm, &cmlen)) {
        for (int i = 0; i < cmlen; i++) path[i] = cm[i];
        *plen = cmlen; *proved = 1; return 1;
    }
    {
        int32_t bi = map_get(&ballmap, hashstate(init));
        if (bi >= 0) {
            int j = recs[bi].dep;
            if (j < best) { best = j; bestlen = backward(bi, bestpath); }
        }
    }
    int rmax = r;
    for (int d = 1; d <= rmax && d < best; d++) {
        int32_t nn = 0;
        int32_t capn = ncur * 16 + 64;
        State *nxt = (State *)malloc((size_t)capn * sizeof(State));
        int32_t *nxtidx = (int32_t *)malloc((size_t)capn * 4);
        for (int32_t i = 0; i < ncur; i++) {
            for (int m = 0; m < 14; m++) {
                State t;
                if (!apply(&cur[i], m, &t)) continue;
                uint64_t fp = hashstate(&t);
                if (map_get(&vis, fp) >= 0) continue;
                int32_t node; nodes_push(&nd, curidx[i], (int8_t)m, &node);
                map_put(&vis, fp, 1);
                int cost = -1;
                int8_t tail[8]; int taillen = 0;
                if (is_goal(&t, cm, &cmlen)) {
                    cost = d + cmlen; memcpy(tail, cm, (size_t)cmlen); taillen = cmlen;
                } else {
                    int32_t bi = map_get(&ballmap, fp);
                    if (bi >= 0) { cost = d + recs[bi].dep; taillen = -1; memcpy(tail, &bi, 4); }
                }
                if (cost >= 0 && cost < best) {
                    best = cost;
                    int f = node_path(&nd, node, bestpath);
                    if (taillen >= 0) { memcpy(bestpath + f, tail, (size_t)taillen); bestlen = f + taillen; }
                    else { int32_t bi; memcpy(&bi, tail, 4); bestlen = f + backward(bi, bestpath + f); }
                }
                if (nn == capn) { capn *= 2; nxt = (State *)realloc(nxt, (size_t)capn * sizeof(State)); nxtidx = (int32_t *)realloc(nxtidx, (size_t)capn * 4); }
                nxt[nn] = t; nxtidx[nn] = node; nn++;
            }
        }
        free(cur); free(curidx); cur = nxt; curidx = nxtidx; ncur = nn;
        if (ncur == 0) break;
    }
    free(cur); free(curidx); free(nd.par); free(nd.mv); free(vis.fp); free(vis.val);
    if (bestlen > 0) {
        memcpy(path, bestpath, (size_t)bestlen);
        *plen = bestlen;
        *proved = (best <= balldepth + r);
        return 1;
    }
    /* nothing within balldepth + r: report the lower bound */
    *proved = 0;
    return 0;
}

/* beam search */
static uint64_t rng_state;
static inline uint64_t xr(void) { uint64_t x = rng_state; x ^= x << 13; x ^= x >> 7; x ^= x << 17; rng_state = x; return x; }

typedef struct { State st; int32_t node; float score; uint32_t key; } Cand;
typedef struct { float score; int32_t idx; } Key;
static float g_ws, g_wm, g_wa, g_noise;
static inline float score_of(const State *s) {
    int a1 = 0, a2 = 0;
    for (int i = 0; i < s->l0; i++) { int c = s->w0[i]; if (c == 1) a1++; else if (c == -1) a1--; else if (c == 2) a2++; else a2--; }
    int b1 = 0, b2 = 0;
    for (int i = 0; i < s->l1; i++) { int c = s->w1[i]; if (c == 1) b1++; else if (c == -1) b1--; else if (c == 2) b2++; else b2--; }
    int ab0 = (a1 < 0 ? -a1 : a1) + (a2 < 0 ? -a2 : a2);
    int ab1 = (b1 < 0 ? -b1 : b1) + (b2 < 0 ? -b2 : b2);
    int mx = s->l0 > s->l1 ? s->l0 : s->l1;
    float f = g_ws * (s->l0 + s->l1) + g_wm * mx + g_wa * (ab0 + ab1);
    if (g_noise > 0) f += g_noise * ((float)(xr() & 0xffff) / 65535.0f);
    return f;
}
static int cmpkey(const void *a, const void *b) {
    float x = ((const Key *)a)->score, y = ((const Key *)b)->score;
    return (x < y) ? -1 : (x > y) ? 1 : 0;
}

static int g_bestlen = 0;   /* diagnostic: shortest total relator length seen */

/* free everything a search allocated; used on the success paths too, which
 * previously leaked about fifty megabytes per solved instance */
#define SEARCH_FREE() do { \
    free(beam); free(cand); free(keys); free(nd.par); free(nd.mv); free(vis.fp); free(vis.val); } while (0)

static int search_beam(const State *init, int W, int S, int8_t *path, int *plen) {
    g_bestlen = init->l0 + init->l1;
    Nodes nd = {0};
    int32_t root; nodes_push(&nd, -1, -1, &root);
    Map vis; map_init(&vis, 1 << 22);
    Cand *beam = (Cand *)malloc((size_t)W * sizeof(Cand));
    Cand *cand = (Cand *)malloc((size_t)W * 14 * sizeof(Cand));
    Key *keys = (Key *)malloc((size_t)W * 14 * sizeof(Key));
    int nb = 1; beam[0].st = *init; beam[0].node = root;
    map_put(&vis, hashstate(init), 1);
    int8_t cm[5]; int cmlen;
    if (is_goal(init, cm, &cmlen)) { for (int i = 0; i < cmlen; i++) path[i] = cm[i]; *plen = cmlen; SEARCH_FREE(); return 1; }
    int32_t bi0 = map_get(&ballmap, hashstate(init));
    if (bi0 >= 0) { *plen = backward(bi0, path); SEARCH_FREE(); return 1; }
    for (int s = 1; s <= S; s++) {
        int nc = 0;
        for (int i = 0; i < nb; i++) {
            for (int m = 0; m < 14; m++) {
                State t;
                if (!apply(&beam[i].st, m, &t)) continue;
                if (t.l0 + t.l1 < g_bestlen) g_bestlen = t.l0 + t.l1;
                uint64_t fp = hashstate(&t);
                if (map_get(&vis, fp) >= 0) continue;
                int32_t node; nodes_push(&nd, beam[i].node, (int8_t)m, &node);
                map_put(&vis, fp, 1);
                if (is_goal(&t, cm, &cmlen)) {
                    int f = node_path(&nd, node, path);
                    for (int j = 0; j < cmlen; j++) path[f + j] = cm[j];
                    *plen = f + cmlen; return 1;
                }
                int32_t bi = map_get(&ballmap, fp);
                if (bi >= 0) {
                    int f = node_path(&nd, node, path);
                    *plen = f + backward(bi, path + f);
                    SEARCH_FREE(); return 1;
                }
                cand[nc].st = t; cand[nc].node = node; cand[nc].score = score_of(&t); nc++;
            }
        }
        if (nc == 0) break;
        for (int i = 0; i < nc; i++) { keys[i].score = cand[i].score; keys[i].idx = (int32_t)i; }
        qsort(keys, (size_t)nc, sizeof(Key), cmpkey);
        {
            int keep = nc > W ? W : nc;
            for (int i = 0; i < keep; i++) {
                beam[i].st = cand[keys[i].idx].st;
                beam[i].node = cand[keys[i].idx].node;
            }
            nb = keep;
        }
    }
    free(beam); free(cand); free(keys); free(nd.par); free(nd.mv); free(vis.fp); free(vis.val);
    return 0;
}

/* ------------------- supermove beam: rotation-aligned concatenation --------
 *
 * A bare multiplication rarely cancels much.  Rotating the other relator to
 * line up its longest match with this relator's end, then multiplying, gives a
 * much larger drop.  In the competition metric a rotation by k costs
 * min(k, n-k) moves, so every macro carries its true move list and cost.
 */
typedef struct { State st; int8_t mv[96]; int nmv; int cost; } Macro;

static inline void rot_left(const int8_t *w, int n, int k, int8_t *out) {
    if (n == 0) return;
    k %= n; if (k < 0) k += n;
    for (int i = 0; i < n; i++) out[i] = w[(i + k) % n];
}

static inline int8_t conj_move(int i, int letter) {
    int g;
    switch (letter) { case 1: g = 6; break; case -1: g = 7; break; case 2: g = 8; break; default: g = 9; }
    return (int8_t)(g + 4 * i);
}

/* cyclic reduce relator i as far as it goes, appending moves */
static void cyc_reduce(int i, State *s, Macro *m, int maxsteps) {
    for (int t = 0; t < maxsteps; t++) {
        const int8_t *w = i ? s->w1 : s->w0;
        int L = i ? s->l1 : s->l0;
        if (L < 2 || w[0] != -w[L - 1]) return;
        int8_t mv = conj_move(i, w[0]);
        apply(s, mv, s);
        if (m->nmv < 96) m->mv[m->nmv++] = mv;
        m->cost++;
    }
}

static int gen_macros(const State *s, Macro *out, int maxout, int topk, int cmax) {
    int n = 0;
    int8_t buf[2 * MAXLEN + 2];
    /* inversions */
    for (int i = 0; i < 2 && n < maxout; i++) {
        out[n].st = *s;
        apply(s, i, &out[n].st);
        out[n].mv[0] = (int8_t)i; out[n].nmv = 1; out[n].cost = 1;
        n++;
    }
    /* pure cyclic reduction */
    for (int i = 0; i < 2 && n < maxout; i++) {
        int L = i ? s->l1 : s->l0;
        const int8_t *w = i ? s->w1 : s->w0;
        if (L >= 2 && w[0] == -w[L - 1]) {
            out[n].st = *s; out[n].nmv = 0; out[n].cost = 0;
            cyc_reduce(i, &out[n].st, &out[n], 6);
            if (out[n].nmv > 0) n++;
        }
    }
    /* rotation-aligned concatenation */
    for (int i = 0; i < 2; i++) {
        int j = 1 - i;
        const int8_t *ri = i ? s->w1 : s->w0;
        int ni = i ? s->l1 : s->l0;
        const int8_t *rj = j ? s->w1 : s->w0;
        int nj = j ? s->l1 : s->l0;
        if (nj == 0) continue;
        for (int sign = 0; sign < 2; sign++) {
            /* score every rotation, keep the best few */
            int bestk[8]; int bestgain[8]; int nb = 0;
            for (int k = 0; k < nj; k++) {
                int cost = (k < nj - k ? k : nj - k) + 1;
                if (cost > cmax) continue;
                int8_t rot[MAXLEN];
                rot_left(rj, nj, k, rot);
                int m2 = 0;
                memcpy(buf, ri, (size_t)ni); m2 = ni;
                if (sign == 0) { memcpy(buf + m2, rot, (size_t)nj); m2 += nj; }
                else { for (int t = 0; t < nj; t++) buf[m2 + t] = (int8_t)(-rot[nj - 1 - t]); m2 += nj; }
                int8_t red[2 * MAXLEN];
                memcpy(red, buf, (size_t)m2);
                int nl = fred(red, m2);
                int gain = ni - nl - cost;
                if (gain <= 0) continue;
                /* insertion sort, keep best topk by gain */
                int pos = nb;
                while (pos > 0 && bestgain[pos - 1] < gain) pos--;
                if (nb == topk && pos >= topk) continue;
                for (int t = (nb < topk ? nb : topk - 1); t > pos; t--) { bestk[t] = bestk[t - 1]; bestgain[t] = bestgain[t - 1]; }
                bestk[pos] = k; bestgain[pos] = gain;
                if (nb < topk) nb++;
            }
            for (int b = 0; b < nb && n < maxout; b++) {
                int k = bestk[b];
                Macro *m = &out[n];
                m->nmv = 0; m->cost = 0;
                State t;
                memcpy(&t, s, sizeof(State));
                /* rotate relator j by k, one conjugation per step */
                for (int step = 0; step < k; step++) {
                    const int8_t *w = j ? t.w1 : t.w0;
                    int L = j ? t.l1 : t.l0;
                    int8_t mv = conj_move(j, w[0]);
                    apply(&t, mv, &t);
                    if (m->nmv < 96) m->mv[m->nmv++] = mv;
                    m->cost++;
                }
                int mul = (i == 0) ? (sign == 0 ? 2 : 3) : (sign == 0 ? 4 : 5);
                apply(&t, mul, &t);
                if (m->nmv < 96) m->mv[m->nmv++] = (int8_t)mul;
                m->cost++;
                cyc_reduce(i, &t, m, 4);
                m->st = t;
                n++;
            }
        }
    }
    return n;
}

#define SEARCH_FREE_S() do { \
    free(beam); free(cand); free(keys); free(macros); free(nd.par); free(nd.mv); free(vis.fp); free(vis.val); } while (0)

static int search_sbeam(const State *init, int W, int S, int topk, int cmax, int8_t *path, int *plen) {
    g_bestlen = init->l0 + init->l1;
    Nodes nd = {0};
    int32_t root; nodes_push(&nd, -1, -1, &root);
    Map vis; map_init(&vis, 1 << 22);
    Cand *beam = (Cand *)malloc((size_t)W * sizeof(Cand));
    Cand *cand = (Cand *)malloc((size_t)W * 64 * sizeof(Cand));
    Key *keys = (Key *)malloc((size_t)W * 64 * sizeof(Key));
    Macro *macros = (Macro *)malloc(64 * sizeof(Macro));
    int nb = 1; beam[0].st = *init; beam[0].node = root;
    map_put(&vis, hashstate(init), 1);
    int8_t cm[5]; int cmlen;
    if (is_goal(init, cm, &cmlen)) { for (int i = 0; i < cmlen; i++) path[i] = cm[i]; *plen = cmlen; SEARCH_FREE_S(); return 1; }
    int32_t bi0 = map_get(&ballmap, hashstate(init));
    if (bi0 >= 0) { *plen = backward(bi0, path); SEARCH_FREE_S(); return 1; }
    for (int s = 1; s <= S; s++) {
        int nc = 0;
        for (int i = 0; i < nb; i++) {
            int nm = gen_macros(&beam[i].st, macros, 64, topk, cmax);
            for (int q = 0; q < nm; q++) {
                State t = macros[q].st;
                if (t.l0 + t.l1 < g_bestlen) g_bestlen = t.l0 + t.l1;
                uint64_t fp = hashstate(&t);
                if (map_get(&vis, fp) >= 0) continue;
                /* chain the macro's real moves as intermediate nodes */
                int32_t cur = beam[i].node;
                for (int z = 0; z < macros[q].nmv; z++) {
                    int32_t nx; nodes_push(&nd, cur, macros[q].mv[z], &nx); cur = nx;
                }
                map_put(&vis, fp, 1);
                if (is_goal(&t, cm, &cmlen)) {
                    int f = node_path(&nd, cur, path);
                    for (int z = 0; z < cmlen; z++) path[f + z] = cm[z];
                    *plen = f + cmlen; SEARCH_FREE_S(); return 1;
                }
                int32_t bi = map_get(&ballmap, fp);
                if (bi >= 0) {
                    int f = node_path(&nd, cur, path);
                    *plen = f + backward(bi, path + f);
                    SEARCH_FREE_S(); return 1;
                }
                cand[nc].st = t; cand[nc].node = cur; cand[nc].score = score_of(&t); nc++;
            }
        }
        if (nc == 0) break;
        for (int i = 0; i < nc; i++) { keys[i].score = cand[i].score; keys[i].idx = (int32_t)i; }
        qsort(keys, (size_t)nc, sizeof(Key), cmpkey);
        int keep = nc > W ? W : nc;
        for (int i = 0; i < keep; i++) { beam[i].st = cand[keys[i].idx].st; beam[i].node = cand[keys[i].idx].node; }
        nb = keep;
    }
    free(beam); free(cand); free(keys); free(macros); free(nd.par); free(nd.mv); free(vis.fp); free(vis.val);
    return 0;
}

static void print_moves(FILE *f, const int8_t *p, int n) {
    fputc('[', f);
    for (int i = 0; i < n; i++) { if (i) fputc(',', f); fprintf(f, "%d", (int)p[i]); }
    fputc(']', f);
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: %s mode ...\n", argv[0]); return 2; }
    const char *mode = argv[1];
    if (!strcmp(mode, "sizes")) {
        int D = atoi(argv[2]);
        build_ball(D, 1);
        return 0;
    }
    if (!strcmp(mode, "ball")) {
        int D = atoi(argv[2]);
        build_ball(D, 1);
        save_ball(argv[3]);
        fprintf(stderr, "saved %d states depth %d\n", nrec, D);
        return 0;
    }
    if (!strcmp(mode, "replay")) {
        /* replay: lines "r0|r1|moves" -> final state */
        FILE *f = stdin;
        char line[16384];
        while (fgets(line, sizeof line, f)) {
            char *p1 = strchr(line, '|');
            if (!p1) continue;
            *p1 = 0;
            char *p2 = strchr(p1 + 1, '|');
            if (!p2) continue;
            *p2 = 0;
            State s; memset(&s, 0, sizeof s);
            s.l0 = (int16_t)parse_word(line, s.w0);
            s.l1 = (int16_t)parse_word(p1 + 1, s.w1);
            char *pm = p2 + 1;
            while (*pm) {
                while (*pm == ' ' || *pm == ',') pm++;
                if (*pm == '\n' || !*pm) break;
                char *e; long v = strtol(pm, &e, 10);
                if (e == pm) break;
                { State before = s; apply(&s, (int)v, &s);
                  if (s.l0 == before.l0 && s.l1 == before.l1 &&
                      !memcmp(s.w0, before.w0, (size_t)before.l0) &&
                      !memcmp(s.w1, before.w1, (size_t)before.l1))
                    fprintf(stderr, "REPLAY-SKIPPED move %ld at %s (relator would exceed MAXLEN=%d)\n", v, line, MAXLEN); }
                pm = e;
            }
            printf("%d|%d:", s.l0, s.l1);
            for (int i = 0; i < s.l0; i++) printf("%s%d", i ? "," : "", (int)s.w0[i]);
            printf("|");
            for (int i = 0; i < s.l1; i++) printf("%s%d", i ? "," : "", (int)s.w1[i]);
            printf("\n");
            fflush(stdout);
        }
        return 0;
    }
    if (!strcmp(mode, "sbeam")) {
        load_ball(argv[2]);
        int W = atoi(argv[3]), S = atoi(argv[4]), topk = atoi(argv[5]), cmax = atoi(argv[6]);
        FILE *out = fopen(argv[7], "w");
        if (!out) { perror("out"); return 1; }
        const char *infile = argv[8];
        rng_state = (uint64_t)strtoull(argv[9], NULL, 10) * 2862933555777941757ULL + 3037000493ULL;
        if (rng_state == 0) rng_state = 88172645463325252ULL;
        g_ws = 1; g_wm = 0; g_wa = 0; g_noise = 0;
        Inst *insts; int n = read_insts(infile, &insts);
        int8_t *path = (int8_t *)malloc(100000);
        for (int i = 0; i < n; i++) {
            int plen = 0, proved = 0;
            int ok = search_sbeam(&insts[i].st, W, S, topk, cmax, path, &plen);
            if (ok) {
                int work = insts[i].st.l0 + insts[i].st.l1;
                State s = insts[i].st;
                for (int k = 0; k < plen; k++) { apply(&s, path[k], &s); work += s.l0 + s.l1; }
                if (!(s.l0 == 1 && s.l1 == 1 && s.w0[0] == 1 && s.w1[0] == 2)) {
                    fprintf(stderr, "SELFCHECK FAILED %s\n", insts[i].id);
                    fprintf(out, "%s\t-1\n", insts[i].id); fflush(out); continue;
                }
                fprintf(out, "%s\t%d\t%d\t", insts[i].id, plen, work);
                print_moves(out, path, plen);
                fputc('\t', out); fputc('-', out); fputc('\n', out);
            } else {
                fprintf(out, "%s\t-1\t%d\n", insts[i].id, g_bestlen);
            }
            fflush(out);
        }
        fprintf(stderr, "capped_moves=%ld over %d instances\n", g_cap_hits, n);
        fclose(out);

        return 0;
    }
    if (!strcmp(mode, "exact") || !strcmp(mode, "beam")) {
        load_ball(argv[2]);
        int exact = !strcmp(mode, "exact");
        FILE *out = fopen(argv[exact ? 4 : 5], "w");
        if (!out) { perror("out"); return 1; }
        int r = 0, W = 0, S = 0;
        const char *infile = NULL;
        if (exact) { r = atoi(argv[3]); infile = argv[5]; }
        else {
            W = atoi(argv[3]); S = atoi(argv[4]); infile = argv[6];
            rng_state = (uint64_t)strtoull(argv[7], NULL, 10) * 2862933555777941757ULL + 3037000493ULL;
            if (rng_state == 0) rng_state = 88172645463325252ULL;
            g_ws = (float)atof(argv[8]); g_wm = (float)atof(argv[9]);
            g_wa = (float)atof(argv[10]); g_noise = (float)atof(argv[11]);
        }
        Inst *insts; int n = read_insts(infile, &insts);
        int8_t *path = (int8_t *)malloc(100000);
        for (int i = 0; i < n; i++) {
            int plen = 0, proved = 0;
            int ok = exact ? search_exact(&insts[i].st, r, path, &plen, &proved)
                           : search_beam(&insts[i].st, W, S, path, &plen);
            if (ok) {
                int work = insts[i].st.l0 + insts[i].st.l1;
                State s = insts[i].st;
                for (int k = 0; k < plen; k++) { apply(&s, path[k], &s); work += s.l0 + s.l1; }
                /* self-check before anything is reported: the endpoint must be
                 * exactly [[1],[2]].  A wrong path must never leave the engine. */
                if (!(s.l0 == 1 && s.l1 == 1 && s.w0[0] == 1 && s.w1[0] == 2)) {
                    fprintf(stderr, "SELFCHECK FAILED %s final=[%d|%d]\n", insts[i].id, s.l0, s.l1);
                    fprintf(out, "%s\t-1\n", insts[i].id);
                    fflush(out);
                    continue;
                }
                fprintf(out, "%s\t%d\t%d\t", insts[i].id, plen, work);
                print_moves(out, path, plen);
                fputc('\t', out);
                fputc(proved ? 'P' : '-', out);
                fputc('\n', out);
            } else {
                fprintf(out, "%s\t-1\t%d\n", insts[i].id, g_bestlen);
            }
            fflush(out);
        }
        fprintf(stderr, "capped_moves=%ld over %d instances\n", g_cap_hits, n);
        fclose(out);
        return 0;
    }
    fprintf(stderr, "unknown mode %s\n", mode);
    return 2;
}
