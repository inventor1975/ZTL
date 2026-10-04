/* gate_bench.c — latency of the ZRuntimeGate gate (lean/ZRuntimeGate.lean): one pass in the lazy (strong
   Kleene) register, pass iff T. Same tables as the Lean file. Formulas are stored in post-order (children before
   parents), so one left-to-right sweep evaluates them — the cost theorem's "one step per node".
   Measures, on THIS machine (x86, single thread): per-check latency p50/p99 for batches of N simultaneous checks
   (N = 10, 100, 1000, 10000) at formula sizes 31, 255, 1023; and the incremental re-check after one atom changes
   (only the nodes on paths from that atom's occurrences to the root are recomputed).
   Build: cc -O2 -o gate_bench gate_bench.c      Run: ./gate_bench */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <time.h>

enum { T = 0, F = 1, Z = 2 };
enum { ATOM, NEG, AND, OR, IMP };
typedef struct { uint8_t op; int32_t a, b, parent; } Node;

static uint8_t knot(uint8_t x) { return x == T ? F : x == F ? T : Z; }
static uint8_t kand(uint8_t x, uint8_t y) { if (x == F || y == F) return F; if (x == T && y == T) return T; return Z; }
static uint8_t kor(uint8_t x, uint8_t y) { if (x == T || y == T) return T; if (x == F && y == F) return F; return Z; }
static uint8_t kimp(uint8_t x, uint8_t y) { return kor(knot(x), y); }

static uint64_t rng = 88172645463325252ull;
static uint64_t rnd(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }

/* random formula with n nodes (n odd for a full binary shape), post-order, atoms over `natoms` */
static int build(Node *f, int *pos, int n, int natoms) {
    if (n <= 1) { int i = (*pos)++; f[i].op = ATOM; f[i].a = (int)(rnd() % natoms); f[i].b = -1; return i; }
    if (n == 2 || rnd() % 8 == 0) { int c = build(f, pos, n - 1, natoms); int i = (*pos)++; f[i].op = NEG; f[i].a = c; f[i].b = -1; f[c].parent = i; return i; }
    int half = (n - 1) / 2; int left = half > 0 ? 1 + 2 * (int)(rnd() % half) : 1;
    if (left > n - 2) left = n - 2; if (left < 1) left = 1;
    int l = build(f, pos, left, natoms), r = build(f, pos, n - 1 - left, natoms);
    int i = (*pos)++; f[i].op = AND + (int)(rnd() % 3); f[i].a = l; f[i].b = r; f[l].parent = i; f[r].parent = i; return i;
}

static uint8_t eval(const Node *f, int n, const uint8_t *mark, uint8_t *val) {
    for (int i = 0; i < n; i++) {
        const Node *x = &f[i];
        switch (x->op) {
            case ATOM: val[i] = mark[x->a]; break;
            case NEG:  val[i] = knot(val[x->a]); break;
            case AND:  val[i] = kand(val[x->a], val[x->b]); break;
            case OR:   val[i] = kor(val[x->a], val[x->b]); break;
            default:   val[i] = kimp(val[x->a], val[x->b]); break;
        }
    }
    return val[n - 1];
}

/* incremental: atom `atom` changed; walk up from each of its occurrences, recompute, stop when unchanged */
/* occurrence index (atom -> its leaf positions), built once with the formula — what makes the re-check
   incremental: it starts at the changed atom's leaves instead of scanning the formula */
typedef struct { int *pos; int cnt; } Occ;

static uint8_t recheck(const Node *f, int n, const Occ *occ, const uint8_t *mark, uint8_t *val, int atom) {
    for (int q = 0; q < occ[atom].cnt; q++) {
        int i = occ[atom].pos[q];
        int j = i; uint8_t nv = mark[atom];
        while (1) {
            if (val[j] == nv) break;
            val[j] = nv;
            int p = f[j].parent; if (p < 0) break;
            const Node *x = &f[p];
            nv = x->op == NEG ? knot(val[x->a]) : x->op == AND ? kand(val[x->a], val[x->b])
               : x->op == OR ? kor(val[x->a], val[x->b]) : kimp(val[x->a], val[x->b]);
            j = p;
        }
    }
    return val[n - 1];
}

static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec * 1e9 + t.tv_nsec; }
static int cmpd(const void *a, const void *b) { double x = *(const double *)a, y = *(const double *)b; return x < y ? -1 : x > y; }

int main(void) {
    const int sizes[] = { 31, 255, 1023 }, Ns[] = { 10, 100, 1000, 10000 }, natoms = 64;
    printf("size  N       batch_total_us  per_check_p50_ns  per_check_p99_ns  incr_p50_ns  incr_p99_ns  passes\n");
    for (int si = 0; si < 3; si++) for (int ni = 0; ni < 4; ni++) {
        int S = sizes[si], N = Ns[ni];
        Node *fs = malloc(sizeof(Node) * S * N); uint8_t *vals = malloc(S * N);
        Occ *occs = calloc((size_t)N * natoms, sizeof(Occ)); int *occbuf = malloc(sizeof(int) * S * N);
        uint8_t *marks = malloc(natoms * N); double *lat = malloc(sizeof(double) * N), *inc = malloc(sizeof(double) * N);
        for (int k = 0; k < N; k++) {
            Node *f = fs + (size_t)k * S; int pos = 0;
            for (int i = 0; i < S; i++) f[i].parent = -1;
            build(f, &pos, S, natoms);
            Occ *oc = occs + (size_t)k * natoms; int *buf = occbuf + (size_t)k * S, used = 0;
            for (int a = 0; a < natoms; a++) {                 /* index: leaves of each atom */
                oc[a].pos = buf + used; oc[a].cnt = 0;
                for (int i = 0; i < S; i++) if (f[i].op == ATOM && f[i].a == a) oc[a].pos[oc[a].cnt++] = i;
                used += oc[a].cnt;
            }
            for (int a = 0; a < natoms; a++) { uint64_t r = rnd() % 10; marks[k * natoms + a] = r < 6 ? T : r < 8 ? F : Z; }
        }
        int passes = 0; double t0 = now();
        for (int k = 0; k < N; k++) {
            double a = now();
            passes += eval(fs + (size_t)k * S, S, marks + k * natoms, vals + (size_t)k * S) == T;
            lat[k] = now() - a;
        }
        double batch = now() - t0;
        for (int k = 0; k < N; k++) {           /* one atom changes (a Z gets checked T), incremental re-check */
            int atom = (int)(rnd() % natoms); marks[k * natoms + atom] = T;
            double a = now();
            recheck(fs + (size_t)k * S, S, occs + (size_t)k * natoms, marks + k * natoms, vals + (size_t)k * S, atom);
            inc[k] = now() - a;
            uint8_t *chk = malloc(S);                          /* the incremental result must equal a full pass */
            if (eval(fs + (size_t)k * S, S, marks + k * natoms, chk) != vals[(size_t)k * S + S - 1]) {
                fprintf(stderr, "MISMATCH incremental vs full at size %d check %d\n", S, k); return 1; }
            free(chk);
        }
        qsort(lat, N, sizeof(double), cmpd); qsort(inc, N, sizeof(double), cmpd);
        printf("%-5d %-7d %-15.1f %-17.0f %-17.0f %-12.0f %-12.0f %d/%d\n", S, N, batch / 1e3,
               lat[N / 2], lat[(int)(N * 0.99)], inc[N / 2], inc[(int)(N * 0.99)], passes, N);
        free(fs); free(vals); free(occs); free(occbuf); free(marks); free(lat); free(inc);
    }
    return 0;
}
