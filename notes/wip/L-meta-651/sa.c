#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define NIN 10
#define W 16
#define MAXG 40

static int S;
static int allow_not;
static uint64_t tt[NIN + MAXG][W];
static uint64_t target[W];
static int op[MAXG], ia[MAXG], ib[MAXG];
static uint64_t rng_state;

static inline uint64_t rng(void) {
    rng_state ^= rng_state << 13; rng_state ^= rng_state >> 7; rng_state ^= rng_state << 17;
    return rng_state;
}
static inline int rnd(int n) { return (int)(rng() % (uint64_t)n); }
static inline double rndf(void) { return (rng() >> 11) * (1.0 / 9007199254740992.0); }

static const int E[15][2] = {{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}};

static void init_inputs(void) {
    for (int t = 0; t < 1024; t++) {
        int fv = 0;
        for (int e = 0; e < 15; e++) if (((t >> E[e][0]) & 1) && ((t >> E[e][1]) & 1)) fv = 1;
        if (fv) target[t >> 6] |= (1ULL << (t & 63));
        for (int v = 0; v < NIN; v++) if ((t >> v) & 1) tt[v][t >> 6] |= (1ULL << (t & 63));
    }
}

static void eval_from(int g0) {
    for (int g = g0; g < S; g++) {
        uint64_t *o = tt[NIN + g], *a = tt[ia[g]], *b = tt[ib[g]];
        if (op[g] == 0) for (int w = 0; w < W; w++) o[w] = a[w] & b[w];
        else if (op[g] == 1) for (int w = 0; w < W; w++) o[w] = a[w] | b[w];
        else for (int w = 0; w < W; w++) o[w] = ~a[w];
    }
}

static int cost(void) {
    int c = 0;
    uint64_t *o = tt[NIN + S - 1];
    for (int w = 0; w < W; w++) c += __builtin_popcountll(o[w] ^ target[w]);
    return c;
}

static void random_gate(int g) {
    int n = NIN + g;
    op[g] = allow_not ? rnd(3) : rnd(2);
    ia[g] = rnd(n); ib[g] = rnd(n);
}

int main(int argc, char **argv) {
    S = atoi(argv[1]);
    allow_not = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], 0, 10);
    double secs = atof(argv[4]);
    double T0 = argc > 5 ? atof(argv[5]) : 2.0;
    long restart_iters = argc > 6 ? atol(argv[6]) : 20000000L;
    int count_mode = argc > 7 ? atoi(argv[7]) : 0;
    int found = 0;
    int max_not = argc > 8 ? atoi(argv[8]) : 1000;
    int dump_thr = argc > 9 ? atoi(argv[9]) : -1;
    int bop[MAXG], bia[MAXG], bib[MAXG];
    rng_state = seed * 2654435761ULL + 88172645463325252ULL;
    init_inputs();
    clock_t start = clock();
    long total = 0;
    int best_ever = 1 << 30;
    int restarts = 0;
    while ((double)(clock() - start) / CLOCKS_PER_SEC < secs) {
        restarts++;
        for (int g = 0; g < S; g++) { random_gate(g); if (op[g] == 2) op[g] = rnd(2); }
        int nnot = 0;
        eval_from(0);
        int c = cost();
        int best = c;
        for (long it = 0; it < restart_iters; it++) {
            double T = T0 * (1.0 - (double)it / restart_iters) + 0.05;
            int g = rnd(S);
            int so = op[g], sa = ia[g], sb = ib[g];
            int kind = rnd(3);
            int n = NIN + g;
            if (kind == 0) {
                int no = allow_not ? rnd(3) : rnd(2);
                if (no == 2 && so != 2 && nnot >= max_not) no = rnd(2);
                op[g] = no;
            }
            else if (kind == 1) ia[g] = rnd(n);
            else ib[g] = rnd(n);
            eval_from(g);
            int c2 = cost();
            if (c2 <= c || rndf() < exp((c - c2) / T)) {
                c = c2;
                nnot += (op[g] == 2) - (so == 2);
                if (c < best) { best = c; memcpy(bop, op, sizeof(int)*S); memcpy(bia, ia, sizeof(int)*S); memcpy(bib, ib, sizeof(int)*S); }
                if (c == 0) {
                    printf("FOUND S=%d seed=%llu restart=%d it=%ld\n", S, (unsigned long long)seed, restarts, it);
                    for (int k = 0; k < S; k++) printf("%s %d %d\n", op[k]==0?"and":op[k]==1?"or":"not", ia[k], ib[k]);
                    fflush(stdout);
                    found++;
                    if (!count_mode) return 0;
                    break;
                }
            } else {
                op[g] = so; ia[g] = sa; ib[g] = sb;
                eval_from(g);
            }
            total++;
        }
        if (best < best_ever) best_ever = best;
        if (best <= dump_thr && best > 0) {
            printf("NEAR %d\n", best);
            for (int k = 0; k < S; k++) printf("%s %d %d\n", bop[k]==0?"and":bop[k]==1?"or":"not", bia[k], bib[k]);
        }
        printf("restart %d found %d best %d best_ever %d total_iters %ld time %.0f\n", restarts, found, best, best_ever, total, (double)(clock() - start) / CLOCKS_PER_SEC);
        fflush(stdout);
    }
    return 1;
}
