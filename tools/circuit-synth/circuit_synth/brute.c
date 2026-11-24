/* Exhaustive minimum circuit sizes for small n, independent of the SAT encodings.
 *
 *   brute table N SMAX MAXNOT
 *       N <= 4. For every truth table tt (0 .. 2^(2^N)-1) prints "tt m0 m1 ... mMAXNOT":
 *       mc = least number of gates of a circuit with at most c NOT gates having tt on one of
 *       its wires (inputs count, size 0), or -1 if more than SMAX gates are needed.
 *   brute multi N SMAX MAXNOT t1 t2 ...
 *       N <= 6. Least s <= SMAX such that one circuit with s gates and at most MAXNOT NOT gates
 *       has every ti (hex) on some wire; -1 if none.
 *
 * Circuits enumerated: gate = AND or OR of two distinct earlier wires, or NOT of one earlier
 * wire (when NOTs remain). The only pruning: a gate whose truth table equals that of an
 * existing wire is skipped (such a gate can always be deleted, its readers redirected).
 * Degenerate Lean gates (0 or 1 inputs, missing wires) are not needed for minimum sizes of
 * non-constant functions; the RAW SAT encoding covers them separately.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

static int n, smax, maxnot, ntarg;
static uint64_t mask, tt[80], targ[16];
static signed char *best; /* best[f * (maxnot+1) + c] */
static int found = -1, have[16];

static void rec_table(int j, int nots) {
  int W = n + j;
  for (int b = 0; b < W; b++) {
    for (int k = 0; k < 3; k++) {
      int amax = (k == 2) ? 1 : b;
      if (k == 2 && nots >= maxnot) continue;
      for (int a = 0; a < amax; a++) {
        uint64_t g;
        if (k == 0) g = tt[a] & tt[b];
        else if (k == 1) g = tt[a] | tt[b];
        else g = ~tt[b] & mask;
        int dup = 0;
        for (int w = 0; w < W; w++) if (tt[w] == g) { dup = 1; break; }
        if (dup) continue;
        int c = nots + (k == 2);
        signed char *p = &best[g * (maxnot + 1) + c];
        if (*p < 0 || *p > j + 1) *p = j + 1;
        if (j + 1 < smax) { tt[W] = g; rec_table(j + 1, c); }
      }
    }
  }
}

static void rec_multi(int j, int nots, int got) {
  if (got == ntarg) { if (found < 0 || j < found) found = j; return; }
  if (j >= smax || (found >= 0 && j + 1 >= found)) return;
  int W = n + j;
  for (int b = 0; b < W; b++) {
    for (int k = 0; k < 3; k++) {
      int amax = (k == 2) ? 1 : b;
      if (k == 2 && nots >= maxnot) continue;
      for (int a = 0; a < amax; a++) {
        uint64_t g;
        if (k == 0) g = tt[a] & tt[b];
        else if (k == 1) g = tt[a] | tt[b];
        else g = ~tt[b] & mask;
        int dup = 0;
        for (int w = 0; w < W; w++) if (tt[w] == g) { dup = 1; break; }
        if (dup) continue;
        int add = 0, which[16], nw = 0;
        for (int q = 0; q < ntarg; q++) if (!have[q] && targ[q] == g) { have[q] = 1; which[nw++] = q; add++; }
        tt[W] = g;
        rec_multi(j + 1, nots + (k == 2), got + add);
        for (int q = 0; q < nw; q++) have[which[q]] = 0;
      }
    }
  }
}

int main(int argc, char **argv) {
  if (argc < 5) { fprintf(stderr, "usage: brute table|multi N SMAX MAXNOT [targets]\n"); return 2; }
  n = atoi(argv[2]); smax = atoi(argv[3]); maxnot = atoi(argv[4]);
  int N = 1 << n;
  mask = (N == 64) ? ~0ULL : ((1ULL << N) - 1);
  for (int i = 0; i < n; i++) {
    tt[i] = 0;
    for (int m = 0; m < N; m++) if ((m >> i) & 1) tt[i] |= 1ULL << m;
  }
  if (!strcmp(argv[1], "table")) {
    if (n > 4) { fprintf(stderr, "table mode needs N <= 4\n"); return 2; }
    uint64_t F = 1ULL << N;
    best = malloc(F * (maxnot + 1));
    memset(best, -1, F * (maxnot + 1));
    for (int i = 0; i < n; i++) for (int c = 0; c <= maxnot; c++) best[tt[i] * (maxnot + 1) + c] = 0;
    rec_table(0, 0);
    for (uint64_t f = 0; f < F; f++) {
      printf("%llu", (unsigned long long)f);
      int cur = -1;
      for (int c = 0; c <= maxnot; c++) {
        int v = best[f * (maxnot + 1) + c];
        if (v >= 0 && (cur < 0 || v < cur)) cur = v;
        printf(" %d", cur);
      }
      printf("\n");
    }
    return 0;
  }
  ntarg = argc - 5;
  int got = 0;
  for (int q = 0; q < ntarg; q++) {
    targ[q] = strtoull(argv[5 + q], 0, 16);
    have[q] = 0;
    for (int i = 0; i < n; i++) if (tt[i] == targ[q]) { have[q] = 1; got++; break; }
  }
  rec_multi(0, 0, got);
  printf("%d\n", found);
  return 0;
}
