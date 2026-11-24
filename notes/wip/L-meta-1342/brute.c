#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
/* brute n s u1 v1 u2 v2 ... : enumerate all NF circuits (exactly s gates, AND/OR of two
   distinct earlier wires, every non-last gate read later, output last); print whether any
   computes f, and for each k whether some circuit computing f has lowest junk AND at k and
   another junk AND above it. Truth tables on 2^n <= 64 inputs. */
static int n, s;
static uint64_t tt[64], f, nf;
static int isand[64], used[64];
static int found[64], anyf;
static void rec(int j) {
  if (j == s) {
    if (tt[n + s - 1] != f) return;
    for (int q = 0; q < s - 1; q++) if (!used[n + q]) return;
    anyf = 1;
    int first = -1, cnt = 0;
    for (int q = 0; q < s; q++) if (isand[q] && (tt[n + q] & nf)) { if (first < 0) first = q; cnt++; }
    if (cnt >= 2) found[first] = 1;
    return;
  }
  int unused = 0;
  for (int q = 0; q < j; q++) if (!used[n + q]) unused++;
  int rafter = s - 1 - j;
  for (int b = 0; b < n + j; b++)
    for (int a = 0; a < b; a++) {
      int nu = unused - ((a >= n && !used[a]) ? 1 : 0) - ((b >= n && !used[b]) ? 1 : 0) + 1;
      if (rafter >= 1 && nu > rafter + 1) continue;
      used[a]++; used[b]++;
      for (int o = 0; o < 2; o++) {
        isand[j] = o;
        tt[n + j] = o ? (tt[a] & tt[b]) : (tt[a] | tt[b]);
        rec(j + 1);
      }
      used[a]--; used[b]--;
    }
}
int main(int argc, char **argv) {
  n = atoi(argv[1]); s = atoi(argv[2]);
  int N = 1 << n;
  uint64_t full = (N == 64) ? ~0ULL : ((1ULL << N) - 1);
  for (int i = 0; i < n; i++) { tt[i] = 0; for (int m = 0; m < N; m++) if ((m >> i) & 1) tt[i] |= 1ULL << m; }
  f = 0;
  for (int m = 0; m < N; m++) {
    int v = 0;
    for (int e = 3; e + 1 < argc; e += 2) { int u = atoi(argv[e]), w = atoi(argv[e + 1]); if (((m >> u) & 1) && ((m >> w) & 1)) v = 1; }
    if (v) f |= 1ULL << m;
  }
  nf = full ^ f;
  rec(0);
  printf("%d", anyf);
  for (int k = 0; k < s; k++) if (found[k]) printf(" %d", k);
  printf("\n");
  return 0;
}
