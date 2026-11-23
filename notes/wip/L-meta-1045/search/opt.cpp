// optimistic product costs with OR-sharing lower bound: top-level product of m<=4 factors OR(W_i) v f_{G-W_i}
#include <bits/stdc++.h>
using namespace std;
int n; int adj[16];
int memoOld[1 << 12], memoNew[1 << 12];
int edgesIn(int U) { int e = 0; for (int u = 0; u < n; u++) if (U >> u & 1) e += __builtin_popcount(adj[u] & U); return e / 2; }
int degIn(int t, int U) { return __builtin_popcount(adj[t] & U); }
int tauOf(int U) { int best = 100; for (int T = U;; T = (T - 1) & U) { bool ok = true; for (int u = 0; u < n && ok; u++) if (U >> u & 1) if ((adj[u] & U & ~T) && !(T >> u & 1)) ok = false; if (ok) best = min(best, __builtin_popcount(T)); if (T == 0) break; } return best; }
vector<int> misOf(int U) { vector<int> res; for (int I = U;; I = (I - 1) & U) { bool indep = true; for (int u = 0; u < n && indep; u++) if (I >> u & 1) if (adj[u] & I) indep = false; if (indep) { bool mx = true; for (int v = 0; v < n && mx; v++) if ((U >> v & 1) && !(I >> v & 1)) if (!(adj[v] & I)) mx = false; if (mx) res.push_back(I); } if (I == 0) break; } return res; }
// standard-only OLD (lower bound for inner: use target-based optimistic: inner cost >= ? we use min(standard recursion))
int OLDstd(int U) {
    if (memoOld[U] >= 0) return memoOld[U];
    int E = edgesIn(U); if (E == 0) return memoOld[U] = 0;
    int best = 1000;
    for (int t = 0; t < n; t++) if (U >> t & 1) { int d = degIn(t, U); if (d == E) best = min(best, d); else if (d > 0) best = min(best, d + 2 + OLDstd(U & ~(1 << t))); }
    // allow inner saving of 1 optimistically if graph is not a star (models nested products)
    return memoOld[U] = best;
}
int main() {
    string line; int total = 0, bad = 0;
    while (getline(cin, line)) {
        if (line.empty()) continue;
        istringstream is(line); string es; is >> n >> es;
        for (int i = 0; i < n; i++) adj[i] = 0; int E = 0;
        for (size_t p = 0; p + 1 < es.size(); p += 3) { int u = es[p] - '0', v = es[p + 1] - '0'; adj[u] |= 1 << v; adj[v] |= 1 << u; E++; }
        int V = (1 << n) - 1;
        for (int U = 0; U <= V; U++) memoOld[U] = -1;
        int tau = tauOf(V), target = E + 2 * tau - 2;
        vector<int> mis = misOf(V); int M = mis.size();
        vector<int> cand, cm, inner;
        for (int W = 1; W <= V; W++) if (__builtin_popcount(W) >= 2) {
            int c = 0; for (int i = 0; i < M; i++) if (!(mis[i] & W)) c |= 1 << i;
            if (!c) continue;
            cand.push_back(W); cm.push_back(c);
            int R = V & ~W; int e = edgesIn(R);
            // optimistic inner: standard cost minus 1 (possible nested saving) if not a star
            int ic = 0; if (e > 0) { ic = OLDstd(R); bool star = false; for (int t = 0; t < n; t++) if ((R >> t & 1) && degIn(t, R) == e) star = true; if (!star) ic -= 1; }
            inner.push_back(ic);
        }
        int full = (1 << M) - 1; int C = cand.size(); int best = 1000; string bw;
        auto eval = [&](vector<int>& ids) {
            int u = 0, cov = 0; for (int i : ids) { u |= cand[i]; cov |= cm[i]; }
            if (cov != full) return;
            int m = ids.size();
            int orc = max(__builtin_popcount(u) - 1, m);
            set<int> Rs; int joins = 0, innerc = 0;
            for (int i : ids) { int R = V & ~cand[i]; if (edgesIn(R) > 0) { joins++; if (!Rs.count(R)) { Rs.insert(R); innerc += inner[i]; } } }
            int old = orc + innerc + joins + (m - 1);
            if (old + 1 < best) { best = old + 1; bw = ""; for (int i : ids) bw += to_string(cand[i]) + " "; }
        };
        for (int a = 0; a < C; a++) for (int b = a + 1; b < C; b++) {
            vector<int> v = {a, b}; eval(v);
            for (int c = b + 1; c < C; c++) { vector<int> w = {a, b, c}; eval(w);
                if (n <= 7) for (int d = c + 1; d < C; d++) { vector<int> x = {a, b, c, d}; eval(x); } }
        }
        total++;
        if (best < target) { bad++; printf("OPTBAD %s target=%d optnew=%d W=%s\n", es.c_str(), target, best, bw.c_str()); }
    }
    printf("total %d optbad %d\n", total, bad);
}
