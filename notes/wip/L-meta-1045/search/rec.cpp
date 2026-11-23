// recursive constructive costs: star / star-split / component split / product of (OR(W) v f_{G-W})
#include <bits/stdc++.h>
using namespace std;
int n;
int adj[16];
int memoOld[1 << 12], memoNew[1 << 12];
int choiceOld[1 << 12];

int edgesIn(int U) { int e = 0; for (int u = 0; u < n; u++) if (U >> u & 1) e += __builtin_popcount(adj[u] & U); return e / 2; }
int degIn(int t, int U) { return __builtin_popcount(adj[t] & U); }

int tauOf(int U) {
    int best = 100;
    for (int T = U;; T = (T - 1) & U) {
        bool ok = true;
        for (int u = 0; u < n && ok; u++) if (U >> u & 1) if ((adj[u] & U & ~T) && !(T >> u & 1)) ok = false;
        if (ok) best = min(best, __builtin_popcount(T));
        if (T == 0) break;
    }
    return best;
}

vector<int> misOf(int U) {
    vector<int> res;
    for (int I = U;; I = (I - 1) & U) {
        bool indep = true;
        for (int u = 0; u < n && indep; u++) if (I >> u & 1) if (adj[u] & I) indep = false;
        if (indep) {
            bool maximal = true;
            for (int v = 0; v < n && maximal; v++) if ((U >> v & 1) && !(I >> v & 1)) if (!(adj[v] & I)) maximal = false;
            if (maximal) res.push_back(I);
        }
        if (I == 0) break;
    }
    return res;
}

void solve(int U);
int OLD(int U) { if (memoOld[U] < 0) solve(U); return memoOld[U]; }
int NEW(int U) { if (memoNew[U] < 0) solve(U); return memoNew[U]; }

void solve(int U) {
    int E = edgesIn(U);
    if (E == 0) { memoOld[U] = memoNew[U] = 0; return; }
    int bo = 1000, bn = 1000;
    // star
    for (int t = 0; t < n; t++) if (U >> t & 1) {
        int d = degIn(t, U);
        if (d == E) { bo = min(bo, d); bn = min(bn, d); }
    }
    // star split
    for (int t = 0; t < n; t++) if (U >> t & 1) {
        int d = degIn(t, U);
        if (d == 0 || d == E) continue;
        int R = U & ~(1 << t);
        bo = min(bo, d + 2 + OLD(R));
        bn = min(bn, d + 2 + NEW(R));
    }
    // product
    vector<int> mis = misOf(U);
    int M = mis.size();
    if (M <= 20) {
        // candidate W subsets of U with |W|>=2
        vector<pair<int,int>> cand; // (coverMask, cost+1)
        for (int W = U;; W = (W - 1) & U) {
            if (__builtin_popcount(W) >= 2) {
                int cm = 0;
                for (int i = 0; i < M; i++) if (!(mis[i] & W)) cm |= 1 << i;
                if (cm) {
                    int R = U & ~W;
                    int c = __builtin_popcount(W) - 1;
                    if (edgesIn(R) > 0) c += OLD(R) + 1;
                    cand.push_back({cm, c + 1});
                }
            }
            if (W == 0) break;
        }
        // keep only undominated candidates per cover mask
        unordered_map<int,int> bestc;
        for (auto& p : cand) { auto it = bestc.find(p.first); if (it == bestc.end() || it->second > p.second) bestc[p.first] = p.second; }
        vector<int> dp(1 << M, 1000);
        dp[0] = 0;
        vector<pair<int,int>> cl(bestc.begin(), bestc.end());
        for (int s = 0; s < (1 << M); s++) if (dp[s] < 1000) {
            for (auto& p : cl) { int t = s | p.first; if (t != s && dp[t] > dp[s] + p.second) dp[t] = dp[s] + p.second; }
        }
        int full = (1 << M) - 1;
        int pc = dp[full] - 1;
        // require at least 2 factors: a single factor W with cover all would mean... allow anyway (m>=1)
        if (pc < 1000) {
            bo = min(bo, pc);
            bn = min(bn, pc + 1);
        }
    }
    memoOld[U] = bo; memoNew[U] = bn;
}

int main(int argc, char** argv) {
    n = atoi(argv[1]);
    // read graphs as edge lists from stdin lines: "n e1,e2,..."
    string line;
    int cntBad = 0, cntOld = 0, total = 0;
    while (getline(cin, line)) {
        if (line.empty()) continue;
        istringstream is(line); int nn; string es; is >> nn >> es; n = nn;
        for (int i = 0; i < n; i++) adj[i] = 0;
        int E = 0;
        for (size_t p = 0; p + 1 < es.size(); p += 3) { int u = es[p] - '0', v = es[p + 1] - '0'; adj[u] |= 1 << v; adj[v] |= 1 << u; E++; }
        int V = (1 << n) - 1;
        for (int U = 0; U <= V; U++) memoOld[U] = memoNew[U] = -1;
        int tau = tauOf(V);
        int target = E + 2 * tau - 2;
        int o = OLD(V), nw = NEW(V);
        total++;
        if (o < target) cntOld++;
        if (nw < target) { cntBad++; printf("NEWBAD %s E=%d tau=%d target=%d old=%d new=%d\n", es.c_str(), E, tau, target, o, nw); }
        else if (o < target - 0 && argc > 2) printf("old-saving %s target=%d old=%d new=%d\n", es.c_str(), target, o, nw);
    }
    printf("total %d oldSaving %d newBad %d\n", total, cntOld, cntBad);
}
