#include <bits/stdc++.h>
using namespace std;
typedef unsigned long long u64;
int N;
u64 code(const vector<int>& adj, const vector<int>& p, int k) {
    u64 c = 0; int bit = 0;
    for (int u = 0; u < k; u++) for (int v = u + 1; v < k; v++) { if (adj[p[u]] >> p[v] & 1) c |= 1ULL << bit; bit++; }
    return c;
}
u64 canon(const vector<int>& adj, int k) {
    vector<int> p(k); iota(p.begin(), p.end(), 0);
    // refine: sort by degree to cut perms: only perms consistent with degree order
    vector<int> deg(k); for (int i = 0; i < k; i++) deg[i] = __builtin_popcount(adj[i]);
    sort(p.begin(), p.end(), [&](int a, int b) { return deg[a] > deg[b] || (deg[a] == deg[b] && a < b); });
    // groups of equal degree; iterate over permutations within groups
    vector<pair<int,int>> groups; int s = 0;
    for (int i = 1; i <= k; i++) if (i == k || deg[p[i]] != deg[p[s]]) { groups.push_back({s, i}); s = i; }
    u64 best = ~0ULL;
    function<void(int)> rec = [&](int gi) {
        if (gi == (int)groups.size()) { best = min(best, code(adj, p, k)); return; }
        int a = groups[gi].first, b = groups[gi].second;
        sort(p.begin() + a, p.begin() + b);
        do { rec(gi + 1); } while (next_permutation(p.begin() + a, p.begin() + b));
    };
    rec(0);
    return best;
}
int main(int argc, char** argv) {
    N = atoi(argv[1]);
    vector<vector<int>> cur = {vector<int>(1, 0)};
    for (int k = 1; k < N; k++) {
        set<u64> seen; vector<vector<int>> nxt;
        for (auto& g : cur) {
            for (int S = 0; S < (1 << k); S++) {
                bool ok = true;
                for (int a = 0; a < k && ok; a++) if (S >> a & 1) for (int b = a + 1; b < k && ok; b++) if (S >> b & 1) if (g[a] & g[b]) ok = false;
                if (!ok) continue;
                vector<int> h(k + 1, 0);
                for (int i = 0; i < k; i++) h[i] = g[i];
                for (int a = 0; a < k; a++) if (S >> a & 1) { h[a] |= 1 << k; h[k] |= 1 << a; }
                u64 c = canon(h, k + 1);
                if (seen.insert(c).second) nxt.push_back(h);
            }
        }
        cur = nxt;
        fprintf(stderr, "k=%d graphs=%zu\n", k + 1, cur.size());
    }
    for (auto& g : cur) {
        bool iso = false; for (int i = 0; i < N; i++) if (!g[i]) iso = true;
        if (iso) continue;
        printf("%d ", N); bool first = true;
        for (int u = 0; u < N; u++) for (int v = u + 1; v < N; v++) if (g[u] >> v & 1) { if (!first) printf(","); printf("%d%d", u, v); first = false; }
        printf("\n");
    }
}
