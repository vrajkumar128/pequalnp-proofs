// G-independent exhaustive search; checks all labeled C4-free graphs (no isolated vertex) at leaves
#include <bits/stdc++.h>
using namespace std;
typedef unsigned long long u64;

int n, budget; int cap = 0; int slack = 0; set<u64> foundG;
struct GInfo { int E, tau, target; int adj[8]; };
unordered_map<u64, GInfo> gmap;

const int MAXW = 32;
u64 tt[MAXW];
int S[MAXW];
int usedc[MAXW];
int gop[MAXW], ga[MAXW], gb[MAXW];
long long nodes = 0, nold = 0, nnew = 0;
map<string, int> bestOldPerGraph;

static inline bool isWide(int w) { return __builtin_popcount(S[w]) >= 2; }

int fzmin(int k, const GInfo& G) {
    vector<int> choiceGates;
    for (int j = 0; j < k; j++) if (gop[j] == 0) {
        if (!isWide(ga[j]) && !isWide(gb[j])) choiceGates.push_back(j);
    }
    int c = choiceGates.size();
    int best = 1000;
    for (int mask = 0; mask < (1 << c); mask++) {
        int des[MAXW];
        for (int j = 0; j < k; j++) {
            des[j] = -1;
            if (gop[j] == 0) {
                bool wa = isWide(ga[j]), wb = isWide(gb[j]);
                if (!wa && wb) des[j] = ga[j];
                else if (wa && !wb) des[j] = gb[j];
            }
        }
        for (int t = 0; t < c; t++) { int j = choiceGates[t]; des[j] = (mask >> t & 1) ? gb[j] : ga[j]; }
        vector<char> vis(n + k, 0);
        vector<int> st; st.push_back(n + k - 1); vis[n + k - 1] = 1;
        int cnt = 0;
        while (!st.empty()) {
            int w = st.back(); st.pop_back();
            if (w < n) continue;
            int j = w - n;
            if (gop[j] == 1) {
                if (!isWide(w)) for (int x : {ga[j], gb[j]}) if (!vis[x]) { vis[x] = 1; st.push_back(x); }
            } else {
                if (des[j] >= 0) { int x = des[j]; if (!vis[x]) { vis[x] = 1; st.push_back(x); } }
                else {
                    bool nonstar = true;
                    for (int cv = 0; cv < n && nonstar; cv++) {
                        bool found = false;
                        for (int u = 0; u < n && !found; u++) for (int v = u + 1; v < n && !found; v++)
                            if ((G.adj[u] >> v & 1) && u != cv && v != cv && (tt[w] >> ((1 << u) | (1 << v)) & 1)) found = true;
                        if (!found) nonstar = false;
                    }
                    if (nonstar) cnt++;
                }
            }
        }
        best = min(best, cnt);
    }
    return best;
}

string show(int k) {
    string s;
    for (int j = 0; j < k; j++) {
        char buf[120];
        auto nm = [&](int w) { string r; if (w < n) r = "x" + to_string(w); else r = "g" + to_string(w - n); return r; };
        int w = n + j;
        sprintf(buf, "g%d=%s(%s,%s)[S=%x%s] ", j, gop[j] ? "OR" : "AND", nm(ga[j]).c_str(), nm(gb[j]).c_str(), S[w], (gop[j] == 1 ? (isWide(w) ? "w" : "t") : ((isWide(ga[j]) && isWide(gb[j])) ? "F" : "")));
        s += buf;
    }
    return s;
}

string gname(const GInfo& G) {
    string s;
    for (int u = 0; u < n; u++) for (int v = u + 1; v < n; v++) if (G.adj[u] >> v & 1) { s += char('0' + u); s += char('0' + v); s += ','; }
    return s;
}

void dfs(int k, int cost, int loose, int m) {
    nodes++;
    if (k > 0 && loose == 1) {
        auto it = gmap.find(tt[n + k - 1]);
        if (it != gmap.end() && cost < it->second.E) { { printf("ABLOW graph=%s E=%d cost=%d : %s\n", gname(it->second).c_str(), it->second.E, cost, show(k).c_str()); fflush(stdout); nold++; if (nold > 20) exit(0); } if (0) {
            nold++;
            const GInfo& G = it->second;
            int fz = fzmin(k, G);
            if (cost + fz < G.target) {
                nnew++;
                if (nnew <= 30) printf("NEWCE graph=%s E=%d tau=%d target=%d cost=%d fz=%d : %s\n", gname(G).c_str(), G.E, G.tau, G.target, cost, fz, show(k).c_str());
            } else if (nold <= 30) {
                printf("OLDCE graph=%s E=%d tau=%d target=%d cost=%d fz=%d : %s\n", gname(G).c_str(), G.E, G.tau, G.target, cost, fz, show(k).c_str());
            }
            fflush(stdout);
        } }
    }
    int nw = n + k;
    if (nw >= MAXW) return;
    int last = nw - 1;
    int pa = -1, pb = -1, po = -1;
    if (k > 0) { pa = ga[k - 1]; pb = gb[k - 1]; po = gop[k - 1]; }
    for (int a = 0; a < nw; a++) for (int b = a + 1; b < nw; b++) {
        int nm2 = m;
        {
            bool okv = true;
            if (a < n && a >= m) { if (a != m) okv = false; }
            if (b < n && b >= m) {
                if (a < n && a >= m) { if (b != m + 1) okv = false; }
                else if (b != m) okv = false;
            }
            if (!okv) continue;
            if (a < n && a >= m) nm2 = a + 1;
            if (b < n && b >= m) nm2 = b + 1;
        }
        int nl = loose - (usedc[a] == 0) - (usedc[b] == 0) + 1;
        int need = nl - 1;
        if (k + 1 + need > cap) continue;
        u64 ta = tt[a], tb = tt[b];
        for (int op = 0; op < 2; op++) {
            if (k > 0 && a != last && b != last) {
                if (a < pa || (a == pa && (b < pb || (b == pb && op <= po)))) continue;
            }
            int s = op ? (S[a] | S[b]) : (S[a] & S[b]);
            int gc = (op == 1 && __builtin_popcount(s) < 2) ? 0 : 1;
            if (cost + gc > budget) continue;
            u64 t = op ? (ta | tb) : (ta & tb);
            if (t == ta || t == tb) continue;
            bool dup = false;
            for (int w = 0; w < nw; w++) if (tt[w] == t) { dup = true; break; }
            if (dup) continue;
            tt[nw] = t; S[nw] = s; usedc[nw] = 0; gop[k] = op; ga[k] = a; gb[k] = b;
            usedc[a]++; usedc[b]++;
            dfs(k + 1, cost + gc, nl, nm2);
            usedc[a]--; usedc[b]--;
        }
    }
}

int main(int argc, char** argv) {
    n = atoi(argv[1]);
    budget = atoi(argv[2]); cap = atoi(argv[3]);
    int N = 1 << n;
    vector<pair<int,int>> pairs;
    for (int u = 0; u < n; u++) for (int v = u + 1; v < n; v++) pairs.push_back({u, v});
    int P = pairs.size();
    for (long long mask = 1; mask < (1LL << P); mask++) {
        GInfo G; for (int i = 0; i < 8; i++) G.adj[i] = 0; G.E = 0;
        for (int i = 0; i < P; i++) if (mask >> i & 1) { G.adj[pairs[i].first] |= 1 << pairs[i].second; G.adj[pairs[i].second] |= 1 << pairs[i].first; G.E++; }
        bool ok = true;
        for (int i = 0; i < n; i++) if (!G.adj[i]) ok = false;
        if (!ok) continue;
        for (int a = 0; a < n && ok; a++) for (int c = a + 1; c < n && ok; c++) if (__builtin_popcount(G.adj[a] & G.adj[c]) >= 2) ok = false;
        if (!ok) continue;
        G.tau = 100;
        for (int T = 0; T < N; T++) {
            bool cov = true;
            for (int i = 0; i < P && cov; i++) if (mask >> i & 1) if (!((T >> pairs[i].first & 1) || (T >> pairs[i].second & 1))) cov = false;
            if (cov) G.tau = min(G.tau, __builtin_popcount(T));
        }
        G.target = G.E + 2 * G.tau - 2;
        u64 f = 0;
        for (int m = 0; m < N; m++) { bool on = false; for (int u = 0; u < n; u++) if ((m >> u & 1) && (G.adj[u] & m)) on = true; if (on) f |= 1ULL << m; }
        gmap[f] = G;
    }
    fprintf(stderr, "graphs: %zu\n", gmap.size());
    for (int i = 0; i < n; i++) { tt[i] = 0; for (int m = 0; m < N; m++) if (m >> i & 1) tt[i] |= 1ULL << m; S[i] = 1 << i; usedc[i] = 0; }
    dfs(0, 0, n, 0);
    if (slack) {
        auto canon = [&](const GInfo& G) { vector<int> p(n); iota(p.begin(), p.end(), 0); long long best = LLONG_MAX;
            do { long long code = 0; int bit = 0; for (int u = 0; u < n; u++) for (int v = u + 1; v < n; v++) { if (G.adj[p[u]] >> p[v] & 1) code |= 1LL << bit; bit++; } best = min(best, code); } while (next_permutation(p.begin(), p.end())); return best; };
        set<long long> foundC; for (u64 f : foundG) foundC.insert(canon(gmap[f]));
        set<long long> allC; int miss = 0;
        for (auto& kv : gmap) if (kv.second.target <= budget) { long long c = canon(kv.second); if (allC.count(c)) continue; allC.insert(c); if (!foundC.count(c)) { miss++; printf("MISSING %s target=%d\n", gname(kv.second).c_str(), kv.second.target); } }
        printf("classes %zu, missing %d\n", allC.size(), miss);
    }
    printf("DONE n=%d budget=%d nodes=%lld nold=%lld nnew=%lld\n", n, budget, nodes, nold, nnew);
}
