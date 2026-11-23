// exhaustive search for monotone fan-in-2 circuits computing f_G with low weighted cost
#include <bits/stdc++.h>
using namespace std;
typedef unsigned long long u64;

int n;
int adjm[8];
u64 fG;
u64 inp[8];
int budget;
int target;
int E, tau;

const int MAXW = 32;
u64 tt[MAXW];
int S[MAXW];
int usedc[MAXW];
int gop[MAXW], ga[MAXW], gb[MAXW];
long long nodes = 0;
long long nsol_old = 0, nsol_new = 0;
int bestNew = 1000;
vector<string> report;

bool isWide(int w) { return __builtin_popcount(S[w]) >= 2; }

int fzmin(int k) {
    // gates 0..k-1, output wire n+k-1
    vector<int> choiceGates;
    for (int j = 0; j < k; j++) if (gop[j] == 0) {
        bool wa = isWide(ga[j]), wb = isWide(gb[j]);
        if (!wa && !wb) choiceGates.push_back(j);
    }
    int c = choiceGates.size();
    int best = 1000;
    for (int mask = 0; mask < (1 << c); mask++) {
        int des[MAXW];
        for (int j = 0; j < k; j++) des[j] = -1;
        for (int j = 0; j < k; j++) if (gop[j] == 0) {
            bool wa = isWide(ga[j]), wb = isWide(gb[j]);
            if (wa && wb) des[j] = -1;
            else if (!wa && wb) des[j] = ga[j];
            else if (wa && !wb) des[j] = gb[j];
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
                if (!isWide(w)) {
                    for (int x : {ga[j], gb[j]}) if (!vis[x]) { vis[x] = 1; st.push_back(x); }
                }
            } else {
                if (des[j] >= 0) { int x = des[j]; if (!vis[x]) { vis[x] = 1; st.push_back(x); } }
                else {
                    // fat AND reached; check non-star
                    bool nonstar = true;
                    for (int cv = 0; cv < n && nonstar; cv++) {
                        bool found = false;
                        for (int u = 0; u < n && !found; u++) for (int v = u + 1; v < n && !found; v++)
                            if ((adjm[u] >> v & 1) && u != cv && v != cv && (tt[w] >> ((1 << u) | (1 << v)) & 1)) found = true;
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
        char buf[100];
        auto nm = [&](int w) { string r; if (w < n) r = "x" + to_string(w); else r = "g" + to_string(w - n); return r; };
        int w = n + j;
        sprintf(buf, "g%d=%s(%s,%s)[S=%x%s] ", j, gop[j] ? "OR" : "AND", nm(ga[j]).c_str(), nm(gb[j]).c_str(), S[w], (gop[j] == 1 ? (isWide(w) ? "w" : "t") : ((isWide(ga[j]) && isWide(gb[j])) ? "F" : "")));
        s += buf;
    }
    return s;
}

void dfs(int k, int cost, int loose) {
    nodes++;
    if (k > 0 && tt[n + k - 1] == fG && loose == 1) {
        nsol_old++;
        int fz = fzmin(k);
        int w = cost + fz;
        if (w < bestNew) bestNew = w;
        if (w <= target - 1) {
            nsol_new++;
            if (report.size() < 20) report.push_back("NEWCE cost=" + to_string(cost) + " fz=" + to_string(fz) + " : " + show(k));
        } else if (nsol_old <= 5) {
            report.push_back("oldCE cost=" + to_string(cost) + " fz=" + to_string(fz) + " : " + show(k));
        }
        return;
    }
    int nw = n + k;
    if (nw >= MAXW) return;
    for (int a = 0; a < nw; a++) for (int b = a + 1; b < nw; b++) for (int op = 0; op < 2; op++) {
        if (k > 0) {
            int last = nw - 1;
            if (a != last && b != last) {
                // require key > key(last gate)
                int pa = ga[k - 1], pb = gb[k - 1], po = gop[k - 1];
                if (make_tuple(a, b, op) <= make_tuple(pa, pb, po)) continue;
            }
        }
        u64 t = op ? (tt[a] | tt[b]) : (tt[a] & tt[b]);
        bool dup = false;
        for (int w = 0; w < nw; w++) if (tt[w] == t) { dup = true; break; }
        if (dup) continue;
        int s = op ? (S[a] | S[b]) : (S[a] & S[b]);
        int gc = 1;
        if (op == 1 && __builtin_popcount(s) < 2) gc = 2;
        int nl = loose - (usedc[a] == 0) - (usedc[b] == 0) + 1;
        int need = nl - 1;
        if (!(t == fG && nl == 1)) need = max(need, 1);
        if (cost + gc + need > budget) continue;
        tt[nw] = t; S[nw] = s; usedc[nw] = 0; gop[k] = op; ga[k] = a; gb[k] = b;
        usedc[a]++; usedc[b]++;
        dfs(k + 1, cost + gc, nl);
        usedc[a]--; usedc[b]--;
    }
}

int main(int argc, char** argv) {
    // input: n, then edge list as pairs, then optional budget offset
    n = atoi(argv[1]);
    string es = argv[2]; // like "01,02,12"
    for (int i = 0; i < n; i++) adjm[i] = 0;
    E = 0;
    for (size_t p = 0; p + 1 < es.size(); p += 3) {
        int u = es[p] - '0', v = es[p + 1] - '0';
        adjm[u] |= 1 << v; adjm[v] |= 1 << u; E++;
    }
    int N = 1 << n;
    for (int i = 0; i < n; i++) { inp[i] = 0; for (int m = 0; m < N; m++) if (m >> i & 1) inp[i] |= 1ULL << m; }
    fG = 0;
    for (int m = 0; m < N; m++) {
        bool ok = false;
        for (int u = 0; u < n; u++) if (m >> u & 1) if (adjm[u] & m) ok = true;
        if (ok) fG |= 1ULL << m;
    }
    tau = 100;
    for (int T = 0; T < N; T++) {
        bool cov = true;
        for (int u = 0; u < n; u++) for (int v = u + 1; v < n; v++) if (adjm[u] >> v & 1) if (!((T >> u & 1) || (T >> v & 1))) cov = false;
        if (cov) tau = min(tau, __builtin_popcount(T));
    }
    target = E + 2 * tau - 2;
    budget = target - 1;
    if (argc > 3) budget = target - 1 + atoi(argv[3]);
    for (int i = 0; i < n; i++) { tt[i] = inp[i]; S[i] = 1 << i; usedc[i] = 0; }
    dfs(0, 0, n);
    printf("n=%d E=%d tau=%d target=%d budget=%d nodes=%lld oldsol=%lld newsol=%lld bestNew=%d\n", n, E, tau, target, budget, nodes, nsol_old, nsol_new, bestNew);
    for (auto& r : report) printf("%s\n", r.c_str());
}
