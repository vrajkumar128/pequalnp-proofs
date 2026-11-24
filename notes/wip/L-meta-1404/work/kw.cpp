// exact monotone KW depth by backtracking splits with monotone pruning + memo
#include <bits/stdc++.h>
using namespace std;
typedef unsigned long long u64;
const int W=4; // up to 256 elements per side
struct S{ u64 w[W]; };
static inline bool eqS(const S&a,const S&b){for(int i=0;i<W;i++) if(a.w[i]!=b.w[i]) return false; return true;}
static inline int cnt(const S&a){int c=0;for(int i=0;i<W;i++) c+=__builtin_popcountll(a.w[i]);return c;}
static inline bool has(const S&a,int i){return a.w[i>>6]>>(i&63)&1;}
static inline void setb(S&a,int i){a.w[i>>6]|=1ULL<<(i&63);}
static inline void clrb(S&a,int i){a.w[i>>6]&=~(1ULL<<(i&63));}
struct Key{ S a,b; bool operator==(const Key&o)const{return eqS(a,o.a)&&eqS(b,o.b);} };
struct KH{ size_t operator()(const Key&k)const{ u64 h=1469598103934665603ULL; for(int i=0;i<W;i++){h^=k.a.w[i];h*=1099511628211ULL;h^=k.b.w[i];h*=1099511628211ULL;} return h^(h>>29);} };
int n; vector<unsigned> AM, BM; // Alice masks (true points ones), Bob masks (false-point zero sets)
unordered_map<Key,pair<int8_t,int8_t>,KH> memo; // lb, ub
long long calls=0;
unsigned interA(const S&a){unsigned r=(1u<<n)-1; for(int i=0;i<W;i++){u64 x=a.w[i]; while(x){int j=__builtin_ctzll(x); x&=x-1; r&=AM[i*64+j];}} return r;}
unsigned interB(const S&b){unsigned r=(1u<<n)-1; for(int i=0;i<W;i++){u64 x=b.w[i]; while(x){int j=__builtin_ctzll(x); x&=x-1; r&=BM[i*64+j];}} return r;}
int clg(int x){int k=0; while((1<<k)<x) k++; return k;}
vector<int> elems(const S&a){vector<int> v; for(int i=0;i<W;i++){u64 x=a.w[i]; while(x){int j=__builtin_ctzll(x); x&=x-1; v.push_back(i*64+j);}} return v;}
bool le(const S&A,const S&B,int k);
// try to split side X (A if sideA) into two parts both <= k-1
bool trySplit(const S&A,const S&B,int k,bool sideA){
  const S& X = sideA?A:B;
  vector<int> el=elems(X);
  int m=el.size(); if(m<2) return false;
  S P1{},P2{}; // partial parts
  // order: as given
  // DFS iterative with recursion
  function<bool(int)> rec=[&](int i)->bool{
    if(i==m) return true;
    int e=el[i];
    // put in P1
    setb(P1,e);
    bool ok = sideA? le(P1,B,k-1) : le(A,P1,k-1);
    if(ok && rec(i+1)) return true;
    clrb(P1,e);
    if(i==0) return false; // symmetry: first elem in P1
    setb(P2,e);
    ok = sideA? le(P2,B,k-1) : le(A,P2,k-1);
    if(ok && rec(i+1)) return true;
    clrb(P2,e);
    return false;
  };
  return rec(0);
}
bool le(const S&A,const S&B,int k){
  calls++;
  int ca=cnt(A), cb=cnt(B);
  if(ca==0||cb==0) return true;
  if(interA(A)&interB(B)) return true;
  if(k<=0) return false;
  Key key{A,B};
  auto it=memo.find(key);
  int lb=1,ub=100;
  if(it!=memo.end()){lb=it->second.first; ub=it->second.second; if(ub<=k) return true; if(lb>k) return false;}
  // quick upper bound: log|A| + log|B|
  if(clg(ca)+clg(cb)<=k){ memo[key]={lb,min(ub,k)}; return true; }
  bool r = trySplit(A,B,k,true) || trySplit(A,B,k,false);
  auto &ent=memo[key];
  if(it==memo.end()) ent={1,100};
  if(r) ent.second=min<int>(ent.second,k); else ent.first=max<int>(ent.first,k+1);
  return r;
}
int main(int argc,char**argv){
  // input: n, then line of Alice masks, line of Bob masks; argv[1]=max depth
  scanf("%d",&n); int na,nb; scanf("%d",&na); AM.resize(na); for(auto&x:AM) scanf("%u",&x); scanf("%d",&nb); BM.resize(nb); for(auto&x:BM) scanf("%u",&x);
  AM.resize(256,(1u<<n)-1); BM.resize(256,(1u<<n)-1);
  S A{},B{}; for(int i=0;i<na;i++) setb(A,i); for(int i=0;i<nb;i++) setb(B,i);
  int maxd=atoi(argv[1]);
  for(int k=0;k<=maxd;k++){
    auto t=clock(); bool r=le(A,B,k);
    printf("k=%d %s calls=%lld memo=%zu %.1fs\n",k,r?"YES":"no",calls,memo.size(),(double)(clock()-t)/CLOCKS_PER_SEC); fflush(stdout);
    if(r) break;
  }
}
