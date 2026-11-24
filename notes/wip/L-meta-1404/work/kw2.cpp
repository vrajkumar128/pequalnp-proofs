#include <bits/stdc++.h>
using namespace std;
typedef unsigned long long u64;
const int W=4;
struct S{ u64 w[W]; };
static inline bool eqS(const S&a,const S&b){for(int i=0;i<W;i++) if(a.w[i]!=b.w[i]) return false; return true;}
static inline int cnt(const S&a){int c=0;for(int i=0;i<W;i++) c+=__builtin_popcountll(a.w[i]);return c;}
static inline bool has(const S&a,int i){return a.w[i>>6]>>(i&63)&1;}
static inline void setb(S&a,int i){a.w[i>>6]|=1ULL<<(i&63);}
static inline void clrb(S&a,int i){a.w[i>>6]&=~(1ULL<<(i&63));}
static inline S andn(const S&a,const S&b){S r; for(int i=0;i<W;i++) r.w[i]=a.w[i]&~b.w[i]; return r;}
struct Key{ S a,b; bool operator==(const Key&o)const{return eqS(a,o.a)&&eqS(b,o.b);} };
struct KH{ size_t operator()(const Key&k)const{ u64 h=1469598103934665603ULL; for(int i=0;i<W;i++){h^=k.a.w[i];h*=1099511628211ULL;h^=k.b.w[i];h*=1099511628211ULL;} return h^(h>>29);} };
struct Ent{ int8_t lb, ub; int8_t side; S part; };
int n; vector<unsigned> AM, BM; int NA, NB;
unordered_map<Key,Ent,KH> memo;
long long calls=0;
unsigned interA(const S&a){unsigned r=(1u<<n)-1; for(int i=0;i<W;i++){u64 x=a.w[i]; while(x){int j=__builtin_ctzll(x); x&=x-1; r&=AM[i*64+j];}} return r;}
unsigned interB(const S&b){unsigned r=(1u<<n)-1; for(int i=0;i<W;i++){u64 x=b.w[i]; while(x){int j=__builtin_ctzll(x); x&=x-1; r&=BM[i*64+j];}} return r;}
int clg(int x){int k=0; while((1<<k)<x) k++; return k;}
vector<int> elems(const S&a){vector<int> v; for(int i=0;i<W;i++){u64 x=a.w[i]; while(x){int j=__builtin_ctzll(x); x&=x-1; v.push_back(i*64+j);}} return v;}
bool le(const S&A,const S&B,int k);
static void record(const S&A,const S&B,int k,bool r,int side,const S&part){
  Key key{A,B}; auto it=memo.find(key);
  if(it==memo.end()){ Ent e; e.lb=1; e.ub=100; e.side=-1; memset(&e.part,0,sizeof(S)); it=memo.emplace(key,e).first; }
  if(r){ if(k<it->second.ub){ it->second.ub=k; it->second.side=side; it->second.part=part; } }
  else it->second.lb=max<int>(it->second.lb,k+1);
}
bool testSplit(const S&A,const S&B,int k,bool sideA,const S&P1){
  const S&X=sideA?A:B; S P2=andn(X,P1);
  if(cnt(P1)==0||cnt(P2)==0) return false;
  if(sideA) return le(P1,B,k-1)&&le(P2,B,k-1);
  return le(A,P1,k-1)&&le(A,P2,k-1);
}
bool exhaustive(const S&A,const S&B,int k,bool sideA,S&out){
  const S& X = sideA?A:B;
  vector<int> el=elems(X); int m=el.size(); if(m<2) return false;
  S P1{},P2{};
  function<bool(int)> rec=[&](int i)->bool{
    if(i==m) return true;
    int e=el[i];
    setb(P1,e);
    if((sideA? le(P1,B,k-1) : le(A,P1,k-1)) && rec(i+1)) return true;
    clrb(P1,e);
    if(i==0) return false;
    setb(P2,e);
    if((sideA? le(P2,B,k-1) : le(A,P2,k-1)) && rec(i+1)) return true;
    clrb(P2,e);
    return false;
  };
  if(rec(0)){ out=P1; return true;} return false;
}
bool le(const S&A,const S&B,int k){
  calls++;
  int ca=cnt(A), cb=cnt(B);
  if(ca==0||cb==0) return true;
  if(interA(A)&interB(B)) return true;
  if(k<=0) return false;
  Key key{A,B};
  auto it=memo.find(key);
  if(it!=memo.end()){ if(it->second.ub<=k) return true; if(it->second.lb>k) return false; }
  if(clg(ca)+clg(cb)<=k){
    bool sideA = ca>=2; vector<int> el=elems(sideA?A:B); S P{}; for(size_t i=0;i<el.size()/2;i++) setb(P,el[i]);
    record(A,B,k,true,sideA?0:1,P); return true; }
  // heuristic coordinate splits
  for(int sd=0;sd<2;sd++) for(int i=0;i<n;i++){
    S P{}; const S&X= sd==0?A:B; for(int e:elems(X)) if(((sd==0?AM[e]:BM[e])>>i)&1) setb(P,e);
    if(testSplit(A,B,k,sd==0,P)){ record(A,B,k,true,sd,P); return true; }
  }
  S out{};
  for(int sd=0;sd<2;sd++) if(exhaustive(A,B,k,sd==0,out)){ record(A,B,k,true,sd,out); return true; }
  record(A,B,k,false,0,out); return false;
}
// formula
struct Node{ int t; int v; int l,r; }; vector<Node> nodes;
int build(const S&A,const S&B,int k){
  int ca=cnt(A), cb=cnt(B);
  unsigned c = interA(A)&interB(B);
  if(ca&&cb&&c){ nodes.push_back({0,__builtin_ctz(c),-1,-1}); return nodes.size()-1; }
  if(!ca||!cb){ nodes.push_back({0,0,-1,-1}); return nodes.size()-1; } // arbitrary
  bool ok=le(A,B,k); assert(ok);
  Ent e=memo[Key{A,B}];
  int kk=e.ub;
  if(e.side==0){ S P2=andn(A,e.part); int l=build(e.part,B,kk-1), r=build(P2,B,kk-1); nodes.push_back({1,0,l,r}); }
  else { S P2=andn(B,e.part); int l=build(A,e.part,kk-1), r=build(A,P2,kk-1); nodes.push_back({2,0,l,r}); }
  return nodes.size()-1;
}
bool evalN(int id,unsigned pt){ Node&x=nodes[id]; if(x.t==0) return pt>>x.v&1; if(x.t==1) return evalN(x.l,pt)||evalN(x.r,pt); return evalN(x.l,pt)&&evalN(x.r,pt);}
int depthN(int id){Node&x=nodes[id]; if(x.t==0) return 0; return 1+max(depthN(x.l),depthN(x.r));}
string show(int id){Node&x=nodes[id]; if(x.t==0) return "x"+to_string(x.v); return "("+show(x.l)+(x.t==1?" | ":" & ")+show(x.r)+")";}
int main(int argc,char**argv){
  if(scanf("%d",&n)!=1) return 1; if(scanf("%d",&NA)!=1) return 1; AM.resize(NA); for(auto&x:AM) if(scanf("%u",&x)!=1) return 1; if(scanf("%d",&NB)!=1) return 1; BM.resize(NB); for(auto&x:BM) if(scanf("%u",&x)!=1) return 1;
  AM.resize(256,(1u<<n)-1); BM.resize(256,(1u<<n)-1);
  int K=atoi(argv[1]); int seed=atoi(argv[2]); string mode=argc>3?argv[3]:"cegar";
  mt19937 rng(seed);
  S A{},B{};
  if(mode=="full"){ for(int i=0;i<NA;i++) setb(A,i); for(int i=0;i<NB;i++) setb(B,i); }
  else { setb(A,rng()%NA); setb(B,rng()%NB); }
  unsigned full=(1u<<n)-1;
  for(int it=1;;it++){
    auto t=clock(); bool r=le(A,B,K);
    printf("iter %d |A|=%d |B|=%d %s calls=%lld memo=%zu %.1fs\n",it,cnt(A),cnt(B),r?"YES":"NO",calls,memo.size(),(double)(clock()-t)/CLOCKS_PER_SEC); fflush(stdout);
    if(!r){ printf("HARD A:"); for(int e:elems(A)) printf(" %d",e); printf("\nHARD B:"); for(int e:elems(B)) printf(" %d",e); printf("\n"); return 0; }
    nodes.clear(); int root=build(A,B,K);
    vector<int> badA,badB;
    for(int i=0;i<NA;i++) if(!evalN(root,AM[i])) badA.push_back(i);
    for(int i=0;i<NB;i++) if(evalN(root,full^BM[i])) badB.push_back(i);
    if(badA.empty()&&badB.empty()){ printf("FORMULA depth %d: %s\n",depthN(root),show(root).c_str()); return 0; }
    if(!badA.empty()) setb(A,badA[rng()%badA.size()]);
    if(!badB.empty()) setb(B,badB[rng()%badB.size()]);
  }
}
