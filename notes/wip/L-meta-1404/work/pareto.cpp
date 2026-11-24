#include <bits/stdc++.h>
using namespace std;
typedef unsigned long long u64;
struct R{ u64 a; u64 b[3]; bool operator==(const R&o)const{return a==o.a&&b[0]==o.b[0]&&b[1]==o.b[1]&&b[2]==o.b[2];}};
struct H{ size_t operator()(const R&r)const{ return r.a*0x9E3779B97F4A7C15ULL ^ (r.b[0]*31+r.b[1])*0xC2B2AE3D27D4EB4FULL ^ r.b[2];}};
int pc(const R&r){return __builtin_popcountll(r.a)+__builtin_popcountll(r.b[0])+__builtin_popcountll(r.b[1])+__builtin_popcountll(r.b[2]);}
bool le(const R&x,const R&y){ return (x.a&~y.a)==0 && (x.b[0]&~y.b[0])==0&&(x.b[1]&~y.b[1])==0&&(x.b[2]&~y.b[2])==0;}
vector<R> pareto(vector<R> v){
  sort(v.begin(),v.end(),[](const R&x,const R&y){return pc(x)>pc(y);});
  vector<R> out;
  for(auto&r:v){ bool dom=false; for(auto&o:out) if(le(r,o)){dom=true;break;} if(!dom) out.push_back(r);}
  return out;
}
int main(){
  vector<u64> mn, mx; ifstream f("rows.txt"); string line; getline(f,line); {stringstream ss(line); u64 x; while(ss>>x) mn.push_back(x);} getline(f,line); {stringstream ss(line); u64 x; while(ss>>x) mx.push_back(x);}
  vector<R> L;
  for(int i=0;i<15;i++){ R r{0,{0,0,0}}; for(int j=0;j<45;j++) if(mn[j]>>i&1) r.a|=1ULL<<j; for(int j=0;j<135;j++) if(mx[j]>>i&1) r.b[j/64]|=1ULL<<(j%64); L.push_back(r);}
  L=pareto(L); printf("L0 %zu\n",L.size());
  for(int k=1;k<=3;k++){
    unordered_set<R,H> S(L.begin(),L.end());
    for(size_t i=0;i<L.size();i++) for(size_t j=i+1;j<L.size();j++){
      R x=L[i],y=L[j]; R a{x.a&y.a,{x.b[0]|y.b[0],x.b[1]|y.b[1],x.b[2]|y.b[2]}}; R o{x.a|y.a,{x.b[0]&y.b[0],x.b[1]&y.b[1],x.b[2]&y.b[2]}}; S.insert(a); S.insert(o);}
    vector<R> v(S.begin(),S.end()); printf("V%d raw %zu\n",k,v.size()); fflush(stdout);
    L=pareto(v); printf("L%d %zu\n",k,L.size()); fflush(stdout);
  }
}
