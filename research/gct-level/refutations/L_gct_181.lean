import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_gct_181
noncomputable section
namespace Aa
open Finset
abbrev aC:=Fin 4×Fin 5→ℂ
abbrev aH:=Fin 5→ℂ
abbrev row (i:Fin 4):aC→ₗ[ℂ] aH:=LinearMap.funLeft ℂ ℂ fun j=>(i,j)
def aO (M:aC):ℂ:=∑e:Fin 4 ↪ Fin 5,∏r,M (r,e r)
abbrev aHw:=Fin 5×Fin 5×Fin 5×Fin 5
def yH:aHw≃(Fin 4→Fin 5) where
 toFun p:= ![p.1,p.2.1,p.2.2.1,p.2.2.2]
 invFun z:=(z 0,z 1,z 2,z 3)
 left_inv _:=rfl
 right_inv z:=by ext i;fin_cases i<;>rfl
lemma cK (M:aC):
  aO M=∑j,∑l,∑m,∑n,
   if j=l∨j=m∨j=n∨l=m∨l=n∨m=n then 0 else
   M (0,j)*M (1,l)*M (2,m)*M (3,n):=by
 classical
 let u (z:Fin 4→Fin 5):=∏r,M (r,z r)
 have A:aO M=∑z:Fin 4→Fin 5,if Function.Injective z then u z else 0:=by
  let E:=Equiv.subtypeInjectiveEquivEmbedding (Fin 4) (Fin 5)
  change(∑e:Fin 4 ↪ Fin 5,u e)=_;rw[←E.sum_comp (fun e:Fin 4 ↪ Fin 5=>u e),←Finset.sum_filter];exact(Finset.sum_subtype _ (by simp) u).symm
 rw[A,←yH.sum_comp (fun z=>if Function.Injective z then u z else 0)];simp only[Fintype.sum_prod_type];refine sum_congr rfl fun a _=>sum_congr rfl fun b _=>sum_congr rfl fun c _=>sum_congr rfl fun d _=> ?_
 let z:=yH (a,b,c,d)
 have p:z 0=a:=rfl;have q:z 1=b:=rfl;have s:z 2=c:=rfl;have t:z 3=d:=rfl;have f:Function.Injective z↔¬(a=b∨a=c∨a=d∨b=c∨b=d∨c=d):=by
  constructor
  ·intro o;have h (i j:Fin 4) (g:i≠j):z i≠z j:=fun h=>g (o h)
   exact not_or_intro (h 0 1 (by decide)) (not_or_intro (h 0 2 (by decide))
    (not_or_intro (h 0 3 (by decide)) (not_or_intro (h 1 2 (by decide))
      (not_or_intro (h 1 3 (by decide)) (h 2 3 (by decide))))))
  ·intro g i j v;simp only[not_or] at g;fin_cases i<;>fin_cases j<;>first | rfl | grind
 change(if Function.Injective z then u z else 0)=_;by_cases g:a=b∨a=c∨a=d∨b=c∨b=d∨c=d
 ·have k:¬Function.Injective z:=fun h=>f.mp h g
  rw[ite_eq_right k,ite_eq_left g]
 ·rw[ite_eq_left (f.mpr g),ite_eq_right g];change(∏r,M (r,z r))=_;simp[Fin.prod_univ_succ,p,q,s,t,mul_assoc]
lemma lO (L:Submodule ℂ aC) (hL:∀t∈L,aO (1+t)≠0)
  (i:Fin 4):∃f:Module.Dual ℂ aH,f 1=1∧∀t∈L,f (row i t)=0:=by
 classical
 have a:(1:aH)∉L.map (row i):=by rintro⟨t,d,g⟩;apply hL (-t) (L.neg_mem d);apply sum_eq_zero;intro e _;apply Finset.prod_eq_zero (mem_univ i);change(1:ℂ)+ -t (i,e i)=0;have h:t (i,e i)=1:=congrFun g (e i);rw[h];ring
 obtain⟨f,j,b⟩:=Submodule.exists_dual_map_eq_bot_of_notMem a inferInstance;refine⟨(f 1)⁻¹ •f,inv_mul_cancel₀ j,?_⟩;intro t d;have c:f (row i t)∈(L.map (row i)).map f:=⟨_,⟨t,d,rfl⟩,rfl⟩
 rw[b] at c;change f (row i t)=0 at c;change(f 1)⁻¹ *f (row i t)=0;simp[c]
abbrev bK (i:Fin 5):aH:=Pi.single i 1
lemma vG (f:Module.Dual ℂ aH) (b:f 1=1):
  ∃a,f (bK a)≠0:=by
 classical
 by_contra! h;have e:∑a:Fin 5,bK a=(1:aH):=by ext j;simp[bK,Finset.sum_apply,Pi.single_apply]
 rw[←e,map_sum] at b;simp[h] at b
lemma aBr (f g:Module.Dual ℂ aH) (r:f 1=1) (s:g 1=1):
  ∃
   x y:aH,f x=1∧g y=1∧
   ∀c d:Fin 5,c≠d→x c*y d+x d*y c=0:=by
 classical
 by_cases e:∃a,f (bK a)≠0∧g (bK a)≠0
 ·obtain⟨a,k,j⟩:=e;refine⟨(f (bK a))⁻¹ •bK a,(g (bK a))⁻¹ •bK a,
   by simp[k],by simp[j],?_⟩
  intro c d i;by_cases h:a=c
  ·subst c;simp[bK,Ne.symm i]
  ·simp[bK,Pi.single_apply,Ne.symm h]
 ·obtain⟨a,k⟩:=vG f r;obtain⟨b,j⟩:=vG g s;have l:g (bK a)=0:=by by_contra h;exact e ⟨a,k,h⟩
  have n:f (bK b)=0:=by by_contra h;exact e ⟨b,h,j⟩
  have hab:a≠b:=by rintro rfl;exact j l
  refine⟨(f (bK a))⁻¹ •(bK a+bK b),
   (g (bK b))⁻¹ •(bK b-bK a),by simp[k,n],
   by simp[j,l],?_⟩
  intro c d i;by_cases m:c=a
  ·subst c;by_cases q:d=b
   ·subst d;simp[bK,hab,hab.symm]
   ·simp[bK,hab,Ne.symm i,q]
  ·by_cases o:c=b
   ·subst c;by_cases p:d=a
    ·subst d;simp[bK,hab,hab.symm]
    ·simp[bK,m,Ne.symm i,p]
   ·simp[bK,Pi.single_apply,m,o]
lemma cD (M:aC) (i j:Fin 4) (a:i≠j)
  (h:∀c d:Fin 5,c≠d→M (i,c)*M (j,d)+M (i,d)*M (j,c)=0):
  aO M=0:=by
 classical
 let τ:=Equiv.swap i j
 let E:=Equiv.embeddingCongr τ (Equiv.refl (Fin 5))
 let w (e:Fin 4 ↪ Fin 5):=∏r,M (r,e r)
 have f (e:Fin 4 ↪ Fin 5) (r:Fin 4):E e r=e (Equiv.swap i j r):=by change e ((Equiv.swap i j).symm r)=_;rw[Equiv.symm_swap]
 let S:Finset (Fin 4):=(univ.erase i).erase j
 have aAg (e:Fin 4 ↪ Fin 5):
   w e=M (i,e i)*M (j,e j)*∏r∈S,M (r,e r):=by
  change(∏r,M (r,e r))=_;rw[←mul_prod_erase univ (fun r=>M (r,e r)) (mem_univ i),←mul_prod_erase (univ.erase i) (fun r=>M (r,e r)) (mem_erase.mpr ⟨a.symm,mem_univ j⟩)];exact(mul_assoc _ _ _).symm
 have b (e:Fin 4 ↪ Fin 5):w e+w (E e)=0:=by
  have l:(∏r∈S,M (r,E e r))=∏r∈S,M (r,e r):=by
   apply prod_congr rfl;intro r n;obtain⟨k,g,_⟩:=(show r≠j∧r≠i∧r∈univ by simpa[S] using n)
   rw[f,Equiv.swap_apply_of_ne_of_ne g k]
  rw[aAg,aAg,l,f,f];simp only[Equiv.swap_apply_left,Equiv.swap_apply_right];rw[←add_mul,h _ _ (fun m=>a (e.injective m)),zero_mul]
 have zero:(∑e,w e)+(∑e,w e)=0:=by
  calc
   _=(∑e,w e)+(∑e,w (E e)):=by rw[E.sum_comp w]
   _=∑e,(w e+w (E e)):=Finset.sum_add_distrib.symm
   _=0:=sum_eq_zero (fun e _=>b e)
 change(∑e,w e)=0;linear_combination zero/2
lemma lB (L:Submodule ℂ aC) (hL:∀t∈L,aO (1+t)≠0)
  (i j:Fin 4) (w:i≠j):
  Module.finrank ℂ (L.map ((row i).prod (row j)))≤7:=by
 classical
 obtain⟨f,k,s⟩:=lO L hL i;obtain⟨g,l,v⟩:=lO L hL j
 let P:=L.map ((row i).prod (row j))
 let H:=(LinearMap.ker f).prod (LinearMap.ker g)
 have n:P≤H:=by rintro _ ⟨t,b,rfl⟩;exact⟨s t b,v t b⟩
 have a (u:Module.Dual ℂ aH) (C:u 1=1):Module.finrank ℂ (LinearMap.ker u)=4:=by
  have B:u≠0:=by rintro rfl;simp at C
  have h:=Module.Dual.finrank_ker_add_one_of_ne_zero B;have d:Module.finrank ℂ aH=5:=by simp[aH]
  omega
 have dimH:Module.finrank ℂ H=8:=by rw[((LinearMap.ker f).prodEquiv (LinearMap.ker g)).finrank_eq,Module.finrank_prod,a f k,a g l]
 change Module.finrank ℂ P≤7;by_contra! A;have q:P=H:=Submodule.eq_of_le_of_finrank_le n (by omega);obtain⟨x,y,E,F,m⟩:=aBr f g k l;have z:(x-1,y-1)∈P:=by rw[q];exact⟨by simp[LinearMap.mem_ker,E,k],by simp[LinearMap.mem_ker,F,l]⟩
 obtain⟨t,b,r⟩:=z;have o (c):(1+t) (i,c)=x c:=by have e:t (i,c)=x c-1:=congrFun (congrArg Prod.fst r) c;change 1+t (i,c)=x c;rw[e];ring
 have p (c):(1+t) (j,c)=y c:=by have e:t (j,c)=y c-1:=congrFun (congrArg Prod.snd r) c;change 1+t (j,c)=y c;rw[e];ring
 apply hL t b (cD _ i j w ?_);simpa only[o,p] using m
end Aa
namespace Aa
def cW (t:aC):ℂ:=(∑i:Fin 4,∑j,t (i,j))
def pQ (t:aC):ℂ:=(∑j,∑l,if j=l then 0 else ∑a:Fin 4,∑b:Fin 4,if a<b then t (a,j)*t (b,l) else 0)
def pR (t:aC):ℂ:=(∑j,∑l,∑m,if j=l∨j=m∨l=m then 0 else ∑a:Fin 4,∑b:Fin 4,∑c:Fin 4,if a<b∧b<c then t (a,j)*t (b,l)*t (c,m) else 0)
def yW (t:aC):ℂ:=(∑j,∑l,∑m,∑n,if j=l∨j=m∨j=n∨l=m∨l=n∨m=n then 0 else t (0,j)*t (1,l)*t (2,m)*t (3,n))
lemma vH (f:Fin 5→ℂ):
  ∑j,f j=f 0+f 1+f 2+f 3+f 4:=by
 simp[Fin.sum_univ_succ];ring
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
lemma oD (t:aC):
  aO (1+t)=120+24*cW t+6*pQ t+2*pR t+yW t:=by
 rw[cK];simp(config:={decide:=true}) only[cW,pQ,pR,yW,vH,Fin.sum_univ_four,Pi.add_apply,Pi.one_apply,ite_true,ite_false,add_zero,zero_add];ring
end Aa
namespace Ac
open Aa
abbrev aD (L:Submodule ℂ aC):=∀t∈L,aO (1+t)=120
abbrev aX (L:Submodule ℂ aC):=Module.finrank ℂ L
def aZ (L:Submodule ℂ aC) (i:Fin 4):Submodule ℂ aC:=L⊓ ⨅ r:{r:Fin 4//r≠i},LinearMap.ker (row r.val)
abbrev u (L:Submodule ℂ aC) (i:Fin 4):=aX (aZ L i)
abbrev p (L:Submodule ℂ aC) (i j:Fin 4):=Module.finrank ℂ (L.map ((row i).prod (row j)))
abbrev vI (M:Submodule ℂ aC):=∃a b:Fin 5,a≠b∧∀x∈M,∀i,x (i,a)=x (i,b)
abbrev vJ:=∀L,aD L→aX L=8→∀i,4≤u L i→False
abbrev MidCase:=∀L,aD L→aX L=8→∀i,2≤u L i→u L i≤3→False
abbrev mI:=∀L,aD L→aX L=8→∀i,u L i=1→∃M,aD M∧aX M=7∧vI M
abbrev eI:=∀M,aD M→aX M=7→vI M→False
abbrev HighPair:=∀L,aD L→aX L=8→(∀i,u L i=0)→∀i j,i≠j→p L i j=7→False
abbrev vK:=∀L,aD L→aX L=8→(∀i,u L i=0)→(∀i j,i≠j→p L i j≤6)→False
lemma aAl (L:Submodule ℂ aC) (a:8≤aX L):
  ∃S:Submodule ℂ aC,S≤L∧aX S=8:=by
 obtain⟨f,b⟩:=exists_linearIndependent_of_le_finrank (R:=ℂ) (M:=L) a;have c:LinearIndependent ℂ (fun i=>(L.subtype (f i):aC)):=b.map' L.subtype (Submodule.ker_subtype L);refine⟨Submodule.span ℂ (Set.range fun i=>(L.subtype (f i):aC)),?_,?_⟩
 ·rw[Submodule.span_le];rintro _ ⟨i,rfl⟩;exact(f i).2
 ·unfold aX;rw[finrank_span_eq_card c];simp
lemma aDd {L:Submodule ℂ aC} (hL:aD L) {i j:Fin 4} (a:i≠j):
  p L i j≤7:=by
 apply lB L _ i j a;intro t b;rw[hL t b];norm_num
lemma aDe (g:vJ) (t:MidCase) (one:mI) (gF:eI)
  (k:HighPair) (s:vK) {L:Submodule ℂ aC} (r:aD L):aX L≤7:=by
 classical
 by_contra! l;obtain⟨S,z,e⟩:=aAl L l;have d:aD S:=fun x h=>r x (z h)
 by_cases n:∃i,2≤u S i
 ·obtain⟨i,c⟩:=n;by_cases y:4≤u S i
  ·exact g S d e i y
  ·exact t S d e i c (by omega)
 by_cases o:∃i,u S i=1
 ·obtain⟨i,c⟩:=o;obtain⟨M,w,m,v⟩:=one S d e i c;exact gF M w m v
 have q (i:Fin 4):u S i=0:=by
  have a:¬2≤u S i:=fun c=>n ⟨i,c⟩
  have b:u S i≠1:=fun c=>o ⟨i,c⟩
  omega
 apply s S d e q;intro i j f;have B:=aDd d f;have A:p S i j≠7:=fun h=>k S d e q i j f h
 omega
lemma aAm (e:vJ) (i:MidCase) (one:mI) (gF:eI)
  (f:HighPair) (g:vK) (L:Submodule ℂ aC)
  (h:∀t∈L,cW t=0∧pQ t=0∧pR t=0∧yW t=0):aX L≤7:=by
 apply aDe e i one gF f g;intro x j;obtain⟨a,b,c,d⟩:=h x j;rw[oD,a,b,c,d];ring
end Ac
namespace Ac
namespace Av
open Aa Finset
def G3 (j:Fin 5) (x y z:aH):ℂ:=∑l,∑m,∑n,if j=l∨j=m∨j=n∨l=m∨l=n∨m=n then 0 else x l*y m*z n
lemma sX (M:aC):
  aO M=∑j,M (0,j)*G3 j (fun l=>M (1,l)) (fun l=>M (2,l)) (fun l=>M (3,l)):=by
 rw[cK];simp only[G3,mul_sum,mul_ite,mul_zero,mul_assoc]
lemma cJ (j:Fin 5) (x y z:aH):
  G3 j x y z=((∑l,x l)-x j)*((∑l,y l)-y j)*((∑l,z l)-z j)
   -((∑l,x l)-x j)*((∑l,y l*z l)-y j*z j)
   -((∑l,y l)-y j)*((∑l,x l*z l)-x j*z j)
   -((∑l,z l)-z j)*((∑l,x l*y l)-x j*y j)
   +2*((∑l,x l*y l*z l)-x j*y j*z j):=by
 rcases (by revert j;decide:j=0∨j=1∨j=2∨j=3∨j=4) with rfl|rfl|rfl|rfl|rfl<;>
 ·simp(config:={decide:=true}) only[G3,Fin.sum_univ_five,ite_true,ite_false,
   zero_add,add_zero]
  ring
def S1 (j:Fin 5) (x y z:aH):ℂ:=((∑l,x l)-x j)+((∑l,y l)-y j)+((∑l,z l)-z j)
def Q2 (j:Fin 5) (x y z:aH):ℂ:=
 ((∑l,x l)-x j)*((∑l,y l)-y j)+((∑l,x l)-x j)*((∑l,z l)-z j)
   +((∑l,y l)-y j)*((∑l,z l)-z j)
   -
    (((∑l,x l*y l)-x j*y j)+((∑l,x l*z l)-x j*z j)
    +((∑l,y l*z l)-y j*z j))
lemma aEm (c:ℂ) (j:Fin 5) (x y z:aH):
  G3 j (fun l=>1+c*x l) (fun l=>1+c*y l) (fun l=>1+c*z l)=24+6*c*S1 j x y z+2*c^2*Q2 j x y z+c^3*G3 j x y z:=by
 simp only[cJ,S1,Q2,Fin.sum_univ_five];ring
lemma aBs (j:Fin 5):G3 j (fun _=>1) (fun _=>1) (fun _=>1)=24:=by simp[cJ];norm_num
lemma yI (σ:Equiv.Perm (Fin 4)) (M:aC):
  aO (fun p=>M (σ p.1,p.2))=aO M:=by
 rw[aO,aO,←(Equiv.embeddingCongr σ (.refl _)).sum_comp (fun e=>∏r,M (r,e r))];refine sum_congr rfl fun e _=> ?_
 rw[←Equiv.prod_comp σ (fun r=>M (r,_))];simp[Equiv.embeddingCongr_apply]
def eJ (i:Fin 4) (w:aH):aC:=fun p=>if p.1=i then w p.2 else 0
lemma vL (T:Finset (Fin 5)) (c:2<T.card) {t:Fin 5} (m:t∉T):
  ∃w:aH,(∀x∉T,w x=0)∧∑x,w x=0∧G3 t w w w≠0:=by
 obtain⟨i,j,k,g,h,l,d,e,f⟩:=Finset.two_lt_card_iff.mp c
 let w:aH:=fun x=>(if x=i then 1 else 0)+(if x=j then 1 else 0)+(if x=k then-2 else 0)
 have a:∑x,w x=0:=by norm_num[w,sum_add_distrib]
 have b (x:Fin 5):w x*w x*w x=(if x=i then 1 else 0)+(if x=j then 1 else 0)+(if x=k then-8 else 0):=by grind
 refine⟨w,fun x n=>by grind,a,?_⟩;rw[cJ,a,show w t=0 by grind];simp[b,sum_add_distrib];norm_num
section
variable {P : Type*} [AddCommGroup P] [Module ℂ P]
lemma dE (f g:P→ₗ[ℂ] ℂ) (h:∀x,f x*g x=0):f=0∨g=0:=by by_contra! a;simp only[ne_eq,LinearMap.ext_iff,LinearMap.zero_apply,not_forall] at a;obtain⟨⟨x,b⟩,⟨y,c⟩⟩:=a;have:=h x;have:=h y;have:=h (x+y);simp only[map_add] at*;grind
variable [FiniteDimensional ℂ P]
lemma yJ {k:Fin 5} (f:P→ₗ[ℂ] ({j//j≠k}→ℂ))
  (a:Function.Injective f) (b:3<Module.finrank ℂ P):Function.Surjective f:=
 (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
   have:=LinearMap.finrank_le_finrank_of_injective a;have:Module.finrank ℂ ({j//j≠k}→ℂ)=4:=by simp[Fintype.card_subtype_compl]
   omega)).mp a
lemma vM (f:Fin 5→P→ₗ[ℂ] ℂ) (o:∀x,(∀i,f i x=0)→x=0)
  (t:∀x j,G3 j (f · x) (f · x) (f · x)=0):Module.finrank ℂ P≤3:=by
 by_contra! g
 let d (i:Fin 5):P→ₗ[ℂ] ({j//j≠i}→ℂ):=LinearMap.pi fun j=>f j.1
 have e (i:Fin 5):¬ ∃x:P,d i x=1:=by
  rintro⟨x,w⟩;have y (j:Fin 5) (a:j≠i):f j x=1:=congrFun w ⟨j,a⟩;have s:(0:ℂ)=24:=by rw[←t x i,←aBs i];unfold G3;exact sum_congr rfl fun l _=>sum_congr rfl fun m _=>sum_congr rfl fun n _=>by split_ifs<;>[rfl;grind]
  norm_num at s
 have b (i:Fin 5):∃x:P,∀j,f j x=if j=i then 1 else 0:=by
  obtain⟨x,c,q⟩:=Submodule.exists_mem_ne_zero_of_ne_bot (p:=LinearMap.ker (d i))
   fun k=>e i (yJ (d i) (LinearMap.ker_eq_bot.mp k) g 1)
  have r (j:Fin 5) (a:j≠i):f j x=0:=congrFun c ⟨j,a⟩;have v:f i x≠0:=fun h=>q (o x fun j=>if a:j=i then a▸h else r j a)
  exact⟨(f i x)⁻¹ •x,fun j=>by split_ifs with a<;>[simp[a,v];simp[r j a]]⟩
 choose u hu using b
 exact e 0 ⟨∑i,u i,funext fun j=>by simp[d,map_sum,hu]⟩
lemma xO (a b:Fin 5→P→ₗ[ℂ] ℂ)
  (E:∀x,(∀i,a i x=0)→(∀i,b i x=0)→x=0)
  (z:∀x i,(2*a i x- ∑j,a j x)*(2*b i x- ∑j,b j x)=(∑j,a j x)*(∑j,b j x))
  (M:∀x j,G3 j (a · x) (a · x) (a · x)+G3 j (b · x) (b · x) (b · x)=0):
  Module.finrank ℂ P≤3:=by
 classical
 by_cases g:∑j,b j=0∨∑j,a j=0
 ·wlog K:∑j,b j=0 generalizing a b
  ·exact this b a (fun x V U=>E x U V) (fun x i=>by simpa only[mul_comm] using z x i) (fun x j=>by simpa only[add_comm] using M x j) g.symm (g.resolve_left K)
  have o (x:P):∑j,b j x=0:=by simpa[LinearMap.sum_apply] using LinearMap.congr_fun K x
  let S:=Finset.univ.filter fun i=>b i≠0
  have l (i:Fin 5) (c:i∈S) (x:P):2*a i x=∑j,a j x:=by
   have h:=(dE ((2:ℂ)•a i- ∑j,a j) ((2:ℂ)•b i)
    fun y=>by simpa[LinearMap.sum_apply,o y] using z y i).resolve_right (by simp[(mem_filter.mp c).2])
   exact sub_eq_zero.mp (by simpa[LinearMap.sum_apply] using LinearMap.congr_fun h x)
  have s (i:Fin 5) (c:i∉S) (x:P):b i x=0:=by simp[show b i=0 by simpa[S] using c]
  by_cases Q:S.Nonempty
  ·by_cases C:∃q,q∉S
   ·obtain⟨p,hp⟩:= Q;obtain⟨q,a1⟩:=C;have n {u v:aH} (G:∀i∈S,2*u i=∑j,u j) (H:∀i∉S,v i=0)
      (d:∑j,v j=0) (hf:∀i≠q,(if i=p∨i∉S then u i else v i)=0):u=0∧v=0:=by
     have us:∑j,u j=0:=by have:=hf p (by grind);have:=G p hp;grind
     have z1 {w:aH} (k:Fin 5) (J:∑j,w j=0) (hk:∀i≠k,w i=0):w=0:=funext fun i=>if c:i=k then c▸(sum_eq_single_of_mem k (mem_univ _) fun j _=>hk j).symm.trans J else hk i c
     exact⟨z1 q us fun i c=>by have:=hf i c;grind,z1 p d fun i c=>if hS:i∈S then by have:=hf i (by grind);grind else H i hS⟩
    by_contra! X
    let F:P→ₗ[ℂ] ({i//i≠q}→ℂ):=LinearMap.pi fun i=>if i.1=p∨i.1∉S then a i else b i
    have hF (x:P) (i:Fin 5) (c:i≠q):F x ⟨i,c⟩=if i=p∨i∉S then a i x else b i x:=by simp only[F,LinearMap.pi_apply];split_ifs<;>rfl
    have Z:Function.Injective F:=(injective_iff_map_eq_zero F).mpr fun x e=>by
     obtain⟨R,T⟩:=n (l · · x) (s · · x) (o x) fun i c=>(hF x i c).symm.trans (congrFun e ⟨i,c⟩)
     exact E x (congrFun R) (congrFun T)
    obtain⟨u,v,t,G,H,d,r⟩:∃u v t,(∀i∈S,2*u i=∑j,u j)∧
      (∀i∉S,v i=0)∧∑j,v j=0∧G3 t u u u+G3 t v v v≠0:=by
     have O (k:Fin 5):G3 k 0 0 0=0:=by simp[cJ]
     by_cases N:2<S.card
     ·obtain⟨v,H,d,r⟩:=vL S N a1;exact⟨0,v,q,by simp,H,d,by simpa[O] using r⟩
     ·obtain⟨u,G,a2,r⟩:=vL Sᶜ (by rw[card_compl];simp;omega) (by simpa using hp);exact⟨u,0,p,fun i c=>by rw[G i (by simpa using c),a2,mul_zero],by simp,by simp,by simpa[O] using r⟩
    obtain⟨x,e⟩:=yJ F Z X fun i=>if i.1=p∨i.1∉S then u i.1 else v i.1
    obtain⟨R,T⟩:=n (u:=(a · x)-u) (v:=(b · x)-v)
     (fun i c=>by simp[sum_sub_distrib,mul_sub,l i c x,G i c])
     (fun i c=>by simp[s i c x,H i c])
     (by simp[sum_sub_distrib,o x,d])
     fun i c=>by have:=(hF x i c).symm.trans (congrFun e ⟨i,c⟩);split_ifs at this ⊢ <;>exact sub_eq_zero.mpr this
    exact r (sub_eq_zero.mp R▸sub_eq_zero.mp T▸M x t)
   ·have m (i:Fin 5):i∈S:=by_contra fun h=>C ⟨i,h⟩
    have az (x:P) (i:Fin 5):a i x=0:=by
     have:2*∑j,a j x=5*∑j,a j x:=by rw[mul_sum,sum_congr rfl fun j _=>l j (m j) x];simp
     have:=l i (m i) x;grind
    exact vM b (fun x V=>E x (az x) V) fun x j=>by simpa[az,cJ] using M x j
  ·have bz (x:P) (i:Fin 5):b i x=0:=s i (fun c=>Q ⟨i,c⟩) x;exact vM a (fun x U=>E x U (bz x)) fun x j=>by simpa[bz,cJ] using M x j
 ·obtain⟨K,hA⟩:=not_or.mp g
  let A:P→ₗ[ℂ] ℂ:=∑j,a j
  let B:P→ₗ[ℂ] ℂ:=∑j,b j
  obtain⟨y,a0⟩:∃y,A y*B y≠0:=by by_contra! hz;exact(dE A B hz).elim hA K
  simp only[A,B,LinearMap.sum_apply] at a0;refine(LinearMap.finrank_le_finrank_of_injective (f:=A.prod B) ?_).trans (by norm_num[Module.finrank_prod]);refine(injective_iff_map_eq_zero (A.prod B)).mpr fun x e=> ?_
  change(A x,B x)=0 at e;simp only[A,B,Prod.mk_eq_zero,LinearMap.sum_apply] at e;have J (i:Fin 5):a i x=0∧b i x=0:=by have h1:=z x i;have h2:=z y i;have h3:=z (x+y) i;simp only[map_add,sum_add_distrib,e.1,e.2,zero_add] at h1 h3;rcases mul_eq_zero.mp (show a i x*b i x=0 by grind) with h|h<;>grind
  exact E x (fun i=>(J i).1) (fun i=>(J i).2)
end
lemma vN (ω:ℂ) (hω:ω^2+ω+1=0) (j:Fin 5) (a b:aH):
  let x:=fun l=>a l+b l
  let y:=fun l=>ω*a l+ω^2*b l
  let z:=fun l=>ω^2*a l+ω*b l
  Q2 j x y z=3*((∑l,a l*b l)-(∑l,a l)*(∑l,b l)+a j*(∑l,b l)+(∑l,a l)*b j-2*(a j*b j))∧
  G3 j x y z=G3 j a a a+G3 j b b b:=by
 dsimp only;have g:(fun l=>a l+b l)=(fun l=>1*a l+1*b l):=by simp
 rw[g];have h (c d:ℂ):∑l,(c*a l+d*b l)=c*∑l,a l+d*∑l,b l:=by simp[sum_add_distrib,←mul_sum]
 have s2 (c d e f:ℂ):∑l,(c*a l+d*b l)*(e*a l+f*b l)=
   c*e*∑l,a l*a l+(c*f+d*e)*∑l,a l*b l+d*f*∑l,b l*b l:=by
  simp only[mul_sum,←sum_add_distrib];exact sum_congr rfl fun l _=>by ring
 have i:∑l,(1*a l+1*b l)*(ω*a l+ω^2*b l)*(ω^2*a l+ω*b l)=
   (∑l,a l*a l*a l)+∑l,b l*b l*b l:=by
  rw[←sum_add_distrib];exact sum_congr rfl fun l _=>by grind
 rw[Q2,cJ,cJ,cJ];simp only[h,s2,i];exact⟨by grind,by grind⟩
lemma aG7 (L:Submodule ℂ aC) (hL:aD L) (hu:4≤u L 0):aX L≤7:=by
 classical
 let y:Module.Dual ℂ aH:=∑l,(LinearMap.proj l:aH→ₗ[ℂ] ℂ)
 have z (v:aH):y v=∑l,v l:=by simp[y,LinearMap.sum_apply]
 have a2:Module.finrank ℂ (LinearMap.ker y)=4:=by
  have:=Module.Dual.finrank_ker_add_one_of_ne_zero (f:=y) fun h=>by have:=LinearMap.congr_fun h 1;simp[z] at this
  have:Module.finrank ℂ aH=5:=by simp[aH]
  omega
 let R:=aZ L 0
 have x {t:aC} (o:t∈R) (r:Fin 4) (B:r≠0) (c:Fin 5):t (r,c)=0:=congrFun ((Submodule.mem_iInf _).mp (Submodule.mem_inf.mp o).2 ⟨r,B⟩) c;have X:R.map (row 0)=LinearMap.ker y:=by
  have J:R.map (row 0)≤LinearMap.ker y:=by rintro _ ⟨t,o,rfl⟩;rw[LinearMap.mem_ker,z];change ∑l,t (0,l)=0;have h:=sX _▸hL t o.1;simp only[Pi.add_apply,Pi.one_apply,x o 1 (by decide),x o 2 (by decide),x o 3 (by decide),add_zero,aBs,←sum_mul,sum_add_distrib] at h;simp at h;linear_combination h/24
  have U:Function.Injective ((row 0).domRestrict R):=
   (injective_iff_map_eq_zero _).mpr fun t h=>Subtype.ext<| funext fun⟨r,c⟩=>
     if B:r=0 then B▸congrFun h c else x t.2 r B c
  have T:=LinearMap.finrank_range_of_inj U;rw[LinearMap.range_domRestrict] at T;have:=Submodule.finrank_mono J;have:4≤Module.finrank ℂ R:=hu;exact Submodule.eq_of_le_of_finrank_eq J (by omega)
 let e (t:aC) (k:Fin 4):aH:=fun l=>t (k,l)
 have F (t:aC) (o:t∈L):(∑l,t (0,l)=0)∧∀j,
   S1 j (e t 1) (e t 2) (e t 3)=0∧Q2 j (e t 1) (e t 2) (e t 3)=0∧G3 j (e t 1) (e t 2) (e t 3)=0:=by
  let g (c:ℂ) (j:Fin 5):ℂ:=G3 j (fun l=>1+c*e t 1 l) (fun l=>1+c*e t 2 l) (fun l=>1+c*e t 3 l)
  have H (c:ℂ) (w:aH) (hw:∑l,w l=0):∑j,(1+c*t (0,j)+w j)*g c j=120:=by obtain⟨s,C,a1⟩:=Submodule.mem_map.mp (X.symm▸(LinearMap.mem_ker.mpr ((z w).trans hw)));simpa[sX,g,e,←a1,row,x C 1 (by decide),x C 2 (by decide),x C 3 (by decide),add_assoc] using hL _ (L.add_mem (L.smul_mem c o) C.1)
  have aEx (c:ℂ):∑j,(1+c*t (0,j))*g c j=120:=by simpa using H c 0 (by simp)
  have G (c:ℂ) (j:Fin 5):g c j=g c 0:=by have h:=H c (Pi.single j 1-Pi.single 0 1) (by simp);have A:=aEx c;simp[add_mul,sub_mul,sum_add_distrib,Pi.single_apply] at h A;linear_combination h-A
  have prod (c:ℂ):(5+c*∑l,t (0,l))*g c 0=120:=by simpa[G c,←sum_mul,sum_add_distrib,←mul_sum] using aEx c
  have M:∑l,t (0,l)=0:=by by_contra a0;have h:=prod (-5/∑l,t (0,l));rw[div_mul_cancel₀ _ a0] at h;norm_num at h
  refine⟨M,fun j=> ?_⟩;have val (c:ℂ):g c j=24:=by rw[G c j];linear_combination(prod c-M*c*g c 0)/5
  have h1:=val 1;have h2:=val (-1);have V:=val 2;simp only[g,aEm] at h1 h2 V;exact⟨by grind,by grind,by grind⟩
 obtain⟨r,B⟩:=IsAlgClosed.exists_pow_nat_eq (-3:ℂ) (n:=2) (by norm_num)
 let ω:ℂ:=(-1+r)/2
 have hω:ω^2+ω+1=0:=by linear_combination B/4
 let P:Submodule ℂ aC:=L⊓LinearMap.ker (row 0)
 let mk (c d:ℂ) (j:Fin 5):P→ₗ[ℂ] ℂ:=
  ((1/3:ℂ)•((LinearMap.proj ((1:Fin 4),j):aC→ₗ[ℂ] ℂ)
    +c•LinearMap.proj ((2:Fin 4),j)+d•LinearMap.proj ((3:Fin 4),j)))∘ₗ P.subtype
 let a:=mk (ω^2) ω
 let b:=mk ω (ω^2)
 have q (c d:ℂ) (j:Fin 5) (p:P):mk c d j p=1/3*(p.1 (1,j)+c*p.1 (2,j)+d*p.1 (3,j)):=rfl;have jS (p:P) (l:Fin 5):p.1 (1,l)+p.1 (2,l)+p.1 (3,l)=0:=by
  have m:=sum_eq_zero fun j (_:j∈univ)=>((F p.1 p.2.1).2 j).1
  have Z:=((F p.1 p.2.1).2 l).1;simp only[S1,e,sum_add_distrib,sum_sub_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at m Z;linear_combination m/4-Z
 have N (p:P):e p.1 1=fun l=>a l p+b l p:=funext fun l=>by have:=jS p l;dsimp[a,b,e];rw[q,q];grind
 have O (p:P):e p.1 2=fun l=>ω*a l p+ω^2*b l p:=funext fun l=>by have:=jS p l;dsimp[a,b,e];rw[q,q];grind
 have Q (p:P):e p.1 3=fun l=>ω^2*a l p+ω*b l p:=funext fun l=>by have:=jS p l;dsimp[a,b,e];rw[q,q];grind
 have C (p:P) (S:∀j,a j p=0) (A:∀j,b j p=0):p=0:=by
  ext ⟨i,l⟩;fin_cases i
  ·exact congrFun p.2.2 l
  ·simpa[e,S,A] using congrFun (N p) l
  ·simpa[e,S,A] using congrFun (O p) l
  ·simpa[e,S,A] using congrFun (Q p) l
 have hq (p:P) (j:Fin 5):
   (2*a j p- ∑l,a l p)*(2*b j p- ∑l,b l p)=(∑l,a l p)*(∑l,b l p):=by
  have K (E:Fin 5):=((vN ω hω E (a · p) (b · p)).1).symm.trans
   (N p▸O p▸Q p▸((F p.1 p.2.1).2 E).2.1)
  have m:=sum_eq_zero fun E (_:E∈univ)=>K E
  simp only[←mul_sum,sum_sub_distrib,sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,←sum_mul] at m;linear_combination(-2/3:ℂ)*K j+(2/9:ℂ)*m
 have hc (p:P) (j:Fin 5):G3 j (a · p) (a · p) (a · p)+G3 j (b · p) (b · p) (b · p)=0:=((vN ω hω j (a · p) (b · p)).2).symm.trans (N p▸O p▸Q p▸((F p.1 p.2.1).2 j).2.2);have V:=xO a b C hq hc;have d:Module.finrank ℂ (L.map (row 0))+Module.finrank ℂ P=Module.finrank ℂ L:=by
  rw[←(Submodule.submoduleOfEquivInf _ _).finrank_eq,
   ←((row 0).submoduleMap L).finrank_range_add_finrank_ker,
   LinearMap.range_submoduleMap,LinearMap.ker_submoduleMap]
  simp
 have hm:=Submodule.finrank_mono (show L.map (row 0)≤LinearMap.ker y by rintro _ ⟨t,o,rfl⟩;rw[LinearMap.mem_ker,z];exact(F t o).1);unfold aX;omega
end Av
open Aa in
lemma aEn:vJ:=by
 intro L hL j i f
 let σ:Equiv.Perm (Fin 4):=Equiv.swap 0 i
 let Φ:aC≃ₗ[ℂ] aC:=LinearEquiv.funCongrLeft ℂ ℂ (Equiv.prodCongr σ (.refl _))
 let L':Submodule ℂ aC:=L.map Φ.toLinearMap
 have c:aD L':=by rintro _ ⟨t,a,rfl⟩;exact(Av.yI σ (1+t)).trans (hL t a)
 have b:(aZ L i).map Φ.toLinearMap≤aZ L' 0:=by rintro _ ⟨t,a,rfl⟩;refine⟨⟨t,a.1,rfl⟩,Submodule.mem_iInf _|>.mpr fun⟨r,d⟩=> ?_⟩;exact(Submodule.mem_iInf _|>.mp (Submodule.mem_inf.mp a).2) ⟨σ r,fun h=>d (σ.injective (h.trans (Equiv.swap_apply_left 0 i).symm))⟩
 have g:=Av.aG7 L' c
  (f.trans ((LinearEquiv.finrank_map_eq Φ _).symm.le.trans (Submodule.finrank_mono b)))
 have e:aX L'=aX L:=LinearEquiv.finrank_map_eq Φ L;omega
end Ac
namespace Ac.Ad
open Aa Finset
lemma cT {L:Submodule ℂ aC} (hL:aD L) {x:aC} (a:x∈L):
  cW x=0∧pQ x=0∧pR x=0∧yW x=0:=by
 have h (s:ℂ):
   120+24*(s*cW x)+6*(s^2*pQ x)+2*(s^3*pR x)+s^4*yW x=120:=by
  have e (v w:ℂ):s*v*(s*w)=s^2*(v*w):=by ring
  have f (n:ℕ) (v w:ℂ):(s^n*v)*(s*w)=s^(n+1)*(v*w):=by ring
  simpa only[cW,pQ,pR,yW,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,mul_ite,mul_zero,e,f] using(oD (s•x)).symm.trans (hL _ (L.smul_mem s a))
 have:=h 1;have:=h (-1);have:=h 2;have:=h (-2);exact⟨by grobner,by grobner,by grobner,by grobner⟩
def kK (x y:aC):ℂ:=∑i:Fin 4,∑j:Fin 5,x (i,j)*y (i,j)
abbrev aS:=cW
abbrev gR (x:aC) (i:Fin 4):=∑j:Fin 5,x (i,j)
abbrev gC (x:aC) (j:Fin 5):=∑i:Fin 4,x (i,j)
def gQ (x:aC):aC:=fun p=>x p-gR x p.1-gC x p.2+aS x
def bQ (F:aC):aC:=fun p=>F p-gR F p.1/4-gC F p.2/3+19*aS F/240
def gr (F G:aC):ℂ:=kK F (bQ G)
def B (x y:aC):ℂ:=kK x y-(∑i,gR x i*gR y i)-(∑j,gC x j*gC y j)+aS x*aS y
lemma sY (x y:aC):B x y=B y x:=by simp only[B,kK,mul_comm]
lemma qS (x y z:aC):B (x+y) z=B x z+B y z:=by simp only[B,gR,gC,kK,aS,cW,Pi.add_apply,add_mul,Finset.sum_add_distrib];ring
lemma kR (x y z:aC):B x (y+z)=B x y+B x z:=by rw[sY x,qS,sY y,sY z]
lemma fH (f:Fin 5→ℂ):
  ∑j,f j=f 0+f 1+f 2+f 3+f 4:=by
 simp[Fin.sum_univ_succ];ring
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma aEo (x:aC):2*pQ x=B x x:=by simp(config:={decide:=true}) only[B,pQ,kK,gR,gC,aS,cW,fH,Fin.sum_univ_four,ite_true,ite_false,zero_add,add_zero];ring
lemma aEp (x y:aC):kK (gQ x) y=B x y:=by simp only[kK,B,gQ,sub_mul,add_mul,Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.mul_sum];rw[Finset.sum_comm (f:=fun(i:Fin 4) (j:Fin 5)=>gC x j*y (i,j))];simp only[←Finset.mul_sum,aS,cW,gC,gR]
lemma gM {L:Submodule ℂ aC} (hL:aD L):
  (∀x∈L,aS x=0)∧(∀x∈L,∀y∈L,kK (gQ x) y=0):=by
 refine⟨fun _ a=>(cT hL a).1,?_⟩;have q (v:aC) (c:v∈L):B v v=0:=by rw[←aEo,(cT hL c).2.1,mul_zero]
 intro x a y b;rw[aEp];have h:=q _ (L.add_mem a b);rw[qS,kR,kR,q x a,q y b,sY y x] at h;linear_combination h/2
lemma aF1 (x:aC):aS (gQ x)=12*aS x:=by simp only[gQ,gR,gC,aS,cW,fH,Fin.sum_univ_four];ring
lemma rQ (x:aC) (a:aS x=0):bQ (gQ x)=x:=by
 funext p;simp only[bQ,gQ,gR,gC,aS,cW,Fin.sum_univ_four,fH] at a ⊢
 linear_combination-a/20
def vO:aC→ₗ[ℂ] aC where
 toFun:=bQ
 map_add' x y:=by funext p;simp only[bQ,gR,gC,aS,cW,Pi.add_apply,Finset.sum_add_distrib];ring
 map_smul' c x:=by funext p;simp only[bQ,gR,gC,aS,cW,Pi.smul_apply,smul_eq_mul,←Finset.mul_sum,RingHom.id_apply];ring
lemma aBt:bQ (1:aC)=0:=by funext p;norm_num[bQ,gR,gC,aS,cW]
abbrev oE:=dotProductEquiv ℂ (Fin 4×Fin 5)
lemma fM (x y:aC):oE x y=kK x y:=by change ∑p:Fin 4×Fin 5,x p*y p=_;rw[Fintype.sum_prod_type];rfl
lemma aCu (x y:aC):gr x y=
  kK x y-(∑i,gR x i*gR y i)/4-(∑j,gC x j*gC y j)/3+aS x*(19*aS y/240):=by
 simp only[gr,bQ,kK,gR,gC,aS,cW,Fin.sum_univ_four,fH];ring
lemma aCv (x y:aC):gr x y=gr y x:=by simp only[aCu,kK,mul_comm (x _) _,mul_comm (gR x _) _,mul_comm (gC x _) _];ring
lemma nK {D E:Type*} [AddCommGroup D] [Module ℂ D]
  [FiniteDimensional ℂ D] [AddCommGroup E] [Module ℂ E] (f:D→ₗ[ℂ] E) (L:Submodule ℂ D):
  Module.finrank ℂ (L.map f)+Module.finrank ℂ (L⊓f.ker:Submodule ℂ D)=Module.finrank ℂ L:=by
 rw[←(Submodule.submoduleOfEquivInf _ _).finrank_eq,
  ←(f.submoduleMap L).finrank_range_add_finrank_ker,
  LinearMap.range_submoduleMap,LinearMap.ker_submoduleMap]
 simp
lemma vP {ι:Type} [Fintype ι] (L:Submodule ℂ aC)
  (P Q:ι ↪ Fin 4×Fin 5) (o:∀i j,P i≠Q j)
  (hfix:∀x∈L,∀i,x (P i)=x (Q i))
  (B:∀x∈L,aS x=0) (E:∀x∈L,∀y∈L,kK (gQ x) y=0)
  (F:∀x∈L,∀i,gQ x (P i)=gQ x (Q i)) (C:aX L=7):
  ∃
   S:Submodule ℂ aC,L≤S∧aX S+Fintype.card ι≤12∧
   ∀x:aC,(∀t∈L,kK x t=0)→(∀i,x (P i)=x (Q i))→bQ x∈S:=by
 classical
 let g (k:ι):aC:=Pi.single (P k) 1-Pi.single (Q k) 1
 let gH:=∑k,(LinearMap.proj k:Module.Dual ℂ (ι→ℂ)).smulRight (g k)
 have s (t:ι→ℂ):gH t=∑k,t k•g k:=by simp[gH,LinearMap.sum_apply]
 have l (t:ι→ℂ) (i:ι):gH t (P i)=t i∧gH t (Q i)= -t i:=by simp[s,g,Finset.sum_apply,Pi.single_apply,o,fun a b=>(o a b).symm,mul_ite,P.injective.eq_iff,Q.injective.eq_iff]
 have q:Module.finrank ℂ (LinearMap.range gH)=Fintype.card ι:=by
  rw[LinearMap.finrank_range_of_inj (f:=gH)]
  ·simp
  ·intro x y e;ext i;exact(l x i).1.symm.trans ((congrFun e (P i)).trans (l y i).1)
 have u:Disjoint L (LinearMap.range gH):=by
  apply Submodule.disjoint_def.mpr;rintro _ c ⟨t,rfl⟩;have z:t=0:=by ext i;have e:=hfix _ c i;rw[(l t i).1,(l t i).2] at e;change t i=0;linear_combination e/2
  rw[z,map_zero]
 let T:=L⊔LinearMap.range gH
 let A:=vO.comp oE.symm.toLinearMap
 let S:=T.dualAnnihilator.map A
 have m (x:aC) (r:∀t∈L,kK x t=0) (c:∀i,x (P i)=x (Q i)):
   oE x∈T.dualAnnihilator:=by
  apply(Submodule.mem_dualAnnihilator _).mpr;change T≤LinearMap.ker (oE x);refine sup_le (fun t G=>(fM x t).trans (r t G)) ?_;rintro _ ⟨t,rfl⟩;change oE x (gH t)=0;have v (p:Fin 4×Fin 5):oE x (Pi.single p 1)=x p:=by change x ⬝ᵥ Pi.single p 1=x p;rw[dotProduct_single_one]
  simp only[s,g,map_sum,map_smul,map_sub,v,c,sub_self,smul_zero,sum_const_zero]
 have w (x:aC) (r:∀t∈L,kK x t=0) (c:∀i,x (P i)=x (Q i)):bQ x∈S:=⟨oE x,m x r c,by simp[A,vO]⟩
 refine⟨S,fun x c=>rQ x (B x c)▸w _ (E x c) (F x c),?_,w⟩;have h:=L.finrank_sup_add_finrank_inf_eq (LinearMap.range gH);rw[u.eq_bot,finrank_bot,add_zero,show Module.finrank ℂ L=7 from C,q] at h;have d:=Subspace.finrank_add_finrank_dualAnnihilator_eq T;rw[show Module.finrank ℂ T=_ from h,show Module.finrank ℂ aC=20 by simp[aC]] at d
 let U:=T.dualAnnihilator⊓LinearMap.ker A
 have one:oE 1∈U:=⟨m 1 (by simpa[kK,aS,cW] using B) (fun _=>rfl),by change bQ (oE.symm (oE 1))=0;simpa using aBt⟩
 have lt: ⊥ <U:=bot_lt_iff_ne_bot.mpr (fun e=>by have z:oE 1∈(⊥ :Submodule ℂ (Module.Dual ℂ aC)):=e▸one;simpa using z);have k:=Submodule.finrank_lt_finrank_of_lt lt;rw[finrank_bot] at k;have n:aX S+Module.finrank ℂ U+(7+Fintype.card ι)=20:=by rw[show aX S+Module.finrank ℂ U=_ from nK A T.dualAnnihilator,add_comm];exact d
 omega
lemma aAn (L:Submodule ℂ aC) (a b:Fin 5) (hab:a≠b)
  (hfix:∀x∈L,∀i,x (i,a)=x (i,b))
  (d:∀x∈L,aS x=0)
  (l:∀x∈L,∀y∈L,
    kK (fun p=>x p-(∑j:Fin 5,x (p.1,j))-(∑i:Fin 4,x (i,p.2))+aS x) y=0)
  (q:Module.finrank ℂ L=7) (F G:aC)
  (A:∀i,F (i,a)=F (i,b)) (B:∀i,G (i,a)=G (i,b))
  (g:∀t∈L,kK F t=0) (k:∀t∈L,kK G t=0):
  gr F F*gr G G=gr F G^2∧(gr F G)•bQ F-(gr F F)•bQ G∈L:=by
 obtain⟨S,n,H,o⟩:=vP L ⟨fun i=>(i,a),fun _ _ h=>congrArg Prod.fst h⟩
  ⟨fun i=>(i,b),fun _ _ h=>congrArg Prod.fst h⟩ (fun _ _ h=>hab (congrArg Prod.snd h)) hfix d l (by
    intro x K i;change gQ x (i,a)=gQ x (i,b);simp only[gQ,gC,hfix x K]) q
 have C:aX S≤8:=by simpa using H
 by_cases c:bQ F∈L
 ·have s:gr F F=0:=g _ c;have u:gr F G=0:=(aCv _ _).trans (k _ c);simp[s,u]
 ·have m:L⊔Submodule.span ℂ {bQ F}=S:=by
   apply Submodule.eq_of_le_of_finrank_le
   ·exact sup_le n ((Submodule.span_singleton_le_iff_mem _ _).mpr (o _ g A))
   ·rw[Submodule.finrank_sup_span_singleton c,q];exact C
  obtain⟨v,z,w,J,r⟩:=Submodule.mem_sup.mp (m▸o _ k B);obtain⟨a,rfl⟩:=Submodule.mem_span_singleton.mp J;have eval (x:aC) (E:∀t∈L,kK x t=0):gr x G=a*gr x F:=by change kK x (bQ G)=a*kK x (bQ F);rw[←fM,←r,map_add,map_smul,fM,E _ z,fM,zero_add,smul_eq_mul]
  have e:=eval F g;have f:=eval G k;rw[aCv G F] at f;constructor
  ·rw[f,e];ring
  ·rw[e,←r];convert L.smul_mem (-(gr F F)) z using 1
   module
def oF (x y:aH) (c:Fin 5):ℂ:=∑j,∑k,if c=j∨c=k∨j=k then 0 else x j*y k
def lP (T:aC):aC:=fun p=>
 let r:=fun i j=>oF (row i T) (row j T) p.2
 ![r 1 2+r 1 3+r 2 3,r 2 0+r 3 0+r 2 3,r 0 1+r 3 0+r 3 1,r 0 1+r 0 2+r 1 2] p.1
set_option maxRecDepth 65536 in
set_option maxHeartbeats 24000000 in
lemma yX (T X:aC):
  pR (T+X)-pR (T-X)-2*pR X=2*kK (lP T) X:=by
 simp(config:={decide:=true}) [pR,lP,kK,row,oF,fH,Fin.sum_univ_four,Matrix.cons_val];ring
lemma aEq {L:Submodule ℂ aC} (hL:aD L) {T:aC} (b:T∈L) {X:aC}
  (a:X∈L):kK (lP T) X=0:=by
 have h {v:aC} (c:v∈L):=(cT hL c).2.2.1;linear_combination(h (L.add_mem b a)-h (L.sub_mem b a)-2*h a-yX T X)/2
def pS:aC:=(fun p=> ![![1,1,0,0,0],
 ![0,0,0,0,0],
 ![0,0,0,0,0],
 ![0,0,0,0,0]] p.1 p.2)
def vQ (b x y:ℂ):aC:=(fun p=> ![![0,0,0,0,0],
 ![b,b,x,y,-2*b-x-y+ 1],
 ![0,0,0,0,0],
 ![0,0,0,0,0]] p.1 p.2)
def xP (b x y:ℂ):aC:=(720:ℂ)•
 (gr pS (vQ b x y)•bQ pS-gr pS pS•bQ (vQ b x y))
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 65536 in
lemma aDf (b x y:ℂ)
  (g:gr pS pS*gr (vQ b x y) (vQ b x y)=gr pS (vQ b x y)^2)
  (d:pR (xP b x y)=0) (e:yW (xP b x y)=0)
  (c:gr pS pS*gr (lP (xP b x y)) (lP (xP b x y))=gr pS (lP (xP b x y))^2):False:=by
 generalize et:xP b x y=T at d e c
 have f (i:Fin 4) (j:Fin 5):T (i,j)=xP b x y (i,j):=congrFun et.symm _;simp[Fin.forall_fin_succ,xP,gr,pS,vQ,kK,bQ,aS,cW,gR,gC,fH,Fin.sum_univ_four,Matrix.cons_val] at f;ring_nf at f
 generalize eh:lP T=H at c
 have a (i:Fin 4) (j:Fin 5):H (i,j)=lP T (i,j):=congrFun eh.symm _;simp(config:={decide:=true}) [Fin.forall_fin_succ,lP,row,oF,f,fH,Matrix.cons_val] at a;ring_nf at a;simp(config:={decide:=true}) only[aCu,pR,yW,oF,row,
  gR,gC,aS,cW,kK,pS,vQ,lP,xP,fH,Fin.sum_univ_four,Fin.reduceFinMk,Matrix.cons_val,ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,one_mul,mul_one,LinearMap.funLeft_apply]
  at g d e c
 simp only[f] at d e;simp only[a] at c;ring_nf at g d e c
 grobner
lemma vR (L:Submodule ℂ aC) (hL:aD L) (l:aX L=7)
  (hfix:∀t∈L,∀i,t (i,0)=t (i,1)) (b x y:ℂ)
  (e:∀t∈L,kK pS t=0) (m:∀t∈L,kK (vQ b x y) t=0):False:=by
 obtain⟨g,h⟩:=gM hL;have aCo:=aAn L 0 1 (by decide) hfix g h l;have d (i:Fin 4):pS (i,0)=pS (i,1):=by fin_cases i<;>rfl
 have j (i:Fin 4):vQ b x y (i,0)=vQ b x y (i,1):=by fin_cases i<;>rfl
 obtain⟨f,k⟩:=aCo _ _ d j e m;have c:xP b x y∈L:=L.smul_mem 720 k;obtain⟨_,_,n,o⟩:=cT hL c;have gF {T:aC} (a:T∈L) (i:Fin 4):lP T (i,0)=lP T (i,1):=by fin_cases i<;>simp(config:={decide:=true}) [lP,oF,row,fH,Matrix.cons_val,hfix T a]<;>ring
 exact aDf _ _ _ f n o (aCo _ _ d (gF c) e (fun _ a=>aEq hL c a)).1
lemma uQ (L:Submodule ℂ aC) (hL:aD L) (k:aX L=7)
  (hfix:∀t∈L,∀i,t (i,0)=t (i,1)) (l:∀t∈L,t (0,0)=0):False:=by
 classical
 obtain⟨f,g,e⟩:=Aa.lO L (fun t a=>by rw[hL t a];norm_num) 1
 let u:aH:=fun j=>f (Pi.single j 1)
 have d (x:aH):(∑j,u j*x j)=f x:=by
  conv_rhs=>rw[pi_eq_sum_univ' x,map_sum]
  simp only[u,map_smul,smul_eq_mul,mul_comm (x _) _]
 have m:u 0+u 1+u 2+u 3+u 4=1:=by simpa[fH] using(d 1).trans g
 let b:=(u 0+u 1)/2
 apply vR L hL k hfix b (u 2) (u 3)
 ·intro t a;have c:=(hfix t a 0).symm;simpa[kK,pS,fH,Fin.sum_univ_four,Matrix.cons_val,c,l t a]
 ·intro t a;have h:=(d (row 1 t)).trans (e t a);simp only[fH,row,LinearMap.funLeft_apply] at h;have c:=hfix t a 1;rw[c] at h;simp[kK,vQ,fH,Fin.sum_univ_four,Matrix.cons_val,c,b];linear_combination h-t (1,4)*m
def re (ρ:Equiv.Perm (Fin 4)) (σ:Equiv.Perm (Fin 5)):aC→ₗ[ℂ] aC:=LinearMap.funLeft ℂ ℂ (fun p:Fin 4×Fin 5=>(ρ p.1,σ p.2))
lemma vS (ρ:Equiv.Perm (Fin 4)) (σ:Equiv.Perm (Fin 5)) (x:aC):
  aO (re ρ σ x)=aO x:=by
 let E:=Equiv.embeddingCongr ρ σ
 let v (e:Fin 4 ↪ Fin 5):=∏r,x (r,e r)
 change(∑e:Fin 4 ↪ Fin 5,∏r,x (ρ r,σ (e r)))=∑e,v e;rw[←E.sum_comp v];refine sum_congr rfl fun e _=> ?_
 change _=∏r,x (r,σ (e (ρ.symm r)));simpa using(Equiv.prod_comp ρ (fun r=>x (r,σ (e (ρ.symm r)))))
lemma gI (ρ:Equiv.Perm (Fin 4)) (σ:Equiv.Perm (Fin 5))
  {L:Submodule ℂ aC} (hL:aD L):aD (L.map (re ρ σ)):=by
 rintro _ ⟨x,a,rfl⟩;exact(vS ρ σ (1+x)).trans (hL x a)
lemma nL (ρ:Equiv.Perm (Fin 4)) (σ:Equiv.Perm (Fin 5)) (L:Submodule ℂ aC):
  aX (L.map (re ρ σ))=aX L:=by
 refine(Submodule.equivMapOfInjective (re ρ σ) ?_ L).finrank_eq.symm;intro x y h;funext p;have e:=congrFun h (ρ.symm p.1,σ.symm p.2);simpa[re] using e
lemma aAo {α:Type} [DecidableEq α] (i j a b:α) (c:i≠j) (hab:a≠b):
  ∃σ:Equiv.Perm α,σ i=a∧σ j=b:=by
 have h:Equiv.swap i a b≠i:=by intro e;simpa[hab] using(congrArg (Equiv.swap i a) e).symm
 exact⟨Equiv.swap i a*Equiv.swap j (Equiv.swap i a b),by simp[Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne c h.symm],by simp[Equiv.Perm.mul_apply]⟩
lemma aEr (a b:Fin 5) (hab:a≠b):∃σ:Equiv.Perm (Fin 5),σ 0=a∧σ 1=b:=aAo _ _ _ _ (by decide) hab
lemma aAp {L:Submodule ℂ aC} (hL:aD L) (f:aX L=7)
  {a b:Fin 5} (hab:a≠b) (hfix:∀t∈L,∀i,t (i,a)=t (i,b))
  (r:Fin 4):∃t∈L,t (r,a)≠0:=by
 classical
 by_contra! g
 let ρ:=Equiv.swap 0 r
 obtain⟨σ,d,e⟩:=aEr a b hab;apply uQ (L.map (re ρ σ)) (gI ρ σ hL) ((nL _ _ _).trans f)
 ·rintro _ ⟨t,c,rfl⟩ i;change t (ρ i,σ 0)=t (ρ i,σ 1);rw[d,e];exact hfix t c (ρ i)
 ·rintro _ ⟨t,c,rfl⟩;change t (ρ 0,σ 0)=0;simpa[ρ,d] using g t c
abbrev r (L:Submodule ℂ aC) (i:Fin 4):=Module.finrank ℂ (L.map (row i))
abbrev yY (a b:Fin 5):Module.Dual ℂ aH:=(LinearMap.proj a:Module.Dual ℂ aH)-(LinearMap.proj b:Module.Dual ℂ aH)
abbrev yZ (a b:Fin 5):=LinearMap.ker (yY a b)
lemma aGr {a b:Fin 5} (hab:a≠b):
  Module.finrank ℂ (yZ a b)=4:=by
 have c:yY a b≠0:=by intro e;have h:=DFunLike.congr_fun e (Pi.single a 1:aH);simpa[yY,Pi.single_apply,hab.symm] using h
 have e:=Module.Dual.finrank_ker_add_one_of_ne_zero c;have dv:Module.finrank ℂ aH=5:=by simp[aH]
 change Module.finrank ℂ (yZ a b)+1=_ at e;omega
lemma qT {L:Submodule ℂ aC} (hL:aD L)
  {a b:Fin 5} (hab:a≠b) (hfix:∀t∈L,∀i,t (i,a)=t (i,b)) (i:Fin 4):
  ∃
   f:Module.Dual ℂ aH,f 1=1∧(∀t∈L,f (row i t)=0)∧r L i≤3∧
   (r L i=3→∀z:aH,z a=z b→f z=1→z-1∈L.map (row i)):=by
 obtain⟨f,h,j⟩:=Aa.lO L (fun t c=>by rw[hL t c];norm_num) i
 let W:=yZ a b⊓LinearMap.ker f
 have g:L.map (row i)≤W:=by rintro _ ⟨t,c,rfl⟩;exact⟨sub_eq_zero.mpr (hfix t c i),j t c⟩
 have lt:W<yZ a b:=lt_of_le_of_ne inf_le_left (fun e=>by have z:(1:aH)∈W:=e▸(sub_self (1:ℂ));exact one_ne_zero (h.symm.trans z.2));have w:=Submodule.finrank_lt_finrank_of_lt lt;rw[aGr hab] at w;refine⟨f,h,j,(Submodule.finrank_mono g).trans (Nat.le_of_lt_succ w),?_⟩;intro d z l k;rw[Submodule.eq_of_le_of_finrank_le g (show Module.finrank ℂ W≤ r L i by omega)];exact⟨by change(z a-1)-(z b-1)=0;rw[l,sub_self],by change f (z-1)=0;simp[k,h]⟩
lemma zA {L:Submodule ℂ aC} (hL:aD L)
  {a b:Fin 5} (hab:a≠b) (hfix:∀t∈L,∀i,t (i,a)=t (i,b))
  (i:Fin 4):r L i≤3:=by
 obtain⟨_,_,_,h,_⟩:=qT hL hab hfix i;exact h
abbrev eA (i:Fin 5):aH:=Pi.single i 1
lemma aGk {L:Submodule ℂ aC} (hL:aD L) (l:aX L=7)
  {a b:Fin 5} (hab:a≠b) (hfix:∀t∈L,∀i,t (i,a)=t (i,b)) (i:Fin 4)
  (f:Module.Dual ℂ aH) (g:f 1=1) (m:∀t∈L,f (row i t)=0):
  ∃c:Fin 5,c≠a∧c≠b∧f (eA c)≠0:=by
 classical
 by_contra! o;obtain⟨t,e,n⟩:=aAp hL l hab hfix i
 let z:=row i t-t (i,a)•(1:aH)
 have d:f z=0:=by
  conv_lhs=>rw[pi_eq_sum_univ' z,map_sum]
  apply sum_eq_zero;intro j _;rw[map_smul];by_cases h:j=a
  ·subst j;simp[z,row]
  by_cases k:j=b
  ·subst j;simp[z,row,hfix t e i]
  ·simp[o j h k]
 simp[z,map_sub,m t e,g,n] at d
lemma aDg (f g:Module.Dual ℂ aH) (a b:Fin 5)
  (u:∃c,c≠a∧c≠b∧f (eA c)≠0)
  (v:∃c,c≠a∧c≠b∧g (eA c)≠0):
  ∃
   x y:aH,f x=1∧g y=1∧x a=x b∧y a=y b∧
   ∀c d:Fin 5,c≠d→x c*y d+x d*y c=0:=by
 classical
 by_cases i:∃c,c≠a∧c≠b∧f (eA c)≠0∧g (eA c)≠0
 ·obtain⟨c,j,k,o,n⟩:=i;refine⟨(f (eA c))⁻¹ •eA c,(g (eA c))⁻¹ •eA c,by simp[o],by simp[n],
   by simp[eA,j.symm,k.symm],by simp[eA,j.symm,k.symm],?_⟩
  intro p q r;by_cases e:c=p
  ·subst p;simp[eA,r.symm]
  ·simp[eA,Pi.single_apply,Ne.symm e]
 ·obtain⟨c,j,k,o⟩:=u;obtain⟨d,l,m,n⟩:=v;have s:g (eA c)=0:=by by_contra h;exact i ⟨_,j,k,o,h⟩
  have t:f (eA d)=0:=by by_contra h;exact i ⟨_,l,m,h,n⟩
  have w:c≠d:=by rintro rfl;exact n s
  refine⟨(f (eA c))⁻¹ •(eA c+eA d),(g (eA d))⁻¹ •(eA d-eA c),
   by simp[o,t],by simp[n,s],by simp[eA,j.symm,k.symm,l.symm,m.symm],
   by simp[eA,j.symm,k.symm,l.symm,m.symm],?_⟩
  intro p q r;by_cases z:p=c<;>by_cases A:p=d<;>
   by_cases B:q=c<;>by_cases C:q=d<;>
   simp_all[eA,Pi.single_apply]
lemma aAq (L:Submodule ℂ aC) (i j:Fin 4):
  L.map ((row i).prod (row j))≤(L.map (row i)).prod (L.map (row j)):=by
 rintro _ ⟨t,a,rfl⟩;exact⟨⟨_,a,rfl⟩,⟨_,a,rfl⟩⟩
lemma aCw (L:Submodule ℂ aC) (i j:Fin 4):
  Module.finrank ℂ ((L.map (row i)).prod (L.map (row j)))=r L i+r L j:=by
 rw[((L.map (row i)).prodEquiv _).finrank_eq,Module.finrank_prod]
lemma xQ {L:Submodule ℂ aC} (hL:aD L) (s:aX L=7)
  {a b:Fin 5} (hab:a≠b) (hfix:∀t∈L,∀i,t (i,a)=t (i,b))
  {i j:Fin 4} (B:i≠j):p L i j≤5:=by
 classical
 let A:=L.map (row i)
 let B':=L.map (row j)
 let P:=L.map ((row i).prod (row j))
 have d:=aAq L i j;obtain⟨f,v,H,O,C⟩:=qT hL hab hfix i;obtain⟨g,w,J,Q,E⟩:=qT hL hab hfix j;have q:=aCw L i j;by_contra! k;change 6≤Module.finrank ℂ P at k;have jF:=Submodule.finrank_mono d;rw[q] at jF;change Module.finrank ℂ P≤ r L i+r L j at jF;have o:P=A.prod B':=Submodule.eq_of_le_of_finrank_le d (by rw[q];omega);obtain⟨x,y,M,N,F,G,h⟩:=aDg f g a b
  (aGk hL s hab hfix i f v H) (aGk hL s hab hfix j g w J)
 have l:(x-1,y-1)∈P:=by rw[o];exact⟨C (by omega) x F M,E (by omega) y G N⟩
 obtain⟨t,K,u⟩:=l;have m (c):(1+t) (i,c)=x c:=by have e:t (i,c)=x c-1:=congrFun (congrArg Prod.fst u) c;change 1+t (i,c)=x c;rw[e];ring
 have n (c):(1+t) (j,c)=y c:=by have e:t (j,c)=y c-1:=congrFun (congrArg Prod.snd u) c;change 1+t (j,c)=y c;rw[e];ring
 have z:=cD (1+t) i j B (by simpa only[m,n] using h);rw[hL t K] at z;norm_num at z
abbrev K1 (L:Submodule ℂ aC) (i:Fin 4):=L⊓LinearMap.ker (row i)
abbrev K2 (L:Submodule ℂ aC) (i j:Fin 4):=L⊓LinearMap.ker ((row i).prod (row j))
lemma vT {E:Type*} [AddCommGroup E] [Module ℂ E] (f:aC→ₗ[ℂ] E)
  (L:Submodule ℂ aC):Module.finrank ℂ (L.map f)+aX (L⊓LinearMap.ker f)=aX L:=by
 exact nK f L
lemma aEs {L:Submodule ℂ aC} {x:aC} {i j:Fin 4}:
  x∈K2 L i j↔x∈L∧row i x=0∧row j x=0:=by
 change(_∧((row i x,row j x):aH×aH)=(0,0))↔_;simp only[Prod.mk.injEq];rfl
lemma bP (L:Submodule ℂ aC) (i j:Fin 4):p L i j=p L j i:=by
 have e:K2 L i j=K2 L j i:=by ext x;simp only[aEs];tauto
 have a:p L i j+aX (K2 L i j)=aX L:=vT _ L;have b:p L j i+aX (K2 L j i)=aX L:=vT _ L;rw[e] at a;omega
lemma aF2 (L:Submodule ℂ aC) (i j:Fin 4):p L i j≤ r L i+r L j:=by exact(Submodule.finrank_mono (aAq L i j)).trans_eq (aCw L i j)
lemma aBu (L:Submodule ℂ aC) (o:aX L=7)
  {i j k l:Fin 4} (y:i≠j) (A:i≠k) (f:i≠l)
  (B:j≠k) (v:j≠l) (w:k≠l):
  7+r L i≤p L i j+p L i k+u L l:=by
 have n:∀q:Fin 4,q=i∨q=j∨q=k∨q=l:=by
  revert i j k l
  decide
 have t:K2 L i j⊓K2 L i k=aZ L l:=by
  ext z;change(z∈K2 L i j∧z∈K2 L i k)↔z∈aZ L l;rw[aEs,aEs];change _↔z∈L∧z∈ ⨅ r:{r:Fin 4//r≠l},LinearMap.ker (row r.val);rw[Submodule.mem_iInf];constructor
  ·intro⟨⟨h,C,E⟩,_,_,F⟩;refine⟨h,fun⟨q,G⟩=> ?_⟩;change row q z=0;rcases n q with rfl|rfl|rfl|rfl<;>tauto
  ·intro⟨h,d⟩;exact⟨⟨h,d ⟨i,f⟩,d ⟨j,v⟩⟩,h,d ⟨i,f⟩,d ⟨k,w⟩⟩
 have g (m:Fin 4):K2 L i m≤K1 L i:=fun _ x=>⟨(aEs.mp x).1,(aEs.mp x).2.1⟩
 have s:=Submodule.finrank_mono (sup_le (g j) (g k));have e:=Submodule.finrank_sup_add_finrank_inf_eq (K2 L i j) (K2 L i k);rw[t] at e;have a:p L i j+aX (K2 L i j)=7:=(vT _ L).trans o;have b:p L i k+aX (K2 L i k)=7:=(vT _ L).trans o;have c:r L i+aX (K1 L i)=7:=(vT _ L).trans o;change aX _+u L l=aX _+aX _ at e;change aX _≤aX _ at s;omega
abbrev lQ (i j k l:Fin 4):=i≠j∧i≠k∧i≠l∧j≠k∧j≠l∧k≠l
set_option maxHeartbeats 4000000 in
lemma aBv (r u:Fin 4→ℕ) (p:Fin 4→Fin 4→ℕ)
  (d:∑i,u i≤3) (b:∀i,r i≤3) (c:∀i j,p i j=p j i)
  (dL:∀i j k l,i<j→lQ i j k l→
    p
     i j≤5∧p i j≤ r i+r j∧(p i j≤4∨u k=2∨u l=2∨
     r i=3∧r j=3∧i=0∧j=1))
  (a:∀i j k l,lQ i j k l→7+r i≤p i j+p i k+u l):False:=by
 simp(config:={decide:=true}) [Fin.forall_fin_succ,Fin.sum_univ_four,lQ,c] at b dL a d;by_cases e:u 0=2<;>by_cases f:u 1=2<;>by_cases g:u 2=2<;>by_cases h:u 3=2<;>omega
def dif (r s:Fin 4) (i:Fin 4):ℂ:=(if i=r then 1 else 0)-(if i=s then 1 else 0)
def zB (a b:Fin 5) (r s:Fin 4):aC:=fun p=>(if p.2=a then dif r s p.1 else 0)+(if p.2=b then dif r s p.1 else 0)
lemma aEt (a b:Fin 5) (r s:Fin 4) (F:aC):
  kK (zB a b r s) F=(F (r,a)+F (r,b))-(F (s,a)+F (s,b)):=by
 simp[kK,zB,dif,sub_mul,add_mul,ite_mul,Finset.sum_add_distrib,Finset.sum_sub_distrib];ring
lemma aG8 {a b:Fin 5} (hab:a≠b) (i j k l:Fin 4):
  gr (zB a b i j) (zB a b k l)=dif k l i-dif k l j:=by
 rw[gr,aEt];simp[bQ,gR,zB,Finset.sum_add_distrib,hab,hab.symm];ring
abbrev sZ (L:Submodule ℂ aC) (a:Fin 5) (r s:Fin 4):=∀x∈L,x (r,a)=x (s,a)
lemma aEu {L:Submodule ℂ aC} (hL:aD L) (o:aX L=7)
  {a b:Fin 5} (hab:a≠b) (hfix:∀t∈L,∀i,t (i,a)=t (i,b))
  {i j k l:Fin 4} (e:i≠j) (f:k≠l)
  (m:sZ L a i j) (n:sZ L a k l):
  (i=k∧j=l)∨(i=l∧j=k):=by
 have d {r s} (q:sZ L a r s) (t:aC) (g:t∈L):
   kK (zB a b r s) t=0:=by
  simp only[aEt,←hfix t g,q t g,sub_self]
 have c (r s i:Fin 4):zB a b r s (i,a)=zB a b r s (i,b):=by simp[zB,hab,hab.symm]
 have⟨u,p⟩:=gM hL;have h:=(aAn L a b hab hfix u p o _ _ (c i j) (c k l) (d m) (d n)).1;simp only[aG8 hab] at h;simp only[dif,ite_eq_left rfl,ite_eq_right e,ite_eq_right f,ite_eq_right e.symm,ite_eq_right f.symm,ite_true] at h
 split_ifs at h<;>norm_num at h<;>tauto
abbrev aEv:=∀{L:Submodule ℂ aC},aD L→aX L=7→∀{a b:Fin 5},a≠b→
 (∀t∈L,∀i,t (i,a)=t (i,b))→∀{i j k l:Fin 4},
 i≠j→i≠k→i≠l→j≠k→j≠l→k≠l→p L i j=5→
 u L k=2∨u L l=2∨(r L i=3∧r L j=3∧sZ L a i j)
abbrev aDh:=∀{L:Submodule ℂ aC},aD L→aX L=7→∀{a b:Fin 5},a≠b→(∀t∈L,∀i,t (i,a)=t (i,b))→∑i,u L i≤3
lemma aEw (xZ:aEv) (pure:aDh):eI:=by
 classical
 rintro L hL c ⟨a,b,hab,hfix⟩;have F {i j:Fin 4} (ne:i≠j):p L i j≤5:=xQ hL c hab hfix ne;obtain⟨ρ,g⟩:∃ρ:Equiv.Perm (Fin 4),∀i j,i<j→
   sZ L a (ρ i) (ρ j)→i=0∧j=1:=by
  by_cases A:∃i j,i≠j∧sZ L a i j
  ·obtain⟨i,j,f,C⟩:=A;obtain⟨ρ,v,w⟩:=aAo (0:Fin 4) 1 i j (by decide) f;refine⟨ρ,?_⟩;intro k l x g;have z:ρ k≠ρ l:=ρ.injective.ne x.ne;rcases aEu hL c hab hfix f z C g with⟨h,s⟩|⟨h,s⟩
   ·exact⟨ρ.injective (h.symm.trans v.symm),ρ.injective (s.symm.trans w.symm)⟩
   ·have G:=ρ.injective (h.symm.trans v.symm);have e1:=ρ.injective (s.symm.trans w.symm);omega
  ·exact⟨Equiv.refl _,fun i j y h=>False.elim (A ⟨i,j,y.ne,h⟩)⟩
 have d {i j:Fin 4} (E:i≠j):ρ i≠ρ j:=ρ.injective.ne E;apply aBv (fun i=>r L (ρ i)) (fun i=>u L (ρ i)) (fun i j=>p L (ρ i) (ρ j))
 ·rw[Equiv.sum_comp ρ (u L)];exact pure hL c hab hfix
 ·exact fun i=>zA hL hab hfix _
 ·exact fun i j=>bP _ _ _
 ·rintro i j k l ord ⟨e,m,n,o,q,t⟩;have B:=F (d e);refine⟨B,aF2 _ _ _,?_⟩;by_cases H:p L (ρ i) (ρ j)=5
  ·have:=xZ hL c hab hfix (d e) (d m) (d n) (d o) (d q) (d t) H;specialize g i j ord;tauto
  ·exact Or.inl (by omega)
 ·rintro i j k l ⟨e,m,n,o,q,t⟩;exact aBu L c (d e) (d m) (d n) (d o) (d q) (d t)
end Ac.Ad
namespace Ac.Ad.Bd
open Aa Finset Module ComplexOrder LinearMap Submodule
abbrev P (m:Fin 4):aH→ₗ[ℂ] aC:=(LinearEquiv.curry ℂ ℂ (Fin 4) (Fin 5)).symm.toLinearMap∘ₗ single ℂ (fun _=>aH) m
abbrev V (L:Submodule ℂ aC) (m:Fin 4):Submodule ℂ aH:=L.comap (P m)
lemma Pap (m:Fin 4) (x:aH):P m x=fun p=>if p.1=m then x p.2 else 0:=by ext ⟨r,c⟩;by_cases h:r=m<;>simp[Function.uncurry,h]
variable {L : Submodule ℂ aC} (hL : aD L) {a b : Fin 5} (hab : a ≠ b)
 (hfix : ∀ t ∈ L, ∀ i, t (i,a) = t (i,b))
lemma le (m:Fin 4):u L m≤finrank ℂ (V L m):=by
 refine le_trans (finrank_mono ?_) (finrank_map_le (P m) (V L m));intro t a;have e:P m (row m t)=t:=by
  rw[Pap];ext ⟨r,c⟩;by_cases h:r=m
  ·subst h;simp[row]
  ·simpa[h] using(congrFun ((mem_iInf _).1 a.2 ⟨r,h⟩) c).symm
 exact⟨row m t,show P m (row m t)∈L from e.symm▸a.1,e⟩
include hL
lemma J (v:Fin 4→aH) (a:∀m,v m∈V L m):
  (∀m,∑c,v m c=0)∧
  v 0 ⬝ᵥ v 1+v 0 ⬝ᵥ v 2+v 0 ⬝ᵥ v 3+v 1 ⬝ᵥ v 2+v 1 ⬝ᵥ v 3+v 2 ⬝ᵥ v 3=0∧
  ∑c,(v 0 c*v 1 c*v 2 c+v 0 c*v 1 c*v 3 c+v 0 c*v 2 c*v 3 c+v 1 c*v 2 c*v 3 c)=0∧
  6*∑c,v 0 c*v 1 c*v 2 c*v 3 c=v 0 ⬝ᵥ v 1*(v 2 ⬝ᵥ v 3)+v 0 ⬝ᵥ v 2*(v 1 ⬝ᵥ v 3)+v 0 ⬝ᵥ v 3*(v 1 ⬝ᵥ v 2):=by
 have c:∀m,∑c,v m c=0:=fun m=>by simpa[cW,Pap,sum_comm (γ:=Fin 4)] using(cT hL (a m)).1
 have b:(fun p:Fin 4×Fin 5=>v p.1 p.2)∈L:=by
  convert L.sum_mem fun m (_:m∈univ)=>a m using 1
  ext p;simp[Pap]
 have e:∀m,v m 4= -(v m 0+v m 1+v m 2+v m 3):=fun m=>by have:=c m;rw[Fin.sum_univ_five] at this;linear_combination this
 obtain⟨-,h2,h3,h4⟩:=cT hL b;simp+decide only[pQ,pR,yW,Fin.sum_univ_five,Fin.sum_univ_four,ite_true,ite_false,add_zero,zero_add,e] at h2 h3 h4;refine⟨c,?_,?_,?_⟩<;>simp only[dotProduct,Fin.sum_univ_five,e]
 ·linear_combination-h2
 ·linear_combination h3/2
 ·linear_combination-h4
lemma aHa {i j:Fin 4} (h:i≠j) {x y:aH}
  (c:x∈V L i) (d:y∈V L j):x ⬝ᵥ y=0:=by
 have:=(J hL (fun n=>if n=i then x else if n=j then y else 0) (by intro n;split_ifs with a b;exacts [a▸c,b▸d,zero_mem _])).2.1;fin_cases i<;>fin_cases j<;>simp[dotProduct_comm] at h this ⊢ <;>exact this
lemma cub {i j k:Fin 4} (f:i≠j) (g:i≠k) (h:j≠k)
  {x y z:aH} (d:x∈V L i) (e:y∈V L j) (l:z∈V L k):∑c,x c*y c*z c=0:=by
 have:=(J hL (fun n=>if n=i then x else if n=j then y else if n=k then z else 0) (by intro n;split_ifs with a b c;exacts [a▸d,b▸e,c▸l,zero_mem _])).2.2.1;fin_cases i<;>fin_cases j<;>fin_cases k<;>simp[mul_comm,mul_left_comm] at f g h this ⊢ <;>exact this
abbrev dv (a b:Fin 5):aH:=Pi.single a 1-Pi.single b 1
abbrev Hq (a b:Fin 5) (q w:aH):Prop:=1 ⬝ᵥ w=0∧dv a b ⬝ᵥ w=0∧q ⬝ᵥ w=0
omit hL in
lemma alg {q:aH} {c:ℂ} (h:q*q=c•q) (a:(1:aH) ⬝ᵥ q=0):q=0:=by
 rw[←dotProduct_star_self_eq_zero];have e:star q ⬝ᵥ q=star c*((1:aH) ⬝ᵥ q):=by
  simp only[dotProduct,mul_sum];refine sum_congr rfl fun j _=> ?_
  rcases mul_eq_mul_right_iff.1 (show q j*q j=c*q j from congrFun h j) with r|r<;>simp[r]
 rw[e,a,mul_zero]
omit hL in
include hab in
lemma xR {q x y:aH} (p:q≠0) (f:Hq a b q q)
  (h:Hq a b q x) (u:Hq a b q y) (v:x ⬝ᵥ y=0):
  (∃c:ℂ,x=c•q)∨∃c:ℂ,y=c•q:=by
 by_contra l;push Not at l
 let A:Matrix (Fin 4) (Fin 5) ℂ:= ![1,dv a b,q,x]
 have z:LinearIndependent ℂ A.row:=by
  rw[Fintype.linearIndependent_iff];intro g B;have e:g 0•(1:aH)+g 1•dv a b+g 2•q+g 3•x=0:=by simpa[Fin.sum_univ_four,A,Matrix.row] using B
  have n:g 0=0:=by simpa[f.1,h.1,dotProduct_sub,hab] using congrArg ((1:aH) ⬝ᵥ ·) e
  have t:g 1=0:=by simpa[f.2.1,h.2.1,dotProduct_sub,sub_dotProduct,hab,hab.symm,n] using congrArg (dv a b ⬝ᵥ ·) e
  have E:g 3=0:=by by_contra k;refine l.1 (-g 2/g 3) ?_;ext j;have:=congrFun e j;simp[n,t] at this;simp;field_simp;linear_combination this
  have F:g 2=0:=by simpa[n,t,E,p] using e
  intro i;fin_cases i<;>assumption
 have C:finrank ℂ (ker A.mulVecLin)=1:=by have:=finrank_range_add_finrank_ker A.mulVecLin;have r:=z.rank_matrix;simp[Matrix.rank] at r this;omega
 have d:∀w,Hq a b q w→x ⬝ᵥ w=0→w∈ker A.mulVecLin:=by intro w m s;refine mem_ker.2 (funext fun i=> ?_);change A i ⬝ᵥ w=0;fin_cases i<;>simp[A,m.1,m.2.1,m.2.2,s]
 obtain⟨c,o⟩:=(finrank_eq_one_iff_of_ne_zero' (⟨q,d q f (dotProduct_comm q x▸h.2.2)⟩:ker A.mulVecLin) (by simpa using p)).1 C ⟨y,d y u v⟩;exact l.2 c (congrArg Subtype.val o).symm
include hfix
lemma aEx {m:Fin 4} {x:aH} (c:x∈V L m):(1:aH) ⬝ᵥ x=0∧dv a b ⬝ᵥ x=0:=by have:=hfix _ c m;simp[Pap] at this;exact⟨by simpa[dotProduct,cW,Pap,sum_comm (γ:=Fin 4)] using(cT hL c).1,by simp[sub_dotProduct,this]⟩
include hab
lemma aHb (v:∀m,V L m) (s t:ℂ) (h:∑m,(v m:aH)+s•1+t•dv a b=0):
  s=0∧t=0∧∀m n,∀y∈V L n,(v m:aH) ⬝ᵥ y=0:=by
 have B:=fun m=>aEx hL hfix (v m).2
 have c:s=0:=by simpa[dotProduct_sum,fun m=>(B m).1,dotProduct_sub] using congrArg ((1:aH) ⬝ᵥ ·) h
 have f:t=0:=by simpa[dotProduct_sum,fun m=>(B m).2,dotProduct_sub,sub_dotProduct,hab,hab.symm,c] using congrArg (dv a b ⬝ᵥ ·) h
 refine⟨c,f,fun m n y d=> ?_⟩;by_cases e:m=n
 ·subst e;have:=congrArg (· ⬝ᵥ y) h;simp only[c,f,zero_smul,add_zero,sum_dotProduct,zero_dotProduct] at this;rwa [sum_eq_single m (fun j _ g=>aHa hL g (v j).2 d) (by simp)] at this
 ·exact aHa hL e (v m).2 d
abbrev F (L:Submodule ℂ aC) (a b:Fin 5):((∀m,V L m)× ℂ× ℂ)→ₗ[ℂ] aH:=
 (lsum ℂ (fun m=>V L m) ℂ fun m=>(V L m).subtype).coprod
  ((toSpanSingleton ℂ aH 1).coprod (toSpanSingleton ℂ aH (dv a b)))
lemma aAr (h4:4≤∑m,finrank ℂ (V L m)):False:=by
 have X:=finrank_pi_fintype ℂ (M:=fun m:Fin 4=>V L m);obtain⟨⟨v,s,t⟩,S,z⟩:=exists_mem_ne_zero_of_ne_bot ((F L a b).ker_ne_bot_of_finrank_lt (by rw[finrank_prod,X];simp;omega));obtain⟨rfl,rfl,R⟩:=aHb hL hab hfix v s t (by simpa[add_assoc] using S);obtain⟨d,a0⟩:=Function.ne_iff.1 (fun h:v=0=>z (by simp[h]));obtain⟨q,f,l,O⟩:∃q:aH,q≠0∧q∈V L d∧∀n,∀y∈V L n,q ⬝ᵥ y=0:=⟨v d,by simpa using a0,(v d).2,R d⟩
 have HQ:∀n,∀x∈V L n,Hq a b q x:=fun n x e=>and_assoc.1 ⟨aEx hL hfix e,O n x e⟩
 have Hqq:=HQ d q l;obtain⟨A,G⟩:∃A,q A≠0:=Function.ne_iff.1 f;obtain⟨⟨⟨v,s,t⟩,r⟩,S,z⟩:=exists_mem_ne_zero_of_ne_bot
  ((((F L a b).coprod (toSpanSingleton ℂ aH (Pi.single A 1))).prod
   (proj A∘ₗ (V L d).subtype∘ₗ proj d∘ₗ fst ℂ _ _∘ₗ
    fst ℂ _ _)).ker_ne_bot_of_finrank_lt
   (by rw[finrank_prod,finrank_prod,finrank_prod,X];simp;omega))
 obtain⟨g,o⟩:=Prod.ext_iff.1 S;simp at g o;have hr:r=0:=by simpa[dotProduct_add,dotProduct_sum,fun m=>O m _ (v m).2,dotProduct_comm q 1,Hqq.1,dotProduct_comm q (dv a b),Hqq.2.1,G] using congrArg (q ⬝ᵥ ·) g
 subst hr;obtain⟨rfl,rfl,R⟩:=aHb hL hab hfix v s t (by simpa[add_assoc] using g);have hv:∀m,∃c:ℂ,(v m:aH)=c•q:=fun m=>(xR hab f Hqq (HQ m _ (v m).2) (HQ m _ (v m).2) (R m m _ (v m).2)).elim id id
 have P:∀m,(v m:aH)≠0→q∈V L m:=fun m hm=>by
  obtain⟨c,B⟩:=hv m;have:c≠0:=fun h=>hm (by simp[B,h])
  exact((V L m).smul_mem_iff this).1 (B▸(v m).2)
 have v0:(v d:aH)=0:=by obtain⟨c,B⟩:=hv d;rw[B] at o ⊢;simp[G] at o;simp[o]
 obtain⟨j,hj⟩:=Function.ne_iff.1 (fun h:v=0=>z (by simp[h]));have u:(v j:aH)≠0:=by simpa using hj
 obtain⟨k,w,E⟩:∃k,k≠j∧(v k:aH)≠0:=by by_contra Z;push Not at Z;rw[sum_eq_single j (fun k _ E=>Z k E) (by simp)] at g;exact u (by simpa using g)
 have H:j≠d:=fun h=>u (h▸v0)
 have N:k≠d:=fun h=>E (h▸v0)
 have qj:=P j u;have qk:=P k E;have C:∀m,∀x∈V L m,∑c,x c*q c*q c=0:=fun m x e=>by
  by_cases p:m=j
  ·exact cub hL (p▸H) (p▸w.symm) N.symm e l qk
  by_cases Q:m=k
  ·exact cub hL (Q▸N) (Q▸w) H.symm e l qj
  ·exact cub hL p Q w.symm e qj qk
 have U:q a=q b:=by have:=Hqq.2.1;simp[sub_dotProduct] at this;linear_combination this
 have Q2:Hq a b q (q*q):=⟨by simpa[dotProduct] using Hqq.2.2,by simp[sub_dotProduct,U],by simpa[dotProduct,mul_assoc] using C d q l⟩
 have T:∀m,∀x∈V L m,∃c:ℂ,x=c•q:=fun m x e=>
  (xR hab f Hqq (HQ m x e) Q2 (by simpa[dotProduct,mul_assoc] using C m x e)).resolve_right
   fun⟨c,h⟩=>f (alg h Hqq.1)
 have TS:∀m,V L m≤ℂ ∙ q:=fun m x e=>by obtain⟨c,rfl⟩:=T m x e;exact smul_mem _ _ (mem_span_singleton_self q)
 have b1:∀m,finrank ℂ (V L m)≤1:=fun m=>finrank_span_singleton (K:=ℂ) f▸finrank_mono (TS m)
 have all:∀m,q∈V L m:=fun m=>by
  have h0:=add_sum_erase univ (fun i=>finrank ℂ (V L i)) (mem_univ m);have p:=sum_le_card_nsmul (univ.erase m) (fun i=>finrank ℂ (V L i)) 1 fun i _=>b1 i
  simp at p;exact eq_of_le_of_finrank_le (TS m) (by rw[finrank_span_singleton f];omega)▸
   mem_span_singleton_self q
 have q4:=(J hL (fun _=>q) all).2.2.2;simp only[Hqq.2.2,mul_zero,add_zero] at q4;rcases xR hab f Hqq Q2 Q2 (by simpa[dotProduct,mul_assoc] using q4) with⟨c,h⟩|⟨c,h⟩<;>exact f (alg h Hqq.1)
end Ac.Ad.Bd
namespace Ac.Ad
open Aa
lemma vU {L:Submodule ℂ aC} (hL:aD L) (c:aX L=7)
  {a b:Fin 5} (hab:a≠b) (hfix:∀t∈L,∀i,t (i,a)=t (i,b)):
  ∑i,u L i≤3:=by
 by_contra h;exact Bd.aAr hL hab hfix (le_trans (by omega) (Finset.sum_le_sum fun m _=>Bd.le m))
end Ac.Ad
namespace Ac.Ad.Bf
open Aa Finset
open scoped Matrix
abbrev V4:=Fin 4→ℂ
abbrev aHc:=Matrix (Fin 4) (Fin 4) ℂ
lemma xS (a b:V4)
  (h:∀i j,i≠j→a i*b j+b i*a j=0) (q:a 0*b 0=0):
  (∀i,a i=0)∨(∀i,b i=0)∨
    (a 0=0∧b 0=0∧∃i j:Fin 4,i≠j∧∀k,k≠i→k≠j→a k=0∧b k=0):=by
 have e (x y:V4) (u:∀i j,i≠j→x i*y j+y i*x j=0)
   {i} (hx:x i≠0) (hy:y i=0) (k:Fin 4):y k=0:=
  if l:k=i then l▸hy
  else(mul_eq_zero.mp (by simpa[hy] using u i k (Ne.symm l))).resolve_left hx
 by_cases f:a 0≠0
 ·exact Or.inr (Or.inl (e a b h f ((mul_eq_zero.mp q).resolve_left f)))
 by_cases g:b 0≠0
 ·exact Or.inl (e b a (fun i j s=>by linear_combination h i j s) g ((mul_eq_zero.mp q).resolve_right g))
 push Not at f g
 by_cases p:∀i,a i=0
 ·exact Or.inl p
 push Not at p;obtain⟨i,n⟩:=p
 by_cases o:b i=0
 ·exact Or.inr (Or.inl (e a b h n o))
 have⟨j,c,v⟩:∃j,j≠i∧∀k,k≠i→k≠j→a k=0:=by
  by_cases t:∃j,j≠i∧a j≠0
  ·obtain⟨j,c,r⟩:=t;exact⟨j,c,fun k d m=>(mul_eq_zero.mp (by
    linear_combination a k*h i j c.symm+a j*h i k d.symm-a i*h j k m.symm:
    (2*b i*a j)*a k=0)).resolve_left (mul_ne_zero (mul_ne_zero (by norm_num) o) r)⟩
  ·obtain⟨j,c⟩:=exists_ne i;exact⟨j,c,fun k d _=>by by_contra w;exact t ⟨k,d,w⟩⟩
 exact Or.inr (Or.inr ⟨f,g,i,j,c.symm,fun k d m=>
  have l:=v k d m
  ⟨l,(mul_eq_zero.mp (by simpa[l] using h i k d.symm)).resolve_left n⟩⟩)
lemma tB {U:Type*} [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
  (a b:Fin 4→Module.Dual ℂ U)
  (K:∀x:U,(∀k,a k x=0)→(∀k,b k x=0)→x=0)
  (w:∀x:U,∑k,(a k x+b k x)+(a 0 x+b 0 x)=0)
  (d:∀x:U,∀i j:Fin 4,i≠j→a i x*b j x+b i x*a j x=0)
  (p:∀x:U,a 0 x*b 0 x=0)
  (hd:2≤Module.finrank ℂ U):(∀i,a i=0)∨(∀i,b i=0):=by
 classical
 let f:=Sum.elim a b
 obtain⟨t,S⟩:=Module.Dual.exists_forall_ne_zero_of_forall_exists
  (fun i:{i//f i≠0}=>f i.val) fun i=>by by_contra! h;exact i.2 (LinearMap.ext h)
 have det (i) (hi:f i t=0):f i=0:=by by_contra hn;exact S ⟨i,hn⟩ hi
 rcases xS (fun i=>a i t) (fun i=>b i t) (d t) (p t) with ha|hb|⟨ha0,hb0,i,j,hij,ho⟩
 ·exact Or.inl fun i=>det (.inl i) (ha i)
 ·exact Or.inr fun i=>det (.inr i) (hb i)
 exfalso;have G:a 0=0:=det (.inl 0) ha0;have H:b 0=0:=det (.inr 0) hb0;have n (k) (y:k≠i) (z:k≠j):a k=0∧b k=0:=⟨det (.inl k) (ho k y z).1,det (.inr k) (ho k y z).2⟩
 let A:=a i;let B:=a j;let C:=b i;let D:=b j
 have O (x:U):A x+B x+C x+D x=0:=by
  have M:=w x;rw[G,H] at M;have e:∑k∈({i,j}:Finset (Fin 4)),(a k x+b k x)=∑k,(a k x+b k x):=sum_subset (subset_univ _) fun k _ r=>by simp only[mem_insert,mem_singleton,not_or] at r;simp[(n k r.1 r.2).1,(n k r.1 r.2).2]
  rw[sum_pair hij] at e;linear_combination e.trans (by simpa using M)
 have o (x:U) (X:A x=0) (E:B x=0) (F:C x=0) (Z:D x=0):x=0:=
  K x
    (fun k=>if g:k=i then g▸X else if l:k=j then l▸E else by rw[(n k g l).1];rfl)
    (fun k=>if g:k=i then g▸F else if l:k=j then l▸Z else by rw[(n k g l).2];rfl)
 obtain⟨⟨u,Q⟩,P⟩:=Module.finrank_pos_iff_exists_ne_zero.mp (by
  have:=LinearMap.finrank_range_add_finrank_ker A;have:Module.finrank ℂ (LinearMap.range A)≤1:=by simpa using Submodule.finrank_le (LinearMap.range A)
  omega:0<Module.finrank ℂ (LinearMap.ker A))
 have c:A u=0:= Q;have s (B' C':Module.Dual ℂ U)
   (hS:∀x,A x+B' x+C' x+D x=0) (hM:∀x,A x*D x+C' x*B' x=0)
   (hI:∀x,A x=0→B' x=0→C' x=0→D x=0→x=0) (hBu:B' u=0):False:=by
  have N:C' u≠0:=fun h=>P (Subtype.ext (hI u c hBu h (by linear_combination hS u-c-hBu-h)))
  have q (v:U):B' v=A v:=by have e:=hM (u+v);simp only[map_add] at e;exact sub_eq_zero.mp ((mul_eq_zero.mp (by linear_combination e-hM v-(D u+D v)*c-(C' u+C' v)*hBu-A v*(hS u-c-hBu):C' u*(B' v-A v)=0)).resolve_left N)
  have m (v:U):A v=0:=sq_eq_zero_iff.mp ((mul_eq_zero.mp (by linear_combination hM v-A v*hS v+(A v-C' v)*q v: -2*(A v)^2=0)).resolve_left (by norm_num));have:=LinearMap.finrank_le_finrank_of_injective ((injective_iff_map_eq_zero C').mpr fun v R=>hI v (m v) ((q v).trans (m v)) R (by linear_combination hS v-m v-(q v).trans (m v)-R));simp at this;omega
 have J:∀x,A x*D x+C x*B x=0:=fun x=>d x i j hij
 rcases mul_eq_zero.mp (by linear_combination J u-D u*c:C u*B u=0) with F|E
 ·exact s C B (fun x=>by linear_combination O x) (fun x=>by linear_combination J x) (fun x g l T V=>o x g T l V) F
 ·exact s B C O J o E
lemma qU (u v p q:V4)
  (n:u ⬝ᵥ 1=1) (o:v ⬝ᵥ 1=1) (E:p ⬝ᵥ 1=0) (G:q ⬝ᵥ 1=0)
  (F:∃k,p k≠0)
  (m:∀j,j≠0→u j*q j-p j*v j=0)
  (c:∀i j,u i*q j-p i*v j=u j*q i-p j*v i):
  (∃j,j≠0∧u j=v j∧u j≠0∧p j=0∧q j=0)∨
  ((∃k,q k≠0)∧∀x y:V4,u ⬝ᵥ x=v ⬝ᵥ y→p ⬝ᵥ x=q ⬝ᵥ y→x 0=y 0):=by
 classical
 have a (i:Fin 4):q i= -p i:=by
  have h:=sum_congr (s₁:=(univ:Finset (Fin 4))) rfl fun j _=>c i j
  simp only[dotProduct,Pi.one_apply,mul_one] at n o E G;simpa[sum_sub_distrib,←mul_sum,←sum_mul,n,o,E,G] using h.symm
 obtain⟨k,C⟩:=F;by_cases g:∃j,j≠0∧u j+v j≠0
 ·obtain⟨j,t,b⟩:=g;have d:=m j t;rw[a j] at d;have l:=(mul_eq_zero.mp (by linear_combination-d:p j*(u j+v j)=0)).resolve_right b;have H:q j=0:=by simp[a,l]
  have s:=c j k;rw[l,H,a k] at s;have B:=sub_eq_zero.mp ((mul_eq_zero.mp (by linear_combination-s:(u j-v j)*p k=0)).resolve_right C);exact Or.inl ⟨j,t,B,fun J=>b (by simp[←B,J]),l,H⟩
 ·push Not at g
  refine Or.inr ⟨⟨k,by rw[a k];exact neg_ne_zero.mpr C⟩,fun x y H1 H2=> ?_⟩
  let δ:=(u k-v k)/p k
  have hδ (i:Fin 4):u i-v i=δ*p i:=by have s:=c i k;rw[a k,a i] at s;dsimp[δ];field_simp;linear_combination-s
  have A (j:Fin 4):u j+v j=if j=0 then 2 else 0:=by
   by_cases b:j=0
   ·subst b;rw[ite_eq_left rfl];have e:∑j,(u j+v j)=2:=by
     simp only[dotProduct,Pi.one_apply,mul_one] at n o;rw[sum_add_distrib,n,o];norm_num
    rwa [sum_eq_single (0:Fin 4) (fun j _ b=>g j b) (by simp)] at e
   ·rw[ite_eq_right b];exact g j b
  have f (w r z:V4) (hw:∀j,2*w j=(if j=0 then 2 else 0)+δ*r j):
    2*(w ⬝ᵥ z)=2*z 0+δ*(r ⬝ᵥ z):=by
   simp only[dotProduct,mul_sum];simp_rw[←mul_assoc,hw,add_mul,mul_assoc];simp[sum_add_distrib,ite_mul,zero_mul]
  have K:=f u p x fun j=>by linear_combination A j+hδ j
  have M:=f v q y fun j=>by linear_combination A j-hδ j-δ*a j
  linear_combination(M-K+2*H1-δ*H2)/2
lemma jK (u p:V4) (e:u ⬝ᵥ 1=1) (d:p ⬝ᵥ 1=0)
  (c:∃k,p k≠0):∃a,u ⬝ᵥ a=0∧p ⬝ᵥ a=1:=by
 obtain⟨k,b⟩:=c;exact⟨(p k)⁻¹ •(Pi.single k 1+(-u k)•1),by simp[e],by simp[d,b]⟩
lemma mJ (Z:aHc) (u v p q:V4)
  (t:u ⬝ᵥ 1=1) (w:v ⬝ᵥ 1=1) (F:p ⬝ᵥ 1=0) (H:q ⬝ᵥ 1=0)
  (K:∀i j,Z i j=Z j i) (N:∀j,j≠0→Z j j=0)
  (s:∀x y:V4,u ⬝ᵥ x=v ⬝ᵥ y→p ⬝ᵥ x=q ⬝ᵥ y→x ⬝ᵥ (Z*ᵥ y)=0):
  (∀i j,Z i j=0)∨((∃k,p k≠0)∧
    ∃c:ℂ,c≠0∧∀i j,Z i j=c*(u i*q j-p i*v j)):=by
 classical
 let e (i:Fin 4):V4:=Pi.single i 1
 have R (i j:Fin 4):e i ⬝ᵥ (Z*ᵥ e j)=Z i j:=by simp[e]
 let P (o r n d:V4):=∀x y:V4,o ⬝ᵥ x=r ⬝ᵥ y→n ⬝ᵥ x=d ⬝ᵥ y→x ⬝ᵥ (Z*ᵥ y)=0
 have bZ {o r n d:V4} (h:P o r n d)
   (x y a b:V4) (l:o ⬝ᵥ x=r ⬝ᵥ y) (m:n ⬝ᵥ x=d ⬝ᵥ y)
   (h₃:o ⬝ᵥ a=r ⬝ᵥ b) (h₄:n ⬝ᵥ a=d ⬝ᵥ b):
   x ⬝ᵥ (Z*ᵥ b)+a ⬝ᵥ (Z*ᵥ y)=0:=by
  have X:=h (x+a) (y+b) (by simp[l,h₃]) (by simp[m,h₄]);simp[Matrix.mulVec_add,h x y l m,h a b h₃ h₄] at X;linear_combination X
 have O {o r n d:V4} (h:P o r n d)
   (hu':o ⬝ᵥ 1=1) (hv':r ⬝ᵥ 1=1) (hq':d ⬝ᵥ 1=0) (g:∀j,n j=0):
   ∀i j,Z i j=0:=by
  have G (x:V4):n ⬝ᵥ x=0:=by simp[dotProduct,g]
  have z:(1:V4) ⬝ᵥ (Z*ᵥ 1)=0:=h 1 1 (hu'.trans hv'.symm) ((G 1).trans hq'.symm);have E (x y:V4) (hy:d ⬝ᵥ y=0):x ⬝ᵥ (Z*ᵥ y)=0:=by
   simpa[Matrix.mulVec_smul,z] using
    bZ h x ((o ⬝ᵥ x)•1) ((r ⬝ᵥ y)•1) y
     (by simp[hv']) (by simp[G,hq']) (by simp[hu']) (by simp[G,hy])
  by_cases f:∃k,k≠0∧d k≠0
  ·obtain⟨k,a0,Q⟩:=f;have J (i j:Fin 4):d k*Z i j-d j*Z i k=0:=by
    have M:=E (e i) (d k•e j-d j•e k) (by simp[e];ring);rw[Matrix.mulVec_sub,Matrix.mulVec_smul,Matrix.mulVec_smul] at M;simpa[R] using M
   have V (j:Fin 4):Z k j=0:=(mul_eq_zero.mp (by simpa[N k a0] using J k j)).resolve_left Q;exact fun i j=>(mul_eq_zero.mp (by simpa[K i k,V] using J i j)).resolve_left Q
  ·push Not at f
   have a1 (k:Fin 4):d k=0:=if E:k=0 then E▸by
    simp only[dotProduct,Pi.one_apply,mul_one] at hq';rwa [sum_eq_single (0:Fin 4) (fun j _ hj=>f j hj) (by simp)] at hq'
    else f k E
   exact fun i j=>R i j▸E (e i) (e j) (by simp[e,a1])
 by_cases g:∃k,p k≠0
 ·by_cases f:∃k,q k≠0
  ·obtain⟨a,S,A⟩:=jK u p t F g;obtain⟨b,T,B⟩:=jK v q w H f;have z:=s 1 1 (t.trans w.symm) (F.trans H.symm);have hab:=s a b (S.trans T.symm) (A.trans B.symm);have C:=bZ s 1 1 a b (t.trans w.symm) (F.trans H.symm) (S.trans T.symm) (A.trans B.symm);have hf (i j:Fin 4):Z i j=((1:V4) ⬝ᵥ (Z*ᵥ b))*(u i*q j-p i*v j):=by
    have U:=bZ s (e i) (u i•1+p i•b) (v j•1+q j•a) (e j)
     (by simp[e,w,T]) (by simp[e,H,B]) (by simp[e,t,S]) (by simp[e,F,A])
    rw[R,Matrix.mulVec_add,Matrix.mulVec_smul,Matrix.mulVec_smul] at U;simp[z,hab] at U;linear_combination U-(q j*u i)*C
   by_cases M:(1:V4) ⬝ᵥ (Z*ᵥ b)=0
   ·exact Or.inl fun i j=>by simpa[M] using hf i j
   ·exact Or.inr ⟨g,_,M,hf⟩
  ·push Not at f
   have ht:Zᵀ=Z:=Matrix.ext fun i j=>K j i
   exact Or.inl (O (fun x y l m=>by rw[Matrix.dotProduct_mulVec,←ht,Matrix.vecMul_transpose,dotProduct_comm];exact s y x l.symm m.symm) w t F f)
 ·push Not at g
  exact Or.inl (O s t w H g)
def cR (f:Module.Dual ℂ V4):V4:=fun i=>f (Pi.single i 1)
lemma dI (f:Module.Dual ℂ V4) (x:V4):cR f ⬝ᵥ x=f x:=by
 have a:∑i,x i•(Pi.single i 1:V4)=x:=by funext k;simp[Pi.single_apply,mul_ite]
 conv_rhs=>rw[←a,map_sum]
 simp[dotProduct,cR,mul_comm]
lemma dN (W:Submodule ℂ (V4×V4))
  (n:Module.finrank ℂ W=6) (f g:Module.Dual ℂ V4)
  (s:f 1=1) (C:g 1=1) (B:∀w∈W,f w.1=g w.2)
  (A:((1,1):V4×V4)∈W):
  ∃
   p q:V4,p ⬝ᵥ 1=0∧q ⬝ᵥ 1=0∧
   ∀x y:V4,(x,y)∈W↔cR f ⬝ᵥ x=cR g ⬝ᵥ y∧p ⬝ᵥ x=q ⬝ᵥ y:=by
 let d:Module.Dual ℂ (V4×V4):=f.comp (LinearMap.fst ℂ V4 V4)-g.comp (LinearMap.snd ℂ V4 V4)
 have j:Module.finrank ℂ (LinearMap.ker d)=7:=by
  have:=Module.Dual.finrank_ker_add_one_of_ne_zero (show d≠0 from fun h=>by simpa[d,s] using LinearMap.congr_fun h ((1,0):V4×V4));have:Module.finrank ℂ (V4×V4)=8:=by norm_num[V4,Module.finrank_prod]
  omega
 have i:W≤LinearMap.ker d:=fun w a=>LinearMap.mem_ker.mpr (sub_eq_zero.mpr (B w a))
 obtain⟨x,u,v⟩:=IsConcreteLE.exists_of_lt (lt_of_le_of_ne i fun h=>by rw[h,j] at n;omega);obtain⟨H,t,z⟩:=Submodule.exists_dual_map_eq_bot_of_notMem v (inferInstance:Module.Projective ℂ _);have e (w:V4×V4) (a:w∈W):H w=0:=by have E:H w∈W.map H:=⟨w,a,rfl⟩;simpa[z] using E
 have m:W=LinearMap.ker d⊓LinearMap.ker H:=Submodule.eq_of_le_of_finrank_eq
  (fun w a=>⟨i a,e w a⟩) (by
    have:=Submodule.finrank_mono (show W≤LinearMap.ker d⊓LinearMap.ker H from fun w a=>⟨i a,e w a⟩);have:=Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inf_le_left fun h=>t (h.symm▸u:x∈LinearMap.ker d⊓LinearMap.ker H).2);omega)
 let r:=H (1,0)
 let P:=H.comp (LinearMap.inl ℂ V4 V4)-r•f
 let Q:= -H.comp (LinearMap.inr ℂ V4 V4)-r•g
 have b (x y:V4):H (x,0)+H (0,y)=H (x,y):=by rw[←map_add];simp
 refine⟨cR P,cR Q,(dI P 1).trans (by change r-r*f 1=0;rw[s,mul_one,sub_self]),
  (dI Q 1).trans (by change-H (0,1)-r*g 1=0;linear_combination-(b 1 1).trans (e (1,1) A)-r*C),
  fun x y=> ?_⟩
 rw[m,Submodule.mem_inf,LinearMap.mem_ker,LinearMap.mem_ker,dI,dI,dI,dI];have c:P x-Q y=H (x,y)-r*(f x-g y):=by change(H (x,0)-r*f x)-(-H (0,y)-r*g y)=H (x,y)-r*(f x-g y);linear_combination b x y
 constructor<;>rintro⟨l,o⟩
 ·have k:f x=g y:=sub_eq_zero.mp l;exact⟨k,sub_eq_zero.mp (by linear_combination c+o-r*k)⟩
 ·exact⟨sub_eq_zero.mpr l,by linear_combination-c+o+r*l⟩
def F4 (x y z w:aH):ℂ:=∑e:Fin 4 ↪ Fin 5,x (e 0)*y (e 1)*z (e 2)*w (e 3)
lemma aCx (M:aC):aO M=F4 (row 0 M) (row 1 M) (row 2 M) (row 3 M):=by simp[aO,F4,Fin.prod_univ_four,mul_assoc]
lemma aF3 {L:Submodule ℂ aC} (hL:aD L) {m t:aC} (j:m∈L) (d:t∈L)
  (f:row 0 t=0) (i:row 1 t=0) (c:ℂ):
  F4 (c•(1:aH)+row 0 m) (c•(1:aH)+row 1 m) (row 2 t) (row 3 t)=0:=by
 let g (s:ℂ):=F4 ((1:aH)+s•row 0 m) ((1:aH)+s•row 1 m) (row 2 t) (row 3 t)
 have zT (s:ℂ):g s=0:=by
  let a:=s•m;have b:a∈L:=L.smul_mem s j
  have h:2*F4 (row 0 (1+a)) (row 1 (1+a)) (row 2 t) (row 3 t)=
    aO (1+(a+t))+aO (1+(a-t))-2*aO (1+a):=by
   simp only[aCx,F4,←add_assoc,←add_sub_assoc,map_add,map_sub,f,i,Pi.add_apply,Pi.sub_apply,Pi.zero_apply,mul_sum,←sum_add_distrib,←sum_sub_distrib];exact sum_congr rfl fun e _=>by ring
  rw[map_add,map_add,map_smul,map_smul] at h;change 2*g s=_ at h;linear_combination(h+hL _ (L.add_mem b d)+hL _ (L.sub_mem b d)-2*hL _ b)/2
 have h:F4 (c•(1:aH)+row 0 m) (c•(1:aH)+row 1 m) (row 2 t) (row 3 t)=
   (c^2-1)*g 0+(c/2+1/2)*g 1+(1/2-c/2)*g (-1):=by
  simp only[g,F4,mul_sum,←sum_add_distrib,Pi.add_apply,Pi.smul_apply,Pi.one_apply,smul_eq_mul];exact sum_congr rfl fun e _=>by ring
 rw[h,zT 0,zT 1,zT (-1)];ring
def cm:Fin 5→Fin 4:= ![0,0,1,2,3]
abbrev unf:V4→ₗ[ℂ] aH:=LinearMap.funLeft ℂ ℂ cm
abbrev gF:aH→ₗ[ℂ] V4:=LinearMap.funLeft ℂ ℂ Fin.succ
abbrev lC (r:Fin 4):aC→ₗ[ℂ] V4:=gF∘ₗ row r
lemma aEy (x:aH) (h:x 0=x 1):unf (gF x)=x:=by funext c;fin_cases c<;>first | exact h.symm | rfl
def Zf (z w:aH):aHc:=fun i j=>∑e:Fin 4 ↪ Fin 5,if cm (e 0)=i∧cm (e 1)=j then z (e 2)*w (e 3) else 0
lemma aHd (z w:aH) (x y:V4):x ⬝ᵥ (Zf z w*ᵥ y)=F4 (unf x) (unf y) z w:=by
 simp only[dotProduct,Matrix.mulVec,Zf,F4,unf,LinearMap.funLeft_apply,mul_sum,sum_mul]
 trans ∑i,∑e:Fin 4 ↪ Fin 5,∑j,x i*((if cm (e 0)=i∧cm (e 1)=j then z (e 2)*w (e 3) else 0)*y j)
 ·exact sum_congr rfl fun i _=>sum_comm
 rw[sum_comm];refine sum_congr rfl fun e _=> ?_
 have a (i j:Fin 4):x i*((if cm (e 0)=i∧cm (e 1)=j then z (e 2)*w (e 3) else 0)*y j)=
   if cm (e 1)=j then if cm (e 0)=i then x i*y j*z (e 2)*w (e 3) else 0 else 0:=by
  by_cases b:cm (e 0)=i<;>by_cases a:cm (e 1)=j<;>simp[b,a];ring
 rw[sum_congr rfl fun i _=>sum_congr rfl fun j _=>a i j];simp
lemma aCz (z w:aH) (i j:Fin 4):Zf z w i j=Zf z w j i:=by unfold Zf;rw[←(Equiv.embeddingCongr (Equiv.swap (0:Fin 4) 1) (Equiv.refl (Fin 5))).sum_comp];exact sum_congr rfl fun e _=>by simp[Equiv.swap_apply_def,and_comm]
lemma aC0 (z w:aH) (i:Fin 4) (f:i≠0):Zf z w i i=0:=
 sum_eq_zero fun e _=>ite_eq_right fun⟨c,d⟩=>
  (by decide:∀k:Fin 4,k≠0→∀a b:Fin 5,a≠b→cm a=k→cm b=k→False)
   i f (e 0) (e 1) (fun h=>absurd (e.injective h) (by decide)) c d
lemma aGs (a b:V4) (h:∀i j,Zf (unf a) (unf b) i j=0):
  (∀i j:Fin 4,i≠j→a i*b j+b i*a j=0)∧a 0*b 0=0:=by
 classical
 let K (c d e f:Fin 5):=c≠d∧c≠e∧c≠f∧d≠e∧d≠f∧e≠f
 let q:(Fin 5×Fin 5×Fin 5×Fin 5)≃(Fin 4→Fin 5):=
  ⟨fun p=> ![p.1,p.2.1,p.2.2.1,p.2.2.2],fun z=>(z 0,z 1,z 2,z 3),
   fun _=>rfl,fun z=>by ext i;fin_cases i<;>rfl⟩
 have J (c d e f:Fin 5):Function.Injective (q (c,d,e,f))↔K c d e f:=by
  refine⟨fun h=> ?_,fun⟨M,Q,R,S,T,U⟩ i j N=> ?_⟩
  ·have o (i j:Fin 4) (A:i≠j:=by decide):q (c,d,e,f) i≠q (c,d,e,f) j:=fun p=>A (h p)
   exact⟨o 0 1,o 0 2,o 0 3,o 1 2,o 1 3,o 2 3⟩
  ·change ![c,d,e,f] i= ![c,d,e,f] j at N;fin_cases i<;>fin_cases j<;>simp_all[Ne.symm]
 have g (i j:Fin 4):(∑c:Fin 5,∑d:Fin 5,if cm c=i∧cm d=j then
   ∑e:Fin 5,∑f:Fin 5,if K c d e f then a (cm e)*b (cm f) else 0 else 0)=0:=by
  let F (z:Fin 4→Fin 5):=if cm (z 0)=i∧cm (z 1)=j then unf a (z 2)*unf b (z 3) else 0
  have H:(∑z:Fin 4→Fin 5,if Function.Injective z then F z else 0)=0:=by
   have M:(∑e:Fin 4 ↪ Fin 5,F e)=∑z,if Function.Injective z then F z else 0:=by rw[←(Equiv.subtypeInjectiveEquivEmbedding (Fin 4) (Fin 5)).sum_comp,←sum_filter (p:=Function.Injective)];exact(sum_subtype _ (fun _=>by simp) F).symm
   exact M.symm.trans (h i j)
  have O (c d e f:Fin 5):F (q (c,d,e,f))=if cm c=i∧cm d=j then a (cm e)*b (cm f) else 0:=rfl
  rw[←q.sum_comp] at H;simp only[Fintype.sum_prod_type] at H;refine(sum_congr rfl fun c _=>sum_congr rfl fun d _=> ?_).symm.trans H
  split_ifs with hc<;>simp[O,J,hc]
 have B:=g 0 0;have t:=g 0 1;have u:=g 0 2;have v:=g 0 3;have w:=g 1 2;have x:=g 1 3;have y:=g 2 3;simp(config:={decide:=true}) only[Fin.sum_univ_five,K,cm,Matrix.cons_val_zero,
  Matrix.cons_val_one,Matrix.cons_val,ite_true,ite_false,add_zero,zero_add]
  at B t u v w x y
 let r (i j:Fin 4):=a i*b j+b i*a j
 have k:a 0*b 0=0:=by linear_combination(w+x+y)/6-(t+u+v-B)/12
 have l:r 0 1=0:=by linear_combination y/2-k
 have m:r 0 2=0:=by linear_combination x/2-k
 have n:r 0 3=0:=by linear_combination w/2-k
 have G:r 2 3=0:=by linear_combination t/2-m-n
 have E:r 1 3=0:=by linear_combination u/2-l-n
 have C:r 1 2=0:=by linear_combination v/2-l-m
 have s {i j:Fin 4} (P:r i j=0):r j i=0:=by linear_combination P
 refine⟨fun i j A=> ?_,k⟩;fin_cases i<;>fin_cases j<;>first
  | exact absurd rfl A | exact l | exact m | exact n | exact C | exact E | exact G
  | exact s l | exact s m | exact s n | exact s C | exact s E | exact s G
lemma std {L : Submodule ℂ aC} (hL : aD L) (hd : aX L = 7)
  (hfix : ∀ t ∈ L, ∀ i, t (i, 0) = t (i, 1)) (hp : p L 0 1 = 5) :
  u
   L 3 = 2 ∨ u L 2 = 2 ∨
   (Module.finrank ℂ (L.map (row 0)) = 3 ∧ Module.finrank ℂ (L.map (row 1)) = 3 ∧
     ∀ t ∈ L, t (0, 0) = t (1, 0)) := by
 classical
 let K : Submodule ℂ aC := L ⊓ LinearMap.ker ((row 0).prod (row 1))
 have hK2 : Module.finrank ℂ K = 2 := by
  have h : Module.finrank ℂ (L.map ((row 0).prod (row 1))) + Module.finrank ℂ K = Module.finrank ℂ L := by
   rw [← (Submodule.submoduleOfEquivInf _ _).finrank_eq,
    ← (((row 0).prod (row 1)).submoduleMap L).finrank_range_add_finrank_ker,
    LinearMap.range_submoduleMap, LinearMap.ker_submoduleMap]; simp
  change p L 0 1 + Module.finrank ℂ K = aX L at h; omega
 have k0 {t : aC} (ht : t ∈ K) : row 0 t = 0 := congrArg Prod.fst (LinearMap.mem_ker.mp ht.2)
 have k1 {t : aC} (ht : t ∈ K) : row 1 t = 0 := congrArg Prod.snd (LinearMap.mem_ker.mp ht.2)
 have uf (t : aC) (ht : t ∈ L) (r : Fin 4) : unf (lC r t) = row r t :=
  aEy (row r t) (hfix t ht r)
 let G : aC →ₗ[ℂ] V4 × V4 := (lC 0).prod (lC 1)
 have hG5 : Module.finrank ℂ (L.map G) = 5 := by
  have h1 : Module.finrank ℂ (L.map G) ≤ p L 0 1 :=
   (Submodule.map_comp ((row 0).prod (row 1)) (gF.prodMap gF) L).symm ▸ Submodule.finrank_map_le _ _
  have h2 : p L 0 1 ≤ Module.finrank ℂ (L.map G) := (Submodule.finrank_mono (show
   L.map ((row 0).prod (row 1)) ≤ (L.map G).map (unf.prodMap unf) by
    rintro _ ⟨t, ht, rfl⟩; exact ⟨G t, ⟨t, ht, rfl⟩, Prod.ext (uf t ht 0) (uf t ht 1)⟩)).trans
   (Submodule.finrank_map_le _ _)
  omega
 have hmissRow (r : Fin 4) : (1 : V4) ∉ L.map (lC r) := fun ⟨t, ht, e⟩ => by
  have h0 : aO (1 + -t) = 0 := sum_eq_zero fun emb _ => prod_eq_zero (mem_univ r) (by
   change (1 : ℂ) + -t (r, emb r) = 0
   have h1 : t (r, emb r) = 1 := congrFun (by rw [← uf t ht r, e]; rfl : row r t = 1) (emb r)
   rw [h1]; ring)
  have h1 := hL (-t) (L.neg_mem ht); rw [h0] at h1; norm_num at h1
 have frowNorm (r : Fin 4) : ∃ f : Module.Dual ℂ V4, f 1 = 1 ∧ ∀ t ∈ L, f (lC r t) = 0 := by
  obtain ⟨f, hf, hb⟩ := Submodule.exists_dual_map_eq_bot_of_notMem (hmissRow r) inferInstance
  refine ⟨(f 1)⁻¹ • f, inv_mul_cancel₀ hf, fun t ht => ?_⟩
  have hm : f (lC r t) ∈ (L.map (lC r)).map f := ⟨_, ⟨t, ht, rfl⟩, rfl⟩
  rw [hb] at hm; change (f 1)⁻¹ * f (lC r t) = 0; rw [show f (lC r t) = 0 from hm, mul_zero]
 obtain ⟨f4, hf4, hf4L⟩ := frowNorm 0; obtain ⟨g4, hg4, hg4L⟩ := frowNorm 1
 let W := L.map G ⊔ Submodule.span ℂ {((1 : V4), (1 : V4))}
 have hW6 : Module.finrank ℂ W = 6 := by
  have := Submodule.finrank_sup_span_singleton
   (show ((1, 1) : V4 × V4) ∉ L.map G from fun ⟨t, ht, e⟩ => hmissRow 0 ⟨t, ht, congrArg Prod.fst e⟩)
  change Module.finrank ℂ W = _ at this; omega
 have wmem (w : V4 × V4) (hw : w ∈ W) : ∃ m ∈ L, ∃ c : ℂ,
   w = (lC 0 m + c • (1 : V4), lC 1 m + c • (1 : V4)) := by
  obtain ⟨_, ⟨m, hm, rfl⟩, _, hy, rfl⟩ := Submodule.mem_sup.mp hw
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy; exact ⟨m, hm, c, rfl⟩
 obtain ⟨pp, q, hpp, hq, hW⟩ := dN W hW6 f4 g4 hf4 hg4
  (fun w hw => by obtain ⟨m, hm, c, rfl⟩ := wmem w hw; simp only [map_add, map_smul, hf4L m hm, hg4L m hm, hf4, hg4])
  (Submodule.mem_sup_right (Submodule.subset_span rfl))
 set u := cR f4; set v := cR g4
 have hu : u ⬝ᵥ 1 = 1 := (dI f4 1).trans hf4
 have hv : v ⬝ᵥ 1 = 1 := (dI g4 1).trans hg4
 have iso (t : aC) (ht : t ∈ K) (x y : V4) (hw : (x, y) ∈ W) :
   x ⬝ᵥ (Zf (row 2 t) (row 3 t) *ᵥ y) = 0 := by
  obtain ⟨m, hm, c, e⟩ := wmem _ hw; obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  rw [aHd, map_add, map_add, map_smul, uf m hm 0, uf m hm 1, add_comm (row 0 m), add_comm (row 1 m)]
  exact aF3 hL hm ht.1 (k0 ht) (k1 ht) c
 by_cases hzero : ∀ t ∈ K, ∀ i j, Zf (row 2 t) (row 3 t) i j = 0
 ·let a (k : Fin 4) : Module.Dual ℂ K := (LinearMap.proj ((2 : Fin 4), k.succ)) ∘ₗ K.subtype
  let b (k : Fin 4) : Module.Dual ℂ K := (LinearMap.proj ((3 : Fin 4), k.succ)) ∘ₗ K.subtype
  have mn (x : K) := aGs (lC 2 (x : aC)) (lC 3 (x : aC)) (by
   rw [uf _ x.2.1 2, uf _ x.2.1 3]; exact hzero x x.2)
  have jS (t : aC) (ht : t ∈ L) (r : Fin 4) (hr : ∀ k : Fin 4, t (r, k.succ) = 0)
    (c : Fin 5) : t (r, c) = 0 := by
   rcases Fin.eq_zero_or_eq_succ c with rfl | ⟨k, rfl⟩
   ·exact (hfix t ht r).trans (hr 0)
   ·exact hr k
  have sum_er (r : Fin 4) (w : aH) : 5 * ∑ e : Fin 4 ↪ Fin 5, w (e r) = 120 * ∑ c, w c := by
   have h (k : Fin 5) : (∑ e : Fin 4 ↪ Fin 5, w (e r)) = ∑ e : Fin 4 ↪ Fin 5, w (e r + k) :=
    ((Equiv.embeddingCongr (.refl _) (Equiv.addRight k)).sum_comp fun e => w (e r)).symm
   have hs := sum_congr (s₁ := (univ : Finset (Fin 5))) rfl fun k _ => h k
   have ha (c : Fin 5) : ∑ k : Fin 5, w (c + k) = ∑ k, w k := Equiv.sum_comp (Equiv.addLeft c) w
   rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, sum_comm] at hs
   simpa [ha, Fintype.card_embedding_eq] using hs
  have zT := tB a b
   (fun x hxa hxb => Subtype.ext (funext fun ⟨r, c⟩ => by
     fin_cases r
     ·exact congrFun (k0 x.2) c
     ·exact congrFun (k1 x.2) c
     ·exact jS x x.2.1 2 hxa c
     ·exact jS x x.2.1 3 hxb c))
   (fun x => by
     have z0 (c : Fin 5) : (x : aC) (0, c) = 0 := congrFun (k0 x.2) c
     have z1 (c : Fin 5) : (x : aC) (1, c) = 0 := congrFun (k1 x.2) c
     have hdiff : aO (1 + (x : aC)) - aO (1 + -(x : aC)) =
       2 * ((∑ e : Fin 4 ↪ Fin 5, (x : aC) (2, e 2)) + ∑ e : Fin 4 ↪ Fin 5, (x : aC) (3, e 3)) := by
      simp only [aCx, F4, Pi.add_apply, Pi.neg_apply, Pi.one_apply, LinearMap.funLeft_apply,
       z0, z1, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
      exact sum_congr rfl fun e _ => by ring
     rw [hL x x.2.1, hL (-x) (L.neg_mem x.2.1)] at hdiff
     have s2 := sum_er 2 (fun c => (x : aC) (2, c)); have s3 := sum_er 3 (fun c => (x : aC) (3, c))
     have hsum (r : Fin 4) : ∑ j, (x : aC) (r, j) = (x : aC) (r, 1) + ∑ j : Fin 4, (x : aC) (r, j.succ) := by
      rw [Fin.sum_univ_succ, hfix _ x.2.1 r]
     have s : (∑ j, (x : aC) (2, j)) + ∑ j, (x : aC) (3, j) = 0 := by
      linear_combination (-5 * hdiff - 2 * s2 - 2 * s3) / 240
     rw [hsum 2, hsum 3] at s; rw [sum_add_distrib]
     change ∑ j : Fin 4, (x : aC) (2, j.succ) + ∑ j : Fin 4, (x : aC) (3, j.succ) + ((x : aC) (2, 1) + (x : aC) (3, 1)) = 0
     linear_combination s)
   (fun x i j hij => (mn x).1 i j hij) (fun x => (mn x).2) hK2.ge
  have pure (r s : Fin 4) (h0s : (0 : Fin 4) ≠ s) (h1s : (1 : Fin 4) ≠ s)
    (hcov : ∀ q : Fin 4, q ≠ s → q = 0 ∨ q = 1 ∨ q = r) (hr : ∀ t ∈ K, row r t = 0) : Ac.u L s = 2 := by
   have e : aZ L s = K := by
    ext t; simp only [aZ, K, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
     LinearMap.prod_apply, Function.prod_apply, Prod.mk_eq_zero, Subtype.forall]
    exact and_congr_right fun ht => ⟨fun hz => ⟨hz 0 h0s, hz 1 h1s⟩, fun ⟨z0, z1⟩ q hq => by
     rcases hcov q hq with rfl | rfl | rfl; exacts [z0, z1, hr t ⟨ht, LinearMap.mem_ker.mpr (Prod.ext z0 z1)⟩]⟩
   change Module.finrank ℂ (aZ L s) = 2; rw [e]; exact hK2
  rcases zT with h | h
  ·exact Or.inl (pure 2 3 (by decide) (by decide) (by decide) fun t ht =>
    funext (jS t ht.1 2 fun k => LinearMap.congr_fun (h k) ⟨t, ht⟩))
  ·exact Or.inr (Or.inl (pure 3 2 (by decide) (by decide) (by decide) fun t ht =>
    funext (jS t ht.1 3 fun k => LinearMap.congr_fun (h k) ⟨t, ht⟩)))
 ·push Not at hzero; obtain ⟨t, ht, i0, j0, hne⟩ := hzero
  refine Or.inr (Or.inr ?_)
  rcases mJ (Zf (row 2 t) (row 3 t)) u v pp q hu hv hpp hq
   (aCz _ _) (aC0 _ _) (fun x y h₁ h₂ => iso t ht x y ((hW x y).mpr ⟨h₁, h₂⟩)) with
   hz | ⟨hn, c, hc, hz⟩
  ·exact absurd (hz i0 j0) hne
  rcases qU u v pp q hu hv hpp hq hn
   (fun j hj => (mul_eq_zero.mp ((hz j j).symm.trans (aC0 _ _ j hj))).resolve_left hc)
   (fun i j => mul_left_cancel₀ hc ((hz i j).symm.trans ((aCz _ _ i j).trans (hz j i)))) with
   ⟨j, hj0, huv, huj, hpj, hqj⟩ | ⟨hq0, h0eq⟩
  ·exfalso
   let e : V4 := Pi.single j 1
   obtain ⟨m, hm, c', he⟩ := wmem _ ((hW e e).mpr ⟨by simpa [e] using huv, by simp [e, hpj, hqj]⟩)
   have he0 : e = lC 0 m + c' • 1 := congrArg Prod.fst he
   have hc' : c' ≠ 0 := by
    rintro rfl; rw [zero_smul, add_zero] at he0
    exact huj (by simpa [e, u, ← he0, ← dI f4 e] using hf4L m hm)
   have z (r : Fin 4) (hr : e = lC r m + c' • 1) (jS : Fin 5) (hcol : jS ≠ j.succ) :
     (1 + c'⁻¹ • m) (r, jS) = 0 := by
    have h1 : (0 : ℂ) = m (r, jS) + c' := by
     have := congrFun (congrArg unf hr) jS; rw [map_add, map_smul, uf m hm r] at this
     simpa [e, (by decide : ∀ j' : Fin 4, j' ≠ 0 → ∀ c : Fin 5, c ≠ j'.succ → cm c ≠ j') j hj0 jS hcol] using this
    change 1 + c'⁻¹ * m (r, jS) = 0
    rw [show m (r, jS) = -c' by linear_combination -h1]; simp [hc']
   have hz' : aO (1 + c'⁻¹ • m) = 0 := sum_eq_zero fun emb _ => by
    by_cases he' : emb 0 = j.succ
    ·exact prod_eq_zero (mem_univ 1) (z 1 (congrArg Prod.snd he) _ fun h =>
      absurd (emb.injective (h.trans he'.symm)) (by decide))
    ·exact prod_eq_zero (mem_univ 0) (z 0 he0 _ he')
   have lev := hL _ (L.smul_mem c'⁻¹ hm); rw [hz'] at lev; norm_num at lev
  ·obtain ⟨bq, hbq, hbq'⟩ := jK v q hv hq hq0
   obtain ⟨bp, hbp, hbp'⟩ := jK u pp hu hpp hn
   have sr (r : Fin 4) (h : ∀ x : V4, ∃ m ∈ L, ∃ c : ℂ, x = lC r m + c • 1) :
     Module.finrank ℂ (L.map (row r)) = 3 := by
    have htop : L.map (lC r) ⊔ Submodule.span ℂ {(1 : V4)} = ⊤ := eq_top_iff.mpr fun x _ =>
     let ⟨m, hm, c, e⟩ := h x; e ▸ Submodule.add_mem_sup ⟨m, hm, rfl⟩ (Submodule.smul_mem _ c (Submodule.subset_span rfl))
    have h3 := Submodule.finrank_sup_span_singleton (hmissRow r)
    rw [htop, finrank_top] at h3
    have : Module.finrank ℂ (L.map (lC r)) ≤ Module.finrank ℂ (L.map (row r)) :=
     (Submodule.map_comp (row r) gF L).symm ▸ Submodule.finrank_map_le gF (L.map (row r))
    have : Module.finrank ℂ (L.map (row r)) ≤ Module.finrank ℂ (L.map (lC r)) :=
     (Submodule.finrank_mono (show L.map (row r) ≤ (L.map (lC r)).map unf by
       rintro _ ⟨m, hm, rfl⟩; exact ⟨lC r m, ⟨m, hm, rfl⟩, uf m hm r⟩)).trans (Submodule.finrank_map_le unf _)
    have : Module.finrank ℂ V4 = 4 := by simp [V4]
    omega
   refine ⟨sr 0 fun x => ?_, sr 1 fun y => ?_, fun t' ht' => ?_⟩
   ·obtain ⟨m, hm, c', he⟩ := wmem _ ((hW x ((u ⬝ᵥ x) • 1 + (pp ⬝ᵥ x) • bq)).mpr
     ⟨by simp [hv, hbq], by simp [hq, hbq']⟩)
    exact ⟨m, hm, c', congrArg Prod.fst he⟩
   ·obtain ⟨m, hm, c', he⟩ := wmem _ ((hW ((v ⬝ᵥ y) • 1 + (q ⬝ᵥ y) • bp) y).mpr
     ⟨by simp [hu, hbp], by simp [hpp, hbp']⟩)
    exact ⟨m, hm, c', congrArg Prod.snd he⟩
   ·obtain ⟨H1, H2⟩ := (hW _ _).mp (Submodule.mem_sup_left ⟨t', ht', rfl⟩)
    rw [hfix t' ht' 0, hfix t' ht' 1]; exact h0eq _ _ H1 H2
end Ac.Ad.Bf
namespace Ac.Ad
open Aa
lemma mK {L:Submodule ℂ aC} (hL:aD L) (G:aX L=7)
  {a b:Fin 5} (hab:a≠b) (hfix:∀t∈L,∀i,t (i,a)=t (i,b))
  {i j k l:Fin 4} (K:i≠j) (M:i≠k) (N:i≠l)
  (O:j≠k) (P:j≠l) (Q:k≠l) (H:p L i j=5):
  u
   L k=2∨u L l=2∨
   (Module.finrank ℂ (L.map (row i))=3∧Module.finrank ℂ (L.map (row j))=3∧
     ∀t∈L,t (i,a)=t (j,a)):=by
 classical
 have C:Equiv.swap 0 a b≠0:=fun q=>hab (by simpa using(congrArg (Equiv.swap 0 a) q).symm)
 let σ:Equiv.Perm (Fin 5):=Equiv.swap 0 a*Equiv.swap 1 (Equiv.swap 0 a b)
 have hσ0:σ 0=a:=by simp[σ,Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne (by decide:(0:Fin 5)≠1) C.symm]
 have hσ1:σ 1=b:=by simp[σ,Equiv.Perm.mul_apply]
 have E:Function.Injective ![i,j,k,l]:=fun x y h=>by fin_cases x<;>fin_cases y<;>simp_all[Ne.symm]
 let ρ:Equiv.Perm (Fin 4):=Equiv.ofBijective _ (Finite.injective_iff_bijective.mp E)
 let R:aC→ₗ[ℂ] aC:=LinearMap.funLeft ℂ ℂ (fun p:Fin 4×Fin 5=>(ρ p.1,σ p.2))
 let L':=L.map R
 have Rinj:Function.Injective R:=LinearMap.funLeft_injective_of_surjective ℂ ℂ _ (Equiv.prodCongr ρ σ).surjective;have z:aD L':=fun _ ⟨x,g,e⟩=>e▸(by
  rw[←hL x g,aO,aO];conv_rhs=>rw[←(Equiv.embeddingCongr ρ σ).sum_comp]
  exact Finset.sum_congr rfl fun f _=>by simpa[R] using Equiv.prod_comp ρ (fun r=>(1+x) (r,σ (f (ρ.symm r)))))
 have A:aX L'=7:=(Submodule.equivMapOfInjective R Rinj L).finrank_eq.symm.trans G;have m:∀t∈L',∀r,t (r,0)=t (r,1):=by rintro _ ⟨x,g,rfl⟩ r;change x (ρ r,σ 0)=x (ρ r,σ 1);rw[hσ0,hσ1];exact hfix x g _
 let S:aH→ₗ[ℂ] aH:=LinearMap.funLeft ℂ ℂ σ
 have Sinj:Function.Injective S:=LinearMap.funLeft_injective_of_surjective ℂ ℂ σ σ.surjective;have d (r:Fin 4):
   Module.finrank ℂ (L'.map (row r))=Module.finrank ℂ (L.map (row (ρ r))):=by
  rw[show L'.map (row r)=(L.map (row (ρ r))).map S by rw[←Submodule.map_comp,←Submodule.map_comp];rfl];exact(Submodule.equivMapOfInjective S Sinj _).finrank_eq.symm
 have B:p L' 0 1=5:=by change Module.finrank ℂ (L'.map ((row 0).prod (row 1)))=5;rw[show L'.map ((row 0).prod (row 1))=(L.map ((row i).prod (row j))).map (S.prodMap S) by rw[←Submodule.map_comp,←Submodule.map_comp];rfl];exact(Submodule.equivMapOfInjective _ (Function.Injective.prodMap Sinj Sinj) _).finrank_eq.symm.trans H
 have n (r:Fin 4):u L' r=u L (ρ r):=by
  have e:aZ L' r=(aZ L (ρ r)).map R:=by
   ext t;simp only[aZ,L',Submodule.mem_inf,Submodule.mem_iInf,Submodule.mem_map,LinearMap.mem_ker,Subtype.forall];constructor
   ·rintro⟨⟨x,g,rfl⟩,h⟩;refine⟨x,⟨g,fun s w=>(map_eq_zero_iff S Sinj).mp ?_⟩,rfl⟩;have v:S (row s x)=row (ρ.symm s) (R x):=by funext c;simp[S,R]
    rw[v];exact h (ρ.symm s) (fun o=>w (by rw[←o,ρ.apply_symm_apply]))
   ·rintro⟨x,⟨g,h⟩,rfl⟩;exact⟨⟨x,g,rfl⟩,fun s w=>(map_eq_zero_iff S Sinj).mpr (h (ρ s) (fun o=>w (ρ.injective o)))⟩
  change Module.finrank ℂ (aZ L' r)=Module.finrank ℂ (aZ L (ρ r));rw[e];exact(Submodule.equivMapOfInjective R Rinj _).finrank_eq.symm
 rcases Bf.std z A m B with h|h|⟨q,v,F⟩
 ·exact Or.inr (Or.inl ((n 3).symm.trans h))
 ·exact Or.inl ((n 2).symm.trans h)
 ·exact Or.inr (Or.inr ⟨(d 0).symm.trans q,(d 1).symm.trans v,fun t J=>by simpa[R,ρ,hσ0] using F (R t) ⟨t,J,rfl⟩⟩)
end Ac.Ad
lemma Ac.vV:Ac.eI:=by
 apply Ac.Ad.aEw
 ·exact @Ac.Ad.mK
 ·exact @Ac.Ad.vU
namespace Ac.Ae
open Aa
abbrev F:=Fin 5
abbrev Q:=Fin 4
abbrev cS (x:aH):ℂ:=∑i,x i
def aL (a b:aH) (i j:F):=a i*b j+a j*b i
def dQ (x y:aH):ℂ:=∑i:F,∑j:F,if i<j then aL x y i j else 0
def dL (a b:aH) (i j:F):ℂ:=if i=j then 0 else ∑c:F,∑d:F,if c<d∧c≠i∧c≠j∧d≠i∧d≠j then aL a b c d else 0
def bil (x y:aH) (z:F→F→ℂ):ℂ:=∑i,∑j,x i*z i j*y j
def bD (a b x y:aH):aC:=fun p=> ![a,b,x,y] p.1 p.2
def aM (s:ℂ) (x:aC):aC:=fun a=>s+x a
def aR (L:Submodule ℂ aC) (x:aC) (s:ℂ):=∃t∈L,x=aM s t
end Ac.Ae
namespace Ac.Ae
open Aa
lemma aBw (x:aC) (c:ℂ):aO (c•x)=c^4*aO x:=by unfold aO;rw[Finset.mul_sum];apply Finset.sum_congr rfl;intro f _;simp only[Pi.smul_apply,smul_eq_mul,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
lemma tC {L:Submodule ℂ aC} (hL:aD L) {x:aC} (a:x∈L):
  aO x=0:=by
 rw[cK];exact(Ac.Ad.cT hL a).2.2.2
lemma bR {L:Submodule ℂ aC} (hL:aD L) {x:aC} (b:x∈L) (s:ℂ):
  aO (aM s x)=120*s^4:=by
 by_cases c:s=0
 ·subst s;have a:aM 0 x=x:=by funext i;simp[aM]
  simp[a,tC hL b]
 ·have a:aM s x=s•(1+s⁻¹ •x):=by
   funext i;simp[aM,mul_add,c]
  rw[a,aBw,hL _ (L.smul_mem _ b),mul_comm]
lemma fU {L:Submodule ℂ aC} (hL:aD L) {x:aC} {s:ℂ}
  (b:aR L x s):aO x=120*s^4:=by
 obtain⟨t,a,rfl⟩:=b;exact bR hL a s
end Ac.Ae
namespace Ac.Ae
open Aa
abbrev kS (a b:aH):Prop:=
 (∃i:F,a i≠0∧b i≠0∧b= -a∧
   ∀k,k≠i→a k=0∧b k=0)∨
 (∃i j:F,i≠j∧a i≠0∧a j≠0∧b i≠0∧b j≠0∧
   (∀k,k≠i→k≠j→a k=0∧b k=0)∧
   a i*b j-a j*b i≠0∧cS a≠0∧cS b≠0)
lemma qG (x:aH) {i j:F} (a:i≠j)
  (c:∀k,k≠i→k≠j→x k=0):cS x=x i+x j:=by
 classical
 calc
  cS x=∑k∈({i,j}:Finset F),x k:=by symm;apply Finset.sum_subset (Finset.subset_univ _);intro k _ b;exact c k (fun h=>b (by simp[h])) (fun h=>b (by simp[h]))
  _=_:=by simp[a]
lemma gN {a b:aH} (E:a≠0) (G:b≠0)
  (J:∀i j,i≠j→aL a b i j=0) (p:cS a+cS b=0):
  kS a b:=by
 classical
 have h (i j:F) (l:i≠j):a i*b j+a j*b i=0:=J i j l;have o (i:F) (w:a i≠0):b i≠0:=by
  intro q;apply G;funext k;change b k=0;by_cases c:i=k
  ·subst k;exact q
  ·have e:=h i k c;simpa[q,w] using e
 obtain⟨i,g⟩:∃i,a i≠0:=by by_contra! y;exact E (funext y)
 have s:=o i g;by_cases u:∃j,i≠j∧a j≠0
 ·obtain⟨j,l,r⟩:=u;have t:=o j r;have det:a i*b j-a j*b i≠0:=by
   intro d;apply mul_ne_zero g t;linear_combination(h i j l+d)/2
  have f (k:F) (C:k≠i) (H:k≠j):a k=0∧b k=0:=by
   have e:(a i*b j-a j*b i)*a k=0:=by linear_combination a i*h j k H.symm-a j*h i k C.symm
   have n:=(mul_eq_zero.mp e).resolve_left det;exact⟨n,by simpa[n,g] using h i k C.symm⟩
  have A:=qG a l (fun k c v=>(f k c v).1);have B:=qG b l (fun k c v=>(f k c v).2);have m:cS a≠0:=by
   intro z;have K:a i+a j=0:=A.symm.trans z;have M:b i+b j=0:=by rw[z,zero_add,B] at p;exact p
   apply det;linear_combination a i*M-b i*K
  exact Or.inr ⟨i,j,l,g,r,s,t,f,det,m,fun z=>m (by simpa[z] using p)⟩
 ·have f (k:F) (c:k≠i):a k=0∧b k=0:=by
   have n:a k=0:=by by_contra w;exact u ⟨k,c.symm,w⟩
   exact⟨n,by simpa[n,g] using h i k c.symm⟩
  have one (x:aH) (q:∀k,k≠i→x k=0):cS x=x i:=Finset.sum_eq_single i (fun k _ c=>q k c) (by simp);have A:=one a fun k c=>(f k c).1
  have B:=one b fun k c=>(f k c).2
  rw[A,B] at p;refine Or.inl ⟨i,g,s,?_,f⟩;funext k;change b k= -(a k)
  by_cases c:k=i
  ·subst k;linear_combination p
  ·simp[(f k c).1,(f k c).2]
end Ac.Ae
namespace Ac.Ae
open Aa
lemma aC1 (f:F→ℂ):
  ∑i,f i=f 0+f 1+f 2+f 3+f 4:=by
 simp[Fin.sum_univ_succ];ring
lemma zC (i:F):i=0∨i=1∨i=2∨i=3∨i=4:=by decide+revert
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
lemma gX (a b x y:aH):
  aO (bD a b x y)=bil x y (dL a b):=by
 have c (i:F):bD a b x y (0,i)=a i:=rfl;have d (i:F):bD a b x y (1,i)=b i:=rfl;have e (i:F):bD a b x y (2,i)=x i:=rfl;have f (i:F):bD a b x y (3,i)=y i:=rfl;rw[cK];simp(config:={decide:=true}) only[bil,dL,aL,aC1,c,d,e,f,ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul];ring
set_option maxHeartbeats 3000000 in
lemma iF (a b:aH) (i:F):
  (∑j,dL a b i j)=2*(dQ a b-
    (a i*cS b+b i*cS a-2*a i*b i)):=by
 rcases zC i with rfl|rfl|rfl|rfl|rfl<;>simp(config:={decide:=true}) only[dL,dQ,aL,cS,aC1,ite_true,ite_false,zero_add,add_zero]<;>ring
set_option maxHeartbeats 3000000 in
lemma pO (a b:aH):
  (∑i,∑j,dL a b i j)=6*dQ a b:=by
 simp_rw[iF];simp(config:={decide:=true}) only[dQ,aL,cS,aC1,ite_true,ite_false,zero_add,add_zero];ring
set_option maxHeartbeats 4000000 in
lemma aEz (a b:aH) (i j:F) (h:i≠j):
  dL a b i j=dQ a b-
   (a i*cS b+b i*cS a-2*a i*b i)-
   (a j*cS b+b j*cS a-2*a j*b j)+aL a b i j:=by
 rcases zC i with rfl|rfl|rfl|rfl|rfl<;>
  rcases zC j with rfl|rfl|rfl|rfl|rfl<;>first
  | exact(h rfl).elim
  | simp(config:={decide:=true}) only[dL,dQ,aL,cS,aC1,
     ite_true,ite_false,zero_add,add_zero]
    ring
lemma oG (a b:aH) (i j:F) (h:i≠j):
  6
   *aL a b i j=6*dL a b i j-3*(∑k,dL a b i k)-
   3*(∑k,dL a b j k)+(∑k,∑l,dL a b k l):=by
 rw[pO,iF,iF,aEz a b i j h];ring
lemma tD (a b:aH) (c:∀i j,i≠j→dL a b i j=0):
  ∀i j,i≠j→aL a b i j=0:=by
 have z (i j:F):dL a b i j=0:=by
  by_cases h:i=j
  ·simp[dL,h]
  ·exact c i j h
 intro i j h;have e:=oG a b i j h;simpa[z] using e
end Ac.Ae
namespace Ac.Ae
open Aa
lemma lD (a u b x y:aH):
  aO (bD (a+u) b x y)=aO (bD a b x y)+aO (bD u b x y):=by
 unfold aO;rw[←Finset.sum_add_distrib];apply Finset.sum_congr rfl;intro f _;simp[Fin.prod_univ_four,bD,add_mul]
lemma iR (a b v x y:aH):
  aO (bD a (b+v) x y)=aO (bD a b x y)+aO (bD a v x y):=by
 unfold aO;rw[←Finset.sum_add_distrib];apply Finset.sum_congr rfl;intro f _;simp[Fin.prod_univ_four,bD,mul_add,add_mul]
lemma rR {L:Submodule ℂ aC} (hL:aD L) {a b:aH}
  (n:bD a b 0 0∈L) {x:aC} {s:ℂ} (q:aR L x s):
  bil (row 2 x) (row 3 x) (dL a b)=0:=by
 let U:=bD a b 0 0
 have m (k:ℂ):aR L (x+k•U) s:=by obtain⟨t,p,rfl⟩:=q;exact⟨t+k•U,L.add_mem p (L.smul_mem k n),by funext i;simp[aM,add_assoc]⟩
 let c:=row 0 x
 let d:=row 1 x
 let y:=row 2 x
 let z:=row 3 x
 have e (k:ℂ):aO (bD (c+k•a) (d+k•b) y z)=120*s^4:=by
  have o:bD (c+k•a) (d+k•b) y z=x+k•U:=by funext ⟨i,j⟩;fin_cases i<;>simp[bD,c,d,y,z,U,row]
  rw[o];exact fU hL (m k)
 have f:=e 0;have g:=e 1;have h:=e (2:ℂ);simp only[zero_smul,add_zero] at f;simp only[one_smul,lD,iR] at g;have l (v:aH):(2:ℂ)•v=v+v:=by rw[two_smul]
 simp only[l,lD,iR] at h;rw[←gX];linear_combination(h-2*g+f)/2
end Ac.Ae
namespace Ac.Ae
open Aa Ac.Ad
lemma zD (i j:Fin 4) (a:i≠j):
  ∃ρ:Equiv.Perm (Fin 4),ρ 2=i∧ρ 3=j:=by
 have h:Equiv.swap 2 i j≠2:=by intro b;apply a;simpa using(congrArg (Equiv.swap 2 i) b).symm
 refine⟨Equiv.swap 2 i*Equiv.swap 3 (Equiv.swap 2 i j),?_,?_⟩
 ·simp[Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne (by decide:(2:Fin 4)≠3) h.symm]
 ·simp[Equiv.Perm.mul_apply]
lemma aGt (ρ:Equiv.Perm (Fin 4)) (L:Submodule ℂ aC) (i j:Fin 4):
  p (L.map (re ρ 1)) i j=p L (ρ i) (ρ j):=by
 unfold p;rw[←Submodule.map_comp];rfl
lemma aBx (ρ:Equiv.Perm (Fin 4)) (L:Submodule ℂ aC) (i:Fin 4):
  aZ (L.map (re ρ 1)) i=(aZ L (ρ i)).map (re ρ 1):=by
 ext x;simp only[aZ,Submodule.mem_map,Submodule.mem_inf,Submodule.mem_iInf,LinearMap.mem_ker];constructor
 ·rintro⟨⟨y,c,rfl⟩,b⟩;refine⟨y,⟨c,?_⟩,rfl⟩;intro k;have e:ρ.symm k.val≠i:=by
   exact fun a=>k.property (by simpa using congrArg ρ a)
  have d:=b ⟨ρ.symm k.val,e⟩;change row (ρ (ρ.symm k.val)) y=0 at d;simpa only[Equiv.apply_symm_apply] using d
 ·rintro⟨y,⟨c,b⟩,rfl⟩;refine⟨⟨y,c,rfl⟩,?_⟩;intro k;exact b ⟨ρ k.val,fun a=>k.property (ρ.injective a)⟩
lemma aF4 (ρ:Equiv.Perm (Fin 4)) (L:Submodule ℂ aC) (i:Fin 4):
  u (L.map (re ρ 1)) i=u L (ρ i):=by
 unfold u;rw[aBx,nL]
lemma pT (h:
  ∀L,aD L→aX L=8→(∀i,u L i=0)→p L 2 3=7→False):
  HighPair:=by
 intro L hL b f i j a e;obtain⟨ρ,c,d⟩:=zD i j a;apply h (L.map (re ρ 1)) (gI ρ 1 hL) (by rw[nL,b])
  (fun k=>(aF4 ρ L k).trans (f (ρ k)))
 simpa[aGt,c,d] using e
end Ac.Ae
namespace Ac.Ap
open Aa Finset
abbrev Vn (n:ℕ):=Fin n→ℂ
def bv (w x:Vn n):ℂ:=∑j,w j*x j
def bb (Z:Matrix (Fin n) (Fin n) ℂ) (x y:Vn n):ℂ:=∑i,∑j,x i*Z i j*y j
def cN (i:Fin n):Vn n:=fun j=>if j=i then 1 else 0
lemma gY (w:Vn n) (i:Fin n):bv w (cN i)=w i:=by simp[bv,cN,mul_ite]
lemma zE (Z:Matrix (Fin n) (Fin n) ℂ) (i j:Fin n):
  bb Z (cN i) (cN j)=Z i j:=by
 classical
 simp[bb,cN,mul_ite,ite_mul]
lemma oH (w x y:Vn n):bv w (x+y)=bv w x+bv w y:=by simp[bv,mul_add,Finset.sum_add_distrib]
lemma jE (w x:Vn n) (c:ℂ):bv w (c•x)=c*bv w x:=by simp[bv,Finset.mul_sum,mul_left_comm]
lemma aC2 (Z:Matrix (Fin n) (Fin n) ℂ) (x a y:Vn n):
  bb Z (x+a) y=bb Z x y+bb Z a y:=by
 simp[bb,add_mul,Finset.sum_add_distrib]
lemma zF (Z:Matrix (Fin n) (Fin n) ℂ) (x b y:Vn n):
  bb Z x (b+y)=bb Z x b+bb Z x y:=by
 simp[bb,mul_add,Finset.sum_add_distrib]
lemma aAt (Z:Matrix (Fin n) (Fin n) ℂ) (c:ℂ) (x y:Vn n):
  bb Z (c•x) y=c*bb Z x y:=by
 simp[bb,Finset.mul_sum,mul_assoc]
lemma vW (Z:Matrix (Fin n) (Fin n) ℂ) (c:ℂ) (x y:Vn n):
  bb Z x (c•y)=c*bb Z x y:=by
 simp[bb,Finset.mul_sum,mul_left_comm]
def zG (Z:Matrix (Fin n) (Fin n) ℂ) (u v p q:Vn n):Prop:=∀x y,bv u x=bv v y→bv p x=bv q y→bb Z x y=0
lemma jL {Z:Matrix (Fin n) (Fin n) ℂ} {u v p q:Vn n} (h:zG Z u v p q)
  (x y a b:Vn n) (c:bv u x=bv v y) (d:bv p x=bv q y)
  (e:bv u a=bv v b) (f:bv p a=bv q b):
  bb Z x b+bb Z a y=0:=by
 have g:=h (x+a) (y+b) (by simp only[oH,c,e]) (by simp only[oH,d,f]);simpa[aC2,zF,h x y c d,h a b e f,add_comm] using g
lemma jK (u p:Vn n) (e:bv u 1=1) (d:bv p 1=0)
  (c:∃k,p k≠0):∃a,bv u a=0∧bv p a=1:=by
 obtain⟨k,b⟩:=c;refine⟨(p k)⁻¹ •(cN k+(-u k)•(1:Vn n)),?_,?_⟩<;>simp only[jE,oH,gY,e,d]<;>simp[b]
lemma nM {Z:Matrix (Fin n) (Fin n) ℂ} {u v p q:Vn n}
  (h:zG Z u v p q)
  (t:bv u 1=1) (w:bv v 1=1) (s:bv q 1=0)
  (r:∀j,p j=0)
  (l:∀i j,Z i j=Z j i) (d:∀i,Z i i=0):
  ∀i j,Z i j=0:=by
 classical
 have f (x:Vn n):bv p x=0:=by simp[bv,r]
 have m:bb Z 1 1=0:=h _ _ (t.trans w.symm) ((f _).trans s.symm);have o (x y:Vn n) (z:bv q y=0):bb Z x y=0:=by
  have a:=jL h x (bv u x•(1:Vn n)) (bv v y•(1:Vn n)) y
   (by simp[jE,w]) (by simp[jE,f,s])
   (by simp[jE,t]) (by simp[f,z])
  simpa[aAt,vW,m] using a
 by_cases b:∃k,q k≠0
 ·obtain⟨k,e⟩:=b;have c (i j:Fin n):q k*Z i j+ -q j*Z i k=0:=by
   have A:=o (cN i) (q k•cN j+(-q j)•cN k)
    (by simp only[oH,jE,gY];ring)
   simpa only[zF,vW,zE] using A
  have g (j:Fin n):Z k j=0:=by have a:=c k j;rw[d,mul_zero,add_zero] at a;exact(mul_eq_zero.mp a).resolve_left e
  intro i j;have a:=c i j;rw[l i k,g,mul_zero,add_zero] at a;exact(mul_eq_zero.mp a).resolve_left e
 ·push Not at b
  intro i j;simpa only[zE] using o (cN i) (cN j) (by simp[gY,b])
lemma aF5 {Z:Matrix (Fin n) (Fin n) ℂ} (a:∀i j,Z i j=Z j i) (x y:Vn n):
  bb Z x y=bb Z y x:=by
 unfold bb;rw[Finset.sum_comm];apply Finset.sum_congr rfl;intro j _;apply Finset.sum_congr rfl;intro i _;rw[a i j];ring
lemma mJ (Z:Matrix (Fin n) (Fin n) ℂ) (u v p q:Vn n)
  (N:∑j,u j=1) (O:∑j,v j=1)
  (K:∑j,p j=0) (M:∑j,q j=0)
  (l:∀i j,Z i j=Z j i) (m:∀j,Z j j=0)
  (h:∀x y:Vn n,(∑j,u j*x j)=(∑j,v j*y j)→
    (∑j,p j*x j)=(∑j,q j*y j)→(∑i,∑j,x i*Z i j*y j)=0):
  (∀i j,Z i j=0)∨((∃k,p k≠0)∧
    ∃c:ℂ,c≠0∧∀i j,Z i j=c*(u i*q j-p i*v j)):=by
 classical
 change zG Z u v p q at h;have d:bv u 1=1:=by simpa[bv] using N
 have e:bv v 1=1:=by simpa[bv] using O
 have f:bv p 1=0:=by simpa[bv] using K
 have g:bv q 1=0:=by simpa[bv] using M
 by_cases o:∃k,p k≠0
 ·by_cases w:∃k,q k≠0
  ·obtain⟨a,A,r⟩:=jK u p d f o;obtain⟨b,B,s⟩:=jK v q e g w;have F:=h 1 1 (d.trans e.symm) (f.trans g.symm);have hab:=h a b (A.trans B.symm) (r.trans s.symm);have t:=jL h 1 1 a b (d.trans e.symm) (f.trans g.symm)
    (A.trans B.symm) (r.trans s.symm)
   have G (i j:Fin n):Z i j=bb Z 1 b*(u i*q j-p i*v j):=by
    have H:=jL h (cN i) (u i•(1:Vn n)+p i•b)
     (v j•(1:Vn n)+q j•a) (cN j)
     (by simp[gY,jE,oH,e,B])
     (by simp[gY,jE,oH,g,s])
     (by simp[gY,jE,oH,d,A])
     (by simp[gY,jE,oH,f,r])
    simp only[zE,aC2,aAt,zF,vW,F,hab,mul_zero,zero_add,add_zero] at H;linear_combination H-(q j*u i)*t
   by_cases J:bb Z 1 b=0
   ·exact Or.inl fun i j=>by simpa[J] using G i j
   ·exact Or.inr ⟨o,_,J,G⟩
  ·push Not at w
   have z:zG Z v u q p:=fun x y C E=>(aF5 l x y).trans (h y x C.symm E.symm)
   exact Or.inl (nM z e d f w l m)
 ·push Not at o
  exact Or.inl (nM h d e g o l m)
lemma nT {n:ℕ} (u v p q:Fin n→ℂ)
  (r:∑j,u j=1) (t:∑j,v j=1)
  (A:∑j,p j=0) (B:∑j,q j=0)
  (o:∃k,p k≠0)
  (e:∀j,u j*q j-p j*v j=0)
  (c:∀i j,u i*q j-p i*v j=u j*q i-p j*v i):
  ∃j,u j=v j∧u j≠0∧p j=0∧q j=0:=by
 classical
 have b (i:Fin n):q i= -p i:=by
  have h:=Finset.sum_congr (s₁:=(Finset.univ:Finset (Fin n))) rfl
   (fun j _=>c i j)
  simpa[Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.sum_mul,r,t,A,B]
   using h.symm
 have g:∃j,u j+v j≠0:=by by_contra! h;have l:=Finset.sum_eq_zero (s:=(Finset.univ:Finset (Fin n))) (fun j _=>h j);rw[Finset.sum_add_distrib,r,t] at l;norm_num at l
 obtain⟨j,m⟩:=g;obtain⟨k,z⟩:=o;have d:=e j;rw[b j] at d;have x:p j*(u j+v j)=0:=by linear_combination-d
 have a:=(mul_eq_zero.mp x).resolve_right m;have w:q j=0:=by simp[b,a]
 have s:=c j k;rw[a,w,b k] at s;have C:(u j-v j)*p k=0:=by linear_combination-s
 have f:=sub_eq_zero.mp ((mul_eq_zero.mp C).resolve_right z);refine⟨j,f,?_,a,w⟩;intro y;exact m (by simp[←f,y])
lemma dN (W:Submodule ℂ (aH×aH))
  (i:Module.finrank ℂ W=8) (f g:Module.Dual ℂ aH)
  (y:f 1=1) (N:g 1=1) (q:∀w∈W,f w.1=g w.2)
  (F:((1,1):aH×aH)∈W):
  ∃
   P Q:Module.Dual ℂ aH,P 1=0∧Q 1=0∧(P≠0∨Q≠0)∧
   ∀w,w∈W↔f w.1=g w.2∧P w.1= Q w.2:=by
 let d:Module.Dual ℂ (aH×aH):=f.comp (LinearMap.fst ℂ aH aH)-g.comp (LinearMap.snd ℂ aH aH)
 have M (w:aH×aH):d w=f w.1-g w.2:=rfl;have v:d≠0:=by intro h;have l:=LinearMap.congr_fun h ((1,0):aH×aH);simp[M,y] at l
 have C:Module.finrank ℂ (aH×aH)=10:=by norm_num[aH,Module.finrank_prod,Module.finrank_fintype_fun_eq_card]
 have k:Module.finrank ℂ (LinearMap.ker d)=9:=by have h:=Module.Dual.finrank_ker_add_one_of_ne_zero v;omega
 have m:W≤LinearMap.ker d:=by intro w b;exact LinearMap.mem_ker.mpr (sub_eq_zero.mpr (q w b))
 have z:W<LinearMap.ker d:=lt_of_le_of_ne m (by intro h;rw[h,k] at i;omega);obtain⟨x,p,B⟩:=IsConcreteLE.exists_of_lt z;obtain⟨H,o,E⟩:=Submodule.exists_dual_map_eq_bot_of_notMem B (inferInstance:Module.Projective ℂ _);have e (w:aH×aH) (b:w∈W):H w=0:=by
  have O:H w∈W.map H:=⟨w,b,rfl⟩
  simpa[E] using O
 let K:=LinearMap.ker d
 let Hk:Module.Dual ℂ K:=H.comp K.subtype
 have t:Hk≠0:=by intro h;exact o (LinearMap.congr_fun h (⟨x,p⟩:K))
 have j:Module.finrank ℂ (LinearMap.ker Hk)=8:=by have h:=Module.Dual.finrank_ker_add_one_of_ne_zero t;change Module.finrank ℂ (LinearMap.ker Hk)+1=Module.finrank ℂ (LinearMap.ker d) at h;omega
 have s:W.comap K.subtype=LinearMap.ker Hk:=by
  apply Submodule.eq_of_le_of_finrank_eq
  ·intro w b;exact LinearMap.mem_ker.mpr (e w b)
  ·rw[j,←i];exact(Submodule.comapSubtypeEquivOfLe m).finrank_eq
 let P₀:Module.Dual ℂ aH:=H.comp (LinearMap.inl ℂ aH aH)
 let Q₀:Module.Dual ℂ aH:= -(H.comp (LinearMap.inr ℂ aH aH))
 have c (w:aH×aH):P₀ w.1-Q₀ w.2=H w:=by change H (w.1,0)- -H (0,w.2)=H w;rw[sub_neg_eq_add,←map_add];congr 1;ext<;>simp
 let r:ℂ:=P₀ 1
 have R:Q₀ 1=r:=(sub_eq_zero.mp ((c (1,1)).trans (e (1,1) F))).symm
 let P:Module.Dual ℂ aH:=P₀-r•f
 let Q:Module.Dual ℂ aH:= Q₀-r•g
 have G:P 1=0:=by change P₀ 1-r*f 1=0;rw[y,mul_one,sub_self]
 have J:Q 1=0:=by change Q₀ 1-r*g 1=0;rw[N,mul_one,R,sub_self]
 have a (w:aH×aH) (b:f w.1=g w.2):
   P w.1-Q w.2=H w:=by
  change(P₀ w.1-r*f w.1)-(Q₀ w.2-r*g w.2)=H w;rw[b,sub_sub_sub_cancel_right,c]
 have u:P≠0∨Q≠0:=by by_contra! h;have l:=a x (sub_eq_zero.mp (LinearMap.mem_ker.mp p));rw[h.1,h.2] at l;exact o (by simpa using l.symm)
 refine⟨P,Q,G,J,u,fun w=>⟨?_,?_⟩⟩
 ·intro b;exact⟨q w b,sub_eq_zero.mp ((a w (q w b)).trans (e w b))⟩
 ·rintro⟨b,A⟩
  let S:K:=⟨w,LinearMap.mem_ker.mpr (sub_eq_zero.mpr b)⟩
  have n:S∈LinearMap.ker Hk:=LinearMap.mem_ker.mpr ((a w b).symm.trans (sub_eq_zero.mpr A));rw[←s] at n;exact n
def cR (f:Module.Dual ℂ aH):aH:=fun i=>f (Pi.single i 1)
lemma dI (f:Module.Dual ℂ aH) (x:aH):
  (∑j,cR f j*x j)=f x:=by
 have a:∑i,(x i)•(Pi.single i 1:aH)=x:=by funext k;simp[Finset.sum_apply,Pi.single_apply,mul_ite]
 conv_rhs=>rw[←a,map_sum]
 simp[cR,mul_comm]
lemma zH (f:Module.Dual ℂ aH):(∑j,cR f j)=f 1:=by simpa using dI f 1
end Ac.Ap
namespace Ac.Ap
open Aa Ac.Ae Finset
def bU (L:Submodule ℂ aC) (i j:Fin 4):Submodule ℂ (aH×aH):=L.map ((row i).prod (row j))⊔Submodule.span ℂ {((1,1):aH×aH)}
lemma jM {L:Submodule ℂ aC} (hL:aD L) (i:Fin 4):
  ∃f:Module.Dual ℂ aH,f 1=1∧∀t∈L,f (row i t)=0:=by
 apply Aa.lO L _ i;intro t a;rw[hL t a];norm_num
lemma gO {L:Submodule ℂ aC} (hL:aD L) (i j:Fin 4):
  Module.finrank ℂ (bU L i j)=p L i j+1:=by
 obtain⟨f,d,a⟩:=jM hL i;apply Submodule.finrank_sup_span_singleton;rintro⟨t,e,c⟩;have h:row i t=1:=congrArg Prod.fst c;have b:=a t e;rw[h,d] at b;exact one_ne_zero b
lemma gP {L:Submodule ℂ aC} {i j:Fin 4} {w:aH×aH}
  (d:w∈bU L i j):
  ∃s:ℂ,∃t∈L,row i (aM s t)=w.1∧row j (aM s t)=w.2:=by
 obtain⟨_,⟨t,b,rfl⟩,_,e,a⟩:=Submodule.mem_sup.mp d;obtain⟨s,rfl⟩:=Submodule.mem_span_singleton.mp e;refine⟨s,t,b,?_,?_⟩
 ·rw[←a];ext c;change s+t (i,c)=t (i,c)+s*1;ring
 ·rw[←a];ext c;change s+t (j,c)=t (j,c)+s*1;ring
lemma gZ {i:Fin 4} {f:Module.Dual ℂ aH} (d:f 1=1)
  {t:aC} (a:f (row i t)=0) (s:ℂ):
  f (row i (aM s t))=s:=by
 have b:row i (aM s t)=s•(1:aH)+row i t:=by funext c;change s+t (i,c)=s*1+t (i,c);ring
 simp[b,d,a]
lemma kM {L:Submodule ℂ aC} (hL:aD L)
  {i j:Fin 4} (O:i≠j) (hr:p L i j=7) (Z:Matrix F F ℂ)
  (X:∀k l,Z k l=Z l k) (K:∀k,Z k k=0)
  (hz:∀w∈bU L i j,bil w.1 w.2 Z=0):
  ∀k l,Z k l=0:=by
 classical
 let W:=bU L i j
 have E:Module.finrank ℂ W=8:=by rw[gO hL,hr]
 obtain⟨f,z,A⟩:=jM hL i;obtain⟨g,G,N⟩:=jM hL j;have hJ:((1,1):aH×aH)∈W:=by apply Submodule.mem_sup_right;exact Submodule.subset_span (Set.mem_singleton _)
 have d (w:aH×aH) (hw:w∈W):f w.1=g w.2:=by obtain⟨s,t,r,hi,hj⟩:=gP hw;rw[←hi,←hj,gZ z (A t r),gZ G (N t r)]
 obtain⟨P,Q,hP,hQ,_,J⟩:=dN W E f g z G d hJ
 let u:=cR f
 let v:=cR g
 let p:=cR P
 let q:=cR Q
 have hu:∑j,u j=1:=(zH f).trans z;have hv:∑j,v j=1:=(zH g).trans G;have R:∑j,p j=0:=(zH P).trans hP;have T:∑j,q j=0:=(zH Q).trans hQ;have C (x y:aH) (m:bv u x=bv v y) (n:bv p x=bv q y):(x,y)∈W:=
  (J (x,y)).mpr ⟨(dI f x).symm.trans (m.trans (dI g y)),
    (dI P x).symm.trans (n.trans (dI Q y))⟩
 rcases mJ Z u v p q hu hv R T X K (fun x y m n=>hz (x,y) (C x y m n)) with h|⟨hn,c,hc,he⟩
 ·exact h
 have kH (k):u k*q k-p k*v k=0:=(mul_eq_zero.mp ((he k k).symm.trans (K k))).resolve_left hc;have symm (k l):u k*q l-p k*v l=u l*q k-p l*v k:=mul_left_cancel₀ hc ((he k l).symm.trans ((X k l).trans (he l k)));obtain⟨k,hk,a1,S,U⟩:=nT u v p q hu hv R T hn kH symm
 let e:=cN k
 have M:(e,e)∈W:=C _ _ (by simpa[e,gY] using hk)
  (by simp[e,gY,S,U])
 obtain⟨s,t,r,B,V⟩:=gP M;have a0:f e=s:=(congrArg f B).symm.trans (gZ z (A t r) s);have H:s≠0:=by have ev:bv u e=f e:=dI f e;exact((gY u k).symm.trans (ev.trans a0))▸a1
 have o:=cD (aM s t) i j O (by
  intro a b hab;change row i (aM s t) a*row j (aM s t) b+row i (aM s t) b*row j (aM s t) a=0;rw[B,V];change cN k a*cN k b+cN k b*cN k a=0;by_cases ha:a=k
  ·subst a;simp[cN,hab.symm]
  ·simp[cN,ha])
 rw[bR hL r s] at o;exact False.elim ((mul_ne_zero (by norm_num:(120:ℂ)≠0) (pow_ne_zero 4 H)) o)
lemma mL {L:Submodule ℂ aC} (hL:aD L)
  (f:p L 2 3=7) {a b:aH} (c:bD a b 0 0∈L):
  ∀i j,dL a b i j=0:=by
 apply kM hL (by decide:(2:Fin 4)≠3) f (dL a b)
 ·intro i j;by_cases h:i=j
  ·subst j;rfl
  ·simp[dL,h,Ne.symm h,and_left_comm,and_comm,and_assoc]
 ·intro k;simp[dL]
 ·intro w l;obtain⟨s,t,g,d,e⟩:=gP l;rw[←d,←e];exact rR hL c ⟨t,g,rfl⟩
lemma fB {L:Submodule ℂ aC} (hL:aD L)
  (d:p L 2 3=7) {a b:aH} (c:bD a b 0 0∈L):
  ∀i j,i≠j→aL a b i j=0:=
 tD a b (fun i j _=>mL hL d c i j)
end Ac.Ap
namespace Ac.Ae
open Aa
abbrev aJ (L:Submodule ℂ aC) (i j:Fin 4):Submodule ℂ aC:=L⊓LinearMap.ker ((row i).prod (row j))
lemma oI {L:Submodule ℂ aC} {i j:Fin 4} {t:aC}:
  t∈aJ L i j↔t∈L∧row i t=0∧row j t=0:=by
 rw[Submodule.mem_inf,LinearMap.mem_ker];change t∈L∧(row i t,row j t)=(0,0)↔_;rw[Prod.mk.injEq]
lemma qV {L:Submodule ℂ aC} {i j:Fin 4}
  (a:aX L=8) (b:p L i j=7):
  aX (aJ L i j)=1:=by
 let f:=(row i).prod (row j)
 have h:p L i j+aX (aJ L i j)=aX L:=by
  change Module.finrank ℂ (L.map f)+Module.finrank ℂ (L⊓LinearMap.ker f:Submodule ℂ aC)=Module.finrank ℂ L;rw[←(Submodule.submoduleOfEquivInf _ _).finrank_eq,
   ←(f.submoduleMap L).finrank_range_add_finrank_ker,
   LinearMap.range_submoduleMap,LinearMap.ker_submoduleMap]
  simp
 omega
lemma oJ {L:Submodule ℂ aC} {i j:Fin 4}
  (e:aX L=8) (g:p L i j=7):
  ∃t∈aJ L i j,t≠0∧aJ L i j=Submodule.span ℂ {t}:=by
 have a:Module.finrank ℂ (aJ L i j)=1:=qV e g;have f:aJ L i j≠ ⊥ :=by intro d;rw[d,finrank_bot] at a;omega
 obtain⟨t,c,b⟩:=(Submodule.ne_bot_iff _).mp f;refine⟨t,c,b,(Submodule.eq_of_le_of_finrank_le ?_ ?_).symm⟩
 ·exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr c)
 ·rw[finrank_span_singleton b,a]
lemma iW {L:Submodule ℂ aC} {t:aC} {i:Fin 4}
  (b:u L i=0) (a:t∈L) (c:∀j,j≠i→ row j t=0):
  t=0:=by
 have h:t∈aZ L i:=by simp only[aZ,Submodule.mem_inf,Submodule.mem_iInf,LinearMap.mem_ker];exact⟨a,fun j=>c j.val j.property⟩
 rw[Submodule.finrank_eq_zero.mp b] at h;simpa only[Submodule.mem_bot] using h
lemma qW {L:Submodule ℂ aC} (hL:aD L)
  (s:aX L=8) (x:p L 2 3=7) (n:∀i,u L i=0)
  (w:∀t∈aJ L 2 3,∀i j:F,i≠j→
    aL (row 0 t) (row 1 t) i j=0):
  ∃
   a b:aH,bD a b 0 0≠0∧bD a b 0 0∈L∧
   aJ L 2 3=Submodule.span ℂ {bD a b 0 0}∧kS a b:=by
 obtain⟨t,m,f,o⟩:=oJ s x;obtain⟨e,c,d⟩:=oI.mp m;have v:bD (row 0 t) (row 1 t) 0 0=t:=by
  funext ⟨i,j⟩;fin_cases i
  ·rfl
  ·rfl
  ·exact(congrFun c j).symm
  ·exact(congrFun d j).symm
 have q:row 0 t≠0:=by
  intro k;apply f (iW (n 1) e ?_);intro i g;fin_cases i
  ·exact k
  ·exact(g rfl).elim
  ·exact c
  ·exact d
 have r:row 1 t≠0:=by
  intro l;apply f (iW (n 0) e ?_);intro i g;fin_cases i
  ·exact(g rfl).elim
  ·exact l
  ·exact c
  ·exact d
 have y:cS (row 0 t)+cS (row 1 t)=0:=by
  have h:=(Ac.Ad.cT hL e).1;rw[cW,Fin.sum_univ_four] at h;change cS (row 0 t)+cS (row 1 t)+cS (row 2 t)+cS (row 3 t)=0 at h;have z:cS (0:aH)=0:=by simp[cS]
  simpa only[c,d,z,add_zero] using h
 refine⟨row 0 t,row 1 t,?_,?_,?_,gN q r (w t m) y⟩<;>rw[v]<;>assumption
end Ac.Ae
namespace Ac.Ap
open Aa Ac.Ae
lemma lE {L:Submodule ℂ aC} (hL:aD L)
  (g:aX L=8) (f:p L 2 3=7) (k:∀i,u L i=0):
  ∃
   a b:aH,bD a b 0 0≠0∧bD a b 0 0∈L∧
   aJ L 2 3=Submodule.span ℂ {bD a b 0 0}∧kS a b:=by
 apply qW hL g f k;intro t j;obtain⟨l,d,e⟩:=oI.mp j;apply fB hL f;have h:bD (row 0 t) (row 1 t) 0 0=t:=by
  funext ⟨r,c⟩;fin_cases r
  ·rfl
  ·rfl
  ·exact(congrFun d c).symm
  ·exact(congrFun e c).symm
 rwa [h]
end Ac.Ap
namespace Ac.Ap
open Aa Ac.Ae
def bV (L:Submodule ℂ aC):Submodule ℂ aC:=L⊔Submodule.span ℂ {(1:aC)}
lemma zI {L:Submodule ℂ aC} {x:aC}:
  x∈bV L↔∃s,aR L x s:=by
 constructor
 ·intro c;obtain⟨t,b,y,d,rfl⟩:=Submodule.mem_sup.mp c;obtain⟨s,rfl⟩:=Submodule.mem_span_singleton.mp d;exact⟨s,t,b,by funext a;change t a+s*1=s+t a;ring⟩
 ·rintro⟨s,t,b,rfl⟩;apply Submodule.mem_sup.mpr;exact⟨t,b,s•(1:aC),Submodule.mem_span_singleton.mpr ⟨s,rfl⟩,by funext a;change t a+s*1=s+t a;ring⟩
lemma rS (L:Submodule ℂ aC) (i j:Fin 4):
  (bV L).map ((row i).prod (row j))=bU L i j:=by
 unfold bV bU;rw[Submodule.map_sup,Submodule.map_span,Set.image_singleton];rfl
end Ac.Ap
namespace Ac.Af
open Aa Finset Av
abbrev bI:=Fin 3×Fin 5→ℂ
def iX (i:Fin 4) (r:Fin 3):Fin 4:=Equiv.swap 0 i r.succ
def bH (i:Fin 4):aC→ₗ[ℂ] bI:=LinearMap.funLeft ℂ ℂ fun p=>(iX i p.1,p.2)
def U (L:Submodule ℂ aC) (i:Fin 4):Submodule ℂ aH:=(aZ L i).map (row i)
def W (L:Submodule ℂ aC) (i:Fin 4):Submodule ℂ bI:=Submodule.span ℂ {(1:bI)}⊔L.map (bH i)
def aA (v:bI) (r:Fin 3) (j:Fin 5):ℂ:=v (r,j)-(∑k,v (r,k))/2
def q (v:bI) (j:Fin 5):ℂ:=
 2
  *(aA v 0 j*aA v 1 j+aA v 0 j*aA v 2 j+
  aA v 1 j*aA v 2 j)
def G (v:bI) (j:Fin 5):ℂ:=G3 j (fun k=>v (0,k)) (fun k=>v (1,k)) (fun k=>v (2,k))
variable {L : Submodule ℂ aC}
lemma fN (L:Submodule ℂ aC) (i:Fin 4):1∈W L i:=Submodule.mem_sup_left (Submodule.subset_span (Set.mem_singleton _))
lemma aAu {i v}:
  v∈W L i↔∃s:ℂ,∃t∈L,v=s•1+bH i t:=by
 simp only[W,Submodule.mem_sup,Submodule.mem_span_singleton,Submodule.mem_map];grind
lemma aAv (i:Fin 4) (r:Fin 3):iX i r≠i:=by simpa[iX] using(Equiv.swap 0 i).injective.ne (Fin.succ_ne_zero r)
lemma aC3 {i d} (a:d∈aZ L i)
  {r:Fin 4} (b:r≠i) (j:Fin 5):d (r,j)=0:=by
 exact congrFun (show row r d=0 from(Submodule.mem_iInf _).mp a.2 ⟨r,b⟩) j
lemma oK {i d} (a:d∈aZ L i):
  eJ i (row i d)=d:=by
 funext ⟨r,j⟩;by_cases h:r=i<;>simp_all[eJ,row,aC3 a]
lemma uE {i w}:
  w∈U L i↔eJ i w∈L:=by
 constructor
 ·rintro⟨d,a,rfl⟩;rw[oK a];exact a.1
 ·intro h;refine⟨eJ i w,⟨h,?_⟩,?_⟩
  ·apply(Submodule.mem_iInf _).mpr;intro r;ext j;simp[row,eJ,r.2]
  ·ext j;simp[row,eJ]
lemma jN (i:Fin 4) (M:aC):
  aO M=∑j,M (i,j)*G (bH i M) j:=by
 rw[←yI (Equiv.swap 0 i) M,sX];simp only[Equiv.swap_apply_left];rfl
lemma jO (i:Fin 4) (s:ℂ) (d:aC):
  bH i (Ae.aM s d)=s•1+bH i d:=by
 funext p;simp[bH,Ae.aM]
lemma oL (hL:aD L) {i v}
  (b:v∈W L i):∃(s:ℂ) (x:aH),∀d:ℂ,
    (∑j,(d+x j)*G (d•(1:bI)+v) j)=120*(d+s)^4:=by
 obtain⟨s,t,a,rfl⟩:=aAu.mp b;refine⟨s,fun j=>s+t (i,j),fun d=> ?_⟩;rw[←Ae.bR hL a,jN i,jO,add_smul];simp[Ae.aM,add_assoc]
lemma dU (hL:aD L) {i w}
  (e:w∈U L i) {v} (d:v∈W L i):
  ∑j,w j*G v j=0:=by
 obtain⟨s,t,c,rfl⟩:=aAu.mp d;have b:=Ae.bR hL (L.add_mem c (uE.mp e)) s;have a:=Ae.bR hL c s;rw[jN i] at b a;have f:bH i (eJ i w)=0:=by funext p;simp[bH,eJ,aAv]
 simp only[jO,map_add,f,add_zero] at b a;simp only[Ae.aM,Pi.add_apply,eJ,ite_true] at b a;simp only[←add_assoc,add_mul,sum_add_distrib] at b;simp only[add_mul,sum_add_distrib] at a;linear_combination b-a
lemma lR (hL:aD L) {i w}
  (a:w∈U L i):∑j,w j=0:=by
 have h:=dU hL a (fN L i);simp only[G,Pi.one_apply,aBs,←sum_mul] at h;linear_combination h/24
lemma aHe (j:Fin 5):q 1 j=27/2:=by norm_num[q,aA]
lemma hO (hL:aD L) {i w}
  (a:w∈U L i) {v} (b:v∈W L i):
  ∑j,w j*q v j=0:=by
 let f (c:ℂ):=G (1+c•v)
 let D j:=f 1 j+f (-1) j-q v j*4
 have K (j):D j=D 0:=by simp only[D,f,G,Pi.add_apply,Pi.one_apply,Pi.smul_apply,smul_eq_mul,aEm,Q2,q,aA];ring
 have E (c:ℂ):∑j,w j*f c j=0:=dU hL a ((W L i).add_mem (fN _ _) ((W L i).smul_mem c b));have Z:∑j,w j*D j=0:=by simp_rw[K,←sum_mul,lR hL a,zero_mul]
 simp only[D,mul_sub,mul_add,←mul_assoc,sum_sub_distrib,sum_add_distrib,←sum_mul,E] at Z;linear_combination-Z/4
lemma rT (hL:aD L) (i:Fin 4):
  (1:bI)∉L.map (bH i):=by
 rintro⟨t,b,a⟩;have z:=Ae.bR hL (L.neg_mem b) 1;rw[jN i,jO,map_neg,a] at z;norm_num[G,G3] at z
lemma aAw (L:Submodule ℂ aC) (i:Fin 4):
  L⊓LinearMap.ker (bH i)=aZ L i:=by
 ext t;constructor
 ·rintro⟨d,f⟩;refine⟨d,(Submodule.mem_iInf _).mpr ?_⟩;intro r;have c:∀(a b:Fin 4),b≠a→∃k:Fin 3,iX a k=b:=by
   decide
  obtain⟨k,e⟩:=c i r r.2;ext j;exact e▸(show t (iX i k,j)=0 from congrFun (show bH i t=0 from f) (k,j))
 ·intro d;exact⟨d.1,funext fun p=>aC3 d (aAv i p.1) p.2⟩
lemma tE (L:Submodule ℂ aC) (i:Fin 4):
  Module.finrank ℂ (U L i)=u L i:=by
 rw[U,←LinearMap.range_domRestrict];apply LinearMap.finrank_range_of_inj;intro a b hab;exact Subtype.ext ((oK a.2).symm.trans ((congrArg (eJ i) hab).trans (oK b.2)))
lemma uF {D E:Type*} [AddCommGroup D] [Module ℂ D] [Module.Finite ℂ D]
  [AddCommGroup E] [Module ℂ E] (f:D→ₗ[ℂ] E) (L:Submodule ℂ D):
  Module.finrank ℂ (L.map f)+Module.finrank ℂ (L⊓f.ker:Submodule ℂ D)=Module.finrank ℂ L:=by
 rw[←(Submodule.submoduleOfEquivInf _ _).finrank_eq,
  ←(f.submoduleMap L).finrank_range_add_finrank_ker,
  LinearMap.range_submoduleMap,LinearMap.ker_submoduleMap]
 simp
lemma jP (hL:aD L) (i:Fin 4):
  Module.finrank ℂ (W L i)+u L i=aX L+1:=by
 rw[W,sup_comm,Submodule.finrank_sup_span_singleton (rT hL i),Nat.add_right_comm];congr 1;have H:=uF (bH i) L;rw[aAw] at H;exact H
def eQ (P:Submodule ℂ aH):Submodule ℂ aH:=P.dualAnnihilator.comap (dotProductEquiv ℂ (Fin 5)).toLinearMap
lemma eK {P:Submodule ℂ aH} {z:aH}:
  z∈eQ P↔∀w∈P,∑j,w j*z j=0:=by
 unfold eQ;rw[Submodule.mem_comap,Submodule.mem_dualAnnihilator];change(∀w∈P,∑j,z j*w j=0)↔_;simp_rw[mul_comm (z _)]
lemma mM (P:Submodule ℂ aH):
  Module.finrank ℂ (eQ P)+Module.finrank ℂ P=5:=by
 rw[eQ,Submodule.comap_equiv_eq_map_symm,LinearEquiv.finrank_map_eq,add_comm,Subspace.finrank_add_finrank_dualAnnihilator_eq,Module.finrank_fin_fun]
lemma oM (hL:aD L) {i}:
  1
   ∈eQ (U L i)∧∀v∈W L i,
   G v∈eQ (U L i)∧q v∈eQ (U L i):=by
 simp only[eK,Pi.one_apply,mul_one];exact⟨fun _=>lR hL,fun _ b=>⟨fun _ a=>dU hL a b,fun _ a=>hO hL a b⟩⟩
lemma qX (P:Submodule ℂ aH) (p:Module.finrank ℂ P=2)
  (e:(1:aH)∈P):
  ∃
   (η:aH) (a b:Fin 5),η∈P∧η a=0∧η b=1∧
   ∀f∈P,∀j,f j=f a+η j*(f b-f a):=by
 let I:=Submodule.span ℂ {(1:aH)}
 have g {z:aH}:=(Submodule.span_singleton_le_iff_mem z P).mpr;have k:I≤P:=g e;have n:Module.finrank ℂ I=1:=finrank_span_singleton one_ne_zero;obtain⟨z,m,l⟩:=IsConcreteLE.exists_of_lt (lt_of_le_of_ne k (by rintro rfl;omega));obtain⟨b,i⟩:∃j,z j≠z 0:=by by_contra! h;exact l (Submodule.mem_span_singleton.mpr ⟨z 0,funext fun j=>by simp[h j]⟩)
 have o:I⊔Submodule.span ℂ {z}=P:=
  Submodule.eq_of_le_of_finrank_eq (sup_le k (g m))
   (by rw[Submodule.finrank_sup_span_singleton l,n,p])
 refine⟨(z b-z 0)⁻¹ •(z-z 0•1),0,b,P.smul_mem _ (P.sub_mem m (P.smul_mem _ e)),by simp,by simp[sub_ne_zero.mpr i],?_⟩;simp only[←o,Submodule.mem_sup,I,Submodule.mem_span_singleton];rintro _ ⟨_,⟨c,rfl⟩,_,⟨d,rfl⟩,rfl⟩ j;simp;field_simp[sub_ne_zero.mpr i];ring
def jF (h:Fin 3→ℂ) (p:aH):bI:=fun a=>h a.1*p a.2
def vX (p:aH):ℂ:=∑a,∑b,∑c,if a<b∧b<c then p a*p b*p c else 0
lemma aAx (p:aH):∑j,G3 j p p p=12*vX p:=by simp(config:={decide:=true}) only[G3,vX,Fin.sum_univ_five,ite_true,ite_false,zero_add,add_zero];ring
lemma vY (hL:aD L) {i h p} (f:jF h p∈W L i)
  (l:h 0+h 1+h 2=0) (m:h 0*h 1+h 0*h 2+h 1*h 2=0)
  (e:h 0*h 1*h 2≠0):vX p=0:=by
 obtain⟨s,b,E⟩:=oL hL f
 let g (j:Fin 5):=(h 0*h 1*h 2)*G3 j p p p
 have a (d:ℂ):120*d^4+(∑j,b j)*(24*d^3)+d*(∑j,g j)+
   (∑j,b j*g j)=120*(d+s)^4:=by
  have k (j):G (d•1+jF h p) j=24*d^3+g j:=by simp[G,jF,g,cJ,Fin.sum_univ_five];grind
  rw[←E];simp only[k,add_mul,mul_add,sum_add_distrib,←mul_sum,←sum_mul];simp;ring
 obtain rfl:s=0:=by apply sq_eq_zero_iff.mp;linear_combination(a 2+a (-2)-16*(a 1+a (-1))+30*a 0)/17280
 have c:(∑j,g j)=0:=by linear_combination(8*(a 1-a (-1))-a 2+a (-2))/12
 simpa[g,←mul_sum,aAx,e] using c
def rU (j:Fin 5):aH:=fun k=>(if k=j then 1 else 0)-1/3
lemma aBy (j:Fin 5):vX (rU j)=8/27:=by fin_cases j<;>norm_num[vX,rU,Fin.sum_univ_five]
lemma iS (v:bI) (r:Fin 3) (j:Fin 5):
  aA (1+v) r j= -(3/2:ℂ)+aA v r j:=by
 simp[aA,sum_add_distrib];ring
def aV (v:bI) (j:Fin 5):ℂ:=aA v 0 j+aA v 1 j+aA v 2 j
lemma eR (hL:aD L) {i w}
  (a:w∈U L i) {v} (c:v∈W L i):
  ∑j,w j*aV v j=0:=by
 have b (j):w j*q (1+v) j=
   w j*(27/2)+w j*q v j-(w j*aV v j)*6:=by
  simp only[q,aV,iS];ring
 have E:=hO hL a ((W L i).add_mem (fN _ _) c);simp_rw[b] at E;rw[sum_sub_distrib,sum_add_distrib,←sum_mul,lR hL a,hO hL a c,←sum_mul] at E;linear_combination-E/6
lemma gS (h:Fin 3→ℂ) (j k:Fin 5) (r:Fin 3):
  aA (jF h (rU j)) r k=if k=j then h r else 0:=by
 simp only[aA,jF,rU,←mul_sum,sum_sub_distrib];simp
 split<;>ring
lemma tF (hL:aD L) {i w}
  (b:w∈U L i) {j} (c:w j≠0) {h}
  (a:jF h (rU j)∈W L i):h=0:=by
 have A:=eR hL b a;have B:=hO hL b a;simp[aV,q,gS,ite_add_ite,mul_ite,c] at A B;have P:h 0*h 1*h 2=0:=by by_contra d;have H:=vY hL a A B d;norm_num[aBy] at H
 funext r;fin_cases r<;>simp only[Pi.zero_apply]<;>grind
end Ac.Af
namespace Ac.Af
open Aa Finset
variable {L : Submodule ℂ aC}
abbrev cI (n:ℕ):=Fin n×Fin 3→ℂ
def qH {n:ℕ} (x:cI n) (j:Fin n):=2*(x (j,0)*x (j,1)+x (j,0)*x (j,2)+x (j,1)*x (j,2))
def qU {n:ℕ} (a:Fin n→ℂ):cI n→ₗ[ℂ] cI n where
 toFun x b:=a b.1*((∑r,x (b.1,r))-x b)
 map_add' x y:=by funext b;simp[sum_add_distrib];ring
 map_smul' c x:=by funext b;simp[←mul_sum];ring
lemma eS {n:ℕ} (a:Fin n→ℂ) (l:∀j,a j≠0)
  (P:Submodule ℂ (cI n)) (b:∀x∈P,∑j,a j*qH x j=0):
  2*Module.finrank ℂ P≤3*n:=by
 let F:=(dotProductEquiv ℂ (Fin n×Fin 3)).toLinearMap.comp (qU a)
 have k:Function.Injective (qU a):=by apply(injective_iff_map_eq_zero _).2;intro x c;funext ⟨j,r⟩;have E (s):(∑t,x (j,t))-x (j,s)=0:=(mul_eq_zero.mp (show a j*_=0 from congrFun c (j,s))).resolve_left (l j);simp only[Fin.sum_univ_three] at E;change x (j,r)=0;linear_combination(E 0+E 1+E 2)/2-E r
 have f:P.map F≤P.dualAnnihilator:=by
  rintro _ ⟨x,c,rfl⟩;apply(Submodule.mem_dualAnnihilator _).mpr;intro y g;have e (j):2*(∑r,(qU a x) (j,r)*y (j,r))=
    a j*qH (x+y) j-a j*qH x j-a j*qH y j:=by
   simp[qH,qU,Fin.sum_univ_three];ring
  change ∑i,(qU a x) i*y i=0;rw[Fintype.sum_prod_type];have h:=sum_congr (s₁:=univ) rfl (fun j _=>e j);rw[←mul_sum,sum_sub_distrib,sum_sub_distrib,b _ (P.add_mem c g),b _ c,b _ g] at h;linear_combination h/2
 have h:=Submodule.finrank_mono f;rw[←(Submodule.equivMapOfInjective F ((dotProductEquiv ℂ _).injective.comp k) P).finrank_eq] at h;have d:=Subspace.finrank_add_finrank_dualAnnihilator_eq P;rw[two_mul,Nat.mul_comm];exact(Nat.add_le_add_left h _).trans (by rw[d];simp[cI])
def jQ (j:Fin 5):bI→ₗ[ℂ] cI 4 where
 toFun v p:=aA v p.2 (j.succAbove p.1)
 map_add' v v':=by funext p;simp[aA,sum_add_distrib];ring
 map_smul' c v:=by funext p;simp[aA,←mul_sum];ring
lemma yK (hL:aD L) {i w}
  (d:w∈U L i) {j:Fin 5} (a:w j=0) (b:∀k≠j,w k≠0):
  Module.finrank ℂ ((W L i).map (jQ j))≤6:=by
 have e:=eS (n:=4) (fun k=>w (j.succAbove k))
  (fun k=>b _ (Fin.succAbove_ne j k)) ((W L i).map (jQ j)) (by
    rintro _ ⟨v,c,rfl⟩;have H:=hO hL d c;rw[Fin.sum_univ_succAbove _ j,a,zero_mul,zero_add] at H;exact H)
 omega
lemma cQ (v:bI) (r:Fin 3) (j:Fin 5):
  v (r,j)=aA v r j-(∑k,aA v r k)/3:=by
 simp[aA,sum_sub_distrib];ring
lemma aE0 {v w:bI} (h:∀r k,aA v r k=aA w r k):v=w:=by funext ⟨r,k⟩;rw[cQ v,cQ w];simp only[h]
lemma fI {v:bI} {j:Fin 5} (b:jQ j v=0):
  v=jF (fun r=>aA v r j) (rU j):=by
 apply aE0;intro r k;rw[gS]
 split_ifs with hk
 ·rw[hk]
 ·obtain⟨a,rfl⟩:k∈Set.range j.succAbove:=by simpa using hk
  exact congrFun b (a,r)
lemma gJ (hL:aD L) {i w}
  (b:w∈U L i) {j:Fin 5} (a:w j≠0):
  Function.Injective ((jQ j).domRestrict (W L i)):=by
 apply(injective_iff_map_eq_zero _).2;intro v c;have h:=fI (show jQ j v.val=0 from c);apply Subtype.ext;have z:=tF hL b a (show jF (fun r=>aA v.val r j) (rU j)∈W L i from h▸v.2);rw[h,z];ext;simp[jF]
lemma lS (hL:aD L) (g:aX L=8)
  {i:Fin 4} (f:u L i=2) {w:aH} (d:w∈U L i) {j:Fin 5}
  (a:w j=0) (c:∀k≠j,w k≠0):
  ∀y∈U L i,y j=0:=by
 intro y e;by_contra b;have D:=LinearMap.finrank_range_of_inj (gJ hL e b);rw[LinearMap.range_domRestrict] at D;have R:=jP hL i;have B:=yK hL d a c;omega
def aK (A:Finset (Fin 5)):bI→ₗ[ℂ] cI A.card where
 toFun v p:=aA v p.2 (A.equivFin.symm p.1).val
 map_add' v v':=by funext p;simp[aA,sum_add_distrib];ring
 map_smul' c v:=by funext p;simp[aA,←mul_sum];ring
lemma aC4 {w:aH} {S:Submodule ℂ bI} {A:Finset (Fin 5)}
  (a:∀k∈A,w k≠0) (h:∀v∈S,∑k∈A,w k*q v k=0):
  2*Module.finrank ℂ (S.map (aK A))≤3*A.card:=by
 apply eS (fun k=>w (A.equivFin.symm k).val) (fun k=>a _ (A.equivFin.symm k).2);rintro _ ⟨v,b,rfl⟩;change ∑k,w (A.equivFin.symm k).val*q v (A.equivFin.symm k).val=0;rw[A.equivFin.symm.sum_comp (fun k=>w k.val*q v k.val),sum_coe_sort A (fun k=>w k*q v k)];exact h v b
lemma dO (hL:aD L) {i w}
  (d:w∈U L i) (A:Finset (Fin 5)) (a:∀k,w k≠0↔k∈A):
  2*Module.finrank ℂ ((W L i).map (aK A))≤3*A.card:=by
 apply aC4 (fun k=>(a k).2);intro v c;rw[←hO hL d c];exact sum_subset (subset_univ _) fun k _ b=>by simp[not_ne_iff.mp (b∘(a k).1)]
lemma mN {A:Finset (Fin 5)} {x y:bI}
  (h:aK A x=aK A y) {k:Fin 5} (a:k∈A) (r:Fin 3):
  aA x r k=aA y r k:=by
 have e:=congrFun h (A.equivFin ⟨k,a⟩,r);simpa[aK] using e
lemma aAy {A:Finset (Fin 5)} {x y:bI}
  (b:aK A x=aK A y) (c:aK Aᶜ x=aK Aᶜ y):x=y:=by
 apply aE0;intro r k;by_cases a:k∈A
 ·exact mN b a r
 ·exact mN c (mem_compl.mpr a) r
lemma vZ (P:Submodule ℂ bI) (A:Finset (Fin 5))
  (c:Module.finrank ℂ (P.map (aK A))+Module.finrank ℂ (P.map (aK Aᶜ))
    ≤Module.finrank ℂ P) {x:bI}
  (e:aK A x∈P.map (aK A)) (g:aK Aᶜ x∈P.map (aK Aᶜ)):
  x∈P:=by
 let F:=((aK A).submoduleMap P).prod ((aK Aᶜ).submoduleMap P)
 have a:Function.Injective F:=fun _ _ h=>Subtype.ext (aAy congr($h.1.1) congr($h.2.1))
 have b:=LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f:=F) (by have d:=LinearMap.finrank_le_finrank_of_injective a;rw[Module.finrank_prod] at d ⊢;exact d.antisymm c) |>.mp a
 obtain⟨z,h⟩:=b (⟨_,e⟩,⟨_,g⟩);exact(aAy congr($h.1.1) congr($h.2.1):z.val=x)▸z.2
lemma kN (hL:aD L) {i}
  (h:Module.finrank ℂ (W L i)=7) {a b:Fin 5} (hab:a≠b)
  {u v:aH} (d:u∈U L i) (e:v∈U L i)
  (Su:∀k,u k≠0↔k=a∨k=b) (Sv:∀k,v k≠0↔k≠a∧k≠b):
  (fun p:Fin 3×Fin 5=>if p.2=a∨p.2=b then(1:ℂ) else 0)∈W L i:=by
 let A:Finset (Fin 5):={a,b}
 let X:bI:=fun p=>if p.2∈A then 1 else 0
 have c:A.card=2:=by simp[A,hab]
 have j:Aᶜ.card=3:=by simp[card_compl,c]
 have f:=dO hL d A (fun k=>by simpa[A] using Su k);have g:=dO hL e Aᶜ (fun k=>by simpa[A,not_or] using Sv k);have ca (r:Fin 3) (k:Fin 5):aA X r k=(if k∈A then 1 else 0)-1:=by simp[aA,X,c,sum_ite_mem]
 suffices X∈W L i by simpa[X,A] using this
 apply vZ _ A (by omega)
 ·refine⟨0,Submodule.zero_mem _,?_⟩;funext ⟨k,r⟩;change aA 0 r _=aA X r _;rw[ca];simp[(A.equivFin.symm k).2,aA]
 ·refine⟨_,(W L i).smul_mem (2/3:ℂ) (fN _ _),?_⟩;funext ⟨k,r⟩;change aA _ r _=aA X r _;rw[ca];norm_num[mem_compl.mp (Aᶜ.equivFin.symm k).2,aA]
lemma kT (P:Submodule ℂ aH) (N:Module.finrank ℂ P=2)
  (S:Finset (Fin 5)) (O:S.Nonempty)
  (n:∀j,j∈S↔∃x:P,x.val j≠0)
  (F:∀(x:P),∀j∈S,x.val j=0→∃k∈S,k≠j∧x.val k=0):
  ∃
   A⊆S,A.card=2∧∃u v:P,
   (∀k,u.val k≠0↔k∈A)∧(∀k,v.val k≠0↔k∈S \ A):=by
 classical
 let f (j:Fin 5):=(LinearMap.proj j:aH→ₗ[ℂ] ℂ).domRestrict P
 let K (j:Fin 5):=LinearMap.ker (f j)
 have g (j) (c:j∈S):IsAtom (K j):=by
  obtain⟨x,m⟩:=(n j).mp c;have U:f j≠0:=fun e=>m (DFunLike.congr_fun e x)
  have e:=Module.Dual.finrank_ker_add_one_of_ne_zero U;apply Submodule.isAtom_iff_finrank_eq_one.mpr;exact Nat.add_right_cancel (e.trans N)
 have i (p) (d:p∈S.image K):∃x:P,x≠0∧
   ∀k,x.val k≠0↔k∈S∧K k≠p:=by
  obtain⟨j,c,rfl⟩:=mem_image.mp d;obtain⟨w,T,G⟩:=(K j).ne_bot_iff.mp (g j c).ne_bot;refine⟨w,G,fun k=>⟨fun r=>⟨(n k).mpr ⟨_,r⟩,fun e=>r (show w∈K k by rwa [e])⟩,?_⟩⟩;rintro⟨l,s⟩ B;exact G (Submodule.disjoint_def.mp ((g k l).disjoint_of_ne (g j c) s) w B T)
 have C (p) (d:p∈S.image K):2≤(S.filter (fun k=>K k=p)).card:=by obtain⟨x,_,m⟩:=i p d;obtain⟨j,c,rfl⟩:=mem_image.mp d;obtain⟨k,l,o,B⟩:=F x j c (not_ne_iff.mp (by simp[m]));exact one_lt_card.mpr ⟨k,by simp[l];grind,j,by simp[c],o⟩
 have H:=mul_card_image_le_card S 2 C;have size:S.card≤5:=(card_le_univ S).trans_eq (Fintype.card_fin 5);obtain⟨t,z⟩:=O.image K;obtain⟨x,V,m⟩:=i t z;obtain⟨j,c⟩:∃j,x.val j≠0:=by by_contra! h;exact V (Subtype.ext (funext h))
 have h:=(m j).mp c;have E:=one_lt_card.mpr ⟨_,mem_image_of_mem K h.1,_,z,h.2⟩;obtain⟨p,d,J⟩:=exists_card_fiber_lt_of_card_lt_mul (f:=K)
  (show S.card<(S.image K).card*3 by omega)
 have Z:=C p d;obtain⟨v,_,R⟩:=i p d;obtain⟨q,y,X⟩:=exists_mem_ne E p;obtain⟨u,_,Q⟩:=i q y;obtain⟨a,b,_,cG⟩:=card_eq_two.mp (show(S.image K).card=2 by omega);refine⟨_,filter_subset (fun k=>K k=p) S,by omega,u,v,fun k=> ?_,fun k=> ?_⟩
 ·have M (l:k∈S):=mem_image_of_mem K l;simp only[cG,mem_insert,mem_singleton] at M d y;simp only[Q,mem_filter];grind
 ·simp[R];tauto
lemma iY (hL:aD L) {i}
  {a b} (hab:a≠b):
  (fun p:Fin 3×Fin 5=>if p.2=a∨p.2=b then(1:ℂ) else 0)∉W L i:=by
 let A:Finset (Fin 5):={a,b}
 let v:bI:=fun p=>if p.2∈A then 1 else 0
 have c:A.card=2:=by simp[A,hab]
 have l:Aᶜ.card=3:=by simp[card_compl,c]
 intro m;obtain⟨s,x,H⟩:=oL hL (show v∈W L i by simpa[v,A] using m)
 let t (d:ℂ) (k:Fin 5):=d+if k∈A then 1 else 0
 have h (f:ℂ→ℂ) (d:ℂ):(∑k,f (t d k))=2*f (d+1)+3*f d:=by rw[←sum_add_sum_compl A];simp+contextual [t,c,l,mem_compl.mp]
 have g (d:ℂ) (j:Fin 5):G (d•1+v) j=
   if j∈A then 6*(d^3+3*d^2*(d+1)) else 6*(2*d^2*(d+1)+2*d*(d+1)^2):=by
  have e (r:Fin 3) (k:Fin 5):(d•(1:bI)+v) (r,k)=t d k:=by simp[t,v]
  simp only[G,e,Av.cJ];simp only[h (fun z=>z) d,h (fun z=>z*z) d,h (fun z=>z*z*z) d];dsimp[t];split_ifs<;>ring
 have K (d:ℂ):=H d;simp_rw[g,mul_ite,sum_ite] at K;simp[sum_add_distrib,add_mul,←sum_mul,filter_notMem_eq_sdiff,card_sdiff_of_subset,c] at K;obtain rfl:s=0:=by simpa using(K 0).symm
 apply one_ne_zero (α:=ℂ);linear_combination(K 2-5*K 1+9*K (-1))/(-576)
lemma rV (hL:aD L) (f:aX L=8)
  {i:Fin 4} (d:u L i=2):∃j:Fin 5,∀w∈U L i,w j=0:=by
 by_contra! c;obtain⟨A,_,e,u,v,m,n⟩:=kT _ ((tE L i).trans d)
  Finset.univ Finset.univ_nonempty (fun j=>by simpa using c j) (by intro x j _ l;obtain⟨y,k,g⟩:=c j;by_contra! h;exact g (lS hL f d x.2 l (by simpa using h) y k))
 obtain⟨a,b,hab,rfl⟩:=Finset.card_eq_two.mp e;have o:=jP hL i;exact iY hL (i:=i) hab (kN hL (by omega)
  hab u.2 v.2 (by simpa using m) (by simpa[not_or] using n))
def jG (j:Fin 5):(Fin 3→ℂ)→ₗ[ℂ] bI where
 toFun h:=jF h (rU j)
 map_add' h g:=by funext p;simp[jF,add_mul]
 map_smul' c h:=by funext p;simp[jF,mul_assoc]
def eL (L:Submodule ℂ aC) (i:Fin 4) (j:Fin 5):Submodule ℂ (Fin 3→ℂ):=(W L i).comap (jG j)
lemma aAz {M:aC} (a:aO M≠0):∃f:Fin 4 ↪ Fin 5,∀r,M (r,f r)≠0:=by by_contra! h;exact a (sum_eq_zero fun e _=>by obtain⟨i,b⟩:=h e;exact prod_eq_zero (mem_univ i) b)
lemma fC (hL:aD L) {i} {v}
  (d:v∈W L i) {r:Fin 3} (e:∀k,v (r,k)=0):v∈L.map (bH i):=by
 obtain⟨s,t,a,rfl⟩:=aAu.mp d
 suffices s=0 by exact⟨t,a,by simp[this]⟩
 by_contra c;obtain⟨f,b⟩:=aAz (M:=Ae.aM s t) (by simp[Ae.bR hL a,c]);exact b (iX i r) (by simpa[bH,Ae.aM] using e (f (iX i r)))
lemma kU (hL:aD L) {i} {v}
  (m:v∈L.map (bH i)) {j:Fin 5} {r s:Fin 3} (b:r≠s)
  (e:∀k≠j,1+v (r,k)=0) (g:∀k≠j,1+v (s,k)=0):False:=by
 obtain⟨t,l,rfl⟩:=m;obtain⟨f,c⟩:=aAz (M:=1+t) (by rw[hL t l];norm_num);have a (r) (h:∀k≠j,1+bH i t (r,k)=0):f (iX i r)=j:=Classical.byContradiction fun d=>c _ (h _ d)
 exact b (Fin.succ_injective _ ((Equiv.swap 0 i).injective
  (f.injective ((a _ e).trans (a _ g).symm))))
lemma aA0 (hL:aD L) {i} {j}
  {b c} (e:b∈eL L i j) (f:c∈eL L i j) (r s:Fin 3):
  b r*c s-b s*c r=0:=by
 by_contra h;have m:r≠s:=by rintro rfl;simp at h
 have a {b c:Fin 3→ℂ} (e:b∈eL L i j) (f:c∈eL L i j)
   (r s) (d:b r*c s-b s*c r≠0):
   ∃x,jF x (rU j)∈L.map (bH i)∧x r=3∧x s=0:=by
  let x:=(3/(b r*c s-b s*c r))•(c s•b-b s•c)
  let P:=eL L i j
  have l:x∈P:=P.smul_mem _ (P.sub_mem (P.smul_mem _ e) (P.smul_mem _ f));have g:x s=0:=by simp[x,mul_comm (c s)]
  refine⟨x,fC hL (show jF x (rU j)∈W L i from l)
   (r:=s) (fun k=>by simp[jF,g]),?_,g⟩
  simp[x,mul_comm (c s) (b r),d]
 obtain⟨x,l,p,g⟩:=a e f r s h;obtain⟨y,o,t,q⟩:=a f e s r (by simpa[mul_comm] using h);apply kU hL ((L.map (bH i)).add_mem l o) (j:=j) m<;>intro k n<;>simp[jF,rU,n,p,q,g,t]
lemma tG (hL:aD L) (i:Fin 4) (j:Fin 5):
  Module.finrank ℂ (eL L i j)≤1:=by
 let P:=eL L i j
 by_cases h:P= ⊥
 ·change Module.finrank ℂ P≤1;rw[h,finrank_bot];decide
 obtain⟨b,a,c⟩:=Submodule.exists_mem_ne_zero_of_ne_bot h;obtain⟨r,f⟩:∃r,b r≠0:=by by_contra! d;exact c (funext d)
 apply finrank_le_one (⟨b,a⟩:P);intro x;refine⟨x.val r/b r,Subtype.ext (funext fun s=> ?_)⟩;change x.val r/b r*b s=x.val s;have e:=aA0 hL a x.2 r s;field_simp;linear_combination-e
def aA1 (j:Fin 5):bI→ₗ[ℂ] (Fin 3→ℂ) where
 toFun v r:=aA v r j
 map_add' _ _:=by funext;simp[aA,sum_add_distrib];ring
 map_smul' _ _:=by funext;simp[aA,←mul_sum];ring
lemma fJ (hL:aD L) (i:Fin 4) (j:Fin 5):
  Module.finrank ℂ (W L i⊓LinearMap.ker (jQ j):Submodule ℂ bI)≤1:=by
 let K:=W L i⊓LinearMap.ker (jQ j)
 let f:=((aA1 j).domRestrict K).codRestrict (eL L i j) fun z=>show jF (fun r=>aA z.val r j) (rU j)∈W L i from fI z.2.2▸z.2.1
 apply le_trans _ (tG hL i j);apply LinearMap.finrank_le_finrank_of_injective (f:=f);intro x y h;exact Subtype.ext ((fI x.2.2).trans
  ((congrArg (fun c=>jF c (rU j)) congr($h.1)).trans (fI y.2.2).symm))
lemma cX {n:ℕ} (S:Submodule ℂ bI) (F:bI→ₗ[ℂ] cI n):
  Module.finrank ℂ (S.map F)+Module.finrank ℂ (S⊓LinearMap.ker F:Submodule ℂ bI)=Module.finrank ℂ S:=by
 exact uF F S
lemma rW (hL:aD L) (K:aX L=8)
  {i:Fin 4} (J:u L i=2) {m j:Fin 5} (g:m≠j)
  (s:∀w∈U L i,w m=0) {y:aH} (l:y∈U L i) (n:y j≠0)
  {w:aH} (t:w∈U L i) (v:w j=0):
  ¬(∀k,k≠m→k≠j→w k≠0):=by
 intro M
 let A:Finset (Fin 5):=({m,j}:Finset (Fin 5))ᶜ
 let B:Finset (Fin 5):={j}
 let P:=W L i
 let Z:=P⊓LinearMap.ker (aK A)
 have F:A.card=3:=by simp[A,card_compl,g]
 have G:B.card=1:=by simp[B]
 have f:∀k,w k≠0↔k∈A:=by intro k;simp[A];grind
 have x:=dO hL t A f;have a (C:Finset (Fin 5)) {z:bI} (b:z∈LinearMap.ker (aK C)) {k}
   (c:k∈C) (r):aA z r k=0:=by
  have e:aK C z=aK C 0:=by rw[map_zero];exact b
  simpa[aA] using mN e c r
 have E:2*Module.finrank ℂ (Z.map (aK B))≤3*B.card:=by
  apply aC4 (w:=y) (by simpa[B] using n);intro z b;rw[←hO hL l b.1];apply sum_subset (subset_univ _);intro k _ c;by_cases e:k=m
  ·simp[e,s y l]
  ·have o:k∈A:=by simpa[A,not_or] using And.intro e (show k≠j by simpa[B] using c)
   simp[q,a A b.2 o]
 have d:Z⊓LinearMap.ker (aK B)≤P⊓LinearMap.ker (jQ m):=by
  rintro z ⟨b,p⟩;refine⟨b.1,?_⟩;ext ⟨k,r⟩;have c:=Fin.succAbove_ne m k;by_cases h:m.succAbove k=j
  ·exact a B p (mem_singleton.mpr h) r
  ·exact a A b.2 (by simp[A,c,h]) r
 have d3:=(Submodule.finrank_mono d).trans (fJ hL i m);have N:=cX P (aK A);have O:=cX Z (aK B);have H:=jP hL i;dsimp only[P,Z] at*
 omega
def bJ (A:Finset (Fin 5)):Submodule ℂ aH:=by
 refine{
          carrier:={x | (∑j,x j)=0∧∀j∉A,x j=0},
          zero_mem':=by simp,add_mem':= ?_,smul_mem':= ?_}
 ·rintro a b ⟨d,e⟩ ⟨f,g⟩;exact⟨by simp[sum_add_distrib,d,f],fun j h=>by simp[e j h,g j h]⟩
 ·rintro c a ⟨d,e⟩;exact⟨by simp[←mul_sum,d],fun j h=>by simp[e j h]⟩
lemma jR (A:Finset (Fin 5)) (c:A.Nonempty):
  Module.finrank ℂ (bJ A)≤A.card-1:=by
 obtain⟨a,d⟩:=c
 let f:=(LinearMap.funLeft ℂ ℂ (fun j:A.erase a=>j.val)).domRestrict (bJ A)
 suffices Function.Injective f by
  simpa only[Module.finrank_fintype_fun_eq_card,Fintype.card_coe,card_erase_of_mem d]
   using LinearMap.finrank_le_finrank_of_injective this
 apply LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr ?_);intro x e;have z k (b:k≠a):x.val k=0:=by
  by_cases h:k∈A
  ·exact congrFun e ⟨k,mem_erase.mpr ⟨b,h⟩⟩
  ·exact x.2.2 k h
 have g:=sum_eq_single_of_mem a (mem_univ a) (fun k _ b=>z k b);exact Subtype.ext (funext fun k=>by change x.val k=0;have:=x.2.1;grind)
def zJ (P:Submodule ℂ aH):Prop:=
 (∃A:Finset (Fin 5),A.card=3∧P=bJ A)∨
 (∃A B:Finset (Fin 5),A.card=2∧B.card=2∧Disjoint A B∧
   P=bJ A⊔bJ B)
lemma lF (hL:aD L) (r:aX L=8)
  {i:Fin 4} (p:u L i=2):zJ (U L i):=by
 obtain⟨m,J⟩:=rV hL r p;have s:=(tE L i).trans p
 let S:=({m}:Finset (Fin 5))ᶜ
 have F:S.card=4:=by simp[S,card_compl]
 by_cases c:∀j∈S,∃x:U L i,x.val j≠0
 ·obtain⟨A,sub,f,u,v,M,C⟩:=kT _ s S (card_pos.mp (by omega))
   (fun j=>⟨c j,by rintro⟨x,P⟩;simpa[S] using(show j≠m by grind)⟩) (by
     intro x j l O;obtain⟨y,K⟩:=c j l;simp only[S,mem_compl,mem_singleton] at l ⊢
     by_contra! n;exact rW hL r p (Ne.symm l) J y.2 K x.2 O n)
  have o:(S \ A).card=2:=by rw[card_sdiff_of_subset sub,F,f]
  have g {B:Finset (Fin 5)} (o:B.card=2) (x:U L i)
    (sx:∀k,x.val k≠0↔k∈B):x.val≠0∧ℂ ∙ x.val=bJ B:=by
   obtain⟨k,a⟩:=card_pos.mp (show 0<B.card by omega);have n:x.val≠0:=fun e=>(sx k).mpr a (congrFun e k)
   have d:=jR B ⟨k,a⟩;refine⟨n,Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem ..).mpr
    ⟨lR hL x.2,fun j l=>not_ne_iff.mp (by rwa [sx])⟩) ?_⟩
   rw[finrank_span_singleton n];omega
  obtain⟨N,q⟩:=g f u M;have G:=(g o v C).2;obtain⟨k,a⟩:=card_pos.mp (show 0<(S \ A).card by omega);have rP:v.val∉ℂ ∙ u.val:=fun h=>(C k).mpr a ((show v.val∈bJ A from q▸h).2 k (mem_sdiff.mp a).2)
  refine Or.inr ⟨A,S \ A,f,o,disjoint_sdiff_self_right,?_⟩;rw[←q,←G,eq_comm];apply Submodule.eq_of_le_of_finrank_le (sup_le (by simp) (by simp));rw[Submodule.finrank_sup_span_singleton rP,finrank_span_singleton N,s]
 ·push Not at c
  obtain⟨b,H,z⟩:=c
  let A:=({m,b}:Finset (Fin 5))ᶜ
  have E:b≠m:=by simpa[S] using H
  have f:A.card=3:=by simp[A,card_compl,E.symm]
  refine Or.inl ⟨A,f,Submodule.eq_of_le_of_finrank_le ?_ ?_⟩
  ·intro w t;refine⟨lR hL t,fun k a=> ?_⟩;have:=z ⟨w,t⟩;simp[A] at a;grind
  ·have:=jR A (card_pos.mp (by omega));omega
abbrev kV:=∀L:Submodule ℂ aC,aD L→aX L=8→∀i,u L i=2→∀A:Finset (Fin 5),A.card=3→U L i=bJ A→False
abbrev fD:=∀L:Submodule ℂ aC,aD L→aX L=8→
 ∀
  i,u L i=2→∀A B:Finset (Fin 5),A.card=2→B.card=2→Disjoint A B→
  U L i=bJ A⊔bJ B→False
abbrev lT:=∀L:Submodule ℂ aC,aD L→aX L=8→∀i,u L i=3→False
lemma uR (t:kV) (p:fD) (h:lT):
  MidCase:=by
 intro L a b i k j;by_cases f:u L i=2
 ·rcases lF a b f with⟨A,c,e⟩|⟨A,B,c,g,d,e⟩
  ·exact t L a b i f A c e
  ·exact p L a b i f A B c g d e
 ·exact h L a b i (by omega)
end Ac.Af
namespace Ac.Aj
open Aa
abbrev cI:=Fin 4×Fin 2→ℂ
def aS (x:cI):ℂ:=∑i:Fin 4,(x (i,0)+x (i,1))
def jS (x:cI) (j:Fin 2):ℂ:=∑i:Fin 4,x (i,j)
def dQ (x:cI):ℂ:=jS x 0*jS x 1- ∑i:Fin 4,x (i,0)*x (i,1)
def
    bZ (x y : cI) : ℂ := jS x 0 * jS y 1 + jS x 1 * jS y 0 -
    ∑ i : Fin 4, (x (i,0)*y (i,1)+x (i,1)*y (i,0))
def xR:cI→ₗ[ℂ] Module.Dual ℂ cI:=
 LinearMap.mk₂ ℂ bZ
  (fun x y z=>by simp[bZ,jS,Fin.sum_univ_four];ring)
  (fun c x y=>by simp[bZ,jS,Fin.sum_univ_four];ring)
  (fun x y z=>by simp[bZ,jS,Fin.sum_univ_four];ring)
  (fun c x y=>by simp[bZ,jS,Fin.sum_univ_four];ring)
lemma wA (x y:cI):xR x y=bZ x y:=rfl
lemma aE1 (x y:cI):bZ x y=dQ (x+y)-dQ x-dQ y:=by simp[bZ,dQ,jS,Fin.sum_univ_four];ring
lemma aDi (x:cI):bZ 1 x=3*aS x:=by simp[bZ,jS,aS,Fin.sum_univ_four];ring
lemma aE2:Function.Injective xR:=by
 rw[←LinearMap.ker_eq_bot,LinearMap.ker_eq_bot'];intro x e;have h (i:Fin 4) (j:Fin 2):bZ x (Pi.single (i,j) 1)=0:=by rw[←wA,e];rfl
 have a (i:Fin 4) (j:Fin 2):jS x j-x (i,j)=0:=by
  fin_cases i<;>fin_cases j<;>
   first
   | simpa[bZ,jS,Fin.sum_univ_four,Pi.single_apply] using h 0 0
   | simpa[bZ,jS,Fin.sum_univ_four,Pi.single_apply] using h 0 1
   | simpa[bZ,jS,Fin.sum_univ_four,Pi.single_apply] using h 1 0
   | simpa[bZ,jS,Fin.sum_univ_four,Pi.single_apply] using h 1 1
   | simpa[bZ,jS,Fin.sum_univ_four,Pi.single_apply] using h 2 0
   | simpa[bZ,jS,Fin.sum_univ_four,Pi.single_apply] using h 2 1
   | simpa[bZ,jS,Fin.sum_univ_four,Pi.single_apply] using h 3 0
   | simpa[bZ,jS,Fin.sum_univ_four,Pi.single_apply] using h 3 1
 have c (j:Fin 2):jS x j=0:=by
  have d:∀i:Fin 4,x (i,j)=jS x j:=fun i=>(sub_eq_zero.mp (a i j)).symm
  have b:jS x j=∑i:Fin 4,jS x j:=by
   conv_lhs=>unfold jS
   exact Finset.sum_congr rfl fun i _=>d i
  simpa[Fin.sum_univ_four] using(show(3:ℂ)*jS x j=0 by simp only[Fin.sum_univ_four] at b;linear_combination-b)
 funext ⟨i,j⟩;simpa[c] using a i j
lemma aBz (S:Submodule ℂ cI)
  (k:∀x∈S,aS x=0) (g:∀x∈S,dQ x=0):
  Module.finrank ℂ S≤3:=by
 let E:=S⊔Submodule.span ℂ {(1:cI)}
 have j (x:cI) (f:x∈S) (y:cI) (d:y∈S):xR x y=0:=by rw[wA,aE1,g _ (S.add_mem f d),g x f,g y d];ring
 have n (x:cI) (f:x∈E):xR x∈S.dualAnnihilator:=by
  rw[Submodule.mem_dualAnnihilator];intro y d;obtain⟨a,o,b,p,rfl⟩:=Submodule.mem_sup.mp f;obtain⟨c,rfl⟩:=Submodule.mem_span_singleton.mp p;have m:xR (1:cI) y=0:=by rw[wA,aDi,k y d,mul_zero]
  simp[j _ o _ d,m]
 have s:Function.Injective ((xR.domRestrict E).codRestrict S.dualAnnihilator
  (fun x=>n x x.2)):=fun a b e=>Subtype.ext (aE2 (congrArg Subtype.val e))
 have q:=LinearMap.finrank_le_finrank_of_injective s;have hnot:(1:cI)∉S:=by intro r;have h:=k 1 r;norm_num[aS,Fin.sum_univ_four] at h
 have t:Module.finrank ℂ S<Module.finrank ℂ E:=by apply Submodule.finrank_lt_finrank_of_lt;apply lt_of_le_of_ne le_sup_left;intro i;apply hnot;rw[i];exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _))
 have i:=Subspace.finrank_add_finrank_dualAnnihilator_eq S;have l:Module.finrank ℂ cI=8:=by simp[cI]
 omega
def bW (x:aC):cI:=fun p=>x (p.1,Fin.castLE (by decide) p.2)
def eV:aC→ₗ[ℂ] cI:=LinearMap.funLeft ℂ ℂ (fun p:Fin 4×Fin 2=>(p.1,Fin.castLE (by decide) p.2))
def bC (x:aC) (i:Fin 4):ℂ:=x (i,2)+x (i,3)+x (i,4)
def eM (x:aC):ℂ:=bC x 0*bC x 1-(x (0,2)*x (1,2)+x (0,3)*x (1,3)+x (0,4)*x (1,4))
lemma fH (f:Fin 5→ℂ):∑j,f j=f 0+f 1+f 2+f 3+f 4:=by simp[Fin.sum_univ_succ];ring
lemma mO {x:aC}
  (g:∀i:Fin 4,2≤ i→∀j:Fin 5,2≤j→x (i,j)=0)
  (h:bC x 0=0) (k:bC x 1=0) (p:eM x=0)
  (m:cW x=0) (n:pQ x=0):aS (bW x)=0∧dQ (bW x)=0:=by
 have o (i:Fin 4) (l:2≤ i):x (i,2)=0∧x (i,3)=0∧x (i,4)=0:=⟨g i l 2 (by decide),g i l 3 (by decide),g i l 4 (by decide)⟩
 obtain⟨a,b,c⟩:=o 2 (by decide);obtain⟨d,e,f⟩:=o 3 (by decide);have t:aS (bW x)+bC x 0+bC x 1=cW x:=by simp[aS,bW,Fin.sum_univ_four,cW,fH,bC,a,b,c,d,e,f];ring
 have q:dQ (bW x)+eM x+
   bC x 0*(bW x (1,0)+bW x (1,1)+bW x (2,0)+bW x (2,1)+bW x (3,0)+bW x (3,1))+
   bC x 1*(bW x (0,0)+bW x (0,1)+bW x (2,0)+bW x (2,1)+bW x (3,0)+bW x (3,1))=
   pQ x:=by
  simp(config:={decide:=true}) [dQ,jS,bW,eM,bC,pQ,Fin.sum_univ_four,fH,a,b,c,d,e,f];ring
 exact⟨by simpa[h,k,m] using t,by simpa[h,k,p,n] using q⟩
lemma mP {L K:Submodule ℂ aC} (hL:aD L) (d:K≤L)
  (b:∀x∈K,∀i:Fin 4,2≤ i→∀j:Fin 5,2≤j→x (i,j)=0)
  (f:∀x∈K,bC x 0=0) (g:∀x∈K,bC x 1=0)
  (h:∀x∈K,eM x=0) (e:Function.Injective (eV.domRestrict K)):
  aX K≤3:=by
 have l:Module.finrank ℂ (K.map eV)≤3:=by
  apply aBz
  ·rintro _ ⟨x,a,rfl⟩;have c:=Ac.Ad.cT hL (d a);exact(mO (b x a) (f x a) (g x a) (h x a) c.1 c.2.1).1
  ·rintro _ ⟨x,a,rfl⟩;have c:=Ac.Ad.cT hL (d a);exact(mO (b x a) (f x a) (g x a) (h x a) c.1 c.2.1).2
 have k:=(LinearEquiv.ofInjective (eV.domRestrict K) e).finrank_eq;have m:LinearMap.range (eV.domRestrict K)=K.map eV:=by
  ext z;constructor
  ·rintro⟨⟨x,a⟩,rfl⟩;exact⟨x,a,rfl⟩
  ·rintro⟨x,a,rfl⟩;exact⟨⟨x,a⟩,rfl⟩
 rw[m] at k;exact k.le.trans l
end Ac.Aj
namespace Ac.An
open Aa Matrix
abbrev bN (L:Submodule ℂ aC) (i:Fin 4):=L.map (row i)
abbrev aE (L:Submodule ℂ aC) (i:Fin 4):=Module.finrank ℂ (bN L i)
abbrev aY (L:Submodule ℂ aC) (i:Fin 4):=bN L i⊔Submodule.span ℂ {(1:aH)}
abbrev bM (n:aH):=LinearMap.ker (dotProductEquiv ℂ (Fin 5) n)
def jT (L:Submodule ℂ aC) (i j:Fin 4):Prop:=
 ∃
  Z:Matrix (Fin 5) (Fin 5) ℂ,Z.IsSymm∧Z*ᵥ (1:aH)≠0∧
  ∀t∈L,(1+row i t) ⬝ᵥ Z*ᵥ (1+row j t)=0
lemma aB0 {L:Submodule ℂ aC} (hL:aD L) (i:Fin 4):
  (1:aH)∉bN L i:=by
 rintro⟨t,c,b⟩;have a:aO (1+ -t)=0:=by apply Finset.sum_eq_zero;intro e _;apply Finset.prod_eq_zero (Finset.mem_univ i);have h:t (i,e i)=1:=congrFun b (e i);change 1+ -t (i,e i)=0;rw[h];ring
 rw[hL _ (L.neg_mem c)] at a;norm_num at a
lemma cV {L:Submodule ℂ aC} (hL:aD L) (i:Fin 4):
  Module.finrank ℂ (aY L i)=aE L i+1:=
 Submodule.finrank_sup_span_singleton (aB0 hL i)
abbrev obs (L:Submodule ℂ aC) (i:Fin 4):=(row i).comp L.subtype
abbrev bS (L:Submodule ℂ aC) (i:Fin 4):=LinearMap.ker (obs L i)
abbrev aJ (L:Submodule ℂ aC) (i j:Fin 4):=bS L i⊓bS L j
lemma lU (L:Submodule ℂ aC) (i:Fin 4):
  aE L i+Module.finrank ℂ (bS L i)=aX L:=by
 have h:=(obs L i).finrank_range_add_finrank_ker;rwa [LinearMap.range_comp,Submodule.range_subtype] at h
lemma cA (L:Submodule ℂ aC) (i j:Fin 4):
  p L i j+Module.finrank ℂ (aJ L i j)=aX L:=by
 let f:=((row i).prod (row j)).comp L.subtype
 have h:=f.finrank_range_add_finrank_ker;have a:LinearMap.ker f=aJ L i j:=LinearMap.ker_prod (obs L i) (obs L j);rwa [a,LinearMap.range_comp,Submodule.range_subtype] at h
lemma tH (L:Submodule ℂ aC) (i j:Fin 4):p L i j=p L j i:=by have h:=cA L i j;have g:=cA L j i;unfold aJ at h g;rw[inf_comm] at g;omega
lemma hV {L:Submodule ℂ aC} (m:∀l,u L l=0)
  {i j k:Fin 4} (a:i≠j) (b:i≠k) (c:j≠k)
  (x:L) (d:row i x=0) (f:row j x=0) (g:row k x=0):x=0:=by
 obtain⟨l,n⟩:∃l:Fin 4,∀r:Fin 4,r≠l→ r=i∨r=j∨r=k:=by clear m x d f g L;decide+revert
 have h:(x:aC)∈aZ L l:=by
  refine⟨x.property,(Submodule.mem_iInf _).mpr ?_⟩;intro r;rcases n r.val r.property with e|e|e
  ·exact e▸d
  ·exact e▸f
  ·exact e▸g
 rw[Submodule.finrank_eq_zero.mp (m l)] at h;exact Subtype.ext h
lemma bB {L:Submodule ℂ aC} (g:∀l,u L l=0)
  {i j k:Fin 4} (a:i≠j) (b:i≠k) (c:j≠k):
  aX L+aE L i≤p L i j+p L i k:=by
 let P:=aJ L i j
 let Q:=aJ L i k
 have e:P⊓Q= ⊥ :=by apply eq_bot_iff.mpr;intro x d;exact hV g a b c x d.1.1 d.1.2 d.2.2
 have f:P⊔Q≤bS L i:=sup_le inf_le_left inf_le_left;have h:=Submodule.finrank_sup_add_finrank_inf_eq P Q;rw[e,finrank_bot,add_zero] at h;have m:=Submodule.finrank_mono f;have n:=cA L i j;have o:=cA L i k;have q:=lU L i;change Module.finrank ℂ (P⊔Q:Submodule ℂ L)≤_ at m;change p L i j+Module.finrank ℂ P=aX L at n;change p L i k+Module.finrank ℂ Q=aX L at o;omega
lemma wB (L:Submodule ℂ aC) (i j:Fin 4):
  L.map ((row i).prod (row j))≤(bN L i).prod (bN L j):=by
 rintro _ ⟨x,a,rfl⟩;exact⟨⟨x,a,rfl⟩,⟨x,a,rfl⟩⟩
lemma rX (L:Submodule ℂ aC) (i j:Fin 4):
  Module.finrank ℂ ((bN L i).prod (bN L j))=aE L i+aE L j:=by
 rw[((bN L i).prodEquiv (bN L j)).finrank_eq,Module.finrank_prod]
lemma cF (L:Submodule ℂ aC) (i j:Fin 4):
  p L i j≤aE L i+aE L j:=
 (Submodule.finrank_mono (wB L i j)).trans_eq (rX L i j)
lemma qI {L:Submodule ℂ aC} {i j:Fin 4}
  (a:p L i j=aE L i+aE L j):
  L.map ((row i).prod (row j))=(bN L i).prod (bN L j):=by
 apply Submodule.eq_of_le_of_finrank_le (wB L i j);rw[rX,←a]
lemma qJ {L:Submodule ℂ aC} {i:Fin 4} (f:Module.Dual ℂ aH)
  (b:∀x∈bN L i,f (1+x)=0):aY L i≤LinearMap.ker f:=by
 have a:f 1=0:=by simpa only[add_zero] using b 0 (Submodule.zero_mem _)
 refine sup_le ?_ ((Submodule.span_singleton_le_iff_mem _ _).mpr a);intro x c;change f x=0;simpa only[map_add,a,zero_add] using b x c
lemma nU {L:Submodule ℂ aC} {i j:Fin 4}
  (h:p L i j=aE L i+aE L j) (F:aH→ₗ[ℂ] aH→ₗ[ℂ] ℂ)
  (f:∀t∈L,F (1+row i t) (1+row j t)=0):
  ∀x∈aY L i,∀y∈aY L j,F x y=0:=by
 have g (v w:aH) (c:v∈bN L i) (d:w∈bN L j):
   F (1+v) (1+w)=0:=by
  obtain⟨t,k,e⟩:=(show(v,w)∈L.map ((row i).prod (row j)) by rw[qI h];exact⟨c,d⟩)
  have a:row i t=v:=congrArg Prod.fst e;have b:row j t=w:=congrArg Prod.snd e;simpa only[a,b] using f t k
 intro x l;apply qJ (F x);intro w d;exact qJ (F.flip (1+w)) (fun v c=>g v w c d) l
lemma wC {n:aH} (b:n≠0):
  Module.finrank ℂ (bM n)=4:=by
 have a:dotProductEquiv ℂ (Fin 5) n≠0:=by simpa using b
 have h:=Module.Dual.finrank_ker_add_one_of_ne_zero a;change Module.finrank ℂ (bM n)+1=Module.finrank ℂ (Fin 5→ℂ) at h;simp only[Module.finrank_pi,Fintype.card_fin] at h;omega
lemma fE {L:Submodule ℂ aC} {i j:Fin 4}
  (q:p L i j=aE L i+aE L j) (s:jT L i j):
  ∃
   n:aH,n≠0∧(∑c,n c)=0∧aY L i≤bM n∧
   aY L j≤bM n:=by
 obtain⟨Z,m,o,h⟩:=s
 let n:=Z*ᵥ (1:aH)
 have f (x y:aH) (g:x∈bN L i) (k:y∈bN L j):
   (1+x) ⬝ᵥ Z*ᵥ (1+y)=0:=by
  obtain⟨t,r,d⟩:=(show(x,y)∈L.map ((row i).prod (row j)) by rw[qI q];exact⟨g,k⟩)
  have a:row i t=x:=congrArg Prod.fst d;have b:row j t=y:=congrArg Prod.snd d;simpa only[a,b] using h t r
 have d:(1:aH) ⬝ᵥ n=0:=by simpa only[add_zero] using f 0 0 (Submodule.zero_mem _) (Submodule.zero_mem _)
 have l:(1:aH)∈bM n:=(dotProduct_comm n 1).trans d;refine⟨n,o,by simpa only[one_dotProduct] using d,
  sup_le ?_ ((Submodule.span_singleton_le_iff_mem _ _).mpr l),
  sup_le ?_ ((Submodule.span_singleton_le_iff_mem _ _).mpr l)⟩
 ·intro x g;have e:=f x 0 g (Submodule.zero_mem _);rw[add_zero,add_dotProduct,d,zero_add] at e;exact(dotProduct_comm n x).trans e
 ·intro y k;have e:=f 0 y (Submodule.zero_mem _) k;rw[add_zero,m.dotProduct_mulVec_comm,add_dotProduct,d,zero_add] at e;exact(dotProduct_comm n y).trans e
lemma jU {L:Submodule ℂ aC} (hL:aD L) {i j:Fin 4}
  (d:aE L i=3) (f:p L i j=aE L i+aE L j)
  (g:jT L i j):aY L j≤aY L i:=by
 obtain⟨n,e,_,a,b⟩:=fE f g;have c:aY L i=bM n:=Submodule.eq_of_le_of_finrank_le a (by rw[wC e,cV hL,d]);rwa [c]
lemma eN {L:Submodule ℂ aC} (hL:aD L)
  (x:aX L=8) (t:∀l,u L l=0)
  (v:∀i j,i≠j→p L i j=6→jT L i j)
  {i j k:Fin 4} (a:i≠j) (b:i≠k) (c:j≠k)
  (f:aE L i=3) (m:aE L j=3) (n:aE L k=3):
  aY L i=aY L j:=by
 have d {r s:Fin 4} (o:r≠s) (e:aE L r=3) (q:aE L s=3)
   (h:p L r s=6):aY L r=aY L s:=by
  have g:=jU hL e (by rw[e,q];exact h) (v _ _ o h);exact(Submodule.eq_of_le_of_finrank_le g (by rw[cV hL,cV hL,e,q])).symm
 by_cases h:p L i j=6
 ·exact d a f m h
 ·have y:=bB t a b c;have w:=bB t a.symm c b;rw[tH L j i] at w;have z:=cF L i j;have A:=cF L i k;have B:=cF L j k;exact(d b f n (by omega)).trans (d c m n (by omega)).symm
lemma xT {L:Submodule ℂ aC} (hL:aD L)
  (v:aX L=8) (o:∀l,u L l=0)
  (q:∀i j,i≠j→p L i j=6→jT L i j)
  {a b c:Fin 4} (hab:a≠b) (d:a≠c) (f:b≠c)
  (e:aE L a=3) (g:aE L b=3) (t:aE L c=3):
  ∃n:aH,n≠0∧(∑j,n j)=0∧∀i,aE L i=3→aY L i=bM n:=by
 have H (i:Fin 4) (k:aE L i=3):aY L a=aY L i:=by
  by_cases h:a=i
  ·rw[h]
  by_cases z:i=b
  ·subst i;exact eN hL v o q hab d f e g t
  exact eN hL v o q h hab z e k g
 have y:∃r:Fin 4,a≠r∧aE L r=3∧p L a r=6:=by
  have m:=bB o hab d f;have E:=cF L a b;have F:=cF L a c;by_cases h:p L a b=6
  ·exact⟨b,hab,g,h⟩
  exact⟨c,d,t,by omega⟩
 obtain⟨r,s,B,x⟩:=y;obtain⟨n,w,C,A,_⟩:=fE
  (show p L a r=aE L a+aE L r by rw[e,B,x]) (q a r s x)
 refine⟨n,w,C,fun i k=>(H i k).symm.trans ?_⟩;exact Submodule.eq_of_le_of_finrank_le A (by rw[wC w,cV hL,e])
end Ac.An
namespace A9
lemma rY {ι:Type*} [Fintype ι] (u v:ι→ℂ)
  (g:∑j,u j=0) (k:∑j,v j=0)
  (f:∀i j,i≠j→u i*v j+u j*v i=0):
  u=0∨v=0:=by
 classical
 have kH (i:ι):u i*v i=0:=by have e:∑j,(u i*v j+u j*v i)=u i*v i+u i*v i:=Finset.sum_eq_single i (fun j _ d=>f i j d.symm) (by simp);rw[Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul,g,k] at e;linear_combination-e/2
 by_cases h:∀i,u i=0
 ·exact Or.inl (funext h)
 push Not at h
 obtain⟨i,b⟩:=h;have a:=(mul_eq_zero.mp (kH i)).resolve_left b;right;funext j;by_cases c:i=j
 ·subst j;exact a
 ·have e:u i*v j=0:=by simpa[a] using f i j c
  exact(mul_eq_zero.mp e).resolve_left b
lemma finrank_le_one {P:Type*} [AddCommGroup P] [Module ℂ P] [FiniteDimensional ℂ P]
  (a b:P→ₗ[ℂ] (Fin 5→ℂ)) (k:Function.Injective a) (l:Function.Injective b)
  (e:∀x,(∑i,a x i)+(∑i,b x i)=0)
  (c:∀x i j,i≠j→a x i*b x j+a x j*b x i=0):
  Module.finrank ℂ P≤1:=by
 classical
 let s:P→ₗ[ℂ] ℂ:=∑i:Fin 5,(LinearMap.proj i).comp a
 have g:Function.Injective s:=by
  rw[←LinearMap.ker_eq_bot,LinearMap.ker_eq_bot'];intro x m;have d:∑i,a x i=0:=by simpa[s,LinearMap.sum_apply] using m
  have f:∑i,b x i=0:=by simpa[d] using e x
  rcases rY (a x) (b x) d f (c x) with h|h
  ·exact k (h.trans a.map_zero.symm)
  ·exact l (h.trans b.map_zero.symm)
 simpa using LinearMap.finrank_le_finrank_of_injective g
end A9
namespace Ag
abbrev Row:=Fin 5→ℂ
variable {P : Type*} [AddCommGroup P] [Module ℂ P]
lemma dE (f g:P→ₗ[ℂ] ℂ)
  (h:∀x,f x*g x=0):f=0∨g=0:=by
 classical
 by_contra! b;obtain⟨x,c⟩:∃x,f x≠0:=by by_contra! a;exact b.1 (LinearMap.ext a)
 obtain⟨y,d⟩:∃y,g y≠0:=by by_contra! a;exact b.2 (LinearMap.ext a)
 have i:=(mul_eq_zero.mp (h x)).resolve_left c;have e:=(mul_eq_zero.mp (h y)).resolve_right d;simpa[map_add,i,e,c,d] using h (x+y)
lemma nV (f g A B:P→ₗ[ℂ] ℂ) (j:A≠0) (k:B≠0)
  (h:∀x,f x*g x=A x*B x) (x:P) (i:A x=0) (n:B x=0):
  f x=0∧g x=0:=by
 classical
 obtain⟨y,o⟩:∃y,A y*B y≠0:=by by_contra! b;exact(dE A B b).elim j k
 have c:f y*g y≠0:=by rwa [h]
 have l:=left_ne_zero_of_mul c;have m:=right_ne_zero_of_mul c;have a:=h (x+y);simp only[map_add,i,n,zero_add,←h y] at a;have b:=h x;rw[i,zero_mul,mul_eq_zero] at b;rcases b with d|e
 ·refine⟨d,?_⟩;apply(mul_eq_zero.mp (show f y*g x=0 by rw[d,zero_add] at a;linear_combination a)).resolve_left l
 ·refine⟨?_,e⟩;apply(mul_eq_zero.mp (show f x*g y=0 by rw[e,zero_add] at a;linear_combination a)).resolve_right m
abbrev lV (a:P→ₗ[ℂ] Row) (i:Fin 5):P→ₗ[ℂ] ℂ:=(LinearMap.proj i).comp a
abbrev aS (a:P→ₗ[ℂ] Row):P→ₗ[ℂ] ℂ:=∑i,lV a i
lemma kW (a:P→ₗ[ℂ] Row) (x:P):aS a x=∑i,a x i:=by simp[aS,lV,LinearMap.sum_apply]
lemma fV (a:P→ₗ[ℂ] Row) (l:Function.Injective a)
  (S:Finset (Fin 5)) (o:S.card≤2) (f:∀x i,i∉S→a x i=0)
  (g:∀x,∑i,a x i=0):Module.finrank ℂ P≤1:=by
 classical
 obtain⟨p,m⟩:∃p:Fin 5,p∈S∨S= ∅ :=by
  rcases S.eq_empty_or_nonempty with h|⟨p,h⟩
  ·exact⟨0,Or.inr h⟩
  ·exact⟨p,Or.inl h⟩
 let d:P→ₗ[ℂ] (↥(S.erase p)→ℂ):=LinearMap.pi fun i=>lV a i
 have k:Function.Injective d:=by
  rw[←LinearMap.ker_eq_bot,LinearMap.ker_eq_bot'];intro x n;have c (i:Fin 5) (j:i≠p):a x i=0:=by
   by_cases h:i∈S
   ·exact congrFun n ⟨i,Finset.mem_erase.mpr ⟨j,h⟩⟩
   ·exact f x i h
  have e:(∑i,a x i)=a x p:=Finset.sum_eq_single p (fun i _ j=>c i j) (by simp);apply l;rw[map_zero];funext i;by_cases h:i=p
  ·exact h▸e.symm.trans (g x)
  ·exact c i h
 have b:=LinearMap.finrank_le_finrank_of_injective k;rw[Module.finrank_pi,Fintype.card_coe] at b;rcases m with h|rfl
 ·rw[Finset.card_erase_of_mem h] at b;omega
 ·simp at b;omega
def lW (u v:Row) (i:Fin 5):ℂ:=u i*(∑j,v j)+v i*(∑j,u j)-2*u i*v i
lemma fW (a b:P→ₗ[ℂ] Row)
  (t:Function.Injective a) (w:Function.Injective b)
  (r:∀x,(∑i,a x i)+(∑i,b x i)=0)
  (v:∀x i,lW (a x) (b x) i=0):Module.finrank ℂ P≤1:=by
 classical
 have c (x:P):aS a x+aS b x=0:=by simpa only[kW] using r x
 have l (x:P) (i:Fin 5):
   a x i*aS b x+b x i*aS a x-2*a x i*b x i=0:=by
  simpa only[kW,lW] using v x i
 by_cases m:aS a=0
 ·have d (x:P):aS a x=0:=LinearMap.congr_fun m x;have k (x:P):aS b x=0:=by simpa only[d,zero_add] using c x
  have g (i:Fin 5):lV a i=0∨lV b i=0:=by apply dE;intro x;change a x i*b x i=0;have h:=l x i;rw[d,k] at h;linear_combination-h/2
  let S:=Finset.univ.filter fun i=>lV a i≠0
  have e (i:Fin 5):i∈S↔lV a i≠0:=by simp[S]
  by_cases f:S.card≤2
  ·apply fV a t S f
   ·intro x i p;have h:lV a i=0:=not_not.mp (p∘(e i).mpr);exact LinearMap.congr_fun h x
   ·simpa only[kW] using d
  ·have A:Sᶜ.card+S.card=5:=by simp
   apply fV b w Sᶜ (by omega)
   ·intro x i p;have u:i∈S:=by simpa using p
    exact LinearMap.congr_fun ((g i).resolve_left ((e i).mp u)) x
   ·simpa only[kW] using k
 ·have n:aS b≠0:=by
   intro n;apply m;ext x;simpa only[n,LinearMap.zero_apply,add_zero] using c x
  have q:Function.Injective (aS a):=by
   rw[←LinearMap.ker_eq_bot,LinearMap.ker_eq_bot'];intro x s;have z:aS b x=0:=by simpa only[s,zero_add] using c x
   apply t;rw[map_zero];funext i;have j (y:P):
     (2*a y i-aS a y)*(2*b y i-aS b y)=aS a y*aS b y:=by
    linear_combination-2*l y i
   have o:=(nV ((2:ℂ)•lV a i-aS a)
    ((2:ℂ)•lV b i-aS b) (aS a) (aS b) m n j x s z).1
   change 2*a x i-aS a x=0 at o;change a x i=0;rw[s,sub_zero,mul_eq_zero] at o;exact o.resolve_left (by norm_num)
  simpa using LinearMap.finrank_le_finrank_of_injective q
def aL (a b:Row) (i j:Fin 5):ℂ:=a i*b j+a j*b i
def dQ (a b:Row):ℂ:=∑i:Fin 5,∑j:Fin 5,if i<j then aL a b i j else 0
def dL (a b:Row):Matrix (Fin 5) (Fin 5) ℂ:=fun i j=>if i=j then 0 else ∑c:Fin 5,∑d:Fin 5,if c<d∧c≠i∧c≠j∧d≠i∧d≠j then aL a b c d else 0
lemma vH (f:Fin 5→ℂ):
  ∑i,f i=f 0+f 1+f 2+f 3+f 4:=by
 simp[Fin.sum_univ_succ];ring
set_option maxHeartbeats 3000000 in
lemma iF (a b:Row) (i:Fin 5):
  (∑j,dL a b i j)=2*(dQ a b-lW a b i):=by
 have h:i=0∨i=1∨i=2∨i=3∨i=4:=by decide+revert
 rcases h with rfl|rfl|rfl|rfl|rfl<;>
  simp(config:={decide:=true}) only[dL,dQ,aL,lW,vH,
   ite_true,ite_false,zero_add,add_zero]<;>ring
lemma iG (a b:P→ₗ[ℂ] Row)
  (f:Function.Injective a) (g:Function.Injective b)
  (d:∀x,(∑i,a x i)+(∑i,b x i)=0)
  (c:∀x,dQ (a x) (b x)=0) (k:2≤Module.finrank ℂ P):
  ∃x,(dL (a x) (b x)).mulVec (1:Row)≠0:=by
 by_contra! l;have e (x:P) (i:Fin 5):lW (a x) (b x) i=0:=by
  have h:(∑j,dL (a x) (b x) i j)=0:=by simpa only[Matrix.mulVec,dotProduct_one,Pi.zero_apply] using congrFun (l x) i
  rw[iF,c] at h;linear_combination-h/2
 have:=fW a b f g d e;omega
end Ag
namespace Ai
abbrev E:=Fin 2→ℂ
abbrev iA:=E→ₗ[ℂ] E→ₗ[ℂ] E→ₗ[ℂ] ℂ
lemma cY (T:iA) (h:∀x y:E,T x y (x+y)=0):
  T=0:=by
 have kH (x y:E):T x y x=0∧T x y y=0:=by
  have e:=h x y;have d:=h x (-y);simp only[map_add,map_neg,LinearMap.neg_apply,neg_neg] at e d;constructor
  ·linear_combination(e-d)/2
  ·linear_combination(e+d)/2
 have a (x y:E):T x y x=0:=(kH x y).1;have c (x y:E):T x y y=0:=(kH x y).2;have f (x y:E):T x x y=0:=by
  simpa only[map_add,LinearMap.add_apply,a,c,zero_add,add_zero]
   using a (x+y) x
 let b:=Pi.basisFun ℂ (Fin 2)
 refine b.ext fun i=>b.ext fun j=>b.ext fun k=> ?_
 change T (b i) (b j) (b k)=0;fin_cases i<;>fin_cases j<;>fin_cases k<;>first | apply a | apply c | apply f
lemma lG (T123 T124 T134 T234:iA)
  (h:∀a b c d:E,a+b+c+d=0→
    T123 a b c+T124 a b d+T134 a c d+T234 b c d=0):
  T123=0∧T124=0∧T134=0∧T234=0:=by
 have e:T124=0:=by
  apply cY;intro x y;simpa only[map_zero,LinearMap.zero_apply,neg_zero,add_zero,zero_add,map_neg,neg_eq_zero]
   using h x y 0 (-(x+y)) (by simp)
 have f:T134=0:=by
  apply cY;intro x y;simpa only[map_zero,LinearMap.zero_apply,neg_zero,add_zero,zero_add,map_neg,neg_eq_zero]
   using h x 0 y (-(x+y)) (by simp)
 have g:T234=0:=by
  apply cY;intro x y;simpa only[map_zero,LinearMap.zero_apply,neg_zero,add_zero,zero_add,map_neg,neg_eq_zero]
   using h 0 x y (-(x+y)) (by simp)
 refine⟨?_,e,f,g⟩;refine LinearMap.ext fun x=>LinearMap.ext fun y=>LinearMap.ext fun z=> ?_
 simpa[e,f,g] using h x y z (-(x+y+z)) (by simp)
lemma rZ (T123 T124 T134 T234:iA)
  (h:∀z:Fin 4→E,∑i,z i=0→
    T123 (z 0) (z 1) (z 2)+T124 (z 0) (z 1) (z 3)+
    T134 (z 0) (z 2) (z 3)+T234 (z 1) (z 2) (z 3)=0):
  T123=0∧T124=0∧T134=0∧T234=0:=by
 apply lG;intro a b c d e;apply h ![a,b,c,d];simpa[Fin.sum_univ_four,add_assoc] using e
end Ai
namespace At
def e3 {N:ℕ} (v:Fin N→ℂ):ℂ:=∑i,∑j,∑k,if i<j∧j<k then v i*v j*v k else 0
lemma aC5 (v:Fin 4→ℂ):
  e3 v=v 0*v 1*v 2+v 0*v 1*v 3+v 0*v 2*v 3+v 1*v 2*v 3:=by
 simp(config:={decide:=true}) only[e3,Fin.sum_univ_four,ite_true,ite_false,zero_add,add_zero]
def jV (v:Fin 3→ℂ):ℂ:= -(v 0)*(v 1^2+v 1*v 2+v 2^2)-v 1*v 2*(v 1+v 2)
lemma aDj (v:Fin 3→ℂ):
  jV v=e3 ![v 0,v 1,v 2,-v 1-v 2]:=by
 simp[jV,aC5];ring
lemma tI {N:ℕ} (S:Submodule ℂ (Fin N→ℂ))
  (k:N≤Module.finrank ℂ S+1) {d:Fin N→ℂ} (c:d∉S)
  (v:Fin N→ℂ):∃t:ℂ,v-t•d∈S:=by
 let P:=S⊔Submodule.span ℂ {d}
 have e:S<P:=Submodule.lt_sup_iff_notMem.mpr c;have j:=Submodule.finrank_lt_finrank_of_lt e;have a:=Submodule.finrank_le P;rw[Module.finrank_fin_fun] at a;have f:P= ⊤ :=Submodule.eq_top_of_finrank_eq (by rw[Module.finrank_fin_fun];omega);have b:v∈P:=f.symm▸Submodule.mem_top;obtain⟨w,g,z,i,h⟩:=Submodule.mem_sup.mp b;obtain⟨t,rfl⟩:=Submodule.mem_span_singleton.mp i;exact⟨t,by simpa[←h] using g⟩
lemma sA (S:Submodule ℂ (Fin 3→ℂ))
  (b:∀v∈S,jV v=0):Module.finrank ℂ S≤1:=by
 by_contra! h
 let A:Fin 3→ℂ:= ![1,0,0]
 let B:Fin 3→ℂ:= ![0,1,0]
 let C:Fin 3→ℂ:= ![0,0,1]
 have f:A∈S:=by by_contra g;obtain⟨s,e⟩:=tI S (by omega) g B;obtain⟨t,a⟩:=tI S (by omega) g C;have c:=b _ e;have d:=b _ a;simp[A,B,jV] at c;simp[A,C,jV] at d;subst s;subst t;simp only[zero_smul,sub_zero] at e a;have H:=b _ (S.add_mem e a);norm_num[jV,B,C] at H
 have i:B∉S:=by intro j;have H:=b _ (S.add_mem f j);norm_num[jV,A,B] at H
 obtain⟨t,a⟩:=tI S (by omega) i C;have c:=b _ a;have d:=b _ (S.add_mem f a);apply(one_ne_zero:(1:ℂ)≠0)
 calc
  1
   =2*jV (C-t•B)-jV (A+(C-t•B)):=by
   simp[A,B,C,jV];ring
  _=0:=by rw[c,d];ring
lemma aC6 (f:Fin 5→ℂ):
  ∑i,f i=f 0+f 1+f 2+f 3+f 4:=by
 simp[Fin.sum_univ_succ];ring
lemma oN (n:Fin 5→ℂ):
  6*e3 n=(∑i,n i)^3-3*(∑i,n i)*(∑i,n i^2)+2*(∑i,n i^3):=by
 simp(config:={decide:=true}) only[e3,aC6,ite_true,ite_false,zero_add,add_zero];ring
lemma aB1 (u:Fin 4→ℂ) (n:Fin 5→ℂ):
  (∑j,∑l,∑m,if j=l∨j=m∨l=m then 0 else
    ∑
     a,∑b,∑c,if a<b∧b<c then
     (u a*n j)*(u b*n l)*(u c*n m) else 0)=6*e3 u*e3 n:=by
 have inner (j l m:Fin 5):
   (∑a,∑b,∑c,if a<b∧b<c then
     (u a*n j)*(u b*n l)*(u c*n m) else 0)=e3 u*(n j*n l*n m):=by
  simp(config:={decide:=true}) only[aC5,Fin.sum_univ_four,ite_true,ite_false,zero_add,add_zero];ring
 have d:(∑j,∑l,∑m,if j=l∨j=m∨l=m then 0 else n j*n l*n m)=
   6*e3 n:=by
  simp(config:={decide:=true}) only[e3,aC6,ite_true,ite_false,zero_add,add_zero];ring
 calc
  _
   =e3 u*(∑j,∑l,∑m,if j=l∨j=m∨l=m then 0 else n j*n l*n m):=by
   simp only[inner,Finset.mul_sum,mul_ite,mul_zero]
  _=_:=by rw[d];ring
lemma oO (a b c:ℂ) (d:a+b+c=0) (e:a^2+b^2+c^2=0)
  (f:a^3+b^3+c^3=0):a=0:=by
 have h:a^3=0:=by linear_combination((a+b+c)^2/6-(a^2+b^2+c^2)/2-a*(a+b+c)/2+a^2)*d+a/2*e+f/3
 simpa using h
lemma mQ (n:Fin 5→ℂ) (z:n≠0)
  (g:(Finset.univ.filter (fun i=>n i≠0)).card≤3)
  (c:∑i,n i=0) (e:∑i,n i^2=0):e3 n≠0:=by
 classical
 intro u;have m:=oN n;rw[c,e,u] at m;have h:∑i,n i^3=0:=by linear_combination-m/2
 obtain⟨s,A,_,t⟩:=Finset.exists_subsuperset_card_eq
  (Finset.subset_univ _) g (by decide)
 obtain⟨i,j,k,o,p,q,rfl⟩:=Finset.card_eq_three.mp t;have d (l:Fin 5) (b:l∉({i,j,k}:Finset _)):n l=0:=by by_contra r;exact b (A (by simpa using r))
 have a (f:ℂ→ℂ) (v:f 0=0):
   (∑l,f (n l))=f (n i)+f (n j)+f (n k):=by
  calc
   _
    =∑l∈({i,j,k}:Finset _),f (n l):=by
    apply Eq.symm;apply Finset.sum_subset (Finset.subset_univ _);intro l _ b;rw[d l b,v]
   _=_:=by simp[o,p,q,add_assoc]
 change ∑l,(fun x:ℂ=>x) (n l)=0 at c;rw[a (fun x=>x) rfl] at c;rw[a (fun x=>x^2) (by norm_num)] at e;rw[a (fun x=>x^3) (by norm_num)] at h;have w:=oO _ _ _ c e h;have y:=oO (n j) (n i) (n k) (by linear_combination c) (by linear_combination e) (by linear_combination h);have B:n k=0:=by linear_combination c-w-y
 apply z;funext l;by_cases b:l∈({i,j,k}:Finset _)
 ·simp only[Finset.mem_insert,Finset.mem_singleton] at b;rcases b with rfl|rfl|rfl<;>assumption
 ·exact d l b
end At
namespace Ac.A4
open Aa Ac.Ae Ac.Ap Finset
abbrev bE:=Fin 4→ℂ
def rP (k:F):aH→ₗ[ℂ] bE:=LinearMap.funLeft ℂ ℂ k.succAbove
def gT (k:F):aC→ₗ[ℂ] bE:=(rP k).comp (row 0-row 1)
def tJ:bE→ₗ[ℂ] bE where
 toFun x i:=(∑j,x j)-2*x i
 map_add' x y:=by ext i;simp[Fin.sum_univ_four];ring
 map_smul' c x:=by ext i;simp[Fin.sum_univ_four];ring
def aA2 (k:F):aH→ₗ[ℂ] bE:=tJ.comp (rP k)
def tK (k:F):aC→ₗ[ℂ] (bE×bE):=((aA2 k).comp (row 2)).prod ((aA2 k).comp (row 3))
def aA3 (k:F):(aH×aH)→ₗ[ℂ] (bE×bE):=((aA2 k).comp (LinearMap.fst ℂ aH aH)).prod ((aA2 k).comp (LinearMap.snd ℂ aH aH))
def D (L:Submodule ℂ aC) (k:F):Submodule ℂ bE:=(bV L).map (gT k)
def M (L:Submodule ℂ aC) (k:F):Submodule ℂ (bE×bE):=(bV L).map (tK k)
def nW (L:Submodule ℂ aC) (k:F):Submodule ℂ (bE×bE):=(bV L⊓LinearMap.ker (gT k)).map (tK k)
lemma wD:tJ 1=(2:ℂ)•(1:bE):=by ext i;norm_num[tJ,Fin.sum_univ_four]
lemma fO (S:Submodule ℂ (bE×bE)) (s:Finset (Fin 4))
  (c:∀w∈S,(∀j∈s,w.1 j=0∧w.2 j=0)→∀i∉s,w.1 i=0∧w.2 i=0):
  Module.finrank ℂ S≤2*s.card:=by
 let b:S→ₗ[ℂ] (↥s→ℂ× ℂ):=
  {toFun w j:=(w.1.1 j.1,w.1.2 j.1),map_add' _ _:=rfl,map_smul' _ _:=rfl}
 have h:Function.Injective b:=(injective_iff_map_eq_zero b).mpr fun w g=>by
  have d (j:Fin 4) (f:j∈s):w.1.1 j=0∧w.1.2 j=0:=⟨congrArg Prod.fst (congrFun g ⟨j,f⟩),congrArg Prod.snd (congrFun g ⟨j,f⟩)⟩
  have a (i:Fin 4):w.1.1 i=0∧w.1.2 i=0:=if hi:i∈s then d i hi else c w.1 w.2 d i hi
  exact Subtype.ext (Prod.ext (funext fun i=>(a i).1) (funext fun i=>(a i).2))
 have e:Module.finrank ℂ (↥s→ℂ× ℂ)=2*s.card:=by rw[Module.finrank_pi_fintype];simp only[Module.finrank_prod,Module.finrank_self,sum_const,card_univ,Fintype.card_coe,smul_eq_mul];ring
 exact e▸b.finrank_le_finrank_of_injective h
lemma tM (L:Submodule ℂ aC) (k:F):((1,1):bE×bE)∈nW L k:=by
 have a:((2:ℂ)•(1:bE),(2:ℂ)•(1:bE))∈nW L k:=
  ⟨1,⟨Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _)),
    LinearMap.mem_ker.mpr (by ext i;simp[gT,rP,row])⟩,
    Prod.ext wD wD⟩
 simpa[Prod.smul_mk,smul_smul] using(nW L k).smul_mem (2:ℂ)⁻¹ a
lemma cL {V W:Type*}
  [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
  [AddCommGroup W] [Module ℂ W] (S:Submodule ℂ V) (f:V→ₗ[ℂ] W):
  Module.finrank ℂ (S.map f)+Module.finrank ℂ (S⊓LinearMap.ker f:Submodule ℂ V)=Module.finrank ℂ S:=by
 have h:=(f.comp S.subtype).finrank_range_add_finrank_ker;rwa [LinearMap.range_comp,Submodule.range_subtype,LinearMap.ker_comp,←Submodule.finrank_map_subtype_eq S,Submodule.map_comap_subtype] at h
lemma wE {L:Submodule ℂ aC} (hL:aD L) (s:p L 2 3=7) (k:F):
  6
   ≤Module.finrank ℂ (M L k)∧
   (Module.finrank ℂ (M L k)=6→
     ∀x y:aH,aA3 k (x,y)∈M L k→(x,y)∈bU L 2 3):=by
 have d:M L k=(bU L 2 3).map (aA3 k):=by rw[M,show tK k=(aA3 k).comp ((row 2).prod (row 3)) by ext x<;>rfl,Submodule.map_comp,rS]
 let K:=LinearMap.ker (aA3 k)
 let c:K→ₗ[ℂ] ℂ× ℂ:=
  {toFun x:=(x.1.1 k,x.1.2 k),map_add' _ _:=rfl,map_smul' _ _:=rfl}
 have a {x:aH} (r:aA2 k x=0) (q:x k=0):x=0:=by
  have n:(4:ℂ)•rP k x=0:=by
   have g:tJ (tJ (rP k x))=(4:ℂ)•rP k x:=by ext i;fin_cases i<;>simp[tJ,Fin.sum_univ_four]<;>ring
   rw[←g];simpa[aA2] using congrArg tJ r
  funext j;by_cases e:j=k
  ·exact e▸q
  ·obtain⟨i,rfl⟩:=Fin.exists_succAbove_eq e;simpa[rP] using congrFun n i
 have o:Function.Injective c:=(injective_iff_map_eq_zero c).mpr fun x l=>
  Subtype.ext (Prod.ext (a (congrArg Prod.fst x.2) (congrArg Prod.fst l))
   (a (congrArg Prod.snd x.2) (congrArg Prod.snd l)))
 have w:Module.finrank ℂ K≤2:=by simpa[Module.finrank_prod] using c.finrank_le_finrank_of_injective o
 have b:=cL (bU L 2 3) (aA3 k);rw[←d,gO hL,s] at b;change Module.finrank ℂ (M L k)+Module.finrank ℂ (bU L 2 3⊓K:Submodule ℂ _)=8 at b;have:=Submodule.finrank_mono (inf_le_right:bU L 2 3⊓K≤K);refine⟨by omega,fun v x y m=> ?_⟩;have f:K≤bU L 2 3:=(Submodule.eq_of_le_of_finrank_le (inf_le_right:bU L 2 3⊓K≤K) (by omega))▸inf_le_left;obtain⟨u,t,h⟩:=d▸m;simpa using(bU L 2 3).add_mem t (f (LinearMap.mem_ker.mpr (by rw[map_sub,h,sub_self]:aA3 k ((x,y)-u)=0)))
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
lemma aE3 (k:F) (a b c d:aH):
  2
   *(aO (bD (Pi.single k 1) b c d)+aO (bD a (-(Pi.single k 1)) c d))=
   -((∑i,rP k c i)*(∑i,rP k d i)-2*∑i,rP k c i*rP k d i)*(∑i,rP k (a-b) i)-
   ∑i,rP k (a-b) i*tJ (rP k c) i*tJ (rP k d) i:=by
 classical
 have r (u v w z:aH) (i:F):
  bD u v w z (0,i)=u i∧bD u v w z (1,i)=v i∧
  bD u v w z (2,i)=w i∧bD u v w z (3,i)=z i:=⟨rfl,rfl,rfl,rfl⟩
 simp only[cK,r,Fin.sum_univ_succAbove _ k,rP,LinearMap.funLeft_apply,tJ,
  LinearMap.coe_mk,AddHom.coe_mk,Pi.sub_apply,Pi.neg_apply,Pi.single_eq_same,
  Pi.single_eq_of_ne (Fin.succAbove_ne _ _),Fin.ne_succAbove,Fin.succAbove_ne,
  Fin.succAbove_right_inj,true_or,false_or,or_true,or_false,ite_true,neg_zero,mul_zero,
  zero_mul,ite_self,sum_const_zero,zero_add,add_zero,one_mul,mul_neg,mul_one]
 simp(config:={decide:=true}) only[Fin.sum_univ_four,ite_true,ite_false,add_zero,zero_add];ring
lemma aDk {L:Submodule ℂ aC} {k:F} (hL:aD L)
  (p:bD (Pi.single k 1) (-(Pi.single k 1)) 0 0∈L)
  {x:aC} (w:x∈bV L):
  (∑i,gT k x i)=0∧
    (∑i,gT k x i*(tK k x).1 i*(tK k x).2 i)=0:=by
 obtain⟨s,t,u,rfl⟩:=zI.mp w
 let c:=rP k (row 2 (aM s t));let d:=rP k (row 3 (aM s t))
 let e:=gT k (aM s t)
 have g (r:ℂ):
   -((∑i,(c+r•1) i)*(∑i,(d+r•1) i)-2*∑i,(c+r•1) i*(d+r•1) i)*(∑i,e i)-
   ∑i,e i*(tJ c+r•(2:ℂ)•1) i*(tJ d+r•(2:ℂ)•1) i=0:=by
  let y:=aM (s+r) t
  have a (v:ℂ):
    aO (bD (row 0 y+v•Pi.single k 1) (row 1 y+v•(-(Pi.single k 1)))
     (row 2 y) (row 3 y))=120*(s+r)^4:=by
   convert bR hL (L.add_mem u (L.smul_mem v p)) (s+r);funext ⟨i,j⟩;fin_cases i<;>simp[y,bD,row,aM,add_assoc]
  have l:=a 0;have e1:=a 1;have e2:=a 2;simp only[zero_smul,one_smul,two_smul,add_zero,lD,iR] at l e1 e2;have h:=(aE3 k (row 0 y) (row 1 y) (row 2 y) (row 3 y)).symm.trans
   (show _=0 by linear_combination 4*e1-e2-3*l)
  have f (j:Fin 4):rP k (row j y)=rP k (row j (aM s t))+r•(1:bE):=by ext i;change s+r+t (j,_)=(s+t (j,_))+r*1;ring
  have q:rP k (row 0 y-row 1 y)=e:=by rw[map_sub,f 0,f 1,add_sub_add_right_eq_sub];rfl
  rw[q,f 2,f 3] at h;simpa only[map_add,map_smul,wD] using h
 have b:=g 0;have m:=g 1;have n:=g (-1);have o:(∑i,e i)=0:=by
  simp only[Fin.sum_univ_four,Pi.add_apply,Pi.smul_apply,Pi.one_apply,smul_eq_mul] at b m n ⊢
  linear_combination-(m+n-2*b)/24
 refine⟨o,?_⟩;simp only[o,mul_zero,zero_smul,add_zero,zero_sub,neg_eq_zero] at b;exact b
lemma wF {L:Submodule ℂ aC} {k:F}
  (c:∀x∈bV L,(∑i,gT k x i*(tK k x).1 i*(tK k x).2 i)=0)
  {x:aC} (d:x∈bV L) {w:bE×bE} (h:w∈nW L k):
  (∑i,gT k x i*w.1 i*w.2 i)=0∧
    (∑i,gT k x i*((tK k x).1 i*w.2 i+w.1 i*(tK k x).2 i))=0:=by
 obtain⟨y,e,rfl⟩:=h;have g:gT k y=0:=e.2;have f:=c x d;have a:=c _ ((bV L).add_mem d e.1);have b:=c _ ((bV L).add_mem d ((bV L).neg_mem e.1));simp only[map_add,map_neg,g,neg_zero,Prod.fst_add,Prod.snd_add,Prod.fst_neg,Prod.snd_neg,Pi.add_apply,Pi.neg_apply,Pi.zero_apply,add_zero,Fin.sum_univ_four] at f a b ⊢
 exact⟨by linear_combination(a+b-2*f)/2,by linear_combination(a-b)/2⟩
lemma qY (S:Submodule ℂ (bE×bE)) (h:bE)
  (e:∀w∈S,(∑i,h i*w.1 i*w.2 i)=0):
  Module.finrank ℂ S+(univ.filter fun i:Fin 4=>h i≠0).card≤8:=by
 classical
 let A:=univ.filter fun i:Fin 4=>h i≠0
 let B:(bE×bE)→ₗ[ℂ] Module.Dual ℂ (bE×bE):=
  LinearMap.mk₂ ℂ (fun a b=>∑i,h i*(a.1 i*b.2 i+a.2 i*b.1 i))
   (by intros;simp[Fin.sum_univ_four];ring) (by intros;simp[Fin.sum_univ_four];ring)
   (by intros;simp[Fin.sum_univ_four];ring) (by intros;simp[Fin.sum_univ_four];ring)
 have k:S.map B≤S.dualAnnihilator:=by
  rintro _ ⟨a,g,rfl⟩;rw[Submodule.mem_dualAnnihilator];intro b j;have c:=e (a+b) (S.add_mem g j);have d:=e a g;have f:=e b j;simp only[B,LinearMap.mk₂_apply,Prod.fst_add,Prod.snd_add,Pi.add_apply,Fin.sum_univ_four] at c d f ⊢
  linear_combination c-d-f
 have o:=fO (LinearMap.ker B) Aᶜ fun z m _ i n=>by
  have l:h i≠0:=by simpa[A] using n
  have c:=LinearMap.congr_fun (LinearMap.mem_ker.mp m) (0,Pi.single i 1);have d:=LinearMap.congr_fun (LinearMap.mem_ker.mp m) (Pi.single i 1,0);simp[B,Pi.single_apply,l] at c d;exact⟨c,d⟩
 rw[card_compl,Fintype.card_fin] at o;have:=Submodule.finrank_mono (inf_le_right:S⊓LinearMap.ker B≤LinearMap.ker B);have:=Submodule.finrank_mono k;have:=Subspace.finrank_add_finrank_dualAnnihilator_eq S;have:=cL S B;have:Module.finrank ℂ (bE×bE)=8:=by rw[Module.finrank_prod,Module.finrank_fin_fun]
 have:A.card≤4:=by simpa using card_le_univ A
 change Module.finrank ℂ S+A.card≤8;omega
lemma wG {S:Submodule ℂ (bE×bE)} {h:bE}
  (g:∀w∈S,(∑i,h i*w.1 i*w.2 i)=0)
  (o:8≤Module.finrank ℂ S+(univ.filter fun i:Fin 4=>h i≠0).card)
  {z:bE×bE} (f:(∑i,h i*z.1 i*z.2 i)=0)
  (l:∀u∈S,(∑i,h i*(z.1 i*u.2 i+u.1 i*z.2 i))=0):z∈S:=by
 by_contra j;have a:∀w∈S⊔Submodule.span ℂ {z},(∑i,h i*w.1 i*w.2 i)=0:=by
  intro w n;obtain⟨u,e,_,m,rfl⟩:=Submodule.mem_sup.mp n;obtain⟨c,rfl⟩:=Submodule.mem_span_singleton.mp m;have b:=g u e;have d:=l u e;simp only[Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Fin.sum_univ_four] at b d f ⊢
  linear_combination b+c*d+c^2*f
 have k:=qY _ h a;rw[Submodule.finrank_sup_span_singleton j] at k;omega
lemma qZ (S:Submodule ℂ (bE×bE)) (m:((1,1):bE×bE)∈S)
  (A:Finset (Fin 4)) (b:Fin 4)
  (j:∀w∈S,∀i∈A,w.1 i*w.2 i=w.1 b*w.2 b):
  Module.finrank ℂ S≤2*(insert b Aᶜ).card:=
 fO S (insert b Aᶜ) fun w k l i n=>by
  classical
  have e:i∈A:=by simpa using fun h=>n (mem_insert_of_mem h)
  have⟨c,d⟩:=l b (mem_insert_self _ _);have a:=j w k i e;rw[c,d,zero_mul] at a;have g:=j (w+(1,1)) (S.add_mem k m) i e;simp only[Prod.fst_add,Prod.snd_add,Pi.add_apply,Pi.one_apply,c,d,zero_add] at g;have f:w.1 i=0:=mul_self_eq_zero.mp (by linear_combination w.1 i*(g-a)-a);exact⟨f,by linear_combination g-a-f⟩
lemma uG (a b:bE):
  ∃c:ℂ,∀i,a i+c*b i=0→a i=0∧b i=0:=by
 classical
 obtain⟨c,f⟩:=Infinite.exists_notMem_finset (univ.image fun i:Fin 4=> -a i/b i);refine⟨c,fun i e=> ?_⟩;by_cases d:b i=0
 ·exact⟨by simpa[d] using e,d⟩
 ·exact(f (mem_image.mpr ⟨i,mem_univ _,(div_eq_iff d).mpr (by linear_combination-e)⟩)).elim
lemma qK {L:Submodule ℂ aC} (hL:aD L)
  (N:p L 2 3=7) {k:F} (E:Module.finrank ℂ (M L k)=6) (j:Fin 4)
  (B:(Pi.single j 1,0)∈M L k) (C:(0,Pi.single j 1)∈M L k):False:=by
 have f:=(wE hL N k).2 E
 let v:aH:=(2:ℂ)•Pi.single (k.succAbove j) 1
 have z:aA2 k (v-1)=(-4:ℂ)•Pi.single j 1:=by
  have J:rP k (v-1)=(2:ℂ)•Pi.single j 1-1:=by ext a;simp[rP,v,Pi.single_apply]
  rw[aA2,LinearMap.comp_apply,J];ext a;fin_cases j<;>fin_cases a<;>norm_num[tJ,Fin.sum_univ_four]
 have left:=f (v-1) 0 (by simpa[aA3,z,Prod.smul_mk] using(M L k).smul_mem (-4:ℂ) B);have right:=f 0 (v-1) (by simpa[aA3,z,Prod.smul_mk] using(M L k).smul_mem (-4:ℂ) C);have A:(v,v)∈bU L 2 3:=by
  simpa[Prod.mk_add_mk] using(bU L 2 3).add_mem ((bU L 2 3).add_mem left right)
   (Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _)))
 have b {u:aC} (P:u∈L) {r:Fin 4} {c:ℂ} (hz:row r (aM c u)=0):c=0:=by
  have n:aO (aM c u)=0:=sum_eq_zero fun e _=>prod_eq_zero (mem_univ r) (congrFun hz (e r))
  rw[bR hL P] at n;simpa using n
 obtain⟨a,t,y,K,O⟩:=gP left;have G:a=0:=b y O;obtain⟨s,m,q,i,w⟩:=gP A;have x:s-1=0:=b (r:=2) (L.sub_mem q y) (by
  ext c;have g:=congrFun K c;have h:=congrFun i c;simp only[row,LinearMap.funLeft_apply,aM,Pi.sub_apply,Pi.one_apply,Pi.zero_apply,G] at g h ⊢
  linear_combination h-g)
 have l:aO (aM s m)=0:=cD (aM s m) 2 3 (by decide) fun c d o=>by
  change row 2 (aM s m) c*row 3 (aM s m) d+row 2 (aM s m) d*row 3 (aM s m) c=0;rw[i,w];by_cases H:c=k.succAbove j
  ·subst c;simp[v,o.symm]
  ·simp[v,H]
 rw[bR hL q,sub_eq_zero.mp x] at l;norm_num at l
lemma nX {L:Submodule ℂ aC} {k:F}
  (hL:aD L) (hp:p L 2 3=7) (hU:bD (Pi.single k 1) (-(Pi.single k 1)) 0 0∈L):
  Module.finrank ℂ (D L k)=0:=by
 classical
 have P (x:aC) (g:x∈bV L):=aDk hL hU g
 let d:Module.Dual ℂ bE:=∑i:Fin 4,LinearMap.proj i
 have C:D L k≤LinearMap.ker d:=by rintro h ⟨x,g,rfl⟩;rw[LinearMap.mem_ker];simpa[d] using(P x g).1
 have r (a b:Fin 4):(Pi.single a 1-Pi.single b 1:bE)∈LinearMap.ker d:=by rw[LinearMap.mem_ker];simp[d,sum_sub_distrib,Pi.single_apply]
 have V:Module.finrank ℂ (LinearMap.ker d)=3:=by have:=Module.Dual.finrank_ker_add_one_of_ne_zero (show d≠0 from fun h=>by have:=congrArg (fun f:Module.Dual ℂ bE=>f 1) h;simp[d] at this);have:Module.finrank ℂ bE=4:=Module.finrank_fin_fun ℂ;omega
 have b5:Module.finrank ℂ (D L k)≤3:=(Submodule.finrank_mono C).trans_eq V;have b6:=(wE hL hp k).1;have b7:Module.finrank ℂ (M L k)≤Module.finrank ℂ (nW L k)+Module.finrank ℂ (D L k):=by
  have J:=cL (bV L) (tK k);have K:=cL (bV L) (gT k);have h3:=cL (bV L⊓LinearMap.ker (gT k)) (tK k);have:=Submodule.finrank_mono (inf_le_inf_right (LinearMap.ker (tK k))
   (inf_le_left:bV L⊓LinearMap.ker (gT k)≤bV L))
  change Module.finrank ℂ (M L k)+_=_ at J;change Module.finrank ℂ (D L k)+_=_ at K;change Module.finrank ℂ (nW L k)+_=_ at h3;omega
 have s {h:bE} (N:h∈D L k) {w:bE×bE} (m:w∈nW L k):
   (∑i,h i*w.1 i*w.2 i)=0:=by
  obtain⟨x,g,rfl⟩:=N;exact(wF (fun _ g=>(P _ g).2) g m).1
 have l {b:Fin 4} {A:Finset (Fin 4)}
   (hA:∀i∈A,(Pi.single i 1-Pi.single b 1:bE)∈D L k):
   ∀w∈nW L k,∀i∈A,w.1 i*w.2 i=w.1 b*w.2 b:=fun w m i o=>by
  simpa[Pi.single_apply,sub_mul,ite_mul,sum_sub_distrib,sub_eq_zero] using s (hA i o) m
 by_contra b9;rcases (show Module.finrank ℂ (D L k)=1∨Module.finrank ℂ (D L k)=2∨Module.finrank ℂ (D L k)=3 by omega) with J|K|h3
 ·obtain⟨v,hv,a4⟩:=finrank_eq_one_iff'.mp J
  let h:=v.val
  have hn:h≠0:=fun e=>hv (Subtype.ext e)
  have hs:(∑i,h i)=0:=by simpa[d] using C v.2
  have hq:∀w∈M L k,(∑i,h i*w.1 i*w.2 i)=0:=by
   rintro w ⟨x,g,rfl⟩;obtain⟨c,he⟩:=a4 ⟨gT k x,⟨x,g,rfl⟩⟩;have e:c•h=gT k x:=congrArg Subtype.val he;by_cases y:c=0
   ·exact s v.2 ⟨x,⟨g,by simpa[y] using e.symm⟩,rfl⟩
   ·have q:=(P x g).2;rw[←e] at q;simp only[Pi.smul_apply,smul_eq_mul,mul_assoc,←mul_sum] at q;simpa only[mul_assoc] using(mul_eq_zero.mp q).resolve_left y
  have b8:2≤(univ.filter fun i:Fin 4=>h i≠0).card:=by
   by_contra! b3;obtain⟨a,O⟩:=Function.ne_iff.mp hn;change h a≠0 at O;have:(∑i,h i)=h a:=Fintype.sum_eq_single a fun b n=>by by_contra a7;exact n ((card_le_one_iff.mp (Nat.le_of_lt_succ b3)) (by simp[a7]) (by simp[O]))
   exact O (this.symm.trans hs)
  have b4:=qY (M L k) h hq;have⟨j,U⟩:∃j,h j=0:=by by_contra! a2;simp[a2] at b4;omega
  exact qK hL hp (by omega) j
   (wG hq (by omega) (by simp) fun u _=>by simp[Pi.single_apply,mul_ite,U])
   (wG hq (by omega) (by simp) fun u _=>by simp[Pi.single_apply,mul_ite,U])
 ·let B:=Module.finBasisOfFinrankEq ℂ (D L k) K
  obtain⟨c0,b0⟩:=uG (B 0).val (B 1).val;by_cases G:∀i,((B 0).val+c0•(B 1).val) i≠0
  ·obtain⟨b,n,a8⟩:=(D L k).add_mem (B 0).2 ((D L k).smul_mem c0 (B 1).2);have Q:∀i,gT k b i≠0:=a8▸G;have mb {x:aC} (g:x∈bV L) (hf:∀i,gT k x i≠0):
     tK k x∈nW L k:=
    wG (fun _ m=>s ⟨x,g,rfl⟩ m) (by simp[hf];omega) (P x g).2 fun _ m=>(wF (fun _ g=>(P _ g).2) g m).2
   have a3:=qY (nW L k) (gT k b) fun _ m=>s ⟨b,n,rfl⟩ m
   simp[Q] at a3;have S:M L k≤nW L k:=by
    rintro _ ⟨x,g,rfl⟩;obtain⟨c,a9⟩:=uG (gT k x) (gT k b);have R:=mb ((bV L).add_mem g ((bV L).smul_mem c n)) fun i y=>Q i (a9 i (by simpa[map_add,map_smul] using y)).2
    rw[map_add,map_smul] at R;exact((nW L k).add_mem_iff_left ((nW L k).smul_mem c (mb n Q))).mp R
   have:=Submodule.finrank_mono S;omega
  ·obtain⟨j,b1⟩:∃j,((B 0).val+c0•(B 1).val) j=0:=by simpa using G
   have⟨a5,a6⟩:=b0 j b1;have U:∀h∈D L k,h j=0:=fun h N=>by have e:=congrArg (fun v:D L k=>v.val j) (B.sum_repr ⟨h,N⟩);rw[Fin.sum_univ_two] at e;simpa[a5,a6] using e.symm
   obtain⟨b,n⟩:=exists_ne j
   let T:=LinearMap.ker d⊓LinearMap.ker (LinearMap.proj j:bE→ₗ[ℂ] ℂ)
   have X:D L k≤T:=fun h N=>⟨C N,U h N⟩
   have a1:D L k=T:=Submodule.eq_of_le_of_finrank_eq X (by have:=Submodule.finrank_lt_finrank_of_lt (lt_iff_le_not_ge.mpr ⟨inf_le_left,fun h=>by have:(Pi.single j 1-Pi.single b 1:bE) j=0:=(h (r j b)).2;simp[Ne.symm n] at this⟩:T<LinearMap.ker d);have:=Submodule.finrank_mono X;omega);have H:=l (b:=b) (A:={j}ᶜ) fun i o=>by rw[a1];exact⟨r i b,by change(Pi.single i 1-Pi.single b 1:bE) j=0;simp[Ne.symm (by simpa using o:i≠j),Ne.symm n]⟩
   have E:(insert b ({j}ᶜ:Finset (Fin 4))ᶜ).card=2:=by simp[compl_compl,card_pair n]
   have t:=qZ (nW L k) (tM L k) ({j}ᶜ) b H;rw[E] at t;have Z {z:bE×bE} (y:∀i≠j,z.1 i=0∧z.2 i=0):z∈M L k:=by
    have hm:z∈nW L k:=by
     by_contra O;have b2:=qZ (nW L k⊔Submodule.span ℂ {z}) (Submodule.mem_sup_left (tM L k))
      ({j}ᶜ) b fun w m i o=>by
        obtain⟨u,hu,_,hv,rfl⟩:=Submodule.mem_sup.mp m;obtain⟨c,rfl⟩:=Submodule.mem_span_singleton.mp hv;have J:=y i (by simpa using o);have K:=y b n;simpa[J.1,J.2,K.1,K.2] using H u hu i o
     rw[Submodule.finrank_sup_span_singleton O,E] at b2;omega
    exact(Submodule.map_mono inf_le_left:nW L k≤M L k) hm
   exact qK hL hp (by omega) j
    (Z fun i o=>⟨Pi.single_eq_of_ne o 1,rfl⟩)
    (Z fun i o=>⟨rfl,Pi.single_eq_of_ne o 1⟩)
 ·have a0:D L k=LinearMap.ker d:=
   Submodule.eq_of_le_of_finrank_eq C (h3.trans V.symm)
  have t:=qZ (nW L k) (tM L k) univ 0
   (l fun i _=>a0▸r i 0)
  simp at t;omega
lemma lX {L:Submodule ℂ aC} {k:F}
  (hL:aD L) (i:aX L=8) (m:p L 2 3=7)
  (b:bD (Pi.single k 1) (-(Pi.single k 1)) 0 0∈L):
  ∃S:Submodule ℂ aC,S≤L∧aD S∧aX S=7∧∀t∈S,row 0 t=row 1 t:=by
 have e:=nX hL m b
 let f:=((LinearMap.proj k:aH→ₗ[ℂ] ℂ).comp (row 0-row 1)).comp L.subtype
 have g:f≠0:=fun l=>by have h:=LinearMap.congr_fun l ⟨bD (Pi.single k 1) (-(Pi.single k 1)) 0 0,b⟩;change(Pi.single k 1:aH) k- -((Pi.single k 1:aH) k)=0 at h;norm_num at h
 let S:=(LinearMap.ker f).map L.subtype
 have a:S≤L:=by rintro _ ⟨v,_,rfl⟩;exact v.2
 refine⟨S,a,fun t n=>hL _ (a n),?_,?_⟩
 ·have:=Module.Dual.finrank_ker_add_one_of_ne_zero g;have q:aX S=Module.finrank ℂ (LinearMap.ker f):=Submodule.finrank_map_subtype_eq _ _;change Module.finrank ℂ L=8 at i;omega
 ·rintro _ ⟨v,o,rfl⟩;have dt:gT k v.1∈D L k:=⟨v.1,Submodule.mem_sup_left v.2,rfl⟩
  rw[Submodule.finrank_eq_zero.mp e,Submodule.mem_bot] at dt;funext c;by_cases d:c=k
  ·exact d▸sub_eq_zero.mp (show f v=0 from o)
  ·obtain⟨j,rfl⟩:=Fin.exists_succAbove_eq d;exact sub_eq_zero.mp (congrFun dt j)
lemma iT {L:Submodule ℂ aC} (hL:aD L)
  (v:aX L=8) (m:p L 2 3=7) (H:∀i,u L i=0):
  (∃S:Submodule ℂ aC,S≤L∧aD S∧aX S=7∧∀t∈S,row 0 t=row 1 t)∨
  (∃a b:aH,bD a b 0 0≠0∧bD a b 0 0∈L∧
    aJ L 2 3=Submodule.span ℂ {bD a b 0 0}∧
    ∃
     i j:F,i≠j∧a i≠0∧a j≠0∧b i≠0∧b j≠0∧
     (∀k,k≠i→k≠j→a k=0∧b k=0)∧
     aL a b i j=0∧a i*b j-a j*b i≠0∧cS a≠0∧cS b≠0):=by
 obtain⟨a,b,G,l,E,B|C⟩:=lE hL v m H
 ·obtain⟨k,w,_,A,d⟩:=B;have z:(a k)⁻¹ •bD a b 0 0=bD (Pi.single k 1) (-(Pi.single k 1)) 0 0:=by
   ext ⟨r,c⟩;fin_cases r<;>try (change(a k)⁻¹ *0=0;ring)
   ·by_cases e:c=k<;>simp[bD,e,w,fun h=>(d c h).1]
   ·by_cases e:c=k<;>simp[bD,A,e,w,fun h=>(d c h).1]
  exact Or.inl (lX hL v m (z▸L.smul_mem _ l))
 ·obtain⟨i,j,f,n,o,q,s,d,g,x,y⟩:=C;exact Or.inr ⟨a,b,G,l,E,i,j,f,n,o,q,s,d,fB hL m l i j f,g,x,y⟩
end Ac.A4
namespace Ac.Aq
open Aa Ae Finset
abbrev bE:=Fin 4→ℂ
abbrev jH:=Fin 2×Fin 3→ℂ
abbrev aG:aC→ₗ[ℂ] bE:=LinearMap.funLeft ℂ ℂ ![(2,0),(2,1),(3,0),(3,1)]
abbrev aB:aC→ₗ[ℂ] jH:=LinearMap.funLeft ℂ ℂ fun a=>(Fin.natAdd 2 a.1,Fin.natAdd 2 a.2)
def per (x:bE):ℂ:=x 0*x 3+x 1*x 2
abbrev aP (L:Submodule ℂ aC):=L⊓LinearMap.ker aB
def dB (Y:aC):ℂ:=
 Y (0,2)*(Y (1,3)+Y (1,4))+Y (0,3)*(Y (1,2)+Y (1,4))+
 Y (0,4)*(Y (1,2)+Y (1,3))
def fL (Y U:aC) (q:Fin 4) (j:Fin 5):=
 Y (q,1)*(U (1,0)*Y (0,j)+U (0,0)*Y (1,j))+
 Y (q,0)*(U (1,1)*Y (0,j)+U (0,1)*Y (1,j))
def iH (Y U T:aC) (r q:Fin 4):ℂ:=
 fL Y U q 2*(T (r,3)+T (r,4))+fL Y U q 3*(T (r,2)+T (r,4))+
 fL Y U q 4*(T (r,2)+T (r,3))
def lY (Y U T:aC) (f:Fin 4→Fin 5):ℂ:=
 let y (i:Fin 4):=Y (i,f i)
 let x (i j:Fin 4):=U (i,f i)*T (j,f j)+T (i,f i)*U (j,f j)
 x 0 1*y 2*y 3+x 0 2*y 1*y 3+x 0 3*y 1*y 2+
 x 1 2*y 0*y 3+x 1 3*y 0*y 2+x 2 3*y 0*y 1
def iw (w:(Fin 4→Fin 5)→ℂ):ℂ:=∑e:Fin 4 ↪ Fin 5,w e
lemma iI {V W:Type*} [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W]
  (L:Submodule ℂ V) (f:V→ₗ[ℂ] W):
  Module.finrank ℂ (L.map f)+Module.finrank ℂ (L⊓LinearMap.ker f:Submodule ℂ V)=Module.finrank ℂ L:=by
 rw[←(Submodule.submoduleOfEquivInf _ _).finrank_eq,
  ←(f.submoduleMap L).finrank_range_add_finrank_ker,
  LinearMap.range_submoduleMap,LinearMap.ker_submoduleMap]
 simp
lemma rA (L:Submodule ℂ aC):
  Module.finrank ℂ (L.map aB)+Module.finrank ℂ ((aP L).map aG)=p L 2 3:=by
 have a:(aP L⊓LinearMap.ker aG:Submodule ℂ aC)=
   L⊓LinearMap.ker ((row 2).prod (row 3)):=by
  ext Y;simp[aP,funext_iff,Prod.forall,Fin.forall_fin_succ];tauto
 have:=iI L aB;have:=iI (aP L) aG;have:=iI L ((row 2).prod (row 3));rw[a] at*;unfold p aP at*;omega
lemma iU {L:Submodule ℂ aC} (h:(1:jH)∉L.map aB):
  ∃
   f:Module.Dual ℂ jH,f≠0∧f 1=1∧
   ∀(Y:aC) (s:ℂ),Ae.aR L Y s→f (aB Y)=s:=by
 obtain⟨g,a,b⟩:=Submodule.exists_dual_map_eq_bot_of_notMem h inferInstance;refine⟨(g 1)⁻¹ •g,smul_ne_zero (inv_ne_zero a) fun j=>a (by simp[j]),inv_mul_cancel₀ a,?_⟩;rintro Y s ⟨v,e,rfl⟩;have d:g (aB v)=0:=(Submodule.mem_bot ℂ).mp (by rw[←b];exact⟨_,⟨v,e,rfl⟩,rfl⟩);have c:aB (aM s v)=s•(1:jH)+aB v:=by ext i;simp[aM]
 simp[c,d,mul_left_comm,inv_mul_cancel₀ a]
lemma iJ {L:Submodule ℂ aC} {Y T:aC} {s u:ℂ}
  (f:aR L Y s) (e:aR L T u) (k:ℂ):
  aR L (Y+k•T) (s+k*u):=by
 obtain⟨a,c,rfl⟩:=f;obtain⟨b,d,rfl⟩:=e;exact⟨a+k•b,L.add_mem c (L.smul_mem k d),by ext i;simp[aM];ring⟩
lemma uH {L:Submodule ℂ aC} (hL:aD L) {Y U T:aC} {s u:ℂ}
  (a:aR L Y s) (d:U∈L) (b:aR L T u):
  (∀k:ℂ,aO (Y+k•(U+T))=aO (Y+k•T))∧
  (∀k:ℂ,aO (Y+k•U)=aO Y):=by
 have c:aR L U 0:=⟨_,d,by ext i;simp[aM]⟩
 exact⟨fun k=>by
   rw[fU hL (iJ a (by simpa using iJ c b 1) k),fU hL (iJ a b k)],
  fun k=>by rw[fU hL (iJ a c k),fU hL a];simp⟩
lemma rB (f:Fin 5→ℂ):
  ∑i,f i=f 0+f 1+f 2+f 3+f 4:=by
 simp[Fin.sum_univ_five,add_assoc]
lemma aHg (f:Fin 5→ℂ):∑j,f j=f 0+f 1+f 2+f 3+f 4:=rB f
lemma aB3 {Y:aC} {z:jH} (a:aB Y=z) (r:Fin 4) (c:Fin 5)
  (d:2≤ r.val) (b:2≤ c.val):
  Y (r,c)=z (⟨r.val-2,by omega⟩,⟨c.val-2,by omega⟩):=by
 subst a;congr 1;ext<;>simp<;>omega
set_option maxHeartbeats 3000000 in
lemma eW {Y:aC} (a:aB Y=0):
  aO Y=per (aG Y)*dB Y:=by
 change aO Y=(Y (2,0)*Y (3,1)+Y (2,1)*Y (3,0))*dB Y;rw[cK];simp(config:={decide:=true}) (disch:=decide) only[rB,ite_true,ite_false,aB3 a,Pi.zero_apply,zero_mul,mul_zero,add_zero,zero_add,dB];ring
lemma iK {L:Submodule ℂ aC} (k:p L 2 3=7)
  (h:(1:jH)∉L.map aB):
  let V:=L⊔Submodule.span ℂ {(1:aC)}
  aP V=aP L∧
  Module.finrank ℂ (V.map aB)=Module.finrank ℂ (L.map aB)+1∧
  Module.finrank ℂ (V.map aB)+Module.finrank ℂ ((aP V).map aG)=8∧
  4≤Module.finrank ℂ (V.map aB)∧Module.finrank ℂ (V.map aB)≤6:=by
 intro V;obtain⟨f,-,-,hf⟩:=iU h;have b:aP V=aP L:=le_antisymm (fun Y ⟨j,e⟩=>by obtain⟨v,d,_,g,rfl⟩:=Submodule.mem_sup.mp j;obtain⟨s,rfl⟩:=Submodule.mem_span_singleton.mp g;have c:=hf (v+s•(1:aC)) s ⟨v,d,by ext i;simp[aM];ring⟩;rw[show aB (v+s•(1:aC))=0 from e,map_zero] at c;exact⟨by simpa[←c] using d,e⟩) (inf_le_inf le_sup_left le_rfl);have a:Module.finrank ℂ (V.map aB)=Module.finrank ℂ (L.map aB)+1:=by dsimp only[V];rw[Submodule.map_sup,Submodule.map_span,Set.image_singleton];exact Submodule.finrank_sup_span_singleton h
 have:=rA L;have:=Submodule.finrank_le ((aP L).map aG);have:=Submodule.finrank_le (V.map aB);have:Module.finrank ℂ bE=4:=by simp[bE]
 have:Module.finrank ℂ jH=6:=by simp[jH]
 exact⟨b,a,by rw[b,a];omega,by omega,by omega⟩
lemma jL (Y U T:aC)
  (b:∀k:ℂ,aO (Y+k•(U+T))=aO (Y+k•T))
  (a:∀k:ℂ,aO (Y+k•U)=aO Y):
  (∑e:Fin 4 ↪ Fin 5,lY Y U T e)=0:=by
 let q (s:ℂ) (e:Fin 4 ↪ Fin 5):=∏i,(Y+s•(U+T)) (i,e i)- ∏i,(Y+s•U) (i,e i)- ∏i,(Y+s•T) (i,e i)
 have d (s:ℂ):∑e,q s e= -aO Y:=by simp only[q,sum_sub_distrib];change aO (Y+s•(U+T))-aO (Y+s•U)-aO (Y+s•T)= -aO Y;rw[b,a];ring
 have c (e:Fin 4 ↪ Fin 5):
   24*lY Y U T e=16*(q 1 e+q (-1) e)-(q 2 e+q (-2) e)-30*q 0 e:=by
  simp[q,lY,Fin.prod_univ_four];ring
 apply mul_left_cancel₀ (show(24:ℂ)≠0 by norm_num);rw[mul_zero,mul_sum];simp_rw[c];simp only[sum_sub_distrib,sum_add_distrib,←mul_sum,d];ring
lemma aDl (w:(Fin 4→Fin 5)→ℂ):
  iw w=∑j,∑l,∑m,∑n,
   if j=l∨j=m∨j=n∨l=m∨l=n∨m=n then 0 else
   w ![j,l,m,n]:=by
 classical
 have h:∀a b c d:Fin 5,Function.Injective ![a,b,c,d]↔¬(a=b∨a=c∨a=d∨b=c∨b=d∨c=d):=by decide
 let e:(Fin 5×Fin 5×Fin 5×Fin 5)≃(Fin 4→Fin 5):=
  ⟨fun p=> ![p.1,p.2.1,p.2.2.1,p.2.2.2],fun z=>(z 0,z 1,z 2,z 3),
   fun _=>rfl,fun z=>by ext i;fin_cases i<;>rfl⟩
 have f (a b c d):e (a,b,c,d)= ![a,b,c,d]:=rfl;have A:iw w=∑z:Fin 4→Fin 5,if Function.Injective z then w z else 0:=by rw[iw,←(Equiv.subtypeInjectiveEquivEmbedding _ _).sum_comp,←Finset.sum_filter];exact(Finset.sum_subtype _ (by simp) w).symm
 rw[A,←e.sum_comp];simp only[Fintype.sum_prod_type,f,h,ite_not]
lemma yL (a b c d x y:ℂ) (g:a*d-b*c≠0)
 (e:a*x+b*y=0) (f:c*x+d*y=0):x=0∧y=0:=by grind
set_option maxHeartbeats 5000000 in
lemma dC {L:Submodule ℂ aC} (hL:aD L) {Y U T:aC} {s u:ℂ}
  (h:aR L Y s) (d:U∈L) (g:aR L T u)
  (f:∀r c,(2≤ r.val∨2≤ c.val)→U (r,c)=0) (e:aB Y=0):
  iH Y U T 2 3+iH Y U T 3 2=0:=by
 obtain⟨a,b⟩:=uH hL h d g;rw[←(aDl (lY Y U T)).symm.trans (jL Y U T a b)];simp(config:={decide:=true}) (disch:=decide) only[aHg,ite_true,ite_false,
  lY,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
  Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,f,aB3 e,Pi.zero_apply,
  zero_add,add_zero,zero_mul,mul_zero,iH,fL]
 ring
lemma oP {L:Submodule ℂ aC} (hL:aD L) {Y U:aC} {s:ℂ}
  (h:aR L Y s) (d:U∈L)
  (g:∀r c,(2≤ r.val∨2≤ c.val)→U (r,c)=0) (e:aB Y=0)
  (f:∀z:jH,∃T u,aR L T u∧aB T=z)
  (i:Fin 2) (j:Fin 3):fL Y U (Fin.natAdd 2 i) (Fin.natAdd 2 j)=0:=by
 let z:jH:=fun p=>if p.1≠i then if p.2=j then-1 else 1 else 0
 obtain⟨T,u,b,k⟩:=f z;have a:=dC hL h d b g e;simp(config:={decide:=true}) (disch:=decide) only[iH,aB3 k,z] at a;fin_cases i<;>fin_cases j<;>norm_num[Fin.natAdd,Fin.ext_iff] at a ⊢ <;>exact a
lemma cB {L:Submodule ℂ aC} (hL:aD L) (hp:p L 2 3=7)
  {U:aC} (hU:U∈L) (E:∀r c,(2≤ r.val∨2≤ c.val)→U (r,c)=0)
  (a0:U (0,0)*U (1,1)-U (0,1)*U (1,0)≠0):(1:jH)∉L.map aB:=by
 rintro⟨w,hw,ew⟩
 let t:= -w
 have V:t∈L:=L.neg_mem hw;have hz:aB (1+t)=0:=by rw[map_add,show aB 1=1 from rfl,map_neg,ew,add_neg_cancel]
 let S:=(aP L).map aG
 let x:=aG (1+t)
 have e {v} (G:v∈S):per (x+v)≠0:=by
  obtain⟨u,⟨F,X⟩,rfl⟩:=G;have d:aO (1+t+u)=120:=by rw[add_assoc];exact hL _ (L.add_mem V F)
  rw[eW (by simp[hz,show aB u=0 from X]),aG.map_add (1+t) u] at d;intro J;simp[x] at J;simp[J] at d
 have K:Module.finrank ℂ S≤1:=by
  have B {u} (F:u∈S):per u=0∧u 0*x 3+u 1*x 2+u 2*x 1+u 3*x 0=0:=by
   let b:=u 0*x 3+u 1*x 2+u 2*x 1+u 3*x 0
   have Q (s:ℂ):per u*(s*s)+b*s+per x≠0:=by convert e (S.smul_mem s F) using 1;simp[per,b];ring
   have N:per u=0:=by_contra fun C=>let⟨s,E⟩:=exists_quadratic_eq_zero C (IsAlgClosed.isSquare _);Q s E
   exact⟨N,by_contra fun hb=>Q (-per x/b) (by simp[N,mul_div_cancel₀ _ (show b≠0 from hb)])⟩
  by_contra! A;obtain⟨f,O⟩:=exists_linearIndependent_of_le_finrank (R:=ℂ) (M:=S) A;have⟨u0,ux⟩:=B (f 0).2;have⟨v0,vx⟩:=B (f 1).2;have⟨uv,_⟩:=B (S.add_mem (f 0).2 (f 1).2);have hx:per x≠0:=by simpa using e S.zero_mem
  obtain⟨i,hi⟩:∃i,(f 0:bE) i≠0:=Function.ne_iff.mp (Subtype.coe_ne_coe.mpr (O.ne_zero 0));have H (j:Fin 4):(f 1:bE) i*(f 0:bE) j-(f 0:bE) i*(f 1:bE) j=0:=by fin_cases i<;>fin_cases j<;>simp[per] at u0 ux v0 vx uv hx ⊢ <;>grind
  exact hi (by simpa using(linearIndependent_iff'.mp O univ ![(f 1:bE) i,-(f 0:bE) i]
   (by ext j;simpa[Fin.sum_univ_two,sub_eq_add_neg] using H j) 1 (mem_univ _)))
 have y:Module.finrank ℂ jH=6:=by simp[jH]
 have g:=rA L;have l:L.map aB= ⊤ :=Submodule.eq_top_of_finrank_eq (by have:=Submodule.finrank_le (L.map aB);dsimp only[S] at K;omega);have P:(aP L).map aG≠ ⊥ :=fun h=>by rw[l,finrank_top,y,h,finrank_bot,hp] at g;omega
 obtain⟨_,⟨v,⟨G,hd⟩,rfl⟩,Z⟩:=Submodule.exists_mem_ne_zero_of_ne_bot P;obtain⟨i,C⟩:∃i,aG v i≠0:=Function.ne_iff.mp Z
 let c:= -aG (1+t) i/aG v i
 let Y:aC:=1+t+c•v
 have n:aR L Y 1:=⟨t+c•v,L.add_mem V (L.smul_mem c G),by ext k;simp[Y,aM,add_assoc]⟩
 have o:aB Y=0:=by simp[Y,hz,show aB v=0 from hd]
 have a:per (aG Y)*dB Y=120:=(eW o).symm.trans (by simpa using fU hL n);have m:aG Y i=0:=by simp[Y,c,aG] at C ⊢;field_simp;ring
 have a1:Y (2,1)*Y (3,0)-Y (2,0)*Y (3,1)≠0:=fun h=>by fin_cases i<;>simp[aG,per] at m a<;>simp[m] at h a<;>grind
 have wt:=oP hL n hU E o fun z=>
  let⟨T,hT,eT⟩:=(l▸trivial:z∈L.map aB)
  ⟨T,0,⟨T,hT,by ext k;simp[aM]⟩,eT⟩
 have q (j:Fin 3):Y (0,Fin.natAdd 2 j)=0:=by have A:fL Y U 2 (Fin.natAdd 2 j)=0:=wt 0 j;have h3:fL Y U 3 (Fin.natAdd 2 j)=0:=wt 1 j;simp only[fL] at A h3;grind
 simp[dB,show Y (0,2)=0 from q 0,show Y (0,3)=0 from q 1,show Y (0,4)=0 from q 2] at a
lemma nN {L:Submodule ℂ aC} (hL:aD L) (d:p L 2 3=7)
  {U:aC} (e:U∈L) (g:∀r c,(2≤ r.val∨2≤ c.val)→U (r,c)=0)
  (a:U (0,0)*U (1,1)-U (0,1)*U (1,0)≠0):
  Module.finrank ℂ (L.map aB)≤5∧
   ∃
    f:Module.Dual ℂ jH,f≠0∧f 1=1∧
    ∀(Y:aC) (s:ℂ),aR L Y s→f (aB Y)=s:=by
 have b:=cB hL d e g a;have⟨_,h,_,_,i⟩:=iK d b;exact⟨by omega,iU b⟩
lemma oQ {L:Submodule ℂ aC} (hL:aD L) (g:p L 2 3=7)
  {a b:aH} (d:bD a b 0 0∈L)
  (i:∀k:Fin 5,k≠0→k≠1→a k=0∧b k=0)
  (e:a 0*b 1-a 1*b 0≠0):
  ∃
   f:Module.Dual ℂ jH,f≠0∧f 1=1∧
   ∀(Y:aC) (s:ℂ),aR L Y s→f (aB Y)=s:=
 (nN hL g d (fun r c h=>by
   fin_cases r<;>try rfl
   all_goals have:=i c (by rintro rfl;simp at h) (by rintro rfl;simp at h);simp[bD,this]) e).2
end Ac.Aq
namespace Ac.An
open Aa Matrix
lemma qL (a b:aH):(Ag.dL a b).IsSymm:=by apply Matrix.IsSymm.ext;intro i j;simp[Ag.dL,eq_comm,and_left_comm,and_assoc,and_comm]
lemma jW (x y:aH) (Z:Matrix (Fin 5) (Fin 5) ℂ):
  Ae.bil x y Z=x ⬝ᵥ Z*ᵥ y:=by
 simp only[Ae.bil,Matrix.mulVec,dotProduct,Finset.mul_sum,mul_assoc]
abbrev sB (L:Submodule ℂ aC) (i j r:Fin 4):
  aJ L i j→ₗ[ℂ] aH:=
 (obs L r).comp (aJ L i j).subtype
lemma eB {L:Submodule ℂ aC} (f:∀l,u L l=0)
  {i j r:Fin 4} (a:r≠i) (b:r≠j) (c:i≠j):
  Function.Injective (sB L i j r):=by
 intro x y h
 let z:=x-y
 have e:row r z.val=0:=by funext d;change x.val.val (r,d)-y.val.val (r,d)=0;exact sub_eq_zero.mpr (congrFun h d)
 exact sub_eq_zero.mp (Subtype.ext (hV f a b c z.val e z.property.1 z.property.2))
lemma fX {T:Type*} [AddCommGroup T] [Module ℂ T]
  (K:Submodule ℂ T) (A B:K→ₗ[ℂ] aH)
  (a:Function.Injective A) (b:Function.Injective B)
  (f:∀x,(∑c,A x c)+(∑c,B x c)=0)
  (e:∀x,Ag.dQ (A x) (B x)=0)
  (d:2≤Module.finrank ℂ K):
  ∃x,Ag.dL (A x) (B x)*ᵥ (1:aH)≠0:=
 Ag.iG (P:= ↥K) A B a b f e d
set_option maxHeartbeats 800000 in
lemma fF {L:Submodule ℂ aC} (hL:aD L) (G:aX L=8)
  (v:∀r,u L r=0) {i j:Fin 4} (b:i≠j) (H:p L i j≤6):
  jT L i j:=by
 classical
 obtain⟨s,e,f⟩:=Ae.zD i j b
 let M:=L.map (Ad.re s 1)
 have q:aD M:=Ad.gI s 1 hL
 let K:=aJ L i j
 let A:=sB L i j (s 0)
 let B:=sB L i j (s 1)
 have w:s 0≠i:=e▸fun h=>(show(0:Fin 4)≠2 by decide) (s.injective h)
 have x:s 0≠j:=f▸fun h=>(show(0:Fin 4)≠3 by decide) (s.injective h)
 have y:s 1≠i:=e▸fun h=>(show(1:Fin 4)≠2 by decide) (s.injective h)
 have z:s 1≠j:=f▸fun h=>(show(1:Fin 4)≠3 by decide) (s.injective h)
 have n:Function.Injective A:=eB v w x b;have o:Function.Injective B:=eB v y z b;have d (k:K):Ae.bD (A k) (B k) 0 0∈M:=by
  refine⟨k.val.val,k.val.property,?_⟩;funext ⟨r,c⟩;fin_cases r
  ·rfl
  ·rfl
  ·change k.val.val (s 2,c)=0;rw[e];exact congrFun (show row i k.val=0 from k.property.1) c
  ·change k.val.val (s 3,c)=0;rw[f];exact congrFun (show row j k.val=0 from k.property.2) c
 have m (k:K):(∑c,A k c)+(∑c,B k c)=0:=by have h:=(Ac.Ad.cT q (d k)).1;simpa[cW,Fin.sum_univ_four,Ae.bD] using h
 have a (k:K) (t:L):
   Ae.bil (1+row i t) (1+row j t) (Ae.dL (A k) (B k))=0:=by
  have F:Ae.aR M (Ae.aM 1 (Ad.re s 1 t)) 1:=⟨_,⟨t,t.property,rfl⟩,rfl⟩
  have h:=Ae.rR q (d k) F;change Ae.bil (1+row (s 2) t) (1+row (s 3) t) _=0 at h;rwa [e,f] at h
 have g (k:K):Ag.dQ (A k) (B k)=0:=by have h:=a k 0;change Ae.bil (1+row i 0) (1+row j 0) (Ae.dL (A k) (B k))=0 at h;simp only[map_zero,add_zero,Ae.bil,Pi.one_apply,one_mul,mul_one,Ae.pO] at h;change Ae.dQ (A k) (B k)=0;exact(mul_eq_zero.mp h).resolve_left (by norm_num)
 have l:2≤Module.finrank ℂ K:=by have h:=cA L i j;change p L i j+Module.finrank ℂ K=aX L at h;omega
 obtain⟨k,C⟩:=fX (T:=L) (aJ L i j) A B n o m g l;refine⟨Ag.dL (A k) (B k),qL _ _,C,?_⟩;intro t E;rw[←jW];exact a k ⟨t,E⟩
lemma mR {L:Submodule ℂ aC} (hL:aD L)
  (f:aX L=8) (h:∀l,u L l=0)
  {a b c:Fin 4} (hab:a≠b) (d:a≠c) (e:b≠c)
  (k:aE L a=3) (m:aE L b=3) (o:aE L c=3):
  ∃n:aH,n≠0∧(∑j,n j)=0∧∀i,aE L i=3→aY L i=bM n:=
 xT hL f h (fun _ _ g p=>fF hL f h g p.le) hab d e k m o
lemma pU {L:Submodule ℂ aC} (hL:aD L)
  (v:aX L=8) (k:∀l,u L l=0)
  {a b c:Fin 4} (hab:a≠b) (o:a≠c) (r:b≠c)
  (d:aE L a=3) (q:aE L b=3) (w:aE L c=3):
  ∃
   n:aH,n≠0∧(∑j,n j)=0∧
   (∀i,aE L i=3→aY L i=bM n)∧
   (∀i,aE L i≤3→aY L i≤bM n):=by
 obtain⟨n,x,z,h⟩:=mR hL v k hab o r d q w;refine⟨n,x,z,h,?_⟩;intro i A;by_cases g:aE L i=3
 ·exact(h i g).le
 have f:a≠i:=fun e=>g (e▸d)
 have s:b≠i:=fun e=>g (e▸q)
 have t:=bB k f hab s.symm;have m:=cF L a b;have B:=cF L a i;have y:p L a i=aE L a+aE L i:=by omega
 exact(jU hL d y (fF hL v k f (by omega))).trans (h a d).le
lemma zK {L:Submodule ℂ aC} (hL:aD L) (o:aX L=8)
  (f:∀l,u L l=0) (d:∀i j,i≠j→p L i j≤6)
  {a b:Fin 4} (g:aE L a=4) (r:aE L b=2):False:=by
 have hab:a≠b:=by rintro rfl;omega
 obtain⟨c,e,k⟩:∃c:Fin 4,a≠c∧b≠c:=by clear hL o f d g r L;decide+revert
 have t:=bB f hab e k;have m:=d a c e;have w:=d a b hab;have v:p L a b=aE L a+aE L b:=by omega
 obtain⟨n,s,_,q,_⟩:=fE v (fF hL o f hab w);have h:=Submodule.finrank_mono q;rw[cV hL,wC s,g] at h;omega
end Ac.An
namespace Ac.An
open Aa
lemma uS {L:Submodule ℂ aC} (d:∀l,u L l=0)
  {i j k:Fin 4} (a:i≠j) (b:i≠k) (c:j≠k):
  aX L≤aE L i+aE L j+aE L k:=by
 have:=bB d a b c;have:=cF L i j;have:=cF L i k;omega
lemma fG {L:Submodule ℂ aC} (hL:aD L) (g:aX L=8)
  (f:∀l,u L l=0) (e:∀i j,i≠j→p L i j≤6) (i:Fin 4):
  2≤aE L i∧aE L i≤4:=by
 obtain⟨j,k,a,b,c⟩:∃j k:Fin 4,j≠i∧j≠k∧i≠k:=by clear hL g f e L;decide+revert
 have:=bB f a b c;have:=e j k b;have:=cF L j i;have m:=(aY L i).finrank_le;rw[cV hL] at m;have d:Module.finrank ℂ aH=5:=by simp[aH]
 omega
lemma zL (i:Fin 4):∃a b c:Fin 4,a≠b∧a≠c∧b≠c∧a≠i∧b≠i∧c≠i:=by decide+revert
lemma wH {L:Submodule ℂ aC} (hL:aD L) (q:aX L=8)
  (o:∀l,u L l=0) (k:∀i j,i≠j→p L i j≤6):
  (∃i j:Fin 4,i≠j∧aE L i=4∧aE L j=4)∨
  (∃a b c:Fin 4,a≠b∧a≠c∧b≠c∧aE L a=3∧
    aE L b=3∧aE L c=3):=by
 classical
 by_cases h:∃i j:Fin 4,i≠j∧aE L i=4∧aE L j=4
 ·exact Or.inl h
 right;have d:=fG hL q o k
 suffices hb:∃r:Fin 4,∀i,i≠r→aE L i=3 by obtain⟨r,f⟩:=hb;obtain⟨a,b,c,x,y,A,z,B,C⟩:=zL r;exact⟨a,b,c,x,y,A,f a z,f b B,f c C⟩
 by_cases s:∃i,aE L i=4
 ·obtain⟨r,f⟩:=s;refine⟨r,fun i m=> ?_⟩;have v:aE L i≠4:=fun e=>h ⟨i,r,m,e,f⟩
  have n:aE L i≠2:=zK hL q o k f;have:=d i;omega
 ·have g (i:Fin 4):aE L i≤3:=by
   have:=d i;have v:aE L i≠4:=fun e=>s ⟨i,e⟩
   omega
  by_cases n:∃i,aE L i=2
  ·obtain⟨r,f⟩:=n;refine⟨r,fun i m=> ?_⟩;obtain⟨j,t,w⟩:∃j:Fin 4,i≠j∧r≠j:=by
    clear* -i r;decide+revert
   have:=uS o m t w;have:=g i;have:=g j;omega
  ·refine⟨0,fun i _=> ?_⟩;have v:aE L i≠2:=fun e=>n ⟨i,e⟩
   have:=g i;have:=d i;omega
end Ac.An
namespace Ac.Az
abbrev bI:=Fin 2×Fin 2→ℂ
abbrev iZ:=Fin 2→ℂ
def iV (t:bI):ℂ:=t (0,0)+t (0,1)+t (1,0)+t (1,1)
def wI (t:bI):ℂ:=t (0,0)*t (1,1)+t (0,1)*t (1,0)
variable {K : Type*} [AddCommGroup K] [Module ℂ K]
lemma sC
  (A B Z:K→ₗ[ℂ] ℂ) (C:K→ₗ[ℂ] iZ) (a:Function.Surjective C)
  (h:∀x,A x*B x-2*(Z x)^2=2*C x 0*C x 1)
  (u:K) (c:C u=0):A u=0:=by
 have i:A u*B u-2*(Z u)^2=0:=by simpa[c] using h u
 have g (x:K):A u*B x+A x*B u-4*Z u*Z x=0:=by have b:=h (u+x);simp[map_add,c] at b;linear_combination b-i-h x
 let f:K→ₗ[ℂ] ℂ:=(A u)•Z-(Z u)•A
 have sq (x:K):(f x)^2= -(A u)^2*C x 0*C x 1:=by change(A u*Z x-Z u*A x)^2=_;linear_combination(A u*A x*g x-(A x)^2*i-(A u)^2*h x)/2
 obtain⟨x,d⟩:=a ![1,0];obtain⟨y,e⟩:=a ![0,1];have j:f x=0:=by simpa[d] using sq x
 have k:f y=0:=by simpa[e] using sq y
 simpa[map_add,d,e,j,k] using(sq (x+y)).symm
lemma rC
  (T:K→ₗ[ℂ] bI) (C:K→ₗ[ℂ] iZ) (l:Function.Surjective C)
  (m:∀x,iV (T x)=0)
  (n:∀x,wI (T x)=2*C x 0*C x 1)
  {u:K} (f:C u=0):T u=0:=by
 let t (i j:Fin 2):K→ₗ[ℂ] ℂ:=(LinearMap.proj (i,j)).comp T
 let Z:=t 0 0
 let A:=t 0 1-Z
 let B:=t 1 0-Z
 have h (x:K):A x*B x-2*(Z x)^2=2*C x 0*C x 1:=by change(T x (0,1)-T x (0,0))*(T x (1,0)-T x (0,0))-2*(T x (0,0))^2=_;have a:=m x;have b:=n x;unfold iV at a;unfold wI at b;linear_combination b-T x (0,0)*a
 have d:=sC A B Z C l h u f;have e:=sC B A Z C l (fun x=>by simpa[mul_comm (B x) (A x)] using h x) u f;have c:Z u=0:=by simpa[d,e,f] using h u
 change T u (0,0)=0 at c;change T u (0,1)-T u (0,0)=0 at d;change T u (1,0)-T u (0,0)=0 at e;have g:T u (0,1)=0:=by linear_combination d+c
 have k:T u (1,0)=0:=by linear_combination e+c
 have o:T u (1,1)=0:=by simpa[iV,c,g,k] using m u
 funext ⟨i,j⟩;fin_cases i<;>fin_cases j<;>assumption
end Ac.Az
namespace Ac.Az
open Aa Ac.Aj
def lZ:cI→ₗ[ℂ] bI:=LinearMap.funLeft ℂ ℂ (fun p:Fin 2×Fin 2=>(Fin.castLE (by decide) p.1,p.2))
def fP:cI→ₗ[ℂ] iZ:=LinearMap.funLeft ℂ ℂ (fun j:Fin 2=>(2,j))
lemma aB4 {x:cI} (c:∀j,x (3,j)= -x (2,j))
  (b:lZ x=0) (a:fP x=0):x=0:=by
 funext ⟨i,j⟩;fin_cases i
 ·exact congrFun b (0,j)
 ·exact congrFun b (1,j)
 ·exact congrFun a j
 ·change x (3,j)=0;rw[c j,show x (2,j)=0 from congrFun a j,neg_zero]
lemma rD {x:cI} (a:∀j,x (3,j)= -x (2,j))
  (c:aS x=0) (b:dQ x=0):
  iV (lZ x)=0∧wI (lZ x)=2*fP x 0*fP x 1:=by
 simp only[aS,Fin.sum_univ_four,a] at c;simp only[dQ,jS,Fin.sum_univ_four,a] at b;constructor
 ·change x (0,0)+x (0,1)+x (1,0)+x (1,1)=0;linear_combination c
 ·change x (0,0)*x (1,1)+x (0,1)*x (1,0)=2*x (2,0)*x (2,1);linear_combination b
lemma pV {x:aC}
  (a:∀(i:Fin 4) (j:Fin 5),2≤j→x (i,j)=0)
  (f:∀j,bW x (3,j)= -bW x (2,j))
  (c:cW x=0) (d:pQ x=0):
  iV (lZ (bW x))=0∧wI (lZ (bW x))=2*fP (bW x) 0*fP (bW x) 1:=by
 have b (i:Fin 4):bC x i=0:=by simp[bC,a i 2 (by decide),a i 3 (by decide),a i 4 (by decide)]
 have g:eM x=0:=by simp[eM,b,a 0 2 (by decide),a 0 3 (by decide),a 0 4 (by decide)]
 obtain⟨h,e⟩:=mO (fun i _=>a i) (b 0) (b 1) g c d;exact rD f h e
lemma kO {L S:Submodule ℂ aC} (hL:aD L) (g:S≤L)
  (a:∀x∈S,∀(i:Fin 4) (j:Fin 5),2≤j→x (i,j)=0)
  (n:∀x∈S,∀j,bW x (3,j)= -bW x (2,j))
  (o:∀c:iZ,∃x∈S,fP (bW x)=c)
  (p:∃u∈S,fP (bW u)=0∧u≠0):False:=by
 let I:=eV.domRestrict S
 let T:=lZ.comp I
 let C:=fP.comp I
 have e:Function.Surjective C:=by intro c;obtain⟨x,r,q⟩:=o c;exact⟨⟨x,r⟩,q⟩
 have d (x:S):iV (T x)=0∧wI (T x)=2*C x 0*C x 1:=by have l:=Ac.Ad.cT hL (g x.2);exact pV (a x x.2) (n x x.2) l.1 l.2.1
 obtain⟨u,b,h,m⟩:=p;have f:=rC T C e (fun x=>(d x).1) (fun x=>(d x).2) (u:=⟨u,b⟩) h;have k:=aB4 (n u b) f h;apply m;funext ⟨i,j⟩;fin_cases j
 ·exact congrFun k (i,0)
 ·exact congrFun k (i,1)
 ·exact a u b i 2 (by decide)
 ·exact a u b i 3 (by decide)
 ·exact a u b i 4 (by decide)
end Ac.Az
namespace Ac.A6
open Aa Ad
def aHh:aC→ₗ[ℂ] aC where
 toFun:=gQ
 map_add' x y:=by funext p;simp only[gQ,gR,gC,aS,cW,Pi.add_apply,Finset.sum_add_distrib];ring
 map_smul' r x:=by funext p;simp only[gQ,gR,gC,aS,cW,Pi.smul_apply,smul_eq_mul,←Finset.mul_sum,RingHom.id_apply];ring
lemma zM {S:Submodule ℂ aC} (c:∀x∈S,cW x=0)
  (d:∀x∈S,∀y∈S,B x y=0):aX S≤9:=by
 classical
 let U:=S⊔Submodule.span ℂ {(1:aC)}
 let A:=(dotProductEquiv ℂ (Fin 4×Fin 5)).toLinearMap.comp aHh
 have g (x y:aC):A x y=B x y:=(fM (gQ x) y).trans (aEp x y);have hab (x:aC) (i:x∈S):A x∈U.dualAnnihilator:=by apply(Submodule.mem_dualAnnihilator _).mpr;change U≤LinearMap.ker (A x);refine sup_le (fun y m=>(g x y).trans (d x i y m)) ?_;apply Submodule.span_le.mpr;rintro _ rfl;change A x (1:aC)=0;change dotProductEquiv ℂ (Fin 4×Fin 5) (gQ x) 1=0;rw[fM];have z:aS x=0:=c x i;simpa[kK,aS,cW] using(show aS (gQ x)=0 by rw[aF1,z,mul_zero])
 let f:=(A.domRestrict S).codRestrict U.dualAnnihilator (fun x=>hab x x.2)
 have k:Function.Injective f:=by
  intro x y j;have h:(dotProductEquiv ℂ (Fin 4×Fin 5)) (gQ x)=(dotProductEquiv ℂ (Fin 4×Fin 5)) (gQ y):=congrArg Subtype.val j;have e:=(dotProductEquiv ℂ (Fin 4×Fin 5)).injective h;exact Subtype.ext ((rQ x (c x x.2)).symm.trans
   ((congrArg bQ e).trans (rQ y (c y y.2))))
 have l:=LinearMap.finrank_le_finrank_of_injective k;have b:(1:aC)∉S:=by intro h;have d:=c 1 h;norm_num[cW] at d
 have o:aX U=aX S+1:=Submodule.finrank_sup_span_singleton b;have n:Module.finrank ℂ aC=20:=by simp[aC]
 have a:=Subspace.finrank_add_finrank_dualAnnihilator_eq U;change aX S≤Module.finrank ℂ U.dualAnnihilator at l;change aX U+Module.finrank ℂ U.dualAnnihilator=Module.finrank ℂ aC at a;omega
lemma nO {L:Submodule ℂ aC} (hL:aD L) (S:Submodule ℂ aC)
  (p:∀x∈S,cW x=0) (n:∀x∈S,∀y∈S,B x y=0)
  (m:∀x∈L,∀y∈S,B x y=0):
  aX L+aX S≤9+aX (L⊓S):=by
 obtain⟨k,l⟩:=gM hL;have f:aX (L⊔S)≤9:=by
  apply zM
  ·intro z q;obtain⟨x,g,y,h,rfl⟩:=Submodule.mem_sup.mp q;have e:cW (x+y)=cW x+cW y:=by simp[cW,Finset.sum_add_distrib]
   rw[e,show cW x=0 from k x g,p y h,add_zero]
  ·intro x g y h;obtain⟨a,e,b,f,rfl⟩:=Submodule.mem_sup.mp g;obtain⟨c,i,d,j,rfl⟩:=Submodule.mem_sup.mp h;rw[qS,kR,kR,←aEp a c,l a e c i,
    m a e d j,sY b c,m c i b f,n b f d j]
   ring
 have o:=L.finrank_sup_add_finrank_inf_eq S;change aX (L⊔S)+aX (L⊓S)=aX L+aX S at o;omega
end Ac.A6
namespace Ac.Ah
open Aa Finset Ad
abbrev bI:=Fin 3×Fin 5→ℂ
def aU:aC→ₗ[ℂ] bI:=LinearMap.funLeft ℂ ℂ (fun p=>(p.1.castSucc,p.2))
def bF (X:bI) (v:aH):aC:=fun p=> ![(fun j=>X (0,j)),(fun j=>X (1,j)),(fun j=>X (2,j)),v] p.1 p.2
def W (L:Submodule ℂ aC):Submodule ℂ bI:=L.map aU⊔Submodule.span ℂ {(1:bI)}
def F (v:aH) (X:bI):ℂ:=aO (bF X v)
lemma jX {L:Submodule ℂ aC} {i:Fin 4} {z:aC}:
  z∈aZ L i↔z∈L∧∀j,j≠i→ row j z=0:=by
 simp only[aZ,Submodule.mem_inf,Submodule.mem_iInf,LinearMap.mem_ker,Subtype.forall]
abbrev rot:=(finRotate 4).symm
abbrev C (L:Submodule ℂ aC):=L.map (Ad.re rot 1)
lemma aE4 (L:Submodule ℂ aC):W L=Af.W (C L) 0:=by
 have a:(Af.bH 0).comp (Ad.re rot 1)=aU:=by ext t ⟨r,j⟩;fin_cases r<;>rfl
 rw[W,Af.W,sup_comm,C,←Submodule.map_comp,a]
lemma aGu {L:Submodule ℂ aC} {v:aH} (h:bF 0 v∈L):v∈Af.U (C L) 0:=by refine Af.uE.mpr ⟨_,h,?_⟩;funext ⟨r,c⟩;fin_cases r<;>rfl
lemma aGv {L:Submodule ℂ aC} (hL:aD L) (a:aX L=8) (b:u L 3=1):
  Module.finrank ℂ (W L)=8:=by
 rw[aE4];have e:=Af.jP (Ad.gI rot 1 hL) 0;rw[Ae.aF4,Ad.nL,a,show rot 0=3 from rfl,b] at e;change Module.finrank ℂ (Af.W (C L) 0)+1=8+1 at e;exact Nat.add_right_cancel e
lemma aE5 {L:Submodule ℂ aC} {X:bI} (f:X∈W L):
  ∃t∈L,∃c:ℂ,X=aU t+c•1:=by
 obtain⟨v,b,w,d,e⟩:=Submodule.mem_sup.mp f;obtain⟨t,a,rfl⟩:=b;obtain⟨c,rfl⟩:=Submodule.mem_span_singleton.mp d;exact⟨t,a,c,e.symm⟩
lemma vD {L:Submodule ℂ aC} (hL:aD L) {z:aC} (a:z∈L) (c:ℂ):
  aO (z+c•1)=120*c^4:=by
 have e:z+c•1=Ae.aM c z:=by ext p;simp[Ae.aM,add_comm]
 rw[e,Ae.bR hL a]
lemma aE6 (z:aC) (v:aH):
  aO (z+bF 0 v)=aO z+F v (aU z):=by
 simp only[F,aO,bF,aU,LinearMap.funLeft_apply,Fin.prod_univ_four,
  Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
  Matrix.head_cons,Matrix.tail_cons,Pi.add_apply,Pi.zero_apply,add_zero,mul_add,Finset.sum_add_distrib]
 rfl
lemma aC8 {L:Submodule ℂ aC} (hL:aD L) (v:aH) (f:bF 0 v∈L)
  (X:bI) (d:X∈W L):F v X=0:=by
 obtain⟨t,a,c,rfl⟩:=aE5 d;have e:=aE6 (t+c•1) v;have z:t+c•1+bF 0 v=t+bF 0 v+c•1:=by abel
 rw[z,vD hL (L.add_mem a f),vD hL a] at e;have b:aU (t+c•1)=aU t+c•1:=rfl;rw[b] at e;linear_combination-e
lemma aHi (v:aH):Av.eJ 3 v=bF 0 v:=by funext ⟨r,c⟩;fin_cases r<;>rfl
lemma aF6 {L:Submodule ℂ aC} (hL:aD L) (c:u L 3=1):
  ∃v:aH,v≠0∧(∑j,v j)=0∧bF 0 v∈L:=by
 obtain⟨v,a,b⟩:=Submodule.exists_mem_ne_zero_of_ne_bot (p:=Af.U L 3) (by intro h;have e:=Af.tE L 3;rw[h,finrank_bot,c] at e;omega);exact⟨v,b,Af.lR hL a,aHi v▸Af.uE.mp a⟩
lemma wJ {L:Submodule ℂ aC} (hL:aD L) (o:aX L=8)
  (i:Fin 4) {a b:Fin 5} (hab:a≠b)
  (k:∀t∈L,∀r,r≠i→t (r,a)=t (r,b)):
  ∃M,aD M∧aX M=7∧vI M:=by
 let f:Module.Dual ℂ aC:=(LinearMap.proj (i,a):aC→ₗ[ℂ] ℂ)-LinearMap.proj (i,b)
 let K:=L⊓LinearMap.ker f
 have h:=Ad.vT f L;have p:=(L.map f).finrank_le;have n:Module.finrank ℂ ℂ=1:=Module.finrank_self ℂ;have g:7≤aX K:=by change _+aX K=_ at h;omega
 obtain⟨v,m⟩:=exists_linearIndependent_of_le_finrank (R:=ℂ) (M:=K) g
 let S:=Submodule.span ℂ (Set.range fun j=>K.subtype (v j))
 have d:S≤K:=by rw[Submodule.span_le];rintro _ ⟨j,rfl⟩;exact(v j).2
 refine⟨S,fun t c=>hL t (d c).1,?_,a,b,hab,?_⟩
 ·have e:LinearIndependent ℂ (fun j=>(K.subtype (v j):aC)):=m.map' K.subtype (Submodule.ker_subtype K);change Module.finrank ℂ (Submodule.span ℂ _)=7;rw[finrank_span_eq_card e];simp
 ·intro t c r;by_cases l:r=i
  ·subst r;exact sub_eq_zero.mp (d c).2
  ·exact k t (d c).1 r l
lemma fH (f:Fin 5→ℂ):
  ∑j,f j=f 0+f 1+f 2+f 3+f 4:=by
 simp[Fin.sum_univ_succ];ring
lemma aHy (L:Submodule ℂ aC):(1:bI)∈W L:=(show Submodule.span ℂ {(1:bI)}≤W L from le_sup_right) (Submodule.mem_span_singleton_self _)
lemma aHz {L:Submodule ℂ aC} (hL:aD L) {v:aH} (b:bF 0 v∈L)
  {X:bI} (a:X∈W L):∑j,v j*Af.q X j=0:=
 Af.hO (gI rot 1 hL) (aGu b) (aE4 L▸a)
lemma blk {L:Submodule ℂ aC} (hL:aD L) {v:aH} (b:bF 0 v∈L)
  (A:Finset (Fin 5)) (a:∀k,v k≠0↔k∈A):
  2*Module.finrank ℂ ((W L).map (Af.aK A))≤3*A.card:=
 aE4 L▸Af.dO (gI rot 1 hL) (aGu b) A a
lemma aF7 {A:Finset (Fin 5)} {x:bI} (h:Af.aK A x=0) {k:Fin 5}
  (a:k∈A) (r:Fin 3):x (r,k)=(∑j,x (r,j))/2:=by
 have e:=congrFun h (A.equivFin ⟨k,a⟩,r);simp only[Af.aK,LinearMap.coe_mk,AddHom.coe_mk,Equiv.symm_apply_apply] at e;exact sub_eq_zero.mp e
lemma wK {L:Submodule ℂ aC} (hL:aD L) (b:aX L=8)
  (f:u L 3=1) {v:aH} (g:bF 0 v∈L):∃j,v j=0:=by
 by_contra! d;have w:=blk hL g univ (by simp[d]);have e:=Af.cX (W L) (Af.aK univ);have z:(W L⊓LinearMap.ker (Af.aK univ):Submodule ℂ bI)= ⊥ :=by
  rw[eq_bot_iff];intro x i;have a (r:Fin 3) (j:Fin 5):=aF7 i.2 (mem_univ j) r;have s (r:Fin 3):(∑c,x (r,c))=0:=by
   have h:=fH fun j=>x (r,j)
   rw[a r 0,a r 1,a r 2,a r 3,a r 4] at h;linear_combination-2*h/3
  exact funext fun q=>by rw[a q.1 q.2,s,zero_div];rfl
 rw[z,finrank_bot,aGv hL b f] at e;have c:(univ:Finset (Fin 5)).card=5:=rfl;omega
lemma wL {L:Submodule ℂ aC} (hL:aD L) (f:aX L=8)
  (g:u L 3=1) {v:aH} (c:bF 0 v∈L) {j:Fin 5}
  (a:v j=0) (b:∀k≠j,v k≠0):False:=by
 have d:=Af.yK hL (Af.uE.mpr (aHi v▸c)) a b;have k:=Af.fJ hL 3 j;have e:=Af.cX (Af.W L 3) (Af.jQ j);have w:=Af.jP hL 3;omega
abbrev yM:=Fin 3×Fin 2→ℂ
abbrev A3:Finset (Fin 5):={0,1,2}
abbrev aE7:bI→ₗ[ℂ] yM:=LinearMap.funLeft ℂ ℂ (fun q=>(q.1,(![0,3]:Fin 2→Fin 5) q.2))
def rad (Z:yM):bI:=fun p=>let a:=Z (p.1,0);let b:=Z (p.1,1); ![a,a,a,b,-a-b] p.2
abbrev K3 (L:Submodule ℂ aC):=W L⊓LinearMap.ker (Af.aK A3)
abbrev S3 (L:Submodule ℂ aC):=(K3 L).map aE7
lemma aB5 {Y:bI} (b:Af.aK A3 Y=0):rad (aE7 Y)=Y:=by
 funext ⟨r,c⟩;have a:=aF7 b (k:=0) (by decide) r;have e1:=aF7 b (k:=1) (by decide) r;have e2:=aF7 b (k:=2) (by decide) r;have d: -Y (r,0)-Y (r,3)=Y (r,4):=by rw[fH] at a e1 e2;linear_combination e1+e2
 fin_cases c<;>first | rfl | exact a.trans e1.symm | exact a.trans e2.symm | exact d
lemma aHj {L:Submodule ℂ aC} (hL:aD L) (g:aX L=8)
  (i:u L 3=1) {v:aH} (j:bF 0 v∈L) (b:∀k,v k≠0↔k∈A3):
  4≤Module.finrank ℂ (S3 L):=by
 have w:=blk hL j A3 b;have a:_+Module.finrank ℂ (K3 L)=_:=Af.cX (W L) (Af.aK A3);rw[aGv hL g i] at a;have d:Module.finrank ℂ (K3 L)≤Module.finrank ℂ (S3 L):=
  LinearMap.finrank_le_finrank_of_injective (f:=aE7.submoduleMap (K3 L)) (by
  intro X Y h;have e:aE7 X.val=aE7 Y.val:=congrArg Subtype.val h;exact Subtype.ext ((aB5 X.2.2).symm.trans ((congrArg rad e).trans (aB5 Y.2.2))))
 have c:A3.card=3:=rfl;omega
lemma aB6 {L:Submodule ℂ aC} {Z:yM} (b:Z∈S3 L):rad Z∈W L:=by obtain⟨Y,a,rfl⟩:=b;rw[aB5 a.2];exact a.1
def fL (v:aH) (X:bI) (r:Fin 3):ℂ:=∑j,v j*X (r,j)
def bZ (f:Fin 3→ℂ) (Z:yM) (r:Fin 3) (c:Fin 2):ℂ:= ![f 1*Z (2,c)+f 2*Z (1,c),f 0*Z (2,c)+f 2*Z (0,c),f 0*Z (1,c)+f 1*Z (0,c)] r
def aE8 (f:Fin 3→ℂ):yM→ₗ[ℂ] yM where
 toFun Z:=fun q=>bZ f Z q.1 q.2+bZ f Z q.1 0+bZ f Z q.1 1
 map_add' X Y:=by funext ⟨r,c⟩;fin_cases r<;>simp[bZ,Matrix.cons_val,mul_add]<;>ring
 map_smul' c X:=by funext ⟨r,j⟩;fin_cases r<;>simp[bZ,Matrix.cons_val]<;>ring
def oR (f:Fin 3→ℂ):yM→ₗ[ℂ] Module.Dual ℂ yM:=(dotProductEquiv ℂ (Fin 3×Fin 2)).toLinearMap.comp (aE8 f)
lemma aE9 (f:Fin 3→ℂ) (X Y:yM):
  oR f X Y=∑r,∑c,aE8 f X (r,c)*Y (r,c):=by
 change ∑q:Fin 3×Fin 2,_=_;rw[Fintype.sum_prod_type]
lemma aDm (f:Fin 3→ℂ) (X Y:yM):oR f X Y=oR f Y X:=by simp only[aE9,Fin.sum_univ_three,Fin.sum_univ_two,aE8,LinearMap.coe_mk,AddHom.coe_mk,bZ,Matrix.cons_val];ring
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
lemma aDn (v:aH) (c:∑j,v j=0) (a:v 3=0) (b:v 4=0) (X:bI) (Z:yM):
  F v (X+rad Z)+F v (X-rad Z)-2*F v X=oR (fL v X) Z Z:=by
 have d:v 2= -(v 0+v 1):=by rw[fH,a,b] at c;linear_combination c
 simp(config:={decide:=true}) only[F,cK,bF,rad,fL,aE9,Fin.sum_univ_three,
  Fin.sum_univ_two,fH,aE8,LinearMap.coe_mk,AddHom.coe_mk,bZ,Matrix.cons_val,
  Pi.add_apply,Pi.sub_apply,d,a,b,mul_zero,zero_mul,ite_true,ite_false,add_zero,zero_add]
 ring
lemma aGw {L:Submodule ℂ aC} {f:Fin 3→ℂ} (j:4≤Module.finrank ℂ (S3 L))
  (b:∀Z∈S3 L,oR f Z Z=0):
  2≤Module.finrank ℂ (S3 L⊓LinearMap.ker (oR f):Submodule ℂ yM):=by
 let S:=S3 L
 let P:=oR f
 have h (X:yM) (c:X∈S) (Y:yM) (g:Y∈S):P X Y=0:=by have e:=b _ (S.add_mem c g);simp only[map_add,LinearMap.add_apply,b X c,b Y g,aDm f Y X] at e;change oR f X Y=0;linear_combination e/2
 have k:S.map P≤S.dualAnnihilator:=by rintro _ ⟨Z,i,rfl⟩;exact(Submodule.mem_dualAnnihilator _).mpr (h Z i)
 have a:=Submodule.finrank_mono k;have e:=Subspace.finrank_add_finrank_dualAnnihilator_eq S;have d:Module.finrank ℂ yM=6:=by simp[yM]
 have r:Module.finrank ℂ (S.map P)+
   Module.finrank ℂ (S⊓LinearMap.ker P:Submodule ℂ yM)=Module.finrank ℂ S:=by
  rw[←(Submodule.submoduleOfEquivInf _ _).finrank_eq,
   ←(P.submoduleMap S).finrank_range_add_finrank_ker,
   LinearMap.range_submoduleMap,LinearMap.ker_submoduleMap]
  simp
 change 4≤Module.finrank ℂ S at j;change 2≤Module.finrank ℂ (S⊓LinearMap.ker P:Submodule ℂ yM);omega
lemma oS {f:Fin 3→ℂ} {Z:yM} (g:oR f Z=0)
  (i j k:Fin 3) (h:i≠j) (l:i≠k) (m:j≠k) (c:Fin 2):
  f j*Z (k,c)+f k*Z (j,c)=0:=by
 have a:aE8 f Z=0:=(dotProductEquiv ℂ (Fin 3×Fin 2)).injective (by rw[map_zero];exact g);have b:bZ f Z i 0+bZ f Z i 0+bZ f Z i 1=0:=congrFun a (i,0);have d:bZ f Z i 1+bZ f Z i 0+bZ f Z i 1=0:=congrFun a (i,1);have e:bZ f Z i c=0:=by
  fin_cases c
  ·change bZ f Z i 0=0;linear_combination(2*b-d)/3
  ·change bZ f Z i 1=0;linear_combination(2*d-b)/3
 rw[←e];fin_cases i<;>fin_cases j<;>fin_cases k<;>first | contradiction | rfl | exact add_comm _ _
lemma sD {L:Submodule ℂ aC} (hL:aD L) {Z:yM} (h:Z∈S3 L)
  {i j k:Fin 3} (d:j≠k) (e:∀c,Z (i,c)=0)
  (f:∀c,Z (j,c)= -1) (g:∀c,Z (k,c)= -1):False:=by
 have a:=gI rot 1 hL;refine Af.kU a (Af.fC a (aE4 L▸aB6 h)
  (r:=i) fun c=> ?_) (j:=4) d ?_ ?_
 ·fin_cases c<;>simp[rad,e]
 ·intro l b;fin_cases l<;>simp[rad,f] at b ⊢
 ·intro l b;fin_cases l<;>simp[rad,g] at b ⊢
lemma aHk:∀k:Fin 3,∃i j:Fin 3,i≠j∧i≠k∧j≠k∧(univ:Finset (Fin 3))={i,j,k}:=by decide
lemma aB7 {L:Submodule ℂ aC} (hL:aD L) {f:Fin 3→ℂ}
  (A:4≤Module.finrank ℂ (S3 L)) (B:∑i,f i=0)
  (x:∀Z∈S3 L,oR f Z Z=0) (k:Fin 3):f k=0:=by
 classical
 by_contra n;obtain⟨i,j,d,a,b,e⟩:=aHk k;have p (q:Fin 3):q=i∨q=j∨q=k:=by have h:=mem_univ q;rw[e] at h;simpa using h
 have o:f i+f j+f k=0:=by rw[←B,e];simp[d,a,b,add_assoc]
 let N:=S3 L⊓LinearMap.ker (oR f)
 let l:N→ₗ[ℂ] (Fin 2→ℂ):=(LinearMap.funLeft ℂ ℂ (fun c:Fin 2=>(k,c))).comp N.subtype
 have w:Function.Injective l:=by
  rw[←LinearMap.ker_eq_bot,LinearMap.ker_eq_bot'];intro Z z;have g (c:Fin 2):Z.val (k,c)=0:=congrFun z c;apply Subtype.ext;funext ⟨r,c⟩;rcases p r with v|v|v
  ·subst r;have e:=oS Z.2.2 j i k d.symm b a c;simpa[g,n] using e
  ·subst r;have e:=oS Z.2.2 i j k d a b c;simpa[g,n] using e
  ·subst r;exact g c
 have C:2≤Module.finrank ℂ N:=aGw A x;have E:=LinearMap.finrank_range_of_inj w;have dt:Module.finrank ℂ (Fin 2→ℂ)=2:=by simp
 have t:Function.Surjective l:=LinearMap.range_eq_top.mp
  (Submodule.eq_top_of_finrank_eq (le_antisymm (LinearMap.range l).finrank_le (by omega)))
 obtain⟨Z,y⟩:=t (-1);have Zk (c:Fin 2):Z.val (k,c)= -1:=congrFun y c;have Zi (c:Fin 2):f k*Z.val (i,c)=f i:=by have e:=oS Z.2.2 j i k d.symm b a c;rw[Zk] at e;linear_combination e
 have Zj (c:Fin 2):f k*Z.val (j,c)=f j:=by have e:=oS Z.2.2 i j k d a b c;rw[Zk] at e;linear_combination e
 have prod:f i*f j=0:=by have e:=oS Z.2.2 k i j a.symm b.symm d 0;linear_combination(f k*e-f i*Zj 0-f j*Zi 0)/2
 have m (r:Fin 3) (zr:∀c,f k*Z.val (r,c)=f r) (fr:f r= -f k)
   (c:Fin 2):Z.val (r,c)= -1:=by
  apply mul_left_cancel₀ n;rw[zr,fr];ring
 rcases mul_eq_zero.mp prod with s|u
 ·exact sD hL Z.2.1 b (i:=i) (fun c=>(mul_eq_zero.mp ((Zi c).trans s)).resolve_left n) (m j Zj (by linear_combination o-s)) Zk
 ·exact sD hL Z.2.1 a (i:=j) (fun c=>(mul_eq_zero.mp ((Zj c).trans u)).resolve_left n) (m i Zi (by linear_combination o-u)) Zk
lemma tN {L:Submodule ℂ aC} (hL:aD L) (i:aX L=8)
  (l:u L 3=1) {v:aH} (a:bF 0 v∈L) (d:∑j,v j=0)
  (m:v 0≠0) (n:v 1≠0) (o:v 2≠0) (g:v 3=0) (h:v 4=0):
  ∀X∈W L,∀r:Fin 3,(∑j,v j*X (r,j))=0:=by
 intro X b;apply aB7 hL (f:=fL v X) (aHj hL i l a (fun k=>by fin_cases k<;>simp[*]))
 ·have e:=Af.eR (gI rot 1 hL) (aGu a) (aE4 L▸b);simp only[Af.aV,Af.aA,mul_add,mul_sub,sum_add_distrib,sum_sub_distrib,
   ←sum_mul,d,zero_mul,sub_zero] at e
  simpa only[fL,Fin.sum_univ_three] using e
 ·intro Z c;have e:=aDn v d g h X Z;rw[aC8 hL v a _ ((W L).add_mem b (aB6 c)),
   aC8 hL v a _ ((W L).sub_mem b (aB6 c)),aC8 hL v a _ b] at e
  linear_combination-e
end Ac.Ah
namespace Ac.Ah.Aw
open Aa Finset
def om:ℂ:=(-1+(IsAlgClosed.exists_pow_nat_eq (-3:ℂ) zero_lt_two).choose)/2
lemma aH0:om^2+om+1=0:=by unfold om;have h:=(IsAlgClosed.exists_pow_nat_eq (-3:ℂ) zero_lt_two).choose_spec;linear_combination h/4
def zN (a b:ℂ):aH:= ![a,b,-a-b,0,0]
def V4 (z:Fin 4→ℂ):aC:=fun p=>
 let v:=zN (z 0) (z 1)
 ![v,om•v,(-1-om)•v,zN (z 2) (z 3)] p.1 p.2
def aDo:(Fin 4→ℂ)→ₗ[ℂ] aC where
 toFun:=V4
 map_add' x y:=by funext ⟨r,c⟩;fin_cases r<;>fin_cases c<;>simp[V4,zN,Matrix.cons_val,mul_add]<;>ring
 map_smul' a x:=by funext ⟨r,c⟩;fin_cases r<;>fin_cases c<;>simp[V4,zN,Matrix.cons_val]<;>ring
lemma aDp {K L:Submodule ℂ aC} (hL:aD L) (v:u L 3=1)
  (s:7≤aX K) (g:K≤L) (h:∀t∈K,∀i:Fin 3,
    t (i.castSucc,0)=t (i.castSucc,2)∧t (i.castSucc,1)=t (i.castSucc,2)):False:=by
 let T:=LinearMap.range aDo
 have l:Function.Injective aDo:=by
  intro a b e;funext j;fin_cases j
  ·exact congrFun e (0,0)
  ·exact congrFun e (0,1)
  ·exact congrFun e (3,0)
  ·exact congrFun e (3,1)
 have q:aX T=4:=(LinearMap.finrank_range_of_inj l).trans (Module.finrank_fin_fun ℂ);have m:=A6.nO (L:=K) (fun t c=>hL t (g c)) T (by
  rintro _ ⟨z,rfl⟩;simp only[cW,Fin.sum_univ_four,fH,aDo,LinearMap.coe_mk,AddHom.coe_mk,V4,zN,Matrix.cons_val,Pi.smul_apply,smul_eq_mul];ring) (by
  rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩;simp only[Ad.B,Ad.kK,Ad.gR,Ad.gC,Ad.aS,cW,
   Fin.sum_univ_four,fH,aDo,LinearMap.coe_mk,AddHom.coe_mk,V4,zN,
   Matrix.cons_val,Pi.smul_apply,smul_eq_mul]
  linear_combination 2*(x 0*y 0+x 1*y 1+(x 0+x 1)*(y 0+y 1))*aH0) (by
  rintro t c _ ⟨x,rfl⟩;have e (r:Fin 3):=h t c r;simp only[Ad.B,Ad.kK,Ad.gR,Ad.gC,Ad.aS,cW,
   Fin.sum_univ_four,fH,aDo,LinearMap.coe_mk,AddHom.coe_mk,V4,zN,
   Matrix.cons_val,Pi.smul_apply,smul_eq_mul]
  have f:t (0,0)=t (0,2)∧t (0,1)=t (0,2):=e 0;have e1:t (1,0)=t (1,2)∧t (1,1)=t (1,2):=e 1;have e2:t (2,0)=t (2,2)∧t (2,1)=t (2,2):=e 2;rw[f.1,f.2,e1.1,e1.2,e2.1,e2.2];ring)
 have k:K⊓T≤aZ L 3:=by
  rintro _ ⟨c,⟨x,rfl⟩⟩;obtain⟨a,b⟩:=h _ c 0;change x 0= -x 0-x 1 at a;change x 1= -x 0-x 1 at b;have o:x 0=0:=by linear_combination(2*a-b)/3
  have p:x 1=0:=by linear_combination(2*b-a)/3
  refine jX.mpr ⟨g c,fun r n=> ?_⟩;funext j;have z:zN (x 0) (x 1)=0:=by rw[o,p];funext j;fin_cases j<;>simp[zN,Matrix.cons_val]
  fin_cases r<;>first | exact(n rfl).elim | simp[aDo,V4,z,row]
 have d:aX (K⊓T)≤u L 3:=Submodule.finrank_mono k;omega
def Dm:bI→ₗ[ℂ] Af.cI 1:=LinearMap.funLeft ℂ ℂ (fun q=>(q.2,0))-LinearMap.funLeft ℂ ℂ (fun q=>(q.2,2))
lemma aB8 (v:aH) (d:∑j,v j=0) (g:v 1≠0) (a:v 3=0) (b:v 4=0)
  (X:bI) (f:∀r:Fin 3,(∑j,v j*X (r,j))=0):
  ∑j,v j*Af.q X j= -(v 0*v 2/v 1)*Af.qH (Dm X) 0:=by
 have c:v 2= -(v 0+v 1):=by rw[fH,a,b] at d;linear_combination d
 have e (r:Fin 3):X (r,1)=X (r,2)-v 0/v 1*(X (r,0)-X (r,2)):=by have h:=f r;rw[fH,a,b,c] at h;field_simp;linear_combination h
 simp only[Af.q,Af.aA,Af.qH,Dm,LinearMap.sub_apply,Pi.sub_apply,LinearMap.funLeft_apply,fH,e,a,b,c];field_simp;ring
end Ac.Ah.Aw
namespace Ac.Ah
open Aa
lemma uT {L:Submodule ℂ aC} (hL:aD L) (q:aX L=8)
  (s:u L 3=1) {v:aH} (x:bF 0 v∈L) (l:∑j,v j=0)
  (o:v 0≠0) (k:v 1≠0) (p:v 2≠0) (d:v 3=0) (g:v 4=0)
  (n:∀X∈W L,∀r:Fin 3,(∑j,v j*X (r,j))=0):False:=by
 have h {t:aC} (c:t∈L):aU t∈W L:=(show L.map aU≤W L from le_sup_left) (Submodule.mem_map_of_mem c)
 have w:=Af.eS (fun _:Fin 1=>(1:ℂ)) (fun _=>one_ne_zero)
  ((W L).map Aw.Dm) (by
  rintro _ ⟨X,m,rfl⟩;have e:=Aw.aB8 v l k d g X (n X m);rw[aHz hL x m] at e;simpa[o,k,p] using e)
 let f:=Aw.Dm.comp aU
 have z:=Submodule.finrank_mono (show L.map f≤(W L).map Aw.Dm from by rintro _ ⟨t,c,rfl⟩;exact⟨_,h c,rfl⟩);have y:=Ad.vT f L;rw[q] at y;refine Aw.aDp (K:=L⊓LinearMap.ker f) hL s (by omega) (fun _ c=>c.1) fun t c i=> ?_
 have a:t (i.castSucc,0)-t (i.castSucc,2)=0:=congrFun c.2 (0,i);have b:=n _ (h c.1) i;rw[fH,d,g] at b;change v 0*t (i.castSucc,0)+v 1*t (i.castSucc,1)+v 2*t (i.castSucc,2)
  +0*t (i.castSucc,3)+0*t (i.castSucc,4)=0 at b
 rw[fH,d,g] at l;refine⟨sub_eq_zero.mp a,sub_eq_zero.mp ((mul_eq_zero.mp (?_:v 1*(t (i.castSucc,1)-t (i.castSucc,2))=0)).resolve_left k)⟩;linear_combination b-v 0*a-t (i.castSucc,2)*l
end Ac.Ah
namespace Ac.Ah
open Aa Finset
abbrev oT  :Prop:=∀{L:Submodule ℂ aC}  ,aD L→aX L=8→
 u L 3=1→bF 0 (Pi.single 0 1-Pi.single 1 1)∈L→
 ∀t∈L,∀i:Fin 3,aU t (i,0)=aU t (i,1)
open Ad
lemma aGl (ρ:Equiv.Perm (Fin 4)) (σ:Equiv.Perm (Fin 5)) (L:Submodule ℂ aC) (i:Fin 4):
  u (L.map (re ρ σ)) i=u L (ρ i):=by
 have d:aZ (L.map (re ρ σ)) i=(aZ L (ρ i)).map (re ρ σ):=by
  ext x;rw[jX];constructor
  ·rintro⟨⟨y,b,rfl⟩,h⟩;refine⟨y,jX.mpr ⟨b,?_⟩,rfl⟩;intro k a;funext c;have e:=congrFun (h (ρ.symm k) (fun f=>a (by simpa using congrArg ρ f))) (σ.symm c);simpa[row,re] using e
  ·rintro⟨y,b,rfl⟩;obtain⟨g,h⟩:=jX.mp b;refine⟨⟨y,g,rfl⟩,fun k a=> ?_⟩;funext c;exact congrFun (h (ρ k) (ρ.injective.ne a)) (σ c)
 unfold u;rw[d,nL]
lemma aDq (v:aH):∃n:ℕ,n≤5∧
  ∃σ:Equiv.Perm (Fin 5),∀j:Fin 5,v (σ j)≠0↔j.val<n:=by
 classical
 let t:=univ.filter (fun j:Fin 5=>v j≠0)
 let n:=t.card
 let s:=univ.filter (fun j:Fin 5=>j.val<n)
 have b:n≤5:=t.card_le_univ;have a:∀m:ℕ,m≤5→(univ.filter (fun j:Fin 5=>j.val< m)).card=m:=by intro m c;interval_cases m<;>decide
 obtain⟨σ,h⟩:=Equiv.Perm.exists_map_finset_eq s t (a n b);refine⟨n,b,σ,fun j=> ?_⟩
 calc
  v (σ j)≠0↔σ j∈t:=by simp[t]
  _↔σ j∈s.map σ.toEmbedding:=by rw[h]
  _↔j.val<n:=by simp[mem_map_equiv,s]
lemma aFa (L:Submodule ℂ aC) {v:aH} (a:bF 0 v∈L)
  (σ:Equiv.Perm (Fin 5)):bF 0 (v∘σ)∈L.map (re 1 σ):=by
 refine⟨_,a,?_⟩;funext ⟨i,j⟩;fin_cases i<;>rfl
lemma aF9 (gT:oT) {L:Submodule ℂ aC} (hL:aD L)
  (d:aX L=8) (n:u L 3=1) {v:aH} (l:bF 0 v∈L) (f:∑j,v j=0)
  (g:v 0≠0) (a:v 2=0) (b:v 3=0) (c:v 4=0):
  ∃M,aD M∧aX M=7∧vI M:=by
 have k:v 1= -v 0:=by rw[fH,a,b,c] at f;linear_combination f
 have e:(v 0)⁻¹ •bF 0 v=bF 0 (Pi.single 0 1-Pi.single 1 1):=by
  funext ⟨i,j⟩;fin_cases i
  ·simp[bF]
  ·simp[bF]
  ·simp[bF]
  ·change(v 0)⁻¹ *v j=(Pi.single 0 1-Pi.single 1 1:aH) j;fin_cases j<;>norm_num[Pi.single_apply,g,k,a,b,c]
 have h:=gT hL d n (e▸L.smul_mem (v 0)⁻¹ l);apply wJ hL d 3 (by decide:(0:Fin 5)≠1);intro t m;exact Fin.lastCases (fun h=>(h rfl).elim) fun i _=>h t m i
lemma aFb (dif:oT):mI:=by
 intro L hL t i A
 let ρ:=Equiv.swap 3 i
 let K:=L.map (re ρ 1)
 have r:u K 3=1:=(aGl ρ 1 L 3).trans (by simpa[ρ] using A);have q:aD K:=gI ρ 1 hL;obtain⟨v,o,z,y⟩:=aF6 q r;obtain⟨n,E,σ,hσ⟩:=aDq v
 let M:=K.map (re 1 σ)
 let w:=v∘σ
 have c:aD M:=gI _ _ q;have d:aX M=8:=(nL _ _ _).trans ((nL _ _ _).trans t);have g:u M 3=1:=(aGl _ _ _ _).trans r;have f:bF 0 w∈M:=aFa K y σ;have l:∑j,w j=0:=(Equiv.sum_comp σ v).trans z;have a (j:Fin 5) (h:j.val<n):w j≠0:=(hσ j).mpr h;have b (j:Fin 5) (h:¬j.val<n):w j=0:=not_not.mp (fun o=>h ((hσ j).mp o));have C:2≤n:=by
  by_contra! B;have h (j:Fin 5) (m:j≠0):w j=0:=b j (by have:=Fin.pos_iff_ne_zero.mpr m;omega);have s:w 0=0:=by simpa[fH,h 1 (by decide),h 2 (by decide),h 3 (by decide),h 4 (by decide)] using l
  exact o (funext (fun j=>by
                                by_cases p:σ.symm j=0
                                ·have e:=congrArg σ p;simpa[w,←e] using s
                                ·simpa[w] using h (σ.symm j) p))
 interval_cases n
 ·exact aF9 dif c d g f l (a 0 (by decide)) (b 2 (by decide)) (b 3 (by decide)) (b 4 (by decide))
 ·apply False.elim;have H:=tN c d g f l (a 0 (by decide)) (a 1 (by decide)) (a 2 (by decide))
   (b 3 (by decide)) (b 4 (by decide))
  exact uT c d g f l (a 0 (by decide)) (a 1 (by decide)) (a 2 (by decide))
   (b 3 (by decide)) (b 4 (by decide)) H
 ·exact(wL c d g f (b 4 (by decide)) fun k x=>a k (by fin_cases k<;>first | decide | exact(x rfl).elim)).elim
 ·obtain⟨j,m⟩:=wK c d g f;exact(a j j.isLt m).elim
end Ac.Ah
namespace Ac.Ah.Au
open Aa Finset Module LinearMap
abbrev dv:aH:=Pi.single 0 1-Pi.single 1 1
variable {L : Submodule ℂ aC}
lemma aA4 {a b:ℂ} (c:a≠0) (h:a*b=0):b=0:=(mul_eq_zero.mp h).resolve_left c
lemma sq0 {x:ℂ} (h:x^2=0):x=0:=by simpa using h
lemma cs:(0:Fin 3).castSucc=0∧(1:Fin 3).castSucc=1∧(2:Fin 3).castSucc=2:=⟨rfl,rfl,rfl⟩
lemma lH {E E':Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
  [AddCommGroup E'] [Module ℂ E'] (g:E→ₗ[ℂ] E') (S:Submodule ℂ E):
  finrank ℂ (S.map g)+finrank ℂ (S⊓ker g:Submodule ℂ E)=finrank ℂ S:=by
 rw[←(Submodule.submoduleOfEquivInf _ _).finrank_eq,←(g.submoduleMap S).finrank_range_add_finrank_ker,range_submoduleMap,ker_submoduleMap];simp
lemma aGx {E:Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
  (f:E→ₗ[ℂ] ℂ) {S:Submodule ℂ E} (h:1<finrank ℂ S):∃x∈S⊓ker f,x≠0:=
 Submodule.exists_mem_ne_zero_of_ne_bot fun e=>by have r:=lH f S;rw[e,finrank_bot] at r;have:=(S.map f).finrank_le;simp at this;omega
lemma aGa {ι:Type*} [Fintype ι] (T:(ι→ℂ)→ₗ[ℂ] (ι→ℂ))
  (S:Submodule ℂ (ι→ℂ)) (b:∀x∈S,∀y∈S,∑p,T x p*y p=0):
  2*finrank ℂ S≤Fintype.card ι+finrank ℂ (S⊓ker T:Submodule ℂ (ι→ℂ)):=by
 classical
 let A:=(dotProductEquiv ℂ ι).toLinearMap.comp T
 have d:ker A=ker T:=by ext x;simp[A]
 have g:finrank ℂ (S.map A)≤finrank ℂ S.dualAnnihilator:=Submodule.finrank_mono fun _ ⟨x,f,e⟩=>e▸(Submodule.mem_dualAnnihilator _).mpr (b x f)
 have c:=lH A S;rw[d] at c;have a:=Subspace.finrank_add_finrank_dualAnnihilator_eq S;simp at a;omega
def al:bI→ₗ[ℂ] (Fin 3→ℂ):=funLeft ℂ ℂ (fun i:Fin 3=>(i,(0:Fin 5)))
def dl:bI→ₗ[ℂ] (Fin 3→ℂ):=al-funLeft ℂ ℂ (fun i:Fin 3=>(i,(1:Fin 5)))
def yp:bI→ₗ[ℂ] (Fin 3×Fin 3→ℂ):=funLeft ℂ ℂ (fun q:Fin 3×Fin 3=>(q.1,(![2,3,4]:Fin 3→Fin 5) q.2))
lemma aFc {M k:aC} {y:Fin 3×Fin 3→ℂ} (a:yp (aU M)=y)
 (b:yp (aU k)=0) (s:ℂ):yp (aU (M+s•k))=y:=by simp[a,b]
def e1 (a:Fin 3→ℂ):ℂ:=a 0+a 1+a 2
def e2 (a:Fin 3→ℂ):ℂ:=a 0*a 1+a 0*a 2+a 1*a 2
def p2 (a b:Fin 3→ℂ):ℂ:=e1 a*e1 b-(a 0*b 0+a 1*b 1+a 2*b 2)
def p3 (a b c:Fin 3→ℂ):ℂ:=a 0*(b 1*c 2+b 2*c 1)+a 1*(b 0*c 2+b 2*c 0)+a 2*(b 0*c 1+b 1*c 0)
def s2 (M:aC) (i j:Fin 4):ℂ:=M (i,0)*M (j,1)+M (i,1)*M (j,0)
def w3 (M:aC):Fin 3→ℂ:=fun c=>M (3,(![2,3,4]:Fin 3→Fin 5) c)
def b3 (M:aC):ℂ:=M (3,2)+M (3,3)+M (3,4)
def Qy (y:(Fin 3×Fin 3→ℂ)) (j k:Fin 3):ℂ:=p2 (fun c=>y (j,c)) (fun c=>y (k,c))
def q (h:(Fin 3→ℂ)) (y:(Fin 3×Fin 3→ℂ)):ℂ:=h 0*Qy y 1 2+h 1*Qy y 0 2+h 2*Qy y 0 1
lemma mA (M:aC):
  let r (i:Fin 3):Fin 3→ℂ:=fun c=>yp (aU M) (i,c)
  aO M=
   (M (0,0)+M (0,1))*p3 (r 1) (r 2) (w3 M)+(M (1,0)+M (1,1))*p3 (r 0) (r 2) (w3 M)+
   (M (2,0)+M (2,1))*p3 (r 0) (r 1) (w3 M)+(M (3,0)+M (3,1))*p3 (r 0) (r 1) (r 2)+
   s2 M 0 1*p2 (r 2) (w3 M)+s2 M 0 2*p2 (r 1) (w3 M)+s2 M 0 3*Qy (yp (aU M)) 1 2+
   s2 M 1 2*p2 (r 0) (w3 M)+s2 M 1 3*Qy (yp (aU M)) 0 2+s2 M 2 3*Qy (yp (aU M)) 0 1:=by
 dsimp only;rw[cK];simp(config:={decide:=true}) only[fH,ite_true,ite_false,add_zero,zero_add,Qy,p2,p3,e1,s2,w3,yp,aU,funLeft_apply,Matrix.cons_val,cs];ring
lemma uI (hL:aD L) (a:bF 0 dv∈L) (X:bI) (b:X∈W L):
  q (dl X) (yp X)=0:=by
 have h:=aC8 hL _ a X b;rw[F,mA] at h;rw[show aU (bF X dv)=X by funext ⟨i,j⟩;fin_cases i<;>rfl] at h;simp(config:={decide:=true}) only[bF,dv,Pi.sub_apply,Pi.single_apply,Matrix.cons_val,p2,p3,e1,s2,w3,ite_true,ite_false] at h;simp only[q,dl,al,LinearMap.sub_apply,Pi.sub_apply,funLeft_apply];linear_combination-h
lemma aHl (h:(Fin 3→ℂ)) (a b:(Fin 3×Fin 3→ℂ)):q h (a+b)+q h (a-b)=2*q h a+2*q h b:=by simp only[q,Qy,p2,e1,Pi.add_apply,Pi.sub_apply];ring
lemma aB9 (hL:aD L) (a:bF 0 dv∈L) {Z X:bI}
  (b:Z∈W L) (c:X∈W L) (d:dl X=0):q (dl Z) (yp X)=0:=by
 have e1:=uI hL a _ ((W L).add_mem b c);have e2:=uI hL a _ ((W L).sub_mem b c);have e3:=uI hL a _ b;rw[map_add,map_add,d,add_zero] at e1;rw[map_sub,map_sub,d,sub_zero] at e2;linear_combination(e1+e2-2*e3-aHl (dl Z) (yp Z) (yp X))/2
lemma sE (hL:aD L) (a:bF 0 dv∈L) (X:bI) (b:X∈W L):
  dl X 0+dl X 1+dl X 2=0:=by
 have h:=aB9 hL a b (aHy L) (by funext i;simp[dl,al]);simp only[q,Qy,p2,e1,yp,funLeft_apply,Pi.one_apply] at h;linear_combination h/6
def nn (y:(Fin 3×Fin 3→ℂ)) (j c:Fin 3):ℂ:=y (j,0)+y (j,1)+y (j,2)-y (j,c)
def Th (h:(Fin 3→ℂ)):(Fin 3×Fin 3→ℂ)→ₗ[ℂ] (Fin 3×Fin 3→ℂ) where
 toFun y:=fun p=> ![h 2*nn y 1 p.2+h 1*nn y 2 p.2,h 2*nn y 0 p.2+h 0*nn y 2 p.2,h 1*nn y 0 p.2+h 0*nn y 1 p.2] p.1
 map_add' y z:=by funext ⟨k,c⟩;fin_cases k<;>simp[nn]<;>ring
 map_smul' a y:=by funext ⟨k,c⟩;fin_cases k<;>simp[nn]<;>ring
lemma aFd (h:(Fin 3→ℂ)) (S:Submodule ℂ (Fin 3×Fin 3→ℂ)) (a:∀y∈S,q h y=0):
  ∀x∈S,∀y∈S,∑p,Th h x p*y p=0:=by
 intro x b y c;have e:∑p,Th h x p*y p=q h (x+y)-q h x-q h y:=by simp[Fintype.sum_prod_type,Fin.sum_univ_three,Th,nn,q,Qy,p2,e1];ring
 rw[e,a _ (S.add_mem b c),a x b,a y c];ring
lemma nnZ {u:Fin 3→ℂ} (h:∀c,u 0+u 1+u 2-u c=0) (c:Fin 3):u c=0:=by linear_combination(h 0+h 1+h 2)/2-h c
lemma aGm (h:(Fin 3→ℂ)) (f:h 0≠0) (g:h 1≠0) (i:h 2≠0):ker (Th h)= ⊥ :=by
 rw[ker_eq_bot'];intro y e;funext ⟨k,c⟩;refine nnZ (u:=fun c=>y (k,c)) (fun c=> ?_) c;have a:=congrFun e (0,c);have b:=congrFun e (1,c);have d:=congrFun e (2,c);simp[Th,nn] at a b d;fin_cases k<;>dsimp only[Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk]
 ·exact aA4 (mul_ne_zero g i) (by linear_combination(h 1*b+h 2*d-h 0*a)/2)
 ·exact aA4 (mul_ne_zero f i) (by linear_combination(h 0*a+h 2*d-h 1*b)/2)
 ·exact aA4 (mul_ne_zero f g) (by linear_combination(h 0*a+h 1*b-h 2*d)/2)
lemma aFe (hL:aD L) {X:bI} (b:X∈W L) (d:yp X=0):∃t∈L,X=aU t:=by
 obtain⟨t,a,c,rfl⟩:=aE5 b;have z:aO (t+c•1)=0:=by rw[mA,show yp (aU (t+c•1))=0 from d];simp[p2,p3,e1,Qy]
 exact⟨t,a,by simp[show c=0 by simpa using(vD hL a c).symm.trans z]⟩
lemma aGy {t:aC} (a:dl (aU t)=0):
  t (0,1)=t (0,0)∧t (1,1)=t (1,0)∧t (2,1)=t (2,0):=
 have e (i:Fin 3):t (i.castSucc,1)=t (i.castSucc,0):=(sub_eq_zero.mp (congrFun a i)).symm
 ⟨e 0,e 1,e 2⟩
lemma aHm (hL:aD L) {t:aC} (f:t∈L) (g:yp (aU t)=0)
  (e:dl (aU t)=0):
  let a:=al (aU t)
  e2 a*b3 t=0∧2*e2 a+e1 a*(b3 t-2*e1 a)=0:=by
 have zT (s:ℂ):=hL _ (L.smul_mem s f);have b:=zT 1;have c:=zT (-1);have d:=zT 2;rw[mA,aFc (y:=1) rfl g] at b c d;simp only[al,aU,funLeft_apply,Pi.add_apply,Pi.one_apply,Pi.smul_apply,smul_eq_mul,p2,p3,e1,e2,s2,w3,b3,Qy,Matrix.cons_val,aGy e,cs] at b c d ⊢
 exact⟨by linear_combination(-b/2-c/6+d/6)/4,by linear_combination(b+c)/12-(t (0,0)+t (1,0)+t (2,0))*(6*b-2*c-d)/144⟩
lemma aGn {X:bI} (c:dl X=0) (a:yp X=0) (b:∀i,X (i,0)=0):X=0:=by
 funext ⟨i,j⟩;fin_cases j
 ·exact b i
 ·exact(sub_eq_zero.mp (congrFun c i)).symm.trans (b i)
 ·exact congrFun a (i,0)
 ·exact congrFun a (i,1)
 ·exact congrFun a (i,2)
lemma aCa (hL:aD L):finrank ℂ (W L⊓ker dl⊓ker yp:Submodule ℂ bI)≤1:=by
 set A:=W L⊓ker dl⊓ker yp;have J:A⊓ker al= ⊥ :=eq_bot_iff.mpr fun _ ⟨⟨⟨_,H⟩,M⟩,G⟩=>aGn H M (congrFun G)
 have r:=lH al A;rw[J,finrank_bot,add_zero] at r;rw[←r];set S:=A.map al;have j:∀a∈S,e2 a*(e2 a-e1 a^2)=0:=by rintro _ ⟨X,⟨⟨q,s⟩,k⟩,rfl⟩;obtain⟨t,K,rfl⟩:=aFe hL q k;obtain⟨N,O⟩:=aHm hL K k s;linear_combination e2 (al (aU t))/2*O-e1 (al (aU t))/2*N
 by_contra! p;obtain⟨u,⟨g,x⟩,w⟩:=aGx ((proj 0:(Fin 3→ℂ)→ₗ[ℂ] ℂ)+proj 1+proj 2) p;have c:u 0= -u 1-u 2:=by have h:u 0+u 1+u 2=0:=x;linear_combination h
 have e:u 1^2+u 1*u 2+u 2^2=0:=sq0<| by have:=j u g;simp only[e1,e2,c] at this;linear_combination this
 have f:u 1*u 2≠0:=fun h=>w<| by
  have E:u 1=0:=sq0<| sq0 (by linear_combination u 1^2*e-(u 1^2+u 1*u 2)*h)
  have F:u 2=0:=sq0<| sq0 (by linear_combination u 2^2*e-(u 2^2+u 1*u 2)*h)
  have Q:u 0=0:=by linear_combination c-E-F
  funext i;fin_cases i<;>assumption
 obtain⟨v,⟨l,y⟩,n⟩:=aGx (proj 0:(Fin 3→ℂ)→ₗ[ℂ] ℂ) p;have m:v 0=0:=y;have o:=j v l;have C:=j _ (S.add_mem l g);have B:=j _ (S.sub_mem l g);simp only[e1,e2,Pi.add_apply,Pi.sub_apply,m,c] at o C B;have d:u 1*v 1+u 2*v 2=0:=sq0<|by linear_combination(C+B-2*o)/2-(u 1^2+u 1*u 2+u 2^2-2*v 1*v 2+(v 1+v 2)^2)*e
 have z:v 2=0:=sq0<| sq0<| aA4 (by simp[f]:2*(u 1*u 2)^2≠0) (b:=(v 2^2)^2) (by linear_combination-u 1^4*o-d*u 1*v 2*(u 1^2*(v 1^2+v 1*v 2+v 2^2))+u 2*v 2*u 1*v 2*(d*(u 1*v 1-u 2*v 2+u 1*v 2)+v 2^2*e))
 have P:v 1=0:=aA4 (left_ne_zero_of_mul f) (by rw[z] at d;linear_combination d);exact n<| funext fun i=>by fin_cases i<;>assumption
lemma aHn (hL:aD L) (m:finrank ℂ (W L)=8) (a:bF 0 dv∈L) (Z:bI)
  (j:Z∈W L) (d:dl Z 0≠0) (f:dl Z 1≠0) (g:dl Z 2≠0):False:=by
 have w:=aGa (Th (dl Z)) ((W L⊓ker dl).map yp)
  (aFd (dl Z) _ fun _ ⟨X,⟨b,c⟩,e⟩=>e▸aB9 hL a j b c)
 rw[aGm _ d f g,inf_bot_eq,finrank_bot] at w;have n:=lH dl (W L);have o:=lH yp (W L⊓ker dl);have l:=aCa hL;have im:=Submodule.finrank_lt (s:=(W L).map dl) fun h=>by obtain⟨X,i,k⟩:=(Submodule.eq_top_iff'.mp h) 1;have:=sE hL a X i;rw[k] at this;norm_num at this
 simp at w im;omega
lemma zO {a b C:ℂ} {g:ℂ→ℂ} (c:C≠0) (h:∀s,(a+s*b)*g s=C):b=0:=by by_contra d;have e:=h (-a/b);rw[show a+ -a/b*b=0 by field_simp;ring,zero_mul] at e;exact c e.symm
def emb:(Fin 3→ℂ)→ₗ[ℂ] (Fin 3×Fin 3→ℂ) where
 toFun u p:=if p.1=2 then 0 else u p.2
 map_add' _ _:=by funext ⟨i,c⟩;by_cases h:i=2<;>simp[h]
 map_smul' _ _:=by funext ⟨i,c⟩;by_cases h:i=2<;>simp[h]
lemma aDr (hL:aD L) (hW:finrank ℂ (W L)=8) (O:bF 0 dv∈L)
  (Z:bI) (E:Z∈W L) (P:dl Z 0≠0) (A:dl Z 2=0):False:=by
 have V:∀{X},X∈W L→dl X 2=0:=by
  by_contra! hn;obtain⟨X,m,hx⟩:=hn;have p (s:ℂ) (hs:s≠0):(dl Z 0+s*dl X 0)*(dl Z 1+s*dl X 1)=0:=by
   by_contra h;exact aHn hL hW O _ ((W L).add_mem E ((W L).smul_mem s m))
    (by simpa using left_ne_zero_of_mul h) (by simpa using right_ne_zero_of_mul h) (by simp[A,hs,hx])
  exact P<| sq0<| by linear_combination-(3*p 1 one_ne_zero-3*p 2 two_ne_zero+p 3 (by norm_num))+dl Z 0*(sE hL O Z E-A)
 have C {X} (m:X∈W L):dl X 1= -dl X 0:=by linear_combination sE hL O X m-V m
 have dz {X} (m:X∈W L) (hf:dl X 0=0):dl X=0:=funext fun i=>by
  fin_cases i; · exact hf
  ·exact(C m).trans (by simp[hf])
  ·exact V m
 have hq:∀y∈(W L).map yp,q (dl Z) y=0:=by
  rintro _ ⟨X,m,rfl⟩;by_cases hx:dl X 0=0
  ·exact aB9 hL O E m (dz m hx)
  ·have g:=uI hL O X m;simp only[q,V m,C m,A,C E] at g ⊢
   linear_combination dl Z 0*aA4 hx (b:= Qy (yp X) 1 2-Qy (yp X) 0 2) (by linear_combination g)
 have w:=aGa (Th (dl Z)) _ (aFd (dl Z) _ hq);set K:=ker (Th (dl Z));have N:K=range emb:=by
  ext y;constructor
  ·intro hy;have y2:=nnZ (u:=fun c=>y (2,c)) fun c=>by
    have a:=congrFun hy (0,c);simp[Th,nn,A,C E,P] at a;exact a
   have c1 (c):y (0,c)=y (1,c):=sub_eq_zero.mp<| nnZ (u:=fun c=>y (0,c)-y (1,c)) (fun c=>aA4 P (by have d:=congrFun hy (2,c);simp[Th,nn,C E] at d;linear_combination-d)) c
   exact⟨fun c=>y (0,c),funext fun⟨i,c⟩=>by fin_cases i<;>simp[emb,y2,c1]⟩
  ·rintro⟨u,rfl⟩;funext ⟨i,c⟩;fin_cases i<;>simp[Th,nn,emb,A,C E]
 have kd:finrank ℂ K=3:=by rw[N,finrank_range_of_inj fun u v h=>funext fun c=>congrFun h (0,c)];simp
 have a6:(W L).map yp⊓K≤K:=inf_le_right;have ki:=Submodule.finrank_mono a6;have r1:=lH yp (W L);set U:=W L⊓ker yp
 let f:bI→ₗ[ℂ] ℂ:=(proj 0:(Fin 3→ℂ)→ₗ[ℂ] ℂ).comp dl
 have r2:=lH f U;have im:finrank ℂ (U.map f)≤1:=by simpa using(U.map f).finrank_le
 have ab:=(Submodule.finrank_mono (show U⊓ker f≤W L⊓ker dl⊓ker yp from fun X ⟨⟨m,hy⟩,hf⟩=>⟨⟨m,dz m hf⟩,hy⟩)).trans (aCa hL);simp at w;have b9:range emb≤(W L).map yp:=by rw[←N,←Submodule.eq_of_le_of_finrank_le a6 (by omega)];exact inf_le_left
 obtain⟨kA,⟨⟨R,o⟩,a9⟩,a8⟩:=aGx f (by omega:1<finrank ℂ U);obtain⟨_,⟨k1,⟨Q,F⟩,rfl⟩,a7⟩:=Submodule.exists_mem_ne_zero_of_ne_bot (p:=U.map f)
  fun e=>by rw[e,finrank_bot] at r2;omega
 have x:=dz R a9;obtain⟨l,G,rfl⟩:=aFe hL R o;obtain⟨n,a5,rfl⟩:=aFe hL Q F;have T:=(aHm hL G o x).2;simp only[e1,e2,al,aU,funLeft_apply,cs] at T;have a3 (H:l (0,0)=0) (J:l (1,0)=0) (a2:l (2,0)=0):False:=a8 (aGn x o fun i=>by fin_cases i<;>assumption);have hr {t k:aC} (ht:t∈L) (N:k∈L) (c s:ℂ):aO (t+c•1+s•k)=120*c^4:=by rw[show t+c•1+s•k=t+s•k+c•1 by abel];exact vD hL (L.add_mem ht (L.smul_mem s N)) c
 have B (j:Fin 3):∃t∈L,yp (aU t)=emb (Pi.single j 1):=by
  obtain⟨X,m,a4⟩:=b9 ⟨Pi.single j 1,rfl⟩;obtain⟨t,ht,c,rfl⟩:=aE5 m;by_cases hc:c=0
  ·exact⟨t,ht,by simpa[hc] using a4⟩
  ·let M:=t+c•(1:aC);have hC:(120:ℂ)*c^4≠0:=by simp[hc]
   have b1:M (2,1)=M (2,0):=(sub_eq_zero.mp (V m)).symm;have zT (s:ℂ):(M (2,0)+s*l (2,0))*
     (((M (0,0)+M (0,1)+M (1,0)+M (1,1))+s*(2*(l (0,0)+l (1,0))))*
      p2 (Pi.single j 1) (w3 (M+s•l)))=120*c^4:=by
    have h:=hr ht G c s;rw[mA,aFc (M:=M) a4 o] at h;simp only[M,Pi.add_apply,Pi.smul_apply,smul_eq_mul,s2,b1,aGy x,emb,coe_mk,AddHom.coe_mk] at h ⊢
    fin_cases j<;>simp[Qy,p2,p3,e1] at h ⊢ <;>linear_combination h
   have z1:l (2,0)=0:=zO hC zT;have z2:2*(l (0,0)+l (1,0))=0:=zO hC fun s=>(mul_left_comm _ _ _).trans (zT s)
   have J:l (1,0)= -l (0,0):=by linear_combination z2/2
   rw[J,z1] at T;have H:l (0,0)=0:=sq0 (by linear_combination-T/2);exact(a3 H (by rw[J,H,neg_zero]) z1).elim
 obtain⟨t0,b2,b5⟩:=B 0;obtain⟨c0,b0,b6⟩:=B 1;obtain⟨t2,b4,b7⟩:=B 2
 let M:aC:= -(t0+c0+t2)+1
 let ye:Fin 3×Fin 3→ℂ:=fun p=>if p.1=2 then 1 else 0
 have b8:yp (aU M)=ye:=by simp only[M,map_add,map_neg,b5,b6,b7];funext ⟨i,c⟩;fin_cases i<;>fin_cases c<;>simp[ye,emb,yp,aU,Pi.single_apply]
 have r (k:aC) (N:k∈L) (hky:yp (aU k)=0):b3 k=0∧s2 k 0 1=0:=by
  have zT (s:ℂ):(b3 M+s*b3 k)*(2*s2 (M+s•k) 0 1)=120:=by
   have h:aO (M+s•k)=120:=by simpa[M] using hr (L.neg_mem (L.add_mem (L.add_mem b2 b0) b4)) N 1 s
   rw[mA,aFc b8 hky] at h;simp(config:={decide:=true}) only[Pi.add_apply,Pi.smul_apply,smul_eq_mul,ye,Qy,p2,p3,e1,w3,b3,Matrix.cons_val,ite_true,ite_false] at h ⊢
   linear_combination h
  have hB:=zO (by norm_num:(120:ℂ)≠0) zT;have k0:=zT 0;have k1:=zT 1;have km:=zT (-1);rw[hB] at k0 k1 km;simp only[s2,Pi.add_apply,Pi.smul_apply,smul_eq_mul] at k0 k1 km ⊢
  exact⟨hB,aA4 (a:=b3 M) (fun z=>by simp[z] at k0) (by linear_combination(k1+km-2*k0)/4)⟩
 obtain⟨bA,pA⟩:=r l G o;obtain⟨_,p1⟩:=r n a5 F;obtain⟨_,pp⟩:=r (n+l) (L.add_mem a5 G) (by simp[mem_ker.mp F,mem_ker.mp o]);simp only[s2,Pi.add_apply,aGy x] at pA p1 pp
 let s0:=n (0,0)+n (0,1);let s1:=n (1,0)+n (1,1)
 have ss:s0*s1≠0:=fun z=>a7<| sq0<| by have f1:n (1,0)-n (1,1)= -(n (0,0)-n (0,1)):=C Q;change(n (0,0)-n (0,1))^2=0;linear_combination-z+2*p1+(n (0,0)-n (0,1))*f1
 have S:l (0,0)*s1+l (1,0)*s0=0:=by linear_combination pp-p1-pA
 have⟨H,J⟩:l (0,0)=0∧l (1,0)=0:=by
  rcases mul_eq_zero.mp (by linear_combination pA/2:l (0,0)*l (1,0)=0) with h|h
  ·exact⟨h,by simpa[h,left_ne_zero_of_mul ss] using S⟩
  ·exact⟨by simpa[h,right_ne_zero_of_mul ss] using S,h⟩
 rw[H,J,bA] at T;exact a3 H J (sq0 (by linear_combination-T/2))
end Ac.Ah.Au
namespace Ac.Ah
open Aa Au Finset LinearMap Module
lemma xU {L:Submodule ℂ aC} (hL:aD L) (z:aX L=8)
  (F:u L 3=1) (n:bF 0 (Pi.single 0 1-Pi.single 1 1)∈L):
  ∀t∈L,∀i:Fin 3,aU t (i,0)=aU t (i,1):=by
 have o:=aGv hL z F
 suffices aAr:∀X∈W L,dl X=0 from fun t E i=>sub_eq_zero.mp (congrFun (aAr _ (Submodule.mem_sup_left ⟨t,E,rfl⟩)) i)
 by_contra! C;obtain⟨Z,s,v⟩:=C;by_cases a:∀i,dl Z i≠0
 ·exact aHn hL o n Z s (a 0) (a 1) (a 2)
 push Not at a;obtain⟨k,B⟩:=a
 let ρ:Equiv.Perm (Fin 3):=Equiv.swap k 2
 let ρ4:Equiv.Perm (Fin 4):=Equiv.swap k.castSucc 2
 let R:aC→ₗ[ℂ] aC:=funLeft ℂ ℂ (fun p:Fin 4×Fin 5=>(ρ4 p.1,p.2))
 let RT:bI→ₗ[ℂ] bI:=funLeft ℂ ℂ (fun p:Fin 3×Fin 5=>(ρ p.1,p.2))
 have m:Function.Injective RT:=fun x y h=>funext fun p=>by simpa[RT] using congrFun h (ρ.symm p.1,p.2)
 have d:aD (L.map R):=by rintro _ ⟨x,G,rfl⟩;rw[←hL x G,aO,aO,←(Equiv.embeddingCongr ρ4.symm (Equiv.refl (Fin 5))).sum_comp];exact sum_congr rfl fun e _=>by simpa[R] using Equiv.prod_comp ρ4 fun r=>(1+x) (r,e r)
 have f:W (L.map R)=(W L).map RT:=by unfold W;rw[Submodule.map_sup,Submodule.map_span,Set.image_singleton,←Submodule.map_comp,←Submodule.map_comp,show aU.comp R=RT.comp aU from LinearMap.ext fun t=>funext fun⟨i,j⟩=>by change t (ρ4 i.castSucc,j)=t ((ρ i).castSucc,j);fin_cases k<;>fin_cases i<;>rfl];rfl
 have q:finrank ℂ (W (L.map R))=8:=by rw[f,←(Submodule.equivMapOfInjective RT m (W L)).finrank_eq,o]
 have c:bF 0 dv∈L.map R:=⟨_,n,funext fun⟨i,j⟩=>by change bF 0 _ (ρ4 i,j)=bF 0 _ (i,j);fin_cases k<;>fin_cases i<;>rfl⟩
 have g:RT Z∈W (L.map R):=f▸⟨Z,s,rfl⟩;have b:dl (RT Z) 2=0:=by simpa[RT,dl,al,ρ] using B
 have l:dl (RT Z) 0≠0:=fun w=>v<| funext fun i=>by
  have H:dl (RT Z) 1=0:=by linear_combination sE d c _ g-w-b
  have A (j:Fin 3):dl (RT Z) j=0:=by fin_cases j<;>assumption
  simpa[RT,dl,al] using A (ρ.symm i)
 exact aDr d q c (RT Z) g l b
end Ac.Ah
lemma Ac.aCb:Ac.mI:=Ac.Ah.aFb Ac.Ah.xU
namespace Ac.Af
open Aa Finset
lemma aFf {A:Finset (Fin 5)} (d:A.card=3):
  ∃σ:Equiv.Perm (Fin 5),∀k,k∈A↔k=σ 0∨k=σ 1∨k=σ 2:=by
 classical
 have l:Aᶜ.card=2:=by rw[card_compl,d];decide
 obtain⟨a,b,c,_,_,_,h⟩:=card_eq_three.mp d;obtain⟨p,q,_,e⟩:=card_eq_two.mp l
 let f:Fin 5→Fin 5:= ![a,b,c,p,q]
 have j:Function.Surjective f:=by
  intro k;by_cases i:k∈A
  ·rw[h] at i;simp only[mem_insert,mem_singleton] at i;rcases i with rfl|rfl|rfl
   ·exact⟨0,rfl⟩
   ·exact⟨1,rfl⟩
   ·exact⟨2,rfl⟩
  ·have g:=mem_compl.mpr i;rw[e] at g;simp only[mem_insert,mem_singleton] at g;rcases g with rfl|rfl
   ·exact⟨3,rfl⟩
   ·exact⟨4,rfl⟩
 exact⟨Equiv.ofBijective f j.bijective_of_finite,fun k=>by change k∈A↔k=a∨k=b∨k=c;simp[h]⟩
abbrev tcI (j:Fin 3):Fin 5:=j.castLE (by decide)
abbrev wM (L:Submodule ℂ aC) (i:Fin 4) (A:Finset (Fin 5)):=W L i⊓LinearMap.ker (aK A)
def jY (σ:Equiv.Perm (Fin 5)):bI→ₗ[ℂ] (Fin 3→Fin 2→ℂ) where
 toFun x r b:=x (r,σ (if b=0 then 3 else 4))
 map_add' _ _:=rfl
 map_smul' _ _:=rfl
lemma jZ {L:Submodule ℂ aC} {i:Fin 4} {A:Finset (Fin 5)}
  {σ:Equiv.Perm (Fin 5)} (hσ:∀k,k∈A↔k=σ 0∨k=σ 1∨k=σ 2)
  {x:bI} (f:x∈wM L i A) (r:Fin 3) (j:Fin 5) (d:j∈A):
  x (r,j)= -((jY σ x) r 0+(jY σ x) r 1):=by
 have z (k:Fin 5) (e:k∈A):x (r,k)=(∑l,x (r,l))/2:=by have b:aK A x=0:=f.2;have c:=congrFun b (A.equivFin ⟨k,e⟩,r);exact sub_eq_zero.mp (by simpa[aK,aA] using c)
 have a:=Equiv.sum_comp σ (fun k=>x (r,k));rw[Fin.sum_univ_five] at a;rw[z _ ((hσ _).mpr (.inl rfl)),z _ ((hσ _).mpr (.inr (.inl rfl))),z _ ((hσ _).mpr (.inr (.inr rfl)))] at a;change x (r,j)= -(x (r,σ 3)+x (r,σ 4))
 linear_combination z j d+a
lemma aGb {L:Submodule ℂ aC} (hL:aD L) (n:aX L=8)
  {i:Fin 4} (v:u L i=2) {A:Finset (Fin 5)} (o:A.card=3)
  (f:U L i=bJ A) {σ:Equiv.Perm (Fin 5)}
  (hσ:∀k,k∈A↔k=σ 0∨k=σ 1∨k=σ 2):
  3≤Module.finrank ℂ ((wM L i A).map (jY σ)):=by
 classical
 let w:aH:=fun k=>if k∈A then(if k=σ 0 then-2 else 1) else 0
 have l:w∈U L i:=by
  rw[f];constructor
  ·rw[←Equiv.sum_comp σ w,Fin.sum_univ_five];norm_num[w,hσ,Equiv.apply_eq_iff_eq]
  ·intro j h;simp[w,h]
 have t:=dO hL l A (fun k=>by by_cases a:k∈A<;>by_cases c:k=σ 0<;>norm_num[w,a,c]);have s:Module.finrank ℂ ((W L i).map (aK A))+
   Module.finrank ℂ (wM L i A)=Module.finrank ℂ (W L i):=by
  unfold wM;rw[←(Submodule.submoduleOfEquivInf _ _).finrank_eq,
   ←((aK A).submoduleMap (W L i)).finrank_range_add_finrank_ker,
   LinearMap.range_submoduleMap,LinearMap.ker_submoduleMap]
  simp
 let F:=(jY σ).domRestrict (wM L i A)
 have g:Function.Injective F:=by
  intro x y e;apply Subtype.ext;funext ⟨r,k⟩;have b:jY σ x.val=jY σ y.val:=e;by_cases a:k∈A
  ·rw[jZ hσ x.2 r k a,jZ hσ y.2 r k a,b]
  ·obtain⟨j,rfl⟩:=σ.surjective k;fin_cases j
   ·exact(a ((hσ _).mpr (.inl rfl))).elim
   ·exact(a ((hσ _).mpr (.inr (.inl rfl)))).elim
   ·exact(a ((hσ _).mpr (.inr (.inr rfl)))).elim
   ·exact congrFun (congrFun b r) 0
   ·exact congrFun (congrFun b r) 1
 have d:=LinearMap.finrank_range_of_inj g;have e:LinearMap.range F=(wM L i A).map (jY σ):=by
  ext p;constructor
  ·rintro⟨x,rfl⟩;exact⟨_,x.2,rfl⟩
  ·rintro⟨x,m,rfl⟩;exact⟨⟨x,m⟩,rfl⟩
 rw[e] at d;have q:=jP hL i;omega
lemma aFg {L:Submodule ℂ aC} (hL:aD L) {i:Fin 4}
  {A:Finset (Fin 5)} (c:U L i=bJ A) {j k:Fin 5}
  (d:j∈A) (e:k∈A) {x:bI} (g:x∈W L i):
  ∑r:Fin 3,(x (r,j)-x (r,k))=0:=by
 classical
 let w:aH:=fun b=>(if b=j then 1 else 0)-(if b=k then 1 else 0)
 have f:w∈U L i:=by
  rw[c];constructor
  ·simp[w,sum_sub_distrib]
  ·intro b a;simp[w,show b≠j from fun h=>a (h▸d),show b≠k from fun h=>a (h▸e)]
 have t:=eR hL f g;simp[w,sub_mul,ite_mul,sum_sub_distrib] at t;simp only[aV,aA] at t;rw[Fin.sum_univ_three];linear_combination t
lemma aGc (a b c:ℂ) (i:¬(a=b∧b=c)):
  ∃h:Fin 3→ℂ,h≠0∧(∑r,h r)=0∧
  ∀
   f:Fin 3→ℂ,(∑r,f r)=0→f 0*a+f 1*b+f 2*c=0→
   ∃t:ℂ,f=t•h:=by
 let h:Fin 3→ℂ:= ![b-c,c-a,a-b]
 refine⟨h,?_,?_,?_⟩
 ·intro m;exact i ⟨sub_eq_zero.mp (congrFun m 2),sub_eq_zero.mp (congrFun m 0)⟩
 ·rw[Fin.sum_univ_three];change b-c+(c-a)+(a-b)=0;ring
 ·intro f d k;rw[Fin.sum_univ_three] at d;by_cases n:b=c
  ·subst c;have hab:b-a≠0:=sub_ne_zero.mpr (fun e=>i ⟨e.symm,rfl⟩);have l:f 0=0:=(mul_eq_zero.mp (show f 0*(b-a)=0 by linear_combination b*d-k)).resolve_right hab;refine⟨f 1/(b-a),?_⟩;funext j;fin_cases j<;>simp[h,Pi.smul_apply,l,hab]
   field_simp[hab];linear_combination(b-a)*d-(b-a)*l
  ·have g:b-c≠0:=sub_ne_zero.mpr n;refine⟨f 0/(b-c),?_⟩;funext j;fin_cases j<;>simp[h,Pi.smul_apply,g]<;>field_simp[g]
   ·linear_combination k-c*d
   ·linear_combination b*d-k
end Ac.Af
namespace Ac.Af
open Aa Finset
lemma oU {L:Submodule ℂ aC} (hL:aD L) {i:Fin 4}
  (σ:Equiv.Perm (Fin 5))
  (h:∀m:Fin 3,∃v∈W L i,(∀k,v (m,k)=0)∧
    (∀r≠m,∀j:Fin 5,(j=σ 0∨j=σ 1∨j=σ 2)→v (r,j)= -1)):
  False:=by
 classical
 choose v hv hz hn using h
 let P:=L.map (bH i)
 have x (m:Fin 3):v m∈P:=fC hL (hv m) (hz m);have y:(1/2:ℂ)•(∑m,v m)∈P:=P.smul_mem _ (P.sum_mem fun m _=>x m);obtain⟨t,z,l⟩:=y;have n (r:Fin 3) (j:Fin 5) (o:j=σ 0∨j=σ 1∨j=σ 2):
   (1+t) (iX i r,j)=0:=by
  change 1+(bH i t) (r,j)=0;rw[l,Fin.sum_univ_three];have u (m:Fin 3):v m (r,j)=if r=m then 0 else-1:=by
   split_ifs with hr
   ·subst r;exact hz m j
   ·exact hn m r hr j o
  simp only[Pi.smul_apply,smul_eq_mul,Pi.add_apply,u];fin_cases r<;>norm_num
 have c (a:Fin 5):
   (σ a=σ 0∨σ a=σ 1∨σ a=σ 2)∨
     σ a∈({σ 3,σ 4}:Finset (Fin 5)):=by
  fin_cases a<;>simp
 have b:aO (1+t)=0:=by
  apply sum_eq_zero;intro f _
  let g:Fin 3→Fin 5:=fun r=>f (iX i r)
  have w:Function.Injective g:=fun _ _ e=>Fin.succ_injective _ ((Equiv.swap 0 i).injective (f.injective e))
  by_contra s;have p:univ.image g⊆({σ 3,σ 4}:Finset (Fin 5)):=by
   intro j o;obtain⟨r,_,rfl⟩:=mem_image.mp o;rcases (show(g r=σ 0∨g r=σ 1∨g r=σ 2)∨
     g r∈({σ 3,σ 4}:Finset (Fin 5)) by
    simpa only[Equiv.apply_symm_apply] using c (σ.symm (g r))) with hbad | hout
   ·exact(s (prod_eq_zero (mem_univ (iX i r)) (n r (g r) hbad))).elim
   ·exact hout
  have d:=card_le_card p;have q:σ 3≠σ 4:=σ.injective.ne (by decide);rw[card_image_of_injective _ w,card_univ,Fintype.card_fin,card_pair_eq_two_iff.mpr q] at d;omega
 rw[hL t z] at b;norm_num at b
end Ac.Af
namespace Ac.Af
open Aa Finset Av
def aN (y:Fin 3→Fin 2→ℂ) (s t:Fin 3):ℂ:=(y s 0+y s 1)*(y t 0+y t 1)+y s 0*y t 0+y s 1*y t 1
lemma nY (j:Fin 5) (x y z:aH):
  G3 j x y z=G3 j y x z:=by
 simp only[cJ,mul_comm,mul_left_comm];ring
lemma iL (j:Fin 5) (x y z:aH):
  G3 j x y z=G3 j z x y:=by
 simp only[cJ,mul_comm,mul_left_comm];ring
lemma pW (j k:Fin 5) (x y z:aH) (d:ℂ)
  (b:y k=y j) (c:z k=z j)
  (e:(∑l,y l)=2*y j) (f:(∑l,z l)=2*z j)
  (a:(∑l,y l*z l)=2*y j*z j+d):
  G3 j x y z-G3 k x y z=(x j-x k)*d:=by
 rw[cJ,cJ,e,f,a,b,c];ring
def fY (j:Fin 5) (x Y:bI):ℂ:=
 G3 j (fun l=>x (0,l)) (fun l=>Y (1,l)) (fun l=>Y (2,l))+
 G3 j (fun l=>x (1,l)) (fun l=>Y (0,l)) (fun l=>Y (2,l))+
 G3 j (fun l=>x (2,l)) (fun l=>Y (0,l)) (fun l=>Y (1,l))
lemma iM (j:Fin 5) (x Y:bI):
  G (x+Y) j+G (x-Y) j-2*G x j=2*fY j x Y:=by
 unfold G fY;rw[nY j (fun l=>x (1,l)),iL j (fun l=>x (2,l)),iL j (fun l=>Y (1,l))];simp only[G3,Pi.add_apply,Pi.sub_apply,mul_add,mul_sum,←sum_add_distrib,←sum_sub_distrib];apply sum_congr rfl;intro l _;apply sum_congr rfl;intro m _;apply sum_congr rfl;intro n _
 split<;>ring
lemma tO {L:Submodule ℂ aC} (g:aD L)
  {i:Fin 4} {A:Finset (Fin 5)} (m:U L i=bJ A)
  {j k:Fin 5} (n:j∈A) (o:k∈A) {v:bI} (p:v∈W L i):
  G v j=G v k:=by
 classical
 let w:aH:=Pi.single j 1-Pi.single k 1
 have q:w∈U L i:=by
  rw[m];change(∑l,w l)=0∧∀l∉A,w l=0;constructor
  ·simp[w,sum_sub_distrib]
  ·intro l f;have c:l≠j:=fun e=>f (e▸n)
   have d:l≠k:=fun e=>f (e▸o)
   simp[w,c,d]
 have h:=dU g q p;have b (a:Fin 5):(∑l,(Pi.single a 1:aH) l*G v l)=G v a:=by simp[Pi.single_apply,ite_mul]
 exact sub_eq_zero.mp (by simpa only[w,Pi.sub_apply,sub_mul,sum_sub_distrib,b] using h)
lemma pX {L:Submodule ℂ aC} (E:aD L) {i:Fin 4}
  {A:Finset (Fin 5)} (G:U L i=bJ A) {σ:Equiv.Perm (Fin 5)}
  (F:∀k,k∈A↔k=σ 0∨k=σ 1∨k=σ 2)
  {x Y:bI} (g:x∈W L i) (q:Y∈W L i) (y:Fin 3→Fin 2→ℂ)
  (b:∀r (k:Fin 3),Y (r,σ (Fin.castLE (by decide:3≤5) k))=
    -(y r 0+y r 1))
  (w:∀r,Y (r,σ 3)=y r 0) (z:∀r,Y (r,σ 4)=y r 1)
  {j k:Fin 3}:
  (x (0,σ (Fin.castLE (by decide:3≤5) j))-
    x (0,σ (Fin.castLE (by decide:3≤5) k)))*aN y 1 2+
  (x (1,σ (Fin.castLE (by decide:3≤5) j))-
    x (1,σ (Fin.castLE (by decide:3≤5) k)))*aN y 0 2+
  (x (2,σ (Fin.castLE (by decide:3≤5) j))-
    x (2,σ (Fin.castLE (by decide:3≤5) k)))*aN y 0 1=0:=by
 let a (l:Fin 3):=σ (Fin.castLE (by decide:3≤5) l)
 have u (l:Fin 3):a l∈A:=by fin_cases l<;>exact(F _).2 (by tauto)
 have h (r:Fin 3):Y (r,σ 0)= -(y r 0+y r 1):=b r 0;have m (r:Fin 3):Y (r,σ 1)= -(y r 0+y r 1):=b r 1;have n (r:Fin 3):Y (r,σ 2)= -(y r 0+y r 1):=b r 2;have B (r:Fin 3):(∑l,Y (r,l))=2*Y (r,a j):=by rw[←Equiv.sum_comp σ (fun l=>Y (r,l)),Fin.sum_univ_five];rw[h,m,n,w,z,show Y (r,a j)= -(y r 0+y r 1) from b r j];ring
 have C (s t:Fin 3):(∑l,Y (s,l)*Y (t,l))=
   2*Y (s,a j)*Y (t,a j)+aN y s t:=by
  rw[←Equiv.sum_comp σ (fun l=>Y (s,l)*Y (t,l)),Fin.sum_univ_five];simp only[h,m,n,w,z,show ∀r,Y (r,a j)= -(y r 0+y r 1) from fun r=>b r j,aN];ring
 have e (r:Fin 3):Y (r,a k)=Y (r,a j):=(b r k).trans (b r j).symm;have f (r s t:Fin 3):=
  pW (a j) (a k) (fun l=>x (r,l)) (fun l=>Y (s,l))
   (fun l=>Y (t,l)) (aN y s t)
   (e s) (e t) (B s) (B t) (C s t)
 have c {v:bI} (H:v∈W L i):=tO E G (u j) (u k) H;have d:=iM (a j) x Y;have p:=iM (a k) x Y;rw[c ((W L i).add_mem g q),c ((W L i).sub_mem g q),c g] at d;change(x (0,a j)-x (0,a k))*aN y 1 2+
  (x (1,a j)-x (1,a k))*aN y 0 2+
  (x (2,a j)-x (2,a k))*aN y 0 1=0
 have o:fY (a j) x Y-fY (a k) x Y=0:=by linear_combination(p-d)/2
 unfold fY at o;linear_combination o-f 0 1 2-f 1 0 2-f 2 0 1
end Ac.Af
namespace Ac.Af
def aF (p q:Fin 2→ℂ):ℂ:=p 0*q 0+p 1*q 1+(p 0+p 1)*(q 0+q 1)
abbrev dF:=Ai.E×Ai.E
lemma bT (p q:Ai.E):
  aF p q=aF q p:=by
 unfold aF;ring
lemma cU (p:Ai.E):
  aF p 0=0:=by
 simp[aF]
lemma kB (p:Ai.E):
  aF 0 p=0:=by
 simp[aF]
lemma eO (p:Ai.E)
  (h:∀q:Ai.E,aF p q=0):p=0:=by
 have a:p 0*1+p 1*0+(p 0+p 1)*(1+0)=0:=h (fun i=>if i=0 then 1 else 0);have b:p 0*0+p 1*1+(p 0+p 1)*(0+1)=0:=h (fun i=>if i=1 then 1 else 0);funext i;fin_cases i
 ·change p 0=0;linear_combination(2*a-b)/3
 ·change p 1=0;linear_combination(2*b-a)/3
def dG:LinearMap.BilinForm ℂ dF where
 toFun x:=
  {toFun:=fun y=>aF x.1 y.2+aF x.2 y.1
   map_add':=by intro y z;simp only[aF,Prod.fst_add,Prod.snd_add,Pi.add_apply];ring
   map_smul':=by
    intro c y;change aF x.1 (c•y.2)+aF x.2 (c•y.1)=c*(aF x.1 y.2+aF x.2 y.1)
    simp only[aF,Pi.smul_apply,smul_eq_mul];ring}
 map_add':=by intro x y;apply LinearMap.ext;intro z;simp only[LinearMap.coe_mk,AddHom.coe_mk,LinearMap.add_apply,aF,Prod.fst_add,Prod.snd_add,Pi.add_apply];ring
 map_smul':=by
  intro c x;apply LinearMap.ext;intro z;change aF (c•x.1) z.2+aF (c•x.2) z.1=c*(aF x.1 z.2+aF x.2 z.1)
  simp only[aF,Pi.smul_apply,smul_eq_mul];ring
lemma eC (x y:dF):dG x y=aF x.1 y.2+aF x.2 y.1:=rfl
lemma mB (x y:dF):
  dG x y=dG y x:=by
 rw[eC,eC,bT x.1,bT x.2,add_comm]
lemma kP:dG.Nondegenerate:=by
 have a:∀x:dF,(∀y:dF,dG x y=0)→x=0:=by
  intro x b;apply Prod.ext
  ·apply eO;intro q;simpa[eC,cU] using b (0,q)
  ·apply eO;intro q;simpa[eC,cU] using b (q,0)
 exact⟨a,fun x b=>a x fun y=>(mB x y).trans (b y)⟩
lemma pY (W:Submodule ℂ dF)
  (c:∀x∈W,dG x x=0):Module.finrank ℂ W≤2:=by
 have d:W≤dG.orthogonal W:=by intro x e y f;have h:=c (y+x) (W.add_mem f e);simp only[map_add,LinearMap.add_apply,c x e,c y f,zero_add,add_zero] at h;change dG y x=0;linear_combination(h+mB y x)/2
 have b:Module.finrank ℂ dF=4:=by simp[dF,Ai.E,Module.finrank_prod]
 have a:=Submodule.finrank_mono d;rw[LinearMap.BilinForm.finrank_orthogonal kP,b] at a;omega
def tP (K:Submodule ℂ (Fin 3→Ai.E))
  (i j k:Fin 3):K→ₗ[ℂ] dF where
 toFun y:=(y.1 i,y.1 j-y.1 k)
 map_add':=by
  intro x y;apply Prod.ext
  ·rfl
  ·change x.1 j+y.1 j-(x.1 k+y.1 k)=(x.1 j-x.1 k)+(y.1 j-y.1 k)
   abel
 map_smul':=by
  intro c y;apply Prod.ext
  ·rfl
  ·change c•y.1 j-c•y.1 k=c•(y.1 j-y.1 k);rw[smul_sub]
lemma dJ (K:Submodule ℂ (Fin 3→Ai.E))
  (z:3≤Module.finrank ℂ K) (i j k:Fin 3) (m:j≠i) (n:k≠i)
  (b:∀r,r=i∨r=j∨r=k)
  (c:∀y∈K,aF (y i) (y j)=aF (y i) (y k)):
  ∃v:Ai.E,v≠0∧(fun r=>if r=i then 0 else v)∈K:=by
 let f:=tP K i j k
 have w:∀x∈LinearMap.range f,dG x x=0:=by
  rintro x ⟨y,rfl⟩;change aF (y.1 i) (y.1 j-y.1 k)+aF (y.1 j-y.1 k) (y.1 i)=0;rw[bT (y.1 j-y.1 k) (y.1 i)];have d:=c y.1 y.2;unfold aF at d ⊢
  simp only[Pi.sub_apply];linear_combination 2*d
 have p:=pY (LinearMap.range f) w;have e:LinearMap.ker f≠ ⊥ :=by intro h;have s:=LinearMap.finrank_range_of_inj (LinearMap.ker_eq_bot.mp h);omega
 have l:∃y:K,f y=0∧y≠0:=by by_contra! h;exact e (LinearMap.ker_eq_bot'.mpr h)
 obtain⟨y,q,g⟩:=l;have t:y.1 i=0:=congrArg Prod.fst q;have o:y.1 j=y.1 k:=sub_eq_zero.mp (congrArg Prod.snd q);have a:(fun r=>if r=i then 0 else y.1 j)=y.1:=by
  funext r;rcases b r with rfl|rfl|rfl
  ·simp[t]
  ·simp[m]
  ·simpa[n] using o
 refine⟨y.1 j,?_,?_⟩
 ·intro u;apply g;apply Subtype.ext;rw[←a,u];funext r;simp
 ·rw[a];exact y.2
lemma mS (K:Submodule ℂ (Fin 3→Fin 2→ℂ))
  (g:3≤Module.finrank ℂ K)
  (a:∀y∈K,aF (y 0) (y 1)=aF (y 1) (y 2)∧
    aF (y 1) (y 2)=aF (y 2) (y 0)) (m:Fin 3):
  ∃v:Fin 2→ℂ,v 0+v 1≠0∧(fun r:Fin 3=>if r=m then 0 else v)∈K:=by
 have j:∃v:Fin 2→ℂ,v≠0∧(fun r:Fin 3=>if r=m then 0 else v)∈K:=by
  fin_cases m
  ·refine dJ K g 0 1 2 (by decide) (by decide) (by decide) ?_;intro y c;rw[bT (y 0) (y 2)];exact(a y c).1.trans (a y c).2
  ·refine dJ K g 1 2 0 (by decide) (by decide) (by decide) ?_;intro y c;rw[bT (y 1) (y 0)];exact(a y c).1.symm
  ·refine dJ K g 2 0 1 (by decide) (by decide) (by decide) ?_;intro y c;rw[bT (y 2) (y 1)];exact(a y c).2.symm
 obtain⟨v,n,d⟩:=j;refine⟨v,?_,d⟩;have b:aF v v=0:=by
  have f:=a _ d;fin_cases m<;>norm_num[cU,kB] at f
  ·exact f.1.symm
  ·exact f.symm
  ·exact f
 intro l;have e:v 1= -v 0:=by linear_combination l
 have k:v 0^2=0:=by unfold aF at b;rw[e] at b;linear_combination b/2
 have h:=sq_eq_zero_iff.mp k;apply n;funext i;fin_cases i
 ·exact h
 ·change v 1=0;simp[e,h]
end Ac.Af
namespace Ac.Af
open Aa Finset
lemma oV {L:Submodule ℂ aC} (hL:aD L) (P:aX L=8)
  {i:Fin 4} (X:u L i=2) {A:Finset (Fin 5)} (C:A.card=3)
  (v:U L i=bJ A):∃h:Fin 3→ℂ,h≠0∧(∑r,h r)=0∧
  ∀x∈W L i,∀j∈A,∀k∈A,∃t:ℂ,(fun r:Fin 3=>x (r,j)-x (r,k))=t•h:=by
 classical
 obtain⟨σ,hσ⟩:=aFf C
 let K:=(wM L i A).map (jY σ)
 let D:=aN
 have d (l:Fin 3):σ (tcI l)∈A:=by apply(hσ _).mpr;fin_cases l<;>tauto
 have g (j:Fin 5) (c:j∈A):∃l:Fin 3,σ (tcI l)=j:=by
  rcases (hσ _).mp c with rfl|rfl|rfl
  ·exact⟨0,rfl⟩
  ·exact⟨1,rfl⟩
  ·exact⟨2,rfl⟩
 by_cases H:∃y∈K,¬(D y 1 2=D y 0 2∧D y 0 2=D y 0 1)
 ·obtain⟨y,n,G⟩:=H;obtain⟨h,O,V,q⟩:=aGc _ _ _ G;refine⟨h,O,V,?_⟩;intro x J j c k F;apply q
  ·exact aFg hL v c F J
  obtain⟨Y,E,rfl⟩:=n;obtain⟨Z,rfl⟩:=g j c;obtain⟨k',rfl⟩:=g k F;exact pX hL v hσ J E.1 (jY σ Y)
   (fun r l=>jZ hσ E r _ (d l)) (fun _=>rfl) (fun _=>rfl)
 ·exfalso;have o (y) (n:y∈K):D y 1 2=D y 0 2∧D y 0 2=D y 0 1:=by
   by_contra R;exact H ⟨y,n,R⟩
  have M (y:Fin 3→Fin 2→ℂ) (s t:Fin 3):
    D y s t=aF (y s) (y t):=by
   dsimp[D,aN,aF];ring
  have N (y:Fin 3→Fin 2→ℂ) (s t:Fin 3):
    aF (y s) (y t)=aF (y t) (y s):=by
   unfold aF;ring
  apply oU hL σ;intro m;obtain⟨p,S,z,w,B⟩:=mS K (aGb hL P X C v hσ) (by intro y n;obtain⟨e,f⟩:=o y n;simp only[M] at e f;exact⟨(e.trans f).symm,e.trans (N y 0 2)⟩) m
  let a:=p 0+p 1
  have Q:a≠0:=S;refine⟨a⁻¹ •z,(W L i).smul_mem _ w.1,?_,?_⟩
  ·intro j;have e (b:Fin 2):jY σ z m b=0:=by rw[B];simp
   suffices h:z (m,j)=0 by simp[h]
   by_cases c:j∈A
   ·rw[jZ hσ w m j c,e,e];simp
   ·obtain⟨j,rfl⟩:=σ.surjective j;fin_cases j
    ·exact(c (d 0)).elim
    ·exact(c (d 1)).elim
    ·exact(c (d 2)).elim
    ·exact e 0
    ·exact e 1
  ·intro r T j c;have e (b:Fin 2):jY σ z r b=p b:=by rw[B];simp[T]
   change a⁻¹ *z (r,j)= -1;rw[jZ hσ w r j ((hσ _).mpr c),e,e];change a⁻¹ * -a= -1;simp[Q]
end Ac.Af
namespace Ac.Af
open Aa Finset
lemma aFh (gF:eI) {L:Submodule ℂ aC} (e:aD L)
  (h:7≤aX L) (d:vI L):False:=by
 obtain⟨v,l⟩:=exists_linearIndependent_of_le_finrank (R:=ℂ) (M:=L) h;have j:LinearIndependent ℂ (fun i=>(L.subtype (v i):aC)):=l.map' L.subtype (Submodule.ker_subtype L)
 let S:=Submodule.span ℂ (Set.range fun i=>(L.subtype (v i):aC))
 have le:S≤L:=Submodule.span_le.mpr (by rintro _ ⟨s,rfl⟩;exact(v s).property);have k:aX S=7:=by dsimp only[S,aX];rw[finrank_span_eq_card j];simp
 obtain⟨a,b,f,g⟩:=d;exact gF S (fun x c=>e x (le c)) k ⟨a,b,f,fun x c=>g x (le c)⟩
lemma wN (gF:eI) {L:Submodule ℂ aC} (h:aD L)
  (l:aX L=8) {i:Fin 4} {j k:Fin 5} (g:j≠k)
  (m:∀x∈W L i,∀r:Fin 3,x (r,j)=x (r,k)):False:=by
 let f:=LinearMap.proj (R:=ℂ) (φ:=fun _:Fin 4×Fin 5=>ℂ) (i,j)-LinearMap.proj (i,k)
 let M:=L⊓LinearMap.ker f
 have d:Module.finrank ℂ (L.map f)+aX M=aX L:=by
  dsimp only[M,aX];rw[←(Submodule.submoduleOfEquivInf _ _).finrank_eq,
   ←(f.submoduleMap L).finrank_range_add_finrank_ker,
   LinearMap.range_submoduleMap,LinearMap.ker_submoduleMap]
  simp
 rw[l] at d;have b:Module.finrank ℂ (L.map f)≤1:=(L.map f).finrank_le.trans_eq (Module.finrank_self ℂ);apply aFh gF (L:=M) (fun x c=>h x c.1) (by omega);refine⟨j,k,g,fun x c r=> ?_⟩;by_cases e:r=i
 ·subst r;exact sub_eq_zero.mp c.2
 ·obtain⟨s,rfl⟩:=(by decide:∀a b:Fin 4,b≠a→∃s,iX a s=b) i r e;exact m _ (le_sup_right (b:=L.map (bH i)) ⟨x,c.1,rfl⟩) s
lemma zP (A:Finset (Fin 5)) (d:A.card=3):
  ∃σ:Equiv.Perm (Fin 5),σ 0∈A∧σ 1∈A∧σ 2∈A:=by
 obtain⟨a,b,c,g,h,i,rfl⟩:=card_eq_three.mp d;have E:∀a b c:Fin 5,a≠b→a≠c→b≠c→∃d e:Fin 5,Function.Injective ![a,b,c,d,e]:=by decide
 obtain⟨d,e,f⟩:=E a b c g h i
 let σ:=Equiv.ofBijective ![a,b,c,d,e] ((Finite.injective_iff_bijective).mp f)
 exact⟨σ,by simp[σ],by simp[σ],by simp[σ]⟩
lemma sF {L:Submodule ℂ aC} {i:Fin 4} {A:Finset (Fin 5)}
  (d:aD L) (r:U L i=bJ A) {a b:Fin 5} (o:a∈A) (p:b∈A)
  {x:bI} (n:x∈W L i):q x a=q x b∧G x a=G x b:=by
 let w:aH:=Pi.single a 1-Pi.single b 1
 have m:w∈U L i:=by
  rw[r];refine⟨by simp[w,sum_sub_distrib,Pi.single_apply],fun k g=> ?_⟩;have h:k≠a:=fun e=>g (e▸o)
  have l:k≠b:=fun e=>g (e▸p)
  simp[w,h,l]
 have c (f:aH) (z:∑j,w j*f j=0):f a=f b:=by simpa[w,Pi.single_apply,sub_mul,ite_mul,sum_sub_distrib,sub_eq_zero] using z
 exact⟨c _ (hO d m n),c _ (dU d m n)⟩
def aCc (h:Fin 3→ℂ) (x:Fin 3→ℂ):ℂ:=h 0*(x 1+x 2)+h 1*(x 0+x 2)+h 2*(x 0+x 1)
lemma tQ {P:Submodule ℂ bI} {a b:Fin 5} {h:Fin 3→ℂ}
  (i:∀x∈P,∃t:ℂ,(fun r=>x (r,a)-x (r,b))=t•h)
  (lQ:∃y∈P,∃r,y (r,a)≠y (r,b))
  (f:∀x∈P,q x a=q x b):
  ∀x∈P,aCc h (fun r=>aA x r a+aA x r b)=0:=by
 let l (x:bI):=aCc h (fun r=>aA x r a+aA x r b)
 have E (x:bI) (c:x∈P) (dif:∃r,x (r,a)≠x (r,b)):l x=0:=by
  obtain⟨t,j⟩:=i x c;obtain⟨r,g⟩:=dif;have m:t≠0:=by rintro rfl;exact g (sub_eq_zero.mp (by simpa using congrFun j r))
  have e (r):aA x r a=aA x r b+t*h r:=by have E:x (r,a)-x (r,b)=t*h r:=congrFun j r;unfold aA;linear_combination E
  apply(mul_eq_zero.mp (show t*l x=0 by have H:=f x c;simp only[q,e] at H;simp only[l,aCc,e];linear_combination H)).resolve_left m
 intro x c;change l x=0;by_cases d:∃r,x (r,a)≠x (r,b)
 ·exact E x c d
 push Not at d
 obtain⟨y,k,r,g⟩:=lQ;have e1:=E y k ⟨r,g⟩;have e2:=E (x+y) (P.add_mem c k) ⟨r,by simpa[d] using g⟩;simp only[l,aCc,aA,Pi.add_apply,sum_add_distrib] at*
 linear_combination e2-e1
lemma tR {P:Submodule ℂ bI} {h:Fin 3→ℂ} {a b c:Fin 5}
  (n:h≠0) (d:∑r,h r=0)
  (i:∀x∈P,∃t:ℂ,(fun r=>x (r,b)-x (r,c))=t•h)
  (lQ:∃y∈P,∃r,y (r,b)≠y (r,c))
  (j:∀x∈P,aCc h (fun r=>aA x r a+aA x r b)=0)
  (l:∀x∈P,aCc h (fun r=>aA x r a+aA x r c)=0):
  ∀r,h r≠0:=by
 obtain⟨y,g,r,o⟩:=lQ;obtain⟨t,m⟩:=i y g;have p:t≠0:=by rintro rfl;exact o (sub_eq_zero.mp (by simpa using congrFun m r))
 have e (r):aA y r b=aA y r c+t*h r:=by have E:y (r,b)-y (r,c)=t*h r:=congrFun m r;unfold aA;linear_combination E
 have H:=j y g;have K:=l y g;simp only[aCc,e] at H K;have f:=(mul_eq_zero.mp (show t*(h 0*h 1+h 0*h 2+h 1*h 2)=0 by linear_combination(H-K)/2)).resolve_left p;rw[Fin.sum_univ_three] at d;intro r z;apply n;rcases (by decide:∀r:Fin 3,r=0∨r=1∨r=2) r with rfl|rfl|rfl<;>rw[z] at d f<;>
  simp only[zero_add,zero_mul,mul_zero,add_zero] at d f<;>
  rcases mul_eq_zero.mp f with k|k<;>rw[k] at d<;>simp only[zero_add,add_zero] at d<;>
  funext s<;>fin_cases s<;>assumption
end Ac.Af
namespace Ac.Af
open Aa Finset Av
def vE:bI→ₗ[ℂ] cI 3 where
 toFun x p:= ![x (p.2,2)+x (p.2,3)+2*x (p.2,4),x (p.2,2)-x (p.2,3),x (p.2,4)] p.1
 map_add' x y:=by funext ⟨j,r⟩;fin_cases j<;>simp<;>ring
 map_smul' c x:=by funext ⟨j,r⟩;fin_cases j<;>simp<;>ring
def sG (x:bI):ℂ:=∑j,(![1,-1,-4]:Fin 3→ℂ) j*qH (vE x) j
lemma aDs (x y:bI):
  sG (x+y)+sG (x-y)=2*sG x+2*sG y:=by
 simp only[sG,Fin.sum_univ_three,qH,map_add,map_sub,Pi.add_apply,Pi.sub_apply];ring
lemma aA5 (x:bI) (t:ℂ) (a:∀r,x (r,0)=x (r,1)+t):
  4*(G x 1-G x 0)=t*sG x:=by
 simp[G,cJ,Fin.sum_univ_five,sG,Fin.sum_univ_three,qH,vE,a];ring
lemma aCd (P:Submodule ℂ bI)
  (c:∀x∈P,∀j:Fin 5,j=0∨j=1→∀r,
    x (r,j)-x (r,2)=x (0,j)-x (0,2))
  (lQ:∃y∈P,y (0,0)≠y (0,1))
  (l:∀x∈P,G x 0=G x 1):Module.finrank ℂ P≤6:=by
 have e (x:bI) (a:x∈P) (f:x (0,0)≠x (0,1)):sG x=0:=by have H:=aA5 x (x (0,0)-x (0,1)) (fun r=>by linear_combination c x a 0 (Or.inl rfl) r-c x a 1 (Or.inr rfl) r);rw[l x a,sub_self,mul_zero] at H;exact(mul_eq_zero.mp H.symm).resolve_left (sub_ne_zero.mpr f)
 have n (x:bI) (a:x∈P):sG x=0:=by
  by_cases h:x (0,0)=x (0,1)
  ·obtain⟨y,i,f⟩:=lQ;have s:=e (x+y) (P.add_mem a i) (by simpa[h] using f);have q:=e (x-y) (P.sub_mem a i) (by simpa[h] using f);have E:=aDs x y;linear_combination(s+q-E)/2-e y i f
  ·exact e x a h
 let F:=vE.domRestrict P
 have b:=eS ![1,-1,-4] (by intro j;fin_cases j<;>norm_num)
  (LinearMap.range F) (by rintro _ ⟨x,rfl⟩;exact n x x.2)
 let lV (p:Fin 3×Fin 5):=(LinearMap.proj (R:=ℂ) (φ:=fun _:Fin 3×Fin 5=>ℂ) p).domRestrict P
 let g:=F.rangeRestrict.prod ((lV (0,0)).prod (lV (0,1)))
 have m:Function.Injective g:=by
  apply LinearMap.ker_eq_bot.mp;apply LinearMap.ker_eq_bot'.mpr;intro x a;have k:vE x=0:=congrArg Subtype.val (congrArg Prod.fst a);have o:(x:bI) (0,0)=0:=congrArg Prod.fst (congrArg Prod.snd a);have e1:(x:bI) (0,1)=0:=congrArg Prod.snd (congrArg Prod.snd a);have tail (r:Fin 3):(x:bI) (r,2)=0∧(x:bI) (r,3)=0∧(x:bI) (r,4)=0:=by have u:(x:bI) (r,2)+(x:bI) (r,3)+2*(x:bI) (r,4)=0:=congrFun k (0,r);have v:(x:bI) (r,2)-(x:bI) (r,3)=0:=congrFun k (1,r);have w:(x:bI) (r,4)=0:=congrFun k (2,r);exact⟨by linear_combination(u+v)/2-w,by linear_combination(u-v)/2-w,w⟩
  apply Subtype.ext;funext ⟨r,j⟩;fin_cases j
  ·simpa[o,(tail 0).1,(tail r).1] using c x x.2 0 (Or.inl rfl) r
  ·simpa[e1,(tail 0).1,(tail r).1] using c x x.2 1 (Or.inr rfl) r
  ·exact(tail r).1
  ·exact(tail r).2.1
  ·exact(tail r).2.2
 have d:=LinearMap.finrank_le_finrank_of_injective m;simp only[Module.finrank_prod,Module.finrank_self] at d;change Module.finrank ℂ P≤Module.finrank ℂ (LinearMap.range F)+(1+1) at d;change 2*Module.finrank ℂ (LinearMap.range F)≤9 at b;omega
def rE (σ:Equiv.Perm (Fin 5)) (h:Fin 3→ℂ):bI→ₗ[ℂ] bI where
 toFun x p:=x (p.1,σ p.2)/h p.1
 map_add' x y:=by funext p;simp[add_div]
 map_smul' c x:=by funext p;simp[mul_div_assoc]
lemma yN (σ:Equiv.Perm (Fin 5)) (h:Fin 3→ℂ) (a:∀r,h r≠0)
  (x:bI) (j:Fin 5):
  G x (σ j)=h 0*h 1*h 2*G (rE σ h x) j:=by
 let y:=rE σ h x
 have e (r k):x (r,σ k)=h r*y (r,k):=by change _=h r*(_/h r);field_simp[a r]
 have S (f:Fin 5→ℂ):∑k,f k=f (σ 0)+f (σ 1)+f (σ 2)+f (σ 3)+f (σ 4):=by rw[←Equiv.sum_comp σ f,Fin.sum_univ_five]
 change G x (σ j)=_ *G y j
 conv_lhs=>simp only[G,cJ,S,e]
 simp only[G,cJ,Fin.sum_univ_five];ring
end Ac.Af
namespace Ac.Af
open Aa Finset
lemma rF (gF:eI) {L:Submodule ℂ aC}
  (l:aD L) (v:aX L=8) {i:Fin 4} (Q:u L i=2)
  {A:Finset (Fin 5)} (G:A.card=3) (w:U L i=bJ A)
  {h:Fin 3→ℂ} (N:h≠0) (K:∑r,h r=0)
  (g:∀x∈W L i,∀j∈A,∀k∈A,∃t:ℂ,
    (fun r:Fin 3=>x (r,j)-x (r,k))=t•h):False:=by
 obtain⟨σ,m,n,o⟩:=zP A G;have lQ (a b:Fin 5) (E:a≠b):∃x∈W L i,∃r,x (r,σ a)≠x (r,σ b):=by by_contra! s;exact wN gF l v (σ.injective.ne E) s
 have polar (j:Fin 5) (p:σ j∈A) (R:0≠j):=tQ
  (fun x d=>g x d _ m _ p) (lQ 0 j R) (fun x d=>(sF l w m p d).1)
 have c:=tR N K (fun x d=>g x d _ n _ o) (lQ 1 2 (by decide)) (polar 1 n (by decide)) (polar 2 o (by decide))
 let F:=rE σ h
 have B:Function.Injective F:=by intro x y J;funext ⟨r,j⟩;obtain⟨k,rfl⟩:=σ.surjective j;exact(div_left_inj₀ (c r)).mp (congrFun J (r,k))
 let P:=(W L i).map F
 have gT {x:bI} (d:x∈W L i) {j k:Fin 5} (p:σ j∈A) (M:σ k∈A):
   ∃t:ℂ,∀r,F x (r,j)-F x (r,k)=t:=by
  obtain⟨t,f⟩:=g x d _ p _ M;refine⟨t,fun r=> ?_⟩;change x (r,σ j)/h r-x (r,σ k)/h r=t;rw[←sub_div,div_eq_iff (c r)];exact congrFun f r
 have C:=aCd P (by
  rintro _ ⟨x,d,rfl⟩ j (rfl|rfl) r
  ·obtain⟨t,f⟩:=gT d m o;rw[f,f]
  ·obtain⟨t,f⟩:=gT d n o;rw[f,f]) (by
  obtain⟨x,d,r,O⟩:=lQ 0 1 (by decide);obtain⟨t,f⟩:=gT d m n;refine⟨F x,⟨x,d,rfl⟩,fun e=>O ?_⟩;have z:t=0:=(f 0).symm.trans (sub_eq_zero.mpr e);exact(div_left_inj₀ (c r)).mp (sub_eq_zero.mp ((f r).trans z))) (by
  rintro _ ⟨x,d,rfl⟩;have H:=(sF l w m n d).2;rw[yN σ h c x 0,yN σ h c x 1] at H;exact mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (c 0) (c 1)) (c 2)) H)
 have q:Module.finrank ℂ (W L i)=Module.finrank ℂ P:=(Submodule.equivMapOfInjective F B _).finrank_eq;have rank:=jP l i;rw[Q,v,q] at rank;omega
end Ac.Af
namespace Ac.Af
lemma rG:kV:=by intro L a d i f A c e;obtain⟨h,j,g,b⟩:=oV a d f c e;exact rF Ac.vV a d f c e j g b
end Ac.Af
namespace Ac.Ah.Au
open Aa Finset
lemma sH {L:Submodule ℂ aC} (hL:aD L)
  (F:Module.finrank ℂ (W L)=7)
  (b:bF 0 (Pi.single 0 1-Pi.single 1 1)∈L)
  (G:Module.finrank ℂ ((W L).map dl)≤1):
  ∃r:Fin 3,∀x∈W L,dl x r=0:=by
 by_cases t:(W L).map dl= ⊥
 ·exact⟨0,fun x j=>congrFun (show dl x=0 by have h:dl x∈(W L).map dl:=⟨x,j,rfl⟩;rw[t] at h;simpa using h) 0⟩
 obtain⟨_,⟨z,l,rfl⟩,n⟩:=Submodule.exists_mem_ne_zero_of_ne_bot t;have le:ℂ ∙ dl z≤(W L).map dl:=(Submodule.span_singleton_le_iff_mem _ _).mpr ⟨z,l,rfl⟩;have v:=Submodule.eq_of_le_of_finrank_le le (by rwa [finrank_span_singleton n]);have e (x:bI) (j:x∈W L):∃c:ℂ,dl x=c•dl z:=by
  have B:dl x∈(W L).map dl:=⟨x,j,rfl⟩
  obtain⟨c,d⟩:=Submodule.mem_span_singleton.mp (v▸B);exact⟨c,d.symm⟩
 by_contra! C;have o (r:Fin 3):dl z r≠0:=fun h=>by obtain⟨x,j,u⟩:=C r;obtain⟨c,d⟩:=e x j;exact u (by rw[d,Pi.smul_apply,h,smul_zero])
 have E:∀y∈(W L).map yp,q (dl z) y=0:=by
  rintro _ ⟨X,f,rfl⟩;obtain⟨c,d⟩:=e X f;by_cases s:c=0
  ·have m:dl X=0:=by rw[d,s,zero_smul]
   have p:=uI hL b _ ((W L).add_mem l f);have em:=uI hL b _ ((W L).sub_mem l f);have A:=uI hL b _ l;rw[map_add,map_add,m,add_zero] at p;rw[map_sub,map_sub,m,sub_zero] at em;linear_combination(p+em-2*A-aHl (dl z) (yp z) (yp X))/2
  ·have g:=uI hL b X f;rw[d,show q (c•dl z) (yp X)=c*q (dl z) (yp X) by simp only[q,Pi.smul_apply,smul_eq_mul];ring] at g;exact(mul_eq_zero.mp g).resolve_left s
 have w:=aGa (Th (dl z)) _ (aFd (dl z) _ E);rw[aGm _ (o 0) (o 1) (o 2),inf_bot_eq,finrank_bot] at w;simp only[Fintype.card_prod,Fintype.card_fin] at w;have i:=Submodule.finrank_mono (show(W L⊓LinearMap.ker yp).map dl≤ℂ ∙ dl z by rintro _ ⟨X,f,rfl⟩;obtain⟨c,d⟩:=e X f.1;exact Submodule.mem_span_singleton.mpr ⟨c,d.symm⟩);rw[finrank_span_singleton n] at i;have k:=lH dl (W L⊓LinearMap.ker yp);rw[inf_assoc,inf_comm (LinearMap.ker yp) (LinearMap.ker dl),←inf_assoc] at k;have r:=lH yp (W L);have a:=aCa hL;omega
end Ac.Ah.Au
namespace Ac.Af
open Aa Finset
abbrev fZ:=Fin 3→ℂ
def eF (j:Fin 5):bI→ₗ[ℂ] fZ where
 toFun v r:=aA v r j
 map_add' _ _:=by ext;simp[aA,sum_add_distrib];ring
 map_smul' _ _:=by ext;simp[aA,←mul_sum];ring
abbrev aI (L:Submodule ℂ aC) (j:Fin 5):=(eF j).domRestrict (W L 0)
def bY (a b:Fin 5):aH:=Pi.single a 1-Pi.single b 1
lemma uJ (a b:Fin 5) (f:aH):
  ∑j,bY a b j*f j=f a-f b:=by
 simp[bY,sub_mul,sum_sub_distrib,Pi.single_apply,ite_mul]
abbrev oW (L:Submodule ℂ aC):=aD L∧aX L=8∧u L 0=2∧bY 0 1∈U L 0∧bY 2 3∈U L 0
def bP:Equiv.Perm (Fin 5):=Equiv.swap 0 2*Equiv.swap 1 3
def fA:Equiv.Perm (Fin 4):=Equiv.swap 1 2
def gA:Equiv.Perm (Fin 5):=Equiv.swap 0 1*Equiv.swap 2 3
abbrev oX (L:Submodule ℂ aC):=L.map (Ad.re 1 bP)
lemma aA6 {L:Submodule ℂ aC} (k:aD L) (n:aX L=8)
  (ρ:Equiv.Perm (Fin 4)) (σ:Equiv.Perm (Fin 5)) (m:u L (ρ 0)=2)
  (d:bY (σ 0) (σ 1)∈U L (ρ 0)) (f:bY (σ 2) (σ 3)∈U L (ρ 0)):
  oW (L.map (Ad.re ρ σ)):=by
 let K:=L.map (Ad.re ρ σ)
 have c:aZ K 0=(aZ L (ρ 0)).map (Ad.re ρ σ):=by
  ext z;simp only[Ah.jX,Submodule.mem_map];constructor
  ·rintro⟨⟨x,g,rfl⟩,q⟩;refine⟨x,⟨g,fun r c=>funext fun j=> ?_⟩,rfl⟩;simpa[Ad.re,row] using congrFun (q (ρ.symm r) fun e=>c (by simpa using congrArg ρ e)) (σ.symm j)
  ·rintro⟨x,⟨g,i⟩,rfl⟩;exact⟨⟨x,g,rfl⟩,fun r c=>funext fun j=>congrFun (i (ρ r) fun e=>c (ρ.injective e)) (σ j)⟩
 have o:u K 0=2:=by change Module.finrank ℂ (aZ K 0)=2;rw[c,←(Submodule.equivMapOfInjective _ (fun _ _ h=>funext fun p=>by simpa[Ad.re] using congrFun h (ρ.symm p.1,σ.symm p.2)) _).finrank_eq];exact m
 have l (a b:Fin 5) (hw:bY (σ a) (σ b)∈U L (ρ 0)):bY a b∈U K 0:=uE.mpr ⟨_,uE.mp hw,funext fun⟨r,j⟩=>by simp[Ad.re,Av.eJ,bY,Pi.single_apply,ρ.injective.eq_iff,σ.injective.eq_iff]⟩;exact⟨Ad.gI ρ σ k,(Ad.nL ρ σ L).trans n,o,l 0 1 d,l 2 3 f⟩
lemma aGz {L:Submodule ℂ aC} (ρ:Equiv.Perm (Fin 4)) (τ:Equiv.Perm (Fin 3))
  (hρ:∀r:Fin 3,ρ r.succ=(τ r).succ) (σ:Equiv.Perm (Fin 5))
  {v:bI} (b:v∈W L 0):
  (fun p:Fin 3×Fin 5=>v (τ p.1,σ p.2))∈W (L.map (Ad.re ρ σ)) 0:=by
 obtain⟨s,t,a,rfl⟩:=aAu.mp b;exact aAu.mpr ⟨s,Ad.re ρ σ t,⟨t,a,rfl⟩,funext fun⟨r,j⟩=>by simp[bH,iX,Ad.re,hρ]⟩
lemma mT (τ:Equiv.Perm (Fin 3)) (σ:Equiv.Perm (Fin 5)) (v:bI) (r:Fin 3) (j:Fin 5):
  aA (fun p:Fin 3×Fin 5=>v (τ p.1,σ p.2)) r j=aA v (τ r) (σ j):=by
 simp only[aA,Equiv.sum_comp σ (fun k=>v (τ r,k))]
lemma xV (L:Submodule ℂ aC):oX (oX L)=L:=by unfold oX;rw[←Submodule.map_comp,show(Ad.re 1 bP).comp (Ad.re 1 bP)=LinearMap.id by ext m ⟨i,j⟩;simp[Ad.re,bP];fin_cases j<;>rfl,Submodule.map_id]
lemma zQ {L:Submodule ℂ aC} (h:oW L):oW (oX L):=aA6 h.1 h.2.1 1 bP h.2.2.1 h.2.2.2.2 h.2.2.2.1
def zR {L:Submodule ℂ aC} (x:W L 0):W (oX L) 0:=⟨_,aGz 1 1 (fun _=>rfl) bP x.2⟩
lemma gB {L:Submodule ℂ aC} (x:W L 0) (j:Fin 5):
  aI (oX L) j (zR x)=aI L (bP j) x:=
 funext fun r=>mT 1 bP x.val r j
def wO {L:Submodule ℂ aC} (y:W (oX L) 0):W L 0:=
 ⟨fun p=>y.1 (p.1,bP p.2),by
   have a:(fun p=>y.1 (p.1,bP p.2))∈W (oX (oX L)) 0:=aGz 1 1 (fun _=>rfl) bP y.2;rwa [xV L] at a⟩
lemma gD {L:Submodule ℂ aC} (y:W (oX L) 0) (j:Fin 5):
  aI L j (wO y)=aI (oX L) (bP j) y:=
 funext fun r=>mT 1 bP y.val r j
lemma bG {L:Submodule ℂ aC} (c:aD L) {a b:Fin 5}
  (d:bY a b∈U L 0) (x:W L 0):
  G
   x.val a=G x.val b∧(∑r,(aI L a x-aI L b x) r)=0∧
   (∑r,(aI L a x-aI L b x) r*(aI L a x+aI L b x) r)=0:=by
 have g:=dU c d x.2;have t:=eR c d x.2;have h:=hO c d x.2;rw[uJ] at g t h;refine⟨sub_eq_zero.mp g,?_,?_⟩
 ·simp only[Fin.sum_univ_three,Pi.sub_apply,aI,eF,LinearMap.domRestrict_apply,
   LinearMap.coe_mk,AddHom.coe_mk]
  unfold aV at t;linear_combination t
 ·simp only[Fin.sum_univ_three,Pi.sub_apply,Pi.add_apply,aI,eF,
   LinearMap.domRestrict_apply,LinearMap.coe_mk,AddHom.coe_mk]
  unfold aV at t;unfold q at h;linear_combination(aA x.val 0 a+aA x.val 1 a+aA x.val 2 a+aA x.val 0 b+aA x.val 1 b+aA x.val 2 b)*t-h
lemma wP {L:Submodule ℂ aC} (h:oW L):
  (∀x y:W L 0,∃t:W L 0,
    aI L 0 t=aI L 0 x∧aI L 1 t=aI L 1 x∧
    aI L 2 t=aI L 2 y∧aI L 3 t=aI L 3 y)∧
  ∃z:fZ,z≠0∧jG 4 z∈W L 0:=by
 have f {a b:Fin 5} (p:bY a b∈U L 0) (l:a≠b):
   Module.finrank ℂ (LinearMap.range ((aI L a).prod (aI L b)))≤3:=by
  let S:Finset (Fin 5):={a,b}
  let g:cI S.card→ₗ[ℂ] fZ×fZ:=
   (LinearMap.funLeft ℂ ℂ (fun r=>(S.equivFin ⟨a,by simp[S]⟩,r))).prod
     (LinearMap.funLeft ℂ ℂ (fun r=>(S.equivFin ⟨b,by simp[S]⟩,r)))
  have H:=dO h.1 p S (fun k=>by by_cases E:k=a<;>by_cases G:k=b<;>simp_all[S,bY]);have e:=(Submodule.finrank_mono (show LinearMap.range ((aI L a).prod (aI L b))≤
   ((W L 0).map (aK S)).map g by
     rintro _ ⟨x,rfl⟩;exact⟨_,⟨x,x.2,rfl⟩,by ext r<;>simp[g,aK,aI,eF]⟩)).trans
   (Submodule.finrank_map_le g _)
  have ca:S.card=2:=by simp[S,l]
  omega
 let A:=(aI L 0).prod (aI L 1);let B:=(aI L 2).prod (aI L 3)
 let F:=A.rangeRestrict.prod B.rangeRestrict
 have d (t:W L 0) (c:t∈LinearMap.ker F):jQ 4 t.val=0:=funext fun⟨k,r⟩=>by
  fin_cases k
  ·exact congrArg (fun v=>v.1.val.1 r) c
  ·exact congrArg (fun v=>v.1.val.2 r) c
  ·exact congrArg (fun v=>v.2.val.1 r) c
  ·exact congrArg (fun v=>v.2.val.2 r) c
 have J:Module.finrank ℂ (LinearMap.ker F)≤1:=by rw[←Submodule.finrank_map_subtype_eq (W L 0) (LinearMap.ker F)];exact(Submodule.finrank_mono (by rintro _ ⟨t,c,rfl⟩;exact⟨t.2,d t c⟩)).trans (fJ h.1 0 4)
 have u:Module.finrank ℂ A.range≤3:=f h.2.2.2.1 (by decide);have C:Module.finrank ℂ B.range≤3:=f h.2.2.2.2 (by decide);have n:=F.finrank_range_add_finrank_ker;have le:=Submodule.finrank_le F.range;rw[Module.finrank_prod] at le;have w:=jP h.1 0;have m:Module.finrank ℂ F.range=6:=by omega
 have j:=LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq (by rw[m,Module.finrank_prod];omega));refine⟨fun x y=> ?_,?_⟩
 ·obtain⟨t,c⟩:=j (A.rangeRestrict x,B.rangeRestrict y);exact⟨t,congrArg (fun v=>v.1.val.1) c,congrArg (fun v=>v.1.val.2) c,congrArg (fun v=>v.2.val.1) c,congrArg (fun v=>v.2.val.2) c⟩
 ·obtain⟨t,c,s⟩:=Submodule.exists_mem_ne_zero_of_ne_bot (show LinearMap.ker F≠ ⊥ from fun o=>by
   rw[o,finrank_bot,add_zero] at n;omega)
  have i:t.val=jG 4 (eF 4 t.val):=fI (d t c);exact⟨eF 4 t.val,fun q=>s (Subtype.ext (by rw[i,q,map_zero];rfl)),i▸t.2⟩
def D (x y z:fZ):ℂ:=x 0*(y 1*z 2+y 2*z 1)+x 1*(y 0*z 2+y 2*z 0)+x 2*(y 0*z 1+y 1*z 0)
lemma oY (v:bI):
  let c j:=eF j v
  12*(G v 1-G v 0)=
   4*D (c 0-c 1) (c 0+c 1) (c 0+c 1)-
   D (c 0-c 1) (c 2+c 3-(2:ℂ)•c 4) (c 2+c 3-(2:ℂ)•c 4)-
   3*D (c 0-c 1) (c 2-c 3) (c 2-c 3):=by
 have b:G v 1-G v 0=
   D (fun r=>v (r,0)-v (r,1)) (fun r=>v (r,2)) (fun r=>v (r,3))+
   D (fun r=>v (r,0)-v (r,1)) (fun r=>v (r,2)) (fun r=>v (r,4))+
   D (fun r=>v (r,0)-v (r,1)) (fun r=>v (r,3)) (fun r=>v (r,4)):=by
  simp only[G,Av.cJ,Fin.sum_univ_five,D];ring
 have a (j:Fin 5) (r:Fin 3):
   v
    (r,j)=eF j v r-(eF 0 v r+eF 1 v r+eF 2 v r+
    eF 3 v r+eF 4 v r)/3:=by
  change v (r,j)=aA v r j-(aA v r 0+aA v r 1+aA v r 2+aA v r 3+aA v r 4)/3;rw[cQ v r j,Fin.sum_univ_five]
 dsimp only;rw[b];simp only[D,Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,a];ring
lemma nP (j k:Fin 5) (z:fZ):
  eF k (jG j z)=if k=j then z else 0:=funext fun r=>by
 change aA (jF z (rU j)) r k=_;rw[gS];split<;>rfl
lemma kC (z r:fZ)
  (h:∀x:fZ,(∑i,x i)=0→D x z r=0):
  z
   1*r 2+z 2*r 1=z 0*r 2+z 2*r 0∧
   z 0*r 2+z 2*r 0=z 0*r 1+z 1*r 0:=by
 have a:=h ![1,-1,0] (by norm_num[Fin.sum_univ_three]);have b:=h ![0,1,-1] (by norm_num[Fin.sum_univ_three]);norm_num[D] at a b;exact⟨by linear_combination a,by linear_combination b⟩
lemma zS {z q:fZ} (v:z≠0)
  (u:∀x:fZ,(∑i,x i)=0→D x z z=0)
  (t:∀x:fZ,(∑i,x i)=0→D x z q=0):∃c:ℂ,q=c•z:=by
 obtain⟨m,n⟩:=kC z z u;obtain⟨e,f⟩:=kC z q t;have sq0 {p s:ℂ} (h:p^2*s=0):p*s=0:=(pow_eq_zero_iff (by decide:2≠0)).mp (by linear_combination s*h);have l:z 2*(q 1-q 0)=0:=sq0 (by linear_combination z 2*e-q 2*m/2);have g:z 0*(q 2-q 1)=0:=sq0 (by linear_combination z 0*f-q 0*n/2);have k:z 1*(q 2-q 0)=0:=sq0 (by linear_combination z 1*(e+f)-q 1*(m+n)/2);have a:z 0*q 1=z 1*q 0:=by linear_combination-e-g+k+l
 have d:z 1*q 2=z 2*q 1:=by linear_combination-f+g+k-l
 have b:z 0*q 2=z 2*q 0:=by linear_combination-e-f+g+k+l
 obtain⟨i,o⟩:∃i,z i≠0:=by by_contra! h;exact v (funext h)
 refine⟨q i/z i,funext fun j=>mul_left_cancel₀ o ?_⟩;have r:z i*q j=z j*q i:=by fin_cases i<;>fin_cases j<;>first | rfl | exact a | exact a.symm | exact d | exact d.symm | exact b | exact b.symm
 simp only[Pi.smul_apply,smul_eq_mul];rw[r];field_simp[o]
lemma uK {L:Submodule ℂ aC} (h:oW L) {z:fZ}
  (f:jG 4 z∈W L 0) (x:W L 0):
  D (aI L 0 x-aI L 1 x) z z=0∧
  D (aI L 0 x-aI L 1 x) z (aI L 2 x+aI L 3 x-(2:ℂ)•aI L 4 x)=0:=by
 let c j:=aI L j x
 have H (s:ℂ):D (c 0-c 1) (c 2+c 3-(2:ℂ)•c 4-(2*s)•z)
   (c 2+c 3-(2:ℂ)•c 4-(2*s)•z)=
   4*D (c 0-c 1) (c 0+c 1) (c 0+c 1)-3*D (c 0-c 1) (c 2-c 3) (c 2-c 3):=by
  have a:=oY (x.val+s•jG 4 z);rw[(bG h.1 h.2.2.2.1 ⟨_,(W L 0).add_mem x.2 ((W L 0).smul_mem s f)⟩).1,sub_self,mul_zero] at a;simp only[map_add,map_smul,nP,show(0:Fin 5)≠4 by decide,
   show(1:Fin 5)≠4 by decide,show(2:Fin 5)≠4 by decide,
   show(3:Fin 5)≠4 by decide,ite_false,ite_true,smul_zero,add_zero] at a
  have g:c 2+c 3-(2:ℂ)•(c 4+s•z)=c 2+c 3-(2:ℂ)•c 4-(2*s)•z:=by rw[smul_add,smul_smul,sub_add_eq_sub_sub]
  change 0=4*D (c 0-c 1) (c 0+c 1) (c 0+c 1)-
   D (c 0-c 1) (c 2+c 3-(2:ℂ)•(c 4+s•z)) (c 2+c 3-(2:ℂ)•(c 4+s•z))-
   3*D (c 0-c 1) (c 2-c 3) (c 2-c 3) at a
  rw[g] at a;linear_combination a
 have d:=H 1;have b:=H (-1);have e:=H 0;simp only[D,Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at d b e ⊢
 exact⟨by linear_combination(d+b-2*e)/8,by linear_combination(b-d)/8⟩
abbrev aCe {E:Type*} [AddCommGroup E] [Module ℂ E] (f:E→ₗ[ℂ] fZ):=∀h:fZ,(∑r,h r)=0→∃x,f x=h
lemma aDt {L:Submodule ℂ aC} (h:oW L)
  (f:aCe (aI L 0-aI L 1)):
  ∀y:W L 0,aI L 2 y-aI L 3 y=0:=by
 obtain⟨j,z,hz,E⟩:=wP h
 let a:=aI L 0+aI L 1;let u:=aI L 0-aI L 1
 let b:=aI L 2+aI L 3;let v:=aI L 2-aI L 3
 let r:=b-(2:ℂ)•aI L 4
 have o (x:W L 0):4*D (u x) (a x) (a x)-D (u x) (r x) (r x)-3*D (u x) (v x) (v x)=0:=by have J:=oY x.val;rw[(bG h.1 h.2.2.2.1 x).1,sub_self,mul_zero] at J;exact J.symm
 have m (x:W L 0):D (u x) z z=0:=(uK h E x).1;have g (x:W L 0):D (u x) z (r x)=0:=(uK h E x).2;intro y;obtain⟨t,B,C,S,T⟩:=j 0 y;have K:a t=0:=by simp[a,B,C]
 have A:u t=0:=by simp[u,B,C]
 have M:v t=v y:=by simp[v,S,T]
 obtain⟨c,Z⟩:=zS hz
  (fun k w=>by obtain⟨x,rfl⟩:=f k w;exact m x)
  (fun k w=>by
    obtain⟨x,rfl⟩:=f k w;have e:=g (x+t);rw[map_add,A,add_zero,map_add] at e;rw[show D (u x) z (r x+r t)=D (u x) z (r x)+D (u x) z (r t) by simp only[D,Pi.add_apply];ring,g x,zero_add] at e;exact e)
 let q:=v y
 have V:∀k:fZ,(∑i,k i)=0→D k q q=0:=fun k w=>by
  obtain⟨x,hx⟩:=f k w;obtain⟨s,N,O,P,Q⟩:=j 0 x
  let p:=x-s
  have H:u p=k:=by have G:u s=0:=(by simp[u,N,O]);simp only[p,map_sub,G,sub_zero];exact hx
  have U:v p=0:=by have G:v s=v x:=(by simp[v,P,Q]);simp[p,G]
  have R:D k (r (p+t)) (r (p+t))=D k (r p) (r p):=by
   rw[map_add,Z,show D k (r p+c•z) (r p+c•z)=
    D
     k (r p) (r p)+2*c*D k z (r p)+c^2*D k z z by
     simp only[D,Pi.add_apply,Pi.smul_apply,smul_eq_mul];ring,
    ←H,m p,g p];ring
  have n:=o p;have d:=o (p+t);rw[show u (p+t)=k by rw[map_add,A,add_zero,H],R,
   show a (p+t)=a p by rw[map_add,K,add_zero],
   show v (p+t)=q by rw[map_add,U,M,zero_add]] at d
  rw[H,U,show D k 0 0=0 by simp[D]] at n;linear_combination(n-d)/3
 have l:=(bG h.1 h.2.2.2.2 y).2.1;rw[Fin.sum_univ_three] at l;change q 0+q 1+q 2=0 at l;obtain⟨d,F⟩:=kC q q V;have X:q 0=0:=(pow_eq_zero_iff (by decide:3≠0)).mp (by linear_combination(3*q 0^2-2*q 0*q 1)*l/3+2*q 0*d/3+(q 0-2*q 1)*F/6);have z1:q 1=0:=(pow_eq_zero_iff (by decide:2≠0)).mp (by rw[X] at l d;linear_combination q 1*l-d/2);have z2:q 2=0:=by rw[X,z1] at l;linear_combination l
 funext i;fin_cases i<;>assumption
lemma nZ {L:Submodule ℂ aC} (h:oW L)
  (w:¬aCe (aI L 0-aI L 1)):
  ∃j:Fin 3,∀x:W L 0,(aI L 0 x-aI L 1 x) j=0:=by
 let d:=aI L 0-aI L 1
 have f:Module.finrank ℂ d.range≤1:=by
  let s:Module.Dual ℂ fZ:=(LinearMap.proj 0:Module.Dual ℂ fZ)+LinearMap.proj 1+LinearMap.proj 2
  have l (x:fZ):s x=∑r,x r:=(Fin.sum_univ_three _).symm;have n:d.range≤ s.ker:=fun _ ⟨x,e⟩=>e▸(l _).trans (bG h.1 h.2.2.2.1 x).2.1
  have B:=Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne n
   fun p=>w fun k u=>by change k∈d.range;rw[p];exact(l k).trans u)
  have H:=Module.Dual.finrank_ker_add_one_of_ne_zero (show s≠0 from fun A=>by have H:=l 1;rw[A] at H;norm_num at H);have dt:Module.finrank ℂ fZ=3:=by simp[fZ]
  omega
 let rot:Equiv.Perm (Fin 4):=Equiv.swap 0 1*Equiv.swap 1 2*Equiv.swap 2 3
 let K:=L.map (Ad.re rot 1)
 have a:Ah.W K=W L 0:=by
  have c:Ah.aU.comp (Ad.re rot 1)=bH 0:=LinearMap.ext fun x=>funext fun⟨r,j⟩=>by change x (rot r.castSucc,j)=x (iX 0 r,j);fin_cases r<;>rfl
  unfold Ah.W W;rw[sup_comm,←Submodule.map_comp,c]
 have i:Module.finrank ℂ (Ah.W K)=7:=by have q:=jP h.1 0;rw[h.2.1,h.2.2.1] at q;rw[a];exact(by omega:Module.finrank ℂ (W L 0)=7)
 have b:Ah.bF 0 (Pi.single 0 1-Pi.single 1 1)∈K:=by
  have m:∀r:Fin 4,rot r=0↔r=3:=by decide
  exact⟨_,uE.mp h.2.2.2.1,funext fun⟨r,j⟩=>by fin_cases r<;>simp[Ad.re,m,Av.eJ,Ah.bF,bY]⟩
 have g (x:W L 0):Ah.Au.dl x.val=d x:=funext fun r=>by change x.val (r,0)-x.val (r,1)=aA x.val r 0-aA x.val r 1;unfold aA;ring
 have o:(Ah.W K).map Ah.Au.dl=d.range:=by ext v;simp only[a,Submodule.mem_map,LinearMap.mem_range];exact⟨fun⟨y,z,e⟩=>⟨⟨y,z⟩,(g _).symm.trans e⟩,fun⟨y,e⟩=>⟨y,y.2,(g y).trans e⟩⟩
 obtain⟨j,t⟩:=Ah.Au.sH (Ad.gI rot 1 h.1) i b (o▸f);exact⟨j,fun x=>(congrFun (g x) j).symm.trans (t x.val (by rw[a];exact x.2))⟩
def orb (p:Fin 4×Fin 5):Fin 11:=
 (![![0,0,1,1,2],![3,4,5,6,7],![4,3,6,5,7],![8,8,9,9,10]]:
   Fin 4→Fin 5→Fin 11) p.1 p.2
lemma aFi (p q:Fin 4×Fin 5) (h:orb q=orb p):q=p∨q=(fA p.1,gA p.2):=by revert p q h;decide
lemma sI:Function.Surjective orb:=by decide
lemma lI {L:Submodule ℂ aC} (hL:aD L) (U:aX L=8)
  (hfix:∀x∈L,∀r:Fin 4,r≠0→∀c:Fin 5,
    x (fA r,gA c)=x (r,c)):False:=by
 let a:aC→ₗ[ℂ] (ℂ× ℂ):=
  ((LinearMap.proj (0,0):aC→ₗ[ℂ] ℂ)-LinearMap.proj (0,1)).prod
    ((LinearMap.proj (0,2):aC→ₗ[ℂ] ℂ)-LinearMap.proj (0,3))
 let K:=L⊓LinearMap.ker a
 have P:6≤aX K:=by have h:=Ah.Au.lH a L;have R:Module.finrank ℂ (L.map a)≤2:=(Submodule.finrank_le _).trans (by simp[Module.finrank_prod]);change _+aX K=aX L at h;omega
 have d (x:aC) (b:x∈K) (r:Fin 4) (c:Fin 5):
   x (fA r,gA c)=x (r,c):=by
  by_cases n:r=0
  ·subst r;have i:=sub_eq_zero.mp (congrArg Prod.fst b.2);have j:=sub_eq_zero.mp (congrArg Prod.snd b.2);fin_cases c<;>simp[fA,gA]<;>first | rfl | exact i | exact i.symm | exact j | exact j.symm
  ·exact hfix x b.1 r n c
 let lift:(Fin 11→ℂ)→ₗ[ℂ] aC:=LinearMap.funLeft ℂ ℂ orb
 have f:Function.Injective lift:=fun u v e=>funext fun k=>by obtain⟨p,rfl⟩:=sI k;exact congrFun e p
 let S:Submodule ℂ (Fin 11→ℂ):=K.comap lift
 have B:S.map lift=K:=le_antisymm (Submodule.map_comap_le lift K) fun x b=>by
  have E:lift (fun k=>x (Function.surjInv sI k))=x:=funext fun p=>by
   change x (Function.surjInv sI (orb p))=x p;rcases aFi p _ (Function.surjInv_eq sI (orb p)) with h|h
   ·exact congrArg x h
   ·rw[h];exact d x b p.1 p.2
  exact⟨_,show lift _∈K from E.symm▸b,E⟩
 have Q:6≤Module.finrank ℂ S:=by have:=(Submodule.equivMapOfInjective lift f S).finrank_eq;rw[B] at this;change Module.finrank ℂ S=aX K at this;omega
 let T:(Fin 11→ℂ)→ₗ[ℂ] (Fin 11→ℂ):=
  (LinearMap.pi fun k=>∑p∈univ.filter (fun p=>orb p=k),
    (LinearMap.proj p:aC→ₗ[ℂ] ℂ).comp A6.aHh).comp lift
 obtain⟨o,l⟩:=Ad.gM hL;have F (u:Fin 11→ℂ) (g:u∈S) (v:Fin 11→ℂ) (O:v∈S):
   ∑k,T u k*v k=0:=by
  have e:(∑k,T u k*v k)=Ad.kK (Ad.gQ (lift u)) (lift v):=by
   have t (k:Fin 11):T u k*v k=∑p∈univ.filter (fun p=>orb p=k),
     Ad.gQ (lift u) p*v (orb p):=by
    simp only[T,LinearMap.comp_apply,LinearMap.pi_apply,LinearMap.sum_apply,LinearMap.proj_apply,sum_mul];exact sum_congr rfl fun p M=>by rw[(mem_filter.mp M).2];rfl
   simp_rw[t,sum_fiberwise_of_maps_to (fun _ _=>mem_univ _)];exact Fintype.sum_prod_type _
  exact e.trans (l _ g.1 _ O.1)
 have m:(S⊓LinearMap.ker T:Submodule ℂ (Fin 11→ℂ))= ⊥ :=by
  rw[eq_bot_iff];rintro u ⟨g,C⟩;have H (r:Fin 4) (c:Fin 5):
    Ad.gQ (lift u) (fA r,gA c)=Ad.gQ (lift u) (r,c):=by
   have s:=d (lift u) g;have n:(∑k,lift u (fA r,k))=∑k,lift u (r,k):=by rw[←Equiv.sum_comp gA (fun k=>lift u (fA r,k))];simp only[s]
   have J:(∑k,lift u (k,gA c))=∑k,lift u (k,c):=by rw[←Equiv.sum_comp fA (fun k=>lift u (k,gA c))];simp only[s]
   simp only[Ad.gQ,Ad.gR,Ad.gC,s,n,J]
  have y:Ad.gQ (lift u)=0:=funext fun p=>by
   have A:T u (orb p)=0:=congrFun C (orb p);have G:T u (orb p)=((univ.filter fun q=>orb q=orb p).card:ℂ)*Ad.gQ (lift u) p:=by
    simp only[T,LinearMap.comp_apply,LinearMap.pi_apply,LinearMap.sum_apply,LinearMap.proj_apply];rw[sum_congr rfl fun q N=> ?_,sum_const,nsmul_eq_mul];rcases aFi p q (mem_filter.mp N).2 with rfl|rfl
    ·rfl
    ·exact H p.1 p.2
   rw[G] at A;exact(mul_eq_zero.mp A).resolve_left (Nat.cast_ne_zero.mpr
    (Finset.card_ne_zero.mpr ⟨p,mem_filter.mpr ⟨mem_univ _,rfl⟩⟩))
  have z:lift u=0:=by rw[←Ad.rQ (lift u) (o _ g.1),y];funext p;simp[Ad.bQ,Ad.gR,Ad.gC,Ad.aS,cW]
  exact f (z.trans (map_zero lift).symm)
 have w:=Ah.Au.aGa T S F;rw[m,finrank_bot,Fintype.card_fin] at w;omega
lemma uU {L:Submodule ℂ aC} (hL:aD L) (d:aX L=8)
  (hfix:∀(x:W L 0) (r:Fin 3) (c:Fin 5),
    aA x.val (Equiv.swap 0 1 r) (gA c)=aA x.val r c):False:=by
 refine lI hL d fun x f r e c=> ?_
 obtain⟨s,rfl⟩:=Fin.exists_succ_eq.mpr e;have a (k:Fin 5):x (fA s.succ,gA k)-(∑j,x (fA s.succ,j))/2=
   x (s.succ,k)-(∑j,x (s.succ,j))/2:=by
  have g:fA s.succ=(Equiv.swap (0:Fin 3) 1 s).succ:=by fin_cases s<;>rfl
  simpa[aA,bH,iX,g] using hfix ⟨bH 0 x,Submodule.mem_sup_right ⟨x,f,rfl⟩⟩ s k
 have b:(∑k,x (fA s.succ,k))=∑k,x (s.succ,k):=by
  have H:=sum_congr (s₁:=univ) rfl fun k _=>a k
  simp only[sum_sub_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Equiv.sum_comp gA (fun k=>x (fA s.succ,k))] at H;linear_combination-2*H/3
 have H:=a c;rw[b] at H;linear_combination H
lemma wQ {E:Type*} [AddCommGroup E] [Module ℂ E]
  (f g:E→ₗ[ℂ] ℂ) (y:E) (b:f y≠0) (H:∀x,f x*g x=0) (x:E):g x=0:=by
 have c:=(mul_eq_zero.mp (H y)).resolve_left b;by_cases a:f x=0
 ·have e:=H (x+y);rw[map_add,map_add,a,c,zero_add,add_zero] at e;exact(mul_eq_zero.mp e).resolve_left b
 ·exact(mul_eq_zero.mp (H x)).resolve_left a
def Qj (j:Fin 3) (y:fZ):ℂ:=(y (j.succAbove 1)-y (j.succAbove 0))*y j
lemma aFj (j:Fin 3) (f:Fin 3→ℂ):
  ∑r,f r=f j+f (j.succAbove 0)+f (j.succAbove 1):=by
 fin_cases j<;>simp[Fin.sum_univ_three,Fin.succAbove]<;>ring
lemma aCf (j:Fin 3) (v:fZ) (b:v j=0) (a:∑r,v r=0):
  v (j.succAbove 1)= -v (j.succAbove 0):=by
 rw[aFj j,b] at a;linear_combination a
lemma aFk {L:Submodule ℂ aC} (h:oW L) (j:Fin 3)
  (m:∀x:W L 0,(aI L 0 x-aI L 1 x) j=0)
  (C:∃x:W L 0,aI L 0 x-aI L 1 x≠0):
  (∀x:W L 0,(aI L 0 x+aI L 1 x) (j.succAbove 1)=(aI L 0 x+aI L 1 x) (j.succAbove 0))∧
  ∀
   x:W L 0,Qj j (aI L 2 x+aI L 3 x-(2:ℂ)•aI L 4 x)=
   -3*Qj j (aI L 2 x-aI L 3 x):=by
 let a:=aI L 0+aI L 1;let u:=aI L 0-aI L 1
 let v:=aI L 2-aI L 3;let r:=aI L 2+aI L 3-(2:ℂ)•aI L 4
 have t (x:W L 0):u x (j.succAbove 1)= -u x (j.succAbove 0):=aCf j (u x) (m x) (bG h.1 h.2.2.2.1 x).2.1;obtain⟨y,E⟩:=C;have o:u y (j.succAbove 0)≠0:=fun e=>E (funext fun i=>by
  rcases (by decide:∀j i:Fin 3,i=j∨i=j.succAbove 0∨i=j.succAbove 1) j i with rfl|rfl|rfl
  ·exact m y
  ·exact e
  ·have:=t y;change u y (j.succAbove 1)=0;rw[this,e,neg_zero])
 have z (x:W L 0):a x (j.succAbove 1)=a x (j.succAbove 0):=sub_eq_zero.mp<|
  wQ ((LinearMap.proj (j.succAbove 0):fZ→ₗ[ℂ] ℂ).comp u)
   (((LinearMap.proj (j.succAbove 1):fZ→ₗ[ℂ] ℂ)-LinearMap.proj (j.succAbove 0)).comp a) y o (fun p=>by
   have l:=(bG h.1 h.2.2.2.1 p).2.2;rw[aFj j] at l;have g:=t p;have k:u p j=0:=m p;change u p j*a p j+u p (j.succAbove 0)*a p (j.succAbove 0)+u p (j.succAbove 1)*a p (j.succAbove 1)=0 at l;rw[g,k] at l;change u p (j.succAbove 0)*(a p (j.succAbove 1)-a p (j.succAbove 0))=0;linear_combination-l) x
 have n (p:W L 0):u p (j.succAbove 0)*(Qj j (r p)+3*Qj j (v p))=0:=by
  have b:=oY p.val;rw[(bG h.1 h.2.2.2.1 p).1,sub_self,mul_zero] at b;have g:=t p;have k:u p j=0:=m p;have q (w:fZ):D (u p) w w=2*u p (j.succAbove 0)*Qj j w:=by fin_cases j<;>simp[D,Qj,Fin.succAbove] at g k ⊢ <;>rw[g,k]<;>ring
  change 0=4*D (u p) (a p) (a p)-D (u p) (r p) (r p)-3*D (u p) (v p) (v p) at b;rw[q,q,q] at b;simp only[Qj,z p,sub_self,zero_mul] at b ⊢
  linear_combination b/2
 refine⟨z,fun x=> ?_⟩;by_cases A:u x (j.succAbove 0)=0
 ·have p (s:ℂ) (B:s≠0):Qj j (r (x+s•y))= -3*Qj j (v (x+s•y)):=
   by linear_combination(mul_eq_zero.mp (n (x+s•y))).resolve_left (by simp only[map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul,A,zero_add];exact mul_ne_zero B o)
  have c:=p 1 one_ne_zero;have d:=p (-1) (by norm_num);have f:=p 2 (by norm_num);simp only[Qj,map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul] at c d f ⊢
  linear_combination c+d/3-f/3
 ·linear_combination(mul_eq_zero.mp (n x)).resolve_left A
lemma yO {L:Submodule ℂ aC} {j k:Fin 3} (o:j≠k) {a b:Fin 5}
  (m:a≠4) (n:b≠4) {y:W L 0}
  (u:(aI L a y-aI L b y) k=0)
  (t:∑r,(aI L a y-aI L b y) r=0)
  (w:aI L a y-aI L b y≠0)
  (E:∀x:W L 0,Qj j (aI L a x+aI L b x-(2:ℂ)•aI L 4 x)=
    -3*Qj j (aI L a x-aI L b x))
  {z:fZ} (l:jG 4 z∈W L 0):
  z j=0∧z (j.succAbove 1)=z (j.succAbove 0):=by
 let v:=aI L a y-aI L b y
 have F: -3*Qj j v≠0:=by
  have d:v k=0:=u;have h:=aCf k v d t;have i:v (k.succAbove 0)≠0:=fun e=>w (funext fun r=>by
   rcases (by decide:∀k r:Fin 3,r=k∨r=k.succAbove 0∨r=k.succAbove 1) k r with rfl|rfl|rfl
   ·exact d
   ·exact e
   ·change v (k.succAbove 1)=0;rw[h,e,neg_zero])
  exact mul_ne_zero (by norm_num) (by fin_cases j<;>fin_cases k<;>simp[Qj,Fin.succAbove] at o h d i ⊢ <;>simp[h,d,i])
 let p:=aI L a y+aI L b y-(2:ℂ)•aI L 4 y
 have f (s:ℂ):((p (j.succAbove 1)-p (j.succAbove 0))+
   s*(-2*(z (j.succAbove 1)-z (j.succAbove 0))))*(p j+s*(-2*z j))= -3*Qj j v:=by
  have q:=E (y+s•⟨jG 4 z,l⟩);have J (c:Fin 5):aI L c ⟨jG 4 z,l⟩=if c=4 then z else 0:=nP 4 c z
  simp only[map_add,map_smul,J,m,n,ite_false,ite_true,smul_zero,add_zero,Qj,p,v,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at q ⊢
  linear_combination q
 have g {A B C D:ℂ} (H:∀s,(A+s*B)*(C+s*D)= -3*Qj j v):B=0:=by by_contra G;have e:=H (-A/B);rw[div_mul_cancel₀ _ G,add_neg_cancel,zero_mul] at e;exact F e.symm
 exact⟨by linear_combination-g (fun s=>(mul_comm _ _).trans (f s))/2,by linear_combination-g f/2⟩
lemma mC (gF:eI) {L:Submodule ℂ aC} (h:oW L):
  ∃x:W L 0,aI L 0 x-aI L 1 x≠0:=by
 by_contra! f;obtain⟨M,c,a,b⟩:=Ah.wJ h.1 h.2.1 0 (by decide:(0:Fin 5)≠1) (by intro t d r g;obtain⟨s,rfl⟩:=Fin.exists_succ_eq.mpr g;have e:=congrFun (f ⟨bH 0 t,Submodule.mem_sup_right ⟨t,d,rfl⟩⟩) s;change aA (bH 0 t) s 0-aA (bH 0 t) s 1=0 at e;simp only[aA,bH,iX,LinearMap.funLeft_apply,Equiv.swap_self,Equiv.refl_apply] at e;linear_combination e);exact gF M c a b
lemma iN (gF:eI) {L:Submodule ℂ aC} (h:oW L):
  (∃j:Fin 3,∀x:W L 0,(aI L 0 x-aI L 1 x) j=0)∧
  ∃x:W L 0,aI L 0 x-aI L 1 x≠0:=by
 obtain⟨x,c⟩:=mC gF h;by_cases a:aCe (aI L 0-aI L 1)
 ·obtain⟨y,d⟩:=mC gF (zQ h);have z:=aDt h a (wO y);have b:bP 2=0∧bP 3=1:=by decide
  rw[gD,gD,b.1,b.2] at z;exact(d z).elim
 ·exact⟨nZ h a,x,c⟩
lemma sJ (gF:eI) {L:Submodule ℂ aC} (h:oW L):False:=by
 obtain⟨⟨j,w⟩,hu⟩:=iN gF h;obtain⟨⟨k,E⟩,F⟩:=iN gF (zQ h);have f:bP 0=2∧bP 1=3∧bP 2=0∧bP 3=1∧bP 4=4:=by decide
 have K (x:W L 0):(aI L 2 x-aI L 3 x) k=0:=by have e:=E (zR x);rwa [gB,gB,f.1,f.2.1] at e
 have M:∃x:W L 0,aI L 2 x-aI L 3 x≠0:=by obtain⟨y,hy⟩:=F;exact⟨wO y,by rwa [gD,gD,f.2.2.1,f.2.2.2.1]⟩
 obtain⟨O,g⟩:=aFk h j w hu;obtain⟨Q,q⟩:=aFk (zQ h) k E F;have P (x:W L 0):(aI L 2 x+aI L 3 x) (k.succAbove 1)=
   (aI L 2 x+aI L 3 x) (k.succAbove 0):=by
  have e:= Q (zR x);rwa [gB,gB,f.1,f.2.1] at e
 have l (x:W L 0):Qj k (aI L 0 x+aI L 1 x-(2:ℂ)•aI L 4 x)=
   -3*Qj k (aI L 0 x-aI L 1 x):=by
  have e:=q (zR x);simp only[gB,f.2.2.1,f.2.2.2.1,f.2.2.2.2] at e;exact e
 obtain⟨u,z,o,G⟩:=wP h;have T:j=k:=by by_contra t;obtain⟨y,hy⟩:=M;obtain⟨x,hx⟩:=hu;obtain⟨zj,v⟩:=yO t (by decide) (by decide) (K y) (bG h.1 h.2.2.2.2 y).2.1 hy g G;obtain⟨C,_⟩:=yO (Ne.symm t) (by decide) (by decide) (w x) (bG h.1 h.2.2.2.1 x).2.1 hx l G;apply o;funext r;fin_cases j<;>fin_cases k<;>fin_cases r<;>simp[Fin.succAbove] at t zj v C ⊢ <;>first | exact zj | exact C | exact v.trans C | exact v.symm.trans C
 subst T;have ew (x:W L 0):aI L 4 x (j.succAbove 1)=aI L 4 x (j.succAbove 0):=by
  let J:W L 0:=⟨1,fN L 0⟩
  obtain⟨s,U,V,X,Z⟩:=u J 0;have N (c:Fin 5):aI L c J j= -(3/2:ℂ):=by change aA 1 j c=_;norm_num[aA]
  refine sub_eq_zero.mp (wQ ((LinearMap.proj j:fZ→ₗ[ℂ] ℂ).comp (aI L 0+aI L 1-aI L 2-aI L 3))
   (((LinearMap.proj (j.succAbove 1):fZ→ₗ[ℂ] ℂ)-LinearMap.proj (j.succAbove 0)).comp (aI L 4)) s (by
    simp only[LinearMap.comp_apply,LinearMap.proj_apply,LinearMap.sub_apply,LinearMap.add_apply,Pi.sub_apply,Pi.add_apply,U,V,X,Z,N,map_zero,Pi.zero_apply];norm_num) (fun y=>by
   have H1:=g y;have H2:=l y;simp only[Qj,K y,w y,mul_zero,Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,P y,O y] at H1 H2;change(aI L 0 y j+aI L 1 y j-aI L 2 y j-aI L 3 y j)*(aI L 4 y (j.succAbove 1)-aI L 4 y (j.succAbove 0))=0;linear_combination(H1-H2)/2) x)
 let ρ:Equiv.Perm (Fin 4):=Equiv.swap j.succ 3
 let τ:Equiv.Perm (Fin 3):=Equiv.swap j 2
 have hρ (r:Fin 3):ρ r.succ=(τ r).succ:=by fin_cases j<;>fin_cases r<;>rfl
 have S:(L.map (Ad.re ρ 1)).map (Ad.re ρ 1)=L:=by rw[←Submodule.map_comp,show(Ad.re ρ 1).comp (Ad.re ρ 1)=LinearMap.id by ext m ⟨i,c⟩;simp[Ad.re,ρ],Submodule.map_id]
 refine uU (Ad.gI ρ 1 h.1) ((Ad.nL ρ 1 L).trans h.2.1) fun y r c=> ?_
 let x:W L 0:=⟨fun p=>y.1 (τ p.1,p.2),by have M:(fun p=>y.1 (τ p.1,p.2))∈W ((L.map (Ad.re ρ 1)).map (Ad.re ρ 1)) 0:=aGz ρ τ hρ 1 y.2;rwa [S] at M⟩
 have n (s:Fin 3) (d:Fin 5):aA y.val s d=aA x.val (τ s) d:=by have e:=mT τ 1 y.val (τ s) d;rw[Equiv.swap_apply_self j 2 s] at e;exact e.symm
 rw[n,n,show τ (Equiv.swap 0 1 r)=Equiv.swap (j.succAbove 0) (j.succAbove 1) (τ r) by fin_cases j<;>fin_cases r<;>rfl];have H (a b:fZ) (hs:(a+b) (j.succAbove 1)=(a+b) (j.succAbove 0))
   (o:(a-b) j=0) (hc:∑r,(a-b) r=0) (s:Fin 3):
   b (Equiv.swap (j.succAbove 0) (j.succAbove 1) s)=a s∧
   a (Equiv.swap (j.succAbove 0) (j.succAbove 1) s)=b s:=by
  have op:=aCf j (a-b) o hc;have d:=(by decide:∀j:Fin 3,j≠j.succAbove 0∧j≠j.succAbove 1) j;simp only[Pi.add_apply,Pi.sub_apply] at hs o op;rcases (by decide:∀j s:Fin 3,s=j∨s=j.succAbove 0∨s=j.succAbove 1) j s with rfl|rfl|rfl
  ·rw[Equiv.swap_apply_of_ne_of_ne d.1 d.2];exact⟨by linear_combination-o,by linear_combination o⟩
  ·rw[Equiv.swap_apply_left];exact⟨by linear_combination(hs-op)/2,by linear_combination(hs+op)/2⟩
  ·rw[Equiv.swap_apply_right];exact⟨by linear_combination-(hs+op)/2,by linear_combination-(hs-op)/2⟩
 have A:=H (aI L 0 x) (aI L 1 x) (O x) (w x) (bG h.1 h.2.2.2.1 x).2.1 (τ r);have B:=H (aI L 2 x) (aI L 3 x) (P x) (K x) (bG h.1 h.2.2.2.2 x).2.1 (τ r);fin_cases c
 ·exact A.1
 ·exact A.2
 ·exact B.1
 ·exact B.2
 ·have R:=ew x;fin_cases j<;>fin_cases r<;>first | rfl | exact R | exact R.symm
lemma jI (gF:eI):fD:=by
 intro L p w i t A B ca cb o l;obtain⟨a,b,r,rfl⟩:=card_eq_two.mp ca;obtain⟨c,d,s,rfl⟩:=card_eq_two.mp cb;have C:=Finset.disjoint_left.mp o;have g:a≠c∧a≠d∧b≠c∧b≠d:=by simp_all
 have j:({a,b,c,d}:Finset (Fin 5))ᶜ.card=1:=by simp[card_compl,r,s,g.1,g.2.1,g.2.2.1,g.2.2.2]
 obtain⟨m,z⟩:=card_pos.mp (j▸Nat.zero_lt_one);have E:m≠a∧m≠b∧m≠c∧m≠d:=by simpa[not_or] using z
 let f:Fin 5→Fin 5:= ![a,b,c,d,m]
 let e:Equiv.Perm (Fin 5):=Equiv.ofBijective f (Finite.injective_iff_bijective.mp fun x y h=>by fin_cases x<;>fin_cases y<;>simp_all[f,ne_comm])
 have q (u v:Fin 5):bY u v∈bJ {u,v}:=
  ⟨by simpa using uJ u v 1,fun k n=>by
   simp only[mem_insert,mem_singleton,not_or] at n;simp[bY,n.1,n.2]⟩
 exact sJ gF (aA6 p w (Equiv.swap 0 i) e (by simpa using t)
  (by rw[Equiv.swap_apply_left,l];exact Submodule.mem_sup_left (q a b))
  (by rw[Equiv.swap_apply_left,l];exact Submodule.mem_sup_right (q c d)))
lemma pZ:fD:=jI Ac.vV
end Ac.Af
namespace Ac.An
open Aa Matrix
abbrev wR (L:Submodule ℂ aC) (i j:Fin 4) (a b:aH):Prop:=
 ∃
  t∈L,∃s:Equiv.Perm (Fin 4),s 2=i∧s 3=j∧
  row i t=0∧row j t=0∧a=row (s 0) t∧b=row (s 1) t
set_option maxHeartbeats 800000 in
lemma sK {L:Submodule ℂ aC} (hL:aD L) (J:aX L=8)
  (x:∀r,u L r=0) {i j:Fin 4} (g:i≠j) (N:p L i j≤6):
  ∃
   a b:aH,wR L i j a b∧(∑c,a c)+(∑c,b c)=0∧
   Ag.dQ a b=0∧(Ag.dL a b).IsSymm∧
   (∀c,Ag.dL a b c c=0)∧Ag.dL a b*ᵥ (1:aH)≠0∧
   ∀t∈L,(1+row i t) ⬝ᵥ Ag.dL a b*ᵥ (1+row j t)=0:=by
 classical
 obtain⟨s,f,l⟩:=Ae.zD i j g
 let M:=L.map (Ad.re s 1)
 have w:aD M:=Ad.gI s 1 hL
 let K:=aJ L i j
 let A:=sB L i j (s 0)
 let B:=sB L i j (s 1)
 have y:s 0≠i:=f▸fun h=>(show(0:Fin 4)≠2 by decide) (s.injective h)
 have z:s 0≠j:=l▸fun h=>(show(0:Fin 4)≠3 by decide) (s.injective h)
 have C:s 1≠i:=f▸fun h=>(show(1:Fin 4)≠2 by decide) (s.injective h)
 have E:s 1≠j:=l▸fun h=>(show(1:Fin 4)≠3 by decide) (s.injective h)
 have q:Function.Injective A:=eB x y z g
 have v:Function.Injective B:=eB x C E g
 have n (k:K):Ae.bD (A k) (B k) 0 0∈M:=by
  refine⟨k.val.val,k.val.property,?_⟩
  funext ⟨r,c⟩
  fin_cases r
  ·rfl
  ·rfl
  ·change k.val.val (s 2,c)=0
   rw[f]
   exact congrFun (show row i k.val=0 from k.property.1) c
  ·change k.val.val (s 3,c)=0
   rw[l]
   exact congrFun (show row j k.val=0 from k.property.2) c
 have m (k:K):(∑c,A k c)+(∑c,B k c)=0:=by
  have h:=(Ac.Ad.cT w (n k)).1
  simpa[cW,Fin.sum_univ_four,Ae.bD] using h
 have d (k:K) (t:L):
   Ae.bil (1+row i t) (1+row j t) (Ae.dL (A k) (B k))=0:=by
  have H:Ae.aR M (Ae.aM 1 (Ad.re s 1 t)) 1:=
   ⟨_,⟨t,t.property,rfl⟩,rfl⟩
  have h:=Ae.rR w (n k) H
  change Ae.bil (1+row (s 2) t) (1+row (s 3) t) _=0 at h
  rwa [f,l] at h
 have e (k:K):Ag.dQ (A k) (B k)=0:=by
  have h:=d k 0
  change Ae.bil (1+row i 0) (1+row j 0) (Ae.dL (A k) (B k))=0 at h
  simp only[map_zero,add_zero,Ae.bil,Pi.one_apply,one_mul,mul_one,
   Ae.pO] at h
  change Ae.dQ (A k) (B k)=0
  exact(mul_eq_zero.mp h).resolve_left (by norm_num)
 have o:2≤Module.finrank ℂ K:=by
  have h:=cA L i j
  change p L i j+Module.finrank ℂ K=aX L at h
  omega
 obtain⟨k,F⟩:=fX (T:=L) (aJ L i j) A B q v m e o
 refine⟨A k,B k,⟨k.val.val,k.val.property,s,f,l,k.property.1,k.property.2,rfl,rfl⟩,
  m k,e k,qL _ _,fun c=>by simp[Ag.dL],F,?_⟩
 intro t G
 rw[←jW]
 exact d k ⟨t,G⟩
abbrev tS (L:Submodule ℂ aC) (i j:Fin 4) (n:aH):Prop:=
 ∃
  a b:aH,wR L i j a b∧(∑c,a c)+(∑c,b c)=0∧
  Ag.dQ a b=0∧(Ag.dL a b).IsSymm∧
  (∀c,Ag.dL a b c c=0)∧Ag.dL a b*ᵥ (1:aH)≠0∧
  ∀x∈bM n,∀y∈bM n,x ⬝ᵥ Ag.dL a b*ᵥ y=0
lemma rH {L:Submodule ℂ aC} (hL:aD L) (m:aX L=8)
  (z:∀r,u L r=0) {i j:Fin 4} {n:aH} (e:i≠j) (f:p L i j=6)
  (q:aE L i=3) (s:aE L j=3) (c:aY L i=bM n)
  (d:aY L j=bM n):tS L i j n:=by
 obtain⟨a,b,A,x,w,l,k,v,h⟩:=sK hL m z e f.le;refine⟨a,b,A,x,w,l,k,v,?_⟩
 let F:=Matrix.toLinearMap₂' ℂ (S₁:=ℂ) (S₂:=ℂ) (Ag.dL a b)
 have g:p L i j=aE L i+aE L j:=by rw[f,q,s]
 have o:=nU g F (fun t y=>by simpa only[F,Matrix.toLinearMap₂'_apply'] using h t y);simpa only[F,Matrix.toLinearMap₂'_apply',c,d] using o
lemma sL {L:Submodule ℂ aC} (k:aX L=8) (i:∀r,u L r=0)
  {a b c:Fin 4} (hab:a≠b) (d:a≠c) (e:b≠c)
  (j:aE L a=3) (f:aE L b=3) (g:aE L c=3):
  ∃r,a≠r∧aE L r=3∧p L a r=6:=by
 have m:=bB i hab d e;have l:=cF L a b;have n:=cF L a c;by_cases h:p L a b=6
 ·exact⟨b,hab,f,h⟩
 exact⟨c,d,g,by omega⟩
lemma oZ {L:Submodule ℂ aC} (hL:aD L) (j:aX L=8)
  (m:∀r,u L r=0) {a b c:Fin 4} {n:aH} (hab:a≠b) (g:a≠c)
  (h:b≠c) (e:aE L a=3) (o:aE L b=3) (q:aE L c=3)
  (f:∀i,aE L i=3→aY L i=bM n):
  ∃r,a≠r∧aE L r=3∧p L a r=6∧tS L a r n:=by
 obtain⟨r,l,d,k⟩:=sL j m hab g h e o q;exact⟨r,l,d,k,rH hL j m l k e d (f a e) (f r d)⟩
end Ac.An
namespace Ac.An
open Aa Matrix
lemma kQ {n:aH} {Z:Matrix (Fin 5) (Fin 5) ℂ}
  (j:Z.IsSymm) (g:∀c,Z c c=0)
  (h:∀x∈bM n,x ⬝ᵥ Z*ᵥ x=0)
  {a b:Fin 5} (e:n a≠0) (f:n b≠0):Z a b=0:=by
 let x:aH:=Pi.single a (n b)+Pi.single b (-n a)
 have k:x∈bM n:=by change n ⬝ᵥ x=0;dsimp only[x];rw[dotProduct_add,dotProduct_single,dotProduct_single];ring
 have d:=h x k;dsimp only[x] at d;rw[mulVec_add,add_dotProduct,dotProduct_add,dotProduct_add] at d;simp only[single_dotProduct,mulVec,dotProduct_single,g,j.apply a b] at d;have i:(-2*n a*n b)*Z a b=0:=by linear_combination d
 exact(mul_eq_zero.mp i).resolve_left
  (mul_ne_zero (mul_ne_zero (by norm_num) e) f)
end Ac.An
namespace Ay
lemma qA (x a b:ℂ)
  (c:2*x+(a+b)=0) (d:2*x^2+(a^2+b^2)=0)
  (e:2*x^3+(a^3+b^3)=0):x=0:=by
 have H:x^3=0:=by
  linear_combination
   (((a+b)^2/2-x*(a+b)+5*x^2)*c-(3*(a+b)/2)*d+e)/12
 simpa using H
lemma sM (n:Fin 5→ℂ) (E:n≠0)
  (r:∑i,n i=0) (F:∑i,n i*n i=0)
  (y:At.e3 n=0) (k:∃i,n i=0):Function.Injective n:=by
 classical
 have d:∑i,n i^2=0:=by simpa only[pow_two] using F
 have H:=At.oN n;rw[y,r,d] at H;have x:∑i,n i^3=0:=by linear_combination-H/2
 obtain⟨z,k⟩:=k;intro i j e;by_contra g;have w:n i≠0:=by
  intro A;have C:=e.symm.trans A;have u:Finset.univ.filter (fun t=>n t≠0)⊆({i,j}:Finset _)ᶜ:=by
   intro t G;have m:n t≠0:=(Finset.mem_filter.mp G).2;simpa only[Finset.mem_compl,Finset.mem_insert,Finset.mem_singleton,not_or]
    using And.intro (fun h:t=i=>m (h▸A)) (fun h:t=j=>m (h▸C))
  apply At.mQ n E _ r d y;exact(Finset.card_le_card u).trans (by simp[Finset.card_compl,g])
 have o:z≠i:=fun h=>w (h▸k)
 have p:z≠j:=fun h=>w (e.trans (h▸k))
 let s:Finset (Fin 5):={z,i,j}
 have l:sᶜ.card=2:=by simp[s,Finset.card_compl,o,p,g]
 obtain⟨a,b,hab,q⟩:=Finset.card_eq_two.mp l;have c (f:ℂ→ℂ) (B:f 0=0):
   ∑t,f (n t)=2*f (n i)+(f (n a)+f (n b)):=by
  rw[←Finset.sum_add_sum_compl s,q];simp[s,o,p,g,hab,k,B,←e,two_mul]
 apply w;apply qA (n i) (n a) (n b)
 ·exact(c id rfl).symm.trans r
 ·exact(c (fun v=>v^2) (by norm_num)).symm.trans d
 ·exact(c (fun v=>v^3) (by norm_num)).symm.trans x
end Ay
namespace Ac.A8
open Aa Ae
def d3 (z:F→F→ℂ) (i j k l m:F):ℂ:=
 z i i*(z j l*z k m-z j m*z k l)-
 z i l*(z j i*z k m-z j m*z k i)+
 z i m*(z j i*z k l-z j l*z k i)
lemma aA7 (a b:aH) (i j k l m:F):
  d3 (aL a b) i j k l m=0:=by
 unfold d3 aL;ring
lemma qB (a b u v:aH)
  (g:∀i j,i≠j→aL a b i j=aL u v i j)
  (n:∀i j,i≠j→u i*v j-u j*v i≠0):
  ∀i j,aL a b i j=aL u v i j:=by
 intro i d;by_cases h:i=d
 ·subst d
  let s:Equiv.Perm F:=Equiv.swap 0 i
  have q:s 0=i:=Equiv.swap_apply_left _ _;rw[←q];have e {r t:F} (h:r≠t):aL a b (s r) (s t)=aL u v (s r) (s t):=g _ _ (s.injective.ne h)
  let j:=s 1
  let k:=s 2
  let l:=s 3
  let m:=s 4
  let o:=s 0
  have c:=aA7 a b o j k l m;have p:=aA7 u v o j k l m;unfold d3 at c p;rw[show aL a b j l=_ from e (by decide:(1:F)≠3),
      show aL a b k m=_ from e (by decide:(2:F)≠4),
      show aL a b j m=_ from e (by decide:(1:F)≠4),
      show aL a b k l=_ from e (by decide:(2:F)≠3),
      show aL a b o l=_ from e (by decide:(0:F)≠3),
      show aL a b j o=_ from e (by decide:(1:F)≠0),
      show aL a b k o=_ from e (by decide:(2:F)≠0),
      show aL a b o m=_ from e (by decide:(0:F)≠4)] at c
  have f:(aL a b o o-aL u v o o)*
    (aL u v j l*aL u v k m-aL u v j m*aL u v k l)=0:=by
   linear_combination c-p
  have det:aL u v j l*aL u v k m-aL u v j m*aL u v k l=
    -(u j*v k-u k*v j)*(u l*v m-u m*v l):=by
   unfold aL;ring
  rw[det] at f;exact sub_eq_zero.mp ((mul_eq_zero.mp f).resolve_right
   (mul_ne_zero (neg_ne_zero.mpr (n j k (s.injective.ne (by decide:(1:F)≠2))))
     (n l m (s.injective.ne (by decide:(3:F)≠4)))))
 ·exact g i d h
lemma lJ (a b:aH) (i:F):
  ∑j,aL a b i j=a i*(∑j,b j)+b i*(∑j,a j):=by
 simp only[aL,Finset.sum_add_distrib,Finset.mul_sum];congr 1;apply Finset.sum_congr rfl;intro j _;ring
lemma uL (a b:aH):
  ∑i,∑j,aL a b i j=2*((∑j,a j)*(∑j,b j)):=by
 simp_rw[lJ];rw[Finset.sum_add_distrib,←Finset.sum_mul,←Finset.sum_mul];ring
def iB (p:F) (c:ℂ):aH:=fun i=>if i=p then c else-c
lemma aA8 (p:F) (c:ℂ):∑j,iB p c j= -3*c:=by fin_cases p<;>simp[Fin.sum_univ_succ,iB]<;>ring
lemma pB (a b n:aH) (p:F) (c:ℂ)
  (l:c≠0) (w:Function.Injective n) (q:n p=0)
  (x:∑i,n i=0) (f:(∑i,a i)+(∑i,b i)=0)
  (B:∀i j,i≠j→aL a b i j=aL (iB p c) n i j):
  False:=by
 let u:=iB p c
 have k (i:F) (h:i≠p):n i≠0:=by simpa only[←q] using w.ne h
 have A (i j:F) (m:i≠j):u i*n j-u j*n i≠0:=by
  by_cases s:i=p
  ·subst i;have o:=k j m.symm;simp[u,iB,q,l,o]
  by_cases o:j=p
  ·subst j;have h:=k i s;simp[u,iB,q,l,h]
  simp only[u,iB,ite_eq_right s,ite_eq_right o];exact fun e=>(mul_ne_zero l (sub_ne_zero.mpr (w.ne m))) (show c*(n i-n j)=0 by linear_combination e)
 have d:=qB a b u n B A;have v:(∑i,∑j,aL a b i j)=(∑i,∑j,aL u n i j):=by simp_rw[d]
 rw[uL,uL,x,mul_zero,mul_zero] at v;have C:(∑i,a i)*(∑i,b i)=0:=by linear_combination v/2
 have r:∑i,a i=0:=by
  rcases mul_eq_zero.mp C with h|h
  ·exact h
  ·linear_combination f-h
 have z:∑i,b i=0:=by linear_combination f-r
 let t:F:=if p=0 then 1 else 0
 have y:t≠p:=by
  dsimp[t]
  split_ifs with h
  ·subst p;decide
  ·exact Ne.symm h
 have g:(∑j,aL a b t j)=(∑j,aL u n t j):=by simp_rw[d]
 rw[lJ,lJ,r,z,x,aA8] at g;exact(mul_ne_zero (k t y) l) (show n t*c=0 by linear_combination g/3)
end Ac.A8
namespace Ac.A8
open Aa Ae Matrix
lemma rI {n v:aH} (d:n≠0) (e:v≠0)
  (h:∀x:aH,n ⬝ᵥ x=0→x ⬝ᵥ v=0):
  ∃t:ℂ,t≠0∧∀i,v i=t*n i:=by
 obtain⟨r,g⟩:∃r,n r≠0:=by by_contra! a;exact d (funext a)
 let t:=v r/n r
 have a (i:F):v i=t*n i:=by
  let x:aH:=Pi.single i (n r)-Pi.single r (n i)
  have f:n ⬝ᵥ x=0:=by simp only[x,dotProduct_sub,dotProduct_single];ring
  have b:=h x f;simp only[x,sub_dotProduct,single_dotProduct] at b;dsimp[t];field_simp;linear_combination b
 refine⟨t,?_,a⟩;intro c;apply e;funext i;simpa[c] using a i
lemma uV {n a b:aH} (B:n≠0) (s:Function.Injective n)
  (v:(∑i,n i)=0) {p:F} (f:n p=0)
  (u:(∑i,a i)+(∑i,b i)=0)
  (y:dQ a b=0)
  (q:Matrix.IsSymm (dL a b:Matrix F F ℂ))
  (r:∀i j,n i≠0→n j≠0→dL a b i j=0)
  (A:(dL a b:Matrix F F ℂ)*ᵥ (1:aH)≠0)
  (w:∀x:aH,n ⬝ᵥ x=0→x ⬝ᵥ (dL a b:Matrix F F ℂ)*ᵥ (1:aH)=0):
  False:=by
 obtain⟨t,z,m⟩:=rI B A w;have o (i:F):(∑j,dL a b i j)=t*n i:=by simpa only[Matrix.mulVec,dotProduct_one] using m i
 have e (i:F) (c:i≠p):n i≠0:=by simpa only[←f] using s.ne c
 have h (i:F) (c:i≠p):dL a b i p=t*n i:=by
  rw[←o];symm;apply Finset.sum_eq_single p
  ·intro j _ l;exact r i j (e i c) (e j l)
  ·simp
 apply pB a b n p (t/2) (div_ne_zero z (by norm_num)) s f v u;intro i j g;have c:=oG a b i j g;rw[pO,y,o,o] at c;unfold aL at c;by_cases d:i=p
 ·subst i;have l:=h j g.symm;have sym:dL a b p j=dL a b j p:=q.apply _ _;rw[sym,l,f] at c;simp[aL,iB,g.symm,f];linear_combination c/6
 by_cases k:j=p
 ·subst j;rw[h i d,f] at c;simp[aL,iB,d,f];linear_combination c/6
 rw[r _ _ (e i d) (e j k)] at c;simp only[aL,iB,ite_eq_right d,ite_eq_right k];linear_combination c/6
end Ac.A8
namespace Ac.An
open Aa Matrix
lemma lK {L:Submodule ℂ aC} {i j:Fin 4} {n:aH}
  (m:n≠0) (g:(∑c,n c)=0) (z:tS L i j n):
  (∑c,n c*n c)≠0∨At.e3 n≠0:=by
 classical
 obtain⟨a,b,_,t,y,o,u,q,h⟩:=z;have k (i j:Fin 5) (v:n i≠0) (w:n j≠0):
   Ag.dL a b i j=0:=
  kQ o u (fun x f=>h x f x f) v w
 have e:∃p,n p=0:=by
  by_contra! l;have s:Ag.dL a b=0:=by ext i j;exact k i j (l i) (l j)
  exact q (by rw[s,Matrix.zero_mulVec])
 by_contra! d;have r:=Ay.sM n m g d.1 d.2 e;obtain⟨p,e⟩:=e;exact A8.uV m r g e t y o k q
  (fun x f=>h x f 1 (by change n ⬝ᵥ (1:aH)=0;simpa only[dotProduct_one] using g))
lemma oA {L:Submodule ℂ aC} (hL:aD L) (k:aX L=8)
  (o:∀r,u L r=0) {a b c:Fin 4} {n:aH}
  (l:n≠0) (m:(∑i,n i)=0)
  (hab:a≠b) (d:a≠c) (e:b≠c)
  (g:aE L a=3) (h:aE L b=3) (j:aE L c=3)
  (f:∀i,aE L i=3→aY L i=bM n):
  (∑i,n i*n i)≠0∨At.e3 n≠0:=by
 obtain⟨_,_,_,_,p⟩:=oZ hL k o hab d e g h j f;exact lK l m p
lemma tT {L:Submodule ℂ aC} (hL:aD L) (f:aX L=8)
  (g:∀l,u L l=0) (h:∀i j,i≠j→p L i j≤6)
  (v:¬ ∃i j:Fin 4,i≠j∧aE L i=4∧aE L j=4):
  ∃
   n:aH,n≠0∧(∑j,n j)=0∧
   (∀i,aE L i=3→aY L i=bM n)∧
   (∀i,aE L i≤3→aY L i≤bM n)∧
   ((∑j,n j*n j)≠0∨At.e3 n≠0):=by
 obtain⟨a,b,c,hab,d,e,m,o,q⟩:=(wH hL f g h).resolve_left v;obtain⟨n,r,s,k,t⟩:=pU hL f g hab d e m o q;exact⟨n,r,s,k,t,oA hL f g r s hab d e m o q k⟩
end Ac.An
namespace Ac.A1
open Aa Ad At
abbrev V (k:ℕ):=Fin k→ℂ
def fQ (n:aH):V 4→ₗ[ℂ] aC where
 toFun u:=fun p=>u p.1*n p.2
 map_add' u v:=by funext p;simp[add_mul]
 map_smul' a u:=by funext p;simp[mul_assoc]
def cG (n:aH) (x:aC) (i:Fin 4):ℂ:=∑j,n j*x (i,j)
def rJ (n:aH):ℂ:=∑j,n j*n j
lemma yP {n:aH} (b:n≠0):Function.Injective (fQ n):=by
 obtain⟨j,a⟩:∃j,n j≠0:=by by_contra! h;exact b (funext h)
 intro x y h;funext i;exact mul_right_cancel₀ a (congrFun h (i,j))
lemma pC (u:V 4) {n:aH} (a:∑j,n j=0):cW (fQ n u)=0:=by simp[cW,fQ,←Finset.mul_sum,a]
lemma rK (u:V 4) (n:aH) (i:Fin 4):
  cG n (fQ n u) i=u i*rJ n:=by
 simp only[cG,fQ,LinearMap.coe_mk,AddHom.coe_mk,rJ,Finset.mul_sum];apply Finset.sum_congr rfl;intro j _;ring
lemma mU (u:V 4) {n:aH} (a:∑j,n j=0) (x:aC):
  B x (fQ n u)=∑i,(u i- ∑k,u k)*cG n x i:=by
 have c:aS (fQ n u)=0:=pC u a;have b (i:Fin 4) (j:Fin 5):gQ (fQ n u) (i,j)=(u i- ∑k,u k)*n j:=by simp only[gQ,c];simp[gR,gC,fQ,←Finset.mul_sum,←Finset.sum_mul,a,sub_mul]
 rw[sY,←aEp];simp only[kK,b,cG,Finset.mul_sum,mul_assoc]
def mD (v:V 3):V 4:= ![v 0,v 1,v 2,-(v 1)-v 2]
def aHo:V 3→ₗ[ℂ] V 4 where
 toFun:=mD
 map_add' a b:=by funext i;fin_cases i<;>simp[mD];ring
 map_smul' c a:=by funext i;fin_cases i<;>simp[mD];ring
def aGd (n:aH):V 3→ₗ[ℂ] aC:=(fQ n).comp aHo
def gU (ω:ℂ) (v:V 2):V 4:= ![v 0,v 1,ω*v 1,(-1-ω)*v 1]
def aGo (ω:ℂ):V 2→ₗ[ℂ] V 4 where
 toFun:=gU ω
 map_add' a b:=by funext i;fin_cases i<;>simp[gU]<;>ring
 map_smul' c a:=by funext i;fin_cases i<;>simp[gU]<;>ring
def aDb (n:aH) (ω:ℂ):V 2→ₗ[ℂ] aC:=(fQ n).comp (aGo ω)
lemma yQ {L:Submodule ℂ aC} (hL:aD L) {k:ℕ} (f:V k→ₗ[ℂ] aC)
  (c:Function.Injective f) (i:∀v,cW (f v)=0)
  (e:∀v w,B (f v) (f w)=0) (g:∀x∈L,∀v,B x (f v)=0):
  aX L+k≤9+Module.finrank ℂ (L.comap f):=by
 have b:=A6.nO hL (LinearMap.range f)
  (by rintro _ ⟨v,rfl⟩;exact i v)
  (by rintro _ ⟨v,rfl⟩ _ ⟨w,rfl⟩;exact e v w)
  (by rintro x l _ ⟨v,rfl⟩;exact g x l v)
 have d:(L.comap f).map f=L⊓LinearMap.range f:=by
  ext z;constructor
  ·rintro⟨u,j,rfl⟩;exact⟨j,⟨u,rfl⟩⟩
  ·rintro⟨m,⟨v,rfl⟩⟩;exact⟨v,m,rfl⟩
 have a:=(Submodule.equivMapOfInjective f c (L.comap f)).finrank_eq;rw[d] at a;have h:aX (LinearMap.range f)=k:=by rw[aX,LinearMap.finrank_range_of_inj c];exact Module.finrank_fin_fun ℂ
 rw[h] at b;exact b.trans_eq (congrArg (9+·) a.symm)
set_option maxHeartbeats 1200000 in
lemma aCg {L:Submodule ℂ aC} (hL:aD L) {n:aH} (q:n≠0)
  (b:∑j,n j=0) (s:rJ n=0) (c:e3 n≠0)
  (g:∀x∈L,∀i:Fin 4,i≠0→cG n x i=0):
  aX L≤7:=by
 let f:=aGd n
 have p:Function.Injective f:=by intro v w h;have e:mD v=mD w:=yP q h;funext k;fin_cases k<;>first | exact congrFun e 0 | exact congrFun e 1 | exact congrFun e 2
 have d:=yQ hL f p (fun v=>pC (mD v) b)
  (by intro v w;change B (fQ n (mD v)) (fQ n (mD w))=0
      simp[mU _ b,rK,s])
  (by
    intro x l v;change B x (fQ n (mD v))=0;rw[mU _ b];simp[Fin.sum_univ_four,mD,g x l 1 (by decide),g x l 2 (by decide),g x l 3 (by decide)])
 have r:∀v∈L.comap f,jV v=0:=by intro v t;have m:=(cT hL (show f v∈L from t)).2.2.1;change pR (fQ n (mD v))=0 at m;have a:6*e3 (mD v)*e3 n=0:=(aB1 (mD v) n).symm.trans m;have h:=(mul_eq_zero.mp a).resolve_right c;rw[aDj];exact(mul_eq_zero.mp h).resolve_left (by norm_num)
 have o:aX L+3≤9+1:=d.trans (Nat.add_le_add_left (sA _ r) 9);omega
set_option maxHeartbeats 1200000 in
lemma xW {L:Submodule ℂ aC} (hL:aD L) {n:aH} (q:n≠0)
  (e:∑j,n j=0) (t:rJ n≠0)
  (b:∀x∈L,∀i:Fin 4,i≠0→cG n x i=0) (y:u L 0=0):aX L≤7:=by
 obtain⟨r,s⟩:=IsAlgClosed.exists_pow_nat_eq (-3:ℂ) (n:=2) (by norm_num);obtain⟨ω,hω⟩:∃ω:ℂ,ω^2+ω+1=0:=⟨(-1+r)/2,by linear_combination s/4⟩
 let f:=aDb n ω
 have a:Function.Injective f:=by intro v w h;have o:gU ω v=gU ω w:=yP q h;funext k;fin_cases k<;>first | exact congrFun o 0 | exact congrFun o 1
 have g:=yQ hL f a (fun v=>pC (gU ω v) e)
  (by
    intro v w;change B (fQ n (gU ω v)) (fQ n (gU ω w))=0;rw[mU _ e];simp[rK,Fin.sum_univ_four,gU];linear_combination 2*v 1*w 1*rJ n*hω)
  (by
    intro x m v;change B x (fQ n (gU ω v))=0;rw[mU _ e];simp[Fin.sum_univ_four,gU,b x m 1 (by decide),b x m 2 (by decide),b x m 3 (by decide)];ring_nf;simp)
 have p:L.comap f= ⊥ :=by
  apply le_antisymm ?_ bot_le;intro v z;change v=0;have d:f v∈L:=z;have l:=b _ d 1 (by decide);change cG n (fQ n (gU ω v)) 1=0 at l;rw[rK] at l;have A:v 1=0:=(mul_eq_zero.mp l).resolve_right t;have c:f v∈aZ L 0:=by simp only[aZ,Submodule.mem_inf,Submodule.mem_iInf,LinearMap.mem_ker];refine⟨d,?_⟩;intro⟨i,a⟩;funext j;fin_cases i<;>first | exact(a rfl).elim | simp[f,aDb,aGo,fQ,gU,A,row]
  rw[Submodule.finrank_eq_zero.mp y] at c;have C:f v=0:=by simpa only[Submodule.mem_bot] using c
  exact a (by simpa only[map_zero] using C)
 rw[p,finrank_bot] at g;omega
end Ac.A1
namespace Ac.A1
open Aa At Ae Ad An
lemma aDu {L:Submodule ℂ aC} (hL:aD L) {n:aH} (f:n≠0)
  (e:∑j,n j=0) (l:rJ n≠0∨e3 n≠0) {r:Fin 4}
  (o:∀x∈L,∀i:Fin 4,i≠r→cG n x i=0) (p:u L r=0):
  aX L≤7:=by
 let ρ:=Equiv.swap 0 r
 let M:=L.map (re ρ 1)
 have d:aD M:=gI ρ 1 hL;have g:ρ 0=r:=Equiv.swap_apply_left 0 r;have b (x:aC) (q:x∈M) (i:Fin 4) (m:i≠0):cG n x i=0:=by obtain⟨y,s,rfl⟩:=q;exact o y s (ρ i) (fun k=>m (ρ.injective (k.trans g.symm)))
 have h:u M 0=0:=(aF4 ρ L 0).trans (by rw[g,p]);have a:aX M≤7:=by
  by_cases c:rJ n=0
  ·exact aCg d f e c (l.resolve_left (not_ne_iff.mpr c)) b
  ·exact xW d f e c b h
 exact(nL ρ 1 L).symm.le.trans a
lemma tU {L:Submodule ℂ aC} (hL:aD L) (d:aX L=8)
  (b:∀i,u L i=0) (a:∀i j,i≠j→p L i j≤6):
  ∃i j:Fin 4,i≠j∧aE L i=4∧aE L j=4:=by
 by_contra h;obtain⟨n,g,o,_,s,q⟩:=tT hL d b a h;have e:∃r:Fin 4,∀i,i≠r→aE L i≤3:=by
  by_cases m:∃r,aE L r=4
  ·obtain⟨r,k⟩:=m;refine⟨r,fun i f=> ?_⟩;have l:=(fG hL d b a i).2;have g:aE L i≠4:=fun c=>h ⟨i,r,f,c,k⟩
   omega
  ·refine⟨0,fun i _=> ?_⟩;have l:=(fG hL d b a i).2;have g:aE L i≠4:=fun c=>m ⟨i,c⟩
   omega
 obtain⟨r,k⟩:=e;have t (x:aC) (v:x∈L) (i:Fin 4) (f:i≠r):cG n x i=0:=s i (k i f) (Submodule.mem_sup_left (Submodule.mem_map_of_mem v:row i x∈bN L i));have l:=aDu hL g o q t (b r);omega
end Ac.A1
namespace Ac.Bb
open LinearMap Matrix Aa Ae An Ap
abbrev U:=Fin 3→ℂ
abbrev aFl:=Matrix (Fin 5) (Fin 5) ℂ
def Cls (W:Submodule ℂ (aH×aH)) (Z:aFl):Prop:=Z.IsSymm∧(∀i,Z i i=0)∧∀x y,(x,y)∈W→Z.toBilin' x y=0
lemma aFm (P Q:aH→ₗ[ℂ] U) (l r:U→ₗ[ℂ] aH)
  (b:∀z,P (l z)=z) (c:∀z,Q (r z)=z)
  (B:LinearMap.BilinForm ℂ aH) (h:∀x y,P x= Q y→B x y=0):
  (B.comp l r).IsAlt∧∀x y,B x y=B.comp l r (P x) (Q y):=by
 have a:(B.comp l r).IsAlt:=fun z=>h _ _ ((b z).trans (c z).symm)
 refine⟨a,fun x y=> ?_⟩;have d:=h (x+l (Q y)) (r (P x)+y) (by simp[b,c]);rw[map_add,map_add,LinearMap.add_apply,LinearMap.add_apply,h x _ (c _).symm,h _ y (b _),zero_add,add_zero] at d;exact(eq_neg_of_add_eq_zero_right d).trans (a.neg_eq (Q y) (P x))
lemma aHp (p q:U) (d:∀c:ℂ,c•q≠p):
  ∃(b:Module.Basis (Fin 3) ℂ U) (c:ℂ),b 2=p∧q=c•b 1:=by
 have i:Module.finrank ℂ U=3:=by simp
 obtain⟨v,c,f,a⟩:∃(v:U) (c:ℂ),LinearIndependent ℂ ![v,p]∧q=c•v:=by
  by_cases a:q=0
  ·obtain⟨v,g⟩:=exists_linearIndependent_pair_of_one_lt_finrank (R:=ℂ)
    (show 1<Module.finrank ℂ U by omega) (x:=p) (by simpa using(d 0).symm)
   exact⟨v,0,LinearIndependent.pair_symm_iff.mp g,by simpa using a⟩
  ·exact⟨q,1,(LinearIndependent.pair_iff' a).mpr d,by simp⟩
 obtain⟨w,h⟩:=exists_linearIndependent_cons_of_lt_finrank f
  (show 2<Module.finrank ℂ U by omega)
 let b:=basisOfLinearIndependentOfCardEqFinrank h (by simp)
 have e: ⇑b=Fin.cons w ![v,p]:=coe_basisOfLinearIndependentOfCardEqFinrank ..;exact⟨b,c,congrFun e 2,a.trans (congrArg (c• ·) (congrFun e 1).symm)⟩
lemma zT (W:Submodule ℂ (aH×aH)) (hd:Module.finrank ℂ W=7)
  (hx:∀x:aH,∃y,(x,y)∈W) (hy:∀y:aH,∃x,(x,y)∈W)
  (i:F) (hi:∀c:ℂ,(Pi.single i 1,c•Pi.single i 1)∉W):
  ∃
   G:aFl,∀Z,Cls W Z→
   (∃c:ℂ,Z=c•G)∧∀i j k,Z i j*Z j k*Z k i=0:=by
 have C:=W.finrank_quotient_add_finrank;rw[hd,Module.finrank_prod,Module.finrank_fin_fun] at C
 let e:((aH×aH) ⧸ W)≃ₗ[ℂ] U:=LinearEquiv.ofFinrankEq _ _ (by rw[Module.finrank_fin_fun];omega)
 have H (z:aH×aH):W.mkQ z=0↔z∈W:=Submodule.Quotient.mk_eq_zero W
 let P:aH→ₗ[ℂ] U:=e.toLinearMap∘ₗ W.mkQ∘ₗ inl ℂ _ _
 let Q:aH→ₗ[ℂ] U:= -(e.toLinearMap∘ₗ W.mkQ∘ₗ inr ℂ _ _)
 have hP:Function.Surjective P:=fun t=>by obtain⟨⟨a,b⟩,hab⟩:=W.mkQ_surjective (e.symm t);obtain⟨c,o⟩:=hy b;refine⟨a-c,?_⟩;change e (W.mkQ (a-c,0))=t;rw[show((a-c,0):aH×aH)=(a,b)-(c,b) by simp,map_sub,hab,(H _).2 o];simp
 have hQ:Function.Surjective Q:=fun t=>by obtain⟨⟨a,b⟩,hab⟩:=W.mkQ_surjective (e.symm t);obtain⟨c,o⟩:=hx a;refine⟨c-b,?_⟩;change-e (W.mkQ (0,c-b))=t;rw[show((0,c-b):aH×aH)=(a,c)-(a,b) by simp,map_sub,hab,(H _).2 o];simp
 have w (x y:aH):(x,y)∈W↔P x= Q y:=by change _↔e (W.mkQ (x,0))= -e (W.mkQ (0,y));rw[←map_neg,e.injective.eq_iff,←H,eq_neg_iff_add_eq_zero,←map_add];simp
 obtain⟨l,O⟩:=P.exists_rightInverse_of_surjective (range_eq_top.mpr hP);obtain⟨r,V⟩:= Q.exists_rightInverse_of_surjective (range_eq_top.mpr hQ);have hl (z:U):P (l z)=z:=congr($O z);have E (z:U):Q (r z)=z:=congr($V z);obtain⟨b,c,R,T⟩:=aHp (P (Pi.single i 1)) (Q (Pi.single i 1)) fun c q=>hi c ((w _ _).mpr (by simpa using q.symm))
 have aAr (Z:aFl) (m:Cls W Z):(∀i j k,Z i j*Z j k*Z k i=0)∧
   (Z.toBilin' (l (b 1)) (r (b 0))=0→Z=0):=by
  obtain⟨s,d,h⟩:=m;obtain⟨n,p⟩:=aFm P Q l r hl E Z.toBilin' fun x y e=>h x y ((w x y).mpr e)
  change _∧(Z.toBilin'.comp l r (b 1) (b 0)=0→_)
  generalize Z.toBilin'.comp l r=S at n p
  constructor
  ·intro i j k
   let A:Matrix (Fin 3) (Fin 3) ℂ:=S.toMatrix'
   have q:=A.det_transpose;rw[show Aᵀ= -A from Matrix.ext fun i j=>(n.neg_eq _ _).symm,det_neg] at q;change(-1:ℂ)^3*A.det=A.det at q;have hB:Z.toBilin'=S.comp P Q:=LinearMap.BilinForm.ext p;have m:Z=P.toMatrix'ᵀ*A*Q.toMatrix':=
    (LinearMap.BilinForm.toMatrix'_toBilin' Z).symm.trans
      ((congrArg _ hB).trans (S.toMatrix'_comp P Q))
   let f:= ![i,j,k]
   have u:(Z.submatrix f f).det=0:=by rw[m];change(P.toMatrix'ᵀ.submatrix f id*A*Q.toMatrix'.submatrix id f).det=0;rw[det_mul,det_mul,show A.det=0 by linear_combination-q/2];simp
   simp only[det_fin_three,submatrix_apply,f,cons_val_zero,cons_val_one,cons_val_two,d,mul_zero,zero_mul,zero_add,sub_zero] at u;change Z i j*Z j k*Z k i+Z i k*Z j i*Z k j=0 at u;rw[s.apply i j,s.apply j k,s.apply k i] at u;linear_combination u/2
  ·intro J;have B (x:aH):S (b 2) (Q x)=S (P x) (c•b 1):=by
    rw[R,←T,←p,←p,(isSymm_toBilin'_iff_isSymm.mpr s).eq]
   have K:S (b 2) (b 1)=0:=by
    by_cases o:c=0
    ·simpa[E,o] using B (r (b 1))
    ·have kH:=(p _ _).symm.trans ((toBilin'_single Z i i).trans (d i));rw[←R,T,map_smul,smul_eq_mul] at kH;exact(mul_eq_zero.mp kH).resolve_left o
   have hv:S (b 1)=0:=b.ext fun i=>by
    fin_cases i
    ·exact J
    ·exact n.self_eq_zero _
    ·exact(n.neg_eq _ _).symm.trans (by simp[K])
   have a0:S (b 2) (b 0)=0:=by have N:=B (r (b 0));rw[E,map_smul,←n.neg_eq (b 1),hv] at N;simpa using N
   have v:S=0:=LinearMap.ext_basis b b fun i j=>by
    change S (b i) (b j)=0;fin_cases i<;>fin_cases j<;>first
     | exact n.self_eq_zero _
     | assumption
     | rwa [←n.neg_eq,neg_eq_zero]
   exact toBilin'.injective (BilinForm.ext fun x y=>by simp[p,v])
 by_cases M:∃G,Cls W G∧G.toBilin' (l (b 1)) (r (b 0))≠0
 ·obtain⟨G,⟨s,d,h⟩,g⟩:=M;refine⟨G,fun Z m=>⟨⟨_,sub_eq_zero.1 ((aAr
   (Z-(Z.toBilin' (l (b 1)) (r (b 0))/G.toBilin' (l (b 1)) (r (b 0)))•G)
   ⟨m.1.sub (s.smul _),by simp[d,m.2.1],fun x y X=>by
     simp[h x y X,m.2.2 x y X]⟩).2 (by simp[g]))⟩,(aAr Z m).1⟩⟩
 ·exact⟨0,fun Z m=>⟨⟨0,by simpa using(aAr Z m).2 (by_contra fun g=>M ⟨Z,m,g⟩)⟩,(aAr Z m).1⟩⟩
lemma yR {L:Submodule ℂ aC} (hL:aD L)
  {i:Fin 4} (b:aE L i=4) (j:Fin 4) (x:aH):
  ∃
   t∈L,∃c:ℂ,row i t+c•(1:aH)=x∧
   (row i t+c•(1:aH),row j t+c•(1:aH))∈bU L i j∧
   (row j t+c•(1:aH),row i t+c•(1:aH))∈bU L j i:=by
 have f:x∈aY L i:=by rw[Submodule.eq_top_of_finrank_eq (S:=aY L i) (by rw[cV hL,b];simp)];trivial
 obtain⟨_,⟨t,a,rfl⟩,v,d,e⟩:=Submodule.mem_sup.mp f;obtain⟨c,rfl⟩:=Submodule.mem_span_singleton.mp d;exact⟨t,a,c,e,
  Submodule.mem_sup.mpr ⟨_,⟨t,a,rfl⟩,_,Submodule.mem_span_singleton.mpr ⟨c,rfl⟩,rfl⟩,
  Submodule.mem_sup.mpr ⟨_,⟨t,a,rfl⟩,_,Submodule.mem_span_singleton.mpr ⟨c,rfl⟩,rfl⟩⟩
lemma aDv {L:Submodule ℂ aC} (hL:aD L) {i j:Fin 4} (e:i≠j):
  ∃k:F,∀c:ℂ,(Pi.single k 1,c•Pi.single k 1)∉bU L i j:=by
 obtain⟨f,b,d⟩:=jM hL i;obtain⟨k,r⟩:=Aa.vG f b;refine⟨k,fun c q=> ?_⟩;obtain⟨s,t,n,o,u⟩:=gP q;have a:=Ap.gZ b (d t n) s;rw[o] at a;have p:=cD (aM s t) i j e (by
  intro l m g;change row i (aM s t) l*row j (aM s t) m+row i (aM s t) m*row j (aM s t) l=0;rw[o,u];by_cases h:l=k
  ·subst l;simp[g.symm]
  ·simp[Pi.single_apply,h])
 rw[bR hL n] at p;exact mul_ne_zero (by norm_num) (pow_ne_zero 4 (a▸r)) p
lemma aG0 {L:Submodule ℂ aC} (hL:aD L) (o:p L 0 1=6)
  (g:aE L 0=4) (l:aE L 1=4):
  ∃
   G:aFl,∀a b:aH,bD 0 0 a b∈L→
   (∃c:ℂ,dL a b=c•G)∧∀i j k:F,
     dL a b i j*dL a b j k*dL a b k i=0:=by
 let ρ:Equiv.Perm (Fin 4):=Equiv.swap 0 2*Equiv.swap 1 3
 let M:=L.map (Ad.re ρ 1)
 have d:=Ad.gI ρ 1 hL;have f (i:Fin 4):aE M i=aE L (ρ i):=by unfold aE bN M;rw[←Submodule.map_comp];rfl
 obtain⟨k,n⟩:=aDv d (by decide:(2:Fin 4)≠3);obtain⟨G,m⟩:=zT (bU M 2 3)
  (by rw[gO d,(aGt ρ L 2 3).trans o])
  (fun x=>by
    obtain⟨t,e,c,rfl,h,-⟩:=yR d ((f 2).trans g) 3 x;exact⟨_,h⟩)
  (fun x=>by
    obtain⟨t,e,c,rfl,-,h⟩:=yR d ((f 3).trans l) 2 x;exact⟨_,h⟩) k n
 refine⟨G,fun a b q=>m _ ⟨Matrix.IsSymm.ext fun i j=> ?_,fun i=>by simp[dL],fun x y u=> ?_⟩⟩
 ·simp[dL,eq_comm,and_left_comm,and_comm,and_assoc]
 ·obtain⟨s,t,e,v,w⟩:=gP u;subst v w;refine(Matrix.toBilin'_apply (dL a b:aFl) _ _).trans
   (rR d (a:=a) (b:=b) ⟨_,q,?_⟩ ⟨t,e,rfl⟩)
  funext ⟨r,c⟩;fin_cases r<;>rfl
end Ac.Bb
namespace Ac.A0
open Aa Ac.An Ac.Ae
open Finset
abbrev E:=Ai.E
def wS:(Fin 4→aH)→ₘₗ[ℂ] ℂ:=
 ∑
  e:Fin 4 ↪ Fin 5,
  (MultilinearMap.mkPiAlgebra ℂ (Fin 4) ℂ).compLinearMap
    (fun i=>LinearMap.proj (e i))
lemma wT (v:Fin 4→aH):
  wS v=aO (fun p=>v p.1 p.2):=by
 simp[wS,aO]
def aFn:((Fin 1→E)→ₘₗ[ℂ] ℂ)→ₗ[ℂ] (E→ₗ[ℂ] ℂ) where
 toFun M:=M.toLinearMap 0 0
 map_add' _ _:=rfl
 map_smul' _ _:=rfl
def aFo:
  ((Fin 2→E)→ₘₗ[ℂ] ℂ)→ₗ[ℂ] (E→ₗ[ℂ] E→ₗ[ℂ] ℂ) where
 toFun M:=aFn.comp M.curryLeft
 map_add' _ _:=rfl
 map_smul' _ _:=rfl
def aGp (M:(Fin 3→E)→ₘₗ[ℂ] ℂ):Ai.iA:=aFo.comp M.curryLeft
lemma aA9 (M:(Fin 3→E)→ₘₗ[ℂ] ℂ) (a b c:E):
  aGp M a b c=M ![a,b,c]:=by
 change M (Fin.cons a (Fin.cons b (Function.update 0 0 c)))=_;congr 1;funext i;fin_cases i<;>simp
def dU (f:Fin 4→(E→ₗ[ℂ] aH)) (r:Fin 4) (v:aH):
  Ai.iA:=
 aGp ((wS.curryMid r v).compLinearMap (fun j=>f (r.succAbove j)))
lemma pD (f:Fin 4→(E→ₗ[ℂ] aH)) (r:Fin 4)
  (v:aH) (a b c:E):
  dU f r v a b c=aO (fun p=>Fin.insertNth (α:=fun _=>aH) r v (fun j:Fin 3=>f (r.succAbove j) (![a,b,c] j)) p.1 p.2):=by
 rw[dU,aA9,MultilinearMap.compLinearMap_apply];exact wT _
def jA (Y W:aC) (i:Fin 4):aC:=fun p=>Function.update (fun r=>row r W) i (row i Y) p.1 p.2
def zU (g:ℂ→ℂ):ℂ:=(g 2-g (-2)-2*(g 1-g (-1)))/12
lemma xX (Y W:aC):
  aO (jA Y W 3)+aO (jA Y W 2)+aO (jA Y W 1)+aO (jA Y W 0)=zU (fun t=>aO (Y+t•W)):=by
 let g (t:ℂ) (e:Fin 4 ↪ Fin 5):=∏i,(Y+t•W) (i,e i)
 let m (r:Fin 4) (e:Fin 4 ↪ Fin 5):=∏i,jA Y W r (i,e i)
 have a (t:ℂ):(∑e,g t e)=aO (Y+t•W):=rfl;have b (r:Fin 4):(∑e,m r e)=aO (jA Y W r):=rfl;have one (e:Fin 4 ↪ Fin 5):
   m
    3 e+m 2 e+m 1 e+m 0 e=
    (g 2 e-g (-2) e-2*(g 1 e-g (-1) e))/12:=by
  simp(config:={decide:=true}) only[m,g,jA,Fin.prod_univ_four,
   Function.update_apply,ite_true,ite_false,row,LinearMap.funLeft_apply,
   Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  ring
 simp only[zU,←b,←a,←sum_add_distrib];simp only[one,div_eq_mul_inv,←sum_mul,sum_sub_distrib,←mul_sum]
def bW (f:Fin 4→(E→ₗ[ℂ] aH)) (z:Fin 4→E):aC:=fun p=>f p.1 (z p.1) p.2
lemma wU (f:Fin 4→(E→ₗ[ℂ] aH)) (r:Fin 4)
  (Y:aC) (z:Fin 4→E):
  dU f r (row r Y) (z (r.succAbove 0)) (z (r.succAbove 1)) (z (r.succAbove 2))=aO (jA Y (bW f z) r):=by
 rw[pD];congr 1;funext ⟨i,k⟩;have h:(fun j:Fin 3=>f (r.succAbove j)
   (![z (r.succAbove 0),z (r.succAbove 1),z (r.succAbove 2)] j))=
   r.removeNth (fun i=>row i (bW f z)):=by
  funext j;fin_cases j<;>rfl
 rw[h,Fin.insertNth_removeNth];rfl
lemma tV {L:Submodule ℂ aC} (hL:aD L)
  (f:Fin 4→(E→ₗ[ℂ] aH))
  (k:∀z:Fin 4→E,(∑i,z i)=0→
    (fun p:Fin 4×Fin 5=>f p.1 (z p.1) p.2)∈L)
  (s:ℂ) {u:aC} (l:u∈L) (r:Fin 4):
  dU f r (row r (aM s u))=0:=by
 let Y:=aM s u
 let T (r:Fin 4):=dU f r (row r Y)
 have b (z:Fin 4→E) (hz:(∑i,z i)=0):
   T
    3 (z 0) (z 1) (z 2)+T 2 (z 0) (z 1) (z 3)+
    T 1 (z 0) (z 2) (z 3)+T 0 (z 1) (z 2) (z 3)=0:=by
  have h (t:ℂ):aO (Y+t•bW f z)=120*s^4:=by
   have e:Y+t•bW f z=aM s (u+t•bW f z):=by funext p;simp[Y,aM,add_assoc]
   rw[e];exact bR hL (L.add_mem l (L.smul_mem t (k z hz))) s
  have e (r:Fin 4):=wU f r Y z;have e3:T 3 (z 0) (z 1) (z 2)=aO (jA Y (bW f z) 3):=e 3;have e2:T 2 (z 0) (z 1) (z 3)=aO (jA Y (bW f z) 2):=e 2;have e1:T 1 (z 0) (z 2) (z 3)=aO (jA Y (bW f z) 1):=e 1;have a:T 0 (z 1) (z 2) (z 3)=aO (jA Y (bW f z) 0):=e 0;rw[e3,e2,e1,a,xX];simp only[zU,h,sub_self,mul_zero,zero_div]
 obtain⟨j,g,d,c⟩:=Ai.rZ (T 3) (T 2) (T 1) (T 0) b;change T r=0;fin_cases r
 ·exact c
 ·exact d
 ·exact g
 ·exact j
lemma gG {L:Submodule ℂ aC} (hL:aD L)
  (f:Fin 4→((Fin 2→ℂ)→ₗ[ℂ] aH))
  (g:∀z:Fin 4→(Fin 2→ℂ),(∑i,z i)=0→
    (fun p:Fin 4×Fin 5=>f p.1 (z p.1) p.2)∈L)
  {r:Fin 4} {v:aH} (l:v∈aY L r) (z:Fin 3→(Fin 2→ℂ)):
  aO (fun p=>Fin.insertNth (α:=fun _=>aH) r v (fun j:Fin 3=>f (r.succAbove j) (z j)) p.1 p.2)=0:=by
 obtain⟨a,c,b,d,hab⟩:=Submodule.mem_sup.mp l;obtain⟨u,h,rfl⟩:=c;obtain⟨s,rfl⟩:=Submodule.mem_span_singleton.mp d;have e:row r (aM s u)=v:=by rw[←hab];funext k;change s+u (r,k)=u (r,k)+s*1;ring
 have m: ![z 0,z 1,z 2]=z:=by funext j;fin_cases j<;>rfl
 have H:=congrArg (fun T:Ai.iA=>T (z 0) (z 1) (z 2)) (tV hL f g s h r);simpa only[pD,m,e,LinearMap.zero_apply] using H
lemma eG {L:Submodule ℂ aC} (hL:aD L)
  (f:Fin 4→((Fin 2→ℂ)→ₗ[ℂ] aH))
  (b:∀z:Fin 4→(Fin 2→ℂ),(∑i,z i)=0→
    (fun p:Fin 4×Fin 5=>f p.1 (z p.1) p.2)∈L)
  {r:Fin 4} (c:aE L r=4) (v:aH) (z:Fin 3→(Fin 2→ℂ)):
  aO (fun p=>Fin.insertNth (α:=fun _=>aH) r v (fun j:Fin 3=>f (r.succAbove j) (z j)) p.1 p.2)=0:=by
 apply gG hL f b _ z;have a:aY L r= ⊤ :=by apply Submodule.eq_top_of_finrank_eq;rw[cV hL,c];simp[aH]
 rw[a];trivial
lemma tW {L:Submodule ℂ aC} (hL:aD L)
  (f:Fin 4→((Fin 2→ℂ)→ₗ[ℂ] aH))
  (e:∀z:Fin 4→(Fin 2→ℂ),(∑i,z i)=0→
    (fun p:Fin 4×Fin 5=>f p.1 (z p.1) p.2)∈L)
  (d:aE L 0=4) (v:aH) (a b c:Fin 2→ℂ):
  aO (bD v (f 1 a) (f 2 b) (f 3 c))=0:=by
 have H:=eG hL f e d v ![a,b,c];convert H using 2;funext ⟨i,k⟩;fin_cases i<;>rfl
lemma tX {L:Submodule ℂ aC} (hL:aD L)
  (f:Fin 4→((Fin 2→ℂ)→ₗ[ℂ] aH))
  (e:∀z:Fin 4→(Fin 2→ℂ),(∑i,z i)=0→
    (fun p:Fin 4×Fin 5=>f p.1 (z p.1) p.2)∈L)
  (d:aE L 1=4) (v:aH) (a b c:Fin 2→ℂ):
  aO (bD (f 0 a) v (f 2 b) (f 3 c))=0:=by
 have H:=eG hL f e d v ![a,b,c];convert H using 2;funext ⟨i,k⟩;fin_cases i<;>rfl
end Ac.A0
namespace Ac.As
open Aa Ac.An
abbrev E:=Fin 2→ℂ
abbrev lL:=Fin 4→E
abbrev kD:=Fin 4→E→ₗ[ℂ] aH
def sN (L:Submodule ℂ aC):Submodule ℂ aC:=(bS L 0⊔bS L 1).map L.subtype
def cM (f:kD) (z:lL):aC:=fun p=>f p.1 (z p.1) p.2
lemma aDc (L:Submodule ℂ aC):sN L≤L:=by rintro _ ⟨x,_,rfl⟩;exact x.property
lemma mV {L:Submodule ℂ aC} (m:aX L=8) (e:∀i,u L i=0)
  (d:∀i j,i≠j→p L i j≤6) {i:Fin 4} (o:aE L i=4):
  Module.finrank ℂ (bS L i)=4∧∀j,i≠j→Module.finrank ℂ (aJ L i j)=2:=by
 refine⟨by have h:=lU L i;omega,?_⟩;intro j a;obtain⟨k,c,b⟩:∃k:Fin 4,i≠k∧j≠k:=by clear* -i j;decide+revert
 have f:=bB e a c b;have g:=d i k c;have l:=d i j a;have n:=cA L i j;omega
lemma uW {L:Submodule ℂ aC} (d:aX L=8) (f:∀i,u L i=0)
  (e:∀i j,i≠j→p L i j≤6)
  (g:aE L 0=4) (h:aE L 1=4):
  Module.finrank ℂ (bS L 0)=4∧
  Module.finrank ℂ (bS L 1)=4∧
  Module.finrank ℂ (aJ L 0 1)=2∧aX (sN L)=6:=by
 obtain⟨b,k⟩:=mV d f e g;obtain⟨c,_⟩:=mV d f e h;have a:=k 1 (by decide);refine⟨b,c,a,?_⟩;have H:=Submodule.finrank_sup_add_finrank_inf_eq (bS L 0) (bS L 1);change _+Module.finrank ℂ (aJ L 0 1)=_ at H;rw[b,c,a] at H;change Module.finrank ℂ ((bS L 0⊔bS L 1).map L.subtype)=6;rw[Submodule.finrank_map_subtype_eq];omega
abbrev zV (L:Submodule ℂ aC) (r:Fin 4):L→ₗ[ℂ] aH:=(row r).comp L.subtype
abbrev bX (L:Submodule ℂ aC) (i j r:Fin 4):aJ L i j→ₗ[ℂ] aH:=(zV L r).comp (aJ L i j).subtype
lemma iO {L:Submodule ℂ aC} (d:∀i,u L i=0)
  {i j r:Fin 4} (a:i≠j) (b:i≠r) (c:j≠r):
  Function.Injective (bX L i j r):=by
 intro x y h
 let w:=x-y
 have e:row r w.val=0:=sub_eq_zero.mpr h;exact sub_eq_zero.mp (Subtype.ext (hV d a b c w.val w.property.1 w.property.2 e))
lemma wV {L:Submodule ℂ aC} (l:∀i,u L i=0)
  {i j k:Fin 4} (a:i≠j) (b:i≠k) (c:j≠k)
  (d:Module.finrank ℂ (bS L i)=4)
  (g:∀r,i≠r→Module.finrank ℂ (aJ L i r)=2):
  aJ L i j⊔aJ L i k=bS L i:=by
 have e:aJ L i j⊓aJ L i k= ⊥ :=by apply eq_bot_iff.mpr;intro x f;exact hV l a b c x f.1.1 f.1.2 f.2.2
 have h:=Submodule.finrank_sup_add_finrank_inf_eq (aJ L i j) (aJ L i k);rw[e,finrank_bot,g _ a,g _ b] at h;exact Submodule.eq_of_le_of_finrank_le (sup_le inf_le_left inf_le_left) (by omega)
lemma sO {L:Submodule ℂ aC} {i j:Fin 4}
  (h:aJ L i j⊔aJ L i 3=bS L i):
  LinearMap.range (bX L i j 3)=(bS L i).map (zV L 3):=by
 apply le_antisymm
 ·rintro _ ⟨x,rfl⟩;exact⟨x.val,x.property.1,rfl⟩
 ·rintro _ ⟨x,a,rfl⟩;rw[←h] at a;obtain⟨y,b,z,c,rfl⟩:=Submodule.mem_sup.mp a;refine⟨⟨y,b⟩,?_⟩;have e:zV L 3 z=0:=c.2;rw[map_add,e,add_zero];rfl
lemma aGq {A B:Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  (a:A→ₗ[ℂ] aH) (b:B→ₗ[ℂ] aH) (f:Function.Injective a) (g:Function.Injective b)
  (h:LinearMap.range a=LinearMap.range b):
  ∃e:A≃ₗ[ℂ] B,∀x,b (e x)=a x:=by
 let d:=LinearEquiv.ofInjective a f
 let c:=LinearEquiv.ofInjective b g
 let t:=LinearEquiv.ofEq _ _ h
 refine⟨(d.trans t).trans c.symm,fun x=> ?_⟩;change(c (c.symm (t (d x)))).val=_;rw[c.apply_symm_apply];rfl
lemma aDw (L:Submodule ℂ aC) (i j r:Fin 4):
  LinearMap.range (bX L i j r)=LinearMap.range (bX L j i r):=by
 ext x;constructor<;>rintro⟨y,rfl⟩<;>exact⟨⟨y.val,y.property.2,y.property.1⟩,rfl⟩
lemma zW {L:Submodule ℂ aC} (m:aX L=8) (f:∀i,u L i=0)
  (o:∀i j,i≠j→p L i j≤6) (t:aE L 0=4) (v:aE L 1=4):
  ∃
   (a:E≃ₗ[ℂ] aJ L 1 2) (b:E≃ₗ[ℂ] aJ L 0 2)
   (c:E≃ₗ[ℂ] aJ L 0 1),
   (∀x,bX L 1 2 3 (a x)=bX L 0 1 3 (c x))∧
   (∀x,bX L 0 2 3 (b x)=bX L 0 1 3 (c x)):=by
 obtain⟨r,q⟩:=mV m f o t;obtain⟨s,C⟩:=mV m f o v;have g (j:Fin 4) (h:(0:Fin 4)≠j) (e:j≠3):=sO (wV f h (by decide:(0:Fin 4)≠3) e r q);have k (j:Fin 4) (h:(1:Fin 4)≠j) (e:j≠3):=sO (wV f h (by decide:(1:Fin 4)≠3) e s C);have l:=q 1 (by decide)
 let _:Module.Free ℂ ↥(aJ L 0 1):=Module.Free.of_divisionRing ℂ ↥(aJ L 0 1)
 let c:E≃ₗ[ℂ] aJ L 0 1:=LinearEquiv.ofFinrankEq (R:=ℂ) E
  ↥(aJ L 0 1) (by rw[Module.finrank_fin_fun,l])
 have d (i j:Fin 4) (n:i≠j) (z:i≠3) (e:j≠3):=iO (L:=L) f n z e;obtain⟨a,w⟩:=aGq (A:= ↥(aJ L 0 1)) (B:= ↥(aJ L 1 2))
  (bX L 0 1 3) (bX L 1 2 3) (d 0 1 (by decide) (by decide) (by decide))
  (d 1 2 (by decide) (by decide) (by decide))
  ((aDw L 0 1 3).trans ((k 0 (by decide) (by decide)).trans (k 2 (by decide) (by decide)).symm))
 obtain⟨b,y⟩:=aGq (A:= ↥(aJ L 0 1)) (B:= ↥(aJ L 0 2))
  (bX L 0 1 3) (bX L 0 2 3) (d 0 1 (by decide) (by decide) (by decide))
  (d 0 2 (by decide) (by decide) (by decide))
  ((g 1 (by decide) (by decide)).trans (g 2 (by decide) (by decide)).symm)
 exact⟨c.trans a,c.trans b,c,fun x=>w (c x),fun x=>y (c x)⟩
lemma aBa {L:Submodule ℂ aC} (t:aX L=8) (d:∀i,u L i=0)
  (w:∀i j,i≠j→p L i j≤6) (l:aE L 0=4) (m:aE L 1=4):
  ∃
   f:kD,(∀i,Function.Injective (f i))∧
   (∀z:lL,∑i,z i=0→cM f z∈sN L)∧
   LinearMap.range (f 2)=LinearMap.range (bX L 0 1 2)∧
   LinearMap.range (f 3)=LinearMap.range (bX L 0 1 3):=by
 obtain⟨a,b,c,r,s⟩:=zW t d w l m
 let g:=(bX L 0 1 3).comp c.toLinearMap
 let f:kD:= ![(bX L 1 2 0).comp a.toLinearMap,(bX L 0 2 1).comp b.toLinearMap,(bX L 0 1 2).comp c.toLinearMap,-g]
 refine⟨f,?_,?_,?_,?_⟩
 ·intro i;fin_cases i
  ·exact(iO d (by decide) (by decide) (by decide)).comp a.injective
  ·exact(iO d (by decide) (by decide) (by decide)).comp b.injective
  ·exact(iO d (by decide) (by decide) (by decide)).comp c.injective
  ·intro x y v;exact c.injective (iO d (by decide) (by decide) (by decide) (neg_inj.mp v))
 ·intro z h
  let A:=a (z 0)
  let B:=b (z 1)
  let C:=c (z 2)
  have n:A.val.val∈sN L:=⟨A.val,Submodule.mem_sup_right A.property.1,rfl⟩
  have o:B.val.val∈sN L:=⟨B.val,Submodule.mem_sup_left B.property.1,rfl⟩
  have q:C.val.val∈sN L:=⟨C.val,Submodule.mem_sup_left C.property.1,rfl⟩
  have e (i:Fin 4):f i (z i)=row i A.val.val+row i B.val.val+row i C.val.val:=by
   fin_cases i
   ·change row 0 A.val.val=row 0 A.val.val+row 0 B.val.val+row 0 C.val.val;rw[show row 0 B.val.val=0 from B.property.1,show row 0 C.val.val=0 from C.property.1];simp
   ·change row 1 B.val.val=row 1 A.val.val+row 1 B.val.val+row 1 C.val.val;rw[show row 1 A.val.val=0 from A.property.1,show row 1 C.val.val=0 from C.property.2];simp
   ·change row 2 C.val.val=row 2 A.val.val+row 2 B.val.val+row 2 C.val.val;rw[show row 2 A.val.val=0 from A.property.2,show row 2 B.val.val=0 from B.property.2];simp
   ·change-(g (z 3))=bX L 1 2 3 A+bX L 0 2 3 B+g (z 2);rw[r (z 0),s (z 1)];change-(g (z 3))=g (z 0)+g (z 1)+g (z 2);rw[Fin.sum_univ_four] at h;rw[←map_add,←map_add,←map_neg];exact congrArg g (neg_eq_of_add_eq_zero_left h)
  have k:cM f z=A.val.val+B.val.val+C.val.val:=funext (fun p=>congrFun (e p.1) p.2);rw[k];exact(sN L).add_mem ((sN L).add_mem n o) q
 ·change LinearMap.range ((bX L 0 1 2).comp c.toLinearMap)=_;rw[LinearMap.range_comp,LinearEquiv.range,Submodule.map_top]
 ·change LinearMap.range (-g)=_;rw[LinearMap.range_neg,LinearMap.range_comp,LinearEquiv.range,Submodule.map_top]
lemma aCh {C:Submodule ℂ aC} (d:aX C=6) (f:kD)
  (o:∀i,Function.Injective (f i))
  (g:∀z:lL,∑i,z i=0→cM f z∈C) (x:aC):
  x∈C↔∃z:lL,∑i,z i=0∧x=cM f z:=by
 let P:=Fin 3→E
 let a (i:Fin 3):P→ₗ[ℂ] E:=LinearMap.proj i
 let q:Fin 4→P→ₗ[ℂ] E:= ![a 0,a 1,a 2,-(a 0+a 1+a 2)]
 let F:P→ₗ[ℂ] aC:=LinearMap.pi fun p=>(LinearMap.proj p.2).comp ((f p.1).comp (q p.1))
 have e (w:P):∑i,q i w=0:=by rw[Fin.sum_univ_four];exact add_neg_cancel _
 have m (w:P):F w=cM f (fun i=>q i w):=rfl;have k:Function.Injective F:=by intro v w h;funext i;have n:f i.castSucc (q i.castSucc v)=f i.castSucc (q i.castSucc w):=congrArg (row i.castSucc) h;have:=o i.castSucc n;fin_cases i<;>exact this
 have c:LinearMap.range F≤C:=by rintro _ ⟨w,rfl⟩;exact g _ (e w)
 have b:Module.finrank ℂ P=6:=by simp[P,E,Module.finrank_pi_fintype]
 have l:LinearMap.range F=C:=Submodule.eq_of_le_of_finrank_le c (by rw[LinearMap.finrank_range_of_inj k,b];exact d.le);constructor
 ·intro j;rw[←l] at j;obtain⟨w,rfl⟩:=j;exact⟨_,e w,m w⟩
 ·rintro⟨z,r,rfl⟩;exact g z r
lemma lG {L:Submodule ℂ aC} (c:aX L=8) (g:∀i,u L i=0)
  (e:∀i j,i≠j→p L i j≤6) (a:aE L 0=4) (b:aE L 1=4):
  ∃
   f:kD,(∀i,Function.Injective (f i))∧
   (∀x:aC,x∈sN L↔∃z:lL,∑i,z i=0∧x=cM f z)∧
   LinearMap.range (f 2)=LinearMap.range (bX L 0 1 2)∧
   LinearMap.range (f 3)=LinearMap.range (bX L 0 1 3):=by
 obtain⟨f,d,l,h,k⟩:=aBa c g e a b;exact⟨f,d,aCh (uW c g e a b).2.2.2 f d l,h,k⟩
lemma xY {L:Submodule ℂ aC} {f:kD} (d:∀i,Function.Injective (f i))
  (c:∀x:aC,x∈sN L↔∃z:lL,∑i,z i=0∧x=cM f z)
  (x:aC):
  (x∈L∧row 0 x=0∧row 1 x=0)↔
    ∃t:E,x=cM f ![0,0,t,-t]:=by
 constructor
 ·rintro⟨e,b,k⟩;have a:x∈sN L:=⟨⟨x,e⟩,
   Submodule.mem_sup_left (show(⟨x,e⟩:L)∈bS L 0 from b),rfl⟩
  obtain⟨z,g,rfl⟩:=(c x).mp a;have h:z 0=0:=d 0 (b.trans (map_zero (f 0)).symm);have j:z 1=0:=d 1 (k.trans (map_zero (f 1)).symm);rw[Fin.sum_univ_four,h,j,zero_add,zero_add] at g;have l:z 3= -z 2:=eq_neg_of_add_eq_zero_right g;refine⟨z 2,congrArg (cM f) (funext fun i=> ?_)⟩;fin_cases i
  ·exact h
  ·exact j
  ·rfl
  ·exact l
 ·rintro⟨t,rfl⟩;have a:=(c (cM f ![0,0,t,-t])).mpr ⟨_,by simp[Fin.sum_univ_four],rfl⟩;exact⟨aDc L a,map_zero (f 0),map_zero (f 1)⟩
lemma aCi {f:kD} (a:∀i,Function.Injective (f i)) (i:Fin 4):
  Module.finrank ℂ (LinearMap.range (f i))=2:=by
 rw[LinearMap.finrank_range_of_inj (a i),Module.finrank_fin_fun]
end Ac.As
namespace Ac.As
open Aa Ac.An Ac.Ae Matrix
lemma aDx (v x a b:aH):
  aO (bD v x a b)=aO (bD a b v x):=by
 let ρ:Equiv.Perm (Fin 4):=Equiv.swap 0 2*Equiv.swap 1 3
 have e:Ad.re ρ 1 (bD a b v x)=bD v x a b:=by funext ⟨i,j⟩;fin_cases i<;>rfl
 rw[←e,Ad.vS]
lemma aCj (v x a b:aH):
  aO (bD v x a b)=aO (bD x v a b):=by
 have e:Ad.re (Equiv.swap 0 1) 1 (bD x v a b)=bD v x a b:=by funext ⟨i,j⟩;fin_cases i<;>rfl
 rw[←e,Ad.vS]
lemma wW (a b x:aH) (h:∀v:aH,aO (bD v x a b)=0):
  Ag.dL a b*ᵥ x=0:=by
 funext k;have c:=h (Pi.single k 1);rw[aDx,gX] at c;change bil (Pi.single k 1) x (Ag.dL a b)=0 at c;rwa [jW,single_dotProduct,one_mul] at c
lemma nQ {L:Submodule ℂ aC} (hL:aD L) (f:kD)
  (g:∀x:aC,x∈sN L↔∃z:lL,∑i,z i=0∧x=cM f z)
  (d:aE L 0=4) (e:aE L 1=4) (a b:E) (x:aH)
  (h:x∈LinearMap.range (f 0)∨x∈LinearMap.range (f 1)):
  Ag.dL (f 2 a) (f 3 b)*ᵥ x=0:=by
 have c (z:lL) (j:∑i,z i=0):cM f z∈L:=aDc L ((g _).mpr ⟨z,j,rfl⟩);apply wW;intro v;rcases h with⟨t,rfl⟩|⟨t,rfl⟩
 ·rw[aCj];exact A0.tX hL f c e v t a b
 ·exact A0.tW hL f c d v t a b
lemma aBb {L:Submodule ℂ aC} (hL:aD L) (m:aX L=8)
  (o:∀i,u L i=0) (n:∀i j,i≠j→p L i j≤6)
  (c:aE L 0=4) (d:aE L 1=4):
  ∃
   f:kD,(∀i,Function.Injective (f i))∧
   (∀i,Module.finrank ℂ (LinearMap.range (f i))=2)∧
   (∀x:aC,x∈sN L↔∃z:lL,∑i,z i=0∧x=cM f z)∧
   LinearMap.range (f 2)=LinearMap.range (bX L 0 1 2)∧
   LinearMap.range (f 3)=LinearMap.range (bX L 0 1 3)∧
   ∀
    a b x:aH,a∈LinearMap.range (f 2)→b∈LinearMap.range (f 3)→
    x∈LinearMap.range (f 0)⊔LinearMap.range (f 1)→
    Ag.dL a b*ᵥ x=0:=by
 obtain⟨f,g,e,k,l⟩:=lG m o n c d;refine⟨f,g,aCi g,e,k,l,?_⟩;rintro _ _ _ ⟨a,rfl⟩ ⟨b,rfl⟩ h;obtain⟨x,q,y,r,rfl⟩:=Submodule.mem_sup.mp h;rw[Matrix.mulVec_add,nQ hL f e c d a b x (Or.inl q),nQ hL f e c d a b y (Or.inr r),add_zero]
lemma wX {L:Submodule ℂ aC} (hL:aD L) (f:aX L=8)
  (o:∀i,u L i=0) (n:∀i j,i≠j→p L i j≤6)
  {i j:Fin 4} (a:i≠j) (g:aE L i=4) (m:aE L j=4):
  ∃
   ρ:Equiv.Perm (Fin 4),ρ 0=i∧ρ 1=j∧
   let M:=L.map (Ad.re ρ 1)
   aD M∧aX M=8∧(∀k,u M k=0)∧(∀k l,k≠l→p M k l≤6)∧aE M 0=4∧aE M 1=4:=by
 obtain⟨σ,hσi,hσj⟩:=zD i j a
 let τ:Equiv.Perm (Fin 4):=Equiv.swap 0 2*Equiv.swap 1 3
 let ρ:=σ*τ
 have b:ρ 0=i:=hσi;have c:ρ 1=j:=hσj;have d (k:Fin 4):aE (L.map (Ad.re ρ 1)) k=aE L (ρ k):=by unfold aE bN;rw[←Submodule.map_comp];rfl
 refine⟨ρ,b,c,Ad.gI ρ 1 hL,(Ad.nL ρ 1 L).trans f,fun k=>(aF4 ρ L k).trans (o _),?_,?_,?_⟩
 ·intro k l h;rw[aGt];exact n _ _ (fun e=>h (ρ.injective e))
 ·rw[d,b,g]
 ·rw[d,c,m]
end Ac.As
namespace Ac.As
open Aa Ae Matrix
def wY (f:kD):E→ₗ[ℂ] aH:= -(f 3)
lemma aBc {L:Submodule ℂ aC} {f:kD} (b:∀i,Function.Injective (f i))
  (a:∀x:aC,x∈sN L↔∃z:lL,∑i,z i=0∧x=cM f z) (v:E):
  bD 0 0 (f 2 v) (wY f v)∈L:=by
 have h:=((xY b a (cM f ![0,0,v,-v])).mpr ⟨v,rfl⟩).1;have e:cM f ![0,0,v,-v]=bD 0 0 (f 2 v) (wY f v):=by funext ⟨r,c⟩;fin_cases r<;>simp[cM,bD,wY]
 rwa [e] at h
lemma aFp (f:F→ℂ):∑i,f i=f 0+f 1+f 2+f 3+f 4:=by simp[Fin.sum_univ_succ];ring
lemma wZ {L:Submodule ℂ aC} (hL:aD L) {a b:aH}
  (h:bD 0 0 a b∈L):cS a+cS b=0∧dQ a b=0:=by
 have c:=Ad.cT hL h;have d:cW (bD 0 0 a b)=cS a+cS b:=by simp[cW,bD,Fin.sum_univ_four,Finset.sum_add_distrib]
 have e:pQ (bD 0 0 a b)=dQ a b:=by
  simp(config:={decide:=true}) only[pQ,bD,dQ,aL,Fin.sum_univ_four,aFp,
   Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,
   Pi.zero_apply,ite_true,ite_false,zero_mul,mul_zero,add_zero,zero_add]
  ring
 exact⟨d.symm.trans c.1,e.symm.trans c.2.1⟩
end Ac.As
namespace Ac.Ba
open Aa Ae
lemma yS {a b:aH} (p:kS a b):
  ∃
   i j:F,j≠i∧a i≠0∧b i≠0∧cS a≠0∧
   ∀k,k≠i→k≠j→a k=0∧b k=0:=by
 rcases p with⟨i,c,d,_,e⟩|⟨i,j,h,c,_,d,_,e,_,l,_⟩
 ·obtain⟨j,g⟩:=exists_ne i;have z:cS a=a i:=Finset.sum_eq_single i (fun k _ f=>(e k f).1) (by simp);exact⟨i,j,g,c,d,fun h=>c (z.symm.trans h),fun k f _=>e k f⟩
 ·exact⟨i,j,h.symm,c,d,l,e⟩
lemma xZ (f:F→ℂ):∑i,f i=f 0+f 1+f 2+f 3+f 4:=by simp[Fin.sum_univ_succ];ring
lemma aFq (a b:aH):dQ a b=cS a*cS b- ∑i,a i*b i:=by simp(config:={decide:=true}) only[dQ,aL,cS,xZ,ite_true,ite_false,zero_add,add_zero];ring
end Ac.Ba
namespace Ac.A5
open Aa Ae
variable {P : Type*} [AddCommGroup P] [Module ℂ P]
def jA (a b c d:aH) (i j:F):ℂ:=aL a d i j+aL c b i j
lemma tY (a b:P→ₗ[ℂ] aH) (r s:P) (t:ℂ) (i j:F):
  aL (a (r+t•s)) (b (r+t•s)) i j=aL (a r) (b r) i j+t*jA (a r) (b r) (a s) (b s) i j+t^2*aL (a s) (b s) i j:=by
 simp[aL,jA];ring
lemma mW (a b:P→ₗ[ℂ] aH)
  (h:∃G:F→F→ℂ,∀x,∃t:ℂ,dL (a x) (b x)=t•G):
  ∃H:F→F→ℂ,∀x,∃t:ℂ,∀i j,i≠j→aL (a x) (b x) i j=t*H i j:=by
 obtain⟨G,d⟩:=h;refine⟨fun i j=>G i j-(∑k,G i k)/2-(∑k,G j k)/2+(∑k,∑l,G k l)/6,?_⟩;intro x;obtain⟨t,f⟩:=d x;refine⟨t,fun i j c=> ?_⟩;have e:=oG (a x) (b x) i j c;rw[f] at e;simp only[Pi.smul_apply,smul_eq_mul,←Finset.mul_sum] at e;linear_combination e/6
abbrev xA (a b:P→ₗ[ℂ] aH) (x:P):=∀i j:F,i≠j→aL (a x) (b x) i j=0
lemma aBd [FiniteDimensional ℂ P] (A:Module.finrank ℂ P=2)
  (a b:P→ₗ[ℂ] aH) (Q:Function.Injective a) (R:Function.Injective b)
  (U:∀x,cS (a x)+cS (b x)=0)
  (h:∃G:F→F→ℂ,∀x,∃t:ℂ,dL (a x) (b x)=t•G):
  ∃
   z:P,cS (a z)=0∧¬xA a b z∧∃r,r≠0∧xA a b r∧
   ∃t:ℂ,∀i j,i≠j→jA (a r) (b r) (a z) (b z) i j=t*aL (a z) (b z) i j:=by
 classical
 let f:P→ₗ[ℂ] ℂ:=∑i:F,(LinearMap.proj i).comp a
 obtain⟨z,J,S⟩:∃z,z≠0∧f z=0:=by
  by_contra! o;have O:Function.Injective f:=LinearMap.ker_eq_bot.mp
   (LinearMap.ker_eq_bot'.mpr (fun x Z=>by by_contra E;exact o x E Z))
  have d:=LinearMap.finrank_le_finrank_of_injective O;simp[A] at d
 have p:cS (a z)=0:=by simpa[cS,f,LinearMap.sum_apply] using S
 have q {l:P→ₗ[ℂ] aH} (T:Function.Injective l):l z≠0:=fun e=>J (T (e.trans l.map_zero.symm))
 obtain⟨i,j,c,N⟩:∃i j,i≠j∧aL (a z) (b z) i j≠0:=by by_contra! o;obtain⟨_,_,_,_,_,h,_⟩:=Ba.yS (gN (q Q) (q R) o (U z));exact h p
 obtain⟨H,M⟩:=mW a b h;obtain⟨s,w⟩:=M z;have E:s≠0:=by rintro rfl;exact N (by simpa using w i j c)
 have g (x:P):∃t:ℂ,∀k l,k≠l→aL (a x) (b x) k l=t*aL (a z) (b z) k l:=by obtain⟨t,V⟩:=M x;exact⟨t/s,fun k l u=>by rw[V k l u,w k l u,←mul_assoc,div_mul_cancel₀ _ E]⟩
 refine⟨z,p,fun h=>N (h i j c),?_⟩;obtain⟨v,X⟩:=exists_linearIndependent_pair_of_one_lt_finrank (by omega:1<Module.finrank ℂ P) J;have q (t:ℂ):v+t•z≠0:=by intro e;exact(LinearIndependent.pair_iff' J).mp X (-t) (by rw[neg_smul];exact(eq_neg_of_add_eq_zero_left e).symm)
 obtain⟨C,K⟩:=g v;obtain⟨D,y⟩:=g (v+z)
 let B:=D-C-1
 obtain⟨d,A⟩:=IsAlgClosed.exists_pow_nat_eq (B^2-4*C) (n:=2) (by norm_num)
 let r:=(-B+d)/2
 have m:xA a b (v+r•z):=by
  intro i j c;have e:=tY a b v z 1 i j;rw[one_smul,y i j c,K i j c] at e;rw[tY,K i j c];dsimp[B,r] at*
  linear_combination-((-(D-C-1)+d)/2)*e+aL (a z) (b z) i j*A/4
 obtain⟨D,y⟩:=g ((v+r•z)+z);refine⟨_,q r,m,D-1,fun i j c=> ?_⟩;have e:=tY a b (v+r•z) z 1 i j;rw[one_smul,y i j c,m i j c] at e;linear_combination-e
lemma zX {c d:aH} {i j:F} (a:i≠j)
  (b:∀k,k≠i→k≠j→c k=0∧d k=0) (e:dQ c d=0):
  ∀k l:F,k≠l→aL c d k l=0:=by
 have g:aL c d i j=0:=by simp(config:={decide:=true}) [dQ,aL,Fin.sum_univ_five] at e;fin_cases i<;>fin_cases j<;>norm_num[Fin.forall_fin_succ] at b a<;>grind only[aL]
 intro k l f;by_cases h:k=i<;>by_cases m:k=j<;>by_cases n:l=i<;>by_cases o:l=j<;>grind [aL]
def
    aFr (g : F → F → ℂ) := ∀ i j k : F, i ≠ j → j ≠ k → k ≠ i →
    g i j * g j k * g k i = 0
end Ac.A5
namespace Ac.A2
open Aa Ag Matrix
lemma yA (σ:Equiv.Perm (Fin 5)) {a b x:Row} (c:dL a b*ᵥ x=0):
  dL (a∘σ) (b∘σ)*ᵥ (x∘σ)=0:=by
 funext i
 let v:Row:=Pi.single i 1
 have e:Ad.re 1 σ (Ae.bD a b (v∘σ.symm) x)=
   Ae.bD (a∘σ) (b∘σ) v (x∘σ):=by
  funext ⟨r,j⟩;fin_cases r<;>first | rfl | exact congrArg v (σ.symm_apply_apply j)
 have h:=Ad.vS 1 σ (Ae.bD a b (v∘σ.symm) x);rw[e,Ae.gX,Ae.gX] at h;change Ae.bil v (x∘σ) (dL (a∘σ) (b∘σ))=Ae.bil (v∘σ.symm) x (dL a b) at h;rw[An.jW,An.jW] at h;simpa only[v,single_dotProduct,one_mul,c,dotProduct_zero,Pi.zero_apply] using h
end Ac.A2
namespace Ac.A2
open Aa Ag Matrix
lemma aCk {X:Submodule ℂ Row} (i:Fin 5)
  (h:∀x∈X,x i=0→x=0):Module.finrank ℂ X≤1:=by
 let f:=(LinearMap.proj (R:=ℂ) (φ:=fun _:Fin 5=>ℂ) i).comp X.subtype
 have a:Function.Injective f:=LinearMap.ker_eq_bot.mp
  (LinearMap.ker_eq_bot'.mpr (fun x b=>Subtype.ext (h x x.2 b)))
 simpa using LinearMap.finrank_le_finrank_of_injective a
set_option maxHeartbeats 3000000 in
lemma zY (a b c d x:Row) (t:ℂ)
  (K:a 0≠0) (hb:b 0≠0)
  (J:∀k,k≠0→k≠1→a k=0∧b k=0)
  (y:aL a b 0 1=0) (O:(∑j,a j)+(∑j,b j)=0)
  (N:∑j,a j≠0) (w:∑j,c j=0) (z:∑j,d j=0)
  (q:∑j,c j*d j=0) (M:c 2≠0∨d 2≠0)
  (m:∀i j:Fin 5,i≠j→aL a d i j+aL c b i j=t*aL c d i j)
  (kc:dL a d*ᵥ x=0) (kd:dL c b*ᵥ x=0) (ke:dL c d*ᵥ x=0)
  (h2:x 2=0):x=0:=by
 have U (i j:Fin 5) (h:i<j):=m i j h.ne;have C (i:Fin 5):=congrFun kc i;have D (i:Fin 5):=congrFun kd i;have E (i:Fin 5):=congrFun ke i;simp(config:={decide:=true}) [Fin.forall_fin_succ] at J;rcases J with⟨⟨a2,b2⟩,⟨a3,b3⟩,a4,b4⟩
 simp(config:={decide:=true}) [Fin.forall_fin_succ,Matrix.mulVec,dotProduct,Fin.sum_univ_five,dL,aL,a2,b2,a3,b3,a4,b4,h2] at y O N w z q U C D E;rcases U with⟨⟨B,e,F,G⟩,⟨g,a0,a1⟩,⟨n,o⟩,H⟩
 rcases C with⟨c0,R,S,T,V⟩
 rcases D with⟨d0,d1,d2,d3,d4⟩
 rcases E with⟨X,e1,e2,e3,Z⟩
 by_cases P:t=0
 ·subst t;have Q:a 1=0∧b 1=0:=by
   clear* -y K hb M e g;grind only
  have z0:b 0= -(a 0):=by grind only
  have a5:d=c:=by clear* -K Q z0 w z B e F G;funext i;fin_cases i<;>grind only
  subst d;simp only[Q.1,Q.2,z0,zero_mul,mul_zero,zero_add,add_zero] at*
  simp[←mul_add,mul_assoc,K] at R S T V;clear* -R S T V X e1 e2 e3 Z M q w h2;funext i;change x i=0;by_cases p:c 2+c 1=0<;>by_cases r:c 2+c 3=0<;>by_cases u:c 2+c 4=0<;>fin_cases i<;>grind only
 ·simp only[P,false_or] at n o H;have s:c 2≠0∧d 2≠0:=by
   clear* -P M O N w z e g n o;grind only
  have no:¬(a 0=t*c 0∧b 0=t*d 0∧a 1=t*c 1∧b 1=t*d 1):=by clear* -N y O P w z q n o H;grind only
  have f (u v:ℂ) (h:c 2*v+u*d 2=0)
    (p:a 0*v+u*b 0=t*(c 0*v+u*d 0)) (r:a 1*v+u*b 1=t*(c 1*v+u*d 1)):
    u=0∧v=0:=by
   clear* -s no h p r e g;grind only
  obtain⟨s3,t3⟩:=f _ _ n F a0;obtain⟨s4,t4⟩:=f _ _ o G a1;have A:(a 0=t*c 0∧b 0=t*d 0)∨(a 1=t*c 1∧b 1=t*d 1):=by clear* -s y B e g;grind only
  clear X e1 e2 e3 Z f;rcases A with⟨l,r⟩|⟨l,r⟩<;>simp_all only[zero_mul,mul_zero,zero_add,add_zero]
  all_goals
   have h3:x 3=0:=by grind (ringSteps:=500000) only
   have h4:x 4=0:=by grind (ringSteps:=500000) only
   simp_all only[mul_zero,add_zero];funext i;change x i=0;fin_cases i<;>grind only
end Ac.A2
namespace Ac.A2
open Aa Ae Matrix A5
set_option maxHeartbeats 1000000 in
lemma aCl {P:Type*} [AddCommGroup P] [Module ℂ P] [FiniteDimensional ℂ P]
  (Q:Module.finrank ℂ P=2) (a b:P→ₗ[ℂ] aH)
  (A:Function.Injective a) (B:Function.Injective b)
  (f:∀t,cS (a t)+cS (b t)=0) (H:∀t,dQ (a t) (b t)=0)
  (S:∃G:F→F→ℂ,∀t,∃c:ℂ,dL (a t) (b t)=c•G)
  (ht:∀t,A5.aFr (dL (a t) (b t)))
  {X:Submodule ℂ aH} (R:∀p q x,x∈X→Ag.dL (a p) (b q)*ᵥ x=0):
  Module.finrank ℂ X≤1:=by
 classical
 obtain⟨z,o,T,r,J,M,t,m⟩:=aBd Q a b A B f S;have p:=gN (fun e=>J (A (e.trans a.map_zero.symm))) (fun e=>J (B (e.trans b.map_zero.symm))) M (f r);obtain⟨i,j,g,N,O,n,K⟩:=Ba.yS p;obtain⟨k,a0,a1,s⟩:∃k,k≠i∧k≠j∧(a z k≠0∨b z k≠0):=by by_contra! u;exact T (zX g.symm u (H z))
 let v:Fin 3→F:= ![i,j,k]
 obtain⟨σ,hσ⟩:=Equiv.Perm.exists_extending_pair (![0,1,2]:Fin 3→F) v
  (by decide) (by intro p q;fin_cases p<;>fin_cases q<;>simp_all[v,ne_comm])
 have d:σ 0=i:=hσ 0;have w:σ 1=j:=hσ 1;have y:σ 2=k:=hσ 2;have Z:cS (b z)=0:=by simpa[o] using f z
 have prod:∑j,a z j*b z j=0:=by simpa[Ba.aFq,o] using H z
 apply aCk k;intro x U V
 suffices x∘σ=0 from funext fun j=>by simpa using congrFun this (σ.symm j)
 apply zY (a r∘σ) (b r∘σ) (a z∘σ) (b z∘σ) (x∘σ) t
 ·simpa[d] using N
 ·simpa[d] using O
 ·intro l C E;exact K _ (d▸σ.injective.ne C) (w▸σ.injective.ne E)
 ·simpa[Ag.aL,aL,d,w] using M i j g.symm
 ·simpa only[Function.comp_apply,Equiv.sum_comp] using f r
 ·simpa only[Function.comp_apply,Equiv.sum_comp] using n
 ·exact(Equiv.sum_comp σ (a z)).trans o
 ·exact(Equiv.sum_comp σ (b z)).trans Z
 ·exact(Equiv.sum_comp σ (fun j=>a z j*b z j)).trans prod
 ·simpa[y] using s
 ·exact fun i j h=>m (σ i) (σ j) (σ.injective.ne h)
 all_goals first | exact yA σ (R _ _ x U) | simpa[y] using V
end Ac.A2
namespace Ac
open Aa An Ae Matrix
lemma aGe:vK:=by
 intro L hL w A e;obtain⟨i,j,y,c,m⟩:=A1.tU hL w A e;obtain⟨ρ,_,_,g,s,C,o,r,B⟩:=As.wX hL w A e y c m
 let M:=L.map (Ad.re ρ 1)
 obtain⟨f,a,d,H,_,_,l⟩:=As.aBb g s C o r B;have u:p M 0 1=6:=by have h:=bB (i:=0) (j:=1) (k:=2) C (by decide) (by decide) (by decide);change aX M+aE M 0≤p M 0 1+p M 0 2 at h;have c:=o 0 1 (by decide);have m:=o 0 2 (by decide);change aX M=8 at s;change aE M 0=4 at r;change p M 0 1≤6 at c;change p M 0 2≤6 at m;omega
 obtain⟨G,v⟩:=Bb.aG0 g u r B
 let b:=As.wY f
 have F:Function.Injective b:=fun p q h=>a 3 (neg_injective h)
 have n (t:As.E):bD 0 0 (f 2 t) (b t)∈M:=As.aBc a H t;have z (t:As.E):=As.wZ g (n t);have c:=A2.aCl (show Module.finrank ℂ As.E=2 from Module.finrank_fin_fun ℂ)
  (f 2) b (a 2) F (fun t=>(z t).1) (fun t=>(z t).2)
  ⟨G,fun t=>(v _ _ (n t)).1⟩
  (fun t i j k _ _ _=>(v _ _ (n t)).2 i j k)
  (X:=LinearMap.range (f 0))
  (fun p q x J=>l _ _ x (LinearMap.mem_range_self _ p)
    (show b q∈LinearMap.range (f 3) from⟨-q,by simp[b,As.wY]⟩)
    (Submodule.mem_sup_left J))
 rw[d 0] at c;omega
end Ac
namespace Ac.Al
open Aa Ac.Ae Ac.Ap
def cO (r:Fin 4) (w:aH):aC:=fun p=>(if p.1=r then(2:ℂ) else-1)*w p.2
def fT (x y:aH) (a b:ℕ):ℂ:=∑f:Fin (a+b) ↪ Fin 5,∏r,if r.val<a then x (f r) else y (f r)
def qC (x y:aH) (a b:ℕ):ℂ:=∑j,x j^a*y j^b
abbrev tZ (x y:aH):Prop:=
 fT x y 1 0= -20∧fT x y 0 1= -20∧
 fT x y 2 0= -40∧fT x y 1 1=80∧fT x y 0 2= -40∧
 fT x y 3 0=48∧fT x y 2 1= -240∧fT x y 1 2= -240∧fT x y 0 3=48∧
 fT x y 4 0= -60∧fT x y 3 1=480∧fT x y 2 2=120∧
 fT x y 1 3=480∧fT x y 0 4= -60
abbrev yT (x y:aH):Prop:=
 qC x y 1 0= -20∧qC x y 0 1= -20∧
 qC x y 2 0=440∧qC x y 1 1=320∧qC x y 0 2=440∧
 qC x y 3 0= -9176∧qC x y 2 1= -6920∧qC x y 1 2= -6920∧qC x y 0 3= -9176∧
 qC x y 4 0=192170∧qC x y 3 1=144560∧qC x y 2 2=133580∧
 qC x y 1 3=144560∧qC x y 0 4=192170
end Ac.Al
namespace Ac.Al.Be
open Aa Ac.Ad Finset
export Ac.Ad (kK aS gQ bQ B aEo aEp gM)
lemma aCm (L:Submodule ℂ aC) (hL:aD L) (a b:Fin 4) (hab:a≠b)
  (hfix:∀x∈L,∀j,x (a,j)=x (b,j)) (g:aX L=7)
  (F:aC) (d:∀j,F (a,j)=F (b,j)) (k:∀t∈L,kK F t=0):
  bQ F∈L:=by
 obtain⟨o,l⟩:=gM hL;obtain⟨S,c,m,f⟩:=vP L ⟨fun i=>(a,i),fun _ _ h=>congrArg Prod.snd h⟩
  ⟨fun i=>(b,i),fun _ _ h=>congrArg Prod.snd h⟩ (fun _ _ h=>hab (congrArg Prod.fst h)) hfix o l (by
    intro x n i;change gQ x (a,i)=gQ x (b,i);simp only[gQ,gR,hfix x n]) g
 have e:L=S:=Submodule.eq_of_le_of_finrank_le c (by change aX S≤aX L;simp only[Fintype.card_fin] at m;omega);exact e▸f F k d
lemma pE {S:Submodule ℂ aC} (hL:aD S) (n:aX S=7)
  (hfix:∀t∈S,row 0 t=row 1 t) (r:Fin 4) (g:0≠r) (l:1≠r):
  ∃x:aH,cO r x-1∈S:=by
 classical
 obtain⟨f,d,c⟩:=Ap.jM hL r
 let u:aH:=fun j=>f (Pi.single j 1)
 have b (x:aH):(∑j,u j*x j)=f x:=by
  have dec:∑j,x j•(Pi.single j 1:aH)=x:=by funext k;simp[Finset.sum_apply,Pi.smul_apply,Pi.single_apply,mul_ite]
  conv_rhs=>rw[←dec,map_sum]
  simp only[u,map_smul,smul_eq_mul,mul_comm (x _) _]
 have s:∑j,u j=1:=by simpa using(b 1).trans d
 let F:aC:=fun p=>if p.1=r then u p.2 else 0
 have e (i:Fin 4):gR F i=if i=r then 1 else 0:=by by_cases h:i=r<;>simp[gR,F,h,s]
 have m (j:Fin 5):gC F j=u j:=by simp[gC,F]
 have a:aS F=1:=by change(∑i,gR F i)=1;simp[e]
 have q:bQ F∈S:=by
  apply aCm S hL 0 1 (by decide) (fun t a j=>congrFun (hfix t a) j) n F
  ·intro j;simp[F,g,l]
  ·intro t a;rw[show kK F t=∑j,u j*t (r,j) by
    unfold kK;rw[Finset.sum_comm];simp[F,ite_mul]]
   exact(b (row r t)).trans (c _ a)
 let w:aH:=fun j=>80*(u j-1/4)
 have o:cO r w-1=(240:ℂ)•bQ F:=by funext p;simp only[cO,Pi.sub_apply,Pi.one_apply,Pi.smul_apply,smul_eq_mul,bQ,e,m,a];by_cases h:p.1=r<;>simp[F,w,h]<;>ring
 exact⟨w,o.symm▸S.smul_mem (240:ℂ) q⟩
end Ac.Al.Be
namespace Ac.Al
open Aa
lemma lM {S:Submodule ℂ aC} (hL:aD S) (a:aX S=7)
  (hfix:∀t∈S,row 0 t=row 1 t):
  ∃x y:aH,cO 2 x-1∈S∧cO 3 y-1∈S:=by
 obtain⟨x,b⟩:=Be.pE hL a hfix 2 (by decide) (by decide);obtain⟨y,c⟩:=Be.pE hL a hfix 3 (by decide) (by decide);exact⟨x,y,b,c⟩
end Ac.Al
namespace Ac.Al
open Aa
lemma zZ (x y:aH) (a b:ℕ) (j:Fin (a+b) ↪ Fin 4):
  (∑e:Fin 4 ↪ Fin 5,∏r:Fin (a+b),
    if r.val<a then x (e (j r)) else y (e (j r)))=
  (((5-(a+b)).descFactorial (4-(a+b)):ℕ):ℂ)*fT x y a b:=by
 classical
 let d:Fin (a+b)⊕ ↥(Set.range j)ᶜ≃Fin 4:=
  (j.toEquivRange.sumCongr (Equiv.refl _)).trans (Equiv.Set.sumCompl (Set.range j))
 let
   E:(Fin 4 ↪ Fin 5)≃
   Σ f:Fin (a+b) ↪ Fin 5,↥(Set.range j)ᶜ ↪ ↥(Set.range f)ᶜ:=
  (Equiv.embeddingCongr d.symm (Equiv.refl _)).trans
    Equiv.sumEmbeddingEquivSigmaEmbeddingRestricted
 let w (f:Fin (a+b) ↪ Fin 5):ℂ:=
  ∏r:Fin (a+b),if r.val<a then x (f r) else y (f r)
 have restrict_eq (e:Fin 4 ↪ Fin 5) (r:Fin (a+b)):(E e).1 r=e (j r):=by
  rfl
 have c (f:Fin (a+b) ↪ Fin 5):
   Fintype.card (↥(Set.range j)ᶜ ↪ ↥(Set.range f)ᶜ)=
    (5-(a+b)).descFactorial (4-(a+b)):=by
  simp only[Fintype.card_embedding_eq,Fintype.card_compl_set,Fintype.card_range,
   Fintype.card_fin]
 calc
  _
   =
    ∑p:Σ f:Fin (a+b) ↪ Fin 5,↥(Set.range j)ᶜ ↪ ↥(Set.range f)ᶜ,
    w p.1:=by
   refine Fintype.sum_equiv E _ _ ?_
   intro e
   simp only[w,restrict_eq]
  _
   =∑f:Fin (a+b) ↪ Fin 5,∑g: ↥(Set.range j)ᶜ ↪ ↥(Set.range f)ᶜ,w f:=
   Fintype.sum_sigma _
  _
   =_:=by
   simp only[Finset.sum_const,Finset.card_univ,c,nsmul_eq_mul,
    Finset.mul_sum,fT,w]
end Ac.Al
namespace Ac.Al
open Aa
def V (a b c d:aH):ℂ:=∑e:Fin 4 ↪ Fin 5,a (e 0)*b (e 1)*c (e 2)*d (e 3)
lemma aFs (a b c d:aH) (i j:Fin 4):
  V
   a b c d=∑e:Fin 4 ↪ Fin 5,a (e (Equiv.swap i j 0))*
   b (e (Equiv.swap i j 1))*c (e (Equiv.swap i j 2))*d (e (Equiv.swap i j 3)):=
 ((Equiv.embeddingCongr (Equiv.swap i j) (Equiv.refl (Fin 5))).sum_comp
   (fun e=>a (e 0)*b (e 1)*c (e 2)*d (e 3))).symm
lemma v12 (a b c d:aH):V a b c d=V b a c d:=by rw[aFs a b c d 0 1];norm_num[V,Equiv.swap_apply_def,mul_comm (a _) (b _)]
lemma v23 (a b c d:aH):V a b c d=V a c b d:=by rw[aFs a b c d 1 2];norm_num[V,Equiv.swap_apply_def,mul_right_comm (_ *_) (b _) (c _),mul_right_comm (a _) (b _) (c _)]
lemma v34 (a b c d:aH):V a b c d=V a b d c:=by rw[aFs a b c d 2 3];norm_num[V,Equiv.swap_apply_def,mul_right_comm (_ *_) (c _) (d _)]
def mix (x y:aH) (s t:ℂ):aH:=fun j=>1+s*x j+t*y j
lemma aH3 (x y a b c:aH) (s t:ℂ):
  V (mix x y s t) a b c=V a b c 1+s*V a b c x+t*V a b c y:=by
 conv_lhs=>rw[v12,v23,v34]
 simp only[V,mix,Pi.one_apply,Finset.mul_sum,←Finset.sum_add_distrib];apply Finset.sum_congr rfl;intro e _;ring
def uN (x y:aH) (a b i:ℕ):aH:=if i<a then x else if i<a+b then y else 1
lemma aH4 (x y:aH) (a b:ℕ) (h:a+b≤4):
  let q:=uN x y a b
  V
   (q 0) (q 1) (q 2) (q 3)=
   (((5-(a+b)).descFactorial (4-(a+b)):ℕ):ℂ)*fT x y a b:=by
 let j:=Fin.castLEEmb h
 rw[←zZ x y a b j];dsimp only;apply Finset.sum_congr rfl;intro e _
 let g (i:Fin 4):=uN x y a b i.val (e i)
 change g 0*g 1*g 2*g 3=_;rw[←Fin.prod_univ_four];symm;apply Fintype.prod_of_injective j j.injective
 ·intro i c;have d:¬i.val<a+b:=fun lt=>c ⟨⟨i.val,lt⟩,rfl⟩
  simp[g,uN,d,show ¬i.val<a by omega]
 ·intro i;change _=(if i.val<a then x else if i.val<a+b then y else 1) _;by_cases H:i.val<a<;>simp[H,i.isLt]
lemma aHq:V 1 1 1 1=120:=by norm_num[V,Fintype.card_embedding_eq,Nat.descFactorial]
lemma aBe (x y:aH) (s t:ℂ):
  aO (1+s•cO 2 x+t•cO 3 y)=
  120
  +(-24)*fT x y 1 0*s^1*t^0
  +(-24)*fT x y 0 1*s^0*t^1
  +(-18)*fT x y 2 0*s^2*t^0
  +(18)*fT x y 1 1*s^1*t^1
  +(-18)*fT x y 0 2*s^0*t^2
  +(10)*fT x y 3 0*s^3*t^0
  +(-6)*fT x y 2 1*s^2*t^1
  +(-6)*fT x y 1 2*s^1*t^2
  +(10)*fT x y 0 3*s^0*t^3
  +(-2)*fT x y 4 0*s^4*t^0
  +(1)*fT x y 3 1*s^3*t^1
  +(6)*fT x y 2 2*s^2*t^2
  +(1)*fT x y 1 3*s^1*t^3
  +(-2)*fT x y 0 4*s^0*t^4
  :=by
 have q:=aH4 x y;have inv (a b:ℕ) (h:a+b≤4):
   fT x y a b=V (uN x y a b 0) (uN x y a b 1)
    (uN x y a b 2) (uN x y a b 3)/
      (((5-(a+b)).descFactorial (4-(a+b)):ℕ):ℂ):=by
  apply(eq_div_iff _).2
  ·rw[q a b h,mul_comm]
  ·have H:=Nat.descFactorial_pos.mpr (show 4-(a+b)≤5-(a+b) by omega);exact_mod_cast H.ne'
 have c:aO (1+s•cO 2 x+t•cO 3 y)=
   V
    (mix x y (-s) (-t)) (mix x y (-s) (-t))
    (mix x y (2*s) (-t)) (mix x y (-s) (2*t)):=by
  unfold aO V;apply Finset.sum_congr rfl;intro e _;norm_num[Fin.prod_univ_four,Pi.add_apply,Pi.smul_apply,cO,mix];ring
 rw[c];simp(disch:=decide) only[inv,aH3];norm_num[uN,Nat.descFactorial];simp only[v12,v23,v34,aHq];ring
end Ac.Al
namespace Ac.Al
open Aa Ac.Ae Polynomial
lemma aAa {L:Submodule ℂ aC} (hL:aD L) {x y:aH}
  (b:cO 2 x-1∈L) (c:cO 3 y-1∈L) (s t:ℂ):
  aO (1+s•cO 2 x+t•cO 3 y)=120*(1+s+t)^4:=by
 have a:=L.add_mem (L.smul_mem s b) (L.smul_mem t c);rw[←bR hL a (1+s+t)];congr 1;funext i;change 1+s*cO 2 x i+t*cO 3 y i=1+s+t+(s*(cO 2 x i-1)+t*(cO 3 y i-1))
 ring
lemma rL {L:Submodule ℂ aC} (hL:aD L) {x y:aH}
  (g:cO 2 x-1∈L) (i:cO 3 y-1∈L):tZ x y:=by
 let m (a b:ℕ) (c d:ℂ):=monomial (a+5*b) (c*(fT x y a b-d))
 let p:=m 1 0 (-24) (-20)+m 0 1 (-24) (-20)+
  m 2 0 (-18) (-40)+m 1 1 18 80+m 0 2 (-18) (-40)+
  m 3 0 10 48+m 2 1 (-6) (-240)+m 1 2 (-6) (-240)+m 0 3 10 48+
  m 4 0 (-2) (-60)+m 3 1 1 480+m 2 2 6 120+m 1 3 1 480+m 0 4 (-2) (-60)
 have f:p=0:=by
  apply eq_of_infinite_eval_eq
  convert(Set.infinite_univ:(Set.univ:Set ℂ).Infinite) using 1
  ext s
  simp only[Set.mem_ofPred_eq,Set.mem_univ,iff_true,eval_zero,p,m,
   eval_add,eval_monomial]
  linear_combination aAa hL g i s (s^5)-aBe x y s (s^5)
 have e (n:ℕ):p.coeff n=0:=by simp[f]
 have h:=And.intro (e 1) (And.intro (e 5) (And.intro (e 2) (And.intro (e 6)
  (And.intro (e 10) (And.intro (e 3) (And.intro (e 7) (And.intro (e 11)
  (And.intro (e 15) (And.intro (e 4) (And.intro (e 8) (And.intro (e 12)
  (And.intro (e 16) (e 20)))))))))))))
 norm_num[p,m,coeff_add,coeff_monomial,mul_eq_zero,sub_eq_zero] at h
 simpa only[add_eq_zero_iff_eq_neg] using h
end Ac.Al
namespace Ac.Al
open Aa
open scoped BigOperators
def aQ {n:ℕ} (z:Fin n→aH):ℂ:=∑f:Fin n ↪ Fin 5,∏i,z i (f i)
lemma kX {n:ℕ} (z:Fin (n+1)→aH):
  aQ z=(∑j,z 0 j)*aQ (fun i=>z i.succ)-
   ∑t:Fin n,aQ (fun i j=>(if i=t then z 0 j else 1)*z i.succ j):=by
 classical
 let w (f:Fin n ↪ Fin 5):=∏i,z i.succ (f i)
 have b:aQ z=∑f:Fin n ↪ Fin 5,
   ∑j:{j//j∉Set.range f},z 0 j*w f:=by
  unfold aQ
  rw[←Fintype.sum_sigma']
  simpa only[Fin.prod_univ_succ,w,Equiv.embeddingFinSucc_fst,
   Equiv.embeddingFinSucc_snd,Function.comp_apply] using
   (Equiv.embeddingFinSucc n (Fin 5)).sum_comp
     (fun p=>z 0 p.2.1*w p.1)
 have c (f:Fin n ↪ Fin 5):
   (∑i,z 0 (f i))+(∑j:{j//j∉Set.range f},z 0 j)=∑j,z 0 j:=by
  have h:=f.toEquivRange.sum_comp (fun j:Set.range f=>z 0 j)
  change(∑i,z 0 (f i))=∑j:Set.range f,z 0 j at h
  rw[h]
  convert! Fintype.sum_subtype_add_sum_subtype (fun j=>j∈Set.range f) (z 0)
   using 1
  congr!
 have a (t:Fin n):
   aQ (fun i j=>(if i=t then z 0 j else 1)*z i.succ j)=
    ∑f:Fin n ↪ Fin 5,z 0 (f t)*w f:=by
  unfold aQ
  apply Finset.sum_congr rfl
  intro f _
  rw[Finset.prod_mul_distrib,Fintype.prod_ite_eq']
 rw[b]
 simp_rw[a]
 rw[Finset.sum_comm (f:=fun t (f:Fin n ↪ Fin 5)=>z 0 (f t)*w f)]
 change _=(∑j,z 0 j)*(∑f,w f)-_
 rw[Finset.mul_sum,←Finset.sum_sub_distrib]
 apply Finset.sum_congr rfl
 intro f _
 rw[←Finset.sum_mul,←Finset.sum_mul,←sub_mul,←c f]
 simp
end Ac.Al
namespace Ac.Al
open Aa
def bL (x y:aH) (a b:ℕ):aH:=fun j=>x j^a*y j^b
lemma dD (x y:aH) (a b c d:ℕ):
  bL x y a b*bL x y c d=bL x y (a+c) (b+d):=by
 funext j;simp[bL,pow_add,mul_left_comm,mul_assoc]
lemma cP (x y:aH) (a b:ℕ):(∑j,bL x y a b j)=qC x y a b:=rfl
lemma cC (u:aH):aQ ![u]=∑j,u j:=by rw[kX (n:=0)];simp[aQ]
lemma dV (u v:aH):
  aQ ![u,v]=(∑j,u j)*aQ ![v]-(aQ ![u*v]):=by
 rw[kX (n:=1)]
 let z:Fin 2→aH:= ![u,v]
 have a:(fun i:Fin 1=>z i.succ)= ![v]:=by funext i;fin_cases i;rfl
 have b:(fun(i:Fin 1) (j:Fin 5)=>(if i=0 then z 0 j else 1)*z i.succ j)= ![u*v]:=by funext i j;fin_cases i;rfl
 change(∑j,u j)*aQ (fun i:Fin 1=>z i.succ)-(∑t:Fin 1,aQ (fun i j=>(if i=t then z 0 j else 1)*z i.succ j))=_;simp only[Fin.sum_univ_one,a,b]
lemma gE (u v w:aH):
  aQ ![u,v,w]=(∑j,u j)*aQ ![v,w]-(aQ ![u*v,w]+aQ ![v,u*w]):=by
 rw[kX (n:=2)]
 let z:Fin 3→aH:= ![u,v,w]
 have a:(fun i:Fin 2=>z i.succ)= ![v,w]:=by funext i;fin_cases i<;>rfl
 have b:(fun(i:Fin 2) (j:Fin 5)=>(if i=0 then z 0 j else 1)*z i.succ j)= ![u*v,w]:=by funext i j;fin_cases i<;>first | rfl | apply one_mul
 have c:(fun(i:Fin 2) (j:Fin 5)=>(if i=1 then z 0 j else 1)*z i.succ j)= ![v,u*w]:=by funext i j;fin_cases i<;>first | rfl | apply one_mul
 change(∑j,u j)*aQ (fun i:Fin 2=>z i.succ)-(∑t:Fin 2,aQ (fun i j=>(if i=t then z 0 j else 1)*z i.succ j))=_;simp only[Fin.sum_univ_two,a,b,c]
lemma pF (u v w s:aH):
  aQ ![u,v,w,s]=(∑j,u j)*aQ ![v,w,s]-(aQ ![u*v,w,s]+aQ ![v,u*w,s]+aQ ![v,w,u*s]):=by
 rw[kX (n:=3)]
 let z:Fin 4→aH:= ![u,v,w,s]
 have a:(fun i:Fin 3=>z i.succ)= ![v,w,s]:=by funext i;fin_cases i<;>rfl
 have b:(fun(i:Fin 3) (j:Fin 5)=>(if i=0 then z 0 j else 1)*z i.succ j)= ![u*v,w,s]:=by funext i j;fin_cases i<;>first | rfl | apply one_mul
 have c:(fun(i:Fin 3) (j:Fin 5)=>(if i=1 then z 0 j else 1)*z i.succ j)= ![v,u*w,s]:=by funext i j;fin_cases i<;>first | rfl | apply one_mul
 have d:(fun(i:Fin 3) (j:Fin 5)=>(if i=2 then z 0 j else 1)*z i.succ j)= ![v,w,u*s]:=by funext i j;fin_cases i<;>first | rfl | apply one_mul
 change(∑j,u j)*aQ (fun i:Fin 3=>z i.succ)-(∑t:Fin 3,aQ (fun i j=>(if i=t then z 0 j else 1)*z i.succ j))=_;simp only[Fin.sum_univ_three,a,b,c,d]
lemma iC (x y:aH):bL x y 1 0=x:=by funext j;simp[bL]
lemma iD (x y:aH):bL x y 0 1=y:=by funext j;simp[bL]
lemma aDy (x y:aH):fT x y 1 0=aQ ![bL x y 1 0]:=by
 rw[fT,aQ,iC];refine Finset.sum_congr rfl fun f _=>Finset.prod_congr rfl fun i _=> ?_
 fin_cases i;rfl
lemma aDz (x y:aH):fT x y 0 1=aQ ![bL x y 0 1]:=by
 rw[fT,aQ,iD];refine Finset.sum_congr rfl fun f _=>Finset.prod_congr rfl fun i _=> ?_
 fin_cases i;rfl
lemma aD0 (x y:aH):fT x y 2 0=aQ ![bL x y 1 0,bL x y 1 0]:=by
 rw[fT,aQ,iC];refine Finset.sum_congr rfl fun f _=>Finset.prod_congr rfl fun i _=> ?_
 fin_cases i<;>rfl
lemma aD1 (x y:aH):fT x y 1 1=aQ ![bL x y 1 0,bL x y 0 1]:=by
 rw[fT,aQ,iC,iD];refine Finset.sum_congr rfl fun f _=>Finset.prod_congr rfl fun i _=> ?_
 fin_cases i<;>rfl
lemma aD2 (x y:aH):fT x y 0 2=aQ ![bL x y 0 1,bL x y 0 1]:=by
 rw[fT,aQ,iD];refine Finset.sum_congr rfl fun f _=>Finset.prod_congr rfl fun i _=> ?_
 fin_cases i<;>rfl
lemma aD3 (x y:aH):fT x y 3 0=aQ ![bL x y 1 0,bL x y 1 0,bL x y 1 0]:=by
 rw[fT,aQ,iC];refine Finset.sum_congr rfl fun f _=>Finset.prod_congr rfl fun i _=> ?_
 fin_cases i<;>rfl
lemma aD4 (x y:aH):fT x y 2 1=aQ ![bL x y 1 0,bL x y 1 0,bL x y 0 1]:=by
 rw[fT,aQ,iC,iD];refine Finset.sum_congr rfl fun f _=>Finset.prod_congr rfl fun i _=> ?_
 fin_cases i<;>rfl
lemma aD5 (x y:aH):fT x y 1 2=aQ ![bL x y 1 0,bL x y 0 1,bL x y 0 1]:=by
 rw[fT,aQ,iC,iD];refine Finset.sum_congr rfl fun f _=>Finset.prod_congr rfl fun i _=> ?_
 fin_cases i<;>rfl
lemma aD6 (x y:aH):fT x y 0 3=aQ ![bL x y 0 1,bL x y 0 1,bL x y 0 1]:=by
 rw[fT,aQ,iD];refine Finset.sum_congr rfl fun f _=>Finset.prod_congr rfl fun i _=> ?_
 fin_cases i<;>rfl
lemma aD7 (x y:aH):fT x y 4 0=aQ ![bL x y 1 0,bL x y 1 0,bL x y 1 0,bL x y 1 0]:=by
 rw[fT,aQ,iC];refine Finset.sum_congr rfl fun f _=>Finset.prod_congr rfl fun i _=> ?_
 fin_cases i<;>rfl
lemma aD8 (x y:aH):fT x y 3 1=aQ ![bL x y 1 0,bL x y 1 0,bL x y 1 0,bL x y 0 1]:=by
 rw[fT,aQ,iC,iD];refine Finset.sum_congr rfl fun f _=>Finset.prod_congr rfl fun i _=> ?_
 fin_cases i<;>rfl
lemma aD9 (x y:aH):fT x y 2 2=aQ ![bL x y 1 0,bL x y 1 0,bL x y 0 1,bL x y 0 1]:=by
 rw[fT,aQ,iC,iD];refine Finset.sum_congr rfl fun f _=>Finset.prod_congr rfl fun i _=> ?_
 fin_cases i<;>rfl
lemma aEa (x y:aH):fT x y 1 3=aQ ![bL x y 1 0,bL x y 0 1,bL x y 0 1,bL x y 0 1]:=by
 rw[fT,aQ,iC,iD];refine Finset.sum_congr rfl fun f _=>Finset.prod_congr rfl fun i _=> ?_
 fin_cases i<;>rfl
lemma aEb (x y:aH):fT x y 0 4=aQ ![bL x y 0 1,bL x y 0 1,bL x y 0 1,bL x y 0 1]:=by
 rw[fT,aQ,iD];refine Finset.sum_congr rfl fun f _=>Finset.prod_congr rfl fun i _=> ?_
 fin_cases i<;>rfl
lemma mX {x y:aH} (h:tZ x y):yT x y:=by
 obtain⟨o,k,s,p,l,v,t,q,m,z,w,u,r,n⟩:=h;have b:qC x y 1 0= -20:=by simp only[aDy,cC,cP] at o;exact o
 have a:qC x y 0 1= -20:=by simp only[aDz,cC,cP] at k;exact k
 have e:qC x y 2 0=440:=by simp only[aD0,dV,cC,dD,Nat.reduceAdd,cP,b] at s;linear_combination-s
 have d:qC x y 1 1=320:=by simp only[aD1,dV,cC,dD,Nat.reduceAdd,cP,b,a] at p;linear_combination-p
 have c:qC x y 0 2=440:=by simp only[aD2,dV,cC,dD,Nat.reduceAdd,cP,a] at l;linear_combination-l
 have j:qC x y 3 0= -9176:=by simp only[aD3,gE,dV,cC,dD,Nat.reduceAdd,cP,b,e] at v;linear_combination(1/2:ℂ)*v
 have i:qC x y 2 1= -6920:=by simp only[aD4,gE,dV,cC,dD,Nat.reduceAdd,cP,b,a,e,d] at t;linear_combination(1/2:ℂ)*t
 have g:qC x y 1 2= -6920:=by simp only[aD5,gE,dV,cC,dD,Nat.reduceAdd,cP,b,a,d,c] at q;linear_combination(1/2:ℂ)*q
 have f:qC x y 0 3= -9176:=by simp only[aD6,gE,dV,cC,dD,Nat.reduceAdd,cP,a,c] at m;linear_combination(1/2:ℂ)*m
 have F:qC x y 4 0=192170:=by simp only[aD7,pF,gE,dV,cC,dD,Nat.reduceAdd,cP,b,e,j] at z;linear_combination(-1/6:ℂ)*z
 have E:qC x y 3 1=144560:=by simp only[aD8,pF,gE,dV,cC,dD,Nat.reduceAdd,cP,b,a,e,d,j,i] at w;linear_combination(-1/6:ℂ)*w
 have C:qC x y 2 2=133580:=by simp only[aD9,pF,gE,dV,cC,dD,Nat.reduceAdd,cP,b,a,e,d,c,i,g] at u;linear_combination(-1/6:ℂ)*u
 have B:qC x y 1 3=144560:=by simp only[aEa,pF,gE,dV,cC,dD,Nat.reduceAdd,cP,b,a,d,c,g,f] at r;linear_combination(-1/6:ℂ)*r
 have A:qC x y 0 4=192170:=by simp only[aEb,pF,gE,dV,cC,dD,Nat.reduceAdd,cP,a,c,f] at n;linear_combination(-1/6:ℂ)*n
 exact⟨b,a,e,d,c,j,i,g,f,F,E,C,B,A⟩
end Ac.Al
namespace Ac.Al
open Aa
def kY:Matrix (Fin 6) (Fin 6) ℤ:=
 !![5,-20,-20,440,320,440;
  -20,440,320,-9176,-6920,-6920;
  -20,320,440,-6920,-6920,-9176;
  440,-9176,-6920,192170,144560,133580;
  320,-6920,-6920,144560,133580,144560;
  440,-6920,-9176,133580,144560,192170]
set_option maxHeartbeats 4000000 in
lemma uX:kY.det= -667430184500352000:=by
 unfold kY
 eval_det
set_option maxHeartbeats 1600000 in
lemma uY (x y:aH) (h:yT x y):False:=by
 classical
 obtain⟨n,f,r,o,g,u,s,p,l,w,v,t,q,m⟩:=h;have e:qC x y 0 0=5:=by simp[qC]
 let a:Fin 6→ℕ:= ![0,1,0,2,1,0]
 let b:Fin 6→ℕ:= ![0,0,1,0,1,2]
 let V:Matrix (Fin 6) (Fin 5) ℂ:=fun i j=>x j^a i*y j^b i
 have d (i k:Fin 6):
   (V*V.transpose) i k=qC x y (a i+a k) (b i+b k):=by
  rw[Matrix.mul_apply,qC];apply Finset.sum_congr rfl;intro j _;change(x j^a i*y j^b i)*(x j^a k*y j^b k)=_;simp only[pow_add];ring
 have c:V*V.transpose=kY.map (fun z=>(z:ℂ)):=by apply Matrix.ext;intro i k;rw[d];fin_cases i<;>fin_cases k<;>norm_num[a,b,kY,Matrix.map_apply,e,n,f,r,o,g,u,s,p,l,w,v,t,q,m]
 have B:(V*V.transpose).rank=6:=by apply Matrix.rank_of_det_ne_zero;rw[c,←Int.cast_det,uX];norm_num
 have A:(V*V.transpose).rank≤5:=(Matrix.rank_mul_le_left _ _).trans V.rank_le_width;omega
end Ac.Al
namespace Ac.Al
open Aa
lemma yB {x y:aH} (a:tZ x y):False:=uY x y (mX a)
end Ac.Al
namespace Ac.Al
open Aa Ac.Ae Ac.Ap Ac.A4
abbrev aBf (L:Submodule ℂ aC):Prop:=
 ∃
  a b:aH,bD a b 0 0≠0∧bD a b 0 0∈L∧
  aJ L 2 3=Submodule.span ℂ {bD a b 0 0}∧
  ∃
   i j:F,i≠j∧a i≠0∧a j≠0∧b i≠0∧b j≠0∧
   (∀k,k≠i→k≠j→a k=0∧b k=0)∧
   aL a b i j=0∧a i*b j-a j*b i≠0∧cS a≠0∧cS b≠0
lemma sP
  (a:∀{S:Submodule ℂ aC},aD S→aX S=7→
    (∀t∈S,row 0 t=row 1 t)→False)
  {L:Submodule ℂ aC} (hL:aD L)
  (d:aX L=8) (g:p L 2 3=7) (h:∀i,u L i=0):aBf L:=by
 rcases iT hL d g h with⟨S,_,c,b,e⟩|f
 ·exact(a c b e).elim
 ·exact f
end Ac.Al
namespace Ac.Al
open Aa Ac.Ae Ac.Ap Ac.A4
lemma uZ {S:Submodule ℂ aC} (a:aD S) (b:aX S=7)
  (hfix:∀t∈S,row 0 t=row 1 t):False:=by
 obtain⟨x,y,c,d⟩:=lM a b hfix;exact yB (rL a c d)
lemma qD {L:Submodule ℂ aC} (hL:aD L)
  (a:aX L=8) (b:p L 2 3=7) (c:∀i,u L i=0):aBf L:=
 sP uZ hL a b c
end Ac.Al
namespace Ac.Am
open Aa Aq Ae
abbrev aEc (L:Submodule ℂ aC):=L⊔Submodule.span ℂ {(1:aC)}
lemma sQ {L:Submodule ℂ aC} {X:aC}:
  X∈aEc L↔∃s,aR L X s:=by
 constructor
 ·intro c;obtain⟨v,b,z,d,rfl⟩:=Submodule.mem_sup.mp c;obtain⟨s,rfl⟩:=Submodule.mem_span_singleton.mp d;refine⟨s,v,b,?_⟩;funext a;change v a+s*1=s+v a;ring
 ·rintro⟨s,v,b,rfl⟩;apply Submodule.mem_sup.mpr;refine⟨v,b,s•(1:aC),Submodule.smul_mem _ _ (Submodule.subset_span (by simp)),?_⟩;funext a;change v a+s*1=s+v a;ring
abbrev dY (U:aC):=∀r c,(2≤ r.val∨2≤ c.val)→U (r,c)=0
abbrev eP (U:aC):=U (0,0)*U (1,1)-U (0,1)*U (1,0)≠0
end Ac.Am
namespace Ac.Aq.Ax
open Aa Ae
abbrev iZ:=Fin 2→ℂ
abbrev iA:=Fin 3→ℂ
abbrev bI:=iA×iA
def cG (x y:iA):ℂ:=x 0*(y 1+y 2)+x 1*(y 0+y 2)+x 2*(y 0+y 1)
lemma qM (x y z:iA):cG (x+y) z=cG x z+cG y z:=by simp[cG];ring
lemma kE (a:ℂ) (x y:iA):cG (a•x) y=a*cG x y:=by simp[cG];ring
lemma tH (x y:iA):cG x y=cG y x:=by unfold cG;ring
lemma xB (x y z:iA):cG x (y+z)=cG x y+cG x z:=by simp[cG];ring
lemma nR (a:ℂ) (x y:iA):cG x (a•y)=a*cG x y:=by simp[cG];ring
@[simp] lemma pair_zero_left (y : iA) : cG 0 y = 0 := by
 simp[cG]
lemma pG (x:iA):cG x 1=2*(x 0+x 1+x 2):=by simp[cG];ring
lemma fR (x:iA) (h:∀y,cG x y=0):x=0:=by funext i;have e:=h (fun j=>if j=i then-1 else 1);fin_cases i<;>norm_num[cG] at e ⊢ <;>grobner
def dW:LinearMap.BilinForm ℂ iA:=
 LinearMap.mk₂ ℂ cG qM kE xB
  (fun a x y=>nR a x y)
lemma mY:dW.Nondegenerate:=by
 have a:dW.IsSymm:=⟨tH⟩
 exact a.isRefl.nondegenerate_iff_separatingLeft.mpr fR
lemma lN (W:Submodule ℂ iA)
  (b:∀x∈W,∀y∈W,cG x y=0):Module.finrank ℂ W≤1:=by
 have c:W≤dW.orthogonal W:=fun y e x d=>b x d y e
 have a:=Submodule.finrank_mono c;rw[LinearMap.BilinForm.finrank_orthogonal mY,Module.finrank_fin_fun] at a;omega
def kF (b:iZ) (B:bI):iA:=b 0•B.1+b 1•B.2
def aT (i:Fin 4):aC→ₗ[ℂ] iA:=LinearMap.funLeft ℂ ℂ fun j=>(i,Fin.natAdd 2 j)
abbrev gV:aC→ₗ[ℂ] bI:=(aT 0).prod (aT 1)
def bO (U:aC):iZ→ₗ[ℂ] iZ where
 toFun c:= ![c 1*U (1,0)+c 0*U (1,1),c 1*U (0,0)+c 0*U (0,1)]
 map_add' a b:=by funext i;fin_cases i<;>simp<;>ring
 map_smul' a b:=by funext i;fin_cases i<;>simp<;>ring
lemma jB (U:aC)
  (c:U (0,0)*U (1,1)-U (0,1)*U (1,0)≠0):
  Function.Bijective (bO U):=by
 suffices h:Function.Injective (bO U) from⟨h,LinearMap.injective_iff_surjective.mp h⟩
 intro x y e;have a:=congrFun e 0;have b:=congrFun e 1;simp[bO] at a b;funext i;fin_cases i<;>dsimp<;>grobner
lemma kG (Y U T:aC) (c d:iZ)
  (a:Y (2,0)=c 0) (b:Y (2,1)=c 1)
  (e:Y (3,0)=d 0) (f:Y (3,1)=d 1):
  iH Y U T 2 3+iH Y U T 3 2=
   cG (kF (bO U d) (gV Y)) (aT 2 T)+
   cG (kF (bO U c) (gV Y)) (aT 3 T):=by
 simp[iH,fL,a,b,e,f,cG,kF,bO,gV,aT];ring
end Ac.Aq.Ax
namespace Ac.Am
open Aa Ae Aq Aq.Ax
abbrev xC:aC→ₗ[ℂ] bE:=LinearMap.funLeft ℂ ℂ ![(0,0),(0,1),(1,0),(1,1)]
abbrev aAb (i j:Fin 4):bE→ₗ[ℂ] iZ:=LinearMap.funLeft ℂ ℂ ![i,j]
abbrev mZ (U:aC):=((bO U).comp (aAb 0 1+aAb 2 3)).comp aG
abbrev iV (i:Fin 4):=(dW.flip 1).comp (aT i)
lemma qN {L:Submodule ℂ aC} (hL:aD L) {U X:aC}
  (c:U∈L) (b:dY U) (a:X∈aP L):
  mZ U X 0*iV 0 X+mZ U X 1*iV 1 X=0:=by
 have h:=dC hL (Y:=X) (s:=0) ⟨X,a.1,by ext;simp[aM]⟩ c
  (T:=1) (u:=1) ⟨0,L.zero_mem,by ext;simp[aM]⟩ b a.2
 let v:=aG X
 rw[kG X U 1 (aAb 0 1 v) (aAb 2 3 v) rfl rfl rfl rfl] at h;change cG (kF _ (gV X)) 1+cG (kF _ (gV X)) 1=0 at h;simp only[kF,qM,kE] at h;simp only[mZ,LinearMap.comp_apply,LinearMap.add_apply,map_add,Pi.add_apply];linear_combination(norm:=ring1!) h
lemma aBg {L:Submodule ℂ aC} (hL:aD L) {U X:aC}
  (k:U∈L) (g:dY U) (m:eP U)
  (b:(aP L).map aG= ⊤) (o:X∈aP L) (n:mZ U X=0):
  Aj.bC X 0=0∧Aj.bC X 1=0:=by
 have a (v:iZ):v 0*iV 0 X+v 1*iV 1 X=0:=by
  obtain⟨c,rfl⟩:=(jB U m).2 v;have l: ![c 0,c 1,0,0]∈(aP L).map aG:=by rw[b];trivial
  obtain⟨Y,f,e⟩:=l;have p:mZ U Y=bO U c:=by simp only[mZ,LinearMap.comp_apply,e];apply congrArg (bO U);funext j;fin_cases j<;>simp[aAb]
  have d:=qN hL k g ((aP L).add_mem o f);simp only[map_add,n,zero_add] at d;rw[←p];linear_combination d-qN hL k g f
 have z (i) (h:iV i X=0):Aj.bC X i=0:=by change cG (aT i X) 1=0 at h;rw[pG] at h;exact(mul_eq_zero.mp h).resolve_left (by norm_num)
 exact⟨z 0 (by simpa using a ![1,0]),z 1 (by simpa using a ![0,1])⟩
lemma aAc {L:Submodule ℂ aC} (hL:aD L) {U X:aC}
  (o:U∈L) (n:dY U) (g:eP U)
  (f:(aP L).map aG= ⊤) (c:X∈aP L) {b:ℂ}
  (a:aG X= ![1,b,-1,-b]) (u:b≠0):
  let t:=xC X
  t 0+t 1+t 2+t 3=0∧t 0*t 3+t 1*t 2=2*b:=by
 obtain⟨h,k⟩:=aBg hL o n g f c (by simp only[mZ,LinearMap.comp_apply,a];rw[←(bO U).map_zero];congr 1;funext j;fin_cases j<;>simp[aAb]);have q:=tC hL c.1;rw[eW c.2,a] at q;have d:per ![1,b,-1,-b]≠0:=by simp[per];grobner
 have p:Aj.eM X=0:=by convert(mul_eq_zero.mp q).resolve_left d using 1;unfold Aj.eM Aj.bC dB;ring
 have m:=Ad.cT hL c.1;obtain⟨s,e⟩:=Aj.mO (x:=X) (by
  intro i g j l;obtain⟨r,rfl⟩:∃r:Fin 2,Fin.natAdd 2 r=i:=⟨_,Fin.natAdd_subNat_cast g⟩
  obtain⟨s,rfl⟩:∃s:Fin 3,Fin.natAdd 2 s=j:=⟨_,Fin.natAdd_subNat_cast l⟩
  exact congrFun (show aB X=0 from c.2) (r,s))
  h k p m.1 m.2.1
 simp only[Aj.aS,Aj.dQ,Aj.jS,Fin.sum_univ_four,
  show Aj.bW X (2,0)=1 from congrFun a 0,show Aj.bW X (2,1)=b from congrFun a 1,
  show Aj.bW X (3,0)= -1 from congrFun a 2,show Aj.bW X (3,1)= -b from congrFun a 3] at s e
 dsimp[Aj.bW] at s e;dsimp[xC];exact⟨by linear_combination s,by linear_combination e⟩
lemma aEd (X Y U:bE)
  (h:∀b c:ℂ,b≠0→let m:=X+b•Y+c•U;
    m 0+m 1+m 2+m 3=0∧m 0*m 3+m 1*m 2=2*b):
  U 0*U 3-U 1*U 2=0:=by
 obtain⟨j,a⟩:=h 1 0 one_ne_zero;obtain⟨s₁,d⟩:=h (-1) 0 (by norm_num);obtain⟨k,e⟩:=h 1 1 one_ne_zero;have f:=(h 2 0 (by norm_num)).2;have g:=(h 1 (-1) one_ne_zero).2;have i:=(h 2 1 (by norm_num)).2;simp at*
 grobner
lemma oB {L:Submodule ℂ aC} (hL:aD L) (g:p L 2 3=7)
  (x:aX L=8) {U:aC} (f:U∈L) (d:dY U) (e:eP U)
  (n:Module.finrank ℂ ((aEc L).map aB)=4):False:=by
 obtain⟨t,_,u,_⟩:=iK g (cB hL g f d e);rw[t,n] at u;have a:(aP L).map aG= ⊤ :=by apply Submodule.eq_top_of_finrank_eq;rw[Module.finrank_fin_fun];omega
 have lift (v:bE):∃X∈aP L,aG X=v:=by change v∈(aP L).map aG;rw[a];trivial
 obtain⟨X,q,l⟩:=lift ![1,0,-1,0];obtain⟨Y,r,m⟩:=lift ![0,1,0,-1];have w:U∈aP L:=⟨f,by change aB U=0;funext ⟨i,j⟩;apply d;left;change 2≤2+i.val;omega⟩
 have k:aG U=0:=by funext i;fin_cases i<;>apply d<;>decide
 apply e;apply aEd (xC X) (xC Y) (xC U);intro b c s
 let K:=aP L
 let T:=X+b•Y+c•U
 have o:T∈K:=K.add_mem (K.add_mem q (K.smul_mem _ r)) (K.smul_mem _ w);have h:=aAc hL f d e a o (b:=b) (by simp only[T,map_add,map_smul,l,m,k,smul_zero,add_zero];funext i;fin_cases i<;>simp) s;simpa only[T,map_add,map_smul] using h
end Ac.Am
namespace Ac.Bc
open Aa Ae Aq Aq.Ax
abbrev V (L:Submodule ℂ aC):=L⊔Submodule.span ℂ {(1:aC)}
abbrev K (L:Submodule ℂ aC):=aP (V L)
abbrev nA (i:Fin 4):aC→ₗ[ℂ] iZ:=LinearMap.funLeft ℂ ℂ (fun j=>(i,Fin.castLE (by decide) j))
abbrev aG2 (i:Fin 2):=Fin.natAdd 2 i
abbrev dY (U:aC):=∀(r:Fin 4) (c:Fin 5),(2≤ r.val∨2≤ c.val)→U (r,c)=0
def dt (X:aC) (i j:Fin 4):=X (i,0)*X (j,1)-X (i,1)*X (j,0)
abbrev Law (L:Submodule ℂ aC) (f:Module.Dual ℂ jH):=∀Z∈V L,aO Z=120*f (aB Z)^4
def det (a b:iZ):ℂ:=a 0*b 1-a 1*b 0
def uA (a b:iZ):ℂ:=a 0*b 1+a 1*b 0
abbrev S (n:Fin 4) (L:Submodule ℂ aC):=K L⊓LinearMap.ker (nA n)
abbrev E (n:Fin 4) (L:Submodule ℂ aC):=V L⊓LinearMap.ker (aT n)
def jJ (j:Fin 3):iA:=fun i=>if i=j then 1 else 0
abbrev uO (m n:Fin 4):=(m=2∧n=3)∨(m=3∧n=2)
variable {m n : Fin 4}
lemma aEe (o:uO m n) {L:Submodule ℂ aC}
  (a:(V L).map aB= ⊤) (r s:iA):
  ∃X∈V L,aT m X=r∧aT n X=s:=by
 let z:jH:=fun p=>if aG2 p.1=m then r p.2 else s p.2
 obtain⟨X,b,e⟩:=(show z∈(V L).map aB by rw[a];trivial)
 rcases o with⟨rfl,rfl⟩|⟨rfl,rfl⟩<;>refine⟨X,b,?_,?_⟩<;>funext k<;>first | exact congrFun e (0,k) | exact congrFun e (1,k)
lemma kZ (o:uO m n) {L:Submodule ℂ aC} {W:aC} (a:W∈K L):
  aT m W=0∧W∈E n L:=by
 have z:=(show aB W=0 from a.2)
 rcases o with⟨rfl,rfl⟩|⟨rfl,rfl⟩<;>refine⟨?_,a.1,?_⟩<;>apply funext<;>intro j<;>first | exact congrFun z (0,j) | exact congrFun z (1,j)
lemma in0 (X:aC) (i:Fin 4):nA i X 0=X (i,0):=rfl
lemma in1 (X:aC) (i:Fin 4):nA i X 1=X (i,1):=rfl
lemma aBh (Z:aC) (i k):aT i Z k=Z (i,Fin.natAdd 2 k):=rfl
lemma aH5:Fin.natAdd 2 (0:Fin 3)=(2:Fin 5):=rfl
lemma aH6:Fin.natAdd 2 (1:Fin 3)=(3:Fin 5):=rfl
lemma aH7:Fin.natAdd 2 (2:Fin 3)=(4:Fin 5):=rfl
def aBi (j:Fin 3):aC→ₗ[ℂ] iZ:=LinearMap.pi fun i=>(dW.flip (jJ j)).comp (aT (![0,1] i))
lemma aBj (j:Fin 3) (Z:aC) (i:Fin 2):aBi j Z i=cG (aT (![0,1] i) Z) (jJ j):=rfl
def aEf (U:aC):LinearMap.BilinForm ℂ iZ:=(dotProductBilin ℂ ℂ).comp (bO U)
lemma aAd (U:aC) (c p:iZ):aEf U c p=
  (c 1*U (1,0)+c 0*U (1,1))*p 0+(c 1*U (0,0)+c 0*U (0,1))*p 1:=by
 simp[aEf,bO,dotProduct,Fin.sum_univ_two]
def iP (m n:Fin 4) (a b:ℂ) (X:aC):=a•nA n X+b•nA m X
def bQ (j:Fin 3) (Z:aC):aC:=fun p=>Z p-aT p.1 Z j
set_option maxHeartbeats 2500000 in
lemma nB (o:uO m n) {Z:aC} (j:Fin 3) {a b:ℂ}
  (q:aT m Z=a•jJ j) (r:aT n Z=b•jJ j):
  aO Z=(uA (nA m Z) (nA n Z)+iP m n a b Z 0+iP m n a b Z 1)*cG (aT 0 Z) (aT 1 Z)+aEf (bQ j Z) (iP m n a b Z) (aBi j Z):=by
 have c (i:Fin 4) (v:ℂ) (h:aT i Z=v•jJ j):
   Z (i,2)=v*jJ j 0∧Z (i,3)=v*jJ j 1∧Z (i,4)=v*jJ j 2:=
  ⟨congrFun h 0,congrFun h 1,congrFun h 2⟩
 obtain⟨e,f,g⟩:=c m a q;obtain⟨k,l,p⟩:=c n b r;rw[cK];have d:=(by decide:∀i:Fin 3,i=0∨i=1∨i=2) j;rcases o with⟨rfl,rfl⟩|⟨rfl,rfl⟩<;>rcases d with rfl|rfl|rfl<;>
  simp(config:={decide:=true}) only[rB,ite_true,ite_false,jJ,e,f,g,k,l,p,
   aAd,bQ,aBj,iP,uA,cG,
   Matrix.cons_val_zero,Matrix.cons_val_one,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
   in0,in1,aBh,aH5,aH6,aH7,zero_mul,mul_zero,mul_one,add_zero,zero_add]<;>ring
lemma aBk (o:uO m n) {L:Submodule ℂ aC} {f:Module.Dual ℂ jH}
  (c:Law L f) {U:aC} (p:U∈K L) (d:dY U) {Z:aC} (q:Z∈V L)
  (j:Fin 3) {a b:ℂ} (h:aT m Z=a•jJ j) (l:aT n Z=b•jJ j):
  aEf U (iP m n a b Z) (aBi j Z)=0:=by
 have e:=c (Z+U) ((V L).add_mem q p.1);rw[map_add,show aB U=0 from p.2,add_zero,←c Z q] at e;have rP (i:Fin 4):aT i (Z+U)=aT i Z:=funext fun k=>add_eq_left.mpr (d _ _ (Or.inr (by change 2≤2+k.val;omega)))
 have bot:2≤ m.val∧2≤n.val:=by rcases o with⟨rfl,rfl⟩|⟨rfl,rfl⟩<;>decide
 have u (k):=d m k (Or.inl bot.1);have v (k):=d n k (Or.inl bot.2);rw[nB o j ((rP m).trans h) ((rP n).trans l),nB o j h l] at e;have g (i k):=congrFun (rP i) k;simp only[aAd,iP,aBj,bQ,uA,
  Matrix.cons_val_zero,Matrix.cons_val_one,
  Pi.add_apply,Pi.smul_apply,smul_eq_mul,in0,in1,rP,g,u,v,add_zero] at e ⊢
 linear_combination e
lemma xD {U:aC} (e:dt U 0 1≠0) {a b x:iZ}
  (hab:det a b≠0) (c:aEf U a x=0) (d:aEf U b x=0):x=0:=by
 simp only[aAd,det,dt] at*
 funext i;fin_cases i<;>change x _=0<;>grobner
lemma uB (o:uO m n) {L:Submodule ℂ aC} {U:aC}
  (C:U∈K L) (A:dY U) (l:dt U 0 1≠0) {f:Module.Dual ℂ jH} (p:Law L f)
  (y:(V L).map aB= ⊤) {X Y:aC} (s:X∈E n L) (b:Y∈S n L)
  (j:Fin 3) (z:aT m X=jJ j) (a:det (nA m Y) (nA n X)≠0)
  (i:uA (nA m Y) (nA n X)≠0):f (aB X)=0:=by
 obtain⟨M,J⟩:=kZ o b.1;have N:aT n Y=0:=J.2;have w:nA n Y=0:=b.2;have x:aT n X=0:=s.2;obtain⟨T,B,G,H⟩:=aEe o y 0 (jJ j)
 let Z (t k:ℂ):=X+t•T+k•Y
 have u (t k):Z t k∈V L:=(V L).add_mem ((V L).add_mem s.1 ((V L).smul_mem t B)) ((V L).smul_mem k b.1.1);have q (t k):aT m (Z t k)=(1:ℂ)•jJ j:=by simp[Z,G,M,z]
 have r (t k):aT n (Z t k)=t•jJ j:=by simp[Z,H,N,x]
 have cH (t k:ℂ):=aBk o p C A (u t k) j (q t k) (r t k);simp only[Z,iP,map_add,map_smul,w,smul_zero,one_smul,add_zero,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul] at cH;have v:aBi j Y=0:=by
  apply xD l a
  ·linear_combination(cH 1 1+cH 1 (-1))/2-cH 1 0
  ·linear_combination cH 0 1-cH 0 0
 simp only[v,map_zero,mul_zero,add_zero] at cH;have F:aBi j X=0:=by
  apply xD l a
  ·linear_combination(cH 1 1-cH 1 0-cH (-1) 1+cH (-1) 0)/2
  ·linear_combination cH 0 0
 let g:=uA (nA m X) (nA n X)+nA n X 0+nA n X 1
 let d:=uA (nA m Y) (nA n X)
 have c (k:ℂ):120*f (aB X)^4=
   (g+k*d)*cG (aT 0 (Z 0 k)) (aT 1 (Z 0 k)):=by
  have e:=nB o j (q 0 k) (r 0 k);rw[p _ (u 0 k)] at e;have op:aB (Z 0 k)=aB X:=by simp[Z,show aB Y=0 from b.1.2]
  rw[op] at e;simp only[g,d,Z,iP,one_smul,zero_smul,add_zero,map_add,map_smul,v,F,smul_zero,w,Pi.zero_apply,uA,Pi.add_apply,Pi.smul_apply,smul_eq_mul,map_zero] at e ⊢
  linear_combination e
 have h:=c (-g/d);rw[div_mul_cancel₀ _ i,add_neg_cancel,zero_mul] at h;exact(pow_eq_zero_iff (by decide:(4:ℕ)≠0)).mp ((mul_eq_zero.mp h).resolve_left (by norm_num))
lemma aFt {x d:iZ} (a:d≠0) (h:det x d=0):
  ∃k:ℂ,x=k•d:=by
 obtain⟨i,b⟩:=Function.ne_iff.mp a;have c:d i≠0:=b;refine⟨x i/d i,funext fun j=> ?_⟩;change x j=x i/d i*d j;field_simp;fin_cases i<;>fin_cases j<;>grind [det]
lemma aAe {c x d:iZ} (a:c≠0) (b:det x d≠0):
  ∃k:ℂ,det c (x+k•d)≠0∧uA c (x+k•d)≠0:=by
 have e:c 0≠0∨c 1≠0:=by by_contra! h;apply a;funext i;fin_cases i<;>first | exact h.1 | exact h.2
 by_contra! h;have p (k:ℂ):det c (x+k•d)=0∨uA c (x+k•d)=0:=or_iff_not_imp_left.mpr (h k);simp only[det,uA,Pi.add_apply,Pi.smul_apply,smul_eq_mul] at p b;rcases p 0 with A|A<;>rcases p 1 with B|B<;>rcases p (-1) with C|C<;>grind
lemma aFu (o:uO m n) (L:Submodule ℂ aC):
  Module.finrank ℂ ((S n L).map (nA m))+Module.finrank ℂ ((K L).map (nA n))=Module.finrank ℂ ((K L).map aG):=by
 have e:S n L⊓LinearMap.ker (nA m)=K L⊓LinearMap.ker aG:=by
  ext x;change((x∈K L∧nA n x=0)∧nA m x=0)↔(x∈K L∧aG x=0)
  rcases o with⟨rfl,rfl⟩|⟨rfl,rfl⟩<;>simp[funext_iff,Fin.forall_fin_succ,aG,nA,Fin.castLE]<;>tauto
 have u:=Aq.iI (S n L) (nA m);have v:=Aq.iI (K L) (nA n);have w:=Aq.iI (K L) aG;rw[e] at u;change _+Module.finrank ℂ (S n L)=_ at v;omega
lemma xE (o:uO m n) {L:Submodule ℂ aC}
  {f:Module.Dual ℂ jH} (O:Law L f) (P:Module.finrank ℂ ((K L).map aG)=2)
  (g:∀{X Y:aC} {j:Fin 3},X∈E n L→Y∈S n L→aT m X=jJ j→
    det (nA m Y) (nA n X)≠0→uA (nA m Y) (nA n X)≠0→f (aB X)=0)
  {X:aC} (s:X∈E n L) (j:Fin 3) (y:aT m X=jJ j):
  f (aB X)=0:=by
 by_contra r
 let C:=(S n L).map (nA m)
 let D:=(K L).map (nA n)
 have b:Module.finrank ℂ C+Module.finrank ℂ D =2:=(aFu o L).trans P;have a:nA n X∉D:=by
  rintro⟨W,d,e⟩;have z:aB W=0:=d.2;have B:=(E n L).sub_mem s (kZ o d).2;have l:nA n (X-W)=0:=by rw[map_sub,e,sub_self]
  have N:aT n (X-W)=0:=B.2;have u (j:Fin 5):(X-W) (n,j)=0:=Fin.addCases (m:=2) (n:=3) (motive:=fun k=>(X-W) (n,k)=0) (congrFun l) (congrFun N) j;have zero:aO (X-W)=0:=Finset.sum_eq_zero fun e _=>Finset.prod_eq_zero (Finset.mem_univ n) (u _)
  rw[O _ B.1,map_sub,z,sub_zero] at zero;exact(mul_ne_zero (by norm_num) (pow_ne_zero 4 r)) zero
 have J:D ≠ ⊤ :=fun p=>a (p▸Submodule.mem_top)
 have v:Module.finrank ℂ iZ=2:=Module.finrank_fin_fun ℂ;have w:=Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr J);rw[finrank_top,v] at w;by_cases x:D = ⊥
 ·have q:C= ⊤ :=by
   rw[x,finrank_bot,add_zero] at b;exact Submodule.eq_top_of_finrank_eq (b.trans v.symm)
  have V:nA n X≠0:=fun h=>a (h▸D.zero_mem)
  obtain⟨c,M,A⟩:∃c:iZ,det c (nA n X)≠0∧uA c (nA n X)≠0:=by obtain⟨i,l⟩:=Function.ne_iff.mp V;refine⟨Pi.single i.rev 1,?_⟩;fin_cases i<;>simpa[det,uA,Fin.rev,Pi.single_apply] using And.intro l l
  obtain⟨Y,t,e⟩:=(show c∈C by rw[q];trivial)
  exact r (g s t y (e▸M) (e▸A))
 ·obtain⟨_,⟨W,d,rfl⟩,U⟩:=Submodule.exists_mem_ne_zero_of_ne_bot x;have R:C≠ ⊥ :=by intro p;rw[p,finrank_bot,zero_add] at b;omega
  obtain⟨_,⟨Y,t,rfl⟩,T⟩:=Submodule.exists_mem_ne_zero_of_ne_bot R;have F:det (nA n X) (nA n W)≠0:=by intro h;obtain⟨k,e⟩:=aFt U h;exact a (e▸D.smul_mem k ⟨W,d,rfl⟩)
  obtain⟨k,Z,A⟩:=aAe T F;have Q:aB W=0:=d.2;have G:aB (X+k•W)=aB X:=by rw[map_add,map_smul,Q,smul_zero,add_zero]
  have H:aT m (X+k•W)=jJ j:=by rw[map_add,map_smul,show aT m W=0 from(kZ o d).1,smul_zero,add_zero];exact y
  have h:=g ((E n L).add_mem s ((E n L).smul_mem k (kZ o d).2))
   t H (by rwa [map_add,map_smul]) (by rwa [map_add,map_smul])
  exact r (G▸h)
lemma sR {L:Submodule ℂ aC} (hL:aD L) (q:p L 2 3=7)
  {U:aC} (r:U∈L) (c:dY U) (h:dt U 0 1≠0):
  (V L).map aB≠ ⊤ :=by
 intro l;obtain⟨f,-,h1,recover⟩:=(nN hL q r c h).2;have g:Law L f:=by intro Z F;obtain⟨v,w⟩:=Am.sQ.mp F;rw[recover Z v w,fU hL w]
 have u:U∈K L:=⟨Submodule.mem_sup_left r,funext fun p=>c _ _ (Or.inl (by change 2≤2+p.1.val;omega))⟩
 have t:=(iK q (cB hL q r c h)).2.2.1;have d:Module.finrank ℂ jH=6:=by simp[jH]
 change Module.finrank ℂ ((V L).map aB)+Module.finrank ℂ ((K L).map aG)=8 at t;rw[l,finrank_top,d] at t
 let z (i:Fin 2) (j:Fin 3):jH:=fun v=>if v.1=i then jJ j v.2 else 0
 have b (i:Fin 2) (j:Fin 3):f (z i j)=0:=by
  have x:z i j∈(V L).map aB:=by rw[l];trivial
  obtain⟨X,s,e⟩:=x;rw[←e];have a {m n:Fin 4} (o:uO m n) (A:aT m X=jJ j) (B:aT n X=0):=
   xE o g (by omega)
    (fun s C y=>uB o u c h g l s C _ y) (show X∈E n L from⟨s,B⟩) j A
  fin_cases i
  ·exact a (m:=2) (n:=3) (Or.inl ⟨rfl,rfl⟩) (funext fun k=>congrFun e (0,k)) (funext fun k=>congrFun e (1,k))
  ·exact a (m:=3) (n:=2) (Or.inr ⟨rfl,rfl⟩) (funext fun k=>congrFun e (1,k)) (funext fun k=>congrFun e (0,k))
 have aS:(∑i:Fin 2,∑j:Fin 3,z i j)=1:=by funext ⟨i,j⟩;fin_cases i<;>fin_cases j<;>norm_num[Fin.sum_univ_two,Fin.sum_univ_three,z,jJ]
 rw[←aS,map_sum] at h1;simp only[map_sum,b,Finset.sum_const_zero] at h1;exact zero_ne_one h1
end Ac.Bc
namespace Ac.Ao
open Aa Ac.Ae Ac.Aq Finset
def mE (j:Fin 3) (z:ℂ):jH:=fun p=>if p.2=j then z else 0
def pH (B:aC) (r:Fin 4) (j:Fin 3):ℂ:=
 (if j=0 then 0 else B (r,2))+(if j=1 then 0 else B (r,3))+
   (if j=2 then 0 else B (r,4))
def dP (X U:aC) (r:Fin 4):ℂ:=U (r,0)*(X (2,1)+X (3,1))+U (r,1)*(X (2,0)+X (3,0))
def mF (X U B:aC) (j:Fin 3):ℂ:=dP X U 1*pH B 0 j+dP X U 0*pH B 1 j
lemma xZ (f:Fin 5→ℂ):
  ∑i,f i=f 0+f 1+f 2+f 3+f 4:=by
 simp[Fin.sum_univ_succ];ring
set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
lemma pI (X U:aC) (j:Fin 3) (z t:ℂ)
  (a:aB X=mE j z)
  (i:∀r c,(2≤ r.val∨2≤ c.val)→U (r,c)=0):
  aO (X+t•U)-aO X=t*z*mF X U X j:=by
 have b:X (2,2)=(if(0:Fin 3)=j then z else 0):=congrFun a (0,0);have d:X (2,3)=(if(1:Fin 3)=j then z else 0):=congrFun a (0,1);have e:X (2,4)=(if(2:Fin 3)=j then z else 0):=congrFun a (0,2);have f:X (3,2)=(if(0:Fin 3)=j then z else 0):=congrFun a (1,0);have g:X (3,3)=(if(1:Fin 3)=j then z else 0):=congrFun a (1,1);have h:X (3,4)=(if(2:Fin 3)=j then z else 0):=congrFun a (1,2);rw[cK,cK];fin_cases j<;>
  simp(config:={decide:=true}) (disch:=decide) only[xZ,ite_true,ite_false,
   Pi.add_apply,Pi.smul_apply,smul_eq_mul,i,b,d,e,f,g,h,
   zero_add,add_zero,zero_mul,mul_zero,mF,dP,pH]<;>ring
lemma mG {L:Submodule ℂ aC} (hL:aD L)
  {X U:aC} {s z:ℂ} {j:Fin 3}
  (a:aR L X s) (b:U∈L)
  (f:∀r c,(2≤ r.val∨2≤ c.val)→U (r,c)=0)
  (e:aB X=mE j z):
  z*mF X U X j=0:=by
 have d:=(uH hL a b a).2 (1:ℂ);simpa only[one_mul,d,sub_self] using(pI X U j z 1 e f).symm
lemma pJ {L:Submodule ℂ aC} (hL:aD L)
  {X U Y:aC} {s z:ℂ} {j:Fin 3}
  (e:aR L X s) (d:U∈L) (m:Y∈L)
  (i:∀r c,(2≤ r.val∨2≤ c.val)→U (r,c)=0)
  (h:aB X=mE j z) (n:aB Y=0)
  (k:Y (2,0)+Y (3,0)=0) (l:Y (2,1)+Y (3,1)=0):
  z*mF X U Y j=0:=by
 have g:aR L Y 0:=⟨Y,m,by funext p;simp[aM]⟩
 have f:aR L (X+Y) s:=by simpa using iJ e g 1
 have a:aB (X+Y)=mE j z:=by rw[map_add,h,n,add_zero]
 have A:=mG hL f d i a;have D:=mG hL e d i h;have w (r:Fin 4):dP (X+Y) U r=dP X U r:=by simp only[dP,Pi.add_apply];linear_combination U (r,0)*l+U (r,1)*k
 have b (r:Fin 4):pH (X+Y) r j=pH X r j+pH Y r j:=by fin_cases j<;>simp(config:={decide:=true}) only[pH,ite_true,ite_false,Pi.add_apply]<;>ring
 simp only[mF,w,b] at A D ⊢
 linear_combination A-D
end Ac.Ao
namespace Ac.Ak
open Aa Ae Aq
abbrev iA:=Fin 3→ℂ
abbrev iZ:=Fin 2→ℂ
abbrev V (L:Submodule ℂ aC):=L⊔Submodule.span ℂ {(1:aC)}
abbrev K (L:Submodule ℂ aC):=aP L
abbrev fK (L:Submodule ℂ aC):=(K L).map aG
abbrev nD (i:Fin 2):jH→ₗ[ℂ] iA:=LinearMap.funLeft ℂ ℂ (fun j=>(i,j))
def kH (r:iA):jH:=fun a=>r a.2
def dH (j:Fin 3):iA:=Pi.single j 1
def mH (i:Fin 2):iZ:=Pi.single i 1
def gH (c:iZ):bE:= ![c 0,c 1,-c 0,-c 1]
lemma nE {L:Submodule ℂ aC} {Y:aC} (a:Y∈V L):
  ∃s,aR L Y s:=by
 obtain⟨t,b,w,c,rfl⟩:=Submodule.mem_sup.mp a;obtain⟨s,rfl⟩:=Submodule.mem_span_singleton.mp c;exact⟨s,t,b,by funext i;change t i+s*1=s+t i;ring⟩
def nF (p:Module.Dual ℂ iA) (a b:ℂ):Module.Dual ℂ jH:=a•p.comp (nD 0)+b•p.comp (nD 1)
lemma qO {L:Submodule ℂ aC} {p:Module.Dual ℂ iA} {a b:ℂ}
  (f:Module.finrank ℂ ((V L).map aB)=5) (d:nF p a b≠0)
  (h:∀X∈V L,nF p a b (aB X)=0):
  (V L).map aB=LinearMap.ker (nF p a b):=by
 apply Submodule.eq_of_le_of_finrank_le (by rintro _ ⟨X,c,rfl⟩;exact h X c);have e:=Module.Dual.finrank_ker_add_one_of_ne_zero d;have:Module.finrank ℂ jH=6:=by simp[jH]
 omega
lemma yC {L:Submodule ℂ aC} {p:Module.Dual ℂ iA} {a b:ℂ}
  (k:Module.finrank ℂ ((V L).map aB)=5) (g:nF p a b≠0)
  (h:∀X∈V L,nF p a b (aB X)=0):
  p
   1=0∨(a≠0∧b= -a∧∀z:jH,
   z∈(V L).map aB↔p (nD 0 z)=p (nD 1 z)):=by
 by_cases i:p 1=0
 ·exact Or.inl i
 right;have e:a*p 1+b*p 1=0:=h 1 (Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _)));have j:=(mul_eq_zero.mp (show(a+b)*p 1=0 by linear_combination e)).resolve_right i;have c:b= -a:=by linear_combination j
 have f:a≠0:=by rintro rfl;apply g;simp[nF,c]
 refine⟨f,c,fun z=> ?_⟩;rw[qO k g h];change a*p (nD 0 z)+b*p (nD 1 z)=0↔_;rw[c];constructor
 ·intro d;exact sub_eq_zero.mp ((mul_eq_zero.mp (show a*(p (nD 0 z)-p (nD 1 z))=0 by linear_combination d)).resolve_left f)
 ·intro d;rw[d];ring
lemma lA {L:Submodule ℂ aC} (e:p L 2 3=7)
  (d:(1:jH)∉L.map aB) (a:Module.finrank ℂ ((V L).map aB)=5):
  Module.finrank ℂ (fK L)=3:=by
 obtain⟨c,_,b,_⟩:=iK e d;rw[c,a] at b;change Module.finrank ℂ ((aP L).map aG)=3;omega
lemma xF {L:Submodule ℂ aC}
  (a:∀j,kH (dH j)∈(V L).map aB)
  {f:Module.Dual ℂ jH} (g:f 1=1)
  (k:∀Y s,aR L Y s→f (aB Y)=s):
  ∃j X s,aR L X s∧aB X=kH (dH j)∧s≠0:=by
 have e:kH (dH 0)+kH (dH 1)+kH (dH 2)=1:=by funext ⟨i,j⟩;fin_cases j<;>norm_num[kH,dH,Pi.single_apply]
 obtain⟨j,l⟩:∃j,f (kH (dH j))≠0:=by by_contra! c;rw[←e,map_add,map_add,c,c,c] at g;norm_num at g
 obtain⟨X,h,d⟩:=a j;obtain⟨s,b⟩:=nE h;exact⟨j,X,s,b,d,by rwa [←k X s b,d]⟩
lemma xG {X:aC} {j:Fin 3} {i:Fin 2} {t:ℂ}
  (e:aB X=kH (dH j)) (f:aG X=t•gH (mH i)):
  aO X=0:=by
 apply cD X 2 3 (by decide);intro c d q;have a:=congrFun f 0;have b:=congrFun f 1;have g:=congrFun f 2;have h:=congrFun f 3;change X (2,0)=t*mH i 0 at a;change X (2,1)=t*mH i 1 at b;change X (3,0)=t* -mH i 0 at g;change X (3,1)=t* -mH i 1 at h;have k:X (2,2)=dH j 0:=congrFun e (0,0);have l:X (2,3)=dH j 1:=congrFun e (0,1);have m:X (2,4)=dH j 2:=congrFun e (0,2);have n:X (3,2)=dH j 0:=congrFun e (1,0);have o:X (3,3)=dH j 1:=congrFun e (1,1);have p:X (3,4)=dH j 2:=congrFun e (1,2);have xZ (v:Fin 5):v=0∨v=1∨v=2∨v=3∨v=4:=by decide+revert
 rcases xZ c with rfl|rfl|rfl|rfl|rfl<;>rcases xZ d with rfl|rfl|rfl|rfl|rfl<;>first | exact(q rfl).elim | simp only[a,b,g,h,k,l,m,n,o,p]
 all_goals first | (solve | ring) | (solve | fin_cases i<;>norm_num[mH,Pi.single_apply]) |
  fin_cases j<;>norm_num[dH,Pi.single_apply]
lemma aAf {L:Submodule ℂ aC} {X:aC} {s:ℂ} (d:aR L X s)
  {v:bE} (e:aG X-v∈fK L):
  ∃Z,aR L Z s∧aB Z=aB X∧aG Z=v:=by
 obtain⟨Y,b,a⟩:=e;refine⟨X-Y,?_,?_,?_⟩
 ·obtain⟨T,c,rfl⟩:=d;exact⟨T-Y,L.sub_mem c b.1,by funext i;simp only[aM,Pi.sub_apply];ring⟩
 ·rw[map_sub,show aB Y=0 from b.2,sub_zero]
 ·rw[map_sub,a];abel
lemma uC {L:Submodule ℂ aC} (hL:aD L)
  (q:Module.finrank ℂ (fK L)=3)
  {X:aC} {j:Fin 3} {s:ℂ} (n:aR L X s)
  (m:aB X=kH (dH j)) (r:s≠0):
  aG X∉fK L∧∀c,gH c∈fK L:=by
 have a (i:Fin 2) (t:ℂ):aG X-t•gH (mH i)∉fK L:=by intro f;obtain⟨Z,o,l,k⟩:=aAf n f;have e:=(xG (l.trans m) k).symm.trans (fU hL o);exact(mul_ne_zero (by norm_num) (pow_ne_zero 4 r)) e.symm
 have b (i:Fin 2):gH (mH i)∈fK L:=by
  by_contra p;have g:=Submodule.finrank_sup_span_singleton p;rw[q] at g;have d:fK L⊔Submodule.span ℂ {gH (mH i)}= ⊤ :=by apply Submodule.eq_top_of_finrank_eq;exact g.trans (Module.finrank_fin_fun ℂ).symm
  have f:aG X∈fK L⊔Submodule.span ℂ {gH (mH i)}:=by rw[d];trivial
  obtain⟨y,v,w,u,h⟩:=Submodule.mem_sup.mp f;obtain⟨t,rfl⟩:=Submodule.mem_span_singleton.mp u;exact a i t (by rwa [←h,add_sub_cancel_right])
 refine⟨by simpa using a 0 0,fun c=> ?_⟩;have e:gH c=c 0•gH (mH 0)+c 1•gH (mH 1):=by funext i;fin_cases i<;>simp[gH,mH]
 rw[e];exact(fK L).add_mem ((fK L).smul_mem _ (b 0)) ((fK L).smul_mem _ (b 1))
end Ac.Ak
namespace Ac.Ak
open Aa Ae Aq
abbrev aG3:bE→ₗ[ℂ] iZ:=LinearMap.funLeft ℂ ℂ ![0,1]
abbrev aHr:bE→ₗ[ℂ] iZ:=LinearMap.funLeft ℂ ℂ ![2,3]
abbrev sS:bE→ₗ[ℂ] iZ:=aG3+aHr
abbrev G (L:Submodule ℂ aC):=(fK L).map sS
def cE (r t:iA):jH:=fun a=> ![r,t] a.1 a.2
lemma yD {L:Submodule ℂ aC} (a:∀c,gH c∈fK L) (v:bE):
  sS v∈G L↔v∈fK L:=by
 refine⟨?_,fun b=>⟨_,b,rfl⟩⟩;rintro⟨w,d,e⟩;have f:w 0+w 2=v 0+v 2:=congrFun e 0;have g:w 1+w 3=v 1+v 3:=congrFun e 1;have h:v=w+gH ![v 0-w 0,v 1-w 1]:=by funext i;fin_cases i<;>simp[gH]<;>grind
 rw[h];exact(fK L).add_mem d (a _)
lemma xH {L:Submodule ℂ aC} (j:Module.finrank ℂ (fK L)=3)
  {c:iZ} (g:c∉G L):
  ∀w:iZ,∃v∈G L,∃t:ℂ,w=v+t•c:=by
 let x:bE:= ![c 0,c 1,0,0]
 have e:sS x=c:=by funext i;fin_cases i<;>exact add_zero _
 have f:x∉fK L:=fun h=>g ⟨_,h,e⟩
 have d:=Submodule.finrank_sup_span_singleton f;rw[j] at d;have a:fK L⊔Submodule.span ℂ {x}= ⊤ :=Submodule.eq_top_of_finrank_eq (d.trans (Module.finrank_fin_fun ℂ).symm);intro w
 let y:bE:= ![w 0,w 1,0,0]
 have m:sS y=w:=by funext i;fin_cases i<;>exact add_zero _
 have b:y∈fK L⊔Submodule.span ℂ {x}:=by rw[a];trivial
 obtain⟨u,k,v,l,h⟩:=Submodule.mem_sup.mp b;obtain⟨t,rfl⟩:=Submodule.mem_span_singleton.mp l;refine⟨sS u,⟨u,k,rfl⟩,t,?_⟩;rw[←m,←h,map_add,map_smul,e]
lemma rM {X:aC} {L:Submodule ℂ aC} (hL:aD L)
  {s:ℂ} (a:aR L X s) (r:Fin 4) (c:∀j,X (r,j)=0):s=0:=by
 by_contra b;have d:aO X=0:=Finset.sum_eq_zero fun e _=>Finset.prod_eq_zero (Finset.mem_univ r) (c (e r))
 exact(mul_ne_zero (by norm_num) (pow_ne_zero 4 b)) ((fU hL a).symm.trans d)
lemma yF {L:Submodule ℂ aC} (hL:aD L)
  (o:∀c,gH c∈fK L) {X:aC} {s:ℂ} (n:aR L X s)
  (i:Fin 2) (p:nD i (aB X)=0):s=0:=by
 let r:=Fin.natAdd 2 i
 let c:iZ:= ![X (r,0),X (r,1)]
 let d:=if i=0 then c else-c
 obtain⟨Y,b,e⟩:=o d;have z (j:Fin 3):X (r,Fin.natAdd 2 j)=0:=congrFun p j;have v (j:Fin 3):Y (r,Fin.natAdd 2 j)=0:=congrFun (show aB Y=0 from b.2) (i,j);obtain⟨T,m,a⟩:=n;refine rM hL (X:=X-Y) (s:=s) ?_ r ?_
 ·refine⟨T-Y,L.sub_mem m b.1,?_⟩;rw[a];funext k;simp only[Pi.sub_apply,aM];ring
 ·intro j;change X (r,j)-Y (r,j)=0;apply sub_eq_zero.mpr;have f:Y (2,0)=d 0:=congrFun e 0;have g:Y (2,1)=d 1:=congrFun e 1;have h:Y (3,0)= -d 0:=congrFun e 2;have l:Y (3,1)= -d 1:=congrFun e 3;fin_cases j
  ·fin_cases i
   ·exact f.symm
   ·simpa[d,c,r] using h.symm
  ·fin_cases i
   ·exact g.symm
   ·simpa[d,c,r] using l.symm
  ·exact(z 0).trans (v 0).symm
  ·exact(z 1).trans (v 1).symm
  ·exact(z 2).trans (v 2).symm
lemma qE {L:Submodule ℂ aC} (hL:aD L)
  (l:∀c,gH c∈fK L) {p:Module.Dual ℂ iA}
  (d:∀z:jH,z∈(V L).map aB↔p (nD 0 z)=p (nD 1 z))
  {f:Module.Dual ℂ jH} (m:∀Y s,aR L Y s→f (aB Y)=s)
  {z:iA} (n:f (kH z)≠0):p z≠0:=by
 intro h;have aAb (u:jH) (i:Fin 2) (hu:u∈(V L).map aB) (h0:nD i u=0):
   f u=0:=by
  obtain⟨Y,k,rfl⟩:=hu;obtain⟨s,g⟩:=nE k;exact(m Y s g).trans (yF hL l g i h0)
 have a:f (cE z 0)=0:=aAb _ 1 ((d _).2 (h.trans (map_zero p).symm)) rfl;have b:f (cE 0 z)=0:=aAb _ 0 ((d _).2 ((map_zero p).trans h.symm)) rfl;have e:kH z=cE z 0+cE 0 z:=by funext ⟨i,j⟩;fin_cases i<;>simp[kH,cE]
 exact n (by rw[e,map_add,a,b,add_zero])
end Ac.Ak
namespace Ac.Ak
open Aa Ae Aq
def H (Y:aC) (r:Fin 4) (z:iA):ℂ:=Y (r,2)*(z 1+z 2)+Y (r,3)*(z 0+z 2)+Y (r,4)*(z 0+z 1)
def cH (U Y:aC) (z:iA) (c:iZ):ℂ:=(U (1,0)*c 1+U (1,1)*c 0)*H Y 0 z+(U (0,0)*c 1+U (0,1)*c 0)*H Y 1 z
abbrev ca (Y:aC):=aG3 (aG Y)
abbrev cb (Y:aC):=aHr (aG Y)
abbrev cs (Y:aC):=sS (aG Y)
lemma aFv (Y Z:aC):cs (Y+Z)=cs Y+cs Z:=(sS.comp aG).map_add _ _
lemma aG4 (Y Z:aC):ca (Y+Z)=ca Y+ca Z:=(aG3.comp aG).map_add _ _
abbrev iQ (U:aC):=∀r c,(2≤ r.val∨2≤ c.val)→U (r,c)=0
abbrev rN (U:aC):=U (0,0)*U (1,1)-U (0,1)*U (1,0)
lemma rO {L:Submodule ℂ aC} (hL:aD L) {U Y:aC}
  (l:U∈L) (o:iQ U) (b:Y∈K L)
  {r v:iA} (m:cE r v∈(V L).map aB):
  cH U Y r (cb Y)+cH U Y v (ca Y)=0:=by
 obtain⟨T,k,e⟩:=m;obtain⟨s,n⟩:=nE k;have p:aR L Y 0:=⟨_,b.1,by funext i;simp[aM]⟩
 have a:=dC hL p l n o b.2;have c:T (2,2)=r 0:=congrFun e (0,0);have d:T (2,3)=r 1:=congrFun e (0,1);have f:T (2,4)=r 2:=congrFun e (0,2);have g:T (3,2)=v 0:=congrFun e (1,0);have h:T (3,3)=v 1:=congrFun e (1,1);have j:T (3,4)=v 2:=congrFun e (1,2);simp only[iH,fL,c,d,f,g,h,j] at a;change cH U Y r ![Y (3,0),Y (3,1)]+cH U Y v ![Y (2,0),Y (2,1)]=0;simp[cH,H];linear_combination a
lemma aBl (U Y:aC) (z:iA) (a b:iZ):cH U Y z (a+b)=cH U Y z a+cH U Y z b:=by simp[cH];ring
lemma aEg (U Y:aC) (z:iA) (t:ℂ) (a:iZ):cH U Y z (t•a)=t*cH U Y z a:=by simp[cH];ring
lemma yU (U Y W:aC) (z:iA) (c:iZ):cH U (Y+W) z c=cH U Y z c+cH U W z c:=by simp[cH,H];ring
lemma xI {L:Submodule ℂ aC} {U:aC}
  (a:∀Z∈K L,∀z,cH U Z z (cs Z)=0)
  {Y:aC} (d:Y∈K L) (f:cs Y=0) (z:iA):
  ∀c∈G L,cH U Y z c=0:=by
 rintro _ ⟨_,⟨Z,b,rfl⟩,rfl⟩;have h:=a (Z+Y) ((K L).add_mem b d) z;have e:cs (Z+Y)=cs Z:=by rw[aFv,f,add_zero]
 rw[e,yU,a Z b z,zero_add] at h;exact h
lemma aBm {L:Submodule ℂ aC} {U Y:aC} {z:iA}
  (e:Module.finrank ℂ (fK L)=3) (b:∀c∈G L,cH U Y z c=0)
  {a:iZ} (d:a∉G L) (h:cH U Y z a=0):∀c,cH U Y z c=0:=by
 intro c;obtain⟨v,f,t,rfl⟩:=xH e d c;simp only[aBl,aEg,b _ f,h,mul_zero,add_zero]
lemma uD {L:Submodule ℂ aC} {U:aC} {p:Module.Dual ℂ iA}
  (y:∀c,gH c∈fK L) (s:Module.finrank ℂ (fK L)=3)
  (f:∀Y∈K L,∀r v,p r=p v→cH U Y r (cb Y)+cH U Y v (ca Y)=0)
  {t:iZ} (m:t∉G L) {j:Fin 3} (A:p (dH j)≠0)
  (l:∀Y∈K L,cs Y=0→cH U Y (dH j) t=0):
  ∀Y∈K L,cs Y=0→∀z c,cH U Y z c=0:=by
 have e (Y) (a:Y∈K L) (z:iA):cH U Y z (cs Y)=0:=by change cH U Y z (ca Y+cb Y)=0;rw[aBl,add_comm];exact f Y a z z rfl
 have single (Y) (a:Y∈K L) (b:cs Y=0):∀c,cH U Y (dH j) c=0:=aBm s (xI e a b _) m (l Y a b);have d (Y) (a:Y∈K L) (b:cs Y=0) (g:ca Y∉G L) (z:iA):
   ∀c,cH U Y z c=0:=by
  let k:=p z/p (dH j)
  have x:p (k•dH j)=p z:=by rw[map_smul,smul_eq_mul,show k=_ from rfl,div_mul_cancel₀ _ A]
  have h:=f Y a (k•dH j) z x;have C:cH U Y (k•dH j) (cb Y)=k*cH U Y (dH j) (cb Y):=by simp[cH,H];ring
  rw[C,single Y a b,mul_zero,zero_add] at h;exact aBm s (xI e a b _) g h
 obtain⟨W,q,u⟩:=y t;have o:ca W=t:=by rw[ca,u];funext i;fin_cases i<;>rfl
 have w:cs W=0:=by rw[cs,u];funext i;fin_cases i<;>exact add_neg_cancel _
 intro Y a b z c;by_cases g:ca Y∈G L
 ·have n:ca (Y+W)∉G L:=by
   rw[aG4,o];intro B;exact m ((G L).add_mem_iff_right g |>.mp B)
  have E:cs (Y+W)=0:=by rw[aFv,b,w,add_zero]
  have h:=d _ ((K L).add_mem a q) E n z c;rw[yU,d _ q w (o▸m) z c,add_zero] at h;exact h
 ·exact d Y a b g z c
lemma aCn {U Y:aC} (f:rN U≠0)
  (h:∀z c,cH U Y z c=0):
  ∀(r:Fin 2) (j:Fin 3),Y (Fin.castLE (by decide) r,Fin.natAdd 2 j)=0:=by
 have d (z:iA):H Y 0 z=0∧H Y 1 z=0:=by
  have a:=h z ![1,0];have b:=h z ![0,1];simp[cH] at a b;constructor
  ·apply(mul_eq_zero.mp (show rN U*H Y 0 z=0 by unfold rN;linear_combination U (0,0)*a-U (0,1)*b)).resolve_left f
  ·apply(mul_eq_zero.mp (show rN U*H Y 1 z=0 by unfold rN;linear_combination U (1,1)*b-U (1,0)*a)).resolve_left f
 intro r j;have e:∀z,H Y (Fin.castLE (by decide) r) z=0:=by
  intro z;fin_cases r
  ·exact(d z).1
  ·exact(d z).2
 have a:=e ![1,0,0];have b:=e ![0,1,0];have c:=e ![0,0,1];simp[H] at a b c;fin_cases j
 ·exact(show Y (_,2)=0 by linear_combination(b+c-a)/2)
 ·exact(show Y (_,3)=0 by linear_combination(a+c-b)/2)
 ·exact(show Y (_,4)=0 by linear_combination(a+b-c)/2)
end Ac.Ak
namespace Ac.Ak
open Aa Ae Aq
set_option maxHeartbeats 1000000 in
lemma xJ {L:Submodule ℂ aC} (hL:aD L) (w:p L 2 3=7)
  {U:aC} (n:U∈L) (q:iQ U) (t:rN U≠0)
  (E:Module.finrank ℂ ((V L).map aB)=5)
  {p:Module.Dual ℂ iA}
  (m:∀z:jH,z∈(V L).map aB↔p (nD 0 z)=p (nD 1 z)):
  (∀c,gH c∈fK L)∧∀Y∈K L,cs Y=0→
    ∀(r:Fin 2) (j:Fin 3),Y (Fin.castLE (by decide) r,Fin.natAdd 2 j)=0:=by
 have u:=cB hL w n q t;have a:=lA w u E;obtain⟨f,_,A,b⟩:=iU u;obtain⟨j,X,s,o,k,J⟩:=xF (L:=L) (fun j=>(m _).2 rfl) A b;obtain⟨C,g⟩:=uC hL a o k J;have B:p (dH j)≠0:=qE hL g m b (by rwa [←k,b _ _ o]);have dd:aB X=Ao.mE j 1:=by rw[k];funext ⟨i,l⟩;simp[kH,dH,Pi.single_apply,Ao.mE]
 have F:cs X∉G L:=fun h=>C ((yD g _).1 h)
 have cG (Z) (e:Z∈K L) (r v:iA) (d:p r=p v):
   cH U Z r (cb Z)+cH U Z v (ca Z)=0:=
  rO hL n q e ((m (cE r v)).2 d)
 refine⟨g,fun Y x y=>aCn t (uD g a cG F B ?_ Y x y)⟩;intro Z e d;have h:=Ao.pJ hL o n e.1 q dd e.2 (congrFun d 0) (congrFun d 1);rw[one_mul] at h;change cH U Z (dH j) ![X (2,0)+X (3,0),X (2,1)+X (3,1)]=0;fin_cases j<;>simpa[cH,H,dH,Pi.single_apply,Ao.mF,Ao.dP,Ao.pH,add_comm,add_left_comm,add_assoc] using h
lemma nG {L:Submodule ℂ aC} (hL:aD L) (s:p L 2 3=7)
  {U:aC} (g:U∈L) (l:iQ U) (k:rN U≠0)
  (w:Module.finrank ℂ ((V L).map aB)=5)
  {p:Module.Dual ℂ iA}
  (o:∀z:jH,z∈(V L).map aB↔p (nD 0 z)=p (nD 1 z)):False:=by
 obtain⟨r,y⟩:=xJ hL s g l k w o
 let S:=K L⊓LinearMap.ker (sS.comp aG)
 apply Az.kO (S:=S) hL (fun _ d=>d.1.1)
 ·intro x d i j B;have m:aB x=0:=d.1.2;have t:=y x d.1 d.2;have f (v:Fin 3):x (i,Fin.natAdd 2 v)=0:=by
   fin_cases i
   ·exact t 0 v
   ·exact t 1 v
   ·exact congrFun m (0,v)
   ·exact congrFun m (1,v)
  fin_cases j<;>first | contradiction | exact f 0 | exact f 1 | exact f 2
 ·intro x d j;have h:cs x=0:=d.2;have e:=congrFun h j;fin_cases j<;>apply eq_neg_of_add_eq_zero_right<;>exact e
 ·intro c;obtain⟨Y,q,e⟩:=r c;have a:ca Y=c:=by rw[ca,e];funext i;fin_cases i<;>rfl
  have b:cs Y=0:=by rw[cs,e];funext i;fin_cases i<;>exact add_neg_cancel _
  refine⟨Y,⟨q,b⟩,?_⟩;funext j;fin_cases j
  ·exact congrFun a 0
  ·exact congrFun a 1
 ·have u (i:Fin 2) (j:Fin 5):U (Fin.natAdd 2 i,j)=0:=
   l _ _ (Or.inl (by change 2≤2+i.val;omega))
  have n:aG U=0:=by funext i;fin_cases i<;>first | exact u 0 0 | exact u 0 1 | exact u 1 0 | exact u 1 1
  refine⟨U,⟨⟨g,funext fun A=>u A.1 _⟩,?_⟩,?_,?_⟩
  ·change sS (aG U)=0;rw[n,map_zero]
  ·funext j;exact u 0 _
  ·rintro rfl;exact k (by simp[rN])
end Ac.Ak
namespace Ac.Ak
open Aa Ae Aq
def yV (e:ℂ) (x:bE):ℂ:=x 0*x 3+e*x 1*x 2
def aCo (e:ℂ):LinearMap.BilinForm ℂ bE:=
 LinearMap.mk₂ ℂ (fun x y=>x 0*y 3+x 3*y 0+e*(x 1*y 2+x 2*y 1))
  (fun _ _ _=>by simp;ring) (fun _ _ _=>by simp;ring)
  (fun _ _ _=>by simp;ring) (fun _ _ _=>by simp;ring)
lemma sT (S:Submodule ℂ bE) (m:Module.finrank ℂ S=3)
  (e:ℂ) (k:e≠0):∃v∈S,yV e v≠0:=by
 by_contra! h;have f:(aCo e).Nondegenerate:=by
  constructor<;>intro v g<;>
   have a:=g ![1,0,0,0]<;>have b:=g ![0,1,0,0]<;>
   have c:=g ![0,0,1,0]<;>have d:=g ![0,0,0,1]<;>
   simp[aCo,k] at a b c d<;>
   funext i<;>fin_cases i<;>first | exact a | exact b | exact c | exact d
 have j:S≤(aCo e).orthogonal S:=by
  intro v g w l;have A:=h _ (S.add_mem l g);have B:=h _ l;have C:=h _ g;simp[aCo,yV] at A B C ⊢
  linear_combination A-B-C
 have d:=Submodule.finrank_mono j;rw[LinearMap.BilinForm.finrank_orthogonal f,m,Module.finrank_fin_fun] at d;omega
lemma aG5 {a b c d e f:ℂ} (g:a≠0)
  (h:∀t:ℂ,(a*t^2+b*t+c)*(d*t^2+e*t+f)=0):f=0:=by
 have A:a*d=0:=by linear_combination(h (-2)-4*h (-1)+6*h 0-4*h 1+h 2)/24
 obtain rfl:=(mul_eq_zero.mp A).resolve_left g;have B:a*e=0:=by linear_combination(h 2-2*h 1+2*h (-1)-h (-2))/12
 obtain rfl:=(mul_eq_zero.mp B).resolve_left g;apply(mul_eq_zero.mp (show a*f=0 by linear_combination(h 1+h (-1)-2*h 0)/2)).resolve_left g
lemma uP {L:Submodule ℂ aC} (p:Module.finrank ℂ (fK L)=3)
  {e:ℂ} (f:e≠0) {g:aC→ℂ}
  (n:∀Y W,∃d b:ℂ,∀t:ℂ,g (Y+t•W)=d*t^2+b*t+g Y)
  (h:∀Y∈K L,yV e (aG Y)≠0→ g Y=0):
  ∀Y∈K L,g Y=0:=by
 obtain⟨_,⟨W,k,rfl⟩,o⟩:=sT (fK L) p e f;intro Y l;obtain⟨d,b,m⟩:=n Y W
 let q (v:aC):=yV e (aG v)
 apply aG5 (a:=q W) (b:=q (Y+W)-q Y-q W) (c:=q Y) (d:=d) (e:=b) o;intro t;have j:q (Y+t•W)=q W*t^2+(q (Y+W)-q Y-q W)*t+q Y:=by simp only[q,yV,map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul];ring
 rw[←j,←m];by_cases i:q (Y+t•W)=0
 ·rw[i,zero_mul]
 ·rw[h _ ((K L).add_mem l ((K L).smul_mem _ k)) i,mul_zero]
lemma xK {L:Submodule ℂ aC} (hL:aD L) (d:Module.finrank ℂ (fK L)=3):
  ∀Y∈K L,Aj.eM Y=0:=by
 have h:=uP (L:=L) d (e:=1) one_ne_zero (g:=dB) (by
  intro Y W;refine⟨dB W,dB (Y+W)-dB Y-dB W,?_⟩;intro t;simp[dB];ring) (by
  intro Y a c;have b:=tC hL a.1;rw[eW a.2] at b;apply(mul_eq_zero.mp b).resolve_left;simpa[per,yV] using c)
 intro Y a;convert h Y a using 1;unfold Aj.eM Aj.bC dB;ring
lemma qP {L:Submodule ℂ aC} (hL:aD L) {U:aC}
  (g:U∈L) (l:iQ U) (o:rN U≠0)
  (s:Module.finrank ℂ (fK L)=3)
  (m:cE 1 0∈(V L).map aB) (n:cE 0 1∈(V L).map aB)
  (r:Fin 2):∀Y∈K L,Aj.bC Y (Fin.castLE (by decide) r)=0:=by
 apply uP s (e:= -1) (by norm_num)
 ·intro Y W;refine⟨0,Aj.bC W (Fin.castLE (by decide) r),?_⟩;intro t;simp[Aj.bC];ring
 intro Y j q;have A:=rO hL g l j m;have B:=rO hL g l j n
 let x:=Aj.bC Y 0
 let y:=Aj.bC Y 1
 have h (i:Fin 4) (h':cH U Y 1 ![Y (i,0),Y (i,1)]=0):
   Y (i,1)*(U (1,0)*x+U (0,0)*y)+Y (i,0)*(U (1,1)*x+U (0,1)*y)=0:=by
  simp[cH,H] at h';simp[x,y,Aj.bC];linear_combination h'/2
 have z (c:iZ):cH U Y 0 c=0:=by simp[cH,H]
 rw[z,add_zero] at A;rw[z,zero_add] at B;have k:Y (2,1)*Y (3,0)-Y (2,0)*Y (3,1)≠0:=by intro p;apply q;change Y (2,0)*Y (3,1)+ -1*Y (2,1)*Y (3,0)=0;linear_combination-p
 obtain⟨a,b⟩:=Aq.yL _ _ _ _ _ _ k (h 2 B) (h 3 A);obtain⟨d,f⟩:=Aq.yL _ _ _ _ _ _
  (show U (1,0)*U (0,1)-U (0,0)*U (1,1)≠0 from fun e=>o (by unfold rN;linear_combination-e)) a b
 fin_cases r
 ·exact d
 ·exact f
end Ac.Ak
namespace Ac.Ak
open Aa Ae Aq
lemma nS {L:Submodule ℂ aC} (hL:aD L) (N:aX L=8)
  (q:p L 2 3=7) {U:aC} (n:U∈L) (r:iQ U) (o:rN U≠0)
  (E:Module.finrank ℂ ((V L).map aB)=5)
  (y:∀Y∈K L,Aj.bC Y 0=0) (z:∀Y∈K L,Aj.bC Y 1=0):False:=by
 have C:=cB hL q n r o;have A:=lA q C E;have H:aX (K L)=4:=by have d:=Aq.iI L aB;have e:=rA L;change Module.finrank ℂ (L.map aB)+aX (K L)=aX L at d;change Module.finrank ℂ (L.map aB)+Module.finrank ℂ (fK L)=p L 2 3 at e;omega
 let Z:=K L⊓LinearMap.ker aG
 have m:aX Z=1:=by have d:=Aq.iI (K L) aG;change Module.finrank ℂ (fK L)+aX Z=aX (K L) at d;omega
 have u:Aj.eV U≠0:=by intro h;have a:U (0,0)=0:=congrFun h (0,0);have b:U (0,1)=0:=congrFun h (0,1);exact o (by simp[rN,a,b])
 have g (i:Fin 2) (j:Fin 5):U (Fin.natAdd 2 i,j)=0:=r _ _ (Or.inl (by change 2≤2+i.val;omega));have B:U∈Z:=by
  refine⟨⟨n,funext fun G=>g G.1 _⟩,?_⟩;change aG U=0;funext i;fin_cases i<;>first
   | exact g 0 0 | exact g 0 1 | exact g 1 0 | exact g 1 1
 have l:Submodule.span ℂ {U}=Z:=by apply Submodule.eq_of_le_of_finrank_le (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr B));rw[finrank_span_singleton (show U≠0 from fun x=>u (x▸map_zero _))];exact m.le
 have t:Function.Injective (Aj.eV.domRestrict (K L)):=by
  apply LinearMap.ker_eq_bot.mp;apply le_antisymm _ bot_le;rintro⟨Y,k⟩ c;have f:Aj.eV Y=0:=c;have v:Y∈Z:=by
   refine⟨k,?_⟩;change aG Y=0;funext i;fin_cases i<;>first
                                   | exact congrFun f (2,0) | exact congrFun f (2,1)
                                   | exact congrFun f (3,0) | exact congrFun f (3,1)
  rw[←l] at v;obtain⟨s,rfl⟩:=Submodule.mem_span_singleton.mp v;rw[map_smul] at f;obtain rfl:=(smul_eq_zero.mp f).resolve_right u;exact Subtype.ext (zero_smul _ _)
 have w:=Aj.mP hL (K:=K L) (fun _ F=>F.1) (by
  intro Y k i J j M;have c:aB Y=0:=k.2;fin_cases i<;>fin_cases j<;>first
   | contradiction
   | exact congrFun c (0,0) | exact congrFun c (0,1) | exact congrFun c (0,2)
   | exact congrFun c (1,0) | exact congrFun c (1,1) | exact congrFun c (1,2))
  y z (xK hL A) t
 omega
lemma jC {L:Submodule ℂ aC} (hL:aD L) (i:aX L=8)
  (d:p L 2 3=7) {U:aC} (a:U∈L) (c:iQ U) (b:rN U≠0)
  (h:Module.finrank ℂ ((V L).map aB)=5)
  (e:cE 1 0∈(V L).map aB) (f:cE 0 1∈(V L).map aB):False:=by
 have g:=lA d (cB hL d a c b) h;exact nS hL i d a c b h
  (qP hL a c b g e f 0) (qP hL a c b g e f 1)
lemma qF {L:Submodule ℂ aC} (hL:aD L) (l:aX L=8)
  (i:p L 2 3=7) {U:aC} (d:U∈L) (j:iQ U) (f:rN U≠0)
  (c:Module.finrank ℂ ((V L).map aB)=5) {p:Module.Dual ℂ iA} {a b:ℂ}
  (g:nF p a b≠0) (h:∀X∈V L,nF p a b (aB X)=0):False:=by
 rcases yC c g h with e|⟨_,_,k⟩
 ·apply jC hL l i d j f c<;>rw[qO c g h]
  ·change a*p 1+b*p 0=0;rw[e,map_zero];ring
  ·change a*p 0+b*p 1=0;rw[e,map_zero];ring
 ·exact nG hL i d j f c k
lemma pK {L:Submodule ℂ aC} (hL:aD L) (s:aX L=8)
  (u:p L 2 3=7) {U:aC} (l:U∈L) (w:iQ U) (q:rN U≠0)
  (v:Module.finrank ℂ ((V L).map aB)=5) (R:Fin 2→Module.Dual ℂ iA)
  (t:R≠0) (f:¬LinearIndependent ℂ R)
  (h:∀X∈V L,R 0 (nD 0 (aB X))+R 1 (nD 1 (aB X))=0):False:=by
 obtain⟨p,a,b,c,d⟩:∃(p:Module.Dual ℂ iA) (a b:ℂ),a•p=R 0∧b•p=R 1:=by
  by_cases z:R 1=0
  ·exact⟨R 0,1,0,one_smul _ _,by simp[z]⟩
  ·have g:¬ ∀a:ℂ,a•R 1≠R 0:=fun k=>f (linearIndependent_fin2.mpr ⟨z,k⟩)
   push Not at g
   obtain⟨a,o⟩:=g;exact⟨R 1,a,1,o,one_smul _ _⟩
 have n:nF p a b≠0:=by
  intro j;apply t;funext i;apply LinearMap.ext;intro r;fin_cases i
  ·have e:a*p r+b*p 0=0:=DFunLike.congr_fun j (cE r 0);change R 0 r=0;rw[←c];simpa using e
  ·have e:a*p 0+b*p r=0:=DFunLike.congr_fun j (cE 0 r);change R 1 r=0;rw[←d];simpa using e
 apply qF hL s u l w q v n;intro X m;have e:=h X m;rw[←c,←d] at e;exact e
end Ac.Ak
namespace Ac.A7
open Aa Aq Aq.Ax
def dir (z:iZ):iZ→ₗ[ℂ] bE where
 toFun s:= ![s 0*z 0,s 0*z 1,-s 1*z 0,-s 1*z 1]
 map_add' _ _:=by ext i;fin_cases i<;>simp<;>ring
 map_smul' _ _:=by ext i;fin_cases i<;>simp<;>ring
def ip (a b:iZ):=a 0*b 1+a 1*b 0
abbrev eH (X:aC) (i:Fin 4):iZ:= ![X (i,0),X (i,1)]
abbrev aFw (r o:Fin 4):=(r=0∧o=1)∨(r=1∧o=0)
set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
lemma aAg (X:aC) {r o:Fin 4} (d:aFw r o)
  (c:aB X=0) (e:aT o X=0):
  pR X=Aj.bC X r*
   (ip (eH X o) (eH X 2)+ip (eH X o) (eH X 3)+
    ip (eH X 2) (eH X 3)):=by
 have b (i:Fin 4) (j:Fin 3) (a:i≠r):X (i,Fin.natAdd 2 j)=0:=by rcases d with⟨rfl,rfl⟩ | ⟨rfl,rfl⟩<;>fin_cases i<;>first | contradiction | exact congrFun e j | exact congrFun c (0,j) | exact congrFun c (1,j)
 have h (i:Fin 4) (j:Fin 5) (a:i≠r) (g:2≤j.val):X (i,j)=0:=by fin_cases j<;>first | contradiction | exact b i 0 a | exact b i 1 a | exact b i 2 a
 have xZ (f:Fin 5→ℂ):∑i,f i=f 0+f 1+f 2+f 3+f 4:=by simp[Fin.sum_univ_succ];ring
 rcases d with⟨rfl,rfl⟩|⟨rfl,rfl⟩<;>
  simp(config:={decide:=true}) (disch:=decide) only
   [pR,xZ,Fin.sum_univ_four,ite_true,ite_false,h,ip,eH,Aj.bC,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
    zero_add,add_zero,zero_mul,mul_zero]<;>ring
lemma aFx {L:Submodule ℂ aC} (hL:aD L) {r o:Fin 4} (z:aFw r o)
  {u:iZ} (F:ip u u≠0) {R:Matrix (Fin 2) (Fin 3) ℂ}
  (A:R 0 0+R 0 1+R 0 2≠0) {a:ℂ} (y:a≠0)
  (lift:∀s:iZ,∃X∈aP L,aG X=dir u s∧
    aT r X=a•R.vecMulLinear s∧aT o X=0):False:=by
 obtain⟨Y,l,n,E,B⟩:=lift ![1,0];obtain⟨Z,m,p,G,C⟩:=lift ![0,-1];have k:Aj.bC Y r≠0:=by change aT r Y 0+aT r Y 1+aT r Y 2≠0;simpa[E,Matrix.vecMul,dotProduct,Fin.sum_univ_two,←mul_add] using mul_ne_zero y A
 have b (X:aC) (s:iZ) (h:aG X=dir u s):
   eH X 2=s 0•u∧eH X 3= -s 1•u:=by
  constructor<;>funext i<;>fin_cases i<;>first
   | exact congrFun h 0 | exact congrFun h 1 | exact congrFun h 2 | exact congrFun h 3
 obtain⟨c,d⟩:=b _ _ n;obtain⟨e,f⟩:=b _ _ p;have g (t:ℂ):
   (Aj.bC Y r+t*Aj.bC Z r)*
   ((1+t)*(ip (eH Y o) u+t*ip (eH Z o) u)+t*ip u u)=0:=by
  have h:=(Ad.cT hL (L.add_mem l.1 (L.smul_mem t m.1))).2.2.1;rw[aAg _ z (by simp[show aB Y=0 from l.2,show aB Z=0 from m.2])
   (by simp[B,C])] at h
  have bD (i):eH (Y+t•Z) i=eH Y i+t•eH Z i:=by funext j;fin_cases j<;>rfl
  simp only[bD,c,d,e,f] at h;simp[ip,Aj.bC,mul_add,add_mul] at h ⊢
  linear_combination h
 have q:=g 0;have v:=g 1;have w:=g 2;have x:=g (-1)
 grobner
abbrev Sq:=Matrix (Fin 2) (Fin 2) ℂ
abbrev vA:=Matrix (Fin 2) (Fin 3) ℂ
def Mof (U Y:aC):Sq:= ![bO U ![Y (3,0),Y (3,1)],bO U ![Y (2,0),Y (2,1)]]
def Bof (Y:aC):vA:= ![aT 0 Y,aT 1 Y]
def iE:vA→ₗ[ℂ] Module.Dual ℂ jH:=
 let f (i:Fin 2):vA→ₗ[ℂ] Module.Dual ℂ jH:=(dW.compl₂ (Ak.nD i)).comp (LinearMap.proj (φ:=fun _=>iA) i)
 f 0+f 1
def fS (R:vA):jH→ₗ[ℂ] ℂ:=iE R
lemma gK:Function.Injective fS:=by
 apply(injective_iff_map_eq_zero iE).2;intro A a;have h (x y:iA):dW (A 0) x+dW (A 1) y=0:=LinearMap.congr_fun a (Ak.cE x y);funext i;apply fR;intro z;change dW (A i) z=0;fin_cases i
 ·simpa using h z 0
 ·simpa using h 0 z
lemma xL (F G:jH→ₗ[ℂ] ℂ)
  (h:LinearMap.ker F≤LinearMap.ker G):∃q:ℂ,q•F=G:=by
 apply Submodule.mem_span_singleton.mp;simpa using mem_span_of_iInf_ker_le_ker (L:=fun _:Unit=>F) (by simpa using h)
lemma aGf (A B:Sq):(A+B).adjugate=A.adjugate+B.adjugate:=by ext i j;fin_cases i<;>fin_cases j<;>simp[Matrix.adjugate_fin_two,add_comm]
lemma aAi {E:Type*} [Add E] (M:E→Sq) (B:E→vA)
  (i:∀x y,M (x+y)=M x+M y) (u:∀x y,B (x+y)=B x+B y)
  (R:vA) (H:Function.Injective (fun A:Sq=>A*R))
  (h:∀x,∃q:ℂ,M x*B x=q•R)
  (w:E) (p:(M w).det≠0) (F:∃v,∀c:ℂ,M v≠c•M w):
  ∃k:ℂ,∀x,B x=k•((M x).adjugate*R):=by
 choose q hq using h
 let k:=q w/(M w).det
 let t x:=q x-k*(M x).det
 let D (x:E):=B x-k•((M x).adjugate*R)
 have j (x y):D (x+y)=D x+D y:=by simp only[D,i,u,aGf,Matrix.add_mul,smul_add];abel
 have g (x):M x*D x=t x•R:=by simp[D,t,Matrix.mul_sub,hq,Matrix.mul_smul,←Matrix.mul_assoc,Matrix.mul_adjugate,Matrix.smul_mul,smul_smul,sub_smul]
 have jJ:=isUnit_iff_ne_zero.mpr p;have d {Z:vA} {s:ℂ} (e:M w*Z=s•R):Z=s•((M w)⁻¹ *R):=by
  simpa only[Matrix.nonsing_inv_mul_cancel_left _ _ jJ,Matrix.mul_smul]
   using congrArg (fun A:vA=>(M w)⁻¹ *A) e
 have z:D w=0:=by simpa[t,k,p] using d (g w)
 have b (x) (f:∀c:ℂ,M x≠c•M w):D x=0:=by
  let s:=t (x+w)-t x
  have G:M w*D x=s•R:=by rw[sub_smul,←g,i,j,z,add_zero,Matrix.add_mul,g];abel
  have m:=d G;by_cases n:s=0
  ·simpa[n] using m
  have e:s•(M x*(M w)⁻¹)=t x•(1:Sq):=H (by simpa[m,Matrix.smul_mul,Matrix.mul_smul,Matrix.mul_assoc] using g x);apply(f (s⁻¹*t x) ?_).elim;simpa[Matrix.smul_mul,Matrix.nonsing_inv_mul _ jJ,smul_smul,n,mul_assoc] using congrArg (fun A:Sq=>s⁻¹ •(A*M w)) e
 refine⟨k,fun x=>sub_eq_zero.mp (show D x=0 from ?_)⟩;by_cases f:∀c:ℂ,M x≠c•M w
 ·exact b x f
 push Not at f
 obtain⟨c,C⟩:=f;obtain⟨v,o⟩:=F;have r:∀a:ℂ,M (x+v)≠a•M w:=by intro a l;apply o (a-c);rw[i,C] at l;rw[sub_smul,←l];abel
 simpa only[j,b v o,add_zero] using b (x+v) r
lemma aHs (U X Y:aC):Mof U (X+Y)=Mof U X+Mof U Y:=by ext i j;rw[Matrix.add_apply];fin_cases i<;>fin_cases j<;>simp[Mof,bO]<;>ring
lemma xM {U X Y:aC} (d:Am.eP U) {a:ℂ}
  (c:Mof U X=a•Mof U Y):aG X=a•aG Y:=by
 let b (T:aC) (r:Fin 4):iZ:= ![T (r,0),T (r,1)]
 have row r (e:bO U (b X r)=a•bO U (b Y r)):b X r=a•b Y r:=(jB U d).1 (by rwa [map_smul]);have p:=row 2 (congrFun c 1);have q:=row 3 (congrFun c 0);funext j;fin_cases j<;>first | exact congrFun p 0 | exact congrFun p 1 | exact congrFun q 0 | exact congrFun q 1
lemma xN {L:Submodule ℂ aC} (hL:aD L)
  {U:aC} (y:U∈L) (w:Am.dY U) (e:Am.eP U)
  (c:Module.finrank ℂ ((aP L).map aG)=3)
  {R:vA} (l:(Am.aEc L).map aB=LinearMap.ker (fS R))
  (m:LinearIndependent ℂ R):
  ∃k:ℂ,∀Y∈aP L,Bof Y=k•((Mof U Y).adjugate*R):=by
 let K:=aP L
 have prod (Y:K):∃q:ℂ,Mof U Y*Bof Y=q•R:=by
  let A:=Mof U Y*Bof Y
  have row (i:Fin 2):(Mof U Y*Bof Y) i=kF (Mof U Y i) (gV Y):=by funext j;rw[Matrix.mul_apply,Fin.sum_univ_two];rfl
  obtain⟨q,v⟩:=xL (fS R) (fS A) (by
   rw[←l];rintro _ ⟨T,n,rfl⟩;obtain⟨u,x⟩:=Am.sQ.mp n;have B:Ae.aR L Y 0:=⟨Y,Y.2.1,by funext F;exact(zero_add _).symm⟩
   have f:=dC hL B y x w Y.2.2;rw[kG Y U T ![Y.val (2,0),Y.val (2,1)] ![Y.val (3,0),Y.val (3,1)]
    rfl rfl rfl rfl] at f
   change cG (A 0) _+cG (A 1) _=0;simp only[A,row];exact f)
  exact⟨q,gK (v.symm.trans (iE.map_smul q R).symm)⟩
 obtain⟨_,⟨W,o,rfl⟩,z⟩:=Ak.sT (K.map aG) c (-1) (by norm_num);have C:(Mof U W).det≠0:=by
  convert! mul_ne_zero (neg_ne_zero.mpr e) z using 1;change _=_ *(W (2,0)*W (3,1)+ -1*W (2,1)*W (3,0))
  rw[Matrix.det_fin_two];simp[Mof,bO];ring
 have t:∃V:K,∀a:ℂ,Mof U V.val≠a•Mof U W:=by
  by_contra! r;have g:K.map aG≤Submodule.span ℂ {aG W}:=by rintro _ ⟨Y,b,rfl⟩;obtain⟨a,p⟩:=r (⟨Y,b⟩:K);exact Submodule.mem_span_singleton.mpr ⟨a,(xM e p).symm⟩
  have d:=(Submodule.finrank_mono g).trans (finrank_span_le_ncard _ (Set.finite_singleton _));simp[K,c] at d
 obtain⟨k,s⟩:=aAi (E:=K) (fun Y=>Mof U Y.val) (fun Y=>Bof Y.val)
  (fun X Y=>aHs U X Y) (by
    intro X Y;ext i j;fin_cases i<;>rfl) R
  (fun _ _ h=>funext fun i=>Matrix.vecMul_injective_iff.mpr m (congrFun h i))
  prod ⟨W,o⟩ C t
 exact⟨k,fun Y b=>s ⟨Y,b⟩⟩
lemma jD {E:Type*} [AddCommGroup E] [Module ℂ E]
  [FiniteDimensional ℂ E] (W:Submodule ℂ E)
  (b:Module.finrank ℂ W+1=Module.finrank ℂ E):
  ∃F:E→ₗ[ℂ] ℂ,F≠0∧W=LinearMap.ker F:=by
 obtain⟨F,a,h⟩:=W.exists_le_ker_of_lt_top (lt_of_le_of_ne le_top (by rintro rfl;simp at b));exact⟨F,a,Submodule.eq_of_le_of_finrank_le h (by have:=Module.Dual.finrank_ker_add_one_of_ne_zero a;omega)⟩
lemma qQ {E:Type*} [AddCommGroup E] [Module ℂ E]
  (f g:E→ₗ[ℂ] ℂ) (c:f≠0) (h:∀x,f x≠0→ g x=0) (x:E):g x=0:=by
 by_cases b:f x=0
 ·obtain⟨v,a⟩:=LinearMap.surjective_of_ne_zero c 1;simpa[h v (a▸one_ne_zero)] using h (x+v) (by simp[b,a])
 exact h x b
lemma vB (f g:iZ→ₗ[ℂ] ℂ) (B:LinearMap.BilinForm ℂ iZ)
  (j:B≠0) (h:∀x y,f x+g y=0→B x y=0):f=0∨g=0:=by
 by_contra! c;apply j;refine LinearMap.ext fun x=>LinearMap.ext fun y=> ?_
 apply qQ f (B.flip y) c.1 _ x;intro a d;apply qQ g (B a) c.2 _ y;intro b i;have e:=h (g b•a) (-f a•b) (by simp[mul_comm]);simpa[d,i] using e
lemma aEh {U X:aC}
  (g:U (0,0)*U (1,1)+U (0,1)*U (1,0)=0)
  {s t:iZ} (h:aG X=dir (eH U 0) s+dir (eH U 1) t)
  {R:vA} {k:ℂ} (f:Bof X=k•((Mof U X).adjugate*R)):
  aT 0 X=(k*ip (eH U 0) (eH U 0))•R.vecMulLinear s∧
  aT 1 X=(-k*ip (eH U 1) (eH U 1))•R.vecMulLinear t:=by
 have a:X (2,0)=s 0*U (0,0)+t 0*U (1,0):=congrFun h 0;have b:X (2,1)=s 0*U (0,1)+t 0*U (1,1):=congrFun h 1;have c:X (3,0)= -s 1*U (0,0)+ -t 1*U (1,0):=congrFun h 2;have d:X (3,1)= -s 1*U (0,1)+ -t 1*U (1,1):=congrFun h 3;rw[Matrix.adjugate_fin_two] at f;constructor<;>funext j
 case' left=>have e:=congrFun (congrFun f (0:Fin 2)) j
 case' right=>have e:=congrFun (congrFun f (1:Fin 2)) j
 all_goals
  simp[Bof,Mof,bO,ip,eH,Matrix.vecMul,dotProduct,Fin.sum_univ_two,a,b,c,d] at e ⊢
  grobner
lemma kI {L:Submodule ℂ aC} (hL:aD L)
  {U:aC} (J:Am.eP U)
  (m:U (0,0)*U (1,1)+U (0,1)*U (1,0)=0)
  (E:Module.finrank ℂ ((aP L).map aG)=3)
  (R:vA) (H:LinearIndependent ℂ R)
  (d:R 0 0+R 0 1+R 0 2≠0)
  (l:∀Y∈aP L,dB Y=0)
  {k:ℂ} (n:k≠0)
  (K:∀Y∈aP L,Bof Y=k•((Mof U Y).adjugate*R)):False:=by
 let u:=eH U 0
 let v:=eH U 1
 have j:ip u u≠0∧ip v v≠0:=by unfold Am.eP at J;simp[ip,u,v,eH];constructor<;>intro h<;>grobner
 let p:=k*ip u u
 let q:= -k*ip v v
 have w:p≠0:=mul_ne_zero n j.1;have z:q≠0:=mul_ne_zero (neg_ne_zero.mpr n) j.2
 let C:=(aP L).map aG
 obtain⟨F,_,G⟩:=jD C (by rw[E,Module.finrank_fin_fun])
 let f:=F.comp (dir u)
 let g:=F.comp (dir v)
 have lift (s t:iZ) (h:f s+g t=0):∃X∈aP L,
   aG X=dir u s+dir v t∧aT 0 X=p•R.vecMulLinear s∧
   aT 1 X=q•R.vecMulLinear t:=by
  have M:dir u s+dir v t∈C:=by rwa [G,LinearMap.mem_ker,map_add]
  obtain⟨X,e,a⟩:=M;exact⟨X,e,a,aEh m a (K X e)⟩
 let N:=R.vecMulLinear
 let B:=dW.comp N N
 have A:B≠0:=by intro a;have i:=lN (LinearMap.range N) (by rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩;change B x y=0;rw[a];rfl);rw[←(LinearEquiv.ofInjective N (Matrix.vecMul_injective_iff.mpr H)).finrank_eq,Module.finrank_fin_fun] at i;omega
 rcases vB f g B A (by intro s t h;obtain⟨X,e,_,b,c⟩:=lift s t h;have a:=l X e;change cG (aT 0 X) (aT 1 X)=0 at a;change cG (R.vecMulLinear s) (R.vecMulLinear t)=0;simpa[b,c,kE,nR,w,z] using a) with hf|hg
 ·apply aFx hL (r:=0) (o:=1) (Or.inl ⟨rfl,rfl⟩) j.1 d w;intro s;simpa using lift s 0 (by simp[hf])
 ·apply aFx hL (r:=1) (o:=0) (Or.inr ⟨rfl,rfl⟩) j.2 d z;intro t;obtain⟨X,e,a,b,c⟩:=lift 0 t (by simp[hg]);exact⟨X,e,by simpa using a,c,by simpa using b⟩
lemma oC (S:Submodule ℂ jH) (c:Module.finrank ℂ S=5):
  ∃
   R:Matrix (Fin 2) (Fin 3) ℂ,fS R≠0∧
   S=LinearMap.ker (fS R):=by
 obtain⟨F,d,b⟩:=jD S (by simp[c,jH]);have a:=(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
  (f:=iE) (by simp[vA,jH,Module.finrank_matrix,Subspace.dual_finrank_eq])).mp gK
 obtain⟨R,rfl⟩:=a F;exact⟨R,d,b⟩
lemma pL {L:Submodule ℂ aC} (hL:aD L) (g:aX L=8)
  (f:p L 2 3=7) {U:aC} (c:U∈L) (b:Am.dY U)
  (a:Am.eP U) (d:Module.finrank ℂ ((Am.aEc L).map aB)=5):
  False:=by
 obtain⟨R,u,m⟩:=oC _ d;by_cases n:LinearIndependent ℂ R
 case neg=>
  let A:=dW∘R
  apply Ak.pK hL g f c b a d A _
   (fun h=>n (LinearIndependent.of_comp dW h))
  ·intro X t;have h:aB X∈(Am.aEc L).map aB:=⟨X,t,rfl⟩
   rw[m] at h;exact h
  ·intro e;apply u;refine LinearMap.ext fun z=> ?_
   change A 0 _+A 1 _=0;simp[e]
 have l:=Ak.lA f (cB hL f c b a) d;obtain⟨k,q⟩:=xN hL c b a l m n;by_cases z:k=0
 ·apply Ak.nS hL g f c b a d<;>intro Y o
  all_goals
   have h:Bof Y=0:=by simpa[z] using q Y o
   first
    | change Bof Y 0 0+Bof Y 0 1+Bof Y 0 2=0
    | change Bof Y 1 0+Bof Y 1 1+Bof Y 1 2=0
   rw[h];simp
 apply kI hL a ?_ l R n ?_ ?_ z q
 ·simpa(disch:=decide) [pQ,Fin.sum_univ_succ,b] using(Ad.cT hL c).2.1
 ·intro s
  let D:=(Am.aEc L).map aB
  have h:Ak.cE 1 0∈D:=by rw[show D =_ from m];change cG (R 0) 1+cG (R 1) 0=0;rw[pG,s];simp[cG]
  apply Ak.jC hL g f c b a d h;have j:(1:jH)∈D:=⟨1,Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _)),rfl⟩
  convert D.sub_mem j h using 1;funext ⟨i,x⟩;fin_cases i<;>simp[Ak.cE]
 intro Y o;have r:=Ak.xK hL l Y o;unfold Aj.eM Aj.bC at r;unfold dB;linear_combination r
end Ac.A7
namespace Ac.Ar
open Aa Ae Ad Al Aq
def nH (σ:Equiv.Perm F):aH→ₗ[ℂ] aH:=LinearMap.funLeft ℂ ℂ σ
lemma aAj (σ:Equiv.Perm F):Function.Injective (nH σ):=by intro a b h;funext i;simpa[nH] using congrFun h (σ.symm i)
lemma aHt (σ:Equiv.Perm F) (L:Submodule ℂ aC) (i j:Fin 4):
  p (L.map (re 1 σ)) i j=p L i j:=by
 let f:=(nH σ).prodMap (nH σ)
 have d:Function.Injective f:=by intro a b h;exact Prod.ext (aAj σ (congrArg Prod.fst h)) (aAj σ (congrArg Prod.snd h))
 let S:=L.map ((row i).prod (row j))
 have c:(L.map (re 1 σ)).map ((row i).prod (row j))=S.map f:=by dsimp only[S];rw[←Submodule.map_comp,←Submodule.map_comp];rfl
 exact(congrArg (fun P:Submodule ℂ (aH×aH)=>Module.finrank ℂ P) c).trans (Submodule.equivMapOfInjective f d S).finrank_eq.symm
lemma aBn {L:Submodule ℂ aC} (d:∀i,u L i=0) (σ:Equiv.Perm F):
  ∀i,u (L.map (re 1 σ)) i=0:=by
 intro i;apply Submodule.finrank_eq_zero.mpr;apply le_antisymm ?_ bot_le;intro x e;obtain⟨⟨t,c,rfl⟩,a⟩:=(Submodule.mem_inf.mp e)
 have b:t∈aZ L i:=by simp only[aZ,Submodule.mem_inf,Submodule.mem_iInf,LinearMap.mem_ker];refine⟨c,?_⟩;intro k;simp only[Submodule.mem_iInf,LinearMap.mem_ker] at a;have h:=a k;apply aAj σ;simpa only[map_zero] using(show nH σ (row k.val t)=0 from h)
 rw[Submodule.finrank_eq_zero.mp (d i)] at b;have f:t=0:=by simpa using b
 simp[f]
def aBo (M:Submodule ℂ aC):=Module.finrank ℂ ((M⊔Submodule.span ℂ {(1:aC)}).map aB)
def nI (k:ℕ):=∀L:Submodule ℂ aC,aD L→aX L=8→p L 2 3=7→
 (∀i,u L i=0)→∀a b:aH,bD a b 0 0∈L→
 (∀j,j≠0→j≠1→a j=0∧b j=0)→
 aL a b 0 1=0→a 0*b 1-a 1*b 0≠0→
 a 0≠0→a 1≠0→b 0≠0→b 1≠0→cS a≠0→cS b≠0→
 aBo L=k→False
lemma yG (X:nI 4) (Z:nI 5) (c6:nI 6):HighPair:=by
 apply pT;intro L hL E Q P;obtain⟨a,b,_,hU,_,i,j,H,S,T,U,V,w,y,t,sa,sb⟩:=qD hL E P Q;obtain⟨σ,m,n⟩:=aEr i j H
 let M:=L.map (re 1 σ)
 let A:=nH σ a
 let B':=nH σ b
 have N:aD M:=gI 1 σ hL;have hm:aX M=8:=(nL 1 σ L).trans E;have z:p M 2 3=7:=(aHt σ L 2 3).trans P;have f:bD A B' 0 0∈M:=by refine⟨bD a b 0 0,hU,?_⟩;funext ⟨r,c⟩;fin_cases r<;>rfl
 have s (k:F) (J:k≠0) (K:k≠1):A k=0∧B' k=0:=w (σ k) (fun u=>J (σ.injective (u.trans m.symm))) (fun u=>K (σ.injective (u.trans n.symm)));have l (v:aH) (k:F):nH σ v k=v (σ k):=rfl;have sum (v:aH):cS (nH σ v)=cS v:=Equiv.sum_comp σ v;have det:A 0*B' 1-A 1*B' 0≠0:=by simpa only[A,B',l,m,n] using t
 have B:=oQ N z f s det;obtain⟨g,_,hg,C⟩:=B;have o:(1:jH)∉M.map aB:=by rintro⟨x,hx,R⟩;have e:=C x 0 ⟨x,hx,by funext ij;simp[aM]⟩;rw[R,hg] at e;exact one_ne_zero e
 obtain⟨_,_,_,O,G⟩:=iK z o;change 4≤aBo M at O;change aBo M≤6 at G;have d {k:ℕ} (h:nI k) (hk:aBo M=k):False:=by
  apply h M N hm z (aBn Q σ) A B' f s _ det _ _ _ _ _ _ hk
  ·simpa only[A,B',aL,l,m,n] using y
  ·simpa only[A,l,m] using S
  ·simpa only[A,l,n] using T
  ·simpa only[B',l,m] using U
  ·simpa only[B',l,n] using V
  ·simpa only[A,sum] using sa
  ·simpa only[B',sum] using sb
 have q:aBo M=4∨aBo M=5∨aBo M=6:=by omega
 exact q.elim (d X) (fun h=>h.elim (d Z) (d c6))
end Ac.Ar
namespace Ac.Ar
open Aa Ae
lemma nJ {a b:aH}
  (f:∀k:F,k≠0→k≠1→a k=0∧b k=0):
  ∀r c,(2≤ r.val∨2≤ c.val)→bD a b 0 0 (r,c)=0:=by
 intro r c h;have d (g:2≤ c.val):a c=0∧b c=0:=f c (fun e=>by subst c;contradiction) (fun e=>by subst c;contradiction);fin_cases r
 ·exact(d (h.resolve_left (by decide))).1
 ·exact(d (h.resolve_left (by decide))).2
 ·rfl
 ·rfl
lemma aGg:nI 4:=by intro L hL f g _ a b e h _ c _ _ _ _ _ _ d;exact Am.oB hL g f e (nJ h) c d
end Ac.Ar
namespace Ac.Ar
open Aa Ae Aq
lemma aG6:nI 6:=by intro L hL _ f _ a b e g _ c _ _ _ _ _ _ d;have h:=Bc.sR hL f e (nJ g) c;apply h;apply Submodule.eq_top_of_finrank_eq;change aBo L=Module.finrank ℂ jH;simpa[jH] using d
end Ac.Ar
namespace Ac.Ar
open Aa Ae
lemma aGh:nI 5:=by intro L hL f g _ a b e h _ c _ _ _ _ _ _ d;exact A7.pL hL f g e (nJ h) c d
end Ac.Ar
lemma Ac.aFy:Ac.HighPair:=Ac.Ar.yG Ac.Ar.aGg Ac.Ar.aGh Ac.Ar.aG6
namespace Ac.Af
open Aa Finset Av
namespace M3
def pP (σ:Equiv.Perm (Fin 5)):aC→ₗ[ℂ] aC:=LinearMap.funLeft ℂ ℂ fun p=>(p.1,σ p.2)
def vF (σ:Equiv.Perm (Fin 5)):bI→ₗ[ℂ] bI:=LinearMap.funLeft ℂ ℂ fun p=>(p.1,σ p.2)
def gL (j:Fin 5) (a b c:ℂ):bI→ₗ[ℂ] ℂ where
 toFun v:=a*aA v 0 j+b*aA v 1 j+c*aA v 2 j
 map_add' _ _:=by simp[aA,sum_add_distrib];ring
 map_smul' _ _:=by simp[aA,←mul_sum];ring
lemma vC (σ:Equiv.Perm (Fin 5)) (v:bI) (r j):
  aA (vF σ v) r j=aA v r (σ j):=by
 change _-(∑k,v (r,σ k))/2=_;rw[Equiv.sum_comp σ (fun k=>v (r,k))];rfl
lemma aEi (σ:Equiv.Perm (Fin 5)) (v:bI) (j):
  G (vF σ v) j=G v (σ j):=by
 have S (f:aH):=Equiv.sum_comp σ f;simp only[G,cJ,vF,LinearMap.funLeft_apply];simp only[S (fun k=>v (0,k)),S (fun k=>v (1,k)),S (fun k=>v (2,k)),
  S (fun k=>v (0,k)*v (1,k)),S (fun k=>v (0,k)*v (2,k)),
  S (fun k=>v (1,k)*v (2,k)),S (fun k=>v (0,k)*v (1,k)*v (2,k))]
lemma aCq {L:Submodule ℂ aC} (hL:aD L) (d:aX L=8)
  {i:Fin 4} (c:u L i=3) (σ:Equiv.Perm (Fin 5)):
  let L':=L.map (pP σ)
  aD L'∧aX L'=8∧u L' i=3∧U L' i=(U L i).map (LinearMap.funLeft ℂ ℂ σ):=by
 intro L';have b:U L' i=(U L i).map (LinearMap.funLeft ℂ ℂ σ):=by
  ext w;simp only[Submodule.mem_map,uE,L'];constructor
  ·rintro⟨t,a,e⟩;refine⟨w∘σ.symm,?_,funext fun j=>by simp⟩;exact(show eJ i (w∘σ.symm)=t from funext fun⟨r,j⟩=>by simpa[pP,eJ] using(congrFun e (r,σ.symm j)).symm)▸a
  ·rintro⟨u,f,rfl⟩;exact⟨eJ i u,f,funext fun⟨r,j⟩=>by simp[pP,eJ]⟩
 refine⟨fun _ ⟨t,a,h⟩=>h▸(Ad.vS 1 σ (1+t)).trans (hL t a),?_,?_,b⟩
 ·exact(Submodule.equivMapOfInjective _
   (Function.LeftInverse.injective (g:=pP σ.symm) fun t=>by funext ⟨r,j⟩;simp[pP])
   L).finrank_eq.symm.trans d
 ·rw[←tE,b,(Submodule.equivMapOfInjective _
   (Function.LeftInverse.injective (g:=LinearMap.funLeft ℂ ℂ σ.symm)
     fun u=>by funext j;simp) _).finrank_eq.symm,tE,c]
lemma sU (P:Submodule ℂ bI) (A B:Finset (Fin 5)):
  Module.finrank ℂ (P.map (aK (A∪B)))+Module.finrank ℂ (P.map (aK (A∩B)))≤Module.finrank ℂ (P.map (aK A))+Module.finrank ℂ (P.map (aK B)):=by
 let K (C:Finset (Fin 5)):=LinearMap.ker ((aK C).domRestrict P)
 have a (C) (v:P):v∈K C↔∀j∈C,∀r,aA v.1 r j=0:=
  ⟨fun h j c r=>by simpa[aK] using congrFun (show aK C v.1=0 from h) (C.equivFin ⟨j,c⟩,r),
   fun h=>funext fun⟨k,r⟩=>h _ (C.equivFin.symm k).2 r⟩
 have u:K (A∪B)=K A⊓K B:=by ext v;simp[a,Submodule.mem_inf,or_imp,forall_and]
 have le:K A⊔K B≤K (A∩B):=sup_le (fun v d=>(a _ _).mpr fun j c=>(a _ _).mp d j (mem_inter.mp c).1) (fun v d=>(a _ _).mpr fun j c=>(a _ _).mp d j (mem_inter.mp c).2);have b C:Module.finrank ℂ (P.map (aK C))+Module.finrank ℂ (K C)=Module.finrank ℂ P:=by rw[←LinearMap.range_domRestrict P (aK C)];exact((aK C).domRestrict P).finrank_range_add_finrank_ker
 have:=Submodule.finrank_sup_add_finrank_inf_eq (K A) (K B);rw[←u] at this;have:=Submodule.finrank_mono le;have:=b (A∪B);have:=b (A∩B);have:=b A;have:=b B;omega
lemma aCr (η:aH) (r:Finset (Fin 5)→ℕ)
  (sub:∀A B,r (A∪B)+r (A∩B)≤ r A+r B)
  (m:∀A,A.card=4→ r A=6)
  (C:∀x y,x≠y→η x=η y→ r {x,y}≤3)
  (q:∀x y z,η x≠η y→η x≠η z→η y≠η z→ r {x,y,z}≤4)
  (a b c:Fin 5) (g:η a≠η b) (i:η a≠η c) (l:η b≠η c):False:=by
 classical
 have f {u v:Fin 5} (h:η u≠η v):u≠v:=fun e=>h (congrArg η e)
 have dL (x y z k:Fin 5) (o:z≠k)
   (xy:η x≠η y) (xz:η x≠η z) (xk:η x≠η k) (yz:η y≠η z) (yk:η y≠η k):
   r {x,y}≤2:=by
  have s:=sub {x,y,z} {x,y,k};have u:({x,y,z}:Finset _)∪{x,y,k}={x,y,z,k}:=by ext;simp
  have n:({x,y,z}:Finset _)∩{x,y,k}={x,y}:=by ext;simp;grind
  rw[u,n,m _ (by simp[f xy,f xz,f xk,f yz,f yk,o])] at s;have:=q x y z xy xz yz;have:=q x y k xy xk yk;omega
 have j (x y z k:Fin 5) (o:z≠k)
   (xy:η x≠η y) (xz:η x≠η z) (xk:η x≠η k) (yz:η y≠η z) (yk:η y≠η k):
   False:=by
  have h:=dL x y z k o xy xz xk yz yk;have E:r {z,k}≤3:=if e:η z=η k then C _ _ o e else(dL z k x y (f xy) e xz.symm yz.symm xk.symm yk.symm).trans (by decide)
  have s:=sub {x,y} {z,k};rw[m _ (by simp[f xy,(f xz).symm,f xk,(f yz).symm,f yk,o])] at s;omega
 obtain⟨d,p⟩:=card_pos.mp
  (show 0<({a,b,c}:Finset _)ᶜ.card by rw[card_compl];simp[f g,f i,f l])
 simp only[mem_compl,mem_insert,mem_singleton,not_or] at p;by_cases t:η d=η a
 ·exact j b c a d (Ne.symm p.1) l g.symm (t▸g.symm) i.symm (t▸i.symm)
 by_cases w:η d=η b
 ·exact j a c b d (Ne.symm p.2.1) i g (w▸g) l.symm (w▸l.symm)
 exact j a b c d (Ne.symm p.2.2) g i (Ne.symm t) l (Ne.symm w)
lemma pN {L:Submodule ℂ aC} (hL:aD L) (h8:aX L=8)
  {i:Fin 4} (Z:u L i=3):
  ∃
   (L':Submodule ℂ aC) (B:Finset (Fin 5)),
   aD L'∧aX L'=8∧u L' i=3∧
   ((B={0,1,2}∧Pi.single 3 (1:ℂ)-Pi.single 4 1∈U L' i)∨B={0,1,2,3})∧
   ∀z∈eQ (U L' i),∀j∈B,∀k∈B,z j=z k:=by
 classical
 have dn:=mM (U L i);rw[tE,Z] at dn;obtain⟨η,a,b,_,r,p,E⟩:=qX _ (by omega) (oM (i:=i) hL).1;have M (w:aH) (s:∑j,w j=0) (t:∑j,w j*η j=0):w∈U L i:=by
  have nn:eQ (eQ (U L i))=U L i:=
   (Submodule.eq_of_le_of_finrank_eq
     (fun w n=>eK.mpr fun z o=>by simpa[mul_comm] using eK.mp o w n)
     (by have:=mM (U L i);have:=mM (eQ (U L i));omega)).symm
  rw[←nn];apply eK.mpr;intro z o
  calc
   ∑
    j,z j*w j=∑j,(w j*z a+w j*η j*(z b-z a)):=
    sum_congr rfl fun j _=>by rw[E z o j];ring
   _=0:=by rw[sum_add_distrib,←sum_mul,←sum_mul,s,t];ring
 have G (x y:Fin 5) (e:η x=η y):Pi.single x (1:ℂ)-Pi.single y 1∈U L i:=M _ (by simp[sum_sub_distrib]) (by simp[sub_mul,sum_sub_distrib,Pi.single_apply,ite_mul,e]);have P:∀c,η c=0∨η c=1:=by
  intro c;by_contra! H;have R (k:Fin 5):∃w∈U L i,w k≠0:=by
   by_contra! h
   let z:aH:=Pi.single k 1
   have o:z∈eQ (U L i):=eK.mpr fun w n=>by simp[z,Pi.single_apply,mul_ite,h w n]
   have C:=E z o c;have K:=E z o k;by_cases ka:k=a
   ·subst k;have cb:c≠a:=fun e=>H.1 (e▸r)
    have ba:b≠a:=fun e=>by rw[e,r] at p;exact zero_ne_one p
    simp[z,cb,ba] at C;exact H.2 (by linear_combination C)
   by_cases kb:k=b
   ·subst k;have cb:c≠b:=fun e=>H.2 (e▸p)
    simp[z,cb,Ne.symm ka] at C;exact H.1 C.symm
   simp[z,Ne.symm ka,Ne.symm kb] at K
  apply aCr η (fun S=>Module.finrank ℂ ((W L i).map (aK S))) (sU _) ?_ ?_ ?_ a b c (by simp[r,p]) (by simpa[r] using H.1.symm) (by simpa[p] using H.2.symm)
  ·intro S d;obtain⟨j,q⟩:=card_eq_one.mp (show Sᶜ.card=1 by simp[card_compl,d]);obtain⟨w,n,a5⟩:=R j;have a6:Function.Injective ((aK S).domRestrict (W L i)):=fun x y h=>
    gJ hL n a5<| funext fun⟨k,s⟩=>by
     have m:j.succAbove k∈S:=by by_contra hn;exact Fin.succAbove_ne j k (mem_singleton.mp (q▸mem_compl.mpr hn))
     simpa[aK,jQ] using congrFun h (S.equivFin ⟨_,m⟩,s)
   have:=jP hL i;rw[←LinearMap.range_domRestrict,LinearMap.finrank_range_of_inj a6];omega
  ·intro x y Q e;have h:=dO hL (G x y e) {x,y} fun k=>by
    clear E r p;by_cases hx:k=x<;>by_cases hy:k=y<;>simp_all
   simp[Q] at h;omega
  ·intro x y z e f g;have Q:x≠y:=fun h=>e (congrArg η h)
   have xz:x≠z:=fun h=>f (congrArg η h)
   have yz:y≠z:=fun h=>g (congrArg η h)
   let w:aH:=Pi.single x (η y-η z)+Pi.single y (η z-η x)+Pi.single z (η x-η y)
   have n:=M w (by simp[w,Pi.add_apply,sum_add_distrib])
    (by simp[w,add_mul,sum_add_distrib,Pi.single_apply,ite_mul];ring)
   have h:=dO hL n {x,y,z} fun k=>by clear E r p;by_cases hx:k=x<;>by_cases hy:k=y<;>by_cases o:k=z<;>simp_all[w,sub_ne_zero,Ne.symm]
   simp[Q,xz,yz] at h;omega
 let F:=univ.filter (η · =0)
 have cb:=card_compl F;simp only[Fintype.card_fin] at cb;have a7:=card_pos.mpr (show F.Nonempty from⟨a,by simp[F,r]⟩);have a8:=card_pos.mpr (show Fᶜ.Nonempty from⟨b,by simp[F,p]⟩);obtain⟨A,dm,a9,sd,se⟩:
   ∃
    A:Finset (Fin 5),3≤A.card∧A.card<5∧
    (∀j∈A,∀k∈A,η j=η k)∧∀j∈Aᶜ,∀k∈Aᶜ,η j=η k:=by
  have s0:∀j∈F,∀k∈F,η j=η k:=fun j q k J=>by simp only[F,mem_filter,mem_univ,true_and] at q J;rw[q,J]
  have s1:∀j∈Fᶜ,∀k∈Fᶜ,η j=η k:=fun j q k J=>by
   have X:∀m∈Fᶜ,η m=1:=by simpa[F] using fun m=>(P m).resolve_left
   rw[X j q,X k J]
  by_cases h:3≤F.card
  ·exact⟨F,h,by omega,s0,s1⟩
  ·exact⟨Fᶜ,by omega,by omega,s1,by simpa using s0⟩
 let B:Finset (Fin 5):=if A.card=3 then{0,1,2} else{0,1,2,3}
 have hB:B.card=A.card:=by dsimp[B];split_ifs with h;simp[h];simp;omega
 obtain⟨σ,hσ⟩:=Equiv.Perm.exists_map_finset_eq B A hB;have memσ (j:Fin 5):j∈B↔σ j∈A:=by simp[←hσ]
 obtain⟨a4,a3,a0,N⟩:=aCq hL h8 Z σ;refine⟨L.map (pP σ),B,a4,a3,a0,?_,?_⟩
 ·by_cases v:A.card=3
  ·refine Or.inl ⟨by simp[B,v],?_⟩;have a1:σ 3∈Aᶜ:=mem_compl.mpr fun h=>by have:=(memσ 3).mpr h;simp[B,v] at this
   have a2:σ 4∈Aᶜ:=mem_compl.mpr fun h=>by have:=(memσ 4).mpr h;simp[B,v] at this
   rw[N];exact⟨_,G _ _ (se _ a1 _ a2),funext fun k=>by simp[Pi.single_apply,σ.injective.eq_iff]⟩
  ·exact Or.inr (by simp[B,v])
 ·intro z o j q k J;have O:z∘σ.symm∈eQ (U L i):=eK.mpr fun w n=>by
   have h:=eK.mp o (w∘σ) (N▸⟨w,n,rfl⟩);simp only[Function.comp_apply] at h ⊢
   rw[←Equiv.sum_comp σ (fun l=>w l*z (σ.symm l))];simpa using h
  have T:=E _ O (σ j);have V:=E _ O (σ k);simp only[Function.comp_apply,Equiv.symm_apply_apply] at T V;rw[T,V,sd _ ((memσ j).mp q) _ ((memσ k).mp J)]
lemma qR {P:Submodule ℂ bI} (V:(1:bI)∈P)
  {B:Finset (Fin 5)} (o:(0:Fin 5)∈B)
  (hr:4≤Module.finrank ℂ (P.map (aK B)))
  (y:∀v∈P,∀j∈B,∀k∈B,q v j=q v k):
  ∃
   (ω:ℂ) (c:Fin 5→ℂ),ω^2+ω+1=0∧(∀j∈B,c j=ω∨c j= -1-ω)∧
   ∀
    v∈P,∀j∈B,∀r:Fin 3,
    aA v r j=aV v 0/3+ ![1,c j,-1-c j] r*(aA v 0 j-aV v 0/3):=by
 classical
 let F:=(LinearMap.funLeft ℂ ℂ (fun r:Fin 3=>(B.equivFin ⟨0,o⟩,r))).domRestrict (P.map (aK B))
 have R:LinearMap.ker F≠ ⊥ :=fun h=>by have:=LinearMap.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp h);rw[Module.finrank_fin_fun] at this;exact absurd (hr.trans this) (by decide)
 obtain⟨z,G,a0⟩:=Submodule.exists_mem_ne_zero_of_ne_bot R;obtain⟨u,hu,O⟩:=z.2;have N (r:Fin 3):aA u r 0=0:=by have h:z.1 (B.equivFin ⟨0,o⟩,r)=0:=congrFun G r;simpa[←O,aK] using h
 obtain⟨j,x,C,E⟩:∃j∈B,∃r:Fin 3,aA u r j≠0:=by by_contra! H;exact a0 (Subtype.ext (O▸funext fun⟨k,r⟩=>H _ (B.equivFin.symm k).2 r))
 have m (v w:bI) (r:Fin 3) (k:Fin 5):aA (v+w) r k=aA v r k+aA w r k:=congrFun (map_add (aA1 k) v w) r;have Q (v:bI) (a:v∈P):q (u+v) j=q v j:=by rw[y _ (P.add_mem hu a) j x 0 o,y v a j x 0 o];simp[q,m,N]
 have i:q u j=0:=by rw[y u hu j x 0 o];simp[q,N]
 let h (s:Fin 3):=aA u s j
 have g:h 0+h 1+h 2=0:=by have e:= Q 1 V;rw[add_comm u 1,aHe] at e;simp only[q,iS] at e i;dsimp[h];linear_combination(i-e)/6
 have t:h 0^2+h 0*h 1+h 1^2=0:=by simp only[q] at i;dsimp[h] at g ⊢;linear_combination-i/2+(h 0+h 1)*g
 have p:h 0≠0:=fun G=>by
  have Z:h 1=0:=by simpa[G] using t
  have a2:h 2=0:=by simpa[G,Z] using g
  change h C≠0 at E;fin_cases C<;>contradiction
 let ω:=h 1/h 0
 have hω:ω^2+ω+1=0:=by dsimp[ω];field_simp[p];linear_combination t
 have A:h 1=ω*h 0:=by dsimp[ω];field_simp[p]
 have J:h 2=(-1-ω)*h 0:=by linear_combination g-A
 have T (v:bI) (a:v∈P) (k:Fin 5) (b:k∈B):aV v k=aV v 0:=by have e:=y (1+v) (P.add_mem V a) k b 0 o;have f:=y v a k b 0 o;simp only[q,iS] at e;unfold q at f;unfold aV;linear_combination(f-e)/6
 let d (v:bI) (r:Fin 3) (k:Fin 5):=aA v r k-aV v 0/3
 have qd (v:bI) (a:v∈P) (k:Fin 5) (b:k∈B):
   q v k=6*(aV v 0/3)^2-2*((d v 0 k)^2+d v 0 k*d v 1 k+(d v 1 k)^2):=by
  dsimp[d];rw[←T v a k b];unfold q aV;ring
 have X:(1+2*ω)≠0:=fun e=>by
  have:(-3:ℂ)=0:=by linear_combination(1+2*ω)*e-4*hω
  norm_num at this
 have sq (v:bI) (a:v∈P) (k:Fin 5) (b:k∈B):
   (d v 1 k-ω*d v 0 k)*(d v 1 k-(-1-ω)*d v 0 k)=0:=by
  have kK:h 0*(aA v 0 j+ω*aA v 1 j+(-1-ω)*aA v 2 j)=0:=by have e:= Q v a;simp only[q,m] at e i;dsimp[h] at g A J;linear_combination(i-e)/2+(aA v 0 j+aA v 1 j+aA v 2 j)*g-aA v 1 j*A-aA v 2 j*J
  have a1:=(mul_eq_zero.mp kK).resolve_left p;have dj:d v 1 j=ω*d v 0 j:=by
   have e:(1+2*ω)*(d v 1 j-ω*d v 0 j)=0:=by dsimp[d];rw[←T v a j x];unfold aV;linear_combination a1-2*(aA v 0 j-(aA v 0 j+aA v 1 j+aA v 2 j)/3)*hω
   linear_combination(mul_eq_zero.mp e).resolve_left X
  have e:=y v a k b j x;rw[qd v a k b,qd v a j x,dj] at e;linear_combination-e/2+(d v 0 j)^2*hω-(d v 0 k)^2*hω
 have l (k:Fin 5) (b:k∈B):∃c:ℂ,(c=ω∨c= -1-ω)∧∀v∈P,d v 1 k=c*d v 0 k:=by
  have n (v:bI) (a:v∈P):=(mul_eq_zero.mp (sq v a k b)).imp sub_eq_zero.mp sub_eq_zero.mp;by_cases S:∀v∈P,d v 1 k=ω*d v 0 k
  ·exact⟨ω,Or.inl rfl,S⟩
  push Not at S;obtain⟨v,a,K⟩:=S
  refine⟨-1-ω,Or.inr rfl,fun w hw=>by_contra fun M=> ?_⟩;have ve:=(n v a).resolve_left K;have we:=(n w hw).resolve_right M;have U (r:Fin 3):d (v+w) r k=d v r k+d w r k:=by dsimp[d,aV];simp only[m];ring
  rcases n (v+w) (P.add_mem a hw) with e|e<;>rw[U,U] at e
  ·exact K (by linear_combination e-we)
  ·exact M (by linear_combination e-ve)
 let c (k:Fin 5):ℂ:=if b:k∈B then(l k b).choose else ω
 refine⟨ω,c,hω,fun k b=>by simpa[c,b] using(l k b).choose_spec.1,fun v a k b r=> ?_⟩;have e:d v 1 k=c k*d v 0 k:=by simpa[c,b] using(l k b).choose_spec.2 v a
 dsimp[d] at e;rw[←T v a k b] at e ⊢;unfold aV at e ⊢
 fin_cases r<;>[simp;(simp;linear_combination e);(simp;linear_combination-e)]
def kJ (w s p q:ℂ):Fin 3→ℂ:= ![s+p+q,s+w*p+(-1-w)*q,s+(-1-w)*p+w*q]
lemma aEj (w s p q:ℂ) (r:Fin 3):kJ (-1-w) s q p r=kJ w s p q r:=by fin_cases r<;>simp[kJ]<;>ring
def dd (u v w:Fin 3→ℂ):=u 0*(v 1*w 2+v 2*w 1)+u 1*(v 0*w 2+v 2*w 0)+u 2*(v 0*w 1+v 1*w 0)
lemma gW {w:ℂ} (B:w^2+w+1=0) (σ:Equiv.Perm (Fin 5))
  {M:bI} {S X Y:Fin 5→ℂ} (x:∀j r,aA M r (σ j)=kJ w (S j) (X j) (Y j) r)
  (A:S 0=S 1) (m:Y 0=0) (n:Y 1=0) (o:G M (σ 1)=G M (σ 0)):
  let g:= -(∑j,S j)/3
  let h:= -(∑j,X j)/3
  let i:= -(∑j,Y j)/3
  let e (u v:Fin 5):=6*(h+X u)*(h+X v)-3*((g+S u)*(i+Y v)+(g+S v)*(i+Y u))
  (X 0-X 1)*(e 2 3+e 2 4+e 3 4)=0:=by
 let N:=vF σ M
 have y (j:Fin 5) (r:Fin 3):aA N r j=kJ w (S j) (X j) (Y j) r:=by rw[vC,x]
 let g:= -(∑j,S j)/3;let h:= -(∑j,X j)/3;let i:= -(∑j,Y j)/3
 have d (j:Fin 5):(fun r=>N (r,j))=kJ w (g+S j) (h+X j) (i+Y j):=by funext r;rw[cQ N r j];simp only[y,Fin.sum_univ_five,g,h,i];fin_cases r<;>simp[kJ]<;>ring
 have sub:(fun r=>N (r,0))-(fun r=>N (r,1))=kJ w 0 (X 0-X 1) 0:=by rw[d,d];funext r;fin_cases r<;>simp[kJ,A,m,n]<;>ring
 have f:let c (j:Fin 5) (r:Fin 3):=N (r,j)
  G
   N 1-G N 0=dd (c 0-c 1) (c 2) (c 3)+dd (c 0-c 1) (c 2) (c 4)+
   dd (c 0-c 1) (c 3) (c 4):=by simp[dd,G,cJ,Fin.sum_univ_five];ring
 have k (z s p q t a b:ℂ):
   dd (kJ w 0 z 0) (kJ w s p q) (kJ w t a b)=z*(6*p*a-3*(s*b+t*q)):=by
  simp[dd,kJ];linear_combination z*(2*s*b+2*t*q-6*p*a+2*p*b+2*q*a+2*q*b-2*s*a-2*p*t)*B
 have l:G N 1-G N 0=0:=by simp[N,aEi,o]
 dsimp only at f;rw[l,sub,d 2,d 3,d 4,k,k,k] at f;dsimp only[g,h,i] at f ⊢;linear_combination-f
def e3 (a b c:ℂ):ℂ:=a*b*c-(a+b+c)*(a*b+b*c+c*a)+8/27*(a+b+c)^3
lemma aCs {L:Submodule ℂ aC} (hL:aD L) {i:Fin 4}
  (a2:Module.finrank ℂ (W L i)=6)
  (a3:Module.finrank ℂ ((W L i).map (aK {3,4}))≤3)
  {ω:ℂ} (hω:ω^2+ω+1=0) {c:Fin 5→ℂ}
  (R:∀j∈({0,1,2}:Finset (Fin 5)),c j=ω∨c j= -1-ω)
  (l:∀v∈W L i,∀j∈({0,1,2}:Finset (Fin 5)),∀r:Fin 3,
    aA v r j=aV v 0/3+ ![1,c j,-1-c j] r*(aA v 0 j-aV v 0/3))
  (hG:∀v∈W L i,G v 0=G v 1):False:=by
 let K:Submodule ℂ bI:=W L i⊓LinearMap.ker (aK {3,4})
 let E:Submodule ℂ bI:=K⊓LinearMap.ker (gL 0 1 1 1)
 have a1:2≤Module.finrank ℂ E:=by
  have d1:Module.finrank ℂ ((W L i).map (aK {3,4}))+Module.finrank ℂ K=Module.finrank ℂ (W L i):=cX (W L i) (aK {3,4})
  let t:=(gL 0 1 1 1).domRestrict K
  have d2:=t.finrank_range_add_finrank_ker;have dl:Module.finrank ℂ (LinearMap.range t)≤1:=by simpa using(LinearMap.range t).finrank_le
  have de:Module.finrank ℂ (LinearMap.ker t)=Module.finrank ℂ E:=((LinearMap.ker (gL 0 1 1 1)).submoduleOfEquivInf K).finrank_eq;omega
 have B (j:Fin 5) (hj:j∈({0,1,2}:Finset (Fin 5))):c j^2+c j+1=0:=by rcases R j hj with h | h<;>rw[h]<;>linear_combination hω
 let x:E→ₗ[ℂ] (Fin 3→ℂ):=(LinearMap.pi fun j:Fin 3=>gL j.castSucc.castSucc 1 0 0).domRestrict E
 have C (z:E) (r:Fin 3) (j:Fin 5):
   aA z.1 r j= ![x z 0* ![1,c 0,-1-c 0] r,x z 1* ![1,c 1,-1-c 1] r,x z 2* ![1,c 2,-1-c 2] r,0,0] j:=by
  have V:aV z.1 0=0:=by simpa[gL,aV] using z.2.2
  have hb (k:Fin 5) (hk:k∈({3,4}:Finset (Fin 5))):aA z.1 r k=0:=by simpa[aK] using congrFun (show aK {3,4} z.1=0 from z.2.1.2) (({3,4}:Finset _).equivFin ⟨k,hk⟩,r)
  fin_cases j
  ·simpa[V,x,gL,mul_comm] using l _ z.2.1.1 0 (by decide) r
  ·simpa[V,x,gL,mul_comm] using l _ z.2.1.1 1 (by decide) r
  ·simpa[V,x,gL,mul_comm] using l _ z.2.1.1 2 (by decide) r
  ·exact hb 3 (by decide)
  ·exact hb 4 (by decide)
 have P (z:E) (d:ℂ) (J:d^2+d+1=0)
   (N:∀j:Fin 3,x z j≠0→c j.castSucc.castSucc=d):e3 (x z 0) (x z 1) (x z 2)=0:=by
  let p:aH:=fun j=> ![x z 0,x z 1,x z 2,0,0] j-(x z 0+x z 1+x z 2)/3
  have A:jF ![1,d,-1-d] p=z.1:=by
   funext ⟨r,j⟩;rw[cQ z.1 r j];have F (k:Fin 3):x z k* ![1,c k.castSucc.castSucc,-1-c k.castSucc.castSucc] r=x z k* ![1,d,-1-d] r:=by by_cases h:x z k=0<;>[simp[h];rw[N k h]]
   have h0:x z 0* ![1,c 0,-1-c 0] r=x z 0* ![1,d,-1-d] r:=F 0;have h1:x z 1* ![1,c 1,-1-c 1] r=x z 1* ![1,d,-1-d] r:=F 1;have h2:x z 2* ![1,c 2,-1-c 2] r=x z 2* ![1,d,-1-d] r:=F 2;simp only[Fin.sum_univ_five,C,h0,h1,h2,jF,p];fin_cases j<;>simp<;>ring
  have nz:d≠0:=by rintro rfl;norm_num at J
  have a0: -1-d≠0:=fun h=>by
   have e:d= -1:=by linear_combination-h
   rw[e] at J;norm_num at J
  have em:=vY hL (A.symm▸z.2.1.1) (by simp) (by simp;linear_combination-J)
   (by simpa using mul_ne_zero nz a0)
  have ep:vX p=e3 (x z 0) (x z 1) (x z 2):=by simp(config:={decide:=true}) [vX,e3,Fin.sum_univ_five,p];ring
  rwa [ep] at em
 let f:E→ₗ[ℂ] (Fin 2→ℂ):=(LinearMap.funLeft ℂ ℂ (Fin.castSucc:Fin 2→Fin 3)).comp x
 have O:Function.Injective f:=by
  rw[←LinearMap.ker_eq_bot,LinearMap.ker_eq_bot'];intro z N;have a:x z 0=0:=congrFun N 0;have b:x z 1=0:=congrFun N 1;have q:x z 2=0:=by simpa[e3,a,b] using P z (c 2) (B 2 (by decide)) fun j hj=>by fin_cases j<;>simp_all
  apply Subtype.ext;funext ⟨r,j⟩;rw[cQ z.1];have zt (k):aA z.1 r k=0:=by rw[C];fin_cases k<;>simp[a,b,q]
  simp[zt]
 have df:=LinearMap.finrank_le_finrank_of_injective O;rw[Module.finrank_fin_fun] at df;have Q:=(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f:=f)
  (by rw[Module.finrank_fin_fun];omega)).mp O
 obtain⟨p,hp⟩:= Q ![1,0];obtain⟨q,hq⟩:= Q ![0,1];have o:x p 0=1:=congrFun hp 0;have s:x p 1=0:=congrFun hp 1;have u:x q 0=0:=congrFun hq 0;have w:x q 1=1:=congrFun hq 1;have n (σ:Equiv.Perm (Fin 5)) (v:bI) {c₀ y:ℂ} (hc₀:c₀^2+c₀+1=0)
   (hg:G v (σ 1)=G v (σ 0))
   (hv:∀k r,aA v r (σ k)= ![![1,c₀,-1-c₀] r,0,y* ![1,c 2,-1-c 2] r,0,0] k):
   c₀=c 2∧y^2=1:=by
  by_cases A:c₀=c 2
  ·refine⟨A,?_⟩;have g:=gW hc₀ σ (M:=v) (S:=0) (X:= ![1,0,y,0,0]) (Y:=0)
    (fun k r=>by rw[hv];fin_cases k<;>fin_cases r<;>simp[kJ,←A]<;>ring) rfl rfl rfl hg
   simp[Fin.sum_univ_five] at g;linear_combination-g/2
  ·exfalso;have dc:c 2= -1-c₀:=by
    have z2:(c 2-c₀)*(c 2+1+c₀)=0:=by linear_combination B 2 (by decide)-hc₀
    linear_combination(mul_eq_zero.mp z2).resolve_left (sub_ne_zero.mpr (Ne.symm A))
   have g:=gW hc₀ σ (M:=v) (S:=0) (X:= ![1,0,0,0,0]) (Y:= ![0,0,y,0,0])
    (fun k r=>by rw[hv];fin_cases k<;>fin_cases r<;>simp[kJ,dc]<;>ring) rfl rfl rfl hg
   simp[Fin.sum_univ_five] at g;norm_num at g
 have Z:=n 1 p.1 (y:=x p 2) (B 0 (by decide)) (hG _ p.2.1.1).symm fun k r=>by rw[C];fin_cases k<;>simp[o,s]
 have aq:=n (Equiv.swap 0 1) q.1 (y:=x q 2) (B 1 (by decide)) (hG _ q.2.1.1) fun k r=>by rw[C];fin_cases k<;>simp[u,w,Equiv.swap_apply_def]
 have m (z:E):=P z (c 2) (B 2 (by decide)) fun j _=>by fin_cases j<;>simp[Z.1,aq.1]
 have H (a:ℂ) (ha:a^2=1) (h:e3 1 0 a=0):a= -1:=by unfold e3 at h;linear_combination(27*h-(8*a-3)*ha)/5
 have T:=H (x p 2) Z.2 (by simpa[o,s] using m p);have U:=H (x q 2) aq.2 (by simpa[e3,u,w] using m q);have h:=m (p+q);norm_num[e3,map_add,o,s,T,u,w,U] at h
lemma aGi {w:ℂ} (g:w^2+w+1=0) (σ:Equiv.Perm (Fin 5))
  {M:bI} {s a b:ℂ}
  (e:∀j r,aA M r (σ j)=kJ w (![0,0,0,0,s] j) (![1,2,3,0,a] j) (![0,0,0,0,b] j) r)
  (h:G M (σ 1)=G M (σ 0)) (i:G M (σ 2)=G M (σ 0)):a=12∧s*b=108:=by
 have c:=gW g σ e rfl rfl rfl h;have d:=gW g ((Equiv.swap 1 2).trans σ) (M:=M)
  (S:= ![0,0,0,0,s]) (X:= ![1,3,2,0,a]) (Y:= ![0,0,0,0,b])
  (fun j r=>by change aA M r (σ (Equiv.swap 1 2 j))=_;rw[e];fin_cases j<;>rfl) rfl rfl rfl i
 norm_num[Fin.sum_univ_five] at c d;have f:a=12:=by linear_combination-(c+d)/2
 exact⟨f,by linear_combination-c/2+(a+9)*f⟩
lemma aHu {w:ℂ} (f:w^2+w+1=0) (σ:Equiv.Perm (Fin 5))
  {M:bI} {s a b:ℂ}
  (e:∀j r,aA M r (σ j)=kJ w (![0,0,0,0,s] j) (![1,-1,0,0,a] j) (![0,0,1,0,b] j) r)
  (g:G M (σ 1)=G M (σ 0)) (h:G M (σ 3)=G M (σ 2)):
  2*(-a^2)=s*(1-2*b)∧2*(1-b^2)=s*(-2*a):=by
 have c:=gW f σ e rfl rfl rfl g;have d:=gW (w:= -1-w) (by linear_combination f) (((Equiv.swap 0 2).trans (Equiv.swap 1 3)).trans σ)
  (M:=M) (S:= ![0,0,0,0,s]) (X:= ![1,0,0,0,b]) (Y:= ![0,0,1,-1,a])
  (fun j r=>by
    change aA M r (σ (((Equiv.swap 0 2).trans (Equiv.swap 1 3)) j))=_;rw[e,aEj];fin_cases j<;>rfl) rfl rfl rfl h
 norm_num[Fin.sum_univ_five] at c d;exact⟨by linear_combination c,by linear_combination d⟩
lemma aEk (d a b D A B:ℂ)
  (h:∀k:ℂ,2*(-(a+k*A)^2)=(d+k*D)*(1-2*(b+k*B))∧
    2*(1-(b+k*B)^2)=(d+k*D)*(-2*(a+k*A))):D =0∧A=0∧B=0:=by
 have f:A^2=D *B:=by linear_combination-((h 1).1+(h (-1)).1-2*(h 0).1)/4
 have g:B^2=D *A:=by linear_combination-((h 1).2+(h (-1)).2-2*(h 0).2)/4
 by_cases e:D =0
 ·simpa[e] using And.intro f g
 let k:= -d/D
 have c:d+k*D =0:=by dsimp[k];field_simp;ring
 have z:a+k*A=0:=by simpa[c] using(h k).1
 have l:D *(1-2*(b+k*B))=0:=by linear_combination-((h (k+1)).1-(h (k-1)).1)/2-4*A*z+2*B*c
 have m:=(mul_eq_zero.mp l).resolve_left e;have n:=(h k).2;rw[c,zero_mul] at n;exact(one_ne_zero (by linear_combination(2*n-(1+2*(b+k*B))*m)/3:(1:ℂ)=0)).elim
lemma aCt (a b c d:Bool):
  let v:Fin 5→Bool:= ![a,b,c,d,false]
  ∃
   τ:Equiv.Perm (Fin 5),τ 4=4∧v (τ 1)=v (τ 0)∧
   (v (τ 2)=v (τ 0)∨v (τ 2)=v (τ 3)):=by
 cases a<;>cases b<;>cases c<;>cases d<;>
  first
  | exact⟨1,by decide⟩
  | exact⟨Equiv.swap 2 3,by decide⟩
  | exact⟨Equiv.swap 1 3,by decide⟩
  | exact⟨Equiv.swap 0 3,by decide⟩
lemma aAk {L:Submodule ℂ aC} (hL:aD L) {i:Fin 4}
  (b0:Module.finrank ℂ (W L i)=6)
  {ω:ℂ} (hω:ω^2+ω+1=0) {c:Fin 5→ℂ}
  (A:∀j∈({0,1,2,3}:Finset (Fin 5)),c j=ω∨c j= -1-ω)
  (F:∀v∈W L i,∀j∈({0,1,2,3}:Finset (Fin 5)),∀r:Fin 3,
    aA v r j=aV v 0/3+ ![1,c j,-1-c j] r*(aA v 0 j-aV v 0/3))
  (T:∀v∈W L i,∀j∈({0,1,2,3}:Finset (Fin 5)),∀k∈({0,1,2,3}:Finset (Fin 5)),
    G v j=G v k)
  (τ:Equiv.Perm (Fin 5)) (hτ4:τ 4=4) (Z:c (τ 1)=c (τ 0))
  (a7:c (τ 2)=c (τ 0)∨c (τ 2)=c (τ 3)):False:=by
 classical
 have d (j:Fin 5):j∈({0,1,2,3}:Finset (Fin 5))↔τ j∈({0,1,2,3}:Finset (Fin 5)):=by
  have a2 (k:Fin 5):k∈({0,1,2,3}:Finset (Fin 5))↔k≠4:=by fin_cases k<;>decide
  rw[a2,a2];exact⟨fun h e=>h (τ.injective (e.trans hτ4.symm)),fun h e=>h (e▸hτ4)⟩
 let w:=c (τ 0)
 have hτ0m:τ 0∈({0,1,2,3}:Finset (Fin 5)):=(d 0).mp (by decide);have Q:w^2+w+1=0:=by rcases A _ hτ0m with h | h<;>dsimp[w]<;>rw[h]<;>linear_combination hω
 have a5 (j:Fin 5) (o:j∈({0,1,2,3}:Finset (Fin 5))):c (τ j)=w∨c (τ j)= -1-w:=by
  rcases A _ hτ0m with h|h<;>rcases A _ ((d j).mp o) with k|k
  ·exact Or.inl (k.trans h.symm)
  ·exact Or.inr (by dsimp[w];rw[k,h])
  ·exact Or.inr (by dsimp[w];rw[k,h];ring)
  ·exact Or.inl (k.trans h.symm)
 let V:bI→ₗ[ℂ] ℂ:=gL 0 (1/3) (1/3) (1/3)
 have u (v:bI):V v=aV v 0/3:=by simp[V,gL,aV];ring
 let q (j:Fin 5):bI→ₗ[ℂ] ℂ:=gL j 1 0 0-V
 let f:bI→ₗ[ℂ] ℂ×(Fin 4→ℂ):=V.prod (LinearMap.pi fun k:Fin 4=>q (τ k.castSucc))
 have x:W L i⊓LinearMap.ker f≤W L i⊓LinearMap.ker (jQ 4):=by
  rintro z ⟨g,hz⟩;refine⟨g,funext fun⟨k,r⟩=> ?_⟩;have o:k.castSucc∈({0,1,2,3}:Finset (Fin 5)):=by fin_cases k<;>decide
  have U:aV z 0/3=0:=(u z).symm.trans (congrArg Prod.fst hz);have a9:aA z 0 k.castSucc=0:=by
   have N:(τ.symm k.castSucc).1<4:=by
    have:=(d _).mpr (by rw[τ.apply_symm_apply];exact o)
    generalize τ.symm k.castSucc=m at this;fin_cases m<;>simp at this ⊢
   have e:aA z 0 (τ (⟨(τ.symm k.castSucc).1,N⟩:Fin 4).castSucc)-aV z 0/3=0:=by simpa[f,q,gL,u] using congrFun (congrArg Prod.snd hz) ⟨_,N⟩
   simp only[Fin.castSucc_mk,Fin.eta,τ.apply_symm_apply] at e;linear_combination e+U
  have B:(4:Fin 5).succAbove k=k.castSucc:=by fin_cases k<;>decide
  simpa[jQ,B,U,a9] using F z g _ o r
 have b1:Module.finrank ℂ (W L i⊓LinearMap.ker f:Submodule ℂ bI)≤1:=(Submodule.finrank_mono x).trans (fJ hL i 4);have rn:Module.finrank ℂ ((W L i).map f)+Module.finrank ℂ (W L i⊓LinearMap.ker f:Submodule ℂ bI)=
   Module.finrank ℂ (W L i):=by
  rw[←LinearMap.range_domRestrict,←((LinearMap.ker f).submoduleOfEquivInf (W L i)).finrank_eq];exact(f.domRestrict (W L i)).finrank_range_add_finrank_ker
 have dr:Module.finrank ℂ ((W L i).map f)≤5:=by simpa[Module.finrank_prod,Module.finrank_fin_fun] using((W L i).map f).finrank_le
 have a4:(W L i).map f= ⊤ :=Submodule.eq_top_of_finrank_eq
  (by rw[Module.finrank_prod,Module.finrank_fin_fun,Module.finrank_self];omega)
 have R (y:ℂ×(Fin 4→ℂ)):∃z∈W L i,f z=y:=by simpa[Submodule.mem_map] using(show y∈(W L i).map f by rw[a4];trivial)
 obtain⟨r,⟨P,hr⟩,a3⟩:=Submodule.exists_mem_ne_zero_of_ne_bot
  (show(W L i⊓LinearMap.ker f:Submodule ℂ bI)≠ ⊥ from fun e=>by rw[e,finrank_bot] at rn;omega)
 let s:bI→ₗ[ℂ] ℂ:=gL 4 (1/3) (1/3) (1/3)
 let a:bI→ₗ[ℂ] ℂ:=gL 4 (1/3) ((-1-w)/3) (w/3)
 let b:bI→ₗ[ℂ] ℂ:=gL 4 (1/3) (w/3) ((-1-w)/3)
 have S (z:bI) (n:Fin 3):aA z n 4=kJ w (s z) (a z) (b z) n:=by
  fin_cases n<;>simp[s,a,b,gL,kJ]
  ·ring
  ·linear_combination(2*(aA z 1 4-aA z 2 4)/3)*Q
  ·linear_combination(2*(aA z 2 4-aA z 1 4)/3)*Q
 have H (B:s r=0) (K:a r=0) (M:b r=0):False:=by
  apply a3;funext ⟨n,j⟩;rw[cQ r n j];have zt (k:Fin 5):aA r n k=0:=by
   by_cases hk:k=4
   ·subst k;rw[S,B,K,M];fin_cases n<;>simp[kJ]
   ·obtain⟨l,rfl⟩:k∈Set.range (4:Fin 5).succAbove:=by simpa using hk
    exact congrFun (x ⟨P,hr⟩).2 (l,n)
  simp[zt]
 have J (z:bI) (g:z∈W L i) (U:(f z).1=0) (j:Fin 5) (n:Fin 3):
   aA z n (τ j)=kJ w (if j=4 then s z else 0)
    (if o:j=4 then a z else if c (τ j)=w then(f z).2 ⟨j.1,by omega⟩ else 0)
    (if o:j=4 then b z else if c (τ j)=w then 0 else(f z).2 ⟨j.1,by omega⟩) n:=by
  by_cases o:j=4
  ·subst o;simpa[hτ4] using S z n
  ·have N:j∈({0,1,2,3}:Finset (Fin 5)):=by fin_cases j<;>simp at o ⊢
   have a1:aV z 0/3=0:=(u z).symm.trans U;have a0:(f z).2 ⟨j.1,by omega⟩=q (τ j) z:=by simp[f]
   rw[F z g (τ j) ((d j).mp N) n];rcases a5 j N with h|h
   ·rw[h];fin_cases n<;>simp[o,a0,kJ,q,gL,u,a1]<;>ring
   ·have a8: -1-w≠w:=fun e=>by
     have:(3:ℂ)=0:=by linear_combination(1+2*w)*e+4*Q
     norm_num at this
    rw[h];fin_cases n<;>simp[o,a8,a0,kJ,q,gL,u,a1]<;>ring
 have X:c (τ 0)=w:=rfl;by_cases E:c (τ 2)=w
 ·obtain⟨p,O,hp⟩:=R (0,![1,2,3,0]);have C (k:ℂ):a (p+k•r)=12∧s (p+k•r)*b (p+k•r)=108:=by
   let z:=p+k•r
   have g:z∈W L i:=(W L i).add_mem O ((W L i).smul_mem k P);have t:f z=(0,![1,2,3,0]):=by simp[z,map_add,map_smul,hp,show f r=0 from hr]
   exact aGi Q τ (s:=s z) (a:=a z) (b:=b z) (fun j n=>by
    rw[J z g (congrArg Prod.fst t)];fin_cases j<;>simp[X,Z,E,t])
    (T z g _ ((d 1).mp (by decide)) _ hτ0m) (T z g _ ((d 2).mp (by decide)) _ hτ0m)
  have K:a r=0:=by have q:=(C 0).1;have e1:=(C 1).1;simp only[map_add,map_smul,smul_eq_mul] at q e1;linear_combination e1-q
  have B:s r=0:=by by_contra hn;have e:=(C (-s p/s r)).2;simp only[map_add,map_smul,smul_eq_mul] at e;rw[div_mul_cancel₀ _ hn,add_neg_cancel,zero_mul] at e;norm_num at e
  have M:b r=0:=by by_contra hn;have e:=(C (-b p/b r)).2;simp only[map_add,map_smul,smul_eq_mul] at e;rw[div_mul_cancel₀ _ hn,add_neg_cancel,mul_zero] at e;norm_num at e
  exact H B K M
 ·have a6:c (τ 3)≠w:=fun e=>E ((a7.resolve_left E).trans e)
  obtain⟨p,O,hp⟩:=R (0,![1,-1,1,0]);obtain⟨B,K,M⟩:=aEk (s p) (a p) (b p) (s r) (a r) (b r) fun k=>by
   let z:=p+k•r
   have g:z∈W L i:=(W L i).add_mem O ((W L i).smul_mem k P);have t:f z=(0,![1,-1,1,0]):=by simp[z,map_add,map_smul,hp,show f r=0 from hr]
   simpa[z,map_add,map_smul,smul_eq_mul] using aHu Q τ (s:=s z) (a:=a z) (b:=b z) (fun j n=>by
    rw[J z g (congrArg Prod.fst t)];fin_cases j<;>simp[X,Z,E,a6,t])
    (T z g _ ((d 1).mp (by decide)) _ hτ0m)
    (T z g _ ((d 3).mp (by decide)) _ ((d 2).mp (by decide)))
  exact H B K M
lemma aEl {L:Submodule ℂ aC} (hL:aD L) {i:Fin 4}
  (o:Module.finrank ℂ (W L i)=6)
  {ω:ℂ} (hω:ω^2+ω+1=0) {c:Fin 5→ℂ}
  (d:∀j∈({0,1,2,3}:Finset (Fin 5)),c j=ω∨c j= -1-ω)
  (g:∀v∈W L i,∀j∈({0,1,2,3}:Finset (Fin 5)),∀r:Fin 3,
    aA v r j=aV v 0/3+ ![1,c j,-1-c j] r*(aA v 0 j-aV v 0/3))
  (s:∀v∈W L i,∀j∈({0,1,2,3}:Finset (Fin 5)),∀k∈({0,1,2,3}:Finset (Fin 5)),
    G v j=G v k):False:=by
 classical
 let a (j:Fin 5):Bool:=decide (c j=ω)
 obtain⟨τ,hτ4,p,q⟩:=aCt (a 0) (a 1) (a 2) (a 3);have b (j:Fin 5):j∈({0,1,2,3}:Finset (Fin 5))↔τ j∈({0,1,2,3}:Finset (Fin 5)):=by
  have n (k:Fin 5):k∈({0,1,2,3}:Finset (Fin 5))↔k≠4:=by fin_cases k<;>decide
  rw[n,n];exact⟨fun h e=>h (τ.injective (e.trans hτ4.symm)),fun h e=>h (e▸hτ4)⟩
 have f (j k:Fin 5) (hj:j∈({0,1,2,3}:Finset (Fin 5))) (hk:k∈({0,1,2,3}:Finset (Fin 5)))
   (h:(![a 0,a 1,a 2,a 3,false]:Fin 5→Bool) (τ j)=
     (![a 0,a 1,a 2,a 3,false]:Fin 5→Bool) (τ k)):c (τ j)=c (τ k):=by
  have l (m:Fin 5) (hm:m∈({0,1,2,3}:Finset (Fin 5))):(![a 0,a 1,a 2,a 3,false]:Fin 5→Bool) m=a m:=by fin_cases m<;>simp at hm ⊢
  rw[l _ ((b j).mp hj),l _ ((b k).mp hk)] at h;by_cases e:c (τ j)=ω
  ·rw[e,show c (τ k)=ω by simpa[a,e] using h.symm]
  ·rw[(d _ ((b j).mp hj)).resolve_left e,(d _ ((b k).mp hk)).resolve_left (by simpa[a,e] using h.symm)]
 exact aAk hL o hω d g s τ hτ4 (f 1 0 (by decide) (by decide) p)
  (q.imp (f 2 0 (by decide) (by decide)) (f 2 3 (by decide) (by decide)))
end M3
lemma sV:lT:=by
 intro L hL E i C
 classical
 obtain⟨L',B,a,N,M,F,t⟩:=M3.pN hL E C;have e:Module.finrank ℂ (W L' i)=6:=by have:=jP a i;omega
 have u (v:bI) (g:v∈W L' i):=t _ ((oM a).2 v g).2;have s (v:bI) (g:v∈W L' i):=t _ ((oM a).2 v g).1;rcases F with⟨rfl,J⟩|rfl
 ·have w:Module.finrank ℂ ((W L' i).map (aK {3,4}))≤3:=by
   have h:=dO a J {3,4} fun k=>by fin_cases k<;>simp
   norm_num at h;omega
  have n:4≤Module.finrank ℂ ((W L' i).map (aK {0,1,2})):=by
   by_contra! G
   let A:Finset (Fin 5):={0,1,2}
   have q:Aᶜ={3,4}:=by decide
   let X:bI:=fun p=>if p.2=3∨p.2=4 then 1 else 0
   have x (r:Fin 3) (k:Fin 5):aA X r k=(if k=3∨k=4 then 1 else 0)-1:=by simp only[aA,X,Fin.sum_univ_five];fin_cases k<;>norm_num
   have l:aK A X=aK A ((2/3:ℂ)•(1:bI)):=by
    funext ⟨k,r⟩;have f:=(A.equivFin.symm k).2;change aA X r (A.equivFin.symm k).1=aA ((2/3:ℂ)•(1:bI)) r (A.equivFin.symm k).1
    generalize (A.equivFin.symm k).1=j at f ⊢;rw[x]
    fin_cases j<;>simp[A] at f<;>norm_num[aA]
   have m:aK Aᶜ X=0:=by
    funext ⟨k,r⟩;have f:=(Aᶜ.equivFin.symm k).2;change aA X r (Aᶜ.equivFin.symm k).1=0
    generalize (Aᶜ.equivFin.symm k).1=j at f ⊢;rw[x]
    fin_cases j<;>simp[A] at f<;>norm_num
   change Module.finrank ℂ ((W L' i).map (aK A))<4 at G;exact iY a (by decide:(3:Fin 5)≠4)<|
    vZ (W L' i) A (by rw[q];omega)
     (l.symm▸⟨_,(W L' i).smul_mem _ (fN _ _),rfl⟩)
     (m.symm▸Submodule.zero_mem _)
  obtain⟨ω,c,hω,d,b⟩:=M3.qR (fN L' i) (by decide) n u;exact M3.aCs a e w hω d b fun v g=>s v g 0 (by decide) 1 (by decide)
 ·have n:4≤Module.finrank ℂ ((W L' i).map (aK {0,1,2,3})):=by
   have o:W L' i⊓LinearMap.ker (aK {0,1,2,3})≤W L' i⊓LinearMap.ker (jQ 4):=by
    rintro z ⟨K,y⟩;refine⟨K,funext fun⟨k,r⟩=> ?_⟩;have H:(4:Fin 5).succAbove k∈({0,1,2,3}:Finset (Fin 5)):=by fin_cases k<;>decide
    simpa[jQ,aA] using mN (show aK _ z=aK _ 0 by rw[map_zero];exact y) H r
   have O:=(Submodule.finrank_mono o).trans (fJ a i 4);have P:=cX (W L' i) (aK {0,1,2,3});omega
  obtain⟨ω,c,hω,d,b⟩:=M3.qR (fN L' i) (by decide) n u;exact M3.aEl a e hω d b s
end Ac.Af
lemma Ac.aGj:Ac.MidCase:=
 Ac.Af.uR Ac.Af.rG
  Ac.Af.pZ Ac.Af.sV
end
theorem bound215 : ∀ L : Submodule ℂ (Fin 4 × Fin 5 → ℂ), (∀ t ∈ L, (∑ i : Fin 4, ∑ j, t (i, j)) = 0 ∧ (∑ j, ∑ l, if j = l then 0 else ∑ a : Fin 4, ∑ b : Fin 4, if a < b then t (a, j) * t (b, l) else 0) = 0 ∧ (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, if a < b ∧ b < c then t (a, j) * t (b, l) * t (c, m) else 0) = 0 ∧ (∑ j, ∑ l, ∑ m, ∑ n, if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0 else t (0, j) * t (1, l) * t (2, m) * t (3, n)) = 0) → Module.finrank ℂ L ≤ 7 :=
 Ac.aAm Ac.aEn Ac.aGj Ac.aCb Ac.vV
  Ac.aFy Ac.aGe

end PEqualNP.Outside.L_gct_181

theorem PEqualNP.Outside.L_gct_181 : ¬ (∃ L : Submodule ℂ (Fin 4 × Fin 5 → ℂ), (∀ t ∈ L, (∑ i : Fin 4, ∑ j, t (i, j)) = 0 ∧ (∑ j, ∑ l, if j = l then 0 else ∑ a : Fin 4, ∑ b : Fin 4, if a < b then t (a, j) * t (b, l) else 0) = 0 ∧ (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, if a < b ∧ b < c then t (a, j) * t (b, l) * t (c, m) else 0) = 0 ∧ (∑ j, ∑ l, ∑ m, ∑ n, if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0 else t (0, j) * t (1, l) * t (2, m) * t (3, n)) = 0) ∧ 8 ≤ Module.finrank ℂ L) := by
  rintro ⟨L, hL, h8⟩
  have h := PEqualNP.Outside.L_gct_181.bound215 L hL
  omega
