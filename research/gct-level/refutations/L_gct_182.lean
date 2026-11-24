import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_182

namespace Gap183
open Finset
theorem sum_perm_succ {n : ℕ} (g : Equiv.Perm (Fin (n + 1)) → ℂ) :
    ∑ σ, g σ = ∑ a : Fin (n + 1), ∑ τ : Equiv.Perm (Fin n),
      g (Equiv.Perm.decomposeFin.symm (a, τ)) := by
  rw [← Equiv.Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]

theorem sum_perm_four (z : Fin 4 × Fin 4 → ℂ) :
    ∑ σ : Equiv.Perm (Fin 4), ∏ i, z (σ i, i) =
      z (0, 0) * z (1, 1) * z (2, 2) * z (3, 3) +
      z (0, 0) * z (1, 1) * z (3, 2) * z (2, 3) +
      z (0, 0) * z (2, 1) * z (1, 2) * z (3, 3) +
      z (0, 0) * z (2, 1) * z (3, 2) * z (1, 3) +
      z (0, 0) * z (3, 1) * z (1, 2) * z (2, 3) +
      z (0, 0) * z (3, 1) * z (2, 2) * z (1, 3) +
      z (1, 0) * z (0, 1) * z (2, 2) * z (3, 3) +
      z (1, 0) * z (0, 1) * z (3, 2) * z (2, 3) +
      z (1, 0) * z (2, 1) * z (0, 2) * z (3, 3) +
      z (1, 0) * z (2, 1) * z (3, 2) * z (0, 3) +
      z (1, 0) * z (3, 1) * z (0, 2) * z (2, 3) +
      z (1, 0) * z (3, 1) * z (2, 2) * z (0, 3) +
      z (2, 0) * z (0, 1) * z (1, 2) * z (3, 3) +
      z (2, 0) * z (0, 1) * z (3, 2) * z (1, 3) +
      z (2, 0) * z (1, 1) * z (0, 2) * z (3, 3) +
      z (2, 0) * z (1, 1) * z (3, 2) * z (0, 3) +
      z (2, 0) * z (3, 1) * z (0, 2) * z (1, 3) +
      z (2, 0) * z (3, 1) * z (1, 2) * z (0, 3) +
      z (3, 0) * z (0, 1) * z (1, 2) * z (2, 3) +
      z (3, 0) * z (0, 1) * z (2, 2) * z (1, 3) +
      z (3, 0) * z (1, 1) * z (0, 2) * z (2, 3) +
      z (3, 0) * z (1, 1) * z (2, 2) * z (0, 3) +
      z (3, 0) * z (2, 1) * z (0, 2) * z (1, 3) +
      z (3, 0) * z (2, 1) * z (1, 2) * z (0, 3)
 := by
  rw [sum_perm_succ]
  simp only [sum_perm_succ (n := 2), sum_perm_succ (n := 1), sum_perm_succ (n := 0)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ,
    Fintype.sum_unique]
  simp (config := { decide := true }) [Equiv.swap_apply_def]
  ring

theorem eval_perm_four (z : Fin 4 × Fin 4 → ℂ) :
    MvPolynomial.eval z (PEqualNP.Gct.permPoly ℂ 4) =
      z (0, 0) * z (1, 1) * z (2, 2) * z (3, 3) +
      z (0, 0) * z (1, 1) * z (3, 2) * z (2, 3) +
      z (0, 0) * z (2, 1) * z (1, 2) * z (3, 3) +
      z (0, 0) * z (2, 1) * z (3, 2) * z (1, 3) +
      z (0, 0) * z (3, 1) * z (1, 2) * z (2, 3) +
      z (0, 0) * z (3, 1) * z (2, 2) * z (1, 3) +
      z (1, 0) * z (0, 1) * z (2, 2) * z (3, 3) +
      z (1, 0) * z (0, 1) * z (3, 2) * z (2, 3) +
      z (1, 0) * z (2, 1) * z (0, 2) * z (3, 3) +
      z (1, 0) * z (2, 1) * z (3, 2) * z (0, 3) +
      z (1, 0) * z (3, 1) * z (0, 2) * z (2, 3) +
      z (1, 0) * z (3, 1) * z (2, 2) * z (0, 3) +
      z (2, 0) * z (0, 1) * z (1, 2) * z (3, 3) +
      z (2, 0) * z (0, 1) * z (3, 2) * z (1, 3) +
      z (2, 0) * z (1, 1) * z (0, 2) * z (3, 3) +
      z (2, 0) * z (1, 1) * z (3, 2) * z (0, 3) +
      z (2, 0) * z (3, 1) * z (0, 2) * z (1, 3) +
      z (2, 0) * z (3, 1) * z (1, 2) * z (0, 3) +
      z (3, 0) * z (0, 1) * z (1, 2) * z (2, 3) +
      z (3, 0) * z (0, 1) * z (2, 2) * z (1, 3) +
      z (3, 0) * z (1, 1) * z (0, 2) * z (2, 3) +
      z (3, 0) * z (1, 1) * z (2, 2) * z (0, 3) +
      z (3, 0) * z (2, 1) * z (0, 2) * z (1, 3) +
      z (3, 0) * z (2, 1) * z (1, 2) * z (0, 3)
 := by
  rw [← sum_perm_four]
  simp [PEqualNP.Gct.permPoly, Matrix.permanent, Matrix.mvPolynomialX_apply]

theorem level_of_sums (t : Fin 4 × Fin 4 → ℂ)
    (h : (∑ i : Fin 4, ∑ j, t (i, j)) = 0 ∧ (∑ j, ∑ l, if j = l then 0 else ∑ a : Fin 4, ∑ b : Fin 4, if a < b then t (a, j) * t (b, l) else 0) = 0 ∧ (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, if a < b ∧ b < c then t (a, j) * t (b, l) * t (c, m) else 0) = 0 ∧ (∑ j, ∑ l, ∑ m, ∑ n, if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0 else t (0, j) * t (1, l) * t (2, m) * t (3, n)) = 0) :
    MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ 4) = 24 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [eval_perm_four]
  simp only [Fin.sum_univ_four] at h1 h2 h3 h4
  simp (config := { decide := true }) only [ite_true, ite_false, add_zero, zero_add] at h2 h3 h4
  linear_combination 6 * h1 + 2 * h2 + h3 + h4

end Gap183

namespace PQ200
abbrev IX := Fin 3
abbrev V := IX → ℂ
abbrev M := IX × IX → ℂ
abbrev T := Fin 4 × Fin 4 → ℂ
abbrev U := Fin 2 × IX → ℂ
def dot (x y : M) : ℂ := ∑ i : IX, ∑ j : IX, x (i,j) * y (i,j)
def P (x : M) : ℂ := (Matrix.of fun i j : IX => x (i,j)).permanent
def pureR (L : Submodule ℂ M) : Prop :=
  ∃ (i : IX) (x : M), x ∈ L ∧ x ≠ 0 ∧ ∀ k, k ≠ i → ∀ j, x (k,j) = 0
def pureC (L : Submodule ℂ M) : Prop :=
  ∃ (j : IX) (x : M), x ∈ L ∧ x ≠ 0 ∧ ∀ k, k ≠ j → ∀ i, x (i,k) = 0
def H : Matrix (Fin 4) IX ℂ := !![1,1,1; 1,-1,-1; -1,1,-1; -1,-1,1]
def toT (x : M) : T := fun p => ∑ i : IX, ∑ j : IX, H p.1 i * x (i,j) * H p.2 j
def F (x : M) : ℂ := (Matrix.of fun i j : Fin 4 => toT x (i,j)).permanent
def udot (x y : U) : ℂ := ∑ i : Fin 2, ∑ j : IX, x (i,j) * y (i,j)
def S (z : V) : Matrix IX IX ℂ := !![0,z 2,z 1; z 2,0,z 0; z 1,z 0,0]
def op (z : V) (x : U) : U := fun p =>
  ∑ j : IX, S z p.2 j * x (if p.1 = 0 then 1 else 0,j)
abbrev Lev (L : Submodule ℂ T) :=
  ∀ t ∈ L, MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ 4) = 24
end PQ200

namespace PQ200
abbrev RowBlock := ∀ (L : Submodule ℂ M), 4 ≤ Module.finrank ℂ L →
    (∀ x ∈ L, P x = 0) → ¬pureR L → ¬pureC L → ∀ i : IX,
    (∀ v : V, ∃ x ∈ L, ∀ j, x (i,j) = v j) →
    ∃ (j : IX) (x : M), x ∈ L ∧ ∀ k l : IX, (x (k,l) ≠ 0 ↔ k ≠ i ∧ l ≠ j)
end PQ200

namespace PQ200
abbrev ColBlock := ∀ (L : Submodule ℂ M), 4 ≤ Module.finrank ℂ L →
    (∀ x ∈ L, P x = 0) → ¬pureR L → ¬pureC L → ∀ j : IX,
    (∀ v : V, ∃ x ∈ L, ∀ i, x (i,j) = v i) →
    ∃ (i : IX) (x : M), x ∈ L ∧ ∀ k l : IX, (x (k,l) ≠ 0 ↔ k ≠ i ∧ l ≠ j)
end PQ200

namespace PQ200
abbrev RowFalse := ∀ (L : Submodule ℂ M), 4 ≤ Module.finrank ℂ L →
    (∀ x ∈ L, ∀ y ∈ L, dot x y = 0) → (∀ x ∈ L, P x = 0) →
    (∀ x ∈ L, F x = 0) → pureR L → False
end PQ200

namespace PQ200
namespace FullRowAux

private theorem sum_succ {n : ℕ} (g : Equiv.Perm (Fin (n + 1)) → ℂ) :
    ∑ σ, g σ = ∑ a : Fin (n + 1), ∑ τ : Equiv.Perm (Fin n),
      g (Equiv.Perm.decomposeFin.symm (a, τ)) := by
  rw [← Equiv.Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]

private def tri (w u v : V) : ℂ :=
  w 0 * (u 1 * v 2 + u 2 * v 1) +
  w 1 * (u 0 * v 2 + u 2 * v 0) +
  w 2 * (u 0 * v 1 + u 1 * v 0)

private abbrev row (x : M) (i : IX) : V := fun j => x (i,j)

private theorem expand (x : M) : P x = tri (row x 0) (row x 1) (row x 2) := by
  unfold P Matrix.permanent IX
  rw [sum_succ]
  simp only [sum_succ (n := 1), sum_succ (n := 0)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ,
    Fintype.sum_unique]
  simp (config := { decide := true }) [Equiv.swap_apply_def, tri, row]
  ring

private theorem expand_any (x : M) (i r s : IX) (hir : i ≠ r) (his : i ≠ s)
    (hrs : r ≠ s) : P x = tri (row x i) (row x r) (row x s) := by
  rw [expand]
  fin_cases i <;> fin_cases r <;> fin_cases s <;>
    first | exact (hir rfl).elim | exact (his rfl).elim | exact (hrs rfl).elim | rfl |
      dsimp [tri, row]; ring

private theorem kernelVector (L : Submodule ℂ M) (hd : 4 ≤ Module.finrank ℂ L) (i : IX) :
    ∃ x ∈ L, x ≠ (0 : M) ∧ ∀ j, x (i,j) = 0 := by
  let f := (LinearMap.funLeft ℂ ℂ (fun j : IX => (i,j))).domRestrict L
  have hn : LinearMap.ker f ≠ ⊥ := by
    intro e
    have hh := LinearMap.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp e)
    have hv : Module.finrank ℂ V = 3 := by simp [V, IX, Module.finrank_fintype_fun_eq_card]
    change Module.finrank ℂ L ≤ Module.finrank ℂ V at hh
    omega
  obtain ⟨x,hx,hnx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  exact ⟨x.1,x.2,fun h => hnx (Subtype.ext h),congrFun (LinearMap.mem_ker.mp hx)⟩

private theorem crosses (L : Submodule ℂ M) (hP : ∀ x ∈ L, P x = 0)
    (i r s : IX) (hir : i ≠ r) (his : i ≠ s) (hrs : r ≠ s)
    (hf : ∀ v : V, ∃ x ∈ L, ∀ j, x (i,j) = v j)
    (x : M) (hx : x ∈ L) (hz : ∀ j, x (i,j) = 0) :
    ∀ a b : IX, a ≠ b → x (r,a) * x (s,b) + x (r,b) * x (s,a) = 0 := by
  have van (w : V) : tri w (row x r) (row x s) = 0 := by
    obtain ⟨y,hy,hyw⟩ := hf w
    have A := hP _ (L.add_mem hy hx)
    have B := hP _ (L.sub_mem hy hx)
    have C := hP _ hy
    rw [expand_any _ i r s hir his hrs] at A B C
    simp only [tri, row, Pi.add_apply, Pi.sub_apply, hz, add_zero, sub_zero, hyw] at A B C ⊢
    linear_combination (A + B)/2 - C
  have h12 := van ![1,0,0]
  have h02 := van ![0,1,0]
  have h01 := van ![0,0,1]
  simp [tri,row] at h12 h02 h01
  intro a b h
  fin_cases a <;> fin_cases b <;>
    first | exact (h rfl).elim | exact h12 | exact h02 | exact h01 |
      rw [add_comm]; first | exact h12 | exact h02 | exact h01

private theorem sameSupport (u v : V) (hv : ∃ j, v j ≠ 0)
    (h : ∀ a b : IX, a ≠ b → u a * v b + u b * v a = 0) :
    ∀ a, u a ≠ 0 → v a ≠ 0 := by
  intro a ha hzero
  obtain ⟨b,hb⟩ := hv
  have hab : a ≠ b := fun e => hb (e ▸ hzero)
  simpa [hzero,ha,hb] using h a b hab

private theorem missing (u v : V) (he : ∀ a, u a ≠ 0 → v a ≠ 0)
    (h : ∀ a b : IX, a ≠ b → u a * v b + u b * v a = 0) : ∃ a, u a = 0 := by
  by_contra! hn
  have eq : 2 * u 1 * u 2 * v 0 = 0 := by
    linear_combination u 2 * h 0 1 (by decide) + u 1 * h 0 2 (by decide) -
      u 0 * h 1 2 (by decide)
  simp [hn,he 0 (hn 0)] at eq

end FullRowAux

open FullRowAux in
theorem fullRowBlock (L : Submodule ℂ M) (hd : 4 ≤ Module.finrank ℂ L)
    (hP : ∀ x ∈ L, P x = 0) (hr : ¬pureR L) (hc : ¬pureC L) (i : IX)
    (hfull : ∀ v : V, ∃ x ∈ L, ∀ j, x (i,j) = v j) :
    ∃ (j : IX) (x : M), x ∈ L ∧ ∀ k l : IX, (x (k,l) ≠ 0 ↔ k ≠ i ∧ l ≠ j) := by
  classical
  obtain ⟨x,hx,hn,hz⟩ := kernelVector L hd i
  have rows : ∀ t : IX, ∃ r s : IX, t ≠ r ∧ t ≠ s ∧ r ≠ s ∧
      ∀ k : IX, k = t ∨ k = r ∨ k = s := by decide
  obtain ⟨r,s,hir,his,hrs,allrow⟩ := rows i
  have huv := crosses L hP i r s hir his hrs hfull x hx hz
  have hu : ∃ j, x (r,j) ≠ 0 := by
    by_contra! h
    apply hr
    refine ⟨s,x,hx,hn,?_⟩
    intro k hk l
    rcases allrow k with e|e|e
    · simpa [e] using hz l
    · simpa [e] using h l
    · exact (hk e).elim
  have hv : ∃ j, x (s,j) ≠ 0 := by
    by_contra! h
    apply hr
    refine ⟨r,x,hx,hn,?_⟩
    intro k hk l
    rcases allrow k with e|e|e
    · simpa [e] using hz l
    · exact (hk e).elim
    · simpa [e] using h l
  have ev := sameSupport (row x r) (row x s) hv huv
  have eu := sameSupport (row x s) (row x r) hu (by
    intro a b hab
    linear_combination huv a b hab)
  obtain ⟨j,hj⟩ := missing _ _ ev huv
  have hcol (l : IX) (hl : x (r,l) = 0) : ∀ k : IX, x (k,l) = 0 := by
    intro k
    rcases allrow k with e|e|e
    · simpa [e] using hz l
    · simpa [e] using hl
    · rw [e]
      by_contra h
      exact eu l h hl
  have one (l : IX) (hl : l ≠ j) : x (r,l) ≠ 0 := by
    intro h
    have third : ∀ j l : IX, l ≠ j → ∃ m : IX, ∀ a : IX, a = j ∨ a = l ∨ a = m := by decide
    obtain ⟨m,hm⟩ := third j l hl
    apply hc
    refine ⟨m,x,hx,hn,?_⟩
    intro a ha k
    rcases hm a with e|e|e
    · simpa [e] using hcol j hj k
    · simpa [e] using hcol l h k
    · exact (ha e).elim
  refine ⟨j,x,hx,?_⟩
  intro k l
  constructor
  · intro h
    exact ⟨fun e => h (e ▸ hz l),fun e => h (e ▸ hcol j hj k)⟩
  · rintro ⟨hk,hl⟩
    rcases allrow k with e|e|e
    · exact (hk e).elim
    · simpa [e] using one l hl
    · rw [e]
      exact ev l (one l hl)

end PQ200

namespace PQ200
namespace ColBlockAux

def tr : M ≃ₗ[ℂ] M := LinearEquiv.funCongrLeft ℂ ℂ (Equiv.prodComm IX IX)

theorem tr_apply (x : M) (a b : IX) : tr x (a, b) = x (b, a) := rfl

theorem tr_tr (x : M) : tr (tr x) = x := by
  funext p; rfl

theorem tr_ne_zero {x : M} (h : x ≠ 0) : tr x ≠ 0 := by
  simpa using h

theorem P_tr (x : M) : P (tr x) = P x := by
  unfold P
  rw [← Matrix.permanent_transpose]
  rfl

theorem mem_map {L : Submodule ℂ M} {y : M} :
    y ∈ L.map (tr : M →ₗ[ℂ] M) ↔ tr y ∈ L := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [LinearEquiv.coe_coe, tr_tr]; exact hx
  · intro h
    exact ⟨tr y, h, by rw [LinearEquiv.coe_coe, tr_tr]⟩

end ColBlockAux

open ColBlockAux in
theorem fullColBlock (base : RowBlock) (L : Submodule ℂ M)
    (hd : 4 ≤ Module.finrank ℂ L) (hP : ∀ x ∈ L, P x = 0)
    (hr : ¬pureR L) (hc : ¬pureC L) (j : IX)
    (hfull : ∀ v : V, ∃ x ∈ L, ∀ i, x (i,j) = v i) :
    ∃ (i : IX) (x : M), x ∈ L ∧ ∀ k l : IX, (x (k,l) ≠ 0 ↔ k ≠ i ∧ l ≠ j) := by
  obtain ⟨i, y, hy, hyb⟩ := base (L.map (tr : M →ₗ[ℂ] M))
    (by rw [LinearEquiv.finrank_map_eq]; exact hd)
    (fun y hy => by rw [← P_tr y]; exact hP _ (mem_map.1 hy))
    (fun ⟨i, y, hy, hy0, hz⟩ =>
      hc ⟨i, tr y, mem_map.1 hy, tr_ne_zero hy0, fun k hk a => hz k hk a⟩)
    (fun ⟨i, y, hy, hy0, hz⟩ =>
      hr ⟨i, tr y, mem_map.1 hy, tr_ne_zero hy0, fun k hk a => hz k hk a⟩)
    j
    (fun v => by
      obtain ⟨x, hx, hxv⟩ := hfull v
      exact ⟨tr x, mem_map.2 (by rw [tr_tr]; exact hx), fun a => hxv a⟩)
  refine ⟨i, tr y, mem_map.1 hy, fun k l => ?_⟩
  rw [tr_apply, hyb l k]
  exact and_comm

end PQ200

namespace PQ200

private noncomputable abbrev dE := dotProductEquiv ℂ (IX × IX)
private theorem de_apply (x y : M) : dE x y = dot x y := by
  change (∑ p, x p * y p) = _
  rw [Fintype.sum_prod_type]; rfl

private theorem dot_comm (x y : M) : dot x y = dot y x := by
  simp only [dot, mul_comm]

private theorem dot_extend (L : Submodule ℂ M) (hd : 4 ≤ Module.finrank ℂ L)
    (hq : ∀ x ∈ L, ∀ y ∈ L, dot x y = 0)
    (n m : M) (hn : ∀ x ∈ L, dot n x = 0) (hm : ∀ x ∈ L, dot m x = 0)
    (hnm : dot n m = 0) : n ∈ L ∨ m ∈ L := by
  classical
  by_contra! h
  let A := L ⊔ Submodule.span ℂ {n}
  let B := L ⊔ Submodule.span ℂ {m}
  have ho (x : A) : dE x.val ∈ B.dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro y hy
    obtain ⟨x₁,hx₁,_,hx₂,ex⟩ := Submodule.mem_sup.1 x.2
    obtain ⟨y₁,hy₁,_,hy₂,ey⟩ := Submodule.mem_sup.1 hy
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.1 hx₂
    obtain ⟨b,rfl⟩ := Submodule.mem_span_singleton.1 hy₂
    have hxm := (dot_comm x₁ m).trans (hm _ hx₁)
    change dE x.val y = 0
    rw [← ex, ← ey]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, de_apply,
      hq _ hx₁ _ hy₁, hxm, hn _ hy₁, hnm, smul_zero, add_zero]
  have hle := LinearMap.finrank_le_finrank_of_injective
    (f := (dE.toLinearMap.domRestrict A).codRestrict B.dualAnnihilator ho)
    (fun a b e => Subtype.ext (dE.injective (congrArg Subtype.val e)))
  have hA : Module.finrank ℂ A = Module.finrank ℂ L + 1 := Submodule.finrank_sup_span_singleton h.1
  have hB : Module.finrank ℂ B = Module.finrank ℂ L + 1 := Submodule.finrank_sup_span_singleton h.2
  have hh := Subspace.finrank_add_finrank_dualAnnihilator_eq B
  have hM : Module.finrank ℂ M = 9 := by simp [M, IX, Module.finrank_fintype_fun_eq_card]
  rw [hA] at hle
  rw [hB,hM] at hh
  omega

private def cell (s : Bool) (i j : IX) := if s then (j,i) else (i,j)
private abbrev full (s : Bool) (L : Submodule ℂ M) (i : IX) :=
  ∀ v : V, ∃ x ∈ L, ∀ j, x (cell s i j) = v j

private def normal (s : Bool) (i : IX) (v : V) (p : IX × IX) : ℂ :=
  if s then (if p.2 = i then v p.1 else 0) else (if p.1 = i then v p.2 else 0)

private theorem normal_eval (s i v) (x : M) :
    dot (normal s i v) x = ∑ j, v j * x (cell s i j) := by
  cases s <;> simp [normal, dot, cell, ite_mul]

private theorem defNormal (s : Bool) (L : Submodule ℂ M) (i : IX) (h : ¬ full s L i) :
    ∃ v : V, v ≠ 0 ∧ ∀ x ∈ L, dot (normal s i v) x = 0 := by
  classical
  let f : M →ₗ[ℂ] V := LinearMap.funLeft ℂ ℂ (cell s i)
  let W := L.map f
  have hn : W ≠ ⊤ := by
    intro e
    apply h
    intro v
    have hv : v ∈ W := e ▸ Submodule.mem_top
    obtain ⟨x,hx,ex⟩ := hv
    exact ⟨x,hx,congrFun ex⟩
  obtain ⟨g,hg,hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (mt Submodule.dualAnnihilator_eq_bot_iff.mp hn)
  let v := (dotProductEquiv ℂ IX).symm g
  have hev : dotProductEquiv ℂ IX v = g := (dotProductEquiv ℂ IX).apply_symm_apply _
  refine ⟨v, fun e => hg0 (by rw [← hev,e,map_zero]), ?_⟩
  intro x hx
  rw [normal_eval]
  change dotProductEquiv ℂ IX v (f x) = 0
  rw [hev]
  exact (Submodule.mem_dualAnnihilator _).mp hg _ ⟨x,hx,rfl⟩

private theorem twoFull_aux {F : IX → Prop} (h : ∀ i j, i ≠ j → ¬ F i → F j) :
    ∃ i j : IX, i ≠ j ∧ F i ∧ F j := by
  by_cases h0 : F 0
  · by_cases h1 : F 1
    · exact ⟨0,1,by decide,h0,h1⟩
    · exact ⟨0,2,by decide,h0,h 1 2 (by decide) h1⟩
  · exact ⟨1,2,by decide,h 0 1 (by decide) h0,h 0 2 (by decide) h0⟩

private theorem twoFull (s : Bool) (L : Submodule ℂ M) (hd : 4 ≤ Module.finrank ℂ L)
    (hq : ∀ x ∈ L, ∀ y ∈ L, dot x y = 0) (hr : ¬ pureR L) (hc : ¬ pureC L) :
    ∃ i j : IX, i ≠ j ∧ full s L i ∧ full s L j := by
  classical
  apply twoFull_aux
  intro i j hij hi
  by_contra hj
  obtain ⟨v,hv,hn⟩ := defNormal _ _ _ hi
  obtain ⟨w,hw,hm⟩ := defNormal _ _ _ hj
  have ho : dot (normal s i v) (normal s j w) = 0 := by
    rw [normal_eval]; cases s <;> simp [cell, normal, hij]
  have bad (k : IX) (u : V) (hu : u ≠ 0) (he : normal s k u ∈ L) : False := by
    have hne : normal s k u ≠ 0 := by
      intro e; apply hu; funext t
      have ev := congrFun e (cell s k t)
      cases s <;> simpa [cell, normal] using ev
    cases s with
    | false => exact hr ⟨k,_,he,hne,fun a ha b => by simp [normal,ha]⟩
    | true => exact hc ⟨k,_,he,hne,fun a ha b => by simp [normal,ha]⟩
  exact (dot_extend L hd hq _ _ hn hm ho).elim (bad _ _ hv) (bad _ _ hw)

private def block (L : Submodule ℂ M) (i j : IX) : Prop :=
  ∃ x ∈ L, ∀ k l, x (k,l) ≠ 0 ↔ k ≠ i ∧ l ≠ j

private theorem thirdIX {i j : IX} (h : i ≠ j) :
    ∃ k : IX, k ≠ i ∧ k ≠ j ∧ ∀ t, t ≠ i → t ≠ j → t = k := by
  revert h i j; decide

private theorem rook (L : Submodule ℂ M) (hq : ∀ x ∈ L, ∀ y ∈ L, dot x y = 0)
    {i j a b : IX} (h : block L i j) (g : block L a b) : i = a ∨ j = b := by
  classical
  by_contra! hn
  obtain ⟨x,hx,ex⟩ := h
  obtain ⟨y,hy,ey⟩ := g
  obtain ⟨k,hki,hka,uk⟩ := thirdIX hn.1
  obtain ⟨l,hlj,hlb,ul⟩ := thirdIX hn.2
  have v := hq _ hx _ hy
  unfold dot at v
  rw [Finset.sum_eq_single k] at v
  · rw [Finset.sum_eq_single l] at v
    · exact (mul_ne_zero ((ex k l).2 ⟨hki,hlj⟩) ((ey k l).2 ⟨hka,hlb⟩)) v
    · intro t _ ht
      by_contra! e
      exact ht (ul _ (((ex k t).1 ((mul_ne_zero_iff.mp e).1)).2)
        (((ey k t).1 ((mul_ne_zero_iff.mp e).2)).2))
    · simp
  · intro t _ ht
    apply Finset.sum_eq_zero
    intro u _
    by_contra! e
    exact ht (uk _ (((ex t u).1 ((mul_ne_zero_iff.mp e).1)).1)
      (((ey t u).1 ((mul_ne_zero_iff.mp e).2)).1))
  · simp

theorem fano_from_blocks (L : Submodule ℂ M) (hd : 4 ≤ Module.finrank ℂ L)
    (hq : ∀ x ∈ L, ∀ y ∈ L, dot x y = 0)
    (br : ¬ pureR L → ¬ pureC L → ∀ i : IX,
      (∀ v : V, ∃ x ∈ L, ∀ j, x (i,j) = v j) → ∃ (j : IX) (x : M), x ∈ L ∧
        ∀ k l : IX, (x (k,l) ≠ 0 ↔ k ≠ i ∧ l ≠ j))
    (bc : ¬ pureR L → ¬ pureC L → ∀ j : IX,
      (∀ v : V, ∃ x ∈ L, ∀ i, x (i,j) = v i) → ∃ (i : IX) (x : M), x ∈ L ∧
        ∀ k l : IX, (x (k,l) ≠ 0 ↔ k ≠ i ∧ l ≠ j)) : pureR L ∨ pureC L := by
  classical
  by_contra! hn
  obtain ⟨i,a,hia,fi,fa⟩ := twoFull false L hd hq hn.1 hn.2
  obtain ⟨j,b,hjb,fj,fb⟩ := twoFull true L hd hq hn.1 hn.2
  obtain ⟨u,hu⟩ := br hn.1 hn.2 i fi
  obtain ⟨v,hv⟩ := br hn.1 hn.2 a fa
  obtain ⟨r,hr⟩ := bc hn.1 hn.2 j fj
  obtain ⟨t,ht⟩ := bc hn.1 hn.2 b fb
  have euv := (rook L hq hu hv).resolve_left hia
  subst v
  have step {k z : IX} (hk : block L k z) : u = z := by
    rcases rook L hq hu hk with he | he
    · exact (rook L hq hv hk).resolve_left (by grind)
    · exact he
  exact hjb ((step hr).symm.trans (step ht))

theorem pure_exists (br : RowBlock) (bc : ColBlock) (L : Submodule ℂ M)
    (hd : 4 ≤ Module.finrank ℂ L) (hQ : ∀ x ∈ L, ∀ y ∈ L, dot x y = 0)
    (hP : ∀ x ∈ L, P x = 0) : pureR L ∨ pureC L :=
  fano_from_blocks L hd hQ (br L hd hP) (bc L hd hP)

end PQ200

namespace PQ200

private abbrev SpecU := Fin 2 × Fin 3 → ℂ
private noncomputable abbrev specDual := dotProductEquiv ℂ (Fin 2 × Fin 3)

private theorem specEigenIn (K : Submodule ℂ SpecU) (N : SpecU →ₗ[ℂ] SpecU)
    (hd : 3 ≤ Module.finrank ℂ K)
    (hq : ∀ x ∈ K, ∀ y ∈ K, specDual x y = 0)
    (hN : ∀ x ∈ K, ∀ y ∈ K, specDual (N x) y = 0) :
    ∃ (w : SpecU) (μ : ℂ), w ∈ K ∧ w ≠ 0 ∧ N w = μ • w := by
  classical
  let A := K.dualAnnihilator.map specDual.symm.toLinearMap
  have memA (w : SpecU) (hw : ∀ y ∈ K, specDual w y = 0) : w ∈ A := by
    exact ⟨specDual w, (Submodule.mem_dualAnnihilator _).mpr hw,
      specDual.symm_apply_apply w⟩
  have he : K = A := by
    apply Submodule.eq_of_le_of_finrank_le (fun w hw => memA w (hq w hw))
    have hm := Submodule.finrank_map_le specDual.symm.toLinearMap K.dualAnnihilator
    change Module.finrank ℂ A ≤ _ at hm
    have hh := Subspace.finrank_add_finrank_dualAnnihilator_eq K
    have hdU : Module.finrank ℂ SpecU = 6 := by
      simp [SpecU, Module.finrank_fintype_fun_eq_card]
    rw [hdU] at hh
    have count (a b : Nat) (he : a + b = 6) (ha : 3 ≤ a) : b ≤ a := by omega
    exact hm.trans (count _ _ hh hd)
  have hs (x : SpecU) (hx : x ∈ K) : N x ∈ K := he ▸ memA _ (hN _ hx)
  let F := N.restrict hs
  have : Nontrivial K := Module.finrank_pos_iff.mp (by omega : 0 < Module.finrank ℂ K)
  obtain ⟨μ,hμ⟩ := Module.End.exists_eigenvalue F
  obtain ⟨w,hw⟩ := hμ.exists_hasEigenvector
  exact ⟨w, μ, w.property, fun e => hw.2 (Subtype.ext e), congrArg Subtype.val hw.apply_eq_smul⟩

end PQ200

namespace PQ200

noncomputable def specS (z v : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![z 2 * v 1 + z 1 * v 2, z 2 * v 0 + z 0 * v 2, z 1 * v 0 + z 0 * v 1]

private theorem spec_coord (a b c u v w m : ℂ)
    (hq : a ^ 2 + b ^ 2 + c ^ 2 = 0)
    (hu : m*u = c*v + b*w) (hv : m*v = c*u + a*w) (hw : m*w = b*u + a*v) :
    (m^3 - 2*a*b*c)*u = 0 ∧
    3*m^2*u^2 = (m^2-a^2)*(u^2 + v^2 + w^2) := by
  constructor
  · linear_combination (m^2-a^2)*hu + (m*c+a*b)*hv + (m*b+a*c)*hw + m*u*hq
  · have e₁ : (m^2-b^2)*u = (m*c+a*b)*v := by linear_combination m*hu + b*hw
    have e₂ : (m^2-a^2)*v = (m*c+a*b)*u := by linear_combination m*hv + a*hw
    have e₃ : (m^2-c^2)*u = (m*b+a*c)*w := by linear_combination m*hu + c*hv
    have e₄ : (m^2-a^2)*w = (m*b+a*c)*u := by linear_combination m*hw + a*hv
    linear_combination u*e₁ - v*e₂ + u*e₃ - w*e₄ + u^2*hq

private theorem spec_facts (z v : Fin 3 → ℂ) (m : ℂ)
    (hq : ∑ i, z i ^ 2 = 0) (he : specS z v = m • v) (i : Fin 3) :
    (m^3 - 2*z 0*z 1*z 2)*v i = 0 ∧
    3*m^2*(v i)^2 = (m^2-(z i)^2)*(∑ j, (v j)^2) := by
  have h₀ : m*v 0 = z 2*v 1 + z 1*v 2 := (congrFun he 0).symm
  have h₁ : m*v 1 = z 2*v 0 + z 0*v 2 := (congrFun he 1).symm
  have h₂ : m*v 2 = z 1*v 0 + z 0*v 1 := (congrFun he 2).symm
  simp only [Fin.sum_univ_three] at hq ⊢
  fin_cases i
  · exact spec_coord _ _ _ _ _ _ _ hq h₀ h₁ h₂
  · have t := spec_coord (z 1) (z 0) (z 2) (v 1) (v 0) (v 2) m
      (by linear_combination hq) h₁ h₀ (by linear_combination h₂)
    change _ * v 1 = 0 ∧ 3*m^2*(v 1)^2 = (m^2-(z 1)^2)*_
    constructor
    · linear_combination t.1
    · linear_combination t.2
  · have t := spec_coord (z 2) (z 1) (z 0) (v 2) (v 1) (v 0) m
      (by linear_combination hq) (by linear_combination h₂)
      (by linear_combination h₁) (by linear_combination h₀)
    change _ * v 2 = 0 ∧ 3*m^2*(v 2)^2 = (m^2-(z 2)^2)*_
    constructor
    · linear_combination t.1
    · linear_combination t.2

theorem spec_no_iso (z x y : Fin 3 → ℂ) (μ : ℂ)
    (hz : ∀ i, z i ≠ 0) (hq : ∑ i, z i ^ 2 = 0) (hn : x ≠ 0 ∨ y ≠ 0)
    (hy : specS z y = μ • x) (hx : specS z x = μ • y)
    (hi : (∑ i, x i ^ 2) + (∑ i, y i ^ 2) = 0) : False := by
  let d := 2*z 0*z 1*z 2
  have hd : d ≠ 0 := by dsimp [d]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (hz 0)) (hz 1)) (hz 2)
  have hplus : specS z (x+y) = μ • (x+y) := by
    funext i
    have h := congrFun hx i
    have g := congrFun hy i
    fin_cases i <;> dsimp [specS] at h g ⊢ <;> linear_combination h + g
  have hminus : specS z (x-y) = (-μ) • (x-y) := by
    funext i
    have h := congrFun hx i
    have g := congrFun hy i
    fin_cases i <;> dsimp [specS] at h g ⊢ <;> linear_combination h - g
  have kill (m : ℂ) (v : Fin 3 → ℂ) (he : specS z v = m • v)
      (hm : m^3 ≠ d) : v = 0 := by
    funext i
    exact (mul_eq_zero.mp (spec_facts z v m hq he i).1).resolve_left (sub_ne_zero.mpr hm)
  have collapse (m : ℂ) (v : Fin 3 → ℂ) (he : specS z v = m • v)
      (hv : ∑ i, v i ^ 2 = 0) : v = 0 := by
    by_cases hm : m^3 = d
    · have hm₀ : m ≠ 0 := by
        intro h
        apply hd
        simpa [h] using hm.symm
      funext i
      have h := (spec_facts z v m hq he i).2
      rw [hv, mul_zero] at h
      simpa [hm₀] using h
    · exact kill m v he hm
  have hxy : x = y ∨ x = -y := by
    by_cases h : μ^3 = d
    · have h' : (-μ)^3 ≠ d := by
        intro t
        apply hd
        linear_combination (-1/2:ℂ)*t - (1/2:ℂ)*h
      exact Or.inl (sub_eq_zero.mp (kill _ _ hminus h'))
    · exact Or.inr (eq_neg_of_add_eq_zero_left (kill _ _ hplus h))
  rcases hxy with rfl | h
  · have hv : ∑ i, x i ^ 2 = 0 := by linear_combination hi / 2
    have h₀ := collapse μ x hx hv
    exact hn.elim (· h₀) (· h₀)
  · have hv : ∑ i, y i ^ 2 = 0 := by
      rw [h] at hi
      simp only [Pi.neg_apply, neg_sq] at hi
      linear_combination hi / 2
    have he : specS z y = (-μ) • y := by
      rw [hy, h, smul_neg, neg_smul]
    have h₀ := collapse (-μ) y he hv
    exact hn.elim (fun n => n (by simp [h, h₀])) (· h₀)

end PQ200
namespace PQ200

private noncomputable def specOp (z : V) : U →ₗ[ℂ] U where
  toFun := op z
  map_add' x y := by
    funext p
    simp [op, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    funext p
    simp [op, ← Finset.mul_sum, mul_left_comm]

private theorem specDual_udot (x y : U) : specDual x y = udot x y := by
  change ∑ p, x p * y p = _
  rw [Fintype.sum_prod_type]
  rfl

private theorem specOpRow (z : V) (w : U) (a : Fin 2) (i : IX) :
    op z w (a,i) = specS z (fun j => w (if a = 0 then 1 else 0,j)) i := by
  fin_cases i <;> simp [op, S, specS, Fin.sum_univ_three]

theorem spectrum (z : V) (hz : (∑ i, z i ^ 2) = 0) (hn : ∀ i, z i ≠ 0)
    (K : Submodule ℂ U) (hk : 3 ≤ Module.finrank ℂ K)
    (hQ : ∀ x ∈ K, ∀ y ∈ K, udot x y = 0)
    (hS : ∀ x ∈ K, ∀ y ∈ K, udot (op z x) y = 0) : False := by
  obtain ⟨w, μ, hw, hne, heq⟩ := specEigenIn K (specOp z) hk
    (fun _ hx _ hy => (specDual_udot ..).trans (hQ _ hx _ hy))
    (fun _ hx _ hy => (specDual_udot ..).trans (hS _ hx _ hy))
  apply spec_no_iso z (fun j => w (0,j)) (fun j => w (1,j)) μ hn hz
  · by_contra! h
    apply hne
    funext ⟨a,i⟩
    fin_cases a
    · exact congrFun h.1 i
    · exact congrFun h.2 i
  · funext i
    have he : op z w (0,i) = μ * w (0,i) := congrFun heq (0,i)
    simpa [specOpRow, Pi.smul_apply] using he
  · funext i
    have he : op z w (1,i) = μ * w (1,i) := congrFun heq (1,i)
    simpa [specOpRow, Pi.smul_apply] using he
  · simpa only [udot, Fin.sum_univ_two, pow_two] using hQ _ hw _ hw

end PQ200

namespace PQ200
namespace PureRed

def vv (z : V) (q : Fin 4) : ℂ := ∑ j : IX, z j * H q j

def srow (i : IX) (z : V) : M := fun p => if p.1 = i then z p.2 else 0
def r0 (i : IX) : IX := if i = 0 then 1 else 0
def r1 (i : IX) : IX := if i = 2 then 1 else 2
def proj (i : IX) : M →ₗ[ℂ] U where
  toFun x := fun p => x (if p.1 = 0 then r0 i else r1 i, p.2)
  map_add' x y := by funext p; rfl
  map_smul' c x := by funext p; rfl
def emb (i : IX) : U →ₗ[ℂ] M where
  toFun u := fun p => if p.1 = r0 i then u (0, p.2) else if p.1 = r1 i then u (1, p.2) else 0
  map_add' x y := by
    funext p; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' c x := by
    funext p; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> simp

theorem vv0 (z : V) : vv z 0 = z 0 + z 1 + z 2 := by
  simp [vv, H, Fin.sum_univ_three]
theorem vv1 (z : V) : vv z 1 = z 0 - z 1 - z 2 := by
  simp [vv, H, Fin.sum_univ_three]; ring
theorem vv2 (z : V) : vv z 2 = -z 0 + z 1 - z 2 := by
  simp [vv, H, Fin.sum_univ_three]; ring
theorem vv3 (z : V) : vv z 3 = -z 0 - z 1 + z 2 := by
  simp [vv, H, Fin.sum_univ_three]; ring

theorem Hprod (i : IX) : H 0 i * H 1 i * H 2 i * H 3 i = 1 := by
  fin_cases i <;> simp [H]

theorem P_eq (x : M) : P x =
    x (0,0) * x (1,1) * x (2,2) + x (0,0) * x (2,1) * x (1,2) +
    x (1,0) * x (0,1) * x (2,2) + x (1,0) * x (2,1) * x (0,2) +
    x (2,0) * x (0,1) * x (1,2) + x (2,0) * x (1,1) * x (0,2) := by
  unfold P Matrix.permanent
  rw [Gap183.sum_perm_succ]
  simp only [Gap183.sum_perm_succ (n := 1), Gap183.sum_perm_succ (n := 0)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ,
    Fintype.sum_unique, Matrix.of_apply]
  simp (config := { decide := true }) [Equiv.swap_apply_def]
  ring

theorem toT_line (i : IX) (z : V) (t : M) (c : ℂ) (p : Fin 4 × Fin 4) :
    toT (srow i z + c • t) p = H p.1 i * vv z p.2 + c * toT t p := by
  fin_cases i <;>
    simp [toT, srow, vv, Fin.sum_univ_three] <;> ring

theorem F_line (i : IX) (z : V) (t : M) (c : ℂ) :
    F (srow i z + c • t) = ∑ σ : Equiv.Perm (Fin 4), ∏ k,
      (fun p : Fin 4 × Fin 4 => H p.1 i * vv z p.2 + c * toT t p) (σ k, k) := by
  unfold F Matrix.permanent
  simp only [Matrix.of_apply, toT_line]

theorem fd (a v : Fin 4 → ℂ) (B : Fin 4 × Fin 4 → ℂ) (g : ℂ → ℂ)
    (hg : ∀ c, g c = ∑ σ : Equiv.Perm (Fin 4), ∏ k,
      (fun p : Fin 4 × Fin 4 => a p.1 * v p.2 + c * B p) (σ k, k)) :
    g 0 = 24 * (a 0 * a 1 * a 2 * a 3) * (v 0 * v 1 * v 2 * v 3) ∧
    8 * (g 1 - g (-1)) - (g 2 - g (-2)) = 72 * (
      v 1 * v 2 * v 3 * (a 1 * a 2 * a 3 * B (0,0) + a 0 * a 2 * a 3 * B (1,0) +
        a 0 * a 1 * a 3 * B (2,0) + a 0 * a 1 * a 2 * B (3,0)) +
      v 0 * v 2 * v 3 * (a 1 * a 2 * a 3 * B (0,1) + a 0 * a 2 * a 3 * B (1,1) +
        a 0 * a 1 * a 3 * B (2,1) + a 0 * a 1 * a 2 * B (3,1)) +
      v 0 * v 1 * v 3 * (a 1 * a 2 * a 3 * B (0,2) + a 0 * a 2 * a 3 * B (1,2) +
        a 0 * a 1 * a 3 * B (2,2) + a 0 * a 1 * a 2 * B (3,2)) +
      v 0 * v 1 * v 2 * (a 1 * a 2 * a 3 * B (0,3) + a 0 * a 2 * a 3 * B (1,3) +
        a 0 * a 1 * a 3 * B (2,3) + a 0 * a 1 * a 2 * B (3,3))) := by
  have e : ∀ c, g c = _ := fun c =>
    (hg c).trans (Gap183.sum_perm_four (fun p : Fin 4 × Fin 4 => a p.1 * v p.2 + c * B p))
  simp only [e]
  constructor <;> ring

theorem cofH (i : IX) (t : M) (q : Fin 4) :
    H 1 i * H 2 i * H 3 i * toT t (0,q) + H 0 i * H 2 i * H 3 i * toT t (1,q) +
      H 0 i * H 1 i * H 3 i * toT t (2,q) + H 0 i * H 1 i * H 2 i * toT t (3,q) =
    4 * vv (fun j => t (i,j)) q := by
  fin_cases i <;> simp [toT, vv, H, Fin.sum_univ_three] <;> ring

theorem core (y0 y1 y2 ρ0 ρ1 ρ2 : ℂ) (hs : y0 + y1 + y2 = 0)
    (hq : y0 ^ 2 + y1 ^ 2 + y2 ^ 2 = 0) (hne : ¬(y0 = 0 ∧ y1 = 0 ∧ y2 = 0)) :
    (y0 ≠ 0 ∧ y1 ≠ 0 ∧ y2 ≠ 0) ∧ (y0 * ρ0 + y1 * ρ1 + y2 * ρ2 = 0 →
      y0 * y1 * y2 * (ρ0 + ρ1 + ρ2) = 0 →
      ∃ α, ρ0 = α * y0 ∧ ρ1 = α * y1 ∧ ρ2 = α * y2) := by
  have aux : ∀ a b c : ℂ, a + b + c = 0 → a ^ 2 + b ^ 2 + c ^ 2 = 0 → a = 0 →
      b = 0 ∧ c = 0 := by
    intro a b c h1 h2 ha
    subst ha
    have hb : b ^ 2 = 0 := by linear_combination h2 / 2 + (b - (0 + b + c) / 2) * h1
    have hb' : b = 0 := by simpa using hb
    exact ⟨hb', by linear_combination h1 - hb'⟩
  have h0 : y0 ≠ 0 := fun h => hne ⟨h, aux y0 y1 y2 hs hq h⟩
  have h1 : y1 ≠ 0 := fun h => by
    have := aux y1 y0 y2 (by linear_combination hs) (by linear_combination hq) h
    exact hne ⟨this.1, h, this.2⟩
  have h2 : y2 ≠ 0 := fun h => by
    have := aux y2 y0 y1 (by linear_combination hs) (by linear_combination hq) h
    exact hne ⟨this.1, this.2, h⟩
  refine ⟨⟨h0, h1, h2⟩, fun hd he => ?_⟩
  have hρ : ρ0 + ρ1 + ρ2 = 0 := by
    rcases mul_eq_zero.1 he with h | h
    · exact absurd h (mul_ne_zero (mul_ne_zero h0 h1) h2)
    · exact h
  have h12 : y1 - y2 ≠ 0 := by
    intro h
    have : y1 ^ 2 = 0 := by
      linear_combination hq / 6 + (2 * y1 - y0) / 6 * hs + (3 * y1 + y2 - y0) / 6 * h
    exact h1 (by simpa using this)
  have d1 : ρ1 * y0 - ρ0 * y1 = 0 := by
    have : (ρ1 * y0 - ρ0 * y1) * (y1 - y2) = 0 := by
      linear_combination y0 * hd - ρ0 * hq - y2 * (y0 * hρ - ρ0 * hs)
    exact (mul_eq_zero.1 this).resolve_right h12
  have d2 : ρ2 * y0 - ρ0 * y2 = 0 := by
    linear_combination y0 * hρ - ρ0 * hs - d1
  refine ⟨ρ0 / y0, ?_, ?_, ?_⟩
  · field_simp
  · field_simp; linear_combination d1
  · field_simp; linear_combination d2

theorem alg (z r : V) (hz : z ≠ 0) (h2 : ∑ j, z j ^ 2 = 0)
    (hv : vv z 0 * vv z 1 * vv z 2 * vv z 3 = 0) :
    (∀ j, z j ≠ 0) ∧ ((∑ j, z j * r j) = 0 →
      vv z 1 * vv z 2 * vv z 3 * vv r 0 + vv z 0 * vv z 2 * vv z 3 * vv r 1 +
      vv z 0 * vv z 1 * vv z 3 * vv r 2 + vv z 0 * vv z 1 * vv z 2 * vv r 3 = 0 →
      ∃ α, ∀ j, r j = α * z j) := by
  simp only [vv0, vv1, vv2, vv3] at hv ⊢
  rw [Fin.sum_univ_three] at h2
  rw [Fin.sum_univ_three]
  have hne : ¬(z 0 = 0 ∧ z 1 = 0 ∧ z 2 = 0) := fun h => hz (by
    funext j; fin_cases j <;> simp [h.1, h.2.1, h.2.2])
  have all3 : ∀ {p : IX → Prop}, p 0 → p 1 → p 2 → ∀ j, p j := by
    intro p a b c j; fin_cases j <;> assumption
  rcases mul_eq_zero.1 hv with h | h3
  · rcases mul_eq_zero.1 h with h | h2'
    · rcases mul_eq_zero.1 h with h0 | h1
      · obtain ⟨⟨a, b, c⟩, k⟩ := core (z 0) (z 1) (z 2) (r 0) (r 1) (r 2)
          (by linear_combination h0) (by linear_combination h2) hne
        refine ⟨all3 a b c, fun hE2 hE1 => ?_⟩
        obtain ⟨α, p0, p1, p2⟩ := k (by linear_combination hE2) (by
          linear_combination (hE1 - (4*r 0*z 0^2 - 4*r 0*z 0*z 1 - 4*r 0*z 0*z 2 - 4*r 1*z 0*z 1 + 4*r 1*z 1^2 - 4*r 1*z 1*z 2 - 4*r 2*z 0*z 2 - 4*r 2*z 1*z 2 + 4*r 2*z 2^2) * h0) / 8)
        exact ⟨α, all3 p0 p1 p2⟩
      · obtain ⟨⟨a, b, c⟩, k⟩ := core (z 0) (-z 1) (-z 2) (r 0) (-r 1) (-r 2)
          (by linear_combination h1) (by linear_combination h2)
          (fun h => hne ⟨h.1, neg_eq_zero.1 h.2.1, neg_eq_zero.1 h.2.2⟩)
        refine ⟨all3 a (neg_ne_zero.1 b) (neg_ne_zero.1 c), fun hE2 hE1 => ?_⟩
        obtain ⟨α, p0, p1, p2⟩ := k (by linear_combination hE2) (by
          linear_combination (hE1 - (4*r 0*z 0^2 + 4*r 0*z 0*z 1 + 4*r 0*z 0*z 2 - 4*r 1*z 0*z 1 - 4*r 1*z 1^2 + 4*r 1*z 1*z 2 - 4*r 2*z 0*z 2 + 4*r 2*z 1*z 2 - 4*r 2*z 2^2) * h1) / 8)
        exact ⟨α, all3 p0 (by linear_combination -p1) (by linear_combination -p2)⟩
    · obtain ⟨⟨a, b, c⟩, k⟩ := core (-z 0) (z 1) (-z 2) (-r 0) (r 1) (-r 2)
        (by linear_combination h2') (by linear_combination h2)
        (fun h => hne ⟨neg_eq_zero.1 h.1, h.2.1, neg_eq_zero.1 h.2.2⟩)
      refine ⟨all3 (neg_ne_zero.1 a) b (neg_ne_zero.1 c), fun hE2 hE1 => ?_⟩
      obtain ⟨α, p0, p1, p2⟩ := k (by linear_combination hE2) (by
        linear_combination (hE1 - (-4*r 0*z 0^2 - 4*r 0*z 0*z 1 + 4*r 0*z 0*z 2 + 4*r 1*z 0*z 1 + 4*r 1*z 1^2 + 4*r 1*z 1*z 2 + 4*r 2*z 0*z 2 - 4*r 2*z 1*z 2 - 4*r 2*z 2^2) * h2') / 8)
      exact ⟨α, all3 (by linear_combination -p0) p1 (by linear_combination -p2)⟩
  · obtain ⟨⟨a, b, c⟩, k⟩ := core (-z 0) (-z 1) (z 2) (-r 0) (-r 1) (r 2)
      (by linear_combination h3) (by linear_combination h2)
      (fun h => hne ⟨neg_eq_zero.1 h.1, neg_eq_zero.1 h.2.1, h.2.2⟩)
    refine ⟨all3 (neg_ne_zero.1 a) (neg_ne_zero.1 b) c, fun hE2 hE1 => ?_⟩
    obtain ⟨α, p0, p1, p2⟩ := k (by linear_combination hE2) (by
      linear_combination (hE1 - (-4*r 0*z 0^2 + 4*r 0*z 0*z 1 - 4*r 0*z 0*z 2 + 4*r 1*z 0*z 1 - 4*r 1*z 1^2 - 4*r 1*z 1*z 2 + 4*r 2*z 0*z 2 + 4*r 2*z 1*z 2 + 4*r 2*z 2^2) * h3) / 8)
    exact ⟨α, all3 (by linear_combination -p0) (by linear_combination -p1) p2⟩

theorem rowLocal (i : IX) (z : V) (hz : z ≠ 0) (h2 : ∑ j, z j ^ 2 = 0)
    (hF : F (srow i z) = 0) :
    (∀ j, z j ≠ 0) ∧ ∀ t : M, (∑ j, z j * t (i,j)) = 0 →
      (∀ c : ℂ, F (srow i z + c • t) = 0) → ∃ α, ∀ j, t (i,j) = α * z j := by
  have hv : vv z 0 * vv z 1 * vv z 2 * vv z 3 = 0 := by
    have h := (fd (fun p => H p i) (vv z) (toT (0 : M)) (fun c => F (srow i z + c • (0 : M)))
      (fun c => F_line i z 0 c)).1
    simp only [smul_zero, add_zero, hF] at h
    have hp := Hprod i
    rw [hp] at h
    linear_combination -h / 24
  refine ⟨(alg z (fun j => z j) hz h2 hv).1, fun t hE2 hl => ?_⟩
  have h := (fd (fun p => H p i) (vv z) (toT t) (fun c => F (srow i z + c • t))
    (fun c => F_line i z t c)).2
  simp only [hl, cofH] at h
  exact (alg z (fun j => t (i,j)) hz h2 hv).2 hE2 (by linear_combination -h / 288)

theorem decomp (i : IX) (z : V) (x : M) (α : ℂ) (h : ∀ j, x (i,j) = α * z j) :
    x = α • srow i z + emb i (proj i x) := by
  funext ⟨k, j⟩
  fin_cases i <;> fin_cases k <;> simp [srow, emb, proj, r0, r1] <;> exact h j

theorem dot_emb (i : IX) (u u' : U) : dot (emb i u) (emb i u') = udot u u' := by
  fin_cases i <;> simp [dot, udot, emb, r0, r1, Fin.sum_univ_three, Fin.sum_univ_two]

theorem dot_srow (i : IX) (z : V) (t : M) : dot (srow i z) t = ∑ j, z j * t (i,j) := by
  fin_cases i <;> simp [dot, srow, Fin.sum_univ_three]

theorem P_emb (i : IX) (z : V) (u : U) :
    2 * P (srow i z + emb i u) = udot (op z u) u := by
  rw [P_eq]
  fin_cases i <;>
    simp [srow, emb, r0, r1, udot, op, S, Fin.sum_univ_three, Fin.sum_univ_two] <;> ring

theorem polar (z : V) (u u' : U) :
    udot (op z (u + u')) (u + u') =
      udot (op z u) u + udot (op z u') u' + 2 * udot (op z u) u' := by
  simp [udot, op, S, Fin.sum_univ_three, Fin.sum_univ_two]; ring

end PureRed

theorem pureReduction (L : Submodule ℂ M) (hd : 4 ≤ Module.finrank ℂ L)
    (hQ : ∀ x ∈ L, ∀ y ∈ L, dot x y = 0)
    (hP : ∀ x ∈ L, P x = 0) (hF : ∀ x ∈ L, F x = 0) (hr : pureR L) :
    ∃ (z : V) (K : Submodule ℂ U), (∑ i, z i^2) = 0 ∧ (∀ i, z i ≠ 0) ∧
      3 ≤ Module.finrank ℂ K ∧ (∀ x ∈ K, ∀ y ∈ K, udot x y = 0) ∧
      (∀ x ∈ K, ∀ y ∈ K, udot (op z x) y = 0) := by
  obtain ⟨i, s, hs, hs0, hrow⟩ := hr
  set z : V := fun j => s (i,j) with hzdef
  have hsz : s = PureRed.srow i z := by
    funext ⟨k, j⟩
    by_cases h : k = i
    · subst h; simp [PureRed.srow, hzdef]
    · simp [PureRed.srow, h, hrow k h j]
  have hsL : PureRed.srow i z ∈ L := hsz ▸ hs
  have hz0 : z ≠ 0 := by
    intro h
    apply hs0
    rw [hsz, h]
    funext p
    simp [PureRed.srow]
  have h2 : ∑ j, z j ^ 2 = 0 := by
    have h := hQ _ hsL _ hsL
    rw [PureRed.dot_srow] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro j _
    simp [PureRed.srow, sq]
  obtain ⟨hnz, hloc⟩ := PureRed.rowLocal i z hz0 h2 (hF _ hsL)
  have hprop : ∀ t ∈ L, ∃ α, ∀ j, t (i,j) = α * z j := by
    intro t ht
    apply hloc t
    · have h := hQ _ hsL t ht
      rwa [PureRed.dot_srow] at h
    · intro c
      exact hF _ (L.add_mem hsL (L.smul_mem c ht))
  have hemb : ∀ t ∈ L, PureRed.emb i (PureRed.proj i t) ∈ L := by
    intro t ht
    obtain ⟨α, hα⟩ := hprop t ht
    have e : PureRed.emb i (PureRed.proj i t) = t - α • PureRed.srow i z := by
      rw [eq_sub_iff_add_eq']
      exact (PureRed.decomp i z t α hα).symm
    rw [e]
    exact L.sub_mem ht (L.smul_mem α hsL)
  have hK : ∀ u ∈ L.map (PureRed.proj i), PureRed.emb i u ∈ L := by
    rintro u ⟨t, ht, rfl⟩
    exact hemb t ht
  refine ⟨z, L.map (PureRed.proj i), h2, hnz, ?_, ?_, ?_⟩
  · have hle : L ≤ Submodule.span ℂ {PureRed.srow i z} ⊔ (L.map (PureRed.proj i)).map (PureRed.emb i) := by
      intro t ht
      obtain ⟨α, hα⟩ := hprop t ht
      rw [PureRed.decomp i z t α hα]
      exact Submodule.add_mem_sup
        (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
        (Submodule.mem_map_of_mem (Submodule.mem_map_of_mem ht))
    have h1 := Submodule.finrank_mono hle
    have h2 := Submodule.finrank_add_le_finrank_add_finrank
      (Submodule.span ℂ {PureRed.srow i z}) ((L.map (PureRed.proj i)).map (PureRed.emb i))
    have h3 : Module.finrank ℂ (Submodule.span ℂ {PureRed.srow i z}) ≤ 1 :=
      (finrank_span_le_card ({PureRed.srow i z} : Set M)).trans (by simp)
    have h4 := Submodule.finrank_map_le (PureRed.emb i) (L.map (PureRed.proj i))
    omega
  · intro u hu u' hu'
    rw [← PureRed.dot_emb i]
    exact hQ _ (hK u hu) _ (hK u' hu')
  · intro u hu u' hu'
    have a := hP _ (L.add_mem hsL (hK u hu))
    have b := hP _ (L.add_mem hsL (hK u' hu'))
    have c := hP _ (L.add_mem hsL (hK (u + u') (Submodule.add_mem _ hu hu')))
    have a' := PureRed.P_emb i z u
    have b' := PureRed.P_emb i z u'
    have c' := PureRed.P_emb i z (u + u')
    rw [a, mul_zero] at a'
    rw [b, mul_zero] at b'
    rw [c, mul_zero, PureRed.polar, ← a', ← b'] at c'
    linear_combination -c' / 2

end PQ200

namespace PQ200

namespace ColFalseProof

private def tr : M →ₗ[ℂ] M where
  toFun x p := x (p.2, p.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem tr_injective : Function.Injective tr := by
  intro x y h
  funext ⟨i, j⟩
  exact congrFun h (j, i)

private theorem permanent_transpose {α : Type*} [Fintype α] [DecidableEq α] (A : Matrix α α ℂ) :
    A.transpose.permanent = A.permanent := by
  unfold Matrix.permanent
  refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm α)) _ _ fun σ => ?_
  refine Fintype.prod_equiv σ _ _ fun i => ?_
  simp

private theorem dot_tr (x y : M) : dot (tr x) (tr y) = dot x y := by
  unfold dot
  exact Finset.sum_comm

private theorem P_tr (x : M) : P (tr x) = P x := by
  unfold P
  exact permanent_transpose (Matrix.of fun i j : IX => x (i, j))

private theorem toT_tr (x : M) (a b : Fin 4) : toT (tr x) (a, b) = toT x (b, a) := by
  unfold toT
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  change H a i * x (j, i) * H b j = H b j * x (j, i) * H a i
  ring

private theorem F_tr (x : M) : F (tr x) = F x := by
  unfold F
  have hmat : (Matrix.of fun a b : Fin 4 => toT (tr x) (a, b)) =
      (Matrix.of fun a b : Fin 4 => toT x (a, b)).transpose := by
    ext a b
    exact toT_tr x a b
  rw [hmat]
  exact permanent_transpose _

private theorem pureR_map_tr {L : Submodule ℂ M} (hc : pureC L) :
    pureR (L.map tr) := by
  obtain ⟨j, x, hxL, hx0, hzero⟩ := hc
  refine ⟨j, tr x, ⟨x, hxL, rfl⟩, ?_, fun k hk i => hzero k hk i⟩
  intro h
  exact hx0 (tr_injective (h.trans (map_zero tr).symm))

private theorem finrank_map_tr (L : Submodule ℂ M) :
    Module.finrank ℂ (L.map tr) = Module.finrank ℂ L := by
  rw [← LinearMap.range_domRestrict]
  exact LinearMap.finrank_range_of_inj fun a b h => Subtype.ext (tr_injective h)

end ColFalseProof

open ColFalseProof in
theorem colFalse (base : RowFalse) (L : Submodule ℂ M) (hd : 4 ≤ Module.finrank ℂ L)
    (hQ : ∀ x ∈ L, ∀ y ∈ L, dot x y = 0)
    (hP : ∀ x ∈ L, P x = 0) (hF : ∀ x ∈ L, F x = 0) (hc : pureC L) : False := by
  apply base (L.map tr)
  · rw [finrank_map_tr]
    exact hd
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [dot_tr]
    exact hQ x hx y hy
  · rintro _ ⟨x, hx, rfl⟩
    rw [P_tr]
    exact hP x hx
  · rintro _ ⟨x, hx, rfl⟩
    rw [F_tr]
    exact hF x hx
  · exact pureR_map_tr hc

end PQ200

namespace PQ200
namespace WalshMomentProof
open Finset

private abbrev Perm := Equiv.Perm (Fin 4)

private theorem sum_perm_succ {n : ℕ} (g : Equiv.Perm (Fin (n + 1)) → ℂ) :
    ∑ σ, g σ = ∑ a : Fin (n + 1), ∑ τ : Equiv.Perm (Fin n),
      g (Equiv.Perm.decomposeFin.symm (a, τ)) := by
  rw [← Equiv.Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]

private def tuples (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ) : ℂ :=
  ∑ σ : Perm, f (σ 0) (σ 1) (σ 2) (σ 3)

private theorem permTuples (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ) :
    tuples f =
      f 0 1 2 3 + f 0 1 3 2 + f 0 2 1 3 + f 0 2 3 1 + f 0 3 1 2 + f 0 3 2 1 +
      f 1 0 2 3 + f 1 0 3 2 + f 1 2 0 3 + f 1 2 3 0 + f 1 3 0 2 + f 1 3 2 0 +
      f 2 0 1 3 + f 2 0 3 1 + f 2 1 0 3 + f 2 1 3 0 + f 2 3 0 1 + f 2 3 1 0 +
      f 3 0 1 2 + f 3 0 2 1 + f 3 1 0 2 + f 3 1 2 0 + f 3 2 0 1 + f 3 2 1 0 := by
  change (∑ σ : Perm, f (σ 0) (σ (0 : Fin 3).succ)
    (σ (0 : Fin 2).succ.succ) (σ (0 : Fin 1).succ.succ.succ)) = _
  rw [sum_perm_succ]
  simp only [sum_perm_succ (n := 2), sum_perm_succ (n := 1), sum_perm_succ (n := 0)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fintype.sum_unique,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ]
  simp (config := { decide := true }) [Equiv.swap_apply_def]
  ring

private abbrev W := Fin 4 → ℂ
private def c1 (u : W) := tuples (fun a _ _ _ => u a)
private def c2 (u v : W) := tuples (fun a b _ _ => u a * v b)
private def c3 (u v w : W) := tuples (fun a b c _ => u a * v b * w c)
private def col (t : T) (j : Fin 4) : W := fun i => t (i,j)

private def lin (t : T) : ℂ :=
  c1 (col t 0) + c1 (col t 1) + c1 (col t 2) + c1 (col t 3)
private def quad (t : T) : ℂ :=
  c2 (col t 0) (col t 1) + c2 (col t 0) (col t 2) + c2 (col t 0) (col t 3) +
  c2 (col t 1) (col t 2) + c2 (col t 1) (col t 3) + c2 (col t 2) (col t 3)
private def cub (t : T) : ℂ :=
  c3 (col t 0) (col t 1) (col t 2) + c3 (col t 0) (col t 1) (col t 3) +
  c3 (col t 0) (col t 2) (col t 3) + c3 (col t 1) (col t 2) (col t 3)

private def e1 (a b c d : ℂ) := a + b + c + d
private def e2 (a b c d : ℂ) := a*b + a*c + a*d + b*c + b*d + c*d
private def e3 (a b c d : ℂ) := a*b*c + a*b*d + a*c*d + b*c*d
private def coeff (f : ℂ → ℂ → ℂ → ℂ → ℂ) (t : T) : ℂ :=
  tuples (fun a b c d => f (t (a,0)) (t (b,1)) (t (c,2)) (t (d,3)))

set_option maxHeartbeats 2000000 in
private theorem coefIds (t : T) :
    coeff e1 t = lin t ∧ coeff e2 t = quad t ∧ coeff e3 t = cub t := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [lin, coeff, c1, permTuples, col, e1]
    ring
  · simp only [quad, coeff, c2, permTuples, col, e2]
    ring
  · simp only [cub, coeff, c3, permTuples, col, e3]
    ring

private theorem lineExpansion (t : T) (s : ℂ) :
    MvPolynomial.eval (fun p => 1 + s * t p) (PEqualNP.Gct.permPoly ℂ 4) =
      24 + s * lin t + s^2 * quad t + s^3 * cub t +
        s^4 * (Matrix.of fun i j => t (i,j)).permanent := by
  obtain ⟨h1,h2,h3⟩ := coefIds t
  rw [← h1, ← h2, ← h3]
  have hc : (∑ _ : Perm, (1 : ℂ)) = 24 := by
    simp [Perm, Fintype.card_perm, Nat.factorial]
  rw [← hc]
  simp only [PEqualNP.Gct.permPoly, Matrix.permanent, map_sum, map_mul,
    Matrix.mvPolynomialX_apply, MvPolynomial.eval_X, Matrix.of_apply, Fin.prod_univ_four,
    coeff, tuples, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  unfold e1 e2 e3
  ring

private def mix (u : V) : W := fun i => ∑ a, H i a * u a
private def y (x : M) (j : Fin 4) : V := fun a => mix (fun b => x (a,b)) j
private theorem col_eq (x : M) (j : Fin 4) : col (toT x) j = mix (y x j) := by
  funext i
  simp only [col, toT, mix, y, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

private def triple (u v w : V) : ℂ :=
  u 0 * v 1 * w 2 + u 0 * v 2 * w 1 + u 1 * v 0 * w 2 +
  u 1 * v 2 * w 0 + u 2 * v 0 * w 1 + u 2 * v 1 * w 0

private theorem mix_one (u : V) : c1 (mix u) = 0 := by
  rw [c1, permTuples]
  simp [mix, H, Fin.sum_univ_three]
  ring

private theorem mix_two (u v : V) : c2 (mix u) (mix v) = -8 * ∑ a, u a * v a := by
  rw [c2, permTuples]
  simp [mix, H, Fin.sum_univ_three]
  ring

set_option maxHeartbeats 2000000 in
private theorem mix_three (u v w : V) :
    c3 (mix u) (mix v) (mix w) = 8 * triple u v w := by
  rw [c3, permTuples]
  simp [mix, H, Fin.sum_univ_three, triple]
  ring

private theorem halfPair (u : V) :
    mix u 0 * mix u 1 + mix u 0 * mix u 2 + mix u 0 * mix u 3 +
    mix u 1 * mix u 2 + mix u 1 * mix u 3 + mix u 2 * mix u 3 = -2 * ∑ a, u a * u a := by
  simp [mix, H, Fin.sum_univ_three]
  ring

private theorem mixedQuad (x : M) : quad (toT x) = 16 * dot x x := by
  simp only [quad, col_eq, mix_two, ← mul_add]
  simp only [← Finset.sum_add_distrib, y, halfPair, dot]
  rw [← Finset.mul_sum]
  ring

private theorem triples_eq (t : Fin 4 → V) :
    triple (t 0) (t 1) (t 2) + triple (t 0) (t 1) (t 3) +
    triple (t 0) (t 2) (t 3) + triple (t 1) (t 2) (t 3) =
      c3 (fun j => t j 0) (fun j => t j 1) (fun j => t j 2) := by
  rw [c3, permTuples]
  unfold triple
  ring

private theorem perm_three (A : Matrix (Fin 3) (Fin 3) ℂ) :
    A.permanent = triple (A 0) (A 1) (A 2) := by
  have hu : (univ : Finset (Equiv.Perm (Fin 3))) =
      {1, Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2,
        Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.swap 1 2 * Equiv.swap 0 1} := by decide
  unfold Matrix.permanent
  rw [hu, sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_insert (by decide), sum_singleton]
  simp only [triple, Fin.prod_univ_three, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
    Equiv.Perm.one_apply]
  simp
  ring

private theorem mixedCub (x : M) : cub (toT x) = 64 * P x := by
  simp only [cub, col_eq, mix_three, ← mul_add, triples_eq, y, P, perm_three]
  let a := triple (fun b => x (0,b)) (fun b => x (1,b)) (fun b => x (2,b))
  change 8 * (8 * a) = 64 * a
  ring

theorem expansion (x : M) (s : ℂ) :
    MvPolynomial.eval (fun p => 1 + s * toT x p) (PEqualNP.Gct.permPoly ℂ 4) =
      24 + 16 * s^2 * dot x x + 64 * s^3 * P x + s^4 * F x := by
  rw [lineExpansion, mixedQuad, mixedCub]
  simp only [lin, col_eq, mix_one, add_zero, mul_zero]
  unfold F
  ring

end WalshMomentProof

theorem walshMoments (x : M)
    (hl : ∀ s : ℂ, MvPolynomial.eval (fun p => 1 + s * toT x p)
        (PEqualNP.Gct.permPoly ℂ 4) = 24) : dot x x = 0 ∧ P x = 0 ∧ F x = 0 := by
  simp only [WalshMomentProof.expansion] at hl
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (16 * (hl 1 + hl (-1)) - (hl 2 + hl (-2))) / 384
  · linear_combination (hl 1 - hl (-1)) / 128
  · linear_combination ((hl 2 + hl (-2)) - 4 * (hl 1 + hl (-1))) / 24

end PQ200

namespace PQ200

private theorem inverse1 (z : Fin 4 → ℂ) (hz : ∑ k, z k = 0) (i : Fin 4) :
    (∑ a : IX, H i a * ((z 0 + z a.succ) / 2)) = z i := by
  rw [Fin.sum_univ_four] at hz
  fin_cases i <;> norm_num [H, Fin.sum_univ_three] <;>
    first | linear_combination hz / 2 | linear_combination -hz / 2

private noncomputable def coords : T →ₗ[ℂ] M where
  toFun t p := ((t (0,0) + t (0,p.2.succ)) / 2 +
                (t (p.1.succ,0) + t (p.1.succ,p.2.succ)) / 2) / 2
  map_add' x y := by funext p; simp only [Pi.add_apply]; ring
  map_smul' c x := by funext p; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem toT_coords (t : T)
    (hr : ∀ i : Fin 4, ∑ j, t (i,j) = 0)
    (hc : ∀ j : Fin 4, ∑ i, t (i,j) = 0) : toT (coords t) = t := by
  let v (r : Fin 4) (b : IX) := (t (r,0) + t (r,b.succ)) / 2
  have hvc (b : IX) : ∑ r, v r b = 0 := by
    simp only [v, ← Finset.sum_div, Finset.sum_add_distrib, hc, add_zero, zero_div]
  funext ⟨i,j⟩
  rw [toT, Finset.sum_comm]
  calc
    _ = ∑ b : IX, (∑ a : IX, H i a * ((v 0 b + v a.succ b) / 2)) * H j b := by
      simp only [Finset.sum_mul]; rfl
    _ = ∑ b : IX, H j b * v i b := by
      apply Finset.sum_congr rfl
      intro b _
      rw [inverse1 (fun r => v r b) (hvc b) i, mul_comm]
    _ = _ := inverse1 (fun s => t (i,s)) (hr i) j

theorem coords_preserve_dim (L : Submodule ℂ T)
    (hc : ∀ t ∈ L, (∀ i : Fin 4, ∑ j, t (i,j) = 0) ∧
                   (∀ j : Fin 4, ∑ i, t (i,j) = 0)) :
    Module.finrank ℂ (L.map coords) = Module.finrank ℂ L := by
  have hi : Function.Injective (coords.domRestrict L) := by
    intro x y e
    apply Subtype.ext
    calc
      x.val = toT (coords x.val) := (toT_coords _ (hc _ x.2).1 (hc _ x.2).2).symm
      _ = toT (coords y.val) := congrArg toT e
      _ = y.val := toT_coords _ (hc _ y.2).1 (hc _ y.2).2
  rw [← LinearMap.range_domRestrict L coords]
  exact LinearMap.finrank_range_of_inj hi

end PQ200
namespace PQ200

private theorem polarWalsh (x y : M) :
    dot (x+y) (x+y) = dot x x + dot y y + 2 * dot x y := by
  simp only [dot, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
  simp_rw [fun i j : IX => mul_comm (y (i,j)) (x (i,j))]
  ring

theorem walsh (L : Submodule ℂ T)
    (hr : ∀ t ∈ L, ∀ i : Fin 4, (∑ j, t (i,j)) = 0)
    (hc : ∀ t ∈ L, ∀ j : Fin 4, (∑ i, t (i,j)) = 0) (hl : Lev L) :
    ∃ W : Submodule ℂ M, Module.finrank ℂ L ≤ Module.finrank ℂ W ∧
      (∀ x ∈ W, ∀ y ∈ W, dot x y = 0) ∧ (∀ x ∈ W, P x = 0) ∧
      (∀ x ∈ W, F x = 0) := by
  let W := L.map coords
  have hm (x : M) (hx : x ∈ W) : dot x x = 0 ∧ P x = 0 ∧ F x = 0 := by
    obtain ⟨t, ht, rfl⟩ := hx
    apply walshMoments
    intro s
    rw [toT_coords t (hr t ht) (hc t ht)]
    exact hl _ (L.smul_mem s ht)
  refine ⟨W, (coords_preserve_dim L (fun t ht => ⟨hr t ht, hc t ht⟩)).ge, ?_,
    fun x hx => (hm x hx).2.1, fun x hx => (hm x hx).2.2⟩
  intro x hx y hy
  have e := (hm _ (W.add_mem hx hy)).1
  rw [polarWalsh, (hm x hx).1, (hm y hy).1, zero_add, zero_add] at e
  exact (mul_eq_zero.mp e).resolve_left (by norm_num)

end PQ200

namespace PQ200
theorem bound (L : Submodule ℂ T)
    (hr : ∀ t ∈ L, ∀ i : Fin 4, (∑ j, t (i,j)) = 0)
    (hc : ∀ t ∈ L, ∀ j : Fin 4, (∑ i, t (i,j)) = 0) (hl : Lev L) :
    Module.finrank ℂ L ≤ 3 := by
  by_contra! h
  obtain ⟨W, hdim, hQ, hP, hF⟩ := walsh L hr hc hl
  have hw : 4 ≤ Module.finrank ℂ W := (Nat.succ_le_of_lt h).trans hdim
  have hrow : RowFalse := by
    intro A ha hq hp hf r
    obtain ⟨z, K, hz, hn, hk, hq', hs⟩ := pureReduction A ha hq hp hf r
    exact spectrum z hz hn K hk hq' hs
  rcases pure_exists fullRowBlock (fullColBlock fullRowBlock) W hw hQ hP with r | c
  · exact hrow W hw hQ hP hF r
  · exact colFalse hrow W hw hQ hP hF c

end PQ200

theorem bound216 : ∀ L : Submodule ℂ (Fin 4 × Fin 4 → ℂ), (∀ t ∈ L, (∀ i : Fin 4, ∑ j, t (i, j) = 0) ∧ (∀ j : Fin 4, ∑ i, t (i, j) = 0) ∧ (∑ j, ∑ l, if j = l then 0 else ∑ a : Fin 4, ∑ b : Fin 4, if a < b then t (a, j) * t (b, l) else 0) = 0 ∧ (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, if a < b ∧ b < c then t (a, j) * t (b, l) * t (c, m) else 0) = 0 ∧ (∑ j, ∑ l, ∑ m, ∑ n, if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0 else t (0, j) * t (1, l) * t (2, m) * t (3, n)) = 0) → Module.finrank ℂ L ≤ 3 := by
  intro L hm
  have hr : ∀ t ∈ L, ∀ i : Fin 4, (∑ j, t (i,j)) = 0 := fun t ht => (hm t ht).1
  have hc : ∀ t ∈ L, ∀ j : Fin 4, (∑ i, t (i,j)) = 0 := fun t ht => (hm t ht).2.1
  apply PQ200.bound L hr hc
  intro t ht
  apply Gap183.level_of_sums
  have h := hr t ht
  exact ⟨by simp [h], (hm t ht).2.2⟩


end PEqualNP.Outside.L_gct_182

theorem PEqualNP.Outside.L_gct_182 : ¬ (∃ L : Submodule ℂ (Fin 4 × Fin 4 → ℂ), (∀ t ∈ L, (∀ i : Fin 4, ∑ j, t (i, j) = 0) ∧ (∀ j : Fin 4, ∑ i, t (i, j) = 0) ∧ (∑ j, ∑ l, if j = l then 0 else ∑ a : Fin 4, ∑ b : Fin 4, if a < b then t (a, j) * t (b, l) else 0) = 0 ∧ (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, if a < b ∧ b < c then t (a, j) * t (b, l) * t (c, m) else 0) = 0 ∧ (∑ j, ∑ l, ∑ m, ∑ n, if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0 else t (0, j) * t (1, l) * t (2, m) * t (3, n)) = 0) ∧ Module.finrank ℂ L = 4) := by
  rintro ⟨L, hL, hr⟩
  have h := PEqualNP.Outside.L_gct_182.bound216 L hL
  omega
