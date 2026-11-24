import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_194

theorem sumEmb (G : (Fin 4 ↪ Fin 5) → ℂ) :
    ∑ f, G f = ∑ σ : Equiv.Perm (Fin 5), G (Fin.castSuccEmb.trans σ.toEmbedding) := by
  have hinj : Function.Injective
      (fun σ : Equiv.Perm (Fin 5) => Fin.castSuccEmb.trans σ.toEmbedding) := by
    intro σ τ h
    have h' : ∀ i : Fin 4, σ (Fin.castSucc i) = τ (Fin.castSucc i) := fun i =>
      DFunLike.congr_fun h i
    have hl : σ (Fin.last 4) = τ (Fin.last 4) := by
      by_contra hne
      obtain ⟨z, hz⟩ := τ.surjective (σ (Fin.last 4))
      induction z using Fin.lastCases with
      | last => exact hne hz.symm
      | cast i =>
        rw [← h' i] at hz
        exact Fin.castSucc_ne_last i (σ.injective hz)
    ext x
    induction x using Fin.lastCases with
    | last => rw [hl]
    | cast i => rw [h' i]
  have hbij : Function.Bijective
      (fun σ : Equiv.Perm (Fin 5) => Fin.castSuccEmb.trans σ.toEmbedding) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    rw [Fintype.card_perm, Fintype.card_embedding_eq]
    rfl
  exact (hbij.sum_comp G).symm

theorem sumPerm5 (f : Equiv.Perm (Fin 5) → ℂ) : ∑ σ, f σ =
    ∑ a : Fin 5, ∑ b : Fin 4, ∑ c : Fin 3, ∑ d : Fin 2, ∑ e : Fin 1,
      f (Equiv.Perm.decomposeFin.symm (a, Equiv.Perm.decomposeFin.symm (b,
        Equiv.Perm.decomposeFin.symm (c, Equiv.Perm.decomposeFin.symm (d,
          Equiv.Perm.decomposeFin.symm (e, 1)))))) := by
  rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Fintype.sum_unique]
  rfl

theorem key (F : ℕ → ℕ → ℕ → ℕ → ℂ) :
    ∑ σ : Equiv.Perm (Fin 5), F (σ (Fin.castSucc 0)).val (σ (Fin.castSucc 1)).val
      (σ (Fin.castSucc 2)).val (σ (Fin.castSucc 3)).val =
    ((((F 0 1 2 3 + F 0 1 2 4) + ((F 0 1 3 2 + F 0 1 3 4) + (F 0 1 4 3 + F 0 1 4 2))) + (((F 0 2 1 3 + F 0 2 1 4) + ((F 0 2 3 1 + F 0 2 3 4) + (F 0 2 4 3 + F 0 2 4 1))) + (((F 0 3 2 1 + F 0 3 2 4) + ((F 0 3 1 2 + F 0 3 1 4) + (F 0 3 4 1 + F 0 3 4 2))) + ((F 0 4 2 3 + F 0 4 2 1) + ((F 0 4 3 2 + F 0 4 3 1) + (F 0 4 1 3 + F 0 4 1 2)))))) + ((((F 1 0 2 3 + F 1 0 2 4) + ((F 1 0 3 2 + F 1 0 3 4) + (F 1 0 4 3 + F 1 0 4 2))) + (((F 1 2 0 3 + F 1 2 0 4) + ((F 1 2 3 0 + F 1 2 3 4) + (F 1 2 4 3 + F 1 2 4 0))) + (((F 1 3 2 0 + F 1 3 2 4) + ((F 1 3 0 2 + F 1 3 0 4) + (F 1 3 4 0 + F 1 3 4 2))) + ((F 1 4 2 3 + F 1 4 2 0) + ((F 1 4 3 2 + F 1 4 3 0) + (F 1 4 0 3 + F 1 4 0 2)))))) + ((((F 2 1 0 3 + F 2 1 0 4) + ((F 2 1 3 0 + F 2 1 3 4) + (F 2 1 4 3 + F 2 1 4 0))) + (((F 2 0 1 3 + F 2 0 1 4) + ((F 2 0 3 1 + F 2 0 3 4) + (F 2 0 4 3 + F 2 0 4 1))) + (((F 2 3 0 1 + F 2 3 0 4) + ((F 2 3 1 0 + F 2 3 1 4) + (F 2 3 4 1 + F 2 3 4 0))) + ((F 2 4 0 3 + F 2 4 0 1) + ((F 2 4 3 0 + F 2 4 3 1) + (F 2 4 1 3 + F 2 4 1 0)))))) + ((((F 3 1 2 0 + F 3 1 2 4) + ((F 3 1 0 2 + F 3 1 0 4) + (F 3 1 4 0 + F 3 1 4 2))) + (((F 3 2 1 0 + F 3 2 1 4) + ((F 3 2 0 1 + F 3 2 0 4) + (F 3 2 4 0 + F 3 2 4 1))) + (((F 3 0 2 1 + F 3 0 2 4) + ((F 3 0 1 2 + F 3 0 1 4) + (F 3 0 4 1 + F 3 0 4 2))) + ((F 3 4 2 0 + F 3 4 2 1) + ((F 3 4 0 2 + F 3 4 0 1) + (F 3 4 1 0 + F 3 4 1 2)))))) + (((F 4 1 2 3 + F 4 1 2 0) + ((F 4 1 3 2 + F 4 1 3 0) + (F 4 1 0 3 + F 4 1 0 2))) + (((F 4 2 1 3 + F 4 2 1 0) + ((F 4 2 3 1 + F 4 2 3 0) + (F 4 2 0 3 + F 4 2 0 1))) + (((F 4 3 2 1 + F 4 3 2 0) + ((F 4 3 1 2 + F 4 3 1 0) + (F 4 3 0 1 + F 4 3 0 2))) + ((F 4 0 2 3 + F 4 0 2 1) + ((F 4 0 3 2 + F 4 0 3 1) + (F 4 0 1 3 + F 4 0 1 2)))))))))) := by
  rw [sumPerm5]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  rfl

end PEqualNP.Outside.L_gct_194

theorem PEqualNP.Outside.L_gct_194 :
    ∀ c d : ℂ, (∑ f : Fin 4 ↪ Fin 5, ∏ j : Fin 4, (1 + (if (f j).val = 4 then d * (if j.val = 0 then (1 : ℂ) else if j.val = 1 then -1 else 0) else c * (if j.val = (f j).val then (1 : ℂ) else if j.val = ((f j).val + 1) % 4 then Complex.I else if j.val = ((f j).val + 2) % 4 then -Complex.I else -1)))) = 120 := by
  intro c d
  let T : Fin 4 → ℕ → ℂ := fun j s => 1 + (if s = 4 then d * (if j.val = 0 then (1 : ℂ) else if j.val = 1 then -1 else 0) else c * (if j.val = s then (1 : ℂ) else if j.val = (s + 1) % 4 then Complex.I else if j.val = (s + 2) % 4 then -Complex.I else -1))
  refine (PEqualNP.Outside.L_gct_194.sumEmb _).trans ?_
  show ∑ σ : Equiv.Perm (Fin 5), ∏ j : Fin 4, T j (σ (Fin.castSucc j)).val = 120
  simp only [Fin.prod_univ_four]
  rw [PEqualNP.Outside.L_gct_194.key (fun a b e g => T 0 a * T 1 b * T 2 e * T 3 g)]
  have t00 : T 0 0 = 1 + c * (1) := by simp only [T]; norm_num
  have t01 : T 0 1 = 1 + c * (-1) := by simp only [T]; norm_num
  have t02 : T 0 2 = 1 + c * (-Complex.I) := by simp only [T]; norm_num
  have t03 : T 0 3 = 1 + c * (Complex.I) := by simp only [T]; norm_num
  have t04 : T 0 4 = 1 + d * (1) := by simp only [T]; norm_num
  have t10 : T 1 0 = 1 + c * (Complex.I) := by simp only [T]; norm_num
  have t11 : T 1 1 = 1 + c * (1) := by simp only [T]; norm_num
  have t12 : T 1 2 = 1 + c * (-1) := by simp only [T]; norm_num
  have t13 : T 1 3 = 1 + c * (-Complex.I) := by simp only [T]; norm_num
  have t14 : T 1 4 = 1 + d * (-1) := by simp only [T]; norm_num
  have t20 : T 2 0 = 1 + c * (-Complex.I) := by simp only [T]; norm_num
  have t21 : T 2 1 = 1 + c * (Complex.I) := by simp only [T]; norm_num
  have t22 : T 2 2 = 1 + c * (1) := by simp only [T]; norm_num
  have t23 : T 2 3 = 1 + c * (-1) := by simp only [T]; norm_num
  have t24 : T 2 4 = 1 + d * (0) := by simp only [T]; norm_num
  have t30 : T 3 0 = 1 + c * (-1) := by simp only [T]; norm_num
  have t31 : T 3 1 = 1 + c * (-Complex.I) := by simp only [T]; norm_num
  have t32 : T 3 2 = 1 + c * (Complex.I) := by simp only [T]; norm_num
  have t33 : T 3 3 = 1 + c * (1) := by simp only [T]; norm_num
  have t34 : T 3 4 = 1 + d * (0) := by simp only [T]; norm_num
  simp only [t00, t01, t02, t03, t04, t10, t11, t12, t13, t14, t20, t21, t22, t23, t24, t30, t31, t32, t33, t34]
  linear_combination (2*Complex.I^2*c^4 - 8*Complex.I*c^4 + 2*c^4 + 24*c^2) * Complex.I_sq
