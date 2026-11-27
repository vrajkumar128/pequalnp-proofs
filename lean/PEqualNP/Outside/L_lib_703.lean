import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_703

open Matrix Finset

def sg (b : Bool) : ℝ := if b then -1 else 1

def eps {n : ℕ} (s : Fin n × Fin n → Bool) (i j : Fin n) : ℝ := if s (i, j) then -1 else 1

noncomputable def posb {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (s : Fin n × Fin n → Bool) (b : Bool) (i j : Fin n) : ℝ :=
  if eps s i j * |H i j| = sg b * H i j then |H i j| else 0

noncomputable def Rb {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (s : Fin n × Fin n → Bool) (b : Bool) (i j : Fin n) : ℝ :=
  if eps s i j * |H i j| = sg b * H i j then H i j else 0

theorem sg_sq (b : Bool) : sg b * sg b = 1 := by cases b <;> simp [sg]

theorem prod_sg_sq {n : ℕ} (u : Fin n → Bool) : (∏ i, sg (u i)) * (∏ i, sg (u i)) = 1 := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one (fun i _ => sg_sq (u i))

theorem eps_mul_posb {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (s : Fin n × Fin n → Bool) (b : Bool) (i j : Fin n) :
    eps s i j * posb H s b i j = sg b * Rb H s b i j := by
  unfold posb Rb
  split_ifs with h
  · exact h
  · simp

theorem eps_cases {n : ℕ} (s : Fin n × Fin n → Bool) (i j : Fin n) : eps s i j = 1 ∨ eps s i j = -1 := by
  unfold eps; split_ifs <;> simp

theorem sum_Rb {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (s : Fin n × Fin n → Bool) (i j : Fin n) :
    ∑ b : Bool, Rb H s b i j = H i j := by
  simp only [Fintype.sum_bool, Rb, sg]
  rcases eps_cases s i j with he | he <;> rw [he] <;>
    rcases lt_trichotomy (H i j) 0 with hh | hh | hh
  · rw [abs_of_neg hh]; simp only [mul_neg, neg_mul, one_mul, mul_one, neg_neg]; split_ifs <;> first | linarith | (intro h; linarith) | simp_all | (simp; linarith)
  · simp [hh]
  · rw [abs_of_pos hh]; simp only [mul_neg, neg_mul, one_mul, mul_one, neg_neg]; split_ifs <;> first | linarith | (intro h; linarith) | simp_all | (simp; linarith)
  · rw [abs_of_neg hh]; simp only [mul_neg, neg_mul, one_mul, mul_one, neg_neg]; split_ifs <;> first | linarith | (intro h; linarith) | simp_all | (simp; linarith)
  · simp [hh]
  · rw [abs_of_pos hh]; simp only [mul_neg, neg_mul, one_mul, mul_one, neg_neg]; split_ifs <;> first | linarith | (intro h; linarith) | simp_all | (simp; linarith)

theorem sum_posb_sq {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (s : Fin n × Fin n → Bool) (i j : Fin n) :
    ∑ b : Bool, (posb H s b i j) ^ 2 = (H i j) ^ 2 := by
  simp only [Fintype.sum_bool, posb, sg]
  rcases eps_cases s i j with he | he <;> rw [he] <;>
    rcases lt_trichotomy (H i j) 0 with hh | hh | hh
  · rw [abs_of_neg hh]; simp only [mul_neg, neg_mul, one_mul, mul_one, neg_neg]; split_ifs <;> first | nlinarith | (intro h; nlinarith) | simp_all | (simp; nlinarith)
  · simp [hh]
  · rw [abs_of_pos hh]; simp only [mul_neg, neg_mul, one_mul, mul_one, neg_neg]; split_ifs <;> first | nlinarith | (intro h; nlinarith) | simp_all | (simp; nlinarith)
  · rw [abs_of_neg hh]; simp only [mul_neg, neg_mul, one_mul, mul_one, neg_neg]; split_ifs <;> first | nlinarith | (intro h; nlinarith) | simp_all | (simp; nlinarith)
  · simp [hh]
  · rw [abs_of_pos hh]; simp only [mul_neg, neg_mul, one_mul, mul_one, neg_neg]; split_ifs <;> first | nlinarith | (intro h; nlinarith) | simp_all | (simp; nlinarith)

theorem det_T {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (s : Fin n × Fin n → Bool) (u : Fin n → Bool) :
    Matrix.det (fun i j => eps s i j * posb H s (u i) i j : Matrix (Fin n) (Fin n) ℝ) =
      (∏ i, sg (u i)) * Matrix.det (fun i j => Rb H s (u i) i j : Matrix (Fin n) (Fin n) ℝ) := by
  have : (fun i j => eps s i j * posb H s (u i) i j : Matrix (Fin n) (Fin n) ℝ) =
      Matrix.of (fun i j => sg (u i) * Rb H s (u i) i j) := by
    ext i j; simp [eps_mul_posb]
  rw [this]
  exact Matrix.det_mul_column (fun i => sg (u i)) (fun i j => Rb H s (u i) i j)

theorem part1 (n : ℕ) (H : Matrix (Fin n) (Fin n) ℝ) (s : Fin n × Fin n → Bool) :
    ∑ u : Fin n → Bool, (∏ i, sg (u i)) *
      Matrix.det (fun i j => eps s i j * posb H s (u i) i j : Matrix (Fin n) (Fin n) ℝ) = H.det := by
  simp_rw [det_T, ← mul_assoc, prod_sg_sq, one_mul]
  have hm := (Matrix.detRowAlternating : (Fin n → ℝ) [⋀^Fin n]→ₗ[ℝ] ℝ).toMultilinearMap.map_sum
    (fun (i : Fin n) (b : Bool) => (fun j => Rb H s b i j))
  have hH : (fun i => ∑ b : Bool, (fun j => Rb H s b i j)) = H := by
    funext i j; rw [Finset.sum_apply]; exact sum_Rb H s i j
  rw [hH] at hm
  exact hm.symm

theorem perm_sq_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.permanent (fun i j => (A i j) ^ 2 : Matrix (Fin n) (Fin n) ℝ) = ∑ σ : Equiv.Perm (Fin n), ∏ i, (A (σ i) i) ^ 2 := by
  rfl

theorem part2 (n : ℕ) (H : Matrix (Fin n) (Fin n) ℝ) (s : Fin n × Fin n → Bool) :
    ∑ u : Fin n → Bool, Matrix.permanent (fun i j => (posb H s (u i) i j) ^ 2 : Matrix (Fin n) (Fin n) ℝ) =
      Matrix.permanent (fun i j => (H i j) ^ 2 : Matrix (Fin n) (Fin n) ℝ) := by
  rw [perm_sq_eq H]
  simp_rw [perm_sq_eq (fun i j => posb H s _ i j)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  have e := Fintype.sum_equiv (Equiv.arrowCongr σ.symm (Equiv.refl Bool))
    (fun u : Fin n → Bool => ∏ i, (posb H s (u (σ i)) (σ i) i) ^ 2)
    (fun w : Fin n → Bool => ∏ i, (posb H s (w i) (σ i) i) ^ 2)
    (fun u => by simp [Equiv.arrowCongr_apply])
  rw [e, ← Fintype.prod_sum (fun i b => (posb H s b (σ i) i) ^ 2)]
  exact Finset.prod_congr rfl (fun i _ => sum_posb_sq H s (σ i) i)

theorem perm_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ Matrix.permanent (fun i j => (A i j) ^ 2 : Matrix (Fin n) (Fin n) ℝ) := by
  rw [perm_sq_eq]
  exact Finset.sum_nonneg (fun σ _ => Finset.prod_nonneg (fun i _ => sq_nonneg _))

theorem T_zero {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (s : Fin n × Fin n → Bool) (u : Fin n → Bool)
    (h : Matrix.permanent (fun i j => (posb H s (u i) i j) ^ 2 : Matrix (Fin n) (Fin n) ℝ) = 0) :
    Matrix.det (fun i j => eps s i j * posb H s (u i) i j : Matrix (Fin n) (Fin n) ℝ) = 0 := by
  unfold Matrix.permanent at h
  dsimp only at h
  erw [Matrix.det_apply]
  refine Finset.sum_eq_zero (fun σ _ => ?_)
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun σ _ => Finset.prod_nonneg (fun i _ => sq_nonneg _))).1 h σ
    (Finset.mem_univ σ)
  obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.1 h0
  have hz : posb H s (u (σ i)) (σ i) i = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 hi
  have : ∏ i, (fun i j => eps s i j * posb H s (u i) i j : Matrix (Fin n) (Fin n) ℝ) (σ i) i = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hz])
  rw [this, smul_zero]

theorem part3 (n : ℕ) (H : Matrix (Fin n) (Fin n) ℝ) (s : Fin n × Fin n → Bool)
    (hP : 0 < Matrix.permanent (fun i j => (H i j) ^ 2 : Matrix (Fin n) (Fin n) ℝ)) :
    ∃ u : Fin n → Bool, 0 < Matrix.permanent (fun i j => (posb H s (u i) i j) ^ 2 : Matrix (Fin n) (Fin n) ℝ) ∧
      H.det ^ 2 * Matrix.permanent (fun i j => (posb H s (u i) i j) ^ 2 : Matrix (Fin n) (Fin n) ℝ) ≤
        (2 : ℝ) ^ n * (Matrix.det (fun i j => eps s i j * posb H s (u i) i j : Matrix (Fin n) (Fin n) ℝ)) ^ 2 *
          Matrix.permanent (fun i j => (H i j) ^ 2 : Matrix (Fin n) (Fin n) ℝ) := by
  set PH := Matrix.permanent (fun i j => (H i j) ^ 2 : Matrix (Fin n) (Fin n) ℝ) with hPH
  set Pu := fun u : Fin n → Bool => Matrix.permanent (fun i j => (posb H s (u i) i j) ^ 2 : Matrix (Fin n) (Fin n) ℝ) with hPu
  set Tu := fun u : Fin n → Bool => Matrix.det (fun i j => eps s i j * posb H s (u i) i j : Matrix (Fin n) (Fin n) ℝ) with hTu
  have hsumP : ∑ u, Pu u = PH := part2 n H s
  have hcs : H.det ^ 2 ≤ (2 : ℝ) ^ n * ∑ u, (Tu u) ^ 2 := by
    rw [← part1 n H s]
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n → Bool)))
      (f := fun u => (∏ i, sg (u i)) * Tu u)
    have hc : ((Finset.univ : Finset (Fin n → Bool)).card : ℝ) = (2 : ℝ) ^ n := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]; push_cast; ring
    have hsq : ∀ u : Fin n → Bool, ((∏ i, sg (u i)) * Tu u) ^ 2 = (Tu u) ^ 2 := by
      intro u
      have := prod_sg_sq u
      nlinarith [this]
    simp only [hsq, hc] at h
    exact h
  by_contra hne
  push_neg at hne
  have hle : ∀ u ∈ (Finset.univ : Finset (Fin n → Bool)), (2 : ℝ) ^ n * (Tu u) ^ 2 * PH ≤ H.det ^ 2 * Pu u := by
    intro u _
    rcases (perm_nonneg (fun i j => posb H s (u i) i j)).lt_or_eq with hpos | hzero
    · exact le_of_lt (hne u hpos)
    · have hT : Tu u = 0 := T_zero H s u hzero.symm
      have hP0 : Pu u = 0 := hzero.symm
      rw [hT, hP0]; simp
  have hex : ∃ u ∈ (Finset.univ : Finset (Fin n → Bool)), (2 : ℝ) ^ n * (Tu u) ^ 2 * PH < H.det ^ 2 * Pu u := by
    by_contra hall
    push_neg at hall
    have hz : ∀ u, Pu u = 0 := by
      intro u
      rcases (perm_nonneg (fun i j => posb H s (u i) i j)).lt_or_eq with hpos | hzero
      · exact absurd (hne u hpos) (not_lt.2 (hall u (Finset.mem_univ u)))
      · exact hzero.symm
    have : PH = 0 := by rw [← hsumP]; simp [hz]
    linarith
  have hlt := Finset.sum_lt_sum hle hex
  rw [← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum, hsumP] at hlt
  have h2 : H.det ^ 2 * PH ≤ (2 : ℝ) ^ n * (∑ u, (Tu u) ^ 2) * PH :=
    mul_le_mul_of_nonneg_right hcs (le_of_lt hP)
  linarith

end PEqualNP.Outside.L_lib_703

theorem PEqualNP.Outside.L_lib_703 : ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℝ) (s : Fin n × Fin n → Bool),
  let I := Fin n
  let ε := fun i j => if s (i,j) then (-1 : ℝ) else 1
  let v := fun (u : I → Bool) i => if u i then (-1 : ℝ) else 1
  let pos := fun (u : I → Bool) (i j : I) =>
    if ε i j * |H i j| = v u i * H i j then |H i j| else 0
  let T := fun (u : I → Bool) => Matrix.det (fun i j => ε i j * pos u i j : Matrix I I ℝ)
  let P := fun A : Matrix I I ℝ => Matrix.permanent (fun i j => (A i j)^2)
  (∑ u : I → Bool, (∏ i : I, v u i) * T u) = H.det ∧
    (∑ u : I → Bool, P (pos u)) = P H ∧
    (0 < P H → ∃ u : I → Bool, 0 < P (pos u) ∧
      H.det^2 * P (pos u) ≤ (2 : ℝ)^n * (T u)^2 * P H) := by
  intro n H s
  exact ⟨PEqualNP.Outside.L_lib_703.part1 n H s, PEqualNP.Outside.L_lib_703.part2 n H s,
    PEqualNP.Outside.L_lib_703.part3 n H s⟩
