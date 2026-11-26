import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19529

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def cm (n : ℕ) : Circuit :=
  ⟨[⟨GateOp.or, [0, n]⟩, ⟨GateOp.or, [n - 1, 2 * n - 1]⟩, ⟨GateOp.not, [2 * n + 1]⟩,
    ⟨GateOp.or, [2 * n, 2 * n + 2]⟩], 2 * n + 3⟩

theorem cm_fan (n : ℕ) : FanInTwo (cm n) := by
  intro g hg
  simp only [cm, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp

theorem cm_size (n : ℕ) : (cm n).size ≤ 4 := by
  simp [cm, Circuit.size]

theorem getD_snoc {α : Type} (l : List α) (a d : α) (j : ℕ) :
    (l ++ [a]).getD j d = if j < l.length then l.getD j d else if j = l.length then a else d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_append_right (by omega)]
    have : j - l.length ≠ 0 := by omega
    simp [this]

theorem getD_app_ofFn {n m : ℕ} (f : Fin n → Bool) (g : Fin m → Bool) (j : ℕ) :
    (List.ofFn f ++ List.ofFn g).getD j false =
      if h : j < n then f ⟨j, h⟩ else if h' : j - n < m then g ⟨j - n, h'⟩ else false := by
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h h'
  · rw [List.getElem?_append_left (by simpa using h)]; simp [h]
  · rw [List.getElem?_append_right (by simp; omega)]; simp [h']
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_ofFn, List.getElem?_ofFn]
    simp [h']

theorem cm_rep (n : ℕ) (hn : 3 ≤ n) :
    Represents (fun u v : Fin n => decide ((u : ℕ) = 0 ∨ (v : ℕ) = 0 ∨ ((u : ℕ) ≠ n - 1 ∧ (v : ℕ) ≠ n - 1)))
      (cm n) := by
  intro u v
  have hl : (oneEach u v).length = 2 * n := by simp [oneEach]; omega
  have e0 : (oneEach u v).getD 0 false = decide ((u : ℕ) = 0) := by
    rw [oneEach, getD_app_ofFn, dif_pos (by omega)]
    simp [Fin.ext_iff, eq_comm]
  have e1 : (oneEach u v).getD n false = decide ((v : ℕ) = 0) := by
    rw [oneEach, getD_app_ofFn, dif_neg (by omega), dif_pos (by omega)]
    simp [Fin.ext_iff, eq_comm]
  have e2 : (oneEach u v).getD (n - 1) false = decide ((u : ℕ) = n - 1) := by
    rw [oneEach, getD_app_ofFn, dif_pos (by omega)]
    simp [Fin.ext_iff, eq_comm]
  have e3 : (oneEach u v).getD (2 * n - 1) false = decide ((v : ℕ) = n - 1) := by
    rw [oneEach, getD_app_ofFn, dif_neg (by omega), dif_pos (by omega)]
    simp only [Fin.ext_iff, decide_eq_decide]
    omega
  simp only [Circuit.eval, Circuit.wires, cm, List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil,
    getD_snoc, List.length_append, List.length_singleton, hl]
  simp only [show 0 < 2 * n by omega, show n < 2 * n by omega, show n - 1 < 2 * n by omega,
    show 2 * n - 1 < 2 * n by omega, show ¬ (2 * n + 1 < 2 * n + 1) by omega,
    show 2 * n < 2 * n + 1 + 1 by omega, show 2 * n + 1 < 2 * n + 1 + 1 by omega,
    show ¬ (2 * n + 2 < 2 * n + 1 + 1) by omega, show 2 * n + 2 = 2 * n + 1 + 1 by omega,
    show ¬ (2 * n + 3 < 2 * n + 1 + 1 + 1) by omega, show 2 * n + 3 = 2 * n + 1 + 1 + 1 by omega,
    show 2 * n < 2 * n + 1 by omega, if_true, if_false, e0, e1, e2, e3]
  simp only [GateOp.eval, List.any_cons, List.any_nil, List.headD_cons, id, Bool.or_false]
  by_cases hu0 : (u : ℕ) = 0 <;> by_cases hv0 : (v : ℕ) = 0 <;>
    by_cases hu1 : (u : ℕ) = n - 1 <;> by_cases hv1 : (v : ℕ) = n - 1 <;> simp_all

end PEqualNP.Outside.L_meta_19529

theorem PEqualNP.Outside.L_meta_19529 : ∀ n : ℕ, 3 ≤ n → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 4 ∧ PEqualNP.Represents.Represents (fun u v : Fin n => decide ((u : ℕ) = 0 ∨ (v : ℕ) = 0 ∨ ((u : ℕ) ≠ n - 1 ∧ (v : ℕ) ≠ n - 1))) C :=
  fun n hn => ⟨PEqualNP.Outside.L_meta_19529.cm n, PEqualNP.Outside.L_meta_19529.cm_fan n,
    PEqualNP.Outside.L_meta_19529.cm_size n, PEqualNP.Outside.L_meta_19529.cm_rep n hn⟩
