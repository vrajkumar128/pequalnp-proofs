import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_143

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma ofFn_three (x : Fin 3 → Bool) : List.ofFn x = [x 0, x 1, x 2] := by
  simp [List.ofFn_succ]

lemma getD_snoc (L : List Bool) (v : Bool) (n : ℕ) :
    (L ++ [v]).getD n false = if n = L.length then v else L.getD n false := by
  split_ifs with h
  · subst h
    simp
  · rcases Nat.lt_or_gt_of_ne h with h' | h'
    · rw [List.getD_append _ _ _ _ h']
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma base_indep (i : ℕ) (k : Fin 3) (h : i ≠ (k : ℕ)) (x y : Fin 3 → Bool)
    (hxy : ∀ j : Fin 3, j ≠ k → x j = y j) :
    (List.ofFn x).getD i false = (List.ofFn y).getD i false := by
  rw [ofFn_three, ofFn_three]
  rcases i with _ | _ | _ | i
  · simpa using hxy 0 (fun e => h (by rw [← e]; rfl))
  · simpa using hxy 1 (fun e => h (by rw [← e]; rfl))
  · simpa using hxy 2 (fun e => h (by rw [← e]; rfl))
  · simp

lemma gate_eq (op : GateOp) (l : List ℕ) (R S : ℕ → Bool) (h : ∀ i ∈ l, R i = S i) :
    op.eval (l.map R) = op.eval (l.map S) := by
  rw [List.map_congr_left h]

lemma not_take (l : List ℕ) (R : ℕ → Bool) :
    GateOp.not.eval (l.map R) = GateOp.not.eval ((l.take 1).map R) := by
  cases l <;> rfl

lemma not_cons (a : Bool) (l : List Bool) : GateOp.not.eval (a :: l) = !a := rfl

lemma exists_fresh (l : List ℕ) (hl : l.length ≤ 2) : ∃ k : Fin 3, (k : ℕ) ∉ l := by
  by_contra hne
  simp only [not_exists, not_not] at hne
  have h0 := hne 0
  have h1 := hne 1
  have h2 := hne 2
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · simp at h0
  · simp at h0 h1
    omega
  · simp at h0 h1 h2
    omega
  · simp only [List.length_cons] at hl
    omega

lemma flatMap_len (l : List ℕ) (F : ℕ → List ℕ) (hF : ∀ j, (F j).length ≤ 1) :
    (l.flatMap F).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have := hF a
    omega

lemma f_sens (k : Fin 3) : ∃ x y : Fin 3 → Bool, (∀ j : Fin 3, j ≠ k → x j = y j) ∧
    ((x 0 && x 1) || (x 1 && x 2)) ≠ ((y 0 && y 1) || (y 1 && y 2)) := by
  fin_cases k
  · exact ⟨![false, true, false], ![true, true, false], by decide, by decide⟩
  · exact ⟨![true, false, false], ![true, true, false], by decide, by decide⟩
  · exact ⟨![false, true, false], ![false, true, true], by decide, by decide⟩

lemma upper : FanInTwo ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [1, 3]⟩], 4⟩ ∧
    circuitFun 3 ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [1, 3]⟩], 4⟩ =
      (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 1 && x 2)) := by
  constructor
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> simp
  · funext x
    simp only [circuitFun, Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil,
      ofFn_three, GateOp.eval]
    cases x 0 <;> cases x 1 <;> cases x 2 <;> rfl

lemma eval_zero (out : ℕ) (x : Fin 3 → Bool) :
    Circuit.eval ⟨[], out⟩ (List.ofFn x) = (List.ofFn x).getD out false := by
  simp [Circuit.eval, Circuit.wires]

lemma eval_one (g1 : Gate) (out : ℕ) (x : Fin 3 → Bool) :
    Circuit.eval ⟨[g1], out⟩ (List.ofFn x) =
      if out = 3 then g1.op.eval (g1.inputs.map fun i => (List.ofFn x).getD i false)
      else (List.ofFn x).getD out false := by
  simp only [Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil, getD_snoc,
    List.length_ofFn]

lemma eval_two (g1 g2 : Gate) (out : ℕ) (x : Fin 3 → Bool) :
    Circuit.eval ⟨[g1, g2], out⟩ (List.ofFn x) =
      if out = 4 then
        g2.op.eval (g2.inputs.map fun i =>
          if i = 3 then g1.op.eval (g1.inputs.map fun i => (List.ofFn x).getD i false)
          else (List.ofFn x).getD i false)
      else if out = 3 then g1.op.eval (g1.inputs.map fun i => (List.ofFn x).getD i false)
      else (List.ofFn x).getD out false := by
  simp only [Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil, getD_snoc,
    List.length_append, List.length_ofFn, List.length_singleton]

lemma v1_eq (g1 : Gate) (k : Fin 3) (hk : ∀ i ∈ g1.inputs, i ≠ (k : ℕ)) (x y : Fin 3 → Bool)
    (hxy : ∀ j : Fin 3, j ≠ k → x j = y j) :
    g1.op.eval (g1.inputs.map fun i => (List.ofFn x).getD i false) =
      g1.op.eval (g1.inputs.map fun i => (List.ofFn y).getD i false) :=
  gate_eq _ _ _ _ (fun i hi => base_indep i k (hk i hi) x y hxy)

lemma v1_eq_not (g1 : Gate) (hop : g1.op = GateOp.not) (k : Fin 3)
    (hk : ∀ i ∈ g1.inputs.take 1, i ≠ (k : ℕ)) (x y : Fin 3 → Bool)
    (hxy : ∀ j : Fin 3, j ≠ k → x j = y j) :
    g1.op.eval (g1.inputs.map fun i => (List.ofFn x).getD i false) =
      g1.op.eval (g1.inputs.map fun i => (List.ofFn y).getD i false) := by
  rw [hop, not_take _ (fun i => (List.ofFn x).getD i false),
    not_take _ (fun i => (List.ofFn y).getD i false)]
  exact gate_eq _ _ _ _ (fun i hi => base_indep i k (hk i hi) x y hxy)

lemma main : ∀ C : Circuit, IsMinimalCircuit 3 C →
    circuitFun 3 C = (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 1 && x 2)) →
    C.size = 2 ∧ ∀ g ∈ C.gates, g.op ≠ GateOp.not := by
  intro C hmin hf
  have hle : C.size ≤ 2 := hmin.2 _ upper.1 (upper.2.trans hf.symm)
  have hfan := hmin.1
  have hsens : ∀ k : Fin 3, ∃ x y : Fin 3 → Bool, (∀ j : Fin 3, j ≠ k → x j = y j) ∧
      C.eval (List.ofFn x) ≠ C.eval (List.ofFn y) := by
    intro k
    obtain ⟨x, y, hxy, hne⟩ := f_sens k
    refine ⟨x, y, hxy, ?_⟩
    have hx := congrFun hf x
    have hy := congrFun hf y
    simp only [circuitFun] at hx hy
    rw [hx, hy]
    exact hne
  have hout : ∀ out : ℕ, ∃ k : Fin 3, out ≠ (k : ℕ) := by
    intro out
    obtain ⟨k, hk⟩ := exists_fresh [out] (by simp)
    exact ⟨k, fun e => hk (by simp [e])⟩
  obtain ⟨gates, out⟩ := C
  rcases gates with _ | ⟨g1, _ | ⟨g2, _ | ⟨g3, rest⟩⟩⟩
  · exfalso
    obtain ⟨k, hk⟩ := hout out
    obtain ⟨x, y, hxy, hne⟩ := hsens k
    apply hne
    rw [eval_zero, eval_zero]
    exact base_indep out k hk x y hxy
  · exfalso
    have hl1 := (hfan g1 (by simp)).2
    by_cases h3 : out = 3
    · obtain ⟨k, hk⟩ := exists_fresh g1.inputs hl1
      obtain ⟨x, y, hxy, hne⟩ := hsens k
      apply hne
      rw [eval_one, eval_one, ite_eq_left h3, ite_eq_left h3]
      exact v1_eq g1 k (fun i hi e => hk (e ▸ hi)) x y hxy
    · obtain ⟨k, hk⟩ := hout out
      obtain ⟨x, y, hxy, hne⟩ := hsens k
      apply hne
      rw [eval_one, eval_one, ite_eq_right h3, ite_eq_right h3]
      exact base_indep out k hk x y hxy
  · refine ⟨rfl, ?_⟩
    have hl1 := (hfan g1 (by simp)).2
    have hl2 := (hfan g2 (by simp)).2
    have h4 : out = 4 := by
      by_contra h4
      by_cases h3 : out = 3
      · obtain ⟨k, hk⟩ := exists_fresh g1.inputs hl1
        obtain ⟨x, y, hxy, hne⟩ := hsens k
        apply hne
        rw [eval_two, eval_two, ite_eq_right h4, ite_eq_right h4, ite_eq_left h3, ite_eq_left h3]
        exact v1_eq g1 k (fun i hi e => hk (e ▸ hi)) x y hxy
      · obtain ⟨k, hk⟩ := hout out
        obtain ⟨x, y, hxy, hne⟩ := hsens k
        apply hne
        rw [eval_two, eval_two, ite_eq_right h4, ite_eq_right h4, ite_eq_right h3, ite_eq_right h3]
        exact base_indep out k hk x y hxy
    subst h4
    have hn1 : g1.op ≠ GateOp.not := by
      intro hop
      set L := g2.inputs.flatMap (fun j => if j = 3 then g1.inputs.take 1 else [j]) with hL
      have hLlen : L.length ≤ 2 := by
        refine le_trans (flatMap_len _ _ ?_) hl2
        intro j
        split_ifs
        · simp
        · simp
      obtain ⟨k, hk⟩ := exists_fresh L hLlen
      obtain ⟨x, y, hxy, hne⟩ := hsens k
      apply hne
      rw [eval_two, eval_two, ite_eq_left rfl, ite_eq_left rfl]
      apply gate_eq
      intro j hj
      split_ifs with hj3
      · apply v1_eq_not g1 hop k _ x y hxy
        intro i hi e
        apply hk
        rw [hL, List.mem_flatMap]
        exact ⟨j, hj, by rw [ite_eq_left hj3]; exact e ▸ hi⟩
      · apply base_indep j k _ x y hxy
        intro e
        apply hk
        rw [hL, List.mem_flatMap]
        exact ⟨j, hj, by rw [ite_eq_right hj3]; simp [e]⟩
    have hn2 : g2.op ≠ GateOp.not := by
      intro hop
      rcases hg2 : g2.inputs with _ | ⟨j, rest⟩
      · obtain ⟨x, y, hxy, hne⟩ := hsens 0
        apply hne
        rw [eval_two, eval_two, ite_eq_left rfl, ite_eq_left rfl, hop, hg2]
        rfl
      · by_cases hj3 : j = 3
        · obtain ⟨k, hk⟩ := exists_fresh g1.inputs hl1
          obtain ⟨x, y, hxy, hne⟩ := hsens k
          apply hne
          rw [eval_two, eval_two, ite_eq_left rfl, ite_eq_left rfl, hop, hg2]
          subst hj3
          simp only [List.map_cons, not_cons, ↓reduceIte]
          rw [v1_eq g1 k (fun i hi e => hk (e ▸ hi)) x y hxy]
        · obtain ⟨k, hk⟩ := hout j
          obtain ⟨x, y, hxy, hne⟩ := hsens k
          apply hne
          rw [eval_two, eval_two, ite_eq_left rfl, ite_eq_left rfl, hop, hg2]
          simp only [List.map_cons, not_cons, hj3, ↓reduceIte]
          rw [base_indep _ k hk x y hxy]
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    exacts [hn1, hn2]
  · simp only [Circuit.size, List.length_cons] at hle
    omega

end PEqualNP.Outside.L_meta_143

theorem PEqualNP.Outside.L_meta_143 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.IsMinimalCircuit 3 C → PEqualNP.MetaComplexity.circuitFun 3 C = (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 1 && x 2)) → C.size = 2 ∧ ∀ g ∈ C.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not := by
  exact PEqualNP.Outside.L_meta_143.main
