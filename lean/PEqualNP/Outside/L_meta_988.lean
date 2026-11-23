import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_988

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

theorem fold_prefix (gs : List Gate) (w : List Bool) :
    ∃ t, gs.foldl step w = w ++ t := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨t, ht⟩ := ih (step w g)
    refine ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, ?_⟩
    rw [List.foldl_cons, ht]
    simp [step]

theorem val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

theorem val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    val (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => val gs x j)
      else val gs x i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [ite_eq_right (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [ite_eq_left h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [ite_eq_right (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem val_append {n : ℕ} (gs rest : List Gate) (x : Fin n → Bool) (i : ℕ)
    (hi : i < n + gs.length) : val (gs ++ rest) x i = val gs x i := by
  unfold val
  rw [List.foldl_append]
  obtain ⟨t, ht⟩ := fold_prefix rest (gs.foldl step (List.ofFn x))
  rw [ht]
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by omega)]

theorem val_ge {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ)
    (hi : n + gs.length ≤ i) : val gs x i = false := by
  unfold val
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none (by omega)]
  rfl

theorem val_input {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    val gs x i = x ⟨i, hi⟩ := by
  have h := val_append [] gs x i (by simp; omega)
  simp only [List.nil_append] at h
  rw [h, val_nil, dite_eq_left hi]

theorem val_gate {n : ℕ} (L : List Gate) (x : Fin n → Bool) (k : ℕ) (hk : k < L.length) :
    val L x (n + k) = L[k].op.eval
      (L[k].inputs.map fun j => if j < n + k then val L x j else false) := by
  have hsplit : L = (L.take k ++ [L[k]]) ++ L.drop (k + 1) := by
    rw [← List.take_succ_eq_append_getElem hk, List.take_append_drop]
  have htk : (L.take k).length = k := by simp; omega
  have h1 : val L x (n + k) = val (L.take k ++ [L[k]]) x (n + k) := by
    conv_lhs => rw [hsplit]
    rw [val_append _ _ _ _ (by simp; omega)]
  rw [h1, val_snoc, ite_eq_left (by rw [htk])]
  congr 1
  apply List.map_congr_left
  intro j _
  by_cases hj : j < n + k
  · rw [ite_eq_left hj]
    have h2 : val L x j = val (L.take k ++ L.drop k) x j := by rw [List.take_append_drop]
    rw [h2, val_append _ _ _ _ (by rw [htk]; exact hj)]
  · rw [ite_eq_right hj]
    exact val_ge _ _ _ (by rw [htk]; omega)

theorem eval_and (ins : List ℕ) (f : ℕ → Bool) :
    GateOp.and.eval (ins.map f) = true ↔ ∀ j ∈ ins, f j = true := by
  simp [GateOp.eval, List.all_eq_true]

theorem eval_or (ins : List ℕ) (f : ℕ → Bool) :
    GateOp.or.eval (ins.map f) = true ↔ ∃ j ∈ ins, f j = true := by
  simp [GateOp.eval, List.any_eq_true]

theorem val_mono {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x x' : Fin n → Bool) (hx : ∀ v, x v = true → x' v = true) :
    ∀ i, val gs x i = true → val gs x' i = true := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i hi
    rw [val_nil] at hi ⊢
    by_cases h : i < n
    · rw [dite_eq_left h] at hi ⊢
      exact hx _ hi
    · rw [dite_eq_right h] at hi
      exact absurd hi (by simp)
  | append_singleton gs g ih =>
    have ih' := ih (fun g' hg' => hg g' (by simp [hg']))
    intro i hi
    rw [val_snoc] at hi ⊢
    by_cases h : i = n + gs.length
    · rw [ite_eq_left h] at hi ⊢
      rcases hg g (by simp) with hop | hop
      · rw [hop, eval_and] at hi ⊢
        exact fun j hj => ih' j (hi j hj)
      · rw [hop, eval_or] at hi ⊢
        obtain ⟨j, hj, hv⟩ := hi
        exact ⟨j, hj, ih' j hv⟩
    · rw [ite_eq_right h] at hi ⊢
      exact ih' i hi

def xy {n : ℕ} (y : Finset (Fin n)) (p : Fin n) : Fin n → Bool :=
  fun v => decide (v ∈ y ∨ v = p)

def Below {n : ℕ} (L : List Gate) (S : Finset (Fin n)) (w : ℕ) : Prop :=
  ∀ x : Fin n → Bool, val L x w = true → ∃ p ∈ S, x p = true

def A {n : ℕ} (L : List Gate) (S y : Finset (Fin n)) (w : ℕ) : Finset (Fin n) :=
  S.filter fun p => val L (xy y p) w = true

def Serv {n : ℕ} (L : List Gate) (S y : Finset (Fin n)) (w : ℕ) : Prop :=
  Below L S w ∧ 2 ≤ (A L S y w).card

open Classical in
noncomputable def cnt {n : ℕ} (L : List Gate) (S y : Finset (Fin n)) (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun w => Serv L S y w).card

open Classical in
noncomputable def cntI {n : ℕ} (L : List Gate) (S y : Finset (Fin n)) : ℕ :=
  ((Finset.Ico n (n + L.length)).filter fun w => Serv L S y w).card

theorem input_A {n : ℕ} (L : List Gate) (S y : Finset (Fin n)) (hy : Disjoint y S)
    (w : ℕ) (hw : w < n) (hb : Below L S w) : (A L S y w).card ≤ 1 := by
  have hmem : (⟨w, hw⟩ : Fin n) ∈ S := by
    obtain ⟨q, hq, hx⟩ := hb (fun u => decide (u = ⟨w, hw⟩)) (by rw [val_input L _ w hw]; simp)
    simp only [decide_eq_true_eq] at hx
    rw [← hx]
    exact hq
  have hsub : A L S y w ⊆ {⟨w, hw⟩} := by
    intro p hp
    simp only [A, Finset.mem_filter] at hp
    rw [val_input L _ w hw] at hp
    simp only [xy, decide_eq_true_eq] at hp
    rcases hp.2 with h | h
    · exact absurd hmem (Finset.disjoint_left.mp hy h)
    · rw [Finset.mem_singleton, ← h]
  calc (A L S y w).card ≤ ({⟨w, hw⟩} : Finset (Fin n)).card := Finset.card_le_card hsub
    _ = 1 := Finset.card_singleton _

theorem beyond_A {n : ℕ} (L : List Gate) (S y : Finset (Fin n)) (w : ℕ)
    (hw : n + L.length ≤ w) : A L S y w = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro p hp
  simp only [A, Finset.mem_filter] at hp
  rw [val_ge L _ w hw] at hp
  exact absurd hp.2 (by simp)

theorem serv_range {n : ℕ} (L : List Gate) (S y : Finset (Fin n)) (hy : Disjoint y S)
    (w : ℕ) (hs : Serv L S y w) : n ≤ w ∧ w < n + L.length := by
  obtain ⟨hb, h2⟩ := hs
  constructor
  · by_contra h
    have := input_A L S y hy w (by omega) hb
    omega
  · by_contra h
    rw [beyond_A L S y w (by omega)] at h2
    simp at h2

open Classical in
theorem gate_children {n : ℕ} (L : List Gate) (S y : Finset (Fin n))
    (hg : ∀ g ∈ L, g.op = GateOp.and ∨ g.op = GateOp.or)
    (k : ℕ) (hk : k < L.length) (hb : Below L S (n + k)) :
    A L S y (n + k) ⊆ (L[k].inputs.toFinset.filter fun j => j < n + k ∧ Below L S j).biUnion
      (A L S y) := by
  classical
  intro p hp
  simp only [A, Finset.mem_filter] at hp
  obtain ⟨hpS, hpv⟩ := hp
  rw [val_gate L _ k hk] at hpv
  rcases hg L[k] (List.getElem_mem hk) with hop | hop
  · rw [hop, eval_and] at hpv
    by_cases hex : ∃ j ∈ L[k].inputs, Below L S j
    · obtain ⟨j, hj, hjb⟩ := hex
      have hv := hpv j hj
      by_cases hjN : j < n + k
      · rw [ite_eq_left hjN] at hv
        rw [Finset.mem_biUnion]
        refine ⟨j, ?_, ?_⟩
        · simp only [Finset.mem_filter, List.mem_toFinset]
          exact ⟨hj, hjN, hjb⟩
        · simp only [A, Finset.mem_filter]
          exact ⟨hpS, hv⟩
      · rw [ite_eq_right hjN] at hv
        exact absurd hv (by simp)
    · exfalso
      simp only [not_exists, not_and, Below, not_forall] at hex
      choose! f hf1 hf2 using hex
      let X : Fin n → Bool := fun v => L[k].inputs.any fun j => f j v
      have hX : ∀ j ∈ L[k].inputs, val L X j = true := by
        intro j hj
        refine val_mono L hg (f j) X ?_ j (hf1 j hj)
        intro v hv
        simp only [X, List.any_eq_true]
        exact ⟨j, hj, hv⟩
      have hXN : val L X (n + k) = true := by
        rw [val_gate L _ k hk, hop, eval_and]
        intro j hj
        have hv := hpv j hj
        by_cases hjN : j < n + k
        · rw [ite_eq_left hjN]
          exact hX j hj
        · rw [ite_eq_right hjN] at hv
          exact absurd hv (by simp)
      obtain ⟨q, hq, hXq⟩ := hb X hXN
      simp only [X, List.any_eq_true] at hXq
      obtain ⟨j, hj, hfj⟩ := hXq
      have := hf2 j hj q hq
      rw [hfj] at this
      exact absurd this (by simp)
  · rw [hop, eval_or] at hpv
    obtain ⟨j, hj, hv⟩ := hpv
    by_cases hjN : j < n + k
    · rw [ite_eq_left hjN] at hv
      have hjb : Below L S j := by
        intro x hx
        apply hb x
        rw [val_gate L _ k hk, hop, eval_or]
        exact ⟨j, hj, by rw [ite_eq_left hjN]; exact hx⟩
      rw [Finset.mem_biUnion]
      refine ⟨j, ?_, ?_⟩
      · simp only [Finset.mem_filter, List.mem_toFinset]
        exact ⟨hj, hjN, hjb⟩
      · simp only [A, Finset.mem_filter]
        exact ⟨hpS, hv⟩
    · rw [ite_eq_right hjN] at hv
      exact absurd hv (by simp)

theorem cnt_le_succ {n : ℕ} (L : List Gate) (S y : Finset (Fin n)) (N : ℕ) :
    cnt L S y N ≤ cnt L S y (N + 1) := by
  classical
  unfold cnt
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  exact Finset.range_subset_range.mpr (by omega)

open Classical in
theorem cnt_succ {n : ℕ} (L : List Gate) (S y : Finset (Fin n)) (N : ℕ)
    (hN : Serv L S y N) : cnt L S y N + 1 ≤ cnt L S y (N + 1) := by
  classical
  unfold cnt
  rw [← Finset.card_insert_of_notMem (s := (Finset.range N).filter fun w => Serv L S y w)
    (a := N) (by simp)]
  apply Finset.card_le_card
  intro w hw
  rw [Finset.mem_insert] at hw
  rw [Finset.mem_filter, Finset.mem_range]
  rcases hw with rfl | hw
  · exact ⟨by omega, hN⟩
  · rw [Finset.mem_filter, Finset.mem_range] at hw
    exact ⟨by omega, hw.2⟩

theorem claim {n : ℕ} (L : List Gate) (S y : Finset (Fin n)) (hy : Disjoint y S)
    (hg : ∀ g ∈ L, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ (N : ℕ) (W : Finset ℕ), (∀ w ∈ W, w < N ∧ Below L S w) →
      (W.biUnion (A L S y)).card ≤ W.card + cnt L S y N := by
  classical
  intro N
  induction N with
  | zero =>
    intro W hW
    have : W = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro w hw
      have := (hW w hw).1
      omega
    subst this
    simp
  | succ N ih =>
    intro W hW
    by_cases hN : N ∈ W
    · have hb : Below L S N := (hW N hN).2
      have hW0 : ∀ w ∈ W.erase N, w < N ∧ Below L S w := by
        intro w hw
        rw [Finset.mem_erase] at hw
        have := hW w hw.2
        exact ⟨by omega, this.2⟩
      have hcard0 := Finset.card_erase_add_one hN
      by_cases hA : (A L S y N).card ≤ 1
      · have hsub : W.biUnion (A L S y) ⊆ (W.erase N).biUnion (A L S y) ∪ A L S y N := by
          intro p hp
          rw [Finset.mem_biUnion] at hp
          obtain ⟨w, hw, hpw⟩ := hp
          by_cases hwN : w = N
          · subst hwN
            exact Finset.mem_union_right _ hpw
          · exact Finset.mem_union_left _
              (Finset.mem_biUnion.mpr ⟨w, Finset.mem_erase.mpr ⟨hwN, hw⟩, hpw⟩)
        have h1 := Finset.card_le_card hsub
        have h2 := Finset.card_union_le ((W.erase N).biUnion (A L S y)) (A L S y N)
        have h3 := ih (W.erase N) hW0
        have h4 := cnt_le_succ L S y N
        omega
      · have hs : Serv L S y N := ⟨hb, by omega⟩
        obtain ⟨hn1, hn2⟩ := serv_range L S y hy N hs
        obtain ⟨k, rfl⟩ : ∃ k, N = n + k := ⟨N - n, by omega⟩
        have hk : k < L.length := by omega
        set Ch := L[k].inputs.toFinset.filter fun j => j < n + k ∧ Below L S j with hCh
        have hch := gate_children L S y (fun g hg' => (hg g hg').1) k hk hb
        have hChcard : Ch.card ≤ 2 := by
          calc Ch.card ≤ L[k].inputs.toFinset.card := Finset.card_filter_le _ _
            _ ≤ L[k].inputs.length := List.toFinset_card_le _
            _ ≤ 2 := (hg L[k] (List.getElem_mem hk)).2
        have hW' : ∀ w ∈ W.erase (n + k) ∪ Ch, w < n + k ∧ Below L S w := by
          intro w hw
          rw [Finset.mem_union] at hw
          rcases hw with hw | hw
          · exact hW0 w hw
          · rw [hCh, Finset.mem_filter] at hw
            exact hw.2
        have hsub : W.biUnion (A L S y) ⊆ (W.erase (n + k) ∪ Ch).biUnion (A L S y) := by
          intro p hp
          rw [Finset.mem_biUnion] at hp
          obtain ⟨w, hw, hpw⟩ := hp
          by_cases hwN : w = n + k
          · subst hwN
            have := hch hpw
            rw [Finset.mem_biUnion] at this ⊢
            obtain ⟨j, hj, hpj⟩ := this
            exact ⟨j, Finset.mem_union_right _ hj, hpj⟩
          · exact Finset.mem_biUnion.mpr
              ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwN, hw⟩), hpw⟩
        have h1 := Finset.card_le_card hsub
        have h2 := Finset.card_union_le (W.erase (n + k)) Ch
        have h3 := ih _ hW'
        have h4 := cnt_succ L S y (n + k) hs
        omega
    · have hW' : ∀ w ∈ W, w < N ∧ Below L S w := by
        intro w hw
        have := hW w hw
        have hne : w ≠ N := fun h => hN (h ▸ hw)
        exact ⟨by omega, this.2⟩
      have h1 := ih W hW'
      have h2 := cnt_le_succ L S y N
      omega

theorem per_set {n : ℕ} (L : List Gate) (S y : Finset (Fin n)) (hy : Disjoint y S)
    (hg : ∀ g ∈ L, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (o : ℕ) (hbelow : Below L S o) (hfire : ∀ p ∈ S, val L (xy y p) o = true) :
    S.card ≤ 1 + cntI L S y := by
  classical
  have h := claim L S y hy hg (o + 1) {o} (by
    intro w hw
    rw [Finset.mem_singleton] at hw
    subst hw
    exact ⟨by omega, hbelow⟩)
  have hAo : A L S y o = S := by
    apply Finset.filter_true_of_mem
    exact hfire
  rw [Finset.singleton_biUnion, hAo, Finset.card_singleton] at h
  have hc : cnt L S y (o + 1) ≤ cntI L S y := by
    unfold cnt cntI
    apply Finset.card_le_card
    intro w hw
    rw [Finset.mem_filter] at hw ⊢
    refine ⟨?_, hw.2⟩
    rw [Finset.mem_Ico]
    exact serv_range L S y hy w hw.2
  omega

theorem pair {n : ℕ} (L : List Gate) (S1 S2 y1 : Finset (Fin n)) (w : ℕ)
    (hSS : (S1 ∩ S2).card ≤ 1) (h1 : 2 ≤ (A L S1 y1 w).card) (h2 : Below L S2 w) :
    ¬ Disjoint y1 S2 := by
  intro hd
  obtain ⟨p1, hp1, p2, hp2, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < (A L S1 y1 w).card)
  have key : ∀ p ∈ A L S1 y1 w, p ∈ S1 ∩ S2 := by
    intro p hp
    simp only [A, Finset.mem_filter] at hp
    obtain ⟨q, hq, hxq⟩ := h2 _ hp.2
    simp only [xy, decide_eq_true_eq] at hxq
    rcases hxq with h | h
    · exact absurd hq (Finset.disjoint_left.mp hd h)
    · rw [h] at hq
      exact Finset.mem_inter.mpr ⟨hp.1, hq⟩
  have hsub : ({p1, p2} : Finset (Fin n)) ⊆ S1 ∩ S2 := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact key _ hp1
    · exact key _ hp2
  have := Finset.card_le_card hsub
  rw [Finset.card_pair hne] at this
  omega

theorem main : ∀ (n m D : ℕ) (S y : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, Disjoint (y i) (S i)) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (i : Fin m) (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (o i) false = true → ∃ p ∈ S i, x p = true) → (∀ i : Fin m, ∀ p ∈ S i, (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y i ∨ v = p)))).getD (o i) false = true) → (∀ J : Finset (Fin m), (∀ i ∈ J, ∀ j ∈ J, i ≠ j → ¬ Disjoint (y i) (S j)) → J.card ≤ D) → ∑ i : Fin m, (S i).card ≤ D * C.gates.length + m := by
  classical
  intro n m D S y C o hSS hy hg hbelow hfire hD
  have hper : ∀ i, (S i).card ≤ 1 + cntI C.gates (S i) (y i) := fun i =>
    per_set C.gates (S i) (y i) (hy i) hg (o i) (hbelow i) (hfire i)
  have hJ : ∀ w, (Finset.univ.filter fun i => Serv C.gates (S i) (y i) w).card ≤ D := by
    intro w
    apply hD
    intro i hi j hj hij
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    exact pair C.gates (S i) (S j) (y i) w (hSS i j hij) hi.2 hj.1
  calc ∑ i, (S i).card ≤ ∑ i, (1 + cntI C.gates (S i) (y i)) :=
        Finset.sum_le_sum fun i _ => hper i
    _ = m + ∑ i, cntI C.gates (S i) (y i) := by simp [Finset.sum_add_distrib]
    _ = m + ∑ w ∈ Finset.Ico n (n + C.gates.length),
          (Finset.univ.filter fun i => Serv C.gates (S i) (y i) w).card := by
        congr 1
        unfold cntI
        simp only [Finset.card_filter]
        exact Finset.sum_comm
    _ ≤ m + ∑ w ∈ Finset.Ico n (n + C.gates.length), D := by
        gcongr with w
        exact hJ w
    _ = D * C.gates.length + m := by
        simp
        ring

end PEqualNP.Outside.L_meta_988

theorem PEqualNP.Outside.L_meta_988 : ∀ (n m D : ℕ) (S y : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, Disjoint (y i) (S i)) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (i : Fin m) (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (o i) false = true → ∃ p ∈ S i, x p = true) → (∀ i : Fin m, ∀ p ∈ S i, (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y i ∨ v = p)))).getD (o i) false = true) → (∀ J : Finset (Fin m), (∀ i ∈ J, ∀ j ∈ J, i ≠ j → ¬ Disjoint (y i) (S j)) → J.card ≤ D) → ∑ i : Fin m, (S i).card ≤ D * C.gates.length + m := by
  exact PEqualNP.Outside.L_meta_988.main
