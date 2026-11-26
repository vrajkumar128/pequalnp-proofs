import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20619

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def dstep (d : List (Finset ℕ)) (g : Gate) : List (Finset ℕ) :=
  d ++ [g.inputs.foldr (fun i acc => d.getD i ∅ ∪ acc) ∅]

def deps (C : Circuit) (N : ℕ) : List (Finset ℕ) :=
  C.gates.foldl dstep ((List.range N).map fun i => {i})

theorem getD_snoc {α : Type} (l : List α) (a d : α) (j : ℕ) :
    (l ++ [a]).getD j d = if j < l.length then l.getD j d else if j = l.length then a else d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_append_right (by omega)]
    have : j - l.length ≠ 0 := by omega
    simp [this]

theorem mem_fold (d : List (Finset ℕ)) (x : ℕ) : ∀ ins : List ℕ,
    x ∈ ins.foldr (fun i acc => d.getD i ∅ ∪ acc) ∅ ↔ ∃ i ∈ ins, x ∈ d.getD i ∅
  | [] => by simp
  | a :: t => by
    rw [List.foldr_cons, Finset.mem_union, mem_fold d x t]
    simp

theorem len_w (gs : List Gate) : ∀ w : List Bool, (gs.foldl wstep w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih => intro w; simp [List.foldl_cons, ih, wstep]; omega

theorem len_d (gs : List Gate) : ∀ d : List (Finset ℕ), (gs.foldl dstep d).length = d.length + gs.length := by
  induction gs with
  | nil => intro d; simp
  | cons g gs ih => intro d; simp [List.foldl_cons, ih, dstep]; omega

theorem loc (P : ℕ → Prop) : ∀ (gs : List Gate) (w1 w2 : List Bool) (d : List (Finset ℕ)),
    w1.length = d.length → w2.length = d.length →
    (∀ j, (∀ i ∈ d.getD j ∅, P i) → w1.getD j false = w2.getD j false) →
    ∀ j, (∀ i ∈ (gs.foldl dstep d).getD j ∅, P i) →
      (gs.foldl wstep w1).getD j false = (gs.foldl wstep w2).getD j false
  | [], w1, w2, d, _, _, h => h
  | g :: gs, w1, w2, d, h1, h2, h => by
    simp only [List.foldl_cons]
    apply loc P gs
    · simp [wstep, dstep, h1]
    · simp [wstep, dstep, h2]
    · intro j hj
      simp only [wstep, dstep, getD_snoc] at hj ⊢
      rw [h1, h2]
      split_ifs at hj ⊢ with ha hb
      · exact h j hj
      · have hU : ∀ i ∈ g.inputs, ∀ x ∈ d.getD i ∅, P x := by
          intro i hi x hx
          exact hj x ((mem_fold d x g.inputs).2 ⟨i, hi, hx⟩)
        have : (g.inputs.map fun i => w1.getD i false) = (g.inputs.map fun i => w2.getD i false) := by
          apply List.map_congr_left
          intro i hi
          exact h i (hU i hi)
        rw [this]
      · rfl

theorem gate_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (f1 f2 : ℕ → Bool) (hf : ∀ i, f1 i = true → f2 i = true) :
    op.eval (ins.map f1) = true → op.eval (ins.map f2) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    intro h i hi; exact hf i (h i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    rintro ⟨i, hi, h⟩; exact ⟨i, hi, hf i h⟩

theorem mono_fold : ∀ (gs : List Gate), (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    ∀ (w1 w2 : List Bool), w1.length = w2.length → (∀ j, w1.getD j false = true → w2.getD j false = true) →
    ∀ j, (gs.foldl wstep w1).getD j false = true → (gs.foldl wstep w2).getD j false = true
  | [], _, w1, w2, _, h => h
  | g :: gs, hg, w1, w2, hl, h => by
    simp only [List.foldl_cons]
    apply mono_fold gs (fun g' hg' => hg g' (List.mem_cons_of_mem g hg'))
    · simp [wstep, hl]
    · intro j hj
      simp only [wstep, getD_snoc] at hj ⊢
      rw [← hl]
      split_ifs at hj ⊢ with ha hb
      · exact h j hj
      · exact gate_mono g.op (hg g List.mem_cons_self) g.inputs _ _ (fun i => h i) hj

theorem relabel_card (S : Finset ℕ) (a b : ℕ) :
    S.card ≤ (S.image fun l => if l = b then a else l).card + 1 := by
  have h1 : ((S.erase b).image fun l => if l = b then a else l) ⊆ S.image fun l => if l = b then a else l :=
    Finset.image_subset_image (Finset.erase_subset b S)
  have h2 : ((S.erase b).image fun l => if l = b then a else l).card = (S.erase b).card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    have hx' : x ≠ b := (Finset.mem_erase.1 hx).1
    have hy' : y ≠ b := (Finset.mem_erase.1 hy).1
    simp only [hx', hy', if_false] at hxy
    exact hxy
  have h3 := Finset.card_le_card h1
  have h4 : S.card ≤ (S.erase b).card + 1 := by
    by_cases hb : b ∈ S
    · rw [Finset.card_erase_add_one hb]
    · rw [Finset.erase_eq_self.2 hb]; omega
  omega

theorem snoc_inv (N : ℕ) (d : List (Finset ℕ)) (lab lab1 : ℕ → ℕ) (U : Finset ℕ)
    (h1 : ∀ j, d.getD j ∅ ⊆ Finset.range N)
    (h2 : ∀ j, ∀ i ∈ d.getD j ∅, ∀ i' ∈ d.getD j ∅, lab i = lab i')
    (hr : ∀ i i', lab i = lab i' → lab1 i = lab1 i')
    (hU1 : U ⊆ Finset.range N) (hU2 : ∀ i ∈ U, ∀ i' ∈ U, lab1 i = lab1 i') :
    (∀ j, (d ++ [U]).getD j ∅ ⊆ Finset.range N) ∧
      (∀ j, ∀ i ∈ (d ++ [U]).getD j ∅, ∀ i' ∈ (d ++ [U]).getD j ∅, lab1 i = lab1 i') := by
  constructor
  · intro j
    rw [getD_snoc]
    split_ifs
    · exact h1 j
    · exact hU1
    · exact Finset.empty_subset _
  · intro j
    rw [getD_snoc]
    split_ifs
    · intro i hi i' hi'; exact hr i i' (h2 j i hi i' hi')
    · exact hU2
    · intro i hi; simp at hi

theorem step_blk (N : ℕ) (g : Gate) (hg : g.inputs.length ≤ 2) (d : List (Finset ℕ)) (lab : ℕ → ℕ) (k : ℕ)
    (h1 : ∀ j, d.getD j ∅ ⊆ Finset.range N)
    (h2 : ∀ j, ∀ i ∈ d.getD j ∅, ∀ i' ∈ d.getD j ∅, lab i = lab i')
    (h3 : N ≤ ((Finset.range N).image lab).card + k) :
    ∃ lab1 : ℕ → ℕ, (∀ j, (dstep d g).getD j ∅ ⊆ Finset.range N) ∧
      (∀ j, ∀ i ∈ (dstep d g).getD j ∅, ∀ i' ∈ (dstep d g).getD j ∅, lab1 i = lab1 i') ∧
      N ≤ ((Finset.range N).image lab1).card + (k + 1) := by
  have hU1 : g.inputs.foldr (fun i acc => d.getD i ∅ ∪ acc) ∅ ⊆ Finset.range N := by
    intro x hx
    obtain ⟨i, -, hx⟩ := (mem_fold d x g.inputs).1 hx
    exact h1 i hx
  rw [dstep]
  generalize g.inputs = ins at hU1 hg ⊢
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · obtain ⟨hA, hB⟩ := snoc_inv N d lab lab (List.foldr (fun i acc => d.getD i ∅ ∪ acc) ∅ []) h1 h2
      (fun i i' h => h) hU1 (by simp)
    exact ⟨lab, hA, hB, by omega⟩
  · obtain ⟨hA, hB⟩ := snoc_inv N d lab lab (List.foldr (fun i acc => d.getD i ∅ ∪ acc) ∅ [a]) h1 h2
      (fun i i' h => h) hU1 (by
        intro i hi i' hi'
        simp only [List.foldr_cons, List.foldr_nil, Finset.union_empty] at hi hi'
        exact h2 a i hi i' hi')
    exact ⟨lab, hA, hB, by omega⟩
  · rcases (d.getD a ∅).eq_empty_or_nonempty with ha | ⟨ia, hia⟩
    · obtain ⟨hA, hB⟩ := snoc_inv N d lab lab (List.foldr (fun i acc => d.getD i ∅ ∪ acc) ∅ [a, b]) h1 h2
        (fun i i' h => h) hU1 (by
          intro i hi i' hi'
          simp only [List.foldr_cons, List.foldr_nil, Finset.union_empty, ha, Finset.empty_union] at hi hi'
          exact h2 b i hi i' hi')
      exact ⟨lab, hA, hB, by omega⟩
    rcases (d.getD b ∅).eq_empty_or_nonempty with hb | ⟨ib, hib⟩
    · obtain ⟨hA, hB⟩ := snoc_inv N d lab lab (List.foldr (fun i acc => d.getD i ∅ ∪ acc) ∅ [a, b]) h1 h2
        (fun i i' h => h) hU1 (by
          intro i hi i' hi'
          simp only [List.foldr_cons, List.foldr_nil, Finset.union_empty, hb] at hi hi'
          exact h2 a i hi i' hi')
      exact ⟨lab, hA, hB, by omega⟩
    have key : ∀ i ∈ List.foldr (fun i acc => d.getD i ∅ ∪ acc) ∅ [a, b],
        (if lab i = lab ib then lab ia else lab i) = lab ia := by
      intro i hi
      simp only [List.foldr_cons, List.foldr_nil, Finset.union_empty, Finset.mem_union] at hi
      rcases hi with hi | hi
      · have := h2 a i hi ia hia
        split_ifs with h
        · rfl
        · exact this
      · have := h2 b i hi ib hib
        simp [this]
    obtain ⟨hA, hB⟩ := snoc_inv N d lab (fun i => if lab i = lab ib then lab ia else lab i)
      (List.foldr (fun i acc => d.getD i ∅ ∪ acc) ∅ [a, b]) h1 h2
      (by intro i i' h; simp only [h]) hU1 (by
        intro i hi i' hi'
        rw [key i hi, key i' hi'])
    refine ⟨_, hA, hB, ?_⟩
    have himg : ((Finset.range N).image fun i => if lab i = lab ib then lab ia else lab i) =
        ((Finset.range N).image lab).image fun l => if l = lab ib then lab ia else l := by
      rw [Finset.image_image]; rfl
    rw [himg]
    have := relabel_card ((Finset.range N).image lab) (lab ia) (lab ib)
    omega
  · simp at hg

theorem blk (N : ℕ) : ∀ (gs : List Gate), (∀ g ∈ gs, g.inputs.length ≤ 2) →
    ∀ (d : List (Finset ℕ)) (lab : ℕ → ℕ) (k : ℕ),
    (∀ j, d.getD j ∅ ⊆ Finset.range N) →
    (∀ j, ∀ i ∈ d.getD j ∅, ∀ i' ∈ d.getD j ∅, lab i = lab i') →
    N ≤ ((Finset.range N).image lab).card + k →
    ∃ lab' : ℕ → ℕ, (∀ j, (gs.foldl dstep d).getD j ∅ ⊆ Finset.range N) ∧
      (∀ j, ∀ i ∈ (gs.foldl dstep d).getD j ∅, ∀ i' ∈ (gs.foldl dstep d).getD j ∅, lab' i = lab' i') ∧
      N ≤ ((Finset.range N).image lab').card + (k + gs.length)
  | [], _, d, lab, k, h1, h2, h3 => ⟨lab, h1, h2, by simpa using h3⟩
  | g :: gs, hg, d, lab, k, h1, h2, h3 => by
    obtain ⟨lab1, h1', h2', h3'⟩ := step_blk N g (hg g List.mem_cons_self) d lab k h1 h2 h3
    obtain ⟨lab', a, b, c⟩ := blk N gs (fun g' hg' => hg g' (List.mem_cons_of_mem g hg')) (dstep d g) lab1 (k + 1) h1' h2' h3'
    refine ⟨lab', a, b, ?_⟩
    simp only [List.length_cons]
    omega

theorem count (N s ℓ : ℕ) (lab : ℕ → ℕ) (D : Finset ℕ) (hD : D ⊆ Finset.range N) (hl : ∀ i ∈ D, lab i = ℓ)
    (hc : N ≤ ((Finset.range N).image lab).card + s) : D.card ≤ s + 1 := by
  set B := (Finset.range N).filter fun i => lab i = ℓ
  have hDB : D ⊆ B := by
    intro i hi; exact Finset.mem_filter.2 ⟨hD hi, hl i hi⟩
  have hB : B ⊆ Finset.range N := Finset.filter_subset _ _
  have h1 : (Finset.range N \ B).card + B.card = N := by
    rw [Finset.card_sdiff_add_card_eq_card hB, Finset.card_range]
  have h2 : (Finset.range N).image lab ⊆ insert ℓ ((Finset.range N \ B).image lab) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
    by_cases h : lab i = ℓ
    · rw [h]; exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      exact Finset.mem_image.2 ⟨i, Finset.mem_sdiff.2 ⟨hi, fun hb => h (Finset.mem_filter.1 hb).2⟩, rfl⟩
  have h3 := Finset.card_le_card h2
  have h4 := Finset.card_insert_le ℓ ((Finset.range N \ B).image lab)
  have h5 := Finset.card_image_le (s := Finset.range N \ B) (f := lab)
  have h6 := Finset.card_le_card hDB
  omega

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

theorem d0_getD (N j : ℕ) : ((List.range N).map fun i => ({i} : Finset ℕ)).getD j ∅ = if j < N then {j} else ∅ := by
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · simp [h]
  · rw [List.getElem?_eq_none (by simp; omega)]; rfl

theorem eval_eq (C : Circuit) (x : List Bool) : C.eval x = (C.gates.foldl wstep x).getD C.output false := rfl

theorem dep_card {N : ℕ} (C : Circuit) (hC : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    ((deps C N).getD C.output ∅).card ≤ C.size + 1 := by
  obtain ⟨lab, h1, h2, h3⟩ := blk N C.gates hC ((List.range N).map fun i => ({i} : Finset ℕ)) id 0
    (by intro j; rw [d0_getD]; split_ifs with h <;> simp [h])
    (by intro j i hi i' hi'; rw [d0_getD] at hi hi'; split_ifs at hi hi' <;> simp_all)
    (by simp)
  rcases ((deps C N).getD C.output ∅).eq_empty_or_nonempty with he | ⟨i0, hi0⟩
  · rw [he]; simp
  · exact count N C.gates.length (lab i0) lab _ (h1 C.output) (fun i hi => h2 C.output i hi i0 hi0)
      (by simpa using h3)

theorem mono_ops (C : Circuit) (hC : Monotone2 C) : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
  intro g hg
  have := (hC g hg).1
  simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this

theorem ess_mem {n m : ℕ} (A : Fin n → Fin m → Bool) (C : Circuit) (hC : Monotone2 C) (hr : Represents A C)
    (i : ℕ) (x1 z x2 : List Bool) (hl1 : x1.length = n + m) (hlz : z.length = n + m) (hl2 : x2.length = n + m)
    (hagree : ∀ j, j ≠ i → x1.getD j false = z.getD j false)
    (hle : ∀ j, z.getD j false = true → x2.getD j false = true)
    (h1 : C.eval x1 = true) (h2 : C.eval x2 = false) :
    i ∈ (deps C (n + m)).getD C.output ∅ := by
  by_contra hi
  have hloc := loc (fun j => j ≠ i) C.gates x1 z ((List.range (n + m)).map fun i => ({i} : Finset ℕ))
    (by simp [hl1]) (by simp [hlz])
    (by
      intro j hj
      rw [d0_getD] at hj
      split_ifs at hj with hjN
      · exact hagree j (hj j (Finset.mem_singleton_self j))
      · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)])
    C.output (by intro j hj hji; subst hji; exact hi hj)
  rw [eval_eq] at h1 h2
  have hz : (C.gates.foldl wstep z).getD C.output false = true := by rw [← hloc]; exact h1
  have := mono_fold C.gates (mono_ops C hC) z x2 (by rw [hlz, hl2]) hle C.output hz
  rw [h2] at this
  exact absurd this (by simp)

theorem floor_bound {n m : ℕ} (A : Fin n → Fin m → Bool) (C : Circuit) (hC : Monotone2 C) (hr : Represents A C)
    (E : Finset ℕ)
    (hE : ∀ i ∈ E, (∃ u u' : Fin n, ∃ v : Fin m, i = u.val ∧ A u v = true ∧ A u' v = false) ∨
      (∃ v v' : Fin m, ∃ u : Fin n, i = n + v.val ∧ A u v = true ∧ A u v' = false)) :
    E.card ≤ C.size + 1 := by
  have hsub : E ⊆ (deps C (n + m)).getD C.output ∅ := by
    intro i hi
    rcases hE i hi with ⟨u, u', v, rfl, ha, hb⟩ | ⟨v, v', u, rfl, ha, hb⟩
    · refine ess_mem A C hC hr u.val (oneEach u v)
        (List.ofFn (fun _ : Fin n => false) ++ List.ofFn (fun j : Fin m => decide (j = v))) (oneEach u' v)
        (by simp [oneEach]) (by simp) (by simp [oneEach]) ?_ ?_ (by rw [hr]; exact ha) (by rw [hr]; exact hb)
      · intro j hj
        rw [oneEach, getD_app_ofFn, getD_app_ofFn]
        split_ifs with h1 h2
        · have : (⟨j, h1⟩ : Fin n) ≠ u := fun e => hj (by rw [← e])
          simp [this]
        · rfl
        · rfl
      · intro j hj
        rw [oneEach, getD_app_ofFn]
        rw [getD_app_ofFn] at hj
        split_ifs at hj ⊢ with h1 h2 <;> simp_all
    · refine ess_mem A C hC hr (n + v.val) (oneEach u v)
        (List.ofFn (fun i : Fin n => decide (i = u)) ++ List.ofFn (fun _ : Fin m => false)) (oneEach u v')
        (by simp [oneEach]) (by simp) (by simp [oneEach]) ?_ ?_ (by rw [hr]; exact ha) (by rw [hr]; exact hb)
      · intro j hj
        rw [oneEach, getD_app_ofFn, getD_app_ofFn]
        split_ifs with h1 h2
        · rfl
        · have : (⟨j - n, h2⟩ : Fin m) ≠ v := fun e => hj (by
            have := congrArg Fin.val e; simp at this; omega)
          simp [this]
        · rfl
      · intro j hj
        rw [oneEach, getD_app_ofFn]
        rw [getD_app_ofFn] at hj
        split_ifs at hj ⊢ with h1 h2 <;> simp_all
  have hc := dep_card (N := n + m) C (fun g hg => (hC g hg).2)
  have := Finset.card_le_card hsub
  omega


def cm : Circuit := ⟨[⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [3, 6]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.and, [10, 14]⟩, ⟨GateOp.or, [11, 15]⟩], 16⟩

theorem cm_mono : Monotone2 cm := by
  intro g hg
  simp only [cm, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem cm_size : cm.size ≤ 7 := by decide

theorem cm_rep : Represents (fun u v : Fin 5 => (29426688 : ℕ).testBit (5 * u.val + v.val)) cm := by
  decide +kernel

def ess : Finset ℕ := {2, 3, 4, 5, 6, 7, 8, 9}

theorem ess_ok : ∀ i ∈ ess, (∃ u u' : Fin 5, ∃ v : Fin 5, i = u.val ∧ (fun u v : Fin 5 => (29426688 : ℕ).testBit (5 * u.val + v.val)) u v = true ∧ (fun u v : Fin 5 => (29426688 : ℕ).testBit (5 * u.val + v.val)) u' v = false) ∨
    (∃ v v' : Fin 5, ∃ u : Fin 5, i = 5 + v.val ∧ (fun u v : Fin 5 => (29426688 : ℕ).testBit (5 * u.val + v.val)) u v = true ∧ (fun u v : Fin 5 => (29426688 : ℕ).testBit (5 * u.val + v.val)) u v' = false) := by
  decide +kernel

theorem ess_card : ess.card = 8 := by decide

theorem lower : ¬ RepSizeAtMost (fun u v : Fin 5 => (29426688 : ℕ).testBit (5 * u.val + v.val)) 6 := by
  rintro ⟨C, hC, hs, hr⟩
  have := floor_bound (fun u v : Fin 5 => (29426688 : ℕ).testBit (5 * u.val + v.val)) C hC hr ess ess_ok
  rw [ess_card] at this
  omega

end PEqualNP.Outside.L_meta_20619

theorem PEqualNP.Outside.L_meta_20619 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (29426688 : ℕ).testBit (5 * u.val + v.val)) 7 ∧ ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (29426688 : ℕ).testBit (5 * u.val + v.val)) 6 :=
  ⟨⟨PEqualNP.Outside.L_meta_20619.cm, PEqualNP.Outside.L_meta_20619.cm_mono, PEqualNP.Outside.L_meta_20619.cm_size, PEqualNP.Outside.L_meta_20619.cm_rep⟩, PEqualNP.Outside.L_meta_20619.lower⟩
