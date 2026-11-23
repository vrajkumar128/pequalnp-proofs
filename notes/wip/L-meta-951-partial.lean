import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_951

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
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem gate_cases {X : Type} (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length ≤ 2) (f : X → ℕ → Bool) (z : X) :
    (∀ y, g.op.eval (g.inputs.map (f y)) = false) ∨
    ∃ a b, g.op.eval (g.inputs.map (f z)) = false →
      (f z a = false ∧ f z b = false ∧
        ∀ y, g.op.eval (g.inputs.map (f y)) = true → f y a = true ∨ f y b = true) := by
  obtain ⟨op, ins⟩ := g
  simp only at hop hlen ⊢
  match ins, hlen with
  | [], _ =>
    rcases hop with rfl | rfl
    · right
      exact ⟨0, 0, by simp [GateOp.eval]⟩
    · left
      simp [GateOp.eval]
  | [a], _ =>
    right
    refine ⟨a, a, ?_⟩
    rcases hop with rfl | rfl <;> simp [GateOp.eval]
  | [a, b], _ =>
    rcases hop with rfl | rfl
    · right
      by_cases h : f z a = false
      · refine ⟨a, a, ?_⟩
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          Bool.and_true, id_eq, Bool.and_eq_true]
        intro _
        exact ⟨h, h, fun y hy => Or.inl hy.1⟩
      · refine ⟨b, b, ?_⟩
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          Bool.and_true, id_eq, Bool.and_eq_true]
        intro hz
        have hb : f z b = false := by
          cases ha : f z a <;> cases hb : f z b <;> simp_all
        exact ⟨hb, hb, fun y hy => Or.inl hy.2⟩
    · right
      refine ⟨a, b, ?_⟩
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        Bool.or_false, id_eq, Bool.or_eq_true, Bool.or_eq_false_iff]
      intro hz
      exact ⟨hz.1, hz.2, fun y hy => hy⟩
  | _ :: _ :: _ :: _, h => simp at h

def Zof {n : ℕ} (S : Finset (Fin n)) : Fin n → Bool := fun c => decide (c ∉ S)

def eof {n : ℕ} (u : Fin n) : Fin n → Bool := fun c => decide (c = u)

def Inv {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) (l : Fin n → Fin n) : Prop :=
  ∀ i u v, val gs (Zof S) i = false → val gs (eof u) i = true → val gs (eof v) i = true →
    u ∈ S ∧ l u = l v

def Cnt {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) (i : ℕ) : Prop :=
  val gs (Zof S) i = false ∧
    ∃ u v : Fin n, u ≠ v ∧ val gs (eof u) i = true ∧ val gs (eof v) i = true

open Classical in
noncomputable def D {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) : Finset ℕ :=
  (Finset.Ico n (n + gs.length)).filter fun i => Cnt S gs i

theorem D_mono {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) (g : Gate) :
    D S gs ⊆ D S (gs ++ [g]) := by
  classical
  intro i hi
  simp only [D, Finset.mem_filter, Finset.mem_Ico, List.length_append, List.length_cons,
    List.length_nil] at hi ⊢
  refine ⟨⟨hi.1.1, by omega⟩, ?_⟩
  have hne : i ≠ n + gs.length := by omega
  obtain ⟨hz, u, v, huv, hu, hv⟩ := hi.2
  refine ⟨?_, u, v, huv, ?_, ?_⟩
  · rw [val_snoc, if_neg hne]; exact hz
  · rw [val_snoc, if_neg hne]; exact hu
  · rw [val_snoc, if_neg hne]; exact hv

theorem main_inv {n : ℕ} (S : Finset (Fin n)) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∃ l : Fin n → Fin n, Inv S gs l ∧ S.card ≤ (S.image l).card + (D S gs).card := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨id, ?_, by simp⟩
    intro i u v hz hu hv
    rw [val_nil] at hz hu hv
    by_cases h : i < n
    · simp only [h, dite_true, Zof, eof, decide_eq_false_iff_not, not_not,
        decide_eq_true_eq] at hz hu hv
      subst hu
      subst hv
      exact ⟨hz, rfl⟩
    · simp [h] at hu
  | append_singleton gs g ih =>
    obtain ⟨l, hinv, hcard⟩ := ih (fun g' hg' => hg g' (by simp [hg']))
    obtain ⟨hop, hlen⟩ := hg g (by simp)
    set N := n + gs.length with hN
    set P : (Fin n → Bool) → Bool := fun x => g.op.eval (g.inputs.map fun j => val gs x j)
      with hP
    have hnew : ∀ x : Fin n → Bool, val (gs ++ [g]) x N = P x := by
      intro x
      rw [val_snoc, if_pos hN]
    have hold : ∀ (x : Fin n → Bool) (i : ℕ), i ≠ N → val (gs ++ [g]) x i = val gs x i := by
      intro x i hi
      rw [val_snoc, if_neg hi]
    have key : P (Zof S) = false → ∀ u, P (eof u) = true →
        u ∈ S ∧ ∃ A B : Fin n → Prop, (∀ w, P (eof w) = true → A w ∨ B w) ∧
          (∀ w w', A w → A w' → l w = l w') ∧ (∀ w w', B w → B w' → l w = l w') := by
      intro hz u hu
      rcases gate_cases g hop hlen (fun x j => val gs x j) (Zof S) with hall | ⟨a, b, hab⟩
      · have := hall (eof u)
        simp only [hP] at hu
        rw [this] at hu
        exact absurd hu (by simp)
      · obtain ⟨ha, hb, hy⟩ := hab hz
        refine ⟨?_, fun w => val gs (eof w) a = true, fun w => val gs (eof w) b = true,
          fun w hw => hy (eof w) hw, fun w w' hw hw' => (hinv a w w' ha hw hw').2,
          fun w w' hw hw' => (hinv b w w' hb hw hw').2⟩
        rcases hy (eof u) hu with h | h
        · exact (hinv a u u ha h h).1
        · exact (hinv b u u hb h h).1
    by_cases hm : P (Zof S) = false ∧ ∃ u v, P (eof u) = true ∧ P (eof v) = true ∧ l u ≠ l v
    · obtain ⟨hz, u0, v0, hu0, hv0, hne⟩ := hm
      refine ⟨fun w => if l w = l v0 then l u0 else l w, ?_, ?_⟩
      · intro i u v hiz hiu hiv
        by_cases hi : i = N
        · subst hi
          rw [hnew] at hiz hiu hiv
          obtain ⟨huS, A, B, hAB, hA, hB⟩ := key hiz u hiu
          refine ⟨huS, ?_⟩
          have two : ∀ w, P (eof w) = true → l w = l u0 ∨ l w = l v0 := by
            intro w hw
            rcases hAB w hw with h | h <;> rcases hAB u0 hu0 with h0 | h0 <;>
              rcases hAB v0 hv0 with h1 | h1
            · exact Or.inl (hA w u0 h h0)
            · exact Or.inl (hA w u0 h h0)
            · exact Or.inr (hA w v0 h h1)
            · exact absurd (hB u0 v0 h0 h1) hne
            · exact absurd (hA u0 v0 h0 h1) hne
            · exact Or.inr (hB w v0 h h1)
            · exact Or.inl (hB w u0 h h0)
            · exact Or.inl (hB w u0 h h0)
          have red : ∀ w, P (eof w) = true → (if l w = l v0 then l u0 else l w) = l u0 := by
            intro w hw
            rcases two w hw with h | h
            · rw [h]; split_ifs <;> rfl
            · rw [if_pos h]
          show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
          rw [red u hiu, red v hiv]
        · rw [hold _ _ hi] at hiz hiu hiv
          obtain ⟨huS, hl⟩ := hinv i u v hiz hiu hiv
          refine ⟨huS, ?_⟩
          show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
          rw [hl]
      · have himg : S.image l ⊆
            insert (l v0) (S.image fun w => if l w = l v0 then l u0 else l w) := by
          intro y hy
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
          by_cases h : l w = l v0
          · rw [h]; exact Finset.mem_insert_self _ _
          · refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨w, hw, ?_⟩)
            rw [if_neg h]
        have h1 : (S.image l).card ≤
            (S.image fun w => if l w = l v0 then l u0 else l w).card + 1 :=
          (Finset.card_le_card himg).trans (Finset.card_insert_le _ _)
        have hNin : N ∈ D S (gs ++ [g]) := by
          simp only [D, Finset.mem_filter, Finset.mem_Ico, List.length_append,
            List.length_cons, List.length_nil]
          refine ⟨⟨by omega, by omega⟩, ?_, u0, v0, ?_, ?_, ?_⟩
          · rw [hnew]; exact hz
          · intro h; exact hne (by rw [h])
          · rw [hnew]; exact hu0
          · rw [hnew]; exact hv0
        have hNnot : N ∉ D S gs := by
          simp only [D, Finset.mem_filter, Finset.mem_Ico]
          intro h
          omega
        have h2 : (D S gs).card + 1 ≤ (D S (gs ++ [g])).card := by
          rw [← Finset.card_insert_of_notMem hNnot]
          apply Finset.card_le_card
          intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact hNin
          · exact D_mono S gs g hi
        omega
    · refine ⟨l, ?_, ?_⟩
      · intro i u v hiz hiu hiv
        by_cases hi : i = N
        · subst hi
          rw [hnew] at hiz hiu hiv
          obtain ⟨huS, -⟩ := key hiz u hiu
          refine ⟨huS, ?_⟩
          by_contra hne
          exact hm ⟨hiz, u, v, hiu, hiv, hne⟩
        · rw [hold _ _ hi] at hiz hiu hiv
          exact hinv i u v hiz hiu hiv
      · have := Finset.card_le_card (D_mono S gs g)
        omega


open Classical in
noncomputable def fixg (b : Bool) (g : Gate) : Gate :=
  if g.op = GateOp.not then ⟨if b then GateOp.and else GateOp.or, []⟩ else g

noncomputable def fix (b : Bool) (gs : List Gate) : List Gate := gs.map (fixg b)

theorem fix_append (b : Bool) (gs : List Gate) (g : Gate) :
    fix b (gs ++ [g]) = fix b gs ++ [fixg b g] := by
  simp [fix]

theorem fix_length (b : Bool) (gs : List Gate) : (fix b gs).length = gs.length := by
  simp [fix]

theorem fix_ok (b : Bool) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) :
    ∀ g ∈ fix b gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hgm
  simp only [fix, List.mem_map] at hgm
  obtain ⟨g0, hg0, rfl⟩ := hgm
  obtain ⟨hop, hlen⟩ := hg g0 hg0
  unfold fixg
  by_cases hn : g0.op = GateOp.not
  · rw [if_pos hn]
    cases b <;> simp
  · rw [if_neg hn]
    refine ⟨?_, hlen⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hn

theorem eval_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (f1 f2 : ℕ → Bool) (h : ∀ j, f1 j = true → f2 j = true) :
    g.op.eval (g.inputs.map f1) = true → g.op.eval (g.inputs.map f2) = true := by
  rcases hop with hop | hop
  · rw [hop]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂]
    intro ha j hj
    exact h j (ha j hj)
  · rw [hop]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq, exists_exists_and_eq_and]
    rintro ⟨j, hj, hv⟩
    exact ⟨j, hj, h j hv⟩

theorem val_le {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) (x : Fin n → Bool) :
    ∀ i, (val (fix false gs) x i = true → val gs x i = true) ∧
      (val gs x i = true → val (fix true gs) x i = true) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i
    simp [fix]
  | append_singleton gs g ih =>
    have ih' := ih (fun g' hg' => hg g' (by simp [hg']))
    obtain ⟨hop, -⟩ := hg g (by simp)
    intro i
    rw [fix_append, fix_append, val_snoc, val_snoc, val_snoc, fix_length, fix_length]
    by_cases hi : i = n + gs.length
    · rw [if_pos hi, if_pos hi, if_pos hi]
      by_cases hn : g.op = GateOp.not
      · simp [fixg, hn, GateOp.eval]
      · have hop' : g.op = GateOp.and ∨ g.op = GateOp.or := by
          rcases hop with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exact absurd h hn
        simp only [fixg, hn, if_false]
        exact ⟨eval_mono g hop' _ _ (fun j => (ih' j).1),
          eval_mono g hop' _ _ (fun j => (ih' j).2)⟩
    · rw [if_neg hi, if_neg hi, if_neg hi]
      exact ih' i

theorem mem_D_one {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) (l : Fin n → Fin n)
    (hinv : Inv S gs l) (i : ℕ) (hi : i ∈ D S gs) :
    (∀ u, val gs (eof u) i = true → u ∈ S) ∧
      ∃ u v : Fin n, u ≠ v ∧ val gs (eof u) i = true ∧ val gs (eof v) i = true := by
  simp only [D, Finset.mem_filter, Finset.mem_Ico] at hi
  obtain ⟨-, hz, huv⟩ := hi
  exact ⟨fun u hu => (hinv i u u hz hu hu).1, huv⟩

theorem D_range {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) (i : ℕ) (hi : i ∈ D S gs) :
    i ∈ Finset.Ico n (n + gs.length) := by
  classical
  simp only [D, Finset.mem_filter] at hi
  exact hi.1

theorem partial_bound (n m : ℕ) (S : Fin m → Finset (Fin n))
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gates : List Gate) (out : Fin m → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true)) :
    ∑ w, (if val (fix true gates) (Zof (S w)) (out w) = false then (S w).card - 1
      else ((S w).filter (fun u => val (fix false gates) (eof u) (out w) = true)).card - 1)
      ≤ gates.length := by
  classical
  have h0 := fix_ok false gates hg
  have h1 := fix_ok true gates hg
  have hle := fun (x : Fin n → Bool) i => val_le gates hg x i
  choose l0 hinv0 hcard0 using fun w => main_inv (S w) (fix false gates) h0
  choose l1 hinv1 hcard1 using fun w => main_inv (S w) (fix true gates) h1
  let DD : Fin m → Finset ℕ := fun w =>
    if val (fix true gates) (Zof (S w)) (out w) = false then D (S w) (fix true gates)
    else D (S w) (fix false gates)
  have hZ0 : ∀ w, val (fix false gates) (Zof (S w)) (out w) = false := by
    intro w
    cases h : val (fix false gates) (Zof (S w)) (out w)
    · rfl
    · have := (hle (Zof (S w)) (out w)).1 h
      rw [hev] at this
      simp [Zof] at this
  have hE1 : ∀ w, ∀ u ∈ S w, val (fix true gates) (eof u) (out w) = true := by
    intro w u hu
    apply (hle (eof u) (out w)).2
    rw [hev]
    simp only [decide_eq_true_eq]
    exact ⟨u, hu, by simp [eof]⟩
  have hbound : ∀ w,
      (if val (fix true gates) (Zof (S w)) (out w) = false then (S w).card - 1
      else ((S w).filter (fun u => val (fix false gates) (eof u) (out w) = true)).card - 1)
        ≤ (DD w).card := by
    intro w
    by_cases hT : val (fix true gates) (Zof (S w)) (out w) = false
    · simp only [DD, hT, if_true]
      have h1' : ((S w).image (l1 w)).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha b hb
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
        exact (hinv1 w (out w) u v hT (hE1 w u hu) (hE1 w v hv)).2
      have := hcard1 w
      omega
    · simp only [DD]
      rw [if_neg hT, if_neg hT]
      have hA1 : (((S w).filter (fun u => val (fix false gates) (eof u) (out w) = true)).image
          (l0 w)).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha b hb
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
        rw [Finset.mem_filter] at hu hv
        exact (hinv0 w (out w) u v (hZ0 w) hu.2 hv.2).2
      have hsub : (S w).image (l0 w) ⊆
          ((S w) \ (S w).filter (fun u => val (fix false gates) (eof u) (out w) = true)).image
            (l0 w) ∪
          ((S w).filter (fun u => val (fix false gates) (eof u) (out w) = true)).image
            (l0 w) := by
        intro y hy
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
        by_cases huA : u ∈ (S w).filter (fun u => val (fix false gates) (eof u) (out w) = true)
        · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ huA)
        · exact Finset.mem_union_left _
            (Finset.mem_image_of_mem _ (Finset.mem_sdiff.mpr ⟨hu, huA⟩))
      have c1 := Finset.card_le_card hsub
      have c2 := Finset.card_union_le
        (((S w) \ (S w).filter (fun u => val (fix false gates) (eof u) (out w) = true)).image
          (l0 w))
        (((S w).filter (fun u => val (fix false gates) (eof u) (out w) = true)).image (l0 w))
      have c3 := Finset.card_image_le
        (s := (S w) \ (S w).filter (fun u => val (fix false gates) (eof u) (out w) = true))
        (f := l0 w)
      have c4 := Finset.card_sdiff_add_card_eq_card
        (Finset.filter_subset (fun u => val (fix false gates) (eof u) (out w) = true) (S w))
      have := hcard0 w
      omega
  have hmem : ∀ c i, i ∈ DD c →
      (∀ u, val (fix false gates) (eof u) i = true → u ∈ S c) ∧
      (((∀ u, val (fix true gates) (eof u) i = true → u ∈ S c) ∧
          ∃ u v : Fin n, u ≠ v ∧ val (fix true gates) (eof u) i = true ∧
            val (fix true gates) (eof v) i = true) ∨
        (∃ u v : Fin n, u ≠ v ∧ val (fix false gates) (eof u) i = true ∧
            val (fix false gates) (eof v) i = true)) := by
    intro c i hi
    by_cases hT : val (fix true gates) (Zof (S c)) (out c) = false
    · simp only [DD, hT, if_true] at hi
      obtain ⟨hp, huv⟩ := mem_D_one (S c) (fix true gates) (l1 c) (hinv1 c) i hi
      exact ⟨fun u hu => hp u ((hle (eof u) i).2 ((hle (eof u) i).1 hu)), Or.inl ⟨hp, huv⟩⟩
    · simp only [DD] at hi
      rw [if_neg hT] at hi
      obtain ⟨hp, huv⟩ := mem_D_one (S c) (fix false gates) (l0 c) (hinv0 c) i hi
      exact ⟨hp, Or.inr huv⟩
  have two : ∀ a b : Fin m, a ≠ b → ∀ u v : Fin n, u ≠ v → u ∈ S a → v ∈ S a → u ∈ S b →
      v ∈ S b → False := by
    intro a b hab u v huv hua hva hub hvb
    have hsub : ({u, v} : Finset (Fin n)) ⊆ S a ∩ S b := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hua, hub⟩
      · exact Finset.mem_inter.mpr ⟨hva, hvb⟩
    have h2 : ({u, v} : Finset (Fin n)).card = 2 := Finset.card_pair huv
    have := Finset.card_le_card hsub
    have := hS a b hab
    omega
  have hdisj : ∀ a ∈ (Finset.univ : Finset (Fin m)), ∀ b ∈ (Finset.univ : Finset (Fin m)),
      a ≠ b → Disjoint (DD a) (DD b) := by
    intro a _ b _ hab
    rw [Finset.disjoint_left]
    intro i hia hib
    obtain ⟨pa, ra⟩ := hmem a i hia
    obtain ⟨pb, rb⟩ := hmem b i hib
    rcases ra with ⟨qa, u, v, huv, hu, hv⟩ | ⟨u, v, huv, hu, hv⟩
    · rcases rb with ⟨qb, -⟩ | ⟨u', v', huv', hu', hv'⟩
      · exact two a b hab u v huv (qa u hu) (qa v hv) (qb u hu) (qb v hv)
      · exact two a b hab u' v' huv' (pa u' hu') (pa v' hv') (pb u' hu') (pb v' hv')
    · exact two a b hab u v huv (pa u hu) (pa v hv) (pb u hu) (pb v hv)
  calc _ ≤ ∑ w, (DD w).card := Finset.sum_le_sum fun w _ => hbound w
    _ = (Finset.univ.biUnion DD).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.Ico n (n + gates.length)).card := by
        apply Finset.card_le_card
        intro i hi
        obtain ⟨w, -, hw⟩ := Finset.mem_biUnion.mp hi
        simp only [DD] at hw
        split_ifs at hw
        · have := D_range _ _ i hw
          rwa [fix_length] at this
        · have := D_range _ _ i hw
          rwa [fix_length] at this
    _ = gates.length := by simp
end PEqualNP.Outside.L_meta_951
