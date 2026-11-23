
lemma value_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length) :
    value C x (n + j) = (C.gates[j]).op.eval
      ((C.gates[j]).inputs.map fun r => if r < n + j then value C x r else false) := by
  have h := gate_value C x (n + j) (by omega) (by unfold Circuit.size; omega)
  have e : n + j - n = j := by omega
  simp only [e] at h
  exact h

lemma eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (f g : ℕ → Bool) (h : ∀ r ∈ ins, f r = true → g r = true) :
    op.eval (ins.map f) = true → op.eval (ins.map g) = true := by
  intro hx
  rcases hop with hop | hop
  · subst hop
    simp only [GateOp.eval, List.all_eq_true, id_eq, List.mem_map] at hx ⊢
    rintro b ⟨r, hr, rfl⟩
    exact h r hr (hx _ ⟨r, hr, rfl⟩)
  · subst hop
    simp only [GateOp.eval, List.any_eq_true, id_eq, List.mem_map] at hx ⊢
    obtain ⟨b, ⟨r, hr, rfl⟩, hb⟩ := hx
    exact ⟨_, ⟨r, hr, rfl⟩, h r hr hb⟩

def isNot (op : GateOp) : Bool := match op with
  | GateOp.not => true
  | _ => false

lemma isNot_iff (op : GateOp) : isNot op = true ↔ op = GateOp.not := by
  cases op <;> simp [isNot]

def fix0 (g : Gate) : Gate := if isNot g.op = true then ⟨GateOp.or, []⟩ else g

def C0 (C : Circuit) : Circuit := ⟨C.gates.map fix0, C.output⟩

lemma C0_length (C : Circuit) : (C0 C).gates.length = C.gates.length := by
  simp [C0]

lemma C0_size (C : Circuit) : (C0 C).size = C.size := by
  simp [C0, Circuit.size]

lemma C0_get (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    (C0 C).gates[j]'(by rw [C0_length]; exact hj) = fix0 (C.gates[j]) := by
  simp [C0]

lemma C0_good (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) :
    ∀ g ∈ (C0 C).gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [C0, List.mem_map] at hg
  obtain ⟨g', hg', rfl⟩ := hg
  obtain ⟨hop, hlen⟩ := hG g' hg'
  unfold fix0
  by_cases h : g'.op = GateOp.not
  · have h' : isNot g'.op = true := (isNot_iff _).mpr h
    simp [h']
  · have h' : ¬ isNot g'.op = true := fun e => h ((isNot_iff _).mp e)
    simp only [h', if_false]
    refine ⟨?_, hlen⟩
    rcases hop with hop | hop | hop
    · exact Or.inl hop
    · exact Or.inr hop
    · exact absurd hop h

lemma value_C0_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length) :
    value (C0 C) x (n + j) = (fix0 (C.gates[j])).op.eval
      ((fix0 (C.gates[j])).inputs.map fun r => if r < n + j then value (C0 C) x r else false) := by
  rw [value_gate (C0 C) x j (by rw [C0_length]; exact hj), C0_get C j hj]

lemma C0_le {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (x : Fin n → Bool) (w : ℕ) : value (C0 C) x w = true → value C x w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value (C0 C) x p = true → value C x p = true
      simp only [input_value]
      exact id
    by_cases hw : w < n + C.size
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by unfold Circuit.size at hw; omega
      rw [value_C0_gate C x j hj, value_gate C x j hj]
      unfold fix0
      by_cases h : (C.gates[j]).op = GateOp.not
      · have h' : isNot (C.gates[j]).op = true := (isNot_iff _).mpr h
        simp [h', GateOp.eval]
      · have h' : ¬ isNot (C.gates[j]).op = true := fun e => h ((isNot_iff _).mp e)
        simp only [h', if_false]
        have hop := (hG _ (List.getElem_mem hj)).1
        have hop' : (C.gates[j]).op = GateOp.and ∨ (C.gates[j]).op = GateOp.or := by
          rcases hop with hop | hop | hop
          · exact Or.inl hop
          · exact Or.inr hop
          · exact absurd hop h
        apply eval_mono _ hop'
        intro r _ hr
        by_cases hlt : r < n + j
        · simp only [hlt, if_true] at hr ⊢
          exact ih r hlt hr
        · simp [hlt] at hr
    · have h0 : value (C0 C) x w = false := missing_value (C0 C) x w (by rw [C0_size]; omega)
      simp [h0]

lemma C0_agree {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (h : ∀ j (hj : j < C.gates.length), n + j ≤ w → (C.gates[j]).op = GateOp.not →
      value C x (n + j) = false) :
    value (C0 C) x w = value C x w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value (C0 C) x p = value C x p
      simp only [input_value]
    by_cases hw : w < n + C.size
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by unfold Circuit.size at hw; omega
      rw [value_C0_gate C x j hj]
      unfold fix0
      by_cases hnot : (C.gates[j]).op = GateOp.not
      · have h' : isNot (C.gates[j]).op = true := (isNot_iff _).mpr hnot
        simp only [h', if_true]
        rw [h j hj le_rfl hnot]
        simp [GateOp.eval]
      · have h' : ¬ isNot (C.gates[j]).op = true := fun e => hnot ((isNot_iff _).mp e)
        simp only [h', if_false]
        rw [value_gate C x j hj]
        congr 1
        apply List.map_congr_left
        intro r _
        by_cases hlt : r < n + j
        · simp only [hlt, if_true]
          exact ih r hlt (fun j' hj' hle hn' => h j' hj' (by omega) hn')
        · simp [hlt]
    · rw [missing_value (C0 C) x w (by rw [C0_size]; omega), missing_value C x w (by omega)]

end PEqualNP.Outside.L_meta_997
