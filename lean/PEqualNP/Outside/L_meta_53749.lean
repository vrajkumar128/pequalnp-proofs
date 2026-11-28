import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53749

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def cm : Circuit := ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [5, 8]⟩, ⟨GateOp.or, [0, 8]⟩, ⟨GateOp.and, [6, 9]⟩, ⟨GateOp.and, [7, 10]⟩, ⟨GateOp.or, [11, 12]⟩], 13⟩

theorem cm_fan : Monotone2 cm := by
  intro g hg
  simp only [cm, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem cm_size : cm.size ≤ 9 := by decide

theorem cm_ok : ∀ i j : Fin 6, cm.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (101950 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_53749

theorem PEqualNP.Outside.L_meta_53749 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (101950 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_53749.cm, PEqualNP.Outside.L_meta_53749.cm_fan, PEqualNP.Outside.L_meta_53749.cm_size, PEqualNP.Outside.L_meta_53749.cm_ok⟩
