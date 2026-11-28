import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55740

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def cm : Circuit := ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.not, [1]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.and, [3, 10]⟩, ⟨GateOp.and, [6, 11]⟩, ⟨GateOp.not, [12]⟩, ⟨GateOp.or, [8, 13]⟩, ⟨GateOp.and, [14, 15]⟩], 16⟩

theorem cm_fan : FanInTwo cm := by
  intro g hg
  simp only [cm, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem cm_size : cm.size ≤ 11 := by decide

theorem cm_ok : ∀ i j : Fin 6, cm.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6508349 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_55740

theorem PEqualNP.Outside.L_meta_55740 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6508349 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_55740.cm, PEqualNP.Outside.L_meta_55740.cm_fan, PEqualNP.Outside.L_meta_55740.cm_size, PEqualNP.Outside.L_meta_55740.cm_ok⟩
