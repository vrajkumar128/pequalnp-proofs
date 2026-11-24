import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace Probe651

def C : Circuit := ⟨[⟨GateOp.or, [2, 5]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [3, 9]⟩, ⟨GateOp.and, [2, 12]⟩, ⟨GateOp.and, [7, 11]⟩, ⟨GateOp.or, [5, 13]⟩, ⟨GateOp.and, [4, 14]⟩, ⟨GateOp.and, [0, 17]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.or, [1, 9]⟩, ⟨GateOp.or, [16, 19]⟩, ⟨GateOp.or, [6, 20]⟩, ⟨GateOp.or, [18, 22]⟩, ⟨GateOp.or, [15, 24]⟩, ⟨GateOp.and, [8, 23]⟩, ⟨GateOp.or, [25, 26]⟩, ⟨GateOp.and, [6, 21]⟩, ⟨GateOp.or, [27, 28]⟩], 29⟩

theorem fan : PEqualNP.MetaComplexity.FanInTwo C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem tab : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    C.eval [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9] = ((b0 && b1) || (b1 && b2) || (b2 && b3) || (b3 && b4) || (b4 && b0) || (b0 && b5) || (b1 && b6) || (b2 && b7) || (b3 && b8) || (b4 && b9) || (b5 && b7) || (b7 && b9) || (b9 && b6) || (b6 && b8) || (b8 && b5)) := by
  decide

theorem main : PEqualNP.MetaComplexity.HasCircuitSize 10 (fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) 20 := by
  refine ⟨C, fan, by simp [C, Circuit.size], ?_⟩
  intro x
  have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9] := by
    simp [List.ofFn_succ]
  rw [h, tab]

end Probe651
