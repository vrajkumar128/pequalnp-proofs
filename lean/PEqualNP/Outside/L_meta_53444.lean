import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53444

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def cm : Circuit := ⟨[⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [10, 9]⟩, ⟨GateOp.or, [11, 8]⟩, ⟨GateOp.and, [0, 12]⟩, ⟨GateOp.or, [10, 4]⟩, ⟨GateOp.and, [1, 14]⟩, ⟨GateOp.or, [3, 2]⟩, ⟨GateOp.or, [5, 4]⟩, ⟨GateOp.and, [16, 17]⟩, ⟨GateOp.or, [13, 15]⟩, ⟨GateOp.or, [18, 19]⟩], 20⟩

theorem cm_mono : Monotone2 cm := by
  intro g hg
  simp only [cm, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem cm_size : cm.size ≤ 11 := by decide

theorem cm_rep : PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 6) => (799612 : ℕ).testBit (6 * u.val + v.val)) cm := by
  decide +kernel

end PEqualNP.Outside.L_meta_53444

theorem PEqualNP.Outside.L_meta_53444 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (799612 : ℕ).testBit (6 * u.val + v.val)) 11 :=
  ⟨PEqualNP.Outside.L_meta_53444.cm, PEqualNP.Outside.L_meta_53444.cm_mono, PEqualNP.Outside.L_meta_53444.cm_size, PEqualNP.Outside.L_meta_53444.cm_rep⟩
