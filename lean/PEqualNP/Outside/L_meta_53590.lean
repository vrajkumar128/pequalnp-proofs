import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53590

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def cm : Circuit := ⟨[⟨GateOp.or, [2, 4]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.or, [3, 7]⟩, ⟨GateOp.or, [6, 8]⟩, ⟨GateOp.or, [1, 11]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.or, [9, 15]⟩, ⟨GateOp.or, [0, 15]⟩, ⟨GateOp.and, [14, 16]⟩, ⟨GateOp.and, [10, 17]⟩, ⟨GateOp.or, [18, 19]⟩], 20⟩

theorem cm_mono : Monotone2 cm := by
  intro g hg
  simp only [cm, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem cm_size : cm.size ≤ 11 := by decide

theorem cm_rep : PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 6) => (905021 : ℕ).testBit (6 * u.val + v.val)) cm := by
  decide +kernel

end PEqualNP.Outside.L_meta_53590

theorem PEqualNP.Outside.L_meta_53590 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (905021 : ℕ).testBit (6 * u.val + v.val)) 11 :=
  ⟨PEqualNP.Outside.L_meta_53590.cm, PEqualNP.Outside.L_meta_53590.cm_mono, PEqualNP.Outside.L_meta_53590.cm_size, PEqualNP.Outside.L_meta_53590.cm_rep⟩
