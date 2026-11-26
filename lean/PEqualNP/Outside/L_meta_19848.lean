import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19848

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def cm : Circuit := ⟨[⟨GateOp.or, [14, 15]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.or, [18, 16]⟩, ⟨GateOp.or, [20, 8]⟩, ⟨GateOp.or, [20, 13]⟩, ⟨GateOp.or, [17, 16]⟩, ⟨GateOp.or, [23, 12]⟩, ⟨GateOp.or, [23, 13]⟩, ⟨GateOp.or, [18, 19]⟩, ⟨GateOp.or, [26, 14]⟩, ⟨GateOp.or, [26, 10]⟩, ⟨GateOp.or, [17, 19]⟩, ⟨GateOp.or, [29, 9]⟩, ⟨GateOp.or, [17, 12]⟩, ⟨GateOp.or, [31, 11]⟩, ⟨GateOp.or, [32, 15]⟩, ⟨GateOp.and, [0, 21]⟩, ⟨GateOp.and, [1, 24]⟩, ⟨GateOp.and, [2, 30]⟩, ⟨GateOp.and, [3, 27]⟩, ⟨GateOp.and, [4, 25]⟩, ⟨GateOp.and, [5, 33]⟩, ⟨GateOp.and, [6, 28]⟩, ⟨GateOp.and, [7, 22]⟩, ⟨GateOp.or, [34, 35]⟩, ⟨GateOp.or, [36, 37]⟩, ⟨GateOp.or, [38, 39]⟩, ⟨GateOp.or, [40, 41]⟩, ⟨GateOp.or, [42, 43]⟩, ⟨GateOp.or, [44, 45]⟩, ⟨GateOp.or, [46, 47]⟩], 48⟩

theorem cm_mono : Monotone2 cm := by
  intro g hg
  simp only [cm, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem cm_size : cm.size ≤ 33 := by decide

theorem cm_rep : PEqualNP.Represents.Represents (fun u v : Fin 8 => (16879102062354748875 : ℕ).testBit (8 * u.val + v.val)) cm := by
  decide +kernel

end PEqualNP.Outside.L_meta_19848

theorem PEqualNP.Outside.L_meta_19848 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16879102062354748875 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨PEqualNP.Outside.L_meta_19848.cm, PEqualNP.Outside.L_meta_19848.cm_mono, PEqualNP.Outside.L_meta_19848.cm_size, PEqualNP.Outside.L_meta_19848.cm_rep⟩
