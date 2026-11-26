import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19718

def witness : Circuit :=
  ⟨[⟨.or, [8, 9]⟩,
    ⟨.or, [10, 12]⟩,
    ⟨.or, [14, 15]⟩,
    ⟨.or, [11, 13]⟩,
    ⟨.or, [11, 16]⟩,
    ⟨.or, [13, 16]⟩,
    ⟨.or, [17, 19]⟩,
    ⟨.or, [8, 22]⟩,
    ⟨.and, [0, 23]⟩,
    ⟨.or, [15, 22]⟩,
    ⟨.and, [1, 25]⟩,
    ⟨.or, [17, 20]⟩,
    ⟨.and, [2, 27]⟩,
    ⟨.or, [18, 20]⟩,
    ⟨.and, [3, 29]⟩,
    ⟨.or, [12, 18]⟩,
    ⟨.or, [31, 19]⟩,
    ⟨.and, [4, 32]⟩,
    ⟨.or, [18, 21]⟩,
    ⟨.and, [5, 34]⟩,
    ⟨.or, [9, 17]⟩,
    ⟨.or, [36, 18]⟩,
    ⟨.and, [6, 37]⟩,
    ⟨.or, [10, 14]⟩,
    ⟨.or, [39, 21]⟩,
    ⟨.and, [7, 40]⟩,
    ⟨.or, [24, 26]⟩,
    ⟨.or, [42, 28]⟩,
    ⟨.or, [43, 30]⟩,
    ⟨.or, [44, 33]⟩,
    ⟨.or, [45, 35]⟩,
    ⟨.or, [46, 38]⟩,
    ⟨.or, [47, 41]⟩], 48⟩

def legal (g : Gate) : Bool :=
  (match g.op with | .and | .or => true | _ => false) && decide (g.inputs.length ≤ 2)

theorem shape : Monotone2 witness := by
  have allLegal : witness.gates.all legal = true := by decide +kernel
  intro g hg
  have ok := List.all_eq_true.mp allLegal g hg
  cases h : g.op <;> simp [legal, h] at ok ⊢ <;> first | assumption | simp_all

end PEqualNP.Outside.L_meta_19718

open PEqualNP.Outside.L_meta_19718 in
set_option maxRecDepth 4096 in
theorem PEqualNP.Outside.L_meta_19718 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7482418488621907005 : ℕ).testBit (8 * u.val + v.val)) 33) := by
  exact ⟨witness, shape, by decide, by decide +kernel⟩
