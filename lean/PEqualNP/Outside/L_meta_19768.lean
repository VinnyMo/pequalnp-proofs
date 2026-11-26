import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19768

def witness : Circuit :=
  ⟨[⟨.or, [8, 10]⟩,
    ⟨.or, [11, 12]⟩,
    ⟨.or, [14, 15]⟩,
    ⟨.or, [9, 13]⟩,
    ⟨.or, [9, 16]⟩,
    ⟨.or, [13, 17]⟩,
    ⟨.or, [18, 21]⟩,
    ⟨.and, [0, 22]⟩,
    ⟨.or, [10, 17]⟩,
    ⟨.or, [24, 19]⟩,
    ⟨.and, [1, 25]⟩,
    ⟨.or, [16, 21]⟩,
    ⟨.and, [2, 27]⟩,
    ⟨.or, [12, 18]⟩,
    ⟨.or, [29, 19]⟩,
    ⟨.and, [3, 30]⟩,
    ⟨.or, [15, 16]⟩,
    ⟨.or, [32, 19]⟩,
    ⟨.and, [4, 33]⟩,
    ⟨.or, [8, 17]⟩,
    ⟨.or, [35, 18]⟩,
    ⟨.and, [5, 36]⟩,
    ⟨.or, [18, 20]⟩,
    ⟨.and, [6, 38]⟩,
    ⟨.or, [11, 14]⟩,
    ⟨.or, [40, 20]⟩,
    ⟨.and, [7, 41]⟩,
    ⟨.or, [23, 26]⟩,
    ⟨.or, [43, 28]⟩,
    ⟨.or, [44, 31]⟩,
    ⟨.or, [45, 34]⟩,
    ⟨.or, [46, 37]⟩,
    ⟨.or, [47, 39]⟩,
    ⟨.or, [48, 42]⟩], 49⟩

def legal (g : Gate) : Bool :=
  (match g.op with | .and | .or => true | _ => false) && decide (g.inputs.length ≤ 2)

theorem shape : Monotone2 witness := by
  have allLegal : witness.gates.all legal = true := by decide +kernel
  intro g hg
  have ok := List.all_eq_true.mp allLegal g hg
  cases h : g.op <;> simp [legal, h] at ok ⊢ <;> first | assumption | simp_all

end PEqualNP.Outside.L_meta_19768

open PEqualNP.Outside.L_meta_19768 in
set_option maxRecDepth 4096 in
theorem PEqualNP.Outside.L_meta_19768 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5748802764708593400 : ℕ).testBit (8 * u.val + v.val)) 34) := by
  exact ⟨witness, shape, by decide, by decide +kernel⟩
