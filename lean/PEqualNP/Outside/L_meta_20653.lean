import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_20653

def witness : Circuit :=
  ⟨[⟨.and, [2, 5]⟩,
    ⟨.and, [3, 6]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.or, [12, 7]⟩,
    ⟨.and, [4, 13]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [15, 14]⟩], 16⟩

def legal (g : Gate) : Bool :=
  (match g.op with | .and | .or => true | _ => false) && decide (g.inputs.length ≤ 2)

theorem shape : Monotone2 witness := by
  have allLegal : witness.gates.all legal = true := by decide +kernel
  intro g hg
  have ok := List.all_eq_true.mp allLegal g hg
  cases h : g.op <;> simp [legal, h] at ok ⊢ <;> first | assumption | simp_all

end PEqualNP.Outside.L_meta_20653

open PEqualNP.Outside.L_meta_20653 in
set_option maxRecDepth 4096 in
theorem PEqualNP.Outside.L_meta_20653 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (7406592 : ℕ).testBit (5 * u.val + v.val)) 7) := by
  exact ⟨witness, shape, by decide, by decide +kernel⟩
