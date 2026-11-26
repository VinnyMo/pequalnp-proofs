import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_22277

def circuit : Circuit := ⟨[⟨.or, [3, 4]⟩, ⟨.or, [6, 5]⟩, ⟨.not, [7]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [10, 5]⟩, ⟨.not, [11]⟩, ⟨.and, [2, 12]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [14, 5]⟩, ⟨.and, [0, 15]⟩, ⟨.or, [9, 13]⟩, ⟨.or, [17, 16]⟩], 18⟩

def legal (g : Gate) : Bool :=
  (match g.op with | .and | .or | .not => true | _ => false) && decide (g.inputs.length ≤ 2)

theorem legalCircuit : FanInTwo circuit := by
  have ok : circuit.gates.all legal = true := by decide +kernel
  intro g hg
  have h := List.all_eq_true.mp ok g hg
  cases e : g.op <;> simp [legal, e] at h ⊢ <;> first | assumption | simp_all

end PEqualNP.Outside.L_meta_22277

open PEqualNP.Outside.L_meta_22277 in
theorem PEqualNP.Outside.L_meta_22277 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16830 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨circuit, legalCircuit, by decide, by decide +kernel⟩
