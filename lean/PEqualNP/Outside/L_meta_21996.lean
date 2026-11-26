import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_21996

def circuit : Circuit := ⟨[⟨.or, [2, 3]⟩, ⟨.not, [6]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [0, 1]⟩, ⟨.not, [9]⟩, ⟨.and, [3, 10]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [12, 8]⟩, ⟨.or, [13, 11]⟩, ⟨.not, [14]⟩], 15⟩

def legal (g : Gate) : Bool :=
  (match g.op with | .and | .or | .not => true | _ => false) && decide (g.inputs.length ≤ 2)

theorem legalCircuit : FanInTwo circuit := by
  have ok : circuit.gates.all legal = true := by decide +kernel
  intro g hg
  have h := List.all_eq_true.mp ok g hg
  cases e : g.op <;> simp [legal, e] at h ⊢ <;> first | assumption | simp_all

end PEqualNP.Outside.L_meta_21996

open PEqualNP.Outside.L_meta_21996 in
theorem PEqualNP.Outside.L_meta_21996 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17165 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨circuit, legalCircuit, by decide, by decide +kernel⟩
