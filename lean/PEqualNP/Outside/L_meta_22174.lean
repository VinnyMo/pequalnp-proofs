import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_22174

def circuit : Circuit := ⟨[⟨.not, [3]⟩, ⟨.and, [1, 6]⟩, ⟨.not, [1]⟩, ⟨.and, [3, 8]⟩, ⟨.not, [0]⟩, ⟨.and, [4, 10]⟩, ⟨.and, [2, 0]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [13, 9]⟩, ⟨.or, [14, 11]⟩, ⟨.or, [15, 12]⟩, ⟨.not, [16]⟩], 17⟩

def legal (g : Gate) : Bool :=
  (match g.op with | .and | .or | .not => true | _ => false) && decide (g.inputs.length ≤ 2)

theorem legalCircuit : FanInTwo circuit := by
  have ok : circuit.gates.all legal = true := by decide +kernel
  intro g hg
  have h := List.all_eq_true.mp ok g hg
  cases e : g.op <;> simp [legal, e] at h ⊢ <;> first | assumption | simp_all

end PEqualNP.Outside.L_meta_22174

open PEqualNP.Outside.L_meta_22174 in
theorem PEqualNP.Outside.L_meta_22174 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16913 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨circuit, legalCircuit, by decide, by decide +kernel⟩
