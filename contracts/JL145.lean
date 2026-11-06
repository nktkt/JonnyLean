import JonnyLean.Languages.Reversal

/- Independent expected types, definition semantics, and boundary cases. -/
universe u v w
open JonnyLean.Languages
variable {α : Type u} {β : Type v} {γ : Type w}
variable {Q : Type u} {R : Type v}

theorem contract_JL145 (L K : Language α) : reverse (concat L K) = concat (reverse K) (reverse L) := reverse_concat L K

theorem contract_JL145_semantics (L : Language α) (w : List α) : reverse L w ↔ L w.reverse := Iff.rfl

theorem contract_JL145_boundary : reverse (fun w : List Nat => w = [1, 2]) [2, 1] := rfl

#print axioms JonnyLean.Languages.reverse_concat
#print axioms contract_JL145
#print axioms contract_JL145_semantics
#print axioms contract_JL145_boundary
