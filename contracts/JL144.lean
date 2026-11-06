import JonnyLean.Languages.Monoid

/- Independent expected types, definition semantics, and boundary cases. -/
universe u v w
open JonnyLean.Languages
variable {α : Type u} {β : Type v} {γ : Type w}
variable {Q : Type u} {R : Type v}

theorem contract_JL144 (L K M : Language α) : concat (concat L K) M = concat L (concat K M) := concat_assoc L K M

theorem contract_JL144_semantics (w : List α) : epsilon w ↔ w = [] := Iff.rfl

theorem contract_JL144_boundary : concat (fun w : List Nat => w = [1]) (fun w => w = [2]) [1, 2] := ⟨[1], [2], rfl, rfl, rfl⟩

#print axioms JonnyLean.Languages.concat_assoc
#print axioms contract_JL144
#print axioms contract_JL144_semantics
#print axioms contract_JL144_boundary
