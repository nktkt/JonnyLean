import JonnyLean.Languages.Image

/- Independent expected types, definition semantics, and boundary cases. -/
universe u v w
open JonnyLean.Languages
variable {α : Type u} {β : Type v} {γ : Type w}
variable {Q : Type u} {R : Type v}

theorem contract_JL150 (f : α → β) (L : Language α) : image f (Star L) = Star (image f L) := image_star f L

theorem contract_JL150_semantics (f : α → β) (L : Language α) (w : List β) : image f L w ↔ ∃ u, L u ∧ u.map f = w := Iff.rfl

theorem contract_JL150_boundary : image (fun _ : Nat => true) (fun w => w = [1, 2]) [true, true] := ⟨[1, 2], rfl, rfl⟩

#print axioms JonnyLean.Languages.image_star
#print axioms contract_JL150
#print axioms contract_JL150_semantics
#print axioms contract_JL150_boundary
