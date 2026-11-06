import JonnyLean.DiscreteProbability.Mass

/- Independent expected statements, definition semantics, and boundary cases. -/
open JonnyLean.DiscreteProbability

theorem contract_JL059 {α : Type u} (w : α → Nat) (p : α → Bool) (xs : List α) :
    eventMass w p xs + eventMass w (fun a => !p a) xs = mass w xs := eventMass_complement w p xs

example (w : α → Nat) : mass w [] = 0 := rfl
example (w : α → Nat) (a : α) (xs : List α) : mass w (a :: xs) = w a + mass w xs := rfl
example (w : α → Nat) (p : α → Bool) (a : α) (xs : List α) :
    eventMass w p (a :: xs) = (if p a then w a else 0) + eventMass w p xs := rfl
example (w : α → Nat) (p : α → Bool) : eventMass w p [] = 0 := rfl
example (w : α → Nat) (p q : α → Bool) (xs : List α)
    (h : ∀ a, a ∈ xs → p a = true → q a = false) :
    eventMass w (fun a => p a || q a) xs = eventMass w p xs + eventMass w q xs :=
  eventMass_disjoint_union w p q xs h
example : eventMass (fun b : Bool => if b then 2 else 1) id [false, true] = 2 := rfl

#print axioms JonnyLean.DiscreteProbability.eventMass_complement
#print axioms contract_JL059
