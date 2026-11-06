import JonnyLean.Languages.Star

/- Independent expected types, definition semantics, and boundary cases. -/
universe u v w
open JonnyLean.Languages
variable {α : Type u} {β : Type v} {γ : Type w}
variable {Q : Type u} {R : Type v}

theorem contract_JL148 {L K : Language α} (h0 : K []) (hL : ∀ w, L w → K w) (hc : ∀ u v, K u → K v → K (u ++ v)) : ∀ w, Star L w → K w := star_minimal h0 hL hc

theorem contract_JL148_semantics {L : Language α} {u v : List α} (hu : L u) (hv : Star L v) : Star L (u ++ v) := Star.step hu hv

theorem contract_JL148_boundary : Star (empty : Language Nat) [] := Star.nil

#print axioms JonnyLean.Languages.star_minimal
#print axioms contract_JL148
#print axioms contract_JL148_semantics
#print axioms contract_JL148_boundary
