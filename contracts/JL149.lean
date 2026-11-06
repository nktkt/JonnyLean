import JonnyLean.Languages.StarClosure

/- Independent expected types, definition semantics, and boundary cases. -/
universe u v w
open JonnyLean.Languages
variable {α : Type u} {β : Type v} {γ : Type w}
variable {Q : Type u} {R : Type v}

theorem contract_JL149 (L : Language α) (w : List α) : Star L w ↔ ∃ n, power L n w := star_iff_power L w

theorem contract_JL149_semantics (L : Language α) : Star (Star L) = Star L := star_idempotent L

theorem contract_JL149_boundary : Star (empty : Language Nat) = epsilon := star_empty

#print axioms JonnyLean.Languages.star_iff_power
#print axioms contract_JL149
#print axioms contract_JL149_semantics
#print axioms contract_JL149_boundary
