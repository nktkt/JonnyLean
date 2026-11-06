import JonnyLean.Languages.Lattice

/- Independent expected types, definition semantics, and boundary cases. -/
universe u v w
open JonnyLean.Languages
variable {α : Type u} {β : Type v} {γ : Type w}
variable {Q : Type u} {R : Type v}

theorem contract_JL142 (A : α → Prop) (u v : List α) : alphabetLanguage A (u ++ v) ↔ alphabetLanguage A u ∧ alphabetLanguage A v := alphabetLanguage_append A u v

theorem contract_JL142_semantics (A : α → Prop) (w : List α) : alphabetLanguage A w ↔ ∀ a, a ∈ w → A a := Iff.rfl

theorem contract_JL142_boundary : alphabetLanguage (fun b : Bool => b = false ∨ b = true) [false, true] ∧ ¬union (alphabetLanguage (fun b : Bool => b = false)) (alphabetLanguage (fun b : Bool => b = true)) [false, true] := by
  constructor
  · intro b _
    cases b <;> simp
  · intro h
    rcases h with h | h
    · have bad := h true (by simp)
      cases bad
    · have bad := h false (by simp)
      cases bad

#print axioms JonnyLean.Languages.alphabetLanguage_append
#print axioms contract_JL142
#print axioms contract_JL142_semantics
#print axioms contract_JL142_boundary
