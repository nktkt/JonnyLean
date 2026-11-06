import JonnyLean.Algorithms.StateTraversal

namespace JonnyLean.Contracts

/-- Independent, fully quantified public target for JL-043. -/
theorem JL043 {σ : Type u} {α : Type v} {β : Type w}
    (step : σ → α → σ × β) (p : σ → Prop) (q : β → Prop)
    (preserve : ∀ s x, p s → p (step s x).1 ∧ q (step s x).2)
    (state : σ) (xs : List α) (hs : p state) :
    p (JonnyLean.Algorithms.mapState step state xs).1 ∧
      ∀ y ∈ (JonnyLean.Algorithms.mapState step state xs).2, q y :=
  JonnyLean.Algorithms.mapState_invariant step p q preserve state xs hs

example : JonnyLean.Algorithms.mapState (fun (s x : Nat) => (s + x, s)) 0 [2, 3, 4] =
    (9, [0, 2, 5]) := rfl

example {σ : Type u} {α : Type v} {β : Type w}
    (step : σ → α → σ × β) (state : σ) :
    JonnyLean.Algorithms.mapState step state [] = (state, []) := rfl
end JonnyLean.Contracts

#print axioms JonnyLean.Algorithms.mapState_invariant
#print axioms JonnyLean.Contracts.JL043
