import Std

namespace JonnyLean.Algorithms

/-- Traverse left to right, returning the final state and one output per input. -/
def mapState (step : σ → α → σ × β) (state : σ) : List α → σ × List β
  | [] => (state, [])
  | x :: xs =>
    let next := step state x
    let rest := mapState step next.1 xs
    (rest.1, next.2 :: rest.2)

theorem mapState_length (step : σ → α → σ × β) (state : σ) (xs : List α) :
    (mapState step state xs).2.length = xs.length := by
  induction xs generalizing state with
  | nil => rfl
  | cons x xs ih => simp only [mapState, List.length_cons, ih]

theorem mapState_final (step : σ → α → σ × β) (state : σ) (xs : List α) :
    (mapState step state xs).1 = xs.foldl (fun s x => (step s x).1) state := by
  induction xs generalizing state with
  | nil => rfl
  | cons x xs ih => exact ih (step state x).1

theorem mapState_append (step : σ → α → σ × β) (state : σ) (xs ys : List α) :
    mapState step state (xs ++ ys) =
      let first := mapState step state xs
      let second := mapState step first.1 ys
      (second.1, first.2 ++ second.2) := by
  induction xs generalizing state with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, mapState, ih]

theorem mapState_invariant (step : σ → α → σ × β) (p : σ → Prop) (q : β → Prop)
    (preserve : ∀ s x, p s → p (step s x).1 ∧ q (step s x).2)
    (state : σ) (xs : List α) (hs : p state) :
    p (mapState step state xs).1 ∧ ∀ y ∈ (mapState step state xs).2, q y := by
  induction xs generalizing state with
  | nil => exact ⟨hs, by simp [mapState]⟩
  | cons x xs ih =>
    have hstep := preserve state x hs
    have hrest := ih (step state x).1 hstep.1
    refine ⟨hrest.1, ?_⟩
    intro y hy
    cases List.mem_cons.mp hy with
    | inl hy => exact hy ▸ hstep.2
    | inr hy => exact hrest.2 y hy

theorem mapState_stateless (f : α → β) (state : σ) (xs : List α) :
    mapState (fun s x => (s, f x)) state xs = (state, xs.map f) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [mapState, ih, List.map_cons]

end JonnyLean.Algorithms
