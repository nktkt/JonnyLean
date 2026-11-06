import Std

namespace JonnyLean.Imperative

abbrev State := Nat → Nat

def update (s : State) (x value : Nat) : State :=
  fun y => if y = x then value else s y

def Agrees (xs : List Nat) (s t : State) : Prop := ∀ x ∈ xs, s x = t x

@[simp] theorem update_self (s : State) (x n : Nat) : update s x n x = n := by
  simp [update]

theorem update_other (s : State) (x y n : Nat) (h : y ≠ x) : update s x n y = s y := by
  simp [update, h]

theorem update_shadow (s : State) (x a b : Nat) : update (update s x a) x b = update s x b := by
  funext y
  simp only [update]
  split <;> rfl

theorem update_comm (s : State) (x y a b : Nat) (h : x ≠ y) :
    update (update s x a) y b = update (update s y b) x a := by
  funext z
  simp only [update]
  by_cases hx : z = x
  · subst z; simp [h]
  · by_cases hy : z = y
    · subst z; simp [hx]
    · simp [hx, hy]

theorem update_same (s : State) (x : Nat) : update s x (s x) = s := by
  funext y
  by_cases h : y = x
  · subst y; simp
  · exact update_other s x y (s x) h

theorem agrees_update (xs : List Nat) (s t : State) (x n : Nat)
    (h : Agrees xs s t) : Agrees xs (update s x n) (update t x n) := by
  intro y hy
  by_cases heq : y = x
  · subst y; simp
  · simpa [update, heq] using h y hy

theorem agrees_refl (xs : List Nat) (s : State) : Agrees xs s s := fun _ _ => rfl

theorem agrees_trans (xs : List Nat) (s t u : State)
    (h : Agrees xs s t) (k : Agrees xs t u) : Agrees xs s u :=
  fun x hx => (h x hx).trans (k x hx)

end JonnyLean.Imperative
