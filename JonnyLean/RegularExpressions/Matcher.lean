import JonnyLean.RegularExpressions.Derivative

namespace JonnyLean.RegularExpressions

def derivatives [DecidableEq α] : List α → Regex α → Regex α
  | [], r => r
  | a::w, r => derivatives w (derivative a r)

def accepts [DecidableEq α] (r : Regex α) (w : List α) : Bool := nullable (derivatives w r)

theorem derivatives_correct [DecidableEq α] (u v : List α) (r : Regex α) :
    denotes (derivatives u r) v ↔ denotes r (u ++ v) := by
  induction u generalizing r with
  | nil => rfl
  | cons a u ih => simpa [derivatives, derivative_correct] using ih (derivative a r)

theorem derivatives_append [DecidableEq α] (u v : List α) (r : Regex α) :
    derivatives (u ++ v) r = derivatives v (derivatives u r) := by
  induction u generalizing r with
  | nil => rfl
  | cons a u ih => exact ih (derivative a r)

theorem accepts_correct [DecidableEq α] (r : Regex α) (w : List α) :
    accepts r w = true ↔ denotes r w := by
  simp [accepts, nullable_correct, derivatives_correct]

theorem accepts_append [DecidableEq α] (r : Regex α) (u v : List α) :
    accepts r (u ++ v) = accepts (derivatives u r) v := by
  simp [accepts, derivatives_append]

theorem derivatives_congr [DecidableEq α] {r s : Regex α} (h : Equivalent r s) (u : List α) :
    Equivalent (derivatives u r) (derivatives u s) := by
  intro v
  rw [derivatives_correct, derivatives_correct]
  exact h (u ++ v)

theorem accepts_congr [DecidableEq α] {r s : Regex α} (h : Equivalent r s) (w : List α) :
    accepts r w = accepts s w := by
  apply Bool.eq_iff_iff.mpr
  rw [accepts_correct, accepts_correct]
  exact h w

end JonnyLean.RegularExpressions
