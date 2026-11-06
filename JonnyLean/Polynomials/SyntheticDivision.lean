import JonnyLean.Polynomials.Addition

namespace JonnyLean.Polynomials

/-- Quotient of p(X)-p(a) by X-a, represented without subtraction. -/
def dividedDifference (a : Nat) : Polynomial → Polynomial
  | [] => []
  | _::p => add [evaluate p a] (0 :: dividedDifference a p)

theorem dividedDifference_identity (a x : Nat) (p : Polynomial) :
    evaluate p x + a * evaluate (dividedDifference a p) x =
      evaluate p a + x * evaluate (dividedDifference a p) x := by
  induction p with
  | nil => simp [evaluate, dividedDifference]
  | cons c p ih =>
    simp only [dividedDifference, evaluate_add, evaluate, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
    calc
      c+x*evaluate p x+a*(evaluate p a+x*evaluate (dividedDifference a p) x) =
          c+a*evaluate p a+x*(evaluate p x+a*evaluate (dividedDifference a p) x) := by
        simp only [Nat.mul_add]; ac_rfl
      _ = c+a*evaluate p a+x*(evaluate p a+x*evaluate (dividedDifference a p) x) := by rw [ih]

theorem dividedDifference_remainder (a x : Nat) (p : Polynomial) (h : a ≤ x) :
    evaluate p x = evaluate p a + (x-a)*evaluate (dividedDifference a p) x := by
  have hi := dividedDifference_identity a x p
  have hx : x = a+(x-a) := (Nat.add_sub_of_le h).symm
  have hm : x*evaluate (dividedDifference a p) x =
      a*evaluate (dividedDifference a p) x+(x-a)*evaluate (dividedDifference a p) x := by
    calc
      x*evaluate (dividedDifference a p) x =
          (a+(x-a))*evaluate (dividedDifference a p) x := congrArg (fun t => t*evaluate (dividedDifference a p) x) hx
      _ = _ := Nat.add_mul _ _ _
  rw [hm] at hi
  omega

theorem dividedDifference_constant (a c : Nat) (x : Nat) :
    evaluate (dividedDifference a [c]) x = 0 := by simp [dividedDifference, evaluate_add, evaluate]

theorem dividedDifference_affine (a b c x : Nat) :
    evaluate (dividedDifference a [c,b]) x = b := by
  simp [dividedDifference, evaluate_add, evaluate]

end JonnyLean.Polynomials
