import JonnyLean.Polynomials.Evaluation

namespace JonnyLean.Polynomials

def add : Polynomial → Polynomial → Polynomial
  | [], q => q
  | p, [] => p
  | a::p, b::q => (a+b)::add p q

theorem evaluate_add (p q : Polynomial) (x : Nat) :
    evaluate (add p q) x = evaluate p x + evaluate q x := by
  induction p generalizing q with
  | nil => simp [add, evaluate]
  | cons a p ih =>
    cases q with
    | nil => simp [add, evaluate]
    | cons b q =>
      simp only [add, evaluate, ih, Nat.mul_add]
      ac_rfl

theorem add_comm (p q : Polynomial) : add p q = add q p := by
  induction p generalizing q with
  | nil => cases q <;> rfl
  | cons a p ih => cases q <;> simp [add, ih, Nat.add_comm]

theorem add_assoc (p q r : Polynomial) : add (add p q) r = add p (add q r) := by
  induction p generalizing q r with
  | nil => rfl
  | cons a p ih =>
    cases q <;> cases r <;> simp [add, ih, Nat.add_assoc]

theorem add_length (p q : Polynomial) : (add p q).length = max p.length q.length := by
  induction p generalizing q with
  | nil => simp [add]
  | cons a p ih => cases q <;> simp [add, ih, Nat.succ_max_succ]

end JonnyLean.Polynomials
