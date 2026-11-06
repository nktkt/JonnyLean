import JonnyLean.Polynomials.Evaluation

namespace JonnyLean.Polynomials

def evaluateMod (m : Nat) : Polynomial → Nat → Nat
  | [], _ => 0
  | a::p, x => (a+x*evaluateMod m p x)%m

theorem evaluateMod_correct (m : Nat) (p : Polynomial) (x : Nat) :
    evaluateMod m p x = evaluate p x % m := by
  induction p with
  | nil => simp [evaluateMod, evaluate]
  | cons a p ih => simp [evaluateMod, evaluate, ih, Nat.add_mod, Nat.mul_mod]

theorem evaluate_congruent (m : Nat) (p : Polynomial) (x y : Nat) (h : x%m = y%m) :
    evaluate p x % m = evaluate p y % m := by
  induction p with
  | nil => rfl
  | cons a p ih => simp [evaluate, Nat.add_mod, Nat.mul_mod, h, ih]

theorem evaluate_coefficients_mod (m : Nat) (p : Polynomial) (x : Nat) :
    evaluate (p.map (fun a => a%m)) x % m = evaluate p x % m := by
  induction p with
  | nil => rfl
  | cons a p ih => simp [evaluate, Nat.add_mod, Nat.mul_mod, ih]

/-- Reduce every coefficient and replace the input by a congruent value without
changing the evaluated residue. Both transformations are allowed simultaneously. -/
theorem evaluate_normalized_congruent (m : Nat) (p : Polynomial) (x y : Nat)
    (h : x % m = y % m) :
    evaluate (p.map (fun a => a % m)) x % m = evaluate p y % m := by
  calc
    evaluate (p.map (fun a => a % m)) x % m = evaluate p x % m :=
      evaluate_coefficients_mod m p x
    _ = evaluate p y % m := evaluate_congruent m p x y h

theorem evaluateMod_bound (m : Nat) (p : Polynomial) (x : Nat) (hm : 0 < m) :
    evaluateMod m p x < m := by rw [evaluateMod_correct]; exact Nat.mod_lt _ hm

theorem evaluateMod_input (m : Nat) (p : Polynomial) (x : Nat) :
    evaluateMod m p (x%m) = evaluateMod m p x := by
  rw [evaluateMod_correct, evaluateMod_correct]
  exact evaluate_congruent m p _ x (Nat.mod_mod x m)

end JonnyLean.Polynomials
