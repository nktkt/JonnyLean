import JonnyLean.Polynomials.Scalar
import JonnyLean.Arithmetic.WeightedResidue

namespace JonnyLean.Polynomials

def sumPolynomials : List Polynomial → Polynomial
  | [] => []
  | p::ps => add p (sumPolynomials ps)

theorem evaluate_sumPolynomials (ps : List Polynomial) (x : Nat) :
    evaluate (sumPolynomials ps) x = Arithmetic.weightedSum (fun p => evaluate p x) ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [sumPolynomials, evaluate_add, Arithmetic.weightedSum, ih]

theorem sumPolynomials_append (ps qs : List Polynomial) :
    sumPolynomials (ps++qs) = add (sumPolynomials ps) (sumPolynomials qs) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [sumPolynomials, ih, add_assoc]

theorem sumPolynomials_scale (c : Nat) (ps : List Polynomial) :
    sumPolynomials (ps.map (scale c)) = scale c (sumPolynomials ps) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [sumPolynomials, ih, scale_add]

theorem evaluate_sumPolynomials_dvd (d x : Nat) (ps : List Polynomial)
    (h : ∀ p ∈ ps, d ∣ evaluate p x) : d ∣ evaluate (sumPolynomials ps) x := by
  rw [evaluate_sumPolynomials]
  exact Arithmetic.weightedSum_dvd d _ ps h

end JonnyLean.Polynomials
