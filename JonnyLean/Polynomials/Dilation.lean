import JonnyLean.Polynomials.Equivalence

namespace JonnyLean.Polynomials

def dilate (c : Nat) : Polynomial → Polynomial
  | [] => []
  | a::p => a :: scale c (dilate c p)

theorem evaluate_dilate (c : Nat) (p : Polynomial) (x : Nat) :
    evaluate (dilate c p) x = evaluate p (c*x) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [dilate, evaluate, evaluate_scale, ih]
    ac_rfl

theorem dilate_dilate (c d : Nat) (p : Polynomial) :
    Equivalent (dilate c (dilate d p)) (dilate (c*d) p) := by
  intro x
  simp only [evaluate_dilate]
  congr 1
  ac_rfl

theorem dilate_length (c : Nat) (p : Polynomial) : (dilate c p).length = p.length := by
  induction p with
  | nil => rfl
  | cons a p ih => simp [dilate, scale_length, ih]

theorem dilate_one (p : Polynomial) : dilate 1 p = p := by
  induction p with
  | nil => rfl
  | cons a p ih => simp [dilate, scale_one, ih]

theorem dilate_scale (c d : Nat) (p : Polynomial) :
    Equivalent (dilate c (scale d p)) (scale d (dilate c p)) := by
  intro x
  simp only [evaluate_dilate, evaluate_scale]

end JonnyLean.Polynomials
