import JonnyLean.Polynomials.Addition

namespace JonnyLean.Polynomials

def scale (c : Nat) (p : Polynomial) : Polynomial := p.map (fun a => c*a)

theorem evaluate_scale (c : Nat) (p : Polynomial) (x : Nat) :
    evaluate (scale c p) x = c*evaluate p x := by
  induction p with
  | nil => simp [scale, evaluate]
  | cons a p ih =>
    change c*a+x*evaluate (scale c p) x = c*(a+x*evaluate p x)
    rw [ih, Nat.mul_add]
    ac_rfl

theorem scale_scale (c d : Nat) (p : Polynomial) : scale c (scale d p) = scale (c*d) p := by
  simp [scale, List.map_map, Nat.mul_assoc]

theorem scale_one (p : Polynomial) : scale 1 p = p := by simp [scale]

theorem scale_add (c : Nat) (p q : Polynomial) : scale c (add p q) = add (scale c p) (scale c q) := by
  induction p generalizing q with
  | nil => rfl
  | cons a p ih =>
    cases q with
    | nil => rfl
    | cons b q =>
      change c*(a+b)::scale c (add p q) = (c*a+c*b)::add (scale c p) (scale c q)
      rw [Nat.mul_add, ih]

theorem scale_length (c : Nat) (p : Polynomial) : (scale c p).length = p.length := by simp [scale]

end JonnyLean.Polynomials
