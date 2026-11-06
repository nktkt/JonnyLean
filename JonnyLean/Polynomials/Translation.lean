import JonnyLean.Polynomials.Equivalence

namespace JonnyLean.Polynomials

def translate (c : Nat) (p : Polynomial) : Polynomial := compose p [c,1]

theorem evaluate_translate (c : Nat) (p : Polynomial) (x : Nat) :
    evaluate (translate c p) x = evaluate p (x+c) := by
  simp [translate, evaluate_compose, evaluate, Nat.add_comm]

theorem translate_translate (c d : Nat) (p : Polynomial) :
    Equivalent (translate c (translate d p)) (translate (c+d) p) := by
  intro x
  simp only [evaluate_translate, Nat.add_assoc]

theorem translate_add (c : Nat) (p q : Polynomial) :
    Equivalent (translate c (add p q)) (add (translate c p) (translate c q)) := by
  intro x
  simp only [evaluate_translate, evaluate_add]

theorem translate_multiply (c : Nat) (p q : Polynomial) :
    Equivalent (translate c (multiply p q)) (multiply (translate c p) (translate c q)) := by
  intro x
  simp only [evaluate_translate, evaluate_multiply]

theorem translate_zero (p : Polynomial) : Equivalent (translate 0 p) p := by
  intro x
  simp [evaluate_translate]

end JonnyLean.Polynomials
