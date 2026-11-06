import JonnyLean.Algebra.GeometricSum

namespace JonnyLean

/-- Natural affine maps; composition is represented by its two coefficients. -/
structure NatAffine where
  slope : Nat
  offset : Nat
  deriving DecidableEq

namespace NatAffine

def eval (f : NatAffine) (x : Nat) : Nat := f.slope * x + f.offset

def identity : NatAffine := ⟨1, 0⟩

def compose (f g : NatAffine) : NatAffine :=
  ⟨f.slope * g.slope, f.slope * g.offset + f.offset⟩

def iterate (f : NatAffine) : Nat → NatAffine
  | 0 => identity
  | n + 1 => compose f (iterate f n)

theorem eval_compose (f g : NatAffine) (x : Nat) :
    (compose f g).eval x = f.eval (g.eval x) := by
  simp only [eval, compose, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

theorem compose_assoc (f g h : NatAffine) :
    compose (compose f g) h = compose f (compose g h) := by
  cases f; cases g; cases h
  simp only [compose, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

theorem identity_left (f : NatAffine) : compose identity f = f := by
  cases f
  simp [identity, compose]

theorem identity_right (f : NatAffine) : compose f identity = f := by
  cases f
  simp [identity, compose]

theorem eval_ext (f g : NatAffine) (h : ∀ x, f.eval x = g.eval x) : f = g := by
  have hzero := h 0
  have hone := h 1
  simp only [eval, Nat.mul_zero, Nat.zero_add] at hzero
  simp only [eval, Nat.mul_one] at hone
  have hslope : f.slope = g.slope := by omega
  cases f; cases g
  simp_all

theorem iterate_coefficients (f : NatAffine) (n : Nat) :
    (iterate f n).slope = f.slope ^ n ∧
    (iterate f n).offset = f.offset * geometricSum f.slope n := by
  induction n with
  | zero => simp [iterate, identity, geometricSum, rangeSum]
  | succ n ih =>
    simp only [iterate, compose]
    constructor
    · rw [ih.1, Nat.pow_succ, Nat.mul_comm]
    · rw [ih.2, geometric_sum_recurrence, Nat.mul_add, Nat.mul_one]
      ac_rfl

theorem iterate_formula (f : NatAffine) (n x : Nat) :
    (iterate f n).eval x = f.slope ^ n * x + f.offset * geometricSum f.slope n := by
  unfold eval
  rw [(iterate_coefficients f n).1, (iterate_coefficients f n).2]

theorem iterate_add (f : NatAffine) (m n : Nat) :
    iterate f (m + n) = compose (iterate f m) (iterate f n) := by
  induction m with
  | zero => simp only [Nat.zero_add, iterate, identity_left]
  | succ m ih =>
    rw [Nat.succ_add]
    simp only [iterate, ih, compose_assoc]

end NatAffine
end JonnyLean
