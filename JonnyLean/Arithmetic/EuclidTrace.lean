import Std

namespace JonnyLean.Arithmetic

def euclidStep (s : Nat × Nat) : Nat × Nat :=
  if s.1 = 0 then s else (s.2 % s.1, s.1)

def euclidRun : Nat → Nat × Nat → Nat × Nat
  | 0, s => s
  | n+1, s => euclidRun n (euclidStep s)

theorem euclidStep_gcd (s : Nat × Nat) :
    Nat.gcd (euclidStep s).1 (euclidStep s).2 = Nat.gcd s.1 s.2 := by
  unfold euclidStep
  split
  · rfl
  · exact (Nat.gcd_rec _ _).symm

theorem euclidRun_gcd (n : Nat) (s : Nat × Nat) :
    Nat.gcd (euclidRun n s).1 (euclidRun n s).2 = Nat.gcd s.1 s.2 := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [euclidRun, ih, euclidStep_gcd]

theorem euclidRun_result (n : Nat) (s : Nat × Nat)
    (h : (euclidRun n s).1 = 0) : (euclidRun n s).2 = Nat.gcd s.1 s.2 := by
  have hg := euclidRun_gcd n s
  simpa [h] using hg

theorem euclidRun_zero (n b : Nat) : euclidRun n (0,b) = (0,b) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [euclidRun, euclidStep] using ih

theorem euclidStep_decreases (a b : Nat) (ha : 0 < a) :
    (euclidStep (a,b)).1 < a := by
  simpa [euclidStep, Nat.ne_of_gt ha] using Nat.mod_lt b ha

theorem euclidRun_terminates (n a b : Nat) (ha : a < n) :
    (euclidRun n (a,b)).1 = 0 := by
  induction n generalizing a b with
  | zero => exact False.elim (Nat.not_lt_zero a ha)
  | succ n ih =>
    by_cases hz : a = 0
    · subst a
      rw [euclidRun_zero]
    · have hp : 0 < a := Nat.pos_of_ne_zero hz
      have hr : b % a < n := Nat.lt_of_lt_of_le (Nat.mod_lt b hp) (Nat.le_of_lt_succ ha)
      simpa [euclidRun, euclidStep, hz] using ih (b % a) a hr

theorem euclidRun_computes (a b : Nat) :
    euclidRun (a+1) (a,b) = (0, Nat.gcd a b) := by
  have h := euclidRun_terminates (a+1) a b (Nat.lt_succ_self a)
  exact Prod.ext h (euclidRun_result (a+1) (a,b) h)

end JonnyLean.Arithmetic
