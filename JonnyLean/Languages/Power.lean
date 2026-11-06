import JonnyLean.Languages.Monoid
namespace JonnyLean.Languages

def power (L : Language α) : Nat → Language α
  | 0 => epsilon
  | n + 1 => concat L (power L n)

theorem power_zero (L : Language α) : power L 0 = epsilon := rfl
theorem power_one (L : Language α) : power L 1 = L := concat_epsilon L
theorem power_add (L : Language α) (m n : Nat) : power L (m + n) = concat (power L m) (power L n) := by
  induction m with
  | zero => simp [power, epsilon_concat]
  | succ m ih =>
    rw [Nat.succ_add, power, ih, power, concat_assoc]
theorem power_mono {L K : Language α} (h : Included L K) (n : Nat) :
    Included (power L n) (power K n) := by
  induction n with
  | zero => exact included_refl _
  | succ n ih => exact concat_mono h ih
theorem epsilon_power (n : Nat) : power (epsilon : Language α) n = epsilon := by
  induction n with
  | zero => rfl
  | succ n ih => simp [power, ih, epsilon_concat]
end JonnyLean.Languages
