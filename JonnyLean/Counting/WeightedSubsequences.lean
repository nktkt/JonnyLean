import JonnyLean.Counting.Subsequences
import JonnyLean.Counting.Choices
namespace JonnyLean.Counting
open DiscreteProbability

def wordWeight (w : α → Nat) (xs : List α) : Nat := natProduct (xs.map w)

theorem mass_scale_left (c : Nat) (w : α → Nat) (xs : List α) :
    mass (fun a => c * w a) xs = c * mass w xs := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih => simp [mass, ih, Nat.mul_add]

theorem mass_add_weights (w v : α → Nat) (xs : List α) :
    mass (fun a => w a + v a) xs = mass w xs + mass v xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [mass, ih, Nat.add_assoc, Nat.add_left_comm]

theorem weighted_subsequences (w : α → Nat) (xs : List α) :
    mass (wordWeight w) (subsequences xs) = wordWeight (fun a => 1 + w a) xs := by
  induction xs with
  | nil => simp [subsequences, mass, wordWeight, natProduct]
  | cons a xs ih =>
    rw [subsequences, mass_append, mass_map]
    change mass (wordWeight w) (subsequences xs) +
      mass (fun ys => w a * wordWeight w ys) (subsequences xs) = _
    rw [mass_scale_left, ih]
    simp [wordWeight, natProduct, Nat.add_mul]

theorem wordWeight_append (w : α → Nat) (xs ys : List α) :
    wordWeight w (xs ++ ys) = wordWeight w xs * wordWeight w ys := by
  induction xs with
  | nil => simp [wordWeight, natProduct]
  | cons a xs ih => simpa [wordWeight, natProduct, Nat.mul_assoc] using congrArg (fun n => w a * n) ih
end JonnyLean.Counting
