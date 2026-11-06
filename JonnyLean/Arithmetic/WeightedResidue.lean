import Std

namespace JonnyLean.Arithmetic

def weightedSum (w : α → Nat) : List α → Nat
  | [] => 0
  | a :: xs => w a + weightedSum w xs

theorem weightedSum_append (w : α → Nat) (xs ys : List α) :
    weightedSum w (xs++ys) = weightedSum w xs + weightedSum w ys := by
  induction xs with
  | nil => simp [weightedSum]
  | cons a xs ih => simp [weightedSum, ih, Nat.add_assoc]

theorem weightedSum_residue (m : Nat) (w v : α → Nat) (xs : List α)
    (h : ∀ a ∈ xs, w a % m = v a % m) :
    weightedSum w xs % m = weightedSum v xs % m := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [weightedSum, Nat.add_mod, Nat.mod_mod]
    rw [h a (by simp), ih (fun b hb => h b (List.mem_cons_of_mem a hb))]

theorem weightedSum_dvd (d : Nat) (w : α → Nat) (xs : List α)
    (h : ∀ a ∈ xs, d ∣ w a) : d ∣ weightedSum w xs := by
  induction xs with
  | nil => exact Nat.dvd_zero d
  | cons a xs ih =>
    exact Nat.dvd_add (h a (by simp)) (ih (fun b hb => h b (List.mem_cons_of_mem a hb)))

theorem weightedSum_linear (w v : α → Nat) (c d : Nat) (xs : List α) :
    weightedSum (fun a => c*w a+d*v a) xs = c*weightedSum w xs+d*weightedSum v xs := by
  induction xs with
  | nil => simp [weightedSum]
  | cons a xs ih =>
    simp only [weightedSum, ih, Nat.mul_add]
    ac_rfl

end JonnyLean.Arithmetic
