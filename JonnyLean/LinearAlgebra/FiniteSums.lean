import Std

namespace JonnyLean.LinearAlgebra

/-- Sum over exactly the finite indices `0,...,n-1`. -/
def sum : {n : Nat} → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => f 0 + sum (fun i : Fin n => f i.succ)

theorem sum_congr {n : Nat} (f g : Fin n → Nat) (h : ∀ i, f i = g i) : sum f = sum g := by
  have : f = g := funext h
  rw [this]

theorem sum_zero (n : Nat) : sum (fun _ : Fin n => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [sum] using ih

theorem sum_add {n : Nat} (f g : Fin n → Nat) :
    sum (fun i => f i + g i) = sum f + sum g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sum, ih]; omega

theorem sum_mul_left {n : Nat} (a : Nat) (f : Fin n → Nat) :
    sum (fun i => a * f i) = a * sum f := by
  induction n with
  | zero => simp [sum]
  | succ n ih => simp [sum, ih, Nat.mul_add]

theorem sum_mul_right {n : Nat} (f : Fin n → Nat) (a : Nat) :
    sum (fun i => f i * a) = sum f * a := by
  simpa only [Nat.mul_comm] using sum_mul_left a f

theorem sum_linear {n : Nat} (a b : Nat) (f g : Fin n → Nat) :
    sum (fun i => a * f i + b * g i) = a * sum f + b * sum g := by
  rw [sum_add, sum_mul_left, sum_mul_left]

theorem sum_swap {m n : Nat} (f : Fin m → Fin n → Nat) :
    sum (fun i => sum (f i)) = sum (fun j => sum (fun i => f i j)) := by
  induction m with
  | zero => simp [sum, sum_zero]
  | succ m ih => simp only [sum, sum_add, ih]

theorem sum_eq_zero_iff {n : Nat} (f : Fin n → Nat) :
    sum f = 0 ↔ ∀ i, f i = 0 := by
  induction n with
  | zero => simp [sum]
  | succ n ih =>
    simp only [sum, Nat.add_eq_zero_iff, ih]
    constructor
    · rintro ⟨h0, hs⟩ i
      exact Fin.cases h0 hs i
    · intro h
      exact ⟨h 0, fun i => h i.succ⟩

theorem sum_mono {n : Nat} (f g : Fin n → Nat) (h : ∀ i, f i ≤ g i) :
    sum f ≤ sum g := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih => exact Nat.add_le_add (h 0) (ih _ _ (fun i => h i.succ))

theorem sum_constant (n c : Nat) : sum (fun _ : Fin n => c) = n * c := by
  induction n with
  | zero => simp [sum]
  | succ n ih => simp [sum, ih, Nat.add_mul, Nat.add_comm]

/-- A finite coordinate selector. -/
def delta {n : Nat} (i j : Fin n) : Nat := if i = j then 1 else 0

theorem delta_symm {n : Nat} (i j : Fin n) : delta i j = delta j i := by
  simp [delta, eq_comm]

theorem sum_delta {n : Nat} (k : Fin n) (f : Fin n → Nat) :
    sum (fun i => delta k i * f i) = f k := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
    refine Fin.cases ?_ (fun k => ?_) k
    · simp [sum, delta, eq_comm, Fin.succ_ne_zero, sum_zero]
    · simpa [sum, delta, Fin.succ_ne_zero] using ih k (fun i => f i.succ)

theorem sum_delta_right {n : Nat} (k : Fin n) (f : Fin n → Nat) :
    sum (fun i => f i * delta i k) = f k := by
  simpa only [delta_symm, Nat.mul_comm] using sum_delta k f

end JonnyLean.LinearAlgebra
