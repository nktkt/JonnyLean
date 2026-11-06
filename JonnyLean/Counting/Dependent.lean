import JonnyLean.Counting.Product
import JonnyLean.DiscreteProbability.Mass
namespace JonnyLean.Counting
open DiscreteProbability

def fibers (xs : List α) (choices : α → List β) : List (α × β) :=
  xs.flatMap (fun x => (choices x).map (fun y => (x, y)))

theorem mass_map (w : β → Nat) (f : α → β) (xs : List α) :
    mass w (xs.map f) = mass (fun x => w (f x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [mass, ih]

theorem mass_flatMap (w : β → Nat) (f : α → List β) (xs : List α) :
    mass w (xs.flatMap f) = mass (fun x => mass w (f x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [mass, mass_append, ih]

theorem length_fibers (xs : List α) (choices : α → List β) :
    (fibers xs choices).length = mass (fun x => (choices x).length) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [fibers, mass, ← ih]

theorem mem_fibers {xs : List α} {choices : α → List β} {x : α} {y : β} :
    (x, y) ∈ fibers xs choices ↔ x ∈ xs ∧ y ∈ choices x := by simp [fibers]

theorem fibers_constant (xs : List α) (ys : List β) : fibers xs (fun _ => ys) = product xs ys := rfl
end JonnyLean.Counting
