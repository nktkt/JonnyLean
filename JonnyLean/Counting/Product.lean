import Init.Data.List.Lemmas
namespace JonnyLean.Counting

/-- Lists count occurrences, including repeated values. -/
def product (xs : List α) (ys : List β) : List (α × β) :=
  xs.flatMap (fun x => ys.map (fun y => (x, y)))

@[simp] theorem product_nil (ys : List β) : product ([] : List α) ys = [] := rfl
@[simp] theorem product_cons (x : α) (xs : List α) (ys : List β) :
    product (x :: xs) ys = ys.map (fun y => (x, y)) ++ product xs ys := rfl

theorem length_product (xs : List α) (ys : List β) :
    (product xs ys).length = xs.length * ys.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.add_mul, Nat.add_comm]

theorem mem_product {xs : List α} {ys : List β} {x : α} {y : β} :
    (x, y) ∈ product xs ys ↔ x ∈ xs ∧ y ∈ ys := by
  simp [product]

theorem product_append (xs zs : List α) (ys : List β) :
    product (xs ++ zs) ys = product xs ys ++ product zs ys := by
  simp [product]
end JonnyLean.Counting
