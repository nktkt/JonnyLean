import JonnyLean.Counting.Product
namespace JonnyLean.Counting

theorem filter_false_list (xs : List α) : xs.filter (fun _ => false) = [] := by
  induction xs with
  | nil => rfl
  | cons a xs ih => exact ih

theorem filter_product (p : α → Bool) (q : β → Bool) (xs : List α) (ys : List β) :
    (product xs ys).filter (fun z => p z.1 && q z.2) = product (xs.filter p) (ys.filter q) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [product_cons, List.filter_append, ih]
    cases hp : p x <;> simp [List.filter_map, Function.comp_def, hp, product, filter_false_list]

theorem length_filter_product (p : α → Bool) (q : β → Bool) (xs : List α) (ys : List β) :
    ((product xs ys).filter (fun z => p z.1 && q z.2)).length =
      (xs.filter p).length * (ys.filter q).length := by
  rw [filter_product, length_product]

theorem filter_product_left (p : α → Bool) (xs : List α) (ys : List β) :
    (product xs ys).filter (fun z => p z.1) = product (xs.filter p) ys := by
  have ht : ys.filter (fun _ => true) = ys := List.filter_eq_self.mpr (by simp)
  simpa [ht] using filter_product p (fun _ => true) xs ys
end JonnyLean.Counting
