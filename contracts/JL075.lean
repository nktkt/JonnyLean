import JonnyLean.Arithmetic.ProductMap

open JonnyLean
open JonnyLean.Arithmetic

/- Independent expected proposition, unfolded definition, and boundary checks. -/
theorem contract_JL075 (f g : α → Nat) (xs : List α) :
    product (xs.map (fun a => f a*g a)) = product (xs.map f)*product (xs.map g) :=
  product_map_mul f g xs

theorem contract_JL075_definition (f : α → Nat) (a : α) (xs : List α) : product ((a::xs).map f) = f a*product (xs.map f) := rfl

theorem contract_JL075_boundary1 : product (([] : List Nat).map (fun n => n^0)) = 1 := by decide

theorem contract_JL075_boundary2 : product ([2,3].map (fun n => 5*n)) = 150 := by decide

#print axioms JonnyLean.Arithmetic.product_map_mul
#print axioms contract_JL075
