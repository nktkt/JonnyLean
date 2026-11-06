import JonnyLean.Arithmetic.ProductDivisibility

open JonnyLean
open JonnyLean.Arithmetic

/- Independent expected proposition, unfolded definition, and boundary checks. -/
theorem contract_JL076 (d : Nat) (xs : List Nat)
    (h : ∀ a ∈ xs, d ∣ a) :
    d^xs.length * product (xs.map (fun a => a/d)) = product xs :=
  product_map_quotient d xs h

theorem contract_JL076_definition (d a : Nat) (xs : List Nat) : product ((a::xs).map (fun n => n/d)) = (a/d)*product (xs.map (fun n => n/d)) := rfl

theorem contract_JL076_boundary1 : product ([12,18].map (fun a => a/6)) = 6 := by decide

theorem contract_JL076_boundary2 : (0:Nat)^0*product (([] : List Nat).map (fun a => a/0)) = 1 := by decide

#print axioms JonnyLean.Arithmetic.product_map_quotient
#print axioms contract_JL076
