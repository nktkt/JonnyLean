import JonnyLean.Polynomials.Congruence

open JonnyLean.Polynomials

/- The expected proposition explicitly names both coefficient reduction and input congruence. -/
theorem contract_JL089 (m : Nat) (p : List Nat) (x y : Nat)
    (h : x % m = y % m) :
    evaluate (p.map (fun a => a % m)) x % m = evaluate p y % m :=
  evaluate_normalized_congruent m p x y h

theorem contract_JL089_definition (m a x : Nat) (p : List Nat) :
    evaluate ((a::p).map (fun c => c % m)) x =
      a % m + x * evaluate (p.map (fun c => c % m)) x := rfl

theorem contract_JL089_horner_definition (m a x : Nat) (p : List Nat) :
    evaluateMod m (a::p) x = (a + x * evaluateMod m p x) % m := rfl

theorem contract_JL089_boundary1 :
    evaluate ([3,2,1].map (fun a => a % 0)) 10 % 0 = 123 := by decide

theorem contract_JL089_boundary2 :
    evaluate ([10,9,8].map (fun a => a % 7)) 10 % 7 = evaluate [10,9,8] 3 % 7 := by decide

theorem contract_JL089_empty (m x y : Nat) :
    evaluate (([] : List Nat).map (fun a => a % m)) x % m = evaluate [] y % m := rfl

#print axioms JonnyLean.Polynomials.evaluate_normalized_congruent
#print axioms contract_JL089
