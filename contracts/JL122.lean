import JonnyLean.VerifiedPrograms.ExpressionSpecifications

namespace JonnyLean.Contracts.JL122

universe u v w
open JonnyLean.VerifiedPrograms
open JonnyLean.VerifiedPrograms.Specification

/-- Fixed, explicit semantic contract. Models are independently defined and bridged. -/
theorem contract :
    ∀ (replacement : Nat → Expr) (env : Nat → Nat) (e : Expr), meaning env (substituted replacement e) = meaning (fun x => meaning env (replacement x)) e := by
  intro replacement env e
  simpa only [meaning_matches, substituted_matches] using Expr.eval_subst replacement env e

theorem constant_expression : substituted (fun _ => .lit 99) (.lit 4) = .lit 4 := rfl

theorem replace_variable : meaning id (substituted (fun x => .add (.var x) (.lit 1)) (.var 2)) = 3 := rfl

end JonnyLean.Contracts.JL122

#print axioms JonnyLean.VerifiedPrograms.Expr.eval_subst
#print axioms JonnyLean.Contracts.JL122.contract
