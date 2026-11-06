import JonnyLean.VerifiedPrograms.ExpressionSpecifications

namespace JonnyLean.Contracts.JL123

universe u v w
open JonnyLean.VerifiedPrograms
open JonnyLean.VerifiedPrograms.Specification

/-- Fixed, explicit semantic contract. Models are independently defined and bridged. -/
theorem contract :
    ∀ (env env' : Nat → Nat) (e : Expr), (∀ x ∈ names e, env x = env' x) → meaning env e = meaning env' e := by
  intro env env' e h
  rw [meaning_matches, meaning_matches]
  apply Expr.eval_congr_on_variables env env' e
  simpa only [names_matches] using h

theorem closed_expression : names (.mul (.lit 2) (.lit 3)) = [] := rfl

theorem repeated_name : names (.add (.var 5) (.var 5)) = [5, 5] := rfl

end JonnyLean.Contracts.JL123

#print axioms JonnyLean.VerifiedPrograms.Expr.eval_congr_on_variables
#print axioms JonnyLean.Contracts.JL123.contract
