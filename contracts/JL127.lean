import JonnyLean.VerifiedPrograms.ExpressionSpecifications

namespace JonnyLean.Contracts.JL127

universe u v w
open JonnyLean.VerifiedPrograms
open JonnyLean.VerifiedPrograms.Specification

/-- Fixed, explicit semantic contract. Models are independently defined and bridged. -/
theorem contract :
    ∀ (env : Nat → Nat) (e : Expr), meaning env (Expr.optimize e) = meaning env e := by
  intro env e
  simpa only [meaning_matches] using Expr.eval_optimize env e

theorem zero_annihilates : Expr.optimize (.mul (.lit 0) (.var 99)) = .lit 0 := rfl

theorem one_removed : Expr.optimize (.mul (.var 4) (.lit 1)) = .var 4 := rfl

end JonnyLean.Contracts.JL127

#print axioms JonnyLean.VerifiedPrograms.Expr.eval_optimize
#print axioms JonnyLean.Contracts.JL127.contract
