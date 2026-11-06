import JonnyLean.VerifiedPrograms.ExpressionSpecifications

namespace JonnyLean.Contracts.JL124

universe u v w
open JonnyLean.VerifiedPrograms
open JonnyLean.VerifiedPrograms.Specification

/-- Fixed, explicit semantic contract. Models are independently defined and bridged. -/
theorem contract :
    ∀ (env : Nat → Nat) (e : Expr), meaning env (folded e) = meaning env e := by
  intro env e
  simpa only [meaning_matches, folded_matches] using Expr.eval_foldConstants env e

theorem constant_product : folded (.mul (.lit 2) (.add (.lit 3) (.lit 4))) = .lit 14 := rfl

theorem open_expression : folded (.add (.var 0) (.lit 1)) = .add (.var 0) (.lit 1) := rfl

end JonnyLean.Contracts.JL124

#print axioms JonnyLean.VerifiedPrograms.Expr.eval_foldConstants
#print axioms JonnyLean.Contracts.JL124.contract
