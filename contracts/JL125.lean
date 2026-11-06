import JonnyLean.VerifiedPrograms.ExpressionSpecifications

namespace JonnyLean.Contracts.JL125

universe u v w
open JonnyLean.VerifiedPrograms
open JonnyLean.VerifiedPrograms.Specification

/-- Fixed, explicit semantic contract. Models are independently defined and bridged. -/
theorem contract :
    ∀ e : Expr, folded (folded e) = folded e := by
  intro e
  simpa only [folded_matches] using Expr.foldConstants_idempotent e

theorem literal_fixed : folded (.lit 0) = .lit 0 := rfl

theorem nested_fixed : folded (folded (.add (.lit 1) (.mul (.lit 2) (.lit 3)))) = .lit 7 := rfl

end JonnyLean.Contracts.JL125

#print axioms JonnyLean.VerifiedPrograms.Expr.foldConstants_idempotent
#print axioms JonnyLean.Contracts.JL125.contract
