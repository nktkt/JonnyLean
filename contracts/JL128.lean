import JonnyLean.VerifiedPrograms.ExpressionSpecifications

namespace JonnyLean.Contracts.JL128

universe u v w
open JonnyLean.VerifiedPrograms
open JonnyLean.VerifiedPrograms.Specification

/-- Fixed, explicit semantic contract. Models are independently defined and bridged. -/
theorem contract :
    ∀ (e : Expr) (x : Nat), x ∈ names (Expr.optimize e) → x ∈ names e := by
  intro e x
  simpa only [names_matches] using Expr.optimize_variables e x

theorem variable_removed : names (Expr.optimize (.mul (.lit 0) (.var 99))) = [] := rfl

theorem variable_retained : names (Expr.optimize (.add (.lit 0) (.var 99))) = [99] := rfl

end JonnyLean.Contracts.JL128

#print axioms JonnyLean.VerifiedPrograms.Expr.optimize_variables
#print axioms JonnyLean.Contracts.JL128.contract
