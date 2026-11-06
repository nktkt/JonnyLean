import JonnyLean.VerifiedPrograms.ExpressionSpecifications

namespace JonnyLean.Contracts.JL126

universe u v w
open JonnyLean.VerifiedPrograms
open JonnyLean.VerifiedPrograms.Specification

/-- Fixed, explicit semantic contract. Models are independently defined and bridged. -/
theorem contract :
    ∀ e : Expr, syntaxSize (folded e) ≤ syntaxSize e := by
  intro e
  simpa only [syntaxSize_matches, folded_matches] using Expr.foldConstants_size e

theorem open_size : syntaxSize (folded (.add (.var 0) (.lit 1))) = 3 := rfl

theorem strict_reduction : syntaxSize (folded (.add (.lit 1) (.lit 2))) < syntaxSize (.add (.lit 1) (.lit 2)) := by decide

end JonnyLean.Contracts.JL126

#print axioms JonnyLean.VerifiedPrograms.Expr.foldConstants_size
#print axioms JonnyLean.Contracts.JL126.contract
