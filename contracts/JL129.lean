import JonnyLean.VerifiedPrograms.ExpressionSpecifications

namespace JonnyLean.Contracts.JL129

universe u v w
open JonnyLean.VerifiedPrograms
open JonnyLean.VerifiedPrograms.Specification

/-- Fixed, explicit semantic contract. Models are independently defined and bridged. -/
theorem contract :
    ∀ (f : Nat → Nat) (e : Expr), names (renamed f e) = (names e).map f := by
  intro f e
  simpa only [names_matches, renamed_matches] using Expr.rename_variables f e

theorem no_names : names (renamed Nat.succ (.lit 5)) = [] := rfl

theorem duplicates_preserved : names (renamed (fun _ => 0) (.add (.var 2) (.var 3))) = [0, 0] := rfl

end JonnyLean.Contracts.JL129

#print axioms JonnyLean.VerifiedPrograms.Expr.rename_variables
#print axioms JonnyLean.Contracts.JL129.contract
