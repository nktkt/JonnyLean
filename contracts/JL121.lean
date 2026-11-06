import JonnyLean.VerifiedPrograms.ExpressionSpecifications

namespace JonnyLean.Contracts.JL121

universe u v w
open JonnyLean.VerifiedPrograms
open JonnyLean.VerifiedPrograms.Specification

/-- Fixed, explicit semantic contract. Models are independently defined and bridged. -/
theorem contract :
    ∀ (f env : Nat → Nat) (e : Expr), meaning env (renamed f e) = meaning (env ∘ f) e := by
  intro f env e
  simpa only [meaning_matches, renamed_matches] using Expr.eval_rename f env e

theorem literal_unchanged : renamed Nat.succ (.lit 7) = .lit 7 := rfl

theorem merged_variables : meaning id (renamed (fun _ => 3) (.add (.var 0) (.var 1))) = 6 := rfl

end JonnyLean.Contracts.JL121

#print axioms JonnyLean.VerifiedPrograms.Expr.eval_rename
#print axioms JonnyLean.Contracts.JL121.contract
