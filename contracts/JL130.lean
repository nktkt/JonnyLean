import JonnyLean.VerifiedPrograms.ExpressionSpecifications

namespace JonnyLean.Contracts.JL130

universe u v w
open JonnyLean.VerifiedPrograms
open JonnyLean.VerifiedPrograms.Specification

/-- Fixed, explicit semantic contract. Models are independently defined and bridged. -/
theorem contract :
    ∀ (first second : Nat → Expr) (e : Expr), substituted second (substituted first e) = substituted (fun x => substituted second (first x)) e := by
  intro first second e
  simpa only [substituted_matches] using Expr.subst_comp first second e

theorem literal_substitution : substituted (fun _ => .lit 2) (.lit 7) = .lit 7 := rfl

theorem nested_substitution : substituted (fun _ => .lit 9) (substituted (fun _ => .var 4) (.var 1)) = .lit 9 := rfl

end JonnyLean.Contracts.JL130

#print axioms JonnyLean.VerifiedPrograms.Expr.subst_comp
#print axioms JonnyLean.Contracts.JL130.contract
