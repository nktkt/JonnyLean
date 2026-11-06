import JonnyLean.VerifiedPrograms.Expressions

/-! Fixed independent mathematical models and checked bridges for the task contracts. -/

namespace JonnyLean.VerifiedPrograms.Specification

def meaning (env : Nat → Nat) : Expr → Nat
  | .lit n => n
  | .var x => env x
  | .add a b => meaning env a + meaning env b
  | .mul a b => meaning env a * meaning env b

def syntaxSize : Expr → Nat
  | .lit _ | .var _ => 1
  | .add a b | .mul a b => 1 + syntaxSize a + syntaxSize b

def names : Expr → List Nat
  | .lit _ => []
  | .var x => [x]
  | .add a b | .mul a b => names a ++ names b

def renamed (f : Nat → Nat) : Expr → Expr
  | .lit n => .lit n
  | .var x => .var (f x)
  | .add a b => .add (renamed f a) (renamed f b)
  | .mul a b => .mul (renamed f a) (renamed f b)

def substituted (replacement : Nat → Expr) : Expr → Expr
  | .lit n => .lit n
  | .var x => replacement x
  | .add a b => .add (substituted replacement a) (substituted replacement b)
  | .mul a b => .mul (substituted replacement a) (substituted replacement b)

def folded : Expr → Expr
  | .lit n => .lit n
  | .var x => .var x
  | .add a b =>
    match folded a, folded b with
    | .lit n, .lit m => .lit (n + m)
    | a', b' => .add a' b'
  | .mul a b =>
    match folded a, folded b with
    | .lit n, .lit m => .lit (n * m)
    | a', b' => .mul a' b'

theorem meaning_matches (env : Nat → Nat) (e : Expr) : meaning env e = Expr.eval env e := by
  induction e <;> simp_all [meaning, Expr.eval]

theorem syntaxSize_matches (e : Expr) : syntaxSize e = Expr.size e := by
  induction e <;> simp_all [syntaxSize, Expr.size] <;> omega

theorem names_matches (e : Expr) : names e = Expr.variables e := by
  induction e <;> simp_all [names, Expr.variables]

theorem renamed_matches (f : Nat → Nat) (e : Expr) : renamed f e = Expr.rename f e := by
  induction e <;> simp_all [renamed, Expr.rename]

theorem substituted_matches (replacement : Nat → Expr) (e : Expr) : substituted replacement e = Expr.subst replacement e := by
  induction e <;> simp_all [substituted, Expr.subst]

theorem folded_matches (e : Expr) : folded e = Expr.foldConstants e := by
  induction e with
  | lit n => rfl
  | var x => rfl
  | add a b ha hb => simp only [folded, Expr.foldConstants, ha, hb]; rfl
  | mul a b ha hb => simp only [folded, Expr.foldConstants, ha, hb]; rfl

end JonnyLean.VerifiedPrograms.Specification
