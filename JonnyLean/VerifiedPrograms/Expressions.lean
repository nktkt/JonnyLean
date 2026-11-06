import Std

namespace JonnyLean.VerifiedPrograms

inductive Expr where
  | lit (value : Nat)
  | var (name : Nat)
  | add (left right : Expr)
  | mul (left right : Expr)
  deriving Repr, DecidableEq

namespace Expr

def eval (env : Nat → Nat) : Expr → Nat
  | .lit n => n
  | .var x => env x
  | .add a b => eval env a + eval env b
  | .mul a b => eval env a * eval env b

def size : Expr → Nat
  | .lit _ | .var _ => 1
  | .add a b | .mul a b => size a + size b + 1

def variables : Expr → List Nat
  | .lit _ => []
  | .var x => [x]
  | .add a b | .mul a b => variables a ++ variables b

def rename (f : Nat → Nat) : Expr → Expr
  | .lit n => .lit n
  | .var x => .var (f x)
  | .add a b => .add (rename f a) (rename f b)
  | .mul a b => .mul (rename f a) (rename f b)

def subst (replacement : Nat → Expr) : Expr → Expr
  | .lit n => .lit n
  | .var x => replacement x
  | .add a b => .add (subst replacement a) (subst replacement b)
  | .mul a b => .mul (subst replacement a) (subst replacement b)

def constantAdd : Expr → Expr → Expr
  | .lit a, .lit b => .lit (a + b)
  | a, b => .add a b

def constantMul : Expr → Expr → Expr
  | .lit a, .lit b => .lit (a * b)
  | a, b => .mul a b

def foldConstants : Expr → Expr
  | .lit n => .lit n
  | .var x => .var x
  | .add a b => constantAdd (foldConstants a) (foldConstants b)
  | .mul a b => constantMul (foldConstants a) (foldConstants b)

def smartAdd (a b : Expr) : Expr :=
  if a = .lit 0 then b else if b = .lit 0 then a else constantAdd a b

def smartMul (a b : Expr) : Expr :=
  if a = .lit 0 ∨ b = .lit 0 then .lit 0
  else if a = .lit 1 then b else if b = .lit 1 then a else constantMul a b

def optimize : Expr → Expr
  | .lit n => .lit n
  | .var x => .var x
  | .add a b => smartAdd (optimize a) (optimize b)
  | .mul a b => smartMul (optimize a) (optimize b)

theorem eval_rename (f env : Nat → Nat) (e : Expr) :
    eval env (rename f e) = eval (env ∘ f) e := by
  induction e <;> simp_all [rename, eval]

theorem rename_identity (e : Expr) : rename id e = e := by
  induction e <;> simp_all [rename]

theorem rename_comp (f g : Nat → Nat) (e : Expr) :
    rename g (rename f e) = rename (g ∘ f) e := by
  induction e <;> simp_all [rename]

theorem eval_subst (replacement : Nat → Expr) (env : Nat → Nat) (e : Expr) :
    eval env (subst replacement e) = eval (fun x => eval env (replacement x)) e := by
  induction e <;> simp_all [subst, eval]

theorem subst_variables (e : Expr) : subst Expr.var e = e := by
  induction e <;> simp_all [subst]

theorem eval_congr_on_variables (env env' : Nat → Nat) (e : Expr)
    (h : ∀ x ∈ variables e, env x = env' x) : eval env e = eval env' e := by
  induction e with
  | lit n => rfl
  | var x => exact h x (by simp [variables])
  | add a b ha hb =>
    simp only [eval]
    rw [ha (fun x hx => h x (List.mem_append_left _ hx)),
      hb (fun x hx => h x (List.mem_append_right _ hx))]
  | mul a b ha hb =>
    simp only [eval]
    rw [ha (fun x hx => h x (List.mem_append_left _ hx)),
      hb (fun x hx => h x (List.mem_append_right _ hx))]

theorem eval_constantAdd (env : Nat → Nat) (a b : Expr) :
    eval env (constantAdd a b) = eval env a + eval env b := by
  cases a <;> cases b <;> rfl

theorem eval_constantMul (env : Nat → Nat) (a b : Expr) :
    eval env (constantMul a b) = eval env a * eval env b := by
  cases a <;> cases b <;> rfl

theorem eval_foldConstants (env : Nat → Nat) (e : Expr) :
    eval env (foldConstants e) = eval env e := by
  induction e with
  | lit n => rfl
  | var x => rfl
  | add a b ha hb => simp only [foldConstants, eval_constantAdd, ha, hb, eval]
  | mul a b ha hb => simp only [foldConstants, eval_constantMul, ha, hb, eval]

theorem foldConstants_constantAdd (a b : Expr)
    (ha : foldConstants a = a) (hb : foldConstants b = b) :
    foldConstants (constantAdd a b) = constantAdd a b := by
  cases a <;> cases b <;> simp_all [constantAdd, foldConstants]

theorem foldConstants_constantMul (a b : Expr)
    (ha : foldConstants a = a) (hb : foldConstants b = b) :
    foldConstants (constantMul a b) = constantMul a b := by
  cases a <;> cases b <;> simp_all [constantMul, foldConstants]

theorem foldConstants_idempotent (e : Expr) : foldConstants (foldConstants e) = foldConstants e := by
  induction e with
  | lit n => rfl
  | var x => rfl
  | add a b ha hb => exact foldConstants_constantAdd _ _ ha hb
  | mul a b ha hb => exact foldConstants_constantMul _ _ ha hb

theorem constantAdd_size (a b : Expr) : size (constantAdd a b) ≤ size a + size b + 1 := by
  cases a <;> cases b <;> simp [constantAdd, size]

theorem constantMul_size (a b : Expr) : size (constantMul a b) ≤ size a + size b + 1 := by
  cases a <;> cases b <;> simp [constantMul, size]

theorem foldConstants_size (e : Expr) : size (foldConstants e) ≤ size e := by
  induction e with
  | lit n => exact Nat.le_refl _
  | var x => exact Nat.le_refl _
  | add a b ha hb =>
    exact Nat.le_trans (constantAdd_size _ _) (by simp only [size]; omega)
  | mul a b ha hb =>
    exact Nat.le_trans (constantMul_size _ _) (by simp only [size]; omega)

theorem eval_smartAdd (env : Nat → Nat) (a b : Expr) :
    eval env (smartAdd a b) = eval env a + eval env b := by
  unfold smartAdd
  split
  · next h => subst a; simp [eval]
  · split
    · next h => subst b; simp [eval]
    · exact eval_constantAdd env a b

theorem eval_smartMul (env : Nat → Nat) (a b : Expr) :
    eval env (smartMul a b) = eval env a * eval env b := by
  unfold smartMul
  split
  · next h => rcases h with h | h <;> subst_vars <;> simp [eval]
  · split
    · next h => subst a; simp [eval]
    · split
      · next h => subst b; simp [eval]
      · exact eval_constantMul env a b

theorem eval_optimize (env : Nat → Nat) (e : Expr) : eval env (optimize e) = eval env e := by
  induction e with
  | lit n => rfl
  | var x => rfl
  | add a b ha hb => simp only [optimize, eval_smartAdd, ha, hb, eval]
  | mul a b ha hb => simp only [optimize, eval_smartMul, ha, hb, eval]

theorem constantAdd_variables (a b : Expr) : variables (constantAdd a b) = variables a ++ variables b := by
  cases a <;> cases b <;> rfl

theorem constantMul_variables (a b : Expr) : variables (constantMul a b) = variables a ++ variables b := by
  cases a <;> cases b <;> rfl

theorem foldConstants_variables (e : Expr) : variables (foldConstants e) = variables e := by
  induction e with
  | lit n => rfl
  | var x => rfl
  | add a b ha hb => simp only [foldConstants, constantAdd_variables, ha, hb, variables]
  | mul a b ha hb => simp only [foldConstants, constantMul_variables, ha, hb, variables]

theorem smartAdd_variables (a b : Expr) (x : Nat) (h : x ∈ variables (smartAdd a b)) :
    x ∈ variables a ++ variables b := by
  unfold smartAdd at h
  split at h
  · exact List.mem_append_right _ h
  · split at h
    · exact List.mem_append_left _ h
    · rwa [constantAdd_variables] at h

theorem smartMul_variables (a b : Expr) (x : Nat) (h : x ∈ variables (smartMul a b)) :
    x ∈ variables a ++ variables b := by
  unfold smartMul at h
  split at h
  · simp [variables] at h
  · split at h
    · exact List.mem_append_right _ h
    · split at h
      · exact List.mem_append_left _ h
      · rwa [constantMul_variables] at h

theorem optimize_variables (e : Expr) (x : Nat) : x ∈ variables (optimize e) → x ∈ variables e := by
  induction e with
  | lit n => exact id
  | var y => exact id
  | add a b ha hb =>
    intro h
    rcases List.mem_append.mp (smartAdd_variables _ _ x h) with h | h
    · exact List.mem_append_left _ (ha h)
    · exact List.mem_append_right _ (hb h)
  | mul a b ha hb =>
    intro h
    rcases List.mem_append.mp (smartMul_variables _ _ x h) with h | h
    · exact List.mem_append_left _ (ha h)
    · exact List.mem_append_right _ (hb h)

theorem rename_variables (f : Nat → Nat) (e : Expr) : variables (rename f e) = (variables e).map f := by
  induction e <;> simp_all [rename, variables]

theorem subst_comp (first second : Nat → Expr) (e : Expr) :
    subst second (subst first e) = subst (fun x => subst second (first x)) e := by
  induction e <;> simp_all [subst]

theorem rename_as_subst (f : Nat → Nat) (e : Expr) : rename f e = subst (fun x => .var (f x)) e := by
  induction e <;> simp_all [rename, subst]

end Expr
end JonnyLean.VerifiedPrograms
