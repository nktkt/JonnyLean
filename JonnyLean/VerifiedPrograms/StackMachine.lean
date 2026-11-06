import JonnyLean.VerifiedPrograms.Expressions

namespace JonnyLean.VerifiedPrograms

inductive Instr where
  | push (value : Nat)
  | load (name : Nat)
  | add
  | mul
  deriving Repr, DecidableEq

namespace Machine

def run (literal variableValue : Nat → α) (plus times : α → α → α) :
    List Instr → List α → Option (List α)
  | [], stack => some stack
  | .push n :: code, stack => run literal variableValue plus times code (literal n :: stack)
  | .load x :: code, stack => run literal variableValue plus times code (variableValue x :: stack)
  | .add :: code, b :: a :: stack => run literal variableValue plus times code (plus a b :: stack)
  | .mul :: code, b :: a :: stack => run literal variableValue plus times code (times a b :: stack)
  | .add :: _, _ => none
  | .mul :: _, _ => none

def execute (env : Nat → Nat) (code : List Instr) (stack : List Nat) : Option (List Nat) :=
  run id env (· + ·) (· * ·) code stack

def decompile (code : List Instr) (stack : List Expr) : Option (List Expr) :=
  run Expr.lit Expr.var Expr.add Expr.mul code stack

def interpret (literal variableValue : Nat → α) (plus times : α → α → α) : Expr → α
  | .lit n => literal n
  | .var x => variableValue x
  | .add a b => plus (interpret literal variableValue plus times a) (interpret literal variableValue plus times b)
  | .mul a b => times (interpret literal variableValue plus times a) (interpret literal variableValue plus times b)

def compile : Expr → List Instr
  | .lit n => [.push n]
  | .var x => [.load x]
  | .add a b => compile a ++ compile b ++ [.add]
  | .mul a b => compile a ++ compile b ++ [.mul]

def compileInto : Expr → List Instr → List Instr
  | .lit n, tail => .push n :: tail
  | .var x, tail => .load x :: tail
  | .add a b, tail => compileInto a (compileInto b (.add :: tail))
  | .mul a b, tail => compileInto a (compileInto b (.mul :: tail))

/-- Reject underflow and otherwise compute the exact final stack depth. -/
def check : List Instr → Nat → Option Nat
  | [], depth => some depth
  | .push _ :: code, depth => check code (depth + 1)
  | .load _ :: code, depth => check code (depth + 1)
  | .add :: code, depth + 2 => check code (depth + 1)
  | .mul :: code, depth + 2 => check code (depth + 1)
  | .add :: _, _ => none
  | .mul :: _, _ => none

theorem run_append (literal variableValue : Nat → α) (plus times : α → α → α)
    (first second : List Instr) (stack : List α) :
    run literal variableValue plus times (first ++ second) stack =
      (run literal variableValue plus times first stack).bind (run literal variableValue plus times second) := by
  induction first generalizing stack with
  | nil => rfl
  | cons instr code ih =>
    cases instr with
    | push n => simpa only [List.cons_append, run] using ih (literal n :: stack)
    | load x => simpa only [List.cons_append, run] using ih (variableValue x :: stack)
    | add =>
      cases stack with
      | nil => rfl
      | cons b rest => cases rest with
        | nil => rfl
        | cons a stack => simpa only [List.cons_append, run] using ih (plus a b :: stack)
    | mul =>
      cases stack with
      | nil => rfl
      | cons b rest => cases rest with
        | nil => rfl
        | cons a stack => simpa only [List.cons_append, run] using ih (times a b :: stack)

theorem execute_append (env : Nat → Nat) (first second : List Instr) (stack : List Nat) :
    execute env (first ++ second) stack = (execute env first stack).bind (execute env second) :=
  run_append id env (· + ·) (· * ·) first second stack

theorem run_compile (literal variableValue : Nat → α) (plus times : α → α → α)
    (e : Expr) (stack : List α) :
    run literal variableValue plus times (compile e) stack =
      some (interpret literal variableValue plus times e :: stack) := by
  induction e generalizing stack with
  | lit n => rfl
  | var x => rfl
  | add a b ha hb => simp only [compile, run_append, ha, hb, Option.bind_some, run, interpret]
  | mul a b ha hb => simp only [compile, run_append, ha, hb, Option.bind_some, run, interpret]

theorem interpret_eval (env : Nat → Nat) (e : Expr) :
    interpret id env (· + ·) (· * ·) e = Expr.eval env e := by
  induction e <;> simp_all [interpret, Expr.eval]

theorem interpret_syntax (e : Expr) : interpret Expr.lit Expr.var Expr.add Expr.mul e = e := by
  induction e <;> simp_all [interpret]

theorem execute_compile (env : Nat → Nat) (e : Expr) (stack : List Nat) :
    execute env (compile e) stack = some (Expr.eval env e :: stack) := by
  simpa only [execute, interpret_eval] using run_compile id env (· + ·) (· * ·) e stack

theorem execute_compile_continuation (env : Nat → Nat) (e : Expr)
    (tail : List Instr) (stack : List Nat) :
    execute env (compile e ++ tail) stack = execute env tail (Expr.eval env e :: stack) := by
  rw [execute_append, execute_compile]
  rfl

theorem compile_length (e : Expr) : (compile e).length = Expr.size e := by
  induction e <;> simp_all [compile, Expr.size, Nat.add_assoc]

theorem run_check_sound (literal variableValue : Nat → α) (plus times : α → α → α)
    (code : List Instr) (stack : List α) (depth : Nat)
    (h : check code stack.length = some depth) :
    ∃ result, run literal variableValue plus times code stack = some result ∧ result.length = depth := by
  induction code generalizing stack depth with
  | nil => exact ⟨stack, rfl, Option.some.inj h⟩
  | cons instr code ih =>
    cases instr with
    | push n => exact ih (literal n :: stack) depth h
    | load x => exact ih (variableValue x :: stack) depth h
    | add =>
      cases stack with
      | nil => simp [check] at h
      | cons b rest => cases rest with
        | nil => simp [check] at h
        | cons a stack => exact ih (plus a b :: stack) depth h
    | mul =>
      cases stack with
      | nil => simp [check] at h
      | cons b rest => cases rest with
        | nil => simp [check] at h
        | cons a stack => exact ih (times a b :: stack) depth h

theorem check_sound (env : Nat → Nat) (code : List Instr) (stack : List Nat) (depth : Nat)
    (h : check code stack.length = some depth) :
    ∃ result, execute env code stack = some result ∧ result.length = depth :=
  run_check_sound id env (· + ·) (· * ·) code stack depth h

theorem check_append (first second : List Instr) (depth : Nat) :
    check (first ++ second) depth = (check first depth).bind (check second) := by
  induction first generalizing depth with
  | nil => rfl
  | cons instr code ih =>
    cases instr with
    | push n => exact ih (depth + 1)
    | load x => exact ih (depth + 1)
    | add =>
      cases depth with
      | zero => rfl
      | succ n => cases n with
        | zero => rfl
        | succ n => exact ih (n + 1)
    | mul =>
      cases depth with
      | zero => rfl
      | succ n => cases n with
        | zero => rfl
        | succ n => exact ih (n + 1)

theorem check_compile (e : Expr) (depth : Nat) : check (compile e) depth = some (depth + 1) := by
  induction e generalizing depth with
  | lit n => rfl
  | var x => rfl
  | add a b ha hb => simp only [compile, check_append, ha, hb, Option.bind_some, check]
  | mul a b ha hb => simp only [compile, check_append, ha, hb, Option.bind_some, check]

theorem execute_optimized_compile (env : Nat → Nat) (e : Expr) (stack : List Nat) :
    execute env (compile (Expr.optimize e)) stack = execute env (compile e) stack := by
  simp only [execute_compile, Expr.eval_optimize]

theorem compileInto_spec (e : Expr) (tail : List Instr) : compileInto e tail = compile e ++ tail := by
  induction e generalizing tail with
  | lit n => rfl
  | var x => rfl
  | add a b ha hb => simp only [compileInto, compile, ha, hb, List.append_assoc, List.singleton_append]
  | mul a b ha hb => simp only [compileInto, compile, ha, hb, List.append_assoc, List.singleton_append]

theorem execute_compileInto (env : Nat → Nat) (e : Expr) (tail : List Instr) (stack : List Nat) :
    execute env (compileInto e tail) stack = execute env tail (Expr.eval env e :: stack) := by
  rw [compileInto_spec, execute_compile_continuation]

theorem run_frame (literal variableValue : Nat → α) (plus times : α → α → α)
    (code : List Instr) (stack result suffix : List α)
    (h : run literal variableValue plus times code stack = some result) :
    run literal variableValue plus times code (stack ++ suffix) = some (result ++ suffix) := by
  induction code generalizing stack with
  | nil => have heq : stack = result := Option.some.inj h; subst stack; rfl
  | cons instr code ih =>
    cases instr with
    | push n => exact ih (literal n :: stack) h
    | load x => exact ih (variableValue x :: stack) h
    | add =>
      cases stack with
      | nil => simp [run] at h
      | cons b rest => cases rest with
        | nil => simp [run] at h
        | cons a stack => exact ih (plus a b :: stack) h
    | mul =>
      cases stack with
      | nil => simp [run] at h
      | cons b rest => cases rest with
        | nil => simp [run] at h
        | cons a stack => exact ih (times a b :: stack) h

theorem execute_frame (env : Nat → Nat) (code : List Instr) (stack result suffix : List Nat)
    (h : execute env code stack = some result) :
    execute env code (stack ++ suffix) = some (result ++ suffix) :=
  run_frame id env (· + ·) (· * ·) code stack result suffix h

theorem decompile_compile (e : Expr) (stack : List Expr) :
    decompile (compile e) stack = some (e :: stack) := by
  simpa only [decompile, interpret_syntax] using run_compile Expr.lit Expr.var Expr.add Expr.mul e stack

theorem run_map (literal variableValue : Nat → α) (plus times : α → α → α)
    (literal' variableValue' : Nat → β) (plus' times' : β → β → β) (f : α → β)
    (hl : ∀ n, f (literal n) = literal' n) (hv : ∀ x, f (variableValue x) = variableValue' x)
    (hp : ∀ a b, f (plus a b) = plus' (f a) (f b))
    (ht : ∀ a b, f (times a b) = times' (f a) (f b))
    (code : List Instr) (stack : List α) :
    (run literal variableValue plus times code stack).map (List.map f) =
      run literal' variableValue' plus' times' code (stack.map f) := by
  induction code generalizing stack with
  | nil => rfl
  | cons instr code ih =>
    cases instr with
    | push n => simpa only [run, List.map_cons, hl] using ih (literal n :: stack)
    | load x => simpa only [run, List.map_cons, hv] using ih (variableValue x :: stack)
    | add =>
      cases stack with
      | nil => rfl
      | cons b rest => cases rest with
        | nil => rfl
        | cons a stack => simpa only [run, List.map_cons, hp] using ih (plus a b :: stack)
    | mul =>
      cases stack with
      | nil => rfl
      | cons b rest => cases rest with
        | nil => rfl
        | cons a stack => simpa only [run, List.map_cons, ht] using ih (times a b :: stack)

theorem decompile_sound (env : Nat → Nat) (code : List Instr) (stack result : List Expr)
    (h : decompile code stack = some result) :
    execute env code (stack.map (Expr.eval env)) = some (result.map (Expr.eval env)) := by
  have hm := run_map Expr.lit Expr.var Expr.add Expr.mul id env (· + ·) (· * ·)
    (Expr.eval env) (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) code stack
  change (decompile code stack).map (List.map (Expr.eval env)) = execute env code (stack.map (Expr.eval env)) at hm
  rw [h] at hm
  exact hm.symm

end Machine
end JonnyLean.VerifiedPrograms
