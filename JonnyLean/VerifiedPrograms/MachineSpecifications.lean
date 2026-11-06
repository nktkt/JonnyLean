import JonnyLean.VerifiedPrograms.StackMachine
import JonnyLean.VerifiedPrograms.ExpressionSpecifications

/-! Fixed independent mathematical models and checked bridges for the task contracts. -/

namespace JonnyLean.VerifiedPrograms.Specification

def instruction (env : Nat → Nat) : Instr → List Nat → Option (List Nat)
  | .push n, s => some (n :: s)
  | .load x, s => some (env x :: s)
  | .add, b :: a :: s => some ((a + b) :: s)
  | .mul, b :: a :: s => some ((a * b) :: s)
  | .add, _ => none
  | .mul, _ => none

def execution (env : Nat → Nat) : List Instr → List Nat → Option (List Nat)
  | [], s => some s
  | i :: code, s => (instruction env i s).bind (execution env code)

def bytecode : Expr → List Instr
  | .lit n => [.push n]
  | .var x => [.load x]
  | .add a b => bytecode a ++ bytecode b ++ [.add]
  | .mul a b => bytecode a ++ bytecode b ++ [.mul]

def abstractInstruction : Instr → Nat → Option Nat
  | .push _, n | .load _, n => some (n + 1)
  | .add, n + 2 | .mul, n + 2 => some (n + 1)
  | .add, _ | .mul, _ => none

def verifiedDepth : List Instr → Nat → Option Nat
  | [], n => some n
  | i :: code, n => (abstractInstruction i n).bind (verifiedDepth code)

def syntaxInstruction : Instr → List Expr → Option (List Expr)
  | .push n, s => some (.lit n :: s)
  | .load x, s => some (.var x :: s)
  | .add, b :: a :: s => some (.add a b :: s)
  | .mul, b :: a :: s => some (.mul a b :: s)
  | .add, _ => none
  | .mul, _ => none

def reconstruction : List Instr → List Expr → Option (List Expr)
  | [], s => some s
  | i :: code, s => (syntaxInstruction i s).bind (reconstruction code)

theorem execution_matches (env : Nat → Nat) (code : List Instr) (stack : List Nat) :
    execution env code stack = Machine.execute env code stack := by
  induction code generalizing stack with
  | nil => rfl
  | cons instr code ih =>
    cases instr with
    | push n => exact ih (n :: stack)
    | load x => exact ih (env x :: stack)
    | add =>
      cases stack with
      | nil => rfl
      | cons b rest => cases rest with
        | nil => rfl
        | cons a stack => exact ih ((a + b) :: stack)
    | mul =>
      cases stack with
      | nil => rfl
      | cons b rest => cases rest with
        | nil => rfl
        | cons a stack => exact ih ((a * b) :: stack)

theorem bytecode_matches (e : Expr) : bytecode e = Machine.compile e := by
  induction e <;> simp_all [bytecode, Machine.compile]

theorem verifiedDepth_matches (code : List Instr) (n : Nat) : verifiedDepth code n = Machine.check code n := by
  induction code generalizing n with
  | nil => rfl
  | cons instr code ih =>
    cases instr with
    | push k => exact ih (n + 1)
    | load x => exact ih (n + 1)
    | add =>
      cases n with
      | zero => rfl
      | succ n => cases n with
        | zero => rfl
        | succ n => exact ih (n + 1)
    | mul =>
      cases n with
      | zero => rfl
      | succ n => cases n with
        | zero => rfl
        | succ n => exact ih (n + 1)

theorem reconstruction_matches (code : List Instr) (stack : List Expr) :
    reconstruction code stack = Machine.decompile code stack := by
  induction code generalizing stack with
  | nil => rfl
  | cons instr code ih =>
    cases instr with
    | push n => exact ih (.lit n :: stack)
    | load x => exact ih (.var x :: stack)
    | add =>
      cases stack with
      | nil => rfl
      | cons b rest => cases rest with
        | nil => rfl
        | cons a stack => exact ih (.add a b :: stack)
    | mul =>
      cases stack with
      | nil => rfl
      | cons b rest => cases rest with
        | nil => rfl
        | cons a stack => exact ih (.mul a b :: stack)

end JonnyLean.VerifiedPrograms.Specification
