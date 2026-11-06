import JonnyLean.RegularExpressions.Syntax

namespace JonnyLean.RegularExpressions
open JonnyLean.Languages

def smartAlt (r s : Regex α) : Regex α :=
  match r,s with
  | .zero,s => s
  | r,.zero => r
  | r,s => .alt r s

def smartSeq (r s : Regex α) : Regex α :=
  match r,s with
  | .zero,_ => .zero
  | _,.zero => .zero
  | .eps,s => s
  | r,.eps => r
  | r,s => .seq r s

def smartStar (r : Regex α) : Regex α :=
  match r with
  | .zero => .eps
  | .eps => .eps
  | .star s => .star s
  | r => .star r

theorem smartAlt_correct (r s : Regex α) (w : List α) :
    denotes (smartAlt r s) w ↔ denotes r w ∨ denotes s w := by
  cases r <;> cases s <;> simp [smartAlt, denotes, union, empty]

theorem smartSeq_correct (r s : Regex α) :
    denotes (smartSeq r s) = concat (denotes r) (denotes s) := by
  cases r <;> cases s <;>
    simp [smartSeq, denotes, empty_concat, concat_empty, epsilon_concat, concat_epsilon]

theorem star_epsilon : Star (epsilon : Language α) = epsilon := by
  apply included_antisymm
  · intro w h
    induction h with
    | nil => rfl
    | @step u v hu hv ih =>
      change u = [] at hu
      simpa [hu] using ih
  · intro w h; cases h; exact Star.nil

theorem smartStar_correct (r : Regex α) : denotes (smartStar r) = Star (denotes r) := by
  cases r <;> simp [smartStar, denotes, star_empty, star_epsilon, star_idempotent]

theorem smartAlt_zero_right (r : Regex α) : smartAlt r .zero = r := by
  cases r <;> rfl

theorem smartSeq_eps_right (r : Regex α) : smartSeq r .eps = r := by
  cases r <;> rfl

theorem smartStar_idempotent (r : Regex α) : smartStar (smartStar r) = smartStar r := by
  cases r <;> rfl

end JonnyLean.RegularExpressions
