import JonnyLean.Imperative.Hoare

namespace JonnyLean.Imperative

def Equivalent (c d : Cmd) : Prop := ∀ s t, Exec c s t ↔ Exec d s t

theorem equivalent_refl (c : Cmd) : Equivalent c c := fun _ _ => Iff.rfl

theorem equivalent_symm (h : Equivalent c d) : Equivalent d c := fun s t => (h s t).symm

theorem equivalent_trans (h : Equivalent c d) (k : Equivalent d e) : Equivalent c e :=
  fun s t => (h s t).trans (k s t)

theorem equivalent_seq (h : Equivalent a a') (k : Equivalent b b') :
    Equivalent (.seq a b) (.seq a' b') := by
  intro s t
  simp only [exec_seq_iff]
  exact exists_congr (fun u => and_congr (h s u) (k u t))

theorem equivalent_if (b : BExp) (h : Equivalent c c') (k : Equivalent d d') :
    Equivalent (.ite b c d) (.ite b c' d') := by
  intro s t
  constructor <;> intro he
  · cases he with
    | ifTrue hb he => exact .ifTrue hb ((h s t).mp he)
    | ifFalse hb he => exact .ifFalse hb ((k s t).mp he)
  · cases he with
    | ifTrue hb he => exact .ifTrue hb ((h s t).mpr he)
    | ifFalse hb he => exact .ifFalse hb ((k s t).mpr he)

theorem exec_while_replace (h : Equivalent c d) (he : Exec (.while b c) s t) :
    Exec (.while b d) s t := by
  generalize hw : Cmd.while b c = w at he
  induction he with
  | skip => cases hw
  | assign => cases hw
  | seq => cases hw
  | ifTrue => cases hw
  | ifFalse => cases hw
  | whileFalse hb => cases hw; exact .whileFalse hb
  | whileTrue hb hc hw' _ ih =>
    cases hw
    exact .whileTrue hb ((h _ _).mp hc) (ih rfl)

theorem equivalent_while (b : BExp) (h : Equivalent c d) :
    Equivalent (.while b c) (.while b d) :=
  fun _ _ => ⟨exec_while_replace h, exec_while_replace (equivalent_symm h)⟩

theorem skip_left (c : Cmd) : Equivalent (.seq .skip c) c := by
  intro s t
  constructor
  · intro h; cases h with | seq h₁ h₂ => cases h₁; exact h₂
  · intro h; exact .seq (.skip _) h

theorem skip_right (c : Cmd) : Equivalent (.seq c .skip) c := by
  intro s t
  constructor
  · intro h; cases h with | seq h₁ h₂ => cases h₂; exact h₁
  · intro h; exact .seq h (.skip _)

theorem sequence_identities (c : Cmd) : Equivalent (.seq .skip c) c ∧ Equivalent (.seq c .skip) c :=
  ⟨skip_left c, skip_right c⟩

theorem constant_branch (b : Bool) (c d : Cmd) :
    Equivalent (.ite (.truth b) c d) (if b then c else d) := by
  intro s t
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · constructor
    · intro h; cases h with
      | ifTrue hb _ => simp [BExp.eval] at hb
      | ifFalse _ h => exact h
    · exact fun h => .ifFalse rfl h
  · constructor
    · intro h; cases h with
      | ifTrue _ h => exact h
      | ifFalse hb _ => simp [BExp.eval] at hb
    · exact fun h => .ifTrue rfl h

theorem false_loop (c : Cmd) : Equivalent (.while (.truth false) c) .skip := by
  intro s t
  constructor
  · intro h
    cases h with
    | whileFalse => exact .skip _
    | whileTrue hb _ _ => simp [BExp.eval] at hb
  · intro h; cases h; exact .whileFalse rfl

theorem assignment_fusion (x : Nat) (a b : AExp) :
    Equivalent (.seq (.assign x a) (.assign x b)) (.assign x (AExp.subst x a b)) := by
  intro s t
  constructor
  · intro h
    cases h with
    | seq ha hb =>
      cases ha; cases hb
      rw [update_shadow, ← AExp.eval_subst]
      exact .assign _ _ _
  · intro h
    cases h
    rw [AExp.eval_subst, ← update_shadow s x (a.eval s)]
    exact .seq (.assign _ _ _) (.assign _ _ _)

def smartSeq (c d : Cmd) : Cmd :=
  match c, d with
  | .skip, d => d
  | c, .skip => c
  | c, d => .seq c d

def smartIf (b : BExp) (c d : Cmd) : Cmd :=
  match b with
  | .truth v => if v then c else d
  | b => .ite b c d

def smartWhile (b : BExp) (c : Cmd) : Cmd :=
  match b with
  | .truth false => .skip
  | b => .while b c

def optimize : Cmd → Cmd
  | .skip => .skip
  | .assign x a => .assign x a
  | .seq c d => smartSeq (optimize c) (optimize d)
  | .ite b c d => smartIf b (optimize c) (optimize d)
  | .while b c => smartWhile b (optimize c)

theorem smartSeq_correct (c d : Cmd) : Equivalent (.seq c d) (smartSeq c d) := by
  cases c <;> cases d <;> first | exact skip_left _ | exact skip_right _ | exact equivalent_refl _

theorem smartIf_correct (b : BExp) (c d : Cmd) : Equivalent (.ite b c d) (smartIf b c d) := by
  cases b <;> first | exact constant_branch _ _ _ | exact equivalent_refl _

theorem smartWhile_correct (b : BExp) (c : Cmd) : Equivalent (.while b c) (smartWhile b c) := by
  cases b with
  | truth v => cases v; exact false_loop c; exact equivalent_refl _
  | eq a d | le a d | not a | and a d => exact equivalent_refl _

theorem optimize_correct (c : Cmd) : Equivalent c (optimize c) := by
  induction c with
  | skip => exact equivalent_refl _
  | assign => exact equivalent_refl _
  | seq c d hc hd => exact equivalent_trans (equivalent_seq hc hd) (smartSeq_correct _ _)
  | ite b c d hc hd => exact equivalent_trans (equivalent_if b hc hd) (smartIf_correct _ _ _)
  | «while» b c hc => exact equivalent_trans (equivalent_while b hc) (smartWhile_correct _ _)

theorem optimize_preserves_hoare (P Q : Assertion) (c : Cmd) :
    Hoare P (optimize c) Q ↔ Hoare P c Q := by
  constructor
  · intro h s t hs he; exact h s t hs ((optimize_correct c s t).mp he)
  · intro h s t hs he; exact h s t hs ((optimize_correct c s t).mpr he)

end JonnyLean.Imperative
