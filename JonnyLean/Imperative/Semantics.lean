import JonnyLean.Imperative.Expressions

namespace JonnyLean.Imperative

inductive Cmd where
  | skip : Cmd
  | assign : Nat → AExp → Cmd
  | seq : Cmd → Cmd → Cmd
  | ite : BExp → Cmd → Cmd → Cmd
  | while : BExp → Cmd → Cmd
  deriving DecidableEq, Repr

namespace Cmd

def writes : Cmd → List Nat
  | .skip => []
  | .assign x _ => [x]
  | .seq c d | .ite _ c d => writes c ++ writes d
  | .while _ c => writes c

end Cmd

/-- Finite derivations describe terminating runs only. -/
inductive Exec : Cmd → State → State → Prop where
  | skip (s) : Exec .skip s s
  | assign (s x e) : Exec (.assign x e) s (update s x (e.eval s))
  | seq : Exec c s u → Exec d u t → Exec (.seq c d) s t
  | ifTrue : b.eval s = true → Exec c s t → Exec (.ite b c d) s t
  | ifFalse : b.eval s = false → Exec d s t → Exec (.ite b c d) s t
  | whileFalse : b.eval s = false → Exec (.while b c) s s
  | whileTrue : b.eval s = true → Exec c s u → Exec (.while b c) u t → Exec (.while b c) s t

theorem exec_deterministic (h : Exec c s t) (k : Exec c s u) : t = u := by
  induction h generalizing u with
  | skip => cases k; rfl
  | assign => cases k; rfl
  | seq h₁ h₂ ih₁ ih₂ =>
    cases k with
    | seq k₁ k₂ => have heq := ih₁ k₁; subst heq; exact ih₂ k₂
  | ifTrue hb h ih =>
    cases k with
    | ifTrue _ k => exact ih k
    | ifFalse hb' _ => simp_all
  | ifFalse hb h ih =>
    cases k with
    | ifTrue hb' _ => simp_all
    | ifFalse _ k => exact ih k
  | whileFalse hb =>
    cases k with
    | whileFalse => rfl
    | whileTrue hb' _ _ => simp_all
  | whileTrue hb h₁ h₂ ih₁ ih₂ =>
    cases k with
    | whileFalse hb' => simp_all
    | whileTrue _ k₁ k₂ => have heq := ih₁ k₁; subst heq; exact ih₂ k₂

theorem exec_seq_iff (c d : Cmd) (s t : State) :
    Exec (.seq c d) s t ↔ ∃ u, Exec c s u ∧ Exec d u t := by
  constructor
  · intro h; cases h with | seq h₁ h₂ => exact ⟨_, h₁, h₂⟩
  · rintro ⟨u, h₁, h₂⟩; exact .seq h₁ h₂

theorem exec_seq_assoc (a b c : Cmd) (s t : State) :
    Exec (.seq (.seq a b) c) s t ↔ Exec (.seq a (.seq b c)) s t := by
  simp only [exec_seq_iff]
  constructor
  · rintro ⟨u, ⟨v, ha, hb⟩, hc⟩; exact ⟨v, ha, u, hb, hc⟩
  · rintro ⟨u, ha, v, hb, hc⟩; exact ⟨v, ⟨u, ha, hb⟩, hc⟩

theorem exec_while_unroll (b : BExp) (c : Cmd) (s t : State) :
    Exec (.while b c) s t ↔ Exec (.ite b (.seq c (.while b c)) .skip) s t := by
  constructor
  · intro h
    cases h with
    | whileFalse hb => exact .ifFalse hb (.skip _)
    | whileTrue hb hc hw => exact .ifTrue hb (.seq hc hw)
  · intro h
    cases h with
    | ifTrue hb hc => cases hc with | seq h₁ h₂ => exact .whileTrue hb h₁ h₂
    | ifFalse hb hs => cases hs; exact .whileFalse hb

theorem exec_preserves (h : Exec c s t) (x : Nat) (hx : x ∉ c.writes) : t x = s x := by
  induction h with
  | skip => rfl
  | assign s y e => exact update_other s y x (e.eval s) (by simpa [Cmd.writes] using hx)
  | seq h₁ h₂ ih₁ ih₂ =>
    have h₁x : x ∉ _ := fun hm => hx (List.mem_append_left _ hm)
    have h₂x : x ∉ _ := fun hm => hx (List.mem_append_right _ hm)
    exact (ih₂ h₂x).trans (ih₁ h₁x)
  | ifTrue hb h ih => exact ih (fun hm => hx (List.mem_append_left _ hm))
  | ifFalse hb h ih => exact ih (fun hm => hx (List.mem_append_right _ hm))
  | whileFalse => rfl
  | whileTrue hb h₁ h₂ ih₁ ih₂ => exact (ih₂ hx).trans (ih₁ hx)

theorem exec_frame_agreement (h : Exec c s t) (xs : List Nat)
    (hx : ∀ x ∈ xs, x ∉ c.writes) : Agrees xs t s := by
  intro x hm
  exact exec_preserves h x (hx x hm)

end JonnyLean.Imperative
