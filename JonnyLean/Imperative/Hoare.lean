import JonnyLean.Imperative.Interpreter

namespace JonnyLean.Imperative

abbrev Assertion := State → Prop

/-- Partial correctness: only states connected by a terminating derivation are constrained. -/
def Hoare (P : Assertion) (c : Cmd) (Q : Assertion) : Prop :=
  ∀ s t, P s → Exec c s t → Q t

def DependsOn (xs : List Nat) (P : Assertion) : Prop :=
  ∀ s t, Agrees xs s t → (P s ↔ P t)

theorem hoare_skip (P : Assertion) : Hoare P .skip P := by
  intro s t hs h; cases h; exact hs

theorem hoare_assign (Q : Assertion) (x : Nat) (e : AExp) :
    Hoare (fun s => Q (update s x (e.eval s))) (.assign x e) Q := by
  intro s t hs h; cases h; exact hs

theorem hoare_seq (P R Q : Assertion) (c d : Cmd)
    (hc : Hoare P c R) (hd : Hoare R d Q) : Hoare P (.seq c d) Q := by
  intro s t hs h
  cases h with
  | seq h₁ h₂ => exact hd _ _ (hc _ _ hs h₁) h₂

theorem hoare_if (P Q : Assertion) (b : BExp) (c d : Cmd)
    (hc : Hoare (fun s => P s ∧ b.eval s = true) c Q)
    (hd : Hoare (fun s => P s ∧ b.eval s = false) d Q) : Hoare P (.ite b c d) Q := by
  intro s t hs h
  cases h with
  | ifTrue hb h => exact hc _ _ ⟨hs, hb⟩ h
  | ifFalse hb h => exact hd _ _ ⟨hs, hb⟩ h

theorem exec_while_invariant (I : Assertion) (b : BExp) (c : Cmd)
    (body : Hoare (fun s => I s ∧ b.eval s = true) c I)
    (h : Exec (.while b c) s t) (hs : I s) : I t ∧ b.eval t = false := by
  generalize hw : Cmd.while b c = w at h
  induction h with
  | skip => cases hw
  | assign => cases hw
  | seq => cases hw
  | ifTrue => cases hw
  | ifFalse => cases hw
  | whileFalse hb => cases hw; exact ⟨hs, hb⟩
  | whileTrue hb hc hw' _ ih =>
    cases hw
    exact ih (body _ _ ⟨hs, hb⟩ hc) rfl

theorem hoare_while (I : Assertion) (b : BExp) (c : Cmd)
    (body : Hoare (fun s => I s ∧ b.eval s = true) c I) :
    Hoare I (.while b c) (fun s => I s ∧ b.eval s = false) := by
  intro s t hs h
  exact exec_while_invariant I b c body h hs

theorem hoare_consequence (P P' Q Q' : Assertion) (c : Cmd)
    (pre : ∀ s, P' s → P s) (post : ∀ s, Q s → Q' s)
    (h : Hoare P c Q) : Hoare P' c Q' := by
  intro s t hs he
  exact post t (h s t (pre s hs) he)

theorem hoare_conjunction (P Q R : Assertion) (c : Cmd)
    (hQ : Hoare P c Q) (hR : Hoare P c R) : Hoare P c (fun s => Q s ∧ R s) := by
  intro s t hs he
  exact ⟨hQ s t hs he, hR s t hs he⟩

theorem hoare_disjunction (P R Q : Assertion) (c : Cmd)
    (hP : Hoare P c Q) (hR : Hoare R c Q) : Hoare (fun s => P s ∨ R s) c Q := by
  intro s t hs he
  cases hs with
  | inl hs => exact hP s t hs he
  | inr hs => exact hR s t hs he

theorem hoare_frame (P Q R : Assertion) (c : Cmd) (xs : List Nat)
    (h : Hoare P c Q) (dep : DependsOn xs R) (fresh : ∀ x ∈ xs, x ∉ c.writes) :
    Hoare (fun s => P s ∧ R s) c (fun s => Q s ∧ R s) := by
  intro s t hs he
  exact ⟨h s t hs.1 he, (dep t s (exec_frame_agreement he xs fresh)).mpr hs.2⟩

/-- The weakest liberal precondition; it does not assert termination. -/
def wlp (c : Cmd) (Q : Assertion) : Assertion := fun s => ∀ t, Exec c s t → Q t

theorem hoare_iff_wlp (P Q : Assertion) (c : Cmd) :
    Hoare P c Q ↔ ∀ s, P s → wlp c Q s := by
  constructor
  · intro h s hs t he; exact h s t hs he
  · intro h s t hs he; exact h s hs t he

theorem wlp_sequence (c d : Cmd) (Q : Assertion) (s : State) :
    wlp (.seq c d) Q s ↔ wlp c (wlp d Q) s := by
  constructor
  · intro h u hc t hd; exact h t (.seq hc hd)
  · intro h t he; cases he with | seq hc hd => exact h _ hc _ hd

theorem wlp_mono (c : Cmd) (P Q : Assertion) (h : ∀ s, P s → Q s) :
    ∀ s, wlp c P s → wlp c Q s := by
  intro s hs t he
  exact h t (hs t he)

end JonnyLean.Imperative
