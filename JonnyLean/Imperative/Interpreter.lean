import JonnyLean.Imperative.Semantics

namespace JonnyLean.Imperative

/-- Fuel bounds the derivation height; both sequence children receive the decremented fuel. -/
def run : Nat → Cmd → State → Option State
  | 0, _, _ => none
  | _ + 1, .skip, s => some s
  | _ + 1, .assign x e, s => some (update s x (e.eval s))
  | n + 1, .seq c d, s => (run n c s).bind (run n d)
  | n + 1, .ite b c d, s => if b.eval s then run n c s else run n d s
  | n + 1, .while b c, s =>
      if b.eval s then (run n c s).bind (run n (.while b c)) else some s

theorem run_sound (n : Nat) (c : Cmd) (s t : State) (h : run n c s = some t) : Exec c s t := by
  induction n generalizing c s t with
  | zero => simp [run] at h
  | succ n ih =>
    cases c with
    | skip => simp [run] at h; subst t; exact .skip s
    | assign x e => simp [run] at h; subst t; exact .assign s x e
    | seq c d =>
      simp only [run, Option.bind_eq_some_iff] at h
      obtain ⟨u, hc, hd⟩ := h
      exact .seq (ih c s u hc) (ih d u t hd)
    | ite b c d =>
      simp only [run] at h
      split at h
      · exact .ifTrue (by assumption) (ih c s t h)
      · exact .ifFalse (by simpa using ‹¬b.eval s = true›) (ih d s t h)
    | «while» b c =>
      simp only [run] at h
      split at h
      · obtain ⟨u, hc, hw⟩ := Option.bind_eq_some_iff.mp h
        exact .whileTrue (by assumption) (ih c s u hc) (ih (.while b c) u t hw)
      · simp only [Option.some.injEq] at h
        subst t
        exact .whileFalse (by simpa using ‹¬b.eval s = true›)

theorem run_mono (n m : Nat) (hnm : n ≤ m) (c : Cmd) (s t : State)
    (h : run n c s = some t) : run m c s = some t := by
  induction n generalizing m c s t with
  | zero => simp [run] at h
  | succ n ih =>
    cases m with
    | zero => exfalso; omega
    | succ m =>
      have hle : n ≤ m := by omega
      cases c with
      | skip => simpa only [run] using h
      | assign x e => simpa only [run] using h
      | seq c d =>
        obtain ⟨u, hc, hd⟩ := Option.bind_eq_some_iff.mp h
        exact Option.bind_eq_some_iff.mpr ⟨u, ih m hle c s u hc, ih m hle d u t hd⟩
      | ite b c d =>
        simp only [run] at h ⊢
        split at h
        · rw [if_pos (by assumption)]; exact ih m hle c s t h
        · rw [if_neg (by assumption)]; exact ih m hle d s t h
      | «while» b c =>
        simp only [run] at h ⊢
        split at h
        · rw [if_pos (by assumption)]
          obtain ⟨u, hc, hw⟩ := Option.bind_eq_some_iff.mp h
          exact Option.bind_eq_some_iff.mpr ⟨u, ih m hle c s u hc, ih m hle (.while b c) u t hw⟩
        · rw [if_neg (by assumption)]; exact h

theorem run_complete (h : Exec c s t) : ∃ n, run n c s = some t := by
  induction h with
  | skip s => exact ⟨1, rfl⟩
  | assign s x e => exact ⟨1, rfl⟩
  | seq hc hd ihc ihd =>
    obtain ⟨n, hn⟩ := ihc; obtain ⟨m, hm⟩ := ihd
    refine ⟨max n m + 1, ?_⟩
    exact Option.bind_eq_some_iff.mpr ⟨_, run_mono n _ (Nat.le_max_left ..) _ _ _ hn,
      run_mono m _ (Nat.le_max_right ..) _ _ _ hm⟩
  | ifTrue hb hc ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by simp [run, hb, hn]⟩
  | ifFalse hb hc ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by simp [run, hb, hn]⟩
  | whileFalse hb => exact ⟨1, by simp [run, hb]⟩
  | whileTrue hb hc hw ihc ihw =>
    obtain ⟨n, hn⟩ := ihc; obtain ⟨m, hm⟩ := ihw
    refine ⟨max n m + 1, ?_⟩
    simp only [run, hb, ite_true]
    exact Option.bind_eq_some_iff.mpr ⟨_, run_mono n _ (Nat.le_max_left ..) _ _ _ hn,
      run_mono m _ (Nat.le_max_right ..) _ _ _ hm⟩

theorem exec_iff_run (c : Cmd) (s t : State) : Exec c s t ↔ ∃ n, run n c s = some t :=
  ⟨run_complete, fun ⟨n, hn⟩ => run_sound n c s t hn⟩

theorem run_fuel_unique (c : Cmd) (s t u : State) (n m : Nat)
    (hn : run n c s = some t) (hm : run m c s = some u) : t = u :=
  exec_deterministic (run_sound n c s t hn) (run_sound m c s u hm)

theorem run_zero (c : Cmd) (s : State) : run 0 c s = none := rfl

end JonnyLean.Imperative
