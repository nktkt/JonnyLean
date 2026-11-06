import JonnyLean.Imperative.Equivalence

namespace JonnyLean.Imperative

def increment (x : Nat) : Cmd := .assign x (.add (.var x) (.lit 1))

theorem increment_correct (x : Nat) (s : State) :
    ∃ t, Exec (increment x) s t ∧ t x = s x + 1 ∧ ∀ y, y ≠ x → t y = s y := by
  refine ⟨update s x (s x + 1), .assign _ _ _, ?_, ?_⟩
  · simp
  · intro y hy; exact update_other s x y _ hy

def swap (x y tmp : Nat) : Cmd :=
  .seq (.assign tmp (.var x)) (.seq (.assign x (.var y)) (.assign y (.var tmp)))

theorem swap_correct (x y tmp : Nat) (hxy : x ≠ y) (hxt : x ≠ tmp) (hyt : y ≠ tmp) (s : State) :
    ∃ t, Exec (swap x y tmp) s t ∧ t x = s y ∧ t y = s x ∧
      ∀ z, z ∉ [x, y, tmp] → t z = s z := by
  let s₁ := update s tmp (s x)
  let s₂ := update s₁ x (s₁ y)
  let t := update s₂ y (s₂ tmp)
  refine ⟨t, .seq (.assign _ _ _) (.seq (.assign _ _ _) (.assign _ _ _)), ?_, ?_, ?_⟩
  · simp [t, s₂, s₁, update, hxy, hyt]
  · simp [t, s₂, s₁, update, Ne.symm hxt]
  · intro z hz
    simp only [List.mem_cons, not_or] at hz
    simp [t, s₂, s₁, update, hz.1, hz.2.1, hz.2.2]

def positive (x : Nat) : BExp := .le (.lit 1) (.var x)
def decrement (x : Nat) : Cmd := .assign x (.sub (.var x) (.lit 1))
def countdown (x : Nat) : Cmd := .while (positive x) (decrement x)

theorem countdown_exec (x n : Nat) (s : State) (hx : s x = n) :
    Exec (countdown x) s (update s x 0) := by
  induction n generalizing s with
  | zero =>
    have hstate : update s x 0 = s := by rw [← hx]; exact update_same s x
    rw [hstate]
    exact .whileFalse (by simp [positive, BExp.eval, AExp.eval, hx])
  | succ n ih =>
    have hb : Exec (decrement x) s (update s x n) := by
      simpa [decrement, AExp.eval, hx] using (Exec.assign s x (.sub (.var x) (.lit 1)))
    have hw := ih (update s x n) (by simp)
    rw [update_shadow] at hw
    exact .whileTrue (by simp [positive, BExp.eval, AExp.eval, hx]) hb hw

theorem countdown_correct (x : Nat) (s : State) :
    Exec (countdown x) s (update s x 0) ∧ ∀ t, Exec (countdown x) s t → t = update s x 0 :=
  ⟨countdown_exec x (s x) s rfl, fun _ h => exec_deterministic h (countdown_exec x (s x) s rfl)⟩

theorem countdown_fuel (x n : Nat) (s : State) (hx : s x = n) :
    run (n + 2) (countdown x) s = some (update s x 0) := by
  induction n generalizing s with
  | zero =>
    have hstate : update s x 0 = s := by rw [← hx]; exact update_same s x
    simp [countdown, run, positive, BExp.eval, AExp.eval, hx, hstate]
  | succ n ih =>
    have hi := ih (update s x n) (by simp)
    rw [update_shadow] at hi
    simpa [countdown, run, positive, decrement, BExp.eval, AExp.eval, hx] using hi

def transfer (x y : Nat) : Cmd :=
  .while (positive x) (.seq (increment y) (decrement x))

theorem transfer_total (x y : Nat) (hxy : x ≠ y) (n : Nat) (s : State) (hx : s x = n) :
    ∃ t, Exec (transfer x y) s t ∧ t x = 0 ∧ t y = s y + n := by
  induction n generalizing s with
  | zero =>
    refine ⟨s, .whileFalse ?_, hx, by simp⟩
    simp [positive, BExp.eval, AExp.eval, hx]
  | succ n ih =>
    let u := update (update s y (s y + 1)) x n
    have hu : u x = n := by simp [u]
    obtain ⟨t, ht, htx, hty⟩ := ih u hu
    have hbody : Exec (.seq (increment y) (decrement x)) s u := by
      apply Exec.seq (Exec.assign s y (.add (.var y) (.lit 1)))
      simpa [decrement, AExp.eval, update, hxy, hx, u] using
        (Exec.assign (update s y (s y + 1)) x (.sub (.var x) (.lit 1)))
    refine ⟨t, .whileTrue ?_ hbody ht, htx, ?_⟩
    · simp [positive, BExp.eval, AExp.eval, hx]
    · simpa [u, update, Ne.symm hxy, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hty

theorem transfer_correct (x y : Nat) (hxy : x ≠ y) (s : State) :
    ∃ t, Exec (transfer x y) s t ∧ t x = 0 ∧ t y = s y + s x ∧
      ∀ z, z ≠ x → z ≠ y → t z = s z := by
  obtain ⟨t, ht, hx, hy⟩ := transfer_total x y hxy (s x) s rfl
  refine ⟨t, ht, hx, hy, ?_⟩
  intro z hzx hzy
  exact exec_preserves ht z (by simp [transfer, increment, decrement, Cmd.writes, hzx, hzy])

def triangle : Nat → Nat
  | 0 => 0
  | n + 1 => triangle n + (n + 1)

def accumulate (x y : Nat) : Cmd :=
  .while (positive x)
    (.seq (.assign y (.add (.var y) (.var x))) (decrement x))

theorem accumulate_total (x y : Nat) (hxy : x ≠ y) (n : Nat) (s : State) (hx : s x = n) :
    ∃ t, Exec (accumulate x y) s t ∧ t x = 0 ∧ t y = s y + triangle n := by
  induction n generalizing s with
  | zero =>
    refine ⟨s, .whileFalse ?_, hx, by simp [triangle]⟩
    simp [positive, BExp.eval, AExp.eval, hx]
  | succ n ih =>
    let u := update (update s y (s y + (n + 1))) x n
    have hu : u x = n := by simp [u]
    obtain ⟨t, ht, htx, hty⟩ := ih u hu
    have hbody : Exec (.seq (.assign y (.add (.var y) (.var x))) (decrement x)) s u := by
      apply Exec.seq (Exec.assign s y (.add (.var y) (.var x)))
      simpa [decrement, AExp.eval, update, hxy, hx, u] using
        (Exec.assign (update s y (s y + (n + 1))) x (.sub (.var x) (.lit 1)))
    refine ⟨t, .whileTrue ?_ hbody ht, htx, ?_⟩
    · simp [positive, BExp.eval, AExp.eval, hx]
    · simpa [u, update, Ne.symm hxy, triangle, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hty

theorem triangle_formula (n : Nat) : 2 * triangle n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [triangle, Nat.mul_add, ih, Nat.add_mul, Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> omega

theorem accumulate_correct (x y : Nat) (hxy : x ≠ y) (s : State) :
    ∃ t, Exec (accumulate x y) s t ∧ t x = 0 ∧
      2 * t y = 2 * s y + s x * (s x + 1) := by
  obtain ⟨t, ht, hx, hy⟩ := accumulate_total x y hxy (s x) s rfl
  refine ⟨t, ht, hx, ?_⟩
  rw [hy, Nat.mul_add, triangle_formula]

end JonnyLean.Imperative
