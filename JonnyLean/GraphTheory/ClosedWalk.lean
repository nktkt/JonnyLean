import JonnyLean.GraphTheory.Components

namespace JonnyLean.GraphTheory

/-- A closed walk may repeat vertices and may be empty. It is not a simple cycle. -/
abbrev ClosedWalk (G : Graph V) (x : V) := Walk G x x

namespace ClosedWalk
variable {V : Type u} {G : Graph V} {x y : V}

/-- Iterate a specified closed walk, with zero repetitions the empty walk. -/
def power (p : ClosedWalk G x) : Nat → ClosedWalk G x
  | 0 => .nil x
  | n + 1 => (power p n).append p

@[simp] theorem power_zero (p : ClosedWalk G x) : power p 0 = .nil x := rfl
@[simp] theorem power_succ (p : ClosedWalk G x) (n : Nat) :
    power p (n + 1) = (power p n).append p := rfl
@[simp] theorem power_one (p : ClosedWalk G x) : power p 1 = p := rfl
@[simp] theorem length_power (p : ClosedWalk G x) (n : Nat) : (power p n).length = n * p.length := by
  induction n with
  | zero => simp [power]
  | succ n ih => simp [power, ih, Nat.succ_mul]

theorem power_add (p : ClosedWalk G x) (m n : Nat) :
    power p (m + n) = (power p m).append (power p n) := by
  induction n with
  | zero => simp
  | succ n ih => simp [power, ih, Walk.append_assoc]

/-- Changing the starting point of two concatenated segments preserves length. -/
theorem rotation_length (p : Walk G x y) (q : Walk G y x) :
    (p.append q).length = (q.append p).length := by
  simp [Nat.add_comm]

theorem segments_same_component (p : Walk G x y) (q : Walk G y x) : SameComponent G x y :=
  ⟨⟨p⟩, ⟨q⟩⟩

end ClosedWalk
end JonnyLean.GraphTheory
