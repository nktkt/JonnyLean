import Init.Data.List.Lemmas

namespace JonnyLean.DiscreteProbability

/-- Natural-number mass on a finite list of outcomes. Repeated outcomes
contribute once per occurrence, so no decidable equality is required. -/
def mass (weight : α → Nat) : List α → Nat
  | [] => 0
  | a :: xs => weight a + mass weight xs

/-- Mass of a decidable event, represented by its Boolean indicator. -/
def eventMass (weight : α → Nat) (event : α → Bool) : List α → Nat
  | [] => 0
  | a :: xs => (if event a then weight a else 0) + eventMass weight event xs

@[simp] theorem mass_nil (w : α → Nat) : mass w [] = 0 := rfl
@[simp] theorem mass_cons (w : α → Nat) (a : α) (xs : List α) : mass w (a :: xs) = w a + mass w xs := rfl
@[simp] theorem eventMass_nil (w : α → Nat) (p : α → Bool) : eventMass w p [] = 0 := rfl

theorem mass_append (w : α → Nat) (xs ys : List α) : mass w (xs ++ ys) = mass w xs + mass w ys := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih => simp [mass, ih, Nat.add_assoc]

theorem eventMass_filter (w : α → Nat) (p : α → Bool) (xs : List α) :
    eventMass w p xs = mass w (xs.filter p) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases hp : p a <;> simp [eventMass, List.filter, hp, ih]

@[simp] theorem eventMass_false (w : α → Nat) (xs : List α) : eventMass w (fun _ => false) xs = 0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [eventMass, ih]

@[simp] theorem eventMass_true (w : α → Nat) (xs : List α) : eventMass w (fun _ => true) xs = mass w xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [eventMass, mass, ih]

/-- An event and its Boolean complement partition all mass. -/
theorem eventMass_complement (w : α → Nat) (p : α → Bool) (xs : List α) :
    eventMass w p xs + eventMass w (fun a => !p a) xs = mass w xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases hp : p a <;> simp [eventMass, mass, hp, Nat.add_assoc, Nat.add_left_comm] at ih ⊢ <;>
      omega

theorem eventMass_le (w : α → Nat) (p : α → Bool) (xs : List α) : eventMass w p xs ≤ mass w xs := by
  have h := eventMass_complement w p xs
  omega

theorem eventMass_ext (w : α → Nat) (p q : α → Bool) (xs : List α)
    (h : ∀ a, a ∈ xs → p a = q a) : eventMass w p xs = eventMass w q xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [eventMass, eventMass, h a List.mem_cons_self, ih (fun b hb => h b (List.mem_cons_of_mem a hb))]

theorem eventMass_mono (w : α → Nat) (p q : α → Bool) (xs : List α)
    (h : ∀ a, a ∈ xs → p a = true → q a = true) : eventMass w p xs ≤ eventMass w q xs := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons a xs ih =>
    have ht := ih (fun b hb => h b (List.mem_cons_of_mem a hb))
    have ha := h a List.mem_cons_self
    cases hp : p a <;> cases hq : q a <;> simp [eventMass, hp, hq] at ha ⊢ <;> omega

/-- Finite additivity for events that are disjoint on the enumerated support. -/
theorem eventMass_disjoint_union (w : α → Nat) (p q : α → Bool) (xs : List α)
    (h : ∀ a, a ∈ xs → p a = true → q a = false) :
    eventMass w (fun a => p a || q a) xs = eventMass w p xs + eventMass w q xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have ht := ih (fun b hb => h b (List.mem_cons_of_mem a hb))
    have ha := h a List.mem_cons_self
    cases hp : p a <;> cases hq : q a <;>
      simp [eventMass, hp, hq, ht, Nat.add_assoc, Nat.add_left_comm] at ha ⊢

theorem mass_unit (xs : List α) : mass (fun _ => 1) xs = xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [mass, ih, Nat.add_comm]

end JonnyLean.DiscreteProbability
