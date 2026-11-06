import Std

namespace JonnyLean.DataStructures

namespace Stack

def pushMany : List α → List α → List α
  | [], stack => stack
  | x :: xs, stack => pushMany xs (x :: stack)

def popMany : Nat → List α → Option (List α × List α)
  | 0, stack => some ([], stack)
  | _ + 1, [] => none
  | n + 1, x :: xs =>
    match popMany n xs with
    | none => none
    | some (taken, rest) => some (x :: taken, rest)

theorem pushMany_spec (xs stack : List α) : pushMany xs stack = xs.reverse ++ stack := by
  induction xs generalizing stack with
  | nil => rfl
  | cons x xs ih => simp only [pushMany, ih, List.reverse_cons, List.append_assoc, List.singleton_append]

theorem popMany_prefix (xs stack : List α) :
    popMany xs.length (xs ++ stack) = some (xs, stack) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.length_cons, List.cons_append, popMany, ih]

theorem popMany_pushMany (xs stack : List α) :
    popMany xs.length (pushMany xs stack) = some (xs.reverse, stack) := by
  simpa only [List.length_reverse, pushMany_spec] using popMany_prefix xs.reverse stack

theorem popMany_certificate (n : Nat) (stack taken rest : List α)
    (h : popMany n stack = some (taken, rest)) : stack = taken ++ rest ∧ taken.length = n := by
  induction n generalizing stack taken with
  | zero => simp only [popMany, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp
  | succ n ih =>
    cases stack with
    | nil => simp [popMany] at h
    | cons x xs =>
      cases hp : popMany n xs with
      | none => simp [popMany, hp] at h
      | some pair =>
        rcases pair with ⟨ys, zs⟩
        simp only [popMany, hp, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨heq, hlen⟩ := ih xs ys hp
        exact ⟨by simp only [List.cons_append, heq], by simp only [List.length_cons, hlen]⟩

theorem popMany_success_iff (n : Nat) (stack : List α) :
    (∃ taken rest, popMany n stack = some (taken, rest)) ↔ n ≤ stack.length := by
  induction n generalizing stack with
  | zero => simp [popMany]
  | succ n ih =>
    cases stack with
    | nil => simp [popMany]
    | cons x xs =>
      constructor
      · rintro ⟨taken, rest, h⟩
        obtain ⟨heq, hlen⟩ := popMany_certificate (n + 1) (x :: xs) taken rest h
        rw [heq, List.length_append, hlen]
        omega
      · intro h
        have hn : n ≤ xs.length := by simpa using h
        obtain ⟨ys, zs, hp⟩ := (ih xs).mpr hn
        exact ⟨x :: ys, zs, by simp only [popMany, hp]⟩

end Stack

structure Queue (α : Type u) where
  front : List α
  back : List α
  deriving Repr, DecidableEq

namespace Queue

def contents (q : Queue α) : List α := q.front ++ q.back.reverse
def Normal (q : Queue α) : Prop := q.front = [] → q.back = []

def normalize (q : Queue α) : Queue α :=
  match q.front with
  | [] => ⟨q.back.reverse, []⟩
  | _ :: _ => q

def enqueue (q : Queue α) (x : α) : Queue α := normalize ⟨q.front, x :: q.back⟩

def dequeue (q : Queue α) : Option (α × Queue α) :=
  match (normalize q).front with
  | [] => none
  | x :: xs => some (x, normalize ⟨xs, (normalize q).back⟩)

def enqueueMany (q : Queue α) : List α → Queue α
  | [] => q
  | x :: xs => enqueueMany (enqueue q x) xs

theorem normalize_contents (q : Queue α) : contents (normalize q) = contents q := by
  rcases q with ⟨front, back⟩
  cases front <;> simp [normalize, contents]

theorem normalize_normal (q : Queue α) : Normal (normalize q) := by
  rcases q with ⟨front, back⟩
  cases front <;> simp [Normal, normalize]

theorem normalize_of_normal (q : Queue α) (h : Normal q) : normalize q = q := by
  rcases q with ⟨front, back⟩
  cases front with
  | nil => have hb : back = [] := h rfl; subst back; rfl
  | cons x xs => rfl

theorem normalize_idempotent (q : Queue α) : normalize (normalize q) = normalize q :=
  normalize_of_normal _ (normalize_normal q)

theorem enqueue_contents (q : Queue α) (x : α) : contents (enqueue q x) = contents q ++ [x] := by
  unfold enqueue
  rw [normalize_contents]
  simp only [contents, List.reverse_cons, List.append_assoc]

theorem enqueue_normal (q : Queue α) (x : α) : Normal (enqueue q x) := normalize_normal _

theorem dequeue_spec (q : Queue α) :
    match dequeue q with
    | none => contents q = []
    | some (x, rest) => contents q = x :: contents rest ∧ Normal rest := by
  have hc := normalize_contents q
  have hn := normalize_normal q
  cases hf : (normalize q).front with
  | nil =>
    have hb := hn hf
    simp only [contents, hf, hb, List.reverse_nil, List.nil_append] at hc
    simpa only [dequeue, hf] using hc.symm
  | cons x xs =>
    simp only [contents, hf, List.cons_append] at hc
    simp only [dequeue, hf]
    constructor
    · rw [normalize_contents]
      exact hc.symm
    · exact normalize_normal _

theorem dequeue_none_iff (q : Queue α) : dequeue q = none ↔ contents q = [] := by
  cases h : dequeue q with
  | none => exact ⟨fun _ => by simpa only [h] using dequeue_spec q, fun _ => rfl⟩
  | some pair =>
    rcases pair with ⟨x, rest⟩
    have hc : contents q = x :: contents rest := (show contents q = x :: contents rest ∧ Normal rest from by simpa only [h] using dequeue_spec q).1
    simp [hc]

theorem enqueueMany_contents (q : Queue α) (xs : List α) :
    contents (enqueueMany q xs) = contents q ++ xs := by
  induction xs generalizing q with
  | nil => simp [enqueueMany]
  | cons x xs ih => simp only [enqueueMany, ih, enqueue_contents, List.append_assoc, List.singleton_append]

theorem enqueueMany_append (q : Queue α) (xs ys : List α) :
    enqueueMany q (xs ++ ys) = enqueueMany (enqueueMany q xs) ys := by
  induction xs generalizing q with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, enqueueMany, ih]

end Queue

namespace Assoc

abbrev Map (α : Type u) := List (Nat × α)

def lookup (key : Nat) : Map α → Option α
  | [] => none
  | (k, v) :: rest => if key = k then some v else lookup key rest

def put (key : Nat) (value : α) (m : Map α) : Map α := (key, value) :: m

def erase (key : Nat) : Map α → Map α
  | [] => []
  | (k, v) :: rest => if key = k then erase key rest else (k, v) :: erase key rest

def union (left right : Map α) : Map α := left ++ right
def mapValues (f : α → β) (m : Map α) : Map β := m.map (fun p => (p.1, f p.2))

theorem lookup_put (query key : Nat) (value : α) (m : Map α) :
    lookup query (put key value m) = if query = key then some value else lookup query m := rfl

theorem put_shadow (key : Nat) (first second : α) (m : Map α) (query : Nat) :
    lookup query (put key second (put key first m)) = lookup query (put key second m) := by
  simp only [lookup_put]; split <;> rfl

theorem put_commute (a b : Nat) (x y : α) (m : Map α) (hab : a ≠ b) (query : Nat) :
    lookup query (put a x (put b y m)) = lookup query (put b y (put a x m)) := by
  simp only [lookup_put]
  by_cases ha : query = a <;> by_cases hb : query = b <;> simp_all

theorem lookup_erase (query key : Nat) (m : Map α) :
    lookup query (erase key m) = if query = key then none else lookup query m := by
  induction m with
  | nil => simp [erase, lookup]
  | cons pair rest ih =>
    rcases pair with ⟨k, v⟩
    simp only [erase]
    by_cases hk : key = k
    · subst k; by_cases hq : query = key <;> simp_all [lookup]
    · simp only [if_neg hk, lookup, ih]
      by_cases hq : query = key <;> by_cases hqk : query = k <;> simp_all

theorem erase_idempotent (key : Nat) (m : Map α) : erase key (erase key m) = erase key m := by
  induction m with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨k, v⟩
    by_cases h : key = k <;> simp_all [erase]

theorem lookup_union (key : Nat) (left right : Map α) :
    lookup key (union left right) = (lookup key left).or (lookup key right) := by
  induction left with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨k, v⟩
    simp only [union, List.cons_append, lookup]
    split
    · rfl
    · exact ih

theorem union_assoc (a b c : Map α) : union (union a b) c = union a (union b c) :=
  List.append_assoc a b c

theorem lookup_mapValues (f : α → β) (key : Nat) (m : Map α) :
    lookup key (mapValues f m) = (lookup key m).map f := by
  induction m with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨k, v⟩
    simp only [mapValues, List.map_cons, lookup]
    split
    · rfl
    · exact ih

theorem mapValues_comp (f : α → β) (g : β → γ) (m : Map α) :
    mapValues g (mapValues f m) = mapValues (g ∘ f) m := by
  induction m with
  | nil => rfl
  | cons pair rest ih => simp only [mapValues, List.map_cons] at *; simp only [ih]; rfl

end Assoc
end JonnyLean.DataStructures
