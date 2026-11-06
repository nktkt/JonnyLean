import Init.Data.List.Lemmas

namespace JonnyLean.Parsing

abbrev Parser (α : Type u) (β : Type v) := List α → Option (β × List α)

def pureP (b : β) : Parser α β := fun input => some (b,input)
def failP : Parser α β := fun _ => none

def bindP (p : Parser α β) (f : β → Parser α γ) : Parser α γ := fun input =>
  match p input with
  | none => none
  | some (b,rest) => f b rest

def mapP (f : β → γ) (p : Parser α β) : Parser α γ := bindP p (fun b => pureP (f b))

def choice (p q : Parser α β) : Parser α β := fun input =>
  match p input with
  | none => q input
  | some result => some result

def Safe (p : Parser α β) : Prop :=
  ∀ input b rest, p input = some (b,rest) → ∃ consumed, input = consumed ++ rest

theorem pure_safe (b : β) : Safe (pureP (α := α) b) := by
  intro input value rest h
  cases h
  exact ⟨[],rfl⟩

theorem fail_safe : Safe (failP : Parser α β) := by
  intro input b rest h
  cases h

theorem bind_safe {p : Parser α β} {f : β → Parser α γ}
    (hp : Safe p) (hf : ∀ b, Safe (f b)) : Safe (bindP p f) := by
  intro input c rest h
  cases e : p input with
  | none => simp [bindP,e] at h
  | some result =>
    rcases result with ⟨b,middle⟩
    obtain ⟨u,hu⟩ := hp input b middle e
    obtain ⟨v,hv⟩ := hf b middle c rest (by simpa [bindP,e] using h)
    exact ⟨u ++ v, by simp [hu,hv,List.append_assoc]⟩

theorem bind_assoc (p : Parser α β) (f : β → Parser α γ) (g : γ → Parser α δ) :
    bindP (bindP p f) g = bindP p (fun b => bindP (f b) g) := by
  funext input
  cases h : p input with
  | none => simp [bindP,h]
  | some result => rcases result with ⟨b,rest⟩; simp [bindP,h]

theorem bind_pure_left (b : β) (f : β → Parser α γ) : bindP (pureP b) f = f b := rfl

theorem bind_pure_right (p : Parser α β) : bindP p pureP = p := by
  funext input
  cases h : p input with
  | none => simp [bindP,h]
  | some result => rcases result with ⟨b,rest⟩; simp [bindP,pureP,h]

theorem choice_assoc (p q r : Parser α β) : choice (choice p q) r = choice p (choice q r) := by
  funext input
  cases h : p input <;> simp [choice,h]

theorem choice_safe {p q : Parser α β} (hp : Safe p) (hq : Safe q) : Safe (choice p q) := by
  intro input b rest h
  cases e : p input with
  | none => exact hq input b rest (by simpa [choice,e] using h)
  | some result => exact hp input b rest (by simpa [choice,e] using h)

theorem map_comp (f : β → γ) (g : γ → δ) (p : Parser α β) :
    mapP g (mapP f p) = mapP (fun b => g (f b)) p := by
  simp [mapP,bind_assoc,bind_pure_left]

theorem map_id (p : Parser α β) : mapP id p = p := bind_pure_right p

theorem map_safe {p : Parser α β} (hp : Safe p) (f : β → γ) : Safe (mapP f p) :=
  bind_safe hp (fun _ => pure_safe _)

def pairP (p : Parser α β) (q : Parser α γ) : Parser α (β × γ) :=
  bindP p (fun b => mapP (fun c => (b,c)) q)

theorem pair_iff (p : Parser α β) (q : Parser α γ) (input rest : List α) (b : β) (c : γ) :
    pairP p q input = some ((b,c),rest) ↔
      ∃ middle, p input = some (b,middle) ∧ q middle = some (c,rest) := by
  unfold pairP bindP mapP
  cases h : p input with
  | none => simp
  | some result =>
    rcases result with ⟨b',middle⟩
    cases k : q middle with
    | none => simp [bindP,k]
    | some result =>
      rcases result with ⟨c',rest'⟩
      simp [bindP,pureP,k,Prod.ext_iff,and_assoc]

end JonnyLean.Parsing
