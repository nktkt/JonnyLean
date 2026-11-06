import JonnyLean.Collections.Intersection

namespace JonnyLean.FiniteSet

def mapInjective (f : α → β) (hf : ∀ a b, f a = f b → a = b)
    (A : FiniteSet α) : FiniteSet β where
  elems := A.elems.map f
  nodup := A.nodup.map f (fun a b hab he => hab (hf a b he))

theorem mem_mapInjective (f : α → β) (hf : ∀ a b, f a = f b → a = b)
    (A : FiniteSet α) (y : β) :
    y ∈ mapInjective f hf A ↔ ∃ x, x ∈ A ∧ f x = y := by
  change y ∈ A.elems.map f ↔ ∃ x, x ∈ A.elems ∧ f x = y
  exact List.mem_map

theorem card_mapInjective (f : α → β) (hf : ∀ a b, f a = f b → a = b)
    (A : FiniteSet α) : card (mapInjective f hf A) = card A := by
  exact List.length_map f

theorem mapInjective_reflects_subset (f : α → β) (hf : ∀ a b, f a = f b → a = b)
    (A B : FiniteSet α) :
    Subset (mapInjective f hf A) (mapInjective f hf B) ↔ Subset A B := by
  constructor
  · intro h x hx
    obtain ⟨y, hy, hyx⟩ := (mem_mapInjective f hf B (f x)).mp
      (h (f x) ((mem_mapInjective f hf A (f x)).mpr ⟨x, hx, rfl⟩))
    exact hf y x hyx ▸ hy
  · intro h y hy
    obtain ⟨x, hx, hxy⟩ := (mem_mapInjective f hf A y).mp hy
    exact (mem_mapInjective f hf B y).mpr ⟨x, h x hx, hxy⟩

theorem mapInjective_intersection [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : ∀ a b, f a = f b → a = b) (A B : FiniteSet α) :
    Equivalent (mapInjective f hf (intersection A B))
      (intersection (mapInjective f hf A) (mapInjective f hf B)) := by
  intro y
  rw [mem_mapInjective, mem_intersection]
  constructor
  · intro ⟨x, hx, hxy⟩
    have h := (mem_intersection A B x).mp hx
    exact ⟨(mem_mapInjective f hf A y).mpr ⟨x, h.1, hxy⟩,
      (mem_mapInjective f hf B y).mpr ⟨x, h.2, hxy⟩⟩
  · intro ⟨ha, hb⟩
    obtain ⟨a, ha, hay⟩ := (mem_mapInjective f hf A y).mp ha
    obtain ⟨b, hb, hby⟩ := (mem_mapInjective f hf B y).mp hb
    have hab := hf a b (hay.trans hby.symm)
    exact ⟨a, (mem_intersection A B a).mpr ⟨ha, hab ▸ hb⟩, hay⟩

end JonnyLean.FiniteSet
