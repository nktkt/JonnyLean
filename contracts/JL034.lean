import JonnyLean.Relations.Kernels

namespace JonnyLean.Contracts

/-- Independent, fully quantified public target for JL-034. -/
theorem JL034 {α : Type u} {β : Type v} {γ : Type w}
    (f : α → β) (s : β → α) (hs : ∀ b, f (s b) = b)
    (g : α → γ) (hg : ∀ a a', f a = f a' → g a = g a') :
    ∀ a, g (s (f a)) = g a :=
  JonnyLean.Relations.factor_with_section f s hs g hg

example {α : Type u} {β : Type v} (f : α → β) (a b c : α)
    (hab : f a = f b) (hbc : f b = f c) : f a = f c :=
  JonnyLean.Relations.kernel_transitive f hab hbc
end JonnyLean.Contracts

#print axioms JonnyLean.Relations.factor_with_section
#print axioms JonnyLean.Contracts.JL034
