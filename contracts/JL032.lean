import JonnyLean.Relations.Closure

namespace JonnyLean.Contracts

/-- Independent, fully quantified public target for JL-032. -/
theorem JL032 {α : Type u} (r s : α → α → Prop)
    (hinc : ∀ a b, r a b → s a b) (href : ∀ a, s a a)
    (htrans : ∀ a b c, s a b → s b c → s a c) :
    ∀ a b, JonnyLean.Relations.Reach r a b → s a b :=
  JonnyLean.Relations.reach_least hinc href htrans

example {α : Type u} (r : α → α → Prop) (a : α) :
    JonnyLean.Relations.Reach r a a := .refl a
end JonnyLean.Contracts

#print axioms JonnyLean.Relations.reach_least
#print axioms JonnyLean.Contracts.JL032
