import JonnyLean.Automata.Homomorphism
import JonnyLean.Automata.Reachability
namespace JonnyLean.Automata.Machine

def restrict (M : Machine α Q) (P : Q → Prop) (stable : M.Stable P)
    (hstart : P M.start) : Machine α {q : Q // P q} where
  step q a := ⟨M.step q.val a, stable q.val a q.property⟩
  start := ⟨M.start, hstart⟩
  accept q := M.accept q.val

def restrictionHom (M : Machine α Q) (P : Q → Prop) (stable : M.Stable P)
    (hstart : P M.start) : Hom (M.restrict P stable hstart) M where
  state := Subtype.val
  start := rfl
  step := fun _ _ => rfl
  accept := fun _ => rfl

theorem language_restrict (M : Machine α Q) (P : Q → Prop) (stable : M.Stable P)
    (hstart : P M.start) : (M.restrict P stable hstart).language = M.language :=
  (M.restrictionHom P stable hstart).language_eq

theorem finite_carrier_run (M : Machine α Q) (states : List Q)
    (closed : ∀ q a, q ∈ states → M.step q a ∈ states)
    (hstart : M.start ∈ states) (w : List α) : M.run M.start w ∈ states :=
  M.start_invariant (fun q => q ∈ states) closed hstart w

theorem reachable_restrict (M : Machine α Q) :
    (M.restrict M.Reachable M.reachable_step M.reachable_start).language = M.language :=
  M.language_restrict _ _ _
end JonnyLean.Automata.Machine
