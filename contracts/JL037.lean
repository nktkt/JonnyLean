import JonnyLean.Collections.ReverseAccumulator

namespace JonnyLean.Contracts

/-- Independent, fully quantified public target for JL-037. -/
theorem JL037 {α : Type u} (xs acc : List α) :
    JonnyLean.Collections.reverseInto xs acc = xs.reverse ++ acc :=
  JonnyLean.Collections.reverseInto_spec xs acc

example : JonnyLean.Collections.reverseInto [1, 2, 3] [8, 9] = [3, 2, 1, 8, 9] := rfl

example {α : Type u} (acc : List α) :
    JonnyLean.Collections.reverseInto [] acc = acc := rfl
end JonnyLean.Contracts

#print axioms JonnyLean.Collections.reverseInto_spec
#print axioms JonnyLean.Contracts.JL037
