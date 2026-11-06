import JonnyLean.Languages.StarClosure

namespace JonnyLean.RegularExpressions
open JonnyLean.Languages

inductive Regex (α : Type u) where
  | zero : Regex α
  | eps : Regex α
  | atom : α → Regex α
  | alt : Regex α → Regex α → Regex α
  | seq : Regex α → Regex α → Regex α
  | star : Regex α → Regex α
  deriving DecidableEq

def denotes : Regex α → Language α
  | .zero => empty
  | .eps => epsilon
  | .atom a => fun w => w = [a]
  | .alt r s => union (denotes r) (denotes s)
  | .seq r s => concat (denotes r) (denotes s)
  | .star r => Star (denotes r)

def nullable : Regex α → Bool
  | .zero => false
  | .eps => true
  | .atom _ => false
  | .alt r s => nullable r || nullable s
  | .seq r s => nullable r && nullable s
  | .star _ => true

theorem concat_nil_iff (L K : Language α) : concat L K [] ↔ L [] ∧ K [] := by
  constructor
  · rintro ⟨u,v,hu,hv,e⟩
    have h := List.append_eq_nil_iff.mp e
    simpa [h.1,h.2] using And.intro hu hv
  · rintro ⟨h,k⟩; exact ⟨[],[],h,k,rfl⟩

theorem nullable_correct (r : Regex α) : nullable r = true ↔ denotes r [] := by
  induction r with
  | zero => simp [nullable, denotes, empty]
  | eps => simp [nullable, denotes, epsilon]
  | atom a => simp [nullable, denotes]
  | alt r s ih jh => simpa [nullable, denotes, union] using or_congr ih jh
  | seq r s ih jh => simpa [nullable, denotes, concat_nil_iff] using and_congr ih jh
  | star r ih => simp only [nullable, denotes, true_iff]; exact Star.nil

def Equivalent (r s : Regex α) : Prop := ∀ w, denotes r w ↔ denotes s w

theorem equivalent_refl (r : Regex α) : Equivalent r r := fun _ => Iff.rfl

theorem equivalent_symm {r s : Regex α} (h : Equivalent r s) : Equivalent s r :=
  fun w => (h w).symm

theorem equivalent_trans {r s t : Regex α} (h : Equivalent r s) (k : Equivalent s t) :
    Equivalent r t := fun w => (h w).trans (k w)

end JonnyLean.RegularExpressions
