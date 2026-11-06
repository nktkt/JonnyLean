import JonnyLean.Languages.Monoid
namespace JonnyLean.Languages

def leftQuotient (u : List α) (L : Language α) : Language α := fun w => L (u ++ w)

theorem quotient_nil (L : Language α) : leftQuotient [] L = L := rfl
theorem quotient_append (u v : List α) (L : Language α) :
    leftQuotient (u ++ v) L = leftQuotient v (leftQuotient u L) := by
  funext w; simp [leftQuotient, List.append_assoc]
theorem quotient_union (u : List α) (L K : Language α) :
    leftQuotient u (union L K) = union (leftQuotient u L) (leftQuotient u K) := rfl
theorem quotient_inter (u : List α) (L K : Language α) :
    leftQuotient u (inter L K) = inter (leftQuotient u L) (leftQuotient u K) := rfl
theorem quotient_mono {L K : Language α} (h : Included L K) (u : List α) :
    Included (leftQuotient u L) (leftQuotient u K) := fun w hw => h (u ++ w) hw
theorem quotient_empty_word (u : List α) (L : Language α) : leftQuotient u L [] ↔ L u := by
  simp [leftQuotient]
end JonnyLean.Languages
