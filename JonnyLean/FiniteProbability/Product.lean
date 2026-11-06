import JonnyLean.FiniteProbability.Expectation
namespace JonnyLean.FiniteProbability
open DiscreteProbability

def product (μ : Measure α) (ν : Measure β) : Measure (α × β) :=
  μ.flatMap (fun p => ν.map (fun q => ((p.1, q.1), p.2 * q.2)))

theorem expect_product (μ : Measure α) (ν : Measure β) (f : α → Nat) (g : β → Nat) :
    expect (product μ ν) (fun p => f p.1 * g p.2) = expect μ f * expect ν g := by
  induction μ with
  | nil => simp [product]
  | cons p μ ih =>
    cases p with
    | mk a n =>
      simp only [product, List.flatMap_cons, expect_append] at ih ⊢
      rw [ih]
      have h : expect (ν.map (fun q => ((a, q.1), n * q.2))) (fun p => f p.1 * g p.2) =
          (n * f a) * expect ν g := by
        unfold expect
        rw [Counting.mass_map]
        change mass (fun q => (n * q.2) * (f a * g q.1)) ν = _
        have he : (fun q : β × Nat => (n * q.2) * (f a * g q.1)) =
            (fun q => (n * f a) * (q.2 * g q.1)) := by funext q; ac_rfl
        rw [he, Counting.mass_scale_left]
      rw [h, expect_cons, Nat.add_mul]

theorem total_product (μ : Measure α) (ν : Measure β) : total (product μ ν) = total μ * total ν := by
  have h := expect_product μ ν (fun _ => 1) (fun _ => 1)
  simpa [expect_const] using h

theorem expect_product_fst (μ : Measure α) (ν : Measure β) (f : α → Nat) :
    expect (product μ ν) (fun p => f p.1) = expect μ f * total ν := by
  simpa [expect_const] using expect_product μ ν f (fun _ => 1)

theorem expect_product_snd (μ : Measure α) (ν : Measure β) (g : β → Nat) :
    expect (product μ ν) (fun p => g p.2) = total μ * expect ν g := by
  simpa [expect_const] using expect_product μ ν (fun _ => 1) g
end JonnyLean.FiniteProbability
