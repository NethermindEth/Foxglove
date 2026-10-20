module

public import Foxglove.Assertion

@[expose] public section
namespace Foxglove

open ProbSpace
open Iris OrderedUnitalResourceAlgebra
open UpperSetBI
open Iris BI UpperSetBI OURAProp

noncomputable section

/-! # Ownership

Reading an entailment on the resources that own its premise, and the σ-algebra a resource
measures. -/

/-- Owning a resource that already satisfies an assertion establishes it: upper sets are
closed upwards. -/
lemma own_entails_of_mem {U : UpperSet (BoundedFootprintSpace Bool)}
    {a : BoundedFootprintSpace Bool} (ha : a ∈ U) : own a ⊢ (fmk U : FProp) :=
  fun _ _ hd ↦ U.upper' hd ha

/-- `P ⊢ fmk U`, checked on the resources that own `P`. -/
lemma entails_fmk_of_own {P : FProp} {U : UpperSet (BoundedFootprintSpace Bool)}
    (h : ∀ a, ✓a → (own a ⊢ P) → a ∈ U) : P ⊢ (fmk U : FProp) := by
  induction P using Quotient.ind with
  | _ P =>
  intro a hva ha
  exact h a hva (fun _ _ hb ↦ P.upper' hb ha)

lemma own_mono {x y : BoundedFootprintSpace Bool} (h : x ≤ y) : own y ⊢ own x :=
  fun _ _ ha ↦ le_trans h ha

lemma own_mul_sep {x y : BoundedFootprintSpace Bool} : own (x * y) ⊢ iprop(own x ∗ own y) :=
  fun _ _ ha ↦ ⟨x, y, ha, le_refl x, le_refl y⟩

/-- Splitting `own M ∗ W` semantically: `M` and a resource owning `W`. -/
lemma own_sep_entails_fmk {M : BoundedFootprintSpace Bool} {W : FProp}
    {U : UpperSet (BoundedFootprintSpace Bool)}
    (h : ∀ a R, ✓a → M * R ≤ a → (own R ⊢ W) → a ∈ U) :
    iprop(own M ∗ W) ⊢ (fmk U : FProp) := by
  induction W using Quotient.ind with
  | _ W =>
  rintro a hva ⟨b₁, b₂, hle, hb₁, hb₂⟩
  exact h a b₂ hva (le_trans (mul_le_mul_right_le hb₁ b₂) hle) (fun _ _ hb ↦ W.upper' hb hb₂)

/-- The σ-algebra of a resource, read off its space. -/
lemma msOf_of_val {x : BoundedFootprintSpace Bool} {p : PSpace Ω} (h : (x : PSp Ω) = some p) :
    msOf x = p.ms := by
  unfold msOf
  rw [h]

/-- The σ-algebra of a defined product is the join. -/
lemma msOf_mul {x y : BoundedFootprintSpace Bool} {p q : PSpace Ω}
    (hx : (x : PSp Ω) = some p) (hy : (y : PSp Ω) = some q) (hv : ✓(x * y)) :
    msOf (x * y) = p.ms ⊔ q.ms := by
  obtain ⟨z, hz⟩ : ∃ z : PSpace Ω, ((x * y : BoundedFootprintSpace Bool) : PSp Ω) = some z :=
    Option.ne_none_iff_exists'.mp (PSp.valid_def.mp hv)
  have hz' : PSp.mul (some p) (some q) = some z := by
    rw [← hx, ← hy]; exact hz
  rw [msOf_of_val hz]
  exact (PSp.mul_inversion hz').1

end

end Foxglove
