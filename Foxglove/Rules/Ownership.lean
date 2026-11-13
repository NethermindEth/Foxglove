module

public import Foxglove.Assertion

public section
namespace Foxglove

open ProbSpace
open Iris OrderedUnitalResourceAlgebra
open UpperSetBI
open Iris BI UpperSetBI OURAProp

noncomputable section

/-! # Ownership

Reading an entailment on the resources that own its premise, and the σ-algebra a resource
measures. -/

lemma own_entails_of_sat {P : FProp} {a : BoundedFootprintSpace Bool} (ha : P.Sat a) :
    own a ⊢ P :=
  entails_iff.2 fun _ hb ↦ sat_mono ha (sat_own.1 hb).2 (sat_own.1 hb).1

lemma sat_of_own_entails {P : FProp} {a : BoundedFootprintSpace Bool} (hv : ✓a)
    (h : own a ⊢ P) : P.Sat a :=
  entails_iff.1 h a (sat_own.2 ⟨hv, le_refl a⟩)

/-- Owning a resource that already satisfies an assertion establishes it: upper sets are
closed upwards. -/
lemma own_entails_of_mem {U : UpperSet (BoundedFootprintSpace Bool)}
    {a : BoundedFootprintSpace Bool} (ha : a ∈ U) : own a ⊢ (fmk U : FProp) :=
  entails_iff.2 fun _ hb ↦ sat_fmk.2 ⟨(sat_own.1 hb).1, U.upper' (sat_own.1 hb).2 ha⟩

/-- `P ⊢ fmk U`, checked on the resources that own `P`. -/
lemma entails_fmk_of_own {P : FProp} {U : UpperSet (BoundedFootprintSpace Bool)}
    (h : ∀ a, ✓a → (own a ⊢ P) → a ∈ U) : P ⊢ (fmk U : FProp) :=
  entails_iff.2 fun a ha ↦
    sat_fmk.2 ⟨sat_valid ha, h a (sat_valid ha) (own_entails_of_sat ha)⟩

/-- An entailment, checked on the resources that own its premise. -/
lemma entails_of_own {P Q : FProp} (h : ∀ a, ✓a → (own a ⊢ P) → own a ⊢ Q) : P ⊢ Q :=
  entails_iff.2 fun a ha ↦
    sat_of_own_entails (sat_valid ha) (h a (sat_valid ha) (own_entails_of_sat ha))

lemma own_mono {x y : BoundedFootprintSpace Bool} (h : x ≤ y) : own y ⊢ own x :=
  entails_iff.2 fun _ ha ↦ sat_own.2 ⟨(sat_own.1 ha).1, le_trans h (sat_own.1 ha).2⟩

/-- Owning a resource above a space's own resource owns the space. -/
lemma own_entails_ownP {p : PSpace Ω} {hp : HasBoundedFootprint (p : PSp Ω)}
    {r : BoundedFootprintSpace Bool}
    (h : (⟨(p : PSp Ω), hp⟩ : BoundedFootprintSpace Bool) ≤ r) : own r ⊢ ownP p := by
  rw [ownP_def]
  exact entails_trans (own_mono h)
    (exists_intro (Ψ := fun h' : HasBoundedFootprint (p : PSp Ω) ↦
      own (⟨(p : PSp Ω), h'⟩ : BoundedFootprintSpace Bool)) hp)

lemma own_mul_sep {x y : BoundedFootprintSpace Bool} : own (x * y) ⊢ iprop(own x ∗ own y) :=
  entails_iff.2 fun _ ha ↦ by
    obtain ⟨hv, hle⟩ := sat_own.1 ha
    have hxy := valid_mono hle hv
    exact sat_sep.2 ⟨hv, x, y, hle, sat_own.2 ⟨valid_mul_l hxy, le_refl x⟩,
      sat_own.2 ⟨valid_mul_r hxy, le_refl y⟩⟩

/-- Splitting `own M ∗ W` semantically: `M` and a resource owning `W`. -/
lemma own_sep_entails_fmk {M : BoundedFootprintSpace Bool} {W : FProp}
    {U : UpperSet (BoundedFootprintSpace Bool)}
    (h : ∀ a R, ✓a → M * R ≤ a → (own R ⊢ W) → a ∈ U) :
    iprop(own M ∗ W) ⊢ (fmk U : FProp) :=
  entails_iff.2 fun a ha ↦ by
    obtain ⟨hv, b₁, b₂, hle, h₁, h₂⟩ := sat_sep.1 ha
    exact sat_fmk.2 ⟨hv, h a b₂ hv
      (le_trans (mul_le_mul_right_le (sat_own.1 h₁).2 b₂) hle) (own_entails_of_sat h₂)⟩

/-- The σ-algebra of a resource, read off its space. -/
lemma msOf_of_val {x : BoundedFootprintSpace Bool} {p : PSpace Ω} (h : (x : PSp Ω) = some p) :
    msOf x = p.ms := by
  rw [msOf_def, h]

/-- The σ-algebra of a defined product is the join. -/
lemma msOf_mul {x y : BoundedFootprintSpace Bool} {p q : PSpace Ω}
    (hx : (x : PSp Ω) = some p) (hy : (y : PSp Ω) = some q) (hv : ✓(x * y)) :
    msOf (x * y) = p.ms ⊔ q.ms := by
  obtain ⟨z, hz⟩ : ∃ z : PSpace Ω, ((x * y : BoundedFootprintSpace Bool) : PSp Ω) = some z :=
    Option.ne_none_iff_exists'.mp (PSp.valid_def.mp hv)
  have hz' : PSp.mul (some p) (some q) = some z := by
    rw [← hx, ← hy]; exact hz
  rw [msOf_of_val hz]
  exact (PSpace.isIndependentProduct_def.1 (PSp.mul_inversion hz')).1

/-- Owning a resource that satisfies a disjunction satisfies one of its disjuncts. -/
lemma own_or_elim {P R : FProp} {b : BoundedFootprintSpace Bool} (hv : ✓b)
    (h : own b ⊢ iprop(P ∨ R)) : (own b ⊢ P) ∨ (own b ⊢ R) :=
  (sat_or.1 (sat_of_own_entails hv h)).imp own_entails_of_sat own_entails_of_sat

/-- Owning a resource that satisfies an existential satisfies one of its instances. -/
lemma own_exists_elim {γ : Type} {P : γ → FProp} {b : BoundedFootprintSpace Bool} (hv : ✓b)
    (h : own b ⊢ iprop(∃ x, P x)) : ∃ x, own b ⊢ P x := by
  obtain ⟨x, hx⟩ := sat_exists.1 (sat_of_own_entails hv h)
  exact ⟨x, own_entails_of_sat hx⟩

end

end Foxglove
