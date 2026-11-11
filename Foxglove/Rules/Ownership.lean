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

/-- Owning a resource that already satisfies an assertion establishes it: upper sets are
closed upwards. -/
lemma own_entails_of_mem {U : UpperSet (BoundedFootprintSpace Bool)}
    {a : BoundedFootprintSpace Bool} (ha : a ∈ U) : own a ⊢ (fmk U : FProp) := by
  rw [own_def]
  exact fun _ _ hd ↦ U.upper' (UpperSetBI.mem_own.1 hd) ha

/-- `P ⊢ fmk U`, checked on the resources that own `P`. -/
lemma entails_fmk_of_own {P : FProp} {U : UpperSet (BoundedFootprintSpace Bool)}
    (h : ∀ a, ✓a → (own a ⊢ P) → a ∈ U) : P ⊢ (fmk U : FProp) := by
  induction P using Quotient.ind with
  | _ P =>
  intro a hva ha
  exact h a hva (by rw [own_def]; exact fun _ _ hb ↦ P.upper' (UpperSetBI.mem_own.1 hb) ha)

/-- An entailment, checked on the resources that own its premise. -/
lemma entails_of_own {P Q : FProp} (h : ∀ a, ✓a → (own a ⊢ P) → own a ⊢ Q) : P ⊢ Q := by
  induction P using Quotient.ind with
  | _ P =>
  induction Q using Quotient.ind with
  | _ Q =>
  intro a hva ha
  have hQ := h a hva (by rw [own_def]; exact fun _ _ hb ↦ P.upper' (UpperSetBI.mem_own.1 hb) ha)
  rw [own_def] at hQ
  exact hQ a hva (UpperSetBI.mem_own.2 (le_refl a))

lemma own_mono {x y : BoundedFootprintSpace Bool} (h : x ≤ y) : own y ⊢ own x := by
  rw [own_def, own_def]
  exact fun _ _ ha ↦ UpperSetBI.mem_own.2 (le_trans h (UpperSetBI.mem_own.1 ha))

/-- Owning a resource above a space's own resource owns the space. -/
lemma own_entails_ownP {p : PSpace Ω} {hp : HasBoundedFootprint (p : PSp Ω)}
    {r : BoundedFootprintSpace Bool}
    (h : (⟨(p : PSp Ω), hp⟩ : BoundedFootprintSpace Bool) ≤ r) : own r ⊢ ownP p := by
  rw [ownP_def]
  exact entails_trans (own_mono h)
    (exists_intro (Ψ := fun h' : HasBoundedFootprint (p : PSp Ω) ↦
      own (⟨(p : PSp Ω), h'⟩ : BoundedFootprintSpace Bool)) hp)

lemma own_mul_sep {x y : BoundedFootprintSpace Bool} : own (x * y) ⊢ iprop(own x ∗ own y) := by
  rw [own_def, own_def, own_def]
  exact fun _ _ ha ↦ UpperSetBI.mem_sep.2 ⟨x, y, UpperSetBI.mem_own.1 ha,
    UpperSetBI.mem_own.2 (le_refl x), UpperSetBI.mem_own.2 (le_refl y)⟩

/-- Splitting `own M ∗ W` semantically: `M` and a resource owning `W`. -/
lemma own_sep_entails_fmk {M : BoundedFootprintSpace Bool} {W : FProp}
    {U : UpperSet (BoundedFootprintSpace Bool)}
    (h : ∀ a R, ✓a → M * R ≤ a → (own R ⊢ W) → a ∈ U) :
    iprop(own M ∗ W) ⊢ (fmk U : FProp) := by
  rw [own_def]
  induction W using Quotient.ind with
  | _ W =>
  intro a hva hsep
  obtain ⟨b₁, b₂, hle, hb₁, hb₂⟩ := UpperSetBI.mem_sep.1 hsep
  exact h a b₂ hva (le_trans (mul_le_mul_right_le (UpperSetBI.mem_own.1 hb₁) b₂) hle)
    (by rw [own_def]; exact fun _ _ hb ↦ W.upper' (UpperSetBI.mem_own.1 hb) hb₂)

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
    (h : own b ⊢ iprop(P ∨ R)) : (own b ⊢ P) ∨ (own b ⊢ R) := by
  induction P using Quotient.ind with
  | _ P =>
  induction R using Quotient.ind with
  | _ R =>
  rw [own_def] at h ⊢
  rcases UpperSetBI.mem_or.1 (h b hv (UpperSetBI.mem_own.2 (le_refl b))) with hP | hR
  · exact Or.inl fun _ _ hy ↦ P.upper' (UpperSetBI.mem_own.1 hy) hP
  · exact Or.inr fun _ _ hy ↦ R.upper' (UpperSetBI.mem_own.1 hy) hR

/-- Owning a resource that satisfies an existential satisfies one of its instances. -/
lemma own_exists_elim {γ : Type} {P : γ → FProp} {b : BoundedFootprintSpace Bool} (hv : ✓b)
    (h : own b ⊢ iprop(∃ x, P x)) : ∃ x, own b ⊢ P x := by
  rw [own_def] at h ⊢
  obtain ⟨U, hU⟩ : ∃ U : γ → UpperSet (BoundedFootprintSpace Bool), P = fun x ↦ fmk (U x) := by
    choose U hU using fun x ↦ Quotient.exists_rep (P x)
    exact ⟨U, funext fun x ↦ (hU x).symm⟩
  subst hU
  obtain ⟨q, ⟨x, hq⟩, hqb⟩ := UpperSetBI.mem_sExists.1 (h b hv (UpperSetBI.mem_own.2 (le_refl b)))
  exact ⟨x, fun y hvy hy ↦ (Quotient.exact hq).2 y hvy (q.upper' (UpperSetBI.mem_own.1 hy) hqb)⟩

end

end Foxglove
