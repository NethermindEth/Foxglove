module

public import Foxglove.Algebra.MeasureOnSpace

@[expose] public section
namespace Foxglove

open ProbSpace
open Iris OrderedUnitalResourceAlgebra
open UpperSetBI
open MeasureTheory

variable {α β : Type}

noncomputable section

/-! # Probability mass functions

The measure of a `PMF` on the full σ-algebra, products, and integration against a `PMF`. -/

/-- The measure of a `PMF`, on a chosen σ-algebra. -/
def _root_.PMF.toMeasureWithMs {A : Type} (μ : PMF A) (ms : MeasurableSpace A) : @MeasureTheory.Measure A ms :=
  @μ.toMeasure A ms

/-- The Dirac distribution. -/
abbrev δ {A : Type} (v : A) : PMF A := PMF.pure v

/-- The product of two laws. -/
noncomputable
def product (μ₁ : PMF α) (μ₂ : PMF β) : PMF (α × β) :=
  let prf : HasSum (fun (a, b) => μ₁ a * μ₂ b) 1 := (by
      have h : ∑' (p : α × β), μ₁ p.1 * μ₂ p.2 = 1 := by
        simp_rw [ENNReal.tsum_prod', ENNReal.tsum_mul_left, ENNReal.tsum_mul_right,
          PMF.tsum_coe, mul_one]
      convert h ▸ ENNReal.summable.hasSum)
  ⟨fun ((a, b) : (α × β)) => μ₁ a * μ₂ b, prf⟩

scoped infix:69 " ⊗ " => product

lemma product_apply (μ₁ : PMF α) (μ₂ : PMF β) (a : α) (b : β) :
    (μ₁ ⊗ μ₂) (a, b) = μ₁ a * μ₂ b := rfl

set_option linter.style.haveILetI false in
/-- The product law gives a rectangle the product of the marginal masses. -/
lemma product_toMeasure_prod (μ₁ : PMF α) (μ₂ : PMF β) (A : Set α) (B : Set β) :
    (μ₁ ⊗ μ₂).toMeasureWithMs ⊤ (A ×ˢ B) = μ₁.toMeasureWithMs ⊤ A * μ₂.toMeasureWithMs ⊤ B := by
  letI : MeasurableSpace α := ⊤
  letI : MeasurableSpace β := ⊤
  letI : MeasurableSpace (α × β) := ⊤
  show (μ₁ ⊗ μ₂).toMeasure (A ×ˢ B) = μ₁.toMeasure A * μ₂.toMeasure B
  rw [PMF.toMeasure_apply _ MeasurableSpace.measurableSet_top,
    PMF.toMeasure_apply _ MeasurableSpace.measurableSet_top,
    PMF.toMeasure_apply _ MeasurableSpace.measurableSet_top,
    ENNReal.tsum_prod', ← ENNReal.tsum_mul_right]
  refine tsum_congr fun a ↦ ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun b ↦ ?_
  by_cases ha : a ∈ A <;> by_cases hb : b ∈ B <;> simp [Set.indicator, ha, hb, product_apply]

set_option linter.style.haveILetI false in
open MeasureTheory in
/-- A PMF's measure lives on the PMF's support. -/
lemma ae_mem_support (μ : PMF α) : ∀ᵐ v ∂(μ.toMeasureWithMs ⊤), v ∈ μ.support := by
  letI : MeasurableSpace α := ⊤
  rw [ae_iff]
  exact (μ.toMeasure_apply_eq_zero_iff MeasurableSpace.measurableSet_top).2
    (Set.disjoint_left.2 fun _ hv hv' ↦ hv' hv)

set_option linter.style.haveILetI false in
open MeasureTheory in
/-- Integrating against a PMF is summing over its (countable) support. -/
lemma pmf_lintegral_eq_tsum {γ : Type} (ν : PMF γ) (F : γ → ENNReal) :
    ∫⁻ v, F v ∂(ν.toMeasureWithMs ⊤) = ∑' v : ν.support, F v * ν v := by
  letI : MeasurableSpace γ := ⊤
  show ∫⁻ v, F v ∂ν.toMeasure = _
  rw [← ν.restrict_toMeasure_support, lintegral_countable _ ν.support_countable]
  refine tsum_congr fun v ↦ ?_
  rw [PMF.toMeasure_apply_singleton _ _ MeasurableSpace.measurableSet_top]

open MeasureTheory in
/-- Integrals against a PMF commute with integrals against any measure. -/
lemma lintegral_pmf_swap {γ X : Type} {_ : MeasurableSpace X} (ν : PMF γ) (κ : Measure X)
    (g : γ → X → ENNReal) (hg : ∀ v, AEMeasurable (g v) κ) :
    ∫⁻ v, ∫⁻ x, g v x ∂κ ∂(ν.toMeasureWithMs ⊤)
      = ∫⁻ x, ∫⁻ v, g v x ∂(ν.toMeasureWithMs ⊤) ∂κ := by
  have := ν.support_countable.to_subtype
  simp_rw [pmf_lintegral_eq_tsum]
  rw [lintegral_tsum (f := fun (v : ν.support) x ↦ g v x * ν v) fun v ↦ (hg v).mul_const _]
  exact tsum_congr fun v ↦ (lintegral_mul_const'' _ (hg v)).symm

set_option linter.style.haveILetI false in
open MeasureTheory in
/-- Each fibre of a PMF mixture, at a point of the PMF's support, is absolutely continuous
with respect to the mixture. -/
lemma bind_fibre_ac {γ X : Type} {_ : MeasurableSpace X} {ν : PMF γ} {μX : Measure X}
    {lam : γ → Measure X} (h : μX = (ν.toMeasureWithMs ⊤).bind lam) {v : γ}
    (hv : v ∈ ν.support) : lam v ≪ μX := by
  letI : MeasurableSpace γ := ⊤
  intro F hF
  obtain ⟨N, hFN, hNmeas, hN⟩ := exists_measurable_superset_of_null hF
  refine measure_mono_null hFN ?_
  rw [h, Measure.bind_apply hNmeas measurable_from_top.aemeasurable, pmf_lintegral_eq_tsum] at hN
  exact (mul_eq_zero.1 (ENNReal.tsum_eq_zero.1 hN ⟨v, hv⟩)).resolve_right
    ((PMF.mem_support_iff _ _).1 hv)

set_option linter.style.haveILetI false in
open MeasureTheory in
/-- A PMF's `bind` becomes the measures' `bind`. -/
lemma toMeasure_bind_eq {γ δ : Type} (p : PMF γ) (f : γ → PMF δ) :
    (p.bind f).toMeasureWithMs ⊤
      = (p.toMeasureWithMs ⊤).bind fun a ↦ (f a).toMeasureWithMs ⊤ := by
  letI : MeasurableSpace γ := ⊤
  letI : MeasurableSpace δ := ⊤
  ext s hs
  rw [Measure.bind_apply hs measurable_from_top.aemeasurable, pmf_lintegral_eq_tsum]
  show (p.bind f).toMeasure s = _
  have hsub : Function.support (fun a ↦ p a * (f a).toMeasure s) ⊆ p.support := fun a ha ↦
    (PMF.mem_support_iff _ _).2 (left_ne_zero_of_mul ha)
  rw [PMF.toMeasure_bind_apply p f s hs, ← tsum_subtype_eq_of_support_subset hsub]
  exact tsum_congr fun a ↦ mul_comm _ _

set_option linter.style.haveILetI false in
open MeasureTheory in
/-- Integrating against the joint law of a pair is integrating out each component in turn. -/
lemma lintegral_pmf_bind_pair {γ δ : Type} (p : PMF γ) (κ : γ → PMF δ) (F : γ × δ → ENNReal) :
    ∫⁻ x, F x ∂((p.bind fun v ↦ (κ v).bind fun w ↦ PMF.pure (v, w)).toMeasureWithMs ⊤)
      = ∫⁻ v, ∫⁻ w, F (v, w) ∂((κ v).toMeasureWithMs ⊤) ∂(p.toMeasureWithMs ⊤) := by
  letI : MeasurableSpace γ := ⊤
  letI : MeasurableSpace δ := ⊤
  letI : MeasurableSpace (γ × δ) := ⊤
  rw [toMeasure_bind_eq,
    Measure.lintegral_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
  refine lintegral_congr fun v ↦ ?_
  rw [toMeasure_bind_eq,
    Measure.lintegral_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
  refine lintegral_congr fun w ↦ ?_
  show ∫⁻ x, F x ∂(PMF.pure (v, w)).toMeasure = F (v, w)
  rw [PMF.toMeasure_pure, lintegral_dirac' _ measurable_from_top]

/-- The pushforward `μ ∘ f⁻¹` of a law along `f`, as Bluebell writes it. -/
scoped syntax:max (name := pmfStx) term:max " ∘ " ident "⁻¹" : term

scoped macro_rules (kind := pmfStx)
  | `($μ ∘ $f:ident⁻¹) => `(PMF.map $f $μ)

/-- The first projection, as a name so that `μ ∘ π₁⁻¹` is the marginal. -/
abbrev π₁ {α β : Type} : α × β → α := Prod.fst

/-- Fusing a law with a kernel: the law of the pair `(v, w)` with `v ← μ`, `w ← κ v`. -/
noncomputable def fuse (μ : PMF α) (κ : α → PMF β) : PMF (α × β) :=
  ⟨fun (v, w) => μ v * (κ v w), by
    have h : ∑' (p : α × β), μ p.1 * κ p.1 p.2 = 1 := by
      simp_rw [ENNReal.tsum_prod', ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one, PMF.tsum_coe]
    convert h ▸ ENNReal.summable.hasSum⟩

scoped infix:69 " -< " => fuse

/-- Fusing is binding: draw `v` from `μ`, then `w` from `κ v`, and report the pair. -/
lemma fuse_eq_bind {μ : PMF α} {κ : α → PMF β} :
    (μ -< κ) = μ.bind fun v ↦ (κ v).map fun w ↦ (v, w) := by
  ext ⟨a, b⟩
  rw [PMF.bind_apply, tsum_eq_single a]
  · rw [PMF.map_apply, tsum_eq_single b]
    · simp only [if_true]
      rfl
    · intro w hw
      simp [Ne.symm hw]
  · intro v hv
    rw [PMF.map_apply]
    simp [Ne.symm hv]


end

end Foxglove
