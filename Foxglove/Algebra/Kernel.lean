module

public import Foxglove.Algebra.PMF
public import Foxglove.Basic

@[expose] public section
namespace Foxglove

open ProbSpace
open Iris OrderedUnitalResourceAlgebra
open UpperSetBI
open ProbabilityTheory MeasureTheory

attribute [local aesop simp] Equivalence.refl Equivalence.trans Equivalence.symm

noncomputable section

/-! # Kernels between probability spaces

A kernel on a space `p` sends each value to a measure on `p`'s σ-algebra; the fibres of a
conditioning are such a kernel. -/

/-- A Markov kernel from a type (with the full σ-algebra) into the σ-algebra of `p`. -/
abbrev _root_.ProbabilityTheory.TrivialMarkovKernel (A : Type) (p : PSpace Ω) : Type :=
  {κ : @Kernel A Ω ⊤ p.ms // IsMarkovKernel κ}

/-- The fibre of a kernel at a value, as a probability space on `p`'s σ-algebra. -/
def _root_.ProbabilityTheory.Kernel.toPSpace {A : Type} {p : PSpace Ω}
  (κ : TrivialMarkovKernel A p) : A → PSpace Ω :=
  fun a ↦ ⟨⟨p.ms, κ.1 a⟩, have := κ.2; inferInstance⟩

open ProbabilityTheory.Kernel in
instance {A : Type} {p : PSpace Ω} : FunLike (TrivialMarkovKernel A p) A (PSpace Ω) :=
  ⟨
    fun κ ↦ toPSpace κ,
    by unfold toPSpace
       intros κ a₂ f
       erw [funext_iff] at f
       aesop
  ⟩

/-- The kernel that ignores its input and hands back the trivial space. -/
def unitKernel (A : Type) : TrivialMarkovKernel A (1 : PSpace Ω) :=
  ⟨@Kernel.const A Ω ⊤ (1 : PSpace Ω).ms (1 : PSpace Ω).μ,
    have := (1 : PSpace Ω).2; inferInstance⟩

set_option linter.style.haveILetI false in
open ProbabilityTheory MeasureTheory in
/-- A fibre of a conditioning kernel is absolutely continuous w.r.t. the mixture, at any
value in the support. -/
theorem kernel_fibre_ac {A : Type} {μ : PMF A} {m : PSpace Ω}
    (κ : TrivialMarkovKernel A m) (hmix : m.μ = (μ.toMeasureWithMs ⊤).bind κ)
    {v : A} (hv : v ∈ μ.support) : (κ.1 v) ≪ m.μ := by
  letI : MeasurableSpace A := ⊤
  have hmeas : ∀ F, MeasurableSet[m.ms] F → m.μ F = 0 → (κ.1 v) F = 0 := by
    intro F hF h0
    rw [hmix, Measure.bind_apply hF (Kernel.measurable κ.1).aemeasurable,
      lintegral_eq_zero_iff (Kernel.measurable_coe κ.1 hF)] at h0
    by_contra hne
    have hsub : ({v} : Set A) ⊆ {a | κ.1 a F ≠ 0} := by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hne
    have hz : (μ.toMeasureWithMs ⊤) {v} = 0 := measure_mono_null hsub h0
    rw [PMF.toMeasureWithMs, @PMF.toMeasure_apply_singleton A ⊤ μ v (by trivial)] at hz
    exact (PMF.mem_support_iff μ v).mp hv hz
  intro F h0
  obtain ⟨F', hFF', hF'meas, hF'0⟩ := @exists_measurable_superset_of_null Ω m.ms m.μ F h0
  exact measure_mono_null hFF' (hmeas F' hF'meas hF'0)

set_option linter.style.haveILetI false in
/-- Binding a PMF against a kernel, read off on the support. -/
lemma bind_apply_support {β : Type} {ms : MeasurableSpace Ω} (μ : PMF β)
    (κ : @Kernel β Ω ⊤ ms) {G : Set Ω} (hG : MeasurableSet[ms] G) :
    ((μ.toMeasureWithMs ⊤).bind κ) G = ∑' i : μ.support, μ i * κ i G := by
  letI : MeasurableSpace β := ⊤
  haveI : MeasurableSingletonClass β := ⟨fun _ ↦ trivial⟩
  rw [Measure.bind_apply hG (Kernel.measurable κ).aemeasurable, PMF.toMeasureWithMs,
    ← PMF.restrict_toMeasure_support, lintegral_countable _ μ.support_countable]
  refine tsum_congr fun i ↦ ?_
  rw [PMF.toMeasure_apply_singleton μ i (measurableSet_singleton _), mul_comm]

end

end Foxglove
