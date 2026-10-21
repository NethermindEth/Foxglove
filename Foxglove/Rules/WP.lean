module

public import Foxglove.Rules.Conditioning
public import Foxglove.Rules.Distribution

@[expose] public section
namespace Foxglove

open ProbSpace
open Iris OrderedUnitalResourceAlgebra
open UpperSetBI
open Iris BI UpperSetBI OURAProp
open Interp Interp.ProbTree MeasureTheory

noncomputable section

/-! # Weakest precondition

Facts about runs that the `wp` rules consume. -/

/-- **A run lands in a defined space.**  `bigStep` takes its valid branch and `ofTree`
always carries a `some`, so the output footprint is never `⊤`.  This is what lets the
witness of a run be known valid, which `WP_FRAME` needs. -/
lemma valid_run {α : Type} [Inhabited α] {m : Type → Type} [Interp.BernoulliInterpretable m]
    (t : m α) (μ₀ : BoundedFootprintPsp) (hv : ✓μ₀.psp) :
    ✓((run t μ₀).1.toSpace) := by
  show ((run t μ₀).1.psp) ≠ (⊤ : PSp Ω)
  rw [run, bigStep, dite_eq_left hv, ofTree_psp']
  exact Option.some_ne_none _

/-- Where a tilt of an atomic space gives an atom no mass: the atom had none, or the density
vanishes there.  The density is measurable for the atoms, so it is constant on each. -/
lemma withDensity_atom_eq_zero_iff (b : Interp.ProbTree.BoundedFootprintPsp) (h : ✓b.psp)
    {g : Ω → ENNReal} (hg : Measurable[(ValidPSp.toPSpace ⟨b.psp, h⟩).ms] g) (ρ : Ω) :
    ((ValidPSp.toPSpace ⟨b.psp, h⟩).μ.withDensity g) (b.atomOf ρ).1 = 0
      ↔ (ValidPSp.toPSpace ⟨b.psp, h⟩).μ (b.atomOf ρ).1 = 0 ∨ g ρ = 0 := by
  have hA : MeasurableSet[(ValidPSp.toPSpace ⟨b.psp, h⟩).ms] (b.atomOf ρ).1 :=
    b.measurable _ (b.atomOf ρ).2 h
  have hsupp : MeasurableSet[(ValidPSp.toPSpace ⟨b.psp, h⟩).ms] (Function.support g) :=
    hg (measurableSet_singleton (0 : ENNReal)).compl
  rw [withDensity_apply _ hA]
  refine not_iff_not.mp ?_
  rw [not_or]
  show ∫⁻ x in (b.atomOf ρ).1, g x ∂(ValidPSp.toPSpace ⟨b.psp, h⟩).μ ≠ 0
    ↔ (ValidPSp.toPSpace ⟨b.psp, h⟩).μ (b.atomOf ρ).1 ≠ 0 ∧ g ρ ≠ 0
  rw [← pos_iff_ne_zero, setLIntegral_pos_iff hg, pos_iff_ne_zero]
  by_cases hρ : g ρ = 0
  · have hsub : (b.atomOf ρ).1 ⊆ (Function.support g)ᶜ :=
      Interp.ProbTree.atom_subset_of_mem b h hsupp.compl (fun hs ↦ hs hρ)
    have hempty : Function.support g ∩ (b.atomOf ρ).1 = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro x ⟨hx1, hx2⟩
      exact hsub hx2 hx1
    rw [hempty, measure_empty]
    simp [hρ]
  · have hsub : (b.atomOf ρ).1 ⊆ Function.support g :=
      Interp.ProbTree.atom_subset_of_mem b h hsupp hρ
    rw [Set.inter_eq_right.mpr hsub]
    simp [hρ]

end

end Foxglove
