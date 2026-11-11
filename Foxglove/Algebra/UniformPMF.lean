module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! # Uniform laws as `PMF`s

Mathlib (since 2026-10-04) states its uniform distributions as measures
(`Measure.uniformOfFinset`).  Foxglove's laws are `PMF`s, so the two `PMF`-valued uniform laws
it uses are kept here: `PMF.uniformOfFinset`, which Mathlib no longer defines, and
`PMF.uniformOfFintype'`, primed because Mathlib's `PMF.uniformOfFintype` is now a deprecated
alias of the measure. -/

@[expose] public section

open scoped ENNReal
open Finset

namespace PMF

variable {α : Type*}

/-- The uniform law on a nonempty finset. -/
noncomputable def uniformOfFinset (s : Finset α) (hs : s.Nonempty) : PMF α := by
  classical
  refine ofFinset (fun a ↦ if a ∈ s then (#s : ℝ≥0∞)⁻¹ else 0) s ?_ fun x hx ↦ by simp [hx]
  simp [ENNReal.mul_inv_cancel, hs.ne_empty]

open scoped Classical in
@[simp]
theorem uniformOfFinset_apply {s : Finset α} (hs : s.Nonempty) (a : α) :
    uniformOfFinset s hs a = if a ∈ s then (#s : ℝ≥0∞)⁻¹ else 0 :=
  rfl

/-- The uniform law on a finite, nonempty type.  Primed because Mathlib's `PMF.uniformOfFintype`
is now a deprecated alias of the measure `Measure.uniformOfFinset`. -/
noncomputable def uniformOfFintype' (α : Type*) [Fintype α] [Nonempty α] : PMF α :=
  uniformOfFinset Finset.univ Finset.univ_nonempty

@[simp]
theorem uniformOfFintype'_apply [Fintype α] [Nonempty α] (a : α) :
    uniformOfFintype' α a = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  simp [uniformOfFintype']

end PMF
