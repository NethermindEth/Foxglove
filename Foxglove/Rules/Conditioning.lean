module

public import Foxglove.Rules.Sure

public section
namespace Foxglove

open ProbSpace
open Iris OrderedUnitalResourceAlgebra
open UpperSetBI
open Iris BI UpperSetBI OURAProp

noncomputable section

/-! # Joint conditioning

What `𝒞⟨μ⟩ v; K v` satisfies at the level of resources: monotonicity, framing, and how a
conditioning is unpacked into a mixture of fibres (`cond_elim`).  `valuePost` is a
conditioning on a law, so it is read off a resource the same way (`valuePost_elim`). -/

lemma sat_jointConditioning {A : Type} {μ : PMF A} {K : A → FProp}
    {r : BoundedFootprintSpace Bool} :
    (jointConditioning μ K).Sat r ↔ ✓r ∧ ∃ (m : PSpace Ω)
      (κ : ProbabilityTheory.TrivialMarkovKernel A m) (hbf : HasBoundedFootprint (m : PSp Ω))
      (c : BoundedFootprintSpace Bool),
      (⟨(m : PSp Ω), hbf⟩ : BoundedFootprintSpace Bool) * c ≤ r ∧
      m.μ = (μ.toMeasureWithMs ⊤).bind κ ∧
      ∀ v : μ.support, (iprop(ownP (κ v) -∗ K v) : FProp).Sat c := by
  rw [jointConditioning_def]
  constructor
  · intro h
    obtain ⟨m, h⟩ := sat_exists.1 h
    obtain ⟨κ, h⟩ := sat_exists.1 h
    obtain ⟨hv, b₁, b₂, hle, hown, hrest⟩ := sat_sep.1 h
    obtain ⟨_, hbf, hmb₁⟩ := sat_ownP.1 hown
    obtain ⟨_, c₁, c₂, hle', hmix, hall⟩ := sat_sep.1 hrest
    have hc₂b₂ : c₂ ≤ b₂ := le_trans (by rw [mul_comm]; exact le_mul_of_one_le PSp.one_le) hle'
    exact ⟨hv, m, κ, hbf, c₂,
      le_trans (mul_le_mul_right_le hmb₁ c₂) (le_trans (mul_le_mul_left_le hc₂b₂ b₁) hle),
      (sat_pure.1 hmix).2, (sat_forall.1 hall).2⟩
  · rintro ⟨hv, m, κ, hbf, c, hle, hmix, hall⟩
    have hvmc := valid_mono hle hv
    exact sat_exists.2 ⟨m, sat_exists.2 ⟨κ, sat_sep.2 ⟨hv, _, _, hle,
      sat_ownP.2 ⟨valid_mul_l hvmc, hbf, le_refl _⟩,
      sat_sep.2 ⟨valid_mul_r hvmc, 1, c, le_of_eq (one_mul c), sat_pure.2 ⟨valid_one, hmix⟩,
        sat_forall.2 ⟨valid_mul_r hvmc, hall⟩⟩⟩⟩⟩

set_option linter.style.haveILetI false in
open MeasureTheory in
/-- **Unpacking a conditioning.**  A valid resource owning `𝒞⟨ν⟩ v; Kc v` contains a space
`s` that is the `ν`-mixture of probability fibres `w v`; on the support, each fibre is owned
(as a resource `X`) in a way satisfying `Kc v`.  The space is the conditioned space times the
continuation's frame, and the fibres are its tilts along the kernel. -/
theorem cond_elim {γ : Type} {ν : PMF γ} {Kc : γ → FProp} {r : BoundedFootprintSpace Bool}
    (hv : ✓r) (h : own r ⊢ jointConditioning ν Kc) :
    ∃ (s : PSpace Ω) (hbfs : HasBoundedFootprint (s : PSp Ω)),
      (⟨(s : PSp Ω), hbfs⟩ : BoundedFootprintSpace Bool) ≤ r ∧
      ∃ w : γ → {p : Measure[s.ms] Ω // IsProbabilityMeasure p},
        s.μ = (ν.toMeasureWithMs ⊤).bind (fun v ↦ (w v).1) ∧
        ∀ v ∈ ν.support, ∃ X : BoundedFootprintSpace Bool,
          X.val = ((show PSpace Ω from ⟨⟨s.ms, (w v).1⟩, (w v).2⟩) : PSp Ω) ∧
            (own X ⊢ Kc v) := by
  classical
  -- `m` and the continuation's frame `c₂` compose, as in `C_FALSE`
  obtain ⟨-, m, ℓ, hbfm, c₂, hmc₂r, hmix, hall⟩ :=
    sat_jointConditioning.1 (sat_of_own_entails hv h)
  have hvmc₂ : ✓((⟨(m : PSp Ω), hbfm⟩ : BoundedFootprintSpace Bool) * c₂) :=
    valid_mono hmc₂r hv
  have hvc₂ : ✓c₂ := valid_mul_r hvmc₂
  obtain ⟨c₂', hc₂'⟩ : ∃ c : PSpace Ω, c₂.val = (c : PSp Ω) :=
    Option.ne_none_iff_exists'.mp (PSp.valid_def.mp hvc₂)
  obtain ⟨s, hs⟩ : ∃ s : PSpace Ω, PSp.mul ((m : PSp Ω)) (c₂.val) = (s : PSp Ω) :=
    Option.ne_none_iff_exists'.mp (PSp.valid_def.mp hvmc₂)
  have hbfs : HasBoundedFootprint (s : PSp Ω) := by
    have h := ((⟨(m : PSp Ω), hbfm⟩ : BoundedFootprintSpace Bool) * c₂).property
    rwa [show ((⟨(m : PSp Ω), hbfm⟩ : BoundedFootprintSpace Bool) * c₂).val
      = (s : PSp Ω) from hs] at h
  have hsr : (⟨(s : PSp Ω), hbfs⟩ : BoundedFootprintSpace Bool) ≤ r := by
    have h : ((⟨(m : PSp Ω), hbfm⟩ : BoundedFootprintSpace Bool) * c₂).val ≤ r.val := hmc₂r
    rw [show ((⟨(m : PSp Ω), hbfm⟩ : BoundedFootprintSpace Bool) * c₂).val
      = (s : PSp Ω) from hs] at h
    exact h
  rw [hc₂'] at hs
  have hcomm : s =ᵢ c₂' ⊕ᵢ m := independentProduct_comm (PSp.mul_inversion hs)
  have hcp := c₂'.2
  have hsp : IsProbabilityMeasure s.μ := PSpace.isProbability
  have hms : m ≤ s := PSpace.le_of_isIndependentProduct_right hcomm
  -- the fibres: tilt `s` along the kernel (on the support)
  let wμ : γ → Measure[s.ms] Ω := fun v ↦
    if v ∈ ν.support then s.μ.withDensity ((ℓ.1 v).rnDeriv m.μ) else s.μ
  have hrect : ∀ v ∈ ν.support, ∀ E F, @MeasurableSet Ω c₂'.ms E → @MeasurableSet Ω m.ms F →
      wμ v (E ∩ F) = c₂'.μ E * ℓ.1 v F := fun v hv E F hE hF ↦ by
    haveI : IsProbabilityMeasure (ℓ.1 v) := ℓ.2.isProbabilityMeasure v
    simp only [wμ, hv, ↓reduceIte]
    exact reweight_rect hcomm (ℓ.1 v) (bind_fibre_ac hmix hv) hE hF
  have hwprob : ∀ v, IsProbabilityMeasure (wμ v) := fun v ↦ by
    by_cases hv : v ∈ ν.support
    · haveI : IsProbabilityMeasure (ℓ.1 v) := ℓ.2.isProbabilityMeasure v
      constructor
      have h := hrect v hv Set.univ Set.univ MeasurableSet.univ MeasurableSet.univ
      rw [Set.inter_univ] at h
      rw [h, measure_univ, measure_univ, one_mul]
    · simp only [wμ, hv, ↓reduceIte]
      exact hsp
  let w : γ → {p : Measure[s.ms] Ω // IsProbabilityMeasure p} := fun v ↦ ⟨wμ v, hwprob v⟩
  refine ⟨s, hbfs, hsr, w, ?_, fun v hv ↦ ?_⟩
  · -- `s` is the mixture of its tilts
    have hsupp := ae_mem_support ν
    letI : MeasurableSpace γ := ⊤
    refine @Measure.ext Ω s.ms _ _ fun A hA ↦ ?_
    rw [Measure.bind_apply hA measurable_from_top.aemeasurable,
      mixture_of_tilts hms ν (fun v ↦ ℓ.1 v) (fun v ↦ ℓ.2.isProbabilityMeasure v) hmix hA]
    refine lintegral_congr_ae ?_
    filter_upwards [hsupp] with v hv
    show _ = wμ v A
    simp only [wμ, hv, ↓reduceIte]
  · -- the fibre at `v` is owned with the frame, which the continuation turns into `Kc v`
    haveI : IsProbabilityMeasure (ℓ.1 v) := ℓ.2.isProbabilityMeasure v
    let S : PSpace Ω := ⟨⟨s.ms, (w v).1⟩, (w v).2⟩
    have hS : S =ᵢ c₂' ⊕ᵢ (ℓ v : PSpace Ω) := by
      refine PSpace.isIndependentProduct_def.2 ⟨?_, fun E hE F hF ↦ ?_⟩
      · simp only [S, PSpace.ms_mk, ProbabilityTheory.TrivialMarkovKernel.ms_apply]
        exact (PSpace.isIndependentProduct_def.1 hcomm).1
      · rw [ProbabilityTheory.TrivialMarkovKernel.ms_apply] at hF
        simp only [S, PSpace.μ_mk_apply, ProbabilityTheory.TrivialMarkovKernel.μ_apply]
        exact hrect v hv E F hE hF
    have hvm : ✓((m : PSp Ω)) := PSp.valid_def.mpr (Option.some_ne_none _)
    have hvk : ✓(((ℓ v : PSpace Ω)) : PSp Ω) := PSp.valid_def.mpr (Option.some_ne_none _)
    have hbfk : HasBoundedFootprint (((ℓ v : PSpace Ω)) : PSp Ω) :=
      hasBoundedFootprint_congr hvm hvk (by
        rw [ValidPSp.toPSpace_eq hvm rfl, ValidPSp.toPSpace_eq hvk rfl,
          ProbabilityTheory.TrivialMarkovKernel.ms_apply]) hbfm
    have hval : (c₂ * (⟨((ℓ v : PSpace Ω) : PSp Ω), hbfk⟩ : BoundedFootprintSpace Bool)).val
        = (S : PSp Ω) := by
      show PSp.mul c₂.val _ = _
      rw [hc₂']
      exact PSp.mul_respect_independentProduct hS
    have hvalid : ✓(c₂ * (⟨((ℓ v : PSpace Ω) : PSp Ω), hbfk⟩ : BoundedFootprintSpace Bool)) := by
      show (c₂ * _).val ≠ (⊤ : PSp Ω)
      rw [hval]
      exact WithTop.coe_ne_top
    have hmem := (sat_wand.1 (hall ⟨v, hv⟩)).2 _ hvalid (sat_ownP.2 ⟨valid_mul_r hvalid, hbfk,
      le_refl (⟨((ℓ v : PSpace Ω) : PSp Ω), hbfk⟩ : BoundedFootprintSpace Bool)⟩)
    exact ⟨_, hval, own_entails_of_sat hmem⟩

/-- `valuePost` at a given law `ν` of `X`: on the fibre at `x` the result surely is `x` and
`Q x` holds.  `valuePost X Q` is `∃ ν, condValue ν X Q`. -/
def condValue {α : Type} (ν : PMF α) (X : RV α) (Q : α → FProp) : FProp :=
  𝒞⟨ν⟩ x; (⌈fun ρ ↦ X ρ = x⌉ ∗ Q x)

lemma condValue_def {α : Type} (ν : PMF α) (X : RV α) (Q : α → FProp) :
    condValue ν X Q = (𝒞⟨ν⟩ x; (⌈fun ρ ↦ X ρ = x⌉ ∗ Q x)) := by
  rfl

/-- What owning a resource that satisfies `condValue ν X K` provides: the conditioned space
as a `ν`-mixture of a kernel, whose fibres each make `X` sure and carry `K` of that value. -/
lemma condValue_elim {β : Type} {X : RV β} {K : β → FProp} {ν : PMF β}
    {b : BoundedFootprintSpace Bool} (hv : ✓b) (h : own b ⊢ condValue ν X K) :
    ∃ (mm : PSpace Ω) (hbf : HasBoundedFootprint (mm : PSp Ω))
      (κ : ProbabilityTheory.TrivialMarkovKernel β mm) (R : BoundedFootprintSpace Bool),
      mm.μ = (ν.toMeasureWithMs ⊤).bind κ ∧
      (⟨(mm : PSp Ω), hbf⟩ : BoundedFootprintSpace Bool) * R ≤ b ∧
      ∀ v ∈ ν.support, ∀ hk : HasBoundedFootprint ((κ v : PSpace Ω) : PSp Ω),
        own (R * ⟨((κ v : PSpace Ω) : PSp Ω), hk⟩) ⊢ iprop(⌈fun ρ ↦ X ρ = v⌉ ∗ K v) := by
  rw [condValue_def] at h
  obtain ⟨-, mm, κ, hbfm, c₂, hle, hmix, hall⟩ :=
    sat_jointConditioning.1 (sat_of_own_entails hv h)
  refine ⟨mm, hbfm, κ, c₂, hmix, hle, fun v hv' hk ↦ entails_iff.2 fun y hy ↦ ?_⟩
  obtain ⟨hvy, hc₂Ky⟩ := sat_own.1 hy
  have hvc₂K : ✓(c₂ * ⟨((κ v : PSpace Ω) : PSp Ω), hk⟩) := valid_mono hc₂Ky hvy
  have hmem := (sat_wand.1 (hall ⟨v, hv'⟩)).2 _ hvc₂K (sat_ownP.2 ⟨valid_mul_r hvc₂K, hk,
    le_refl (⟨((κ v : PSpace Ω) : PSp Ω), hk⟩ : BoundedFootprintSpace Bool)⟩)
  exact sat_mono hmem hc₂Ky hvy

/-- What owning a resource that satisfies `valuePost X K` provides: `condValue_elim` at the
law the resource conditions on. -/
lemma valuePost_elim {β : Type} {X : RV β} {K : β → FProp} {b : BoundedFootprintSpace Bool}
    (hv : ✓b) (h : own b ⊢ valuePost X K) :
    ∃ (ν : PMF β) (mm : PSpace Ω) (hbf : HasBoundedFootprint (mm : PSp Ω))
      (κ : ProbabilityTheory.TrivialMarkovKernel β mm) (R : BoundedFootprintSpace Bool),
      mm.μ = (ν.toMeasureWithMs ⊤).bind κ ∧
      (⟨(mm : PSp Ω), hbf⟩ : BoundedFootprintSpace Bool) * R ≤ b ∧
      ∀ v ∈ ν.support, ∀ hk : HasBoundedFootprint ((κ v : PSpace Ω) : PSp Ω),
        own (R * ⟨((κ v : PSpace Ω) : PSp Ω), hk⟩) ⊢ iprop(⌈fun ρ ↦ X ρ = v⌉ ∗ K v) := by
  rw [valuePost_def] at h
  obtain ⟨ν, h'⟩ := own_exists_elim hv h
  exact ⟨ν, condValue_elim hv h'⟩

/-- An assertion recoverable from the fibres of any conditioning (Amaryllis's *strongly
convex* assertions).  `WP_BIND` needs it to collapse the conditioning `WP_BIND_C` returns;
`not_convex_constQ` shows `AEProper` does not imply it. -/
def Convex (P : FProp) : Prop :=
  ∀ {γ : Type} (ν : PMF γ), (𝒞⟨ν⟩ _v; P) ⊢ P

lemma convex_def (P : FProp) :
    Iff (Convex P) (∀ {γ : Type} (ν : PMF γ), (𝒞⟨ν⟩ _v; P) ⊢ P) := by
  rfl

end

end Foxglove
