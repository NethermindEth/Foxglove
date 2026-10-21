module

public import Foxglove.Rules.Sure

@[expose] public section
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

/-- Conditioning is monotone in its continuation. -/
lemma jointConditioning_mono {A : Type} {ν : PMF A} {K K' : A → FProp}
    (h : ∀ x, K x ⊢ K' x) : jointConditioning ν K ⊢ jointConditioning ν K' := by
  unfold jointConditioning
  exact exists_mono fun m ↦ exists_mono fun κ ↦ sep_mono_right (sep_mono_right
    (forall_mono fun v ↦ wand_mono_right (h v)))

/-- A resource held outside a conditioning can be pushed into every fibre: one `∗`-splitting
serves every value at once, so nothing has to be duplicated. -/
lemma jointConditioning_frame {A : Type} {ν : PMF A} {K : A → FProp} {R : FProp} :
    iprop(R ∗ jointConditioning ν K) ⊢ jointConditioning ν (fun x ↦ iprop(R ∗ K x)) := by
  unfold jointConditioning
  iintro ⟨HR, %m, %κ, Hm, %hmix, Hall⟩
  iexists m, κ
  isplitl [Hm]
  · iexact Hm
  · isplitl []
    · ipureintro
      exact hmix
    · iintro %v Hv
      ispecialize Hall $$ %v Hv
      isplitl [HR]
      · iexact HR
      · iexact Hall

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
  obtain ⟨Kr, rfl⟩ : ∃ Kr : γ → UpperSet (BoundedFootprintSpace Bool), Kc = fun v ↦ fmk (Kr v) :=
    ⟨fun v ↦ (Kc v).out, funext fun v ↦ (Quotient.out_eq _).symm⟩
  have hr := h r hv (le_refl r)
  obtain ⟨q, ⟨m, hq⟩, hqr⟩ := hr
  obtain ⟨q', ⟨ℓ, hq'⟩, hq'r⟩ := (Quotient.exact hq).2 r hv hqr
  obtain ⟨b₁, b₂, hle, hown, hrest⟩ := (Quotient.exact hq').2 r hv hq'r
  obtain ⟨c₁, c₂, hle', hmix, hall⟩ := hrest
  obtain ⟨r₁, ⟨hbfm, hr₁⟩, hb₁⟩ := hown
  have hmb₁ := (Quotient.exact hr₁).2 b₁
    (valid_mono (le_trans (le_mul_of_one_le PSp.one_le) hle) hv) hb₁
  -- `m` and the continuation's frame `c₂` compose, as in `C_FALSE`
  have hc₂b₂ : c₂ ≤ b₂ := by
    refine le_trans ?_ hle'
    rw [mul_comm]
    exact le_mul_of_one_le PSp.one_le
  have hmc₂r : (⟨(m : PSp Ω), hbfm⟩ : BoundedFootprintSpace Bool) * c₂ ≤ r :=
    le_trans (mul_le_mul_right_le hmb₁ c₂) (le_trans (mul_le_mul_left_le hc₂b₂ b₁) hle)
  have hvmc₂ : ✓((⟨(m : PSp Ω), hbfm⟩ : BoundedFootprintSpace Bool) * c₂) :=
    valid_mono hmc₂r hv
  have hb₂r : b₂ ≤ r := by
    refine le_trans ?_ hle
    rw [mul_comm]
    exact le_mul_of_one_le PSp.one_le
  have hvc₂ : ✓c₂ := valid_mono (le_trans hc₂b₂ hb₂r) hv
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
  have hsp := s.2
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
    have hS : S =ᵢ c₂' ⊕ᵢ (ℓ v : PSpace Ω) :=
      ⟨hcomm.1, fun E hE F hF ↦ hrect v hv E F hE hF⟩
    have hvm : ✓((m : PSp Ω)) := PSp.valid_def.mpr (Option.some_ne_none _)
    have hvk : ✓(((ℓ v : PSpace Ω)) : PSp Ω) := PSp.valid_def.mpr (Option.some_ne_none _)
    have hbfk : HasBoundedFootprint (((ℓ v : PSpace Ω)) : PSp Ω) :=
      hasBoundedFootprint_congr hvm hvk rfl hbfm
    have hval : (c₂ * (⟨((ℓ v : PSpace Ω) : PSp Ω), hbfk⟩ : BoundedFootprintSpace Bool)).val
        = (S : PSp Ω) := by
      show PSp.mul c₂.val _ = _
      rw [hc₂']
      exact mul_respect_independentProduct hS
    have hvalid : ✓(c₂ * (⟨((ℓ v : PSpace Ω) : PSp Ω), hbfk⟩ : BoundedFootprintSpace Bool)) := by
      show (c₂ * _).val ≠ (⊤ : PSp Ω)
      rw [hval]
      exact WithTop.coe_ne_top
    have hmem := hall _ ⟨⟨v, hv⟩, rfl⟩ _ hvalid
      ⟨_, ⟨hbfk, rfl⟩,
        le_refl (⟨((ℓ v : PSpace Ω) : PSp Ω), hbfk⟩ : BoundedFootprintSpace Bool)⟩
    exact ⟨_, hval, fun y _ hy ↦ UpperSet.upper _ hy hmem⟩

/-- A deterministic result needs no conditioning: at a constant random variable `valuePost`
is just the postcondition at that value.  Mix over `δ x`, whose only fibre is the trivial
space, and the sure fact `x = x` is free. -/
lemma valuePost_const {α : Type} (x : α) (Q : α → FProp) : Q x ⊢ valuePost (fun _ ↦ x) Q := by
  unfold valuePost jointConditioning
  iintro HQ
  iexists (δ x), (1 : PSpace Ω), unitKernel α
  isplitl []
  · exact ownP_one
  · isplitl []
    · ipureintro
      show PSpace.μ 1 = (((δ x) : PMF α).toMeasureWithMs ⊤).bind (fun _ ↦ PSpace.μ 1)
      simp [PMF.toMeasureWithMs]
    · iintro %y Hy
      have hy : (y : α) = x := by simpa using y.2
      simp only [hy]
      isplitl []
      · dsimp only [LiftPred.lift]
        iexists (1 : PSpace Ω)
        isplitl []
        · exact ownP_one
        · ipureintro
          simp [LiftUnary.lift]
      · iexact HQ

/-- `valuePost` at a given law `ν` of `X`: on the fibre at `x` the result surely is `x` and
`Q x` holds.  `valuePost X Q` is `∃ ν, condValue ν X Q`. -/
def condValue {α : Type} (ν : PMF α) (X : RV α) (Q : α → FProp) : FProp :=
  𝒞⟨ν⟩ x; (⌈fun ρ ↦ X ρ = x⌉ ∗ Q x)

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
  obtain ⟨U, hU⟩ : ∃ U : β → UpperSet (BoundedFootprintSpace Bool), K = fun v ↦ fmk (U v) := by
    choose U hU using fun v ↦ Quotient.exists_rep (K v)
    exact ⟨U, funext fun v ↦ (hU v).symm⟩
  subst hU
  obtain ⟨q', ⟨mm, hq'⟩, hq'b⟩ := h b hv (le_refl b)
  obtain ⟨q'', ⟨κ, hq''⟩, hq''b⟩ := (Quotient.exact hq').2 b hv hq'b
  obtain ⟨b₁, b₂, hle, hown, hrest⟩ := (Quotient.exact hq'').2 b hv hq''b
  obtain ⟨c₁, c₂, hle', hmix, hall⟩ := hrest
  obtain ⟨r₁, ⟨hbfm, hr₁⟩, hb₁⟩ := hown
  have hvb₁ : ✓b₁ := valid_mono (le_trans (le_mul_of_one_le PSp.one_le) hle) hv
  have hmb₁ := (Quotient.exact hr₁).2 b₁ hvb₁ hb₁
  have hc₂b₂ : c₂ ≤ b₂ := le_trans (by rw [mul_comm]; exact le_mul_of_one_le PSp.one_le) hle'
  refine ⟨mm, hbfm, κ, c₂, hmix, ?_, ?_⟩
  · exact le_trans (mul_le_mul_right_le hmb₁ c₂) (le_trans (mul_le_mul_left_le hc₂b₂ b₁) hle)
  · intro v hv' hk y hvy hy
    have hvc₂K : ✓(c₂ * ⟨((κ v : PSpace Ω) : PSp Ω), hk⟩) := valid_mono hy hvy
    have hmem := hall _ ⟨⟨v, hv'⟩, rfl⟩ _ hvc₂K ⟨_, ⟨hk, rfl⟩,
      (show (⟨((κ v : PSpace Ω) : PSp Ω), hk⟩ : BoundedFootprintSpace Bool)
        ≤ ⟨((κ v : PSpace Ω) : PSp Ω), hk⟩ from le_refl _)⟩
    exact (UpperSetBI.sep _ _).upper' hy hmem

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
  obtain ⟨ν, h'⟩ := own_exists_elim hv h
  exact ⟨ν, condValue_elim hv h'⟩

/-- An assertion recoverable from the fibres of any conditioning (Amaryllis's *strongly
convex* assertions).  `WPBind` needs it to collapse the conditioning `WPBindC` returns;
`not_convex_constQ` shows `AEProper` does not imply it. -/
def Convex (P : FProp) : Prop :=
  ∀ {γ : Type} (ν : PMF γ), (𝒞⟨ν⟩ _v; P) ⊢ P

end

end Foxglove
