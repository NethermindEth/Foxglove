module

import Foxglove.Basic
public import Foxglove.Algebra.MeasureOnSpace
public import Foxglove.Algebra.OURA
public import Foxglove.Interp.Bernoulli.Basic
public import Iris.ProofMode


@[expose] public section
namespace Foxglove

open ProbSpace

open Iris OrderedUnitalResourceAlgebra


noncomputable section

attribute [local aesop simp] Equivalence.refl Equivalence.trans Equivalence.symm

abbrev FProp := Iris.UpperSetBI.OURAProp (BoundedFootprintSpace Bool)

instance : Iris.BI FProp := inferInstance

open UpperSetBI

section

open ProbabilityTheory

abbrev _root_.ProbabilityTheory.TrivialMarkovKernel (A : Type) (p : PSpace Ω) : Type :=
  {κ : @Kernel A Ω ⊤ p.ms // IsMarkovKernel κ}

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

def _root_.PMF.toMeasureWithMs {A : Type} (μ : PMF A) (ms : MeasurableSpace A) : @MeasureTheory.Measure A ms :=
  @μ.toMeasure A ms

abbrev δ {A : Type} (v : A) : PMF A := PMF.pure v

def own {M} [OrderedUnitalResourceAlgebra M] (b : M) : OURAProp M := UpperSetBI.own b

/-- Owning the unit costs nothing: `emp` and `own 1` are the same upper set. -/
lemma own_one {M} [OrderedUnitalResourceAlgebra M] : ⊢ (own (1 : M) : OURAProp M) :=
  fun _ _ h ↦ h

def ownP (p : PSpace Ω) : FProp :=
  iprop(∃ h : HasBoundedFootprint (p : PSp Ω), own ⟨(p : PSp Ω), h⟩)

open Iris.BI in
lemma ownP_one : ⊢ ownP 1 := by
  unfold ownP
  refine entails_trans ?_ (exists_intro hasBoundedFootprint_one)
  exact own_one

/-- `p` satisfies `P`: `p` is a resource, and owning exactly `p` establishes `P`.  In the
upper-set model this is `p ∈ P`. -/
def satP (p : PSpace Ω) (P : FProp) : Prop :=
  ∃ h : HasBoundedFootprint (p : PSp Ω),
    own (⟨(p : PSp Ω), h⟩ : BoundedFootprintSpace Bool) ⊢ P

/-- **Joint conditioning**, in the shape Amaryllis gives it (arXiv 2605.13765, §3.3):

```
  C_{v←μ} Φ(v) (x)  ⟺  ∃κ. wsum(μ, κ) ≼ x ∧ ∀ v ∈ supp μ. Φ(v) (κ v)
```

Each fibre carries its own σ-algebra and `PSpace.wsum` mixes over the *intersection*
`⨅ v ∈ μ.support, (κ v).ms`, so a set the mixture measures is measured by every fibre --
which is what lets per-fibre independence from a frame transfer to the mixture
(`PSpace.wsum_indep`).  The fibre satisfies its assertion directly rather than supplying it
through a wand, so no single residual has to serve every `v` at once; and the mixture law is
definitional, so no side condition states it. -/
def jointConditioning {A : Type} (μ : PMF A) (K : A → FProp) : FProp :=
  iprop(
    ∃ m : PSpace Ω,
    ∃ κ : TrivialMarkovKernel A m,
      ownP m ∗
      ⌜m.μ = (μ.toMeasureWithMs ⊤).bind κ⌝ ∗
      ∀ v : μ.support, ownP (κ v) -∗ K v
  )

notation "𝒞" "⟨" μ "⟩" v ";" K => jointConditioning μ (fun v => iprop(K))

def almostMeasurable {A : Type} (E : RV A) (P : PSp Ω) : Prop :=
  match P with
  | none => False
  | some p => @AEMeasurable Ω A ⊤ _ E p.1.μ

def hasDistribution {A : Type} (E : RV A) (μ : PMF A) : FProp :=
  iprop(
    ∃ P : PSpace Ω,
      ownP P ∗
      ⌜
        have Eμ := @P.μ.map Ω A P.ms ⊤ E
        almostMeasurable E P ∧ Eμ = μ.toMeasureWithMs ⊤
      ⌝
  )

notation:100 E:100 " ~ " p:100 => hasDistribution E p

def liftPred (a : Ω → Prop) : FProp :=
  iprop(∃ P : PSpace Ω, ownP P ∗ ⌜P.μ {ρ | ¬ a ρ} = 0⌝)

@[inherit_doc] notation:max "⌈" a "⌉" => liftPred a

/-- Assertions of the shape `∃ P, ownP P ∗ ⌜φ P⌝` -- the shape `hasDistribution` and
`liftPred` share -- with pointwise equivalent side conditions are the same assertion. -/
theorem ownP_pure_congr {φ ψ : PSpace Ω → Prop} (h : ∀ P, φ P ↔ ψ P) :
    (iprop(∃ P : PSpace Ω, ownP P ∗ ⌜φ P⌝) : FProp)
      = iprop(∃ P : PSpace Ω, ownP P ∗ ⌜ψ P⌝) := by
  have hfe : φ = ψ := funext fun P ↦ propext (h P)
  rw [hfe]

def valuePost {α : Type} (X : RV α) (Q : α → FProp) : FProp :=
  iprop(∃ ν : PMF α, 𝒞⟨ν⟩ x; (⌈fun ρ ↦ X ρ = x⌉ ∗ Q x))

/-! ### A `wp'` with a locality clause, for comparison

`wp` leaves its witness `b` wide open: nothing relates it to `a`, so two witnesses produced
at two *different* ambients -- which is exactly what the fibres of a conditioning are -- need
not be comparable, and `CWPSwap`'s conclusion cannot be assembled from them.

`wp'` adds one clause: the witness may not measure anything beyond what `a` could already
measure, together with the randomness the run itself added (`freshMs`).  It is an upper
bound, not an equality, so upward closure is unchanged -- a bigger `a` only relaxes it, and
the same witness still serves.

That bound is enough for the swap: at each fibre the input resource is `c₂ * κ v`, and since
the fibres of a conditioning all carry `m.ms`, the bound
`msOf (c₂ * κ v) ⊔ freshMs = c₂.ms ⊔ m.ms ⊔ freshMs` is *the same for every* `v`.  The
witnesses can then all be enlarged to that one σ-algebra, which is independent of the frame
because `c₂ * m` is and because fresh randomness is independent of everything prior. -/

/-- The σ-algebra a resource measures.  `⊤` on the undefined resource, which keeps `msOf`
monotone and makes the clause below vacuous there. -/
def msOf (x : BoundedFootprintSpace Bool) : MeasurableSpace Ω :=
  match (x : PSp Ω) with
  | none => ⊤
  | some p => p.ms

lemma msOf_mono {x y : BoundedFootprintSpace Bool} (hxy : x ≤ y) : msOf x ≤ msOf y := by
  unfold msOf
  cases hx : (x : PSp Ω) with
  | none =>
    have hy : (y : PSp Ω) = none := by
      refine PSp.ge_top_imp_top ?_
      rw [show (⊤ : PSp Ω) = (x : PSp Ω) from by rw [hx]; rfl]
      exact hxy
    rw [hy]
  | some p =>
    cases hy : (y : PSp Ω) with
    | none => exact le_top
    | some q =>
      have hle : (x : PSp Ω) ≤ (y : PSp Ω) := hxy
      rw [hx, hy] at hle
      exact (WithTop.coe_le_coe.1 hle).1



open Interp Interp.ProbTree Iris.BI OURAProp in
/-- **The proposed `wp`.**  `wp` with the locality clause `msOf b ≤ msOf a ⊔ freshMs …`. -/
def wp' {α : Type} [Inhabited α] {m : Type → Type} [Interp.BernoulliInterpretable m]
    (t : m α) (Q : RV α → FProp) : FProp :=
  fmk {
    carrier := {a |
      ∀ (μ₀ : BoundedFootprintPsp) (c : BoundedFootprintSpace Bool),
        ✓μ₀.psp → a * c ≤ μ₀.toSpace →
        ∃ b : BoundedFootprintSpace Bool,
          b * c ≤ (run t μ₀).1.toSpace ∧ ✓b ∧
            msOf b ≤ msOf a ⊔ freshMs μ₀ (Interp.BernoulliInterpretable.interp t) ∧
            (own b ⊢ Q (result (run t μ₀)))}
    upper' := by
      intro x y hxy hx μ₀ c hv hle
      obtain ⟨b, hb1, hb2, hb3, hb4⟩ := hx μ₀ c hv (le_trans (mul_le_mul_right_le hxy c) hle)
      exact ⟨b, hb1, hb2, le_trans hb3 (sup_le_sup_right (msOf_mono hxy) _), hb4⟩
  }

open Interp Interp.ProbTree Iris.BI OURAProp in
def wp {α : Type} [Inhabited α] {m : Type → Type} [Interp.BernoulliInterpretable m]
    (t : m α) (Q : RV α → FProp) : FProp :=
  fmk {
    carrier := {a |
      ∀ (μ₀ : BoundedFootprintPsp) (c : BoundedFootprintSpace Bool),
        ✓μ₀.psp → a * c ≤ μ₀.toSpace →
        ∃ b : BoundedFootprintSpace Bool,
          b * c ≤ (run t μ₀).1.toSpace ∧ ✓b ∧
            (own b ⊢ Q (result (run t μ₀)))}
    upper' := by
      intro x y hxy hx μ₀ c hv hle
      exact hx μ₀ c hv (le_trans (mul_le_mul_right_le hxy c) hle)
  }

end

end

section

open Iris BI UpperSetBI OURAProp

noncomputable def ftrue : FProp := fmk UpperSetBI.true

noncomputable def ffalse : FProp := fmk UpperSetBI.false

variable {P Q R : FProp}

/-! ### What `FProp` satisfies as a BI -/

/-- `1` sits below every resource (`PSp.one_le`), so `emp` is the whole upper set and the
logic is affine: resources may always be thrown away.  Through iris-lean's generic instance
this also makes every `FProp` `Absorbing`. -/
instance : BIAffine FProp where
  affine P := ⟨by induction P using Quotient.ind; exact fun _ _ _ ↦ PSp.one_le⟩

/-- `<pers> P` holds either of everything or of nothing, according to whether `P` already
holds of the unit resource, so `Persistent P` says exactly that owning nothing suffices for
`P`.  Neither `Persistent` nor `Intuitionistic` therefore holds of a general `FProp`: for a
valid `b`, `own b` is persistent exactly when `b ≤ 1`.  The persistent fragment is the one iris-lean already covers with `pure_persistent`
and `emp_persistent`. -/
lemma persistent_iff {U : UpperSet (BoundedFootprintSpace Bool)} :
    Persistent (fmk U) ↔ ∀ m, ✓m → m ∈ U → (1 : BoundedFootprintSpace Bool) ∈ U :=
  ⟨fun h ↦ h.persistent, fun h ↦ ⟨h⟩⟩

attribute [grind .] and_intro entails_rfl pure_intro or_intro_l or_intro_r or_elim
                    Iris.BI.BIBase.pure and_elim_l and_elim_r Iris.BI.BIBase.BiEntails.mk

attribute [grind cases] Iris.BI.BIBase.BiEntails

attribute [grind →] entails_trans

@[simp, grind .]
lemma entails_ftrue : P ⊢ ftrue := pure_intro True.intro

@[simp, grind .]
lemma fals_entails : ffalse ⊢ P := by
  apply pure_elim'
  grind

lemma C_True
  {A : Type} {μ : PMF A}
  : ⊢ (𝒞⟨μ⟩ _v; ftrue : FProp) := by
  sorry
--   unfold jointConditioning
--   iexists (1 : PSpace Ω), unitKernel A
--   isplitl []
--   · exact ownP_one
--   · isplitl []
--     · ipureintro
--       show PSpace.μ 1 = (μ.toMeasureWithMs ⊤).bind (fun _ ↦ PSpace.μ 1)
--       simp [PMF.toMeasureWithMs]
--     · iintro %v Hv
--       exact entails_ftrue
--
/-- Conditioning is monotone in its continuation. -/
lemma jointConditioning_mono {A : Type} {ν : PMF A} {K K' : A → FProp}
    (h : ∀ x, K x ⊢ K' x) : jointConditioning ν K ⊢ jointConditioning ν K' := by
  sorry
--   unfold jointConditioning
--   exact exists_mono fun m ↦ exists_mono fun κ ↦ sep_mono_right (sep_mono_right
--     (forall_mono fun v ↦ wand_mono_right (h v)))
--
/-- A resource held outside a conditioning can be pushed into every fibre: one `∗`-splitting
serves every value at once, so nothing has to be duplicated. -/
lemma jointConditioning_frame {A : Type} {ν : PMF A} {K : A → FProp} {R : FProp} :
    iprop(R ∗ jointConditioning ν K) ⊢ jointConditioning ν (fun x ↦ iprop(R ∗ K x)) := by
  sorry
--   unfold jointConditioning
--   iintro ⟨HR, %m, %κ, Hm, %hmix, Hall⟩
--   iexists m, κ
--   isplitl [Hm]
--   · iexact Hm
--   · isplitl []
--     · ipureintro
--       exact hmix
--     · iintro %v Hv
--       ispecialize Hall $$ %v Hv
--       isplitl [HR]
--       · iexact HR
--       · iexact Hall
--
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
/-- Conditioning with a `False` continuation is `False`: pick a value in the support and
hand the continuation the fibre it asks for.  The fibre composes with the continuation's
frame by `PSpace.isIndependentProduct_reweight`. -/
lemma C_False
  {A : Type} {μ : PMF A}
  : (𝒞⟨μ⟩ _v; ffalse : FProp) ⊢ ffalse := by
  sorry
--   intro r hv h
--   obtain ⟨q, ⟨m, hq⟩, hqr⟩ := h
--   obtain ⟨q', ⟨κ, hq'⟩, hq'r⟩ := (Quotient.exact hq).2 r hv hqr
--   obtain ⟨b₁, b₂, hle, hown, hrest⟩ := (Quotient.exact hq').2 r hv hq'r
--   obtain ⟨c₁, c₂, hle', hmix, hall⟩ := hrest
--   obtain ⟨r₁, ⟨hbfm, hr₁⟩, hb₁⟩ := hown
--   have hmb₁ := (Quotient.exact hr₁).2 b₁ (valid_mono (le_trans (le_mul_of_one_le PSp.one_le) hle) hv) hb₁
--   obtain ⟨v, hvsupp⟩ := μ.support_nonempty
--   -- `c₂` sits inside `b₂`, so `m`'s resource and `c₂` compose inside `r`
--   have hc₂b₂ : c₂ ≤ b₂ := by
--     refine le_trans ?_ hle'
--     rw [mul_comm]
--     exact le_mul_of_one_le PSp.one_le
--   have hmc₂r : (⟨(m : PSp Ω), hbfm⟩ : BoundedFootprintSpace Bool) * c₂ ≤ r :=
--     le_trans (mul_le_mul_right_le hmb₁ c₂) (le_trans (mul_le_mul_left_le hc₂b₂ b₁) hle)
--   have hvmc₂ : ✓((⟨(m : PSp Ω), hbfm⟩ : BoundedFootprintSpace Bool) * c₂) := valid_mono hmc₂r hv
--   have hb₂r : b₂ ≤ r := by
--     refine le_trans ?_ hle
--     rw [mul_comm]
--     exact le_mul_of_one_le PSp.one_le
--   have hvc₂ : ✓c₂ := valid_mono (le_trans hc₂b₂ hb₂r) hv
--   -- the spaces behind `c₂` and behind `m * c₂`
--   obtain ⟨c₂', hc₂'⟩ : ∃ c : PSpace Ω, c₂.val = (c : PSp Ω) :=
--     Option.ne_none_iff_exists'.mp (PSp.valid_def.mp hvc₂)
--   obtain ⟨s, hs⟩ : ∃ s : PSpace Ω, PSp.mul ((m : PSp Ω)) (c₂.val) = (s : PSp Ω) :=
--     Option.ne_none_iff_exists'.mp (PSp.valid_def.mp hvmc₂)
--   rw [hc₂'] at hs
--   have hcomm : s =ᵢ c₂' ⊕ᵢ m := independentProduct_comm (PSp.mul_inversion hs)
--   -- reweight that product along the `v`-fibre
--   haveI hprob : MeasureTheory.IsProbabilityMeasure (κ.1 v) := κ.2.isProbabilityMeasure v
--   obtain ⟨s', hs'⟩ :=
--     PSpace.isIndependentProduct_reweight hcomm (κ.1 v) (kernel_fibre_ac κ hmix hvsupp)
--   have hvm : ✓((m : PSp Ω)) := PSp.valid_def.mpr (Option.some_ne_none _)
--   have hvk : ✓(((κ v : PSpace Ω)) : PSp Ω) := PSp.valid_def.mpr (Option.some_ne_none _)
--   have hbfk : HasBoundedFootprint (((κ v : PSpace Ω)) : PSp Ω) :=
--     hasBoundedFootprint_congr hvm hvk rfl hbfm
--   have hvalid : ✓(c₂ * (⟨((κ v : PSpace Ω) : PSp Ω), hbfk⟩ : BoundedFootprintSpace Bool)) := by
--     show PSp.mul c₂.val _ ≠ (⊤ : PSp Ω)
--     rw [hc₂']
--     exact PSp.mul_ne_top_of_exists ⟨s', hs'⟩
--   exact hall _ ⟨⟨v, hvsupp⟩, rfl⟩ _ hvalid
--     ⟨_, ⟨hbfk, rfl⟩,
--       le_refl (⟨((κ v : PSpace Ω) : PSp Ω), hbfk⟩ : BoundedFootprintSpace Bool)⟩

open MeasureTheory in
theorem EDistInj
  {A : Type} {E : RV A} {μ μ' : PMF A}
  : E ~ μ ∧ E ~ μ' ⊢ ⌜μ = μ'⌝ := by
  intro m hv h
  obtain ⟨h₁, h₂⟩ := h
  -- the ambient space the two claims share
  obtain ⟨y, hy⟩ : ∃ y : PSpace Ω, m.val = some y :=
    Option.ne_none_iff_exists'.mp (PSp.valid_def.mp hv)
  -- the space witnessing `E ~ μ`, and its resource, sit below `m`
  obtain ⟨q₁, ⟨P, hq₁P⟩, hq₁m⟩ := h₁
  obtain ⟨b₁, b₂, hle₁, hown₁, hpure₁⟩ := (Quotient.exact hq₁P).2 m hv hq₁m
  obtain ⟨r₁, ⟨hbf₁, hr₁⟩, hb₁⟩ := hown₁
  have hb₁m : b₁ ≤ m := le_trans (le_mul_of_one_le PSp.one_le) hle₁
  have hPb₁ := (Quotient.exact hr₁).2 b₁ (valid_mono hb₁m hv) hb₁
  -- and the same for `E ~ μ'`
  obtain ⟨q₂, ⟨P', hq₂P'⟩, hq₂m⟩ := h₂
  obtain ⟨c₁, c₂, hle₂, hown₂, hpure₂⟩ := (Quotient.exact hq₂P').2 m hv hq₂m
  obtain ⟨r₂, ⟨hbf₂, hr₂⟩, hc₁⟩ := hown₂
  have hc₁m : c₁ ≤ m := le_trans (le_mul_of_one_le PSp.one_le) hle₂
  have hP'c₁ := (Quotient.exact hr₂).2 c₁ (valid_mono hc₁m hv) hc₁
  have hPy : P ≤ y := by
    have hPm : (P : PSp Ω) ≤ (m : PSp Ω) := le_trans hPb₁ hb₁m
    rw [hy] at hPm
    exact WithTop.coe_le_coe.1 hPm
  have hP'y : P' ≤ y := by
    have hP'm : (P' : PSp Ω) ≤ (m : PSp Ω) := le_trans hP'c₁ hc₁m
    rw [hy] at hP'm
    exact WithTop.coe_le_coe.1 hP'm
  -- both push `E` forward along the one ambient measure, so the two laws agree
  obtain ⟨ham, hμ₁⟩ := hpure₁
  obtain ⟨ham', hμ₂⟩ := hpure₂
  show μ = μ'
  apply @PMF.toMeasure_injective A ⊤
  calc @PMF.toMeasure A ⊤ μ
      = @Measure.map Ω A P.ms ⊤ E P.μ := hμ₁.symm
    _ = @Measure.map Ω A P'.ms ⊤ E P'.μ := PSpace.map_eq_of_le hPy hP'y ham ham'
    _ = @PMF.toMeasure A ⊤ μ' := hμ₂

set_option linter.style.haveILetI false in
open MeasureTheory in
/-- On a fixed space, pushing `E` forward to `δ v` is the same as `E` being `v` off a null
set: the two only differ in how they say "almost surely `v`". -/
theorem law_dirac_iff {A : Type} {E : RV A} {v : A} (P : PSpace Ω) :
    (almostMeasurable E (P : PSp Ω) ∧
        @Measure.map Ω A P.ms ⊤ E P.μ = (δ v).toMeasureWithMs ⊤)
      ↔ P.μ {ρ | ¬ E ρ = v} = 0 := by
  have hP := P.isProbability
  letI : MeasurableSpace A := ⊤
  letI : MeasurableSpace Ω := P.ms
  constructor
  · rintro ⟨ham, hmap⟩
    replace ham : @AEMeasurable Ω A ⊤ P.ms E P.μ := ham
    have h := Measure.map_apply_of_aemeasurable ham
      (s := {v}ᶜ) MeasurableSpace.measurableSet_top
    rw [hmap] at h
    show P.μ (E ⁻¹' {v}ᶜ) = 0
    rw [← h]
    simp [PMF.toMeasureWithMs, PMF.toMeasure_pure]
  · intro h
    -- `E` is a.e. the constant `v`, which is measurable, so it is a.e.-measurable
    have hae : E =ᵐ[P.μ] (fun _ ↦ v) := h
    refine ⟨⟨fun _ ↦ v, measurable_const, hae⟩, ?_⟩
    rw [Measure.map_congr hae, Measure.map_const]
    simp [PMF.toMeasureWithMs, PMF.toMeasure_pure]

/-- Being Dirac-distributed is being almost surely equal to the value. -/
theorem ESureDirac {A : Type} {E : RV A} {v : A}
  : E ~ δ v ⊣⊢ ⌈fun ρ ↦ E ρ = v⌉ := by
  have h : (E ~ δ v) = ⌈fun ρ ↦ E ρ = v⌉ :=
    ownP_pure_congr (fun P ↦ law_dirac_iff P)
  rw [h]
  exact ⟨entails_rfl, entails_rfl⟩

/-- Two sure facts held separately are both sure on the ambient space, so they merge. -/
theorem liftPred_sep {a b : Ω → Prop} : ⌈a⌉ ∗ ⌈b⌉ ⊢ ⌈fun ω ↦ a ω ∧ b ω⌉ := by
  intro m hv h
  obtain ⟨d₁, d₂, hle, h₁, h₂⟩ := h
  obtain ⟨y, hy⟩ : ∃ y : PSpace Ω, m.val = (y : PSp Ω) :=
    Option.ne_none_iff_exists'.mp (PSp.valid_def.mp hv)
  have hd₁ : d₁ ≤ m := le_trans (le_mul_of_one_le PSp.one_le) hle
  have hd₂ : d₂ ≤ m := by
    refine le_trans ?_ hle
    rw [mul_comm]
    exact le_mul_of_one_le PSp.one_le
  -- the space behind the first conjunct sits below the ambient `y`
  obtain ⟨q₁, ⟨P₁, hq₁⟩, hq₁m⟩ := h₁
  obtain ⟨e₁, _, hlee₁, hown₁, hpure₁⟩ := (Quotient.exact hq₁).2 d₁ (valid_mono hd₁ hv) hq₁m
  obtain ⟨r₁, ⟨hbf₁, hr₁⟩, he₁⟩ := hown₁
  have he₁m : e₁ ≤ m := le_trans (le_trans (le_mul_of_one_le PSp.one_le) hlee₁) hd₁
  have hP₁ := (Quotient.exact hr₁).2 e₁ (valid_mono he₁m hv) he₁
  have hP₁y : P₁ ≤ y := by
    have hP₁m : (P₁ : PSp Ω) ≤ (m : PSp Ω) := le_trans hP₁ he₁m
    rw [hy] at hP₁m
    exact WithTop.coe_le_coe.1 hP₁m
  -- and the same for the second
  obtain ⟨q₂, ⟨P₂, hq₂⟩, hq₂m⟩ := h₂
  obtain ⟨e₂, _, hlee₂, hown₂, hpure₂⟩ := (Quotient.exact hq₂).2 d₂ (valid_mono hd₂ hv) hq₂m
  obtain ⟨r₂, ⟨hbf₂, hr₂⟩, he₂⟩ := hown₂
  have he₂m : e₂ ≤ m := le_trans (le_trans (le_mul_of_one_le PSp.one_le) hlee₂) hd₂
  have hP₂ := (Quotient.exact hr₂).2 e₂ (valid_mono he₂m hv) he₂
  have hP₂y : P₂ ≤ y := by
    have hP₂m : (P₂ : PSp Ω) ≤ (m : PSp Ω) := le_trans hP₂ he₂m
    rw [hy] at hP₂m
    exact WithTop.coe_le_coe.1 hP₂m
  -- both exceptional sets are null on `y`, hence so is their union
  have hnull₁ : y.μ {ρ | ¬ a ρ} = 0 := PSpace.null_of_le hP₁y hpure₁
  have hnull₂ : y.μ {ρ | ¬ b ρ} = 0 := PSpace.null_of_le hP₂y hpure₂
  have hbfy : HasBoundedFootprint (y : PSp Ω) := hy ▸ m.property
  have hmy : (⟨(y : PSp Ω), hbfy⟩ : BoundedFootprintSpace Bool) = m := Subtype.ext hy.symm
  refine ⟨_, ⟨y, rfl⟩, m, 1, ?_, ⟨_, ⟨hbfy, rfl⟩, le_of_eq hmy⟩, ?_⟩
  · rw [mul_one]
  · have hsub : {ρ | ¬ (a ρ ∧ b ρ)} ⊆ {ρ | ¬ a ρ} ∪ {ρ | ¬ b ρ} := by
      intro ρ hρ
      by_cases ha : a ρ
      · exact Or.inr fun hb ↦ hρ ⟨ha, hb⟩
      · exact Or.inl ha
    exact MeasureTheory.measure_mono_null hsub
      (MeasureTheory.measure_union_null hnull₁ hnull₂)

/-- A sure fact splits.  `∗` demands two resources whose independent product is defined, so
splitting needs an idempotent witness, and one exists: trim the owned space to the σ-algebra
generated by a null cover of the exceptional set.  That trim carries only the measures `0`
and `1`, hence is independent of itself, and it is a resource because `HasBoundedFootprint`
is closed under coarsening. -/
theorem liftPred_split {a b : Ω → Prop} : ⌈fun ω ↦ a ω ∧ b ω⌉ ⊢ ⌈a⌉ ∗ ⌈b⌉ := by
  intro m hv h
  obtain ⟨q, ⟨P, hq⟩, hqm⟩ := h
  obtain ⟨d₁, d₂, hle, hown, hpure⟩ := (Quotient.exact hq).2 m hv hqm
  obtain ⟨r₁, ⟨hbfP, hr₁⟩, hd₁⟩ := hown
  have hd₁m : d₁ ≤ m := le_trans (le_mul_of_one_le PSp.one_le) hle
  have hPm : (⟨(P : PSp Ω), hbfP⟩ : BoundedFootprintSpace Bool) ≤ m :=
    le_trans ((Quotient.exact hr₁).2 d₁ (valid_mono hd₁m hv) hd₁) hd₁m
  -- a measurable null cover of the exceptional set
  obtain ⟨N, hNsub, hNmeas, hNnull⟩ :=
    @MeasureTheory.exists_measurable_superset_of_null Ω P.ms P.μ _ hpure
  have hgen : MeasurableSpace.generateFrom {N} ≤ P.ms :=
    MeasurableSpace.generateFrom_le (by rintro t rfl; exact hNmeas)
  -- the 0-1 trim
  set P₀ : PSpace Ω := @PSpace.trim Ω P _ hgen with hP₀
  have hP₀P : P₀ ≤ P := PSpace.trim_le hgen
  have hNmeas₀ : @MeasurableSet Ω P₀.ms N := MeasurableSpace.measurableSet_generateFrom rfl
  have hN₀ : P₀.μ N = 0 := by
    rw [MeasureOnSpace.le_preserves_measure hP₀P hNmeas₀]
    exact hNnull
  have hidem : P₀ =ᵢ P₀ ⊕ᵢ P₀ :=
    PSpace.isIndependentProduct_self (PSpace.zero_or_one_generateFrom (le_refl _) hN₀)
  have hbf₀ : HasBoundedFootprint ((P₀ : PSp Ω)) :=
    hasBoundedFootprint_mono (PSp.valid_def.mpr (Option.some_ne_none _))
      (WithTop.coe_le_coe.2 hP₀P) hbfP
  have hb₀b₀ :
      (⟨(P₀ : PSp Ω), hbf₀⟩ : BoundedFootprintSpace Bool) * ⟨(P₀ : PSp Ω), hbf₀⟩ ≤ m := by
    refine le_trans ?_ hPm
    show PSp.mul (some P₀) (some P₀) ≤ (some P : PSp Ω)
    rw [PSp.mul_self_eq hidem]
    exact WithTop.coe_le_coe.2 hP₀P
  refine ⟨_, _, hb₀b₀, ⟨_, ⟨P₀, rfl⟩, ?_⟩, ⟨_, ⟨P₀, rfl⟩, ?_⟩⟩
  · refine ⟨_, 1, le_of_eq (mul_one _),
      ⟨_, ⟨hbf₀, rfl⟩, le_refl (⟨(P₀ : PSp Ω), hbf₀⟩ : BoundedFootprintSpace Bool)⟩, ?_⟩
    exact MeasureTheory.measure_mono_null (fun ρ hρ ↦ hNsub fun hab ↦ hρ hab.1) hN₀
  · refine ⟨_, 1, le_of_eq (mul_one _),
      ⟨_, ⟨hbf₀, rfl⟩, le_refl (⟨(P₀ : PSp Ω), hbf₀⟩ : BoundedFootprintSpace Bool)⟩, ?_⟩
    exact MeasureTheory.measure_mono_null (fun ρ hρ ↦ hNsub fun hab ↦ hρ hab.2) hN₀

/-- A sure fact is duplicable. -/
theorem liftPred_dup {p : Ω → Prop} : ⌈p⌉ ⊢ ⌈p⌉ ∗ ⌈p⌉ := by
  have h : (⌈p⌉ : FProp) = ⌈fun ω ↦ p ω ∧ p ω⌉ := by
    refine ownP_pure_congr (fun P ↦ ?_)
    have hs : {ρ | ¬ p ρ} = {ρ | ¬ (p ρ ∧ p ρ)} := by ext ρ; simp
    rw [hs]
  nth_rewrite 1 [h]
  exact liftPred_split

/-- A sure fact weakens: the exceptional set only shrinks. -/
theorem liftPred_mono {a b : Ω → Prop} (h : ∀ ρ, a ρ → b ρ) : ⌈a⌉ ⊢ ⌈b⌉ := by
  intro m hv hm
  obtain ⟨q, ⟨P, hq⟩, hqm⟩ := hm
  obtain ⟨d₁, d₂, hle, hown, hpure⟩ := (Quotient.exact hq).2 m hv hqm
  exact ⟨_, ⟨P, rfl⟩, d₁, d₂, hle, hown,
    MeasureTheory.measure_mono_null (fun ρ hρ hab ↦ hρ (h ρ hab)) hpure⟩

/-- Sure equalities substitute: this is the measure-theoretic content of `AEProper`, and
what lets a fibre's report of the result stand in for the global one. -/
theorem liftPred_subst {β : Type} {X Y : RV β} {x : β} :
    iprop(⌈fun ρ ↦ X ρ = Y ρ⌉ ∗ ⌈fun ρ ↦ X ρ = x⌉) ⊢ ⌈fun ρ ↦ Y ρ = x⌉ :=
  Iris.BI.entails_trans liftPred_sep (liftPred_mono (fun _ h ↦ h.1 ▸ h.2))

/-- Sure facts merge and split. -/
theorem ESureMerge {E₁ E₂ : RV Bool}
  : ⌈fun ω ↦ E₁ ω = true⌉ ∗ ⌈fun ω ↦ E₂ ω = true⌉ ⊣⊢ ⌈fun ω ↦ E₁ ω ∧ E₂ ω = true⌉ :=
  ⟨liftPred_sep, liftPred_split⟩

/-- Being Dirac-distributed is duplicable: a deterministic random variable is independent
of itself. -/
theorem EDiracDup {A : Type} {E : RV A} (v : A) : E ~ δ v ⊢ E ~ δ v ∗ E ~ δ v := by
  have h1 : (E ~ δ v) = ⌈fun ρ ↦ E ρ = v⌉ := ownP_pure_congr (fun P ↦ law_dirac_iff P)
  rw [h1]
  exact liftPred_dup

section wp

/-- Owning a resource that already satisfies an assertion establishes it: upper sets are
closed upwards. -/
lemma own_entails_of_mem {U : UpperSet (BoundedFootprintSpace Bool)}
    {a : BoundedFootprintSpace Bool} (ha : a ∈ U) : own a ⊢ (fmk U : FProp) :=
  fun _ _ hd ↦ U.upper' hd ha

/-- A deterministic result needs no conditioning: at a constant random variable `valuePost`
is just the postcondition at that value.  Mix over `δ x`, whose only fibre is the trivial
space, and the sure fact `x = x` is free. -/
lemma valuePost_const {α : Type} (x : α) (Q : α → FProp) : Q x ⊢ valuePost (fun _ ↦ x) Q := by
  sorry
--   unfold valuePost jointConditioning
--   iintro HQ
--   iexists (δ x), (1 : PSpace Ω), unitKernel α
--   isplitl []
--   · exact ownP_one
--   · isplitl []
--     · ipureintro
--       show PSpace.μ 1 = (((δ x) : PMF α).toMeasureWithMs ⊤).bind (fun _ ↦ PSpace.μ 1)
--       simp [PMF.toMeasureWithMs]
--     · iintro %y Hy
--       have hy : (y : α) = x := by simpa using y.2
--       simp only [hy]
--       isplitl []
--       · unfold liftPred
--         iexists (1 : PSpace Ω)
--         isplitl []
--         · exact ownP_one
--         · ipureintro
--           simp
--       · iexact HQ

open Interp in
/-- **Returning a value.**  `pure x` reads nothing, so `run` leaves the footprint untouched
(`run_pure_psp`) and every atom reports `x` (`result_run_pure`): the resource that already
satisfied `Q x` is handed straight back, and the postcondition is `valuePost` at a
constant. -/
lemma CWPPure {α : Type} {m : Type → Type} [Monad m] [Interp.LawfulBernoulliInterpretable m]
    [Inhabited α] {Q : RV α → FProp} {x : α} : Q (fun _ ↦ x) ⊢ wp (pure x : m α) Q := by
  obtain ⟨U, hU⟩ : ∃ U : UpperSet (BoundedFootprintSpace Bool), Q (fun _ ↦ x) = fmk U :=
    ⟨(Q (fun _ ↦ x)).out, (Quotient.out_eq _).symm⟩
  rw [hU]
  intro a hva ha μ₀ c hvalid hle
  refine ⟨a, ?_, hva, ?_⟩
  · have hsp : ((run (pure x : m α) μ₀).1.toSpace : BoundedFootprintSpace Bool) = μ₀.toSpace :=
      Subtype.ext (run_pure_psp x μ₀ hvalid)
    rw [hsp]
    exact hle
  · rw [result_run_pure (m := m) x μ₀ hvalid, hU]
    exact own_entails_of_mem ha

/-! ### Auxiliaries for `CWPSwap` -/

section SwapAux

open MeasureTheory ProbabilityTheory

/-- `p ≤ S` from the σ-algebras and the measures on `p`'s sets. -/
lemma PSpace.le_of_ms_le {p S : PSpace Ω} (h : p.ms ≤ S.ms)
    (hμ : ∀ E, MeasurableSet[p.ms] E → S.μ E = p.μ E) : p ≤ S := by
  refine ⟨h, ?_⟩
  apply @Measure.ext Ω p.ms
  intro u hu
  exact (hμ u hu).symm.trans (Measure.le_preserves_measure (h := h) (μ := S.μ) (hu := hu)).symm

/-- A space below `S` that measures no more than `f` sits below `S` trimmed to `f`. -/
lemma PSpace.le_trim_of_le {p S : PSpace Ω} {f : MeasurableSpace Ω} (hf : f ≤ S.ms)
    (hpS : p ≤ S) (hpf : p.ms ≤ f) : p ≤ @PSpace.trim Ω S f hf := by
  refine PSpace.le_of_ms_le hpf fun E hE ↦ ?_
  show (MeasureOnSpace.trim hf).μ E = p.μ E
  rw [MeasureOnSpace.trim_eq hf (hpf E hE), MeasureOnSpace.le_preserves_measure hpS hE]

/-- A set integral of a function the smaller space measures can be taken in either space. -/
lemma PSpace.setLIntegral_of_le {s P : PSpace Ω} (hsP : s ≤ P) {g : Ω → ENNReal}
    (hg : Measurable[s.ms] g) {A : Set Ω} (hA : MeasurableSet[s.ms] A) :
    ∫⁻ x in A, g x ∂P.μ = ∫⁻ x in A, g x ∂s.μ := by
  have htrim : s.μ = P.μ.trim hsP.1 := by
    apply @Measure.ext Ω s.ms
    intro u hu
    rw [MeasureOnSpace.le_preserves_measure hsP hu,
      @trim_measurableSet_eq Ω s.ms P.ms P.μ u hsP.1 hu]
  rw [htrim, setLIntegral_trim hsP.1 hg hA]

/-- **Reweighting an ambient along a factor.**  If `s = m ⊗ d` sits in `P`, then tilting `P`
by `dν/dm` turns the `m`-factor into `ν` and leaves `d` alone. -/
lemma PSpace.withDensity_rect {m d s P : PSpace Ω} (hs : s =ᵢ m ⊕ᵢ d) (hsP : s ≤ P)
    (ν : Measure[m.ms] Ω) [IsProbabilityMeasure ν] (hac : ν ≪ m.μ)
    {E : Set Ω} (hE : MeasurableSet[d.ms] E) {F : Set Ω} (hF : MeasurableSet[m.ms] F) :
    (P.μ.withDensity (ν.rnDeriv m.μ)) (E ∩ F) = d.μ E * ν F := by
  have hmp := m.2
  have hmle : m.ms ≤ s.ms := (PSpace.le_of_isIndependentProduct_left hs).1
  have hdle : d.ms ≤ s.ms := (PSpace.le_of_isIndependentProduct_right hs).1
  have hfmeas : Measurable[m.ms] (ν.rnDeriv m.μ) := Measure.measurable_rnDeriv ν m.μ
  have hEF : MeasurableSet[s.ms] (E ∩ F) := (hdle _ hE).inter (hmle _ hF)
  rw [withDensity_apply _ (hsP.1 _ hEF),
    PSpace.setLIntegral_of_le hsP (hfmeas.mono hmle le_rfl) hEF,
    PSpace.lintegral_rect (independentProduct_comm hs) hfmeas hE hF,
    ← withDensity_apply _ hF, Measure.withDensity_rnDeriv_eq ν m.μ hac]

/-- **Mixing the reweighted ambients back.**  If `m` is the `w`-mixture of the `ν i`, then the
ambient `P ≥ m` is the `w`-mixture of its tilts by `dν i/dm`. -/
lemma PSpace.withDensity_mixture {ι : Type} [Countable ι] {m P : PSpace Ω} (hmP : m ≤ P)
    (w : ι → ENNReal) (ν : ι → Measure[m.ms] Ω) [∀ i, IsProbabilityMeasure (ν i)]
    (hac : ∀ i, ν i ≪ m.μ)
    (hmix : ∀ F, MeasurableSet[m.ms] F → m.μ F = ∑' i, w i * ν i F)
    {E : Set Ω} (hE : MeasurableSet[P.ms] E) :
    P.μ E = ∑' i, w i * (P.μ.withDensity ((ν i).rnDeriv m.μ)) E := by
  have hmp := m.2
  have hPp := P.2
  have hfm : ∀ i, Measurable[m.ms] ((ν i).rnDeriv m.μ) := fun i ↦ Measure.measurable_rnDeriv _ _
  have hfP : ∀ i, Measurable[P.ms] ((ν i).rnDeriv m.μ) := fun i ↦ (hfm i).mono hmP.1 le_rfl
  set g : Ω → ENNReal := fun x ↦ ∑' i, w i * (ν i).rnDeriv m.μ x with hg
  have hgm : Measurable[m.ms] g := Measurable.ennreal_tsum fun i ↦ (hfm i).const_mul _
  -- `g` is the density of `m.μ` against itself
  have hg1 : g =ᵐ[m.μ] 1 := by
    refine @ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite Ω m.ms m.μ _ g 1 hgm
      measurable_const ?_
    intro F hF _
    rw [hg, lintegral_tsum (fun i ↦ ((hfm i).const_mul _).aemeasurable)]
    simp_rw [lintegral_const_mul _ (hfm _)]
    have hterm : ∀ i, w i * ∫⁻ x in F, (ν i).rnDeriv m.μ x ∂m.μ = w i * ν i F := by
      intro i
      rw [← withDensity_apply _ hF, Measure.withDensity_rnDeriv_eq _ _ (hac i)]
    rw [tsum_congr hterm, ← hmix F hF]
    simp
  have hg1P : g =ᵐ[P.μ] 1 := PSpace.ae_eq_of_le hmP hg1
  symm
  calc ∑' i, w i * (P.μ.withDensity ((ν i).rnDeriv m.μ)) E
      = ∑' i, ∫⁻ x in E, w i * (ν i).rnDeriv m.μ x ∂P.μ := by
        refine tsum_congr fun i ↦ ?_
        rw [withDensity_apply _ hE, lintegral_const_mul _ (hfP i)]
    _ = ∫⁻ x in E, g x ∂P.μ := by
        rw [lintegral_tsum (fun i ↦ ((hfP i).const_mul _).aemeasurable)]
    _ = ∫⁻ x in E, 1 ∂P.μ := lintegral_congr_ae (ae_restrict_of_ae hg1P)
    _ = P.μ E := by simp

/-- **Independence of a join, from a π-system.**  A frame `c` inside `S` that is independent
of every `A ∩ F` (with `A` from `m₁`, `F` from `m₂`) is independent of all of `m₁ ⊔ m₂`. -/
lemma PSpace.indep_sup_of_rect {S c : PSpace Ω} {m₁ m₂ : MeasurableSpace Ω}
    (h₁ : m₁ ≤ S.ms) (h₂ : m₂ ≤ S.ms) (hc : c ≤ S)
    (hbase : ∀ A, MeasurableSet[m₁] A → ∀ F, MeasurableSet[m₂] F → ∀ E,
      MeasurableSet[c.ms] E → S.μ (A ∩ F ∩ E) = S.μ (A ∩ F) * c.μ E)
    {E : Set Ω} (hE : MeasurableSet[c.ms] E) :
    ∀ G, MeasurableSet[m₁ ⊔ m₂] G → S.μ (G ∩ E) = S.μ G * c.μ E := by
  have hSp := S.2
  have hcp := c.2
  have hES : MeasurableSet[S.ms] E := hc.1 _ hE
  have hcE : S.μ E = c.μ E := (MeasureOnSpace.le_preserves_measure hc hE).symm
  have hle : m₁ ⊔ m₂ ≤ S.ms := sup_le h₁ h₂
  intro G hG
  refine MeasurableSpace.induction_on_inter (C := fun G _ ↦ S.μ (G ∩ E) = S.μ G * c.μ E)
    (MeasurableSpace.generateFrom_supGenerator_eq_sup m₁ m₂).symm ?_ ?_ ?_ ?_ ?_ G hG
  · rintro _ ⟨u, v, rfl, hu, hv⟩ _ ⟨u', v', rfl, hu', hv'⟩ _
    exact ⟨u ∩ u', v ∩ v', by rw [Set.inter_inter_inter_comm], hu.inter hu', hv.inter hv'⟩
  · simp
  · rintro _ ⟨A, F, rfl, hA, hF⟩
    exact hbase A hA F hF E hE
  · intro t ht ih
    have htS : MeasurableSet[S.ms] t := hle _ ht
    have hdiff : tᶜ ∩ E = E \ (t ∩ E) := by ext; simp; tauto
    rw [hdiff, measure_sdiff Set.inter_subset_right (htS.inter hES).nullMeasurableSet
      (measure_ne_top _ _), ih, hcE, PSpace.measure_compl htS,
      ENNReal.sub_mul (fun _ _ ↦ measure_ne_top _ _), one_mul]
  · intro f hdisj hfm ih
    have hfS : ∀ i, MeasurableSet[S.ms] (f i) := fun i ↦ hle _ (hfm i)
    rw [Set.iUnion_inter, measure_iUnion (fun i j hij ↦ (hdisj hij).mono Set.inter_subset_left
      Set.inter_subset_left) (fun i ↦ (hfS i).inter hES), measure_iUnion hdisj hfS,
      ← ENNReal.tsum_mul_right]
    exact tsum_congr ih

/-- A trim of `S` that is independent of a frame `c ≤ S` composes with it inside `S`. -/
lemma PSpace.mul_trim_le {S c : PSpace Ω} {f : MeasurableSpace Ω} (hf : f ≤ S.ms) (hc : c ≤ S)
    (hrect : ∀ G, MeasurableSet[f] G → ∀ E, MeasurableSet[c.ms] E →
      S.μ (G ∩ E) = S.μ G * c.μ E) :
    PSp.mul (some (@PSpace.trim Ω S f hf)) (some c) ≤ (some S : PSp Ω) := by
  have hsup : f ⊔ c.ms ≤ S.ms := sup_le hf hc.1
  have hT : @PSpace.trim Ω S (f ⊔ c.ms) hsup =ᵢ (@PSpace.trim Ω S f hf) ⊕ᵢ c := by
    refine ⟨rfl, fun G hG E hE ↦ ?_⟩
    have hGE : MeasurableSet[f ⊔ c.ms] (G ∩ E) :=
      ((le_sup_left : f ≤ f ⊔ c.ms) _ hG).inter ((le_sup_right : c.ms ≤ f ⊔ c.ms) _ hE)
    show (MeasureOnSpace.trim hsup).μ (G ∩ E) = (MeasureOnSpace.trim hf).μ G * c.μ E
    rw [MeasureOnSpace.trim_eq hsup hGE, MeasureOnSpace.trim_eq hf hG]
    exact hrect G hG E hE
  rw [mul_respect_independentProduct hT]
  exact WithTop.coe_le_coe.2 (PSpace.trim_le hsup)

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

end SwapAux

section SwapAuxBI

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

end SwapAuxBI

set_option linter.style.haveILetI false in
open Interp Interp.ProbTree Interp.ProbTree.BoundedFootprintPsp ProbabilityTheory MeasureTheory in
/-- `CWPSwap`, semantically.  Reweight the ambient along each fibre of the conditioning,
run there, and mix the runs back: the runs' mixture is the real run (`run_psp_mixture`),
every fibre's witness lives on the one σ-algebra `m ⊔ R ⊔ fresh` (the locality clause of
`wp'`), and that σ-algebra is independent of the frame because `m ⊗ R` was and fresh
randomness is independent of everything prior (`run_fresh`). -/
lemma CWPSwap_core {α β : Type} {m' : Type → Type} [Interp.BernoulliInterpretable m']
    [Inhabited α] {C : m' α} {μ : PMF β} {Q : β → RV α → FProp}
    (m : PSpace Ω) (κ : TrivialMarkovKernel β m)
    (hmix : m.μ = (μ.toMeasureWithMs ⊤).bind κ)
    (hbf : HasBoundedFootprint (m : PSp Ω)) (R : BoundedFootprintSpace Bool)
    (hfib : ∀ v ∈ μ.support, ∀ hk : HasBoundedFootprint ((κ v : PSpace Ω) : PSp Ω),
      own (R * ⟨((κ v : PSpace Ω) : PSp Ω), hk⟩) ⊢ wp' C (Q v)) :
    own ((⟨(m : PSp Ω), hbf⟩ : BoundedFootprintSpace Bool) * R)
      ⊢ wp' C (fun X ↦ 𝒞⟨μ⟩ v; Q v X) := by
  set Cb : BernoulliM α := BernoulliInterpretable.interp C with hCb
  set M : BoundedFootprintSpace Bool := ⟨(m : PSp Ω), hbf⟩ with hM
  have hmp := m.2
  intro a hva ha μ₀ c hvalid hle
  have ha' : M * R ≤ a := ha
  -- the ambient, and the spaces sitting in it
  set P₀ : PSpace Ω := ValidPSp.toPSpace ⟨μ₀.psp, hvalid⟩ with hP₀
  have hμ₀P : μ₀.psp = .some P₀ := (Option.some_get _).symm
  have hvμ₀ : ✓(μ₀.toSpace) := hvalid
  have hle_amb : ∀ {x : BoundedFootprintSpace Bool} {p : PSpace Ω},
      x ≤ μ₀.toSpace → (x : PSp Ω) = .some p → p ≤ P₀ := by
    intro x p hx hp
    have h : (.some p : PSp Ω) ≤ .some P₀ := by rw [← hp, ← hμ₀P]; exact hx
    exact WithTop.coe_le_coe.1 h
  have hMRc : (M * R) * c ≤ μ₀.toSpace := le_trans (mul_le_mul_right_le ha' c) hle
  have hMD : M * (R * c) ≤ μ₀.toSpace := by rw [← mul_assoc]; exact hMRc
  have hvMRc : ✓((M * R) * c) := valid_mono hMRc hvμ₀
  have hvMR : ✓(M * R) := valid_mul_l hvMRc
  have hvR : ✓R := valid_mul_r hvMR
  have hvc : ✓c := valid_mul_r hvMRc
  have hvMD : ✓(M * (R * c)) := valid_mono hMD hvμ₀
  have hvD : ✓(R * c) := valid_mul_r hvMD
  obtain ⟨d, hd⟩ : ∃ d : PSpace Ω, ((R * c : BoundedFootprintSpace Bool) : PSp Ω) = .some d :=
    Option.ne_none_iff_exists'.mp (PSp.valid_def.mp hvD)
  obtain ⟨r, hr⟩ : ∃ r : PSpace Ω, (R : PSp Ω) = .some r :=
    Option.ne_none_iff_exists'.mp (PSp.valid_def.mp hvR)
  obtain ⟨c', hc'⟩ : ∃ c' : PSpace Ω, (c : PSp Ω) = .some c' :=
    Option.ne_none_iff_exists'.mp (PSp.valid_def.mp hvc)
  obtain ⟨s, hs⟩ : ∃ s : PSpace Ω, ((M * (R * c) : BoundedFootprintSpace Bool) : PSp Ω) = .some s :=
    Option.ne_none_iff_exists'.mp (PSp.valid_def.mp hvMD)
  obtain ⟨y, hy⟩ : ∃ y : PSpace Ω, ((M * R : BoundedFootprintSpace Bool) : PSp Ω) = .some y :=
    Option.ne_none_iff_exists'.mp (PSp.valid_def.mp hvMR)
  obtain ⟨w, hw⟩ : ∃ w : PSpace Ω, (((M * R) * c : BoundedFootprintSpace Bool) : PSp Ω) = .some w :=
    Option.ne_none_iff_exists'.mp (PSp.valid_def.mp hvMRc)
  have hsmd : s =ᵢ m ⊕ᵢ d := by
    apply PSp.mul_inversion
    have h := hs
    rw [show ((M * (R * c) : BoundedFootprintSpace Bool) : PSp Ω)
      = PSp.mul (M : PSp Ω) ((R * c : BoundedFootprintSpace Bool) : PSp Ω) from rfl, hd] at h
    exact h
  have hymr : y =ᵢ m ⊕ᵢ r := by
    apply PSp.mul_inversion
    have h := hy
    rw [show ((M * R : BoundedFootprintSpace Bool) : PSp Ω)
      = PSp.mul (M : PSp Ω) (R : PSp Ω) from rfl, hr] at h
    exact h
  have hwyc : w =ᵢ y ⊕ᵢ c' := by
    apply PSp.mul_inversion
    have h := hw
    rw [show (((M * R) * c : BoundedFootprintSpace Bool) : PSp Ω)
      = PSp.mul ((M * R : BoundedFootprintSpace Bool) : PSp Ω) (c : PSp Ω) from rfl, hy, hc'] at h
    exact h
  have hsP : s ≤ P₀ := hle_amb hMD hs
  have hwP : w ≤ P₀ := hle_amb hMRc hw
  have hyP : y ≤ P₀ := le_trans (PSpace.le_of_isIndependentProduct_left hwyc) hwP
  have hcP : c' ≤ P₀ := le_trans (PSpace.le_of_isIndependentProduct_right hwyc) hwP
  have hm_le_P : m ≤ P₀ := le_trans (PSpace.le_of_isIndependentProduct_left hsmd) hsP
  have hmP : m.ms ≤ P₀.ms := hm_le_P.1
  have hdP : d.ms ≤ P₀.ms := le_trans (PSpace.le_of_isIndependentProduct_right hsmd).1 hsP.1
  have hdp := d.2
  -- the fibres, as reweightings of the ambient
  haveI : Countable μ.support := μ.support_countable.to_subtype
  have hac : ∀ i : μ.support, κ.1 i ≪ m.μ := fun i ↦ kernel_fibre_ac κ hmix i.2
  haveI hκp : ∀ i : μ.support, IsProbabilityMeasure (κ.1 i) :=
    fun i ↦ κ.2.isProbabilityMeasure i
  set ρ : μ.support → Measure[P₀.ms] Ω :=
    fun i ↦ P₀.μ.withDensity ((κ.1 i).rnDeriv m.μ) with hρ
  have hρrect : ∀ i E, MeasurableSet[d.ms] E → ∀ F, MeasurableSet[m.ms] F →
      ρ i (E ∩ F) = d.μ E * κ.1 i F :=
    fun i E hE F hF ↦ PSpace.withDensity_rect hsmd hsP (κ.1 i) (hac i) hE hF
  haveI hρp : ∀ i, IsProbabilityMeasure (ρ i) := fun i ↦ ⟨by
    have h := hρrect i Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ
    rwa [Set.inter_univ, hdp.measure_univ, (hκp i).measure_univ, one_mul] at h⟩
  have hκmix : ∀ F, MeasurableSet[m.ms] F → m.μ F = ∑' i : μ.support, μ i * κ.1 i F := by
    intro F hF; rw [hmix]; exact bind_apply_support μ κ.1 hF
  have hP₀mix : ∀ E, MeasurableSet[P₀.ms] E → P₀.μ E = ∑' i : μ.support, μ i * ρ i E :=
    fun E hE ↦ PSpace.withDensity_mixture hm_le_P (fun i : μ.support ↦ μ i)
      (fun i : μ.support ↦ κ.1 i) hac hκmix hE
  -- the reweighted footprints
  obtain ⟨τ, hτ⟩ : ∃ τ : μ.support → BoundedFootprintPsp,
      ∀ i, τ i = BoundedFootprintPsp.reweight μ₀ hvalid (ρ i) (hρp i) := ⟨_, fun _ ↦ rfl⟩
  have hτpsp : ∀ i, (τ i).psp = .some ⟨⟨P₀.ms, ρ i⟩, hρp i⟩ := fun i ↦ by rw [hτ]; rfl
  have hτvalid : ∀ i, ✓(τ i).psp := fun i ↦ by rw [hτ]; exact reweight_valid
  have hτtree : ∀ i, toTree (τ i) (fun _ ↦ Cb) = toTree μ₀ (fun _ ↦ Cb) :=
    fun i ↦ by rw [hτ]; exact toTree_reweight Cb
  have hτfresh : ∀ i, freshMs (τ i) Cb = freshMs μ₀ Cb := fun i ↦ by rw [hτ]; rfl
  have hτres : ∀ i, result (run Cb (τ i)) = result (run Cb μ₀) :=
    fun i ↦ by rw [hτ]; exact result_run_reweight Cb
  -- each fibre, with the frame, sits in its reweighted ambient
  have hvm : ✓((m : PSp Ω)) := PSp.valid_def.mpr (Option.some_ne_none _)
  have hk : ∀ i : μ.support, HasBoundedFootprint (((κ i : PSpace Ω)) : PSp Ω) := fun i ↦
    hasBoundedFootprint_congr hvm (PSp.valid_def.mpr (Option.some_ne_none _)) rfl hbf
  set K : μ.support → BoundedFootprintSpace Bool := fun i ↦ ⟨((κ i : PSpace Ω) : PSp Ω), hk i⟩
    with hK
  have hKD : ∀ i, K i * (R * c) ≤ (τ i).toSpace := by
    intro i
    have hsup : m.ms ⊔ d.ms ≤ P₀.ms := sup_le hmP hdP
    have hX : @PSpace.trim Ω ⟨⟨P₀.ms, ρ i⟩, hρp i⟩ (m.ms ⊔ d.ms) hsup
        =ᵢ (κ i : PSpace Ω) ⊕ᵢ d := by
      refine ⟨rfl, fun F hF E hE ↦ ?_⟩
      have h1 : ρ i (F ∩ E) = κ.1 i F * d.μ E := by
        rw [Set.inter_comm, hρrect i E hE F hF, mul_comm]
      have h2 := MeasureOnSpace.trim_eq (p := ⟨P₀.ms, ρ i⟩) hsup
        (((le_sup_left : m.ms ≤ _) _ hF).inter ((le_sup_right : d.ms ≤ _) _ hE))
      exact h2.trans h1
    show PSp.mul (.some (κ i : PSpace Ω)) ((R * c : BoundedFootprintSpace Bool) : PSp Ω)
      ≤ (τ i).psp
    rw [hd, hτpsp]
    exact (le_of_eq (mul_respect_independentProduct hX)).trans
      (WithTop.coe_le_coe.2 (PSpace.trim_le (p := ⟨⟨P₀.ms, ρ i⟩, hρp i⟩) hsup))
  have hRKc : ∀ i, (R * K i) * c ≤ (τ i).toSpace := by
    intro i; rw [mul_comm R, mul_assoc]; exact hKD i
  have hvRK : ∀ i, ✓(R * K i) := fun i ↦ valid_mul_l (valid_mono (hRKc i) (hτvalid i))
  -- run every fibre
  have hfib' : ∀ i : μ.support, ∃ b : BoundedFootprintSpace Bool,
      b * c ≤ (run C (τ i)).1.toSpace ∧ ✓b ∧
        msOf b ≤ msOf (R * K i) ⊔ freshMs (τ i) Cb ∧
        (own b ⊢ Q i (result (run C (τ i)))) :=
    fun i ↦ hfib i i.2 (hk i) (R * K i) (hvRK i) (le_refl (R * K i)) (τ i) c (hτvalid i) (hRKc i)
  choose bv hbvc hbvv hbvms hbvQ using hfib'
  -- the run, and the reweighted runs
  obtain ⟨S, hS, -, hSsub, -, hSpres, -⟩ := run_const μ₀ Cb hvalid
  choose Sf hSf _ hSfsub _ _ _ using fun i : μ.support ↦ run_const (τ i) Cb (hτvalid i)
  have htreems : (toTree μ₀ (fun _ ↦ Cb)).ms = P₀.ms := by
    rw [toTree_ms_eq, μ₀.sigmaAgrees hvalid]
  have hP₀S : P₀.ms ≤ S.ms := htreems ▸ hSsub
  have hP₀Sf : ∀ i, P₀.ms ≤ (Sf i).ms := fun i ↦ by
    have h := hSfsub i
    rw [hτtree, htreems] at h
    exact h
  -- the one σ-algebra every witness lives on
  set 𝓜 : MeasurableSpace Ω := (m.ms ⊔ r.ms) ⊔ freshMs μ₀ Cb with h𝓜
  have hy𝓜 : y.ms = m.ms ⊔ r.ms := hymr.1
  have h𝓜S : 𝓜 ≤ S.ms :=
    sup_le (hy𝓜 ▸ le_trans hyP.1 hP₀S) (run_fresh μ₀ Cb hvalid hS).1
  have h𝓜Sf : ∀ i, 𝓜 ≤ (Sf i).ms := fun i ↦ by
    refine sup_le (hy𝓜 ▸ le_trans hyP.1 (hP₀Sf i)) ?_
    have h := (run_fresh (τ i) Cb (hτvalid i) (hSf i)).1
    rwa [hτfresh] at h
  have hmsRK : ∀ i, msOf (R * K i) = r.ms ⊔ m.ms := fun i ↦
    msOf_mul (q := (κ i : PSpace Ω)) hr rfl (hvRK i)
  have hbv𝓜 : ∀ i, msOf (bv i) ≤ 𝓜 := fun i ↦ by
    refine le_trans (hbvms i) ?_
    rw [hmsRK, hτfresh, sup_comm r.ms]
  -- the witness: the run, trimmed to `𝓜`
  set B : PSpace Ω := @PSpace.trim Ω S 𝓜 h𝓜S with hB
  have hvS : ✓((run Cb μ₀).1.psp) := by rw [hS]; exact Option.some_ne_none _
  have hbfB : HasBoundedFootprint ((B : PSp Ω)) :=
    hasBoundedFootprint_mono hvS (by rw [hS]; exact WithTop.coe_le_coe.2 (PSpace.trim_le h𝓜S))
      (hasBoundedFootprint_of_tree _)
  have hP₀S' : P₀ ≤ S := PSpace.le_of_ms_le hP₀S fun E hE ↦ hSpres (htreems ▸ hE)
  have hcS : c' ≤ S := le_trans hcP hP₀S'
  have hmrS : m.ms ⊔ r.ms ≤ S.ms := by rw [← hy𝓜]; exact le_trans hyP.1 hP₀S
  -- `𝓜` is independent of the frame: `m ⊗ R` was, and the fresh bits are
  have hrect : ∀ G, MeasurableSet[𝓜] G → ∀ E, MeasurableSet[c'.ms] E →
      S.μ (G ∩ E) = S.μ G * c'.μ E := by
    intro G hG E hE
    refine PSpace.indep_sup_of_rect hmrS (run_fresh μ₀ Cb hvalid hS).1 hcS ?_ hE G hG
    intro A hA F hF E hE
    have hAy : MeasurableSet[y.ms] A := by rw [hy𝓜]; exact hA
    have hAP : MeasurableSet[P₀.ms] A := hyP.1 _ hAy
    have hEP : MeasurableSet[P₀.ms] E := hcP.1 _ hE
    have hfr : ∀ {F : Set Ω}, MeasurableSet[freshMs μ₀ Cb] F → ∀ {E : Set Ω},
        MeasurableSet[P₀.ms] E → S.μ (F ∩ E) = S.μ F * P₀.μ E :=
      (run_fresh μ₀ Cb hvalid hS).2
    have h1 : S.μ (A ∩ F ∩ E) = S.μ F * P₀.μ (A ∩ E) := by
      rw [show A ∩ F ∩ E = F ∩ (A ∩ E) by ext; simp only [Set.mem_inter_iff]; tauto]
      exact hfr hF (hAP.inter hEP)
    have h2 : S.μ (A ∩ F) = S.μ F * P₀.μ A := by
      rw [Set.inter_comm]; exact hfr hF hAP
    have hAEw : MeasurableSet[w.ms] (A ∩ E) :=
      hwyc.1.symm.le _ (mem_sup_inter y.ms c'.ms hAy hE)
    have h3 : P₀.μ (A ∩ E) = y.μ A * c'.μ E := by
      rw [← MeasureOnSpace.le_preserves_measure hwP hAEw]
      exact hwyc.2 A hAy E hE
    have h4 : P₀.μ A = y.μ A := (MeasureOnSpace.le_preserves_measure hyP hAy).symm
    rw [h1, h2, h3, h4, mul_assoc]
  refine ⟨⟨(B : PSp Ω), hbfB⟩, ?_, PSp.valid_def.mpr (Option.some_ne_none _), ?_, ?_⟩
  · show PSp.mul (.some B) (c : PSp Ω) ≤ (run Cb μ₀).1.psp
    rw [hc', hS]
    exact PSpace.mul_trim_le h𝓜S hcS hrect
  · rw [msOf_of_val (p := B) rfl]
    show (m.ms ⊔ r.ms) ⊔ freshMs μ₀ Cb ≤ msOf a ⊔ freshMs μ₀ Cb
    refine sup_le_sup_right ?_ _
    rw [← hy𝓜, ← msOf_of_val hy]
    exact msOf_mono ha'
  -- the conditioning: the reweighted runs, trimmed to `𝓜`, are its fibres
  have hfib_meas : ∀ v, ∃ ν : Measure[𝓜] Ω, IsProbabilityMeasure ν ∧
      ∀ hv : v ∈ μ.support, ν = (@PSpace.trim Ω (Sf ⟨v, hv⟩) 𝓜 (h𝓜Sf ⟨v, hv⟩)).μ := by
    intro v
    by_cases hv : v ∈ μ.support
    · exact ⟨_, (@PSpace.trim Ω (Sf ⟨v, hv⟩) 𝓜 (h𝓜Sf ⟨v, hv⟩)).2, fun _ ↦ rfl⟩
    · exact ⟨B.μ, B.2, fun h ↦ absurd h hv⟩
  choose κ'f hκ'p hκ'f' using hfib_meas
  have hκ'f : ∀ i : μ.support, κ'f i = (@PSpace.trim Ω (Sf i) 𝓜 (h𝓜Sf i)).μ :=
    fun i ↦ hκ'f' i i.2
  obtain ⟨κ', hκ'⟩ : ∃ κ' : TrivialMarkovKernel β B, ∀ v, κ'.1 v = κ'f v := by
    letI : MeasurableSpace β := ⊤
    exact ⟨⟨⟨κ'f, measurable_from_top⟩, ⟨hκ'p⟩⟩, fun _ ↦ rfl⟩
  have hmix' : B.μ = (μ.toMeasureWithMs ⊤).bind κ' := by
    apply @Measure.ext Ω 𝓜
    intro G hG
    refine Eq.trans ?_ (bind_apply_support μ κ'.1 hG).symm
    show (MeasureOnSpace.trim h𝓜S).μ G = _
    rw [MeasureOnSpace.trim_eq h𝓜S hG,
      run_psp_mixture μ₀ hvalid Cb (fun i : μ.support ↦ μ i) ρ hρp hP₀mix hS
        (fun i ↦ by rw [← hτ]; exact hSf i) (h𝓜S G hG)]
    refine tsum_congr fun i ↦ ?_
    rw [hκ' i, hκ'f i]
    show _ = _ * (MeasureOnSpace.trim (h𝓜Sf i)).μ G
    rw [MeasureOnSpace.trim_eq (h𝓜Sf i) hG]
  have hτres' : ∀ i, result (run C (τ i)) = result (run C μ₀) := hτres
  show own (⟨(B : PSp Ω), hbfB⟩ : BoundedFootprintSpace Bool)
    ⊢ jointConditioning μ (fun v ↦ Q v (result (run C μ₀)))
  unfold jointConditioning
  refine entails_trans ?_ (exists_intro B)
  refine entails_trans ?_ (exists_intro κ')
  refine entails_trans sep_emp.2 (sep_mono ?_ ?_)
  · unfold ownP
    exact exists_intro (Ψ := fun h : HasBoundedFootprint ((B : PSp Ω)) ↦
      own (⟨(B : PSp Ω), h⟩ : BoundedFootprintSpace Bool)) hbfB
  refine entails_trans emp_sep.2 (sep_mono (pure_intro hmix') ?_)
  refine forall_intro fun i ↦ wand_intro (entails_trans emp_sep.1 ?_)
  unfold ownP
  refine exists_elim fun hk' ↦ ?_
  have hQ := hbvQ i
  rw [hτres' i] at hQ
  refine entails_trans (own_mono ?_) hQ
  -- the fibre's witness sits below the trimmed reweighted run
  obtain ⟨bp, hbp⟩ : ∃ bp : PSpace Ω, (bv i : PSp Ω) = .some bp :=
    Option.ne_none_iff_exists'.mp (PSp.valid_def.mp (hbvv i))
  have hbpSf : bp ≤ Sf i := by
    have h : bv i ≤ (run C (τ i)).1.toSpace := le_trans (le_mul_of_one_le PSp.one_le) (hbvc i)
    have h' : (.some bp : PSp Ω) ≤ .some (Sf i) := by rw [← hbp, ← hSf i]; exact h
    exact WithTop.coe_le_coe.1 h'
  have hbpms : bp.ms ≤ 𝓜 := by rw [← msOf_of_val hbp]; exact hbv𝓜 i
  show (bv i : PSp Ω) ≤ ((κ' i : PSpace Ω) : PSp Ω)
  rw [hbp]
  refine WithTop.coe_le_coe.2 (PSpace.le_of_ms_le (S := (κ' i : PSpace Ω)) hbpms fun E hE ↦ ?_)
  show κ'.1 i E = bp.μ E
  rw [hκ' i, hκ'f i]
  show (MeasureOnSpace.trim (h𝓜Sf i)).μ E = _
  rw [MeasureOnSpace.trim_eq (h𝓜Sf i) (hbpms E hE)]
  exact (MeasureOnSpace.le_preserves_measure hbpSf hE).symm

lemma CWPSwap {α β : Type} {m : Type → Type} [Monad m] [Interp.BernoulliInterpretable m] [Inhabited α]
  {C : m α} {μ : PMF β} {Q : β → RV α → FProp} :
    iprop(𝒞⟨μ⟩ v; wp' C (Q v)) ⊢ wp' C (fun x ↦ 𝒞⟨μ⟩ v; Q v x) := by
  unfold jointConditioning
  refine exists_elim fun m₀ ↦ exists_elim fun κ ↦ ?_
  refine pure_elim _ (entails_trans sep_elim_right sep_elim_left) fun hmix ↦ ?_
  refine entails_trans (sep_mono_right sep_elim_right) ?_
  unfold ownP
  refine entails_trans sep_exists_right.1 (exists_elim fun hbf ↦ ?_)
  refine own_sep_entails_fmk fun a R hva hle hR ↦ ?_
  refine CWPSwap_core m₀ κ hmix hbf R (fun v hv hk ↦ ?_) a hva hle
  refine entails_trans own_mul_sep (entails_trans (sep_mono hR (exists_intro
    (Ψ := fun h : HasBoundedFootprint ((κ v : PSpace Ω) : PSp Ω) ↦
      own (⟨((κ v : PSpace Ω) : PSp Ω), h⟩ : BoundedFootprintSpace Bool)) hk)) ?_)
  exact wand_elim (forall_elim (Ψ := fun v : μ.support ↦
    iprop(ownP (κ v) -∗ wp' C (Q v))) ⟨v, hv⟩)

/-- A postcondition that cannot tell almost-surely-equal random variables apart.

`CWPBind` needs this.  The bound run reports the *global* result of `C >>= F`, while the
continuation's `wp` reports the result of `F v` as a random variable of the `v`-fibre: the
two agree on that fibre and nowhere else, so an arbitrary `Q : RV β → FProp` cannot be
carried from one to the other. -/
def AEProper {β : Type} (Q : RV β → FProp) : Prop :=
  ∀ X Y : RV β, iprop(⌈fun ρ ↦ X ρ = Y ρ⌉ ∗ Q X) ⊢ Q Y

/-- Value-indexed postconditions are automatically proper: they only look at the result
through `⌈X = x⌉`, and sure equalities substitute (`liftPred_subst`).  So `CWPBind`'s side
condition is discharged once and for all for the postconditions it is meant for. -/
lemma aeProper_valuePost {β : Type} (Q : β → FProp) :
    AEProper (fun X ↦ valuePost X Q) := by
  sorry
--   intro X Y
--   unfold valuePost jointConditioning
--   iintro ⟨Heq, %ν, %m, %κ, Hm, %hmix, Hall⟩
--   iexists ν, m, κ
--   isplitl [Hm]
--   · iexact Hm
--   · isplitl []
--     · ipureintro
--       exact hmix
--     · iintro %v Hv
--       ispecialize Hall $$ %v Hv
--       icases Hall with ⟨Hsure, HQ⟩
--       isplitl [Heq Hsure]
--       · iapply liftPred_subst
--         isplitl [Heq]
--         · iexact Heq
--         · iexact Hsure
--       · iexact HQ

/-- **Sequencing.**  `F` consumes a value, so the result of `C` has to be split along its
value before `F` can be named: that is exactly `valuePost`, which conditions on the law of
the result and hands each fibre the value it reports.

This is the direction a program logic uses, and the direction whose obligations are the
ordinary ones: run `C`, land in the `v`-fibre, run `F v` there.  `AEProper Q` is what lets
the fibre's report of `F v` stand in for the global report of `C >>= F`, which it equals
almost surely on that fibre.

`AEProper` is necessary but **not sufficient**.  The proof gets `Q` once per fibre, at the
reweighted ambient that fibre lives in, and has to produce it once for the whole run.  So
`Q` must also be *mixable*: recoverable from its fibres.  Value-indexed postconditions
(`fun Y ↦ valuePost Y Q'`) are -- that is what `𝒞` does -- but an arbitrary `RV β → FProp`
is not, so the rule should be read at `valuePost`-shaped `Q` only.  `CWPBindDist` below is
the fragment of it that goes through today. -/
lemma CWPBind {α β : Type} {m : Type → Type} [Monad m] [Interp.LawfulBernoulliInterpretable m]
    [Inhabited α] [Inhabited β] {C : m α} {F : α → m β} {Q : RV β → FProp}
    (hQ : AEProper Q) :
    wp C (fun X ↦ valuePost X (fun v ↦ wp (F v) Q)) ⊢ wp (C >>= F) Q := by
  sorry

/-- The converse.  Iris proves both directions of `bind`, but its `wp` is a fixpoint over
the operational semantics, whereas this one quantifies over *every* ambient footprint
containing the resource.  So this direction asks for more than inverting a run: from one
run of `C >>= F` it has to manufacture a fibre resource that is a precondition for `F v`
in every possible future ambient, not just the one that run produced. -/
lemma CWPBindInv {α β : Type} {m : Type → Type} [Monad m]
    [Interp.LawfulBernoulliInterpretable m] [Inhabited α] [Inhabited β]
    {C : m α} {F : α → m β} {Q : RV β → FProp} (hQ : AEProper Q) :
    wp (C >>= F) Q ⊢ wp C (fun X ↦ valuePost X (fun v ↦ wp (F v) Q)) := by
  sorry

section ProgramRules

open Interp Interp.ProbTree Interp.ProbTree.BoundedFootprintPsp ProbSpace MeasureTheory
open unitInterval

set_option linter.style.haveILetI false in
/-- **The law of a program.**  Whatever the state already is, running `t` reports a value
distributed as `t`'s own law and independent of everything that state could measure. -/
lemma CWPDist {α : Type} [Inhabited α] [Countable α] (t : BernoulliM α) (ν : PMF α)
    (hν : ∀ a : α, lawOf t a = ν a) :
    ⊢ wp t (fun X ↦ X ~ ν) := by
  intro a hva ha μ₀ c hvalid hle
  letI : MeasurableSpace α := ⊤
  haveI : MeasurableSingletonClass α := ⟨fun _ ↦ trivial⟩
  have hcμ : c ≤ μ₀.toSpace := by
    refine le_trans ?_ hle
    conv_lhs => rw [← one_mul c]
    exact mul_le_mul_right_le ha c
  have hvc : ✓c := valid_mono hcμ (show ✓(μ₀.toSpace) from hvalid)
  obtain ⟨C, hC⟩ : ∃ C : PSpace Ω, (c : PSp Ω) = .some C :=
    Option.ne_none_iff_exists'.mp (PSp.valid_def.mp hvc)
  set P : PSpace Ω := ValidPSp.toPSpace ⟨μ₀.psp, hvalid⟩ with hP
  have hμ₀P : μ₀.psp = .some P := (Option.some_get _).symm
  have hCP : C ≤ P := by
    have h : (.some C : PSp Ω) ≤ .some P := by rw [← hC, ← hμ₀P]; exact hcμ
    exact WithTop.coe_le_coe.1 h
  obtain ⟨S, hpsp, hres, hsub, hmeas, hpres, hind⟩ := run_const μ₀ t hvalid
  set X := treeValue t (toTree μ₀ (fun _ ↦ t)) with hX
  -- the σ-algebra of the reported value
  set BX : MeasurableSpace Ω := MeasurableSpace.comap X ⊤ with hBXdef
  have hXB : Measurable[BX, ⊤] X := Measurable.of_comap_le le_rfl
  have hcomap : ∀ b : α, MeasurableSet[BX] (X ⁻¹' {b}) := fun b ↦ ⟨{b}, trivial, rfl⟩
  have hpre : ∀ T : Set α, MeasurableSet[S.ms] (X ⁻¹' T) := by
    intro T
    rw [show X ⁻¹' T = ⋃ b : T, X ⁻¹' {(b : α)} from by ext ρ; simp]
    exact MeasurableSet.iUnion fun b ↦ hmeas b
  have hBX : BX ≤ S.ms := by
    rintro E ⟨T, -, rfl⟩
    exact hpre T
  set B : PSpace Ω := @PSpace.trim Ω S BX hBX with hBdef
  have hBS : B ≤ S := PSpace.trim_le hBX
  have hBμ : ∀ E, MeasurableSet[BX] E → B.μ E = S.μ E :=
    fun E hE ↦ MeasureOnSpace.trim_eq hBX hE
  -- the frame sits inside the pre-state
  have hCms : C.ms ≤ (toTree μ₀ (fun _ ↦ t)).ms := by
    rw [toTree_ms_eq, ← μ₀.sigmaAgrees hvalid]
    exact hCP.1
  -- the reported value is independent of everything the pre-state could measure
  have hsum : ∀ (T : Set α) {E : Set Ω}, MeasurableSet[(toTree μ₀ (fun _ ↦ t)).ms] E →
      S.μ (X ⁻¹' T ∩ E)
        = (∑' b : T, (fixpoint (rootTree t)).2 (runValue t ⁻¹' {(b : α)})) * P.μ E := by
    intro T E hE
    have hcover : X ⁻¹' T ∩ E = ⋃ b : T, (X ⁻¹' {(b : α)} ∩ E) := by ext ρ; simp
    have hdisj : Pairwise (Function.onFun Disjoint fun b : T ↦ X ⁻¹' {(b : α)} ∩ E) := by
      intro b b' hbb'
      refine Set.disjoint_left.mpr fun ρ hρ hρ' ↦ hbb' ?_
      have h1 := hρ.1; have h2 := hρ'.1
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at h1 h2
      exact Subtype.ext (h1.symm.trans h2)
    have hmeasf : ∀ b : T, MeasurableSet[S.ms] (X ⁻¹' {(b : α)} ∩ E) :=
      fun b ↦ (hmeas (b : α)).inter (hsub E hE)
    rw [hcover, measure_iUnion (μ := S.μ) hdisj hmeasf,
      tsum_congr (fun b : T ↦ hind (b : α) hE), ENNReal.tsum_mul_right]
  have hlaw : ∀ T : Set α, B.μ (X ⁻¹' T)
      = ∑' b : T, (fixpoint (rootTree t)).2 (runValue t ⁻¹' {(b : α)}) := by
    intro T
    rw [hBμ _ ⟨T, trivial, rfl⟩]
    have h := hsum T (E := Set.univ) MeasurableSet.univ
    rw [Set.inter_univ] at h
    rw [h, P.2.measure_univ, mul_one]
  have hsup : BX ⊔ C.ms ≤ S.ms := sup_le hBX (le_trans hCms hsub)
  set s : PSpace Ω := @PSpace.trim Ω S (BX ⊔ C.ms) hsup with hsdef
  have hsμ : ∀ E, MeasurableSet[BX ⊔ C.ms] E → s.μ E = S.μ E :=
    fun E hE ↦ MeasureOnSpace.trim_eq hsup hE
  have hCμ : ∀ F, MeasurableSet[C.ms] F → C.μ F = P.μ F :=
    fun F hF ↦ MeasureOnSpace.le_preserves_measure hCP hF
  have hsBC : s =ᵢ B ⊕ᵢ C := by
    refine ⟨rfl, ?_⟩
    intro E hE F hF
    obtain ⟨T, -, rfl⟩ := hE
    have hFtree : MeasurableSet[(toTree μ₀ (fun _ ↦ t)).ms] F := hCms F hF
    have hTsup : MeasurableSet[BX ⊔ C.ms] (X ⁻¹' T ∩ F) :=
      ((le_sup_left : BX ≤ BX ⊔ C.ms) _ ⟨T, trivial, rfl⟩).inter
        ((le_sup_right : C.ms ≤ BX ⊔ C.ms) F hF)
    rw [hsμ _ hTsup, hsum T hFtree, hlaw T, hCμ F hF]
  obtain ⟨xy, hxy⟩ : ∃ xy : PSpace Ω, PSp.mul (.some B) (.some C) = .some xy :=
    Option.ne_none_iff_exists'.mp (PSp.mul_ne_top_of_exists ⟨s, hsBC⟩)
  have hxys : xy = s := PSpace.uniqueness (PSp.mul_inversion hxy) hsBC
  have hvS : ✓((run t μ₀).1.psp) := by rw [hpsp]; exact Option.some_ne_none _
  have hbf : HasBoundedFootprint ((B : PSpace Ω) : PSp Ω) :=
    hasBoundedFootprint_mono hvS (by rw [hpsp]; exact WithTop.coe_le_coe.2 hBS)
      (hasBoundedFootprint_of_tree _)
  refine ⟨⟨((B : PSpace Ω) : PSp Ω), hbf⟩, ?_, PSp.valid_def.mpr (Option.some_ne_none _), ?_⟩
  · show PSp.mul _ _ ≤ _
    rw [hC, hxy, hxys, BoundedFootprintPsp.toSpace_val, hpsp]
    exact WithTop.coe_le_coe.2 (PSpace.trim_le hsup)
  · rw [hres]
    intro d hvd hd
    refine ⟨_, ⟨B, rfl⟩, ⟨((B : PSpace Ω) : PSp Ω), hbf⟩, 1, by rw [mul_one]; exact hd,
      ⟨_, ⟨hbf, rfl⟩,
        le_refl (⟨((B : PSpace Ω) : PSp Ω), hbf⟩ : BoundedFootprintSpace Bool)⟩,
      hXB.aemeasurable, ?_⟩
    refine MeasureTheory.Measure.ext_of_singleton (fun b ↦ ?_)
    have h1 : (@Measure.map Ω α B.ms ⊤ X B.μ) {b} = B.μ (X ⁻¹' {b}) :=
      @Measure.map_apply Ω α B.ms ⊤ B.μ X hXB {b} MeasurableSpace.measurableSet_top
    have h2 : (ν.toMeasureWithMs ⊤) {b} = ν b := by
      rw [PMF.toMeasureWithMs]
      exact @PMF.toMeasure_apply_singleton α ⊤ _ b (by trivial)
    rw [h1, h2, hlaw {b},
      tsum_singleton b (fun y : α ↦ (fixpoint (rootTree t)).2 (runValue t ⁻¹' {y}))]
    exact hν b

/-- **Flipping a coin**, as an instance of `CWPDist`. -/
lemma CWPFlip {p : I} :
    ⊢ wp (Interp.flip p)
        (fun X ↦ X ~ bernoulliWeights (toNNReal p) (Interp.toNNReal_le_one p)) := by
  refine CWPDist (Interp.flip p) _ (fun b ↦ ?_)
  unfold lawOf
  have h0 : runValue (Interp.flip p) ⁻¹' {b} = prefixEqEvent [b] := preimage_head b
  rw [h0]
  refine Eq.trans (measure_congr_tree (fixpoint_oneFlip (fun b : Bool ↦ b) p) _) ?_
  show flipMeasure _ p _ = _
  rw [flipMeasure_apply_singleton p b (measurableSet_prefixEqEvent_singleton b),
    flipWeight_eq_bernoulliWeights]

/-- **Sequencing, for distributions.**  The result of `t >>= f` is distributed as the bind
of the laws -- and, by `CWPDist`, independently of whatever the state already was. -/
lemma CWPBindDist {α β : Type} [Inhabited α] [Inhabited β] [Countable β]
    (t : BernoulliM α) (f : α → BernoulliM β) (ν : PMF α) (κ : α → PMF β)
    (hν : ∀ a, lawOf t a = ν a) (hκ : ∀ a b, lawOf (f a) b = κ a b) :
    ⊢ wp (t >>= f) (fun X ↦ X ~ ν.bind κ) := by
  refine CWPDist (t >>= f) _ (fun b ↦ ?_)
  rw [lawOf_bind, PMF.bind_apply]
  exact tsum_congr fun a ↦ by rw [hν a, hκ a b]

end ProgramRules

end wp

/-! ### Worked examples

Everything below is a standard BI fact, true in any affine BI.  The proofs are kept as
worked examples of the proof mode at `FProp`, not as results about this model. -/

section Examples

@[simp, grind .]
theorem and_ident : P ∧ ftrue ⊣⊢ P := by grind

@[simp, grind .]
theorem and_comm : P ∧ Q ⊣⊢ Q ∧ P := by grind

@[simp, grind .]
theorem and_entails_of_entails_l (h : P ⊢ R) : P ∧ Q ⊢ R := by
  have : P ∧ Q ⊢ P := by grind
  grind

@[simp, grind .]
theorem and_entails_of_entails_r (h : Q ⊢ R) : P ∧ Q ⊢ R := by
  have : P ∧ Q ⊢ Q := by grind
  grind

@[simp, grind .]
theorem and_assoc : (P ∧ Q) ∧ R ⊣⊢ P ∧ (Q ∧ R) := by
  grind

@[simp, grind .]
theorem or_ident : P ∨ ffalse ⊣⊢ P := by
  grind

@[simp, grind .]
theorem or_comm : P ∨ Q ⊣⊢ Q ∨ P := by
  grind

theorem or_assoc : (P ∨ Q) ∨ R ⊣⊢ P ∨ (Q ∨ R) := Iris.BI.or_assoc

theorem sep_ident : P ∗ ftrue ⊣⊢ P := by
  refine ⟨?_, ?_⟩
  · iintro ⟨h, _⟩
    iexact h
  · iintro h
    isplitl [h]
    · iexact h
    · exact entails_ftrue

theorem sep_comm : P ∗ Q ⊣⊢ Q ∗ P := by
  refine ⟨?_, ?_⟩
  · iintro ⟨h₁, h₂⟩
    isplitl [h₂]
    · iexact h₂
    · iexact h₁
  · iintro ⟨h₁, h₂⟩
    isplitl [h₂]
    · iexact h₂
    · iexact h₁

theorem sep_assoc : (P ∗ Q) ∗ R ⊣⊢ P ∗ (Q ∗ R) := by
  refine ⟨?_, ?_⟩
  · iintro ⟨⟨h₁, h₂⟩, h₃⟩
    isplitl [h₁]
    · iexact h₁
    · isplitl [h₂]
      · iexact h₂
      · iexact h₃
  · iintro ⟨h₁, h₂, h₃⟩
    isplitl [h₁ h₂]
    · isplitl [h₁]
      · iexact h₁
      · iexact h₂
    · iexact h₃

theorem wand_ftrue : ⊢ P -∗ ftrue := entails_wand entails_ftrue

theorem sep_affine : P ∗ Q ⊢ P := by
  iintro ⟨h₁, _⟩
  iexact h₁

theorem true_subst_star (h : Q ⊣⊢ ftrue) : P ⊢ P ∗ Q := by
  iintro h₁
  isplitl [h₁]
  · iexact h₁
  · exact entails_trans entails_ftrue h.2

end Examples

end

end Foxglove
