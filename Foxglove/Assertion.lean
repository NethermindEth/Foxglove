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

open Interp Interp.ProbTree Iris.BI OURAProp in
def wp {α : Type} [Inhabited α] {m : Type → Type} [Interp.BernoulliInterpretable m]
    (t : m α) (Q : RV α → FProp) : FProp :=
  fmk {
    carrier := {a |
      ∀ (μ₀ : BoundedFootprintPsp) (c : BoundedFootprintSpace Bool),
        ✓μ₀.psp → a * c ≤ μ₀.toSpace →
        ∃ b : BoundedFootprintSpace Bool,
          b * c ≤ (run t μ₀).1.toSpace ∧ ✓b ∧ (own b ⊢ Q (result (run t μ₀)))}
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
  unfold jointConditioning
  iexists (1 : PSpace Ω), unitKernel A
  isplitl []
  · exact ownP_one
  · isplitl []
    · ipureintro
      show PSpace.μ 1 = (μ.toMeasureWithMs ⊤).bind (fun _ ↦ PSpace.μ 1)
      simp [PMF.toMeasureWithMs]
    · iintro %v Hv
      exact entails_ftrue

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

/-- Sure facts merge.  Only this direction holds in this model -- see the note above. -/
theorem ESureMerge {E₁ E₂ : RV Bool}
  : ⌈fun ω ↦ E₁ ω = true⌉ ∗ ⌈fun ω ↦ E₂ ω = true⌉ ⊢ ⌈fun ω ↦ E₁ ω ∧ E₂ ω = true⌉ :=
  liftPred_sep

-- Not provable as stated; see the note above.
-- theorem EDiracDup {A : Type} {E : RV A} (v : A) : E ~ δ v ⊢ E ~ δ v ∗ E ~ δ v

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
