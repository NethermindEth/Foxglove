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

-- def liftPred (a : Ω → Prop) : FProp :=
--   iprop(∃ P : PSpace Ω, ownP P ∗ ⌜P.μ {ρ | ¬ a ρ} = 0⌝)

class LiftPred (α : Type) where
  lift : (Ω → α) → FProp

instance : LiftPred Prop where
  lift a := iprop(∃ P : PSpace Ω, ownP P ∗ ⌜P.μ {ρ | ¬ a ρ} = 0⌝)

instance : LiftPred Bool where
  lift a := iprop(∃ P : PSpace Ω, ownP P ∗ ⌜P.μ {ρ | ¬ a ρ} = 0⌝)

class LiftAny (β : Type) where
  lift : β → Ω → Prop

instance : LiftAny (Ω → Prop) := ⟨fun a ω ↦ a ω⟩

instance : LiftAny (RV Bool) := ⟨fun E ω ↦ E ω = true⟩

instance : LiftAny Prop := ⟨fun p _ ↦ p⟩

syntax "lift(" term ", " term ")" : term

macro_rules
  | `(lift(¬$a, $ρ))     => `(¬lift($a, $ρ))
  | `(lift($a ∧ $b, $ρ)) => `(lift($a, $ρ) ∧ lift($b, $ρ))
  | `(lift($a ∨ $b, $ρ)) => `(lift($a, $ρ) ∨ lift($b, $ρ))
  | `(lift($a → $b, $ρ)) => `(lift($a, $ρ) → lift($b, $ρ))
  | `(lift(($x), $ρ))    => `(lift($x, $ρ))
  | `(lift($x, $ρ))      => `(LiftAny.lift $x $ρ)

syntax (name := liftStx) (priority := high) "⌈" term "⌉" : term  

macro_rules (kind := liftStx)
  | `(⌈$t⌉) => `(LiftPred.lift fun ω ↦ lift($t, ω))

/-- Assertions of the shape `∃ P, ownP P ∗ ⌜φ P⌝` -- the shape `hasDistribution` and
`liftPred` share -- with pointwise equivalent side conditions are the same assertion. -/
theorem ownP_pure_congr {φ ψ : PSpace Ω → Prop} (h : ∀ P, φ P ↔ ψ P) :
    (iprop(∃ P : PSpace Ω, ownP P ∗ ⌜φ P⌝) : FProp)
      = iprop(∃ P : PSpace Ω, ownP P ∗ ⌜ψ P⌝) := by
  have hfe : φ = ψ := funext fun P ↦ propext (h P)
  rw [hfe]

def valuePost {α : Type} (X : RV α) (Q : α → FProp) : FProp :=
  iprop(∃ ν : PMF α, 𝒞⟨ν⟩ x; (⌈fun ρ ↦ X ρ = x⌉ ∗ Q x))

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

/-
Rules named `<RULE>'` are heavily modified from the Bluebell model and are likely safe to
disregard.

TODO - They need a review because I kinda just put whatever I thought was semi-reasonable.
-/

section DistributionOwnershipRules

variable {P Q : FProp} {α β : Type}
         {E E₁ E₂ : RV Bool}
         {μ μ' μ₁ μ₂ : PMF Bool}

/--
Not relevant for Foxglove.
-/
private
theorem AND_TO_STAR'_PRF (h : (⊢ P) ∨ (⊢ Q)) : P ∧ Q ⊢ P ∗ Q := by
  rcases h with hP | hQ
  · exact entails_trans and_elim_r (entails_trans emp_sep.2 (sep_mono_left hP))
  · exact entails_trans and_elim_l (entails_trans sep_emp.2 (sep_mono_right hQ))

open MeasureTheory in
theorem DIST_INJ : E ~ μ ∧ E ~ μ' ⊢ ⌜μ = μ'⌝ := by
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
  apply @PMF.toMeasure_injective _ ⊤
  calc @PMF.toMeasure _ ⊤ μ
      = @Measure.map Ω _ P.ms ⊤ E P.μ := hμ₁.symm
    _ = @Measure.map Ω _ P'.ms ⊤ E P'.μ := PSpace.map_eq_of_le hPy hP'y ham ham'
    _ = @PMF.toMeasure _ ⊤ μ' := hμ₂

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

theorem SURE_MERGE : ⌈E₁⌉ ∗ ⌈E₂⌉ ⊣⊢ ⌈E₁ ∧ E₂⌉ :=
  ⟨liftPred_sep, liftPred_split⟩

open MeasureTheory in
/-- A space carrying only the measures `0` and `1` and sitting below `y` is independent of
`y`, with `y` itself as the product. -/
theorem PSpace.isIndependentProduct_of_zero_one_le {p y : PSpace Ω} (hpy : p ≤ y)
    (h01 : ∀ t, @MeasurableSet Ω p.ms t → p.μ t = 0 ∨ p.μ t = 1) : y =ᵢ p ⊕ᵢ y := by
  have hy := y.2
  refine ⟨(sup_eq_right.mpr hpy.1).symm, fun E hE F _ ↦ ?_⟩
  have hEy : p.μ E = y.μ E := MeasureOnSpace.le_preserves_measure hpy hE
  rcases h01 E hE with h | h
  · rw [h, zero_mul]
    exact measure_mono_null Set.inter_subset_left (hEy.symm.trans h)
  · rw [h, one_mul]
    refine le_antisymm (measure_mono Set.inter_subset_right) ?_
    have hc : y.μ Eᶜ = 0 := by
      rw [PSpace.measure_compl (hpy.1 _ hE), ← hEy, h]; simp
    calc y.μ F ≤ y.μ ((E ∩ F) ∪ Eᶜ) := by
          refine measure_mono fun x hx ↦ ?_
          by_cases hxe : x ∈ E
          · exact Or.inl ⟨hxe, hx⟩
          · exact Or.inr hxe
      _ ≤ y.μ (E ∩ F) + y.μ Eᶜ := measure_union_le _ _
      _ = y.μ (E ∩ F) := by rw [hc, add_zero]

/-- A sure fact can be split off any assertion it holds alongside: its 0-1 trim (as in
`liftPred_split`) is independent of the whole resource and multiplies with it to itself. -/
theorem Sure_And_Star : ⌈E₁⌉ ∧ P ⊢ ⌈E₁⌉ ∗ P := by
  induction P using Quotient.ind
  intro m hv ⟨hE, hP⟩
  obtain ⟨q, ⟨W, hq⟩, hqm⟩ := hE
  obtain ⟨d₁, d₂, hle, hown, hpure⟩ := (Quotient.exact hq).2 m hv hqm
  obtain ⟨r₁, ⟨hbfW, hr₁⟩, hd₁⟩ := hown
  have hd₁m : d₁ ≤ m := le_trans (le_mul_of_one_le PSp.one_le) hle
  have hWm : (⟨(W : PSp Ω), hbfW⟩ : BoundedFootprintSpace Bool) ≤ m :=
    le_trans ((Quotient.exact hr₁).2 d₁ (valid_mono hd₁m hv) hd₁) hd₁m
  obtain ⟨y, hy⟩ : ∃ y : PSpace Ω, m.val = (y : PSp Ω) :=
    Option.ne_none_iff_exists'.mp (PSp.valid_def.mp hv)
  have hWy : W ≤ y := by
    have h : (W : PSp Ω) ≤ (m : PSp Ω) := hWm
    rw [hy] at h
    exact WithTop.coe_le_coe.1 h
  -- a measurable null cover of the exceptional set, and the 0-1 trim it generates
  obtain ⟨N, hNsub, hNmeas, hNnull⟩ :=
    @MeasureTheory.exists_measurable_superset_of_null Ω W.ms W.μ _ hpure
  have hgen : MeasurableSpace.generateFrom {N} ≤ W.ms :=
    MeasurableSpace.generateFrom_le (by rintro t rfl; exact hNmeas)
  set W₀ : PSpace Ω := @PSpace.trim Ω W _ hgen with hW₀
  have hW₀W : W₀ ≤ W := PSpace.trim_le hgen
  have hNmeas₀ : @MeasurableSet Ω W₀.ms N := MeasurableSpace.measurableSet_generateFrom rfl
  have hN₀ : W₀.μ N = 0 := by
    rw [MeasureOnSpace.le_preserves_measure hW₀W hNmeas₀]
    exact hNnull
  have hbf₀ : HasBoundedFootprint ((W₀ : PSp Ω)) :=
    hasBoundedFootprint_mono (PSp.valid_def.mpr (Option.some_ne_none _))
      (WithTop.coe_le_coe.2 hW₀W) hbfW
  -- the trim is independent of the whole space, so splitting it off costs nothing
  have hind : y =ᵢ W₀ ⊕ᵢ y :=
    PSpace.isIndependentProduct_of_zero_one_le (le_trans hW₀W hWy)
      (PSpace.zero_or_one_generateFrom (le_refl _) hN₀)
  have hb₀m : (⟨(W₀ : PSp Ω), hbf₀⟩ : BoundedFootprintSpace Bool) * m ≤ m := by
    show PSp.mul (W₀ : PSp Ω) m.val ≤ m.val
    rw [hy]
    exact le_of_eq (mul_respect_independentProduct hind)
  refine ⟨_, m, hb₀m, ⟨_, ⟨W₀, rfl⟩, ?_⟩, hP⟩
  refine ⟨_, 1, le_of_eq (mul_one _),
    ⟨_, ⟨hbf₀, rfl⟩, le_refl (⟨(W₀ : PSp Ω), hbf₀⟩ : BoundedFootprintSpace Bool)⟩, ?_⟩
  exact MeasureTheory.measure_mono_null hNsub hN₀

noncomputable
def product (μ₁ : PMF α) (μ₂ : PMF β) : PMF (α × β) :=
  let prf : HasSum (fun (a, b) => μ₁ a * μ₂ b) 1 := (by
      have h : ∑' (p : α × β), μ₁ p.1 * μ₂ p.2 = 1 := by
        simp_rw [ENNReal.tsum_prod', ENNReal.tsum_mul_left, ENNReal.tsum_mul_right,
          PMF.tsum_coe, mul_one]
      convert h ▸ ENNReal.summable.hasSum)
  ⟨fun ((a, b) : (α × β)) => μ₁ a * μ₂ b, prf⟩

infix:69 " ⊗ " => product

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
open MeasureTheory ProbabilityTheory in
/-- A pair with a product law on `P` splits `P` into two independent pieces, each carrying
one component's law: trim `P` to what each component sees.  A component is only almost
measurable, so each piece also sees a null set off which the pair agrees with a measurable
version; null, that set changes no measure and so keeps the pieces independent. -/
theorem PSpace.split_of_product_law {E₁ : Ω → α} {E₂ : Ω → β} {μ₁ : PMF α} {μ₂ : PMF β}
    (P : PSpace Ω) (ham : almostMeasurable (fun s ↦ (E₁ s, E₂ s)) (P : PSp Ω))
    (hlaw : @Measure.map Ω (α × β) P.ms ⊤ (fun s ↦ (E₁ s, E₂ s)) P.μ
      = (μ₁ ⊗ μ₂).toMeasureWithMs ⊤) :
    ∃ D₁ D₂ : PSpace Ω, D₁ ≤ P ∧ D₂ ≤ P ∧ PSp.mul (D₁ : PSp Ω) (D₂ : PSp Ω) ≤ (P : PSp Ω) ∧
      (almostMeasurable E₁ (D₁ : PSp Ω) ∧
        @Measure.map Ω α D₁.ms ⊤ E₁ D₁.μ = μ₁.toMeasureWithMs ⊤) ∧
      (almostMeasurable E₂ (D₂ : PSp Ω) ∧
        @Measure.map Ω β D₂.ms ⊤ E₂ D₂.μ = μ₂.toMeasureWithMs ⊤) := by
  have hP := P.isProbability
  letI : MeasurableSpace α := ⊤
  letI : MeasurableSpace β := ⊤
  letI : MeasurableSpace (α × β) := ⊤
  letI : MeasurableSpace Ω := P.ms
  -- a measurable version `g` of the pair, agreeing with it off a measurable null set `N`
  obtain ⟨g, hg, hae⟩ : AEMeasurable (fun s ↦ (E₁ s, E₂ s)) P.μ := ham
  obtain ⟨N, hNsub, hNmeas, hNnull⟩ := exists_measurable_superset_of_null (ae_iff.mp hae)
  let g₁ : Ω → α := fun s ↦ (g s).1
  let g₂ : Ω → β := fun s ↦ (g s).2
  have hg₁ : Measurable g₁ := measurable_from_top.comp hg
  have hg₂ : Measurable g₂ := measurable_from_top.comp hg
  -- the law of `g` on rectangles, and its marginals
  have hrect : ∀ A B, P.μ (g₁ ⁻¹' A ∩ g₂ ⁻¹' B)
      = μ₁.toMeasureWithMs ⊤ A * μ₂.toMeasureWithMs ⊤ B := by
    intro A B
    have h := congrArg (fun ν : Measure (α × β) ↦ ν (A ×ˢ B))
      ((Measure.map_congr hae).symm.trans hlaw)
    rw [Measure.map_apply hg MeasurableSpace.measurableSet_top] at h
    rw [show g₁ ⁻¹' A ∩ g₂ ⁻¹' B = g ⁻¹' (A ×ˢ B) by ext; simp [g₁, g₂], h]
    exact product_toMeasure_prod μ₁ μ₂ A B
  have hmarg₁ : ∀ A, P.μ (g₁ ⁻¹' A) = μ₁.toMeasureWithMs ⊤ A := by
    intro A
    have h := hrect A Set.univ
    rw [Set.preimage_univ, Set.inter_univ] at h
    rw [h]
    unfold PMF.toMeasureWithMs
    rw [measure_univ, mul_one]
  have hmarg₂ : ∀ B, P.μ (g₂ ⁻¹' B) = μ₂.toMeasureWithMs ⊤ B := by
    intro B
    have h := hrect Set.univ B
    rw [Set.preimage_univ, Set.univ_inter] at h
    rw [h]
    unfold PMF.toMeasureWithMs
    rw [measure_univ, one_mul]
  -- intersecting with `Set.univ` or with the conull `Nᶜ` changes no measure
  have hC : ∀ C ∈ ({Set.univ, Nᶜ} : Set (Set Ω)), ∀ X, P.μ (X ∩ C) = P.μ X := by
    rintro C (rfl | rfl) X
    · rw [Set.inter_univ]
    · exact measure_inter_conull (by rwa [compl_compl])
  have hCC : ∀ C ∈ ({Set.univ, Nᶜ} : Set (Set Ω)), ∀ C' ∈ ({Set.univ, Nᶜ} : Set (Set Ω)),
      C ∩ C' ∈ ({Set.univ, Nᶜ} : Set (Set Ω)) := by
    rintro C (rfl | rfl) C' (rfl | rfl) <;> simp
  have hCmeas : ∀ C ∈ ({Set.univ, Nᶜ} : Set (Set Ω)), MeasurableSet C := by
    rintro C (rfl | rfl)
    · exact MeasurableSet.univ
    · exact hNmeas.compl
  -- the π-systems of what each component sees, together with `N`
  let S₁ : Set (Set Ω) :=
    {t | ∃ A : Set α, ∃ C ∈ ({Set.univ, Nᶜ} : Set (Set Ω)), t = g₁ ⁻¹' A ∩ C}
  let S₂ : Set (Set Ω) :=
    {t | ∃ B : Set β, ∃ C ∈ ({Set.univ, Nᶜ} : Set (Set Ω)), t = g₂ ⁻¹' B ∩ C}
  have hS₁meas : ∀ t ∈ S₁, MeasurableSet t := by
    rintro _ ⟨A, C, hCm, rfl⟩
    exact (hg₁ MeasurableSpace.measurableSet_top).inter (hCmeas C hCm)
  have hS₂meas : ∀ t ∈ S₂, MeasurableSet t := by
    rintro _ ⟨B, C, hCm, rfl⟩
    exact (hg₂ MeasurableSpace.measurableSet_top).inter (hCmeas C hCm)
  have hS₁pi : IsPiSystem S₁ := by
    rintro _ ⟨A, C, hCm, rfl⟩ _ ⟨A', C', hCm', rfl⟩ _
    refine ⟨A ∩ A', C ∩ C', hCC C hCm C' hCm', ?_⟩
    ext x; simp only [Set.mem_inter_iff, Set.mem_preimage]; tauto
  have hS₂pi : IsPiSystem S₂ := by
    rintro _ ⟨B, C, hCm, rfl⟩ _ ⟨B', C', hCm', rfl⟩ _
    refine ⟨B ∩ B', C ∩ C', hCC C hCm C' hCm', ?_⟩
    ext x; simp only [Set.mem_inter_iff, Set.mem_preimage]; tauto
  have hind : Indep (MeasurableSpace.generateFrom S₁) (MeasurableSpace.generateFrom S₂) P.μ := by
    refine IndepSets.indep' hS₁meas hS₂meas hS₁pi hS₂pi ((IndepSets_iff _ _ _).2 ?_)
    rintro _ _ ⟨A, C, hCm, rfl⟩ ⟨B, C', hCm', rfl⟩
    rw [show g₁ ⁻¹' A ∩ C ∩ (g₂ ⁻¹' B ∩ C') = (g₁ ⁻¹' A ∩ g₂ ⁻¹' B) ∩ (C ∩ C') by
        ext x; simp only [Set.mem_inter_iff]; tauto,
      hC _ (hCC C hCm C' hCm'), hC C hCm, hC C' hCm', hrect, hmarg₁, hmarg₂]
  -- the two pieces, and their product
  set G₁ := MeasurableSpace.generateFrom S₁ with hG₁def
  set G₂ := MeasurableSpace.generateFrom S₂ with hG₂def
  have hG₁ : G₁ ≤ P.ms := MeasurableSpace.generateFrom_le hS₁meas
  have hG₂ : G₂ ≤ P.ms := MeasurableSpace.generateFrom_le hS₂meas
  let D₁ : PSpace Ω := @PSpace.trim Ω P G₁ hG₁
  let D₂ : PSpace Ω := @PSpace.trim Ω P G₂ hG₂
  let s : PSpace Ω := @PSpace.trim Ω P (G₁ ⊔ G₂) (sup_le hG₁ hG₂)
  have hD₁P : D₁ ≤ P := PSpace.trim_le hG₁
  have hD₂P : D₂ ≤ P := PSpace.trim_le hG₂
  have hsP : s ≤ P := PSpace.trim_le (sup_le hG₁ hG₂)
  have hprod : s =ᵢ D₁ ⊕ᵢ D₂ := by
    refine ⟨rfl, fun E hE F hF ↦ ?_⟩
    have hEF : @MeasurableSet Ω (G₁ ⊔ G₂) (E ∩ F) :=
      MeasurableSet.inter (le_sup_left (a := G₁) (b := G₂) E hE)
        (le_sup_right (a := G₁) (b := G₂) F hF)
    rw [MeasureOnSpace.le_preserves_measure hsP hEF, MeasureOnSpace.le_preserves_measure hD₁P hE,
      MeasureOnSpace.le_preserves_measure hD₂P hF]
    exact (Indep_iff _ _ _).1 hind E F hE hF
  -- each component is a.e. its measurable version on its piece
  have hg₁D : @Measurable Ω α G₁ ⊤ g₁ := fun A _ ↦
    MeasurableSpace.measurableSet_generateFrom ⟨A, Set.univ, by simp, (Set.inter_univ _).symm⟩
  have hg₂D : @Measurable Ω β G₂ ⊤ g₂ := fun B _ ↦
    MeasurableSpace.measurableSet_generateFrom ⟨B, Set.univ, by simp, (Set.inter_univ _).symm⟩
  have hN₁ : @MeasurableSet Ω G₁ N := by
    have h : @MeasurableSet Ω G₁ Nᶜ :=
      MeasurableSpace.measurableSet_generateFrom ⟨Set.univ, Nᶜ, by simp, by simp⟩
    simpa using h.compl
  have hN₂ : @MeasurableSet Ω G₂ N := by
    have h : @MeasurableSet Ω G₂ Nᶜ :=
      MeasurableSpace.measurableSet_generateFrom ⟨Set.univ, Nᶜ, by simp, by simp⟩
    simpa using h.compl
  have hae₁ : E₁ =ᵐ[D₁.μ] g₁ := by
    refine ae_iff.2 (measure_mono_null (fun s hs ↦ hNsub fun h ↦ hs (congrArg Prod.fst h)) ?_)
    rw [MeasureOnSpace.le_preserves_measure hD₁P hN₁]
    exact hNnull
  have hae₂ : E₂ =ᵐ[D₂.μ] g₂ := by
    refine ae_iff.2 (measure_mono_null (fun s hs ↦ hNsub fun h ↦ hs (congrArg Prod.snd h)) ?_)
    rw [MeasureOnSpace.le_preserves_measure hD₂P hN₂]
    exact hNnull
  refine ⟨D₁, D₂, hD₁P, hD₂P,
    (le_of_eq (mul_respect_independentProduct hprod)).trans (WithTop.coe_le_coe.2 hsP),
    ⟨⟨g₁, hg₁D, hae₁⟩, ?_⟩, ⟨⟨g₂, hg₂D, hae₂⟩, ?_⟩⟩
  · refine (Measure.map_congr hae₁).trans ?_
    ext A _
    exact (Measure.map_apply hg₁D MeasurableSpace.measurableSet_top).trans
      ((MeasureOnSpace.le_preserves_measure hD₁P (hg₁D MeasurableSpace.measurableSet_top)).trans
        (hmarg₁ A))
  · refine (Measure.map_congr hae₂).trans ?_
    ext B _
    exact (Measure.map_apply hg₂D MeasurableSpace.measurableSet_top).trans
      ((MeasureOnSpace.le_preserves_measure hD₂P (hg₂D MeasurableSpace.measurableSet_top)).trans
        (hmarg₂ B))

/--
TODO(Do we want?) - I _think_ I can make this work as it says in the paper,
i.e. `(E₁, E₂) ~ (μ₁ ⊗ μ₂)` instead of `(fun s => (E₁ s, E₂ s)) ~ (μ₁ ⊗ μ₂)`, but it would be
touching quite a common syntax pattern, so I think I'd rather not.

Thoughts?
-/
theorem PROD_SPLIT :
  (fun s => (E₁ s, E₂ s)) ~ (μ₁ ⊗ μ₂) ⊢ E₁ ~ μ₁ ∗ E₂ ~ μ₂ := by
  intro m hv h
  obtain ⟨q, ⟨P, hq⟩, hqm⟩ := h
  obtain ⟨d₁, d₂, hle, hown, hpure⟩ := (Quotient.exact hq).2 m hv hqm
  obtain ⟨r₁, ⟨hbfP, hr₁⟩, hd₁⟩ := hown
  obtain ⟨ham, hlaw⟩ := hpure
  have hd₁m : d₁ ≤ m := le_trans (le_mul_of_one_le PSp.one_le) hle
  have hPm : (⟨(P : PSp Ω), hbfP⟩ : BoundedFootprintSpace Bool) ≤ m :=
    le_trans ((Quotient.exact hr₁).2 d₁ (valid_mono hd₁m hv) hd₁) hd₁m
  obtain ⟨D₁, D₂, hD₁P, hD₂P, hmul, hlaw₁, hlaw₂⟩ := PSpace.split_of_product_law P ham hlaw
  have hbf₁ : HasBoundedFootprint (D₁ : PSp Ω) :=
    hasBoundedFootprint_mono (PSp.valid_def.mpr (Option.some_ne_none _))
      (WithTop.coe_le_coe.2 hD₁P) hbfP
  have hbf₂ : HasBoundedFootprint (D₂ : PSp Ω) :=
    hasBoundedFootprint_mono (PSp.valid_def.mpr (Option.some_ne_none _))
      (WithTop.coe_le_coe.2 hD₂P) hbfP
  refine ⟨⟨D₁, hbf₁⟩, ⟨D₂, hbf₂⟩, le_trans ?_ hPm, ⟨_, ⟨D₁, rfl⟩, ?_⟩, ⟨_, ⟨D₂, rfl⟩, ?_⟩⟩
  · exact hmul
  · exact ⟨_, 1, le_of_eq (mul_one _),
      ⟨_, ⟨hbf₁, rfl⟩, le_refl (⟨(D₁ : PSp Ω), hbf₁⟩ : BoundedFootprintSpace Bool)⟩, hlaw₁⟩
  · exact ⟨_, 1, le_of_eq (mul_one _),
      ⟨_, ⟨hbf₂, rfl⟩, le_refl (⟨(D₂ : PSp Ω), hbf₂⟩ : BoundedFootprintSpace Bool)⟩, hlaw₂⟩

end DistributionOwnershipRules

section JointConditioningRules



end JointConditioningRules

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
  intro r hv h
  obtain ⟨q, ⟨m, hq⟩, hqr⟩ := h
  obtain ⟨q', ⟨κ, hq'⟩, hq'r⟩ := (Quotient.exact hq).2 r hv hqr
  obtain ⟨b₁, b₂, hle, hown, hrest⟩ := (Quotient.exact hq').2 r hv hq'r
  obtain ⟨c₁, c₂, hle', hmix, hall⟩ := hrest
  obtain ⟨r₁, ⟨hbfm, hr₁⟩, hb₁⟩ := hown
  have hmb₁ := (Quotient.exact hr₁).2 b₁ (valid_mono (le_trans (le_mul_of_one_le PSp.one_le) hle) hv) hb₁
  obtain ⟨v, hvsupp⟩ := μ.support_nonempty
  -- `c₂` sits inside `b₂`, so `m`'s resource and `c₂` compose inside `r`
  have hc₂b₂ : c₂ ≤ b₂ := by
    refine le_trans ?_ hle'
    rw [mul_comm]
    exact le_mul_of_one_le PSp.one_le
  have hmc₂r : (⟨(m : PSp Ω), hbfm⟩ : BoundedFootprintSpace Bool) * c₂ ≤ r :=
    le_trans (mul_le_mul_right_le hmb₁ c₂) (le_trans (mul_le_mul_left_le hc₂b₂ b₁) hle)
  have hvmc₂ : ✓((⟨(m : PSp Ω), hbfm⟩ : BoundedFootprintSpace Bool) * c₂) := valid_mono hmc₂r hv
  have hb₂r : b₂ ≤ r := by
    refine le_trans ?_ hle
    rw [mul_comm]
    exact le_mul_of_one_le PSp.one_le
  have hvc₂ : ✓c₂ := valid_mono (le_trans hc₂b₂ hb₂r) hv
  -- the spaces behind `c₂` and behind `m * c₂`
  obtain ⟨c₂', hc₂'⟩ : ∃ c : PSpace Ω, c₂.val = (c : PSp Ω) :=
    Option.ne_none_iff_exists'.mp (PSp.valid_def.mp hvc₂)
  obtain ⟨s, hs⟩ : ∃ s : PSpace Ω, PSp.mul ((m : PSp Ω)) (c₂.val) = (s : PSp Ω) :=
    Option.ne_none_iff_exists'.mp (PSp.valid_def.mp hvmc₂)
  rw [hc₂'] at hs
  have hcomm : s =ᵢ c₂' ⊕ᵢ m := independentProduct_comm (PSp.mul_inversion hs)
  -- reweight that product along the `v`-fibre
  haveI hprob : MeasureTheory.IsProbabilityMeasure (κ.1 v) := κ.2.isProbabilityMeasure v
  obtain ⟨s', hs'⟩ :=
    PSpace.isIndependentProduct_reweight hcomm (κ.1 v) (kernel_fibre_ac κ hmix hvsupp)
  have hvm : ✓((m : PSp Ω)) := PSp.valid_def.mpr (Option.some_ne_none _)
  have hvk : ✓(((κ v : PSpace Ω)) : PSp Ω) := PSp.valid_def.mpr (Option.some_ne_none _)
  have hbfk : HasBoundedFootprint (((κ v : PSpace Ω)) : PSp Ω) :=
    hasBoundedFootprint_congr hvm hvk rfl hbfm
  have hvalid : ✓(c₂ * (⟨((κ v : PSpace Ω) : PSp Ω), hbfk⟩ : BoundedFootprintSpace Bool)) := by
    show PSp.mul c₂.val _ ≠ (⊤ : PSp Ω)
    rw [hc₂']
    exact PSp.mul_ne_top_of_exists ⟨s', hs'⟩
  exact hall _ ⟨⟨v, hvsupp⟩, rfl⟩ _ hvalid
    ⟨_, ⟨hbfk, rfl⟩,
      le_refl (⟨((κ v : PSpace Ω) : PSp Ω), hbfk⟩ : BoundedFootprintSpace Bool)⟩

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

/-- A sure fact is duplicable. -/
theorem liftPred_dup {p : Ω → Prop} : ⌈p⌉ ⊢ ⌈p⌉ ∗ ⌈p⌉ := by
  have h : (⌈p⌉ : FProp) = ⌈fun ω ↦ p ω ∧ p ω⌉ := by
    refine ownP_pure_congr (fun P ↦ ?_)
    have hs : {ρ | ¬ p ρ} = {ρ | ¬ (p ρ ∧ p ρ)} := by ext ρ; simp
    show P.μ {ρ | ¬ p ρ} = 0 ↔ P.μ {ρ | ¬ (p ρ ∧ p ρ)} = 0
    rw [hs]
  nth_rewrite 1 [h]
  exact liftPred_split

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
          simp [LiftAny.lift]
      · iexact HQ

open Interp in
/-- **Returning a value.**  `pure x` reads nothing, so `run` leaves the footprint untouched
(`run_pure_psp`) and every atom reports `x` (`result_run_pure`): the resource that already
satisfied `Q x` is handed straight back, and the postcondition is `valuePost` at a
constant. -/
lemma CWPPure {α : Type} {m : Type → Type} [Monad m] [Interp.LawfulBernoulliInterpretable m]
    [Inhabited α] {Q : RV α → FProp} {x : α} : Q (fun _ ↦ x) ⊢ wp (pure x : m α) Q := by
  sorry
  -- obtain ⟨U, hU⟩ : ∃ U : UpperSet (BoundedFootprintSpace Bool), Q x = fmk U :=
  --   ⟨(Q x).out, (Quotient.out_eq _).symm⟩
  -- rw [hU]
  -- intro a hva ha μ₀ c hvalid hle
  -- refine ⟨a, ?_, hva, ?_⟩
  -- · have hsp : ((run (pure x : m α) μ₀).1.toSpace : BoundedFootprintSpace Bool) = μ₀.toSpace :=
  --     Subtype.ext (run_pure_psp x μ₀ hvalid)
  --   rw [hsp]
  --   exact hle
  -- · rw [result_run_pure (m := m) x μ₀ hvalid]
  --   have h1 : own a ⊢ Q x := by rw [hU]; exact own_entails_of_mem ha
  --   exact entails_trans h1 (valuePost_const x Q)

lemma CWPSwap {α β : Type} {m : Type → Type} [Monad m] [Interp.BernoulliInterpretable m] [Inhabited α]
  {C : m α} {μ : PMF β} {Q : β → RV α → FProp} :
    iprop(𝒞⟨μ⟩ v; wp C (Q v)) ⊢ wp C (fun x ↦ 𝒞⟨μ⟩ v; Q v x) := by
  sorry

lemma CWPBind {α β : Type} {m : Type → Type} [Monad m] [Interp.BernoulliInterpretable m] [Inhabited α] [Inhabited β]
  {C : m α} {F : α → m β} {Q : β → FProp} :
    wp (C >>= F) Q ⊢ wp C (fun v ↦ wp (F v) Q) := by
  sorry

open unitInterval in
lemma CWPFlip {m : Type → Type} [Monad m] [Interp.BernoulliInterpretable m] {p : I} :
    ⌜0 < p ∧ p < 1⌝ ⊢ wp (Interp.flip p) (fun v ↦ v ~ sorry) := by
  sorry

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
