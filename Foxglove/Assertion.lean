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


/--
A tale of precedence!

- Need to overrule `⊢` and `⊣⊢` to state stuff like `𝒞⟨μ⟩ v; K₁ v ⊢ 𝒞⟨μ⟩ v; K₂ v`.
  These happen to be at 29.

- Ehh... `∗` wants at least 36; onwards and upwards.
  `P ∗ 𝒞⟨μ⟩ v; K v ⊢ 𝒞⟨μ⟩ v; (P ∗ (K v))`
-/
notation:36 "𝒞" "⟨" μ "⟩" v:arg ";" K:36 => jointConditioning μ (fun v => iprop(K))

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

class LiftUnary (β : Type) where
  lift : β → Ω → Prop

instance : LiftUnary (RV Prop) := ⟨fun a ω ↦ a ω⟩

instance : LiftUnary (RV Bool) := ⟨fun E ω ↦ E ω = true⟩

instance : LiftUnary Prop := ⟨fun p _ ↦ p⟩

instance : LiftUnary Bool := ⟨fun p _ ↦ p = true⟩

class LiftBinary (α β : Type) where
  lift : α → β → Ω → Prop

instance {α : Type} : LiftBinary (RV α) α where
  lift := fun l r ω ↦ l ω = r

instance {α : Type} : LiftBinary α (RV α) where
  lift := fun l r ω ↦ l = r ω

instance {α : Type} : LiftBinary (RV α) (RV α) where
  lift := fun l r ω ↦ l ω = r ω

syntax "lift(" term ", " term ")" : term

macro_rules
  | `(lift(¬$a, $ρ))     => `(¬lift($a, $ρ))
  | `(lift($a ∧ $b, $ρ)) => `(lift($a, $ρ) ∧ lift($b, $ρ))
  | `(lift($a ∨ $b, $ρ)) => `(lift($a, $ρ) ∨ lift($b, $ρ))
  | `(lift($a → $b, $ρ)) => `(lift($a, $ρ) → lift($b, $ρ))
  | `(lift($a = $b, $ρ)) => `(LiftBinary.lift $a $b $ρ)
  | `(lift(($x), $ρ))    => `(lift($x, $ρ))
  | `(lift($x, $ρ))      => `(LiftUnary.lift $x $ρ)

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

section Rules

variable {P Q : FProp} {α β : Type}
         {v₀ : α}
         {E E₁ : RV α} {E₂ : RV β}
         {μ μ' μ₁ : PMF α} {μ₂ : PMF β}
         {K : α → FProp}

section DistributionOwnershipRules

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

theorem SURE_MERGE {E₁ E₂ : RV Prop} : ⌈E₁⌉ ∗ ⌈E₂⌉ ⊣⊢ ⌈E₁ ∧ E₂⌉ :=
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
theorem SURE_AND_STAR {a : Ω → Prop} : ⌈a⌉ ∧ P ⊢ ⌈a⌉ ∗ P := by
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

variable {K K₁ K₂ : α → FProp}

lemma C_TRUE : ⊢ 𝒞⟨μ⟩ _v; ftrue := by
  unfold jointConditioning
  iexists (1 : PSpace Ω), unitKernel α
  isplitl []
  · exact ownP_one
  · isplitl []
    · ipureintro
      show PSpace.μ 1 = (μ.toMeasureWithMs ⊤).bind (fun _ ↦ PSpace.μ 1)
      simp [PMF.toMeasureWithMs]
    · iintro %v Hv
      exact entails_ftrue

set_option linter.style.haveILetI false in
open MeasureTheory in
/-- A PMF's measure lives on the PMF's support. -/
lemma ae_mem_support (μ : PMF α) : ∀ᵐ v ∂(μ.toMeasureWithMs ⊤), v ∈ μ.support := by
  letI : MeasurableSpace α := ⊤
  rw [ae_iff]
  exact (μ.toMeasure_apply_eq_zero_iff MeasurableSpace.measurableSet_top).2
    (Set.disjoint_left.2 fun _ hv hv' ↦ hv' hv)

open MeasureTheory in
/-- The tilt behind `PSpace.isIndependentProduct_reweight`, spelled out: on rectangles it
multiplies `c`'s measure with `ν`. -/
theorem reweight_rect {c m s : PSpace Ω} (hs : s =ᵢ c ⊕ᵢ m) (ν : Measure[m.ms] Ω)
    [IsProbabilityMeasure ν] (hac : ν ≪ m.μ) {E F : Set Ω} (hE : @MeasurableSet Ω c.ms E)
    (hF : @MeasurableSet Ω m.ms F) :
    (s.μ.withDensity (ν.rnDeriv m.μ)) (E ∩ F) = c.μ E * ν F := by
  have hmle : m.ms ≤ s.ms := (PSpace.le_of_isIndependentProduct_right hs).1
  have hcle : c.ms ≤ s.ms := (PSpace.le_of_isIndependentProduct_left hs).1
  have hmp := m.2
  rw [withDensity_apply _ ((hcle _ hE).inter (hmle _ hF)),
    PSpace.lintegral_rect hs (Measure.measurable_rnDeriv ν m.μ) hE hF, ← withDensity_apply _ hF,
    Measure.withDensity_rnDeriv_eq ν m.μ hac]

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

open MeasureTheory in
/-- A density measurable on a sub-space integrates the same on the sub-space and on the whole
space, over the sub-space's sets. -/
lemma PSpace.withDensity_le_apply {p q : PSpace Ω} (hpq : p ≤ q) {f : Ω → ENNReal}
    (hf : @Measurable Ω ENNReal p.ms _ f) {A : Set Ω} (hA : @MeasurableSet Ω p.ms A) :
    q.μ.withDensity f A = p.μ.withDensity f A := by
  have htrim : p.μ = q.μ.trim hpq.1 := by
    refine @Measure.ext Ω p.ms _ _ fun u hu ↦ ?_
    rw [trim_measurableSet_eq hpq.1 hu]
    exact MeasureOnSpace.le_preserves_measure hpq hu
  rw [withDensity_apply _ (hpq.1 _ hA), withDensity_apply _ hA, htrim,
    restrict_trim hpq.1 _ hA, lintegral_trim hpq.1 hf]

/-- A space is below another if its σ-algebra is coarser and the measures agree on it. -/
lemma PSpace.le_of_measure_eq {p q : PSpace Ω} (hms : p.ms ≤ q.ms)
    (hμ : ∀ u, @MeasurableSet Ω p.ms u → p.μ u = q.μ u) : p ≤ q := by
  refine ⟨hms, ?_⟩
  apply @MeasureTheory.Measure.ext Ω p.ms
  intro u hu
  exact (hμ u hu).trans (_root_.Measure.le_preserves_measure (h := hms) (μ := q.μ) (hu := hu)).symm

set_option linter.style.haveILetI false in
open MeasureTheory in
/-- **Tilting along a mixture.**  If a sub-space `m` of `S` is the `ν`-mixture of fibres
`lam v`, then `S` is the `ν`-mixture of its tilts by the fibres' densities over `m`: those
densities sum to one `m`-a.e., hence `S`-a.e. -/
theorem mixture_of_tilts {γ : Type} {S m : PSpace Ω} (hmS : m ≤ S) (ν : PMF γ)
    (lam : γ → Measure[m.ms] Ω) (hprob : ∀ v, IsProbabilityMeasure (lam v))
    (hmix : m.μ = (ν.toMeasureWithMs ⊤).bind lam) {A : Set Ω} (hA : @MeasurableSet Ω S.ms A) :
    S.μ A = ∫⁻ v, S.μ.withDensity ((lam v).rnDeriv m.μ) A ∂(ν.toMeasureWithMs ⊤) := by
  have hmp := m.2
  have hsupp := ae_mem_support ν
  letI : MeasurableSpace γ := ⊤
  have hf : ∀ v, @Measurable Ω ENNReal m.ms _ ((lam v).rnDeriv m.μ) :=
    fun v ↦ Measure.measurable_rnDeriv _ _
  have hfS : ∀ v, @Measurable Ω ENNReal S.ms _ ((lam v).rnDeriv m.μ) :=
    fun v ↦ (hf v).mono hmS.1 le_rfl
  -- the densities sum to one, `m`-a.e.
  let Fs : Ω → ENNReal := fun ρ ↦ ∫⁻ v, (lam v).rnDeriv m.μ ρ ∂(ν.toMeasureWithMs ⊤)
  have hFmeas : @Measurable Ω ENNReal m.ms _ Fs := by
    haveI := ν.support_countable.to_subtype
    have h : Fs = fun ρ ↦ ∑' v : ν.support, (lam v).rnDeriv m.μ ρ * ν v :=
      funext fun ρ ↦ pmf_lintegral_eq_tsum ν _
    rw [h]
    letI : MeasurableSpace Ω := m.ms
    exact Measurable.tsum fun v ↦ (hf v).mul_const _
  have hFone : Fs =ᵐ[m.μ] 1 := by
    letI : MeasurableSpace Ω := m.ms
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite hFmeas measurable_const
      fun F hF _ ↦ ?_
    calc ∫⁻ x in F, Fs x ∂m.μ
        = ∫⁻ v, ∫⁻ x in F, (lam v).rnDeriv m.μ x ∂m.μ ∂(ν.toMeasureWithMs ⊤) :=
          (lintegral_pmf_swap ν (m.μ.restrict F) _ fun v ↦ (hf v).aemeasurable).symm
      _ = ∫⁻ v, lam v F ∂(ν.toMeasureWithMs ⊤) := by
          refine lintegral_congr_ae ?_
          filter_upwards [hsupp] with v hv
          haveI := hprob v
          exact Measure.setLIntegral_rnDeriv (bind_fibre_ac hmix hv) F
      _ = m.μ F := by rw [hmix, Measure.bind_apply hF measurable_from_top.aemeasurable]
      _ = ∫⁻ x in F, (1 : Ω → ENNReal) x ∂m.μ := by simp
  have hFoneS : Fs =ᵐ[S.μ] 1 := PSpace.ae_eq_of_le hmS hFone
  calc S.μ A = ∫⁻ x in A, Fs x ∂S.μ := by
        rw [lintegral_congr_ae (ae_restrict_of_ae hFoneS)]
        simp
    _ = ∫⁻ v, ∫⁻ x in A, (lam v).rnDeriv m.μ x ∂S.μ ∂(ν.toMeasureWithMs ⊤) :=
        (lintegral_pmf_swap ν (S.μ.restrict A) _ fun v ↦ (hfS v).aemeasurable).symm
    _ = _ := lintegral_congr fun v ↦ (withDensity_apply _ hA).symm

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

/-- Conditioning with a `False` continuation is `False`: the support is nonempty, and the
fibre owned there would have to satisfy `False`. -/
lemma C_FALSE : 𝒞⟨μ⟩ _v; ffalse ⊢ ffalse := by
  intro r hv h
  have hown : own r ⊢ jointConditioning μ (fun _ ↦ ffalse) :=
    fun _ _ hry ↦ UpperSet.upper _ hry h
  obtain ⟨s, -, -, w, -, hX⟩ := cond_elim hv hown
  obtain ⟨v, hvsupp⟩ := μ.support_nonempty
  obtain ⟨X, hXval, hXK⟩ := hX v hvsupp
  have hXv : ✓X := by
    show X.val ≠ (⊤ : PSp Ω)
    rw [hXval]
    exact WithTop.coe_ne_top
  exact False.elim (hXK X hXv (le_refl X))

theorem C_CONS (h : ∀ v, K₁ v ⊢ K₂ v) : 𝒞⟨μ⟩ v; K₁ v ⊢ 𝒞⟨μ⟩ v; K₂ v := by
  unfold jointConditioning
  iintro ⟨%m, %κ, Hown, %hmix, Hall⟩
  iexists m, κ
  isplitl [Hown]
  · iexact Hown
  · isplitl []
    · ipureintro
      exact hmix
    · iintro %v Hv
      iapply (h v)
      iapply Hall
      iexact Hv

/-- A frame can be moved under conditioning: keep the space and the kernel, and hand the frame
to every fibre's continuation. -/
theorem C_FRAME : P ∗ 𝒞⟨μ⟩ v; K v ⊢ 𝒞⟨μ⟩ v; (P ∗ K v) := by
  unfold jointConditioning
  iintro ⟨HP, %m, %κ, Hown, %hmix, Hall⟩
  iexists m, κ
  isplitl [Hown]
  · iexact Hown
  · isplitl []
    · ipureintro
      exact hmix
    · iintro %v Hv
      isplitl [HP]
      · iexact HP
      · iapply Hall
        iexact Hv

set_option linter.style.haveILetI false in
open MeasureTheory in
/-- Conditioning on a Dirac distribution does nothing: its only fibre is the whole space, so
the continuation is handed back what was owned (`⊢`); conversely, condition the trivial space
(`⊣`). -/
theorem C_UNIT_L : 𝒞⟨δ v₀⟩ v; K v ⊣⊢ K v₀ := by
  constructor
  · unfold jointConditioning
    iintro ⟨%m, %κ, Hown, %hmix, Hall⟩
    -- the only fibre, at `v₀`, is `m` itself
    have hκ : (κ v₀ : PSpace Ω) = m := by
      apply Subtype.ext
      show (⟨m.ms, κ.1 v₀⟩ : MeasureOnSpace Ω) = m.1
      have h : κ.1 v₀ = m.μ := by
        letI : MeasurableSpace α := ⊤
        rw [hmix]
        simp only [PMF.toMeasureWithMs, PMF.toMeasure_pure]
        exact (Measure.dirac_bind (ProbabilityTheory.Kernel.measurable κ.1) v₀).symm
      rw [h]
    have hown : ownP m ⊢ ownP (κ v₀) := by rw [hκ]
    ispecialize Hall $$ %⟨v₀, (PMF.mem_support_pure_iff _ _).2 rfl⟩
    iapply Hall
    iapply hown
    iexact Hown
  · unfold jointConditioning
    iintro HK
    iexists (1 : PSpace Ω), unitKernel α
    isplitl []
    · exact ownP_one
    · isplitl []
      · ipureintro
        show PSpace.μ 1 = (((δ v₀) : PMF α).toMeasureWithMs ⊤).bind (fun _ ↦ PSpace.μ 1)
        simp [PMF.toMeasureWithMs]
      · iintro %v Hv
        -- the only value in the support is `v₀`
        obtain ⟨v, hv⟩ := v
        rw [PMF.mem_support_pure_iff] at hv
        subst hv
        iexact HK

set_option linter.style.haveILetI false in
open MeasureTheory in
/-- A space that is a `μ`-mixture of fibres, on each of which `E` surely is the fibre's
value, gives `E` the law `μ`.  A measurable version of `E` is read off a conull cover of each
fibre's event `E = v`; the covers are disjoint, and there are countably many of them. -/
theorem law_of_fibres {E : RV α} {μ : PMF α} (s : PSpace Ω) (w : α → Measure[s.ms] Ω)
    (hmix : ∀ S, @MeasurableSet Ω s.ms S → s.μ S = ∫⁻ v, w v S ∂(μ.toMeasureWithMs ⊤))
    (hprob : ∀ v ∈ μ.support, w v Set.univ = 1)
    (hsure : ∀ v ∈ μ.support, w v {ρ | ¬ E ρ = v} = 0) :
    almostMeasurable E (s : PSp Ω) ∧
      @Measure.map Ω α s.ms ⊤ E s.μ = μ.toMeasureWithMs ⊤ := by
  classical
  have hsupp := ae_mem_support μ
  letI : MeasurableSpace α := ⊤
  letI : MeasurableSpace Ω := s.ms
  -- a measurable null cover `N v` of each fibre's exceptional set
  choose! N hNsub hNmeas hNnull using fun v (hv : v ∈ μ.support) ↦
    exists_measurable_superset_of_null (hsure v hv)
  have hEv : ∀ v ∈ μ.support, ∀ ρ, ρ ∉ N v → E ρ = v := fun v hv ρ hρ ↦
    by_contra fun h ↦ hρ (hNsub v hv h)
  set U := ⋃ v ∈ μ.support, (N v)ᶜ with hU
  have hUmeas : MeasurableSet U :=
    MeasurableSet.biUnion μ.support_countable fun v hv ↦ (hNmeas v hv).compl
  have hmemU : ∀ v ∈ μ.support, ∀ ρ, ρ ∉ N v → ρ ∈ U := fun v hv ρ hρ ↦
    Set.mem_biUnion hv hρ
  obtain ⟨v₁, -⟩ := μ.support_nonempty
  -- the measurable version: `E` on the covers, anything off them
  let g : Ω → α := fun ρ ↦ if ρ ∈ U then E ρ else v₁
  have hgv : ∀ v ∈ μ.support, ∀ ρ, ρ ∉ N v → g ρ = v := fun v hv ρ hρ ↦ by
    simp only [g, hmemU v hv ρ hρ, ↓reduceIte]
    exact hEv v hv ρ hρ
  have hpre : ∀ B : Set α, g ⁻¹' B
      = (⋃ v ∈ {v | v ∈ μ.support ∧ v ∈ B}, (N v)ᶜ) ∪ (Uᶜ ∩ {_ρ | v₁ ∈ B}) := by
    intro B
    ext ρ
    by_cases hρ : ρ ∈ U
    · obtain ⟨v, hv, hρv⟩ : ∃ v ∈ μ.support, ρ ∉ N v := by simpa [hU] using hρ
      simp only [Set.mem_preimage, hgv v hv ρ hρv, Set.mem_union, Set.mem_iUnion,
        Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_ofPred_eq, hρ, not_true_eq_false,
        false_and, or_false, exists_prop]
      constructor
      · exact fun hvB ↦ ⟨v, ⟨hv, hvB⟩, hρv⟩
      · rintro ⟨v', ⟨hv', hv'B⟩, hρv'⟩
        rwa [← hgv v hv ρ hρv, hgv v' hv' ρ hρv']
    · simp only [Set.mem_preimage, g, Set.mem_union, Set.mem_iUnion,
        Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_ofPred_eq, hρ, not_false_eq_true,
        true_and, exists_prop]
      constructor
      · exact Or.inr
      · rintro (⟨v', ⟨hv', -⟩, hρv'⟩ | h)
        · exact absurd (hmemU v' hv' ρ hρv') hρ
        · exact h
  have hg : Measurable g := by
    intro B _
    rw [hpre B]
    refine MeasurableSet.union ?_ (hUmeas.compl.inter (MeasurableSet.const _))
    exact MeasurableSet.biUnion (μ.support_countable.mono fun v hv ↦ hv.1)
      fun v hv ↦ (hNmeas v hv.1).compl
  -- off the covers there is no mass
  have hUc : s.μ Uᶜ = 0 := by
    rw [hmix _ hUmeas.compl]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hsupp] with v hv
    exact measure_mono_null (fun ρ hρ ↦ by_contra fun h ↦ hρ (hmemU v hv ρ h)) (hNnull v hv)
  have hae : E =ᵐ[s.μ] g := by
    refine ae_iff.2 (measure_mono_null
      (show {ρ | ¬ E ρ = g ρ} ⊆ Uᶜ from fun ρ hρ hρU ↦ hρ ?_) hUc)
    simp only [g, hρU, ↓reduceIte]
  have haem : AEMeasurable E s.μ := ⟨g, hg, hae⟩
  refine ⟨haem, ?_⟩
  -- each fibre puts all its mass on `g ⁻¹' B` or none
  ext B _
  rw [Measure.map_apply_of_aemeasurable haem MeasurableSpace.measurableSet_top,
    measure_congr (hae.preimage B), hmix _ (hg MeasurableSpace.measurableSet_top)]
  have hind : ∀ᵐ v ∂(μ.toMeasureWithMs ⊤), w v (g ⁻¹' B) = B.indicator 1 v := by
    filter_upwards [hsupp] with v hv
    by_cases hvB : v ∈ B
    · rw [Set.indicator_of_mem hvB, Pi.one_apply]
      have hNfin : w v (N v) ≠ (⊤ : ENNReal) := by rw [hNnull v hv]; exact ENNReal.zero_ne_top
      have hcov : w v (N v)ᶜ = 1 := by
        rw [measure_compl (hNmeas v hv) hNfin, hprob v hv, hNnull v hv, tsub_zero]
      refine le_antisymm ((measure_mono (Set.subset_univ _)).trans (hprob v hv).le) ?_
      rw [← hcov]
      exact measure_mono fun ρ hρ ↦ show g ρ ∈ B by rw [hgv v hv ρ hρ]; exact hvB
    · rw [Set.indicator_of_notMem hvB]
      refine measure_mono_null (fun ρ hρ ↦ by_contra fun hρN ↦ hvB ?_) (hNnull v hv)
      have hρB : g ρ ∈ B := hρ
      rwa [hgv v hv ρ hρN] at hρB
  rw [lintegral_congr_ae hind, lintegral_indicator_one MeasurableSpace.measurableSet_top]

set_option linter.style.haveILetI false in
open MeasureTheory ProbabilityTheory in
/-- A random variable with law `μ` on `P` conditions `P`: sending `v` to `P` conditioned on
`E = v` (read on a measurable version of `E`) is a kernel mixing back to `P`, and on its fibre
at `v` the variable surely is `v`. -/
theorem condKernel_of_law {E : RV α} {μ : PMF α} (P : PSpace Ω)
    (ham : almostMeasurable E (P : PSp Ω))
    (hlaw : @Measure.map Ω α P.ms ⊤ E P.μ = μ.toMeasureWithMs ⊤) :
    ∃ κ : TrivialMarkovKernel α P, P.μ = (μ.toMeasureWithMs ⊤).bind κ ∧
      ∀ v ∈ μ.support, (κ v : PSpace Ω).μ {ρ | ¬ E ρ = v} = 0 := by
  classical
  have hP := P.isProbability
  letI : MeasurableSpace α := ⊤
  letI : MeasurableSpace Ω := P.ms
  obtain ⟨g, hg, hae⟩ : AEMeasurable E P.μ := ham
  have hlaw' : Measure.map g P.μ = μ.toMeasure := (Measure.map_congr hae).symm.trans hlaw
  have hG : ∀ v, MeasurableSet (g ⁻¹' {v}) := fun _ ↦ hg MeasurableSpace.measurableSet_top
  have hGμ : ∀ v, P.μ (g ⁻¹' {v}) = μ v := fun v ↦ by
    rw [← Measure.map_apply hg MeasurableSpace.measurableSet_top, hlaw',
      PMF.toMeasure_apply_singleton _ _ MeasurableSpace.measurableSet_top]
  have hG0 : ∀ v ∈ μ.support, P.μ (g ⁻¹' {v}) ≠ 0 := fun v hv ↦ by
    rw [hGμ]; exact (PMF.mem_support_iff _ _).1 hv
  -- the fibres: `P` conditioned on `g = v`
  let f : α → Measure Ω := fun v ↦ if v ∈ μ.support then P.μ[|g ⁻¹' {v}] else P.μ
  have hfprob : ∀ v, IsProbabilityMeasure (f v) := by
    intro v
    by_cases hv : v ∈ μ.support
    · simp only [f, hv, ↓reduceIte]
      exact cond_isProbabilityMeasure (hG0 v hv)
    · simp only [f, hv, ↓reduceIte]
      exact hP
  let κ : TrivialMarkovKernel α P := ⟨⟨f, measurable_from_top⟩, ⟨hfprob⟩⟩
  refine ⟨κ, ?_, fun v hv ↦ ?_⟩
  · -- `P` is the mixture of its fibres: sum over the countable support
    ext F hF
    rw [Measure.bind_apply hF (Kernel.measurable κ.1).aemeasurable]
    show P.μ F = ∫⁻ v, f v F ∂μ.toMeasure
    have hcon : P.μ (g ⁻¹' μ.support)ᶜ = 0 := by
      rw [← Set.preimage_compl, ← Measure.map_apply hg MeasurableSpace.measurableSet_top, hlaw',
        μ.toMeasure_apply_eq_zero_iff MeasurableSpace.measurableSet_top]
      exact disjoint_compl_right
    have hterm : ∀ v : μ.support,
        f v F * μ.toMeasure {(v : α)} = (P.μ.restrict F) (g ⁻¹' {(v : α)}) := by
      rintro ⟨v, hv⟩
      simp only [f, hv, ↓reduceIte]
      rw [cond_apply (hG v), PMF.toMeasure_apply_singleton _ _ MeasurableSpace.measurableSet_top,
        ← hGμ, Measure.restrict_apply (hG v), Set.inter_comm, mul_comm, ← mul_assoc,
        ENNReal.mul_inv_cancel (hG0 v hv) (measure_ne_top _ _), one_mul]
    rw [← μ.restrict_toMeasure_support, lintegral_countable _ μ.support_countable,
      tsum_congr hterm,
      tsum_measure_preimage_singleton μ.support_countable (fun v _ ↦ hG v),
      Measure.restrict_apply (hg MeasurableSpace.measurableSet_top), Set.inter_comm,
      measure_inter_conull hcon]
  · -- on the fibre at `v`, `E` is `v` up to the null set where `E` and `g` differ
    show f v {ρ | ¬ E ρ = v} = 0
    simp only [f, hv, ↓reduceIte]
    obtain ⟨N, hNsub, -, hNnull⟩ := exists_measurable_superset_of_null (ae_iff.1 hae)
    refine measure_mono_null (t := (g ⁻¹' {v})ᶜ ∪ N) (fun ρ hρ ↦ ?_)
      (measure_union_null ?_ (cond_absolutelyContinuous hNnull))
    · by_cases hgv : g ρ = v
      · exact Or.inr (hNsub fun h ↦ hρ (h.trans hgv))
      · exact Or.inl hgv
    · rw [cond_apply (hG v), Set.inter_compl_self, measure_empty, mul_zero]

set_option linter.style.haveILetI false in
open MeasureTheory in
/-- A random variable with law `μ` is the conditioning on `μ` of surely being each value:
condition on `E = v` (`⊢`); conversely, unpack the conditioning (`cond_elim`): `E` is surely
`v` on the fibre at `v`, so the mixture of the fibres gives `E` the law `μ` (`⊣`). -/
theorem C_UNIT_R : E ~ μ ⊣⊢ 𝒞⟨μ⟩ v; ⌈E = v⌉ := by
  constructor
  · unfold hasDistribution jointConditioning
    iintro ⟨%P, HP, %hpure⟩
    obtain ⟨ham, hlaw⟩ := hpure
    obtain ⟨κ, hmix, hsure⟩ := condKernel_of_law P ham hlaw
    iexists P, κ
    isplitl [HP]
    · iexact HP
    · isplitl []
      · ipureintro
        exact hmix
      · iintro %v Hv
        dsimp only [LiftPred.lift]
        iexists (κ v)
        isplitl [Hv]
        · iexact Hv
        · ipureintro
          exact hsure v v.2
  · intro r hv h
    have hown : own r ⊢ jointConditioning μ (fun v ↦ ⌈E = v⌉) :=
      fun _ _ hry ↦ UpperSet.upper _ hry h
    obtain ⟨s, hbfs, hsr, w, hsmix, hX⟩ := cond_elim hv hown
    -- on each fibre the continuation made `E` surely its value
    have hsure : ∀ v ∈ μ.support, (w v).1 {ρ | ¬ E ρ = v} = 0 := by
      intro v hv'
      obtain ⟨X, hXval, hXK⟩ := hX v hv'
      have hXv : ✓X := by
        show X.val ≠ (⊤ : PSp Ω)
        rw [hXval]
        exact WithTop.coe_ne_top
      obtain ⟨q₀, ⟨P', hq₀⟩, hq₀m⟩ := hXK X hXv (le_refl X)
      obtain ⟨e₁, _, hlee, hown', hpure'⟩ := (Quotient.exact hq₀).2 _ hXv hq₀m
      obtain ⟨r', ⟨hbf', hr'⟩, he₁⟩ := hown'
      have he₁m := le_trans (le_mul_of_one_le PSp.one_le) hlee
      have hP' := (Quotient.exact hr').2 e₁ (valid_mono he₁m hXv) he₁
      have hP'S : P' ≤ (show PSpace Ω from ⟨⟨s.ms, (w v).1⟩, (w v).2⟩) := by
        have h : (P' : PSp Ω) ≤ X.val := le_trans hP' he₁m
        rw [hXval] at h
        exact WithTop.coe_le_coe.1 h
      exact PSpace.null_of_le hP'S hpure'
    -- so the mixture of the fibres gives `E` the law `μ`
    have hmix : ∀ S, @MeasurableSet Ω s.ms S →
        s.μ S = ∫⁻ v, (w v).1 S ∂(μ.toMeasureWithMs ⊤) := by
      letI : MeasurableSpace α := ⊤
      intro S hS
      rw [hsmix, Measure.bind_apply hS measurable_from_top.aemeasurable]
    obtain ⟨ham, hlaw⟩ := law_of_fibres s (fun v ↦ (w v).1) hmix
      (fun v _ ↦ (w v).2.measure_univ) hsure
    exact ⟨_, ⟨s, rfl⟩, ⟨(s : PSp Ω), hbfs⟩, 1, by rw [mul_one]; exact hsr,
      ⟨_, ⟨hbfs, rfl⟩, le_refl (⟨(s : PSp Ω), hbfs⟩ : BoundedFootprintSpace Bool)⟩,
      ⟨ham, hlaw⟩⟩

variable {μ₀ : PMF (α × β)} {κ : α → PMF β} {K : (α × β) → FProp} in
set_option linter.style.haveILetI false in
open MeasureTheory in
/-- Conditioning twice is conditioning once on the joint law.  Unpack both conditionings
(`cond_elim`); the outer space `s` is the mixture of fibres `S v`, and each `S v` contains an
inner space `s v` mixing fibres `T v w`.  Extend each `T v w` to `s`'s σ-algebra by tilting
`S v` with the density of `T v w` over `s v`: by `mixture_of_tilts` these extensions mix back
to `S v`, so to `s`, and each still contains `T v w`, which satisfies the continuation. -/
theorem C_ASSOC (h : μ₀ = (PMF.bind μ fun v ↦ PMF.bind (κ v) fun w ↦ PMF.pure (v, w))) :
  𝒞⟨μ⟩ v; 𝒞⟨κ v⟩ w; K (v, w) ⊢ 𝒞⟨μ₀⟩ (v, w); K (v, w) := by
  classical
  subst h
  obtain ⟨Kr, rfl⟩ : ∃ Kr : α × β → UpperSet (BoundedFootprintSpace Bool),
      K = fun x ↦ fmk (Kr x) :=
    ⟨fun x ↦ (K x).out, funext fun x ↦ (Quotient.out_eq _).symm⟩
  intro r hv hr
  have hown : own r ⊢ jointConditioning μ
      (fun v ↦ jointConditioning (κ v) (fun w ↦ fmk (Kr (v, w)))) :=
    fun _ _ hry ↦ UpperSet.upper _ hry hr
  -- the outer conditioning
  obtain ⟨s, hbfs, hsr, w, hsmix, hX⟩ := cond_elim hv hown
  have hsp := s.2
  -- the inner conditionings, one per value of the outer one
  have hinner : ∀ v ∈ μ.support, ∃ (sv : PSpace Ω)
      (wv : β → {p : Measure[sv.ms] Ω // IsProbabilityMeasure p}),
      sv ≤ (⟨⟨s.ms, (w v).1⟩, (w v).2⟩ : PSpace Ω) ∧
      sv.μ = ((κ v).toMeasureWithMs ⊤).bind (fun b ↦ (wv b).1) ∧
      ∀ b ∈ (κ v).support, ∃ Y : BoundedFootprintSpace Bool,
        Y.val = ((show PSpace Ω from ⟨⟨sv.ms, (wv b).1⟩, (wv b).2⟩) : PSp Ω) ∧
          (own Y ⊢ fmk (Kr (v, b))) := by
    intro v hv'
    obtain ⟨X, hXval, hXK⟩ := hX v hv'
    have hXv : ✓X := by
      show X.val ≠ (⊤ : PSp Ω)
      rw [hXval]
      exact WithTop.coe_ne_top
    obtain ⟨sv, hbfsv, hsvX, wv, hsvmix, hY⟩ := cond_elim hXv hXK
    refine ⟨sv, wv, ?_, hsvmix, hY⟩
    have h : (sv : PSp Ω) ≤ X.val := hsvX
    rw [hXval] at h
    exact WithTop.coe_le_coe.1 h
  choose sv wv hsvle hsvmix hY using hinner
  -- the joint fibres: `S v` tilted by the density of `T v b` over `s v`
  let Λμ : α × β → Measure[s.ms] Ω := fun x ↦
    if hx : x.1 ∈ μ.support ∧ x.2 ∈ (κ x.1).support then
      (w x.1).1.withDensity (((wv x.1 hx.1 x.2).1).rnDeriv (sv x.1 hx.1).μ)
    else s.μ
  -- on the inner space's sets, the joint fibre is `T v b`
  have hΛT : ∀ v (hv : v ∈ μ.support), ∀ b ∈ (κ v).support, ∀ A,
      @MeasurableSet Ω (sv v hv).ms A → Λμ (v, b) A = (wv v hv b).1 A := by
    intro v hv b hb A hA
    haveI := (wv v hv b).2
    have hsvp := (sv v hv).2
    have hac : (wv v hv b).1 ≪ (sv v hv).μ := bind_fibre_ac (hsvmix v hv) hb
    simp only [Λμ, show (v, b).1 ∈ μ.support ∧ (v, b).2 ∈ (κ (v, b).1).support from ⟨hv, hb⟩]
    refine (PSpace.withDensity_le_apply (hsvle v hv)
      (@Measure.measurable_rnDeriv Ω (sv v hv).ms (wv v hv b).1 (sv v hv).μ) hA).trans ?_
    rw [Measure.withDensity_rnDeriv_eq _ _ hac]
  have hΛprob : ∀ x, IsProbabilityMeasure (Λμ x) := by
    rintro ⟨v, b⟩
    by_cases hx : v ∈ μ.support ∧ b ∈ (κ v).support
    · constructor
      rw [hΛT v hx.1 b hx.2 _ MeasurableSet.univ]
      exact (wv v hx.1 b).2.measure_univ
    · simp only [Λμ, show ¬ ((v, b).1 ∈ μ.support ∧ (v, b).2 ∈ (κ (v, b).1).support) from hx,
        ↓reduceDIte]
      exact hsp
  letI : MeasurableSpace (α × β) := ⊤
  obtain ⟨Λk, hΛk⟩ : ∃ Λk : ProbabilityTheory.TrivialMarkovKernel (α × β) s, ∀ x, Λk.1 x = Λμ x := by
    letI : MeasurableSpace Ω := s.ms
    exact ⟨⟨⟨Λμ, measurable_from_top⟩, ⟨hΛprob⟩⟩, fun _ ↦ rfl⟩
  -- `s` is the joint mixture of the joint fibres
  have hΛmix : s.μ = (((μ.bind fun v ↦ (κ v).bind fun w ↦ PMF.pure (v, w)).toMeasureWithMs ⊤).bind
      Λk.1) := by
    refine @Measure.ext Ω s.ms _ _ fun A hA ↦ ?_
    rw [Measure.bind_apply hA (ProbabilityTheory.Kernel.measurable Λk.1).aemeasurable,
      lintegral_pmf_bind_pair, hsmix]
    letI : MeasurableSpace α := ⊤
    rw [Measure.bind_apply hA measurable_from_top.aemeasurable]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_mem_support μ] with v hv
    refine (mixture_of_tilts (hsvle v hv) (κ v) (fun b ↦ (wv v hv b).1) (fun b ↦ (wv v hv b).2)
      (hsvmix v hv) hA).trans ?_
    refine lintegral_congr_ae ?_
    filter_upwards [ae_mem_support (κ v)] with b hb
    rw [hΛk]
    simp only [Λμ, show (v, b).1 ∈ μ.support ∧ (v, b).2 ∈ (κ (v, b).1).support from ⟨hv, hb⟩]
    rfl
  -- the joint conditioning, framed by nothing: each joint fibre contains `T v b`
  refine ⟨_, ⟨s, rfl⟩, _, ⟨Λk, rfl⟩, ⟨(s : PSp Ω), hbfs⟩, 1, by rw [mul_one]; exact hsr,
    ⟨_, ⟨hbfs, rfl⟩, le_refl (⟨(s : PSp Ω), hbfs⟩ : BoundedFootprintSpace Bool)⟩,
    1, 1, le_of_eq (mul_one 1), hΛmix, ?_⟩
  intro p ⟨x, hxp⟩
  obtain ⟨⟨a, b⟩, hab⟩ := x
  obtain ⟨ha, hb⟩ : a ∈ μ.support ∧ b ∈ (κ a).support := by
    rw [PMF.mem_support_bind_iff] at hab
    obtain ⟨v, hv, hvb⟩ := hab
    rw [PMF.mem_support_bind_iff] at hvb
    obtain ⟨b', hb', hpb⟩ := hvb
    rw [PMF.mem_support_pure_iff] at hpb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpb
    exact ⟨hv, hb'⟩
  refine (Quotient.exact hxp).1 1 valid_one fun y _ hy ↦ ?_
  rw [one_mul]
  -- `y` owns the joint fibre, hence `T a b`, which satisfies the continuation
  obtain ⟨q, ⟨hbfΛ, hq⟩, hyq⟩ := hy
  have hvy : ✓y := valid_mono (le_of_eq (one_mul y).symm) ‹_›
  have hΛy := (Quotient.exact hq).2 y hvy hyq
  obtain ⟨Y, hYval, hYK⟩ := hY a ha b hb
  have hTΛ : (⟨⟨(sv a ha).ms, (wv a ha b).1⟩, (wv a ha b).2⟩ : PSpace Ω)
      ≤ (Λk (a, b) : PSpace Ω) :=
    PSpace.le_of_measure_eq (le_trans (hsvle a ha).1 le_rfl)
      fun u hu ↦ by
        show _ = Λk.1 (a, b) u
        rw [hΛk]
        exact (hΛT a ha b hb u hu).symm
  have hYy : Y ≤ y := by
    refine le_trans ?_ hΛy
    show Y.val ≤ ((Λk (a, b) : PSpace Ω) : PSp Ω)
    rw [hYval]
    exact WithTop.coe_le_coe.2 hTΛ
  exact hYK y hvy hYy

set_option linter.style.haveILetI false in
open MeasureTheory in
/-- Conditioning on a `bind` can be split into two conditionings.  Unpack the joint one
(`cond_elim`): its space `s` mixes fibres `T w` along `bind μ κ`.  Keep `s`, and take the outer
fibre at `v` to be the `κ v`-mixture of the `T w`.  These fibres mix back to `s`, and each of them
is conditioned by `κ v` into the original `T w`. -/
theorem C_UNASSOC {K : β → FProp} :
  𝒞⟨PMF.bind μ κ⟩ w; K w ⊢ 𝒞⟨μ⟩ v; 𝒞⟨κ v⟩ w; K w := by
  intro r hv hr
  have hown : own r ⊢ jointConditioning (μ.bind κ) (fun w ↦ K w) :=
    fun _ _ hry ↦ UpperSet.upper _ hry hr
  obtain ⟨s, hbfs, hsr, w, hsmix, hX⟩ := cond_elim hv hown
  have hsp := s.2
  -- the outer fibres: the `κ v`-mixtures of the joint fibres
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ProbabilityTheory.TrivialMarkovKernel α s,
      ∀ v, ℓ.1 v = ((κ v).toMeasureWithMs ⊤).bind fun b ↦ (w b).1 := by
    letI : MeasurableSpace Ω := s.ms
    letI : MeasurableSpace α := ⊤
    letI : MeasurableSpace β := ⊤
    refine ⟨⟨⟨fun v ↦ ((κ v).toMeasureWithMs ⊤).bind fun b ↦ (w b).1, measurable_from_top⟩,
      ⟨fun v ↦ ⟨?_⟩⟩⟩, fun _ ↦ rfl⟩
    show (((κ v).toMeasureWithMs ⊤).bind fun b ↦ (w b).1) Set.univ = 1
    rw [Measure.bind_apply MeasurableSet.univ measurable_from_top.aemeasurable,
      lintegral_congr fun b ↦ (w b).2.measure_univ, lintegral_one]
    show (κ v).toMeasure Set.univ = 1
    exact measure_univ
  -- they mix back to `s`
  have hℓmix : s.μ = (μ.toMeasureWithMs ⊤).bind ℓ.1 := by
    refine @Measure.ext Ω s.ms _ _ fun A hA ↦ ?_
    letI : MeasurableSpace α := ⊤
    letI : MeasurableSpace β := ⊤
    rw [hsmix, Measure.bind_apply hA measurable_from_top.aemeasurable, toMeasure_bind_eq,
      Measure.lintegral_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable,
      Measure.bind_apply hA (ProbabilityTheory.Kernel.measurable ℓ.1).aemeasurable]
    refine lintegral_congr fun v ↦ ?_
    rw [hℓ, Measure.bind_apply hA measurable_from_top.aemeasurable]
  -- the inner kernels hand back the joint fibres
  let ι : ∀ v, ProbabilityTheory.TrivialMarkovKernel β (ℓ v) := fun _ ↦
    letI : MeasurableSpace Ω := s.ms
    letI : MeasurableSpace β := ⊤
    ⟨⟨fun b ↦ (w b).1, measurable_from_top⟩, ⟨fun b ↦ (w b).2⟩⟩
  have hKb : ∀ v (b : β), b ∈ (μ.bind κ).support → ownP (ι v b) ⊢ K b := by
    intro v b hb
    obtain ⟨X, hXval, hXK⟩ := hX b hb
    unfold ownP
    refine Iris.BI.exists_elim fun hbf ↦ ?_
    rw [show (⟨((ι v b : PSpace Ω) : PSp Ω), hbf⟩ : BoundedFootprintSpace Bool) = X from
      Subtype.ext (by rw [hXval]; rfl)]
    exact hXK
  have key : ownP s ⊢ 𝒞⟨μ⟩ v; 𝒞⟨κ v⟩ w; K w := by
    unfold jointConditioning
    iintro Hown
    iexists s, ℓ
    isplitl [Hown]
    · iexact Hown
    · isplitl []
      · ipureintro
        exact hℓmix
      · iintro %v Hv
        iexists (ℓ v : PSpace Ω), ι v
        isplitl [Hv]
        · iexact Hv
        · isplitl []
          · ipureintro
            show ℓ.1 v = ((κ v).toMeasureWithMs ⊤).bind fun b ↦ (w b).1
            exact hℓ v
          · iintro %b Hb
            iapply (hKb v b ((PMF.mem_support_bind_iff _ _ _).2 ⟨v, v.2, b.2⟩))
            iexact Hb
  exact key r hv ⟨_, ⟨hbfs, rfl⟩, hsr⟩

/-
Does not apply in our unary logic. (Bluebell carries a side-condition here.)

theorem C_AND : ¬ ∀ {K₁ K₂ : α → FProp}, 𝒞⟨μ⟩ v; K₁ v ∧ 𝒞⟨μ⟩ v; K₂ v ⊢ 𝒞⟨μ⟩ v; (K₁ v ∧ K₂ v) :=
  sorry
-/

/--
Note: In Bluebell, we have `𝜇 : D(Σ𝐴)` side condition.
Here, we take a `μ` that's a `PMF`, not a measure. As such, every subset is measurable, and we are,
as some would say, Gucci.
-/
theorem C_SKOLEM {α X : Type} {μ : PMF α} {Q : (α × X) → FProp} :
  𝒞⟨μ⟩ v; (∃ x : X, Q (v, x)) ⊢ ∃ (f : α → X), 𝒞⟨μ⟩ v; Q (v, f v) := by
  classical
  obtain ⟨Qr, rfl⟩ : ∃ Qr : α × X → UpperSet (BoundedFootprintSpace Bool),
      Q = fun x ↦ fmk (Qr x) :=
    ⟨fun x ↦ (Q x).out, funext fun x ↦ (Quotient.out_eq _).symm⟩
  intro r hv hr
  have hown : own r ⊢ jointConditioning μ (fun v ↦ iprop(∃ x : X, fmk (Qr (v, x)))) :=
    fun _ _ hry ↦ UpperSet.upper _ hry hr
  obtain ⟨s, hbfs, hsr, w, hsmix, hX⟩ := cond_elim hv hown
  -- a witness per value in the support, read off the fibre itself
  have hwit : ∀ v ∈ μ.support, ∃ x : X, ∀ p : PSpace Ω,
      (p : PSp Ω) = ((show PSpace Ω from ⟨⟨s.ms, (w v).1⟩, (w v).2⟩) : PSp Ω) →
        ownP p ⊢ fmk (Qr (v, x)) := by
    intro v hv'
    obtain ⟨Y, hYval, hYK⟩ := hX v hv'
    have hYv : ✓Y := by
      show Y.val ≠ (⊤ : PSp Ω)
      rw [hYval]
      exact WithTop.coe_ne_top
    obtain ⟨q, ⟨x, hqx⟩, hYq⟩ := hYK Y hYv (le_refl Y)
    have hmem := (Quotient.exact hqx).2 Y hYv hYq
    refine ⟨x, fun p hp ↦ ?_⟩
    unfold ownP
    refine Iris.BI.exists_elim fun hbf ↦ ?_
    intro y _ hy
    have hpY : (⟨(p : PSp Ω), hbf⟩ : BoundedFootprintSpace Bool) = Y :=
      Subtype.ext (hp.trans hYval.symm)
    rw [hpY] at hy
    exact UpperSet.upper _ hy hmem
  obtain ⟨v₀, hv₀⟩ := μ.support_nonempty
  have : Nonempty X := ⟨(hwit v₀ hv₀).choose⟩
  choose! f hf using hwit
  -- the fibres of `s` themselves form the kernel
  let ℓ : ProbabilityTheory.TrivialMarkovKernel α s :=
    letI : MeasurableSpace Ω := s.ms
    letI : MeasurableSpace α := ⊤
    ⟨⟨fun v ↦ (w v).1, measurable_from_top⟩, ⟨fun v ↦ (w v).2⟩⟩
  have key : ownP s ⊢ ∃ f : α → X, 𝒞⟨μ⟩ v; fmk (Qr (v, f v)) := by
    iintro Hown
    iexists f
    unfold jointConditioning
    iexists s, ℓ
    isplitl [Hown]
    · iexact Hown
    · isplitl []
      · ipureintro
        exact hsmix
      · iintro %v Hv
        iapply (hf v.1 v.2 (ℓ v.1) rfl)
        iexact Hv
  exact key r hv ⟨_, ⟨hbfs, rfl⟩, hsr⟩

variable {f : β → α} in
set_option linter.style.haveILetI false in
open MeasureTheory in
/-- Relabelling the values of a conditioning along a bijection of supports that preserves
the weights.  Keep the space and pull the fibres back along `f`: the mixture over `μ'` is the
mixture over `μ` reindexed by the bijection. -/
theorem C_TRANSF
  (h₁ : Set.BijOn f μ₂.support μ₁.support)
  (h₂ : ∀ b ∈ μ₂.support, μ₂ b = μ₁ (f b)) :
  𝒞⟨μ₁⟩ a; K a ⊢ 𝒞⟨μ₂⟩ b; K (f b) := by
  intro r hv hr
  have hown : own r ⊢ jointConditioning μ₁ (fun a ↦ K a) :=
    fun _ _ hry ↦ UpperSet.upper _ hry hr
  obtain ⟨s, hbfs, hsr, w, hsmix, hX⟩ := cond_elim hv hown
  -- the fibres pulled back along `f`
  let ℓ : ProbabilityTheory.TrivialMarkovKernel β s :=
    letI : MeasurableSpace Ω := s.ms
    letI : MeasurableSpace β := ⊤
    ⟨⟨fun b ↦ (w (f b)).1, measurable_from_top⟩, ⟨fun b ↦ (w (f b)).2⟩⟩
  -- they mix to `s` along `μ'`: reindex the sum over the support by the bijection
  have hℓmix : s.μ = (μ₂.toMeasureWithMs ⊤).bind ℓ.1 := by
    refine @Measure.ext Ω s.ms _ _ fun A hA ↦ ?_
    letI : MeasurableSpace α := ⊤
    rw [Measure.bind_apply hA (ProbabilityTheory.Kernel.measurable ℓ.1).aemeasurable, hsmix,
      Measure.bind_apply hA measurable_from_top.aemeasurable,
      pmf_lintegral_eq_tsum, pmf_lintegral_eq_tsum, ← h₁.equiv.tsum_eq]
    refine tsum_congr fun b ↦ ?_
    show (w (f b)).1 A * μ₁ (f b) = (w (f b)).1 A * μ₂ b
    rw [h₂ b b.2]
  have hKb : ∀ b ∈ μ₂.support, ownP (ℓ b) ⊢ K (f b) := by
    intro b hb
    obtain ⟨X, hXval, hXK⟩ := hX (f b) (h₁.mapsTo hb)
    unfold ownP
    refine Iris.BI.exists_elim fun hbf ↦ ?_
    rw [show (⟨((ℓ b : PSpace Ω) : PSp Ω), hbf⟩ : BoundedFootprintSpace Bool) = X from
      Subtype.ext (by rw [hXval]; rfl)]
    exact hXK
  have key : ownP s ⊢ 𝒞⟨μ₂⟩ b; K (f b) := by
    unfold jointConditioning
    iintro Hown
    iexists s, ℓ
    isplitl [Hown]
    · iexact Hown
    · isplitl []
      · ipureintro
        exact hℓmix
      · iintro %b Hb
        iapply (hKb b.1 b.2)
        iexact Hb
  exact key r hv ⟨_, ⟨hbfs, rfl⟩, hsr⟩

variable {E : RV Prop} in
set_option linter.style.haveILetI false in
open MeasureTheory in
/-- Sure facts are convex: if every fibre of a conditioning makes `a` sure, so does their
mixture.  Each fibre's exceptional set has a measurable null cover on the conditioned space;
the (countable) intersection of the covers is null under every fibre, hence under the mixture. -/
theorem C_SURE_CONVEX : 𝒞⟨μ⟩ _v; ⌈E⌉ ⊢ ⌈E⌉ := by
  intro r hv hr
  have hown : own r ⊢ jointConditioning μ (fun _ ↦ ⌈E⌉) :=
    fun _ _ hry ↦ UpperSet.upper _ hry hr
  obtain ⟨s, hbfs, hsr, w, hsmix, hX⟩ := cond_elim hv hown
  -- each fibre makes `a` sure
  have hnull : ∀ v ∈ μ.support, (w v).1 {ρ | ¬ E ρ} = 0 := by
    intro v hv'
    obtain ⟨X, hXval, hXK⟩ := hX v hv'
    have hXv : ✓X := by
      show X.val ≠ (⊤ : PSp Ω)
      rw [hXval]
      exact WithTop.coe_ne_top
    obtain ⟨q, ⟨P, hq⟩, hqX⟩ := hXK X hXv (le_refl X)
    obtain ⟨e₁, _, hle, hownP, hpure⟩ := (Quotient.exact hq).2 X hXv hqX
    obtain ⟨r₁, ⟨hbfP, hr₁⟩, he₁⟩ := hownP
    have he₁X : e₁ ≤ X := le_trans (le_mul_of_one_le PSp.one_le) hle
    have hPX : (P : PSp Ω) ≤ X.val :=
      le_trans ((Quotient.exact hr₁).2 e₁ (valid_mono he₁X hXv) he₁) he₁X
    rw [hXval] at hPX
    exact PSpace.null_of_le (WithTop.coe_le_coe.1 hPX) hpure
  -- measurable null covers on `s`, and their intersection over the support
  have hcover : ∀ v ∈ μ.support, ∃ N, {ρ | ¬ E ρ} ⊆ N ∧ @MeasurableSet Ω s.ms N ∧
      (w v).1 N = 0 :=
    fun v hv' ↦ @exists_measurable_superset_of_null Ω s.ms _ _ (hnull v hv')
  choose! N hNsub hNmeas hNnull using hcover
  have := μ.support_countable.to_subtype
  have hNi : @MeasurableSet Ω s.ms (⋂ v : μ.support, N v) :=
    @MeasurableSet.iInter Ω _ s.ms _ _ fun v : μ.support ↦ hNmeas v.1 v.2
  have hsN : s.μ (⋂ v : μ.support, N v) = 0 := by
    letI : MeasurableSpace α := ⊤
    rw [hsmix, Measure.bind_apply hNi measurable_from_top.aemeasurable]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [ae_mem_support μ] with v hv'
    exact measure_mono_null (Set.iInter_subset _ ⟨v, hv'⟩) (hNnull v hv')
  have hs : s.μ {ρ | ¬ E ρ} = 0 :=
    measure_mono_null (Set.subset_iInter fun v : μ.support ↦ hNsub v.1 v.2) hsN
  exact ⟨_, ⟨s, rfl⟩, r, 1, by rw [mul_one], ⟨_, ⟨hbfs, rfl⟩, hsr⟩, hs⟩

/-- A sure fact holding in every fibre can be pulled out of the conditioning: it is sure on the
mixture (`C_SURE_CONVEX`), and a sure fact splits off anything it holds alongside
(`SURE_AND_STAR`). -/
theorem SURE_STR_CONVEX {K : α → FProp} {E : RV Prop} :
  𝒞⟨μ⟩ v; (K v ∗ ⌈E⌉) ⊢ ⌈E⌉ ∗ 𝒞⟨μ⟩ v; K v := by
  have hsure : 𝒞⟨μ⟩ v; (K v ∗ ⌈E⌉) ⊢ ⌈E⌉ :=
    entails_trans (C_CONS fun _ ↦ sep_elim_right) C_SURE_CONVEX
  have hcond : 𝒞⟨μ⟩ v; (K v ∗ ⌈E⌉) ⊢ 𝒞⟨μ⟩ v; K v := C_CONS fun _ ↦ sep_elim_left
  exact entails_trans (and_intro hsure hcond) SURE_AND_STAR

variable {Q : α × β → FProp} in
theorem C_FOR_ALL :
  𝒞⟨μ⟩ v; (∀ (x : β), Q (v, x)) ⊢ ∀ (x : β), 𝒞⟨μ⟩ v; Q (v, x) :=
  forall_intro fun x ↦ C_CONS fun _ ↦ forall_elim x

#check μ

/--
TODO(Preference?):
4 options.
- 0 `⌜μ X = 1⌝                   ∗ 𝒞⟨μ.toPMF⟩ v; K v ⊣⊢ 𝒞⟨μ.toPMF⟩ v; (⌜v ∈ X⌝ ∗ K v)`
- 1 `⌜μ.toMeasureWithMs ⊤ X = 1⌝ ∗ 𝒞⟨μ⟩ v; K v ⊣⊢ 𝒞⟨μ⟩ v; (⌜v ∈ X⌝ ∗ K v)`
- 2 `⌜∑' x : X, μ x = 1⌝         ∗ 𝒞⟨μ⟩ v; K v ⊣⊢ 𝒞⟨μ⟩ v; (⌜v ∈ X⌝ ∗ K v)`
- 3 `⌜μ.support ⊆ X⌝             ∗ 𝒞⟨μ⟩ v; K v ⊣⊢ 𝒞⟨μ⟩ v; (⌜v ∈ X⌝ ∗ K v)`

`0` looks the best (it keeps exactly `⌜μ X = 1⌝`) but it requires we use `μ : Measure`,
which needs a bunch of 'context': `[MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]`
`{μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]`

`1` is the current implementation which I believe gets closest to the paper, if we consider
that `0` needs a lot of extra fluff, and two casts to `PMF`.

`2` is in the current Bluebell model.

`3` is the tersest, but drops the `_ = 1` bit from the paper.
-/
theorem C_PURE {X : Set α} :
    ⌜μ.toMeasureWithMs ⊤ X = 1⌝ ∗ 𝒞⟨μ⟩ v; K v ⊣⊢ 𝒞⟨μ⟩ v; (⌜v ∈ X⌝ ∗ K v) := by
  have hsupp : μ.toMeasureWithMs ⊤ X = 1 ↔ μ.support ⊆ X :=
    @PMF.toMeasure_apply_eq_one_iff α ⊤ μ X MeasurableSpace.measurableSet_top
  constructor
  · unfold jointConditioning
    iintro ⟨%hX, %m, %κ, Hown, %hmix, Hall⟩
    iexists m, κ
    isplitl [Hown]
    · iexact Hown
    · isplitl []
      · ipureintro
        exact hmix
      · iintro %v Hv
        isplitl []
        · ipureintro
          exact hsupp.1 hX v.2
        · iapply Hall
          iexact Hv
  · -- every fibre is a valid resource, so its continuation's pure part holds
    have hpure : 𝒞⟨μ⟩ v; (⌜v ∈ X⌝ ∗ K v) ⊢ ⌜μ.toMeasureWithMs ⊤ X = 1⌝ := by
      intro r hv hr
      have hown : own r ⊢ jointConditioning μ (fun v ↦ iprop(⌜v ∈ X⌝ ∗ K v)) :=
        fun _ _ hry ↦ UpperSet.upper _ hry hr
      obtain ⟨s, -, -, w, -, hX'⟩ := cond_elim hv hown
      refine hsupp.2 fun v hv' ↦ ?_
      obtain ⟨Y, hYval, hYK⟩ := hX' v hv'
      have hYv : ✓Y := by
        show Y.val ≠ (⊤ : PSp Ω)
        rw [hYval]
        exact WithTop.coe_ne_top
      exact (entails_trans hYK sep_elim_left) Y hYv (le_refl Y)
    refine pure_elim _ hpure fun hX ↦ ?_
    iintro H
    isplitl []
    · ipureintro
      exact hX
    · iapply (C_CONS fun _ ↦ sep_elim_right)
      iexact H

end JointConditioningRules

section OwnershipAndDistributions

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
theorem SURE_DIRAC {v : α} : E ~ δ v ⊣⊢ ⌈E = v⌉ := by
  have h : (E ~ δ v) = ⌈fun ρ ↦ E ρ = v⌉ :=
    ownP_pure_congr (fun P ↦ law_dirac_iff P)
  rw [h]
  exact ⟨entails_rfl, entails_rfl⟩

theorem SURE_EQ_INJ {E : RV α} {v v' : α} :
  ⌈(E = v)⌉ ∗ ⌈(E = v')⌉
  ⊢ ⌜v = v'⌝ := sorry

end OwnershipAndDistributions

end Rules

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

theorem very_sure {E : Ω → Prop} : E ~ δ True ⊣⊢ ⌈E⌉ := by
  convert ESureDirac; simp

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
          simp [LiftUnary.lift]
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
