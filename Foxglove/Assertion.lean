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

class LiftMem (α β : Type) where
  lift : α → β → Ω → Prop

instance {α : Type} : LiftMem (RV α) (Set α) where
  lift := fun E S ω ↦ E ω ∈ S

syntax "lift(" term ", " term ")" : term

macro_rules
  | `(lift(¬$a, $ρ))            => `(¬lift($a, $ρ))
  | `(lift($a ∧ $b, $ρ))        => `(lift($a, $ρ) ∧ lift($b, $ρ))
  | `(lift($a ∨ $b, $ρ))        => `(lift($a, $ρ) ∨ lift($b, $ρ))
  | `(lift($a → $b, $ρ))        => `(lift($a, $ρ) → lift($b, $ρ))
  | `(lift($a = $b, $ρ))        => `(LiftBinary.lift $a $b $ρ)
  | `(lift(∀ $x:ident, $b, $ρ)) => `(∀ $x:ident, lift($b, $ρ))
  | `(lift(∃ $x:ident, $b, $ρ)) => `(∃ $x:ident, lift($b, $ρ))
  | `(lift($a ∈ $b, $ρ))        => `(LiftMem.lift $a $b $ρ)
  | `(lift(($x), $ρ))           => `(lift($x, $ρ))
  | `(lift($x, $ρ))             => `(LiftUnary.lift $x $ρ)

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

/-! ### `wp` and its locality clause

A `wp` that left its witness `b` wide open -- nothing relating it to `a` -- would be useless
for conditioning: two witnesses produced at two *different* ambients, which is exactly what
the fibres of a conditioning are, need not be comparable, and `CWPSwap`'s conclusion cannot
be assembled from them.

So `wp` carries one extra clause: the witness may not measure anything beyond what `a` could
already measure, together with the randomness the run itself added (`freshMs`).  It is an
upper bound, not an equality, so upward closure is unchanged -- a bigger `a` only relaxes
it, and the same witness still serves.

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

/-- A defined product measures exactly what its two factors measure between them: the
independent product's σ-algebra is the join.  Needed wherever a witness is multiplied by a
frame and `wp`'s locality clause has to be re-established. -/
lemma msOf_mul_le {x y : BoundedFootprintSpace Bool} (h : ✓(x * y)) :
    msOf (x * y) ≤ msOf x ⊔ msOf y := by
  obtain ⟨x', hx'⟩ := Option.ne_none_iff_exists'.mp (PSp.valid_def.mp (valid_mul h))
  obtain ⟨y', hy'⟩ := Option.ne_none_iff_exists'.mp (PSp.valid_def.mp (valid_mul_r h))
  obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp (PSp.valid_def.mp h)
  have hmul : PSp.mul ((x : PSp Ω)) ((y : PSp Ω)) = (s : PSp Ω) := hs
  rw [hx', hy'] at hmul
  unfold msOf
  rw [hs, hx', hy']
  exact le_of_eq (PSp.mul_inversion hmul).1



open Interp Interp.ProbTree Iris.BI OURAProp in
/-- **The proposed `wp`.**  `wp` with the locality clause `msOf b ≤ msOf a ⊔ freshMs …`. -/
def wp {α : Type} [Inhabited α] {m : Type → Type} [Interp.BernoulliInterpretable m]
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

-- open Interp Interp.ProbTree Iris.BI OURAProp in
-- def wp {α : Type} [Inhabited α] {m : Type → Type} [Interp.BernoulliInterpretable m]
--     (t : m α) (Q : RV α → FProp) : FProp :=
--   fmk {
--     carrier := {a |
--       ∀ (μ₀ : BoundedFootprintPsp) (c : BoundedFootprintSpace Bool),
--         ✓μ₀.psp → a * c ≤ μ₀.toSpace →
--         ∃ b : BoundedFootprintSpace Bool,
--           b * c ≤ (run t μ₀).1.toSpace ∧ ✓b ∧
--             (own b ⊢ Q (result (run t μ₀)))}
--     upper' := by
--       intro x y hxy hx μ₀ c hv hle
--       exact hx μ₀ c hv (le_trans (mul_le_mul_right_le hxy c) hle)
--   }

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

/-- Conditioning is monotone in its continuation. -/
lemma jointConditioning_mono {A : Type} {ν : PMF A} {K K' : A → FProp}
    (h : ∀ x, K x ⊢ K' x) : jointConditioning ν K ⊢ jointConditioning ν K' := by
  unfold jointConditioning
  exact exists_mono fun m ↦ exists_mono fun κ ↦ sep_mono_right (sep_mono_right
    (forall_mono fun v ↦ wand_mono_right (h v)))
--
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

/-- A sure fact weakens: the exceptional set only shrinks. -/
theorem liftPred_mono {a b : Ω → Prop} (h : ∀ ρ, a ρ → b ρ) : ⌈a⌉ ⊢ ⌈b⌉ := by
  intro m hv hm
  obtain ⟨q, ⟨P, hq⟩, hqm⟩ := hm
  obtain ⟨d₁, d₂, hle, hown, hpure⟩ := (Quotient.exact hq).2 m hv hqm
  exact ⟨_, ⟨P, rfl⟩, d₁, d₂, hle, hown,
    MeasureTheory.measure_mono_null (fun ρ hρ hab ↦ hρ (h ρ hab)) hpure⟩

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

scoped infix:69 " ⊗ " => product

scoped notation:70 E₁:71 " ×ᵣ " E₂:71 => fun s => (E₁ s, E₂ s)

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

open MeasureTheory in
/-- A measure carried by a countable set is the sum of its masses at the points. -/
lemma measure_eq_tsum_of_countable {γ : Type} [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (ν : Measure γ) {S : Set γ} (hS : S.Countable) (hnull : ν Sᶜ = 0) (T : Set γ) :
    ν T = ∑' p : ↥(T ∩ S), ν {(p : γ)} := by
  rw [← measure_inter_conull (s := T) hnull]
  conv_lhs => rw [← Set.biUnion_of_singleton (T ∩ S)]
  exact measure_biUnion (hS.mono Set.inter_subset_right)
    (fun _ _ _ _ h ↦ Set.disjoint_singleton.2 h) (fun _ _ ↦ measurableSet_singleton _)

set_option linter.style.haveILetI false in
open MeasureTheory in
/-- The converse of `split_of_product_law`: two independent pieces carrying the components'
laws carry the product law of the pair.  Each component has a measurable version, which can
be moved into its law's (countable) support off a null set; the pair of those versions then
takes countably many values, so it is measurable, and its law agrees with `μ₁ ⊗ μ₂` at every
point by independence. -/
theorem PSpace.product_law_of_split {E₁ : Ω → α} {E₂ : Ω → β} {μ₁ : PMF α} {μ₂ : PMF β}
    {P₁ P₂ s : PSpace Ω} (hs : s =ᵢ P₁ ⊕ᵢ P₂)
    (ham₁ : almostMeasurable E₁ (P₁ : PSp Ω))
    (hlaw₁ : @Measure.map Ω α P₁.ms ⊤ E₁ P₁.μ = μ₁.toMeasureWithMs ⊤)
    (ham₂ : almostMeasurable E₂ (P₂ : PSp Ω))
    (hlaw₂ : @Measure.map Ω β P₂.ms ⊤ E₂ P₂.μ = μ₂.toMeasureWithMs ⊤) :
    almostMeasurable (fun ω ↦ (E₁ ω, E₂ ω)) (s : PSp Ω) ∧
      @Measure.map Ω (α × β) s.ms ⊤ (fun ω ↦ (E₁ ω, E₂ ω)) s.μ
        = (μ₁ ⊗ μ₂).toMeasureWithMs ⊤ := by
  classical
  have hp₁ := P₁.isProbability
  have hp₂ := P₂.isProbability
  have hps := s.isProbability
  letI : MeasurableSpace α := ⊤
  letI : MeasurableSpace β := ⊤
  letI : MeasurableSpace (α × β) := ⊤
  haveI : MeasurableSingletonClass (α × β) := ⟨fun _ ↦ trivial⟩
  replace ham₁ : @AEMeasurable Ω α ⊤ P₁.ms E₁ P₁.μ := ham₁
  replace ham₂ : @AEMeasurable Ω β ⊤ P₂.ms E₂ P₂.μ := ham₂
  have h1s : P₁ ≤ s := PSpace.le_of_isIndependentProduct_left hs
  have h2s : P₂ ≤ s := PSpace.le_of_isIndependentProduct_right hs
  obtain ⟨a₀, ha₀⟩ := μ₁.support_nonempty
  obtain ⟨b₀, hb₀⟩ := μ₂.support_nonempty
  -- measurable versions of the components, valued in the supports
  set f₁ : Ω → α := fun ω ↦ if ham₁.mk E₁ ω ∈ μ₁.support then ham₁.mk E₁ ω else a₀ with hf₁def
  set f₂ : Ω → β := fun ω ↦ if ham₂.mk E₂ ω ∈ μ₂.support then ham₂.mk E₂ ω else b₀ with hf₂def
  have hf₁ : @Measurable Ω α P₁.ms ⊤ f₁ :=
    (measurable_from_top (f := fun a ↦ if a ∈ μ₁.support then a else a₀)).comp
      ham₁.measurable_mk
  have hf₂ : @Measurable Ω β P₂.ms ⊤ f₂ :=
    (measurable_from_top (f := fun b ↦ if b ∈ μ₂.support then b else b₀)).comp
      ham₂.measurable_mk
  have hf₁r : ∀ ω, f₁ ω ∈ μ₁.support := fun ω ↦ by
    simp only [hf₁def]; split_ifs with h
    · exact h
    · exact ha₀
  have hf₂r : ∀ ω, f₂ ω ∈ μ₂.support := fun ω ↦ by
    simp only [hf₂def]; split_ifs with h
    · exact h
    · exact hb₀
  -- each version is a.e. its component: the version leaves the support only on a null set
  have hae₁ : E₁ =ᵐ[P₁.μ] f₁ := by
    have hmk : @Measure.map Ω α P₁.ms ⊤ (ham₁.mk E₁) P₁.μ = μ₁.toMeasureWithMs ⊤ :=
      (Measure.map_congr ham₁.ae_eq_mk).symm.trans hlaw₁
    have hnull : P₁.μ (ham₁.mk E₁ ⁻¹' (μ₁.support)ᶜ) = 0 := by
      rw [← Measure.map_apply ham₁.measurable_mk MeasurableSpace.measurableSet_top, hmk,
        PMF.toMeasureWithMs]
      exact (PMF.toMeasure_apply_eq_zero_iff μ₁ MeasurableSpace.measurableSet_top).2
        disjoint_compl_right
    refine ham₁.ae_eq_mk.trans (ae_iff.2 (measure_mono_null (fun ω hω ↦ ?_) hnull))
    simp only [Set.mem_setOf_eq, hf₁def] at hω
    split_ifs at hω with h
    · exact absurd rfl hω
    · exact h
  have hae₂ : E₂ =ᵐ[P₂.μ] f₂ := by
    have hmk : @Measure.map Ω β P₂.ms ⊤ (ham₂.mk E₂) P₂.μ = μ₂.toMeasureWithMs ⊤ :=
      (Measure.map_congr ham₂.ae_eq_mk).symm.trans hlaw₂
    have hnull : P₂.μ (ham₂.mk E₂ ⁻¹' (μ₂.support)ᶜ) = 0 := by
      rw [← Measure.map_apply ham₂.measurable_mk MeasurableSpace.measurableSet_top, hmk,
        PMF.toMeasureWithMs]
      exact (PMF.toMeasure_apply_eq_zero_iff μ₂ MeasurableSpace.measurableSet_top).2
        disjoint_compl_right
    refine ham₂.ae_eq_mk.trans (ae_iff.2 (measure_mono_null (fun ω hω ↦ ?_) hnull))
    simp only [Set.mem_setOf_eq, hf₂def] at hω
    split_ifs at hω with h
    · exact absurd rfl hω
    · exact h
  -- the laws of the versions, at a point
  have hsing₁ : ∀ a, P₁.μ (f₁ ⁻¹' {a}) = μ₁ a := fun a ↦ by
    rw [← Measure.map_apply hf₁ MeasurableSpace.measurableSet_top,
      ← Measure.map_congr hae₁, hlaw₁, PMF.toMeasureWithMs,
      PMF.toMeasure_apply_singleton _ _ MeasurableSpace.measurableSet_top]
  have hsing₂ : ∀ b, P₂.μ (f₂ ⁻¹' {b}) = μ₂ b := fun b ↦ by
    rw [← Measure.map_apply hf₂ MeasurableSpace.measurableSet_top,
      ← Measure.map_congr hae₂, hlaw₂, PMF.toMeasureWithMs,
      PMF.toMeasure_apply_singleton _ _ MeasurableSpace.measurableSet_top]
  -- the pair of versions takes countably many values, so it is measurable
  set g : Ω → α × β := fun ω ↦ (f₁ ω, f₂ ω) with hgdef
  set S : Set (α × β) := μ₁.support ×ˢ μ₂.support with hSdef
  have hS : S.Countable := μ₁.support_countable.prod μ₂.support_countable
  have hgr : ∀ ω, g ω ∈ S := fun ω ↦ ⟨hf₁r ω, hf₂r ω⟩
  have hpt : ∀ p : α × β, MeasurableSet[s.ms] (g ⁻¹' {p}) := fun p ↦ by
    rw [show g ⁻¹' {p} = f₁ ⁻¹' {p.1} ∩ f₂ ⁻¹' {p.2} by
      ext ω; simp [hgdef, Prod.ext_iff]]
    exact (h1s.1 _ (hf₁ MeasurableSpace.measurableSet_top)).inter
      (h2s.1 _ (hf₂ MeasurableSpace.measurableSet_top))
  have hg : @Measurable Ω (α × β) s.ms ⊤ g := by
    intro T _
    rw [show g ⁻¹' T = ⋃ p ∈ T ∩ S, g ⁻¹' {p} by
      ext ω; simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop]
      exact ⟨fun h ↦ ⟨g ω, ⟨h, hgr ω⟩, rfl⟩, fun ⟨_, ⟨hp, _⟩, he⟩ ↦ he ▸ hp⟩]
    exact MeasurableSet.biUnion (hS.mono Set.inter_subset_right) fun p _ ↦ hpt p
  have hae : (fun ω ↦ (E₁ ω, E₂ ω)) =ᵐ[s.μ] g := by
    filter_upwards [PSpace.ae_eq_of_le h1s hae₁, PSpace.ae_eq_of_le h2s hae₂] with ω h₁ h₂
    simp [hgdef, h₁, h₂]
  refine ⟨⟨g, hg, hae⟩, ?_⟩
  rw [Measure.map_congr hae]
  -- both laws live on `S` and agree at every point
  have hν₁ : (@Measure.map Ω (α × β) s.ms ⊤ g s.μ) Sᶜ = 0 := by
    rw [Measure.map_apply hg MeasurableSpace.measurableSet_top]
    rw [show g ⁻¹' Sᶜ = ∅ from Set.eq_empty_of_forall_notMem fun ω h ↦ h (hgr ω)]
    exact measure_empty
  have hν₂ : ((μ₁ ⊗ μ₂).toMeasureWithMs ⊤) Sᶜ = 0 := by
    rw [PMF.toMeasureWithMs]
    refine (PMF.toMeasure_apply_eq_zero_iff _ MeasurableSpace.measurableSet_top).2 ?_
    refine Set.disjoint_left.2 fun p hp hpS ↦ hpS ?_
    obtain ⟨a, b⟩ := p
    rw [PMF.mem_support_iff, product_apply] at hp
    exact ⟨(PMF.mem_support_iff _ _).2 (left_ne_zero_of_mul hp),
      (PMF.mem_support_iff _ _).2 (right_ne_zero_of_mul hp)⟩
  ext T _
  rw [measure_eq_tsum_of_countable _ hS hν₁ T, measure_eq_tsum_of_countable _ hS hν₂ T]
  refine tsum_congr fun ⟨⟨a, b⟩, _⟩ ↦ ?_
  rw [Measure.map_apply hg MeasurableSpace.measurableSet_top,
    show g ⁻¹' {(a, b)} = f₁ ⁻¹' {a} ∩ f₂ ⁻¹' {b} by ext ω; simp [hgdef, Prod.ext_iff],
    hs.2 _ (hf₁ MeasurableSpace.measurableSet_top) _ (hf₂ MeasurableSpace.measurableSet_top),
    hsing₁, hsing₂, PMF.toMeasureWithMs,
    PMF.toMeasure_apply_singleton _ _ MeasurableSpace.measurableSet_top, product_apply]

/--
TODO(Do we want?) - I _think_ I can make this work as it says in the paper,
i.e. `(E₁, E₂) ~ (μ₁ ⊗ μ₂)` instead of `(fun s => (E₁ s, E₂ s)) ~ (μ₁ ⊗ μ₂)`, but it would be
touching quite a common syntax pattern, so I think I'd rather not.

Thoughts?
-/
theorem PROD_SPLIT :
  (E₁ ×ᵣ E₂) ~ (μ₁ ⊗ μ₂) ⊢ E₁ ~ μ₁ ∗ E₂ ~ μ₂ := by
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
  have h : (E ~ δ v) = ⌈E = v⌉ :=
    ownP_pure_congr (fun P ↦ law_dirac_iff P)
  rw [h]
  exact ⟨entails_rfl, entails_rfl⟩

variable {v v' : α} in
/-- A random variable is surely equal to at most one value: if `v ≠ v'`, the two sure facts
merge into one whose exceptional set is everything, which no probability space makes null. -/
theorem SURE_EQ_INJ : ⌈(E = v)⌉ ∗ ⌈(E = v')⌉ ⊢ ⌜v = v'⌝ := by
  refine entails_trans liftPred_sep ?_
  intro m hv h
  obtain ⟨q, ⟨P, hq⟩, hqm⟩ := h
  obtain ⟨_, _, _, _, hpure⟩ := (Quotient.exact hq).2 m hv hqm
  replace hpure : P.μ {ρ | ¬ (E ρ = v ∧ E ρ = v')} = 0 := hpure
  show v = v'
  by_contra hne
  have huniv : {ρ | ¬ (E ρ = v ∧ E ρ = v')} = Set.univ :=
    Set.eq_univ_of_forall fun ρ hρ ↦ hne (hρ.1.symm.trans hρ.2)
  have hP := P.isProbability
  rw [huniv, MeasureTheory.measure_univ] at hpure
  exact one_ne_zero hpure

scoped syntax:max (name := pmfStx) term:max " ∘ " ident "⁻¹" : term

scoped macro_rules (kind := pmfStx)
  | `($μ ∘ $f:ident⁻¹) => `(PMF.map $f $μ)

set_option linter.style.haveILetI false in
theorem SURE_SUB {E₁ : RV α} {E₂ : RV β} {f : α → β} :
  E₁ ~ μ ∗ ⌈E₂ = f ∘ E₁⌉ ⊢ E₂ ~ μ ∘ f⁻¹ := by
  intro m hv h
  obtain ⟨d₁, d₂, hle, h₁, h₂⟩ := h
  obtain ⟨y, hy⟩ : ∃ y : PSpace Ω, m.val = (y : PSp Ω) :=
    Option.ne_none_iff_exists'.mp (PSp.valid_def.mp hv)
  have hd₁ : d₁ ≤ m := le_trans (le_mul_of_one_le PSp.one_le) hle
  have hd₂ : d₂ ≤ m := by
    refine le_trans ?_ hle
    rw [mul_comm]
    exact le_mul_of_one_le PSp.one_le
  -- the space carrying `E₁`'s law sits below the ambient `y`
  obtain ⟨q₁, ⟨P₁, hq₁⟩, hq₁m⟩ := h₁
  obtain ⟨e₁, _, hlee₁, hown₁, hpure₁⟩ := (Quotient.exact hq₁).2 d₁ (valid_mono hd₁ hv) hq₁m
  obtain ⟨r₁, ⟨hbf₁, hr₁⟩, he₁⟩ := hown₁
  have he₁m : e₁ ≤ m := le_trans (le_trans (le_mul_of_one_le PSp.one_le) hlee₁) hd₁
  have hP₁ := (Quotient.exact hr₁).2 e₁ (valid_mono he₁m hv) he₁
  have hP₁y : P₁ ≤ y := by
    have hP₁m : (P₁ : PSp Ω) ≤ (m : PSp Ω) := le_trans hP₁ he₁m
    rw [hy] at hP₁m
    exact WithTop.coe_le_coe.1 hP₁m
  -- and so does the space on which `E₂ = f ∘ E₁` is sure
  obtain ⟨q₂, ⟨P₂, hq₂⟩, hq₂m⟩ := h₂
  obtain ⟨e₂, _, hlee₂, hown₂, hpure₂⟩ := (Quotient.exact hq₂).2 d₂ (valid_mono hd₂ hv) hq₂m
  obtain ⟨r₂, ⟨hbf₂, hr₂⟩, he₂⟩ := hown₂
  have he₂m : e₂ ≤ m := le_trans (le_trans (le_mul_of_one_le PSp.one_le) hlee₂) hd₂
  have hP₂ := (Quotient.exact hr₂).2 e₂ (valid_mono he₂m hv) he₂
  have hP₂y : P₂ ≤ y := by
    have hP₂m : (P₂ : PSp Ω) ≤ (m : PSp Ω) := le_trans hP₂ he₂m
    rw [hy] at hP₂m
    exact WithTop.coe_le_coe.1 hP₂m
  -- on `y`: `E₁` keeps its law, and `E₂` is almost surely `f ∘ E₁`
  letI : MeasurableSpace α := ⊤
  letI : MeasurableSpace β := ⊤
  obtain ⟨ham₁, hlaw₁⟩ := hpure₁
  replace ham₁ : @AEMeasurable Ω α ⊤ P₁.ms E₁ P₁.μ := ham₁
  have ham₁y : @AEMeasurable Ω α ⊤ y.ms E₁ y.μ :=
    ⟨ham₁.mk E₁, ham₁.measurable_mk.mono hP₁y.1 le_rfl, PSpace.ae_eq_of_le hP₁y ham₁.ae_eq_mk⟩
  have hlaw₁y : @MeasureTheory.Measure.map Ω α y.ms ⊤ E₁ y.μ = μ.toMeasureWithMs ⊤ :=
    (PSpace.map_eq_of_le (le_refl y) hP₁y ham₁y ham₁).trans hlaw₁
  have hnull : y.μ {ρ | ¬ E₂ ρ = (f ∘ E₁) ρ} = 0 := PSpace.null_of_le hP₂y hpure₂
  have hae : E₂ =ᵐ[y.μ] f ∘ E₁ := MeasureTheory.ae_iff.2 hnull
  have hf : Measurable f := measurable_from_top
  have hfE₁ : @AEMeasurable Ω β ⊤ y.ms (f ∘ E₁) y.μ := hf.comp_aemeasurable ham₁y
  have hbfy : HasBoundedFootprint (y : PSp Ω) := hy ▸ m.property
  have hmy : (⟨(y : PSp Ω), hbfy⟩ : BoundedFootprintSpace Bool) = m := Subtype.ext hy.symm
  refine ⟨_, ⟨y, rfl⟩, m, 1, ?_, ⟨_, ⟨hbfy, rfl⟩, le_of_eq hmy⟩, ?_, ?_⟩
  · rw [mul_one]
  · exact hfE₁.congr hae.symm
  · show @MeasureTheory.Measure.map Ω β y.ms ⊤ E₂ y.μ = (μ.map f).toMeasureWithMs ⊤
    rw [MeasureTheory.Measure.map_congr hae, ← AEMeasurable.map_map_of_aemeasurable hf.aemeasurable ham₁y,
      hlaw₁y, PMF.toMeasureWithMs, PMF.toMeasureWithMs]
    exact PMF.toMeasure_map (p := μ) (hf := hf)

variable {f : α → β} in
theorem DIST_FUN : E ~ μ ⊢ (f ∘ E) ~ μ ∘ f⁻¹ := by
  refine entails_trans ?_ (SURE_SUB (E₁ := E) (E₂ := f ∘ E) (f := f))
  iintro H
  isplitl [H]
  · iexact H
  · dsimp only [LiftPred.lift]
    iexists (1 : PSpace Ω)
    isplitl []
    · exact ownP_one
    · ipureintro
      simp [LiftBinary.lift]

variable {v : α} in
theorem DIRAC_DUP : E ~ δ v ⊢ E ~ δ v ∗ E ~ δ v := by
  have h : (E ~ δ v) = ⌈E = v⌉ := ownP_pure_congr (fun P ↦ law_dirac_iff P)
  have h2 : (⌈E = v⌉ : FProp) = ⌈fun ω ↦ E ω = v ∧ E ω = v⌉ :=
    ownP_pure_congr fun P ↦ by simp [LiftUnary.lift, LiftBinary.lift]
  rw [h]
  nth_rewrite 1 [h2]
  exact liftPred_split

set_option linter.style.haveILetI false in
/-- A random variable lands in its law's support almost surely: the support's complement is
`μ`-null, so its preimage is null on the space carrying the law.  A sure fact held alongside
an assertion can be separated from it (`SURE_AND_STAR`), which turns the `∧` into `∗`. -/
theorem DIST_SUPP : E ~ μ ⊢ E ~ μ ∗ ⌈E ∈ μ.support⌉ := by
  have hsupp : E ~ μ ⊢ ⌈E ∈ μ.support⌉ := by
    dsimp only [hasDistribution, LiftPred.lift]
    refine exists_elim fun P ↦ entails_trans (sep_mono_right (pure_mono fun hP ↦ ?_))
      (exists_intro (Ψ := fun P : PSpace Ω ↦
        iprop(ownP P ∗ ⌜P.μ {ρ | ¬ LiftMem.lift E μ.support ρ} = 0⌝)) P)
    obtain ⟨ham, hmap⟩ := hP
    have hPp := P.isProbability
    letI : MeasurableSpace α := ⊤
    letI : MeasurableSpace Ω := P.ms
    replace ham : @AEMeasurable Ω α ⊤ P.ms E P.μ := ham
    have h := MeasureTheory.Measure.map_apply_of_aemeasurable ham
      (s := (μ.support)ᶜ) MeasurableSpace.measurableSet_top
    rw [hmap] at h
    show P.μ (E ⁻¹' (μ.support)ᶜ) = 0
    rw [← h, PMF.toMeasureWithMs]
    exact (PMF.toMeasure_apply_eq_zero_iff μ MeasurableSpace.measurableSet_top).2
      disjoint_compl_right
  exact entails_trans (and_intro hsupp entails_rfl) (entails_trans SURE_AND_STAR sep_comm.1)

/-- Independent random variables with known laws have the product law jointly: the two
spaces carrying the laws are independent in the ambient, and on their product the pair has
law `μ₁ ⊗ μ₂` (`PSpace.product_law_of_split`). -/
theorem PROD_UNSPLIT : E₁ ~ μ₁ ∗ E₂ ~ μ₂ ⊢ (E₁ ×ᵣ E₂) ~ (μ₁ ⊗ μ₂) := by
  intro m hv h
  obtain ⟨d₁, d₂, hle, h₁, h₂⟩ := h
  have hd₁ : d₁ ≤ m := le_trans (le_mul_of_one_le PSp.one_le) hle
  have hd₂ : d₂ ≤ m := by
    refine le_trans ?_ hle
    rw [mul_comm]
    exact le_mul_of_one_le PSp.one_le
  -- the space carrying `E₁`'s law sits in `d₁`
  obtain ⟨q₁, ⟨P₁, hq₁⟩, hq₁m⟩ := h₁
  obtain ⟨e₁, _, hlee₁, hown₁, hpure₁⟩ := (Quotient.exact hq₁).2 d₁ (valid_mono hd₁ hv) hq₁m
  obtain ⟨r₁, ⟨hbf₁, hr₁⟩, he₁⟩ := hown₁
  have he₁d : e₁ ≤ d₁ := le_trans (le_mul_of_one_le PSp.one_le) hlee₁
  have hP₁ : (⟨(P₁ : PSp Ω), hbf₁⟩ : BoundedFootprintSpace Bool) ≤ d₁ :=
    le_trans ((Quotient.exact hr₁).2 e₁ (valid_mono (le_trans he₁d hd₁) hv) he₁) he₁d
  -- and `E₂`'s in `d₂`
  obtain ⟨q₂, ⟨P₂, hq₂⟩, hq₂m⟩ := h₂
  obtain ⟨e₂, _, hlee₂, hown₂, hpure₂⟩ := (Quotient.exact hq₂).2 d₂ (valid_mono hd₂ hv) hq₂m
  obtain ⟨r₂, ⟨hbf₂, hr₂⟩, he₂⟩ := hown₂
  have he₂d : e₂ ≤ d₂ := le_trans (le_mul_of_one_le PSp.one_le) hlee₂
  have hP₂ : (⟨(P₂ : PSp Ω), hbf₂⟩ : BoundedFootprintSpace Bool) ≤ d₂ :=
    le_trans ((Quotient.exact hr₂).2 e₂ (valid_mono (le_trans he₂d hd₂) hv) he₂) he₂d
  -- so their product is defined and sits in `m`
  set R : BoundedFootprintSpace Bool :=
    (⟨(P₁ : PSp Ω), hbf₁⟩ : BoundedFootprintSpace Bool) * ⟨(P₂ : PSp Ω), hbf₂⟩ with hR
  have hRm : R ≤ m :=
    le_trans (le_trans (mul_le_mul_right_le hP₁ _) (mul_le_mul_left_le hP₂ _)) hle
  obtain ⟨s, hs⟩ : ∃ s : PSpace Ω, (R : PSp Ω) = .some s :=
    Option.ne_none_iff_exists'.mp (PSp.valid_def.mp (valid_mono hRm hv))
  have hsP : s =ᵢ P₁ ⊕ᵢ P₂ := PSp.mul_inversion hs
  have hbfs : HasBoundedFootprint (s : PSp Ω) := hs ▸ R.property
  have hsR : (⟨(s : PSp Ω), hbfs⟩ : BoundedFootprintSpace Bool) = R := Subtype.ext hs.symm
  obtain ⟨ham₁, hlaw₁⟩ := hpure₁
  obtain ⟨ham₂, hlaw₂⟩ := hpure₂
  refine ⟨_, ⟨s, rfl⟩, R, 1, by rw [mul_one]; exact hRm,
    ⟨_, ⟨hbfs, rfl⟩, le_of_eq hsR⟩, ?_⟩
  exact PSpace.product_law_of_split hsP ham₁ hlaw₁ ham₂ hlaw₂

end OwnershipAndDistributions

section JointConditioning

noncomputable def fuse (μ : PMF α) (κ : α → PMF β) : PMF (α × β) :=
  ⟨fun (v, w) => μ v * (κ v w), by
    have h : ∑' (p : α × β), μ p.1 * κ p.1 p.2 = 1 := by
      simp_rw [ENNReal.tsum_prod', ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one, PMF.tsum_coe]
    convert h ▸ ENNReal.summable.hasSum⟩

infix:69 " -< " => fuse

/-- Fusing is binding: draw `v` from `μ`, then `w` from `κ v`, and report the pair. -/
lemma fuse_eq_bind {κ : α → PMF β} :
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

/-- **C-FUSE.**  Conditioning on `v ← μ` and then on `w ← κ v` is conditioning once on the
fused law of the pair.  Left to right is `C_ASSOC`; right to left splits the fused law back
into its two stages with `C_UNASSOC`, and relabels each inner stage's values `(v, w) ↦ w`
with `C_TRANSF`, which is a bijection of supports preserving the weights. -/
theorem C_FUSE {K : (α × β) → FProp} :
    𝒞⟨μ⟩ v; 𝒞⟨κ v⟩ w; (K (v, w)) ⊣⊢ 𝒞⟨μ -< κ⟩ (v, w) ; K (v, w) := by
  constructor
  · refine C_ASSOC (κ := κ) ?_
    rw [fuse_eq_bind]
    rfl
  · rw [fuse_eq_bind]
    refine entails_trans (C_UNASSOC (κ := fun v ↦ (κ v).map fun w ↦ (v, w))) (C_CONS fun v ↦ ?_)
    have hinj : Function.Injective fun w : β ↦ (v, w) := fun _ _ h ↦ (Prod.mk.inj h).2
    refine C_TRANSF (f := fun w ↦ (v, w)) ?_ ?_
    · rw [PMF.support_map]
      exact hinj.injOn.bijOn_image
    · intro b _
      rw [PMF.map_apply, tsum_eq_single b]
      · simp
      · intro w hw
        simp [Ne.symm hw]

variable {K : (α × β) → FProp} in
/-- **C-SWAP.**  Independent conditionings commute.  Fuse the two into one conditioning on the
product law (`C_FUSE`), relabel its values along `Prod.swap` (`C_TRANSF`: the two product
laws agree up to swapping), and unfuse in the other order. -/
theorem C_SWAP :
  𝒞⟨μ₁⟩ v₁; 𝒞⟨μ₂⟩ v₂; K (v₁, v₂) ⊢ 𝒞⟨μ₂⟩ v₂; 𝒞⟨μ₁⟩ v₁; K (v₁, v₂) := by
  have hw : ∀ (a : α) (b : β), (μ₂ -< fun _ ↦ μ₁) (b, a) = (μ₁ -< fun _ ↦ μ₂) (a, b) :=
    fun a b ↦ by
      show μ₂ b * μ₁ a = μ₁ a * μ₂ b
      exact mul_comm _ _
  have hbij : Set.BijOn Prod.swap (μ₂ -< fun _ ↦ μ₁).support (μ₁ -< fun _ ↦ μ₂).support := by
    refine ⟨fun ⟨b, a⟩ h ↦ ?_, Prod.swap_injective.injOn, fun ⟨a, b⟩ h ↦ ⟨(b, a), ?_, rfl⟩⟩
    · rw [PMF.mem_support_iff] at h ⊢
      rwa [Prod.swap_prod_mk, ← hw]
    · rw [PMF.mem_support_iff] at h ⊢
      rwa [hw]
  refine entails_trans (C_FUSE (κ := fun _ ↦ μ₂) (K := K)).1 ?_
  refine entails_trans (C_TRANSF (f := Prod.swap) hbij fun ⟨b, a⟩ _ ↦ hw a b) ?_
  exact (C_FUSE (μ := μ₂) (κ := fun _ ↦ μ₁) (K := fun q ↦ K (q.2, q.1))).2

variable {E : RV Prop} in
theorem SURE_CONVEX : 𝒞⟨μ⟩ _v; ⌈E⌉ ⊢ ⌈E⌉ := C_SURE_CONVEX

theorem DIST_CONVEX {α : Type} {μ : PMF α} : 𝒞⟨μ⟩ _v; E ~ μ' ⊢ E ~ μ' := by
  refine entails_trans (C_CONS fun _ ↦ C_UNIT_R.1) ?_
  refine entails_trans (C_SWAP (μ₁ := μ) (μ₂ := μ') (K := fun p ↦ ⌈E = p.2⌉)) ?_
  refine entails_trans (C_CONS fun w ↦ SURE_CONVEX (E := fun ω ↦ E ω = w)) ?_
  exact C_UNIT_R.2

/-- The first projection `π₁`, as in Bluebell.  An abbreviation rather than a notation, so that
it is a name and `μ ∘ π₁⁻¹` parses as the pushforward. -/
abbrev π₁ {α β : Type} : α × β → α := Prod.fst

/-- **Projecting a conditioning.**  A conditioning on pairs whose continuation only reads the
first component can be pushed to the marginal `μ ∘ π₁⁻¹`, provided the continuation is
convex: conditioning it on anything, with no dependence on the value, gives it back.  Write
`μ` as its marginal bound with the conditional laws (`PMF.filter`) and split (`C_UNASSOC`);
inside fibre `a` the first component is surely `a` (`C_PURE`), so the inner conditioning no
longer depends on its value and collapses by convexity. -/
theorem C_PROJ_OF_CONVEX {μ : PMF (α × β)} {K : α → FProp}
    (hK : ∀ (a : α) (ν : PMF (α × β)), 𝒞⟨ν⟩ _p; K a ⊢ K a) :
    𝒞⟨μ⟩ p; K p.1 ⊢ 𝒞⟨μ ∘ π₁⁻¹⟩ a; K a := by
  classical
  -- the marginal at `a` sums the joint law over the second component
  have hmarg : ∀ a, (μ ∘ π₁⁻¹) a = ∑' b, μ (a, b) := fun a ↦ by
    rw [PMF.map_apply, ENNReal.tsum_prod', tsum_eq_single a]
    · simp
    · intro a' ha'
      simp [Ne.symm ha']
  have hind : ∀ a, ∑' p, {p : α × β | p.1 = a}.indicator μ p = (μ ∘ π₁⁻¹) a := fun a ↦ by
    rw [PMF.map_apply]
    exact tsum_congr fun p ↦ by by_cases h : p.1 = a <;> simp [Set.indicator, h, eq_comm]
  -- `μ` is its marginal bound with the conditional laws, each living on `{p | p.1 = a}`
  have hex : ∀ a, (μ ∘ π₁⁻¹) a ≠ 0 → ∃ p ∈ {p : α × β | p.1 = a}, p ∈ μ.support := by
    intro a ha
    rw [hmarg] at ha
    obtain ⟨b, hb⟩ := not_forall.1 fun h ↦ ha (ENNReal.tsum_eq_zero.2 h)
    exact ⟨(a, b), rfl, (PMF.mem_support_iff _ _).2 hb⟩
  let cond : α → PMF (α × β) := fun a ↦
    if h : (μ ∘ π₁⁻¹) a = 0 then (μ.map Prod.snd).map fun b ↦ (a, b)
    else μ.filter {p | p.1 = a} (hex a h)
  have hcond : ∀ a, (cond a).support ⊆ {p | p.1 = a} := by
    intro a p hp
    simp only [cond] at hp
    split_ifs at hp with h
    · rw [PMF.support_map] at hp
      obtain ⟨b, -, rfl⟩ := hp
      rfl
    · rw [PMF.support_filter] at hp
      exact hp.1
  have hbind : (μ ∘ π₁⁻¹).bind cond = μ := by
    ext ⟨a, b⟩
    rw [PMF.bind_apply, tsum_eq_single a]
    · by_cases h : (μ ∘ π₁⁻¹) a = 0
      · have hab : μ (a, b) = 0 := by
          refine nonpos_iff_eq_zero.1 ?_
          rw [← h, hmarg]
          exact ENNReal.le_tsum (f := fun b ↦ μ (a, b)) b
        rw [h, zero_mul, hab]
      · simp only [cond, dif_neg h]
        rw [PMF.filter_apply, hind,
          Set.indicator_of_mem (s := {p : α × β | p.1 = a}) (show (a, b).1 = a from rfl),
          mul_comm, mul_assoc, ENNReal.inv_mul_cancel h (PMF.apply_ne_top _ _), mul_one]
    · intro a' ha'
      have : (a, b) ∉ (cond a').support := fun hp ↦ ha' (hcond a' hp).symm
      rw [(PMF.apply_eq_zero_iff _ _).2 this, mul_zero]
  have hsplit := C_UNASSOC (μ := μ ∘ π₁⁻¹) (κ := cond) (K := fun p ↦ K p.1)
  rw [hbind] at hsplit
  refine entails_trans hsplit (C_CONS fun a ↦ ?_)
  -- inside fibre `a`, the first component is surely `a`
  have hX : (cond a).toMeasureWithMs ⊤ {p : α × β | p.1 = a} = 1 :=
    (@PMF.toMeasure_apply_eq_one_iff _ ⊤ (cond a) _ MeasurableSpace.measurableSet_top).2
      (hcond a)
  refine entails_trans (entails_trans emp_sep.2 (sep_mono (pure_intro hX) entails_rfl))
    (entails_trans C_PURE.1 (entails_trans (C_CONS fun p ↦ ?_) (hK a (cond a))))
  refine pure_elim _ sep_elim_left fun h ↦ ?_
  rw [← show p.1 = a from h]
  exact sep_elim_right

/-- **C-SURE-PROJ.**  Conditioning on a pair whose second component the sure fact ignores is
conditioning on the first component alone, under the marginal `μ ∘ π₁⁻¹`.  Sure facts are
convex (`SURE_CONVEX`), so `C_PROJ_OF_CONVEX` gives `⊢`; the marginal is `μ` followed by a
Dirac on the first component, which gives `⊣`. -/
theorem C_SURE_PROJ {μ : PMF (α × β)} {E : α → Ω → Prop} :
  𝒞⟨μ⟩ (v, _w); ⌈E v⌉ ⊣⊢ 𝒞⟨μ ∘ π₁⁻¹⟩ v; ⌈E v⌉ := by
  constructor
  · have h := C_PROJ_OF_CONVEX (μ := μ) (K := fun v ↦ ⌈E v⌉)
      fun a ν ↦ SURE_CONVEX (μ := ν) (E := E a)
    exact h
  · exact entails_trans (C_UNASSOC (μ := μ) (κ := fun p ↦ δ p.1) (K := fun v ↦ ⌈E v⌉))
      (C_CONS fun _ ↦ C_UNIT_L.1)

theorem C_SURE_PROJ_MANY {ι γ B : Type} {Xs : ι → RV γ} {μ : PMF ((ι → γ) × B)} :
  𝒞⟨μ⟩ (v, _w); ⌈∀ x, Xs x = v x⌉ ⊣⊢ 𝒞⟨μ ∘ π₁⁻¹⟩ v; ⌈∀ x, Xs x = v x⌉ := by
  have h := C_SURE_PROJ (μ := μ) (E := fun v ω ↦ ∀ x, LiftBinary.lift (Xs x) (v x) ω)
  exact h

theorem C_EXTRACT {E₁ : RV α} {E₂ : RV β} :
  𝒞⟨μ₁⟩ v₁; (⌈E₁ = v₁⌉ ∗ E₂ ~ μ₂) ⊢ E₁ ~ μ₁ ∗ E₂ ~ μ₂ := by
  -- in each fibre, both components are surely their values
  have hfib : ∀ v₁ : α, iprop(⌈E₁ = v₁⌉ ∗ E₂ ~ μ₂)
      ⊢ 𝒞⟨μ₂⟩ v₂; ⌈(E₁ ×ᵣ E₂) = (v₁, v₂)⌉ := fun v₁ ↦
    entails_trans (sep_mono_right C_UNIT_R.1) (entails_trans C_FRAME (C_CONS fun v₂ ↦
      entails_trans liftPred_sep (liftPred_mono fun _ h ↦ Prod.ext h.1 h.2)))
  refine entails_trans (C_CONS hfib) ?_
  refine entails_trans
    (C_FUSE (μ := μ₁) (κ := fun _ ↦ μ₂) (K := fun p ↦ ⌈(E₁ ×ᵣ E₂) = p⌉)).1 ?_
  refine entails_trans (C_UNIT_R (E := E₁ ×ᵣ E₂) (μ := μ₁ -< fun _ ↦ μ₂)).2 ?_
  exact PROD_SPLIT

/-- **C-DIST-PROJ.**  A law that only depends on the first component survives projecting the
conditioning to the marginal: laws are convex (`DIST_CONVEX`), so this is `C_PROJ_OF_CONVEX`. -/
theorem C_DIST_PROJ {A B C : Type} {μ₁ : PMF (A × B)} {μ₂ : A → PMF C} {E : A → RV C} :
  𝒞⟨μ₁⟩ (x, _y); E x ~ μ₂ x ⊢ 𝒞⟨μ₁ ∘ π₁⁻¹⟩ x; E x ~ μ₂ x := by
  have h := C_PROJ_OF_CONVEX (μ := μ₁) (K := fun x ↦ E x ~ μ₂ x)
    fun a ν ↦ DIST_CONVEX (μ := ν) (E := E a) (μ' := μ₂ a)
  exact h

end JointConditioning

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
  have h : (⌈E⌉ : FProp) = ⌈E = True⌉ := by
    congr 1
    funext ω
    simp [LiftUnary.lift, LiftBinary.lift]
  rw [h]
  exact SURE_DIRAC

/-- A sure fact is duplicable. -/
theorem liftPred_dup {p : Ω → Prop} : ⌈p⌉ ⊢ ⌈p⌉ ∗ ⌈p⌉ := by
  have h : (⌈p⌉ : FProp) = ⌈fun ω ↦ p ω ∧ p ω⌉ := by
    refine ownP_pure_congr (fun P ↦ ?_)
    have hs : {ρ | ¬ p ρ} = {ρ | ¬ (p ρ ∧ p ρ)} := by ext ρ; simp
    show P.μ {ρ | ¬ p ρ} = 0 ↔ P.μ {ρ | ¬ (p ρ ∧ p ρ)} = 0
    rw [hs]
  nth_rewrite 1 [h]
  exact liftPred_split

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
  obtain ⟨U, hU⟩ : ∃ U : UpperSet (BoundedFootprintSpace Bool), Q (fun _ ↦ x) = fmk U :=
    ⟨(Q (fun _ ↦ x)).out, (Quotient.out_eq _).symm⟩
  rw [hU]
  intro a hva ha μ₀ c hvalid hle
  refine ⟨a, ?_, hva, le_sup_left, ?_⟩
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
every fibre's witness lives on the one σ-algebra `m ⊔ R ⊔ fresh` (`wp`'s locality clause),
and that σ-algebra is independent of the frame because `m ⊗ R` was and fresh
randomness is independent of everything prior (`run_fresh`). -/
lemma CWPSwap_core {α β : Type} {m' : Type → Type} [Interp.BernoulliInterpretable m']
    [Inhabited α] {C : m' α} {μ : PMF β} {Q : β → RV α → FProp}
    (m : PSpace Ω) (κ : TrivialMarkovKernel β m)
    (hmix : m.μ = (μ.toMeasureWithMs ⊤).bind κ)
    (hbf : HasBoundedFootprint (m : PSp Ω)) (R : BoundedFootprintSpace Bool)
    (hfib : ∀ v ∈ μ.support, ∀ hk : HasBoundedFootprint ((κ v : PSpace Ω) : PSp Ω),
      own (R * ⟨((κ v : PSpace Ω) : PSp Ω), hk⟩) ⊢ wp C (Q v)) :
    own ((⟨(m : PSp Ω), hbf⟩ : BoundedFootprintSpace Bool) * R)
      ⊢ wp C (fun X ↦ 𝒞⟨μ⟩ v; Q v X) := by
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
    iprop(𝒞⟨μ⟩ v; wp C (Q v)) ⊢ wp C (fun x ↦ 𝒞⟨μ⟩ v; Q v x) := by
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
    iprop(ownP (κ v) -∗ wp C (Q v))) ⟨v, hv⟩)

/-- A postcondition that cannot tell almost-surely-equal random variables apart.

`CWPBind` needs this.  The bound run reports the *global* result of `C >>= F`, while the
continuation's `wp` reports the result of `F v` as a random variable of the `v`-fibre: the
two agree on that fibre and nowhere else, so an arbitrary `Q : RV β → FProp` cannot be
carried from one to the other. -/
def AEProper {β : Type} (Q : RV β → FProp) : Prop :=
  ∀ X Y : RV β, iprop(⌈fun ρ ↦ X ρ = Y ρ⌉ ∗ Q X) ⊢ Q Y

/-- **Mixability.**  An assertion that is recoverable from its fibres: if every fibre of a
conditioning establishes it, so does the mixture.  This is the Amaryllis notion of a
*convex* assertion, and `C_SURE_CONVEX` says sure facts have it.

`CWPBind` needs it on top of `AEProper`, and that is the whole of what `AEProper` is missing:
the proof obtains `Q` once per fibre, at the reweighted ambient the fibre lives in, and has
to produce it once for the whole run.  `not_convex_constQ` exhibits an `AEProper` `Q` that
is not convex, which is exactly why `CWPBind_counterexample` goes through. -/
def Convex (P : FProp) : Prop :=
  ∀ {γ : Type} (ν : PMF γ), (𝒞⟨ν⟩ _v; P) ⊢ P

/-- Sure facts are convex: `C_SURE_CONVEX` in the shape `Convex` wants. -/
lemma convex_liftPred {E : RV Prop} : Convex ⌈E⌉ := fun _ ↦ C_SURE_CONVEX

/-- A pure fact is convex: the support is nonempty, so some fibre already asserts it. -/
lemma convex_pure {φ : Prop} : Convex iprop(⌜φ⌝) := by
  intro γ ν r hv hr
  have hown : own r ⊢ jointConditioning ν (fun _ ↦ iprop(⌜φ⌝)) :=
    fun _ _ hry ↦ UpperSet.upper _ hry hr
  obtain ⟨s, hbfs, hsr, w, hsmix, hX⟩ := cond_elim hv hown
  obtain ⟨v₀, hv₀⟩ := ν.support_nonempty
  obtain ⟨Y, hYval, hYK⟩ := hX v₀ hv₀
  have hYv : ✓Y := by
    show Y.val ≠ (⊤ : PSp Ω)
    rw [hYval]
    exact WithTop.coe_ne_top
  exact hYK Y hYv (le_refl Y)

lemma convex_ftrue : Convex ftrue := fun _ ↦ entails_ftrue

/-- Convexity is closed under `∧`: push the conditioning through each conjunct. -/
lemma convex_and {P R : FProp} (hP : Convex P) (hR : Convex R) : Convex iprop(P ∧ R) :=
  fun ν ↦ and_intro (entails_trans (C_CONS fun _ ↦ and_elim_l) (hP ν))
    (entails_trans (C_CONS fun _ ↦ and_elim_r) (hR ν))

/-- Convexity is closed under `∀`, pointwise. -/
lemma convex_forall {γ : Type} {P : γ → FProp} (h : ∀ x, Convex (P x)) :
    Convex iprop(∀ x, P x) :=
  fun ν ↦ forall_intro fun x ↦ entails_trans (C_CONS fun _ ↦ forall_elim x) (h x ν)

/-- Value-indexed postconditions are automatically proper: they only look at the result
through `⌈X = x⌉`, and sure equalities substitute (`liftPred_subst`).  So `CWPBind`'s side
condition is discharged once and for all for the postconditions it is meant for. -/
lemma aeProper_valuePost {β : Type} (Q : β → FProp) :
    AEProper (fun X ↦ valuePost X Q) := by
  intro X Y
  unfold valuePost jointConditioning
  iintro ⟨Heq, %ν, %m, %κ, Hm, %hmix, Hall⟩
  iexists ν, m, κ
  isplitl [Hm]
  · iexact Hm
  · isplitl []
    · ipureintro
      exact hmix
    · iintro %v Hv
      ispecialize Hall $$ %v Hv
      icases Hall with ⟨Hsure, HQ⟩
      isplitl [Heq Hsure]
      · iapply liftPred_subst
        isplitl [Heq]
        · iexact Heq
        · iexact Hsure
      · iexact HQ

/-- Having a given law is `AEProper` too: condition on the law (`C_UNIT_R`), substitute the
sure equality in every fibre (`liftPred_subst`), and mix back.  So `AEProper` is a weak
side condition -- it holds of postconditions that are very far from mixable, which is what
`CWPBind_counterexample` exploits. -/
lemma aeProper_hasDistribution {α : Type} (ν : PMF α) : AEProper (fun X ↦ X ~ ν) := fun _ _ ↦
  entails_trans (sep_mono_right C_UNIT_R.1)
    (entails_trans C_FRAME (entails_trans (C_CONS fun _ ↦ liftPred_subst) C_UNIT_R.2))

/-- A law for `X` is already a `valuePost`, provided every fibre's postcondition holds
outright: condition on the law and hand each fibre its free postcondition. -/
lemma valuePost_of_law {α : Type} {X : RV α} {ν : PMF α} {Q' : α → FProp}
    (h : ∀ v, ⊢ Q' v) : (X ~ ν) ⊢ valuePost X Q' := by
  unfold valuePost
  refine entails_trans C_UNIT_R.1 (entails_trans (C_CONS ?_)
    (exists_intro (Ψ := fun ν' : PMF α ↦
      iprop(𝒞⟨ν'⟩ x; (⌈fun ρ ↦ X ρ = x⌉ ∗ Q' x))) ν))
  intro v
  show (⌈X = v⌉ : FProp) ⊢ iprop(⌈fun ρ ↦ X ρ = v⌉ ∗ Q' v)
  iintro H
  isplitl [H]
  · iexact H
  · exact h v

/-- A predicate that holds everywhere is surely true, and costs nothing: the exceptional set
is empty, so the trivial space witnesses it. -/
lemma liftPred_of_forall {a : Ω → Prop} (h : ∀ ρ, a ρ) : ⊢ (LiftPred.lift a : FProp) := by
  dsimp only [LiftPred.lift]
  iexists (1 : PSpace Ω)
  isplitl []
  · exact ownP_one
  · ipureintro
    have hs : {ρ : Ω | ¬ a ρ} = (∅ : Set Ω) := by ext ρ; simp [h ρ]
    rw [hs]
    simp

/-! ### Structural rules for `wp`

Consequence and framing do not touch the run: the witness a run produces does not depend on
the postcondition, and a frame the run never reads can be carried through the run's own
frame slot.  Both need the run to land in a *defined* space, which is `valid_run`. -/

section WPStructural

open Interp Interp.ProbTree

/-- **A run lands in a defined space.**  `bigStep` takes its valid branch and `ofTree`
always carries a `some`, so the output footprint is never `⊤`.  This is what lets the
witness of a run be known valid, which `WPFrame` needs. -/
lemma valid_run {α : Type} [Inhabited α] {m : Type → Type} [Interp.BernoulliInterpretable m]
    (t : m α) (μ₀ : BoundedFootprintPsp) (hv : ✓μ₀.psp) :
    ✓((run t μ₀).1.toSpace) := by
  show ((run t μ₀).1.psp) ≠ (⊤ : PSp Ω)
  rw [run, bigStep, dite_eq_left hv, ofTree_psp']
  exact Option.some_ne_none _

/-- **A program's value is determined by the bits it read.**  `runValue` and `runPath`
recurse on the same program and consume the same bits, so a tape is pinned down as far as
the value is concerned by the path. -/
lemma runValue_eq_of_runPath_eq {α : Type} (m : BernoulliM α) :
    ∀ {ρ ρ' : Ω}, runPath m ρ = runPath m ρ' → runValue m ρ = runValue m ρ' := by
  induction m with
  | pure a => intro ρ ρ' _; rfl
  | liftBind op c ih =>
    intro ρ ρ' h
    rw [runPath, runPath] at h
    obtain ⟨h0, htl⟩ := List.cons.inj h
    rw [runValue, runValue, h0]
    rw [h0] at htl
    exact ih (ρ' 0) htl

/-- Shifting past one more bit, from the inside. -/
lemma shiftBy_shift (n : ℕ) (ρ : Ω) : shiftBy n (shift ρ) = shiftBy (n + 1) ρ := rfl

/-- **The value of a bind, on a tape.**  Run `p`, then run `q` of its value on the tape `p`
left behind.  The first of the two tape-level halves of a `run`-level bind lemma; both are
plain structural inductions on the free monad. -/
lemma runValue_bind {α β : Type} (q : α → BernoulliM β) :
    ∀ (p : BernoulliM α) (ρ : Ω), runValue (p >>= q) ρ
      = runValue (q (runValue p ρ)) (shiftBy (runPath p ρ).length ρ) := by
  intro p
  induction p with
  | pure a => intro ρ; rfl
  | liftBind op c ih =>
    intro ρ
    show runValue ((c (ρ 0)) >>= q) (shift ρ) = _
    rw [ih (ρ 0) (shift ρ)]
    show _ = runValue (q (runValue (c (ρ 0)) (shift ρ)))
      (shiftBy ((ρ 0 :: runPath (c (ρ 0)) (shift ρ)).length) ρ)
    rw [List.length_cons, shiftBy_shift]

/-- **The path of a bind, on a tape**: `p`'s bits, then `q`'s. -/
lemma runPath_bind {α β : Type} (q : α → BernoulliM β) :
    ∀ (p : BernoulliM α) (ρ : Ω), runPath (p >>= q) ρ
      = runPath p ρ ++ runPath (q (runValue p ρ)) (shiftBy (runPath p ρ).length ρ) := by
  intro p
  induction p with
  | pure a => intro ρ; rfl
  | liftBind op c ih =>
    intro ρ
    show ρ 0 :: runPath ((c (ρ 0)) >>= q) (shift ρ) = _
    rw [ih (ρ 0) (shift ρ)]
    show _ = (ρ 0 :: runPath (c (ρ 0)) (shift ρ)) ++
      runPath (q (runValue (c (ρ 0)) (shift ρ)))
        (shiftBy ((ρ 0 :: runPath (c (ρ 0)) (shift ρ)).length) ρ)
    rw [List.cons_append, List.length_cons, shiftBy_shift]

/-- **The value a run reports is part of the randomness the run added.**  This is what makes
`wp`'s locality clause discharegable for `CWPDist`: the witness measures only the reported
value, and the reported value is a function of the path. -/
lemma comap_footprintValue_le_freshMs {α : Type} (b : BoundedFootprintPsp)
    (m : BernoulliM α) :
    MeasurableSpace.comap (footprintValue b m) ⊤ ≤ freshMs b m := by
  rintro _ ⟨T, -, rfl⟩
  refine ⟨footprintPath b m '' (footprintValue b m ⁻¹' T), trivial, ?_⟩
  ext ρ
  constructor
  · rintro ⟨ρ', hρ', hpath⟩
    show footprintValue b m ρ ∈ T
    rw [show footprintValue b m ρ = footprintValue b m ρ' from
      (runValue_eq_of_runPath_eq m hpath).symm]
    exact hρ'
  · intro hρ
    exact ⟨ρ, hρ, rfl⟩

/-- **Consequence.**  The witness a run produces is chosen without reference to the
postcondition, so the same witness serves a weaker one. -/
lemma WPCons {α : Type} [Inhabited α] {m : Type → Type} [Monad m]
    [Interp.LawfulBernoulliInterpretable m]
    {Q Q' : RV α → FProp} {t : m α} (h : ∀ v, Q v ⊢ Q' v) : iprop(wp t Q) ⊢ wp t Q' := by
  intro a hva ha μ₀ c hv hle
  obtain ⟨b, hb₁, hb₂, hb₃, hb₄⟩ := ha μ₀ c hv hle
  exact ⟨b, hb₁, hb₂, hb₃, entails_trans hb₄ (h _)⟩

/-- **Framing.**  `P` is not read by the run, so hand it to the run as part of its frame:
`wp t Q`'s witness `b` is disjoint from `p * c`, hence `p * b` is disjoint from `c` and
still sits inside the output footprint.  `p` is then handed back alongside `Q`. -/
lemma WPFrame {α : Type} [Inhabited α] {m : Type → Type} [Monad m]
    [Interp.LawfulBernoulliInterpretable m]
    {P : FProp} {Q : RV α → FProp} {t : m α} :
    iprop(P ∗ wp t Q) ⊢ wp t (fun v ↦ iprop(P ∗ (Q v))) := by
  obtain ⟨U, rfl⟩ : ∃ U : UpperSet (BoundedFootprintSpace Bool), P = fmk U :=
    ⟨P.out, (Quotient.out_eq _).symm⟩
  obtain ⟨Qr, rfl⟩ : ∃ Qr : RV α → UpperSet (BoundedFootprintSpace Bool),
      Q = fun X ↦ fmk (Qr X) :=
    ⟨fun X ↦ (Q X).out, funext fun X ↦ (Quotient.out_eq _).symm⟩
  intro a hva ha μ₀ c hv hle
  obtain ⟨p, w, hpw, hp, hw⟩ := ha
  have hvr : ✓((run t μ₀).1.toSpace) := valid_run t μ₀ hv
  have hwle : w * (p * c) ≤ μ₀.toSpace := by
    calc w * (p * c) = (p * w) * c := by rw [← mul_assoc, mul_comm w p]
      _ ≤ a * c := mul_le_mul_right_le hpw c
      _ ≤ μ₀.toSpace := hle
  obtain ⟨b, hb₁, hb₂, hb₃, hb₄⟩ := hw μ₀ (p * c) hv hwle
  have hkey : (p * b) * c ≤ (run t μ₀).1.toSpace := by
    calc (p * b) * c = b * (p * c) := by rw [mul_comm p b, mul_assoc]
      _ ≤ _ := hb₁
  have hvpb : ✓(p * b) := valid_mul (valid_mono hkey hvr)
  refine ⟨p * b, hkey, hvpb, ?_, ?_⟩
  · -- the frame measures no more than `a` did, and `b` is local to `w`
    have hpa : msOf p ≤ msOf a := msOf_mono (le_trans (le_mul_of_one_le PSp.one_le) hpw)
    have hwa : msOf w ≤ msOf a :=
      msOf_mono (le_trans (by rw [mul_comm]; exact le_mul_of_one_le PSp.one_le) hpw)
    calc msOf (p * b) ≤ msOf p ⊔ msOf b := msOf_mul_le hvpb
      _ ≤ msOf a ⊔ (msOf w ⊔ freshMs μ₀ (Interp.BernoulliInterpretable.interp t)) :=
          sup_le_sup hpa hb₃
      _ ≤ msOf a ⊔ freshMs μ₀ (Interp.BernoulliInterpretable.interp t) :=
          sup_le le_sup_left (sup_le (le_trans hwa le_sup_left) le_sup_right)
  · intro mm hvmm hmm
    exact ⟨p, b, hmm, hp, hb₄ b hb₂ (le_refl b)⟩

end WPStructural

/-! ### Sequencing

`F` consumes a value, so the result of `C` has to be split along its value before `F` can be
named: that is exactly `valuePost`, which conditions on the law of the result and hands each
fibre the value it reports.  The rule one would like is

```
  CWPBind : AEProper Q → wp C (fun X ↦ valuePost X (fun v ↦ wp (F v) Q)) ⊢ wp (C >>= F) Q
```

**It is false at that side condition** -- `CWPBind_counterexample` proves it -- so a
bi-entailment is out too (`CWPBind_biEntails_counterexample`).  Both refutations are stated
against the *locality-clause* `wp`, so moving from the old unconstrained `wp` to this one
does not repair the rule: the counterexample is about mixing an assertion, not about
assembling witnesses.

The diagnosis is that this rule is *not* the bind rule; it is the bind rule plus a
specialisation step.  `CWPBindC` is the bind rule: `F` runs once per fibre of `C`'s law, so
what comes back is one `Q v` per fibre, and a resource whose fibres satisfy `Q v Y` simply
*is* a conditioning `𝒞⟨ν⟩ v; Q v Y`.  Recording that in the conclusion costs nothing and
needs no side condition on `Q` (this is the shape `CWPSwap`'s conclusion has, for the same
reason).  `CWPBind` then asks for the conditioning to be collapsed back to a bare `Q Y`,
and *that* is `Convex`.  The counterexample attacks the collapse, not the bind: `constQ` is
perfectly fine as a `CWPBindC` postcondition.

With that split, `CWPBind` is proved outright from `CWPBindC` and `WPCons`, and what is left
is item 2 below -- a single semantic lemma -- plus the structural work of item 0.

**How this relates to Amaryllis** (arXiv 2605.13765).  `CWPSwap` is already exactly the
paper's `c-lift` (rule 2.5): `∀ x ∈ supp μ. {P x} E {V. Q x V}` gives
`{𝐂_{x←μ} P x} E {V. 𝐂_{x←μ} Q x V}` -- conditioning in, conditioning out, no side
condition, and crucially *the same* `E` in every fibre.  `CWPBindC` is **not** an instance of
it, and is not the paper's bind rule either.  The paper's bind (rule 2.4) is
`{P} E {W. P' W}`, `∀ W. {P' W} K[W] {V. Q V}` ⟹ `{P} K[E] {V. Q V}`, where `W` ranges over
*random variables* `Ω → Val` and `K[W]` is a random expression: the continuation is never
split along a value, so nothing is ever mixed back, which is why no convexity-like side
condition appears anywhere in that development.

Both logics are operational, so that is not the difference; the difference is the shape of
the step.  The paper's triples are over a small-step relation with *evaluation contexts*, so
`K[E]` reduces to `E`'s own steps and bind is structural -- Iris's `wp_bind`, essentially for
free.  `run` is big-step and runs a whole program to completion, so there is no evaluation
context to induct on and compositionality has to be proved outright.  (The resource side is
the easy direction here: with no heap and no permissions, none of the paper's `⊠`/authority
machinery is needed.)

On top of that, `wp` is indexed by a fixed `t : m α`, so a continuation `F : α → m β` has to
be routed through `valuePost` and run as a *different* program per fibre.  That per-fibre-program generalisation of `c-lift`/`CWPSwap_core` is the new work
`CWPBindC` needs; there is nothing in the paper to specialise.  The alternative is to follow
the paper properly and index `wp` by a random program.  The semantics already supports it --
`bigStep` takes `programs : bfpsp.atoms → BernoulliM α`, which *is* a random expression, and
`run` throws that away by passing `fun _ ↦ interp t`.  Reinstating it would buy the paper's
bind rule verbatim, with no conditioning and no convexity, and leave `valuePost`-style
per-value reasoning to `CWPSwap`, where it belongs.  Either way item 2 is still owed.

**0. The locality clause (done).**  The fibres of a conditioning live at *different*,
reweighted ambients, so the continuation's witnesses arrive one per fibre and have to be
assembled into a single resource.  An unconstrained witness leaves two fibres' witnesses
incomparable; the clause `msOf b ≤ msOf a ⊔ freshMs` bounds each of them, and
`freshMs_reweight` makes that bound the same at every fibre, since all fibres of a
conditioning carry the mixture's σ-algebra.  `CWPSwap` was already stated for this `wp` for
exactly that reason, and `CWPSwap_core` *is* the mixing argument, carried out.  What
sequencing needs is `CWPSwap_core` generalised from one program `C` run at every fibre to a
family `fun v ↦ F v`, one program per fibre.  The reweighting side is in place:
`BoundedFootprintPsp.reweight`, `freshMs_reweight`, `result_run_reweight`, and the
mixing-back lemma above `CWPSwap_core`.

**1. `Convex (Q X)`, for the collapse only.**  `AEProper` lets a fibre's report of `F v`
stand in for the global report of `C >>= F`; it says nothing about recovering `Q` from the
fibres.  `not_convex_constQ` shows the two are independent:
`constQ X := ⌈X = true⌉ ∨ ⌈X = false⌉` -- "the result is almost surely a constant" -- is
`AEProper` (`aeProper_constQ`) and is not convex, and that gap is the whole of the
counterexample.  `convex_liftPred` is the base case (`C_SURE_CONVEX`), and `convex_pure`,
`convex_and`, `convex_forall` close it under the connectives that preserve it; the natural
next one, not yet proved, is that `fun X ↦ X ~ ν` is convex, its fibres being the convex
`⌈X = v⌉`.

Restricting to `valuePost`-shaped `Q` does not dodge the condition either.  Collapsing
`𝒞⟨ν⟩ v; valuePost Y R` with `C_SKOLEM` and `C_ASSOC` lands at
`𝒞⟨joint⟩ (v, y); (⌈Y = y⌉ ∗ R y)`, and getting from there to a conditioning over `y` alone
is a marginalisation `𝒞⟨μ₀⟩ (v, w); K w ⊢ 𝒞⟨μ₀.map Prod.snd⟩ w; K w`, which is itself
refuted: at `μ₀` the product of `bernoulliWeights (1/2)` with a point mass, and `K _ := constQ X`,
it *is* `Convex (constQ X)`, which `not_convex_constQ` rules out.  Marginalisation holds
exactly when the fibre assertion is convex, so a `valuePost`-shaped `Q` is mixable precisely
when the values' assertions are.  (`CWPBindDist` sidesteps all of this: it reads the law of
the whole composite program off `CWPDist`, rather than sequencing anything.)

**2. A `run`-level bind lemma.**  Nothing in the development relates `run (C >>= F) μ₀` to
running `C` and then `F`: `LawfulBernoulliInterpretable.interp_bind` is a law about `interp`,
never about `bigStep`.  `bigStep` already takes a per-atom family of programs, so the
statement is expressible --

```
  run (C >>= F) μ₀ = bigStep (run C μ₀).1 (fun A ↦ interp (F ((run C μ₀).2 A)))
```

-- but the `toTree`/`fixpoint` composition theorem behind it is not.  It splits in two, and
the tape half is cheap: `runValue_bind` and `runPath_bind` are plain structural inductions
on the free monad and are proved.  What is left is (a) that running `p` refines a
footprint's atoms by `p`'s own paths, so that `footprintValue`/`footprintPath` compose the
way `runValue`/`runPath` do, and (b) the measure half -- `run_psp_mixture` says the space a
run lands in is the mixture of the spaces its reweighted runs land in, and it is stated for
one program; bind needs it for a per-atom family, which is the shape `bigStep` already
takes.  Three consequences are
what the proof actually consumes: `(run C μ₀).1.toSpace ≤ (run (C >>= F) μ₀).1.toSpace`;
each fibre's `run (F v) (BoundedFootprintPsp.reweight (run C μ₀).1 …)` landing inside the
matching reweighting of `run (C >>= F) μ₀`; and
`result (run (C >>= F) μ₀) = result (run (F v) …)` almost surely on `{result (run C μ₀) = v}`,
which is the equation `AEProper` exists to exploit.  The locality side additionally needs
`freshMs μ₀ (interp (F v)) ≤ freshMs μ₀ (interp (C >>= F))`, so that a fibre's locality bound
implies the one the conclusion asks for.  This is the one genuinely missing input: with it,
item 0's machinery plus `Convex` is the whole proof. -/

/-- **Sequencing, in conditioned form** -- the shape the mixing argument actually produces,
and the one `CWPBind` is a special case of.

`F` is run once per fibre of `C`'s law, so what comes back is one `Q v` per fibre, at the
reweighted ambient that fibre lives in.  Mixing them is not a *collapse*: a resource whose
fibres satisfy `Q v Y` is by definition a conditioning `𝒞⟨ν⟩ v; Q v Y`, and that is what the
conclusion records.  Nothing has to be recovered from the fibres, so there is no convexity
side condition here, and the postcondition may be genuinely value-indexed.  Compare
`CWPSwap`, whose conclusion has the same shape for the same reason.

`AEProper (Q v)` is still needed, and for the reason it was introduced: the fibre's `wp`
reports `F v`'s result as a random variable of that fibre, while the conclusion is about the
global result of `C >>= F`, and the two agree only almost surely on the fibre.

Not proved.  The one missing input is the `run`-level bind lemma of item 2 above; given it,
the mixing is `CWPSwap_core` with a per-fibre program family in place of the single `C`. -/
lemma CWPBindC {α β : Type} {m : Type → Type} [Monad m]
    [Interp.LawfulBernoulliInterpretable m] [Inhabited α] [Inhabited β]
    {C : m α} {F : α → m β} {Q : α → RV β → FProp}
    (hQ : ∀ v, AEProper (Q v)) :
    wp C (fun X ↦ valuePost X (fun v ↦ wp (F v) (Q v)))
      ⊢ wp (C >>= F) (fun Y ↦ iprop(∃ ν : PMF α, 𝒞⟨ν⟩ v; Q v Y)) := by
  sorry

/-- **Sequencing**, at the side conditions that make it survive `CWPBind_counterexample`.

This is `CWPBindC` at a postcondition that does not depend on `C`'s value, followed by the
one extra step that specialisation needs: collapsing `∃ ν, 𝒞⟨ν⟩ v; Q Y` back to `Q Y`.  That
step *is* `Convex`, which is why `AEProper` alone is refuted -- the counterexample attacks
the collapse, not the bind.

So the whole of what `CWPBind` asks beyond the general rule is `hC`, and it is discharged by
`convex_liftPred`, `convex_pure`, `convex_and`, `convex_forall` for the postconditions built
out of sure facts. -/
lemma CWPBind {α β : Type} {m : Type → Type} [Monad m]
    [Interp.LawfulBernoulliInterpretable m] [Inhabited α] [Inhabited β]
    {C : m α} {F : α → m β} {Q : RV β → FProp}
    (hQ : AEProper Q) (hC : ∀ X : RV β, Convex (Q X)) :
    wp C (fun X ↦ valuePost X (fun v ↦ wp (F v) Q)) ⊢ wp (C >>= F) Q :=
  entails_trans (CWPBindC (Q := fun _ ↦ Q) fun _ ↦ hQ)
    (WPCons fun Y ↦ exists_elim fun ν ↦ hC Y ν)

/-- The converse direction.  Iris proves both directions of `bind`, but its `wp` is a
fixpoint over the operational semantics, whereas this one quantifies over *every* ambient
footprint containing the resource.  So this direction asks for more than inverting a run:
from one run of `C >>= F` it has to manufacture a fibre resource that is a precondition for
`F v` in every possible future ambient, not just the one that run produced.

The locality clause does not change its status: it strengthens the premise, but it also
strengthens both `wp`s in the conclusion, including the fibre obligation `wp (F v) Q`, which
is the hard one.  So this stays open, blocked on the same missing `run`-level bind lemma as
the forward direction (item 2 above) -- and that is also why the two directions cannot be
merged into a single `⊣⊢` yet: the forward one is refuted at `AEProper` alone
(`CWPBind_biEntails_counterexample`) and only conjectural once `Convex` is added, while this
one has no proof and no counterexample.

It is not known to be false: the natural refutation takes
`Q := fun X ↦ X ~ ν` for a non-Dirac `ν`, which is `AEProper` by `aeProper_hasDistribution`
and holds of `flip half >>= pure` by `CWPFlip`, while each fibre would have to prove
`(fun _ ↦ v) ~ ν`; contradicting that fibre obligation means reading `wp` at an ambient
containing the fibre, and a conditioning's fibres are reweightings, so they do not sit below
the ambient they came from.  `BoundedFootprintPsp.reweight` together with the tilt machinery
(`reweight_rect`, `mixture_of_tilts`) should supply that ambient; nobody has carried it
out. -/
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
  refine ⟨⟨((B : PSpace Ω) : PSp Ω), hbf⟩, ?_, PSp.valid_def.mpr (Option.some_ne_none _),
    ?_, ?_⟩
  · show PSp.mul _ _ ≤ _
    rw [hC, hxy, hxys, BoundedFootprintPsp.toSpace_val, hpsp]
    exact WithTop.coe_le_coe.2 (PSpace.trim_le hsup)
  · -- the witness measures only the reported value, and that is part of the run's own
    -- randomness: `treeValue` factors through `footprintPath`
    refine le_trans ?_ (le_sup_right (a := msOf a))
    show (B : PSpace Ω).ms ≤ freshMs μ₀ (Interp.BernoulliInterpretable.interp t)
    rw [hBdef]
    show BX ≤ _
    rw [hBXdef, hX, treeValue_toTree, interp_bernoulliM]
    exact comap_footprintValue_le_freshMs μ₀ t
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

/-! ### Why `AEProper` is not enough for sequencing

The witness that the sequencing rule stated above is unsound.  Everything here is about one
program -- a single fair coin -- and one postcondition. -/

/-- **"The result is almost surely a constant."**  `AEProper`, but not mixable: it holds on
each fibre of a coin and fails on the coin. -/
noncomputable def constQ : RV Bool → FProp := fun X ↦ iprop(⌈X = true⌉ ∨ ⌈X = false⌉)

/-- `constQ` cannot tell almost-surely-equal results apart: distribute `∗` over `∨` and
substitute the sure equality in each disjunct. -/
lemma aeProper_constQ : AEProper constQ := fun _ _ ↦
  entails_trans sep_or_left.1
    (or_elim (entails_trans liftPred_subst or_intro_l)
      (entails_trans liftPred_subst or_intro_r))

/-- A constant result is surely constant, for free. -/
lemma constQ_const (v : Bool) : ⊢ constQ (fun _ ↦ v) := by
  cases v
  · exact entails_trans (liftPred_of_forall (a := fun _ : Ω ↦ (false : Bool) = false)
      (fun _ ↦ rfl)) or_intro_r
  · exact entails_trans (liftPred_of_forall (a := fun _ : Ω ↦ (true : Bool) = true)
      (fun _ ↦ rfl)) or_intro_l

/-- Every fibre of the bind discharges `constQ` outright: `pure v` reports the constant `v`,
which is surely constant. -/
lemma wp_pure_constQ (v : Bool) : ⊢ wp (pure v : Interp.BernoulliM Bool) constQ :=
  entails_trans (constQ_const v) CWPPure

/-- So the whole premise of the sequencing rule is available for free: the coin has a law
(`CWPFlip`), conditioning on it is a `valuePost` (`valuePost_of_law`), and each fibre's
postcondition costs nothing. -/
lemma wp_flip_valuePost :
    ⊢ wp (Interp.flip Interp.half)
        (fun X ↦ valuePost X (fun v ↦ wp (pure v : Interp.BernoulliM Bool) constQ)) :=
  entails_trans CWPFlip (WPCons fun _ ↦ valuePost_of_law fun v ↦ wp_pure_constQ v)

lemma toNNReal_half_ne_zero : unitInterval.toNNReal Interp.half ≠ 0 := by
  intro h
  have hc : ((unitInterval.toNNReal Interp.half : NNReal) : ℝ) = 0 := by rw [h]; simp
  rw [unitInterval.coe_toNNReal] at hc
  norm_num [Interp.half] at hc

lemma toNNReal_half_ne_one : unitInterval.toNNReal Interp.half ≠ 1 := by
  intro h
  have hc : ((unitInterval.toNNReal Interp.half : NNReal) : ℝ) = 1 := by rw [h]; simp
  rw [unitInterval.coe_toNNReal] at hc
  norm_num [Interp.half] at hc

/-- A nondegenerate coin is not a point mass. -/
lemma delta_ne_bernoulli (v : Bool) {r : NNReal} {hr : r ≤ 1} (h0 : r ≠ 0) (h1 : r ≠ 1) :
    (δ v : PMF Bool) ≠ bernoulliWeights r hr := by
  intro h
  cases v
  · have hm : true ∈ (bernoulliWeights r hr).support := mem_support_bernoulliWeights_true h0
    rw [← h] at hm
    simp [δ] at hm
  · have hm : false ∈ (bernoulliWeights r hr).support := mem_support_bernoulliWeights_false h1
    rw [← h] at hm
    simp [δ] at hm

/-- **`constQ` is `AEProper` but not convex**, and that is exactly the gap
`CWPBind_counterexample` walks through: the fair coin's law splits into two fibres, on each
of which the result is surely a constant, while on the coin itself it is surely neither. -/
theorem not_convex_constQ : ¬ ∀ X : RV Bool, Convex (constQ X) := by
  intro hconv
  have hemp : (1 : BoundedFootprintSpace Bool) ∈ (UpperSetBI.emp :
      UpperSet (BoundedFootprintSpace Bool)) := by
    show (1 : BoundedFootprintSpace Bool) ≤ 1
    exact le_refl 1
  have hv1 : ✓(1 : BoundedFootprintPsp).psp := BoundedFootprintPsp.valid_one
  have hle1 : (1 : BoundedFootprintSpace Bool) * 1 ≤ (1 : BoundedFootprintPsp).toSpace := by
    rw [mul_one]; exact le_refl _
  obtain ⟨b, hb₁, hb₂, -, hb₃⟩ := (CWPFlip (p := Interp.half)) 1 valid_one hemp 1 1 hv1 hle1
  have hvS := valid_run (Interp.flip Interp.half) (1 : BoundedFootprintPsp) hv1
  have hbS : b ≤ (run (Interp.flip Interp.half) (1 : BoundedFootprintPsp)).1.toSpace := by
    have h := hb₁; rwa [mul_one] at h
  have hlaw := hb₃ _ hvS hbS
  -- on the fibre at `v` the result is surely `v`, hence surely a constant
  have hstep : ∀ v : Bool,
      (⌈result (run (Interp.flip Interp.half) (1 : BoundedFootprintPsp)) = v⌉ : FProp)
        ⊢ constQ (result (run (Interp.flip Interp.half) (1 : BoundedFootprintPsp))) := by
    intro v
    cases v
    · exact or_intro_r
    · exact or_intro_l
  have hcond := C_CONS hstep _ hvS (C_UNIT_R.1 _ hvS hlaw)
  rcases hconv _ _ _ hvS hcond with h1 | h1
  · exact delta_ne_bernoulli true toNNReal_half_ne_zero toNNReal_half_ne_one
      (EDistInj _ hvS ⟨SURE_DIRAC.2 _ hvS h1, hlaw⟩)
  · exact delta_ne_bernoulli false toNNReal_half_ne_zero toNNReal_half_ne_one
      (EDistInj _ hvS ⟨SURE_DIRAC.2 _ hvS h1, hlaw⟩)

/-- **Sequencing is unsound at `AEProper`.**  Take `C := flip half`, `F := pure` (so that
`C >>= F = C`) and `Q := constQ`.  The premise holds outright (`wp_flip_valuePost`), so the
rule would give `⊢ wp (flip half) constQ`; reading that at the unit ambient produces a
resource below the run's space on which the coin is surely `true` or surely `false`, while
`CWPFlip` makes that same run's space give the coin the law `bernoulliWeights (1/2)`.
`EDistInj` then equates a point mass with a fair coin. -/
theorem CWPBind_counterexample :
    ¬ ∀ {α β : Type} {m : Type → Type} [Monad m] [Interp.LawfulBernoulliInterpretable m]
        [Inhabited α] [Inhabited β] {C : m α} {F : α → m β} {Q : RV β → FProp},
        AEProper Q → wp C (fun X ↦ valuePost X (fun v ↦ wp (F v) Q)) ⊢ wp (C >>= F) Q := by
  intro hbind
  have hbad : ⊢ wp (Interp.flip Interp.half >>= (pure : Bool → Interp.BernoulliM Bool)) constQ :=
    entails_trans wp_flip_valuePost (hbind aeProper_constQ)
  rw [bind_pure] at hbad
  have hemp : (1 : BoundedFootprintSpace Bool) ∈ (UpperSetBI.emp :
      UpperSet (BoundedFootprintSpace Bool)) := by
    show (1 : BoundedFootprintSpace Bool) ≤ 1
    exact le_refl 1
  have hv1 : ✓(1 : BoundedFootprintPsp).psp := BoundedFootprintPsp.valid_one
  have hle1 : (1 : BoundedFootprintSpace Bool) * 1 ≤ (1 : BoundedFootprintPsp).toSpace := by
    rw [mul_one]; exact le_refl _
  obtain ⟨b, hb₁, hb₂, -, hb₃⟩ := hbad 1 valid_one hemp 1 1 hv1 hle1
  obtain ⟨b', hb'₁, hb'₂, -, hb'₃⟩ :=
    (CWPFlip (p := Interp.half)) 1 valid_one hemp 1 1 hv1 hle1
  have hvS := valid_run (Interp.flip Interp.half) (1 : BoundedFootprintPsp) hv1
  have hbS : b ≤ (run (Interp.flip Interp.half) (1 : BoundedFootprintPsp)).1.toSpace := by
    have h := hb₁; rwa [mul_one] at h
  have hb'S : b' ≤ (run (Interp.flip Interp.half) (1 : BoundedFootprintPsp)).1.toSpace := by
    have h := hb'₁; rwa [mul_one] at h
  have h2 := hb'₃ _ hvS hb'S
  rcases hb₃ _ hvS hbS with h1 | h1
  · exact delta_ne_bernoulli true toNNReal_half_ne_zero toNNReal_half_ne_one
      (EDistInj _ hvS ⟨SURE_DIRAC.2 _ hvS h1, h2⟩)
  · exact delta_ne_bernoulli false toNNReal_half_ne_zero toNNReal_half_ne_one
      (EDistInj _ hvS ⟨SURE_DIRAC.2 _ hvS h1, h2⟩)

/-- **The two sequencing directions cannot be packaged as one bi-entailment**: a `⊣⊢` would
give the direction `CWPBind_counterexample` refutes. -/
theorem CWPBind_biEntails_counterexample :
    ¬ ∀ {α β : Type} {m : Type → Type} [Monad m] [Interp.LawfulBernoulliInterpretable m]
        [Inhabited α] [Inhabited β] {C : m α} {F : α → m β} {Q : RV β → FProp},
        AEProper Q → (wp C (fun X ↦ valuePost X (fun v ↦ wp (F v) Q)) ⊣⊢ wp (C >>= F) Q) :=
  fun h ↦ CWPBind_counterexample fun hQ ↦ (h hQ).1

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
