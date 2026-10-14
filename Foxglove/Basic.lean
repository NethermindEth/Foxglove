module

public import Foxglove.MeasureOnSpace
public import Foxglove.OURA


@[expose] public section
namespace Foxglove

open ProbSpace

abbrev RId : Type := ℕ

abbrev Ω : Type := RId → Bool

abbrev PSpΩ := PSp Ω

/-- `Ω` is the tapes of coin flips; `ValidPSp`, `BoundedFootprintPsp` and friends are the
general constructions of `MeasureOnSpace`, instantiated at `α := Bool`. -/
abbrev ValidPSpΩ : Type := ValidPSp Ω

abbrev FProp := Iris.UpperSetBI.OURAProp (BoundedFootprintSpace Bool)

abbrev RV (α : Type) := Ω → α

open Iris OrderedUnitalResourceAlgebra

-- instance : FunLike ABprop PSpΩ Prop where
--   coe := fun P ↦ P.holds
--   coe_injective {P Q h} := by aesop

noncomputable section

attribute [local aesop simp] Equivalence.refl Equivalence.trans Equivalence.symm

instance : OrderedUnitalResourceAlgebra PSpΩ := inferInstance

instance : Iris.CMRA PSpΩ := inferInstance

instance : Iris.UCMRA PSpΩ := inferInstance

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

def _root_.PMF.toMeasureWithMs {A : Type} (μ : PMF A) (ms : MeasurableSpace A) : @MeasureTheory.Measure A ms :=
  @μ.toMeasure A ms

def own {M} [OrderedUnitalResourceAlgebra M] (b : M) : OURAProp M := UpperSetBI.own b

-- def jointConditioning {A : Type} (μ : PMF A) (K : A → FProp) : FProp :=
--   iprop(
--     ∃ m : PSpace Ω,
--     ∃ κ : TrivialMarkovKernel A m,
--       own m ∗
--       ⌜m.μ = (μ.toMeasureWithMs ⊤).bind κ⌝ ∗
--       ∀ v : μ.support, own (κ v) -∗ K v
--   )

-- notation "𝒞" "⟨" μ "⟩" v ";" K => jointConditioning μ (fun v => iprop(K))

-- def almostMeasurable {A Ω : Type} (E : Ω → A) (P : PSp Ω) : Prop :=
--   match P with
--   | none => False
--   | some p => @AEMeasurable Ω A ⊤ _ E p.1.μ

-- def hasDistribution {A : Type} (E : Ω → A) (μ : PMF A) : FProp :=
--   iprop(
--     ∃ P : PSpace Ω,
--       own P ∗
--       ⌜
--         have Eμ := @P.μ.map Ω A P.ms ⊤ E
--         almostMeasurable E P ∧ Eμ = μ.toMeasureWithMs ⊤
--       ⌝
--   )

-- notation:100 E:100 "⟨" i:100 "⟩" " ~ " p:100 => hasDistribution E i p

def liftPred (a : Ω → Prop) : FProp := sorry
  -- set of probability spaces, where the prob of prop = true ≃ 1

-- def wp {Var Val : Type*}
--   [DecidableEq Var] [Inhabited Val] [Finite Var] [Countable Val]
--   (t : IndexedPSpPm I Var Val → IndexedPSpPm I Var Val)
--   (Q : bProp I Var Val) : bProp I Var Val := {
--   carrier := fun a =>
--     ∀ μ₀ : IndexedPSpPm I Var Val,
--       ∀ c : IndexedPSpPm I Var Val,
--         ✓ μ₀ → (a * c) ≤ μ₀ → ∃ b : IndexedPSpPm I Var Val,
--           (b * c) ≤ t μ₀ ∧ ✓ b ∧ Q b
--   upper' := by
--     intro x y hxy hx μ₀ c hvμ₀ hmul
--     exact hx μ₀ c hvμ₀ (le_trans (mul_left_mono hxy) hmul)
-- }

end

end

section

open Iris BI UpperSetBI OURAProp

noncomputable def ftrue : FProp := fmk UpperSetBI.true

noncomputable def ffalse : FProp := fmk UpperSetBI.false

variable {P Q R : FProp}

attribute [grind .] and_intro entails_rfl pure_intro or_intro_l or_intro_r or_elim
                    Iris.BI.BIBase.pure and_elim_l and_elim_r Iris.BI.BIBase.BiEntails.mk

attribute [grind cases] Iris.BI.BIBase.BiEntails

attribute [grind →] entails_trans

@[simp, grind .]
lemma entails_ftrue : P ⊢ ftrue := pure_intro True.intro

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
lemma fals_entails : ffalse ⊢ P := by
  apply pure_elim'
  grind

@[simp, grind .]
theorem or_ident : P ∨ ffalse ⊣⊢ P := by
  grind

@[simp, grind .]
theorem or_comm : P ∨ Q ⊣⊢ Q ∨ P := by
  grind

theorem or_assoc : (P ∨ Q) ∨ R ⊣⊢ P ∨ (Q ∨ R) := by
  sorry

-- theorem sep_ident {P : bProp I Var Val}
--   : P ∗ True ⊣⊢ P := by
--   refine ⟨?_, ?_⟩
--   · iintro ⟨h, _⟩
--     iexact h
--   · iintro h
--     isplitl [h]
--     · iexact h
--     · exact fun m a a_1 => a_1

-- theorem sep_comm {P Q : bProp I Var Val}
--   : P ∗ Q ⊣⊢ Q ∗ P := by
--   constructor
--   · intro m hv hm
--     obtain ⟨b₁, ⟨b₂, h⟩⟩ := hm
--     use b₂, b₁
--     have : b₁ * b₂ = b₂ * b₁ := CommMonoid.mul_comm b₁ b₂
--     aesop
--   · intro m hv hm
--     obtain ⟨b₁, ⟨b₂, h⟩⟩ := hm
--     use b₂, b₁
--     have : b₁ * b₂ = b₂ * b₁ := CommMonoid.mul_comm b₁ b₂
--     aesop

-- theorem sep_assoc {P Q R : bProp I Var Val}
--   : (P ∗ Q) ∗ R ⊣⊢ P ∗ (Q ∗ R) := by
--   constructor
--   · intro m _ hm
--     obtain ⟨b₁, b₂, hle, ⟨c₁, c₂, hle', hPc₁, hQc₂⟩, hRb₂⟩ := hm
--     refine ⟨c₁, c₂ * b₂, ?_, hPc₁, c₂, b₂, le_refl _, hQc₂, hRb₂⟩
--     calc c₁ * (c₂ * b₂)
--         = (c₁ * c₂) * b₂ := (mul_assoc c₁ c₂ b₂).symm
--       _ ≤ b₁ * b₂ := mul_left_mono hle'
--       _ ≤ m := hle
--   · intro m _ hm
--     obtain ⟨b₁, b₂, hle, hPb₁, ⟨c₁, c₂, hle', hQc₁, hRc₂⟩⟩ := hm
--     refine ⟨b₁ * c₁, c₂, ?_, ⟨b₁, c₁, le_refl _, hPb₁, hQc₁⟩, hRc₂⟩
--     calc (b₁ * c₁) * c₂
--         = b₁ * (c₁ * c₂) := mul_assoc b₁ c₁ c₂
--       _ ≤ b₁ * b₂ := by
--           rw [mul_comm b₁ (c₁ * c₂), mul_comm b₁ b₂]
--           exact mul_left_mono hle'
--       _ ≤ m := hle

-- variable [Finite Var] [Countable Val]

-- example {P : bProp I Var Val} : ⊢ P -∗ BTrue := by
--   exact Iris.BI.entails_wand fun m a a_1 => trivial

-- omit [Finite Var] [Countable Val]
-- lemma emp_implies_own_unit : emp ⊢ own (1 : IndexedPSpPm I Var Val) := by
--   intro m hv hemp
--   have : m ∈ {a | 1 ≤ a} := by
--     have : 1 ≤ m := IndexedPSpPm.one_le I Val Var
--     aesop
--   assumption

-- lemma true_subst_star
--   {P Q : bProp I Var Val} (h : Q ⊣⊢ BTrue)
--   : P ⊢ P ∗ Q := by
--   intro m hv hp
--   simp [Iris.BI.sep]
--   have : m ∈ sep P Q := by
--     simp [Membership.mem, Set.Mem, sep]
--     use m, 1
--     have : Q 1 := by
--       have : 1 ∈ (BTrue : bProp I Var Val) := by
--         simp [Membership.mem, Set.Mem, BTrue]
--         trivial
--       have := h.2 1 (by aesop) this
--       assumption
--     constructor
--     · have : m * 1 = m := MulOneClass.mul_one m
--       rw [this]
--     · exact ⟨hp, by assumption⟩
--   assumption

-- noncomputable instance : OfNat (ValidIndexedPSpPm I Var Val) 1 where
--   ofNat := ⟨1, by aesop⟩

-- noncomputable def validOne : ValidIndexedPSpPm I Var Val := 1

-- noncomputable def k {A : Type*} : CompatibleKernel A (@validOne I Var Val _ _) := {
--   kernel := fun i _ => PSpace.unit.1.μ
--   isProb := fun i a => by
--     have := (@validOne.PSpace I Var Val _ _ i).2
--     assumption
--   isComp := by
--     intro i a
--     cases h : (@validOne I Var Val _ _).1 i
--     obtain ⟨p, h⟩ := h
--     aesop
-- }

-- lemma C_True
--   {I Var Val A : Type*} [DecidableEq Var] [Inhabited Val]
--   [Finite Var] [Countable Val] {μ : PMF A}
--   : ⊢ (𝒞⟨μ⟩ _v; BTrue : bProp I Var Val) := by
--   unfold jointConditioning
--   iexists 1, k
--   isplitl
--   · intro m _ _ i
--     have := @IndexedPSpPm.one_le I Val Var _ _ m i
--     trivial
--   · isplitl
--     · apply Iris.BI.forall_intro
--       intro i _ _ _
--       have : (@ValidIndexedPSpPm.μ I Var Val _ _) 1 i
--         = (1 : MeasureOnSpace (Var → Val)).μ := by rfl
--       rw [this]
--       let k' (v : A) := (k.kernel i v : @Measure (Var → Val) ⊥)
--       have {v : A} : k' v = (1 : MeasureOnSpace (Var → Val)).μ := by rfl
--       have : (@μ.toMeasure A ⊤).bind k' = MeasureOnSpace.μ 1 := by aesop
--       rw [this]
--       trivial
--     · apply Iris.BI.forall_intro
--       intro v _ _ _ _ _ _
--       trivial

-- lemma sep_affine
--   {P Q : bProp I Var Val}
--   : P ∗ Q ⊢ P := by
--   iintro ⟨h1, h2⟩
--   iexact h1

-- end Properties

end

end Foxglove
