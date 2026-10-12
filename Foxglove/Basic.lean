module

public import Foxglove.MeasureOnSpace
public import Foxglove.OURA


@[expose] public section
namespace Foxglove

open ProbSpace

abbrev RId : Type := ℕ

abbrev Ω : Type := RId → Bool

abbrev PSpΩ := PSp Ω

abbrev ValidPSpΩ : Type := {psp : PSpΩ // ✓psp}

@[grind =]
lemma valid_def {psp : PSpΩ} : ✓psp ↔ psp ≠ (⊤ : PSpΩ) := by rfl

@[grind norm]
lemma top_def : (⊤ : PSpΩ) = .none := rfl

abbrev FProp := Iris.UpperSetBI.OURAProp PSpΩ

namespace ValidPSpΩ

def toPSpace (vpsp : ValidPSpΩ) : PSpace Ω :=
  vpsp.1.get (by rcases vpsp with ⟨val, h⟩
                 have : val ≠ .none := by grind
                 erw [Option.ne_none_iff_isSome] at this
                 exact this)

end ValidPSpΩ

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

def own {M} [OrderedUnitalResourceAlgebra M] (b : M) : OURAProp M := Quotient.mk _ (UpperSetBI.own b)

def jointConditioning {A : Type} (μ : PMF A) (K : A → FProp) : FProp :=
  iprop(
    ∃ m : PSpace Ω,
    ∃ κ : TrivialMarkovKernel A m,
      own m ∗
      ⌜m.μ = (μ.toMeasureWithMs ⊤).bind κ⌝ ∗
      ∀ v : μ.support, own (κ v) -∗ K v
  )

notation "𝒞" "⟨" μ "⟩" v ";" K => jointConditioning μ (fun v => iprop(K))

def almostMeasurable {A Ω : Type} (E : Ω → A) (P : PSp Ω) : Prop :=
  match P with
  | none => False
  | some p => @AEMeasurable Ω A ⊤ _ E p.1.μ

def hasDistribution {A : Type} (E : Ω → A) (μ : PMF A) : FProp :=
  iprop(
    ∃ P : PSpace Ω,
      own P ∗
      ⌜
        have Eμ := @P.μ.map Ω A P.ms ⊤ E
        almostMeasurable E P ∧ Eμ = μ.toMeasureWithMs ⊤
      ⌝
  )

notation:100 E:100 "⟨" i:100 "⟩" " ~ " p:100 => hasDistribution E i p

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

-- lemma abc {P Q : }: 

end

end Foxglove
