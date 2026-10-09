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

instance : Iris.BI (UpperSetBI.OURAProp PSpΩ) := inferInstance

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

def jointConditioning {A : Type} (μ : PMF A) (K : A → OURAProp PSpΩ) : OURAProp PSpΩ :=
  iprop(
    ∃ m : PSpace Ω,
    ∃ κ : TrivialMarkovKernel A m,
      own m ∗
      ⌜m.μ = (μ.toMeasureWithMs ⊤).bind κ⌝ ∗
      ∀ v : μ.support, own (κ v) -∗ (K v)
  )

notation "𝒞" "⟨" μ "⟩" v ";" K => jointConditioning μ (fun v => iprop(K))

end

end

end Foxglove
