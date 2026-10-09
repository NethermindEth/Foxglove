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

-- TODO(check) - I put ⊤ to silence the measurability for Lean's Kernel thing :sweat_smile:
abbrev _root_.ProbabilityTheory.TrivialMarkovKernel (A : Type) (p : PSpace Ω) : Type :=
  {κ : @Kernel A Ω ⊤ p.ms // IsMarkovKernel κ}

def _root_.ProbabilityTheory.Kernel.toPSpace {A : Type} {p : PSpace Ω}
  (κ : TrivialMarkovKernel A p) : A → PSpace Ω :=
  fun a ↦ ⟨⟨p.ms, κ.1 a⟩, have := κ.2; inferInstance⟩

instance {A : Type} {p : PSpace Ω} : FunLike (TrivialMarkovKernel A p) A (PSpace Ω) :=
  ⟨
    fun κ a ↦ ⟨⟨p.ms, κ.1 a⟩, have := κ.2; inferInstance⟩,
    by intros κ a₂ f
       erw [funext_iff] at f
       aesop
  ⟩

def _root_.PMF.toMeasureWithMs {A : Type} (μ : PMF A) (ms : MeasurableSpace A) : @MeasureTheory.Measure A ms :=
  @μ.toMeasure A ms

-- open MeasureTheory in
-- structure CompatibleKernel (A : Type*) (m : ValidIndexedPSpPm I Var Val) where
--   kernel : (i : I) → A → @Measure (Var → Val) (m.ms i)
--   isProb : ∀ (i : I) (a : A), IsProbabilityMeasure (kernel i a)
--   isComp : ∀ (i : I) (a : A), PSpace.compatiblePerm ⟨⟨m.ms i, kernel i a⟩, isProb i a⟩ (m.perm i)

-- def jointConditioning {A Var Val : Type*}
--   [DecidableEq Var] [Inhabited Val] [Finite Var] [Countable Val]
--   (μ : PMF A) (K : A → bProp I Var Val)
--   : bProp I Var Val :=
--   iprop(
--     ∃ m : ValidIndexedPSpPm I Var Val, -- `μ = m.toPSpace.μ`
--     ∃ κ : CompatibleKernel A m,
--       own m.val
--         ∗ (∀ (i : I), ⌜m.μ i = Measure.bind (mα := ⊤) (mβ := m.ms i) μ (κ.kernel i)⌝)
--         ∗
--           (
--             ∀ (v : μ.support),
--               (
--                 own (fun i => ⟨⟨some ⟨⟨m.ms i, κ.kernel i v⟩, κ.isProb i v⟩, m.perm i⟩, κ.isComp i v⟩) -∗
--                   (K v))
--           )
--   )

def own {M} [OrderedUnitalResourceAlgebra M] (b : M) : OURAProp M := Quotient.mk _ (UpperSetBI.own b)

def jointConditioning {A : Type} (μ : PMF A) (K : A → OURAProp PSpΩ) : OURAProp PSpΩ :=
  iprop(
    ∃ m : PSpace Ω,
    ∃ κ : TrivialMarkovKernel A m,
      own m ∗
      ⌜m.μ = (μ.toMeasureWithMs ⊤).bind κ⌝ ∗
      ∀ v : μ.support,
        own (some ⟨⟨m.ms, _⟩, _⟩) -∗ (K v)
  )

notation "𝒞" "⟨" μ "⟩" v ";" K => jointConditioning μ (fun v => iprop(K))

end

end

end Foxglove
