module

public import Foxglove.Rules.Sure

@[expose] public section
namespace Foxglove

open ProbSpace
open Iris OrderedUnitalResourceAlgebra
open UpperSetBI
open Iris BI UpperSetBI OURAProp

noncomputable section

/-! # Laws

What `E ~ μ` satisfies beyond the rules: a Dirac law is a sure fact. -/

/-- Having the law `δ v` is being surely `v`. -/
theorem hasDistribution_dirac {α : Type} {E : RV α} {v : α} :
    (E ~ δ v) = ⌈fun ρ ↦ E ρ = v⌉ :=
  ownP_pure_congr fun P ↦ law_dirac_iff P

/-- A sure fact is a Dirac law at `True`. -/
theorem very_sure {E : Ω → Prop} : E ~ δ True ⊣⊢ ⌈E⌉ := by
  have h : (⌈E⌉ : FProp) = ⌈E = True⌉ := by
    congr 1
    funext ω
    simp [LiftUnary.lift, LiftBinary.lift]
  rw [h, hasDistribution_dirac]
  exact ⟨entails_rfl, entails_rfl⟩

end

end Foxglove
