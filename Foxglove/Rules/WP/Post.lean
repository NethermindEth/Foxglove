module

public import Foxglove.Rules

@[expose] public section
namespace Foxglove

open ProbSpace
open Iris OrderedUnitalResourceAlgebra
open UpperSetBI
open Iris BI UpperSetBI OURAProp

noncomputable section

/-! # Postconditions

Discharging the side conditions of the `wp` rules: which postconditions are `AEProper`, which
are `Convex`, and what `valuePost` satisfies in the logic. -/

/-- Sure facts are convex: `SURE_CONVEX` in the shape `Convex` wants. -/
lemma convex_liftPred {E : RV Prop} : Convex ⌈E⌉ := fun _ ↦ SURE_CONVEX

/-- Laws are convex: `DIST_CONVEX`. -/
lemma convex_hasDistribution {α : Type} {X : RV α} (ν : PMF α) : Convex (X ~ ν) :=
  fun _ ↦ DIST_CONVEX

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

/-- Convexity transfers along bi-entailment. -/
lemma convex_congr {P R : FProp} (h : P ⊣⊢ R) (hR : Convex R) : Convex P :=
  fun ν ↦ entails_trans (C_CONS fun _ ↦ h.1) (entails_trans (hR ν) h.2)

/-- `∗` does not preserve convexity in general (a mixture of independent products need not be
one), but it does on separated sure facts, which `SURE_MERGE` turns into a single sure fact. -/
lemma convex_liftPred_sep {E E' : RV Prop} : Convex iprop(⌈E⌉ ∗ ⌈E'⌉) :=
  convex_congr SURE_MERGE convex_liftPred

/-- Value-indexed postconditions are automatically proper: they only look at the result
through `⌈X = x⌉`, and sure equalities substitute (`liftPred_subst`).  So `WP_BIND`'s side
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

/-- Having a given law is `AEProper`: `DISTR_SUBST`. -/
lemma aeProper_hasDistribution {α : Type} (ν : PMF α) : AEProper (fun X ↦ X ~ ν) :=
  fun _ _ ↦ entails_trans Iris.BI.sep_comm.1 DISTR_SUBST

/-- `valuePost` is monotone in the postcondition: weaken every fibre under the conditioning.
This is what lets a `wp` rule be applied *inside* a `valuePost`, through `WP_CONS`. -/
lemma valuePost_mono {α : Type} {X : RV α} {Q Q' : α → FProp} (h : ∀ x, Q x ⊢ Q' x) :
    valuePost X Q ⊢ valuePost X Q' :=
  exists_mono fun _ ↦ C_CONS fun x ↦ sep_mono_right (h x)

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

end

end Foxglove
