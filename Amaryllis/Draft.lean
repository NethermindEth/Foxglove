import Amaryllis.MeasureOnSpace
import Iris
namespace Model

@[reducible]
def ms₁ : MeasurableSpace (ℕ → Bool) := (MeasurableSpace.mk (λ s ↦ (s = ∅ ∨ s = Set.univ)) (by aesop)
            (by intros f hf
                cases hf
                case inl h₁ => rw [h₁]
                               right
                               exact Set.compl_empty                     
                case inr h₂ => rw [h₂]
                               left                     
                               exact Set.compl_univ
              )
            (by sorry))

noncomputable def One : PSp (ℕ → Bool) := .some {
  val := {
    ms := ms₁
    μ := (
      @MeasureTheory.Measure.mk 
      (ℕ → Bool) ms₁
      (
        MeasureTheory.OuterMeasure.mk
          (λ f ↦ if f = Set.univ then 1 else 0)
          ((by simp_all only [ite_eq_right_iff, one_ne_zero, imp_false]
               apply Aesop.BuiltinRules.not_intro
               intro a
               
               have elem : (ℕ → Bool) := (λ _ ↦ false)
               have helem : {elem} ⊆ Set.univ := by simp
               rw [←a] at helem
               apply Set.subset_empty_iff.1 at helem
               simp only [Set.singleton_ne_empty] at helem                   
               ))
          (by intros s₁ s₂ hs
              split
              next h =>
                subst h
                split
                next h =>
                  subst h
                  simp_all only [Std.le_refl]
                next h =>
                  simp_all only [nonpos_iff_eq_zero, one_ne_zero]
                  apply Set.univ_subset_iff.1 at hs
                  contradiction
              next h => simp_all only [zero_le]
          ) (by sorry)
      )
      (by sorry)
      (by sorry)
    )
  }
  property := MeasureTheory.IsProbabilityMeasure.mk 
                (by unfold DFunLike.coe
                    unfold MeasureTheory.Measure.instFunLike
                    unfold MeasureTheory.Measure.toOuterMeasure
                    aesop
                    )
}

instance : Inhabited (ℕ → Bool) := {
  default := (λ _ ↦ true)
}

open PSp
open ProbabilityTheory MeasureTheory
open PSpace


noncomputable instance : OrderedUnitalResourceAlgebra (PSp (ℕ → Bool)) := {
  mul := PSp.mul
  mul_assoc := (by unfold HMul.hMul instHMul Mul.mul; apply PSp.mul_assoc)
  one := One
  one_mul := (by sorry)
  mul_one := (by sorry)
  mul_comm := (by unfold HMul.hMul instHMul Mul.mul; apply PSp.mul_comm)
  valid P := P.isSome
  le p₁ p₂ := match p₁, p₂ with
              | .some p₁', .some p₂' => p₁' ≤ p₂'
              | .some _, .none => True
              | .none, .some _ => False
              | .none, .none => True
  le_refl := (by aesop)
  le_trans := (by grind)
  elim := (by sorry)
  valid_one := (by aesop)
  valid_mono := (by aesop)
  valid_mul := (by intros a b
                   unfold HMul.hMul instHMul Mul.mul
                   aesop)
  lt_iff_le_not_ge := (by unfold WithTop.instPreorder WithTop.instLE LT.lt
                          simp
                          unfold WithTop.instLT
                          simp
                          intros a b
                          apply Iff.intro
                          · intro h
                            cases h with
                            | bot_lt h => simp
                            | coe_lt_coe h => aesop
                          · intro h
                            cases a
                            · cases b
                              · aesop
                              · aesop
                            · cases b
                              · apply WithBot.bot_lt_coe
                              · simp at h
                                rename_i p₁ p₂
                                sorry)
}
