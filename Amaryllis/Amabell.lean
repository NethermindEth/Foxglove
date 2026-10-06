-- import Mathlib.Data.Nat.Basic
-- import Mathlib.Data.Finmap

-- import Amaryllis.MeasureOnSpace

-- namespace Amaryllis

-- abbrev RId : Type := Nat

-- abbrev Ω : Type := Finmap fun (_ : RId) ↦ Bool

-- abbrev PSpΩ := PSp Ω

-- abbrev RV (α : Type) := Ω → α

-- abbrev ABprop := UpperSet PSpΩ

-- instance : FunLike ABprop PSpΩ Prop where
--   coe := fun P ↦ P.carrier
--   coe_injective {P Q h} := by aesop

-- section

-- attribute [local aesop unsafe cases] UpperSet OrderedUnitalResourceAlgebra

-- def true : ABprop :=
--   {
--     carrier := Set.univ
--     upper' := by aesop
--   }

-- def entail (P Q : ABprop) : Prop :=
--   ∀ (m : PSpΩ), ✓m → P m → Q m

-- def bientail (P Q : ABprop) : Prop :=
--   entail P Q ∧ entail Q P

-- def lift (φ : Prop) : ABprop :=
--   {
--     carrier := {x | φ}
--     upper' := by aesop
--   }

-- def and (P Q : ABprop) : ABprop :=
--   {
--     carrier := {a | P a ∧ Q a}
--     upper' := by aesop
--   }

-- def or (P Q : ABprop) : ABprop :=
--   {
--     carrier := {a | P a ∨ Q a}
--     upper' := by aesop      
--   }

-- def imp (P Q : ABprop) : ABprop :=
--   {
--     carrier := {a | ∀ b, a ≤ b → ✓b → P b → Q b}
--     upper' {a : PSpΩ} := by grind
--   }

-- def sForall (Ψ : ABprop → Prop) : ABprop :=
--   {
--     carrier := {a | ∀ p, Ψ p → p a}
--     upper' {_ _ h₁ _ p _} := p.upper' h₁ (by aesop)
--   }

-- def sExists (Ψ : ABprop → Prop) : ABprop := {
--   carrier := {a | ∃ p, Ψ p ∧ p a}
--   upper' := by aesop
-- }

-- def sep (P Q : ABprop) : ABprop :=
--   {
--     carrier := {a | ∃ (b₁ b₂ : PSpΩ), (b₁ * b₂) ≤ a ∧ P b₁ ∧ Q b₂}
--     upper' {a : PSpΩ} := by grind
--   }

-- def wand (P Q : ABprop) : ABprop :=
--   {
--     carrier := {a | ∀ b, ✓(a * b) → P b → Q (a * b)}
--     upper' {_ _ h₁ h₂ b h₃ h₄} :=
--       have := mul_left_mono h₁
--       Q.upper' this (h₂ b (valid_mono this h₃) h₄)
--   }

-- def persistently (P : ABprop) : ABprop :=
--   {
--     carrier := {_a | P 1}
--     upper' {a : PSpΩ} := by grind
--   }

-- end

-- section

-- @[simp, grind .]
-- lemma refl_entail : Std.Refl entail := ⟨by simp [entail]⟩

-- @[simp, grind .]
-- lemma trans_entail : IsTrans _ entail := ⟨by grind [entail]⟩

-- @[simp, grind .]
-- lemma refl_entail' {P} : entail P P := refl_entail.refl _

-- @[simp, grind .]
-- lemma trans_entail' {P Q R} : entail P Q → entail Q R → entail P R :=
--   trans_entail.trans _ _ _

-- @[simp, grind .]
-- lemma antisymm_entail' {P Q} : entail P Q → entail Q P → P = Q := by
--   unfold entail
--   intros
  

-- @[simp, grind .]
-- lemma equivalence_bientail : Equivalence bientail where
--   refl := by simp [bientail]
--   symm := by grind [bientail]
--   trans := by grind [bientail]

-- end

-- noncomputable section

-- attribute [local aesop simp] Equivalence.refl Equivalence.trans Equivalence.symm

-- instance : OrderedUnitalResourceAlgebra PSpΩ := inferInstance

-- instance : DiscreteCMRA PSpΩ := inferInstance

-- instance : Iris.CMRA PSpΩ := inferInstance

-- open Iris

-- instance assertionBIBase : BI.BIBase ABprop where
--   Entails := entail
--   emp := true
--   pure := lift
--   and := and
--   or := or
--   imp := imp
--   sForall := sForall
--   sExists := sExists
--   sep := sep
--   wand := wand
--   persistently := persistently
--   later := id

-- instance assertionBI : BI ABprop where
--   Dist _ := bientail
--   dist_eqv := by simp
--   eq_dist := by

    
--   -- ⟨fun h _ => h, fun h => h 0⟩
--   dist_lt := _
--   compl := _
--   conv_compl := _
--   Entails := _
--   emp := _
--   pure := _
--   and := _
--   or := _
--   imp := _
--   sForall := _
--   sExists := _
--   sep := _
--   wand := _
--   persistently := _
--   later := _
--   entails_preorder := _
--   equiv_iff := _
--   and_ne := _
--   or_ne := _
--   imp_ne := _
--   sForall_ne := _
--   sExists_ne := _
--   sep_ne := _
--   wand_ne := _
--   persistently_ne := _
--   later_ne := _
--   pure_intro := _
--   pure_elim' := _
--   and_elim_l := _
--   and_elim_r := _
--   and_intro := _
--   or_intro_l := _
--   or_intro_r := _
--   or_elim := _
--   imp_intro := _
--   imp_elim := _
--   sForall_intro := _
--   sForall_elim := _
--   sExists_intro := _
--   sExists_elim := _
--   sep_mono := _
--   emp_sep := _
--   sep_symm := _
--   sep_assoc_l := _
--   wand_intro := _
--   wand_elim := _
--   persistently_mono := _
--   persistently_idem_2 := _
--   persistently_emp_2 := _
--   persistently_and_2 := _
--   persistently_sExists_1 := _
--   persistently_absorb_l := _
--   persistently_and_l := _
--   later_mono := _
--   later_intro := _
--   later_sForall_2 := _
--   later_sExists_false := _
--   later_sep := _
--   later_persistently := _
--   later_false_em := _

-- end

-- end Amaryllis
