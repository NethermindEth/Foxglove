(* Dependencies of PSp_wsum_instance, extracted from iris/prelude and iris/algebra/pcmras.
   Proofs are replaced by Admitted. *)

From Stdlib Require Import Reals Lra.
From stdpp Require Import base sets fin_sets fin_maps fin_map_dom gmap countable.
From iris.algebra Require Export ora.


(* ======================================================================
   required_axioms
   ====================================================================== *)
Module required_axioms.

From Stdlib Require Import ChoiceFacts.
Axiom classicT : ∀ P, Decision P.
Local Existing Instance classicT.
Axiom ID_epsilon : ∀ A, ConstructiveIndefiniteDescription_on (list A).
End required_axioms.
Import required_axioms.

(* ======================================================================
   fin_sets_ext
   ====================================================================== *)
Module fin_sets_ext.

Set Default Proof Using "Type*".
Section fin_sets_ext.
Context `{FinSet A SA}.
Global Instance elem_of_dec_slow_set : RelDecision (∈@{SA}).
Admitted.
Global Instance set_subsetdec : RelDecision (⊆@{SA}).
Admitted.
Global Instance set_equivdec : RelDecision (≡@{SA}).
Admitted.
Global Instance set_eqdec `{!LeibnizEquiv SA} : EqDecision (SA).
Admitted.
Global Instance set_disjdec : RelDecision (##@{SA}).
Admitted.
Lemma set_choose_type_L (X : SA) `{!LeibnizEquiv SA}:
    X ≠ ∅ → { x : A | x ∈ X }.
Admitted.
End fin_sets_ext.
Definition union_set `{Empty A} `{Union A} `{FinSet A SA} : SA → A := set_fold (∪) ∅.
Notation "⋃ s" := (union_set s) : stdpp_scope.
Definition intersect_set `{Empty A} `{Intersection A} `{Union A} `{FinSet A SA} (X : SA) (b : A) : A := set_fold (∩) b X.
Notation "⋂ s" := (intersect_set s (⋃ s)) (at level 20, format "⋂ s") : stdpp_scope.
End fin_sets_ext.
Import fin_sets_ext.

(* ======================================================================
   propsets
   ====================================================================== *)
Module propsets.

Local Existing Instance classicT.
Record propset (A : Type) : Type := PropSet { propset_car : A → bool }.
Add Printing Constructor propset.
Global Arguments PropSet {_} _ : assert.
Global Arguments propset_car {_} _ _ : assert.
Notation "{[ x | P ]}" := (PropSet (λ x, bool_decide P))
  (at level 1, x as pattern, format "{[ x | P ]}") : stdpp_scope.
Global Instance propset_elem_of {A} : ElemOf A (propset A) := λ x X, propset_car X x = true.
Global Instance propset_top {A} : Top (propset A) := {[ _ | True ]}.
Global Instance propset_empty {A} : Empty (propset A) := {[ _ | False ]}.
Global Instance propset_singleton {A} : Singleton A (propset A) := λ y, {[ x | y = x ]}.
Global Instance propset_union {A} : Union (propset A) := λ X1 X2, {[ x | x ∈ X1 ∨ x ∈ X2 ]}.
Global Instance propset_intersection {A} : Intersection (propset A) := λ X1 X2,
  {[ x | x ∈ X1 ∧ x ∈ X2 ]}.
Global Instance propset_difference {A} : Difference (propset A) := λ X1 X2,
  {[ x | x ∈ X1 ∧ x ∉ X2 ]}.
Global Instance propset_set {A} : Set_ A (propset A).
Admitted.
Global Instance propset_ret : MRet propset := λ A (x : A), {[ x ]}.
Global Instance propset_bind : MBind propset := λ A B (f : A → propset B) (X : propset A),
  PropSet (λ b, bool_decide (∃ a, b ∈ f a ∧ a ∈ X)).
Global Instance propset_fmap : FMap propset := λ A B (f : A → B) (X : propset A),
  {[ b | ∃ a, b = f a ∧ a ∈ X ]}.
Global Instance propset_join : MJoin propset := λ A (XX : propset (propset A)),
  {[ a | ∃ X : propset A, a ∈ X ∧ X ∈ XX ]}.
Definition is_finite {A} (X : propset A) := ∃ (xs : list A), ∀ x, x ∈ X → x ∈ xs.
Global Opaque propset_elem_of propset_top propset_set propset_empty propset_singleton.
Global Opaque propset_union propset_intersection propset_difference.
Global Opaque propset_ret propset_bind propset_fmap propset_join.
End propsets.
Import propsets.

(* ======================================================================
   classical_sets
   ====================================================================== *)
Module classical_sets.

Local Existing Instance classicT.
Record set (A : Type) `{EqDecision A}: Type := FiniteSet { propset_car : propset A; propset_finite : bool_decide (is_finite propset_car) = true }.
Global Arguments propset_car {_ _} _.
Global Arguments propset_finite {_ _} _.
Section fin_ext_sets.
Context `{A : Type}.
Context `{EqDecision A}.
Global Instance set_elem_of: ElemOf A (set A) := λ a X, propset_elem_of a (propset_car X).
Lemma set_empty_finite : bool_decide (is_finite ({[ x | False ]} : propset A)) = true.
Admitted.
Global Instance set_empty: Empty (set A) := FiniteSet A _ {[ x | False ]} set_empty_finite.
Lemma set_singleton_finite (a : A) : bool_decide (is_finite ({[ x | x = a ]} : propset A)) = true.
Admitted.
Global Instance set_singleton: Singleton A (set A) := λ a,
  FiniteSet A _ {[ x | x = a ]} (set_singleton_finite a).
Lemma set_union_finite (X1 X2 : propset A) :
  bool_decide (is_finite X1) = true → bool_decide (is_finite X2) = true →
  bool_decide (is_finite ({[ x | x ∈ X1 ∨ x ∈ X2 ]} : propset A)) = true.
Admitted.
Global Instance set_union: Union (set A) := λ X Y,
  match X, Y with
  | FiniteSet _ _ X1 finX1, FiniteSet _ _ X2 finX2 =>
      FiniteSet A _ {[ x | x ∈ X1 ∨ x ∈ X2 ]} (set_union_finite X1 X2 finX1 finX2)
  end.
Lemma set_intersection_finite (X1 X2 : propset A) :
  bool_decide (is_finite X1) = true → bool_decide (is_finite X2) = true →
  bool_decide (is_finite ({[ x | x ∈ X1 ∧ x ∈ X2 ]} : propset A)) = true.
Admitted.
Global Instance set_intersection: Intersection (set A) := λ X Y,
  match X, Y with
  | FiniteSet _ _ X1 finX1, FiniteSet _ _ X2 finX2 =>
      FiniteSet A _ {[ x | x ∈ X1 ∧ x ∈ X2 ]} (set_intersection_finite X1 X2 finX1 finX2)
  end.
Lemma set_difference_finite (X1 X2 : propset A) :
  bool_decide (is_finite X1) = true → bool_decide (is_finite X2) = true →
  bool_decide (is_finite ({[ x | x ∈ X1 ∧ x ∉ X2 ]} : propset A)) = true.
Admitted.
Global Instance set_difference: Difference (set A) := λ X Y,
  match X, Y with
  | FiniteSet _ _ X1 finX1, FiniteSet _ _ X2 finX2 =>
      FiniteSet A _ {[ x | x ∈ X1 ∧ x ∉ X2 ]} (set_difference_finite X1 X2 finX1 finX2)
  end.
Global Instance set_elements: Elements A (set A) := λ X,
  match X with
  | FiniteSet _ _ X finX =>
      remove_dups (filter (λ x, x ∈ X) (proj1_sig (ID_epsilon A _ (proj1 (bool_decide_eq_true _) finX))))
  end.
Global Existing Instance set_elem_of.
Global Existing Instance set_empty.
Global Existing Instance set_singleton.
Global Existing Instance set_union.
Global Existing Instance set_intersection.
Global Existing Instance set_difference.
Global Existing Instance set_elements.
Lemma set_finset : FinSet A (set A).
Admitted.
Lemma set_leibnitz: LeibnizEquiv (set A).
Admitted.
Global Existing Instance set_finset.
Global Existing Instance set_leibnitz.
End fin_ext_sets.
Section power_set.
Context `{EqDecision A}.
Definition powerset (X : set A) : set (set A) := 
    set_fold (λ a, λ ssa, ssa ∪ (set_map (λ sa, {[a]} ∪ sa) ssa)) ({[∅]}) X.
End power_set.
Section cart_prod.
Definition cartesian_prod `{EqDecision A, EqDecision B} (sa : set A) (sb : set B) : set (A * B) := set_fold (λ a, λ prod, prod ∪ (set_map (λ b, (a, b)) sb)) ∅ sa.
End cart_prod.
Local Open Scope R_scope.
Definition set_sum `{EqDecision A} (f : A → R) (X : set A) := (set_fold (λ a sum, f a + sum) R0) X.
Definition set_minimum `{EqDecision A} f b (X : set A) : R := set_fold (λ x m, Rmin m (f x)) b X.
End classical_sets.
Import classical_sets.

(* ======================================================================
   measure_theory
   ====================================================================== *)
Module measure_theory.

Local Existing Instance classicT.
Definition σAlgebra A `{EqDecision A} := set (set A).
Section algebras.
Context `{EqDecision A}.
Implicit Types (Ω : set A).
Definition is_σAlg Ω (F : σAlgebra A) := 
    set_Forall (λ X, X ⊆ Ω) F ∧ 
    Ω ∈ F ∧ 
    set_Forall (λ X, (set_Forall (λ Y, X ∪ Y ∈ F) F)) F ∧ 
    set_Forall (λ X, Ω ∖ X ∈ F) F.
Definition outcomes_σ (F : σAlgebra A) := union_set F .
Definition TrivialF Ω : σAlgebra A := {[ ∅; Ω ]}.
Definition Full Ω : σAlgebra A := powerset Ω.
Fixpoint generate_closure (Ω : set A) (preF : set (set A)) (n : nat) : σAlgebra A :=
    let compl_gen := preF ∪ (set_map (λ X, Ω ∖ X) preF) in 
        let union_gen := compl_gen ∪ set_map (λ prod, (prod.1 ∪ prod.2)) (cartesian_prod compl_gen compl_gen) in 
            match n with
            | 0 => preF
            | S n' => generate_closure Ω union_gen n'
            end.
Definition make_σ Ω (preF : set (set A)) : σAlgebra A := 
    if decide (preF = ∅) then TrivialF Ω else generate_closure Ω preF (size (Full Ω)).
Definition make_σ' (preF : set (set A)) : σAlgebra A := make_σ (⋃ preF) preF.
Definition σ_union (F1 F2 : σAlgebra A) : σAlgebra A := make_σ' (F1 ∪ F2).
Definition σ_add_impossible (F : σAlgebra A) X : set (set A) := σ_union F (Full X).
End algebras.
Local Open Scope R_scope.
Global Instance R_eqdec : EqDecision (R).
Admitted.
Global Instance R_gedec (x y : R) : Decision (x >= y).
Admitted.
Global Instance R_gtdec (x y : R) : Decision (x > y).
Admitted.
Definition measure A `{EqDecision A} := set (set A * R).
Section measures.
Context `{EqDecision A}.
Implicit Types (Ω : set A).
Definition distr (μ : measure A) : set A → R := 
    λ X, match elements (filter (λ Y, X = Y.1) μ) with
    | [] => 0
    | [ (s, r) ] => r
    | _ => 0 (* This case is impossible *)
    end.
Definition is_distr Ω F (μ : measure A) := 
    is_σAlg Ω F ∧ 
    set_map (λ X, X.1) μ = F ∧
    set_Forall (λ X, set_Forall (λ Y, X.1 = Y.1 → X.2 = Y.2) μ) μ ∧
    set_Forall (λ X, X.2 >= 0) μ ∧ 
    set_Forall (λ X, X.1 = Ω → X.2 = 1) μ ∧
    set_Forall (λ X, set_Forall (λ Y, set_Forall (λ Z, X.1 ## Y.1 → Z.1 = X.1 ∪ Y.1 → Z.2 = X.2 + Y.2) μ) μ) μ.
Definition outcomes (μ : measure A) : set A := set_bind (λ X, X.1) μ.
Definition supp (μ : measure A) : set A := filter (λ X, 0 < distr μ {[X]}) (outcomes μ).
Definition distrF (μ : measure A) := λ a, distr μ {[a]}.
Definition Trivialμ (Ω : set A): measure A := {[ (∅, 0); (Ω, 1) ]}.
Definition restrict (μ : measure A) (F1 : σAlgebra A) : measure A := (filter (λ X, X.1 ∈ F1) μ).
End measures.
Definition PSpace A `{EqDecision A} := (σAlgebra A * measure A)%type.
Section probability_spaces.
Context `{EqDecision A}.
Implicit Types (Ω : set A).
Definition PSp (F : σAlgebra A) (μ: measure A) : PSpace A := (F, μ).
Definition PSpace_distr (P : PSpace A) : measure A := P.2.
Definition π_μ (P : PSpace A) : set A → R := distr (PSpace_distr P).
Definition π_σ (P : PSpace A) : σAlgebra A := P.1.
Definition is_PSpace Ω P := is_distr Ω (π_σ P) (PSpace_distr P).
Definition PSp' (F : σAlgebra A ) μ := PSp F (set_map (λ X, (X, μ X)) F).
Definition TrivialP Ω : PSpace A := PSp (TrivialF Ω) (Trivialμ Ω).
Definition leq_ext (P1 P2: PSpace A) : Prop := (π_σ P1) ⊆ (π_σ P2) ∧ set_Forall (λ X, π_μ P1 X = π_μ P2 X) (π_σ P1).
Definition prob0_set P : set A := (set_bind (λ X, if (decide (X.2 = 0%R)) then X.1 else ∅ ) (PSpace_distr P)).
Definition μ_add_impossible' P X : measure A := set_map (λ Y, (Y, π_μ P (Y ∪ prob0_set P))) (σ_add_impossible (π_σ P) X).
Definition PSp_add_impossible' P X := PSp (σ_add_impossible (π_σ P) X) (μ_add_impossible' P X).
Definition get_Ω (P :PSpace A) := outcomes_σ (π_σ P).
Definition supp' (P : PSpace A) := get_Ω P ∖ prob0_set P.
Definition PSp_make_complete P := PSp_add_impossible' P (prob0_set P).
Definition PSp_complete_alt (P : PSpace A) := set_Forall (λ X, set_Forall (λ m, {[m]} ∈ π_σ P) X) (filter (λ X, π_μ P X = 0%R) (π_σ P)).
Definition get_σ `{EqDecision ℑ} (X : set ℑ) (κ : ℑ → PSpace A) : σAlgebra A.
Proof.
  destruct (decide (X = ∅)) as [-> | Hnemp].
  - exact (Full ∅).
  - destruct (set_choose_type_L X).
    eauto.
    exact (π_σ (κ x)).
Defined.
Definition get_μ `{EqDecision ℑ} (κ : ℑ → PSpace A) : ℑ → measure A :=
  λ i, PSpace_distr (κ i).
End probability_spaces.
Section lifting.
Context `{EqDecision A}.
Implicit Types (Ω : set A).
Record distribution Ω := mkddist {
    dist_car :> measure A;
    dist_is_distr : bool_decide (is_distr Ω (Full Ω) dist_car) = true;
}.
End lifting.
Section extension_theorem.
Context `{EqDecision A}.
Implicit Types (Ω : set A).
Definition outer_measure Ω (preF : set (set A)) (μ : measure A) : measure A := 
    set_map (λ A, (A, set_minimum (λ S, set_sum (λ s, distr μ s) S) (INR (size preF)) (filter (λ S, A ⊆ ⋃ S) (powerset preF)))) (powerset Ω).
Definition M_pred Ω preF μ (A : set A) := 
    set_Forall (λ E, 
        distr (outer_measure Ω preF μ) (A ∩ E) + distr (outer_measure Ω preF μ) ((Ω ∖ A) ∩ E) = distr (outer_measure Ω preF μ) E)
    (powerset Ω).
Definition extended_σ Ω (preF : set (set A)) (μ : measure A) : σAlgebra A := 
    filter (λ A, M_pred Ω preF μ A) (powerset Ω).
Definition extended_μ Ω (preF : set (set A)) (μ : measure A) : measure A := 
    set_map (λ A, (A, distr (outer_measure Ω preF μ) A)) (extended_σ Ω preF μ).
Definition extended_PSpace Ω (preF : set (set A)) (μ : measure A) : PSpace A :=
    PSp (extended_σ Ω preF μ) (extended_μ Ω preF μ).
End extension_theorem.
End measure_theory.
Import measure_theory.

(* ======================================================================
   distributions
   ====================================================================== *)
Module distributions.

Local Existing Instance classicT.
Local Open Scope R_scope.
Section measures.
Context `{EqDecision A}.
Implicit Types (Ω : set A).
Definition dirac' Ω (a : A) : set (set A * R) := 
    set_map (λ X, (X, if decide (a ∈ X) then 1 else 0)) (Full Ω).
Global Instance distr_inhabited: Inhabited A → Inhabited (measure A).
Proof. intros. constructor. exact ( (dirac' ∅ inhabitant) ). Defined.
End measures.
Section monad_structure.
Definition joint_distr `{EqDecision A, EqDecision B} (μ : measure A) (κ: A → measure B) (a : A) (bs : set B) : R :=
  distrF μ a * distr (κ a) bs.
Definition distr_bind `{EqDecision A, EqDecision B} (F : σAlgebra B) (μ : measure A) (κ: A → measure B) : set (set B * R) := 
    set_map (λ bs, (bs, set_sum (λ a, joint_distr μ κ a bs) (supp μ))) F.
Definition PSp_bind `{EqDecision A} `{EqDecision ℑ} {Ω: set ℑ} (μ : distribution Ω) (κ: ℑ → PSpace A)
 :=  (PSp (get_σ (supp μ) κ) (distr_bind (get_σ (supp μ) κ) μ (get_μ κ))).
End monad_structure.
Section restrict_PSp.
Context `{EqDecision A}.
Definition restrict_PSp (P : PSpace A) (F : σAlgebra A) : PSpace A := PSp F (restrict (PSpace_distr P) F).
End restrict_PSp.
Section independent_product.
Context `{EqDecision A}.
Implicit Types (Ω : set A).
Definition pairwise_intersec_σ (P1 P2 : PSpace A) : σAlgebra A :=
set_map (λ X, X.1 ∩ X.2) (cartesian_prod (π_σ P1) (π_σ P2)).
Definition pairwise_intersec_μ (P1 P2 : PSpace A) : measure A := 
set_map (λ X, (X.1 ∩ X.2, (π_μ P1 X.1) * (π_μ P2 X.2))) (cartesian_prod (π_σ P1) (π_σ P2)).
Definition iprod_exists (P1 P2 : PSpace A) : Prop := 
    set_Forall (λ A1, set_Forall (λ A2, set_Forall (λ B1, set_Forall (λ B2, 
        A1 ∩ B1 = A2 ∩ B2 → 
        (π_μ P1) A1 * (π_μ P2) B1 = (π_μ P1) A2 * (π_μ P2) B2
    ) (π_σ P2)) (π_σ P2)) (π_σ P1)) (π_σ P1).
Definition iprod Ω (P1 P2 : PSpace A) : option (PSpace A) := 
    if decide (iprod_exists P1 P2)
    then Some (extended_PSpace Ω (pairwise_intersec_σ P1 P2) (pairwise_intersec_μ P1 P2))
    else None.
End independent_product.
Section PSp_map2.
Context `{EqDecision A}.
Implicit Types (Ω : set A).
Definition sure_info P: PSpace A := PSp' {[ ∅; prob0_set P; supp' P; get_Ω P]} (λ X, if decide (X ⊆ prob0_set P) then 0%R else 1%R).
End PSp_map2.
End distributions.
Import distributions.

(* Classes from iris.algebra.pcmra (which depends on the original iris.prelude types) *)
Class WSum (A: Type)   := wsum ℑ `{EqDecision ℑ} (Ω : set ℑ): distribution Ω → (ℑ → A) → A.
Global Arguments wsum {_ _ _ _ _} _ _  .
Global Hint Mode WSum !  : typeclass_instances.
Global Instance: Params (@wsum) 4 := {}.

Class FCore (A : Type) := fcore : A → option A.
Global Hint Mode FCore ! : typeclass_instances.
Global Instance: Params (@fcore) 2 := {}.

(* ======================================================================
   domain_extensions_ra
   ====================================================================== *)
Module domain_extensions_ra.

Local Existing Instance classicT.
Notation RID := nat (only parsing).
Section RID_map_res_def.
Program Definition RID_map_ext_dom (m : gmap RID bool) ι : set (gmap RID bool) :=
    {[ <[ι := true]> m;  <[ι := false]> m ]}.
Program Definition all_maps (rid: gset RID): set (gmap RID bool)
    := set_fold (λ ι X, set_bind (λ m, (RID_map_ext_dom m ι)) X) {[∅]} rid.
Record RID_map_res := mkRID_map_res {
    Rid : gset RID;
    PSp_car :> PSpace (gmap RID bool);
    is_PSp : bool_decide (is_PSpace (all_maps Rid) PSp_car) = true;
    complete: bool_decide (PSp_complete_alt PSp_car) = true;
}.
End RID_map_res_def.
Section extP.
Set Default Proof Using "Type*".
Notation RID := nat (only parsing).
Definition insert_RIDs (rid : gset RID)  X : set(gmap RID bool) :=
  set_fold (λ ι X, set_bind (λ m, RID_map_ext_dom m  ι) X) X rid.
Program Definition σ_alg_ext_dom  (F: σAlgebra (gmap RID bool)) rid: σAlgebra (gmap RID bool) :=
    set_map (insert_RIDs rid) F.
Definition delete_RIDs (rid : gset RID) (m : gmap RID bool) := set_fold (λ ι X, delete ι X) m rid.
Definition σ_alg_ext_dom_inv (rid : gset RID) (X : set (gmap RID bool)) : set (gmap RID bool) := set_map (delete_RIDs rid) X.
Definition PSp_ext_domain (P : PSpace (gmap RID bool)) rid: PSpace (gmap RID bool) :=
    PSp' (σ_alg_ext_dom (π_σ P) rid) (λ X, π_μ P (σ_alg_ext_dom_inv rid X)).
Definition extP r1 (P : PSpace (gmap RID bool)) (r2 : gset RID)
    :=  PSp_make_complete (PSp_ext_domain P (r2 ∖ r1)).
Lemma unit_ok_1: bool_decide (is_PSpace (all_maps ∅) (TrivialP {[∅]})) = true.
Admitted.
Lemma unit_ok_3: bool_decide (PSp_complete_alt (TrivialP ({[∅]} : set (gmap RID bool)))) = true.
Admitted.
End extP.
Inductive PSp_ra :=
  | PSp_val : RID_map_res → PSp_ra
  | PSp_Bot : PSp_ra.
Definition RID_map_res_ε := (mkRID_map_res ∅ (TrivialP {[ ∅ ]}) unit_ok_1 unit_ok_3).
Definition PSp_ra_to_RID_map_res  (P : PSp_ra) : RID_map_res := match P with
  | PSp_val P => P
  | PSp_Bot => RID_map_res_ε 
end.
Global Coercion PSp_ra_to_RID_map_res: PSp_ra >-> RID_map_res.
Global Instance PSp_ra_equiv_instance : Equiv PSp_ra := λ x y, 
  match x, y with 
  | PSp_val x, PSp_val y =>  extP (Rid x) x (Rid y) = extP (Rid y) y (Rid x)
  | PSp_Bot, PSp_Bot => True
  | _, _ => False
end.
Section PSp_ra.
Notation RID := nat (only parsing).
Lemma some_or_none {A} (x : option A) : { xy & x = Some xy } + { x = None }.
Admitted.
Lemma prod_ok1 (x : RID_map_res) y (xyB : { xy & iprod (all_maps (Rid x ∪ Rid y)) (extP (Rid x) x (Rid y)) (extP (Rid y) y (Rid x)) = Some xy})
: bool_decide (is_PSpace (all_maps (Rid x ∪ Rid y)) (projT1 xyB)) = true.
Admitted.
Lemma prod_ok3 (x y : RID_map_res) (xyB : { xy & iprod (all_maps (Rid x ∪ Rid y)) (extP (Rid x) x (Rid y)) (extP (Rid y) y (Rid x)) = Some xy})
: bool_decide (PSp_complete_alt (projT1 xyB)) = true.
Admitted.
Definition psp_op_prod (x y : RID_map_res) := 
 let prod := iprod (all_maps (Rid x ∪ Rid y)) (extP (Rid x) x (Rid y)) (extP (Rid y) y (Rid x)) in
 match some_or_none prod with 
            | inleft xy => PSp_val (mkRID_map_res (Rid x ∪ Rid y) (projT1 xy) (prod_ok1 x y xy) (prod_ok3 x y xy))
            | _ => PSp_Bot
 end.
Global Instance PSp_valid_instance : Valid (PSp_ra) := λ x, x ≠ PSp_Bot.
Global Instance PSp_op_instance : Op (PSp_ra) := λ x y, 
    match x, y with 
    | PSp_val x, PSp_val y => psp_op_prod x y
    | _, _ => PSp_Bot
end.
Global Instance PSp_unit_instance: Unit (PSp_ra) :=
  PSp_val RID_map_res_ε .
Lemma pcore_ok_1 (x : RID_map_res): bool_decide (is_PSpace (all_maps (Rid x)) (PSp_make_complete (sure_info x))) = true.
Admitted.
Lemma pcore_ok_3 (x : RID_map_res): bool_decide (PSp_complete_alt (PSp_make_complete (sure_info x))) = true.
Admitted.
Global Instance pcore_instance : PCore (PSp_ra) := λ x, Some
  match x with
  | PSp_val x => PSp_val (mkRID_map_res (Rid x) (PSp_make_complete (sure_info x)) (pcore_ok_1 x) (pcore_ok_3 x))
  | PSp_Bot => PSp_Bot
  end.
Global Instance PSp_ra_eqdec : EqDecision (PSp_ra).
Admitted.
End PSp_ra.
End domain_extensions_ra.
Import domain_extensions_ra.

(* ======================================================================
   domain_extensions_ora
   ====================================================================== *)
Module domain_extensions_ora.

Local Existing Instance classicT.
Notation RID := nat (only parsing).
Section PSp_ora.
Global Instance PSp_ora_order_instance : OraOrder (PSp_ra) := λ x y, 
  match x, y with 
  | PSp_val x, PSp_val y => leq_ext (extP (Rid x) x (Rid y) ) (extP (Rid y) y (Rid x))
  | _, PSp_Bot => True
  | _, _ => False
  end.
End PSp_ora.
End domain_extensions_ora.
Import domain_extensions_ora.

(* ======================================================================
   domain_extensions_pra
   ====================================================================== *)
Module domain_extensions_pra.

Local Existing Instance classicT.
Section distr_ext.
Context `{EqDecision A}.
Definition sigma_intersec `{EqDecision ℑ} (X : set ℑ) (κ : ℑ → PSpace A) :=
  ⋂ ((set_map (λ i, π_σ (κ i)) X) : set (σAlgebra A)).
End distr_ext.
Section domain_extensions_pra.
Notation RID := nat (only parsing).
Definition Rid_union `{EqDecision ℑ} (X : set ℑ) (κ: ℑ → PSp_ra) :=
   union_set (set_map (λ i, Rid (κ i)) X : gset (gset RID)).
Definition part_extP `{EqDecision ℑ} (X : set ℑ) (κ: ℑ → PSp_ra) i :=
  extP (Rid (κ i)) (κ i) (Rid_union X κ).
Definition common_PSp' `{EqDecision ℑ} (X : set ℑ) (κ: ℑ → PSp_ra) :=
  λ i, restrict_PSp (part_extP X κ i) (sigma_intersec X (part_extP X κ)).
Definition has_rv `{EqDecision ℑ} (μ: measure ℑ) (κ : ℑ → PSp_ra) := 
  ∀ v1 v2, v1 ∈ supp μ → v2 ∈ supp μ → v1 ≠ v2 → 
    supp' (part_extP (supp μ) κ v1) ## supp' (part_extP (supp μ) κ v2).
Definition wsum_ok `{EqDecision ℑ} (μ : measure ℑ) κ := 
  has_rv μ κ ∧ ∀ i, i ∈ (supp μ) → ✓ (κ i).
Lemma wsum_ok1 `{EqDecision ℑ} {Ω : set ℑ} {μ: distribution Ω} {κ} (Hok : wsum_ok μ κ):
   bool_decide (is_PSpace (all_maps (Rid_union (supp μ) κ)) (PSp_bind μ (common_PSp' (supp μ) κ))) = true.
Admitted.
Lemma wsum_ok3 `{EqDecision ℑ} {Ω : set ℑ} {μ: distribution Ω} {κ} (Hok : wsum_ok μ κ): 
  bool_decide (PSp_complete_alt (PSp_bind μ (common_PSp' (supp μ) κ))) = true.
Admitted.
Global Instance PSp_wsum_instance : WSum (PSp_ra) := λ ℑ eqdec Ω μ κ,
  match (decide (wsum_ok μ κ)) with
    | left H => PSp_val (mkRID_map_res (Rid_union (supp μ) κ) (PSp_bind μ (common_PSp' (supp μ) κ)) (wsum_ok1 H) (wsum_ok3 H))
    | _ => PSp_Bot
  end.
Global Instance PSp_fcore_instance : FCore (PSp_ra) := Some.
End domain_extensions_pra.
End domain_extensions_pra.
Import domain_extensions_pra.

