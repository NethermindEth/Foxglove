module

public import Foxglove.Rules.WP

@[expose] public section
namespace Foxglove

open ProbSpace
open Iris OrderedUnitalResourceAlgebra
open UpperSetBI
open Iris BI UpperSetBI OURAProp

noncomputable section

/-! # The core of `WPBindC` -/

set_option linter.style.haveILetI false in
set_option maxHeartbeats 1000000 in
open Interp Interp.ProbTree Interp.ProbTree.BoundedFootprintPsp ProbabilityTheory MeasureTheory in
/-- The semantic core of `WPBindCond` and `WPBindC`: from a witness of `C`'s run whose
resource conditions, on a law `ν` of the result, the continuation's `wp` at each value, a
witness of the run of `C >>= F` whose resource conditions the continuation's postconditions
on the same `ν`.

The proof is the mixing argument of `CWPSwap_core`, with the second stage of the sequenced
run (`secondStage`) in place of the one program: the fibres of the conditioning are the second
stage run at each fibre's measure (`run_bind`, `fixpoint_sum'`), each fibre's witness sits
below its fibre because the fibre's own run differs from the second stage only at atoms the
fibre gives no mass (`fixpoint_agreeOffNull`), and the fibre's result agrees with the
composite's off those atoms (`result_run_fibre`), which `AEProper` turns into `Q v` of the
composite's result through a null-set space (`PSpace.nullSpace_mul_le`). -/
lemma WPBindC_core {α β : Type} {m : Type → Type} [Monad m]
    [Interp.LawfulBernoulliInterpretable m] [Inhabited α] [Inhabited β]
    {C : m α} {F : α → m β} {ν : PMF α} {Q : α → RV β → FProp} (hQ : ∀ v, AEProper (Q v))
    (μ₀ : BoundedFootprintPsp) (hvalid : ✓μ₀.psp) (a c : BoundedFootprintSpace Bool)
    (hva : ✓a) (hle : a * c ≤ μ₀.toSpace) (b : BoundedFootprintSpace Bool)
    (hbc : b * c ≤ (run C μ₀).1.toSpace) (hvb : ✓b)
    (hbms : msOf b ≤ msOf a ⊔ freshMs μ₀ (Interp.BernoulliInterpretable.interp C))
    (hbQ : own b ⊢ condValue ν (result (run C μ₀)) (fun v ↦ wp (F v) (Q v))) :
    ∃ b' : BoundedFootprintSpace Bool,
      b' * c ≤ (run (C >>= F) μ₀).1.toSpace ∧ ✓b' ∧
        msOf b' ≤ msOf a ⊔ freshMs μ₀ (Interp.BernoulliInterpretable.interp (C >>= F)) ∧
        (own b' ⊢ 𝒞⟨ν⟩ v; Q v (result (run (C >>= F) μ₀))) := by
  set Cb : BernoulliM α := BernoulliInterpretable.interp C with hCb
  set Fb : α → BernoulliM β := fun v ↦ BernoulliInterpretable.interp (F v) with hFb
  have hCF : BernoulliInterpretable.interp (C >>= F) = Cb >>= Fb :=
    LawfulBernoulliInterpretable.interp_bind C F
  have hrun : run (C >>= F) μ₀ = run (Cb >>= Fb) μ₀ := by
    show bigStep μ₀ (fun _ ↦ BernoulliInterpretable.interp (C >>= F))
      = bigStep μ₀ (fun _ ↦ Cb >>= Fb)
    rw [hCF]
  rw [hrun, hCF]
  -- the ambient before `C`, and the ambient after it
  set P₀ : PSpace Ω := ValidPSp.toPSpace ⟨μ₀.psp, hvalid⟩ with hP₀
  have hμ₀P : μ₀.psp = .some P₀ := (Option.some_get _).symm
  have hle_amb : ∀ {x : BoundedFootprintSpace Bool} {p : PSpace Ω},
      x ≤ μ₀.toSpace → (x : PSp Ω) = .some p → p ≤ P₀ := by
    intro x p hx hp
    have h : (.some p : PSp Ω) ≤ .some P₀ := by rw [← hp, ← hμ₀P]; exact hx
    exact WithTop.coe_le_coe.1 h
  set μ₁ : BoundedFootprintPsp := (run Cb μ₀).1 with hμ₁
  have h₁ : ✓μ₁.psp := valid_run_psp μ₀ hvalid Cb
  set P₁ : PSpace Ω := ValidPSp.toPSpace ⟨μ₁.psp, h₁⟩ with hP₁
  have hμ₁P : μ₁.psp = .some P₁ := (Option.some_get _).symm
  have hle_amb₁ : ∀ {x : BoundedFootprintSpace Bool} {p : PSpace Ω},
      x ≤ μ₁.toSpace → (x : PSp Ω) = .some p → p ≤ P₁ := by
    intro x p hx hp
    have h : (.some p : PSp Ω) ≤ .some P₁ := by rw [← hp, ← hμ₁P]; exact hx
    exact WithTop.coe_le_coe.1 h
  set X : RV α := result (run Cb μ₀) with hX
  have hbc' : b * c ≤ μ₁.toSpace := hbc
  have hbQ' : own b ⊢ condValue ν X (fun v ↦ wp (F v) (Q v)) := hbQ
  have hbms' : msOf b ≤ msOf a ⊔ freshMs μ₀ Cb := hbms
  -- the conditioning inside the premise's postcondition
  obtain ⟨mm, hbfm, κ, R, hmix, hMR, hfib⟩ := condValue_elim hvb hbQ'
  set M : BoundedFootprintSpace Bool := ⟨(mm : PSp Ω), hbfm⟩ with hM
  have hmp := mm.2
  have hMRc : (M * R) * c ≤ μ₁.toSpace := le_trans (mul_le_mul_right_le hMR c) hbc'
  have hMD : M * (R * c) ≤ μ₁.toSpace := by rw [← mul_assoc]; exact hMRc
  have hvμ₁ : ✓(μ₁.toSpace) := h₁
  have hvMRc : ✓((M * R) * c) := valid_mono hMRc hvμ₁
  have hvMR : ✓(M * R) := valid_mul_l hvMRc
  have hvR : ✓R := valid_mul_r hvMR
  have hvc : ✓c := valid_mul_r hvMRc
  have hvMD : ✓(M * (R * c)) := valid_mono hMD hvμ₁
  have hvD : ✓(R * c) := valid_mul_r hvMD
  obtain ⟨d, hd⟩ : ∃ d : PSpace Ω, ((R * c : BoundedFootprintSpace Bool) : PSp Ω) = .some d :=
    Option.ne_none_iff_exists'.mp (PSp.valid_def.mp hvD)
  obtain ⟨r, hr⟩ : ∃ r : PSpace Ω, (R : PSp Ω) = .some r :=
    Option.ne_none_iff_exists'.mp (PSp.valid_def.mp hvR)
  obtain ⟨c', hc'⟩ : ∃ c' : PSpace Ω, (c : PSp Ω) = .some c' :=
    Option.ne_none_iff_exists'.mp (PSp.valid_def.mp hvc)
  obtain ⟨s, hs⟩ : ∃ s : PSpace Ω,
      ((M * (R * c) : BoundedFootprintSpace Bool) : PSp Ω) = .some s :=
    Option.ne_none_iff_exists'.mp (PSp.valid_def.mp hvMD)
  obtain ⟨y, hy⟩ : ∃ y : PSpace Ω, ((M * R : BoundedFootprintSpace Bool) : PSp Ω) = .some y :=
    Option.ne_none_iff_exists'.mp (PSp.valid_def.mp hvMR)
  have hsmd : s =ᵢ mm ⊕ᵢ d := by
    apply PSp.mul_inversion
    have h := hs
    rw [show ((M * (R * c) : BoundedFootprintSpace Bool) : PSp Ω)
      = PSp.mul (M : PSp Ω) ((R * c : BoundedFootprintSpace Bool) : PSp Ω) from rfl, hd] at h
    exact h
  have hymr : y =ᵢ mm ⊕ᵢ r := by
    apply PSp.mul_inversion
    have h := hy
    rw [show ((M * R : BoundedFootprintSpace Bool) : PSp Ω)
      = PSp.mul (M : PSp Ω) (R : PSp Ω) from rfl, hr] at h
    exact h
  have hsP : s ≤ P₁ := hle_amb₁ hMD hs
  have hm_le_P : mm ≤ P₁ := le_trans (PSpace.le_of_isIndependentProduct_left hsmd) hsP
  have hmP : mm.ms ≤ P₁.ms := hm_le_P.1
  have hdP : d.ms ≤ P₁.ms := le_trans (PSpace.le_of_isIndependentProduct_right hsmd).1 hsP.1
  have hdp := d.2
  have hy𝓜 : y.ms = mm.ms ⊔ r.ms := hymr.1
  -- the fibres, as reweightings of the ambient after `C`
  haveI : Countable ν.support := ν.support_countable.to_subtype
  have hac : ∀ i : ν.support, κ.1 i ≪ mm.μ := fun i ↦ kernel_fibre_ac κ hmix i.2
  haveI hκp : ∀ i : ν.support, IsProbabilityMeasure (κ.1 i) :=
    fun i ↦ κ.2.isProbabilityMeasure i
  set g : ν.support → Ω → ENNReal := fun i ↦ (κ.1 i).rnDeriv mm.μ with hg
  have hgm : ∀ i, Measurable[mm.ms] (g i) := fun i ↦ Measure.measurable_rnDeriv _ _
  set ρ : ν.support → Measure[P₁.ms] Ω := fun i ↦ P₁.μ.withDensity (g i) with hρ
  have hρrect : ∀ i E, MeasurableSet[d.ms] E → ∀ F, MeasurableSet[mm.ms] F →
      ρ i (E ∩ F) = d.μ E * κ.1 i F :=
    fun i E hE F hF ↦ PSpace.withDensity_rect hsmd hsP (κ.1 i) (hac i) hE hF
  haveI hρp : ∀ i, IsProbabilityMeasure (ρ i) := fun i ↦ ⟨by
    have h := hρrect i Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ
    rwa [Set.inter_univ, hdp.measure_univ, (hκp i).measure_univ, one_mul] at h⟩
  have hκmix : ∀ F, MeasurableSet[mm.ms] F → mm.μ F = ∑' i : ν.support, ν i * κ.1 i F := by
    intro F hF; rw [hmix]; exact bind_apply_support ν κ.1 hF
  have hP₁mix : ∀ E, MeasurableSet[P₁.ms] E → P₁.μ E = ∑' i : ν.support, ν i * ρ i E :=
    fun E hE ↦ PSpace.withDensity_mixture hm_le_P (fun i : ν.support ↦ ν i)
      (fun i : ν.support ↦ κ.1 i) hac hκmix hE
  have hρac : ∀ i, ρ i ≪ P₁.μ := fun i ↦ withDensity_absolutelyContinuous _ _
  -- the reweighted footprints
  set τ : ν.support → BoundedFootprintPsp :=
    fun i ↦ BoundedFootprintPsp.reweight μ₁ h₁ (ρ i) (hρp i) with hτ
  have hτpsp : ∀ i, (τ i).psp = .some ⟨⟨P₁.ms, ρ i⟩, hρp i⟩ := fun i ↦ rfl
  have hτvalid : ∀ i, ✓(τ i).psp := fun i ↦ reweight_valid
  have hτP : ∀ i, ValidPSp.toPSpace ⟨(τ i).psp, hτvalid i⟩ = ⟨⟨P₁.ms, ρ i⟩, hρp i⟩ :=
    fun i ↦ ValidPSp.toPSpace_eq _ (hτpsp i)
  -- each fibre, with the frame, sits in its reweighted ambient
  have hvm : ✓((mm : PSp Ω)) := PSp.valid_def.mpr (Option.some_ne_none _)
  have hk : ∀ i : ν.support, HasBoundedFootprint (((κ i : PSpace Ω)) : PSp Ω) := fun i ↦
    hasBoundedFootprint_congr hvm (PSp.valid_def.mpr (Option.some_ne_none _)) rfl hbfm
  set K : ν.support → BoundedFootprintSpace Bool :=
    fun i ↦ ⟨((κ i : PSpace Ω) : PSp Ω), hk i⟩ with hK
  have hKD : ∀ i, K i * (R * c) ≤ (τ i).toSpace := by
    intro i
    have hsup : mm.ms ⊔ d.ms ≤ P₁.ms := sup_le hmP hdP
    have hX' : @PSpace.trim Ω ⟨⟨P₁.ms, ρ i⟩, hρp i⟩ (mm.ms ⊔ d.ms) hsup
        =ᵢ (κ i : PSpace Ω) ⊕ᵢ d := by
      refine ⟨rfl, fun F hF E hE ↦ ?_⟩
      have h1 : ρ i (F ∩ E) = κ.1 i F * d.μ E := by
        rw [Set.inter_comm, hρrect i E hE F hF, mul_comm]
      have h2 := MeasureOnSpace.trim_eq (p := ⟨P₁.ms, ρ i⟩) hsup
        (((le_sup_left : mm.ms ≤ _) _ hF).inter ((le_sup_right : d.ms ≤ _) _ hE))
      exact h2.trans h1
    show PSp.mul (.some (κ i : PSpace Ω)) ((R * c : BoundedFootprintSpace Bool) : PSp Ω)
      ≤ (τ i).psp
    rw [hd, hτpsp]
    exact (le_of_eq (mul_respect_independentProduct hX')).trans
      (WithTop.coe_le_coe.2 (PSpace.trim_le (p := ⟨⟨P₁.ms, ρ i⟩, hρp i⟩) hsup))
  have hRKc : ∀ i, (R * K i) * c ≤ (τ i).toSpace := by
    intro i; rw [mul_comm R, mul_assoc]; exact hKD i
  have hvRK : ∀ i, ✓(R * K i) := fun i ↦ valid_mul_l (valid_mono (hRKc i) (hτvalid i))
  -- the fibre's resource: `X = i` sure, and a resource for the continuation's `wp`
  have hfib' : ∀ i : ν.support, ∃ (Pi : PSpace Ω) (hbfPi : HasBoundedFootprint (Pi : PSp Ω))
      (Ri : BoundedFootprintSpace Bool),
      (⟨(Pi : PSp Ω), hbfPi⟩ : BoundedFootprintSpace Bool) * Ri ≤ R * K i ∧
        Pi.μ {ρ' | ¬ X ρ' = i} = 0 ∧ (own Ri ⊢ wp (F i) (Q i)) :=
    fun i ↦ liftPred_sep_elim (hvRK i) (hfib i i.2 (hk i))
  choose Pi hbfPi Ri hPR hPi0 hRi using hfib'
  have hRi_le : ∀ i, Ri i ≤ R * K i := fun i ↦
    le_trans (by rw [mul_comm]; exact le_mul_of_one_le PSp.one_le) (hPR i)
  have hRic : ∀ i, Ri i * c ≤ (τ i).toSpace := fun i ↦
    le_trans (mul_le_mul_right_le (hRi_le i) c) (hRKc i)
  have hvRi : ∀ i, ✓(Ri i) := fun i ↦ valid_mul_l (valid_mono (hRic i) (hτvalid i))
  -- run every fibre
  have hwp : ∀ i : ν.support, ∃ bv : BoundedFootprintSpace Bool,
      bv * c ≤ (run (F i) (τ i)).1.toSpace ∧ ✓bv ∧
        msOf bv ≤ msOf (Ri i) ⊔ freshMs (τ i) (Fb i) ∧
        (own bv ⊢ Q i (result (run (F i) (τ i)))) :=
    fun i ↦ hRi i (Ri i) (hvRi i) (le_refl (Ri i)) (τ i) c (hτvalid i) (hRic i)
  choose bv hbvc hbvv hbvms hbvQ using hwp
  -- on a fibre, the value `C` reported is the fibre's value, wherever the fibre has mass
  have hPiτ : ∀ i, Pi i ≤ ⟨⟨P₁.ms, ρ i⟩, hρp i⟩ := by
    intro i
    have h1 : (⟨(Pi i : PSp Ω), hbfPi i⟩ : BoundedFootprintSpace Bool) ≤ (τ i).toSpace :=
      le_trans (le_mul_of_one_le PSp.one_le) (le_trans (hPR i)
        (le_trans (le_mul_of_one_le PSp.one_le) (hRKc i)))
    have h2 : (.some (Pi i) : PSp Ω) ≤ .some ⟨⟨P₁.ms, ρ i⟩, hρp i⟩ := h1
    exact WithTop.coe_le_coe.1 h2
  have hρnull : ∀ i, PSpace.μ (⟨⟨P₁.ms, ρ i⟩, hρp i⟩ : PSpace Ω) {ρ' | ¬ X ρ' = i} = 0 :=
    fun i ↦ PSpace.null_of_le (hPiτ i) (hPi0 i)
  have hXv : ∀ i : ν.support, ∀ ρ', ρ i (μ₁.atomOf ρ').1 ≠ 0 → X ρ' = i := by
    intro i ρ' hρ'
    by_contra hne
    apply hρ'
    refine measure_mono_null (fun ρ'' hρ'' ↦ ?_) (hρnull i)
    show ¬ (run Cb μ₀).2 (μ₁.atomOf ρ'') = i
    rw [μ₁.atomOf_eq hρ'']
    exact hne
  have hac' : ∀ i : ν.support, ∀ ρ', P₁.μ (μ₁.atomOf ρ').1 = 0 → ρ i (μ₁.atomOf ρ').1 = 0 :=
    fun i ρ' h0 ↦ hρac i h0
  -- the composite run, and the second stage
  obtain ⟨S, hS, hP₀S, hSmeas, hSpres, -⟩ := run_const μ₀ (Cb >>= Fb) hvalid
  obtain ⟨hSle, hSμ⟩ := run_bind μ₀ hvalid Cb Fb hS
  set T : ProbTree β := secondStage μ₀ Cb Fb with hT
  have hTms : T.ms = P₁.ms := by
    rw [hT, secondStage, toTree_ms_eq, μ₁.sigmaAgrees h₁]
  have hfreshS := run_fresh μ₀ (Cb >>= Fb) hvalid hS
  -- `a` and `c` live independently in the ambient
  obtain ⟨a', ha'⟩ : ∃ a' : PSpace Ω, (a : PSp Ω) = .some a' :=
    Option.ne_none_iff_exists'.mp (PSp.valid_def.mp hva)
  have hvac : ✓(a * c) := valid_mono hle hvalid
  obtain ⟨w, hw⟩ : ∃ w : PSpace Ω, ((a * c : BoundedFootprintSpace Bool) : PSp Ω) = .some w :=
    Option.ne_none_iff_exists'.mp (PSp.valid_def.mp hvac)
  have hwac : w =ᵢ a' ⊕ᵢ c' := by
    apply PSp.mul_inversion
    have h := hw
    rw [show ((a * c : BoundedFootprintSpace Bool) : PSp Ω)
      = PSp.mul (a : PSp Ω) (c : PSp Ω) from rfl, ha', hc'] at h
    exact h
  have hwP : w ≤ P₀ := hle_amb hle hw
  have haP : a' ≤ P₀ := le_trans (PSpace.le_of_isIndependentProduct_left hwac) hwP
  have hcP : c' ≤ P₀ := le_trans (PSpace.le_of_isIndependentProduct_right hwac) hwP
  have hP₀S' : P₀ ≤ S := PSpace.le_of_ms_le hP₀S fun E hE ↦ hSpres hE
  have hcS : c' ≤ S := le_trans hcP hP₀S'
  have haS : a'.ms ≤ S.ms := le_trans haP.1 hP₀S
  -- the one σ-algebra every witness lives on
  set 𝓜 : MeasurableSpace Ω := (mm.ms ⊔ r.ms) ⊔ freshMs μ₀ (Cb >>= Fb) with h𝓜
  have hmsOfa : msOf a = a'.ms := msOf_of_val ha'
  have hyb : y.ms ≤ msOf b := by
    rw [← msOf_of_val hy]; exact msOf_mono hMR
  have hmr_le : mm.ms ⊔ r.ms ≤ a'.ms ⊔ freshMs μ₀ (Cb >>= Fb) := by
    rw [← hy𝓜]
    refine le_trans hyb (le_trans hbms' ?_)
    rw [hmsOfa]
    exact sup_le_sup_left (freshMs_le_freshMs_bind μ₀ Cb Fb) _
  have h𝓜a : 𝓜 ≤ a'.ms ⊔ freshMs μ₀ (Cb >>= Fb) := sup_le hmr_le le_sup_right
  have h𝓜S : 𝓜 ≤ S.ms := le_trans h𝓜a (sup_le haS hfreshS.1)
  have h𝓜T : 𝓜 ≤ (fixpoint ⟨T, P₁.μ.cast T.ms⟩).1.ms := le_trans h𝓜S hSle
  -- `𝓜` is independent of the frame: `a ⊗ c` was, and the fresh bits are
  have hrect : ∀ G, MeasurableSet[𝓜] G → ∀ E, MeasurableSet[c'.ms] E →
      S.μ (G ∩ E) = S.μ G * c'.μ E := by
    intro G hG E hE
    refine PSpace.indep_sup_of_rect haS hfreshS.1 hcS ?_ hE G (h𝓜a G hG)
    intro A hA F hF E hE
    have hAP : MeasurableSet[P₀.ms] A := haP.1 _ hA
    have hEP : MeasurableSet[P₀.ms] E := hcP.1 _ hE
    have h1 : S.μ (A ∩ F ∩ E) = S.μ F * P₀.μ (A ∩ E) := by
      rw [show A ∩ F ∩ E = F ∩ (A ∩ E) by ext; simp only [Set.mem_inter_iff]; tauto]
      exact hfreshS.2 hF (hAP.inter hEP)
    have h2 : S.μ (A ∩ F) = S.μ F * P₀.μ A := by
      rw [Set.inter_comm]; exact hfreshS.2 hF hAP
    have hAEw : MeasurableSet[w.ms] (A ∩ E) :=
      hwac.1.symm.le _ (mem_sup_inter a'.ms c'.ms hA hE)
    have h3 : P₀.μ (A ∩ E) = a'.μ A * c'.μ E := by
      rw [← MeasureOnSpace.le_preserves_measure hwP hAEw]
      exact hwac.2 A hA E hE
    have h4 : P₀.μ A = a'.μ A := (MeasureOnSpace.le_preserves_measure haP hA).symm
    rw [h1, h2, h3, h4, mul_assoc]
  -- the witness: the composite run, trimmed to `𝓜`
  set B : PSpace Ω := @PSpace.trim Ω S 𝓜 h𝓜S with hB
  have hvS : ✓((run (Cb >>= Fb) μ₀).1.psp) := by rw [hS]; exact Option.some_ne_none _
  have hbfB : HasBoundedFootprint ((B : PSp Ω)) :=
    hasBoundedFootprint_mono hvS (by rw [hS]; exact WithTop.coe_le_coe.2 (PSpace.trim_le h𝓜S))
      (hasBoundedFootprint_of_tree _)
  refine ⟨⟨(B : PSp Ω), hbfB⟩, ?_, PSp.valid_def.mpr (Option.some_ne_none _), ?_, ?_⟩
  · show PSp.mul (.some B) (c : PSp Ω) ≤ (run (Cb >>= Fb) μ₀).1.psp
    rw [hc', hS]
    exact PSpace.mul_trim_le h𝓜S hcS hrect
  · rw [msOf_of_val (p := B) rfl]
    show (mm.ms ⊔ r.ms) ⊔ freshMs μ₀ (Cb >>= Fb) ≤ msOf a ⊔ freshMs μ₀ (Cb >>= Fb)
    rw [hmsOfa]
    exact sup_le hmr_le le_sup_right
  -- the fibres of the conditioning: the second stage, run with each fibre's measure
  have hTprob : ∀ i, IsProbabilityMeasure (fixpoint ⟨T, (ρ i).cast T.ms⟩).2 := fun i ↦ ⟨by
    rw [fixpoint_preserves' _ MeasurableSet.univ,
      Measure.le_preserves_measure (h := le_of_eq hTms) (μ := ρ i) (hu := MeasurableSet.univ),
      (hρp i).measure_univ]⟩
  set Sf : ν.support → PSpace Ω := fun i ↦ ⟨⟨(fixpoint ⟨T, (ρ i).cast T.ms⟩).1.ms,
    (fixpoint ⟨T, (ρ i).cast T.ms⟩).2⟩, hTprob i⟩ with hSf
  have hSfms : ∀ i, (Sf i).ms = (fixpoint ⟨T, P₁.μ.cast T.ms⟩).1.ms := fun i ↦
    congrArg ProbTree.ms (fixpoint_fst_congr' ((ρ i).cast T.ms) (P₁.μ.cast T.ms))
  have h𝓜Sf : ∀ i, 𝓜 ≤ (Sf i).ms := fun i ↦ by rw [hSfms i]; exact h𝓜T
  -- the atoms a fibre gives no mass: dead after `C`, or where the fibre's density vanishes
  set N : ν.support → Set Ω := fun i ↦ {ρ' | ρ i (μ₁.atomOf ρ').1 = 0} with hN
  have hN𝓜 : ∀ i, MeasurableSet[𝓜] (N i) := by
    intro i
    have hset : N i = deadAtoms μ₁ h₁ ∪ {ρ' | g i ρ' = 0} := by
      ext ρ'
      exact withDensity_atom_eq_zero_iff μ₁ h₁ ((hgm i).mono hmP le_rfl) ρ'
    rw [hset]
    refine MeasurableSet.union ?_ ?_
    · exact (le_sup_right : freshMs μ₀ (Cb >>= Fb) ≤ 𝓜) _
        (freshMs_le_freshMs_bind μ₀ Cb Fb _ (deadAtoms_run_measurableSet μ₀ hvalid Cb))
    · exact (le_trans le_sup_left le_sup_left : mm.ms ≤ 𝓜) _
        ((hgm i) (measurableSet_singleton (0 : ENNReal)))
  have hNP₁ : ∀ i, MeasurableSet[P₁.ms] (N i) := fun i ↦
    measurableSet_preimage_atomOf μ₁ h₁ {A | ρ i A.1 = 0}
  have hNnull : ∀ i, ρ i (N i) = 0 := fun i ↦
    measure_preimage_atomOf_null' μ₁ h₁ (ρ i) {A | ρ i A.1 = 0} fun _ hA ↦ hA
  -- the fibre witnesses live on `𝓜`
  have hbv𝓜 : ∀ i, msOf (bv i) ≤ 𝓜 := by
    intro i
    refine le_trans (hbvms i) (sup_le ?_ ?_)
    · refine le_trans (msOf_mono (hRi_le i)) ?_
      rw [msOf_mul (q := (κ i : PSpace Ω)) hr rfl (hvRK i), sup_comm r.ms]
      exact le_sup_left
    · show freshMs (BoundedFootprintPsp.reweight μ₁ h₁ (ρ i) (hρp i)) (Fb i) ≤ 𝓜
      rw [freshMs_of_valid _ reweight_valid,
        prunedPath_fibre μ₀ hvalid Cb Fb (ρ i) (hρp i) i (hXv i) (hac' i)]
      refine le_trans (comap_ite_le _ _ _) (sup_le ?_ ?_)
      · exact MeasurableSpace.generateFrom_le fun _ ht ↦ by
          rw [Set.mem_singleton_iff] at ht; rw [ht]; exact hN𝓜 i
      · show MeasurableSpace.comap ((Option.map fun π ↦ π.drop (runPath Cb (tapeOf π)).length)
            ∘ prunedPath μ₀ hvalid (Cb >>= Fb)) ⊤ ≤ 𝓜
        rw [← MeasurableSpace.comap_comp]
        refine le_trans (MeasurableSpace.comap_mono le_top) ?_
        rw [← freshMs_of_valid μ₀ hvalid (Cb >>= Fb)]
        exact le_sup_right
  -- each fibre witness sits below the fibre's version of the second stage
  have hfibre_psp : ∀ i : ν.support, (run (F i) (τ i)).1.psp = .some ⟨⟨(fixpoint ⟨toTree (τ i)
      (prunePrograms (τ i) (hτvalid i) (fun _ ↦ Fb i)),
      (ValidPSp.toPSpace ⟨(τ i).psp, hτvalid i⟩).μ.cast
        (toTree (τ i) (prunePrograms (τ i) (hτvalid i) (fun _ ↦ Fb i))).ms⟩).1.ms,
      (fixpoint ⟨toTree (τ i) (prunePrograms (τ i) (hτvalid i) (fun _ ↦ Fb i)),
      (ValidPSp.toPSpace ⟨(τ i).psp, hτvalid i⟩).μ.cast
        (toTree (τ i) (prunePrograms (τ i) (hτvalid i) (fun _ ↦ Fb i))).ms⟩).2⟩,
      inferInstance⟩ := fun i ↦ run_psp_eq (τ i) (hτvalid i) (Fb i)
  have hbp' : ∀ i : ν.support, ∃ p : PSpace Ω, (bv i : PSp Ω) = .some p := fun i ↦
    Option.ne_none_iff_exists'.mp (PSp.valid_def.mp (hbvv i))
  choose bp hbp using hbp'
  have hbp𝓜 : ∀ i : ν.support, (bp i).ms ≤ 𝓜 := fun i ↦ by
    rw [← msOf_of_val (hbp i)]; exact hbv𝓜 i
  have hTi : ∀ i : ν.support, toTree (τ i) (prunePrograms (τ i) (hτvalid i) (fun _ ↦ Fb i))
      = toTree μ₁ (prunePrograms (τ i) (hτvalid i) (fun _ ↦ Fb i)) := fun i ↦ toTree_reweight _
  have hTims : ∀ i : ν.support,
      (toTree (τ i) (prunePrograms (τ i) (hτvalid i) (fun _ ↦ Fb i))).ms = P₁.ms := by
    intro i
    rw [hTi i]
    exact (toTree_ms_eq μ₁ _).trans (μ₁.sigmaAgrees h₁).symm
  have hag : ∀ i : ν.support,
      AgreeOffNull T (toTree (τ i) (prunePrograms (τ i) (hτvalid i) (fun _ ↦ Fb i)))
        ((ρ i).cast T.ms) := by
    intro i
    rw [hTi i]
    refine agreeOffNull_toTree_go μ₁ h₁ _ _ (ρ i) (fun A hA ↦ ?_) []
      (fun _ h' ↦ List.prefix_nil.mp h') ⟨T, (ρ i).cast T.ms⟩ rfl (fun q hq ↦ ?_)
    · simp only [prunePrograms]
      split_ifs with h0
      · exact absurd h0 hA
      · have hmem : tapeOf (μ₁.prefixes A) ∈ A.1 := by
          rw [atom_eq_prefixEqEvent]; exact mem_prefixEqEvent_tapeOf _
        have hatom : μ₁.atomOf (tapeOf (μ₁.prefixes A)) = A := μ₁.atomOf_eq hmem
        have := hXv i (tapeOf (μ₁.prefixes A)) (by rw [hatom]; exact hA)
        show Fb ((run Cb μ₀).2 A) = Fb i
        rw [← this]
        show Fb ((run Cb μ₀).2 A) = Fb ((run Cb μ₀).2 (μ₁.atomOf (tapeOf (μ₁.prefixes A))))
        rw [hatom]
    · rw [List.nil_append]
      exact Measure.le_preserves_measure (h := le_of_eq hTms) (μ := ρ i)
        (hu := measurableSet_prefixEqEvent hq)
  have hbpSf : ∀ i : ν.support, bp i ≤ Sf i := by
    intro i
    have hbvle : bv i ≤ (run (F i) (τ i)).1.toSpace :=
      le_trans (le_mul_of_one_le PSp.one_le) (hbvc i)
    have hbvle' : (.some (bp i) : PSp Ω) ≤ (run (F i) (τ i)).1.psp := by
      rw [← hbp i]; exact hbvle
    rw [hfibre_psp i] at hbvle'
    have hle₂ := WithTop.coe_le_coe.1 hbvle'
    refine PSpace.le_of_ms_le (le_trans (hbp𝓜 i) (h𝓜Sf i)) fun E hE ↦ ?_
    show (fixpoint ⟨T, (ρ i).cast T.ms⟩).2 E = (bp i).μ E
    rw [MeasureOnSpace.le_preserves_measure hle₂ hE]
    refine fixpoint_agreeOffNull ((ρ i).cast T.ms) _ (hag i) (fun E hE ↦ ?_) E
      (h𝓜Sf i _ (hbp𝓜 i _ hE)) (hle₂.1 _ hE)
    rw [Measure.le_preserves_measure (h := le_of_eq hTms) (μ := ρ i) (hu := hE), hτP i]
    show ρ i E = ((ρ i).cast _) E
    rw [Measure.le_preserves_measure (h := le_of_eq (hTims i)) (μ := ρ i)
      (hu := by rw [hTims i, ← hTms]; exact hE)]
  -- the conditioning: the second stage at each fibre's measure, trimmed to `𝓜`
  have hfib_meas : ∀ v, ∃ ν' : Measure[𝓜] Ω, IsProbabilityMeasure ν' ∧
      ∀ hv : v ∈ ν.support, ν' = (@PSpace.trim Ω (Sf ⟨v, hv⟩) 𝓜 (h𝓜Sf ⟨v, hv⟩)).μ := by
    intro v
    by_cases hv : v ∈ ν.support
    · exact ⟨_, (@PSpace.trim Ω (Sf ⟨v, hv⟩) 𝓜 (h𝓜Sf ⟨v, hv⟩)).2, fun _ ↦ rfl⟩
    · exact ⟨B.μ, B.2, fun h ↦ absurd h hv⟩
  choose κ'f hκ'p hκ'f' using hfib_meas
  have hκ'f : ∀ i : ν.support, κ'f i = (@PSpace.trim Ω (Sf i) 𝓜 (h𝓜Sf i)).μ :=
    fun i ↦ hκ'f' i i.2
  obtain ⟨κ', hκ'⟩ : ∃ κ' : TrivialMarkovKernel α B, ∀ v, κ'.1 v = κ'f v := by
    letI : MeasurableSpace α := ⊤
    exact ⟨⟨⟨κ'f, measurable_from_top⟩, ⟨hκ'p⟩⟩, fun _ ↦ rfl⟩
  have hmix' : B.μ = (ν.toMeasureWithMs ⊤).bind κ' := by
    apply @Measure.ext Ω 𝓜
    intro G hG
    refine Eq.trans ?_ (bind_apply_support ν κ'.1 hG).symm
    show (MeasureOnSpace.trim h𝓜S).μ G = _
    rw [MeasureOnSpace.trim_eq h𝓜S hG, hSμ G (h𝓜S G hG)]
    have hf : ∀ E, MeasurableSet[T.ms] E →
        (P₁.μ.cast T.ms) E = ∑' i : ν.support, (HSMul.hSMul (ν i) ((ρ i).cast T.ms)) E := by
      intro E hE
      rw [Measure.le_preserves_measure (h := le_of_eq hTms) (μ := P₁.μ) (hu := hE),
        hP₁mix E (by rw [← hTms]; exact hE)]
      refine tsum_congr fun i ↦ ?_
      rw [Measure.smul_apply, smul_eq_mul,
        Measure.le_preserves_measure (h := le_of_eq hTms) (μ := ρ i) (hu := hE)]
    rw [fixpoint_sum' (P₁.μ.cast T.ms) (fun i : ν.support ↦ HSMul.hSMul (ν i) ((ρ i).cast T.ms))
      hf (h𝓜T G hG)]
    refine tsum_congr fun i ↦ ?_
    rw [hκ' i, hκ'f i]
    show _ = _ * (MeasureOnSpace.trim (h𝓜Sf i)).μ G
    rw [MeasureOnSpace.trim_eq (h𝓜Sf i) hG,
      measure_congr_tree (fixpoint_smul (ν i) ((ρ i).cast T.ms)) G]
    show (HSMul.hSMul (ν i) (fixpoint ⟨T, (ρ i).cast T.ms⟩).2) G = _
    rw [Measure.smul_apply, smul_eq_mul]
  show own (⟨(B : PSp Ω), hbfB⟩ : BoundedFootprintSpace Bool)
    ⊢ 𝒞⟨ν⟩ v; Q v (result (run (Cb >>= Fb) μ₀))
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
  -- the fibre's space is `Sf i` trimmed to `𝓜`; the witness sits below it, and the null set
  -- `N i` makes the fibre's result and the composite's agree
  have hbpκ : bp i ≤ (κ' i : PSpace Ω) := by
    refine PSpace.le_of_ms_le (S := (κ' i : PSpace Ω)) (hbp𝓜 i) fun E hE ↦ ?_
    show κ'.1 i E = (bp i).μ E
    rw [hκ' i, hκ'f i]
    show (MeasureOnSpace.trim (h𝓜Sf i)).μ E = _
    rw [MeasureOnSpace.trim_eq (h𝓜Sf i) (hbp𝓜 i E hE)]
    exact (MeasureOnSpace.le_preserves_measure (hbpSf i) hE).symm
  have hNκ : MeasurableSet[(κ' i : PSpace Ω).ms] (N i) := hN𝓜 i
  have hNκ0 : (κ' i : PSpace Ω).μ (N i) = 0 := by
    show κ'.1 i (N i) = 0
    rw [hκ' i, hκ'f i]
    show (MeasureOnSpace.trim (h𝓜Sf i)).μ (N i) = 0
    rw [MeasureOnSpace.trim_eq (h𝓜Sf i) (hN𝓜 i)]
    show (fixpoint ⟨T, (ρ i).cast T.ms⟩).2 (N i) = 0
    rw [fixpoint_preserves' _ (by rw [hTms]; exact hNP₁ i),
      Measure.le_preserves_measure (h := le_of_eq hTms) (μ := ρ i)
        (hu := by rw [hTms]; exact hNP₁ i)]
    exact hNnull i
  have hvκ : ✓(((κ' i : PSpace Ω)) : PSp Ω) := PSp.valid_def.mpr (Option.some_ne_none _)
  have hbfPN : HasBoundedFootprint (((@PSpace.trim Ω (κ' i : PSpace Ω)
      (MeasurableSpace.generateFrom {N i}) (PSpace.generateFrom_singleton_le hNκ) : PSpace Ω)) : PSp Ω) :=
    hasBoundedFootprint_mono hvκ (WithTop.coe_le_coe.2 (PSpace.trim_le _)) hk'
  have hmul : (⟨_, hbfPN⟩ : BoundedFootprintSpace Bool) * bv i
      ≤ (⟨(((κ' i : PSpace Ω)) : PSp Ω), hk'⟩ : BoundedFootprintSpace Bool) := by
    show PSp.mul (.some _) (bv i : PSp Ω) ≤ .some (κ' i : PSpace Ω)
    rw [hbp i]
    exact PSpace.nullSpace_mul_le hNκ hNκ0 hbpκ
  refine entails_trans (own_mono hmul) (entails_trans own_mul_sep ?_)
  refine entails_trans (sep_mono (nullSpace_liftPred hNκ hNκ0 (fun ρ' hρ' ↦ ?_) hbfPN)
    (hbvQ i)) (hQ i _ _)
  by_contra hN'
  exact hρ' (result_run_fibre μ₀ hvalid Cb Fb (ρ i) (hρp i) i (hXv i) (hac' i) hN')

end

end Foxglove
