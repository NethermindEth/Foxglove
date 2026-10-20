module

public import Foxglove.Rules.WP

@[expose] public section
namespace Foxglove

open ProbSpace
open Iris OrderedUnitalResourceAlgebra
open UpperSetBI
open Iris BI UpperSetBI OURAProp

noncomputable section

/-! # The core of `CWPSwap` -/

set_option linter.style.haveILetI false in
set_option maxHeartbeats 1000000 in
open Interp Interp.ProbTree Interp.ProbTree.BoundedFootprintPsp ProbabilityTheory MeasureTheory in
/-- `CWPSwap`, semantically.  Reweight the ambient along each fibre of the conditioning,
run there, and mix the runs back.

Every fibre's witness lives on the one σ-algebra `m ⊔ R ⊔ fresh` (`wp`'s locality clause),
which is independent of the frame because `m ⊗ R` was and fresh randomness is independent of
everything prior (`run_fresh`).  The fibres of the conditioning produced are the run's own
tree, run with each fibre's measure and trimmed to that σ-algebra: their mixture is the real
run (`fixpoint_sum`), a fibre's own run differs from it only at the atoms the fibre gives no
mass (`fixpoint_agreeOffNull`), and that is also where the fibre's result may differ from the
run's (`result_run_reweight`), so `AEProper` carries `Q v` across through a null-set space
(`PSpace.nullSpace_mul_le`). -/
lemma CWPSwap_core {α β : Type} {m' : Type → Type} [Interp.BernoulliInterpretable m']
    [Inhabited α] {C : m' α} {μ : PMF β} {Q : β → RV α → FProp}
    (hQ : ∀ v, AEProper (Q v))
    (m : PSpace Ω) (κ : TrivialMarkovKernel β m)
    (hmix : m.μ = (μ.toMeasureWithMs ⊤).bind κ)
    (hbf : HasBoundedFootprint (m : PSp Ω)) (R : BoundedFootprintSpace Bool)
    (hfib : ∀ v ∈ μ.support, ∀ hk : HasBoundedFootprint ((κ v : PSpace Ω) : PSp Ω),
      own (R * ⟨((κ v : PSpace Ω) : PSp Ω), hk⟩) ⊢ wp C (Q v)) :
    own ((⟨(m : PSp Ω), hbf⟩ : BoundedFootprintSpace Bool) * R)
      ⊢ wp C (fun X ↦ 𝒞⟨μ⟩ v; Q v X) := by
  set Cb : BernoulliM α := BernoulliInterpretable.interp C with hCb
  set M : BoundedFootprintSpace Bool := ⟨(m : PSp Ω), hbf⟩ with hM
  have hmp := m.2
  intro a hva ha μ₀ c hvalid hle
  have ha' : M * R ≤ a := ha
  -- the ambient, and the spaces sitting in it
  set P₀ : PSpace Ω := ValidPSp.toPSpace ⟨μ₀.psp, hvalid⟩ with hP₀
  have hμ₀P : μ₀.psp = .some P₀ := (Option.some_get _).symm
  have hvμ₀ : ✓(μ₀.toSpace) := hvalid
  have hle_amb : ∀ {x : BoundedFootprintSpace Bool} {p : PSpace Ω},
      x ≤ μ₀.toSpace → (x : PSp Ω) = .some p → p ≤ P₀ := by
    intro x p hx hp
    have h : (.some p : PSp Ω) ≤ .some P₀ := by rw [← hp, ← hμ₀P]; exact hx
    exact WithTop.coe_le_coe.1 h
  have hMRc : (M * R) * c ≤ μ₀.toSpace := le_trans (mul_le_mul_right_le ha' c) hle
  have hMD : M * (R * c) ≤ μ₀.toSpace := by rw [← mul_assoc]; exact hMRc
  have hvMRc : ✓((M * R) * c) := valid_mono hMRc hvμ₀
  have hvMR : ✓(M * R) := valid_mul_l hvMRc
  have hvR : ✓R := valid_mul_r hvMR
  have hvc : ✓c := valid_mul_r hvMRc
  have hvMD : ✓(M * (R * c)) := valid_mono hMD hvμ₀
  have hvD : ✓(R * c) := valid_mul_r hvMD
  obtain ⟨d, hd⟩ : ∃ d : PSpace Ω, ((R * c : BoundedFootprintSpace Bool) : PSp Ω) = .some d :=
    Option.ne_none_iff_exists'.mp (PSp.valid_def.mp hvD)
  obtain ⟨r, hr⟩ : ∃ r : PSpace Ω, (R : PSp Ω) = .some r :=
    Option.ne_none_iff_exists'.mp (PSp.valid_def.mp hvR)
  obtain ⟨c', hc'⟩ : ∃ c' : PSpace Ω, (c : PSp Ω) = .some c' :=
    Option.ne_none_iff_exists'.mp (PSp.valid_def.mp hvc)
  obtain ⟨s, hs⟩ : ∃ s : PSpace Ω, ((M * (R * c) : BoundedFootprintSpace Bool) : PSp Ω) = .some s :=
    Option.ne_none_iff_exists'.mp (PSp.valid_def.mp hvMD)
  obtain ⟨y, hy⟩ : ∃ y : PSpace Ω, ((M * R : BoundedFootprintSpace Bool) : PSp Ω) = .some y :=
    Option.ne_none_iff_exists'.mp (PSp.valid_def.mp hvMR)
  obtain ⟨w, hw⟩ : ∃ w : PSpace Ω, (((M * R) * c : BoundedFootprintSpace Bool) : PSp Ω) = .some w :=
    Option.ne_none_iff_exists'.mp (PSp.valid_def.mp hvMRc)
  have hsmd : s =ᵢ m ⊕ᵢ d := by
    apply PSp.mul_inversion
    have h := hs
    rw [show ((M * (R * c) : BoundedFootprintSpace Bool) : PSp Ω)
      = PSp.mul (M : PSp Ω) ((R * c : BoundedFootprintSpace Bool) : PSp Ω) from rfl, hd] at h
    exact h
  have hymr : y =ᵢ m ⊕ᵢ r := by
    apply PSp.mul_inversion
    have h := hy
    rw [show ((M * R : BoundedFootprintSpace Bool) : PSp Ω)
      = PSp.mul (M : PSp Ω) (R : PSp Ω) from rfl, hr] at h
    exact h
  have hwyc : w =ᵢ y ⊕ᵢ c' := by
    apply PSp.mul_inversion
    have h := hw
    rw [show (((M * R) * c : BoundedFootprintSpace Bool) : PSp Ω)
      = PSp.mul ((M * R : BoundedFootprintSpace Bool) : PSp Ω) (c : PSp Ω) from rfl, hy, hc'] at h
    exact h
  have hsP : s ≤ P₀ := hle_amb hMD hs
  have hwP : w ≤ P₀ := hle_amb hMRc hw
  have hyP : y ≤ P₀ := le_trans (PSpace.le_of_isIndependentProduct_left hwyc) hwP
  have hcP : c' ≤ P₀ := le_trans (PSpace.le_of_isIndependentProduct_right hwyc) hwP
  have hm_le_P : m ≤ P₀ := le_trans (PSpace.le_of_isIndependentProduct_left hsmd) hsP
  have hmP : m.ms ≤ P₀.ms := hm_le_P.1
  have hdP : d.ms ≤ P₀.ms := le_trans (PSpace.le_of_isIndependentProduct_right hsmd).1 hsP.1
  have hdp := d.2
  -- the fibres, as reweightings of the ambient
  haveI : Countable μ.support := μ.support_countable.to_subtype
  have hac : ∀ i : μ.support, κ.1 i ≪ m.μ := fun i ↦ kernel_fibre_ac κ hmix i.2
  haveI hκp : ∀ i : μ.support, IsProbabilityMeasure (κ.1 i) :=
    fun i ↦ κ.2.isProbabilityMeasure i
  set g : μ.support → Ω → ENNReal := fun i ↦ (κ.1 i).rnDeriv m.μ with hg
  have hgm : ∀ i, Measurable[m.ms] (g i) := fun i ↦ Measure.measurable_rnDeriv _ _
  set ρ : μ.support → Measure[P₀.ms] Ω := fun i ↦ P₀.μ.withDensity (g i) with hρ
  have hρrect : ∀ i E, MeasurableSet[d.ms] E → ∀ F, MeasurableSet[m.ms] F →
      ρ i (E ∩ F) = d.μ E * κ.1 i F :=
    fun i E hE F hF ↦ PSpace.withDensity_rect hsmd hsP (κ.1 i) (hac i) hE hF
  haveI hρp : ∀ i, IsProbabilityMeasure (ρ i) := fun i ↦ ⟨by
    have h := hρrect i Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ
    rwa [Set.inter_univ, hdp.measure_univ, (hκp i).measure_univ, one_mul] at h⟩
  have hκmix : ∀ F, MeasurableSet[m.ms] F → m.μ F = ∑' i : μ.support, μ i * κ.1 i F := by
    intro F hF; rw [hmix]; exact bind_apply_support μ κ.1 hF
  have hP₀mix : ∀ E, MeasurableSet[P₀.ms] E → P₀.μ E = ∑' i : μ.support, μ i * ρ i E :=
    fun E hE ↦ PSpace.withDensity_mixture hm_le_P (fun i : μ.support ↦ μ i)
      (fun i : μ.support ↦ κ.1 i) hac hκmix hE
  have hρac : ∀ i, ρ i ≪ P₀.μ := fun i ↦ withDensity_absolutelyContinuous _ _
  have hac' : ∀ i : μ.support, ∀ ρ', P₀.μ (μ₀.atomOf ρ').1 = 0 → ρ i (μ₀.atomOf ρ').1 = 0 :=
    fun i ρ' h0 ↦ hρac i h0
  -- the reweighted footprints
  set τ : μ.support → BoundedFootprintPsp :=
    fun i ↦ BoundedFootprintPsp.reweight μ₀ hvalid (ρ i) (hρp i) with hτ
  have hτpsp : ∀ i, (τ i).psp = .some ⟨⟨P₀.ms, ρ i⟩, hρp i⟩ := fun i ↦ rfl
  have hτvalid : ∀ i, ✓(τ i).psp := fun i ↦ reweight_valid
  have hτP : ∀ i, ValidPSp.toPSpace ⟨(τ i).psp, hτvalid i⟩ = ⟨⟨P₀.ms, ρ i⟩, hρp i⟩ :=
    fun i ↦ ValidPSp.toPSpace_eq _ (hτpsp i)
  -- each fibre, with the frame, sits in its reweighted ambient
  have hvm : ✓((m : PSp Ω)) := PSp.valid_def.mpr (Option.some_ne_none _)
  have hk : ∀ i : μ.support, HasBoundedFootprint (((κ i : PSpace Ω)) : PSp Ω) := fun i ↦
    hasBoundedFootprint_congr hvm (PSp.valid_def.mpr (Option.some_ne_none _)) rfl hbf
  set K : μ.support → BoundedFootprintSpace Bool := fun i ↦ ⟨((κ i : PSpace Ω) : PSp Ω), hk i⟩
    with hK
  have hKD : ∀ i, K i * (R * c) ≤ (τ i).toSpace := by
    intro i
    have hsup : m.ms ⊔ d.ms ≤ P₀.ms := sup_le hmP hdP
    have hX : @PSpace.trim Ω ⟨⟨P₀.ms, ρ i⟩, hρp i⟩ (m.ms ⊔ d.ms) hsup
        =ᵢ (κ i : PSpace Ω) ⊕ᵢ d := by
      refine ⟨rfl, fun F hF E hE ↦ ?_⟩
      have h1 : ρ i (F ∩ E) = κ.1 i F * d.μ E := by
        rw [Set.inter_comm, hρrect i E hE F hF, mul_comm]
      have h2 := MeasureOnSpace.trim_eq (p := ⟨P₀.ms, ρ i⟩) hsup
        (((le_sup_left : m.ms ≤ _) _ hF).inter ((le_sup_right : d.ms ≤ _) _ hE))
      exact h2.trans h1
    show PSp.mul (.some (κ i : PSpace Ω)) ((R * c : BoundedFootprintSpace Bool) : PSp Ω)
      ≤ (τ i).psp
    rw [hd, hτpsp]
    exact (le_of_eq (mul_respect_independentProduct hX)).trans
      (WithTop.coe_le_coe.2 (PSpace.trim_le (p := ⟨⟨P₀.ms, ρ i⟩, hρp i⟩) hsup))
  have hRKc : ∀ i, (R * K i) * c ≤ (τ i).toSpace := by
    intro i; rw [mul_comm R, mul_assoc]; exact hKD i
  have hvRK : ∀ i, ✓(R * K i) := fun i ↦ valid_mul_l (valid_mono (hRKc i) (hτvalid i))
  -- run every fibre
  have hfib' : ∀ i : μ.support, ∃ b : BoundedFootprintSpace Bool,
      b * c ≤ (run C (τ i)).1.toSpace ∧ ✓b ∧
        msOf b ≤ msOf (R * K i) ⊔ freshMs (τ i) Cb ∧
        (own b ⊢ Q i (result (run C (τ i)))) :=
    fun i ↦ hfib i i.2 (hk i) (R * K i) (hvRK i) (le_refl (R * K i)) (τ i) c (hτvalid i) (hRKc i)
  choose bv hbvc hbvv hbvms hbvQ using hfib'
  -- the run, and its tree
  obtain ⟨S, hS, hP₀S, hSmeas, hSpres, -⟩ := run_const μ₀ Cb hvalid
  set T : ProbTree α := toTree μ₀ (prunePrograms μ₀ hvalid (fun _ ↦ Cb)) with hT
  have hTms : T.ms = P₀.ms := by rw [hT, toTree_ms_eq, μ₀.sigmaAgrees hvalid]
  have hval := Option.some_injective _ ((run_psp_eq μ₀ hvalid Cb).symm.trans hS)
  have hSms : S.ms = (fixpoint ⟨T, P₀.μ.cast T.ms⟩).1.ms := by rw [← hval]
  have hSμ : ∀ G, S.μ G = (fixpoint ⟨T, P₀.μ.cast T.ms⟩).2 G := fun G ↦ by rw [← hval]
  have hfreshS := run_fresh μ₀ Cb hvalid hS
  -- the one σ-algebra every witness lives on
  set 𝓜 : MeasurableSpace Ω := (m.ms ⊔ r.ms) ⊔ freshMs μ₀ Cb with h𝓜
  have hy𝓜 : y.ms = m.ms ⊔ r.ms := hymr.1
  have h𝓜S : 𝓜 ≤ S.ms := sup_le (hy𝓜 ▸ le_trans hyP.1 hP₀S) hfreshS.1
  have h𝓜T : 𝓜 ≤ (fixpoint ⟨T, P₀.μ.cast T.ms⟩).1.ms := by rw [← hSms]; exact h𝓜S
  have hmsRK : ∀ i, msOf (R * K i) = r.ms ⊔ m.ms := fun i ↦
    msOf_mul (q := (κ i : PSpace Ω)) hr rfl (hvRK i)
  -- the atoms a fibre gives no mass: dead already, or where the fibre's density vanishes
  set N : μ.support → Set Ω := fun i ↦ {ρ' | ρ i (μ₀.atomOf ρ').1 = 0} with hN
  have hN𝓜 : ∀ i, MeasurableSet[𝓜] (N i) := by
    intro i
    have hset : N i = deadAtoms μ₀ hvalid ∪ {ρ' | g i ρ' = 0} := by
      ext ρ'
      exact withDensity_atom_eq_zero_iff μ₀ hvalid ((hgm i).mono hmP le_rfl) ρ'
    rw [hset]
    refine MeasurableSet.union ?_ ?_
    · exact (le_sup_right : freshMs μ₀ Cb ≤ 𝓜) _ (deadAtoms_measurableSet_freshMs μ₀ hvalid Cb)
    · exact (le_trans le_sup_left le_sup_left : m.ms ≤ 𝓜) _
        ((hgm i) (measurableSet_singleton (0 : ENNReal)))
  have hNP₀ : ∀ i, MeasurableSet[P₀.ms] (N i) := fun i ↦
    measurableSet_preimage_atomOf μ₀ hvalid {A | ρ i A.1 = 0}
  have hNnull : ∀ i, ρ i (N i) = 0 := fun i ↦
    measure_preimage_atomOf_null' μ₀ hvalid (ρ i) {A | ρ i A.1 = 0} fun _ hA ↦ hA
  -- the fibre witnesses live on `𝓜`: a fibre's fresh σ-algebra is the run's, plus `N i`
  have hbv𝓜 : ∀ i, msOf (bv i) ≤ 𝓜 := by
    intro i
    refine le_trans (hbvms i) (sup_le ?_ ?_)
    · rw [hmsRK i, sup_comm r.ms]
      exact le_sup_left
    · show freshMs (BoundedFootprintPsp.reweight μ₀ hvalid (ρ i) (hρp i)) Cb ≤ 𝓜
      rw [freshMs_of_valid _ reweight_valid,
        prunedPath_reweight μ₀ hvalid (ρ i) (hρp i) Cb (hac' i)]
      refine le_trans (comap_ite_le _ _ _) (sup_le ?_ ?_)
      · exact MeasurableSpace.generateFrom_le fun _ ht ↦ by
          rw [Set.mem_singleton_iff] at ht; rw [ht]; exact hN𝓜 i
      · rw [← freshMs_of_valid μ₀ hvalid Cb]
        exact le_sup_right
  -- the witness: the run, trimmed to `𝓜`
  set B : PSpace Ω := @PSpace.trim Ω S 𝓜 h𝓜S with hB
  have hvS : ✓((run Cb μ₀).1.psp) := by rw [hS]; exact Option.some_ne_none _
  have hbfB : HasBoundedFootprint ((B : PSp Ω)) :=
    hasBoundedFootprint_mono hvS (by rw [hS]; exact WithTop.coe_le_coe.2 (PSpace.trim_le h𝓜S))
      (hasBoundedFootprint_of_tree _)
  have hP₀S' : P₀ ≤ S := PSpace.le_of_ms_le hP₀S fun E hE ↦ hSpres hE
  have hcS : c' ≤ S := le_trans hcP hP₀S'
  have hmrS : m.ms ⊔ r.ms ≤ S.ms := by rw [← hy𝓜]; exact le_trans hyP.1 hP₀S
  -- `𝓜` is independent of the frame: `m ⊗ R` was, and the fresh bits are
  have hrect : ∀ G, MeasurableSet[𝓜] G → ∀ E, MeasurableSet[c'.ms] E →
      S.μ (G ∩ E) = S.μ G * c'.μ E := by
    intro G hG E hE
    refine PSpace.indep_sup_of_rect hmrS hfreshS.1 hcS ?_ hE G hG
    intro A hA F hF E hE
    have hAy : MeasurableSet[y.ms] A := by rw [hy𝓜]; exact hA
    have hAP : MeasurableSet[P₀.ms] A := hyP.1 _ hAy
    have hEP : MeasurableSet[P₀.ms] E := hcP.1 _ hE
    have h1 : S.μ (A ∩ F ∩ E) = S.μ F * P₀.μ (A ∩ E) := by
      rw [show A ∩ F ∩ E = F ∩ (A ∩ E) by ext; simp only [Set.mem_inter_iff]; tauto]
      exact hfreshS.2 hF (hAP.inter hEP)
    have h2 : S.μ (A ∩ F) = S.μ F * P₀.μ A := by
      rw [Set.inter_comm]; exact hfreshS.2 hF hAP
    have hAEw : MeasurableSet[w.ms] (A ∩ E) :=
      hwyc.1.symm.le _ (mem_sup_inter y.ms c'.ms hAy hE)
    have h3 : P₀.μ (A ∩ E) = y.μ A * c'.μ E := by
      rw [← MeasureOnSpace.le_preserves_measure hwP hAEw]
      exact hwyc.2 A hAy E hE
    have h4 : P₀.μ A = y.μ A := (MeasureOnSpace.le_preserves_measure hyP hAy).symm
    rw [h1, h2, h3, h4, mul_assoc]
  refine ⟨⟨(B : PSp Ω), hbfB⟩, ?_, PSp.valid_def.mpr (Option.some_ne_none _), ?_, ?_⟩
  · show PSp.mul (.some B) (c : PSp Ω) ≤ (run Cb μ₀).1.psp
    rw [hc', hS]
    exact PSpace.mul_trim_le h𝓜S hcS hrect
  · rw [msOf_of_val (p := B) rfl]
    show (m.ms ⊔ r.ms) ⊔ freshMs μ₀ Cb ≤ msOf a ⊔ freshMs μ₀ Cb
    refine sup_le_sup_right ?_ _
    rw [← hy𝓜, ← msOf_of_val hy]
    exact msOf_mono ha'
  -- the fibres of the conditioning: the run's tree, at each fibre's measure
  have hTprob : ∀ i, IsProbabilityMeasure (fixpoint ⟨T, (ρ i).cast T.ms⟩).2 := fun i ↦ ⟨by
    rw [fixpoint_preserves' _ MeasurableSet.univ,
      Measure.le_preserves_measure (h := le_of_eq hTms) (μ := ρ i) (hu := MeasurableSet.univ),
      (hρp i).measure_univ]⟩
  set Sf : μ.support → PSpace Ω := fun i ↦ ⟨⟨(fixpoint ⟨T, (ρ i).cast T.ms⟩).1.ms,
    (fixpoint ⟨T, (ρ i).cast T.ms⟩).2⟩, hTprob i⟩ with hSf
  have hSfms : ∀ i, (Sf i).ms = (fixpoint ⟨T, P₀.μ.cast T.ms⟩).1.ms := fun i ↦
    congrArg ProbTree.ms (fixpoint_fst_congr' ((ρ i).cast T.ms) (P₀.μ.cast T.ms))
  have h𝓜Sf : ∀ i, 𝓜 ≤ (Sf i).ms := fun i ↦ by rw [hSfms i]; exact h𝓜T
  -- each fibre witness sits below the fibre's version of the run: the fibre's own run
  -- differs from it only at the atoms the fibre gives no mass
  have hfibre_psp : ∀ i : μ.support, (run C (τ i)).1.psp = .some ⟨⟨(fixpoint ⟨toTree (τ i)
      (prunePrograms (τ i) (hτvalid i) (fun _ ↦ Cb)),
      (ValidPSp.toPSpace ⟨(τ i).psp, hτvalid i⟩).μ.cast
        (toTree (τ i) (prunePrograms (τ i) (hτvalid i) (fun _ ↦ Cb))).ms⟩).1.ms,
      (fixpoint ⟨toTree (τ i) (prunePrograms (τ i) (hτvalid i) (fun _ ↦ Cb)),
      (ValidPSp.toPSpace ⟨(τ i).psp, hτvalid i⟩).μ.cast
        (toTree (τ i) (prunePrograms (τ i) (hτvalid i) (fun _ ↦ Cb))).ms⟩).2⟩,
      inferInstance⟩ := fun i ↦ run_psp_eq (τ i) (hτvalid i) Cb
  have hbp' : ∀ i : μ.support, ∃ p : PSpace Ω, (bv i : PSp Ω) = .some p := fun i ↦
    Option.ne_none_iff_exists'.mp (PSp.valid_def.mp (hbvv i))
  choose bp hbp using hbp'
  have hbp𝓜 : ∀ i : μ.support, (bp i).ms ≤ 𝓜 := fun i ↦ by
    rw [← msOf_of_val (hbp i)]; exact hbv𝓜 i
  have hTi : ∀ i : μ.support, toTree (τ i) (prunePrograms (τ i) (hτvalid i) (fun _ ↦ Cb))
      = toTree μ₀ (prunePrograms (τ i) (hτvalid i) (fun _ ↦ Cb)) := fun i ↦ toTree_reweight _
  have hTims : ∀ i : μ.support,
      (toTree (τ i) (prunePrograms (τ i) (hτvalid i) (fun _ ↦ Cb))).ms = P₀.ms := by
    intro i
    rw [hTi i]
    exact (toTree_ms_eq μ₀ _).trans (μ₀.sigmaAgrees hvalid).symm
  have hag : ∀ i : μ.support,
      AgreeOffNull T (toTree (τ i) (prunePrograms (τ i) (hτvalid i) (fun _ ↦ Cb)))
        ((ρ i).cast T.ms) := by
    intro i
    rw [hTi i]
    refine agreeOffNull_toTree_go μ₀ hvalid _ _ (ρ i) (fun X hX ↦ ?_) []
      (fun _ h' ↦ List.prefix_nil.mp h') ⟨T, (ρ i).cast T.ms⟩ rfl (fun q hq ↦ ?_)
    · have h0 : ¬ P₀.μ X.1 = 0 := fun h0 ↦ hX (hρac i h0)
      have h0' : ¬ (ValidPSp.toPSpace ⟨(τ i).psp, hτvalid i⟩).μ X.1 = 0 := by
        rw [hτP i]; exact hX
      simp only [prunePrograms]
      rw [ite_eq_right h0, ite_eq_right h0']
    · rw [List.nil_append]
      exact Measure.le_preserves_measure (h := le_of_eq hTms) (μ := ρ i)
        (hu := measurableSet_prefixEqEvent hq)
  have hbpSf : ∀ i : μ.support, bp i ≤ Sf i := by
    intro i
    have hbvle : bv i ≤ (run C (τ i)).1.toSpace :=
      le_trans (le_mul_of_one_le PSp.one_le) (hbvc i)
    have hbvle' : (.some (bp i) : PSp Ω) ≤ (run C (τ i)).1.psp := by
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
  -- the conditioning: the run's tree at each fibre's measure, trimmed to `𝓜`
  have hfib_meas : ∀ v, ∃ ν : Measure[𝓜] Ω, IsProbabilityMeasure ν ∧
      ∀ hv : v ∈ μ.support, ν = (@PSpace.trim Ω (Sf ⟨v, hv⟩) 𝓜 (h𝓜Sf ⟨v, hv⟩)).μ := by
    intro v
    by_cases hv : v ∈ μ.support
    · exact ⟨_, (@PSpace.trim Ω (Sf ⟨v, hv⟩) 𝓜 (h𝓜Sf ⟨v, hv⟩)).2, fun _ ↦ rfl⟩
    · exact ⟨B.μ, B.2, fun h ↦ absurd h hv⟩
  choose κ'f hκ'p hκ'f' using hfib_meas
  have hκ'f : ∀ i : μ.support, κ'f i = (@PSpace.trim Ω (Sf i) 𝓜 (h𝓜Sf i)).μ :=
    fun i ↦ hκ'f' i i.2
  obtain ⟨κ', hκ'⟩ : ∃ κ' : TrivialMarkovKernel β B, ∀ v, κ'.1 v = κ'f v := by
    letI : MeasurableSpace β := ⊤
    exact ⟨⟨⟨κ'f, measurable_from_top⟩, ⟨hκ'p⟩⟩, fun _ ↦ rfl⟩
  have hmix' : B.μ = (μ.toMeasureWithMs ⊤).bind κ' := by
    apply @Measure.ext Ω 𝓜
    intro G hG
    refine Eq.trans ?_ (bind_apply_support μ κ'.1 hG).symm
    show (MeasureOnSpace.trim h𝓜S).μ G = _
    rw [MeasureOnSpace.trim_eq h𝓜S hG, hSμ G]
    have hf : ∀ E, MeasurableSet[T.ms] E →
        (P₀.μ.cast T.ms) E = ∑' i : μ.support, (HSMul.hSMul (μ i) ((ρ i).cast T.ms)) E := by
      intro E hE
      rw [Measure.le_preserves_measure (h := le_of_eq hTms) (μ := P₀.μ) (hu := hE),
        hP₀mix E (by rw [← hTms]; exact hE)]
      refine tsum_congr fun i ↦ ?_
      rw [Measure.smul_apply, smul_eq_mul,
        Measure.le_preserves_measure (h := le_of_eq hTms) (μ := ρ i) (hu := hE)]
    rw [fixpoint_sum' (P₀.μ.cast T.ms) (fun i : μ.support ↦ HSMul.hSMul (μ i) ((ρ i).cast T.ms))
      hf (h𝓜T G hG)]
    refine tsum_congr fun i ↦ ?_
    rw [hκ' i, hκ'f i]
    show _ = _ * (MeasureOnSpace.trim (h𝓜Sf i)).μ G
    rw [MeasureOnSpace.trim_eq (h𝓜Sf i) hG,
      measure_congr_tree (fixpoint_smul (μ i) ((ρ i).cast T.ms)) G]
    show (HSMul.hSMul (μ i) (fixpoint ⟨T, (ρ i).cast T.ms⟩).2) G = _
    rw [Measure.smul_apply, smul_eq_mul]
  show own (⟨(B : PSp Ω), hbfB⟩ : BoundedFootprintSpace Bool)
    ⊢ jointConditioning μ (fun v ↦ Q v (result (run C μ₀)))
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
  -- the fibre's witness sits below the fibre, and the null set `N i` makes the fibre's
  -- result and the run's agree, which is what `AEProper` needs
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
    rw [fixpoint_preserves' _ (by rw [hTms]; exact hNP₀ i),
      Measure.le_preserves_measure (h := le_of_eq hTms) (μ := ρ i)
        (hu := by rw [hTms]; exact hNP₀ i)]
    exact hNnull i
  have hvκ : ✓(((κ' i : PSpace Ω)) : PSp Ω) := PSp.valid_def.mpr (Option.some_ne_none _)
  have hbfPN : HasBoundedFootprint (((@PSpace.trim Ω (κ' i : PSpace Ω)
      (MeasurableSpace.generateFrom {N i}) (PSpace.generateFrom_singleton_le hNκ) : PSpace Ω))
        : PSp Ω) :=
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
  exact hρ' (result_run_reweight (b := μ₀) (h := hvalid) (ν := ρ i) (hν := hρp i) Cb
    (fun hd ↦ hN' (hac' i ρ' hd)) hN')

end

end Foxglove
