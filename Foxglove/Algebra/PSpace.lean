module

public import Foxglove.Algebra.Kernel

@[expose] public section
namespace Foxglove

open ProbSpace
open Iris OrderedUnitalResourceAlgebra
open UpperSetBI
open ProbabilityTheory MeasureTheory

variable {α β : Type}

noncomputable section

/-! # Probability spaces on the tape

Facts about `PSpace Ω` used by the rules: sub-spaces, trims, tilts by a density, mixtures,
null sets, and the law of a random variable on a space. -/

/-! ### Sub-spaces and trims -/

/-- `p ≤ S` from the σ-algebras and the measures on `p`'s sets. -/
lemma PSpace.le_of_ms_le {p S : PSpace Ω} (h : p.ms ≤ S.ms)
    (hμ : ∀ E, MeasurableSet[p.ms] E → S.μ E = p.μ E) : p ≤ S := by
  refine ⟨h, ?_⟩
  apply @Measure.ext Ω p.ms
  intro u hu
  exact (hμ u hu).symm.trans (Measure.le_preserves_measure (h := h) (μ := S.μ) (hu := hu)).symm

/-- A space is below another if its σ-algebra is coarser and the measures agree on it. -/
lemma PSpace.le_of_measure_eq {p q : PSpace Ω} (hms : p.ms ≤ q.ms)
    (hμ : ∀ u, @MeasurableSet Ω p.ms u → p.μ u = q.μ u) : p ≤ q := by
  refine ⟨hms, ?_⟩
  apply @MeasureTheory.Measure.ext Ω p.ms
  intro u hu
  exact (hμ u hu).trans (_root_.Measure.le_preserves_measure (h := hms) (μ := q.μ) (hu := hu)).symm

/-- A space below `S` that measures no more than `f` sits below `S` trimmed to `f`. -/
lemma PSpace.le_trim_of_le {p S : PSpace Ω} {f : MeasurableSpace Ω} (hf : f ≤ S.ms)
    (hpS : p ≤ S) (hpf : p.ms ≤ f) : p ≤ @PSpace.trim Ω S f hf := by
  refine PSpace.le_of_ms_le hpf fun E hE ↦ ?_
  show (MeasureOnSpace.trim hf).μ E = p.μ E
  rw [MeasureOnSpace.trim_eq hf (hpf E hE), MeasureOnSpace.le_preserves_measure hpS hE]

/-- A set integral of a function the smaller space measures can be taken in either space. -/
lemma PSpace.setLIntegral_of_le {s P : PSpace Ω} (hsP : s ≤ P) {g : Ω → ENNReal}
    (hg : Measurable[s.ms] g) {A : Set Ω} (hA : MeasurableSet[s.ms] A) :
    ∫⁻ x in A, g x ∂P.μ = ∫⁻ x in A, g x ∂s.μ := by
  have htrim : s.μ = P.μ.trim hsP.1 := by
    apply @Measure.ext Ω s.ms
    intro u hu
    rw [MeasureOnSpace.le_preserves_measure hsP hu,
      @trim_measurableSet_eq Ω s.ms P.ms P.μ u hsP.1 hu]
  rw [htrim, setLIntegral_trim hsP.1 hg hA]

open MeasureTheory in
/-- A density measurable on a sub-space integrates the same on the sub-space and on the whole
space, over the sub-space's sets. -/
lemma PSpace.withDensity_le_apply {p q : PSpace Ω} (hpq : p ≤ q) {f : Ω → ENNReal}
    (hf : @Measurable Ω ENNReal p.ms _ f) {A : Set Ω} (hA : @MeasurableSet Ω p.ms A) :
    q.μ.withDensity f A = p.μ.withDensity f A := by
  have htrim : p.μ = q.μ.trim hpq.1 := by
    refine @Measure.ext Ω p.ms _ _ fun u hu ↦ ?_
    rw [trim_measurableSet_eq hpq.1 hu]
    exact MeasureOnSpace.le_preserves_measure hpq hu
  rw [withDensity_apply _ (hpq.1 _ hA), withDensity_apply _ hA, htrim,
    restrict_trim hpq.1 _ hA, lintegral_trim hpq.1 hf]

open MeasureTheory in
/-- A space carrying only the measures `0` and `1` and sitting below `y` is independent of
`y`, with `y` itself as the product. -/
theorem PSpace.isIndependentProduct_of_zero_one_le {p y : PSpace Ω} (hpy : p ≤ y)
    (h01 : ∀ t, @MeasurableSet Ω p.ms t → p.μ t = 0 ∨ p.μ t = 1) : y =ᵢ p ⊕ᵢ y := by
  have hy := y.2
  refine ⟨(sup_eq_right.mpr hpy.1).symm, fun E hE F _ ↦ ?_⟩
  have hEy : p.μ E = y.μ E := MeasureOnSpace.le_preserves_measure hpy hE
  rcases h01 E hE with h | h
  · rw [h, zero_mul]
    exact measure_mono_null Set.inter_subset_left (hEy.symm.trans h)
  · rw [h, one_mul]
    refine le_antisymm (measure_mono Set.inter_subset_right) ?_
    have hc : y.μ Eᶜ = 0 := by
      rw [PSpace.measure_compl (hpy.1 _ hE), ← hEy, h]; simp
    calc y.μ F ≤ y.μ ((E ∩ F) ∪ Eᶜ) := by
          refine measure_mono fun x hx ↦ ?_
          by_cases hxe : x ∈ E
          · exact Or.inl ⟨hxe, hx⟩
          · exact Or.inr hxe
      _ ≤ y.μ (E ∩ F) + y.μ Eᶜ := measure_union_le _ _
      _ = y.μ (E ∩ F) := by rw [hc, add_zero]

/-- **Independence of a join, from a π-system.**  A frame `c` inside `S` that is independent
of every `A ∩ F` (with `A` from `m₁`, `F` from `m₂`) is independent of all of `m₁ ⊔ m₂`. -/
lemma PSpace.indep_sup_of_rect {S c : PSpace Ω} {m₁ m₂ : MeasurableSpace Ω}
    (h₁ : m₁ ≤ S.ms) (h₂ : m₂ ≤ S.ms) (hc : c ≤ S)
    (hbase : ∀ A, MeasurableSet[m₁] A → ∀ F, MeasurableSet[m₂] F → ∀ E,
      MeasurableSet[c.ms] E → S.μ (A ∩ F ∩ E) = S.μ (A ∩ F) * c.μ E)
    {E : Set Ω} (hE : MeasurableSet[c.ms] E) :
    ∀ G, MeasurableSet[m₁ ⊔ m₂] G → S.μ (G ∩ E) = S.μ G * c.μ E := by
  have hSp := S.2
  have hcp := c.2
  have hES : MeasurableSet[S.ms] E := hc.1 _ hE
  have hcE : S.μ E = c.μ E := (MeasureOnSpace.le_preserves_measure hc hE).symm
  have hle : m₁ ⊔ m₂ ≤ S.ms := sup_le h₁ h₂
  intro G hG
  refine MeasurableSpace.induction_on_inter (C := fun G _ ↦ S.μ (G ∩ E) = S.μ G * c.μ E)
    (MeasurableSpace.generateFrom_supGenerator_eq_sup m₁ m₂).symm ?_ ?_ ?_ ?_ ?_ G hG
  · rintro _ ⟨u, v, rfl, hu, hv⟩ _ ⟨u', v', rfl, hu', hv'⟩ _
    exact ⟨u ∩ u', v ∩ v', by rw [Set.inter_inter_inter_comm], hu.inter hu', hv.inter hv'⟩
  · simp
  · rintro _ ⟨A, F, rfl, hA, hF⟩
    exact hbase A hA F hF E hE
  · intro t ht ih
    have htS : MeasurableSet[S.ms] t := hle _ ht
    have hdiff : tᶜ ∩ E = E \ (t ∩ E) := by ext; simp; tauto
    rw [hdiff, measure_sdiff Set.inter_subset_right (htS.inter hES).nullMeasurableSet
      (measure_ne_top _ _), ih, hcE, PSpace.measure_compl htS,
      ENNReal.sub_mul (fun _ _ ↦ measure_ne_top _ _), one_mul]
  · intro f hdisj hfm ih
    have hfS : ∀ i, MeasurableSet[S.ms] (f i) := fun i ↦ hle _ (hfm i)
    rw [Set.iUnion_inter, measure_iUnion (fun i j hij ↦ (hdisj hij).mono Set.inter_subset_left
      Set.inter_subset_left) (fun i ↦ (hfS i).inter hES), measure_iUnion hdisj hfS,
      ← ENNReal.tsum_mul_right]
    exact tsum_congr ih

/-- A trim of `S` that is independent of a frame `c ≤ S` composes with it inside `S`. -/
lemma PSpace.mul_trim_le {S c : PSpace Ω} {f : MeasurableSpace Ω} (hf : f ≤ S.ms) (hc : c ≤ S)
    (hrect : ∀ G, MeasurableSet[f] G → ∀ E, MeasurableSet[c.ms] E →
      S.μ (G ∩ E) = S.μ G * c.μ E) :
    PSp.mul (some (@PSpace.trim Ω S f hf)) (some c) ≤ (some S : PSp Ω) := by
  have hsup : f ⊔ c.ms ≤ S.ms := sup_le hf hc.1
  have hT : @PSpace.trim Ω S (f ⊔ c.ms) hsup =ᵢ (@PSpace.trim Ω S f hf) ⊕ᵢ c := by
    refine ⟨rfl, fun G hG E hE ↦ ?_⟩
    have hGE : MeasurableSet[f ⊔ c.ms] (G ∩ E) :=
      ((le_sup_left : f ≤ f ⊔ c.ms) _ hG).inter ((le_sup_right : c.ms ≤ f ⊔ c.ms) _ hE)
    show (MeasureOnSpace.trim hsup).μ (G ∩ E) = (MeasureOnSpace.trim hf).μ G * c.μ E
    rw [MeasureOnSpace.trim_eq hsup hGE, MeasureOnSpace.trim_eq hf hG]
    exact hrect G hG E hE
  rw [mul_respect_independentProduct hT]
  exact WithTop.coe_le_coe.2 (PSpace.trim_le hsup)

/-! ### Null sets -/

/-- A null set stays null above: a space measures no more than any space above it. -/
lemma PSpace.null_of_le {p q : PSpace Ω} (h : p ≤ q) {N : Set Ω} (hN : p.μ N = 0) :
    q.μ N = 0 := by
  obtain ⟨N', hNN', hN'meas, hN'0⟩ := @exists_measurable_superset_of_null Ω p.ms p.μ N hN
  refine measure_mono_null hNN' ?_
  rw [← MeasureOnSpace.le_preserves_measure h hN'meas]
  exact hN'0

/-- A null set `N` of `S` that `S` measures generates a space inside `S`. -/
lemma PSpace.generateFrom_singleton_le {S : PSpace Ω} {N : Set Ω} (hN : MeasurableSet[S.ms] N) :
    MeasurableSpace.generateFrom {N} ≤ S.ms :=
  MeasurableSpace.generateFrom_le fun _ ht ↦ by
    rw [Set.mem_singleton_iff] at ht
    rw [ht]
    exact hN

/-- **The null space.**  `S` cut down to `{∅, N, Nᶜ, univ}` for a null set `N` is independent
of everything `S` measures, so it composes with any space below `S`. -/
lemma PSpace.nullSpace_mul_le {S p : PSpace Ω} {N : Set Ω} (hN : MeasurableSet[S.ms] N)
    (hN0 : S.μ N = 0) (hp : p ≤ S) :
    PSp.mul (some (@PSpace.trim Ω S (MeasurableSpace.generateFrom {N})
      (PSpace.generateFrom_singleton_le hN))) (some p) ≤ (some S : PSp Ω) := by
  refine PSpace.mul_trim_le _ hp fun G hG E hE ↦ ?_
  have hSp := S.2
  rcases MeasureTheory.measurableSet_generateFrom_singleton_iff.mp hG with rfl | rfl | rfl | rfl
  · simp
  · rw [measure_mono_null Set.inter_subset_left hN0, hN0, zero_mul]
  · rw [prob_compl_eq_one_sub hN, hN0, tsub_zero, one_mul, ← Set.sdiff_eq_compl_inter,
      measure_sdiff_null hN0]
    exact (MeasureOnSpace.le_preserves_measure hp hE).symm
  · rw [Set.univ_inter, measure_univ, one_mul]
    exact (MeasureOnSpace.le_preserves_measure hp hE).symm

/-! ### Tilts and mixtures -/

open MeasureTheory in
/-- **Reweighting a product along a factor.**  Tilting `s = c ⊗ m` by `dν/dm` turns the
`m`-factor into `ν` and leaves `c` alone. -/
theorem reweight_rect {c m s : PSpace Ω} (hs : s =ᵢ c ⊕ᵢ m) (ν : Measure[m.ms] Ω)
    [IsProbabilityMeasure ν] (hac : ν ≪ m.μ) {E F : Set Ω} (hE : @MeasurableSet Ω c.ms E)
    (hF : @MeasurableSet Ω m.ms F) :
    (s.μ.withDensity (ν.rnDeriv m.μ)) (E ∩ F) = c.μ E * ν F := by
  have hmle : m.ms ≤ s.ms := (PSpace.le_of_isIndependentProduct_right hs).1
  have hcle : c.ms ≤ s.ms := (PSpace.le_of_isIndependentProduct_left hs).1
  have hmp := m.2
  rw [withDensity_apply _ ((hcle _ hE).inter (hmle _ hF)),
    PSpace.lintegral_rect hs (Measure.measurable_rnDeriv ν m.μ) hE hF, ← withDensity_apply _ hF,
    Measure.withDensity_rnDeriv_eq ν m.μ hac]

/-- **Reweighting an ambient along a factor.**  If `s = m ⊗ d` sits in `P`, then tilting `P`
by `dν/dm` turns the `m`-factor into `ν` and leaves `d` alone. -/
lemma PSpace.withDensity_rect {m d s P : PSpace Ω} (hs : s =ᵢ m ⊕ᵢ d) (hsP : s ≤ P)
    (ν : Measure[m.ms] Ω) [IsProbabilityMeasure ν] (hac : ν ≪ m.μ)
    {E : Set Ω} (hE : MeasurableSet[d.ms] E) {F : Set Ω} (hF : MeasurableSet[m.ms] F) :
    (P.μ.withDensity (ν.rnDeriv m.μ)) (E ∩ F) = d.μ E * ν F := by
  have hmp := m.2
  have hmle : m.ms ≤ s.ms := (PSpace.le_of_isIndependentProduct_left hs).1
  have hdle : d.ms ≤ s.ms := (PSpace.le_of_isIndependentProduct_right hs).1
  have hfmeas : Measurable[m.ms] (ν.rnDeriv m.μ) := Measure.measurable_rnDeriv ν m.μ
  have hEF : MeasurableSet[s.ms] (E ∩ F) := (hdle _ hE).inter (hmle _ hF)
  rw [withDensity_apply _ (hsP.1 _ hEF),
    PSpace.setLIntegral_of_le hsP (hfmeas.mono hmle le_rfl) hEF,
    PSpace.lintegral_rect (independentProduct_comm hs) hfmeas hE hF,
    ← withDensity_apply _ hF, Measure.withDensity_rnDeriv_eq ν m.μ hac]

set_option linter.style.haveILetI false in
open MeasureTheory in
/-- **Tilting along a mixture.**  If a sub-space `m` of `S` is the `ν`-mixture of fibres
`lam v`, then `S` is the `ν`-mixture of its tilts by the fibres' densities over `m`: those
densities sum to one `m`-a.e., hence `S`-a.e. -/
theorem mixture_of_tilts {γ : Type} {S m : PSpace Ω} (hmS : m ≤ S) (ν : PMF γ)
    (lam : γ → Measure[m.ms] Ω) (hprob : ∀ v, IsProbabilityMeasure (lam v))
    (hmix : m.μ = (ν.toMeasureWithMs ⊤).bind lam) {A : Set Ω} (hA : @MeasurableSet Ω S.ms A) :
    S.μ A = ∫⁻ v, S.μ.withDensity ((lam v).rnDeriv m.μ) A ∂(ν.toMeasureWithMs ⊤) := by
  have hmp := m.2
  have hsupp := ae_mem_support ν
  letI : MeasurableSpace γ := ⊤
  have hf : ∀ v, @Measurable Ω ENNReal m.ms _ ((lam v).rnDeriv m.μ) :=
    fun v ↦ Measure.measurable_rnDeriv _ _
  have hfS : ∀ v, @Measurable Ω ENNReal S.ms _ ((lam v).rnDeriv m.μ) :=
    fun v ↦ (hf v).mono hmS.1 le_rfl
  -- the densities sum to one, `m`-a.e.
  let Fs : Ω → ENNReal := fun ρ ↦ ∫⁻ v, (lam v).rnDeriv m.μ ρ ∂(ν.toMeasureWithMs ⊤)
  have hFmeas : @Measurable Ω ENNReal m.ms _ Fs := by
    haveI := ν.support_countable.to_subtype
    have h : Fs = fun ρ ↦ ∑' v : ν.support, (lam v).rnDeriv m.μ ρ * ν v :=
      funext fun ρ ↦ pmf_lintegral_eq_tsum ν _
    rw [h]
    letI : MeasurableSpace Ω := m.ms
    exact Measurable.tsum fun v ↦ (hf v).mul_const _
  have hFone : Fs =ᵐ[m.μ] 1 := by
    letI : MeasurableSpace Ω := m.ms
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite hFmeas measurable_const
      fun F hF _ ↦ ?_
    calc ∫⁻ x in F, Fs x ∂m.μ
        = ∫⁻ v, ∫⁻ x in F, (lam v).rnDeriv m.μ x ∂m.μ ∂(ν.toMeasureWithMs ⊤) :=
          (lintegral_pmf_swap ν (m.μ.restrict F) _ fun v ↦ (hf v).aemeasurable).symm
      _ = ∫⁻ v, lam v F ∂(ν.toMeasureWithMs ⊤) := by
          refine lintegral_congr_ae ?_
          filter_upwards [hsupp] with v hv
          haveI := hprob v
          exact Measure.setLIntegral_rnDeriv (bind_fibre_ac hmix hv) F
      _ = m.μ F := by rw [hmix, Measure.bind_apply hF measurable_from_top.aemeasurable]
      _ = ∫⁻ x in F, (1 : Ω → ENNReal) x ∂m.μ := by simp
  have hFoneS : Fs =ᵐ[S.μ] 1 := PSpace.ae_eq_of_le hmS hFone
  calc S.μ A = ∫⁻ x in A, Fs x ∂S.μ := by
        rw [lintegral_congr_ae (ae_restrict_of_ae hFoneS)]
        simp
    _ = ∫⁻ v, ∫⁻ x in A, (lam v).rnDeriv m.μ x ∂S.μ ∂(ν.toMeasureWithMs ⊤) :=
        (lintegral_pmf_swap ν (S.μ.restrict A) _ fun v ↦ (hfS v).aemeasurable).symm
    _ = _ := lintegral_congr fun v ↦ (withDensity_apply _ hA).symm

/-- **Mixing the reweighted ambients back.**  If `m` is the `w`-mixture of the `ν i`, then the
ambient `P ≥ m` is the `w`-mixture of its tilts by `dν i/dm`. -/
lemma PSpace.withDensity_mixture {ι : Type} [Countable ι] {m P : PSpace Ω} (hmP : m ≤ P)
    (w : ι → ENNReal) (ν : ι → Measure[m.ms] Ω) [∀ i, IsProbabilityMeasure (ν i)]
    (hac : ∀ i, ν i ≪ m.μ)
    (hmix : ∀ F, MeasurableSet[m.ms] F → m.μ F = ∑' i, w i * ν i F)
    {E : Set Ω} (hE : MeasurableSet[P.ms] E) :
    P.μ E = ∑' i, w i * (P.μ.withDensity ((ν i).rnDeriv m.μ)) E := by
  have hmp := m.2
  have hPp := P.2
  have hfm : ∀ i, Measurable[m.ms] ((ν i).rnDeriv m.μ) := fun i ↦ Measure.measurable_rnDeriv _ _
  have hfP : ∀ i, Measurable[P.ms] ((ν i).rnDeriv m.μ) := fun i ↦ (hfm i).mono hmP.1 le_rfl
  set g : Ω → ENNReal := fun x ↦ ∑' i, w i * (ν i).rnDeriv m.μ x with hg
  have hgm : Measurable[m.ms] g := Measurable.ennreal_tsum fun i ↦ (hfm i).const_mul _
  -- `g` is the density of `m.μ` against itself
  have hg1 : g =ᵐ[m.μ] 1 := by
    refine @ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite Ω m.ms m.μ _ g 1 hgm
      measurable_const ?_
    intro F hF _
    rw [hg, lintegral_tsum (fun i ↦ ((hfm i).const_mul _).aemeasurable)]
    simp_rw [lintegral_const_mul _ (hfm _)]
    have hterm : ∀ i, w i * ∫⁻ x in F, (ν i).rnDeriv m.μ x ∂m.μ = w i * ν i F := by
      intro i
      rw [← withDensity_apply _ hF, Measure.withDensity_rnDeriv_eq _ _ (hac i)]
    rw [tsum_congr hterm, ← hmix F hF]
    simp
  have hg1P : g =ᵐ[P.μ] 1 := PSpace.ae_eq_of_le hmP hg1
  symm
  calc ∑' i, w i * (P.μ.withDensity ((ν i).rnDeriv m.μ)) E
      = ∑' i, ∫⁻ x in E, w i * (ν i).rnDeriv m.μ x ∂P.μ := by
        refine tsum_congr fun i ↦ ?_
        rw [withDensity_apply _ hE, lintegral_const_mul _ (hfP i)]
    _ = ∫⁻ x in E, g x ∂P.μ := by
        rw [lintegral_tsum (fun i ↦ ((hfP i).const_mul _).aemeasurable)]
    _ = ∫⁻ x in E, 1 ∂P.μ := lintegral_congr_ae (ae_restrict_of_ae hg1P)
    _ = P.μ E := by simp

/-! ### The law of a random variable on a space -/

/-- `E` is almost-everywhere measurable for the space `P`. -/
def almostMeasurable {A : Type} (E : RV A) (P : PSp Ω) : Prop :=
  match P with
  | none => False
  | some p => @AEMeasurable Ω A ⊤ _ E p.1.μ

set_option linter.style.haveILetI false in
open MeasureTheory ProbabilityTheory in
/-- A pair with a product law on `P` splits `P` into two independent pieces, each carrying
one component's law: trim `P` to what each component sees.  A component is only almost
measurable, so each piece also sees a null set off which the pair agrees with a measurable
version; null, that set changes no measure and so keeps the pieces independent. -/
theorem PSpace.split_of_product_law {E₁ : Ω → α} {E₂ : Ω → β} {μ₁ : PMF α} {μ₂ : PMF β}
    (P : PSpace Ω) (ham : almostMeasurable (fun s ↦ (E₁ s, E₂ s)) (P : PSp Ω))
    (hlaw : @Measure.map Ω (α × β) P.ms ⊤ (fun s ↦ (E₁ s, E₂ s)) P.μ
      = (μ₁ ⊗ μ₂).toMeasureWithMs ⊤) :
    ∃ D₁ D₂ : PSpace Ω, D₁ ≤ P ∧ D₂ ≤ P ∧ PSp.mul (D₁ : PSp Ω) (D₂ : PSp Ω) ≤ (P : PSp Ω) ∧
      (almostMeasurable E₁ (D₁ : PSp Ω) ∧
        @Measure.map Ω α D₁.ms ⊤ E₁ D₁.μ = μ₁.toMeasureWithMs ⊤) ∧
      (almostMeasurable E₂ (D₂ : PSp Ω) ∧
        @Measure.map Ω β D₂.ms ⊤ E₂ D₂.μ = μ₂.toMeasureWithMs ⊤) := by
  have hP := P.isProbability
  letI : MeasurableSpace α := ⊤
  letI : MeasurableSpace β := ⊤
  letI : MeasurableSpace (α × β) := ⊤
  letI : MeasurableSpace Ω := P.ms
  -- a measurable version `g` of the pair, agreeing with it off a measurable null set `N`
  obtain ⟨g, hg, hae⟩ : AEMeasurable (fun s ↦ (E₁ s, E₂ s)) P.μ := ham
  obtain ⟨N, hNsub, hNmeas, hNnull⟩ := exists_measurable_superset_of_null (ae_iff.mp hae)
  let g₁ : Ω → α := fun s ↦ (g s).1
  let g₂ : Ω → β := fun s ↦ (g s).2
  have hg₁ : Measurable g₁ := measurable_from_top.comp hg
  have hg₂ : Measurable g₂ := measurable_from_top.comp hg
  -- the law of `g` on rectangles, and its marginals
  have hrect : ∀ A B, P.μ (g₁ ⁻¹' A ∩ g₂ ⁻¹' B)
      = μ₁.toMeasureWithMs ⊤ A * μ₂.toMeasureWithMs ⊤ B := by
    intro A B
    have h := congrArg (fun ν : Measure (α × β) ↦ ν (A ×ˢ B))
      ((Measure.map_congr hae).symm.trans hlaw)
    rw [Measure.map_apply hg MeasurableSpace.measurableSet_top] at h
    rw [show g₁ ⁻¹' A ∩ g₂ ⁻¹' B = g ⁻¹' (A ×ˢ B) by ext; simp [g₁, g₂], h]
    exact product_toMeasure_prod μ₁ μ₂ A B
  have hmarg₁ : ∀ A, P.μ (g₁ ⁻¹' A) = μ₁.toMeasureWithMs ⊤ A := by
    intro A
    have h := hrect A Set.univ
    rw [Set.preimage_univ, Set.inter_univ] at h
    rw [h]
    unfold PMF.toMeasureWithMs
    rw [measure_univ, mul_one]
  have hmarg₂ : ∀ B, P.μ (g₂ ⁻¹' B) = μ₂.toMeasureWithMs ⊤ B := by
    intro B
    have h := hrect Set.univ B
    rw [Set.preimage_univ, Set.univ_inter] at h
    rw [h]
    unfold PMF.toMeasureWithMs
    rw [measure_univ, one_mul]
  -- intersecting with `Set.univ` or with the conull `Nᶜ` changes no measure
  have hC : ∀ C ∈ ({Set.univ, Nᶜ} : Set (Set Ω)), ∀ X, P.μ (X ∩ C) = P.μ X := by
    rintro C (rfl | rfl) X
    · rw [Set.inter_univ]
    · exact measure_inter_conull (by rwa [compl_compl])
  have hCC : ∀ C ∈ ({Set.univ, Nᶜ} : Set (Set Ω)), ∀ C' ∈ ({Set.univ, Nᶜ} : Set (Set Ω)),
      C ∩ C' ∈ ({Set.univ, Nᶜ} : Set (Set Ω)) := by
    rintro C (rfl | rfl) C' (rfl | rfl) <;> simp
  have hCmeas : ∀ C ∈ ({Set.univ, Nᶜ} : Set (Set Ω)), MeasurableSet C := by
    rintro C (rfl | rfl)
    · exact MeasurableSet.univ
    · exact hNmeas.compl
  -- the π-systems of what each component sees, together with `N`
  let S₁ : Set (Set Ω) :=
    {t | ∃ A : Set α, ∃ C ∈ ({Set.univ, Nᶜ} : Set (Set Ω)), t = g₁ ⁻¹' A ∩ C}
  let S₂ : Set (Set Ω) :=
    {t | ∃ B : Set β, ∃ C ∈ ({Set.univ, Nᶜ} : Set (Set Ω)), t = g₂ ⁻¹' B ∩ C}
  have hS₁meas : ∀ t ∈ S₁, MeasurableSet t := by
    rintro _ ⟨A, C, hCm, rfl⟩
    exact (hg₁ MeasurableSpace.measurableSet_top).inter (hCmeas C hCm)
  have hS₂meas : ∀ t ∈ S₂, MeasurableSet t := by
    rintro _ ⟨B, C, hCm, rfl⟩
    exact (hg₂ MeasurableSpace.measurableSet_top).inter (hCmeas C hCm)
  have hS₁pi : IsPiSystem S₁ := by
    rintro _ ⟨A, C, hCm, rfl⟩ _ ⟨A', C', hCm', rfl⟩ _
    refine ⟨A ∩ A', C ∩ C', hCC C hCm C' hCm', ?_⟩
    ext x; simp only [Set.mem_inter_iff, Set.mem_preimage]; tauto
  have hS₂pi : IsPiSystem S₂ := by
    rintro _ ⟨B, C, hCm, rfl⟩ _ ⟨B', C', hCm', rfl⟩ _
    refine ⟨B ∩ B', C ∩ C', hCC C hCm C' hCm', ?_⟩
    ext x; simp only [Set.mem_inter_iff, Set.mem_preimage]; tauto
  have hind : Indep (MeasurableSpace.generateFrom S₁) (MeasurableSpace.generateFrom S₂) P.μ := by
    refine IndepSets.indep' hS₁meas hS₂meas hS₁pi hS₂pi ((IndepSets_iff _ _ _).2 ?_)
    rintro _ _ ⟨A, C, hCm, rfl⟩ ⟨B, C', hCm', rfl⟩
    rw [show g₁ ⁻¹' A ∩ C ∩ (g₂ ⁻¹' B ∩ C') = (g₁ ⁻¹' A ∩ g₂ ⁻¹' B) ∩ (C ∩ C') by
        ext x; simp only [Set.mem_inter_iff]; tauto,
      hC _ (hCC C hCm C' hCm'), hC C hCm, hC C' hCm', hrect, hmarg₁, hmarg₂]
  -- the two pieces, and their product
  set G₁ := MeasurableSpace.generateFrom S₁ with hG₁def
  set G₂ := MeasurableSpace.generateFrom S₂ with hG₂def
  have hG₁ : G₁ ≤ P.ms := MeasurableSpace.generateFrom_le hS₁meas
  have hG₂ : G₂ ≤ P.ms := MeasurableSpace.generateFrom_le hS₂meas
  let D₁ : PSpace Ω := @PSpace.trim Ω P G₁ hG₁
  let D₂ : PSpace Ω := @PSpace.trim Ω P G₂ hG₂
  let s : PSpace Ω := @PSpace.trim Ω P (G₁ ⊔ G₂) (sup_le hG₁ hG₂)
  have hD₁P : D₁ ≤ P := PSpace.trim_le hG₁
  have hD₂P : D₂ ≤ P := PSpace.trim_le hG₂
  have hsP : s ≤ P := PSpace.trim_le (sup_le hG₁ hG₂)
  have hprod : s =ᵢ D₁ ⊕ᵢ D₂ := by
    refine ⟨rfl, fun E hE F hF ↦ ?_⟩
    have hEF : @MeasurableSet Ω (G₁ ⊔ G₂) (E ∩ F) :=
      MeasurableSet.inter (le_sup_left (a := G₁) (b := G₂) E hE)
        (le_sup_right (a := G₁) (b := G₂) F hF)
    rw [MeasureOnSpace.le_preserves_measure hsP hEF, MeasureOnSpace.le_preserves_measure hD₁P hE,
      MeasureOnSpace.le_preserves_measure hD₂P hF]
    exact (Indep_iff _ _ _).1 hind E F hE hF
  -- each component is a.e. its measurable version on its piece
  have hg₁D : @Measurable Ω α G₁ ⊤ g₁ := fun A _ ↦
    MeasurableSpace.measurableSet_generateFrom ⟨A, Set.univ, by simp, (Set.inter_univ _).symm⟩
  have hg₂D : @Measurable Ω β G₂ ⊤ g₂ := fun B _ ↦
    MeasurableSpace.measurableSet_generateFrom ⟨B, Set.univ, by simp, (Set.inter_univ _).symm⟩
  have hN₁ : @MeasurableSet Ω G₁ N := by
    have h : @MeasurableSet Ω G₁ Nᶜ :=
      MeasurableSpace.measurableSet_generateFrom ⟨Set.univ, Nᶜ, by simp, by simp⟩
    simpa using h.compl
  have hN₂ : @MeasurableSet Ω G₂ N := by
    have h : @MeasurableSet Ω G₂ Nᶜ :=
      MeasurableSpace.measurableSet_generateFrom ⟨Set.univ, Nᶜ, by simp, by simp⟩
    simpa using h.compl
  have hae₁ : E₁ =ᵐ[D₁.μ] g₁ := by
    refine ae_iff.2 (measure_mono_null (fun s hs ↦ hNsub fun h ↦ hs (congrArg Prod.fst h)) ?_)
    rw [MeasureOnSpace.le_preserves_measure hD₁P hN₁]
    exact hNnull
  have hae₂ : E₂ =ᵐ[D₂.μ] g₂ := by
    refine ae_iff.2 (measure_mono_null (fun s hs ↦ hNsub fun h ↦ hs (congrArg Prod.snd h)) ?_)
    rw [MeasureOnSpace.le_preserves_measure hD₂P hN₂]
    exact hNnull
  refine ⟨D₁, D₂, hD₁P, hD₂P,
    (le_of_eq (mul_respect_independentProduct hprod)).trans (WithTop.coe_le_coe.2 hsP),
    ⟨⟨g₁, hg₁D, hae₁⟩, ?_⟩, ⟨⟨g₂, hg₂D, hae₂⟩, ?_⟩⟩
  · refine (Measure.map_congr hae₁).trans ?_
    ext A _
    exact (Measure.map_apply hg₁D MeasurableSpace.measurableSet_top).trans
      ((MeasureOnSpace.le_preserves_measure hD₁P (hg₁D MeasurableSpace.measurableSet_top)).trans
        (hmarg₁ A))
  · refine (Measure.map_congr hae₂).trans ?_
    ext B _
    exact (Measure.map_apply hg₂D MeasurableSpace.measurableSet_top).trans
      ((MeasureOnSpace.le_preserves_measure hD₂P (hg₂D MeasurableSpace.measurableSet_top)).trans
        (hmarg₂ B))

set_option linter.style.haveILetI false in
open MeasureTheory in
/-- A space that is a `μ`-mixture of fibres, on each of which `E` surely is the fibre's
value, gives `E` the law `μ`.  A measurable version of `E` is read off a conull cover of each
fibre's event `E = v`; the covers are disjoint, and there are countably many of them. -/
theorem law_of_fibres {E : RV α} {μ : PMF α} (s : PSpace Ω) (w : α → Measure[s.ms] Ω)
    (hmix : ∀ S, @MeasurableSet Ω s.ms S → s.μ S = ∫⁻ v, w v S ∂(μ.toMeasureWithMs ⊤))
    (hprob : ∀ v ∈ μ.support, w v Set.univ = 1)
    (hsure : ∀ v ∈ μ.support, w v {ρ | ¬ E ρ = v} = 0) :
    almostMeasurable E (s : PSp Ω) ∧
      @Measure.map Ω α s.ms ⊤ E s.μ = μ.toMeasureWithMs ⊤ := by
  classical
  have hsupp := ae_mem_support μ
  letI : MeasurableSpace α := ⊤
  letI : MeasurableSpace Ω := s.ms
  -- a measurable null cover `N v` of each fibre's exceptional set
  choose! N hNsub hNmeas hNnull using fun v (hv : v ∈ μ.support) ↦
    exists_measurable_superset_of_null (hsure v hv)
  have hEv : ∀ v ∈ μ.support, ∀ ρ, ρ ∉ N v → E ρ = v := fun v hv ρ hρ ↦
    by_contra fun h ↦ hρ (hNsub v hv h)
  set U := ⋃ v ∈ μ.support, (N v)ᶜ with hU
  have hUmeas : MeasurableSet U :=
    MeasurableSet.biUnion μ.support_countable fun v hv ↦ (hNmeas v hv).compl
  have hmemU : ∀ v ∈ μ.support, ∀ ρ, ρ ∉ N v → ρ ∈ U := fun v hv ρ hρ ↦
    Set.mem_biUnion hv hρ
  obtain ⟨v₁, -⟩ := μ.support_nonempty
  -- the measurable version: `E` on the covers, anything off them
  let g : Ω → α := fun ρ ↦ if ρ ∈ U then E ρ else v₁
  have hgv : ∀ v ∈ μ.support, ∀ ρ, ρ ∉ N v → g ρ = v := fun v hv ρ hρ ↦ by
    simp only [g, hmemU v hv ρ hρ, ↓reduceIte]
    exact hEv v hv ρ hρ
  have hpre : ∀ B : Set α, g ⁻¹' B
      = (⋃ v ∈ {v | v ∈ μ.support ∧ v ∈ B}, (N v)ᶜ) ∪ (Uᶜ ∩ {_ρ | v₁ ∈ B}) := by
    intro B
    ext ρ
    by_cases hρ : ρ ∈ U
    · obtain ⟨v, hv, hρv⟩ : ∃ v ∈ μ.support, ρ ∉ N v := by simpa [hU] using hρ
      simp only [Set.mem_preimage, hgv v hv ρ hρv, Set.mem_union, Set.mem_iUnion,
        Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_ofPred_eq, hρ, not_true_eq_false,
        false_and, or_false, exists_prop]
      constructor
      · exact fun hvB ↦ ⟨v, ⟨hv, hvB⟩, hρv⟩
      · rintro ⟨v', ⟨hv', hv'B⟩, hρv'⟩
        rwa [← hgv v hv ρ hρv, hgv v' hv' ρ hρv']
    · simp only [Set.mem_preimage, g, Set.mem_union, Set.mem_iUnion,
        Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_ofPred_eq, hρ, not_false_eq_true,
        true_and, exists_prop]
      constructor
      · exact Or.inr
      · rintro (⟨v', ⟨hv', -⟩, hρv'⟩ | h)
        · exact absurd (hmemU v' hv' ρ hρv') hρ
        · exact h
  have hg : Measurable g := by
    intro B _
    rw [hpre B]
    refine MeasurableSet.union ?_ (hUmeas.compl.inter (MeasurableSet.const _))
    exact MeasurableSet.biUnion (μ.support_countable.mono fun v hv ↦ hv.1)
      fun v hv ↦ (hNmeas v hv.1).compl
  -- off the covers there is no mass
  have hUc : s.μ Uᶜ = 0 := by
    rw [hmix _ hUmeas.compl]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hsupp] with v hv
    exact measure_mono_null (fun ρ hρ ↦ by_contra fun h ↦ hρ (hmemU v hv ρ h)) (hNnull v hv)
  have hae : E =ᵐ[s.μ] g := by
    refine ae_iff.2 (measure_mono_null
      (show {ρ | ¬ E ρ = g ρ} ⊆ Uᶜ from fun ρ hρ hρU ↦ hρ ?_) hUc)
    simp only [g, hρU, ↓reduceIte]
  have haem : AEMeasurable E s.μ := ⟨g, hg, hae⟩
  refine ⟨haem, ?_⟩
  -- each fibre puts all its mass on `g ⁻¹' B` or none
  ext B _
  rw [Measure.map_apply_of_aemeasurable haem MeasurableSpace.measurableSet_top,
    measure_congr (hae.preimage B), hmix _ (hg MeasurableSpace.measurableSet_top)]
  have hind : ∀ᵐ v ∂(μ.toMeasureWithMs ⊤), w v (g ⁻¹' B) = B.indicator 1 v := by
    filter_upwards [hsupp] with v hv
    by_cases hvB : v ∈ B
    · rw [Set.indicator_of_mem hvB, Pi.one_apply]
      have hNfin : w v (N v) ≠ (⊤ : ENNReal) := by rw [hNnull v hv]; exact ENNReal.zero_ne_top
      have hcov : w v (N v)ᶜ = 1 := by
        rw [measure_compl (hNmeas v hv) hNfin, hprob v hv, hNnull v hv, tsub_zero]
      refine le_antisymm ((measure_mono (Set.subset_univ _)).trans (hprob v hv).le) ?_
      rw [← hcov]
      exact measure_mono fun ρ hρ ↦ show g ρ ∈ B by rw [hgv v hv ρ hρ]; exact hvB
    · rw [Set.indicator_of_notMem hvB]
      refine measure_mono_null (fun ρ hρ ↦ by_contra fun hρN ↦ hvB ?_) (hNnull v hv)
      have hρB : g ρ ∈ B := hρ
      rwa [hgv v hv ρ hρN] at hρB
  rw [lintegral_congr_ae hind, lintegral_indicator_one MeasurableSpace.measurableSet_top]

set_option linter.style.haveILetI false in
open MeasureTheory ProbabilityTheory in
/-- A random variable with law `μ` on `P` conditions `P`: sending `v` to `P` conditioned on
`E = v` (read on a measurable version of `E`) is a kernel mixing back to `P`, and on its fibre
at `v` the variable surely is `v`. -/
theorem condKernel_of_law {E : RV α} {μ : PMF α} (P : PSpace Ω)
    (ham : almostMeasurable E (P : PSp Ω))
    (hlaw : @Measure.map Ω α P.ms ⊤ E P.μ = μ.toMeasureWithMs ⊤) :
    ∃ κ : TrivialMarkovKernel α P, P.μ = (μ.toMeasureWithMs ⊤).bind κ ∧
      ∀ v ∈ μ.support, (κ v : PSpace Ω).μ {ρ | ¬ E ρ = v} = 0 := by
  classical
  have hP := P.isProbability
  letI : MeasurableSpace α := ⊤
  letI : MeasurableSpace Ω := P.ms
  obtain ⟨g, hg, hae⟩ : AEMeasurable E P.μ := ham
  have hlaw' : Measure.map g P.μ = μ.toMeasure := (Measure.map_congr hae).symm.trans hlaw
  have hG : ∀ v, MeasurableSet (g ⁻¹' {v}) := fun _ ↦ hg MeasurableSpace.measurableSet_top
  have hGμ : ∀ v, P.μ (g ⁻¹' {v}) = μ v := fun v ↦ by
    rw [← Measure.map_apply hg MeasurableSpace.measurableSet_top, hlaw',
      PMF.toMeasure_apply_singleton _ _ MeasurableSpace.measurableSet_top]
  have hG0 : ∀ v ∈ μ.support, P.μ (g ⁻¹' {v}) ≠ 0 := fun v hv ↦ by
    rw [hGμ]; exact (PMF.mem_support_iff _ _).1 hv
  -- the fibres: `P` conditioned on `g = v`
  let f : α → Measure Ω := fun v ↦ if v ∈ μ.support then P.μ[|g ⁻¹' {v}] else P.μ
  have hfprob : ∀ v, IsProbabilityMeasure (f v) := by
    intro v
    by_cases hv : v ∈ μ.support
    · simp only [f, hv, ↓reduceIte]
      exact cond_isProbabilityMeasure (hG0 v hv)
    · simp only [f, hv, ↓reduceIte]
      exact hP
  let κ : TrivialMarkovKernel α P := ⟨⟨f, measurable_from_top⟩, ⟨hfprob⟩⟩
  refine ⟨κ, ?_, fun v hv ↦ ?_⟩
  · -- `P` is the mixture of its fibres: sum over the countable support
    ext F hF
    rw [Measure.bind_apply hF (Kernel.measurable κ.1).aemeasurable]
    show P.μ F = ∫⁻ v, f v F ∂μ.toMeasure
    have hcon : P.μ (g ⁻¹' μ.support)ᶜ = 0 := by
      rw [← Set.preimage_compl, ← Measure.map_apply hg MeasurableSpace.measurableSet_top, hlaw',
        μ.toMeasure_apply_eq_zero_iff MeasurableSpace.measurableSet_top]
      exact disjoint_compl_right
    have hterm : ∀ v : μ.support,
        f v F * μ.toMeasure {(v : α)} = (P.μ.restrict F) (g ⁻¹' {(v : α)}) := by
      rintro ⟨v, hv⟩
      simp only [f, hv, ↓reduceIte]
      rw [cond_apply (hG v), PMF.toMeasure_apply_singleton _ _ MeasurableSpace.measurableSet_top,
        ← hGμ, Measure.restrict_apply (hG v), Set.inter_comm, mul_comm, ← mul_assoc,
        ENNReal.mul_inv_cancel (hG0 v hv) (measure_ne_top _ _), one_mul]
    rw [← μ.restrict_toMeasure_support, lintegral_countable _ μ.support_countable,
      tsum_congr hterm,
      tsum_measure_preimage_singleton μ.support_countable (fun v _ ↦ hG v),
      Measure.restrict_apply (hg MeasurableSpace.measurableSet_top), Set.inter_comm,
      measure_inter_conull hcon]
  · -- on the fibre at `v`, `E` is `v` up to the null set where `E` and `g` differ
    show f v {ρ | ¬ E ρ = v} = 0
    simp only [f, hv, ↓reduceIte]
    obtain ⟨N, hNsub, -, hNnull⟩ := exists_measurable_superset_of_null (ae_iff.1 hae)
    refine measure_mono_null (t := (g ⁻¹' {v})ᶜ ∪ N) (fun ρ hρ ↦ ?_)
      (measure_union_null ?_ (cond_absolutelyContinuous hNnull))
    · by_cases hgv : g ρ = v
      · exact Or.inr (hNsub fun h ↦ hρ (h.trans hgv))
      · exact Or.inl hgv
    · rw [cond_apply (hG v), Set.inter_compl_self, measure_empty, mul_zero]

set_option linter.style.haveILetI false in
open MeasureTheory in
/-- On a fixed space, pushing `E` forward to `δ v` is the same as `E` being `v` off a null
set: the two only differ in how they say "almost surely `v`". -/
theorem law_dirac_iff {A : Type} {E : RV A} {v : A} (P : PSpace Ω) :
    (almostMeasurable E (P : PSp Ω) ∧
        @Measure.map Ω A P.ms ⊤ E P.μ = (δ v).toMeasureWithMs ⊤)
      ↔ P.μ {ρ | ¬ E ρ = v} = 0 := by
  have hP := P.isProbability
  letI : MeasurableSpace A := ⊤
  letI : MeasurableSpace Ω := P.ms
  constructor
  · rintro ⟨ham, hmap⟩
    replace ham : @AEMeasurable Ω A ⊤ P.ms E P.μ := ham
    have h := Measure.map_apply_of_aemeasurable ham
      (s := {v}ᶜ) MeasurableSpace.measurableSet_top
    rw [hmap] at h
    show P.μ (E ⁻¹' {v}ᶜ) = 0
    rw [← h]
    simp [PMF.toMeasureWithMs, PMF.toMeasure_pure]
  · intro h
    -- `E` is a.e. the constant `v`, which is measurable, so it is a.e.-measurable
    have hae : E =ᵐ[P.μ] (fun _ ↦ v) := h
    refine ⟨⟨fun _ ↦ v, measurable_const, hae⟩, ?_⟩
    rw [Measure.map_congr hae, Measure.map_const]
    simp [PMF.toMeasureWithMs, PMF.toMeasure_pure]

end

end Foxglove
