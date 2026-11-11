module

public import Foxglove.Rules.WP.Post

public section
namespace Foxglove

open ProbSpace
open Iris OrderedUnitalResourceAlgebra
open UpperSetBI
open Iris BI UpperSetBI OURAProp
open Interp Interp.ProbTree Interp.ProbTree.BoundedFootprintPsp MeasureTheory ProbabilityTheory
open unitInterval

noncomputable section

/-! # Counterexamples

What the side conditions of the sequencing rules rule out, on one program -- a single fair
coin -- and one postcondition each: `AEProper` alone does not make `WP_BIND` sound, and the
converse of `WP_BIND` fails outright. -/

/-- **"The result is almost surely a constant."**  `AEProper`, but not mixable: it holds on
each fibre of a coin and fails on the coin. -/
noncomputable def constQ : RV Bool → FProp := fun X ↦ iprop(⌈X = true⌉ ∨ ⌈X = false⌉)

/-- `constQ` cannot tell almost-surely-equal results apart: distribute `∗` over `∨` and
substitute the sure equality in each disjunct. -/
lemma aeProper_constQ : AEProper constQ := (aeProper_def _).2 fun _ _ ↦
  entails_trans sep_or_left.1
    (or_elim (entails_trans liftPred_subst or_intro_l)
      (entails_trans liftPred_subst or_intro_r))

/-- A constant result is surely constant, for free. -/
lemma constQ_const (v : Bool) : ⊢ constQ (fun _ ↦ v) := by
  cases v
  · exact entails_trans (liftPred_of_forall (a := fun _ : Ω ↦ (false : Bool) = false)
      (fun _ ↦ rfl)) or_intro_r
  · exact entails_trans (liftPred_of_forall (a := fun _ : Ω ↦ (true : Bool) = true)
      (fun _ ↦ rfl)) or_intro_l

/-- Every fibre of the bind discharges `constQ` outright: `pure v` reports the constant `v`,
which is surely constant. -/
lemma wp_pure_constQ (v : Bool) : ⊢ wp (pure v : Interp.BernoulliM Bool) constQ :=
  entails_trans (constQ_const v) WP_PURE

/-- So the whole premise of the sequencing rule is available for free: the coin has a law
(`WP_FLIP`), conditioning on it is a `valuePost` (`valuePost_of_law`), and each fibre's
postcondition costs nothing. -/
lemma wp_flip_valuePost :
    ⊢ wp (Interp.flip Interp.half)
        ⦃X, valuePost X (fun v ↦ wp (pure v : Interp.BernoulliM Bool) constQ)⦄ :=
  entails_trans WP_FLIP (WP_CONS fun _ ↦ valuePost_of_law fun v ↦ wp_pure_constQ v)

lemma half_ne_zero : Interp.half ≠ 0 := by
  intro h
  have hc := congrArg Subtype.val h
  rw [Interp.half_coe] at hc
  norm_num at hc

lemma half_ne_one : Interp.half ≠ 1 := by
  intro h
  have hc := congrArg Subtype.val h
  rw [Interp.half_coe] at hc
  norm_num at hc

/-- A nondegenerate coin is not a point mass. -/
lemma delta_ne_bernoulli (v : Bool) {r : I} (h0 : r ≠ 0) (h1 : r ≠ 1) :
    (δ v : PMF Bool) ≠ bernoulliWeights r := by
  intro h
  cases v
  · have hm : true ∈ (bernoulliWeights r).support := mem_support_bernoulliWeights_true h0
    rw [← h] at hm
    simp [δ] at hm
  · have hm : false ∈ (bernoulliWeights r).support := mem_support_bernoulliWeights_false h1
    rw [← h] at hm
    simp [δ] at hm

/-- **`constQ` is `AEProper` but not convex**, and that is exactly the gap
`WPBind_counterexample` walks through: the fair coin's law splits into two fibres, on each
of which the result is surely a constant, while on the coin itself it is surely neither. -/
theorem not_convex_constQ : ¬ ∀ X : RV Bool, Convex (constQ X) := by
  intro hconv
  have hemp : (1 : BoundedFootprintSpace Bool) ∈ (UpperSetBI.emp :
      UpperSet (BoundedFootprintSpace Bool)) := by
    exact UpperSetBI.mem_emp.2 (le_refl 1)
  have hv1 : ✓(1 : BoundedFootprintPsp).psp := BoundedFootprintPsp.valid_one
  have hle1 : (1 : BoundedFootprintSpace Bool) * 1 ≤ (1 : BoundedFootprintPsp).toSpace := by
    rw [mul_one]
    show (1 : BoundedFootprintSpace Bool).val ≤ (1 : BoundedFootprintPsp).toSpace.val
    rw [BoundedFootprintPsp.toSpace_val]
    exact le_refl _
  have hflip := WP_FLIP (p := Interp.half)
  rw [wp_def] at hflip
  obtain ⟨b, hb₁, hb₂, -, hb₃⟩ := hflip 1 valid_one hemp 1 1 hv1 hle1
  have hvS := valid_run (Interp.flip Interp.half) (1 : BoundedFootprintPsp) hv1
  have hbS : b ≤ (run (Interp.flip Interp.half) (1 : BoundedFootprintPsp)).1.toSpace := by
    have h := hb₁; rwa [mul_one] at h
  have hlaw := entails_trans (own_mono hbS) hb₃
  -- on the fibre at `v` the result is surely `v`, hence surely a constant
  have hstep : ∀ v : Bool,
      (⌈result (run (Interp.flip Interp.half) (1 : BoundedFootprintPsp)) = v⌉ : FProp)
        ⊢ constQ (result (run (Interp.flip Interp.half) (1 : BoundedFootprintPsp))) := by
    intro v
    cases v
    · exact or_intro_r
    · exact or_intro_l
  have hconst := entails_trans hlaw (entails_trans C_UNIT_R.1
    (entails_trans (C_CONS hstep) ((convex_def _).1 (hconv _) _)))
  rcases own_or_elim hvS hconst with h1 | h1
  · have h := entails_trans (and_intro (entails_trans h1 SURE_DIRAC.2) hlaw) DIST_INJ
    rw [own_def] at h
    exact delta_ne_bernoulli true half_ne_zero half_ne_one (UpperSetBI.mem_pure.1 (h _ hvS (UpperSetBI.mem_own.2
      (le_refl (run (Interp.flip Interp.half) (1 : BoundedFootprintPsp)).1.toSpace))))
  · have h := entails_trans (and_intro (entails_trans h1 SURE_DIRAC.2) hlaw) DIST_INJ
    rw [own_def] at h
    exact delta_ne_bernoulli false half_ne_zero half_ne_one (UpperSetBI.mem_pure.1 (h _ hvS (UpperSetBI.mem_own.2
      (le_refl (run (Interp.flip Interp.half) (1 : BoundedFootprintPsp)).1.toSpace))))

/-- **Sequencing is unsound at `AEProper`.**  Take `C := flip half`, `F := pure` (so that
`C >>= F = C`) and `Q := constQ`.  The premise holds outright (`wp_flip_valuePost`), so the
rule would give `⊢ wp (flip half) constQ`; reading that at the unit ambient produces a
resource below the run's space on which the coin is surely `true` or surely `false`, while
`WP_FLIP` makes that same run's space give the coin the law `bernoulliWeights (1/2)`.
`DIST_INJ` then equates a point mass with a fair coin. -/
theorem WPBind_counterexample :
    ¬ ∀ {α β : Type} {m : Type → Type} [Monad m] [Interp.LawfulBernoulliInterpretable m]
        [Inhabited α] [Inhabited β] {C : m α} {F : α → m β} {Q : RV β → FProp},
        AEProper Q → wp C ⦃X, valuePost X (fun v ↦ wp (F v) Q)⦄ ⊢ wp (C >>= F) Q := by
  intro hbind
  have hbad : ⊢ wp (Interp.flip Interp.half >>= (pure : Bool → Interp.BernoulliM Bool)) constQ :=
    entails_trans wp_flip_valuePost (hbind aeProper_constQ)
  rw [bind_pure] at hbad
  have hemp : (1 : BoundedFootprintSpace Bool) ∈ (UpperSetBI.emp :
      UpperSet (BoundedFootprintSpace Bool)) := by
    exact UpperSetBI.mem_emp.2 (le_refl 1)
  have hv1 : ✓(1 : BoundedFootprintPsp).psp := BoundedFootprintPsp.valid_one
  have hle1 : (1 : BoundedFootprintSpace Bool) * 1 ≤ (1 : BoundedFootprintPsp).toSpace := by
    rw [mul_one]
    show (1 : BoundedFootprintSpace Bool).val ≤ (1 : BoundedFootprintPsp).toSpace.val
    rw [BoundedFootprintPsp.toSpace_val]
    exact le_refl _
  have hflip := WP_FLIP (p := Interp.half)
  rw [wp_def] at hbad hflip
  obtain ⟨b, hb₁, hb₂, -, hb₃⟩ := hbad 1 valid_one hemp 1 1 hv1 hle1
  obtain ⟨b', hb'₁, hb'₂, -, hb'₃⟩ := hflip 1 valid_one hemp 1 1 hv1 hle1
  have hvS := valid_run (Interp.flip Interp.half) (1 : BoundedFootprintPsp) hv1
  have hbS : b ≤ (run (Interp.flip Interp.half) (1 : BoundedFootprintPsp)).1.toSpace := by
    have h := hb₁; rwa [mul_one] at h
  have hb'S : b' ≤ (run (Interp.flip Interp.half) (1 : BoundedFootprintPsp)).1.toSpace := by
    have h := hb'₁; rwa [mul_one] at h
  have h2 := entails_trans (own_mono hb'S) hb'₃
  rcases own_or_elim hvS (entails_trans (own_mono hbS) hb₃) with h1 | h1
  · have h := entails_trans (and_intro (entails_trans h1 SURE_DIRAC.2) h2) DIST_INJ
    rw [own_def] at h
    exact delta_ne_bernoulli true half_ne_zero half_ne_one (UpperSetBI.mem_pure.1 (h _ hvS (UpperSetBI.mem_own.2
      (le_refl (run (Interp.flip Interp.half) (1 : BoundedFootprintPsp)).1.toSpace))))
  · have h := entails_trans (and_intro (entails_trans h1 SURE_DIRAC.2) h2) DIST_INJ
    rw [own_def] at h
    exact delta_ne_bernoulli false half_ne_zero half_ne_one (UpperSetBI.mem_pure.1 (h _ hvS (UpperSetBI.mem_own.2
      (le_refl (run (Interp.flip Interp.half) (1 : BoundedFootprintPsp)).1.toSpace))))

/-- **The two sequencing directions cannot be packaged as one bi-entailment**: a `⊣⊢` would
give the direction `WPBind_counterexample` refutes. -/
theorem WPBind_biEntails_counterexample :
    ¬ ∀ {α β : Type} {m : Type → Type} [Monad m] [Interp.LawfulBernoulliInterpretable m]
        [Inhabited α] [Inhabited β] {C : m α} {F : α → m β} {Q : RV β → FProp},
        AEProper Q → (wp C ⦃X, valuePost X (fun v ↦ wp (F v) Q)⦄ ⊣⊢ wp (C >>= F) Q) :=
  fun h ↦ WPBind_counterexample fun hQ ↦ (h hQ).1

set_option linter.style.haveILetI false in
/-- **The converse of `WP_BIND` is unsound.**  Take `C := flip half`, `F := pure` and
`Q := (· ~ Ber½)`.  The premise holds by `WP_FLIP`, so the rule would split the coin's result
along its law and ask, on the fibre at `v`, for `wp (pure v) Q`; read at the fibre's own
ambient, that makes the constant `v` distributed as a fair coin. -/
theorem WPBindInv_counterexample :
    ¬ ∀ {α β : Type} {m : Type → Type} [Monad m] [Interp.LawfulBernoulliInterpretable m]
        [Inhabited α] [Inhabited β] {C : m α} {F : α → m β} {Q : RV β → FProp},
        AEProper Q → wp (C >>= F) Q ⊢ wp C ⦃X, valuePost X (fun v ↦ wp (F v) Q)⦄ := by
  intro hinv
  set Ber : PMF Bool :=
    bernoulliWeights Interp.half with hBer
  have hpre : ⊢ wp (Interp.flip Interp.half >>= (pure : Bool → Interp.BernoulliM Bool))
      ⦃X, X ~ Ber⦄ := by
    rw [bind_pure]
    exact WP_FLIP
  have hbad : ⊢ wp (Interp.flip Interp.half) ⦃X, valuePost X
      (fun v ↦ wp (pure v : Interp.BernoulliM Bool) ⦃X, X ~ Ber⦄)⦄ :=
    entails_trans hpre (hinv (aeProper_hasDistribution Ber))
  have hemp : (1 : BoundedFootprintSpace Bool) ∈ (UpperSetBI.emp :
      UpperSet (BoundedFootprintSpace Bool)) := by
    exact UpperSetBI.mem_emp.2 (le_refl 1)
  have hv1 : ✓(1 : BoundedFootprintPsp).psp := BoundedFootprintPsp.valid_one
  have hle1 : (1 : BoundedFootprintSpace Bool) * 1 ≤ (1 : BoundedFootprintPsp).toSpace := by
    rw [mul_one]
    show (1 : BoundedFootprintSpace Bool).val ≤ (1 : BoundedFootprintPsp).toSpace.val
    rw [BoundedFootprintPsp.toSpace_val]
    exact le_refl _
  rw [wp_def] at hbad
  obtain ⟨b, hb₁, hvb, -, hb₃⟩ := hbad 1 valid_one hemp 1 1 hv1 hle1
  -- the run of the coin, and the conditioning the premise produced
  set μ₁ : BoundedFootprintPsp := (run (Interp.flip Interp.half) (1 : BoundedFootprintPsp)).1
    with hμ₁
  have h₁ : ✓μ₁.psp := valid_run_psp 1 hv1 (Interp.flip Interp.half)
  set P₁ : PSpace Ω := ValidPSp.toPSpace ⟨μ₁.psp, h₁⟩ with hP₁
  have hμ₁P : μ₁.psp = .some P₁ := ValidPSp.eq_some_toPSpace h₁
  have hvμ₁ : ✓(μ₁.toSpace) := by
    show μ₁.toSpace.val ≠ (⊤ : PSp Ω)
    rw [μ₁.toSpace_val]
    exact PSp.valid_def.mp h₁
  have hbμ : b ≤ μ₁.toSpace := by rw [mul_one] at hb₁; exact hb₁
  have hb₃' : own b ⊢ valuePost (result (run (Interp.flip Interp.half) (1 : BoundedFootprintPsp)))
      (fun v ↦ wp (pure v : Interp.BernoulliM Bool) ⦃X, X ~ Ber⦄) := hb₃
  obtain ⟨ν, mm, hbfm, κ, R, hmix, hMR, hfib⟩ := valuePost_elim hvb hb₃'
  set M : BoundedFootprintSpace Bool := ⟨(mm : PSp Ω), hbfm⟩ with hM
  have hmp : IsProbabilityMeasure mm.μ := PSpace.isProbability
  have hMRμ : M * R ≤ μ₁.toSpace := le_trans hMR hbμ
  have hvMR : ✓(M * R) := valid_mono hMRμ hvμ₁
  have hvR : ✓R := valid_mul_r hvMR
  obtain ⟨r, hr⟩ : ∃ r : PSpace Ω, (R : PSp Ω) = .some r :=
    Option.ne_none_iff_exists'.mp (PSp.valid_def.mp hvR)
  obtain ⟨y, hy⟩ : ∃ y : PSpace Ω, ((M * R : BoundedFootprintSpace Bool) : PSp Ω) = .some y :=
    Option.ne_none_iff_exists'.mp (PSp.valid_def.mp hvMR)
  have hymr : y =ᵢ mm ⊕ᵢ r := by
    apply PSp.mul_inversion
    have h := hy
    rw [show ((M * R : BoundedFootprintSpace Bool) : PSp Ω)
      = PSp.mul (M : PSp Ω) (R : PSp Ω) from rfl, hr] at h
    exact h
  have hyP : y ≤ P₁ := by
    have h : (.some y : PSp Ω) ≤ .some P₁ := by
      rw [← hy, ← hμ₁P, ← μ₁.toSpace_val]; exact hMRμ
    exact WithTop.coe_le_coe.1 h
  have hmP : mm.ms ≤ P₁.ms := le_trans (PSpace.le_of_isIndependentProduct_left hymr).1 hyP.1
  have hrP : r.ms ≤ P₁.ms := le_trans (PSpace.le_of_isIndependentProduct_right hymr).1 hyP.1
  -- a value in the support, and the ambient its fibre lives in
  obtain ⟨v, hv⟩ := ν.support_nonempty
  have hac : κ.1 v ≪ mm.μ := kernel_fibre_ac κ hmix hv
  haveI hκp : IsProbabilityMeasure (κ.1 v) := κ.2.isProbabilityMeasure v
  set g : Ω → ENNReal := (κ.1 v).rnDeriv mm.μ with hg
  set ρ : Measure[P₁.ms] Ω := P₁.μ.withDensity g with hρ
  have hρrect : ∀ E, MeasurableSet[r.ms] E → ∀ F, MeasurableSet[mm.ms] F →
      ρ (E ∩ F) = r.μ E * κ.1 v F :=
    fun E hE F hF ↦ PSpace.withDensity_rect hymr hyP (κ.1 v) hac hE hF
  haveI hρp : IsProbabilityMeasure ρ := ⟨by
    have h := hρrect Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ
    rwa [Set.inter_univ, measure_univ (μ := r.μ), measure_univ (μ := κ.1 v), one_mul] at h⟩
  set τ : BoundedFootprintPsp := BoundedFootprintPsp.reweight μ₁ h₁ ρ hρp with hτ
  have hτpsp : τ.psp = .some ⟨⟨P₁.ms, ρ⟩, hρp⟩ := rfl
  have hτvalid : ✓τ.psp := reweight_valid
  have hvm : ✓((mm : PSp Ω)) := PSp.valid_def.mpr (Option.some_ne_none _)
  have hk : HasBoundedFootprint (((κ v : PSpace Ω)) : PSp Ω) :=
    hasBoundedFootprint_congr hvm (PSp.valid_def.mpr (Option.some_ne_none _)) (by
      rw [ValidPSp.toPSpace_eq hvm rfl, ValidPSp.toPSpace_eq _ rfl,
        ProbabilityTheory.TrivialMarkovKernel.ms_apply]) hbfm
  set K : BoundedFootprintSpace Bool := ⟨((κ v : PSpace Ω) : PSp Ω), hk⟩ with hK
  have hKR : K * R ≤ τ.toSpace := by
    let Pτ : PSpace Ω := ⟨⟨P₁.ms, ρ⟩, hρp⟩
    have hsup : mm.ms ⊔ r.ms ≤ Pτ.ms := by
      rw [show Pτ.ms = P₁.ms from PSpace.ms_mk _ _]; exact sup_le hmP hrP
    have hX' : @PSpace.trim Ω Pτ (mm.ms ⊔ r.ms) hsup =ᵢ (κ v : PSpace Ω) ⊕ᵢ r := by
      refine PSpace.isIndependentProduct_def.2 ⟨?_, fun F hF E hE ↦ ?_⟩
      · rw [PSpace.trim_ms, ProbabilityTheory.TrivialMarkovKernel.ms_apply]
      rw [ProbabilityTheory.TrivialMarkovKernel.ms_apply] at hF
      have h1 : ρ (F ∩ E) = κ.1 v F * r.μ E := by
        rw [Set.inter_comm, hρrect E hE F hF, mul_comm]
      rw [PSpace.trim_μ_apply
          (((le_sup_left : mm.ms ≤ _) _ hF).inter ((le_sup_right : r.ms ≤ _) _ hE)),
        show Pτ.μ (F ∩ E) = ρ (F ∩ E) from PSpace.μ_mk_apply _ _ _,
        ProbabilityTheory.TrivialMarkovKernel.μ_apply]
      exact h1
    show PSp.mul (.some (κ v : PSpace Ω)) (R : PSp Ω) ≤ τ.toSpace.val
    rw [hr, τ.toSpace_val, hτpsp]
    exact (le_of_eq (PSp.mul_respect_independentProduct hX')).trans
      (WithTop.coe_le_coe.2 (PSpace.trim_le (p := Pτ) hsup))
  have hRK : R * K ≤ τ.toSpace := by rw [mul_comm]; exact hKR
  have hvτ : ✓(τ.toSpace) := by
    show τ.toSpace.val ≠ (⊤ : PSp Ω)
    rw [τ.toSpace_val]
    exact PSp.valid_def.mp hτvalid
  have hvRK : ✓(R * K) := valid_mono hRK hvτ
  -- the fibre's resource for the continuation, and the continuation run there
  obtain ⟨Pi, hbfPi, Ri, hPR, -, hRi⟩ := liftPred_sep_elim hvRK (hfib v hv hk)
  have hRi_le : Ri ≤ R * K :=
    le_trans (by rw [mul_comm]; exact le_mul_of_one_le PSp.one_le) hPR
  have hRiτ : Ri * 1 ≤ τ.toSpace := by rw [mul_one]; exact le_trans hRi_le hRK
  have hvRi : ✓Ri := valid_mono (le_trans hRi_le hRK) hvτ
  rw [own_def, wp_def] at hRi
  obtain ⟨b', -, hvb', -, hb'Q⟩ := hRi Ri hvRi (UpperSetBI.mem_own.2 (le_refl Ri)) τ 1 hτvalid hRiτ
  rw [result_run_pure (m := Interp.BernoulliM) v τ hτvalid] at hb'Q
  -- on it, the constant `v` has both the law `δ v` and the law of a fair coin
  have hemp' : own b' ⊢ iprop(emp) := by
    rw [own_def]
    exact fun y _ hy ↦ UpperSetBI.mem_emp.2 (le_trans PSp.one_le (UpperSetBI.mem_own.1 hy))
  have hδ : own b' ⊢ (fun _ : Ω ↦ v) ~ δ v :=
    entails_trans hemp' (entails_trans
      (liftPred_of_forall (a := fun ω ↦ LiftBinary.lift (fun _ : Ω ↦ v) v ω) (fun _ ↦ rfl))
      (SURE_DIRAC (E := fun _ : Ω ↦ v) (v := v)).2)
  have h := entails_trans (and_intro hδ hb'Q) DIST_INJ
  rw [own_def] at h
  exact delta_ne_bernoulli v half_ne_zero half_ne_one (UpperSetBI.mem_pure.1 (h b' hvb' (UpperSetBI.mem_own.2 (le_refl b'))))

end

end Foxglove
