module

public import Foxglove.Rules.WP.Swap
public import Foxglove.Rules.WP.Bind
public import Foxglove.Rules.WP.Dist

@[expose] public section
namespace Foxglove

open ProbSpace
open Iris OrderedUnitalResourceAlgebra
open UpperSetBI
open Iris BI UpperSetBI OURAProp

noncomputable section

/-! # The rules of Foxglove

The unary rules of Bluebell (arXiv 2402.18708; Fig. 9, 10 and 11), together with the bind
rule of Amaryllis (arXiv 2605.13765, Fig. 2) adapted to the monadic `wp`.  Not included: the
rules with index side conditions (`and-to-star`, `c-and`, `wp-conj`), the relational rules,
and the rules for imperative programs. -/

variable {P Q : FProp} {α β : Type} {v₀ : α} {E E₁ : RV α} {E₂ : RV β}
  {μ μ' μ₁ : PMF α} {μ₂ : PMF β} {K K₁ K₂ : α → FProp}

/-! ### Distribution ownership -/

open MeasureTheory in
/-- `dist-inj` (Bluebell, Fig. 9). -/
theorem DIST_INJ : E ~ μ ∧ E ~ μ' ⊢ ⌜μ = μ'⌝ := by
  intro m hv h
  obtain ⟨h₁, h₂⟩ := h
  -- the ambient space the two claims share
  obtain ⟨y, hy⟩ : ∃ y : PSpace Ω, m.val = some y :=
    Option.ne_none_iff_exists'.mp (PSp.valid_def.mp hv)
  -- the space witnessing `E ~ μ`, and its resource, sit below `m`
  obtain ⟨q₁, ⟨P, hq₁P⟩, hq₁m⟩ := h₁
  obtain ⟨b₁, b₂, hle₁, hown₁, hpure₁⟩ := (Quotient.exact hq₁P).2 m hv hq₁m
  obtain ⟨r₁, ⟨hbf₁, hr₁⟩, hb₁⟩ := hown₁
  have hb₁m : b₁ ≤ m := le_trans (le_mul_of_one_le PSp.one_le) hle₁
  have hPb₁ := (Quotient.exact hr₁).2 b₁ (valid_mono hb₁m hv) hb₁
  -- and the same for `E ~ μ'`
  obtain ⟨q₂, ⟨P', hq₂P'⟩, hq₂m⟩ := h₂
  obtain ⟨c₁, c₂, hle₂, hown₂, hpure₂⟩ := (Quotient.exact hq₂P').2 m hv hq₂m
  obtain ⟨r₂, ⟨hbf₂, hr₂⟩, hc₁⟩ := hown₂
  have hc₁m : c₁ ≤ m := le_trans (le_mul_of_one_le PSp.one_le) hle₂
  have hP'c₁ := (Quotient.exact hr₂).2 c₁ (valid_mono hc₁m hv) hc₁
  have hPy : P ≤ y := by
    have hPm : (P : PSp Ω) ≤ (m : PSp Ω) := le_trans hPb₁ hb₁m
    rw [hy] at hPm
    exact WithTop.coe_le_coe.1 hPm
  have hP'y : P' ≤ y := by
    have hP'm : (P' : PSp Ω) ≤ (m : PSp Ω) := le_trans hP'c₁ hc₁m
    rw [hy] at hP'm
    exact WithTop.coe_le_coe.1 hP'm
  -- both push `E` forward along the one ambient measure, so the two laws agree
  obtain ⟨ham, hμ₁⟩ := hpure₁
  obtain ⟨ham', hμ₂⟩ := hpure₂
  show μ = μ'
  apply @PMF.toMeasure_injective _ ⊤
  calc @PMF.toMeasure _ ⊤ μ
      = @Measure.map Ω _ P.ms ⊤ E P.μ := hμ₁.symm
    _ = @Measure.map Ω _ P'.ms ⊤ E P'.μ := PSpace.map_eq_of_le hPy hP'y ham ham'
    _ = @PMF.toMeasure _ ⊤ μ' := hμ₂

/-- `sure-merge` (Bluebell, Fig. 9). -/
theorem SURE_MERGE {E₁ E₂ : RV Prop} : ⌈E₁⌉ ∗ ⌈E₂⌉ ⊣⊢ ⌈E₁ ∧ E₂⌉ :=
  ⟨liftPred_sep, liftPred_split⟩

/-- `sure-and-star` (Bluebell, Fig. 9). -/
theorem SURE_AND_STAR {a : Ω → Prop} : ⌈a⌉ ∧ P ⊢ ⌈a⌉ ∗ P := by
  induction P using Quotient.ind
  intro m hv ⟨hE, hP⟩
  obtain ⟨q, ⟨W, hq⟩, hqm⟩ := hE
  obtain ⟨d₁, d₂, hle, hown, hpure⟩ := (Quotient.exact hq).2 m hv hqm
  obtain ⟨r₁, ⟨hbfW, hr₁⟩, hd₁⟩ := hown
  have hd₁m : d₁ ≤ m := le_trans (le_mul_of_one_le PSp.one_le) hle
  have hWm : (⟨(W : PSp Ω), hbfW⟩ : BoundedFootprintSpace Bool) ≤ m :=
    le_trans ((Quotient.exact hr₁).2 d₁ (valid_mono hd₁m hv) hd₁) hd₁m
  obtain ⟨y, hy⟩ : ∃ y : PSpace Ω, m.val = (y : PSp Ω) :=
    Option.ne_none_iff_exists'.mp (PSp.valid_def.mp hv)
  have hWy : W ≤ y := by
    have h : (W : PSp Ω) ≤ (m : PSp Ω) := hWm
    rw [hy] at h
    exact WithTop.coe_le_coe.1 h
  -- a measurable null cover of the exceptional set, and the 0-1 trim it generates
  obtain ⟨N, hNsub, hNmeas, hNnull⟩ :=
    @MeasureTheory.exists_measurable_superset_of_null Ω W.ms W.μ _ hpure
  have hgen : MeasurableSpace.generateFrom {N} ≤ W.ms :=
    MeasurableSpace.generateFrom_le (by rintro t rfl; exact hNmeas)
  set W₀ : PSpace Ω := @PSpace.trim Ω W _ hgen with hW₀
  have hW₀W : W₀ ≤ W := PSpace.trim_le hgen
  have hNmeas₀ : @MeasurableSet Ω W₀.ms N := MeasurableSpace.measurableSet_generateFrom rfl
  have hN₀ : W₀.μ N = 0 := by
    rw [MeasureOnSpace.le_preserves_measure hW₀W hNmeas₀]
    exact hNnull
  have hbf₀ : HasBoundedFootprint ((W₀ : PSp Ω)) :=
    hasBoundedFootprint_mono (PSp.valid_def.mpr (Option.some_ne_none _))
      (WithTop.coe_le_coe.2 hW₀W) hbfW
  -- the trim is independent of the whole space, so splitting it off costs nothing
  have hind : y =ᵢ W₀ ⊕ᵢ y :=
    PSpace.isIndependentProduct_of_zero_one_le (le_trans hW₀W hWy)
      (PSpace.zero_or_one_generateFrom (le_refl _) hN₀)
  have hb₀m : (⟨(W₀ : PSp Ω), hbf₀⟩ : BoundedFootprintSpace Bool) * m ≤ m := by
    show PSp.mul (W₀ : PSp Ω) m.val ≤ m.val
    rw [hy]
    exact le_of_eq (mul_respect_independentProduct hind)
  refine ⟨_, m, hb₀m, ⟨_, ⟨W₀, rfl⟩, ?_⟩, hP⟩
  refine ⟨_, 1, le_of_eq (mul_one _),
    ⟨_, ⟨hbf₀, rfl⟩, le_refl (⟨(W₀ : PSp Ω), hbf₀⟩ : BoundedFootprintSpace Bool)⟩, ?_⟩
  exact MeasureTheory.measure_mono_null hNsub hN₀

/-- `prod-split` (Bluebell, Fig. 9). -/
theorem PROD_SPLIT :
  (fun s => (E₁ s, E₂ s)) ~ (μ₁ ⊗ μ₂) ⊢ E₁ ~ μ₁ ∗ E₂ ~ μ₂ := by
  intro m hv h
  obtain ⟨q, ⟨P, hq⟩, hqm⟩ := h
  obtain ⟨d₁, d₂, hle, hown, hpure⟩ := (Quotient.exact hq).2 m hv hqm
  obtain ⟨r₁, ⟨hbfP, hr₁⟩, hd₁⟩ := hown
  obtain ⟨ham, hlaw⟩ := hpure
  have hd₁m : d₁ ≤ m := le_trans (le_mul_of_one_le PSp.one_le) hle
  have hPm : (⟨(P : PSp Ω), hbfP⟩ : BoundedFootprintSpace Bool) ≤ m :=
    le_trans ((Quotient.exact hr₁).2 d₁ (valid_mono hd₁m hv) hd₁) hd₁m
  obtain ⟨D₁, D₂, hD₁P, hD₂P, hmul, hlaw₁, hlaw₂⟩ := PSpace.split_of_product_law P ham hlaw
  have hbf₁ : HasBoundedFootprint (D₁ : PSp Ω) :=
    hasBoundedFootprint_mono (PSp.valid_def.mpr (Option.some_ne_none _))
      (WithTop.coe_le_coe.2 hD₁P) hbfP
  have hbf₂ : HasBoundedFootprint (D₂ : PSp Ω) :=
    hasBoundedFootprint_mono (PSp.valid_def.mpr (Option.some_ne_none _))
      (WithTop.coe_le_coe.2 hD₂P) hbfP
  refine ⟨⟨D₁, hbf₁⟩, ⟨D₂, hbf₂⟩, le_trans ?_ hPm, ⟨_, ⟨D₁, rfl⟩, ?_⟩, ⟨_, ⟨D₂, rfl⟩, ?_⟩⟩
  · exact hmul
  · exact ⟨_, 1, le_of_eq (mul_one _),
      ⟨_, ⟨hbf₁, rfl⟩, le_refl (⟨(D₁ : PSp Ω), hbf₁⟩ : BoundedFootprintSpace Bool)⟩, hlaw₁⟩
  · exact ⟨_, 1, le_of_eq (mul_one _),
      ⟨_, ⟨hbf₂, rfl⟩, le_refl (⟨(D₂ : PSp Ω), hbf₂⟩ : BoundedFootprintSpace Bool)⟩, hlaw₂⟩

/-! ### Joint conditioning -/

/-- `c-true` (Bluebell, Fig. 9). -/
theorem C_TRUE : ⊢ 𝒞⟨μ⟩ _v; ftrue := by
  unfold jointConditioning
  iexists (1 : PSpace Ω), unitKernel α
  isplitl []
  · exact ownP_one
  · isplitl []
    · ipureintro
      show PSpace.μ 1 = (μ.toMeasureWithMs ⊤).bind (fun _ ↦ PSpace.μ 1)
      simp [PMF.toMeasureWithMs]
    · iintro %v Hv
      exact entails_ftrue

/-- `c-false` (Bluebell, Fig. 9). -/
theorem C_FALSE : 𝒞⟨μ⟩ _v; ffalse ⊢ ffalse := by
  intro r hv h
  have hown : own r ⊢ jointConditioning μ (fun _ ↦ ffalse) :=
    fun _ _ hry ↦ UpperSet.upper _ hry h
  obtain ⟨s, -, -, w, -, hX⟩ := cond_elim hv hown
  obtain ⟨v, hvsupp⟩ := μ.support_nonempty
  obtain ⟨X, hXval, hXK⟩ := hX v hvsupp
  have hXv : ✓X := by
    show X.val ≠ (⊤ : PSp Ω)
    rw [hXval]
    exact WithTop.coe_ne_top
  exact False.elim (hXK X hXv (le_refl X))

/-- `c-cons` (Bluebell, Fig. 9). -/
theorem C_CONS (h : ∀ v, K₁ v ⊢ K₂ v) : 𝒞⟨μ⟩ v; K₁ v ⊢ 𝒞⟨μ⟩ v; K₂ v := by
  unfold jointConditioning
  iintro ⟨%m, %κ, Hown, %hmix, Hall⟩
  iexists m, κ
  isplitl [Hown]
  · iexact Hown
  · isplitl []
    · ipureintro
      exact hmix
    · iintro %v Hv
      iapply (h v)
      iapply Hall
      iexact Hv

/-- `c-frame` (Bluebell, Fig. 9). -/
theorem C_FRAME : P ∗ 𝒞⟨μ⟩ v; K v ⊢ 𝒞⟨μ⟩ v; (P ∗ K v) := by
  unfold jointConditioning
  iintro ⟨HP, %m, %κ, Hown, %hmix, Hall⟩
  iexists m, κ
  isplitl [Hown]
  · iexact Hown
  · isplitl []
    · ipureintro
      exact hmix
    · iintro %v Hv
      isplitl [HP]
      · iexact HP
      · iapply Hall
        iexact Hv

set_option linter.style.haveILetI false in
open MeasureTheory in
/-- `c-unit-l` (Bluebell, Fig. 9). -/
theorem C_UNIT_L : 𝒞⟨δ v₀⟩ v; K v ⊣⊢ K v₀ := by
  constructor
  · unfold jointConditioning
    iintro ⟨%m, %κ, Hown, %hmix, Hall⟩
    -- the only fibre, at `v₀`, is `m` itself
    have hκ : (κ v₀ : PSpace Ω) = m := by
      apply Subtype.ext
      show (⟨m.ms, κ.1 v₀⟩ : MeasureOnSpace Ω) = m.1
      have h : κ.1 v₀ = m.μ := by
        letI : MeasurableSpace α := ⊤
        rw [hmix]
        simp only [PMF.toMeasureWithMs, PMF.toMeasure_pure]
        exact (Measure.dirac_bind (ProbabilityTheory.Kernel.measurable κ.1) v₀).symm
      rw [h]
    have hown : ownP m ⊢ ownP (κ v₀) := by rw [hκ]
    ispecialize Hall $$ %⟨v₀, (PMF.mem_support_pure_iff _ _).2 rfl⟩
    iapply Hall
    iapply hown
    iexact Hown
  · unfold jointConditioning
    iintro HK
    iexists (1 : PSpace Ω), unitKernel α
    isplitl []
    · exact ownP_one
    · isplitl []
      · ipureintro
        show PSpace.μ 1 = (((δ v₀) : PMF α).toMeasureWithMs ⊤).bind (fun _ ↦ PSpace.μ 1)
        simp [PMF.toMeasureWithMs]
      · iintro %v Hv
        -- the only value in the support is `v₀`
        obtain ⟨v, hv⟩ := v
        rw [PMF.mem_support_pure_iff] at hv
        subst hv
        iexact HK

set_option linter.style.haveILetI false in
open MeasureTheory in
/-- `c-unit-r` (Bluebell, Fig. 9). -/
theorem C_UNIT_R : E ~ μ ⊣⊢ 𝒞⟨μ⟩ v; ⌈E = v⌉ := by
  constructor
  · unfold hasDistribution jointConditioning
    iintro ⟨%P, HP, %hpure⟩
    obtain ⟨ham, hlaw⟩ := hpure
    obtain ⟨κ, hmix, hsure⟩ := condKernel_of_law P ham hlaw
    iexists P, κ
    isplitl [HP]
    · iexact HP
    · isplitl []
      · ipureintro
        exact hmix
      · iintro %v Hv
        dsimp only [LiftPred.lift]
        iexists (κ v)
        isplitl [Hv]
        · iexact Hv
        · ipureintro
          exact hsure v v.2
  · intro r hv h
    have hown : own r ⊢ jointConditioning μ (fun v ↦ ⌈E = v⌉) :=
      fun _ _ hry ↦ UpperSet.upper _ hry h
    obtain ⟨s, hbfs, hsr, w, hsmix, hX⟩ := cond_elim hv hown
    -- on each fibre the continuation made `E` surely its value
    have hsure : ∀ v ∈ μ.support, (w v).1 {ρ | ¬ E ρ = v} = 0 := by
      intro v hv'
      obtain ⟨X, hXval, hXK⟩ := hX v hv'
      have hXv : ✓X := by
        show X.val ≠ (⊤ : PSp Ω)
        rw [hXval]
        exact WithTop.coe_ne_top
      obtain ⟨q₀, ⟨P', hq₀⟩, hq₀m⟩ := hXK X hXv (le_refl X)
      obtain ⟨e₁, _, hlee, hown', hpure'⟩ := (Quotient.exact hq₀).2 _ hXv hq₀m
      obtain ⟨r', ⟨hbf', hr'⟩, he₁⟩ := hown'
      have he₁m := le_trans (le_mul_of_one_le PSp.one_le) hlee
      have hP' := (Quotient.exact hr').2 e₁ (valid_mono he₁m hXv) he₁
      have hP'S : P' ≤ (show PSpace Ω from ⟨⟨s.ms, (w v).1⟩, (w v).2⟩) := by
        have h : (P' : PSp Ω) ≤ X.val := le_trans hP' he₁m
        rw [hXval] at h
        exact WithTop.coe_le_coe.1 h
      exact PSpace.null_of_le hP'S hpure'
    -- so the mixture of the fibres gives `E` the law `μ`
    have hmix : ∀ S, @MeasurableSet Ω s.ms S →
        s.μ S = ∫⁻ v, (w v).1 S ∂(μ.toMeasureWithMs ⊤) := by
      letI : MeasurableSpace α := ⊤
      intro S hS
      rw [hsmix, Measure.bind_apply hS measurable_from_top.aemeasurable]
    obtain ⟨ham, hlaw⟩ := law_of_fibres s (fun v ↦ (w v).1) hmix
      (fun v _ ↦ (w v).2.measure_univ) hsure
    exact ⟨_, ⟨s, rfl⟩, ⟨(s : PSp Ω), hbfs⟩, 1, by rw [mul_one]; exact hsr,
      ⟨_, ⟨hbfs, rfl⟩, le_refl (⟨(s : PSp Ω), hbfs⟩ : BoundedFootprintSpace Bool)⟩,
      ⟨ham, hlaw⟩⟩

variable {μ₀ : PMF (α × β)} {κ : α → PMF β} {K : (α × β) → FProp} in
set_option linter.style.haveILetI false in
open MeasureTheory in
/-- `c-assoc` (Bluebell, Fig. 9). -/
theorem C_ASSOC (h : μ₀ = (PMF.bind μ fun v ↦ PMF.bind (κ v) fun w ↦ PMF.pure (v, w))) :
  𝒞⟨μ⟩ v; 𝒞⟨κ v⟩ w; K (v, w) ⊢ 𝒞⟨μ₀⟩ (v, w); K (v, w) := by
  classical
  subst h
  obtain ⟨Kr, rfl⟩ : ∃ Kr : α × β → UpperSet (BoundedFootprintSpace Bool),
      K = fun x ↦ fmk (Kr x) :=
    ⟨fun x ↦ (K x).out, funext fun x ↦ (Quotient.out_eq _).symm⟩
  intro r hv hr
  have hown : own r ⊢ jointConditioning μ
      (fun v ↦ jointConditioning (κ v) (fun w ↦ fmk (Kr (v, w)))) :=
    fun _ _ hry ↦ UpperSet.upper _ hry hr
  -- the outer conditioning
  obtain ⟨s, hbfs, hsr, w, hsmix, hX⟩ := cond_elim hv hown
  have hsp := s.2
  -- the inner conditionings, one per value of the outer one
  have hinner : ∀ v ∈ μ.support, ∃ (sv : PSpace Ω)
      (wv : β → {p : Measure[sv.ms] Ω // IsProbabilityMeasure p}),
      sv ≤ (⟨⟨s.ms, (w v).1⟩, (w v).2⟩ : PSpace Ω) ∧
      sv.μ = ((κ v).toMeasureWithMs ⊤).bind (fun b ↦ (wv b).1) ∧
      ∀ b ∈ (κ v).support, ∃ Y : BoundedFootprintSpace Bool,
        Y.val = ((show PSpace Ω from ⟨⟨sv.ms, (wv b).1⟩, (wv b).2⟩) : PSp Ω) ∧
          (own Y ⊢ fmk (Kr (v, b))) := by
    intro v hv'
    obtain ⟨X, hXval, hXK⟩ := hX v hv'
    have hXv : ✓X := by
      show X.val ≠ (⊤ : PSp Ω)
      rw [hXval]
      exact WithTop.coe_ne_top
    obtain ⟨sv, hbfsv, hsvX, wv, hsvmix, hY⟩ := cond_elim hXv hXK
    refine ⟨sv, wv, ?_, hsvmix, hY⟩
    have h : (sv : PSp Ω) ≤ X.val := hsvX
    rw [hXval] at h
    exact WithTop.coe_le_coe.1 h
  choose sv wv hsvle hsvmix hY using hinner
  -- the joint fibres: `S v` tilted by the density of `T v b` over `s v`
  let Λμ : α × β → Measure[s.ms] Ω := fun x ↦
    if hx : x.1 ∈ μ.support ∧ x.2 ∈ (κ x.1).support then
      (w x.1).1.withDensity (((wv x.1 hx.1 x.2).1).rnDeriv (sv x.1 hx.1).μ)
    else s.μ
  -- on the inner space's sets, the joint fibre is `T v b`
  have hΛT : ∀ v (hv : v ∈ μ.support), ∀ b ∈ (κ v).support, ∀ A,
      @MeasurableSet Ω (sv v hv).ms A → Λμ (v, b) A = (wv v hv b).1 A := by
    intro v hv b hb A hA
    haveI := (wv v hv b).2
    have hsvp := (sv v hv).2
    have hac : (wv v hv b).1 ≪ (sv v hv).μ := bind_fibre_ac (hsvmix v hv) hb
    simp only [Λμ, show (v, b).1 ∈ μ.support ∧ (v, b).2 ∈ (κ (v, b).1).support from ⟨hv, hb⟩]
    refine (PSpace.withDensity_le_apply (hsvle v hv)
      (@Measure.measurable_rnDeriv Ω (sv v hv).ms (wv v hv b).1 (sv v hv).μ) hA).trans ?_
    rw [Measure.withDensity_rnDeriv_eq _ _ hac]
  have hΛprob : ∀ x, IsProbabilityMeasure (Λμ x) := by
    rintro ⟨v, b⟩
    by_cases hx : v ∈ μ.support ∧ b ∈ (κ v).support
    · constructor
      rw [hΛT v hx.1 b hx.2 _ MeasurableSet.univ]
      exact (wv v hx.1 b).2.measure_univ
    · simp only [Λμ, show ¬ ((v, b).1 ∈ μ.support ∧ (v, b).2 ∈ (κ (v, b).1).support) from hx,
        ↓reduceDIte]
      exact hsp
  letI : MeasurableSpace (α × β) := ⊤
  obtain ⟨Λk, hΛk⟩ : ∃ Λk : ProbabilityTheory.TrivialMarkovKernel (α × β) s, ∀ x, Λk.1 x = Λμ x := by
    letI : MeasurableSpace Ω := s.ms
    exact ⟨⟨⟨Λμ, measurable_from_top⟩, ⟨hΛprob⟩⟩, fun _ ↦ rfl⟩
  -- `s` is the joint mixture of the joint fibres
  have hΛmix : s.μ = (((μ.bind fun v ↦ (κ v).bind fun w ↦ PMF.pure (v, w)).toMeasureWithMs ⊤).bind
      Λk.1) := by
    refine @Measure.ext Ω s.ms _ _ fun A hA ↦ ?_
    rw [Measure.bind_apply hA (ProbabilityTheory.Kernel.measurable Λk.1).aemeasurable,
      lintegral_pmf_bind_pair, hsmix]
    letI : MeasurableSpace α := ⊤
    rw [Measure.bind_apply hA measurable_from_top.aemeasurable]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_mem_support μ] with v hv
    refine (mixture_of_tilts (hsvle v hv) (κ v) (fun b ↦ (wv v hv b).1) (fun b ↦ (wv v hv b).2)
      (hsvmix v hv) hA).trans ?_
    refine lintegral_congr_ae ?_
    filter_upwards [ae_mem_support (κ v)] with b hb
    rw [hΛk]
    simp only [Λμ, show (v, b).1 ∈ μ.support ∧ (v, b).2 ∈ (κ (v, b).1).support from ⟨hv, hb⟩]
    rfl
  -- the joint conditioning, framed by nothing: each joint fibre contains `T v b`
  refine ⟨_, ⟨s, rfl⟩, _, ⟨Λk, rfl⟩, ⟨(s : PSp Ω), hbfs⟩, 1, by rw [mul_one]; exact hsr,
    ⟨_, ⟨hbfs, rfl⟩, le_refl (⟨(s : PSp Ω), hbfs⟩ : BoundedFootprintSpace Bool)⟩,
    1, 1, le_of_eq (mul_one 1), hΛmix, ?_⟩
  intro p ⟨x, hxp⟩
  obtain ⟨⟨a, b⟩, hab⟩ := x
  obtain ⟨ha, hb⟩ : a ∈ μ.support ∧ b ∈ (κ a).support := by
    rw [PMF.mem_support_bind_iff] at hab
    obtain ⟨v, hv, hvb⟩ := hab
    rw [PMF.mem_support_bind_iff] at hvb
    obtain ⟨b', hb', hpb⟩ := hvb
    rw [PMF.mem_support_pure_iff] at hpb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpb
    exact ⟨hv, hb'⟩
  refine (Quotient.exact hxp).1 1 valid_one fun y _ hy ↦ ?_
  rw [one_mul]
  -- `y` owns the joint fibre, hence `T a b`, which satisfies the continuation
  obtain ⟨q, ⟨hbfΛ, hq⟩, hyq⟩ := hy
  have hvy : ✓y := valid_mono (le_of_eq (one_mul y).symm) ‹_›
  have hΛy := (Quotient.exact hq).2 y hvy hyq
  obtain ⟨Y, hYval, hYK⟩ := hY a ha b hb
  have hTΛ : (⟨⟨(sv a ha).ms, (wv a ha b).1⟩, (wv a ha b).2⟩ : PSpace Ω)
      ≤ (Λk (a, b) : PSpace Ω) :=
    PSpace.le_of_measure_eq (le_trans (hsvle a ha).1 le_rfl)
      fun u hu ↦ by
        show _ = Λk.1 (a, b) u
        rw [hΛk]
        exact (hΛT a ha b hb u hu).symm
  have hYy : Y ≤ y := by
    refine le_trans ?_ hΛy
    show Y.val ≤ ((Λk (a, b) : PSpace Ω) : PSp Ω)
    rw [hYval]
    exact WithTop.coe_le_coe.2 hTΛ
  exact hYK y hvy hYy

set_option linter.style.haveILetI false in
open MeasureTheory in
/-- `c-unassoc` (Bluebell, Fig. 9). -/
theorem C_UNASSOC {K : β → FProp} :
  𝒞⟨PMF.bind μ κ⟩ w; K w ⊢ 𝒞⟨μ⟩ v; 𝒞⟨κ v⟩ w; K w := by
  intro r hv hr
  have hown : own r ⊢ jointConditioning (μ.bind κ) (fun w ↦ K w) :=
    fun _ _ hry ↦ UpperSet.upper _ hry hr
  obtain ⟨s, hbfs, hsr, w, hsmix, hX⟩ := cond_elim hv hown
  have hsp := s.2
  -- the outer fibres: the `κ v`-mixtures of the joint fibres
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ProbabilityTheory.TrivialMarkovKernel α s,
      ∀ v, ℓ.1 v = ((κ v).toMeasureWithMs ⊤).bind fun b ↦ (w b).1 := by
    letI : MeasurableSpace Ω := s.ms
    letI : MeasurableSpace α := ⊤
    letI : MeasurableSpace β := ⊤
    refine ⟨⟨⟨fun v ↦ ((κ v).toMeasureWithMs ⊤).bind fun b ↦ (w b).1, measurable_from_top⟩,
      ⟨fun v ↦ ⟨?_⟩⟩⟩, fun _ ↦ rfl⟩
    show (((κ v).toMeasureWithMs ⊤).bind fun b ↦ (w b).1) Set.univ = 1
    rw [Measure.bind_apply MeasurableSet.univ measurable_from_top.aemeasurable,
      lintegral_congr fun b ↦ (w b).2.measure_univ, lintegral_one]
    show (κ v).toMeasure Set.univ = 1
    exact measure_univ
  -- they mix back to `s`
  have hℓmix : s.μ = (μ.toMeasureWithMs ⊤).bind ℓ.1 := by
    refine @Measure.ext Ω s.ms _ _ fun A hA ↦ ?_
    letI : MeasurableSpace α := ⊤
    letI : MeasurableSpace β := ⊤
    rw [hsmix, Measure.bind_apply hA measurable_from_top.aemeasurable, toMeasure_bind_eq,
      Measure.lintegral_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable,
      Measure.bind_apply hA (ProbabilityTheory.Kernel.measurable ℓ.1).aemeasurable]
    refine lintegral_congr fun v ↦ ?_
    rw [hℓ, Measure.bind_apply hA measurable_from_top.aemeasurable]
  -- the inner kernels hand back the joint fibres
  let ι : ∀ v, ProbabilityTheory.TrivialMarkovKernel β (ℓ v) := fun _ ↦
    letI : MeasurableSpace Ω := s.ms
    letI : MeasurableSpace β := ⊤
    ⟨⟨fun b ↦ (w b).1, measurable_from_top⟩, ⟨fun b ↦ (w b).2⟩⟩
  have hKb : ∀ v (b : β), b ∈ (μ.bind κ).support → ownP (ι v b) ⊢ K b := by
    intro v b hb
    obtain ⟨X, hXval, hXK⟩ := hX b hb
    unfold ownP
    refine Iris.BI.exists_elim fun hbf ↦ ?_
    rw [show (⟨((ι v b : PSpace Ω) : PSp Ω), hbf⟩ : BoundedFootprintSpace Bool) = X from
      Subtype.ext (by rw [hXval]; rfl)]
    exact hXK
  have key : ownP s ⊢ 𝒞⟨μ⟩ v; 𝒞⟨κ v⟩ w; K w := by
    unfold jointConditioning
    iintro Hown
    iexists s, ℓ
    isplitl [Hown]
    · iexact Hown
    · isplitl []
      · ipureintro
        exact hℓmix
      · iintro %v Hv
        iexists (ℓ v : PSpace Ω), ι v
        isplitl [Hv]
        · iexact Hv
        · isplitl []
          · ipureintro
            show ℓ.1 v = ((κ v).toMeasureWithMs ⊤).bind fun b ↦ (w b).1
            exact hℓ v
          · iintro %b Hb
            iapply (hKb v b ((PMF.mem_support_bind_iff _ _ _).2 ⟨v, v.2, b.2⟩))
            iexact Hb
  exact key r hv ⟨_, ⟨hbfs, rfl⟩, hsr⟩

/-- `c-skolem` (Bluebell, Fig. 9). -/
theorem C_SKOLEM {α X : Type} {μ : PMF α} {Q : (α × X) → FProp} :
  𝒞⟨μ⟩ v; (∃ x : X, Q (v, x)) ⊢ ∃ (f : α → X), 𝒞⟨μ⟩ v; Q (v, f v) := by
  classical
  obtain ⟨Qr, rfl⟩ : ∃ Qr : α × X → UpperSet (BoundedFootprintSpace Bool),
      Q = fun x ↦ fmk (Qr x) :=
    ⟨fun x ↦ (Q x).out, funext fun x ↦ (Quotient.out_eq _).symm⟩
  intro r hv hr
  have hown : own r ⊢ jointConditioning μ (fun v ↦ iprop(∃ x : X, fmk (Qr (v, x)))) :=
    fun _ _ hry ↦ UpperSet.upper _ hry hr
  obtain ⟨s, hbfs, hsr, w, hsmix, hX⟩ := cond_elim hv hown
  -- a witness per value in the support, read off the fibre itself
  have hwit : ∀ v ∈ μ.support, ∃ x : X, ∀ p : PSpace Ω,
      (p : PSp Ω) = ((show PSpace Ω from ⟨⟨s.ms, (w v).1⟩, (w v).2⟩) : PSp Ω) →
        ownP p ⊢ fmk (Qr (v, x)) := by
    intro v hv'
    obtain ⟨Y, hYval, hYK⟩ := hX v hv'
    have hYv : ✓Y := by
      show Y.val ≠ (⊤ : PSp Ω)
      rw [hYval]
      exact WithTop.coe_ne_top
    obtain ⟨q, ⟨x, hqx⟩, hYq⟩ := hYK Y hYv (le_refl Y)
    have hmem := (Quotient.exact hqx).2 Y hYv hYq
    refine ⟨x, fun p hp ↦ ?_⟩
    unfold ownP
    refine Iris.BI.exists_elim fun hbf ↦ ?_
    intro y _ hy
    have hpY : (⟨(p : PSp Ω), hbf⟩ : BoundedFootprintSpace Bool) = Y :=
      Subtype.ext (hp.trans hYval.symm)
    rw [hpY] at hy
    exact UpperSet.upper _ hy hmem
  obtain ⟨v₀, hv₀⟩ := μ.support_nonempty
  have : Nonempty X := ⟨(hwit v₀ hv₀).choose⟩
  choose! f hf using hwit
  -- the fibres of `s` themselves form the kernel
  let ℓ : ProbabilityTheory.TrivialMarkovKernel α s :=
    letI : MeasurableSpace Ω := s.ms
    letI : MeasurableSpace α := ⊤
    ⟨⟨fun v ↦ (w v).1, measurable_from_top⟩, ⟨fun v ↦ (w v).2⟩⟩
  have key : ownP s ⊢ ∃ f : α → X, 𝒞⟨μ⟩ v; fmk (Qr (v, f v)) := by
    iintro Hown
    iexists f
    unfold jointConditioning
    iexists s, ℓ
    isplitl [Hown]
    · iexact Hown
    · isplitl []
      · ipureintro
        exact hsmix
      · iintro %v Hv
        iapply (hf v.1 v.2 (ℓ v.1) rfl)
        iexact Hv
  exact key r hv ⟨_, ⟨hbfs, rfl⟩, hsr⟩

variable {f : β → α} in
set_option linter.style.haveILetI false in
open MeasureTheory in
/-- `c-transf` (Bluebell, Fig. 9). -/
theorem C_TRANSF
  (h₁ : Set.BijOn f μ₂.support μ₁.support)
  (h₂ : ∀ b ∈ μ₂.support, μ₂ b = μ₁ (f b)) :
  𝒞⟨μ₁⟩ a; K a ⊢ 𝒞⟨μ₂⟩ b; K (f b) := by
  intro r hv hr
  have hown : own r ⊢ jointConditioning μ₁ (fun a ↦ K a) :=
    fun _ _ hry ↦ UpperSet.upper _ hry hr
  obtain ⟨s, hbfs, hsr, w, hsmix, hX⟩ := cond_elim hv hown
  -- the fibres pulled back along `f`
  let ℓ : ProbabilityTheory.TrivialMarkovKernel β s :=
    letI : MeasurableSpace Ω := s.ms
    letI : MeasurableSpace β := ⊤
    ⟨⟨fun b ↦ (w (f b)).1, measurable_from_top⟩, ⟨fun b ↦ (w (f b)).2⟩⟩
  -- they mix to `s` along `μ'`: reindex the sum over the support by the bijection
  have hℓmix : s.μ = (μ₂.toMeasureWithMs ⊤).bind ℓ.1 := by
    refine @Measure.ext Ω s.ms _ _ fun A hA ↦ ?_
    letI : MeasurableSpace α := ⊤
    rw [Measure.bind_apply hA (ProbabilityTheory.Kernel.measurable ℓ.1).aemeasurable, hsmix,
      Measure.bind_apply hA measurable_from_top.aemeasurable,
      pmf_lintegral_eq_tsum, pmf_lintegral_eq_tsum, ← h₁.equiv.tsum_eq]
    refine tsum_congr fun b ↦ ?_
    show (w (f b)).1 A * μ₁ (f b) = (w (f b)).1 A * μ₂ b
    rw [h₂ b b.2]
  have hKb : ∀ b ∈ μ₂.support, ownP (ℓ b) ⊢ K (f b) := by
    intro b hb
    obtain ⟨X, hXval, hXK⟩ := hX (f b) (h₁.mapsTo hb)
    unfold ownP
    refine Iris.BI.exists_elim fun hbf ↦ ?_
    rw [show (⟨((ℓ b : PSpace Ω) : PSp Ω), hbf⟩ : BoundedFootprintSpace Bool) = X from
      Subtype.ext (by rw [hXval]; rfl)]
    exact hXK
  have key : ownP s ⊢ 𝒞⟨μ₂⟩ b; K (f b) := by
    unfold jointConditioning
    iintro Hown
    iexists s, ℓ
    isplitl [Hown]
    · iexact Hown
    · isplitl []
      · ipureintro
        exact hℓmix
      · iintro %b Hb
        iapply (hKb b.1 b.2)
        iexact Hb
  exact key r hv ⟨_, ⟨hbfs, rfl⟩, hsr⟩

variable {E : RV Prop} in
set_option linter.style.haveILetI false in
open MeasureTheory in
/-- `sure-convex` (Bluebell, Fig. 11). -/
theorem C_SURE_CONVEX : 𝒞⟨μ⟩ _v; ⌈E⌉ ⊢ ⌈E⌉ := by
  intro r hv hr
  have hown : own r ⊢ jointConditioning μ (fun _ ↦ ⌈E⌉) :=
    fun _ _ hry ↦ UpperSet.upper _ hry hr
  obtain ⟨s, hbfs, hsr, w, hsmix, hX⟩ := cond_elim hv hown
  -- each fibre makes `a` sure
  have hnull : ∀ v ∈ μ.support, (w v).1 {ρ | ¬ E ρ} = 0 := by
    intro v hv'
    obtain ⟨X, hXval, hXK⟩ := hX v hv'
    have hXv : ✓X := by
      show X.val ≠ (⊤ : PSp Ω)
      rw [hXval]
      exact WithTop.coe_ne_top
    obtain ⟨q, ⟨P, hq⟩, hqX⟩ := hXK X hXv (le_refl X)
    obtain ⟨e₁, _, hle, hownP, hpure⟩ := (Quotient.exact hq).2 X hXv hqX
    obtain ⟨r₁, ⟨hbfP, hr₁⟩, he₁⟩ := hownP
    have he₁X : e₁ ≤ X := le_trans (le_mul_of_one_le PSp.one_le) hle
    have hPX : (P : PSp Ω) ≤ X.val :=
      le_trans ((Quotient.exact hr₁).2 e₁ (valid_mono he₁X hXv) he₁) he₁X
    rw [hXval] at hPX
    exact PSpace.null_of_le (WithTop.coe_le_coe.1 hPX) hpure
  -- measurable null covers on `s`, and their intersection over the support
  have hcover : ∀ v ∈ μ.support, ∃ N, {ρ | ¬ E ρ} ⊆ N ∧ @MeasurableSet Ω s.ms N ∧
      (w v).1 N = 0 :=
    fun v hv' ↦ @exists_measurable_superset_of_null Ω s.ms _ _ (hnull v hv')
  choose! N hNsub hNmeas hNnull using hcover
  have := μ.support_countable.to_subtype
  have hNi : @MeasurableSet Ω s.ms (⋂ v : μ.support, N v) :=
    @MeasurableSet.iInter Ω _ s.ms _ _ fun v : μ.support ↦ hNmeas v.1 v.2
  have hsN : s.μ (⋂ v : μ.support, N v) = 0 := by
    letI : MeasurableSpace α := ⊤
    rw [hsmix, Measure.bind_apply hNi measurable_from_top.aemeasurable]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [ae_mem_support μ] with v hv'
    exact measure_mono_null (Set.iInter_subset _ ⟨v, hv'⟩) (hNnull v hv')
  have hs : s.μ {ρ | ¬ E ρ} = 0 :=
    measure_mono_null (Set.subset_iInter fun v : μ.support ↦ hNsub v.1 v.2) hsN
  exact ⟨_, ⟨s, rfl⟩, r, 1, by rw [mul_one], ⟨_, ⟨hbfs, rfl⟩, hsr⟩, hs⟩

/-- `sure-str-convex` (Bluebell, Fig. 9). -/
theorem SURE_STR_CONVEX {K : α → FProp} {E : RV Prop} :
  𝒞⟨μ⟩ v; (K v ∗ ⌈E⌉) ⊢ ⌈E⌉ ∗ 𝒞⟨μ⟩ v; K v := by
  have hsure : 𝒞⟨μ⟩ v; (K v ∗ ⌈E⌉) ⊢ ⌈E⌉ :=
    entails_trans (C_CONS fun _ ↦ sep_elim_right) C_SURE_CONVEX
  have hcond : 𝒞⟨μ⟩ v; (K v ∗ ⌈E⌉) ⊢ 𝒞⟨μ⟩ v; K v := C_CONS fun _ ↦ sep_elim_left
  exact entails_trans (and_intro hsure hcond) SURE_AND_STAR

variable {Q : α × β → FProp} in
/-- `c-for-all` (Bluebell, Fig. 9). -/
theorem C_FOR_ALL :
  𝒞⟨μ⟩ v; (∀ (x : β), Q (v, x)) ⊢ ∀ (x : β), 𝒞⟨μ⟩ v; Q (v, x) :=
  forall_intro fun x ↦ C_CONS fun _ ↦ forall_elim x

/-- `c-pure` (Bluebell, Fig. 9). -/
theorem C_PURE {X : Set α} :
    ⌜μ.toMeasureWithMs ⊤ X = 1⌝ ∗ 𝒞⟨μ⟩ v; K v ⊣⊢ 𝒞⟨μ⟩ v; (⌜v ∈ X⌝ ∗ K v) := by
  have hsupp : μ.toMeasureWithMs ⊤ X = 1 ↔ μ.support ⊆ X :=
    @PMF.toMeasure_apply_eq_one_iff α ⊤ μ X MeasurableSpace.measurableSet_top
  constructor
  · unfold jointConditioning
    iintro ⟨%hX, %m, %κ, Hown, %hmix, Hall⟩
    iexists m, κ
    isplitl [Hown]
    · iexact Hown
    · isplitl []
      · ipureintro
        exact hmix
      · iintro %v Hv
        isplitl []
        · ipureintro
          exact hsupp.1 hX v.2
        · iapply Hall
          iexact Hv
  · -- every fibre is a valid resource, so its continuation's pure part holds
    have hpure : 𝒞⟨μ⟩ v; (⌜v ∈ X⌝ ∗ K v) ⊢ ⌜μ.toMeasureWithMs ⊤ X = 1⌝ := by
      intro r hv hr
      have hown : own r ⊢ jointConditioning μ (fun v ↦ iprop(⌜v ∈ X⌝ ∗ K v)) :=
        fun _ _ hry ↦ UpperSet.upper _ hry hr
      obtain ⟨s, -, -, w, -, hX'⟩ := cond_elim hv hown
      refine hsupp.2 fun v hv' ↦ ?_
      obtain ⟨Y, hYval, hYK⟩ := hX' v hv'
      have hYv : ✓Y := by
        show Y.val ≠ (⊤ : PSp Ω)
        rw [hYval]
        exact WithTop.coe_ne_top
      exact (entails_trans hYK sep_elim_left) Y hYv (le_refl Y)
    refine pure_elim _ hpure fun hX ↦ ?_
    iintro H
    isplitl []
    · ipureintro
      exact hX
    · iapply (C_CONS fun _ ↦ sep_elim_right)
      iexact H

/-! ### Ownership and laws -/

/-- `sure-dirac` (Bluebell, Fig. 11). -/
theorem SURE_DIRAC {v : α} : E ~ δ v ⊣⊢ ⌈E = v⌉ := by
  rw [hasDistribution_dirac]
  exact ⟨entails_rfl, entails_rfl⟩

/-- `sure-eq-inj` (Bluebell, Fig. 11). -/
theorem SURE_EQ_INJ {E : RV α} {v v' : α} : ⌈(E = v)⌉ ∗ ⌈(E = v')⌉ ⊢ ⌜v = v'⌝ :=
  entails_trans liftPred_sep
    (entails_trans (liftPred_mono fun _ h ↦ Eq.trans (Eq.symm h.1) h.2) liftPred_pure)

/-- `dirac-dup` (Bluebell, Fig. 11). -/
theorem DIRAC_DUP {v : α} : E ~ δ v ⊢ E ~ δ v ∗ E ~ δ v := by
  rw [hasDistribution_dirac]
  exact liftPred_dup

/-- `distr-subst` (Amaryllis, Fig. 1). -/
theorem DIST_SUBST {X Y : RV α} : X ~ μ ∗ ⌈X = Y⌉ ⊢ Y ~ μ :=
  entails_trans (sep_mono_left C_UNIT_R.1)
    (entails_trans Iris.BI.sep_comm.1 (entails_trans C_FRAME
      (entails_trans (C_CONS fun _ ↦ liftPred_subst) C_UNIT_R.2)))

/-! ### Weakest precondition -/

section WeakestPrecondition

open Interp Interp.ProbTree Interp.ProbTree.BoundedFootprintPsp
open unitInterval

open Interp in
/-- `wp-value` (Amaryllis, Fig. 2). -/
theorem WPPure {α : Type} {m : Type → Type} [Monad m] [Interp.LawfulBernoulliInterpretable m]
    [Inhabited α] {Q : RV α → FProp} {x : α} : Q (fun _ ↦ x) ⊢ wp (pure x : m α) Q := by
  obtain ⟨U, hU⟩ : ∃ U : UpperSet (BoundedFootprintSpace Bool), Q (fun _ ↦ x) = fmk U :=
    ⟨(Q (fun _ ↦ x)).out, (Quotient.out_eq _).symm⟩
  rw [hU]
  intro a hva ha μ₀ c hvalid hle
  refine ⟨a, ?_, hva, le_sup_left, ?_⟩
  · have hsp : ((run (pure x : m α) μ₀).1.toSpace : BoundedFootprintSpace Bool) = μ₀.toSpace :=
      Subtype.ext (run_pure_psp x μ₀ hvalid)
    rw [hsp]
    exact hle
  · rw [result_run_pure (m := m) x μ₀ hvalid, hU]
    exact own_entails_of_mem ha

/-- `wp-cons` (Bluebell, Fig. 10). -/
theorem WPCons {α : Type} [Inhabited α] {m : Type → Type} [Monad m]
    [Interp.LawfulBernoulliInterpretable m]
    {Q Q' : RV α → FProp} {t : m α} (h : ∀ v, Q v ⊢ Q' v) : iprop(wp t Q) ⊢ wp t Q' := by
  intro a hva ha μ₀ c hv hle
  obtain ⟨b, hb₁, hb₂, hb₃, hb₄⟩ := ha μ₀ c hv hle
  exact ⟨b, hb₁, hb₂, hb₃, entails_trans hb₄ (h _)⟩

/-- `wp-frame` (Bluebell, Fig. 10). -/
theorem WPFrame {α : Type} [Inhabited α] {m : Type → Type} [Monad m]
    [Interp.LawfulBernoulliInterpretable m]
    {P : FProp} {Q : RV α → FProp} {t : m α} :
    iprop(P ∗ wp t Q) ⊢ wp t (fun v ↦ iprop(P ∗ (Q v))) := by
  obtain ⟨U, rfl⟩ : ∃ U : UpperSet (BoundedFootprintSpace Bool), P = fmk U :=
    ⟨P.out, (Quotient.out_eq _).symm⟩
  obtain ⟨Qr, rfl⟩ : ∃ Qr : RV α → UpperSet (BoundedFootprintSpace Bool),
      Q = fun X ↦ fmk (Qr X) :=
    ⟨fun X ↦ (Q X).out, funext fun X ↦ (Quotient.out_eq _).symm⟩
  intro a hva ha μ₀ c hv hle
  obtain ⟨p, w, hpw, hp, hw⟩ := ha
  have hvr : ✓((run t μ₀).1.toSpace) := valid_run t μ₀ hv
  have hwle : w * (p * c) ≤ μ₀.toSpace := by
    calc w * (p * c) = (p * w) * c := by rw [← mul_assoc, mul_comm w p]
      _ ≤ a * c := mul_le_mul_right_le hpw c
      _ ≤ μ₀.toSpace := hle
  obtain ⟨b, hb₁, hb₂, hb₃, hb₄⟩ := hw μ₀ (p * c) hv hwle
  have hkey : (p * b) * c ≤ (run t μ₀).1.toSpace := by
    calc (p * b) * c = b * (p * c) := by rw [mul_comm p b, mul_assoc]
      _ ≤ _ := hb₁
  have hvpb : ✓(p * b) := valid_mul (valid_mono hkey hvr)
  refine ⟨p * b, hkey, hvpb, ?_, ?_⟩
  · -- the frame measures no more than `a` did, and `b` is local to `w`
    have hpa : msOf p ≤ msOf a := msOf_mono (le_trans (le_mul_of_one_le PSp.one_le) hpw)
    have hwa : msOf w ≤ msOf a :=
      msOf_mono (le_trans (by rw [mul_comm]; exact le_mul_of_one_le PSp.one_le) hpw)
    calc msOf (p * b) ≤ msOf p ⊔ msOf b := msOf_mul_le hvpb
      _ ≤ msOf a ⊔ (msOf w ⊔ freshMs μ₀ (Interp.BernoulliInterpretable.interp t)) :=
          sup_le_sup hpa hb₃
      _ ≤ msOf a ⊔ freshMs μ₀ (Interp.BernoulliInterpretable.interp t) :=
          sup_le le_sup_left (sup_le (le_trans hwa le_sup_left) le_sup_right)
  · intro mm hvmm hmm
    exact ⟨p, b, hmm, hp, hb₄ b hb₂ (le_refl b)⟩

/-- `c-wp-swap` (Bluebell, Fig. 10), with `AEProper` in place of `ownX`. -/
theorem CWPSwap {α β : Type} {m : Type → Type} [Monad m] [Interp.BernoulliInterpretable m] [Inhabited α]
  {C : m α} {μ : PMF β} {Q : β → RV α → FProp} (hQ : ∀ v, AEProper (Q v)) :
    iprop(𝒞⟨μ⟩ v; wp C (Q v)) ⊢ wp C (fun x ↦ 𝒞⟨μ⟩ v; Q v x) := by
  unfold jointConditioning
  refine exists_elim fun m₀ ↦ exists_elim fun κ ↦ ?_
  refine pure_elim _ (entails_trans sep_elim_right sep_elim_left) fun hmix ↦ ?_
  refine entails_trans (sep_mono_right sep_elim_right) ?_
  unfold ownP
  refine entails_trans sep_exists_right.1 (exists_elim fun hbf ↦ ?_)
  refine own_sep_entails_fmk fun a R hva hle hR ↦ ?_
  refine CWPSwap_core hQ m₀ κ hmix hbf R (fun v hv hk ↦ ?_) a hva hle
  refine entails_trans own_mul_sep (entails_trans (sep_mono hR (exists_intro
    (Ψ := fun h : HasBoundedFootprint ((κ v : PSpace Ω) : PSp Ω) ↦
      own (⟨((κ v : PSpace Ω) : PSp Ω), h⟩ : BoundedFootprintSpace Bool)) hk)) ?_)
  exact wand_elim (forall_elim (Ψ := fun v : μ.support ↦
    iprop(ownP (κ v) -∗ wp C (Q v))) ⟨v, hv⟩)

/-- `wp-samp` (Bluebell, Fig. 10), for the law of any closed program. -/
theorem WPDist {α : Type} [Inhabited α] [Countable α] (t : BernoulliM α) (ν : PMF α)
    (hν : ∀ a : α, lawOf t a = ν a) :
    ⊢ wp t (fun X ↦ X ~ ν) := by
  intro a hva ha μ₀ c hvalid hle
  have hcμ : c ≤ μ₀.toSpace := by
    refine le_trans ?_ hle
    conv_lhs => rw [← one_mul c]
    exact mul_le_mul_right_le ha c
  obtain ⟨b, hb₁, hb₂, hb₃, hb₄⟩ := WPDist_core t ν hν μ₀ hvalid c hcμ
  exact ⟨b, hb₁, hb₂, le_trans hb₃ le_sup_right, hb₄⟩

/-- `wp-samp` (Bluebell, Fig. 10), for a coin. -/
theorem WPFlip {p : I} :
    ⊢ wp (Interp.flip p)
        (fun X ↦ X ~ bernoulliWeights (toNNReal p) (Interp.toNNReal_le_one p)) := by
  refine WPDist (Interp.flip p) _ (fun b ↦ ?_)
  unfold lawOf
  have h0 : runValue (Interp.flip p) ⁻¹' {b} = prefixEqEvent [b] := preimage_head b
  rw [h0]
  refine Eq.trans (measure_congr_tree (fixpoint_oneFlip (fun b : Bool ↦ b) p) _) ?_
  show flipMeasure _ p _ = _
  rw [flipMeasure_apply_singleton p b (measurableSet_prefixEqEvent_singleton b),
    flipWeight_eq_bernoulliWeights]

/-- `wp-bind` (Amaryllis, Fig. 2), for the monadic `wp`: the continuation runs once per fibre
of `C`'s law, and the conclusion keeps the conditioning. -/
theorem WPBindC {α β : Type} {m : Type → Type} [Monad m]
    [Interp.LawfulBernoulliInterpretable m] [Inhabited α] [Inhabited β]
    {C : m α} {F : α → m β} {Q : α → RV β → FProp}
    (hQ : ∀ v, AEProper (Q v)) :
    wp C (fun X ↦ valuePost X (fun v ↦ wp (F v) (Q v)))
      ⊢ wp (C >>= F) (fun Y ↦ iprop(∃ ν : PMF α, 𝒞⟨ν⟩ v; Q v Y)) := by
  intro a hva ha μ₀ c hvalid hle
  obtain ⟨b, hbc, hvb, hbms, hbQ⟩ := ha μ₀ c hvalid hle
  exact WPBindC_core hQ μ₀ hvalid a c hva hle b hbc hvb hbms hbQ

/-- `wp-bind` with the conditioning collapsed, which needs `Convex` (`WPBind_counterexample`). -/
theorem WPBind {α β : Type} {m : Type → Type} [Monad m]
    [Interp.LawfulBernoulliInterpretable m] [Inhabited α] [Inhabited β]
    {C : m α} {F : α → m β} {Q : RV β → FProp}
    (hQ : AEProper Q) (hC : ∀ X : RV β, Convex (Q X)) :
    wp C (fun X ↦ valuePost X (fun v ↦ wp (F v) Q)) ⊢ wp (C >>= F) Q :=
  entails_trans (WPBindC (Q := fun _ ↦ Q) fun _ ↦ hQ)
    (WPCons fun Y ↦ exists_elim fun ν ↦ hC Y ν)

/-- `wp-bind` and `wp-samp` combined, for laws. -/
theorem WPBindDist {α β : Type} [Inhabited α] [Inhabited β] [Countable β]
    (t : BernoulliM α) (f : α → BernoulliM β) (ν : PMF α) (κ : α → PMF β)
    (hν : ∀ a, lawOf t a = ν a) (hκ : ∀ a b, lawOf (f a) b = κ a b) :
    ⊢ wp (t >>= f) (fun X ↦ X ~ ν.bind κ) := by
  refine WPDist (t >>= f) _ (fun b ↦ ?_)
  rw [lawOf_bind, PMF.bind_apply]
  exact tsum_congr fun a ↦ by rw [hν a, hκ a b]

end WeakestPrecondition

end

end Foxglove
