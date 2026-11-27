/-
The Haar-quotient integral of a normalizer translate.

For a locally compact second-countable group `G`, a closed subgroup `H`, a left-invariant
Haar measure `μ` on `G`, a right-invariant Haar measure `μH` on `H`, and an element `b` in
the **normalizer** of `H` (the hypothesis `hb : ∀ y, y ∈ H ↔ b * y * b⁻¹ ∈ H`) whose
conjugation action scales `μH` by `D ≠ 0`, this module proves the Haar-quotient translate
identity for complex-valued integrands:

for `h : G → ℂ` right-`H`-invariant and `b`-invariant, a `ℤ`-valued cocycle `m` with
`m (x * g) = m g` on `H` and `m (b * g) = m g + 1`, and a coefficient sequence `Φ` whose
weighted sum `∑' n, D^n * ‖Φ n‖` converges,

  `Integrable (fun q => h q.out * Φ (m q.out)) (HaarQuotient.measure μ H μH)`

and

  `∫ q, h q.out * Φ (m q.out) ∂(HaarQuotient.measure μ H μH)
     = (∑' n, D^n * Φ n) * ∫ q in {q | m q.out = 0}, h q.out ∂(HaarQuotient.measure μ H μH)`.

This is the "unfold the `ℤ`-orbit of the normalizer translate" lemma: the quotient splits
into the `ℤ`-indexed translates `bⁿ · {m = 0}` by the cocycle `m`, each carrying the same
`h`-integral and the scaling factor `Dⁿ` on the measure, and the sum over `n` is a
geometric-type series that converges because `∑ Dⁿ ‖Φ n‖` does.  Its two premises are the
density and the Fubini identity of this `HaarQuotient` API
(`MeasureTheory/HaarQuotient.lean`).  The automorphic consumer is the archimedean normalizer
of the Borel subgroup, where `b` is the Weyl element and `D` is the modulus.

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_HaarQuotient_integrable_and_integral_mul_comp_out_eq_tsum_mul_setIntegral_of_mem_normalizer.lean>

spec-pin: Theorems/Thm_HaarQuotient_integrable_and_integral_mul_comp_out_eq_tsum_mul_setIntegral_of_mem_normalizer.lean
spec-pin: P2M/Sol/S_HaarQuotient_integrable_and_integral_mul_comp_out_eq_tsum_mul_setIntegral_of_mem_normalizer.lean

## Substitution, not transcription (SET-AF104 D2)

The pin's 16 declarations are **15 already-public engine rows plus this headline**.  The 15
`PeelC.*` helpers — `exists_out_mk_eq`, `comp_out_comp_mk_eq`, `measurable_comp_out`,
`leftTranslate`, `leftTranslate_mk`, `inv_conj_iff`, `leftTranslate_leftTranslate_inv`,
`leftTranslate_inv_leftTranslate`, `measurable_leftTranslate`, `leftTranslateEquiv`,
`leftTranslateEquiv_apply`, `leftTranslateEquiv_symm_apply`,
`leftTranslateEquiv_apply_eq_mk`, `leftTranslateEquiv_symm_apply_eq_mk`,
`leftTranslateEquiv_out` — were **already transcribed into this module's own premise file**
`FLTForHuman/MeasureTheory/HaarQuotient.lean` (§ "The orbit decomposition under a
normalizing element", imported below) as public `HaarQuotient.*` declarations, as the pin's
text with only the generated `PeelC` namespace label dropped.  They are therefore
**substituted by import**, not re-declared: re-declaring a public full name that already
exists is forbidden (FR-0274), and the pin's `PeelC` label is exactly what the naming policy
removes.  So this module declares one row, and `check_port` measures 1, not 16; the engine
diff below accounts for the other 15.

The header's "no private helpers" holds: the pin has none, and neither does this module.

## Heartbeat probe (recorded, never installed — FR-0225)

`lake env lean -DautoImplicit=false -DmaxHeartbeats=N` on this file, one run per value: **silent
at `N = 8000`, first failure at `N = 7500`** (a deterministic `whnf` timeout at the
`integral_iUnion` step of `hsplit`); at `7000` the failure moves into `hI`'s `rw [h2, ih, …]`,
at `6000` into `htsum`'s `simp_rw [← hcoe]`, and at `5000` it reaches the declaration itself.
So this whole row costs ≈8 k heartbeats against the project's 4 M.  Nothing is installed: the
edit loop runs at `200000` and the module carries no `set_option maxHeartbeats`.

## Gates (SET-AF104 D2, measured)

`check_port --force`: **1 ok / 0 mismatch / 0 missing / 0 own** (one row, because 15 of the
pin's 16 are substituted — see above).  Edit loop silent.  One locked `lake build` clean, no
warning line from this file.  `#print axioms` on the row: `[propext, Classical.choice,
Quot.sound]`.  `dedup --within`: 0 clusters.  `move_dead --dry-run`: 0 declarations, 0 lines.
-/
import FLTForHuman.MeasureTheory.HaarQuotient

noncomputable section

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

theorem HaarQuotient.integrable_and_integral_mul_comp_out_eq_tsum_mul_setIntegral_of_mem_normalizer
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (b : G) (hb : ∀ y : G, y ∈ H ↔ b * y * b⁻¹ ∈ H) (D : ℝ≥0) (hD₀ : D ≠ 0)
    (hbD : ∀ F : H → ℝ≥0∞, Measurable F →
      ∫⁻ x, F ⟨b * (x : G) * b⁻¹, (hb (x : G)).mp x.2⟩ ∂μH = (D : ℝ≥0∞) * ∫⁻ x, F x ∂μH)
    (m : G → ℤ) (hm : Measurable m) (hmH : ∀ x ∈ H, ∀ g : G, m (x * g) = m g)
    (hmb : ∀ g : G, m (b * g) = m g + 1)
    (h : G → ℂ) (hh : Measurable h) (hhH : ∀ x ∈ H, ∀ g : G, h (x * g) = h g)
    (hhb : ∀ g : G, h (b * g) = h g)
    (hint : IntegrableOn (fun q : MulAction.orbitRel.Quotient H G => h q.out)
      {q : MulAction.orbitRel.Quotient H G | m q.out = 0} (HaarQuotient.measure μ H μH))
    (Φ : ℤ → ℂ) (hΦ : Summable fun n : ℤ => (D : ℝ) ^ n * ‖Φ n‖) :
    Integrable (fun q : MulAction.orbitRel.Quotient H G => h q.out * Φ (m q.out)) (HaarQuotient.measure μ H μH) ∧
    (∫ q, h q.out * Φ (m q.out) ∂(HaarQuotient.measure μ H μH)) =
      (∑' n : ℤ, ((D : ℝ) : ℂ) ^ n * Φ n) *
        ∫ q in {q : MulAction.orbitRel.Quotient H G | m q.out = 0}, h q.out ∂(HaarQuotient.measure μ H μH) := by
  set ν := HaarQuotient.measure μ H μH with hν
  set T := HaarQuotient.leftTranslateEquiv H b hb with hT_def
  have hD₀' : (D : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hD₀
  have hDtop : (D : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  have hDC : ((D : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr hD₀)

  have hT : ∀ s : Set (MulAction.orbitRel.Quotient H G), MeasurableSet s →
      ν (T '' s) = (D : ℝ≥0∞) * ν s := by
    intro s hs
    set f : G → ℝ≥0∞ := fun g => s.indicator 1 (Quotient.mk'' g) with hf_def
    have hf : Measurable f := (measurable_one.indicator hs).comp measurable_quotient_mk''
    have hfH : ∀ x ∈ H, ∀ g : G, f (x * g) = f g := by
      intro x hx g
      simp only [hf_def]
      congr 1
      exact Quotient.sound' (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨⟨x, hx⟩, rfl⟩))
    have key := HaarQuotient.lintegral_comp_inv_mul_out_eq_mul_lintegral_of_mem_normalizer μ H hH μH b hb
      (D : ℝ≥0∞) hbD f hf hfH
    have hR : ∫⁻ q, f q.out ∂ν = ν s := by
      have : ∀ q : MulAction.orbitRel.Quotient H G, f q.out = s.indicator 1 q := fun q => by
        simp only [hf_def, Quotient.out_eq']
      simp_rw [this, lintegral_indicator_one hs]
    have hL : ∫⁻ q, f (b⁻¹ * q.out) ∂ν = ν (T '' s) := by
      rw [MeasurableEquiv.image_eq_preimage_symm]
      have : ∀ q : MulAction.orbitRel.Quotient H G, f (b⁻¹ * q.out) = (T.symm ⁻¹' s).indicator 1 q := by
        intro q
        have hq : (Quotient.mk'' (b⁻¹ * q.out) : MulAction.orbitRel.Quotient H G) = T.symm q :=
          (HaarQuotient.leftTranslateEquiv_symm_apply_eq_mk H b hb q).symm
        simp only [hf_def, hq]
        exact (Set.indicator_comp_right _).symm
      simp_rw [this]
      exact lintegral_indicator_one (T.symm.measurable hs)
    rw [← hL, ← hR, key]

  have hm' : Measurable fun q : MulAction.orbitRel.Quotient H G => m q.out :=
    HaarQuotient.measurable_comp_out H m hm hmH
  have hh' : Measurable fun q : MulAction.orbitRel.Quotient H G => h q.out :=
    HaarQuotient.measurable_comp_out H h hh hhH
  have hmT : ∀ q, m (T q).out = m q.out + 1 := by
    intro q
    obtain ⟨x, hx⟩ := HaarQuotient.leftTranslateEquiv_out H b hb q
    rw [hx, hmH _ x.2, hmb]
  have hhT : ∀ q, h (T q).out = h q.out := by
    intro q
    obtain ⟨x, hx⟩ := HaarQuotient.leftTranslateEquiv_out H b hb q
    rw [hx, hhH _ x.2, hhb]
  have hhS : ∀ q, h (T.symm q).out = h q.out := fun q => by
    conv_rhs => rw [← MeasurableEquiv.apply_symm_apply T q]
    exact (hhT _).symm

  set A : ℤ → Set (MulAction.orbitRel.Quotient H G) := fun n => {q | m q.out = n} with hA_def
  have hA : ∀ n, MeasurableSet (A n) := fun n => hm' (measurableSet_singleton n)
  have hdisj : Pairwise (Function.onFun Disjoint A) := by
    intro i j hij
    refine Set.disjoint_left.mpr fun q hqi hqj => hij ?_
    rw [hA_def] at hqi hqj
    exact hqi.symm.trans hqj
  have hunion : (⋃ n, A n) = Set.univ := by
    ext q; simp [hA_def]
  have hAsucc : ∀ n, A (n + 1) = T.symm ⁻¹' (A n) := by
    intro n; ext q
    simp only [hA_def, Set.mem_ofPred_eq, Set.mem_preimage]
    have h := hmT (T.symm q)
    rw [MeasurableEquiv.apply_symm_apply] at h
    rw [h]; exact add_left_inj 1

  have hmap : ν.map T.symm = (D : ℝ≥0∞) • ν := by
    refine Measure.ext fun s hs => ?_
    rw [Measure.map_apply T.symm.measurable hs, Measure.smul_apply, smul_eq_mul, ← hT s hs,
      MeasurableEquiv.image_eq_preimage_symm]

  have hΦ' : Summable fun n : ℤ => D ^ n * ‖Φ n‖₊ := by
    rw [← NNReal.summable_coe]
    simpa using hΦ
  have htsum : (∑' n : ℤ, (D : ℝ≥0∞) ^ n * ‖Φ n‖ₑ) ≠ ∞ := by
    have hcoe : ∀ n : ℤ, ((D ^ n * ‖Φ n‖₊ : ℝ≥0) : ℝ≥0∞) = (D : ℝ≥0∞) ^ n * ‖Φ n‖ₑ := fun n => by
      rw [ENNReal.coe_mul, ENNReal.coe_zpow hD₀]
      rfl
    simp_rw [← hcoe]
    exact ENNReal.tsum_coe_ne_top_iff_summable.mpr hΦ'
  have hmeas : Measurable fun q : MulAction.orbitRel.Quotient H G => h q.out * Φ (m q.out) :=
    hh'.mul ((measurable_of_countable Φ).comp hm')
  have hfi : Integrable (fun q : MulAction.orbitRel.Quotient H G => h q.out * Φ (m q.out)) ν := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    have hpeel := HaarQuotient.lintegral_mul_comp_out_eq_tsum_zpow_mul_setLIntegral_of_mem_normalizer μ H hH μH
      b hb (D : ℝ≥0∞) hD₀' hDtop hbD m hm hmH hmb (fun g => ‖h g‖ₑ) hh.enorm
      (fun x hx g => by simp only [hhH x hx g]) (fun g => by simp only [hhb g]) (fun n => ‖Φ n‖ₑ)
    show ∫⁻ q, ‖h q.out * Φ (m q.out)‖ₑ ∂ν < ∞
    simp_rw [enorm_mul]
    rw [hpeel]
    exact ENNReal.mul_lt_top htsum.lt_top hint.2
  refine ⟨hfi, ?_⟩

  set I : ℤ → ℂ := fun n => ∫ q in A n, h q.out ∂ν with hI_def
  have hstep : ∀ n, I (n + 1) = ((D : ℝ) : ℂ) * I n := by
    intro n
    simp only [hI_def]
    rw [hAsucc]
    calc ∫ q in T.symm ⁻¹' A n, h q.out ∂ν
        = ∫ q, (T.symm ⁻¹' A n).indicator (fun q => h q.out) q ∂ν :=
          (integral_indicator (T.symm.measurable (hA n))).symm
      _ = ∫ q, (A n).indicator (fun q => h q.out) (T.symm q) ∂ν := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
          simp only [Set.indicator, Set.mem_preimage, hhS]
      _ = ∫ q, (A n).indicator (fun q => h q.out) q ∂(ν.map T.symm) := (integral_map_equiv T.symm _).symm
      _ = ((D : ℝ) : ℂ) * ∫ q in A n, h q.out ∂ν := by
          rw [hmap, integral_smul_measure, integral_indicator (hA n), ENNReal.coe_toReal, Complex.real_smul]
  have hI : ∀ n : ℤ, I n = ((D : ℝ) : ℂ) ^ n * I 0 := by
    intro n
    induction n using Int.induction_on with
    | zero => simp
    | succ k ih =>
        rw [hstep, ih, ← mul_assoc, zpow_add_one₀ hDC, mul_comm (((D : ℝ) : ℂ) ^ (k : ℤ))]
    | pred k ih =>
        have h1 : I (-(k : ℤ)) = ((D : ℝ) : ℂ) * I (-(k : ℤ) - 1) := by
          rw [← hstep]; congr 1; ring
        have h2 : I (-(k : ℤ) - 1) = ((D : ℝ) : ℂ)⁻¹ * I (-(k : ℤ)) := by
          rw [h1, ← mul_assoc, inv_mul_cancel₀ hDC, one_mul]
        rw [h2, ih, ← mul_assoc, zpow_sub_one₀ hDC, mul_comm _⁻¹]

  have hlevel : ∀ n, ∫ q in A n, h q.out * Φ (m q.out) ∂ν = I n * Φ n := by
    intro n
    simp only [hI_def]
    rw [← integral_mul_const]
    refine setIntegral_congr_fun (hA n) fun q hq => ?_
    simp only [hA_def, Set.mem_ofPred_eq] at hq
    simp only [hq]
  have hsplit : ∫ q, h q.out * Φ (m q.out) ∂ν = ∑' n, I n * Φ n := by
    rw [← setIntegral_univ, ← hunion, integral_iUnion hA hdisj hfi.integrableOn]
    exact tsum_congr hlevel
  rw [hsplit, ← tsum_mul_right]
  refine tsum_congr fun n => ?_
  rw [hI n]
  simp only [hI_def, hA_def]
  ring
