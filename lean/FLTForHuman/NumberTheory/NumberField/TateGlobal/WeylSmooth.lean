/-
  The smooth local intertwining integral: the headline
  `AutomorphicForm.LocalIntertwining.integral_smoothWeylIntegrand_adicCompletion` together with
  its private development.

  Ported from the pin's `SmoothShell_Main` section of
  `S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.lean`
  lines 1420–2015 (`SetBridges`, `Substitution`, `Regularity`, `Tail`, `Main`); the headline's
  binders are the `Theorems/` wrapper
  `Thm_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.lean`
  verbatim (the checker diffs that text, not the `S_` file's section-variable form).

  The residual prelude this consumes is homed in `TateGlobal/WeylShell.lean` (shared with the
  unramified twin of set LI-1); the rest of the prelude is in `TateGlobal/WeylPrelude.lean` and
  the T1 `TateGlobal` modules. The pin's implementation lemma `integral_smoothWeylIntegrand_impl`
  is `private` and nothing of the development is part of the pin's surface, so every helper here
  stays `private`; the only other public declaration is the prerequisite `higherUnitsAt` below.

  One prerequisite is transcribed here rather than imported: `higherUnitsAt`, the character
  depth condition of the headline's hypothesis, is a pin `Definitions/` declaration
  (`Def_LanglandsTunnell_TateLocalConstantsAt.lean`) with no port home yet — the headline cannot
  even be stated without it. Its natural home is a `LanglandsTunnell/TateLocalConstantsAt.lean`
  module; a later refactor round should move it there.

  Pin `anthropics/fermats-last-theorem@aa2d8b3`, mathlib `v4.34.0`. Names are the pin's
  (prefix-stripped) except the recorded `ValuationOrd.ord` → `IsDiscreteValuationRing.ord`
  rename.
-/
import FLTForHuman.NumberTheory.NumberField.TateGlobal.WeylShell

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing Set
open Filter Topology
open scoped NNReal ENNReal Pointwise
open WithZero Multiplicative
open LanglandsTunnell.TateLocal

noncomputable section

namespace LanglandsTunnell

namespace TateLocal

/-
`K` and `v` are section variables in the pin, so the checker's signature text is `(n : ℕ)`;
keep that form (the elaborated signature is the same either way).
-/
variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

-- pin: higherUnitsAt (Def_LanglandsTunnell_TateLocalConstantsAt.lean:14)
def higherUnitsAt (n : ℕ) : Set (v.adicCompletion K)ˣ :=
  {u | Valued.v (u : v.adicCompletion K) = 1 ∧
    (n = 0 ∨ Valued.v ((u : v.adicCompletion K) - 1) ≤ WithZero.exp (-(n : ℤ)))}

end TateLocal

end LanglandsTunnell

namespace NumberField

namespace TateGlobal

namespace WeylSmooth

open WeylPrelude WeylShell LocalZetaUnramified MulHaarFromAdditive ValuedOrdBridge

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

section SetBridges

variable {π : v.adicCompletionIntegers F}

-- pin: zero_notMem_genShell (S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.lean:1440)
private theorem zero_notMem_genShell (hπ : Irreducible π) (k : ℤ) :
    (0 : v.adicCompletion F) ∉ genShell hπ k := by
  rintro ⟨y, hy, h0⟩
  have h0' : ((piUnit hπ ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F) * y = 0 := h0
  have hy0 : y = 0 := by
    rcases mul_eq_zero.mp h0' with h | h
    · exact absurd h (Units.ne_zero _)
    · exact h
  exact zero_notMem_shellSet hπ 0 (hy0 ▸ hy)

-- pin: genShell_subset_compl_zero (S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.lean:1450)
private theorem genShell_subset_compl_zero (hπ : Irreducible π) (k : ℤ) :
    genShell hπ k ⊆ {(0 : v.adicCompletion F)}ᶜ := by
  intro x hx h0
  rw [Set.mem_singleton_iff] at h0
  exact zero_notMem_genShell hπ k (h0 ▸ hx)

-- pin: setOf_valued_eq_genShell (S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.lean:1456)
private theorem setOf_valued_eq_genShell (hπ : Irreducible π) (k : ℤ) :
    {x : v.adicCompletion F | Valued.v x = (Multiplicative.ofAdd k : Multiplicative ℤ)}
      = genShell hπ (-k) := by
  ext x
  simp only [Set.mem_ofPred_eq]
  by_cases hx : x = 0
  · subst hx
    rw [map_zero]
    constructor
    · intro h
      exact absurd h.symm WithZero.coe_ne_zero
    · intro h
      exact absurd h (zero_notMem_genShell hπ (-k))
  · rw [mem_genShell_iff hπ hx]
    have hv : Valued.v x = WithZero.exp
        (-(IsDiscreteValuationRing.ord (v.adicCompletionIntegers F)
          (Additive.ofMul (Units.mk0 x hx)))) :=
      valued_coe_units_eq_exp_neg_ord (Units.mk0 x hx)
    rw [hv, show ((Multiplicative.ofAdd k : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
        = WithZero.exp k from rfl, WithZero.exp_inj]
    omega

-- pin: setOf_valued_eq_one_eq_genShell (S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.lean:1477)
private theorem setOf_valued_eq_one_eq_genShell (hπ : Irreducible π) :
    {u : v.adicCompletion F | Valued.v u = 1} = genShell hπ 0 := by
  have h := setOf_valued_eq_genShell (F := F) (v := v) hπ 0
  rw [neg_zero] at h
  rw [← h]
  ext u
  simp only [Set.mem_ofPred_eq, ofAdd_zero, WithZero.coe_one]

-- pin: genShell_zero_eq (S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.lean:1485)
private theorem genShell_zero_eq (hπ : Irreducible π) : genShell hπ 0 = shellSet hπ 0 := by
  rw [genShell, zpow_zero, Units.val_one, one_smul]

-- pin: smul_shellSet_zero_of_ord_eq_zero (S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.lean:1488)
private theorem smul_shellSet_zero_of_ord_eq_zero (hπ : Irreducible π) (w : (v.adicCompletion F)ˣ)
    (hw : IsDiscreteValuationRing.ord (v.adicCompletionIntegers F) (Additive.ofMul w) = 0) :
    (w : v.adicCompletion F) • shellSet hπ 0 = shellSet hπ 0 := by
  have key : ∀ w : (v.adicCompletion F)ˣ,
      IsDiscreteValuationRing.ord (v.adicCompletionIntegers F) (Additive.ofMul w) = 0 →
        (w : v.adicCompletion F) • shellSet hπ 0 ⊆ shellSet hπ 0 := by
    intro w hw x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hy0 : y ≠ 0 := fun h => zero_notMem_shellSet hπ 0 (h ▸ hy)
    have hx0 : (w : v.adicCompletion F) • y ≠ 0 := by
      rw [smul_eq_mul]
      exact mul_ne_zero (Units.ne_zero _) hy0
    refine (mem_shellSet_iff_ord_eq hπ 0 hx0).mpr ?_
    have hmk : Units.mk0 ((w : v.adicCompletion F) • y) hx0 = w * Units.mk0 y hy0 :=
      Units.ext (by simp [smul_eq_mul])
    rw [hmk, ord_ofMul_mul, hw, (mem_shellSet_iff_ord_eq hπ 0 hy0).mp hy]
    simp
  refine Set.Subset.antisymm (key w hw) ?_
  intro x hx
  have hw' : IsDiscreteValuationRing.ord (v.adicCompletionIntegers F) (Additive.ofMul w⁻¹) = 0 := by
    have h := ord_ofMul_mul w w⁻¹
    rw [mul_inv_cancel, hw, zero_add] at h
    rw [← h]
    exact map_zero _
  refine ⟨((w⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) • x, key w⁻¹ hw' ⟨x, hx, rfl⟩, ?_⟩
  show (w : v.adicCompletion F) • (((w⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) • x) = x
  rw [smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]

-- pin: genShell_neg_eq_smul (S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.lean:1516)
private theorem genShell_neg_eq_smul (hπ : Irreducible π) (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) (n : ℕ) :
    genShell hπ (-(n : ℤ)) = ((ϖ⁻¹ ^ n : (v.adicCompletion F)ˣ) : v.adicCompletion F) • genShell hπ 0 := by
  rw [genShell_zero_eq]
  set w : (v.adicCompletion F)ˣ := (ϖ⁻¹ ^ n)⁻¹ * piUnit hπ ^ (-(n : ℤ)) with hw_def
  have hordϖ : IsDiscreteValuationRing.ord (v.adicCompletionIntegers F) (Additive.ofMul ϖ) = 1 :=
    ord_eq_one_of_valued ϖ hϖ
  have hw : IsDiscreteValuationRing.ord (v.adicCompletionIntegers F) (Additive.ofMul w) = 0 := by
    rw [hw_def, ord_ofMul_mul, ord_ofMul_zpow_piUnit hπ, inv_pow, inv_inv]
    have h1 : Additive.ofMul (ϖ ^ n) = n • Additive.ofMul ϖ := rfl
    rw [h1, map_nsmul, hordϖ]
    simp
  have hfac : (piUnit hπ ^ (-(n : ℤ)) : (v.adicCompletion F)ˣ) = (ϖ⁻¹ ^ n) * w := by
    rw [hw_def, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [genShell, hfac, Units.val_mul, mul_smul, smul_shellSet_zero_of_ord_eq_zero hπ w hw]

-- pin: isCompact_shellSet_zero (S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.lean:1532)
private theorem isCompact_shellSet_zero (hπ : Irreducible π) : IsCompact (shellSet hπ 0) := by
  unfold shellSet
  exact IsCompact.diff (isCompact_smul_integers _)
    ((NumberField.isOpenAdicCompletionIntegers F v).smul₀ (Units.ne_zero _))

-- pin: isCompact_genShell (S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.lean:1537)
private theorem isCompact_genShell (hπ : Irreducible π) (k : ℤ) : IsCompact (genShell hπ k) := by
  unfold genShell
  exact IsCompact.smul _ (isCompact_shellSet_zero hπ)

-- pin: ord_inv_pow (S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.lean:1541)
private theorem ord_inv_pow (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) (n : ℕ) :
    IsDiscreteValuationRing.ord (v.adicCompletionIntegers F) (Additive.ofMul (ϖ⁻¹ ^ n)) = -(n : ℤ) := by
  rw [inv_pow]
  have h1 : Additive.ofMul ((ϖ ^ n)⁻¹) = -(n • Additive.ofMul ϖ) := rfl
  rw [h1, map_neg, map_nsmul, ord_eq_one_of_valued ϖ hϖ]
  simp

-- pin: distribHaarChar_inv_pow (S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.lean:1549)
private theorem distribHaarChar_inv_pow (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) (n : ℕ) :
    distribHaarChar (v.adicCompletion F) (ϖ⁻¹ ^ n) = normQ v ^ n := by
  rw [LocalHaarModulus.distribHaarChar_adicCompletion, ord_inv_pow ϖ hϖ n, neg_neg, zpow_natCast]

-- pin: modulus_inv_pow_mul (S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.lean:1554)
private theorem modulus_inv_pow_mul (hπ : Irreducible π) (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) (n : ℕ)
    {u : v.adicCompletion F} (hu : u ∈ genShell hπ 0) :
    modulus (((ϖ⁻¹ ^ n : (v.adicCompletion F)ˣ) : v.adicCompletion F) * u) = normQ v ^ n := by
  have hu0 : u ≠ 0 := fun h => zero_notMem_genShell hπ 0 (h ▸ hu)
  have hx0 : ((ϖ⁻¹ ^ n : (v.adicCompletion F)ˣ) : v.adicCompletion F) * u ≠ 0 :=
    mul_ne_zero (Units.ne_zero _) hu0
  rw [modulus_of_ne_zero_adicCompletion hx0]
  have hmk : Units.mk0 _ hx0 = ϖ⁻¹ ^ n * Units.mk0 u hu0 := Units.ext (by simp)
  have hordu : IsDiscreteValuationRing.ord (v.adicCompletionIntegers F)
      (Additive.ofMul (Units.mk0 u hu0)) = 0 :=
    (mem_genShell_iff hπ hu0).mp hu
  rw [hmk, ord_ofMul_mul, hordu, add_zero, ord_inv_pow ϖ hϖ n, neg_neg, zpow_natCast]

-- pin: modulus_of_mem_genShell (S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.lean:1567)
private theorem modulus_of_mem_genShell (hπ : Irreducible π) {k : ℤ} {x : v.adicCompletion F}
    (hx : x ∈ genShell hπ k) : modulus x = normQ v ^ (-k) := by
  have hx0 : x ≠ 0 := fun h => zero_notMem_genShell hπ k (h ▸ hx)
  rw [modulus_of_ne_zero_adicCompletion hx0, (mem_genShell_iff hπ hx0).mp hx]

end SetBridges

section Substitution

variable [MeasurableSpace (v.adicCompletion F)]
variable [BorelSpace (v.adicCompletion F)]
variable (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure] [μ.Regular]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option linter.overlappingInstances false in
-- pin: setIntegral_units_smul (S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.lean:1581)
private theorem setIntegral_units_smul (u : (v.adicCompletion F)ˣ) {S : Set (v.adicCompletion F)}
    (hS : MeasurableSet S) (f : v.adicCompletion F → E) :
    ∫ x in (u : v.adicCompletion F) • S, f x ∂μ
      = ((distribHaarChar (v.adicCompletion F) u : ℝ≥0) : ℝ)
          • ∫ y in S, f ((u : v.adicCompletion F) * y) ∂μ := by
  set T : v.adicCompletion F ≃ᵐ v.adicCompletion F :=
    MeasurableEquiv.mulLeft₀ (u : v.adicCompletion F) u.ne_zero with hT
  have hTapply : (T : v.adicCompletion F → v.adicCompletion F) = fun y => (u : v.adicCompletion F) * y := rfl
  set Δ : ℝ≥0 := distribHaarChar (v.adicCompletion F) u with hΔ
  have hΔ0 : Δ ≠ 0 := (distribHaarChar_pos).ne'
  have hΔinv : distribHaarChar (v.adicCompletion F) u⁻¹ = Δ⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [hΔ, ← map_mul, inv_mul_cancel, map_one]
  have hpre : ∀ A : Set (v.adicCompletion F),
      T ⁻¹' A = ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) • A := by
    intro A
    ext y
    simp only [Set.mem_preimage, hTapply]
    constructor
    · intro hy
      exact ⟨(u : v.adicCompletion F) * y, hy, by simp [smul_eq_mul]⟩
    · rintro ⟨z, hz, rfl⟩
      simpa [smul_eq_mul] using hz
  have hmap : Measure.map T μ = ((Δ : ℝ≥0∞))⁻¹ • μ := by
    refine Measure.ext fun A hA => ?_
    rw [Measure.map_apply T.measurable hA, Measure.smul_apply, smul_eq_mul, hpre A,
      measure_units_smul μ u⁻¹ A, hΔinv, ENNReal.coe_inv hΔ0]
  have hmeas : MeasurableSet ((u : v.adicCompletion F) • S) := measurableSet_smul_set u.ne_zero hS
  have hpreS : T ⁻¹' ((u : v.adicCompletion F) • S) = S := by
    rw [hpre, smul_smul, Units.inv_mul, one_smul]
  have hind : ∀ y, S.indicator (fun y => f ((u : v.adicCompletion F) * y)) y
      = ((u : v.adicCompletion F) • S).indicator f (T y) := by
    intro y
    have hmemiff : y ∈ S ↔ T y ∈ (u : v.adicCompletion F) • S := by
      rw [← Set.mem_preimage, hpreS]
    by_cases hy : y ∈ S
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (hmemiff.mp hy), hTapply]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (fun h => hy (hmemiff.mpr h))]
  have key : ∫ y in S, f ((u : v.adicCompletion F) * y) ∂μ
      = (((Δ : ℝ≥0∞))⁻¹).toReal • ∫ x in (u : v.adicCompletion F) • S, f x ∂μ := by
    rw [← integral_indicator hS, ← integral_indicator hmeas, ← integral_smul_measure, ← hmap,
      integral_map_equiv]
    exact integral_congr_ae (Eventually.of_forall hind)
  rw [key, ENNReal.toReal_inv, ENNReal.coe_toReal, smul_smul,
    mul_inv_cancel₀ (NNReal.coe_ne_zero.mpr hΔ0), one_smul]

end Substitution

section Regularity

-- pin: setOf_valued_sub_le_mem_nhds (S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.lean:1632)
private theorem setOf_valued_sub_le_mem_nhds (x z : v.adicCompletion F) (hz : Valued.v z ≠ 0) :
    {y : v.adicCompletion F | Valued.v (y - x) ≤ Valued.v z} ∈ 𝓝 x := by
  have hr : Valued.v.restrict z ≠ 0 := by
    rwa [Ne, Valuation.restrict_eq_zero_iff]
  have hopen : IsOpen {w : v.adicCompletion F | Valued.v.restrict w ≤ Valued.v.restrict z} :=
    Valued.isOpen_closedBall (R := v.adicCompletion F) hr
  have hopen' : IsOpen {y : v.adicCompletion F | Valued.v.restrict (y - x) ≤ Valued.v.restrict z} :=
    hopen.preimage (continuous_id.sub continuous_const)
  have hx : x ∈ {y : v.adicCompletion F | Valued.v.restrict (y - x) ≤ Valued.v.restrict z} := by
    simp
  refine Filter.mem_of_superset (hopen'.mem_nhds hx) fun y hy => ?_
  rw [Set.mem_ofPred_eq, Valuation.restrict_le_iff] at hy
  exact hy

-- pin: setOf_valued_sub_lt_mem_nhds (S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.lean:1646)
private theorem setOf_valued_sub_lt_mem_nhds (x z : v.adicCompletion F) (hz : Valued.v z ≠ 0) :
    {y : v.adicCompletion F | Valued.v (y - x) < Valued.v z} ∈ 𝓝 x := by
  have hr : Valued.v.restrict z ≠ 0 := by
    rwa [Ne, Valuation.restrict_eq_zero_iff]
  have hopen : IsOpen {w : v.adicCompletion F | Valued.v.restrict w < Valued.v.restrict z} :=
    Valued.isOpen_ball (R := v.adicCompletion F) _
  have hopen' : IsOpen {y : v.adicCompletion F | Valued.v.restrict (y - x) < Valued.v.restrict z} :=
    hopen.preimage (continuous_id.sub continuous_const)
  have hx : x ∈ {y : v.adicCompletion F | Valued.v.restrict (y - x) < Valued.v.restrict z} := by
    simp only [Set.mem_ofPred_eq, sub_self, map_zero]
    exact pos_iff_ne_zero.mpr hr
  refine Filter.mem_of_superset (hopen'.mem_nhds hx) fun y hy => ?_
  rw [Set.mem_ofPred_eq, Valuation.restrict_lt_iff] at hy
  exact hy

-- pin: continuous_of_depth (S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.lean:1661)
/-
The port's `exists_irreducible_valued` states its value as `WithZero.exp (-1 : ℤ)` rather than
the pin's `Multiplicative.ofAdd (-1 : ℤ)`; the two are definitionally equal, so the pin's proof
transcribes unchanged.
-/
private theorem continuous_of_depth (m : ℕ) (B : v.adicCompletion F → ℂ)
    (hB : ∀ x y : v.adicCompletion F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x) :
    Continuous B := by
  obtain ⟨π, -, hπv⟩ := exists_irreducible_valued (v := v)
  have hz : Valued.v (((π : v.adicCompletionIntegers F) : v.adicCompletion F) ^ m)
      = (Multiplicative.ofAdd (-(m : ℤ)) : Multiplicative ℤ) := by
    rw [map_pow, hπv, ← WithZero.exp_nsmul]
    simp [WithZero.exp]
  have hz0 : Valued.v (((π : v.adicCompletionIntegers F) : v.adicCompletion F) ^ m) ≠ 0 := by
    rw [hz]
    exact WithZero.coe_ne_zero
  refine continuous_iff_continuousAt.mpr fun x => ?_
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [setOf_valued_sub_le_mem_nhds x _ hz0] with y hy
  rw [hz] at hy
  exact (hB x y hy).symm

-- pin: apply_inv_eq_apply_zero_of_depth (S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.lean:1679)
private theorem apply_inv_eq_apply_zero_of_depth (m : ℕ) (B : v.adicCompletion F → ℂ)
    (hB : ∀ x y : v.adicCompletion F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x)
    {n : ℕ} (hmn : m ≤ n) {x : v.adicCompletion F}
    (hx : Valued.v x = (Multiplicative.ofAdd (n : ℤ) : Multiplicative ℤ)) :
    B x⁻¹ = B 0 := by
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, map_zero] at hx
    exact WithZero.coe_ne_zero hx.symm
  refine hB 0 x⁻¹ ?_
  rw [sub_zero, map_inv₀, hx,
    show ((Multiplicative.ofAdd (n : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
      = WithZero.exp (n : ℤ) from rfl, ← WithZero.exp_neg,
    show ((Multiplicative.ofAdd (-(m : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
      = WithZero.exp (-(m : ℤ)) from rfl, WithZero.exp_le_exp]
  omega

-- pin: continuousOn_charExt_inv (S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.lean:1697)
private theorem continuousOn_charExt_inv (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∃ c : ℕ, ∀ u ∈ higherUnitsAt F v c, χ u = 1) :
    ContinuousOn (charExt χ⁻¹) {(0 : v.adicCompletion F)}ᶜ := by
  obtain ⟨c, hc⟩ := hχ
  intro x hx
  rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
  have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  apply ContinuousAt.continuousWithinAt
  obtain ⟨π, -, hπv⟩ := exists_irreducible_valued (v := v)
  have hzv : Valued.v (x * (((π : v.adicCompletionIntegers F) : v.adicCompletion F) ^ c))
      = Valued.v x * WithZero.exp (-(c : ℤ)) := by
    rw [map_mul, map_pow, hπv, ← WithZero.exp_nsmul]
    simp
  have hz0 : Valued.v (x * (((π : v.adicCompletionIntegers F) : v.adicCompletion F) ^ c)) ≠ 0 := by
    rw [hzv]
    exact mul_ne_zero hvx WithZero.coe_ne_zero
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [setOf_valued_sub_lt_mem_nhds x _ hz0] with y hy
  rw [hzv] at hy
  have hyle := hy.le
  have hle1 : WithZero.exp (-(c : ℤ)) ≤ 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have hlt : Valued.v (y - x) < Valued.v x :=
    lt_of_lt_of_le hy (mul_le_of_le_one_right' hle1)
  have hvy : Valued.v y = Valued.v x := Valuation.map_eq_of_sub_lt _ hlt
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, map_zero] at hvy
    exact hvx hvy.symm
  set u : (v.adicCompletion F)ˣ := (Units.mk0 x hx)⁻¹ * Units.mk0 y hy0 with hu
  have huval : (u : v.adicCompletion F) = x⁻¹ * y := by simp [hu]
  have hu1 : Valued.v (u : v.adicCompletion F) = 1 := by
    rw [huval, map_mul, map_inv₀, hvy, inv_mul_cancel₀ hvx]
  have hu2 : Valued.v ((u : v.adicCompletion F) - 1) ≤ WithZero.exp (-(c : ℤ)) := by
    have h1 : (u : v.adicCompletion F) - 1 = x⁻¹ * (y - x) := by
      rw [huval, mul_sub, inv_mul_cancel₀ hx]
    rw [h1, map_mul, map_inv₀]
    calc (Valued.v x)⁻¹ * Valued.v (y - x)
        ≤ (Valued.v x)⁻¹ * (Valued.v x * WithZero.exp (-(c : ℤ))) := by gcongr
      _ = WithZero.exp (-(c : ℤ)) := by rw [← mul_assoc, inv_mul_cancel₀ hvx, one_mul]
  have hmem : u ∈ higherUnitsAt F v c := ⟨hu1, Or.inr hu2⟩
  have hχu : χ u = 1 := hc u hmem
  have hy' : Units.mk0 y hy0 = Units.mk0 x hx * u := by
    rw [hu, ← mul_assoc, mul_inv_cancel, one_mul]
  show charExt χ⁻¹ x = charExt χ⁻¹ y
  rw [charExt_of_ne_zero _ hx, charExt_of_ne_zero _ hy0, hy', map_mul]
  simp [hχu]

variable [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
variable (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure] [μ.Regular]
variable {π : v.adicCompletionIntegers F}

omit [μ.Regular] in
-- pin: integrableOn_genShell (S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.lean:1752)
private theorem integrableOn_genShell (hπ : Irreducible π) (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∃ c : ℕ, ∀ u ∈ higherUnitsAt F v c, χ u = 1) (w : ℂ) (m : ℕ)
    (B : v.adicCompletion F → ℂ)
    (hB : ∀ x y : v.adicCompletion F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x) (k : ℤ) :
    IntegrableOn (fun x => charExt χ⁻¹ x * (((modulus x : ℝ)) : ℂ) ^ w * B x⁻¹) (genShell hπ k) μ := by
  have hcont : ContinuousOn (fun x => charExt χ⁻¹ x * (((modulus x : ℝ)) : ℂ) ^ w * B x⁻¹)
      (genShell hπ k) := by
    have h0 := genShell_subset_compl_zero hπ k
    have hc : ContinuousOn (fun x : v.adicCompletion F => ((((normQ v ^ (-k) : ℝ≥0) : ℝ)) : ℂ) ^ w)
        (genShell hπ k) := continuousOn_const
    have hmod : ContinuousOn (fun x : v.adicCompletion F => (((modulus x : ℝ)) : ℂ) ^ w) (genShell hπ k) :=
      hc.congr (fun x hx => by simp only [modulus_of_mem_genShell hπ hx])
    have hB' : ContinuousOn (fun x : v.adicCompletion F => B x⁻¹) (genShell hπ k) :=
      (continuous_of_depth m B hB).comp_continuousOn (continuousOn_inv₀.mono h0)
    exact (((continuousOn_charExt_inv χ hχ).mono h0).mul hmod).mul hB'
  exact hcont.integrableOn_compact (isCompact_genShell hπ k)

end Regularity

section Tail

-- pin: ofReal_pow_cpow (S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.lean:700)
/-
A file-local copy of the pin's 8-line version. `TateGlobal/WeylShell.lean` re-proves the same
identity `private`, and a `private` declaration is not importable, so it is re-derived here
rather than widening the frozen module (FR-0015/FR-0017).
-/
private theorem ofReal_pow_cpow {a : ℝ} (ha : 0 ≤ a) (s : ℂ) (k : ℕ) :
    (((a ^ k : ℝ)) : ℂ) ^ s = (((a : ℝ) : ℂ) ^ s) ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (pow_nonneg ha n) ha, ih,
        pow_succ]

variable [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
variable (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure] [μ.Regular]
variable {π : v.adicCompletionIntegers F}

omit [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)] in
-- pin: normQ_pos (S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.lean:1780)
private theorem normQ_pos : (0 : ℝ) < ((normQ v : ℝ≥0) : ℝ) := by
  exact_mod_cast lt_of_lt_of_le one_pos (one_le_normQ (v := v))

omit [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)] in
-- pin: integrand_inv_pow_mul (S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.lean:1785)
private theorem integrand_inv_pow_mul (hπ : Irreducible π) (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ) (w : ℂ) (m : ℕ) (B : v.adicCompletion F → ℂ)
    (hB : ∀ x y : v.adicCompletion F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x)
    {n : ℕ} (hmn : m ≤ n) {u : v.adicCompletion F} (hu : u ∈ genShell hπ 0) :
    charExt χ⁻¹ (((ϖ⁻¹ ^ n : (v.adicCompletion F)ˣ) : v.adicCompletion F) * u)
        * (((modulus (((ϖ⁻¹ ^ n : (v.adicCompletion F)ˣ) : v.adicCompletion F) * u) : ℝ)) : ℂ) ^ w
        * B (((ϖ⁻¹ ^ n : (v.adicCompletion F)ˣ) : v.adicCompletion F) * u)⁻¹
      = (((χ ϖ : ℂˣ) : ℂ) ^ n * ((((normQ v : ℝ≥0) : ℝ) : ℂ) ^ w) ^ n * B 0) * charExt χ⁻¹ u := by
  set c : (v.adicCompletion F)ˣ := ϖ⁻¹ ^ n with hc
  have hu0 : u ≠ 0 := fun h => zero_notMem_genShell hπ 0 (h ▸ hu)
  have hx0 : (c : v.adicCompletion F) * u ≠ 0 := mul_ne_zero (Units.ne_zero _) hu0

  have hchar : charExt χ⁻¹ ((c : v.adicCompletion F) * u) = ((χ ϖ : ℂˣ) : ℂ) ^ n * charExt χ⁻¹ u := by
    have hmk : Units.mk0 _ hx0 = c * Units.mk0 u hu0 := Units.ext (by simp)
    rw [charExt_of_ne_zero _ hx0, charExt_of_ne_zero _ hu0, hmk, map_mul, hc]
    simp [map_pow]

  have hmod : (((modulus ((c : v.adicCompletion F) * u) : ℝ)) : ℂ) ^ w
      = ((((normQ v : ℝ≥0) : ℝ) : ℂ) ^ w) ^ n := by
    rw [hc, modulus_inv_pow_mul hπ ϖ hϖ n hu, NNReal.coe_pow,
      ofReal_pow_cpow (normQ_pos (v := v)).le]

  have hval : Valued.v ((c : v.adicCompletion F) * u) = (Multiplicative.ofAdd (n : ℤ) : Multiplicative ℤ) := by
    have hmem : (c : v.adicCompletion F) * u
        ∈ {x : v.adicCompletion F | Valued.v x = (Multiplicative.ofAdd (n : ℤ) : Multiplicative ℤ)} := by
      rw [setOf_valued_eq_genShell hπ (n : ℤ), genShell_neg_eq_smul hπ ϖ hϖ n, ← hc]
      exact Set.smul_mem_smul_set hu
    exact hmem
  have hBval : B ((c : v.adicCompletion F) * u)⁻¹ = B 0 := apply_inv_eq_apply_zero_of_depth m B hB hmn hval
  rw [hchar, hmod, hBval]
  ring

set_option linter.overlappingInstances false in
-- pin: setIntegral_tailShell (S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.lean:1818)
private theorem setIntegral_tailShell (hπ : Irreducible π) (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ) (s : ℂ) (m : ℕ) (B : v.adicCompletion F → ℂ)
    (hB : ∀ x y : v.adicCompletion F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x)
    {n : ℕ} (hmn : m ≤ n) :
    ∫ x in genShell hπ (-(n : ℤ)), charExt χ⁻¹ x * (((modulus x : ℝ)) : ℂ) ^ (-(2 * s + 1)) * B x⁻¹ ∂μ
      = B 0 * (∫ u in genShell hπ 0, charExt χ⁻¹ u ∂μ)
          * ((((χ ϖ : ℂˣ) : ℂ) * ((((normQ v : ℝ≥0) : ℝ) : ℂ)) ^ (-(2 * s))) ^ n) := by
  have hN0 : ((((normQ v : ℝ≥0) : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast (normQ_pos (v := v)).ne'
  rw [genShell_neg_eq_smul hπ ϖ hϖ n, setIntegral_units_smul μ (ϖ⁻¹ ^ n) (measurableSet_genShell hπ 0),
    distribHaarChar_inv_pow ϖ hϖ n, Complex.real_smul,
    setIntegral_congr_fun (measurableSet_genShell hπ 0)
      (fun u hu => integrand_inv_pow_mul hπ ϖ hϖ χ (-(2 * s + 1)) m B hB hmn hu),
    integral_const_mul]
  have hpow : ((((normQ v : ℝ≥0) : ℝ) : ℂ)) ^ (-(2 * s + 1))
      = ((((normQ v : ℝ≥0) : ℝ) : ℂ)) ^ (-(2 * s)) * ((((normQ v : ℝ≥0) : ℝ) : ℂ))⁻¹ := by
    rw [show (-(2 * s + 1) : ℂ) = -(2 * s) + (-1) by ring, Complex.cpow_add _ _ hN0, Complex.cpow_neg_one]
  rw [hpow, NNReal.coe_pow, Complex.ofReal_pow, mul_pow]
  have hw : ((((normQ v : ℝ≥0) : ℝ) : ℂ)) ^ n * (((((normQ v : ℝ≥0) : ℝ) : ℂ))⁻¹) ^ n = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hN0, one_pow]
  linear_combination (((χ ϖ : ℂˣ) : ℂ) ^ n * ((((normQ v : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * s))) ^ n * B 0
    * ∫ u in genShell hπ 0, charExt χ⁻¹ u ∂μ) * hw

set_option linter.overlappingInstances false in
-- pin: setIntegral_norm_tailShell (S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.lean:1841)
private theorem setIntegral_norm_tailShell (hπ : Irreducible π) (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ) (s : ℂ) (m : ℕ) (B : v.adicCompletion F → ℂ)
    (hB : ∀ x y : v.adicCompletion F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x)
    {n : ℕ} (hmn : m ≤ n) :
    ∫ x in genShell hπ (-(n : ℤ)), ‖charExt χ⁻¹ x * (((modulus x : ℝ)) : ℂ) ^ (-(2 * s + 1)) * B x⁻¹‖ ∂μ
      = ‖B 0‖ * (∫ u in genShell hπ 0, ‖charExt χ⁻¹ u‖ ∂μ)
          * ‖((χ ϖ : ℂˣ) : ℂ) * ((((normQ v : ℝ≥0) : ℝ) : ℂ)) ^ (-(2 * s))‖ ^ n := by
  have hN0 : ((((normQ v : ℝ≥0) : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast (normQ_pos (v := v)).ne'
  have hNpos : (0 : ℝ) < ((normQ v : ℝ≥0) : ℝ) := normQ_pos (v := v)
  rw [genShell_neg_eq_smul hπ ϖ hϖ n,
    setIntegral_units_smul μ (ϖ⁻¹ ^ n) (measurableSet_genShell hπ 0)
      (fun x => ‖charExt χ⁻¹ x * (((modulus x : ℝ)) : ℂ) ^ (-(2 * s + 1)) * B x⁻¹‖),
    distribHaarChar_inv_pow ϖ hϖ n, smul_eq_mul,
    setIntegral_congr_fun (measurableSet_genShell hπ 0)
      (fun u hu => by
        show ‖_‖ = ‖((χ ϖ : ℂˣ) : ℂ) ^ n * ((((normQ v : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * s + 1))) ^ n * B 0‖
            * ‖charExt χ⁻¹ u‖
        rw [integrand_inv_pow_mul hπ ϖ hϖ χ (-(2 * s + 1)) m B hB hmn hu, norm_mul]),
    integral_const_mul]

  have hpow : ((((normQ v : ℝ≥0) : ℝ) : ℂ)) ^ (-(2 * s + 1))
      = ((((normQ v : ℝ≥0) : ℝ) : ℂ)) ^ (-(2 * s)) * ((((normQ v : ℝ≥0) : ℝ) : ℂ))⁻¹ := by
    rw [show (-(2 * s + 1) : ℂ) = -(2 * s) + (-1) by ring, Complex.cpow_add _ _ hN0, Complex.cpow_neg_one]
  have hnormQ : ‖((((normQ v : ℝ≥0) : ℝ) : ℂ))‖ = (((normQ v : ℝ≥0) : ℝ)) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hNpos.le]
  rw [hpow, NNReal.coe_pow]
  simp only [norm_mul, norm_pow, mul_pow, norm_inv, hnormQ]
  have hw : (((normQ v : ℝ≥0) : ℝ)) ^ n * ((((normQ v : ℝ≥0) : ℝ))⁻¹) ^ n = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hNpos.ne', one_pow]
  linear_combination (‖((χ ϖ : ℂˣ) : ℂ)‖ ^ n * ‖((((normQ v : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * s)))‖ ^ n * ‖B 0‖
    * ∫ u in genShell hπ 0, ‖charExt χ⁻¹ u‖ ∂μ) * hw

omit [μ.IsAddHaarMeasure] [μ.Regular] in
-- pin: setIntegral_lowShell (S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.lean:1876)
private theorem setIntegral_lowShell (hπ : Irreducible π) (χ : (v.adicCompletion F)ˣ →* ℂˣ) (s : ℂ)
    (B : v.adicCompletion F → ℂ) (n : ℕ) :
    ∫ x in genShell hπ (-(n : ℤ)), charExt χ⁻¹ x * (((modulus x : ℝ)) : ℂ) ^ (-(2 * s + 1)) * B x⁻¹ ∂μ
      = (((((normQ v : ℝ≥0) : ℝ) : ℂ)) ^ (-(2 * s + 1))) ^ n
          * ∫ x in genShell hπ (-(n : ℤ)), charExt χ⁻¹ x * B x⁻¹ ∂μ := by
  rw [← integral_const_mul]
  refine setIntegral_congr_fun (measurableSet_genShell hπ _) fun x hx => ?_
  rw [modulus_of_mem_genShell hπ hx, neg_neg, zpow_natCast, NNReal.coe_pow,
    ofReal_pow_cpow (normQ_pos (v := v)).le]
  ring

end Tail

section Main

set_option linter.style.haveILetI false in
set_option linter.overlappingInstances false in
-- pin: integral_smoothWeylIntegrand_impl (S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.lean:1894)
private theorem integral_smoothWeylIntegrand_impl
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (ϖ : (v.adicCompletion F)ˣ) (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∃ c : ℕ, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v c, χ u = 1)
    (m : ℕ) (hm : 1 ≤ m)
    (A : v.adicCompletion F → ℂ)
    (hA : IntegrableOn A (v.adicCompletionIntegers F : Set (v.adicCompletion F)) μ)
    (B : v.adicCompletion F → ℂ)
    (hB : ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x)
    (s : ℂ) (hs : ‖((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1) :
    ∫ x, ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A x
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * B y⁻¹) x) ∂μ
      = (∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)), A x ∂μ)
        + (∑ n ∈ Finset.Ico 1 m,
            (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))) ^ n
              * ∫ x in {x : v.adicCompletion F | Valued.v x = Multiplicative.ofAdd (n : ℤ)},
                  LanglandsTunnell.TateLocal.charExt χ⁻¹ x * B x⁻¹ ∂μ)
        + B 0 * (∫ u in {u : v.adicCompletion F | Valued.v u = 1}, LanglandsTunnell.TateLocal.charExt χ⁻¹ u ∂μ)
            * (((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))) ^ m
            * (1 - ((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s)))⁻¹ := by
  classical
  haveI : μ.Regular := inferInstance
  obtain ⟨π, hπ, -⟩ := exists_irreducible_valued (v := v)
  obtain ⟨m', rfl⟩ : ∃ m' : ℕ, m = m' + 1 := ⟨m - 1, by omega⟩

  set O : Set (v.adicCompletion F) := (v.adicCompletionIntegers F : Set (v.adicCompletion F)) with hO
  set N : ℂ := ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) with hN
  set a : ℂ := ((χ ϖ : ℂˣ) : ℂ) * N ^ (-(2 * s)) with ha
  set g : v.adicCompletion F → ℂ :=
    fun y => charExt χ⁻¹ y * (((modulus y : ℝ)) : ℂ) ^ (-(2 * s + 1)) * B y⁻¹ with hg
  have hQN : ((((normQ v : ℝ≥0) : ℝ) : ℂ)) = N := by
    rw [hN, normQ]
    push_cast
    rfl
  have ha1 : ‖a‖ < 1 := hs
  have hns : ∀ k : ℕ, negShell hπ k = genShell hπ (-((k + 1 : ℕ) : ℤ)) := by
    intro k
    simp only [negShell, Nat.cast_add, Nat.cast_one]

  have hIntShell : ∀ k : ℕ, IntegrableOn g (negShell hπ k) μ := fun k =>
    integrableOn_genShell μ hπ χ hχ (-(2 * s + 1)) (m' + 1) B hB (-((k : ℤ) + 1))

  have htailval : ∀ k : ℕ, m' + 1 ≤ k + 1 → ∫ x in negShell hπ k, g x ∂μ
      = B 0 * (∫ u in genShell hπ 0, charExt χ⁻¹ u ∂μ) * a ^ (k + 1) := by
    intro k hk
    rw [hns k, hg, setIntegral_tailShell μ hπ ϖ hϖ χ s (m' + 1) B hB hk, hQN]
  set C : ℝ := ‖B 0‖ * ∫ u in genShell hπ 0, ‖charExt χ⁻¹ u‖ ∂μ with hC
  have hnorm : ∀ k : ℕ, m' + 1 ≤ k + 1 → ∫ x in negShell hπ k, ‖g x‖ ∂μ = C * ‖a‖ ^ (k + 1) := by
    intro k hk
    rw [hns k, hg, setIntegral_norm_tailShell μ hπ ϖ hϖ χ s (m' + 1) B hB hk, hQN]

  have hlowval : ∀ k : ℕ, ∫ x in negShell hπ k, g x ∂μ
      = (N ^ (-(2 * s + 1))) ^ (k + 1)
        * ∫ x in {x : v.adicCompletion F | Valued.v x = (Multiplicative.ofAdd (((k + 1 : ℕ)) : ℤ) : Multiplicative ℤ)},
            charExt χ⁻¹ x * B x⁻¹ ∂μ := by
    intro k
    rw [hns k, hg, setIntegral_lowShell μ hπ χ s B (k + 1), hQN, setOf_valued_eq_genShell hπ]

  have hsum : Summable fun k : ℕ => ∫ x in negShell hπ k, ‖g x‖ ∂μ := by
    refine (summable_nat_add_iff m').mp ?_
    have h : (fun k : ℕ => ∫ x in negShell hπ (k + m'), ‖g x‖ ∂μ)
        = fun k => (C * ‖a‖ ^ (m' + 1)) * ‖a‖ ^ k := by
      funext k
      rw [hnorm (k + m') (by omega), show k + m' + 1 = (m' + 1) + k by ring, pow_add]
      ring
    rw [h]
    exact (summable_geometric_of_lt_one (norm_nonneg _) ha1).mul_left _
  have hOc : Oᶜ = ⋃ k : ℕ, negShell hπ k := compl_integers_eq_iUnion_negShell hπ
  have hInt : IntegrableOn g Oᶜ μ := by
    rw [hOc]
    exact integrableOn_iUnion_of_summable_integral_norm hIntShell hsum
  have hHas : HasSum (fun k : ℕ => ∫ x in negShell hπ k, g x ∂μ) (∫ x in Oᶜ, g x ∂μ) := by
    rw [hOc] at hInt ⊢
    exact hasSum_integral_iUnion (fun k => measurableSet_negShell hπ k) (negShell_disjoint hπ) hInt

  have hsplit : ∫ x in Oᶜ, g x ∂μ
      = (∑ k ∈ Finset.range m', ∫ x in negShell hπ k, g x ∂μ)
        + ∑' j : ℕ, ∫ x in negShell hπ (j + m'), g x ∂μ := by
    rw [← hHas.tsum_eq, hHas.summable.sum_add_tsum_nat_add m']
  have htail : ∑' j : ℕ, ∫ x in negShell hπ (j + m'), g x ∂μ
      = B 0 * (∫ u in genShell hπ 0, charExt χ⁻¹ u ∂μ) * a ^ (m' + 1) * (1 - a)⁻¹ := by
    have h2 : HasSum (fun j : ℕ => B 0 * (∫ u in genShell hπ 0, charExt χ⁻¹ u ∂μ) * a ^ (m' + 1) * a ^ j)
        (B 0 * (∫ u in genShell hπ 0, charExt χ⁻¹ u ∂μ) * a ^ (m' + 1) * (1 - a)⁻¹) :=
      (hasSum_geometric_of_norm_lt_one ha1).mul_left _
    have h : (fun j : ℕ => ∫ x in negShell hπ (j + m'), g x ∂μ)
        = fun j => B 0 * (∫ u in genShell hπ 0, charExt χ⁻¹ u ∂μ) * a ^ (m' + 1) * a ^ j := by
      funext j
      rw [htailval (j + m') (by omega), show j + m' + 1 = (m' + 1) + j by ring, pow_add]
      ring
    rw [h]
    exact h2.tsum_eq
  have hlow : ∑ k ∈ Finset.range m', ∫ x in negShell hπ k, g x ∂μ
      = ∑ n ∈ Finset.Ico 1 (m' + 1), (N ^ (-(2 * s + 1))) ^ n
          * ∫ x in {x : v.adicCompletion F | Valued.v x = (Multiplicative.ofAdd (n : ℤ) : Multiplicative ℤ)},
              charExt χ⁻¹ x * B x⁻¹ ∂μ := by
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hlowval k, add_comm k 1]

  have hOmeas : MeasurableSet O := (isCompact_integers (F := F) (v := v)).isClosed.measurableSet
  have hint1 : Integrable (O.indicator A) μ := hA.integrable_indicator hOmeas
  have hint2 : Integrable (Oᶜ.indicator g) μ := hInt.integrable_indicator hOmeas.compl
  have hunit : {u : v.adicCompletion F | Valued.v u = 1} = genShell hπ 0 := setOf_valued_eq_one_eq_genShell hπ
  rw [integral_add hint1 hint2, integral_indicator hOmeas, integral_indicator hOmeas.compl, hsplit, hlow, htail,
    hunit]
  ring

end Main

-- pin: integral_smoothWeylIntegrand_adicCompletion (Thm_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.lean:10)
theorem integral_smoothWeylIntegrand_adicCompletion
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (ϖ : (v.adicCompletion F)ˣ) (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∃ c : ℕ, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v c, χ u = 1)
    (m : ℕ) (hm : 1 ≤ m)
    (A : v.adicCompletion F → ℂ)
    (hA : IntegrableOn A (v.adicCompletionIntegers F : Set (v.adicCompletion F)) μ)
    (B : v.adicCompletion F → ℂ)
    (hB : ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x)
    (s : ℂ) (hs : ‖((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1) :
    ∫ x, ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A x
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * B y⁻¹) x) ∂μ
      = (∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)), A x ∂μ)
        + (∑ n ∈ Finset.Ico 1 m,
            (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))) ^ n
              * ∫ x in {x : v.adicCompletion F | Valued.v x = Multiplicative.ofAdd (n : ℤ)},
                  LanglandsTunnell.TateLocal.charExt χ⁻¹ x * B x⁻¹ ∂μ)
        + B 0 * (∫ u in {u : v.adicCompletion F | Valued.v u = 1}, LanglandsTunnell.TateLocal.charExt χ⁻¹ u ∂μ)
            * (((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))) ^ m
            * (1 - ((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s)))⁻¹ :=
  integral_smoothWeylIntegrand_impl F v μ ϖ hϖ χ hχ m hm A hA B hB s hs

end WeylSmooth

end TateGlobal

end NumberField
