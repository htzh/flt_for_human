/-
  The local atom at one place: it and its shift are integrable.

  At a finite place `v` of a number field, the pin's *smooth atom* attached to two functions `A`, `B`
  that are locally constant at depth `m` is

    `a = A` on the completion's integers, and `modulus ^ (-(2s+1)) * B (·⁻¹)` off them,

  and the integrability statements of this module are that `a` is integrable and that its Weyl shift
  `modulus ^ (-(2s+1)) * a (·⁻¹)` is too (`integrable_smoothAtom_and_integrable_weylShift_adicCompletion`),
  for `re s > 0`.

  At the archimedean places the same pair of statements holds for the pin's real and complex atoms

    `atom σ x = ((x - I) / sqrt (1 + x^2)) ^ k * (1 + x^2) ^ (-(σ + 1/2))`  (real place),
    `atom σ z = z ^ a₀ * conj z ^ b₀ * (1 + ‖z‖ ^ 2) ^ (-(2σ+1) - m/2)`     (complex place),

  together with the corresponding statement for the Möbius transform of the atom, with its Jacobian
  factor: `integrable_complexAtom_and_integrable_moebiusShift` and
  `integrable_realAtom_and_integrable_moebiusShift`.

  Transcribed from three pin `S_` files (pinned `aa2d8b3`), whose `Theorems/` wrappers carry the
  headlines' statements:

  * `P2M/Sol/S_AutomorphicForm_LocalIntertwining_integrable_smoothAtom_and_integrable_weylShift_adicCompletion.lean`
  * `P2M/Sol/S_AutomorphicForm_LocalIntertwining_integrable_complexAtom_and_integrable_moebiusShift.lean`
  * `P2M/Sol/S_AutomorphicForm_LocalIntertwining_integrable_realAtom_and_integrable_moebiusShift.lean`

  The pin's file-level labels (`IntV`, `IntArchC`, `IntArchR`) are proof-search artefacts; the two
  archimedean ones are replaced by the subject namespaces `ComplexAtom` and `RealAtom`, and the
  finite-place one is kept as the pin spells it. The pin's archimedean `S_` files import `Mathlib`; this
  module names the mathlib modules they need instead.

  **Visibility.** Helper visibility follows the pin's: the finite-place row's prelude is `private`
  there and stays `private` here; the two archimedean rows are flat public surfaces in the pin and are
  public here.

  **Wiring.** `spec/check_port.py` owns every public declaration here: the three `Theorems/` wrappers
  and the three `S_` files are the wire.
  spec-pin: Theorems/Thm_AutomorphicForm_LocalIntertwining_integrable_smoothAtom_and_integrable_weylShift_adicCompletion.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_LocalIntertwining_integrable_smoothAtom_and_integrable_weylShift_adicCompletion.lean
  spec-pin: Theorems/Thm_AutomorphicForm_LocalIntertwining_integrable_complexAtom_and_integrable_moebiusShift.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_LocalIntertwining_integrable_complexAtom_and_integrable_moebiusShift.lean
  spec-pin: Theorems/Thm_AutomorphicForm_LocalIntertwining_integrable_realAtom_and_integrable_moebiusShift.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_LocalIntertwining_integrable_realAtom_and_integrable_moebiusShift.lean
-/
import FLTForHuman.EisensteinGeneral.LocalRam
import FLTForHuman.NumberTheory.NumberField.TateGlobal.NormIntegrable
import FLTForHuman.NumberTheory.NumberField.TateGlobal.LocalZetaUnramified
import FLTForHuman.LanglandsTunnell.TateLocalZeta
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open scoped NNReal

namespace AutomorphicForm
namespace LocalIntertwining

/-! ### The finite place: the smooth atom and its Weyl shift are integrable

The pin's `S_` file for this row is `S_…_integrable_smoothAtom_and_integrable_weylShift_adicCompletion`,
whose 15 helpers are `private` there and stay `private` here; the pin's own `isCompact_integers` is the
port's public `NumberField.TateGlobal.LocalZetaUnramified.isCompact_integers` and is imported, not
restated. -/
namespace IntV

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

private theorem exists_uniformizer :
    ∃ ϖ : (v.adicCompletion F)ˣ, Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ) := by
  obtain ⟨r, hr⟩ := v.valuation_exists_uniformizer' F
  obtain ⟨x, hx⟩ : ∃ x : v.adicCompletion F, Valued.v x = WithZero.exp (-1 : ℤ) :=
    ⟨_, (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation v r).trans hr⟩
  have hne : x ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hx
    exact WithZero.exp_ne_zero hx.symm
  exact ⟨Units.mk0 x hne, hx⟩

private theorem two_le_absNorm : 2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

private theorem isOpen_ball {r0 : v.adicCompletion F} (hr0v : Valued.v r0 ≠ 0) :
    IsOpen {y : v.adicCompletion F | Valued.v y ≤ Valued.v r0} := by
  have hr : Valued.v.restrict r0 ≠ 0 := fun h0 => hr0v ((Valuation.restrict_eq_zero_iff Valued.v).1 h0)
  have hset : {y : v.adicCompletion F | Valued.v y ≤ Valued.v r0}
      = {y | Valued.v.restrict y ≤ Valued.v.restrict r0} :=
    Set.ext fun y => (Valuation.restrict_le_iff Valued.v (x := y) (y := r0)).symm
  rw [hset]
  exact (Valued.isClopen_closedBall (v.adicCompletion F) hr).isOpen

private theorem integrableOn_of_locallyConstantOn
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (ϖ : (v.adicCompletion F)ˣ) (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (m : ℕ) (A : v.adicCompletion F → ℂ)
    (hA : ∀ x ∈ v.adicCompletionIntegers F, ∀ y ∈ v.adicCompletionIntegers F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → A y = A x) :
    IntegrableOn A (v.adicCompletionIntegers F : Set (v.adicCompletion F)) μ := by
  refine ContinuousOn.integrableOn_compact
    (NumberField.TateGlobal.LocalZetaUnramified.isCompact_integers (F := F) (v := v)) ?_
  intro x hx
  set r0 : v.adicCompletion F := (ϖ : v.adicCompletion F) ^ m with hr0
  have hvr0 : Valued.v r0 = Multiplicative.ofAdd (-(m : ℤ)) := by
    rw [hr0, map_pow, hϖ, ← WithZero.coe_pow, ← ofAdd_nsmul, smul_neg, nsmul_eq_mul, mul_one]
  have hr0v : Valued.v r0 ≠ 0 := by rw [hvr0]; exact WithZero.coe_ne_zero
  have hU : {y : v.adicCompletion F | Valued.v (y - x) ≤ Valued.v r0} ∈ 𝓝 x :=
    ((isOpen_ball F v hr0v).preimage (continuous_id.sub continuous_const)).mem_nhds (by simp)
  refine (continuousWithinAt_const (b := A x)).congr_of_eventuallyEq ?_ rfl
  filter_upwards [mem_nhdsWithin_of_mem_nhds hU, self_mem_nhdsWithin] with y hy hyO
  exact hA x hx y hyO (by rw [← hvr0]; exact hy)

private theorem integrable_atom
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (m : ℕ) (hm : 1 ≤ m)
    (A B : v.adicCompletion F → ℂ)
    (hA : IntegrableOn A (v.adicCompletionIntegers F : Set (v.adicCompletion F)) μ)
    (hB : ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x)
    (s : ℂ) (hs : 0 < s.re) :
    Integrable (fun x => (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A x + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
        (fun y => (((LanglandsTunnell.TateLocal.modulus y : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * s + 1)) * B y⁻¹) x) μ := by
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer F v
  have hχ : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v 1, (1 : (v.adicCompletion F)ˣ →* ℂˣ) u = 1 :=
    fun _ _ => rfl
  have h2 := two_le_absNorm F v
  have hN : 1 < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by exact_mod_cast (lt_of_lt_of_le one_lt_two h2)
  have hs' : ‖(((1 : (v.adicCompletion F)ˣ →* ℂˣ) ϖ : ℂˣ) : ℂ) *
      ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1 := by
    rw [MonoidHom.one_apply, Units.val_one, one_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
    refine Real.rpow_lt_one_of_one_lt_of_neg hN ?_
    simp only [Complex.neg_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    linarith
  have h := EisensteinGeneral.LocalRam.integrable_twisted_smooth F v μ ϖ hϖ 1 1 le_rfl hχ m hm A hA B hB s hs'
    (1 : AddChar (v.adicCompletion F) ℂ) 0 (fun _ _ => AddChar.one_apply _) 0
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  beta_reduce
  rw [AddChar.one_apply, mul_one]
  congr 1
  by_cases hx : x ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hx (zero_mem _)
    rw [LanglandsTunnell.TateLocal.charExt_of_ne_zero _ hx0, MonoidHom.inv_apply, MonoidHom.one_apply, inv_one,
      Units.val_one, one_mul]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]

private theorem mem_O_iff (x : v.adicCompletion F) : x ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) ↔ Valued.v x ≤ 1 := Iff.rfl

private theorem mem_O_iff' (x : v.adicCompletion F) : x ∈ v.adicCompletionIntegers F ↔ Valued.v x ≤ 1 := Iff.rfl

private theorem modulus_eq_one_of_v_eq_one {x : v.adicCompletion F} (hx : Valued.v x = 1) :
    LanglandsTunnell.TateLocal.modulus x = 1 := by
  rw [NumberField.TateGlobal.modulus_adicCompletion_eq_nnnorm (v := v) x, ← NNReal.coe_inj, coe_nnnorm, NNReal.coe_one,
    NumberField.FinitePlace.norm_def (K := F) (v := v) x, hx, map_one, NNReal.coe_one]

private theorem modulus_mul_modulus_inv {x : v.adicCompletion F} (hx : x ≠ 0) :
    LanglandsTunnell.TateLocal.modulus x * LanglandsTunnell.TateLocal.modulus x⁻¹ = 1 := by
  rw [← LanglandsTunnell.TateLocal.modulus_mul, mul_inv_cancel₀ hx, LanglandsTunnell.TateLocal.modulus_one]

private theorem ofAdd_neg_lt_one {m : ℕ} (hm : 1 ≤ m) :
    ((Multiplicative.ofAdd (-(m : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) < 1 := by
  rw [← WithZero.coe_one, WithZero.coe_lt_coe, ← ofAdd_zero, Multiplicative.ofAdd_lt]
  omega

private theorem v_lt_one_of_close {m : ℕ} (hm : 1 ≤ m) {x y : v.adicCompletion F}
    (hxy : Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ))) (hx : Valued.v x < 1) : Valued.v y < 1 := by
  have : y = y - x + x := by ring
  rw [this]
  exact lt_of_le_of_lt (Valued.v.map_add _ _) (max_lt (lt_of_le_of_lt hxy (ofAdd_neg_lt_one hm)) hx)

private theorem v_le_one_of_close {m : ℕ} (hm : 1 ≤ m) {x y : v.adicCompletion F}
    (hxy : Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ))) (hx : Valued.v x ≤ 1) : Valued.v y ≤ 1 := by
  have : y = y - x + x := by ring
  rw [this]
  exact le_trans (Valued.v.map_add _ _) (max_le (le_trans hxy (ofAdd_neg_lt_one hm).le) hx)

private theorem v_sub_comm (x y : v.adicCompletion F) : Valued.v (x - y) = Valued.v (y - x) := by
  rw [← neg_sub, Valuation.map_neg]

private theorem nhdsNE_zero_neBot : (𝓝[≠] (0 : v.adicCompletion F)).NeBot := by
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer F v
  have hnorm : ‖(ϖ : v.adicCompletion F)‖ < 1 := by
    rw [NumberField.FinitePlace.norm_def (K := F) (v := v), hϖ]
    have h1 : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) < 1 := by
      rw [← WithZero.coe_one, WithZero.coe_lt_coe, ← ofAdd_zero, Multiplicative.ofAdd_lt]
      omega
    exact_mod_cast (WithZeroMulInt.toNNReal_lt_one_iff
      (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)).mpr h1
  have ht := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hnorm
  have hmem : (0 : v.adicCompletion F) ∈ closure ({0}ᶜ : Set (v.adicCompletion F)) :=
    mem_closure_of_tendsto ht (Filter.Eventually.of_forall fun n => pow_ne_zero n ϖ.ne_zero)
  exact mem_closure_iff_nhdsWithin_neBot.mp hmem

theorem main
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (m : ℕ) (hm : 1 ≤ m)
    (A B : v.adicCompletion F → ℂ)
    (hA : ∀ x ∈ v.adicCompletionIntegers F, ∀ y ∈ v.adicCompletionIntegers F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → A y = A x)
    (hB : ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x)
    (s : ℂ) (hs : 0 < s.re) :
    let a : v.adicCompletion F → ℂ := fun x =>
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A x
        + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
            (fun y => (((LanglandsTunnell.TateLocal.modulus y : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * s + 1)) * B y⁻¹) x
    Integrable a μ ∧
    Integrable (fun x =>
      (((LanglandsTunnell.TateLocal.modulus x : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * s + 1)) * a x⁻¹) μ := by
  intro a
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer F v
  have hAint := integrableOn_of_locallyConstantOn F v μ ϖ hϖ m A hA
  refine ⟨integrable_atom F v μ m hm A B hAint hB s hs, ?_⟩

  classical
  let A2 : v.adicCompletion F → ℂ := fun x => if Valued.v x < 1 then B x else A x⁻¹
  let B2 : v.adicCompletion F → ℂ := (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A
  have hA2 : ∀ x ∈ v.adicCompletionIntegers F, ∀ y ∈ v.adicCompletionIntegers F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → A2 y = A2 x := by
    intro x hx y hy hxy
    by_cases hvx : Valued.v x < 1
    · have hvy : Valued.v y < 1 := v_lt_one_of_close F v hm hxy hvx
      simp only [A2, ite_eq_left hvx, ite_eq_left hvy]
      exact hB x y hxy
    · have hx1 : Valued.v x = 1 := le_antisymm ((mem_O_iff' F v x).mp hx) (not_lt.mp hvx)
      have hvy : ¬ Valued.v y < 1 := by
        intro hvy
        exact hvx (v_lt_one_of_close F v hm (by rwa [v_sub_comm]) hvy)
      have hy1 : Valued.v y = 1 := le_antisymm ((mem_O_iff' F v y).mp hy) (not_lt.mp hvy)
      simp only [A2, ite_eq_right hvx, ite_eq_right hvy]
      have hx0 : x ≠ 0 := by rintro rfl; rw [map_zero] at hx1; exact zero_ne_one hx1
      have hy0 : y ≠ 0 := by rintro rfl; rw [map_zero] at hy1; exact zero_ne_one hy1
      have hval : Valued.v (y⁻¹ - x⁻¹) = Valued.v (y - x) := by
        have : y⁻¹ - x⁻¹ = (x - y) * (x⁻¹ * y⁻¹) := by field_simp
        rw [this, Valuation.map_mul, Valuation.map_mul, map_inv₀, map_inv₀, hx1, hy1, v_sub_comm F v x y]
        simp
      refine hA x⁻¹ ?_ y⁻¹ ?_ ?_
      · exact (mem_O_iff' F v _).mpr (by rw [map_inv₀, hx1, inv_one])
      · exact (mem_O_iff' F v _).mpr (by rw [map_inv₀, hy1, inv_one])
      · rw [hval]; exact hxy
  have hB2 : ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B2 y = B2 x := by
    intro x y hxy
    by_cases hx : x ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))
    · have hy : y ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := (mem_O_iff F v y).mpr (v_le_one_of_close F v hm hxy ((mem_O_iff F v x).mp hx))
      simp only [B2, Set.indicator_of_mem hx, Set.indicator_of_mem hy]
      exact hA x hx y hy hxy
    · have hy : y ∉ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
        intro hy
        exact hx ((mem_O_iff F v x).mpr
          (v_le_one_of_close F v hm (by rwa [v_sub_comm]) ((mem_O_iff F v y).mp hy)))
      simp only [B2, Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]
  have hA2int := integrableOn_of_locallyConstantOn F v μ ϖ hϖ m A2 hA2
  have h2 := integrable_atom F v μ m hm A2 B2 hA2int hB2 s hs

  have hpt : ∀ x : v.adicCompletion F, x ≠ 0 →
      (((LanglandsTunnell.TateLocal.modulus x : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * s + 1)) * a x⁻¹ =
        (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A2 x + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
          (fun y => (((LanglandsTunnell.TateLocal.modulus y : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * s + 1)) * B2 y⁻¹) x := by
    intro x hx0
    have hmm := modulus_mul_modulus_inv F v hx0
    by_cases hxO : x ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))
    · rw [Set.indicator_of_mem hxO, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hxO), add_zero]
      by_cases hvx : Valued.v x < 1
      ·
        have hxinv : x⁻¹ ∉ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
          rw [mem_O_iff, map_inv₀, not_le]
          exact one_lt_inv_iff₀.mpr ⟨(Valuation.pos_iff _).mpr hx0, hvx⟩
        simp only [a, A2, ite_eq_left hvx, Set.indicator_of_notMem hxinv, Set.indicator_of_mem (Set.mem_compl hxinv),
          zero_add, inv_inv]
        rw [← mul_assoc, ← Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _),
          ← Complex.ofReal_mul, ← NNReal.coe_mul, hmm, NNReal.coe_one, Complex.ofReal_one, Complex.one_cpow, one_mul]
      ·
        have hx1 : Valued.v x = 1 := le_antisymm ((mem_O_iff F v x).mp hxO) (not_lt.mp hvx)
        have hxinv : x⁻¹ ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by rw [mem_O_iff, map_inv₀, hx1, inv_one]
        simp only [a, A2, ite_eq_right hvx, Set.indicator_of_mem hxinv,
          Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hxinv), add_zero]
        rw [modulus_eq_one_of_v_eq_one F v hx1, NNReal.coe_one, Complex.ofReal_one, Complex.one_cpow, one_mul]
    ·
      have hvx : 1 < Valued.v x := not_le.mp (fun h => hxO ((mem_O_iff F v x).mpr h))
      have hxinv : x⁻¹ ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
        rw [mem_O_iff, map_inv₀]
        exact inv_le_one_of_one_le₀ hvx.le
      rw [Set.indicator_of_notMem hxO, Set.indicator_of_mem (Set.mem_compl hxO), zero_add]
      simp only [a, B2, Set.indicator_of_mem hxinv, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hxinv),
        add_zero]

  have := nhdsNE_zero_neBot F v
  have hae : (fun x => (((LanglandsTunnell.TateLocal.modulus x : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * s + 1)) * a x⁻¹) =ᵐ[μ]
      fun x => (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A2 x + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
        (fun y => (((LanglandsTunnell.TateLocal.modulus y : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * s + 1)) * B2 y⁻¹) x := by
    have h0 : μ {(0 : v.adicCompletion F)} = 0 := measure_singleton 0
    refine (ae_iff.mpr (measure_mono_null (fun x hx => ?_) h0))
    simp only [Set.mem_ofPred_eq] at hx
    by_contra hx0
    exact hx (hpt x hx0)
  exact h2.congr hae.symm

end IntV

theorem integrable_smoothAtom_and_integrable_weylShift_adicCompletion
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (m : ℕ) (_hm : 1 ≤ m)
    (A B : v.adicCompletion F → ℂ)
    (_hA : ∀ x ∈ v.adicCompletionIntegers F, ∀ y ∈ v.adicCompletionIntegers F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → A y = A x)
    (_hB : ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x)
    (s : ℂ) (_hs : 0 < s.re) :
    let a : v.adicCompletion F → ℂ := fun x =>
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A x
        + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
            (fun y => (((LanglandsTunnell.TateLocal.modulus y : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * s + 1)) * B y⁻¹) x
    Integrable a μ ∧
    Integrable (fun x =>
      (((LanglandsTunnell.TateLocal.modulus x : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * s + 1)) * a x⁻¹) μ :=
  IntV.main F v μ m _hm A B _hA _hB s _hs

/-! ### The complex place: the atom and its Möbius shift are integrable -/
namespace ComplexAtom

theorem integrable_complexFactor (a b m : ℕ) (habm : a + b ≤ m) (s : ℂ) (hs : 0 < s.re) :
    Integrable (fun z : ℂ => z ^ a * (starRingEnd ℂ) z ^ b
      * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * s + 1) - (m : ℂ) / 2)) := by
  have hmaj : Integrable (fun z : ℂ => ((1 : ℝ) + ‖z‖ ^ 2) ^ (-(2 * (2 * s.re + 1)) / 2)) :=
    integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume)
      (by rw [Complex.finrank_real_complex]; push_cast; linarith)
  refine hmaj.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
  · refine ((Continuous.mul (by fun_prop) (by fun_prop)).mul ?_).aestronglyMeasurable
    exact Continuous.cpow (by fun_prop) continuous_const (fun z => Complex.ofReal_mem_slitPlane.2 (by positivity))
  · have hB1 : (1 : ℝ) ≤ 1 + ‖z‖ ^ 2 := le_add_of_nonneg_right (sq_nonneg _)
    have hBpos : (0 : ℝ) < 1 + ‖z‖ ^ 2 := by linarith
    have hre : (-(2 * s + 1) - (m : ℂ) / 2).re = -(2 * s.re + 1 + (m : ℝ) / 2) := by
      simp; ring
    rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj,
      Complex.norm_cpow_eq_rpow_re_of_pos hBpos, hre]
    have hz : ‖z‖ ≤ (1 + ‖z‖ ^ 2) ^ ((1 : ℝ) / 2) := by
      calc ‖z‖ = Real.sqrt (‖z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg z)).symm
        _ ≤ Real.sqrt (1 + ‖z‖ ^ 2) := Real.sqrt_le_sqrt (by linarith)
        _ = (1 + ‖z‖ ^ 2) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
    have hzab : ‖z‖ ^ a * ‖z‖ ^ b ≤ (1 + ‖z‖ ^ 2) ^ ((m : ℝ) / 2) := by
      calc ‖z‖ ^ a * ‖z‖ ^ b = ‖z‖ ^ (a + b) := (pow_add _ _ _).symm
        _ ≤ ((1 + ‖z‖ ^ 2) ^ ((1 : ℝ) / 2)) ^ (a + b) := pow_le_pow_left₀ (norm_nonneg z) hz _
        _ = (1 + ‖z‖ ^ 2) ^ ((1 : ℝ) / 2 * ((a + b : ℕ) : ℝ)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hBpos.le]
        _ ≤ (1 + ‖z‖ ^ 2) ^ ((m : ℝ) / 2) := by
            refine Real.rpow_le_rpow_of_exponent_le hB1 ?_
            have hm : ((a + b : ℕ) : ℝ) ≤ m := by exact_mod_cast habm
            linarith
    calc ‖z‖ ^ a * ‖z‖ ^ b * (1 + ‖z‖ ^ 2) ^ (-(2 * s.re + 1 + (m : ℝ) / 2))
        ≤ (1 + ‖z‖ ^ 2) ^ ((m : ℝ) / 2) * (1 + ‖z‖ ^ 2) ^ (-(2 * s.re + 1 + (m : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_right hzab (Real.rpow_nonneg hBpos.le _)
      _ = ((1 : ℝ) + ‖z‖ ^ 2) ^ (-(2 * (2 * s.re + 1)) / 2) := by
          rw [← Real.rpow_add hBpos]; congr 1; ring

theorem norm_complexFactor_le (a b m : ℕ) (habm : a + b ≤ m) (σ : ℝ) (y : ℂ) :
    ‖y ^ a * (starRingEnd ℂ) y ^ b * (((1 + ‖y‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * (σ : ℂ) + 1) - (m : ℂ) / 2)‖
      ≤ (1 + ‖y‖ ^ 2) ^ (-(2 * σ + 1)) := by
  have hB1 : (1 : ℝ) ≤ 1 + ‖y‖ ^ 2 := le_add_of_nonneg_right (sq_nonneg _)
  have hBpos : (0 : ℝ) < 1 + ‖y‖ ^ 2 := by linarith
  have hre : (-(2 * (σ : ℂ) + 1) - (m : ℂ) / 2).re = -(2 * σ + 1 + (m : ℝ) / 2) := by
    simp; ring
  rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj,
    Complex.norm_cpow_eq_rpow_re_of_pos hBpos, hre]
  have hz : ‖y‖ ≤ (1 + ‖y‖ ^ 2) ^ ((1 : ℝ) / 2) := by
    calc ‖y‖ = Real.sqrt (‖y‖ ^ 2) := (Real.sqrt_sq (norm_nonneg y)).symm
      _ ≤ Real.sqrt (1 + ‖y‖ ^ 2) := Real.sqrt_le_sqrt (by linarith)
      _ = (1 + ‖y‖ ^ 2) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
  have hzab : ‖y‖ ^ a * ‖y‖ ^ b ≤ (1 + ‖y‖ ^ 2) ^ ((m : ℝ) / 2) := by
    calc ‖y‖ ^ a * ‖y‖ ^ b = ‖y‖ ^ (a + b) := (pow_add _ _ _).symm
      _ ≤ ((1 + ‖y‖ ^ 2) ^ ((1 : ℝ) / 2)) ^ (a + b) := pow_le_pow_left₀ (norm_nonneg y) hz _
      _ = (1 + ‖y‖ ^ 2) ^ ((1 : ℝ) / 2 * ((a + b : ℕ) : ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hBpos.le]
      _ ≤ (1 + ‖y‖ ^ 2) ^ ((m : ℝ) / 2) := by
          refine Real.rpow_le_rpow_of_exponent_le hB1 ?_
          have hm : ((a + b : ℕ) : ℝ) ≤ m := by exact_mod_cast habm
          linarith
  calc ‖y‖ ^ a * ‖y‖ ^ b * (1 + ‖y‖ ^ 2) ^ (-(2 * σ + 1 + (m : ℝ) / 2))
      ≤ (1 + ‖y‖ ^ 2) ^ ((m : ℝ) / 2) * (1 + ‖y‖ ^ 2) ^ (-(2 * σ + 1 + (m : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_right hzab (Real.rpow_nonneg hBpos.le _)
    _ = (1 + ‖y‖ ^ 2) ^ (-(2 * σ + 1)) := by
        rw [← Real.rpow_add hBpos]; congr 1; ring

theorem floor (a b c d z : ℂ) :
    ‖a * d - b * c‖ ^ 2 * (1 + ‖z‖ ^ 2)
      ≤ (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2) * (‖a + z * c‖ ^ 2 + ‖b + z * d‖ ^ 2) := by
  set P := a + z * c with hP
  set Q := b + z * d with hQ
  have h1 : a * d - b * c = d * P - c * Q := by rw [hP, hQ]; ring
  have h2 : z * (a * d - b * c) = a * Q - b * P := by rw [hP, hQ]; ring
  have n1 : ‖a * d - b * c‖ ≤ ‖d‖ * ‖P‖ + ‖c‖ * ‖Q‖ := by
    rw [h1]
    exact (norm_sub_le _ _).trans (by rw [norm_mul, norm_mul])
  have n2 : ‖z‖ * ‖a * d - b * c‖ ≤ ‖a‖ * ‖Q‖ + ‖b‖ * ‖P‖ := by
    rw [← norm_mul, h2]
    exact (norm_sub_le _ _).trans (by rw [norm_mul, norm_mul])
  have hD := norm_nonneg (a * d - b * c)
  have hz := norm_nonneg z
  have ha := norm_nonneg a
  have hb := norm_nonneg b
  have hc := norm_nonneg c
  have hd := norm_nonneg d
  have hPn := norm_nonneg P
  have hQn := norm_nonneg Q
  have s1 : ‖a * d - b * c‖ ^ 2 ≤ (‖d‖ ^ 2 + ‖c‖ ^ 2) * (‖P‖ ^ 2 + ‖Q‖ ^ 2) := by
    calc ‖a * d - b * c‖ ^ 2 ≤ (‖d‖ * ‖P‖ + ‖c‖ * ‖Q‖) ^ 2 :=
          pow_le_pow_left₀ hD n1 2
      _ ≤ (‖d‖ ^ 2 + ‖c‖ ^ 2) * (‖P‖ ^ 2 + ‖Q‖ ^ 2) := by
          nlinarith [sq_nonneg (‖d‖ * ‖Q‖ - ‖c‖ * ‖P‖)]
  have s2 : ‖z‖ ^ 2 * ‖a * d - b * c‖ ^ 2 ≤ (‖a‖ ^ 2 + ‖b‖ ^ 2) * (‖P‖ ^ 2 + ‖Q‖ ^ 2) := by
    calc ‖z‖ ^ 2 * ‖a * d - b * c‖ ^ 2 = (‖z‖ * ‖a * d - b * c‖) ^ 2 := by ring
      _ ≤ (‖a‖ * ‖Q‖ + ‖b‖ * ‖P‖) ^ 2 := pow_le_pow_left₀ (mul_nonneg hz hD) n2 2
      _ ≤ (‖a‖ ^ 2 + ‖b‖ ^ 2) * (‖P‖ ^ 2 + ‖Q‖ ^ 2) := by
          nlinarith [sq_nonneg (‖a‖ * ‖P‖ - ‖b‖ * ‖Q‖)]
  nlinarith [s1, s2]

theorem entries_pos {a b c d : ℂ} (hdet : a * d - b * c ≠ 0) :
    0 < ‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2 := by
  have h := floor a b c d 0
  simp only [norm_zero, add_zero, zero_mul] at h
  have hD : 0 < ‖a * d - b * c‖ ^ 2 := by positivity
  have hS : 0 ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by positivity
  nlinarith [h, hD, hS, sq_nonneg ‖c‖, sq_nonneg ‖d‖]

theorem main (a b c d : ℂ) (hdet : a * d - b * c ≠ 0) (a₀ b₀ m : ℕ) (habm : a₀ + b₀ ≤ m)
    (σ : ℝ) (hσ : 0 < σ) :
    Integrable (fun z : ℂ =>
      (((‖a * d - b * c‖ ^ 2 : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2) * ((‖a + z * c‖ ^ 2 : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1)))
        * ((fun σ z => z ^ a₀ * (starRingEnd ℂ) z ^ b₀
            * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * (σ : ℂ) + 1) - ((m : ℂ)) / 2)) σ
              ((b + z * d) / (a + z * c)))) := by
  set D : ℝ := ‖a * d - b * c‖ ^ 2 with hDdef
  set S : ℝ := ‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2 with hSdef
  have hD : 0 < D := by positivity
  have hS : 0 < S := entries_pos hdet
  set K : ℝ := D ^ (σ + 1 / 2) * (D / S) ^ (-(2 * σ + 1)) with hKdef
  have hK : 0 ≤ K := mul_nonneg (Real.rpow_nonneg hD.le _) (Real.rpow_nonneg (div_pos hD hS).le _)

  have hmaj0 : Integrable (fun z : ℂ => ((1 : ℝ) + ‖z‖ ^ 2) ^ (-(2 * (2 * σ + 1)) / 2)) :=
    integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume)
      (by rw [Complex.finrank_real_complex]; push_cast; linarith)
  have hmaj : Integrable (fun z : ℂ => K * ((1 : ℝ) + ‖z‖ ^ 2) ^ (-(2 * σ + 1))) := by
    refine (hmaj0.const_mul K).congr (Filter.Eventually.of_forall fun z => ?_)
    show K * ((1 : ℝ) + ‖z‖ ^ 2) ^ (-(2 * (2 * σ + 1)) / 2) = K * ((1 : ℝ) + ‖z‖ ^ 2) ^ (-(2 * σ + 1))
    congr 1; congr 1; ring
  refine hmaj.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
  ·
    apply Measurable.aestronglyMeasurable
    fun_prop
  ·
    simp only
    set P : ℂ := a + z * c with hPdef
    set Q : ℂ := b + z * d with hQdef
    have hB1 : (1 : ℝ) ≤ 1 + ‖z‖ ^ 2 := le_add_of_nonneg_right (sq_nonneg _)
    have hBpos : (0 : ℝ) < 1 + ‖z‖ ^ 2 := by linarith
    have hrhs0 : 0 ≤ K * ((1 : ℝ) + ‖z‖ ^ 2) ^ (-(2 * σ + 1)) :=
      mul_nonneg hK (Real.rpow_nonneg hBpos.le _)
    have hexp1 : ((σ : ℂ) + 1 / 2) = (((σ + 1 / 2 : ℝ)) : ℂ) := by push_cast; ring
    have hexp2 : (-(2 * (σ : ℂ) + 1)) = (((-(2 * σ + 1) : ℝ)) : ℂ) := by push_cast; ring
    rcases eq_or_ne P 0 with hP0 | hP0
    ·
      have hne : (-(2 * (σ : ℂ) + 1)) ≠ 0 := by
        intro h
        have := congrArg Complex.re h
        simp at this; linarith
      have hzero : ((‖P‖ ^ 2 : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1)) = 0 := by
        rw [hP0, norm_zero, zero_pow two_ne_zero, Complex.ofReal_zero]
        exact Complex.zero_cpow hne
      rw [hzero, mul_zero, zero_mul, norm_zero]
      exact hrhs0
    · have hPpos : 0 < ‖P‖ ^ 2 := by positivity
      set y : ℂ := Q / P with hydef
      have hy1 : (1 : ℝ) ≤ 1 + ‖y‖ ^ 2 := le_add_of_nonneg_right (sq_nonneg _)
      have hypos : (0 : ℝ) < 1 + ‖y‖ ^ 2 := by linarith

      have nJ1 : ‖((D : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2)‖ = D ^ (σ + 1 / 2) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hD]; congr 1; simp
      have nJ2 : ‖((‖P‖ ^ 2 : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1))‖ = (‖P‖ ^ 2) ^ (-(2 * σ + 1)) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hPpos]; congr 1; simp
      have hatom := norm_complexFactor_le a₀ b₀ m habm σ y

      have hPy : ‖P‖ ^ 2 * (1 + ‖y‖ ^ 2) = ‖P‖ ^ 2 + ‖Q‖ ^ 2 := by
        rw [hydef, norm_div]
        field_simp
      have hfl : D * (1 + ‖z‖ ^ 2) / S ≤ ‖P‖ ^ 2 + ‖Q‖ ^ 2 := by
        rw [div_le_iff₀ hS]
        have := floor a b c d z
        rw [← hPdef, ← hQdef] at this
        linarith
      have hflpos : 0 < D * (1 + ‖z‖ ^ 2) / S := by positivity
      calc ‖((D : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2) * ((‖P‖ ^ 2 : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1))
              * (y ^ a₀ * (starRingEnd ℂ) y ^ b₀
                * (((1 + ‖y‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * (σ : ℂ) + 1) - ((m : ℂ)) / 2))‖
          = D ^ (σ + 1 / 2) * (‖P‖ ^ 2) ^ (-(2 * σ + 1))
              * ‖y ^ a₀ * (starRingEnd ℂ) y ^ b₀
                * (((1 + ‖y‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * (σ : ℂ) + 1) - ((m : ℂ)) / 2)‖ := by
            rw [norm_mul, norm_mul, nJ1, nJ2]
        _ ≤ D ^ (σ + 1 / 2) * (‖P‖ ^ 2) ^ (-(2 * σ + 1)) * (1 + ‖y‖ ^ 2) ^ (-(2 * σ + 1)) :=
            mul_le_mul_of_nonneg_left hatom
              (mul_nonneg (Real.rpow_nonneg hD.le _) (Real.rpow_nonneg hPpos.le _))
        _ = D ^ (σ + 1 / 2) * (‖P‖ ^ 2 + ‖Q‖ ^ 2) ^ (-(2 * σ + 1)) := by
            rw [mul_assoc, ← Real.mul_rpow hPpos.le hypos.le, hPy]
        _ ≤ D ^ (σ + 1 / 2) * (D * (1 + ‖z‖ ^ 2) / S) ^ (-(2 * σ + 1)) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hflpos hfl (by linarith))
              (Real.rpow_nonneg hD.le _)
        _ = K * ((1 : ℝ) + ‖z‖ ^ 2) ^ (-(2 * σ + 1)) := by
            rw [hKdef, show D * (1 + ‖z‖ ^ 2) / S = (D / S) * (1 + ‖z‖ ^ 2) from by ring,
              Real.mul_rpow (div_pos hD hS).le hBpos.le]
            ring

end ComplexAtom

theorem integrable_complexAtom_and_integrable_moebiusShift
    (a b c d : ℂ) (_hdet : a * d - b * c ≠ 0) (a₀ b₀ m : ℕ) (_habm : a₀ + b₀ ≤ m) (σ : ℝ) (_hσ : 0 < σ) :
    let atom : ℝ → ℂ → ℂ := fun σ z =>
      z ^ a₀ * (starRingEnd ℂ) z ^ b₀ * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * (σ : ℂ) + 1) - ((m : ℂ)) / 2)
    Integrable (atom σ) ∧
    Integrable (fun z : ℂ =>
      (((‖a * d - b * c‖ ^ 2 : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2) * ((‖a + z * c‖ ^ 2 : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1)))
        * atom σ ((b + z * d) / (a + z * c))) := by
  intro atom
  exact ⟨ComplexAtom.integrable_complexFactor a₀ b₀ m _habm (σ : ℂ) (by simpa using _hσ),
    ComplexAtom.main a b c d _hdet a₀ b₀ m _habm σ _hσ⟩

/-! ### The real place: the atom and its Möbius shift are integrable -/
namespace RealAtom

theorem norm_sub_I (x : ℝ) : ‖(x : ℂ) - Complex.I‖ = Real.sqrt (1 + x ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg ((x : ℂ) - Complex.I)), Complex.sq_norm, Complex.normSq_apply]
  congr 1
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.I_re, sub_zero, Complex.sub_im, Complex.ofReal_im,
    Complex.I_im, zero_sub]
  ring

theorem norm_unit (x : ℝ) :
    ‖((x : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)‖ = 1 := by
  have hpos : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.2 (by positivity)
  rw [norm_div, norm_sub_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos, div_self hpos.ne']

theorem unit_ne_zero (x : ℝ) : ((x : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ) ≠ 0 := by
  intro h
  have h1 := norm_unit x
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

theorem integrable_realFactor (k : ℤ) (s : ℂ) (hs : 0 < s.re) :
    Integrable (fun x : ℝ => (((x : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
      * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-(s + 1 / 2))) := by
  have hmaj : Integrable (fun x : ℝ => ((1 : ℝ) + ‖x‖ ^ 2) ^ (-(2 * s.re + 1) / 2)) :=
    integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (by rw [Module.finrank_self]; push_cast; linarith)
  refine hmaj.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · refine (Continuous.mul ?_ ?_).aestronglyMeasurable
    · exact Continuous.zpow₀ (Continuous.div (by fun_prop) (by fun_prop)
        (fun x => Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (by positivity)).ne')) k
        (fun x => Or.inl (unit_ne_zero x))
    · exact Continuous.cpow (by fun_prop) continuous_const
        (fun x => Complex.ofReal_mem_slitPlane.2 (by positivity))
  · have hre : (-(s + 1 / 2)).re = -(2 * s.re + 1) / 2 := by
      simp; ring
    have heq : ‖(((x : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
        * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-(s + 1 / 2))‖
          = ((1 : ℝ) + ‖x‖ ^ 2) ^ (-(2 * s.re + 1) / 2) := by
      rw [norm_mul, norm_zpow, norm_unit x, one_zpow, one_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), hre, Real.norm_eq_abs, sq_abs]
    exact heq.le

theorem norm_realFactor_eq (k : ℤ) (σ y : ℝ) :
    ‖(((y : ℂ) - Complex.I) / ((Real.sqrt (1 + y ^ 2) : ℝ) : ℂ)) ^ k
        * (((1 + y ^ 2 : ℝ) : ℂ)) ^ (-((σ : ℂ) + 1 / 2))‖ = (1 + y ^ 2) ^ (-(σ + 1 / 2)) := by
  have hre : (-((σ : ℂ) + 1 / 2)).re = -(σ + 1 / 2) := by simp
  rw [norm_mul, norm_zpow, norm_unit y, one_zpow, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), hre]

theorem floor (a b c d x : ℝ) :
    (a * d - b * c) ^ 2 * (1 + x ^ 2)
      ≤ (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * ((a + x * c) ^ 2 + (b + x * d) ^ 2) := by
  set P := a + x * c with hP
  set Q := b + x * d with hQ
  have h1 : a * d - b * c = d * P - c * Q := by rw [hP, hQ]; ring
  have h2 : x * (a * d - b * c) = a * Q - b * P := by rw [hP, hQ]; ring
  have s1 : (a * d - b * c) ^ 2 ≤ (d ^ 2 + c ^ 2) * (P ^ 2 + Q ^ 2) := by
    rw [h1]; nlinarith [sq_nonneg (d * Q + c * P)]
  have s2 : x ^ 2 * (a * d - b * c) ^ 2 ≤ (a ^ 2 + b ^ 2) * (P ^ 2 + Q ^ 2) := by
    have : x ^ 2 * (a * d - b * c) ^ 2 = (a * Q - b * P) ^ 2 := by rw [← h2]; ring
    rw [this]; nlinarith [sq_nonneg (a * P + b * Q)]
  nlinarith [s1, s2]

theorem entries_pos {a b c d : ℝ} (hdet : a * d - b * c ≠ 0) :
    0 < a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  have h := floor a b c d 0
  simp only [add_zero, zero_pow two_ne_zero, mul_one] at h
  have hD : 0 < (a * d - b * c) ^ 2 := by positivity
  have hS : 0 ≤ a ^ 2 + b ^ 2 := by positivity
  nlinarith [h, hD, hS, sq_nonneg c, sq_nonneg d]

theorem main (a b c d : ℝ) (hdet : a * d - b * c ≠ 0) (k : ℤ) (σ : ℝ) (hσ : 0 < σ) :
    Integrable (fun x : ℝ =>
      (((|a * d - b * c| : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2) * ((|a + x * c| : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1)))
        * ((fun σ x => ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
            * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-((σ : ℂ) + 1 / 2))) σ ((b + x * d) / (a + x * c)))) := by
  set D : ℝ := |a * d - b * c| with hDdef
  set S : ℝ := a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 with hSdef
  have hD : 0 < D := abs_pos.2 hdet
  have hS : 0 < S := entries_pos hdet
  set K : ℝ := D ^ (σ + 1 / 2) * (D ^ 2 / S) ^ (-(σ + 1 / 2)) with hKdef
  have hK : 0 ≤ K := mul_nonneg (Real.rpow_nonneg hD.le _) (Real.rpow_nonneg (by positivity) _)

  have hmaj0 : Integrable (fun x : ℝ => ((1 : ℝ) + ‖x‖ ^ 2) ^ (-(2 * σ + 1) / 2)) :=
    integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume)
      (by rw [Module.finrank_self]; push_cast; linarith)
  have hmaj : Integrable (fun x : ℝ => K * (1 + x ^ 2) ^ (-(σ + 1 / 2))) := by
    refine (hmaj0.const_mul K).congr (Filter.Eventually.of_forall fun x => ?_)
    show K * ((1 : ℝ) + ‖x‖ ^ 2) ^ (-(2 * σ + 1) / 2) = K * (1 + x ^ 2) ^ (-(σ + 1 / 2))
    rw [Real.norm_eq_abs, sq_abs]
    congr 1; congr 1; ring
  refine hmaj.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  ·
    apply Measurable.aestronglyMeasurable
    fun_prop
  ·
    simp only
    set P : ℝ := a + x * c with hPdef
    set Q : ℝ := b + x * d with hQdef
    have hBpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
    have hrhs0 : 0 ≤ K * (1 + x ^ 2) ^ (-(σ + 1 / 2)) :=
      mul_nonneg hK (Real.rpow_nonneg hBpos.le _)
    rcases eq_or_ne P 0 with hP0 | hP0
    ·
      have hne : (-(2 * (σ : ℂ) + 1)) ≠ 0 := by
        intro h
        have := congrArg Complex.re h
        simp at this; linarith
      have hzero : ((abs P : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1)) = 0 := by
        rw [hP0, abs_zero, Complex.ofReal_zero]
        exact Complex.zero_cpow hne
      rw [hzero, mul_zero, zero_mul, norm_zero]
      exact hrhs0
    · have hPpos : 0 < |P| := abs_pos.2 hP0
      have hP2pos : 0 < P ^ 2 := by positivity
      set y : ℝ := Q / P with hydef
      have hypos : (0 : ℝ) < 1 + y ^ 2 := by positivity

      have nJ1 : ‖((D : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2)‖ = D ^ (σ + 1 / 2) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hD]; congr 1; simp
      have nJ2 : ‖((abs P : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1))‖ = (P ^ 2) ^ (-(σ + 1 / 2)) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hPpos]
        have hre : (-(2 * (σ : ℂ) + 1)).re = 2 * (-(σ + 1 / 2)) := by simp; ring
        rw [hre, Real.rpow_mul (abs_nonneg P), ← sq_abs P]
        congr 1
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hatom := norm_realFactor_eq k σ y

      have hPy : P ^ 2 * (1 + y ^ 2) = P ^ 2 + Q ^ 2 := by
        rw [hydef]
        field_simp
      have hfl : D ^ 2 * (1 + x ^ 2) / S ≤ P ^ 2 + Q ^ 2 := by
        rw [div_le_iff₀ hS, hDdef, sq_abs]
        have := floor a b c d x
        rw [← hPdef, ← hQdef] at this
        linarith
      have hflpos : 0 < D ^ 2 * (1 + x ^ 2) / S := by positivity
      calc ‖((D : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2) * ((abs P : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1))
              * (((((y : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + y ^ 2) : ℝ) : ℂ)) ^ k
                * (((1 + y ^ 2 : ℝ) : ℂ)) ^ (-((σ : ℂ) + 1 / 2)))‖
          = D ^ (σ + 1 / 2) * (P ^ 2) ^ (-(σ + 1 / 2)) * (1 + y ^ 2) ^ (-(σ + 1 / 2)) := by
            rw [norm_mul, norm_mul, nJ1, nJ2, hatom]
        _ = D ^ (σ + 1 / 2) * (P ^ 2 + Q ^ 2) ^ (-(σ + 1 / 2)) := by
            rw [mul_assoc, ← Real.mul_rpow hP2pos.le hypos.le, hPy]
        _ ≤ D ^ (σ + 1 / 2) * (D ^ 2 * (1 + x ^ 2) / S) ^ (-(σ + 1 / 2)) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hflpos hfl (by linarith))
              (Real.rpow_nonneg hD.le _)
        _ = K * (1 + x ^ 2) ^ (-(σ + 1 / 2)) := by
            rw [hKdef, show D ^ 2 * (1 + x ^ 2) / S = (D ^ 2 / S) * (1 + x ^ 2) from by ring,
              Real.mul_rpow (by positivity) hBpos.le]
            ring

end RealAtom

theorem integrable_realAtom_and_integrable_moebiusShift
    (a b c d : ℝ) (_hdet : a * d - b * c ≠ 0) (k : ℤ) (σ : ℝ) (_hσ : 0 < σ) :
    let atom : ℝ → ℝ → ℂ := fun σ x =>
      ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-((σ : ℂ) + 1 / 2))
    Integrable (atom σ) ∧
    Integrable (fun x : ℝ =>
      (((|a * d - b * c| : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2) * ((|a + x * c| : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1)))
        * atom σ ((b + x * d) / (a + x * c))) := by
  intro atom
  exact ⟨RealAtom.integrable_realFactor k (σ : ℂ) (by simpa using _hσ),
    RealAtom.main a b c d _hdet k σ _hσ⟩

end LocalIntertwining
end AutomorphicForm
