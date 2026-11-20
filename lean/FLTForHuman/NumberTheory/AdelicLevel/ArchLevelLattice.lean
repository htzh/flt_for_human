/-
The adelic level lattice and its archimedean dictionary.

Three rows of the `AdelicLevel` layer: the rational strong-approximation step into the
level-`N` subgroup (`exists_glFin_globalPoints_mul_mem_finiteLevelOne_rat`), the
commutation of `diagOne` with the real unipotent subgroup together with the standard
character's value at the half-characteristic, and the `diagOne` decomposition into a
finite-level part, an archimedean lift and a central scalar.

  spec-pin: P2M/Sol/S_NumberField_AdelicLevel_exists_glFin_globalPoints_mul_mem_finiteLevelOne_rat.lean
  spec-pin: P2M/Sol/S_NumberField_AdelicLevel_diagOne_mul_archRealGLAt_unipotent_eq_and_stdAddChar_single_half.lean
  spec-pin: P2M/Sol/S_NumberField_AdelicLevel_diagOne_eq_diagOne_mul_archRealLiftAt_mul_centralScalar.lean

## Port deltas

* `import FLTForHuman.NumberTheory.NumberField.TateGlobal.IdeleNormValues` — carries the pin's
  public `map_diagOne` (`S_…diagOne_mul_archRealGLAt…:20`, `S_…diagOne_eq_diagOne_mul…:20`), which
  both pins state as a shared prelude; it is declared there at the pin's statement, so it is used
  from the import rather than re-proved.

## Heartbeat probe (measured 2026-11-19, never installed)

`lake env lean -DautoImplicit=false -DmaxHeartbeats=N FLTForHuman/NumberTheory/AdelicLevel/ArchLevelLattice.lean`
is **silent at N = 32 000** and **fails at N = 16 000** (the first reported site is
`LevelCovering.exists_sub_algebraMap_mem_idealBall`, its `Submodule.exists_mem_ne_zero_of_ne_bot`
step). The natural per-declaration cost is ≈30 000, so 32 000 is ≈1.07× — the floor is a real
measurement, not a margin. No `set_option maxHeartbeats` is carried by this module; the gate is
run at the playbook's own `-DmaxHeartbeats=200000`.
-/
import FLTForHuman.NumberTheory.AdelicLevel.StrongApproxRat
import FLTForHuman.NumberTheory.NumberField.IdeleSPartIntegral
import FLTForHuman.NumberTheory.UnimodularLift
import FLTForHuman.NumberTheory.AdelicLevel.Level
import FLTForHuman.NumberTheory.NumberField.AdelicTraceFin
import FLTForHuman.AutomorphicForm.Adelic.ArchCasimir
import FLTForHuman.NumberTheory.NumberField.TateGlobal.IdeleNormValues

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm IsDedekindDomain Matrix
open scoped Classical ENNReal BigOperators

namespace NumberField.AdelicLevel

/-! ### B1 — the rational level-covering engine (pin `S_…finiteLevelOne_rat.lean`, `M4aP1R.LevelCovering`) -/

namespace LevelCovering

open IsDedekindDomain.HeightOneSpectrum

open scoped WithZero

section General

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem exists_algebraMap_eq_of_mem_integralFiniteAdeles {q : K}
    (hq : algebraMap K (FiniteAdeleRing R K) q ∈ integralFiniteAdeles R K) :
    ∃ r : R, algebraMap R K r = q := by
  have h : ∀ v : HeightOneSpectrum R, v.valuation K q ≤ 1 := fun v => by
    have h1 := hq v
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      show (algebraMap K (FiniteAdeleRing R K) q) v = ((q : K) : v.adicCompletion K) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h1
    exact h1
  exact HeightOneSpectrum.mem_integers_of_valuation_le_one K q h

theorem pow_count_dvd {N : Ideal R} (hN : N ≠ ⊥) (v : HeightOneSpectrum R) :
    v.asIdeal ^ ((Associates.mk v.asIdeal).count (Associates.mk N).factors) ∣ N := by
  classical
  rw [← Associates.mk_le_mk_iff_dvd, Associates.mk_pow]
  exact (Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hN)
    (Associates.irreducible_mk.mpr v.irreducible)).mpr le_rfl

theorem intValuation_le_idealBound {N : Ideal R} (hN : N ≠ ⊥) {r : R} (hr : r ∈ N)
    (v : HeightOneSpectrum R) : v.intValuation r ≤ idealBound R N v := by
  classical
  rw [idealBound_of_ne_bot hN, intValuation_le_pow_iff_dvd]
  exact (pow_count_dvd hN v).trans (Ideal.dvd_span_singleton.mpr hr)

theorem algebraMap_mem_idealBall {N : Ideal R} (hN : N ≠ ⊥) {r : R} (hr : r ∈ N) :
    algebraMap K (FiniteAdeleRing R K) (algebraMap R K r) ∈ idealBall R K N := fun v => by
  rw [show (algebraMap K (FiniteAdeleRing R K) (algebraMap R K r)) v
      = algebraMap K (v.adicCompletion K) (algebraMap R K r) from rfl, valued_algebraMap]
  exact intValuation_le_idealBound hN hr v

theorem algebraMap_mem_integralFiniteAdeles (r : R) :
    algebraMap K (FiniteAdeleRing R K) (algebraMap R K r) ∈ integralFiniteAdeles R K := fun v =>
  NumberField.AdelicLevel.algebraMap_mem_adicCompletionIntegers v r

theorem idealBound_span_singleton {n₀ : R} (hn : n₀ ≠ 0) (v : HeightOneSpectrum R) :
    idealBound R (Ideal.span {n₀}) v = v.intValuation n₀ := by
  classical
  rw [idealBound_of_ne_bot (by rwa [Ne, Ideal.span_singleton_eq_bot]), v.intValuation_if_neg hn]

theorem mem_span_singleton_of_algebraMap_mem_idealBall {n₀ r : R} (hn : n₀ ≠ 0)
    (h : algebraMap K (FiniteAdeleRing R K) (algebraMap R K r) ∈ idealBall R K (Ideal.span {n₀})) :
    r ∈ Ideal.span {n₀} := by
  have hv : ∀ v : HeightOneSpectrum R, v.intValuation r ≤ v.intValuation n₀ := fun v => by
    have h1 := h v
    rw [show (algebraMap K (FiniteAdeleRing R K) (algebraMap R K r)) v
        = algebraMap K (v.adicCompletion K) (algebraMap R K r) from rfl, valued_algebraMap,
      idealBound_span_singleton hn] at h1
    exact h1
  have hn' : algebraMap R K n₀ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hn
  have hle : ∀ v : HeightOneSpectrum R,
      v.valuation K (algebraMap R K r / algebraMap R K n₀) ≤ 1 := fun v => by
    rw [map_div₀, valuation_of_algebraMap, valuation_of_algebraMap]
    exact (div_le_one₀ (zero_lt_iff.mpr (intValuation_ne_zero v n₀ hn))).mpr (hv v)
  obtain ⟨m, hm⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K _ hle
  rw [Ideal.mem_span_singleton']
  refine ⟨m, IsFractionRing.injective R K ?_⟩
  rw [map_mul, hm, div_mul_cancel₀ _ hn']

theorem neg_mem_idealBall {N : Ideal R} {x : FiniteAdeleRing R K} (hx : x ∈ idealBall R K N) :
    -x ∈ idealBall R K N := fun v => by
  rw [coe_neg_apply, Valuation.map_neg]; exact hx v

theorem sub_mem_idealBall {N : Ideal R} {x y : FiniteAdeleRing R K} (hx : x ∈ idealBall R K N)
    (hy : y ∈ idealBall R K N) : x - y ∈ idealBall R K N := by
  rw [sub_eq_add_neg]; exact add_mem_idealBall hx (neg_mem_idealBall hy)

theorem idealBall_mono {M N : Ideal R} (hM : M ≠ ⊥) (h : M ≤ N) :
    idealBall R K M ⊆ idealBall R K N := fun x hx v => by
  classical
  have hN : N ≠ ⊥ := fun hN => hM (le_bot_iff.mp (hN ▸ h))
  refine (hx v).trans ?_
  rw [idealBound_of_ne_bot hM, idealBound_of_ne_bot hN, WithZero.exp_le_exp, neg_le_neg_iff,
    Int.ofNat_le]
  exact Associates.count_le_count_of_le (Associates.mk_ne_zero.mpr hM)
    (Associates.irreducible_mk.mpr v.irreducible)
    (Associates.mk_le_mk_iff_dvd.mpr (Ideal.dvd_iff_le.mpr h))

theorem exists_sub_algebraMap_mem_idealBall {N : Ideal R} (hN : N ≠ ⊥) {x : FiniteAdeleRing R K}
    (hx : x ∈ integralFiniteAdeles R K) :
    ∃ a : R, x - algebraMap K (FiniteAdeleRing R K) (algebraMap R K a) ∈ idealBall R K N := by
  obtain ⟨n₀, hnN, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN
  have hnK : algebraMap R K n₀ ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hn0
  set nA : FiniteAdeleRing R K := algebraMap K (FiniteAdeleRing R K) (algebraMap R K n₀) with hnA_def
  have hnA : IsUnit nA := (Ne.isUnit hnK).map (algebraMap K (FiniteAdeleRing R K))

  obtain ⟨k, hk⟩ := IsDedekindDomain.FiniteAdeleRing.exists_sub_algebraMap_mem_adicCompletionIntegers
    K (((hnA.unit⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) * x)
  set y : FiniteAdeleRing R K := ((hnA.unit⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) * x
    - algebraMap K (FiniteAdeleRing R K) k with hy_def
  have hy : y ∈ integralFiniteAdeles R K := fun v => hk v

  have hunit : nA * ((hnA.unit⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) = 1 :=
    hnA.mul_val_inv
  have hxy : x - algebraMap K (FiniteAdeleRing R K) (algebraMap R K n₀ * k) = nA * y := by
    rw [hy_def, mul_sub, ← mul_assoc, hunit, one_mul, map_mul]

  have hint : algebraMap K (FiniteAdeleRing R K) (algebraMap R K n₀ * k)
      ∈ integralFiniteAdeles R K := by
    have h1 : algebraMap K (FiniteAdeleRing R K) (algebraMap R K n₀ * k) = x - nA * y := by
      rw [← hxy, sub_sub_cancel]
    rw [h1]
    exact sub_mem_integralFiniteAdeles hx (idealBall_subset_integralFiniteAdeles N
      (mul_mem_idealBall_right (algebraMap_mem_idealBall hN hnN) hy))
  obtain ⟨a, ha⟩ := exists_algebraMap_eq_of_mem_integralFiniteAdeles hint
  refine ⟨a, ?_⟩
  rw [ha, hxy]
  exact mul_mem_idealBall_right (algebraMap_mem_idealBall hN hnN) hy

theorem isLevelOneMatrix_mono {M N : Ideal R} (hM : M ≠ ⊥) (h : M ≤ N)
    {m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)} (hm : IsLevelOneMatrix R K M m) :
    IsLevelOneMatrix R K N m :=
  { integral := hm.integral
    lowerLeft := idealBall_mono hM h hm.lowerLeft
    lowerRight := idealBall_mono hM h hm.lowerRight }

end General

section SL2

variable {A : Type*} [CommRing A]

def bezoutGL2 (a b s t : A) (h : a * s + b * t = 1) : GL (Fin 2) A where
  val := !![b, -a; s, t]
  inv := !![t, a; -s, b]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> first | linear_combination h | ring
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> first | linear_combination h | ring

@[scoped simp] theorem bezoutGL2_val (a b s t : A) (h : a * s + b * t = 1) :
    ((bezoutGL2 a b s t h : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = !![b, -a; s, t] := rfl

@[scoped simp] theorem bezoutGL2_inv_val (a b s t : A) (h : a * s + b * t = 1) :
    (((bezoutGL2 a b s t h)⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = !![t, a; -s, b] := rfl

end SL2

section Rat

theorem glFin_globalPoints_eq_map (γ : GL (Fin 2) ℚ) :
    glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ)
      = Matrix.GeneralLinearGroup.map (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)) γ := by
  ext i j
  rfl

abbrev intAdele (r : 𝓞 ℚ) : FiniteAdeleRing (𝓞 ℚ) ℚ :=
  algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (algebraMap (𝓞 ℚ) ℚ r)

theorem intAdele_mem (r : 𝓞 ℚ) : intAdele r ∈ integralFiniteAdeles (𝓞 ℚ) ℚ :=
  algebraMap_mem_integralFiniteAdeles r

theorem exists_map_mul_mem_finiteLevelOne {N : Ideal (𝓞 ℚ)} (hN : N ≠ ⊥)
    {k : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hk : k ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ) :
    ∃ γ : GL (Fin 2) ℚ,
      Matrix.GeneralLinearGroup.map (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)) γ * k
        ∈ finiteLevelOne (𝓞 ℚ) ℚ N := by
  rw [mem_finiteIntegralGL2_iff] at hk
  obtain ⟨hkint, hkinvint⟩ := hk

  obtain ⟨n₀, hnN, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN
  set P : Ideal (𝓞 ℚ) := Ideal.span {n₀} with hP_def
  have hP : P ≠ ⊥ := by rwa [hP_def, Ne, Ideal.span_singleton_eq_bot]
  have hPN : P ≤ N := (Ideal.span_singleton_le_iff_mem _).mpr hnN

  set A : FiniteAdeleRing (𝓞 ℚ) ℚ := ((k⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) _) 1 0 with hA
  set B : FiniteAdeleRing (𝓞 ℚ) ℚ := ((k⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) _) 1 1 with hB
  have hAint : A ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := hkinvint 1 0
  have hBint : B ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := hkinvint 1 1

  have hinv : ((k⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
      * (k : Matrix (Fin 2) (Fin 2) _) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hrow0 : A * (k : Matrix (Fin 2) (Fin 2) _) 0 0 + B * (k : Matrix (Fin 2) (Fin 2) _) 1 0 = 0 := by
    have h := congrFun (congrFun hinv 1) 0
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_ne (by decide)] at h
    exact h
  have hrow1 : A * (k : Matrix (Fin 2) (Fin 2) _) 0 1 + B * (k : Matrix (Fin 2) (Fin 2) _) 1 1 = 1 := by
    have h := congrFun (congrFun hinv 1) 1
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at h
    exact h

  obtain ⟨c₀, hc₀⟩ := exists_sub_algebraMap_mem_idealBall (K := ℚ) hP hAint
  obtain ⟨d₀, hd₀⟩ := exists_sub_algebraMap_mem_idealBall (K := ℚ) hP hBint
  obtain ⟨p₀, hp₀⟩ := exists_sub_algebraMap_mem_idealBall (K := ℚ) hP (hkint 0 1)
  obtain ⟨q₀, hq₀⟩ := exists_sub_algebraMap_mem_idealBall (K := ℚ) hP (hkint 1 1)

  have hbez : c₀ * p₀ + d₀ * q₀ - 1 ∈ P := by
    refine mem_span_singleton_of_algebraMap_mem_idealBall (K := ℚ) hn0 ?_
    have himage : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)
          (algebraMap (𝓞 ℚ) ℚ (c₀ * p₀ + d₀ * q₀ - 1))
        = intAdele c₀ * intAdele p₀ + intAdele d₀ * intAdele q₀ - 1 := by
      simp only [intAdele, map_add, map_sub, map_mul, map_one]
    rw [himage]

    have halg : intAdele c₀ * intAdele p₀ + intAdele d₀ * intAdele q₀ - 1
        = (A * (k : Matrix (Fin 2) (Fin 2) _) 0 1 + B * (k : Matrix (Fin 2) (Fin 2) _) 1 1 - 1)
          - ((A - intAdele c₀) * (k : Matrix (Fin 2) (Fin 2) _) 0 1
              + intAdele c₀ * ((k : Matrix (Fin 2) (Fin 2) _) 0 1 - intAdele p₀)
              + (B - intAdele d₀) * (k : Matrix (Fin 2) (Fin 2) _) 1 1
              + intAdele d₀ * ((k : Matrix (Fin 2) (Fin 2) _) 1 1 - intAdele q₀)) := by ring
    rw [halg, hrow1, sub_self, zero_sub]
    refine neg_mem_idealBall (add_mem_idealBall (add_mem_idealBall (add_mem_idealBall ?_ ?_) ?_) ?_)
    · exact mul_mem_idealBall_right hc₀ (hkint 0 1)
    · exact mul_mem_idealBall_left (intAdele_mem c₀) hp₀
    · exact mul_mem_idealBall_right hd₀ (hkint 1 1)
    · exact mul_mem_idealBall_left (intAdele_mem d₀) hq₀

  set e : 𝓞 ℚ ≃+* ℤ := Rat.ringOfIntegersEquiv with he
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hbez
  have htriple : ∃ x y z : ℤ, x * e c₀ + y * e d₀ + z * e n₀ = 1 := by
    refine ⟨e p₀, e q₀, -e w, ?_⟩
    have h := congrArg e hw
    rw [map_mul, map_sub, map_add, map_mul, map_mul, map_one] at h
    linear_combination -h
  obtain ⟨s, t, hs, ht, hcop⟩ := Int.exists_modEq_and_modEq_and_isCoprime htriple
  obtain ⟨a, b, hab⟩ := hcop

  set s₀ := e.symm s with hs₀
  set t₀ := e.symm t with ht₀
  set a₀ := e.symm a with ha₀
  set b₀ := e.symm b with hb₀
  have hab₀ : a₀ * s₀ + b₀ * t₀ = 1 := by
    apply e.injective
    rw [map_add, map_mul, map_mul, map_one, hs₀, ht₀, ha₀, hb₀, e.apply_symm_apply,
      e.apply_symm_apply, e.apply_symm_apply, e.apply_symm_apply]
    exact hab

  have hcong : ∀ {u : ℤ} {r₀ : 𝓞 ℚ}, u ≡ e r₀ [ZMOD e n₀] →
      intAdele (e.symm u) - intAdele r₀ ∈ idealBall (𝓞 ℚ) ℚ P := by
    intro u r₀ hu
    have hdvd : n₀ ∣ e.symm u - r₀ := by
      have h1 : e n₀ ∣ u - e r₀ := (Int.modEq_iff_dvd.mp hu.symm)
      have h2 := map_dvd e.symm h1
      rwa [map_sub, e.symm_apply_apply, e.symm_apply_apply] at h2
    have hmem : e.symm u - r₀ ∈ P := Ideal.mem_span_singleton.mpr hdvd
    have h3 := algebraMap_mem_idealBall (K := ℚ) hP hmem
    rwa [map_sub, map_sub] at h3
  have hsA : intAdele s₀ - A ∈ idealBall (𝓞 ℚ) ℚ P := by
    have h1 : intAdele s₀ - A = (intAdele s₀ - intAdele c₀) - (A - intAdele c₀) := by ring
    rw [h1]; exact sub_mem_idealBall (hcong hs) hc₀
  have htB : intAdele t₀ - B ∈ idealBall (𝓞 ℚ) ℚ P := by
    have h1 : intAdele t₀ - B = (intAdele t₀ - intAdele d₀) - (B - intAdele d₀) := by ring
    rw [h1]; exact sub_mem_idealBall (hcong ht) hd₀

  have habQ : algebraMap (𝓞 ℚ) ℚ a₀ * algebraMap (𝓞 ℚ) ℚ s₀
      + algebraMap (𝓞 ℚ) ℚ b₀ * algebraMap (𝓞 ℚ) ℚ t₀ = 1 := by
    have h := congrArg (algebraMap (𝓞 ℚ) ℚ) hab₀
    rwa [map_add, map_mul, map_mul, map_one] at h
  refine ⟨bezoutGL2 _ _ _ _ habQ, ?_⟩
  set S := bezoutGL2 _ _ _ _ habQ with hS
  set SA := Matrix.GeneralLinearGroup.map (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)) S with hSA

  have hSA00 : (SA : Matrix (Fin 2) (Fin 2) _) 0 0 = intAdele b₀ := by
    rw [hSA, Matrix.GeneralLinearGroup.map_apply, hS, LevelCovering.bezoutGL2_val]; rfl
  have hSA01 : (SA : Matrix (Fin 2) (Fin 2) _) 0 1 = intAdele (-a₀) := by
    rw [hSA, Matrix.GeneralLinearGroup.map_apply, hS, LevelCovering.bezoutGL2_val]
    show algebraMap ℚ _ (-(algebraMap (𝓞 ℚ) ℚ a₀)) = _
    rw [← map_neg]
  have hSA10 : (SA : Matrix (Fin 2) (Fin 2) _) 1 0 = intAdele s₀ := by
    rw [hSA, Matrix.GeneralLinearGroup.map_apply, hS, LevelCovering.bezoutGL2_val]; rfl
  have hSA11 : (SA : Matrix (Fin 2) (Fin 2) _) 1 1 = intAdele t₀ := by
    rw [hSA, Matrix.GeneralLinearGroup.map_apply, hS, LevelCovering.bezoutGL2_val]; rfl
  have hSAi00 : ((SA⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) _) 0 0 = intAdele t₀ := by
    rw [hSA, ← map_inv, Matrix.GeneralLinearGroup.map_apply, hS, LevelCovering.bezoutGL2_inv_val]
    rfl
  have hSAi01 : ((SA⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) _) 0 1 = intAdele a₀ := by
    rw [hSA, ← map_inv, Matrix.GeneralLinearGroup.map_apply, hS, LevelCovering.bezoutGL2_inv_val]
    rfl
  have hSAi10 : ((SA⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) _) 1 0 = intAdele (-s₀) := by
    rw [hSA, ← map_inv, Matrix.GeneralLinearGroup.map_apply, hS, LevelCovering.bezoutGL2_inv_val]
    show algebraMap ℚ _ (-(algebraMap (𝓞 ℚ) ℚ s₀)) = _
    rw [← map_neg]
  have hSAi11 : ((SA⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) _) 1 1 = intAdele b₀ := by
    rw [hSA, ← map_inv, Matrix.GeneralLinearGroup.map_apply, hS, LevelCovering.bezoutGL2_inv_val]
    rfl
  have hSAint : ∀ i j, (SA : Matrix (Fin 2) (Fin 2) _) i j ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
    refine Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩, Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩
    · rw [hSA00]; exact intAdele_mem _
    · rw [hSA01]; exact intAdele_mem _
    · rw [hSA10]; exact intAdele_mem _
    · rw [hSA11]; exact intAdele_mem _
  have hSAiint : ∀ i j, ((SA⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) _) i j
      ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
    refine Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩, Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩
    · rw [hSAi00]; exact intAdele_mem _
    · rw [hSAi01]; exact intAdele_mem _
    · rw [hSAi10]; exact intAdele_mem _
    · rw [hSAi11]; exact intAdele_mem _
  have hAs : A - intAdele s₀ ∈ idealBall (𝓞 ℚ) ℚ P := by
    rw [← neg_sub]; exact neg_mem_idealBall hsA
  have hBt : B - intAdele t₀ ∈ idealBall (𝓞 ℚ) ℚ P := by
    rw [← neg_sub]; exact neg_mem_idealBall htB

  have hM : ((SA * k : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
      = (SA : Matrix (Fin 2) (Fin 2) _) * (k : Matrix (Fin 2) (Fin 2) _) := Units.val_mul _ _
  have hMi : (((SA * k)⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
      = ((k⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) _)
        * ((SA⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) _) := by
    rw [_root_.mul_inv_rev, Units.val_mul]
  rw [mem_finiteLevelOne_iff]
  constructor
  · refine { integral := ?_, lowerLeft := ?_, lowerRight := ?_ }
    · intro i j
      rw [hM, Matrix.mul_apply, Fin.sum_univ_two]
      exact add_mem_integralFiniteAdeles (mul_mem_integralFiniteAdeles (hSAint i 0) (hkint 0 j))
        (mul_mem_integralFiniteAdeles (hSAint i 1) (hkint 1 j))
    · rw [hM, Matrix.mul_apply, Fin.sum_univ_two, hSA10, hSA11]
      have h1 : intAdele s₀ * (k : Matrix (Fin 2) (Fin 2) _) 0 0
            + intAdele t₀ * (k : Matrix (Fin 2) (Fin 2) _) 1 0
          = (intAdele s₀ - A) * (k : Matrix (Fin 2) (Fin 2) _) 0 0
            + (intAdele t₀ - B) * (k : Matrix (Fin 2) (Fin 2) _) 1 0
            + (A * (k : Matrix (Fin 2) (Fin 2) _) 0 0
                + B * (k : Matrix (Fin 2) (Fin 2) _) 1 0) := by
        ring
      rw [h1, hrow0, add_zero]
      exact idealBall_mono hP hPN (add_mem_idealBall (mul_mem_idealBall_right hsA (hkint 0 0))
        (mul_mem_idealBall_right htB (hkint 1 0)))
    · rw [hM, Matrix.mul_apply, Fin.sum_univ_two, hSA10, hSA11]
      have h1 : intAdele s₀ * (k : Matrix (Fin 2) (Fin 2) _) 0 1
            + intAdele t₀ * (k : Matrix (Fin 2) (Fin 2) _) 1 1 - 1
          = (intAdele s₀ - A) * (k : Matrix (Fin 2) (Fin 2) _) 0 1
            + (intAdele t₀ - B) * (k : Matrix (Fin 2) (Fin 2) _) 1 1
            + (A * (k : Matrix (Fin 2) (Fin 2) _) 0 1
                + B * (k : Matrix (Fin 2) (Fin 2) _) 1 1 - 1) := by
        ring
      rw [h1, hrow1, sub_self, add_zero]
      exact idealBall_mono hP hPN (add_mem_idealBall (mul_mem_idealBall_right hsA (hkint 0 1))
        (mul_mem_idealBall_right htB (hkint 1 1)))
  · refine { integral := ?_, lowerLeft := ?_, lowerRight := ?_ }
    · intro i j
      rw [hMi, Matrix.mul_apply, Fin.sum_univ_two]
      exact add_mem_integralFiniteAdeles (mul_mem_integralFiniteAdeles (hkinvint i 0) (hSAiint 0 j))
        (mul_mem_integralFiniteAdeles (hkinvint i 1) (hSAiint 1 j))
    · rw [hMi, Matrix.mul_apply, Fin.sum_univ_two, hSAi00, hSAi10, ← hA, ← hB]
      have h1 : A * intAdele t₀ + B * intAdele (-s₀)
          = A * (intAdele t₀ - B) - B * (intAdele s₀ - A) := by
        simp only [intAdele, map_neg]; ring
      rw [h1]
      exact idealBall_mono hP hPN (sub_mem_idealBall (mul_mem_idealBall_left hAint htB)
        (mul_mem_idealBall_left hBint hsA))
    · rw [hMi, Matrix.mul_apply, Fin.sum_univ_two, hSAi01, hSAi11, ← hA, ← hB]
      have hone : intAdele a₀ * intAdele s₀ + intAdele b₀ * intAdele t₀ = 1 := by
        simp only [intAdele, ← map_mul, ← map_add, hab₀, map_one]
      have h1 : A * intAdele a₀ + B * intAdele b₀ - 1
          = intAdele a₀ * (A - intAdele s₀) + intAdele b₀ * (B - intAdele t₀)
            + (intAdele a₀ * intAdele s₀ + intAdele b₀ * intAdele t₀ - 1) := by
        ring
      rw [h1, hone, sub_self, add_zero]
      exact idealBall_mono hP hPN (add_mem_idealBall (mul_mem_idealBall_left (intAdele_mem _) hAs)
        (mul_mem_idealBall_left (intAdele_mem _) hBt))

theorem exists_glFin_globalPoints_mul_mem_finiteLevelOne_rat_impl
    {N : Ideal (𝓞 ℚ)} (hN : N ≠ ⊥) (g : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    ∃ γ : GL (Fin 2) ℚ,
      NumberField.AdelicLevel.glFin (𝓞 ℚ) ℚ (AutomorphicForm.globalPoints (𝓞 ℚ) ℚ γ) * g
        ∈ NumberField.AdelicLevel.finiteLevelOne (𝓞 ℚ) ℚ N := by
  obtain ⟨γ₀, hγ₀⟩ := NumberField.AdelicLevel.exists_globalPoints_mul_mem_finiteIntegralGL2_rat g
  obtain ⟨γ₁, hγ₁⟩ := exists_map_mul_mem_finiteLevelOne hN hγ₀
  refine ⟨γ₁ * γ₀, ?_⟩
  rw [map_mul, map_mul, glFin_globalPoints_eq_map γ₁, mul_assoc]
  exact hγ₁

end Rat

end LevelCovering

/-! ### B2/B3 — the archimedean dictionary of `diagOne` (the pins' `Elem17` block) -/

namespace ArchLevel

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion

variable {F : Type} [Field F] [NumberField F]

theorem map_scalar {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (a : Aˣ) :
    Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.scalar (Fin 2) a) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map f.toMonoidHom a) := by
  ext i j
  change f ((Matrix.scalar (Fin 2) (a : A)) i j)
    = (Matrix.scalar (Fin 2) ((Units.map f.toMonoidHom a : Bˣ) : B)) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs
  · rfl
  · exact map_zero f

theorem scalar_coe_apply {A : Type*} [CommRing A] (a : Aˣ) (i j : Fin 2) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) a : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) i j =
      if i = j then (a : A) else 0 := by
  change (Matrix.scalar (Fin 2) (a : A)) i j = _
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]

theorem archComponent_glArch_diagOne (w : InfinitePlace F) (a : (AdeleRing (𝓞 F) F)ˣ) :
    archComponent F w (glArch (𝓞 F) F (diagOne a)) =
      diagOne (Units.map (archEval F w).toMonoidHom (Units.map (adeleArch (𝓞 F) F).toMonoidHom a)) := by
  change Matrix.GeneralLinearGroup.map (archEval F w)
    (Matrix.GeneralLinearGroup.map (adeleArch (𝓞 F) F) (diagOne a)) = _
  rw [NumberField.TateGlobal.map_diagOne, NumberField.TateGlobal.map_diagOne]

theorem glFin_diagOne_of_snd_eq_one (a : (AdeleRing (𝓞 F) F)ˣ)
    (ha : ((a : AdeleRing (𝓞 F) F)).2 = 1) :
    glFin (𝓞 F) F (diagOne a) = 1 := by
  change Matrix.GeneralLinearGroup.map (adeleFin (𝓞 F) F) (diagOne a) = 1
  rw [NumberField.TateGlobal.map_diagOne]
  have : Units.map (adeleFin (𝓞 F) F).toMonoidHom a = 1 := Units.ext ha
  rw [this, map_one]

theorem archComponent_glArch_centralScalar (w : InfinitePlace F) (z : (AdeleRing (𝓞 F) F)ˣ) :
    archComponent F w (glArch (𝓞 F) F (centralScalar (𝓞 F) F z)) =
      Matrix.GeneralLinearGroup.scalar (Fin 2)
        (Units.map (archEval F w).toMonoidHom (Units.map (adeleArch (𝓞 F) F).toMonoidHom z)) := by
  change Matrix.GeneralLinearGroup.map (archEval F w)
    (Matrix.GeneralLinearGroup.map (adeleArch (𝓞 F) F)
      (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) = _
  rw [map_scalar, map_scalar]

theorem glFin_centralScalar_of_snd_eq_one (z : (AdeleRing (𝓞 F) F)ˣ)
    (hz : ((z : AdeleRing (𝓞 F) F)).2 = 1) :
    glFin (𝓞 F) F (centralScalar (𝓞 F) F z) = 1 := by
  change Matrix.GeneralLinearGroup.map (adeleFin (𝓞 F) F)
    (Matrix.GeneralLinearGroup.scalar (Fin 2) z) = 1
  rw [map_scalar]
  have : Units.map (adeleFin (𝓞 F) F).toMonoidHom z = 1 := Units.ext hz
  rw [this, map_one]

theorem map_unipotentGL2 {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (x : A) :
    Matrix.GeneralLinearGroup.map f (unipotentGL2 x) = unipotentGL2 (f x) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change f ((unipotentGL2 x : Matrix (Fin 2) (Fin 2) A) i j) = _
  rw [unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

theorem archComponent_glArch_unipotentGL2 (w : InfinitePlace F) (X : AdeleRing (𝓞 F) F) :
    archComponent F w (glArch (𝓞 F) F (unipotentGL2 X)) = unipotentGL2 (X.1 w) := by
  change Matrix.GeneralLinearGroup.map (archEval F w)
    (Matrix.GeneralLinearGroup.map (adeleArch (𝓞 F) F) (unipotentGL2 X)) = _
  rw [map_unipotentGL2, map_unipotentGL2]
  rfl

theorem glFin_unipotentGL2 (X : AdeleRing (𝓞 F) F) :
    glFin (𝓞 F) F (unipotentGL2 X) = unipotentGL2 X.2 := by
  change Matrix.GeneralLinearGroup.map (adeleFin (𝓞 F) F) (unipotentGL2 X) = _
  rw [map_unipotentGL2]
  rfl

theorem glEquivOfRingEquiv_unipotentGL2 {A B : Type*} [NormedField A] [NormedField B]
    (e : A ≃+* B) (x : A) :
    glEquivOfRingEquiv e (unipotentGL2 x) = unipotentGL2 (e x) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [glEquivOfRingEquiv_apply_entry, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

open scoped Classical in
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion NumberField.StandardAddChar in

theorem stdAddChar_single_half (w : InfinitePlace F) (hw : w.IsReal) :
    stdAddChar F (show (AdeleRing (𝓞 F) F) from
      (Pi.single w ((ringEquivRealOfIsReal hw).symm (1 / 2)), 0)) = -1 := by
  classical
  show (adelicTraceData F).psiK _ = -1
  set x : InfiniteAdeleRing F := Pi.single w ((ringEquivRealOfIsReal hw).symm (1 / 2)) with hx
  set u : AdeleRing (𝓞 F) F := (x, 0) with hu
  have hu1 : u.1 = x := by rw [hu]
  have hu2 : u.2 = 0 := by rw [hu]
  have hxw : x w = (ringEquivRealOfIsReal hw).symm (1 / 2) := by
    rw [hx]; exact Pi.single_eq_same w _
  have hxw' : ∀ w' : InfinitePlace F, w' ≠ w → x w' = 0 := by
    intro w' h; rw [hx]; exact Pi.single_eq_of_ne h _
  have hsum : infTraceSum F x = ((1 / 2 : ℚ) : ℝ) := by
    unfold infTraceSum
    rw [Finset.sum_eq_single w]
    · rw [hxw, mult_isReal ⟨w, hw⟩]
      have hre : (extensionEmbedding w ((ringEquivRealOfIsReal hw).symm (1 / 2))).re = 1 / 2 := by
        rw [← extensionEmbeddingOfIsReal_apply hw, Complex.ofReal_re, ← ringEquivRealOfIsReal_apply,
          RingEquiv.apply_symm_apply]
      rw [hre]
      push_cast
      ring
    · intro w' _ hw'
      rw [hxw' w' hw', map_zero, Complex.zero_re, mul_zero]
    · intro h; exact absurd (Finset.mem_univ w) h
  have hinf : (adelicTraceData F).traceInf x
      = algebraMap ℚ (InfiniteAdeleRing ℚ) (1 / 2 : ℚ) := by
    show traceInfHom F x = _
    rw [traceInfHom_apply, hsum, ratArchLine_ratCast]
  have hfin : (adelicTraceData F).traceFin u.2 = 0 := by
    rw [hu2]
    exact map_zero _
  set z : AdeleRing (𝓞 ℚ) ℚ := (algebraMap ℚ (InfiniteAdeleRing ℚ) (1 / 2), 0) with hz
  have hz1 : z.1 = algebraMap ℚ (InfiniteAdeleRing ℚ) (1 / 2) := by rw [hz]
  have hz2 : z.2 = (0 : FiniteAdeleRing (𝓞 ℚ) ℚ) := by rw [hz]
  have hzpsi : psiQ z = -1 := by
    rw [psiQ_apply, hz1, hz2, psiArch_algebraMap, AddChar.map_zero_eq_one, mul_one]
    have : (2 * Real.pi * Complex.I) * (((1 / 2 : ℚ)) : ℂ) = Real.pi * Complex.I := by
      push_cast; ring
    rw [this, Complex.exp_pi_mul_I]
  have htr : (adelicTraceData F).adelicTrace u = z := by
    refine Prod.ext ?_ ?_
    · show (adelicTraceData F).traceInf u.1 = _
      rw [hinf, hz1]
    · show (adelicTraceData F).traceFin u.2 = _
      rw [hfin, hz2]
  rw [AdelicTraceData.psiK_apply, htr, hzpsi]

end ArchLevel

theorem exists_glFin_globalPoints_mul_mem_finiteLevelOne_rat
    {N : Ideal (NumberField.RingOfIntegers ℚ)} (hN : N ≠ ⊥)
    (g : Matrix.GeneralLinearGroup (Fin 2)
      (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) :
    ∃ γ : Matrix.GeneralLinearGroup (Fin 2) ℚ,
      NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ
          (AutomorphicForm.globalPoints (NumberField.RingOfIntegers ℚ) ℚ γ) * g
        ∈ NumberField.AdelicLevel.finiteLevelOne (NumberField.RingOfIntegers ℚ) ℚ N
  := by
  exact LevelCovering.exists_glFin_globalPoints_mul_mem_finiteLevelOne_rat_impl hN g

theorem diagOne_mul_archRealGLAt_unipotent_eq_and_stdAddChar_single_half
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal) (a : (AdeleRing (𝓞 K) K)ˣ) (ha : ((a : (AdeleRing (𝓞 K) K))).2 = 1) (x : ℝ) :
    diagOne a * archRealGLAt hw (unipotentGL2 x) =
        unipotentGL2 (show (AdeleRing (𝓞 K) K) from (Pi.single w (((a : (AdeleRing (𝓞 K) K))).1 w *
            (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm x), 0)) * diagOne a ∧
      NumberField.StandardAddChar.stdAddChar K
        (show (AdeleRing (𝓞 K) K) from (Pi.single w ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm (1 / 2)), 0)) = -1
  := by
  classical
  refine ⟨?_, ArchLevel.stdAddChar_single_half w hw⟩
  refine eq_of_glArch_eq_of_glFin_eq K (AutomorphicForm.ElemLR.glArch_ext fun w' => ?_) ?_
  · rw [map_mul, map_mul, map_mul, map_mul, ArchLevel.archComponent_glArch_diagOne,
      ArchLevel.archComponent_glArch_unipotentGL2]
    by_cases hww : w' = w
    · subst hww
      rw [AutomorphicForm.ElemLR.archComponent_glArch_archRealGLAt_self,
        ArchLevel.glEquivOfRingEquiv_unipotentGL2]
      refine Matrix.GeneralLinearGroup.ext fun i j => ?_
      rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
        Fin.sum_univ_two, diagOne_coe_apply, diagOne_coe_apply, diagOne_coe_apply, diagOne_coe_apply,
        unipotentGL2_coe, unipotentGL2_coe]
      simp only [Units.coe_map]
      show _ = _
      fin_cases i <;> fin_cases j
      · simp
      · simp
        exact Or.inl rfl
      · simp
      · simp
    · rw [AutomorphicForm.ElemLR.archComponent_glArch_archRealGLAt_of_ne hw hww, mul_one]
      have h0 : ((show (AdeleRing (𝓞 K) K) from (Pi.single w (((a : (AdeleRing (𝓞 K) K))).1 w *
          (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm x), 0))).1 w' = 0 := by
        show Pi.single w
          (((a : (AdeleRing (𝓞 K) K))).1 w
            * (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm x) w' = 0
        exact Pi.single_eq_of_ne hww _
      rw [h0, unipotentGL2_zero, one_mul]
  · rw [map_mul, map_mul, ArchLevel.glFin_diagOne_of_snd_eq_one a ha,
      AutomorphicForm.ElemLR.glFin_archRealGLAt, ArchLevel.glFin_unipotentGL2]
    show (1 : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) * 1 = unipotentGL2 0 * 1
    rw [unipotentGL2_zero]

theorem diagOne_eq_diagOne_mul_archRealLiftAt_mul_centralScalar
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (u : ℝ) (hu : 0 < u)
    (a b' z : (AdeleRing (𝓞 K) K)ˣ)
    (ha : ((a : (AdeleRing (𝓞 K) K))).2 = 1) (hb' : ((b' : (AdeleRing (𝓞 K) K))).2 = 1) (hz : ((z : (AdeleRing (𝓞 K) K))).2 = 1)
    (hab : ∀ w' : InfinitePlace K, w' ≠ w → ((a : (AdeleRing (𝓞 K) K))).1 w' = ((b' : (AdeleRing (𝓞 K) K))).1 w')
    (hbw : ((b' : (AdeleRing (𝓞 K) K))).1 w = 1)
    (haw : InfinitePlace.Completion.ringEquivRealOfIsReal hw (((a : (AdeleRing (𝓞 K) K))).1 w) = ε * u)
    (hzw' : ∀ w' : InfinitePlace K, w' ≠ w → ((z : (AdeleRing (𝓞 K) K))).1 w' = 1)
    (hzw : InfinitePlace.Completion.ringEquivRealOfIsReal hw (((z : (AdeleRing (𝓞 K) K))).1 w) = Real.sqrt u) :
    diagOne a = diagOne b' * archRealLiftAt hw (Matrix.of.symm !![ε * Real.sqrt u, 0; 0, (Real.sqrt u)⁻¹]) *
        centralScalar (𝓞 K) K z ∧
      archComponent K w (glArch (𝓞 K) K (diagOne b')) = 1
  := by
  have hsq : Real.sqrt u ≠ 0 := (Real.sqrt_pos.mpr hu).ne'
  have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hA : Matrix.of (Matrix.of.symm !![ε * Real.sqrt u, 0; 0, (Real.sqrt u)⁻¹]) =
      !![ε * Real.sqrt u, 0; 0, (Real.sqrt u)⁻¹] := Equiv.apply_symm_apply _ _
  have hdet : (Matrix.of (Matrix.of.symm !![ε * Real.sqrt u, 0; 0, (Real.sqrt u)⁻¹])).det ≠ 0 := by
    rw [hA, Matrix.det_fin_two_of]
    simp only [zero_mul, sub_zero]
    exact mul_ne_zero (mul_ne_zero hε0 hsq) (inv_ne_zero hsq)
  rw [archRealLiftAt_of_det_ne_zero hw hdet]
  set m : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet with hm
  have hmij : ∀ i j, (m : Matrix (Fin 2) (Fin 2) ℝ) i j
      = !![ε * Real.sqrt u, 0; 0, (Real.sqrt u)⁻¹] i j := by
    intro i j
    show (Matrix.of (Matrix.of.symm !![ε * Real.sqrt u, 0; 0, (Real.sqrt u)⁻¹])) i j = _
    rw [hA]

  have hbcomp : archComponent K w (glArch (𝓞 K) K (diagOne b')) = 1 := by
    rw [ArchLevel.archComponent_glArch_diagOne]
    have : Units.map (archEval K w).toMonoidHom (Units.map (adeleArch (𝓞 K) K).toMonoidHom b') = 1 :=
      Units.ext hbw
    rw [this, map_one]
  refine ⟨?_, hbcomp⟩
  refine eq_of_glArch_eq_of_glFin_eq K (AutomorphicForm.ElemLR.glArch_ext fun w' => ?_) ?_
  · rw [map_mul, map_mul, map_mul, map_mul]
    by_cases hww : w' = w
    · subst hww
      rw [hbcomp, one_mul, AutomorphicForm.ElemLR.archComponent_glArch_archRealGLAt_self,
        ArchLevel.archComponent_glArch_diagOne, ArchLevel.archComponent_glArch_centralScalar]
      refine Matrix.GeneralLinearGroup.ext fun i j => ?_
      rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, diagOne_coe_apply,
        glEquivOfRingEquiv_apply_entry, glEquivOfRingEquiv_apply_entry, hmij, hmij,
        ArchLevel.scalar_coe_apply, ArchLevel.scalar_coe_apply]
      simp only [Units.coe_map]
      fin_cases i <;> fin_cases j
      · show ((a : AdeleRing (𝓞 K) K)).1 w' = _
        simp
        apply (InfinitePlace.Completion.ringEquivRealOfIsReal hw).injective
        rw [haw]
        simp only [map_mul, RingEquiv.apply_symm_apply]
        rw [show (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
              ((archEval K w') ((adeleArch (𝓞 K) K) ↑z)) = Real.sqrt u from hzw,
          mul_assoc, Real.mul_self_sqrt hu.le]
      · show (0 : w'.Completion) = _
        simp
      · show (0 : w'.Completion) = _
        simp
      · show (1 : w'.Completion) = _
        simp
        apply (InfinitePlace.Completion.ringEquivRealOfIsReal hw).injective
        simp only [map_mul, map_inv₀, map_one, RingEquiv.apply_symm_apply]
        rw [show (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
              ((archEval K w') ((adeleArch (𝓞 K) K) ↑z)) = Real.sqrt u from hzw,
          inv_mul_cancel₀ hsq]
    · rw [AutomorphicForm.ElemLR.archComponent_glArch_archRealGLAt_of_ne hw hww, mul_one,
        ArchLevel.archComponent_glArch_diagOne, ArchLevel.archComponent_glArch_diagOne,
        ArchLevel.archComponent_glArch_centralScalar]
      have hz1 : Units.map (archEval K w').toMonoidHom
          (Units.map (adeleArch (𝓞 K) K).toMonoidHom z) = 1 :=
        Units.ext (hzw' w' hww)
      rw [hz1, map_one, mul_one]
      congr 1
      exact Units.ext (hab w' hww)
  · rw [map_mul, map_mul, ArchLevel.glFin_diagOne_of_snd_eq_one a ha,
      ArchLevel.glFin_diagOne_of_snd_eq_one b' hb',
      AutomorphicForm.ElemLR.glFin_archRealGLAt,
      ArchLevel.glFin_centralScalar_of_snd_eq_one z hz, one_mul, one_mul]

end NumberField.AdelicLevel

end
