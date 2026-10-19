/-
  Strong approximation for `GL₂` over a PID: the global profile and the headline engine.

  In a principal ideal domain every finite idèle has a *global profile*: for
  `δ : (𝔸_K^fin)ˣ` there is `α ∈ Kˣ` with both `α⁻¹ δ` and `α δ⁻¹` integral at every
  finite place (`finiteIdele_exists_global_profile`). The proof chooses a uniformizer
  `π v` at each place (`exists_primeGenerator`, using that `v.asIdeal` is principal),
  reads the place-by-place exponents of `δ` as `m v = log (v(δ v))` — the finite
  support coming from `FiniteAdeleRing.isUnit_iff` — and sets
  `a = ∏ v ∈ S, π v ^ (-(m v))`.

  `exists_ratGL_inv_mul_mem_of_finiteIdele` assembles this with the Gauss
  decomposition: the diagonal unit `detUnit g` is split as
  `ratGL (diagTorusGL2 α) * diagTorusGL2 w` with `w` integral, and the three
  `absorb_*` steps of the previous module move the unipotent factors into the
  rational point, leaving a rational `γ` with `(ratGL γ)⁻¹ * g` integral.
  `exists_map_mul_mem_finiteIntegralGL2` inverts it into the headline form
  `ratGL γ * g ∈ finiteIntegralGL2`, and `glFin_globalPoints` identifies the adèlic
  `glFin` of a global point with `ratGL γ`, which is what the rational headline needs.

  Transcribed verbatim from
  `P2M/Sol/S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:721–874`
  (the pin's `Approximation` block, pinned `aa2d8b3`). No statement is changed; the
  call sites are the previous modules'. The pin's `p2m_reactivate` lines are not
  transcribed.
-/
import FLTForHuman.NumberTheory.AdelicLevel.StrongApprox.Conjugation
import FLTForHuman.NumberTheory.AdelicLevel.StrongApprox.Gauss
import FLTForHuman.NumberTheory.AdelicLevel.Projections
import FLTForHuman.AutomorphicForm.Adelic.Basic

set_option autoImplicit false

open Matrix IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField AutomorphicForm

noncomputable section

namespace NumberField

namespace AdelicLevel

namespace GL2StrongApproxW8M

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

omit [IsFractionRing R K] in
-- The pin's `haveI` below feeds instance search (`Ideal.span_singleton_generator`).
set_option linter.style.haveILetI false in

-- pin: exists_primeGenerator (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:723)
theorem exists_primeGenerator [IsPrincipalIdealRing R] (v : HeightOneSpectrum R) :
    ∃ π : R, π ≠ 0 ∧ v.intValuation π = WithZero.exp (-1 : ℤ) ∧
      ∀ w : HeightOneSpectrum R, w ≠ v → w.intValuation π = 1 := by
  classical
  haveI := IsPrincipalIdealRing.principal v.asIdeal
  have hspan : Ideal.span {Submodule.IsPrincipal.generator v.asIdeal} = v.asIdeal :=
    Ideal.span_singleton_generator v.asIdeal
  have h0 : Submodule.IsPrincipal.generator v.asIdeal ≠ 0 := fun h ↦
    v.ne_bot (by rw [← hspan, h]; exact Ideal.span_singleton_eq_bot.mpr rfl)
  refine ⟨Submodule.IsPrincipal.generator v.asIdeal, h0,
    intValuation_singleton v h0 hspan.symm, fun w hw ↦ ?_⟩
  rw [intValuation_eq_one_iff]
  intro hmem
  apply hw
  have hle : v.asIdeal ≤ w.asIdeal := by
    rw [← hspan, Ideal.span_le, Set.singleton_subset_iff]
    exact hmem
  exact (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hle)).symm

-- pin: finiteIdele_exists_global_profile (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:742)
theorem finiteIdele_exists_global_profile [IsPrincipalIdealRing R]
    (δ : (FiniteAdeleRing R K)ˣ) :
    ∃ α : Kˣ,
      (∀ v : HeightOneSpectrum R,
        (algebraMap K (FiniteAdeleRing R K) ((α⁻¹ : Kˣ) : K)
          * (δ : FiniteAdeleRing R K)) v ∈ v.adicCompletionIntegers K) ∧
      (∀ v : HeightOneSpectrum R,
        (algebraMap K (FiniteAdeleRing R K) ((α : Kˣ) : K)
          * ((δ⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K)) v
          ∈ v.adicCompletionIntegers K) := by
  classical
  obtain ⟨hne, hev⟩ := FiniteAdeleRing.isUnit_iff.mp (Units.isUnit δ)
  have hvne : ∀ v : HeightOneSpectrum R, Valued.v ((δ : FiniteAdeleRing R K) v) ≠ 0 :=
    fun v ↦ (Valuation.ne_zero_iff _).mpr (hne v)

  choose π hπ0 hπv hπw using fun v : HeightOneSpectrum R ↦ exists_primeGenerator R v
  obtain ⟨m, hm⟩ : ∃ m : HeightOneSpectrum R → ℤ,
      ∀ v, WithZero.exp (m v) = Valued.v ((δ : FiniteAdeleRing R K) v) :=
    ⟨fun v ↦ WithZero.log (Valued.v ((δ : FiniteAdeleRing R K) v)),
      fun v ↦ WithZero.exp_log (hvne v)⟩

  obtain ⟨S, hS⟩ : ∃ S : Finset (HeightOneSpectrum R),
      ∀ w, w ∉ S → Valued.v ((δ : FiniteAdeleRing R K) w) = 1 :=
    ⟨(Filter.eventually_cofinite.mp hev).toFinset,
      fun w hw ↦ by_contra fun h ↦ hw ((Set.Finite.mem_toFinset _).mpr h)⟩
  have hπK : ∀ v, algebraMap R K (π v) ≠ 0 := fun v h ↦
    hπ0 v (IsFractionRing.injective R K (by rw [h, map_zero]))

  set a : K := ∏ v ∈ S, (algebraMap R K (π v)) ^ (-(m v)) with ha
  have ha0 : a ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ ↦ zpow_ne_zero _ (hπK v)

  have hval : ∀ w : HeightOneSpectrum R,
      w.valuation K a = Valued.v ((δ : FiniteAdeleRing R K) w) := by
    intro w
    rw [ha, map_prod]
    simp_rw [map_zpow₀]
    rw [Finset.prod_eq_single w]
    · rw [valuation_of_algebraMap, hπv w, ← WithZero.exp_zsmul, ← hm w]
      congr 1
      rw [smul_eq_mul, neg_mul_neg, mul_one]
    · intro v _ hvw
      rw [valuation_of_algebraMap, hπw v w (Ne.symm hvw), _root_.one_zpow]
    · intro hw
      have hm0 : m w = 0 := by
        have h1 := hm w
        rw [hS w hw, WithZero.exp_eq_one] at h1
        exact h1
      rw [hm0, neg_zero, zpow_zero]
  refine ⟨Units.mk0 a ha0, fun v ↦ ?_, fun v ↦ ?_⟩
  · rw [coe_mul_apply, mem_adicCompletionIntegers, Valuation.map_mul,
      valued_algebraMap_finiteAdeleRing_apply, Units.val_inv_eq_inv_val, Units.val_mk0,
      map_inv₀, hval v]
    exact le_of_eq (inv_mul_cancel₀ (hvne v))
  · have hprod : (δ : FiniteAdeleRing R K) v
        * ((δ⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v = 1 := by
      rw [← coe_mul_apply, Units.mul_inv, coe_one_apply]
    rw [coe_mul_apply, mem_adicCompletionIntegers, Valuation.map_mul,
      valued_algebraMap_finiteAdeleRing_apply, Units.val_mk0, hval v]
    exact le_of_eq (by rw [← Valuation.map_mul, hprod, Valuation.map_one])

-- pin: exists_ratGL_inv_mul_mem_of_finiteIdele (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:802)
theorem exists_ratGL_inv_mul_mem_of_finiteIdele
    (hcn : ∀ δ : (FiniteAdeleRing R K)ˣ, ∃ α : Kˣ,
      (∀ v : HeightOneSpectrum R,
        (algebraMap K (FiniteAdeleRing R K) ((α⁻¹ : Kˣ) : K)
          * (δ : FiniteAdeleRing R K)) v ∈ v.adicCompletionIntegers K) ∧
      (∀ v : HeightOneSpectrum R,
        (algebraMap K (FiniteAdeleRing R K) ((α : Kˣ) : K)
          * ((δ⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K)) v
          ∈ v.adicCompletionIntegers K))
    (g : GL (Fin 2) (FiniteAdeleRing R K)) :
    ∃ γ : GL (Fin 2) K, (ratGL R K γ)⁻¹ * g ∈ finiteIntegralGL2 R K := by
  obtain ⟨t, x, z, cu, htint, hg⟩ := exists_gauss_decomposition R K g
  obtain ⟨α, hα₁, hα₂⟩ := hcn (detUnit R K g)

  set w : (FiniteAdeleRing R K)ˣ :=
    (Units.map (algebraMap K (FiniteAdeleRing R K) : K →* FiniteAdeleRing R K) α)⁻¹
      * detUnit R K g with hw
  have hmapinv :
      (Units.map (algebraMap K (FiniteAdeleRing R K) : K →* FiniteAdeleRing R K) α)⁻¹
        = Units.map (algebraMap K (FiniteAdeleRing R K) : K →* FiniteAdeleRing R K) α⁻¹ :=
    (map_inv (Units.map (algebraMap K (FiniteAdeleRing R K) : K →* FiniteAdeleRing R K)) α).symm
  have hwval : (w : FiniteAdeleRing R K)
      = algebraMap K (FiniteAdeleRing R K) ((α⁻¹ : Kˣ) : K)
        * (detUnit R K g : FiniteAdeleRing R K) := by
    rw [hw, hmapinv, Units.val_mul, Units.coe_map]; rfl
  have hwinvval : ((w⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K)
      = algebraMap K (FiniteAdeleRing R K) ((α : Kˣ) : K)
        * (((detUnit R K g)⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) := by
    rw [hw, _root_.mul_inv_rev, inv_inv, Units.val_mul, mul_comm, Units.coe_map]; rfl
  have hwmem : diagTorusGL2 w ∈ finiteIntegralGL2 R K :=
    diagTorusGL2_mem R K (fun v ↦ by rw [hwval]; exact hα₁ v)
      (fun v ↦ by rw [hwinvval]; exact hα₂ v)

  have hδsplit : diagTorusGL2 (detUnit R K g) = ratGL R K (diagTorusGL2 α) * diagTorusGL2 w := by
    rw [show ratGL R K (diagTorusGL2 α) = diagTorusGL2
        (Units.map (algebraMap K (FiniteAdeleRing R K) : K →* FiniteAdeleRing R K) α) from
      map_diagTorusGL2 _ _, ← diagTorusGL2_mul, hw]
    congr 1
    group
  have hbase : (ratGL R K (diagTorusGL2 α))⁻¹
      * (diagTorusGL2 (detUnit R K g) * lowerUnipGL2 (-t)) ∈ finiteIntegralGL2 R K := by
    have heq : (ratGL R K (diagTorusGL2 α))⁻¹
        * (diagTorusGL2 (detUnit R K g) * lowerUnipGL2 (-t))
        = diagTorusGL2 w * lowerUnipGL2 (-t) := by
      rw [hδsplit]; group
    rw [heq]
    refine mul_mem hwmem (lowerUnipGL2_mem R K fun v ↦ ?_)
    rw [coe_neg_apply]
    exact neg_mem (htint v)

  obtain ⟨q₁, hq₁⟩ := absorb_unipotent_left R K hbase z
  obtain ⟨q₂, hq₂⟩ := absorb_lowerUnip_left R K hq₁ (cu : FiniteAdeleRing R K)
  obtain ⟨q₃, hq₃⟩ := absorb_unipotent_left R K hq₂ x
  refine ⟨unipotentGL2 q₃ * (lowerUnipGL2 q₂ * (unipotentGL2 q₁ * diagTorusGL2 α)), ?_⟩
  rw [hg]
  exact hq₃

-- pin: exists_map_mul_mem_finiteIntegralGL2 (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:859)
theorem exists_map_mul_mem_finiteIntegralGL2 [IsPrincipalIdealRing R]
    (g : GL (Fin 2) (FiniteAdeleRing R K)) :
    ∃ γ : GL (Fin 2) K,
      GeneralLinearGroup.map (algebraMap K (FiniteAdeleRing R K)) γ * g
        ∈ finiteIntegralGL2 R K := by
  obtain ⟨γ, hγ⟩ := exists_ratGL_inv_mul_mem_of_finiteIdele R K
    (finiteIdele_exists_global_profile R K) g
  refine ⟨γ⁻¹, ?_⟩
  rw [map_inv]
  exact hγ

-- pin: glFin_globalPoints (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:870)
theorem glFin_globalPoints (γ : GL (Fin 2) K) :
    glFin R K (globalPoints R K γ)
      = GeneralLinearGroup.map (algebraMap K (FiniteAdeleRing R K)) γ := by
  ext i j
  rfl

end GL2StrongApproxW8M

end AdelicLevel

end NumberField
