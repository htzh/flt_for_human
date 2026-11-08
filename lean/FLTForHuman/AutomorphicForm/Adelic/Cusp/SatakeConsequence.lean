/-
  The Satake bound read on a genuine cusp realization: `a v ^ 2 ≠ b v · (N + 2 + N⁻¹)`.

  Over a centre-cut Siegel cover that covers the centre, a genuine smooth cusp realization `R` of the
  raw-central eigensystem `Θ.toRawCentral` has, at every place outside the level and the exceptional
  set, Hecke eigenvalues satisfying `a v ^ 2 ≠ b v · (N v + 2 + N v⁻¹)` — the level-one form of the
  Ramanujan bound, read off the Satake bound `LanglandsTunnell.satake_…` once the unitary input
  `‖b v‖ = 1` is produced from the Petersson sesquilinear form by
  `AutomorphicForm.a_mul_conj_b_…` at `s = 1`.

  This is the headline the weight-one lifting consumes: it is what makes `a v` and `b v` incompatible
  with the trivial (`b = a²`) Satake assignment at every place outside the level.

  The row is the pin's assembly over its two premises; its proof file
  `P2M/Sol/S_AutomorphicForm_SmoothCuspRealizationAt_a_sq_ne_b_mul_of_not_dvd_level_of_not_mem_exceptionalSet.lean`
  is 125 lines / 2 declarations (pinned `aa2d8b3`), its statement the wrapper
  `Theorems/Thm_AutomorphicForm_SmoothCuspRealizationAt_a_sq_ne_b_mul_of_not_dvd_level_of_not_mem_exceptionalSet.lean`.

  spec-pin: Theorems/Thm_AutomorphicForm_SmoothCuspRealizationAt_a_sq_ne_b_mul_of_not_dvd_level_of_not_mem_exceptionalSet.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_SmoothCuspRealizationAt_a_sq_ne_b_mul_of_not_dvd_level_of_not_mem_exceptionalSet.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SatakeParameters
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SatakeBound
import FLTForHuman.AutomorphicForm.Adelic.Cusp.RealizationTwist
import FLTForHuman.AutomorphicForm.Adelic.PeterssonSlabPairing
import FLTForHuman.AutomorphicForm.Adelic.DetNormSlabFundamentalDomain

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

noncomputable section

namespace AutomorphicForm

theorem SmoothCuspRealizationAt.a_sq_ne_b_mul_of_not_dvd_level_of_not_mem_exceptionalSet
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (Θ : HeckeEigensystem K ℂ)
    (R : SmoothCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.toRawCentral R) :
    ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ Θ.level → v ∉ R.exceptionalSet →
      Θ.a v ^ 2 ≠ Θ.b v * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) + 2 + ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)⁻¹) := by
  intro v hvl hve

  obtain ⟨hICC, -, hcontImp⟩ :=
    SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine K
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)
      Θ.toRawCentral R
  have hχc := hcontImp hR
  obtain ⟨s, hs⟩ := NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow K _ hICC hχc
  -- The pin's `hs' : ∀ x, ‖((R.centralChar ⟨x, mem_top x⟩ : ℂˣ) : ℂ)‖ = ideleNorm K x ^ s` is
  -- not needed: in the port `R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom x` is
  -- definitionally `R.centralChar ⟨x, Subgroup.mem_top x⟩`, so `hs` is the statement the
  -- Petersson pairing below asks for.
  have hs' := hs

  obtain ⟨S, hSs, hSfd⟩ :=
    exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc K 1 2
  obtain ⟨-, hne, hcross⟩ :=
    exists_sesqForm_eq_peterssonIntegral_of_isGenuineCuspRealizationAt_of_isFundamentalDomain K
      c u d₁ d₂ T hd hcov Θ Θ R R hR s hs' 1 2 one_pos one_lt_two S hSs hSfd
  obtain ⟨-, P, hPcov, -, hPagree⟩ := hcross rfl

  have hRmem : R.toFun ∈
      Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 K) K => fun z => R.toFun (z * h)) :=
    Submodule.subset_span ⟨1, funext fun z => by simp⟩
  have hPcov' : ∀ g : AdelicGL2 (𝓞 K) K, ∀ x y : AdelicGL2 (𝓞 K) K → ℂ,
      x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 K) K => fun z => R.toFun (z * h)) →
      y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 K) K => fun z => R.toFun (z * h)) →
      P (fun z => x (z * g)) (fun z => y (z * g)) =
        ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * P x y :=
    fun g x y hx hy => hPcov g x y (Submodule.mem_sup_left hx) hy
  have hPself : P R.toFun R.toFun ≠ 0 := by
    rw [hPagree R.toFun R.toFun (Submodule.mem_sup_left hRmem) hRmem]
    exact hne

  have hw := a_mul_conj_b_eq_and_norm_b_eq_of_sesqForm_covariant_of_ne_zero K
    (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) Θ R P s hPcov' hPself

  set t : ℝ := (1 - s) / 2 with ht
  obtain ⟨R', hR', hexc, -⟩ :=
    SmoothCuspRealizationAt.exists_twist_rpow_absNorm_exceptionalSet_eq_toFun_eq_ideleNorm_det_rpow_mul K
      c u d₁ d₂ T hd₁ Θ R hR t
  have hb' : ∀ v : HeightOneSpectrum (𝓞 K),
      ¬ v.asIdeal ∣ (Θ.twist (fun v : HeightOneSpectrum (𝓞 K) =>
        (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ))).level → v ∉ R'.exceptionalSet →
      ‖(Θ.twist (fun v : HeightOneSpectrum (𝓞 K) =>
        (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ))).b v‖ = 1 := by
    intro v hvl' hve'
    rw [hexc] at hve'
    have hvl0 : ¬ v.asIdeal ∣ Θ.level := hvl'
    have hbv : ‖Θ.b v‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (1 - s) := (hw v hve' hvl0).2
    have hN : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
      have : Ideal.absNorm v.asIdeal ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
      positivity
    simp only [HeckeEigensystem.twist_b, norm_mul, norm_pow, Complex.norm_real, hbv]
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hN.le _), ← Real.rpow_natCast, ← Real.rpow_mul hN.le,
      ← Real.rpow_add hN, ht]
    norm_num

  have hve' : v ∉ R'.exceptionalSet := by rw [hexc]; exact hve
  have hvl' : ¬ v.asIdeal ∣ (Θ.twist (fun v : HeightOneSpectrum (𝓞 K) =>
      (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ))).level := hvl
  have hgen := (LanglandsTunnell.satake_norm_lt_sqrt_absNorm_of_not_dvd_level_of_not_mem_exceptionalSet
    K c u d₁ d₂ T hc hd₁ hd hcov
    (Θ.twist (fun v : HeightOneSpectrum (𝓞 K) =>
      (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ))) R' hR' hb' v hvl' hve').1

  intro h
  apply hgen
  simp only [HeckeEigensystem.twist_a, HeckeEigensystem.twist_b]
  rw [mul_pow, h]
  ring

end AutomorphicForm
