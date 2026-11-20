/-
  The Nebentypus of the weight-one lift: the finite-level row.

  On a finite-level element (`finiteLevelZero (ratLevel N)`) the lift of a right translate is the
  inverse of the Nebentypus character times the lift, so the lift of a `Γ₁(N)`-form is an
  eigenfunction of the finite-level action with the Nebentypus eigenvalue.

  Transcribed from
  `P2M/Sol/S_DihedralWeightOne_weightOneLift_mul_finEmbed_eq_inv_nebentypus_mul_of_mem_finiteLevelZero.lean`
  (436 lines / 29 declarations), the one row of that pin. The shared prelude of the Nebentypus /
  q-expansion pins lives in `WeightOneLiftLevel`; the declarations this module carries are the
  ones only this pin has, at the pin's names, statements and qualification (all public — the pin
  spells none of them `private`).

  The second pin of the original order,
  `P2M/Sol/S_DihedralWeightOne_exists_hasNebentypus_eq_weightOneLift_of_mem_span_of_apply_mul_finEmbed_eq_inv_mul.lean`,
  is **not** ported here: its engine is built on `LocalNewvector.AdelicSpan` /
  `AdelicSpanSubmodule` / `AdelicFnCarrier` / `HasReading` from
  `Definitions/Def_LocalNewvector_AdelicSpanCarrier.lean`, which the port does not have (a
  definition gate, FR-0049). See `## Deferred pin surface` below.

  spec-pin: P2M/Sol/S_DihedralWeightOne_weightOneLift_mul_finEmbed_eq_inv_nebentypus_mul_of_mem_finiteLevelZero.lean

  ## Port deltas

  * Added `local notation "Int𝔸" => integralFiniteAdeles (𝓞 ℚ) ℚ` beside the pin's `Ball` at the
    head of the `BallLemmas` section (pin `:296`–`:297`). Without it `mul_sub_mul_mem` (pin
    `:311`) reports `unknown identifier Int𝔸` under `autoImplicit false`. The notation is part of
    the *statement* text — the checker does not expand `local notation` (FR-0224 trap 3) — so the
    statement keeps `Int𝔸` and the fix is the notation line, not a re-spelling.
  * Added `import FLTForHuman.LanglandsTunnell.WeightOneLiftGlobalPoints`:
    `apply_decomp₁` (pin `:200`) invokes
    `weightOneLift_globalPoints_mul_and_mul_finEmbed_and_eq_weightOneArchLift`
    (`WeightOneLiftGlobalPoints:56`), and `WeightOneLiftLevel` does not import that module
    (FR-0229: a `sorry` body never calls its premises, so the scaffold's green elaboration could
    not have shown this).
  * The second wire line of the scaffold (the deferred row's `spec-pin`) was **removed**, because the
    module no longer transcribes that pin and `scaffold_audit.py` reads every wired pin as surface
    this module must carry (that pin's one public declaration outside the deferred row,
    `exists_gamma1_cuspForm_coe_eq` at pin `:634`, would report `MISSING`). The deferred pin is
    named in full in `## Deferred pin surface` instead. The first pin's line is unchanged.
  * Namespace mapping and staging as in `WeightOneLiftLevel`: the pin's search-stage namespaces
    (`WeightOneLevelZero`, `BallLemmas`) are dropped, the pin's `p2m_export`/`p2m_open` staging
    lines have no counterpart, and the declarations sit at `DihedralWeightOne`. All declaration
    names and statements are the pin's.

  Proof-side (statement-neutral) edits against the pin, all in bodies, all forced by v4.34:

  * `exists_algebraMap_eq_of_mem_integralFiniteAdeles`: the pin's
    `HeightOneSpectrum.exists_algebraMap_eq_of_valuation_le_one` no longer exists; the body is the
    one `LanglandsTunnell/WeightOneLiftAdelic.lean` already carries for the same statement
    (`HeightOneSpectrum.mem_integers_of_valuation_le_one` plus the `rfl` identification
    `(algebraMap K (FiniteAdeleRing R K) q) v = ((q : K) : v.adicCompletion K)` closed by
    `HeightOneSpectrum.valuedAdicCompletion_eq_valuation'`).
  * `exists_intCast_eq_of_mem_integralFiniteAdeles`: ends at `Rat.ringOfIntegersEquiv r` (the pin's
    bare `⟨r, …⟩` no longer typechecks, `r : 𝓞 ℚ`).
  * `exists_mapGL_eq_of_mem_finiteIntegralGL2`: the pin's
    `rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]` is dropped — `SpecialLinearGroup.mapGL` is a
    `def` and the rewrite fails at the implicit transparency level (FR-0245, the same site and the
    same fix as in `WeightOneLiftAdelic`).
  * `lowerRight_mul_sub_mem`: the pin's `add_sub_cancel_right` is gone from v4.34's core; the
    2×2 entry computation is closed by a local `have … := by rw [Matrix.mul_apply,
    Fin.sum_univ_two]; ring`.
  * `slash_eq_nebentypus_smul`: v4.34's `CuspForm.HasNebentypus` spells its character value
    `ε (ModularForm.Level.dd (N := M) γ)`, so one `show … = ((γ 1 1 : ℤ) : ZMod M) from rfl` is
    inserted before the pin's `field_simp` (the two are definitionally equal).
  * `weightOneArchLift_coe_mul`: `if_pos` → `ite_eq_left` (v4.34 deprecation).
  * `natCast_dvd_of_mem_idealBall`: `haveI : Fact p.Prime` → `have : Fact p.Prime` — the
    `linter.style.haveILetI` suggestion is *right* at this site (Lean 4.34 does put a local
    `have` of class type into the instance table), and the module elaborates with no linter
    `set_option` of its own. Only the pin's `p2m` staging lines and the namespace shell differ.

  Surface: **19 declarations, all public** (pin 1 spells none of them `private`, so the
  scaffold's "row-local `private` declarations" does not apply to this pin — FR-0224 keeps the
  pin's own qualification), 506 lines.

  ## Deferred pin surface

  The pin
  `P2M/Sol/S_DihedralWeightOne_exists_hasNebentypus_eq_weightOneLift_of_mem_span_of_apply_mul_finEmbed_eq_inv_mul.lean`
  (854 lines / 72 declarations) is deferred whole; reason: `AdelicSpan` unported. Its row is
  `exists_hasNebentypus_eq_weightOneLift_of_mem_span_of_apply_mul_finEmbed_eq_inv_mul`
  (pin `:776`–`:854`). Its shared prelude (the `ratArch`/`archPart` block, the
  `natGenerator`/`idealBound` block, the `glFin_globalPoints_mapGL` block,
  `continuous_denom`/`continuous_slash`/`dense_ratPoints`/`exists_glFin_eq_one_and_smul_I_eq`) is
  ported in `WeightOneLiftLevel`; the declarations that were scaffolded here and are now dropped
  with the row are, by pin range:

  * `slashSpan`, `slash_map_mem_slashSpan`, `HasReading`, `weightOneArchLift_zero'`,
    `weightOneArchLift_add'`, `weightOneArchLift_smul'`, `weightOneArchLift_mul'`,
    `hasReading_zero`, `HasReading.add`, `HasReading.smul`, `glFin_conj_eq_one`
    (pin `:168`–`:217`) — `slashSpan` itself is `AdelicSpan`-free, but `HasReading` and every
    consumer of it are not;
  * `exists_hasReading_finEmbed_smul_self`, `exists_hasReading_of_mem_span` (pin `:219`–`:282`);
  * `continuous_of_mem_slashSpan` (pin `:307`–`:314`) and `eq_of_forall_weightOneArchLift_eq`
    (pin `:364`–`:382`) — they only serve `HasReading`'s two existence lemmas;
  * the `fn` carrier block: `fn`, `fn_smul_self`, `fn_add`, `fn_csmul`, `fn_zero`, `hasReading_iff`
    (pin `:514`–`:531`) — `fn` *is* `(AdelicSpan.toFn φ y).toFn`;
  * the `GammaOneCuspAux` block `isCusp_SL2Z_map_smul`, `isCusp_SL2Z_of_isCusp_map`,
    `isZeroAt_slash_map`, `isZeroAt_sum`, `mdifferentiable_sum`, `exists_gamma1_cuspForm_coe_eq`
    (pin `:587`–`:652`) — only the deferred row's final assembly uses them;
  * the `NebentypusDescent` block `exists_eq_sum_of_mem_slashSpan'`,
    `fn_globalPoints_mul_of_mem_span`, `fn_mul_finEmbed_of_mem_finiteLevelOne`,
    `slash_eq_inv_smul`, `eq_zero_of_hasReading_zero'`, `isCoprime_and_mul_eq_one`
    (pin `:664`–`:770`).

  Reviving them is one `import` of a ported `Def_LocalNewvector_AdelicSpanCarrier` away; nothing of
  the mathematics of this module's own row depends on them.

  ## Heartbeat probe

  Not installed (FR-0225). Measured on landing, project cap 4,000,000: the module is silent at
  `-DmaxHeartbeats=16000` and fails at `-DmaxHeartbeats=8000` (= N/2, `deterministic timeout at
  isDefEq` first at `lowerRight_mul_sub_mem`). It is a cheap module — the whole file re-elaborates
  in seconds — so the margin is reported and no floor is set.
-/


import FLTForHuman.LanglandsTunnell.WeightOneLiftLevel
import FLTForHuman.LanglandsTunnell.WeightOneLiftAdelic
import FLTForHuman.LanglandsTunnell.WeightOneLiftGlobalPoints

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm UpperHalfPlane
open UpperHalfPlane Matrix
open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel Matrix
open Matrix Matrix.GeneralLinearGroup
open CongruenceSubgroup ModularGroup
open AdelicDock
open NumberField.AdelicHaar
open HeckeIntegralSeam HeckePair
open AutomorphicForm.SmoothCusp IsDedekindDomain.HeightOneSpectrum
open LanglandsTunnell.RatArch

open NumberField.AdelicLevel AutomorphicForm.WindowedSiegel NumberField.AdelicVolume
open MeasureTheory
open scoped Topology Manifold
open DihedralWeightOne


namespace DihedralWeightOne



theorem ratArch_globalPoints_mapGL (ε : SL(2, ℤ)) :
    LanglandsTunnell.ratArchGL2 (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ ε)) =
      (ε : GL (Fin 2) ℝ) := by
  rw [ratArch_globalPoints]
  exact Matrix.SpecialLinearGroup.map_mapGL (S := ℚ) (T := ℝ) ε

theorem det_ratArch_globalPoints (γ : GL (Fin 2) ℚ) :
    ((LanglandsTunnell.ratArchGL2 (globalPoints (𝓞 ℚ) ℚ γ)).det.val : ℝ) =
      (((GeneralLinearGroup.det γ : ℚˣ) : ℚ) : ℝ) := by
  rw [ratArch_globalPoints, GeneralLinearGroup.map_det, Units.coe_map, MonoidHom.coe_coe, eq_ratCast]

theorem exists_algebraMap_eq_of_mem_integralFiniteAdeles {R : Type*} [CommRing R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {q : K}
    (hq : algebraMap K (FiniteAdeleRing R K) q ∈ integralFiniteAdeles R K) :
    ∃ r : R, algebraMap R K r = q := by
  have h : ∀ v : HeightOneSpectrum R, v.valuation K q ≤ 1 := fun v => by
    have h1 := hq v
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      show (algebraMap K (FiniteAdeleRing R K) q) v = ((q : K) : v.adicCompletion K) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h1
    exact h1
  exact HeightOneSpectrum.mem_integers_of_valuation_le_one K q h

theorem exists_intCast_eq_of_mem_integralFiniteAdeles {q : ℚ}
    (hq : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q ∈ integralFiniteAdeles (𝓞 ℚ) ℚ) :
    ∃ n : ℤ, (n : ℚ) = q := by
  obtain ⟨r, hr⟩ := exists_algebraMap_eq_of_mem_integralFiniteAdeles hq
  exact ⟨Rat.ringOfIntegersEquiv r, by rw [← hr, Rat.ringOfIntegersEquiv_apply_coe]⟩

theorem exists_mapGL_eq_of_mem_finiteIntegralGL2 {γ : GL (Fin 2) ℚ}
    (hint : glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ)
    (hpos : 0 < ((Matrix.GeneralLinearGroup.det γ : ℚˣ) : ℚ)) :
    ∃ δ : SL(2, ℤ), Matrix.SpecialLinearGroup.mapGL ℚ δ = γ := by
  rw [mem_finiteIntegralGL2_iff] at hint
  obtain ⟨hγ, hγinv⟩ := hint
  have hγ' : ∀ i j, ∃ n : ℤ, (n : ℚ) = (γ : Matrix (Fin 2) (Fin 2) ℚ) i j := fun i j =>
    exists_intCast_eq_of_mem_integralFiniteAdeles (by rw [← glFin_globalPoints_apply]; exact hγ i j)
  have hγinv' : ∀ i j, ∃ n : ℤ, (n : ℚ) = ((γ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) i j :=
    fun i j => exists_intCast_eq_of_mem_integralFiniteAdeles (by
      rw [← glFin_globalPoints_apply, map_inv, map_inv]; exact hγinv i j)
  choose a ha using hγ'
  choose b hb using hγinv'
  set A : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of fun i j => a i j with hA
  set B : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of fun i j => b i j with hB
  have hAmap : A.map (Int.castRingHom ℚ) = (γ : Matrix (Fin 2) (Fin 2) ℚ) := by
    ext i j; simp [hA, ha]
  have hBmap : B.map (Int.castRingHom ℚ) = ((γ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) := by
    ext i j; simp [hB, hb]
  have hAB : A * B = 1 := by
    have hinj : Function.Injective fun M : Matrix (Fin 2) (Fin 2) ℤ => M.map (Int.castRingHom ℚ) :=
      Matrix.map_injective (f := ⇑(Int.castRingHom ℚ)) Int.cast_injective
    apply hinj
    dsimp only
    rw [Matrix.map_mul, hAmap, hBmap, Matrix.map_one _ (map_zero _) (map_one _),
      ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hdetAB : A.det * B.det = 1 := by rw [← Matrix.det_mul, hAB, Matrix.det_one]
  have hdetQ : ((A.det : ℤ) : ℚ) = ((Matrix.GeneralLinearGroup.det γ : ℚˣ) : ℚ) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, ← hAmap]
    exact (RingHom.map_det (Int.castRingHom ℚ) A)
  have hdetA : A.det = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hdetAB with h1 | h1
    · exact h1
    · exfalso
      rw [← hdetQ, h1] at hpos
      norm_num at hpos
  refine ⟨⟨A, hdetA⟩, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change (algebraMap ℤ ℚ) (A i j) = _
  rw [← hAmap, Matrix.map_apply]
  rfl

theorem pow_factorization_dvd_of_valued_le_idealBound {M : ℕ} (hM : M ≠ 0) (n : ℤ) (p : ℕ) [Fact p.Prime]
    (h : Valued.v ((algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (n : ℚ)) (AdelicDock.padicPlace p)) ≤
      idealBound (𝓞 ℚ) (AdelicDock.ratLevel M) (AdelicDock.padicPlace p)) :
    ((p : ℤ) ^ M.factorization p) ∣ n := by
  have hL : (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (n : ℚ)) (AdelicDock.padicPlace p) =
      (n : (AdelicDock.padicPlace p).adicCompletion ℚ) := by
    change ((algebraMap ℚ ((AdelicDock.padicPlace p).adicCompletion ℚ)).comp (Int.castRingHom ℚ)) n = _
    exact eq_intCast _ n
  have hR : AdelicDock.padicRingEquiv p ((n : ℤ_[p]) : ℚ_[p]) = (n : (AdelicDock.padicPlace p).adicCompletion ℚ) := by
    rw [PadicInt.coe_intCast, map_intCast]
  have hcoe : (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (n : ℚ)) (AdelicDock.padicPlace p) =
      AdelicDock.padicRingEquiv p ((n : ℤ_[p]) : ℚ_[p]) := hL.trans hR.symm
  rw [hcoe, AdelicDock.valued_coe_le_idealBound_iff p hM] at h
  rw [← PadicInt.norm_int_le_pow_iff_dvd]
  exact (PadicInt.norm_le_pow_iff_mem_span_pow _ _).mpr h

theorem natCast_dvd_of_mem_idealBall {M : ℕ} (hM : M ≠ 0) (n : ℤ)
    (h : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (n : ℚ) ∈ idealBall (𝓞 ℚ) ℚ (AdelicDock.ratLevel M)) :
    (M : ℤ) ∣ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact dvd_zero _
  rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast, ← Nat.factorization_prime_le_iff_dvd hM (Int.natAbs_ne_zero.mpr hn)]
  intro p hp
  have : Fact p.Prime := ⟨hp⟩
  have hdvd : ((p : ℤ) ^ M.factorization p) ∣ n :=
    pow_factorization_dvd_of_valued_le_idealBound hM n p (h (AdelicDock.padicPlace p))
  have hdvd' : p ^ M.factorization p ∣ n.natAbs := by
    rw [← Int.natCast_dvd_natCast, Int.dvd_natAbs]; exact_mod_cast hdvd
  exact (hp.pow_dvd_iff_le_factorization (Int.natAbs_ne_zero.mpr hn)).mp hdvd'

section

variable {M : ℕ}

theorem slash_eq (f : CuspForm (CongruenceSubgroup.Gamma1 M) 1) (ε : SL(2, ℤ))
    (hε : ε ∈ CongruenceSubgroup.Gamma1 M) :
    (⇑f) ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = ⇑f :=
  SlashInvariantForm.slash_action_eqn f (ε : GL (Fin 2) ℝ) ⟨ε, hε, rfl⟩

theorem apply_decomp₁ (hM : M ≠ 0) (f : CuspForm (CongruenceSubgroup.Gamma1 M) 1)
    {γ : GL (Fin 2) ℚ} {h : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    {k : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hh : glFin (𝓞 ℚ) ℚ h = 1)
    (hpos : LanglandsTunnell.ratArchGL2 h ∈ GLPos (Fin 2) ℝ)
    (hk : k ∈ finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel M)) :
    DihedralWeightOne.weightOneLift (Ideal.span {(M : 𝓞 ℚ)}) (⇑f)
        (globalPoints (𝓞 ℚ) ℚ γ * h * AdelicDock.finEmbed (𝓞 ℚ) ℚ k)
      = DihedralWeightOne.weightOneArchLift (⇑f) (LanglandsTunnell.ratArchGL2 h) := by
  obtain ⟨hleft, hlev, harch⟩ :=
    DihedralWeightOne.weightOneLift_globalPoints_mul_and_mul_finEmbed_and_eq_weightOneArchLift hM (⇑f)
      (slash_eq f)
  rw [mul_assoc, hleft, hlev k hk, harch h hh hpos]

theorem slash_eq_nebentypus_smul {ε : DirichletCharacter ℂ M} {f : CuspForm (CongruenceSubgroup.Gamma1 M) 1}
    (hε : CuspForm.HasNebentypus ε f) {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) :
    (⇑f) ∣[(1 : ℤ)] (γ : GL (Fin 2) ℝ) = ε ((γ 1 1 : ℤ) : ZMod M) • (⇑f) := by
  ext τ
  rw [← ModularForm.SL_slash, ModularForm.SL_slash_apply, hε γ hγ τ, Pi.smul_apply, smul_eq_mul]
  rw [show ModularForm.Level.dd (N := M) γ = ((γ 1 1 : ℤ) : ZMod M) from rfl]
  have hd : UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) τ = ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) := by
    simp [UpperHalfPlane.denom]
  have hd0 : UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) τ ≠ 0 := UpperHalfPlane.denom_ne_zero _ τ
  rw [hd] at hd0 ⊢
  rw [_root_.zpow_neg, zpow_one]
  field_simp

theorem weightOneArchLift_coe_mul {ε : DirichletCharacter ℂ M} {f : CuspForm (CongruenceSubgroup.Gamma1 M) 1}
    (hε : CuspForm.HasNebentypus ε f) {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 M)
    {g : GL (Fin 2) ℝ} (hg : 0 < (g.det.val : ℝ)) :
    DihedralWeightOne.weightOneArchLift (⇑f) ((γ : GL (Fin 2) ℝ) * g)
      = ε ((γ 1 1 : ℤ) : ZMod M) * DihedralWeightOne.weightOneArchLift (⇑f) g := by
  have hdet : (((γ : GL (Fin 2) ℝ) * g).det.val : ℝ) = (g.det.val : ℝ) := by
    rw [map_mul, Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply]
    have : ((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
      rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.det_coe]
    rw [this, one_mul]
  unfold DihedralWeightOne.weightOneArchLift
  rw [hdet, SlashAction.slash_mul, slash_eq_nebentypus_smul hε hγ, ModularForm.smul_slash, UpperHalfPlane.σ,
    ite_eq_left hg, Pi.smul_apply, smul_eq_mul, mul_assoc]
  rfl

theorem exists_sl_of_levelZero (hM : M ≠ 0)
    {γ γ' : GL (Fin 2) ℚ} {h h' : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} {u u' : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hu : u ∈ finiteLevelZero (𝓞 ℚ) ℚ (AdelicDock.ratLevel M)) (hh : glFin (𝓞 ℚ) ℚ h = 1)
    (hpos : LanglandsTunnell.ratArchGL2 h ∈ GLPos (Fin 2) ℝ)
    (hu' : u' ∈ finiteLevelZero (𝓞 ℚ) ℚ (AdelicDock.ratLevel M)) (hh' : glFin (𝓞 ℚ) ℚ h' = 1)
    (hpos' : LanglandsTunnell.ratArchGL2 h' ∈ GLPos (Fin 2) ℝ)
    (hx : globalPoints (𝓞 ℚ) ℚ γ * h * AdelicDock.finEmbed (𝓞 ℚ) ℚ u =
      globalPoints (𝓞 ℚ) ℚ γ' * h' * AdelicDock.finEmbed (𝓞 ℚ) ℚ u') :
    ∃ ε₀ : SL(2, ℤ), ε₀ ∈ CongruenceSubgroup.Gamma0 M ∧
      LanglandsTunnell.ratArchGL2 h' = (ε₀ : GL (Fin 2) ℝ) * LanglandsTunnell.ratArchGL2 h ∧
      glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ ε₀)) = u' * u⁻¹ := by
  set P := globalPoints (𝓞 ℚ) ℚ with hP
  set E := AdelicDock.finEmbed (𝓞 ℚ) ℚ with hE
  set δ : GL (Fin 2) ℚ := γ'⁻¹ * γ with hδ
  have hquot : P δ = h' * E u' * (E u)⁻¹ * h⁻¹ := by
    have Eq : P γ * (h * E u) = P γ' * (h' * E u') := by rw [← mul_assoc, ← mul_assoc, hx]
    rw [hδ, map_mul, map_inv]
    have : P γ = P γ' * (h' * E u') * (h * E u)⁻¹ := eq_mul_inv_of_mul_eq Eq
    rw [this, _root_.mul_inv_rev]
    group
  have hfinq : glFin (𝓞 ℚ) ℚ (P δ) = u' * u⁻¹ := by
    rw [hquot, map_mul, map_mul, map_mul, map_inv, map_inv, hh, hh', hE, AdelicDock.glFin_finEmbed,
      AdelicDock.glFin_finEmbed, one_mul, inv_one, mul_one]
  have hK0 : glFin (𝓞 ℚ) ℚ (P δ) ∈ finiteLevelZero (𝓞 ℚ) ℚ (AdelicDock.ratLevel M) := by
    rw [hfinq]; exact Subgroup.mul_mem _ hu' (Subgroup.inv_mem _ hu)
  have hint : glFin (𝓞 ℚ) ℚ (P δ) ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ :=
    (mem_finiteIntegralGL2_iff).mpr ⟨hK0.1.integral, hK0.2.integral⟩
  have harch : LanglandsTunnell.ratArchGL2 (P δ) =
      LanglandsTunnell.ratArchGL2 h' * (LanglandsTunnell.ratArchGL2 h)⁻¹ := by
    rw [hquot, ratArch_mul, ratArch_mul, ratArch_mul, ratArch_inv, ratArch_inv, hE, ratArch_finEmbed,
      ratArch_finEmbed, inv_one, mul_one, mul_one]
  have hdetpos : 0 < ((GeneralLinearGroup.det δ : ℚˣ) : ℚ) := by
    have h1 : 0 < ((LanglandsTunnell.ratArchGL2 (P δ)).det.val : ℝ) := by
      rw [harch, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
      exact mul_pos hpos' (inv_pos.mpr hpos)
    rw [det_ratArch_globalPoints] at h1
    exact_mod_cast h1
  obtain ⟨ε₀, hε₀⟩ := exists_mapGL_eq_of_mem_finiteIntegralGL2 hint hdetpos
  have hε0 : ε₀ ∈ CongruenceSubgroup.Gamma0 M := by
    rw [CongruenceSubgroup.Gamma0_mem]
    have hll : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (((ε₀ 1 0 : ℤ) : ℚ)) ∈
        idealBall (𝓞 ℚ) ℚ (AdelicDock.ratLevel M) := by
      have := hK0.1.lowerLeft
      rw [← hε₀] at this
      rw [show (((ε₀ 1 0 : ℤ) : ℚ)) =
            ((Matrix.SpecialLinearGroup.mapGL ℚ ε₀ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 0
          by rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]; rfl, ← glFin_globalPoints_apply]
      exact this
    have hdvd := natCast_dvd_of_mem_idealBall hM _ hll
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mpr hdvd
  refine ⟨ε₀, hε0, ?_, ?_⟩
  · rw [← ratArch_globalPoints_mapGL, hε₀, harch, inv_mul_cancel_right]
  · rw [hε₀, hfinq]

end

section

variable {M : ℕ}
variable {N : Ideal (𝓞 ℚ)}

local notation "Ball" => idealBall (𝓞 ℚ) ℚ N
local notation "Int𝔸" => integralFiniteAdeles (𝓞 ℚ) ℚ

theorem neg_mem_idealBall {x : FiniteAdeleRing (𝓞 ℚ) ℚ} (hx : x ∈ Ball) : -x ∈ Ball := fun v => by
  rw [show (-x) v = -(x v) from rfl, Valuation.map_neg]; exact hx v

theorem sub_mem_idealBall {x y : FiniteAdeleRing (𝓞 ℚ) ℚ} (hx : x ∈ Ball) (hy : y ∈ Ball) : x - y ∈ Ball := by
  rw [sub_eq_add_neg]; exact add_mem_idealBall hx (neg_mem_idealBall hy)

theorem lowerRight_mul_sub_mem {X Y : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hX : IsLevelZeroMatrix (𝓞 ℚ) ℚ N X) (hY : IsLevelZeroMatrix (𝓞 ℚ) ℚ N Y) :
    (X * Y) 1 1 - X 1 1 * Y 1 1 ∈ Ball := by
  have h : (X * Y) 1 1 - X 1 1 * Y 1 1 = X 1 0 * Y 0 1 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]; ring
  rw [h]
  exact mul_mem_idealBall_right hX.lowerLeft (hY.integral 0 1)

theorem mul_sub_mul_mem {a a' b b' : FiniteAdeleRing (𝓞 ℚ) ℚ} (ha : a - a' ∈ Ball) (hb : b - b' ∈ Ball)
    (ha' : a' ∈ Int𝔸) (hbI : b ∈ Int𝔸) : a * b - a' * b' ∈ Ball := by
  have : a * b - a' * b' = (a - a') * b + a' * (b - b') := by ring
  rw [this]
  exact add_mem_idealBall (mul_mem_idealBall_right ha hbI) (mul_mem_idealBall_left ha' hb)

end

section

variable {M : ℕ}

theorem algebraMap_mul_lowerRight_sub_one_mem {N : Ideal (𝓞 ℚ)}
    {k k' u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hk : k ∈ finiteLevelOne (𝓞 ℚ) ℚ N) (hk' : k' ∈ finiteLevelOne (𝓞 ℚ) ℚ N)
    (hu : u ∈ finiteLevelZero (𝓞 ℚ) ℚ N) (d : ℚ) (hdI : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) d ∈ integralFiniteAdeles (𝓞 ℚ) ℚ)
    (hd : (u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 - algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) d
      ∈ idealBall (𝓞 ℚ) ℚ N) :
    algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) d *
        ((k' * (k * u)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
      - 1 ∈ idealBall (𝓞 ℚ) ℚ N := by
  set A := algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) d with hA

  have hK' : IsLevelOneMatrix (𝓞 ℚ) ℚ N (k' : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := hk'.1
  have hKi : IsLevelOneMatrix (𝓞 ℚ) ℚ N ((k⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := hk.2
  have hUi : IsLevelZeroMatrix (𝓞 ℚ) ℚ N ((u⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := hu.2
  have hU : IsLevelZeroMatrix (𝓞 ℚ) ℚ N (u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := hu.1

  have hut : (u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 * ((u⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 - 1
      ∈ idealBall (𝓞 ℚ) ℚ N := by
    have h1 := lowerRight_mul_sub_mem hU hUi
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq] at h1

    have := neg_mem_idealBall h1
    rwa [neg_sub] at this

  have hdt : A * ((u⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 - 1 ∈ idealBall (𝓞 ℚ) ℚ N := by
    have h2 : A * ((u⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
        - (u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 * ((u⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
        ∈ idealBall (𝓞 ℚ) ℚ N := by
      rw [← sub_mul]
      exact mul_mem_idealBall_right (by have := neg_mem_idealBall hd; rwa [neg_sub] at this) (hUi.integral 1 1)
    have := add_mem_idealBall h2 hut
    rwa [sub_add_sub_cancel] at this

  have hm1 := lowerRight_mul_sub_mem hK'.toIsLevelZeroMatrix (Subgroup.inv_mem _ (Subgroup.mul_mem _ (finiteLevelOne_le_finiteLevelZero _ _ _ hk) hu)).1

  rw [← Units.val_mul] at hm1
  have hm2 := lowerRight_mul_sub_mem hUi hKi.toIsLevelZeroMatrix
  rw [← Units.val_mul, ← _root_.mul_inv_rev] at hm2

  have hk'1 : (k' : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 - 1 ∈ idealBall (𝓞 ℚ) ℚ N := hK'.lowerRight
  have hki1 : ((k⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 - 1 ∈ idealBall (𝓞 ℚ) ℚ N := hKi.lowerRight

  have h3 : (((k * u)⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
      - ((u⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 ∈ idealBall (𝓞 ℚ) ℚ N := by
    have h := mul_sub_mul_mem (N := N) (show ((u⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
        - ((u⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 ∈ idealBall (𝓞 ℚ) ℚ N by rw [sub_self]; exact zero_mem_idealBall N)
      hki1 (hUi.integral 1 1) (hKi.integral 1 1)
    rw [mul_one] at h
    have := add_mem_idealBall hm2 h
    rwa [sub_add_sub_cancel] at this

  have h4 : ((k' * (k * u)⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
      - ((u⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 ∈ idealBall (𝓞 ℚ) ℚ N := by
    have h := mul_sub_mul_mem (N := N) hk'1 h3 one_mem_integralFiniteAdeles
      ((Subgroup.inv_mem _ (Subgroup.mul_mem _ (finiteLevelOne_le_finiteLevelZero _ _ _ hk) hu)).1.integral 1 1)
    rw [one_mul] at h
    have := add_mem_idealBall hm1 h
    rwa [sub_add_sub_cancel] at this

  have h5 : A * ((k' * (k * u)⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
      - A * ((u⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 ∈ idealBall (𝓞 ℚ) ℚ N := by
    rw [← mul_sub]; exact mul_mem_idealBall_left hdI h4
  have := add_mem_idealBall h5 hdt
  rwa [sub_add_sub_cancel] at this

theorem intCast_mem_integralFiniteAdeles (n : ℤ) :
    algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (n : ℚ) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
  intro v
  have h := algebraMap_mem_adicCompletionIntegers (R := 𝓞 ℚ) (K := ℚ) v (n : 𝓞 ℚ)
  rw [map_intCast] at h
  exact h

end

theorem weightOneLift_mul_finEmbed_eq_inv_nebentypus_mul_of_mem_finiteLevelZero
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 1}
    (hε : CuspForm.HasNebentypus ε h)
    (u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) (hu : u ∈ finiteLevelZero (𝓞 ℚ) ℚ (AdelicDock.ratLevel M))
    (d : ℤ)
    (hd : (u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
        - algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (d : ℚ) ∈ idealBall (𝓞 ℚ) ℚ (AdelicDock.ratLevel M))
    (x : AdelicGL2 (𝓞 ℚ) ℚ) :
    weightOneLift (Ideal.span {(M : 𝓞 ℚ)}) (⇑h) (x * AdelicDock.finEmbed (𝓞 ℚ) ℚ u) =
      (ε (d : ZMod M))⁻¹ * weightOneLift (Ideal.span {(M : 𝓞 ℚ)}) (⇑h) x := by
  have hM : M ≠ 0 := NeZero.ne M
  obtain ⟨γ, y, k, hh, hpos, hk, hx⟩ := exists_eq_globalPoints_mul_mul_finEmbed_of_mem_finiteLevelOne hM x
  obtain ⟨γ', y', k', hh', hpos', hk', hx'⟩ :=
    exists_eq_globalPoints_mul_mul_finEmbed_of_mem_finiteLevelOne hM (x * AdelicDock.finEmbed (𝓞 ℚ) ℚ u)
  rw [hx', apply_decomp₁ hM h hh' hpos' hk', hx, apply_decomp₁ hM h hh hpos hk]
  have hku : k * u ∈ finiteLevelZero (𝓞 ℚ) ℚ (AdelicDock.ratLevel M) :=
    Subgroup.mul_mem _ (finiteLevelOne_le_finiteLevelZero _ _ _ hk) hu
  have hk'0 : k' ∈ finiteLevelZero (𝓞 ℚ) ℚ (AdelicDock.ratLevel M) := finiteLevelOne_le_finiteLevelZero _ _ _ hk'
  have heq : globalPoints (𝓞 ℚ) ℚ γ * y * AdelicDock.finEmbed (𝓞 ℚ) ℚ (k * u) =
      globalPoints (𝓞 ℚ) ℚ γ' * y' * AdelicDock.finEmbed (𝓞 ℚ) ℚ k' := by
    rw [← hx', hx, map_mul, ← mul_assoc]
  obtain ⟨ε₀, hε0, harch, hfin⟩ := exists_sl_of_levelZero hM hku hh hpos hk'0 hh' hpos' heq

  have he : ε ((ε₀ 1 1 : ℤ) : ZMod M) = (ε (d : ZMod M))⁻¹ := by
    have hent : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (((ε₀ 1 1 : ℤ) : ℚ))
        = ((k' * (k * u)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 := by
      rw [← hfin, glFin_globalPoints_apply, Matrix.SpecialLinearGroup.mapGL_coe_matrix]
      rfl
    have hball := algebraMap_mul_lowerRight_sub_one_mem hk hk' hu (d : ℚ) (intCast_mem_integralFiniteAdeles d) hd
    rw [← hent, ← map_mul, ← Int.cast_mul, show (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)
        = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((1 : ℤ) : ℚ) by rw [Int.cast_one, map_one], ← map_sub,
      ← Int.cast_sub] at hball
    have hdvd := natCast_dvd_of_mem_idealBall hM _ hball
    have hZ : ((d : ZMod M)) * ((ε₀ 1 1 : ℤ) : ZMod M) = 1 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mpr hdvd
      rwa [Int.cast_sub, Int.cast_mul, Int.cast_one, sub_eq_zero] at this
    have hmul : ε (d : ZMod M) * ε ((ε₀ 1 1 : ℤ) : ZMod M) = 1 := by rw [← map_mul, hZ, map_one]
    exact (eq_inv_of_mul_eq_one_right hmul)
  rw [harch, weightOneArchLift_coe_mul hε hε0 (show 0 < (LanglandsTunnell.ratArchGL2 y).det.val from hpos), he]

end DihedralWeightOne

end
