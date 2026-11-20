/-
  The weight-one lift is a cuspidal automorphic form.

  For a holomorphic weight-one form `f` on `Γ₁(n)`, bounded by `C / im τ^(1/2)` and vanishing at
  every cusp, the adelic lift `weightOneLift (span {n}) f` is cuspidal: it is continuous, `L²`, and
  its constant term vanishes along the unipotent radical.

  Transcribed from `P2M/Sol/S_LanglandsTunnell_isCuspidalFn_weightOneLift.lean` (pinned `aa2d8b3`,
  1,831 lines / 139 declarations). The module carries the row and **46** of the pin's private
  declarations — 47 in all — at the pin's `private` visibility, names and statements; the
  48-declaration shared prelude, and four integrality lemmas the boundedness row already had, are
  imported from `WeightOneLiftAdelic`; and the pin's 40 unreachable private declarations are
  deferred (see `## Deferred pin surface`, below).

  spec-pin: P2M/Sol/S_LanglandsTunnell_isCuspidalFn_weightOneLift.lean

  ## Port deltas

  Added import `FLTForHuman.AutomorphicForm.Adelic.ConstantTermUnipotent`: the pin's
  `constantTerm_eq_zero_of_arch_mul` (pin `:1690`) uses
  `AutomorphicForm.constantTerm_adelicBox_unipotentGL2_mul`, which lives there and is not in
  `AutomorphicForm.Adelic.ConstantTerm`'s closure.

  Proof-side (statement-neutral) edits against the pin, all in bodies:
  * pin-namespace prefixes stripped (`R1.`/`R3.`/`R4a.`/`R7.`/`R8.` → the port's flat
    `LanglandsTunnell` names; `P2GProbe.R8.isCuspidalFn_weightOneLift` →
    `isCuspidalFn_weightOneLift_impl`);
  * v4.34 drift: `if_pos`/`if_neg`/`dif_pos`/`dif_neg` → `ite_eq_left`/`ite_eq_right`/
    `dite_eq_left`/`dite_eq_right`; `continuous_ofReal` → `Complex.continuous_ofReal`;
    `im_smul_eq_div_normSq` → `UpperHalfPlane.im_smul_eq_div_normSq` (a `ModularGroup`
    namesake at v4.34 makes the bare name ambiguous);
  * `NumberField.AdelicBox.` qualification of `adelicBox`/`isProbabilityMeasure_cond_adelicBox`
    (this module does not open that namespace, for the reason recorded for `ν₀`);
  * `haveI`/`letI` → `have`/`let` (FR-0223);
  * `eq_of_glArch_eq_of_glFin_eq` → `DetIntegral.eq_of_glArch_eq_of_glFin_eq` (the port's
    `AutomorphicForm.`-namesake makes the bare name ambiguous at three sites);
  * `measurableSet_adelicBox` → `NumberField.AdelicBox.measurableSet_adelicBox`.

  ## Deferred pin surface (40 private declarations, the playbook §1 cut)

  The pin's own file carries 40 `private` declarations that nothing in it reaches from
  `solution` (a prefix- and suffix-aware reference scan over the pin puts them in the pin's
  unreachable set of 55 — the cut is not a port artefact). The pin's other 15 unreachable ones
  are either in the shared engine, where other rows use them (9), or live *here* because this
  module's flat `LanglandsTunnell` namespace makes its own copy win where the pin's reference
  resolves to the same-named imported declaration (6). Their mathematics is *another node's*
  content, which the port already has — the delta lift is `LanglandsTunnell/DeltaLift.lean`
  (`deltaArchLift`/`HasDeltaDecomp`/`deltaLift`) and the arch lift's boundedness is
  `LanglandsTunnell/WeightOneBound.lean` — so the cut loses no mathematics and no consumer
  exists (`move_dead.py` reads `0 declarations, 0 lines` since the cut). Pin ranges:

  * the `P4.I2` delta-lift block, pin `:31`–`:610`: `deltaArch`, `deltaArch_def`,
    `deltaArch_sl_mul`, `slash_scalar`, `deltaArch_scalar_mul`, `deltaArch_one`,
    `deltaArch_one_ne_zero`, `norm_deltaArch_le` (`:31`–`:110`); `IsDeltaDecomp`,
    `deltaArch_ratArch_eq_of_isDeltaDecomp`, `deltaLiftFn`, `deltaLiftFn_eq`,
    `deltaLiftFn_of_not`, `deltaLiftFn_globalPoints_mul`, `deltaLiftFn_mul_of_mem_U`,
    `isDeltaDecomp_one`, `deltaLiftFn_one`, `deltaLiftFn_one_ne_zero`,
    `exists_isDeltaDecomp_of_strongApprox`, `isDeltaDecomp_mul`, `deltaLiftFn_mul_eq`
    (`:283`–`:490`); `deltaArch_eq_of_det_pos`, `continuousOn_discriminant_smul_I`,
    `continuousOn_deltaArch`, `continuous_deltaLiftFn`, `norm_deltaLiftFn_le`,
    `memLp_two_deltaLiftFn` (`:531`–`:610`);
  * `span_243_ne_bot`, `hasWeightOneDecomp_243`, `not_exists_not_hasWeightOneDecomp`
    (pin `:893`–`:902`);
  * arch-lift and `nArch` leaves with no consumer: `weightOneArchLift_one` (`:807`),
    `weightOneArchLift_iwasawa` (`:810`), `weightOneLift_eq_dif_pos` (`:906`),
    `finPart_globalPoints_mapGL_mem_U` (`:716`), `gamma1_slash_binder_of_SL_slash` (`:1341`);
  * the boundedness pair whose only consumer is itself: `norm_weightOneLift_le_of_mem_D`
    (`:1188`), `memLp_two_weightOneLift` (`:1321`);
  * the integrality leaves: `algebraMap_det_mem_integral` (`:1131`),
    `abs_det_eq_one_of_glFin_mem_finiteIntegralGL2` (`:1141`), `det_ratArch_eq_archDetNorm`
    (`:1165`).

  ## Heartbeat probe (FR-0225 — a measurement, not a floor; nothing is installed)

  The heaviest declaration is `exists_weightOneLift_unipotent_eq` (pin `:1589`). One pair, both
  runs of
  `lake env lean -DautoImplicit=false -DmaxHeartbeats=<n> FLTForHuman/LanglandsTunnell/WeightOneLiftCuspidal.lean`:

  * `n = 25000` — silent (whole module, no output);
  * `n = 12500` — fails: `(deterministic) timeout at isDefEq, maximum number of heartbeats
    (12500) has been reached`, plus the `whnf` timeout it cascades into; both sites are inside
    `exists_weightOneLift_unipotent_eq`, the declaration named above.

  So the natural cost lies in `(12500, 25000]` heartbeats, i.e. under 0.7 % of the project's
  4,000,000 cap. The module is silent at the playbook's 200,000 and at the project default.
-/


import FLTForHuman.AutomorphicForm.Adelic.ConstantTermUnipotent
import FLTForHuman.LanglandsTunnell.WeightOneLiftAdelic
import FLTForHuman.LanglandsTunnell.DihedralWeightOneLift
import FLTForHuman.AutomorphicForm.Adelic.ProductionPinsCompact
import FLTForHuman.AutomorphicForm.Adelic.Basic
import FLTForHuman.NumberTheory.AdelicLevel.Projections
import FLTForHuman.NumberTheory.AdelicLevel.Level
import FLTForHuman.NumberTheory.AdelicLevel.IdealBall
import FLTForHuman.NumberTheory.AdelicDock.LocalEmbedding
import FLTForHuman.NumberTheory.AdelicHaar.Adele
import FLTForHuman.AutomorphicForm.Adelic.ConstantTerm
import FLTForHuman.AutomorphicForm.Adelic.WindowedSiegel.Topology
import FLTForHuman.AutomorphicForm.Adelic.BorelSubgroup
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.Bounds

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
open NumberField.AdelicLevel AutomorphicForm.WindowedSiegel NumberField.AdelicVolume
open MeasureTheory
open scoped Topology Manifold
open DihedralWeightOne
attribute [local instance] NumberField.AdelicHaar.adeleBorel
local notation "𝔾" => GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)
local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ
local notation "ν₀" => ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) (NumberField.AdelicBox.adelicBox ℚ)


namespace LanglandsTunnell

open RatArch DetIntegral ArchLift



section

private theorem continuous_ratArch : Continuous ratArch := by
  have hcont : Continuous
      (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom := by
    have : ⇑(InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom
        = InfinitePlace.Completion.extensionEmbeddingOfIsReal (isReal_rat_infinitePlace default) := by
      funext x; rfl
    rw [this]
    exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal _).continuous
  have hmap : Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2)
      (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom) :=
    Continuous.units_map _ ((continuous_id.matrix_map hcont) :
      Continuous fun m : Matrix (Fin 2) (Fin 2) _ => m.map _)
  exact hmap.comp ((continuous_archComponent ℚ default).comp (continuous_glArch (𝓞 ℚ) ℚ))

private theorem continuous_entry (i j : Fin 2) : Continuous fun h : GL (Fin 2) ℝ => (((h : Matrix (Fin 2) (Fin 2) ℝ) i j :
    ℝ) : ℂ) :=
  Complex.continuous_ofReal.comp (Units.continuous_val.matrix_elem i j)

private theorem continuous_denom_I : Continuous fun h : GL (Fin 2) ℝ => denom h UpperHalfPlane.I := by
  show Continuous fun h : GL (Fin 2) ℝ =>
    (((h : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℝ) : ℂ) * UpperHalfPlane.I + (((h : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℝ) : ℂ)
  exact ((continuous_entry 1 0).mul continuous_const).add (continuous_entry 1 1)

private theorem continuous_num_I : Continuous fun h : GL (Fin 2) ℝ => num h UpperHalfPlane.I := by
  show Continuous fun h : GL (Fin 2) ℝ =>
    (((h : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℝ) : ℂ) * UpperHalfPlane.I + (((h : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℝ) : ℂ)
  exact ((continuous_entry 0 0).mul continuous_const).add (continuous_entry 0 1)

private theorem continuous_det_val : Continuous fun h : GL (Fin 2) ℝ => h.det.val := by
  show Continuous fun h : GL (Fin 2) ℝ => (Matrix.GeneralLinearGroup.det h).val
  simp_rw [Matrix.GeneralLinearGroup.val_det_apply]
  exact Units.continuous_val.matrix_det

private theorem isOpen_detPos : IsOpen {h : GL (Fin 2) ℝ | 0 < h.det.val} :=
  isOpen_lt continuous_const continuous_det_val

private theorem continuousOn_coe_smul_I :
    ContinuousOn (fun h : GL (Fin 2) ℝ => ((h • UpperHalfPlane.I : ℍ) : ℂ)) {h | 0 < h.det.val} := by
  refine ContinuousOn.congr (f := fun h : GL (Fin 2) ℝ => num h UpperHalfPlane.I / denom h UpperHalfPlane.I) ?_ ?_
  · exact (continuous_num_I.div continuous_denom_I fun h => denom_ne_zero h _).continuousOn
  · intro h hh
    exact coe_smul_of_det_pos hh _

private theorem exists_borel_mul_mapGL (γ : GL (Fin 2) ℚ) :
    ∃ β : GL (Fin 2) ℚ, β ∈ AutomorphicForm.borelSubgroup ℚ ∧
      ∃ δ : SL(2, ℤ), γ = β * Matrix.SpecialLinearGroup.mapGL ℚ δ := by
  set c : ℚ := (γ : Matrix (Fin 2) (Fin 2) ℚ) 1 0 with hc
  set d : ℚ := (γ : Matrix (Fin 2) (Fin 2) ℚ) 1 1 with hd
  by_cases h0 : c = 0
  · exact ⟨γ, by rw [AutomorphicForm.mem_borelSubgroup_iff, ← hc, h0], 1, by rw [map_one, mul_one]⟩

  set r : ℚ := d / c with hr
  have hcop : IsCoprime r.num (-(r.den : ℤ)) := by
    refine IsCoprime.neg_right (Int.isCoprime_iff_gcd_eq_one.mpr ?_)
    rw [Int.gcd_eq_natAbs_gcd_natAbs, Int.natAbs_natCast]
    exact r.reduced
  obtain ⟨g, -, hg⟩ := ModularGroup.bottom_row_surj (R := ℤ)
    (show ![r.num, -(r.den : ℤ)] ∈ {cd : Fin 2 → ℤ | IsCoprime (cd 0) (cd 1)} from hcop)
  have hg0 : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = r.num := by
    have := congrFun hg 0; simpa using this
  have hg1 : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = -(r.den : ℤ) := by
    have := congrFun hg 1; simpa using this

  let δ : SL(2, ℤ) := Matrix.SpecialLinearGroup.transpose g * ModularGroup.S
  have hδ00 : (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = r.num := by
    simp [δ, Matrix.SpecialLinearGroup.coe_transpose, ModularGroup.coe_S, Matrix.mul_apply, Fin.sum_univ_two, hg0]
  have hδ10 : (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = -(r.den : ℤ) := by
    simp [δ, Matrix.SpecialLinearGroup.coe_transpose, ModularGroup.coe_S, Matrix.mul_apply, Fin.sum_univ_two, hg1]
  refine ⟨γ * Matrix.SpecialLinearGroup.mapGL ℚ δ, ?_, δ⁻¹, by rw [map_inv, mul_inv_cancel_right]⟩

  rw [AutomorphicForm.mem_borelSubgroup_iff, Matrix.GeneralLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe, Matrix.mul_apply,
    Fin.sum_univ_two, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.map_apply, hδ00, hδ10, ← hc, ← hd]
  have hden : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hnum : (r.num : ℚ) = r * r.den := (div_eq_iff hden).mp (Rat.num_div_den r)
  simp only [map_neg, eq_intCast, Int.cast_natCast]
  rw [hnum, hr]
  field_simp
  ring

private theorem isLevelOneMatrix_glFin_globalPoints_mapGL (ε : SL(2, ℤ)) :
    IsLevelOneMatrix (𝓞 ℚ) ℚ ⊤ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ ε)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
  have hint : ∀ i j, (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ ε)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
    intro i j
    rw [glFin_globalPoints_apply, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, eq_intCast]
    exact intCast_mem_integralFiniteAdeles _
  refine ⟨⟨hint, fun v => ?_⟩, fun v => ?_⟩
  · rw [idealBound_top]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hint 1 0 v)
  · rw [idealBound_top]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp
      (sub_mem_integralFiniteAdeles (hint 1 1) one_mem_integralFiniteAdeles v)

private theorem glFin_globalPoints_mapGL_mem (δ : SL(2, ℤ)) :
    glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ δ)) ∈ finiteLevelOne (𝓞 ℚ) ℚ ⊤ := by
  rw [mem_finiteLevelOne_iff]
  refine ⟨isLevelOneMatrix_glFin_globalPoints_mapGL δ, ?_⟩
  rw [← map_inv, ← map_inv, ← map_inv]
  exact isLevelOneMatrix_glFin_globalPoints_mapGL δ⁻¹

private theorem ratArch_archPart_globalPoints_mapGL (δ : SL(2, ℤ)) :
    ratArch (archPart (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ δ))) = (δ : GL (Fin 2) ℝ) := by
  rw [ratArch_archPart, ratArch_globalPoints_mapGL]

private theorem det_ratArch_archPart_globalPoints_mapGL (δ : SL(2, ℤ)) :
    (ratArch (archPart (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ δ)))).det.val = 1 := by
  rw [ratArch_archPart_globalPoints_mapGL, Matrix.GeneralLinearGroup.val_det_apply]
  exact Matrix.SpecialLinearGroup.det_coe _

end

section

variable (f : ℍ → ℂ)

private theorem norm_weightOneArchLift_le (C : ℝ)
    (hf : ∀ τ : ℍ, ‖f τ‖ ≤ C / τ.im ^ (((1 : ℤ) : ℝ) / 2))
    (h : GL (Fin 2) ℝ) (hh : 0 < h.det.val) :
    ‖weightOneArchLift f h‖ ≤ C * Real.sqrt h.det.val := by
  have hd : denom h UpperHalfPlane.I ≠ 0 := denom_ne_zero h UpperHalfPlane.I
  have hdn : 0 < ‖denom h UpperHalfPlane.I‖ := norm_pos_iff.mpr hd

  have him : (h • UpperHalfPlane.I).im = h.det.val / ‖denom h UpperHalfPlane.I‖ ^ 2 := by
    rw [UpperHalfPlane.im_smul_eq_div_normSq, abs_of_pos hh, UpperHalfPlane.I_im, mul_one,
      Complex.normSq_eq_norm_sq]
  have himpos : 0 < (h • UpperHalfPlane.I).im := (h • UpperHalfPlane.I).im_pos

  have hnorm : ‖weightOneArchLift f h‖ =
      ‖f (h • UpperHalfPlane.I)‖ * ‖denom h UpperHalfPlane.I‖⁻¹ * h.det.val := by
    unfold weightOneArchLift
    rw [ModularForm.slash_apply, σ, ite_eq_left hh]
    simp only [ContinuousAlgEquiv.refl_apply, sub_self, zpow_zero, mul_one, _root_.zpow_neg, zpow_one,
      norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]

  have hsq : (h • UpperHalfPlane.I).im ^ (((1 : ℤ) : ℝ) / 2) = Real.sqrt (h • UpperHalfPlane.I).im := by
    rw [Real.sqrt_eq_rpow]; norm_num
  have hspos : 0 < Real.sqrt (h • UpperHalfPlane.I).im := Real.sqrt_pos.mpr himpos
  have hpet : ‖f (h • UpperHalfPlane.I)‖ * Real.sqrt (h • UpperHalfPlane.I).im ≤ C := by
    have h1 := hf (h • UpperHalfPlane.I)
    rw [hsq] at h1
    calc ‖f (h • UpperHalfPlane.I)‖ * Real.sqrt (h • UpperHalfPlane.I).im
        ≤ C / Real.sqrt (h • UpperHalfPlane.I).im * Real.sqrt (h • UpperHalfPlane.I).im :=
          mul_le_mul_of_nonneg_right h1 hspos.le
      _ = C := by field_simp

  have hsqrt_im : Real.sqrt (h • UpperHalfPlane.I).im
      = Real.sqrt h.det.val / ‖denom h UpperHalfPlane.I‖ := by
    rw [him, Real.sqrt_div hh.le, Real.sqrt_sq hdn.le]
  have hds : Real.sqrt h.det.val * Real.sqrt h.det.val = h.det.val := Real.mul_self_sqrt hh.le

  have hkey : ‖weightOneArchLift f h‖ =
      (‖f (h • UpperHalfPlane.I)‖ * Real.sqrt (h • UpperHalfPlane.I).im) * Real.sqrt h.det.val := by
    rw [hnorm, hsqrt_im, div_eq_mul_inv]
    calc ‖f (h • UpperHalfPlane.I)‖ * ‖denom h UpperHalfPlane.I‖⁻¹ * h.det.val
        = ‖f (h • UpperHalfPlane.I)‖ * ‖denom h UpperHalfPlane.I‖⁻¹
            * (Real.sqrt h.det.val * Real.sqrt h.det.val) := by rw [hds]
      _ = ‖f (h • UpperHalfPlane.I)‖ * (Real.sqrt h.det.val * ‖denom h UpperHalfPlane.I‖⁻¹)
            * Real.sqrt h.det.val := by ring
  rw [hkey]
  exact mul_le_mul_of_nonneg_right hpet (Real.sqrt_nonneg _)

private theorem weightOneArchLift_eq_of_det_pos (f : ℍ → ℂ) (h : GL (Fin 2) ℝ) (hh : 0 < h.det.val) :
    weightOneArchLift f h
      = f (h • UpperHalfPlane.I) * (denom h UpperHalfPlane.I)⁻¹ * ((h.det.val : ℝ) : ℂ) := by
  have h' : 0 < ((h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rwa [← Matrix.GeneralLinearGroup.val_det_apply]
  have hσ : ∀ w : ℂ, σ h w = w := fun w => by simp [σ, h']
  rw [weightOneArchLift_def, ModularForm.slash_apply, hσ]
  simp

private theorem continuousOn_weightOneArchLift (f : ℍ → ℂ) (hf : Continuous f) :
    ContinuousOn (weightOneArchLift f) {h : GL (Fin 2) ℝ | 0 < h.det.val} := by
  have hsmul : ContinuousOn (fun h : GL (Fin 2) ℝ => (h • UpperHalfPlane.I : ℍ)) {h | 0 < h.det.val} :=
    UpperHalfPlane.isEmbedding_coe.continuousOn_iff.mpr continuousOn_coe_smul_I
  have hdet : Continuous fun h : GL (Fin 2) ℝ => ((h.det.val : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp continuous_det_val
  refine ContinuousOn.congr (f := fun h : GL (Fin 2) ℝ =>
      f (h • UpperHalfPlane.I) * (denom h UpperHalfPlane.I)⁻¹ * ((h.det.val : ℝ) : ℂ))
    ?_ fun h hh => weightOneArchLift_eq_of_det_pos f h hh
  exact ((hf.comp_continuousOn hsmul).mul (continuous_denom_I.inv₀ fun h => denom_ne_zero h _).continuousOn).mul
    hdet.continuousOn

private theorem continuous_weightOneLift {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ) (hf_cont : Continuous f)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f) :
    Continuous (weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f) := by
  have hN : Ideal.span {(n : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  refine continuous_iff_continuousAt.mpr fun g₀ => ?_
  obtain ⟨γ₀, h₀, u₀, hu₀, hh₀, hpos₀, hg₀⟩ := hasWeightOneDecomp_of_ne_bot hN g₀
  have hh₀pos : 0 < (ratArch h₀).det.val := by
    rw [← ratArchGL2_eq_ratArch]
    exact hpos₀
  have hinner : Continuous fun g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) => ratArch h₀ * ratArch (g₀⁻¹ * g) :=
    continuous_const.mul (continuous_ratArch.comp (continuous_const.mul continuous_id))
  let W : Set (GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :=
    {g | glFin (𝓞 ℚ) ℚ (g₀⁻¹ * g) ∈ finiteLevelOne (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)})
      ∧ 0 < (ratArch h₀ * ratArch (g₀⁻¹ * g)).det.val}
  have hWopen : IsOpen W := by
    refine IsOpen.inter ?_ ?_
    · exact (isOpen_finiteLevelOne (𝓞 ℚ) ℚ (N := Ideal.span {(n : 𝓞 ℚ)}) hN).preimage
        ((continuous_glFin (𝓞 ℚ) ℚ).comp (continuous_const.mul continuous_id))
    · exact isOpen_detPos.preimage hinner
  have hg₀W : g₀ ∈ W := by
    refine ⟨?_, ?_⟩
    · show glFin (𝓞 ℚ) ℚ (g₀⁻¹ * g₀) ∈ finiteLevelOne (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)})
      rw [inv_mul_cancel, map_one]
      exact Subgroup.one_mem _
    · show 0 < (ratArch h₀ * ratArch (g₀⁻¹ * g₀)).det.val
      rwa [inv_mul_cancel, ratArch_one, mul_one]
  have hEq : Set.EqOn (weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f)
      (fun g => weightOneArchLift f (ratArch h₀ * ratArch (g₀⁻¹ * g))) W := by
    intro g hg
    have := weightOneLift_mul_eq hn f hf hu₀ hh₀ hg₀ (g₀⁻¹ * g) hg.1 hg.2
    rwa [mul_inv_cancel_left] at this
  have hpt : ContinuousAt (weightOneArchLift f) (ratArch h₀ * ratArch (g₀⁻¹ * g₀)) :=
    (continuousOn_weightOneArchLift f hf_cont).continuousAt (isOpen_detPos.mem_nhds hg₀W.2)
  have hmodel : ContinuousAt (fun g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) =>
      weightOneArchLift f (ratArch h₀ * ratArch (g₀⁻¹ * g))) g₀ :=
    ContinuousAt.comp (f := fun g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) => ratArch h₀ * ratArch (g₀⁻¹ * g))
      (x := g₀) hpt hinner.continuousAt
  exact hmodel.congr ((Filter.eventuallyEq_of_mem (hWopen.mem_nhds hg₀W) hEq).symm)

private theorem coe_SL_inv (ρ : SL(2, ℤ)) : ((ρ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) = ((ρ : GL (Fin 2) ℝ))⁻¹ := by
  change Matrix.SpecialLinearGroup.mapGL ℝ ρ⁻¹ = (Matrix.SpecialLinearGroup.mapGL ℝ ρ)⁻¹
  exact map_inv _ _

private def nArch (t : ℝ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, t; 0, 1] (by rw [Matrix.det_fin_two_of]; simp)

private theorem nArch_apply (t : ℝ) : ((nArch t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![1, t; 0, 1] := rfl

private theorem det_nArch (t : ℝ) : (nArch t).det.val = 1 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  change Matrix.det !![(1 : ℝ), t; 0, 1] = _
  rw [Matrix.det_fin_two_of]; ring

private theorem det_pos_nArch (t : ℝ) : 0 < (nArch t).det.val := by
  rw [det_nArch]; exact one_pos

private theorem denom_nArch (t : ℝ) (z : ℍ) : denom (nArch t) z = 1 := by
  simp [denom, nArch_apply]

private theorem num_nArch (t : ℝ) (z : ℍ) : num (nArch t) z = (z : ℂ) + t := by
  simp [num, nArch_apply]

private theorem nArch_smul (t : ℝ) (z : ℍ) : nArch t • z = t +ᵥ z := by
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos (det_pos_nArch t), num_nArch, denom_nArch, div_one, coe_vadd, add_comm]

private theorem slash_nArch (F : ℍ → ℂ) (t : ℝ) : F ∣[(1 : ℤ)] nArch t = fun z => F (t +ᵥ z) := by
  have h' : 0 < ((nArch t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact det_pos_nArch t
  have hσ : ∀ w : ℂ, σ (nArch t) w = w := fun w => by simp [σ, h']
  funext z
  rw [ModularForm.slash_apply, hσ, nArch_smul, det_nArch, denom_nArch]
  simp

private theorem weightOneArchLift_SL_mul (f : ℍ → ℂ) (ρ : SL(2, ℤ)) (M : GL (Fin 2) ℝ) :
    weightOneArchLift f ((ρ : GL (Fin 2) ℝ) * M) = weightOneArchLift (f ∣[(1 : ℤ)] (ρ : GL (Fin 2) ℝ)) M := by
  rw [weightOneArchLift_def, weightOneArchLift_def, SlashAction.slash_mul, map_mul, Units.val_mul,
    det_coe_SL, one_mul]

private theorem weightOneArchLift_nArch_mul (F : ℍ → ℂ) (t : ℝ) (H : GL (Fin 2) ℝ) (hH : 0 < H.det.val) :
    weightOneArchLift F (nArch t * H)
      = F (t +ᵥ (H • UpperHalfPlane.I : ℍ)) * (denom H UpperHalfPlane.I)⁻¹ * ((H.det.val : ℝ) : ℂ) := by
  have hG : weightOneArchLift F (nArch t * H) = weightOneArchLift (fun z => F (t +ᵥ z)) H := by
    rw [weightOneArchLift_def, weightOneArchLift_def, SlashAction.slash_mul, slash_nArch, map_mul,
      Units.val_mul, det_nArch, one_mul]
  rw [hG, weightOneArchLift_eq_of_det_pos _ H hH]

private theorem intervalIntegral_weightOneArchLift_nArch_mul (F : ℍ → ℂ) (n : ℕ)
    (hF : ∀ z : ℍ, ∫ s in (0 : ℝ)..(n : ℝ), F (s +ᵥ z) = 0) (r : ℝ) (H : GL (Fin 2) ℝ)
    (hH : 0 < H.det.val) :
    ∫ s in (0 : ℝ)..(n : ℝ), weightOneArchLift F (nArch (r + s) * H) = 0 := by
  simp_rw [weightOneArchLift_nArch_mul F _ H hH, add_comm r, add_vadd]
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const, hF, zero_mul, zero_mul]

private theorem gamma_le_gamma1_of_level (n : ℕ) : CongruenceSubgroup.Gamma n ≤ CongruenceSubgroup.Gamma1 n := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ
  exact (CongruenceSubgroup.Gamma1_mem n γ).mpr ⟨hγ.1, hγ.2.2.2, hγ.2.2.1⟩

private theorem slash_vadd_natCast {n : ℕ} (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (ρ : SL(2, ℤ)) (w : ℍ) :
    (f ∣[(1 : ℤ)] (ρ : GL (Fin 2) ℝ)) ((n : ℝ) +ᵥ w) = (f ∣[(1 : ℤ)] (ρ : GL (Fin 2) ℝ)) w := by
  have hT : ModularGroup.T ^ (n : ℤ) ∈ CongruenceSubgroup.Gamma n := by
    simpa using CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma (n : ℤ) (n : ℤ) dvd_rfl
  have hκ : ρ * ModularGroup.T ^ (n : ℤ) * ρ⁻¹ ∈ CongruenceSubgroup.Gamma1 n :=
    gamma_le_gamma1_of_level n ((CongruenceSubgroup.Gamma_normal n).conj_mem _ hT ρ)
  have hfκ : f ∣[(1 : ℤ)] (ρ * ModularGroup.T ^ (n : ℤ) * ρ⁻¹) = f := hf _ hκ
  have hslash : (f ∣[(1 : ℤ)] ρ) ∣[(1 : ℤ)] (ModularGroup.T ^ (n : ℤ)) = f ∣[(1 : ℤ)] ρ := by
    rw [← SlashAction.slash_mul,
      show ρ * ModularGroup.T ^ (n : ℤ) = (ρ * ModularGroup.T ^ (n : ℤ) * ρ⁻¹) * ρ by group,
      SlashAction.slash_mul, hfκ]
  have h := congr_fun hslash w
  have hden : denom ((ModularGroup.T ^ (n : ℤ) : SL(2, ℤ)) : GL (Fin 2) ℝ) w = 1 := by
    rw [ModularGroup.denom_apply, ModularGroup.coe_T_zpow]
    simp
  rw [ModularForm.SL_slash_apply, modular_T_zpow_smul, hden, _root_.one_zpow, mul_one, Int.cast_natCast] at h
  exact h

private theorem intervalIntegral_slash_vadd_eq_zero {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf_hol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (ρ : SL(2, ℤ)) (hρ : IsZeroAtImInfty (f ∣[(1 : ℤ)] (ρ : GL (Fin 2) ℝ))) (z : ℍ) :
    ∫ s in (0 : ℝ)..(n : ℝ), (f ∣[(1 : ℤ)] (ρ : GL (Fin 2) ℝ)) (s +ᵥ z) = 0 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hFper : ∀ w : ℍ, (f ∣[(1 : ℤ)] (ρ : GL (Fin 2) ℝ)) ((n : ℝ) +ᵥ w)
      = (f ∣[(1 : ℤ)] (ρ : GL (Fin 2) ℝ)) w := fun w => slash_vadd_natCast f hf ρ w
  set F : ℍ → ℂ := f ∣[(1 : ℤ)] (ρ : GL (Fin 2) ℝ) with hFdef

  have hper : Function.Periodic (F ∘ UpperHalfPlane.ofComplex) (n : ℝ) := by
    intro w
    by_cases hw : 0 < w.im
    · have hw' : 0 < (w + (n : ℝ)).im := by simpa using hw
      simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hw',
        UpperHalfPlane.ofComplex_apply_of_im_pos hw]
      rw [← hFper ⟨w, hw⟩]
      congr 1
      apply UpperHalfPlane.ext
      simp [add_comm]
    · have hw₀ : w.im ≤ 0 := not_lt.mp hw
      have hw' : (w + (n : ℝ)).im ≤ 0 := by simpa using hw₀
      simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_nonpos hw',
        UpperHalfPlane.ofComplex_apply_of_im_nonpos hw₀]
  have hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F := hf_hol.slash 1 _
  have hbdd : IsBoundedAtImInfty F := hρ.isBoundedAtImInfty

  have h0 := UpperHalfPlane.qExpansion_coeff_eq_intervalIntegral hnpos hper hhol hbdd 0 z.im_pos
  rw [UpperHalfPlane.qExpansion_coeff_zero hnpos
      (UpperHalfPlane.analyticAt_cuspFunction_zero hnpos hper hhol hbdd) hper,
    hρ.valueAtInfty_eq_zero] at h0
  simp only [pow_zero, div_one, one_mul] at h0
  set G : ℝ → ℂ := fun u => F ⟨(u : ℂ) + z.im * Complex.I, by simpa using z.im_pos⟩ with hGdef
  have hint : ∫ u in (0 : ℝ)..(n : ℝ), G u = 0 := by
    have hn' : (1 : ℂ) / ((n : ℝ) : ℂ) ≠ 0 := one_div_ne_zero (by exact_mod_cast hn)
    rcases mul_eq_zero.mp h0.symm with h | h
    · exact absurd h hn'
    · exact h

  have hGper : Function.Periodic G (n : ℝ) := by
    intro u
    simp only [hGdef]
    conv_rhs => rw [← hFper]
    congr 1
    apply UpperHalfPlane.ext
    simp only [coe_vadd]
    push_cast
    ring
  have hshift : ∀ s : ℝ, F (s +ᵥ z) = G (s + z.re) := by
    intro s
    simp only [hGdef]
    congr 1
    apply UpperHalfPlane.ext
    simp only [coe_vadd]
    push_cast
    rw [add_assoc, UpperHalfPlane.re_add_im]
  simp_rw [hshift]
  rw [intervalIntegral.integral_comp_add_right G z.re, zero_add, add_comm (n : ℝ) z.re,
    hGper.intervalIntegral_add_eq z.re 0, zero_add, hint]

private def realCoord (x : 𝔸) : ℝ :=
  (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)) (x.1 default)

private theorem ratArch_unipotentGL2 (x : 𝔸) : ratArch (unipotentGL2 x) = nArch (realCoord x) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change ((InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom.comp
      ((archEval ℚ default).comp (adeleArch (𝓞 ℚ) ℚ)))
      ((unipotentGL2 x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j)
    = (nArch (realCoord x) : Matrix (Fin 2) (Fin 2) ℝ) i j
  have h1 : ((1 : AdeleRing (𝓞 ℚ) ℚ).1 default) = 1 := rfl
  have h0 : ((0 : AdeleRing (𝓞 ℚ) ℚ).1 default) = 0 := rfl
  rw [unipotentGL2_coe, nArch_apply]
  fin_cases i <;> fin_cases j <;> simp [realCoord, archEval_apply, adeleArch_apply, h1, h0]

private theorem glFin_unipotentGL2_mem_integral {x : 𝔸}
    (hx : x.2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ) :
    glFin (𝓞 ℚ) ℚ (unipotentGL2 x) ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ := by
  have hval : (glFin (𝓞 ℚ) ℚ (unipotentGL2 x) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
      = !![1, x.2; 0, 1] := by
    ext i j
    rw [glFin_apply, unipotentGL2_coe]
    fin_cases i <;> fin_cases j <;> rfl
  have hinv : (((glFin (𝓞 ℚ) ℚ (unipotentGL2 x))⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) = !![1, -x.2; 0, 1] := by
    rw [← map_inv]
    refine Matrix.ext fun i j => ?_
    rw [glFin_apply]
    change ((!![1, -x; 0, 1] : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 = _
    fin_cases i <;> fin_cases j <;> rfl
  have h0 := zero_mem_idealBall (R := 𝓞 ℚ) (K := ℚ) (⊤ : Ideal (𝓞 ℚ))
  have hx' : -x.2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ := by
    simpa using sub_mem_integralFiniteAdeles zero_mem_integralFiniteAdeles hx
  have hmem : glFin (𝓞 ℚ) ℚ (unipotentGL2 x) ∈ finiteLevelOne (𝓞 ℚ) ℚ ⊤ := by
    rw [mem_finiteLevelOne_iff, hval, hinv]
    refine ⟨⟨⟨?_, by simpa using h0⟩, by simpa using h0⟩, ⟨⟨?_, by simpa using h0⟩, by simpa using h0⟩⟩
    · intro i j
      fin_cases i <;> fin_cases j <;>
        simp [one_mem_integralFiniteAdeles, zero_mem_integralFiniteAdeles, hx]
    · intro i j
      fin_cases i <;> fin_cases j <;>
        simp [one_mem_integralFiniteAdeles, zero_mem_integralFiniteAdeles, hx']
  exact finiteLevelOne_le_finiteLevelZero _ _ _ hmem

private def archAdele (s : ℝ) : 𝔸 :=
  (fun w => (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace w)).symm s, 0)

private theorem realCoord_add_archAdele (x : 𝔸) (s : ℝ) : realCoord (x + archAdele s) = realCoord x + s := by
  change (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default))
      (x.1 default + (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).symm s)
    = (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)) (x.1 default) + s
  rw [map_add, RingEquiv.apply_symm_apply]

private theorem snd_add_archAdele (x : 𝔸) (s : ℝ) : (x + archAdele s).2 = x.2 := by
  change x.2 + 0 = x.2
  exact add_zero _

private theorem continuous_archAdele : Continuous archAdele := by
  refine Continuous.prodMk (continuous_pi fun w => ?_) continuous_const
  exact (InfinitePlace.Completion.isometryEquivRealOfIsReal (isReal_rat_infinitePlace w)).symm.continuous

private theorem unipotentGL2_inv_coe (y : 𝔸) :
    (((unipotentGL2 y)⁻¹ : 𝔾) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) = !![1, -y; 0, 1] := rfl

private theorem continuous_unipotentGL2 : Continuous fun y : 𝔸 => (unipotentGL2 y : 𝔾) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> first | exact continuous_const | exact continuous_id'
  · refine continuous_matrix fun i j => ?_
    simp only [unipotentGL2_inv_coe]
    fin_cases i <;> fin_cases j <;> simp [continuous_neg] <;> exact continuous_const

private theorem finPart_unipotentGL2_add_archAdele (x : 𝔸) (s : ℝ) :
    finPart (unipotentGL2 (x + archAdele s)) = finPart (unipotentGL2 x) := by
  apply DetIntegral.eq_of_glArch_eq_of_glFin_eq
  · rw [glArch_finPart, glArch_finPart]
  · rw [glFin_finPart, glFin_finPart]
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [glFin_apply, glFin_apply, unipotentGL2_coe, unipotentGL2_coe]
    fin_cases i <;> fin_cases j
    · rfl
    · exact snd_add_archAdele x s
    · rfl
    · rfl

private theorem exists_weightOneLift_unipotent_eq {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    {x : 𝔸} (hx : x.2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ) {h₁ q : 𝔾}
    (hh₁ : glFin (𝓞 ℚ) ℚ h₁ = 1)
    (hh₁pos : 0 < (ratArch h₁).det.val)
    (hq : glArch (𝓞 ℚ) ℚ q = 1) (hqint : glFin (𝓞 ℚ) ℚ q ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ) :
    ∃ ρ : SL(2, ℤ), ∀ s : ℝ,
      weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f (unipotentGL2 (x + archAdele s) * (h₁ * q))
        = weightOneArchLift f (((ρ : GL (Fin 2) ℝ))⁻¹ * (nArch (realCoord x + s) * ratArch h₁)) := by
  have hN : Ideal.span {(n : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  have harch₁ : archPart h₁ = h₁ :=
    DetIntegral.eq_of_glArch_eq_of_glFin_eq (glArch_archPart h₁) (by rw [glFin_archPart, hh₁])

  set Q : 𝔾 := finPart (unipotentGL2 x) * q with hQdef
  have hQarch : glArch (𝓞 ℚ) ℚ Q = 1 := by
    rw [hQdef, map_mul, glArch_finPart, hq, mul_one]
  have hQint : glFin (𝓞 ℚ) ℚ Q ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ := by
    rw [hQdef, map_mul, glFin_finPart]
    exact Subgroup.mul_mem _ (glFin_unipotentGL2_mem_integral hx) hqint
  obtain ⟨γ, h₀, u₀, hu₀, hh₀, hpos₀, hQ⟩ := hasWeightOneDecomp_of_ne_bot hN Q
  have hh₀pos : 0 < (ratArch h₀).det.val := by
    rw [← ratArchGL2_eq_ratArch]
    exact hpos₀

  have hγint : glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ := by
    have hsplit : glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) = glFin (𝓞 ℚ) ℚ Q * (glFin (𝓞 ℚ) ℚ u₀)⁻¹ := by
      rw [hQ, map_mul, map_mul, hh₀, mul_one, mul_inv_cancel_right]
    have hu₀int : glFin (𝓞 ℚ) ℚ u₀ ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ :=
      finiteLevelZero_le_finiteIntegralGL2 _ (finiteLevelOne_le_finiteLevelZero _ _ _
        (glFin_mem_finiteLevelOne_of_mem_productionPinsCompact_U ℚ _ hu₀))
    rw [hsplit]
    exact Subgroup.mul_mem _ hQint (Subgroup.inv_mem _ hu₀int)

  have hprod : ratArch (globalPoints (𝓞 ℚ) ℚ γ) * ratArch h₀ = 1 := by
    have h1 : ratArch Q = 1 := ratArch_eq_one_of_glArch_eq_one hQarch
    have hu₀arch : ratArch u₀ = 1 :=
      ratArch_eq_one_of_glArch_eq_one (glArch_eq_one_of_mem_productionPinsCompact_U ℚ _ hu₀)
    rwa [hQ, ratArch_mul, ratArch_mul, hu₀arch, mul_one] at h1
  have hdetγ : 0 < ((Matrix.GeneralLinearGroup.det γ : ℚˣ) : ℚ) := by
    have hd : (ratArch (globalPoints (𝓞 ℚ) ℚ γ)).det.val * (ratArch h₀).det.val = 1 := by
      rw [← Units.val_mul, ← map_mul, hprod, map_one, Units.val_one]
    have hpos' : 0 < (ratArch (globalPoints (𝓞 ℚ) ℚ γ)).det.val := by
      rw [eq_inv_of_mul_eq_one_left hd]
      exact inv_pos.mpr hh₀pos
    rw [det_ratArch_globalPoints] at hpos'
    exact_mod_cast hpos'
  obtain ⟨ρ, hρ⟩ := exists_mapGL_eq_of_mem_finiteIntegralGL2 hγint hdetγ
  have hρarch : ratArch (globalPoints (𝓞 ℚ) ℚ γ) = (ρ : GL (Fin 2) ℝ) := by
    rw [← hρ, ratArch_globalPoints_mapGL]
  have hh₀arch : ratArch h₀ = ((ρ : GL (Fin 2) ℝ))⁻¹ := by
    rw [hρarch] at hprod
    exact eq_inv_of_mul_eq_one_right hprod
  refine ⟨ρ, fun s => ?_⟩

  set A : 𝔾 := archPart (unipotentGL2 (x + archAdele s)) * h₁ with hAdef
  have hAfin : glFin (𝓞 ℚ) ℚ A = 1 := by
    rw [hAdef, map_mul, glFin_archPart, hh₁, mul_one]
  have hAarch : ratArch A = nArch (realCoord x + s) * ratArch h₁ := by
    rw [hAdef, ratArch_mul, ratArch_archPart, ratArch_unipotentGL2, realCoord_add_archAdele]
  have hpoint : unipotentGL2 (x + archAdele s) * (h₁ * q) = A * Q := by
    rw [hAdef, hQdef, ← finPart_unipotentGL2_add_archAdele x s]
    calc unipotentGL2 (x + archAdele s) * (h₁ * q)
        = archPart (unipotentGL2 (x + archAdele s)) * finPart (unipotentGL2 (x + archAdele s)) * archPart h₁ * q := by
          rw [archPart_mul_finPart, harch₁]; group
      _ = archPart (unipotentGL2 (x + archAdele s)) * (archPart h₁ * finPart (unipotentGL2 (x + archAdele s))) * q := by
          rw [archPart_mul_finPart_comm h₁ (unipotentGL2 (x + archAdele s))]; group
      _ = archPart (unipotentGL2 (x + archAdele s)) * h₁ * (finPart (unipotentGL2 (x + archAdele s)) * q) := by
          rw [harch₁]; group
  set h' : 𝔾 := (globalPoints (𝓞 ℚ) ℚ γ)⁻¹ * A * globalPoints (𝓞 ℚ) ℚ γ * h₀ with hh'def
  have hdecomp : unipotentGL2 (x + archAdele s) * (h₁ * q) = globalPoints (𝓞 ℚ) ℚ γ * h' * u₀ := by
    rw [hpoint, hQ, hh'def]; group
  have hh'fin : glFin (𝓞 ℚ) ℚ h' = 1 := by
    rw [hh'def, map_mul, map_mul, map_mul, map_inv, hAfin, hh₀, mul_one, mul_one, inv_mul_cancel]
  have hh'arch : ratArch h' = ((ρ : GL (Fin 2) ℝ))⁻¹ * (nArch (realCoord x + s) * ratArch h₁) := by
    rw [hh'def, ratArch_mul, ratArch_mul, ratArch_mul, ratArch_inv, hρarch, hh₀arch, hAarch]
    group
  have hh'pos : LanglandsTunnell.ratArchGL2 h' ∈ GLPos (Fin 2) ℝ := by
    show 0 < (LanglandsTunnell.ratArchGL2 h').det.val
    rw [ratArchGL2_eq_ratArch, hh'arch, map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul,
      Units.val_inv_eq_inv_val, det_coe_SL, inv_one, one_mul, det_nArch, one_mul]
    exact hh₁pos
  rw [weightOneLift_eq hn f hf _ γ h' u₀ hu₀ hh'fin hh'pos hdecomp, ratArchGL2_eq_ratArch, hh'arch]

private theorem constantTerm_eq_zero_of_arch_mul {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ) (hf_cont : Continuous f)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (C : ℝ) (hC : ∀ τ : ℍ, ‖f τ‖ ≤ C / τ.im ^ (((1 : ℤ) : ℝ) / 2))
    (hper : ∀ ρ : SL(2, ℤ), ∀ z : ℍ,
      ∫ s in (0 : ℝ)..(n : ℝ), (f ∣[(1 : ℤ)] (ρ : GL (Fin 2) ℝ)) (s +ᵥ z) = 0)
    {h₁ q : 𝔾} (hh₁ : glFin (𝓞 ℚ) ℚ h₁ = 1) (hh₁pos : 0 < (ratArch h₁).det.val)
    (hq : glArch (𝓞 ℚ) ℚ q = 1) (hqint : glFin (𝓞 ℚ) ℚ q ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ) :
    constantTerm ν₀ (fun x => unipotentGL2 x) (weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f) (h₁ * q) = 0 := by
  have : BorelSpace 𝔸 := borelSpace_adeleBorel (𝓞 ℚ) ℚ
  have : IsProbabilityMeasure ν₀ := NumberField.AdelicBox.isProbabilityMeasure_cond_adelicBox ℚ
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  set φ : 𝔾 → ℂ := weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f with hφdef
  set K : ℝ → 𝔸 → ℂ := fun s x => φ (unipotentGL2 (x + archAdele s) * (h₁ * q)) with hKdef

  have hA : ∀ s : ℝ, constantTerm ν₀ (fun x => unipotentGL2 x) φ (h₁ * q) = ∫ x, K s x ∂ν₀ := by
    intro s
    rw [← AutomorphicForm.constantTerm_adelicBox_unipotentGL2_mul ℚ (φ := φ)
      (fun k g => weightOneLift_globalPoints_mul hn f hf (unipotentGL2 k) g) (archAdele s) (h₁ * q)]
    unfold constantTerm constantTermIntegrand
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show φ (unipotentGL2 x * (unipotentGL2 (archAdele s) * (h₁ * q))) = φ (unipotentGL2 (x + archAdele s) * (h₁ * q))
    rw [← mul_assoc, ← unipotentGL2_add]

  have hB : ∀ x : 𝔸, x ∈ NumberField.AdelicBox.adelicBox ℚ → ∫ s in (0 : ℝ)..(n : ℝ), K s x = 0 := by
    intro x hx
    obtain ⟨ρ, hρ⟩ := exists_weightOneLift_unipotent_eq hn f hf hx.2 hh₁ hh₁pos hq hqint
    have hK : ∀ s : ℝ, K s x
        = weightOneArchLift (f ∣[(1 : ℤ)] ((ρ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ)) (nArch (realCoord x + s) * ratArch h₁) := by
      intro s
      rw [hKdef, hφdef]
      show weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f (unipotentGL2 (x + archAdele s) * (h₁ * q)) = _
      rw [hρ s, ← coe_SL_inv, weightOneArchLift_SL_mul]
    simp_rw [hK]
    exact intervalIntegral_weightOneArchLift_nArch_mul _ n (hper ρ⁻¹) (realCoord x) (ratArch h₁) hh₁pos

  have hKcont : Continuous (Function.uncurry K) := by
    have h1 : Continuous fun p : ℝ × 𝔸 => p.2 + archAdele p.1 :=
      continuous_snd.add (continuous_archAdele.comp continuous_fst)
    have h2 : Continuous fun p : ℝ × 𝔸 => (unipotentGL2 (p.2 + archAdele p.1) : 𝔾) * (h₁ * q) :=
      (continuous_unipotentGL2.comp h1).mul continuous_const
    exact (continuous_weightOneLift hn f hf_cont hf).comp h2
  have hKbound : ∀ s : ℝ, ∀ x : 𝔸, x ∈ NumberField.AdelicBox.adelicBox ℚ → ‖K s x‖ ≤ C * Real.sqrt (ratArch h₁).det.val := by
    intro s x hx
    obtain ⟨ρ, hρ⟩ := exists_weightOneLift_unipotent_eq hn f hf hx.2 hh₁ hh₁pos hq hqint
    have hK : K s x = weightOneArchLift f (((ρ : GL (Fin 2) ℝ))⁻¹ * (nArch (realCoord x + s) * ratArch h₁)) := hρ s
    have hdet : 0 < (((ρ : GL (Fin 2) ℝ))⁻¹ * (nArch (realCoord x + s) * ratArch h₁)).det.val := by
      rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val, det_coe_SL, inv_one,
        one_mul, det_nArch, one_mul]
      exact hh₁pos
    have hdet' : (((ρ : GL (Fin 2) ℝ))⁻¹ * (nArch (realCoord x + s) * ratArch h₁)).det.val = (ratArch h₁).det.val := by
      rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val, det_coe_SL, inv_one,
        one_mul, det_nArch, one_mul]
    rw [hK]
    have := norm_weightOneArchLift_le f C hC _ hdet
    rwa [hdet'] at this
  have hmeas : MeasurableSet (NumberField.AdelicBox.adelicBox ℚ) := NumberField.AdelicBox.measurableSet_adelicBox ℚ
  have hae : ∀ᵐ p : ℝ × 𝔸 ∂(volume.restrict (Set.Ioc (0 : ℝ) n)).prod ν₀, p ∈ Prod.snd ⁻¹' NumberField.AdelicBox.adelicBox ℚ :=
    (Measure.ae_prod_mem_iff_ae_ae_mem (hmeas.preimage measurable_snd)).mpr
      (Filter.Eventually.of_forall fun _ => ProbabilityTheory.ae_cond_mem hmeas)
  have hint : Integrable (Function.uncurry K) ((volume.restrict (Set.Ioc (0 : ℝ) n)).prod ν₀) := by
    refine memLp_one_iff_integrable.mp
      (MemLp.of_bound hKcont.aestronglyMeasurable (C * Real.sqrt (ratArch h₁).det.val) ?_)
    filter_upwards [hae] with p hp
    exact hKbound p.1 p.2 hp

  have hswap : ∫ s in (0 : ℝ)..(n : ℝ), ∫ x, K s x ∂ν₀ = ∫ x, (∫ s in (0 : ℝ)..(n : ℝ), K s x) ∂ν₀ := by
    rw [intervalIntegral.integral_of_le hnpos.le]
    simp_rw [intervalIntegral.integral_of_le hnpos.le]
    exact integral_integral_swap hint
  have hinner : ∫ x, (∫ s in (0 : ℝ)..(n : ℝ), K s x) ∂ν₀ = 0 := by
    calc ∫ x, (∫ s in (0 : ℝ)..(n : ℝ), K s x) ∂ν₀ = ∫ _x, (0 : ℂ) ∂ν₀ := by
          refine integral_congr_ae ?_
          filter_upwards [ProbabilityTheory.ae_cond_mem hmeas] with x hx
          exact hB x hx
      _ = 0 := integral_zero _ _
  have hCT : ∫ s in (0 : ℝ)..(n : ℝ), constantTerm ν₀ (fun x => unipotentGL2 x) φ (h₁ * q)
      = ∫ s in (0 : ℝ)..(n : ℝ), ∫ x, K s x ∂ν₀ :=
    intervalIntegral.integral_congr fun s _ => hA s
  have hconst : ∫ s in (0 : ℝ)..(n : ℝ), constantTerm ν₀ (fun x => unipotentGL2 x) φ (h₁ * q)
      = ((n : ℝ) : ℂ) * constantTerm ν₀ (fun x => unipotentGL2 x) φ (h₁ * q) := by
    rw [intervalIntegral.integral_const, sub_zero, Complex.real_smul]
  have hmain : ((n : ℝ) : ℂ) * constantTerm ν₀ (fun x => unipotentGL2 x) φ (h₁ * q) = 0 := by
    rw [← hconst, hCT, hswap, hinner]
  have hn' : ((n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn
  exact (mul_eq_zero.mp hmain).resolve_left hn'

private theorem constantTerm_weightOneLift_eq_zero {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ) (hf_cont : Continuous f)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (C : ℝ) (hC : ∀ τ : ℍ, ‖f τ‖ ≤ C / τ.im ^ (((1 : ℤ) : ℝ) / 2))
    (hper : ∀ ρ : SL(2, ℤ), ∀ z : ℍ,
      ∫ s in (0 : ℝ)..(n : ℝ), (f ∣[(1 : ℤ)] (ρ : GL (Fin 2) ℝ)) (s +ᵥ z) = 0)
    (g : 𝔾) :
    constantTerm ν₀ (fun x => unipotentGL2 x) (weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f) g = 0 := by
  have hN : Ideal.span {(n : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  obtain ⟨γ, h, u, hu, hh, hpos, hg⟩ := hasWeightOneDecomp_of_ne_bot hN g
  have hhpos : 0 < (ratArch h).det.val := by
    rw [← ratArchGL2_eq_ratArch]
    exact hpos
  obtain ⟨β, hβ, δ, hγ⟩ := exists_borel_mul_mapGL γ
  set k : 𝔾 := globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ δ) with hk
  have hg' : g = globalPoints (𝓞 ℚ) ℚ β * (k * h * u) := by
    rw [hg, hγ, map_mul, hk]
    simp only [mul_assoc]
  rw [hg', AutomorphicForm.constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup ℚ
    (φ := weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f)
    (fun γ' _ h' => weightOneLift_globalPoints_mul hn f hf γ' h') hβ]
  have harch : archPart h = h :=
    DetIntegral.eq_of_glArch_eq_of_glFin_eq (glArch_archPart h) (by rw [glFin_archPart, hh])
  have hsplit : k * h * u = archPart k * h * (finPart k * u) := by
    calc k * h * u = archPart k * finPart k * archPart h * u := by rw [archPart_mul_finPart, harch]
      _ = archPart k * (archPart h * finPart k) * u := by rw [archPart_mul_finPart_comm h k]; group
      _ = archPart k * h * (finPart k * u) := by rw [harch]; group
  rw [hsplit]
  refine constantTerm_eq_zero_of_arch_mul hn f hf_cont hf C hC hper ?_ ?_ ?_ ?_
  · rw [map_mul, glFin_archPart, one_mul, hh]
  · rw [ratArch_mul, map_mul, Units.val_mul, det_ratArch_archPart_globalPoints_mapGL, one_mul]
    exact hhpos
  · rw [map_mul, glArch_finPart, glArch_eq_one_of_mem_productionPinsCompact_U ℚ _ hu, mul_one]
  · rw [map_mul, glFin_finPart]
    exact Subgroup.mul_mem _ (finiteLevelOne_le_finiteLevelZero _ _ _ (glFin_globalPoints_mapGL_mem δ))
      (finiteLevelZero_le_finiteIntegralGL2 _ (finiteLevelOne_le_finiteLevelZero _ _ _
        (glFin_mem_finiteLevelOne_of_mem_productionPinsCompact_U ℚ _ hu)))

private theorem isCuspidalFn_weightOneLift_of_period {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ) (hf_cont : Continuous f)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (C : ℝ) (hC : ∀ τ : ℍ, ‖f τ‖ ≤ C / τ.im ^ (((1 : ℤ) : ℝ) / 2))
    (hper : ∀ ρ : SL(2, ℤ), ∀ z : ℍ,
      ∫ s in (0 : ℝ)..(n : ℝ), (f ∣[(1 : ℤ)] (ρ : GL (Fin 2) ℝ)) (s +ᵥ z) = 0) :
    IsCuspidalFn ν₀ (fun x => unipotentGL2 x) (weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f) :=
  fun g => constantTerm_weightOneLift_eq_zero hn f hf_cont hf C hC hper g

private theorem isCuspidalFn_weightOneLift_impl {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf_hol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (C : ℝ) (hC : ∀ τ : ℍ, ‖f τ‖ ≤ C / τ.im ^ (((1 : ℤ) : ℝ) / 2))
    (hzero : ∀ δ : SL(2, ℤ), IsZeroAtImInfty (f ∣[(1 : ℤ)] (δ : GL (Fin 2) ℝ))) :
    @IsCuspidalFn _ (productionPinsCompact ℚ).nS _ _ (productionPinsCompact ℚ).ν unipotentGL2
      (weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f) :=
  isCuspidalFn_weightOneLift_of_period hn f hf_hol.continuous hf C hC
    (fun ρ z => intervalIntegral_slash_vadd_eq_zero hn f hf_hol hf ρ (hzero ρ) z)

end

theorem isCuspidalFn_weightOneLift
    {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf_hol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (C : ℝ) (hC : ∀ τ : ℍ, ‖f τ‖ ≤ C / τ.im ^ (((1 : ℤ) : ℝ) / 2))
    (hzero : ∀ δ : SL(2, ℤ), IsZeroAtImInfty (f ∣[(1 : ℤ)] (δ : GL (Fin 2) ℝ))) :
    @IsCuspidalFn _ (productionPinsCompact ℚ).nS _ _ (productionPinsCompact ℚ).ν unipotentGL2
      (weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f) := by
  exact isCuspidalFn_weightOneLift_impl hn f hf_hol hf C hC hzero

end LanglandsTunnell

end
