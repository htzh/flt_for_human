/-
  The weight-one lift is a nonzero cuspidal function of the primitive form's level.

  For a primitive weight-one cusp form `f` on `Γ₁(N)` with nebentypus `ψ`, the adelic lift
  `weightOneLift (span {N}) f` is (i) the underlying function of a *smooth cuspidal realization* of
  the Hecke eigensystem `Φ` whose Hecke eigenvalues are `f`'s `q`-coefficients and whose central
  character is `ψ` read on the idèle class character, at the *general* (not the compact) pins, and
  is bounded on Siegel windows; and (ii) nonzero and right-invariant under the principal
  congruence subgroup of level `N`.

  **One development, two headlines.** The two pins are the same file up to their last theorem:
  76 declarations each, 75 byte-identical and only `solution` differing, so the engine is written
  *once* here and consumed by both rows. It is: the archimedean projection `ratArch` and its
  continuity; the Iwasawa value, the bound and the continuity of the archimedean slash lift
  `weightOneArchLift`; the integrality leaves (`algebraMap_det_mem_integral`,
  `abs_det_eq_one_of_glFin_mem_finiteIntegralGL2`, `det_ratArch_eq_archDetNorm`) that turn the
  pin's Siegel-window hypothesis into a bound on that lift; the `L²`-membership of the lift on the
  Siegel domain; and the point `archPoint τ` at which the lift is `im τ · f τ`, hence nonzero.

  **Surface, 76 of 76.** 30 declarations are declared here — 5 public (`exists_prime_mem`,
  `absNorm_asIdeal_eq`, `slash_eq`, and the two rows) and 25 private, at the pin's own `private`
  markers, names and statements. The pin's other 46 private declarations are public in this
  module's import closure and are used through their namespaces rather than re-proved: the
  AF93 prelude in `LanglandsTunnell/WeightOneLiftAdelic.lean`
  (`LanglandsTunnell.RatArch`, `…DetIntegral`, `…ArchLift`) plus
  `LanglandsTunnell/WeightOneLiftLevel.lean`. Nothing of the pin is dropped: the four public
  `Ws1.L1` helpers are `exists_prime_mem`, `absNorm_asIdeal_eq`, `slash_eq` (transcribed at the
  pin's text) and `slash_eq_smul_of_hasNebentypus`, which the port already has in the same
  namespace in `LanglandsTunnell/WeightOneLiftLevel.lean:1003` and which is therefore re-used. The
  two `solution` statements are the two rows. `check_port` reads the five public declarations
  (the shared helper through the import closure for `scaffold_audit`).

  spec-pin: P2M/Sol/S_DihedralWeightOne_exists_smoothCuspRealizationAt_productionPinsGeneral_toFun_eq_weightOneLift_of_isPrimitiveForm.lean
  spec-pin: P2M/Sol/S_DihedralWeightOne_weightOneLift_ne_zero_and_apply_mul_finEmbed_eq_of_isPrimitiveForm.lean

  ## Port deltas

  Imports. The scaffold's six, plus nine the development needs and the scaffold could not know
  about (each is the home of a row or a lemma a pin body calls):
  `ModularForms.Level.DegeneracyString` (`heckeU_add_smul_slash_heckeDiagMatrix_degeneracy_eq_qCoeff_smul`,
  the `T_ℓ`-on-degeneracy lemma of the `hT` computation),
  `AutomorphicForm.Adelic.LsXiL2BoundExists` (`mem_centreCutSiegelSet_iff`),
  `LanglandsTunnell.WeightOneLiftCuspidal` (`isCuspidalFn_weightOneLift`),
  `…WeightOneLiftKfSmooth`, `…WeightOneBound`, `…WeightOneLiftHeckeEigen`,
  `…WeightOneLiftCentralScalar`, `…WeightOneLiftCentralDet`, and
  `LanglandsTunnell.TateLocal.DirichletIdele` (`dirichletIdeleChar_mul_modulus_det_gen`).
  No `import Mathlib` (FR-0254): every module named is a leaf, has its `.olean` in the tree, and
  the module elaborates in 8.6 s wall.

  Namespaces. The pin scatters the one development over six search-stage namespaces
  (`LanglandsTunnell.P4.I2`, `P2GProbe.R1`, `P2GProbe.R3`, `P2GProbe.R4a`, `P2GProbe.R7`,
  `P2GProbe.Alpha`, `Ws1.L1`); as in every ported module of this column they are flattened to the
  row's own `DihedralWeightOne`, and the pin's stage prefixes are dropped from the *bodies*
  (`R1.weightOneArchLift_def` → `weightOneArchLift_def`, `P2GProbe.R4a.weightOneLift_eq` →
  the imported `LanglandsTunnell.weightOneLift_eq`, …). No statement is touched: the qualifiers
  the row statements carry are the pin's own.

  **A port-side shadowing the pin does not have.** `LanglandsTunnell/WeightOneLiftLevel.lean`
  declares, inside `DihedralWeightOne` itself, nine names that are also on the AF93 prelude:
  `ratArch_mul`, `ratArch_inv`, `ratArchHom_apply`, `ratArch_eq_one_of_glArch_eq_one`,
  `ratArch_globalPoints`, `archPart`, `glFin_archPart`, `ratArch_archPart` and
  `slash_eq_smul_of_hasNebentypus` — all of them about `LanglandsTunnell.ratArchGL2` (the delta
  lift's projection), not about the pin's `ratArch`. In the pin's flat `P2GProbe.R4a` those two
  families never meet, but inside `DihedralWeightOne` the local names win over the opened
  prelude, so a body that reads `ratArch_mul` gets the `ratArchGL2` law. The two sites that mix
  the families (`det_ratArch_eq_archDetNorm`) therefore spell
  `LanglandsTunnell.RatArch.ratArch_mul` / `…ratArch_eq_one_of_glArch_eq_one` in full. This is a
  body-only qualifier, not a statement change. The ninth, `slash_eq_smul_of_hasNebentypus`, is the
  *reason* the pin's 21-line helper is not re-declared here; it is re-used, and its statement is
  the port's (binder spelling `{γ : SL(2,ℤ)}` and type `CuspForm (Subgroup.map … (Gamma1 N)) 1`,
  the pin's `∀ γ, γ ∈ Gamma0 N →` conclusion unchanged), so the pin's call
  `slash_eq_smul_of_hasNebentypus ψ f hf.1.hasNebentypus` is written here as
  `fun γ hγ => slash_eq_smul_of_hasNebentypus (F := f) hf.1.hasNebentypus hγ`.

  Mathlib drift (FR-0255), bodies only, statements untouched:
  * `if_pos` → `ite_eq_left` (`weightOneArchLift_iwasawa`, `norm_weightOneArchLift_le`);
  * `continuous_ofReal` → `Complex.continuous_ofReal` (`continuous_entry`,
    `continuousOn_weightOneArchLift`);
  * `im_smul_eq_div_normSq` → `UpperHalfPlane.im_smul_eq_div_normSq` (`norm_weightOneArchLift_le`;
    a `ModularGroup` namesake makes the bare name ambiguous at this mathlib pin);
  * `haveI` → `have` (`memLp_two_weightOneLift`).

  One measurement, not a drift. The pin writes `letI := (productionPinsCompact ℚ).mS` in
  `memLp_two_weightOneLift`'s proof and in the first row's `smoothCusp` field. `linter.style.haveILetI`
  asks for `let`, and `let` — or a `have : MeasurableSpace …` — does not compile: the goal's
  instance is the *inlined* `productionPinsCompact.mS`, and an opaque local is not definitionally
  equal to it (`synthesized type class instance is not definitionally equal to expression inferred
  by typing rules`). The pin's `letI`, whose whole point is that inlining, is therefore kept, and
  the style linter is silenced with a `set_option … in` scoped to exactly the two declarations that
  need it (the same accommodation, in the same shape, as
  `AutomorphicForm.Adelic.Cusp.BoundedGenuineRealization`). No other linter is touched; the pin's
  own `linter.unusedSectionVars false` is kept because its `Ws1.L1.slash_eq` does not use `[NeZero N]`.

  ## Heartbeat probe (FR-0225 — a measurement, not a floor; nothing is installed)

  The heaviest declarations are `norm_weightOneArchLift_le` (pin `:355`), `det_ratArch_eq_archDetNorm`
  (pin `:663`) and the first row (pin `:969`); at any limit below the bracket all three are what
  fails. One pair, both runs of
  `lake env lean -DautoImplicit=false -DmaxHeartbeats=<n> FLTForHuman/LanglandsTunnell/WeightOneLiftCuspidalRealization.lean`:

  * `n = 10000` — silent (whole module, no output, 8.6 s wall at the project default);
  * `n = 5000` — fails: `(deterministic) timeout at whnf`, maximum number of heartbeats (5000)
    has been reached, at `:225` (`norm_weightOneArchLift_le`), `:549` (the first row) and `:622`
    (`refine` in its `IsSmoothCuspAutomorphicFnAt` block), plus a `whnf`/`isDefEq` cascade.

  So the natural cost lies in `(5000, 10000]` heartbeats, i.e. under 0.25 % of the project's
  4,000,000 cap. The module is silent at the project default, which is what the gates read.
-/

import FLTForHuman.LanglandsTunnell.WeightOneLiftAdelic
import FLTForHuman.LanglandsTunnell.WeightOneLiftLevel
import FLTForHuman.AutomorphicForm.Adelic.Cusp.BoundedGenuineRealization
import FLTForHuman.AutomorphicForm.Adelic.ProductionPinsCompact
import FLTForHuman.AutomorphicForm.Adelic.ArchType
import FLTForHuman.NumberTheory.AdelicDock.LocalEmbedding
import FLTForHuman.ModularForms.Level.DegeneracyString
import FLTForHuman.AutomorphicForm.Adelic.LsXiL2BoundExists
import FLTForHuman.LanglandsTunnell.WeightOneLiftCuspidal
import FLTForHuman.LanglandsTunnell.WeightOneLiftKfSmooth
import FLTForHuman.LanglandsTunnell.WeightOneBound
import FLTForHuman.LanglandsTunnell.WeightOneLiftHeckeEigen
import FLTForHuman.LanglandsTunnell.WeightOneLiftCentralScalar
import FLTForHuman.LanglandsTunnell.WeightOneLiftCentralDet
import FLTForHuman.LanglandsTunnell.TateLocal.DirichletIdele

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm AdelicDock
open CongruenceSubgroup
open scoped MatrixGroups ModularForm

namespace DihedralWeightOne

open scoped UpperHalfPlane Topology Manifold
open UpperHalfPlane Matrix
open Matrix Matrix.GeneralLinearGroup
open NumberField.AdelicHaar MeasureTheory
open AutomorphicForm.WindowedSiegel IsDedekindDomain.HeightOneSpectrum NumberField.AdelicVolume
open LanglandsTunnell LanglandsTunnell.RatArch LanglandsTunnell.DetIntegral
open LanglandsTunnell.ArchLift

/-! ## The rational archimedean projection and the continuity of the archimedean lift

The pin's `LanglandsTunnell.P4.I2` block: `ratArch` is the composite of the archimedean component,
the (real) completion isomorphism at the default infinite place and `GL₂` of the residue field,
and everything below it in this section is the topological input to the continuity of
`weightOneLift`. -/

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

/-! ## The archimedean lift: its Iwasawa value, its bound, and its continuity

The pin's `P2GProbe.R1` block. `weightOneArchLift f h = (f ∣[1] h) I · (det h)`, so on the Iwasawa
matrix of `z` it is `im z · f z`; that identity is what makes the lift nonzero at the explicit
point `archPoint τ` in the last section. -/

section ArchBounds

variable (f : ℍ → ℂ)

private theorem weightOneArchLift_iwasawa (z : ℍ) (h : GL (Fin 2) ℝ)
    (hh : (h : Matrix (Fin 2) (Fin 2) ℝ) = !![z.im, z.re; 0, 1]) :
    weightOneArchLift f h = (z.im : ℂ) * f z := by
  have h00 : h 0 0 = z.im := by
    have := congr_fun (congr_fun hh 0) 0; simpa using this
  have h01 : h 0 1 = z.re := by
    have := congr_fun (congr_fun hh 0) 1; simpa using this
  have h10 : h 1 0 = 0 := by
    have := congr_fun (congr_fun hh 1) 0; simpa using this
  have h11 : h 1 1 = 1 := by
    have := congr_fun (congr_fun hh 1) 1; simpa using this
  have hdet : h.det.val = z.im := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h00, h01, h10, h11]; ring
  have hdetpos : 0 < h.det.val := by rw [hdet]; exact z.im_pos
  have hsmul : h • UpperHalfPlane.I = z := by
    apply UpperHalfPlane.ext
    rw [coe_smul_of_det_pos hdetpos, num, denom, h00, h01, h10, h11]
    simp only [UpperHalfPlane.coe_I, Complex.ofReal_zero, Complex.ofReal_one, zero_mul, zero_add,
      div_one]
    apply Complex.ext <;> simp
  unfold weightOneArchLift
  rw [ModularForm.slash_apply, σ, ite_eq_left hdetpos, hsmul, denom, h10, h11, hdet]
  simp only [ContinuousAlgEquiv.refl_apply, Complex.ofReal_zero, Complex.ofReal_one, zero_mul,
    zero_add, sub_self, zpow_zero, mul_one, _root_.zpow_neg, inv_one, zpow_one]
  ring

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

end ArchBounds

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

/-! ## The integrality leaves and the archimedean determinant

The pin's `P2GProbe.R7` block, first half: a rational point of `GL₂` whose finite component is
integral has determinant of absolute value one, and the archimedean determinant of a point that
decomposes as `globalPoints γ · h · u` with `h` of positive determinant is the determinant of `h`.
These are the two facts that turn the pin's Siegel-window hypothesis into a bound on
`weightOneArchLift`. -/

private theorem algebraMap_det_mem_integral (γ : GL (Fin 2) ℚ)
    (h : ∀ i j, (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j ∈ integralFiniteAdeles (𝓞 ℚ) ℚ) :
    algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((GeneralLinearGroup.det γ : ℚˣ) : ℚ)
      ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
  rw [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, map_sub, map_mul, map_mul]
  simp only [← glFin_globalPoints_apply]
  exact sub_mem_integralFiniteAdeles (mul_mem_integralFiniteAdeles (h 0 0) (h 1 1))
    (mul_mem_integralFiniteAdeles (h 0 1) (h 1 0))

private theorem abs_det_eq_one_of_glFin_mem_finiteIntegralGL2 {γ : GL (Fin 2) ℚ}
    (hint : glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ) :
    |((GeneralLinearGroup.det γ : ℚˣ) : ℚ)| = 1 := by
  rw [mem_finiteIntegralGL2_iff] at hint
  obtain ⟨hγ, hγinv⟩ := hint
  have hγinv' : ∀ i j, (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ⁻¹) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
    intro i j
    rw [map_inv, map_inv]
    exact hγinv i j
  have h1 := algebraMap_det_mem_integral γ hγ
  have h2 := algebraMap_det_mem_integral γ⁻¹ hγinv'
  rw [map_inv, Units.val_inv_eq_inv_val] at h2
  exact abs_eq_one_of_mem_integral (GeneralLinearGroup.det γ).ne_zero h1 h2

private theorem det_ratArch_eq_archDetNorm {n : ℕ} {g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} {γ : GL (Fin 2) ℚ}
    {h u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    (hgint : glFin (𝓞 ℚ) ℚ g ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ)
    (hu : u ∈ (productionPinsCompact ℚ).U (Ideal.span {(n : 𝓞 ℚ)})) (hh : glFin (𝓞 ℚ) ℚ h = 1)
    (hpos : LanglandsTunnell.ratArchGL2 h ∈ GLPos (Fin 2) ℝ)
    (hg : g = globalPoints (𝓞 ℚ) ℚ γ * h * u) :
    (LanglandsTunnell.ratArchGL2 h).det.val = archDetNorm (default : InfinitePlace ℚ) g := by
  simp only [ratArchGL2_eq_ratArch] at hpos ⊢
  have huarch := glArch_eq_one_of_mem_productionPinsCompact_U ℚ _ hu
  have hufin : glFin (𝓞 ℚ) ℚ u ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ :=
    finiteLevelZero_le_finiteIntegralGL2 _ (finiteLevelOne_le_finiteLevelZero _ _ _
      (glFin_mem_finiteLevelOne_of_mem_productionPinsCompact_U ℚ _ hu))
  have hγ : glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ := by
    have hsplit : glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) = glFin (𝓞 ℚ) ℚ g * (glFin (𝓞 ℚ) ℚ u)⁻¹ := by
      rw [hg, map_mul, map_mul, hh, mul_one, mul_inv_cancel_right]
    rw [hsplit]
    exact Subgroup.mul_mem _ hgint (Subgroup.inv_mem _ hufin)
  have habs : |(((GeneralLinearGroup.det γ : ℚˣ) : ℚ) : ℝ)| = 1 := by
    exact_mod_cast abs_det_eq_one_of_glFin_mem_finiteIntegralGL2 hγ
  have hpos' : 0 < (ratArch h).det.val := hpos
  rw [archDetNorm_default_eq, hg, LanglandsTunnell.RatArch.ratArch_mul,
    LanglandsTunnell.RatArch.ratArch_mul,
    LanglandsTunnell.RatArch.ratArch_eq_one_of_glArch_eq_one huarch,
    mul_one, map_mul, Units.val_mul, abs_mul, det_ratArch_globalPoints, habs, one_mul, abs_of_pos hpos']

private theorem norm_weightOneLift_le_of_mem_D {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (C : ℝ) (hC : ∀ τ : ℍ, ‖f τ‖ ≤ C / τ.im ^ (((1 : ℤ) : ℝ) / 2))
    {g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} (hgD : g ∈ (productionPinsCompact ℚ).D) :
    ‖weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f g‖ ≤ C * Real.sqrt 2 := by
  have hN : Ideal.span {(n : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  obtain ⟨γ, h, u, hu, hh, hpos, hg⟩ := hasWeightOneDecomp_of_ne_bot hN g
  rw [weightOneLift_eq hn f hf g γ h u hu hh hpos hg]
  have hC0 : 0 ≤ C := by
    have h1 := hC UpperHalfPlane.I
    rw [UpperHalfPlane.I_im, Real.one_rpow, div_one] at h1
    exact (norm_nonneg _).trans h1
  have hdetpos : 0 < (LanglandsTunnell.ratArchGL2 h).det.val := hpos
  have hD := mem_centreCutSiegelSet_iff.mp hgD
  have hwin : archDetNorm (default : InfinitePlace ℚ) g ∈ Set.Icc (1 / 2 : ℝ) 2 := hD.2.2.2 default
  have hdet := det_ratArch_eq_archDetNorm hD.1 hu hh hpos hg
  calc ‖weightOneArchLift f (LanglandsTunnell.ratArchGL2 h)‖
      ≤ C * Real.sqrt (LanglandsTunnell.ratArchGL2 h).det.val :=
        norm_weightOneArchLift_le f C hC _ hdetpos
    _ ≤ C * Real.sqrt 2 := by
        apply mul_le_mul_of_nonneg_left _ hC0
        apply Real.sqrt_le_sqrt
        rw [hdet]
        exact hwin.2

/-! ## Continuity and `L²`-membership of the lift

The pin's `P2GProbe.R7` block, second half. Continuity is local: near `g₀` the lift is exactly
`weightOneArchLift f (ratArch h₀ * ratArch (g₀⁻¹ g))` on the open set where `g₀⁻¹ g` is at level `n`
and the determinant is positive; `L²`-membership then follows from the window bound above. -/

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

set_option linter.style.haveILetI false in
private theorem memLp_two_weightOneLift {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ) (hf_cont : Continuous f)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (C : ℝ) (hC : ∀ τ : ℍ, ‖f τ‖ ≤ C / τ.im ^ (((1 : ℤ) : ℝ) / 2)) :
    letI := (productionPinsCompact ℚ).mS
    MemLp (weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f) 2
      (((productionPinsCompact ℚ).μ).restrict (productionPinsCompact ℚ).D) := by
  letI := (productionPinsCompact ℚ).mS
  have : BorelSpace (GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :=
    NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 ℚ) ℚ
  have : IsFiniteMeasure (((productionPinsCompact ℚ).μ).restrict (productionPinsCompact ℚ).D) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (productionPinsCompact_μ_D_pos_lt_top ℚ).2⟩
  refine MemLp.of_bound (continuous_weightOneLift hn f hf_cont hf).aestronglyMeasurable (C * Real.sqrt 2) ?_
  exact ae_restrict_of_forall_mem (measurableSet_productionPinsCompact_D ℚ)
    fun g hg => norm_weightOneLift_le_of_mem_D hn f hf C hC hg

/-! ## The point at which the lift is nonzero

The pin's `P2GProbe.Alpha` block: the Iwasawa matrix `archMat τ`, the archimedean point
`archPoint τ` of `GL₂(𝔸_ℚ)` that projects to it, and `weightOneLift` at that point, which is
`im τ · f τ` — nonzero as soon as `f` is not identically zero. -/

private noncomputable def archMat (τ : ℍ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![τ.im, τ.re; 0, 1]
    (by rw [Matrix.det_fin_two_of]; simpa using τ.im_ne_zero)

private theorem coe_archMat (τ : ℍ) :
    ((archMat τ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![τ.im, τ.re; 0, 1] := rfl

private theorem det_archMat_pos (τ : ℍ) : 0 < (archMat τ).det.val := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_archMat, Matrix.det_fin_two_of]
  simpa using τ.im_pos

private noncomputable def ratArchEquiv :
    (default : InfinitePlace ℚ).Completion ≃+* ℝ :=
  InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)

private noncomputable def archPoint (τ : ℍ) : AdelicGL2 (𝓞 ℚ) ℚ :=
  adelicArchGLIncl ℚ (archGLIncl ℚ default
    (Matrix.GeneralLinearGroup.map (ratArchEquiv.symm : ℝ ≃+* _).toRingHom (archMat τ)))

private theorem glFin_archPoint (τ : ℍ) : NumberField.AdelicLevel.glFin (𝓞 ℚ) ℚ (archPoint τ) = 1 :=
  glFin_adelicArchGLIncl ℚ _

private theorem ratArch_archPoint (τ : ℍ) : ratArch (archPoint τ) = archMat τ := by
  unfold ratArch archPoint
  rw [glArch_adelicArchGLIncl, archComponent_archGLIncl_self]
  ext i j
  simp [ratArchEquiv]

private theorem weightOneLift_exists_ne_zero {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (hf0 : ∃ τ : ℍ, f τ ≠ 0) :
    ∃ g : AdelicGL2 (𝓞 ℚ) ℚ, weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f g ≠ 0 := by
  obtain ⟨τ, hτ⟩ := hf0
  refine ⟨archPoint τ, ?_⟩
  have h1 : weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f (1 * archPoint τ)
      = weightOneArchLift f (ratArch 1 * ratArch (archPoint τ)) :=
    weightOneLift_mul_eq hn f hf (g₀ := 1) (γ₀ := 1) (h₀ := 1) (u₀ := 1)
      (Subgroup.one_mem _) (map_one _) (by simp) (archPoint τ)
      (by rw [glFin_archPoint]; exact Subgroup.one_mem _)
      (by rw [ratArch_one, one_mul, ratArch_archPoint]; exact det_archMat_pos τ)
  rw [one_mul] at h1
  rw [h1, ratArch_one, one_mul, ratArch_archPoint,
    weightOneArchLift_iwasawa f τ (archMat τ) (coe_archMat τ)]
  exact mul_ne_zero (by exact_mod_cast τ.im_ne_zero) hτ

/-! ## The public helpers of the pin's `Ws1.L1` block

`exists_prime_mem` and `absNorm_asIdeal_eq` describe the residue field of a height-one prime as a
prime field `𝔽_p`, and `slash_eq`/`slash_eq_smul_of_hasNebentypus` are the two slash laws of a
level-`N` form. The pin states `slash_eq` inside its stage namespace `Ws1.L1`, and the port keeps
that nesting: `LanglandsTunnell/WeightOneLiftNebentypus.lean` holds `DihedralWeightOne.slash_eq`
publicly, and a second public copy of that full name would make the two modules impossible to import
together (SET-AF97's consumer zone hit exactly that clash). -/

section PinPublic

variable {N : ℕ} [NeZero N]

theorem exists_prime_mem (v : HeightOneSpectrum (𝓞 ℚ)) : ∃ p : ℕ, p.Prime ∧ (p : 𝓞 ℚ) ∈ v.asIdeal := by
  have key : ∀ n : ℕ, (n : 𝓞 ℚ) ∈ v.asIdeal → n ≠ 1 → n ≠ 0 → ∃ p : ℕ, p.Prime ∧ (p : 𝓞 ℚ) ∈ v.asIdeal := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn h1 h0
      obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd h1
      obtain ⟨k, rfl⟩ := hpn
      have hk0 : k ≠ 0 := by rintro rfl; exact h0 (by simp)
      rw [Nat.cast_mul] at hn
      rcases v.isPrime.mem_or_mem hn with h | h
      · exact ⟨p, hp, h⟩
      · by_cases hk1 : k = 1
        · subst hk1
          exact absurd (v.asIdeal.eq_top_of_isUnit_mem (by simpa using h) isUnit_one) v.isPrime.ne_top
        · exact ih k (lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hk0) hp.one_lt) h hk1 hk0
  refine key (Ideal.absNorm v.asIdeal) (Ideal.absNorm_mem v.asIdeal) ?_ ?_
  · rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  · rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot

theorem absNorm_asIdeal_eq {p : ℕ} (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (p : 𝓞 ℚ) ∈ v.asIdeal) :
    Ideal.absNorm v.asIdeal = p := by
  have hdvd : Ideal.absNorm v.asIdeal ∣ p := by
    have h1 : Ideal.span {(p : 𝓞 ℚ)} ≤ v.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr hv
    have h2 := Ideal.absNorm_dvd_absNorm_of_le h1
    have h3 : Ideal.absNorm (Ideal.span {(p : 𝓞 ℚ)}) = p := by
      rw [Ideal.absNorm_span_singleton]
      have : (p : 𝓞 ℚ) = algebraMap ℤ (𝓞 ℚ) (p : ℤ) := by simp
      rw [this, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Module.finrank_self, pow_one, Int.natAbs_natCast]
    rwa [h3] at h2
  have hne1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  rcases (Nat.dvd_prime hp).mp hdvd with h | h
  · exact absurd h hne1
  · exact h

namespace Ws1.L1

theorem slash_eq (f : CuspForm (Gamma1 N) 1) (ε : SL(2, ℤ)) (hε : ε ∈ Gamma1 N) :
    (⇑f) ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = ⇑f :=
  SlashInvariantForm.slash_action_eqn f (ε : GL (Fin 2) ℝ) ⟨ε, hε, rfl⟩

end Ws1.L1

end PinPublic

/-! ## The two headlines -/

set_option linter.style.haveILetI false in
theorem exists_smoothCuspRealizationAt_productionPinsGeneral_toFun_eq_weightOneLift_of_isPrimitiveForm
    (N : ℕ) [NeZero N] (ψ : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) 1)
    (hf : CuspForm.IsPrimitiveForm ψ f) :
    ∃ (Φ : HeckeEigensystem ℚ ℂ) (R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ.toRawCentral),
      R.toFun = weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑f) ∧
      IsGenuineCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ.toRawCentral R ∧
      IsBoundedOnSiegelWindows ℚ R.toFun ∧
      ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → ¬ p ∣ N →
        ∀ v : HeightOneSpectrum (𝓞 ℚ), (p : 𝓞 ℚ) ∈ v.asIdeal →
          Φ.a v = ModularFormClass.qCoeff f p ∧ Φ.b v = ψ (p : ZMod N) := by
  classical
  have hN : N ≠ 0 := NeZero.ne N
  have hNI : Ideal.span {(N : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hN

  let Φ : HeckeEigensystem ℚ ℂ :=
    { level := Ideal.span {(N : 𝓞 ℚ)}
      level_ne_bot := hNI
      a := fun v => ModularFormClass.qCoeff f (Ideal.absNorm v.asIdeal)
      b := fun v => ψ ((Ideal.absNorm v.asIdeal : ℕ) : ZMod N) }

  have hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑f) := ModularFormClass.holo f
  have hcont : Continuous (⇑f) := hhol.continuous
  have hsl : ∀ ε : SL(2, ℤ), ε ∈ Gamma1 N → (⇑f) ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = ⇑f := Ws1.L1.slash_eq f
  have hχ : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 N →
      (⇑f) ∣[(1 : ℤ)] (γ : GL (Fin 2) ℝ) = ψ ((γ 1 1 : ℤ) : ZMod N) • (⇑f) :=
    fun γ hγ => slash_eq_smul_of_hasNebentypus (F := f) hf.1.hasNebentypus hγ
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ τ : UpperHalfPlane, ‖f τ‖ ≤ C / τ.im ^ (((1 : ℤ) : ℝ) / 2) :=
    CuspFormClass.exists_bound f
  have hzero : ∀ δ : SL(2, ℤ), IsZeroAtImInfty ((⇑f) ∣[(1 : ℤ)] (δ : GL (Fin 2) ℝ)) :=
    fun δ => CuspFormClass.zero_at_infty_slash f δ

  have hΓ : (1 : ℝ) ∈ (Gamma1 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples 1
  have hf0 : ∃ τ : UpperHalfPlane, f τ ≠ 0 := by
    by_contra h
    push Not at h
    have han := ModularFormClass.analyticAt_cuspFunction_zero f one_pos hΓ
    have h1 := hf.1.qCoeff_one
    have hzeroFn : (⇑f : UpperHalfPlane → ℂ) = (0 : ℂ) • (⇑f) := by
      ext τ; simp [h τ]
    have h2 : ModularFormClass.qCoeff ((0 : ℂ) • (⇑f)) 1 = 0 := by
      simp only [ModularFormClass.qCoeff]
      rw [UpperHalfPlane.qExpansion_smul han]
      simp
    rw [← hzeroFn] at h2
    rw [h2] at h1
    exact zero_ne_one h1

  set S : Finset (HeightOneSpectrum (𝓞 ℚ)) := (Ideal.finite_factors hNI).toFinset with hSdef
  have hS : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ¬ v.asIdeal ∣ Ideal.span {(N : 𝓞 ℚ)} :=
    fun v hv h => hv ((Set.Finite.mem_toFinset _).2 h)

  have hgood : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      ∃ p : ℕ, p.Prime ∧ (p : 𝓞 ℚ) ∈ v.asIdeal ∧ Ideal.absNorm v.asIdeal = p ∧ ¬ p ∣ N := by
    intro v hv
    obtain ⟨p, hp, hpv⟩ := exists_prime_mem v
    refine ⟨p, hp, hpv, absNorm_asIdeal_eq hp v hpv, fun h => hS v hv ?_⟩
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    obtain ⟨m, rfl⟩ := h
    rw [Nat.cast_mul]
    exact v.asIdeal.mul_mem_right _ hpv

  have hdiag1 : ModularForm.heckeDiagMatrix 1 = 1 := by
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [ModularForm.val_heckeDiagMatrix one_ne_zero]
    fin_cases i <;> fin_cases j <;> simp
  have hT : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      ModularForm.heckeU 1 (Ideal.absNorm v.asIdeal) (⇑f)
          + ψ ((Ideal.absNorm v.asIdeal : ℕ) : ZMod N) •
              ((⇑f) ∣[(1 : ℤ)] ModularForm.heckeDiagMatrix (Ideal.absNorm v.asIdeal))
        = Φ.toRawCentral.a v • (⇑f) := by
    intro v hv
    obtain ⟨p, hp, hpv, hnorm, hpN⟩ := hgood v hv
    have h2 := CuspForm.IsEigenformWith.heckeU_add_smul_slash_heckeDiagMatrix_degeneracy_eq_qCoeff_smul
      N 1 (L := N) dvd_rfl hf.1 (fun _ => f)
      (fun d hd τ => by
        rw [Nat.div_self (Nat.pos_of_ne_zero hN)] at hd
        rw [Nat.dvd_one.1 hd, hdiag1, one_smul])
      hp hpN (d := 1) (by rw [Nat.div_self (Nat.pos_of_ne_zero hN)])
    have ha : Φ.toRawCentral.a v = ModularFormClass.qCoeff (⇑f) p := by
      simp [Φ, HeckeEigensystem.toRawCentral_a, hnorm]
    rw [ha, hnorm]
    simpa using h2

  set ξ : (productionPinsCompact ℚ).Z →* ℂˣ :=
    ((DirichletCharacter.dirichletIdeleChar ψ *
        (Units.map (Complex.ofRealHom.toMonoidHom.comp NNReal.toRealHom.toMonoidHom)).comp
          (MeasureTheory.distribHaarChar (AdeleRing (𝓞 ℚ) ℚ)).toHomUnits).comp
      (productionPinsCompact ℚ).Z.subtype)
  have hξ := LanglandsTunnell.weightOneLift_centralScalar_mul hN (⇑f) hsl ψ hχ

  have hb : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      Φ.toRawCentral.b v = ((((DirichletCharacter.dirichletIdeleChar ψ *
          (Units.map (Complex.ofRealHom.toMonoidHom.comp NNReal.toRealHom.toMonoidHom)).comp
            (MeasureTheory.distribHaarChar (AdeleRing (𝓞 ℚ) ℚ)).toHomUnits).comp
          Matrix.GeneralLinearGroup.det) ((productionPinsCompact ℚ).gen v) : ℂˣ) : ℂ) := by
    intro v hv
    rw [LanglandsTunnell.dirichletIdeleChar_mul_modulus_det_gen ψ S hS v hv, HeckeEigensystem.toRawCentral_b,
      mul_comm]
    rfl

  have hodd : Odd (classNumber ℚ) := by rw [Rat.classNumber_eq]; exact odd_one
  rw [productionPinsGeneral_eq_compact_of_odd ℚ hodd]

  refine ⟨Φ,
    { toFun := weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑f)
      exists_ne_zero := weightOneLift_exists_ne_zero hN (⇑f) hsl hf0
      centralChar := ξ
      smoothCusp := by
        letI := (productionPinsCompact ℚ).mS
        letI : MeasureTheory.MeasureSpace (AdelicGL2 (𝓞 ℚ) ℚ) := ⟨(productionPinsCompact ℚ).μ⟩
        exact ⟨⟨⟨⟨fun γ g => weightOneLift_globalPoints_mul hN (⇑f) hsl γ g, hξ⟩,
          memLp_two_weightOneLift hN (⇑f) hcont hsl C hC⟩,
          LanglandsTunnell.isCuspidalFn_weightOneLift hN (⇑f) hhol hsl C hC hzero⟩,
          LanglandsTunnell.isKfSmooth_weightOneLift hN (⇑f) hsl⟩
      level_invariant := fun g u hu =>
        weightOneLift_mul_of_mem_U hN (⇑f) hsl g hu
      exceptionalSet := S
      hecke_eigen := LanglandsTunnell.isHeckeCosetEigenfunctionAt_weightOneLift hN (⇑f) hsl ψ hχ
        Φ.toRawCentral rfl S hS hT
      central_eigen := LanglandsTunnell.weightOneLift_centralScalar_det_gen_mul hN (⇑f) hsl ψ hχ
        Φ.toRawCentral S hb }, rfl, ?_, ?_, ?_⟩
  · exact continuous_weightOneLift hN (⇑f) hcont hsl
  · exact LanglandsTunnell.isBoundedOnSiegelWindows_weightOneLift (⇑f) C hC
  · refine ⟨∅, fun p hp _ hpN v hv => ?_⟩
    have hnorm : Ideal.absNorm v.asIdeal = p := absNorm_asIdeal_eq hp v hv
    exact ⟨by simp [Φ, hnorm], by simp [Φ, hnorm]⟩

theorem weightOneLift_ne_zero_and_apply_mul_finEmbed_eq_of_isPrimitiveForm
    (N : ℕ) [NeZero N] (ψ : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) 1)
    (hf : CuspForm.IsPrimitiveForm ψ f) :
    weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑f) ≠ 0 ∧
    ∀ g ∈ NumberField.AdelicLevel.finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel N),
      ∀ x, weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑f) (x * AdelicDock.finEmbed (𝓞 ℚ) ℚ g) =
        weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑f) x := by
  classical
  have hN : N ≠ 0 := NeZero.ne N
  have hsl : ∀ ε : SL(2, ℤ), ε ∈ Gamma1 N → (⇑f) ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = ⇑f := Ws1.L1.slash_eq f

  have hΓ : (1 : ℝ) ∈ (Gamma1 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples 1
  have hf0 : ∃ τ : UpperHalfPlane, f τ ≠ 0 := by
    by_contra h
    push Not at h
    have han := ModularFormClass.analyticAt_cuspFunction_zero f one_pos hΓ
    have h1 := hf.1.qCoeff_one
    have hzeroFn : (⇑f : UpperHalfPlane → ℂ) = (0 : ℂ) • (⇑f) := by
      ext τ; simp [h τ]
    have h2 : ModularFormClass.qCoeff ((0 : ℂ) • (⇑f)) 1 = 0 := by
      simp only [ModularFormClass.qCoeff]
      rw [UpperHalfPlane.qExpansion_smul han]
      simp
    rw [← hzeroFn] at h2
    rw [h2] at h1
    exact zero_ne_one h1
  refine ⟨?_, fun g hg x => ?_⟩
  · obtain ⟨g, hg⟩ := weightOneLift_exists_ne_zero hN (⇑f) hsl hf0
    exact fun h0 => hg (by rw [h0]; rfl)
  · have hu : AdelicDock.finEmbed (𝓞 ℚ) ℚ g ∈ (productionPinsCompact ℚ).U (Ideal.span {(N : 𝓞 ℚ)}) := by
      rw [mem_U_iff, AdelicDock.glFin_finEmbed, AdelicDock.glArch_finEmbed]
      exact ⟨hg, rfl⟩
    exact weightOneLift_mul_of_mem_U hN (⇑f) hsl x hu

end DihedralWeightOne

end
