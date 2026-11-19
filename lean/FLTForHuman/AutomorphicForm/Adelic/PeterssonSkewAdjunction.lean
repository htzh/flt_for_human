/-
  Archimedean derivatives and Casimir operators against the Petersson pairing.

  Four rows of the formal adjointness of the archimedean differential operators for the Petersson
  pairing on a fundamental domain of the determinant-norm slab, two per archimedean place type:

  * `setIntegral_archDerivAt_mul_conj_add_eq_zero_of_isFundamentalDomain` and its complex companion: the
    directional derivative `archDerivAt X` (`archDerivAtComplex X`) is **skew-adjoint** — the integral of
    `X x * conj x' + x * conj (X x')` over the fundamental domain vanishes. It is the derivative of
    `x * conj x'`, so the statement says the boundary term of the archimedean flow dies on a fundamental
    domain;
  * `setIntegral_archCasimirAt_mul_conj_eq_and_lower_adjoint_of_isFundamentalDomain` and its complex
    companion: the Casimir operator is **self-adjoint**, and the raised and lowered combinations are
    adjoint to each other up to a sign — in the real case for `H`/`E`/`Fm`, in the complex case for
    `E`/`Fm` with the holomorphic `archDelAt` and the antiholomorphic `archDelBarAt`.

  All four rest on the same inputs: the archimedean flow preserves the slab's Haar measure
  (`NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar`), the slab's fundamental domain has finite
  measure (`AutomorphicForm/Adelic/Siegel/SlabVolume.lean`), and the functions are `GL₂(K)`-invariant and
  bounded with their derivatives on the slab.

  Transcribed from the four `S_` files below (pinned `aa2d8b3`, 385 + 392 + 270 + 476 lines). The pins are
  *flattened* files whose 22 public declarations each share a common prelude
  (`smulInvariantMeasure_restrict`, `preimage_subtype_mul_slab`, `dn_globalPoints_mul`, the `rel_*` family):
  it is transcribed once, and the four developments differ in the archimedean dictionary they use.

  Port deltas (statement text unchanged; `spec/check_port.py` is the authority):

  * The pins' search-stage namespaces (`UnitSymFlow25`, `UnitSymFlowC26`, `UnitSymAlg25`, `Ws50U1`) are
    replaced by the one subject namespace `AutomorphicForm.PeterssonSkewAdjunction`; the four rows keep
    their pin names at `AutomorphicForm.…`, as the scaffold has them.
  * **The shared prelude is transcribed once** (FR-0226's "port once"): `dn`, `slab`, `Γp`, `dn_mul`,
    `dn_globalPoints_mul`, `dn_subtype_mul`, `measurableSet_slab`, `preimage_subtype_mul_slab`,
    `smulInvariantMeasure_restrict`, `smulInvariantMeasure_slab`, `measurePreserving_mul_right'`,
    `integrable_mul_conj`, `slab` and the private `norm_mul_conj_le` appear in two, three or four of the
    pins each; each is declared once here, at the first pin's text. `slab` in particular is in all four
    pins with byte-identical text.
  * **Four engines are renamed, because a name cannot hold two statements**: every one of the four pins
    ends in an engine literally named `main` (pins `:273`, `:279`, `:64`, `:81`) with pairwise different
    statements. Pin 1's keeps the pin name; the others are `main_archDerivAtComplex`,
    `main_archCasimirAt`, `main_archCasimirAtComplex`. All four verify by `check_port`'s content-hash
    tier (a faithful rename needs no marker row, and no `own:` row is used in this module). Likewise
    pin 3 `:44` and pin 4 `:45` both declare `integral_lincomb`, with *different* statements (a three-term
    and a `Fin n`-term linear combination): pin 3's keeps the name, pin 4's is `integral_lincomb_fin`.
  * The pins' private `dA`/`dB`/`sw`/`dE` exist twice (once over `ℝ` at pin 1 `:30–54`, once over `ℂ` at
    pin 2 `:31–55`, where the second copy shadows the first inside its own file); the complex twins are
    renamed `dAC`/`dBC`/`swC`/`dEC` (`C` for the complex place, the port's recorded practice) and their
    relations `rel_EC`/`rel_FmC`/`rel_HC`. They are `private`: proof-side plumbing, not wire surface.
  * The pins' five `scoped instance` `Countable` declarations (pin 1 `:110`, `:113` and its twins) are not
    transcribed as instances, following the recorded decision on `Siegel/SlabVolume.lean`: they are instance
    plumbing, and the two places the argument needs countability state it locally, through the private
    `countable_Γp` (`Countable ↥(Γp K)`) and class-typed `have` binders (FR-0223).
  * `haveI` → `have` wherever the linter suggests it (FR-0223); the pins' `attribute [-…]` walls and
    `p2m_reactivate` lines are dropped, as is this port's practice.
  * **Imports added for premises the scaffold's closure lacked** (FR-0229): the pins' proofs also use
    `NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar` (`NumberTheory/AdelicHaar/MulRightInvariant.lean`,
    pins 1–2 `:186`), `AutomorphicForm.archDerivAt_commutator_of_isArchSmoothAt`
    (`AutomorphicForm/Adelic/ArchCasimir.lean`, pin 3 `:147`) and
    `AutomorphicForm.archDerivAtComplex_commutator_of_isArchSmoothAtComplex`
    (`AutomorphicForm/Adelic/ArchCasimirComplex.lean`, pin 4 `:249`) plus the complex derivative API
    (`ArchDerivCasimirComplexAPI.lean`, pin 4 `:57`, `:65`). None of the four modules was in the
    scaffold's 121-module closure; all four `.olean`s already existed.

  THE FOUR RENAMES (a Lean name holds one statement, and each of these pins has a twin):

  | port name | pin | pin line |
  |---|---|---:|
  | `main` | `UnitSymFlow25.main` (pin 1) | 273 |
  | `main_archDerivAtComplex` | `UnitSymFlowC26.main` (pin 2) | 279 |
  | `main_archCasimirAt` | `UnitSymAlg25.main` (pin 3) | 64 |
  | `main_archCasimirAtComplex` | `Ws50U1.main` (pin 4) | 81 |
  | `integral_lincomb` | pin 3's three-term form | 44 |
  | `integral_lincomb_fin` | pin 4's `Fin n`-term form, same pin name | 45 |

  All six verify at `spec/check_port.py`'s **content tier**: their statements are the pins' byte for byte, so
  the checker attributes them by `nhash` and no `spec/decl_markers.tsv` row is needed (0 `own`). Nothing else
  is renamed. Nothing is dropped or deferred: the four wire files carry 59 public declarations, four of which
  are the `solution` wrapper (FOLDED into the four rows), and the remaining 55 are satisfied by the 41 engine
  declarations here — the 14-declaration difference is the shared prelude declared once (`slab` ×4 → 1, and
  `dn`/`dn_globalPoints_mul`/`dn_mul`/`dn_subtype_mul`/`Γp`/`measurableSet_slab`/
  `preimage_subtype_mul_slab`/`smulInvariantMeasure_restrict`/`smulInvariantMeasure_slab`/
  `measurePreserving_mul_right'`/`integrable_mul_conj` ×2 → 1 each).

  DEDUP (gate 4, recorded rather than silenced): `dedup.py --within` reports **3 body-tier clusters**,
  `dA`/`dAC` (`:104`/`:130`), `dB`/`dBC` (`:110`/`:136`), `sw`/`swC` (`:116`/`:142`). Each is the pin's **own**
  ℝ/ℂ duplicate — pin 1 `:30–47` declares the three matrices over `ℝ`, pin 2 `:31–48` over `ℂ`, under the same
  private names in two files — transcribed at those names as the order asks. They cannot be merged by the
  port: the bodies are the same numerals in different scalar rings, which this tier's normaliser erases,
  while the declarations are not interchangeable (`rel_E` at pin 1 `:56` is a `GL (Fin 2) ℝ` identity and
  `rel_EC` at pin 2 `:57` a `GL (Fin 2) ℂ` one; and the `H`-direction needs `Real.exp` against `Complex.exp`
  so `dE`/`dEC` stay apart for that reason and are not clustered). This is the false-positive class
  `dedup.py`'s own docstring records for instance arguments: it is private proof plumbing, invisible to
  every consumer.

  HEARTBEAT PROBE (gate 6 — a measurement, the module carries **no** `set_option maxHeartbeats`):
  `lake env lean -DautoImplicit=false -DmaxHeartbeats=N` is silent at the edit-loop cap **N = 200000**, still
  silent at **N = 120000**, and fails at **N = 60000** — both halves measured, so the pair is 120000/60000.
  The floor is a single declaration: **`main_archCasimirAtComplex`** (pin 4 `:81`, the largest of the four
  rows). At 60000 the first abort is `whnf` at the `simp only` of its third conjunct (`:1328` of this file);
  at 30000 the first abort moves earlier, to the `simp only` of its second conjunct (`:1252`), and no
  declaration outside that engine is ever the first to fail. A future wave reopening pin 4's engine should
  quote 120000 as the natural cost and 60000 as the abort point; the four rows themselves are one-line
  applications and cost nothing.

  spec-pin: P2M/Sol/S_AutomorphicForm_setIntegral_archDerivAt_mul_conj_add_eq_zero_of_isFundamentalDomain.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_setIntegral_archDerivAtComplex_mul_conj_add_eq_zero_of_isFundamentalDomain.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_setIntegral_archCasimirAt_mul_conj_eq_and_lower_adjoint_of_isFundamentalDomain.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_setIntegral_archCasimirAtComplex_mul_conj_eq_and_archDelAt_adjoint_of_isFundamentalDomain.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.ArchDerivCasimir
import FLTForHuman.AutomorphicForm.Adelic.ArchDerivCasimirComplex
import FLTForHuman.AutomorphicForm.Adelic.ArchDerivCasimirComplexAPI
import FLTForHuman.AutomorphicForm.Adelic.ArchCasimir
import FLTForHuman.AutomorphicForm.Adelic.ArchCasimirComplex
import FLTForHuman.AutomorphicForm.Adelic.Siegel.SlabVolume
import FLTForHuman.AutomorphicForm.Adelic.IdeleNormDet
import FLTForHuman.NumberTheory.NumberField.TateGlobalIdeleNormDet
import FLTForHuman.NumberTheory.AdelicHaar.GeneralLinear
import FLTForHuman.NumberTheory.AdelicHaar.MulRightInvariant
import Mathlib.Analysis.Calculus.Deriv.Star

set_option autoImplicit false

noncomputable section

open MeasureTheory Set NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.TateGlobal
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped Classical ENNReal NNReal Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace AutomorphicForm

namespace PeterssonSkewAdjunction

/-! ## The determinant-one flows and their complex twins

The four pinned matrix relations that make `det` of an archimedean flow trivial. Private: proof-side
plumbing. Pin 1 `:30–75` (over `ℝ`) and pin 2 `:31–78` (over `ℂ`), the complex copies renamed `…C`. -/

section DetOne

private def dA : GL (Fin 2) ℝ where
  val := !![1, 0; 0, 2]
  inv := !![1, 0; 0, 2⁻¹]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private def dB : GL (Fin 2) ℝ where
  val := !![2, 0; 0, 1]
  inv := !![2⁻¹, 0; 0, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private def sw : GL (Fin 2) ℝ where
  val := !![0, 1; 1, 0]
  inv := !![0, 1; 1, 0]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private def dE (t : ℝ) : GL (Fin 2) ℝ where
  val := !![Real.exp (-t), 0; 0, 1]
  inv := !![Real.exp t, 0; 0, 1]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ← Real.exp_add]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ← Real.exp_add]

private def dAC : GL (Fin 2) ℂ where
  val := !![1, 0; 0, 2]
  inv := !![1, 0; 0, 2⁻¹]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private def dBC : GL (Fin 2) ℂ where
  val := !![2, 0; 0, 1]
  inv := !![2⁻¹, 0; 0, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private def swC : GL (Fin 2) ℂ where
  val := !![0, 1; 1, 0]
  inv := !![0, 1; 1, 0]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private def dEC (z : ℂ) : GL (Fin 2) ℂ where
  val := !![Complex.exp (-z), 0; 0, 1]
  inv := !![Complex.exp z, 0; 0, 1]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ← Complex.exp_add]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ← Complex.exp_add]

private theorem rel_E (t : ℝ) : unipotentGL2 t * unipotentGL2 t * dB = dB * unipotentGL2 t := by
  apply Units.ext
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [dB, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

private theorem rel_Fm (t : ℝ) : lowerUnipotentGL2 t * lowerUnipotentGL2 t * dA = dA * lowerUnipotentGL2 t := by
  apply Units.ext
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [dA, lowerUnipotentGL2, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

private theorem rel_H (t : ℝ) : splitTorusGL2 t * dE t * sw = sw * dE t := by
  apply Units.ext
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [dE, sw, splitTorusGL2, Matrix.mul_apply, Fin.sum_univ_two, ← Real.exp_add]

private theorem rel_EC (z : ℂ) : unipotentGL2 z * unipotentGL2 z * dBC = dBC * unipotentGL2 z := by
  apply Units.ext
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [dBC, Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem rel_FmC (z : ℂ) :
    lowerUnipotentGL2 z * lowerUnipotentGL2 z * dAC = dAC * lowerUnipotentGL2 z := by
  apply Units.ext
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [dAC, lowerUnipotentGL2, Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem rel_HC (z : ℂ) : splitTorusGL2Complex z * dEC z * swC = swC * dEC z := by
  apply Units.ext
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [dEC, swC, splitTorusGL2Complex, Matrix.mul_apply, Fin.sum_univ_two, ← Complex.exp_add]

private theorem map_eq_one_of_rel {G C : Type*} [Group G] [CommGroup C] (ψ : G →* C) {m u a : G}
    (h : m * u * a = a * u) : ψ m = 1 := by
  have h' := congrArg ψ h
  rw [map_mul, map_mul, map_mul, mul_comm (ψ a) (ψ u), mul_assoc] at h'
  exact mul_eq_right.mp h'

variable {K : Type} [Field K] [NumberField K]

theorem det_archFlowAt {w : InfinitePlace K} (hw : w.IsReal) (d : ArchDir) (t : ℝ) :
    Matrix.GeneralLinearGroup.det (archFlowAt hw d t) = 1 := by
  let ψ : GL (Fin 2) ℝ →* (AdeleRing (𝓞 K) K)ˣ := (Matrix.GeneralLinearGroup.det).comp (archRealGLAt hw)
  show ψ (archFlowMatrix d t) = 1
  cases d
  · exact map_eq_one_of_rel ψ (rel_H t)
  · exact map_eq_one_of_rel ψ (rel_E t)
  · exact map_eq_one_of_rel ψ (rel_Fm t)

theorem archFlowAt_inv {w : InfinitePlace K} (hw : w.IsReal) (d : ArchDir) (t : ℝ) :
    (archFlowAt hw d t)⁻¹ = archFlowAt hw d (-t) :=
  inv_eq_of_mul_eq_one_right (by rw [← archFlowAt_add, add_neg_cancel, archFlowAt_zero])

theorem det_archFlowAtComplex {w : InfinitePlace K} (hw : w.IsComplex) (d : ArchDirComplex) (t : ℝ) :
    Matrix.GeneralLinearGroup.det (archFlowAtComplex hw d t) = 1 := by
  let ψ : GL (Fin 2) ℂ →* (AdeleRing (𝓞 K) K)ˣ := (Matrix.GeneralLinearGroup.det).comp (archComplexGLAt hw)
  show ψ (archFlowMatrixComplex d t) = 1
  cases d
  · exact map_eq_one_of_rel ψ (rel_HC (t : ℂ))
  · exact map_eq_one_of_rel ψ (rel_EC (t : ℂ))
  · exact map_eq_one_of_rel ψ (rel_FmC (t : ℂ))
  · exact map_eq_one_of_rel ψ (rel_HC ((t : ℂ) * Complex.I))
  · exact map_eq_one_of_rel ψ (rel_EC ((t : ℂ) * Complex.I))
  · exact map_eq_one_of_rel ψ (rel_FmC ((t : ℂ) * Complex.I))

theorem archFlowAtComplex_inv {w : InfinitePlace K} (hw : w.IsComplex) (d : ArchDirComplex) (t : ℝ) :
    (archFlowAtComplex hw d t)⁻¹ = archFlowAtComplex hw d (-t) :=
  inv_eq_of_mul_eq_one_right (by rw [← archFlowAtComplex_add, add_neg_cancel, archFlowAtComplex_zero])

end DetOne

/-! ## Two boundedness helpers (private, pin 1 `:259–265`) -/

section Bounds

private theorem norm_mul_conj_le {a b : ℂ} {B : ℝ} (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) : ‖a * conj b‖ ≤ B * B := by
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul ha hb (norm_nonneg _) ((norm_nonneg a).trans ha)

private theorem norm_add_le' {a b c d : ℂ} {B : ℝ} (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ B)
    (hd : ‖d‖ ≤ B) : ‖a * conj b + c * conj d‖ ≤ B * B + B * B :=
  (norm_add_le _ _).trans (add_le_add (norm_mul_conj_le ha hb) (norm_mul_conj_le hc hd))

end Bounds

/-! ## The slab and its measure -/

section Slab

variable {K : Type} [Field K] [NumberField K]

attribute [local instance] NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

abbrev dn (g : AdelicGL2 (𝓞 K) K) : ℝ := ideleNorm K (Matrix.GeneralLinearGroup.det g)

abbrev slab (K : Type) [Field K] [NumberField K] (a b : ℝ) : Set (AdelicGL2 (𝓞 K) K) :=
  {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}

abbrev Γp (K : Type) [Field K] [NumberField K] : Subgroup (AdelicGL2 (𝓞 K) K) :=
  (globalPoints (𝓞 K) K).range

private theorem countable_Γp : Countable ↥(Γp K) := by
  have : Countable K := (Module.finBasis ℚ K).equivFun.toEquiv.injective.countable
  have : Countable (Matrix (Fin 2) (Fin 2) K) := inferInstanceAs (Countable (Fin 2 → Fin 2 → K))
  have : Countable (GL (Fin 2) K) := Units.val_injective.countable
  exact (MonoidHom.rangeRestrict_surjective (globalPoints (𝓞 K) K)).countable

theorem dn_mul (g h : AdelicGL2 (𝓞 K) K) : dn (g * h) = dn g * dn h := by
  show ideleNorm K _ = _
  rw [map_mul, ideleNorm_mul]

theorem dn_globalPoints_mul (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K) :
    dn (globalPoints (𝓞 K) K γ * g) = dn g := by
  rw [dn_mul]
  show ideleNorm K (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 K) K γ)) * dn g = dn g
  rw [AutomorphicForm.ideleNorm_det_globalPoints, one_mul]

theorem dn_subtype_mul (γ : ↥(Γp K)) (g : AdelicGL2 (𝓞 K) K) : dn ((γ : AdelicGL2 (𝓞 K) K) * g) = dn g := by
  obtain ⟨_, γ', rfl⟩ := γ
  exact dn_globalPoints_mul γ' g

theorem measurableSet_slab (a b : ℝ) : MeasurableSet (slab K a b) :=
  NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc K a b

theorem preimage_subtype_mul_slab (γ : ↥(Γp K)) (a b : ℝ) :
    (fun g : AdelicGL2 (𝓞 K) K => (γ : AdelicGL2 (𝓞 K) K) * g) ⁻¹' slab K a b = slab K a b := by
  ext g
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  rw [show ideleNorm K (Matrix.GeneralLinearGroup.det ((γ : AdelicGL2 (𝓞 K) K) * g)) = dn g from
    dn_subtype_mul γ g]

theorem smulInvariantMeasure_restrict (Γ : Subgroup (AdelicGL2 (𝓞 K) K))
    (μ : Measure (AdelicGL2 (𝓞 K) K)) [SMulInvariantMeasure ↥Γ (AdelicGL2 (𝓞 K) K) μ]
    {T : Set (AdelicGL2 (𝓞 K) K)} (hT : MeasurableSet T)
    (hΓT : ∀ γ : ↥Γ, (fun g : AdelicGL2 (𝓞 K) K => γ • g) ⁻¹' T = T) :
    SMulInvariantMeasure ↥Γ (AdelicGL2 (𝓞 K) K) (μ.restrict T) := by
  refine ⟨fun γ A hA => ?_⟩
  rw [Measure.restrict_apply (hA.preimage (measurable_const_smul _)), Measure.restrict_apply hA]
  conv_lhs => rw [← hΓT γ, ← Set.preimage_inter]
  exact SMulInvariantMeasure.measure_preimage_smul γ (hA.inter hT)

theorem smulInvariantMeasure_slab (a b : ℝ) :
    SMulInvariantMeasure ↥(Γp K) (AdelicGL2 (𝓞 K) K) ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K a b)) :=
  smulInvariantMeasure_restrict (Γp K) (adelicGLHaar (Fin 2) (𝓞 K) K) (measurableSet_slab a b)
    (fun γ => preimage_subtype_mul_slab γ a b)

theorem measurePreserving_mul_right' (k : AdelicGL2 (𝓞 K) K) :
    MeasurePreserving (fun g : AdelicGL2 (𝓞 K) K => g * k)
      (adelicGLHaar (Fin 2) (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K) := by
  have := NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar K
  exact measurePreserving_mul_right (adelicGLHaar (Fin 2) (𝓞 K) K) k

theorem integrable_mul_conj {a b : ℝ} {𝓕 : Set (AdelicGL2 (𝓞 K) K)} (h𝓕m : MeasurableSet 𝓕)
    (h𝓕s : 𝓕 ⊆ slab K a b) (hfin : adelicGLHaar (Fin 2) (𝓞 K) K 𝓕 < ⊤)
    {u v : AdelicGL2 (𝓞 K) K → ℂ} (hu : Continuous u) (hv : Continuous v) {B : ℝ}
    (hbu : ∀ g ∈ slab K a b, ‖u g‖ ≤ B) (hbv : ∀ g ∈ slab K a b, ‖v g‖ ≤ B) :
    Integrable (fun g => u g * conj (v g)) ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict 𝓕) :=
  Measure.integrableOn_of_bounded (M := B * B) hfin.ne (hu.mul (Complex.continuous_conj.comp hv)).aestronglyMeasurable
    ((ae_restrict_iff' h𝓕m).mpr (Filter.Eventually.of_forall fun g hg =>
      norm_mul_conj_le (hbu g (h𝓕s hg)) (hbv g (h𝓕s hg))))

theorem integral_lincomb {α : Type*} [MeasurableSpace α] (ν : Measure α) {f₁ f₂ f₃ : α → ℂ}
    (h₁ : Integrable f₁ ν) (h₂ : Integrable f₂ ν) (h₃ : Integrable f₃ ν) (a b c : ℂ) :
    ∫ g, (a * f₁ g + b * f₂ g + c * f₃ g) ∂ν = a * ∫ g, f₁ g ∂ν + b * ∫ g, f₂ g ∂ν + c * ∫ g, f₃ g ∂ν := by
  have h₁' : Integrable (fun g => a * f₁ g) ν := h₁.const_mul a
  have h₂' : Integrable (fun g => b * f₂ g) ν := h₂.const_mul b
  have h₃' : Integrable (fun g => c * f₃ g) ν := h₃.const_mul c
  have h12 : Integrable (fun g => a * f₁ g + b * f₂ g) ν := h₁'.add h₂'
  rw [integral_add h12 h₃', integral_add h₁' h₂', integral_const_mul, integral_const_mul, integral_const_mul]

theorem integral_lincomb_fin {α : Type*} [MeasurableSpace α] (ν : Measure α) {n : ℕ} (c : Fin n → ℂ)
    (f : Fin n → α → ℂ) (hf : ∀ i, Integrable (f i) ν) :
    ∫ g, (∑ i, c i * f i g) ∂ν = ∑ i, c i * ∫ g, f i g ∂ν := by
  rw [integral_finsetSum _ fun i _ => (hf i).const_mul (c i)]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

end Slab

/-! ## The real archimedean flow acting on the slab

Pin 1 `:132–235`. -/

section Flow

variable {K : Type} [Field K] [NumberField K]

theorem dn_mul_archFlowAt {w : InfinitePlace K} (hw : w.IsReal) (d : ArchDir) (t : ℝ)
    (g : AdelicGL2 (𝓞 K) K) : dn (g * archFlowAt hw d t) = dn g := by
  rw [dn_mul]
  show dn g * ideleNorm K (Matrix.GeneralLinearGroup.det (archFlowAt hw d t)) = dn g
  rw [det_archFlowAt]
  simp [ideleNorm]

theorem preimage_mul_archFlowAt_slab {w : InfinitePlace K} (hw : w.IsReal) (d : ArchDir) (t : ℝ) (a b : ℝ) :
    (fun g : AdelicGL2 (𝓞 K) K => g * archFlowAt hw d t) ⁻¹' slab K a b = slab K a b := by
  ext g
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  rw [show ideleNorm K (Matrix.GeneralLinearGroup.det (g * archFlowAt hw d t)) = dn g from
    dn_mul_archFlowAt hw d t g]

theorem mul_archFlowAt_mem_slab {w : InfinitePlace K} (hw : w.IsReal) (d : ArchDir) (t : ℝ) {a b : ℝ}
    {g : AdelicGL2 (𝓞 K) K} (hg : g ∈ slab K a b) : g * archFlowAt hw d t ∈ slab K a b := by
  show dn (g * archFlowAt hw d t) ∈ Set.Icc a b
  rw [dn_mul_archFlowAt]
  exact hg

theorem image_mul_archFlowAt_subset {w : InfinitePlace K} (hw : w.IsReal) (d : ArchDir) (t : ℝ) {a b : ℝ}
    {𝓕 : Set (AdelicGL2 (𝓞 K) K)} (h : 𝓕 ⊆ slab K a b) :
    (fun g : AdelicGL2 (𝓞 K) K => g * archFlowAt hw d t) '' 𝓕 ⊆ slab K a b := by
  rintro _ ⟨g, hg, rfl⟩
  exact mul_archFlowAt_mem_slab hw d t (h hg)

theorem isFundamentalDomain_image_mul_archFlowAt {w : InfinitePlace K} (hw : w.IsReal) (d : ArchDir) (t : ℝ)
    (a b : ℝ) {𝓕 : Set (AdelicGL2 (𝓞 K) K)}
    (h𝓕 : IsFundamentalDomain ↥(Γp K) 𝓕 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K a b))) :
    IsFundamentalDomain ↥(Γp K) ((fun g : AdelicGL2 (𝓞 K) K => g * archFlowAt hw d t) '' 𝓕)
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K a b)) := by
  have hcoe : (⇑(Equiv.mulRight (archFlowAt hw d t)) : AdelicGL2 (𝓞 K) K → AdelicGL2 (𝓞 K) K) =
      fun g => g * archFlowAt hw d t := Equiv.coe_mulRight _
  have hqmp : Measure.QuasiMeasurePreserving (⇑(Equiv.mulRight (archFlowAt hw d t)).symm)
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K a b))
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K a b)) := by
    rw [Equiv.mulRight_symm, Equiv.coe_mulRight, archFlowAt_inv]
    have h1 := (measurePreserving_mul_right' (K := K) (archFlowAt hw d (-t))).restrict_preimage
      (measurableSet_slab (K := K) a b)
    rw [preimage_mul_archFlowAt_slab] at h1
    exact h1.quasiMeasurePreserving
  have h := h𝓕.image_of_equiv (Equiv.mulRight (archFlowAt hw d t)) hqmp (Equiv.refl _) (fun γ g => by
    show (((Equiv.refl _ γ : ↥(Γp K)) : AdelicGL2 (𝓞 K) K) * g) * archFlowAt hw d t =
      (γ : AdelicGL2 (𝓞 K) K) * (g * archFlowAt hw d t)
    rw [Equiv.refl_apply, mul_assoc])
  rwa [hcoe] at h

theorem setIntegral_comp_mul_archFlowAt_eq {w : InfinitePlace K} (hw : w.IsReal) (d : ArchDir) (t : ℝ)
    (a b : ℝ) {𝓕 : Set (AdelicGL2 (𝓞 K) K)} (h𝓕s : 𝓕 ⊆ slab K a b)
    (h𝓕 : IsFundamentalDomain ↥(Γp K) 𝓕 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K a b)))
    (f : AdelicGL2 (𝓞 K) K → ℂ)
    (hf : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), f (globalPoints (𝓞 K) K γ * g) = f g) :
    ∫ g in 𝓕, f (g * archFlowAt hw d t) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ∫ g in 𝓕, f g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  have := countable_Γp (K := K)
  have := smulInvariantMeasure_slab (K := K) a b
  have hemb : MeasurableEmbedding (fun g : AdelicGL2 (𝓞 K) K => g * archFlowAt hw d t) :=
    (Homeomorph.mulRight (archFlowAt hw d t)).measurableEmbedding
  have hsub := image_mul_archFlowAt_subset hw d t h𝓕s
  have hinv : ∀ (γ : ↥(Γp K)) (g : AdelicGL2 (𝓞 K) K), f (γ • g) = f g := by
    rintro ⟨_, γ', rfl⟩ g
    exact hf γ' g
  calc ∫ g in 𝓕, f (g * archFlowAt hw d t) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
      = ∫ h in (fun g : AdelicGL2 (𝓞 K) K => g * archFlowAt hw d t) '' 𝓕, f h ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
        ((measurePreserving_mul_right' (K := K) (archFlowAt hw d t)).setIntegral_image_emb hemb f 𝓕).symm
    _ = ∫ h in (fun g : AdelicGL2 (𝓞 K) K => g * archFlowAt hw d t) '' 𝓕, f h
          ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K a b)) := by
        rw [Measure.restrict_restrict_of_subset hsub]
    _ = ∫ h in 𝓕, f h ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K a b)) :=
        (isFundamentalDomain_image_mul_archFlowAt hw d t a b h𝓕).setIntegral_eq h𝓕 hinv
    _ = ∫ g in 𝓕, f g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
        rw [Measure.restrict_restrict_of_subset h𝓕s]

end Flow

/-! ## The complex archimedean flow acting on the slab

Pin 2 `:138–245`. -/

section FlowComplex

variable {K : Type} [Field K] [NumberField K]

theorem dn_mul_archFlowAtComplex {w : InfinitePlace K} (hw : w.IsComplex) (d : ArchDirComplex) (t : ℝ)
    (g : AdelicGL2 (𝓞 K) K) : dn (g * archFlowAtComplex hw d t) = dn g := by
  rw [dn_mul]
  show dn g * ideleNorm K (Matrix.GeneralLinearGroup.det (archFlowAtComplex hw d t)) = dn g
  rw [det_archFlowAtComplex]
  simp [ideleNorm]

theorem preimage_mul_archFlowAtComplex_slab {w : InfinitePlace K} (hw : w.IsComplex) (d : ArchDirComplex)
    (t : ℝ) (a b : ℝ) :
    (fun g : AdelicGL2 (𝓞 K) K => g * archFlowAtComplex hw d t) ⁻¹' slab K a b = slab K a b := by
  ext g
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  rw [show ideleNorm K (Matrix.GeneralLinearGroup.det (g * archFlowAtComplex hw d t)) = dn g from
    dn_mul_archFlowAtComplex hw d t g]

theorem mul_archFlowAtComplex_mem_slab {w : InfinitePlace K} (hw : w.IsComplex) (d : ArchDirComplex) (t : ℝ)
    {a b : ℝ} {g : AdelicGL2 (𝓞 K) K} (hg : g ∈ slab K a b) : g * archFlowAtComplex hw d t ∈ slab K a b := by
  show dn (g * archFlowAtComplex hw d t) ∈ Set.Icc a b
  rw [dn_mul_archFlowAtComplex]
  exact hg

theorem image_mul_archFlowAtComplex_subset {w : InfinitePlace K} (hw : w.IsComplex) (d : ArchDirComplex)
    (t : ℝ) {a b : ℝ} {𝓕 : Set (AdelicGL2 (𝓞 K) K)} (h : 𝓕 ⊆ slab K a b) :
    (fun g : AdelicGL2 (𝓞 K) K => g * archFlowAtComplex hw d t) '' 𝓕 ⊆ slab K a b := by
  rintro _ ⟨g, hg, rfl⟩
  exact mul_archFlowAtComplex_mem_slab hw d t (h hg)

theorem isFundamentalDomain_image_mul_archFlowAtComplex {w : InfinitePlace K} (hw : w.IsComplex)
    (d : ArchDirComplex) (t : ℝ) (a b : ℝ) {𝓕 : Set (AdelicGL2 (𝓞 K) K)}
    (h𝓕 : IsFundamentalDomain ↥(Γp K) 𝓕 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K a b))) :
    IsFundamentalDomain ↥(Γp K) ((fun g : AdelicGL2 (𝓞 K) K => g * archFlowAtComplex hw d t) '' 𝓕)
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K a b)) := by
  have hcoe : (⇑(Equiv.mulRight (archFlowAtComplex hw d t)) : AdelicGL2 (𝓞 K) K → AdelicGL2 (𝓞 K) K) =
      fun g => g * archFlowAtComplex hw d t := Equiv.coe_mulRight _
  have hqmp : Measure.QuasiMeasurePreserving (⇑(Equiv.mulRight (archFlowAtComplex hw d t)).symm)
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K a b))
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K a b)) := by
    rw [Equiv.mulRight_symm, Equiv.coe_mulRight, archFlowAtComplex_inv]
    have h1 := (measurePreserving_mul_right' (K := K) (archFlowAtComplex hw d (-t))).restrict_preimage
      (measurableSet_slab (K := K) a b)
    rw [preimage_mul_archFlowAtComplex_slab] at h1
    exact h1.quasiMeasurePreserving
  have h := h𝓕.image_of_equiv (Equiv.mulRight (archFlowAtComplex hw d t)) hqmp (Equiv.refl _) (fun γ g => by
    show (((Equiv.refl _ γ : ↥(Γp K)) : AdelicGL2 (𝓞 K) K) * g) * archFlowAtComplex hw d t =
      (γ : AdelicGL2 (𝓞 K) K) * (g * archFlowAtComplex hw d t)
    rw [Equiv.refl_apply, mul_assoc])
  rwa [hcoe] at h

theorem setIntegral_comp_mul_archFlowAtComplex_eq {w : InfinitePlace K} (hw : w.IsComplex)
    (d : ArchDirComplex) (t : ℝ) (a b : ℝ) {𝓕 : Set (AdelicGL2 (𝓞 K) K)} (h𝓕s : 𝓕 ⊆ slab K a b)
    (h𝓕 : IsFundamentalDomain ↥(Γp K) 𝓕 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K a b)))
    (f : AdelicGL2 (𝓞 K) K → ℂ)
    (hf : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), f (globalPoints (𝓞 K) K γ * g) = f g) :
    ∫ g in 𝓕, f (g * archFlowAtComplex hw d t) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ∫ g in 𝓕, f g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  have := countable_Γp (K := K)
  have := smulInvariantMeasure_slab (K := K) a b
  have hemb : MeasurableEmbedding (fun g : AdelicGL2 (𝓞 K) K => g * archFlowAtComplex hw d t) :=
    (Homeomorph.mulRight (archFlowAtComplex hw d t)).measurableEmbedding
  have hsub := image_mul_archFlowAtComplex_subset hw d t h𝓕s
  have hinv : ∀ (γ : ↥(Γp K)) (g : AdelicGL2 (𝓞 K) K), f (γ • g) = f g := by
    rintro ⟨_, γ', rfl⟩ g
    exact hf γ' g
  calc ∫ g in 𝓕, f (g * archFlowAtComplex hw d t) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
      = ∫ h in (fun g : AdelicGL2 (𝓞 K) K => g * archFlowAtComplex hw d t) '' 𝓕, f h ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
        ((measurePreserving_mul_right' (K := K) (archFlowAtComplex hw d t)).setIntegral_image_emb hemb f 𝓕).symm
    _ = ∫ h in (fun g : AdelicGL2 (𝓞 K) K => g * archFlowAtComplex hw d t) '' 𝓕, f h
          ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K a b)) := by
        rw [Measure.restrict_restrict_of_subset hsub]
    _ = ∫ h in 𝓕, f h ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K a b)) :=
        (isFundamentalDomain_image_mul_archFlowAtComplex hw d t a b h𝓕).setIntegral_eq h𝓕 hinv
    _ = ∫ g in 𝓕, f g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
        rw [Measure.restrict_restrict_of_subset h𝓕s]

end FlowComplex

/-! ## The derivative of the flow, and two boundedness helpers -/

section Deriv

variable {K : Type} [Field K] [NumberField K]

theorem hasDerivAt_comp_mul_archFlowAt {w : InfinitePlace K} {hw : w.IsReal} (d : ArchDir)
    {x : AdelicGL2 (𝓞 K) K → ℂ} (hxs : IsArchSmoothAt hw x) (g : AdelicGL2 (𝓞 K) K) (t : ℝ) :
    HasDerivAt (fun s : ℝ => x (g * archFlowAt hw d s)) (archDerivAt hw d x (g * archFlowAt hw d t)) t := by
  have h0 : HasDerivAt (fun s : ℝ => x (g * archFlowAt hw d t * archFlowAt hw d s))
      (archDerivAt hw d x (g * archFlowAt hw d t)) 0 :=
    (hxs.differentiableAt_flow d (g * archFlowAt hw d t)).hasDerivAt
  have h1 : HasDerivAt (fun s : ℝ => x (g * archFlowAt hw d (t + s)))
      (archDerivAt hw d x (g * archFlowAt hw d t)) 0 := by
    have hfun : (fun s : ℝ => x (g * archFlowAt hw d t * archFlowAt hw d s)) =
        fun s : ℝ => x (g * archFlowAt hw d (t + s)) := by
      funext s; rw [archFlowAt_add, mul_assoc]
    rwa [hfun] at h0
  have h1' : HasDerivAt (fun s : ℝ => x (g * archFlowAt hw d (t + s)))
      (archDerivAt hw d x (g * archFlowAt hw d t)) (-t + t) := by rwa [neg_add_cancel]
  have h2 := h1'.comp_const_add (-t) t
  simp only [add_neg_cancel_left] at h2
  exact h2

theorem hasDerivAt_comp_mul_archFlowAtComplex {w : InfinitePlace K} {hw : w.IsComplex} (d : ArchDirComplex)
    {x : AdelicGL2 (𝓞 K) K → ℂ} (hxs : IsArchSmoothAtComplex hw x) (g : AdelicGL2 (𝓞 K) K) (t : ℝ) :
    HasDerivAt (fun s : ℝ => x (g * archFlowAtComplex hw d s))
      (archDerivAtComplex hw d x (g * archFlowAtComplex hw d t)) t := by
  have h0 : HasDerivAt (fun s : ℝ => x (g * archFlowAtComplex hw d t * archFlowAtComplex hw d s))
      (archDerivAtComplex hw d x (g * archFlowAtComplex hw d t)) 0 :=
    (hxs.differentiableAt_flow d (g * archFlowAtComplex hw d t)).hasDerivAt
  have h1 : HasDerivAt (fun s : ℝ => x (g * archFlowAtComplex hw d (t + s)))
      (archDerivAtComplex hw d x (g * archFlowAtComplex hw d t)) 0 := by
    have hfun : (fun s : ℝ => x (g * archFlowAtComplex hw d t * archFlowAtComplex hw d s)) =
        fun s : ℝ => x (g * archFlowAtComplex hw d (t + s)) := by
      funext s; rw [archFlowAtComplex_add, mul_assoc]
    rwa [hfun] at h0
  have h1' : HasDerivAt (fun s : ℝ => x (g * archFlowAtComplex hw d (t + s)))
      (archDerivAtComplex hw d x (g * archFlowAtComplex hw d t)) (-t + t) := by rwa [neg_add_cancel]
  have h2 := h1'.comp_const_add (-t) t
  simp only [add_neg_cancel_left] at h2
  exact h2

end Deriv

/-! ## The real directional derivative is skew-adjoint (pin 1 `:273`) -/

section Main

variable {K : Type} [Field K] [NumberField K]

attribute [local instance] NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

theorem main
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal) (X : ArchDir)
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂)
    (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (h𝓕m : MeasurableSet 𝓕)
    (h𝓕s : 𝓕 ⊆ slab K e₁ e₂)
    (h𝓕 : IsFundamentalDomain (globalPoints (𝓞 K) K).range 𝓕
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K e₁ e₂)))
    (x x' : AdelicGL2 (𝓞 K) K → ℂ)
    (hx : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x (globalPoints (𝓞 K) K γ * g) = x g)
    (hx' : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x' (globalPoints (𝓞 K) K γ * g) = x' g)
    (hxc : Continuous x) (hx'c : Continuous x')
    (hxs : IsArchSmoothAt hw x) (hx's : IsArchSmoothAt hw x')
    (hDx : Continuous (archDerivAt hw X x)) (hDx' : Continuous (archDerivAt hw X x'))
    (B : ℝ) (hB : ∀ g : AdelicGL2 (𝓞 K) K, ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
      ‖x g‖ ≤ B ∧ ‖x' g‖ ≤ B ∧ ‖archDerivAt hw X x g‖ ≤ B ∧ ‖archDerivAt hw X x' g‖ ≤ B) :
    ∫ g in 𝓕, (archDerivAt hw X x g * conj (x' g) + x g * conj (archDerivAt hw X x' g))
      ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 := by
  set μ : Measure (AdelicGL2 (𝓞 K) K) := adelicGLHaar (Fin 2) (𝓞 K) K with hμ

  let Φ : ℝ → AdelicGL2 (𝓞 K) K → ℂ := fun t g =>
    x (g * archFlowAt hw X t) * conj (x' (g * archFlowAt hw X t))
  let Φ' : ℝ → AdelicGL2 (𝓞 K) K → ℂ := fun t g =>
    archDerivAt hw X x (g * archFlowAt hw X t) * conj (x' (g * archFlowAt hw X t)) +
      x (g * archFlowAt hw X t) * conj (archDerivAt hw X x' (g * archFlowAt hw X t))

  have hfin : μ 𝓕 < ⊤ := by
    have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
      K e₁ e₂ he₁ he 𝓕 h𝓕
    rwa [Set.inter_eq_left.mpr h𝓕s] at h
  have : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.mpr hfin.ne

  have hΦc : ∀ t, Continuous (Φ t) := fun t =>
    (hxc.comp (continuous_mul_const (archFlowAt hw X t))).mul
      (Complex.continuous_conj.comp (hx'c.comp (continuous_mul_const (archFlowAt hw X t))))
  have hΦ'c : ∀ t, Continuous (Φ' t) := fun t =>
    ((hDx.comp (continuous_mul_const (archFlowAt hw X t))).mul
      (Complex.continuous_conj.comp (hx'c.comp (continuous_mul_const (archFlowAt hw X t))))).add
    ((hxc.comp (continuous_mul_const (archFlowAt hw X t))).mul
      (Complex.continuous_conj.comp (hDx'.comp (continuous_mul_const (archFlowAt hw X t)))))

  have hΦb : ∀ t, ∀ g ∈ 𝓕, ‖Φ t g‖ ≤ B * B := fun t g hg => by
    obtain ⟨h1, h2, -, -⟩ := hB _ (mul_archFlowAt_mem_slab hw X t (h𝓕s hg))
    exact norm_mul_conj_le h1 h2
  have hΦ'b : ∀ t, ∀ g ∈ 𝓕, ‖Φ' t g‖ ≤ B * B + B * B := fun t g hg => by
    obtain ⟨h1, h2, h3, h4⟩ := hB _ (mul_archFlowAt_mem_slab hw X t (h𝓕s hg))
    exact norm_add_le' h3 h2 h1 h4

  have hint : Integrable (Φ 0) (μ.restrict 𝓕) :=
    Measure.integrableOn_of_bounded hfin.ne (hΦc 0).aestronglyMeasurable
      ((ae_restrict_iff' h𝓕m).mpr (Filter.Eventually.of_forall fun g hg => hΦb 0 g hg))

  have hdiff : ∀ (g : AdelicGL2 (𝓞 K) K) (t : ℝ), HasDerivAt (fun s => Φ s g) (Φ' t g) t := fun g t => by
    have ha := hasDerivAt_comp_mul_archFlowAt X hxs g t
    have hb := HasDerivAt.star (hasDerivAt_comp_mul_archFlowAt X hx's g t)
    exact ha.mul hb

  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict 𝓕) (F := Φ) (F' := Φ')
    (x₀ := (0 : ℝ)) (s := Set.univ) (bound := fun _ => B * B + B * B) Filter.univ_mem
    (Filter.Eventually.of_forall fun t => (hΦc t).aestronglyMeasurable) hint
    (hΦ'c 0).aestronglyMeasurable
    ((ae_restrict_iff' h𝓕m).mpr (Filter.Eventually.of_forall fun g hg t _ => hΦ'b t g hg))
    (integrable_const _)
    (Filter.Eventually.of_forall fun g t _ => hdiff g t)
  obtain ⟨-, hderiv⟩ := key

  have hconst : (fun t : ℝ => ∫ g, Φ t g ∂(μ.restrict 𝓕)) = fun _ => ∫ g in 𝓕, x g * conj (x' g) ∂μ := by
    funext t
    exact setIntegral_comp_mul_archFlowAt_eq hw X t e₁ e₂ h𝓕s h𝓕 (fun g => x g * conj (x' g))
      (fun γ g => by show x _ * conj (x' _) = x g * conj (x' g); rw [hx, hx'])
  have hzero : HasDerivAt (fun t : ℝ => ∫ g, Φ t g ∂(μ.restrict 𝓕)) 0 0 := by
    rw [hconst]; exact hasDerivAt_const _ _
  have h0 : ∫ g, Φ' 0 g ∂(μ.restrict 𝓕) = 0 := hderiv.unique hzero
  have hΦ'0 : ∀ g, Φ' 0 g = archDerivAt hw X x g * conj (x' g) + x g * conj (archDerivAt hw X x' g) := by
    intro g
    show archDerivAt hw X x (g * archFlowAt hw X 0) * conj (x' (g * archFlowAt hw X 0)) +
      x (g * archFlowAt hw X 0) * conj (archDerivAt hw X x' (g * archFlowAt hw X 0)) = _
    rw [archFlowAt_zero, mul_one]
  have h1 : ∫ g, Φ' 0 g ∂(μ.restrict 𝓕) =
      ∫ g in 𝓕, (archDerivAt hw X x g * conj (x' g) + x g * conj (archDerivAt hw X x' g)) ∂μ := by
    congr 1
    funext g
    exact hΦ'0 g
  rw [← h1]
  exact h0

end Main

/-! ## The complex directional derivative is skew-adjoint (pin 2 `:279`) -/

section MainComplex

variable {K : Type} [Field K] [NumberField K]

attribute [local instance] NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

theorem main_archDerivAtComplex
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsComplex) (X : ArchDirComplex)
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂)
    (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (h𝓕m : MeasurableSet 𝓕)
    (h𝓕s : 𝓕 ⊆ slab K e₁ e₂)
    (h𝓕 : IsFundamentalDomain (globalPoints (𝓞 K) K).range 𝓕
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K e₁ e₂)))
    (x x' : AdelicGL2 (𝓞 K) K → ℂ)
    (hx : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x (globalPoints (𝓞 K) K γ * g) = x g)
    (hx' : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x' (globalPoints (𝓞 K) K γ * g) = x' g)
    (hxc : Continuous x) (hx'c : Continuous x')
    (hxs : IsArchSmoothAtComplex hw x) (hx's : IsArchSmoothAtComplex hw x')
    (hDx : Continuous (archDerivAtComplex hw X x)) (hDx' : Continuous (archDerivAtComplex hw X x'))
    (B : ℝ) (hB : ∀ g : AdelicGL2 (𝓞 K) K, ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
      ‖x g‖ ≤ B ∧ ‖x' g‖ ≤ B ∧ ‖archDerivAtComplex hw X x g‖ ≤ B ∧ ‖archDerivAtComplex hw X x' g‖ ≤ B) :
    ∫ g in 𝓕, (archDerivAtComplex hw X x g * conj (x' g) + x g * conj (archDerivAtComplex hw X x' g))
      ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 := by
  set μ : Measure (AdelicGL2 (𝓞 K) K) := adelicGLHaar (Fin 2) (𝓞 K) K with hμ

  let Φ : ℝ → AdelicGL2 (𝓞 K) K → ℂ := fun t g =>
    x (g * archFlowAtComplex hw X t) * conj (x' (g * archFlowAtComplex hw X t))
  let Φ' : ℝ → AdelicGL2 (𝓞 K) K → ℂ := fun t g =>
    archDerivAtComplex hw X x (g * archFlowAtComplex hw X t) * conj (x' (g * archFlowAtComplex hw X t)) +
      x (g * archFlowAtComplex hw X t) * conj (archDerivAtComplex hw X x' (g * archFlowAtComplex hw X t))

  have hfin : μ 𝓕 < ⊤ := by
    have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
      K e₁ e₂ he₁ he 𝓕 h𝓕
    rwa [Set.inter_eq_left.mpr h𝓕s] at h
  have : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.mpr hfin.ne

  have hΦc : ∀ t, Continuous (Φ t) := fun t =>
    (hxc.comp (continuous_mul_const (archFlowAtComplex hw X t))).mul
      (Complex.continuous_conj.comp (hx'c.comp (continuous_mul_const (archFlowAtComplex hw X t))))
  have hΦ'c : ∀ t, Continuous (Φ' t) := fun t =>
    ((hDx.comp (continuous_mul_const (archFlowAtComplex hw X t))).mul
      (Complex.continuous_conj.comp (hx'c.comp (continuous_mul_const (archFlowAtComplex hw X t))))).add
    ((hxc.comp (continuous_mul_const (archFlowAtComplex hw X t))).mul
      (Complex.continuous_conj.comp (hDx'.comp (continuous_mul_const (archFlowAtComplex hw X t)))))

  have hΦb : ∀ t, ∀ g ∈ 𝓕, ‖Φ t g‖ ≤ B * B := fun t g hg => by
    obtain ⟨h1, h2, -, -⟩ := hB _ (mul_archFlowAtComplex_mem_slab hw X t (h𝓕s hg))
    exact norm_mul_conj_le h1 h2
  have hΦ'b : ∀ t, ∀ g ∈ 𝓕, ‖Φ' t g‖ ≤ B * B + B * B := fun t g hg => by
    obtain ⟨h1, h2, h3, h4⟩ := hB _ (mul_archFlowAtComplex_mem_slab hw X t (h𝓕s hg))
    exact norm_add_le' h3 h2 h1 h4

  have hint : Integrable (Φ 0) (μ.restrict 𝓕) :=
    Measure.integrableOn_of_bounded hfin.ne (hΦc 0).aestronglyMeasurable
      ((ae_restrict_iff' h𝓕m).mpr (Filter.Eventually.of_forall fun g hg => hΦb 0 g hg))

  have hdiff : ∀ (g : AdelicGL2 (𝓞 K) K) (t : ℝ), HasDerivAt (fun s => Φ s g) (Φ' t g) t := fun g t => by
    have ha := hasDerivAt_comp_mul_archFlowAtComplex X hxs g t
    have hb := HasDerivAt.star (hasDerivAt_comp_mul_archFlowAtComplex X hx's g t)
    exact ha.mul hb

  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict 𝓕) (F := Φ) (F' := Φ')
    (x₀ := (0 : ℝ)) (s := Set.univ) (bound := fun _ => B * B + B * B) Filter.univ_mem
    (Filter.Eventually.of_forall fun t => (hΦc t).aestronglyMeasurable) hint
    (hΦ'c 0).aestronglyMeasurable
    ((ae_restrict_iff' h𝓕m).mpr (Filter.Eventually.of_forall fun g hg t _ => hΦ'b t g hg))
    (integrable_const _)
    (Filter.Eventually.of_forall fun g t _ => hdiff g t)
  obtain ⟨-, hderiv⟩ := key

  have hconst : (fun t : ℝ => ∫ g, Φ t g ∂(μ.restrict 𝓕)) = fun _ => ∫ g in 𝓕, x g * conj (x' g) ∂μ := by
    funext t
    exact setIntegral_comp_mul_archFlowAtComplex_eq hw X t e₁ e₂ h𝓕s h𝓕 (fun g => x g * conj (x' g))
      (fun γ g => by show x _ * conj (x' _) = x g * conj (x' g); rw [hx, hx'])
  have hzero : HasDerivAt (fun t : ℝ => ∫ g, Φ t g ∂(μ.restrict 𝓕)) 0 0 := by
    rw [hconst]; exact hasDerivAt_const _ _
  have h0 : ∫ g, Φ' 0 g ∂(μ.restrict 𝓕) = 0 := hderiv.unique hzero
  have hΦ'0 : ∀ g, Φ' 0 g =
      archDerivAtComplex hw X x g * conj (x' g) + x g * conj (archDerivAtComplex hw X x' g) := by
    intro g
    show archDerivAtComplex hw X x (g * archFlowAtComplex hw X 0) * conj (x' (g * archFlowAtComplex hw X 0)) +
      x (g * archFlowAtComplex hw X 0) * conj (archDerivAtComplex hw X x' (g * archFlowAtComplex hw X 0)) = _
    rw [archFlowAtComplex_zero, mul_one]
  have h1 : ∫ g, Φ' 0 g ∂(μ.restrict 𝓕) =
      ∫ g in 𝓕, (archDerivAtComplex hw X x g * conj (x' g) + x g * conj (archDerivAtComplex hw X x' g)) ∂μ := by
    congr 1
    funext g
    exact hΦ'0 g
  rw [← h1]
  exact h0

end MainComplex

end PeterssonSkewAdjunction

/-! ## The two derivative rows -/

/-- **The real place.** The Petersson pairing of the directional archimedean derivative with `x'` plus
its mirror vanishes over a fundamental domain of the determinant-norm slab. -/
theorem setIntegral_archDerivAt_mul_conj_add_eq_zero_of_isFundamentalDomain
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal) (X : ArchDir)
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂)
    (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (h𝓕m : MeasurableSet 𝓕)
    (h𝓕s : 𝓕 ⊆ {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂})
    (h𝓕 : IsFundamentalDomain (globalPoints (𝓞 K) K).range 𝓕
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂}))
    (x x' : AdelicGL2 (𝓞 K) K → ℂ)
    (hx : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x (globalPoints (𝓞 K) K γ * g) = x g)
    (hx' : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x' (globalPoints (𝓞 K) K γ * g) = x' g)
    (hxc : Continuous x) (hx'c : Continuous x')
    (hxs : IsArchSmoothAt hw x) (hx's : IsArchSmoothAt hw x')
    (hDx : Continuous (archDerivAt hw X x)) (hDx' : Continuous (archDerivAt hw X x'))
    (B : ℝ) (hB : ∀ g : AdelicGL2 (𝓞 K) K, ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
      ‖x g‖ ≤ B ∧ ‖x' g‖ ≤ B ∧ ‖archDerivAt hw X x g‖ ≤ B ∧ ‖archDerivAt hw X x' g‖ ≤ B) :
    ∫ g in 𝓕, (archDerivAt hw X x g * conj (x' g) + x g * conj (archDerivAt hw X x' g)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 :=
  PeterssonSkewAdjunction.main K w hw X e₁ e₂ he₁ he 𝓕 h𝓕m h𝓕s h𝓕 x x' hx hx' hxc hx'c hxs hx's hDx hDx' B hB

/-- **The complex place.** The same skew-adjointness for `ArchDirComplex` and `archDerivAtComplex`. -/
theorem setIntegral_archDerivAtComplex_mul_conj_add_eq_zero_of_isFundamentalDomain
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsComplex) (X : ArchDirComplex)
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂)
    (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (h𝓕m : MeasurableSet 𝓕)
    (h𝓕s : 𝓕 ⊆ {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂})
    (h𝓕 : IsFundamentalDomain (globalPoints (𝓞 K) K).range 𝓕
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂}))
    (x x' : AdelicGL2 (𝓞 K) K → ℂ)
    (hx : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x (globalPoints (𝓞 K) K γ * g) = x g)
    (hx' : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x' (globalPoints (𝓞 K) K γ * g) = x' g)
    (hxc : Continuous x) (hx'c : Continuous x')
    (hxs : IsArchSmoothAtComplex hw x) (hx's : IsArchSmoothAtComplex hw x')
    (hDx : Continuous (archDerivAtComplex hw X x)) (hDx' : Continuous (archDerivAtComplex hw X x'))
    (B : ℝ) (hB : ∀ g : AdelicGL2 (𝓞 K) K, ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
      ‖x g‖ ≤ B ∧ ‖x' g‖ ≤ B ∧ ‖archDerivAtComplex hw X x g‖ ≤ B ∧ ‖archDerivAtComplex hw X x' g‖ ≤ B) :
    ∫ g in 𝓕, (archDerivAtComplex hw X x g * conj (x' g) + x g * conj (archDerivAtComplex hw X x' g))
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 :=
  PeterssonSkewAdjunction.main_archDerivAtComplex K w hw X e₁ e₂ he₁ he 𝓕 h𝓕m h𝓕s h𝓕 x x' hx hx' hxc hx'c hxs hx's hDx hDx' B hB


namespace PeterssonSkewAdjunction

/-! ## The global points commute with the directional derivative (pins 3 `:53`, 4 `:51`) -/

section GlobalPoints

variable {K : Type} [Field K] [NumberField K]

theorem archDerivAt_globalPoints_mul {w : InfinitePlace K} (hw : w.IsReal) (d : ArchDir)
    {x : AdelicGL2 (𝓞 K) K → ℂ}
    (hx : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x (globalPoints (𝓞 K) K γ * g) = x g) :
    ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
      archDerivAt hw d x (globalPoints (𝓞 K) K γ * g) = archDerivAt hw d x g := by
  intro γ g
  have h := archDerivAt_comp_mul_left hw d x (globalPoints (𝓞 K) K γ)
  have hfun : (fun g => x (globalPoints (𝓞 K) K γ * g)) = x := funext (hx γ)
  rw [hfun] at h
  exact (congrFun h g).symm

theorem archDerivAtComplex_globalPoints_mul {w : InfinitePlace K} (hw : w.IsComplex) (d : ArchDirComplex)
    {x : AdelicGL2 (𝓞 K) K → ℂ}
    (hx : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x (globalPoints (𝓞 K) K γ * g) = x g) :
    ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
      archDerivAtComplex hw d x (globalPoints (𝓞 K) K γ * g) = archDerivAtComplex hw d x g := by
  intro γ g
  have h := archDerivAtComplex_comp_mul_left hw d x (globalPoints (𝓞 K) K γ)
  have hfun : (fun g => x (globalPoints (𝓞 K) K γ * g)) = x := funext (hx γ)
  rw [hfun] at h
  exact (congrFun h g).symm

theorem archDerivAtComplex_lin {w : InfinitePlace K} (hw : w.IsComplex) (X : ArchDirComplex)
    {u v : AdelicGL2 (𝓞 K) K → ℂ} (hu : IsArchSmoothAtComplex hw u) (hv : IsArchSmoothAtComplex hw v) (a b : ℂ) :
    archDerivAtComplex hw X (a • u + b • v) = a • archDerivAtComplex hw X u + b • archDerivAtComplex hw X v := by
  rw [archDerivAtComplex_add (hu.smul a) (hv.smul b), archDerivAtComplex_smul, archDerivAtComplex_smul]

theorem archDelAt_eq {w : InfinitePlace K} (hw : w.IsComplex) (d : ArchDir) (u : AdelicGL2 (𝓞 K) K → ℂ) :
    archDelAt hw d u = (1 / 2 : ℂ) • archDerivAtComplex hw d.toComplex u +
      (-(Complex.I / 2)) • archDerivAtComplex hw d.toComplexI u := by
  funext g
  simp only [archDelAt, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
  ring

theorem archDelBarAt_eq {w : InfinitePlace K} (hw : w.IsComplex) (d : ArchDir) (u : AdelicGL2 (𝓞 K) K → ℂ) :
    archDelBarAt hw d u = (1 / 2 : ℂ) • archDerivAtComplex hw d.toComplex u +
      (Complex.I / 2) • archDerivAtComplex hw d.toComplexI u := by
  funext g
  simp only [archDelBarAt, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  ring

end GlobalPoints

/-! ## The real Casimir is self-adjoint (pin 3 `:64`) -/

section Casimir

variable {K : Type} [Field K] [NumberField K]

theorem main_archCasimirAt
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal)
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂)
    (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (h𝓕m : MeasurableSet 𝓕)
    (h𝓕s : 𝓕 ⊆ slab K e₁ e₂)
    (h𝓕 : IsFundamentalDomain (globalPoints (𝓞 K) K).range 𝓕
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K e₁ e₂)))
    (x x' : AdelicGL2 (𝓞 K) K → ℂ)
    (hx : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x (globalPoints (𝓞 K) K γ * g) = x g)
    (hx' : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x' (globalPoints (𝓞 K) K γ * g) = x' g)
    (hxc : Continuous x) (hx'c : Continuous x')
    (hxs : IsArchSmoothAt hw x) (hx's : IsArchSmoothAt hw x')
    (hD1 : ∀ d : ArchDir, Continuous (archDerivAt hw d x)) (hD1' : ∀ d : ArchDir, Continuous (archDerivAt hw d x'))
    (hD2 : ∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' x)))
    (hD2' : ∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' x')))
    (B : ℝ) (hB : ∀ g : AdelicGL2 (𝓞 K) K, ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
      ‖x g‖ ≤ B ∧ ‖x' g‖ ≤ B ∧ (∀ d : ArchDir, ‖archDerivAt hw d x g‖ ≤ B ∧ ‖archDerivAt hw d x' g‖ ≤ B) ∧
      (∀ d d' : ArchDir, ‖archDerivAt hw d (archDerivAt hw d' x) g‖ ≤ B ∧ ‖archDerivAt hw d (archDerivAt hw d' x') g‖ ≤ B)) :
    (∫ g in 𝓕, archCasimirAt hw x g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        ∫ g in 𝓕, x g * conj (archCasimirAt hw x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    (∫ g in 𝓕, (archDerivAt hw .H x - Complex.I • (archDerivAt hw .E x + archDerivAt hw .Fm x)) g * conj (x' g)
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        -∫ g in 𝓕, x g * conj ((archDerivAt hw .H x' + Complex.I • (archDerivAt hw .E x' + archDerivAt hw .Fm x')) g)
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    (∫ g in 𝓕, (archDerivAt hw .H x + Complex.I • (archDerivAt hw .E x + archDerivAt hw .Fm x)) g * conj (x' g)
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        -∫ g in 𝓕, x g * conj ((archDerivAt hw .H x' - Complex.I • (archDerivAt hw .E x' + archDerivAt hw .Fm x')) g)
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) := by
  have hfin : adelicGLHaar (Fin 2) (𝓞 K) K 𝓕 < ⊤ := by
    have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
      K e₁ e₂ he₁ he 𝓕 h𝓕
    rwa [Set.inter_eq_left.mpr h𝓕s] at h

  have bx : ∀ g ∈ slab K e₁ e₂, ‖x g‖ ≤ B := fun g hg => (hB g hg).1
  have bx' : ∀ g ∈ slab K e₁ e₂, ‖x' g‖ ≤ B := fun g hg => (hB g hg).2.1
  have bD : ∀ d, ∀ g ∈ slab K e₁ e₂, ‖archDerivAt hw d x g‖ ≤ B := fun d g hg => ((hB g hg).2.2.1 d).1
  have bD' : ∀ d, ∀ g ∈ slab K e₁ e₂, ‖archDerivAt hw d x' g‖ ≤ B := fun d g hg => ((hB g hg).2.2.1 d).2
  have bDD : ∀ d d', ∀ g ∈ slab K e₁ e₂, ‖archDerivAt hw d (archDerivAt hw d' x) g‖ ≤ B :=
    fun d d' g hg => ((hB g hg).2.2.2 d d').1
  have bDD' : ∀ d d', ∀ g ∈ slab K e₁ e₂, ‖archDerivAt hw d (archDerivAt hw d' x') g‖ ≤ B :=
    fun d d' g hg => ((hB g hg).2.2.2 d d').2

  have iD : ∀ d, ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
      archDerivAt hw d x (globalPoints (𝓞 K) K γ * g) = archDerivAt hw d x g :=
    fun d => archDerivAt_globalPoints_mul hw d hx
  have iD' : ∀ d, ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
      archDerivAt hw d x' (globalPoints (𝓞 K) K γ * g) = archDerivAt hw d x' g :=
    fun d => archDerivAt_globalPoints_mul hw d hx'

  have skew : ∀ (d : ArchDir) (u v : AdelicGL2 (𝓞 K) K → ℂ)
      (hu : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), u (globalPoints (𝓞 K) K γ * g) = u g)
      (hv : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), v (globalPoints (𝓞 K) K γ * g) = v g)
      (huc : Continuous u) (hvc : Continuous v) (hus : IsArchSmoothAt hw u) (hvs : IsArchSmoothAt hw v)
      (hDu : Continuous (archDerivAt hw d u)) (hDv : Continuous (archDerivAt hw d v))
      (bu : ∀ g ∈ slab K e₁ e₂, ‖u g‖ ≤ B) (bv : ∀ g ∈ slab K e₁ e₂, ‖v g‖ ≤ B)
      (bDu : ∀ g ∈ slab K e₁ e₂, ‖archDerivAt hw d u g‖ ≤ B) (bDv : ∀ g ∈ slab K e₁ e₂, ‖archDerivAt hw d v g‖ ≤ B),
      ∫ g in 𝓕, archDerivAt hw d u g * conj (v g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = -∫ g in 𝓕, u g * conj (archDerivAt hw d v g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
    intro d u v hu hv huc hvc hus hvs hDu hDv bu bv bDu bDv
    have h := AutomorphicForm.setIntegral_archDerivAt_mul_conj_add_eq_zero_of_isFundamentalDomain K w hw d e₁ e₂
      he₁ he 𝓕 h𝓕m h𝓕s h𝓕 u v hu hv huc hvc hus hvs hDu hDv B
      (fun g hg => ⟨bu g hg, bv g hg, bDu g hg, bDv g hg⟩)
    rw [integral_add (integrable_mul_conj h𝓕m h𝓕s hfin hDu hvc bDu bv)
      (integrable_mul_conj h𝓕m h𝓕s hfin huc hDv bu bDv)] at h
    exact eq_neg_of_add_eq_zero_left h

  have S3 := skew .H x x' hx hx' hxc hx'c hxs hx's (hD1 .H) (hD1' .H) bx bx' (bD .H) (bD' .H)
  have S6 := skew .E x x' hx hx' hxc hx'c hxs hx's (hD1 .E) (hD1' .E) bx bx' (bD .E) (bD' .E)
  have S7 := skew .Fm x x' hx hx' hxc hx'c hxs hx's (hD1 .Fm) (hD1' .Fm) bx bx' (bD .Fm) (bD' .Fm)

  have S1 := skew .H (archDerivAt hw .H x) x' (iD .H) hx' (hD1 .H) hx'c (hxs.archDerivAt .H) hx's (hD2 .H .H) (hD1' .H)
    (bD .H) bx' (bDD .H .H) (bD' .H)
  have S2 := skew .H x (archDerivAt hw .H x') hx (iD' .H) hxc (hD1' .H) hxs (hx's.archDerivAt .H) (hD1 .H) (hD2' .H .H)
    bx (bD' .H) (bD .H) (bDD' .H .H)

  have S4 := skew .E (archDerivAt hw .Fm x) x' (iD .Fm) hx' (hD1 .Fm) hx'c (hxs.archDerivAt .Fm) hx's (hD2 .E .Fm) (hD1' .E)
    (bD .Fm) bx' (bDD .E .Fm) (bD' .E)
  have S5 := skew .Fm x (archDerivAt hw .E x') hx (iD' .E) hxc (hD1' .E) hxs (hx's.archDerivAt .E) (hD1 .Fm) (hD2' .Fm .E)
    bx (bD' .E) (bD .Fm) (bDD' .Fm .E)

  have CR : ∀ g, archDerivAt hw .Fm (archDerivAt hw .E x') g = archDerivAt hw .E (archDerivAt hw .Fm x') g - (archDerivAt hw .H x') g := by
    intro g
    have h := (AutomorphicForm.archDerivAt_commutator_of_isArchSmoothAt K hw x' hx's).2.2
    have hg := congrFun h g
    simp only [Pi.sub_apply] at hg
    rw [← hg]
    ring
  have T4 : ∫ g in 𝓕, x g * conj (archDerivAt hw .Fm (archDerivAt hw .E x') g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ∫ g in 𝓕, x g * conj (archDerivAt hw .E (archDerivAt hw .Fm x') g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) - ∫ g in 𝓕, x g * conj ((archDerivAt hw .H x') g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
    rw [← integral_sub (integrable_mul_conj h𝓕m h𝓕s hfin hxc (hD2' .E .Fm) bx (bDD' .E .Fm))
      (integrable_mul_conj h𝓕m h𝓕s hfin hxc (hD1' .H) bx (bD' .H))]
    congr 1
    funext g
    rw [CR g, map_sub, mul_sub]

  have I_HHx := integrable_mul_conj h𝓕m h𝓕s hfin (hD2 .H .H) hx'c (bDD .H .H) bx'
  have I_Hx := integrable_mul_conj h𝓕m h𝓕s hfin (hD1 .H) hx'c (bD .H) bx'
  have I_Ex := integrable_mul_conj h𝓕m h𝓕s hfin (hD1 .E) hx'c (bD .E) bx'
  have I_Fx := integrable_mul_conj h𝓕m h𝓕s hfin (hD1 .Fm) hx'c (bD .Fm) bx'
  have I_EFx := integrable_mul_conj h𝓕m h𝓕s hfin (hD2 .E .Fm) hx'c (bDD .E .Fm) bx'
  have I_HHx' := integrable_mul_conj h𝓕m h𝓕s hfin hxc (hD2' .H .H) bx (bDD' .H .H)
  have I_Hx' := integrable_mul_conj h𝓕m h𝓕s hfin hxc (hD1' .H) bx (bD' .H)
  have I_Ex' := integrable_mul_conj h𝓕m h𝓕s hfin hxc (hD1' .E) bx (bD' .E)
  have I_Fx' := integrable_mul_conj h𝓕m h𝓕s hfin hxc (hD1' .Fm) bx (bD' .Fm)
  have I_EFx' := integrable_mul_conj h𝓕m h𝓕s hfin hxc (hD2' .E .Fm) bx (bDD' .E .Fm)

  have EL1 : ∫ g in 𝓕, archCasimirAt hw x g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      (-1/4 : ℂ) * ∫ g in 𝓕, archDerivAt hw .H (archDerivAt hw .H x) g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) +
      (1/2 : ℂ) * ∫ g in 𝓕, (archDerivAt hw .H x) g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) +
      (-1 : ℂ) * ∫ g in 𝓕, archDerivAt hw .E (archDerivAt hw .Fm x) g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
    rw [← integral_lincomb _ I_HHx I_Hx I_EFx]
    congr 1
    funext g
    simp only [archCasimirAt, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have ER1 : ∫ g in 𝓕, x g * conj (archCasimirAt hw x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      (-1/4 : ℂ) * ∫ g in 𝓕, x g * conj (archDerivAt hw .H (archDerivAt hw .H x') g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) +
      (1/2 : ℂ) * ∫ g in 𝓕, x g * conj ((archDerivAt hw .H x') g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) +
      (-1 : ℂ) * ∫ g in 𝓕, x g * conj (archDerivAt hw .E (archDerivAt hw .Fm x') g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
    rw [← integral_lincomb _ I_HHx' I_Hx' I_EFx']
    congr 1
    funext g
    simp only [archCasimirAt, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      map_neg, map_add, map_sub, map_mul, map_div₀, map_one, map_ofNat]
    ring
  have EL2 : ∫ g in 𝓕, ((archDerivAt hw .H x) - Complex.I • ((archDerivAt hw .E x) + (archDerivAt hw .Fm x))) g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      (1 : ℂ) * ∫ g in 𝓕, (archDerivAt hw .H x) g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) +
      (-Complex.I) * ∫ g in 𝓕, (archDerivAt hw .E x) g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) +
      (-Complex.I) * ∫ g in 𝓕, (archDerivAt hw .Fm x) g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
    rw [← integral_lincomb _ I_Hx I_Ex I_Fx]
    congr 1
    funext g
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have EL3 : ∫ g in 𝓕, ((archDerivAt hw .H x) + Complex.I • ((archDerivAt hw .E x) + (archDerivAt hw .Fm x))) g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      (1 : ℂ) * ∫ g in 𝓕, (archDerivAt hw .H x) g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) +
      Complex.I * ∫ g in 𝓕, (archDerivAt hw .E x) g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) +
      Complex.I * ∫ g in 𝓕, (archDerivAt hw .Fm x) g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
    rw [← integral_lincomb _ I_Hx I_Ex I_Fx]
    congr 1
    funext g
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have ER2 : ∫ g in 𝓕, x g * conj (((archDerivAt hw .H x') + Complex.I • ((archDerivAt hw .E x') + (archDerivAt hw .Fm x'))) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      (1 : ℂ) * ∫ g in 𝓕, x g * conj ((archDerivAt hw .H x') g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) +
      (-Complex.I) * ∫ g in 𝓕, x g * conj ((archDerivAt hw .E x') g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) +
      (-Complex.I) * ∫ g in 𝓕, x g * conj ((archDerivAt hw .Fm x') g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
    rw [← integral_lincomb _ I_Hx' I_Ex' I_Fx']
    congr 1
    funext g
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, Complex.conj_I]
    ring
  have ER3 : ∫ g in 𝓕, x g * conj (((archDerivAt hw .H x') - Complex.I • ((archDerivAt hw .E x') + (archDerivAt hw .Fm x'))) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      (1 : ℂ) * ∫ g in 𝓕, x g * conj ((archDerivAt hw .H x') g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) +
      Complex.I * ∫ g in 𝓕, x g * conj ((archDerivAt hw .E x') g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) +
      Complex.I * ∫ g in 𝓕, x g * conj ((archDerivAt hw .Fm x') g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
    rw [← integral_lincomb _ I_Hx' I_Ex' I_Fx']
    congr 1
    funext g
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_add, map_sub, map_mul,
      Complex.conj_I]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [EL1, ER1, S1, S2, S3, S4, S5, T4]
    ring
  · rw [EL2, ER2, S3, S6, S7]
    ring
  · rw [EL3, ER3, S3, S6, S7]
    ring

end Casimir

/-! ## The complex Casimir is self-adjoint (pin 4 `:81`) -/

section CasimirComplex

variable {K : Type} [Field K] [NumberField K]

attribute [local instance] NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

theorem main_archCasimirAtComplex
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsComplex)
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂)
    (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (h𝓕m : MeasurableSet 𝓕)
    (h𝓕s : 𝓕 ⊆ slab K e₁ e₂)
    (h𝓕 : IsFundamentalDomain (globalPoints (𝓞 K) K).range 𝓕
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        (slab K e₁ e₂)))
    (x x' : AdelicGL2 (𝓞 K) K → ℂ)
    (hx : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x (globalPoints (𝓞 K) K γ * g) = x g)
    (hx' : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x' (globalPoints (𝓞 K) K γ * g) = x' g)
    (hxc : Continuous x) (hx'c : Continuous x')
    (hxs : IsArchSmoothAtComplex hw x) (hx's : IsArchSmoothAtComplex hw x')
    (hD1 : ∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d x))
    (hD1' : ∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d x'))
    (hD2 : ∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' x)))
    (hD2' : ∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' x')))
    (B : ℝ) (hB : ∀ g : AdelicGL2 (𝓞 K) K, ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
      ‖x g‖ ≤ B ∧ ‖x' g‖ ≤ B ∧
      (∀ d : ArchDirComplex, ‖archDerivAtComplex hw d x g‖ ≤ B ∧ ‖archDerivAtComplex hw d x' g‖ ≤ B) ∧
      (∀ d d' : ArchDirComplex,
        ‖archDerivAtComplex hw d (archDerivAtComplex hw d' x) g‖ ≤ B ∧
        ‖archDerivAtComplex hw d (archDerivAtComplex hw d' x') g‖ ≤ B)) :
    let pPlus : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun u => archDelAt hw .E u + archDelBarAt hw .Fm u
    let pMinus : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun u => archDelAt hw .Fm u + archDelBarAt hw .E u
    (∀ d : ArchDir,
      ∫ g in 𝓕, archDelAt hw d x g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        -∫ g in 𝓕, x g * conj (archDelBarAt hw d x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    (∀ d : ArchDir,
      ∫ g in 𝓕, archDelBarAt hw d x g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        -∫ g in 𝓕, x g * conj (archDelAt hw d x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    (∫ g in 𝓕, archCasimirAtComplex hw x g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        ∫ g in 𝓕, x g * conj (archCasimirBarAtComplex hw x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    (∫ g in 𝓕, archCasimirBarAtComplex hw x g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        ∫ g in 𝓕, x g * conj (archCasimirAtComplex hw x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    (∫ g in 𝓕, pPlus x g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        -∫ g in 𝓕, x g * conj (pMinus x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    (∫ g in 𝓕, pMinus x g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        -∫ g in 𝓕, x g * conj (pPlus x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) := by
  intro pPlus pMinus
  set μ : Measure (AdelicGL2 (𝓞 K) K) := adelicGLHaar (Fin 2) (𝓞 K) K with hμ

  have hfin : μ 𝓕 < ⊤ := by
    have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
      K e₁ e₂ he₁ he 𝓕 h𝓕
    rwa [Set.inter_eq_left.mpr h𝓕s] at h

  have bx : ∀ g ∈ slab K e₁ e₂, ‖x g‖ ≤ B := fun g hg => (hB g hg).1
  have bx' : ∀ g ∈ slab K e₁ e₂, ‖x' g‖ ≤ B := fun g hg => (hB g hg).2.1
  have bD : ∀ d, ∀ g ∈ slab K e₁ e₂, ‖archDerivAtComplex hw d x g‖ ≤ B := fun d g hg => ((hB g hg).2.2.1 d).1
  have bD' : ∀ d, ∀ g ∈ slab K e₁ e₂, ‖archDerivAtComplex hw d x' g‖ ≤ B := fun d g hg => ((hB g hg).2.2.1 d).2
  have bDD : ∀ d d', ∀ g ∈ slab K e₁ e₂, ‖archDerivAtComplex hw d (archDerivAtComplex hw d' x) g‖ ≤ B :=
    fun d d' g hg => ((hB g hg).2.2.2 d d').1
  have bDD' : ∀ d d', ∀ g ∈ slab K e₁ e₂, ‖archDerivAtComplex hw d (archDerivAtComplex hw d' x') g‖ ≤ B :=
    fun d d' g hg => ((hB g hg).2.2.2 d d').2

  have iD : ∀ d, ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
      archDerivAtComplex hw d x (globalPoints (𝓞 K) K γ * g) = archDerivAtComplex hw d x g :=
    fun d => archDerivAtComplex_globalPoints_mul hw d hx
  have iD' : ∀ d, ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
      archDerivAtComplex hw d x' (globalPoints (𝓞 K) K γ * g) = archDerivAtComplex hw d x' g :=
    fun d => archDerivAtComplex_globalPoints_mul hw d hx'

  have skew : ∀ (d : ArchDirComplex) (u v : AdelicGL2 (𝓞 K) K → ℂ)
      (hu : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), u (globalPoints (𝓞 K) K γ * g) = u g)
      (hv : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), v (globalPoints (𝓞 K) K γ * g) = v g)
      (huc : Continuous u) (hvc : Continuous v) (hus : IsArchSmoothAtComplex hw u) (hvs : IsArchSmoothAtComplex hw v)
      (hDu : Continuous (archDerivAtComplex hw d u)) (hDv : Continuous (archDerivAtComplex hw d v))
      (bu : ∀ g ∈ slab K e₁ e₂, ‖u g‖ ≤ B) (bv : ∀ g ∈ slab K e₁ e₂, ‖v g‖ ≤ B)
      (bDu : ∀ g ∈ slab K e₁ e₂, ‖archDerivAtComplex hw d u g‖ ≤ B)
      (bDv : ∀ g ∈ slab K e₁ e₂, ‖archDerivAtComplex hw d v g‖ ≤ B),
      ∫ g in 𝓕, archDerivAtComplex hw d u g * conj (v g) ∂μ = -∫ g in 𝓕, u g * conj (archDerivAtComplex hw d v g) ∂μ := by
    intro d u v hu hv huc hvc hus hvs hDu hDv bu bv bDu bDv
    have h := AutomorphicForm.setIntegral_archDerivAtComplex_mul_conj_add_eq_zero_of_isFundamentalDomain K w hw d e₁ e₂
      he₁ he 𝓕 h𝓕m h𝓕s h𝓕 u v hu hv huc hvc hus hvs hDu hDv B
      (fun g hg => ⟨bu g hg, bv g hg, bDu g hg, bDv g hg⟩)
    rw [integral_add (integrable_mul_conj h𝓕m h𝓕s hfin hDu hvc bDu bv)
      (integrable_mul_conj h𝓕m h𝓕s hfin huc hDv bu bDv)] at h
    exact eq_neg_of_add_eq_zero_left h

  have RA : ∀ d : ArchDirComplex,
      ∫ g in 𝓕, archDerivAtComplex hw d x g * conj (x' g) ∂μ = -∫ g in 𝓕, x g * conj (archDerivAtComplex hw d x' g) ∂μ :=
    fun d => skew d x x' hx hx' hxc hx'c hxs hx's (hD1 d) (hD1' d) bx bx' (bD d) (bD' d)

  have RC : ∀ X Y : ArchDirComplex,
      ∫ g in 𝓕, archDerivAtComplex hw X (archDerivAtComplex hw Y x) g * conj (x' g) ∂μ =
        ∫ g in 𝓕, x g * conj (archDerivAtComplex hw Y (archDerivAtComplex hw X x') g) ∂μ := by
    intro X Y
    have h1 := skew X (archDerivAtComplex hw Y x) x' (iD Y) hx' (hD1 Y) hx'c (hxs.archDerivAtComplex Y) hx's
      (hD2 X Y) (hD1' X) (bD Y) bx' (bDD X Y) (bD' X)
    have h2 := skew Y x (archDerivAtComplex hw X x') hx (iD' X) hxc (hD1' X) hxs (hx's.archDerivAtComplex X)
      (hD1 Y) (hD2' Y X) bx (bD' X) (bD Y) (bDD' Y X)
    rw [h1, h2, neg_neg]

  have I1 : ∀ d, Integrable (fun g => archDerivAtComplex hw d x g * conj (x' g)) (μ.restrict 𝓕) :=
    fun d => integrable_mul_conj h𝓕m h𝓕s hfin (hD1 d) hx'c (bD d) bx'
  have I1' : ∀ d, Integrable (fun g => x g * conj (archDerivAtComplex hw d x' g)) (μ.restrict 𝓕) :=
    fun d => integrable_mul_conj h𝓕m h𝓕s hfin hxc (hD1' d) bx (bD' d)
  have I2 : ∀ X Y, Integrable (fun g => archDerivAtComplex hw X (archDerivAtComplex hw Y x) g * conj (x' g)) (μ.restrict 𝓕) :=
    fun X Y => integrable_mul_conj h𝓕m h𝓕s hfin (hD2 X Y) hx'c (bDD X Y) bx'
  have I2' : ∀ X Y, Integrable (fun g => x g * conj (archDerivAtComplex hw X (archDerivAtComplex hw Y x') g)) (μ.restrict 𝓕) :=
    fun X Y => integrable_mul_conj h𝓕m h𝓕s hfin hxc (hD2' X Y) bx (bDD' X Y)

  have ADJ1 : ∀ d : ArchDir, ∫ g in 𝓕, archDelAt hw d x g * conj (x' g) ∂μ = -∫ g in 𝓕, x g * conj (archDelBarAt hw d x' g) ∂μ := by
    intro d
    have hL : ∫ g in 𝓕, archDelAt hw d x g * conj (x' g) ∂μ =
        ∑ i, ![(1 / 2 : ℂ), -(Complex.I / 2)] i *
          ∫ g, ![fun g => archDerivAtComplex hw d.toComplex x g * conj (x' g),
                 fun g => archDerivAtComplex hw d.toComplexI x g * conj (x' g)] i g ∂(μ.restrict 𝓕) := by
      rw [← integral_lincomb_fin _ _ _ (fun i => by fin_cases i <;> simp [I1])]
      congr 1
      funext g
      simp only [archDelAt_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      ring
    have hR : ∫ g in 𝓕, x g * conj (archDelBarAt hw d x' g) ∂μ =
        ∑ i, ![(1 / 2 : ℂ), -(Complex.I / 2)] i *
          ∫ g, ![fun g => x g * conj (archDerivAtComplex hw d.toComplex x' g),
                 fun g => x g * conj (archDerivAtComplex hw d.toComplexI x' g)] i g ∂(μ.restrict 𝓕) := by
      rw [← integral_lincomb_fin _ _ _ (fun i => by fin_cases i <;> simp [I1'])]
      congr 1
      funext g
      simp only [archDelBarAt_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, map_add, map_mul, map_div₀, Complex.conj_I, map_one, map_ofNat]
      ring
    rw [hL, hR]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [RA, RA]
    ring
  have ADJ2 : ∀ d : ArchDir, ∫ g in 𝓕, archDelBarAt hw d x g * conj (x' g) ∂μ = -∫ g in 𝓕, x g * conj (archDelAt hw d x' g) ∂μ := by
    intro d
    have hL : ∫ g in 𝓕, archDelBarAt hw d x g * conj (x' g) ∂μ =
        ∑ i, ![(1 / 2 : ℂ), (Complex.I / 2)] i *
          ∫ g, ![fun g => archDerivAtComplex hw d.toComplex x g * conj (x' g),
                 fun g => archDerivAtComplex hw d.toComplexI x g * conj (x' g)] i g ∂(μ.restrict 𝓕) := by
      rw [← integral_lincomb_fin _ _ _ (fun i => by fin_cases i <;> simp [I1])]
      congr 1
      funext g
      simp only [archDelBarAt_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      ring
    have hR : ∫ g in 𝓕, x g * conj (archDelAt hw d x' g) ∂μ =
        ∑ i, ![(1 / 2 : ℂ), (Complex.I / 2)] i *
          ∫ g, ![fun g => x g * conj (archDerivAtComplex hw d.toComplex x' g),
                 fun g => x g * conj (archDerivAtComplex hw d.toComplexI x' g)] i g ∂(μ.restrict 𝓕) := by
      rw [← integral_lincomb_fin _ _ _ (fun i => by fin_cases i <;> simp [I1'])]
      congr 1
      funext g
      simp only [archDelAt_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, map_add, map_mul, map_div₀, map_neg, Complex.conj_I, map_one, map_ofNat]
      ring
    rw [hL, hR]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [RA, RA]
    ring

  have ddx : ∀ (X Y Z : ArchDirComplex) (a b : ℂ),
      archDerivAtComplex hw X (a • archDerivAtComplex hw Y x + b • archDerivAtComplex hw Z x) =
        a • archDerivAtComplex hw X (archDerivAtComplex hw Y x) + b • archDerivAtComplex hw X (archDerivAtComplex hw Z x) :=
    fun X Y Z a b => archDerivAtComplex_lin hw X (hxs.archDerivAtComplex Y) (hxs.archDerivAtComplex Z) a b
  have ddx' : ∀ (X Y Z : ArchDirComplex) (a b : ℂ),
      archDerivAtComplex hw X (a • archDerivAtComplex hw Y x' + b • archDerivAtComplex hw Z x') =
        a • archDerivAtComplex hw X (archDerivAtComplex hw Y x') + b • archDerivAtComplex hw X (archDerivAtComplex hw Z x') :=
    fun X Y Z a b => archDerivAtComplex_lin hw X (hx's.archDerivAtComplex Y) (hx's.archDerivAtComplex Z) a b

  have hC := AutomorphicForm.archDerivAtComplex_commutator_of_isArchSmoothAtComplex K hw x' hx's
  have Krel : ∀ (X Y Z : ArchDirComplex) (k : ℂ),
      archDerivAtComplex hw X (archDerivAtComplex hw Y x') - archDerivAtComplex hw Y (archDerivAtComplex hw X x') =
        k • archDerivAtComplex hw Z x' → (starRingEnd ℂ) k = k →
      ∫ g in 𝓕, x g * conj (archDerivAtComplex hw X (archDerivAtComplex hw Y x') g) ∂μ -
        ∫ g in 𝓕, x g * conj (archDerivAtComplex hw Y (archDerivAtComplex hw X x') g) ∂μ =
        k * ∫ g in 𝓕, x g * conj (archDerivAtComplex hw Z x' g) ∂μ := by
    intro X Y Z k h hk
    rw [← integral_sub (I2' X Y) (I2' Y X), ← integral_const_mul]
    congr 1
    funext g
    have hg := congrFun h g
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hg
    rw [← mul_sub, ← map_sub, hg, map_mul, hk]
    ring
  have K1 := Krel .E .Fm .H 1 hC.2.2.1 (map_one _)
  have K2 := Krel .E .iFm .iH 1 hC.2.2.2.2.2.1 (map_one _)
  have K3 := Krel .iE .Fm .iH 1 hC.2.2.2.2.2.2.1 (map_one _)
  have K4 := Krel .iE .iFm .H (-1) hC.2.2.2.2.2.2.2.2.2.2.2.1 (by simp)
  refine ⟨ADJ1, ADJ2, ?_, ?_, ?_, ?_⟩
  ·
    have hL : ∫ g in 𝓕, archCasimirAtComplex hw x g * conj (x' g) ∂μ =
        ∑ i, ![-(1/16 : ℂ), Complex.I/16, Complex.I/16, (1/16 : ℂ), -(1/4 : ℂ), Complex.I/4, Complex.I/4, (1/4 : ℂ), (1/4 : ℂ), -(Complex.I/4)] i *
          ∫ g, ![fun g => archDerivAtComplex hw .H (archDerivAtComplex hw .H x) g * conj (x' g),
                 fun g => archDerivAtComplex hw .H (archDerivAtComplex hw .iH x) g * conj (x' g),
                 fun g => archDerivAtComplex hw .iH (archDerivAtComplex hw .H x) g * conj (x' g),
                 fun g => archDerivAtComplex hw .iH (archDerivAtComplex hw .iH x) g * conj (x' g),
                 fun g => archDerivAtComplex hw .E (archDerivAtComplex hw .Fm x) g * conj (x' g),
                 fun g => archDerivAtComplex hw .E (archDerivAtComplex hw .iFm x) g * conj (x' g),
                 fun g => archDerivAtComplex hw .iE (archDerivAtComplex hw .Fm x) g * conj (x' g),
                 fun g => archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm x) g * conj (x' g),
                 fun g => archDerivAtComplex hw .H x g * conj (x' g),
                 fun g => archDerivAtComplex hw .iH x g * conj (x' g)] i g ∂(μ.restrict 𝓕) := by
      rw [← integral_lincomb_fin _ _ _ (fun i => by fin_cases i <;> simp [I1, I2])]
      congr 1
      funext g
      simp only [archCasimirAtComplex, archDelAt_eq, ArchDir.toComplex, ArchDir.toComplexI, ddx, Pi.neg_apply, Pi.add_apply,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]
      ring_nf
      simp only [Complex.I_sq]
      try ring
    have hR : ∫ g in 𝓕, x g * conj (archCasimirBarAtComplex hw x' g) ∂μ =
        ∑ i, ![-(1/16 : ℂ), Complex.I/16, Complex.I/16, (1/16 : ℂ), -(1/4 : ℂ), Complex.I/4, Complex.I/4, (1/4 : ℂ), (1/4 : ℂ), -(Complex.I/4)] i *
          ∫ g, ![fun g => x g * conj (archDerivAtComplex hw .H (archDerivAtComplex hw .H x') g),
                 fun g => x g * conj (archDerivAtComplex hw .H (archDerivAtComplex hw .iH x') g),
                 fun g => x g * conj (archDerivAtComplex hw .iH (archDerivAtComplex hw .H x') g),
                 fun g => x g * conj (archDerivAtComplex hw .iH (archDerivAtComplex hw .iH x') g),
                 fun g => x g * conj (archDerivAtComplex hw .E (archDerivAtComplex hw .Fm x') g),
                 fun g => x g * conj (archDerivAtComplex hw .E (archDerivAtComplex hw .iFm x') g),
                 fun g => x g * conj (archDerivAtComplex hw .iE (archDerivAtComplex hw .Fm x') g),
                 fun g => x g * conj (archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm x') g),
                 fun g => x g * conj (archDerivAtComplex hw .H x' g),
                 fun g => x g * conj (archDerivAtComplex hw .iH x' g)] i g ∂(μ.restrict 𝓕) := by
      rw [← integral_lincomb_fin _ _ _ (fun i => by fin_cases i <;> simp [I1', I2'])]
      congr 1
      funext g
      simp only [archCasimirBarAtComplex, archDelBarAt_eq, ArchDir.toComplex, ArchDir.toComplexI, ddx', Pi.neg_apply, Pi.add_apply,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_neg, map_add, map_sub, map_mul, map_div₀, Complex.conj_I,
        map_one, map_ofNat, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]
      ring_nf
      simp only [Complex.I_sq]
      try ring
    rw [hL, hR]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero, RC, RA]
    linear_combination (1/4 : ℂ) * K1 - (Complex.I/4) * K2 - (Complex.I/4) * K3 - (1/4 : ℂ) * K4
  ·
    have hL : ∫ g in 𝓕, archCasimirBarAtComplex hw x g * conj (x' g) ∂μ =
        ∑ i, ![-(1/16 : ℂ), -(Complex.I/16), -(Complex.I/16), (1/16 : ℂ), -(1/4 : ℂ), -(Complex.I/4), -(Complex.I/4), (1/4 : ℂ), (1/4 : ℂ), (Complex.I/4)] i *
          ∫ g, ![fun g => archDerivAtComplex hw .H (archDerivAtComplex hw .H x) g * conj (x' g),
                 fun g => archDerivAtComplex hw .H (archDerivAtComplex hw .iH x) g * conj (x' g),
                 fun g => archDerivAtComplex hw .iH (archDerivAtComplex hw .H x) g * conj (x' g),
                 fun g => archDerivAtComplex hw .iH (archDerivAtComplex hw .iH x) g * conj (x' g),
                 fun g => archDerivAtComplex hw .E (archDerivAtComplex hw .Fm x) g * conj (x' g),
                 fun g => archDerivAtComplex hw .E (archDerivAtComplex hw .iFm x) g * conj (x' g),
                 fun g => archDerivAtComplex hw .iE (archDerivAtComplex hw .Fm x) g * conj (x' g),
                 fun g => archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm x) g * conj (x' g),
                 fun g => archDerivAtComplex hw .H x g * conj (x' g),
                 fun g => archDerivAtComplex hw .iH x g * conj (x' g)] i g ∂(μ.restrict 𝓕) := by
      rw [← integral_lincomb_fin _ _ _ (fun i => by fin_cases i <;> simp [I1, I2])]
      congr 1
      funext g
      simp only [archCasimirBarAtComplex, archDelBarAt_eq, ArchDir.toComplex, ArchDir.toComplexI, ddx, Pi.neg_apply, Pi.add_apply,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]
      ring_nf
      simp only [Complex.I_sq]
      try ring
    have hR : ∫ g in 𝓕, x g * conj (archCasimirAtComplex hw x' g) ∂μ =
        ∑ i, ![-(1/16 : ℂ), -(Complex.I/16), -(Complex.I/16), (1/16 : ℂ), -(1/4 : ℂ), -(Complex.I/4), -(Complex.I/4), (1/4 : ℂ), (1/4 : ℂ), (Complex.I/4)] i *
          ∫ g, ![fun g => x g * conj (archDerivAtComplex hw .H (archDerivAtComplex hw .H x') g),
                 fun g => x g * conj (archDerivAtComplex hw .H (archDerivAtComplex hw .iH x') g),
                 fun g => x g * conj (archDerivAtComplex hw .iH (archDerivAtComplex hw .H x') g),
                 fun g => x g * conj (archDerivAtComplex hw .iH (archDerivAtComplex hw .iH x') g),
                 fun g => x g * conj (archDerivAtComplex hw .E (archDerivAtComplex hw .Fm x') g),
                 fun g => x g * conj (archDerivAtComplex hw .E (archDerivAtComplex hw .iFm x') g),
                 fun g => x g * conj (archDerivAtComplex hw .iE (archDerivAtComplex hw .Fm x') g),
                 fun g => x g * conj (archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm x') g),
                 fun g => x g * conj (archDerivAtComplex hw .H x' g),
                 fun g => x g * conj (archDerivAtComplex hw .iH x' g)] i g ∂(μ.restrict 𝓕) := by
      rw [← integral_lincomb_fin _ _ _ (fun i => by fin_cases i <;> simp [I1', I2'])]
      congr 1
      funext g
      simp only [archCasimirAtComplex, archDelAt_eq, ArchDir.toComplex, ArchDir.toComplexI, ddx', Pi.neg_apply, Pi.add_apply,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_neg, map_add, map_sub, map_mul, map_div₀, Complex.conj_I,
        map_one, map_ofNat, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]
      ring_nf
      simp only [Complex.I_sq]
      try ring
    rw [hL, hR]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero, RC, RA]
    linear_combination (1/4 : ℂ) * K1 + (Complex.I/4) * K2 + (Complex.I/4) * K3 - (1/4 : ℂ) * K4
  ·
    show ∫ g in 𝓕, (archDelAt hw .E x + archDelBarAt hw .Fm x) g * conj (x' g) ∂μ =
      -∫ g in 𝓕, x g * conj ((archDelAt hw .Fm x' + archDelBarAt hw .E x') g) ∂μ
    have hL : ∫ g in 𝓕, (archDelAt hw .E x + archDelBarAt hw .Fm x) g * conj (x' g) ∂μ =
        ∑ i, ![(1 / 2 : ℂ), -(Complex.I / 2), (1 / 2 : ℂ), (Complex.I / 2)] i *
          ∫ g, ![fun g => archDerivAtComplex hw .E x g * conj (x' g),
                 fun g => archDerivAtComplex hw .iE x g * conj (x' g),
                 fun g => archDerivAtComplex hw .Fm x g * conj (x' g),
                 fun g => archDerivAtComplex hw .iFm x g * conj (x' g)] i g ∂(μ.restrict 𝓕) := by
      rw [← integral_lincomb_fin _ _ _ (fun i => by fin_cases i <;> simp [I1])]
      congr 1
      funext g
      simp only [archDelAt_eq, archDelBarAt_eq, ArchDir.toComplex, ArchDir.toComplexI, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
      ring
    have hR : ∫ g in 𝓕, x g * conj ((archDelAt hw .Fm x' + archDelBarAt hw .E x') g) ∂μ =
        ∑ i, ![(1 / 2 : ℂ), -(Complex.I / 2), (1 / 2 : ℂ), (Complex.I / 2)] i *
          ∫ g, ![fun g => x g * conj (archDerivAtComplex hw .E x' g),
                 fun g => x g * conj (archDerivAtComplex hw .iE x' g),
                 fun g => x g * conj (archDerivAtComplex hw .Fm x' g),
                 fun g => x g * conj (archDerivAtComplex hw .iFm x' g)] i g ∂(μ.restrict 𝓕) := by
      rw [← integral_lincomb_fin _ _ _ (fun i => by fin_cases i <;> simp [I1'])]
      congr 1
      funext g
      simp only [archDelAt_eq, archDelBarAt_eq, ArchDir.toComplex, ArchDir.toComplexI, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, map_add, map_mul, map_div₀, map_neg,
        Complex.conj_I, map_one, map_ofNat]
      ring
    rw [hL, hR]
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.tail_cons]
    rw [RA, RA, RA, RA]
    ring
  ·
    show ∫ g in 𝓕, (archDelAt hw .Fm x + archDelBarAt hw .E x) g * conj (x' g) ∂μ =
      -∫ g in 𝓕, x g * conj ((archDelAt hw .E x' + archDelBarAt hw .Fm x') g) ∂μ
    have hL : ∫ g in 𝓕, (archDelAt hw .Fm x + archDelBarAt hw .E x) g * conj (x' g) ∂μ =
        ∑ i, ![(1 / 2 : ℂ), -(Complex.I / 2), (1 / 2 : ℂ), (Complex.I / 2)] i *
          ∫ g, ![fun g => archDerivAtComplex hw .Fm x g * conj (x' g),
                 fun g => archDerivAtComplex hw .iFm x g * conj (x' g),
                 fun g => archDerivAtComplex hw .E x g * conj (x' g),
                 fun g => archDerivAtComplex hw .iE x g * conj (x' g)] i g ∂(μ.restrict 𝓕) := by
      rw [← integral_lincomb_fin _ _ _ (fun i => by fin_cases i <;> simp [I1])]
      congr 1
      funext g
      simp only [archDelAt_eq, archDelBarAt_eq, ArchDir.toComplex, ArchDir.toComplexI, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
      ring
    have hR : ∫ g in 𝓕, x g * conj ((archDelAt hw .E x' + archDelBarAt hw .Fm x') g) ∂μ =
        ∑ i, ![(1 / 2 : ℂ), -(Complex.I / 2), (1 / 2 : ℂ), (Complex.I / 2)] i *
          ∫ g, ![fun g => x g * conj (archDerivAtComplex hw .Fm x' g),
                 fun g => x g * conj (archDerivAtComplex hw .iFm x' g),
                 fun g => x g * conj (archDerivAtComplex hw .E x' g),
                 fun g => x g * conj (archDerivAtComplex hw .iE x' g)] i g ∂(μ.restrict 𝓕) := by
      rw [← integral_lincomb_fin _ _ _ (fun i => by fin_cases i <;> simp [I1'])]
      congr 1
      funext g
      simp only [archDelAt_eq, archDelBarAt_eq, ArchDir.toComplex, ArchDir.toComplexI, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, map_add, map_mul, map_div₀, map_neg,
        Complex.conj_I, map_one, map_ofNat]
      ring
    rw [hL, hR]
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.tail_cons]
    rw [RA, RA, RA, RA]
    ring

end CasimirComplex

end PeterssonSkewAdjunction

/-! ## The two Casimir rows -/

/-- **The real place, the Casimir.** The Casimir is self-adjoint for the pairing and the two raised and
lowered combinations are adjoint to each other with a sign. -/
theorem setIntegral_archCasimirAt_mul_conj_eq_and_lower_adjoint_of_isFundamentalDomain
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal)
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂)
    (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (h𝓕m : MeasurableSet 𝓕)
    (h𝓕s : 𝓕 ⊆ {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂})
    (h𝓕 : IsFundamentalDomain (globalPoints (𝓞 K) K).range 𝓕
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂}))
    (x x' : AdelicGL2 (𝓞 K) K → ℂ)
    (hx : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x (globalPoints (𝓞 K) K γ * g) = x g)
    (hx' : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x' (globalPoints (𝓞 K) K γ * g) = x' g)
    (hxc : Continuous x) (hx'c : Continuous x')
    (hxs : IsArchSmoothAt hw x) (hx's : IsArchSmoothAt hw x')
    (hD1 : ∀ d : ArchDir, Continuous (archDerivAt hw d x)) (hD1' : ∀ d : ArchDir, Continuous (archDerivAt hw d x'))
    (hD2 : ∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' x)))
    (hD2' : ∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' x')))
    (B : ℝ) (hB : ∀ g : AdelicGL2 (𝓞 K) K, ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
      ‖x g‖ ≤ B ∧ ‖x' g‖ ≤ B ∧ (∀ d : ArchDir, ‖archDerivAt hw d x g‖ ≤ B ∧ ‖archDerivAt hw d x' g‖ ≤ B) ∧
      (∀ d d' : ArchDir, ‖archDerivAt hw d (archDerivAt hw d' x) g‖ ≤ B ∧ ‖archDerivAt hw d (archDerivAt hw d' x') g‖ ≤ B)) :
    let lower : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun u => archDerivAt hw .H u - Complex.I • (archDerivAt hw .E u + archDerivAt hw .Fm u)
    let raise : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun u => archDerivAt hw .H u + Complex.I • (archDerivAt hw .E u + archDerivAt hw .Fm u)
    (∫ g in 𝓕, archCasimirAt hw x g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        ∫ g in 𝓕, x g * conj (archCasimirAt hw x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    (∫ g in 𝓕, lower x g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        -∫ g in 𝓕, x g * conj (raise x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    (∫ g in 𝓕, raise x g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        -∫ g in 𝓕, x g * conj (lower x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) := by
  intro lower raise
  exact PeterssonSkewAdjunction.main_archCasimirAt K w hw e₁ e₂ he₁ he 𝓕 h𝓕m h𝓕s h𝓕 x x' hx hx' hxc hx'c
    hxs hx's hD1 hD1' hD2 hD2' B hB

/-- **The complex place, the Casimir.** The holomorphic and antiholomorphic derivatives are adjoint to
each other with a sign, the two Casimirs are adjoint to each other, and the two combined raising and
lowering operators are adjoint with a sign. -/
theorem setIntegral_archCasimirAtComplex_mul_conj_eq_and_archDelAt_adjoint_of_isFundamentalDomain
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsComplex)
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂)
    (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (h𝓕m : MeasurableSet 𝓕)
    (h𝓕s : 𝓕 ⊆ {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂})
    (h𝓕 : IsFundamentalDomain (globalPoints (𝓞 K) K).range 𝓕
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂}))
    (x x' : AdelicGL2 (𝓞 K) K → ℂ)
    (hx : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x (globalPoints (𝓞 K) K γ * g) = x g)
    (hx' : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x' (globalPoints (𝓞 K) K γ * g) = x' g)
    (hxc : Continuous x) (hx'c : Continuous x')
    (hxs : IsArchSmoothAtComplex hw x) (hx's : IsArchSmoothAtComplex hw x')
    (hD1 : ∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d x))
    (hD1' : ∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d x'))
    (hD2 : ∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' x)))
    (hD2' : ∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' x')))
    (B : ℝ) (hB : ∀ g : AdelicGL2 (𝓞 K) K, ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
      ‖x g‖ ≤ B ∧ ‖x' g‖ ≤ B ∧
      (∀ d : ArchDirComplex, ‖archDerivAtComplex hw d x g‖ ≤ B ∧ ‖archDerivAtComplex hw d x' g‖ ≤ B) ∧
      (∀ d d' : ArchDirComplex,
        ‖archDerivAtComplex hw d (archDerivAtComplex hw d' x) g‖ ≤ B ∧
        ‖archDerivAtComplex hw d (archDerivAtComplex hw d' x') g‖ ≤ B)) :
    let pPlus : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun u => archDelAt hw .E u + archDelBarAt hw .Fm u
    let pMinus : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun u => archDelAt hw .Fm u + archDelBarAt hw .E u
    (∀ d : ArchDir,
      ∫ g in 𝓕, archDelAt hw d x g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        -∫ g in 𝓕, x g * conj (archDelBarAt hw d x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    (∀ d : ArchDir,
      ∫ g in 𝓕, archDelBarAt hw d x g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        -∫ g in 𝓕, x g * conj (archDelAt hw d x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    (∫ g in 𝓕, archCasimirAtComplex hw x g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        ∫ g in 𝓕, x g * conj (archCasimirBarAtComplex hw x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    (∫ g in 𝓕, archCasimirBarAtComplex hw x g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        ∫ g in 𝓕, x g * conj (archCasimirAtComplex hw x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    (∫ g in 𝓕, pPlus x g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        -∫ g in 𝓕, x g * conj (pMinus x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    (∫ g in 𝓕, pMinus x g * conj (x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        -∫ g in 𝓕, x g * conj (pPlus x' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) := by
  intro pPlus pMinus
  exact PeterssonSkewAdjunction.main_archCasimirAtComplex K w hw e₁ e₂ he₁ he 𝓕 h𝓕m h𝓕s h𝓕 x x' hx hx'
    hxc hx'c hxs hx's hD1 hD1' hD2 hD2' B hB

end AutomorphicForm
