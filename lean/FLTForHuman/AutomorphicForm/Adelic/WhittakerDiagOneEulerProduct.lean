/-
The `diagOne` Whittaker coefficient of the Bruhat–Eisenstein series is a character times an Euler product.

For a flat family `φ` of induced sections, a global additive character `ψ` with its local data
(`ψv`, `nψ`, `θr`, `θc`), a uniformiser family `ϖ`, and `Re s` in the range where the whole series
converges, the `diagOne` Whittaker coefficient of the Bruhat–Eisenstein series at `1` factors as

  `w(...) (1) (diagOne b) = cpowChar ⋯ * ∑ ... Euler product`,

the identity that makes the Bruhat–Eisenstein `L`-function an Euler product. The proof is the adelic
unfolding at the `diagOne` torus, in the pin's four layers (the local shells, the archimedean
integrals, the finite-product bookkeeping, and the flat-family reduction).

The engine is `EisensteinGeneral/PiecePartialEulerProduct.lean`'s (the AF110 row): the pin states its
declarations in that file too, the port holds them `private`, and this set promotes them (§4 of the
set brief) so that this row imports instead of re-proving them.

Assumes, from earlier modules: `PieceFactorizationDatum`, `PiecePartialEulerProduct`,
`PieceWeylIntegrability`, the `AutomorphicForm` induced-section/Whittaker family, and
SET-AF112's `AddCharLocalComponents` and `BruhatEisensteinWhittakerSummability`.

Transcribed from the pin below (pinned `aa2d8b3`, 2,695 `S_` lines).

## The rows

* `AutomorphicForm.whittakerCoefficient_bruhatEisenstein_diagOne_eq_cpowChar_mul_sum_eulerProduct_of_flat_family` — 2,695 pin `S_` lines.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AutomorphicForm_whittakerCoefficient_bruhatEisenstein_diagOne_eq_cpowChar_mul_sum_eulerProduct_of_flat_family.lean>

## Port deltas

Statement-level: none — `check_port` diffs the headline `ok` against the pin's `Theorems/` wrapper,
and the flat-family hypothesis and the `_`-prefixed binders are the pin's text.

Proof-level (all inside the pin's `T1Helpers` helper blocks; the pin's names are kept):

* the pin's `T1Helpers` label is dropped: its helpers are `private` in `namespace AutomorphicForm`
  (this module's own namespace), as the pin states them `private` in its stage namespace;
* `isOpen_setOf_valued_le`, `isOpen_setOf_valued_lt` and `measurableSet_setOf_valued_eq_exp`
  (pin `:353`, `:357`, `:361`) are **not** restated: the port already has them public as
  `EisensteinGeneral.TwistedSmoothLocal.{isOpen_setOf_valued_le, isOpen_setOf_valued_lt,
  measurableSet_setOf_valued_eq}` (`EisensteinGeneral/LocalRamShells.lean:79,89,104`), and
  `measurableSet_adicCompletionIntegers` (pin `:375`) is inlined as the `.measurableSet` of
  `FiniteAdelicFactorization.isOpen_adicCompletionIntegers` (the pin's uses at `:391` and `:414`);
* `pc_isCompact_integers`/`pc_isOpen_integers` (pin `:851`, `:855`) are not needed: the port has the
  first public (`EisensteinGeneral.Piece.pc_isCompact_integers`,
  `EisensteinGeneral/PieceWeylIntegrability.lean:366`) and the second is
  `FiniteAdelicFactorization.isOpen_adicCompletionIntegers`; the pin uses both only inside the
  promoted `pc_*` engine, whose port proofs already carry them;
* `pc_finite_value` (pin `:1291`) is **not** transcribed: the port holds it `private` as a binder
  variant (`EisensteinGeneral/PiecePartialEulerProduct.lean:912`) and its only consumer
  `pc_term_value` is public, so the headline's proof never names it;
* `centralScalar_val` is proved in the pin's `!![z,0;0,z]` form (pin `:84`); the port's
  `AutomorphicForm.centralScalar_val` states `Matrix.diagonal (fun _ => z)` and lives in a module
  (`NumberTheory/AdelicVolume.lean:116`) this one does not import, so the six-line proof is the
  pin's own;
* the call site of `integrable_weyl_unipotent_mul_of_factorization` (pin's solution, in the `hint`
  block) drops the pin's `Piece.` prefix: the port declares that theorem at the **root** name
  (`EisensteinGeneral/PieceWeylIntegrability.lean:548`, after `end PieceLayer`), unlike the pin's
  `EgenPiece` label. The port's form takes the local characters `ψv` (preamble item 1) and is used
  as stated;
* `pc_norm_mul_cpow_lt_one` is the port's `v`-first binder variant
  (`EisensteinGeneral/PieceWeylIntegrability.lean:276`), applied through `simpa` at the pin's
  `ℂ`-spelling of the same bound;
* proof-script adaptations only: `if_pos`/`if_neg` → `ite_eq_left`/`ite_eq_right` (mathlib `v4.34`
  deprecations), `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`, `simp only [Φ, …]` for the local `let`s
  where the pin's `rw` list unfolds them, and `congr 1 <;> simp` split over two lines (the
  `linter.unnecessarySeqFocus` style linter);
* `set_option linter.style.haveILetI false` on the theorem: the pin's proof installs three local
  instances (`letI := pc_locBorel F v`, `pc_locBorelSpace`, `pc_isAddHaarMeasure_locHaar`) and the
  style linter rejects `letI`/`haveI` in a proposition goal; the same option guards the port's
  `pc_integrable_affine` (`EisensteinGeneral/PieceWeylIntegrability.lean:519`);
* one `open` added, `NumberField.AdelicHaar`: the pin opens it (for `adelicAddHaar`) and the
  module's scaffold did not. It does not touch the headline's statement.

spec-pin: Theorems/Thm_AutomorphicForm_whittakerCoefficient_bruhatEisenstein_diagOne_eq_cpowChar_mul_sum_eulerProduct_of_flat_family.lean
spec-pin: P2M/Sol/S_AutomorphicForm_whittakerCoefficient_bruhatEisenstein_diagOne_eq_cpowChar_mul_sum_eulerProduct_of_flat_family.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.Basic
import FLTForHuman.AutomorphicForm.Adelic.WindowedSiegel.RowIsometry
import FLTForHuman.AutomorphicForm.Adelic.HeightWeylMass
import FLTForHuman.AutomorphicForm.Adelic.InducedSection
import FLTForHuman.AutomorphicForm.Adelic.EtaFamily
import FLTForHuman.AutomorphicForm.Adelic.ArchKFinite
import FLTForHuman.AutomorphicForm.Adelic.SmoothAutomorphicFn
import FLTForHuman.AutomorphicForm.Adelic.ProductionPins
import FLTForHuman.AutomorphicForm.Adelic.WhittakerCoefficient
import FLTForHuman.AutomorphicForm.Adelic.ConstantTerm
import FLTForHuman.AutomorphicForm.Adelic.WeylIntertwining
import FLTForHuman.NumberTheory.AdelicBox
import FLTForHuman.NumberTheory.AdelicModulus
import FLTForHuman.NumberTheory.AdelicLevel.Level
import FLTForHuman.NumberTheory.NumberField.MixedEmbedding
import FLTForHuman.NumberTheory.NumberField.TateGlobal.Defs
import FLTForHuman.EisensteinGeneral.PieceFactorizationDatum
import FLTForHuman.EisensteinGeneral.PiecePartialEulerProduct
import FLTForHuman.AutomorphicForm.Adelic.AddCharLocalComponents
import FLTForHuman.AutomorphicForm.Adelic.BruhatEisensteinWhittakerSummability
import FLTForHuman.EisensteinGeneral.PieceWeylIntegrability
import FLTForHuman.EisensteinGeneral.ArchIntegralBound
import FLTForHuman.EisensteinGeneral.LocalRam
import FLTForHuman.EisensteinGeneral.LocalUnr
import FLTForHuman.NumberTheory.NumberField.HeightOneSpectrumSummable
import FLTForHuman.NumberTheory.NumberField.GlobalAddChar.Circle
import FLTForHuman.LanglandsTunnell.TateLocalZeta
import FLTForHuman.LanglandsTunnell.StandardLocalConstantsAt

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicBox NumberField.AdelicLevel
open NumberField.InfinitePlace NumberField.AdelicHaar AutomorphicForm.WindowedSiegel
open MeasureTheory AutomorphicForm
open scoped Classical NNReal nonZeroDivisors

namespace AutomorphicForm

/-! ## The `diagOne` / `centralScalar` value dictionary and the induced-section translate

The pin's `T1Helpers` block (`:60`–`:180`): the matrix values of `adelicWeyl`, `diagOne`,
`centralScalar`, the Borel membership and Iwasawa components of `centralScalar y * (diagOne y)⁻¹`,
and the translation of the Bruhat cell by `diagOne y`. -/

section DiagOneDictionary

variable (F : Type) [Field F] [NumberField F]

private theorem adelicWeyl_val :
    ((adelicWeyl (𝓞 F) F : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = !![0, 1; 1, 0] := by
  ext i j
  rw [show adelicWeyl (𝓞 F) F = globalPoints (𝓞 F) F gl2Weyl from rfl, globalPoints_apply, gl2Weyl_val]
  fin_cases i <;> fin_cases j <;> simp

private theorem diagOne_val (a : (AdeleRing (𝓞 F) F)ˣ) :
    ((diagOne a : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = !![(a : AdeleRing (𝓞 F) F), 0; 0, 1] := by
  ext i j
  rw [diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

private theorem diagOne_inv_val (a : (AdeleRing (𝓞 F) F)ˣ) :
    (((diagOne a)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = !![((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F), 0; 0, 1] := by
  rw [← map_inv, diagOne_val]

private theorem centralScalar_val (z : (AdeleRing (𝓞 F) F)ˣ) :
    ((centralScalar (𝓞 F) F z : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = !![(z : AdeleRing (𝓞 F) F), 0; 0, (z : AdeleRing (𝓞 F) F)] := by
  change Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 F) F) = _
  ext i j
  rw [Matrix.scalar_apply]
  fin_cases i <;> fin_cases j <;> simp

private theorem diagOne_mem_adelicBorel (y : (AdeleRing (𝓞 F) F)ˣ) :
    (diagOne y : AdelicGL2 (𝓞 F) F) ∈ adelicBorel (𝓞 F) F := by
  show ((diagOne y : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0
  rw [diagOne_val]
  simp

private theorem centralScalar_mul_diagOne_inv_mem_adelicBorel (y : (AdeleRing (𝓞 F) F)ˣ) :
    centralScalar (𝓞 F) F y * (diagOne y)⁻¹ ∈ adelicBorel (𝓞 F) F :=
  (adelicBorel (𝓞 F) F).mul_mem (centralScalar_mem_adelicBorel (𝓞 F) F y)
    ((adelicBorel (𝓞 F) F).inv_mem (diagOne_mem_adelicBorel F y))

private theorem centralScalar_mul_diagOne_inv_val (y : (AdeleRing (𝓞 F) F)ˣ) :
    ((centralScalar (𝓞 F) F y * (diagOne y)⁻¹ : AdelicGL2 (𝓞 F) F)
      : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) = !![1, 0; 0, (y : AdeleRing (𝓞 F) F)] := by
  rw [Units.val_mul, centralScalar_val, diagOne_inv_val, Matrix.mul_fin_two]
  simp

private theorem borelDiagFst_centralScalar_mul_diagOne_inv (y : (AdeleRing (𝓞 F) F)ˣ) :
    borelDiagFst (⟨centralScalar (𝓞 F) F y * (diagOne y)⁻¹, centralScalar_mul_diagOne_inv_mem_adelicBorel F y⟩ :
      ↥(adelicBorel (𝓞 F) F)) = 1 := by
  apply Units.ext
  rw [borelDiagFst_apply_val]
  show ((centralScalar (𝓞 F) F y * (diagOne y)⁻¹ : AdelicGL2 (𝓞 F) F)
      : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 = 1
  rw [centralScalar_mul_diagOne_inv_val]
  simp

private theorem borelDiagSnd_centralScalar_mul_diagOne_inv (y : (AdeleRing (𝓞 F) F)ˣ) :
    borelDiagSnd (⟨centralScalar (𝓞 F) F y * (diagOne y)⁻¹, centralScalar_mul_diagOne_inv_mem_adelicBorel F y⟩ :
      ↥(adelicBorel (𝓞 F) F)) = y := by
  apply Units.ext
  rw [borelDiagSnd_apply_val]
  show ((centralScalar (𝓞 F) F y * (diagOne y)⁻¹ : AdelicGL2 (𝓞 F) F)
      : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 = (y : AdeleRing (𝓞 F) F)
  rw [centralScalar_mul_diagOne_inv_val]
  simp

private theorem adelicWeyl_mul_unipotentGL2_mul_diagOne (y : (AdeleRing (𝓞 F) F)ˣ)
    (x : AdeleRing (𝓞 F) F) :
    adelicWeyl (𝓞 F) F * unipotentGL2 x * diagOne y
      = (centralScalar (𝓞 F) F y * (diagOne y)⁻¹) *
          (adelicWeyl (𝓞 F) F * unipotentGL2 (((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x)) := by
  apply Units.ext
  change ((adelicWeyl (𝓞 F) F : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        * ((unipotentGL2 x : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        * ((diagOne y : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = ((centralScalar (𝓞 F) F y * (diagOne y)⁻¹ : AdelicGL2 (𝓞 F) F)
          : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        * (((adelicWeyl (𝓞 F) F : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
          * ((unipotentGL2 (((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x) : AdelicGL2 (𝓞 F) F) :
              Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))
  rw [centralScalar_mul_diagOne_inv_val, adelicWeyl_val, unipotentGL2_coe, unipotentGL2_coe, diagOne_val,
    Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.mul_fin_two]
  congr 1
  simp

private theorem apply_adelicWeyl_mul_unipotentGL2_mul_diagOne_of_isInducedSection
    (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ)) (s : ℂ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) φ)
    (y : (AdeleRing (𝓞 F) F)ˣ) (x : AdeleRing (𝓞 F) F) :
    φ (adelicWeyl (𝓞 F) F * unipotentGL2 x * diagOne y)
      = ((cpowChar α hα (-(s + 1 / 2)) y : ℂˣ) : ℂ) *
          φ (adelicWeyl (𝓞 F) F * unipotentGL2 (((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x) * 1) := by
  rw [mul_one, adelicWeyl_mul_unipotentGL2_mul_diagOne F y x,
    hφ _ (centralScalar_mul_diagOne_inv_mem_adelicBorel F y),
    borelDiagFst_centralScalar_mul_diagOne_inv, borelDiagSnd_centralScalar_mul_diagOne_inv, map_one,
    Units.val_one, one_mul, etaSnd_apply, MonoidHom.one_apply, one_mul]

end DiagOneDictionary

/-! ## The shell/twist integrals and the character algebra

The pin's `T1Helpers` blocks `B4`/`B5` (`:318`–`:560`): the two translate-invariance identities
of the twisted integrals (over the integer ring and over a shell), the valuation equality, and the
`cpowChar` identity that produces the headline's character factor. -/

section ShellTwist

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

private theorem addChar_neg_mul_eq_of_valued_le (ψ : AddChar (v.adicCompletion F) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (w w₀ x : v.adicCompletion F) (h : Valued.v ((w - w₀) * x) ≤ WithZero.exp n) :
    ψ (-(w * x)) = ψ (-(w₀ * x)) := by
  have hsplit : -(w * x) = -(w₀ * x) + -((w - w₀) * x) := by ring
  rw [hsplit, AddChar.map_add_eq_mul, hψn (-((w - w₀) * x)) (by rwa [Valuation.map_neg]), mul_one]

private theorem setIntegral_integers_twist_eq_of_valued_sub_le
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)] (μ : Measure (v.adicCompletion F))
    (ψ : AddChar (v.adicCompletion F) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (A : v.adicCompletion F → ℂ) (w w₀ : v.adicCompletion F) (hw : Valued.v (w - w₀) ≤ WithZero.exp n) :
    ∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)),
        (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A x * ψ (-(w * x)) ∂μ
      = ∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)),
        (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A x * ψ (-(w₀ * x)) ∂μ := by
  refine setIntegral_congr_fun
    (EisensteinGeneral.FiniteAdelicFactorization.isOpen_adicCompletionIntegers F v).measurableSet fun x hx => ?_
  have hx1 : Valued.v x ≤ 1 := hx
  have h : Valued.v ((w - w₀) * x) ≤ WithZero.exp n := by
    rw [Valuation.map_mul]
    calc Valued.v (w - w₀) * Valued.v x ≤ WithZero.exp n * 1 := mul_le_mul' hw hx1
      _ = WithZero.exp n := mul_one _
  simp only [addChar_neg_mul_eq_of_valued_le F v ψ n hψn w w₀ x h]

private theorem setIntegral_shell_twist_eq_of_valued_sub_le
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)] (μ : Measure (v.adicCompletion F))
    (ψ : AddChar (v.adicCompletion F) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (G : v.adicCompletion F → ℂ) (k : ℕ) (w w₀ : v.adicCompletion F)
    (hw : Valued.v (w - w₀) ≤ WithZero.exp (n - k)) :
    ∫ x in {x : v.adicCompletion F | Valued.v x = WithZero.exp (k : ℤ)}, G x * ψ (-(w * x)) ∂μ
      = ∫ x in {x : v.adicCompletion F | Valued.v x = WithZero.exp (k : ℤ)}, G x * ψ (-(w₀ * x)) ∂μ := by
  refine setIntegral_congr_fun
    (EisensteinGeneral.TwistedSmoothLocal.measurableSet_setOf_valued_eq (v := v) (k := (k : ℤ))) fun x hx => ?_
  have hxk : Valued.v x = WithZero.exp (k : ℤ) := hx
  have h : Valued.v ((w - w₀) * x) ≤ WithZero.exp n := by
    rw [Valuation.map_mul, hxk]
    calc Valued.v (w - w₀) * WithZero.exp (k : ℤ) ≤ WithZero.exp (n - k) * WithZero.exp (k : ℤ) :=
          mul_le_mul' hw le_rfl
      _ = WithZero.exp n := by rw [← WithZero.exp_add, sub_add_cancel]
  simp only [addChar_neg_mul_eq_of_valued_le F v ψ n hψn w w₀ x h]

private theorem valued_eq_of_valued_sub_lt (w w₀ : v.adicCompletion F) (h : Valued.v (w - w₀) < Valued.v w₀) :
    Valued.v w = Valued.v w₀ := by
  have := Valuation.map_add_eq_of_lt_left (v := (Valued.v : Valuation (v.adicCompletion F) _)) h
  rwa [add_sub_cancel] at this

end ShellTwist

private theorem cpowChar_neg_add_half_mul_self (F : Type) [Field F] [NumberField F]
    (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ)
    (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ)) (s : ℂ) (y : (AdeleRing (𝓞 F) F)ˣ) :
    ((cpowChar α hα (-(s + 1 / 2)) y : ℂˣ) : ℂ) * ((((α y : ℝˣ) : ℝ) : ℂ))
      = ((cpowChar α hα (1 / 2 - s) y : ℂˣ) : ℂ) := by
  have h0 : (((α y : ℝˣ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hα y).ne'
  rw [cpowChar_apply_val, cpowChar_apply_val]
  calc (((α y : ℝˣ) : ℝ) : ℂ) ^ (-(s + 1 / 2)) * (((α y : ℝˣ) : ℝ) : ℂ)
      = (((α y : ℝˣ) : ℝ) : ℂ) ^ (-(s + 1 / 2)) * (((α y : ℝˣ) : ℝ) : ℂ) ^ (1 : ℂ) := by
        rw [Complex.cpow_one]
    _ = (((α y : ℝˣ) : ℝ) : ℂ) ^ (-(s + 1 / 2) + 1) := (Complex.cpow_add _ _ h0).symm
    _ = (((α y : ℝˣ) : ℝ) : ℂ) ^ (1 / 2 - s) := by
        congr 1
        ring

set_option linter.style.haveILetI false in
open EisensteinGeneral EisensteinGeneral.Piece in
theorem whittakerCoefficient_bruhatEisenstein_diagOne_eq_cpowChar_mul_sum_eulerProduct_of_flat_family (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (_hψ : IsGlobalAddChar F ψ)
      (ψv : (v : HeightOneSpectrum (𝓞 F)) → AddChar (v.adicCompletion F) ℂ)
      (nψ : HeightOneSpectrum (𝓞 F) → ℤ)
      (_hnψfin : (Function.support nψ).Finite)
      (_hψv : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F),
        Valued.v x ≤ WithZero.exp (nψ v) → ψv v x = 1)
      (_hψv' : ∀ v : HeightOneSpectrum (𝓞 F),
        ∃ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp (nψ v + 1) ∧ ψv v x ≠ 1)
      (_hψfin : ∀ x : FiniteAdeleRing (𝓞 F) F,
        ψ (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) x)
        = ∏ᶠ v : HeightOneSpectrum (𝓞 F), ψv v (x v))
      (θr : {w : InfinitePlace F // w.IsReal} → ℝ) (_hθr : ∀ i, θr i ≠ 0)
      (θc : {w : InfinitePlace F // w.IsComplex} → ℂ) (_hθc : ∀ w, θc w ≠ 0)
      (_hψarch : ∀ p : mixedEmbedding.mixedSpace F,
        ψ (AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm p))
        = (∏ i : {w : InfinitePlace F // w.IsReal},
        Complex.exp (-(((2 * Real.pi * θr i * p.1 i : ℝ) : ℂ) * Complex.I)))
        * ∏ w : {w : InfinitePlace F // w.IsComplex},
        Complex.exp (-(((4 * Real.pi * (θc w * p.2 w).re : ℝ) : ℂ) * Complex.I)))
      (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
      (_hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
      (_hφflat : ∀ (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
          glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
          φ s k = φ s' k)
      (_hφne : ∃ (s : ℂ) (g : AdelicGL2 (𝓞 F) F), φ s g ≠ 0),
    let E : ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun s h =>
      φ s h + ∑' ξ : F, φ s (adelicWeyl (𝓞 F) F *
        unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * h)
    let jR : ℤ → ℂ → ℝ → ℂ := fun k w t => ∫ x : ℝ,
      ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
          * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w)
          * Complex.exp (-(((2 * Real.pi * t * x : ℝ) : ℂ) * Complex.I))
    let jC : ℕ → ℕ → ℂ → ℂ → ℂ := fun a b w ζ => ∫ z : ℂ,
      z ^ a * (starRingEnd ℂ) z ^ b * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-w)
          * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I))
    ∃ (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ) (C : Fin n → ℂ → ℂ)
      (kdat : Fin n → {w : InfinitePlace F // w.IsReal} → ℤ)
      (τr : Fin n → {w : InfinitePlace F // w.IsReal} → ℝ)
      (abm : Fin n → {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
      (τc : Fin n → {w : InfinitePlace F // w.IsComplex} → ℝ)
      (a : (AdeleRing (𝓞 F) F)ˣ) (u : AdeleRing (𝓞 F) F)
      (thr : HeightOneSpectrum (𝓞 F) → ℤ)
      (Φ : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ → ℂ),
      (∀ j, Differentiable ℂ (C j)) ∧
      (∀ (j : Fin n) (w : {w : InfinitePlace F // w.IsComplex}),
        (abm j w).1 + (abm j w).2.1 ≤ (abm j w).2.2) ∧
      (∀ v ∉ S, thr v = 0) ∧
      (∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 F)) (w : v.adicCompletion F), Differentiable ℂ (Φ j v w)) ∧
      (∀ (j : Fin n), ∀ v ∉ S, ∀ (w : v.adicCompletion F) (s : ℂ), Valued.v w = 1 → Φ j v w s = 1) ∧
      (∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 F)) (w : v.adicCompletion F) (s : ℂ), w ≠ 0 →
        WithZero.exp (thr v) < Valued.v w → Φ j v w s = 0) ∧
      (∀ R : ℝ, ∃ (M : ℝ) (κ : ℕ), 0 ≤ M ∧ ∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 F))
        (w : v.adicCompletion F) (e : ℤ) (s : ℂ), ‖s‖ ≤ R → Valued.v w = WithZero.exp e →
          ‖Φ j v w s‖ ≤ (if v ∈ S then M else 1) * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-e).toNat) ^ κ) ∧
      (∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 F)) (w₀ : v.adicCompletion F), w₀ ≠ 0 → ∃ δ : ℤ,
        ∀ (w : v.adicCompletion F) (s : ℂ), Valued.v (w - w₀) ≤ WithZero.exp δ → Φ j v w s = Φ j v w₀ s) ∧
      ∀ (s : ℂ), 1 < s.re → ∀ (ξ : F), ξ ≠ 0 → ∀ y : (AdeleRing (𝓞 F) F)ˣ,
        whittakerCoefficient F (productionPins F) ψ (E s) ξ (diagOne y)
          = ((cpowChar α hα (1 / 2 - s) y : ℂˣ) : ℂ)
            * ∑ j : Fin n, C j s
              * ((((2 : ℝ) ^ nrComplexPlaces F / Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ)
                  * ((((distribHaarChar (AdeleRing (𝓞 F) F) a : ℝ≥0) : ℝ) : ℂ)⁻¹
                  * ψ (algebraMap F (AdeleRing (𝓞 F) F) ξ * (y : AdeleRing (𝓞 F) F) * u)))
              * (∏ i : {w : InfinitePlace F // w.IsReal},
                  jR (kdat j i) (s + 1 / 2 + ((τr j i : ℝ) : ℂ) * Complex.I / 2)
                    (-(θr i * (InfiniteAdeleRing.ringEquiv_mixedSpace F
                      (algebraMap F (AdeleRing (𝓞 F) F) ξ * (y : AdeleRing (𝓞 F) F)
                        * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).1).1 i)))
              * (∏ w : {w : InfinitePlace F // w.IsComplex},
                  jC (abm j w).1 (abm j w).2.1
                    (2 * s + 1 + ((abm j w).2.2 : ℂ) / 2 + ((τc j w : ℝ) : ℂ) * Complex.I / 2)
                    (-(θc w * (InfiniteAdeleRing.ringEquiv_mixedSpace F
                      (algebraMap F (AdeleRing (𝓞 F) F) ξ * (y : AdeleRing (𝓞 F) F)
                        * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).1).2 w)))
              * ((∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
                  (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))))
                * ∏ᶠ v : HeightOneSpectrum (𝓞 F),
                    Φ j v ((algebraMap F (AdeleRing (𝓞 F) F) ξ * (y : AdeleRing (𝓞 F) F)
                        * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).2 v) s) := by
  intro α hα ψ hψ ψv nψ hnψfin hψv hψv' hψfin θr hθr θc hθc hψarch ϖ hϖ φ hφ hφK hφf hφjc hφhol hφflat hφne E
    jR jC
  classical
  haveI := NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 F) F

  have h1u : IsUnitaryChar (𝓞 F) F (1 : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) := by
    intro x
    simp only [MonoidHom.one_apply, Units.val_one, norm_one]
  have h1c : Continuous (1 : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) := continuous_const
  set χv : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ →* ℂˣ :=
    NumberField.TateGlobal.localChar (1 : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) with hχv
  have hχv1 : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ), χv v x = 1 := by
    intro v x
    simp only [hχv, NumberField.TateGlobal.localChar, MonoidHom.one_comp, MonoidHom.one_apply]
  have hψv1 : ∀ (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F), ‖ψv v y‖ = 1 :=
    pc_norm_localChar_eq_one F ψ hψ ψv hψfin
  have hDall := Piece.exists_forall_nonempty_factorizationDatum F hα 1 1 h1u h1u h1c h1c ψ hψ ψv nψ hnψfin hψv
    hψv' hψfin θr hθr θc hθc hψarch 1 (by ext x; simp [MonoidHom.inv_apply]) ϖ hϖ φ hφ hφK hφf hφjc hφhol hφflat hφne
  obtain ⟨S, hS⟩ := hDall 1
  obtain ⟨D⟩ := hS S (Finset.Subset.refl S)
  obtain ⟨cS, mS, n, A, B, h, kdat, τr, abm, τc, Wr, Wc, a, u, C,
    hχϖ, hχS, hnψ, hcS, hχc, hmS, hA, hB, hoff, hon, habm, hWr, hWc, hC, hfac⟩ := D

  let thr : HeightOneSpectrum (𝓞 F) → ℤ := fun v => if v ∈ S then nψ v + ((max mS (cS v) : ℕ) : ℤ) else 0
  let Φ : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ → ℂ := fun j v w s =>
    if v ∈ S then
      pc_corrOn (Ideal.absNorm v.asIdeal) (nψ v) (cS v) mS (pc_exp w)
        ((pc_locHaar F v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
        (∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)),
          (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (A j v) x * ψv v (-(w * x))
            ∂(pc_locHaar F v))
        (fun k : ℕ => ∫ x in {x : v.adicCompletion F | Valued.v x = WithZero.exp (k : ℤ)},
          LanglandsTunnell.TateLocal.charExt (χv v)⁻¹ x * B j v x⁻¹ * ψv v (-(w * x)) ∂(pc_locHaar F v)) s
    else pc_corrOff ((χv v (ϖ v) : ℂˣ) : ℂ) (Ideal.absNorm v.asIdeal) (pc_exp w) s
  have hΦcorr : ∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 F)) (wf : FiniteAdeleRing (𝓞 F) F) (s : ℂ),
      pc_corr F S χv ϖ ψv nψ cS mS (A j) (B j) wf v s = Φ j v (wf v) s := fun _ _ _ _ => rfl
  have hN2 : ∀ v : HeightOneSpectrum (𝓞 F), 2 ≤ Ideal.absNorm v.asIdeal := fun v => pc_one_lt_absNorm F v
  have hexp_of_eq : ∀ {v : HeightOneSpectrum (𝓞 F)} {w : v.adicCompletion F} {e : ℤ},
      Valued.v w = WithZero.exp e → w ≠ 0 ∧ pc_exp w = e := by
    intro v w e he
    have hw0 : w ≠ 0 := by
      intro h0
      rw [h0, map_zero] at he
      exact WithZero.zero_ne_coe he
    refine ⟨hw0, ?_⟩
    have h2 := (pc_valued_eq_exp hw0).symm.trans he
    exact WithZero.exp_injective h2
  refine ⟨S, n, C, kdat, τr, abm, τc, a, u, thr, Φ, hC, habm, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro v hv
    simp only [thr, hv, ↓reduceIte]
  ·
    intro j v w
    have hN : 0 < Ideal.absNorm v.asIdeal := by have := hN2 v; omega
    by_cases hv : v ∈ S
    · simp only [Φ, hv, ↓reduceIte]
      exact pc_corrOn_differentiable hN _ _ _ _ _ _ _
    · simp only [Φ, hv, ↓reduceIte]
      exact pc_corrOff_differentiable _ hN _
  ·
    intro j v hv w s hw
    obtain ⟨-, he⟩ := hexp_of_eq (e := 0) (by rw [hw, WithZero.exp_zero])
    simp only [Φ, hv, ↓reduceIte, pc_corrOff, he, le_refl, neg_zero, Int.toNat_zero, pc_geom, zero_add,
      Finset.range_one, Finset.sum_singleton, pow_zero]
  ·
    intro j v w s hw0 hlt
    rw [pc_valued_eq_exp hw0, WithZero.exp_lt_exp] at hlt
    by_cases hv : v ∈ S
    · simp only [thr, hv, ↓reduceIte] at hlt
      simp only [Φ, hv, ↓reduceIte, pc_corrOn]
      rw [ite_eq_right (by omega)]
    · simp only [thr, hv, ↓reduceIte] at hlt
      simp only [Φ, hv, ↓reduceIte, pc_corrOff]
      rw [ite_eq_right (by omega)]
  ·
    intro R
    set R' : ℝ := max R 0 with hR'
    have hR'0 : 0 ≤ R' := le_max_right _ _
    have hN1' : ∀ v : HeightOneSpectrum (𝓞 F), (1 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℕ) := fun v => by
      exact_mod_cast le_trans (by norm_num) (hN2 v)
    have hμ : ∀ v : HeightOneSpectrum (𝓞 F),
        0 < (pc_locHaar F v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
      intro v
      letI := pc_locBorel F v
      haveI := pc_locBorelSpace F v
      haveI := pc_isAddHaarMeasure_locHaar F v
      exact pc_measureReal_integers_pos F v (pc_locHaar F v)
    set c₀' : Fin n → HeightOneSpectrum (𝓞 F) → ℝ := fun j v =>
      ∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)), ‖A j v x‖ ∂(pc_locHaar F v) with hc₀'
    have hc₀'0 : ∀ j v, 0 ≤ c₀' j v := fun j v => integral_nonneg fun x => norm_nonneg _
    set bI : Fin n → HeightOneSpectrum (𝓞 F) → ℝ := fun j v =>
      ∫ x, ‖((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator
            ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (A j v)) x
            + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
                (fun y => LanglandsTunnell.TateLocal.charExt (χv v)⁻¹ y
                  * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * (1 : ℂ) + 1)) * B j v y⁻¹) x)
            * ψv v (-(0 * x))‖ ∂(pc_locHaar F v) with hbI
    have hbI0 : ∀ j v, 0 ≤ bI j v := fun j v => integral_nonneg fun x => norm_nonneg _
    set d : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
      (LanglandsTunnell.TateLocal.modulus ((ϖ v : v.adicCompletion F)⁻¹) : ℝ) ^ 3 with hd
    have hd1 : ∀ v, 1 ≤ d v := fun v => one_le_pow₀ (pc_one_le_modulus_inv_uniformizer v (ϖ v) (hϖ v))
    choose Ec κ hE0 hE using fun (j : Fin n) (v : HeightOneSpectrum (𝓞 F)) =>
      pc_exists_norm_corrOn_le (hN2 v) (nψ v) (cS v) mS (hμ v) (c₀' j v) (bI j v) (d v) R'
        (hc₀'0 j v) (hbI0 j v) (hd1 v) hR'0
    set k' : ℕ := ⌈2 * R'⌉₊ with hk'
    have hk'R : 2 * R' ≤ k' := Nat.le_ceil _
    set kk : ℕ := max (k' + 1) ((Finset.univ ×ˢ S).sup fun p : Fin n × HeightOneSpectrum (𝓞 F) => κ p.1 p.2)
      with hkk
    have hκle : ∀ j, ∀ v ∈ S, κ j v ≤ kk := by
      intro j v hv
      have h1 : (fun p : Fin n × HeightOneSpectrum (𝓞 F) => κ p.1 p.2) (j, v)
          ≤ (Finset.univ ×ˢ S).sup (fun p : Fin n × HeightOneSpectrum (𝓞 F) => κ p.1 p.2) :=
        Finset.le_sup (f := fun p : Fin n × HeightOneSpectrum (𝓞 F) => κ p.1 p.2)
          (Finset.mem_product.mpr ⟨Finset.mem_univ j, hv⟩)
      exact h1.trans (le_max_right _ _)
    set M : ℝ := 1 + ∑ j : Fin n, ∑ v ∈ S, Ec j v with hM
    have hM0 : 0 ≤ M := by
      have : 0 ≤ ∑ j : Fin n, ∑ v ∈ S, Ec j v :=
        Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun v _ => hE0 j v
      linarith
    have hEM : ∀ j, ∀ v ∈ S, Ec j v ≤ M := by
      intro j v hv
      have h1 : Ec j v ≤ ∑ v' ∈ S, Ec j v' := Finset.single_le_sum (fun v' _ => hE0 j v') hv
      have h2 : (∑ v' ∈ S, Ec j v') ≤ ∑ j' : Fin n, ∑ v' ∈ S, Ec j' v' :=
        Finset.single_le_sum (fun j' _ => Finset.sum_nonneg fun v' _ => hE0 j' v') (Finset.mem_univ j)
      linarith
    refine ⟨M, kk, hM0, fun j v w e s hs he => ?_⟩
    have hsR' : ‖s‖ ≤ R' := hs.trans (le_max_left _ _)
    obtain ⟨hw0, hwe⟩ := hexp_of_eq he
    have hpow1 : (1 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-e).toNat := one_le_pow₀ (hN1' v)
    by_cases hvS : v ∈ S
    · rw [ite_eq_left hvS]
      simp only [Φ, hvS, ↓reduceIte]
      letI := pc_locBorel F v
      haveI := pc_locBorelSpace F v
      haveI := pc_isAddHaarMeasure_locHaar F v
      have hc₀ := pc_norm_integral_integers_le v (A j v) (ψv v) (hψv1 v) w
      have hAint : IntegrableOn ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (A j v))
          (v.adicCompletionIntegers F : Set (v.adicCompletion F)) (pc_locHaar F v) :=
        pc_integrableOn_integers_of_depth_const (pc_locHaar F v) (hϖ v) mS
          (pc_indicator_depth_const hmS (hA j v hvS))
      have hs1 : ‖((χv v (ϖ v) : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * (1 : ℂ)))‖ < 1 := by
        simpa using pc_norm_mul_cpow_lt_one v ((χv v (ϖ v) : ℂˣ) : ℂ) (hχϖ v) 1 (by norm_num)
      have hint := LocalRam.integrable_twisted_smooth F v (pc_locHaar F v) (ϖ v) (hϖ v)
        (χv v) (cS v) (hcS v hvS) (hχc v hvS) mS hmS _ hAint (B j v) (hB j v hvS) 1 hs1 (ψv v) (nψ v) (hψv v) 0
      have hsh := fun (k : ℕ) (hk : 1 ≤ k) =>
        pc_norm_shell_le v (ϖ v) (hϖ v) (χv v) (A j v) (B j v) (ψv v) (hψv1 v) hint w k hk
      calc _ ≤ Ec j v * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(pc_exp w)).toNat) ^ κ j v :=
            hE j v (pc_exp w) _ _ s hc₀ hsh hsR'
        _ ≤ M * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-e).toNat) ^ kk := by
            rw [hwe]
            exact mul_le_mul (hEM j v hvS) (pow_le_pow_right₀ hpow1 (hκle j v hvS)) (by positivity) hM0
    · rw [ite_eq_right hvS, one_mul]
      simp only [Φ, hvS, ↓reduceIte]
      calc _ ≤ (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(pc_exp w)).toNat) ^ (k' + 1) :=
            pc_norm_corrOff_le (hχϖ v) (hN2 v) _ k' hk'R hsR'
        _ ≤ (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-e).toNat) ^ kk := by
            rw [hwe]
            exact pow_le_pow_right₀ hpow1 (le_max_left _ _)
  ·
    intro j v w₀ hw₀
    set e₀ : ℤ := pc_exp w₀ with he₀
    have hv0 : Valued.v w₀ = WithZero.exp e₀ := pc_valued_eq_exp hw₀
    set K : ℕ := (max ((mS : ℤ) - 1) (nψ v + (cS v : ℤ) - e₀)).toNat with hK
    refine ⟨min (e₀ - 1) (nψ v - K), fun w s hw => ?_⟩
    have hval : Valued.v w = Valued.v w₀ := by
      refine valued_eq_of_valued_sub_lt F v w w₀ (lt_of_le_of_lt hw ?_)
      rw [hv0, WithZero.exp_lt_exp]
      omega
    have hw0' : w ≠ 0 := by
      intro h0
      rw [h0, map_zero, hv0] at hval
      exact WithZero.zero_ne_coe hval
    have hexp : pc_exp w = e₀ := by
      have h2 := (pc_valued_eq_exp hw0').symm.trans (hval.trans hv0)
      exact WithZero.exp_injective h2
    have hwn : Valued.v (w - w₀) ≤ WithZero.exp (nψ v) :=
      hw.trans (by rw [WithZero.exp_le_exp]; omega)
    have hwk : ∀ k : ℕ, k ≤ K → Valued.v (w - w₀) ≤ WithZero.exp (nψ v - k) := fun k hk =>
      hw.trans (by rw [WithZero.exp_le_exp]; omega)
    by_cases hv : v ∈ S
    · simp only [Φ, hv, ↓reduceIte, hexp, ← he₀]
      letI := pc_locBorel F v
      haveI := pc_locBorelSpace F v
      unfold pc_corrOn
      split_ifs with hle
      · congr 1
        unfold pc_ram
        rw [setIntegral_integers_twist_eq_of_valued_sub_le F v (pc_locHaar F v) (ψv v) (nψ v) (hψv v)
          (A j v) w w₀ hwn]
        congr 1
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [Finset.mem_Icc] at hk
        beta_reduce
        rw [setIntegral_shell_twist_eq_of_valued_sub_le F v (pc_locHaar F v) (ψv v) (nψ v) (hψv v)
          (fun x => LanglandsTunnell.TateLocal.charExt (χv v)⁻¹ x * B j v x⁻¹) k w w₀ (hwk k hk.2)]
      · rfl
    · simp only [Φ, hv, ↓reduceIte, hexp, ← he₀]
  ·
    intro s hs ξ hξ y

    obtain ⟨Sy, hSy⟩ := hDall (diagOne y)
    obtain ⟨Dy⟩ := hSy Sy (Finset.Subset.refl Sy)
    have hint : Integrable (fun x => φ s (adelicWeyl (𝓞 F) F * unipotentGL2 x * diagOne y))
        (adelicAddHaar (𝓞 F) F) :=
      EisensteinGeneral.Piece.integrable_weyl_unipotent_mul_of_factorization F ψv nψ 1 Sy ϖ hϖ φ (diagOne y) Dy s hs
    have hunf := Unfolding.whittakerCoefficient_bruhatSeries_eq_of_isInducedSection hψ (hφ s) hξ (diagOne y) hint
    refine hunf.trans ?_

    set f : AdeleRing (𝓞 F) F → ℂ := fun z => φ s (adelicWeyl (𝓞 F) F * unipotentGL2 z * 1) with hf
    set ξ' : AdeleRing (𝓞 F) F := algebraMap F (AdeleRing (𝓞 F) F) ξ * (y : AdeleRing (𝓞 F) F) with hξ'
    have hαy : (((α y : ℝˣ) : ℝ) : ℂ) = (((distribHaarChar (AdeleRing (𝓞 F) F) y : ℝ≥0) : ℝ) : ℂ) := rfl
    have hdinv : (((distribHaarChar (AdeleRing (𝓞 F) F) y⁻¹ : ℝ≥0) : ℝ) : ℂ)⁻¹
        = (((distribHaarChar (AdeleRing (𝓞 F) F) y : ℝ≥0) : ℝ) : ℂ) := by
      have hm : distribHaarChar (AdeleRing (𝓞 F) F) y⁻¹ * distribHaarChar (AdeleRing (𝓞 F) F) y = 1 := by
        rw [← map_mul, inv_mul_cancel, map_one]
      have hm' : (((distribHaarChar (AdeleRing (𝓞 F) F) y⁻¹ : ℝ≥0) : ℝ) : ℂ)
          * (((distribHaarChar (AdeleRing (𝓞 F) F) y : ℝ≥0) : ℝ) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, ← NNReal.coe_mul, hm, NNReal.coe_one, Complex.ofReal_one]
      exact inv_eq_of_mul_eq_one_right hm'
    have hcv : (∫ x, φ s (adelicWeyl (𝓞 F) F * unipotentGL2 x * diagOne y)
          * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) ξ * x)) ∂(adelicAddHaar (𝓞 F) F))
        = ((cpowChar α hα (-(s + 1 / 2)) y : ℂˣ) : ℂ) * ((((α y : ℝˣ) : ℝ)) : ℂ)
          * ∫ z, f z * ψ (-(ξ' * z)) ∂(adelicAddHaar (𝓞 F) F) := by
      have h1 : ∀ x : AdeleRing (𝓞 F) F,
          φ s (adelicWeyl (𝓞 F) F * unipotentGL2 x * diagOne y) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) ξ * x))
            = ((cpowChar α hα (-(s + 1 / 2)) y : ℂˣ) : ℂ)
              * (f (y⁻¹ • (x + 0)) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) ξ * x))) := by
        intro x
        rw [apply_adelicWeyl_mul_unipotentGL2_mul_diagOne_of_isInducedSection F α hα s (hφ s) y x,
          add_zero, Units.smul_def, smul_eq_mul, mul_assoc]
      rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ h1), MeasureTheory.integral_const_mul,
        Piece.integral_smul_add_mul_addChar_neg_mul_eq F ψ f y⁻¹ 0 (algebraMap F (AdeleRing (𝓞 F) F) ξ),
        mul_zero, AddChar.map_zero_eq_one, mul_one, inv_inv, hdinv, ← hαy, mul_assoc]
    rw [hcv]

    have hΨ' : ∀ z : AdeleRing (𝓞 F) F, f z * ψ (-(ξ' * z))
        = ∑ j : Fin n, C j s * pc_tensor F (fun i => Wr j i s) (fun w => Wc j w s) (fun v => h j v s) (a • (z + u))
            * ψ (-(ξ' * z)) := by
      intro z
      simp only [hf, hfac s, Finset.sum_mul, pc_tensor]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have hsum : (∫ z, f z * ψ (-(ξ' * z)) ∂(adelicAddHaar (𝓞 F) F))
        = ∑ j : Fin n, ∫ z, C j s * pc_tensor F (fun i => Wr j i s) (fun w => Wc j w s) (fun v => h j v s)
            (a • (z + u)) * ψ (-(ξ' * z)) ∂(adelicAddHaar (𝓞 F) F) := by
      rw [← MeasureTheory.integral_finsetSum _ fun j _ => pc_term_integrable F ψ hψ (kdat j) (τr j) (abm j) (τc j)
        (habm j) (Wr j) (hWr j) (Wc j) (hWc j) S χv ϖ hϖ hχϖ hχS ψv nψ hψv cS hcS hχc mS hmS
        (A j) (B j) (hA j) (hB j) s hs (fun v => h j v s) (fun v hv x => hoff j v hv s x)
        (fun v hv x => hon j v hv s x) (C j s) a u ξ']
      exact MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ hΨ')

    set U : (AdeleRing (𝓞 F) F)ˣ :=
      Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom (Units.mk0 ξ hξ) * y * a⁻¹ with hUdef
    have hU : (U : AdeleRing (𝓞 F) F) = ξ' * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) := by
      simp only [hUdef, hξ', Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
        Units.val_mk0]
    have hU' : ξ' * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
        = algebraMap F (AdeleRing (𝓞 F) F) ξ * (y : AdeleRing (𝓞 F) F)
          * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) := rfl

    have hArchR : ∀ j : Fin n,
        (∏ i : {w : InfinitePlace F // w.IsReal}, ∫ x : ℝ, Wr j i s x
            * Complex.exp (-(((2 * Real.pi * (-(θr i * (InfiniteAdeleRing.ringEquiv_mixedSpace F
              (U : AdeleRing (𝓞 F) F).1).1 i)) * x : ℝ) : ℂ) * Complex.I)))
          = ∏ i : {w : InfinitePlace F // w.IsReal}, jR (kdat j i) (s + 1 / 2 + ((τr j i : ℝ) : ℂ) * Complex.I / 2)
              (-(θr i * (InfiniteAdeleRing.ringEquiv_mixedSpace F (U : AdeleRing (𝓞 F) F).1).1 i)) := by
      intro j
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [jR, hWr]
    have hArchC : ∀ j : Fin n,
        (∏ w : {w : InfinitePlace F // w.IsComplex}, ∫ z : ℂ, Wc j w s z
            * Complex.exp (-(((4 * Real.pi * ((-(θc w * (InfiniteAdeleRing.ringEquiv_mixedSpace F
              (U : AdeleRing (𝓞 F) F).1).2 w)) * z).re : ℝ) : ℂ) * Complex.I)))
          = ∏ w : {w : InfinitePlace F // w.IsComplex}, jC (abm j w).1 (abm j w).2.1
              (2 * s + 1 + ((abm j w).2.2 : ℂ) / 2 + ((τc j w : ℝ) : ℂ) * Complex.I / 2)
              (-(θc w * (InfiniteAdeleRing.ringEquiv_mixedSpace F (U : AdeleRing (𝓞 F) F).1).2 w)) := by
      intro j
      refine Finset.prod_congr rfl fun w _ => ?_
      simp only [jC, hWc]

    have hEp : (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, pc_euler S χv ϖ v.1 s)
        = ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
            (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))) :=
      tprod_congr fun v => by simp only [pc_euler, v.2, ↓reduceIte, hχv1, Units.val_one, one_mul]

    have hFin : ∀ j : Fin n,
        ∏ v ∈ S ∪ (pc_unit_fin_exp_finite U).toFinset, pc_corr F S χv ϖ ψv nψ cS mS (A j) (B j)
            (U : AdeleRing (𝓞 F) F).2 v s
          = ∏ᶠ v : HeightOneSpectrum (𝓞 F), Φ j v ((U : AdeleRing (𝓞 F) F).2 v) s := by
      intro j
      rw [finprod_eq_prod_of_mulSupport_subset _ (s := S ∪ (pc_unit_fin_exp_finite U).toFinset) ?_]
      · exact Finset.prod_congr rfl fun v _ => hΦcorr j v _ s
      · intro v hv
        rw [Function.mem_mulSupport] at hv
        rw [Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_coe, Set.Finite.mem_toFinset,
          Set.mem_ofPred_eq]
        by_contra hc
        push Not at hc
        exact hv ((hΦcorr j v _ s).symm.trans (pc_corr_eq_one F S χv ϖ ψv nψ cS mS (A j) (B j) _ v hc.1 hc.2 s))

    rw [hsum, ENNReal.toReal_inv, Complex.real_smul, Complex.ofReal_inv, mul_left_comm, Finset.mul_sum,
      Finset.sum_congr rfl fun j _ => pc_term_value F ψ ψv hψfin θr θc hψarch S χv ϖ hϖ hχϖ hχS nψ hψv hψv'
        hnψ cS hcS hχc mS hmS (A j) (B j) (hA j) (hB j) s hs (fun v => h j v s) (fun v hv x => hoff j v hv s x)
        (fun v hv x => hon j v hv s x) (fun i => Wr j i s) (fun w => Wc j w s) (C j s) a u ξ' U hU]
    simp only [hArchR, hArchC, hFin, hEp]
    rw [← cpowChar_neg_add_half_mul_self F α hα s y, Finset.mul_sum, Finset.mul_sum, hU]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

end AutomorphicForm
