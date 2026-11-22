/-
  The Haar measure of the adèlic Borel subgroup, disintegrated.

  Every locally finite, open-positive, left-invariant measure `μB` on the Borel subgroup of `GL₂(𝔸_K)`
  is, up to a single constant `c ∈ (0, ∞)`, the product of the additive Haar measure on the unipotent
  radical, two copies of the idèle Haar measure, and the `‖t‖⁻¹` density:

  `∫⁻ b, F b ∂μB = c · ∫⁻ x ∫⁻ u ∫⁻ t, F (n(x) · z(u) · diag(t)) · ‖t‖⁻¹`.

  This is the measure-theoretic form of the Iwasawa/Bruhat decomposition of the Borel — the identity that
  turns an integral over `B(𝔸_K)` into iterated integrals over `𝔸_K`, the idèles, and the idèles again.
  It is the standard first step of the unfolding arguments (the cuspidal unfolding, the Rankin–Selberg
  integral, the constant term) and it is the row SET-AF39 deferred because the port lacked the idèle
  measure `NumberField.Idele.idelicHaar` (now ported in the definition layer of SET-AF40).

  Transcribed whole from the pin's proof file
  `P2M/Sol/S_AutomorphicForm_exists_lintegral_adelicBorel_eq_mul_lintegral_coord_of_isMulLeftInvariant.lean`
  (pinned `aa2d8b3`, 429 lines / 36 declarations) and its statement from the wrapper
  `Theorems/Thm_AutomorphicForm_exists_lintegral_adelicBorel_eq_mul_lintegral_coord_of_isMulLeftInvariant.lean`.

  ## The `GL₂(𝔸_K)` companion (SET-AF100F)

  `AutomorphicForm.IwasawaCoord.exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa'` is the same
  disintegration one level up, on the whole of `GL₂(𝔸_K)` against the Iwasawa coordinates
  `n(x) · z(u) · diag(t) · k`: the module's own Borel row supplies the Borel half, a
  compactly-supported-left-invariant-functional uniqueness step
  (`Measure.exists_eq_smul_map_smul_of_forall_map_smul_eq_of_isCompact_stabilizer`, on the
  pretransitive action of `B(𝔸_K) × K_max` with compact stabilizer) supplies the constant, and the
  headline `NumberField.AdelicHaar.exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa`
  (`Theorems/Thm_…:19`, the statement authority) is its `IwasawaCoord` call.

  Transcribed from `P2M/Sol/S_NumberField_AdelicHaar_exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa.lean`
  (`:32`–`:232`): the 14 public engine declarations plus the headline, at the pin's names and
  visibility, in the pin's `AutomorphicForm.IwasawaCoord` subject namespace. The pin's three
  *anonymous* `scoped instance`s (`:36`, `:163`, `:173`) are transcribed as the pin states them
  (the checker skips them); its named `scoped instance`s (`action` `:56`, `continuousSMul` `:71`,
  `isPretransitive` `:84`, `compactSpace_BK` `:92`, `sigmaFinite_*`, …) are the pin's too and stay
  `scoped`. Two imports carry the pin's `Theorems/` premises: `MeasureTheory/HaarAveraging.lean`
  (the stabilizer uniqueness) and `NumberTheory/AdelicHaar/MulRightInvariant.lean`
  (`isMulRightInvariant_adelicGLHaar`, and with it mathlib's modular-character lemma that the pin's
  `isInvInvariant_of_compactSpace` uses — `Mathlib.MeasureTheory.Group.ModularCharacter` is not
  re-exported by `Haar.Unique`).

  `check_port --force`: **16 ok / 0 mismatch / 0 missing / 0 own** (the two Borel rows + the 14
  `IwasawaCoord` engine rows + the `Iwasawa` headline). Engine diff against the pin's two files:
  14 `S_` engine rows byte-identical by statement hash, the `S_` `solution` row is the same theorem
  as the wrapper row spelled with every name qualified (the wrapper, `:19`, is the authority and is
  what the port headline matches); no port declaration claims a hash that is in neither pin.

  ## Dedup (gate 5)

  `dedup.py --within --module BorelHaarDisintegration` reports 4 intra-module clusters, and all
  four are the **pins' own pairs** (the two pins this module transcribes each carry all four), so
  no copy is deleted:

  * shape: `IwasawaCoord.exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa'` (the pin's engine,
    `S_…iwasawa.lean:175`) against the headline
    `NumberField.AdelicHaar.exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa` (`:241`, and the
    `Theorems/` wrapper) — FR-0221 keeps the `main`/`solution` pair as two declarations;
  * name: `BorelCoord.isClosed_adelicBorel` (private, Borel pin `:221`) against
    `IwasawaCoord.isClosed_adelicBorel` (Iwasawa pin `:45`);
  * name: `BorelCoord.secondCountableTopology_borel` (`:218`) against its `IwasawaCoord` twin
    (`:39`);
  * body: `BorelCoord.locallyCompactSpace_borel` (`:228`) against its `IwasawaCoord` twin (`:52`).

  The last three are the same three instances/lemmas stated twice by the two pins, each in its own
  subject namespace; `check_port` matches each row through its own pin.

  ## move_dead (gate 6)

  `move_dead.py --dry-run --source …/BorelHaarDisintegration.lean --target …/tmp/af100/shelf-F.lean`
  → **14 declarations, 225 lines** — the documented escape clause, and **pre-existing** (at HEAD it
  is 15 / 229, the one difference being `isClosed_adelicBorel`, which the new `IwasawaCoord`
  `locallyCompactSpace_borel` now references). These are the pin's own `private` helpers of the
  Borel engine (`theta`, `psiHomeo`, `lmul`, `psi_mul`, `map_lmul_rho`, `continuous_lmul`, …): the
  only declarations that reference them are the module's `scoped instance`s
  (`isMulLeftInvariant_kappa`, `isFiniteMeasureOnCompacts_kappa`), which `move_dead`'s scanner does
  not model as declarations, so they read as unreachable. Nothing is moved or deleted.

  ## Heartbeat probe pair (recorded, never installed — FR-0225)

  `lake env lean -DautoImplicit=false -DmaxHeartbeats=N FLTForHuman/AutomorphicForm/Adelic/BorelHaarDisintegration.lean`
  is **silent at N = 12 000** and **fails at N = 10 000**, at a `(deterministic) timeout at
  isDefEq` raised inside `exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa'` (the `calc` step
  that reads `hc₂`); at N = 8 000 the same engine row times out a step earlier and at 6 000 the
  failure is a `whnf` timeout in the same proof. No `set_option maxHeartbeats` is in this module.

  spec-pin: Theorems/Thm_AutomorphicForm_exists_lintegral_adelicBorel_eq_mul_lintegral_coord_of_isMulLeftInvariant.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_exists_lintegral_adelicBorel_eq_mul_lintegral_coord_of_isMulLeftInvariant.lean
  spec-pin: Theorems/Thm_NumberField_AdelicHaar_exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa.lean
  spec-pin: P2M/Sol/S_NumberField_AdelicHaar_exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.BorelSubgroup
import FLTForHuman.AutomorphicForm.Adelic.AdelicMaximalCompact
import FLTForHuman.AutomorphicForm.Adelic.AdelicIwasawa
import FLTForHuman.NumberTheory.NumberField.IdeleProductMeasure
import FLTForHuman.NumberTheory.AdelicHaar.GeneralLinear
import FLTForHuman.NumberTheory.NumberField.TateGlobal.Defs
-- Three imports beyond the scaffold, each carrying one of the pin's own `Theorems/` imports:
-- `TateGlobalContinuousIdeleNorm` = the pin's `Thm_NumberField_TateGlobal_continuous_ideleNorm`
-- (pin `:189`), `AdelicLevel.Countability` = the pin's second-countability theorems (pin `:209`,
-- `:215`), `AdelicHaar.ProductFormula` = the port's `regular_adelicAddHaar` for the pin's
-- `unfold adelicAddHaar Measure.addHaar; infer_instance` (pin `:252`).
import FLTForHuman.NumberTheory.NumberField.TateGlobalContinuousIdeleNorm
import FLTForHuman.NumberTheory.AdelicLevel.Countability
import FLTForHuman.NumberTheory.AdelicHaar.ProductFormula
-- The pin's `Theorems/Thm_MeasureTheory_Measure_exists_eq_smul_map_smul_of_forall_map_smul_eq_of_isCompact_stabilizer`
-- import (`S_…iwasawa.lean:6`): the Haar-uniqueness engine the Iwasawa row opens with. The port's
-- home is `MeasureTheory/HaarAveraging.lean` (no module of this file's closure reaches it, and it
-- imports none of this file's closure, so there is no cycle).
import FLTForHuman.MeasureTheory.HaarAveraging
-- The pin's `Theorems/Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar` import
-- (`S_…iwasawa.lean:9`): the port's home of `isMulRightInvariant_adelicGLHaar`, and (through its
-- own `Mathlib.MeasureTheory.Group.ModularCharacter` import) of the modular-character lemma the
-- pin's `isInvInvariant_of_compactSpace` uses.
import FLTForHuman.NumberTheory.AdelicHaar.MulRightInvariant

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain
open AutomorphicForm
open scoped ENNReal NNReal

noncomputable section

namespace AutomorphicForm

-- The pin's local instance wall (its `S_` file sets the same six).
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

namespace BorelCoord

variable (K : Type) [Field K] [NumberField K]

-- The pin's `haveI : <class> := …` are the port's named `have`: mathlib `v4.34.0`'s
-- `linter.style.haveILetI` warns on them (the goal is a proposition), and the module builds
-- warning-free. `have` registers the local instance just the same (playbook, `AdelicModulus.lean`).

/-! ### Block 1 — the Borel coordinate maps -/

-- pin `:32` `continuous_unipotentGL2` is the port's `AutomorphicForm.continuous_unipotentGL2`
-- (`ConstantTerm.lean`), stated for a general topological ring: it is reused, not restated.

-- pin `:44`
private theorem continuous_centralScalar :
    Continuous (centralScalar (𝓞 K) K : (AdeleRing (𝓞 K) K)ˣ → AdelicGL2 (𝓞 K) K) := by
  have hval : Continuous fun u : (AdeleRing (𝓞 K) K)ˣ =>
      ((centralScalar (𝓞 K) K u : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) := by
    change Continuous fun u : (AdeleRing (𝓞 K) K)ˣ =>
      Matrix.scalar (Fin 2) (u : AdeleRing (𝓞 K) K)
    simp_rw [Matrix.scalar_apply]
    exact (continuous_pi fun _ => Units.continuous_val).matrix_diagonal
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  simp_rw [← map_inv]
  exact hval.comp continuous_inv

-- pin `:55`
private theorem continuous_diagOne :
    Continuous (diagOne : (AdeleRing (𝓞 K) K)ˣ → AdelicGL2 (𝓞 K) K) := by
  have hval : Continuous fun u : (AdeleRing (𝓞 K) K)ˣ =>
      ((diagOne u : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) := by
    change Continuous fun u : (AdeleRing (𝓞 K) K)ˣ =>
      Matrix.diagonal ![(u : AdeleRing (𝓞 K) K), 1]
    refine (continuous_pi fun i => ?_).matrix_diagonal
    fin_cases i
    · exact Units.continuous_val
    · exact continuous_const
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  simp_rw [← map_inv]
  exact hval.comp continuous_inv

-- pin `:68`
private def psiG (p : AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ) :
    AdelicGL2 (𝓞 K) K :=
  unipotentGL2 p.1 * centralScalar (𝓞 K) K p.2.1 * diagOne p.2.2

-- pin `:71`
private theorem psiG_apply (p : AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ)
    (i j : Fin 2) :
    ((psiG K p : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j =
      !![(p.2.1 : AdeleRing (𝓞 K) K) * p.2.2, p.1 * p.2.1; 0,
        (p.2.1 : AdeleRing (𝓞 K) K)] i j := by
  rw [psiG, Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, unipotentGL2_coe]
  change (!![1, p.1; 0, 1] * Matrix.scalar (Fin 2) (p.2.1 : AdeleRing (𝓞 K) K) *
    Matrix.diagonal ![(p.2.2 : AdeleRing (𝓞 K) K), 1]) i j = _
  rw [Matrix.scalar_apply, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.diagonal_apply, Matrix.diagonal_apply]
  fin_cases i <;> fin_cases j <;> simp [mul_comm]

-- pin `:81`
private theorem psiG_mem (p : AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ) :
    psiG K p ∈ adelicBorel (𝓞 K) K := by
  rw [mem_borelSubgroup_iff, psiG_apply]; rfl

-- pin `:85`
private theorem continuous_psiG : Continuous (psiG K) :=
  (((continuous_unipotentGL2 (R := AdeleRing (𝓞 K) K)).comp continuous_fst).mul
    ((continuous_centralScalar K).comp (continuous_fst.comp continuous_snd))).mul
    ((continuous_diagOne K).comp (continuous_snd.comp continuous_snd))

-- pin `:90`
private def psi (p : AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ) :
    adelicBorel (𝓞 K) K :=
  ⟨psiG K p, psiG_mem K p⟩

-- pin `:93`
private theorem continuous_psi : Continuous (psi K) := (continuous_psiG K).subtype_mk _

-- pin `:95`
private def theta (b : adelicBorel (𝓞 K) K) :
    AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ :=
  (((b : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1 *
      ((borelDiagSnd b)⁻¹ : (AdeleRing (𝓞 K) K)ˣ),
    borelDiagSnd b, borelDiagFst b * (borelDiagSnd b)⁻¹)

-- pin `:99`
private theorem continuous_borelDiagSnd :
    Continuous (borelDiagSnd : adelicBorel (𝓞 K) K → (AdeleRing (𝓞 K) K)ˣ) := by
  have hent : ∀ i j : Fin 2, Continuous fun b : adelicBorel (𝓞 K) K =>
      (((b : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j) := fun i j =>
    ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).matrix_elem i j).comp
      continuous_subtype_val
  refine Units.continuous_iff.mpr ⟨hent 1 1, ?_⟩
  simp_rw [← map_inv]
  exact (hent 1 1).comp continuous_inv

-- pin `:107`
private theorem continuous_borelDiagFst :
    Continuous (borelDiagFst : adelicBorel (𝓞 K) K → (AdeleRing (𝓞 K) K)ˣ) := by
  have hent : ∀ i j : Fin 2, Continuous fun b : adelicBorel (𝓞 K) K =>
      (((b : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j) := fun i j =>
    ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).matrix_elem i j).comp
      continuous_subtype_val
  refine Units.continuous_iff.mpr ⟨hent 0 0, ?_⟩
  simp_rw [← map_inv]
  exact (hent 0 0).comp continuous_inv

-- pin `:115`
private theorem continuous_theta : Continuous (theta K) := by
  have h01 : Continuous fun b : adelicBorel (𝓞 K) K =>
      (((b : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1) :=
    ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).matrix_elem 0 1).comp
      continuous_subtype_val
  refine (h01.mul (Units.continuous_val.comp ((continuous_borelDiagSnd K).inv))).prodMk
    ((continuous_borelDiagSnd K).prodMk ((continuous_borelDiagFst K).mul (continuous_borelDiagSnd K).inv))

-- pin `:122`
private theorem theta_psi (p : AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ) :
    theta K (psi K p) = p := by
  obtain ⟨x, u, t⟩ := p
  have hsnd : borelDiagSnd (psi K (x, u, t)) = u := Units.ext (by
    change ((psiG K (x, u, t) : AdelicGL2 (𝓞 K) K) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1 = (u : AdeleRing (𝓞 K) K)
    rw [psiG_apply]; rfl)
  have hfst : borelDiagFst (psi K (x, u, t)) = u * t := Units.ext (by
    change ((psiG K (x, u, t) : AdelicGL2 (𝓞 K) K) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0 = (u : AdeleRing (𝓞 K) K) * t
    rw [psiG_apply]; rfl)
  simp only [theta, hsnd, hfst]
  refine Prod.ext ?_ (Prod.ext rfl ?_)
  · change ((psiG K (x, u, t) : AdelicGL2 (𝓞 K) K) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1 * _ = x
    rw [psiG_apply]
    change x * (u : AdeleRing (𝓞 K) K) * ((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) = x
    rw [mul_assoc, Units.mul_inv, mul_one]
  · change u * t * u⁻¹ = t
    rw [mul_comm u t, mul_inv_cancel_right]

-- pin `:140`
private theorem psi_theta (b : adelicBorel (𝓞 K) K) : psi K (theta K b) = b := by
  have h10 : (((b : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0 := b.2
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  change ((psiG K (theta K b) : AdelicGL2 (𝓞 K) K) :
    Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j = _
  rw [psiG_apply]
  set M := (((b : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) with hM
  have hu : ((borelDiagSnd b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) = M 1 1 := rfl
  have ht : ((borelDiagFst b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) = M 0 0 := rfl
  have hinv : M 1 1 * (((borelDiagSnd b)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) = 1 := by
    rw [← hu, Units.mul_inv]
  have e00 : ((borelDiagSnd b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) *
      ((borelDiagFst b * (borelDiagSnd b)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) :
        AdeleRing (𝓞 K) K) = M 0 0 := by
    rw [Units.val_mul, hu, ht, mul_left_comm, hinv, mul_one]
  have e01 : M 0 1 * (((borelDiagSnd b)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) *
      ((borelDiagSnd b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) = M 0 1 := by
    rw [mul_assoc, Units.inv_mul, mul_one]
  simp only [theta]
  fin_cases i <;> fin_cases j
  · exact e00
  · exact e01
  · exact h10.symm
  · exact hu

-- pin `:162`
private def psiHomeo :
    (AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ) ≃ₜ adelicBorel (𝓞 K) K where
  toFun := psi K
  invFun := theta K
  left_inv := theta_psi K
  right_inv := psi_theta K
  continuous_toFun := continuous_psi K
  continuous_invFun := continuous_theta K

-- pin `:170`
private def lmul (p q : AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ) :
    AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ :=
  (p.1 + (p.2.2 : AdeleRing (𝓞 K) K) * q.1, p.2.1 * q.2.1, p.2.2 * q.2.2)

-- pin `:174`
private theorem psi_mul (p q : AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ) :
    psi K p * psi K q = psi K (lmul K p q) := by
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  change (((psiG K p : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) *
      ((psiG K q : AdelicGL2 (𝓞 K) K) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))) i j =
    ((psiG K (lmul K p q) : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j
  rw [Matrix.mul_apply, Fin.sum_univ_two, psiG_apply, psiG_apply, psiG_apply, psiG_apply, psiG_apply]
  simp only [lmul, Units.val_mul]
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-! ### Block 2 — the densities and the measures -/

-- pin `:184`
private def dens (t : (AdeleRing (𝓞 K) K)ˣ) : ℝ≥0∞ :=
  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)

-- pin `:186`
private theorem continuous_dens : Continuous (dens K) := by
  unfold dens
  refine ENNReal.continuous_ofReal.comp ?_
  exact (NumberField.TateGlobal.continuous_ideleNorm K).inv₀ fun t =>
    (NumberField.TateGlobal.ideleNorm_pos t).ne'

-- pin `:191`
private theorem measurable_dens : Measurable (dens K) := (continuous_dens K).measurable

-- pin `:193`
private theorem dens_pos (t : (AdeleRing (𝓞 K) K)ˣ) : 0 < dens K t :=
  ENNReal.ofReal_pos.mpr (inv_pos.mpr (NumberField.TateGlobal.ideleNorm_pos t))

-- pin `:196`
private theorem dens_mul (t₀ t : (AdeleRing (𝓞 K) K)ˣ) :
    dens K (t₀⁻¹ * t) = (distribHaarChar (AdeleRing (𝓞 K) K) t₀ : ℝ≥0∞) * dens K t := by
  unfold dens NumberField.TateGlobal.ideleNorm
  rw [map_mul, map_inv, NNReal.coe_mul, mul_inv, NNReal.coe_inv, inv_inv,
    ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]

-- pin `:202`
private def idelicHaarW : Measure (AdeleRing (𝓞 K) K)ˣ :=
  (NumberField.Idele.idelicHaar K).withDensity (dens K)

-- pin `:204`
private def rho : Measure (AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ) :=
  (adelicAddHaar (𝓞 K) K).prod ((NumberField.Idele.idelicHaar K).prod (idelicHaarW K))

-- pin `:207`
private def kappa : Measure (adelicBorel (𝓞 K) K) := (rho K).map (psi K)

-- pin `:209`
scoped instance : SecondCountableTopology (AdeleRing (𝓞 K) K) :=
  NumberField.AdeleRing.secondCountableTopology K

-- pin `:211`
scoped instance secondCountableTopology_idele : SecondCountableTopology (AdeleRing (𝓞 K) K)ˣ := by
  have hop : SecondCountableTopology (AdeleRing (𝓞 K) K)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

-- pin `:215`
scoped instance : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
  NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K

-- pin `:218`
scoped instance secondCountableTopology_borel : SecondCountableTopology (adelicBorel (𝓞 K) K) :=
  TopologicalSpace.Subtype.secondCountableTopology _

-- pin `:221`
private theorem isClosed_adelicBorel : IsClosed (adelicBorel (𝓞 K) K : Set (AdelicGL2 (𝓞 K) K)) := by
  have : (adelicBorel (𝓞 K) K : Set (AdelicGL2 (𝓞 K) K)) =
      (fun g : AdelicGL2 (𝓞 K) K => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0) ⁻¹' {0} := by
    -- Adapted (pin `:224`): the port's `mem_borelSubgroup_iff` has `A` as an explicit binder,
    -- so the pin's `mem_borelSubgroup_iff _` is spelled `(A := …)` here.
    ext g; exact mem_borelSubgroup_iff (A := AdeleRing (𝓞 K) K)
  rw [this]
  exact isClosed_singleton.preimage
    ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).matrix_elem 1 0)

-- pin `:228`
scoped instance locallyCompactSpace_borel : LocallyCompactSpace (adelicBorel (𝓞 K) K) :=
  (isClosed_adelicBorel K).locallyCompactSpace

-- pin `:230`
scoped instance sigmaFinite_adelicAddHaar : SigmaFinite (adelicAddHaar (𝓞 K) K) := by
  have hhaar := isAddHaarMeasure_adelicAddHaar (𝓞 K) K
  infer_instance

-- pin `:234`
scoped instance locallyCompactSpace_idele : LocallyCompactSpace (AdeleRing (𝓞 K) K)ˣ :=
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace

-- pin `:237`
scoped instance sigmaCompactSpace_idele : SigmaCompactSpace (AdeleRing (𝓞 K) K)ˣ :=
  @sigmaCompactSpace_of_locallyCompact_secondCountable _ _ (locallyCompactSpace_idele K)
    (secondCountableTopology_idele K)

-- pin `:240`
scoped instance sigmaFinite_idelicHaar : SigmaFinite (NumberField.Idele.idelicHaar K) := by
  have hhaar := NumberField.Idele.isHaarMeasure_idelicHaar K
  infer_instance

-- pin `:244`
scoped instance sFinite_idelicHaarW : SFinite (idelicHaarW K) := by
  unfold idelicHaarW; infer_instance

-- pin `:246`
scoped instance sFinite_rho : SFinite (rho K) := by unfold rho; infer_instance

/-! ### Block 3 — the invariance laws -/

-- pin `:248` (the pin's `unfold adelicAddHaar Measure.addHaar; infer_instance` for `Regular` is the
-- port's `regular_adelicAddHaar`)
private theorem map_mul_left_adelicAddHaar (x₀ : AdeleRing (𝓞 K) K)
    (t₀ : (AdeleRing (𝓞 K) K)ˣ) :
    (adelicAddHaar (𝓞 K) K).map (fun x => x₀ + (t₀ : AdeleRing (𝓞 K) K) * x) =
      (((distribHaarChar (AdeleRing (𝓞 K) K) t₀)⁻¹ : ℝ≥0) : ℝ≥0∞) • adelicAddHaar (𝓞 K) K := by
  have hadd := isAddHaarMeasure_adelicAddHaar (𝓞 K) K
  have hreg : (adelicAddHaar (𝓞 K) K).Regular := NumberField.AdelicHaar.regular_adelicAddHaar K
  have h1 : (adelicAddHaar (𝓞 K) K).map (fun x => (t₀ : AdeleRing (𝓞 K) K) * x) =
      (((distribHaarChar (AdeleRing (𝓞 K) K) t₀)⁻¹ : ℝ≥0) : ℝ≥0∞) • adelicAddHaar (𝓞 K) K := by
    refine Measure.ext fun s hs => ?_
    open scoped Pointwise in
    rw [Measure.map_apply (measurable_const_mul _) hs, Measure.smul_apply, smul_eq_mul,
      show (fun y => (t₀ : AdeleRing (𝓞 K) K) * y) ⁻¹' s = t₀⁻¹ • s from Set.preimage_smul t₀ s,
      ← distribHaarChar_mul (adelicAddHaar (𝓞 K) K) t₀⁻¹ s, map_inv]
  have hcomp : (fun x => x₀ + (t₀ : AdeleRing (𝓞 K) K) * x) =
      (fun x => x₀ + x) ∘ (fun x => (t₀ : AdeleRing (𝓞 K) K) * x) := rfl
  -- Adapted (pin `:264`): mathlib `v4.34.0`'s `Measure.map_smul` takes its `AEMeasurable`
  -- argument explicitly (`map_smul (c) {μ} {f} (hf)`), where `v4.33.0`'s was bare.
  rw [hcomp, ← Measure.map_map (measurable_const_add x₀) (measurable_const_mul _), h1,
    Measure.map_smul _ (measurable_const_add x₀).aemeasurable, map_add_left_eq_self]

-- pin `:266`
private theorem map_mul_left_idelicHaarW (t₀ : (AdeleRing (𝓞 K) K)ˣ) :
    (idelicHaarW K).map (fun t => t₀ * t) =
      (distribHaarChar (AdeleRing (𝓞 K) K) t₀ : ℝ≥0∞) • idelicHaarW K := by
  have hhaar := NumberField.Idele.isHaarMeasure_idelicHaar K
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply (measurable_const_mul _) hs, Measure.smul_apply, smul_eq_mul, idelicHaarW,
    withDensity_apply _ (measurable_const_mul _ hs), withDensity_apply _ hs]
  have h := lintegral_mul_left_eq_self (μ := NumberField.Idele.idelicHaar K)
    (fun t => s.indicator (dens K ∘ fun t => t₀⁻¹ * t) t) t₀
  have hind : ∀ t, s.indicator (dens K ∘ fun t => t₀⁻¹ * t) (t₀ * t) =
      ((fun t => t₀ * t) ⁻¹' s).indicator (dens K) t := by
    intro t
    simp only [Set.indicator, Set.mem_preimage, Function.comp_apply, inv_mul_cancel_left]
    rfl
  simp_rw [hind] at h
  rw [← lintegral_indicator (measurable_const_mul _ hs), h, ← lintegral_indicator hs]
  have hdens : ∀ t, s.indicator (dens K ∘ fun t => t₀⁻¹ * t) t =
      (distribHaarChar (AdeleRing (𝓞 K) K) t₀ : ℝ≥0∞) * s.indicator (dens K) t := by
    intro t
    simp only [Set.indicator, Function.comp_apply, dens_mul]
    split_ifs <;> simp
  simp_rw [hdens]
  rw [lintegral_const_mul _ ((measurable_dens K).indicator hs)]

-- pin `:290`
private theorem map_lmul_rho
    (p : AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ) :
    (rho K).map (lmul K p) = rho K := by
  have hhaar := NumberField.Idele.isHaarMeasure_idelicHaar K
  obtain ⟨x₀, u₀, t₀⟩ := p
  have hl : lmul K (x₀, u₀, t₀) = Prod.map (fun x => x₀ + (t₀ : AdeleRing (𝓞 K) K) * x)
      (Prod.map (fun u => u₀ * u) (fun t => t₀ * t)) := rfl
  have hmx : Measurable (fun x : AdeleRing (𝓞 K) K => x₀ + (t₀ : AdeleRing (𝓞 K) K) * x) :=
    (measurable_const_add x₀).comp (measurable_const_mul _)
  have hmu : Measurable (fun u : (AdeleRing (𝓞 K) K)ˣ => u₀ * u) := measurable_const_mul u₀
  have hmt : Measurable (fun t : (AdeleRing (𝓞 K) K)ˣ => t₀ * t) := measurable_const_mul t₀
  rw [hl, rho, ← Measure.map_prod_map _ _ hmx (hmu.prodMap hmt), ← Measure.map_prod_map _ _ hmu hmt,
    map_mul_left_adelicAddHaar, map_mul_left_eq_self, map_mul_left_idelicHaarW,
    Measure.prod_smul_right, Measure.prod_smul_right, Measure.prod_smul_left, smul_smul,
    ← ENNReal.coe_mul, mul_inv_cancel₀ (distribHaarChar_pos (g := t₀)).ne', ENNReal.coe_one,
    one_smul]

-- pin `:304`
private theorem continuous_lmul
    (p : AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ) :
    Continuous (lmul K p) := by
  unfold lmul
  exact (continuous_const.add (continuous_const.mul continuous_fst)).prodMk
    ((continuous_const.mul (continuous_fst.comp continuous_snd)).prodMk
      (continuous_const.mul (continuous_snd.comp continuous_snd)))

-- pin `:310`
scoped instance isMulLeftInvariant_kappa : (kappa K).IsMulLeftInvariant := by
  refine ⟨fun b₀ => ?_⟩
  obtain ⟨p₀, rfl⟩ : ∃ p₀, psi K p₀ = b₀ := ⟨theta K b₀, psi_theta K b₀⟩
  rw [kappa, Measure.map_map (measurable_const_mul _) (continuous_psi K).measurable]
  have hmul : (fun b => psi K p₀ * b) ∘ psi K = psi K ∘ lmul K p₀ :=
    funext fun q => psi_mul K p₀ q
  rw [hmul, ← Measure.map_map (continuous_psi K).measurable, map_lmul_rho]
  exact (continuous_lmul K p₀).measurable

-- pin `:318`
scoped instance isFiniteMeasureOnCompacts_idelicHaarW : IsFiniteMeasureOnCompacts (idelicHaarW K) := by
  have hhaar := NumberField.Idele.isHaarMeasure_idelicHaar K
  refine ⟨fun C hC => ?_⟩
  rw [idelicHaarW, withDensity_apply _ hC.measurableSet]
  rcases C.eq_empty_or_nonempty with h | h
  · simp [h]
  obtain ⟨t₁, _, ht₁⟩ := hC.exists_isMaxOn h (continuous_dens K).continuousOn
  calc ∫⁻ t in C, dens K t ∂(NumberField.Idele.idelicHaar K)
      ≤ ∫⁻ _ in C, dens K t₁ ∂(NumberField.Idele.idelicHaar K) :=
        setLIntegral_mono measurable_const fun t ht => ht₁ ht
    _ = dens K t₁ * (NumberField.Idele.idelicHaar K) C := setLIntegral_const C _
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC.measure_lt_top

-- pin `:330`
scoped instance isFiniteMeasureOnCompacts_rho : IsFiniteMeasureOnCompacts (rho K) := by
  have hadd := isAddHaarMeasure_adelicAddHaar (𝓞 K) K
  have hhaar := NumberField.Idele.isHaarMeasure_idelicHaar K
  unfold rho; infer_instance

-- pin `:335`
scoped instance isFiniteMeasureOnCompacts_kappa : IsFiniteMeasureOnCompacts (kappa K) := by
  refine ⟨fun C hC => ?_⟩
  rw [kappa, Measure.map_apply (continuous_psi K).measurable hC.measurableSet]
  exact ((psiHomeo K).isCompact_preimage.mpr hC).measure_lt_top

/-! ### Block 4 — the assembly -/

-- pin `:340`
private theorem idelicHaarW_univ_ne_zero : idelicHaarW K Set.univ ≠ 0 := by
  have hhaar := NumberField.Idele.isHaarMeasure_idelicHaar K
  rw [idelicHaarW, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  intro h
  rw [lintegral_eq_zero_iff (measurable_dens K)] at h
  have h2 : (NumberField.Idele.idelicHaar K) Set.univ = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    exact h.mono fun t ht htU => (dens_pos K t).ne' ht
  exact isOpen_univ.measure_ne_zero (NumberField.Idele.idelicHaar K) Set.univ_nonempty h2

-- pin `:350`
private theorem kappa_univ_ne_zero : kappa K Set.univ ≠ 0 := by
  have hadd := isAddHaarMeasure_adelicAddHaar (𝓞 K) K
  have hhaar := NumberField.Idele.isHaarMeasure_idelicHaar K
  rw [kappa, Measure.map_apply (continuous_psi K).measurable MeasurableSet.univ, Set.preimage_univ, rho,
    ← Set.univ_prod_univ, Measure.prod_prod, ← Set.univ_prod_univ, Measure.prod_prod]
  refine mul_ne_zero (isOpen_univ.measure_ne_zero _ Set.univ_nonempty)
    (mul_ne_zero (isOpen_univ.measure_ne_zero _ Set.univ_nonempty) (idelicHaarW_univ_ne_zero K))

-- pin `:358`
private theorem exists_eq_mul_lintegral_kappa (μB : Measure (adelicBorel (𝓞 K) K))
    [μB.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μB] [μB.IsOpenPosMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ ∀ F : adelicBorel (𝓞 K) K → ℝ≥0∞,
      ∫⁻ b, F b ∂μB = c * ∫⁻ b, F b ∂(kappa K) := by
  have hμB : μB.IsHaarMeasure := ⟨⟩
  set c' := Measure.haarScalarFactor (kappa K) μB with hc'
  have hκ : kappa K = c' • μB := Measure.isMulLeftInvariant_eq_smul (kappa K) μB
  have hc0 : c' ≠ 0 := by
    intro h0
    apply kappa_univ_ne_zero K
    rw [hκ, h0, zero_smul, Measure.coe_zero, Pi.zero_apply]
  refine ⟨((c' : ℝ≥0∞))⁻¹, ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top,
    ENNReal.inv_ne_top.mpr (ENNReal.coe_ne_zero.mpr hc0), fun F => ?_⟩
  have h1 : ∫⁻ b, F b ∂(kappa K) = (c' : ℝ≥0∞) * ∫⁻ b, F b ∂μB := by
    rw [hκ, lintegral_smul_measure]
    rfl
  rw [h1, ← mul_assoc, ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.mpr hc0) ENNReal.coe_ne_top,
    one_mul]

end BorelCoord

open BorelCoord in
theorem exists_lintegral_adelicBorel_eq_mul_lintegral_coord_of_isMulLeftInvariant
    (K : Type) [Field K] [NumberField K]
    (μB : Measure (adelicBorel (𝓞 K) K)) [μB.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μB]
    [μB.IsOpenPosMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
      ∀ F : AdelicGL2 (𝓞 K) K → ℝ≥0∞, Measurable F →
        ∫⁻ b, F (b : AdelicGL2 (𝓞 K) K) ∂μB =
          c * ∫⁻ x, ∫⁻ u, ∫⁻ t,
                F (unipotentGL2 x * centralScalar (𝓞 K) K u * diagOne t) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
              ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(adelicAddHaar (𝓞 K) K) := by
  have hhaar := NumberField.Idele.isHaarMeasure_idelicHaar K
  obtain ⟨c, hc0, hctop, hc⟩ := exists_eq_mul_lintegral_kappa K μB
  refine ⟨c, hc0, hctop, fun F hF => ?_⟩
  rw [hc (fun b => F b)]
  congr 1
  set Φ : AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞ :=
    fun p => F (psiG K p) with hΦ_def
  have hΦ : Measurable Φ := hF.comp (continuous_psiG K).measurable
  have hFb : Measurable fun b : adelicBorel (𝓞 K) K => F (b : AdelicGL2 (𝓞 K) K) :=
    hF.comp measurable_subtype_coe
  rw [kappa, lintegral_map hFb (continuous_psi K).measurable]
  change ∫⁻ p, Φ p ∂(rho K) = _
  rw [rho, lintegral_prod _ hΦ.aemeasurable]
  refine lintegral_congr fun x => ?_
  have hΦx : Measurable fun q : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ => Φ (x, q) :=
    hΦ.comp measurable_prodMk_left
  rw [lintegral_prod _ hΦx.aemeasurable]
  refine lintegral_congr fun u => ?_
  have hΦxu : Measurable fun t : (AdeleRing (𝓞 K) K)ˣ => Φ (x, u, t) :=
    hΦx.comp measurable_prodMk_left
  rw [idelicHaarW, lintegral_withDensity_eq_lintegral_mul _ (measurable_dens K) hΦxu]
  refine lintegral_congr fun t => ?_
  simp only [Pi.mul_apply, hΦ_def, dens, psiG, mul_comm]


namespace IwasawaCoord

/-! ### The Iwasawa coordinates and the disintegration on `GL₂(𝔸_K)`

  Transcribed from
  `P2M/Sol/S_NumberField_AdelicHaar_exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa.lean`
  (`:32`–`:232`). The pin's `variable (K : Type) [Field K] [NumberField K]` is kept as a
  `variable`, so the declarations are the pin's text. The three anonymous `scoped instance`s
  (`:36`, `:163`, `:173`) are transcribed as the pin states them; the named instances
  (`action`, `continuousSMul`, `isPretransitive`, `compactSpace_BK`, `sigmaFinite_*`, …) are the
  pin's too and stay `scoped`. -/

variable (K : Type) [Field K] [NumberField K]

-- pin `:36`
scoped instance : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
  NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K

-- pin `:39`
scoped instance secondCountableTopology_borel : SecondCountableTopology (adelicBorel (𝓞 K) K) :=
  TopologicalSpace.Subtype.secondCountableTopology _

-- pin `:42`
scoped instance secondCountableTopology_maxCpt : SecondCountableTopology (adelicMaximalCompact K) :=
  TopologicalSpace.Subtype.secondCountableTopology _

-- pin `:45`
theorem isClosed_adelicBorel : IsClosed (adelicBorel (𝓞 K) K : Set (AdelicGL2 (𝓞 K) K)) := by
  have hpre : (adelicBorel (𝓞 K) K : Set (AdelicGL2 (𝓞 K) K)) =
      (fun g : AdelicGL2 (𝓞 K) K => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0) ⁻¹' {0} := by
    ext g; exact mem_borelSubgroup_iff (A := AdeleRing (𝓞 K) K)
  rw [hpre]
  exact isClosed_singleton.preimage
    ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).matrix_elem 1 0)

-- pin `:52`
scoped instance locallyCompactSpace_borel : LocallyCompactSpace (adelicBorel (𝓞 K) K) :=
  (isClosed_adelicBorel K).locallyCompactSpace

-- pin `:54`
abbrev L := adelicBorel (𝓞 K) K × adelicMaximalCompact K

-- pin `:56`
scoped instance action : MulAction (L K) (AdelicGL2 (𝓞 K) K) where
  smul l g := (l.1 : AdelicGL2 (𝓞 K) K) * g * ((l.2 : adelicMaximalCompact K) : AdelicGL2 (𝓞 K) K)⁻¹
  one_smul g := by
    change ((1 : adelicBorel (𝓞 K) K) : AdelicGL2 (𝓞 K) K) * g * (((1 : adelicMaximalCompact K)) : AdelicGL2 (𝓞 K) K)⁻¹ = g
    simp
  mul_smul l l' g := by
    change ((l * l').1 : AdelicGL2 (𝓞 K) K) * g * (((l * l').2 : adelicMaximalCompact K) : AdelicGL2 (𝓞 K) K)⁻¹ =
      (l.1 : AdelicGL2 (𝓞 K) K) * ((l'.1 : AdelicGL2 (𝓞 K) K) * g * ((l'.2 : adelicMaximalCompact K) : AdelicGL2 (𝓞 K) K)⁻¹) *
        ((l.2 : adelicMaximalCompact K) : AdelicGL2 (𝓞 K) K)⁻¹
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, mul_inv_rev]
    group

-- pin `:68`
theorem smul_def (l : L K) (g : AdelicGL2 (𝓞 K) K) :
    l • g = (l.1 : AdelicGL2 (𝓞 K) K) * g * ((l.2 : adelicMaximalCompact K) : AdelicGL2 (𝓞 K) K)⁻¹ := rfl

-- pin `:71`
scoped instance continuousSMul : ContinuousSMul (L K) (AdelicGL2 (𝓞 K) K) := by
  refine ⟨?_⟩
  change Continuous fun p : L K × AdelicGL2 (𝓞 K) K =>
    (p.1.1 : AdelicGL2 (𝓞 K) K) * p.2 * ((p.1.2 : adelicMaximalCompact K) : AdelicGL2 (𝓞 K) K)⁻¹
  exact ((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).mul continuous_snd).mul
    (continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).inv

-- pin `:78`
theorem exists_smul_one_eq (g : AdelicGL2 (𝓞 K) K) : ∃ l : L K, l • (1 : AdelicGL2 (𝓞 K) K) = g := by
  obtain ⟨b, k, hb, hk1, hk2, rfl⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq K g
  refine ⟨(⟨b, hb⟩, ⟨k, mem_adelicMaximalCompact_iff.mpr ⟨hk1, hk2⟩⟩⁻¹), ?_⟩
  rw [smul_def]
  simp

-- pin `:84`
scoped instance isPretransitive : MulAction.IsPretransitive (L K) (AdelicGL2 (𝓞 K) K) := by
  refine ⟨fun g₁ g₂ => ?_⟩
  obtain ⟨l₁, h₁⟩ := exists_smul_one_eq K g₁
  obtain ⟨l₂, h₂⟩ := exists_smul_one_eq K g₂
  exact ⟨l₂ * l₁⁻¹, by rw [← h₁, ← h₂, mul_smul, inv_smul_smul]⟩

-- pin `:90`
abbrev BK := {k : adelicMaximalCompact K // (k : AdelicGL2 (𝓞 K) K) ∈ adelicBorel (𝓞 K) K}

-- pin `:92`
scoped instance compactSpace_BK : CompactSpace (BK K) := by
  refine isCompact_iff_compactSpace.mp ?_
  exact ((isClosed_adelicBorel K).preimage continuous_subtype_val).isCompact

-- pin `:96`
def toStab (k : BK K) : L K := (⟨(k.1 : AdelicGL2 (𝓞 K) K), k.2⟩, k.1)

-- pin `:98`
theorem continuous_toStab : Continuous (toStab K) :=
  ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).prodMk continuous_subtype_val

-- pin `:101`
theorem stabilizer_eq_range : (MulAction.stabilizer (L K) (1 : AdelicGL2 (𝓞 K) K) : Set (L K)) = Set.range (toStab K) := by
  ext l
  rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, smul_def, mul_one, mul_inv_eq_one]
  constructor
  · intro h
    refine ⟨⟨l.2, ?_⟩, ?_⟩
    · rw [← h]; exact l.1.2
    · refine Prod.ext (Subtype.ext ?_) rfl
      exact h.symm
  · rintro ⟨k, rfl⟩; rfl

-- pin `:112`
theorem isCompact_stabilizer : IsCompact (MulAction.stabilizer (L K) (1 : AdelicGL2 (𝓞 K) K) : Set (L K)) := by
  rw [stabilizer_eq_range]; exact isCompact_range (continuous_toStab K)

-- pin `:115`
theorem map_smul_adelicGLHaar (l : L K) :
    (adelicGLHaar (Fin 2) (𝓞 K) K).map (fun g : AdelicGL2 (𝓞 K) K => l • g) = adelicGLHaar (Fin 2) (𝓞 K) K := by
  have hhaar : (adelicGLHaar (Fin 2) (𝓞 K) K).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  have hright : (adelicGLHaar (Fin 2) (𝓞 K) K).IsMulRightInvariant :=
    NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar K
  have hcomp : (fun g : AdelicGL2 (𝓞 K) K => l • g) =
      (fun g => (l.1 : AdelicGL2 (𝓞 K) K) * g) ∘ (fun g => g * ((l.2 : adelicMaximalCompact K) : AdelicGL2 (𝓞 K) K)⁻¹) := by
    funext g; rw [Function.comp_apply, smul_def, mul_assoc]
  rw [hcomp, ← Measure.map_map (measurable_const_mul _) (measurable_mul_const _), map_mul_right_eq_self,
    map_mul_left_eq_self]

-- pin `:125`
theorem isInvInvariant_of_compactSpace {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (μ : Measure H) [μ.IsHaarMeasure] : μ.IsInvInvariant := by

  have hright : μ.IsMulRightInvariant := by
    refine ⟨fun g => ?_⟩
    have h := Measure.map_right_mul_eq_modularCharacterFun_smul μ g
    have huniv : (μ.map (· * g)) Set.univ = μ Set.univ := by
      rw [Measure.map_apply (measurable_mul_const g) MeasurableSet.univ, Set.preimage_univ]
    have hc : Measure.modularCharacterFun g = 1 := by
      have h2 := congrArg (fun ν : Measure H => ν Set.univ) h
      simp only [huniv] at h2
      have hne : μ Set.univ ≠ 0 := isOpen_univ.measure_ne_zero μ Set.univ_nonempty
      have htop : μ Set.univ ≠ ∞ := measure_ne_top μ _
      have : (Measure.modularCharacterFun g : ℝ≥0∞) = 1 := by
        rw [← ENNReal.mul_left_inj hne htop, one_mul]; exact h2.symm
      exact_mod_cast this
    rw [h, hc, one_smul]

  have h := Measure.isMulLeftInvariant_eq_smul μ.inv μ
  have huniv : μ.inv Set.univ = μ Set.univ := by
    rw [Measure.inv_def, Measure.map_apply measurable_inv MeasurableSet.univ, Set.preimage_univ]
  have hc : Measure.haarScalarFactor μ.inv μ = 1 := by
    have h2 := congrArg (fun ν : Measure H => ν Set.univ) h
    simp only [huniv] at h2
    have hne : μ Set.univ ≠ 0 := isOpen_univ.measure_ne_zero μ Set.univ_nonempty
    have htop : μ Set.univ ≠ ∞ := measure_ne_top μ _
    have : (Measure.haarScalarFactor μ.inv μ : ℝ≥0∞) = 1 := by
      rw [← ENNReal.mul_left_inj hne htop, one_mul]; exact h2.symm
    exact_mod_cast this
  refine ⟨?_⟩
  rw [h, hc, one_smul]

-- pin `:158`
scoped instance isInvInvariant_maximalCompactHaar : (maximalCompactHaar K).IsInvInvariant :=
  isInvInvariant_of_compactSpace (maximalCompactHaar K)

-- pin `:161`
def borelHaar : Measure (adelicBorel (𝓞 K) K) := Measure.haar

-- pin `:163`
scoped instance : (borelHaar K).IsHaarMeasure := by unfold borelHaar; infer_instance

-- pin `:165`
scoped instance sigmaFinite_borelHaar : SigmaFinite (borelHaar K) := by
  have hσ : SigmaCompactSpace (adelicBorel (𝓞 K) K) := sigmaCompactSpace_of_locallyCompact_secondCountable
  infer_instance

-- pin `:169`
scoped instance sigmaFinite_maximalCompactHaar : SigmaFinite (maximalCompactHaar K) := inferInstance

-- pin `:171`
def LHaar : Measure (L K) := (borelHaar K).prod (maximalCompactHaar K)

-- pin `:173`
scoped instance : (LHaar K).IsHaarMeasure := by unfold LHaar; infer_instance

-- pin `:175`
theorem exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa' :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
      ∀ φ : AdelicGL2 (𝓞 K) K → ℝ≥0∞, Measurable φ →
        ∫⁻ g, φ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
          c * ∫⁻ x, ∫⁻ u, ∫⁻ t, ∫⁻ k,
                φ (unipotentGL2 x * centralScalar (𝓞 K) K u * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
              ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K)
            ∂(adelicAddHaar (𝓞 K) K) := by
  have hhaar : (adelicGLHaar (Fin 2) (𝓞 K) K).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ

  obtain ⟨c₁, hc₁top, hc₁⟩ :=
    MeasureTheory.Measure.exists_eq_smul_map_smul_of_forall_map_smul_eq_of_isCompact_stabilizer (LHaar K)
      (X := AdelicGL2 (𝓞 K) K) (1 : AdelicGL2 (𝓞 K) K) (isCompact_stabilizer K) μ (map_smul_adelicGLHaar K)
  have hc₁0 : c₁ ≠ 0 := by
    intro h0
    have huniv : μ Set.univ = 0 := by rw [hc₁, h0, zero_smul]; rfl
    exact isOpen_univ.measure_ne_zero μ Set.univ_nonempty huniv

  obtain ⟨c₂, hc₂0, hc₂top, hc₂⟩ :=
    AutomorphicForm.exists_lintegral_adelicBorel_eq_mul_lintegral_coord_of_isMulLeftInvariant K (borelHaar K)
  refine ⟨c₁ * c₂, mul_ne_zero hc₁0 hc₂0, ENNReal.mul_ne_top hc₁top hc₂top, fun φ hφ => ?_⟩

  have hsm : Measurable fun l : L K => l • (1 : AdelicGL2 (𝓞 K) K) :=
    (continuous_id.smul continuous_const).measurable
  have hF : Measurable fun g : AdelicGL2 (𝓞 K) K => ∫⁻ k, φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) := by
    refine Measurable.lintegral_prod_right ?_
    exact hφ.comp (continuous_fst.mul (continuous_subtype_val.comp continuous_snd)).measurable
  calc ∫⁻ g, φ g ∂μ = c₁ * ∫⁻ l, φ (l • (1 : AdelicGL2 (𝓞 K) K)) ∂(LHaar K) := by
        rw [hc₁, lintegral_smul_measure, lintegral_map hφ hsm, smul_eq_mul]
    _ = c₁ * ∫⁻ b, ∫⁻ k, φ ((b : AdelicGL2 (𝓞 K) K) * ((k : AdelicGL2 (𝓞 K) K))⁻¹) ∂(maximalCompactHaar K) ∂(borelHaar K) := by
        congr 1
        rw [LHaar, lintegral_prod _ (show Measurable (fun l : L K => φ (l • (1 : AdelicGL2 (𝓞 K) K))) from hφ.comp hsm).aemeasurable]
        refine lintegral_congr fun b => lintegral_congr fun k => ?_
        rw [smul_def, mul_one]
    _ = c₁ * ∫⁻ b, ∫⁻ k, φ ((b : AdelicGL2 (𝓞 K) K) * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) ∂(borelHaar K) := by
        congr 1
        refine lintegral_congr fun b => ?_
        have hψ : Measurable fun k : adelicMaximalCompact K => φ ((b : AdelicGL2 (𝓞 K) K) * (k : AdelicGL2 (𝓞 K) K)) :=
          hφ.comp (continuous_const.mul continuous_subtype_val).measurable
        calc ∫⁻ k, φ ((b : AdelicGL2 (𝓞 K) K) * ((k : AdelicGL2 (𝓞 K) K))⁻¹) ∂(maximalCompactHaar K)
            = ∫⁻ k, φ ((b : AdelicGL2 (𝓞 K) K) * (k : AdelicGL2 (𝓞 K) K)) ∂((maximalCompactHaar K).inv) := by
              rw [Measure.inv_def, lintegral_map hψ measurable_inv]
              rfl
          _ = _ := by rw [Measure.IsInvInvariant.inv_eq_self]
    _ = c₁ * (c₂ * ∫⁻ x, ∫⁻ u, ∫⁻ t, (∫⁻ k, φ (unipotentGL2 x * centralScalar (𝓞 K) K u * diagOne t *
          (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) * ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
          ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(adelicAddHaar (𝓞 K) K)) := by
        rw [hc₂ _ hF]
    _ = _ := by
        rw [mul_assoc]
        congr 2
        refine lintegral_congr fun x => lintegral_congr fun u => lintegral_congr fun t => ?_
        rw [lintegral_mul_const _ ?_]
        exact hφ.comp (continuous_const.mul continuous_subtype_val).measurable

end IwasawaCoord

end AutomorphicForm

namespace NumberField.AdelicHaar

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

/-- The Iwasawa disintegration of the Haar integral on `GL₂(𝔸_K)`: up to one constant it is the
four-fold integral over the unipotent radical, the centre, the diagonal torus and the adelic
maximal compact, against the density `‖t‖⁻¹`. -/
theorem exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa
    (K : Type) [Field K] [NumberField K] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
      ∀ φ : AdelicGL2 (𝓞 K) K → ℝ≥0∞, Measurable φ →
        ∫⁻ g, φ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
          c * ∫⁻ x, ∫⁻ u, ∫⁻ t, ∫⁻ k,
                φ (unipotentGL2 x * centralScalar (𝓞 K) K u * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
              ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K)
            ∂(adelicAddHaar (𝓞 K) K) := by
  exact AutomorphicForm.IwasawaCoord.exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa' K

end NumberField.AdelicHaar
