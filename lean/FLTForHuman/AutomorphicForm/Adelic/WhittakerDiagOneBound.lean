/-
  The decay of the Whittaker coefficient at `diagOne` at a complex place.

  For an automorphic function `x` on the `Fin (n + 1)` circle-weight family at a complex place `w`,
  whose Whittaker coefficient is an eigenvector of the two Casimir operators with eigenvalues
  `lam`, `lam'`, and which is an su(2)-string in the sense of the complex Whittaker system, the
  coefficient at `diagOne` obeys a bound

    `‖W (g₀ * archComplexGLAt hw h)‖ ≤ C * (max 1 ‖det h‖) ^ r`

  for an exponent `r` read off the Casimir eigenvalue: a growth bound along the torus is exactly
  what the Bessel inequality consumes, and the two halves of the bound are the cusp half and the
  growth half of the profile.

  The row is the quantitative half of the archimedean Whittaker system: the local system supplies
  the differential equations, the torus-system growth lemmas turn them into a bound on the torus,
  and the coefficient's own API carries the bound back to `GL₂(𝔸)`.

  spec-pin: P2M/Sol/S_AutomorphicForm_exists_norm_whittakerCoefficient_diagOne_le_min_norm_rpow_of_isComplex_of_su2String.lean

  ## Shape

  One row from one 1,827-line pin (87 declarations, 85 of them public). The pin's development is
  transcribed in the pin's own order, one port namespace per pin proof-block label:

  | pin block | port home |
  |---|---|
  | `E40DCFN` (60 declarations) | `AutomorphicForm.DCFN` — the pin's 913-line sibling copy of this prelude is ported once in `AutomorphicForm/Adelic/WhittakerDiagOne.lean` (45 rows) and the eleven names it lacks (`casWords`/`casCoeff`/`casBarCoeff`, `archCasimir{,Bar}AtComplex_eq_sum`, `hasDerivAt_W_string`, the four `arch…` complex-derivative rows) once in `AutomorphicForm/Adelic/WhittakerSystem.lean` (11 rows) |
  | `E40UNI` (7) | `AutomorphicForm.StringUnipotent` (2 here) + `AutomorphicForm.UnipotentPoint` (3, in `WhittakerSystem.lean`); the two matrix-map rows are the port's `NumberField.AdelicLevel.ArchLevel` copies |
  | `E40IFC` (7) | `AutomorphicForm.IFC` (3 here, 4 in `WhittakerDiagOne.lean`) |
  | `E37K` (5) | `AutomorphicForm.KType` (4, in `WhittakerSystem.lean`) and `AutomorphicForm.Su2KType` (1: the pin's *second*, differently-stated `whittakerCoefficient_mul_right`, which takes `pins`/`ψ` and therefore cannot share the `DCFN` copy's home) |
  | `E43Z` (6) | `AutomorphicForm.Sl2Zero` |
  | `E41DISPATCH` (6) | `AutomorphicForm.TorusDisp` (5; `bdd_Icc` is the port's `LanglandsTunnell.GammaP41.bdd_Icc`) |
  | `E41ASM` (2) | `AutomorphicForm.Su2Core` |
  | wrapper `solution` | the published row name |

  Of the 85 pin public declarations, **17 are declared here** (all with distinct last names),
  **67 are satisfied by the import closure** (66 distinct names: the pin states
  `unipotentGL2_algebraMap_eq_globalPoints` twice, at `E40UNI:298` and `E43Z:1254`) and **1 is
  folded** into the row's name (`solution`). Every closure-credited copy was diffed against the pin's
  row with `statement_db`: **65 of the 66 names are byte-identical**, and the one exception,
  `KType.final_bound`, is alpha-equivalent only — `WhittakerSystem.lean` names the declaration's
  unused binder `_hδ` where the pin writes `hδ` (`check_port`'s `alpha_stmt` agrees, so the row is the
  pin's statement and nothing was re-declared).

  ## Reused, not re-proved

  * `AutomorphicForm/Adelic/WhittakerDiagOne.lean` — the 45 rows of the pin's `E40DCFN`/`E40IFC`
    machinery (`eC`, `iotaW`, `bprime`, `g0`, `W`, `Fstr`/`DFstr`/`DDstr`/`fstr`, `norm_eC`,
    `diagGL`, `diagOne_archUnitHom_eq_archComplexGLAt`, `norm_W_diagOne_eq_rpow_mul_norm_fstr`,
    `exists_norm_fstr_le`, `hM_string`/`twist`/`large`/`bounded`, `g0_comm`, `det_diagOne`, …).
  * `AutomorphicForm/Adelic/WhittakerSystem.lean` — the 18 su(2)-string prelude rows (the Casimir
    dictionary, the `K`-type block and `glArch_ext'`/`archComplexGLAt_unipotentGL2`/
    `unipotentGL2_algebraMap_eq_globalPoints`), written once there for the two orders that both pin
    them — `dedup --cross` on the pair reads 0 clusters.
  * `AutomorphicForm/Adelic/WhittakerCoefficient.lean` and `…/ArchWhittaker.lean` (the scaffold's) —
    the coefficient API, `whittakerCoefficient_sum_smul_of_continuous`, and the local complex
    Whittaker system the headline feeds.
  * `NumberTheory/AdelicLevel/ArchLevelLattice.lean` — `map_unipotentGL2`,
    `glEquivOfRingEquiv_unipotentGL2`.
  * `LanglandsTunnell/TorusSystemGrowth.lean` — `bdd_Icc` and the three growth lemmas
    `E41DISPATCH.exists_pos_norm_le_mul_rpow_of_torus_system` dispatches on.
  * `LanglandsTunnell/ODENearZeroBounds.lean`, `NumberTheory/StandardAddChar/GlobalAndInfinite.lean`,
    `NumberTheory/NumberField/TateGlobal/IdeleNormValues.lean` (the scaffold's) — the Bessel
    near-zero bound, `stdAddChar_single_infinitePlace_of_isComplex`, and the idèle-norm values.

  ## Port deltas

  Statements are the pin's byte for byte (`check_port` 20 ok / 0 mismatch / 0 missing); deltas are
  imports and proofs.

  * imports: two added — `…/WhittakerDiagOne` (the sibling copy of the prelude) and
    `…/WhittakerSystem` (the su(2)-string prelude) — plus
    `NumberTheory/AdelicLevel/ArchLevelLattice`, because the scaffold's six do not reach
    `map_unipotentGL2`. No `import Mathlib` (FR-0254).
  * the pin's `attribute [-instance] instCountableOfNumberField_definitions` is a pin-prelude name
    the port does not have, and is not carried; the pin's two `attribute [-ext]` lines are not
    carried either (`WhittakerDiagOne.lean` already removes
    `NumberField.InfinitePlace.Completion.ext` for the tree).
  * `letI := pins.nS` → `let` (FR-0255) in `Su2KType.whittakerCoefficient_mul_right` and
    `Sl2Zero.W_eq_zero_of_sl2_invariant`.
  * `eq_of_glArch_eq_of_glFin_eq` takes its field explicitly in the port (`K` in the pin is
    implicit); supplied in `StringUnipotent.archComplexGLAt_unipotentGL2`.
  * `UnipotentPoint.unipotentGL2_algebraMap_eq_globalPoints`: the pin states this twice
    (`E40UNI:298`, `E43Z:1254`) with the same statement, so it has one home; the pin's
    `Matrix.map_apply` simp argument is unused at `v4.34.0` and is dropped.
  * `Su2Core.mult_eq_two`: `if_neg` → `ite_eq_right` (FR-0255), and `omit [NumberField K] in` —
    `v4.34.0` includes the instance and then reports it unused (`unusedSectionVars`).
  * `TorusDisp.rescale0`: the pin's `all_goals try rfl` and its
    `convert … <;> first | rfl | ring` are no-ops at `v4.34.0` and trip `linter.unusedTactic`; they
    are folded into `all_goals (try simp only […]); push_cast; ring` and a bare `convert … using 1`
    (same proof, same statement).
  * `IFC.hCas_string`: seven of the pin's `simp only` arguments are unused at `v4.34.0`
    (`Matrix.cons_val_{zero,succ,one}`, `Matrix.head_cons`, `Fin.isValue`,
    `Fin.succ_{zero_eq_one,one_eq_two}`) and are dropped; `dif_pos` → `dite_eq_left`.
  * `TorusDisp.exists_pos_norm_le_mul_rpow_of_torus_system` reaches `bdd_Icc` as the port's
    `LanglandsTunnell.GammaP41.bdd_Icc` (opened at the block head) instead of re-declaring it.
  * the pin's `E37K` `final_bound` carries an unused `hδ : 0 ≤ δ`. Here that name is AF98A's
    (`_hδ`); this module cites nothing of it, and no declaration of the same name is re-declared.

  ## The one intra-module duplicate cluster

  `dedup.py --within` reports `W_eq_zero_of_sl2_invariant` twice (17 removable lines). This is the
  pin's own pair — `E43Z:1261` is the proof and `E40IFC:1335` is a one-line forwarder to it — kept
  because both copies are `private` in the pin and are `private` here, and the second is the name
  the row's driver calls. No other cluster; `move_dead.py` reads 0 declarations / 0 lines.

  ## Heartbeat probe

  (`lake env lean -DautoImplicit=false -DmaxHeartbeats=N`, never installed.) Silent at **75000**;
  first failure at **60000**, a `deterministic timeout at whnf` on the
  `unipotentGL2_algebraMap_eq_globalPoints` rewrite inside
  `Sl2Zero.W_eq_zero_of_sl2_invariant`. The measured pair for the probe is 75000 / 60000.
-/


import FLTForHuman.AutomorphicForm.Adelic.WhittakerDiagOne
import FLTForHuman.AutomorphicForm.Adelic.WhittakerSystem
import FLTForHuman.NumberTheory.AdelicLevel.ArchLevelLattice
import FLTForHuman.AutomorphicForm.Adelic.WhittakerCoefficient
import FLTForHuman.AutomorphicForm.Adelic.ArchWhittaker
import FLTForHuman.LanglandsTunnell.TorusSystemGrowth
import FLTForHuman.LanglandsTunnell.ODENearZeroBounds
import FLTForHuman.NumberTheory.StandardAddChar.GlobalAndInfinite
import FLTForHuman.NumberTheory.NumberField.TateGlobal.IdeleNormValues

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain

namespace AutomorphicForm

open scoped Classical

namespace StringUnipotent

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion

variable {K : Type} [Field K] [NumberField K]

theorem archComponent_glArch_unipotentGL2 (w : InfinitePlace K) (X : AdeleRing (𝓞 K) K) :
    archComponent K w (glArch (𝓞 K) K (unipotentGL2 X)) = unipotentGL2 (X.1 w) := by
  change Matrix.GeneralLinearGroup.map (archEval K w)
    (Matrix.GeneralLinearGroup.map (adeleArch (𝓞 K) K) (unipotentGL2 X)) = _
  rw [NumberField.AdelicLevel.ArchLevel.map_unipotentGL2, NumberField.AdelicLevel.ArchLevel.map_unipotentGL2]
  rfl

theorem glFin_unipotentGL2 (X : AdeleRing (𝓞 K) K) :
    glFin (𝓞 K) K (unipotentGL2 X) = unipotentGL2 X.2 := by
  change Matrix.GeneralLinearGroup.map (adeleFin (𝓞 K) K) (unipotentGL2 X) = _
  rw [NumberField.AdelicLevel.ArchLevel.map_unipotentGL2]
  rfl

end StringUnipotent

namespace IFC

open DCFN StringUnipotent UnipotentPoint NumberField.InfinitePlace.Completion

variable {K : Type} [Field K] [NumberField K]

open scoped Classical in
theorem hN_string (D : Set (AdelicGL2 (𝓞 K) K)) {w : InfinitePlace K} (hw : w.IsComplex) (b : (AdeleRing (𝓞 K) K)ˣ)
    {n : ℕ} (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ))
    (hxG : ∀ p (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x p (globalPoints (𝓞 K) K γ * g) = x p g)
    (hcomm : ∀ m : GL (Fin 2) ℂ, archComplexGLAt hw m * g0 w b = g0 w b * archComplexGLAt hw m) :
    ∀ (p : Fin (n + 1)) (z : ℂ) (h : GL (Fin 2) ℂ),
      whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g0 w b * archComplexGLAt hw (unipotentGL2 z * h)) =
        Complex.exp (2 * Real.pi * Complex.I * ((2 * ((1 : ℂ) * z).re : ℝ) : ℂ)) *
          whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g0 w b * archComplexGLAt hw h) := by
  intro p z h
  set X : AdeleRing (𝓞 K) K := (show (AdeleRing (𝓞 K) K) from (Pi.single w ((ringEquivComplexOfIsComplex hw).symm z), 0))
    with hX
  have hgeom : g0 w b * archComplexGLAt hw (unipotentGL2 z * h) = unipotentGL2 X * (g0 w b * archComplexGLAt hw h) := by
    rw [map_mul, ← mul_assoc, ← hcomm, archComplexGLAt_unipotentGL2, mul_assoc]
  rw [hgeom]
  have hper : ∀ (β : K) (u : AdeleRing (𝓞 K) K),
      x p (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β + u) * (g0 w b * archComplexGLAt hw h)) =
        x p (unipotentGL2 u * (g0 w b * archComplexGLAt hw h)) := by
    intro β u
    rw [unipotentGL2_add, mul_assoc, unipotentGL2_algebraMap_eq_globalPoints, hxG]
  have hcov := AutomorphicForm.whittakerCoefficient_unipotentGL2_mul K D
    (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
    (NumberField.StandardAddChar.stdAddChar K)
    (NumberField.StandardAddChar.adelicTraceData K).isGlobalAddChar_psiK.principalInvariant
    (x p) (g0 w b * archComplexGLAt hw h) hper 1 X
  rw [map_one, one_mul] at hcov
  rw [hcov, hX, NumberField.StandardAddChar.stdAddChar_single_infinitePlace_of_isComplex K w hw z, one_mul]

theorem hCas_string (D : Set (AdelicGL2 (𝓞 K) K)) {w : InfinitePlace K} (hw : w.IsComplex) (b : (AdeleRing (𝓞 K) K)ˣ)
    {n : ℕ} (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ)) (hxc : ∀ p, Continuous (x p))
    (hreg : ∀ p (l : List ArchDirComplex),
      IsArchSmoothAtComplex hw (l.foldr (archDerivAtComplex hw) (x p)) ∧ Continuous (l.foldr (archDerivAtComplex hw) (x p)))
    (lam lam' : ℂ)
    (hcas : ∀ p, archCasimirAtComplex hw (x p) = lam • x p ∧ archCasimirBarAtComplex hw (x p) = lam' • x p) :
    (∀ (p : Fin (n + 1)) (h : GL (Fin 2) ℂ),
      -((1 / 4 : ℂ) * ((1 / 2 : ℂ) * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .H (archDerivAtComplex hw .H (x p))) 1 (g0 w b * archComplexGLAt hw h) - Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .H (archDerivAtComplex hw .iH (x p))) 1 (g0 w b * archComplexGLAt hw h)) -
            Complex.I * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iH (archDerivAtComplex hw .H (x p))) 1 (g0 w b * archComplexGLAt hw h) - Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iH (archDerivAtComplex hw .iH (x p))) 1 (g0 w b * archComplexGLAt hw h))))) -
          (1 / 2 : ℂ) * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .H (x p)) 1 (g0 w b * archComplexGLAt hw h) - Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iH (x p)) 1 (g0 w b * archComplexGLAt hw h))) +
          (1 / 2 : ℂ) * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .E (archDerivAtComplex hw .Fm (x p))) 1 (g0 w b * archComplexGLAt hw h) - Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .E (archDerivAtComplex hw .iFm (x p))) 1 (g0 w b * archComplexGLAt hw h)) -
            Complex.I * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iE (archDerivAtComplex hw .Fm (x p))) 1 (g0 w b * archComplexGLAt hw h) - Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm (x p))) 1 (g0 w b * archComplexGLAt hw h))))) = lam * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g0 w b * archComplexGLAt hw h)) ∧
    (∀ (p : Fin (n + 1)) (h : GL (Fin 2) ℂ),
      -((1 / 4 : ℂ) * ((1 / 2 : ℂ) * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .H (archDerivAtComplex hw .H (x p))) 1 (g0 w b * archComplexGLAt hw h) + Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .H (archDerivAtComplex hw .iH (x p))) 1 (g0 w b * archComplexGLAt hw h)) +
            Complex.I * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iH (archDerivAtComplex hw .H (x p))) 1 (g0 w b * archComplexGLAt hw h) + Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iH (archDerivAtComplex hw .iH (x p))) 1 (g0 w b * archComplexGLAt hw h))))) -
          (1 / 2 : ℂ) * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .H (x p)) 1 (g0 w b * archComplexGLAt hw h) + Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iH (x p)) 1 (g0 w b * archComplexGLAt hw h))) +
          (1 / 2 : ℂ) * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .E (archDerivAtComplex hw .Fm (x p))) 1 (g0 w b * archComplexGLAt hw h) + Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .E (archDerivAtComplex hw .iFm (x p))) 1 (g0 w b * archComplexGLAt hw h)) +
            Complex.I * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iE (archDerivAtComplex hw .Fm (x p))) 1 (g0 w b * archComplexGLAt hw h) + Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm (x p))) 1 (g0 w b * archComplexGLAt hw h))))) = lam' * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g0 w b * archComplexGLAt hw h)) := by
  have hψ : Continuous (NumberField.StandardAddChar.stdAddChar K) :=
    (NumberField.StandardAddChar.isGlobalAddChar_stdAddChar K).continuous

  have hcw : ∀ (p : Fin (n + 1)) (j : Fin 10), Continuous (casWords hw (x p) j) := by
    intro p j
    have h2 : ∀ a b' : ArchDirComplex, Continuous (archDerivAtComplex hw a (archDerivAtComplex hw b' (x p))) :=
      fun a b' => by simpa only [List.foldr] using (hreg p [a, b']).2
    have h1 : ∀ a : ArchDirComplex, Continuous (archDerivAtComplex hw a (x p)) :=
      fun a => by simpa only [List.foldr] using (hreg p [a]).2
    fin_cases j <;> simp only [casWords] <;> first | exact h2 _ _ | exact h1 _
  have hsm : ∀ p : Fin (n + 1), IsArchSmoothAtComplex hw (x p) := fun p => by simpa only [List.foldr] using (hreg p []).1

  have hWsmul : ∀ (p : Fin (n + 1)) (c : ℂ) (g : AdelicGL2 (𝓞 K) K),
      whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (c • x p) 1 g = c * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 g := by
    intro p c g
    have h := AutomorphicForm.whittakerCoefficient_sum_smul_of_continuous K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
      (fun v => heckeGen (𝓞 K) K v) _ hψ 1 (fun _ => x p) (fun _ => hxc p) (fun _ => c) 1 g
    simp only [Fin.sum_univ_one] at h
    rw [show (c • x p) = fun g' => c * x p g' from funext fun g' => by simp [Pi.smul_apply, smul_eq_mul]]
    exact h
  have hWsum : ∀ (p : Fin (n + 1)) (cf : Fin 10 → ℂ) (g : AdelicGL2 (𝓞 K) K),
      whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (fun g' => ∑ j : Fin 10, cf j * casWords hw (x p) j g') 1 g =
        ∑ j : Fin 10, cf j * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (casWords hw (x p) j) 1 g := fun p cf g =>
    AutomorphicForm.whittakerCoefficient_sum_smul_of_continuous K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
      (fun v => heckeGen (𝓞 K) K v) _ hψ 10 (casWords hw (x p)) (hcw p) cf 1 g
  constructor
  · intro p h
    set g : AdelicGL2 (𝓞 K) K := g0 w b * archComplexGLAt hw h with hg
    have key : ∑ j : Fin 10, casCoeff j * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (casWords hw (x p) j) 1 g = lam * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 g := by
      rw [← hWsum, ← hWsmul, ← archCasimirAtComplex_eq_sum hw (hsm p), (hcas p).1]
    rw [← key]
    simp only [casCoeff, casWords, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.isValue]
    linear_combination (-(1 / 16 : ℂ) * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iH (archDerivAtComplex hw .iH (x p))) 1 g -
      (1 / 4 : ℂ) * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm (x p))) 1 g) * Complex.I_sq
  · intro p h
    set g : AdelicGL2 (𝓞 K) K := g0 w b * archComplexGLAt hw h with hg
    have key : ∑ j : Fin 10, casBarCoeff j * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (casWords hw (x p) j) 1 g = lam' * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 g := by
      rw [← hWsum, ← hWsmul, ← archCasimirBarAtComplex_eq_sum hw (hsm p), (hcas p).2]
    rw [← key]
    simp only [casBarCoeff, casWords, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.isValue]
    linear_combination (-(1 / 16 : ℂ) * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iH (archDerivAtComplex hw .iH (x p))) 1 g -
      (1 / 4 : ℂ) * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm (x p))) 1 g) * Complex.I_sq


end IFC


namespace Su2KType

variable (K : Type) [Field K] [NumberField K]

theorem whittakerCoefficient_mul_right (pins : CarrierPins K) (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (α : K) (g k : AdelicGL2 (𝓞 K) K) :
    whittakerCoefficient K pins ψ φ α (g * k) = whittakerCoefficient K pins ψ (fun y => φ (y * k)) α g := by
  let := pins.nS
  simp only [whittakerCoefficient, mul_assoc]

end Su2KType

namespace Sl2Zero

open DCFN NumberField.InfinitePlace.Completion

variable {K : Type} [Field K] [NumberField K]

def uW {w : InfinitePlace K} (hw : w.IsComplex) (z : ℂ) : AdeleRing (𝓞 K) K :=
  (show (AdeleRing (𝓞 K) K) from (Pi.single w ((ringEquivComplexOfIsComplex hw).symm z), 0))

theorem coe_archComplexGLAt {w : InfinitePlace K} (hw : w.IsComplex) (m : GL (Fin 2) ℂ) :
    ((archComplexGLAt hw m : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
      Matrix.of fun i j => (archMatrixUpdate K w ((m : Matrix (Fin 2) (Fin 2) ℂ).map (ringEquivComplexOfIsComplex hw).symm) i j,
        (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) :=
  rfl

theorem archComplexGLAt_unipotentGL2 {w : InfinitePlace K} (hw : w.IsComplex) (t : ℂ) :
    archComplexGLAt hw (unipotentGL2 t) = unipotentGL2 (uW hw t) := by
  apply Units.ext
  rw [coe_archComplexGLAt, unipotentGL2_coe]
  ext i j
  ·
    show (archMatrixUpdate K w (((unipotentGL2 t : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).map
        (ringEquivComplexOfIsComplex hw).symm) i j) = ((!![(1 : AdeleRing (𝓞 K) K), uW hw t; 0, 1]) i j).1
    funext v
    by_cases hv : v = w
    · subst hv
      rw [archMatrixUpdate_apply_self, Matrix.map_apply, unipotentGL2_coe]
      fin_cases i <;> fin_cases j <;> simp [uW, Matrix.of_apply] <;> rfl
    · rw [archMatrixUpdate_apply_of_ne K _ _ i j hv]
      fin_cases i <;> fin_cases j <;> simp [uW, Pi.single_eq_of_ne hv, Matrix.of_apply] <;> rfl
  ·
    fin_cases i <;> fin_cases j <;> simp [uW, Matrix.of_apply] <;> rfl

theorem stdAddChar_principalInvariant : IsPrincipalInvariantAddChar K (NumberField.StandardAddChar.stdAddChar K) :=
  (NumberField.StandardAddChar.isGlobalAddChar_stdAddChar K).principalInvariant

private theorem W_eq_zero_of_sl2_invariant (D : Set (AdelicGL2 (𝓞 K) K)) {w : InfinitePlace K} (hw : w.IsComplex) (b : (AdeleRing (𝓞 K) K)ˣ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφG : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), φ (globalPoints (𝓞 K) K γ * g) = φ g)
    (hZ : ∀ (g : AdelicGL2 (𝓞 K) K) (h : GL (Fin 2) ℂ), Matrix.GeneralLinearGroup.det h = 1 → φ (g * archComplexGLAt hw h) = φ g)
    (hcomm : ∀ m : GL (Fin 2) ℂ, archComplexGLAt hw m * g0 w b = g0 w b * archComplexGLAt hw m) (h : GL (Fin 2) ℂ) :
    whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1 (g0 w b * archComplexGLAt hw h) = 0 := by
  set g : AdelicGL2 (𝓞 K) K := g0 w b * archComplexGLAt hw h with hg

  have hii : ∀ t : ℂ, whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1 (unipotentGL2 (uW hw t) * g) = whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1 (g) := by
    intro t
    let := (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS
    simp only [whittakerCoefficient]
    congr 1
    funext x
    congr 1
    have hconj : g⁻¹ * archComplexGLAt hw (unipotentGL2 t) * g =
        archComplexGLAt hw (h⁻¹ * unipotentGL2 t * h) := by
      rw [hg, mul_inv_rev, map_mul, map_mul, map_inv]
      calc (archComplexGLAt hw h)⁻¹ * (g0 w b)⁻¹ * archComplexGLAt hw (unipotentGL2 t) * (g0 w b * archComplexGLAt hw h)
          = (archComplexGLAt hw h)⁻¹ * ((g0 w b)⁻¹ * (archComplexGLAt hw (unipotentGL2 t) * g0 w b)) * archComplexGLAt hw h := by
            simp only [mul_assoc]
        _ = (archComplexGLAt hw h)⁻¹ * archComplexGLAt hw (unipotentGL2 t) * archComplexGLAt hw h := by
            rw [hcomm, ← mul_assoc (g0 w b)⁻¹, inv_mul_cancel, one_mul]
    have hdet : Matrix.GeneralLinearGroup.det (h⁻¹ * unipotentGL2 t * h) = 1 := by
      rw [map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]
      apply Units.ext
      simp [Matrix.GeneralLinearGroup.val_det_apply, unipotentGL2_coe, Matrix.det_fin_two]
    calc φ (unipotentGL2 x * (unipotentGL2 (uW hw t) * g))
        = φ ((unipotentGL2 x * g) * (g⁻¹ * archComplexGLAt hw (unipotentGL2 t) * g)) := by
          rw [← archComplexGLAt_unipotentGL2]; congr 1; group
      _ = φ (unipotentGL2 x * g) := by rw [hconj]; exact hZ _ _ hdet

  have hi : ∀ t : ℂ, whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1 (unipotentGL2 (uW hw t) * g) =
      NumberField.StandardAddChar.stdAddChar K (uW hw t) * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1 (g) := by
    intro t
    have h := AutomorphicForm.whittakerCoefficient_unipotentGL2_mul K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
      (fun v => heckeGen (𝓞 K) K v) (NumberField.StandardAddChar.stdAddChar K) stdAddChar_principalInvariant φ g
      (fun β u => by rw [unipotentGL2_add, UnipotentPoint.unipotentGL2_algebraMap_eq_globalPoints, mul_assoc, hφG]) 1 (uW hw t)
    rwa [map_one, one_mul] at h

  have hval : NumberField.StandardAddChar.stdAddChar K (uW hw (1 / 4 : ℂ)) = -1 := by
    have h := NumberField.StandardAddChar.stdAddChar_single_infinitePlace_of_isComplex K w hw (1 / 4 : ℂ)
    rw [show uW hw (1 / 4 : ℂ) = (show (AdeleRing (𝓞 K) K) from (Pi.single w ((ringEquivComplexOfIsComplex hw).symm (1 / 4 : ℂ)), 0)) from rfl, h]
    have hre : (2 * (1 / 4 : ℂ).re : ℝ) = 1 / 2 := by norm_num
    rw [hre]
    push_cast
    rw [show (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (1 / 2) = (Real.pi : ℂ) * Complex.I by ring, Complex.exp_pi_mul_I]
  have h1 := hi (1 / 4 : ℂ)
  rw [hii, hval] at h1

  have : (2 : ℂ) * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1 (g) = 0 := by linear_combination h1
  exact (mul_eq_zero.mp this).resolve_left two_ne_zero

end Sl2Zero

namespace IFC

open DCFN

variable {K : Type} [Field K] [NumberField K]

private theorem W_eq_zero_of_sl2_invariant (D : Set (AdelicGL2 (𝓞 K) K)) {w : InfinitePlace K} (hw : w.IsComplex) (b : (AdeleRing (𝓞 K) K)ˣ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφG : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), φ (globalPoints (𝓞 K) K γ * g) = φ g)
    (hZ : ∀ (g : AdelicGL2 (𝓞 K) K) (h : GL (Fin 2) ℂ), Matrix.GeneralLinearGroup.det h = 1 → φ (g * archComplexGLAt hw h) = φ g)
    (hcomm : ∀ m : GL (Fin 2) ℂ, archComplexGLAt hw m * g0 w b = g0 w b * archComplexGLAt hw m) (h : GL (Fin 2) ℂ) :
    whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1 (g0 w b * archComplexGLAt hw h) = 0 :=
  Sl2Zero.W_eq_zero_of_sl2_invariant D hw b φ hφG hZ hcomm h

end IFC

open scoped Real

namespace TorusDisp

open Real Set LanglandsTunnell.GammaP41

theorem extend_bdd (f : ℝ → ℂ) (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (L B : ℝ)
    (hB : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ B) :
    ∃ B' : ℝ, 0 ≤ B' ∧ ∀ y : ℝ, 0 < y → y ≤ L → ‖f y‖ ≤ B' := by
  obtain ⟨M, hM0, hM⟩ := LanglandsTunnell.GammaP41.bdd_Icc f hf 1 L one_pos
  refine ⟨max B 0 + M, by positivity, fun y hy hyL => ?_⟩
  rcases le_or_gt y 1 with h1 | h1
  · exact (hB y hy h1).trans ((le_max_left _ _).trans (by linarith))
  · exact (hM y ⟨h1.le, hyL⟩).trans (by linarith [le_max_right B 0])

theorem rpow_m12_hasDerivAt {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) (-(1 / 2 : ℝ) * (y ^ (-(1 / 2 : ℝ)) * y⁻¹)) y := by
  have h := Real.hasDerivAt_rpow_const (p := -(1 / 2 : ℝ)) (Or.inl hy.ne')
  rw [Real.rpow_sub_one hy.ne', div_eq_mul_inv] at h
  exact h

theorem rescale0 (κ lam : ℂ) (hκ : κ ≠ 0) (νC : ℂ) (hν : νC ^ 2 = 1 - 4 * lam) (F : ℝ → ℂ)
    (hF : DifferentiableOn ℝ F (Set.Ioi 0)) (hF' : DifferentiableOn ℝ (deriv F) (Set.Ioi 0))
    (heq : ∀ y : ℝ, 0 < y → (y : ℂ) ^ 2 * deriv (deriv F) y - (y : ℂ) * deriv F y +
      (4 * lam - 16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ : ℝ) : ℂ) ^ 2 * (y : ℂ) ^ 2) * F y = 0) :
    let c : ℝ := 2 * ‖κ‖
    let G : ℝ → ℂ := fun Y => ((((Y / c) ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * F (Y / c)
    0 < c ∧ DifferentiableOn ℝ G (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv G) (Set.Ioi 0) ∧
    (∀ Y : ℝ, 0 < Y → (Y : ℂ) ^ 2 * deriv (deriv G) Y + (1 / 4 - νC ^ 2 - 4 * (π : ℂ) ^ 2 * (Y : ℂ) ^ 2) * G Y = 0) ∧
    (∀ y : ℝ, 0 < y → G (c * y) = (((y ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * F y) := by
  intro c G
  have hκn : 0 < ‖κ‖ := norm_pos_iff.mpr hκ
  have hc : 0 < c := by positivity
  set g : ℝ → ℂ := fun y => (((y ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * F y with hgdef
  set g1 : ℝ → ℂ := fun y => (((y ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * (-(1 / 2 : ℂ) * (y : ℂ)⁻¹ * F y + deriv F y) with hg1def
  set g2 : ℝ → ℂ := fun y => (((y ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) *
    ((3 / 4 : ℂ) * (y : ℂ)⁻¹ * (y : ℂ)⁻¹ * F y - (y : ℂ)⁻¹ * deriv F y + deriv (deriv F) y) with hg2def
  have hFd : ∀ y : ℝ, 0 < y → HasDerivAt F (deriv F y) y :=
    fun y hy => (hF.differentiableAt (Ioi_mem_nhds hy)).hasDerivAt
  have hFdd : ∀ y : ℝ, 0 < y → HasDerivAt (deriv F) (deriv (deriv F) y) y :=
    fun y hy => (hF'.differentiableAt (Ioi_mem_nhds hy)).hasDerivAt
  have hpwC : ∀ y : ℝ, 0 < y → HasDerivAt (fun x : ℝ => (((x ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ))
      (((-(1 / 2 : ℝ) * (y ^ (-(1 / 2 : ℝ)) * y⁻¹)) : ℝ) : ℂ) y :=
    fun y hy => (rpow_m12_hasDerivAt hy).ofReal_comp
  have hg1 : ∀ y : ℝ, 0 < y → HasDerivAt g (g1 y) y := by
    intro y hy
    have h := (hpwC y hy).mul (hFd y hy)
    have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    convert h using 1
    all_goals (try simp only [hg1def]); push_cast; ring
  have hderiv_g : ∀ y : ℝ, 0 < y → deriv g y = g1 y := fun y hy => (hg1 y hy).deriv
  have hg2 : ∀ y : ℝ, 0 < y → HasDerivAt g1 (g2 y) y := by
    intro y hy
    have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    have hinv : HasDerivAt (fun x : ℝ => (x : ℂ)⁻¹) (-((y : ℂ) ^ 2)⁻¹) y := by
      have h1 := (hasDerivAt_inv hy.ne').ofReal_comp
      have hfun : (fun x : ℝ => (x : ℂ)⁻¹) = fun x : ℝ => (((x⁻¹ : ℝ)) : ℂ) := by funext x; push_cast; rfl
      rw [hfun]
      convert h1 using 1
      all_goals push_cast; ring
    have hin : HasDerivAt (fun x : ℝ => -(1 / 2 : ℂ) * (x : ℂ)⁻¹ * F x + deriv F x)
        (-(1 / 2 : ℂ) * (-((y : ℂ) ^ 2)⁻¹) * F y + -(1 / 2 : ℂ) * (y : ℂ)⁻¹ * deriv F y + deriv (deriv F) y) y := by
      have := ((hinv.const_mul (-(1 / 2 : ℂ))).mul (hFd y hy)).add (hFdd y hy)
      convert this using 1
    have h := (hpwC y hy).mul hin
    convert h using 1
    all_goals (try simp only [hg2def]); push_cast; field_simp; ring
  have hg1d : ∀ y : ℝ, 0 < y → HasDerivAt (deriv g) (g2 y) y := by
    intro y hy
    refine (hg2 y hy).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hy] with s hs
    exact hderiv_g s hs
  have hGg : G = fun Y => g (Y / c) := rfl
  have hdiv : ∀ Y : ℝ, HasDerivAt (fun X : ℝ => X / c) (1 / c) Y := fun Y => by
    simpa using (hasDerivAt_id Y).div_const c
  have hG1 : ∀ Y : ℝ, 0 < Y → HasDerivAt G ((1 / c) • g1 (Y / c)) Y := by
    intro Y hY
    have hy : 0 < Y / c := div_pos hY hc
    rw [hGg]; exact (hg1 _ hy).scomp Y (hdiv Y)
  have hderiv_G : ∀ Y : ℝ, 0 < Y → deriv G Y = (1 / c) • g1 (Y / c) := fun Y hY => (hG1 Y hY).deriv
  have hG2 : ∀ Y : ℝ, 0 < Y → HasDerivAt (deriv G) ((1 / c) • ((1 / c) • g2 (Y / c))) Y := by
    intro Y hY
    have hy : 0 < Y / c := div_pos hY hc
    have h := ((hg2 _ hy).scomp Y (hdiv Y)).const_smul (1 / c)
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hY] with s hs
    rw [hderiv_G s hs]; rfl
  have hGd : DifferentiableOn ℝ G (Set.Ioi 0) := fun Y hY => (hG1 Y hY).differentiableAt.differentiableWithinAt
  have hGd' : DifferentiableOn ℝ (deriv G) (Set.Ioi 0) := fun Y hY => (hG2 Y hY).differentiableAt.differentiableWithinAt
  have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hcn : (c : ℂ) ^ 2 = 4 * ((‖κ‖ : ℝ) : ℂ) ^ 2 := by show ((2 * ‖κ‖ : ℝ) : ℂ) ^ 2 = _; push_cast; ring
  have hsum : ∀ y : ℝ, 0 < y → (y : ℂ) ^ 2 * g2 y + (-(3 / 4 : ℂ) + 4 * lam - 4 * (π : ℂ) ^ 2 * (c : ℂ) ^ 2 * (y : ℂ) ^ 2) * g y = 0 := by
    intro y hy
    have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    have e := heq y hy
    have h2 : (y : ℂ) ^ 2 * g2 y = (((y ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) *
        ((3 / 4 : ℂ) * F y - (y : ℂ) * deriv F y + (y : ℂ) ^ 2 * deriv (deriv F) y) := by
      simp only [hg2def]; field_simp
    rw [h2]
    simp only [hgdef]
    linear_combination (((y ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * e +
      (-(4 : ℂ) * (π : ℂ) ^ 2 * (y : ℂ) ^ 2 * (((y ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * F y) * hcn
  refine ⟨hc, hGd, hGd', fun Y hY => ?_, fun y hy => ?_⟩
  · have hy : 0 < Y / c := div_pos hY hc
    rw [(hG2 Y hY).deriv]
    have hYy : (Y : ℂ) = (c : ℂ) * ((Y / c : ℝ) : ℂ) := by push_cast; field_simp
    have h3 : (Y : ℂ) ^ 2 * ((1 / c) • ((1 / c) • g2 (Y / c))) = (((Y / c : ℝ)) : ℂ) ^ 2 * g2 (Y / c) := by
      rw [hYy]; simp only [Complex.real_smul]; push_cast; field_simp
    have hGY : G Y = g (Y / c) := rfl
    rw [h3, hGY, hYy, hν]
    linear_combination hsum (Y / c) hy
  · show g (c * y / c) = _
    rw [mul_div_cancel_left₀ _ hc.ne']

theorem n0_neg (κ lam : ℂ) (hκ : κ ≠ 0) (him : lam.im = 0) (hneg : lam.re < 0) (F : ℝ → ℂ)
    (hF : DifferentiableOn ℝ F (Set.Ioi 0)) (hF' : DifferentiableOn ℝ (deriv F) (Set.Ioi 0))
    (heq : ∀ y : ℝ, 0 < y → (y : ℂ) ^ 2 * deriv (deriv F) y - (y : ℂ) * deriv F y +
      (4 * lam - 16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ : ℝ) : ℂ) ^ 2 * (y : ℂ) ^ 2) * F y = 0)
    (B : ℝ) (hB : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖F y‖ ≤ B) :
    ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖F y‖ ≤ C * y := by
  have hlam : lam = ((lam.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [him]
  set ν : ℝ := Real.sqrt (1 - 4 * lam.re) with hνdef
  have hν1 : 1 < ν := by
    rw [hνdef]
    calc (1 : ℝ) = Real.sqrt 1 := by simp
      _ < Real.sqrt (1 - 4 * lam.re) := Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  have hν0 : 0 ≤ ν := by linarith
  have hνsq : ν ^ 2 = 1 - 4 * lam.re := Real.sq_sqrt (by linarith)
  have hνC : ((ν : ℝ) : ℂ) ^ 2 = 1 - 4 * lam := by rw [hlam]; exact_mod_cast hνsq
  have hνre : ((ν : ℝ) : ℂ).re = ν := Complex.ofReal_re _
  obtain ⟨hc, hGd, hGd', hGeq, hGval⟩ := rescale0 κ lam hκ ((ν : ℝ) : ℂ) hνC F hF hF' heq
  set c : ℝ := 2 * ‖κ‖ with hcdef
  set G : ℝ → ℂ := fun Y => ((((Y / c) ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * F (Y / c) with hGdef
  obtain ⟨B', hB'0, hB'⟩ := extend_bdd F hF (1 / c) B hB

  have hGap : ∀ Y : ℝ, 0 < Y → Y ≤ 1 → ‖G Y‖ ≤ (B' * c ^ (-(-(1 / 2 : ℝ)))) * Y ^ (-(1 / 2 : ℝ)) := by
    intro Y hY hY1
    have hy : 0 < Y / c := div_pos hY hc
    have hyc : Y / c ≤ 1 / c := div_le_div_of_nonneg_right hY1 hc.le
    simp only [hGdef]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hy _),
      Real.div_rpow hY.le hc.le, Real.rpow_neg hc.le, div_eq_mul_inv, inv_inv]
    calc Y ^ (-(1 / 2 : ℝ)) * c ^ (1 / 2 : ℝ) * ‖F (Y / c)‖ ≤ Y ^ (-(1 / 2 : ℝ)) * c ^ (1 / 2 : ℝ) * B' := by
          gcongr; exact hB' _ hy hyc
      _ = (B' * c ^ (-(-(1 / 2 : ℝ)))) * Y ^ (-(1 / 2 : ℝ)) := by rw [neg_neg]; ring
  have hGAP := LanglandsTunnell.norm_le_mul_rpow_near_zero_of_bessel_ode_of_forcing_of_apriori ((ν : ℝ) : ℂ)
    (by rw [hνre]; exact hν0) 10 0 (-(1 / 2)) _ G (fun _ => 0) hGd hGd' (fun Y _ _ => by simp)
    hGap (fun Y hY => by rw [hGeq Y hY])
  have hr : 1 / 2 - ((ν : ℝ) : ℂ).re < -(1 / 2) := by rw [hνre]; linarith
  obtain ⟨C, hC⟩ := hGAP.2 hr (1 / 2) (by norm_num)
  have hexp1 : (1 : ℝ) ≤ min (1 / 2 + ((ν : ℝ) : ℂ).re) 10 - 1 / 2 := by
    rw [hνre]; refine le_sub_iff_add_le.mpr (le_min (by linarith) (by norm_num))

  have hnear : ∀ y : ℝ, 0 < y → y ≤ 1 → c * y ≤ 1 → ‖F y‖ ≤ max C 0 * c * y := by
    intro y hy hy1 hcy
    have hY : 0 < c * y := by positivity
    have h := (hC (c * y) hY hcy).1
    rw [hGval y hy, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hy _)] at h
    have hle : (c * y) ^ (min (1 / 2 + ((ν : ℝ) : ℂ).re) 10 - 1 / 2) ≤ (c * y) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hY hcy hexp1
    rw [Real.rpow_one] at hle
    have hpos := Real.rpow_pos_of_pos hy (1 / 2 : ℝ)
    have h2 := mul_le_mul_of_nonneg_left h hpos.le
    rw [← mul_assoc, ← Real.rpow_add hy, show (1 / 2 : ℝ) + -(1 / 2) = 0 by norm_num, Real.rpow_zero, one_mul] at h2
    have hy12 : y ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hy.le hy1 (by norm_num)
    have hA : C * (c * y) ^ (min (1 / 2 + ((ν : ℝ) : ℂ).re) 10 - 1 / 2) ≤ max C 0 * (c * y) :=
      calc C * (c * y) ^ (min (1 / 2 + ((ν : ℝ) : ℂ).re) 10 - 1 / 2)
          ≤ max C 0 * (c * y) ^ (min (1 / 2 + ((ν : ℝ) : ℂ).re) 10 - 1 / 2) := by gcongr; exact le_max_left _ _
        _ ≤ max C 0 * (c * y) := mul_le_mul_of_nonneg_left hle (le_max_right _ _)
    calc ‖F y‖ ≤ y ^ (1 / 2 : ℝ) * (C * (c * y) ^ (min (1 / 2 + ((ν : ℝ) : ℂ).re) 10 - 1 / 2)) := h2
      _ ≤ y ^ (1 / 2 : ℝ) * (max C 0 * (c * y)) := mul_le_mul_of_nonneg_left hA hpos.le
      _ ≤ 1 * (max C 0 * (c * y)) := mul_le_mul_of_nonneg_right hy12 (by positivity)
      _ = max C 0 * c * y := by ring

  obtain ⟨M, hM0, hM⟩ := bdd_Icc F hF (1 / c) 1 (by positivity)
  refine ⟨max C 0 * c + M * c, fun y hy hy1 => ?_⟩
  rcases le_or_gt (c * y) 1 with hcy | hcy
  · calc ‖F y‖ ≤ max C 0 * c * y := hnear y hy hy1 hcy
      _ ≤ (max C 0 * c + M * c) * y := by
          rw [add_mul]; linarith [mul_nonneg (mul_nonneg hM0 hc.le) hy.le]
  · have hyc' : 1 / c ≤ y := by rw [div_le_iff₀ hc, mul_comm]; exact hcy.le
    calc ‖F y‖ ≤ M := hM y ⟨hyc', hy1⟩
      _ ≤ M * (c * y) := le_mul_of_one_le_right hM0 hcy.le
      _ ≤ (max C 0 * c + M * c) * y := by nlinarith [le_max_right C 0, hc]

theorem exists_pos_norm_le_mul_rpow_of_torus_system
    (n : ℕ) (κ lam lam' : ℂ) (hκ : κ ≠ 0) (f : ℕ → ℝ → ℂ)
    (hsys :
    ∀ p : Fin (n + 1),
      DifferentiableOn ℝ (f p) (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv (f p)) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        ((y : ℂ) ^ 2 * deriv (deriv (f p)) y + (((n : ℂ) - 2 * (p : ℕ)) - 1) * (y : ℂ) * deriv (f p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) - 4) / 4 + 4 * lam -
                16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * f p y +
            8 * (Real.pi : ℂ) * Complex.I * κ * (y : ℂ) * f ((p : ℕ) + 1) y = 0) ∧
        ((y : ℂ) ^ 2 * deriv (deriv (f p)) y - (((n : ℂ) - 2 * (p : ℕ)) + 1) * (y : ℂ) * deriv (f p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) + 4) / 4 + 4 * lam' -
                16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * f p y -
            8 * (Real.pi : ℂ) * Complex.I * (starRingEnd ℂ) κ * ((p : ℕ) * ((n : ℂ) + 1 - (p : ℕ))) * (y : ℂ) *
              f ((p : ℕ) - 1) y = 0))
    (hfn : ∀ y : ℝ, f (n + 1) y = 0)
    (hU : lam' = (starRingEnd ℂ) lam)
    (hR : lam' = lam → lam.im = 0 → n = 0 ∨ -(((n : ℝ) ^ 2 + 4 * (n : ℝ)) / 16) < lam.re)
    (hZ0 : lam = 0 → n = 0 → ∀ y : ℝ, 0 < y → f 0 y = 0)
    (hbdd : ∀ p : Fin (n + 1), ∃ B : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f p y‖ ≤ B) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ (p : Fin (n + 1)) (y : ℝ), 0 < y → y ≤ 1 → ‖f p y‖ ≤ C * y ^ δ := by

  have fromEps : (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ (p : Fin (n + 1)) (y : ℝ), 0 < y → y ≤ 1 → ‖f p y‖ ≤ C * y ^ (1 - ε)) →
      ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ (p : Fin (n + 1)) (y : ℝ), 0 < y → y ≤ 1 → ‖f p y‖ ≤ C * y ^ δ := by
    intro h
    obtain ⟨C, hC⟩ := h (1 / 2) (by norm_num)
    exact ⟨1 / 2, by norm_num, C, fun p y hy hy1 => by have := hC p y hy hy1; norm_num at this ⊢; exact this⟩
  by_cases him : lam.im = 0
  ·
    have hlam' : lam' = lam := by rw [hU]; exact Complex.conj_eq_iff_im.mpr him
    rcases lt_or_ge 0 lam.re with hpos | hnp
    ·
      exact LanglandsTunnell.exists_pos_norm_le_mul_rpow_of_torus_system_casimir_eq_real_pos n κ lam lam' hκ hlam' him hpos
        f hsys hfn
    · rcases Nat.even_or_odd n with hev | hodd
      · rcases Nat.eq_zero_or_pos n with hn0 | hnpos
        ·
          subst hn0
          by_cases hl0 : lam = 0
          ·
            refine ⟨1, one_pos, 0, fun p y hy hy1 => ?_⟩
            have hp : ((p : Fin (0 + 1)) : ℕ) = 0 := by omega
            rw [hp, hZ0 hl0 rfl y hy]; simp
          ·
            have hneg : lam.re < 0 := by
              rcases lt_or_eq_of_le hnp with h | h
              · exact h
              · exact absurd (Complex.ext (by simpa using h) (by simpa using him)) hl0
            obtain ⟨B, hB⟩ := hbdd 0
            have heq : ∀ y : ℝ, 0 < y → (y : ℂ) ^ 2 * deriv (deriv (f 0)) y - (y : ℂ) * deriv (f 0) y +
                (4 * lam - 16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ : ℝ) : ℂ) ^ 2 * (y : ℂ) ^ 2) * f 0 y = 0 := by
              intro y hy
              have h2 := (((hsys 0).2.2) y hy).2
              rw [hlam'] at h2
              have h0 : (((0 : Fin (0 + 1)) : ℕ)) = 0 := rfl
              simp only [h0] at h2
              push_cast at h2 ⊢
              linear_combination h2
            obtain ⟨C, hC⟩ := n0_neg κ lam hκ him hneg (f 0) (hsys 0).1 (hsys 0).2.1 heq B hB
            refine ⟨1, one_pos, C, fun p y hy hy1 => ?_⟩
            have hp : ((p : Fin (0 + 1)) : ℕ) = 0 := by omega
            rw [hp, Real.rpow_one]
            exact hC y hy hy1
        ·
          have hn2 : 2 ≤ n := by obtain ⟨m, hm⟩ := hev; omega
          exact LanglandsTunnell.exists_norm_le_mul_rpow_of_torus_system_even_casimir_real_nonpos_of_bounded n hev hn2
            κ lam lam' hκ hlam' him hnp f hfn hbdd hsys
      ·
        have hre : lam.re = lam'.re := by rw [hlam']
        exact fromEps (LanglandsTunnell.norm_le_mul_rpow_of_torus_system_of_casimir_ne_of_re_eq n κ lam lam' hκ
          (Or.inr hodd) hre f hfn hsys)
  ·
    have hne : lam ≠ lam' := by
      intro h
      apply him
      have : (starRingEnd ℂ) lam = lam := by rw [← hU, ← h]
      exact Complex.conj_eq_iff_im.mp this
    have hre : lam.re = lam'.re := by rw [hU, Complex.conj_re]
    exact fromEps (LanglandsTunnell.norm_le_mul_rpow_of_torus_system_of_casimir_ne_of_re_eq n κ lam lam' hκ
      (Or.inl hne) hre f hfn hsys)
end TorusDisp

namespace Su2Core

open DCFN NumberField.InfinitePlace

variable {K : Type} [Field K] [NumberField K]

omit [NumberField K] in
theorem mult_eq_two {w : InfinitePlace K} (hw : w.IsComplex) : (w.mult : ℝ) = 2 := by
  rw [NumberField.InfinitePlace.mult, ite_eq_right (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr hw)]; norm_num

theorem core (D : Set (AdelicGL2 (𝓞 K) K))
    (ξ : (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    {w : InfinitePlace K} (hw : w.IsComplex)
    {n : ℕ} (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ))
    (hxZ : ∀ p (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      x p (centralScalar (𝓞 K) K z * g) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x p g)
    (hwt : ∀ p : Fin (n + 1), HasCircleWeightAt hw ((n : ℤ) - 2 * (p : ℕ)) (x p))
    (hgr : ∀ p, ∃ C₀ : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 g‖ ≤ C₀ * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2))
    (lam lam' : ℂ) (hU : lam' = (starRingEnd ℂ) lam)
    (hR : lam' = lam → lam.im = 0 → n = 0 ∨ -(((n : ℝ) ^ 2 + 4 * (n : ℝ)) / 16) < lam.re)
    (b : (AdeleRing (𝓞 K) K)ˣ) (hb : ((b : AdeleRing (𝓞 K) K)).2 = 1)
    (f : ℕ → ℝ → ℂ)
    (hf : ∀ (p : Fin (n + 1)) (y : ℝ), f p y =
      whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g0 w b * archComplexGLAt hw (splitTorusGL2Complex ((Real.log y / 2 : ℝ) : ℂ))))
    (hsys :
    ∀ p : Fin (n + 1),
      DifferentiableOn ℝ (f p) (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv (f p)) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        ((y : ℂ) ^ 2 * deriv (deriv (f p)) y + (((n : ℂ) - 2 * (p : ℕ)) - 1) * (y : ℂ) * deriv (f p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) - 4) / 4 + 4 * lam -
                16 * (Real.pi : ℂ) ^ 2 * ((‖(1 : ℂ)‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * f p y +
            8 * (Real.pi : ℂ) * Complex.I * (1 : ℂ) * (y : ℂ) * f ((p : ℕ) + 1) y = 0) ∧
        ((y : ℂ) ^ 2 * deriv (deriv (f p)) y - (((n : ℂ) - 2 * (p : ℕ)) + 1) * (y : ℂ) * deriv (f p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) + 4) / 4 + 4 * lam' -
                16 * (Real.pi : ℂ) ^ 2 * ((‖(1 : ℂ)‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * f p y -
            8 * (Real.pi : ℂ) * Complex.I * (starRingEnd ℂ) (1 : ℂ) * ((p : ℕ) * ((n : ℂ) + 1 - (p : ℕ))) * (y : ℂ) *
              f ((p : ℕ) - 1) y = 0))
    (hfn : ∀ y : ℝ, f (n + 1) y = 0)
    (hZ0 : lam = 0 → n = 0 → ∀ y : ℝ, 0 < y → f 0 y = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ p : Fin (n + 1),
      ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
        (∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w') →
        ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (diagOne a)‖ ≤
          C * ‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) * (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 w‖) ^ δ := by

  have hbdd : ∀ p : Fin (n + 1), ∃ B : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f p y‖ ≤ B := by
    intro p
    obtain ⟨B, hB⟩ := IFC.bounded D ξ w₀ hξ hw b hb (x p) (hxZ p) (hgr p)
    exact ⟨B, fun y hy hy1 => by rw [hf]; exact hB y hy hy1⟩

  obtain ⟨δ, hδ, C, hC⟩ := TorusDisp.exists_pos_norm_le_mul_rpow_of_torus_system n 1 lam lam' one_ne_zero f hsys hfn hU hR hZ0 hbdd

  choose Bl hBl using fun p => IFC.large D w₀ hw b hb (x p) (hgr p)
  refine ⟨δ, hδ, max C 0 + ∑ p : Fin (n + 1), max (Bl p) 0, fun p a ha hab => ?_⟩
  set r : ℝ := ‖((a : AdeleRing (𝓞 K) K)).1 w‖ with hr
  set E : ℝ := (w.mult : ℝ) * w₀ / 2 with hE
  have hr0 : 0 < r := by
    rw [hr, norm_pos_iff]
    intro h0
    have h1 : (((a * a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w = 1 := by rw [mul_inv_cancel]; rfl
    have : (((a * a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w =
        ((a : AdeleRing (𝓞 K) K)).1 w * (((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w := rfl
    rw [this, h0, zero_mul] at h1; exact zero_ne_one h1
  have hrE : 0 ≤ r ^ E := Real.rpow_nonneg hr0.le _
  have hmin0 : 0 < min 1 r := lt_min one_pos hr0
  have hminδ : 0 ≤ (min 1 r) ^ δ := Real.rpow_nonneg hmin0.le _
  have hBsum : max (Bl p) 0 ≤ ∑ q : Fin (n + 1), max (Bl q) 0 :=
    Finset.single_le_sum (fun q _ => le_max_right (Bl q) 0) (Finset.mem_univ p)
  have hlarge := hBl p a ha hab
  rcases le_or_gt r 1 with hr1 | hr1
  ·
    have htw := IFC.twist D ξ w₀ hξ hw b hb x hxZ hwt p a ha hab
    rw [min_eq_right hr1]
    rw [htw, ← hf p r]
    calc r ^ E * ‖f p r‖ ≤ r ^ E * (C * r ^ δ) := mul_le_mul_of_nonneg_left (hC p r hr0 hr1) hrE
      _ ≤ r ^ E * (max C 0 * r ^ δ) := by gcongr; exact le_max_left _ _
      _ = max C 0 * r ^ E * r ^ δ := by ring
      _ ≤ (max C 0 + ∑ q : Fin (n + 1), max (Bl q) 0) * r ^ E * r ^ δ := by
          gcongr
          linarith [Finset.sum_nonneg (fun q (_ : q ∈ Finset.univ) => le_max_right (Bl q) 0)]
  ·
    rw [min_eq_left hr1.le, Real.one_rpow, mul_one]
    calc _ ≤ Bl p * r ^ E := hlarge
      _ ≤ max (Bl p) 0 * r ^ E := by gcongr; exact le_max_left _ _
      _ ≤ (max C 0 + ∑ q : Fin (n + 1), max (Bl q) 0) * r ^ E := by
          gcongr; linarith [le_max_right C 0]
end Su2Core

open DCFN in

theorem exists_norm_whittakerCoefficient_diagOne_le_min_norm_rpow_of_isComplex_of_su2String
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (ξ : (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (w : InfinitePlace K) (hw : w.IsComplex)
    (n : ℕ) (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ))
    (hxc : ∀ p, Continuous (x p))
    (hxG : ∀ p (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x p (globalPoints (𝓞 K) K γ * g) = x p g)
    (hxZ : ∀ p (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      x p (centralScalar (𝓞 K) K z * g) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x p g)
    (hreg : ∀ p (l : List ArchDirComplex),
      IsArchSmoothAtComplex hw (l.foldr (archDerivAtComplex hw) (x p)) ∧ Continuous (l.foldr (archDerivAtComplex hw) (x p)))
    (hwt : ∀ p : Fin (n + 1), HasCircleWeightAt hw ((n : ℤ) - 2 * (p : ℕ)) (x p))
    (E₁ E₂ : ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hE₁ : E₁ 0 = 1) (hE₂ : E₂ 0 = 1)
    (hE₁' : ∀ i j : Fin (n + 1), HasDerivAt (fun s : ℝ => E₁ s i j)
      (if (i : ℕ) = j + 1 then 1 else if (j : ℕ) = i + 1 then -((j : ℂ) * ((n : ℂ) + 1 - j)) else 0) 0)
    (hE₂' : ∀ i j : Fin (n + 1), HasDerivAt (fun s : ℝ => E₂ s i j)
      (if (i : ℕ) = j + 1 then Complex.I else if (j : ℕ) = i + 1 then Complex.I * ((j : ℂ) * ((n : ℂ) + 1 - j)) else 0) 0)
    (hK₁ : ∀ (p : Fin (n + 1)) (s : ℝ) (g : AdelicGL2 (𝓞 K) K),
      x p (g * archComplexLiftAt hw !![(Real.cos s : ℂ), -(Real.sin s : ℂ); (Real.sin s : ℂ), (Real.cos s : ℂ)]) = ∑ p' : Fin (n + 1), E₁ s p' p * x p' g)
    (hK₂ : ∀ (p : Fin (n + 1)) (s : ℝ) (g : AdelicGL2 (𝓞 K) K),
      x p (g * archComplexLiftAt hw !![(Real.cos s : ℂ), (Real.sin s : ℂ) * Complex.I; (Real.sin s : ℂ) * Complex.I, (Real.cos s : ℂ)]) = ∑ p' : Fin (n + 1), E₂ s p' p * x p' g)
    (lam lam' : ℂ)
    (hcas : ∀ p, archCasimirAtComplex hw (x p) = lam • x p ∧ archCasimirBarAtComplex hw (x p) = lam' • x p)
    (hgr : ∀ p, ∃ C₀ : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (x p) 1 g‖ ≤ C₀ * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2))
    (hU : lam' = (starRingEnd ℂ) lam)
    (hR : lam' = lam → lam.im = 0 → n = 0 ∨ -(((n : ℝ) ^ 2 + 4 * (n : ℝ)) / 16) < lam.re)
    (hZ : lam = 0 → n = 0 → ∀ (g : AdelicGL2 (𝓞 K) K) (h : GL (Fin 2) ℂ),
      Matrix.GeneralLinearGroup.det h = 1 → x 0 (g * archComplexGLAt hw h) = x 0 g)
    (b : (AdeleRing (𝓞 K) K)ˣ) (hb : ((b : AdeleRing (𝓞 K) K)).2 = 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ p : Fin (n + 1),
      ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
        (∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w') →
        ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (x p) 1
              (diagOne a)‖ ≤
          C * ‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) * (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 w‖) ^ δ
  := by
  have hW := DCFN.hasDerivAt_W_string D hw b x hxc hreg
  have hCas := IFC.hCas_string D hw b x hxc hreg lam lam' hcas
  have hK := KType.hK_of_string K D hw (g0 w b) n x hxc E₁ E₂ hK₁ hK₂

  have hI := AutomorphicForm.gl2Complex_whittaker_system_of_casimir_pair_of_unipotent_covariant_of_circleWeight_of_ktype n
    (fun (p : Fin (n + 1)) (h : GL (Fin 2) ℂ) => whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g0 w b * archComplexGLAt hw h))
    1 lam lam'
    (fun (p : Fin (n + 1)) (d : ArchDirComplex) (h : GL (Fin 2) ℂ) =>
      whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw d (x p)) 1 (g0 w b * archComplexGLAt hw h))
    (fun (p : Fin (n + 1)) (d' d : ArchDirComplex) (h : GL (Fin 2) ℂ) =>
      whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw d' (archDerivAtComplex hw d (x p))) 1 (g0 w b * archComplexGLAt hw h))
    hW.1 (fun p d d' h => hW.2 p d' d h) hCas.1 hCas.2
    (IFC.hN_string D hw b x hxG (IFC.g0_comm hw b)) (IFC.hM_string D hw b x hwt)
    E₁ E₂ hE₁ hE₂ hE₁' hE₂' hK.1 hK.2

  set f : ℕ → ℝ → ℂ := fun m y => if hm : m < n + 1 then
      whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x ⟨m, hm⟩) 1 (g0 w b * archComplexGLAt hw (splitTorusGL2Complex ((Real.log y / 2 : ℝ) : ℂ)))
    else 0 with hfdef
  have hsys :
    ∀ p : Fin (n + 1),
      DifferentiableOn ℝ (f p) (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv (f p)) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        ((y : ℂ) ^ 2 * deriv (deriv (f p)) y + (((n : ℂ) - 2 * (p : ℕ)) - 1) * (y : ℂ) * deriv (f p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) - 4) / 4 + 4 * lam -
                16 * (Real.pi : ℂ) ^ 2 * ((‖(1 : ℂ)‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * f p y +
            8 * (Real.pi : ℂ) * Complex.I * (1 : ℂ) * (y : ℂ) * f ((p : ℕ) + 1) y = 0) ∧
        ((y : ℂ) ^ 2 * deriv (deriv (f p)) y - (((n : ℂ) - 2 * (p : ℕ)) + 1) * (y : ℂ) * deriv (f p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) + 4) / 4 + 4 * lam' -
                16 * (Real.pi : ℂ) ^ 2 * ((‖(1 : ℂ)‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * f p y -
            8 * (Real.pi : ℂ) * Complex.I * (starRingEnd ℂ) (1 : ℂ) * ((p : ℕ) * ((n : ℂ) + 1 - (p : ℕ))) * (y : ℂ) *
              f ((p : ℕ) - 1) y = 0) := hI
  have hf : ∀ (p : Fin (n + 1)) (y : ℝ), f p y =
      whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g0 w b * archComplexGLAt hw (splitTorusGL2Complex ((Real.log y / 2 : ℝ) : ℂ))) := by
    intro p y
    simp only [hfdef, dite_eq_left p.isLt, Fin.eta]
  have hfn : ∀ y : ℝ, f (n + 1) y = 0 := fun y => by simp [hfdef]
  have hZ0 : lam = 0 → n = 0 → ∀ y : ℝ, 0 < y → f 0 y = 0 := by
    intro hl hn0 y _
    have h0 : f 0 y = whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x 0) 1 (g0 w b * archComplexGLAt hw (splitTorusGL2Complex ((Real.log y / 2 : ℝ) : ℂ))) := by
      have := hf 0 y
      simpa using this
    rw [h0]
    exact IFC.W_eq_zero_of_sl2_invariant D hw b (x 0) (hxG 0) (hZ hl hn0) (IFC.g0_comm hw b) _
  exact Su2Core.core D ξ w₀ hξ hw x hxZ hwt hgr lam lam' hU hR b hb f hf hsys hfn hZ0


end AutomorphicForm

end
