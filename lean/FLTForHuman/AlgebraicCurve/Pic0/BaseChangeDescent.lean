/-
The correspondence's base-changed lift vanishes, so the correspondence does.

`AlgebraicCurve.Pic0.freeAlgebra_lift_baseChange_correspondence_eq_zero` (170 pin lines): if the free
algebra lift of the correspondences' `Pic0` classes is zero *after* base change along `E → FE` for every
data set that makes the extended correspondence defined, then it is zero before. It is the **descent**
form of `Pic0/BaseChange.lean`'s row (which lifts a vanishing correspondence *to* the base change), and
the two are the two directions of the base-change dictionary the D–S route's `Pic0` step needs.

Its premises are `ConstantReductionCorrespondence` and SET-AF109D's
`Genus/PlaceReductionRiemannRoch` (the divisor-descent row), so the home must sit above both; the
subject is `Pic0` + base change, which is `Pic0/` — hence a new module in that directory rather than an
insertion into the `Genus/` module that happens to be in its premise set.

## The rows

* `AlgebraicCurve.Pic0.freeAlgebra_lift_baseChange_correspondence_eq_zero` — 170 pin `S_` lines.

## The declaration surface — 6 of the 7 pin rows are imported, not re-proved

The pin's `S_` file is a surface of **7 declarations**, all public: the six-row
`BaseChangeRigidityAssembly` block (`lift_equivariant` `:20`, `degree_eq_sum` `:35`,
`degree_mapDomain` `:46`, `mk_eq_zero_iff` `:56`, `mkHom` `:60`, `mkHom_apply` `:63`) and the headline
`solution` `:72`. The six are **already public in `AlgebraicCurve/Pic0/BaseChange.lean`** under the
subject namespace `AlgebraicCurve.Pic0.BaseChange`, so this module imports them and re-proves none of
them — the substitution pass measured all six **byte-identical** (`port_advise`: 8 declarations already
in the port, 8 tier 1, 8 importable, 0 suspect):

| pin row | imported from |
|---|---|
| `lift_equivariant` | `AlgebraicCurve.Pic0.BaseChange.lift_equivariant` |
| `degree_eq_sum` | `AlgebraicCurve.Pic0.BaseChange.degree_eq_sum` |
| `degree_mapDomain` | `AlgebraicCurve.Pic0.BaseChange.degree_mapDomain` |
| `mk_eq_zero_iff` | `AlgebraicCurve.Pic0.BaseChange.mk_eq_zero_iff` |
| `mkHom` | `AlgebraicCurve.Pic0.BaseChange.mkHom` |
| `mkHom_apply` | `AlgebraicCurve.Pic0.BaseChange.mkHom_apply` |

The module therefore declares **1 new declaration**; the engine diff reads "pin sources 2, pin
declarations 8, module declarations 1, **1 by hash**, 0 unaccounted" for the module alone, and **7/7 by
statement hash** once the six imported rows are counted at their `Pic0/BaseChange.lean` home. The pin has
**no `private` declaration** here, so there is no surface-gate question.

The proof is the pin's: `Pic0.mk_surjective` reduces to a degree-zero divisor `D`, `lift_equivariant`
descends the `Pic0` lift to the divisor lift on `Divisor.degZero` and then to `Divisor` itself,
`degree_mapDomain` keeps `Finsupp.mapDomain r D` in `Divisor.degZero`, and
`Divisor.isPrincipal_of_forall_isPrincipal_mapDomain_placeReduction` (SET-AF109D's row, imported) closes
it with the base-change correspondence identity
`Divisor.mapDomain_placeReduction_correspondence` (AF106C's row, imported).

## What the transcription measured

* **Statement text is verbatim** (`check_port` 1 `ok`). Two proof-text-only drifts:
  1. the pin's `open AlgebraicCurve.BaseChangeRigidityAssembly in` becomes
     `open AlgebraicCurve.Pic0.BaseChange in` — the block's home, per the port's naming policy;
  2. the unused `with hTPE` / `with hDK` binder names of the two `set`/`let` introductions are dropped.
* **Dedup** (`dedup.py --within`): **0 duplicate clusters**. **`move_dead --dry-run`**: `0 declarations,
  0 lines`.
* **Axioms**: the headline reads `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.
* **The heartbeat probe** (recorded, never installed). Downward ladder, one run per value:

  | cap | 40000 | 20000 | 10000 | 5000 | 1000 |
  |---|---|---|---|---|---|
  | module | **pass** | fail | fail | fail | fail |
  | first failure | — | `simp` at the `Divisor.degZero` `subtype` step | `whnf` in the statement | `isDefEq` in the statement | `whnf` in the statement |

  **Module floor** (the headline proof `sorry`, one run): passes at **20000**, the lowest cap at which
  the real module fails — so the cost is in the proof, not in the types. No cap is installed.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Pic0_freeAlgebra_lift_baseChange_correspondence_eq_zero.lean>

spec-pin: Theorems/Thm_AlgebraicCurve_Pic0_freeAlgebra_lift_baseChange_correspondence_eq_zero.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Pic0_freeAlgebra_lift_baseChange_correspondence_eq_zero.lean
-/
import FLTForHuman.AlgebraicCurve.ConstantReductionCorrespondence
import FLTForHuman.AlgebraicCurve.Genus.PlaceReductionRiemannRoch
import FLTForHuman.AlgebraicCurve.Pic0.BaseChange
import Mathlib.Tactic

set_option autoImplicit false

open AlgebraicCurve

open AlgebraicCurve.Pic0.BaseChange in
theorem AlgebraicCurve.Pic0.freeAlgebra_lift_baseChange_correspondence_eq_zero
    (K F : Type*) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K] [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    {ι : Type*} (F' : ι → Type*) [∀ i, Field (F' i)] [∀ i, Algebra K (F' i)]
    [∀ i, HasPrincipalDivisors K (F' i)]
    (φ ψ : ∀ i, F →ₐ[K] F' i)
    (hφ : ∀ i, (φ i).toRingHom.IsIntegral) (hψ : ∀ i, (ψ i).toRingHom.IsIntegral)
    (hFI : ∀ i, FundamentalIdentityAlong K (φ i) (hφ i))
    (hfin : ∀ i, FiniteAlong K (ψ i)) (hN : ∀ i, NormFormulaAlong K (ψ i) (hfin i))
    (p : FreeAlgebra ℤ ι)
    (hp : FreeAlgebra.lift ℤ (fun i =>
      (Pic0.correspondence (φ i) (ψ i) (hφ i) (hψ i) (hFI i) (hfin i) (hN i)).toIntLinearMap) p = 0)
    (E FE : Type*) [Field E] [Field FE] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
    [IsScalarTower K E FE] [IsScalarTower K F FE] [IsAlgClosed E] [IsCurveOver E FE]
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (F'E : ι → Type*) [∀ i, Field (F'E i)] [∀ i, Algebra E (F'E i)] [∀ i, Algebra (F' i) (F'E i)]
    [∀ i, Algebra K (F'E i)] [∀ i, IsScalarTower K E (F'E i)] [∀ i, IsScalarTower K (F' i) (F'E i)]
    [∀ i, IsCurveOver E (F'E i)]
    (hfgE' : ∀ i, ∃ x' : F'E i, Transcendental E x' ∧
      FiniteDimensional (IntermediateField.adjoin E ({x'} : Set (F'E i))) (F'E i))
    (hgen' : ∀ i, IntermediateField.adjoin E (Set.range (algebraMap (F' i) (F'E i))) = ⊤)
    (φE ψE : ∀ i, FE →ₐ[E] F'E i)
    (hφcomm : ∀ i (f : F), φE i (algebraMap F FE f) = algebraMap (F' i) (F'E i) (φ i f))
    (hψcomm : ∀ i (f : F), ψE i (algebraMap F FE f) = algebraMap (F' i) (F'E i) (ψ i f))
    (hφE : ∀ i, (φE i).toRingHom.IsIntegral) (hψE : ∀ i, (ψE i).toRingHom.IsIntegral)
    (hFIE : ∀ i, FundamentalIdentityAlong E (φE i) (hφE i))
    (hfinE : ∀ i, FiniteAlong E (ψE i)) (hNE : ∀ i, NormFormulaAlong E (ψE i) (hfinE i)) :
    FreeAlgebra.lift ℤ (fun i =>
      (Pic0.correspondence (φE i) (ψE i) (hφE i) (hψE i) (hFIE i) (hfinE i) (hNE i)).toIntLinearMap)
        p = 0 := by
  classical

  set TPE : ι → Pic0 E FE →+ Pic0 E FE := fun i =>
    Pic0.correspondence (φE i) (ψE i) (hφE i) (hψE i) (hFIE i) (hfinE i) (hNE i)
  let TZE : ι → Divisor.degZero (K := E) (F := FE) →+ Divisor.degZero (K := E) (F := FE) :=
    fun i => Pic0.degZeroCorrespondence (φE i) (ψE i) (hφE i) (hψE i) (hFIE i)
  let TDE : ι → Divisor E FE →+ Divisor E FE :=
    fun i => Divisor.correspondence (φE i) (ψE i) (hφE i) (hψE i)
  let TPK : ι → Pic0 K F →+ Pic0 K F := fun i =>
    Pic0.correspondence (φ i) (ψ i) (hφ i) (hψ i) (hFI i) (hfin i) (hN i)
  let TZK : ι → Divisor.degZero (K := K) (F := F) →+ Divisor.degZero (K := K) (F := F) :=
    fun i => Pic0.degZeroCorrespondence (φ i) (ψ i) (hφ i) (hψ i) (hFI i)
  let TDK : ι → Divisor K F →+ Divisor K F :=
    fun i => Divisor.correspondence (φ i) (ψ i) (hφ i) (hψ i)

  apply LinearMap.ext
  intro c
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective c
  rw [LinearMap.zero_apply]

  have h1 : FreeAlgebra.lift ℤ (fun i => (TPE i).toIntLinearMap) p (Pic0.mk D) =
      Pic0.mk (FreeAlgebra.lift ℤ (fun i => (TZE i).toIntLinearMap) p D) := by
    have := lift_equivariant (mkHom (k := E) (L := FE)) TZE TPE (fun i a => rfl) p D
    simpa only [mkHom_apply] using this.symm
  have h2 : ((FreeAlgebra.lift ℤ (fun i => (TZE i).toIntLinearMap) p D :
      Divisor.degZero (K := E) (F := FE)) : Divisor E FE) =
      FreeAlgebra.lift ℤ (fun i => (TDE i).toIntLinearMap) p (D : Divisor E FE) :=
    lift_equivariant (Divisor.degZero (K := E) (F := FE)).subtype TZE TDE (fun i a => rfl) p D
  rw [h1, mk_eq_zero_iff, h2]

  have hdeg0 : Divisor.degree
      (FreeAlgebra.lift ℤ (fun i => (TDE i).toIntLinearMap) p (D : Divisor E FE)) = 0 := by
    rw [← h2]; exact (FreeAlgebra.lift ℤ (fun i => (TZE i).toIntLinearMap) p D).2

  refine AlgebraicCurve.Divisor.isPrincipal_of_forall_isPrincipal_mapDomain_placeReduction
    K F E FE hfg hfgE hgen _ hdeg0 ?_
  intro A r hKA hArat hr

  have h3 : Finsupp.mapDomain r
      (FreeAlgebra.lift ℤ (fun i => (TDE i).toIntLinearMap) p (D : Divisor E FE)) =
      FreeAlgebra.lift ℤ (fun i => (TDK i).toIntLinearMap) p
        (Finsupp.mapDomain r (D : Divisor E FE)) := by
    have := lift_equivariant (Finsupp.mapDomain.addMonoidHom r) TDE TDK (fun i D' => ?_) p D
    · simpa only [Finsupp.mapDomain.addMonoidHom_apply] using this
    · simp only [Finsupp.mapDomain.addMonoidHom_apply]
      exact AlgebraicCurve.Divisor.mapDomain_placeReduction_correspondence K F hfg (F' i)
        (φ i) (ψ i) (hφ i) (hψ i) (hFI i) (hfin i) (hN i) E FE hfgE hgen (F'E i) (hfgE' i)
        (hgen' i) (φE i) (ψE i) (hφcomm i) (hψcomm i) (hφE i) (hψE i) (hFIE i) (hfinE i)
        (hNE i) A hKA hArat r hr D'
  rw [h3]

  have hdegK : Finsupp.mapDomain r (D : Divisor E FE) ∈ Divisor.degZero (K := K) (F := F) := by
    rw [Divisor.mem_degZero, degree_mapDomain]; exact D.2
  set DK : Divisor.degZero (K := K) (F := F) := ⟨_, hdegK⟩
  have h4 : FreeAlgebra.lift ℤ (fun i => (TPK i).toIntLinearMap) p (Pic0.mk DK) =
      Pic0.mk (FreeAlgebra.lift ℤ (fun i => (TZK i).toIntLinearMap) p DK) := by
    have := lift_equivariant (mkHom (k := K) (L := F)) TZK TPK (fun i a => rfl) p DK
    simpa only [mkHom_apply] using this.symm
  have h5 : ((FreeAlgebra.lift ℤ (fun i => (TZK i).toIntLinearMap) p DK :
      Divisor.degZero (K := K) (F := F)) : Divisor K F) =
      FreeAlgebra.lift ℤ (fun i => (TDK i).toIntLinearMap) p (DK : Divisor K F) :=
    lift_equivariant (Divisor.degZero (K := K) (F := F)).subtype TZK TDK (fun i a => rfl) p DK
  have h6 : FreeAlgebra.lift ℤ (fun i => (TPK i).toIntLinearMap) p (Pic0.mk DK) = 0 := by
    rw [hp, LinearMap.zero_apply]
  rw [h4, mk_eq_zero_iff, h5] at h6
  exact h6

