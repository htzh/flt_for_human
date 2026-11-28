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
spec-pin: Theorems/Thm_AlgebraicCurve_Pic0_exists_principal_geometricCycle_of_lift_correspondence_eq_zero.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Pic0_exists_principal_geometricCycle_of_lift_correspondence_eq_zero.lean
-/
import FLTForHuman.AlgebraicCurve.ConstantReductionCorrespondence
import FLTForHuman.AlgebraicCurve.Genus.PlaceReductionRiemannRoch
import FLTForHuman.AlgebraicCurve.Pic0.BaseChange
import Mathlib.Tactic
import FLTForHuman.AlgebraicCurve.IsCurveOver.BaseChangeCorrespondence
import FLTForHuman.AlgebraicCurve.Place.ConstantFieldExtension
import FLTForHuman.AlgebraicCurve.IsCurveOver.ConstantFieldExtension

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

/-
## SET-AF111 insertion: AlgebraicCurve.Pic0.exists_principal_geometricCycle_of_lift_correspondence_eq_zero

A vanishing base-changed lift makes the geometric cycle principal.

`AlgebraicCurve.Pic0.exists_principal_geometricCycle_of_lift_correspondence_eq_zero` (286 pin lines): given
the base-changed correspondences' lifts vanish, a geometric cycle becomes principal — the `Pic0`-side
conclusion of the descent row SET-AF110D landed in this module, and the consumer of the constant-field
extension correspondence layer.

**This row is a consumer of AF110D's row and of the constant-field-extension machinery; the module was not
built to hold it, so treat the import direction as the first check** (WO-C says what to do if a premise is
above the home).

## The declaration surface — 2 of the 7 pin rows are imported, not re-proved

The pin's `S_` file is a surface of **7 declarations**, all public: the headline `solution` `:92` and six
helpers (`lift_equivariant` `:26`, `Centred` `:42`, `eq_zero_of_valuation_algebraMap_lt_one` `:45`,
`Centred.eq` `:63`, `Centred.mem` `:70`, `not_mem_of_ord_neg` `:78`). Two are imported:

| pin row | imported from |
|---|---|
| `lift_equivariant` | `AlgebraicCurve.Pic0.BaseChange.lift_equivariant` (byte-identical, this module already uses it) |
| `eq_zero_of_valuation_algebraMap_lt_one` | `AlgebraicCurve.CentredPlaceRigidity.eq_zero_of_valuation_algebraMap_lt_one` (`Place/ConstantFieldExtension.lean`; the pin's binder names `{a} (ha)` are the port's `{c} (hc)` — `check_port`'s `alpha_stmt` tier accepts, and the engine diff reads it `ALPHA`) |

The other four are declared here, in the module's namespace `AlgebraicCurve.Pic0` (the pin's generated
label `GeometricCycleAssembly` dropped). `Centred` and `Centred.eq` are **not** the port's
`CentredPlaceRigidity` block: that block states the centredness hypothesis *inline*
(`centre_unique`) and has no `Centred` predicate at all, so the pin's `def` is new and `Centred.eq` is its
`centre_unique` in the pin's statement shape.

**Import direction (the check WO-C asked for): passes.** All three added imports elaborate, and every new
premise is in the module's import closure: `Place.existsUnique_valuation_sub_lt_one_of_constantFieldExtension`
and `Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed` (`Place/ConstantFieldExtension.lean`),
`exists_baseChange_correspondence_of_constantFieldExtension` (`IsCurveOver/BaseChangeCorrespondence.lean`),
`linearIndependent_of_constantFieldExtension` (`IsCurveOver/ConstantFieldExtension.lean`), and the module's
own `Pic0.freeAlgebra_lift_baseChange_correspondence_eq_zero`. No module below the home was needed.

## What the transcription measured

* **Statement text is verbatim**: `check_port` **6 ok / 0 mismatch / 0 missing / 0 own** (the four new
  helpers included — `Centred` matches the pin's `def` row, `Centred.eq`/`Centred.mem` its dotted rows).
* **Engine diff** (`port_omissions.py`, the module's two wires): **16 pin public declarations — 6 declared,
  8 imported (1 alpha only: `eq_zero_of_valuation_algebraMap_lt_one`), 2 folded (`solution` ×2),
  0 MISSING**.
* **Proof-text drifts** (three, all mechanical):
  1. the pin's `open AlgebraicCurve.GeometricCycleAssembly in` becomes
     `open AlgebraicCurve.Pic0.BaseChange AlgebraicCurve.Pic0 in` (the blocks' homes);
  2. the pin's `if_pos` / `if_neg` / `dif_pos` / `dif_neg` are deprecated in this mathlib and are written
     `ite_eq_left` / `ite_eq_right` / `dite_eq_left` / `dite_eq_right`;
  3. `haveI := hx₀fin` is the pin's, and `linter.style.haveILetI` fires on it (the goal at that point is a
     proposition); silenced **declaration-scoped** with `set_option linter.style.haveILetI false in` on this
     theorem only — no module-wide silencing, no `maxHeartbeats`.
* **Axioms**: all 6 public declarations read `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.
* **Dedup** (`dedup.py --within --module '*Pic0/BaseChangeDescent*'`): **0 duplicate clusters**.
* **`move_dead --dry-run`**: **0 declarations, 0 lines**.
* **The heartbeat probe** (recorded, never installed). Downward ladder, one run per value:

  | cap | 40000 | 20000 | 10000 | 5000 | 1000 |
  |---|---|---|---|---|---|
  | module | fail | fail | fail | fail | fail |
  | first failure | `whnf` in this row's statement (`:291`) | `simp` in `freeAlgebra_lift_baseChange_correspondence_eq_zero` (`:167`) | `whnf` in that row's statement (`:90`) | `isDefEq` (`:121`) | `whnf` (`:101`) |

  The module **passes at the 200 k edit-loop cap**; it is the insertion that pushed it over 40000 (the row
  already in this module passed 40000 on its own, see above — both rows are one module therefore one cap).
  **Module floor** (every theorem proof `sorry`, one run): passes at **40000**, the first cap at which the
  real module fails — so the cost is in the proofs, not in the types. No cap is installed.
-/
namespace AlgebraicCurve.Pic0

section GeometricCycle

variable {K F E FE : Type*} [Field K] [Field F] [Algebra K F] [Field E] [Field FE]
  [Algebra K E] [Algebra E FE] [Algebra F FE]

/-- A place of the constant extension `FE / E` is *centred* at `e : F →ₐ[K] E` when every
`f : F` is represented to first order by `e f`.  The pin's
`GeometricCycleAssembly.Centred`. -/
def Centred (P : Place E FE) (e : F →ₐ[K] E) : Prop :=
  ∀ f : F, P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (e f)) < 1

/-- The centre of a place is unique: the pin's `Centred.eq`, the port's
`CentredPlaceRigidity.centre_unique` in the pin's predicate shape. -/
theorem Centred.eq {P : Place E FE} {e e' : F →ₐ[K] E} (he : Centred P e) (he' : Centred P e') :
    e = e' :=
  AlgebraicCurve.CentredPlaceRigidity.centre_unique P he he'

/-- A centred place contains the image of `F`: the pin's `Centred.mem`. -/
theorem Centred.mem {P : Place E FE} {e : F →ₐ[K] E} (he : Centred P e) (f : F) :
    algebraMap F FE f ∈ P.toValuationSubring := by
  have h1 : algebraMap F FE f - algebraMap E FE (e f) ∈ P.toValuationSubring :=
    (ValuationSubring.valuation_le_one_iff _ _).mp (he f).le
  simpa using add_mem h1 (P.algebraMap_mem' (e f))

/-- A place of negative order on `f ≠ 0` does not contain it: the pin's
`GeometricCycleAssembly.not_mem_of_ord_neg`. -/
theorem not_mem_of_ord_neg {k L : Type*} [Field k] [Field L] [Algebra k L] (v : Place k L)
    {f : L} (hf : f ≠ 0) (h : v.ord f < 0) : f ∉ v.toValuationSubring := by
  intro hmem
  have hinv : f⁻¹ ∈ v.toValuationSubring :=
    v.mem_toValuationSubring_of_ord_nonneg_alt (inv_ne_zero hf) (by rw [Place.ord_inv]; omega)
  let u : v.toValuationSubringˣ :=
    ⟨⟨f, hmem⟩, ⟨f⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hf), Subtype.ext (inv_mul_cancel₀ hf)⟩
  have hu := v.ord_coe_unit u
  change v.ord f = 0 at hu
  omega

end GeometricCycle

end AlgebraicCurve.Pic0

open AlgebraicCurve.Pic0.BaseChange AlgebraicCurve.Pic0 in
set_option linter.style.haveILetI false in
theorem AlgebraicCurve.Pic0.exists_principal_geometricCycle_of_lift_correspondence_eq_zero
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
    (η : F →ₐ[K] E) :
    ∃ (g : FE) (_ : g ≠ 0) (S : Finset (Place E FE)) (y : Place E FE → (F →ₐ[K] E)),
      (∀ P ∈ S, ∀ f : F,
        P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (y P f)) < 1) ∧
      (∀ P : Place E FE, P ∉ S → P.ord g ≠ 0 →
        ∃ f : F, algebraMap F FE f ∉ P.toValuationSubring) ∧
      (∑ P ∈ S, Finsupp.single (y P) (P.ord g) : (F →ₐ[K] E) →₀ ℤ) =
        FreeAlgebra.lift ℤ (fun i => (Finsupp.liftAddHom fun e : F →ₐ[K] E =>
          zmultiplesHom ((F →ₐ[K] E) →₀ ℤ)
            (∑ᶠ σ ∈ {σ : F' i →ₐ[K] E | σ.comp (φ i) = e},
              Finsupp.single (σ.comp (ψ i)) (1 : ℤ))).toIntLinearMap) p (Finsupp.single η 1) :=
  by
  classical

  obtain ⟨hC1, hC1b⟩ :=
    Place.existsUnique_valuation_sub_lt_one_of_constantFieldExtension K F hfg E FE hfgE hgen

  choose F'E instF instAE instAF' instAK instTE instTF' instC φE ψE hφE hψE hFIE hfinE hNE
    hfgE' hgen' hφcomm hψcomm hfib hcen hrat using
    fun i => exists_baseChange_correspondence_of_constantFieldExtension K F hfg (F' i) (φ i) (ψ i)
      (hφ i) (hψ i) (hFI i) (hfin i) (hN i) E FE hfgE hgen

  have hpE := Pic0.freeAlgebra_lift_baseChange_correspondence_eq_zero K F hfg F' φ ψ hφ hψ hFI
    hfin hN p hp E FE hfgE hgen F'E hfgE' hgen' φE ψE hφcomm hψcomm hφE hψE hFIE hfinE hNE

  set TZ : ι → (Divisor.degZero (K := E) (F := FE) →+ Divisor.degZero (K := E) (F := FE)) :=
    fun i => Pic0.degZeroCorrespondence (φE i) (ψE i) (hφE i) (hψE i) (hFIE i) with hTZ
  set TD : ι → (Divisor E FE →+ Divisor E FE) :=
    fun i => Divisor.correspondence (φE i) (ψE i) (hφE i) (hψE i) with hTD
  set Z : ι → (F →ₐ[K] E) → ((F →ₐ[K] E) →₀ ℤ) := fun i e =>
    ∑ᶠ σ ∈ {σ : F' i →ₐ[K] E | σ.comp (φ i) = e}, Finsupp.single (σ.comp (ψ i)) (1 : ℤ) with hZ
  set TA : ι → (((F →ₐ[K] E) →₀ ℤ) →+ ((F →ₐ[K] E) →₀ ℤ)) := fun i =>
    Finsupp.liftAddHom fun e : F →ₐ[K] E => zmultiplesHom ((F →ₐ[K] E) →₀ ℤ) (Z i e) with hTA

  let ctrH : Place E FE → ℤ →+ ((F →ₐ[K] E) →₀ ℤ) := fun Q =>
    if h : ∃ e : F →ₐ[K] E, Centred Q e then Finsupp.singleAddHom h.choose else 0
  have ctrH_pos : ∀ {Q : Place E FE} (h : ∃ e : F →ₐ[K] E, Centred Q e),
      ctrH Q = Finsupp.singleAddHom h.choose := fun h => dite_eq_left h
  have ctrH_neg : ∀ {Q : Place E FE}, (¬ ∃ e : F →ₐ[K] E, Centred Q e) → ctrH Q = 0 :=
    fun h => dite_eq_right h
  set Φ : Divisor E FE →+ ((F →ₐ[K] E) →₀ ℤ) := Finsupp.liftAddHom ctrH with hΦdef

  have dichotomy : ∀ Q : Place E FE, (¬ ∃ e : F →ₐ[K] E, Centred Q e) →
      ∃ f : F, algebraMap F FE f ∉ Q.toValuationSubring := by
    intro Q hQ
    by_contra hall
    push Not at hall
    exact hQ (hC1b Q hall)
  have not_centred_of_rat : ∀ Q : Place E FE, (∃ f : F, algebraMap F FE f ∉ Q.toValuationSubring) →
      ¬ ∃ e : F →ₐ[K] E, Centred Q e := by
    rintro Q ⟨f, hf⟩ ⟨e, he⟩
    exact hf (he.mem f)

  have key : ∀ (i : ι) (P : Place E FE),
      Φ (TD i (Finsupp.single P 1)) = TA i (Φ (Finsupp.single P 1)) := by
    intro i P
    rw [hΦdef, Finsupp.liftAddHom_apply_single]
    by_cases hP : ∃ e : F →ₐ[K] E, Centred P e
    · have hc : Centred P hP.choose := hP.choose_spec
      rw [ctrH_pos hP, Finsupp.singleAddHom_apply, hTA, Finsupp.liftAddHom_apply_single,
        zmultiplesHom_apply, one_zsmul]
      ext e'
      obtain ⟨Q', hQ'c, hQ'u⟩ := hC1 e'
      rw [Finsupp.liftAddHom_apply, Finsupp.sum, Finsupp.finsetSum_apply,
        Finset.sum_eq_single Q']
      · have hQ' : ∃ e : F →ₐ[K] E, Centred Q' e := ⟨e', hQ'c⟩
        have hce : hQ'.choose = e' := Centred.eq hQ'.choose_spec hQ'c
        rw [ctrH_pos hQ', hce, Finsupp.singleAddHom_apply, Finsupp.single_eq_same]
        exact hfib i P hP.choose hc Q' e' hQ'c
      · intro Q hQ hne
        by_cases hQc : ∃ e : F →ₐ[K] E, Centred Q e
        · rw [ctrH_pos hQc, Finsupp.singleAddHom_apply, Finsupp.single_apply, ite_eq_right]
          intro heq
          exact hne (hQ'u Q (heq ▸ hQc.choose_spec))
        · rw [ctrH_neg hQc, AddMonoidHom.zero_apply, Finsupp.zero_apply]
      · intro hnot
        rw [Finsupp.notMem_support_iff.mp hnot, map_zero, Finsupp.zero_apply]
    · have hrP := dichotomy P hP
      rw [ctrH_neg hP, AddMonoidHom.zero_apply, map_zero, Finsupp.liftAddHom_apply, Finsupp.sum]
      refine Finset.sum_eq_zero fun Q hQ => ?_
      have hQc := not_centred_of_rat Q (hrat i P hrP Q (Finsupp.mem_support_iff.mp hQ))
      rw [ctrH_neg hQc, AddMonoidHom.zero_apply]
  have hΦ : ∀ (i : ι) (D : Divisor E FE), Φ (TD i D) = TA i (Φ D) := by
    intro i
    suffices h : Φ.comp (TD i) = (TA i).comp Φ from fun D => DFunLike.congr_fun h D
    refine Finsupp.addHom_ext' fun P => AddMonoidHom.ext_int ?_
    simpa only [AddMonoidHom.comp_apply, Finsupp.singleAddHom_apply] using key i P

  obtain ⟨Pη, hPη, -⟩ := hC1 η
  have hPηc : ∃ e : F →ₐ[K] E, Centred Pη e := ⟨η, hPη⟩

  obtain ⟨x, hx, -⟩ := id hfg
  obtain ⟨x₀, hx₀, hx₀fin⟩ := id hfgE
  haveI := hx₀fin
  have hxne : x ≠ 0 := fun h => hx (h ▸ isAlgebraic_zero)
  have hli : LinearIndependent K ![(1 : F), x] := by
    refine LinearIndependent.pair_iff.2 fun s t hst => ?_
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hst
      exact ⟨hst, rfl⟩
    · exfalso
      apply hx
      have ht' : algebraMap K F t ≠ 0 := (map_ne_zero _).2 ht
      have hx' : x = algebraMap K F (-s / t) := by
        rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
        rw [map_div₀, map_neg, eq_div_iff ht', mul_comm]
        exact eq_neg_of_add_eq_zero_right hst
      rw [hx']
      exact isAlgebraic_algebraMap _
  have hxE : algebraMap F FE x ∉ (algebraMap E FE).range := by
    have hli' := linearIndependent_of_constantFieldExtension K F E FE hfg hfgE hgen hli
    have h2 : LinearIndependent E ![algebraMap F FE 1, algebraMap F FE x] := by
      convert hli' using 1
      ext j
      fin_cases j <;> rfl
    rw [LinearIndependent.pair_iff] at h2
    rintro ⟨c, hc⟩
    have := h2 c (-1) (by rw [map_one, ← hc, Algebra.smul_def, mul_one, neg_one_smul, add_neg_cancel])
    exact absurd this.2 (by norm_num)
  have hcE' : ¬ ∀ v : Place E FE, v.ord (algebraMap F FE x) = 0 := fun h =>
    hxE (Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed x₀ hx₀ h)
  push Not at hcE'
  obtain ⟨cE, hcE⟩ := hcE'
  have hxEne : algebraMap F FE x ≠ 0 := (map_ne_zero _).2 hxne
  have hcErat : ∃ f : F, algebraMap F FE f ∉ cE.toValuationSubring := by
    rcases lt_or_gt_of_ne hcE with hlt | hgt
    · exact ⟨x, not_mem_of_ord_neg cE hxEne hlt⟩
    · refine ⟨x⁻¹, ?_⟩
      rw [map_inv₀]
      exact not_mem_of_ord_neg cE (inv_ne_zero hxEne) (by rw [Place.ord_inv]; omega)
  have hcEnc : ¬ ∃ e : F →ₐ[K] E, Centred cE e := not_centred_of_rat cE hcErat

  have hdeg1 : ∀ P : Place E FE, Divisor.degree (Finsupp.single P (1 : ℤ)) = 1 := fun P => by
    rw [Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed P]; simp
  let D0 : Divisor.degZero (K := E) (F := FE) :=
    ⟨Finsupp.single Pη 1 - Finsupp.single cE 1, by
      rw [Divisor.mem_degZero, map_sub, hdeg1, hdeg1, sub_self]⟩
  have hΦD0 : Φ (D0 : Divisor E FE) = Finsupp.single η 1 := by
    show Φ (Finsupp.single Pη 1 - Finsupp.single cE 1) = Finsupp.single η 1
    rw [map_sub, hΦdef, Finsupp.liftAddHom_apply_single, Finsupp.liftAddHom_apply_single,
      ctrH_pos hPηc, ctrH_neg hcEnc, Centred.eq hPηc.choose_spec hPη,
      Finsupp.singleAddHom_apply, AddMonoidHom.zero_apply, sub_zero]

  have hmk := lift_equivariant
    (QuotientAddGroup.mk' ((Divisor.principal (K := E) (F := FE)).addSubgroupOf Divisor.degZero))
    TZ (fun i => Pic0.correspondence (φE i) (ψE i) (hφE i) (hψE i) (hFIE i) (hfinE i) (hNE i))
    (fun i D => rfl) p D0
  rw [hpE, LinearMap.zero_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff,
    AddSubgroup.mem_addSubgroupOf, Divisor.mem_principal] at hmk
  obtain ⟨g, hg0, hdiv⟩ := hmk

  have hmain := lift_equivariant (Φ.comp (Divisor.degZero (K := E) (F := FE)).subtype) TZ TA
    (fun i D => hΦ i (D : Divisor E FE)) p D0
  simp only [AddMonoidHom.comp_apply, AddSubgroup.subtype_apply] at hmain
  rw [hΦD0] at hmain

  set Dg : Divisor E FE :=
    ((FreeAlgebra.lift ℤ (fun i => (TZ i).toIntLinearMap) p D0 :
      Divisor.degZero (K := E) (F := FE)) : Divisor E FE) with hDg
  have hDgv : ∀ v : Place E FE, Dg v = v.ord g := hdiv
  let y : Place E FE → (F →ₐ[K] E) := fun Q =>
    if h : ∃ e : F →ₐ[K] E, Centred Q e then h.choose else η
  refine ⟨g, hg0, Dg.support.filter (fun Q => ∃ e : F →ₐ[K] E, Centred Q e), y, ?_, ?_, ?_⟩
  · intro P hP
    obtain ⟨-, hPc⟩ := Finset.mem_filter.mp hP
    show Centred P (y P)
    simp only [y, dite_eq_left hPc]
    exact hPc.choose_spec
  · intro P hPS hPg
    refine dichotomy P fun hPc => hPS ?_
    exact Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr (by rwa [hDgv]), hPc⟩
  · rw [← hmain, hΦdef, Finsupp.liftAddHom_apply, Finsupp.sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun Q _ => ?_
    by_cases hQc : ∃ e : F →ₐ[K] E, Centred Q e
    · rw [ite_eq_left hQc, ctrH_pos hQc, Finsupp.singleAddHom_apply, hDgv]
      simp only [y, dite_eq_left hQc]
    · rw [ite_eq_right hQc, ctrH_neg hQc, AddMonoidHom.zero_apply]
