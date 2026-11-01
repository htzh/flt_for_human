# WORKORDER SET9 — the reciprocity chain's proof bodies (RAT, REC, PAIR) and the ℓ-invariance row (ELL)

Scope: **one insertion** into `FLTForHuman/AlgebraicCurve/Place/DegreeOne.lean`, **one insertion**
into `FLTForHuman/AlgebraicCurve/IsCurveOver/ConstantFieldExtensionSpan.lean`, and **two new
modules** `FLTForHuman/AlgebraicCurve/WeilExchange/WeilReciprocity.lean` and
`FLTForHuman/AlgebraicCurve/Pic0/DivisorialPairing.lean`. Nothing else may be edited: no hub, no
`spec/` file, no `spec/decl_markers.tsv`, no `Pic0/WeilPairing.lean` (the manager's gate, already
landed). Part of SET 9, [SET-9.md](SET-9.md) §1 and §5.

## Nodes

| step | node (`AlgebraicCurve.` dropped) | silo | net | home |
|---|---|---:|---:|---|
| ELL | `ell_mapDomain_eq_of_constantFieldExtension_of_isAlgClosed` | 151 | 122 | append to `IsCurveOver/ConstantFieldExtensionSpan.lean` |
| RAT | `Place.isRational_of_isAlgClosed` | 119 | 103 | append to `Place/DegreeOne.lean` |
| REC | `weilReciprocity` | 100 | 70 | new `WeilExchange/WeilReciprocity.lean` |
| PAIR | `DivisorialWeilPairingData.toHom_injective_of_divisible` | 496 | 452 | new `Pic0/DivisorialPairing.lean` |

Pin at `aa2d8b3`, clone `~/proj/fermats-last-theorem`. Read every `S_` file **and** its
`Theorems/` wrapper: the statement is the wrapper's, the proof the `S_` file's.
`P2M/Sol/S_AlgebraicCurve_<stem>.lean`, `Theorems/Thm_AlgebraicCurve_<stem>.lean`, e.g.
<https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_isRational_of_isAlgClosed.lean>.

Do them **in the order of the table**: each one unblocks the next, and the first two are small. If
you run out of budget, the value is ELL → RAT → REC → PAIR.

## What the ground prep already gives you (do not rewrite it)

- **The carrier is landed.** `Pic0/WeilPairing.lean` now has `DivisorialWeilPairingData`,
  `exists_witness`, `exists_datum`, `exists_datum_pair`, `pair_ne_zero`, `pair_add_left`,
  `pair_mul_pair_swap`, `pair_zero_left`, `pair_zero_right`, `pair_swap_eq_inv`, `pair_add_right`,
  `toChar`, `toChar_apply`, `toHom`, `toHom_apply_apply`, and the datum layer at the pin's clean
  names (`WeilDatum.classLeft`, `classRight`, `coe_classLeft`, `coe_classRight`, `degZeroLeft`,
  `degZeroRight`, `coe_degZeroLeft`, `coe_degZeroRight`, `mk_mem_torsion`, `classLeft_symm`,
  `classRight_symm`, `classLeft_addLeft`, `classRight_addLeft`, `Divisor.evalFun_one`). It checks
  **38 ok / 0 mismatch / 0 missing / 2 own**. **Do not edit this module**; import it.
  Note the clean spellings: the pin's two `S_` files spell these `degZeroLeft_i`/`classLeft_i`, the
  port does not.
- **The module frames are in place.** The two new modules exist with their header prose, their
  imports and their `spec-pin:` lines; `Place/DegreeOne.lean` has the extra
  `import …Defs.PlaceEvaluation` and its two `spec-pin:` lines; the span module has its two
  `spec-pin:` lines. Fill the bodies; adjust an import only if a name genuinely needs more (never
  `import Mathlib`).
- **Already in the port, import them rather than restating:**
  * `Place/DegreeOne.lean` itself carries `Place.deg_eq_one_of_isAlgebraic_adjoin` and the private
    `surjective_algebraMap_residueField` / `valuation_aeval_eq_one`;
  * `Defs/PlaceEvaluation.lean`: `Place.isRational_iff_deg_eq_one`, `Place.algebraMap_evalAt`,
    `Place.evalAt_ne_zero`;
  * `Defs/PushPull.lean`: `Place.mem_of_ord_nonneg` (note the `hf : f ≠ 0` argument),
    `Place.restrictInclusion`, `Place.restrictResidueMap_residue`, `Place.algebraMap_residueField_eq`,
    `Place.restrict`;
  * `P1/Dictionary.lean`: `RationalFunctionField.deg_eq_one_of_isAlgClosed`,
    `RationalFunctionField.weilReciprocity`, `RationalFunctionField.hasPrincipalDivisors`
    (the last is in `PrincipalDivisors/RatFuncDegree.lean`);
  * `Place/EvalAtNorm.lean`: `weilReciprocity_algebraMap`;
  * `FunctionField.lean`: `FunctionField.exists_ratFuncAlgHom_apply_X_eq`,
    `FunctionField.finite_of_ratFuncAlgHom`;
  * `IsCurveOver/ConstantFieldExtensionSpan.lean` (its own subject): `lSpace_mapDomain_subset_span_image_lSpace_of_constantFieldExtension_of_isAlgClosed`,
    `algebraMap_mem_of_new` (already there, generalised, at line ≈341);
  * `IsCurveOver/ConstantFieldExtension.lean`: `linearIndependent_of_constantFieldExtension_of_isAlgClosed`;
  * `IsCurveOver/PerfectField.lean`: `exists_separating_transcendental_of_perfectField`;
  * `Place/FromValuationSubring.lean`: `Place.exists_toValuationSubring_eq_comap_ringHom_of_isSeparable`;
  * `Place/ConstantFieldExtension.lean`: `Place.inertiaDeg_eq_one_of_isRational`;
  * `Pic0/Torsion.lean`: `Pic0.exists_ord_eq_mul_and_forall_pow_ne_of_ne_zero`;
  * `Place/OrderArithmetic.lean`: a **private** `not_mem_range_of_pow_eq` — copy it privately
    (18 lines) into `Pic0/DivisorialPairing.lean`, do not promote it.

## What to write

### 1. ELL — `IsCurveOver/ConstantFieldExtensionSpan.lean`

Append, before `end AlgebraicCurve` of the module, the wrapper's statement verbatim (the `151` node;
`S_AlgebraicCurve_ell_mapDomain_eq_of_constantFieldExtension_of_isAlgClosed.lean`):

```
theorem ell_mapDomain_eq_of_constantFieldExtension_of_isAlgClosed
    (K F K' F' : Type*) … (D : Divisor K F) [FiniteDimensional K ↥(riemannRochSpace D)] :
    ell (K := K') (D.mapDomain lift) = ell (K := K) D
```

Take the binders from the `Theorems/` wrapper (they are the pin's). The proof is the `S_` file's
(151 lines, 3 declarations):

- `algebraMap_mem_of_new` (19 lines) — **already in this module, generalised** (line ≈341, with
  `[FiniteDimensional]`/`[IsSeparable]` instance arguments and a `RingHom.id F` call). Write the
  pin's `hfg`-form as a ≈5-line specialisation through
  `exists_separating_transcendental_of_perfectField`, public at the pin's name;
- `algebraMap_mem_lSpace` (26 lines) — new, public at the pin's name (the surface gate reads it);
- `solution` (73 lines) — the headline, at the pin's name (`ell_mapDomain_eq_…`, not `solution`).

The pin sets `maxHeartbeats 4000000`; do not. The module already carries a pre-existing 200k
offender (`finrank_le_finrank`); the added declarations are after it, so the module's build gate is
the project cap, and the edit loop may need `-DmaxHeartbeats=2000000` for this module — record it.

### 2. RAT — `Place/DegreeOne.lean`

Append, before `end AlgebraicCurve`, the `119` node at the wrapper's binders:

```
theorem Place.isRational_of_isAlgClosed {K F : Type*} [Field K] [IsAlgClosed K] [Field F]
    [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [FiniteDimensional (RatFunc K) F] (v : Place K F) : v.IsRational
```

The proof is the `S_` file's `solution` (103 lines): restrict `v` to `RatFunc K`, which is rational
by `Place.isRational_iff_deg_eq_one` + the module's own `deg_eq_one_of_isAlgebraic_adjoin`; then
the residue field argument (`IsLocalRing.residue_surjective`, a polynomial `p` annihilating the
residue generator, `Finset.exists_min_image` on the coefficient orders, `Place.mem_of_ord_nonneg`
to put each `coeff i / coeff j` in the valuation ring).

**Do not** use `Place.isRational_of_isCurveOver` (`Place/OrdCalculus.lean:110`): it assumes
`[IsCurveOver K F]`, which the pin's statement does not have and `IsAlgClosed K` does not give (the
characteristic is arbitrary). That substitution is the documented instrument failure FR-0075.

### 3. REC — `WeilExchange/WeilReciprocity.lean`

The `100` node at the wrapper's binders (`{K F} [Field K] [IsAlgClosed K] [CharZero K] … :
WeilReciprocity K F`). The pin's `S_` file is 100 lines, 3 declarations:

- `finsupp_prod_zpow_const` (10) and `degree_eq_sum_of_rational` (12) — the pin's
  `WeilReciprocityAnchor` block, **private** here (they are not in the pin's `p2m_export` list);
- `solution` (≈40) — the headline.

Two traps: the `hconst` branch (`g ∈ range (algebraMap K F)`) needs `Dg = 0` and
`∑ Df = degree Df = 0`; and the descent branch builds a **second** `Algebra (RatFunc K) F`
(`let algφ := φ.toRingHom.toAlgebra`, `stφ`, `finφ`, `CharZero (RatFunc K)`, `IsAlgebraic`,
`IsSeparable`) and then applies `weilReciprocity_algebraMap` with `@`-explicit arguments. Keep
every `@`-spelling and every `let algφ := …` exactly as pinned.

### 4. PAIR — `Pic0/DivisorialPairing.lean`

The `496` node at the wrapper's binders, with the universes spelled as the wrapper does
(`theorem …toHom_injective_of_divisible.{u, v} {K : Type u} {F : Type v} …` and the `hdiv`
hypothesis quantifying `(L' : Type v)`). The pin's `S_` file is 496 lines: 15 private helpers
(439) + the headline (11). Transcribe them in the pin's order:

| helper | pin lines |
|---|---:|
| `Divisor.ord_eq_pullback_of_pow_eq_algebraMap` | 27 |
| `Divisor.exists_mem_support_restrict_eq_of_mem_support_pushforward` | 16 |
| `charZero_of_algebra` | 4 |
| `Divisor.exists_apply_ne_zero_of_mk_ne_zero` | 14 |
| `Place.restrict_restrictScalars_smul` | 16 |
| `isScalarTower_ratFunc_splittingField` | 9 |
| `finiteDimensional_ratFunc_splittingField` | 4 |
| `hasPrincipalDivisors_splittingField` | 8 |
| `isSeparable_splittingField` | 8 |
| `mem_range_algebraMap_of_pow_eq_one` | 8 |
| `not_mem_range_of_pow_eq` | 18 (private copy of `Place/OrderArithmetic.lean:412`) |
| `exists_pair_ne_one_of_pow_eq_of_smul_eq` | **226** — the engine |
| `exists_pair_ne_one_of_ne_zero_of_kummer` | 28 |
| `exists_root_aut_eq_const_mul` | 38 |
| `toHom_injective_of_forall_exists_pair_ne_one` | 15 |
| headline `solution` | 11 |

`exists_pair_ne_one_of_pow_eq_of_smul_eq` is the whole job: the Kummer cover, the `σ` with
`σ h = ζ · h`, divisibility of `Pic⁰(L)` (`hdiv`) on the two-place class `(τ • w₀) − w₀`, the norm
pushdown, and `e.pair x y ≠ 1`. Give it its own wall time. `exists_root_aut_eq_const_mul` uses
`Polynomial.rootOfSplitsXPowSubC`, `HasEnoughRootsOfUnity` and `IsGalois.of_separable_splitting_field`
(all in mathlib v4.34 at those names). The proof's `push Not` is the pin's deprecated `push_neg`
(FR-0036).

## Rules

- Statements are the `Theorems/` wrappers', character for character (binder names included — the
  checker keeps them). Proofs are the `S_` files', adapted to mathlib `v4.34.0` and the port's
  names. If a proof needs a declaration that is `private` in the port or below the home, **stop and
  report** — do not promote, do not restate, do not edit a hub.
- No `set_option maxHeartbeats`, no `sorry`/`admit`/`axiom`/`native_decide`, no `import Mathlib`,
  `set_option autoImplicit false` (the project sets it), zero warnings.
- Edit loop from `lean/`: `timeout 110 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000
  FLTForHuman/…/X.lean`. Finished module: `flock tmp/lean-build.lock timeout 110 lake build
  FLTForHuman.AlgebraicCurve.…X`. **No tree build, no dependents**; every command under two
  minutes with its own `timeout`; logs under `lean/tmp/set9-*.log`.
- `python3 spec/check_port.py --force <module>` → **0 mismatch, 0 missing** per module (expect
  ≈+4 ok on the span module, ≈+1 on `Place/DegreeOne`, ≈+3 on each new module).
- `#print axioms` on the four headlines → `[propext, Classical.choice, Quot.sound]`.
- `python3 tools/deps/dedup.py --within --module <module>` on each module: report the clusters, do
  not refactor them.
- No commit.

## Report (one message)

Per module: the build line and any warnings, the `check_port` summary line, the axioms line, the
line count, and the dedup clusters. Any deviation from the pin's statements, every blocker (with the
exact goal state), and anything the next set should know.
