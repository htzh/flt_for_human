# WORKORDER CFE2 — genus, separability and the different under a constant field extension

Scope: **three insertions**, into `Genus/ConstantFieldExtension.lean`,
`Place/FromValuationSubring.lean` and `Differential/RegularDiffs.lean`. Nothing else may be edited.
The eleven promotions and the `FromValuationSubring` generalisation are the **manager's** and are
already in place before this order runs. (Part of SET 5, [SET-5.md](SET-5.md) §1 and §4.3 —
reviewer's calls 3 and 4.)

## Nodes

| node | pin `S_` / `Theorems/` stem | silo | decls | home |
|---|---|---:|---:|---|
| `AlgebraicCurve.genus_eq_of_constantFieldExtension_of_isAlgClosed` | `S_AlgebraicCurve_genus_eq_of_constantFieldExtension_of_isAlgClosed` | 539 | 36 | insert into `Genus/ConstantFieldExtension.lean` |
| `AlgebraicCurve.Place.exists_toValuationSubring_eq_comap_ringHom_of_isSeparable` | `S_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom_of_isSeparable` | 209 | 12 (11 `private`) | insert into `Place/FromValuationSubring.lean` |
| `AlgebraicCurve.regularDiffs_eq_regularDifferentials` | `S_AlgebraicCurve_regularDiffs_eq_regularDifferentials` | 68 | 5 | insert into `Differential/RegularDiffs.lean` |

Pin at `aa2d8b3`, clone `~/proj/fermats-last-theorem`. **Statements come from each node's
`Theorems/Thm_<stem>.lean` wrapper**, proofs from the `S_` file.

**The mathematics.** Three faces of one base change:
the genus does not move under a constant field extension `F ↦ F' = K'F` (over algebraically closed
`K`, `K'`); a valuation subring of `F` that contains the constants and is not everything is the
preimage of a place's valuation ring along a ring hom, under separability of `F/K(x)` (the pin's
separable form, strictly more general than the `[CharZero K]` form the port carries); and the regular
differentials equal the span of the regular-diff forms.

## Why these homes (do not re-home them)

- **`Genus/ConstantFieldExtension.lean`** (1,635 lines, 8 `spec-pin:` lines, 1 importer) is the CFE
  invariants module — the torsion order, index of specialty, degree/trace and place-counts rows from
  SET 4 live there. It is already above four of this node's six premises
  (`Canonical/DCoordGenerates`, `IsCurveOver/EssFiniteType`, `Place/ConstantFieldExtension`,
  `Place/FromValuationSubring`). It needs **two added imports** — `Differential.Coefficient` and
  `Differential.RegularDiffs` — because the node's sixth premise
  (`Place.ordDifferential_D_eq_zero_of_constantFieldExtension_of_forall_mem`) and
  `localUnitDerivativeRegular_of_isCurveOver` live there. Neither module imports
  `Genus/ConstantFieldExtension`, so both are safe; add them and nothing else at the top.
- **`Place/FromValuationSubring.lean`** (268 lines, 4 `spec-pin:` lines, 5 importers) is the
  valuation-subring↔place dictionary and is where the manager has just generalised the nine-theorem
  private block from `[CharZero K]` to `[Algebra.IsSeparable (adjoin K {x}) F]` and stated the pin's
  two public headlines. **The node's 11 helpers already exist there** — do not write them again:
  `isDedekindDomain_Kx` (12), `isDedekindDomain_integralClosure` (6),
  `isFractionRing_integralClosure` (6), `Kx_le_A` (8), `integralClosure_Kx_le_A` (14),
  `inv_mem_of_notMem_maximalIdeal` (14), `idealOfA_ne_bot` (23), `place_of_idealOfA_le` (16),
  `exists_place_of_mem` (19), `exists_of_valuationSubring` (…), plus the headline itself. The
  node's proof is the pin's one-line application of `exists_of_valuationSubring`.
- **`Differential/RegularDiffs.lean`** (519 lines, 6 `spec-pin:` lines) is above both of the node's
  premises (`ordDiff_eq_ordDifferential` is there; `Canonical/DCoordGenerates` it imports). The
  node's engine is `regularDiffs_eq` — the pin's own 25-line theorem inside the `S_` file — and the
  `solution` is `exact S12R.regularDiffs_eq`: **port the engine, not the three-line wrapper as the
  whole proof.** Its supporting declarations are already public:
  `regularDiffs_eq_span` and `mem_regularDiffs_of_isRegularDiff` in `Differential/Coefficient.lean`,
  `mem_regularDifferentials_iff` in `Defs/RegularDifferentials.lean`, and the promoted
  `coeffLin` / `coeffDer` / `D_ne_zero_of_transcendental`.

**The genus node's engine is the CFE differential block**, 172 lines of which is already in the
port: `differentialCoeff_D_mem` (41, public in `RegularDiffs`), `transcendental_algebraMap` (18) and
`isIntegral_algebraMap` (10), `one_le_ord_of_mem_of_inv_not_mem` (17), `algebraMap_mem_adjoin` (9),
`mem_iff_ord_nonneg` (9), plus the eleven declarations the manager has just promoted
(`Differential/ConstantFieldExtension.lean`: `finiteDimensional_adjoin_of_transcendental`,
`exists_basis_D`, `ratFuncBasis{,_zero}`, `towerBasis{,_zero}`, `polyBasis{,_zero}`;
`RegularDiffs.lean`: `coeffLin`, `coeffDer`, `D_ne_zero_of_transcendental`). Import all of them.
`finiteDimensional_adjoin_of_transcendental` also has a public *shape* twin in
`ModularCurve/X1/FunctionFieldResidue.lean` (`ModularCurve.QExpDeuring.…`, different binders) — the
promoted copy at the pin's binders is the one to use.

## Rules

- Insertions only: append to each module and add the node's wrapper **and** `S_` file to that
  module's existing `spec-pin:` block. Keep every existing declaration untouched; the two added
  imports are the only change above the inserted block.
- Universe and binder spelling from the wrapper, character for character. The genus node's 36
  declarations are pin-public: leave them public. The separable node's 11 helpers are pin-public in
  its `S_` file, but they are **the same statements already in the module** now — import them; the
  node adds only its headline.
- Imports stay specific: **never `import Mathlib`** in a library module. Replace the pin's
  `import Mathlib` (and any broad import a `S_` file carries) with the specific mathlib modules the
  file needs — playbook §4's hygiene rule.
- **No tree build, no dependents.** Edit loop `timeout 110 lake env lean -DautoImplicit=false
  -DmaxHeartbeats=200000 <file>` from `lean/`; finished module `flock .lake/flt_build.lock timeout
  110 lake build <module>`. Every command under 2 minutes, its own `timeout`, no loops; logs under
  `lean/tmp/cfe2-*.log`.
- `python3 spec/check_port.py --force <module>` → **0 mismatch, 0 missing** per module, every added
  declaration `ok`; `#print axioms` on the three headlines → `[propext, Classical.choice,
  Quot.sound]`; 0 warnings; no `sorry`/`admit`/`axiom`; no `set_option maxHeartbeats`; no commit; no
  `spec/decl_markers.tsv` row.
- If a proof needs a `private` port helper or a declaration below its home, **stop and report** —
  do not promote, do not restate, do not edit a hub. If a promoted declaration's *statement* does
  not match what the pin proof consumes, report it: that is a manager error, not yours to patch.

## Report (one message)

per module: build + warnings, the checker summary line, declarations added; the three axioms lines;
whether the genus proof consumed the promoted declarations as they stand (and which); any blocker.
