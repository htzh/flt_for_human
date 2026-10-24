# WORKORDER DP1 — differentials as divisor function spaces (regular and polar)

**Status: LANDED (2026-10-24).** Both modules green, reviewed by the manager: checker
**13 ok / 0 mismatch / 0 missing / 0 own** (polar) and **8 ok / 0 / 0 / 0** (regular), tier-1 builds
green with no warning from either module, both headlines `[propext, Classical.choice, Quot.sound]`,
`dedup.py` 0 clusters and `move_dead.py --select dead` 0 declarations on each, and the `S = ∅`
cross-check re-run independently as a compiled example.  Ground prepared before the dispatch:
`Defs/PolarDifferentials.lean` (18 ok / 0 / 0 / 0, built) and
`AlgebraicCurve.riemannRoch_and_constantsAreBase` promoted into `ResidueTheorem/RRAssembly.lean`
(42 ok / 0 / 0 / 0, built, one `spec/decl_markers.tsv` row).  Plan and mathematics:
[TOPIC-differentials-pole-bound.md](TOPIC-differentials-pole-bound.md).  Pin `aa2d8b3`; mathlib
`v4.34.0`.

## 0. Scope

Port two pin nodes in one set, as one development:

```
AlgebraicCurve.finite_and_finrank_polarDifferentials_eq          (S_ 334 ln, general)
AlgebraicCurve.finite_and_finrank_regularDifferentials_eq_genus   (S_ 220 ln, the S = ∅ case)
```

Write the divisor dictionary **once**, in the general (polar) module; the regular module derives
its statements from it.  Statements are the pin's verbatim (the `Theorems/Thm_*` wrappers for the
two headlines, the `S_` files for everything else).  Do not restate the pin's duplicated prelude
(§3), do not edit any existing module (§5).

## 1. Deliverables

### 1.1 `FLTForHuman/AlgebraicCurve/Canonical/PolarDifferentials.lean` (general)

Declarations, in this order, statements verbatim from
`P2M/Sol/S_AlgebraicCurve_finite_and_finrank_polarDifferentials_eq.lean`:

| pin line | declaration |
|---:|---|
| 84 | `isRegularAt_smul_iff` |
| 105 | `hasSimplePoleAt_smul_iff` |
| 128 | `smul_mem_polarDifferentials_iff` |
| 147 | `toPolar` |
| 158 | `toPolar_apply` |
| 163 | `toPolar_bijective` |
| 178 | `lSpaceEquivPolar` |
| 191 | `degree_canonical_eq` |
| 202 | `ord_algebraMap_eq_zero` |
| 214 | `lSpace_neg_polarDivisor_eq_bot` |
| 237 | `degree_polarDivisor` |
| 247 | `ell_canonical_add_polarDivisor` |
| wrapper | **headline** `AlgebraicCurve.finite_and_finrank_polarDifferentials_eq` |

The pin's phase section `Comparison` becomes a `section` (not a namespace).  `polarDivisor`,
`polarDivisor_apply`, `polarDifferentials`, `mem_polarDifferentials_iff`, the per-place predicates
and closure lemmas are **already in** `Defs/PolarDifferentials.lean` — import them, do not restate.

The headline statement is the `Theorems/` wrapper verbatim:

```lean
theorem AlgebraicCurve.finite_and_finrank_polarDifferentials_eq
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [Algebra.EssFiniteType K F]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    (S : Finset (AlgebraicCurve.Place K F)) (hS : S.Nonempty) :
    Module.Finite K ↥(AlgebraicCurve.polarDifferentials K F (S : Set (AlgebraicCurve.Place K F))) ∧
      Module.finrank K ↥(AlgebraicCurve.polarDifferentials K F (S : Set (AlgebraicCurve.Place K F))) =
        AlgebraicCurve.genus K F + S.card - 1
```

The pin proves it through a private `solution`; state the headline directly (no `solution` twin,
per `WORKORDER-RPF1` §1).  The proof is the pin's: `dCoordGenerates_of_isCurveOver`,
`riemannRoch_and_constantsAreBase` (imported), `finiteDimensional_lSpace`, `lSpaceEquivPolar`,
`ell_canonical_add_polarDivisor`.

### 1.2 `FLTForHuman/AlgebraicCurve/Canonical/RegularDifferentialsFinrank.lean` (the `S = ∅` case)

| pin line | declaration |
|---:|---|
| 65 | `exists_smul_eq` |
| 74 | `smul_mem_regularDifferentials_iff` |
| 101 | `toRegular` |
| 111 | `toRegular_apply` |
| 114 | `toRegular_bijective` |
| 129 | `lSpaceCanonicalEquivRegular` |
| 133 | `ell_canonical_eq_genus` (ℕ form) |
| wrapper | **headline** `AlgebraicCurve.finite_and_finrank_regularDifferentials_eq_genus` |

from `P2M/Sol/S_AlgebraicCurve_finite_and_finrank_regularDifferentials_eq_genus.lean`.  The headline
is the `Theorems/` wrapper verbatim:

```lean
theorem AlgebraicCurve.finite_and_finrank_regularDifferentials_eq_genus {K F : Type*} [Field K]
    [Field F] [Algebra K F] [IsAlgClosed K] [Algebra.EssFiniteType K F]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)] :
    Module.Finite K ↥(AlgebraicCurve.regularDifferentials K F) ∧
      Module.finrank K ↥(AlgebraicCurve.regularDifferentials K F) =
        AlgebraicCurve.genus K F
```

Derive `smul_mem_regularDifferentials_iff` from the polar dictionary: at `S = ∅`,
`polarDifferentials_empty` and `polarDivisor ∅ = 0` turn
`h • ω₀ ∈ polarDifferentials ∅ ↔ h ∈ LSpace (W + polarDivisor ∅)` into the pin's statement.  State
the pin's text verbatim; the proof is the specialization.  Then the maps are the pin's own (11–15
lines each) over that lemma.  `ell_canonical_eq_genus` (ℕ) is `Nat.cast_injective` /
`exact_mod_cast` applied to the imported `AlgebraicCurve.ell_canonicalDivisor_eq_genus_of_riemannRoch`
(ℤ form, `RRAssembly.lean`, already ported).

Namespaces: `AlgebraicCurve`, with the pin's `namespace RegularDifferentialsFinrank` block kept as
an inner namespace for the helper declarations (the pin's names then transcribe verbatim, and the
generic `toRegular` / `toPolar` stay namespaced); the headlines go directly under `AlgebraicCurve`.

## 2. Imports

Polar module: `FLTForHuman.AlgebraicCurve.Defs.{AdelicIndex, CanonicalDivisor, PushPull,
IsCurveOver, PolarDifferentials, RegularDifferentials, RiemannRochRows}`,
`FLTForHuman.AlgebraicCurve.Genus.Index` (for `finiteDimensional_lSpace`),
`FLTForHuman.AlgebraicCurve.ResidueTheorem.RRAssembly` (for `riemannRoch_and_constantsAreBase`,
`constantsAreBase_of_isAlgClosed`, `ell_canonicalDivisor_eq_genus_of_riemannRoch`), plus the narrow
mathlib modules the proofs need.  No `import Mathlib`.  Regular module: the polar module plus
`Defs.{RegularDifferentials, CanonicalDivisor, AdelicIndex}` and
`Mathlib.LinearAlgebra.FiniteDimensional.Basic` (for `exists_smul_eq_of_finrank_eq_one`).

Do **not** import `Differential/Hurwitz.lean` or `Canonical/WeilDifferential.lean`: the dictionary
uses neither, and `exists_smul_eq` here is the pin's `S_` :65 declaration (no non-zero hypothesis on
`ω`), which is *not* Hurwitz's `IsCurveOver.exists_smul_eq` (both arguments non-zero, from its own
pin file).

## 3. Do not restate (the pin's duplicated prelude)

These are already public elsewhere; the two `S_` files' copies are left undiffed (the checker only
diffs declarations the port makes):

| pin declaration | port home |
|---|---|
| `ord_nonneg_of_mem_valuationSubring`, `mem_valuationSubring_of_ord_nonneg` | `Place.ord_nonneg_of_mem`, `Place.mem_of_ord_nonneg` — `Defs/PushPull.lean` |
| `differentialCoeff_ne_zero` | `Place.differentialCoeff_ne_zero` — `Defs/LocalResidue.lean` |
| `riemannRoch_and_constantsAreBase` | `ResidueTheorem/RRAssembly.lean` (marker row in `spec/decl_markers.tsv`) |
| `ell_canonical_eq_genus` (ℤ form, polar `S_` :183) | `ell_canonicalDivisor_eq_genus_of_riemannRoch` — `ResidueTheorem/RRAssembly.lean` (same statement, other name; use it, do not declare the twin) |

The two §1.2 items that *are* declared (`exists_smul_eq`:65, `ell_canonical_eq_genus`:133 ℕ) are the
pin's own statements and belong in the wire.

## 4. Route and risk

* The dictionary is per-place: `isRegularAt_smul_iff` (`0 ≤ ord h + W v`) and
  `hasSimplePoleAt_smul_iff` (`-1 ≤ ord h + W v`); both are `canonicalDivisorOf_apply` +
  `differentialCoeff_smul_dCoord` + `ord_mul` + `ord_uniformizer` arithmetic.  The lemmas exist in
  the module's imports (`Defs/CanonicalDivisor.lean`, `Defs/Place*.lean`); the pin's proofs use
  `ord_nonneg_of_mem_valuationSubring` / `mem_valuationSubring_of_ord_nonneg`, whose port names are
  `Place.ord_nonneg_of_mem` / `Place.mem_of_ord_nonneg`.
* `polarDivisor_apply` is already ported; `polarDivisor ∅ = 0` is `Finset.sum_empty` (`simp`).
* `lSpace_neg_polarDivisor_eq_bot` needs `ConstantsAreBase` (`LSpace 0 = range (algebraMap)`) and
  `ord_algebraMap_eq_zero`; `degree_polarDivisor` needs `[IsAlgClosed K]`,
  `deg_eq_one_of_isAlgClosed_of_finite`, `Module.Finite K v.ResidueField` (from `IsCurveOver`).
* `ell_canonical_add_polarDivisor` ends with `omega` over `ℤ` after
  `← degree_canonical_eq`, `degree_polarDivisor`, `ell (−polarDivisor S) = 0` and `1 ≤ S.card`.
* **Stop-early risks**: (a) a definitional mismatch between the pin's `IsRegularAt` and
  `regularDifferentials` membership — report, do not weaken; (b) `toPolar_bijective`'s surjectivity
  needs the pin's `exists_smul_eq` (:65) at `ω ≠ 0`; if the port's `Place` API spells the valuation
  dictionary differently, use the port's spelling and note it; (c) if `ell_canonical_add_polarDivisor`
  needs `[IsCurveOver]`/`[HasCanonicalDivisor]` instances the pin's `omit` removed, restore them
  (they are in the section variables of the pin) and report the drift.

## 5. Do not touch

`Defs/PolarDifferentials.lean`, `ResidueTheorem/RRAssembly.lean`, `spec/decl_markers.tsv` are frozen
for this set (they are the ground).  No existing module is edited; if the port needs a helper that
does not exist, add it `private` in the new module and report it.  `Canonical/WeilDifferential.lean`
is **not** part of this order (its two divisor-membership lemmas become corollaries of this
dictionary in a later, legacy-module order — see the topic note §4.4).

## 6. Header and wiring

Port-style header: subject, pin URLs at `aa2d8b3`, the mathematics in a paragraph, `spec-pin:` lines
(wrapper first, then the `S_` file), drift note.  `set_option autoImplicit false`,
`noncomputable section`, `namespace AlgebraicCurve`, and the pin's `namespace
RegularDifferentialsFinrank` where the names are the pin's.

```
  spec-pin: Theorems/Thm_AlgebraicCurve_finite_and_finrank_polarDifferentials_eq.lean
  spec-pin: P2M/Sol/S_AlgebraicCurve_finite_and_finrank_polarDifferentials_eq.lean
```

(resp. the regular pair).  No `spec/decl_markers.tsv` row is expected; if one is needed, report why
before adding it.

## 7. Verification

```bash
cd lean
timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 \
  FLTForHuman/AlgebraicCurve/Canonical/PolarDifferentials.lean
timeout 90 flock lake.lock lake build FLTForHuman.AlgebraicCurve.Canonical.PolarDifferentials
python3 spec/check_port.py --force FLTForHuman/AlgebraicCurve/Canonical/PolarDifferentials.lean
# then the same three for RegularDifferentialsFinrank
python3 ../tools/deps/dedup.py 'Canonical/PolarDifferentials'
python3 ../tools/deps/dedup.py 'Canonical/RegularDifferentialsFinrank'
python3 ../tools/deps/move_dead.py --source lean/FLTForHuman/AlgebraicCurve/Canonical/PolarDifferentials.lean \
  --target lean/Reserve/AlgebraicCurve/DeadPolar.lean --select dead --dry-run   # 0 expected
```

Acceptance: checker `0 mismatch / 0 missing / 0 own`, tier-1 builds green with 0 warnings, dedup 0
clusters, dead-code scan 0, `#print axioms` on both headlines `[propext, Classical.choice,
Quot.sound]`, no `sorry`/`admit`/`axiom`, no `set_option maxHeartbeats`.

**Cross-check the structural claim**: instantiate `smul_mem_polarDifferentials_iff` at `S = ∅` and
confirm it is `smul_mem_regularDifferentials_iff` up to `polarDifferentials_empty` and
`polarDivisor ∅ = 0`; if that fails, the specialization is not a specialization — report before
working around it.

## 8. Report

Return: the two module paths and their checker/build readings, the two headlines' axiom sets, the
`S = ∅` cross-check result, the declaration list actually produced with any renamed pin name and its
pin line, the deferred/blocked items, and anything the next (legacy `WeilDifferential`) order needs
to know.  Do not narrate the proof search.
