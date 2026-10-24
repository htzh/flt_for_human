# TOPIC — differentials as divisor function spaces (the pole-bound dictionary)

**Status (2026-10-24): landed and green; this note is the landing record.** The port is
`Canonical/PolarDifferentials.lean` (274 ln, 13 public declarations) and
`Canonical/RegularDifferentialsFinrank.lean` (135 ln, 8), on the definition layer
`Defs/PolarDifferentials.lean` (18), with the shared producer
`AlgebraicCurve.riemannRoch_and_constantsAreBase` promoted into
`ResidueTheorem/RRAssembly.lean`.  Measured: checker **13 ok / 0 / 0 / 0** and
**8 ok / 0 / 0 / 0** (and 18 ok for the definition module, 42 ok for `RRAssembly`, which
gained the producer and one `spec/decl_markers.tsv` row); `Canonical/WeilDifferential.lean`
migrated off the legacy checker onto its own wire (**25 ok / 0 / 0 / 0 / 0**) with its two
membership lemmas now corollaries of the shared per-place engine; tier-1 builds green with no
warning from any of the five modules; both headlines
`[propext, Classical.choice, Quot.sound]`; `dedup.py` 0 clusters and `move_dead.py --select dead`
0 declarations on each.  The `S = ∅` cross-check of §2 is a compiled example: the polar
dictionary at `∅`, `rw [polarDifferentials_empty]; simp [polarDivisor]`, is the regular
statement, and that `simpa` is literally the proof of `smul_mem_regularDifferentials_iff`.
The proof body was dispatched from
[WORKORDER-DP1-differentials-pole-bound.md](WORKORDER-DP1-differentials-pole-bound.md).
This note fixes the mathematics and the module structure for the two pin nodes

```
AlgebraicCurve.finite_and_finrank_regularDifferentials_eq_genus          (S_ 220 ln)
AlgebraicCurve.finite_and_finrank_polarDifferentials_eq                  (S_ 334 ln)
```

They are the two ends of one statement, so they are one topic and one development.  Pinned at
`anthropics/fermats-last-theorem` `aa2d8b3`; the port's mathlib is `v4.34.0`.  §4 is the
refactoring executed as ground preparation, §5 the deliverables as landed, §6 the deferred
surface, and §8 the commands behind every number above.

**Subject, in one sentence.** For a curve `F/K` and a divisor `D`, multiplication by a non-zero
differential `ω₀` identifies the Riemann–Roch space `L(W − D)`, `W = (ω₀)`, with the differentials
whose divisor is `≥ D`; taking `D = 0` gives `dim Ω^1_reg = g`, and taking `D = −Σ_S` (simple poles
on a finite `S`) gives `dim Ω^1(S) = g + |S| − 1`.

## 0. Provenance

`frontier.py --ds --ready --fanin-min 7` surfaces
`AlgebraicCurve.finite_and_finrank_regularDifferentials_eq_genus` as the next ready node
(`used_by` 4 cone / 25 project, `needed 1`, silo 220).  The frontier's silo reading is the `S_`
file, and its own note applies: check the local proof.  Measured (`twin_scan.py`,
`port_advise.py`):

| node | `S_` ln | `port_advise` substitutes | twin |
|---|---:|---|---|
| regular | 220 | 2 (~24 ln: two valuation helpers already in `Defs/PushPull.lean`) | none, prelude 0/12 |
| polar | 334 | the same two, plus `differentialCoeff_ne_zero` | none |

Both are unported (`N` on the frontier).  Their seven in-cone premises (separating
transcendental, `isCurveOver_ratFunc`, `essFiniteType_of_transcendental_of_finiteDimensional`,
`functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver`, `constantsAreBase_of_isAlgClosed`,
`dCoordGenerates_of_isCurveOver`, `finiteDimensional_lSpace`) are ported, as are the
definitions (`regularDifferentials`, `canonicalDivisorOf`, `genus`, `LSpace`, `ell`,
`FunctionFieldRiemannRoch`, `ConstantsAreBase`).

The sibling `S_` files in the same pin family are **not** this topic (they are consumers of it,
or belong to the `genusFF` / Čech families): `finite_and_finrank_regularDiffs_eq_genusFF_of_isAlgClosed`
(129 ln), `finite_and_finrank_kaehlerSections_H0_eq_genusFF_of_isAlgClosed` (113 ln),
`ModularCurve.finite_and_finrank_regularDifferentials_qExpFunctionFieldC_eq_genusFF_of_isAlgClosed`
(30 ln).  Each becomes a short corollary once this development lands; they are not taken here
because their subject is the comparison of the two genera, not the divisor dictionary.

## 1. The mathematics

Write `W = (ω₀) = canonicalDivisorOf hω₀` and `Σ_S = polarDivisor S = Σ_{v ∈ S} v`.  Since `Ω` is
one-dimensional (`IsCurveOver.finrank_kaehler`), every `ω` is `h · ω₀` for some `h : F`, and
`(h · ω₀) = (h) + W`.  The dictionary is the three faces of that identity:

| port object | divisor condition on `ω` | `ω = h · ω₀` gives |
|---|---|---|
| `regularDifferentials` | `div ω ≥ 0` | `h ∈ L(W)` |
| `polarDifferentials (S : Set _)` | `div ω ≥ −Σ_S` | `h ∈ L(W + Σ_S)` |
| `omegaSpace D` | `div ω ≥ D` | `h ∈ L(W − D)` |

The signs are fixed by the pin, not by choice — quote them, do not re-derive a "generic `D`"
dictionary:

* regular: `h • ω₀ ∈ regularDifferentials ↔ h ∈ LSpace (canonicalDivisorOf hω₀)`
  ([`S_…regularDifferentials…:74`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_finite_and_finrank_regularDifferentials_eq_genus.lean#L74));
* polar: `h • ω₀ ∈ polarDifferentials S ↔ h ∈ LSpace (canonicalDivisorOf hω₀ + polarDivisor S)`
  ([`S_…polarDifferentials…:128`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_finite_and_finrank_polarDifferentials_eq.lean#L128));
* adelic: `finrank omegaSpace D = ell (canonicalDivisorOf hω − D)`
  (`ResidueTheorem/RRAssembly.lean:568`, `Defs/RiemannRochRows.lean:49`).

A "pole bound `D`" (`div ω ≥ −D`) therefore pairs with `L(W + D)`, and the `W − D` form needs `Ω(D)`,
a *lower* bound.  Mixing the two conventions is the one sign error this subject invites; state the
dictionary with the pin's own divisor (`W`, `W + polarDivisor S`) and specialize.

Per place, the two halves of the dictionary are

```
IsRegularAt   (h • ω₀) ↔  0 ≤ v.ord h + W(v)
HasSimplePoleAt (h • ω₀) ↔ −1 ≤ v.ord h + W(v)
```

(`isRegularAt_smul_iff`, `hasSimplePoleAt_smul_iff`), and the regular case is the polar case at
`S = ∅` (`polarDifferentials_empty : polarDifferentials ∅ = regularDifferentials`,
`polarDivisor ∅ = 0`).

The dimension half is Riemann–Roch at `D = 0` and at `D = −Σ_S`:

```
ℓ(W + Σ_S) = deg W + |S| + 1 − g + ℓ(−Σ_S)
           = 2g − 2 + |S| + 1 − g + ℓ(−Σ_S).
```

The two nodes are its two branches: `ℓ(0) = 1` when `S = ∅` (giving `g`, the regular headline) and
`ℓ(−Σ_S) = 0` when `S ≠ ∅` (giving `g + |S| − 1`, the polar headline, which the pin states under
`hS : S.Nonempty` for that reason).  The polar `S_` file carries exactly those pieces —
`degree_canonical_eq` (`deg W = 2g − 2`), `lSpace_neg_polarDivisor_eq_bot`, `degree_polarDivisor`,
`ell_canonical_add_polarDivisor` (which needs `1 ≤ S.card`).

`degree_canonical_eq` is wanted well beyond this topic: `Differential/Hurwitz.lean` currently takes
`deg W = 2g − 2` as a hypothesis (`hK`) because nothing in the port proves it.

## 2. Why one development and two modules

The pin writes the same development twice, one divisor higher: the polar `S_` file repeats, verbatim,

| repeated declaration | regular file | polar file |
|---|---|---|
| `ord_nonneg_of_mem_valuationSubring`, `mem_valuationSubring_of_ord_nonneg` | 35, 51 | 35, 51 |
| `differentialCoeff_ne_zero`, `exists_smul_eq` | 59, 65 | 59, 65 |
| `ell_canonical_eq_genus` (ℤ form) | 133 (ℕ form) | 183 (ℤ form) |
| `riemannRoch_and_constantsAreBase` | 143 | 261 |

and proves `smul_mem_polarDifferentials_iff` / `toPolar` / `lSpaceEquivPolar` by the same script as
`smul_mem_regularDifferentials_iff` / `toRegular` / `lSpaceCanonicalEquivRegular`, with `W` replaced
by `W + Σ_S` and one extra branch at the places of `S`.

Porting the regular node alone would write the dictionary in the special form and leave the polar
order to write it again one divisor higher; porting the polar node alone would lose the `D = 0`
headline that the Deligne–Serre transport consumes.  So: one topic, two modules, the dictionary
written once in the general (polar) form, the regular form as its `S = ∅` instance.

Two modules, not one, because a module is a mathematical role (§3.1) and the two `S_` files state
two headlines with two wires.  The general module is the engine, the regular module its
specialization; `spec-pin:` in each header keeps the diff mechanical, and the pin's duplicated
prelude is *not* restated (the checker diffs port declarations, so an unstated duplicate costs
nothing, while a restated one would be a `dedup.py` cluster).

## 3. Homes

```
Defs/PolarDifferentials.lean        vocabulary: IsRegularAt, HasSimplePoleAt,
                                    polarDifferentials, polarDivisor, closure lemmas
        │
        ├── Canonical/PolarDifferentials.lean     general dictionary (W + Σ_S),
        │                                         ℓ/degree lemmas, polar headline
        │       │
        │       └── Canonical/RegularDifferentialsFinrank.lean   D = 0 instances,
        │                                                        ell(W) = g (ℕ),
        │                                                        regular headline
        └── (imported by both) ResidueTheorem/RRAssembly.lean     hRR, hC producers
```

* `Canonical/` and not `Differential/`: the subject is a divisor cut on `Ω` — `W`, `L(·)`, `ell`,
  `deg` — not the operations theory (push/pull, trace, generation, Hurwitz ramification).
* `Canonical/` and not `Genus/`: `Genus/` is the adelic engine (`indexOfSpecialty`, `RiemannGenusReached`,
  Stichtenoth).  Here the object is `Ω`, cut by a divisor; `Genus/RatFunc.lean` is the precedent for a
  small subject module that imports `RRAssembly`.
* Next to `Canonical/WeilDifferential.lean`, which is the *other* model of the same object
  (`Ω_reg ≃ omegaSpace 0`, conditional on `ResidueTheorem`).  Two models, two modules, one theory.
* The `S = ∅` instance imports the general module; the general module never imports the special one.
  Neither imports `Differential/Hurwitz.lean` or `Canonical/WeilDifferential.lean`: the dictionary's
  only inputs are the divisor, `L`, `Ω` and the rank-one fact, and `RRAssembly` for the producers.

## 4. Ground preparation (executed, §5 of the plan below)

1. **`Defs/PolarDifferentials.lean`** (new).  The pin's definition module
   `Definitions/Def_AlgebraicCurve_PolarDifferentials.lean` (200 ln), cut at the residue-theorem
   boundary: the `HasSimpleResidue` / `gluedPolarDifferentials` half and the `HasValue` block it
   needs (which lives in `Definitions/Def_AlgebraicCurve_GluedPic0.lean`, together with the
   `GluingData` / `gluedPrincipal` Pic⁰ gluing) are deferred — none of them is reached by either
   headline.  Deferred surface registered in §6.
2. **`ResidueTheorem/RRAssembly.lean`** — `AlgebraicCurve.riemannRoch_and_constantsAreBase`
   promoted to public at the pin's statement (identical in both `S_` files, :143 and :261), by
   moving out the `RatFunc`-tower body that already sits inside
   `functionFieldRiemannRoch_of_isAlgClosed_of_transcendental`; that wrapper now reads `(…).1`.
   One copy of the tower, and the pin's sixteen `_of_transcendental`-style consumers get a public
   producer.  Wire accounting: one `spec/decl_markers.tsv` row.
3. **No legacy module is edited for the two theory modules.**  The four helpers are already public
   in the port at other names
   (`Place.ord_nonneg_of_mem`, `Place.mem_of_ord_nonneg` in `Defs/PushPull.lean`;
   `Place.differentialCoeff_ne_zero` in `Defs/LocalResidue.lean`), so the two `S_` files' copies are
   simply not restated.  `Differential/Hurwitz.lean`'s `IsCurveOver.exists_smul_eq` is a *different*
   pin declaration (namespace `IsCurveOver`, stated with both arguments non-zero, from
   `S_AlgebraicCurve_map_ne_zero_of_tame.lean:547`), not a twin of our `exists_smul_eq` (`S_` :65,
   no non-zero hypothesis on `ω`): both stay, in their own wires.
4. **`Canonical/WeilDifferential.lean`: done in the same round (2026-10-24).**  The pin states
   `isRegularAt_smul_iff` in an `[IsCurveOver K F]` section, but its proof needs only
   `[HasCanonicalDivisor]`, `[v.DCoordGenerates]` and `[Nontrivial Ω[F⁄K]]`, and the
   Weil-differential bridge has no `IsCurveOver` to offer.  So the engine moved **down** to
   `Defs/PolarDifferentials.lean` as `Place.isRegularAt_smul_iff_ord` (`own:`-marked: the pin's
   lemma without its unused section binder), and the polar module's public
   `PolarFinrank.isRegularAt_smul_iff` is now the pin's statement on top of it (`v.…_ord hω₀ hh`),
   so the per-place dictionary is proved once for both theories.  Consequences in
   `WeilDifferential`:
   * `canonicalDivisorOf_nonneg_of_mem_regularDifferentials` and
     `mem_regularDifferentials_of_canonicalDivisorOf_nonneg` are now the `h = 1` case
     (`one_smul`, `v.ord_one`), two lines each, no `canonicalDivisorOf_apply` arithmetic;
   * `ord_nonneg_of_mem_vs` is a one-line alias of `Place.ord_nonneg_of_mem`, and
     `mem_vs_of_ord_nonneg` is two lines through `Place.mem_of_ord_nonneg`; the latter keeps its
     more general statement (no `f ≠ 0` hypothesis), so it is *not* a duplicate of that lemma.
     The still-same-statement pair (`ord_nonneg_of_mem_vs` against `Place.ord_nonneg_of_mem`) is a
     zero-cost delegating duplicate (invisible to `dedup.py` without `--min-cost 0`); it stays
     because `Canonical/HasCanonicalDivisor.lean` calls that name at five sites, and a later
     `HasCanonicalDivisor` order should drop the alias and rename them;
   * migration: the module now carries its own `spec-pin:` wire (wrapper + `S_` file) and its
     `PORT_FILES` entry is removed from `spec/old_check_stmts.py`; `spec/check_port.py` reads
     **25 ok / 0 mismatch / 0 missing / 0 own / 0 kw** with **no** `spec/decl_markers.tsv` row
     (the pin-private and `p2m_export`ed spellings match through the checker's promoted-key and
     content tiers), `ord_nonneg_of_mem_vs` / `mem_vs_of_ord_nonneg` included;
   * one file-scoped `set_option linter.unusedSectionVars false`, justified in place: the pin's
     `Generic` section carries four instances and each lemma uses a subset (7 declarations), and
     the statements' binder lists are the pin's verbatim, so they are kept rather than omitted.

   Verification: build 4.1 s, the two direct dependents `Canonical/HasCanonicalDivisor` (16 s) and
   `Differential/Hurwitz` rebuilt green, `#print axioms` on the headline and on both membership
   lemmas `[propext, Classical.choice, Quot.sound]`, `dedup.py` 0 clusters, dead scan 0.  **Open
   item, build only:** editing `WeilDifferential` stales the oleans of its ~60-module dependent
   cascade (`build_ladder.py --edit` prices it at ≈512 s); it needs one wave build of the affected
   targets, or the session-end build with the user's agreement — the two direct dependents are
   done.

## 5. Deliverables and their statements

`Canonical/PolarDifferentials.lean` (general):

* `isRegularAt_smul_iff`, `hasSimplePoleAt_smul_iff` (per place, `h ≠ 0`);
* `smul_mem_polarDifferentials_iff` (the dictionary);
* `toPolar`, `toPolar_apply`, `toPolar_bijective`, `lSpaceEquivPolar`;
* `degree_canonical_eq`, the supporting lemma `ord_algebraMap_eq_zero`,
  `lSpace_neg_polarDivisor_eq_bot`, `degree_polarDivisor` (needs `[IsAlgClosed K]`),
  `ell_canonical_add_polarDivisor`;
* headline `AlgebraicCurve.finite_and_finrank_polarDifferentials_eq`
  (`Module.Finite K (polarDifferentials … (S : Set _)) ∧ finrank = genus K F + S.card − 1`,
  under `[IsAlgClosed K] [Algebra.EssFiniteType K F] [IsCurveOver K F] [HasCanonicalDivisor …]`,
  `S : Finset (Place K F)`, `hS : S.Nonempty`).

`Canonical/RegularDifferentialsFinrank.lean` (the `S = ∅` instance, our node):

* `exists_smul_eq` (the pin's :65, 3 lines from `exists_smul_eq_of_finrank_eq_one` and
  `IsCurveOver.finrank_kaehler`);
* `smul_mem_regularDifferentials_iff`, `toRegular`, `toRegular_apply`, `toRegular_bijective`,
  `lSpaceCanonicalEquivRegular` (each derived from the polar form at `polarDifferentials_empty`);
* `ell_canonical_eq_genus` (ℕ form, from `RRAssembly`'s ℤ form);
* headline `AlgebraicCurve.finite_and_finrank_regularDifferentials_eq_genus`.

Both headlines and the dictionary are the pin's `Theorems/Thm_*` / `S_` statements verbatim; the pin's
`RegularDifferentialsFinrank` phase namespace is kept as the inner namespace (it also protects the
generic names `toRegular` / `toPolar`).

## 6. Deferred surface (registered, not in this topic)

From `Definitions/Def_AlgebraicCurve_PolarDifferentials.lean`: `Place.HasSimpleResidue`,
`Place.irreducible_mk_uniformizer`, `HasSimpleResidue.hasSimplePoleAt`,
`hasSimpleResidue_zero_of_mem`, `IsGluedPolarPair`, `gluedPolarDifferentials` and its five lemmas.
From `Definitions/Def_AlgebraicCurve_GluedPic0.lean`: `Place.HasValue` and its API,
`GluingData`, `admissible`, `IsGluedPrincipal`, `gluedPrincipal`.  Their consumers are the residue
theorem's residue-data nodes (`exists_mem_polarDifferentials_forall_hasSimpleResidue_of_sum_eq_zero`,
`exists_linearMap_hasSimpleResidue_ker_eq_regular_range_eq_sum_zero_…`) and the Pic⁰ gluing, not the
dimension theory.

## 7. Verification

* New modules wire themselves with `spec-pin:` (pin definition module first, then the `S_` file and
  its `Theorems/` wrapper).  `python3 spec/check_port.py --force <module>` per module:
  `0 mismatch / 0 missing`; any `own:` marker justified in its source comment.
* `python3 tools/deps/dedup.py 'Canonical/RegularDifferentials*'` and
  `'Canonical/PolarDifferentials*'`: no cluster; `move_dead.py --select dead --dry-run` on each:
  empty.
* `lake build` per module (tier 1), `#print axioms` on both headlines, no `sorry`, no `axiom`.
* The polar `S = ∅` cross-check: instantiate `smul_mem_polarDifferentials_iff` at `∅` and compare
  with `smul_mem_regularDifferentials_iff` — the two must be the same statement, which is the
  structural claim of §2.

## 8. Reproduce

```bash
cd tools/deps
python3 twin_scan.py --node AlgebraicCurve.finite_and_finrank_regularDifferentials_eq_genus
python3 port_advise.py --nodes AlgebraicCurve.finite_and_finrank_polarDifferentials_eq
python3 frontier.py --ds --ready --fanin-min 7
```
