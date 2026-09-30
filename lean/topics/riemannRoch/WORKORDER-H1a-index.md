# Work order — H1a: the adelic-index / `ell` prelude and the index targets

**Status: DISPATCHED (2026-09-29).** Set D reviewed green (checker 2683/0/0, six
modules build, axioms clean). The mathlib audit is still running; it is **advisory,
not a gate** — read `AUDIT-mathlib.md` if it exists when you start, otherwise do your
own bounded searches. Use `ScratchH1a.lean`, **not** `Scratch.lean` (another agent
holds that file). Method: `lean/porting-playbook.md` §2.4, §3.1–§3.7, §4.
Plan: `PLAN-P1.md` §2. Prerequisite set: D.

## 0. Scope

The largest single block of the phase-1 engine: the `ell` / `LSpace` degree
inequalities, the adelic-quotient finiteness chain
(`finrank_adeleBdd*`, `lSpaceShiftEquiv`, `adeleBddQuotSingleEquivResidueField`),
the residue-pairing / `weilSmul` block, the `RiemannGenusReachedAt` gates, and the
five index targets. Union content **75 names / 1,635 once-each lines** (refined
partition, `tools/deps/build/rr_homes.txt` §H1a). Nearly all of it lives in one
pin file, which is the primary transcription source.

**Explicitly not this set:** the Stichtenoth tower (H1b); the assembly wrappers and
the `H¹` identification (H2); the differentials / residue block (H3). Definitions
come from Set D — **import, do not re-prove**: `LSpace`, `ell`, `adeleBdd`,
`adeleSpace`, `globalSub`, `adeleBddPrincipal`, `indexOfSpecialty`, `omegaSpace`,
`weilDifferentialModule`, `weilSmul`, `residuePairing`, `RiemannGenusReachedAt`,
`RiemannGenusReached`, `StichtenothGenusExists`, `RiemannGenusBounded`,
`IndexOfSpecialtyFinite`, `PoleDivisorPackage`, `HasPoleDivisorPackage`.

## 1. Deliverable

`FLTForHuman/AlgebraicCurve/Genus/Index.lean`

- namespace `AlgebraicCurve` (keep the pin's names verbatim).
- imports: `FLTForHuman.AlgebraicCurve.Defs.{AdelicIndex,Repartitions,PoleDivisorPackage,CanonicalDivisor,IsCurveOver}` and `FLTForHuman.AlgebraicCurve.Defs.PushPull` (for the three already-ported `Place.*ord*` lemmas); specific mathlib modules only.
- one module, one theory: the adelic index of a function field. Public the whole
  union; keep `private` exactly what the pin keeps `private`.

**Primary source** (`69 of the 75 names`):
`P2M/Sol/S_AlgebraicCurve_exists_genus_riemannIndex_of_stichtenothGenusExists.lean`
(1,632 lines). It is the pin's self-contained copy of the whole index prelude plus
the engine `exists_genus_riemannIndex_of_stichtenothGenusExists`; transcribe the
prelude from it in its own declaration order. The four target declarations are
spelled from their `Theorems/Thm_*` wrappers (checker rule, playbook §4):

| target | pin wrapper | pin body |
|---|---|---|
| `indexOfSpecialty_eq_of_genusReached` | `Theorems/Thm_AlgebraicCurve_indexOfSpecialty_eq_of_genusReached.lean` | `S_..._exists_genus_riemannIndex_of_stichtenothGenusExists.lean:1014` |
| `indexOfSpecialty_eq_zero_of_genusReached` | `Theorems/Thm_AlgebraicCurve_indexOfSpecialty_eq_zero_of_genusReached.lean` | `…:1002` |
| `RiemannGenusReachedAt.eq_of_ge` | `Theorems/Thm_AlgebraicCurve_RiemannGenusReachedAt_eq_of_ge.lean` | `…:970` |
| `omegaSpace_finite_of_genusReached` | `Theorems/Thm_AlgebraicCurve_omegaSpace_finite_of_genusReached.lean` | `…:1235` |
| `exists_genus_riemannIndex_of_stichtenothGenusExists` | `Theorems/Thm_AlgebraicCurve_exists_genus_riemannIndex_of_stichtenothGenusExists.lean` | `…:1616` |

The other files contributing one name each:
`S_..._RiemannGenusReachedAt_eq_of_ge.lean`, `S_..._indexOfSpecialty_eq_of_genusReached.lean`,
`S_..._indexOfSpecialty_eq_zero_of_genusReached.lean`,
`S_..._omegaSpace_finite_of_genusReached.lean`,
`S_..._exists_genus_riemannIndex_of_isCurveOver.lean`,
`S_..._weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists.lean`.

## 2. The union — collapsing the pin's duplicate copies

The pin's auto-generated files re-state the same development several times. The
appendix lists 75 names; **collapse these before writing**, they are not distinct
mathematics:

- `eq_of_ge_port` ≡ `eq_of_ge`; `indexOfSpecialty_eq_of_genusReached_port` ≡
  `indexOfSpecialty_eq_of_genusReached`; `indexOfSpecialty_eq_zero_of_genusReached_port` ≡
  `indexOfSpecialty_eq_zero_of_genusReached`; `omegaSpace_finite_of_genusReached_port` ≡
  `omegaSpace_finite_of_genusReached`; `stichtenothGenusExists_of_isCurveOver_port`
  is a port-named wrapper — write the target once and keep local aliases only where
  the checker needs the pin's spelling.
- `solution` (43 lines, in `S_..._weilDualityAdelic_…`) is the assembly proof body,
  not an index-prelude statement: **it is H2's**, not this set's. Do not land a
  bare `solution` here.
- `ord_nonneg_of_mem`, `mem_of_ord_nonneg`, `mem_iff_ord_nonneg` are **already in
  the port** (`Defs/PushPull.lean`) with identical statements — import them; a
  `port_advise` substitution confirms it.

Load-bearing declarations the rest of the engine imports (write these first, in
dependency order): `lSpaceShiftEquiv`, `ell_le_degree_add_ellZero`,
`ell_le_ell_sub_single_add_deg`, `finrank_adeleBdd_quotient`,
`finrank_adeleBddSup_quotient`, `lSpaceQuotientToAdeleBddQuotient`,
`range_lSpaceQuotientToAdeleBddQuotient`, `adeleBddQuotSingleEquivResidueField`,
`finiteDimensional_lSpace`, `residuePairing_surjective_of_rankOne_max`,
`exists_weilSmul_eq_of_genusReached`, `two_mul_ell_le_indexOfSpecialty`,
`weilDifferentialRankOne_of_genusReached`.

## 3. Route and risk

- **mathlib supplies proof ingredients, not the statements.** The audit
  (`AUDIT-mathlib.md`, landed) is the authority. In particular: `lSpaceShiftEquiv`
  should be built on mathlib's `Units.mulLeftLinearEquiv` (R2), leaving only the
  `LSpace D ↦ LSpace (D + Dg)` submodule compatibility bespoke; the four
  `Submodule` chain helpers (`finrank_quotient_chain`, `finrank_quotient_chain'`,
  `finrank_quotient_chain_top`, `comap_subtype_sup_of_le_of_le`) have **no packaged
  mathlib version** and stay port-local (R5); there is **no `Submodule.mapQ_injective`**,
  so `lSpaceQuotientToAdeleBddQuotient_injective` goes through
  `Submodule.Quotient.mk_eq_zero` as the pin does. The audit's §5.10 also corrects an
  earlier note: `Submodule.finrank_sup_add_finrank_inf_eq` is **not** used here.
  Other mathlib ingredients the pin calls: `Submodule.finrank_quotient_add_finrank`,
  `Submodule.quotientQuotientEquivQuotient`, `Submodule.comap_map_eq`,
  `Submodule.map_comap_eq`, `LinearEquiv.finrank_eq`, `Submodule.finrank_mono`,
  `Finsupp.le_def`, `Set.Finite.subset`, `Submodule.mem_iSup_of_directed`,
  `Submodule.equivMapOfInjective`.
- **Do not weaken a statement from a private copy.** The pin's `X_port` copies
  occasionally carry an extra hypothesis; spell the public target from the
  wrapper, and if a `_port` copy differs, take the wrapper's form.
- **Stop-early risks** (stop and report; do not inline a fix into this set):
  1. A declaration needs a Set D name that Set D did not land → report the pin
     `file:line`.
  2. A proof needs a tower lemma that belongs to H1b (`degree_sub_ell_le`,
     `ell_nsmul_*`, the `gate_*`/`stichtenothGenusExists_of_*` chain). The H1a
     partition already excludes the 2-file-only names; if the boundary is wrong,
     stop rather than inline.
  3. `Finsupp`/`Submodule.quotient` API drift needing more than a rename.
- Record a negative for every mathlib search that finds nothing.

## 4. Checker wiring, build discipline, verification

**Checker wiring** (append last, so a bare last-name match cannot flip):
- `SOURCES` += `P2M/Sol/S_AlgebraicCurve_exists_genus_riemannIndex_of_stichtenothGenusExists.lean`
  **after** the five `Theorems/Thm_*` wrappers of §1 (wrappers first: the target's
  binders come from the wrapper). Add
  `P2M/Sol/S_AlgebraicCurve_existence…`-style entries only for names the wrappers
  do not carry.
- `PORT_FILES` += `FLTForHuman/AlgebraicCurve/Genus/Index.lean`.
- Expected checker move: `identical` rises by the number of new public
  declarations; `0 mismatched / 0 missing`.

**Build discipline (copy in).** Edit loop
`timeout 120 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>`
(2,000+ line module — iterate individual declarations in `Scratch.lean`, never
re-check the whole file); file-done
`flock /tmp/flt_for_human.lock timeout 180 lake build FLTForHuman.AlgebraicCurve.Genus.Index`;
**one** `lake build` per wave; no whole-tree `lake build`; never raise the cap; no
`sorry`/`admit`/`axiom`; no `import Mathlib`; serialize with `flock`.

**Verification.**
```bash
cd lean
python3 spec/check_flt_statements.py
flock /tmp/flt_for_human.lock timeout 180 lake build FLTForHuman.AlgebraicCurve.Genus.Index
# #print axioms on indexOfSpecialty_eq_of_genusReached, omegaSpace_finite_of_genusReached,
#   RiemannGenusReachedAt.eq_of_ge, exists_genus_riemannIndex_of_stichtenothGenusExists
```

**Do not run any git command.**

## 5. Report shape

As `WORKORDER-D-defs.md` §5: module path + written lines; checker before → after;
bounded build wall time and command; friction-log entries (boundary stops,
collapsed duplicates, mathlib negatives, wrapper-vs-pin spellings, any `_port` copy
whose statement differs); `#print axioms` on the five headlines; explicit list of
anything not landed with pin `file:line`.

## Appendix — the H1a declaration list

`tools/deps/build/rr_homes.txt`, section `### H1a` (75 rows:
`span | kind | name | pin file:line`). The names in §2 must be collapsed; the rest
are the union to write once.
