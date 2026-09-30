# Phase 1 — the Riemann–Roch genus / index engine: port plan and set map

**Status: phase 1 COMPLETE (2026-09-29).** All 14 targets landed and checker-verified;
sets D, H1a, H1b, H2, H3, the refactor round and the R2 residual all ACCEPTED;
checker **2944 identical / 0 mismatched / 0 missing / 30 own-proof** (2974 checked);
full `lake build` green; `spec/RiemannRochConsumer.lean` 0 errors; all 14 headlines
`[propext, Classical.choice, Quot.sound]`. The blueprint `../PORTING-RR.md` is
retired to COMPLETE; the method record is
`../../logs/riemann-roch-friction.md`.

**Phase 2 (the canonical divisor) is COMPLETE (2026-09-30)** — see
`WORKORDER-P2-canonical.md` and `AUDIT-mathlib-p2.md`. New homes
`Defs/KaehlerTranscendental.lean` (94 ln: the two Kähler headlines) and
`Canonical/HasCanonicalDivisor.lean` (1,559 ln: the `hasCanonicalDivisor_of_isCurveOver`
construction, 140 rows incl. the six `instance`s the inventory tool drops). Checker
**3060 identical / 0 mismatched / 0 missing / 30 own-proof** (3090 checked); full
`lake build` green (4837 jobs); consumer 0 errors; headline + both Kähler theorems
`[propext, Classical.choice, Quot.sound]`. The manager gap round promoted the 47
pin-`p2m_export`ed declarations the worker had kept `private` (checker 3013 → 3060 on
the pin-private dotted-name fallback, no `OWN_PROOFS` addition), leaving 16 genuinely
pin-private helpers.

Pin `anthropics/fermats-last-theorem@aa2d8b3`; port mathlib `v4.34.0`. The
measured blueprint is [../PORTING-RR.md](../PORTING-RR.md); the measurement study is
[../../../studies/riemann-roch-strategy.md](../../../studies/riemann-roch-strategy.md).
This file is the *operative* plan: the set map, the homes, the budget, the route
audit and the verification recipe. Where it disagrees with the blueprint, this
file and the work orders are right.

Method: [../porting-playbook.md](../porting-playbook.md) §2 (plan), §3.4 (sets and
review gates), §3.5 (build ladder), §3.7 (porting order), §4 (faithfulness). The
precedent effort is [../PORTING-DeligneSerre.md](../PORTING-DeligneSerre.md) §2–§5.

## 0. What phase 1 is

The 14-node genus / index engine of the blueprint §1: Stichtenoth genus existence,
the `RiemannGenusReachedAt` / `indexOfSpecialty` API, `Ω`-finiteness, and the thin
assemblies producing `WeilDualityAdelic` (hence Riemann–Roch) and the Weil
canonical divisor. The target is the API 104 forward-cone nodes consume, not the
full RR family (study §5.2).

## 1. The measured cone, and the definition layer the blueprint omits

The blueprint's 12,262 raw lines are the 14 auto-generated `S_` files, which each
**inline a private prelude and import the pin's `Definitions/` modules**. Those
definition modules are not counted there but are prerequisites the port does not
yet have (verified: no `LSpace`, `ell`, `repartitions`, `riemannRochSpace`,
`adeleBdd`, `indexOfSpecialty`, `omegaSpace`, `genusFF`, `HasCanonicalDivisor`,
`ordDifferential` anywhere under `FLTForHuman/`).

`port_advise --with-defs` prices the full scope: **42 target files / 1,001
declarations**, 12,262 (`S_`) + 3,113 (14 definition modules) = **15,375 raw
lines**, 1,118 substituted, **8,584 removable** by dedup, → **≈5,700 projected
lines**. Budget ≈5,000–6,000 written lines, in sets (playbook §2.5).

*Caveat, recorded:* the tool's substitution matcher has false positives on
trivial `def … : Prop` declarations (it matches `RiemannInequality`,
`HasPoleDivisorPackage`, `WeilDualityAdelic`, … against
`EisensteinWeightOne.E1Chi3IsModular` with "19 copies"). Its 126 substitutions /
1,118 lines are therefore an **upper bound**; the real reuse is the
`Place`/`Divisor`/`PushPull`/`RatFuncPlaces` block the AC effort already ported
(≈60 real substitutions). Do not bank the false ones.

**Method finding (refactor round, confirmed).** The 14-`S_`-file measurement is
exact for the 14 *headlines* but a **lower bound on the checked surface**: target
proofs reach helper targets outside the measured file set.  Four were found and
promoted in the refactor round — `IsCurveOver.exists_separating_transcendental`
(curve-level prerequisite), `exists_indexOfSpecialty_nsmul_single_eq_zero_of_genusReached`
(a 15th helper target, H2) and
`weilOfKaehler_mem_omegaSpace_of_residueTheorem` /
`weilOfKaehler_ne_zero_and_maximal` (H3) — plus the H2 curve-level wrapper
`stichtenothGenusExists_of_isCurveOver`.  A future measurement should close over
the targets' **proof-reached public wrappers**, not just their own `S_` files.
See `logs/riemann-roch-friction.md` § Refactor round.

### 1.1 The shared prelude (dedup before coding)

`port_advise` on the 14 nodes (see PORTING-RR §5): 155 names proved in ≥2 target
files, 8,523 removable lines, union content ≈2,483 lines. Grouped by
copy-signature (`tools/deps/build/rr_prelude_groups.txt`):

| signature | names | what it is | home |
|---|---:|---|---|
| 7 files | 38 | adelic-quotient finiteness chain (`adeleBddQuotSingleEquivResidueField`, `ell_le_ell_sub_single_add_deg`, `finrank_adeleBdd*`, `lSpaceShiftEquiv`, `ell_le_degree_add_ellZero`, …) | `AlgebraicCurve/Genus/Prelude.lean` |
| 2 files | 80 | Stichtenoth genus-existence tower (`indexOfSpecialtyFinite_of_ratFunc_tower`, `gate_*`, `stichtenothGenusExists_of_*`, `ofTranscendenceTower`, …) | `AlgebraicCurve/Genus/Stichtenoth.lean` |
| 4 files | 15 | residue-pairing / `weilSmul` block | `Genus/Prelude.lean` (public) |
| 3 files | 12 | `degree_sub_ell_le`, `ell_nsmul_*`, bounded-genus gates | `Genus/Stichtenoth.lean` |
| singles (7–10 copies) | 10 | `mem_of_ord_nonneg`, `ord_nonneg_of_mem`, `mk_mem_maximalIdeal_iff`, … | `Genus/Prelude.lean` |

The union is written **once**, never `private` per consumer (playbook §2.4). The
pin's own two 2,545-line files share one prelude — the port writes it once.

## 2. The forward-import order and the sets

**The cut is by mathematical block, not by target.** Each `S_` file is ~99%
shared prelude: measured per-file unique content is 0–25 declarations / 0–249
lines (`tools/deps/build/rr_unique_per_file.txt`), and only 4 of the 14 targets
even appear in the shared-name list. So the port's real work is the **union** of
the prelude declarations — ~212 names / 3,218 lines once each — and the 14
targets are declarations inside that union or thin proofs resting on it. Porting
"one file per target" would re-write the union 14 times; the homes below write it
once.

```text
D    the pin Definitions/ modules                         (leaves, no cascade)
 └ H1  the shared prelude homes into NEW files             (no cascade)
    └ H2  the assembly and the thin targets                (imports H1)
       H3  canonical / Weil differential interface         (imports H1/H2)
```

The union splits by subject (line totals are once-each spans):

| block | content | ≈lines | home |
|---|---|---:|---|
| **H1a** | adelic-quotient / `ell` / index core: the 7-file 38-name group, the 4-file residue-pairing 15, the 3-file 12, and the singles; carries targets `indexOfSpecialty_eq_of_genusReached`, `indexOfSpecialty_eq_zero_of_genusReached`, `omegaSpace_finite_of_genusReached`, `eq_of_ge`, `exists_riemannGenusReachedAt_nsmul_single_…` | ≈1,500 | `AlgebraicCurve/Genus/Index.lean` |
| **H1b** | Stichtenoth tower: the 2-file 80-name group; carries `stichtenothGenusExists`, `finiteDimensional_lSpace_zero_of_constantsAreBase`, `exists_genus_riemannIndex_of_stichtenothGenusExists` | ≈1,000 | `AlgebraicCurve/Genus/Stichtenoth.lean` |
| **H2** | assembly / thin targets: `exists_genus_riemannIndex_of_isCurveOver`, `weilDifferentialRankOne_of_isCurveOver`, `weilDualityAdelic_of_…`, `exists_weilCanonical_riemannRoch`, `indexOfSpecialty_eq_finrank_H1` | ≈500 | `AlgebraicCurve/RiemannRoch/Assembly.lean` |
| **H3** | canonical / Weil differential: `exists_linearEquiv_regularDifferentials_omegaSpace_zero` + the `LocalResidue`/`WeilOfKaehler`/`RegularDifferentials` definitions (conditional on `ResidueTheorem`, `HasCanonicalDivisor`) | ≈500 | `AlgebraicCurve/Canonical/WeilDifferential.lean` |

The exact declaration→home assignment is generated mechanically
(`build/rr_prelude_groups.txt`) and frozen in each work order's appendix. H1a is
the prerequisite of H1b (the tower's gates cite the index core); H2 imports H1;
H3 imports H1/H2. One work order and one subagent per block; the manager reviews
before the next (playbook §3.4).

Real dependency edges among the 14 targets (from the pin graph; the rest are
independent and rest on the private prelude):

```text
exists_genus_riemannIndex_of_isCurveOver  -> stichtenothGenusExists, exists_genus_riemannIndex_of_stichtenothGenusExists
weilDifferentialRankOne_of_isCurveOver   -> stichtenothGenusExists
weilDualityAdelic_of_…                   -> indexOfSpecialty_eq_of_genusReached
exists_riemannGenusReachedAt_nsmul_single-> indexOfSpecialty_eq_of_genusReached, omegaSpace_finite_of_genusReached
exists_weilCanonical_riemannRoch         -> stichtenothGenusExists, indexOfSpecialty_eq_finrank_H1,
                                            indexOfSpecialty_eq_of_genusReached, weilDifferentialRankOne_of_isCurveOver
exists_linearEquiv_regularDifferentials  -> stichtenothGenusExists, weilDifferentialRankOne_of_isCurveOver
```

A frozen file is not reopened: resolve locally `private`, append to the friction
log, and let the final refactor round promote.

The 14 targets map onto the blocks as: H1a carries `indexOfSpecialty_eq_of_genusReached`,
`indexOfSpecialty_eq_zero_of_genusReached`, `omegaSpace_finite_of_genusReached`,
`eq_of_ge`, `exists_genus_riemannIndex_of_stichtenothGenusExists`,
`exists_riemannGenusReachedAt_nsmul_single_…`; H1b carries `stichtenothGenusExists`
and `finiteDimensional_lSpace_zero_of_constantsAreBase`; H2 carries the four thin
wrappers plus `indexOfSpecialty_eq_finrank_H1`; H3 carries
`exists_linearEquiv_regularDifferentials_omegaSpace_zero`.

## 3. Route audit (`rfl`-first; recorded negatives)

* **Already in the port and must be imported, not re-proved** (verified by
  substitution): `Defs/Place.lean` (the `Place` structure, `ord`, `adicValuation`,
  `deg`, residue field), `Defs/Divisor.lean` (`Divisor`, `degree`, `degZero`,
  `IsPrincipal`, `principal`, `HasPrincipalDivisors`, `Pic0`), `Defs/PushPull.lean`
  (`Divisor.pullback` and the fibre dictionary), `Defs/RatFuncPlaces.lean`
  (`placeInfty`), `Defs/PlaceDictionary.lean`, `WeilExchange/*`.
* **mathlib supplies the algebraic primitives the pin's definitions call**:
  `ValuationSubring`, `IsDiscreteValuationRing.exists_irreducible`,
  `HeightOneSpectrum`, `KaehlerDifferential.D`, `Submodule.dualAnnihilator`,
  `Submodule.dualQuotEquivDualAnnihilator`, `Subspace.dual_finrank_eq`,
  `Submodule.equivMapOfInjective`, `Module.Finite`, `Submodule.finrank_quotient_add_finrank`.
  The definitions layer is therefore **transcription plus elaboration**, not new
  mathematics.
* **Recorded negatives (audit complete: `AUDIT-mathlib.md`, 136 rows / 5
  SUBSTITUTE / 78 PROOF-INGREDIENT / 53 BESPOKE).** mathlib has **no `genus` at
  all** (no curve/function-field genus), no `RiemannRoch`, no function-field
  `repartitions`/`LSpace`/`ell`/`indexOfSpecialty`/`omegaSpace`/`canonicalDivisor`/
  `differentialCoeff`. Correction to the first pass: `IsDedekindDomain.FiniteAdeleRing`
  *is* generic over Dedekind domains, but it is a restricted product of
  **completions** over `HeightOneSpectrum R` with no bounded/quotient/index API and
  no relation to the pin's completion-free repartitions. Also absent:
  `Submodule.mapQ_injective`, `Submodule.comap_subtype_sup_of_le_of_le`,
  `Submodule.finrank_quotient_chain`/`_top`, `Algebra.adjoin_eq_self`; and the
  seeded `Submodule.finrank_sup_add_finrank_inf_eq` is **not used** here. The pin's
  `indexOfSpecialty` is an *adelic* index, not by definition `ell (K − D)`; the
  identification with `H¹` is `indexOfSpecialty_eq_finrank_H1` (H2), a consequence
  to prove, not an unfolding.
* **Reuse wins (all `rfl`/`exact`-checked).** `omegaSpace = Submodule.dualAnnihilator`
  and `omegaSpaceEquivIndexDual = Submodule.dualQuotEquivDualAnnihilator` (`rfl`);
  `adeleBdd_le_adeleSpace`/`omegaSpace_le_weilDifferentialModule` are `le_iSup`;
  `diagonal_mem_globalSub` is `LinearMap.mem_range_self`. One-mathlib-call proofs
  (statement kept, pin body dropped): `exists_eq_smul_dCoord`,
  `differentialCoeff_*`, `dCoord_ne_zero`, `instNontrivialKaehler`,
  `deg_eq_one_of_isAlgClosed_of_finite`, `finrank_omegaSpace_eq_indexOfSpecialty`,
  `ell_sub_le_indexOfSpecialty`, `ell_zero_eq_one_of_constantsAreBase`,
  `finrank_adeleBdd_inf_global_eq_ell`, `mem_adeleSpace_iff`,
  `mem_weilDifferentialModule_iff`, `finiteDimensional_lSpace_zero_of_constantsAreBase`.
* **Route options (design decisions, not deletions):** R1 `differentialCoeff` via
  `FiniteDimensional.basisSingleton`; R2 `lSpaceShiftEquiv` via
  `Units.mulLeftLinearEquiv`; R3 the `repartitions` carrier via mathlib
  `RestrictedProduct` (ring part only — no mathlib `Algebra F`/pointwise `Module F`,
  so the `F`-algebra glue stays bespoke); R4 the index block is
  `dualQuotEquivDualAnnihilator` + `Subspace.dual_finrank_eq`; R5 the four
  `Submodule` chain helpers stay port-local.
* **The genuinely new piece** is the Stichtenoth genus-existence construction
  (`Genus/Stichtenoth.lean`, H1b). It is the scout gate (playbook §2.6): prototype
  the `TranscendenceTower`/`PoleDivisorPackage` → `HasIntegralBasisInLSpace` →
  `RiemannGenusBounded` chain in `Scratch.lean` before dispatching H1b in full. The
  pin proof looks like transcription (the `S_` file is the pin's own proof), so the
  scout is expected to convert "new mathematics" into "transcription" — record the
  pre/post estimate either way.

## 4. Risk register (named shape risks, in the order they will bite)

| risk | mitigation | status |
|---|---|---|
| `Place`/`Divisor` statement drift between pin `DivisorClassGroup` and the port's `Defs/` | import the port's copy; `port_advise` substitution check before writing; the checker is the arbiter | open (D) |
| `indexOfSpecialty` carrier: the pin's `adeleSpace ⧸ adeleBddPrincipal` vs `H1` (`repartitions ⧸ repartitionsOf ⊔ principalRepartitions`) | keep both carriers; `indexOfSpecialty_eq_finrank_H1` is the bridge, assigned to S3 | open (S3) |
| the pin's `placeInfty`/`RatFunc` tower support (`ord_placeInfty`, `deg_placeInfty`, `exists_separating_transcendental`) is only partly ported | D/S1 workers stop at the boundary and report; a focused later dispatch ports the missing wrapper | open (S1) |
| binder drift on the public targets (`eq_of_ge`, `indexOfSpecialty_eq_zero_of_genusReached`, `finiteDimensional_lSpace_zero_of_constantsAreBase`, `stichtenothGenusExists` have 2 statements each in the pin pool) | spell every public statement from the `Theorems/Thm_*` wrapper, not the `S_` file (playbook §4.1) | open |
| long S1 module (2,500 lines) | edit loop in `Scratch.lean`; per-declaration probes; `lake env lean` bound 120 s | open |
| predicate false positives in `port_advise` substitutions | do not bank; verify each with the checker | recorded |

Predicted non-events (not budgeted): an instance diamond in `IsCurveOver`
(`HasPrincipalDivisors` extension is the pin's own shape), and defeq trouble
between `adeleBdd` and `repartitionsOf` (different carriers, connected by explicit
lemmas, not `rfl`).

## 5. Verification (per set, and the milestone)

```bash
cd lean
python3 spec/check_flt_statements.py                    # 0 mismatched / 0 missing
flock /tmp/flt_for_human.lock timeout 90  lake build <module>
flock /tmp/flt_for_human.lock timeout 120 \
  lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>
```

Build discipline (copy into every work order): `lake env lean` needs
`-DmaxHeartbeats=4000000 -DautoImplicit=false`; one `lake build` per wave,
serialized with `flock` and bounded with `timeout`; never raise the cap. At the
milestone: full `lake build`, the consumer `spec/RiemannRochConsumer.lean` with one
executed RR zone per set, `#print axioms` over the 14 headlines, and a `grep` sweep
for `sorry`/`admit`/`axiom`/`import Mathlib`/heartbeat overrides.

**Wave-target caveat (recorded).** `lake build FLTForHuman.AlgebraicCurve` is **not**
a target — there is no `FLTForHuman/AlgebraicCurve.lean` facade. Name the module
list (`FLTForHuman.AlgebraicCurve.{Genus.Index,Genus.Stichtenoth,RiemannRoch.Assembly,
Canonical.WeilDifferential,IsCurveOver.SeparatingTranscendental,Defs.WeilOfKaehler,
Defs.Divisor,Defs.CanonicalDivisor,Defs.CanonicalDivisorUniformizer}`), or build the
whole library target `FLTForHuman`, which does exist.

Baseline before the effort: **2552 identical / 0 mismatched / 0 missing / 30 own-proof
exempted**.

## 6. Reproduce

```bash
cd tools/deps
# the 14-node reading (phase-1 targets only)
python3 port_advise.py --nodes "$(cat build/stich_engine_nodes.txt)" \
        --json build/stich_advise.json
# the full phase-1 scope including the definition layer
python3 port_advise.py --nodes "$(cat build/stich_engine_nodes.txt)" --with-defs \
        --json build/stich_advise_defs.json
# the prelude copy-signature groups (the homes table of §1.1)
python3 - <<'PY' > build/rr_prelude_groups.txt
import json
from collections import defaultdict
d=json.load(open('build/stich_advise.json'))
f=[r for r in d['factor'] if r.get('in_target_pair')]
sig=defaultdict(list)
for r in f:
    sig[tuple(sorted({o['module'] for o in r['occurrences']}))].append(r)
for mods,rows in sorted(sig.items(), key=lambda kv:(-len(kv[1]),-len(kv[0]))):
    print(f"### signature: {len(mods)} files, {len(rows)} names")
    for m in mods: print("    -",m)
    for r in sorted(rows,key=lambda r:-r['removable']):
        o=r['occurrences'][0]
        print(f"    {r['removable']:5}  {o['span']:4}  {r['kind']:9} {r['name']}   ({o['module']}:{o['line']})")
    print()
PY
# the per-target S_ lines and the frontier split
python3 - <<'PY'
import frontier, os
fr=frontier.Frontier(); pay=fr.pay; front=fr.frontier('union')
for n in open('build/stich_engine_nodes.txt').read().strip().split(','):
    i=pay.pid(n); print('P' if i in front else 'N', fr.lines(i), n)
PY
```

## 7. Close-out status

1. **Refactor round — DONE** (`WORKORDER-R-refactor.md`): the four proof-reached
   gaps are closed publicly — `IsCurveOver.exists_separating_transcendental` in
   `AlgebraicCurve/IsCurveOver/SeparatingTranscendental.lean`,
   `exists_indexOfSpecialty_nsmul_single_eq_zero_of_genusReached` in
   `Genus/Index.lean`, the two Weil-differential helpers in `Defs/WeilOfKaehler.lean`
   — plus `stichtenothGenusExists_of_isCurveOver`; R3's private-layer review, R4's
   `Pic` move and R5's `uniformizer` unification are in
   `logs/riemann-roch-friction.md` § Refactor round. Checker 2920 → 2942.
2. **Consumer wire test — NEXT** (`spec/RiemannRochConsumer.lean`; playbook §4.2):
   one executed cross-module zone per set — Set D (definitions instantiated), H1a
   (the index API applied), H1b (the tower/genera applied), H2 (`WeilDualityAdelic`
   composed from `FunctionFieldRiemannRoch`), H3 (the conditional differentials
   interface at abstract hypotheses). Real executed compositions, no `#check`s;
   deleting any one module must make it fail. The manager writes this one (it is the
   review instrument).
3. **Milestone gate:** full `lake build FLTForHuman` (or `lake build`, whole tree),
   `#print axioms` over all 14 headlines, checker `0 mismatched / 0 missing`, a
   `grep` sweep for `sorry`/`admit`/`axiom`/`import Mathlib`/heartbeat overrides,
   and retire the blueprint status in `../PORTING-RR.md`.

**Known residual — CLOSED** (`WORKORDER-R2-ratfunc-promote.md`):
`Place.eq_ofHeightOneSpectrum_or_eq_placeInfty` and
`Place.placeInfty_ne_ofHeightOneSpectrum` are now public and pin-named in
`PrincipalDivisors/RatFuncDegree.lean`, with their two `Theorems/` wrappers wired
into the checker's `SOURCES`, and the Stichtenoth private rebuilds deleted. Checker
2942 → 2944. The one drift found on promotion was the pin's explicit `(K : Type*)`
binder on `placeInfty_ne_ofHeightOneSpectrum` (the port had `{K : Type*}`); it was
corrected to the pin's form under manager authorization. See
`logs/riemann-roch-friction.md` § Refactor round (R2 follow-up).
