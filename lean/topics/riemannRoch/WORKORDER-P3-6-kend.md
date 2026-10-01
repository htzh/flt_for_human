# Work order — row 6 (K ending): `residueTheoremK_of_isAlgClosed` and its `RatFunc` headline

**Status: ready to dispatch.** Row 6 of [../PORTING-RR.md](../PORTING-RR.md) §3 (the
**K ending**); method [../porting-playbook.md](../porting-playbook.md) §2–§5; build
economy [../PORTING-DeligneSerre.md](../PORTING-DeligneSerre.md) §3. Read
[WORKFLOW.md](WORKFLOW.md) first.

Baseline: checker **4071 identical / 0 mismatched / 0 missing / 30 own-proof**
(4101 checked). Pin `anthropics/fermats-last-theorem@aa2d8b3`; mathlib `v4.34.0`.

## 0. Scope

Row 6 is the **K ending**: the general-curve producer of `ResidueTheoremK`, plus the
`RatFunc` specialisation. **Two public headlines**, each spelled from its `Thm_`
wrapper:

| target | wrapper (statement authority) | body |
|---|---|---|
| `AlgebraicCurve.residueTheoremK_ratFunc_of_isAlgClosed` | `Theorems/Thm_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean` | `P2M/Sol/S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean` (`solution`) |
| `AlgebraicCurve.residueTheoremK_of_isAlgClosed` | `Theorems/Thm_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean` | `P2M/Sol/S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean` (`solution`, pin 8082) |

**The measured residual is one worker.** `port_advise` (reproduce in §5) on the two
targets:

| file | raw | substitutions | residual (name/once-each) | genuinely new |
|---|---:|---:|---:|---:|
| `_ratFunc` | 13,170 | 454 ≈ 9,760 ln | 133 / 3,253 ln | **1 name / 5 ln** |
| `_of_isAlgClosed` | 8,121 | 130 ≈ 4,211 ln | 113 / 3,995 ln | **67 names / 2,858 ln** |
| union | 21,300 | — | 208 / 6,247 ln | 68 / 2,863 ln |

The `_ratFunc` residual is **adapters** (the port has the same mathematics under its
`p1PlaceInfty` spelling or different binders) and its `solution` is a **one-liner**:

```lean
-- pin S_ ..._ratFunc_of_isAlgClosed.lean, `solution`
theorem solution (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)] … :
    ResidueTheoremK K (RatFunc K) :=
  AlgebraicCurve.p0n22_cpf_residueTheoremK_ratFunc_of_isAlgClosed_main K
```

and `p0n22_cpf_residueTheoremK_ratFunc_of_isAlgClosed_main` **is already in the port**
(`FLTForHuman/AlgebraicCurve/P1/Core.lean:753`). So the `_ratFunc` target is a
statement-only wrapper; the real work is the general-curve file's 67 new declarations
(the cotrace/Kähler-cotrace residue machinery and its assembly).

**Explicitly out of scope:** row 3.5 (the perfect-field ending), row 3.7 (the RR
assembly `functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed` — pin
5971–6257), the `_v2` twins, and the PF-side names.

## 1. Deliverables

New modules; **no existing module is edited** (so no cascade):

| module | content |
|---|---|
| `FLTForHuman/AlgebraicCurve/ResidueTheorem/KRatFunc.lean` | the `residueTheoremK_ratFunc_of_isAlgClosed` public headline (wrapper-spelled) |
| `FLTForHuman/AlgebraicCurve/ResidueTheorem/KFamily.lean` | the general-curve ending: the residual declarations of `S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean` (the 67 new + the adapters the proofs reach) and the `residueTheoremK_of_isAlgClosed` public headline |

`ResidueTheorem/` is the home [../PORTING-RR.md](../PORTING-RR.md) §3 names. A third
module is allowed if the 67 new declarations split cleanly at a namespace boundary
(e.g. `KFamily.lean` + `KCotrace.lean`); keep a linear import chain.

## 2. Statements

Spell each public statement **verbatim from its `Thm_` wrapper**, explicit binders
included (the checker diffs the declaration text after the name; §4 of the friction
log records this trap). The two statements, copied from the wrappers:

```lean
theorem AlgebraicCurve.residueTheoremK_ratFunc_of_isAlgClosed
    (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K (RatFunc K)]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := RatFunc K)]
    [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates] :
    AlgebraicCurve.ResidueTheoremK K (RatFunc K)

theorem AlgebraicCurve.residueTheoremK_of_isAlgClosed
    {K F : Type*} [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
    [Field F] [Algebra K F]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    [∀ w : AlgebraicCurve.Place K F, w.DCoordGenerates]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
    [AlgebraicCurve.HasLocalResidue K F]
    [∀ w : AlgebraicCurve.Place K F, w.FiniteResidue]
    [Nontrivial Ω[F⁄K]]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver K (RatFunc K)]
    [∀ u : AlgebraicCurve.Place K (RatFunc K), u.FiniteResidue]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K F]
    [AlgebraicCurve.HasPrincipalDivisors K F] [Algebra.IsSeparable (RatFunc K) F]
    [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates] :
    AlgebraicCurve.ResidueTheoremK K F
```

(The two statements above are copies of the wrapper files — copy the files, do not
retype.)

The wrapper hypotheses are largely **redundant in the port** (`HasCanonicalDivisor`
and `HasCanonicalLocalResidueKStar` are unconditional for curves, `P1/Differential.lean`
has the `RatFunc` `HasPrincipalDivisors` instance, etc.), but the binder block must
stay; discharge unused ones by instance search / `haveI` inside the proof.

## 3. Reuse and the mathlib audit

**Do the mathlib audit first** (playbook §2.2) and write
`AUDIT-mathlib-p3-6.md` beside the port. Leads that the port already pays for:

- `_ratFunc` headline: `AlgebraicCurve.p0n22_cpf_residueTheoremK_ratFunc_of_isAlgClosed_main`
  (`P1/Core.lean:753`), directly.
- general-curve assembly: the pin's `solution` calls
  `ModularCurve.KwTateRR3.kwTateRR3_residueTheoremK_of_isAlgClosed`
  (pin 8082) which is
  `kw_es_residueTheoremK_of_RTCC_isAlgClosed' (kwTateRR3_RTCC_of_isSeparable (E := RatFunc K))`;
  the port's `AlgebraicCurve.residueTraceCompletionCommute`
  (`Tate/TraceCompletionCommute.lean`) **is** the pin's `kwTateRR3_RTCC_of_isSeparable`
  (byte-identical statement), so import it.
- the shared engine: `P1/Core.lean`, the `P1/` chain, `LocalResidue/Calculus.lean`
  (`p0n22_cpf_*`), `Tate/{CommFinite,Agreement,TraceCompat,Prelude,TraceCompletionCommute,CompletionTraceSum}.lean`,
  `Canonical/HasCanonicalDivisor.lean` (`hasCanonicalDivisor_of_isCurveOver`),
  `LocalResidue/Instance.lean` (`instHasCanonicalLocalResidueKStar`).
- `Place/Completion.lean` (the `InlineSpecific` chain) and the R8 refactor round.

**Measurement traps (corrected by the worker's interim #1, 2026-09-30).** `port_advise`
marks **ten** `def … : Prop` as substitutions to `EisensteinWeightOne.E1Chi3IsModular`
(the known false positive: the checker sees only a `def`'s signature). Of these the port
genuinely has, public: `OrdDifferentialWellDefined` (`P1/EnginePrelude.lean:102`, same
statement), `KaehlerRankOne` and `RamificationInertiaIdentity` (`P1/DXCoeff.lean`). The
rest are **new** here: `CotraceFiberLocalizedPolarApprox` (S_ 5034),
`CotraceResidueIdentityOnFiberLocalized` (5024), `FiberKaehlerCotraceResidueIdentity`
(4278), `IsSeparatingTranscendental` (4672), and
`KwF4R1V384a{CompletionSemilocalBij,DistinctKernels,FinrankCompletionEF}` — the last
three exist only as `private` defs in `Tate/CompletionTraceSum.lean:269/282/288`, so
re-land them locally `private` at the pin names and report the promotion debt.

`IsSeparatingTranscendental` is **not** the port's `HasSeparatingTranscendental`
(`Canonical/HasCanonicalDivisor.lean:918`, the ∃-transcendental form): the pin row-6 def
is `KaehlerDifferential.D K F (algebraMap (RatFunc K) F RatFunc.X) ≠ 0`. Define it at
the pin body; do not alias.

**`placeInfty` vs `p1PlaceInfty`.** The port's ℙ¹ chain spells the place
`p1PlaceInfty` (`@[reducible] def p1PlaceInfty := placeInfty K`), while the row-6
files spell the pin's `placeInfty`. 45 residual names / 1,023 ln are these twins:
statements are definitionally equal but not textually identical, so the checker wants
the pin's `placeInfty` spelling. State them at `placeInfty` and prove from the port's
`p1` lemmas via `change`/`simpa [p1PlaceInfty]` — do not re-prove.

**Stop-early protocol.** If a proof reaches a declaration outside the measured files,
resolve it locally `private` with the statement verbatim, report the pin `file:line` as
promotion debt, and **do not edit a frozen module**. The R5/R8 debt is closed; do not
re-open it.

## 4. Build discipline (verbatim, [../PORTING-DeligneSerre.md](../PORTING-DeligneSerre.md) §3)

- every set lands in **NEW** files; nothing imports them yet, so they cannot cascade;
- edit loop: `timeout 120 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>`;
- `flock /tmp/flt_for_human.lock timeout 240 lake build <module>` when a file is done;
- **no whole-tree build** during the set; one at the milestone;
- never raise the heartbeat cap; no `sorry`/`admit`/`axiom`; no bare `import Mathlib`.

## 5. Checker wiring and verification

Append **last** (order disambiguates same-last-name collisions):

- `SOURCES +=` `Theorems/Thm_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean`,
  then `P2M/Sol/S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean`; then
  `Theorems/Thm_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean`, then
  `P2M/Sol/S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean`.
- `PORT_FILES +=` the new modules.

Verify:

```bash
cd lean
python3 spec/check_flt_statements.py                    # 0 mismatched / 0 missing
flock /tmp/flt_for_human.lock timeout 900 lake build FLTForHuman.AlgebraicCurve.ResidueTheorem.KFamily
flock /tmp/flt_for_human.lock timeout 300 lake build FLTForHuman.AlgebraicCurve.ResidueTheorem.KRatFunc
lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false spec/RiemannRochConsumer.lean
# #print axioms on the two headlines; hygiene grep; .olean mtimes
```

Reproduce the measurement:

```bash
cd tools/deps
python3 port_advise.py --target P2M/Sol/S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean \
        --json build/row6_kend_advise.json > build/row6_kend_advise.log 2>&1
python3 port_advise.py --target P2M/Sol/S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean \
        --json build/row6_ratfunc_advise.json > build/row6_ratfunc_advise.log 2>&1
```

The 67 genuinely-new general-curve declarations, with pin line and span, are in
`tools/deps/build/row6_new.tsv` (generated by the manager; the worker should regenerate
it and take `--drags-full` itself). Largest: `gf24a9r_cotraceFiberLocalizedPolarApprox` (152),
`finsum_place_eq_finsum_fiber_sum` (121), `kaehlerCotrace_smul_algebraMap` (113),
`differentialCoeff_kaehlerPullback` (109), `exists_mem_regularPoleSubmodule` (107),
`cotraceResidueIdentityOnFiberLocalizedK_of_committed` (107),
`kw_mlc_hrtCharP7_kaehlerPullback_smul` (99),
`kaehlerResidueTerm_kaehlerPullback_diagonal_eq_dCoord_shift` (99),
`kwHgfV352_localResidueCompletion_sum` (97).

## 8. Closeout — ACCEPTED (manager, 2026-09-30)

Three new modules, 1,689 ln, **no existing module edited** (the worker's whole tree
diff is the three new modules + the checker wiring + the audit):

| module | ln | content |
|---|---:|---|
| `ResidueTheorem/KRatFunc.lean` | 32 | `residueTheoremK_ratFunc_of_isAlgClosed` (wrapper verbatim; proof `p0n22_cpf_…_main`) |
| `ResidueTheorem/KCotrace.lean` | 760 | the four `Prop` rows, `regularPoleSubmodule` family, `mem_regularSubmodule`, the Kähler-cotrace bridge, `Cotpk43T3.*`, `gf24a9r_*`, `differentialCoeff_kaehlerPullback`, `kw_mlc_hrtCharP7_*` |
| `ResidueTheorem/KFamily.lean` | 897 | the assembly (`p0n22_cpf_…`, K-currency row, rowAK, dataKStar seam, alg-closed discharge, committed tower, FKCRI wire+production, completion sum, dCoord shift, trace linearity, RTCC+CTS, `kw_es_*`, `kwTateRR3_*`) and the public `residueTheoremK_of_isAlgClosed` (wrapper verbatim) |

Independently re-verified by the manager (not the worker's report):

- checker **4071 → 4144 identical / 0 mismatched / 0 missing / 30 own-proof**
  (4101 → 4174 checked); `promoted` 133 → 150.
- forced per-module `lake build` green (deleted the three `.olean`s and rebuilt);
  only the three new `.olean`s moved. No whole-tree build; nothing imports them, so
  the cascade is zero by construction.
- `#print axioms` on both headlines plus `kwTateRR3_residueTheoremK_of_isAlgClosed`,
  `p0n22_cpf_residueTheoremK_ratFunc_of_isAlgClosed`,
  `residueTheoremK_of_cotraceResidueIdentityK` → `[propext, Classical.choice,
  Quot.sound]`.
- hygiene clean; `spec/RiemannRochConsumer.lean` exits 0; both headline statements read
  against their wrappers (verbatim).

**Deviation accepted.** The worker did not re-land the pin's three
`KwF4R1V384a{CompletionSemilocalBij,DistinctKernels,FinrankCompletionEF}` (`def … :
Prop`). They are pin-public, but their enclosing `KwF4R1V384a` block is
import-discharged through the port's public
`AlgebraicCurve.completionTraceSum_of_isSeparable`, so copies would be dead code.
Recorded as a **disposition (subsumed)**, not open debt. (The pin does mention them
inside its own 384a block, so the worker's "no body mentions them" phrasing was
imprecise; the net conclusion holds.)

**Boundary notes recorded.** `IsSeparatingTranscendental` (pin 4672) is a distinct def
from the port's `HasSeparatingTranscendental` (existential form); landed at the pin
body. The port's `def ResidueTheoremK` (`Defs/LocalResidue.lean:320`) carries an extra
auto-bound `[∀ v, v.DCoordGenerates]` in its elaborated signature absent from the pin's,
so theorems mentioning `ResidueTheoremK K E` list it as a section variable (source text
unchanged).

Row 6 is complete. Rows 3.5 (PF ending) and 3.7 (RR assembly) remain.
