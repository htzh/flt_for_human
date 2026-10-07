# P-3 work order — the two-curve countable descent (set D-6)

**Status: drafted 2026-10-06, for dispatch.** Pin `anthropics/fermats-last-theorem@aa2d8b3`;
port mathlib `v4.34.0`. Depends on the P-2 column, all landed: D-1 (`Isogeny/BaseChange.lean`),
D-2 (`Isogeny/IntermediateField.lean`), D-5 (`Isogeny/KernelBaseChange.lean`). Method:
[../../porting-playbook.md](../../porting-playbook.md) §0.2, §2.4–§2.5, §3.1–§3.5, §3.7, §4–§5.

**Why this set exists.** `frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen
--rank-by silo --ready` ranks
`WeierstrassCurve.Affine.exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward`
first, at 3,729 silo lines, with an unported closure of **0** — because P-2 landed all
eighteen of its cited premises. It is the D row restated in two-curve form, and the finding
is registered in [../../CARRY-FORWARD.md](../../CARRY-FORWARD.md) under "A row can surface
again as a fresh silo". This set lands what the node's *demand* actually needs without
porting its silo.

## 1. Scope

Land the **two-curve countable descent** and, on top of it, the headline

```
WeierstrassCurve.Affine.exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward
```

Given an isogeny `ι : E'.FunctionField →ₐ[K] E.FunctionField` between two elliptic curves
over an algebraically closed char-0 field, with `ι` integral and finite, and given that the
kernel of the pushforward point map is cyclic of cardinality `N`, produce a **countable**
`K₀ ≤ K`, models `E₀`, `E₀'` of `E`, `E'` over `K₀`, and a descended `ι₀` over
`AlgebraicClosure K₀` such that — for *every* admissible gate data on the base-changed
curves — the kernel is cyclic with cardinality `N`.

This is the only prerequisite of the S/D capstone
`eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward` (415 lines)
that P-2 left unported. Its sole consumer in the whole pin is that capstone.

**Not this set:** the S row (`exists_differentiable_toPoint_comp_…`,
`exists_scale_lattice_…`, `exists_mem_primCosetReps…`, `IsAddCyclic.of_squarefree_natCard`),
the `rationalHomSet`/torsion columns, and the capstone itself —
`eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward` is the
**next** set and must not be ported here. A worker who reaches an unported prerequisite
stops at the boundary and reports.

## 2. Source and the dedup, measured

- `P2M/Sol/S_WeierstrassCurve_Affine_exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward.lean`
  (3,729 lines, 183 declarations).
- Statement authority: `Theorems/Thm_WeierstrassCurve_Affine_exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward.lean`
  (41 lines) — spell its binders **exactly**, including the `letI : Algebra ℚ K` in the
  statement and the `∀ [DecidableEq (AlgebraicClosure K₀)] [gate instances …] (hN₀)` block
  of the conclusion (that block is load-bearing; §3).

`port_advise --nodes …` and `port_plan` on the file report:

```
raw S_ lines                                 3,729
  − boilerplate (imports/attrs/p2m)            −53
  − duplicate copies within the file           −21
  = distinct declaration lines               3,655
  − already in the port (statement-matched) −1,680
  NET NEW (the tool's figure)                1,975
substitutions: 76 trusted / 31 suspect
```

Three corrections to that figure, all measured:

1. **The tool under-counts the reuse.** Its statement test cannot see the base-change engine
   `kw_surgehgf4_hfgkd_bc*` (`:2519–2839`, ~320 lines) because the pin renamed the token
   *and* the binders (`hfin'`/`ι'` against D-5's `hfin₀`/`ι₀`); only four lines matched, by
   type. That block is D-5's landed `kw_surge_hgf4_bc*` in `KernelBaseChange.lean`, and it is
   **imported, not re-proved**.
2. **The pin's proof staging is not ported.** The `KwD5*`/`KwD5BC*` class chain and the
   `s13GlobalGate` device are the pin's own scaffolding for a staged proof; §3 explains why
   the port does not land them. ≈290 raw lines.
3. At source level, **62%** of the file's substantive lines are verbatim in the five pin
   files P-2 landed (41% in the D-2 `S_` file alone, 47% in each D-5 silo).

After (1) and (2): **≈1,400 raw** lines that a transcription would write. Because the
descent layer is an adaptation of D-2's *promoted* helpers rather than fresh text, the
working estimate is **600–900 written lines** plus a 25-declaration promotion set. Re-price
this range after the pre-flight stub (§6).

Region table (`A` = the pin file above):

| lines | contents | disposition |
|---|---|---|
| 1–600 | imports, attributes, the place dictionary: `CoordinateRing.*`, `IsFinitePlace.*`, `placeOfEquation*`, `InfinitePlace.*`, `placeOfPoint_*` | ported (`Place/Dictionary.lean`, `IsogenyEndDatum/Engine.lean`) — **import** |
| 603–680 | `s13_exists_gate`, the `s13GlobalGate*` scoped instances, `s13DecEqAlgebraicClosure`, `adjoin_yCoord_eq_top`, `s13_finiteDimensional_ratFunc_functionField` | `s13_exists_gate` wraps the ported `exists_genusOnePlaceGate_isCentred_and_abelTheorem`; `adjoin_yCoord_eq_top` / `finiteDimensional_ratFunc_functionField` / `isIntegral_yCoord` are **already ported** (`WeierstrassCurve/FunctionFieldFinite.lean`, `FunctionFieldQuadratic.lean`) — import. The `s13GlobalGate*` device is **not landed** (§3) |
| 690–1790 | the `AlgebraicCurve`/place prelude and the `pointPullback*`/tensor base-change block | ported (D-1 `BaseChange.lean`, `Place/*`, `AlgebraicCurve/*`) — **import** |
| 1799–2386 | `kw_iA_*`, `kw_iCa_*`, `kw_iPFA_*`, `kw_iPFE_*`, `kw_fdn2_…countable_of_fg` | **D-2**, `IntermediateField.lean`, but `private` there — **promote** (§4.1) |
| 2292–2386 | `kw_iotaDescent{Curve_map_FF, Phi_equation, Phi_transcendental, Phi, Phi_X, Phi_yGen}` | **new** (~45); the pin's public spelling of the descent map — the port has none (`grep -c iotaDescent` = 0) |
| 2389–2441 | `KwD5BetweenCurvesSubfieldDescent`, `…KerDescendAlgClosed` | pin staging — **not landed** (§3) |
| 2446–2500, 2984–2992 | `…bcFGDescent_of_two` / `_of_three` | pin staging — **not landed** |
| 2501–2839 | `kw_surgehgf4_hfgkd_bc*` engine | **D-5** `KernelBaseChange.lean` at the `kw_surge_hgf4_bc*` names — **import** |
| 2844–2877 | `KwD5BetweenCurvesKerTransportAlongEmbed`, `…ChiCompChiEqPhi` | the first is **D-5** (import); the second is pin staging — not landed |
| 2886–2992 | `…hKD_of_kerTransport` | inlined into the headline proof (§3) |
| 3025–3380 | `kw_surgehgf4_hSD_*` — the two-curve descent | **new** (~410), built from §4.1's promoted helpers |
| 3389–3435 | `KwD5BCSubfieldDescent{Pinned,Canonical}FinrankEq`, `…hSD_of_canonicalFinrankEq` | inlined; the finrank equality is **D-5's** `kw_surge_hgf4_bcIota₁_finrankAlong` + the identification (§5) |
| 3435–3630 | `…chiCompChiEqPhi_proved`, `kw_surgehgf4_cfe_*` | inlined (~60 after reuse) |
| 3661–3729 | `s13_stub_ktd`, `s13_bcFGDescent`, `solution` | the headline's assembly; `stub_ktd` is a 12-line call into D-5's landed headline |

## 3. The one route decision the pin forces, and the port's answer

The pin stages the proof through four `Prop`s — `KwD5BetweenCurvesSubfieldDescent`,
`…KerDescendAlgClosed`, `…ChiCompChiEqPhi`, `…FGFieldDescent` — and canonicalizes the ambient
gate instances with a global `scoped instance s13GlobalGate : GenusOnePlaceGate W`, whose
only proof is the producer `exists_genusOnePlaceGate_isCentred_and_abelTheorem`.

That device is **unavailable in the port**: the producer lives in
`WeierstrassCurve/GenusOnePlaceGateCentred.lean`, which imports `Place/RRSpace.lean`, whose
`scoped instance instInfinitePlace` collides at the name level with
`IsogenyEndDatum/Engine.lean`'s `instInfinitePlace` — and this set needs `Engine.lean` through
`KernelBaseChange.lean`. No environment imports both
([../../CARRY-FORWARD.md](../../CARRY-FORWARD.md), "A co-import collision can be a
*producer-vs-classes* choice"; P-2 §3.1).

**The port does not need it.** The pin's class chain is staging: the intermediate `Prop`s
mention `pointMapOfPushforward` at the *base-changed* curves, where the pin supplies the
instances from `s13GlobalGate`. The **headline's own conclusion already quantifies those
instances** (`∀ [DecidableEq (AC K₀)] [GenusOnePlaceGate …] [IsCentred …] [AbelTheorem …] (hN₀)`),
so a direct proof of the headline `intro`s them and never needs a global instance.

Binding consequence: **do not land the four `KwD5*`/`KwD5BC*` class declarations, do not land
`s13GlobalGate`/`s13_exists_gate`/`s13DecEqAlgebraicClosure`, and do not port the capstone.**
Inline their content in the headline's proof. The pin's statements that *are* landed (the
headline, and `iotaDescentPhi`'s family) keep their pin names; the classes are ours to omit —
they are declarations the port never writes, which the checker does not report.

The `∀` block is not decoration: the headline's conclusion must be at the *caller's* gate
instances and the *caller's* `hN₀`, so the proof must `intro` them and discharge the goal
after `letI`-binding them. `NormFormulaAlong` is a `Prop`, so the caller's `hN₀` and
`normFormulaAlong_of_elliptic ι₀ hfin₀` are equal by proof irrelevance; `DecidableEq` is a
`Subsingleton`, so the pin's `s13DecEqAlgebraicClosure` and its `subst hdec` are unnecessary.
Record both observations in the friction log.

## 4. Deliverable

### 4.1 The promotion set (do this first)

D-2's descent helpers are `private` in
`FLTForHuman/WeierstrassCurve/Isogeny/IntermediateField.lean` (already at their
prefix-stripped pin names, so promotion = drop `private`). Promote exactly the ones the
proof **names**, and no more: a promotion enlarges the checker's compared surface and makes
every promoted declaration a diff row, while a `private` helper left alone stays out of it.
Each promotion is a `RENAMED` row through the checker's `stripped_source` fallback
(playbook §4–§5).

Measured by call count inside the pin's two-curve regions (`A:3025–3435` the descent,
`A:3435–3630` the compatibility step), the pin names exactly **seven**:

| port name | port line | calls there |
|---|---:|---:|
| `iA_crCoeffsIn` | 282 | 4 |
| `iA_phi` | 323 | 23 + 6 |
| `iA_ffDescend_exists` | 368 | 4 |
| `iCa_ffCoeffSet` | 547 | 6 |
| `iCa_crCoeffsIn_of_ffCoeffSet_subset` | 611 | 4 |
| `iPFA_finiteDimensional_adjoin_transcendental` | 805 | 1 |
| `iPFE_functionField_ringHom_ext` | 930 | 2 |

Everything else in D-2's block (`iA_polyDescend*`, `iA_crDescend*`, `iA_phiEquation`,
`iA_phiTranscendental`, `iA_polyToFF_eq_aeval`, `iA_phiCRCompat`, `iCa_crRepr*`,
`iCa_crCoeffSet`, `iCa_ffNum`, `iCa_ffDen`, `iP_xP`, `iP_yP`, `iPFA_isTranscendenceBasis_coord`,
`iPFA_isAlgebraic_adjoin_transcendental`, `iotaSubd_countable_of_fg`) scores **zero** direct
calls there: it is either an internal dependency of the seven (privacy restricts naming, not
use, so that needs no promotion) or the pin's own copy of a one-curve argument this set does
not re-run. `grep -c` each before promoting, promote any extra one the port's own proof ends
up naming, and record the skipped names with their counts in the log. Nothing outside
`IntermediateField.lean` is edited by this step.

### 4.2 The module

**`FLTForHuman/WeierstrassCurve/Isogeny/TwoCurveDescent.lean`** (new leaf). Imports
`IntermediateField` (the promoted helpers), `KernelBaseChange` (D-5's engine, its
`KwD5BetweenCurvesKerTransportAlongEmbed` and its headline), and specifics from mathlib. It
imports **neither** `GenusOnePlaceGateCentred.lean` nor `Place/RRSpace.lean`.

Public, in `WeierstrassCurve.Affine` / `ModularCurve` as the pin has them:

- `ModularCurve.iotaDescentCurve_map_FF`, `iotaDescentPhi`, `iotaDescentPhi_equation`,
  `iotaDescentPhi_transcendental`, `iotaDescentPhi_X`, `iotaDescentPhi_yGen` — promotions at
  the prefix-stripped pin names (the pin's `kw_iotaDescent*` at `A:2292–2386`);
- the two-curve descent itself, as **port-own** declarations (there is no pin name for a
  reusable two-curve descent outside the class chain): `private` is wrong here — the S row
  and the capstone will want it — so give it a public home with a content name and record it
  in `OWN_PROOFS` with the reason (§4 of the playbook: a declaration that is ours goes on the
  exemption list *with the reason*). Suggested spelling: `ModularCurve.exists_twoCurveDescent`
  at the shape of `A:2391–2405`'s `KwD5BetweenCurvesSubfieldDescent` body, with the `∀ hcoeffs`
  and the finrank equality;
- `WeierstrassCurve.Affine.exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward`
  at the wrapper's statement.

Helpers local to the module are `private` with content names — never public and `kw_`-stripped.

## 5. Route, with recorded negatives

- **The descent is D-2's construction at a second curve.** `iotaDescentPhi` is
  `pointPullbackHomTo` on the equation of `E₀.map (algebraMap K₀ E.FunctionField)`, exactly as
  D-2's `iA_phi` is on `E₀.map (algebraMap K₀ E.FunctionField)`; the pin even proves
  `iA_phi E₀ = iotaDescentPhi … rfl` (7 lines). Build it once, generically.
- **Reuse the promoted helpers, do not re-derive them.** `xP`/`yP` come from
  `iA_ffDescend_exists`; the equation and transcendence come from `iA_phiEquation` /
  `iA_phiTranscendental`; the compatibility square is
  `functionField_algHom_ext` on `X` and `yGen`; `finiteAlong`/`isIntegral` come from
  `iPFA_finiteDimensional_adjoin_transcendental` (the pin's own call, at `A:3248`).
- **The finrank equality is not new mathematics.** The pin proves it by rewriting D-5's
  landed `kw_surge_hgf4_bcIota₁_finrankAlong` along the identification
  `bcIota₁NoAC (the descended ι') = ι`; both halves are D-5's. Do the same.
- **The kernel step is D-5's landed headline.** `ι₀ := kw_surge_hgf4_bcIota₁` (or the `NoAC`
  spelling at the same statement), then
  `isAddCyclic_ker_pointMapOfPushforward_of_baseChange_algHom` with `F₁ := AlgebraicClosure K₀`,
  `F₂ := K`, and the commuting square built by `functionField_algHom_ext` — the pin's
  `hKD_of_kerTransport` body minus its `subst hgE`/`s13GlobalGate` lines.
- **Recorded negatives** (do not repeat the search): `adjoin_yCoord_eq_top`,
  `finiteDimensional_ratFunc_functionField` and `isIntegral_yCoord` are **already ported**
  (`WeierstrassCurve/FunctionFieldFinite.lean`, `FunctionFieldQuadratic.lean`), so the pin's
  163-line `S13FiniteOverRatFunc` block is not written; `IsAlgClosed.lift` exists in mathlib
  (`Mathlib/FieldTheory/IsAlgClosed/Basic.lean:350`), so `hKD`'s `let τ := IsAlgClosed.lift`
  needs no substitute; `ModularCurve.kw_fdn2_qephod_hend7_pmopKerCard_proved` is **not**
  declared (the name owns a differently stated `Prop`; use the imported
  `natCard_ker_pointMapOfPushforward_eq_finrankAlong`, P-2e §Amended).
- **A `def … : Prop` is never dropped on the tool's word** (P-2 §6). The classes here are not
  landed at all, but the same applies to any `Prop` you *do* transcribe: `grep -c` its body.

## 6. Build discipline (binding) and pre-flight

> `lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>` is the edit loop (without
> the options the check runs at the default cap and lies about heavy modules);
> `lake build <module>` when a file is done; **one** `lake build` per wave; the full build at
> the milestone. Bound every build (`timeout 60`/`90`/`300`), serialize every `lake build` with
> `flock .lake/flt_build.lock`, and time it: high user CPU with a timeout is a real blow-up to
> bisect, ~0 CPU is contention. **Never raise `maxHeartbeats`.** Never `import Mathlib` in a
> library module. Iterate in a gitignored `Scratch.lean`, in bounded blocks.

**Pre-flight, before writing anything** (report the numbers):

1. `timeout 300 lake env lean <opts>` on a stub that imports `IntermediateField` +
   `KernelBaseChange`, timed. Both are heavy oleans; the D-5 record has the first-stub figure
   (1 m 47 s) for comparison.
2. `#check @IsAlgClosed.lift`, `#check @ModularCurve.kw_surge_hgf4_bcIota₁_finrankAlong`,
   `#check @ModularCurve.KwD5BetweenCurvesKerTransportAlongEmbed`,
   `#check @ModularCurve.iA_ffDescend_exists` — pin the exact names and signatures you will
   call before writing against them.
3. Promote **one** helper (`iA_phi`), `lake build FLTForHuman.WeierstrassCurve.Isogeny.IntermediateField`,
   and confirm the consumer still builds. Then do the rest in one pass.

**The pin raises hearts three times in this region** (`48,000,000` on
`bcFGDescent_of_three`, and `6.4M`/`3.2M` sections). The port's cap is 4,000,000 and is not
raised. D-1's lesson applies: a `whnf` heartbeat timeout in this block usually means a
universe was pinned too tight or an implicit was left to search, not that the proof is heavy
— name the implicits at the application sites and restructure. Report the declaration if one
blows.

## 7. Stop conditions

Stop and report, do not push on: an unported prerequisite outside §2/§4; a statement that does
not transcribe to `v4.34.0`; a heartbeat blow-up that restructuring does not fix; any pull
toward the S row or the capstone; and — the live one — any pressure to import
`GenusOnePlaceGateCentred.lean` or `Place/RRSpace.lean` (§3).

## 8. Verification

- `lake env lean` clean per module; `lake build` for the promoted module and for
  `TwoCurveDescent`; one `flock`ed wave build.
- `python3 spec/check_flt_statements.py` → **0 mismatched / 0 missing**. Baseline at drafting:
  **`6037 identical (313 promoted, 67 renamed), 0 mismatched, 0 missing, 36 own, 6073 checked`**.
  Expect **+7-or-so promoted** (the §4.1 set, each a `renamed` row) and `+N identical` for the
  new module's public surface; anything else is a bug and must be reconciled. A one-token drift
  in a promoted declaration surfaces as `missing`, not `mismatched` — read both.
- `PORT_FILES`: append `FLTForHuman/WeierstrassCurve/Isogeny/TwoCurveDescent.lean` (last), and
  update the `IntermediateField.lean` comment that says its descent helpers are `private`.
  `SOURCES`: append the `Theorems/` wrapper and the `S_` file of this node (last, wrapper
  before its `S_` file) so `iotaDescentPhi`'s family and the headline can resolve; append last
  so no earlier last-name match can flip.
- A `spec/TwoCurveDescentConsumer.lean` (new, `spec/` only) with real executed cross-module
  zones, no `#check`, no `sorry`; deleting the module must make it fail; exit 0. Where a
  concrete instantiation needs unported hypotheses, state the test in hypothesis form and keep
  the named instance `private` (playbook §4). Suggested zones: (i) the headline at a concrete
  algebraically closed char-0 `K` with the gate instances named `private` in the probe, its
  existential unpacked and composed with `WeierstrassCurve.map_Δ`; (ii) the descent's
  `finrankAlong` output composed with the ported `natCard_ker_pointMapOfPushforward_eq_finrankAlong`
  (the bridge the capstone will use); (iii) `iotaDescentPhi` composed with
  `WeierstrassCurve.map_map`.
- `#print axioms` on the headline: `[propext, Classical.choice, Quot.sound]`; no `sorry`
  (`#print axioms` cannot see a `sorry` inside a `def`).
- `grep -c` of every declaration dropped as already-present or as pin staging, with the reason,
  in the log.
- Whole-tree `flock`ed `lake build`; jobs and seconds.

## 9. Close-out (fill on landing)

Written lines per module; the promotion set with its `grep -c`; checker before → after and the
reconciliation; the measured saving against the silo (state both figures: the 3,729 raw lines
and what was actually written); the consumer exit and time; whole-tree build jobs and seconds;
`#print axioms`; the friction findings — in particular whether dropping the pin's `KwD5*` class
chain changed any proof shape, and how the headline's `∀ [gate instances] (hN₀)` block was
discharged. Then delete this order's line from
[../../CARRY-FORWARD.md](../../CARRY-FORWARD.md) and fold the generalizable part into
[../../porting-playbook.md](../../porting-playbook.md) and
[../../logs/velu-port.md](../../logs/velu-port.md) §P-3.
