# P-3 work order — the two-curve countable descent (set D-6)

**Status: LANDED 2026-10-06 (fourth pass).** The statements are faithful and mechanically
checked — `6054 identical (313 promoted, 83 renamed), 0 mismatched, 0 missing, 36 own, 6090
checked`, exit 0 (the `37 own, 6091` figure first written here is stale; the current checker gives
`36/6090` on the pristine tree too) — and the module now **elaborates**:
`lake env lean -DmaxHeartbeats=4000000` is green in **4 m 49 s**; `lake build
FLTForHuman.WeierstrassCurve.Isogeny.TwoCurveDescent` completes (9,039 jobs);
`spec/TwoCurveDescentConsumer.lean` exits 0; `#print axioms` on the headline and on
`ModularCurve.exists_twoCurveDescent` both give `[propext, Classical.choice, Quot.sound]`; no
`sorry`. **The earlier "tower-at-`R₀` defeq / frozen-4,000,000-cap" reading is withdrawn** — both
*pinned* mathlib checkouts define `WeierstrassCurve.baseChange` identically as a semireducible
`def` and `Affine.baseChange` as an `abbrev`, and the one-line escapes (`local reducible` under
`allowUnsafeReducibility`, `respectTransparency false`) were probed and fail. §9 records the
diagnosis, the four fixes that landed, the three *previously-masked* defects they exposed, and the
method that made it affordable (a low-`maxHeartbeats` diagnostic loop; restating intermediate
goals in the plain spelling instead of rewriting `⁄`). One declaration,
`gateDescent_of_descent`, carries the pin's own budget — `set_option maxHeartbeats 48000000` /
`synthInstance.maxHeartbeats 8000000`, transcribed from `kw_surgehgf4_hfgkd_hKD_of_kerTransport`
(`S_:2882–2885`); that is a fidelity fix, not a cap exception, and it is where the 4 m 49 s goes.
`FLTForHuman/WeierstrassCurve/Isogeny/TwoCurveDescent.lean` is 1,299 lines and `lake build` is
green. `spec/TwoCurveDescentConsumer.lean` and the `spec/check_flt_statements.py` wiring
exist; the headline is at `:1255` and the D-5 seam is reused at `:1236`. The promotion pass in
`IntermediateField.lean` landed 10 helpers (`iA_crCoeffsIn`, `iA_phi`, `iA_ffDescend_exists`,
`iCa_ffNum`, `iCa_ffDen`, `iCa_ffCoeffSet`, `iCa_crCoeffsIn_of_ffCoeffSet_subset`,
`iPFA_finiteDimensional_adjoin_transcendental`, `iPFE_functionField_ringHom_ext`,
`iotaSubd_countable_of_fg`). Pin
`anthropics/fermats-last-theorem@aa2d8b3`;
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
   type.

   **Amended 2026-10-06, from the worker's pre-flight (verified by the manager).** That
   block is *not* importable from D-5, and this correction was wrong in the first draft of
   this order. The pin's block is the **`NoAC`** spelling — no `[IsAlgClosed F]`, no gate
   instances — while D-5 landed only the `General` twin, whose section
   (`KernelBaseChange.lean:133–141`) carries `[IsAlgClosed F] [IsAlgClosed F']` and the four
   gate blocks, so `kw_surge_hgf4_bcIota₁` cannot be instantiated at `F = K₀`, a subfield that
   is neither algebraically closed nor gate-equipped — which is exactly where the two-curve
   descent needs it (the pin calls `bcIota₁NoAC E₀ E₀' (↥K₀) K ι'`). D-1 had already resolved
   this same split for the *prelude* (the `NoAC` name is the primitive, the `General` name a
   one-line invocation); D-5's engine section did not. So the engine is **written here**,
   once, `private` at port-own content names, from the pin's `NoAC` block — and the
   generality reconciliation is registered as an open follow-up in
   [../../CARRY-FORWARD.md](../../CARRY-FORWARD.md) for a refactor round after this set, not
   folded into it (playbook §3.7: a frozen file is not reopened mid-set).
2. **The pin's proof staging is not ported.** The `KwD5*`/`KwD5BC*` class chain and the
   `s13GlobalGate` device are the pin's own scaffolding for a staged proof; §3 explains why
   the port does not land them. ≈290 raw lines.
3. At source level, **62%** of the file's substantive lines are verbatim in the five pin
   files P-2 landed (41% in the D-2 `S_` file alone, 47% in each D-5 silo).

After (1) — with the amendment, the engine stays in — and (2): **≈1,700 raw** lines that a
transcription would write. Because the
descent layer is an adaptation of D-2's *promoted* helpers rather than fresh text, the
working estimate is **900–1,200 written lines** plus a 7-declaration promotion set. Re-price
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
| 2501–2839 | `kw_surgehgf4_hfgkd_bc*` engine | the pin's **`NoAC`** engine; D-5 landed only its `General` twin, unusable at `F = K₀` — **written here**, `private` (§2 amendment) |
| 2844–2877 | `KwD5BetweenCurvesKerTransportAlongEmbed`, `…ChiCompChiEqPhi` | the first is **D-5** (import); the second is pin staging — not landed |
| 2886–2992 | `…hKD_of_kerTransport` | inlined into the headline proof (§3) |
| 3025–3380 | `kw_surgehgf4_hSD_*` — the two-curve descent | **new** (~410), built from §4.1's promoted helpers |
| 3389–3435 | `KwD5BCSubfieldDescent{Pinned,Canonical}FinrankEq`, `…hSD_of_canonicalFinrankEq` | inlined; the finrank equality is D-5's arithmetic at the `NoAC` statement + the identification (§5) |
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
`s13GlobalGate`/`s13_exists_gate`, and do not port the capstone.**
Inline their content in the headline's proof. The pin's statements that *are* landed (the
headline, and `iotaDescentPhi`'s family) keep their pin names; the classes are ours to omit —
they are declarations the port never writes, which the checker does not report.

**Correction (2026-10-06, after the first dispatch failed on it).** `s13DecEqAlgebraicClosure`
is **not** part of that device and must not be dropped with it. Its whole content is
`noncomputable scoped instance (priority := 50) … : DecidableEq (AlgebraicClosure K₀) :=
Classical.decEq _` (`A:603`); it drags no `RRSpace` and has nothing to do with the gate
producer. Without it — or an equivalent local instance — the pin's `hKD_of_kerTransport` body
does not elaborate: the port's first attempt produced ~10
`failed to synthesize instance of type class DecidableEq (AlgebraicClosure ↥K₀)` errors and a
downstream `whnf` heartbeat timeout. **Declare it, or add
`haveI : DecidableEq (AlgebraicClosure K₀) := Classical.decEq _`** at the top of the
corresponding proof, which is what D-2 already does at
`WeierstrassCurve/Isogeny/IntermediateField.lean:183`.

The `∀` block is not decoration: the headline's conclusion must be at the *caller's* gate
instances and the *caller's* `hN₀`, so the proof must `intro` them and discharge the goal
after `letI`-binding them. `NormFormulaAlong` is a `Prop`, so the caller's `hN₀` and
`normFormulaAlong_of_elliptic ι₀ hfin₀` are equal by proof irrelevance. (`DecidableEq` is a
`Subsingleton`, so a `subst hdec : instDec = s13DecEqAlgebraicClosure` is *unnecessary* — but the
*instance itself* is not, per the correction above; the two are different points and the first
draft of this order conflated them.) Record both observations in the friction log.

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
`IntermediateField` (the promoted helpers), `KernelBaseChange` (D-5's landed seam and
headline — **not** its engine, which is `General`-only; §2 amendment), and specifics from
mathlib. It imports **neither** `GenusOnePlaceGateCentred.lean` nor `Place/RRSpace.lean`.

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
- **The finrank equality is D-5's arithmetic at this set's generality.** The pin proves it by
  rewriting `kw_surgehgf4_hfgkd_bcIota₁NoAC_finrankAlong` (the §2-amended engine, at
  `F := K₀`, `F' := K`) along the identification `bcIota₁NoAC (the descended ι') = ι`. The
  *content* is D-5's; the *statement* must be the `NoAC` one, because `F = K₀` is a subfield.
- **The kernel step is D-5's landed headline.** Build `ι₀` at `AlgebraicClosure K₀` from the
  descended `ι'` with that same `NoAC` engine, then
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
2. `#check @IsAlgClosed.lift`, `#check @ModularCurve.KwD5BetweenCurvesKerTransportAlongEmbed`,
   `#check @ModularCurve.iA_ffDescend_exists`, and — the §2 amendment's check —
   `#check @ModularCurve.kw_surge_hgf4_bcIota₁_finrankAlong` **and its section variables**:
   confirm on the spot that its section carries `[IsAlgClosed F]` and the gate blocks and so
   does not apply at `F := K₀`. Pin the exact names and signatures you will call before
   writing against them.
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

### Partial close-out — as of 2026-10-06, with the proof still red

Recorded because the set is half-verified and the tree is otherwise complete; **it is not a
landing record.** What is measured and green:

- **Checker: green, and it reconciles exactly.** `6037 statements identical (313 promoted from
  pin-private declarations, 67 renamed), 0 mismatched, 0 missing, 36 own-proof declarations
  exempted (6073 port declarations checked)` → `6054 statements identical (313 promoted, 83
  renamed), 0 mismatched, 0 missing, 37 own-proof declarations exempted (6091 port declarations
  checked)`, exit 0. The delta is +17 `identical` (the 10 `IntermediateField` promotions + the 6
  `iotaDescent*` promotions, all named in `RENAMED` rows, plus the headline matched directly
  against its wrapper), +1 `own` (`ModularCurve.exists_twoCurveDescent`, exempted with its
  reason), +18 checked. Nothing unexplained. So **every statement this set lands is faithful**,
  and omitting the pin's `KwD5*`/`KwD5BC*` staging and its `s13GlobalGate` device cost nothing
  at the checker.
- **The module**: `WeierstrassCurve/Isogeny/TwoCurveDescent.lean`, 1,231 lines, imports
  `IntermediateField` + `KernelBaseChange` only (no `Mathlib`, no `GenusOnePlaceGateCentred`, no
  `RRSpace`); public surface exactly the six `iotaDescent*` promotions, `exists_twoCurveDescent`
  (`:949`) and the headline (`:1188`); no `maxHeartbeats` bump, no `sorry`; the pin's
  `s13GlobalGate` lines dropped and its content inlined; the D-5 seam genuinely reused
  (`kerTransport_s17` at `:1169`). The promotion set in `IntermediateField.lean` is 10 names
  (`iA_crCoeffsIn`, `iA_phi`, `iA_ffDescend_exists`, `iCa_ffNum`, `iCa_ffDen`, `iCa_ffCoeffSet`,
  `iCa_crCoeffsIn_of_ffCoeffSet_subset`, `iPFA_finiteDimensional_adjoin_transcendental`,
  `iPFE_functionField_ringHom_ext`, `iotaSubd_countable_of_fg`).
- **The consumer**: `spec/TwoCurveDescentConsumer.lean`, three zones matching the order's
  suggested ones, importing the module directly (so deleting the module fails the probe), with
  no `#check` and no `sorry`.
- **Build cost**: three `lake env lean` runs on successive revisions cost 254 s / 438 s /
  **1,119 s** wall (`USER ≈ 2 × WALL`) — measured and recorded in
  [../../../notes/lean-build-cost.md](../../../notes/lean-build-cost.md) §2, with the lesson
  that a *failing* check can exceed the recorded per-file bounds.

**What is missing, and why — corrected and probe-confirmed (2026-10-06, second pass).** The
three missing/bound items are fixed and the `universe u` line is in (`:70` reads
`universe u uK`); those fixes collapsed 25 of the original errors. **The earlier
"tower-at-`R₀` defeq / frozen-4,000,000-cap" reading is WITHDRAWN — it rests on a false premise
and points at the wrong lever.** Verified against both *pinned* mathlib checkouts: the pin
(`aa2d8b3` → mathlib `db584cd6`) and the port (mathlib `v4.34.0` = `5ed2965256`) define
`WeierstrassCurve.baseChange` **identically as a semireducible `def`** (`Weierstrass.lean:236`)
and `WeierstrassCurve.Affine.baseChange` identically as a reducible `abbrev`
(`Affine/Basic.lean:264`). There is no reducibility difference, so neither a cap exception nor
"restructure the tower cost" can address the cause.

**The cause is two defects this port introduced**, each reproducible in isolation at the pin's
*own* budget (`lake env lean -DsynthInstance.maxHeartbeats=3200000 -DmaxHeartbeats=6400000`) —
i.e. they are **not** budget starvation. The two minimal probes, quoted verbatim:

```lean
-- (1) duplicate instance: section `variable {K} [Field K] [Algebra ℚ K] [CharZero K]`
example (K₀ : IntermediateField ℚ K) :
    letI : Algebra ℚ K := DivisionRing.toRatAlgebra
    ∃ (K₁ : IntermediateField ℚ K), K₁ = K₀ := by
  letI : Algebra ℚ K := DivisionRing.toRatAlgebra
  exact ⟨K₀, rfl⟩   -- ✘ Type mismatch: inst✝¹ (section) vs this (the letI)
-- with only the default instance, `:= ⟨K₀, rfl⟩` is ✔

-- (2) spelling: `open scoped WeierstrassCurve TensorProduct`
example {K₀ K : Type} [Field K₀] [Field K] [Algebra K₀ K] (E₀ : WeierstrassCurve K₀)
    [IsDomain (E₀.toAffine.FunctionField ⊗[K₀] K)] :
    IsDomain ((E₀⁄K₀).toAffine.FunctionField ⊗[K₀] K) := inferInstance  -- ✘ synthInstanceFailed
```

1. **A duplicate `Algebra ℚ K` instance.** `section TwoCurveAssembly`
   (`TwoCurveDescent.lean:880`) carries `[Algebra ℚ K]`, and `twoCurveDescentInstance`'s
   *statement* installs `letI : Algebra ℚ K := DivisionRing.toRatAlgebra` (`:926`, again `:935`);
   `exists_twoCurveDescent` (`:957`) does the same. The pin's counterpart
   (`kw_surgehgf4_hSD_instance_cast`, `S_:3313`) has **no `letI` in its statement** — the `letI`
   belongs to the `KwD5BetweenCurvesSubfieldDescent` *Prop* (`S_:2391`), not to its proof helper.
   The two instances give two *different* `IntermediateField ℚ K` types, refuted by `rfl`:

   > `K₀ has type @IntermediateField ℚ K Rat.instField inst✝² inst✝¹`
   > `but is expected to have type @IntermediateField ℚ K Rat.instField inst✝² this`

   That is exactly the `:937`/`:938` pair (`Type mismatch` / "synthesized type class instance is
   not definitionally equal to expression inferred by typing rules"), and every downstream
   `K₀ : IntermediateField ℚ K`, `K₀.FG`, `(K₀ : Set K)` and `finrankAlong K₀` inherits it.

2. **`(E₀⁄(↥K₀))` written where the pin writes `E₀`.** The pin's entire two-curve region
   (`S_:3114–3385`) contains **zero** `⁄`. The port's private helpers write `(E₀⁄(↥K₀))` /
   `(E₀'⁄(↥K₀))` / `(E₀⁄(AlgebraicClosure (↥K₀)))` at 18 sites
   (`TwoCurveDescent.lean:836,837,846,849,855,858,919,920,978,980,1073,1074,1077,1079,1138,1141,1148,1151`),
   while the call sites supply those instances in the plain `E₀`/`map` spelling. `E₀⁄R = E₀` is
   `rfl` at default transparency but **fails at reducible transparency** — which is what `isDefEq`,
   instance search and `erw` use — and it fails at the pin's budget too:

   > `failed to synthesize instance of type class IsDomain ((E₀⁄K₀).toAffine.FunctionField ⊗[K₀] K)`

   with a plain-spelling `IsDomain` binder *in scope*. That is the `:912`/`:919` `IsDomain`
   binder, the `:1007` missing `IsScalarTower (↥K₀) F₁ (W⁄K).FunctionField`, and the
   `whnf`/`isDefEq` residue at `:842`/`:850`/`:853`/`:1034`/`:1148`–`:1151`.

**Confirmed at module scale, pre-fix.** The unchanged module, truncated at `end TwoCurveAssembly`
and checked at the pin's own budget, still fails: **7 error sites, wall 10 m 42 s**
(`user 21 m 40 s`). Translated back to the shipped file's line numbers they are the same sites
§9 already names: `:842`/`:850`/`:853` (`twoCurve_bcIota_eq_ι`), `:912` (`whnf`, the `IsDomain`
statement), `:937` `Application type mismatch` and `:938` "synthesized type class instance is not
definitionally equal …" (the `Exists.intro` under the duplicate `Algebra ℚ K`), and the `:953`
cascade. Raising the cap from 4,000,000 to 6,400,000 *did* remove the instance-family errors
(14 sites → 7), so the budget omission is real but partial; **not one of the type-level sites
moved**. The cap is not the fix.

**Remedy, applied and measured (2026-10-06, third pass).**

1. **Single `Algebra ℚ K` — DONE, and it worked.** `section TwoCurveAssembly` (the section whose
   statements carry the `letI`s) dropped its `[Algebra ℚ K]` section variable, so
   `IntermediateField ℚ K` elaborates at `DivisionRing.toRatAlgebra` throughout it. Measured:
   the `:937` `Type mismatch`, the `:938` "instance is not definitionally equal", the `:912`
   `whnf` on the `IsDomain` statement and the `:953` cascade are **gone** (14 error sites → 9).
   The checker is unmoved by this and by item 2: it reports
   `6054 statements identical (313 promoted, 83 renamed), 0 mismatched, 0 missing, 36 own, 6090
   checked` on the edited tree *and* on the pristine `HEAD` tree — so the `37 own, 6091` figure
   written earlier in this order is stale and must not be used as a baseline.
2. **The pin's `⁄`-spelling instance bridges — DONE, and they were not enough.** Four
   `private instance … := inferInstanceAs (…)` bridges were added in `section TwoCurveBcIota`,
   and the `inferInstance`s in `gateDescent_of_descent` re-spelled the same way. The result:
   `twoCurve_bcIota_eq_ι` still times out (`:858`/`:866`/`:869`); `twoCurve_chiCompChiEqPhi` still
   fails to synthesize `IsScalarTower (↥K₀) F₁ (W⁄K).FunctionField` (`:1034`) and still `whnf`s at
   `:1061`; the `hχ` block still times out (`:1173`/`:1175`/`:1176`), then the `:1214` cascade.

   **So the set still has not landed, and the check is slower after the two edits:
   `lake env lean` at the project's 4,000,000 cap is now 14 m 41 s (user 14 m 00 s) for the full
   module, against 9 m 11 s for the same file at the same cap before either edit.** The
   attribution is not certain — the surviving `erw` sites are a different (smaller) set, and a
   failing `erw` burns hearts by brute force, so the cost tracks *which* steps fail, not simply
   how many. What the number does settle is that no cap or bridge makes this leaf cheap.

**What the residue actually is.** Every surviving site is one mechanism: a proof step or an
instance has to unify a term written `E⁄(↥K₀)` with one written `E` / `E.map (algebraMap (↥K₀)
(↥K₀))`, at **reducible** transparency. `erw` patterns and typeclass search both run there, and
`WeierstrassCurve.baseChange` is a semireducible `def`, so neither can unfold it — at any budget.
Two one-line escapes were probed and both fail: `attribute [local reducible]` requires
`set_option allowUnsafeReducibility true` (a hack that perturbs `simp`/instance indexing), and
`backward.isDefEq.respectTransparency false` does not reach instance search.

**The fix that addresses it at the source** is not more bridges: it is to stop writing `⁄` in the
port's **own** private transcriptions. `section DescentEngine` and the two-curve helpers are
port-own `private` declarations — the pin's checked public statements (the six `iotaDescent*` and
the headline) are elsewhere and none of them moves — and `E₀⁄F` is pure sugar for
`E₀.map (algebraMap R₀ F)`. Writing the `map` spelling everywhere makes the two spellings
*syntactically equal*, which removes the class: instance search finds `(W.map f).IsElliptic`,
`rw`/`erw` key-match, and no unification has to unfold a `def`. Cost: a spelling refactor over the
`⁄` sites (the engine region plus ~18 two-curve sites), plus explicit conversion wherever an
imported D-1/D-5 helper forces the `⁄` head, which must be checked rather than assumed.

**The cheaper and better-founded variant — restate the intermediate goals.** D-2 met exactly this
wall and recorded the idiom. `IntermediateField.lean:960–966` restates a `⁄`-spelled generic
lemma's conclusion in the plain spelling:

```lean
have htmul : ∀ (a : E₀.toAffine.FunctionField) (c : K),
    tensorIotaRingHomGeneralNoAC E₀ (K₀ : Type uK) K D₀ (a ⊗ₜ[K₀] c) = (ι₀ a) ⊗ₜ[K₀] c :=
  fun a c => tensorIotaRingHomGeneralNoAC_tmul E₀ (K₀ : Type uK) K D₀ a c
```

with the comment "the raw `rw […]` cannot unify the two spellings", and `:1009–1020` replaces the
pin's `calc` with an explicit `Eq.trans` chain because "a `calc` step would have to unify
`(E).toAffine.FunctionField` with `(E₀⁄K).FunctionField`, which is a semireducible `baseChange`
unfolding, at too low a transparency". Two reasons it works, and both matter:

* the restatement's own proof is a **single direct application**, elaborated at the *default*
  transparency, where `E₀⁄(↥K₀) = E₀` is `rfl` (probe-verified);
* its statement is in the plain spelling, so at the *use* site the `⁄`-term becomes a
  **metavariable** in the `rw` pattern — the rewrite *assigns* it instead of having to unify it.

So the residue is fixed by restating `descentBCIota_compat`,
`functionFieldMapAlongGeneralNoAC_polyToFunctionField_X`/`_yGen` and the `ChiCompChiEqPhi`
compositions at `F = ↥K₀` in the plain spelling, and using `rw`/`Eq.trans` instead of `erw`. This
is confined to `private` proofs — checker-neutral — and does not touch the engine, which makes it
strictly preferable to the spelling refactor as a first move. What it does not fix is the
statement-elaboration cost (`:1061`) and the genuinely missing instance (`:1034`); those take the
hand bricks above.

**Measured: a low cap turns the diagnostic into a bounded loop.** `lake env lean
-DmaxHeartbeats=200000` reports the full error map in **2 m 30 s**, and `1000000` in **5 m 22 s**,
against **14 m 41 s** at the project's 4 000 000 — same target sites, plus the engine's own heavy
declarations timing out (which are cap artefacts, identifiable because they sit at `:213–:452`).
Iterate the fix in a `tmp/` copy under that cap, then confirm once at 4 000 000. The caveat is
real: at low caps the engine declarations fail, so downstream contexts are degraded and some
errors are spurious — read the target lines, not the count.

**Restatement validated in situ (2026-10-06, fourth pass).** With the low-cap loop, the
restatement technique cleared two of the three `erw` groups — `twoCurve_bcIota_eq_ι`
(`:858`/`:866`/`:869`) and the `hχ` block of `gateDescent_of_descent`
(`:1173`/`:1175`/`:1176`) — and the edits are **in the tree** now (`hcompat₀`/`hpolyX`/`hpolyy`
and `hpolyX_ac`/`hpolyy_ac`). The residue is three, and two are instance-keying rather than
unification:

* the genuinely missing `IsScalarTower (↥K₀) F₁ (W⁄K).FunctionField` — the hand brick must be
  stated in the goal's **exact** spelling (`(W.toAffine⁄K).FunctionField`, not
  `(W.map (algebraMap (↥K₀) K)).toAffine.FunctionField`): instance search matches local instances
  by syntactic key, so a brick in the wrong spelling is invisible;
* a `DecidableEq (AlgebraicClosure K₀)` identity clash at the final
  `kerTransport_s17` application in `gateDescent_of_descent` ("synthesized type class instance is
  not definitionally equal … synthesized `inst✝` / inferred `this✝⁵`") — the proof's local
  `haveI := Classical.decEq _` and the `∀ [DecidableEq …]` binder it later `intro`s are two
  different terms. This was **masked** before the `hχ` restatement: the declaration failed
  earlier, so this error was never reached. It is the same class as the withdrawn
  `s13DecEqAlgebraicClosure` note in §3, one level down;
* the statement-level `whnf` at `:1061`.

**Resolution — landed (2026-10-06, fifth pass).** All three residue items are fixed, each by a
device the pin already had:

* `IsScalarTower (↥K₀) F₁ (W⁄K).FunctionField` — a `haveI` brick stated **in the goal's
  spelling** (`((W.toAffine)⁄K).FunctionField`), proved by `inferInstance` for the `F₁ → K → B`
  tower plus `IsScalarTower.of_algebraMap_eq` and three `rw [IsScalarTower.algebraMap_apply …]`.
  The earlier attempt in the `map` spelling was invisible to search — the "state it in the goal's
  spelling" rule, live. The brick then exposed two `show`/`rw` patterns in
  `twoCurve_chiCompChiEqPhi` that had been masked; those are restated in the plain spelling
  (`h0`/`h1` + an `Eq.trans` chain).
* the `DecidableEq (AlgebraicClosure K₀)` clash — the pin's `subst` device: name the local
  instance `hdecAC`, then after `intro instDec …` do
  `have hdec_eq : instDec = hdecAC := Subsingleton.elim _ _; subst hdec_eq`. (`clear hdecAC`
  cannot work — `ι₀` depends on it; and proof irrelevance is only *propositional*, not the
  definitional equality the instance argument needs, so §3's "`subst` is unnecessary" note was
  wrong at the elaborator level.)
* the statement-level `whnf` — the pin's own `set_option maxHeartbeats 48000000` /
  `synthInstance.maxHeartbeats 8000000` for `kw_surgehgf4_hfgkd_hKD_of_kerTransport`
  (`S_:2882–2885`), transcribed. Not a port error, not a cap exception.

The last item exposed the final defect, also masked: `pointMapOfPushforward` and
`KwD5BetweenCurvesKerTransportAlongEmbed` carry the gate instances as *arguments*, and the
caller's are on `E₀.map …` while the seam wants `(E₀⁄K)`. The bridges must be `letI` — which
*inlines* the value, so the seam's instance arguments become literally the caller's terms —
rather than `haveI`. Final state: module `lake env lean` green at 4,000,000 in **4 m 49 s**;
`lake build` of the module 9,039 jobs; consumer exit 0; axioms
`[propext, Classical.choice, Quot.sound]`; no `sorry`; checker `6054 (313, 83), 0/0, 36 own,
6090` — unmoved, because every fix is in a `private` proof.

**Build cost is a first-class constraint here, not an afterthought.** Even the engine + descent
construction alone (before the failing tactics) was measured at 225 s, and the full red module is
15 min. Per the port's own cost model the repeating cost is re-elaboration, so a 1,200-line leaf
that cannot be checked in under a minute should either be **split by region** before the next
attempt, or **parked out of the library** (move the leaf aside: `lake build` goes green, the
statements are preserved in the file) until SC actually needs the headline.

**The friction finding to write up** is now two, both recorded in
[../../porting-playbook.md](../../porting-playbook.md) §6 and
[../../instance-friction.md](../../instance-friction.md) IF-003: "**a misspelling across a
semireducible `def` is a type-level wall, not a heartbeat problem**" (`⁄` vs `map`: `rfl` at
default transparency does not imply `isDefEq` at reducible, so instance search and `erw` cannot
cross it at any budget), and "**two `Algebra`-like instances in one context is a hard type
error**" (a statement `letI` plus an ambient section variable make `IntermediateField ℚ K` two
types). Its predecessor — "a missing instance reads as a heavy proof" (three missing instances
and one unbound universe produced ten `whnf`/`isDefEq` timeouts and two type mismatches) — stands.
