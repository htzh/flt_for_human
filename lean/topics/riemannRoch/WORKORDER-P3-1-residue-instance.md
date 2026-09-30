# Work order — P3.1: the `HasCanonicalLocalResidueKStar` instance

**Status: COMPLETE (2026-09-30).** Sets 3.1a, 3.1b-i and 3.1b-ii all landed,
reviewed and green; the acceptance evidence is [PLAN-P3.md](PLAN-P3.md) §1.6.
Phase 3.1 = row 1 of [../PORTING-RR.md](../PORTING-RR.md) §3, the first phase of
the residue-theorem block. Operative plan: [PLAN-P3.md](PLAN-P3.md); method:
[../porting-playbook.md](../porting-playbook.md) §2–§5. Precedent sets and review
gates as in [PLAN-P1.md](PLAN-P1.md) §2 and
[WORKORDER-P2-canonical.md](WORKORDER-P2-canonical.md).

Baseline: checker **3060 identical / 0 mismatched / 0 missing / 30 own-proof**
(3090 checked); full `lake build` green (4837 jobs);
`spec/RiemannRochConsumer.lean` 0 errors.

## 0. Scope

Two pin `Definitions/` files with no `Theorems/` wrappers — the **producer** of
the `HasCanonicalLocalResidueKStar` class that
[`Defs/LocalResidue.lean`](../../FLTForHuman/AlgebraicCurve/Defs/LocalResidue.lean)
already declares, so the K-side hypotheses can later be discharged:

| pin file | lines | decls | private | raw |
|---|---:|---:|---:|---:|
| `Definitions/Def_AlgebraicCurve_PlaceCompletion.lean` | 529 | 33 | 2 | 529 |
| `Definitions/Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2.lean` | 2,173 | 131 | 3 | 2,173 |

Raw 2,702; `port_advise` finds **no shared prelude** and ≈100 lines of
substitutions, so projected **≈2,600 written** — transcription, not new
mathematics. The work is split into two sets on a dispatch-time dependency that the
phase-3.1 audit later **removed** (see §4, R2): the pin's V2 file imports
`PlaceCompletion` vestigially and names nothing from it, so 3.1b does **not**
import 3.1a and the two sets are independent:

- **3.1a — the completion layer** (`Defs/PlaceCompletion.lean`, ≈530 written):
  the `kw_ffgc_*` adic-completion API and the `kwHgfV352_*` /
  `ModularCurve.KwF4gRRTate` residue-completion facts. **LANDED and reviewed
  2026-09-30 (551 ln, checker 3091 / 0 / 0, build green, axioms clean).**
- **3.1b — the instance** (`Defs/CanonicalLocalResidueInstanceV2.lean`, ≈2,100
  written): the whole pin V2 construction and the unconditional
  `instHasCanonicalLocalResidueKStar`. **3.1b-i (pin 1–789, the `Place`
  pole/Laurent layer) LANDED and reviewed 2026-09-30: 552 ln, 58 public decls,
  checker 3149 / 0 / 0, build green, axioms clean.** 3.1b-ii appends pin 797–2173
  (the `Ldgr35/36/Lg37` + Hensel/adic-completion engine + `KwNo6Pin` + the
  instance). One flagged deviation: the pin's one-line `def uniformizerSubring`
  (pin 199) is transcribed verbatim rather than imported from
  `Canonical/HasCanonicalDivisor.lean`'s `uniformizerSubring'`, because that
  module transitively imports `Canonical/WeilDifferential.lean` and must not be
  imported into a `Defs/` module; the body is the identical `Classical.choose` and
  the four dependent statements land verbatim (refactor debt: switch the body to
  `v.uniformizerSubring'` once the import is acceptable). Part 1 also dropped
  `algebraMap_residueField_residue` (pin 161) to the port's
  `restrictResidueMap_residue` + `algebraMap_residueField_eq`; part 2 does not
  reference it.

**Explicitly not this set:** the pin's V1 shim
`Def_AlgebraicCurve_CanonicalLocalResidueInstance.lean` (694 ln — the same
development around the V1 import; the port keeps one name per piece); the
`InlineSpecific` prelude (`Def_DedekindDomain_AdicValuation_InlineSpecific.lean`,
564 ln) except for the exact declaration(s), if any, that 3.1a cannot get from
mathlib `v4.34.0`; and everything in phases 3.2–3.7 (the ℙ¹ core, Tate
agreement, commutation, the endings, the RR assembly).

## 1. Deliverables

| new module | content | pin |
|---|---|---|
| `FLTForHuman/AlgebraicCurve/Defs/PlaceCompletion.lean` | the 33-row completion layer, pin names kept | `Def_AlgebraicCurve_PlaceCompletion.lean` |
| `FLTForHuman/AlgebraicCurve/Defs/CanonicalLocalResidueInstanceV2.lean` | the 131-row construction + `instHasCanonicalLocalResidueKStar` + `localResidue_eq_resStar{,ₗ}` | `Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2.lean` |

Keep the pin's namespaces: `AlgebraicCurve.Place.*`, `AlgebraicCurve.*` (the
`HasSeparableResidue.of_perfectField*` instances), `ModularCurve.Ldgr37Ch`,
`ModularCurve.Lg37`, `Mp72a102T1/T2/T3`, `Mp72a103T2`,
`ModularCurve.KwNo6Section`, `ModularCurve.KwNo6Pin`. The pin's
`p2m_export`/`p2m_open`/`p2m_reactivate`/`attribute [-instance]`/`attribute
[-simp]` scaffolding is dropped (ordinary `open`/local instances only where the
proof needs them). The pin-private helpers stay `private` (5 rows total; see the
appendix); everything else lands public. **Never change a statement to ease a
proof.**

## 2. Statements and source

No `Theorems/` wrappers exist for these `Definitions/` files, so the pin
`Definitions/` files themselves are the statement authority. Port each public
declaration **verbatim** from its pin `file:line` (appendix). The V2 module's
internal shape is five order-dependent blocks (pin lines):

1. **`Place` pole/Laurent layer** (99–790): `finiteResidue_of_deg_pos`,
   `restrict*` residue-field instances, `uniformizerSubring`, `simplePole*`,
   `poleSubmodule`, `laurentTailCoeff`, `higherPoleCorrection`,
   `canonicalLocalResidueDataKOfExtend`, `instHasCanonicalLocalResidueK`,
   `CoefficientFieldSection`, `CanonicalLocalResidueDataS`;
2. **`ModularCurve.Lg37`** (929–975): `lg37_completion`, `lg37_residueHat`,
   `Lg37CompletionSection`;
3. **the Hensel / adic-completion engine** (981–1532): `Mp72a102T1/T2/T3`,
   `Mp72a103T2`, `ModularCurve.KwNo6Section`;
4. **`ModularCurve.KwNo6Pin`** (1541–2124): `maximalIdeal_fg` … `section_unique`,
   `aCoeff` and the `aCoeff_*` block, `clearPow_mem`, `clearedHat`, `resStar`,
   `resStarₗ`, `canonicalLocalResidueDataKStar`;
5. **the instance** (2133–2173): `completionSection_nonempty_generic`,
   `instHasCanonicalLocalResidueKStar [IsCurveOver K F] [PerfectField K]`,
   `localResidue_eq_resStar`, `localResidue_eq_resStarₗ`.

The headline shape to preserve (pin 2149):

```lean
noncomputable instance instHasCanonicalLocalResidueKStar [IsCurveOver K F] [PerfectField K] :
    HasCanonicalLocalResidueKStar K F
```

## 3. Route and risk

**Reuse to import, not re-prove** (`port_advise` row 1 substitutions):

- `Place.ord_nonneg_of_mem` (V2:208) ← `Place.ord_nonneg_of_mem_vs`
  (`Canonical/HasCanonicalDivisor.lean`) — the port's name for the same
  statement; the pin-private copy stays `private` only if a local rewrite needs
  it, otherwise import;
- `Place.mem_of_ord_nonneg` (V2:223), `Place.mem_iff_ord_nonneg` (V2:231) ←
  `Defs/PushPull.lean` (binder spelling only);
- `Place.restrictSubringHom` (V2:127) ← `Place.restrictInclusion`
  (`Defs/PushPull.lean`);
- `Place.residueFieldMapRestrict` (V2:155) ← `Place.restrictResidueMap`;
- `Place.instAlgebra_restrictResidueField` (V2:158) ←
  `Place.instAlgebraResidueFieldRestrictPushforward`;
- `Place.instIsScalarTower_restrictResidueField` (V2:167) ←
  `Place.instIsScalarTowerResidueFieldRestrictPushforward`;
- `Place.uniformizerSubring` (V2:199) ← `Place.uniformizerSubring'`
  (`Canonical/HasCanonicalDivisor.lean`); both are the same
  `(IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose`, and
  `Defs/CanonicalDivisor.lean`'s `Place.uniformizer` is that choose coerced to `F`,
  so the pin's `coe_uniformizerSubring` is `rfl` and `irreducible_uniformizerSubring`
  is the `choose_spec`;
- `Place.adicCompletion` (PlaceCompletion:31) ← mathlib
  `IsDedekindDomain.HeightOneSpectrum.adicCompletion` (the port's abbreviation
  is defined here); the `port_advise` match against `CohCarrier.H1` is a false
  positive;
- `ord_nonneg_of_mem_placeCompletionAux` / `mem_of_ord_nonneg_placeCompletionAux`
  (PlaceCompletion:441/432) ← `Place.ord_nonneg_of_mem` / `Place.mem_of_ord_nonneg`
  (`Defs/PushPull.lean`).

**`HasSeparableResidue` — already landed, in a different shape.** The pin V2's
first two declarations are `instance HasSeparableResidue.of_perfectField`
(V2:19, hypotheses `[PerfectField K] [∀ v : Place K F, v.FiniteResidue]`) and
`instance HasSeparableResidue.of_perfectField_of_isCurveOver` (V2:25). The port
**already has the same content** as a *theorem*,
`hasSeparableResidue_of_perfectField` in
[`Canonical/WeilDifferential.lean`](../../FLTForHuman/AlgebraicCurve/Canonical/WeilDifferential.lean)
(validated by the checker against the pin's
`P2M/Sol/S_AlgebraicCurve_exists_linearEquiv_regularDifferentials_omegaSpace_zero.lean:76`,
already in `SOURCES`). The instances are still part of the pin API — the pin's
`ComponentChart`/`ConstantReduction`/`CurveModel` `Theorems/` wrappers name
`AlgebraicCurve.HasSeparableResidue.of_perfectField`,
`…of_perfectField_of_isCurveOver` and `AlgebraicCurve.instHasCanonicalLocalResidueKStar`
in `attribute [-instance]` lists — so 3.1b transcribes both instances at the pin
names and the pin proofs (5 lines). Do **not** import
`Canonical/WeilDifferential.lean` into the `Defs/` module to share the theorem
(that would invert the import graph, playbook §2.4); do **not** edit the frozen
`WeilDifferential.lean`. Record the duplicate proof as refactor debt for the final
promotion round. The `attribute [-instance]` scaffolding is dropped, as usual; be
alert for instance-search changes in modules that take `[HasSeparableResidue K F]`
explicitly (`Defs/WeilOfKaehler.lean`) — report, do not paper over.

**Imports.** `PlaceCompletion.lean` imports the port's
`Defs/{Place,PlacesOverDVR,PushPull,Divisor,Divisor}` (and whatever the pin body
reaches); the V2 module imports `Defs/{LocalResidue,IsCurveOver,PushPull,
PlaceCompletion,WeilOfKaehler}`. The pin's `import Mathlib` is replaced by
specific imports; **never `import Mathlib` in a library module.**

- **Scout gate (§2.6).** Before dispatching 3.1b, 3.1a must confirm the
  `PlaceCompletion` spine elaborates against mathlib `v4.34.0` (in particular
  `Valuation.IsRankOneDiscrete.rankOne` is now a plain function, so the pin's
  InlineSpecific `IsRankOneDiscrete` instance may be unnecessary); record the
  pre/post estimate. If 3.1a turns out to need a genuine InlineSpecific lemma,
  port the minimal declaration(s) into `PlaceCompletion.lean` and report them.
- **Stop-early risks** (stop and report the pin `file:line`):
  1. `PlaceCompletion` needs a declaration from the unported
     `Def_DedekindDomain_AdicValuation_InlineSpecific.lean` that mathlib lacks;
  2. the port's `Place.heightOneSpectrum` / `ramificationIndex` / `restrict`
     API drifts from the pin's by more than names;
  3. the V2 proof reaches a declaration **outside** the two measured pin files
     (the H2/H3 measurement gap). **Resolve it locally `private` with the
     statement verbatim and report it as promotion debt — do not inline new
     mathematics and do not edit a frozen module.** The manager closes the gap
     in the follow-up round;
  4. a `resStar`/`aCoeff` step needs a `simp`/`rw` bridge the port's `Defs`
     does not expose; name the missing bridge rather than weakening a statement.

## 4. Audit fold-in (`AUDIT-mathlib-p3-1.md`, landed)

Counts: `PlaceCompletion` **6 SUBSTITUTE / 21 PROOF-INGREDIENT / 7 BESPOKE = 34
rows** (33 inventoried + the anonymous global `Algebra O L` instance at pin 9), V2
**10 / 95 / 26 = 131**; total 16 / 116 / 33 = 165.

**InlineSpecific verdict — stop-early risk 1 does not fire.** Of its 39
declarations exactly one is consumed by 3.1a in effect: the anonymous
`Valuation.IsRankOneDiscrete` instance for `(Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)`
(InlineSpecific 215–219). It is already mathlib `v4.34.0`'s anonymous instance in
`Mathlib/NumberTheory/NumberField/Completion/FinitePlace.lean:102`, whose context is
generic over a Dedekind domain. Everything else in the 564-line prelude is
NOT-NEEDED by either file (grep count 0 for every distinctive name; the DVR/PID/
`DimensionLEOne` instances on `v.adicCompletionIntegers` are unreachable). The
prelude is **not ported**.

**Manager-applied reuse wins (set 3.1a, re-verified):**

- **R1** — 3.1a imports `Mathlib.NumberTheory.NumberField.Completion.FinitePlace`
  instead of transcribing InlineSpecific 215–219 (which the first worker did
  verbatim). A duplicated global instance is also a diamond hazard.
- **R3** — the pin's global anonymous `instance … : Algebra O L` for
  `O : ValuationSubring K` (pin line 9) is deliberately dropped: mathlib `v4.34.0`
  already supplies that algebra structure (probe: `inferInstance` closes), and the
  first worker's copy would have been a diamond.
- 3.1a is green after both: `PlaceCompletion.lean` 551 ln, checker 3091 / 0 / 0,
  forced `lake build` 6.8 s, `#print axioms` on the public surface
  `[propext, Classical.choice, Quot.sound]`. Its own closure grew 2817 → 3407 jobs
  (the FinitePlace import); wall time is unchanged, and the number-theory closure
  is largely already in the port's tree.

**R2 — V2 need not import `PlaceCompletion`.** V2's `lg37_completion` carrier is
mathlib `AdicCompletion (maximalIdeal v.toValuationSubring) v.toValuationSubring`,
and V2 has grep count 0 for every `kw_ffgc_*` / `kwHgfV352_*` / `adicCompletion` /
`algebraMapKIntegers` / `KwF4gRRTate` name (probe D1). The pin's import is
vestigial; set 3.1b drops it, so the two sets are **independent** (3.1b need not
wait on 3.1a) and the V2 module's build cascade stays small.

**Import-discharged (statements still land; import, do not re-prove):**
`restrictSubringHom` → `Place.restrictInclusion` (body `rfl`);
`residueFieldMapRestrict` → `Place.restrictResidueMap`; its three instances
(`instIsLocalHom_restrictSubringHom`, `instAlgebra_restrictResidueField`,
`instIsScalarTower_restrictResidueField`) → the port's `restrictInclusion`/
`restrictResidueMap` instances (`Defs/PushPull.lean`);
`uniformizerSubring` → `Place.uniformizerSubring'` (same `.choose`; then
`coe_uniformizerSubring` is `rfl`, `irreducible_uniformizerSubring` is
`choose_spec`); the three private ord helpers `ord_nonneg_of_mem`,
`mem_of_ord_nonneg`, `mem_iff_ord_nonneg` → the **public** port
`Place.{ord_nonneg_of_mem, mem_of_ord_nonneg, mem_iff_ord_nonneg}`
(`Defs/PushPull.lean:43/60/69` — this corrects `rt_instance_advise.txt`, which
listed only the private `LocalResidue` copy); `gate_hasLocalResidue_uniformizer_inv`
→ `gate_localResidue_uniformizer_inv` (`Defs/LocalResidue.lean`).

**Imports the V2 worker may use:** `Mathlib.RingTheory.AdicCompletion.{Algebra,
Completeness}`, `Mathlib.RingTheory.Henselian`,
`Mathlib.FieldTheory.IntermediateField.Adjoin.Basic`,
`Mathlib.FieldTheory.PrimitiveElement`, plus
`FLTForHuman.AlgebraicCurve.Defs.{LocalResidue, IsCurveOver, PushPull, Place}`.
No `import Mathlib`; no `PlaceCompletion`.

**API drift to apply (audit §6):** `AlgEquiv.coe_algHom` (V2:1681, deprecated) →
`AlgEquiv.coe_to_algHom`; `IsAdicComplete.henselianRing` and
`IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub` live in
`Mathlib.RingTheory.Henselian`; `adjoinRootEquivAdjoin` is
`IntermediateField.adjoinRootEquivAdjoin` with `open IntermediateField`;
`AdicCompletion.isAdicComplete` / `.pow_smul_top_eq_ker_eval` take `I.FG` (the pin
already passes `(IsPrincipalIdealRing.principal …).fg`); `evalₐ`/`evalOneₐ`/
`factorₐ_evalₐ_one` live in `Mathlib.RingTheory.AdicCompletion.Algebra`. No
`Place.heightOneSpectrum`/`ramificationIndex`/`restrict` drift was found at the
call sites (audit §8), and the InlineSpecific strengthening of the approximation
lemma (R5) is **not** the route — PlaceCompletion's weaker
`kwHgfV352_exists_sub_mem_adicCompletionIntegers` is mathlib-only.


## 5. Checker wiring, build, verification

Append **last** to `spec/check_flt_statements.py`:
- `SOURCES` += `Definitions/Def_AlgebraicCurve_PlaceCompletion.lean`, then
  `Definitions/Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2.lean` (last so
  no earlier last-name match flips; `Def_AlgebraicCurve_DivisorPushPull` and
  `Def_AlgebraicCurve_LocalResidue` are already listed).
- `PORT_FILES` += the two new modules.

Build discipline: edit loop `timeout 120 lake env lean
-DmaxHeartbeats=4000000 -DautoImplicit=false <file>`; iterate declarations in
`ScratchP3.lean` (do not touch other `Scratch*.lean`); file-done `flock
/tmp/flt_for_human.lock timeout 240 lake build <module>`; no whole-tree
`lake build`; no `sorry`/`admit`/`axiom`; never raise the cap.

Verification:
```bash
cd lean
python3 spec/check_flt_statements.py                    # 0 mismatched / 0 missing
flock /tmp/flt_for_human.lock timeout 240 lake build FLTForHuman.AlgebraicCurve.Defs.PlaceCompletion
flock /tmp/flt_for_human.lock timeout 240 lake build FLTForHuman.AlgebraicCurve.Defs.CanonicalLocalResidueInstanceV2
# #print axioms on instHasCanonicalLocalResidueKStar's witness and completionSection_nonempty_generic
```
Expected checker: identical rises by the new public surface, `0 mismatched / 0
missing`, `30 own-proof` unless a reasoned `OWN_PROOFS` entry is added.
`instHasCanonicalLocalResidueKStar` is an instance but the checker's `DECL_RE`
does parse `instance`, so it is checked by statement; it must **also** be
exercised in a real consumer zone (an actual `example`/theorem that uses the
instance over a curve, not a `#check`).

**Do not run any git command.** Append friction entries under a new `## Set P3.1`
section in `lean/logs/riemann-roch-friction.md`.

## 6. Report shape

Module paths + written lines; checker before → after; bounded build wall time and
command; the scout pre/post estimate and the `InlineSpecific` disposition;
friction highlights; `#print axioms` on the witness and the public surface; the
list of private helpers kept; and **explicitly** every out-of-set declaration
resolved locally with its pin `file:line` (the promotion debt the manager will
close).

## Appendix — inventory

`tools/deps/build/p3_1_inventory.txt`: `decl | kind | line | span | private` for
all 33 + 131 declarations of the two pin files (5 private: 2 in
`PlaceCompletion`, 3 in V2).
