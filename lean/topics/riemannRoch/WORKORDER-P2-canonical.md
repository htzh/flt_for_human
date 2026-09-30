# Work order — P2: the canonical divisor (`hasCanonicalDivisor_of_isCurveOver`)

**Status: ready to dispatch.** Phase 2 of [../PORTING-RR.md](../PORTING-RR.md): the
construction that gives every curve a canonical divisor, unblocking the
differentials layer and the `HasCanonicalDivisor` interfaces. Method:
[../porting-playbook.md](../porting-playbook.md) §2–§5; precedent sets and review
gates as in [PLAN.md](PLAN.md) and the phase-1 work orders in this directory.

Baseline after phase 1: checker **2944 identical / 0 mismatched / 0 missing / 30
own-proof** (2974 checked); full `lake build` green (4830 jobs); consumer
`spec/RiemannRochConsumer.lean` 0 errors.

## 0. Scope

One target **plus its two unported Kähler prerequisites**:

| target | pin | raw |
|---|---|---:|
| `AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver` | `P2M/Sol/S_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver.lean` | 1,723 |
| `KaehlerDifferential.span_D_eq_top_of_transcendental` | `P2M/Sol/S_KaehlerDifferential_span_D_eq_top_of_transcendental.lean` | 64 |
| `KaehlerDifferential.D_ne_zero_of_transcendental` | `P2M/Sol/S_KaehlerDifferential_D_ne_zero_of_transcendental.lean` | 63 |

Raw ≈1,850; content ≈1,200–1,400. Most of the 130 declarations in the big file are
`private` helpers over a chain of **public model predicates**
(`ValSubringKaehlerSpanTop`, `ValSubringPolynomialFormallyUnramified`,
`ValSubringKaehlerFinite`, `ValSubringEssFiniteType`, `ValSubringFiniteTypeModel`,
`ValSubringDedekindModel`, `ValSubringDedekindFractionModel`,
`ValSubringTwoAffineCharts`, `HasSeparatingTranscendental`, …) — those public
predicates are the construction's interface and must land public.

**Explicitly not this set:** phase 3 (the analytic `ResidueTheorem` block), phase 4
(the cusp-form transport), the `ModularCurve.*_hasCanonicalDivisor_*` consumers, and
`instHasCanonicalDivisorRatFuncPerfectField` (a separate `S_` file — report if the
target needs it; do not port it here without saying so).

## 1. Deliverables

| new module | content | pin |
|---|---|---|
| `FLTForHuman/AlgebraicCurve/Defs/KaehlerTranscendental.lean` | the two `KaehlerDifferential.*` theorems + their private preludes | the two `S_KaehlerDifferential_*` files |
| `FLTForHuman/AlgebraicCurve/Canonical/HasCanonicalDivisor.lean` | the whole target `S_` union, headline spelled from the wrapper | `S_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver.lean` |

Keep the pin's namespaces (`KaehlerDifferential.*`, `AlgebraicCurve.*`). Import the
port's already-landed vocabulary — **do not re-prove**:
`Defs/{IsCurveOver,CanonicalDivisor,PlacesOverDVR,AdelicIndex,Repartitions,PushPull}`,
`WeilExchange/{Bifibre,FiberOverCount}` (`Place.fiberOver`, the ramification
identity), `IsCurveOver/SeparatingTranscendental` (`IsCurveOver.exists_separating_transcendental`),
`Defs/WeilOfKaehler` if the pin body reaches it.

## 2. Statements

The headline's wrapper is
`Theorems/Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver.lean`:

```lean
theorem AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    [PerfectField K] [Algebra.EssFiniteType K F] [AlgebraicCurve.IsCurveOver K F] :
    AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)
```

The two Kähler wrappers take **explicit `(K : Type*)` and implicit `{F : Type*}`**:

```lean
theorem KaehlerDifferential.span_D_eq_top_of_transcendental (K : Type*) [Field K] {F : Type*}
    [Field F] [Algebra K F] (x : F) (hx : Transcendental K x)
    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F] :
    Submodule.span F ({KaehlerDifferential.D K F x} : Set (KaehlerDifferential K F)) = ⊤

theorem KaehlerDifferential.D_ne_zero_of_transcendental (K : Type*) [Field K] {F : Type*}
    [Field F] [Algebra K F] (x : F) (hx : Transcendental K x)
    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F] :
    KaehlerDifferential.D K F x ≠ 0
```

Spell all three from the wrappers; the rest of the union from the `S_` files.
**Never change a statement to ease a proof.** The pin's `p2m_export`/`p2m_open`/
`p2m_reactivate`/`attribute [-instance]`/`attribute [-simp]` scaffolding is dropped
(port them as ordinary `open`/local instances only where the proof needs them).

## 3. Route and risk

- **The construction is transcription, not new mathematics.** The `S_` file is the
  pin's own proof; the port walks the same model chain. The genuinely load-bearing
  port imports are `IsCurveOver.exists_separating_transcendental` (separating
  transcendence, landed by the refactor round) and the `fiberOver` ramification
  identity (landed by the AC effort).
- **Scout gate (playbook §2.6):** before writing the 1,400-line module, prototype the
  spine in `ScratchP2.lean` — `span_D_eq_top_of_transcendental` →
  `valSubringKaehlerSpanTop_of_…` → `hasCanonicalDivisor_of_generator_finiteSupport_s12` →
  the headline — and record the pre/post estimate. The H1b experience says the
  estimate will hold.
- **Recorded reuse:** `port_advise` reports `ord_nonneg_of_mem_s12` matches the
  port's `AlgebraicCurve.Place.ord_nonneg_of_mem_vs`
  (`Canonical/WeilDifferential.lean`) — import it, do not re-prove. The other
  `--nodes` "substitutions" are the known `def … : Prop` false positives; do not
  bank them.
- **Stop-early risks** (stop and report the pin `file:line`):
  1. a `Place.*`/`Divisor.*` lemma the `S_` file needs is absent from the port's
     `Defs/PlacesOverDVR.lean`/`PushPull.lean` (name or statement drift);
  2. `KaehlerDifferential` API drift needing more than a rename;
  3. the target reaches a declaration **outside** the three measured `S_` files (the
     H2/H3 measurement gap). **Resolve it locally `private` with the statement
     verbatim, and report it as promotion debt — do not inline new mathematics and
     do not edit a frozen module.** The manager closes that gap in the follow-up
     round.
- The private helpers the pin marks `private` stay `private` here (record the list);
  the pin-public model predicates are public.

## 4. Audit fold-in (`AUDIT-mathlib-p2.md`, landed)

The phase-2 mathlib audit classifies **140** declarations (the inventory's 134 omits
six `instance`s): 6 SUBSTITUTE, 111 PROOF-INGREDIENT, 23 BESPOKE. **Import-discharged**
(statement still lands for the checker): `Place.eq_of_isDiscreteValuationRing_of_le_s12`
← `ValuationSubring.eq_of_le_of_ne_top`; `Place.isIntegrallyClosed_toValuationSubring`
← the `IsIntegrallyClosed V` instance; `isScalarTower_integralClosure_subalgebra` ←
`inferInstance`; `Place.ord_nonneg_of_mem_s12`/`mem_of_ord_nonneg_s12`/
`ord_uniformizerSubring'_s12` ← the port's `Place.ord_nonneg_of_mem`/
`mem_of_ord_nonneg`/`ord_uniformizer`; drop the three `uniformizerSubring'` aliases in
favour of `Place.uniformizer`. Twelve rows are one-mathlib-call rewrites (audit §6).
The two Kähler modules import **mathlib only**; the one v4.34.0 edit is
`AlgEquiv.coe_algHom` → `coe_toAlgHom`. Keep bespoke: the 11 public model predicates,
the `centerIdeal` block, `ofPrime_congr_s12`/`eq_top_of_idealOfLE_eq_bot_s12`/
`idealOfLE_ne_bot_of_ne_top_s12` (probe V1b: mathlib cannot rewrite under `ofPrime`),
and `finite_ordDifferential_D_ne_zero_s12`. **No stop-early risk:** the target reaches
only the three `S_` files plus already-landed port lemmas.

## 5. Checker wiring, build, verification

Append **last** to `spec/check_flt_statements.py`:
- `SOURCES` += the three `Theorems/Thm_*` wrappers **first**, then the three `S_`
  files (wrapper binder authority).
- `PORT_FILES` += the two new modules.

Build discipline: edit loop `timeout 120 lake env lean
-DmaxHeartbeats=4000000 -DautoImplicit=false <file>`; iterate declarations in
`ScratchP2.lean` (do not touch the other `Scratch*.lean`); file-done
`flock /tmp/flt_for_human.lock timeout 240 lake build <module>`; no whole-tree
`lake build`; no `sorry`/`admit`/`axiom`; no `import Mathlib`; never raise the cap.

Verification:
```bash
cd lean
python3 spec/check_flt_statements.py                    # 0 mismatched / 0 missing
flock /tmp/flt_for_human.lock timeout 240 lake build FLTForHuman.AlgebraicCurve.Canonical.HasCanonicalDivisor
# #print axioms on the headline and the two Kähler theorems
```
Expected checker: identical rises by the new public surface; `0 mismatched / 0
missing`, `30 own-proof` unless a reasoned `OWN_PROOFS` entry is added.

**Do not run any git command.** Append friction entries under a new `## Set P2`
section in `lean/logs/riemann-roch-friction.md`.

## 6. Report shape

Module paths + written lines; checker before → after; bounded build wall time and
command; the scout pre/post estimate; friction highlights; `#print axioms` on the
three headlines; the list of private helpers kept; and **explicitly** every
out-of-set declaration resolved locally with its pin `file:line` (the promotion debt
the manager will close).

## Appendix — inventory

`tools/deps/build/p2_inventory.txt`: `kind | line | span | private | name` for all
134 declarations of the three `S_` files.
