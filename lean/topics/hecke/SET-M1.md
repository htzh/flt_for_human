# SET-M1 — the Hecke vocabulary, the cusp/`q`-adic vocabulary, and the modular-unit `q`-expansion (m1–m3)

**Status (2026-09-23): work orders written, not started.** This is the run brief
for the **first** coding set of the `ModularCurve` Hecke-layer effort
([PORTING-MC.md](../PORTING-MC.md)). It authorizes exactly three topics:

| order | work order | object | pin | ≈ port | prereq |
|---|---|---|---|---|---|
| 1 | [TOPIC-m1-hecke-vocabulary.md](TOPIC-m1-hecke-vocabulary.md) | the Hecke correspondence vocabulary (M1) | 5 def modules, 516 lines | 500–650 | AC + ported FFG/Φ vocabulary |
| 2 | [TOPIC-m2-geometric-cusp-vocabulary.md](TOPIC-m2-geometric-cusp-vocabulary.md) | geometric base change, cusps, `q`-adic place, modular unit, `jq`-constants (M3) | 6 def modules, 1,036 lines | 700–900 | m1, AC |
| 3 | [TOPIC-m3-modular-unit-qexpansion.md](TOPIC-m3-modular-unit-qexpansion.md) | the modular-unit `q`-expansion core (M7) | 9 nodes, 1,677 raw / 1,282 content | 1,300–1,600 | m2, ported `ModularForms/*` |

Run m1 → m2 → m3. m1 is the shared vocabulary (including `JZero` and
`modularFunctionFieldBar`, which m2's modules state over); m2 is independent of
m1 except for that `bar` vocabulary; m3 needs m2's `ModularUnit` and the ported
`ModularForms/HeckeQExpansion`/`Hauptmodul`.

This set deliberately takes the **whole vocabulary plus the first analytic
layer**. The two hard stories (the Fricke/inclusion core and the degree/Φ tail)
are SET-M2+ because their routes are priced against the modules this set
actually writes, exactly as [SET-2 of AC](../algebraicCurve/SET-2.md) was written
after SET 1 was reviewed.

## 0. What the port hands over (verified 2026-09-23)

- **`lake build` green**, mathlib `v4.34.0` prebuilt; the paused Hecke effort's
  SET 4 is uncommitted in the working tree and must not be disturbed.
- **Statement checker: 802 identical (53 promoted), 0 mismatched, 0 missing, 14
  own-proof** (`python3 spec/check_flt_statements.py`). This is the baseline.
- The `AlgebraicCurve` vocabulary the Hecke layer consumes is in
  `FLTForHuman/AlgebraicCurve/Defs/` — in particular `Place` and its `≃ₐ`-action,
  `Divisor`, `Correspondence` (`Divisor.correspondence`, `FundamentalIdentityAlong`,
  `FiniteAlong`, `NormFormulaAlong`, `HasPrincipalDivisors`, `Pic0`), and
  `SemilinearAut`.
- The FFG and Φ_p vocabularies are in `FLTForHuman/ModularCurve/Defs/`:
  `Laurent.lean` (`qExpand`, `qExpandₐ`, `coeffMap`, `coeffEmb`,
  `laurentBaseChange`, `coeffMap_qExpand`, `coeffEmb_qExpand`), `Jq.lean`
  (`jq`, `jqN`, `dedekindPsi`, `transcendental_jq`, `evalAtJ`), `Fields.lean`
  (`modularFunctionField(Full)`, `full_degeneracy_le`, `gen_prime`,
  `relfinrank_modularFunctionField`), `PhiGen.lean`, `PhiAtSlot.lean`, `TS.lean`,
  `Twist.lean`, `Cyclotomic.lean`, `PhiSlotRoots.lean` (`TS`, `conj`,
  `phiAtSeed`, `roots_prime_at_slot`), `Polynomial.lean`
  (`ModularPolynomialData`), `JqCoefficients.lean`, and the
  `ModularPolynomial*`/`PhiGen*` proof modules.
- The ported analytic modules: `ModularForms/QExpansionPrinciple.lean`,
  `JqAnalyticModel.lean` (`hasSum_jq_qParam`), `Hauptmodul.lean`
  (`hasSum_qParam_mul{,_laurent}`, `RealL`), `HeckeQExpansion.lean`
  (`hasSum_qParam_hecke{Matrix,DiagMatrix}_smul`), and the automorphic Hecke
  block `Defs/HeckeOperator.lean` (`ModularForm.heckeDiagMatrix` etc.).

## 1. The source of truth, and how to read it

- **Pin**: `anthropics/fermats-last-theorem@aa2d8b3`, local clone
  `~/proj/fermats-last-theorem`. Read it; never modify it.
- A theorem's statement is `Theorems/Thm_<dotted, `_` for `.`>.lean`; its proof is
  `P2M/Sol/S_<same>.lean`. **The wrapper is the statement authority; the `S_`
  file is a reading aid.** Definition modules have no wrapper: match their
  declaration names and signatures against `Definitions/Def_ModularCurve_*.lean`.
- The `S_` files are ~28% `import`/`attribute`/`p2m_*` scaffolding. Drop it.
  `p2m_open`/`p2m_export` only make FLT-internal names visible; the port imports
  the modules directly.
- The pin repeats large private preludes; this set's job is to **import the one
  the port already has**, not to write it again (see each topic's §Dedup).

## 2. Build discipline — read this first

Measured with mathlib prebuilt: `lake env lean <file>` ~4–30 s warm,
`lake build <module>` deps-cached ~2–30 s, full `lake build` green at **4,103
jobs in seconds to about a minute**. The lakefile sets `maxHeartbeats` to
4,000,000 globally, so `timeout` is the only real guard.

- Bound every build: `timeout 60 lake env lean <file>`,
  `timeout 90 lake build <module>`, `timeout 180 lake build`.
- **Expect ≤ 30 s, and treat any build past ~60 s as a blow-up.** A multi-minute
  build is never acceptable, not even while experimenting — a fifteen-minute
  bound is a bug in the work order, not a licence to wait. Quarantine on a
  non-return: bisect, or reproduce in the gitignored `Scratch*.lean` with
  `set_option diagnostics true` and `set_option maxHeartbeats 20000`. Never
  re-run the same file hoping for a different result.
- **Never add or raise `maxHeartbeats`/`maxRecDepth`.** The default cap errors in
  under 20 s; raising it turns a fast error into an unbounded wait. m3's
  `qParam_coeff_unique` is a known stall candidate; restate over the natural type
  instead.
- **Tell a blow-up from contention by CPU time.** Measure with `time` (or
  `/usr/bin/time -v`): high user CPU + timeout is a real blow-up (bisect);
  ~0 CPU wall-time is lock contention with another agent's build (re-run when
  idle — never build concurrently with another agent).
- The two known blow-up families: a `FunLike`-quantified lemma at a bare function
  type, and a concrete `IntermediateField` carrier defeq (see
  [porting-playbook.md](../../porting-playbook.md) §3.11 — the `ifRE` fix).
- Keep imports specific; import the port's modules, never `Mathlib` wholesale.

## 3. Shared conventions

1. Statements verbatim from the wrappers (theorems) or the `Definitions/` files
   (definitions), binders included.
2. **Dedup where FLT duplicates.** Import the port's `TS`/`PhiAtSlot`/`TS`-prelude
   and the `ModularForms` analytic modules; do not re-derive. Record `grep -c`.
3. Checker: append each topic's wrappers to `SOURCES`, each new module to
   `PORT_FILES`, and the pin's definition files (once) to `SOURCES`. Definition
   declarations verify by name. Target **0 mismatched, 0 missing**.
4. A consumer zone per set in `spec/ModularCurveHeckeConsumer.lean`; the checker
   plus a full build is the wire test.
5. `logs/mc-port.md` gains a §m1/§m2/§m3 section (or one §SET-M1); `README.md`
   gains the module rows.
6. **No commits.** The working tree is the hand-off.
7. **Do not touch the paused Hecke face's modules** (`ModularForms/*Hecke*`,
   `Defs/HeckeOperator.lean`, `HeckeAlgebra.lean`, `HeckeLattice.lean`, …) or the
   FFG modules (`ModularCurve/ModularPolynomial*.lean`,
   `FunctionFieldGeneration/*`, `PhiGen*`, `PhiSlotRoots.lean`): other efforts own
   them. Read and import them; do not edit them. If a ported statement needs a
   missing helper, prove it `private` locally and record it.

## 4. Definition of done (per topic and for the set)

- Modules as named; statements verbatim; specific imports.
- `timeout 180 lake build` green, 0 warnings, no `sorry`/`admit`.
- `#print axioms` on the topic's headlines clean
  (`[propext, Classical.choice, Quot.sound]`).
- `spec/check_flt_statements.py`: sources/files appended; **0 mismatched, 0
  missing**, and the identical count ≥ 802.
- Dedup demonstrated with `grep -c` (m1's private preludes, m3's 4-way prelude).
- `logs/mc-port.md` section; `README.md` rows.
- One consumer zone per set, at 0 errors.

## 5. What to report back

1. The per-topic table: modules, port lines, public decls, build, checker
   before/after.
2. **The dedup, measured**: for m1, the four `'`-prelude lemmas the pin re-proves
   (`coeffMap_qExpand'`, `coeffEmb_qExpand'`, `laurentBaseChange_mono'`,
   `qExpand_mem_laurentBaseChange'`) against the ported public ones; for m3, the
   165-line 4-way prelude and `diff | grep -c`.
3. Any declaration that had to be restated or adapted, quoted rather than
   weakened, and whether it should be promoted instead of left `private`.
4. The out-of-cone declarations deliberately ported (with counts) and those
   deliberately deferred (with `grep -c 0`).
5. The SET-M2 hand-off: which m1/m2 declarations the Fricke/inclusion and
   degree topics should import, and any shape decision that constrains them.
