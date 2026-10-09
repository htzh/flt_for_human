# WORKORDER-B1 — the modular polynomial `Φ_N`: leading coefficient, uniqueness, irreducibility, star action

**Status: ready to dispatch.** Five of the six subject-**B** rows of the `ModularCurve` ready shelf
(scoping: [TOPIC-levelN-and-modular-polynomial.md](TOPIC-levelN-and-modular-polynomial.md) §2).
**New files only; no existing Lean module is edited; no promotion is needed; no new definition
layer** — the definition modules these five import are checker-registered (§1). The sixth row is
split off as **B2** and is *not* this order (§2).

Pin `anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`); port mathlib
`v4.34.0`. Checker baseline **7502 identical (313 promoted, 83 renamed), 0 mismatched, 0 missing,
36 own (7538 checked)**; milestone whole-tree build green (9,378 jobs). Target: `+5` identical
(one per headline), helpers `private`, `0 mismatched / 0 missing`.

## 1. Why five and not six — a scoping correction (read this first)

The topic note cut subject B as one set of six on the strength of "**No new definition layer**".
That is **wrong for the sixth row** and the hand-check caught it. The five rows here import
`Definitions/Def_ModularCurve_{X0,LaurentCoeff,PhiGen,JqCoeff}.lean`, and all four are registered
in the checker's `SOURCES`, so their declarations are statement-verified against the port — the
definition layer really is there.

The sixth row, `ModularCurve.fibrePoly_phiTwo_j_eq_prod_veluQuotient2_j`, additionally imports
`Definitions/Def_ModularCurve_FibrePoly.lean` and
`Definitions/Def_ModularCurve_ClassicalModularPolynomials.lean`, and **neither is registered**, and
neither is ported:

| pin module | declarations | port status |
|---|---|---|
| `Def_ModularCurve_FibrePoly.lean` | `fibrePoly` | **`private` only** in `ModularCurve/Degree/PhiData.lean:210` |
| | `eval₂RingHom_intCast_eq_comp` | absent |
| | `fibrePoly_eq_map_reduceModBivar` | absent (needs `reduceModBivar`) |
| | `C_sub_X_pow_eq_neg_pow` | absent |
| `Def_ModularCurve_ClassicalModularPolynomials.lean` | `phiTwoC2/C1/C0`, `phiTwo`, `phiThreeC3/C2/C1/C0`, `phiThree`, `intFibre` | **all ten absent** |
| `Def_ModularCurve_KroneckerTransport.lean` | `reduceModBivar`, `reduceModBivar_X`, `reduceModBivar_C_X` | absent |

`fibrePoly` is named in that row's **statement** (`fibrePoly phiTwo W.j = …`) and occurs in 68 pin
files, and `phiTwo` in 11; the port's only `fibrePoly` is `private` inside `PhiData.lean`, and
`phiTwo` does not exist anywhere in the port. So B2 is definition-layer-first — the manager's own
work order, after this set. **Do not port that row here**, and do not "helpfully" promote
`fibrePoly` or add `phiTwo`: a promotion is a hub edit, and a subagent that believes one is
required **stops and reports** (§7).

## 2. The five rows of this set

| # | headline (`ModularCurve.` prefix) | `S_` lines | content |
|---|---:|---:|---|
| 1 | `ModularPolynomialData.isUnit_leadingCoeff_diag_of_not_isSquare` | 724 | for `N` not a square, `IsUnit (data.Φ.eval₂ (RingHom.id (Polynomial ℤ)) Polynomial.X).leadingCoeff` |
| 2 | `ModularPolynomialData.eq_all` | 75 | `d = d'` for any two `ModularPolynomialData N` — uniqueness |
| 3 | `phiIrreducible_of_prime` | 73 | `PhiIrreducible data` for `p` prime |
| 4 | `ModularPolynomialData.evalSymm_of_prime` | 14 | `EvalSymm data.Φ` for `p` prime |
| 5 | `StarBank.press` | 209 | the star action: `R.Monic`, `R.natDegree = p`, `R.map (algebraMap K (LaurentSeries K)) - C (jqNModC K p) = ∏ b ∈ range p, (X - C (qTwist (ζ^b) (jqModC K)))` |

One story in one layer: the classical facts about `Φ_N` on the already-ported `Φ` machinery.
`port_plan` prices the whole six-row slice at 1,325 raw / **740 net new math lines**; this set is
that minus B2's row (`S_` 230 raw, 8 declarations).

## 3. The statements (verbatim from the wrappers, pin `aa2d8b3`)

```lean
theorem ModularCurve.ModularPolynomialData.isUnit_leadingCoeff_diag_of_not_isSquare (N : ℕ)
    [NeZero N] (hN : ¬ IsSquare N) (data : ModularCurve.ModularPolynomialData N) :
    IsUnit (data.Φ.eval₂ (RingHom.id (Polynomial ℤ)) Polynomial.X).leadingCoeff

theorem ModularCurve.ModularPolynomialData.eq_all (N : ℕ) [NeZero N]
    (d d' : ModularPolynomialData N) : d = d'

theorem ModularCurve.phiIrreducible_of_prime (p : ℕ) [hp : Fact (Nat.Prime p)]
    (data : ModularPolynomialData p) : PhiIrreducible data

theorem ModularCurve.ModularPolynomialData.evalSymm_of_prime (p : ℕ) [hp : Fact (Nat.Prime p)]
    (data : ModularPolynomialData p) : EvalSymm data.Φ

theorem ModularCurve.StarBank.press {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) p) {R : Polynomial K}
    (hR : Polynomial.aeval (jqModC K) R = jqNModC K p) :
    R.Monic ∧ R.natDegree = p ∧
      R.map (algebraMap K (LaurentSeries K)) - Polynomial.C (jqNModC K p) =
        ∏ b ∈ Finset.range p, (Polynomial.X - Polynomial.C (qTwist (ζ ^ b) (jqModC K)))
```

Pinned sources (statement = `Theorems/`, proof = `P2M/Sol/`), replace `refs/heads/main` by the pin
`aa2d8b3`:

* <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag_of_not_isSquare.lean>
  · <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag_of_not_isSquare.lean>
* <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_ModularPolynomialData_eq_all.lean>
  · <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_ModularPolynomialData_eq_all.lean>
* <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_phiIrreducible_of_prime.lean>
  · <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_phiIrreducible_of_prime.lean>
* <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_ModularPolynomialData_evalSymm_of_prime.lean>
  · <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_ModularPolynomialData_evalSymm_of_prime.lean>
* <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_StarBank_press.lean>
  · <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_StarBank_press.lean>

(The local pin clone is `~/proj/fermats-last-theorem`; read the files there.)

## 4. What is already in the port — import, never re-prove

`port_advise` finds **41 declarations with an identical statement already in the port**
(≈397 lines): import them and do not re-prove. All 41 are public in the port; the ones this set
needs, with their port homes:

* `Defs/TS.lean` — `TS_injective`, `TS_coeff_of_lt`, `TS_coeff_neg`, `TS_ne_zero`, `qExpand_qTwist_TS`
* `Defs/Twist.lean` — `qTwistEquiv`, `qTwist_iota_of_pow_eq_one`, `qTwist_TS_one_cycle`
* `Defs/Cyclotomic.lean` — `cycUnit_pow`, `isPrimitiveRoot_pow_div`, `exists_isPrimitiveRoot_cyclotomicField`
* `Defs/PhiAtSlot.lean` — `phiAtSeed_iota_eval`, `phiAtSeed_map`, `phiAtSeed_jq_eval`, `roots_phiProd_conj`, `roots_phiProd_conj_nodup`, `phiProd_conj_eq`
* `PhiSlotRoots.lean` — `roots_prime_at_slot`, `roots_prime_at_slot_nodup`, `roots_prime_at_slot_roots_nodup`, `isRoot_prime_at_slot_iff`, `prod_form_ne_zero`
* `ModularPolynomialUniqueness.lean` — `ModularPolynomialData.eq_of_prime`
* `ModularPolynomialIrreducible.lean` — `aeval_jqN_toAdjoin`, and `toAdjoin_eq_minpoly` beside it

The full table is `tools/deps/build/mc_b_advise.txt` §1 (regenerate with the command in §9).

**Private helpers to re-derive locally `private`** (`port_advise` drags, per target file): the
leading-coefficient file drags **12 helpers ≈305 lines**, of which `prod_form_ne_zero` and
`w1_aeval_jqN_toAdjoin` are already in the port (import those two) and the other ten are new
(`w1_diag_lc_pow` 142, `w1_slot_factor` 54, `w1_prod_ne_zero_leadingCoeff` 16,
`w1_order_sub_{left,right}` 15 each, `w1_toAdjoin_eq_minpoly` 11, `w1_order_eq` 9, `w1_order_TS` 8,
`w1_natDegree_toAdjoin` 4, plus the file's own private `isUnit_leadingCoeff_diag_of_not_isSquare`
17); `eq_all` drags 1 (11); `phiIrreducible_of_prime` drags 2 (its `eq_of_prime` is in the port);
`evalSymm_of_prime` drags 0; `StarBank.press` drags 2 (`press` 54, `coeff_algebraMap_mul` 4).
**No promotion is authorised** — every one of these is `private` at the pin too, or is a copy the
port already holds publicly.

## 5. Deliverable modules

Suggested homes (re-home freely within `ModularCurve/`, recording the choice in the report):

| module | rows |
|---|---|
| `FLTForHuman/ModularCurve/ModularPolynomialLeadingCoeff.lean` | 1 (the heavy one; its 36-declaration prelude goes here once) |
| `FLTForHuman/ModularCurve/ModularPolynomialUniquenessIrreducible.lean` | 2, 3, 4 |
| `FLTForHuman/ModularCurve/ModularPolynomialStarBank.lean` | 5 |

**Only the headlines are public**; everything else is `private` (or imported). Keep the pin's
namespaces (`ModularCurve`, `ModularCurve.StarBank`, `ModularCurve.PhiGen`); statements verbatim,
including binder names; adapt proof bodies to `v4.34.0`; replace the pin's `import Mathlib` with
specific imports. Do **not** edit `ModularPolynomial{Properties,Irreducible,Uniqueness,Assembly,
E4Cube,EvalJ}.lean`, `Degree/PhiData.lean`, `PhiSlotRoots.lean` or any `Defs/` module.

## 6. Build discipline

* edit loop `timeout 300 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>` (writes
  no `.olean`, builds no dependent);
* `flock .lake/flt_build.lock timeout 300 lake build <module>` when a file is done;
* **no whole-tree `lake build`** — the manager runs the milestone build;
* every `lake build` serialized and bounded; never raise the heartbeat cap. On a timeout,
  quarantine and bisect (`ModularPolynomialE4Cube` alone is ~280 s: tell real CPU work from
  another agent's lock by CPU time, and report, do not re-run with a bigger cap).

## 7. Stop and report

Stop and report, with the quotation and the pin line, if: a statement cannot be matched without
moving the pin's text; a proof needs an unported `Definitions/` module beyond the four named in
§1 (report the import verbatim); a helper is genuinely needed publicly and is `private` in a hub
(a promotion is the manager's — this includes `fibrePoly` and anything under `Degree/`); or a
build exceeds its bound and bisecting does not settle it. Do **not** open a new set, and do not
reach into B2's row.

## 8. Wiring

Append to `SOURCES`, last, each target's `Theorems/Thm_ModularCurve_<stem>.lean` and
`P2M/Sol/S_ModularCurve_<stem>.lean`; append each new module to `PORT_FILES`, last. Run the
checker as soon as each module is written and reconcile the `identical` delta to that module's new
public surface before building. The manager reviews and owns the final wiring state.

## 9. Completion report

Module paths and line counts; public/`private` counts; tier-0 wall/CPU and warnings (target **0**);
tier-1 result per module; every local `private` re-derivation with its host; the checker before →
after with the `identical` delta reconciled; one-token mutation on each of the five headlines,
caught and reverted; `#print axioms` on all five (`[propext, Classical.choice, Quot.sound]`);
`git status --porcelain` showing only this set's files; anything you could not match, quoted.

Scoping command (from `tools/deps/`):

```bash
python3 port_advise.py \
  --target ModularCurve.ModularPolynomialData.isUnit_leadingCoeff_diag_of_not_isSquare \
  --target ModularCurve.ModularPolynomialData.eq_all \
  --target ModularCurve.phiIrreducible_of_prime \
  --target ModularCurve.ModularPolynomialData.evalSymm_of_prime \
  --target ModularCurve.StarBank.press \
  --json build/mc_b1_advise.json
python3 port_plan.py --json build/mc_b1_advise.json
```
