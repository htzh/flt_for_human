# WORKORDER-B2 — the `N = 2` fibre: `fibrePoly phiTwo W.j` as a product over the Vélu quotients

**Status: ready to dispatch.** The sixth and last subject-**B** row of the `ModularCurve` ready
shelf, unblocked by the manager's definition wave ([WORKORDER-B1](WORKORDER-B1-phi-rows.md) §1 and
[TOPIC-levelN-and-modular-polynomial.md](TOPIC-levelN-and-modular-polynomial.md) §2 for the
scoping, which corrected the topic note's "no new definition layer" claim).

**New file only; no existing Lean module is edited; no promotion is needed** — the definition
layer this row needs is now landed and is imported, not re-derived (§2).

Pin `anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`); port mathlib
`v4.34.0`. Checker baseline immediately before this set: **7535 identical (313 promoted,
83 renamed), 0 mismatched, 0 missing, 36 own (7571 checked)**; milestone whole-tree build green
(9,384 jobs). Target: `+1` identical (the headline), helpers `private`, `0 mismatched / 0 missing`.

## 1. The row

| headline | `S_` lines | content |
|---|---:|---|
| `ModularCurve.fibrePoly_phiTwo_j_eq_prod_veluQuotient2_j` | 230 | for an elliptic `W` over a field of characteristic not 2 with three distinct 2-torsion points, `fibrePoly phiTwo W.j = ∏ i, (X - C (WeierstrassCurve.j (W/⟨P i⟩)))` |

`port_plan` prices it at 230 raw / **198 net new math lines**, 7 declaration groups, one 3-line
private helper, no shared block, 0 substitutions (the definitions it consumes are `def`s, which
the substitution table does not count).

Statement, verbatim from the pinned wrapper (`Theorems/Thm_ModularCurve_fibrePoly_phiTwo_j_eq_prod_veluQuotient2_j.lean`):

```lean
theorem ModularCurve.fibrePoly_phiTwo_j_eq_prod_veluQuotient2_j
    {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    (W : WeierstrassCurve K) [W.IsElliptic]
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = 3) (P : ι → K × K) (hP : Function.Injective P)
    (hPeq : ∀ i, W.toAffine.Equation (P i).1 (P i).2) (hPgy : ∀ i, W.veluGy (P i).1 (P i).2 = 0)
    (hΔ : ∀ i, (W.veluQuotient2 (P i).1 (P i).2).Δ ≠ 0) :
    fibrePoly phiTwo W.j =
      ∏ i, (X - C (@WeierstrassCurve.j K _ (W.veluQuotient2 (P i).1 (P i).2)
        ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩))
```

Pinned sources: statement
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_fibrePoly_phiTwo_j_eq_prod_veluQuotient2_j.lean>,
proof <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_fibrePoly_phiTwo_j_eq_prod_veluQuotient2_j.lean>
(the local pin clone is `~/proj/fermats-last-theorem`).

## 2. What is already in the port — import, never re-prove

The wave landed this row's whole definition layer; all of it is public and checker-verified
(the four `Definitions/` files are in `SOURCES`, the three modules in `PORT_FILES`):

| what | port home |
|---|---|
| `ModularCurve.phiTwo`, `phiTwoC2/C1/C0`, `phiThree*`, `intFibre` | `FLTForHuman/ModularCurve/Defs/ClassicalModularPolynomials.lean` |
| `ModularCurve.fibrePoly` (no longer `private` in `Degree/PhiData.lean`) | `FLTForHuman/ModularCurve/Defs/FibrePoly.lean` |
| `fibrePoly_eq_map_reduceModBivar`, `C_sub_X_pow_eq_neg_pow`, `reduceModBivar`, `reduceModBivar_X`, `reduceModBivar_C_X` | same |
| the Vélu quotient layer (`veluQuotient2`, `veluGy`, `j`, `Affine.Equation`) | `FLTForHuman/WeierstrassCurve/Velu/*` (pin `Def_WeierstrassCurve_Velu` / `VeluOrderTwo`, both in `SOURCES`) |

Do not re-declare any of them, and do not edit their modules.

**The pin silo's other six public declarations** — `fibrePoly_phiTwo_eq`, `cubic_expand`,
`coeff_two_identity`, `coeff_one_identity`, `coeff_zero_identity`, `main` — are `S_`-local: the pin
suppresses them with `p2m_export` and no later pin file consumes them. Write them `private` (the
port convention; B1 did the same with the pin's `W1` prelude). The one pin-private helper,
`sixteen_ne_zero`, is 3 lines: re-derive it locally `private`.

## 3. Deliverable module

Suggested home: `FLTForHuman/ModularCurve/ModularPolynomialFibreTwo.lean` (beside B1's three
`ModularPolynomial*.lean` modules). Only `ModularCurve.fibrePoly_phiTwo_j_eq_prod_veluQuotient2_j`
is public. Statements verbatim, binders as the pin writes them; keep the pin's opens; replace the
pin's `import Mathlib` with specific imports; no `sorry`/`admit`/`axiom`/`native_decide`, no bare
`import Mathlib`, no `set_option linter.*` suppression and no heartbeat override.

## 4. Build discipline

* edit loop `timeout 300 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>`;
* `flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.ModularCurve.ModularPolynomialFibreTwo`
  when the file is done;
* **no whole-tree `lake build`** — the manager runs the milestone build;
* every `lake build` serialized and bounded; never raise the heartbeat cap; on a timeout quarantine
  and bisect, and tell real CPU work from another agent's lock by CPU time.

## 5. Stop and report

Stop and report, with the quotation and the pin line, if: the statement cannot be matched without
moving the pin's text; a proof needs an unported definition or theorem (report the import or name
verbatim); a helper is genuinely needed publicly and is `private` in an existing hub (a promotion
is the manager's); or a build exceeds its bound and bisecting does not settle it. Do not open
another set, and do not touch subject A's rows or any `Defs/` module.

## 6. Wiring

Append to `SOURCES`, last, `Theorems/Thm_ModularCurve_fibrePoly_phiTwo_j_eq_prod_veluQuotient2_j.lean`
and `P2M/Sol/S_ModularCurve_fibrePoly_phiTwo_j_eq_prod_veluQuotient2_j.lean`; append
`FLTForHuman/ModularCurve/ModularPolynomialFibreTwo.lean` to `PORT_FILES`, last. Run the checker and
reconcile the `identical` delta to `+1` before building. The manager owns the final wiring state.

## 7. Completion report

Module path and line count; public/`private` counts; tier-0 wall/CPU and warnings (target **0**);
tier-1 result; the local `private` re-derivation(s) with host; the checker before → after with the
`identical` delta reconciled; a one-token mutation on the headline (caught, then reverted);
`#print axioms` on the headline (`[propext, Classical.choice, Quot.sound]`); `git status
--porcelain` showing only this set's files (the tree is dirty before you start — the manager's
notes, B1's three modules and the wave's definition modules are pre-existing; report only your
delta); anything you could not match, quoted.

Reproduce the scoping (from `tools/deps/`):

```bash
python3 port_advise.py --target ModularCurve.fibrePoly_phiTwo_j_eq_prod_veluQuotient2_j \
  --json build/mc_b2_advise.json
python3 port_plan.py --json build/mc_b2_advise.json
```
