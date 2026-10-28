# WORKORDER-MC1b — the resultant divisibility and the coefficient-degree bound

Status: **landed 2026-10-27** (SET [MC-1](SET-MC1.md), order MC-1b). Both rows inserted into
`lean/FLTForHuman/ModularCurve/ModularPolynomialUniquenessIrreducible.lean` (123 → 332 lines).
Manager-verified on the same tree: `check_port --force` **8 ok / 0 mismatch / 0 missing / 0 own**
(the five pre-existing verdicts still `ok`); axioms `[propext, Classical.choice, Quot.sound]` on
`dvd_resultant_of_mul`, `natDegree_coeff_le`, `natDegree_coeff_le'`; the module **and its one
dependent `ModularPolynomialLeadingCoeff`** build silent; zero warnings; no options.
Four private helpers, each used only by its row: `qExpand_comp_evalAtJ`, `swapInner_eq_map`,
`swapBivar_C_mul_X_pow`, `coeff_coeff_swapBivar` (`Degree/PhiData` holds the same statement as its
own private — a private cannot be imported, and it may not be edited from this order).
`evalAtJGen_injective` was **not** re-written (it is public and identical at
`ModularPolynomialIrreducible.lean:106`); a pin-shaped restatement would have been a facade.
The suggested `Degree/PhiDegree` import was acyclic but unnecessary (`transcendental_jq` is
`Defs/Jq.lean`'s); the reviewer removed it — one fewer edge, gates unchanged.
The `dedup` reading's two intra-module shape clusters are the pin's own pair and a pre-existing
one: recorded, not folded (the order requires both forms).

| node | pin `S_` | pin lines | declares | frontier |
|---|---|---:|---|---|
| `ModularCurve.ModularPolynomialData.dvd_resultant_of_mul` | `P2M/Sol/S_ModularCurve_ModularPolynomialData_dvd_resultant_of_mul.lean` | 134 | 3 | needed 1, cone 1 / project 1 |
| `ModularCurve.ModularPolynomialData.natDegree_coeff_le` | `P2M/Sol/S_ModularCurve_ModularPolynomialData_natDegree_coeff_le.lean` | 62 | 5 | needed 1, cone 1 / project **10** |

Read [SET-MC1.md](SET-MC1.md) first (§1, §3 — **including the import-direction caveat**, §4, §5).
**Pin**: `/home/haitao/proj/fermats-last-theorem` at `aa2d8b3`.
**Port**: `/home/haitao/proj/reasonix-sandbox/flt_for_human/lean`.

## 1. What to write

**Insert both rows into `lean/FLTForHuman/ModularCurve/ModularPolynomialUniquenessIrreducible.lean`**
(no new module), in two sections:

**(a) the 134 row** — `evalAtJGen_injective`, `qExpand_comp_evalAtJ` (both in the pin's local
`P2MKcResPhi` namespace — keep a local namespace so `evalAtJGen` cannot collide), and the headline
`dvd_resultant_of_mul` from the `Theorems/` wrapper (16 lines). The proof: evaluate the resultant
identity at `Ξ : B →+* LaurentSeries ℚ` with `Ξ C = evalAtJ` and `Ξ X = jqN (ℓ*M)`, rewrite
`qExpand` along the evaluation (`qExpand_comp_evalAtJ`), use `minpoly_jqN_eq` and `phiIrreducible_all`
(imported/in-module), and conclude divisibility from `evalAtJGen_injective`. `minpoly_jqN_eq` is in
`ModularPolynomialProperties.lean` (already imported by the home); `transcendental_jq` is **not** —
see §2.

**(b) the 62 row** — `swapInner_eq_map`, `swapBivar_C_mul_X_pow`, `coeff_coeff_swapBivar`,
`ModularPolynomialData.natDegree_coeff_le'` and the headline `natDegree_coeff_le` from its wrapper
(10 lines). The two premises are ported: `evalSymm_of_prime` (this module) and
`swapBivar_eq_of_evalSymm` (`ModularPolynomialIrreducible.lean`, already reachable through
`Degree/PhiData`).

**Wire**: add exactly four lines to the module's leading block —

```
spec-pin: Theorems/Thm_ModularCurve_ModularPolynomialData_dvd_resultant_of_mul.lean
spec-pin: P2M/Sol/S_ModularCurve_ModularPolynomialData_dvd_resultant_of_mul.lean
spec-pin: Theorems/Thm_ModularCurve_ModularPolynomialData_natDegree_coeff_le.lean
spec-pin: P2M/Sol/S_ModularCurve_ModularPolynomialData_natDegree_coeff_le.lean
```

The module's five existing wires and its five existing declarations stay as they are.

## 2. The one structural decision: the `transcendental_jq` import

The 134 proof needs `transcendental_jq`, which lives in `ModularCurve/Degree/PhiDegree.lean`. The
home doés not import it today. `PhiDegree` imports `Degree/PhiData`, `Analytic/ModularUnitQExpansion`
and `PhiGenDescendsStructure`, and only `ModularPolynomialLeadingCoeff.lean` imports the home, so a
new `import FLTForHuman.ModularCurve.Degree.PhiDegree` is *expected* to be acyclic — **test it
first** (add the import, build). If it cycles, do **not** work around it by restating anything: move
**both** rows of this order to a new module `ModularCurve/ModularPolynomialResultant.lean` above
both sides, and say so in your report. The recipe's rule is absolute: a home below a premise is a
cycle, not a cost.

## 3. Rules (the set's standing ones)

- **No duplicated mathematics, no facades**: the one substitution (`minpoly_jqN_eq`'s chain) is
  imported; no pin-shaped wrapper around an existing port lemma. The 62 row's `natDegree_coeff_le'`
  is a pin declaration (a stronger form) — write it, do not fold it into the headline.
- No `set_option maxHeartbeats` / `synthInstance.maxHeartbeats`; **no linter suppressions** — fix
  warnings instead (FR-0054: `haveI → have`; `omit` only on a private declaration).
- No `sorry`/`admit`/`axiom`/`native_decide`; no edits outside the home module (plus an axioms probe
  in `lean/tmp/`); no `git` writes.

## 4. Gates

1. edit loop at `-DautoImplicit=false -DmaxHeartbeats=200000` → silent;
2. `python3 spec/check_port.py --force FLTForHuman/ModularCurve/ModularPolynomialUniquenessIrreducible.lean`
   → **0 mismatch, 0 missing**, and the five pre-existing `ok`s still `ok`;
3. `#print axioms` on both headlines and on `natDegree_coeff_le'` →
   `[propext, Classical.choice, Quot.sound]`;
4. `flock /tmp/dsh-lake.lock lake build FLTForHuman.ModularCurve.ModularPolynomialUniquenessIrreducible`
   → builds, `.olean` present, no dependents; **and** build the module you added the import from
   (`Degree.PhiDegree`) if it was not already built;
5. `dedup.py --module` on the module → report the reading (no new cluster expected);
6. zero warnings.

## 5. Report back

The checker summary and the five pre-existing verdicts, the axioms lines, the build's last two
lines, the final line count, whether the `PhiDegree` import was acyclic (and what you did
otherwise), the declarations kept `private` (with the reason), and any deviation. The module's
prose header should gain a line naming the two rows it now hosts.
