# SET W4 — generalise the near-duplicates, demote the adapters, close out

**Status: width family done — remaining: MF-class `qExpansion_coeff_width` copies, adapters,
close-out.** Fifth and last coding set of the [WeightOne rectification](TOPIC-weightone-rectify.md).
SET-W1–W3 removed the *identical* duplication. What remains is the part that is not
byte-identical: declarations that say the same thing with different binders, declarations
that are trivia rather than mathematics, and the bookkeeping that closes the effort.

## Execution record

- **Width family (done).** `ModularForms/QExpansionCoeff.lean` now carries the Γ spelling
  `qExpansion_coeff_widthN` (explicit `N`, `[NeZero N]`), the function-form
  `qExpansion_coeff_width` (alias of `qExpansion_coeff_width_fn`), `qParam_one_eq_pow` and
  `qExpansion_coeff_unique'`. Deleted the function-form `qExpansion_coeff_width` and
  `qParam_one_eq_pow` from `FrickeFunction`/`LevelFraction`/`LevelN`/`LevelOneHauptmodul`/
  `WeierstrassPTorsion`, `qExpansion_coeff_unique'` from the Γ modules and `LevelN`, and the
  width-`N` copies earlier. `--blocks` 5,737 → **5,333** over the two slices.
- **Still unshared.** `ModularFormClass.qExpansion_coeff_width` copies in
  `LevelOneHauptmodul`/`WeierstrassPTorsion` (their namespace is `WLight.ModularFormClass`)
  need deleting plus qualified-reference rewrites; the `Gamma0Integral`/`Gamma0Rationality`
  `qParam_one_eq_pow` spellings (`τ : ℍ`) differ from the home's (`τ : ℂ`).

## 0. Scope

### 0.1 Generalise, do not copy twice (playbook §2, "deduplicate at the source")

The statement-level grouping found 56 names whose copies differ only in binder spelling or
in which predicate they belong to. Resolve each to **one** declaration:

| family | decision |
|---|---|
| `qExpansion_coeff_width` vs `qExpansion_coeff_widthN` | one lemma; the width-`N` form is the general one (`N = 1` specialisation may be kept as a one-line alias if a caller's statement needs it) |
| `zetaN` / `zetaK` (section-variable vs explicit `N`) | one, with the binder spelling the consumers' statements need |
| `conj_mem_Gamma` / `conj_mem_Gamma1` (+ explicit-`N` variants) | one per subgroup (`Gamma`, `Gamma1`); drop the explicit-`N` duplicate |
| `add`/`mul`/`pow` on `KPole`, `NiceK`, `PoleBounded`, `GoodAt`, `BddA`, `IsRat`, `CoeffIn`, `IsFQ`, `Nice` | **not** duplicates — distinct predicates. Give each predicate's lemmas its namespace so the names stop colliding (`KPole.add`, `NiceK.mul`, …) and they stop dominating the tool report |
| `qExpansion_coeff_unique'`, `analyticAt_cuspFunction_zero_of`, `periodic_mul`, `mul`/`add` on the analysis predicates | one each in the generic home; the consumers lose their copies |

### 0.2 Demote the adapters (§9)

Anything that merely re-exposes another theory's API — coercions, `_apply`, `_mono`,
`_congr`, `_self`, one-line `rfl` restatements — stays `private` in its consumer and is not
public in a home. `port_graph.py` listed ten such duplicates totalling 37 lines
(`cw_apply`, `full_congr`, `mono`, `sl_smul_apply`, `smul_eq_coe_smul`,
`smulLatticeEquiv_coe`, `levelRing_coe_smul`, `ring_coe_smul`, `phiOf_apply`,
`cwAlgHom_apply`); re-derive the list after W2/W3 and demote any that were wrongly
promoted.

### 0.3 Not authorized

No re-porting, no statement changes, no new mathematics; the six headlines and the capstone
are frozen; FFG/T-side untouched; no commits.

## 1. Bookkeeping

- `spec/check_flt_statements.py`: reconcile `PORT_FILES` with the final layout — every module
  that now carries a public ported declaration is listed; any module whose *only* public
  content was moved away is removed from `PORT_FILES`. Confirm the `identical` count moves
  only by the deliberately demoted declarations, which are listed in the report; a drop of
  exactly the demoted number is the expected signal (§9).
- `README.md`: update the module rows (path, subject, one-line role) for every new/renamed
  module; the rows for demoted content say where it went.
- `topic`/plan docs: mark [TOPIC-weightone-rectify.md](TOPIC-weightone-rectify.md) done and
  record the before/after in `logs/weightone-rectify.md` (owner: the manager; the set
  executor supplies the numbers).

## 2. Verification (all four must pass)

```bash
cd lean
timeout 180 lake build                       # green, 0 warnings, no sorry
python3 spec/check_flt_statements.py         # 0 mismatched, 0 missing; identical accounted for
timeout 120 lake env lean spec/WeightOneConsumer.lean
cd ../tools/deps && python3 port_graph.py --blocks 5 --no-json   # no block over threshold
```

Plus `#print axioms` on `CuspForm.exists_basis_gamma1_qCoeff_slash_mem_range_intCast`,
`CuspForm.span_frickeRational_E4_pow_E6_pow_eq_top`,
`CuspForm.hasIntegralStructure_of_basis_gamma1`, `CuspForm.hasIntegralStructure_of_two_le`,
`CuspForm.hasIntegralStructure_two` and `ModularForm.weierstrassP_torsion_qExpansion_package`
— all `[propext, Classical.choice, Quot.sound]`.

## 3. Definition of done

- `port_graph.py --blocks` removable-line figure for the weight-one cluster falls from
  **7,242** to under the 100-line display threshold.
- Every declaration with an identical statement appears once; the near-duplicates are one
  each; adapters are private.
- All four commands green; the checker total and the demotion list reconcile exactly.
- `logs/weightone-rectify.md` records: before/after removable lines, modules created/removed,
  declarations generalised, adapters demoted, the checker delta.

## 4. What to report back

1. The generalisation table: each family, the chosen form, the copies deleted, the call
   sites adjusted.
2. The adapter demotion list with the checker count before/after and the reconciliation.
3. The `port_graph.py --blocks` before/after.
4. The four verification command results, verbatim tails.
5. Any near-duplicate that could **not** be unified (differing statements) and why it must
   stay two.
