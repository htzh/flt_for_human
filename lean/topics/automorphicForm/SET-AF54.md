# SET-AF54 — the place map's ord dictionary, and the non-unit multiple

**Status: LANDED (2026-11-12).** Read off the eleven-marker corrected shelf of SET-AF52/AF53
(`needed` **693 / 291,557**, ready 46 / 9,004).

**2 rows / 547 silo / ≈530 net in 24 declarations** — the two rows AF52 readied, and the last of the
`RegularProlongation` residue chain this column has been climbing since AF45: the place-map dictionary
that turns a chart's uniqueness theorem into an `ord` identity, and the non-unit multiple the residue-span
argument consumes.

| # | row | silo | lev | what it says |
|---|---|---:|---:|---|
| **A1** | `AlgebraicCurve.RegularProlongation.exists_placeMap_mapDomain_eq_ord_of_residue_integralClosure_surjective` | 375 | 1/5 | the chart's place maps to the function field's place with the same `ord` on integral elements |
| **B1** | `AlgebraicCurve.RegularProlongation.exists_nonunit_smul_eq_of_forall_residue_eq_zero_of_sum_finrank_eq` | 172 | 2/2 | under the degree hypothesis, a residue-independent family has a non-unit multiple with all residues zero |

**Premises**: all ported — A1's are AF48's reduced place and AF52's ord equality (`:398`); B1's is AF52's
residue basis (`:261`). **Definition gate**: closed (two `Def_AlgebraicCurve_*` modules, both ported).
**B1 is an ingredient of the Kummer family** (`exists_forall_residue_eq_algebraMap_of_mem_residueSpan_inf_of_krullDimLE_one`,
783, one of the three nodes SET-AF50 §5 named as two sets away), so it shortens that chain.

**Homes and the manager's landed layer** (both scaffolded, elaborated and checker-green before dispatch):

| module | lines | decls | `sorry` | `check_port` |
|---|---:|---:|---:|---|
| `AlgebraicCurve/RegularProlongationPlaceMapOrd.lean` | 187 | 14 | 13 | **14 ok / 0 / 0** |
| `AlgebraicCurve/RegularProlongationNonunitSmul.lean` | 143 | 10 | 9 | **10 ok / 0 / 0** |

The pin's labels `AJDFXC` → `PlaceMapOrd` and `E81QM` → `NonunitSmul` are rectified. Two in-file
substitutes are imported rather than copied: `Red` (AF52's `OrdResidueEquality`) and `inv_adjoin_eq`
(AF48's `ReducedPlace`). **The `172` file's nine-declaration prelude is kept**, not deduped against
`RegularProlongationResidueBasis.lean` (which holds the same prelude from the `261` file): the pin states
them publicly in this file's own label namespace, the two copies carry different `variable … in` preludes,
and the checker diffs them here — the same "deliberately not cut" ruling SET-AF50 gave its `ord_*` blocks.
It is recorded, not silently duplicated.

**Order**: `tmp/af54/WORKORDER-AF54A-place-map-ord-and-nonunit.md` (one dispatch, both modules).

## 2. The landing (2026-11-12)

| module | lines | `sorry` → | `check_port` | build | axioms |
|---|---|---|---:|---|---|
| `RegularProlongationPlaceMapOrd.lean` | 187 → **398** | 13 → 0 | **14 ok / 0 / 0** | 3,883 jobs, 5.4 s | clean |
| `RegularProlongationNonunitSmul.lean` | 143 → **212** | 9 → 0 | **10 ok / 0 / 0** | 3,883 jobs, 4.5 s | clean |
| | **330 → 610** | **22 → 0** | **24 ok, 0 mismatch, 0 missing** | | **2/2** |

Both silent at 200,000 heartbeats with zero warnings (the gate is live: the lakefile's 4M project default is
never exercised), no `set_option` beyond `autoImplicit false`, no silencer, and **zero imports added** — every
cited ported lemma was already reachable, the second set running where the manager's cone was complete.
`dedup` 0 clusters / 0 removable lines on both (and the kept nine-declaration prelude produces no cluster
against `RegularProlongationResidueBasis`, because the two copies are namespace-separated — exactly the
SET-AF50 `ord_*` situation); `move_dead` 0. `#check` at both wrapper names resolves the frozen signatures.

**Two deviations only**: v4.34's `dif_pos`/`dif_neg` → `dite_eq_left`/`dite_eq_right` and `push_neg` →
`push Not` (each was the single warning in its module), plus `haveI` → `have` once. **FR-0187 did not bite** —
no `Subtype`-under-`ord` coercion appeared in this file's proofs.

**One order-vs-landed mismatch, the worker's call being right**: the order's §1 listed
`mem_of_sum_smul_mem_joint` and `linearIndependent_coe_joint` among module 2's declarations; the landed
scaffold does not carry them (they live in AF52's `ResidueBasis`) and carries `coe_constHom` instead. The
worker proved **the file as landed**, changed no statement, and reported the discrepancy — the second time
this session a worker has been right against a manager's declaration table (cf. FR-0185), and the reason the
standing rule is "the pin's text and the landed file win over the order's inventory".

### 2.1 The re-read

| figure | before | **after** | forecast |
|---|---:|---:|---:|
| `needed [F terminal]` | 693 / 291,557 | **691 / 291,010** | 691 / 291,010 ✓ |
| `needed [literal]` | 714 / 298,479 | **712 / 297,932** | — |
| frontier F | 1,713 / 831,468 | **1,715 / 832,015** | +547 ✓ |
| ready rows | 46 / 9,004 | **45 / 8,516** | — |
| `AlgebraicCurve` demand | 33 / 11,824 | **31 / 11,277** | 31 / 11,277 ✓ |
| rows readied | — | **1 / 59** | not forecast, as stated |

Every cell closes exactly on the two rows' 547 lines and 2 nodes. The one row readied is
`exists_placeMap_mapDomain_eq_ord_of_good_constantReduction` (59) — A1's consumer, and the natural next row
of this chain.

**Forecast**: `needed` 693 / 291,557 → **691 / 291,010**; frontier **+547**; `AlgebraicCurve` demand
33 / 11,824 → **31 / 11,277**. Rows readied are measured at the landing (A1's five consumers include the
310-line `exists_constantReduction_isGood_and_forall_residueField_pow_pow_eq_self`; B1's two are the 783 and
1,116-silo residue-span rows).

**Not this set**: the `EisensteinGeneral.Piece` factorization (890) — **its definition gate is not ported**
(`Def_EisensteinGeneral_FactorizationDatum` and the five `Def_AutomorphicForm_*` modules have no port
declarations), so it needs a definition wave before an order; the adelic-box pair (129 + 122, whose home
needs the `AutomorphicForm/Adelic` cone); and the Kummer root-lifting family, which B1 now brings one node
closer.
