# SET MC-1 — M2, the modular polynomial one level up

**Status: scoped and dispatched (2026-10-27).** The shelf's **MC-1**
([TOPIC-ready-shelf.md](TOPIC-ready-shelf.md) §1) is story **M2**: the three
`ModularPolynomialData` rows that lift the modular polynomial one level — the fibre product over
the Vélu quotients at an *algebraically closed* field, the multiplicativity of `Φ` under `ℓ · M`,
and the coefficient-degree bound. 706 silo; the shelf priced it at **630 net** with **no
definition gate**; this brief re-reads it against the tree M1 left (§7 of
[SET-MC7.md](SET-MC7.md)) and cuts it as **two orders on two disjoint landed modules**.

| figure | value |
|---|---:|
| `ModularPolynomialData` ready rows | **3 / 706** |
| their net (shelf's `port_advise`) | 630 |
| definition gate | **none** (the four `Def_` modules are ported whole) |
| new modules | **none** (two insertions) |
| promotions / migrations | none |
| after-read target | the three rows leave; MC shelf 23 → 20 |

## 0. The read

The three rows are on the corrected shelf and on the instrument's alike (none carries a marker,
none is a leaf, none is withheld):

| row (`ModularCurve.ModularPolynomialData.` dropped) | silo | prem | lev (cone / project) |
|---|---:|---:|---:|
| `fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental_of_isAlgClosed` | 510 | 2 | 1 / 1 |
| `dvd_resultant_of_mul` | 134 | 3 | 1 / 1 |
| `natDegree_coeff_le` | 62 | 2 | 1 / **10** |

The 62 row has the largest project leverage of the MC block: the coefficient-degree bound is read
by ten declarations across the column (the `Φ`-degree estimates), so it is the cheapest row with
the widest fan-out — the recipe's "demand is inverted relative to size" again.

**No definition gate.** The pin's `Def_ModularCurve_X0`, `Def_ModularCurve_FibrePoly`,
`Def_ModularCurve_PhiGen`, `Def_WeierstrassCurve_Velu` and `Def_WeierstrassCurve_OddOrderSummingSet`
are all in the shelf's "fully ported (21)" list; `HahnSeries.isAlgClosed_rat` is in the port
(`RingTheory/HahnSeries/IsAlgClosed.lean`, already imported by the 510 home). Spot checks:
`ModularCurve.X0`/`FibrePoly`/`PhiGen` and `WeierstrassCurve.Velu.*` resolve at their pin names.

## 1. The rows

**510 — `fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental_of_isAlgClosed`.**
`fibrePoly data.Φ W.j = ∏ i, (X - C (j (W.veluQuotient (W.oddOrderSummingSet (Q i) (ℓ/2)))))`
for `W` over an algebraically closed field of characteristic zero, `Q : ι → W.Point` of exact
order `ℓ`, pairwise distinct subgroups, and `Δ ≠ 0` at each quotient. The pin's `S_` file (510
lines, **30 declarations, none in the port**) is the *descent* that the ported transcendental node
(`ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental`, in the
home module) does not perform: a `TDescent` block which maps `W` along a ring hom (`mapFun`,
`mapPoint : Point →+ Point`), commutes Vélu with the map (`map_veluT`, `map_veluW`,
`veluQuotient_map`), covers the field by `ℓ+1` points (`exists_cover`), embeds the coefficient
field into `HahnSeries ℚ (AlgebraicClosure ℚ)` (`aleph0_lt_mk_hahn`, `nonempty_ringHom_hahn`,
`exists_cover_hahn`), and assembles `aux`/`main` to reach the transcendental node at
`W.map φ`. **The product form is not re-proved.**

**134 — `dvd_resultant_of_mul`.** `dN.Φ ∣ (dℓ.Φ.map C).resultant (dM.Φ.eval₂ … (C X))` for
`dℓ, dM, dN` at `ℓ`, `M`, `ℓ*M`. The pin's `S_` (134 lines, 3 declarations, 1 in the port) is
small and its proof is one evaluation: apply the ring hom `Ξ : B →+* LaurentSeries ℚ` at
`jqN (ℓ*M)`, use `qExpand_comp_evalAtJ` and `evalAtJGen_injective`, and read the resultant as the
product over the roots via `minpoly_jqN_eq` and `phiIrreducible_all`.

**62 — `natDegree_coeff_le`.** `(data.Φ.coeff k).natDegree ≤ p + 1` for `p` prime. The pin's `S_`
(62 lines, 5 declarations, none in the port) first transports the coefficient bound to a `swapBivar`
normal form (`swapInner_eq_map`, `swapBivar_C_mul_X_pow`, `coeff_coeff_swapBivar`) and then gets
`natDegree_coeff_le'` from the two ported premises `evalSymm_of_prime` and
`swapBivar_eq_of_evalSymm`; `solution` is its specialisation.

## 2. The pricing

`port_advise` per row, on the tree after MC-7:

| row | target decls | already in the port | note |
|---|---:|---:|---|
| 510 | 30 (+1 wrapper) | **0** | all new; the product form is a *premise*, not a copy |
| 134 | 3 (+1) | 1 (≈9 lines, binder spelling) | `minpoly_jqN_eq`'s chain is imported |
| 62 | 5 (+1) | 0 | the two premises are ported (`evalSymm_of_prime` in the home, `swapBivar_eq_of_evalSymm` in `ModularPolynomialIrreducible.lean`) |

Net ≈ **630** (the shelf's figure), of which the 510 order is ≈450 and the 134+62 order ≈180.
The pin's own duplication is nil here (`port_advise` finds no name proved in two target files), so
the SET-MC7 rule has nothing to resolve; the one substitution (the 9-line binder variant) is
imported, not copied.

## 3. Homes

Method as in the recipe §4, and confirmed against the import graph:

| order | row | home | why |
|---|---|---|---|
| **MC-1a** | 510 | **insert** `ModularCurve/ModularPolynomialVelu.lean` | the module already hosts the transcendental node and imports `RingTheory/HahnSeries/IsAlgClosed.lean`, i.e. it is above both premises; the descent's `WeierstrassCurve/Velu/*` API is already imported |
| **MC-1b** | 134, 62 | **insert** `ModularCurve/ModularPolynomialUniquenessIrreducible.lean` | it hosts `eq_all`/`evalSymm_of_prime`/`phiIrreducible_all` (two of the five premises) and `Degree/PhiData` already imports `ModularPolynomialIrreducible` (the 62 row's second premise) |

**One import-direction check, resolved — and a scoping correction.** The 134 row needs
`transcendental_jq`, and this brief first placed it in `Degree/PhiDegree.lean`. That was wrong:
the port's `ModularCurve.transcendental_jq` is in **`Defs/Jq.lean:190`** (the pin's
`Thm_ModularCurve_transcendental_jq` is that file), already in the home's cone, while
`Degree/PhiDegree:74` hosts the *different* `transcendental_jqModC`. MC-1b added the suggested
`import … Degree.PhiDegree` (acyclic, as predicted) and then verified the module elaborates
without it; the reviewer removed it, and the module builds, checks 8 ok / 0 / 0, and has one fewer
import edge. The one import the proof genuinely needs is
`Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure` (the pin gets it from FLT's glob imports).
`minpoly_jqN_eq` is in `ModularPolynomialProperties.lean`, already imported by the home.
The recipe's rule stands: a home below a premise is a cycle, not a cost — but the check is worth
doing against the *port's* declarations, not the pin's file names.

## 4. The orders

| order | rows | home | silo | est. net |
|---|---|---|---:|---:|
| **MC-1a** | 510 | `ModularPolynomialVelu.lean` | 510 | ≈450 |
| **MC-1b** | 134, 62 | `ModularPolynomialUniquenessIrreducible.lean` | 196 | ≈180 — **landed**, 8 ok / 0 / 0; dedup's two intra-module shape clusters (`natDegree_coeff_le'`/`natDegree_coeff_le`, the pin's own pair, and the pre-existing `phiIrreducible_*` pair) are the recorded exception |

Workorders: [WORKORDER-MC1a-fibre-poly-isAlgClosed.md](WORKORDER-MC1a-fibre-poly-isAlgClosed.md),
[WORKORDER-MC1b-resultant-and-degree.md](WORKORDER-MC1b-resultant-and-degree.md).

**MC-1a traps.** (i) The transcendental product form is **ported**: call
`ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental`; do not
re-prove a line of it. (ii) `mapPoint` is a *group hom* built from `mapFun` — the pin proves
`mapFun_add` by coordinate chase through the chord/tangent cases; keep the pin's case order.
(iii) `veluQuotient_map` needs `Set.InjOn (Prod.map φ φ) T`; the descent's `φ` is a *field*
embedding, so injectivity is free but the `T` in question is a `Finset` of coordinate pairs —
spell it as the pin does. (iv) The `HahnSeries` embedding uses a **cardinality** argument
(`aleph0_lt_mk_hahn`); the pin's `nonempty_ringHom_hahn` is an `IsAlgClosed`-free statement and
must be taken at its pin shape. (v) `ConclT`/`j_congr` are the pin's `Prop`-valued packaging of
the conclusion; keep them (they are what makes `conclT_map_iff` usable).
**MC-1b traps.** (i) `evalAtJGen_injective` is a `P2MKcResPhi` local lemma in the pin; keep it in
a local namespace so its name cannot collide (`evalAtJGen` exists in the port). (ii)
`qExpand_comp_evalAtJ` is a `RingHom.ext'` on `Int` casts — watch the `Polynomial.ringHom_ext'`
instance. (iii) the 134 proof's `Ξ` is at `jqN (ℓ*M)`; the pin's `hΞC`/`hΞX` are the two
computation lemmas. (iv) the 62 row's `swapInner`/`coeff_coeff_swapBivar` are the pin's
`swapBivar` bookkeeping; `natDegree_coeff_le'` is the real content and `solution` a one-liner.
(v) no `set_option maxHeartbeats` — the pin carries none in these three files.

## 5. Gates

As the recipe §6 and the SET-MC7 §6 practice, per order: `check_port --force` on the **whole
edited module** with `0 mismatch / 0 missing` (the module's existing rows must stay `ok` — an
insertion is a test of the wire it already has), axioms clean on every headline, the module's own
silent build under `flock`/`timeout`, `dedup.py` on the module, zero warnings, and **no linter or
heartbeat option** in the file (SET-MC7's FR-0054: the three suppressions a worker reaches for are
all fixable). Each insertion adds its `Thm_` wrapper and `S_` copy to the module's wire — and
nothing else.

## 6. After the landing

Re-read the shelf (recipe §7) and record: what the set consumed (expected 3 rows / 706 silo),
the new `needed`, and which rows became ready because of it — the 62 row's ten project consumers
are the candidates, so a readiness change is plausible here in a way it was not for M1. Update
[TOPIC-ready-shelf.md](TOPIC-ready-shelf.md) §1's MC-1 line and the three workorders' statuses.

**Measured after the wave (2026-10-27, one read over MC-1 + MC-2 + MC-3).**
Instrument `needed` 1,016 / 402,071 → **1,004 / 398,972**; corrected 1,018 / 402,432 →
**1,006 / 399,333**. Ready 83 / 17,475 → **75 / 15,689**; `ModularCurve` shelf 23 / 5,949 →
**15 / 4,163** (corrected 22 / 5,913 → 14 / 4,127); MC demand 182 / 79,025 → **170 / 75,926**;
frontier +16 nodes / +3,637 lines (the ten cut headlines plus six further pin declarations the
wave made ported — MC-2b's four `tatePowerSeries` nodes among them); leaves 296 / 72,205 →
**294 / 71,671**, because **two rows became ready out of the leaves block**:
`c4_mul_toricPoint_fst_div_c6_mem_qExpFunctionFieldC_gamma1` and
`meromorphicOrderAt_E4_cube_div_discriminant_sub_eq_card_stabilizer_div_two` — the readiness delta
this wave produced, and M3's next cut.  Ten rows were cut, nothing was lost, and the only tree
defect found was pre-existing (FR-0055).

## 7. What this set does not do

- **M2's siblings.** The shelf's M2 is the *whole* story; the pin also carries the
  `fibrePoly`/`Φ` rows at composite levels, which are not on today's shelf.
- **The ported transcendental node's own surface.** `ModularPolynomialVelu.lean`'s existing
  `private` helpers stay private; the set adds the descent, it does not promote the module.
- **No new module, no migration, no promotion.** Two insertions, two wires, two orders.
