# Two uniformizations of one Jacobian — the port structure of the complex-analytic Jacobian layer

Scoping note, 2026-10-25. Born of a D-S reading of the `TateModule` pair, whose numerical premise
the D-S prune avoids: the subject is **two independent developments**, each a wide body of complex
analysis with a narrow mouth, and each producing the *same* mathematical object — the uniformization
of `Pic⁰` — for a different class of curves. A one-day narrowing of the prune that would have priced
the whole subject for the D-S column was reverted
([deligneSerre/PRUNABLE-complex-analytic.md](deligneSerre/PRUNABLE-complex-analytic.md) §7): the
subject is treated **in its own right** from here, and this note is its port structure. The finding
that the D-S column has a second, modular supply for the same torsion finiteness is what keeps the
two separate.

## 0. Status and measurements

All figures below are the pin's (`aa2d8b3`), measured with `frontier.py`/`fltdata` citers and the
prunable payout (`ds_prunable.prunable`): **210 nodes / 116,825 lines** are reachable only through
the prunable set, of which **197 nodes / 106,462 lines** are unported. The nine `RadialRegion` nodes
are already ported (17 modules, 9,934 lines — [algebraicCurve/TOPIC-cell-dissection.md](algebraicCurve/TOPIC-cell-dissection.md)).
The whole subject is the RR column's phase 3 and the general-curve/Drinfeld supply; the **B** half
is off the D-S critical path, while the **A** half doubles as the D-S column's modular supply for
the same torsion facts (`finite_torsion_jOne`, the Tate module ≅ period lattice ⊗ ℤ_[p]) — which is
why the two halves are kept apart in the port structure, and why the prune's switch can assume A.
The subject itself is treated in its own right below: its own roadmap, its own gates, its own
consumers.

| group | unported nodes / raw lines | content ≈ |
|---|---:|---:|
| **A** modular period / multiplier / parabolic-hom family (`ModularCurve.*`: `ComplexPlaceDictionary{,Of}`, `period{,Of,Along,AlongOf}`, `isParabolicHom`, `realize`/`smoothedFundamental`, the `UpperHalfPlane` residue/slash lemmas) | 107 / 52,374 | ≈ 40,000 |
| A support (`ModularForm.*`, `CohCarrier.*`, `PeriodPair.*`, `FLT.Gamma0FundamentalSet`, `Matrix`/`ZMod` leaves) | 20 / 4,853 | ≈ 3,400 |
| **B1** cell dissection and radial regions (`CellDissection.*`, `exists_cellDissection`, `exists_dissectionScaleData`, `exists_pairedCellFamily` 4,730) | 13 / 19,946 | ≈ 14,000 |
| **B2** Abel–Jacobi divisor/vector and path periods (`abelJacobiDiv`/`abelJacobiVec`, `pathPeriodLattice`, the path-integral lemmas) | 19 / 13,866 | ≈ 9,700 |
| **B0** complex prelude (`Complex.*` circle-integral/dbar/residue, `exists_chartedSpace_*`, `isPrimitiveAlong`, `exists_sheet_decomposition`) | 17 / 5,979 | ≈ 4,200 |
| B0 Place/Divisor support (`Place.*_complex`, `Divisor.*`, `genus_ratFunc_eq_zero`) | 12 / 4,314 | ≈ 3,000 |
| other (leaf utilities cited from within the payout) | 9 / 5,130 | ≈ 3,600 |

A and B touch each other only through the shared prelude (B0 and the modular-form vocabulary):
their interfaces are disjoint.

## 1. The two uniformizations

**B — the Riemann-surface route.** Dissect a compact Riemann surface into radial cells
(`CellDissection`), integrate meromorphic differentials over the resulting loops
(`pathIntegral`/residue identities), record the periods in `pathPeriodLattice`, and conclude the
Abel–Jacobi theorem: there is a free `ℤ`-lattice `L` of rank `2g` in `Fin g → ℂ` with
`Pic0 ℂ F ≃+ (Fin g → ℂ) ⧸ L`. That statement is
`AlgebraicCurve.Pic0.exists_addEquiv_quotient_submodule_complex` — **33 pin lines, two premises
(`…_of_chartedSpace_complex` 159, `Place.exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex`
482), and exactly one direct citer**.

**A — the modular route.** For `Γ ∈ {Γ₀(N), Γ_H}`, build the *same* uniformization out of periods
of cusp forms over a fundamental set: `periodAlongOf` integrates a cusp form along a geodesic in
the fundamental domain, `periodLatticeOf` collects them (`Def_ModularCurve_PeriodOf.lean:65`),
`isParabolicHom` is the resulting period functional, `ComplexPlaceDictionary{,Of}` carries the
curve-theoretic dictionary, and the assembly
`ModularCurve.exists_bijective_heckeEquivariant_addMonoidHom_pic0_complex_xH_quotient_periodLatticeOf`
(15 premises, 2 citers) states `Pic0(ℂ) ≃ … ⧸ periodLatticeOf`, Hecke-equivariantly. Its usable top
is `…exists_injective_…_jH_quotient_periodLatticeOf` (302 lines, 5 premises), which feeds
`ModularCurve.exists_heckeEquivariant_linearEquiv_tateModule_jH_padicInt_tensor_periodLatticeOf`, the
Tate module ≅ period lattice ⊗ ℤ_[p] identification, `ModularCurve.finite_torsion_jOne`
(`Finite (Pic0.torsion … n)`, 80 lines, all premises in A), and a rational-Hecke independence lemma.

So A is not a variant of B: it is the **modular** uniformization, and it is the route the D-S
column actually takes at its Tate-module step. B is the general-curve uniformization, and its
consumers are the arithmetic cardinality `abelJacobiCard_genus` (fan-in 12) and, outside D-S, the
Drinfeld-curve cardinality `DrinfeldCurve.abelJacobiCard_drinfeldFunctionField` (288 lines, 3
citers). The two supplies meet only at the arithmetic facts they both prove.

## 2. The graph shape that this implies

Both halves are **wide bodies with narrow mouths**:

```
A: 52k lines ─► …_jH_quotient_periodLatticeOf (302) ─► TateModule ⊗ periodLatticeOf, finite_torsion_*
B: 44k lines ─► exists_addEquiv_quotient_submodule_complex (33, fan-in 1)
                        └─► natCard_torsion_prime_eq_pow_genus_complex (61)
                              └─► natCard_torsion_prime_eq_pow_genus (45)
                                    └─► abelJacobiCard_genus (113, fan-in 12) ─► the Tate-module trio, the pairings, cardinalityAJ
```

A port can therefore *enter* either half at its mouth, and the mouth is a single statement. Two
structural consequences:

1. **Either half can be ported for its own sake without a consumer existing.** The contract is one
   statement per half, so the work is well-bounded even though the bodies are 40k+ lines.
2. **The same arithmetic conclusion has two proofs.** `Finite (Pic0.torsion …)` for the modular
   curve is `finite_torsion_jOne` on A; `Module.Finite ∧ Module.Free (TateModule p (JH M H))` is
   `moduleFinite_and_free_padicInt_tateModule_jH` on B. The D-S column's pinned chain cites both, so
   `frontier --ds` (which prunes B) is a **rewiring assumption**, not a fact about the target: it
   prices the route that uses A. That is now recorded where the switch lives.

## 3. Four port structures, and what each buys

| | scope | content lines | dispatches (≈1.5k) | buys | leaves |
|---|---|---:|---:|---|---|
| **P1** A-only | A + A support + the `Complex`/`Place` leaves A uses | ≈ 40,000 | ≈ 28 | the period lattice of the modular Jacobians, the Tate-module⊗lattice identification, `finite_torsion_*`, the rational-Hecke independence | B (44k): the general uniformization, `abelJacobiCard_genus`, the Drinfeld consumer |
| **P2** full programme | A + B | ≈ 74,000 | ≈ 50 | both uniformizations; every arithmetic consumer | nothing |
| **P3** B-first | B only | ≈ 31,000 | ≈ 21 | the Abel–Jacobi theorem for general curves, `abelJacobiCard_genus`, Drinfeld | A: the modular period lattice and the Tate identification |
| **P4** conditional spine | the two mouths as named hypotheses | ≈ 400 | 1 | the arithmetic layer *now*: state `AbelJacobiUniformization` and `ModularPeriodLattice` as structures, prove the hub and the Tate-module pair conditionally from them | the two proofs; a frozen spine to retire when P1/P3 lands |

P4 is the playbook's conditional-capstone device (§2.3): a proved artifact, no `sorryAx`, its
premises a structure of named hypotheses, so the remaining work becomes an ordered list. Here it is
unusually cheap because each half's *only* outbound content is one statement, and unusually
valuable because the arithmetic hub (`abelJacobiCard_genus`, 12 consumers) and the Tate-module
trio sit on the other side of it.

**Recommendation, given that the subject stands on its own.** Its own roadmap is **P1 then B**
(P2 in full): A is the smaller body and it is the route that turns the modular Jacobian into an
explicit torus — the period lattice of `Γ_H`, the Hecke-equivariant uniformization, the Tate module
identified with the lattice; B is the general Riemann-surface route, which is where the Abel–Jacobi
theorem proper lives, with `abelJacobiCard_genus` (fan-in 12) and the Drinfeld consumer as its
arithmetic output. P3 alone is the choice only if the general-curve/Drinfeld mathematics is the
goal and the modular case is not.

**P4 is a separate, optional device**, and only worth doing if the arithmetic layer wants to move
before this subject lands: a day's work that freezes the two mouths as a structure of hypotheses
(the statements taken verbatim from
`Theorems/Thm_AlgebraicCurve_Pic0_exists_addEquiv_quotient_submodule_complex.lean`, and for A from
the pin's `PeriodOf` definition layer plus the `…_jH_quotient_periodLatticeOf` wrapper) and derives
`natCard_torsion_* → abelJacobiCard_genus →` the Tate-module trio conditionally, axiom-free. It is
not on this subject's path; it is the interface contract made executable.

## 4. Module layout

```
AlgebraicCurve/
  AbelJacobi/            -- B2: the Abel-Jacobi divisor/vector, path periods, the period lattice
    Basic.lean           --   defs: AbelJacobiDiv/Vec, pathPeriodLattice, the correspondence
    Periods.lean         --   the path-integral period lemmas and the lattice's discreteness
    Uniformization.lean  --   the mouth (Pic0 ≃ ℂ^g ⧸ L) and its two premises
  CellDissection/        -- B1: the existing phase-3 plan (RadialRegion landed under Reserve/)
  Analysis/Complex/      -- B0: circleIntegral/dbar/residue supplements to mathlib
                         --   (beside the existing Analysis/Complex/LogBranchAndPrimitiveRoot.lean)
ModularCurve/
  Period/                -- A: periodAlongOf, periodLatticeOf, isParabolicHom, the multiplier lemmas
    Basic.lean           --   the definitions (pin Def_ModularCurve_PeriodOf.lean)
    PlaceDictionary.lean --   ComplexPlaceDictionary{,Of}
    Assembly.lean        --   the Hecke-equivariant Pic0 ≃ … ⧸ periodLatticeOf  (A's mouth)
AlgebraicCurve/AbelJacobi/Spine.lean   -- P4: the two mouth statements as hypotheses + the arithmetic chain
```

Homing notes: B0's `Complex.*` lemmas (`circleIntegral` residue formula, `dbar` identities) are
mathlib-adjacent general analysis and belong in `Complex/` as supplements, not inside
`AlgebraicCurve/`; the period lattice is a *definition* of the modular curve's Jacobian and belongs
with `Period/`; the landed `RadialRegion` modules stay where they are under `Reserve/`
([algebraicCurve/TOPIC-cell-dissection.md](algebraicCurve/TOPIC-cell-dissection.md)).

## 5. Route and mathlib (audit, with the recorded negatives)

* **Mathlib has**: `circleIntegral` and the Cauchy/residue circle-integral API
  (`Mathlib/Analysis/Complex/CauchyIntegral.lean`), `MeromorphicOn`/`meromorphicOrderAt`,
  `ChartedSpace`/`IsManifold`, `AddCircle`, `Complex.exp`/`log`, `Submodule.torsionBy`,
  `Module.finrank`.
* **Mathlib does not have** (searched, recorded): an analytic Jacobian or `Pic⁰` uniformization, a
  `ComplexTorus`/period-lattice construction, the Abel–Jacobi map, `dbar`/Stokes on a Riemann
  surface, or a cell decomposition of a surface. Both halves are therefore built, not adopted.
* The pin's route is the cheap one *for the pin's own development*: B builds a **combinatorial**
  cell dissection and reduces the analysis to one-dimensional integrals along arcs (the
  `CellDissection` cluster is 12.8k lines for exactly this reason). A needs **no cell
  dissection at all**: its integrals are one-dimensional, along geodesics and a fundamental set in
  the upper half plane, and its surface theory is just the place dictionary
  (`ComplexPlaceDictionary{,Of}`). That is why A is the smaller of the two bodies for the
  uniformization it proves, and why P1 is recommended over P3 for a D-S-adjacent port — but note
  that A does need the dictionary of complex places, which is 12.6k of its 52k lines.
* The pin's files carry long `attribute [-instance]` walls (charted-space instances) in every `S_`
  file of this subject; the port drops them and must not add them back — they are the place the
  build will misbehave if it does.

## 6. Risks

1. **Charted-space instance walls.** Both halves instantiate `MeasurableSpace`/`BorelSpace`/
   `ChartedSpace` on function spaces; the pin's `attribute [-instance]` lists are proof-engineering,
   and a port that keeps them will be unmaintainable, while one that drops them may face
   unification blow-ups. Expect the low heartbeat cap to find these; that is its job (§3.5 of the
   playbook).
2. **`exists_pairedCellFamily` is a 4,730-line silo** with one consumer chain of its own; port B1
   only behind it, never as a standalone sweep.
3. **`exists_bijective_heckeEquivariant_addMonoidHom_pic0_complex_xH_quotient_periodLatticeOf` has
   15 premises** — A's mouth is narrow but *wide-based*, so the visible interface is not the
   dispatch count.
4. **The arithmetic hub is fan-in 12**, and it is part of this subject (the algebraic packaging of
   the analytic route). The D-S prune keeps it, with the subject it packages; that is deliberate, and
   a D-S read that shows the pair as one node relies on the modular supply, not on an omission.

## 7. Verification

Each module carries its own `spec-pin:` wire to the pin's `S_` file (or the `Theorems/` wrapper where
the node's statement is the wrapper's), `check_port` at `0 mismatch / 0 missing`; the consumer
zones in `spec/` gain one zone per mouth (B: `Pic0 ≃ ℂ^g/L` at a concrete curve; A: the period
lattice of `Γ_H` and `finite_torsion_jOne`); `#print axioms` clean on both mouths and on the spine's
conditional assembly; a coverage report for the payout (`0 / 0 / 0` on the ported subset).

## 8. First moves

1. **P1 set 1.** `ModularCurve/Period/Basic.lean` from `Def_ModularCurve_PeriodOf.lean` (the
   definitions and `periodOf_mem_periodLatticeOf`); then `PlaceDictionary`, then `Assembly`.
2. **B's definition layer** (`AlgebraicCurve/AbelJacobi/Basic.lean`) when its turn comes — but do
   not open `CellDissection/` before `exists_pairedCellFamily`'s own chain is scheduled; it is a
   4,730-line silo with a single consumer.
3. Re-price **P2** after P1's first set with the measured written ÷ content ratio; take the B half
   when the general uniformization is wanted for its own sake — it is, and it is self-contained
   enough to be a project of its own.
4. **P4 only on request** from the arithmetic side, as the interface contract, not as a shortcut
   for this subject.

## 9. Links

* the prune, its narrowing and the residual: [deligneSerre/PRUNABLE-complex-analytic.md](deligneSerre/PRUNABLE-complex-analytic.md) §7
* the cell-dissection / radial-region plan: [algebraicCurve/TOPIC-cell-dissection.md](algebraicCurve/TOPIC-cell-dissection.md)
* the pair that surfaced this: [modularCurve/TOPIC-padic-tate-module.md](modularCurve/TOPIC-padic-tate-module.md)
* the RR column: [PORTING-RR.md](PORTING-RR.md); the scout: [../studies/deligne-serre-weight-one-scout.md](../studies/deligne-serre-weight-one-scout.md) §4.2
