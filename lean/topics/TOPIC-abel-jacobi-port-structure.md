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
their interfaces are disjoint. Measured on the two mouths' closures, that prelude is **19 unported
nodes / 1,118 lines**, of which the whole analytic part is the 311-line circle-integral residue pair;
§9 is the audit of the question the reader will ask next — whether B could carry A anyway.

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

**The conclusions are not the same theorem, and generality is not comparable.**

B says: `∃ L : Submodule ℤ (Fin g → ℂ), Module.Free ℤ L ∧ Module.Finite ℤ L ∧
Module.finrank ℤ L = 2 * g ∧ Nonempty (Pic0 ℂ F ≃+ (Fin g → ℂ) ⧸ L)` — an *abstract* lattice in a
coordinate space and a plain additive isomorphism. It names no cusp form, no Hecke operator, no Tate
module, and its hypothesis (`∃ x, Transcendental …`) admits any curve over an algebraically closed
characteristic-zero field.

A says, at its usable top:
`∃ u : JH M H →+ Module.Dual ℂ (CuspForm (GammaH M H) 2) ⧸ periodLatticeOf (GammaH M H)`,
injective, containing all torsion (`∀ y, IsOfFinAddOrder y → y ∈ u.range`), and **equivariant** for
`heckeTLinH`, `heckeULinH` and `diamondLinH` (the Hecke-T, Hecke-U and diamond operators acting on
the dual of cusp forms); and above it
`∃ e : TateModule p (JH M H) ≃ₗ[ℤ_[p]] ℤ_[p] ⊗[ℤ] periodLatticeOf (CohCarrier.GammaH M H)` with the
Hecke/diamond action transported through it (`χ' (e x) = χ (e (tateGenOpH … x))`).

So B is more general **in the curve** and far weaker **in the conclusion**: A identifies the lattice
with the periods of cusp forms, carries the Hecke action across, and identifies the Tate module with
that lattice. To get A's *statement* from B one would need three comparisons that exist nowhere in
the pin — (i) B's `L` equals `periodLatticeOf` (the periods of the Abel–Jacobi map are the integrals
of the holomorphic differentials, i.e. the cusp forms), (ii) the Hecke action on `periodLatticeOf`
(H¹ of the curve = cusp forms, Hecke-equivariantly), (iii) `TateModule ≅ periodLatticeOf ⊗ ℤ_[p]`.
A develops exactly those three as its content; B develops none of them. That is why the two are
separate projects rather than one project with a special case.

**A is heavily consumed, and not by this subject.** The Tate-module identification has five citers,
all of them weight: `CuspForm.exists_padicGaloisModule_heckeRingH_two_frobenius_relation` (859
lines — the p-adic Galois module the D-S construction is built on),
`ModularCurve.exists_heckeEquivariant_parabolicHoms_to_dual_tateModule_jH`,
`…exists_map_eq_charpoly_heckeTLinOne_and_charpoly_tateHeckeRepOne_jOne_eq_map_sq` (the
characteristic-polynomial comparison between Hecke on cusp forms and Hecke on the Tate module),
`…exists_monic_aeval_tateGenOpH_T_eq_zero_forall_norm_root_lt`, and
`…exists_ringHom_moduleEnd_twoCuspForms_apply_eq_twoCuspGenMod`. A is the Eichler–Shimura bridge of
the Galois-representation development. B's consumers are the arithmetic cardinality hub
`abelJacobiCard_genus` (fan-in 12) and, outside the D-S column,
`DrinfeldCurve.abelJacobiCard_drinfeldFunctionField` (288 lines, 3 citers). The two meet only in the
arithmetic facts they both prove — which is exactly the overlap that lets a D-S read price the
column's torsion finiteness without B.

**Weights, for scheduling.** A is the bigger body and B the more intrinsic theorem, and that
asymmetry is what makes the two projects feel different in kind:

| | A (modular / Eichler–Shimura) | B (Abel–Jacobi for any curve) |
|---|---:|---:|
| nodes / lines in the Fermat cone | 145 / 61,519 | 44,000 lines unported (cell 19,946 + divisor/vector 13,866 + prelude ~10,300) |
| unported | 57,000 (52,374 + 4,853 support) | 44,000 |
| D-S dependency | yes — 15 nodes / 5,301 visible, and **86 nodes / 41,714 hidden** behind the 19 pruned `abelJacobi_mem_periodLattice*` lemmas | none: 0 of its nodes are needed by the column; its only touch point is the pair's proof, which A replaces |
| its own consumers | the p-adic Galois module (859 l), the char-poly comparison, parabolic-homs duality, the Igusa chain | `abelJacobiCard_genus` (fan-in 12), the Drinfeld curve |

So B is scheduled on its own merits with no D-S timing dependency at all, while A is a real
dependency whose true price is its whole 61.5k family, not the 5.3k the pruned column shows. That
asymmetry is a property of the two *conclusions*, not of the two *bodies*: §10 finds the shared
complex analysis formalized twice, at 2.3k lines in A and 10.1k in B, and it is B that is carrying
the avoidable weight.

**And the two closures are disjoint where it matters.** Taking premise closures on the pin's graph:
`exists_heckeEquivariant_linearEquiv_tateModule_jH_padicInt_tensor_periodLatticeOf` (528 nodes),
`exists_injective_heckeEquivariant_addMonoidHom_jH_quotient_periodLatticeOf` (521) and
`finite_torsion_jOne` (528) each contain **neither** B's mouth **nor** `abelJacobiCard_genus`. So B is
not an ingredient of A: A is an independent proof, not a consumer of the abstract theory.

That settles what the D-S column needs. Both routes are in its closure, and the pinned chain cites
both — but the *needs* are met by A alone:

* finiteness/freeness of `TateModule p (JH M H)`: A gives it by transferring it across
  `TateModule ≅ ℤ_[p] ⊗ periodLatticeOf` from the lattice's own finite-free-rank-`2g` facts (`…is a
  ℤ-lattice of rank 2g`, the `periodLatticeOf_gammaH_heckeDiamondStable`/basis family), and
  numerically through `finite_torsion_jOne`; B gives the same fact only as the arithmetic
  cardinality behind the pair;
* the Hecke-equivariant identification and the char-poly comparison: **only A** gives those.

So **B is not needed for D-S** — it is needed for its own consumers (the general uniformization, the
arithmetic hub's fan-out at fan-in 12, the Drinfeld curve). A faithful port of the pinned chain still
meets the pair's proof citing B's hub; taking A instead means deriving one node (the pair) from the
period-lattice identification rather than from the Abel–Jacobi cardinality, a recorded rewiring, and
the `--ds` prune already prices the column that way. What the prune does *not* justify is cutting A's
own Abel–Jacobi dictionary lemmas (three of them, PRUNABLE §7): those are A's, and A is the route
D-S needs.

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
2. **The same arithmetic conclusion has two proofs, and the prune currently cuts both.** `Finite
   (Pic0.torsion …)` for the modular curve is `finite_torsion_jOne` on A;
   `Module.Finite ∧ Module.Free (TateModule p (JH M H))` is
   `moduleFinite_and_free_padicInt_tateModule_jH`, whose proof reaches B. Inside the D-S cone
   `frontier --ds` removes 44 nodes / 30,570 lines, and they decompose as **29 nodes / 24,391 lines of
   B** (`exists_int_pathIntegral_eq_sum_periods_add_sum_residues` 3,374,
   `exists_loops_pathIntegral_reciprocity_raw` 2,388, the cotree/Kirchhoff quartet),
   **9 nodes / 3,228 lines of A's own Abel theorem and its witnesses**
   (`abelJacobi_mem_periodLatticeOf_gammaH_of_isPrincipal` 313, `isPrincipal_…` 133,
   `exists_meromorphic_…` 117, `exists_cuspForm_mul_exp_periodOf_eq_one_…` 495,
   `exists_norm_multiplier_eq_one_and_abelJacobi_add_petersson_…` 548,
   `exists_mapDomain_eq_heckeDivHBar_abelJacobi_sub_mem_periodLatticeOf` 684, and three multiplier
   lemmas), and **6 nodes / 2,951 lines of the hub and the `abelJacobiDiv` correspondence**
   (`abelJacobiCard_genus` 113, `natCard_torsion_prime_eq_pow_genus_complex` 61, three
   `abelJacobiDiv_correspondence_*` / `exists_ball_*`, 2,454). So `--ds` is not "A instead of B": the
   `abelJacobi` pattern cannot tell the two Abel theorems apart. What the scoping establishes is
   stronger: the column's needs (torsion finiteness, the Hecke-equivariant identification, the Tate
   module ≅ lattice ⊗ ℤ_[p]) are met by A *as a whole*, and **520 of A's 529 nodes are untouched by the
   prune** — what survives of A is the dictionary, the period lattice and the Tate identification, i.e.
   exactly the part the column needs. So the route to price is A complete, and the defect is in the
   pattern set rather than in the reading: `abelJacobi` has to be split into the analytic spellings the
   prune means and the algebraic cardinality it does not, otherwise A's Abel theorem keeps being cut.
   PRUNABLE §7 records the same cut on a wider count (19 dictionary lemmas / 5,981 lines over the
   subject's own cone, 86 nodes / 41,714 lines behind them); the 9 / 3,228 above is the slice of it
   that lies inside the D-S cone itself.

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
(P2 in full): A has the cheaper analysis (2.6k against 10.1k, §10) and is the route that turns the
modular Jacobian into an explicit torus — the period lattice of `Γ_H`, the Hecke-equivariant uniformization, the Tate module
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
  `CellDissection` cluster is 12.8k lines for exactly this reason). A needs **no cell dissection**:
  its integrals are one-dimensional, along geodesics and a fundamental set in the upper half plane,
  and the surface theory of its curve is the place dictionary (`ComplexPlaceDictionary{,Of}`, 12.6k
  of its 52k lines). A's *analysis* is the smaller of the two for the uniformization it proves
  (2.6k against B's 10.1k, §10), although its *body* is the larger — 57k unported against B's 44k —
  and it is on the D-S critical path; that is why P1 is recommended over P3 for a D-S-adjacent port.
  **A is not analysis-free, though**: its
  closure carries 9 `Complex.*` nodes / 2,624 lines, **2,313 of them A's own** Stokes/`dbar` theory on
  the modular fundamental domain — `integral_modularFundamentalDomain_eq_boundary_of_hasFDerivAt` 639,
  `integral_logDeriv_wedge_add_finsum_eq_integral_dbarLogDeriv` 643,
  `integral_inv_sub_mul_dbar_eq_neg_pi_mul` 463,
  `integral_mul_dbar_eq_neg_pi_mul_finsum_residue` 306,
  `integral_mul_logDeriv_mul_dbar_eq_neg_pi_mul_finsum` 98,
  `integral_mul_dbar_eq_zero_of_differentiableOn` 90, `locallyIntegrableOn_of_simplePoles` 74 —
  consumed by the Petersson/side-pairing and the winding-pairing lemmas. It dissects no surface, but
  it does integrate a `dbar` over a domain with a boundary: the same *kind* of work as B0, in a
  different setting. **The one genuine cross-route factoring in the whole subject is therefore a
  shared "Stokes on a bounded domain" API**, of which A's `dbar` family and B0's circle-integral
  family are two hand-rolled copies (2,313 + 2,080 unported lines).
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

## 9. Could B carry A? — the 2026-10-26 audit

Asked directly, and answered from the two mouths' premise closures on the pin (`frontier.Frontier`,
the `union` frontier, 1,212 ported nodes). The answer is **no supplanting and no net
simplification**, but the reason is sharper than "different theorems" and it locates one real
opening, so it is recorded here rather than left as an impression.

### 9.1 A's needs, against B's supply

Enumerated from the two nodes the D-S column and the Tate chain rest on
(`…exists_injective_…_jH_quotient_periodLatticeOf` 302,
`…exists_heckeEquivariant_linearEquiv_tateModule_jH_padicInt_tensor_periodLatticeOf` 653) plus
`finite_torsion_jOne` 80:

| what A needs | what the pin's B side has | verdict |
|---|---|---|
| freeness + finiteness of `periodLatticeOf` (the 267-line basis theorem) | discreteness of *its own* lattice, `discreteTopology_pathPeriodLattice_and_span_eq_top` 106 | two lattices in two ambient spaces; no transfer |
| `Module.finrank ℤ (periodLattice N) = 2 * genusFF` | `Module.finrank ℤ L = 2 * genus` in B's mouth | **not from B**: A's rank is counted against the algebraic `p^(2g)` (§9.2) |
| injectivity of the uniformization | only after B is re-stated (§9.3) | the pin states it existentially |
| "every torsion class is an Abel–Jacobi value" | needs `L = periodLatticeOf`, not just `⊆` | no: a proper inclusion leaves a finite kernel the comparison cannot see into (§9.3) |
| Hecke-T/U/diamond stability of the lattice, and the period map's Hecke compatibility (464 + 591 + 357 + 158) | nothing — no Hecke action on any lattice anywhere in B | no |
| `TateModule p (JH M H) ≃ ℤ_[p] ⊗ periodLatticeOf`, Hecke-equivariantly | `Module.Finite ∧ Module.Free (TateModule …)` 327, obtained *through* the cardinality | finiteness only; no identification, no Hecke |
| the H/Γ dictionary (`ComplexPlaceDictionary{,Of}`), 45 nodes / 16,867 lines | `Place.exists_chartedSpace_…_complex` 482 + `connectedSpace_of_chartedSpace_…` 369 | no: A's dictionary is the explicit `realize`/`pt`/ramification/Hecke-correspondence content; the abstract charted space gives none of it, and A's closure does not contain either node |

### 9.2 The measured interface

Closures: A's two top nodes, 529 nodes / 216,100 lines (189 unported / 63,186); B's mouth, 212 /
129,246 (91 unported / 47,861); B's hub, 298 / 163,214 (149 unported / 66,381). Their intersection is
**113 nodes but only 19 unported / 1,118 lines**, and none of it is B's subject — it is the
`Place`/`Divisor`/`RationalFunctionField` prelude both halves stand on, already ported in the large.
The analytic part of it is exactly two nodes, cited by A's
`ModularCurve.eventually_abelFibreSumOf_sub_mem_periodLatticeOf` and by B0:
`Complex.circleIntegral_eq_sum_residue_of_simplePole` (142) and
`Complex.hasDerivAt_circleIntegral_mul_deriv_div_sub` (169). So porting either half first donates
≈1.1k lines of prelude to the other, and that is the entire supply.

**A's rank fact is a coupling.** `ModularCurve.finrank_periodLattice_eq_two_mul_genusFF` (80) — the
Γ₀(N) rank fact — takes a premise from each side: A's
`natCard_torsion_jZero_eq_pow_finrank_periodLattice` (81, cardinality of the torus) and
`AlgebraicCurve.Pic0.natCard_torsion_prime_eq_pow_two_mul_genusFF_of_forall_pow_eq_self` (144, the
*algebraic* route through `…abelJacobiCard_genusFF_of_frobenius_of_isAlgebraic`, not B's analytic
one). It is the one node found whose proof takes a premise from each side, so as written it keeps both
the torus and the algebraic cardinality alive. A port need not keep it: §12.1 chain 1 is an RR route
to `dim S₂ = g`, and `2g` follows from the basis theorem — but that route has to be *written*, the pin
does not contain it. Until it is, A's rank is borrowed, which is why the D-S prune keeps the hub and
why P4's spine needs a rank premise it cannot get from A alone.

### 9.3 The one real opening, and why it still does not pay

B's mouth is 33 lines of existential packaging over a **parametric** theorem that B's own proof
establishes and then throws away. `S_AlgebraicCurve_Pic0_exists_addEquiv_quotient_submodule_of_chartedSpace_complex`
builds, for an arbitrary `b : Fin n → Ω[F⁄ℂ]` and base point `P₀` (no basis, no discreteness),

```
ajDegZero b P₀ : Divisor.degZero →+ (Fin n → ℂ) ⧸ pathPeriodLattice b
ajPic0     b P₀ : Pic0 ℂ F        →+ (Fin n → ℂ) ⧸ pathPeriodLattice b
ajPic0_injective, ajPic0_surjective          -- i.e. an AddEquiv, parametrically
```

from the three hypotheses B's Abel theorems supply (`habel`, `hconv` from
`Divisor.isPrincipal_of_abelJacobiDiv_mem_pathPeriodLattice`, `hjac` from
`exists_degree_eq_zero_and_abelJacobiDiv_sub_mem_pathPeriodLattice`). Only at the last line is it
instantiated at a genus-basis and existentially packaged. **A port that states the parametric form —
the natural strengthening, no new mathematics — is the only version of B that could ever serve a
second uniformization**, and it would give A the injectivity half of its mouth: `u = π ∘ φ` is
injective whenever `φ` is bijective and `ι(L_A) ⊆ L_B` makes `π` well defined. The needed comparison
is then only the loop-period **inclusion**, which is cheap in principle: each `periodOf γ` is the
integral around the loop the geodesic from `I` to `γ·I` closes up to.

What it does not give is the torsion-containment clause of A's mouth
(`∀ y, IsOfFinAddOrder y → y ∈ u.range`): with `ι(L_A) ⊆ L_B` proper, `ker π = L_B/ι(L_A)` is a
nonzero finite group inside which B's bijection sees nothing, so that clause needs
`L_A = L_B` — exactly comparison (i) of §1. And no restatement of B reaches (ii) Hecke or (iii) the
Tate module. So the parametric port buys one clause of one node, at the price of the cusp-forms ↔
`regularDifferentials` transport plus a reconciliation of the two integral *definitions*:
`periodAlongOf` is an explicit interval integral, `pathIntegral` is
`if ∃ g, IsPrimitiveAlong ω γ g then … else 0` — a choice-form definition that A cannot compute with
and would have to be proved primitive along every path it uses.

Statement-for-statement, A's Abel lemmas *are* the modular instances of B's —
`ComplexPlaceDictionaryOf.abelJacobi_mem_periodLatticeOf_gammaH_of_isPrincipal` (313) /
`…isPrincipal_of_abelJacobi_mem_periodLatticeOf_gammaH` (133) /
`…exists_meromorphic_meromorphicOrderAt_eq_of_abelJacobi_mem_periodLatticeOf_gammaH` (117) against
`abelJacobiDiv_mem_pathPeriodLattice_of_isPrincipal` (193) /
`Divisor.isPrincipal_of_abelJacobiDiv_mem_pathPeriodLattice` (193) /
`exists_regular_pathIntegral_sub_eq_of_abelJacobiDiv_mem_pathPeriodLattice` (677) — and
`abelFibreSumOf` is the same construction as `abelJacobiDiv`. But they live inside the 45-node,
16,867-line dictionary whose remaining content (the ramification `two_mul_ramification_eq_card_stabilizer`
pair, the Hecke divisor correspondence, the Galois/`ofAlgAut` point actions, the residue lemmas) has
no analogue in B, so the 563 lines B would replace do not come out of the 16.9k cleanly. Net: the
bridge costs about what it saves, and only a port committed to P2 has any reason to build it.

**What B is worth to A is a shared definition, not a second proof.** The modular torsion cardinality
would gain a second proof (`natCard_torsion_jZero_eq_pow_finrank_periodLattice` + rank against
`natCard_torsion_pic0_xHFunctionFieldBar_eq_pow_two_mul_genusFF`), and by §10.4 that is a cost, not a
check. What does pay is definitional: `periodAlongOf` and `pathIntegral` are two definitions of one
notion, §10.2 says which to keep, and the ordering follows from that — B comes after A because B's
*analytic layer* should be written on A's definition.

**Consequence.** §3's recommendation is unchanged — P1 then B, no restructuring of A around B, no
dependency either way — with one line added to any future B module plan: state
`AbelJacobi/Uniformization.lean`'s theorem parametrically in `b` and `P₀` *before* packaging it
existentially. That is free at porting time, and it is the only form of B that is reusable by
anything else.

### 9.4 The two Abel theorems, statement for statement

§9.3 said "A's Abel lemmas *are* the modular instances of B's". Reading the six statements off the pin
(`statement_db show`, pin `aa2d8b3`) qualifies that: the shape is identical, the objects in it are not.

Both halves state `principal ⟺ AJ ∈ L`, and both do it in the same three-statement arrangement — a
forward implication, a converse, and a third statement that is the *engine* of the converse and is
cited by nothing else (A's 117 is cited only by A's 133; B's 677 only by B's 193). Every object inside
is different:

| | A, at `Γ_H` / `xHFunctionField M H` with `D : ComplexPlaceDictionaryOf Γ_H _` | B, at an arbitrary curve `F / ℂ` |
|---|---|---|
| `L` | `periodLatticeOf Γ : Submodule ℤ (Module.Dual ℂ (CuspForm Γ 2))`, spanned by `periodOf γ = periodAlongOf Γ I (γ • I)` for `γ ∈ Γ` — **no basis, no `n`, no genus**; `CuspForm` is mathlib's | `pathPeriodLattice b : Submodule ℤ (Fin n → ℂ)`, spanned by `fun i => pathIntegral (b i) γ` over *all* loops at *all* base points; `b : Fin n → Ω[F⁄ℂ]` (a `Module.Basis` in the converse) |
| the summand | `periodAlongOf Γ τ₀ τ₁ f = ∫₀¹ f (segmentPath τ₀ τ₁ t) · (τ₁ − τ₀)` — an interval integral; evaluation is `rfl` | `pathIntegral ω γ = if ∃ g, IsPrimitiveAlong ω γ g then g 1 − g 0 else 0` — a choice over an existence |
| AJ | `∑_τ c τ • periodAlongOf Γ I τ`, a functional; `c : ℍ →₀ ℤ` is **upstairs** | `abelJacobiDiv b P₀ D = ∑_v (D v) • (fun i => pathIntegral (b i) (some path P₀ → v))`, coordinates; `D : Divisor ℂ F` is **downstairs** |
| forward (313 / 245) | `hc : IsPrincipal (Finsupp.mapDomain D.pt c)`, `hdeg`, `⊢ ∑_τ c τ • periodAlongOf Γ I τ ∈ periodLatticeOf Γ` | `hc : IsPrincipal D`, `⊢ abelJacobiDiv b P₀ D ∈ pathPeriodLattice b` — no degree hypothesis, no basis |
| converse (133 / 193) | `hdeg`, `hΛ`, `⊢ IsPrincipal (Finsupp.mapDomain D.pt c)` | `b` a basis, `hD0`, `hD`, `⊢ IsPrincipal D` |
| engine (117 / 677) | names the witness `F : ℍ → ℂ`: meromorphic, `F (γ • τ) = F τ`, bounded at every cusp, and `meromorphicOrderAt F τ = ramification τ * (mapDomain D.pt c) (D.pt τ)` — a *strengthening* of the converse, same hypotheses | constructs `ζ ∈ regularDifferentials` with `pathIntegral (η − ζ) γ = 2π i m` for every loop off the support of `D` — the third-kind-differential form, an *engine*, not a strengthening |

Four differences a bridge has to pay, in the order they bite:

1. **Ambient space.** A's `L` is a lattice of functionals on mathlib's `CuspForm Γ 2`; B's is a
   coordinate lattice in `Fin n → ℂ` against a chosen basis of the pin's `regularDifferentials`.
   This is comparison (i) of §1, and it is where A's basis-free statements (and its borrowed rank
   fact, §9.2) come from: A never needs `n`, so it never needs the genus.
2. **Upstairs versus downstairs divisor.** A quantifies over `c : ℍ →₀ ℤ` and pushes it down with
   `pt`; the orders it prescribes are the *pullback* orders `ramification τ * …`, so the statement is
   orbifold-weighted, and `hdeg` is a hypothesis on the pushed divisor in *both* directions. B
   quantifies over `Divisor ℂ F` and needs `degree = 0` only in the converse.
3. **The third statements are not the same theorem.** A's strengthens its converse with a modular
   function; B's is the device that proves its converse. Instantiating B's 677 at `X_H` therefore
   does not give A's 117 — it gives a third-kind differential, which is not what the Hecke
   dictionary consumes. §9.3's "modular instances" is true of the first two pairs, and there only up
   to (1) and (2).
4. **The weights run opposite ways, and for the same reason as §10.2.** A: 313 + 133 + 117 = 563, of
   which the expensive statement is the forward one — the winding-pairing computation that proves an
   explicit sum of `periodAlongOf`s is a ℤ-combination of loop periods. B: 245 + 193 + 677 = 1,115,
   of which the expensive statement is the engine. A's converse is 133 lines precisely because its
   summand is an honest integral and its `L` is generated by `periodOf γ`; B has to buy the same
   implication with 677 lines of third-kind bookkeeping. That is the statement-level shadow of
   §10.2, and it says the cheap side of the bridge is *B borrowing A's definition*, not the
   statements.

### 9.5 What deriving B's statements from A's would take

§9.4 makes the two Abel theorems look like one theorem in two vocabularies, which invites the
question the other way round from §9: can B's statements be *derived* from A's? Six things have to be
in place, and only the fourth and fifth are lattice-theoretic — the two that such a plan would name
first are neither first nor, in one case, needed at all:

1. **Scope: an obstruction, not a gate.** A's statements are about one curve family
   (`xHFunctionField M H` at `GammaH M H`), and the pin's `CuspForm` ↔ `regularDifferentials`
   transport is at `Gamma0 N`. B's are about an arbitrary curve over `ℂ` with a charted-space
   structure. So the derivation can deliver B *at* `X_H` only. B in general needs the uniformization
   of a compact Riemann surface by a Fuchsian group, in neither the pin nor mathlib (§5).
2. **The differential identification.** A's lattice lives in `Dual ℂ (CuspForm Γ 2)`, B's in
   `Fin n → ℂ` against a `Module.Basis` of `regularDifferentials`; "the lattices are equal" is not
   even a statement until these spaces are identified. The pin has
   `exists_linearEquiv_tensor_regularDifferentialsBar_cuspForm` (323),
   `ℂ ⊗[AlgebraicClosure ℚ] regularDifferentialsBar N ≃ₗ[ℂ] CuspForm (Gamma0 N) 2` — at `Γ₀(N)`,
   through the arithmetic model, not for `Γ_H`.
3. **The integral identification — the gate with no node in the pin.** A's summand is an honest
   interval integral `∫₀¹ f (segmentPath I (γ • I) t) · (γ • I − I)` anchored at `I`; B's is a
   primitive difference along the *image* loop at `pt I` (closed by the dictionary's `pt_smul`); B also
   anchors at an arbitrary `P₀`, which is only bookkeeping once the base point is set to `pt I`.
   Agreeing the two is exactly the "honest integral" redesign §10.2 prices at ≈1–1.5k, and it is
   needed for *both* inclusions — so it is prior to lattice equality, not a corollary of it.
4. **A ⊆ B is then free**: `pt_smul` closes the geodesic and the two identifications transport the
   integral. This is §9.3's "only the loop-period inclusion", and it is as cheap as §9.3 says.
5. **B ⊆ A is where genus enters, and its content is spanning, not the number.** Every loop's period
   must be a `ℤ`-combination of the `2g` periods `periodOf γᵢ`: A's row-2 machinery (810 + 1,052 +
   596 + 874 + 693 ≈ 4,025, §10.1) plus the 267-line basis theorem. The *number*
   `finrank ℤ periodLatticeOf = 2 * genusFF` is a separate 80-line node and the pin's only
   two-route count (§9.2), so a derivation that also wants B's rank conclusion is where circularity
   would enter.
6. **None of the six Abel statements needs a rank.** B's converse quantifies over any
   `b : Module.Basis (Fin n) ℂ regularDifferentials`, so the instantiation `n = g` is discharged by
   the ported `finite_and_finrank_regularDifferentials_eq_genus` (220). Rank is wanted only for B's
   *mouth*, which asserts `finrank ℤ L = 2 * g`. Divisor transport is the one cheap item: `hdeg`
   follows from `degree D = 0` because places over an algebraically closed field have degree one
   (`Place.deg_eq_one_of_isAlgClosed`, 13, ported).

**Verdict.** Lattice equivalence: yes, but it splits into a free half and a ≈4k half, and both
presuppose an integral reconciliation the pin does not have. Genus → rank: only for B's mouth, not for
Abel's theorem, and its numeric form is the one borrowed node. So the derivation is a *deletion*
artefact at best — it would let the port keep one period lattice instead of two at `Γ₀(N)` — and not a
port strategy: it costs more than the 563 lines of A it would explain, and it says nothing at a curve
that is not a modular curve.

## 10. Where the duplication actually is — the 2026-10-26 second read

§9 asked the question in the wrong direction. "Can B supply A" is about *theorems*; the question
that decides whether two bodies are one body is where the same mathematics is formalized twice, and
on which side it is formalized better. Measured, it is formalized twice in exactly one place — the
complex analysis of periods and residues — and **A's formalization is four times cheaper**. So the
duplication is real, it is worth about 10k lines, and it is B that pays it.

### 10.1 The four lemmas both halves prove

Both routes need the same four statements about a compact Riemann surface, and both prove them from
scratch:

| the lemma | A's proof | B's proof |
|---|---|---|
| residue / Stokes on a domain: the integral of a meromorphic form over a domain with boundary is its periods plus its residues | `Complex.integral_mul_dbar_eq_neg_pi_mul_finsum_residue` 306 (simple poles) + `integral_mul_logDeriv_mul_dbar_eq_neg_pi_mul_finsum` 98 and `integral_logDeriv_wedge_add_finsum_eq_integral_dbarLogDeriv` 643 (arbitrary order, via `logDeriv`) + `integral_modularFundamentalDomain_eq_boundary_of_hasFDerivAt` 639 (the FD boundary) + 3 supporting lemmas (463 + 90 + 74). **7 nodes / 2,313 lines** | `CellDissection.exists_int_pathIntegral_eq_sum_periods_add_sum_residues` 3,374 + `two_pi_I_mul_sum_residue_mul_primitive_eq_sum_jump_mul_edgeInt` 1,209 + `exists_int_pathIntegral_sub_primitive_eq_sum_jump` 912 + `exists_primitives_jump_eq_zero_of_dualTree` 1,395 + `jump_kirchhoff_and_wordFormula_of_primitives` 1,314 + `kirchhoff_and_jump_formula_of_arc_values` 665 + `exists_loop_pathIntegral_eq_sum_cycle_mul_edgeInt` 1,240. **7 nodes / 10,109 lines** |
| every loop's period is a ℤ-combination of 2g base periods (H₁ side pairing / reciprocity) | `exists_mem_periodLatticeOf_eq_sum_intCast_mul_edgeIntegral_of_isParabolicHom` 810, `exists_isParabolicHom_sum_intCast_mul_edgeIntegral_eq_periodOf` 1,052, `sum_periodOf_mul_edgeIntegral_eq_zero` 596, `exists_mem_periodLatticeOf_tendsto_windingPairing_smoothedFundamental` 874, `integral_petersson_gammaFundamentalSet_eq_sum_conj_periodOf_mul_edgeIntegral` 693 ≈ 4,025 | `exists_loops_pathIntegral_reciprocity_raw` 2,388 + `exists_loop_pathIntegral_eq_sum_cycle_mul_edgeInt` 1,240 ≈ 3,628 |
| the Abel–Jacobi map is well defined modulo the lattice, and locally injective | `eventually_abelFibreSumOf_sub_mem_periodLatticeOf` 1,547 + the winding pairing | `exists_ball_abelJacobiDiv_*` / `exists_abelJacobiDiv_sub_mem_pathPeriodLattice_and_image_mem_nhds` |
| Abel's theorem: principal ⟺ AJ value in the lattice | `abelJacobi_mem_periodLattice*` (313/256) + `isPrincipal_of_abelJacobi_mem_periodLattice*` (133/103) + `exists_meromorphic_meromorphicOrderAt_eq_*` (117/114) plus the multiplier/cusp-form witness chain | `abelJacobiDiv_mem_pathPeriodLattice_of_isPrincipal` 193 + `Divisor.isPrincipal_of_abelJacobiDiv_mem_pathPeriodLattice` 193 + `exists_regular_pathIntegral_sub_eq_of_abelJacobiDiv_mem_pathPeriodLattice` 677 |

Rows 2–4 are a fair trade (A ≈ B, or B slightly cheaper); row 1 is not. A's row-1 lemma is also
*more general than B's*: `integral_mul_dbar_eq_neg_pi_mul_finsum_residue` is stated for an arbitrary
open `U ⊆ ℂ`, an arbitrary `C¹` compactly supported test function `h`, and any `F` locally equal to
`c a / (z - a) + analytic` — no curve, no place, no chart, no dissection. Its statement is

```
∫ z, F z * ((fderiv ℝ h z 1 + I * fderiv ℝ h z I) / 2) = -π * ∑ᶠ a, c a * h a
```

i.e. the ∂̄-Pompeiu identity, from which the domain-with-boundary residue theorem follows by taking
`h` a bump adapted to each cell: for `F` holomorphic the left side vanishes, and `∂̄h` localized at
the boundary turns the identity into "boundary integral = Σ residues". B's 3,374-line version is that
same identity, restated in the cell complex's normalization, with the cell/edge/vertex bookkeeping as
the hypotheses (`hvert`, `𝒯`/`𝒯s` cotree, the Kirchhoff condition `hZ`, the `ZMod m` word datum
`hWD`, …).

### 10.2 Why B is 44k and not 34k: one definitional choice

`CellDissection.edgeInt` is already an **honest interval integral**
(`∫ s in (…φs …)..(…φs …), bdryIntegrand θ s`, `Def_AlgebraicCurve_CellDissection.lean:145`) — A's
style exactly. It is `pathIntegral` that is not: it is
`if ∃ g, IsPrimitiveAlong ω γ g then g 1 - g 0 else 0`, a choice-form definition over *arbitrary*
paths between arbitrary places, introduced in the 101-line
`Def_AlgebraicCurve_ComplexLineIntegral.lean` before any dissection exists. Without an honest line
integral of a 1-form on a charted surface, the only way to have a path integral is "a primitive
exists", and then every computation needs the primitive's bookkeeping: primitives on cells, their
jumps across edges, the cotree that makes the jumps vanish, Kirchhoff's law on the word. That is
**5,495 of the 10,109** lines (`exists_primitives_jump_eq_zero_of_dualTree`,
`jump_kirchhoff_and_wordFormula_of_primitives`, `kirchhoff_and_jump_formula_of_arc_values`,
`exists_int_pathIntegral_sub_primitive_eq_sum_jump`), and the residue theorem's own 3,374 lines are
written in that language.

So the avoidable weight in B is: replace the primitive-based `pathIntegral` by A-style honest
integrals subdivided over charts (B already has `Place.chartRead`/`readDifferential` in that same
101-line file, and B already proves every regular differential primitive-able,
`exists_isPrimitiveAlong_of_mem_regularDifferentials`), then prove "path integral = sum of edge
integrals" and the residue theorem by A's Pompeiu identity applied cell-wise, the interior edges
cancelling in pairs. What survives is the genuine combinatorics — the dissection's existence
(`exists_pairedCellFamily` 4,730, `exists_dissectionScaleData` 2,429, `exists_cellDissection` 779),
`exists_tree_cotree` 883, `exists_polygonWord` 882, `euler_count_grid` 55, and the already-ported
`RadialRegion` 9,652 — plus about 1k to build the charted-surface Stokes lemma and the honest
integral once.

Net: **≈ 8.9k unported lines off B's 47.9k** (B1 in B's mouth closure is 23 nodes / 30,377, of which
20,725 unported), for a one-off ≈ 1–1.5k of new general analysis. It is not free: it is a redesign of
B's analytic layer, not a port of it, and the chart subdivision / Lebesgue-number argument is exactly
the kind of thing that grows. But it is the only move in the subject that removes weight rather than
relocating it, and it is worth about a quarter of B's cell-dissection block.

### 10.3 So the bridge runs A → B, and B → A is upside down

* **Into A: no.** The parts of A that are the same mathematics as B are the parts A does better; the
  part a bridge would actually delete (A's own proofs of rows 3–4 plus its lattice-freeness lemma,
  ≈ 3–4k of the 63k unported, of which the Abel statements are entangled with the Hecke dictionary
  and may not come out cleanly) is no bigger than the bridge (the `CuspForm ↔ regularDifferentials`
  transport exists only for Γ₀(N), `exists_linearEquiv_tensor_regularDifferentialsBar_cuspForm` 329,
  so Γ_H would need its own; plus the two integral definitions reconciled; plus B's charted-space
  hypotheses instantiated for X_Γ). Importing B to delete A would import a heavier proof of the same
  lemmas.
* **Into B: yes, ≈ 8.9k.** And it needs A's analysis to exist first — 2.3k lines of it are in A's
  closure already, are mathlib-adjacent (the §4 homing note puts them in `Complex/`), and are the one
  thing in the whole subject A can hand to B.
* **The other asymmetry runs the other way and is unusable.** B0's general place dictionary is 851
  lines (`exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex` 482 +
  `connectedSpace_of_chartedSpace_…` 369) against A's 16,867-line `ComplexPlaceDictionary{,Of}` — B
  is 20× cheaper there. A cannot borrow it: A's dictionary is not "a complex structure on the places"
  but the *explicit* H/Γ parametrization (`realize`/`pt`, the orbifold ramification
  `two_mul_ramification_eq_card_stabilizer`, the Hecke and Galois point actions) that the Hecke
  equivariance and the Tate identification are stated against. So the exchange is one-way on both
  counts: A lends analysis to B, B lends A nothing.

**Consequence for the plan.** A is not the bloated half per unit of mathematics; B1 is the subject's
main avoidable cost. If P2 is real, the port order should be: A's general residue/Stokes layer (2.3k,
`Complex/`), then A, then B with its analytic layer restructured — at §3's own written ÷ content
ratio (74,000 for 101k unported ≈ 0.73) the 8.9k is ≈ 6.5k of content, so P3's 31,000 becomes
≈ 24,500 and P2's 74,000 ≈ 67,500. If P3 alone is ever scheduled, the 8.9k restructure is the single
biggest lever available in this subject and should be priced before the first module is written, not
after.

### 10.4 The criterion is simplicity, not verification

In a formalization the checker is the check, so a second independent proof of a statement is not
evidence: it costs a second definition layer, a second maintenance surface, and a coupling — a node
that consumes both sides keeps both sides alive. The objective is therefore **simplicity**: one
definition per object, one proof per statement, the fewest boundaries between developments. Measured
against it, the subject's duplications are a list of deletions rather than of acquisitions:

1. **Two definitions of the path integral.** `periodAlongOf` (an interval integral of the form along a
   geodesic) and `pathIntegral` (`if ∃ g, IsPrimitiveAlong ω γ g then g 1 − g 0 else 0`). §10.2 prices
   the consequence: 5,495 lines of primitive/jump/cotree/Kirchhoff bookkeeping plus a 3,374-line
   residue theorem written in that language, less ≈1–1.5k of new general analysis. This is the single
   largest deletion in the subject.
2. **Two spellings of one period lattice.** `periodLatticeOf Γ : Submodule ℤ (Dual ℂ (CuspForm Γ 2))`
   and `pathPeriodLattice b : Submodule ℤ (Fin n → ℂ)`. Not two objects: coordinates against a basis
   versus the basis-free functional. Simplicity says one lives and the other is its presentation —
   and the basis-free one is the smaller statement (§9.4), while the coordinate one is what a *computed*
   lattice is used through.
3. **Two copies of the reciprocity / H₁ generation family.** A's ≈4,025 against B's ≈3,628 (§10.1
   row 2). §10.1 called that "a fair trade" and judged which *proof* is cheaper; as mathematics it is
   one statement with a general form and a modular instance, so it should be written once, in the
   general form, and instantiated — B slightly cheaper is then also the right home.
4. **One `IsCurveOver`/RR layer, instantiated rather than re-derived.** 17–28 lines per field, and it
   gives the dimension half of the rank fact without the arithmetic detour (§9.2, §12.1 chain 1). A
   port derives the rank once and does not port the counting argument.

Two things that are *not* duplications, and so are not candidates for deletion however similar they
look. The order-level dictionary (`realizeOf`, `mem_pt_iff`, `meromorphicOrderAt_realizeOf`) and B0's
manifold-level `∃ ChartedSpace …` answer different questions — orders versus integrals (§12.2) — and
the `jq` column's ψ(N)/relative-index/Φ_N-irreducibility machinery has no RR route at all (§12.3). And
neither of those is a *subject* duplication either: the first is one construction on each side of a
definitional divide, the second is a different theory of the same curve.

**Consequence for the plan: what the measure prices.** "Does it delete a definition?" has an
operational answer. Deleting a duplicated definition is worth its own lines plus every consumer that
had to be written against the losing spelling, and it costs the **bridge**: a translation lemma
between the survivor and the loser, plus the re-statement of the consumers. A node's value is
therefore `duplicated lines − bridge`, which is a sharper question than a line count. The subject's
four duplications, with survivor, deletion and bridge:

| # | one notion, two definitions | survivor | gone | bridge |
|---|---|---|---|---|
| 1 | the path integral: `periodAlongOf` (interval integral) vs `pathIntegral` (`if ∃ primitive …`) | A's | B's 5,495 primitive/jump/cotree/Kirchhoff lines and the 3,374-line residue theorem re-expressed through them — the ≈8.9k of §10.2 | ≈1–1.5k: Stokes on a bounded charted domain, plus "path integral = sum of chart integrals" |
| 2 | the period lattice: `periodLatticeOf` (submodule of `Dual ℂ (CuspForm Γ 2)`) vs `pathPeriodLattice` (submodule of `Fin n → ℂ`) | A's — the basis-free statement is the smaller one (§9.4), and the coordinate form is a *presentation* of it, not a second lattice | B's lattice as an object, and the `Fin n → ℂ`-shaped statements it forced | `CuspForm Γ 2 ≅ regularDifferentials` (the pin has it only at `Γ₀(N)`, 323 + 329) plus the coordinate map |
| 3 | the reciprocity / H₁ generation: A's ≈4,025 (winding pairing, Petersson) vs B's ≈3,628 (loops, cycle decomposition) | B's — the general form, slightly cheaper by §10.1 | A's ≈4,025, instantiated instead | 2's bridge, plus "A's `periodOf γ` is B's loop period" |
| 4 | the genus: the rank node (80), A's torus cardinality against the algebraic cardinality | RR, via `IsCurveOver` (17–28 lines per field) | the counting argument (81 + 144) and the coupling that keeps both routes alive (§9.2) | `dim S₂ = g` written once — one inequality from RR (167), the other from the differential side (§12.1) |

**Three of the four share one bridge**, which is why they fall together: duplications 1–3 all need the
honest chart integral (§10.2's ≈1–1.5k) and the `Γ_H` form of the cusp-form ↔ regular-differential
identification. Build those two and three definitions go; the fourth is independent and needs only a
short derivation.

**Restated, P2 is ≈ 61k rather than 74k, and B is the half that moves.** At §3's written ÷ content
ratio: 74,000 − 8.9k (1) − 4.0k (3) − 0.3k (4) + 1.5k (bridge) ≈ **61,000**, so B's half falls from
44k to ≈31k and P3's 31,000 becomes ≈21,000, against the 24,500 of §10.3, which priced only
duplication 1. The same arithmetic fixes P1's contents: P1 is A **plus** the two general lemmas the
three deletions depend on — the `Complex/` Stokes layer (§10.2) and the `Γ_H` cusp-form ↔
regular-differential identification — because a definition transcribed against cannot be deleted later
(§10.5). Leave either to P2 and the deletions stop being deletions and become re-work.

**The first wave is that bridge.** Its scope is the nine `Complex.*` nodes the two mouths reach — the
∂̄-Pompeiu identity, its simple-pole and log-derivative residue forms, the modular-region Green theorem
and the `circleIntegral` pair: 2,624 pin lines whose union demand is *exactly themselves*, so the wave
is closed and can be scheduled first regardless of P1/P2. Plan:
[aj/PLAN-W1-stokes.md](aj/PLAN-W1-stokes.md).

**Amendment, 2026-10-26 — the wave order follows the survivors, not the cone.** The four deletions
above are decisions about *definitions*, and the port's order has to be decided the same way, or the
deletions arrive too late to be deletions. Two things measured against `needed(653)` (`frontier
--target …`, the plain A cone, 529 nodes):

* **Items 2 and 4 are off A's cone and already the port's shape.** B's `pathPeriodLattice`, B's mouth and
  hub, and the two-route count's three nodes (80, 81, 144) are all `needed = False`; survivors 2 and 4 are
  `periodLatticeOf` and the RR route 267. Neither needs a porting decision.
* **Item 1 is not a duplication, and its 8.9k is not cashable.** The W3 scouts
  ([aj/PLAN-W3-honest-integral.md](aj/PLAN-W3-honest-integral.md) §4b–§4c) show that `pathIntegral`
  (total, chart-free, a choice over primitives) and an honest charted integral are **different objects**,
  not two spellings of one: they agree on regular paths carrying a primitive and differ elsewhere, and the
  pin already has honest integrals where it needs them (`CellDissection.edgeInt`, one fixed chart per
  cell). Replacing `pathIntegral` inside B's proofs would need a chart-change law for `readDifferential`
  that exists in neither the pin nor the port — a Kähler chart-expansion dictionary, unbounded — and it
  would change what B's statements say. So item 1 survives as *one object per side*, and the subject has
  **three** duplications, not four. Consequence for the arithmetic: P2 re-prices from ≈61k to
  **≈70k** (74k − 4.0k (3) − 0.3k (4) + the item-3 bridge), and the honest integral stays a supplement.
* **Item 3 does survive, and its bridge is now cheaper than this note thought.** Its bridge is "2's
  bridge plus 'A's `periodOf γ` is B's loop period'", and the second conjunct does *not* need the honest
  integral: both sides' integrals are chart-free, so the comparison is the **pointwise derivative
  dictionary** at `pt τ` ([aj/TOPIC-translation-a-b.md](aj/TOPIC-translation-a-b.md) §3), not a
  chart-invariance theorem. So item 3 is the best deletion left in the subject, and the honest-integral
  question does not gate it.
* **Item 3 names the only survivor inside A's cone**, and A's five row-2 nodes (810, 1052, 596, 874,
  693 ≈ 4,025) are all `needed = True`. So the decision "keep B's general form, instantiate A's" cannot
  be taken late: A's row-2 *proofs* are exactly what the bridge rewrites, and writing them first means
  writing 4,025 lines twice.

That fixes the order, and it is not "A first, then B". The subject's waves follow the
**definitional spine** — survivor definitions first, consumers after:

1. the analysis both halves stand on — **W1, landed** (the ∂̄/Stokes layer; survivor 1's analysis);
2. the survivor definitions themselves — survivor 1's general form is the one still missing: an honest
   line integral of a 1-form on a charted complex surface, plus the transport that makes `pathIntegral`
   a theorem about it. That is **W3**,
   [aj/PLAN-W3-honest-integral.md](aj/PLAN-W3-honest-integral.md), and it is cheap because mathlib
   `v4.34.0` already has `curveIntegral` with concatenation additivity and the closed-form cancellation
   (`MeasureTheory/Integral/CurveIntegral/`), which the port does not yet use — scratch-verified, along
   with `lebesgue_number_lemma_of_emetric` and `Path.map'`, and with the negative that mathlib has no
   exact-form value theorem, so that one lemma is the wave's own (`PLAN-W3` §2–§3);
3. then the consumers, in whichever order they are wanted: A's dictionary, Abel, Hecke and Tate; B's
   combinatorics; the cardinality packaging. Nothing among them is written twice as long as A's row-2
   (item 3) is written **after** W3, A's `ComplexPlaceDictionary` and the `Γ_H` cusp-form ↔
   regular-differential identification — the reconciliation of parent §9.5 item 3.

So "P1 then B" survives as a *scope* statement (A is the half the D-S column needs) and dies as an
*order* for the two pieces in items 1 and 3. My earlier reading — "the bridge is pre-B, not pre-A,
because A's cone contains no `pathIntegral`" — is withdrawn: a definition's priority is a fact about
what gets written against it, not about citation edges.

Wave order as it now stands: W1 (landed) → W2 (landed) → **W3, the honest integral**, with **W3b, the
Hecke-equivariance layer** ([aj/PLAN-W3b-hecke-equivariance.md](aj/PLAN-W3b-hecke-equivariance.md)) as
its parallel no-regret set — the largest premise-ready block that no outcome of these decisions can
invalidate. The smoothed-fundamental cluster that W2 §7 named as the natural third wave is re-cut by
W3 §7: its analysis half is W4a, and its row-2 fifth is held until the reconciliation exists.

**What the measure does not move.** B1's dissection (`exists_pairedCellFamily` 4,730,
`exists_dissectionScaleData` 2,429, `exists_cellDissection` 779, `exists_tree_cotree` 883,
`exists_polygonWord` 882, `euler_count_grid` 55, and the ported `RadialRegion`), A's
`ComplexPlaceDictionary` (16.9k, §9.1) and the `jq` column's ψ(N)/irreducibility (§12.3) are not
duplications of anything: they are the three things only one side has. They put P2's floor near 61k.
One caveat decides how much of the rest is real: the bridge is *estimated*, and §10.2 warns the
chart-subdivision argument is the kind that grows. At 3k instead of 1.5k, duplications 2 and 3 stop
paying (§9.5's verdict on the lattice comparison) and only duplication 1 survives the test.

### 10.5 Provenance: the duplications are an artefact of how the pin was written

§10.4's list is not a list of mistakes. The pin is the output of a distributed strategy — many workers,
each closing its own consumers — so every redundancy in it is a boundary where two workers met and did
not merge. The signature is measurable, and it is what the earlier sections kept running into:

* **duplicated definitions rather than duplicated claims** — two path integrals, two lattices, two
  copies of the reciprocity family, three foundations for one curve (RR, `jq`, uniformization);
* **silos** — a file's own lines against its premise cone: `minpoly_jqN_map_eq_prod_slots` is 2,002
  lines over a 60-node cone, and the `tateCurve` twin pair is 1,343 lines each with a normalized
  difference of 2 lines (a worker re-running a sibling's file);
* **identifications that are absent although every ingredient exists** — the `jq` column and RR
  (§12.3), and the pin's own cusp-form ↔ `regularDifferentials` transport sitting in neither Jacobian's
  closure (§12);
* **two-route counts**, which are the trace of two workers each needing the same fact
  (`finrank_periodLattice_eq_two_mul_genusFF`, §9.2).

The consequence is a division of what the port inherits. **The pin is a good specification of
statements and a bad architecture.** Its mouths are narrow because each worker exported only what its
own consumer needed — B's 33 lines, A's 302 and 653 — so statement-level fidelity (the `spec-pin:`
wire, `check_port` at 0 / 0) stays exactly as §7 requires, while module- and lemma-level fidelity must
*not* be inherited: the interior is not evidence of anything but the order in which the workers ran.

Two practical corollaries. First, the dedup of §10.4 cannot be done per node or per wave, the way
[porting-playbook.md](../porting-playbook.md) §2.4 does it for a single cut: these duplications span
silos whose own consumers never force them to meet, so the decision has to be taken at the subject's
level and *before* the first module — which is why the analytic layer of §10.2 (2.3k, `Complex/`) is not
a P2 luxury but a P1 prerequisite if B is ever coming. Second, the same provenance explains why the
conditional-capstone device (§3, P4) works so well here: with the interior untrusted, the pin's mouths
*are* the specification, and a port may design the middle freely as long as the two mouth statements
are reproduced verbatim.

## 11. Where the sharing ends — the 2026-10-26 graph read

§9 and §10 measured the *floor* of the sharing (the prelude both halves stand on). Neither says where
the sharing *stops*, which is what a plan that lets A supplant B needs: if the two bodies meet again
above, the supplanting is a rewiring up there, at a particular node. Measured on the same graph
(`frontier.Frontier`, union frontier, 1,212 ported nodes; A's two mouths 302 + 653, B's mouth 33):

* **Floor.** A's two mouths close over 529 nodes / 216,100 lines (189 unported / 63,186), B's mouth
  over 212 / 129,246 (91 unported / 47,861); the intersection is 113 nodes, 19 of them unported,
  1,118 lines (§9.2). Its **top** — the shared statements that no *other* shared statement cites —
  is **19 nodes**: the `Place`/`Divisor`/`RiemannRoch`/`regularDifferentials` tops, 10 of them already
  ported, plus the 311-line `Complex.circleIntegral*` pair among the nine that are not (694 of the
  1,118 lines are the tops themselves). So the floor is not a leaf: port those 19 nodes and
  *everything* A and B have in common is in the port.
* **Middle.** The intersection is *entirely* prelude. No node of A's own development appears in B's
  closure and none of B's in A's (§9.2), so between the floor and the endpoint the two are separate
  bodies, and either can be ported, or dropped, without touching the other's interface.
* **Endpoint — one node.** They meet again, as *supplies*, at exactly one node of the pin:
  `CuspForm.exists_padicGaloisModule_heckeRingH_two_frobenius_relation` (859) has **both** A's
  `…exists_heckeEquivariant_linearEquiv_tateModule_jH_padicInt_tensor_periodLatticeOf` (653) and
  `ModularCurve.moduleFinite_and_free_padicInt_tateModule_jH` (327) as *direct* premises — and it is
  the only node that has both: the 653's other four consumers (`…exists_heckeEquivariant_parabolicHoms_to_dual_tateModule_jH`
  390, `…exists_map_eq_charpoly_heckeTLinOne_and_charpoly_tateHeckeRepOne_jOne_eq_map_sq` 705,
  `…exists_monic_aeval_tateGenOpH_T_eq_zero_forall_norm_root_lt` 650,
  `…exists_ringHom_moduleEnd_twoCuspForms_apply_eq_twoCuspGenMod` 634) never see the 327, and the 327's other
  twenty consumers never see the 653. Above the 859 the column is one chain; the two routes are
  alternatives, not partners, and this is §2's rewiring located.
* **Two doors below it.** The 327-line node is where B arrives: four premises, three already ported,
  and the fourth is B's hub `AlgebraicCurve.Pic0.abelJacobiCard_genus` — 113 lines standing for 298
  nodes / 163,214 lines (149 unported / 66,381), and containing B's entire 212-node body. That is the
  *arithmetic* door. The *analytic* door is a node the notes had not named: the 126-line
  `AlgebraicCurve.Place.exists_natCast_dvd_ord_sub_single_sub_single_complex` reaches
  `Divisor.isPrincipal_of_abelJacobiDiv_mem_pathPeriodLattice` (193) and so the reciprocity and
  dissection chain down to `exists_pairedCellFamily` (4,730). Measured on the 859's own demand
  (546 nodes / 211,511 lines): closing the arithmetic door leaves 527 / 204,775 with 75 B nodes /
  43,259 lines still demanded; closing both leaves 469 / 162,886 with 18 nodes / 1,496 lines. **So
  the two doors carry 77 nodes / 48,625 lines and there is no third one.**

What that fixes. (a) B's cost to the column is not one edge: the hub premise is the visible door, but
the 126-line `Place.*_complex` node alone pulls the whole dissection, and the pin has no A-side
restatement of it — a port that takes A *instead of* B must swap the 327 for the 653 at its 21 consumers
(statement-compatible, since both give `Module.Finite ∧ Module.Free` of the Tate module) **and**
re-prove that one `Place` statement against `periodLatticeOf`, which is P2-only work (§9.3). (b) The
`--ds` prune closes both doors by name — `abelJacobi` matches A's own `abelJacobi_mem_periodLattice*`
lemmas as well, which is *why* it has to: they are the A-side half of the same door. (c) §3's P1 is
unaffected and gets a sharper contract: enter at the 653; the first node of the column it satisfies on
its own is the 859, and the only B it then inherits is the 126-line door, not the hub.

## 12. The stratification by foundation — RR, jq, uniformization

The subject's two halves do not differ at the foundations; the *pin* does. It builds the same curve
three times over, from three foundations that share no theorems:

* **RR**, the abstract function-field theory (`AlgebraicCurve.{Place,Divisor,RationalFunctionField,
  RiemannRoch,WeilExchange}`): `lSpace`, the canonical divisor, `indexOfSpecialty`, adelic Weil
  duality, `residueTheoremK` — 76 nodes / 75,135 lines by name;
* **jq**, the `q`-expansion / modular-polynomial theory (`qExpFunctionFieldC`, `xHFunctionField`,
  `modularFunctionFieldFull`, `jqN`, `Φ_N`): the function field is generated by `j` and `jqN`, and its
  degrees are computed by Dedekind's `ψ` and relative indices, never by RR;
* **uniformization**, the period/torus theory (`Pic0.exists_torusPoints_uniformization_of_periodDatum`,
  the Mumford/equivariant uniformization): periods and lattices, again not divisors.

Measured on premise cones (pin `aa2d8b3`):

| development | cone | RR nodes in it |
|---|---:|---|
| `minpoly_jqN_map_eq_prod_slots`, the jq/FFG slot product | 60 / 15,816 | **0** |
| `…exists_torusPoints_uniformization_of_periodDatum…` | 147 / 42,842 | **0** |
| `…exists_equivariantUniformization_of_mumfordQuotient…` | 248 / 67,304 | 4 / 3,823 |
| **A**, both mouths | 529 / 216,100 | 14 / 32,733 |
| **B**, the mouth | 212 / 129,246 | 14 / 30,211 |

So the two halves of *this* subject are not the strange pair: their RR cones overlap in **twelve of
fourteen nodes** — `residueTheoremK_ratFunc_of_isAlgClosed` (13,170),
`residueTheoremK_of_isAlgClosed` (8,121),
`functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed` (6,257), its three `of_…` instances,
`finiteDimensional_lSpace` (1,092), `indexOfSpecialty_{eq_of_genusReached,eq_finrank_H1}`,
`weilDualityAdelic_…`, `ell_canonicalDivisor_eq_genus_of_riemannRoch`,
`degree_canonicalDivisor_eq_of_riemannRoch` — and the two differences are unrelated to the subject
(A adds `lSpace_eq_bot_of_degree_neg` and `RationalFunctionField.finiteDimensional_lSpace_zero_of_constantsAreBase`;
B adds `degree_canonicalDivisor_eq_of_isAlgClosed` and
`exists_indexOfSpecialty_nsmul_single_eq_zero_of_genusReached`). RR is not B's private foundation; it
is the floor of both, and that floor is most of the 113 nodes the two closures share (§9.2).

The strange pair is **jq and uniformization against RR**, and the zeroes above are structural, not
accidental: the `jq` column asks for *degrees of a covering* (`j(q^p) ∉ K(j(q))`, `finrank = ψ(N)`,
relative index and relative rank) and the uniformization column asks for *periods of a torus*. **The
`jq` column never states "this curve is an abstract function field, so RR applies to it"**, though it
works with exactly the field `xHFunctionField M H` on which the statement is available
(`isCurveOver_of_transcendental` 21, `hasCanonicalDivisor_of_isCurveOver` 1,723) and though the
arithmetic column states it for its own curve (`isCurveOver_modularFunctionFieldFullC` inside
`ell_eq_degree_add_one_sub_genusFF_modularFunctionFieldFullC`, 506, with fifteen consumers in the
height/dimension-formula column). It re-derives degrees inside its own foundation instead. Transporting
along a change of foundation is a theorem, and the pin only wrote such theorems where a consumer needed
one; every consumer of the `jq` and uniformization columns lives inside one foundation, so none was
written.

### 12.1 How A uses RR — three chains

A *does* instantiate RR on its curve, and it uses it three times. Measured on the cones:

1. **Dimension bookkeeping, inside Abel's theorem itself.** The mouth (302) → 817 → the converse (133)
   → the witness (117) → `exists_cuspForm_mul_exp_periodOf_eq_one_of_abelJacobi_mem_periodLatticeOf_gammaH`
   (495) → `finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup` (40) →
   `finrank_parabolicHoms_Gamma_le_two_mul_finrank_cuspForm` (134) →
   `twelve_mul_add_mul_index_le_finrank_cuspForm_Gamma` (167) → `LevelN.twelve_mul_add_mul_index_le_genusFF`
   (597) → `regularDifferentials ↪ CuspForm` (101, 813, 870) + `sum_ord_sub_one_le_two_mul_genusFF_of_isSeparable`
   (76) / `sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable` (418) + `functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver`
   (39) + `ell_canonicalDivisor_eq_genus_of_riemannRoch` (13). The bound
   `finrank ℤ (parabolicHoms ℤ Γ ℤ) ≤ 2 · finrank ℂ (CuspForm Γ 2)`, which the witness needs, *is* the classical
   `12 · index` computation, and the pin gets it from RR.
2. **Separation of places.** `exists_slashInvariant_residue_ne_zero_of_pt_ne_gammaH` (419) cites
   `functionFieldRiemannRoch_of_isAlgClosed_of_transcendental` (77) *directly*: it produces a
   weight-2 slash-invariant with a simple pole of prescribed residue at `pt τ₁` and none elsewhere —
   RR's existence of a function with a prescribed pole, which is the one place A treats its curve as
   an abstract function field for a function-theoretic purpose.
3. **Vanishing, and principality by descent.** The injectivity half of the mouth,
   `exists_injective_heckeEquivariant_addMonoidHom_jH_pic0_complex` (670), cites
   `AlgebraicCurve.Divisor.exists_torsion_descent_of_constantFieldExtension` (878), whose proof is RR:
   `lSpace_eq_bot_of_degree_neg` (89), `finiteDimensional_lSpace` (1,092),
   `RationalFunctionField.finiteDimensional_lSpace_zero_of_constantsAreBase` (2,545). "Zero period
   vector ⇒ principal" is decided over `ℚ̄` and descended — with RR's vanishing doing the deciding.

So RR is not B's foundation that A happens to share: it is load-bearing in A at the dimension, the
place-separation and the descent, i.e. at exactly the three points where the modular construction
needs the *curve* rather than the *series*. That is also the state of §9.5's rank gate: chain 1 gives
one inequality of `dim S₂ = g` from RR (167, with `dimFormula ≤ finrank` alongside it); the other
inequality comes from the differential side, and the pin's actual rank node (80) does not take this
route at all — it pairs A's torus cardinality with the algebraic one. So the rank fact stays a
coupling until someone writes the equality this way.

### 12.2 Why A can use RR without the curve–function-field connection

Because in this pin the "curve" RR speaks about *is* the function field. `Place K F` is a
valuation-theoretic object — `toValuationSubring : ValuationSubring F`, `≠ ⊤`, `IsPrincipalIdealRing`
— `ord` is that valuation, `Divisor` is the free abelian group on such places, and `IsCurveOver` adds
only the finiteness hypotheses. Applying RR at `F = laurentBaseChange ℂ (xHFunctionField M H)`
therefore needs `IsCurveOver ℂ F` and nothing else, which `isCurveOver_of_transcendental` (21) supplies
from a transcendental generator; `hasCanonicalDivisor_of_isCurveOver` (1,723) then hands over the
canonical divisor. There is no manifold anywhere in A's use of RR: A's 529-node cone contains **zero**
nodes mentioning `ChartedSpace`, `extChartAt`, `IsPrimitiveAlong` or `pathIntegral`, against B's three
charted-space nodes / 1,010 lines, two `extChartAt` / 761 and ten `pathIntegral` / 11,340.

What A proves instead is an *order-faithful series realization*, and it pays for it in two structure
fields rather than in theorems:

* `realizeOf Γ x τ` is defined by **substitution**: write `x` as `f / g` with `f`, `g` modular forms
  whose `qExpansion`s give `x`, and evaluate `f τ / g τ` (the `if ∃ … then … else 0` of
  `Def_ModularCurve_ComplexPlaceDictionaryOf.lean:15`);
* `mem_pt_iff` then says `x ∈ (pt τ).toValuationSubring` iff `‖realizeOf Γ x‖` is bounded in a
  punctured neighbourhood of `τ` — the place is *defined* by analytic boundedness of the series, never
  by a chart;
* `meromorphicOrderAt_realizeOf` reads off `meromorphicOrderAt (realizeOf Γ x) τ = ramification τ * (pt τ).ord x`.

So "the curve is its function field" is replaced by "the `q`-expansion realization is order-faithful",
a statement about series, absorbed into the dictionary's construction. That is enough for all three RR
uses of §12.1 — the dimension computation (pure function field), place separation (a function-field
existence statement transported to `ℍ` through the same realization, 419), and vanishing/descent (pure
function field, 878).

It is *not* enough for B, and that is the gap: B's `MeromorphicAt` and `pathIntegral` are computed on
`Place ℂ F` *as a complex manifold*, whose existence and order-compatibility is B0's
`exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex` (482) plus
`connectedSpace_of_chartedSpace_…` (369). So "connect a curve to its function field" has two strengths
here: the **order-level** one, which A has as a structure field and which costs nothing beyond
`qExpansion`; and the **manifold-level** one, which only B needs and which A never states. A hands over
an order dictionary; B needs a complex structure.

### 12.3 Could the same device have carried RR into the rest of the `jq`-based curve theory?

Yes, and the pin already has the parts — scattered across three columns, none of them the `jq` one:

| statement | lines |
|---|---:|
| `isCurveOver_qExpFunctionFieldC_of_isAlgClosed` | 22 |
| `isCurveOver_modularFunctionFieldC_of_good` | 17 |
| `isCurveOver_modularFunctionFieldC_of_isSeparable_jqNModC` | 28 |
| `isCurveOver_modularFunctionFieldC_of_perfectField` | 390 |
| `isCurveOver_modularFunctionFieldBar` | 162 |
| `genusFF_qExpFunctionFieldC_eq_of_ringHom` | 265 |
| `genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar` | 686 |
| `ell_eq_degree_add_one_sub_genusFF_modularFunctionFieldFullC` | 506 |
| `abelJacobiCard_genusFF_qExpFunctionFieldC` | 478 |

The `jq`/FFG cone (60 nodes) cites **none** of them: zero nodes mentioning `IsCurveOver`, `genusFF`,
`Divisor`, `lSpace` or `RiemannRoch`. Note what the last two rows mean — RR *is* applied to the modular
function field (`ell = deg + 1 − genusFF`, 506, inside the height/dimension-formula column) and the
Abel–Jacobi **cardinality** is stated for the `q`-expansion field itself (478, for
`qExpFunctionFieldC K Γ` over any algebraically closed `K`), with a single consumer in the char-`p`
Frobenius-degeneracy column. So the theory of §12.2 is not confined to A's curve: it is `IsCurveOver`
plus a function field, and every field in the `jq` family admits it for 17–28 lines.

**What it would and would not replace.** RR delivers genus, `lSpace` dimensions, `deg K = 2g − 2` and
vanishing. The `jq` column's outputs are different statements: exact covering degrees
(`finrank = ψ(N)`, relative index and relative rank) and irreducibility of `Φ_N` (`minpoly` = the slot
product). RR produces neither — an exact cover degree needs Hurwitz, which is not in the pin, and
irreducibility needs the Galois theory the column already uses. So the device buys no **second route**
to genus or to the dimensions of form spaces — by §10.4 that would be a cost — it buys nothing unless a
dimension is wanted once and RR is the cheapest place to get it, which is the case for A (§12.1) and
not for the `jq` column. And it buys nothing at all for B, because the `q`-series device transports
orders while `pathIntegral` needs charts (§12.2).

**What that means for a port.** (a) The RR pillar is *shared*, so porting it is not porting B: A's
cone and B's cone use twelve of the same fourteen nodes, and `AlgebraicCurve/{Genus,Differential,
RiemannRoch,WeilExchange}` in `FLTForHuman` is the common floor. (b) The `jq` column is genuinely
independent: in the port, `FunctionFieldGeneration` (13 modules) and `Jq*`/`ModularPolynomial*`/
`PhiGen*` (21) import **nothing** from the 82 ported `AlgebraicCurve/{RiemannRoch,Genus,Differential,
Canonical,WeilExchange,ResidueTheorem,P1,IsCurveOver,Place,PrincipalDivisors,Tate}` modules — 0
imports — which is why it could land as a silo. The only port modules that do import that pillar are
`ModularCurve/XH|X1|LevelN` (12) and `ModularCurve/Analytic/CuspDichotomy` (5, into
`PrincipalDivisors`/`WeilExchange`). (c) The three arrows that would join the foundations are the
same three comparisons §1 lists (periods = integrals of holomorphic differentials, Hecke
equivariance, Tate ≅ lattice ⊗ ℤ_[p]) — so the foundation-level comparison is not cheaper than the
statement-level one, and *this* is why the subject looks like two developments: the pin never had to
write the identification, and the port inherits the gap rather than causing it.

The one concrete mechanic in that gap is worth keeping: where the pin *does* cross a foundation
boundary, it crosses by a `q`-series substitution (`qExpansion` → `LaurentSeries`, `laurentBaseChange`,
`realizeOf Γ x` at `q = e^{2πiz}`), which transports **orders** — the complex place dictionary's own
field is `meromorphicOrderAt (realizeOf Γ x) τ = ramification τ * (pt τ).ord x`. That is why A's cone
carries 82 `jq`/`qExp` nodes / 26,850 lines while B's carries none with any modular vocabulary at all,
and why an order-level interface is the one kind a port can build cheaply. Periods do not transport
along it.

## 13. Links

* **the first wave — the shared ∂̄/Stokes layer as a mathlib supplement (9 `Complex.*` nodes, 2,624
  lines; landed, 2,768 written):** [aj/PLAN-W1-stokes.md](aj/PLAN-W1-stokes.md),
  [aj/WORKORDER-W1-stokes.md](aj/WORKORDER-W1-stokes.md)
* **the second wave — the parabolic-hom / period-map layer (6 nodes, 2,433 lines; landed):**
  [aj/PLAN-W2-parabolic-homs.md](aj/PLAN-W2-parabolic-homs.md),
  [aj/WORKORDER-W2-parabolic-homs.md](aj/WORKORDER-W2-parabolic-homs.md)
* **the third wave — the honest integral on a charted surface**, i.e. survivor 1's general form and the
  transport that makes `pathIntegral` a theorem about it:
  [aj/PLAN-W3-honest-integral.md](aj/PLAN-W3-honest-integral.md). ≈400–800 written for a gate on ≈12.9k
  of deletion (§10.4's items 1 and 3). mathlib already has the curve integral
  (`MeasureTheory/Integral/CurveIntegral/`), which the port does not yet use, so this is adoption plus
  chart glue — scouted first (§2.6), because the one open question is whether the primitive transport
  needs a path-regularity hypothesis that B's pinned statements do not carry (plan §3, D1). It also
  re-cuts the smoothed-fundamental cluster (plan §7): its analysis half is W4a, its row-2 fifth is
  held.
* **W3b — the Hecke-equivariance layer of the period map (12 nodes, 2,366 lines + ~75 of definition
  tails):** [aj/PLAN-W3b-hecke-equivariance.md](aj/PLAN-W3b-hecke-equivariance.md). The third wave's
  parallel set and the largest premise-ready block no survivor decision can invalidate, so it is
  dispatched beside W3's scout rather than after it. It also happens to be the third block of the
  mouth's unported premises: after it `…tateModule_jH_padicInt_tensor_periodLatticeOf` (653) has **two**
  unported direct premises (302 and 267) instead of nine, and `needed(653)` drops from 168 nodes /
  57,836 lines to 156 / 55,470.
* why A and not B: the FLT cone reaches A's Tate identification (653) through
  `CuspForm.exists_padicGaloisModule_…` (859) and nothing else proves it; `needed(653)` was 174 unported
  nodes / 60,220 lines, of which 66 nodes / 12,778 were ready when W1 landed (§10.4)
* **the translation layer — what a merged A–B theory has to identify:** the seven identifications
  (curve, charts, cusp forms ↔ differentials, geodesics ↔ paths, integrals, lattices, divisors) with their
  status, and the finding that the translation is *pointwise* — a derivative dictionary at `pt τ` — so it
  needs neither the honest-integral decision nor the chart-change cocycle:
  [aj/TOPIC-translation-a-b.md](aj/TOPIC-translation-a-b.md)
* the prune, its narrowing and the residual: [deligneSerre/PRUNABLE-complex-analytic.md](deligneSerre/PRUNABLE-complex-analytic.md) §7
* the cell-dissection / radial-region plan: [algebraicCurve/TOPIC-cell-dissection.md](algebraicCurve/TOPIC-cell-dissection.md)
* the pair that surfaced this: [modularCurve/TOPIC-padic-tate-module.md](modularCurve/TOPIC-padic-tate-module.md)
* the RR column: [PORTING-RR.md](PORTING-RR.md); the scout: [../studies/deligne-serre-weight-one-scout.md](../studies/deligne-serre-weight-one-scout.md) §4.2
