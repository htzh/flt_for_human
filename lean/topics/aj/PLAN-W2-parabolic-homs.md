# W2 — the parabolic-hom / period-map layer

Second wave of the aj subject, 2026-10-26. Parent: [PLAN-W1-stokes.md](PLAN-W1-stokes.md) (the ∂̄/Stokes
layer, landed) and [../TOPIC-abel-jacobi-port-structure.md](../TOPIC-abel-jacobi-port-structure.md).
Pin `anthropics/fermats-last-theorem@aa2d8b3`; port mathlib `v4.34.0`.

**Why A, and why this slice.** A is not avoidable for the FLT target: `closure(FLT.fermatLastTheorem)`
contains `CuspForm.exists_padicGaloisModule_heckeRingH_two_frobenius_relation` (859), which contains
A's Tate identification `…exists_heckeEquivariant_linearEquiv_tateModule_jH_padicInt_tensor_periodLatticeOf`
(653), whose statement has no other proof in the pin (B gives finiteness only). `needed(653)` is
**174 unported nodes / 60,220 lines**; of those **66 nodes / 12,778 lines are ready now** — every premise
already ported — and this wave takes the parabolic-hom block out of that shelf.

**Status: landed 2026-10-26.** Six headlines green in two modules (2,411 written lines), plus the one
gap node the wave exposed (`Period.IsEquivariantPrimitive.isParabolicHom_periodHom`, now public in
`ModularForms/EichlerShimura/PeriodHomParabolic.lean`): `check_port.py --all` 5852 ok / 0 mismatch /
0 missing over 269 modules. Outcome, the two open micro-items and the W3 homing note are in
[WORKORDER-W2-parabolic-homs.md](WORKORDER-W2-parabolic-homs.md) §10. Nothing committed.

## 1. Scope

Six pin nodes, **2,433 lines**, pairwise **independent** (none cites another; all their premises are
ported or mathlib):

| # | pin node | lines | content |
|---|---|---:|---|
| 1 | `Period.exists_basis_parabolicHoms_of_isAddTorsionFree` | 273 | a `ℤ`-basis of `parabolicHoms ℤ Γ ℤ`, and a matching basis over every commutative torsion-free ring, with the same coordinates |
| 2 | `Period.exists_basis_parabolicHoms_castAddHom_comp` | 505 | the same statement for fields: a `ℤ`-basis and a matching `K`-basis whose coordinates agree under `Int.castAddHom K` |
| 3 | `Period.finrank_parabolicHoms_add_natCard_le_finrank_addMonoidHom_add_one` | 141 | the rank inequality `finrank (parabolicHoms K Γ K) + #(orbits of T) ≤ finrank (Γ →+ K) + 1` |
| 4 | `Period.existsUnique_isParabolicHom_sup_zpowers_neg_one_apply_eq` | 169 | extending a parabolic hom along `Γ ↪ Γ ⊔ ⟨−1⟩`: existence and uniqueness |
| 5 | `Period.exists_parabolicHoms_int_castAddHom_comp_eq_of_forall_isOfFinOrder` | 886 | a parabolic hom `Γ → ZMod n` vanishing on torsion lifts to one `Γ → ℤ` |
| 6 | `exists_exp_eq_of_invariant_ne_zero_isParabolicHom` | 410 | an invariant nowhere-zero `Φ` with cusp limits is `exp` of a primitive `L` whose periods are a parabolic hom |

Nodes 1–3 are the lattice/rank theory of `parabolicHoms`; 4 is the `±1` extension; 5 is the arithmetic
determination lemma (a coboundary is detected on torsion); 6 is the analytic counterpart that produces a
parabolic hom from an invariant function. They are the layer the period map rides on: `periodMapOf`
already maps cusp forms into `parabolicHoms` (ported, `ModularCurve/Period/ParabolicHoms.lean`).

## 2. Homing

Both modules continue the existing subject directory — this is the period-map layer, and
`ModularCurve/Period/` is where the port already keeps `PeriodLatticeSpan`, `PeriodLatticeBoundary`,
`ParabolicHoms`, `QExpansionDerivative`, `QExpansionDiff`, `ThetaMul`:

| module | nodes |
|---|---|
| `FLTForHuman/ModularCurve/Period/ParabolicHomsBasis.lean` | 1, 2, 3 |
| `FLTForHuman/ModularCurve/Period/ParabolicHomsDetermination.lean` | 4, 5, 6 |

The split is by content, not by size: 1–3 are basis/rank statements about one module; 4–6 are
determination statements (by torsion values, by an invariant function). No new definition layer is
expected — `Period.parabolicHoms`, `IsParabolicHom`, `IsEquivariantPrimitive` and `periodHom` are all
ported (`ModularForms/EichlerShimura/PeriodPrimitive.lean`), and `periodAlongOf` sits in
`ModularForms/EichlerShimura/PeriodOf.lean`.

## 3. Order

The six are independent, so the order is by module only: 1, 2, 3 then 4, 5, 6. Two implementers can work
in parallel, one per module, since neither imports the other.

## 4. Budget

2,433 pin lines → ≈2,600 written at W1's measured 1.07 written-per-pin. Nodes 5 (886) and 2 (505) are
the two large proofs; 3 and 4 are short.

## 5. Decisions

* **D1 (inherited).** Pinned statements are transcribed verbatim; `dbar`/local abbreviations never enter
  them. Helpers are `private`, headlines public at the pin names.
* **D2 (new).** Nodes 1 and 2 state `∃ n, ∃ b : Basis (Fin n) …`. Do not replace `n` by
  `finrank` — the pin's `n` is existential and the statement is what the checker diffs.
* **D3 (new).** Node 3's `Nat.card (MulAction.orbitRel.Quotient (zpowers T) (SL(2,ℤ) ⧸ Γ))` is the
  orbit count of `T` on the cosets; it is not `finrank`-shaped and must not be normalised.
* **D4 (new).** Node 6 produces `L` together with `HasFDerivAt L ((Φ τ)⁻¹ • fderiv ℝ Φ τ) τ` — keep the
  `ℂ`-scalar `•` spelling; it is the pin's.

## 6. Verification

Same as W1: `spec-pin:` headers for the six headlines (wrappers + `S_` files), `check_port.py` module at
`0 mismatch / 0 missing` with **no** `SOURCES`/`PORT_FILES` edit (those lists are frozen in
`spec/old_check_stmts.py`), `#print axioms` clean, a mutation test per headline, and the
upstreamability not required here (these are `ModularCurve` statements, not mathlib supplements — homing
is by subject, not by upstreamability).

## 7. The rest of the ready shelf (W3 and later)

**Corrected 2026-10-26 (see §8).** This section originally named the smoothed-fundamental-set cluster
as the natural W3 and left the choice there. Measured on the frontier after this wave landed, that
priority is wrong: the third wave is the **Hecke-equivariance layer** — 12 nodes / 2,366 lines, 7 of
the 9 unported direct premises of A's mouth — and the smoothed cluster is deferred one wave, to W4.
The shelf figures below are still right (measured now: **62 nodes / 11,330 lines** premise-ready, of
which 17 / 2,858 are `--ready` in the strict sense that they also reach the frontier); it is the
ordering that was wrong, not the count.

62 nodes / 11,330 lines are premise-ready after this wave, in four clusters:

* **smoothed fundamental set / UHP analysis** (4,419 lines): `contDiff_and_finsum_smoothedFundamental_eq_one` 509,
  `UpperHalfPlane.exists_localModel_pair_integral_mul_dbarLogDeriv_eq` 410,
  `exists_modularForm_eventuallyEq_div_of_meromorphic_of_finiteIndex` 659,
  `exists_meromorphic_logDeriv_eq_of_int_residue` 557, the orbit-rep and stabiliser lemmas — the
  consumer of W1's ∂̄ layer;
* **Hecke/slash on modular forms** (≈1,460): `heckeU_slash_eq_self_of_mem_GammaH` 481 + `add_slash` 489,
  `exists_gamma0_apply_mul_apply_ne_of_forall_smul_ne` 418, `HeckeEis.existsUnique_coeffCocycles_sl2z_apply_S_ST_eq` 452;
* **the cusp-form/`jq` bridge** (≈1,100): `finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap` 314,
  the `qExpansion`/`coeMap` family, `realizeOf_eq_div` 57;
* **`Place`/`PeriodPair` leaves** (≈900): the RR-prelude and Weierstrass-period leaves.

**Not W3 either — corrected twice the same day, and then again by scope.** The paragraph above reads the
order off the target's premise list, and that is the criterion the subject does not run on. §10.4's
criterion is **simplicity**: survivor definitions first, consumers after. With the port ordered A-only
(parent §10.4's wave order), the merged theory is deferred, and with it the honest integral — item 1's
survivor, which is B's — built and green but shelved in `Reserve/`. So the third wave is the Hecke block,
[PLAN-W3b-hecke-equivariance.md](PLAN-W3b-hecke-equivariance.md): A's own last definitional layer, the
largest premise-ready block whose content no survivor decision can invalidate, and 7 of the 9 unported
direct premises of the mouth (653), which it takes to two. The smoothed cluster is still W4, and W3 §7
re-cuts it: its analysis half is W4a, and its row-2 fifth (A's ≈4,025) is no longer *held* — with the
reconciliation deferred there is no rewire, so it is transcribed at its pin size after W4a.

This section's one durable observation survives the correction: the smoothed cluster is where W1's ∂̄
layer is consumed, and the homing question it raises (`ModularCurve/Analytic/` versus the existing
`AutomorphicForm/UpperHalfPlane/` — which already holds `Gamma0FundamentalSet.lean`,
`ModularFundamentalDomain.lean`, `HyperbolicMeasure.lean`) is the first thing W4's own plan must
settle, since W1's node 7 sits in `ModularForms/FundamentalDomainStokes.lean` for the same reason.

## 8. Was W2 the right wave? — the 2026-10-26 retrospective

Asked after W3 was scoped, and answerable now with the numbers. **Yes: W2 was correctly chosen, and
better-placed than its own §1 argued.** Three measurements:

1. **Zero waste.** All six headlines are in `needed(653)`; the frontier moved by exactly them
   (174 → 168 nodes, 60,220 → 57,836 lines). Nothing ported here is outside the mouth's cone.
2. **It sits one layer *under a surviving mouth premise*.** All six have a cone citer, and four land
   in the 267 block (`exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup`,
   the rank/discreteness half of the mouth): node 1's cone citers are 495, 548, **267 itself** and 416;
   nodes 2, 3 and 4 all feed `six_mul_level_mul_finrank_parabolicHoms_Gamma_add_eq` (552), which 134 —
   in 267's sub-closure — consumes. The other two build *both* downstream blocks: node 5 (886) feeds
   384, whose own citer 604 is the multiplier/`exp` chain, and node 6
   (`exists_exp_eq_of_invariant_ne_zero_isParabolicHom`, 410) feeds **874**, the winding-pairing node
   that W4's cluster is built on. So W2 was support for W3's and W4's subject at once — a better
   placement than §1 claimed for it, which argued only from A's Tate identification.
3. **The gain test passes too.** Node 1 has **19** citers outside A's cone and node 2 **14** — the
   `parabolicHoms` basis API is used well beyond this subject, which is what an early wave should
   optimise for.

One qualification, added after the criterion correction: the three reasons above are about *value*, and
they remain the right answer to "was the work worth doing". They are not the reason the wave was
*correctly placed*, because the plan now orders waves by definitions rather than by the mouth. The
property W2 actually has under that criterion is that `parabolicHoms` sits on the **survivor** side of
every §10.4 decision — it is the codomain of A's period map, on A's honest integral, and B has no
analogue of it at all (`§9.1`'s table) — so nothing W2 wrote is a spelling a later decision rewrites.

The two non-line returns W2 recorded also stand: the `isParabolicHom_periodHom` gap node (read as
satisfied because it existed only as `private`, a frontier defect now fixed) and the homed
crossed-hom prelude. What was wrong was not the wave but the sentence after it — §7's "natural W3" —
and that is corrected above.
