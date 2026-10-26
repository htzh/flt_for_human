# The p-adic Tate module: the `jOne`/`jH` pair, and the definition layer beneath them

Scoping note, 2026-10-25. Two frontier nodes looked at together because they are one theory:
`ModularCurve.moduleFinite_padicInt_tateModule_jOne` (283 pin lines) and
`ModularCurve.moduleFinite_and_free_padicInt_tateModule_jH` (327). The measurement says they are the
same set, that neither is dispatchable yet, and that the piece worth doing first is the definition
layer they stand on.

## 1. The pair

`moduleFinite_padicInt_tateModule_jOne M p : Module.Finite ℤ_[p] (TateModule p (JOne M))`;
`moduleFinite_and_free_padicInt_tateModule_jH M p H : Module.Finite ℤ_[p] (TateModule p (JH M H)) ∧
Module.Free ℤ_[p] (TateModule p (JH M H))`. The second is the first plus freeness, for the
intermediate Jacobian `JH` with `H ≤ (ZMod M)ˣ` (`JOne` is the `Γ₁` case). Both go through
`2 · genus` torsion growth: `Nat.card (torsionBy ℤ (JH M H) ((p^n : ℕ) : ℤ)) = (p^n) ^ (2 · genus)`.

**They are one set.** The two `S_` files share a **13-declaration engine** byte-identically —
`TateModule.RankD`: `finite_torsionBy`, `mulP_surjective`, `proj_surjective`,
`exists_family_of_card_eq_pow`, `exists_indep_family`, `dvd_of_rel_apply`, `levelMap`,
`levelMap_injective`, `levelMap_bijective`, `exists_coeffs`, `exists_eq_sum_smul`, `exists_family`,
`moduleFinite` — **191 removable lines** (`port_advise` §2), stated at general rank `d` with
`hcard : ∀ n, Nat.card (torsionBy ℤ M ((p^n : ℕ) : ℤ)) = (p^n)^d`. The `jH` file adds the basis half,
`TateModule.RankDBasis`: `top_le_span`, `coe_sum_smul_apply`, `linearIndependent_family`,
`basisOfCard`, `moduleFinite_and_free`, `finrank_eq` — six declarations. So `jOne` is the rank
engine plus finiteness, `jH` the same plus a `ℤ_[p]`-basis. Porting them apart would write the
engine twice.

## 2. Readiness — measured

### The `--ds` reading, and the second supply

`frontier --ds --target ModularCurve.moduleFinite_and_free_padicInt_tateModule_jH` prices this
pair at **1 node / 327 lines**, i.e. as its own node with its numerical premise avoided: the D-S
prunable set is pattern-matched on the pin's names and the substring `abelJacobi` catches
`AlgebraicCurve.Pic0.abelJacobiCard_genus`, the node the pair's proof takes its `p^n`-torsion
cardinality from.

That reading is a **rewiring assumption**: the column also has a modular supply for the same fact —
`ModularCurve.finite_torsion_jOne` (80 pin lines) proves `Finite (Pic0.torsion … n)` for the modular
curve from `periodLatticeOf`/`periodAlongOf`, and
`exists_heckeEquivariant_linearEquiv_tateModule_jH_padicInt_tensor_periodLatticeOf` identifies the
Tate module with the period lattice ⊗ ℤ_[p] (five citers, among them the p-adic Galois module
itself). The pinned chain cites both routes, and *both* are cut by the prune at their Abel–Jacobi
core — the modular route too, through `ComplexPlaceDictionaryOf.abelJacobi_mem_periodLatticeOf_*`
([../deligneSerre/PRUNABLE-complex-analytic.md](../deligneSerre/PRUNABLE-complex-analytic.md) §7). A
one-day narrowing of the prune was reverted on 2026-10-25: the breadth is the subject's, not a
naming bug.

A's premise closure contains neither `abelJacobiCard_genus` nor B's mouth, so the modular route does
not consume the abstract theory — and since the Tate module's finiteness/freeness follows from
`TateModule ≅ ℤ_[p] ⊗ periodLatticeOf` plus the lattice's freeness, the pair's *statement* can be
derived on the modular route. **B is therefore not needed for the D-S column**; a faithful port of
the pinned pair, however, cites B's hub, so taking A means recording that one-node rewiring.

So: the pair's own price is the unpruned one (145 nodes / 66,603 lines for its cone), the D-S column
does not have to pay it, and which route the port takes — this pair's Abel–Jacobi route or the
modular period route — is a scheduling decision, with both prices and the two-supply structure in
[../TOPIC-abel-jacobi-port-structure.md](../TOPIC-abel-jacobi-port-structure.md).

Neither reading prices the *definition*: the frontier walks citation edges, not import-only
definition nodes, so `Definitions/Def_EllipticCurve_TateModule` (the `TateModule` definition, 69 of
its 100 declarations) is invisible to both. That is why §3 starts with the definition layer.


| | `jOne` | `jH` |
|---|---:|---:|
| cone | 301 nodes / 164,863 lines | 301 nodes / 164,907 lines |
| frontier nodes inside the cone | 151 | 151 |
| needed (unported) | 145 nodes / 66,603 lines | 145 nodes / 66,647 lines |

The demand is `AlgebraicCurve.` 125 nodes / 62,165 lines, plus a thin tail (`Complex.` 6, `Manifold.`
2, `Homeomorphism`/`Matrix`/`ZMod`/`Submodule`/`ValuationSubring` one each, and the
`exists_fundamentalCycles_of_spanningTree` leaf).

**The gate is one node.** Both targets are one hop from
`AlgebraicCurve.Pic0.abelJacobiCard_genus`, whose own frontier is **144 needed nodes / 66,320
lines** — the remaining differential/Pic⁰/Jacobian layer of the curve development. Everything else
the two instantiations use is already ported: `isCurveOver_of_transcendental` (6 modules),
`hasCanonicalDivisor_of_isCurveOver` (6), `genus`, `x1FunctionFieldBar` / `xHFunctionFieldBar`,
`ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange`,
`Gamma1_le_GammaH`, `translation_mem_GammaH`, and `T_mem_Gamma1` (already in the port as
`WPGamma1.T_mem_Gamma1` in `Elliptic/PeriodPair/InvariantsTorsion.lean`).

**The other gate is the definition.** `TateModule` itself is **absent from the port** — a grep finds
it only in a header comment. The pin declares it in
`Definitions/Def_EllipticCurve_TateModule.lean` (883 lines, 100 declarations), of which the
`TateModule` namespace is **69** declarations (the definition, `proj`/`mulP`/`kerMulPEquiv`/
`liftFun`/`levelMap`, the torsion-cardinality API, and the rank-2 `free`/`finite`/`finrank_eq_two`
tail); the other 31 are **other nodes' material** — `WeierstrassCurve` 18 (`Affine.Point.coords`, the
torsion field, `tateModuleRep`, `isAdicContinuous`) and `GaloisRep` 11 + `PadicInt` 2 — consumed by
`ModularCurve.exists_module_padicInt_tateModule_jZero_galoisRep_isAdicContinuous_heckeRep`, not by
this pair.

## 3. What to do, in order

**(T1) the definition layer, now.** A module for the p-adic Tate module and its rank theory, of
which the two headlines are later fifteen-line assemblies:

* the pin's `TateModule` namespace (69 declarations, mathlib-only), minus the Galois-rep and
  Weierstrass halves, which are deferred to the `tateModule_jZero_galoisRep` node and registered;
* the general-`d` rank engine once (the 13 shared declarations + the six of `RankDBasis`), as the
  generic theorem *"a `ℤ`-module whose `p^n`-torsion has cardinal `(p^n)^d` has a free `ℤ_[p]`-Tate
  module of rank `d`"* — the pin's own rank-2 block is then the `d = 2` consequence, which is the
  dedup: state the pin's rank-2 statements (they are public surface for the elliptic-curve/Galois
  consumer) and prove them from the general engine rather than twice.

Home and names: a new `NumberTheory/PadicTateModule.lean`, namespace `PadicTateModule` — the object
is not curve-specific (`[AddCommGroup M]`), and its consumers are modular Jacobians first,
elliptic curves later; `AlgebraicCurve/Tate/` is the residue/trace machinery and is not the home.
The pin's rank-2 facts keep the pin's names; the general-`d` engine is this module's own.

**(T2) the two headlines, when the gate lands.** `JOnePort`/`JHPort` (5 + 6 declarations: the curve
facts, the `card_torsionBy_*` step, the `solution`s) are otherwise ready; they are one dispatch,
the engine already being in place. Do not port the instantiation blocks before the gate: without
`card_torsionBy_*` their only consumer is the missing headline.

Prices: T1 ≈ 90 declarations, ~700 written lines, one dispatch after the manager's definitions; T2
≈ 60 lines once `abelJacobiCard_genus` exists. The gate itself (144 nodes / 66k lines) is a
programme, not a wave, and is what "the AlgebraicCurve Jacobian layer" means — schedule the pair
behind it, not before it.

## 4. Risks

1. **`TateModule` is a `Subgroup`/`AddSubgroup` of `ℕ → M`**, so it is `AddSubgroup`-coerced to a
   type; the port's `Module ℤ_[p]` instance on it comes from mathlib's `Submodule`/`AddSubgroup`
   API plus the pin's own `smul_apply`/`natCast_padicInt_smul_apply` route. If the pin's instance
   route does not transpose (its `p2m_export` list suggests it is assembled by hand), that is the
   one place to expect adaptation.
2. The rank engine's `liftFun` is a `Classical.choose` over compatible systems; its `coe_liftAux_congr`
   / `liftFun_mem` lemmas are the proof-cost centre. They are 8–13 lines each at the pin.
3. `Module.Free`/`Module.Finite` from `Module.Basis` is mathlib-standard, but the pin's
   `basisOfCard` needs the `dvd_of_rel_apply` independence criterion in the exact `ℤ_[p]`
   `appr`/`toZModPow` form; `PadicInt.ext_of_toZModPow` is mathlib.

## 5. Not this set

The `jZero` Galois-representation node, which owns the 31 Galois-rep/Weierstrass declarations of the
same pin module; the two target headlines themselves; and `Pic0.abelJacobiCard_genus`.
