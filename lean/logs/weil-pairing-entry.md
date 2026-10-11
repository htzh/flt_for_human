# Weil-pairing entry points (`IsWeilPairing` + `weilPairing0`)

The first two nodes of the Weil-pairing cone: the six-law interface on the
torsion of an elliptic curve, and the ad-hoc function-field construction
`weilPairing0`. Pin `anthropics/fermats-last-theorem@aa2d8b3`; port mathlib
`v4.34.0`. One set, one round, no subagent (well under the ≈1,000-line dispatch
threshold of [porting-playbook.md](../porting-playbook.md) §0.2).

## 1. Scope and measured cone

| pin file | lines | decls | ported |
|---|---|---|---|
| `Definitions/Def_GaloisRep_WeilPairing.lean` | 40 | 2 | whole node |
| `Definitions/Def_EllipticCurve_WeilPairingFun.lean` | 69 | 13 | whole node |
| `Definitions/Def_EllipticCurve_FunctionFieldPullback.lean` | 1,218 | ~90 | **partial** — the 9-decl slice `weilPairing0` consumes |

The second file is not a leaf: its `placeIdeal_of_ne_zero` and
`transEquiv_weilFun` statements name `placeOf` and `transEquiv`, both declared in
the 1,218-line `Def_EllipticCurve_FunctionFieldPullback.lean`, which the port did
**not** carry (a `grep` over `FLTForHuman/` for `placeOf`/`transEquiv`/`xc`/`yc`
found nothing; the nearest port analogues are `placeOfPoint`/`geomPlaceOfPoint`
and `translationAlgEquivOf` under different names and types).

## 2. What landed

| module | lines | decls | pin |
|---|---|---|---|
| `FLTForHuman/WeierstrassCurve/WeilPairing.lean` | 67 | 2 | `Def_GaloisRep_WeilPairing` |
| `FLTForHuman/WeierstrassCurve/WeilPairingFun.lean` | 109 | 13 | `Def_EllipticCurve_WeilPairingFun` |
| `FLTForHuman/WeierstrassCurve/Place/PointPlace.lean` | 95 | 9 | partial `Def_EllipticCurve_FunctionFieldPullback` |

Statements are the pin's verbatim (`--prop-bodies` not needed: no propositional
`def`); only proof bodies adapted (`dif_pos`/`dif_neg` → `dite_eq_left`/
`dite_eq_right`, mathlib `v4.34.0`).

**The two re-derivations inside `PointPlace.lean`.** `xc`/`yc`/`nonsingular_xc_yc`/
`eq_some_xc_yc` are transcribed verbatim. `placeOf` is built as
`CoordinateRing.heightOneSpectrumOfEquation (Point.nonsingular_xc_yc hP).left`
(the same `asIdeal`, via the port's dictionary) rather than the pin's inline
`HeightOneSpectrum` literal; `transEquiv` is `translationAlgEquivOf`
(`Velu/Engine.lean`) on `.some x y h` and `AlgEquiv.refl` at `0`, with the
`(W⁄K).IsElliptic` brick (`dsimp only [Affine.baseChange, WeierstrassCurve.baseChange];
infer_instance`) — the pin's route is `transPull`/`pointPull`/`pointHom`, not
transcribed. The `weilPairing0` proofs never unfold `transEquiv`, so the route
change is safe; the checker sees only the type.

## 3. Verification

| instrument | result |
|---|---|
| `spec/check_flt_statements.py` | **0 mismatched / 0 missing**; 7,626 identical (+24; one-token mutation on `mem_fibSet` → exactly 1 mismatched, reverted) |
| `spec/WeilPairingConsumer.lean` | **0 errors** (ZONE A derives `B P Q * B Q P = 1` from `add_left`/`add_right`/`alternate`; ZONE B composes `placeIdeal`/`fibSet`/`transEquiv_weilFun`/`weilPairing0_of_not`/`span_weilNum`) |
| `#print axioms` on `transEquiv_weilFun`, `weilPairing0_of_not` | `[propext, Classical.choice, Quot.sound]` |
| `lake build <module>` | 3.3 s + 2.7 s + 1.9 s; no `sorry` |

New `SOURCES`: `Def_EllipticCurve_FunctionFieldPullback`,
`Def_EllipticCurve_WeilPairingFun`, `Def_GaloisRep_WeilPairing`. New
`PORT_FILES`: the three modules above.

## 4. Plan vs actual, and carry-forward

Plan was "two def files, ≈110 lines". Actual 271 lines of module (95 of them the
prerequisite slice), because the second file is not self-contained. The
`Def_EllipticCurve_FunctionFieldPullback` surface behind `transEquiv`/`pointHom`
/`genericPoint`/`negPull`/`mulPull` is deferred and registered in
[CARRY-FORWARD.md](../CARRY-FORWARD.md) §Deferred API.

**Friction.** Two things only the build could tell: (a) `lake env lean` on
`WeilPairingFun.lean` reports `object file … PointPlace.olean does not exist`
until the prerequisite module is `lake build`-ed — the ladder's stale/missing
`.olean` trap, here expected on a fresh file; (b) `isElliptic_Δ_ne_zero` requires
`[W.IsElliptic]` at the *goal's* spelling, so `(W⁄K).IsElliptic` needs the
explicit brick before it can be used (playbook §6, instance keyed on a
semireducible `def`).

**Next.** The divisorial construction
(`Def_AlgebraicCurve_WeilPairingDivisorial`, `WeilDatum`, `WeilPairingData`) is
the expensive half; `frontier.py --target AlgebraicCurve.Pic0.exists_weilPairing`
prices it at 184 needed nodes / 78,444 raw `S_` lines.

## 5. Second node: `fibSet_finite` (2026-10-10)

Ported `WeierstrassCurve.Affine.fibSet_finite` (the `[n]`-fibre finiteness) into
`FLTForHuman/WeierstrassCurve/FibSetFinite.lean`, 89 lines, pin
`P2M/Sol/S_WeierstrassCurve_Affine_fibSet_finite.lean` + wrapper
`Theorems/Thm_WeierstrassCurve_Affine_fibSet_finite.lean`. It was the ready node
of the pairing cone (`needed = 1`), consuming `fibSet`/`mem_fibSet` and the landed
`card_torsion_of_isAlgClosed`. `torsion_finite` and `card_torsion_toFinset` are a
byte-identical prelude of **three** pin `S_` files (`fibSet_finite`,
`ncard_fibSet`, `valuation_weilNum`), so they are promoted here once, public;
`ncard_fibSet` (`needed = 2` → 1) and `valuation_weilNum` now import them.

Checker 7,630 identical (+4), 0 mismatched / 0 missing; `--prop-bodies` clean;
`spec/WeilPairingConsumer.lean` ZONE C green (0 errors); axioms
`[propext, Classical.choice, Quot.sound]`.

Scoped the next node, `WeierstrassCurve.exists_pairing_torsionBy`, in
[`topics/weilPairing/TOPIC-exists-pairing-torsionBy.md`](../topics/weilPairing/TOPIC-exists-pairing-torsionBy.md):
cone 43 nodes / 5,993 raw, needed 39 / 4,038, cut into four route groups. Its own
directory — not `deligneSerre/` — because the cone is `WeierstrassCurve.*` and the
Mazur/Ribet level-lowering column that consumes it is entirely unported and
unscoped. Two of its needed nodes (`valuation_mulPull_le_of_ne_zero`,
`zsmul_genericPoint_good`) are stated in the deferred
`Def_EllipticCurve_FunctionFieldPullback` vocabulary, so that node is a
prerequisite of the cone (CARRY-FORWARD §Deferred API).
