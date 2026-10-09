# WORKORDER-W3b — equal Vélu-quotient `j` forces equal cyclic subgroups

**Status: ready to dispatch (2026-10-08).** The second half of story D, unblocked by the
refactor wave of the same day ([TOPIC-weierstrass-ready-shelf.md](TOPIC-weierstrass-ready-shelf.md)
§5.1). Its sibling, the `stepCurve` half, already landed as
[WORKORDER-W3-stepcurve.md](WORKORDER-W3-stepcurve.md). **One new module**, leaf. No existing
module is edited; no promotion, no definition-layer work (§0).

| order | module | headline | `S_` file |
|---|---|---|---|
| 1 | `FLTForHuman/WeierstrassCurve/Velu/CyclicQuotientJInjective.lean` | `WeierstrassCurve.zmultiples_eq_of_veluQuotient_j_eq_of_forall_isogenyEndDatum_exists_int` | `S_…_of_forall_isogenyEndDatum_exists_int.lean` (525) |

## 0. The collision that parked this node is gone — import both cones freely

The module needs premises from the `IsogenyEndDatum/Engine` cone *and* from the
`Velu/PointMapOddOrder` (hence `Velu/RestrictAlong`) cone, which were unimportable together
until the manager renamed `Velu/RestrictAlong.lean`'s character-free
`normFormulaAlong_of_elliptic` to **`normFormulaAlong_of_elliptic_cf`**. The reviewer probed
the full twelve-module union of this node's premise homes and it elaborates. **Read
`logs/deligne-serre-friction.md`, "Refactor wave (2026-10-08)", before choosing imports**, and
note: the copy to reuse for the pin's `normFormulaAlong_of_elliptic` helper is the **Engine**
one (`IsogenyEndDatum/Engine.lean:152`, the `[IsAlgClosed F] [CharZero F]`, `hsep`-free special
case), which is the statement the pin's own `S_` file re-proves; do not name the `_cf` copy.

Every definition the statement uses is public and ported:
`Def_WeierstrassCurve_Velu`, `…_OddOrderSummingSet`, `Def_Isogeny_ConditionalCurrency`,
`Def_WeierstrassCurve_GenusOnePlaceGateCentred` (the classes `GenusOnePlaceGate`,
`GenusOnePlaceGate.IsCentred` and `AbelTheorem` all live in
`WeierstrassCurve/GenusOnePlaceGate.lean`; the *statement* does not need
`GenusOnePlaceGateCentred.lean`, only the proof's `exists_genusOnePlaceGate_isCentred_and_abelTheorem`).

**Premise homes** (all public; the union is probe-verified importable):

| pin premise | port home |
|---|---|
| `Affine.IsogenyHomDatum.exists_pointHom_comp_eq_of_ker_le_of_isCentred` | `IsogenyEndDatum/Vocabulary.lean` |
| `exists_veluFunctionFieldHom_pointMapOfPushforward_ker_eq_zmultiples` | `Velu/PointMapOddOrder.lean` |
| `Affine.natCard_ker_pointMapOfPushforward_eq_finrankAlong` | `IsogenyEndDatum/Vocabulary.lean:161` |
| `Affine.pointMapOfPushforward_surjective` | `Isogeny/PointMapSurjective.lean:39` (namespace-qualified `WeierstrassCurve.Affine.…`) |
| `Affine.Point.exists_zsmul_eq_of_isAlgClosed` | `Elliptic/TorsionZMod.lean:164` |
| `card_torsionBy_eq_sq_of_isAlgClosed` | `Elliptic/TorsionCardLight.lean:49` |
| `Affine.IsogenyEndDatum.exists_pointEnd_eq_of_mem_isogenyEndSubring` | `IsogenyEndDatum/CharPolySquare.lean` |
| `nonempty_functionField_algEquiv_of_variableChange` | `Isogeny/VariableChangeAlgEquiv.lean` |
| `Affine.exists_genusOnePlaceGate_isCentred_and_abelTheorem` | `GenusOnePlaceGateCentred.lean` |
| `Affine.CoordinateRing.isDedekindDomain` | `Place/CoordinateRingDedekind.lean` |
| `Affine.hasPrincipalDivisors_functionField` | `PrincipalDivisors.lean` |
| `AlgebraicCurve.normFormulaAlong`, `Divisor.pushforwardAlong_pushforwardAlong`, `finiteAlong_comp`, `finiteAlong_of_surjective` | `AlgebraicCurve/WeilExchange/Transport.lean` |

*(Corrected at review, 2026-10-08.)* **Four premise rows of the table above were wrong** — the
implementer imported the real hosts and the module builds, so the homes here are now verified by
declaration grep: `natCard_ker_pointMapOfPushforward_eq_finrankAlong` is **not** in
`Isogeny/NatCard.lean` (whose docstring only re-exports the name), `pointMapOfPushforward_surjective`
is **not** there either (`NatCard` has only the `_of_separableAlong'` form), and
`exists_zsmul_eq_of_isAlgClosed` / `card_torsionBy_eq_sq_of_isAlgClosed` are in `Elliptic/`, not in
the `Isogeny` consumers. The reviewer's probe union did not include the three modules that turned
out to hold them (`Isogeny/PointMapSurjective.lean`, `Elliptic/TorsionZMod.lean`,
`Elliptic/TorsionCardLight.lean`), so the probe was necessary but not sufficient; the module's own
build over the actual hosts is the stronger evidence. Method note for next time: a `grep -l` for a
name finds *references*, not declarations — anchor on `^(optional modifiers) (theorem|lemma) <name>`
and remember namespace-qualified declarations (`theorem WeierstrassCurve.Affine.foo`) do not match
a `theorem foo` pattern.

**Transcribe the pin's linter suppressions, never its `maxHeartbeats`.** The pin sets
`autoImplicit false`, `linter.unusedVariables false` and `linter.unusedSectionVars false`
(its lines just after the attribute blocks); carry those three, and add nothing else. The
attribute scaffolding is not transcribed — none of its names is in the port's cone.

## 1. Source of truth

Pin `anthropics/fermats-last-theorem@aa2d8b3` at `~/proj/fermats-last-theorem` (read-only;
never modify). **Statement = the `Theorems/Thm_…` wrapper**, binders verbatim; proof = the
matching `P2M/Sol/S_…` file (525 lines; `cmm5_dp_natCard_ker_comp` at 39,
`normFormulaAlong_of_elliptic` 106, `charZero_addMonoidEnd_point` 127,
`intCast_addMonoidEnd_point_injective` 155, `kw_point_infinite` 162,
`kw_nat_card_ker_of_zsmul` 190, `kw_eq_zero_of_zsmul_eq_zero` 211,
`Pic0_pushforwardAlongHom_comp` 230, `pointMapOfPushforward_comp` 248,
`finrankAlong_eq_one_of_bijective` 273, `pointMapOfPushforward_injective_of_bijective` 287,
`kw_veluOddQuotientJInjOnCyclic_of_isogenyEndInt` 314, `solution` 510).

Public mirror, pinned:
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_zmultiples_eq_of_veluQuotient_j_eq_of_forall_isogenyEndDatum_exists_int.lean>.

## 2. The statement (verbatim from the wrapper)

```lean
theorem WeierstrassCurve.zmultiples_eq_of_veluQuotient_j_eq_of_forall_isogenyEndDatum_exists_int
    [DecidableEq (HahnSeries ℚ (AlgebraicClosure ℚ))] [CharZero (HahnSeries ℚ (AlgebraicClosure ℚ))]
    [IsAlgClosed (HahnSeries ℚ (AlgebraicClosure ℚ))]
    (W : WeierstrassCurve (HahnSeries ℚ (AlgebraicClosure ℚ))) [W.IsElliptic]
    [GenusOnePlaceGate W.toAffine] [GenusOnePlaceGate.IsCentred W.toAffine] [AbelTheorem W.toAffine]
    (hNs : ∀ D : IsogenyEndDatum W.toAffine, NormFormulaAlong (HahnSeries ℚ (AlgebraicClosure ℚ)) D.ι D.hfin)
    (hEnd : ∀ D : IsogenyEndDatum W.toAffine, ∃ m : ℤ, ∀ P : W.toAffine.Point, D.pointEnd (hNs D) P = m • P)
    (n : ℕ) (Q Q' : W.toAffine.Point)
    (hQ : addOrderOf Q = 2 * n + 1) (hQ' : addOrderOf Q' = 2 * n + 1)
    (hΔ : (W.veluQuotient (W.oddOrderSummingSet Q n)).Δ ≠ 0)
    (hΔ' : (W.veluQuotient (W.oddOrderSummingSet Q' n)).Δ ≠ 0)
    (hj : haveI : (W.veluQuotient (W.oddOrderSummingSet Q n)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
      haveI : (W.veluQuotient (W.oddOrderSummingSet Q' n)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ'⟩
      (W.veluQuotient (W.oddOrderSummingSet Q n)).j = (W.veluQuotient (W.oddOrderSummingSet Q' n)).j) :
    AddSubgroup.zmultiples Q = AddSubgroup.zmultiples Q'
```

Note the `hj` hypothesis carries two `haveI` *inside its statement* — transcribe them exactly;
they are statement text, not proof tactics, and they are the pin's own spelling.

Only this headline is public. The pin's twelve helpers stay `private` at the pin's leaf names
(`cmm5_dp_natCard_ker_comp`, the four substitution rows, `kw_*`, `Pic0_*`, `pointMapOf*`,
`finrankAlong_eq_one_of_bijective`).

## 3. Substitutions and route

`port_advise` reports **4 public port-identical rows, ≈93 lines not to re-prove**, all in this
file: `normFormulaAlong_of_elliptic` → `IsogenyEndDatum/Engine.lean` (see §0 — the Engine copy,
not `_cf`), `charZero_addMonoidEnd_point` and `intCast_addMonoidEnd_point_injective` →
`IsogenyEndDatum/CharPolySquare.lean`, `kw_point_infinite` → `Isogeny/NatCard.lean`. Import
them; do not transcribe the pin's copies. `port_plan`'s "blocks" section is these four alone
(100 lines, 4 declarations). There are **no** suspect `def`-`Prop` rows.

The two named risks in `port_advise`'s "generalise" section are the *known* two-copy pairs, both
resolved as above: `normFormulaAlong_of_elliptic` (Engine special vs RestrictAlong `_cf` general)
and `kw_point_infinite` (4 files, 2 statements — use `Isogeny/NatCard.lean`'s).

The engine is `kw_veluOddQuotientJInjOnCyclic_of_isogenyEndInt` (pin 314–509, ≈196 lines): over
the Hahn-series curve with every `IsogenyEndDatum` endomorphism an integer multiple, equal
`j`-invariants of the two odd Vélu quotients force the cyclic subgroups equal. The pin is on
Lean `v4.33.1` / mathlib `db584cd6`, the port on `v4.34.0`: expect drift
(`if_neg` → `ite_eq_right`, `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`, `dif_*` → `dite_eq_*`,
self-base-change not definitional) — see `porting-playbook.md` §7.

## 4. Build discipline

`lake env lean <file>` is the edit loop; `lake build <module>` when the file is done; **no
whole-tree build**. Bound everything:
`timeout 300 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>`,
`flock .lake/flt_build.lock timeout 300 lake build <module>`. Never raise
`maxHeartbeats`/`maxRecDepth`; on a timeout quarantine and bisect, and tell a blow-up from
contention by CPU time. Serial builds only. Do not commit. The module is a leaf.

The imports pull two large cones (`Engine` and `RestrictAlong`); a `lake env lean` on this
module may take a while before doing any work (a big `.olean` import cost). That is not a
blow-up — check CPU time.

## 5. The hub prohibition

**Do not edit any existing Lean module.** If a needed helper is `private` in a hub, re-derive it
locally as `private` in your module and report it. If a promotion seems genuinely required,
**stop and report** with the declaration, host, reason and
`python3 tools/deps/build_ladder.py --edit <host>` — the manager decides.

## 6. Wiring

In `lean/spec/check_flt_statements.py`, appending **last**: the target's
`Theorems/Thm_WeierstrassCurve_zmultiples_eq_of_veluQuotient_j_eq_of_forall_isogenyEndDatum_exists_int.lean`
and `P2M/Sol/S_WeierstrassCurve_zmultiples_eq_of_veluQuotient_j_eq_of_forall_isogenyEndDatum_exists_int.lean`
to `SOURCES`; `"FLTForHuman/WeierstrassCurve/Velu/CyclicQuotientJInjective.lean"` to
`PORT_FILES`.

Run the checker **as soon as the module is written** (text-only, no build). Baseline:
**7246 identical (313 promoted, 83 renamed), 0 mismatched, 0 missing, 37 own (7283 checked)**;
expected **+1** to 7247 with the headline as the whole public surface. Any other delta is
statement drift to fix before building. Target **0 mismatched, 0 missing**, then mutation-test
the headline and revert.

## 7. Stop and report

If the statement cannot be matched without moving the pin's text; if the union of premise
imports does not elaborate after all (it is probe-verified, so report the error verbatim rather
than routing around it); if a helper is genuinely needed publicly and is `private` in a hub; or
if a build exceeds its bound and bisecting does not settle it.

## 8. Completion report

Module path; public/`private` counts; tier-0 warning count (target **0**) and wall/CPU; tier-1
wall/CPU; which of the four substitution rows you imported and which you declined; every local
`private` re-derivation with its host; the checker before → after with the `identical` delta
reconciled and the mutation result; `#print axioms` for the headline
(`[propext, Classical.choice, Quot.sound]`); `git status --porcelain` showing only the set's
files; anything you could not match, quoted.

## 9. Outcome (2026-10-08, landed and manager-verified)

One new module, 468 lines, **1 public / 8 locally-declared `private`**; no existing Lean module
edited, no promotion, nothing committed.

| tier 0 | tier 1 | checker |
|---|---|---|
| 220.0 s wall / ≈181 s CPU, **0 warnings / 0 errors** | 234.3 s wall / ≈198 s CPU, exit 0 (9,055 jobs) | 7246 → **7247 identical**, 0 mismatched, 0 missing, 37 own (7284 checked) |

The `identical` delta is exactly the headline; no new exemption. One-token mutation
(`2 * n + 1` → `2 * n + 2` in `hQ`) gave 7246/1/0 with the diff printed, and the revert restored
the file's sha256 and 7247/0/0. `#print axioms`: `[propext, Classical.choice, Quot.sound]`.

The reviewer confirmed the headline is byte-for-byte the wrapper's **including the two `haveI`
binders inside the `hj` hypothesis**. All four substitution rows were imported (Engine's
`normFormulaAlong_of_elliptic`, not the `_cf` copy; `Ws13S7.charZero_addMonoidEnd_point` and
`Ws13S7.intCast_addMonoidEnd_point_injective` from `IsogenyEndDatum/CharPolySquare.lean`;
`Affine.kw_point_infinite` from `Isogeny/NatCard.lean`). The eight `private` helpers are the pin's
own `S_`-local machinery (`cmm5_dp_natCard_ker_comp`, `kw_nat_card_ker_of_zsmul`,
`kw_eq_zero_of_zsmul_eq_zero`, `Pic0_pushforwardAlongHom_comp`, `pointMapOfPushforward_comp`,
`finrankAlong_eq_one_of_bijective`, `pointMapOfPushforward_injective_of_bijective`,
`kw_veluOddQuotientJInjOnCyclic_of_isogenyEndInt`); the implementer audited them as having no
counterpart anywhere in the port, which the reviewer's spot check agrees with.

**Proof adaptations (no statement moved):** `AddMonoidHom.ker_restrict` → `ker_domRestrict`
(v4.34 deprecation); the pin's in-proof `haveI`/`letI` instance walls → `have`/`let` (Lean 4
registers the local instance either way, so the pin's three suppressions stay the only options);
`intCast_mem` resolves to mathlib's `Subring.intCast_mem`.

**This closes story D and the last ungated node on the `WeierstrassCurve` ready shelf.** Every
remaining shelf node is gated on the W4 definition wave, whose stages 2–4 are handed to a new
session ([WORKORDER-W4-definition-wave.md](WORKORDER-W4-definition-wave.md) §1a).
