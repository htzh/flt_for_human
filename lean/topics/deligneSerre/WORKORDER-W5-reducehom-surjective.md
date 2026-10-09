# WORKORDER-W5 — reduction is surjective on prime-to-`p` torsion

**Status: ready to dispatch (2026-10-08).** The first half of story C, ungated now that the W4
good-reduction definition wave is complete
([TOPIC-weierstrass-ready-shelf.md](TOPIC-weierstrass-ready-shelf.md) §3;
[WORKORDER-W4-definition-wave.md](WORKORDER-W4-definition-wave.md) §6). **One new module**, leaf.
No existing module is edited; no promotion, no definition-layer work.

| order | module | headline | `S_` file |
|---|---|---|---|
| 1 | `FLTForHuman/WeierstrassCurve/Reduction/ReduceHomSurjective.lean` | `WeierstrassCurve.exists_reduceHom_eq_of_nsmul_eq_zero_of_natCast_ne_zero` | `S_…_of_natCast_ne_zero.lean` (185) |

The sibling half, the inertia-equivariant reduction (601 lines), is
[WORKORDER-W6](WORKORDER-W6-inertia-reduction.md) and is dispatched after this set is reviewed.
`port_advise` reports **no shared prelude and no substitution** between the two — they are
independent.

## 0. The definition layer is in — build on it, do not re-prove it

Every definition the statement and proof use is public and ported. Premise homes (verified by
declaration grep):

| pin premise | port home |
|---|---|
| `reduceHom`, `reducePoint`, `reducePoint_some_of_mem` | `WeierstrassCurve/Reduction/ReduceHom.lean`, `…/Point.lean` |
| `Affine.X_mem_of_nsmul_eq_zero'` | `WeierstrassCurve/Reduction/TorsionIntegral.lean` |
| `map_residue_Δ_ne_zero_iff` | `WeierstrassCurve/Reduction/Point.lean` |
| `nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed` | `Elliptic/TorsionZMod.lean:180` |

**Transcribe the pin's linter suppressions, never its `maxHeartbeats`.** The pin's `S_` file sets
`autoImplicit false`; carry that. Do **not** transcribe the `attribute [-instance]`/`[-simp]`
scaffolding — none of its names is in the port's cone.

## 1. Source of truth

Pin `anthropics/fermats-last-theorem@aa2d8b3` at `~/proj/fermats-last-theorem` (read-only; never
modify). **Statement = the `Theorems/Thm_…` wrapper**, binders verbatim; proof = the matching
`P2M/Sol/S_…` file (185 lines).

Declaration lines in the `S_` file: `reduceHom_injOn'` 16, `mapPointFun` 46, `mapPointFun_add` 51,
`mapPointHom` 72, `mapPointHom_injective` 78, `torsionMap` 90, `torsionMap_injective` 97, `main`
106, `solution` 176.

Public mirror, pinned:
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_exists_reduceHom_eq_of_nsmul_eq_zero_of_natCast_ne_zero.lean>.

## 2. The statement (verbatim from the wrapper)

```lean
theorem WeierstrassCurve.exists_reduceHom_eq_of_nsmul_eq_zero_of_natCast_ne_zero
    {L : Type*} [Field L] [DecidableEq L] [IsAlgClosed L] [CharZero L]
    (A : ValuationSubring L) [DecidableEq (ResidueField A)]
    (W : WeierstrassCurve A) (hΔ : (W.map (residue A)).Δ ≠ 0)
    {ℓ : ℕ} (hℓ : (ℓ : ResidueField A) ≠ 0)
    (Q₀ : (W.map (residue A)).toAffine.Point) (hQ₀ : ℓ • Q₀ = 0) :
    ∃ Q : (W.map A.subtype).toAffine.Point, ℓ • Q = 0 ∧ reduceHom hΔ Q = Q₀
```

Only this headline is public, at its pin name in `namespace WeierstrassCurve` (the `S_` file's
`solution` lives under `P2MW.S_…`; the wrapper is the authority). The pin's eight helpers stay
`private` at the pin's leaf names (`reduceHom_injOn'`, `mapPointFun`, `mapPointFun_add`,
`mapPointHom`, `mapPointHom_injective`, `torsionMap`, `torsionMap_injective`, `main`). No
`def`-valued helper needs to be public.

## 3. Route and recorded negatives

This is a public-surface transcription. The engine is `main` (pin 106–172, ≈67 lines): the
reduction map is injective on `ℓ`-torsion (`reduceHom_injOn'`, via
`X_mem_of_nsmul_eq_zero'` + `reducePoint_some_of_mem`), and a cardinality comparison of the
`ℓ`-torsion of `W` and of the residue curve lifted along the algebraic closure
(`torsionMap`, `mapPointHom`) forces surjectivity. Every premise is ported (§0), so the route is
fixed; do not re-plan it.

The pin is Lean `v4.33.1` / mathlib `db584cd6`, the port `v4.34.0`. Expect drift — see
`porting-playbook.md` §7. Known in point:

* `Affine.Point.some_ne_zero` — the pin uses it in `reduceHom_injOn'`, `mapPointHom_injective`
  and `torsionMap_injective`; use whatever the port's own modules use for the same fact (some
  port files call `Affine.Point.some_ne_zero`, others `cases` on the equality).
* `Submodule.mem_torsionBy_iff` may take explicit arguments in `v4.34.0`; `Nat.card_zmod` no
  longer needs a `NeZero` hypothesis.
* `Nat.finite_of_card_ne_zero`, `Nat.card_congr`, `natCast_zsmul`, `isUnit_iff_ne_zero`,
  `WeierstrassCurve.map_Δ` — check the direction/spelling at the call site.

## 4. Build discipline

`lake env lean <file>` is the edit loop; `lake build <module>` when the file is done; **no
whole-tree build**. Bound everything:
`timeout 300 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>`,
`flock .lake/flt_build.lock timeout 300 lake build <module>`. Never raise
`maxHeartbeats`/`maxRecDepth`; on a timeout quarantine and bisect, and tell a blow-up from
contention by CPU time. Serial builds only. Do not commit. The module is a leaf.

## 5. The hub prohibition

**Do not edit any existing Lean module.** If a needed helper is `private` in a hub, re-derive it
locally as `private` in your module and report it. If a promotion seems genuinely required,
**stop and report** with the declaration, host, reason and
`python3 tools/deps/build_ladder.py --edit <host>` — the manager decides.

## 6. Wiring — verify with a private probe; the manager wires the shared file

This wave dispatches W5 and W6 in parallel, so **do not edit the shared
`lean/spec/check_flt_statements.py`** — the manager appends both sets' rows at review. For full
checker feedback, run a private copy: `cp spec/check_flt_statements.py spec/_probe_w5.py` (W6 uses
`_probe_w6.py`, so the two never collide), append to that copy the target's
`Theorems/Thm_WeierstrassCurve_exists_reduceHom_eq_of_nsmul_eq_zero_of_natCast_ne_zero.lean` and
`P2M/Sol/S_WeierstrassCurve_exists_reduceHom_eq_of_nsmul_eq_zero_of_natCast_ne_zero.lean` to
`SOURCES`, and `"FLTForHuman/WeierstrassCurve/Reduction/ReduceHomSurjective.lean"` to
`PORT_FILES`; run `python3 spec/_probe_w5.py`; delete the copy when done. (The checker resolves
the pin clone from `--flt` and the port files from its own directory, so a copy in `spec/` behaves
identically.)

Run the probe **as soon as the module is written** (text-only, no build). Baseline:
**7368 identical (313 promoted, 83 renamed), 0 mismatched, 0 missing, 37 own (7405 checked)**;
expected **+1** to 7369 with the headline as the whole public surface. Any other delta is
statement drift to fix before building. Target **0 mismatched, 0 missing**, then mutation-test
the headline (`ℓ • Q = 0` → `ℓ + 1 • Q = 0`) in the probe and revert.

## 7. Stop and report

If the statement cannot be matched without moving the pin's text; if a premise home in §0 is
wrong (report the real host, do not route around it); if a helper is genuinely needed publicly
and is `private` in a hub; or if a build exceeds its bound and bisecting does not settle it.

## 8. Completion report

Module path; public/`private` counts; tier-0 warning count (target **0**) and wall/CPU; tier-1
wall/CPU; every local `private` re-derivation with its host; the checker before → after with the
`identical` delta reconciled and the mutation result; `#print axioms` for the headline
(`[propext, Classical.choice, Quot.sound]`); `git status --porcelain` showing only the set's
files; anything you could not match, quoted.

## 9. Outcome (2026-10-08, landed; manager-wired and verified)

One new module, **217 lines**, **1 public / 8 `private`**; no existing Lean module edited, no
promotion, no hub edit, nothing committed. Imports: `Elliptic/TorsionZMod` +
`WeierstrassCurve/Reduction/ReduceHom.lean`.

| tier 0 | tier 1 | checker |
|---|---|---|
| exit 0, **0 warnings** (needed only `linter.style.haveILetI false`, for the pin's verbatim `haveI`/`letI`) | module built (75 s) | 7368 → **7369 identical**, 0 mismatched, 0 missing, 37 own (7406 checked) |

The `identical` delta is exactly the headline; one-token mutation (`ℓ • Q = 0` → `ℓ + 1 • Q = 0`)
gave 7368/1/0 and the revert restored 7369/0/0. `#print axioms`:
`[propext, Classical.choice, Quot.sound]`. Drift handled at the call site only: the pin's
now-unneeded `NeZero ℓ` block before `Nat.card_zmod` was dropped, and `Affine.Point.some_ne_zero`
is the port's one-argument form. The manager appended the two `SOURCES` rows (wrapper + `S_` file)
and the `PORT_FILES` row to `spec/check_flt_statements.py` and re-confirmed 7369/0/0.
