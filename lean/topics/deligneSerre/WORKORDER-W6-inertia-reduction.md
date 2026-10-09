# WORKORDER-W6 — the inertia-equivariant good-reduction map (Serre–Tate)

**Status: ready to dispatch (2026-10-08).** The second half of story C, ungated now that the W4
good-reduction definition wave is complete
([TOPIC-weierstrass-ready-shelf.md](TOPIC-weierstrass-ready-shelf.md) §3;
[WORKORDER-W4-definition-wave.md](WORKORDER-W4-definition-wave.md) §6). **One new module**, leaf.
No existing module is edited; no promotion, no definition-layer work.

| order | module | headline | `S_` file |
|---|---|---|---|
| 1 | `FLTForHuman/WeierstrassCurve/Reduction/InertiaReduction.lean` | `WeierstrassCurve.exists_inertia_equivariant_reduction_of_variableChange_eq_map` | `S_…_of_variableChange_eq_map.lean` (601) |

The sibling half, reduction surjectivity (185 lines), is
[WORKORDER-W5](WORKORDER-W5-reducehom-surjective.md) and lands first; `port_advise` reports **no
shared prelude and no substitution** between the two.

## 0. The definition layer is in — build on it, do not re-prove it

Every definition the statement and proof use is public and ported. Premise homes (verified by
declaration grep):

| pin premise | port home |
|---|---|
| `VariableChange`, `VariableChange.map`, `VariableChange.smul` | mathlib `Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange` |
| `Affine.Point.vcInvFun` (`Def_WeierstrassCurve_VariableChangePointEquiv` half) | `WeierstrassCurve/Velu/Equivariance.lean:154` |
| `Affine.Point.vcInvFun_add` (`Thm_…_Affine_Point_vcInvFun_add`) | `WeierstrassCurve/Velu/VariableChangePoint.lean:202` |
| `reducePoint`, `reducePoint_some_of_mem`, `reducePoint_some_of_notMem` | `WeierstrassCurve/Reduction/Point.lean` |
| `reduceHom` | `WeierstrassCurve/Reduction/ReduceHom.lean` |
| `ZeroComponentReduction`'s `SmoothLocusReductionData`, `reducePointSmooth`, `mem_zeroComponentSubgroup_iff` | `WeierstrassCurve/Reduction/ZeroComponent.lean` |
| `A.decompositionSubgroup`, `A.inertiaSubgroup` | mathlib `RingTheory.Valuation.RamificationGroup` |
| `IsLocalRing.ResidueField`, `residue` | mathlib `RingTheory.Valuation.LocalSubring` |

`port_advise` reports **no substitution and no shared prelude**; the one name it matches is the
pin's `some_congr` (S_ line 39) against the port's **`private`** `some_congr` in
`Reduction/Point.lean` — a hub-private helper, so **re-derive it locally `private`**; do not
promote it.

**Transcribe the pin's linter suppressions, never its `maxHeartbeats`.** The pin's `S_` file sets
`autoImplicit false`; carry that. Do **not** transcribe the `attribute [-instance]`/`[-simp]`
scaffolding — none of its names is in the port's cone. The wrapper's is large and mentions
`galoisRep_apply`/`galoisRepModuleEnd_apply`; those are scaffolding, not premises of the proof.

## 1. Source of truth

Pin `anthropics/fermats-last-theorem@aa2d8b3` at `~/proj/fermats-last-theorem` (read-only; never
modify). **Statement = the `Theorems/Thm_…` wrapper**, binders verbatim; proof = the matching
`P2M/Sol/S_…` file (601 lines). The `S_` file is organised as sections, all private machinery in
`namespace P2MKcSerreTate`:

| section | declarations (pin line) |
|---|---|
| Cast | `castPt` 19, `castPt_some` 26, `castPt_rfl` 29, `heq_castPt` 32, `castPt_eq_zero_iff` 35, `some_congr` 39, `heq_some_of_eq` 44, `heq_zero_of_eq` 49, `castPt_add` 55, `castAddHom` 59 |
| Coord | `vcXInv_mul` 73, `vcYInv_mul` 81, `map_vcXInv` 91, `map_vcYInv` 96 |
| IntegralCoord | `coe_map_u` 107, `coe_map_u_inv` 110, `vcXInv_map_subtype` 114, `vcYInv_map_subtype` 118, `vcXInv_mem_iff` 123, `vcYInv_mem` 134, `residue_vcXInv` 141, `residue_vcYInv` 155 |
| IntegralChange | `coe_notMem_nonunits_of_isUnit` 176, `pow_mem_nonunits` 180, `mem_of_sq_add_mul_eq` 190, `exists_map_subtype_eq_of_smul_eq` 203 |
| Conj | `decompRingHom` 348, `subtype_comp_decompRingHom` 354, `residue_comp_decompRingHom` 358, `conj` 366, `conj_map_subtype` 369, `conj_map_residue` 373, `isUnit_conj_Δ` 378 |
| Main | `vcInvAddHom` 390, `vcInvFun_some` 399, `VariableChange.map_mul'` 404, `VariableChange.map_inv'` 408, `baseChange_map_algEquiv` 414, `cocycle_smul_conj` 419, `heq_reducePoint_of_inertia` 426, `exists_inertia_equivariant_reduction` 463, `solution` 580 |

Public mirror, pinned:
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_exists_inertia_equivariant_reduction_of_variableChange_eq_map.lean>.

## 2. The statement (verbatim from the wrapper)

```lean
universe u v in
theorem WeierstrassCurve.exists_inertia_equivariant_reduction_of_variableChange_eq_map
    {F : Type u} {M : Type v} [Field F] [Field M] [DecidableEq M] [Algebra F M]
    (A : ValuationSubring M) [DecidableEq (ResidueField A)]
    (E : WeierstrassCurve F) (W : WeierstrassCurve A) (κ : VariableChange M)
    (hκ : κ • E.baseChange M = W.map A.subtype) (hΔ : IsUnit W.Δ) :
    ∃ (θ : (E.baseChange M).toAffine.Point →+ (W.map (residue A)).toAffine.Point)
      (g : (M ≃ₐ[F] M) → VariableChange A),
      (∀ (n : ℕ) (P : (E.baseChange M).toAffine.Point),
          (n : ResidueField A) ≠ 0 → n • P = 0 → θ P = 0 → P = 0) ∧
      (∀ (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F),
          (⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F →
          (g σ).map A.subtype = κ * (κ.map (σ : M →+* M))⁻¹ ∧
          (g σ).map (residue A) • W.map (residue A) = W.map (residue A) ∧
          ∀ P : (E.baseChange M).toAffine.Point,
            HEq (Point.vcInvFun ((g σ).map (residue A)) (W.map (residue A)).toAffine (θ P))
              (θ (Point.map (σ : M →ₐ[F] M) P))) ∧
      (∀ (σ τ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F)
          (hτ : τ ∈ A.decompositionSubgroup F),
          (⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F →
          (⟨τ, hτ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F →
          (g (σ * τ)).map (residue A) = (g σ).map (residue A) * (g τ).map (residue A)) :=
```

The `universe u v in` prefix and the `HEq` are **statement text** — transcribe them exactly.
Only this headline is public; the pin's helpers stay `private` under a `private`-marked
`P2MKcSerreTate` namespace (mark each declaration `private`; keep the section structure).

## 3. Route and recorded negatives

This is a public-surface transcription of ≈601 lines. The pin builds `θ` and the cocycle `g` in
`exists_inertia_equivariant_reduction` (pin 463–573, ≈110 lines) from the helper blocks above:
`Conj` conjugates `W` by the decomposition action, `IntegralChange` produces the variable change
carrying `W` to its conjugate over `A`, and `Main` assembles `θ` as the additive map on points and
proves the inertia-equivariance, injectivity on the prime-to-`p` part and the cocycle identity.

Every premise is ported (§0), so the route is fixed; do not re-plan it.

The pin is Lean `v4.33.1` / mathlib `db584cd6`, the port `v4.34.0`. Expect drift — see
`porting-playbook.md` §7. Known in point:

* **Self-base-change is not definitional in `v4.34.0`.** The statement's `κ • E.baseChange M =
  W.map A.subtype` and the proof's `baseChange_map_algEquiv` / `cocycle_smul_conj` move between
  `(E.baseChange M)` and `E.baseChange M` spellings; carry the `have hb : … = … := rfl`-style
  bridge the way `WeierstrassCurve/Velu/CyclicCount.lean` does, and read that file first.
* **`Affine.Point.vcInvFun` is `Point.vcInvFun` in the port** (`Velu/Equivariance.lean`), with a
  different argument order from any mathlib spelling: use the port's.
* `Affine.Point.some_ne_zero`, `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`, `if_*` → `ite_*`,
  `dif_*` → `dite_eq_*` as applicable.
* `VariableChange.map_mul`/`map_inv` — the pin re-proves them as `map_mul'`/`map_inv'`; check
  whether mathlib `v4.34.0` now supplies them before transcribing the re-proofs (the pin's names
  must stay if you keep them, since they are part of the compared surface only if public — they
  are not, so rename freely and stay `private`).

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
checker feedback, run a private copy: `cp spec/check_flt_statements.py spec/_probe_w6.py` (W5 uses
`_probe_w5.py`, so the two never collide), append to that copy the target's
`Theorems/Thm_WeierstrassCurve_exists_inertia_equivariant_reduction_of_variableChange_eq_map.lean`
and `P2M/Sol/S_WeierstrassCurve_exists_inertia_equivariant_reduction_of_variableChange_eq_map.lean`
to `SOURCES`, and `"FLTForHuman/WeierstrassCurve/Reduction/InertiaReduction.lean"` to
`PORT_FILES`; run `python3 spec/_probe_w6.py`; delete the copy when done. (The checker resolves
the pin clone from `--flt` and the port files from its own directory, so a copy in `spec/` behaves
identically.)

Run the probe **as soon as the module is written** (text-only, no build). Baseline:
**7368 identical, 0 mismatched, 0 missing, 37 own (7405 checked)** (W5's row is not in your copy);
expected **+1** to 7369 with the headline as the whole public surface. Any other delta is
statement drift to fix before building. Target **0 mismatched, 0 missing**, then mutation-test
the headline (drop the `[DecidableEq (ResidueField A)]` binder or flip `HEq` to `=`) in the probe
and revert.

## 7. Stop and report

If the statement cannot be matched without moving the pin's text (in particular the
`universe u v in` prefix or the `HEq`); if a premise home in §0 is wrong (report the real host, do
not route around it); if a helper is genuinely needed publicly and is `private` in a hub; or if a
build exceeds its bound and bisecting does not settle it.

## 8. Completion report

Module path and line count; public/`private` counts; tier-0 warning count (target **0**) and
wall/CPU; tier-1 wall/CPU; every local `private` re-derivation with its host; the checker before →
after with the `identical` delta reconciled and the mutation result; `#print axioms` for the
headline (`[propext, Classical.choice, Quot.sound]`); `git status --porcelain` showing only the
set's files; anything you could not match, quoted.

## 9. Outcome (2026-10-08, landed; manager-wired and verified)

One new module, **630 lines**, **1 public / 45 `private`** in `namespace P2MKcSerreTate` (sections
Cast/Coord/IntegralCoord/IntegralChange/Conj/Main preserved); no existing Lean module edited;
nothing committed. Imports: `WeierstrassCurve/Reduction/ZeroComponent.lean` +
`WeierstrassCurve/Velu/VariableChangePoint.lean`.

| tier 0 | tier 1 | checker (private probe) |
|---|---|---|
| **0 warnings** | module built (8.0 s) | 7368 → **7369 identical**, 0 mismatched, 0 missing, 37 own (7406 checked) |

The `identical` delta is exactly the headline. Two mutations were caught and reverted
(drop `[DecidableEq (ResidueField A)]`; flip `HEq` to `Eq`), each 7368/1/0 — so the binder and the
`HEq` really are on the compared surface. `#print axioms`:
`[propext, Classical.choice, Quot.sound]`. The only hub-private collision, the pin's `some_congr`
(host `Reduction/Point.lean:37`), was **re-derived `private`**; no promotion. Body adaptations
only: `dif_pos` → `dite_eq_left`, and the pin's explicit `K` argument to
`ValuationSubring.smul_mem_of_mem_decompositionSubgroup` is dropped (the port carries it as an
implicit variable). No self-base-change bridge was needed — the port's `Affine`/`toAffine` are
`abbrev`s, so `baseChange_map_algEquiv` transcribes unchanged. The manager appended the two
`SOURCES` rows and the `PORT_FILES` row; the combined checker then read **7370 identical, 0/0**
and the milestone whole-tree build was green (9,359 jobs).
