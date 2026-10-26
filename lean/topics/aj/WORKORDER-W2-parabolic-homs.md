# WORKORDER-W2 — the parabolic-hom / period-map layer

**Status: ready to dispatch** (two groups, below). Second wave of the aj subject; the plan is
[PLAN-W2-parabolic-homs.md](PLAN-W2-parabolic-homs.md), the landed predecessor
[WORKORDER-W1-stokes.md](WORKORDER-W1-stokes.md). **New files only** — no existing Lean module is
edited, no existing declaration promoted, nothing committed. Pin
`anthropics/fermats-last-theorem@aa2d8b3`; port mathlib `v4.34.0`.

Six pin nodes, **2,433 lines**, pairwise independent. All their premises are ported or mathlib, so each
of the six is a self-contained port (`frontier` `needed` = 1).

| order | module | headline | pin lines |
|---|---|---|---:|
| 1 | `FLTForHuman/ModularCurve/Period/ParabolicHomsBasis.lean` | `Period.exists_basis_parabolicHoms_of_isAddTorsionFree` | 273 |
| 2 | idem | `Period.exists_basis_parabolicHoms_castAddHom_comp` | 505 |
| 3 | idem | `Period.finrank_parabolicHoms_add_natCard_le_finrank_addMonoidHom_add_one` | 141 |
| 4 | `FLTForHuman/ModularCurve/Period/ParabolicHomsDetermination.lean` | `Period.existsUnique_isParabolicHom_sup_zpowers_neg_one_apply_eq` | 169 |
| 5 | idem | `Period.exists_parabolicHoms_int_castAddHom_comp_eq_of_forall_isOfFinOrder` | 886 |
| 6 | idem | `exists_exp_eq_of_invariant_ne_zero_isParabolicHom` | 410 |

## 1. The mathematics

`Period.parabolicHoms R Γ R` is the submodule of `Additive Γ →+ R` of the parabolic cocycles of `Γ`; it
is where `periodMapOf` lands, so it is the lattice the period map measures against.

* **1–3, basis and rank.** Over `ℤ` the module is free, and one basis serves every commutative
  torsion-free ring (1) and every characteristic-zero field (2), with coordinates agreeing under
  `Int.castAddHom`; (3) is the rank inequality relating `finrank (parabolicHoms K Γ K)` to
  `finrank (Γ →+ K)` through the number of `T`-orbits on the cosets `SL(2,ℤ) ⧸ Γ`.
* **4, the `±1` extension.** A parabolic hom on `Γ` extends uniquely to `Γ ⊔ ⟨−1⟩`.
* **5, determination by torsion.** A parabolic hom into `ZMod n` vanishing on every torsion element
  lifts to one into `ℤ`.
* **6, the analytic counterpart.** An invariant nowhere-zero `Φ` with cusp limits is `exp` of a
  primitive `L` whose period map is a parabolic hom — the analytic half, and the natural continuation of
  W1's ∂̄ layer.

## 2. Homing (fixed; do not rename)

Both modules join the port's existing subject directory `FLTForHuman/ModularCurve/Period/`:

* **`ParabolicHomsBasis.lean`** — nodes 1, 2, 3;
* **`ParabolicHomsDetermination.lean`** — nodes 4, 5, 6.

No new definition layer: `Period.parabolicHoms`, `IsParabolicHom`, `IsEquivariantPrimitive`,
`periodHom`, `period_mul`, `period_one`, `mem_parabolicHoms_iff` are ported in
`ModularForms/EichlerShimura/PeriodPrimitive.lean`; `periodAlongOf`, `periodOf`, `periodLatticeOf`,
`periodMapOf` and the `rfl` identification `periodMapOf_gamma0` in `.../PeriodOf.lean`;
`periodMapOf_mem_parabolicHoms` in `ModularCurve/Period/ParabolicHoms.lean`; the span and boundary
lemmas in `PeriodLatticeSpan.lean` / `PeriodLatticeBoundary.lean`.

**Overlap check (manager, before the proofs).** `twin_scan.py` marks all six statements `new` — none is
already in the port under another name — and the definitions above are the whole overlap, so the wave
adds no definitions. The nearest existing mathematics is the Eichler-integral route in
`ModularForms/EichlerShimura/PeriodMap.lean` (`exists_isEichlerIntegral` 655,
`isParabolicCocycle_cocycle_of_isEichlerIntegral` 786,
`exists_isEichlerIntegral_isParabolicCocycle` 878, `periodMap_injective` 1076) — read it before node 6.
The only duplication risk left is *private* helper re-derivation across the two new modules; the W1
tidy (eight helpers, 63 lines, moved into `Analysis/Complex/Dbar.lean`) is the precedent to avoid.
No `W2`/`aj`/`FLT` token in paths or names; helpers `private`; headlines public at their pin names.

## 3. The statements (verbatim; transcribe exactly)

### `FLTForHuman/ModularCurve/Period/ParabolicHomsBasis.lean`

`spec-pin:` `Theorems/Thm_ModularCurve_exists_basis_parabolicHoms_of_isAddTorsionFree.lean` and `P2M/Sol/S_ModularCurve_exists_basis_parabolicHoms_of_isAddTorsionFree.lean`

```lean
theorem ModularCurve.Period.exists_basis_parabolicHoms_of_isAddTorsionFree (Γ : Subgroup SL(2, ℤ))
    [Γ.FiniteIndex] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℤ (ModularCurve.Period.parabolicHoms ℤ Γ ℤ)),
      ∀ (R : Type*) [CommRing R] [IsAddTorsionFree R],
        ∃ bR : Module.Basis (Fin n) R (ModularCurve.Period.parabolicHoms R Γ R),
          ∀ i, (bR i : Additive Γ →+ R) = (Int.castAddHom R).comp (b i : Additive Γ →+ ℤ)
```

`spec-pin:` `Theorems/Thm_ModularCurve_exists_basis_parabolicHoms_castAddHom_comp.lean` and `P2M/Sol/S_ModularCurve_exists_basis_parabolicHoms_castAddHom_comp.lean`

```lean
theorem ModularCurve.Period.exists_basis_parabolicHoms_castAddHom_comp (Γ : Subgroup SL(2, ℤ))
    [Γ.FiniteIndex] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℤ (ModularCurve.Period.parabolicHoms ℤ Γ ℤ)),
      ∀ (K : Type*) [Field K] [CharZero K],
        ∃ bK : Module.Basis (Fin n) K (ModularCurve.Period.parabolicHoms K Γ K),
          ∀ i, (bK i : Additive Γ →+ K) = (Int.castAddHom K).comp (b i : Additive Γ →+ ℤ)
```

`spec-pin:` `Theorems/Thm_ModularCurve_finrank_parabolicHoms_add_natCard_le_finrank_addMonoidHom_add_one.lean` and `P2M/Sol/S_ModularCurve_finrank_parabolicHoms_add_natCard_le_finrank_addMonoidHom_add_one.lean`

```lean
theorem ModularCurve.Period.finrank_parabolicHoms_add_natCard_le_finrank_addMonoidHom_add_one
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Γ) (K : Type) [Field K] :
    Module.finrank K (ModularCurve.Period.parabolicHoms K Γ K) +
        Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers ModularGroup.T)
          (Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ Γ)) ≤
      Module.finrank K (Additive Γ →+ K) + 1
```

### `FLTForHuman/ModularCurve/Period/ParabolicHomsDetermination.lean`

`spec-pin:` `Theorems/Thm_ModularCurve_existsUnique_isParabolicHom_sup_zpowers_neg_one_apply_eq.lean` and `P2M/Sol/S_ModularCurve_existsUnique_isParabolicHom_sup_zpowers_neg_one_apply_eq.lean`

```lean
theorem ModularCurve.Period.existsUnique_isParabolicHom_sup_zpowers_neg_one_apply_eq
    (Γ : Subgroup SL(2, ℤ)) (A : Type*) [AddCommGroup A] (ψ : Additive Γ →+ A)
    (hψ : ModularCurve.Period.IsParabolicHom Γ ψ) :
    ∃! φ : Additive ↥(Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) →+ A,
      ModularCurve.Period.IsParabolicHom (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) φ ∧
        ∀ γ : Γ, φ (Additive.ofMul ⟨(γ : SL(2, ℤ)), Subgroup.mem_sup_left γ.2⟩) = ψ (Additive.ofMul γ)
```

`spec-pin:` `Theorems/Thm_ModularCurve_exists_parabolicHoms_int_castAddHom_comp_eq_of_forall_isOfFinOrder.lean` and `P2M/Sol/S_ModularCurve_exists_parabolicHoms_int_castAddHom_comp_eq_of_forall_isOfFinOrder.lean`

```lean
theorem ModularCurve.Period.exists_parabolicHoms_int_castAddHom_comp_eq_of_forall_isOfFinOrder
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (n : ℕ)
    (φ : ModularCurve.Period.parabolicHoms (ZMod n) Γ (ZMod n))
    (hφ : ∀ γ : Γ, IsOfFinOrder γ →
      (φ : Additive Γ →+ ZMod n) (Additive.ofMul γ) = 0) :
    ∃ x : ModularCurve.Period.parabolicHoms ℤ Γ ℤ,
      (Int.castAddHom (ZMod n)).comp (x : Additive Γ →+ ℤ) = (φ : Additive Γ →+ ZMod n)
```

`spec-pin:` `Theorems/Thm_ModularCurve_exists_exp_eq_of_invariant_ne_zero_isParabolicHom.lean` and `P2M/Sol/S_ModularCurve_exists_exp_eq_of_invariant_ne_zero_isParabolicHom.lean`

```lean
theorem ModularCurve.exists_exp_eq_of_invariant_ne_zero_isParabolicHom (Γ : Subgroup SL(2, ℤ))
    (Φ : ℂ → ℂ) (hΦ : ∀ τ : ℍ, ContDiffAt ℝ 1 Φ τ) (hne : ∀ τ : ℍ, Φ τ ≠ 0)
    (hinv : ∀ γ ∈ Γ, ∀ τ : ℍ, Φ ((γ • τ : ℍ) : ℂ) = Φ τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ c : ℂ, c ≠ 0 ∧
      Tendsto (fun τ : ℍ => Φ ((σ • τ : ℍ) : ℂ)) atImInfty (𝓝 c)) :
    ∃ (L : ℂ → ℂ) (m : Additive Γ →+ ℤ),
      ModularCurve.Period.IsParabolicHom Γ m ∧
        (∀ τ : ℍ, ContDiffAt ℝ 1 L τ) ∧
        (∀ τ : ℍ, HasFDerivAt L ((Φ τ)⁻¹ • fderiv ℝ Φ τ) τ) ∧
        (∀ τ : ℍ, Complex.exp (L τ) = Φ τ) ∧
        (∀ (γ : Γ) (τ : ℍ),
          L (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) = L τ + 2 * π * Complex.I * (m (Additive.ofMul γ) : ℂ)) ∧
        (∀ σ : SL(2, ℤ), ∃ c : ℂ,
          Tendsto (fun τ : ℍ => L ((σ • τ : ℍ) : ℂ)) atImInfty (𝓝 c))
```

## 4. Build discipline

* Edit loop `cd lean && flock .lake/flt_build.lock timeout 110 lake env lean -DautoImplicit=false <file>`;
  `timeout 110 lake build <Module>` when a file is done. **No whole-tree build.** Never raise
  `maxHeartbeats`/`maxRecDepth`.
* **A build-time blow-up is fixed, not reported**: split the proof into named `private` lemmas (W1's
  pattern — a 643-line node came out as 36 lemmas), factor the large case splits, replace monolithic
  `simp`/`gcongr` blocks by named intermediate facts. Keep `lake env lean` well inside the 110 s bound
  and report wall/CPU.
* Serial builds only (`flock`), 0 warnings per module, `set_option autoImplicit false`, log to
  `lean/tmp/w2-<module>.log`.

## 5. Do not edit existing modules

No existing Lean module edited, no declaration promoted. If a helper is `private` in a hub, re-derive it
locally as `private` and report it; if a promotion is genuinely required, stop and report.

## 6. Wiring — corrected after W1

Do **not** touch `SOURCES`/`PORT_FILES`: they live in the frozen `spec/old_check_stmts.py`, the playbook
§4 forbids adding to them, and their side effect is to exempt a module from `check_port.py`'s default
scan. The wiring is the header: two `spec-pin:` lines per headline (its `Theorems/` wrapper and its
`P2M/Sol/S_` copy). Check with
`timeout 110 python3 spec/check_port.py FLTForHuman/ModularCurve/Period/<Module>.lean` and require
`0 mismatch / 0 missing`; mutation-test each headline (perturb a hypothesis, expect a mismatch, revert,
verify the file hash).

## 7. Stop and report

If a statement cannot be matched without moving the pin's text; if a premise turns out unported (report
the real host); if a helper is genuinely needed publicly and is `private` in a hub; or if a build
exceeds its bound after splitting.

## 8. Completion report

Module paths and line counts; public/`private` counts; 0-warning confirmation with wall/CPU; the checker
result per module plus one mutation per headline; `#print axioms` per headline
(`[propext, Classical.choice, Quot.sound]`); `git status --porcelain` showing only this wave's files;
anything you could not match, quoted.

## 9. The two groups

* **G1** — `ParabolicHomsBasis.lean`, nodes 1, 2, 3; start immediately.
* **G2** — `ParabolicHomsDetermination.lean`, nodes 4, 5, 6; independent of G1, start immediately in
  parallel. Node 5 (886 lines) is the wave's largest proof and the one to split.

## 10. Outcome — W2 landed (manager-reviewed)

| module | group | lines | public | checker |
|---|---|---:|---:|---|
| `ModularCurve/Period/ParabolicHomsBasis.lean` | G1 | 974 | 3 | `3 ok / 0 mismatch / 0 missing` |
| `ModularCurve/Period/ParabolicHomsDetermination.lean` | G2 | 1,437 | 3 | `3 ok / 0 mismatch / 0 missing` |
| `ModularForms/EichlerShimura/PeriodHomParabolic.lean` | manager | 101 | 1 | `1 ok / 0 mismatch / 0 missing` |
| **total** | | **2,512** | **7** | **7 pin statements** |

Written ÷ pin = 1.03 (1,465 → 1,507 for G2; 919 → 974 for G1). `check_port.py --all` after the wave:
**5852 ok, 0 mismatch, 0 missing, 31 own, 0 kw, 269 modules** (before W2: 5845 / 266) — the delta is
exactly the six headlines plus the gap node below. `lake build` green on all three modules (3,792 jobs);
`#print axioms` clean on all six headlines; every mutation test caught, reverted, hash verified.

**Gap found and closed: `Period.IsEquivariantPrimitive.isParabolicHom_periodHom` was unported.** The
port carried only a `private`, Γ₀(N)-bundled special case, so `frontier` read the node as satisfied
(`needed = 1`) while it was missing — the `names` tier scans `private` declarations. G2 re-derived the
general statement privately for node 6; the manager lifted it into
`ModularForms/EichlerShimura/PeriodHomParabolic.lean`, public at the pin's qualified name, and G2's
copy is gone (the determination module now imports it). The frontier caveat and the **statement-
qualification lesson** (the checker is text-level: inside `namespace ModularCurve.Period` a statement
must still spell `ModularCurve.Period.IsParabolicHom …` as the pin does) are registered in the tools
(`tools/deps/README.md`, Notes and limits, and the `Frontier.tiers` docstring).

**G1's correction to §3.** The pin's wrapper and `S_` filenames carry a `Period_` segment
(`Theorems/Thm_ModularCurve_Period_<stem>.lean`), not the `Them_ModularCurve_<stem>` spelling used in
§3 above; G1 wired the real paths. §3's spelling is wrong for the parabolic-hom headlines — trust the
pin file names, not the pattern.

**Reuse wins (do not re-add).** G2 replaced ~130 pin lines of SL2 prelude with the ported public
`ModularGroup.exists_eq_conj_T_zpow_of_trace_sq_eq_four` and
`ModularGroup.PingPong.mem_center_iff_eq`; G1 dropped node 2's private `mem_parabolicHoms_iff` twin in
favour of the public one in `PeriodPrimitive.lean`, and derived the `Group.FG SL(2, ℤ)` instance once
from the ported `SpecialLinearGroup.SL2Z_generators` instead of the pin's `Γ(2)` bootstrap (~80 lines
saved).

**Open items — all three closed the same day (manager).**

1. **The touched legacy module is upgraded.** `ModularCurve/Period/ParabolicHoms.lean` now carries its
   `spec-pin:` pair, and its three helpers are public: `tendsto_vadd_atImInfty`,
   `const_eq_zero_of_tendsto_sub` and `period_eq_zero` — all
   three turned out to be **pin nodes** with `Theorems/` wrappers, i.e. three more nodes hidden behind
   `private`, which is the same blind spot as the `isParabolicHom_periodHom` gap below. Consequences:
   the module is now checked by the new checker instead of the frozen lists (its `PORT_FILES` row and
   its two `SOURCES` rows were deleted from `spec/old_check_stmts.py`, per the legacy rule that a
   touched module moves to the new wire), and it reports **4 ok / 0 mismatch**.
   `ModularForms/EichlerShimura/PeriodHomParabolic.lean` shrank from 103 to 61 lines: it now imports
   `ParabolicHoms` and cites `PeriodMapParabolicOf.period_eq_zero` instead of re-deriving the general
   conjugate-`T`-power lemma.
2. **The dead transcriptions are gone.** `tr_zero`, `evalBase_sub`, `evalBase_zsmul` were deleted from
   the determination module (10 lines); `tr_zsmul` stays — it is used.
3. **The crossed-hom prelude is homed.** [WORKORDER-W2b-crossed-hom.md](WORKORDER-W2b-crossed-hom.md):
   `namespace FreeProductCrossed` (745 lines, was `ParabolicHomsDetermination.lean:672–1416`) is now
   `FLTForHuman/GroupTheory/FreeProductCrossed.lean` — **841 lines, 73 declarations, 70 public / 3
   private**, moved verbatim (the diff is exactly the 70 dropped `private` keywords, machine-checked).
   `ParabolicHomsDetermination.lean` went **1,427 → 793** lines (the group-theory block out, `main`
   back in — see the layering paragraph below), with only the import, the removal, `main`'s
   re-insertion and one stale section comment as edits. Checker stays `3 ok / 0 mismatch / 0 missing`,
   axioms unchanged, both builds green at 0 warnings.

   **The group-theory module is diffed, and it exposed real drift.** The prelude's declarations are not
   graph *nodes* (no `Theorems/Thm_…` wrapper) but they *are* pinned statements, and the checker
   compares by normalised statement hash across the wire. Wiring the module to
   `P2M/Sol/S_ModularCurve_Period_exists_parabolicHoms_int_castAddHom_comp_eq_of_forall_isOfFinOrder.lean`
   (80 pin declarations in `namespace P2mKuroshTor`) gave **59 ok / 12 mismatch** on the first read. The
   twelve were transcription drift, not mathematics: binder `π` renamed to `pi`; `tP` renamed to
   `coprodT` (a pin declaration name used *inside* statements — my rename, reverted); `hker`/`hT` written
   as explicit hypotheses where the pin has section `variable`s; and two spellings (`S` vs
   `ModularGroup.S`, a parenthesised `trace`). All twelve are fixed: `π`/`hπ` restored, `tP` restored
   (my `coprodT` rename reverted — it renamed a pin name that occurs *inside* statements), the `Bridge`
   block restructured to the pin's `variable (ρ …) (hker …) (hT : ρ T = tP)` + `include` shape so
   `hker`/`hT` leave the statement text while keeping the parameter order `main` calls with, and the two
   spellings put right.

   The module now reads **71 ok / 0 mismatch / 0 missing, 0 own, 0 kw** — 745 lines, 72 declarations
   (71 public + `private trace_conj_T_zpow`, the one undiffed declaration, left private because only its
   in-module consumer uses it; the pin's copy is public, so promoting it would add a 72nd diffed
   statement). The delta to the pin's 80 `P2mKuroshTor` declarations is exactly the SL(2,ℤ) prelude the
   port replaced with already-ported public results (`PingPong.mem_center_iff_eq`,
   `exists_eq_conj_T_zpow_of_trace_sq_eq_four`), so 71/71 is full coverage of what the module states,
   not a partial wire. `check_port.py --all` after this: **5927 ok, 0 mismatch, 0 missing, 271 modules**
   — the prelude's 71 statements are now part of the port's diffed surface.

   The lesson is general: "no `Thm_` wrapper" says nothing about whether a statement is pinned — wire the
   prelude to its `S_` file and let the hash decide.

   The home exposed one layering defect, now being fixed: moving `main` verbatim made the
   `GroupTheory/` module import `ModularForms/EichlerShimura/PeriodPrimitive` for `parabolicHoms` in
   `main`'s statement — the group-theory → modular-forms inversion that
   `GroupTheory/ModularGroup/FreeProduct.lean`'s header objects to. `main` is modular-curve content
   (parabolic homomorphisms of `Γ`), so it moves back beside its only consumer and the new module ends
   up importing group theory only. Its remaining `FLTForHuman` imports are
   `GroupTheory.ModularGroup.FreeProduct` and `BassSerre.MinimalPeriod` (group theory) plus
   `ModularForms.ModularGroup` — *that* one is a pre-existing homing wart, since SL(2, ℤ) lives under
   `ModularForms/` although it is a group; the bridge `SL(2,ℤ) ↔ G23` genuinely belongs to group theory,
   so the block stays put and the wart is noted for a later homing pass. **Rule this sets for W3+:** a prelude's *engine* may be shared, but
   the statement that mentions the modular vocabulary stays in the modular layer — homing follows the
   statement, not the block it sat in.

`check_port.py --all` after items 1–2: **5856 ok, 0 mismatch, 0 missing, 270 modules** (the +4 is the
legacy module's headline plus its three promoted pin nodes). **Token sweep:** no `kw_`/`kwX`/`_kw`/`Kw`
and no pin-generated collision token in any declaration name across W1's five modules, W2's three, or
the upgraded legacy module; a comment citing the pin's `P2mKuroshTor` namespace is the only `P2m`. Short
conventional names were left alone (`Q` for a documented quotient, `tr`, `Θ`, `main`); `φ`/`η`/`tP` were
renamed to `bumpProfile`/`bumpKernel`/`coprodT` before that ruling, which is the rectification direction
and is green.
