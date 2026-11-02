# WORKORDER-AF5-rightconv-regularity — the right-convolution operator's regularity, one module, one headline

**Status (closed 2026-11-02): landed and reviewed green.** One worker dispatch, one new module,
**one public headline**, no blocker at any point:

| step | module (Δ lines) | checker | build | axioms |
|---|---|---:|---|---|
| W1 | `Adelic/RightConvRegularity.lean` (**new, 530**: header 52 + 8 imports + 27 `private` + 1 public) | **1 ok** / 0 / 0 | silent, 5.6 s fresh (olean deleted), zero warnings | clean |

`dedup --within` 0 clusters on 28 declarations; `move_dead --dry-run` reports 2 declarations / 5 lines
that are **all** a tool false positive (`private abbrev instNG`/`instNS` + their two
`attribute [local instance]` lines — load-bearing, kept, nothing moved; FR-0104); consumer zone C
appended (4 → 9 examples, 3 zones) at 0 errors; nothing frozen was edited. `set_option
maxHeartbeats` was not needed (the 4M global is untouched), and no mathlib rename was required —
v4.34's `ContDiff` exponent change (`ℕ∞ω`) lands the pin's `(⊤ : ℕ∞)` by coercion. The four measured
deviations — the `haveILetI` linter option, the explicit `R :=` in `glArch_unipotent`/`glFin_unipotent`
(FR-0105), the empty rename list, and the `open scoped Classical` a `mixedSpace` consumer now needs —
are recorded in [SET-AF5.md](SET-AF5.md) §1.6, together with the exact-forecast re-read. The original
order follows unedited as the record of what was asked.

**Status as issued (2026-11-02): the ground is landed and frozen; the proof body is this order.**
Scope: [SET-AF5.md](SET-AF5.md) — read it once before starting; §0.4 and §1.5 are why this order exists
in the shape it does. The set's other two rows are **already landed by the manager** and must not be
re-proved, re-stated or moved (§1 below).

**Audience.** A fresh coding session. Method: [porting-playbook.md](../../porting-playbook.md) §3–§5;
wire: the per-module protocol — a `spec-pin:` header, `spec/check_port.py`, no in-source
per-declaration marker. Pin clone `/home/haitao/proj/fermats-last-theorem`, pinned `aa2d8b3`.

**One new file, one public headline, 471 raw pin lines / 450 net.** The row is a *single* development:
a generic dominated-convergence/`ContDiff` shape block, an adèlic slice that makes the integrand affine
in `z`, and the `ε/δ` continuity estimate in `g`. Nothing is imported from a sibling port module
beyond the four already in the tree (§2). Log every build in `lean/tmp/`. Report a blocker as soon as
one appears (§6); never leave a `sorry` in the tree.

## 1. What the ground gives you (frozen API — do not edit these modules)

| declaration | module | statement you will call |
|---|---|---|
| `AutomorphicForm.continuous_unipotentGL2` | `AutomorphicForm/Adelic/ConstantTerm.lean` | **general in `R`**: `{R} [CommRing R] [TopologicalSpace R] [ContinuousNeg R] : Continuous fun x : R => AutomorphicForm.unipotentGL2 x` |
| `AutomorphicForm.rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply` | `AutomorphicForm/Adelic/RightConvolution.lean` | `rightConv K φ f (g * t) = rightConv K φ (fun y => f (t⁻¹ * y)) g` |
| `AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn` | `AutomorphicForm/Adelic/TestFnTop.lean` | `Continuous f ∧ HasCompactSupport f` from `IsFactorizableTestFn K f` |
| `rightConv`, `rightConv_apply` | `AutomorphicForm/Adelic/RightConvolution.lean` | the unfolding (`rfl`) |
| `AutomorphicForm.unipotentGL2{,Hom,_coe,_zero,_add}` | `AutomorphicForm/Adelic/ConstantTerm.lean` | the embedding at `R := AdeleRing (𝓞 K) K` |
| `archEntries`, `archEntries_apply`, `IsFactorizableTestFn`, `IsArchTestFactor`, `IsFinTestFactor` | `AutomorphicForm/Adelic/FactorizableTestFn.lean` | the `f = fa · ff` decomposition |
| `AdelicLevel.glArch`, `glFin`, `continuous_glArch`, `continuous_glFin` | `NumberTheory/AdelicLevel/Projections.lean` | the two projections |
| `AdelicBox.continuous_ringEquiv_mixedSpace` | `NumberTheory/AdelicBox.lean` | continuity of `InfiniteAdeleRing.ringEquiv_mixedSpace` |
| `AdelicHaar.glBorel`, `borelSpace_glBorel`, `isHaarMeasure_adelicGLHaar`, `isMulRightInvariant_adelicGLHaar` | `NumberTheory/AdelicHaar/GeneralLinear.lean` | the measurable structure and the measure |

**Do not re-prove `continuous_unipotentGL2` or the translation law.** They are landed, checked against
their `Thm_` wrappers (`ok`), axiom-clean, and their three former specialised copies are gone —
`continuous_unipotentGL2_adele`, `continuous_unipotentGL2'` and a `private continuous_unipotentGL2` no
longer exist. Use `continuous_unipotentGL2 (R := AdeleRing (𝓞 K) K)`.

## 2. Scope — one module, one headline

`FLTForHuman/AutomorphicForm/Adelic/RightConvRegularity.lean` (**new**, 0 importers, cascade-free).

Imports (fix this list; add nothing else):

```lean
import FLTForHuman.AutomorphicForm.Adelic.RightConvolution
import FLTForHuman.AutomorphicForm.Adelic.FactorizableTestFn
import FLTForHuman.AutomorphicForm.Adelic.TestFnTop
import FLTForHuman.AutomorphicForm.Adelic.ConstantTerm
import FLTForHuman.AutomorphicForm.Adelic.Basic
import FLTForHuman.NumberTheory.AdelicBox
import FLTForHuman.NumberTheory.AdelicLevel.Projections
import FLTForHuman.NumberTheory.AdelicHaar.GeneralLinear
```

Header: a `/- … -/` block (a `--` line mis-aligns the checker's namespace tracker), the subject
sentence, and exactly two wires:

```
spec-pin: Theorems/Thm_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn.lean
spec-pin: P2M/Sol/S_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn.lean
```

**The headline** — the wrapper's statement verbatim (it goes public, at the pin's name, in
`namespace AutomorphicForm`):

```lean
theorem AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn
    (K : Type) [Field K] [NumberField K]
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hcont : Continuous φ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : IsFactorizableTestFn K f) :
    Continuous (rightConv K φ f) ∧
      ∀ g : AdelicGL2 (𝓞 K) K,
        ContDiff ℝ (Module.finrank ℚ K + 1) (fun z : mixedEmbedding.mixedSpace K =>
          rightConv K φ f (unipotentGL2 (R := AdeleRing (𝓞 K) K)
            ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm z, 0) * g))
```

**Everything else stays `private`.** The pin's `RightConvRegularity` prelude is 27 private
declarations and belongs to this file only: the `port once` block is empty (no other pin file copies
it) and no port module states it. Do **not** promote it — this is explicitly not the FR-0101 case.

The proof is `P2M/Sol/S_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn.lean`
lines 1–471, transcribed with the pin's namespace `P2MW.S_…RightConvRegularity` dropped (the
declarations are `AutomorphicForm`'s, as their statements are; the file keeps them `private`, so the
namespace is a name-collision device only).

## 3. The shape, so you know where the weight is

| pin block | lines | what it is | what lands it |
|---|---:|---|---|
| `exists_integrable_bound`, `integrable_of_vanish` | 26 | dominated bound on a compact support, from a continuous `H : P × α → E'` | `exists_bound_of_continuousOn` on `closedBall z₀ 1 × S` + `S.indicator` |
| `continuous_shape` | 8 | continuity of `p ↦ T p.2 (Ψ (c p.2 + L p.1))` | composition, `ContinuousLinearMap.clm_apply` |
| `contDiff_integral_shape` | 60 | **the engine**: `ContDiff ℝ n (fun z => ∫ a, T a (Ψ (c a + L z)))`, by induction on `n` | `contDiff_zero` + `continuousAt_of_dominated` for `n = 0`; `contDiff_succ_iff_hasFDerivAt` + `hasFDerivAt_integral_of_dominated_of_fderiv_le` for the step |
| `entry_affine`, `sliceL{,Psi,CD,apply}`, `nz`, `continuous_{symm_ringEquiv_mixedSpace,nz}`, `glArch_unipotent`, `glFin_unipotent`, `unipotentGL2_inv'` | 90 | the adèlic dictionary: `archEntries ((n(z)·g)⁻¹·y)` is `sliceCD g y .1 + z · sliceCD g y .2`; `glFin` is `z`-free | entry identity for `!![1,a;0,1]`, `map_add`/`map_mul`, `unipotentGL2_zero` + `inv_one` |
| `contDiff_slice` | 68 | the pin's `hsupp` compact-support bound and the Haar re-indexation into `shape_applies` | `(z, y) ↦ n(z)·g·y` on `closedBall z₀ 1 × tsupport f`, then `integral_mul_left_eq_self` |
| `continuous_rightConv` | 55 | **continuity in `g`**: `ε/δ` with `δ = ε/(‖f‖₁ + 1)` | `hfs.isCompact.eventually_forall_of_forall_eventually`, `norm_integral_le_of_norm_le`, `integral_sub` |
| `solution` | 10 | the pair | `obtain ⟨hfc, hfs⟩ := continuous_and_hasCompactSupport_…`; `exact_mod_cast` for the `ℕ∞`/`ℕ` order |

## 4. Traps (from the manager's read of the pin — all measured, not guessed)

1. **the `private abbrev instNG`/`instNS` + `attribute [local instance]` wall.** The pin installs the
   `NormedAddCommGroup`/`NormedSpace ℝ` structures on `mixedEmbedding.mixedSpace K` locally, before
   `section Slice`. Keep them (and keep them `private` + `local instance`, not `haveI`):
   `hasFDerivAt_integral_of_dominated_of_fderiv_le` needs the normed structure at that type.
2. **keep the shape block parameter-order.** `contDiff_integral_shape (L) (n) : ∀ {E E'} … (Ψ) (hΨ) (T)
   (hT) (c) (hc) (hsupp), ContDiff ℝ n …` — `n` is explicit *before* the implicit block, and the
   induction hypothesis is applied at `(fderiv ℝ Ψ)`, `T'`, `hsupp'`. Reordering breaks the recursion.
3. **`hasFDerivAt_integral_of_dominated_of_fderiv_le` wants six arguments in the pin's order**; the
   `bound` is the *derivative* integrand's domination and `integrable_of_vanish` supplies each of the
   three measurability/integrability side goals.
4. **`fun_prop` after `fin_cases`/`simp`** in every `Continuous` entry block — the port's deleted
   specialised copies had exactly this shape; `simp` alone leaves the `1`-entry open.
5. **`exact_mod_cast` closes the headline**, not a `Nat.cast` rewrite through `ContDiff ℝ n`.
6. **no `set_option maxHeartbeats`.** The pin sets none on this file; if the module needs one, report it
   as a finding instead of adding it.
7. **no `push_neg`/deprecated spelling** — FR-0036.

## 5. Build and check discipline

- check the file with `lake env lean FLTForHuman/AutomorphicForm/Adelic/RightConvRegularity.lean` while
  iterating; the project's global `maxHeartbeats` is 4M, so wall-clock `timeout` is the real guard;
- write the `.olean` with `flock .lake/flt_build.lock timeout 280 lake build
  FLTForHuman.AutomorphicForm.Adelic.RightConvRegularity`; **no tree build**, no dependents (the module
  has 0 importers);
- log every build in `lean/tmp/`;
- `python3 spec/check_port.py --force FLTForHuman/AutomorphicForm/Adelic/RightConvRegularity.lean` →
  **1 ok** (the headline) / **0 mismatch** / **0 missing**; the pin's private prelude shows as
  `promoted` through the pin-private fallback;
- `#print axioms AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn` →
  `[propext, Classical.choice, Quot.sound]`;
- `python3 ../tools/deps/dedup.py --within --module FLTForHuman/AutomorphicForm/Adelic/RightConvRegularity.lean`
  → report clusters, do not refactor; `move_dead.py --dry-run` → expect 0 dead;
- **zero warnings**; no `sorry`/`admit`/`axiom`/`native_decide`.

## 6. The consumer zone (part of the deliverable)

Append **zone C** to `spec/AutomorphicFormSetAF5Consumer.lean` (the manager's zones A/B are there and
green): a real composition of the headline with the port, no `#check` — e.g. continuity of
`g ↦ ∫ x, φ (g * x) * f x` read off the first component and then re-indexed by
`rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply` (so the zone fails if either the headline or the
translation law is deleted), or the second component at `g = 1` composed with
`continuous_unipotentGL2`. Error count is the metric: **0**.

## 7. Report

Report back: the module's line count, the checker's three numbers, the axioms line, the build time and
its silence, the dedup/move_dead verdicts, the consumer zone's error count, and **any deviation from
the pin** (a renamed mathlib lemma, a binder the port's imports force, a `local instance` you had to
add) — deviations are expected and are recorded in SET-AF5 §1.5/§5, not hidden. A blocker goes back as
soon as it is hit, with the pin line and the error.
