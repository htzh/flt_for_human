# WORKORDER-T4 — the continuous norm section (tier-3 engine + thin façade)

**Status: landed 2026-10-18** — results in §8. Read
[../../PORTING-DeligneSerre.md](../../PORTING-DeligneSerre.md) §3 (the workflow), §4
(definitions whole node; `private` is a build tool; a hub edit is a wave) and
[porting-playbook.md](../../../porting-playbook.md) §3–§5 before starting, then
[TOPIC-continuous-ideleNorm.md](TOPIC-continuous-ideleNorm.md) §3 and §10 — this set is the
next block of the same `M4aLocalCFT.FujisakiC3` pin development.

Pin `anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`); port
mathlib `v4.34.0`.

**One node, one story: the idele norm has a continuous splitting.** 901 raw pin lines, of
which 684 are already in the port (the T1 prelude the silo re-copies); the genuinely new
mathematics is **25 declarations / 179 net new lines**, and the pin re-proves the same block
in nine sibling `S_` files, so it is homed **once** as a tier-3 engine.

## 1. Scope

Two new modules, nothing else:

1. **Engine** `FLTForHuman/NumberTheory/NumberField/TateGlobal/NormSection.lean` — tier 3,
   **unlisted**, 25 public declarations at the pin names, namespace
   `NumberField.TateGlobal.FujisakiC3` (the pin's `M4aLocalCFT.FujisakiC3`, chapter-prefix
   renamed exactly as WORKORDER-T1 renamed every other `M4aLocalCFT.*` block).
2. **Façade** `FLTForHuman/NumberTheory/NumberField/TateGlobalNormSection.lean` — listed,
   **one** headline.

**Explicitly not this order.**

* The two `exists_norm_apply_eq_ideleNorm_rpow` cousins (`NumberField.TateGlobal.…`,
  `RatIdele.…`, 236 / 312 silo lines). They are a *different* story — the absolute value of a
  continuous idèle-class character is a power of the idèle norm — and they will import this
  engine rather than copy `continuous_archUnitHom` when their orders come. Do not port them.
* The eight `normQ` siblings of [TOPIC-continuous-ideleNorm.md](TOPIC-continuous-ideleNorm.md)
  §11; they import `TateGlobal/FujisakiC3.lean` and, later, this engine.
* The silo's T1 prelude (pin lines 1–727, 43 declarations): all 42 substitutable names are
  already in the port (§3). Do not re-prove any of them.
* The pin's `p2m_*` scaffolding (`p2m_open`, `p2m_export`, `p2m_reactivate`, `P2M.Util`).
* **Any edit to an existing module.** No promotion, no hub edit, no wave — see §6.

## 2. The headline

Statement authority is the pin wrapper
`Theorems/Thm_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.lean`
(9 lines). State it **verbatim** (the checker diffs it, and the façade is the only new
checker surface):

```lean
theorem NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq
    (F : Type) [Field F] [NumberField F] :
    ∃ s : ℝ≥0ˣ →* (AdeleRing (𝓞 F) F)ˣ, Continuous s ∧
      (∀ r : ℝ≥0ˣ, ideleNorm F (s r) = ((r : ℝ≥0) : ℝ)) ∧
      ∀ r : ℝ≥0ˣ, ((s r : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1
```

Its pin proof is `P2M/Sol/S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.lean`,
`solution` at lines 893–901; the wrapper's `open NumberField NumberField.TateGlobal` and
`open scoped NNReal` are port-local choices.

## 3. What the engine holds — the 25 declarations, pin lines verbatim

Pin line numbers are in
`P2M/Sol/S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.lean`
(fetch it read-only; the raw URL is
`https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.lean`).

| pin line | span | declaration |
|---:|---:|---|
| 729 | 8 | `continuous_archUnitHom_val` (`open scoped Classical in`) |
| 737 | 9 | `continuous_archUnitHom` |
| 774 | 3 | `ideleNormU` (`def`, `variable (F) in`) |
| 777 | 2 | `val_ideleNormU` |
| 780 | 2 | `coe_val_ideleNormU` |
| 783 | 3 | `ideleNormU_eq_one_iff` |
| 786 | 2 | `ideleNormU_of_mem` |
| 794 | 5 | `norm_ringEquivRealOfIsReal_symm` (`omit [NumberField F] in`) |
| 800 | 5 | `norm_ringEquivComplexOfIsComplex_symm` (`omit [NumberField F] in`) |
| 807 | 2 | `continuous_ringEquivRealOfIsReal_symm` (`omit [NumberField F] in`) |
| 811 | 3 | `continuous_ringEquivComplexOfIsComplex_symm` (`omit [NumberField F] in`) |
| 815 | 3 | `realSectionOfIsReal` (`def`) |
| 818 | 5 | `realSectionOfIsComplex` (`def`) |
| 824 | 3 | `val_realSectionOfIsReal` |
| 829 | 3 | `val_realSectionOfIsComplex` |
| 834 | 3 | `continuous_realSectionOfIsReal` |
| 839 | 4 | `continuous_realSectionOfIsComplex` |
| 847 | 2 | `localSection` (`def`, `open scoped Classical in`, `variable (w)`) |
| 851 | 4 | `continuous_localSection` |
| 857 | 8 | `norm_localSection_pow_mult` |
| 866 | 2 | `normSectionAt` (`def`) |
| 869 | 1 | `normSectionAt_apply` (`rfl`) |
| 871 | 2 | `continuous_normSectionAt` |
| 874 | 2 | `ideleNorm_normSectionAt` |
| 877 | 2 | `ideleNormU_normSectionAt` |

The pin's two `scoped instance`s (line 16 `LocallyCompactSpace (AdeleRing …)ˣ`, line 36
`instSecondCountableCompletion`) are prelude for the T1 half, **not** for these 25 lines:
do not port them (the port has its own `haveI` sites where they are needed; a `scoped
instance` in the engine would change instance search for every importer).

Every declaration carries a `-- pin: <name> (S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.lean:<line>)`
marker above it, so `tools/deps/unwired_register.py` fills the provenance column.

**The mathematics** (for the module docstring, which is part of the deliverable):
`ideleNormU` is `distribHaarChar (AdeleRing (𝓞 F) F)` pushed into the unit group; at an
archimedean place `w`, the completion is `ℝ` (`IsReal`) or `ℂ` (`IsComplex`) up to a ring
equivalence that is an isometry (`ringEquivRealOfIsReal`, `ringEquivComplexOfIsComplex`), so
`t ↦ e.symm t` (`realSectionOfIsReal`) and `r ↦ e.symm (√r : ℂ)` (`realSectionOfIsComplex`,
the square root because `w.mult = 2` there) are continuous monoid homomorphisms
`ℝ≥0ˣ →* (w.Completion)ˣ` whose norm to the power `w.mult` is `r`. `localSection` is the
`if hv : IsReal w` merge; `normSectionAt : ℝ≥0ˣ →* (AdeleRing …)ˣ` transports it through
`archUnitHom w` into the idèles, has trivial finite part by construction, and
`ideleNorm_normSectionAt` computes `ideleNorm F (normSectionAt w r) = r` by
`ideleNorm_archUnitHom` (already in the port). The headline takes any place
(`Classical.arbitrary (InfinitePlace F)`) — a nonempty `F` always has one.

## 4. What is already in the port — import, never re-prove

`port_advise` reports **42 identical statements (≈690 lines)**. The ones the 25 new lines
actually name, with their homes (hand-checked — the tool's `port_name` column can print a
last-name fallback):

| name | port home |
|---|---|
| `ideleNorm`, `normOneIdeles`, `archUnitHom` | `TateGlobal/Defs.lean` |
| `ideleNorm_archUnitHom` | `TateGlobal/ArchNorm.lean:54` |
| `ArchMulHaarCompletion.nnnorm_ringEquivReal`, `…nnnorm_ringEquivComplex` | `TateGlobal/ArchMulHaar.lean:188,194` |
| `ArchMulHaarCompletion.distribHaarChar_*`, `distribHaarChar_completion_eq_pow_mult` | `TateGlobal/ArchMulHaar.lean`, `TateGlobal/IntLocalIntegrability.lean` |
| `archUnitHom_apply`, `archCentralUnit`, `isCompact_box`, `archSlab*` … | `TateGlobal/Defs.lean`, `ArchSlab.lean`, `FiniteSlab.lean` |

So the engine's import block is **two port modules** — `…TateGlobal.Defs` and
`…TateGlobal.ArchNorm` — plus whatever mathlib file `NNReal.sqrtHom` /
`NNReal.continuous_sqrt` needs if it is not already in that cone
(`Mathlib.Analysis.Real.Sqrt`). Do not import `TateGlobal/FujisakiC3.lean`: the norm-`Q`
engine is a different subject and its 11k-line T1 cone must not be dragged into a consumer of
the section.

`norm_ringEquivRealOfIsReal_symm` / `norm_ringEquivComplexOfIsComplex_symm` are also proved
(inline, in the same shape) inside `TateGlobal/ArchNorm.lean`'s `exists_norm_pow_mult_eq` and
declared publicly under a *different namespace* in
`AutomorphicForm/Adelic/WeylIntegrable/LatticeEstimates.lean:691,703`. Neither is a
substitution: the first is not a declaration, the second is downstream (importing
`AutomorphicForm` from `NumberField/TateGlobal` inverts the tower). **Re-prove the two in the
engine** and say so in the module docstring.

## 5. The façade

`FLTForHuman/NumberTheory/NumberField/TateGlobalNormSection.lean`:

```lean
theorem NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq
    (F : Type) [Field F] [NumberField F] :
    ∃ s : ℝ≥0ˣ →* (AdeleRing (𝓞 F) F)ˣ, Continuous s ∧ …   -- verbatim, §2
```

proved as in the pin's `solution`:

```lean
  classical
  refine ⟨FujisakiC3.normSectionAt (Classical.arbitrary (InfinitePlace F)),
    FujisakiC3.continuous_normSectionAt _, fun r => ?_, fun r => rfl⟩
  exact FujisakiC3.ideleNorm_normSectionAt _ r
```

(the pin's `M4aLocalCFT.FujisakiC3.` prefix becomes the port's
`NumberField.TateGlobal.FujisakiC3.`; inside `namespace NumberField.TateGlobal` it is
`FujisakiC3.`). The third conjunct is `rfl` because `archUnitHom`'s finite part is
`1 : FiniteAdeleRing`, whose coercion to `AdeleRing` has second component `1`.

The façade imports only the engine, opens `NumberField`/`NumberField.TateGlobal` and
`scoped NNReal`, and carries a docstring tying it to
`topics/numberTheory/tateGlobal/TOPIC-norm-section.md`.

## 6. Build discipline (copy in, verbatim)

> Edit loop
> `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` — the cap is
> **low on purpose**: a declaration that exceeds it has an instance-inference defect, and the
> low cap is what finds it. Diagnose it (`set_option diagnostics true`,
> `trace.Meta.synthInstance true` on that one declaration, in a scratch copy under `tmp/`),
> fix the inference, re-run. Never raise `maxHeartbeats`, never add a module
> `set_option maxHeartbeats`. When a file is done,
> `flock .lake/flt_build.lock timeout 300 lake build <module>` (writes the `.olean`, builds
> dependencies, never dependents). Every `lake build` serialized and bounded. **Never a bare
> whole-tree `lake build`.**

**Hub prohibition.** Do not edit `TateGlobal/Defs.lean`, `Ideles.lean`, `ArchNorm.lean`,
`ArchMulHaar.lean`, `FujisakiC3.lean`, the existing façade
`NumberField/TateGlobalContinuousIdeleNorm.lean`, or any other existing module — not even to
add a `simp` lemma or a promotion. If you believe a promotion is genuinely required, **stop
and report** with the declaration, the host and the price from
`python3 tools/deps/build_ladder.py --edit <host>`. On this measurement none is needed:
`ArchNorm.lean` is 7 modules / 3,655 lines / ≈45 s, `FujisakiC3.lean` 6 / 2,143 / ≈27 s, and
this order avoids both.

**Drift surface, in the order the pin hits it.**

1. `continuous_archUnitHom_val`: the pin's `show Continuous fun a : (w.Completion)ˣ =>
   Function.update (1 : InfiniteAdeleRing F) w (a : w.Completion)` then
   `continuous_const.update w Units.continuous_val`. In the port `InfiniteAdeleRing` is a
   `def`, not a reducible `abbrev`, so its `TopologicalSpace` instance is keyed on the folded
   head — the same defect the `continuous_normQ` landing recorded
   ([TOPIC-continuous-ideleNorm.md](TOPIC-continuous-ideleNorm.md) §10). If `show` fails,
   spell the base monoid explicitly: `Units.continuous_val (M := InfiniteAdeleRing F)` and
   the Pi-type `((w : InfinitePlace F) → w.Completion)` in the `show`. Adapt the proof, never
   the statement.
2. `continuous_archUnitHom`: `Units.continuous_iff.mpr ⟨_, _⟩` with the `map_inv` rewrite; the
   pin's `(continuous_archUnitHom_val w).comp continuous_inv`.
3. `localSection` / `continuous_localSection`: `dif_pos` / `dif_neg` are the pin's spelling;
   in `v4.34.0` the `rw` may need `dite_eq_left` / `dite_eq_right` (the drift every landed
   block has hit). The `def` needs `open scoped Classical in`.
4. `norm_localSection_pow_mult`: `mult_isReal ⟨w, hv⟩` / `mult_isComplex ⟨w, not_isReal_iff_isComplex.mp hv⟩`
   are mathlib `v4.34.0` names; `NNReal.sq_sqrt`, `NNReal.norm_eq`, `Complex.norm_real`.
5. `Continuous.units_map (f : M →* N) (Continuous f)` — argument order `f` then proof, as the
   pin writes it (`v4.34.0` agrees: `Mathlib/Topology/Algebra/Monoid.lean:922`).
6. `NNReal.sqrtHom : ℝ≥0 →*₀ ℝ≥0`, `Complex.ofRealHom`, `NNReal.toRealHom : ℝ≥0 →+* ℝ` — use
   `.toMonoidHom` where the pin does.

## 7. Verification

| check | expected |
|---|---|
| tier-0 edit loop, both modules | exit 0, **0 warnings**, no `sorry`/`admit`/`axiom`/`native_decide`/bare `import Mathlib`/`set_option maxHeartbeats` |
| tier-1 `flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.NumberTheory.NumberField.TateGlobalNormSection` | green, engine .olean written |
| checker before | 10342 identical / 0 mismatched / 0 missing / 42 own / 294 registered (10678) |
| checker after | **10343** identical — delta **+1**, exactly the headline |
| `#print axioms` on the headline | `[propext, Classical.choice, Quot.sound]` |
| `python3 tools/deps/unwired_register.py --check` | current after the engine's 25 `-- pin:` markers and a `--rebuild` |
| `git status` | only the two new modules, the register and the checker wiring |

The checker's mutation sensitivity is the instrument's own test
(`python3 spec/check_flt_statements.py --selftest`), not a per-set manual mutation; run it
only if you touch the checker.

## 8. Report shape

1. The two module paths and their final line counts; the 25 declaration names as landed.
2. The engine's exact import block and why each module is there.
3. Every proof adaptation made (pin line → port spelling), with the pin's line number.
4. Checker before/after with the delta reconciled against the +1 surface.
5. `#print axioms` output for the headline; the forbidden-token sweep result.
6. Tier-0 and tier-1 results with wall times.
7. Anything you had to leave undone, and any promotion you judged necessary (you should have
   stopped and asked instead).

## 9. Results as landed (2026-10-18)

| | |
|---|---|
| engine | `FLTForHuman/NumberTheory/NumberField/TateGlobal/NormSection.lean` — 239 lines, 25 public declarations, tier 3 |
| façade | `FLTForHuman/NumberTheory/NumberField/TateGlobalNormSection.lean` — 44 lines, 1 headline |
| checker | 10,342 → **10,343 identical**, 0 mismatched / 0 missing, 42 own, 294 registered-unwired |
| axioms | `[propext, Classical.choice, Quot.sound]` |
| tier-0 | both modules exit 0, 0 warnings |
| tier-1 | `… lake build FLTForHuman.NumberTheory.NumberField.TateGlobalNormSection` green, 3684 jobs |
| register | 129 modules / 4055 public / 3751 with a pin counterpart (was 128 / 4030 / 3726) |
| existing modules edited | none |

Two corrections to this order, both from the landing:

1. **§6.1's fallback does not work.** `Units.continuous_val (M := InfiniteAdeleRing F)` fails
   for the same reason the pin's `continuous_const.update w Units.continuous_val` does: the
   implicit family `A : InfinitePlace F → Type*` of `Continuous.update` is a *section variable*
   that the elaborator commits to `fun _ => Pi` from `Units.continuous_val`'s monoid before the
   goal constrains it, because `InfiniteAdeleRing` is a non-reducible `def`. What works is
   naming the family: `Continuous.update (A := fun v : InfinitePlace F => v.Completion)
   continuous_const w Units.continuous_val`.
2. **§4's conditional `Mathlib.Analysis.Real.Sqrt` is unnecessary** — `NNReal.sqrtHom`,
   `NNReal.continuous_sqrt`, `NNReal.toRealHom`, `NNReal.sq_sqrt` and `Complex.ofRealHom` all
   resolve in the `ArchNorm` cone already, so the engine's import block is exactly the two
   port modules.

The full record is [logs/norm-section.md](../../../logs/norm-section.md).
