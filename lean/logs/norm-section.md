# The continuous norm section — one tier-3 engine, one headline

**Status: landed 2026-10-18.** Two new modules, green with 0 errors and 0 warnings:

* `FLTForHuman/NumberTheory/NumberField/TateGlobal/NormSection.lean` — 239 lines, **25 public
  declarations**, namespace `NumberField.TateGlobal.FujisakiC3`, tier 3 (unlisted, registered
  in `spec/UNWIRED-PUBLIC.md` with a `-- pin:` line each);
* `FLTForHuman/NumberTheory/NumberField/TateGlobalNormSection.lean` — 44 lines, one listed
  headline.

Checker **10,343 identical** (was 10,342), 0 mismatched / 0 missing: the delta **+1** is
exactly the headline. `#print axioms` on it is `[propext, Classical.choice, Quot.sound]`.
**No existing module was edited** — no promotion, no hub edit, no wave.

| | |
|---|---|
| headline | `NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq` |
| pin proof | `P2M/Sol/S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.lean` (901 lines, 68 declarations) |
| statement authority | `Theorems/Thm_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.lean` (9 lines) |
| net new math | 179 lines of 901 (684 are already-ported prelude) |
| structure | 25-declaration engine public tier 3; one wired headline |
| build | engine 3.2 s, façade green (3684 jobs) after the docstring edit; tier-0 exit 0 / 0 warnings |
| register | 128 → 129 modules, 4030 → 4055 public declarations, 3726 → 3751 with a pin counterpart |

## 1. What the theorem says

The idèle norm `ideleNorm F : (AdeleRing (𝓞 F) F)ˣ → ℝ` is continuous (the sibling landing
`NumberField.TateGlobal.continuous_ideleNorm`) and this node **splits it continuously**: there
is a continuous monoid homomorphism `s : ℝ≥0ˣ →* (AdeleRing (𝓞 F) F)ˣ` with

```
ideleNorm F (s r) = ((r : ℝ≥0) : ℝ)      for all r : ℝ≥0ˣ
((s r : …ˣ) : AdeleRing (𝓞 F) F).2 = 1   for all r : ℝ≥0ˣ
```

i.e. a section of the norm that is supported at a single archimedean place. The construction
is elementary and exact: at a real place `w` the completion is `ℝ` (`IsReal w`) via the
isometry `ringEquivRealOfIsReal`, so `t ↦ e.symm t` works; at a complex place it is `ℂ` via
`ringEquivComplexOfIsComplex`, and since `w.mult = 2` there, `r ↦ e.symm (√r : ℂ)` has norm
`r^(1/2)`, whose square is `r`. `localSection` merges the two by `if hv : IsReal w`;
`normSectionAt = archUnitHom w ∘ localSection` pushes it into the idèles, whose finite part is
`1` by construction; `ideleNorm_archUnitHom` (already in the port) computes the norm; the
headline instantiates at `Classical.arbitrary (InfinitePlace F)`.

The node is a **graph leaf** with 57 whole-project dependents, and it sits on the shortest
citation path from the Deligne–Serre gate up to `fermatLastTheorem` — its direct consumer is
`NumberField.TateGlobal.exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow`,
which the `LanglandsTunnell` layer reaches through
`exists_isArithGenuineCuspRealizable_of_isJLNice`.

## 2. Why this is one engine and not a 901-line transcription

`port_advise` puts **684 of the 901 lines already in the port** — the silo re-copies the T1
`archSlab` / `distribHaarChar` / `ideleNorm_archUnitHom` prelude, 42 declarations, all
importable. The genuinely new mathematics is the pin's `Fold_FujisakiC3c` + `Fold_FujisakiC3e`
sections, 25 declarations / 179 net new lines:

| group | declarations |
|---|---|
| continuity of `archUnitHom` | `continuous_archUnitHom_val`, `continuous_archUnitHom` |
| the norm hom into units | `ideleNormU` + `val_` / `coe_val_` / `…_eq_one_iff` / `…_of_mem` |
| real/complex sections | `norm_ringEquiv{,Real,Complex}*_symm`, `continuous_ringEquiv*_symm`, `realSectionOfIsReal`, `realSectionOfIsComplex`, their `val_` / `continuous_` lemmas |
| the merged section | `localSection`, `continuous_localSection`, `norm_localSection_pow_mult` |
| transport to the idèles | `normSectionAt`, `…_apply`, `continuous_normSectionAt`, `ideleNorm_normSectionAt`, `ideleNormU_normSectionAt` |

**The block is shared by nine pin `S_` files.** `grep -rl` over `P2M/Sol/` finds all 25 names in
the eight `normQ` siblings of
[../topics/numberTheory/tateGlobal/TOPIC-continuous-ideleNorm.md](../topics/numberTheory/tateGlobal/TOPIC-continuous-ideleNorm.md)
§11 plus this node — the `normQ` family with `continuous_ideleNorm` swapped for this node. So
the engine is justified family-wide: the eight siblings will import `NumberField.TateGlobal.FujisakiC3`
*and* this module when their orders come, instead of re-proving 130 lines each.

## 3. Structure, and the two hosts it deliberately avoids

* **Engine** `TateGlobal/NormSection.lean` — the 25 declarations at the pin names, public, tier 3.
  Imports exactly two port modules: `TateGlobal/Defs.lean` (the vocabulary: `archUnitHom`,
  `ideleNorm`, `normOneIdeles`, `distribHaarChar`) and `TateGlobal/ArchNorm.lean`
  (`ideleNorm_archUnitHom`, and transitively `ArchMulHaarCompletion.nnnorm_ringEquivReal/Complex`).
  The conditional `Mathlib.Analysis.Real.Sqrt` of the work order was **not** needed: `NNReal.sqrtHom`,
  `continuous_sqrt`, `toRealHom`, `sq_sqrt` and `Complex.ofRealHom` all resolve in the `ArchNorm`
  cone (measured with `#check`).
* **Façade** `NumberField/TateGlobalNormSection.lean` — the headline, stated verbatim from the
  wrapper (the subagent verified the diff mechanically with the checker's own
  `raw_declarations`/`norm` helpers rather than by eye), proved from `normSectionAt` at an
  arbitrary place.

**Why not append to `TateGlobal/FujisakiC3.lean`** (same pin namespace, adjacent section,
6 modules / 2,143 lines / ≈27 s wave): that engine is the `normQ` block and drags the 11k-line
T1 analytic cone — `Coordinates`, `ZetaIntegrand`, `IntLocalIntegrability`, `NormIntegrable` —
none of which the section names. A consumer of the section now pays for two modules, not for
the T1 core. **Why not reuse the landed façade `TateGlobalContinuousIdeleNorm.lean`**: its
subject is the *continuity* of the norm, this one is a *section* of it, and adding it there
would both mis-describe the module and force the 6-module wave.

## 4. Verification

| check | result |
|---|---|
| tier-0 `lake env lean -DautoImplicit=false -DmaxHeartbeats=200000` both modules | exit 0, **0 warnings** |
| tier-1 `flock … lake build FLTForHuman.NumberTheory.NumberField.TateGlobalNormSection` | green, 3684 jobs |
| checker before | 10,342 / 0 / 0 / 42 own / 294 registered (10,678) |
| checker after | **10,343** / 0 / 0 / 42 own / 294 registered (10,679) — delta **+1**, the headline |
| `#print axioms` | `[propext, Classical.choice, Quot.sound]` |
| forbidden tokens | none (`sorry`/`admit`/`axiom`/`native_decide`/bare `import Mathlib`/`maxHeartbeats`/`set_option linter.*`) |
| register | `unwired_register.py --check` current; 25 new rows, each with its pin line |
| `git status` | the two new modules, the two new topic files, `spec/check_flt_statements.py`, `spec/UNWIRED-PUBLIC.md` — nothing else |

Wiring: the wrapper appended last to `SOURCES`; the façade appended last to `PORT_FILES`; the
`solution` `S_` file **deliberately not** listed, so the engine's 25 declarations stay tier 3
(the `continuous_ideleNorm` and centre-cut landings' convention) instead of half-entering the
diffed surface.

## 5. Proof adaptations (pin → v4.34.0), statements verbatim

1. `continuous_archUnitHom_val` (pin:729). The pin's `show` + `continuous_const.update w
   Units.continuous_val` does not elaborate: `InfiniteAdeleRing` is a plain `def`, so
   `Continuous.update`'s implicit family `A : InfinitePlace F → Type*` cannot be read off the
   folded head of the goal — it commits `A := fun _ => Pi` from `Units.continuous_val`'s monoid
   before the goal constrains it. Naming it,
   `Continuous.update (A := fun v : InfinitePlace F => v.Completion) continuous_const w
   Units.continuous_val`, restores the pin's one-liner. (The work order predicted the
   `Units.continuous_val (M := …)` spelling from the `continuous_normQ` landing's defect; that
   spelling fails here, so the order's §6.1 is corrected by the landing record.)
2. `continuous_localSection` (pin:851) and `norm_localSection_pow_mult` (pin:857): the pin's
   `dif_pos` / `dif_neg` are `dite_eq_left` / `dite_eq_right` in `v4.34.0`; otherwise four
   deprecation warnings.

Everything else transcribed verbatim and compiled first try — `Units.continuous_iff.mpr` +
`map_inv` (pin:737), the `RingEquiv.symm.toRingHom.toMonoidHom` / `NNReal.toRealHom.toMonoidHom`
/ `Complex.ofRealHom.toMonoidHom` / `NNReal.sqrtHom.toMonoidHom` chain (pin:815/818), the two
`rfl` `val_` lemmas and `normSectionAt_apply` (pin:824/829/869), `Continuous.units_map _ proof`
in the pin's argument order (pin:834/839), `mult_isReal` / `mult_isComplex` / `NNReal.sq_sqrt` /
`NNReal.norm_eq` / `Complex.norm_real` (pin:857).

## 6. Residuals

* `norm_ringEquivRealOfIsReal_symm` / `norm_ringEquivComplexOfIsComplex_symm` are re-proved in
  the engine though `ArchNorm.lean` uses the same argument inline and
  `AutomorphicForm/Adelic/WeylIntegrable/LatticeEstimates.lean:691,703` declares public copies
  under another namespace. Neither substitutes (one is not a declaration; the other is
  downstream of `NumberField`). If `AutomorphicForm` ever needs them from here, `ArchNorm.lean`
  is the natural home — a 7-module / 3,655-line / ≈45 s hub wave, not owed now.
* The pin's two `scoped instance`s (pin:16 `LocallyCompactSpace (AdeleRing …)ˣ`, pin:36
  `instSecondCountableCompletion`) are prelude for the silo's T1 half and are **not** ported:
  a `scoped instance` in an engine changes instance search for every importer, and no line of
  the 25 needs either.
* The **two cousins** remain on the ready shelf:
  `NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow` (236 silo lines, 42 project
  dependents) and `RatIdele.exists_norm_apply_eq_ideleNorm_rpow` (312, 7). They are a different
  story — the absolute value of a continuous idèle-class character is a power of the norm —
  and they share only the `continuous_archUnitHom` pair (plus a 15-line `expUnit` block with
  each other). Priced with this node the trio is 675 net new lines, so the cousins are 496
  lines of real content: their own order, importing this engine.
* The eight `normQ` siblings keep their own blocks (the 4,314 / 2,885 / 513 once-line blocks of
  [../topics/numberTheory/tateGlobal/TOPIC-continuous-ideleNorm.md](../topics/numberTheory/tateGlobal/TOPIC-continuous-ideleNorm.md)
  §11); they are unchanged by this landing.

## 7. Reproduce

```bash
cd lean
timeout 110 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 \
  FLTForHuman/NumberTheory/NumberField/TateGlobal/NormSection.lean
flock .lake/flt_build.lock timeout 280 lake build FLTForHuman.NumberTheory.NumberField.TateGlobalNormSection
timeout 600 python3 spec/check_flt_statements.py | tail -1     # 10343 identical
python3 tools/deps/unwired_register.py --check                 # current
```
