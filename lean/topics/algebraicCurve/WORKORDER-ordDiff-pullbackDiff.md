# WORKORDER — `ordDiff` of a pulled-back differential

Scope: port **one** pin node into a **new** module. Single module, single node, ~250 lines of
transcription. Do not touch any other file.

## The target

New module `lean/FLTForHuman/AlgebraicCurve/Differential/PullbackOrd.lean`, containing

- the pin node `AlgebraicCurve.Place.ordDiff_pullbackDiff_of_natCast_ramificationIndexAlong_ne_zero`
  at its `Theorems/` wrapper's statement, **verbatim**;
- the pin's own private prelude for it (12 helpers, see below), transcribed as `private` in the
  new module.

Pin sources (pinned at `aa2d8b3`, in `~/proj/fermats-last-theorem`):

- `Theorems/Thm_AlgebraicCurve_Place_ordDiff_pullbackDiff_of_natCast_ramificationIndexAlong_ne_zero.lean`
  — the statement authority. Read it; the headline's binder block and conclusion must be copied
  from it character for character (module for the leading `AlgebraicCurve.Place.` on *your*
  theorem: write the theorem inside `namespace AlgebraicCurve` / `namespace Place` if that reads
  better, but the checker compares the text after the declaration name).
- `P2M/Sol/S_AlgebraicCurve_Place_ordDiff_pullbackDiff_of_natCast_ramificationIndexAlong_ne_zero.lean`
  (283 lines) — the proof: `pullbackDiff_smul'`, `ordDiff_pullbackDiff_of_local`, then the
  `Discharge` section (`ord_phi_uniformizer`, `ord_phi_uniformizer_ne_zero`, `hadd`, `hspan`,
  `ord_algebraMap_eq_zero`, `diffCoeff_eq_of_eq_smul`, `exists_good_coeff`,
  `hDt_of_tame`, `hR6a_of_tame`) and the headline.

## What the port already has (use these, do not re-prove)

Every one of these is public and verified; the mapping is the whole job:

| pin prelude name | port declaration |
|---|---|
| `Place.ord_pow_of_ne_zero` | `v.ord_pow f n` — `FLTForHuman/AlgebraicCurve/Defs/PlaceCalculus.lean` |
| `Place.ramificationIndexAlong_pos` | `Place.ramificationIndexAlong_pos φ hφ w'` — `Defs/RestrictAlongAPI.lean` (already public; **no** private copy needed) |
| `Place.exists_ord_eq_one` | same name, `Place/OrdCalculus.lean` (import it, then keep the pin's proof text) |
| `pullbackDiff`, `pullbackDiff_D` | just added to `Differential/Coefficient.lean` (`AlgebraicCurve.pullbackDiff`, `AlgebraicCurve.pullbackDiff_D`) |
| `Place.ordDiff_smul_of_perfectField` | `Differential/Coefficient.lean` |
| `Place.ord_add_eq_of_lt` | `Place/OrdCalculus.lean` |
| `Place.isSeparable_adjoin_of_ord_eq_one` | `Place/SeparableUniformiser.lean` |
| `Place.ord_diffCoeff_D_nonneg_of_isSeparable` | `Differential/Coefficient.lean` |
| `Place.ord_restrictAlong`, `restrictAlong`, `ramificationIndexAlong`, `algebraAlong`, `isScalarTower_along`, `isIntegral_along`, `algebraMap_mem'`, `mem_iff_ord_nonneg`, `ord_zpow`, `ord_inv`, `ord_zero`, `ord_mul` | `Defs/RestrictAlongAPI.lean`, `Defs/Place.lean`, `Defs/PushPull.lean` — find them by `rg` |
| `KaehlerDifferential.exists_unique_smul_D_of_transcendental`, `D_ne_zero_of_transcendental` | `Defs/KaehlerTranscendental.lean` |

The pin's `p2m_export` / `p2m_open` / `p2m_open_scoped` lines are **not** transcribed; they exist
only to make the pin file compile in isolation. Use plain `namespace` / `open`.

## Naming

- Private helpers: keep the pin's names, dropping a trailing prime when the bare name is free in
  the new module (`pullbackDiff_smul'` → `pullbackDiff_smul`). No machine tokens, no `_impl`.
- The headline keeps the pin's (long) node name — it is the name the checker matches.

## Wire and header

The module's leading `/- … -/` block must carry, in this shape:

```
spec-pin: Theorems/Thm_AlgebraicCurve_Place_ordDiff_pullbackDiff_of_natCast_ramificationIndexAlong_ne_zero.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_ordDiff_pullbackDiff_of_natCast_ramificationIndexAlong_ne_zero.lean   -- comparable copy
```

plus 5–10 lines of prose: what the statement says mathematically (`ordDiff` of a pulled-back
differential: the order picks up the ramification index and one different exponent), that the
hypothesis `((ramificationIndexAlong φ w' : ℕ) : K) ≠ 0` is tameness, and that the prelude is the
pin's. No links to other port modules (this project's rule).

## The statement (from the Thm wrapper — copy this text)

```
theorem AlgebraicCurve.Place.ordDiff_pullbackDiff_of_natCast_ramificationIndexAlong_ne_zero
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [PerfectField K]
    (x₀ : F) [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x₀} : Set F)) F]
    (x : F') [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F')) F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w' : Place K F') {ω : Ω[F⁄K]}
    (hω : ω ≠ 0)
    (he : ((Place.ramificationIndexAlong φ w' : ℕ) : K) ≠ 0) :
    w'.ordDiff (pullbackDiff φ ω)
      = (Place.ramificationIndexAlong φ w' : ℤ) * (w'.restrictAlong φ hφ).ordDiff ω
        + ((Place.ramificationIndexAlong φ w' : ℤ) - 1)
```

## Build and check discipline

- **Never** a tree build. Build only the new module:
  `lake build FLTForHuman.AlgebraicCurve.Differential.PullbackOrd`, run from `lean/`.
- Every command must finish inside 2 minutes; do not loop to dodge that. Log to
  `lean/tmp/build-pullbackord.log`.
- The build must be **silent**: no warning from your module (`set_option autoImplicit false` at
  the top, as the sibling modules do, and keep `linter.style.haveILetI false` if you hit the
  `haveI` style linter the pin's proof walls trip).
- Statement check: `python3 spec/check_port.py --force FLTForHuman/AlgebraicCurve/Differential/PullbackOrd.lean`
  from `lean/`. Target: **1 ok / 0 mismatch / 0 missing** (private helpers are invisible to it).
  The comparison is **textual**: if the checker reports `MISMATCH`, the difference is spelling —
  the pin writes `Place.diffCoeff`, `Place.ordDiff_def`, `pullbackDiff` unqualified inside its
  namespaces, and `Place.ramificationIndexAlong` qualified. Fix the spelling, never the statement.
- Axioms: in `lean/tmp/axioms-pullbackord.lean`,
  `#print axioms AlgebraicCurve.Place.ordDiff_pullbackDiff_of_natCast_ramificationIndexAlong_ne_zero`
  must print `[propext, Classical.choice, Quot.sound]`.
- Do not edit any other file, do not add `spec/decl_markers.tsv` rows, do not commit.

## Report back (one message, no polling)

1. build: ok/fail, wall time, warnings in your module (want 0);
2. the `check_port` summary line;
3. the axioms line;
4. **early blockers**: if a pin step does not transcribe (a missing port lemma, an instance
   mismatch, a definitional-equality wall), stop after the first two attempts on the same step
   and report the exact goal state and what is missing, rather than burning rounds. A partial
   module that builds with the helpers proved and the headline `sorry`-free but blocked is a
   useful report; a `sorry` is not acceptable in the delivered file.
