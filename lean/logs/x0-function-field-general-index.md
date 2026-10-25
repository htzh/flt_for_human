# The `C` function fields at a general index — the ground for the `C`-layer prime-power step

Record of the definition-layer edit that landed 2026-10-25 as the **ground** for
[WORKORDER-CL2](../topics/modularCurve/WORKORDER-CL2-fullc-prime-power-step.md), the
`C`-layer prime-power step `ModularCurve.relfinrank_fullC_mul_prime_pow`. No new
mathematics: the point is that the pin's `C`-layer `S_` files state their lemmas about
`divisorExpansionsC` / `modularFunctionFieldFullC` at an index with no nonzeroness
hypothesis, and the port could not say the same.

## 1. The defect

`ModularCurve/X0/FunctionFieldFull.lean` declared

```lean
variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

def divisorExpansionsC : Set (LaurentSeries K) := ...
def modularFunctionFieldFullC : IntermediateField K (LaurentSeries K) := ...
```

The `[NeZero N]` is **vestigial in both bodies** — neither uses it — and five of the
section's seven lemmas already carried `omit [NeZero N]`. But it is on the *definition*,
so it is on the type, and the pin's `S_` consumers use the fields at an index that is
only known to be nonzero:

| pin lemma | index | why `[NeZero]` is unavailable |
|---|---|---|
| `divSet_mono`, `fullC_mono`, `fullC_le_iff` | `L`, `L'` | no hypothesis on `L` at all |
| `jqNModC_mem_fullC`, `jqModC_mem_fullC` | `L` | ditto |
| `eFull_le_fullC` | `L * n` | `n` is nonzero; `L` is not |
| `fullC_mul_prime_eq_adjoin_insert_image` | `L₀ * p` | `[NeZero (L₀ * p)]` is not synthesizable from `[NeZero L₀]` |
| `relfinrank_fullC_insert_eq_natDegree` | `L` | ditto |

Transcribing those at the pin's text would therefore have cost ~10 `own:` rows in
`spec/decl_markers.tsv`, each recording "the port's field needs a nonzero index the pin's
does not".

## 2. What changed

One edit in `ModularCurve/X0/FunctionFieldFull.lean` (16 insertions, 9 deletions — the
docstring paragraph included):

1. `[NeZero N]` dropped from the two `def`s and from the two `section` `variable` lines
   (`FunctionField`, `Jacobian`); the five `omit [NeZero N] in` lines removed.
2. The two lemmas whose *statement* does consume it carry it explicitly.
   `modularFunctionFieldC_le_full` takes it through a nested `variable [NeZero N]` section
   rather than an explicit binder, **because the checker parses the source statement text**:
   with an explicit `[NeZero N]` it printed one binder more than the pin and read
   `MISMATCH` (probed; the pin's own `[NeZero N]` is a section variable there too).
3. `modularFunctionFieldFullC_rat` needed no instance at all — `modularFunctionFieldFull`
   does not carry one — so its nested section was removed; it had produced an
   "unused section variable" warning in the first draft.

`JZeroC` is unchanged (an `abbrev`), and the pin's `Def_ModularCurve_X0ModL.lean`
statements are untouched: the general index is the pin's own text at
`S_ModularCurve_relfinrank_fullC_mul_prime_pow.lean:354` (`divSet`) and `:357` (`fullC`).

## 3. Readings

- **Elaboration**: `flock .lake/flt_build.lock timeout 100 lake env lean
  -DautoImplicit=false -DmaxHeartbeats=200000 FLTForHuman/ModularCurve/X0/FunctionFieldFull.lean`
  — exit 0, **no output** (0 errors, 0 warnings).
- **Statement check**: `python3 spec/check_port.py --force FLTForHuman/ModularCurve/X0/FunctionFieldFull.lean`
  — **13 ok / 0 mismatch / 0 missing / 1 own**, the one `own` row being the pre-existing
  `full_degeneracyC_map_le` (the pin spells the map `qExpandAlgHomC`, the port's one home
  for it is `qExpandAlg`). Both defs read `ok` against `Definitions/Def_ModularCurve_X0ModL.lean:92/100`
  — the checker's `def` tier hashes the type, and a dropped instance argument does not
  separate the two texts.
- **Build**: `lake build FLTForHuman.ModularCurve.X0.FunctionFieldFull` — green (4,135 jobs).
- **Dependent cascade** (priced by `build_ladder.py --edit`: 5 modules / 2,999 lines):
  `lake build` of `X1.FunctionFieldInclusion`, `X1.HeckeDegree`, `X1.HeckeCommute`,
  `XH.HeckeCommute`, `XH.HeckeDegree` — `Build completed successfully (4460 jobs)`, exit 0.
  The log's 69 warnings are **all pre-existing and none in these five modules from this
  edit**: they are `linter.style.haveILetI` ("Try this: have") / "Variable name `hx` is not
  explicitly referenced" in `XH/HeckeCommute.lean` and `linter.unusedSectionVars` /
  "Overlapping instance parameters" in `AlgebraicCurve/Defs/LocalResidue.lean` and
  `AlgebraicCurve/Genus/Stichtenoth.lean` — modules untouched here, re-elaborated because
  Lake found them stale.

## 4. Probe kept from the scoping pass

The three definitional equalities the `C`-layer orders rest on were confirmed by a
throwaway file importing `X0/FunctionFieldFull` (exit 0, no output), at `[NeZero L]`:

```lean
example (L : ℕ) [NeZero L] :
    divisorExpansionsC K L
      = {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ L ∧ x = jqNModC K d'} := rfl
example (L : ℕ) [NeZero L] :
    modularFunctionFieldFullC K L
      = IntermediateField.adjoin K
          {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ L ∧ x = jqNModC K d'} := rfl
example (n : ℕ) [NeZero n] (f : LaurentSeries K) : qExpandAlg K n f = qExpand K n f := rfl
```

So `WORKORDER-CL2`'s three `abbrev`s (`divSet`, `fullC`, `qExpandₐK`) are one-line aliases
of homed objects, not a second home.
