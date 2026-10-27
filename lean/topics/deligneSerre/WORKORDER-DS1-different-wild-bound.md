# WORKORDER DS1 — the different's wild lower bound

**Landed 2026-10-27.** `Different.lean` 232 → 1,069 lines (+837), then 1,059 after the
duplicate `deg_eq_one_of_isAlgClosed` copy was removed in favour of the orbit module's
promoted public one; `check_port` 5 ok / 0 / 0 / 0 (the three prelude lemmas resolve to
`S_…isGalois.lean:360/363/368`), axioms clean, `move_dead` 0, consumer zone 4 extended and
at 0 errors, frontier: the node off the ready shelf and the two `jqModC` demands 54 → 53.
The proof-level deviations below §5 are recorded in the topic's close.

One node, one file. Read this whole file before writing any Lean.

## 0. The node

`AlgebraicCurve.Place.sub_one_add_pow_sub_one_le_ordDiff_D_of_isGalois`, pin
`anthropics/fermats-last-theorem@aa2d8b3`, the local clone at
`~/proj/fermats-last-theorem`:

* the statement: `Theorems/Thm_AlgebraicCurve_Place_sub_one_add_pow_sub_one_le_ordDiff_D_of_isGalois.lean`;
* the proof: `P2M/Sol/S_AlgebraicCurve_Place_sub_one_add_pow_sub_one_le_ordDiff_D_of_isGalois.lean`
  (899 lines, `namespace P2MW.…` / `HilbertWildLB`, the public `solution` at the end is
  `HilbertWildLB.main`).

The statement, verbatim from the wrapper:

```lean
theorem sub_one_add_pow_sub_one_le_ordDiff_D_of_isGalois
    {K E M : Type*} [Field K] [IsAlgClosed K] [Field E] [Field M]
    [Algebra K E] [Algebra K M] [Algebra E M] [IsScalarTower K E M]
    [FiniteDimensional E M] [IsGalois E M]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (x : E) [FiniteDimensional (IntermediateField.adjoin K ({algebraMap E M x} : Set M)) M]
    (P : Place K M) (hx : (P.restrict E).ord x = 1)
    (a : ℕ) (ha : (p : ℤ) ^ a ∣ P.ord (algebraMap E M x)) :
    P.ord (algebraMap E M x) - 1 + ((p : ℤ) ^ a - 1) ≤
      P.ordDiff (D K M (algebraMap E M x))
```

It is inside `namespace AlgebraicCurve.Place` in the port, so write it unqualified. The
`D` is `KaehlerDifferential.D`; the pin's statement spells it `D` (its wrapper opens
`KaehlerDifferential`), so do the same — add `open KaehlerDifferential` to the module's
`open` block if `D` is not already in scope — and **check the statement against the wire
before writing the proof** (`python3 spec/check_port.py FLTForHuman/AlgebraicCurve/Differential/Different.lean
--force`): it must resolve to `Theorems/Thm_…isGalois.lean`, not mismatch.

## 1. Where it goes

`FLTForHuman/AlgebraicCurve/Differential/Different.lean` (212 lines, on the wire at 1 ok).
Its header already carries the wild `spec-pin` pair and the module imports
`FLTForHuman.AlgebraicCurve.Place.OrbitCardinality`; the prelude is therefore in scope.

Write the headline **public** at the pin's name, the engine **private** in the same file, as
the pin's own `solution := HilbertWildLB.main` shape. Do not create a new module, do not touch
any other file, do not edit `spec/` metadata.

## 2. What is already ported — do not re-prove it

Two substitutions from this very file are in the port and must be imported (they are already
in scope through the module's imports):

* `ord_neg'` → `ModularCurve.Es1a1.es1a10_ncPole_ord_neg` (a general `ord (-f) = ord f`);
  if the private engine wants its own name, derive it in one line, do not re-prove the order
  argument;
* `ord_pow'` → `AlgebraicCurve.Place.ord_pow` (`Defs/PlaceCalculus`).

Seven more, the pin's public prelude for this file, are **public** in
`Place/OrbitCardinality.lean` and in scope here — import, never restate:

`toSemilinear`, `placeAction`, `smul_place_def`, `mem_fiberOver_iff_mem_orbit`,
`card_stabilizer_mul_card_fiberOver`, `inertiaDeg_eq_one_of_deg_eq_one`,
`card_stabilizer_eq`.

The pin's `ord_smul_apply`, `ord_apply_of_smul_eq` and `apply_algebraMap` are **not** ported
yet: they are three one-line consequences of `SemilinearAut.ord_smul` (the port's
`SemilinearAut.ord_smul` is in `Defs/SemilinearAut.lean`, public), so port them here, public,
as the pin has them.

## 3. The instance wall

The pin registers `attribute [local instance] placeAction` in its `Galois` section and uses
`σ • W` for `σ : M ≃ₐ[E] M`, `W : Place K M` throughout the proof. Do the same: register
`attribute [local instance] Place.placeAction` in each section that needs the notation, and
**never globally** — a global `MulAction (M ≃ₐ[E] M) (Place K M)` would shadow the port's own
`SemilinearAut` action and is forbidden. If a section needs the action only to rewrite
`σ • W`, `smul_place_def` gives the definitional equation.

## 4. How the pin file is organised

| lines | content | note |
|---|---|---|
| 38–208 | `OrdCalc`: `OrdGe`, `ordGe_*`, `ord_neg'`, `ord_prod`, `ord_pow'`, `mem_of_ordGe_zero`, `exists_constant`, `transcendental_of_ord_ne_zero`, … | the port has `ord_neg'`, `ord_pow'`, `ord_prod`-equivalents; the rest is the pin's private order calculus and must be ported (it is generic `Place` algebra) |
| 210–277 | `Transport`: `adjoinEquiv`, `finiteDimensional_adjoin_of_tower`, `isSeparable_adjoin_right`, … | port as-is |
| 279–338 | `Der`: `der t f = Place.diffCoeff t (D K F f)` and its calculus (`der_spec`, `der_mul`, `der_pow`, `ordGe_der`, …) | `Place.diffCoeff` exists in `Differential/Coefficient.lean` |
| 340–487 | `Galois`: the seven public prelude declarations, then `ZK`/`mem_ZK_iff`/`algebraMap_mem_ZK`/`finiteDimensional_ZK`/`isGalois_ZK`/`finrank_ZK`/`fiberOver_ZK`/`ramificationIndex_ZK`/`dvd_ord_of_mem_ZK` | the seven are imported; the `ZK` block is new |
| 489–511 | `Vieta`: `map_univ_erase_one`, `map_univ_mul_left` | generic ring lemmas, port as-is |
| 513–883 | `Main`: `main`, the engine | the body to port |
| 887–899 | `solution` | = the public headline |

## 5. Build and verification discipline

* Tool calls finish within 2 minutes. `lake build` of the module may exceed that once the body
  is in: run it as a background job (`run_in_background: true`) and collect with
  `job_output`, log to `lean/tmp/<name>.log`.
* **No tree build.** One module at a time. No warnings, no `sorry`, no `axiom`,
  no `native_decide` (the pin's `set_option linter.unusedSectionVars false` /
  `unusedVariables false` blanket is **not** copied: use `omit … in` or `include … in` per
  declaration, and `variable` restructuring where it is the real fix).
* The pin's `attribute [-instance]` / `[-simp]` walls are not copied. Keep `scoped` exactly
  where the pin has it.
* Do not edit the module's header, its `spec-pin` block or its imports beyond what §2/§3 need.
* Do not commit; the human commits.
* Headers/comments: do not add cross-references to other ported modules or to docs.

## 6. Acceptance

1. `lake build FLTForHuman.AlgebraicCurve.Differential.Different` green and **silent**;
2. `python3 spec/check_port.py FLTForHuman/AlgebraicCurve/Differential/Different.lean --force
   --strict-markers` → `0 mismatch / 0 missing / 0 own`, and the wild headline resolves to
   `Theorems/Thm_…isGalois.lean`;
3. `#print axioms AlgebraicCurve.Place.sub_one_add_pow_sub_one_le_ordDiff_D_of_isGalois` =
   `[propext, Classical.choice, Quot.sound]` (one scratch file in `lean/tmp`, or a temporary
   `#print axioms` line removed afterwards);
4. `python3 tools/deps/dedup.py Different.lean --min-cost 0` (the engine-plus-headline pair may
   show as a `shape` cluster, cost 0 — that is the pin's own structure) and
   `python3 tools/deps/move_dead.py --source FLTForHuman/AlgebraicCurve/Differential/Different.lean
   --target Reserve/Dead.lean --select dead --dry-run` (declarations that are only used through
   instance search will read as dead; check the call sites before deleting anything);
5. no change to any other file (`git status` shows only
   `FLTForHuman/AlgebraicCurve/Differential/Different.lean`).

## 7. Reporting

Report **once** at the first genuine blocker — an unported premise, an instance wall that will
not re-register locally, or a proof step that needs something the pin proves privately in
another file — with the exact goal state and what you tried. Otherwise report once, when the
module is green and the gates of §6 pass, with the five results and anything you had to
deviate from in the pin's proof (state only; the statement must not change).
