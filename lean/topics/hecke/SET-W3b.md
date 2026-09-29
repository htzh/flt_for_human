# SET W3b — lift the `X1DiamondRational` region with its context

**Status: done for `Gamma0Rationality` (2026-09); `Gamma1Basis`/`Gamma0Integral`/`Gamma1IntegralBasis` not yet rewired.** Follows SET-W3's core and the W4 block-homing. It is the
piece the block-by-block recipe cannot do: the Γ rationality vocabulary is spread across
several *sections* of `Gamma0Rationality`, and lifting the declarations one at a time loses
the sections' `open`s and `variable`s (the round-5 attempt failed with
`Unknown identifier Periodic`/`IsBoundedAtImInfty`/`K`, `unsupported token`, and bogus
`Function expected at` errors).

## 0. Goal

Move the shared Γ rationality vocabulary out of `Gamma0Rationality` and `Gamma1Basis` into
[`WeightOne/Defs/Gamma.lean`](../FLTForHuman/ModularForms/WeightOne/Defs/Gamma.lean) (the
existing Γ home), so each is written once. The vocabulary:

`tauPair`/`WW`/`fricke`/`jf` (already homed) plus the rationality engine `cw`, `cw_apply`,
`cw_mul`, `cw_one`, `cw_eq_slash`, `cw_ne_zero`, `cwAlgHom`, `cwAlgHom_apply`, `cw_mul_fun`,
`cw_aeval`, `cw_ev`, `cw_gen`, `conj_mem_Gamma`, `gen`, `genSet`, `gen_none`, `gen_some`,
`gen_id_mem`, `exists_rat_combination`, `exists_pow_of_aut`, `exists_map_of_rat`, `jf_smul`,
`mdifferentiable_cw`, `periodic_add`, and the helpers `FD`, `RatAt`, `Idx`, `disc_smul`,
`zetaK`, `coe_zetaK`, `isPrimitiveRoot_zetaK`, `isPrimitiveRoot_zetaN`, `phiOf`,
`phiOf_apply`, `phiOf_zeta`, `phiOf_ratCast`.

## 1. Why the block recipe does not work here

`Gamma0Rationality`'s copies live inside `namespace WLightS10.S_…` → `namespace
X1DiamondRational` (≈1,210–2,426 of the committed original), under sections
`Cyclo`, `Width`, `Transport`, `Group`, `Invariance`, `Fricke`, `Descent`, `Algebra`,
`Main`, with file-level `open Complex UpperHalfPlane ModularForm …`, `variable (N : ℕ)
[NeZero N]`, and `local notation "Δ"`. A declaration's source text does not carry its
`open`s or section variables, so extracted text does not compile in isolation — exactly the
failure seen in round 5.

## 2. Method — lift the region, not the declarations

1. **Freeze the prerequisite.** The region's `Width` section consumes the width family; those
   lemmas are already homed in `ModularForms/QExpansionCoeff.lean` (`UpperHalfPlaneAux.*`), so
   the new home imports it. Confirm with
   `python3 tools/deps/port_graph.py --closure FLTForHuman.ModularForms.WeightOne.Gamma0Rationality "<names>"`.
2. **Extract the region verbatim** from `Gamma0Rationality`'s `namespace X1DiamondRational`
   through its matching `end X1DiamondRational`, strip `private`, and place it in the home
   **inside a namespace of the same name** (`X1DiamondRational`), preceded by the file-level
   opens, `variable (N : ℕ) [NeZero N]` and `local notation "Δ"`. Keeping the namespace means
   the declarations' reachable names are unchanged, so references in `Gamma0Rationality` and
   `Gamma1Basis` resolve after an `open X1DiamondRational`.
3. **Do not lift the region's `Main` section** if it proves the module's headline from the
   vocabulary; the headline stays in `Gamma0Rationality`. Lift only the vocabulary sections
   (`Cyclo`–`Descent`/`Algebra`), and leave `Main` behind.
4. **Rewire `Gamma0Rationality`**: import the home, delete the lifted region, `open
   X1DiamondRational`. **Rewire `Gamma1Basis`**: delete the statement-identical copies (use
   the multi-occurrence script in [SET-W4](SET-W4.md)), `open X1DiamondRational`. Any
   qualified reference to a deleted copy must be rewritten.
5. **Build after each module**, then the Γ family, then `timeout 300 lake build`.

## 3. Risks

- **Duplicate-name collision inside the region**: `Gamma0Rationality` itself contains
  several copies of some names (e.g. `qParam_one_eq_pow` three times, `qExpansion_disc_rat_one`
  three times). The region extraction must deduplicate by keeping one canonical copy, or the
  home will not elaborate (`already declared`).
- **Section-variable binder forms**: the region's `variable (N : ℕ)` is explicit; keep it
  explicit so call sites (`foo N …`) keep working.
- **`IntermediateField`/`adjoin` carrier defeq** (playbook §3.11, second failure mode): if a
  coercion lemma in the region goes from seconds to minutes, apply the generic `ifRE` remedy
  rather than raising a cap.
- **Placement**: if part of the region turns out to be a different subject (the `phiOf`
  cyclotomic block, say), split it into its own `Defs/` module rather than growing `Gamma`.

## 4. Definition of done

- The Γ vocabulary is written once in the home; `Gamma0Rationality` and `Gamma1Basis` import
  it and their copies are gone.
- `timeout 300 lake build` green, 0 warnings; checker `0 mismatched / 0 missing`, `identical`
  unchanged; consumer exit 0.
- `port_graph.py --blocks` falls below the post-W4 figure; the `Gamma0Rationality ↔
  Gamma1Basis` pair drops out of the report.


## 5. Outcome

`Defs/GammaRational.lean` was created by lifting lines 1151–2047 of `Gamma0Rationality` with
the namespace, opens and `variable (N : ℕ)` preserved. The home imports the level-family
modules whose headlines the region consumes (no cycle) and drops the region's local
`zetaN`/`kN` (they duplicate `WLight`'s with the same elaborated type, and keeping both made
term resolution ambiguous under `open WLight` + `open X1DiamondRational`).
`Gamma0Rationality` imports the home and its region is deleted; `--blocks` fell 4,560 → 3,870.

The batch rewire of `Gamma1Basis`/`Gamma0Integral`/`Gamma1IntegralBasis` was **reverted**: it
reproduced the binder-form failures (`Application type mismatch`, and an `Idx` deleted when a
copy was matched by statement alone). Those modules still carry the vocabulary; wiring them
requires per-declaration call-site review, and the deletion gate must require **name +
statement**, not statement alone.
