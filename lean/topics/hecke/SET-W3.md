# SET W3 — the Γ home, and rewire the Γ family

**Status: partially executed — the Γ core vocabulary is homed and the four Γ modules rewired
onto it; the remaining Γ sub-blocks (width/cw/descent) are still to do.** Fourth set of the
[WeightOne rectification](TOPIC-weightone-rectify.md). SET-W1/W2 handled the level family;
this set creates the Γ₀/Γ₁ vocabulary home and rewires the four Γ modules. Each Γ module is
edited **once**.

## Execution record

`Defs/Gamma.lean` created with the cleanly-closed Γ core — `tauPair`, `tauPair_spec`, `WW`,
`WW_spec`, `fricke`, `fricke_spec`, `jf`, `jf_spec` — lifted verbatim from
`Gamma0Rationality`'s `X1DiamondRational` namespace (whose `--closure` for exactly these eight
is **empty**), under `namespace WLight`. Each of the four Γ modules imports it, `open`s
`WLight`, and deletes its 8 statement-identical copies:

| module | before → after |
|---|---|
| `Gamma0Rationality.lean` | 3,012 → 2,978 |
| `Gamma0Integral.lean` | 2,517 → 2,483 |
| `Gamma1Basis.lean` | 4,246 → 4,213 |
| `Gamma1IntegralBasis.lean` | 1,082 → 1,049 |

Still to do in W3: the `cw*`/`conj_mem_Gamma`/`gen(Set)` rationality vocabulary
(`Gamma0Rationality` ↔ `Gamma1Basis`, ~205 lines / 32 units), the `qExpansion_disc_rat*` /
`descent` / `stab_of_anchor` analysis (shared with `LevelN`), and the `Gamma1Basis` ↔
`Gamma1IntegralBasis` integral-basis block — all entangled with the deferred width family, so
they follow W4's generalisation of `qExpansion_coeff_width{,N}`.

## 0. Scope

The Γ block measured **2,695 removable lines / 116 proofs** over `Gamma0Integral`,
`Gamma0Rationality`, `Gamma1Basis`, `Gamma1IntegralBasis` (plus `LevelN`, which SET-W2 has
already rewired — so the analysis shared with `LevelN` was placed in SET-W1's
`QExpansionCoeff`, and this home holds only what the Γ modules share among themselves).

**Orders:**

1. `ModularForms/WeightOne/Defs/Gamma.lean` — the Γ-vocabulary:
   - the period/level pair `tauPair`/`tauPair_spec`, the ℘-normalised `WW`/`WW_spec`, the
     Hauptmodul `jf`/`jf_spec`, and `fricke`/`fricke_spec` (shared by all four Γ modules);
   - the conjugation/transport `cw`, `cw_apply`, `cw_mul`, `cw_one`, `cw_ne_zero`,
     `cw_aeval`, `cw_eq_slash`, `mdifferentiable_cw`, `conj_mem_Gamma`, `conj_mem_Gamma1`,
     `gen`, `genSet`, `gen_id_mem`;
   - the rationality engine `exists_rat_combination`, `exists_pow_of_aut`,
     `exists_map_of_rat`, `jf_smul`, `periodic_add` (shared by `Gamma0Rationality`,
     `Gamma1Basis`).
2. *(conditional)* `ModularForms/WeightOne/Defs/Gamma1.lean` — only if order 1's closure
   pulls in the `Gamma1Basis`/`Gamma1IntegralBasis`-only vocabulary
   (`coe_eq_of_qExpansion_eq`, `coe_modularForm`, `isIntegralQExp_coeff`,
   `neg_one_mem_Gamma1`, `stab_of_forall_eq_zero`, `kN_eq`, …) that nothing else uses:
   keep it in `Gamma1Basis` then, and do **not** create the module.
3. Rewire, in this order, one module at a time with a build after each:
   `Gamma0Rationality`, `Gamma0Integral`, `Gamma1Basis`, `Gamma1IntegralBasis`.

**Not authorized:** re-editing `LevelN` or any level-family module (SET-W2), the
near-duplicate generalisations and adapter demotions (SET-W4), the capstone, FFG/T-side,
commits.

## 1. Placement judgement

`tauPair`/`WW`/`jf` are Γ-specific vocabulary (they name the period pair and the
`E₄³/Δ`-normalised data the Γ₀-basis uses), so they belong in `WeightOne/Defs/Gamma.lean`.
Anything that is really about q-expansions of `disc` (`qExpansion_disc_rat*`,
`mdifferentiable_disc`, `periodic_disc_one`, `isBoundedAtImInfty_disc`, `ds`,
`disc_pow_ne_zero`) is ordinary discriminant analysis and belongs in SET-W1's generic
`QExpansionCoeff`/`DiscPow`, **not** here — if it is missing there, extend those homes and
report the change rather than duplicating it here.

## 2. Definition of done

- `Defs/Gamma.lean` created, closure self-contained (no import of a consumer).
- `Gamma0Rationality`, `Gamma0Integral`, `Gamma1Basis`, `Gamma1IntegralBasis` import it,
  their duplicated private copies deleted, references resolved.
- Public surface unchanged; `PORT_FILES` entries unchanged except the new home.
- `timeout 180 lake build` green, 0 warnings, no `sorry`.
- `python3 spec/check_flt_statements.py`: **0 mismatched, 0 missing**, `identical`
  unchanged except the new home's public surface (matched or listed as exempt with reason).
- `timeout 120 lake env lean spec/WeightOneConsumer.lean` exit 0.
- `python3 ../tools/deps/port_graph.py --blocks 5`: no block over threshold (both the level
  and Γ blocks are gone).

## 3. What to report back

1. Per module: imports added, private copies deleted (count/lines), build time.
2. The decision on `Defs/Gamma1.lean` (created or not, and why).
3. Any declaration that had to move to `QExpansionCoeff`/`DiscPow` instead of `Gamma`, and
   the SET-W1/W2 file it was taken from.
4. The `--blocks` before/after figure and the checker delta.
5. Any build that hit its bound.
