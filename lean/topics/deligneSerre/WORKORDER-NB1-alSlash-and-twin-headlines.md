# WORKORDER-NB1 — the Atkin–Lehner slash, and two headlines over one proof

Status: **open**, dispatched 2026-10-25. Owner: the set's agent, reviewed by the manager.
Ground: [logs/nb-ground.md](../../logs/nb-ground.md) — the datum module is in the tree and the
seven nebentypus helpers are promoted, so every substitution this order needs is importable.

## 1. The nodes

| node | pin `S_` | raw | already in the port | new |
|---|---|---:|---|---:|
| `ModularForm.isZeroAt_alSlash` | `S_ModularForm_isZeroAt_alSlash.lean` | 307 | 0 | **≈280** |
| `ModularForm.mdifferentiable_alSlash` | `S_ModularForm_mdifferentiable_alSlash.lean` | 306 | **same development** | — |
| `CuspForm.norm_qCoeff_sq_eq_pow_of_isPrimitiveForm_of_not_sq_dvd` | `S_…_of_not_sq_dvd.lean` | 1,321 | 15 substitutions (150 lines) | **1,140** |
| `CuspForm.qCoeff_sq_eq_mul_zpow_or_exists_hasNebentypus_…` | `S_…_hasNebentypus_….lean` | 1,312 | same block; only the head differs | **≈150** |

All four are in the D-S needed set: the pair is −4 nodes / −3,246 raw (1,184 → 1,180 nodes,
446,334 → 443,088). They gate at least three further unported nodes
(`norm_qCoeff_sq_le_of_isPrimitiveForm`, `IsPrimitiveForm_pow_dvd_…`,
`IsEigenformWith_exists_changeLevel_…`), so this is a sub-development, not a leaf.

## 2. What the mathematics is

**Part 1, the slash calculus.** `AtkinLehnerDatum` (`ModularForms/Defs/AtkinLehnerDatum.lean`,
landed) supplies the Fricke matrix `mat` of determinant `q`, its square `mat * mat = q • sqUnit`
with `sqUnitSL ∈ Γ₀ M`, and the slash `alSlash W k f = f ∣[k] alGL`. The pin then builds:
`nonempty_of_prime_of_dvd_of_not_sq_dvd'` (a datum exists whenever `q ∣ M`, `q² ∤ M` — the Bézout
step), `isEmpty_four_two`, `isCusp_smul_of_rat'`, `isCusp_alGL_smul`, `exists_cocycle_al` (the
`1`-cocycle that makes the slash well defined on the level), `alSlash_slash`, `alSlash_mdiff`,
`alSlash_isBoundedAt`, `alSlash_isZeroAt`, the `scalarGL` def, `alSlash_alSlash`,
`alSlash_alSlash_two`, and the two wrappers.

**Part 2, the norm identity.** For `g` a primitive level-`M` form and `ℓ ‖ M`, the Fricke-twisted
combination `h = trForm W ℓ g` (`alSlash` plus `heckeU`) is again a nebentypus form, so `T_p h`
can be computed two ways; the norm `‖qCoeff g ℓ‖²` comes out as `ℓ^(k-2)`. The 63 shared lemmas are
that computation's pieces (`phi_props`, `phi_eq_smul_of_qCoeff`, `cusp_slash_T_pow`,
`isBoundedAtImInfty_heckeU`, `T_mem_Gamma1`, `denom_ne_zero'`, …) — all now public.

**Part 3, the nebentypus disjunction.** The same computation with `U_p`/`T` eigen-hypotheses gives
either the algebraic identity or a level-lowered eigenform at `M / p`; the difference from Part 2
is only in the two hypotheses blocks and the final case split.

## 3. Port once: the measured arrangement

The twin pair is *one* development. Chunked at declaration boundaries, 63 of 66 declarations are
byte-identical after normalising the prime name, and `datum` is too; the only genuinely different
declarations are `main` (88 vs 73) and `solution` (7 vs 19). So:

- **P1** — `ModularForms/AtkinLehnerSlash.lean` (new, wired to both premise pin files): the 24
  declarations of the pair, with **both** headlines (`alSlash_isZeroAt` and the `mdifferentiable`
  one) as public declarations. The pin's file is the same code twice; port it once.
- **P2** — `ModularForms/WeightOne/PrimitiveQCoeffNorm.lean` (new, wired to A's pin file): the shared
  63-declaration block **verbatim from A**, `main_of_isPrimitiveForm` (private), and A's headline.
- **P3** — `ModularForms/WeightOne/NebentypusQCoeffSq.lean` (new, wired to B's pin file): imports P2,
  adds `main_of_nebentypus` (private, 73 lines) and **B's headline only**. The 63 shared declarations
  are *not* re-declared: the checker's verdicts are computed on port declarations, so a pin row the
  module does not declare is never compared. No `own:` rows, no duplication.

**Statement fidelity.** A's block keeps A's spelling (`ℓ`); the checker hashes statement text and
never α-normalises bound variables, so this costs nothing and requires no markers. B's headline is
copied verbatim from `Theorems/Thm_CuspForm_qCoeff_sq_eq_mul_zpow_or_exists_hasNebentypus_…lean:9`.
Use `Pkg`-style abbreviations nowhere in a pinned statement.

## 4. Imports — do not restate

`ModularCurve.Defs.AtkinLehnerDatum` (the datum, `alGL`, `alSlash`); from P1's own module the
`alSlash` API; `ModularForms/HeckeNebentypusFricke.lean` (`phi` and its properties,
`cusp_slash_T_pow`, `isBoundedAtImInfty_heckeU`); `HeckeEigenNebentypus.lean` (`T_mem_Gamma1`);
`DeligneSerre/Relevement.lean` (`denom_ne_zero'`); `ModularForms/HeckePrelude.lean` (the ported
`periodic_of_slash_T`, `heckeDiagMatrix_mul_T`, `slash_heckeDiagMatrix_slash_T`, `cusp_bdd`);
`ModularForms/WeightOne/Defs/RatAt.lean` (`periodic_smul`); `Defs/PrimitiveFormGamma1.lean`
(`IsPrimitiveForm`); `WeightOne/Defs/GammaRational.lean` (`T_pow_mem_Gamma1`).

## 5. Build discipline

Single-module `lake build` only, never a tree build; every call inside the 2-minute rule, output
to `lean/tmp/`; serialize with `flock -w 900 /tmp/flt-build.lock`. Fix warnings (the datum module
needed `if_pos` → `ite_eq_left`; expect a few more deprecations in 2,600 lines). No `sorry`.

## 6. Gates

1. `lake build` each new module — green, 0 warnings, and the build output silent. Axioms are
   checked in a scratch file (`lean/tmp/axioms.lean`: import the module, then `#print axioms …`),
   never by a `#print axioms` line in the module itself — a top-level print runs on every build.
2. `spec/check_port.py --force` on the three modules — expect 0 mismatch and 0 missing, with the
   premise pair at 24 ok on one module and the headlines at 1 ok each on their own.
3. `frontier --target` on the four nodes → `needed 0`.
4. `dedup.py` and `move_dead.py` on the new modules; the block is one copy by construction, so
   `dedup` should be 0.
5. `spec/DsHeadConsumer.lean` gains a zone applying both headlines (at `k = 0` or `1`, `M = 2`,
   `ℓ = p = 2`, where `IsPrimitiveForm` is available from the ported level-one vocabulary), so
   deleting a headline breaks the consumer.
6. Report `--ds` before/after (expected 1,184 → 1,180 nodes) and update
   `topics/deligneSerre/TOPIC-weight-one-lifting-and-assembly.md`.

## 7. Result

**Landed, all three parts**, 2026-10-25. The long-form record is
[logs/nb1-alSlash.md](../../logs/nb1-alSlash.md).

| part | module | written | target | decls |
|---|---|---:|---:|---:|
| P1 | `ModularForms/AtkinLehnerSlash.lean` | **367** (290 of development: the pin's 280 + 10 for the `let δ` fix; rest header/wrappers) | ≈280 | 24 (21 public, 3 private) |
| P2 | `ModularForms/WeightOne/PrimitiveQCoeffNorm.lean` | **1,297** (1,223 of block, of which 1,189 byte-identical to A) | 1,140 | 71 (70 public, 1 private) |
| P3 | `ModularForms/WeightOne/NebentypusQCoeffSq.lean` | **138** | ≈150 | 2 (1 public, 1 private) |

**The block.** Chunked at `section API` … `end Main` (A pin lines 30–1306, 1,277 lines), the port
keeps **1,189 lines byte-identical**; every statement is A's text. The other 88 lines are four
kinds of proof-level change only: 59 lines removed because P1 carries `map_int_mul` and the
`scalarGL` group publicly and P2 imports them (this is what takes `dedup` to 0), seven
`let δ` hoists forced by Lean 4.34's `Membership.mem` transparency (see the log §5), one
`if_pos` → `ite_eq_left`, and two proofs delegated to the port (`T_mem_Gamma1`,
`periodic_of_slash_T`, 19 → 2 lines). P2 is 1,297 rather than 1,140 because the block was kept
whole: the promotion set stayed *available* but is not consumed by this wave, except the
19-line `periodic_of_slash_T` proof.

**B's 1,312 lines.** 1,174 of them are the shared block (its own copy), and the head is **138
lines** of port: the 64-line `main_of_nebentypus` plus the 17-line headline (rest: header and
local notation). Nothing of the block is re-declared in P3.

**Readings.**

| gate | reading |
|---|---|
| `lake build` P1 / P2 / P3 | green, 0 warnings each (5.3 s / 9.3 s / 4.2 s) |
| `#print axioms`, four headlines | `[propext, Classical.choice, Quot.sound]` |
| `check_port --force` P1 / P2 / P3 | **21 / 70 / 1 ok**, 0 mismatch, 0 missing, 0 own, 0 kw |
| `frontier --target`, four nodes | **needed 0** each |
| `dedup.py` over the three | **0 clusters** (99 declarations) |
| `move_dead.py --select dead` | 0 declarations each |
| `spec/DsHeadConsumer.lean` zone `[nb1]` | exit 0, 0 errors; fails (`unknown constant`) when a headline is renamed |
| `frontier --ds` | **1,180 nodes / 443,088 raw** (was 1,184 / 446,334) |

No `own:` rows and no `spec/decl_markers.tsv` edit were needed. The only wiring beyond the
order's plan: six `-- pin:` comments in P1 pointing at A's file for the helpers that are public
in P1 and imported by P2 (§4 of the log).
