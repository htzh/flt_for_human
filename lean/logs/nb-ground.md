# NB ground: the Atkin–Lehner datum and the nebentypus promotions

2026-10-25. Manager prep for the alSlash / twin-headline cluster
(`ModularForm.isZeroAt_alSlash`, `ModularForm.mdifferentiable_alSlash`,
`CuspForm.norm_qCoeff_sq_eq_pow_of_isPrimitiveForm_of_not_sq_dvd`,
`CuspForm.qCoeff_sq_eq_mul_zpow_or_exists_hasNebentypus_qCoeff_hecke_eigen_of_dvd_of_not_sq_dvd`).
Both headline nodes' frontier cones are 9 nodes with 3 needed, and the needed pair is shared — so
the cluster is one wave with one prelude, not four ports.

## 1. What the two "twins" actually are

Measured by chunking both files at declaration boundaries and hashing each body after normalising
the prime name (`ℓ` ↔ `p`), rather than by `diff` line counts:

| | |
|---|---|
| declarations | A 67, B 66, **66 in common** |
| byte-identical after the rename | **63 of 66**, 1,175 of A's 1,321 lines |
| identical up to the rename (flagged only by compound names `hℓ`, `bℓ`, `M / ℓ`) | `datum`, 14 lines |
| genuinely different | `main` (A 88 lines, B 73), `solution` (A 7, B 19) |
| only in A | `coe_ne_zero_of_qCoeff_one`, 6 lines |

So the *code* is 1,189 of 1,321 lines, and the two heads are short assemblies over it (A's `main`
is a sequence of `heckeU_eq_smul_of_qCoeff`, `hasNebentypus_trForm`, `phi_eq_smul_of_qCoeff`,
`alSlash_phi`, `phi_add`, `alSlash_smul`, `phi_smul` calls). The statements differ:
A is the norm identity `‖qCoeff g ℓ‖ ^ 2 = ℓ ^ (k - 2)` for a primitive form; B is the disjunction
`qCoeff f p ^ 2 = ε'(p) · p ^ (k - 2) ∨ ∃ g` at level `M / p`, with `U_p`/`T` eigen-hypotheses.
Two theorems, one proof.

The two *premise* files are a true twin: identical 24-declaration lists, 306/307 lines, differing
only in which alSlash lemma is the headline.

## 2. The checker does not obstruct the arrangement

Verdicts are computed on **port** declarations only. Porting the shared block once (in A's spelling,
which costs nothing: A already uses `ℓ`) and giving B only its head means B's pin rows for the 63
shared declarations are simply never consulted. No `own:` rows, no duplication. The one rule that
matters is the reverse: do not put `Pkg`-style abbreviations or renamed binders into a *pinned*
statement — the hash is over statement text.

## 3. Laid: `ModularForms/Defs/AtkinLehnerDatum.lean` (195 lines, 25 ok)

Port of `Definitions/Def_ModularForm_AtkinLehnerDatum.lean` (157 lines): the `structure
AtkinLehnerDatum` (`R`, `hM`, `a`, `b`, `bezout`), `mat`/`det_mat`/`mat_sq`/`sqUnit`/`sqUnitSL`/
`sqUnitSL_mem`, `alGL` with `det`/`pos`/`σ`-triviality, `alGLQ`, and `alSlash` with `alSlash_def`/
`alSlash_add`/`alSlash_smul`. It generalises the port's hand-built `frickeGL M` (the case `q = M`).

Two deviations from the pin, both to the port's conventions: **no `import Mathlib`** — the port has
0 modules importing bare Mathlib and 904 that do not, so the imports are the four modules the file
actually needs (`UpperHalfPlane.Basic`, `GeneralLinearGroup.Basic`, `ModularForms.CongruenceSubgroups`,
`ModularForms.SlashActions`), which took the build from 170 s to **7.8 s**; and `if_pos` →
`ite_eq_left` for the v4.34 deprecation. 0 warnings, checker **25 ok / 0 mismatch / 0 missing**.

## 4. Laid: seven promotions, each diffed against its pin

| declaration | module | lines |
|---|---|---:|
| `phi` (def), `phi_props`, `phi_eq_smul_of_qCoeff`, `cusp_slash_T_pow` | `ModularForms/HeckeNebentypusFricke.lean` | 51 + 10 + 4 + 3 |
| `isBoundedAtImInfty_heckeU` | same (the `HeckeNebentypusExistence` copy stays `private`: same statement, would collide) | 9 |
| `T_mem_Gamma1` | `ModularForms/HeckeEigenNebentypus.lean` | 3 |
| `denom_ne_zero'` (the pin's `denom_SL_ne_zero`) | `DeligneSerre/Relevement.lean` | 5 |

Each module's header gains `spec-pin: P2M/Sol/S_CuspForm_norm_qCoeff_sq_eq_pow_of_isPrimitiveForm_of_not_sq_dvd.lean`
— the file those statements come from — so the promotions are *diffed*, not merely declared. That
line is the checker accommodation, and it is one line per module, not a copy of the code.

Effect on the headline's price, re-measured: the substitution list went from **8 importable + 7
port-private** to **15 importable + 0 private**. Before the promotions the 1,140-line headline could
only be written by re-stating seven helpers; now the whole prelude is importable.

## 5. Gates

| gate | reading |
|---|---|
| `lake build` the datum module | green, 7.8 s, 0 warnings |
| `lake build` the two promoted modules | green, 0 warnings |
| `check_port --force` on the three | 25 / 6 / 9 ok, 0 mismatch, 0 missing, 0 own |
| tree-wide `check_port --changed` | **5,514 ok, 0 mismatch, 0 missing, 31 own, 0 kw — 248 modules, exit 0** |
| `dedup.py` over the three | 0 clusters |
| `move_dead.py` on datum + Fricke | 0 declarations each |

## 6. Readiness

The cluster's remaining cost, measured: the alSlash calculus ≈ 280 net new (24 declarations, none
substituting), the shared headline block + A ≈ 1,140, B's head ≈ 150. Ground that is now paid:
the datum (≈130) and the promotions (≈85). Nothing else in either cone is unported — the two
premises are the last gate.
