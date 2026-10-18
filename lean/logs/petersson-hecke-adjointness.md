# The Petersson adjointness of `T_p` on a nebentypus component — `peterssonOn_hecke_eq_conj_mul_of_hasNebentypus`

**Status: landed 2026-10-17.** Four modules, checker `9857 → 9877 identical (+20)`, 0
mismatched / 0 missing; the headline is `#print axioms`-clean
(`[propext, Classical.choice, Quot.sound]`).

| module | role | lines | declarations |
|---|---|---:|---:|
| `ModularForms/Analytic/Petersson.lean` | def layer: `peterssonOn` | 46 | 3 (wired) |
| `AutomorphicForm/UpperHalfPlane/ModularFundamentalDomain.lean` | def layer: `goodSet`/translate identities | 269 | 16 (wired) + 6 `private` cut helpers |
| `ModularForms/Analytic/PeterssonHecke.lean` | tier-3 engine | 1,368 | 118 (registered) |
| `ModularForms/Analytic/PeterssonHeckeTheorems.lean` | tier-1 façade | 30 | 1 (the headline) |

| | |
|---|---|
| statement | `⟨T_p f, g⟩ = conj ε(p) ⟨f, T_p g⟩`, `T_p f = heckeU k p f + ε(p) • (f ∣ heckeDiagMatrix p)` |
| pin source | `P2M/Sol/S_CuspForm_peterssonOn_hecke_eq_conj_mul_of_hasNebentypus.lean` (1,230 lines, 118 development declarations + `solution`, none `private`) |
| statement authority | `Theorems/Thm_CuspForm_peterssonOn_hecke_eq_conj_mul_of_hasNebentypus.lean` |
| consumers | 2 in the D-S cone: `CuspForm.exists_basis_hasNebentypus_qCoeff_hecke_eigen` (864), `CuspForm.conj_heckeEigenvalue_eq_of_hasNebentypus` (269) |
| build | engine edit loop ~10 s; module builds 3–4 s each |

## 1. Where it is homed, and why

Mathlib `v4.34.0` already has the **pointwise** Petersson density
(`Mathlib/NumberTheory/ModularForms/Petersson.lean`, `UpperHalfPlane.petersson`) and the slash
and coset API. The pin's `Definitions/Def_CuspForm_PeterssonOn.lean` is 31 lines of glue: the
coset sum over `SL(2, ℤ) ⧸ Γ` and its integral over `volume.restrict 𝒟`. The FLT content is the
adjointness proof itself, so the module lives under our `ModularForms/` (beside the Hecke column,
`HeckeNebentypus.lean`, `HeckeEigenNebentypus.lean`), not under the pin's consumers in
`ModularCurve/`. This is **not** a mathlib supplement (contrast
[logs/hahn-series-alg-closed.md](hahn-series-alg-closed.md)): the definition wraps mathlib, and
the theorem is FLT's analytic Hecke theory.

## 2. The definition layer, and the one cut

The statement's vocabulary was already ported and wired: `heckeU`, `heckeDiagMatrix`
(`ModularForms/Defs/HeckeOperator.lean`), `CuspForm.HasNebentypus` (`HeckeNebentypus.lean`),
`CuspForm (Gamma1 N) k` (`Defs/PrimitiveFormGamma1.lean`). Missing were `peterssonOn` (31 lines)
and the proof's fundamental-domain ground.

`Definitions/Def_AutomorphicForm_ModularFundamentalDomain.lean` (217 lines) reaches a six-module
chain of 1,436 lines (`Gamma0ExactVolume` 176, `FundamentalDomainExactVolume` 236,
`EisensteinScattering` 278, `L2ProductionInstance` 111, `L2AutomorphicCarrier` 147,
`TruncatedDomainPartition` 488) for five facts only:

- `volume_fd_diff_fdo`, `volume_fdo_eq_volume_fd` — from `Gamma0ExactVolume`;
- `volume_fd_eq`, `gate_volume_ne_zero` — from `FundamentalDomainExactVolume`;
- `measurableSet_smul_fd` — from `L2ProductionInstance`.

The port carries the first two and the last as `private` helpers (short measure-theory proofs over
the already-ported `FundamentalDomainVolume`/`HyperbolicMeasure`), wires the module's other **16**
public declarations verbatim, and defers the four gate theorems plus the whole chain in
[CARRY-FORWARD.md](../CARRY-FORWARD.md). The cut is justified by measurement: over the 1,396
needed rows of `frontier.py --ds --include-leaves --list`, **no needed D-S node imports any of the
six directly**; they are reached only through `ModularFundamentalDomain`, which three needed nodes
use (this row plus the two `norm_sq` rows).

## 3. The proof and its adaptations

The pin's 118 declarations are taken whole, all public (policy: no pin-public demotion), each with
its `-- pin:` provenance comment; the module is tier 3 and the register lists all 118 with pin
originals. The proof unfolds `peterssonOn` (`petersson_sum_left`/`petersson_sum_right`), rewrites
the Hecke double coset as the `Option (Fin p)` representatives `rr`, reindexes the coset sum over
`Lam N p` (`unfold_sum`), and applies `integral_cosum_pair` with the character identity
`ε(p)⁻¹ = conj ε(p)` (`norm_char_p`).

`v4.34.0` adaptations (five, no statement change):

1. `det_heckeMatrix` is `private` in the port's `Defs/HeckeOperator.lean`, so the engine proves it
   locally from the public `val_heckeMatrix` (the pin's two-line proof).
2. `MulChar.unit_norm_eq_one` → `DirichletCharacter.unit_norm_eq_one` (`norm_char_p`).
3. `if_pos` → `ite_eq_left` (deprecation, two sites).
4. `dvd_sandwich_01` / `dvd_sandwich_10`: apply the `mul_apply_*` lemmas **before** rewriting
   `gInf_inv_coe`. Rewriting first puts the Subtype-typed explicit matrix into a product, and
   `v4.34.0`'s implicit transparency then rejects the product as ill-typed.
5. Three `haveI` lints: `Lam_finiteIndex` uses `have hN : NeZero (p * N)`; `exists_rr_mul_mem`
   keeps `haveI : Fact p.Prime` (load-bearing for `field_simp`) under a local
   `set_option linter.style.haveILetI false in`; the `Countable (SL(2, ℤ) ⧸ Λ)` instance is
   inherited from the cut module.

The engine is unlisted, so the checker does not diff it; a last-name/statement comparison with the
checker's own parser gives **118/118 matches, 0 differences** (`solution` skipped). The one
apparent difference, `rr`, is the known register/parser artifact: `def rr` is equation-style, so
the checker's statement cut runs to the next `:=` and absorbs the following `-- pin:` line
([CARRY-FORWARD.md](../CARRY-FORWARD.md), "known issues").

## 4. Reproduce

```sh
cd lean
lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 \
    FLTForHuman/ModularForms/Analytic/Petersson.lean
lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 \
    FLTForHuman/AutomorphicForm/UpperHalfPlane/ModularFundamentalDomain.lean
lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 \
    FLTForHuman/ModularForms/Analytic/PeterssonHecke.lean
lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 \
    FLTForHuman/ModularForms/Analytic/PeterssonHeckeTheorems.lean
flock .lake/flt_build.lock timeout 300 lake build \
    FLTForHuman.ModularForms.Analytic.PeterssonHeckeTheorems
python3 spec/check_flt_statements.py          # 9877 identical
python3 tools/deps/unwired_register.py        # engine 118/118 pin originals
```
