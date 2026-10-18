# The Petersson adjointness of `T_p` on a nebentypus component — `peterssonOn_hecke_eq_conj_mul_of_hasNebentypus`

**Status: landed 2026-10-17.** Mathematics:
[../../../math/030-petersson-adjointness-of-hecke.md](../../../math/030-petersson-adjointness-of-hecke.md)
(the classical adjointness, the unfolding proof, and the two consumers). Four modules, checker `9857 → 9877 identical (+20)`, 0
mismatched / 0 missing; the headline is `#print axioms`-clean
(`[propext, Classical.choice, Quot.sound]`).

| module | role | lines | declarations |
|---|---|---:|---:|
| `ModularForms/Analytic/Petersson.lean` | def layer: `peterssonOn` | 46 | 3 (wired) |
| `AutomorphicForm/UpperHalfPlane/ModularFundamentalDomain.lean` | def layer: `goodSet`/translate identities | 269 | 16 (wired) + 6 `private` cut helpers |
| `ModularForms/Analytic/PeterssonHecke.lean` | tier-3 engine | 1,150 | 100 (registered) |
| `ModularForms/Analytic/PeterssonHeckeTheorems.lean` | tier-1 façade | 30 | 1 (the headline) |

| | |
|---|---|
| statement | `⟨T_p f, g⟩ = conj ε(p) ⟨f, T_p g⟩`, `T_p f = heckeU k p f + ε(p) • (f ∣ heckeDiagMatrix p)` |
| pin source | `P2M/Sol/S_CuspForm_peterssonOn_hecke_eq_conj_mul_of_hasNebentypus.lean` (1,230 lines, 118 development declarations + `solution`, none `private`) |
| statement authority | `Theorems/Thm_CuspForm_peterssonOn_hecke_eq_conj_mul_of_hasNebentypus.lean` |
| consumers | 2 in the D-S cone: `CuspForm.exists_basis_hasNebentypus_qCoeff_hecke_eigen` (864), `CuspForm.conj_heckeEigenvalue_eq_of_hasNebentypus` (269) |
| build | engine edit loop ~10 s; module builds 3–4 s each |

The headline, verbatim (the pin wrapper's statement, with the convention and the
operator of [math/030](../../../math/030-petersson-adjointness-of-hecke.md) §2–§3):

```lean
theorem CuspForm.peterssonOn_hecke_eq_conj_mul_of_hasNebentypus
    (N : ℕ) [NeZero N] (k : ℤ) (ε : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime)
    (hpN : ¬ p ∣ N) (f g : CuspForm (Gamma1 N) k) (hf : CuspForm.HasNebentypus ε f)
    (hg : CuspForm.HasNebentypus ε g) :
    CuspForm.peterssonOn (Gamma1 N) k
        (heckeU k p ⇑f + ε (p : ZMod N) • (⇑f ∣[k] heckeDiagMatrix p)) ⇑g
      = starRingEnd ℂ (ε (p : ZMod N)) *
        CuspForm.peterssonOn (Gamma1 N) k ⇑f
          (heckeU k p ⇑g + ε (p : ZMod N) • (⇑g ∣[k] heckeDiagMatrix p))
```

([`PeterssonHeckeTheorems.lean`](https://github.com/htzh/flt_for_human/blob/2d8e5c1/lean/FLTForHuman/ModularForms/Analytic/PeterssonHeckeTheorems.lean#L25-L37);
the pin's statement authority is
[`Thm_CuspForm_peterssonOn_hecke_eq_conj_mul_of_hasNebentypus.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_peterssonOn_hecke_eq_conj_mul_of_hasNebentypus.lean)).
Here `heckeU k p f` is the `U_p` of [math/030](../../../math/030-petersson-adjointness-of-hecke.md) §3,
`heckeDiagMatrix p` is `diag(p,1)`, and `starRingEnd ℂ` is complex conjugation.

**Façade note.** `PeterssonHeckeTheorems.lean` exists because the checker wires modules, not
declarations: it carries the pin wrapper's statement verbatim (+1) while the engine stays tier 3. It is a bridge, not a permanent home — when the checker gains per-declaration wiring
([CARRY-FORWARD.md](../../CARRY-FORWARD.md), "Checker: per-declaration wiring") the headline folds
into the engine and the façade is deleted.

## 1. Where it is homed, and why

Mathlib `v4.34.0` already has the **pointwise** Petersson density
(`Mathlib/NumberTheory/ModularForms/Petersson.lean`, `UpperHalfPlane.petersson`) and the slash
and coset API. The pin's `Definitions/Def_CuspForm_PeterssonOn.lean` is 31 lines of glue: the
coset sum over `SL(2, ℤ) ⧸ Γ` and its integral over `volume.restrict 𝒟`. The FLT content is the
adjointness proof itself, so the module lives under our `ModularForms/` (beside the Hecke column,
`HeckeNebentypus.lean`, `HeckeEigenNebentypus.lean`), not under the pin's consumers in
`ModularCurve/`. This is **not** a mathlib supplement (contrast
[../../logs/hahn-series-alg-closed.md](../../logs/hahn-series-alg-closed.md)): the definition wraps mathlib, and
the theorem is FLT's analytic Hecke theory.

## 2. The definition layer, and the one cut

The statement's vocabulary was already ported and wired: `heckeU`, `heckeDiagMatrix`
(`ModularForms/Defs/HeckeOperator.lean`), `CuspForm.HasNebentypus` (`HeckeNebentypus.lean`),
`CuspForm (Gamma1 N) k` (`Defs/PrimitiveFormGamma1.lean`). Missing were `peterssonOn` (31 lines)
and the proof's fundamental-domain ground.

The product is the pin's `peterssonOn`, a three-line wrapper over mathlib's pointwise density
(`UpperHalfPlane.petersson`):

```lean
def peterssonOnIntegrand (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f g : UpperHalfPlane → ℂ)
    (τ : UpperHalfPlane) : ℂ :=
  ∑ᶠ q : SL(2, ℤ) ⧸ Γ,
    UpperHalfPlane.petersson k (f ∣[k] (q.out⁻¹ : SL(2, ℤ))) (g ∣[k] (q.out⁻¹ : SL(2, ℤ))) τ

def peterssonOn (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f g : UpperHalfPlane → ℂ) : ℂ :=
  MeasureTheory.integral (MeasureTheory.volume.restrict ModularGroup.fd)
    (peterssonOnIntegrand Γ k f g)
```

([`Petersson.lean`](https://github.com/htzh/flt_for_human/blob/2d8e5c1/lean/FLTForHuman/ModularForms/Analytic/Petersson.lean#L27-L36)).
`ModularGroup.fd` is the standard fundamental domain 𝒟; the `finsum` over the quotient is the
coset sum of [math/030](../../../math/030-petersson-adjointness-of-hecke.md) §2.

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
[CARRY-FORWARD.md](../../CARRY-FORWARD.md). Those 16 are the double-counting ground the proof
needs: `goodSet`, the set of points at which exactly two translates of 𝒟 meet, and the translate /
integral identities (`tsum_indicator_smul_fd`, `setLIntegral_smul_fd`,
`tsum_setLIntegral_fd_smul`, `setLIntegral_fd_tsum_smul`, …). The cut is justified by measurement:
over the 1,396 needed rows of `frontier.py --ds --include-leaves --list`, **no needed D-S node
imports any of the six directly**; they are reached only through `ModularFundamentalDomain`, which
three needed nodes use (this row plus the two `norm_sq` rows).

## 3. The proof and its adaptations

The pin's 118 declarations are taken whole, all public (policy: no pin-public demotion), each with
its `-- pin:` provenance comment. 18 of them are the coset-integral layer the pin wrote twice; on
2026-10-18 they were moved to the wired definition layer
`ModularForms/Analytic/PeterssonCoset.lean` (see the successor topic), so this engine carries **100**
declarations, tier 3, and the register lists those 100 with pin originals. The proof unfolds `peterssonOn` (`petersson_sum_left`/`petersson_sum_right`), rewrites
the Hecke double coset as the `Option (Fin p)` representatives `rr`, reindexes the coset sum over
`Lam N p` (`unfold_sum`), and applies `integral_cosum_pair` with the character identity
`ε(p)⁻¹ = conj ε(p)` (`norm_char_p`).

The engine names corresponding to the mathematical steps of
[math/030](../../../math/030-petersson-adjointness-of-hecke.md) §5:

| math §5 | engine (`CuspForm.PetHeckeAdj`) |
|---|---|
| the `p+1` representatives, Λ | `Lam`, `rr`, `exists_rr_mul_mem`, `rr_mul_rr_inv_mem` |
| the unfolding | `unfold_sum` |
| Φ, Ψ | `Φ`, `Ψ` |
| the character identity (math §5.3) | `slash_heckeDiagMatrix_eq`, `Ψ_eq`, `norm_char_p` |
| the two integrands | `integrand_left`, `integrand_right` |
| the integral invariance | `integral_cosum_pair`, `adm_slash_α`, `adm_coe` |
| assembly | `main` |

`v4.34.0` adaptations (five, no statement change):

1. `det_heckeMatrix` was `private` in the port's `Defs/HeckeOperator.lean` when this engine
   landed, so the engine proved it locally from the public `val_heckeMatrix` (the pin's two-line
   proof). On 2026-10-18 the whole `det_*`/`denom_*` family was promoted to public — the pin has
   them public, and the `norm_sq` silo needs `det_heckeDiagMatrix{,_pos}` — and the engine's local
   copy was dropped.
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
checker's own parser gives **100/100 matches, 0 differences** (`solution` skipped; the 18 moved
declarations are diffed against `Def_CuspForm_PeterssonCoset.lean` by that module's +56). The one
apparent difference, `rr`, is the known register/parser artifact: `def rr` is equation-style, so
the checker's statement cut runs to the next `:=` and absorbs the following `-- pin:` line
([CARRY-FORWARD.md](../../CARRY-FORWARD.md), "known issues").

The successor set — the coset-space pairing this engine's technique does not cover (the pin
wrote its coset-integral layer a second time, whole, in `Def_CuspForm_PeterssonCoset.lean`) and
the two `norm_sq` leaves that need it — has its own handoff record:
[TOPIC-petersson-coset-and-level-prime-eigenvalue.md](TOPIC-petersson-coset-and-level-prime-eigenvalue.md).
Its mathematics is [math/030](../../../math/030-petersson-adjointness-of-hecke.md) §7.

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
python3 tools/deps/unwired_register.py        # engine 100/100 pin originals
```
