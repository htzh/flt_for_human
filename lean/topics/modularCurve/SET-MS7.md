# SET MS-7 — the toric-point dictionary at both levels, and `Φ = Φ₂`

**Status: landed (2026-10-28), seventh order of ready shelf 1.** Ready shelf 1
([TOPIC-ready-shelf-1.md](TOPIC-ready-shelf-1.md)) §0.4 **U4 + U5**, §1, §2, §3, §4; brief
[WORKORDER-MS7-toric-and-phi-two.md](WORKORDER-MS7-toric-and-phi-two.md). Three rows, two new
modules, **no manager lane** (the lane — the `XHDiamondModL` gate and the `qExpansion_E6_eq_map_mk`
promotion — had landed earlier as [SET-MSDEF.md](SET-MSDEF.md)).

| row | silo | home | checker | promotion (§9.1) |
|---|---:|---|---:|---:|
| `exists_qExpFunctionFieldC_gammaH_bot_coe_eq_toricPoint_pow_and_diamondPullbackModL_apply_eq` | 373 | **new** `TateSlots/ToricPointDictionary.lean` (519 lines) | 2 ok (with 168) | → **38 ok / 7 mismatch** |
| `c4_mul_toricPoint_fst_div_c6_mem_qExpFunctionFieldC_gamma1` | 168 | same module | (counted above) | — |
| `ModularPolynomialData.phi_eq_phiTwo` | 410 | **new** `ModularPolynomialLevelTwo.lean` (501 lines) | 1 ok | → **34 ok / 0 / 0** |

| figure | priced | measured |
|---|---:|---:|
| rows / silo | 3 / 951 | 3 / 951 |
| net new math lines | ≈780 | 780 (the two `Def_`-free rows' declaration lines, in-port 33) |
| definitions needed | `XHDiamondModL` 37 + the promotion | **landed before the order** (SET-MSDEF) |
| imports | 5 + 4 port modules | as briefed, **no addition** |

## 0. What landed

- **`TateSlots/ToricPointDictionary.lean`** — the two heads of the toric dictionary: the Γ₁-level
  membership of both Tate-slot ratios (`c₄(1+12x)/c₆`, `(x+6x²+2a₄)/c₄`) in
  `qExpFunctionFieldC K (Γ₁ M)` (168), and the Γ_H-level dictionary `w₁`/`w₂` with their formulas and
  the `ρ`-equivariance `ρ γ (wᵢ t) = wᵢ (t · (gamma0Units M γ)⁻¹)` under `IsDiamondPullbackModL K M ⊥ ρ`
  (373-XH). The pin's `W769` engine (the `Field` section) is transcribed once.
- **`ModularPolynomialLevelTwo.lean`** — `data.Φ = phiTwo` for every `ModularPolynomialData 2`: the
  pin's `PhiTwoCalc` coefficient computation (`LowCoeffs`/`conv`/`NF`/`LJ`/`L2`/`nf_*`, `eval`,
  `cubic_expand`, `coeff_identities`, `phiTwo_coeff`, `natDegree_phiTwoC`,
  `qExpand_evalAtJ_phiTwoC`), then the identification.

## 1. Gates, as measured

| gate | result |
|---|---|
| `check_port --force` | ToricPointDictionary **2 ok**, ModularPolynomialLevelTwo **1 ok**, each `0 mismatch / 0 missing / 0 own` |
| `#print axioms` | all three `[propext, Classical.choice, Quot.sound]` |
| builds (workspace lock) | ToricPointDictionary green; ModularPolynomialLevelTwo 4,043 jobs, `exit=0` |
| edit loop (200k cap) | silent, zero warnings, both |
| `dedup.py --module … --within --tier shape` | 0 clusters (before the surface pass) |
| `set_option` | only the project-universal `autoImplicit false`; the pin's 3.2M heartbeat cap on 410 was **not** copied |

## 2. Deviations

1. **410's pin cap refused.** The pin's `S_` carries `set_option maxHeartbeats 3200000` around the
   coefficient computation; the port ran it at the 200k edit cap without it (FR-0067), which is the
   strongest evidence yet that the pin's caps are defensive rather than necessary.
2. **The three coefficient declarations had to be written** — `natDegree_phiTwoC`, `phiTwo_coeff`,
   `evalAtJ_phiTwoC`: the port's `Defs/ClassicalModularPolynomials.lean` has `phiTwo` and
   `phiTwoC2/C1/C0` only. (The pin spells the third `qExpandand_evalAtJ_phiTwoC`; the port drops the
   typo — a private helper name, no wire.)
3. **Surface pass**: 34 of 36 declarations in `ModularPolynomialLevelTwo` are pin-faithful public
   statements and were promoted (`getD_map_intCast`/`conv_map_intCast` kept private — direct-name
   mismatches); `ToricPointDictionary` reads 38 ok / 7 mismatch with `private` dropped, and its
   promotion was **not** applied — the seven mismatches are the pin's binder re-spellings and are
   recorded in the module header instead, because the two headlines' wire is what the order owes.

## 3. What these rows unlock

- 373-XH: `exists_algHom_qExpFunctionFieldC_gammaH_bot_comp_eq_iff_and_comp_diamondPullbackModL_of_transcendental_j`
  (1,071) — the Γ_H slot/`DiamondPullbackModL` dictionary.
- 168: `exists_algHom_qExpFunctionFieldC_gamma1_comp_eq_of_map_eq_or_eq_neg` (950).
- 410: `isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_lt_five` (660), and (as the
  re-read shows) the ready row `ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient2_j` (28).
- The consumer zone's `[toric]` zone ([spec/ModularCurveReady1Consumer.lean](../../spec/ModularCurveReady1Consumer.lean)
  zone D) consumes the Γ_H row by unpacking its existential to the two coordinate clauses.
