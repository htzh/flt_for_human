# SET MS-6 — the ratio dictionary and the index bound, and cusp decay under integrality

**Status: landed (2026-10-28), sixth order of ready shelf 1** (finished on the resume, after the
pause). Ready shelf 1 ([TOPIC-ready-shelf-1.md](TOPIC-ready-shelf-1.md)) §0.4 **U6 + U8**, §1, §2,
§3, §4; brief [WORKORDER-MS6-ratio-and-decay.md](WORKORDER-MS6-ratio-and-decay.md) — with the §-note
correction that U8's engine was already in the port (`Analytic/ANb.lean`).

| row | silo | home | checker | promotion (§9.1) |
|---|---:|---|---:|---:|
| `exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC` | 166 | insert `X1/CoeffMap.lean` (+24) | 93 → **94** | — |
| `finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index` | 442 | **new** `X1/FunctionFieldIndex.lean` (334 lines) | 1 ok | → **3 ok** |
| `eventually_norm_slash_le_of_isIntegral_adjoin_jqModC_inv_pow` | 734 | **new** `Analytic/CuspDecay.lean` (505 lines) | 1 ok | → **14 ok** |

| figure | priced | measured |
|---|---:|---:|
| rows / silo | 3 / 1,342 | 3 / 1,342 |
| net new math lines | ≈905 (U6 354 + U8 551) | **≈880** — U6 is +24 (166) and 334 (442) lines; U8 is 505, below its 551 because the `ANb` engine was reused (§0.2's correction) |
| declarations | 20 + 16 + 53 pin | 3 (442) + 14 (734) + 1 (166) |
| imports | 166: 1; 442: 6; 734: 5 | 166: 1; 442: **7** (+`X1/FunctionFieldIsAlgClosed`); 734: **6** (+`Analytic/ANb`) |

## 0. What landed

- **166** — appended to `X1/CoeffMap.lean`: the row is **one line**, `RatioFieldOfGroup.isRatio_of_mem
  hT hx`, because the ratio-field dictionary was already in the module (line 647) as the engine of
  the `_of_T_mem` twin (line 669). Statement verbatim, including the `[Γ.FiniteIndex]` and the
  `GL (Fin 2) ℝ`-coerced forms. The host's 93 verdicts are untouched.
- **442** — `X1/FunctionFieldIndex.lean`: the pin's *finrank* transfer (`transfer_finrank`, not in the
  port — the port's `QExpBaseChange.transfer` is the *existence* transfer from the
  `of_isAlgClosed` file, a different pin statement) and `bound_of_isAlgClosed`; the pin's
  Transfer/Residue/CharZero block is **imported** from `X1/FunctionFieldIsAlgClosed` (MC-3's module),
  and so is `Φ_injective` — the brief's warning that the port's `Φ_injective` was a different map is
  stale: the MC-3 module has the right one.
- **734** — `Analytic/CuspDecay.lean`: the decay block (`coeffEmb_jq_eq_jqModC`, `coeff_one_mul`,
  `coeff_zero_mul`, the `qA0`/`qB0`/`qA1`/`qB1`/`qD1` block, `A_cube_sub_B_sq`, `J_mul_D`,
  `J_sub_mul_D`, `order_le_of_identity`, `Jinv_mul_A_cube`, `ev`/`slash_coe_apply`/
  `levelOne_apply_smul`, `tendsto_nice`, `norm_le_of_monic_relation`, `coreC`) on top of the
  **imported** `ANb` engine — `Nice`/`niceSubalgebra`/`toC`/`qexpHom`/`ψ`/`ofMF`/`nice_of_modularForm`/
  `an`/`𝔞` are not restated (no new `Nice`; the port has two already).

## 1. Gates, as measured

| gate | result |
|---|---|
| `check_port --force` | **94** / **1** / **1** ok, each `0 mismatch / 0 missing / 0 own` |
| `#print axioms` | all three `[propext, Classical.choice, Quot.sound]` |
| builds (workspace lock) | `CoeffMap` 52 s; `FunctionFieldIndex` 22 s (4,459 jobs); `CuspDecay` 14 s (3,990 jobs) — all `exit=0` |
| edit loop (200k cap) | `CoeffMap` silent; `CuspDecay` silent (15 s, zero warnings); **`FunctionFieldIndex` needs ≈240k** — see §2 |
| `dedup.py --module … --within --tier shape` | 0 clusters in all three |
| `set_option` | none beyond the project-universal `autoImplicit false`; **no cap copied** (the pin's 6.4M/1.6M on 442 and 3.2M on 734 stay out) |

## 2. The one gate not met: 442's edit-loop cost (the open item)

`transfer_finrank` needs ≈**240,000** heartbeats — 0 errors at 240k/250k, fails at 230k/200k — and the
pin's `maxHeartbeats 6400000` + `synthInstance.maxHeartbeats 1600000` sit on exactly that
declaration. Nothing is capped in the module: it builds under the lakefile's cap, the checker reads
3 ok, the axioms are clean and the warnings are zero. What is not met is the port's 200k
**edit-loop** discipline.

The diagnosis (done by the worker with `sorry`-cut probes, all in `tmp/`, deleted):

- everything through `hrankN` fits 200k in 9 s; the whole overrun is the final ~20-line transport —
  `let e₂ : N₁ ≃+* Fk := RingEquiv.refl Fk`, `hcomm`, and `Module.Finite.of_equiv_equiv` /
  `Algebra.finrank_eq_of_equiv_equiv`;
- the instance trace locates it in recurring base-change searches over `IntermediateField` subtypes
  (`Module ↥K₁ ↥S` ≈3,300 trace lines ×5, `Module ↥K₁ ↥(N₁.toSubalgebra)` ≈3,700,
  `Algebra k ↥K₀` ≈1,100 ×3, and a *failing* `Nonempty (Fin n)` search ≈2,900).
- tried and rejected: local `haveI` bricks (2.5× faster but the kernel's defeq check breaks on
  `Module.Finite.span_of_finite` and on `hcomm`'s `change` — two distinct non-defeq instances);
  extracting the transport into a small-context lemma (typechecks, no gain at the call site);
  type-ascribing `algebraMap` in `hcomm` (no gain). All reverted.

The next move, recorded for whoever picks it up: prove `FiniteDimensional K₀ Fk ∧ finrank K₀ Fk ≤ n`
from `hrankN` by `IntermediateField`-level rewriting (`N₁` and `Fk` share their carrier;
`K₀.map val = K₁`) and drop the `RingEquiv.refl`/`hcomm`/`of_equiv_equiv` detour entirely — that is
where all the remaining inference lives.

## 3. Deviations

1. **442 imports `X1/FunctionFieldIsAlgClosed`** — the brief's six-file list omits it, but the
   residue/Transfer block it says to reuse lives there (`FunctionFieldResidue`/`FunctionFieldDegree`
   do not import it). No mathlib import beyond the brief.
2. **734 imports `Analytic/ANb`** (the §-note correction): the pin's 734 lives in namespace `ANb`, and
   the port's `Analytic/ANb.lean` is that namespace. Not redefining `Nice` was the point.
3. **734's two inference fixes** (how the pin's 3.2M cap was avoided): the pin's `M = 0` branch does
   `subst hM` over ~40 hypotheses and then a context-wide `simp only … at hT hCη` plus `nlinarith` —
   that one branch was the whole blow-up; it is replaced by `simpa [hM]`-extracted facts and
   hypothesis-limited `nlinarith only [hCη0]` / `linarith only [h1, h2, h3]`. Eleven `positivity`
   calls under the same 40-hypothesis context became explicit `mul_nonneg`/`pow_pos`/`pow_nonneg`
   terms (28 s → 15 s). The pin's unused `hm`/`hh` are referenced by `have _hm : 1 ≤ m := hm` /
   `have _hh : h ≠ 0 := hh` rather than any linter suppression.
4. **442's six `haveI` sites** use the term-mode pattern `refine (haveI : X := e; ?_)` (and
   `refine (letI := …; ?_)`), which is what keeps the file at zero warnings without suppression;
   `hSrank`'s `by simp` became `by rw [Fintype.card_fin]`.

## 4. What these rows unlock

- 442 — the mod-ℓ block: `exists_xHDRModelAtP_atkinLehner_generic_chart` (2,368) and the
  `XHDRModelAtP` minimal-primes rows (1,819 / 1,544 / 1,474 / 1,465).
- 166 — the place-order/slash block: `exists_ringHom_place_order_eq_mul_ord_of_qExpansion_slash`
  (1,286), `ord_eq_neg_width_…` (1,077), `exists_tendsto_realizeOf_smul_of_forall_ord_eq_zero`
  (1,073), `exists_isBigO_slash_realizeOf_mul_deriv_…` (1,028).
- 734 — `exists_cuspForm_qExpansion_eq_mul_thetaL_pow_of_isIntegral_qExpFunctionFieldC` (233).
- The consumer zone's `[ratio]` and `[decay]` zones ([spec/ModularCurveReady1Consumer.lean](../../spec/ModularCurveReady1Consumer.lean)
  zones E and F) consume the three: 442 at `Γ' = Γ`, 166 with its existential unpacked, and 734 at
  the trivial twist `A = 1`.
