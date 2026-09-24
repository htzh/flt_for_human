# Topic m7 — the Laurent/`coeffEmb` glue and the two relative-degree theorems (M4)

**Status: work order drafted (pending the SET-M2 dispatch/review).** First topic
of [SET-M3](SET-M3.md). Read [SET-M1](SET-M1.md) §2–§3 first.

**Goal.** Two modules:

- `FLTForHuman/ModularCurve/Degree/LaurentGlue.lean` — the eight short nodes.
- `FLTForHuman/ModularCurve/Degree/Relfinrank.lean` — `relfinrank_laurentBaseChange`
  and `relfinrank_qExpand_full`.

**Two nodes of this group were delivered early by m1** (they are the pin's private
Hecke-operator prelude and are themselves wrapper targets): do **not** write
`laurentBaseChange_mono` or `qExpand_mem_laurentBaseChange`; import them from
`Defs/HeckeOperator.lean` and register their wrappers in `SOURCES`.

## 1. The eight short nodes

| node | content | route |
|---|---|---|
| `ModularCurve.coeffEmb_jq (L)` | 19 | `coeffEmb L jq = jqModC L`; unfold `coeffEmb = coeffMap (algebraMap ℚ L)` and `jqModC`; `jqModC_rat` is `rfl` |
| `ModularCurve.coeffEmb_jqN (L) (N)` | 19 | `coeffEmb L (jqN N) = jqNModC L N`; the previous + the ported `coeffEmb_qExpand` |
| `ModularCurve.order_qExpand {R} (N) (f)` | 19 | `(qExpand R N f).order = N * f.order`; HahnSeries order under the monomial reindexing |
| `ModularCurve.order_coeffEmb (L) (x)` | 15 | `(coeffEmb L x).order = x.order`; `algebraMap ℚ L` injective |
| `ModularCurve.laurentBaseChange_adjoin (L) (S)` | 22 | `laurentBaseChange L (adjoin ℚ S) = adjoin L (coeffEmb L '' S)`; unfold both sides and commute image/adjoin |
| `ModularCurve.laurentBaseChange_modularFunctionField (L) (N)` | 30 | `= modularFunctionFieldC L N`; both are `adjoin {coeffEmb jq, coeffEmb (jqN N)}`, then `coeffEmb_jq`/`coeffEmb_jqN` |
| `ModularCurve.laurentBaseChange_modularFunctionFieldFull (L) (N)` | 10 | `= adjoin L {x | ∃ d, NeZero d ∧ d ∣ N ∧ x = jqNModC L d}`; the full field is `adjoin {jqN d | d ∣ N}` |
| `ModularCurve.transcendental_jqN (N)` | 10 | `Transcendental ℚ (jqN N)`; `jqN N = qExpand ℚ N jq`, `qExpand` injective, ported `transcendental_jq` |

Statements verbatim from the wrappers (quoted in SET-M3 §2's predecessor order
files; re-quote from `Theorems/Thm_ModularCurve_<node>.lean`).

## 2. `relfinrank_laurentBaseChange` (265 content)

Wrapper: `(L) [Field L] [Algebra ℚ L] (F₀) (t) (ht : t ∈ F₀)
(htr : Transcendental ℚ t) : relfinrank (adjoin L {coeffEmb L t})
(laurentBaseChange L F₀) = relfinrank (adjoin ℚ {t}) F₀`.

The pin's `TransportDev` block (all `private` here): `K₀`, `K`, `K₀_le`, `K_le`,
`coeffEmb_aeval`, `coeffEmb_mem_K`, `E₀`, `E`, `φ`, `ψ`, `coe_φ`, `coe_ψ`,
`ψ_compat`, `isAlgebraic_coeffEmb`, `laurentBaseChange_eq_adjoin`,
`restrictScalars_adjoin_K`, `closure_image_eq`, `mem_span_image`, `mem_span_range`,
`finite_and_finrank_le`, `linearIndependent_pow_mul`, `exists_common_denom`,
`linearIndependent_ψ`, `relfinrank_eq`; then `relfinrank_laurentBaseChange`.
Note the pin also defines `relfinrank_laurentBaseChange_full`,
`relfinrank_restrictScalars` and `relfinrank_full_prime` in the same file;
`relfinrank_full_prime` is **not a target and needs m5's
`finrank_adjoin_jqNModC_eq_of_prime`**, so **omit it** (and its two helpers
unless the main proof uses them). The main proof goes through `relfinrank_eq`
alone — verified against the pin: `solution` is
`TransportRows.relfinrank_laurentBaseChange L F₀ t ht htr`.

Seam: mathlib `IntermediateField.relfinrank`/`extendScalars`/`restrictScalars`/
`relfinrank_eq_finrank_of_le`, `Module.Free.chooseBasis`,
`Module.finrank_of_not_finite`. **Scout `relfinrank_eq` first** (the linear
independence of `ψ`'s image is the hard half).

## 3. `relfinrank_qExpand_full` (631 content)

Wrapper: `(N ℓ) [NeZero N] [Fact (Nat.Prime ℓ)] :
relfinrank ((modularFunctionFieldFull N).map (qExpandₐ ℓ)) (modularFunctionFieldFull (N * ℓ))
= if ℓ ∣ N then ℓ else ℓ + 1`.

The pin's file carries the ~370-raw-line `TS`/`conj`/`phiAtSeed`/`roots_prime_at_slot`
prelude at its head (lines 32–~400). **All of it is ported** — import it and do
not write it. The genuinely new block is:

- private `jqN_congr`, `g2_relfinrank_union_left`, `g2_coeffEmb_injective`,
  `g2_zeta_mod`, `g2_seed_eq`, `g2_y0_eq`, `g2_twist_fix`;
- private `ModularCurve.finrank_adjoin_jq_of_subset_range_qExpand` (≈73 lines)
  and `..._of_mem` (≈158 lines);
- private `ModularCurve.relfinrank_qExpand_full` (≈77 lines) and the solution.

Inputs (all ported): `PhiGen_splits_prime_at_slot`, `exists_phiIrreducible_evalSymm`,
`finrank_adjoin_jqN_eq_dedekindPsi`, `jqN_prime_not_mem_full`,
`modularFunctionField_eq_full`, `coeffMap_qExpand`, plus the ported `phiAtSeed_jqN_eval`
/`phiAtSeed_eval_symm`. Verify with `grep -c` that no prelude declaration is
re-declared.

## 4. Verification

- Append the 10 wrappers to `SOURCES`; the two modules to `PORT_FILES`.
- checker 0 mismatched / 0 missing.
- `#print axioms` on `relfinrank_qExpand_full` and `relfinrank_laurentBaseChange`.
- Consumer Zone: `relfinrank_qExpand_full` at `N = 1`, `ℓ = 2`;
  `coeffEmb_jq`/`coeffEmb_jqN` at `L = ℂ`.

## 5. Budget

**3 goal rounds.** Round 1: the eight short nodes. Round 2:
`relfinrank_laurentBaseChange` (scout `relfinrank_eq`). Round 3:
`relfinrank_qExpand_full`, log/README/consumer.

**Stop early on**: `relfinrank_eq`'s linear-independence argument needing a
mathlib statement the pin does not reach; a prelude declaration genuinely absent
from the port (write it `private`, record); or a statement mismatch.

## 6. Reporting back

1. Module/line/decl table and checker before/after.
2. **The prelude drop**: `grep -c` of the ported prelude names in the two
   modules (imports only), and the new-line count of `relfinrank_qExpand_full`
   after subtracting the prelude.
3. `relfinrank_eq`/`linearIndependent_ψ`: the route and where it bit.
4. `finrank_adjoin_jq_of_subset_range_qExpand{,_of_mem}`: structure and inputs.
5. Promotion candidates (any generic helper written `private`).
