# Topic m6 — the Φ datum family and its degree tail (M5)

**Status: work order drafted (pending the SET-M1 review).** Second topic of
[SET-M2](SET-M2.md). Read [SET-M1](SET-M1.md) §2–§3 first.

**Goal.** Two modules:

- `FLTForHuman/ModularCurve/Degree/PhiData.lean` — the family, the squarefree
  existence, the `jqNModC` evaluation/integrality tail, and the prime
  generation facts.
- `FLTForHuman/ModularCurve/Degree/PhiDegree.lean` — `transcendental_jqModC`,
  `finiteDimensional_adjoin_jqNModC`, `finrank_adjoin_jqNModC_le`.

(`finrank_adjoin_jqNModC_eq_of_prime` is **m8**, after m5's restrict-scalars
identification and m7's glue.)

**Why this topic.** These 14 nodes are the cone's Φ input. **Five of them are
one-liners over the already-ported Φ_p effort** (verified, see below); four more
are short transcriptions (`eval_jqNModC_{mul_eq_zero,of_mul_eq_zero}` at ~30
content each, `isIntegral_jqNModC_mul` at 12,
`isIntegral_jqNModC_all_of_modularPolynomialFamily` at 47); the two real proofs
are `nonempty_modularPolynomialData_of_squarefree` and
`finrank_adjoin_jqNModC_le`. The point of the topic is to *verify* the one-liners
and record them, exactly as the FFG capstone collapsed.

## 1. The five one-liners (verified) and the four short proofs

| node | content | reduce to |
|---|---|---|
| `ModularCurve.exists_modularPolynomialData_evalSymm` | 31 | ported `exists_phiIrreducible_evalSymm` (`ModularPolynomialProperties.lean:138`), `PhiIrreducible` dropped |
| `ModularCurve.modularPolynomialFamily` | 29 | the same, universally |
| `ModularCurve.full_eq_of_prime` | 3 | `functionFieldGeneration_of_prime` + ported `functionFieldGeneration_iff_full_eq` |
| `ModularCurve.functionFieldGeneration_of_prime` | 8 | ported `Defs/Fields.lean` `gen_prime` (opposite orientation) |
| `ModularCurve.ModularPolynomialData.isIntegral_jqN` | 5 | `⟨data.toAdjoin, data.toAdjoin_monic, aeval_jqN_toAdjoin data⟩` |
| `ModularCurve.isIntegral_jqNModC_mul` | 12 | private `isIntegral_of_eval₂_eq_zero` + `eval_jqNModC_mul_eq_zero` |
| `ModularCurve.ModularPolynomialData.eval_jqNModC_{mul_eq_zero,of_mul_eq_zero}` | 29+32 | **not one-liners**: private `coeffMap_jqNModC`, `coeffMap_eval₂_jqNModC`, `eval₂_rat_of_data` over ported `coeffMap_qExpand`/`coeffMap_injective`, `data.eval_eq_zero`, `map_jqModC` (m2), `qExpand_qExpand` |

**The `eval_jqNModC_mul_eq_zero` proof is confirmed verbatim by the manager**
(2026-09-23, 3.9 s `lake env lean` probe against `Defs/JqCoeff.lean` +
`Defs/Jq.lean` + `Defs/Laurent.lean` + `Defs/PhiGen.lean`): the pin's three
private helpers (`coeffMap_jqNModC`, `coeffMap_eval₂_jqNModC`, `eval₂_rat_of_data`)
and the final `ℤ → ℚ → K` transport compile exactly as written. No API drift.
`_of_mul_eq_zero` is the same argument with `hsymm` replacing the `data.eval_eq_zero`
input (via `EvalSymm`).

**Claim to test, not assume.** For each row, the work order's first step is a
`grep -n` of the target in `FLTForHuman/` and a one-line `Scratch.lean` probe; if
a one-liner does not close by `exact`/short `rw`, prove it normally and record
the mismatch rather than transcribing the pin's long proof.

**First two rows confirmed by the manager (2026-09-23, 4.8 s `lake env lean`
probe against the built `ModularPolynomialProperties.lean`):**

```lean
example (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] :
    ∃ data : ModularPolynomialData ℓ, EvalSymm data.Φ := by
  obtain ⟨data, _, hsymm⟩ := exists_phiIrreducible_evalSymm ℓ
  exact ⟨data, hsymm⟩

example : ModularPolynomialFamily := fun ℓ _ hℓ => by
  have : Fact (Nat.Prime ℓ) := ⟨hℓ⟩          -- the Prop binds `[NeZero ℓ]` then `ℓ.Prime`
  obtain ⟨data, _, hsymm⟩ := exists_phiIrreducible_evalSymm ℓ
  exact ⟨data, hsymm⟩
```

Note the `Fact`/`NeZero` binder mismatch: `ModularPolynomialFamily` is
`∀ (ℓ) [NeZero ℓ], ℓ.Prime → …`, while `exists_phiIrreducible_evalSymm` wants
`[Fact ℓ.Prime]`; synthesize the `Fact` with `have` (not `haveI` — the port's
`linter.style.haveILetI` fires otherwise).

**Also confirmed by probe (3.7 s):** the two generation rows. Note `gen_prime`
returns `Gen p`, i.e. `modularFunctionField p = modularFunctionFieldFull p`, and
`functionFieldGeneration_iff_full_eq` is stated in the other orientation:

```lean
example {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) : FunctionFieldGeneration ℓ := by
  have : Fact (Nat.Prime ℓ) := ⟨hℓ⟩
  exact (functionFieldGeneration_iff_full_eq ℓ).mpr (gen_prime ℓ).symm

example {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) :
    modularFunctionFieldFull ℓ = modularFunctionField ℓ :=
  (functionFieldGeneration_iff_full_eq ℓ).mp (functionFieldGeneration_of_prime hℓ)
```

**And `ModularPolynomialData.isIntegral_jqN` (4.4 s):**
`⟨data.toAdjoin, data.toAdjoin_monic, aeval_jqN_toAdjoin data⟩` over
`open ModularCurve IntermediateField` (the `ℚ⟮jq⟯` notation needs the
`IntermediateField` namespace open, exactly as `Defs/Fields.lean` does).

The exact wrapper statements:

```lean
theorem ModularCurve.exists_modularPolynomialData_evalSymm (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] :
    ∃ data : ModularPolynomialData ℓ, EvalSymm data.Φ
theorem ModularCurve.modularPolynomialFamily : ModularPolynomialFamily
theorem ModularCurve.full_eq_of_prime {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) :
    modularFunctionFieldFull ℓ = modularFunctionField ℓ
theorem ModularCurve.functionFieldGeneration_of_prime {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) :
    FunctionFieldGeneration ℓ
theorem ModularCurve.ModularPolynomialData.isIntegral_jqN {N : ℕ} [NeZero N]
    (data : ModularPolynomialData N) : IsIntegral ℚ⟮jq⟯ (jqN N)
theorem ModularCurve.isIntegral_jqNModC_mul {K : Type*} [Field K]
    (F : IntermediateField K (LaurentSeries K)) {ℓ : ℕ} [NeZero ℓ]
    (data : ModularPolynomialData ℓ) (d : ℕ) [NeZero d] (hd : jqNModC K d ∈ F) :
    IsIntegral F (jqNModC K (d * ℓ))
theorem ModularCurve.ModularPolynomialData.eval_jqNModC_mul_eq_zero {ℓ : ℕ} [NeZero ℓ]
    (data : ModularPolynomialData ℓ) (K : Type*) [CommRing K] (d : ℕ) [NeZero d] :
    data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqNModC K d)).toRingHom (jqNModC K (d * ℓ)) = 0
theorem ModularCurve.ModularPolynomialData.eval_jqNModC_of_mul_eq_zero {ℓ : ℕ} [NeZero ℓ]
    (data : ModularPolynomialData ℓ) (hsymm : EvalSymm data.Φ) (K : Type*) [CommRing K]
    (d : ℕ) [NeZero d] :
    data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqNModC K (d * ℓ))).toRingHom (jqNModC K d) = 0
```

## 2. The two real proofs

**`nonempty_modularPolynomialData_of_squarefree`** (363 content; wrapper
`(N) [NeZero N] (hsf : Squarefree N) (hN : 1 < N) : Nonempty (ModularPolynomialData N)`).
The pin's private block: `squarefreeIndicator` + multiplicativity,
`dedekindPsi_eq_mul_apply`, `le_dedekindPsi`, `dedekindPsi_pos`;
`fibrePoly`, `monic_fibrePoly`, `natDegree_fibrePoly`,
`card_roots_fibrePoly_of_monic`; `compositeFibrePoly` + `monic_`/`natDegree_`;
`resLiftInner`/`resLiftOuter`/`resLiftOuterK`/`specializeAt` + their `map_`/
`eval_` lemmas, `natDegree_resLiftOuterK_le`; `biResultant`,
`fibrePoly_biResultant`, `coeff_fibrePoly`,
`eval₂_coeff_biResultant_eq_coeff_compositeFibrePoly`,
`coeff_biResultant_natDegree_mul_natDegree`,
`coeff_biResultant_eq_zero_of_natDegree_mul_lt`, `monic_biResultant`,
`natDegree_biResultant`; `evalModularPair` + `_eq_eval_fibrePoly`,
`Polynomial.resultant_eq_zero_of_isRoot_isRoot`,
`eval_map_evalRingHom_resLiftOuterK`, `evalModularPair_biResultant_eq_zero_of_common`,
and `ModularPolynomialData.eval₂_qExpand_eq_zero`.

**Seam.** mathlib's `Polynomial.resultant`/`resultant_eq_zero_iff` and
`IsAlgClosed`/`AlgebraicClosure`; the pin imports
`Mathlib.RingTheory.Polynomial.Resultant.Basic`, `FieldTheory.IsAlgClosed.*`,
`NumberTheory.ArithmeticFunction.Misc`. **Scout the coefficient comparison
(`coeff_biResultant_*` and `eval₂_coeff_biResultant_eq_coeff_compositeFibrePoly`)
first**: it is the block most likely to need a mathlib-API restatement.

**`finrank_adjoin_jqNModC_le`** (65 content; wrapper `(K) [Field K] {N} [NeZero N]
(data : ModularPolynomialData N) : Module.finrank (adjoin K {jqModC K})
(adjoin (adjoin K {jqModC K}) {jqNModC K N}) ≤ dedekindPsi N`). The pin's private
`phiAt`/`coeffMap_eq_map`/`coeffMap_phiAt`/`phiAt_rat`/`phiAt_eq_zero`/`phiOver`/
`aeval_phiOver`; `finiteDimensional_adjoin_jqNModC` is the immediate corollary.

**`transcendental_jqModC`** (61 content; wrapper `(K) [CommRing K] :
Transcendental K (jqModC K)`): the pin's `jqModC_pow`, coefficient triangularity,
`aeval_jqModC_eq_zero` — the `jqModC` analogue of the ported `Defs/Jq.lean`
`transcendental_jq` proof. **Check for a reusable ported `coeff_aeval_jq_neg`
analogue** (the port promoted it; the pin re-derives it for `jqModC`).

## 3. Verification

- Append the 14 wrappers to `SOURCES`, the two modules to `PORT_FILES`.
- checker 0 mismatched / 0 missing.
- `#print axioms` on the two real proofs + the seven one-liners.
- Consumer Zone D `[degree]`: `nonempty_modularPolynomialData_of_squarefree` at
  `N = 1`/`N = 2`, `finrank_adjoin_jqNModC_le` at `N = 2`, and
  `transcendental_jqModC ℚ` composed with `jqModC_rat`.

## 4. Budget

**3 goal rounds.** Round 1: the one-liners + `transcendental_jqModC` +
`finiteDimensional`/`finrank_le`. Round 2: the `nonempty_..._of_squarefree`
biresultant scout and proof. Round 3: finish, log/README/consumer.

**Stop early on**: a one-liner that will not close (report it); the biresultant
coefficient comparison needing a mathlib API the pin's proof does not have; or
`transcendental_jqModC` needing a `jqModC`-specific triangularity block that the
ported `Defs/Jq.lean` cannot instantiate.

## 5. Reporting back

1. Module/line/decl table and checker before/after.
2. **The one-liner table, measured**: for each of the seven, the port declaration
   it reduced to and the proof length; flag any that did not stay a one-liner.
3. `nonempty_modularPolynomialData_of_squarefree`: its block structure, the
   mathlib resultant API used, and where it bit.
4. Whether `jqModC`'s triangularity deduped to the ported `jq` one.
5. The SET-M3 hand-off.
