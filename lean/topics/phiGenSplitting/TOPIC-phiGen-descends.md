# Topic 8: the cone application — the descended coefficients lie in `ℚ[jq]`

**Status: done (2026-09-22), one goal round — the plan sequence is complete and
the cone's (c) is discharged.** The modules are
`FLTForHuman/ModularForms/Defs/HeckeOperator.lean`,
`FLTForHuman/ModularForms/HeckeQExpansion.lean` and
`FLTForHuman/ModularForms/PhiGenDescends.lean`, green with 0 warnings and no
`sorry`; the measured cost, the audit accounting and the three shape issues are
in [logs/phiGen-port.md](../../logs/phiGen-port.md) §8. What remains of the cone
is its other five pieces, and [PORTING-PhiGen.md](../../PORTING-PhiGen.md) §6 is
the re-route menu. This file is kept as the executed plan. Fourth and last topic
of the Φ_p splitting / R1 sub-effort's planned sequence. The plan is
[PORTING-PhiGen.md](../../PORTING-PhiGen.md); the mathematics is
[base/013](../../../base/013-riemann-existence-and-the-q-expansion-principle.md)
§4.3 and §6. T5–T7 are executed and **R1 is complete**; their records are
[TOPIC-r1-kernel.md](TOPIC-r1-kernel.md), [TOPIC-jq-model.md](TOPIC-jq-model.md),
[TOPIC-hauptmodul.md](TOPIC-hauptmodul.md) and
[logs/phiGen-port.md](../../logs/phiGen-port.md).

> **Build discipline — read this first.** Every build is bounded and a blow-up is
> quarantined, not waited on. Measured with mathlib prebuilt: a green
> `lake env lean <module>` of this size is **~4 s**, `lake build <module>` with
> deps cached **~2–5 s**, and a `whnf`/heartbeat timeout at the default cap
> **errors in ~15–20 s** — it does not hang.
>
> - Run every build under a bound: `timeout 60 lake env lean <file>`,
>   `timeout 120 lake build <module>`. Non-return at 60 s is a blow-up.
> - **Quarantine immediately.** On a timeout, comment the declaration out and
>   bisect, or reproduce in the gitignored `Scratch.lean` with
>   `set_option diagnostics true`. Do not re-run the same file hoping for a
>   different result.
> - **Never raise `maxHeartbeats`.** The cap already fails in under 20 s; raising
>   it turns that into an unbounded wait. The usual cause is a `FunLike`-quantified
>   lemma instantiated at a bare function type (`DFunLike.coe` unfolds without
>   bound) — restate it over the concrete function instead. T5's log §2.2 has the
>   worked example.

**Audience.** A fresh session taking this topic. Read, in this order:

1. [PORTING-PhiGen.md](../../PORTING-PhiGen.md) §3–§6 — the cone's six pieces,
   the R1/R2 split, and the re-route question this topic feeds;
2. [base/013](../../../base/013-riemann-existence-and-the-q-expansion-principle.md)
   §4.3 (the Hecke-coset construction that makes the coefficients level-one
   invariant) and §5.6 (the application);
3. [TOPIC-hauptmodul.md](TOPIC-hauptmodul.md) — the exported `RealL` API and
   `hasSum_qParam_mul_laurent` this topic imports;
4. [logs/phiGen-port.md](../../logs/phiGen-port.md) §7 — the "match the wrapper's
   spelling for checker-verified public declarations" rule;
5. [porting-playbook.md](../../porting-playbook.md) §3, especially §2
   (deduplicate at the source) and §3.11.

**Goal.** The cone's item **(c)**: the descended coefficients of the conjugate
product lie in `ℚ[jq]`. The public deliverable, verbatim from its wrapper:

```lean
theorem ModularCurve.PhiGen.mem_adjoin_jq_of_phiGenDescends
    (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : (CyclotomicField ℓ ℚ)ˣ)
    (hζ : IsPrimitiveRoot (ζ : CyclotomicField ℓ ℚ) ℓ)
    (c : ℕ → LaurentSeries ℚ) (hc : PhiGenDescends ℓ ζ c) (k : ℕ) :
    c k ∈ Algebra.adjoin ℚ {jq}
```

Three more public declarations (pin nodes with wrappers; consumers inside this
topic and in the cone's later pieces):

```lean
theorem ModularCurve.hasSum_qParam_heckeMatrix_smul (ℓ : ℕ) [NeZero ℓ] (b : ℕ)
    (A : LaurentSeries ℂ) (F : UpperHalfPlane → ℂ)
    (hA : ∀ τ, HasSum (fun m : ℤ => A.coeff m * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (F τ))
    (τ : UpperHalfPlane) :
    HasSum (fun m : ℤ => (Complex.exp (2 * Real.pi * Complex.I * b * m / ℓ) * A.coeff m) *
      Function.Periodic.qParam ℓ (τ : ℂ) ^ m) (F (ModularForm.heckeMatrix ℓ b • τ))

theorem ModularCurve.hasSum_qParam_heckeDiagMatrix_smul (ℓ : ℕ) [NeZero ℓ]
    (A : LaurentSeries ℂ) (F : UpperHalfPlane → ℂ)
    (hA : ∀ τ, HasSum (fun m : ℤ => A.coeff m * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (F τ))
    (τ : UpperHalfPlane) :
    HasSum (fun m : ℤ => (ModularCurve.qExpand ℂ (ℓ * ℓ) A).coeff m *
      Function.Periodic.qParam ℓ (τ : ℂ) ^ m) (F (ModularForm.heckeDiagMatrix ℓ • τ))

theorem ModularCurve.cosetPoly_smul (ℓ : ℕ) (hℓ : ℓ.Prime) (F : UpperHalfPlane → ℂ)
    (hF : ∀ γ τ, F (γ • τ) = F τ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (τ : UpperHalfPlane) :
    (Polynomial.X - Polynomial.C (F (ModularForm.heckeDiagMatrix ℓ • γ • τ))) *
        ∏ b : Fin ℓ, (Polynomial.X - Polynomial.C (F (ModularForm.heckeMatrix ℓ (b : ℕ) • γ • τ)))
      = (Polynomial.X - Polynomial.C (F (ModularForm.heckeDiagMatrix ℓ • τ))) *
        ∏ b : Fin ℓ, (Polynomial.X - Polynomial.C (F (ModularForm.heckeMatrix ℓ (b : ℕ) • τ)))
```

Plus a new **definition** module for the Hecke matrices, and the pin's
`hasSum_coeff_of_phiGenDescends` (the intermediate that turns `hc` into the
realization T7 consumes) kept private.

## 1. Why this topic, and what is settled

R1 was isolated so that this application could exist. base/013 §4.3 is the pivot:
the descended coefficients are made `SL₂(ℤ)`-invariant (not merely
`Γ₀(ℓ)`-invariant) by the **Hecke-coset construction**, which is why R1 at level
one suffices and the level-`N` q-expansion principle is never needed. T8 ports
that construction: the two Hecke-translate q-expansions, the coset product's
invariance, the realization of its coefficients, and T7's headline applied to
them.

- **Settled: mathlib has no Hecke operators.** This is the audit's headline
  (§2.1): `heckeMatrix`, `heckeDiagMatrix`, `heckeU`, `heckeT`, `HeckeSlash` do
  not exist anywhere in `Mathlib/`. FLT defines them in
  `Definitions/Def_ModularForm_HeckeOperator.lean` (204 lines, 38 declarations).
  So this topic **adds a definition module**, the first since Layer 0b.
- **Settled: port only the Hecke subset T8 uses, and record the drops.**
  Grepping the five T8 pin files for the def module's identifiers gives:
  `heckeMatrix` (3 files), `heckeDiagMatrix` (3), `coe_heckeMatrix_smul` (1),
  `coe_heckeDiagMatrix_smul` (1) — and **nothing else**. The port needs
  `upperTriangularGL`, `heckeMatrix`, `heckeDiagMatrix`, their `val_*`,
  `det_*`, `det_*_pos`, `denom_*` and `coe_*_smul` (≈60 of the 204 lines); the
  `heckeU`/`heckeT`/`coeffHecke*`/`σ_*`/`slash_*` block (~130 lines) is **not
  ported**, with the `grep -c` counts recorded (PORTING-FFG §1.5). If a later
  cone piece needs `heckeU`/`heckeT`, it extends the module then.
- **Settled: deduplicate the `RealL` block.** The pin's
  `S_ModularCurve_PhiGen_PhiGenDescends_hasSum_cosetPoly_coeff.lean` **copies**
  the whole `RealL` + closure block (~90 lines) and the `jt`/`jqC` glue (~17)
  from T7's file. The port imports T7's
  (`FLTForHuman.ModularForms.Hauptmodul`) instead — this is the payoff of T7
  exporting the API, and the header should say so.
- **Settled: statements are the pin's, verbatim**, and the four wrappers go in
  `SOURCES`. Per T7 log §7.3, a checker-verified public declaration must use the
  **wrapper's spelling** (`UpperHalfPlane → ℂ`, `Function.Periodic.qParam`), not
  `ℍ`/`𝕢`.
- **Settled: this completes the planned sub-effort sequence.** After T8 the
  cone's (c) is discharged. The cone's remaining pieces — (a) `exists_phiGenDescends`,
  (b) integrality/pole bounds, (d) assembly + uniqueness, (e)
  irreducibility/symmetry, (f) the splitting statement — are a separate, larger
  effort; [PORTING-PhiGen.md](../../PORTING-PhiGen.md) §6 records the re-route
  options now that the analytic input is in hand.

## 2. The scouted inventory

Five pin files, ~681 lines, plus the def module subset.

| pin file | lines | content |
|---|---|---|
| `Definitions/Def_ModularForm_HeckeOperator.lean` | 204 | `upperTriangularGL`, `heckeMatrix`, `heckeDiagMatrix`, their API |
| `S_ModularCurve_hasSum_qParam_heckeMatrix_smul.lean` | 54 | `τ ↦ (τ+b)/ℓ` on a realized `q`-expansion |
| `S_ModularCurve_hasSum_qParam_heckeDiagMatrix_smul.lean` | 55 | `τ ↦ ℓτ`, i.e. `q ↦ q^{ℓ²}` |
| `S_ModularCurve_cosetPoly_smul.lean` | 244 | the coset polynomial is `SL₂(ℤ)`-invariant |
| `S_ModularCurve_PhiGen_PhiGenDescends_hasSum_cosetPoly_coeff.lean` | 281 | realize the descended coefficient, then T7's headline |
| `S_ModularCurve_PhiGen_mem_adjoin_jq_of_phiGenDescends.lean` | 47 | the exported application |

Declaration inventory:

| block | pin lines | size |
|---|---|---|
| Hecke defs subset (see §2.1) | `Def…HeckeOperator` 11–71 | ≈60 of 204 |
| `hasSum_qParam_heckeMatrix_smul'` | heckeMatrix 20–52 | 33 |
| `hasSum_qParam_heckeDiagMatrix_smul'` | heckeDiag 22–53 | 32 |
| `det_eq`, `heckeMatrix_mul_of_eq'`, `heckeDiagMatrix_mul_of_eq'` | coset 24–97 | 74 |
| `heckeRep`, `redMatrix`, `heckeRep_mul` | coset 98–184 | 87 |
| `apply_heckeRep_smul_smul`, `prod_range_eq_prod_zmod`, `prod_fin_eq_prod_zmod`, `cosetPoly_eq_prod_onePoint` | coset 185–221 | 37 |
| `cosetPoly_smul'` | coset 222–242 | 21 |
| **`RealL` + closure (pin copy; import T7's)** | coset-coeff 30–119 | ~90 (dropped) |
| `expRoot`, `isPrimitiveRoot_expRoot`, `sigma`, `sigma_zeta`, `sigma_ratCast'` | coset-coeff 120–153 | 30 |
| `jt`/`castC`/`jqC`/`jqC_coeff`/`realL_jqC` (pin copy; reuse) | coset-coeff 154–170 | ~17 (dropped) |
| `conjC`, `rep`, `realL_conjC_zero`, `expRoot_pow_zpow`, `realL_conjC_succ`, `realL_conjC` | coset-coeff 171–214 | 44 |
| `map_phiProd`, `realL_phiProd_coeff`, `realL_one_of_realL_qExpand`, `coeffMap_sigma_coeffEmb` | coset-coeff 215–254 | 40 |
| `hasSum_coeff_of_phiGenDescends` (private) | coset-coeff 255–276 | 22 |
| `jt`/`jt_smul` (duplicates T6/T7) + the exported application | mem_adjoin 31–48 | ~10 (dropped) |

### 2.1 The mathlib-first audit

Audited against `v4.34.0`. **This topic's audit has a positive finding and a
negative one.**

| pin piece | mathlib `v4.34.0` | verdict |
|---|---|---|
| `upperTriangularGL`, `heckeMatrix`, `heckeDiagMatrix`, `heckeU`, `heckeT`, `coeffHeckeT`, `coeffHeckeU`, `slash_hecke*`, `σ_hecke*` | **absent** — `grep -rln heckeMatrix Mathlib/` is empty; there are no Hecke operators in mathlib | **new `Defs/` module**, minimal subset |
| `val_hecke*`, `det_hecke*`, `denom_hecke*`, `coe_hecke*_smul` | `UpperHalfPlane.coe_smul_of_det_pos`, `Matrix.det_fin_two_of`, `Matrix.GeneralLinearGroup.mkOfDetNeZero` | port, using mathlib's matrix/`UpperHalfPlane` API |
| `hasSum_qParam_heckeMatrix_smul'`, `…_heckeDiagMatrix_smul'` | `Periodic.qParam`, `Complex.exp` arithmetic, `UpperHalfPlane.coe_smul_of_det_pos`; no product/Hecke q-expansion lemma | port (small; the two lemmas are ~33/32 lines) |
| `cosetPoly_eq_prod_onePoint`, `heckeRep`, `redMatrix`, `prod_*_zmod` | `OnePoint (ZMod p)` / `ProjectiveLine` (Topology/Compactification/OnePoint/ProjectiveLine), `ZMod`, `Fintype.prod_option`, `Equiv.prod_comp` | port; mathlib gives the `OnePoint`/`ZMod` objects and the `prod_comp` reindex |
| `apply_heckeRep_smul_smul`, `cosetPoly_smul'` | none (the Hecke coset rep is FLT's) | port |
| `RealL` block, `jt`/`jqC` glue | **present in the port** (T7's `Hauptmodul`, T6's `JqAnalyticModel`) | **import, do not copy** |
| `sigma`, `sigma_zeta`, `expRoot` | `Complex.isPrimitiveRoot_exp`, `IsPrimitiveRoot.embeddingsEquivPrimitiveRoots`, `Polynomial.cyclotomic.irreducible_rat` | port the wrapper (small) |
| `realL_conjC_*`, `map_phiProd`, `realL_phiProd_coeff`, `realL_one_of_realL_qExpand` | none; uses T7's `RealL` closure, T6's `hasSum_qParam_hecke*` and `coeffMap_qExpand` | port |
| the exported application | none; T7's headline + the above | port (small) |

**Headline.** Mathlib supplies the *objects* (`OnePoint (ZMod p)`, `ZMod`, the
`GL(2,ℝ)` action on `ℍ`, `coe_smul_of_det_pos`) but none of FLT's Hecke
operators or their `q`-expansion behaviour. So this topic adds the sub-effort's
**first new definition module** and its port is dominated by FLT's own group
theory. The `FunLike` trap is not expected, but the discipline stands.

**Post-execution note (2026-09-22).** The headline held: mathlib has no Hecke
operators, and the port adds the Hecke layer plus the coset/descend group theory.
The port is **725 lines** across three modules (115 defs + 100 Hecke q-expansions
+ 510 descend), 8 public and 43 private declarations, against ~741 lines of pin
content (681 + the 60-line Hecke subset); ratio **0.98** — the sub-effort's
cheapest, and the deduplication saved ~97 lines (T7's `RealL`/closure imported
rather than copied). The predicted `FunLike` trap did not occur, but a different
matching issue did: the pin's `@[scoped simp] mapGL_apply` does not rewrite the
entries of the anonymous `SL(2,ℤ)` matrix `⟨!![…], _⟩` under v4.34's transparency
settings, and the fix is mathlib's own
`set_option backward.isDefEq.respectTransparency.types false`. Two smaller shape
issues (explicit `(p := p)` for `redMatrix`; the `haveI` linter in `sigma_zeta`)
are in the log. The dropped `heckeU`/`heckeT` block is genuinely unused
(§4 item 4). Full accounting in [logs/phiGen-port.md](../../logs/phiGen-port.md)
§8.

## 3. What is different about this topic

- **It is the largest topic and the only one adding definitions.** T6 was 622
  lines and T7 483, both one round; T8's pin is ~681 plus ~60 lines of Hecke
  definitions, minus ~107 lines of pin duplication the port imports instead —
  ≈630 lines of new content, over four modules. Budget accordingly.
- **It is the payoff of the deduplication rule.** The pin copies the `RealL`
  block and the `jt`/`jqC` glue into the descend file; the port imports them. The
  header should record that this is the reason T7 exported the API.
- **Its group theory is over `OnePoint (ZMod ℓ)`.** `heckeRep` sends
  `x ∈ ℙ¹(𝔽_ℓ)` to the corresponding coset matrix, and invariance follows
  because `SL₂(ℤ)` acts through `redMatrix` and `Equiv.prod_comp` permutes the
  factors. This is a different flavour from T5–T7's analysis; expect `ZMod`/
  `OnePoint` friction, not heartbeat friction.
- **It completes the planned sequence but not the cone.** After T8, (c) is done;
  the cone's other five pieces are the next effort (§6 of the plan).

## 4. Verification and the wire test

Beyond `lake build` green / 0 warnings / no `sorry`:

1. **`#print axioms`** on the four public declarations: only `propext,
   Classical.choice, Quot.sound`.
2. **Statement checker.** Add the four wrappers to `SOURCES` (`hasSum_qParam_heckeMatrix_smul`,
   `hasSum_qParam_heckeDiagMatrix_smul`, `cosetPoly_smul`,
   `mem_adjoin_jq_of_phiGenDescends`); verified count rises from **168**, 0
   mismatched; `PORT_FILES` gains the modules. Use the wrappers' spelling
   (T7 log §7.3).
3. **The wire test, cross-module.** The internal chain is genuine:
   `hasSum_coeff_of_phiGenDescends` produces the realization, T7's
   `mem_adjoin_jq_of_hasSum_of_slash_invariant` consumes it, and the two Hecke
   q-expansion lemmas feed `hasSum_coeff_of_phiGenDescends`. Show it composes —
   a consumer Zone binding for `mem_adjoin_jq_of_phiGenDescends` (`#check` plus
   the correspondence) — and say in the report that the node's *real* consumer is
   the cone's (d) `exists_modularPolynomialData_coeff_eq`, which is not ported.
   There is no concrete `hc : PhiGenDescends ℓ ζ c` available (that is the cone's
   (a)), so do not invent one.
4. **The dropped Hecke block.** Record the `grep -c` counts for `heckeU`,
   `heckeT`, `coeffHeckeT`, `coeffHeckeU`, `slash_hecke*`, `σ_hecke*` showing T8
   does not use them, per PORTING-FFG §1.5.

## 5. Budget

**4 goal rounds, checkpoint at 1; split if it grows.** Pin ≈681 + 60 Hecke − 107
duplication ≈ **630 lines of new content**, the sub-effort's largest; T6 (622)
and T7 (483) each took one round, but T8 has more shape variety (new `Defs/`
module, `ZMod`/`OnePoint` group theory, a cyclotomic embedding). Round 1 scouting
should build the Hecke defs and one Hecke q-expansion to confirm the `qParam`
arithmetic; the coset polynomial and the descend application follow.

**Documented split point.** If by the round-2 checkpoint the coset group theory
is still not closed, split at the natural seam and write the second work order:
**T8a** = Hecke defs + the two Hecke q-expansions + `cosetPoly_smul`; **T8b** =
`hasSum_coeff_of_phiGenDescends` + `mem_adjoin_jq_of_phiGenDescends` (which only
needs T8a's exports and T6/T7). Record the decision in the log either way.

Stop early on: the Hecke `coe_*_smul` needing a `UpperHalfPlane` lemma that is
private; `heckeRep_mul` not matching `SL₂(ℤ)`'s action on `OnePoint (ZMod ℓ)`; or
the descend application forcing a change to T7's exported `RealL` API (which T8
cannot make).

## 6. Definition of done

- [x] `FLTForHuman/ModularCurve/Defs/HeckeOperator.lean` (or `ModularForms/Defs/`):
      the minimal Hecke subset, mathlib-only, with the dropped block's grep counts
      in the header.
- [x] the Hecke q-expansion modules and the descend module; the four public
      statements verbatim from their wrappers; T7's `RealL`/`hasSum_qParam_mul_laurent`
      imported, not copied; `hasSum_coeff_of_phiGenDescends` private.
- [x] `lake build` green, 0 warnings, no `sorry`.
- [x] `#print axioms` clean.
- [x] `spec/check_flt_statements.py`: the four wrappers in `SOURCES` (168 → 176),
      0 mismatched; `PORT_FILES` gains the module(s).
- [x] the wire item and the dropped-block counts from §4 recorded.
- [x] `PORTING-PhiGen.md` §5 marks T8 done (the planned sequence complete, the
      cone's (c) discharged) and states what remains of the cone; the log gains
      T8's cost and the audit accounting; README module table gains the module(s).
- [x] report in the §7 shape.

## 7. Reporting back

1. **The cost and the dedup payoff** — rounds, declarations, lines, port/pin
   ratio (T5 1.79, T6 1.06, T7 1.05); how many lines the imported `RealL`/glue
   saved.
2. **The Hecke definitions** — did the minimal subset really suffice, and is the
   dropped `heckeU`/`heckeT` block genuinely unused by the cone's remaining
   pieces? (A cheap `grep` over the cone's other pin files answers the second.)
3. **Did the `ZMod`/`OnePoint` group theory behave, and did any mathlib lemma
   blow up?** Name either finding.

## 8. Where this sits: the cone's six pieces

| piece | deliverable | status |
|---|---|---|
| (f) | `PhiGen.splits_of_prime` / `splits_prime_at_slot` | not started |
| (a) | `exists_phiGenDescends` (descent to `ℚ((q))`) | not started |
| (b) | `intCoeffs`, pole bounds, `exists_modularPolynomialData_coeff_eq` inputs | not started |
| **(c)** | **`mem_adjoin_jq_of_phiGenDescends`** | **this topic** |
| (d) | `exists_modularPolynomialData_coeff_eq`, `eq_of_prime` (assembly + uniqueness) | not started |
| (e) | `phiIrreducible_of_splits`, `evalSymm_of_splits` (the 895-line block) | not started |

R1 (T5–T7) supplied the analytic input (c) needs; **T8 discharges (c)**. The
remaining five pieces are the cone's algebra, and [PORTING-PhiGen.md](../../PORTING-PhiGen.md)
§6 is the menu for how to route them now that (c) is available.
