# TOPIC — the `q`-expansion function field head: Γ₀-rationality, relative degree, and the residue-field model

**Status: PLANNED (2026-10-08), ready to dispatch.** Planning record for the five
largest `ModularCurve` entries of the ready shelf, taken as one cluster. Pin
`aa2d8b3`, port mathlib `v4.34.0`, port checker at `6520 identical (312 promoted,
83 renamed), 0 mismatched, 0 missing, 36 own-proof (6556 checked)`. Method:
[porting-playbook.md](../../porting-playbook.md) §2.1–§2.6, §3.1–§3.5, §4–§5.
Group advise (the raw tables this file is built from):
`tools/deps/build/next5_advise.txt`, `next5_plan.txt`, `next5_nodes.txt`,
`next5.json`.

## 0. Where this set comes from

```bash
cd tools/deps
python3 frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen \
  --rank-by silo --ready --top 0
python3 port_advise.py --nodes "$(paste -sd, build/next5_nodes.txt)" --json build/next5.json
python3 port_plan.py --json build/next5.json
```

The command leaves **89 ready nodes**. By silo: `ModularCurve` **38 / 14,819 raw
silo lines**, `WeierstrassCurve` 8 / 3,868, `CuspForm` 10 / 2,843,
`AlgebraicCurve` 23 / 2,504, `AutomorphicForm` 2 / 681, `PeriodPair` 2 / 601,
`CohCarrier` 2 / 552, `ModularForm` 2 / 102, `CuspFormClass` 2 / 98. The list is
ranked by silo lines and its **five largest entries are all `ModularCurve.*`**
(5,900 of the silo's 14,819 lines, 40%): this cluster.

This is the head that the landed Deligne–Serre differential tail handed over; see
[../deligneSerre/ds-head-recon.md](../deligneSerre/ds-head-recon.md) §1.

## 1. Targets and verdict

**Targets.** Five pinned statements, transcribed verbatim from their `Theorems/`
wrappers (wrapped for readability; the checker's own text is the authority):

```lean
theorem ModularCurve.exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0_of_dvd
    (M ℓ : ℕ) [NeZero M] [NeZero ℓ] (m : ℕ) (G : UpperHalfPlane → ℂ)
    (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (hinv : ∀ g ∈ CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 (M * ℓ),
      ∀ τ : UpperHalfPlane, G (g • τ) = G τ)
    (hbd : ∀ α : SL(2, ℤ), UpperHalfPlane.IsBoundedAtImInfty
      ((fun τ : UpperHalfPlane => G (α • τ)) * ModularForm.discriminant ^ m))
    (hrat : ∀ n : ℕ, ∃ r : ℚ,
      (UpperHalfPlane.qExpansion 1 (G * ModularForm.discriminant ^ m)).coeff n = (r : ℂ))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (hγℓ : (ℓ : ℤ) ∣ γ 1 1) (n : ℕ) :
    ∃ r : ℚ, (UpperHalfPlane.qExpansion ℓ
      ((fun τ : UpperHalfPlane => G (γ • τ)) * ModularForm.discriminant ^ m)).coeff n = (r : ℂ)

theorem ModularCurve.le_relrank_xHFunctionField_xHTopFunctionFieldC_of_not_dvd
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M) :
    ((ℓ + 1 : ℕ) : Cardinal) ≤ IntermediateField.relrank (xHFunctionField M H)
      (xHTopFunctionFieldC ℚ M H (M * ℓ))

theorem ModularCurve.exists_qExpansion_S_smul_eq_and_conj_eq_of_ratCast_qExpansion
    (N : ℕ) [NeZero N] (m : ℕ) (G : UpperHalfPlane → ℂ) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (hinv : ∀ g ∈ CongruenceSubgroup.Gamma1 N, ∀ τ : UpperHalfPlane, G (g • τ) = G τ)
    (hbd : ∀ α : SL(2, ℤ), UpperHalfPlane.IsBoundedAtImInfty
      ((fun τ : UpperHalfPlane => G (α • τ)) * ModularForm.discriminant ^ m))
    (hrat : ∀ n : ℕ, ∃ r : ℚ,
      (UpperHalfPlane.qExpansion 1 (G * ModularForm.discriminant ^ m)).coeff n = (r : ℂ))
    (ι : AlgebraicClosure ℚ →+* ℂ) :
    ∃ a : ℕ → AlgebraicClosure ℚ,
      (∀ n : ℕ, (UpperHalfPlane.qExpansion N
          ((fun τ : UpperHalfPlane => G (ModularGroup.S • τ))
            * ModularForm.discriminant ^ m)).coeff n = ι (a n)) ∧
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ),
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ N = 1 → σ ζ = ζ ^ c) → ∀ γ : SL(2, ℤ),
          ((γ 0 1 : ℤ) : ZMod N) = 0 → ((γ 1 1 : ℤ) : ZMod N) = c → ∀ n : ℕ,
            (UpperHalfPlane.qExpansion N
              ((fun τ : UpperHalfPlane => G (ModularGroup.S • γ • τ))
                * ModularForm.discriminant ^ m)).coeff n = ι (σ (a n))

theorem ModularCurve.finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index
    (L : Type*) [Field L] [Algebra ℚ L] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hΓ' : Γ ≤ Γ')
    (hneg : ∀ γ ∈ Γ', γ ∈ Γ ∨ -γ ∈ Γ)
    (y : laurentBaseChange L (qExpFunctionFieldC ℚ Γ)) (hy : (y : LaurentSeries L) = jqModC L) :
    Module.finrank (IntermediateField.adjoin L
        ({y} : Set (laurentBaseChange L (qExpFunctionFieldC ℚ Γ))))
      (laurentBaseChange L (qExpFunctionFieldC ℚ Γ)) ≤ Γ'.index

theorem ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField
    (L : Type*) [Field L] [Algebra ℚ L] (A : ValuationSubring L)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) :
    ∃ x : qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ,
      (x : LaurentSeries (IsLocalRing.ResidueField A)) = jqModC (IsLocalRing.ResidueField A) ∧
      Transcendental (IsLocalRing.ResidueField A) x ∧
      FiniteDimensional (IntermediateField.adjoin (IsLocalRing.ResidueField A)
          ({x} : Set (qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ)))
        (qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ) ∧
      ∀ (y : laurentBaseChange L (qExpFunctionFieldC ℚ Γ)),
        (y : LaurentSeries L) = jqModC L →
        Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
            ({x} : Set (qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ)))
          (qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ) ≤
        Module.finrank (IntermediateField.adjoin L
            ({y} : Set (laurentBaseChange L (qExpFunctionFieldC ℚ Γ))))
          (laurentBaseChange L (qExpFunctionFieldC ℚ Γ))
```

**Verdict. Port, in three sets — but the cluster is far cheaper than its raw size.**
All five are ready, and 249 of their 578 public declarations (43%) already have
byte-identical statements in the port: the pin's newer `S_` files are **consumers**
of three layers the port already carries —

1. the weight-one rectification (`ModularForms/WeightOne/`), imported as the whole
   `Thm_WLight_*` wrapper cluster by the two q-expansion targets;
2. `JOneES` (`ModularCurve/X1/FunctionField.lean`), imported as a `Thm_` headline by
   the two JOneES targets;
3. the `X_H` layer (`ModularCurve/XH/`, SET-H-A/B/C), imported as
   `Def_ModularCurve_XH` + `ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul` by
   the relrank target.

The genuinely new mathematics is the relrank bound (target 2) and the residue-field
model (target 5); the Γ₀-rationality pair (targets 1, 3) is a new engine over a
mostly ported base; the finrank/index bound (target 4) is the `JOneES` engine again
with a headline.

## 2. The measured cone

`port_plan.py` on the ten target files (five `S_` + five `Thm_`), 583 declarations:

| row | lines |
|---|---:|
| raw `S_` lines | 5,900 |
| declaration lines | 5,782 |
| − duplicate copies (port once) | −374 |
| − boilerplate | −118 |
| once-cost after dedup | 5,408 |
| − already in the port (vetted) | −1,710 |
| **net new math lines** | **3,698** |

Substitutions: **264 rows / ≈2,104 raw lines already statement-identical**, of which
185 are importable public and **79 are port-`private`**. Per target (public
declarations; "ported" = byte-identical statement in the port; my re-count by name):

| target (`S_ModularCurve_…`) | raw | public | ported | new | new decl lines | main reuse homes |
|---|---:|---:|---:|---:|---:|---|
| 1 `exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0_of_dvd` | 1,388 | 131 | **101 (77%)** | 30 | 528 | `GammaRational` 69, `RatAt` 12, `Gamma0Rationality` 6 |
| 2 `le_relrank_xHFunctionField_xHTopFunctionFieldC_of_not_dvd` | 1,221 | 165 | 22 (13%) | **143** | 1,204 | `XH/HeckeInputs` 8, `X1/FunctionField` 6 |
| 3 `exists_qExpansion_S_smul_eq_and_conj_eq_of_ratCast_qExpansion` | 1,196 | 126 | **77 (61%)** | 49 | 791 | `GammaRational` 33, `Gamma1Basis` 15, `RatAt` 10 |
| 4 `finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index` | 1,095 | 86 | **49 (57%)** | 37 | 546 | `X1/FunctionField` 46 (**all private**), `JqIntegralRatios` 3 |
| 5 `exists_…_qExpFunctionFieldC_residueField` | 1,000 | 70 | **0** | **70** | 1,045 | — |
| **total** | **5,900** | **578** | **249 (43%)** | **329** | **4,114** | |

(The 4,114 is the raw sum of the new declarations' own spans; `port_plan`'s 3,698 is
the same content after the once-only dedup and the boilerplate correction. Reconcile
against whichever ledger the order uses.)

## 3. Route audit: what the port already has

**Importable reuse (185 rows).** The public homes, by volume:

| port home | rows | supplies |
|---|---:|---|
| `ModularForms/WeightOne/Defs/GammaRational.lean` | 102 | the `X1DiamondRational` engine (`descent`, `exists_of_mul_eq`, `exists_rat_combination`, …) |
| `ModularForms/WeightOne/Defs/RatAt.lean` | 33 | the `RatAt` predicate and its closure |
| `ModularForms/WeightOne/Defs/Gamma.lean` | 10 | `Γ`/`Γ₁`/`Γ₀` vocabulary |
| `ModularForms/DiscPow.lean` | 9 | `Δ ^ m` analyticity |
| `ModularCurve/XH/HeckeInputs.lean` | 8 | `conjMat`/`conjSL`/`heckeDiag_mul_mul_inv`/`inf_le_conj` (SET-H-C) |
| `Elliptic/PeriodPair/Basic.lean` | 5 | period-pair supply |
| `ModularForms/QExpansionCoeff.lean`, `ModularCurve/X1/FunctionField.lean` | 4 each | q-coefficient transport; `JOneES` |
| `ModularForms/WeightOne/LevelN.lean` | 3 | level-`N` vocabulary |
| `ModularForms/WeightOne/Gamma0Rationality.lean` | 2 | `Γ₀` rationality |
| `MonicRel.lean`, `X1/Defs.lean`, `Defs/Fields.lean`, `X1/QExpandStretch.lean`, `Gamma1Basis.lean` | 1 each | — |

**Port-`private` reuse (79 rows / 741 raw lines)** — the promotion decision. The
last column is the target the row serves (`X1/FunctionField` serves both JOneES
targets):

| port home | rows | lines | needed by |
|---|---:|---:|---|
| `ModularCurve/X1/FunctionField.lean` | 51 | 572 | targets 2 and 4 (the `JOneES` private engine) |
| `ModularForms/WeightOne/Gamma1Basis.lean` | 14 | 76 | target 3 |
| `ModularForms/WeightOne/Gamma0Rationality.lean` | 5 | 58 | target 1 |
| `ModularCurve/JqIntegralRatios.lean` | 5 | 23 | targets 2 and 4 |
| `ModularForms/WeightOne/Gamma0Integral.lean` | 2 | 6 | target 2 |
| `ModularForms/WeightOne/Defs/GammaRational.lean` | 1 | 4 | target 1 |
| `DeligneSerre/Lifting.lean` | 1 | 2 | target 2 |

**Recorded negatives** (do not repeat the searches):

* Mathlib supplies `IntermediateField.relrank` (the `Cardinal`-valued relative
  degree), `Module.finrank`, `IsLocalRing.ResidueField`, `ValuationSubring`,
  `PowerSeries.map`/`HahnSeries.map`. There is no mathlib statement of any of the
  five conclusions, and no `jqModC`/`qExpFunctionFieldC` vocabulary — those are the
  pin's and are ported.
* `Def_ModularCurve_X0ModL.lean` (imported by target 5) is **not** a missing module,
  despite the `SOURCES` note at `spec/check_flt_statements.py:1830` that its generic
  `modularFunctionFieldFullC` half is deliberately unported: target 5 uses only two
  of that file's 20 declarations, `coeffMap_ofPowerSeries` (ported,
  `Frobenius/Defs.lean:57`) and `coeffMap_jqModC` (**not** a named lemma in the port;
  the same statement is proved inline at `Degree/PhiDegree.lean:103`). Budget ~3
  lines for it, not a module.
* `--ready` and `--with-defs` do **not** see import-only definitions. `--with-defs`
  adds only `Def_ModularCurve_JqCoeff`, `Def_ModularCurve_X1` and
  `Def_ModularCurve_XH` (all already in `SOURCES`); each order must hand-check the
  five import lists as above.
* `ModularCurve.HeckeInputsAlong` (`Defs/HeckeTotal.lean`) is a different predicate
  from anything here; the relrank target's `HeckeInputsHAll` neighbours are the
  SET-H-C ones.

## 4. Dedup before coding

1. **The Γ₀-rationality pair is one development.** Targets 1 and 3 share a 683-line
   block of 65 declarations (of which **661 already in port**), and the
   `port_advise` factorisation finds the strongest pair sharing **339 lines / 55
   proofs**. They differ in the headline: target 1 is the Γ₀(`M`) × `ℓ ∣ γ 1 1`
   rationality step, target 3 the `S`-twist/conjugation statement over
   `Γ₁(N)`. Write the engine once and keep the two headlines as its consumers.
2. **70 names are proved in ≥2 target files, ≈349 removable lines.** Beyond the pair,
   the largest are `exists_rat_combination` (9 copies / 41 lines),
   `qExpansion_coeff_widthN` (20 / 25), `tauPair` (10 / 17), `exists_map` (10 / 14,
   the copies already disagree on length — 14 vs 6), `qExpansion_coeff_unique'`
   (28 / 13), `Gamma_le_Gamma1` (20 / 12), `intSeriesC_ne_zero_of_constantCoeff`
   (2 / 10).
3. **Block structure** (`once` / `inport` / decls): 683/661/65 (the pair),
   432/309/41 (target 1 alone), 231/107/28 (target 3 alone), 227/94/26 (target 2),
   163/106/19 (target 4). Target 5 contributes no block — nothing in it is
   duplicated anywhere in the pool, which is the same signal as its 0% ported
   surface: it is wholly new.
4. **The level-`N` spelling is the generalise surface.** 31 names are binder-only
   variants and 50 share a name with a *different* statement, nearly all of them the
   pin's newer files threading the level explicitly where the port's WLight copies do
   not: `fricke N v` vs `fricke v`, `ds N s v` vs `ds s v`, `ev N id R` vs `ev id R`,
   `vm N γ v` vs `vm γ v`, `redN` with/without `(N : ℕ)`, `conj_mem_Gamma N` vs `N`
   explicit, plus the `coeffEmb_eq_map` `L`/`ℂ` pair. Each must be read against both
   statements — the ratio (0.98–0.99) is not a licence.
5. **Verify the 17 suspect substitutions by hand** before importing them: `tauPair`
   → `PeriodPair.ofTau`, `SField` → `modularFunctionField`, `A12`/`D12`/`AΓ`/`BΓ` →
   `e4cube`, `E4cube`/`E6sq` → `UpperHalfPlaneAux.eCubeSubESq`, `fricke` →
   `WLight.WW`, `expandInt` → `expandPS`. These are the parser's type-only `def`
   matches; the same class of row was wrong twice in the X_H topic.

## 5. Module layout

| module | pin source | role |
|---|---|---|
| `ModularForms/WeightOne/RationalityDvd.lean` | `S_…_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0_of_dvd` + `S_…_exists_qExpansion_S_smul_eq_and_conj_eq_…` | the Γ₀-rationality pair's shared engine **once**, plus the two headlines |
| `ModularCurve/XH/Relrank.lean` | `S_…_le_relrank_xHFunctionField_xHTopFunctionFieldC_of_not_dvd` | the `X_H` relative-degree headline |
| `ModularCurve/X1/FunctionFieldDegree.lean` | `S_…_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index` | the finrank/index bound, over the promoted `JOneES` engine |
| `ModularCurve/X1/FunctionFieldResidue.lean` | `S_…_exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField` | the residue-field model |

Namespaces stay `ModularCurve` / `ModularForm` (the pin's). The two JOneES-tail
modules sit beside `X1/FunctionField.lean` because that is where the engine they
consume lives; `RationalityDvd.lean` sits in `ModularForms/WeightOne/` because both
its headlines import the WLight wrapper cluster. Whether the pair's `RatAt`/`TD`/
`TRel` extensions belong in the new module or extend `Defs/RatAt.lean` /
`Defs/GammaRational.lean` is decided at dispatch by reading the pin — §7 item 2 is
the build price of the second option.

## 6. Sets and work orders

Three sets, one agent per set, reviewed between sets (playbook §3.4). Order is free
— every target is ready and none cites another — so the cut is by mathematics:

* **SET-R-A — the Γ₀-rationality pair.** Targets 1 and 3, written once
  (`RationalityDvd.lean`). New: 79 declarations / ≈1,300 lines; the pair's 683-line
  block is 661 lines already in port. Includes the promotions from `Gamma1Basis`
  (14 rows) and `Gamma0Rationality` (5 rows) — see §7 item 2.
* **SET-R-B — the `X_H` relrank.** Target 2 (`XH/Relrank.lean`). New: 143
  declarations / ≈1,200 lines; the largest single new declaration is `core` (~83
  lines), then `linearIndependent_pow_y` (~65). Reuses the SET-H-C
  `HeckeInputsHAll` helpers.
* **SET-R-C — the JOneES tail.** Targets 4 and 5, in that order
  (`FunctionFieldDegree.lean`, then `FunctionFieldResidue.lean`, the latter
  independent of the former). New: 107 declarations / ≈1,600 lines, plus the
  `JOneES` promotions of §7 item 1. Target 5 is the only wholly new theory in the
  cluster and should be written last, when the promoted engine is settled.

## 7. Budget and risk register

**Budget.** Net new `port_plan` 3,698; raw new-declaration span 4,114; written-÷-content
1.0–1.2 (the AC/MC/X₁ calibration) gives **≈3,700–4,500 written lines** across the
three sets — 1,300 / 1,200 / 1,600, each inside the one-subagent rule. The 264
substitution rows (≈2,104 raw lines) are import, not work.

**Named risks, in the order they will bite.**

1. **The `JOneES` promotions (51 rows / 572 lines, targets 2 and 4).** 46 of
   target 4's 49 in-port declarations are `private` in
   `ModularCurve/X1/FunctionField.lean`. Priced with `build_ladder.py --edit`:
   **4 dependent modules / 1,279 lines / ≈29 s** — a leaf-grade edit, unlike the
   ds-head riders. **Wiring first:** only the two JOneES `Thm_` wrappers are in
   `SOURCES` today; the `S_` file the port was transcribed from
   (`S_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC.lean`)
   is not, and a promoted declaration is checker-visible, so appending it — or the
   target `S_` file, which declares the same helpers publicly — is a prerequisite
   of the promotion pass, not an afterthought. `promoted` will move; reconcile it.
   *Predicted low.*
2. **The WeightOne hubs.** Promoting the pair's rows prices at
   `Gamma1Basis.lean` **6 modules / 2,815 lines / ≈80 s**,
   `Gamma0Rationality.lean` **32 modules / 17,662 lines / ≈231 s**,
   `Defs/RatAt.lean` **35 modules / 21,790 lines / ≈264 s**. A promotion pass
   touching the latter two is a wave, not a leaf. Mitigation: prefer a local
   re-derivation in the new module for the 5 + 14 rows (each 4–14 lines) over a hub
   promotion, and record the duplicate in the friction log. *Predicted medium — the
   cluster's only real build cost.*
3. **The `generalise` rows (§4 item 4).** 31 binder-only + 50 statement-different
   names, dominated by the level-`N` threading. Resolve by reading both statements
   before writing; do not "fix" the port's WLight copies to the pin's newer spelling
   without checking their consumers. *Predicted medium.*
4. **The 17 suspect `def` substitutions (§4 item 5).** `tauPair`, `SField`, the
   `E4`/`E6`/`A12`/`D12` family, `fricke`, `expandInt`. Each is a `def` whose *type*
   matches and whose body may not. *Predicted low once read.*
5. **The import-only definition check.** `--ready` does not do it. Only target 5's
   `coeffMap_jqModC` (~3 lines, body already inline in the port) surfaced; re-run the
   hand-check per order. *Predicted low.*
6. **Statement fidelity at the `Thm_` boundary.** All five headlines are verified
   against their wrappers, not their `S_` files (the `S_` files carry the same
   statements under `solution`). Append the five wrappers to `SOURCES` with the
   modules. The `S_` files are needed only where a set promotes: SET-R-C appends the
   JOneES `S_` file (§7 item 1), SET-R-A may need the `Gamma1Basis`/
   `Gamma0Rationality` pin sources for its 19 private rows.

## 8. Faithfulness and verification recipe (per set)

1. **Checker.** Append the set's `Theorems/Thm_<stem>.lean` wrappers to `SOURCES`
   last and the new modules to `PORT_FILES`; run
   `python3 spec/check_flt_statements.py`. Target `0 mismatched / 0 missing`.
   Baseline today `6520 (312 promoted, 83 renamed), 0 mismatched, 0 missing, 36 own
   (6556 checked)`. Verify with a one-token mutation (expect exactly one more
   `mismatched`) and revert.
2. **Consumer.** Extend `spec/XHConsumer.lean` or add `spec/QExpFieldConsumer.lean`;
   the error count is the deliverable and every zone must delete-fail.
3. **Axioms.** `#print axioms` on the set's headlines; expect
   `[propext, Classical.choice, Quot.sound]`.
4. **Build ladder.** `lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false`
   for the edit loop; one `flock .lake/flt_build.lock timeout 300 lake build` at the
   set boundary; whole-tree at the end.
5. **Coverage.** Re-run §0 and record the remaining figure moving per set.

## 9. What this topic is not

* Not the `C`-layer capstone `qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull`
  of [TOPIC-qexp-function-field-c.md](TOPIC-qexp-function-field-c.md) — that is a
  34-node unported cone whose `JOneES`/socket set is a different cut; this topic is
  the *ready* head that sits above the ported `JOneES` layer, and the two should be
  reconciled (the sibling's status predates the `JOneES` landing).
* Not the `X_H` Hecke/diamond inputs
  ([TOPIC-xH-hecke-diamond-inputs.md](../hecke/TOPIC-xH-hecke-diamond-inputs.md));
  the relrank target *consumes* that layer. Not the weight-one rectification either;
  the rationality pair consumes its wrappers.
* Not the `modularFunctionFieldFullC` definition layer, the `JH`/Tate layer, or the
  remaining 33 `ModularCurve` ready nodes (`exists_qExpansion_S_smul…`,
  `LevelN.*`, `ModularPolynomialData.*`, the Frobenius/`periodAlongOf` group); each
  is its own cut once this head is down.
* Not a re-opening of **route A**, the pin's integral-structure route the C′
  shortcut avoided. Measured: the Γ₀-rationality pair stands on the C′ cone's
  ported base (16/16 and 20/20 premises), no target here touches route A's
  criterion or its Eichler–Shimura layer, and pruning route A's proof is 4
  nodes / 800 lines with zero rewire obligations. The head's own gap and the
  interface it does *not* retire are accounted in
  [../../../studies/qexp-head-and-integrality.md](../../../studies/qexp-head-and-integrality.md)
  (§4–§6 there; §6 also records the one saving-direction overlap — target 1 at
  `ℓ = 1` re-derives the ported C′ Γ₀ node, 1,267 lines).
* Not the `CuspForm`/`WeierstrassCurve`/`AlgebraicCurve`/`AutomorphicForm`/`PeriodPair`
  silos the same frontier command exposes.
