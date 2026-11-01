# WORKORDER RS2 — ready shelf 2: the six `ModularCurve` successors (orders A–D)

**Status: landed (2026-10-31) — all four orders green; the measured landing is
[TOPIC-ready-shelf-2.md](TOPIC-ready-shelf-2.md) §12.** Scoping: [TOPIC-ready-shelf-2.md](TOPIC-ready-shelf-2.md)
(read §0.3 for the shelf, §2 for the rows, §5 for the traps, §6 for the gates). Pin
`anthropics/fermats-last-theorem@aa2d8b3`; port mathlib `v4.34.0`.

**Six rows / 1,478 silo / 1,242 net** (≈1,150 after the hand reads below), in four orders. The
manager lane is **landed** (§0.3 here); nothing else is pre-done: the statements and proofs are
yours.

| order | row (`ModularCurve.` dropped) | silo | net | home |
|---|---|---:|---:|---|
| B1 | `ModularPolynomialData.exists_isPrimitiveRoot_forall_isRoot_cosetConj_complex` | 347 | 295 | insert `ModularCurve/ModularPolynomialCoset.lean` |
| B2 | `ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient2_j` | 28 | 11 | insert `ModularCurve/ModularPolynomialFibreTwo.lean` |
| D | `LevelN.exists_place_ord_jGen_le_two_three_level` | 303 | 243 | **new** `ModularCurve/LevelN/SpecialRamification.lean` |
| A | `SiegelUnit.exists_isIntegral_hasSum_prod_siegelFun_pow` | 364 | 348 | insert `ModularCurve/SiegelUnit/Integrality.lean` |
| C1 | `genusFF_qExpFunctionFieldC_eq_of_ringHom` | 265 | 197 | **new** `ModularCurve/X1/FunctionFieldConstExt.lean` |
| C2 | `transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC` | 171 | ≈70 (hand) | the same new module |

**Do the orders in this sequence: B, D, A, C.** B and D have no pin heartbeat cap and are the
cheapest; A and C are the set's two elaboration walls (§5.1 of the brief). Finish and gate one order
before starting the next; do not leave a non-compiling file behind.

## 0. Ground already landed (do not redo, do not edit these modules)

| item | module | state |
|---|---|---|
| `ρ_ne_one` promoted `private` → public, `ModularCurve.JMultiplicity.ρ_ne_one` | `ModularCurve/TateSlots/Invariants.lean:1052` | build green (9 s, silent); `check_port --force`: **154 ok / 0 / 0**; matched at `S_…meromorphicOrderAt_…:110` |
| `coeffMap_intSeriesC_gen` renamed and promoted → public `ModularCurve.QExpAutBaseChange.coeffMap_intSeriesC` | `ModularCurve/X1/CoeffMap.lean:96` | build green (24 s, module silent; the 11 warnings in the log are pre-existing ones in `AlgebraicCurve/Defs/LocalResidue.lean` and `Genus/Stichtenoth.lean` in the cascade); `check_port --force`: **95 ok / 0 / 0**; matched at `S_…existsUnique_algEquiv_…:28` |
| `ModularPolynomialFibreTwo.lean` wired (it had no `spec-pin:` line) | `ModularCurve/ModularPolynomialFibreTwo.lean` | `check_port --force`: **1 ok / 0 / 0**; no Lean edit, no build needed |
| bridge | **new** `AlgebraicCurve/Place/LaurentSeriesRingHom.lean`: `Place.exists_ord_mul_eq_order_of_ringHom` — the place/order dictionary for a *ring hom* `F →+* LaurentSeries K` that sends constants to `HahnSeries.C`, so it carries no `LaurentSeries`-side algebra instance (the `HahnSeries.instAlgebra` / `powerSeriesAlgebra` diamond, §2; the module pins the former locally) | `1 own / 0 / 0` (port spelling, `own:` row); build green, 2.1 s, silent |

Both promotions are public at the pin's names: **import them, do not restate them**. The new wires
added to the two headers are the pin `S_` files that state them publicly; do not remove them.

Definition layer: **none needed** — the eleven `Def_` modules of the six rows' closure are landed
(`gate_scan`: 0 missing; the three `QAdicPlaceMod` names the scan reports are already in the port as
`order_jqModC`, `jqModC_ne_zero_of_nontrivial`, `order_qExpand`). No migration.

## 1. Order B — the coset roots and the Φ₂ fibre (375 silo / 306 net)

Two insertions, two files, one story. **B1 first, B2 immediately after** (B2 is two lines on B1's
neighbours and SET-MS7's module).

### B1 — `exists_isPrimitiveRoot_forall_isRoot_cosetConj_complex` (347)

- Wrapper: `Theorems/Thm_ModularCurve_ModularPolynomialData_exists_isPrimitiveRoot_forall_isRoot_cosetConj_complex.lean`;
  `S_`: `P2M/Sol/S_ModularCurve_ModularPolynomialData_exists_isPrimitiveRoot_forall_isRoot_cosetConj_complex.lean`
  (347 lines, 19 declarations).
- Home: append to `ModularCurve/ModularPolynomialCoset.lean` (551 lines, **0 importers**). New imports:
  `FLTForHuman.ModularCurve.ModularPolynomialE4Cube` (and `…JqIntegralRatios` if you name
  `jqModC_eq_qExpansion_E4_cube_div_discriminant`; it is also in `E4Cube`'s closure).
- Wire: append **two** `spec-pin:` lines to the host's leading `/- … -/` block (the wrapper and the
  `S_` file). Do not add others.
- Statement (verbatim from the wrapper):

```
theorem ModularCurve.ModularPolynomialData.exists_isPrimitiveRoot_forall_isRoot_cosetConj_complex
    (N : ℕ) [NeZero N] (data : ModularCurve.ModularPolynomialData N) :
    ∃ ζ : ℂˣ, IsPrimitiveRoot ζ N ∧ ∀ t ∈ ModularCurve.primCosetReps N,
      (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℂ))
        (ModularCurve.qExpand ℂ N (ModularCurve.jqModC ℂ)))).IsRoot
        (ModularCurve.cosetConj ζ (ModularCurve.jqModC ℂ) t)
```

- **The trap, and it is this order's whole risk.** The port's `ModularCurve.DeepCosetAux.An`
  (`ModularPolynomialE4Cube.lean:131`) is `AnalyticAt (cuspFunction 1 f) 0` — the **width-1
  specialisation** of the pin's `An (h : ℝ) (f)`, and its `qExpansion_finset_prod` / `_sum_smul` /
  `qExpansion_pow'` / `An.mul` / `An.add` / `An.smul` are stated at `qExpansion 1` / `An` (no `h`).
  They are *weaker statements*, not binder variants, and **cannot** serve this proof, which needs
  width `N` (`An N`, `qExpansion N`). Write the pin's `CosetRootFormalAux` block at width `h` in a
  namespace of your own (the pin's `An`/`Nice`/`qExpansion_finset_prod`/`_sum_smul`/
  `qExpansion_pow'`, ≈130 lines). Import from the port only: `ModularCurve.CosetTranslate.cosetPt`
  (already in the host), `ModularCurve.DeepCosetAux.pow_mul_div_pow`,
  `UpperHalfPlaneAux.qParam_one_eq_pow`.
- **Use, do not restate:** the host's own `private theorem hasSum_laurent`
  (`ModularPolynomialCoset.lean:439`, generalised to `hper`/`hhol` instead of a `Nice` bundle) is
  usable from the same file; derive the pin's `Nice`-shaped version from it in three lines or keep
  the pin's shape. Also in the host: `qExpansion_cosetTranslate_eq_cosetSubst` is the row's premise
  already; `qTwist`, `cosetSubst` are there.
- Proof shape (the pin): pick the primitive root `ζ = exp(2πi/N)`, reduce `t = (a,b,d)` with
  `cosetConj_eq`; set `A = q(E₄)`, `D = q(Δ)`, `J = jqModC ℂ`; the identity
  `J = A³/D`; the `N`-monomial sum `H = ∑ c_{i,k} • (A³)^k D^{m-k} ((G₁)³)^i (G₂)^{n-i}` is **zero**
  as a function (`eval_E4_cube_div_discriminant_coset_eq_zero` + `pow_mul_div_pow`), hence its
  `qExpansion N` is zero after multiplying by `D^m (cs D)^n`; conclude the evaluation at `cosetConj`
  is `0`.
- Checker baseline: 20 ok; after: **21 ok / 0 / 0** (the new headline only).

### B2 — `fibrePoly_j_eq_prod_veluQuotient2_j` (28)

- Wrapper: `Theorems/Thm_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient2_j.lean`;
  `S_`: `P2M/Sol/S_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient2_j.lean`.
- Home: append to `ModularCurve/ModularPolynomialFibreTwo.lean` (315 lines, **0 importers**; the
  module is now wired, 1 ok). New import: `FLTForHuman.ModularCurve.ModularPolynomialLevelTwo`
  (acyclic — `LevelTwo` does not import `FibreTwo`); add **two** `spec-pin:` lines for this row.
- Proof: the pin's `solution` is exactly
  `rw [ModularCurve.ModularPolynomialData.phi_eq_phiTwo data]` then
  `exact ModularCurve.fibrePoly_phiTwo_j_eq_prod_veluQuotient2_j h2 W hι P hP hPeq hPgy hΔ`.
  Both premises are in the port (`ModularPolynomialLevelTwo.lean:383`,
  `ModularPolynomialFibreTwo.lean:302`).
- **Statement trap:** the conclusion's right-hand factor is
  `C (@WeierstrassCurve.j K _ (W.veluQuotient2 (P i).1 (P i).2) ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)` —
  the explicit `IsUnit` argument is part of the statement; copy the wrapper's text, do not let Lean
  insert a different instance. The port's premise spells exactly that, so `exact` should close.
- Checker after: **2 ok / 0 / 0**.

## 2. Order D — the special places of `X(N)` (303 silo / 243 net)

- Wrapper: `Theorems/Thm_ModularCurve_LevelN_exists_place_ord_jGen_le_two_three_level.lean`;
  `S_`: `P2M/Sol/S_ModularCurve_LevelN_exists_place_ord_jGen_le_two_three_level.lean` (303 lines,
  26 declarations).
- Home: **new file** `ModularCurve/LevelN/SpecialRamification.lean`. Imports (verified acyclic):
  `FLTForHuman.ModularCurve.LevelN.Places`,
  `FLTForHuman.ModularCurve.LevelN.FieldGalois`,
  `FLTForHuman.ModularCurve.TateSlots.Invariants`,
  `FLTForHuman.AlgebraicCurve.Place.LaurentSeriesModel`,
  **`FLTForHuman.ModularCurve.Degree.LaurentGlue`** (for `order_qExpand`, which the first
  attempt found missing), and **`FLTForHuman.AlgebraicCurve.Place.LaurentSeriesRingHom`** (the
  bridge of §0). Wire: two `spec-pin:` lines (wrapper + `S_`). Namespace:
  `ModularCurve.LevelN.SpecialRamification` (the pin's).
- Statement (verbatim from the wrapper):

```
theorem ModularCurve.LevelN.exists_place_ord_jGen_le_two_three_level (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ModularCurve.LevelN.ring N) K]
    [IsScalarTower ℂ (ModularCurve.LevelN.ring N) K]
    [IsFractionRing (ModularCurve.LevelN.ring N) K] :
    (∃ W : AlgebraicCurve.Place ℂ K,
        0 < W.ord (algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N) - 1728) ∧
          W.ord (algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N) - 1728) ≤ 2) ∧
      (∃ W : AlgebraicCurve.Place ℂ K,
        0 < W.ord (algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N)) ∧
          W.ord (algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N)) ≤ 3) ∧
      (∃ W : AlgebraicCurve.Place ℂ K,
        W.ord (algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N)) < 0 ∧
          -(N : ℤ) ≤ W.ord (algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N)))
```

- Import, do not restate: `ModularCurve.JMultiplicity.E₆_I`,
  `ModularCurve.JMultiplicity.denom_TinvS_ρ`, and the **just-promoted**
  `ModularCurve.JMultiplicity.ρ_ne_one` (all in `TateSlots/Invariants.lean`); the row's four premises
  `LevelN.exists_algHom_laurentSeries_qExpansion` (`LevelN/FieldGalois.lean:821`),
  `LevelN.exists_place_analyticOrderAt_eq_mul_ord` (`LevelN/Places.lean:1170`),
  `meromorphicOrderAt_E4_cube_div_discriminant_sub_eq_card_stabilizer_div_two`
  (`TateSlots/Invariants.lean:1539`), `Place.exists_ord_mul_eq_order_of_algHom_laurentSeries`
  (`AlgebraicCurve/Place/LaurentSeriesModel.lean:691`). Write the pin's `SpecialRamification` block
  (`E₄_smul`, `E₆_smul`, `S_smul_I`, `ST_smul_ρ`, `TinvS_smul_ρ`, `E₄_ρ`, `jAnalytic_ρ`,
  `jAnalytic_I`, `jAnalytic_sub_ne_zero`, the two `natCard_stabilizer_*_le`, `jK`,
  `mdifferentiable_jAnalytic`, `analyticAt_comp_ofComplex`, `comp_ofComplex_apply_coe`,
  `analyticOrderAt_jsub`, `co_algebraMap_ring`, `jsub_mem`, `algebraMap_jsub`,
  `exists_place_ord_sub_le`, `exists_place_ord_neg_ge`, `main`). The port's `jAnalytic_I` is
  `private` (`LevelN/GenusFF.lean:167`), so write the pin's four-line proof; the public
  `ModularCurve.JMultiplicity.jf_eq_of_E₆_eq_zero` (`TateSlots/Invariants.lean:1400`) proves the same
  fact for `jf = E₄³/Δ`, which is `LevelN.jAnalytic` by definition — read both (and check the defeq)
  before choosing.
- **The cusp conjunct's dictionary step — the only step that blocked the first attempt — is
  solved by the bridge of §0; do not try to transport `E`.** `LevelN.exists_algHom_laurentSeries_qExpansion`'s
  `E` carries `HahnSeries.powerSeriesAlgebra`, while
  `Place.exists_ord_mul_eq_order_of_algHom_laurentSeries` is frozen at `HahnSeries.instAlgebra`,
  and no `AlgHom` cast survives the instance check (nine spellings were tried). Use the ring-hom
  form:

```
  obtain ⟨E, hEj, -⟩ := ModularCurve.LevelN.exists_algHom_laurentSeries_qExpansion M K
  have hC : ∀ c : ℂ, E (algebraMap ℂ K c) = HahnSeries.C c := by
    intro c
    rw [E.commutes, HahnSeries.algebraMap_apply']
    simp
  have hordj : (E (algebraMap (ModularCurve.LevelN.ring M) K
      (ModularCurve.LevelN.jGen M))).order = -(M : ℤ) := by
    rw [hEj, order_qExpand, order_jqModC]
    ring
  obtain ⟨W, γ, hγ, hW⟩ :=
    AlgebraicCurve.Place.exists_ord_mul_eq_order_of_ringHom (K := ℂ) (F := K) E.toRingHom hC
      ⟨algebraMap (ModularCurve.LevelN.ring M) K (ModularCurve.LevelN.jGen M),
        by rw [hordj]; exact_mod_cast NeZero.ne M⟩
```

  and then the pin's two closing steps verbatim (`W.ord jK < 0` by contradiction from
  `w.ord jK * γ = -(M:ℤ)` and `γ > 0`; `-(M:ℤ) ≤ W.ord jK` from `1 ≤ γ` and `nlinarith`).
  `order_qExpand` and `order_jqModC` are public (`Degree/LaurentGlue.lean:72`,
  `Defs/JqCoeff.lean:208`); `E.toRingHom` is instance-free and `hC` is the producer's own
  `commutes` at its instance. Keep `E` out of any `→ₐ` ascription and add no `local instance` pin
  to this module.
- **Two Lean notes from the first attempt:** `omit … in theorem` does not parse in this toolchain
  (use a `variable` re-ordering, or a section-level `omit`), and the file needs the `LaurentGlue`
  import named above — the row's `S_` file imports `Def_ModularCurve_QAdicPlaceMod`, whose
  `order_qExpandC` is the port's `order_qExpand`.
- No pin heartbeat cap. No new definitions.
- Checker after: the new module's declarations `0 mismatch / 0 missing`; make the pin-public
  prelude public where the pin states it publicly (surface gate, §6 of the brief).
- **Landed (2026-10-31).** `ModularCurve/LevelN/SpecialRamification.lean`, 310 lines, 18 public /
  0 private; edit loop silent at 200k (4.5 s); module build exit 0 (4.4 s); checker
  **18 ok / 0 mismatch / 0 missing**; axioms `[propext, Classical.choice, Quot.sound]`; dedup
  0 clusters; consumer zone appended, 0 errors. Two adjustments worth carrying:
  (i) `hordj` is *stated* about `E.toRingHom (algebraMap …)`, not `E (algebraMap …)`, otherwise
  `rw [hordj]` does not match `hW`'s conclusion (`E.toRingHom x` versus `E x`); (ii) because
  `omit … in theorem` does not parse in this toolchain, the pin's single `variable (M) (K)` block is
  split into three `variable` blocks (before `coe_algebraMap_ring`, before `jK`, and the
  `[NeZero M]`/`[IsFractionRing]` pair before the three places lemmas) — the declaration text is
  unchanged, which is why all 18 statements still match.

## 3. Order A — the Siegel product (364 silo / 348 net)

- Wrapper: `Theorems/Thm_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_prod_siegelFun_pow.lean`;
  `S_`: `P2M/Sol/S_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_prod_siegelFun_pow.lean`
  (364 lines, 18 declarations).
- Home: append to `ModularCurve/SiegelUnit/Integrality.lean` (1,094 lines, **0 importers**). New
  import: `FLTForHuman.ModularForms.Hauptmodul` (acyclic; `hasSum_qParam_mul` is there). Wire: two
  `spec-pin:` lines.
- Statement: the long `∃ C d, C^N = 1 ∧ (∀ n, IsIntegral ℤ (d n)) ∧ d 0 = ∏ s, (1 - exp …)^(12N e 0 s)
  ∧ d 0 ≠ 0 ∧ IsIntegral ℤ (N^(12N∑e) * (d 0)⁻¹) ∧ (∀ τ, HasSum …) ∧ Tendsto … atImInfty`
  — verbatim from the wrapper; copy it, do not paraphrase.
- Premise engine: `ModularCurve.SiegelUnit.exists_isIntegral_hasSum_siegelFun`
  (`SiegelUnit/Integrality.lean:1069`, already in the host, arbitrary `N r s`) and
  `ModularCurve.hasSum_qParam_mul` (`ModularForms/Hauptmodul.lean:119`). Write the pin's `SExpPi`
  block (`IsIntPS` + `Expands` and their `mul`/`pow`/`prod`, ≈130 lines), then `main`:
  instantiate the engine at each `(r,s)`, assemble `Pser = ∏ A_{rs}^{12Ne(r,s)}`, multiply the
  `HasSum`s with `hasSum_qParam_mul`, and push the `i∞` limit through the finite product.
- **The set's worst heartbeat wall: the pin's `main` carries `set_option maxHeartbeats 12800000`
  (line 136). Do not copy it; the module must build without any `set_option`.** Probe plan before
  writing: keep the pin's factoring (`hdata`, `hE`, `hCst`, `key` as separate private lemmas), state
  the headline first with `sorry`-cut private lemmas **in a `tmp/` scratch file**, and measure. The
  edit loop is 200k and the build cap is 4M; if `main` cannot fit even as a build, split it along
  the pin's own `key`/`hCst` boundary and report the real cost. Drop the pin's `#print axioms
  solution` (line 362).
- Checker baseline 115 ok; after: **116 ok / 0 / 0**.
- If the elaboration cannot be brought under the build cap, land the module with the pin's proof
  restructured as far as it goes and report precisely which declaration overruns — do not leave a
  `sorry` in the module and do not add a `set_option`.

## 4. Order C — the constant extension of the q-expansion function field (436 silo / ≈270 net)

One **new file** for both rows: `ModularCurve/X1/FunctionFieldConstExt.lean`, namespace
`ModularCurve.QExpConstExt` (the pin's). Imports (verified acyclic):
`FLTForHuman.ModularCurve.X1.FunctionFieldIndex`,
`FLTForHuman.AlgebraicCurve.Genus.ConstantFieldExtensionConsequences`,
`FLTForHuman.AlgebraicCurve.IsCurveOver.Transcendental`,
`FLTForHuman.RingTheory.LaurentSeriesAlgebraic`.
Wire: four `spec-pin:` lines (two wrappers + two `S_` files).

### C1 — `genusFF_qExpFunctionFieldC_eq_of_ringHom` (265)

- Wrapper: `Theorems/Thm_ModularCurve_genusFF_qExpFunctionFieldC_eq_of_ringHom.lean`; `S_`:
  `P2M/Sol/S_ModularCurve_genusFF_qExpFunctionFieldC_eq_of_ringHom.lean` (265 lines, 13 declarations).
- Statement (verbatim): `{K₀ K} [Field K₀] [Field K] [IsAlgClosed K₀] [IsAlgClosed K] (φ : K₀ →+* K)
  (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hfg : ∃ x : qExpFunctionFieldC K₀ Γ,
  Transcendental K₀ x ∧ FiniteDimensional (adjoin K₀ {x}) (qExpFunctionFieldC K₀ Γ)) :
  genusFF K (qExpFunctionFieldC K Γ) = genusFF K₀ (qExpFunctionFieldC K₀ Γ)`.
- Import, do not restate: `ModularCurve.QExpAutBaseChange.coeffMap_mem`,
  `…coeffMap_algebraMap'`, `…coeffMap_intSeriesC` (**just promoted**; the pin's
  `coeffMap_intSeriesC`), and `ModularCurve.laurentBaseChange_qExpFunctionFieldC_eq` if you want it
  (not needed by this row). Write the pin's `QExpConstExt` block: `coeffMap_injective`,
  `coeffMap_C`, `coeffMap_algebraMap_const` (the port public copy is `coeffMap_algebraMap'`),
  `qMap`, `coeq_qMap`, `le_map_adjoin_range`, `finiteDimensional_adjoin_algebraMap`,
  `transcendental_qMap`, then `genusFF_eq` via SET 10's
  `AlgebraicCurve.genusFF_eq_of_constantFieldExtension_of_isAlgClosed`.
- **Pin cap: `set_option maxHeartbeats 3200000` on `genusFF_eq` and a module-level
  `synthInstance.maxHeartbeats 1600000`. Do not copy either.** Probe as in A; the transfer block is
  where the cost is, not the two-line genus step.

### C2 — `transcendental_and_finiteDimensional_adjoin_laurentBaseChange_…` (171)

- Wrapper: `Theorems/Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC.lean`;
  `S_`: the same stem under `P2M/Sol/` (171 lines, 10 declarations).
- **The row's engine is already in the port**: `ModularCurve.laurentBaseChange_qExpFunctionFieldC_eq`
  (`X1/CoeffMap.lean:250`) — same statement, the pin's `variable` binders written inline — and
  `BCEqProof.image_intFormRatiosC` (`:219`) / `BCEqProof.coeffEmb_mem_adjoin` (`:235`) are its
  `image_intFormRatiosC`/`coeffEmb_mem_adjoin`. Import them; write only
  `coeffEmb_ne_zero_iff` (4 lines), `finrank_adjoin_eq_relfinrank` (18 lines) and the ≈45-line
  headline (`transcendental_algebraMap_iff`, the relfinrank transport, `Module.finite_of_finrank_pos`
  via MS-6's `finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index`). Do not
  transcribe the pin's `coeffEmb_*` block: `coeffEmb_injective` (`Defs/Laurent.lean:367`),
  `coeffEmb_intSeriesC` (`JqIntegralRatios.lean`), `algebraMap_laurentSeries_eq_C`
  (`X1/FunctionFieldIsAlgClosed.lean`), `coeffEmb_algebraMap` (`X1/Pic0Correspondence.lean`) are
  public at the pin's statements (binder spellings differ; read them before choosing).
- **Pin cap: `set_option synthInstance.maxHeartbeats 1600000` + `set_option maxHeartbeats 3200000` on
  `solution`. Do not copy them.** This row also consumes FR-0074's `transfer_finrank` (240k at the
  edit loop, in `X1/FunctionFieldIndex.lean`); if your `solution` overruns 200k, localise and report
  in the FR-0074 form rather than bumping the cap.
- Checker after (new module): **2 ok / 0 / 0** for the two headlines (the module's other public
  declarations are `ok` too when public at the pin's statements).

## 5. Gates, per order (all six must hold before an order is called done)

1. Edit loop: `cd lean && timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>`
   → silent, zero warnings, on every file you touch. Never `lake build` in the edit loop.
2. `flock tmp/lean-build.lock timeout 90 lake build <module>` per finished module, logs in
   `lean/tmp/rs2/`; a `Replayed` line is not evidence the `.olean` exists — build the module itself.
   All commands under 2 minutes; anything that may run longer is a background job with its own
   `timeout` and a log file (FR-0072). **No tree build.**
3. `python3 spec/check_port.py --force <file>` → **0 mismatch / 0 missing**, every added declaration
   `ok`. New modules get exactly the wires listed above; no `spec/decl_markers.tsv` row (if you
   believe one is needed, stop and report instead).
4. `#print axioms` on every headline → `[propext, Classical.choice, Quot.sound]`; no
   `sorry`/`admit`/`axiom`/`native_decide`, no `set_option`, no linter suppression, no
   `attribute [-simp]`/`[-instance]`/`p2m_*` walls, no `autoImplicit` option, no doc cross-references
   in Lean headers or comments.
5. `cd tools/deps && python3 dedup.py --module <path/to/Module.lean> --within --tier shape
   (`--targets` wants a *file* of patterns, not a stem)` per module (report
   only). The width-`h` `An`/`Nice` block in B1 is the pin's own prelude and stays; record it.
6. One `spec/` consumer zone, one section per order, real cross-module compositions (no
   `#check`s). B and C are in `spec/ModularCurveReady2Consumer.lean` (landed); D appends its zone
   there; A writes its own `spec/ModularCurveReady2ConsumerA.lean` (the two lanes run in parallel
   and must not edit one file), and the manager merges them. Zones: B — `cosetConj` roots with `phi_eq_phiTwo` and the new
   `fibrePoly` row at `N = 2`, plus `nonempty_modularPolynomialData`; D — the three ord bounds
   instantiated at a concrete `K` (the port's `LevelN` function-field model, or
   `FractionRing (LevelN.ring N)` if the tower instances exist) composed with
   `exists_place_analyticOrderAt_eq_mul_ord`; A — the product's `HasSum`/`d 0` with
   `SiegelUnit/Basic`'s product law; C — the genus equality with `laurentBaseChange` and
   `place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC`. The zone's error count is the deliverable
   metric; build/check it as its own file.

## 6. Early feedback contract

Stop and report (with the state of the tree, the file, the failing declaration and the numbers) if:

- a statement will not elaborate at the 200k loop, or a proof overruns it and you cannot localise it;
- a home turns out to be wrong (import cycle, a premise whose port module is above the home, a
  statement needing an unported structure);
- a premise turns out to be a specialisation/shadow rather than the general statement the row
  consumes;
- you need a marker row, a `set_option`, a statement change, or an edit to a module outside your
  order (the two manager modules of §0 are off-limits, as is every module you are not appending to).

Report at the end, per order: files, declarations (public/private), lines, checker line, axioms,
build result, dedup clusters, consumer-zone result, and every deviation from the pin (with the reason).
If an order cannot be finished inside your budget, leave its file compiling (no `sorry`) and report
exactly where it stands — do not start the next order with a broken tree.
