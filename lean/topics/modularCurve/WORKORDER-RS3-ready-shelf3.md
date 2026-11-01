# WORKORDER RS3 — ready shelf 3: the five `ModularCurve` rows (orders A–C)

**Status: dispatched 2026-11-01, all five rows landed green the same day.** Two agents, one at a
time: orders A + C by the first, order B by the second. The measured landing is
[TOPIC-ready-shelf-3.md](TOPIC-ready-shelf-3.md) §11. Scoping: [TOPIC-ready-shelf-3.md](TOPIC-ready-shelf-3.md)
(read §0 for the read, §0.2 for the definition audit, §2 for the rows, §4 for the homes, §5 for the
traps, §6 for the gates). Pin `anthropics/fermats-last-theorem@aa2d8b3`; port mathlib `v4.34.0`.

**Five rows / 2,426 silo / 2,046 net** (≈2,066 by hand), in three orders over three disjoint files.
**The manager lane is empty: there is no ground prep to land (§0).** The statements and proofs are
the workers'.

| order | row (`ModularCurve.` dropped) | silo | net | home |
|---|---|---:|---:|---|
| A | `SiegelUnit.exists_modularForm_gamma1_coe_eq_prod_siegelFun_pow_mul_discriminant_pow` | 249 | | **new** `ModularCurve/SiegelUnit/ProductForm.lean` |
| A | `SiegelUnit.isIntegral_qExpansion_slash_S_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow` | 469 | | the same new module |
| A | `SiegelUnit.qExpansion_one_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow` | 457 | | the same new module |
| B | `natCard_doubleCoset_le_card_fibres_of_finrank_eq_index` | 1,123 | 878 | insert `ModularCurve/LevelN/GenusFF.lean` |
| C | `ModularPolynomialData.separable_map_ratFunc_of_natCast_ne_zero` | 128 | 97 | insert `ModularCurve/ModularPolynomialCoset.lean` |
| | **5** | **2,426** | **2,046** | 1 new, 2 inserts |

Checker baselines taken on this tree (so a landing can be diffed): `SiegelUnit/Integrality.lean`
**116 ok / 0 / 0**; `LevelN/SpecialRamification.lean` **18 ok / 0 / 0**; `LevelN/GenusFF.lean`
**2 ok / 0 / 0**; `ModularPolynomialCoset.lean` **34 ok / 0 / 0**. Corpus `aa2d8b3`.

### Errata, verified at dispatch (manager)

- **`restrictMF` has no public copy in the port.** `ModularForms/Level/Degeneracy.lean:44` is
  `private def restrictMF` inside `namespace ModularForm.DegeneracyPort`, and
  `DeligneSerre/Lifting.lean:70` is a second private copy. So A2 does **not** import it: write the
  pin's 4-line `def` plus its `rfl` `coe_restrictMF` privately in the new module, exactly as the two
  `IsIntegral` helpers are written. No promotion, no hub edit, no `own:` row (private declarations
  are invisible to the checker). Corrected above in §0's promotions row, A0, A2, A4.
- **`check_port.py`'s state file is shared and not concurrency-safe.** Two runs at once race on
  `tmp/check-port/state.json.tmp` and one dies with `FileNotFoundError` (hit at dispatch). Run it
  **serialized** — never alongside another checker run.
- **Re-measured on this tree, so the numbers above hold:** pin clone at `aa2d8b3`; the five `S_`
  files at 249 / 469 / 457 / 1,123 / 128 lines; `GenusFF` **2 ok / 0 / 0** and
  `ModularPolynomialCoset` **34 ok / 0 / 0** re-run and green; the A premises
  (`exists_isIntegral_hasSum_prod_siegelFun_pow` `Integrality:1468`,
  `prod_siegelFun_pow_specialLinearGroup_smul` `Basic:733`, `hasSum_coeff_etaProd_pow`
  `JqCoefficients:690`, `qExpansion_coeff_mul_width` `QExpansionCoeff:406`), the A4 helpers
  (`T_mem_Gamma1`/`Gamma_le_Gamma1` `Gamma1Slash:65,77`, `qParam_one_eq_pow`/`natCast_pos`
  `RatAt:113,115`, `T_pow_mem_Gamma` `Prelude:287`), and the C premises
  (`transcendental_jqModC` `PhiDegree:74`, `card_primCosetReps_eq_dedekindPsi` `Gamma0Index:725`,
  `coeff_jqModC_neg_one` `JqCoeff:196`, `qExpandAlg` `Laurent:230`) all present as stated; none of
  the four B-imports imports `GenusFF` or `ModularPolynomialCoset`, so no cycle.
- **Dispatch split.** Two agents, one at a time: **(1) orders A + C** (disjoint files, no heartbeat
  risk), then **(2) order B** (`LevelN/GenusFF`, its own wall time, §6).

## 0. Ground prep: none, measured

The recipe's four manager lanes were each checked and each is empty for this set:

| lane | verdict | the measurement |
|---|---|---|
| definition layer (`Def_*`) | **none** | six pin `Def_` modules in the five rows' closure (16 target files, 372 declarations); `spec/gate_scan.py` reads **0 missing** on all six (the index is public-only — see its `port_index`), so no definition has to be written, promoted or moved |
| promotions | **none** | the 15 `GenusFF` declarations the 1,123 row needs are used **in module**; `restrictMF` has **no public copy** in the port (see the errata below) and is re-spelled in the new module like the `IsIntegral` helpers (`isIntegral_intCast` 4 lines, `isIntegral_natCast` 7 lines) |
| migrations | **none** | none of the three homes is in `spec/old_check_stmts.py`'s `PORT_FILES`; the new module is fresh, the two insertion hosts are already wired and green |
| bridge / refactor | **none** | no premise of the five rows needs the `LaurentSeries` instance bridge (the 1,123 row's `Φ` is a ring hom into an intermediate field of `K`, not an `AlgHom` into `LaurentSeries`) |

**The wires are not prep.** The six `spec-pin:` lines for A and the two each for B and C are appended
**with the declarations, in the same edit**, by the worker (or by the manager at merge once the
declarations are in). A `spec-pin:` line that names a source before its declaration lands is exactly
MD-001's false ported marker: `frontier.py --selfcheck` fails, and the row disappears from the demand
while reading as done. Do not pre-wire.

So this order starts from a clean tree: `--selfcheck` PASSes (1,319 `Thm_` sources, 1,484 union
nodes), `needed [F terminal]` is 931 / 378,258 (corrected 932 / 378,519), and the only thing to
write is the mathematics.

## 1. Order A — the Siegel product form and its q-expansion (1,175 silo / 1,075 net)

One new module, **one story in three layers**, in the pin's three namespaces. Do the layers in
order: 249 first (the others take its conclusion as a hypothesis), then 469, then 457.

### A0 — the module

- **Home:** `lean/FLTForHuman/ModularCurve/SiegelUnit/ProductForm.lean` (new, module docstring at
  the top: the Siegel product `u_μ Δ^t`, its modularity on `Γ₁(N)` and its two q-expansion
  conclusions). Header carries **no** `spec-pin:` line yet — add the six at the end of the order,
  when all three headlines exist (six lines: wrapper + `S_` for each of the three rows, the `S_`
  lines marked `-- comparable copy`).
- **Imports** (the core; A4 adds the helper modules, all acyclic):
  `FLTForHuman.ModularCurve.SiegelUnit.Integrality`, `FLTForHuman.ModularCurve.JqCoefficients`,
  `FLTForHuman.NumberTheory.ModularForms.QExpansionCoeff` (for `qExpansion_coeff_mul_width`).
  `Defs.SiegelFunction`, `Defs.Laurent`, `Hauptmodul`, `QParamUnique`, `SiegelUnit.Basic` are already
  above `Integrality`.

### A1 — `SiegelUnit.exists_modularForm_gamma1_coe_eq_prod_siegelFun_pow_mul_discriminant_pow` (249)

- Wrapper: `Theorems/Thm_ModularCurve_SiegelUnit_exists_modularForm_gamma1_coe_eq_prod_siegelFun_pow_mul_discriminant_pow.lean`;
  `S_`: `P2M/Sol/S_…_exists_modularForm_gamma1_coe_eq_prod_siegelFun_pow_mul_discriminant_pow.lean`
  (249 lines, 24 declarations).
- Namespace: the pin's `FORM`; public headline at the wrapper's name in `ModularCurve.SiegelUnit`.
- Statement: `∃ ϑ : ModularForm (Γ₁ N) (12 * t)`, `ϑ` equals `∏_{r,s} siegelFun N r s ^ (12*N*m r s) *
  Δ^t` pointwise, and every `S`-slash `ϑ ∣[12t] β` is `O(exp(-2π((Ord β)/N + t)·im))` at `i∞`.
  Copy the wrapper's text exactly (the `ht` hypothesis is the long `Ord` sum; do not re-spell it).
- Proof shape (the pin, all of it new): `uFun`, `Ord`, `thetaFun`, `discr_slash`,
  `thetaFun_slash_apply`, `e00…e11`/`det_rel`/`rowMul`/`mT`/`mT_zero`/`mT_rowMul`/`idx_cast`,
  `uFun_smul`, `ord_eq`, `discr_isBigO`, `norm_C_eq_one`, `thetaFun_slash_isBigO`,
  `mdifferentiable_thetaFun`, the `ModularForm` structure `theta` and `theta_apply`, then `solution`.
  `discr_isBigO` consumes mathlib's `CuspFormClass.exp_decay_atImInfty` and `CuspForm.discriminant`.
- **Trap.** `uFun`, `thetaFun`, `P1728`, `P144`, `deltaZ`, `sigmaSeries`, `GammaS` have **type-only**
  twins in the port (`uFun → LevelN.jAnalytic`, `P1728/deltaZ/P144 → e1Chi3`, `thetaFun → EIS2K1.qN`,
  `sigmaSeries → EtaQSeries.f`, `GammaS → Gamma0Upper`). They share a type, not a value; do not
  import them (a `P1728 = e1Chi3` would be a silent mathematical error).
- Pin artifacts to drop: `autoImplicit false`, `p2m_export`/`p2m_open`/`p2m_reactivate`, the
  wrapper's attribute walls. No `#print axioms` line (there is none in this file).
- Checker after: **3 ok / 0 / 0** for the module once A1–A3 are in (the three public headlines;
  private prelude rows are invisible to the checker).

### A2 — `…isIntegral_qExpansion_slash_S_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow` (469)

- Wrapper/`S_`: `Theorems/Thm_…_isIntegral_qExpansion_slash_S_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow.lean`
  and the matching `P2M/Sol/S_…` (469 lines, 31 declarations).
- Namespace: the pin's `ModularCurve.SiegelUnit.IntZero`; public headline in `ModularCurve.SiegelUnit`.
- Statement: `∃ a, ∀ n, IsIntegral ℤ ((N : ℂ) ^ a * (qExpansion (N : ℝ) (ϑ ∣[12t] S)).coeff n)`, with
  `ϑ` a `Γ₁(N)`-form equal to the Siegel product (the `hϑ` hypothesis).
- Proof shape: the `Group` block (`GammaS`, `restrictMF`, `mem_GammaS_iff`, `T_pow_mem_GammaS`,
  `natCast_mem_strictPeriods_GammaS`, `GammaS_le_conjS`), `Forms` (`Thetaform`, `coe_Thetaform`),
  `QSeries` (`hasSum_shift`, `hasSum_spread`, `qExpansion_coeff_eq_of_hasSum_div_qParam_zpow`),
  `Siegel` (`uProd`, `uProd_eq_zero`, `uProd_S_smul`, `slash_S_apply`, `qParam_one_eq_pow`,
  `hasSum_discriminant_pow`, `isIntegral_intCast`), then `main`. The `IntZero.main` block is the
  pin's `by_cases m 0 0 = 0` split; the non-zero branch instantiates
  `SiegelUnit.exists_isIntegral_hasSum_prod_siegelFun_pow` at `e r s = m (-s) r`.
- **Use, do not restate:** `T_pow_mem_Gamma` from `LevelN/Prelude.lean` (public); `T_mem_Gamma1`,
  `Gamma_le_Gamma1`, `qParam_one_eq_pow`, `natCast_pos` from the port at the wrapper's binders (A4).
  `restrictMF` is **not** imported: the port's copies are `private` (`ModularForms/Level/Degeneracy.lean:44`
  in `ModularForm.DegeneracyPort`, `DeligneSerre/Lifting.lean:70`), so write the pin's 4-line `def`
  and its `coe_restrictMF` (`rfl`) privately in the new module — a promotion there is a hub edit with
  a cascade for four lines, and the checker only reads public declarations (see A4, errata).
  `isIntegral_intCast` is 4 lines — re-spell it (`simp`-close `IsIntegral ℤ (z : ℂ)` from
  `isIntegral_algebraMap`); if the checker objects, the manager writes the `own:` row, not the worker.
- **Trap.** The wrapper carries a 13-lemma `[-simp]` wall. Do not transcribe it; if a `simp` call
  needs one of them, use a local `simp only […]` at that call site.
- Checker after: **+1 ok / 0 / 0** over A1.

### A3 — `…qExpansion_one_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow` (457)

- Wrapper/`S_`: `Theorems/Thm_…_qExpansion_one_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow.lean`
  and the matching `P2M/Sol/S_…` (457 lines, 45 declarations).
- Namespace: the pin's `DeltaQExpInt` and `INTINF`; public headline in `ModularCurve.SiegelUnit`.
- Statement: with `m₀` pinned by `(N : ℤ) * m₀ = Ord + (N : ℤ) * t`, `∃ a` such that
  `qExpansion 1 ϑ` vanishes below `m₀`, is non-zero at `m₀`, `N^a * (coeff m₀)⁻¹` is integral, and
  `N^a * coeff n` is integral for every `n`.
- Proof shape: the `DeltaQExpInt` block (`sigmaSeries`, `E4Z`, `E6Z`, `qExpansion_E₄/E₆_eq_map`,
  `P144`, `P1728`, `E4Z_cube_sub_E6Z_sq`, `twelve_dvd*`, `deltaZ`, `C_mul_deltaZ`,
  `qExpansion_discriminant_eq`, the coefficient lemmas, `coeff_zero/one_deltaZ`), then `INTINF`
  (`EvA` and its laws, `qParam_natCast_pow/zpow`, `deltaN` and `CoeffMem`, `isIntegral_natCast`),
  then `solution`. The `EvA_of_forall_hasSum` bridge converts the product's `HasSum` into
  coefficient membership; `C_mul_deltaZ`/`qParam_one_eq_pow` normalise the width-1 expansion.
- **Use, do not restate:** `isIntegral_natCast` is 7 lines — re-spell as in A2. `coeff_jqModC_*` are
  not needed here. `qParam_one_eq_pow` and `T_mem_Gamma1` at the wrapper's binders.
- Checker after: **+1 ok / 0 / 0** over A2.

### A4 — the helper layer 469/457 need, and the one decision in it

The 249 layer imports nothing of this; the 469 and 457 layers each re-prove a short "group facts"
prelude in the pin (`T_mem_Gamma1`, `Gamma_le_Gamma1`, `T_pow_mem_Gamma`, `conj_mem_Gamma`,
`coeGL_mul`, `qParam_one_eq_pow`, `natCast_pos`, `strictPeriods_Gamma1`,
`one_mem_strictPeriods_Gamma1`, `natCast_mem_strictPeriods_Gamma1`). The port has public copies of
some and only private or no copies of the rest. **Import the public ones; write the pin's short fact
for the rest** — a wire source may state a declaration the module writes or imports; the checker
only reads the module's own declarations, and an absent pin copy is not a `MISSING`. The criterion
is the import's closure: never pull a 38- or 158-module tree for a 3–5-line fact.

| helper | pin lines | port home (public) | closure | call |
|---|---:|---|---:|---|
| `Gamma_le_Gamma1`, `T_mem_Gamma1` | 6, 3 | `ModularForms/Level/Gamma1Slash.lean` | 2 | **import** (both) |
| `qParam_one_eq_pow`, `natCast_pos` | 9, 6 | `ModularForms/WeightOne/Defs/RatAt.lean` | 5 | **import** (both) |
| `conj_mem_Gamma` | 4 | `ModularForms/WeightOne/Defs/GammaRational.lean` | 38 | write the 4 lines |
| `T_pow_mem_Gamma` | 5 | `ModularCurve/LevelN/Prelude.lean:287` | 38 | write the 5 lines |
| `strictPeriods_Gamma1` | 3 | — (mathlib's `CongruenceSubgroup.strictPeriods_Gamma1` is a different statement) | — | write |
| `one_mem_strictPeriods_Gamma1` | 5 | **private** in `ModularForms/WeightOne/IntegralWeightOneForm.lean` and `Gamma0Rationality.lean` | — | write |
| `natCast_mem_strictPeriods_Gamma1` | 5 | absent | — | write |
| `coeGL_mul` | 4 | `ModularCurve/X1/DiamondCorrespondence.lean` | **158** | write the 4-line `map_mul` |
| `GammaS` | 4 | none: `CohCarrier.Gamma0Upper` is a **type-only** match, a different subgroup | — | write |
| `isIntegral_intCast`, `isIntegral_natCast` | 4, 7 | private in `SiegelUnit/Integrality.lean` / `SiegelUnit/Eisenstein.lean` | — | write; do not promote |
| `restrictMF` (+ `coe_restrictMF`) | 4, 3 | **private only**: `ModularForms/Level/Degeneracy.lean:44` (`ModularForm.DegeneracyPort`), `DeligneSerre/Lifting.lean:70` | — | write private in the new module (errata; no public copy exists) |

The two imports are `ModularForms/Level/Gamma1Slash` and `ModularForms/WeightOne/Defs/RatAt` (add
them to A0's list). Everything else is ≈40 lines of the pin's own facts, written once in the new
module and checked `ok` against the 469/457 wire; `dedup.py` will not see a cross-module cluster
because the port's copies of those facts stay private or absent.

### A5 — the surface gate (review, not the worker)

After A1–A3 are green and wired, drop `private` from the module's prelude, `check_port --force`, and
read the three numbers: every `ok` is a pin-faithful statement the pin states public and may be
promoted; every `MISMATCH` is the pin's own prelude copy re-spelled (keep it private); every
`MISSING` is a port-side helper (keep it private). The proofs do not change.

## 2. Order B — the special-fibre bounds for `j` on `X(N)` (1,123 silo / 878 net)

One row, one insertion, the set's long pole. **Give it its own wall time; do not run it against the
build of another order.**

### B0 — the pin's map, read at dispatch (so the worker does not roam)

| pin lines | block | contents |
|---|---|---|
| 20–35 | scaffold | the `P2MW.…` namespace, the two attribute walls, `autoImplicit false`, `set_option synthInstance.maxHeartbeats 1600000` — **none transcribed** |
| 40–118 | special points | `E₄_smul`, `E₆_smul`, `S_smul_I`, `ST_smul_ρ`, `TinvS_smul_ρ`, `E₆_I`, `denom_TinvS_ρ`, `ρ_ne_one`, `E₄_ρ`, `jAnalytic_ρ`, `jAnalytic_I` |
| 121–265 | `Gpm` and its orders | `abbrev Gpm`, `mem_Gpm_imp/of`, `entry_10/01…`, `dvd_of_T/S/ST_pow_mem`, `T_pow_mem_Gamma` (public at `LevelN/Prelude.lean:287`), `one_ne_zero_zmod`, `S_sq`, `coe_ST`, `ST_cube`, `Gamma_le_Gamma1` (public at `Gamma1Slash:77`), the three `neg_one_mem_zpowers_*` |
| 269–490 | `Galois` | `apply_eq_self_of_mem_adjoin`, `isIntegral_of_apply_eq(_sub)`, `algHom_apply_algebraMap`, `adjoin_inv_eq`, `ord_sub_eq_ord_sub`, `stab`, `mem_stab_iff`, `natCard_stab_eq_ord`, `stab_eq_zpowers`, `natCard_doubleCoset_le` |
| 492–546 | `Lift` | `liftE`, `liftE_apply`, `restrictScalars_liftE`, `liftHom`, `liftHom_apply`, `restrictScalars_liftHom`, `liftHom_eq_one_iff`, `liftHom_ker` |
| 548–643 | `LevelN` | `galoisPackage`, `comp_smul_mem`, `σK` + `σK_algebraMap/ker/fix`, `fixedField_σK`, `transcendental_jK`, `finiteDimensional_jK`, `finrank_jK`, `isGalois_jK`, `σ'`, `restrictScalars_σ'`, `σ'_apply/ker/eq_one_iff/pow_eq_one_iff`, `mem_stab_σ'_iff`, `σ'_surjective` |
| 645–791 | `Stabilisers` | `orderOf_σ'_S/ST/T`, `subsingleton_gal_of_lt_two`, `exists_place_1728/zero/infty` |
| 793–831 | `ConstantField` | `adjoin_adjoin_subset`, `adjoin_range_eq_top` (feed the port's `finrank_le_and_natCard_places_le_of_constantFieldExtension_adjoin`) |
| 833–884 | `Main` (part 1) | `T_mem_Gamma1`, `neg_one_mem_center`, `isDomain_ring` (→ `LevelN.isDomain_ring M`, one application), `finrank_fixedField_map` |
| 889–1065 | `Main` (part 2) | the `variable (Γ) (hΓ)` block, `local notation ℚ̄`/`FF`, `include K hΓ in`, `set_option maxHeartbeats 6400000 in`, **`main_K`** (170 lines) — the wall |
| 1067–1084 | `Main` (part 3) | `main` — the wrapper's statement, three lines of proof via `main_K (FractionRing (LevelN.ring M))` |
| 1095–1123 | `solution` | the wrapper's alias of `main`; the port writes **one** public headline at the wrapper's name, everything else private |

The port writes **one** public declaration: `ModularCurve.natCard_doubleCoset_le_card_fibres_of_finrank_eq_index`
at the wrapper's statement, which spells `hfull`'s adjoin as
`Module.finrank (IntermediateField.adjoin (AlgebraicClosure ℚ) ({y} : Set (…))) (…) = (Γ ⊔ Subgroup.zpowers (-1)).index`
— the pin's `main` uses `ℚ̄⟮y⟯` for the same thing, and **the wrapper's full spelling is what the
checker diffs**. `main_K` may stay private, and decomposing its proof into private lemmas at the
pin's own `have` boundaries does not change the public statement.

### B0.1 — the two walls, and how to stay under the cap

- **`main_K`.** The pin's 6.4M override is not transcribed, and the port has no
  `set_option maxHeartbeats`. Split the 170-line proof at its own internal steps (the three
  conjuncts; the `finrank_fixedField_map` reduction; the three `exists_place_*` applications) into
  private lemmas with the pin's hypotheses, so each command meets the 200k edit loop. If one lemma
  still cannot, report it as a localised overrun in the FR-0074 form with the module building — a
  report, not a cap.
- **`synthInstance.maxHeartbeats 1600000` (pin line 26)** exists because some search in this file is
  slow. Find it with `set_option trace.Meta.synthInstance true` plus `-DmaxHeartbeats=3000` on the
  offending declaration, then supply that instance explicitly at the section head (`haveI : … := …`),
  the way shelf 2's order C replaced its `Module.Free`/`finrank_pos_iff_of_free` search. Do not
  transcribe the option.
- **The edit loop re-elaborates the whole host** (784 lines + your new section) on every run:
  expect ~1 min, which is fine; put only statements you mean to keep in the file. Use
  `lean/tmp/Scratch.lean` for statement probes that do not need the file's private prelude.
- **The private prelude resolves from the appended section.** Verified at dispatch: in one file,
  `LevelN.GenusBound.dvd_of_ST_pow_mem` resolves from `namespace ModularCurve`, and
  `open ModularCurve.LevelN.GenusBound in` works too. `rho` (the pin's `ρ : ℍ`) is
  `GenusFF`'s private `rho` (`:80`) with `coe_rho`/`rho_sq`; `Gpm` is the pin-shaped private
  `abbrev` at `:188`, and the public `LevelN.GaloisStructure.Gpm` also exists.
- Do **not** copy the prelude, do **not** promote it (that is the §6 gate's review experiment).

### B1 — the row

- Wrapper: `Theorems/Thm_ModularCurve_natCard_doubleCoset_le_card_fibres_of_finrank_eq_index.lean`;
  `S_`: `P2M/Sol/S_…_natCard_doubleCoset_le_card_fibres_of_finrank_eq_index.lean` (1,123 lines,
  83 declarations).
- **Home:** append to `ModularCurve/LevelN/GenusFF.lean` (784 lines; 2 public declarations, one
  dependent `ModularCurve/Period/ParabolicHomsBasis.lean`). Namespace: the pin's
  `ModularCurve.SpecialFibresLB` (disjoint from the module's existing private
  `ModularCurve.LevelN.GenusBound`); public headline at the wrapper's name in `namespace ModularCurve`.
- **Imports to add:** `FLTForHuman.ModularCurve.LevelN.QExpBridge`,
  `FLTForHuman.ModularCurve.LevelN.SpecialRamification`,
  `FLTForHuman.AlgebraicCurve.IsCurveOver.ConstantFieldExtensionSpan`,
  `FLTForHuman.ModularCurve.Degree.PhiDegree`. (`OrbitCardinality`, `IsCurveOver.Transcendental`,
  `WeightOne.LevelN`, `Places`, `FieldGalois` are already in the closure; no cycle — the
  reachability check is in the brief §4.)
- Wire: append **two** `spec-pin:` lines (wrapper + `S_`) to the module's leading `/- … -/` block,
  and extend its subject sentence to name the fibre bounds as the module's second subject.
- **The prelude is already written.** `GenusFF`'s 15 private declarations (`E₆_I`, `Gpm`,
  `mem_Gpm_imp`, `entry_01/10…`, `dvd_of_T/S/ST_pow_mem`, `apply_eq_self_of_mem_adjoin`,
  `isIntegral_of_apply_eq`, `adjoin_inv_eq`, `liftE`, `restrictScalars_liftE`, `liftHom`,
  `restrictScalars_liftHom`, `one_ne_zero_zmod`) are byte-identical to the pin's; use them *from the
  same file* by qualified name from `namespace ModularCurve`
  (`LevelN.GenusBound.dvd_of_ST_pow_mem`, or `open ModularCurve.LevelN.GenusBound in …` at a section
  head). **Do not copy them, do not promote them** unless the §A4-style surface gate is run
  deliberately.
- **Statement.** Copy the wrapper's text exactly: `M : ℕ`, `[NeZero M]`, `Γ : Subgroup SL(2,ℤ)`,
  `hΓ : CongruenceSubgroup.Gamma1 M ≤ Γ`, `y` in `laurentBaseChange (AlgebraicClosure ℚ)
  (qExpFunctionFieldC ℚ Γ)`, `hy : (y : LaurentSeries ℚ̄) = jqModC ℚ̄`, `hfull : finrank
  ℚ̄⟮y⟯ FF = (Γ ⊔ zpowers (-1)).index`, and the three `Nat.card (DoubleCoset.Quotient …) ≤
  Nat.card {P // 0 < P.ord y}`, `… (y - 1728)`, `… P.ord y < 0` conjuncts. The binders are the
  deliverable; the port's `GenusBound` row spells `AlgebraicClosure ℚ` in full for the same reason.
- **Proof shape (the pin's sections).** `Galois` (`S_smul_I`, `ST_smul_ρ`, `TinvS_smul_ρ`,
  `E₄_smul`, `E₆_smul`, `E₆_I`, `E₄_ρ`, `jAnalytic_ρ`, `jAnalytic_I`, `ρ_ne_one`,
  `denom_TinvS_ρ`); `Lift` (`liftE`, `liftHom`, their `restrictScalars` and `pow_eq_one` lemmas);
  `LevelN` (`galoisPackage`, `comp_smul_mem`, `σK`, `jK`, `σK_ker`, `fixedField_σK`,
  `transcendental_jK`, `finiteDimensional_jK`, `finrank_jK`, `isGalois_jK`, `σ'`,
  `orderOf_σ'_S/ST/T`, `subsingleton_gal_of_lt_two`); `Stabilisers` (`stab`, `mem_stab_iff`,
  `natCard_stab_eq_ord`, `stab_eq_zpowers`, `natCard_doubleCoset_le`, `exists_place_1728/zero/infty`);
  `ConstantField` (`adjoin_adjoin_subset`, `adjoin_range_eq_top`, `finrank_le_and_natCard_places_le…`);
  `Main` (`finrank_fixedField_map`, `main_K`, `main`, `solution`). `main_K` is ≈170 lines; split it
  into the pin's own pieces, not by cutting proof steps.
- **The two substitutions that are not imports.** `isDomain_ring` (pin 846) uses
  `WLight.levelN_structure_package` only for its no-zero-divisors clause: replace the pin's 12-line
  proof with `ModularCurve.LevelN.isDomain_ring M` (`LevelN/FieldGalois.lean:61`, already in
  `GenusFF`'s closure and used at its line 750). `T_pow_mem_Gamma` (pin 170) is already public in
  `LevelN/Prelude.lean:287`, and `Prelude` is already in `GenusFF`'s closure (via `FieldGalois` and
  `Places`), so **use it — do not re-write the five lines** (this differs from order A, whose
  closure does not reach `Prelude`).
- **Trap 1 — the wall.** The pin sets `synthInstance.maxHeartbeats 1600000` at module level and
  `set_option maxHeartbeats 6400000 in` on `main_K` (lines 26, 895). **Neither may be transcribed.**
  The port cap is 4M and the edit loop 200k. Probe the `main_K` statement in `tmp/` first; if the
  block cannot meet 200k, split at `finrank_fixedField_map` / `galoisPackage` /
  `exists_place_*` and report the residue as a localised overrun in the FR-0074 form (module still
  building) rather than bumping a cap.
- **Trap 2 — `include K hΓ in` and `local notation`.** The pin states `main_K` under
  `variable (Γ) (hΓ)` with `local notation "ℚ̄"`/`"FF"` and `include K hΓ in`. The port's convention:
  make the variables explicit or split the section; the wrapper's statement spells
  `AlgebraicClosure ℚ` and `laurentBaseChange …` in full, and that is what the checker diffs.
- **Trap 3 — the attribute walls.** The wrapper carries two long `attribute [-instance]` /
  `[-simp]` walls; do not transcribe them. Local `simp only` if a call needs one.
- **Trap 4 — the namespace split.** The module already has a private `GenusBound.main` (the genus
  inequality) and the pin's `SpecialFibresLB.main` is a different statement with the same last name.
  Keep both, in their own namespaces; the pin itself writes both.
- Checker after: **≥3 ok / 0 / 0** (the two existing headlines plus the new one, plus whatever the
  worker exposes; private rows are invisible).

## 3. Order C — separability of `Φ_N` over `K(X)` (128 silo / 97 net)

One row, one insertion, the cheapest order; it is also the door to the mod-ℓ block.

- Wrapper: `Theorems/Thm_ModularCurve_ModularPolynomialData_separable_map_ratFunc_of_natCast_ne_zero.lean`;
  `S_`: `P2M/Sol/S_…_separable_map_ratFunc_of_natCast_ne_zero.lean` (128 lines, 7 declarations).
- **Home:** append to `ModularCurve/ModularPolynomialCoset.lean` (871 lines, **0 importers**), in the
  pin's `IgusaSepAux` namespace; public headline at `ModularCurve.ModularPolynomialData.…` in
  `ModularCurve`. **New import:** `FLTForHuman.ModularCurve.Degree.PhiDegree` (acyclic);
  `Gamma0Index` (for `card_primCosetReps_eq_dedekindPsi`) is already in the closure.
- Wire: append **two** `spec-pin:` lines to the header, and name the separability conclusion in the
  module's subject sentence.
- Statement (verbatim from the wrapper):
  `(K : Type*) [Field K] (N : ℕ) [NeZero N] (data : ModularCurve.ModularPolynomialData N)
  (hNK : (N : K) ≠ 0) : ((data.Φ.map (Polynomial.mapRingHom (Int.castRingHom K))).map
  (algebraMap (Polynomial K) (RatFunc K))).Separable`.
- Proof shape: `separable_map_ratFunc_of_transcendental` (10 lines — the transfer along a
  transcendental generator, via `IsFractionRing.lift` and `Polynomial.separable_map`),
  `map_aeval_comp_mapRingHom_intCast` (5), `transcendental_qExpand_jqModC` (10), then `solution`:
  take `L = AlgebraicClosure K`, a primitive `N`-th root `ζ`, `x = qExpand L N (jqModC L)`, build
  `P = Φ_N(ζ, x)` from the coset-root roots, `P = cosetTwoVarPoly` by
  `eq_cosetTwoVarPoly_of_forall_isRoot`, separable by `separable_cosetTwoVarPoly`, and descend to
  `K(X)` by the transfer.
- **Use, do not restate:** `coeff_jqModC_neg_one` and `coeff_jqModC_of_lt` (`Defs/JqCoeff.lean`),
  `qExpandAlg` (`Defs/Laurent.lean`), `card_primCosetReps_eq_dedekindPsi` (`Gamma0Index.lean`),
  and the three coset-root theorems in the host. Binder spellings are in the port; take them.
- Checker after: **35 ok / 0 / 0** (34 → 35).

## 4. The consumer zone

Each order delivers its own zone file in `spec/` (so parallel workers never edit one file):
`spec/ModularCurveReady3ZoneA.lean`, `spec/ModularCurveReady3ZoneB.lean`,
`spec/ModularCurveReady3ZoneC.lean`; the manager merges them into
`spec/ModularCurveReady3Consumer.lean` at landing. Real cross-module compositions, no `#check`s:

- **A:** apply 249 to get `ϑ`, then 469 for `a` and 457 for `m₀`; compose the product with
  `SiegelUnit.prod_siegelFun_pow_specialLinearGroup_smul` and read the `S`-slash coefficient
  integrality at `n = m₀` (the row pair's own cross-module step).
- **B:** instantiate the three inequalities at a concrete `K` (the port's `LevelN/FunctionField`
  model or `FractionRing (LevelN.ring N)`), and compose with
  `LevelN.exists_place_ord_jGen_le_two_three_level` and the genus inequality in the same module.
- **C:** compose the new separability row with `ModularPolynomialFibreTwo`'s `Φ₂` data and
  `separable_cosetTwoVarPoly` (e.g. derive separability for the level-two `data` at a field `K`
  with `(2 : K) ≠ 0`).

**The error count is the deliverable metric.**

## 5. Build and gate discipline (all orders)

1. `python3 spec/check_port.py --force <module>` → **0 mismatch, 0 missing**; every added
   declaration `ok` (or an `own:`/`pin:` row in `spec/decl_markers.tsv`, which the **manager**
   writes, not the worker). The module's `spec-pin:` lines are the only claim of ported surface;
   add them in the same edit as the declarations.
2. `#print axioms` on every public headline → `[propext, Classical.choice, Quot.sound]`; no
   `sorry`/`admit`/`axiom`/`native_decide`.
3. The module's own `lake build` under `flock` and `timeout`, and **the module silent**. A
   `Replayed` line is not evidence the `.olean` exists — build the defining module explicitly
   (FR-0033). **No tree build.** No dependents.
4. `dedup.py --within --module <module>` and `move_dead.py`; report clusters, do not refactor
   wrapper-over-engine pairs (the pin's own `main`/`solution`, `theta`/`theta_apply`).
5. Zero warnings. **No** `set_option maxHeartbeats`, `set_option synthInstance.maxHeartbeats`,
   `set_option autoImplicit false`, `p2m_*` lines, or `attribute [-instance]`/`[-simp]` walls.
6. **Stop and report** (do not improvise) if: a statement does not elaborate against the
   wrapper's text; a needed premise is missing or private; the 200k loop is exceeded and the
   split points above do not recover it; a build exceeds the timeout; or the checker reports a
   `MISMATCH` whose fix would change a statement. A blocker report is a deliverable, a silent
   `sorry` is not.

## 6. Sequence

1. **A and C first** (disjoint files, no heartbeat risk): A is a new module, C an insertion into a
   0-importer module. Both can run concurrently.
2. **B in parallel if there is a third lane**, with its own wall time; otherwise immediately after
   A/C. B edits `LevelN/GenusFF.lean`, which no other order touches; its one dependent
   (`Period/ParabolicHomsBasis`) re-elaborates and is not otherwise edited.
3. **The manager** wires nothing before the declarations exist; at each landing it writes/confirms
   the `spec-pin:` lines and the header subject sentence, merges the consumer zone, runs the
   surface gate on the touched module, re-reads the shelf (recipe §7: the consumed 2,426, the new
   `needed`, the one row the set makes ready), records the landing in
   `TOPIC-ready-shelf-3.md`, and appends frictions to `lean/logs/frictions.md`.

The forecast to check at the end: all five rows land → `needed` 932 / 378,519 → **927 / 376,093**,
MC ready 6 / 2,450 → **2 / 276**, and exactly one row becomes ready,
`SiegelUnit.exists_gamma1_peaked_auxiliary_form_twelve_dvd` (252).
