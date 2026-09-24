# Pin inventory: ModularCurve definition modules for the `heckeOperatorsCommuteBar` cone

Pin: `/home/haitao/proj/fermats-last-theorem` @ `aa2d8b3` (read-only). Target: the 13 unported `Definitions/Def_ModularCurve_*.lean` modules imported by the remaining 82 proof files `P2M/Sol/S_ModularCurve_<stem>.lean` for the `ModularCurve.heckeOperatorsCommuteBar` cone (all 82 exist).

**How to read the `refs` column.** For every declaration I searched its *last name* (Unicode-aware word boundary) across exactly those 82 files, and split hits into buckets:
* **use n** — real occurrences in statements, proof bodies or definitions (the trustworthy signal);
* **p2m n** — hits only inside `p2m_open` / `p2m_export "ModularCurve" "…"` whitelist scaffolding (every S file repeats such a block ~8×);
* **attr n** — hits only inside `attribute [-simp] …` lines (the declaration is *named* only to be removed from the simp set);
* import lines are excluded (they name modules, not declarations, and the `_` before a declaration name in a `Thm_…_<name>` import path blocks the boundary match).
`[ns-qual n]` = extra real-code hits written with a namespace path (e.g. `PhiGen.conj`, `ModularCurve.modularUnitSeries`). No S file ever writes the fully qualified `ModularCurve.<ns>.<name>` form of an ordinary declaration, because they all `open AlgebraicCurve ModularCurve` (some also `open ModularCurve.PhiGen`).

**Homonym warning.** A few very short namespaced names have bare counts inflated by Mathlib or sibling modules and are marked † below: `IsMonicOfOrder.ne_zero/coeff_self/coeff_of_lt/single/ofPowerSeries/mul/qExpand` get hits from Mathlib `ne_zero`, dot-notation `.mul`, `HahnSeries.single`, `PowerSeries.ofPowerSeries` and from the *global* `qExpand` of `Def_ModularCurve_X0`; the namespace-qualified counts of all of them are **0**, and the string `IsMonicOfOrder` occurs **0** times in the 82 files. They are nevertheless needed transitively, because they appear in the *statements* of `isMonicOfOrder_deltaSeries(N)` / `isMonicOfOrder_modularUnitSeries`, which are referenced. The same caveat applies to the `PhiGen.*` `phiProd*`/`PoleOrderLE`/`TPoleOrderLE` etc. (qualified counts 0 but bare `phiProd` = 9 real uses).

**Signature convention.** Signatures are copied verbatim from the pin; continuation lines are joined by a space, and the trailing `:=`, `:= by`, `where` terminators are trimmed. For `def`/`abbrev`/`structure`/`instance` the first lines of the value/body are included (long ones cut with `…`), since for `: Prop := …` definitions the body *is* the statement. Private declarations are listed because they are supply code that must be reproduced, but they are not public API.

---
### 1. `Definitions/Def_ModularCurve_DegeneracyTower.lean`

*Imports:* `Definitions.Def_ModularCurve_HeckeOperator`  ·  18 decls (17 public, 1 private)

**Role.** Level-changing maps between bar function fields over any field `L`: `towerInclBar` is the inclusion `N∣M`, `towerSubstBar` is `qExpand ℓ` followed by inclusion (`N*ℓ∣M`); the `Composites` section relates them to `heckeAlphaBar`/`heckeBetaBar`, and `HeckeExchangeAt` is the divisor-exchange hypothesis consumed by the nodes `heckeOperatorBar_comm_of_heckeExchangeAt`, `heckeDivBar_comm_of_heckeExchangeAt`, `heckeOperatorsCommuteBar_of_heckeExchangeAt`. **Port dup.** None in the port; private `laurentBaseChange_mono''` duplicates the same-named private lemma in module 2 and the ported public `ModularCurve.laurentBaseChange_mono` (`ModularCurve/Defs/Laurent.lean`).

**`ModularCurve` / section `PrivateSupply`**
- **theorem** `laurentBaseChange_mono''` — refs private — `private theorem laurentBaseChange_mono'' {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)} (h : F₀ ≤ F₁) : laurentBaseChange L F₀ ≤ laurentBaseChange L F₁`
**`ModularCurve` / section `TowerMaps`**
- **def** `towerInclBar` — refs **use 28** — `def towerInclBar (h : N ∣ M) : laurentBaseChange L (modularFunctionFieldFull N) →ₐ[L] laurentBaseChange L (modularFunctionFieldFull M) := IntermediateField.inclusion (laurentBaseChange_mono'' L (full_degeneracy_le h))`
- **theorem** `coe_towerInclBar` — refs **use 3** — `theorem coe_towerInclBar (h : N ∣ M) (x : laurentBaseChange L (modularFunctionFieldFull N)) : (towerInclBar L h x : LaurentSeries L) = (x : LaurentSeries L) := IntermediateField.coe_inclusion _ x`
- **theorem** `towerInclBar_eq_inclusion` — refs **0** — `theorem towerInclBar_eq_inclusion (h : N ∣ M) (h' : laurentBaseChange L (modularFunctionFieldFull N) ≤ laurentBaseChange L (modularFunctionFieldFull M)) : towerInclBar L h = IntermediateField.inclusion h'`
- **theorem** `towerInclBar_comp_towerInclBar` — refs **use 5** — `theorem towerInclBar_comp_towerInclBar {M' : ℕ} [NeZero M'] (h₁ : N ∣ M') (h₂ : M' ∣ M) (h : N ∣ M) : (towerInclBar L h₂).comp (towerInclBar L h₁) = towerInclBar L h`
- **theorem** `towerInclBar_self` — refs **use 3** — `theorem towerInclBar_self (h : N ∣ N) (x : laurentBaseChange L (modularFunctionFieldFull N)) : towerInclBar L h x = x := Subtype.ext (coe_towerInclBar L h x)`
- **def** `towerSubstBar` — refs **use 29** — `def towerSubstBar (ℓ : ℕ) [NeZero ℓ] (h : N * ℓ ∣ M) : laurentBaseChange L (modularFunctionFieldFull N) →ₐ[L] laurentBaseChange L (modularFunctionFieldFull M) := (towerInclBar L h).comp (heckeBetaBar L N ℓ)`
- **theorem** `coe_towerSubstBar` — refs **use 2** — `theorem coe_towerSubstBar (ℓ : ℕ) [NeZero ℓ] (h : N * ℓ ∣ M) (x : laurentBaseChange L (modularFunctionFieldFull N)) : (towerSubstBar L N ℓ h x : LaurentSeries L) = qExpand L ℓ (x : LaurentSeries L)`
- **theorem** `towerSubstBar_congr` — refs **use 1** — `theorem towerSubstBar_congr {ℓ ℓ' : ℕ} [NeZero ℓ] [NeZero ℓ'] (hℓ : ℓ = ℓ') (h : N * ℓ ∣ M) (h' : N * ℓ' ∣ M) : towerSubstBar L N ℓ h = towerSubstBar L N ℓ' h'`
**`ModularCurve` / section `Composites`**
- **theorem** `heckeAlphaBar_eq_towerInclBar` — refs **use 2** — `theorem heckeAlphaBar_eq_towerInclBar : heckeAlphaBar L N ℓ = towerInclBar L (dvd_mul_right N ℓ)`
- **theorem** `heckeBetaBar_eq_towerSubstBar` — refs **0** — `theorem heckeBetaBar_eq_towerSubstBar : heckeBetaBar L N ℓ = towerSubstBar L N ℓ dvd_rfl`
- **theorem** `towerInclBar_comp_heckeAlphaBar` — refs **use 2** — `theorem towerInclBar_comp_heckeAlphaBar (h : N * ℓ ∣ M) (h' : N ∣ M) : (towerInclBar L h).comp (heckeAlphaBar L N ℓ) = towerInclBar L h'`
- **theorem** `towerInclBar_comp_heckeBetaBar` — refs **0** — `theorem towerInclBar_comp_heckeBetaBar (h : N * ℓ ∣ M) : (towerInclBar L h).comp (heckeBetaBar L N ℓ) = towerSubstBar L N ℓ h`
- **theorem** `towerSubstBar_comp_heckeAlphaBar` — refs **0** — `theorem towerSubstBar_comp_heckeAlphaBar (h : N * ℓ' * ℓ ∣ M) (h' : N * ℓ ∣ M) : (towerSubstBar L (N * ℓ') ℓ h).comp (heckeAlphaBar L N ℓ') = towerSubstBar L N ℓ h'`
- **theorem** `towerSubstBar_comp_heckeBetaBar` — refs **use 3** — `theorem towerSubstBar_comp_heckeBetaBar (h : N * ℓ' * ℓ ∣ M) (h' : N * (ℓ * ℓ') ∣ M) : (towerSubstBar L (N * ℓ') ℓ h).comp (heckeBetaBar L N ℓ') = towerSubstBar L N (ℓ * ℓ') h'`
- **theorem** `heckeSquareBar_commutes` — refs **use 1** — `theorem heckeSquareBar_commutes (h₁ : N * ℓ ∣ M) (h₂ : N * ℓ' * ℓ ∣ M) : (towerInclBar L h₁).comp (heckeBetaBar L N ℓ) = (towerSubstBar L (N * ℓ') ℓ h₂).comp (heckeAlphaBar L N ℓ')`
**`ModularCurve` / section `Exchange`**
- **theorem** `dvd_of_eq_roof` — refs **use 36** — `theorem dvd_of_eq_roof (hM : M = N * ℓ * ℓ') : N * ℓ ∣ M ∧ N * ℓ' * ℓ ∣ M := ⟨⟨ℓ', hM⟩, ⟨1, by rw [hM]; ring⟩⟩`
- **def** `HeckeExchangeAt` — refs **use 6** — `def HeckeExchangeAt (hM : M = N * ℓ * ℓ') : Prop := ∀ [HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull (N * ℓ)))] [HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull M))] (hβ : (heckeBet ...`

### 2. `Definitions/Def_ModularCurve_HeckeOperator.lean`

*Imports:* `Definitions.Def_AlgebraicCurve_Correspondence`, `Definitions.Def_ModularCurve_ArithmeticGalois`  ·  17 decls (13 public, 4 private)

**Role.** α/β degeneracy maps `heckeAlphaBar` (inclusion) and `heckeBetaBar` (q-expansion) plus their integrality predicates and the induced `Divisor`/`Pic0` correspondences (`heckeDivBar`, `heckePic0Bar`) and transposes. **Port dup.** The four private lemmas duplicate: `coeffMap_qExpand'`↔ported public `ModularCurve.coeffMap_qExpand`, `coeffEmb_qExpand'`↔ported `ModularCurve.coeffEmb_qExpand` (both `ModularCurve/Defs/Laurent.lean`); `laurentBaseChange_mono'` duplicates ported `laurentBaseChange_mono`; only `qExpand_mem_laurentBaseChange'` is not in the port.

**`ModularCurve` / section `PrivateSupply`**
- **theorem** `coeffMap_qExpand'` — refs private — `private theorem coeffMap_qExpand' {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) [NeZero n] (x : LaurentSeries R) : coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x)`
- **theorem** `coeffEmb_qExpand'` — refs private — `private theorem coeffEmb_qExpand' (L : Type*) [Field L] [Algebra ℚ L] (n : ℕ) [NeZero n] (x : LaurentSeries ℚ) : coeffEmb L (qExpand ℚ n x) = qExpand L n (coeffEmb L x) := coeffMap_qExpand' _ n x`
- **theorem** `laurentBaseChange_mono'` — refs private — `private theorem laurentBaseChange_mono' {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)} (h : F₀ ≤ F₁) : laurentBaseChange L F₀ ≤ laurentBaseChange L F₁`
- **theorem** `qExpand_mem_laurentBaseChange'` — refs private — `private theorem qExpand_mem_laurentBaseChange' {F₀ : IntermediateField ℚ (LaurentSeries ℚ)} (n : ℕ) [NeZero n] {F₁ : IntermediateField ℚ (LaurentSeries ℚ)} (hF : ∀ y ∈ F₀, qExpand ℚ n y ∈ F₁) {x : LaurentSeries L} (hx : x ∈ laurentBaseChange L F₀) : qExpand L n x ∈ laurentBaseChange L F₁`
**`ModularCurve` / section `DegeneracyMapsBar`**
- **def** `heckeAlphaBar` — refs **use 25** — `def heckeAlphaBar : laurentBaseChange L (modularFunctionFieldFull N) →ₐ[L] laurentBaseChange L (modularFunctionFieldFull (N * ℓ)) := IntermediateField.inclusion (laurentBaseChange_mono' L (full_degeneracy_le (dvd_mul_right N ℓ)))`
- **theorem** `coe_heckeAlphaBar` — refs **0** — `theorem coe_heckeAlphaBar (x : laurentBaseChange L (modularFunctionFieldFull N)) : (heckeAlphaBar L N ℓ x : LaurentSeries L) = (x : LaurentSeries L) := IntermediateField.coe_inclusion _ x`
- **def** `heckeBetaBarRingHom` — refs **0** — `def heckeBetaBarRingHom : laurentBaseChange L (modularFunctionFieldFull N) →+* laurentBaseChange L (modularFunctionFieldFull (N * ℓ))`
- **theorem** `coe_heckeBetaBarRingHom` — refs **0** — `theorem coe_heckeBetaBarRingHom (x : laurentBaseChange L (modularFunctionFieldFull N)) : (heckeBetaBarRingHom L N ℓ x : LaurentSeries L) = qExpand L ℓ (x : LaurentSeries L)`
- **def** `heckeBetaBar` — refs **use 25** — `def heckeBetaBar : laurentBaseChange L (modularFunctionFieldFull N) →ₐ[L] laurentBaseChange L (modularFunctionFieldFull (N * ℓ)) := { heckeBetaBarRingHom L N ℓ with commutes' := fun a => Subtype.ext <| by`
- **theorem** `heckeAlphaBar_eq_inclusion` — refs **0** — `theorem heckeAlphaBar_eq_inclusion (h : laurentBaseChange L (modularFunctionFieldFull N) ≤ laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) : heckeAlphaBar L N ℓ = IntermediateField.inclusion h`
- **theorem** `coe_heckeBetaBar` — refs **use 2** — `theorem coe_heckeBetaBar (x : laurentBaseChange L (modularFunctionFieldFull N)) : (heckeBetaBar L N ℓ x : LaurentSeries L) = qExpand L ℓ (x : LaurentSeries L)`
**`ModularCurve` / section `HeckePic0Bar`**
- **def** `HeckeAlphaBarIntegral` — refs **use 4** — `def HeckeAlphaBarIntegral : Prop := (heckeAlphaBar L N ℓ).toRingHom.IsIntegral`
- **def** `HeckeBetaBarIntegral` — refs **use 4** — `def HeckeBetaBarIntegral : Prop := (heckeBetaBar L N ℓ).toRingHom.IsIntegral`
- **def** `heckeDivBar` — refs **use 3** — `def heckeDivBar : Divisor L (laurentBaseChange L (modularFunctionFieldFull N)) →+ Divisor L (laurentBaseChange L (modularFunctionFieldFull N)) := Divisor.correspondence (heckeBetaBar L N ℓ) (heckeAlphaBar L N ℓ) hβ hα`
- **def** `heckePic0Bar` — refs **0** — `def heckePic0Bar (hFI : FundamentalIdentityAlong L (heckeBetaBar L N ℓ) hβ) (hfin : FiniteAlong L (heckeAlphaBar L N ℓ)) (hN : NormFormulaAlong L (heckeAlphaBar L N ℓ) hfin) : Pic0 L (laurentBaseChange L (modularFunctionFieldFu ...`
**`ModularCurve` / section `Transpose`**
- **def** `heckeDivBarTranspose` — refs **0** — `def heckeDivBarTranspose : Divisor L (laurentBaseChange L (modularFunctionFieldFull N)) →+ Divisor L (laurentBaseChange L (modularFunctionFieldFull N)) := Divisor.correspondence (heckeAlphaBar L N ℓ) (heckeBetaBar L N ℓ) hα hβ`
- **def** `heckePic0BarTranspose` — refs **0** — `def heckePic0BarTranspose (hFI : FundamentalIdentityAlong L (heckeAlphaBar L N ℓ) hα) (hfin : FiniteAlong L (heckeBetaBar L N ℓ)) (hN : NormFormulaAlong L (heckeBetaBar L N ℓ) hfin) : Pic0 L (laurentBaseChange L (modularFunctio ...`

### 3. `Definitions/Def_ModularCurve_HeckeModule.lean`

*Imports:* `Definitions.Def_ModularCurve_HeckeOperatorTotal`, `Definitions.Def_HeckeGalois_EichlerShimura`  ·  16 decls (16 public, 0 private)

**Role.** Capstone layer: `heckeOperatorBar` (from `heckeOperatorAlong` at `AlgebraicClosure ℚ`), the predicate `HeckeOperatorsCommuteBar`, and the Hecke-algebra evaluation/`Module HeckeAlg (JZero N)` structure. The node `ModularCurve_heckeOperatorsCommuteBar` *is* this predicate. **Port dup.** None.

**`ModularCurve` / section `Operators`**
- **def** `heckeOperatorBar` — refs **use 3** — `def heckeOperatorBar (ℓ : Nat.Primes) : Module.End ℤ (JZero N) := haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩`
- **theorem** `heckeOperatorBar_apply` — refs **use 2** — `theorem heckeOperatorBar_apply (ℓ : Nat.Primes) (x : JZero N) : heckeOperatorBar N ℓ x = (haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩; heckeOperatorAlong (AlgebraicClosure ℚ) N ℓ x) :=`
- **def** `HeckeOperatorsCommuteBar` — refs **use 3** — `def HeckeOperatorsCommuteBar : Prop := ∀ ℓ ℓ' : Nat.Primes, heckeOperatorBar N ℓ * heckeOperatorBar N ℓ' = heckeOperatorBar N ℓ' * heckeOperatorBar N ℓ`
**`ModularCurve` / section `Eval`**
- **theorem** `isMulCommutative_adjoin_heckeOperatorBar` — refs **0** — `theorem isMulCommutative_adjoin_heckeOperatorBar (h : HeckeOperatorsCommuteBar N) : IsMulCommutative (Algebra.adjoin ℤ (Set.range (heckeOperatorBar N))) := Algebra.isMulCommutative_adjoin ℤ (by rintro _ ⟨ℓ, rfl⟩ _ ⟨ℓ', rfl⟩ exact h ℓ ℓ')`
- **def** `heckeEvalBarAux` — refs **0** — `def heckeEvalBarAux (h : HeckeOperatorsCommuteBar N) : HeckeAlg →ₐ[ℤ] (Algebra.adjoin ℤ (Set.range (heckeOperatorBar N)) : Subalgebra ℤ (Module.End ℤ (JZero N))) := haveI := isMulCommutative_adjoin_heckeOperatorBar h`
- **def** `heckeEvalBar` — refs **0** — `def heckeEvalBar (h : HeckeOperatorsCommuteBar N) : HeckeAlg →+* Module.End ℤ (JZero N) := ((Algebra.adjoin ℤ (Set.range (heckeOperatorBar N))).val.comp (heckeEvalBarAux h)).toRingHom`
- **theorem** `heckeEvalBar_apply` — refs **0** — `theorem heckeEvalBar_apply (h : HeckeOperatorsCommuteBar N) (t : HeckeAlg) : heckeEvalBar h t = (heckeEvalBarAux h t : Module.End ℤ (JZero N))`
- **theorem** `heckeEvalBarAux_heckeGen` — refs **0** — `theorem heckeEvalBarAux_heckeGen (h : HeckeOperatorsCommuteBar N) (ℓ : Nat.Primes) : heckeEvalBarAux h (heckeGen ℓ) = ⟨heckeOperatorBar N ℓ, Algebra.subset_adjoin (Set.mem_range_self ℓ)⟩ := haveI := isMulCommutative_adjoin_heckeOperatorBar h`
- **theorem** `heckeEvalBar_heckeGen` — refs **0** — `theorem heckeEvalBar_heckeGen (h : HeckeOperatorsCommuteBar N) (ℓ : Nat.Primes) : heckeEvalBar h (heckeGen ℓ) = heckeOperatorBar N ℓ`
- **theorem** `heckeEvalBar_C` — refs **0** — `theorem heckeEvalBar_C (h : HeckeOperatorsCommuteBar N) (a : ℤ) : heckeEvalBar h (MvPolynomial.C a) = (a : Module.End ℤ (JZero N))`
**`ModularCurve` / section `TheModule`**
- **def** `heckeModuleBar` — refs **0** — `def heckeModuleBar : Module HeckeAlg (JZero N) := if h : HeckeOperatorsCommuteBar N then Module.compHom (JZero N) (heckeEvalBar h) else Module.compHom (JZero N) (MvPolynomial.eval₂Hom (Int.castRingHom ℤ) (0 : Nat.Primes → ℤ))`
- **theorem** `heckeModuleBar_smul_def` — refs **0** — `theorem heckeModuleBar_smul_def (h : HeckeOperatorsCommuteBar N) (t : HeckeAlg) (x : JZero N) : (letI := heckeModuleBar N; t • x) = heckeEvalBar h t x`
- **theorem** `heckeModuleBar_heckeGen_smul` — refs **0** — `theorem heckeModuleBar_heckeGen_smul (h : HeckeOperatorsCommuteBar N) (ℓ : Nat.Primes) (x : JZero N) : (letI := heckeModuleBar N; heckeGen ℓ • x) = heckeOperatorBar N ℓ x`
- **theorem** `heckeModuleBar_smul_of_not` — refs **0** — `theorem heckeModuleBar_smul_of_not (h : ¬ HeckeOperatorsCommuteBar N) (t : HeckeAlg) (x : JZero N) : (letI := heckeModuleBar N; t • x) = MvPolynomial.constantCoeff t • x`
- **theorem** `heckeModuleBar_heckeGen_smul_of_not` — refs **0** — `theorem heckeModuleBar_heckeGen_smul_of_not (h : ¬ HeckeOperatorsCommuteBar N) (ℓ : Nat.Primes) (x : JZero N) : (letI := heckeModuleBar N; heckeGen ℓ • x) = 0`
- **theorem** `heckeModuleBar_C_smul` — refs **0** — `theorem heckeModuleBar_C_smul (a : ℤ) (x : JZero N) : (letI := heckeModuleBar N; (MvPolynomial.C a : HeckeAlg) • x) = a • x`

### 4. `Definitions/Def_ModularCurve_HeckeOperatorTotal.lean`

*Imports:* `Definitions.Def_ModularCurve_HeckeOperator`  ·  5 decls (5 public, 0 private)

**Role.** Total-function packaging: `HeckeInputsAlong` bundles `HeckeAlphaBarIntegral`, `HeckeBetaBarIntegral`, `HasPrincipalDivisors`, `FiniteAlong`, `FundamentalIdentityAlong`, `NormFormulaAlong`; `heckeOperatorAlong` is `heckePic0Bar` when these exist and `0` otherwise (making `heckeOperatorBar` definitional). **Port dup.** None.

**`ModularCurve`**
- **def** `HeckeInputsAlong` — refs **use 2** — `def HeckeInputsAlong : Prop := ∃ (_ : HeckeAlphaBarIntegral L N ℓ) (hβ : HeckeBetaBarIntegral L N ℓ) (_ : HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull (N * ℓ)))) (hfin : FiniteAlong L (heckeAlphaBar L N ...`
- **def** `heckeOperatorAlong` — refs **use 3** — `def heckeOperatorAlong : Pic0 L (laurentBaseChange L (modularFunctionFieldFull N)) →+ Pic0 L (laurentBaseChange L (modularFunctionFieldFull N)) := if h : HeckeInputsAlong L N ℓ then haveI := h.snd.snd.fst`
- **theorem** `heckeInputsAlong_intro` — refs **0** — `theorem heckeInputsAlong_intro (hα : HeckeAlphaBarIntegral L N ℓ) (hβ : HeckeBetaBarIntegral L N ℓ) [hP : HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull (N * ℓ)))] (hFI : FundamentalIdentityAlong L (heckeBetaBar L N ℓ) hβ) (hfin : FiniteAlong L (heckeAlphaBar L N ℓ)) (hN : NormFormulaAlong L (heckeAlphaBar L N ℓ) hfin) : HeckeInputsAlong L N ℓ := ⟨hα, hβ, hP, hfin, hFI, hN⟩`
- **theorem** `heckeOperatorAlong_eq` — refs **use 1** — `theorem heckeOperatorAlong_eq (hα : HeckeAlphaBarIntegral L N ℓ) (hβ : HeckeBetaBarIntegral L N ℓ) [HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull (N * ℓ)))] (hFI : FundamentalIdentityAlong L (heckeBetaBar L N ℓ) hβ) (hfin : FiniteAlong L (heckeAlphaBar L N ℓ)) (hN : NormFormulaAlong L (heckeAlphaBar L N ℓ) hfin) : heckeOperatorAlong L N ℓ = heckePic0Bar hα hβ hFI hfin hN`
- **theorem** `heckeOperatorAlong_of_not` — refs **use 2** — `theorem heckeOperatorAlong_of_not (h : ¬ HeckeInputsAlong L N ℓ) : heckeOperatorAlong L N ℓ = 0`

### 5. `Definitions/Def_ModularCurve_HeckeInputsAll.lean`

*Imports:* `Mathlib`, `Definitions.Def_ModularCurve_HeckeOperatorTotal`  ·  1 decls (1 public, 0 private)

**Role.** `HeckeInputsAll N` = `∀ ℓ : Nat.Primes, HeckeInputsAlong (AlgebraicClosure ℚ) N ℓ`. **Port dup.** None. Not named anywhere in the 82 node files (only reached through module 3/4 statements), so its necessity for the cone must be re-checked at port time.

**`ModularCurve`**
- **def** `HeckeInputsAll` — refs **0** — `def HeckeInputsAll (N : ℕ) [NeZero N] : Prop := ∀ ℓ : Nat.Primes, haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩`

### 6. `Definitions/Def_ModularCurve_ArithmeticGalois.lean`

*Imports:* `Definitions.Def_ModularCurve_X0`, `Definitions.Def_ModularCurve_LaurentCoeff`, `Definitions.Def_AlgebraicCurve_BaseChangeGalois`, `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`  ·  15 decls (15 public, 0 private)

**Role.** Arithmetic Galois action on the base-changed Laurent field (`arithmeticRingAut`, `arithmeticGalois`, `SMul`/`DistribMulAction` on `Pic0`), and the two abbreviations that are used everywhere downstream: `modularFunctionFieldBar N := laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)` and `JZero N := Pic0 (AlgebraicClosure ℚ) (modularFunctionFieldBar N)`. `JZero` itself is never written in the 82 files, but it occurs in the definitions of `heckeOperatorBar`/`HeckeOperatorsCommuteBar`. **Port dup.** None; the port's `Defs/Laurent.lean` has `laurentBaseChange` but no `Bar`/`JZero`.

**`ModularCurve` / section `ArithmeticGalois`**
- **def** `arithmeticRingAut` — refs **0** — `def arithmeticRingAut (σ : L ≃ₐ[ℚ] L) : (laurentBaseChange L F₀) ≃+* (laurentBaseChange L F₀)`
- **theorem** `coe_arithmeticRingAut_apply` — refs **0** — `theorem coe_arithmeticRingAut_apply (σ : L ≃ₐ[ℚ] L) (x : laurentBaseChange L F₀) : (arithmeticRingAut F₀ σ x : LaurentSeries L) = coeffMap (σ : L →+* L) (x : LaurentSeries L)`
- **theorem** `arithmeticRingAut_algebraMap` — refs **0** — `theorem arithmeticRingAut_algebraMap (σ : L ≃ₐ[ℚ] L) (a : L) : arithmeticRingAut F₀ σ (algebraMap L (laurentBaseChange L F₀) a) = algebraMap L (laurentBaseChange L F₀) (σ a) := Subtype.ext (coeffMap_algebraMap (σ : L →+* L) a)`
- **def** `arithmeticGalois` — refs **0** — `def arithmeticGalois : (L ≃ₐ[ℚ] L) →* SemilinearAut L (laurentBaseChange L F₀)`
- **theorem** `toRingAut_arithmeticGalois` — refs **0** — `theorem toRingAut_arithmeticGalois (σ : L ≃ₐ[ℚ] L) : SemilinearAut.toRingAut (arithmeticGalois F₀ σ) = arithmeticRingAut F₀ σ`
- **theorem** `baseAut_arithmeticGalois` — refs **0** — `theorem baseAut_arithmeticGalois (σ : L ≃ₐ[ℚ] L) : SemilinearAut.baseAut (arithmeticGalois F₀ σ) = σ.toRingEquiv`
- **theorem** `coe_arithmeticGalois_smul` — refs **0** — `theorem coe_arithmeticGalois_smul (σ : L ≃ₐ[ℚ] L) (x : laurentBaseChange L F₀) : ((arithmeticGalois F₀ σ • x : laurentBaseChange L F₀) : LaurentSeries L) = coeffMap (σ : L →+* L) (x : LaurentSeries L)`
**`ModularCurve` / section `PicAction`**
- **instance** `<anon-instance>` — refs **0** — `instance : SMul (L ≃ₐ[ℚ] L) (Pic0 L (laurentBaseChange L F₀))`
- **theorem** `galois_smul_pic0_def` — refs **0** — `theorem galois_smul_pic0_def (σ : L ≃ₐ[ℚ] L) (x : Pic0 L (laurentBaseChange L F₀)) : σ • x = arithmeticGalois F₀ σ • x`
- **instance** `<anon-instance>` — refs **0** — `instance : DistribMulAction (L ≃ₐ[ℚ] L) (Pic0 L (laurentBaseChange L F₀))`
**`ModularCurve` / section `ModularInstance`**
- **abbrev** `modularFunctionFieldBar` — refs **use 77** — `abbrev modularFunctionFieldBar : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) := laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)`
- **abbrev** `JZero` — refs **0** — `abbrev JZero : Type _ := Pic0 (AlgebraicClosure ℚ) (modularFunctionFieldBar N)`
- **def** `JZero.torsionGaloisRep` — refs **0** — `def JZero.torsionGaloisRep (n : ℕ) : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End (ZMod n) (Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) n) := (SemilinearAut.torsionRep _ _ n).comp (arithmeticGal ...`
- **theorem** `JZero.torsionGaloisRep_apply` — refs **0** — `theorem JZero.torsionGaloisRep_apply {n : ℕ} (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) n) : JZero.torsionGaloisRep N n σ x = arithmeticGalois (modularFunctionFieldFull N) σ • x`
- **theorem** `JZero.coe_torsionGaloisRep_apply` — refs **0** — `theorem JZero.coe_torsionGaloisRep_apply {n : ℕ} (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) n) : ((JZero.torsionGaloisRep N n σ x : Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) n) : JZero N) = σ • (x : JZero N)`

### 7. `Definitions/Def_ModularCurve_CuspidalClass.lean`

*Imports:* `Definitions.Def_ModularCurve_AtkinLehner`, `Definitions.Def_ModularCurve_GeometricBaseChange`  ·  11 decls (11 public, 0 private)

**Role.** The Fricke involution descended to the bar field (`frickeInvolutionBar = geomAut ... frickeInvolutionFull`), the cusp `cuspZeroBar := frickeInvolutionBar • cuspInftyBar`, the cuspidal divisor `cuspidalDivisor = [cuspZeroBar] - [cuspInftyBar]`, its degree-zero normalization `cuspidalDivisor₀`, and the class `cuspidalClass ∈ JZero N`. **Port dup.** None.

**`ModularCurve`**
- **def** `frickeInvolutionBar` — refs **use 8** — `def frickeInvolutionBar : modularFunctionFieldBar N ≃ₐ[AlgebraicClosure ℚ] modularFunctionFieldBar N := geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull N) (frickeInvolutionFull N)`
- **theorem** `frickeInvolutionBar_def` — refs **use 2** — `theorem frickeInvolutionBar_def : frickeInvolutionBar N = geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull N) (frickeInvolutionFull N)`
- **def** `cuspZeroBar` — refs **use 37** — `def cuspZeroBar : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := frickeInvolutionBar N • cuspInftyBar N`
- **theorem** `cuspZeroBar_def` — refs **use 2** — `theorem cuspZeroBar_def : cuspZeroBar N = frickeInvolutionBar N • cuspInftyBar N`
- **def** `cuspidalDivisor` — refs **use 2** — `def cuspidalDivisor : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := Finsupp.single (cuspZeroBar N) 1 - Finsupp.single (cuspInftyBar N) 1`
- **theorem** `cuspidalDivisor_def` — refs **use 1** — `theorem cuspidalDivisor_def : cuspidalDivisor N = Finsupp.single (cuspZeroBar N) 1 - Finsupp.single (cuspInftyBar N) 1`
- **theorem** `degree_cuspidalDivisor` — refs **0** — `theorem degree_cuspidalDivisor : Divisor.degree (cuspidalDivisor N) = 0`
- **def** `cuspidalDivisor₀` — refs **0** — `def cuspidalDivisor₀ : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N) :=`
- **theorem** `coe_cuspidalDivisor₀` — refs **use 2** — `theorem coe_cuspidalDivisor₀ : (cuspidalDivisor₀ N : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) = cuspidalDivisor N`
- **def** `cuspidalClass` — refs **use 2** — `def cuspidalClass : JZero N := Pic0.mk (cuspidalDivisor₀ N)`
- **theorem** `cuspidalClass_def` — refs **use 2** — `theorem cuspidalClass_def : cuspidalClass N = Pic0.mk (cuspidalDivisor₀ N)`

### 8. `Definitions/Def_ModularCurve_ModularUnit.lean`

*Imports:* `Definitions.Def_ModularCurve_X0`  ·  37 decls (37 public, 0 private)

**Role.** Modular-unit theory: predicate `IsMonicOfOrder` (order `m`, leading coeff `1`) with its closure lemmas, the ℚ-lift `dedekindEtaUnitQ` of the pin's `dedekindEtaUnit`, `deltaSeries = q · ofPowerSeries dedekindEtaUnitQ`, `deltaSeriesN = qExpand ℚ p deltaSeries`, and the unit `modularUnitSeries = deltaSeries * (deltaSeriesN)⁻¹`; plus `eisensteinNumerator p = (p-1)/gcd(p-1)12` and its `@[simp]` values. **Port dup.** `dedekindEtaUnit`, `jq`, `qExpand` and their API already live in the port (`ModularCurve/Defs/Jq.lean`, `Defs/Laurent.lean`); the `IsMonicOfOrder.*` lemmas are used only *inside* this pin module (qualified name count 0 in the 82 files) but are needed to state/justify `isMonicOfOrder_deltaSeries(N)`/`isMonicOfOrder_modularUnitSeries`, which are referenced. `eisensteinNumerator` has no port counterpart.

**`ModularCurve`**
- **def** `IsMonicOfOrder` — refs **0** — `def IsMonicOfOrder (f : LaurentSeries ℚ) (m : ℤ) : Prop := f.order = m ∧ f.leadingCoeff = 1`
**`ModularCurve.IsMonicOfOrder`**
- **theorem** `ne_zero` — refs **use 102** — `theorem ne_zero {f : LaurentSeries ℚ} {m : ℤ} (h : IsMonicOfOrder f m) : f ≠ 0 := HahnSeries.leadingCoeff_ne_zero.mp (by rw [h.2]; exact one_ne_zero)`
- **theorem** `coeff_self` — refs **use 8** — `theorem coeff_self {f : LaurentSeries ℚ} {m : ℤ} (h : IsMonicOfOrder f m) : f.coeff m = 1`
- **theorem** `coeff_of_lt` — refs **use 4** — `theorem coeff_of_lt {f : LaurentSeries ℚ} {m k : ℤ} (h : IsMonicOfOrder f m) (hk : k < m) : f.coeff k = 0 := HahnSeries.coeff_eq_zero_of_lt_order (h.1 ▸ hk)`
- **theorem** `single` — refs **use 23** — `theorem single (m : ℤ) : IsMonicOfOrder (HahnSeries.single m (1 : ℚ)) m`
- **theorem** `ofPowerSeries` — refs **use 1** — `theorem ofPowerSeries {U : PowerSeries ℚ} (hU : PowerSeries.constantCoeff U = 1) : IsMonicOfOrder (HahnSeries.ofPowerSeries ℤ ℚ U) 0`
- **theorem** `mul` — refs **use 24** — `theorem mul {f g : LaurentSeries ℚ} {m n : ℤ} (hf : IsMonicOfOrder f m) (hg : IsMonicOfOrder g n) : IsMonicOfOrder (f * g) (m + n)`
- **theorem** `of_mul_right` — refs **0** — `theorem of_mul_right {f g : LaurentSeries ℚ} {k n : ℤ} (hfg : IsMonicOfOrder (f * g) k) (hg : IsMonicOfOrder g n) : IsMonicOfOrder f (k - n)`
- **theorem** `qExpand` — refs **use 181** — `theorem qExpand {f : LaurentSeries ℚ} {m : ℤ} (p : ℕ) [NeZero p] (hf : IsMonicOfOrder f m) : IsMonicOfOrder (ModularCurve.qExpand ℚ p f) ((p : ℤ) * m)`
**`ModularCurve` / section `ModularUnit`**
- **def** `dedekindEtaUnitQ` — refs **use 4** — `def dedekindEtaUnitQ : PowerSeries ℚ := dedekindEtaUnit.map (Int.castRingHom ℚ)`
- **theorem** `constantCoeff_dedekindEtaUnitQ` — refs noise only (p2m 0 / attr 3) — `theorem constantCoeff_dedekindEtaUnitQ : PowerSeries.constantCoeff dedekindEtaUnitQ = 1`
- **def** `deltaSeries` — refs **use 44** — `def deltaSeries : LaurentSeries ℚ := HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ℚ dedekindEtaUnitQ`
- **theorem** `isMonicOfOrder_deltaSeries` — refs **use 8** — `theorem isMonicOfOrder_deltaSeries : IsMonicOfOrder deltaSeries 1`
- **theorem** `deltaSeries_ne_zero` — refs **use 2** — `theorem deltaSeries_ne_zero : deltaSeries ≠ 0 := isMonicOfOrder_deltaSeries.ne_zero`
- **def** `deltaSeriesN` — refs **use 40** — `def deltaSeriesN : LaurentSeries ℚ := qExpand ℚ p deltaSeries`
- **theorem** `isMonicOfOrder_deltaSeriesN` — refs **use 4** — `theorem isMonicOfOrder_deltaSeriesN : IsMonicOfOrder (deltaSeriesN p) (p : ℤ)`
- **theorem** `deltaSeriesN_ne_zero` — refs **0** — `theorem deltaSeriesN_ne_zero : deltaSeriesN p ≠ 0 := (isMonicOfOrder_deltaSeriesN p).ne_zero`
- **def** `modularUnitSeries` — refs **use 52** — `def modularUnitSeries : LaurentSeries ℚ := deltaSeries * (deltaSeriesN p)⁻¹`
- **theorem** `modularUnitSeries_mul_deltaSeriesN` — refs **use 2** — `theorem modularUnitSeries_mul_deltaSeriesN : modularUnitSeries p * deltaSeriesN p = deltaSeries`
- **theorem** `isMonicOfOrder_modularUnitSeries` — refs **0** — `theorem isMonicOfOrder_modularUnitSeries : IsMonicOfOrder (modularUnitSeries p) (1 - p)`
- **theorem** `modularUnitSeries_ne_zero` — refs **use 1** — `theorem modularUnitSeries_ne_zero : modularUnitSeries p ≠ 0 := (isMonicOfOrder_modularUnitSeries p).ne_zero`
- **theorem** `order_modularUnitSeries` — refs **use 1** — `theorem order_modularUnitSeries : (modularUnitSeries p).order = 1 - (p : ℤ) := (isMonicOfOrder_modularUnitSeries p).1`
- **theorem** `coeff_modularUnitSeries_self` — refs **0** — `theorem coeff_modularUnitSeries_self : (modularUnitSeries p).coeff (1 - (p : ℤ)) = 1 := (isMonicOfOrder_modularUnitSeries p).coeff_self`
- **theorem** `coeff_modularUnitSeries_of_lt` — refs **0** — `theorem coeff_modularUnitSeries_of_lt {k : ℤ} (hk : k < 1 - (p : ℤ)) : (modularUnitSeries p).coeff k = 0 := (isMonicOfOrder_modularUnitSeries p).coeff_of_lt hk`
- **theorem** `deltaSeriesN_one` — refs **0** — `theorem deltaSeriesN_one : deltaSeriesN 1 = deltaSeries := qExpand_one_apply deltaSeries`
- **theorem** `modularUnitSeries_one` — refs **use 1** — `theorem modularUnitSeries_one : modularUnitSeries 1 = 1`
- **theorem** `deltaSeriesN_mul` — refs **0** — `theorem deltaSeriesN_mul (a b : ℕ) [NeZero a] [NeZero b] [NeZero (a * b)] : deltaSeriesN (a * b) = qExpand ℚ a (deltaSeriesN b)`
- **theorem** `modularUnitSeries_mul` — refs **use 1** — `theorem modularUnitSeries_mul (a b : ℕ) [NeZero a] [NeZero b] [NeZero (a * b)] : modularUnitSeries (a * b) = modularUnitSeries a * qExpand ℚ a (modularUnitSeries b)`
**`ModularCurve`**
- **def** `eisensteinNumerator` — refs **0** — `def eisensteinNumerator (p : ℕ) : ℕ := (p - 1) / Nat.gcd (p - 1) 12`
- **theorem** `eisensteinNumerator_dvd` — refs **0** — `theorem eisensteinNumerator_dvd (p : ℕ) : eisensteinNumerator p ∣ p - 1 := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)`
- **theorem** `eisensteinNumerator_five` — refs noise only (p2m 0 / attr 3) — `@[simp] theorem eisensteinNumerator_five : eisensteinNumerator 5 = 1 := by decide`
- **theorem** `eisensteinNumerator_seven` — refs noise only (p2m 0 / attr 3) — `@[simp] theorem eisensteinNumerator_seven : eisensteinNumerator 7 = 1 := by decide`
- **theorem** `eisensteinNumerator_thirteen` — refs noise only (p2m 0 / attr 3) — `@[simp] theorem eisensteinNumerator_thirteen : eisensteinNumerator 13 = 1 := by decide`
- **theorem** `eisensteinNumerator_eleven` — refs noise only (p2m 0 / attr 3) — `@[simp] theorem eisensteinNumerator_eleven : eisensteinNumerator 11 = 5 := by decide`
- **theorem** `eisensteinNumerator_seventeen` — refs noise only (p2m 0 / attr 3) — `@[simp] theorem eisensteinNumerator_seventeen : eisensteinNumerator 17 = 4 := by decide`
- **theorem** `eisensteinNumerator_nineteen` — refs noise only (p2m 0 / attr 3) — `@[simp] theorem eisensteinNumerator_nineteen : eisensteinNumerator 19 = 3 := by decide`
- **theorem** `eisensteinNumerator_twentythree` — refs noise only (p2m 0 / attr 3) — `@[simp] theorem eisensteinNumerator_twentythree : eisensteinNumerator 23 = 11 := by decide`

### 9. `Definitions/Def_ModularCurve_AtkinLehner.lean`

*Imports:* `Definitions.Def_ModularCurve_QAdicPlace`, `Definitions.Def_ModularCurve_ArithmeticGalois`  ·  15 decls (15 public, 0 private)

**Role.** Fricke/Atkin–Lehner automorphisms: `IsFrickeAut`/`frickeInvolution` on `modularFunctionField N`; `IsFrickeAutFull`/`frickeInvolutionFull` on the full field; `cuspZero(Full)`; and the bar-level cusp `cuspInftyBar` (via `qInftyPlaceBar`), which is the single most-used declaration here (49 uses). **Port dup.** None. Note the non-full `IsFrickeAut`/`frickeInvolution` half is used by node `exists_isFrickeAut*`, while `cuspZero`/`cuspZeroFull`/`cuspInftyBar_toValuationSubring` are not named in the 82 files.

**`ModularCurve` / section `Fricke`**
- **def** `IsFrickeAut` — refs **use 4** — `def IsFrickeAut (σ : modularFunctionField N ≃ₐ[ℚ] modularFunctionField N) : Prop := σ ⟨jq, jq_mem N⟩ = ⟨jqN N, jqN_mem N⟩ ∧ σ ⟨jqN N, jqN_mem N⟩ = ⟨jq, jq_mem N⟩`
- **def** `frickeInvolution` — refs **0** — `def frickeInvolution : modularFunctionField N ≃ₐ[ℚ] modularFunctionField N := if h : ∃ σ : modularFunctionField N ≃ₐ[ℚ] modularFunctionField N, IsFrickeAut N σ then h.choose else AlgEquiv.refl`
- **theorem** `isFrickeAut_frickeInvolution` — refs **0** — `theorem isFrickeAut_frickeInvolution (h : ∃ σ : modularFunctionField N ≃ₐ[ℚ] modularFunctionField N, IsFrickeAut N σ) : IsFrickeAut N (frickeInvolution N)`
- **theorem** `frickeInvolution_eq_refl` — refs **0** — `theorem frickeInvolution_eq_refl (h : ¬ ∃ σ : modularFunctionField N ≃ₐ[ℚ] modularFunctionField N, IsFrickeAut N σ) : frickeInvolution N = AlgEquiv.refl`
- **def** `cuspZero` — refs **0** — `def cuspZero : Place ℚ (modularFunctionField N) := frickeInvolution N • cuspInfty N`
- **theorem** `cuspZero_def` — refs **0** — `theorem cuspZero_def : cuspZero N = frickeInvolution N • cuspInfty N`
**`ModularCurve` / section `Full`**
- **def** `IsFrickeAutFull` — refs **use 13** — `def IsFrickeAutFull (N : ℕ) [NeZero N] (σ : modularFunctionFieldFull N ≃ₐ[ℚ] modularFunctionFieldFull N) : Prop := ∀ (a b : ℕ) (hab : a * b = N) (_ : NeZero a) (_ : NeZero b), σ ⟨qExpand ℚ a jq, jqd_mem_full N (Dvd.intro b hab) ...`
- **def** `frickeInvolutionFull` — refs **use 16** — `def frickeInvolutionFull (N : ℕ) [NeZero N] : modularFunctionFieldFull N ≃ₐ[ℚ] modularFunctionFieldFull N := if h : ∃ σ : modularFunctionFieldFull N ≃ₐ[ℚ] modularFunctionFieldFull N, IsFrickeAutFull N σ then h.choose else AlgEq ...`
- **theorem** `isFrickeAutFull_frickeInvolutionFull` — refs **use 1** — `theorem isFrickeAutFull_frickeInvolutionFull (N : ℕ) [NeZero N] (h : ∃ σ : modularFunctionFieldFull N ≃ₐ[ℚ] modularFunctionFieldFull N, IsFrickeAutFull N σ) : IsFrickeAutFull N (frickeInvolutionFull N)`
- **theorem** `frickeInvolutionFull_eq_refl` — refs **0** — `theorem frickeInvolutionFull_eq_refl (N : ℕ) [NeZero N] (h : ¬ ∃ σ : modularFunctionFieldFull N ≃ₐ[ℚ] modularFunctionFieldFull N, IsFrickeAutFull N σ) : frickeInvolutionFull N = AlgEquiv.refl`
- **def** `cuspZeroFull` — refs **0** — `def cuspZeroFull : Place ℚ (modularFunctionFieldFull N) := frickeInvolutionFull N • cuspInftyFull N`
- **theorem** `cuspZeroFull_def` — refs **0** — `theorem cuspZeroFull_def : cuspZeroFull N = frickeInvolutionFull N • cuspInftyFull N`
**`ModularCurve` / section `Bar`**
- **theorem** `order_coeffEmb_jq` — refs **use 1** — `theorem order_coeffEmb_jq (L : Type*) [Field L] [Algebra ℚ L] : (coeffEmb L jq).order = -1`
- **def** `cuspInftyBar` — refs **use 49** — `def cuspInftyBar : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := qInftyPlaceBar (AlgebraicClosure ℚ) (modularFunctionFieldBar N) ⟨⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (L := AlgebraicClos ...`
- **theorem** `cuspInftyBar_toValuationSubring` — refs **0** — `theorem cuspInftyBar_toValuationSubring : (cuspInftyBar N).toValuationSubring = qIntegersBar (AlgebraicClosure ℚ) (modularFunctionFieldBar N)`

### 10. `Definitions/Def_ModularCurve_QAdicPlace.lean`

*Imports:* `Definitions.Def_ModularCurve_X0`, `Definitions.Def_AlgebraicCurve_DivisorClassGroup`  ·  49 decls (49 public, 0 private)

**Role.** q-adic valuation infrastructure at q=0: order arithmetic on `LaurentSeries L`, the coercion `qSeriesBar`, the valuation subring `qIntegersBar = {f | 0 ≤ ord f}` with `IsPrincipalIdealRing`, the place `qInftyPlaceBar`/rational twin `qInftyPlaceRat`, rational-level `cuspInfty`/`cuspInftyFull`, and the place-based cusp predicate `IsCusp j v := j ∉ v.toValuationSubring` with the q-expansion membership lemma `jq_mem_full`. **Port dup.** None. The `IsCusp` hits in the port (`ModularForms/HeckeCusps.lean` etc.) are Mathlib's unrelated `IsCusp c Γ` on `OnePoint ℝ` — a homonym, not duplication.

**`ModularCurve`**
- **theorem** `order_jq` — refs **use 1** — `theorem order_jq : jq.order = -1`
**`ModularCurve` / section `OrderArithBar`**
- **theorem** `order_mul_of_ne_zero_bar` — refs **0** — `theorem order_mul_of_ne_zero_bar {f g : LaurentSeries L} (hf : f ≠ 0) (hg : g ≠ 0) : (f * g).order = f.order + g.order := HahnSeries.order_mul_of_ne_zero (mul_ne_zero (HahnSeries.leadingCoeff_ne_zero.mpr hf) (HahnSeries.leadingCoeff_ne_zero.mpr hg))`
- **theorem** `order_inv_of_ne_zero_bar` — refs **0** — `theorem order_inv_of_ne_zero_bar {f : LaurentSeries L} (hf : f ≠ 0) : (f⁻¹).order = -f.order`
- **theorem** `order_pow_of_ne_zero_bar` — refs **0** — `theorem order_pow_of_ne_zero_bar {f : LaurentSeries L} (hf : f ≠ 0) (n : ℕ) : (f ^ n).order = n * f.order`
- **theorem** `order_zpow_of_ne_zero_bar` — refs **use 1** — `theorem order_zpow_of_ne_zero_bar {f : LaurentSeries L} (hf : f ≠ 0) (n : ℤ) : (f ^ n).order = n * f.order`
- **theorem** `order_div_of_ne_zero_bar` — refs **use 1** — `theorem order_div_of_ne_zero_bar {f g : LaurentSeries L} (hf : f ≠ 0) (hg : g ≠ 0) : (f / g).order = f.order - g.order`
**`ModularCurve` / section `QSeriesBar`**
- **def** `qSeriesBar` — refs **use 3** — `def qSeriesBar (f : F) : LaurentSeries L := (f : LaurentSeries L)`
- **theorem** `qSeriesBar_zero` — refs **use 1** — `@[simp] theorem qSeriesBar_zero : qSeriesBar L F 0 = 0`
- **theorem** `qSeriesBar_one` — refs noise only (p2m 0 / attr 2) — `@[simp] theorem qSeriesBar_one : qSeriesBar L F 1 = 1`
- **theorem** `qSeriesBar_mul` — refs noise only (p2m 0 / attr 2) — `@[simp] theorem qSeriesBar_mul (f g : F) : qSeriesBar L F (f * g) = qSeriesBar L F f * qSeriesBar L F g`
- **theorem** `qSeriesBar_add` — refs noise only (p2m 0 / attr 2) — `@[simp] theorem qSeriesBar_add (f g : F) : qSeriesBar L F (f + g) = qSeriesBar L F f + qSeriesBar L F g`
- **theorem** `qSeriesBar_neg` — refs noise only (p2m 0 / attr 2) — `@[simp] theorem qSeriesBar_neg (f : F) : qSeriesBar L F (-f) = -(qSeriesBar L F f)`
- **theorem** `qSeriesBar_sub` — refs noise only (p2m 0 / attr 2) — `@[simp] theorem qSeriesBar_sub (f g : F) : qSeriesBar L F (f - g) = qSeriesBar L F f - qSeriesBar L F g`
- **theorem** `qSeriesBar_inv` — refs noise only (p2m 0 / attr 2) — `@[simp] theorem qSeriesBar_inv (f : F) : qSeriesBar L F f⁻¹ = (qSeriesBar L F f)⁻¹`
- **theorem** `qSeriesBar_div` — refs **use 1** — `@[simp] theorem qSeriesBar_div (f g : F) : qSeriesBar L F (f / g) = qSeriesBar L F f / qSeriesBar L F g`
- **theorem** `qSeriesBar_pow` — refs noise only (p2m 0 / attr 2) — `@[simp] theorem qSeriesBar_pow (f : F) (n : ℕ) : qSeriesBar L F (f ^ n) = (qSeriesBar L F f) ^ n`
- **theorem** `qSeriesBar_zpow` — refs **use 1** — `theorem qSeriesBar_zpow (f : F) (n : ℤ) : qSeriesBar L F (f ^ n) = (qSeriesBar L F f) ^ n`
- **theorem** `qSeriesBar_eq_zero_iff` — refs noise only (p2m 0 / attr 2) — `@[simp] theorem qSeriesBar_eq_zero_iff {f : F} : qSeriesBar L F f = 0 ↔ f = 0 := ZeroMemClass.coe_eq_zero`
- **theorem** `qSeriesBar_ne_zero` — refs **use 3** — `theorem qSeriesBar_ne_zero {f : F} (hf : f ≠ 0) : qSeriesBar L F f ≠ 0 := fun h => hf (qSeriesBar_eq_zero_iff.mp h)`
- **theorem** `qSeriesBar_algebraMap` — refs **0** — `theorem qSeriesBar_algebraMap (c : L) : qSeriesBar L F (algebraMap L F c) = HahnSeries.single (0 : ℤ) c`
- **theorem** `order_qSeriesBar_mul` — refs **0** — `theorem order_qSeriesBar_mul {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) : (qSeriesBar L F (f * g)).order = (qSeriesBar L F f).order + (qSeriesBar L F g).order`
**`ModularCurve` / section `QAdicPlaceBar`**
- **def** `qIntegersBar` — refs **use 5** — `def qIntegersBar : ValuationSubring F`
- **theorem** `mem_qIntegersBar_iff` — refs **use 1** — `theorem mem_qIntegersBar_iff {f : F} : f ∈ qIntegersBar L F ↔ 0 ≤ (qSeriesBar L F f).order := Iff.rfl`
- **theorem** `isUnit_qIntegersBar_iff` — refs **use 1** — `theorem isUnit_qIntegersBar_iff {x : qIntegersBar L F} (hx : (x : F) ≠ 0) : IsUnit x ↔ (qSeriesBar L F (x : F)).order = 0`
**`ModularCurve` / section `QAdicPlaceBar.Witness`**
- **theorem** `ne_zero_of_order_eq_neg_one` — refs **use 1** — `theorem ne_zero_of_order_eq_neg_one : j ≠ 0`
- **theorem** `notMem_qIntegersBar_of_order_eq_neg_one` — refs **0** — `theorem notMem_qIntegersBar_of_order_eq_neg_one : j ∉ qIntegersBar L F`
- **theorem** `qIntegersBar_ne_top` — refs **0** — `theorem qIntegersBar_ne_top : qIntegersBar L F ≠ ⊤ := fun h =>`
- **theorem** `order_inv_of_order_eq_neg_one` — refs **use 1** — `theorem order_inv_of_order_eq_neg_one : (qSeriesBar L F j⁻¹).order = 1`
- **theorem** `inv_mem_qIntegersBar_of_order_eq_neg_one` — refs **0** — `theorem inv_mem_qIntegersBar_of_order_eq_neg_one : j⁻¹ ∈ qIntegersBar L F`
- **def** `uniformizerBar` — refs **use 1** — `def uniformizerBar : qIntegersBar L F := ⟨j⁻¹, inv_mem_qIntegersBar_of_order_eq_neg_one hj⟩`
- **theorem** `coe_uniformizerBar` — refs **use 1** — `theorem coe_uniformizerBar : ((uniformizerBar hj : qIntegersBar L F) : F) = j⁻¹`
- **theorem** `uniformizerBar_ne_zero` — refs **0** — `theorem uniformizerBar_ne_zero : ((uniformizerBar hj : qIntegersBar L F) : F) ≠ 0 := inv_ne_zero (ne_zero_of_order_eq_neg_one hj)`
- **theorem** `irreducible_uniformizerBar` — refs **use 1** — `theorem irreducible_uniformizerBar : Irreducible (uniformizerBar hj)`
- **theorem** `qIntegersBar_isPrincipalIdealRing` — refs **0** — `theorem qIntegersBar_isPrincipalIdealRing : IsPrincipalIdealRing (qIntegersBar L F)`
**`ModularCurve` / section `QAdicPlaceBar`**
- **def** `qInftyPlaceBar` — refs **use 2** — `def qInftyPlaceBar (h : ∃ j : F, (qSeriesBar L F j).order = -1) : Place L F`
- **theorem** `qInftyPlaceBar_toValuationSubring` — refs noise only (p2m 0 / attr 2) — `theorem qInftyPlaceBar_toValuationSubring (h : ∃ j : F, (qSeriesBar L F j).order = -1) : (qInftyPlaceBar L F h).toValuationSubring = qIntegersBar L F`
**`ModularCurve` / section `RationalTwin`**
- **def** `qInftyPlaceRat` — refs **0** — `def qInftyPlaceRat (h : ∃ j : F, (qSeriesBar ℚ F j).order = -1) : Place ℚ F`
- **theorem** `qInftyPlaceRat_toValuationSubring` — refs noise only (p2m 0 / attr 2) — `@[simp] theorem qInftyPlaceRat_toValuationSubring (h : ∃ j : F, (qSeriesBar ℚ F j).order = -1) : (qInftyPlaceRat F h).toValuationSubring = qIntegersBar ℚ F`
- **def** `cuspInfty` — refs **0** — `def cuspInfty : Place ℚ (modularFunctionField N) := qInftyPlaceRat _ ⟨⟨jq, jq_mem N⟩, order_jq⟩`
- **theorem** `cuspInfty_toValuationSubring` — refs noise only (p2m 0 / attr 2) — `@[simp] theorem cuspInfty_toValuationSubring : (cuspInfty N).toValuationSubring = qIntegersBar ℚ (modularFunctionField N)`
- **theorem** `jq_mem_full` — refs **use 18** — `theorem jq_mem_full : jq ∈ modularFunctionFieldFull N := modularFunctionField_le_full N (jq_mem N)`
- **def** `cuspInftyFull` — refs **0** — `def cuspInftyFull : Place ℚ (modularFunctionFieldFull N) := qInftyPlaceRat _ ⟨⟨jq, jq_mem_full N⟩, order_jq⟩`
- **theorem** `cuspInftyFull_toValuationSubring` — refs noise only (p2m 0 / attr 2) — `@[simp] theorem cuspInftyFull_toValuationSubring : (cuspInftyFull N).toValuationSubring = qIntegersBar ℚ (modularFunctionFieldFull N)`
**`ModularCurve` / section `IsCusp`**
- **def** `IsCusp` — refs **use 14** — `def IsCusp (j : E) (v : Place K E) : Prop := j ∉ v.toValuationSubring`
- **theorem** `isCusp_iff` — refs **use 3** — `theorem isCusp_iff (j : E) (v : Place K E) : IsCusp j v ↔ j ∉ v.toValuationSubring := Iff.rfl`
**`ModularCurve`**
- **theorem** `isCusp_qInftyPlaceBar` — refs **0** — `theorem isCusp_qInftyPlaceBar {F : IntermediateField L (LaurentSeries L)} (h : ∃ j : F, (qSeriesBar L F j).order = -1) {j : F} (hj : (qSeriesBar L F j).order = -1) : IsCusp j (qInftyPlaceBar L F h) := notMem_qIntegersBar_of_order_eq_neg_one hj`
- **theorem** `isCusp_qInftyPlaceRat` — refs **0** — `theorem isCusp_qInftyPlaceRat {F : IntermediateField ℚ (LaurentSeries ℚ)} (h : ∃ j : F, (qSeriesBar ℚ F j).order = -1) {j : F} (hj : (qSeriesBar ℚ F j).order = -1) : IsCusp j (qInftyPlaceRat F h) := notMem_qIntegersBar_of_order_eq_neg_one hj`
- **theorem** `isCusp_cuspInfty` — refs **0** — `theorem isCusp_cuspInfty (N : ℕ) [NeZero N] : IsCusp (⟨jq, jq_mem N⟩ : modularFunctionField N) (cuspInfty N) := notMem_qIntegersBar_of_order_eq_neg_one order_jq`
- **theorem** `isCusp_cuspInftyFull` — refs **0** — `theorem isCusp_cuspInftyFull (N : ℕ) [NeZero N] : IsCusp (⟨jq, jq_mem_full N⟩ : modularFunctionFieldFull N) (cuspInftyFull N) := notMem_qIntegersBar_of_order_eq_neg_one order_jq`

### 11. `Definitions/Def_ModularCurve_LaurentCoeff.lean`

*Imports:* `Mathlib.RingTheory.LaurentSeries`, `Mathlib.FieldTheory.IntermediateField.Adjoin.Basic`  ·  15 decls (15 public, 0 private)

**Role.** The coefficient/base-change layer of the Laurent-series model: `coeffMap` (coefficientwise ring hom), `coeffEmb = coeffMap (algebraMap ℚ L)`, and the intermediate field `laurentBaseChange L F₀ := adjoin L (coeffEmb L '' F₀)`, with membership/transport lemmas. **Port dup.** *Fully already ported* with identical names/namespace in `lean/FLTForHuman/ModularCurve/Defs/Laurent.lean`; the port file additionally makes `coeffMap_qExpand`/`coeffEmb_qExpand` public and adds `coeffMap_injective`/`coeffEmb_injective`. Nothing new needs writing here.

**`ModularCurve` / section `CoeffMap`**
- **def** `coeffMap` — refs **use 93** — `def coeffMap (f : R →+* S) : LaurentSeries R →+* LaurentSeries S`
- **theorem** `coeffMap_coeff` — refs **use 19** — `theorem coeffMap_coeff (f : R →+* S) (x : LaurentSeries R) (k : ℤ) : (coeffMap f x).coeff k = f (x.coeff k)`
- **theorem** `coeffMap_single` — refs **use 1** — `theorem coeffMap_single (f : R →+* S) (k : ℤ) (r : R) : coeffMap f (HahnSeries.single k r) = HahnSeries.single k (f r)`
- **theorem** `coeffMap_coeffMap` — refs **0** — `theorem coeffMap_coeffMap (g : S →+* T) (f : R →+* S) (x : LaurentSeries R) : coeffMap g (coeffMap f x) = coeffMap (g.comp f) x`
- **theorem** `coeffMap_id` — refs noise only (p2m 0 / attr 5) — `theorem coeffMap_id (x : LaurentSeries R) : coeffMap (RingHom.id R) x = x`
- **theorem** `coeffMap_congr` — refs **0** — `theorem coeffMap_congr {f g : R →+* S} (h : f = g) (x : LaurentSeries R) : coeffMap f x = coeffMap g x`
**`ModularCurve` / section `Constants`**
- **theorem** `algebraMap_laurentSeries_eq_single` — refs **use 8** — `theorem algebraMap_laurentSeries_eq_single (c : L) : algebraMap L (LaurentSeries L) c = HahnSeries.single 0 c`
- **theorem** `coeffMap_algebraMap` — refs **0** — `theorem coeffMap_algebraMap (φ : L →+* L) (c : L) : coeffMap φ (algebraMap L (LaurentSeries L) c) = algebraMap L (LaurentSeries L) (φ c)`
- **def** `coeffEmb` — refs **use 209** — `def coeffEmb : LaurentSeries ℚ →+* LaurentSeries L := coeffMap (algebraMap ℚ L)`
- **theorem** `coeffEmb_coeff` — refs **use 22** — `theorem coeffEmb_coeff (x : LaurentSeries ℚ) (k : ℤ) : (coeffEmb L x).coeff k = algebraMap ℚ L (x.coeff k)`
- **theorem** `coeffMap_coeffEmb` — refs **use 12** — `theorem coeffMap_coeffEmb (σ : L ≃ₐ[ℚ] L) (x : LaurentSeries ℚ) : coeffMap (σ : L →+* L) (coeffEmb L x) = coeffEmb L x`
**`ModularCurve` / section `BaseChange`**
- **def** `laurentBaseChange` — refs **use 132** — `def laurentBaseChange : IntermediateField L (LaurentSeries L) := IntermediateField.adjoin L (⇑(coeffEmb L) '' (F₀ : Set (LaurentSeries ℚ)))`
- **theorem** `coeffEmb_mem_laurentBaseChange` — refs **use 27** — `theorem coeffEmb_mem_laurentBaseChange {x : LaurentSeries ℚ} (hx : x ∈ F₀) : coeffEmb L x ∈ laurentBaseChange L F₀ := IntermediateField.subset_adjoin L _ ⟨x, hx, rfl⟩`
- **theorem** `mem_laurentBaseChange_iff` — refs **use 1** — `theorem mem_laurentBaseChange_iff {x : LaurentSeries L} : x ∈ laurentBaseChange L F₀ ↔ x ∈ Subfield.closure (Set.range (algebraMap L (LaurentSeries L)) ∪ (⇑(coeffEmb L) '' (F₀ : Set (LaurentSeries ℚ)))) := Iff.rfl`
- **theorem** `coeffMap_mem_laurentBaseChange` — refs **0** — `theorem coeffMap_mem_laurentBaseChange (σ : L ≃ₐ[ℚ] L) {x : LaurentSeries L} (hx : x ∈ laurentBaseChange L F₀) : coeffMap (σ : L →+* L) x ∈ laurentBaseChange L F₀`

### 12. `Definitions/Def_ModularCurve_JqCoeff.lean`

*Imports:* `Definitions.Def_ModularCurve_X0`  ·  11 decls (11 public, 0 private)

**Role.** General-`CommRing` j-invariant q-expansions: `jqModC K = q⁻¹ · jNum` and `jqNModC K N = qExpand K N (jqModC K)`, the intermediate field `modularFunctionFieldC K N = adjoin K {jqModC K, jqNModC K N}`, and membership/cast lemmas. **Port dup.** None by name; the port's `ModularCurve/Defs/Jq.lean` provides the ℚ-only `jq`/`jqN`, so `jqModC`/`jqNModC`/`modularFunctionFieldC` are new general-ring re-derivations (partial conceptual overlap with `Jq.lean`).

**`ModularCurve` / section `JExpansion`**
- **def** `jqModC` — refs **use 99** — `def jqModC : LaurentSeries K := HahnSeries.single (-1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ K (jNum.map (Int.castRingHom K))`
- **def** `jqNModC` — refs **use 125** — `def jqNModC (N : ℕ) [NeZero N] : LaurentSeries K := qExpand K N (jqModC K)`
- **theorem** `jqNModC_one` — refs **use 3** — `theorem jqNModC_one : jqNModC K 1 = jqModC K := qExpand_one_apply _`
- **theorem** `jqModC_rat` — refs **use 6** — `theorem jqModC_rat : jqModC ℚ = jq`
- **theorem** `map_jqModC` — refs **use 8** — `theorem map_jqModC {K' : Type*} [CommRing K'] (f : K →+* K') : (jqModC K).map f = jqModC K'`
- **theorem** `jqModC_eq_map_intCast` — refs **0** — `theorem jqModC_eq_map_intCast : jqModC K = (jqModC ℤ).map (Int.castRingHom K) := (map_jqModC (Int.castRingHom K)).symm`
**`ModularCurve` / section `FunctionField`**
- **def** `modularFunctionFieldC` — refs **use 3** — `def modularFunctionFieldC (N : ℕ) [NeZero N] : IntermediateField K (LaurentSeries K) := IntermediateField.adjoin K {jqModC K, jqNModC K N}`
- **theorem** `jqModC_mem` — refs **use 1** — `theorem jqModC_mem (N : ℕ) [NeZero N] : jqModC K ∈ modularFunctionFieldC K N := IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)`
- **theorem** `jqNModC_mem` — refs **use 1** — `theorem jqNModC_mem (N : ℕ) [NeZero N] : jqNModC K N ∈ modularFunctionFieldC K N := IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ rfl)`
- **theorem** `modularFunctionFieldC_rat` — refs **0** — `theorem modularFunctionFieldC_rat (N : ℕ) [NeZero N] : modularFunctionFieldC ℚ N = modularFunctionField N`
- **theorem** `modularFunctionFieldC_one` — refs **0** — `theorem modularFunctionFieldC_one : modularFunctionFieldC K 1 = IntermediateField.adjoin K {jqModC K}`

### 13. `Definitions/Def_ModularCurve_PhiGen.lean`

*Imports:* `Definitions.Def_ModularCurve_X0`, `Definitions.Def_ModularCurve_LaurentCoeff`, `Mathlib.Algebra.Polynomial.BigOperators`  ·  50 decls (50 public, 0 private)

**Role.** The modular-polynomial generation layer: the q-twist operators `qTwistFun`/`qTwist` (multiply the `k`-th coefficient by `u^k`), `cosetSubst` (twist + `qExpand (a*a)`), `evalAtJqN`/`evalAtJ`, `EvalSymm`, the pole/coefficient predicates `PoleOrderLE`, `TPoleOrderLE`, `JSimplePole`, `IntCoeffs`, `ModularPolynomialFamily`, `PhiIrreducible`, the adjoin ring `adjoinJq`/`jAdj`/`evalAtJAdj`, the bivariate swap `swapInner`/`swapBivar`, and `PhiGen.cosetA/B`, `PhiGen.conj`, `phiProd`, `PhiGenDescends`. **Port dup.** *Essentially fully already ported*: `ModularCurve/Defs/Twist.lean` has all of `QTwist` (plus `qTwistEquiv`, `qTwist_iota_of_pow_eq_one`), and `ModularCurve/Defs/PhiGen.lean` has `cosetSubst`, `EvalAtJqN` (`evalAtJqN(_X/_def/_one)`, `evalAtJ_def`), `EvalSymm`/`aeval_toRingHom_X`, `PoleOrderLE`, `ModularPolynomialFamily`, `PhiIrreducible`, `adjoinJq`/`jAdj`/`evalAtJAdj`, `swapInner`/`swapBivar`/`swapBivar_X`/`swapBivar_C_X`, `PhiGen.cosetA/B`(+lemmas+`instNeZeroPhiGenCosetA`), `cosetSubst_congr`, `conj`(+`conj_zero`/`conj_succ`), `phiProd`(+`_monic`/`_natDegree`/`_ne_zero`/`_eval_conj`), `TPoleOrderLE`(+extra), `JSimplePole`, `IntCoeffs`, `PhiGenDescends`. The port then adds far more (TS, PhiAtSlot, descent/integrality/pole-bound/splitting files).

**`ModularCurve` / section `QTwist`**
- **def** `qTwistFun` — refs **0** — `def qTwistFun (u : Rˣ) (f : LaurentSeries R) : LaurentSeries R`
- **theorem** `qTwistFun_coeff` — refs noise only (p2m 0 / attr 17) — `theorem qTwistFun_coeff (u : Rˣ) (f : LaurentSeries R) (k : ℤ) : (qTwistFun u f).coeff k = (u ^ k : Rˣ) * f.coeff k`
- **theorem** `support_qTwistFun` — refs **0** — `theorem support_qTwistFun (u : Rˣ) (f : LaurentSeries R) : (qTwistFun u f).support = f.support`
- **def** `qTwist` — refs **use 124** — `def qTwist (u : Rˣ) : LaurentSeries R →+* LaurentSeries R`
- **theorem** `qTwist_coeff` — refs **use 15** — `theorem qTwist_coeff (u : Rˣ) (f : LaurentSeries R) (k : ℤ) : (qTwist u f).coeff k = (u ^ k : Rˣ) * f.coeff k`
- **theorem** `support_qTwist` — refs **0** — `theorem support_qTwist (u : Rˣ) (f : LaurentSeries R) : (qTwist u f).support = f.support := support_qTwistFun u f`
- **theorem** `qTwist_single` — refs noise only (p2m 0 / attr 17) — `theorem qTwist_single (u : Rˣ) (k : ℤ) (r : R) : qTwist u (HahnSeries.single k r) = HahnSeries.single k ((u ^ k : Rˣ) * r)`
- **theorem** `qTwist_one_apply` — refs **use 31** — `theorem qTwist_one_apply (f : LaurentSeries R) : qTwist (1 : Rˣ) f = f`
- **theorem** `qTwist_qTwist` — refs **use 20** — `theorem qTwist_qTwist (u v : Rˣ) (f : LaurentSeries R) : qTwist u (qTwist v f) = qTwist (u * v) f`
- **theorem** `qTwist_injective` — refs **0** — `theorem qTwist_injective (u : Rˣ) : Function.Injective (qTwist u)`
- **theorem** `qTwist_qExpand` — refs **use 16** — `theorem qTwist_qExpand (v : Rˣ) (N : ℕ) [NeZero N] (f : LaurentSeries R) : qTwist v (qExpand R N f) = qExpand R N (qTwist (v ^ (N : ℤ)) f)`
**`ModularCurve` / section `CosetSubst`**
- **def** `cosetSubst` — refs **0** — `def cosetSubst (ζ : Kˣ) (a b : ℕ) [NeZero a] : LaurentSeries K →+* LaurentSeries K := haveI : NeZero (a * a) := ⟨Nat.mul_ne_zero (NeZero.ne a) (NeZero.ne a)⟩`
**`ModularCurve` / section `EvalAtJqN`**
- **def** `evalAtJqN` — refs **use 3** — `def evalAtJqN : Polynomial ℤ →+* LaurentSeries ℚ := (Polynomial.aeval (R := ℤ) (jqN N)).toRingHom`
- **theorem** `evalAtJqN_X` — refs **use 1** — `theorem evalAtJqN_X : evalAtJqN N Polynomial.X = jqN N`
- **theorem** `evalAtJqN_def` — refs **use 1** — `theorem evalAtJqN_def : evalAtJqN N = (Polynomial.aeval (R := ℤ) (jqN N)).toRingHom`
- **theorem** `evalAtJ_def` — refs **0** — `theorem evalAtJ_def : evalAtJ = (Polynomial.aeval (R := ℤ) jq).toRingHom`
- **theorem** `evalAtJqN_one` — refs **0** — `theorem evalAtJqN_one : evalAtJqN 1 = evalAtJ`
**`ModularCurve` / section `Symmetry`**
- **def** `EvalSymm` — refs **use 24** — `def EvalSymm (Φ : Polynomial (Polynomial ℤ)) : Prop := ∀ x y : LaurentSeries ℚ, Φ.eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y`
- **theorem** `aeval_toRingHom_X` — refs noise only (p2m 0 / attr 17) — `theorem aeval_toRingHom_X (x : LaurentSeries ℚ) : (Polynomial.aeval (R := ℤ) x).toRingHom Polynomial.X = x`
**`ModularCurve`**
- **def** `PoleOrderLE` — refs **0** — `def PoleOrderLE (f : LaurentSeries ℚ) (n : ℕ) : Prop := ∀ k : ℤ, k < -(n : ℤ) → f.coeff k = 0`
- **def** `ModularPolynomialFamily` — refs **use 7** — `def ModularPolynomialFamily : Prop := ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ∃ data : ModularPolynomialData ℓ, EvalSymm data.Φ`
**`ModularCurve` / section `Named`**
- **def** `PhiIrreducible` — refs **use 15** — `def PhiIrreducible (data : ModularPolynomialData N) : Prop := Irreducible data.toAdjoin`
**`ModularCurve` / section `AdjoinRing`**
- **abbrev** `adjoinJq` — refs **0** — `abbrev adjoinJq : Subalgebra ℚ (LaurentSeries ℚ) := Algebra.adjoin ℚ {jq}`
- **def** `jAdj` — refs **0** — `def jAdj : adjoinJq := ⟨jq, Algebra.self_mem_adjoin_singleton ℚ jq⟩`
- **def** `evalAtJAdj` — refs **0** — `def evalAtJAdj : Polynomial ℤ →+* adjoinJq := Polynomial.eval₂RingHom (Int.castRingHom adjoinJq) jAdj`
**`ModularCurve` / section `SwapBivar`**
- **def** `swapInner` — refs **0** — `def swapInner : Polynomial ℤ →+* Polynomial (Polynomial ℤ) := (Polynomial.aeval (R := ℤ) (Polynomial.X : Polynomial (Polynomial ℤ))).toRingHom`
- **def** `swapBivar` — refs **0** — `def swapBivar : Polynomial (Polynomial ℤ) →+* Polynomial (Polynomial ℤ) := Polynomial.eval₂RingHom swapInner (Polynomial.C Polynomial.X)`
- **theorem** `swapBivar_X` — refs noise only (p2m 0 / attr 17) — `theorem swapBivar_X : swapBivar Polynomial.X = Polynomial.C Polynomial.X := Polynomial.eval₂_X _ _`
- **theorem** `swapBivar_C_X` — refs noise only (p2m 0 / attr 17) — `theorem swapBivar_C_X : swapBivar (Polynomial.C Polynomial.X) = Polynomial.X`
**`ModularCurve.PhiGen` / section `CosetIndex`**
- **def** `cosetA` — refs **0** — `def cosetA (i : Fin (ℓ + 1)) : ℕ := if i = 0 then ℓ else 1`
- **def** `cosetB` — refs **0** — `def cosetB (i : Fin (ℓ + 1)) : ℕ := if i = 0 then 0 else (i : ℕ) - 1`
- **theorem** `cosetA_zero` — refs noise only (p2m 0 / attr 17) — `theorem cosetA_zero : cosetA ℓ (0 : Fin (ℓ + 1)) = ℓ := if_pos rfl`
- **theorem** `cosetB_zero` — refs noise only (p2m 0 / attr 17) — `theorem cosetB_zero : cosetB ℓ (0 : Fin (ℓ + 1)) = 0 := if_pos rfl`
- **theorem** `cosetA_succ` — refs noise only (p2m 0 / attr 17) — `theorem cosetA_succ (b : Fin ℓ) : cosetA ℓ b.succ = 1 := if_neg (Fin.succ_ne_zero b)`
- **theorem** `cosetB_succ` — refs noise only (p2m 0 / attr 17) — `theorem cosetB_succ (b : Fin ℓ) : cosetB ℓ b.succ = (b : ℕ)`
- **instance** `instNeZeroPhiGenCosetA` — refs noise only (p2m 0 / attr 17) — `instance instNeZeroPhiGenCosetA [hℓ : Fact (Nat.Prime ℓ)] (i : Fin (ℓ + 1)) : NeZero (cosetA ℓ i) := ⟨by unfold cosetA; split <;> simp [hℓ.out.ne_zero]⟩`
**`ModularCurve.PhiGen` / section `ConjugateFamily`**
- **theorem** `cosetSubst_congr` — refs **0** — `theorem cosetSubst_congr (ζ : Kˣ) {a a' b b' : ℕ} [NeZero a] [NeZero a'] (ha : a = a') (hb : b = b') (f : LaurentSeries K) : cosetSubst ζ a b f = cosetSubst ζ a' b' f`
- **def** `conj` — refs **use 39** [ns-qual 27] — `def conj (i : Fin (ℓ + 1)) : LaurentSeries K := cosetSubst ζ (cosetA ℓ i) (cosetB ℓ i) (coeffEmb K jq)`
- **theorem** `conj_zero` — refs **use 15** [ns-qual 12] — `theorem conj_zero : conj ℓ ζ (0 : Fin (ℓ + 1)) = qExpand K (ℓ * ℓ) (coeffEmb K jq)`
- **theorem** `conj_succ` — refs **use 12** [ns-qual 9] — `theorem conj_succ (b : Fin ℓ) : conj ℓ ζ b.succ = qTwist (ζ ^ (b : ℕ)) (coeffEmb K jq)`
**`ModularCurve.PhiGen` / section `Product`**
- **def** `phiProd` — refs **use 9** — `def phiProd (conj : Fin (ℓ + 1) → LaurentSeries K) : Polynomial (LaurentSeries K) := ∏ i : Fin (ℓ + 1), (Polynomial.X - Polynomial.C (conj i))`
- **theorem** `phiProd_monic` — refs **0** — `theorem phiProd_monic (conj : Fin (ℓ + 1) → LaurentSeries K) : (phiProd ℓ conj).Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (conj i)`
- **theorem** `phiProd_natDegree` — refs **0** — `theorem phiProd_natDegree (conj : Fin (ℓ + 1) → LaurentSeries K) : (phiProd ℓ conj).natDegree = ℓ + 1`
- **theorem** `phiProd_ne_zero` — refs **0** — `theorem phiProd_ne_zero (conj : Fin (ℓ + 1) → LaurentSeries K) : phiProd ℓ conj ≠ 0 := (phiProd_monic ℓ conj).ne_zero`
- **theorem** `phiProd_eval_conj` — refs **0** — `theorem phiProd_eval_conj (conj : Fin (ℓ + 1) → LaurentSeries K) (i : Fin (ℓ + 1)) : (phiProd ℓ conj).eval (conj i) = 0`
**`ModularCurve.PhiGen` / section `PoleDefs`**
- **def** `TPoleOrderLE` — refs **0** — `def TPoleOrderLE (f : LaurentSeries K) (n : ℕ) : Prop := ∀ m : ℤ, m < -(n : ℤ) → f.coeff m = 0`
- **theorem** `tPoleOrderLE_iff_poleOrderLE` — refs **0** — `theorem tPoleOrderLE_iff_poleOrderLE (f : LaurentSeries ℚ) (n : ℕ) : TPoleOrderLE f n ↔ PoleOrderLE f n := Iff.rfl`
- **def** `JSimplePole` — refs **0** — `def JSimplePole : Prop := ∀ m : ℤ, m < -1 → J.coeff m = 0`
**`ModularCurve.PhiGen`**
- **def** `IntCoeffs` — refs **use 2** [ns-qual 2] — `def IntCoeffs (f : LaurentSeries ℚ) : Prop := ∀ m : ℤ, ∃ z : ℤ, f.coeff m = (z : ℚ)`
**`ModularCurve.PhiGen` / section `Descends`**
- **def** `PhiGenDescends` — refs **0** — `def PhiGenDescends (c : ℕ → LaurentSeries ℚ) : Prop := ∀ k : ℕ, (phiProd ℓ (conj ℓ ζ)).coeff k = coeffEmb K (qExpand ℚ ℓ (c k))`
## Appendix

### (d) Public declarations with 0 real-code references, per module

- **1 DegeneracyTower**: `towerInclBar_eq_inclusion`, `heckeBetaBar_eq_towerSubstBar`, `towerInclBar_comp_heckeBetaBar`, `towerSubstBar_comp_heckeAlphaBar`
- **2 HeckeOperator**: `coe_heckeAlphaBar`, `heckeBetaBarRingHom`, `coe_heckeBetaBarRingHom`, `heckeAlphaBar_eq_inclusion`, `heckePic0Bar`, `heckeDivBarTranspose`, `heckePic0BarTranspose`
- **3 HeckeModule**: `isMulCommutative_adjoin_heckeOperatorBar`, `heckeEvalBarAux`, `heckeEvalBar`, `heckeEvalBar_apply`, `heckeEvalBarAux_heckeGen`, `heckeEvalBar_heckeGen`, `heckeEvalBar_C`, `heckeModuleBar`, `heckeModuleBar_smul_def`, `heckeModuleBar_heckeGen_smul`, `heckeModuleBar_smul_of_not`, `heckeModuleBar_heckeGen_smul_of_not`, `heckeModuleBar_C_smul`
- **4 HeckeOperatorTotal**: `heckeInputsAlong_intro`
- **5 HeckeInputsAll**: `HeckeInputsAll`
- **6 ArithmeticGalois**: `arithmeticRingAut`, `coe_arithmeticRingAut_apply`, `arithmeticRingAut_algebraMap`, `arithmeticGalois`, `toRingAut_arithmeticGalois`, `baseAut_arithmeticGalois`, `coe_arithmeticGalois_smul`, `<anon-instance>`, `galois_smul_pic0_def`, `<anon-instance>`, `JZero`, `JZero.torsionGaloisRep`, `JZero.torsionGaloisRep_apply`, `JZero.coe_torsionGaloisRep_apply`
- **7 CuspidalClass**: `degree_cuspidalDivisor`, `cuspidalDivisor₀`
- **8 ModularUnit**: `IsMonicOfOrder`, `of_mul_right`, `deltaSeriesN_ne_zero`, `isMonicOfOrder_modularUnitSeries`, `coeff_modularUnitSeries_self`, `coeff_modularUnitSeries_of_lt`, `deltaSeriesN_one`, `deltaSeriesN_mul`, `eisensteinNumerator`, `eisensteinNumerator_dvd`
  - *noise-only* (appear only in `attribute [-simp]`/`p2m_*`): `constantCoeff_dedekindEtaUnitQ`, `eisensteinNumerator_five`, `eisensteinNumerator_seven`, `eisensteinNumerator_thirteen`, `eisensteinNumerator_eleven`, `eisensteinNumerator_seventeen`, `eisensteinNumerator_nineteen`, `eisensteinNumerator_twentythree`
- **9 AtkinLehner**: `frickeInvolution`, `isFrickeAut_frickeInvolution`, `frickeInvolution_eq_refl`, `cuspZero`, `cuspZero_def`, `frickeInvolutionFull_eq_refl`, `cuspZeroFull`, `cuspZeroFull_def`, `cuspInftyBar_toValuationSubring`
- **10 QAdicPlace**: `order_mul_of_ne_zero_bar`, `order_inv_of_ne_zero_bar`, `order_pow_of_ne_zero_bar`, `qSeriesBar_algebraMap`, `order_qSeriesBar_mul`, `notMem_qIntegersBar_of_order_eq_neg_one`, `qIntegersBar_ne_top`, `inv_mem_qIntegersBar_of_order_eq_neg_one`, `uniformizerBar_ne_zero`, `qIntegersBar_isPrincipalIdealRing`, `qInftyPlaceRat`, `cuspInfty`, `cuspInftyFull`, `isCusp_qInftyPlaceBar`, `isCusp_qInftyPlaceRat`, `isCusp_cuspInfty`, `isCusp_cuspInftyFull`
  - *noise-only* (appear only in `attribute [-simp]`/`p2m_*`): `qSeriesBar_one`, `qSeriesBar_mul`, `qSeriesBar_add`, `qSeriesBar_neg`, `qSeriesBar_sub`, `qSeriesBar_inv`, `qSeriesBar_pow`, `qSeriesBar_eq_zero_iff`, `qInftyPlaceBar_toValuationSubring`, `qInftyPlaceRat_toValuationSubring`, `cuspInfty_toValuationSubring`, `cuspInftyFull_toValuationSubring`
- **11 LaurentCoeff**: `coeffMap_coeffMap`, `coeffMap_congr`, `coeffMap_algebraMap`, `coeffMap_mem_laurentBaseChange`
  - *noise-only* (appear only in `attribute [-simp]`/`p2m_*`): `coeffMap_id`
- **12 JqCoeff**: `jqModC_eq_map_intCast`, `modularFunctionFieldC_rat`, `modularFunctionFieldC_one`
- **13 PhiGen**: `qTwistFun`, `support_qTwistFun`, `support_qTwist`, `qTwist_injective`, `cosetSubst`, `evalAtJ_def`, `evalAtJqN_one`, `PoleOrderLE`, `adjoinJq`, `jAdj`, `evalAtJAdj`, `swapInner`, `swapBivar`, `cosetA`, `cosetB`, `cosetSubst_congr`, `phiProd_monic`, `phiProd_natDegree`, `phiProd_ne_zero`, `phiProd_eval_conj`, `TPoleOrderLE`, `tPoleOrderLE_iff_poleOrderLE`, `JSimplePole`, `PhiGenDescends`
  - *noise-only* (appear only in `attribute [-simp]`/`p2m_*`): `qTwistFun_coeff`, `qTwist_single`, `aeval_toRingHom_X`, `swapBivar_X`, `swapBivar_C_X`, `cosetA_zero`, `cosetB_zero`, `cosetA_succ`, `cosetB_succ`, `instNeZeroPhiGenCosetA`

### (e) Public declarations with ≥1 real-code reference, per module

- **1 DegeneracyTower**: towerInclBar(28), coe_towerInclBar(3), towerInclBar_comp_towerInclBar(5), towerInclBar_self(3), towerSubstBar(29), coe_towerSubstBar(2), towerSubstBar_congr(1), heckeAlphaBar_eq_towerInclBar(2), towerInclBar_comp_heckeAlphaBar(2), towerSubstBar_comp_heckeBetaBar(3), heckeSquareBar_commutes(1), dvd_of_eq_roof(36), HeckeExchangeAt(6)
- **2 HeckeOperator**: heckeAlphaBar(25), heckeBetaBar(25), coe_heckeBetaBar(2), HeckeAlphaBarIntegral(4), HeckeBetaBarIntegral(4), heckeDivBar(3)
- **3 HeckeModule**: heckeOperatorBar(3), heckeOperatorBar_apply(2), HeckeOperatorsCommuteBar(3)
- **4 HeckeOperatorTotal**: HeckeInputsAlong(2), heckeOperatorAlong(3), heckeOperatorAlong_eq(1), heckeOperatorAlong_of_not(2)
- **6 ArithmeticGalois**: modularFunctionFieldBar(77)
- **7 CuspidalClass**: frickeInvolutionBar(8), frickeInvolutionBar_def(2), cuspZeroBar(37), cuspZeroBar_def(2), cuspidalDivisor(2), cuspidalDivisor_def(1), coe_cuspidalDivisor₀(2), cuspidalClass(2), cuspidalClass_def(2)
- **8 ModularUnit**: †`ne_zero`(102), †`coeff_self`(8), †`coeff_of_lt`(4), †`single`(23), †`ofPowerSeries`(1), †`mul`(24), †`qExpand`(181), dedekindEtaUnitQ(4), deltaSeries(44), isMonicOfOrder_deltaSeries(8), deltaSeries_ne_zero(2), deltaSeriesN(40), isMonicOfOrder_deltaSeriesN(4), modularUnitSeries(52), modularUnitSeries_mul_deltaSeriesN(2), modularUnitSeries_ne_zero(1), order_modularUnitSeries(1), modularUnitSeries_one(1), modularUnitSeries_mul(1)
- **9 AtkinLehner**: IsFrickeAut(4), IsFrickeAutFull(13), frickeInvolutionFull(16), isFrickeAutFull_frickeInvolutionFull(1), order_coeffEmb_jq(1), cuspInftyBar(49)
- **10 QAdicPlace**: order_jq(1), order_zpow_of_ne_zero_bar(1), order_div_of_ne_zero_bar(1), qSeriesBar(3), qSeriesBar_zero(1), qSeriesBar_div(1), qSeriesBar_zpow(1), qSeriesBar_ne_zero(3), qIntegersBar(5), mem_qIntegersBar_iff(1), isUnit_qIntegersBar_iff(1), ne_zero_of_order_eq_neg_one(1), order_inv_of_order_eq_neg_one(1), uniformizerBar(1), coe_uniformizerBar(1), irreducible_uniformizerBar(1), qInftyPlaceBar(2), jq_mem_full(18), IsCusp(14), isCusp_iff(3)
- **11 LaurentCoeff**: coeffMap(93), coeffMap_coeff(19), coeffMap_single(1), algebraMap_laurentSeries_eq_single(8), coeffEmb(209), coeffEmb_coeff(22), coeffMap_coeffEmb(12), laurentBaseChange(132), coeffEmb_mem_laurentBaseChange(27), mem_laurentBaseChange_iff(1)
- **12 JqCoeff**: jqModC(99), jqNModC(125), jqNModC_one(3), jqModC_rat(6), map_jqModC(8), modularFunctionFieldC(3), jqModC_mem(1), jqNModC_mem(1)
- **13 PhiGen**: qTwist(124), qTwist_coeff(15), qTwist_one_apply(31), qTwist_qTwist(20), qTwist_qExpand(16), evalAtJqN(3), evalAtJqN_X(1), evalAtJqN_def(1), EvalSymm(24), ModularPolynomialFamily(7), PhiIrreducible(15), conj(39), conj_zero(15), conj_succ(12), phiProd(9), IntCoeffs(2)

---

## CORRECTIONS (manager, verified by grep 2026-09-23)

- **`laurentBaseChange_mono` is NOT ported.** `grep -rn 'laurentBaseChange_mono' lean/FLTForHuman` returns 0 hits (the only related ported facts are the *specialized* `Defs/Fields.lean` lemmas `full_degeneracy_le` and `full_degeneracy_map_le`). The report's takeaway 3 is wrong on this point: the pin's `laurentBaseChange_mono'` and `laurentBaseChange_mono''` must be **written once** (promote to `Defs/Laurent.lean` beside `laurentBaseChange`, or keep `private` in one module and import). `qExpand_mem_laurentBaseChange'` is likewise not ported. The two `coeffMap_qExpand'` / `coeffEmb_qExpand'` **are** ported public (`Defs/Laurent.lean`: `coeffMap_qExpand`, `coeffEmb_qExpand`).
- **The three M8 Fricke/inclusion `S_` files share a 651-content-line prelude** (lines 50–861 / 50–861 / 53–863); the first two differ by 12 lines total (all `p2m_*` + the final `solution`). This is SET-M2's headline dedup; the port writes the prelude once. The pin's `RealL` block (lines 262–417) is **already ported** as `ModularForms/Hauptmodul.lean:230`'s `RealL` + closure. Relevant to m4, not SET-M1.
