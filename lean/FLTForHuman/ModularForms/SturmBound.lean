/-
  The **Sturm bound** for arithmetic level, and its three inputs.

  A modular form is determined by its `q`-expansion up to the Sturm bound: here,
  if the `q`-expansion vanishes below `k · [SL(2, ℤ) : Γ] / 12`, the form is
  zero. FLT needs the general arithmetic-level form:

  * `Subgroup.IsArithmetic.exists_nat_mem_strictPeriods_conj` — for an arithmetic
    `𝒢`, some `M > 0` is a strict period of every `SL(2, ℤ)`-conjugate of `𝒢`
    (the normal core's index);
  * `ModularForm.levelOne_eq_zero_of_lt_order_qExpansion` — the level-one case,
    a corollary of mathlib's `ModularForm.sturm_bound_levelOne`;
  * `ModularForm.eq_zero_of_lt_order_qExpansion_of_isArithmetic` — the general
    case, by dividing the norm of `f` (mathlib's `ModularForm.norm`) by the
    level-one vanishing, with `UpperHalfPlane.qExpansion_prod` for the order;
  * `ModularForm.sturm_bound_of_isArithmetic` and
    `ModularForm.sturm_bound_Gamma0` — the headlines, the second specialising the
    first to `Γ₀(N)` through `(Γ₀ N).index = relIndex` in `GL(2, ℝ)`.

  FLT provenance, pinned `aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_sturm_bound_of_isArithmetic.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_sturm_bound_Gamma0.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_eq_zero_of_lt_order_qExpansion_of_isArithmetic.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_levelOne_eq_zero_of_lt_order_qExpansion.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_Subgroup_IsArithmetic_exists_nat_mem_strictPeriods_conj.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_CongruenceSubgroup_one_mem_strictPeriods_Gamma0.lean

  The pin's `S_ModularForm_levelOne_eq_zero_of_lt_order_qExpansion.lean` carries a
  second private copy of `qExpansion_coeff_nat_mul` (54 lines); the port imports
  the single copy from `QExpansionOrder.lean`. `HeckeEigenform.lean` had a
  `private` `CuspForm.one_mem_strictPeriods_Gamma0` (a one-line twin of the leaf
  below); the public leaf here is the wrapper target.

  The final section carries the weight-`2` **cusp-form vanishing corollaries**
  (`S2_Gamma0_2_eq_zero`, `S2_Gamma0_one_eq_zero`): for weight `2` the bound is
  `⌊2 · index / 12⌋ = ⌊index / 6⌋`, which is `0` at `Γ(1)` and `Γ₀(2)`, and a
  cusp form has vanishing constant term, so the bound applies immediately. The
  older norm-route proof of the same two theorems is kept in the `Reserve`
  library (`Reserve.ModularForms.LevelTwoCuspVanishing`).
-/
import FLTForHuman.ModularForms.QExpansionOrder
import FLTForHuman.ModularForms.Gamma0TwoIndex
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.Cusps

set_option autoImplicit false

-- The pin's `haveI` walls are load-bearing; keep them literal.
set_option linter.style.haveILetI false

noncomputable section

open UpperHalfPlane ModularForm SlashInvariantForm Matrix.SpecialLinearGroup ConjAct
open scoped MatrixGroups ModularForm Topology Manifold Pointwise CongruenceSubgroup

/-- `(1 : ℝ)` is a strict period of `Γ₀(N)`: `Γ₀(N)` contains `T`. -/
theorem CongruenceSubgroup.one_mem_strictPeriods_Gamma0 (N : ℕ) :
    (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ)
      (CongruenceSubgroup.Gamma0 N)).strictPeriods := by
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem]
    simp [ModularGroup.T]
  have h := Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT
  rw [h]
  exact AddSubgroup.mem_zmultiples (1 : ℝ)

/-- For an arithmetic `𝒢`, a single positive `M` is a strict period of every
`SL(2, ℤ)`-conjugate of `𝒢` — the index of the normal core of `𝒢.comap mapGL`. -/
theorem Subgroup.IsArithmetic.exists_nat_mem_strictPeriods_conj (𝒢 : Subgroup (GL (Fin 2) ℝ))
    [𝒢.IsArithmetic] : ∃ M : ℕ, 0 < M ∧ ∀ γ : SL(2, ℤ),
      (M : ℝ) ∈ (ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ γ) • 𝒢).strictPeriods := by
  haveI : (𝒢.comap (mapGL (R := ℤ) ℝ)).FiniteIndex := Subgroup.IsArithmetic.finiteIndex_comap 𝒢
  set Λ : Subgroup SL(2, ℤ) := (𝒢.comap (mapGL (R := ℤ) ℝ)).normalCore with hΛ
  haveI : Λ.FiniteIndex := inferInstance
  haveI hN : Λ.Normal := inferInstance
  refine ⟨Λ.index, Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero, fun γ ↦ ?_⟩
  have hT : ModularGroup.T ^ Λ.index ∈ Λ := Λ.pow_index_mem ModularGroup.T
  have hconj : γ⁻¹ * ModularGroup.T ^ Λ.index * γ ∈ 𝒢.comap (mapGL ℝ) := by
    apply Subgroup.normalCore_le
    simpa using hN.conj_mem _ hT γ⁻¹
  have hU : ∀ m : ℤ, Matrix.GeneralLinearGroup.upperRightHom ((m : ℝ)) =
      mapGL ℝ (ModularGroup.T ^ m) := by
    intro m
    simp only [Units.ext_iff, mapGL_coe_matrix, map_apply_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ModularGroup.coe_T_zpow]
  have hU' := hU Λ.index
  rw [zpow_natCast, Int.cast_natCast] at hU'
  rw [Subgroup.mem_strictPeriods_iff, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← toConjAct_inv,
    toConjAct_smul, inv_inv, hU', ← map_inv, ← map_mul, ← map_mul]
  exact hconj

namespace Subgroup

/-- The relative index of `Γ ≤ SL(2, ℤ)` inside `GL(2, ℝ)` is its index in
`SL(2, ℤ)`; the bridge `sturm_bound_Gamma0` needs for the `𝒮ℒ`-normalised
Sturm bound. -/
private lemma relIndex_map_mapGL_W2D (Γ : Subgroup SL(2, ℤ)) :
    (Γ : Subgroup (GL (Fin 2) ℝ)).relIndex 𝒮ℒ = Γ.index := by
  rw [← Subgroup.index_comap, Subgroup.comap_map_eq_self_of_injective mapGL_injective]

end Subgroup

namespace ModularForm

/-- **Level-one vanishing from the `q`-order.** If the order of the period-`M`
`q`-expansion is beyond the Sturm bound `M · (k / 12)`, the level-one form is
zero. A corollary of mathlib's `ModularForm.sturm_bound_levelOne` through the
coefficient reindexing `qExpansion_coeff_nat_mul`. -/
theorem levelOne_eq_zero_of_lt_order_qExpansion (M : ℕ) (hM : 0 < M) {k : ℤ}
    (F : ModularForm 𝒮ℒ k) (h : ((M * (k.toNat / 12) : ℕ) : ℕ∞) < (qExpansion (M : ℝ) F).order) :
    F = 0 := by
  by_contra hF
  have hq1 : qExpansion 1 F ≠ 0 := by
    rwa [Ne, ModularForm.qExpansion_eq_zero_iff one_pos one_mem_strictPeriods_SL]
  have hord : (qExpansion 1 F).order ≠ ⊤ := by
    rwa [Ne, PowerSeries.order_eq_top]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hord
  have hle : n ≤ k.toNat / 12 := by
    refine le_of_not_gt fun hlt ↦ hF (ModularForm.sturm_bound_levelOne ?_)
    rw [← hn]
    exact_mod_cast hlt
  have hcoeff : (qExpansion 1 F).coeff n ≠ 0 := by
    have := PowerSeries.coeff_order hq1
    rwa [← hn, ENat.toNat_natCast] at this
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex F one_mem_strictPeriods_SL
  have : Fact (IsCusp OnePoint.infty 𝒮ℒ) := ⟨(𝒮ℒ).isCusp_of_mem_strictPeriods one_pos
    one_mem_strictPeriods_SL⟩
  have hM' := qExpansion_coeff_nat_mul one_pos hper (ModularFormClass.holo F)
    (ModularFormClass.bdd_at_infty F) hM (M * n)
  rw [mul_one, ite_eq_left (dvd_mul_right M n), Nat.mul_div_cancel_left _ hM] at hM'
  have hordM : (qExpansion (M : ℝ) F).order ≤ (M * n : ℕ) :=
    PowerSeries.order_le _ (by rwa [hM'])
  have : ((M * n : ℕ) : ℕ∞) ≤ (M * (k.toNat / 12) : ℕ) := by
    exact_mod_cast Nat.mul_le_mul_left M hle
  exact absurd (h.trans_le (hordM.trans this)) (lt_irrefl _)

/-- Each translate of `f` by an `SL(2, ℤ)`-conjugate has an analytic cusp
function at `0` — the input `qExpansion_prod` needs for the norm. -/
private theorem analyticAt_cuspFunction_quotientFunc_W2D {𝒢 : Subgroup (GL (Fin 2) ℝ)}
    {k : ℤ} (f : ModularForm 𝒢 k) {M : ℕ} (hM : 0 < M)
    (hconj : ∀ γ : SL(2, ℤ), (M : ℝ) ∈ (toConjAct (mapGL ℝ γ) • 𝒢).strictPeriods)
    (q : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) :
    AnalyticAt ℂ (cuspFunction M (quotientFunc f q)) 0 := by
  induction q using Quotient.inductionOn with
  | h r =>
    obtain ⟨γ, hγ⟩ := r.2
    have hp : (M : ℝ) ∈ (toConjAct (r.1⁻¹)⁻¹ • 𝒢).strictPeriods := by
      rw [inv_inv, ← hγ]
      exact hconj γ
    exact ModularFormClass.analyticAt_cuspFunction_zero (ModularForm.translate f r.1⁻¹)
      (Nat.cast_pos.mpr hM) hp

/-- **General-level vanishing from the `q`-order.** For an arithmetic `𝒢`, if the
period-`M` expansion of `f` vanishes beyond `M · (k · [𝒮ℒ : 𝒢] / 12)`, then `f`
is zero. The norm `ModularForm.norm 𝒮ℒ f` is a level-one form whose order is at
most that of `f`, so the level-one bound applies and `norm_eq_zero_iff` reads the
conclusion back. -/
theorem eq_zero_of_lt_order_qExpansion_of_isArithmetic {𝒢 : Subgroup (GL (Fin 2) ℝ)}
    [𝒢.IsArithmetic] {k : ℤ} (f : ModularForm 𝒢 k) {M : ℕ} (hM : 0 < M)
    (hconj : ∀ γ : SL(2, ℤ), (M : ℝ) ∈
      (ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ γ) • 𝒢).strictPeriods)
    (h : ((M * ((k * 𝒢.relIndex 𝒮ℒ).toNat / 12) : ℕ) : ℕ∞) < (qExpansion M f).order) :
    f = 0 := by
  set F := ModularForm.norm 𝒮ℒ f with hF
  have hanalytic := f.analyticAt_cuspFunction_quotientFunc_W2D hM hconj
  let _ : Fintype (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) := Fintype.ofFinite _
  have hprod : qExpansion M F = ∏ q : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ, qExpansion M (quotientFunc f q) := by
    rw [hF, ModularForm.coe_norm]
    exact UpperHalfPlane.qExpansion_prod Finset.univ fun q _ ↦ hanalytic q
  have hone : quotientFunc f (⟦1⟧ : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) = ⇑f := by
    rw [quotientFunc_mk]
    simp
  have horder : (qExpansion M f).order ≤ (qExpansion M F).order := by
    rw [hprod, PowerSeries.order_prod, ← hone]
    exact Finset.single_le_sum (f := fun q ↦ (qExpansion M (quotientFunc f q)).order)
      (fun _ _ ↦ zero_le) (Finset.mem_univ _)
  have hrel : 𝒢.relIndex 𝒮ℒ = Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) := rfl
  have hF0 : F = 0 := by
    refine ModularForm.levelOne_eq_zero_of_lt_order_qExpansion M hM F (lt_of_lt_of_le ?_ horder)
    simpa [hrel] using h
  rw [hF, ModularForm.norm_eq_zero_iff] at hF0
  exact DFunLike.coe_injective (by simpa using hF0)

/-- **The Sturm bound for an arithmetic subgroup.** If the `q`-expansion of `f`
vanishes up to `k · [𝒮ℒ : 𝒢] / 12`, then `f = 0`. -/
theorem sturm_bound_of_isArithmetic {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic] {k : ℤ}
    {f : ModularForm 𝒢 k} (h1 : (1 : ℝ) ∈ 𝒢.strictPeriods)
    (h : (↑((k * 𝒢.relIndex 𝒮ℒ).toNat / 12) : ℕ∞) < (qExpansion 1 f).order) : f = 0 := by
  obtain ⟨M, hM, hconj⟩ := Subgroup.IsArithmetic.exists_nat_mem_strictPeriods_conj 𝒢
  haveI : Fact (IsCusp OnePoint.infty 𝒢) := ⟨𝒢.isCusp_of_mem_strictPeriods one_pos h1⟩
  refine f.eq_zero_of_lt_order_qExpansion_of_isArithmetic hM hconj ?_
  refine lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self _) (PowerSeries.nat_le_order _ _ fun n hn ↦ ?_)
  have := qExpansion_coeff_nat_mul one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex f h1) (ModularFormClass.holo f)
    (ModularFormClass.bdd_at_infty f) hM n
  rw [mul_one] at this
  rw [this]
  split_ifs with hd
  · apply PowerSeries.coeff_of_lt_order
    refine lt_of_le_of_lt ?_ h
    exact_mod_cast Nat.div_le_of_le_mul (by lia)
  · rfl

/-- **The Sturm bound for `Γ₀(N)`.** The `𝒮ℒ`-relative index is `(Γ₀ N).index`,
and `Γ₀(N)` contains `T`, so `1` is a strict period. -/
theorem sturm_bound_Gamma0 (N : ℕ) [NeZero N] {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    (h : ∀ n : ℕ, n ≤ (k * (CongruenceSubgroup.Gamma0 N).index).toNat / 12 →
      (qExpansion 1 f).coeff n = 0) : f = 0 := by
  have h1 : (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simp [CongruenceSubgroup.strictPeriods_Gamma0]
  refine ModularForm.sturm_bound_of_isArithmetic h1 ?_
  rw [Subgroup.relIndex_map_mapGL_W2D]
  refine lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self _)
    (PowerSeries.nat_le_order _ _ fun n hn ↦ ?_)
  exact h n (by lia)

/-! ## Weight-2 cusp-form vanishing (corollaries)

For weight `2` the Sturm bound is `⌊2 · index / 12⌋ = ⌊index / 6⌋`, which is `0`
at `Γ(1)` (index 1) and `Γ₀(2)` (index 3). A cusp form has vanishing constant
term, so the bound applies with no other input: the only coefficient to check
below the bound is the constant term. -/

section CuspFormVanishing

/-- `Γ(1)` is `𝒮ℒ`, the image of `SL(2, ℤ)` in `GL(2, ℝ)`; the bridge between
mathlib's level-one statements and FLT's congruence-subgroup spelling. -/
lemma coe_Gamma_one_eq_SL : (↑Γ(1) : Subgroup (GL (Fin 2) ℝ)) = 𝒮ℒ := by
  rw [CongruenceSubgroup.Gamma_one_top]
  ext x
  simp [Subgroup.mem_map, MonoidHom.mem_range]

/-- Transport a vanishing statement across an equality of level subgroups. -/
lemma cuspForm_eq_zero_of_subgroup_eq {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)} (h : Γ₂ = Γ₁)
    {k : ℤ} (H : ∀ g : CuspForm Γ₂ k, g = 0) (f : CuspForm Γ₁ k) : f = 0 := by
  subst h; exact H f

private lemma Gamma0_one_eq_top :
    (CongruenceSubgroup.Gamma0 1 : Subgroup SL(2, ℤ)) = ⊤ := by
  ext A
  simp [CongruenceSubgroup.Gamma0_mem, eq_iff_true_of_subsingleton]

private lemma coe_Gamma0_one_eq_SL :
    ((CongruenceSubgroup.Gamma0 1 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) = 𝒮ℒ := by
  rw [Gamma0_one_eq_top, ← CongruenceSubgroup.Gamma_one_top]
  exact coe_Gamma_one_eq_SL

/-- **Level one.** `S₂(SL(2, ℤ)) = 0`: the weight-`2` Sturm bound is
`⌊2 / 12⌋ = 0`, and a cusp form has vanishing constant term. -/
theorem S2_Gamma0_one_eq_zero (f : CuspForm (CongruenceSubgroup.Gamma0 1) 2) : f = 0 :=
  cuspForm_eq_zero_of_subgroup_eq coe_Gamma0_one_eq_SL.symm
    (fun g => CuspForm.toModularFormₗ_injective (by
      simpa using sturm_bound_levelOne (f := CuspForm.toModularFormₗ g) (by
        have h1 : (1 : ℕ∞) ≤ (qExpansion 1 ⇑g).order :=
          PowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr (by
            simpa [PowerSeries.coeff_zero_eq_constantCoeff] using
              CuspFormClass.qExpansion_coeff_zero g one_pos one_mem_strictPeriods_SL)
        change (↑((2 : ℤ).toNat / 12) : ℕ∞) < (qExpansion 1 ⇑g).order
        norm_num
        exact lt_of_lt_of_le (by norm_num : (0 : ℕ∞) < 1) h1))) f

/-- **Level two.** `S₂(Γ₀(2)) = 0`: the weight-`2` Sturm bound is
`⌊2 · 3 / 12⌋ = 0`, and a cusp form has vanishing constant term. -/
theorem S2_Gamma0_2_eq_zero (f : CuspForm (CongruenceSubgroup.Gamma0 2) 2) : f = 0 := by
  have hB : (((2 : ℤ) * (CongruenceSubgroup.Gamma0 2).index).toNat / 12) = 0 := by
    rw [Gamma0_two_index_eq_three]; norm_num
  have hM : CuspForm.toModularFormₗ (Γ := CongruenceSubgroup.Gamma0 2) (k := 2) f = 0 := by
    refine sturm_bound_Gamma0 2 _ (fun n hn => ?_)
    rw [hB] at hn
    have hn0 : n = 0 := by omega
    subst hn0
    change (qExpansion 1 ⇑f).coeff 0 = 0
    exact CuspFormClass.qExpansion_coeff_zero f one_pos
      (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 2)
  exact CuspForm.toModularFormₗ_injective (by simpa using hM)

end CuspFormVanishing

end ModularForm

end
