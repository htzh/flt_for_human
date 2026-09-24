/-
  Consumer for the Sturm-bound port.

  Four zones, each a real instantiation:

  * **A `[qexp]`** — the coefficient reindexing and the product of `q`-expansions;
  * **B `[periods]`** — the arithmetic-period input;
  * **C `[levelone]`** — the level-one vanishing;
  * **D `[sturm]`** — the two headline Sturm bounds, applied at `Γ₀(2)` and `𝒮ℒ`;
  * **E `[coeffsturm]`** — the coefficient-form bounds and the norm-free wire test:
    FLT's own `qCoeffTrunc` + `FiniteDimensional.of_injective` argument re-run on
    `CuspForm.Gamma0_eq_zero_of_qExpansion_coeff_eq_zero`, with no `CuspForm.norm`
    and no `normCofactor`.
-/
import FLTForHuman.ModularForms.SturmBound

set_option autoImplicit false

noncomputable section

open UpperHalfPlane ModularForm SlashInvariantForm Matrix.SpecialLinearGroup ConjAct
open scoped MatrixGroups ModularForm Topology Manifold Pointwise

/-! ## Zone A — `[qexp]` the `q`-expansion order lemmas -/

#check @UpperHalfPlane.qExpansion_coeff_nat_mul
#check @UpperHalfPlane.qExpansion_prod

/-- The period-`2` coefficient reindexing for a `Γ₀(2)` form, through the
`one_mem_strictPeriods_Gamma0` leaf. -/
example {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 2) k) (n : ℕ) :
    (qExpansion (2 * 1) f).coeff n = if 2 ∣ n then (qExpansion 1 f).coeff (n / 2) else 0 :=
  UpperHalfPlane.qExpansion_coeff_nat_mul one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex f
      (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 2))
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) (by norm_num) n

/-- The empty product case of `qExpansion_prod`, exercised at `h = 1`. -/
example : qExpansion (1 : ℝ) (∏ _i ∈ (∅ : Finset ℕ), (1 : ℍ → ℂ)) = 1 := by
  rw [UpperHalfPlane.qExpansion_prod]
  · simp
  · intro i hi
    exact absurd hi (Finset.notMem_empty i)

/-! ## Zone B — `[periods]` the arithmetic-period input -/

#check @Subgroup.IsArithmetic.exists_nat_mem_strictPeriods_conj

/-- At level one, some positive `M` is a strict period of every `SL(2, ℤ)`
conjugate of `𝒮ℒ`. -/
example : ∃ M : ℕ, 0 < M ∧ ∀ γ : SL(2, ℤ),
    (M : ℝ) ∈ (ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ γ) • 𝒮ℒ).strictPeriods :=
  Subgroup.IsArithmetic.exists_nat_mem_strictPeriods_conj 𝒮ℒ

/-! ## Zone C — `[levelone]` the level-one vanishing -/

#check @ModularForm.levelOne_eq_zero_of_lt_order_qExpansion

example {k : ℤ} (F : ModularForm 𝒮ℒ k)
    (h : ((1 * (k.toNat / 12) : ℕ) : ℕ∞) < (qExpansion (1 : ℝ) F).order) : F = 0 :=
  ModularForm.levelOne_eq_zero_of_lt_order_qExpansion 1 (by norm_num) F (by simpa using h)

/-! ## Zone D — `[sturm]` the two headlines -/

#check @ModularForm.sturm_bound_of_isArithmetic
#check @ModularForm.sturm_bound_Gamma0

/-- The headline at `Γ₀(2)`, weight `2`: the bound is `2 * 3 / 12 = 0`. -/
example (f : ModularForm (CongruenceSubgroup.Gamma0 2) 2)
    (h : ∀ n : ℕ, n ≤ ((2 : ℤ) * (CongruenceSubgroup.Gamma0 2).index).toNat / 12 →
      (qExpansion 1 f).coeff n = 0) : f = 0 :=
  ModularForm.sturm_bound_Gamma0 2 f h

/-- The general headline at `𝒮ℒ`, weight `12`: the bound is `12 * 1 / 12 = 1`. -/
example (f : ModularForm 𝒮ℒ 12)
    (h : (↑(((12 : ℤ) * (𝒮ℒ).relIndex 𝒮ℒ).toNat / 12) : ℕ∞) < (qExpansion 1 f).order) : f = 0 :=
  ModularForm.sturm_bound_of_isArithmetic one_mem_strictPeriods_SL h

/-! ## Zone E — `[coeffsturm]` the coefficient-form bounds and the norm-free
finiteness wire test

FLT proves `CuspForm.eq_zero_of_qExpansion_coeff_eq_zero` through
`CuspForm.norm` and its ~300-line norm block; the port derives it from
`sturm_bound_of_isArithmetic`. The wire test below re-runs FLT's own
`qCoeffTrunc` + `FiniteDimensional.of_injective` argument on the ported bound,
so the norm is not needed anywhere in the finite-dimensionality proof. -/

#check @CuspForm.eq_zero_of_qExpansion_coeff_eq_zero
#check @CuspForm.Gamma0_eq_zero_of_qExpansion_coeff_eq_zero

/-- The coefficient-truncation linear map of FLT's `qCoeffTrunc`. -/
private def qCoeffTrunc (N : ℕ) [NeZero N] (k : ℤ) (d : ℕ) :
    CuspForm (CongruenceSubgroup.Gamma0 N) k →ₗ[ℂ] (Fin d → ℂ) where
  toFun f := fun i => (qExpansion 1 ⇑f).coeff i
  map_add' f g := by
    have hf := ModularFormClass.analyticAt_cuspFunction_zero f one_pos
      (by rw [CongruenceSubgroup.strictPeriods_Gamma0]; exact AddSubgroup.mem_zmultiples 1)
    have hg := ModularFormClass.analyticAt_cuspFunction_zero g one_pos
      (by rw [CongruenceSubgroup.strictPeriods_Gamma0]; exact AddSubgroup.mem_zmultiples 1)
    funext i
    simp only [FunLike.coe_add, Pi.add_apply, qExpansion_add hf hg, map_add]
  map_smul' c f := by
    have hf := ModularFormClass.analyticAt_cuspFunction_zero f one_pos
      (by rw [CongruenceSubgroup.strictPeriods_Gamma0]; exact AddSubgroup.mem_zmultiples 1)
    funext i
    have hcoe : ⇑(c • f) = c • ⇑f := rfl
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    rw [hcoe, UpperHalfPlane.qExpansion_smul hf c, map_smul, smul_eq_mul]

/-- **The norm-free finiteness.** `CuspForm (Γ₀ N) k` embeds into `Fin d → ℂ`
with `d = k.toNat · [𝒮ℒ : Γ₀ N] + 1`; the kernel is zero by the coefficient-form
Sturm bound, so FLT's `normCofactor` prelude and `CuspForm.norm` drop out of
`CuspForm.finiteDimensional_cuspForm`. -/
example (N : ℕ) [NeZero N] (k : ℤ) :
    FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k) := by
  classical
  set c : ℕ := Nat.card (𝒮ℒ ⧸ ((CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)) with hc
  set d : ℕ := k.toNat * c + 1 with hd_def
  have hd : k * (c : ℤ) < 12 * (d : ℤ) := by
    have h1 : k * (c : ℤ) ≤ (k.toNat : ℤ) * c :=
      mul_le_mul_of_nonneg_right (Int.self_le_toNat k) (Int.natCast_nonneg c)
    have h2 : (0 : ℤ) ≤ (k.toNat : ℤ) * c := by positivity
    have h3 : (12 : ℤ) * (d : ℤ) = 12 * ((k.toNat : ℤ) * c) + 12 := by
      rw [hd_def]; push_cast; ring
    linarith
  refine FiniteDimensional.of_injective (qCoeffTrunc N k d) ?_
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  refine CuspForm.Gamma0_eq_zero_of_qExpansion_coeff_eq_zero f d (by rw [← hc]; exact hd) ?_
  intro m hm
  have hfm := congrFun hf ⟨m, hm⟩
  simpa [qCoeffTrunc] using hfm

end
