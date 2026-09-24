/-
  Consumer for the Sturm-bound port.

  Four zones, each a real instantiation:

  * **A `[qexp]`** — the coefficient reindexing and the product of `q`-expansions;
  * **B `[periods]`** — the arithmetic-period input;
  * **C `[levelone]`** — the level-one vanishing;
  * **D `[sturm]`** — the two headline Sturm bounds, applied at `Γ₀(2)` and `𝒮ℒ`;
  * **E `[coeffsturm]`** — the coefficient-form bounds and the finite-dimensionality
    corollary: FLT's `qCoeffTrunc` + `FiniteDimensional.of_injective` argument is
    a library corollary in `SturmBound.lean` (no `CuspForm.norm`, no
    `normCofactor`), and the consumer applies it at arbitrary `N`, `k`.
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

/-! ## Zone E — `[coeffsturm]` the coefficient-form bounds and the
finite-dimensionality corollary

FLT proves `CuspForm.eq_zero_of_qExpansion_coeff_eq_zero` through `CuspForm.norm`
and its ~300-line norm block; the port derives it from
`sturm_bound_of_isArithmetic`. The same bound drives `qCoeffTrunc` +
`FiniteDimensional.of_injective`, giving FLT's `finiteDimensional_cuspForm` — an
endgame corollary (closure 1, 4 consumers, all inside `fermatLastTheorem`). The
wire test consumes the library corollary rather than re-proving it. -/

#check @CuspForm.eq_zero_of_qExpansion_coeff_eq_zero
#check @CuspForm.Gamma0_eq_zero_of_qExpansion_coeff_eq_zero
#check @CuspForm.qCoeffTrunc
#check @CuspForm.finiteDimensional_cuspForm

/-- The consumed corollary, at level `N` and arbitrary weight. -/
example (N : ℕ) [NeZero N] (k : ℤ) :
    FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k) :=
  CuspForm.finiteDimensional_cuspForm N k

/-- The file-local instance interface (no consumer outside the pin file). -/
example (N : ℕ) [NeZero N] (k : ℤ) :
    FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k) :=
  CuspForm.finiteDimensional_Gamma0

end
