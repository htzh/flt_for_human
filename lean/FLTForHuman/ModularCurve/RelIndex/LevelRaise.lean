/-
Raising the level of a modular form by `t`, and twisting it by an upper-right
translation.

For a subgroup `Γg ≤ GL(2, ℝ)`, a natural `t ≠ 0` and `x : ℝ`:

* `raise t f` is `t ^ (k-1) • (f ∣[k] heckeDiagMatrix t)`, a modular form for
  `t⁻¹ Γg t` with the same coefficients, reindexed (`τ ↦ t τ`);
* `twist x f` is `f` translated by `!![1, x; 0, 1]`, a modular form for the
  conjugate subgroup, whose `q`-expansion is `f`'s with the coefficient of `q^m`
  multiplied by `exp (2πix)^m`;
* `hP N γ` is the upper-triangular matrix `!![hA, hB; 0, hD]` of the Hermite datum
  of `γ` (`ModularCurve/RelIndex/Hermite.lean`), and `heckeDiag_mul_eq` /
  `heckeDiag_smul_smul` identify `heckeDiagMatrix N * γ` with it on the upper
  half-plane. Together with `raise` this is what turns a conjugate
  `ρ(γ) = j(q^N)` into an explicit Laurent series `qExpand (nA²) (qTwist …)`.

This is the `Groups`/`Raise`/`TwistRaise` half of the `RelIndex` body
(`P2M/Sol/S_ModularCurve_relIndex_gamma0_le_relrank_adjoin_insert_jqNModC.lean:222-463`).

Dedup (`topics/TOPIC-dedup-refactoring.md` §3). The port carries four *level-
and group-specific* level-raise operators — `XH/HeckeInputs.lean:193` and
`X1/IsIntegralAtkinLehner.lean:215`, `X1/AtkinLehnerExchange.lean:611,1413` — and
one private `liftDiag` in `ModularForms/FrickeReciprocity.lean`. None of them is
this general `t`/`x` form, so this module is the general home and they are the
residue (`§8`); the cut does not open them (`§6`, fourth rule). The `hP` block
has no port counterpart at all. `heckeDiagMatrix`, `val_heckeDiagMatrix`,
`coe_heckeDiagMatrix_smul`, `slash_heckeDiagMatrix_apply` and `upperTriangularGL`
are `ModularForms/Defs/HeckeOperator.lean`'s and are imported, as is the
coefficient transport `ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul`
(`ModularForms/HeckeQCoeff.lean`).

The `qC`-facing consequences (`qC_raise`, `qC_twist`, `qC_twRaiseFn`) are in
`ModularCurve/RelIndex/RatioField.lean`, next to `qC` itself.

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_relIndex_gamma0_le_relrank_adjoin_insert_jqNModC.lean
-/
import FLTForHuman.ModularForms.Defs.HeckeOperator
import FLTForHuman.ModularForms.HeckeQCoeff
import FLTForHuman.ModularCurve.RelIndex.Hermite
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.NumberTheory.ModularForms.SlashInvariantForms

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open scoped MatrixGroups Pointwise

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix

namespace ModularCurve

namespace RelIndex

/-! ## Periodicity of a level-`T` subgroup -/

theorem one_mem_strictPeriods {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ) :
    (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
  exact AddSubgroup.mem_zmultiples _

theorem natCast_mem_strictPeriods {Γg : Subgroup (GL (Fin 2) ℝ)}
    (hΓ : (1 : ℝ) ∈ Γg.strictPeriods) (t : ℕ) : (t : ℝ) ∈ Γg.strictPeriods := by
  simpa using AddSubgroup.nsmul_mem _ hΓ t

/-! ## The upper-triangular matrix of the Hermite datum -/

variable (N : ℕ) [NeZero N]

/-- The upper-triangular `!![hA, hB; 0, hD]` of `γ`'s Hermite datum, as an
element of `GL(2, ℝ)`. -/
def hP (γ : SL(2, ℤ)) : GL (Fin 2) ℝ :=
  upperTriangularGL (hA N γ) (hB N γ) (hD N γ)
    (by exact_mod_cast (mul_pos (hA_pos N γ) (hD_pos N γ)).ne')

theorem val_hP (γ : SL(2, ℤ)) :
    ((hP N γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(hA N γ : ℝ), (hB N γ : ℝ); 0, (hD N γ : ℝ)] := rfl

theorem heckeDiag_mul_eq (γ : SL(2, ℤ)) :
    heckeDiagMatrix N * ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) =
      ((hδ N γ : SL(2, ℤ)) : GL (Fin 2) ℝ) * hP N γ := by
  have hM := dMul_eq_hermite N γ
  have hent : ∀ i j, (dMul N γ i j : ℝ) =
      (((hδ N γ : Matrix (Fin 2) (Fin 2) ℤ) * !![hA N γ, hB N γ; 0, hD N γ]) i j : ℝ) := by
    intro i j; rw [hM]
  ext i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, val_heckeDiagMatrix (NeZero.ne N), val_hP]
  have h := hent i j
  fin_cases i <;> fin_cases j <;>
    simp [dMul, Matrix.mul_apply, Fin.sum_univ_two] at h ⊢ <;> linarith

theorem heckeDiag_smul_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    heckeDiagMatrix N • ((γ : SL(2, ℤ)) • τ) = (hδ N γ : SL(2, ℤ)) • (hP N γ • τ) := by
  rw [ModularGroup.sl_moeb, ModularGroup.sl_moeb, ← mul_smul, ← mul_smul, heckeDiag_mul_eq]

theorem coe_upperRightHom_smul (x : ℝ) (τ : ℍ) :
    (((Matrix.GeneralLinearGroup.upperRightHom x • τ : ℍ)) : ℂ) = (τ : ℂ) + x := by
  have hdet : 0 < ((Matrix.GeneralLinearGroup.upperRightHom x).det : ℝˣ).val := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    simp [Matrix.det_fin_two_of]
  rw [UpperHalfPlane.coe_smul_of_det_pos hdet]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom]

theorem coe_hP_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    (((hP N γ • τ : ℍ)) : ℂ) = ((hA N γ : ℂ) * τ + (hB N γ : ℂ)) / (hD N γ : ℂ) := by
  have hdet : 0 < ((hP N γ).det : ℝˣ).val := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, val_hP, Matrix.det_fin_two_of]
    have := mul_pos (hA_pos N γ) (hD_pos N γ)
    simp only [mul_zero, sub_zero]
    exact_mod_cast this
  rw [UpperHalfPlane.coe_smul_of_det_pos hdet]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, val_hP]

theorem hP_smul_heckeDiag_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    hP N γ • (heckeDiagMatrix N • τ) =
      Matrix.GeneralLinearGroup.upperRightHom ((hB N γ : ℝ) / (hD N γ : ℝ)) •
        (heckeDiagMatrix (nA N γ ^ 2) • τ) := by
  have hN : N ≠ 0 := NeZero.ne N
  have ha2 : nA N γ ^ 2 ≠ 0 := pow_ne_zero _ (nA_ne_zero N γ)
  have hd' : (hD N γ : ℂ) ≠ 0 := by exact_mod_cast (hD_pos N γ).ne'
  have had : (hA N γ : ℂ) * (hD N γ : ℂ) = N := by exact_mod_cast hA_mul_hD N γ
  have haN : ((nA N γ ^ 2 : ℕ) : ℂ) = (hA N γ : ℂ) ^ 2 := by
    push_cast; rw [← nA_cast N γ]; push_cast; ring
  apply UpperHalfPlane.ext
  rw [coe_hP_smul, coe_heckeDiagMatrix_smul hN, coe_upperRightHom_smul, coe_heckeDiagMatrix_smul ha2,
    haN]
  push_cast
  field_simp
  rw [← had]
  ring

/-! ## The raise operation -/

section Raise

variable {Γg : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

theorem one_mem_strictPeriods_conj (g : GL (Fin 2) ℝ)
    (h : g * Matrix.GeneralLinearGroup.upperRightHom (1 : ℝ) * g⁻¹ ∈ Γg) :
    (1 : ℝ) ∈ (ConjAct.toConjAct g⁻¹ • Γg).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ← ConjAct.toConjAct_inv, inv_inv, ConjAct.toConjAct_smul]
  exact h

theorem heckeDiag_conj_upperRightHom {t : ℕ} (ht : t ≠ 0) :
    heckeDiagMatrix t * Matrix.GeneralLinearGroup.upperRightHom (1 : ℝ) * (heckeDiagMatrix t)⁻¹ =
      Matrix.GeneralLinearGroup.upperRightHom (t : ℝ) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, val_heckeDiagMatrix ht]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.upperRightHom]

theorem one_mem_strictPeriods_conjDiag (hΓ : (1 : ℝ) ∈ Γg.strictPeriods) {t : ℕ} (ht : t ≠ 0) :
    (1 : ℝ) ∈ (ConjAct.toConjAct (heckeDiagMatrix t)⁻¹ • Γg).strictPeriods := by
  refine one_mem_strictPeriods_conj _ ?_
  rw [heckeDiag_conj_upperRightHom ht]
  exact (Subgroup.mem_strictPeriods_iff).mp (natCast_mem_strictPeriods hΓ t)

/-- Raise the level: `f` precomposed with `τ ↦ t τ`, at the same weight. -/
def raise (t : ℕ) [NeZero t] (f : ModularForm Γg k) :
    ModularForm (ConjAct.toConjAct (heckeDiagMatrix t)⁻¹ • Γg) k :=
  ((t : ℝ) ^ (k - 1))⁻¹ • ModularForm.translate f (heckeDiagMatrix t)

theorem raise_apply (t : ℕ) [NeZero t] (f : ModularForm Γg k) (τ : ℍ) :
    raise t f τ = f (heckeDiagMatrix t • τ) := by
  have ht : (t : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne t
  show ((t : ℝ) ^ (k - 1))⁻¹ • ((⇑f ∣[k] heckeDiagMatrix t) τ) = _
  rw [slash_heckeDiagMatrix_apply k (NeZero.ne t), Complex.real_smul]
  push_cast
  rw [← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero _ ht), one_mul]

theorem coe_raise (t : ℕ) [NeZero t] (f : ModularForm Γg k) :
    ⇑(raise t f) = fun τ => f (heckeDiagMatrix t • τ) :=
  funext (raise_apply t f)

theorem coeff_qExpansion_raise (hΓ : (1 : ℝ) ∈ Γg.strictPeriods) (t : ℕ) [NeZero t]
    (f : ModularForm Γg k) (n : ℕ) :
    PowerSeries.coeff n (qExpansion 1 (raise t f)) =
      if t ∣ n then PowerSeries.coeff (n / t) (qExpansion 1 f) else 0 := by
  rw [coe_raise]
  exact ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul f hΓ (NeZero.ne t) n

/-- The upper-right translation `!![1, x; 0, 1]`. -/
abbrev Ux (x : ℝ) : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.upperRightHom x

/-- Twist by the upper-right translation `τ ↦ τ + x`. -/
def twist (x : ℝ) (F : ModularForm Γg k) : ModularForm (ConjAct.toConjAct (Ux x)⁻¹ • Γg) k :=
  ModularForm.translate F (Ux x)

theorem twist_apply (x : ℝ) (F : ModularForm Γg k) (τ : ℍ) : twist x F τ = F (Ux x • τ) := by
  rw [twist, ModularForm.coe_translate, ModularForm.slash_apply]
  have hdet : ((Ux x).det : ℝˣ).val = 1 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]; simp [Matrix.det_fin_two_of]
  have hσ : UpperHalfPlane.σ (Ux x) = .refl ℝ ℂ := by
    unfold UpperHalfPlane.σ
    rw [hdet]
    simp
  have hden : UpperHalfPlane.denom (Ux x) τ = 1 := by
    simp [UpperHalfPlane.denom]
  rw [hσ, hdet, hden]
  simp

theorem coe_twist (x : ℝ) (F : ModularForm Γg k) : ⇑(twist x F) = fun τ => F (Ux x • τ) :=
  funext (twist_apply x F)

theorem one_mem_strictPeriods_twist (hΓ : (1 : ℝ) ∈ Γg.strictPeriods) (x : ℝ) :
    (1 : ℝ) ∈ (ConjAct.toConjAct (Ux x)⁻¹ • Γg).strictPeriods := by
  refine one_mem_strictPeriods_conj _ ?_
  have hcomm : Ux x * Matrix.GeneralLinearGroup.upperRightHom (1 : ℝ) * (Ux x)⁻¹ =
      Matrix.GeneralLinearGroup.upperRightHom (1 : ℝ) := by
    rw [Ux, ← AddChar.map_add_eq_mul, ← AddChar.map_neg_eq_inv, ← AddChar.map_add_eq_mul]
    congr 1; ring
  rw [hcomm]
  exact (Subgroup.mem_strictPeriods_iff).mp hΓ

theorem qParam_Ux_smul (x : ℝ) (τ : ℍ) :
    Function.Periodic.qParam 1 ((Ux x • τ : ℍ) : ℂ) =
      Complex.exp (2 * Real.pi * Complex.I * x) * Function.Periodic.qParam 1 τ := by
  rw [Function.Periodic.qParam, Function.Periodic.qParam, coe_upperRightHom_smul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem coeff_qExpansion_twist (hΓ : (1 : ℝ) ∈ Γg.strictPeriods) (x : ℝ) (F : ModularForm Γg k)
    (m : ℕ) :
    (qExpansion 1 (twist x F)).coeff m =
      Complex.exp (2 * Real.pi * Complex.I * x) ^ m * (qExpansion 1 F).coeff m := by
  have : Fact (IsCusp OnePoint.infty Γg) := ⟨Γg.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex F hΓ
  have hhol := ModularFormClass.holo F
  have hbdd : IsBoundedAtImInfty (F : ℍ → ℂ) := ModularFormClass.bdd_at_infty F
  have hF : ∀ τ : ℍ, HasSum (fun n : ℕ => (Complex.exp (2 * Real.pi * Complex.I * x) ^ n *
      (qExpansion 1 F).coeff n) • Function.Periodic.qParam 1 τ ^ n) (twist x F τ) := by
    intro τ
    have h := hasSum_qExpansion one_pos hper hhol hbdd (Ux x • τ)
    have hfun : (fun n : ℕ => (Complex.exp (2 * Real.pi * Complex.I * x) ^ n *
        (qExpansion 1 F).coeff n) • Function.Periodic.qParam 1 τ ^ n) =
        fun n : ℕ => (qExpansion 1 F).coeff n • Function.Periodic.qParam 1 ((Ux x • τ : ℍ) : ℂ) ^ n := by
      funext n
      rw [qParam_Ux_smul, mul_pow, smul_eq_mul, smul_eq_mul]
      ring
    rw [hfun, twist_apply]
    exact h
  exact (ModularFormClass.qExpansion_coeff_unique one_pos (one_mem_strictPeriods_twist hΓ x) hF m).symm

end Raise

/-! ## Twisted raises -/

section TwistRaise

variable {Γg : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

def expU (x : ℝ) : ℂˣ := Units.mk0 (Complex.exp (2 * Real.pi * Complex.I * x)) (Complex.exp_ne_zero _)

@[scoped simp] theorem val_expU (x : ℝ) :
    (expU x : ℂ) = Complex.exp (2 * Real.pi * Complex.I * x) := rfl

/-- `F` twisted by `x` and then raised by `t`: the composite `τ ↦ F (x + t τ)`. -/
def twRaiseFn (x : ℝ) (t : ℕ) (F : ModularForm Γg k) : ℍ → ℂ :=
  fun τ => F (Ux x • (heckeDiagMatrix t • τ))

theorem twRaiseFn_eq (x : ℝ) (t : ℕ) [NeZero t] (F : ModularForm Γg k) :
    twRaiseFn x t F = ⇑(raise t (twist x F)) := by
  funext τ
  rw [raise_apply, twist_apply]
  rfl

end TwistRaise

end RelIndex

end ModularCurve
