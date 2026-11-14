/-
  The primitive-form level reduction: the `q`-power divisibility criterion, and the level and
  `q`-expansion of a primitive form.

  * `CuspForm.IsPrimitiveForm.pow_dvd_of_pow_dvd_of_sq_dvd_of_factorsThrough_of_forall_coprime_qCoeff_eq`:
    if a prime `q` has `q ^ 2 ∣ d * M` and `q ∤ d`, then `q` divides the level `M` of a primitive form
    through the `q`-power divisibility criterion on its coefficients (`LiCaseOne`: the `q`-coefficient
    layer, the nebentypus layer `Neb`, the beta layer `Beta` and `Main`).
  * `CuspForm.IsPrimitiveForm.level_eq_and_qCoeff_eq_of_forall_prime_notMem_qCoeff_eq`: a primitive
    form is determined by its level and by the coefficients at the primes not dividing it
    (`SMOGamma1`: the strong multiplicity-one step on the `q`-expansion).

  Transcribed from the pin's proof files (pinned `aa2d8b3`)
  `P2M/Sol/S_CuspForm_IsPrimitiveForm_pow_dvd_of_pow_dvd_of_sq_dvd_of_factorsThrough_of_forall_coprime_qCoeff_eq.lean`
  (802 lines, `namespace LiCaseOne`, sections `QCoeff` `Neb` `Beta` `Main`) and
  `S_CuspForm_IsPrimitiveForm_level_eq_and_qCoeff_eq_of_forall_prime_notMem_qCoeff_eq.lean` (907 lines,
  `namespace SMOGamma1`), with the statements from the wrappers of the same names.  Both pin label
  namespaces are word names and are kept.

  Assumes from earlier modules: `ModularForms/PrimitiveFormSlash.lean` (the two coset-sum rows, the 802's
  only unported premises before this set), `ModularForms/NebentypusDirectSum.lean` (the coefficient
  vanishing under the slash-sum trace), `ModularForms/NewformDecomposition.lean` (the newform
  decomposition, multiplicity one, and the nebentypus level-lowering row),
  `ModularForms/AtkinLehnerLowering.lean` (the plain level-lowering row),
  `ModularForms/HeckeDiagDegeneracy.lean` (the degeneracy lift), and the three coefficient/norm rows
  `ModularForms/WeightOne/{PrimitiveQCoeffNorm,NebentypusQCoeffSq}.lean` and
  `ModularForms/Analytic/NormSqLt.lean` (`norm_qCoeff_sq_eq_pow_…`, `qCoeff_sq_eq_mul_zpow_…`,
  `norm_sq_lt_…`).

  spec-pin: Theorems/Thm_CuspForm_IsPrimitiveForm_pow_dvd_of_pow_dvd_of_sq_dvd_of_factorsThrough_of_forall_coprime_qCoeff_eq.lean
  spec-pin: P2M/Sol/S_CuspForm_IsPrimitiveForm_pow_dvd_of_pow_dvd_of_sq_dvd_of_factorsThrough_of_forall_coprime_qCoeff_eq.lean
  spec-pin: Theorems/Thm_CuspForm_IsPrimitiveForm_level_eq_and_qCoeff_eq_of_forall_prime_notMem_qCoeff_eq.lean
  spec-pin: P2M/Sol/S_CuspForm_IsPrimitiveForm_level_eq_and_qCoeff_eq_of_forall_prime_notMem_qCoeff_eq.lean
-/
import FLTForHuman.ModularForms.PrimitiveFormSlash
import FLTForHuman.ModularForms.NebentypusDirectSum
import FLTForHuman.ModularForms.NewformDecomposition
import FLTForHuman.ModularForms.AtkinLehnerLowering
import FLTForHuman.ModularForms.HeckeDiagDegeneracy
import FLTForHuman.ModularForms.HeckeULevel
import FLTForHuman.ModularForms.HeckeNebentypusExistence
import FLTForHuman.ModularForms.HeckePrelude
import FLTForHuman.ModularForms.HeckeQCoeff
import FLTForHuman.ModularForms.WeightOne.PrimitiveQCoeffNorm
import FLTForHuman.ModularForms.WeightOne.NebentypusQCoeffSq
import FLTForHuman.ModularForms.Analytic.NormSqLt
import FLTForHuman.ModularForms.Defs.PrimitiveFormGamma1
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section


namespace LiCaseOne

open CongruenceSubgroup ModularForm ModularFormClass Matrix.SpecialLinearGroup
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm ComplexConjugate

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section QCoeff

variable {L : ℕ} {k : ℤ}

theorem one_mem_strictPeriods (L : ℕ) : (1 : ℝ) ∈ (Γ₁ℝ L).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]
  exact AddSubgroup.mem_zmultiples _

theorem periodic (f : CuspForm (Γ₁ℝ L) k) : Function.Periodic (⇑f ∘ ofComplex) 1 := by
  exact SlashInvariantFormClass.periodic_comp_ofComplex f (one_mem_strictPeriods L)

theorem bdd (f : CuspForm (Γ₁ℝ L) k) : IsBoundedAtImInfty (⇑f) := by
  have : Fact (IsCusp OnePoint.infty (Γ₁ℝ L)) :=
    ⟨(Γ₁ℝ L).isCusp_of_mem_strictPeriods one_pos (one_mem_strictPeriods L)⟩
  exact ModularFormClass.bdd_at_infty f

theorem analytic (f : CuspForm (Γ₁ℝ L) k) : AnalyticAt ℂ (cuspFunction 1 (⇑f)) 0 := by
  exact analyticAt_cuspFunction_zero one_pos (periodic f) f.holo' (bdd f)

theorem qCoeff_zero_fun (n : ℕ) : qCoeff (0 : ℍ → ℂ) n = 0 := by
  simp [qCoeff, UpperHalfPlane.qExpansion_zero]

theorem qCoeff_zero (n : ℕ) : qCoeff (⇑(0 : CuspForm (Γ₁ℝ L) k)) n = 0 := by
  simp [qCoeff, UpperHalfPlane.qExpansion_zero]

theorem qCoeff_smul (c : ℂ) (f : CuspForm (Γ₁ℝ L) k) (n : ℕ) :
    qCoeff (⇑(c • f)) n = c * qCoeff (⇑f) n := by
  rw [qCoeff, qCoeff, FunLike.coe_smul, qExpansion_smul (analytic f), map_smul, smul_eq_mul]

theorem qCoeff_sub (f g : CuspForm (Γ₁ℝ L) k) (n : ℕ) :
    qCoeff (⇑(f - g)) n = qCoeff (⇑f) n - qCoeff (⇑g) n := by
  rw [qCoeff, qCoeff, qCoeff, FunLike.coe_sub, qExpansion_sub (analytic f) (analytic g),
    map_sub]

theorem qCoeff_add (f g : CuspForm (Γ₁ℝ L) k) (n : ℕ) :
    qCoeff (⇑(f + g)) n = qCoeff (⇑f) n + qCoeff (⇑g) n := by
  rw [qCoeff, qCoeff, qCoeff, FunLike.coe_add, qExpansion_add (analytic f) (analytic g),
    map_add]

end QCoeff

section Neb

variable {M : ℕ} {k : ℤ}

theorem hasNebentypus_zero (ε : DirichletCharacter ℂ M) :
    CuspForm.HasNebentypus ε (0 : CuspForm (Γ₁ℝ M) k) := by
  intro γ _ τ; simp

theorem hasNebentypus_add {ε : DirichletCharacter ℂ M} {f g : CuspForm (Γ₁ℝ M) k}
    (hf : CuspForm.HasNebentypus ε f) (hg : CuspForm.HasNebentypus ε g) :
    CuspForm.HasNebentypus ε (f + g) := by
  intro γ hγ τ
  rw [add_apply, add_apply, hf γ hγ τ, hg γ hγ τ]; ring

theorem hasNebentypus_sub {ε : DirichletCharacter ℂ M} {f g : CuspForm (Γ₁ℝ M) k}
    (hf : CuspForm.HasNebentypus ε f) (hg : CuspForm.HasNebentypus ε g) :
    CuspForm.HasNebentypus ε (f - g) := by
  intro γ hγ τ
  rw [sub_apply, sub_apply, hf γ hγ τ, hg γ hγ τ]; ring

theorem hasNebentypus_smul {ε : DirichletCharacter ℂ M} {f : CuspForm (Γ₁ℝ M) k}
    (hf : CuspForm.HasNebentypus ε f) (c : ℂ) : CuspForm.HasNebentypus ε (c • f) := by
  intro γ hγ τ
  rw [smul_apply, smul_apply, smul_eq_mul, smul_eq_mul, hf γ hγ τ]; ring

end Neb

section Beta

variable {k : ℤ}

theorem coe_beta (m : ℤ) :
    ((ModularGroup.S * ModularGroup.T ^ m * ModularGroup.S⁻¹ : SL(2, ℤ)) :
      Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; -m, 1] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    ModularGroup.coe_T_zpow, ModularGroup.coe_S, Matrix.SpecialLinearGroup.coe_inv,
    ModularGroup.coe_S]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

theorem beta_apply (m : ℤ) (i j : Fin 2) :
    (ModularGroup.S * ModularGroup.T ^ m * ModularGroup.S⁻¹ : SL(2, ℤ)) i j = !![1, 0; -m, 1] i j := by
  rw [← coe_beta]

theorem beta_add (m m' : ℤ) :
    (ModularGroup.S * ModularGroup.T ^ (m + m') * ModularGroup.S⁻¹ : SL(2, ℤ))
      = (ModularGroup.S * ModularGroup.T ^ m * ModularGroup.S⁻¹)
        * (ModularGroup.S * ModularGroup.T ^ m' * ModularGroup.S⁻¹) := by
  rw [_root_.zpow_add]; group

theorem beta_mem_Gamma1 (L : ℕ) (r : ℤ) :
    (ModularGroup.S * ModularGroup.T ^ ((L : ℤ) * r) * ModularGroup.S⁻¹ : SL(2, ℤ)) ∈ Gamma1 L := by
  rw [Gamma1_mem]
  refine ⟨?_, ?_, ?_⟩ <;> simp [beta_apply]

theorem coe_beta_smul (m : ℤ) (τ : ℍ) :
    (((ModularGroup.S * ModularGroup.T ^ m * ModularGroup.S⁻¹ : SL(2, ℤ)) • τ : ℍ) : ℂ)
      = (τ : ℂ) / (1 - (m : ℂ) * (τ : ℂ)) := by
  rw [UpperHalfPlane.specialLinearGroup_apply]
  simp only [beta_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  simp only [algebraMap_int_eq, eq_intCast, Int.cast_one, Complex.ofReal_one, one_mul,
    Int.cast_zero, Complex.ofReal_zero, add_zero, Int.cast_neg, Complex.ofReal_neg,
    Complex.ofReal_intCast]
  ring_nf

theorem slash_beta_apply (k : ℤ) (G : ℍ → ℂ) (m : ℤ) (τ : ℍ) :
    (G ∣[k] (ModularGroup.S * ModularGroup.T ^ m * ModularGroup.S⁻¹ : SL(2, ℤ))) τ
      = G ((ModularGroup.S * ModularGroup.T ^ m * ModularGroup.S⁻¹ : SL(2, ℤ)) • τ)
          * (1 - (m : ℂ) * (τ : ℂ)) ^ (-k) := by
  rw [ModularForm.SL_slash_apply, ModularGroup.denom_apply, beta_apply, beta_apply]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Int.cast_neg, Int.cast_one]
  ring_nf

theorem one_sub_ne_zero (m : ℤ) (τ : ℍ) : (1 - (m : ℂ) * (τ : ℂ)) ≠ 0 := by
  have h := denom_ne_zero (ModularGroup.S * ModularGroup.T ^ m * ModularGroup.S⁻¹ : SL(2, ℤ)) τ
  rw [ModularGroup.denom_apply, beta_apply, beta_apply] at h
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Int.cast_neg, Int.cast_one] at h
  intro h0; apply h; linear_combination h0

theorem slash_beta_add_level {P : ℕ} (F : CuspForm (Γ₁ℝ P) k) (m r : ℤ) :
    (⇑F : ℍ → ℂ) ∣[k] (ModularGroup.S * ModularGroup.T ^ (m + (P : ℤ) * r) * ModularGroup.S⁻¹ :
        SL(2, ℤ))
      = (⇑F : ℍ → ℂ) ∣[k] (ModularGroup.S * ModularGroup.T ^ m * ModularGroup.S⁻¹ : SL(2, ℤ)) := by
  rw [add_comm, beta_add]
  show (⇑F : ℍ → ℂ) ∣[k] (mapGL ℝ ((ModularGroup.S * ModularGroup.T ^ ((P : ℤ) * r) *
      ModularGroup.S⁻¹) * (ModularGroup.S * ModularGroup.T ^ m * ModularGroup.S⁻¹)) :
        GL (Fin 2) ℝ)
    = (⇑F : ℍ → ℂ) ∣[k] (mapGL ℝ (ModularGroup.S * ModularGroup.T ^ m * ModularGroup.S⁻¹) :
        GL (Fin 2) ℝ)
  rw [map_mul, SlashAction.slash_mul]
  congr 1
  exact SlashInvariantFormClass.slash_action_eq F _
    (Subgroup.mem_map.mpr
      ⟨(ModularGroup.S * ModularGroup.T ^ ((P : ℤ) * r) * ModularGroup.S⁻¹ : SL(2, ℤ)),
        beta_mem_Gamma1 P r, rfl⟩)

theorem slash_beta_level {P : ℕ} (F : CuspForm (Γ₁ℝ P) k) (r : ℤ) :
    (⇑F : ℍ → ℂ) ∣[k] (ModularGroup.S * ModularGroup.T ^ ((P : ℤ) * r) * ModularGroup.S⁻¹ :
        SL(2, ℤ)) = ⇑F := by
  show (⇑F : ℍ → ℂ) ∣[k] (mapGL ℝ (ModularGroup.S * ModularGroup.T ^ ((P : ℤ) * r) *
      ModularGroup.S⁻¹) : GL (Fin 2) ℝ) = ⇑F
  exact SlashInvariantFormClass.slash_action_eq F _
    (Subgroup.mem_map.mpr
      ⟨(ModularGroup.S * ModularGroup.T ^ ((P : ℤ) * r) * ModularGroup.S⁻¹ : SL(2, ℤ)),
        beta_mem_Gamma1 P r, rfl⟩)

end Beta

theorem sum_range_reindex {α : Type*} [AddCommMonoid α] {q : ℕ} (hq : q.Prime) (f : ℕ → α)
    (hper : ∀ y r : ℕ, f (y + q * r) = f y) {u : ℕ} (hu : ¬ q ∣ u) :
    ∑ j ∈ Finset.range q, f (j * u) = ∑ x ∈ Finset.range q, f x := by
  have hcop : Nat.Coprime u q := (Nat.coprime_comm).mp ((Nat.Prime.coprime_iff_not_dvd hq).mpr hu)
  obtain ⟨v, -, hv⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hq.one_lt
  have hqpos : 0 < q := hq.pos
  have hmod : ∀ j : ℕ, f (j * u) = f (j * u % q) := by
    intro j
    conv_lhs => rw [← Nat.mod_add_div (j * u) q]
    exact hper _ _
  simp_rw [hmod]
  refine Finset.sum_nbij' (fun j => j * u % q) (fun x => x * v % q) (fun j _ => ?_) (fun x _ => ?_)
    (fun j hj => ?_) (fun x hx => ?_) (fun j _ => rfl)
  · exact Finset.mem_range.mpr (Nat.mod_lt _ hqpos)
  · exact Finset.mem_range.mpr (Nat.mod_lt _ hqpos)
  · have hj' : j < q := Finset.mem_range.mp hj
    calc j * u % q * v % q = j * (u * v) % q := by
            rw [Nat.mul_mod (j * u % q) v, Nat.mod_mod, ← Nat.mul_mod, mul_assoc]
      _ = j % q := by rw [Nat.mul_mod, hv, mul_one, Nat.mod_mod]
      _ = j := Nat.mod_eq_of_lt hj'
  · have hx' : x < q := Finset.mem_range.mp hx
    calc x * v % q * u % q = x * (u * v) % q := by
            rw [Nat.mul_mod (x * v % q) u, Nat.mod_mod, ← Nat.mul_mod, mul_assoc, mul_comm v u]
      _ = x % q := by rw [Nat.mul_mod, hv, mul_one, Nat.mod_mod]
      _ = x := Nat.mod_eq_of_lt hx'

theorem changeLevel_apply_natCast {M M' : ℕ} [NeZero M] (h : M' ∣ M)
    (χ : DirichletCharacter ℂ M') {p : ℕ} (hp : Nat.Coprime p M) :
    DirichletCharacter.changeLevel h χ (p : ZMod M) = χ (p : ZMod M') := by
  have hu : IsUnit (p : ZMod M) := (ZMod.isUnit_iff_coprime p M).mpr hp
  rw [← hu.unit_spec, DirichletCharacter.changeLevel_eq_cast_of_dvd χ h, hu.unit_spec,
    ZMod.cast_natCast h]

theorem changeLevel_eq_of_forall_coprime {M₁ M₂ N : ℕ} [NeZero N] (h1 : M₁ ∣ N) (h2 : M₂ ∣ N)
    (ε₁ : DirichletCharacter ℂ M₁) (ε₂ : DirichletCharacter ℂ M₂)
    (hε : ∀ n : ℕ, Nat.Coprime n M₁ → Nat.Coprime n M₂ → ε₁ (n : ZMod M₁) = ε₂ (n : ZMod M₂)) :
    DirichletCharacter.changeLevel h1 ε₁ = DirichletCharacter.changeLevel h2 ε₂ := by
  apply MulChar.ext
  intro a
  have hcop : Nat.Coprime (a : ZMod N).val N := ZMod.val_coe_unit_coprime a
  have han : ((((a : ZMod N).val : ℕ)) : ZMod N) = a := ZMod.natCast_zmod_val _
  rw [← han, changeLevel_apply_natCast h1 ε₁ hcop, changeLevel_apply_natCast h2 ε₂ hcop]
  exact hε _ (hcop.coprime_dvd_right h1) (hcop.coprime_dvd_right h2)

section Main

variable {M₁ M₂ : ℕ} [NeZero M₁] [NeZero M₂] {k : ℤ}
    {ε₁ : DirichletCharacter ℂ M₁} {ε₂ : DirichletCharacter ℂ M₂}
    {g₁ : CuspForm (Γ₁ℝ M₁) k} {g₂ : CuspForm (Γ₁ℝ M₂) k}

theorem coe_heckeDiagMatrix_beta_smul {d : ℕ} (hd : d ≠ 0) (m : ℤ) (τ : ℍ) :
    ((heckeDiagMatrix d •
        ((ModularGroup.S * ModularGroup.T ^ m * ModularGroup.S⁻¹ : SL(2, ℤ)) • τ) : ℍ) : ℂ)
      = (d : ℂ) * (τ : ℂ) / (1 - (m : ℂ) * (τ : ℂ)) := by
  rw [coe_heckeDiagMatrix_smul hd, coe_beta_smul]; ring

theorem heckeMatrix_smul_heckeDiagMatrix_smul {q : ℕ} (hq : q ≠ 0) (τ : ℍ) :
    heckeMatrix q 0 • (heckeDiagMatrix q • τ) = τ := by
  apply UpperHalfPlane.ext
  rw [coe_heckeMatrix_smul hq, coe_heckeDiagMatrix_smul hq]
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  push_cast; field_simp; ring

theorem heckeDiagMatrix_one_smul (τ : ℍ) : heckeDiagMatrix 1 • τ = τ := by
  apply UpperHalfPlane.ext
  rw [coe_heckeDiagMatrix_smul one_ne_zero]
  push_cast; ring

theorem slash_beta_comp_apply (F : ℍ → ℂ) {d : ℕ} (hd : d ≠ 0) (m m' : ℤ)
    (hmm' : (m' : ℂ) * (d : ℂ) = (m : ℂ)) (τ : ℍ) :
    ((fun σ : ℍ => F (heckeDiagMatrix d • σ)) ∣[k]
        (ModularGroup.S * ModularGroup.T ^ m * ModularGroup.S⁻¹ : SL(2, ℤ))) τ
      = (F ∣[k] (ModularGroup.S * ModularGroup.T ^ m' * ModularGroup.S⁻¹ : SL(2, ℤ)))
          (heckeDiagMatrix d • τ) := by
  rw [slash_beta_apply, slash_beta_apply, coe_heckeDiagMatrix_smul hd]
  have hpt : heckeDiagMatrix d •
      ((ModularGroup.S * ModularGroup.T ^ m * ModularGroup.S⁻¹ : SL(2, ℤ)) • τ)
        = (ModularGroup.S * ModularGroup.T ^ m' * ModularGroup.S⁻¹ : SL(2, ℤ)) •
            (heckeDiagMatrix d • τ) := by
    apply UpperHalfPlane.ext
    rw [coe_heckeDiagMatrix_beta_smul hd, coe_beta_smul, coe_heckeDiagMatrix_smul hd]
    have h1 := one_sub_ne_zero m τ
    have h2 : (1 - (m' : ℂ) * ((d : ℂ) * (τ : ℂ))) ≠ 0 := by
      rw [← mul_assoc, hmm']; exact h1
    field_simp
    rw [← hmm']; ring
  rw [hpt]
  congr 1
  rw [← mul_assoc, hmm']

theorem main
    (h₁ : CuspForm.IsPrimitiveForm ε₁ g₁) (h₂ : CuspForm.IsPrimitiveForm ε₂ g₂)
    (ha : ∀ n : ℕ, Nat.Coprime n M₁ → Nat.Coprime n M₂ → qCoeff g₁ n = qCoeff g₂ n)
    (hε : ∀ n : ℕ, Nat.Coprime n M₁ → Nat.Coprime n M₂ → ε₁ (n : ZMod M₁) = ε₂ (n : ZMod M₂))
    {q : ℕ} (hq : q.Prime) (hqM : q ^ 2 ∣ M₁) (hε₁ : ε₁.FactorsThrough (M₁ / q))
    (j : ℕ) (hj : q ^ j ∣ M₁) : q ^ j ∣ M₂ := by
  classical
  by_contra hjM₂

  have hM₁0 : M₁ ≠ 0 := NeZero.ne M₁
  have hM₂0 : M₂ ≠ 0 := NeZero.ne M₂
  have hq0 : q ≠ 0 := hq.ne_zero
  have hq1 : 1 < q := hq.one_lt
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq0
  have hqM₁ : q ∣ M₁ := (dvd_pow_self q two_ne_zero).trans hqM
  have hqM₁q : q ∣ M₁ / q := Nat.dvd_div_of_mul_dvd (by rw [← pow_two]; exact hqM)

  set m : ℕ := M₁.factorization q with hmdef
  set e : ℕ := M₂.factorization q with hedef
  set A : ℕ := M₁ / q ^ m with hAdef
  set B : ℕ := M₂ / q ^ e with hBdef
  have hM₁A : q ^ m * A = M₁ := Nat.ordProj_mul_ordCompl_eq_self M₁ q
  have hM₂B : q ^ e * B = M₂ := Nat.ordProj_mul_ordCompl_eq_self M₂ q
  have hqA : Nat.Coprime q A := Nat.coprime_ordCompl hq hM₁0
  have hqB : Nat.Coprime q B := Nat.coprime_ordCompl hq hM₂0
  have hej : e < j := by
    by_contra hle
    push Not at hle
    exact hjM₂ ((hq.pow_dvd_iff_le_factorization hM₂0).mpr hle)
  have hjm : j ≤ m := (hq.pow_dvd_iff_le_factorization hM₁0).mp hj
  have hem : e + 1 ≤ m := by omega

  set L : ℕ := Nat.lcm M₁ M₂ with hLdef
  have hL0 : L ≠ 0 := Nat.lcm_ne_zero hM₁0 hM₂0
  have hM₁L : M₁ ∣ L := Nat.dvd_lcm_left M₁ M₂
  have hM₂L : M₂ ∣ L := Nat.dvd_lcm_right M₁ M₂
  have hqL : q ∣ L := hqM₁.trans hM₁L
  set t : ℕ := L / q with htdef
  have hLqt : q * t = L := Nat.mul_div_cancel' hqL
  have ht0 : t ≠ 0 := by intro h; apply hL0; rw [← hLqt, h, mul_zero]
  have : NeZero t := ⟨ht0⟩
  have : NeZero (q * t) := ⟨by rw [hLqt]; exact hL0⟩
  have hqt : q ∣ t := by
    apply Nat.dvd_div_of_mul_dvd
    rw [← pow_two]; exact hqM.trans hM₁L
  have hM₁N : M₁ ∣ q * t := by rw [hLqt]; exact hM₁L
  have hM₂N : M₂ ∣ q * t := by rw [hLqt]; exact hM₂L

  have hqM₂N : q * M₂ ∣ q * t := by
    rw [hLqt, ← hM₂B, ← mul_assoc, ← pow_succ']
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.Coprime.pow_left _ hqB) ?_ ?_
    · exact ((pow_dvd_pow q (by omega : e + 1 ≤ j)).trans hj).trans hM₁L
    · exact (Dvd.intro_left _ hM₂B).trans hM₂L
  have hM₂t : M₂ ∣ t := Nat.dvd_of_mul_dvd_mul_left hq.pos hqM₂N

  have hLdvd : L ∣ q ^ m * (A * B) := by
    refine Nat.lcm_dvd ?_ ?_
    · rw [← hM₁A, ← mul_assoc]; exact Dvd.intro _ rfl
    · rw [← hM₂B]
      calc q ^ e * B ∣ q ^ m * B := mul_dvd_mul_right (pow_dvd_pow q (by omega)) B
        _ ∣ q ^ m * (A * B) := mul_dvd_mul_left _ (Dvd.intro_left A rfl)
  have hnot : ¬ q ^ (m + 1) ∣ q * t := by
    rw [hLqt]
    intro h
    have h' : q ^ m * q ∣ q ^ m * (A * B) := by rw [← pow_succ]; exact h.trans hLdvd
    have h'' : q ∣ A * B := Nat.dvd_of_mul_dvd_mul_left (pow_pos hq.pos m) h'
    rcases (Nat.Prime.dvd_mul hq).mp h'' with hA' | hB'
    · exact (Nat.Prime.coprime_iff_not_dvd hq).mp hqA hA'
    · exact (Nat.Prime.coprime_iff_not_dvd hq).mp hqB hB'

  set P : ℕ := M₁ * M₂ with hPdef
  have hP0 : P ≠ 0 := mul_ne_zero hM₁0 hM₂0
  set K : ℕ := P / q ^ P.factorization q with hKdef
  have hK0 : K ≠ 0 := (Nat.ordCompl_pos q hP0).ne'
  have hqK : Nat.Coprime q K := Nat.coprime_ordCompl hq hP0
  have hPK : q ^ P.factorization q * K = P := Nat.ordProj_mul_ordCompl_eq_self P q
  have hKcop : ∀ n : ℕ, Nat.Coprime n K → ¬ q ∣ n → Nat.Coprime n M₁ ∧ Nat.Coprime n M₂ := by
    intro n hnK hqn
    have hnq : Nat.Coprime n q := Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqn)
    have hnP : Nat.Coprime n P := by
      rw [← hPK]; exact Nat.Coprime.mul_right (hnq.pow_right _) hnK
    exact ⟨hnP.coprime_dvd_right (Dvd.intro _ rfl), hnP.coprime_dvd_right (Dvd.intro_left _ rfl)⟩

  set εt : DirichletCharacter ℂ t := DirichletCharacter.changeLevel hM₂t ε₂ with hεtdef
  set εN : DirichletCharacter ℂ (q * t) :=
    DirichletCharacter.changeLevel (dvd_mul_left t q) εt with hεNdef
  have hεN₂ : DirichletCharacter.changeLevel hM₂N ε₂ = εN := by
    rw [hεNdef, hεtdef, ← DirichletCharacter.changeLevel_trans]
  have hεN₁ : DirichletCharacter.changeLevel hM₁N ε₁ = εN := by
    rw [← hεN₂]; exact changeLevel_eq_of_forall_coprime hM₁N hM₂N ε₁ ε₂ hε

  have haq₁ : qCoeff g₁ q = 0 := by
    obtain ⟨hdvd, χ, hχ⟩ := hε₁
    have h₁' : CuspForm.IsPrimitiveForm
        (DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd hqM₁) χ) g₁ := by
      rw [hχ] at h₁; exact h₁
    exact CuspForm.IsPrimitiveForm.qCoeff_eq_zero_of_dvd_div M₁ k hq hqM₁ hqM₁q χ g₁ h₁'

  set b : ℂ := qCoeff g₂ q with hbdef
  set c₂ : ℂ := if q ∣ M₂ then 0 else ε₂ (q : ZMod M₂) * (q : ℂ) ^ (k - 1) with hc₂def
  have hrel₂ : ∀ n : ℕ, qCoeff g₂ (q * n)
      = b * qCoeff g₂ n - c₂ * (if q ∣ n then qCoeff g₂ (n / q) else 0) := by
    intro n
    by_cases hqM₂ : q ∣ M₂
    · rw [hc₂def, ite_eq_left hqM₂, zero_mul, sub_zero]
      exact h₂.isEigenformWith.hecke_of_dvd hq hqM₂ n
    · rw [hc₂def, ite_eq_right hqM₂]
      linear_combination h₂.isEigenformWith.hecke_of_not_dvd hq hqM₂ n
  have hrel₁ : ∀ n : ℕ, qCoeff g₁ (q * n) = 0 := fun n => by
    rw [h₁.isEigenformWith.hecke_of_dvd hq hqM₁ n, haq₁, zero_mul]

  obtain ⟨G₁, hG₁fun, hG₁coef, hG₁neb⟩ := CuspForm.exists_degeneracy_gamma1_hasNebentypus
    (k := k) (N := q * t) (d := 1) (by rw [mul_one]; exact hM₁N) g₁
  obtain ⟨G₂, hG₂fun, hG₂coef, hG₂neb⟩ := CuspForm.exists_degeneracy_gamma1_hasNebentypus
    (k := k) (N := q * t) (d := 1) (by rw [mul_one]; exact hM₂N) g₂
  obtain ⟨G₂t, hG₂tfun, hG₂tcoef, -⟩ := CuspForm.exists_degeneracy_gamma1_hasNebentypus
    (k := k) (N := t) (d := 1) (by rw [mul_one]; exact hM₂t) g₂
  obtain ⟨X, hXfun, hXcoef, hXneb⟩ := CuspForm.exists_degeneracy_gamma1_hasNebentypus
    (k := k) (N := q * t) (d := q) (by rw [mul_comm]; exact hqM₂N) g₂
  have hG₁val : ∀ τ, G₁ τ = g₁ τ := fun τ => by rw [hG₁fun, heckeDiagMatrix_one_smul]
  have hG₂val : ∀ τ, G₂ τ = g₂ τ := fun τ => by rw [hG₂fun, heckeDiagMatrix_one_smul]
  have hG₂tval : ∀ τ, G₂t τ = g₂ τ := fun τ => by rw [hG₂tfun, heckeDiagMatrix_one_smul]
  have hG₁c : ∀ n, qCoeff G₁ n = qCoeff g₁ n := fun n => by
    rw [hG₁coef, ite_eq_left (one_dvd n), Nat.div_one]
  have hG₂c : ∀ n, qCoeff G₂ n = qCoeff g₂ n := fun n => by
    rw [hG₂coef, ite_eq_left (one_dvd n), Nat.div_one]
  have hG₂tc : ∀ n, qCoeff G₂t n = qCoeff g₂ n := fun n => by
    rw [hG₂tcoef, ite_eq_left (one_dvd n), Nat.div_one]

  obtain ⟨Y, hYcoef, hYfun, hYneb⟩ : ∃ Y : CuspForm (Γ₁ℝ (q * t)) k,
      (∀ n : ℕ, qCoeff Y n = c₂ * (if q ^ 2 ∣ n then qCoeff g₂ (n / q ^ 2) else 0)) ∧
      (∀ τ : ℍ, Y τ = c₂ * g₂ (heckeDiagMatrix (q ^ 2) • τ)) ∧
      CuspForm.HasNebentypus εN Y := by
    by_cases hqM₂ : q ∣ M₂
    · refine ⟨0, fun n => ?_, fun τ => ?_, hasNebentypus_zero εN⟩
      · rw [qCoeff_zero, hc₂def, ite_eq_left hqM₂, zero_mul]
      · rw [zero_apply, hc₂def, ite_eq_left hqM₂, zero_mul]
    · have hq2M₂N : M₂ * q ^ 2 ∣ q * t := by
        rw [mul_comm]
        refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ ?_ hM₂N
        · exact Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqM₂)
        · rw [hLqt]; exact hqM.trans hM₁L
      obtain ⟨X2, hX2fun, hX2coef, hX2neb⟩ := CuspForm.exists_degeneracy_gamma1_hasNebentypus
        (k := k) (N := q * t) (d := q ^ 2) hq2M₂N g₂
      refine ⟨c₂ • X2, fun n => ?_, fun τ => ?_, ?_⟩
      · rw [qCoeff_smul, hX2coef]
      · rw [smul_apply, smul_eq_mul, hX2fun]
      · have := hasNebentypus_smul (hX2neb ε₂ h₂.isEigenformWith.hasNebentypus) c₂
        rwa [show DirichletCharacter.changeLevel (dvd_of_mul_right_dvd hq2M₂N) ε₂ = εN from hεN₂]
          at this

  set E : CuspForm (Γ₁ℝ (q * t)) k := G₁ - G₂ + b • X - Y with hEdef
  have hEneb : CuspForm.HasNebentypus εN E := by
    have h1 : CuspForm.HasNebentypus εN G₁ := by
      have := hG₁neb ε₁ h₁.isEigenformWith.hasNebentypus
      rwa [show DirichletCharacter.changeLevel _ ε₁ = εN from hεN₁] at this
    have h2 : CuspForm.HasNebentypus εN G₂ := by
      have := hG₂neb ε₂ h₂.isEigenformWith.hasNebentypus
      rwa [show DirichletCharacter.changeLevel _ ε₂ = εN from hεN₂] at this
    have h3 : CuspForm.HasNebentypus εN X := by
      have := hXneb ε₂ h₂.isEigenformWith.hasNebentypus
      rwa [show DirichletCharacter.changeLevel _ ε₂ = εN from hεN₂] at this
    exact hasNebentypus_sub (hasNebentypus_add (hasNebentypus_sub h1 h2) (hasNebentypus_smul h3 b)) hYneb
  have hEcoef : ∀ n : ℕ, qCoeff E n = if q ∣ n then 0 else qCoeff g₁ n - qCoeff g₂ n := by
    intro n
    rw [hEdef, qCoeff_sub, qCoeff_add, qCoeff_sub, qCoeff_smul, hG₁c, hG₂c, hXcoef, hYcoef]
    by_cases hqn : q ∣ n
    · obtain ⟨n₁, rfl⟩ := hqn
      rw [ite_eq_left (Dvd.intro n₁ rfl), ite_eq_left (Dvd.intro n₁ rfl), hrel₁, hrel₂,
        Nat.mul_div_cancel_left n₁ hq.pos]
      have hiff : (q ^ 2 ∣ q * n₁ ↔ q ∣ n₁) := by
        rw [pow_two]; exact Nat.mul_dvd_mul_iff_left hq.pos
      by_cases hqn₁ : q ∣ n₁
      · rw [ite_eq_left hqn₁, ite_eq_left (hiff.mpr hqn₁)]
        obtain ⟨n₂, rfl⟩ := hqn₁
        rw [Nat.mul_div_cancel_left n₂ hq.pos, pow_two, ← mul_assoc,
          Nat.mul_div_cancel_left n₂ (mul_pos hq.pos hq.pos)]
        ring
      · rw [ite_eq_right hqn₁, ite_eq_right (fun h => hqn₁ (hiff.mp h))]
        ring
    · rw [ite_eq_right hqn, ite_eq_right hqn,
        ite_eq_right (fun h => hqn ((dvd_pow_self q two_ne_zero).trans h))]
      ring
  have hEzero : ∀ n : ℕ, Nat.Coprime n K → qCoeff E n = 0 := by
    intro n hn
    rw [hEcoef]
    by_cases hqn : q ∣ n
    · rw [ite_eq_left hqn]
    · rw [ite_eq_right hqn]
      obtain ⟨hn₁, hn₂⟩ := hKcop n hn hqn
      rw [ha n hn₁ hn₂, sub_self]

  have hM₁qt : M₁ / q ∣ t := by
    have : M₁ / q * q ∣ t * q := by
      rw [Nat.div_mul_cancel hqM₁, mul_comm t q]; exact hM₁N
    exact Nat.dvd_of_mul_dvd_mul_right hq.pos this
  obtain ⟨u₁, hu₁⟩ := hM₁qt
  set D₁ : ℕ := M₁ / q with hD₁def
  have hD₁q : D₁ * q = M₁ := Nat.div_mul_cancel hqM₁
  have hqu₁ : ¬ q ∣ u₁ := by
    intro h
    apply hnot
    have hM₁t : M₁ ∣ t := by
      obtain ⟨w, hw⟩ := h
      exact ⟨w, by rw [hu₁, hw, ← mul_assoc, Nat.div_mul_cancel hqM₁]⟩
    calc q ^ (m + 1) = q * q ^ m := by ring
      _ ∣ q * M₁ := mul_dvd_mul_left q (Nat.ordProj_dvd M₁ q)
      _ ∣ q * t := mul_dvd_mul_left q hM₁t
  have hTa : ∀ τ : ℍ, ∑ i ∈ Finset.range q,
      ((⇑G₁ : ℍ → ℂ) ∣[k]
        (ModularGroup.S * ModularGroup.T ^ ((i : ℤ) * t) * ModularGroup.S⁻¹ : SL(2, ℤ))) τ = 0 := by
    intro τ
    have hG₁eq : (⇑G₁ : ℍ → ℂ) = ⇑g₁ := funext hG₁val
    rw [hG₁eq]
    have hper : ∀ y r : ℕ,
        ((⇑g₁ : ℍ → ℂ) ∣[k] (ModularGroup.S * ModularGroup.T ^ (((y + q * r : ℕ) : ℤ) * (D₁ : ℕ)) *
          ModularGroup.S⁻¹ : SL(2, ℤ))) τ
        = ((⇑g₁ : ℍ → ℂ) ∣[k] (ModularGroup.S * ModularGroup.T ^ ((y : ℤ) * (D₁ : ℕ)) *
          ModularGroup.S⁻¹ : SL(2, ℤ))) τ := by
      intro y r
      have : (((y + q * r : ℕ) : ℤ) * (D₁ : ℕ) : ℤ) = (y : ℤ) * (D₁ : ℕ) + (M₁ : ℤ) * r := by
        rw [← hD₁q]; push_cast; ring
      rw [this, slash_beta_add_level]
    have hstep : ∀ i : ℕ, ((i : ℤ) * t : ℤ) = ((i * u₁ : ℕ) : ℤ) * (D₁ : ℕ) := by
      intro i; rw [hu₁]; push_cast; ring
    simp_rw [hstep]
    rw [sum_range_reindex hq (fun x => ((⇑g₁ : ℍ → ℂ) ∣[k] (ModularGroup.S *
      ModularGroup.T ^ ((x : ℤ) * (D₁ : ℕ)) * ModularGroup.S⁻¹ : SL(2, ℤ))) τ) hper hqu₁,
      CuspForm.IsPrimitiveForm.sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_dvd M₁ k ε₁ g₁ h₁ hq
        hqM₁ τ, haq₁, map_zero, mul_zero, zero_mul]

  have hTb : ∀ τ : ℍ, ∑ i ∈ Finset.range q,
      ((⇑G₂ : ℍ → ℂ) ∣[k]
        (ModularGroup.S * ModularGroup.T ^ ((i : ℤ) * t) * ModularGroup.S⁻¹ : SL(2, ℤ))) τ
        = (q : ℂ) * G₂t τ := by
    intro τ
    have hG₂eq : (⇑G₂ : ℍ → ℂ) = ⇑g₂ := funext hG₂val
    obtain ⟨w, hw⟩ := hM₂t
    have hterm : ∀ i : ℕ, (⇑g₂ : ℍ → ℂ) ∣[k]
        (ModularGroup.S * ModularGroup.T ^ ((i : ℤ) * t) * ModularGroup.S⁻¹ : SL(2, ℤ)) = ⇑g₂ := by
      intro i
      have : ((i : ℤ) * t : ℤ) = (M₂ : ℤ) * (i * w) := by rw [hw]; push_cast; ring
      rw [this, slash_beta_level]
    rw [hG₂eq]
    simp_rw [hterm]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hG₂tval]

  obtain ⟨ΦX, hΦXfun, hΦX1⟩ : ∃ ΦX : CuspForm (Γ₁ℝ t) k,
      (∀ τ : ℍ, ΦX τ = ∑ i ∈ Finset.range q, ((⇑X : ℍ → ℂ) ∣[k]
        (ModularGroup.S * ModularGroup.T ^ ((i : ℤ) * t) * ModularGroup.S⁻¹ : SL(2, ℤ))) τ) ∧
      (qCoeff ΦX 1 = 0 ∨ (qCoeff ΦX 1 = (q : ℂ) ^ (1 - k) * conj b ∧ q ∣ M₂)) := by
    by_cases hA : M₂ * q ∣ t
    ·
      obtain ⟨Xt, hXtfun, hXtcoef, -⟩ := CuspForm.exists_degeneracy_gamma1_hasNebentypus
        (k := k) (N := t) (d := q) hA g₂
      have hXeq : (⇑X : ℍ → ℂ) = ⇑Xt := funext fun τ => by rw [hXfun, hXtfun]
      obtain ⟨w, hw⟩ := hA
      refine ⟨(q : ℂ) • Xt, fun τ => ?_, Or.inl ?_⟩
      · rw [hXeq]
        have hterm : ∀ i : ℕ, (⇑Xt : ℍ → ℂ) ∣[k]
            (ModularGroup.S * ModularGroup.T ^ ((i : ℤ) * t) * ModularGroup.S⁻¹ : SL(2, ℤ))
              = ⇑Xt := by
          intro i
          have : ((i : ℤ) * t : ℤ) = (t : ℤ) * i := by ring
          rw [this, slash_beta_level]
        simp_rw [hterm]
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, smul_apply, smul_eq_mul]
      · rw [qCoeff_smul, hXtcoef, ite_eq_right (fun h => hq1.ne' (Nat.dvd_one.mp h)), mul_zero]
    ·
      obtain ⟨u, hu⟩ := hM₂t
      have hqu : ¬ q ∣ u := by
        rintro ⟨w, hw⟩; apply hA; exact ⟨w, by rw [hu, hw]; ring⟩
      have hqM₂ : q ∣ M₂ := by
        rcases (Nat.Prime.dvd_mul hq).mp (hu ▸ hqt) with h | h
        · exact h
        · exact (hqu h).elim
      refine ⟨((q : ℂ) ^ (1 - k) * conj b) • G₂t, fun τ => ?_, Or.inr ⟨?_, hqM₂⟩⟩
      · rw [smul_apply, smul_eq_mul, hG₂tval]
        have hXeq : (⇑X : ℍ → ℂ) = fun σ => g₂ (heckeDiagMatrix q • σ) := funext hXfun
        rw [hXeq]

        set D₂ : ℕ := M₂ / q with hD₂def
        have hD₂q : D₂ * q = M₂ := Nat.div_mul_cancel hqM₂
        have htD : t = q * (u * D₂) := by
          rw [hu, ← hD₂q]; ring
        have hterm : ∀ i : ℕ,
            ((fun σ : ℍ => g₂ (heckeDiagMatrix q • σ)) ∣[k]
              (ModularGroup.S * ModularGroup.T ^ ((i : ℤ) * t) * ModularGroup.S⁻¹ : SL(2, ℤ))) τ
            = ((⇑g₂ : ℍ → ℂ) ∣[k] (ModularGroup.S *
                ModularGroup.T ^ (((i * u : ℕ) : ℤ) * (D₂ : ℕ)) * ModularGroup.S⁻¹ :
                  SL(2, ℤ))) (heckeDiagMatrix q • τ) := by
          intro i
          refine slash_beta_comp_apply (k := k) (⇑g₂) hq0 _ _ ?_ τ
          rw [htD]; push_cast; ring
        simp_rw [hterm]
        have hper : ∀ y r : ℕ,
            ((⇑g₂ : ℍ → ℂ) ∣[k] (ModularGroup.S *
              ModularGroup.T ^ (((y + q * r : ℕ) : ℤ) * (D₂ : ℕ)) * ModularGroup.S⁻¹ :
                SL(2, ℤ))) (heckeDiagMatrix q • τ)
            = ((⇑g₂ : ℍ → ℂ) ∣[k] (ModularGroup.S * ModularGroup.T ^ ((y : ℤ) * (D₂ : ℕ)) *
              ModularGroup.S⁻¹ : SL(2, ℤ))) (heckeDiagMatrix q • τ) := by
          intro y r
          have : (((y + q * r : ℕ) : ℤ) * (D₂ : ℕ) : ℤ)
              = (y : ℤ) * (D₂ : ℕ) + (M₂ : ℤ) * r := by
            rw [← hD₂q]; push_cast; ring
          rw [this, slash_beta_add_level]
        rw [sum_range_reindex hq (fun x => ((⇑g₂ : ℍ → ℂ) ∣[k] (ModularGroup.S *
          ModularGroup.T ^ ((x : ℤ) * (D₂ : ℕ)) * ModularGroup.S⁻¹ : SL(2, ℤ)))
            (heckeDiagMatrix q • τ)) hper hqu,
          CuspForm.IsPrimitiveForm.sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_dvd M₂ k ε₂ g₂ h₂
            hq hqM₂, heckeMatrix_smul_heckeDiagMatrix_smul hq0]
      · rw [qCoeff_smul, hG₂tc, h₂.isEigenformWith.qCoeff_one, mul_one]

  obtain ⟨ΦY, hΦYfun, hΦY1⟩ : ∃ ΦY : CuspForm (Γ₁ℝ t) k,
      (∀ τ : ℍ, ΦY τ = ∑ i ∈ Finset.range q, ((⇑Y : ℍ → ℂ) ∣[k]
        (ModularGroup.S * ModularGroup.T ^ ((i : ℤ) * t) * ModularGroup.S⁻¹ : SL(2, ℤ))) τ) ∧
      (qCoeff ΦY 1 = 0 ∨ (qCoeff ΦY 1 = -(q : ℂ)⁻¹ ∧ ¬ q ∣ M₂)) := by
    by_cases hqM₂ : q ∣ M₂
    · refine ⟨0, fun τ => ?_, Or.inl (qCoeff_zero 1)⟩
      have hY0 : (⇑Y : ℍ → ℂ) = 0 := funext fun τ => by
        rw [hYfun, hc₂def, ite_eq_left hqM₂, zero_mul]; rfl
      rw [hY0]
      simp
    · have hc₂ : c₂ = ε₂ (q : ZMod M₂) * (q : ℂ) ^ (k - 1) := by rw [hc₂def, ite_eq_right hqM₂]
      by_cases hB : M₂ * q ^ 2 ∣ t
      · obtain ⟨X2t, hX2tfun, hX2tcoef, -⟩ := CuspForm.exists_degeneracy_gamma1_hasNebentypus
          (k := k) (N := t) (d := q ^ 2) hB g₂
        have hYeq : (⇑Y : ℍ → ℂ) = ⇑(c₂ • X2t) := funext fun τ => by
          rw [hYfun, smul_apply, smul_eq_mul, hX2tfun]
        obtain ⟨w, hw⟩ := hB
        refine ⟨(q : ℂ) • (c₂ • X2t), fun τ => ?_, Or.inl ?_⟩
        · rw [hYeq]
          have hterm : ∀ i : ℕ, (⇑(c₂ • X2t) : ℍ → ℂ) ∣[k]
              (ModularGroup.S * ModularGroup.T ^ ((i : ℤ) * t) * ModularGroup.S⁻¹ : SL(2, ℤ))
                = ⇑(c₂ • X2t) := by
            intro i
            have : ((i : ℤ) * t : ℤ) = (t : ℤ) * i := by ring
            rw [this, slash_beta_level]
          simp_rw [hterm]
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, smul_apply, smul_eq_mul]
        · rw [qCoeff_smul, qCoeff_smul, hX2tcoef, ite_eq_right, mul_zero, mul_zero]
          intro h
          exact hq1.ne' (Nat.dvd_one.mp ((dvd_pow_self q two_ne_zero).trans h))
      ·
        have hqM₂t : q * M₂ ∣ t :=
          Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqM₂) hqt hM₂t
        obtain ⟨u, hu⟩ := hqM₂t
        have hqu : ¬ q ∣ u := by
          rintro ⟨w, hw⟩; apply hB; exact ⟨w, by rw [hu, hw]; ring⟩
        obtain ⟨Xt, hXtfun, hXtcoef, -⟩ := CuspForm.exists_degeneracy_gamma1_hasNebentypus
          (k := k) (N := t) (d := q) ⟨u, by rw [hu]; ring⟩ g₂
        have : NeZero (q * M₂) := ⟨mul_ne_zero hq0 hM₂0⟩
        obtain ⟨XqM, hXqMfun, -, -⟩ := CuspForm.exists_degeneracy_gamma1_hasNebentypus
          (k := k) (N := q * M₂) (d := q) ⟨1, by ring⟩ g₂
        refine ⟨c₂ • (((q : ℂ) ^ (1 - k) * conj b) • Xt
            - (conj (ε₂ (q : ZMod M₂)) * (q : ℂ) ^ (-k)) • G₂t), fun τ => ?_, Or.inr ⟨?_, hqM₂⟩⟩
        · rw [smul_apply, smul_eq_mul, sub_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul,
            hXtfun, hG₂tval]
          have hYeq : (⇑Y : ℍ → ℂ) = c₂ • fun σ => g₂ (heckeDiagMatrix (q ^ 2) • σ) := by
            funext σ; rw [hYfun, Pi.smul_apply, smul_eq_mul]
          rw [hYeq]
          have hsm : ∀ i : ℕ, ((c₂ • fun σ : ℍ => g₂ (heckeDiagMatrix (q ^ 2) • σ)) ∣[k]
              (ModularGroup.S * ModularGroup.T ^ ((i : ℤ) * t) * ModularGroup.S⁻¹ : SL(2, ℤ))) τ
              = c₂ * ((fun σ : ℍ => g₂ (heckeDiagMatrix (q ^ 2) • σ)) ∣[k]
                (ModularGroup.S * ModularGroup.T ^ ((i : ℤ) * t) * ModularGroup.S⁻¹ : SL(2, ℤ))) τ := by
            intro i; rw [ModularForm.SL_smul_slash]; rfl
          simp_rw [hsm]
          rw [← Finset.mul_sum]
          congr 1

          have hq20 : q ^ 2 ≠ 0 := pow_ne_zero 2 hq0
          have hpt : ∀ σ : ℍ, heckeDiagMatrix (q ^ 2) • σ = heckeDiagMatrix q • (heckeDiagMatrix q • σ) := by
            intro σ; apply UpperHalfPlane.ext
            rw [coe_heckeDiagMatrix_smul hq20, coe_heckeDiagMatrix_smul hq0,
              coe_heckeDiagMatrix_smul hq0]; push_cast; ring
          have hterm : ∀ i : ℕ,
              ((fun σ : ℍ => g₂ (heckeDiagMatrix (q ^ 2) • σ)) ∣[k]
                (ModularGroup.S * ModularGroup.T ^ ((i : ℤ) * t) * ModularGroup.S⁻¹ : SL(2, ℤ))) τ
              = ((fun σ : ℍ => g₂ (heckeDiagMatrix q • σ)) ∣[k] (ModularGroup.S *
                  ModularGroup.T ^ (((i * u : ℕ) : ℤ) * M₂) * ModularGroup.S⁻¹ :
                    SL(2, ℤ))) (heckeDiagMatrix q • τ) := by
            intro i
            have h := slash_beta_comp_apply (k := k) (fun σ : ℍ => g₂ (heckeDiagMatrix q • σ)) hq0
              ((i : ℤ) * t) (((i * u : ℕ) : ℤ) * M₂) (by rw [hu]; push_cast; ring) τ
            simp only [hpt] at h ⊢
            exact h
          simp_rw [hterm]
          have hXqMeq : (fun σ : ℍ => g₂ (heckeDiagMatrix q • σ)) = ⇑XqM := (funext hXqMfun).symm
          have hper : ∀ y r : ℕ,
              ((fun σ : ℍ => g₂ (heckeDiagMatrix q • σ)) ∣[k] (ModularGroup.S *
                ModularGroup.T ^ (((y + q * r : ℕ) : ℤ) * M₂) * ModularGroup.S⁻¹ :
                  SL(2, ℤ))) (heckeDiagMatrix q • τ)
              = ((fun σ : ℍ => g₂ (heckeDiagMatrix q • σ)) ∣[k] (ModularGroup.S *
                ModularGroup.T ^ ((y : ℤ) * M₂) * ModularGroup.S⁻¹ : SL(2, ℤ)))
                  (heckeDiagMatrix q • τ) := by
            intro y r
            have : (((y + q * r : ℕ) : ℤ) * M₂ : ℤ) = (y : ℤ) * M₂ + ((q * M₂ : ℕ) : ℤ) * r := by
              push_cast; ring
            rw [this, hXqMeq, slash_beta_add_level]
          rw [sum_range_reindex hq (fun x => ((fun σ : ℍ => g₂ (heckeDiagMatrix q • σ)) ∣[k]
            (ModularGroup.S * ModularGroup.T ^ ((x : ℤ) * M₂) * ModularGroup.S⁻¹ : SL(2, ℤ)))
              (heckeDiagMatrix q • τ)) hper hqu,
            CuspForm.IsPrimitiveForm.sum_slash_S_mul_T_zpow_mul_S_inv_comp_heckeDiagMatrix_apply_eq_of_not_dvd
              M₂ k ε₂ g₂ h₂ hq hqM₂, heckeMatrix_smul_heckeDiagMatrix_smul hq0]
        · rw [qCoeff_smul, qCoeff_sub, qCoeff_smul, qCoeff_smul, hXtcoef, hG₂tc,
            ite_eq_right (fun h => hq1.ne' (Nat.dvd_one.mp h)), h₂.isEigenformWith.qCoeff_one, hc₂]
          have hunit : ε₂ (q : ZMod M₂) * conj (ε₂ (q : ZMod M₂)) = 1 := by
            have hu : IsUnit (q : ZMod M₂) :=
              (ZMod.isUnit_iff_coprime q M₂).mpr ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqM₂)
            have hn : ‖ε₂ (q : ZMod M₂)‖ = 1 := by
              rw [← hu.unit_spec]; exact ε₂.unit_norm_eq_one hu.unit
            rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; norm_num
          have hzp : (q : ℂ) ^ (k - 1) * (q : ℂ) ^ (-k) = (q : ℂ)⁻¹ := by
            rw [← zpow_add₀ hqC, show (k - 1 + -k : ℤ) = -1 by ring, zpow_neg_one]
          rw [mul_zero, zero_sub]
          calc ε₂ (q : ZMod M₂) * (q : ℂ) ^ (k - 1) *
                -((starRingEnd ℂ) (ε₂ (q : ZMod M₂)) * (q : ℂ) ^ (-k) * 1)
              = -(ε₂ (q : ZMod M₂) * (starRingEnd ℂ) (ε₂ (q : ZMod M₂))) *
                  ((q : ℂ) ^ (k - 1) * (q : ℂ) ^ (-k)) := by ring
            _ = -(q : ℂ)⁻¹ := by rw [hunit, hzp]; ring

  set Φ : CuspForm (Γ₁ℝ t) k := b • ΦX - (q : ℂ) • G₂t - ΦY with hΦdef
  have hΦfun : ∀ τ : ℍ, Φ τ = ∑ i ∈ Finset.range q, ((⇑E : ℍ → ℂ) ∣[k]
      (ModularGroup.S * ModularGroup.T ^ ((i : ℤ) * t) * ModularGroup.S⁻¹ : SL(2, ℤ))) τ := by
    intro τ
    rw [hΦdef, sub_apply, sub_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul, hΦXfun,
      hΦYfun, ← hTb τ, hEdef]
    have hcoe : (⇑(G₁ - G₂ + b • X - Y) : ℍ → ℂ) = ⇑G₁ - ⇑G₂ + b • ⇑X - ⇑Y := by
      rw [FunLike.coe_sub, FunLike.coe_add, FunLike.coe_sub, FunLike.coe_smul]
    rw [hcoe]
    simp only [SlashAction.add_slash, sub_eq_add_neg, SlashAction.neg_slash,
      ModularForm.SL_smul_slash, Pi.add_apply, Pi.neg_apply, Pi.smul_apply,
      smul_eq_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
    rw [← Finset.sum_apply, ← Finset.sum_apply, ← Finset.sum_apply, ← Finset.sum_apply]
    rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_apply, Finset.sum_apply, hTa τ]
    ring
  have hΦ1 : qCoeff Φ 1 = b * qCoeff ΦX 1 - q - qCoeff ΦY 1 := by
    rw [hΦdef, qCoeff_sub, qCoeff_sub, qCoeff_smul, qCoeff_smul, hG₂tc,
      h₂.isEigenformWith.qCoeff_one, mul_one]

  have hΦ1ne : qCoeff Φ 1 ≠ 0 := by
    rw [hΦ1]
    have hqR : (1 : ℝ) < q := by exact_mod_cast hq1
    rcases hΦX1 with hX0 | ⟨hX1, hqM₂⟩
    · rw [hX0, mul_zero, zero_sub]
      rcases hΦY1 with hY0 | ⟨hY1, -⟩
      · rw [hY0, sub_zero, neg_ne_zero]; exact hqC
      · rw [hY1]
        intro h
        have h' : (q : ℂ)⁻¹ = q := by linear_combination h
        have : (q : ℂ) * q = 1 := by
          nth_rewrite 2 [← h']; exact mul_inv_cancel₀ hqC
        have h2 : (q : ℝ) * q = 1 := by exact_mod_cast this
        nlinarith
    ·
      have hY0 : qCoeff ΦY 1 = 0 := by
        rcases hΦY1 with h | ⟨-, h⟩
        · exact h
        · exact (h hqM₂).elim
      rw [hY0, sub_zero, hX1]
      have hbb : b * conj b = ((‖b‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      have hg₂0 : g₂ ≠ 0 := by
        intro h0
        have h1 := h₂.isEigenformWith.qCoeff_one
        rw [h0, FunLike.coe_zero, qCoeff_zero_fun] at h1
        exact zero_ne_one h1
      by_cases hfac : ε₂.FactorsThrough (M₂ / q)
      · obtain ⟨hdvd, χ, hχ⟩ := hfac
        have h₂' : CuspForm.IsPrimitiveForm
            (DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd hqM₂) χ) g₂ := by
          rw [hχ] at h₂; exact h₂
        by_cases hq2 : q ∣ M₂ / q
        ·
          have hb0 : b = 0 :=
            CuspForm.IsPrimitiveForm.qCoeff_eq_zero_of_dvd_div M₂ k hq hqM₂ hq2 χ g₂ h₂'
          rw [hb0, zero_mul, zero_sub, neg_ne_zero]; exact hqC
        ·
          have hq2' : ¬ q ^ 2 ∣ M₂ := by
            intro h; apply hq2
            exact Nat.dvd_div_of_mul_dvd (by rw [← pow_two]; exact h)
          have hnorm := CuspForm.norm_qCoeff_sq_eq_pow_of_isPrimitiveForm_of_not_sq_dvd M₂ k hq hqM₂
            hq2' χ g₂ h₂'
          have hval : b * ((q : ℂ) ^ (1 - k) * conj b) = (q : ℂ)⁻¹ := by
            rw [mul_left_comm, hbb, hnorm]
            push_cast
            rw [← zpow_add₀ hqC, show (1 - k + (k - 2) : ℤ) = -1 by ring, zpow_neg_one]
          rw [hval]
          intro h
          have h' : (q : ℂ)⁻¹ = q := by linear_combination h
          have : (q : ℂ) * q = 1 := by
            nth_rewrite 2 [← h']; exact mul_inv_cancel₀ hqC
          have h2 : (q : ℝ) * q = 1 := by exact_mod_cast this
          nlinarith
      ·
        have hnorm := CuspForm.norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough M₂ k ε₂ hq
          hqM₂ hfac g₂ hg₂0 h₂.isEigenformWith.hasNebentypus b
          (h₂.isEigenformWith.hecke_of_dvd hq hqM₂)
        have hval : b * ((q : ℂ) ^ (1 - k) * conj b) = 1 := by
          rw [mul_left_comm, hbb, hnorm]
          push_cast
          rw [← zpow_add₀ hqC, show (1 - k + (k - 1) : ℤ) = 0 by ring, zpow_zero]
        rw [hval]
        intro h
        have : (q : ℂ) = 1 := by linear_combination -h
        have h2 : (q : ℕ) = 1 := by exact_mod_cast this
        exact hq1.ne' h2

  have hΦ0 : qCoeff Φ 1 = 0 :=
    CuspForm.HasNebentypus.qCoeff_eq_zero_of_coprime_of_apply_eq_sum_slash hq0 hqt εt E hEneb
      hK0 (Nat.coprime_comm.mp hqK) hEzero Φ hΦfun 1 (Nat.coprime_one_left K)
  exact hΦ1ne hΦ0

end Main

end LiCaseOne

theorem CuspForm.IsPrimitiveForm.pow_dvd_of_pow_dvd_of_sq_dvd_of_factorsThrough_of_forall_coprime_qCoeff_eq
    {M₁ M₂ : ℕ} [NeZero M₁] [NeZero M₂] {k : ℤ}
    {ε₁ : DirichletCharacter ℂ M₁} {ε₂ : DirichletCharacter ℂ M₂}
    {g₁ : CuspForm (CongruenceSubgroup.Gamma1 M₁) k}
    {g₂ : CuspForm (CongruenceSubgroup.Gamma1 M₂) k}
    (h₁ : CuspForm.IsPrimitiveForm ε₁ g₁) (h₂ : CuspForm.IsPrimitiveForm ε₂ g₂)
    (ha : ∀ n : ℕ, Nat.Coprime n M₁ → Nat.Coprime n M₂ →
      ModularFormClass.qCoeff g₁ n = ModularFormClass.qCoeff g₂ n)
    (hε : ∀ n : ℕ, Nat.Coprime n M₁ → Nat.Coprime n M₂ → ε₁ (n : ZMod M₁) = ε₂ (n : ZMod M₂))
    {q : ℕ} (hq : q.Prime) (hqM : q ^ 2 ∣ M₁) (hε₁ : ε₁.FactorsThrough (M₁ / q))
    (j : ℕ) (hj : q ^ j ∣ M₁) : q ^ j ∣ M₂ := by
  exact LiCaseOne.main h₁ h₂ ha hε hq hqM hε₁ j hj

open CongruenceSubgroup ModularFormClass UpperHalfPlane Function
open scoped MatrixGroups


namespace SMOGamma1

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem exists_coeff_restrict {K V P ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : P → V →ₗ[K] V) (v : ι → V) (β : ι → P → K) (α : P → K) (s : Finset ι) :
    ∀ c : ι → K,
      (∀ i ∈ s, ∀ p, T p (v i) = β i p • v i) →
      (∀ p, T p (∑ i ∈ s, c i • v i) = α p • ∑ i ∈ s, c i • v i) →
      ∃ c' : ι → K, (∀ i ∈ s, c' i ≠ 0 → β i = α) ∧
        ∑ i ∈ s, c i • v i = ∑ i ∈ s, c' i • v i := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
    intro c hv hw
    by_cases hall : ∀ i ∈ s, c i ≠ 0 → β i = α
    · exact ⟨c, hall, rfl⟩
    push Not at hall
    obtain ⟨j, hj, -, hβj⟩ := hall
    obtain ⟨p₀, hp₀⟩ : ∃ p₀, β j p₀ ≠ α p₀ := by
      by_contra hcon
      push Not at hcon
      exact hβj (funext hcon)
    set w : V := ∑ i ∈ s, c i • v i with hwdef
    have hne : α p₀ - β j p₀ ≠ 0 := sub_ne_zero.2 (Ne.symm hp₀)
    set c₁ : ι → K := fun i => (α p₀ - β j p₀)⁻¹ * (c i * (β i p₀ - β j p₀)) with hc₁
    have h2 : ∑ i ∈ s, (c i * (β i p₀ - β j p₀)) • v i = T p₀ w - β j p₀ • w := by
      rw [hwdef, map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [map_smul, hv i hi p₀, smul_smul, smul_smul, ← sub_smul]
      congr 1
      ring
    have hsum : ∑ i ∈ s, c₁ i • v i = w := by
      have h3 : ∑ i ∈ s, c₁ i • v i =
          (α p₀ - β j p₀)⁻¹ • ∑ i ∈ s, (c i * (β i p₀ - β j p₀)) • v i := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul]
      rw [h3, h2, hw p₀, ← sub_smul, smul_smul, inv_mul_cancel₀ hne, one_smul]
    have hc₁j : c₁ j = 0 := by simp [hc₁]
    have herase : ∑ i ∈ s.erase j, c₁ i • v i = ∑ i ∈ s, c₁ i • v i :=
      Finset.sum_erase _ (by rw [hc₁j, zero_smul])
    have hv' : ∀ i ∈ s.erase j, ∀ p, T p (v i) = β i p • v i :=
      fun i hi p => hv i (Finset.mem_of_mem_erase hi) p
    have hw' : ∀ p, T p (∑ i ∈ s.erase j, c₁ i • v i) = α p • ∑ i ∈ s.erase j, c₁ i • v i := by
      intro p
      rw [herase, hsum]
      exact hw p
    obtain ⟨c', h2', h3⟩ := ih (s.erase j) (Finset.erase_ssubset hj) c₁ hv' hw'
    refine ⟨fun i => if i = j then 0 else c' i, ?_, ?_⟩
    · intro i hi hne'
      change (if i = j then 0 else c' i) ≠ 0 at hne'
      by_cases hij : i = j
      · rw [ite_eq_left hij] at hne'
        exact absurd rfl hne'
      · rw [ite_eq_right hij] at hne'
        exact h2' i (Finset.mem_erase.2 ⟨hij, hi⟩) hne'
    · have hjz : (fun i => (if i = j then 0 else c' i) • v i) j = 0 := by
        show (if j = j then 0 else c' j) • v j = 0
        rw [ite_eq_left rfl, zero_smul]
      rw [← hsum, ← herase, h3, ← Finset.sum_erase s hjz]
      refine Finset.sum_congr rfl fun i hi => ?_
      show c' i • v i = (if i = j then 0 else c' i) • v i
      rw [ite_eq_right (Finset.ne_of_mem_erase hi)]

def heckeSeq (k : ℤ) (e : ℕ → ℂ) (p : ℕ) : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) where
  toFun s := fun n => s (p * n) + e p * (p : ℂ) ^ (k - 1) * (if p ∣ n then s (n / p) else 0)
  map_add' s t := by
    funext n
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' c s := by
    funext n
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem heckeSeq_apply (k : ℤ) (e : ℕ → ℂ) (p : ℕ) (s : ℕ → ℂ) (n : ℕ) :
    heckeSeq k e p s n = s (p * n) + e p * (p : ℂ) ^ (k - 1) * (if p ∣ n then s (n / p) else 0) := by
  rfl

def stretchSeq (d : ℕ) (b : ℕ → ℂ) : ℕ → ℂ := fun n => if d ∣ n then b (n / d) else 0

theorem stretchSeq_apply (d : ℕ) (b : ℕ → ℂ) (n : ℕ) :
    stretchSeq d b n = if d ∣ n then b (n / d) else 0 := by
  rfl

theorem heckeSeq_stretchSeq {k : ℤ} {e : ℕ → ℂ} {p d : ℕ} (hp0 : p ≠ 0) (hd : d ≠ 0)
    (hpd : Nat.Coprime p d)
    {b : ℕ → ℂ} {lam : ℂ}
    (hb : ∀ m : ℕ, b (p * m) + e p * (p : ℂ) ^ (k - 1) * (if p ∣ m then b (m / p) else 0) = lam * b m) :
    heckeSeq k e p (stretchSeq d b) = lam • stretchSeq d b := by
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  have hppos : 0 < p := Nat.pos_of_ne_zero hp0
  funext n
  simp only [heckeSeq_apply, Pi.smul_apply, smul_eq_mul, stretchSeq_apply]
  by_cases hdn : d ∣ n
  · obtain ⟨m, rfl⟩ := hdn
    have h1 : d ∣ p * (d * m) := ⟨p * m, by ring⟩
    have h2 : p * (d * m) / d = p * m := by
      rw [show p * (d * m) = d * (p * m) by ring, Nat.mul_div_cancel_left _ hdpos]
    have h3 : d * m / d = m := Nat.mul_div_cancel_left _ hdpos
    rw [ite_eq_left h1, h2, ite_eq_left (dvd_mul_right d m), h3]
    by_cases hpm : p ∣ m
    · obtain ⟨r, rfl⟩ := hpm
      have h4 : p ∣ d * (p * r) := ⟨d * r, by ring⟩
      have h5 : d * (p * r) / p = d * r := by
        rw [show d * (p * r) = p * (d * r) by ring, Nat.mul_div_cancel_left _ hppos]
      rw [ite_eq_left h4, h5, ite_eq_left (dvd_mul_right d r), Nat.mul_div_cancel_left _ hdpos]
      have := hb (p * r)
      rw [ite_eq_left (dvd_mul_right p r), Nat.mul_div_cancel_left _ hppos] at this
      exact this
    · have h4 : ¬ p ∣ d * m := fun h => hpm (hpd.dvd_of_dvd_mul_left h)
      rw [ite_eq_right h4]
      have := hb m
      rw [ite_eq_right hpm] at this
      exact this
  · have h1 : ¬ d ∣ p * n := fun h => hdn ((Nat.Coprime.symm hpd).dvd_of_dvd_mul_left h)
    rw [ite_eq_right h1, ite_eq_right hdn, mul_zero]
    have hmid : (if p ∣ n then (if d ∣ n / p then b (n / p / d) else 0) else 0) = 0 := by
      split_ifs with hpn hdnp
      · exact absurd (dvd_trans hdnp (Nat.div_dvd_of_dvd hpn)) hdn
      · rfl
      · rfl
    rw [hmid, mul_zero, add_zero]

def copSeq (L' : ℕ) (s : ℕ → ℂ) : ℕ → ℂ := fun n => if Nat.Coprime n L' then s n else 0

theorem copSeq_apply (L' : ℕ) (s : ℕ → ℂ) (n : ℕ) :
    copSeq L' s n = if Nat.Coprime n L' then s n else 0 := by
  rfl

theorem copSeq_smul (L' : ℕ) (c : ℂ) (s : ℕ → ℂ) : copSeq L' (c • s) = c • copSeq L' s := by
  funext n
  simp only [copSeq_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

theorem heckeSeq_copSeq {k : ℤ} {e : ℕ → ℂ} {p L' : ℕ} (hp0 : p ≠ 0) (hp : Nat.Coprime p L')
    (s : ℕ → ℂ) : heckeSeq k e p (copSeq L' s) = copSeq L' (heckeSeq k e p s) := by
  have hppos : 0 < p := Nat.pos_of_ne_zero hp0
  funext n
  simp only [heckeSeq_apply, copSeq_apply]
  by_cases hn : Nat.Coprime n L'
  · rw [ite_eq_left hn, ite_eq_left (Nat.Coprime.mul_left hp hn)]
    by_cases hpn : p ∣ n
    · obtain ⟨r, rfl⟩ := hpn
      have hr : Nat.Coprime r L' := Nat.Coprime.coprime_dvd_left (Dvd.intro_left p rfl) hn
      rw [ite_eq_left (dvd_mul_right p r), ite_eq_left (dvd_mul_right p r),
        Nat.mul_div_cancel_left _ hppos, ite_eq_left hr]
    · rw [ite_eq_right hpn, ite_eq_right hpn]
  · rw [ite_eq_right hn]
    have h1 : ¬ Nat.Coprime (p * n) L' := fun h =>
      hn (Nat.Coprime.coprime_dvd_left (Dvd.intro_left p rfl) h)
    rw [ite_eq_right h1]
    have hmid : (if p ∣ n then (if Nat.Coprime (n / p) L' then s (n / p) else 0) else 0) = 0 := by
      split_ifs with hpn hcop
      · exfalso
        obtain ⟨r, rfl⟩ := hpn
        rw [Nat.mul_div_cancel_left _ hppos] at hcop
        exact hn (Nat.Coprime.mul_left hp hcop)
      · rfl
      · rfl
    rw [hmid, mul_zero, add_zero]

theorem changeLevel_apply_natCast {M N : ℕ} [NeZero N] (hMN : M ∣ N) (εM : DirichletCharacter ℂ M)
    (ε : DirichletCharacter ℂ N) (h : DirichletCharacter.changeLevel hMN εM = ε)
    (p : ℕ) (hp : Nat.Coprime p N) :
    εM (p : ZMod M) = ε (p : ZMod N) := by
  have : NeZero M := ⟨fun h0 => by
    subst h0
    exact (NeZero.ne N) (Nat.eq_zero_of_zero_dvd hMN)⟩
  set u : (ZMod N)ˣ := ZMod.unitOfCoprime p hp with hu
  have hu' : (u : ZMod N) = (p : ZMod N) := ZMod.coe_unitOfCoprime p hp
  rw [← h, ← hu', DirichletCharacter.changeLevel_eq_cast_of_dvd εM hMN u, hu',
    ZMod.cast_natCast hMN]

section QCoeff

variable {L : ℕ} {k : ℤ}

theorem one_mem_strictPeriods (L : ℕ) : (1 : ℝ) ∈ (Γ₁ℝ L).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]
  exact AddSubgroup.mem_zmultiples _

theorem periodic (f : CuspForm (Γ₁ℝ L) k) : Periodic (⇑f ∘ ofComplex) 1 := by
  exact SlashInvariantFormClass.periodic_comp_ofComplex f (one_mem_strictPeriods L)

theorem bdd (f : CuspForm (Γ₁ℝ L) k) : IsBoundedAtImInfty (⇑f) := by
  have : Fact (IsCusp OnePoint.infty (Γ₁ℝ L)) :=
    ⟨(Γ₁ℝ L).isCusp_of_mem_strictPeriods one_pos (one_mem_strictPeriods L)⟩
  exact ModularFormClass.bdd_at_infty f

theorem analytic (f : CuspForm (Γ₁ℝ L) k) : AnalyticAt ℂ (cuspFunction 1 (⇑f)) 0 := by
  exact analyticAt_cuspFunction_zero one_pos (periodic f) f.holo' (bdd f)

theorem qCoeff_zero_fun (n : ℕ) : qCoeff (0 : ℍ → ℂ) n = 0 := by
  simp [qCoeff, UpperHalfPlane.qExpansion_zero]

theorem qCoeff_zero (n : ℕ) : qCoeff (⇑(0 : CuspForm (Γ₁ℝ L) k)) n = 0 := by
  simp [qCoeff, UpperHalfPlane.qExpansion_zero]

theorem qCoeff_smul (c : ℂ) (f : CuspForm (Γ₁ℝ L) k) (n : ℕ) :
    qCoeff (⇑(c • f)) n = c * qCoeff (⇑f) n := by
  rw [qCoeff, qCoeff, FunLike.coe_smul, qExpansion_smul (analytic f), map_smul, smul_eq_mul]

theorem qCoeff_sub (f g : CuspForm (Γ₁ℝ L) k) (n : ℕ) :
    qCoeff (⇑(f - g)) n = qCoeff (⇑f) n - qCoeff (⇑g) n := by
  rw [qCoeff, qCoeff, qCoeff, FunLike.coe_sub, qExpansion_sub (analytic f) (analytic g), map_sub]

end QCoeff

theorem apply_eq_zero_of_good {k : ℤ} (a : ℕ → ℂ) (e lam : ℕ → ℂ) (good : ℕ → Prop)
    (h1 : a 1 = 0)
    (heig : ∀ q : ℕ, q.Prime → good q → ∀ m : ℕ,
      a (q * m) + e q * (q : ℂ) ^ (k - 1) * (if q ∣ m then a (m / q) else 0) = lam q * a m) :
    ∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → q ∣ n → good q) → a n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn0 hgood
    by_cases hn1 : n = 1
    · rw [hn1]; exact h1
    · set q := n.minFac with hq
      have hqp : q.Prime := Nat.minFac_prime hn1
      have hqn : q ∣ n := Nat.minFac_dvd n
      obtain ⟨m, hm⟩ := hqn
      have hm0 : m ≠ 0 := by rintro rfl; exact hn0 (by rw [hm, mul_zero])
      have hmlt : m < n := by
        rw [hm]
        exact lt_mul_left (Nat.pos_of_ne_zero hm0) hqp.one_lt
      have hgood_m : ∀ r : ℕ, r.Prime → r ∣ m → good r :=
        fun r hr hrm => hgood r hr (hm ▸ dvd_mul_of_dvd_right hrm q)
      have ham : a m = 0 := ih m hmlt hm0 hgood_m
      have hrel := heig q hqp (hgood q hqp ⟨m, hm⟩) m
      rw [ham, mul_zero] at hrel
      have hmid : (if q ∣ m then a (m / q) else 0) = 0 := by
        split_ifs with hqm
        · obtain ⟨r, hr⟩ := hqm
          have hr0 : r ≠ 0 := by rintro rfl; exact hm0 (by rw [hr, mul_zero])
          have hrlt : r < n := by
            calc r < m := by rw [hr]; exact lt_mul_left (Nat.pos_of_ne_zero hr0) hqp.one_lt
              _ < n := hmlt
          have hdiv : m / q = r := by rw [hr, Nat.mul_div_cancel_left _ hqp.pos]
          rw [hdiv]
          exact ih r hrlt hr0 (fun t ht htr => hgood_m t ht (hr ▸ dvd_mul_of_dvd_right htr q))
        · rfl
      rw [hmid, mul_zero, add_zero] at hrel
      rw [hm]
      exact hrel

theorem changeLevel_eq_of_forall_prime_notMem {M₁ M₂ N : ℕ} [NeZero N] (h₁ : M₁ ∣ N) (h₂ : M₂ ∣ N)
    (ε₁ : DirichletCharacter ℂ M₁) (ε₂ : DirichletCharacter ℂ M₂) (S : Finset ℕ)
    (hε : ∀ p : ℕ, p.Prime → p ∉ S → ε₁ (p : ZMod M₁) = ε₂ (p : ZMod M₂)) :
    DirichletCharacter.changeLevel h₁ ε₁ = DirichletCharacter.changeLevel h₂ ε₂ := by
  apply MulChar.ext'
  intro a
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd ε₁ h₁ u,
      DirichletCharacter.changeLevel_eq_cast_of_dvd ε₂ h₂ u]
    obtain ⟨p, hpgt, hp, hpu⟩ :=
      Nat.forall_exists_prime_gt_and_eq_mod (Units.isUnit u) (S.sup id)
    have hpS : p ∉ S := by
      intro hpS
      have : p ≤ S.sup id := Finset.le_sup (f := id) hpS
      omega
    rw [← hpu, ZMod.cast_natCast h₁, ZMod.cast_natCast h₂]
    exact hε p hp hpS
  · rw [MulChar.map_nonunit _ ha, MulChar.map_nonunit _ ha]

theorem eq_of_forall_prime_notMem {M : ℕ} [NeZero M]
    (ε₁ ε₂ : DirichletCharacter ℂ M) (S : Finset ℕ)
    (hε : ∀ p : ℕ, p.Prime → p ∉ S → ε₁ (p : ZMod M) = ε₂ (p : ZMod M)) : ε₁ = ε₂ := by
  have h := changeLevel_eq_of_forall_prime_notMem (dvd_refl M) (dvd_refl M) ε₁ ε₂ S hε
  rwa [DirichletCharacter.changeLevel_self, DirichletCharacter.changeLevel_self] at h

theorem ne_zero_of_isEigenformWith {M : ℕ} {k : ℤ} {ε : DirichletCharacter ℂ M}
    {g : CuspForm (Γ₁ℝ M) k} (hg : CuspForm.IsEigenformWith ε g) : g ≠ 0 := by
  intro h0
  have h1 := hg.qCoeff_one
  rw [h0, qCoeff_zero] at h1
  exact zero_ne_one h1

theorem qCoeff_eq_of_level_eq
    {M : ℕ} [NeZero M] {k : ℤ}
    {ε₁ ε₂ : DirichletCharacter ℂ M}
    {g₁ g₂ : CuspForm (Γ₁ℝ M) k}
    (h₁ : CuspForm.IsPrimitiveForm ε₁ g₁) (h₂ : CuspForm.IsPrimitiveForm ε₂ g₂) (S : Finset ℕ)
    (ha : ∀ p : ℕ, p.Prime → p ∉ S → qCoeff g₁ p = qCoeff g₂ p)
    (hε : ∀ p : ℕ, p.Prime → p ∉ S → ε₁ (p : ZMod M) = ε₂ (p : ZMod M)) :
    ∀ n : ℕ, qCoeff g₁ n = qCoeff g₂ n := by
  have heq : ε₁ = ε₂ := eq_of_forall_prime_notMem ε₁ ε₂ S hε
  subst heq
  have hmo := CuspForm.eq_smul_of_isPrimitiveForm_of_qCoeff_hecke_eigen M k ε₁ g₁ h₁ g₂
    h₂.1.hasNebentypus S (fun p hp hpS hpM n => by
      rw [ha p hp hpS]
      exact h₂.1.hecke_of_not_dvd hp hpM n)
  rw [h₂.1.qCoeff_one, one_smul] at hmo
  intro n
  rw [hmo]

def LevelIH (k : ℤ) (L : ℕ) : Prop :=
  ∀ (N₁ N₂ : ℕ) (_ : NeZero N₁) (_ : NeZero N₂)
    (η₁ : DirichletCharacter ℂ N₁) (η₂ : DirichletCharacter ℂ N₂)
    (f₁ : CuspForm (Γ₁ℝ N₁) k) (f₂ : CuspForm (Γ₁ℝ N₂) k),
    CuspForm.IsPrimitiveForm η₁ f₁ → CuspForm.IsPrimitiveForm η₂ f₂ →
    ∀ S : Finset ℕ,
      (∀ p : ℕ, p.Prime → p ∉ S → qCoeff f₁ p = qCoeff f₂ p) →
      (∀ p : ℕ, p.Prime → p ∉ S → η₁ (p : ZMod N₁) = η₂ (p : ZMod N₂)) →
      Nat.lcm N₁ N₂ < L → N₁ = N₂

theorem qCoeff_eq_of_levelIH {k : ℤ} {L : ℕ} [NeZero L] (IH : LevelIH k L)
    {M₂ : ℕ} [NeZero M₂] {ε₂ : DirichletCharacter ℂ M₂} {g₂ : CuspForm (Γ₁ℝ M₂) k}
    (h₂ : CuspForm.IsPrimitiveForm ε₂ g₂) (hM₂L : M₂ ∣ L)
    (ε : DirichletCharacter ℂ L) (hε₂ : DirichletCharacter.changeLevel hM₂L ε₂ = ε)
    (S : Finset ℕ) (lam : ℕ → ℂ)
    (hlam : ∀ p : ℕ, p.Prime → p ∉ S → ¬ p ∣ L → qCoeff g₂ p = lam p)
    {N : ℕ} [NeZero N] {η : DirichletCharacter ℂ N} {h : CuspForm (Γ₁ℝ N) k}
    (hh : CuspForm.IsPrimitiveForm η h) (hNL : N ∣ L)
    (hη : DirichletCharacter.changeLevel hNL η = ε)
    (hpk : ∀ p : ℕ, p.Prime → p ∉ S → ¬ p ∣ L → qCoeff h p = lam p)
    (hlcm : Nat.lcm N M₂ < L) :
    N = M₂ ∧ ∀ r : ℕ, qCoeff h r = qCoeff g₂ r := by
  classical
  have hL0 : L ≠ 0 := NeZero.ne L
  have hcoef : ∀ p : ℕ, p.Prime → p ∉ S ∪ L.primeFactors → qCoeff h p = qCoeff g₂ p := by
    intro p hp hpS
    rw [Finset.mem_union, not_or] at hpS
    have hpL : ¬ p ∣ L := fun hd => hpS.2 (Nat.mem_primeFactors.2 ⟨hp, hd, hL0⟩)
    rw [hpk p hp hpS.1 hpL, hlam p hp hpS.1 hpL]
  have hchar : ∀ p : ℕ, p.Prime → p ∉ S ∪ L.primeFactors → η (p : ZMod N) = ε₂ (p : ZMod M₂) := by
    intro p hp hpS
    rw [Finset.mem_union, not_or] at hpS
    have hpL : ¬ p ∣ L := fun hd => hpS.2 (Nat.mem_primeFactors.2 ⟨hp, hd, hL0⟩)
    have hcop : Nat.Coprime p L := (Nat.Prime.coprime_iff_not_dvd hp).2 hpL
    rw [changeLevel_apply_natCast hNL η ε hη p hcop, changeLevel_apply_natCast hM₂L ε₂ ε hε₂ p hcop]
  have hNM : N = M₂ :=
    IH N M₂ inferInstance inferInstance η ε₂ h g₂ hh h₂ (S ∪ L.primeFactors) hcoef hchar hlcm
  subst hNM
  refine ⟨rfl, ?_⟩
  have hηε : η = ε₂ := DirichletCharacter.changeLevel_injective hNL (hη.trans hε₂.symm)
  subst hηε
  exact qCoeff_eq_of_level_eq hh h₂ (S ∪ L.primeFactors) hcoef hchar

theorem tower {k : ℤ} {L : ℕ} [NeZero L] (ε : DirichletCharacter ℂ L)
    (D : CuspForm (Γ₁ℝ L) k) (hD : CuspForm.HasNebentypus ε D)
    (S : Finset ℕ) (lam : ℕ → ℂ)
    (h1 : qCoeff (⇑D) 1 = 0)
    (heig : ∀ p : ℕ, p.Prime → p ∉ S → ¬ p ∣ L → ∀ n : ℕ,
      qCoeff (⇑D) (p * n) + ε (p : ZMod L) * (p : ℂ) ^ (k - 1) *
        (if p ∣ n then qCoeff (⇑D) (n / p) else 0) = lam p * qCoeff (⇑D) n)
    {q : ℕ} (hq : q.Prime) (hqL : q ∣ L) (L' : ℕ) (hL' : L = q ^ (L.factorization q) * L') :
    ∃ (n : ℕ) (d : Fin n → ℕ) (c : Fin n → ℂ) (N : Fin n → ℕ)
      (η : (i : Fin n) → DirichletCharacter ℂ (N i)) (h : (i : Fin n) → CuspForm (Γ₁ℝ (N i)) k),
      (∀ i, c i ≠ 0 →
        N i * d i ∣ L / q ∧ CuspForm.IsPrimitiveForm (η i) (h i) ∧
        (∃ hN : N i ∣ L, DirichletCharacter.changeLevel hN (η i) = ε) ∧
        ∀ p : ℕ, p.Prime → p ∉ S → ¬ p ∣ L → qCoeff (⇑(h i)) p = lam p) ∧
      ∀ m : ℕ, Nat.Coprime m L' →
        qCoeff (⇑D) m = ∑ i, c i * (if q * d i ∣ m then qCoeff (⇑(h i)) (m / (q * d i)) else 0) := by
  classical
  have hL0 : L ≠ 0 := NeZero.ne L
  have hL'L : L' ∣ L := Dvd.intro_left _ hL'.symm
  let echar : ℕ → ℂ := fun n => ε (n : ZMod L)
  let good : ℕ → Prop := fun p => p.Prime ∧ p ∉ S ∧ ¬ p ∣ L

  set K : ℕ := 2 * L * ∏ p ∈ S.filter Nat.Prime, p with hK
  have hK0 : K ≠ 0 := by
    rw [hK]
    refine mul_ne_zero (mul_ne_zero two_ne_zero hL0) ?_
    rw [Finset.prod_ne_zero_iff]
    intro p hp
    exact (Finset.mem_filter.1 hp).2.ne_zero
  have hvan : ∀ m : ℕ, Nat.Coprime m K → qCoeff (⇑D) m = 0 := by
    intro m hm
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [Nat.coprime_zero_left] at hm
      have h2 : 2 ∣ K := ⟨L * ∏ p ∈ S.filter Nat.Prime, p, by rw [hK]; ring⟩
      rw [hm] at h2
      exact absurd (Nat.le_of_dvd one_pos h2) (by norm_num)
    refine apply_eq_zero_of_good (k := k) (fun r => qCoeff (⇑D) r) echar lam good h1
      (fun p hp hg r => heig p hp hg.2.1 hg.2.2 r) m hm0 (fun p hp hpm => ⟨hp, ?_, ?_⟩)
    · intro hpS
      have hpK : p ∣ K := by
        rw [hK]
        exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨hpS, hp⟩)) _
      exact hp.one_lt.ne' ((hm.coprime_dvd_left hpm).eq_one_of_dvd hpK)
    · intro hpL
      have hpK : p ∣ K := by
        rw [hK]
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hpL 2) _
      exact hp.one_lt.ne' ((hm.coprime_dvd_left hpm).eq_one_of_dvd hpK)

  obtain ⟨F, hF, hFcoef⟩ :=
    CuspForm.exists_hasNebentypus_qCoeff_eq_sum_primeFactors_of_forall_coprime_qCoeff_eq_zero
      L k K hK0 ε D hD hvan
  have hqmem : q ∈ L.primeFactors := Nat.mem_primeFactors.2 ⟨hq, hqL, hL0⟩
  have hpL' : ∀ p ∈ L.primeFactors, p ≠ q → p ∣ L' := by
    intro p hp hpq
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpL : p ∣ L := Nat.dvd_of_mem_primeFactors hp
    have hcop : Nat.Coprime p (q ^ L.factorization q) :=
      Nat.Coprime.pow_right _ ((Nat.coprime_primes hpp hq).2 hpq)
    rw [hL'] at hpL
    exact hcop.dvd_of_dvd_mul_left hpL
  have hsingle : ∀ m : ℕ, Nat.Coprime m L' →
      qCoeff (⇑D) m = if q ∣ m then qCoeff (⇑(F q)) (m / q) else 0 := by
    intro m hm
    rw [hFcoef m, Finset.sum_eq_single q]
    · intro p hp hpq
      have hpm : ¬ p ∣ m := fun hd => by
        have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
        exact hpp.one_lt.ne' ((hm.coprime_dvd_left hd).eq_one_of_dvd (hpL' p hp hpq))
      rw [ite_eq_right hpm]
    · intro hnot
      exact absurd hqmem hnot

  rcases hF q hqmem with hFq0 | ⟨εq, hεq, hFqneb⟩
  · refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
      fun i => Fin.elim0 i, fun m hm => ?_⟩
    rw [hsingle m hm, hFq0, Finset.univ_eq_empty, Finset.sum_empty]
    split_ifs
    · exact qCoeff_zero _
    · rfl
  · have hLq0 : L / q ≠ 0 :=
      (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hL0) hqL) hq.pos).ne'
    have : NeZero (L / q) := ⟨hLq0⟩
    have hLqL : L / q ∣ L := Nat.div_dvd_of_dvd hqL
    obtain ⟨n, N, d, hNd, η, h, c, hprim, hsum⟩ :=
      CuspForm.exists_qCoeff_eq_sum_isPrimitiveForm_of_hasNebentypus (L / q) k εq (F q) hFqneb
    have hd0 : ∀ i, d i ≠ 0 := by
      intro i h0
      have := hNd i
      rw [h0, mul_zero] at this
      exact hLq0 (Nat.eq_zero_of_zero_dvd this)
    have hqd0 : ∀ i, q * d i ≠ 0 := fun i => mul_ne_zero hq.ne_zero (hd0 i)
    have hqdL : ∀ i, q * d i ∣ L := by
      intro i
      have hdi : d i ∣ L / q := Dvd.dvd.trans (Dvd.intro_left _ rfl) (hNd i)
      calc q * d i ∣ q * (L / q) := Nat.mul_dvd_mul_left q hdi
        _ = L := Nat.mul_div_cancel' hqL
    have hNL : ∀ i, N i ∣ L := fun i => (dvd_of_mul_right_dvd (hNd i)).trans hLqL
    have hηε : ∀ i, DirichletCharacter.changeLevel (hNL i) (η i) = ε := by
      intro i
      have e1 := DirichletCharacter.changeLevel_trans (η i) (dvd_of_mul_right_dvd (hNd i)) hLqL
      rw [(hprim i).2] at e1
      refine e1.trans ?_
      exact hεq

    have hstretch : ∀ m : ℕ, Nat.Coprime m L' →
        qCoeff (⇑D) m = ∑ i, c i * (if q * d i ∣ m then qCoeff (⇑(h i)) (m / (q * d i)) else 0) := by
      intro m hm
      rw [hsingle m hm]
      by_cases hqm : q ∣ m
      · obtain ⟨r, rfl⟩ := hqm
        rw [ite_eq_left (dvd_mul_right q r), Nat.mul_div_cancel_left _ hq.pos, hsum r]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hdr : d i ∣ r
        · rw [ite_eq_left hdr, ite_eq_left (Nat.mul_dvd_mul_left q hdr),
            Nat.mul_div_mul_left _ _ hq.pos]
        · rw [ite_eq_right hdr,
            ite_eq_right (fun hd => hdr ((Nat.mul_dvd_mul_iff_left hq.pos).1 hd))]
      · rw [ite_eq_right hqm]
        symm
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [ite_eq_right (fun hd => hqm (dvd_trans (Dvd.intro _ rfl) hd)), mul_zero]

    let 𝒯 : ℕ → (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) := fun p => if good p then heckeSeq k echar p else 0
    let v : Fin n → ℕ → ℂ := fun i => copSeq L' (stretchSeq (q * d i) (fun r => qCoeff (⇑(h i)) r))
    let β : Fin n → ℕ → ℂ := fun i p => if good p then qCoeff (⇑(h i)) p else 0
    let α : ℕ → ℂ := fun p => if good p then lam p else 0
    have hgoodL' : ∀ p, good p → Nat.Coprime p L' := fun p hg =>
      (Nat.Prime.coprime_iff_not_dvd hg.1).2 (fun hd => hg.2.2 (hd.trans hL'L))
    have hv : ∀ i ∈ (Finset.univ : Finset (Fin n)), ∀ p, 𝒯 p (v i) = β i p • v i := by
      intro i _ p
      by_cases hg : good p
      · simp only [𝒯, β, ite_eq_left hg]
        have hp := hg.1
        have hpL := hg.2.2
        have hpN : ¬ p ∣ N i := fun hd => hpL (hd.trans (hNL i))
        have hcopqd : Nat.Coprime p (q * d i) :=
          (Nat.Prime.coprime_iff_not_dvd hp).2 (fun hd => hpL (hd.trans (hqdL i)))
        have hcopL : Nat.Coprime p L := (Nat.Prime.coprime_iff_not_dvd hp).2 hpL
        have hst : heckeSeq k echar p (stretchSeq (q * d i) (fun r => qCoeff (⇑(h i)) r)) =
            qCoeff (⇑(h i)) p • stretchSeq (q * d i) (fun r => qCoeff (⇑(h i)) r) :=
          heckeSeq_stretchSeq hp.ne_zero (hqd0 i) hcopqd (fun r => by
            have := (hprim i).1.1.hecke_of_not_dvd hp hpN r
            rw [changeLevel_apply_natCast (hNL i) (η i) ε (hηε i) p hcopL] at this
            exact this)
        show heckeSeq k echar p (copSeq L' _) = _
        rw [heckeSeq_copSeq hp.ne_zero (hgoodL' p hg), hst, copSeq_smul]
      · simp only [𝒯, β, ite_eq_right hg, LinearMap.zero_apply, zero_smul]
    have haeig_fun : ∀ p, good p →
        heckeSeq k echar p (fun r => qCoeff (⇑D) r) = lam p • (fun r => qCoeff (⇑D) r) := by
      intro p hg
      funext r
      rw [heckeSeq_apply, Pi.smul_apply, smul_eq_mul]
      exact heig p hg.1 hg.2.1 hg.2.2 r
    have hw0 : (∑ i ∈ (Finset.univ : Finset (Fin n)), c i • v i) =
        copSeq L' (fun r => qCoeff (⇑D) r) := by
      funext r
      rw [Finset.sum_apply, copSeq_apply]
      by_cases hr : Nat.Coprime r L'
      · rw [ite_eq_left hr, hstretch r hr]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Pi.smul_apply, smul_eq_mul, v, copSeq_apply, stretchSeq_apply, ite_eq_left hr]
      · rw [ite_eq_right hr]
        refine Finset.sum_eq_zero fun i _ => ?_
        simp only [Pi.smul_apply, smul_eq_mul, v, copSeq_apply, ite_eq_right hr, mul_zero]
    have hw : ∀ p, 𝒯 p (∑ i ∈ (Finset.univ : Finset (Fin n)), c i • v i) =
        α p • ∑ i ∈ (Finset.univ : Finset (Fin n)), c i • v i := by
      intro p
      rw [hw0]
      by_cases hg : good p
      · simp only [𝒯, α, ite_eq_left hg]
        rw [heckeSeq_copSeq hg.1.ne_zero (hgoodL' p hg), haeig_fun p hg, copSeq_smul]
      · simp only [𝒯, α, ite_eq_right hg, LinearMap.zero_apply, zero_smul]
    obtain ⟨c', hc'β, hsum'⟩ := exists_coeff_restrict 𝒯 v β α Finset.univ c hv hw
    refine ⟨n, d, c', N, η, h, fun i hi => ⟨hNd i, (hprim i).1, ⟨hNL i, hηε i⟩,
      fun p hp hpS hpL => ?_⟩, fun m hm => ?_⟩
    · have hβ : β i = α := hc'β i (Finset.mem_univ i) hi
      have := congrFun hβ p
      simp only [β, α, ite_eq_left (show good p from ⟨hp, hpS, hpL⟩)] at this
      exact this
    · have := congrFun hsum' m
      rw [hw0, copSeq_apply, ite_eq_left hm] at this
      rw [this, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul, v, copSeq_apply, stretchSeq_apply, ite_eq_left hm]

theorem keyStep {k : ℤ} {L : ℕ} (IH : LevelIH k L)
    {M₁ M₂ : ℕ} [NeZero M₁] [NeZero M₂]
    {ε₁ : DirichletCharacter ℂ M₁} {ε₂ : DirichletCharacter ℂ M₂}
    {g₁ : CuspForm (Γ₁ℝ M₁) k} {g₂ : CuspForm (Γ₁ℝ M₂) k}
    (h₁ : CuspForm.IsPrimitiveForm ε₁ g₁) (h₂ : CuspForm.IsPrimitiveForm ε₂ g₂) (S : Finset ℕ)
    (ha : ∀ p : ℕ, p.Prime → p ∉ S → qCoeff g₁ p = qCoeff g₂ p)
    (hε : ∀ p : ℕ, p.Prime → p ∉ S → ε₁ (p : ZMod M₁) = ε₂ (p : ZMod M₂))
    (hL : Nat.lcm M₁ M₂ = L) {q : ℕ} (hq : q.Prime)
    (hlt : M₂.factorization q < M₁.factorization q) : False := by
  classical
  have hM₁0 : M₁ ≠ 0 := NeZero.ne M₁
  have hM₂0 : M₂ ≠ 0 := NeZero.ne M₂
  have hL0 : L ≠ 0 := hL ▸ Nat.lcm_ne_zero hM₁0 hM₂0
  have : NeZero L := ⟨hL0⟩
  have hM₁L : M₁ ∣ L := hL ▸ Nat.dvd_lcm_left M₁ M₂
  have hM₂L : M₂ ∣ L := hL ▸ Nat.dvd_lcm_right M₁ M₂
  have hLprod : L ∣ M₁ * M₂ := hL ▸ Nat.lcm_dvd_mul M₁ M₂
  set m : ℕ := M₁.factorization q with hm_def
  set e : ℕ := M₂.factorization q with he_def
  have hm1 : 1 ≤ m := by omega
  have hqM₁ : q ∣ M₁ := (hq.dvd_iff_one_le_factorization hM₁0).2 hm1
  have hLfac : L.factorization q = m := by
    rw [← hL, Nat.factorization_lcm hM₁0 hM₂0, Finsupp.sup_apply]
    exact max_eq_left hlt.le
  have hqL : q ∣ L := hqM₁.trans hM₁L

  set L' : ℕ := L / q ^ L.factorization q with hL'_def
  have hLL' : L = q ^ L.factorization q * L' := (Nat.ordProj_mul_ordCompl_eq_self L q).symm
  have hqL' : Nat.Coprime q L' := Nat.coprime_ordCompl hq hL0
  have hL'L : L' ∣ L := Dvd.intro_left _ hLL'.symm
  have hL'0 : L' ≠ 0 := fun h0 => hL0 (by rw [hLL', h0, mul_zero])

  set ε : DirichletCharacter ℂ L := DirichletCharacter.changeLevel hM₁L ε₁ with hε_def
  have hε₁L : DirichletCharacter.changeLevel hM₁L ε₁ = ε := rfl
  have hε₂L : DirichletCharacter.changeLevel hM₂L ε₂ = ε :=
    (changeLevel_eq_of_forall_prime_notMem hM₁L hM₂L ε₁ ε₂ S hε).symm

  have hprod : DirichletCharacter.changeLevel (Nat.dvd_mul_right M₁ M₂) ε₁ =
      DirichletCharacter.changeLevel (Nat.dvd_mul_left M₂ M₁) ε₂ := by
    have e1 := DirichletCharacter.changeLevel_trans ε₁ hM₁L hLprod
    have e2 := DirichletCharacter.changeLevel_trans ε₂ hM₂L hLprod
    rw [hε₁L] at e1
    rw [hε₂L] at e2
    exact e1.trans e2.symm
  have hgcd : ε₁.FactorsThrough (M₁.gcd M₂) := DirichletCharacter.factorsThrough_gcd ε₁ ε₂ hprod
  have hMq0 : M₁ / q ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hM₁0) hqM₁) hq.pos).ne'
  have hgcd_dvd : M₁.gcd M₂ ∣ M₁ / q := by
    have hg0 : M₁.gcd M₂ ≠ 0 := Nat.gcd_ne_zero_left hM₁0
    rw [← Nat.factorization_le_iff_dvd hg0 hMq0, Nat.factorization_div hqM₁, hq.factorization,
      Finsupp.le_def]
    intro p
    rw [Finsupp.tsub_apply, Finsupp.single_apply]
    have hgM₁ : (M₁.gcd M₂).factorization p ≤ M₁.factorization p :=
      Finsupp.le_def.1 ((Nat.factorization_le_iff_dvd hg0 hM₁0).2 (Nat.gcd_dvd_left M₁ M₂)) p
    have hgM₂ : (M₁.gcd M₂).factorization p ≤ M₂.factorization p :=
      Finsupp.le_def.1 ((Nat.factorization_le_iff_dvd hg0 hM₂0).2 (Nat.gcd_dvd_right M₁ M₂)) p
    by_cases hpq : q = p
    · subst hpq
      rw [ite_eq_left rfl]
      omega
    · rw [ite_eq_right hpq]
      omega
  have hft : ε₁.FactorsThrough (M₁ / q) :=
    DirichletCharacter.FactorsThrough.mono ε₁ hgcd hgcd_dvd (Nat.div_dvd_of_dvd hqM₁)

  obtain ⟨G₁, -, hG₁c, hG₁n⟩ := CuspForm.exists_degeneracy_gamma1_hasNebentypus (k := k) (N := L)
    (d := 1) (show M₁ * 1 ∣ L by rw [mul_one]; exact hM₁L) g₁
  obtain ⟨G₂, -, hG₂c, hG₂n⟩ := CuspForm.exists_degeneracy_gamma1_hasNebentypus (k := k) (N := L)
    (d := 1) (show M₂ * 1 ∣ L by rw [mul_one]; exact hM₂L) g₂
  have hG₁c' : ∀ n, qCoeff (⇑G₁) n = qCoeff (⇑g₁) n := fun n => by
    rw [hG₁c n, ite_eq_left (one_dvd n), Nat.div_one]
  have hG₂c' : ∀ n, qCoeff (⇑G₂) n = qCoeff (⇑g₂) n := fun n => by
    rw [hG₂c n, ite_eq_left (one_dvd n), Nat.div_one]
  have hG₁neb : CuspForm.HasNebentypus ε G₁ := hG₁n ε₁ h₁.1.hasNebentypus
  have hG₂neb' : CuspForm.HasNebentypus (DirichletCharacter.changeLevel hM₂L ε₂) G₂ :=
    hG₂n ε₂ h₂.1.hasNebentypus
  have hG₂neb : CuspForm.HasNebentypus ε G₂ := by rw [hε₂L] at hG₂neb'; exact hG₂neb'
  set D : CuspForm (Γ₁ℝ L) k := G₁ - G₂ with hD_def
  have hDneb : CuspForm.HasNebentypus ε D := by
    intro γ hγ τ
    have e1 := hG₁neb γ hγ τ
    have e2 := hG₂neb γ hγ τ
    simp only [hD_def, FunLike.coe_sub, Pi.sub_apply]
    rw [e1, e2]
    ring
  have hDc : ∀ n, qCoeff (⇑D) n = qCoeff (⇑g₁) n - qCoeff (⇑g₂) n := fun n => by
    rw [hD_def, qCoeff_sub, hG₁c', hG₂c']
  have hD1 : qCoeff (⇑D) 1 = 0 := by rw [hDc, h₁.1.qCoeff_one, h₂.1.qCoeff_one, sub_self]
  set lam : ℕ → ℂ := fun p => qCoeff (⇑g₁) p with hlam
  have heig : ∀ p : ℕ, p.Prime → p ∉ S → ¬ p ∣ L → ∀ n : ℕ,
      qCoeff (⇑D) (p * n) + ε (p : ZMod L) * (p : ℂ) ^ (k - 1) *
        (if p ∣ n then qCoeff (⇑D) (n / p) else 0) = lam p * qCoeff (⇑D) n := by
    intro p hp hpS hpL n
    have hpM₁ : ¬ p ∣ M₁ := fun hd => hpL (hd.trans hM₁L)
    have hpM₂ : ¬ p ∣ M₂ := fun hd => hpL (hd.trans hM₂L)
    have hcop : Nat.Coprime p L := (Nat.Prime.coprime_iff_not_dvd hp).2 hpL
    have r1 := h₁.1.hecke_of_not_dvd hp hpM₁ n
    have r2 := h₂.1.hecke_of_not_dvd hp hpM₂ n
    rw [changeLevel_apply_natCast hM₁L ε₁ ε hε₁L p hcop] at r1
    rw [changeLevel_apply_natCast hM₂L ε₂ ε hε₂L p hcop, ← ha p hp hpS] at r2
    simp only [hDc, hlam]
    have hite : (if p ∣ n then qCoeff (⇑g₁) (n / p) - qCoeff (⇑g₂) (n / p) else 0) =
        (if p ∣ n then qCoeff (⇑g₁) (n / p) else 0) -
          (if p ∣ n then qCoeff (⇑g₂) (n / p) else 0) := by
      split_ifs <;> ring
    rw [hite]
    linear_combination r1 - r2

  obtain ⟨n, d, c, N, η, h, hgood, htow⟩ := tower ε D hDneb S lam hD1 heig hq hqL L' hLL'
  have hlamg₂ : ∀ p : ℕ, p.Prime → p ∉ S → ¬ p ∣ L → qCoeff (⇑g₂) p = lam p :=
    fun p hp hpS _ => (ha p hp hpS).symm
  have hcopL : ∀ u : ℕ, Nat.Coprime u L → qCoeff (⇑g₁) u = qCoeff (⇑g₂) u := by
    intro u hu
    have huL' : Nat.Coprime u L' := Nat.Coprime.coprime_dvd_right hL'L hu
    have hqu : ¬ q ∣ u := fun hd =>
      hq.one_lt.ne' ((Nat.Coprime.coprime_dvd_left hd hu).eq_one_of_dvd hqL)
    have := htow u huL'
    rw [hDc] at this
    have hzero : ∑ i, c i * (if q * d i ∣ u then qCoeff (⇑(h i)) (u / (q * d i)) else 0) = 0 :=
      Finset.sum_eq_zero fun i _ => by
        rw [ite_eq_right (fun hd => hqu ((Dvd.intro _ rfl : q ∣ q * d i).trans hd)), mul_zero]
    rw [hzero, sub_eq_zero] at this
    exact this
  rcases hm1.eq_or_lt with hm_one | hm_two
  ·
    have hm1' : m = 1 := hm_one.symm
    have hqM₂ : ¬ q ∣ M₂ := fun hd => by
      have := (hq.dvd_iff_one_le_factorization hM₂0).1 hd
      omega
    have hq2 : ¬ q ^ 2 ∣ M₁ := fun hd => by
      have := (hq.pow_dvd_iff_le_factorization hM₁0).1 hd
      omega
    have hLq : L = q * L' := by
      have := hLL'
      rw [hLfac, hm1', pow_one] at this
      exact this
    have hLdq : L / q = L' := by
      rw [hLq, Nat.mul_div_cancel_left _ hq.pos]
    have hM₂L' : M₂ ∣ L' := by
      have h1 : M₂ ∣ q * L' := hLq ▸ hM₂L
      exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hq).2 hqM₂)).dvd_of_dvd_mul_left h1

    have hconst : ∀ i, c i ≠ 0 → d i = 1 → ∀ r, qCoeff (⇑(h i)) r = qCoeff (⇑g₂) r := by
      intro i hi hdi
      obtain ⟨hNd, hprim, ⟨hNL, hηε⟩, hpk⟩ := hgood i hi
      have hN0 : N i ≠ 0 := by
        intro h0
        rw [h0, zero_mul, hLdq] at hNd
        exact hL'0 (Nat.eq_zero_of_zero_dvd hNd)
      have : NeZero (N i) := ⟨hN0⟩
      have hNL' : N i ∣ L' := by
        have := dvd_of_mul_right_dvd hNd
        rwa [hLdq] at this
      have hlcm : Nat.lcm (N i) M₂ < L := by
        have hdvd : Nat.lcm (N i) M₂ ∣ L' := Nat.lcm_dvd hNL' hM₂L'
        calc Nat.lcm (N i) M₂ ≤ L' := Nat.le_of_dvd (Nat.pos_of_ne_zero hL'0) hdvd
          _ < L := by rw [hLq]; exact lt_mul_left (Nat.pos_of_ne_zero hL'0) hq.one_lt
      exact (qCoeff_eq_of_levelIH IH h₂ hM₂L ε hε₂L S lam hlamg₂ hprim hNL hηε hpk hlcm).2

    set a₁ : ℂ := qCoeff (⇑g₁) q with ha₁_def
    set b : ℂ := qCoeff (⇑g₂) q with hb_def
    set C : ℂ := ∑ i, (if d i = 1 then c i else 0) with hC
    have hcopq : Nat.Coprime q L' := hqL'
    have hcopqq : Nat.Coprime (q * q) L' := Nat.Coprime.mul_left hqL' hqL'
    have hterm1 : ∀ i, c i * (if q * d i ∣ q then qCoeff (⇑(h i)) (q / (q * d i)) else 0) =
        (if d i = 1 then c i else 0) := by
      intro i
      by_cases hci : c i = 0
      · rw [hci, zero_mul]
        split_ifs <;> rfl
      by_cases hdi : d i = 1
      · rw [hdi, mul_one, ite_eq_left (dvd_refl q), Nat.div_self hq.pos, ite_eq_left rfl,
          (hgood i hci).2.1.1.qCoeff_one, mul_one]
      · have hnd : ¬ q * d i ∣ q := fun hd =>
          hdi (Nat.dvd_one.1 ((Nat.mul_dvd_mul_iff_left hq.pos).1 (by rwa [mul_one])))
        rw [ite_eq_right hnd, ite_eq_right hdi, mul_zero]
    have hCq : qCoeff (⇑D) q = C := by
      rw [htow q hcopq, hC]
      exact Finset.sum_congr rfl fun i _ => hterm1 i
    have hterm2 : ∀ i,
        c i * (if q * d i ∣ q * q then qCoeff (⇑(h i)) (q * q / (q * d i)) else 0) =
          (if d i = 1 then c i else 0) * b := by
      intro i
      by_cases hci : c i = 0
      · rw [hci, zero_mul]
        split_ifs <;> simp
      by_cases hdi : d i = 1
      · rw [hdi, mul_one, ite_eq_left (Dvd.intro q rfl), Nat.mul_div_cancel_left q hq.pos,
          ite_eq_left rfl, hconst i hci hdi q]
      · have hnd : ¬ q * d i ∣ q * q := by
          intro hd
          have hdq : d i ∣ q := (Nat.mul_dvd_mul_iff_left hq.pos).1 hd
          rcases (Nat.dvd_prime hq).1 hdq with hd1 | hd2
          · exact hdi hd1
          · obtain ⟨hNd, -, -, -⟩ := hgood i hci
            rw [hLdq, hd2] at hNd
            exact hq.one_lt.ne' (hqL'.eq_one_of_dvd ((Dvd.intro_left _ rfl).trans hNd))
        rw [ite_eq_right hnd, ite_eq_right hdi, zero_mul, mul_zero]
    have hCqq : qCoeff (⇑D) (q * q) = C * b := by
      rw [htow (q * q) hcopqq, hC, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => hterm2 i
    have hread1 : a₁ - b = C := by rw [← hCq, hDc]
    have hread2 : qCoeff (⇑g₁) (q * q) - qCoeff (⇑g₂) (q * q) = C * b := by rw [← hCqq, hDc]
    have hU : qCoeff (⇑g₁) (q * q) = a₁ * a₁ := h₁.1.hecke_of_dvd hq hqM₁ q
    have hT : qCoeff (⇑g₂) (q * q) + ε₂ (q : ZMod M₂) * (q : ℂ) ^ (k - 1) = b * b := by
      have := h₂.1.hecke_of_not_dvd hq hqM₂ q
      rw [ite_eq_left (dvd_refl q), Nat.div_self hq.pos, h₂.1.qCoeff_one, mul_one] at this
      exact this
    have hquad : a₁ * a₁ - a₁ * b + ε₂ (q : ZMod M₂) * (q : ℂ) ^ (k - 1) = 0 := by
      linear_combination -hU + hread2 + hT - b * hread1

    obtain ⟨hdvq, ε₁', hε₁'⟩ := hft
    have hε₁'v : ∀ u : ℕ, Nat.Coprime u M₁ → ε₁' (u : ZMod (M₁ / q)) = ε₁ (u : ZMod M₁) :=
      fun u hu => changeLevel_apply_natCast hdvq ε₁' ε₁ hε₁'.symm u hu
    have hg₁0 : g₁ ≠ 0 := ne_zero_of_isEigenformWith h₁.1
    have hneb₁ : CuspForm.HasNebentypus
        (DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd hqM₁) ε₁') g₁ := by
      have := h₁.1.hasNebentypus
      rw [hε₁'] at this
      exact this
    have hdich :=
      CuspForm.qCoeff_sq_eq_mul_zpow_or_exists_hasNebentypus_qCoeff_hecke_eigen_of_dvd_of_not_sq_dvd
        M₁ k hq hqM₁ hq2 ε₁' g₁ hg₁0 hneb₁ (fun r => h₁.1.hecke_of_dvd hq hqM₁ r)
        (fun ℓ hℓ hℓM r => by
          have := h₁.1.hecke_of_not_dvd hℓ hℓM r
          rw [← hε₁'v ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hℓM)] at this
          exact this)
    have hsq : a₁ ^ 2 = ε₁' (q : ZMod (M₁ / q)) * (q : ℂ) ^ (k - 2) := by
      rcases hdich with hsq | ⟨g, hg0, hgneb, hgT⟩
      · exact hsq
      · exfalso
        refine h₁.not_eigenpacketOccursAt (Nat.div_dvd_of_dvd hqM₁)
          (Nat.div_lt_self (Nat.pos_of_ne_zero hM₁0) hq.one_lt).ne
          ⟨ε₁', g, hg0, hgneb, M₁.primeFactors, fun p hp hpS => ?_⟩
        have hpM : ¬ p ∣ M₁ := fun hd => hpS (Nat.mem_primeFactors.2 ⟨hp, hd, hM₁0⟩)
        exact ⟨hε₁'v p ((Nat.Prime.coprime_iff_not_dvd hp).2 hpM), fun r => hgT p hp hpM r⟩

    have hqcopMq : Nat.Coprime q (M₁ / q) := (Nat.Prime.coprime_iff_not_dvd hq).2 (fun hd => hq2 (by
      have := Nat.mul_dvd_mul_left q hd
      rwa [Nat.mul_div_cancel' hqM₁, ← sq] at this))
    have hqcopM₂ : Nat.Coprime q M₂ := (Nat.Prime.coprime_iff_not_dvd hq).2 hqM₂
    have hcharq : ε₁' (q : ZMod (M₁ / q)) = ε₂ (q : ZMod M₂) := by
      set Q : ℕ := M₁ / q * M₂ with hQ
      have : NeZero Q := ⟨mul_ne_zero hMq0 hM₂0⟩
      have hqQ : Nat.Coprime q Q := Nat.Coprime.mul_right hqcopMq hqcopM₂
      obtain ⟨P, hPgt, hP, hPq⟩ :=
        Nat.forall_exists_prime_gt_and_eq_mod ((ZMod.isUnit_iff_coprime q Q).2 hqQ) L
      have hPL : ¬ P ∣ L := fun hd => (Nat.le_of_dvd (Nat.pos_of_ne_zero hL0) hd).not_gt hPgt
      have hd1 : M₁ / q ∣ Q := Dvd.intro _ rfl
      have hd2 : M₂ ∣ Q := Dvd.intro_left _ rfl
      have e1 : (P : ZMod (M₁ / q)) = (q : ZMod (M₁ / q)) := by
        have := congrArg (ZMod.castHom hd1 (ZMod (M₁ / q))) hPq
        rwa [map_natCast, map_natCast] at this
      have e2 : (P : ZMod M₂) = (q : ZMod M₂) := by
        have := congrArg (ZMod.castHom hd2 (ZMod M₂)) hPq
        rwa [map_natCast, map_natCast] at this
      have hPcopL : Nat.Coprime P L := (Nat.Prime.coprime_iff_not_dvd hP).2 hPL
      have hPcopM₁ : Nat.Coprime P M₁ := Nat.Coprime.coprime_dvd_right hM₁L hPcopL
      rw [← e1, ← e2, hε₁'v P hPcopM₁, changeLevel_apply_natCast hM₁L ε₁ ε hε₁L P hPcopL,
        ← changeLevel_apply_natCast hM₂L ε₂ ε hε₂L P hPcopL]
    have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne_zero
    have hunit : IsUnit (ε₂ (q : ZMod M₂)) := by
      rw [← ZMod.coe_unitOfCoprime q hqcopM₂, ← MulChar.coe_toUnitHom]
      exact Units.isUnit _
    have hE : ε₂ (q : ZMod M₂) * (q : ℂ) ^ (k - 1) = (q : ℂ) * (a₁ * a₁) := by
      rw [← sq, hsq, hcharq, show (k - 1) = (k - 2) + 1 by ring, zpow_add_one₀ hq0]
      ring
    have ha0 : a₁ ≠ 0 := by
      intro h0
      have h2 : a₁ ^ 2 = 0 := by rw [h0]; ring
      rw [hsq, hcharq] at h2
      exact (mul_ne_zero hunit.ne_zero (zpow_ne_zero _ hq0)) h2
    have hbq : b = ((q : ℂ) + 1) * a₁ := by
      have h3 : a₁ * (((q : ℂ) + 1) * a₁ - b) = 0 := by
        linear_combination hquad - hE
      rcases mul_eq_zero.1 h3 with h4 | h4
      · exact absurd h4 ha0
      · exact (sub_eq_zero.1 h4).symm

    have hnormE : ‖ε₂ (q : ZMod M₂)‖ = 1 := by
      have := DirichletCharacter.unit_norm_eq_one ε₂ (ZMod.unitOfCoprime q hqcopM₂)
      rwa [ZMod.coe_unitOfCoprime] at this
    have hna : ‖a₁‖ ^ 2 = (q : ℝ) ^ (k - 2) := by
      rw [← norm_pow, hsq, hcharq, norm_mul, hnormE, one_mul, norm_zpow, Complex.norm_natCast]
    have hq1n : ‖((q : ℂ) + 1)‖ = (q : ℝ) + 1 := by
      rw [show ((q : ℂ) + 1) = ((q + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
      push_cast
      ring
    have hnb : ‖b‖ ^ 2 = ((q : ℝ) + 1) ^ 2 * (q : ℝ) ^ (k - 2) := by
      rw [hbq, norm_mul, mul_pow, hna, hq1n]
    have hHB := CuspForm.norm_sq_lt_of_hasNebentypus_qCoeff_hecke_eigen M₂ k ε₂ g₂
      (ne_zero_of_isEigenformWith h₂.1) h₂.1.hasNebentypus hq hqM₂ b
      (fun r => h₂.1.hecke_of_not_dvd hq hqM₂ r)
    rw [hnb] at hHB
    exact lt_irrefl _ hHB
  ·
    have hq2 : q ^ 2 ∣ M₁ := (hq.pow_dvd_iff_le_factorization hM₁0).2 (by omega)
    have hcop2 : ∀ u : ℕ, Nat.Coprime u M₁ → Nat.Coprime u M₂ → Nat.Coprime u L :=
      fun u hu1 hu2 => Nat.Coprime.coprime_dvd_right hLprod (Nat.Coprime.mul_right hu1 hu2)
    have hchild :=
      CuspForm.IsPrimitiveForm.pow_dvd_of_pow_dvd_of_sq_dvd_of_factorsThrough_of_forall_coprime_qCoeff_eq
        h₁ h₂ (fun u hu1 hu2 => hcopL u (hcop2 u hu1 hu2))
        (fun u hu1 hu2 => by
          have hcop := hcop2 u hu1 hu2
          rw [changeLevel_apply_natCast hM₁L ε₁ ε hε₁L u hcop,
            changeLevel_apply_natCast hM₂L ε₂ ε hε₂L u hcop])
        hq hq2 hft m (Nat.ordProj_dvd M₁ q)
    have hle : m ≤ e := (hq.pow_dvd_iff_le_factorization hM₂0).1 hchild
    omega

theorem level_eq_of_lcm_eq (k : ℤ) : ∀ (L : ℕ) {M₁ M₂ : ℕ} [NeZero M₁] [NeZero M₂]
    {ε₁ : DirichletCharacter ℂ M₁} {ε₂ : DirichletCharacter ℂ M₂}
    {g₁ : CuspForm (Γ₁ℝ M₁) k} {g₂ : CuspForm (Γ₁ℝ M₂) k},
    CuspForm.IsPrimitiveForm ε₁ g₁ → CuspForm.IsPrimitiveForm ε₂ g₂ → ∀ S : Finset ℕ,
    (∀ p : ℕ, p.Prime → p ∉ S → qCoeff g₁ p = qCoeff g₂ p) →
    (∀ p : ℕ, p.Prime → p ∉ S → ε₁ (p : ZMod M₁) = ε₂ (p : ZMod M₂)) →
    Nat.lcm M₁ M₂ = L → M₁ = M₂ := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro M₁ M₂ _ _ ε₁ ε₂ g₁ g₂ h₁ h₂ S ha hε hL
    have IH : LevelIH k L := by
      intro N₁ N₂ i₁ i₂ η₁ η₂ f₁ f₂ hf₁ hf₂ S' ha' hε' hlt
      have := i₁
      have := i₂
      exact ih (Nat.lcm N₁ N₂) hlt hf₁ hf₂ S' ha' hε' rfl
    by_contra hne
    have hM₁0 : M₁ ≠ 0 := NeZero.ne M₁
    have hM₂0 : M₂ ≠ 0 := NeZero.ne M₂
    obtain ⟨q, hq⟩ : ∃ q, M₁.factorization q ≠ M₂.factorization q := by
      by_contra hall
      push Not at hall
      exact hne (Nat.eq_of_factorization_eq hM₁0 hM₂0 hall)
    have hqprime : q.Prime := by
      by_contra hnp
      apply hq
      rw [Nat.factorization_eq_zero_of_not_prime _ hnp, Nat.factorization_eq_zero_of_not_prime _ hnp]
    rcases lt_or_gt_of_ne hq with hlt | hlt
    · exact keyStep IH h₂ h₁ S (fun p hp hpS => (ha p hp hpS).symm)
        (fun p hp hpS => (hε p hp hpS).symm) (by rw [Nat.lcm_comm]; exact hL) hqprime hlt
    · exact keyStep IH h₁ h₂ S ha hε hL hqprime hlt

end SMOGamma1

theorem CuspForm.IsPrimitiveForm.level_eq_and_qCoeff_eq_of_forall_prime_notMem_qCoeff_eq
    {M₁ M₂ : ℕ} [NeZero M₁] [NeZero M₂] {k : ℤ}
    {ε₁ : DirichletCharacter ℂ M₁} {ε₂ : DirichletCharacter ℂ M₂}
    {g₁ : CuspForm (CongruenceSubgroup.Gamma1 M₁) k}
    {g₂ : CuspForm (CongruenceSubgroup.Gamma1 M₂) k}
    (h₁ : CuspForm.IsPrimitiveForm ε₁ g₁) (h₂ : CuspForm.IsPrimitiveForm ε₂ g₂) (S : Finset ℕ)
    (ha : ∀ p : ℕ, p.Prime → p ∉ S → ModularFormClass.qCoeff g₁ p = ModularFormClass.qCoeff g₂ p)
    (hε : ∀ p : ℕ, p.Prime → p ∉ S → ε₁ (p : ZMod M₁) = ε₂ (p : ZMod M₂)) :
    M₁ = M₂ ∧ ∀ n : ℕ, ModularFormClass.qCoeff g₁ n = ModularFormClass.qCoeff g₂ n := by
  have hM : M₁ = M₂ := SMOGamma1.level_eq_of_lcm_eq k (Nat.lcm M₁ M₂) h₁ h₂ S ha hε rfl
  subst hM
  exact ⟨rfl, SMOGamma1.qCoeff_eq_of_level_eq h₁ h₂ S ha hε⟩


end
