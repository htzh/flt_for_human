/-
  The Hecke operators on `q`-coefficients: `U_p`, `T_p`, the diagonal dilation and
  the coefficient algebra.

  Each operator carries one presentation (`hasSum_average` for `U_p`, the dilation
  `d • τ` for the diagonal translate, and their sum for `T_p`), and every public
  statement is that presentation read through one of two eliminators
  `qCoeff_eq_of_hasSum` for a coefficient identity, `hasQCoeff_of_hasSum` for a
  certificate.

  Two shape notes. `UpperHalfPlane.qExpansion_coeff_unique` in mathlib `v4.34.0`
  is stated over `{F : Type*} [FunLike F ℍ ℂ]`; instantiating it at the bare
  function type `ℍ → ℂ` unfolds `DFunLike.coe` millions of times. The port's
  `qExpansion_coeff_unique_of_hasSum` is that statement at the bare type, reading the
  analyticity at the cusp off the presentation. And
  `ModularForm.qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne`
  is proved here coefficientwise through `qCoeff_eq_of_hasSum`.
-/
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.BoundedAtCusp
import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Algebra.Rat
import FLTForHuman.ModularForms.Defs.FormalHeckeOperators
import FLTForHuman.ModularForms.HeckeAnalytic
import FLTForHuman.ModularForms.Defs.HeckeOperator
import FLTForHuman.ModularCurve.Defs.Laurent
import FLTForHuman.ModularForms.QCoeff
import FLTForHuman.ModularForms.QCoeffClass

set_option autoImplicit false

noncomputable section

open Complex Function Filter
open UpperHalfPlane hiding I
open scoped Real MatrixGroups ModularForm Manifold Topology

open ModularForm ModularFormClass

/-! ## The shared tail (private) -/

private theorem qParam_one (z : ℂ) : Periodic.qParam 1 z = exp (2 * π * I * z) := by
  simp [Periodic.qParam]

private theorem natCast_ne_zero' {p : ℕ} (hp : p ≠ 0) : (p : ℂ) ≠ 0 := by
  exact_mod_cast hp

/-- The `q`-parameter along an upper-triangular Hecke matrix. -/
private theorem qParam_heckeMatrix_smul {p : ℕ} (hp : p ≠ 0) (j : ℕ) (τ : ℍ) :
    Periodic.qParam 1 ((heckeMatrix p j • τ : ℍ) : ℂ)
      = exp (2 * π * I * τ / p) * exp (2 * π * I / p) ^ j := by
  rw [qParam_one, coe_heckeMatrix_smul hp, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  have := natCast_ne_zero' hp
  field_simp

/-- The `q`-parameter along the diagonal Hecke matrix: `q(ℓτ) = q(τ) ^ ℓ`. -/
private theorem qParam_heckeDiagMatrix_smul {p : ℕ} (hp : p ≠ 0) (τ : ℍ) :
    Periodic.qParam 1 ((heckeDiagMatrix p • τ : ℍ) : ℂ) = Periodic.qParam 1 τ ^ p := by
  rw [qParam_one, qParam_one, coe_heckeDiagMatrix_smul hp, ← Complex.exp_nat_mul]
  congr 1
  ring

private theorem exp_div_pow {p : ℕ} (hp : p ≠ 0) (τ : ℍ) :
    exp (2 * π * I * τ / p) ^ p = Periodic.qParam 1 τ := by
  rw [qParam_one, ← Complex.exp_nat_mul]
  congr 1
  have := natCast_ne_zero' hp
  field_simp

/-- The root-of-unity filter: `∑_j (ζ ^ j) ^ m` is `p` on multiples of `p`. -/
private theorem sum_rootOfUnity_pow {p : ℕ} (hp : p ≠ 0) (m : ℕ) :
    ∑ j ∈ Finset.range p, (exp (2 * π * I / p) ^ j) ^ m = if p ∣ m then (p : ℂ) else 0 := by
  have hζ := Complex.isPrimitiveRoot_exp p hp
  have hswap : ∀ j : ℕ, (exp (2 * π * I / p) ^ j) ^ m = (exp (2 * π * I / p) ^ m) ^ j := fun j => by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm j m]
  simp only [hswap]
  split_ifs with h
  · rw [(hζ.pow_eq_one_iff_dvd m).mpr h]
    simp
  · have hne : exp (2 * π * I / p) ^ m ≠ 1 := fun h1 => h ((hζ.pow_eq_one_iff_dvd m).mp h1)
    rw [geom_sum_eq hne, ← pow_mul, Nat.mul_comm m p, pow_mul, hζ.pow_eq_one, one_pow, sub_self,
      zero_div]

private theorem not_dvd_of_not_mem_range {p m : ℕ} (hm : m ∉ Set.range (fun l : ℕ ↦ l * p)) :
    ¬ p ∣ m := by
  rintro ⟨l, rfl⟩
  exact hm ⟨l, by simp [mul_comm]⟩

/-- The `p`-fold average: `U_p f` is presented by the coefficients of `f` read on the
multiples of `p`. `sum_rootOfUnity_pow` is the root-of-unity filter that collapses the `p`
cosets onto those multiples. -/
private theorem hasSum_average {p : ℕ} (hp : p ≠ 0) {f : ℍ → ℂ} (hF : HasQCoeff f) (k : ℤ) :
    HasQCoeffWith (heckeU k p f) (coeffHeckeU p (qCoeff f)) := by
  intro τ
  have h1 : HasSum (fun m ↦ ∑ j ∈ Finset.range p,
      qCoeff f m • (exp (2 * π * I * τ / p) * exp (2 * π * I / p) ^ j) ^ m)
      (∑ j ∈ Finset.range p, f (heckeMatrix p j • τ)) := by
    refine hasSum_sum fun j _ => ?_
    have := hF (heckeMatrix p j • τ)
    rwa [qParam_heckeMatrix_smul hp j τ] at this

  have h2 : (fun m ↦ ∑ j ∈ Finset.range p,
      qCoeff f m • (exp (2 * π * I * τ / p) * exp (2 * π * I / p) ^ j) ^ m)
      = fun m ↦ if p ∣ m then (p : ℂ) * qCoeff f m * exp (2 * π * I * τ / p) ^ m else 0 := by
    funext m
    simp only [mul_pow, smul_eq_mul, ← Finset.mul_sum, sum_rootOfUnity_pow hp m]
    split_ifs <;> ring
  rw [h2] at h1

  have hinj : Function.Injective (fun l : ℕ ↦ l * p) := mul_left_injective₀ hp
  have h3 := (hinj.hasSum_iff (f := fun m ↦
      if p ∣ m then (p : ℂ) * qCoeff f m * exp (2 * π * I * τ / p) ^ m else 0)
    (fun m hm => by simp [not_dvd_of_not_mem_range hm])).mpr h1
  have h4 : ((fun m ↦ if p ∣ m then (p : ℂ) * qCoeff f m * exp (2 * π * I * τ / p) ^ m else 0) ∘
      fun l : ℕ ↦ l * p) = fun l ↦ (p : ℂ) * (qCoeff f (l * p) * Periodic.qParam 1 τ ^ l) := by
    funext l
    simp only [comp_apply, ite_eq_left (dvd_mul_left p l)]
    rw [mul_comm l p, pow_mul, exp_div_pow hp τ]
    ring
  rw [h4] at h3
  have h5 := h3.mul_left ((p : ℂ)⁻¹)
  simp only [← mul_assoc, inv_mul_cancel₀ (natCast_ne_zero' hp), one_mul] at h5
  rw [heckeU_apply k hp]
  simpa only [coeffHeckeU_apply, smul_eq_mul] using h5

/-- The diagonal translate `τ ↦ f (d • τ)` is presented by `V_d` applied to the
coefficients of `f`. -/
private theorem hasQCoeffWith_comp_heckeDiagMatrix_smul {d : ℕ} (hd : d ≠ 0) {f : ℍ → ℂ}
    (hF : HasQCoeff f) :
    HasQCoeffWith (fun τ ↦ f (heckeDiagMatrix d • τ)) (coeffHeckeV d (qCoeff f)) := by
  intro τ
  have hq : Periodic.qParam 1 ((heckeDiagMatrix d • τ : ℍ) : ℂ) = Periodic.qParam 1 τ ^ d :=
    qParam_heckeDiagMatrix_smul hd τ
  have hs := hF (heckeDiagMatrix d • τ)
  simp_rw [hq, ← pow_mul] at hs
  have hinj : Injective (fun m : ℕ ↦ d * m) := mul_right_injective₀ hd
  refine (hinj.hasSum_iff ?_).mp ?_
  · intro x hx
    have hx' : ¬ d ∣ x := fun ⟨e, he⟩ => hx ⟨e, he.symm⟩
    simp only [coeffHeckeV_apply, ite_eq_right hx', zero_smul]
  · convert hs using 1
    ext m
    simp only [Function.comp_apply, coeffHeckeV_apply,
      Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd)]
    rw [ite_eq_left (dvd_mul_right d m)]

/-- `T_p f` is `U_p f` plus the diagonal dilation, so its presentation is the sum of the
two: the coefficient decomposition is `coeffHeckeT_eq_add_smul`. -/
private theorem hasQCoeffWith_heckeT {p : ℕ} (hp : p ≠ 0) {f : ℍ → ℂ} (hF : HasQCoeff f)
    (k : ℤ) : HasQCoeffWith (heckeT k p f) (coeffHeckeT k p (qCoeff f)) := by
  have hfun : heckeT k p f
      = heckeU k p f + (p : ℂ) ^ (k - 1) • fun τ ↦ f (heckeDiagMatrix p • τ) := by
    rw [heckeT_eq_heckeU_add k p f]
    congr 1
    funext τ
    rw [Pi.smul_apply, smul_eq_mul, slash_heckeDiagMatrix_apply k hp]
  have hcoeff := congrArg (fun g => g (qCoeff f)) (coeffHeckeT_eq_add_smul k p)
  rw [hfun, hcoeff]
  exact (hasSum_average hp hF k).add
    ((hasQCoeffWith_comp_heckeDiagMatrix_smul hp hF).const_smul ((p : ℂ) ^ (k - 1)))

/-! ## The public targets

The declarations are written with their **dotted** wrapper names (`theorem
UpperHalfPlane.qCoeff_heckeU …`, not inside the namespace).  -/

/-- `U_p` acts on `q`-coefficients through `coeffHeckeU`.  -/
theorem UpperHalfPlane.qCoeff_heckeU {f : UpperHalfPlane → ℂ} (hF : HasQCoeff f) (k : ℤ) {p : ℕ} (hp : p ≠ 0) (n : ℕ) : ModularFormClass.qCoeff (ModularForm.heckeU k p f) n = ModularForm.coeffHeckeU p (ModularFormClass.qCoeff f) n :=
  qCoeff_eq_of_hasSum (hasSum_average hp hF k) n

/-- `T_p` acts on `q`-coefficients through `coeffHeckeT`.  -/
theorem UpperHalfPlane.qCoeff_heckeT {f : UpperHalfPlane → ℂ} (hF : HasQCoeff f) (k : ℤ) {p : ℕ} (hp : p ≠ 0) (n : ℕ) : ModularFormClass.qCoeff (ModularForm.heckeT k p f) n = ModularForm.coeffHeckeT k p (ModularFormClass.qCoeff f) n :=
  qCoeff_eq_of_hasSum (hasQCoeffWith_heckeT hp hF k) n

/-- `U_p` preserves the `q`-expansion certificate. -/
theorem hasSum_qCoeff_heckeU {p : ℕ} (hp : p ≠ 0) {f : ℍ → ℂ} (hF : HasQCoeff f) (k : ℤ) :
    HasQCoeff (heckeU k p f) :=
  hasQCoeff_of_hasSum (hasSum_average hp hF k)

/-- `T_p` preserves the `q`-expansion certificate. -/
theorem hasSum_qCoeff_heckeT {p : ℕ} (hp : p ≠ 0) {f : ℍ → ℂ} (hF : HasQCoeff f) (k : ℤ) :
    HasQCoeff (heckeT k p f) :=
  hasQCoeff_of_hasSum (hasQCoeffWith_heckeT hp hF k)

/-- The diagonal translate scales the `q`-parameter by `d`.  -/
theorem UpperHalfPlane.qCoeff_comp_heckeDiagMatrix_smul {f : UpperHalfPlane → ℂ} (hF : HasQCoeff f) {d : ℕ} (hd : d ≠ 0) (n : ℕ) : ModularFormClass.qCoeff (fun τ ↦ f (ModularForm.heckeDiagMatrix d • τ)) n = if d ∣ n then ModularFormClass.qCoeff f (n / d) else 0 :=
  qCoeff_eq_of_hasSum (hasQCoeffWith_comp_heckeDiagMatrix_smul hd hF) n

/-- The diagonal translate preserves the `q`-expansion certificate. -/
theorem hasSum_qCoeff_comp_heckeDiagMatrix_smul {d : ℕ} (hd : d ≠ 0) {f : ℍ → ℂ}
    (hF : HasQCoeff f) : HasQCoeff (fun τ ↦ f (heckeDiagMatrix d • τ)) :=
  hasQCoeff_of_hasSum (hasQCoeffWith_comp_heckeDiagMatrix_smul hd hF)

/-- The diagonal slash preserves the `q`-expansion certificate. -/
theorem hasSum_qCoeff_slash_heckeDiagMatrix {k : ℤ} {p : ℕ} (hp : p ≠ 0) {f : ℍ → ℂ}
    (hF : HasQCoeff f) : HasQCoeff (f ∣[k] heckeDiagMatrix p) := by
  have hDG : f ∣[k] heckeDiagMatrix p
      = ((p : ℂ) ^ (k - 1)) • fun τ => f (heckeDiagMatrix p • τ) := by
    funext τ
    rw [slash_heckeDiagMatrix_apply k hp, Pi.smul_apply, smul_eq_mul]
  rw [hDG]
  exact hasSum_qCoeff_const_smul (hasSum_qCoeff_comp_heckeDiagMatrix_smul hp hF) _

/-! ### The `q`-coefficient algebra

`qCoeff` is additive and `ℂ`-linear on the periodic-holomorphic-bounded
functions.  -/

/-! The bundled spellings, over any `ModularFormClass`.  Like mathlib's
protected `ModularForm.qExpansion_{add,sub,smul}`, the addition is written at the function
type: that is what `qCoeff` consumes, and it needs no `Add`/`Sub`/`SMul` on the form type. -/

/-- The bundled form of `UpperHalfPlane.qCoeff_heckeU`. Stated verbatim from
`Theorems/Thm_ModularFormClass_qCoeff_heckeU.lean`. -/
theorem ModularFormClass.qCoeff_heckeU {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {p : ℕ} (hp : p ≠ 0) (n : ℕ) : ModularFormClass.qCoeff (ModularForm.heckeU k p f) n = ModularForm.coeffHeckeU p (ModularFormClass.qCoeff f) n :=
  haveI : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  UpperHalfPlane.qCoeff_heckeU (ModularFormClass.hasSum_qCoeff f hΓ) k hp n

/-- The bundled form of `UpperHalfPlane.qCoeff_heckeT`. Stated verbatim from
`Theorems/Thm_ModularFormClass_qCoeff_heckeT.lean`. -/
theorem ModularFormClass.qCoeff_heckeT {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {p : ℕ} (hp : p ≠ 0) (n : ℕ) : ModularFormClass.qCoeff (ModularForm.heckeT k p f) n = ModularForm.coeffHeckeT k p (ModularFormClass.qCoeff f) n :=
  haveI : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  UpperHalfPlane.qCoeff_heckeT (ModularFormClass.hasSum_qCoeff f hΓ) k hp n

/-- The bundled form of the diagonal dilation. Stated verbatim from
`Theorems/Thm_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul.lean`. -/
theorem ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {d : ℕ} (hd : d ≠ 0) (n : ℕ) : ModularFormClass.qCoeff (fun τ ↦ f (ModularForm.heckeDiagMatrix d • τ)) n = if d ∣ n then ModularFormClass.qCoeff f (n / d) else 0 :=
  haveI : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  UpperHalfPlane.qCoeff_comp_heckeDiagMatrix_smul (ModularFormClass.hasSum_qCoeff f hΓ) hd n

/-- `qExpansion` of `U_p f` is the formal `PowerSeries.heckeU p` of the
`qExpansion` of `f`. Stated verbatim from
`Theorems/Thm_ModularFormClass_qExpansion_heckeU_eq_heckeU.lean`. -/
theorem ModularFormClass.qExpansion_heckeU_eq_heckeU {F : Type*} [FunLike F UpperHalfPlane ℂ]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] (f : F)
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {p : ℕ} (hp : p ≠ 0) :
    UpperHalfPlane.qExpansion 1 (ModularForm.heckeU k p ⇑f)
      = PowerSeries.heckeU p (UpperHalfPlane.qExpansion 1 ⇑f) := by
  ext n
  have h := ModularFormClass.qCoeff_heckeU (k := k) f hΓ hp n
  simp only [ModularFormClass.qCoeff] at h
  rw [PowerSeries.coeff_heckeU, h, ModularForm.coeffHeckeU, mul_comm n p]
  rfl

/-- `qExpansion` of `T_p f` is the formal `PowerSeries.heckeT p k` of the
`qExpansion` of `f`. Stated verbatim from
`Theorems/Thm_ModularFormClass_qExpansion_heckeT_eq_heckeT.lean`. -/
theorem ModularFormClass.qExpansion_heckeT_eq_heckeT {F : Type*} [FunLike F UpperHalfPlane ℂ]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℕ} [ModularFormClass F Γ k] (f : F)
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {p : ℕ} (hp : p ≠ 0) (hk : 1 ≤ k) :
    UpperHalfPlane.qExpansion 1 (ModularForm.heckeT k p ⇑f)
      = PowerSeries.heckeT p k (UpperHalfPlane.qExpansion 1 ⇑f) := by
  ext n
  have h := ModularFormClass.qCoeff_heckeT (k := (k : ℤ)) f hΓ hp n
  simp only [ModularFormClass.qCoeff] at h
  rw [PowerSeries.coeff_heckeT, h, ModularForm.coeffHeckeT, mul_comm n p]
  have hk' : ((k : ℤ) - 1) = ((k - 1 : ℕ) : ℤ) := (Nat.cast_sub hk).symm
  rw [hk', zpow_natCast]
  split_ifs <;> simp [ModularFormClass.qCoeff]

/-! ### The diagonal degeneration

The diagonal translate `τ ↦ d • τ` substitutes `q ↦ q ^ d` on the `q`-expansion. Nothing
level-theoretic enters: `d` is an integer, so the translate of a `1`-periodic function is
`1`-periodic again, and the width-one presentation of `f` (`HasQCoeff`) is all the
statement uses. -/

/-- `qExpand` agrees with the formal dilation `PowerSeries.heckeV` on a power series: both put
the coefficient `n` at the exponent `N * n`, and the negative exponents are killed on both
sides (`ModularCurve.qExpand_coe_powerSeries_coeff_of_neg`). -/
private theorem qExpand_coe_heckeV (N : ℕ) [NeZero N] (φ : PowerSeries ℂ) :
    ModularCurve.qExpand ℂ N ((φ : LaurentSeries ℂ))
      = ((PowerSeries.heckeV N φ : PowerSeries ℂ) : LaurentSeries ℂ) := by
  ext k
  rcases lt_or_ge k 0 with hk | hk
  · rw [ModularCurve.qExpand_coe_powerSeries_coeff_of_neg N φ hk,
      ModularCurve.coe_powerSeries_coeff_of_neg _ hk]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    by_cases h : N ∣ n
    · obtain ⟨j, rfl⟩ := h
      rw [LaurentSeries.coeff_coe_powerSeries, PowerSeries.coeff_heckeV, Nat.cast_mul,
        ModularCurve.qExpand_coeff_mul, LaurentSeries.coeff_coe_powerSeries]
      simp [Nat.mul_div_cancel_left j (Nat.pos_of_ne_zero (NeZero.ne N))]
    · have h' : ¬ (N : ℤ) ∣ ((n : ℤ)) := fun hd => h (Int.natCast_dvd_natCast.mp hd)
      rw [ModularCurve.qExpand_coeff_of_not_dvd (N := N) (f := (φ : LaurentSeries ℂ)) h',
        LaurentSeries.coeff_coe_powerSeries, PowerSeries.coeff_heckeV]
      simp [h]

/-- The `q`-expansion of the diagonal translate is the `d`-th `qExpand` of the
`q`-expansion. -/
theorem UpperHalfPlane.qExpansion_heckeDiagMatrix_smul_eq_qExpand {f : ℍ → ℂ} (hF : HasQCoeff f)
    (d : ℕ) [NeZero d] :
    ((qExpansion 1 (fun τ ↦ f (heckeDiagMatrix d • τ)) : PowerSeries ℂ) : LaurentSeries ℂ)
      = ModularCurve.qExpand ℂ d ((qExpansion 1 f : PowerSeries ℂ) : LaurentSeries ℂ) := by
  have hps : (qExpansion 1 (fun τ ↦ f (heckeDiagMatrix d • τ)) : PowerSeries ℂ)
      = PowerSeries.heckeV d (qExpansion 1 f) := by
    ext m
    rw [PowerSeries.coeff_heckeV]
    simpa only [ModularFormClass.qCoeff] using
      UpperHalfPlane.qCoeff_comp_heckeDiagMatrix_smul hF (NeZero.ne d) m
  rw [hps]
  exact (qExpand_coe_heckeV d (qExpansion 1 f)).symm

namespace ModularForm

/-! ### The level-one diagonal degeneration

The pin states the degeneration for a level-one form. That is the case `f := ⇑F` of
`UpperHalfPlane.qExpansion_heckeDiagMatrix_smul_eq_qExpand`, and all `𝒮ℒ` supplies is
`1 ∈ 𝒮ℒ.strictPeriods`: the width one that `HasQCoeff` already carries.  -/

/-- The level-one diagonal degeneration. Stated verbatim from
`Theorems/Thm_ModularForm_qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne.lean`. -/
theorem qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne (N : ℕ) [NeZero N] {k : ℤ} (F : ModularForm 𝒮ℒ k) : ((qExpansion 1 (fun τ : ℍ => (F : ℍ → ℂ) (ModularForm.heckeDiagMatrix N • τ)) : PowerSeries ℂ) : LaurentSeries ℂ) = ModularCurve.qExpand ℂ N ((qExpansion 1 (F : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) :=
  UpperHalfPlane.qExpansion_heckeDiagMatrix_smul_eq_qExpand
    (ModularFormClass.hasSum_qCoeff F one_mem_strictPeriods_SL) N

/-! ### The coefficient algebra

The pinned statements are verbatim from their `Theorems/` wrappers. This is a `q`-side
algebra: `T_p = U_p + p ^ (k - 1) • V_p` (`ModularForm.coeffHeckeT_eq_add_smul`), and the
commutation of `T_p` with `T_q` is that of the four products `U U`, `U V`, `V U`, `V V`. -/

/-- `U_p` and `U_q` commute on coefficient sequences. Stated verbatim from
`Theorems/Thm_ModularForm_coeffHeckeU_comm.lean`. -/
theorem coeffHeckeU_comm (p q : ℕ) (a : ℕ → ℂ) : ModularForm.coeffHeckeU p (ModularForm.coeffHeckeU q a) = ModularForm.coeffHeckeU q (ModularForm.coeffHeckeU p a) := by
  funext n
  simp only [coeffHeckeU_apply, Nat.mul_right_comm]

/-- `V` is multiplicative: `V_p ∘ V_q = V_{p * q}`. -/
theorem coeffHeckeV_comp (p q : ℕ) (a : ℕ → ℂ) :
    ModularForm.coeffHeckeV p (ModularForm.coeffHeckeV q a)
      = ModularForm.coeffHeckeV (p * q) a := by
  funext n
  simp only [ModularForm.coeffHeckeV_apply]
  by_cases hp : p ∣ n
  · rw [ite_eq_left hp]
    by_cases hq : q ∣ n / p
    · rw [ite_eq_left hq, ite_eq_left ((Nat.dvd_div_iff_mul_dvd hp).mp hq)]
      exact congrArg a (Nat.div_div_eq_div_mul n p q)
    · rw [ite_eq_right hq, ite_eq_right (fun h => hq ((Nat.dvd_div_iff_mul_dvd hp).mpr h))]
  · rw [ite_eq_right hp, ite_eq_right (fun h => hp (dvd_trans (dvd_mul_right p q) h))]

/-- The dilations commute. -/
theorem coeffHeckeV_comm (p q : ℕ) (a : ℕ → ℂ) :
    ModularForm.coeffHeckeV p (ModularForm.coeffHeckeV q a)
      = ModularForm.coeffHeckeV q (ModularForm.coeffHeckeV p a) := by
  rw [coeffHeckeV_comp p q a, coeffHeckeV_comp q p a, Nat.mul_comm]

/-- `U_p` commutes with the dilation `V_q` for coprime `p`, `q`. -/
theorem coeffHeckeU_coeffHeckeV_comm {p q : ℕ} (hpq : Nat.Coprime p q) (a : ℕ → ℂ) :
    ModularForm.coeffHeckeU p (ModularForm.coeffHeckeV q a)
      = ModularForm.coeffHeckeV q (ModularForm.coeffHeckeU p a) := by
  funext n
  simp only [ModularForm.coeffHeckeU_apply, ModularForm.coeffHeckeV_apply]
  have h : q ∣ n * p ↔ q ∣ n := hpq.symm.dvd_mul_right
  by_cases hq : q ∣ n
  · rw [ite_eq_left (h.mpr hq), ite_eq_left hq]
    exact congrArg a (Nat.div_mul_right_comm hq p).symm
  · rw [ite_eq_right (fun hh => hq (h.mp hh)), ite_eq_right hq]

/-- `T_p` commutes with `U_q` for coprime `p`, `q`. Stated verbatim from
`Theorems/Thm_ModularForm_coeffHeckeT_coeffHeckeU_comm.lean`. -/
theorem coeffHeckeT_coeffHeckeU_comm (k : ℤ) {p q : ℕ} (hpq : Nat.Coprime p q) (a : ℕ → ℂ) : ModularForm.coeffHeckeT k p (ModularForm.coeffHeckeU q a) = ModularForm.coeffHeckeU q (ModularForm.coeffHeckeT k p a) := by
  have hUU : coeffHeckeU p (coeffHeckeU q a) = coeffHeckeU q (coeffHeckeU p a) :=
    coeffHeckeU_comm p q a
  have hVU : coeffHeckeV p (coeffHeckeU q a) = coeffHeckeU q (coeffHeckeV p a) :=
    (coeffHeckeU_coeffHeckeV_comm hpq.symm a).symm
  rw [coeffHeckeT_eq_add_smul k p]
  simp only [Pi.add_apply, Pi.smul_apply, coeffHeckeU_add, coeffHeckeU_smul]
  rw [hUU, hVU]

/-- `T_p` and `T_q` commute for coprime `p`, `q`. Stated verbatim from
`Theorems/Thm_ModularForm_coeffHeckeT_comm.lean`. -/
theorem coeffHeckeT_comm (k : ℤ) {p q : ℕ} (hpq : Nat.Coprime p q) (a : ℕ → ℂ) : ModularForm.coeffHeckeT k p (ModularForm.coeffHeckeT k q a) = ModularForm.coeffHeckeT k q (ModularForm.coeffHeckeT k p a) := by
  have hUU : coeffHeckeU p (coeffHeckeU q a)
      = coeffHeckeU q (coeffHeckeU p a) :=
    coeffHeckeU_comm p q a
  have hUV : coeffHeckeU p (coeffHeckeV q a)
      = coeffHeckeV q (coeffHeckeU p a) :=
    coeffHeckeU_coeffHeckeV_comm hpq a
  have hVU : coeffHeckeV p (coeffHeckeU q a)
      = coeffHeckeU q (coeffHeckeV p a) :=
    (coeffHeckeU_coeffHeckeV_comm hpq.symm a).symm
  have hVV : coeffHeckeV p (coeffHeckeV q a)
      = coeffHeckeV q (coeffHeckeV p a) :=
    coeffHeckeV_comm p q a
  rw [coeffHeckeT_eq_add_smul k p, coeffHeckeT_eq_add_smul k q]
  simp only [Pi.add_apply, Pi.smul_apply, coeffHeckeU_add,
    coeffHeckeU_smul, coeffHeckeV_add, coeffHeckeV_smul]
  rw [hUU, hUV, hVU, hVV]
  simp only [smul_add, smul_smul, mul_comm ((p : ℂ) ^ (k - 1)) ((q : ℂ) ^ (k - 1))]
  abel

/-- Integrality of `U_p` on integral coefficient sequences. Stated verbatim from
`Theorems/Thm_ModularForm_coeffHeckeU_int.lean`. -/
theorem coeffHeckeU_int (p : ℕ) {a : ℕ → ℂ} (ha : ∀ n : ℕ, ∃ m : ℤ, a n = m) (n : ℕ) : ∃ m : ℤ, ModularForm.coeffHeckeU p a n = m := by
  rw [coeffHeckeU_apply]
  exact ha (n * p)

/-- Integrality of `T_p` on integral coefficient sequences. Stated verbatim from
`Theorems/Thm_ModularForm_coeffHeckeT_int.lean`. -/
theorem coeffHeckeT_int (k : ℤ) (hk : 1 ≤ k) (p : ℕ) {a : ℕ → ℂ} (ha : ∀ n : ℕ, ∃ m : ℤ, a n = m) (n : ℕ) : ∃ m : ℤ, ModularForm.coeffHeckeT k p a n = m := by
  obtain ⟨m₁, hm₁⟩ := ha (n * p)
  rw [coeffHeckeT_apply, hm₁]
  split_ifs with h
  · obtain ⟨m₂, hm₂⟩ := ha (n / p)
    obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr hk)
    refine ⟨m₁ + p ^ j * m₂, ?_⟩
    rw [hm₂, hj, zpow_natCast]
    push_cast
    ring
  · exact ⟨m₁, by simp⟩

end ModularForm

end
