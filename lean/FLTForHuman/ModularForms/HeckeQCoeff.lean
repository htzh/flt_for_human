/-
  The `q`-coefficient layer of the Hecke operators: `qCoeff`, `qExpansion` and the
  coefficient algebra.

  FLT states the `q`-coefficient theory in **four** 353-line `S_` files
  (`S_UpperHalfPlane_qCoeff_hecke{U,T}.lean`,
  `S_ModularFormClass_qCoeff_hecke{U,T}.lean`). Their first 154 lines are the
  analytic head already ported once in `HeckeAnalytic.lean`; their tail (pin lines
  156–345: `qExpansion_coeff_unique'`, `hasSum_qCoeff`, `qParam_*`,
  `sum_rootOfUnity_pow`, `hasSum_average`/`hasSum_diag`, `hasSum_heckeU/T`,
  `qCoeff_heckeU/T_bare/class`) is byte-identical across the four. This module
  writes that tail **once** (all `private`) and lands the public targets verbatim
  from their `Theorems/` wrappers (pinned `aa2d8b3`):

  - `UpperHalfPlane.qCoeff_heckeU`, `…qCoeff_heckeT`;
  - `ModularFormClass.qCoeff_heckeU`, `…qCoeff_heckeT`;
  - `UpperHalfPlane.qCoeff_comp_heckeDiagMatrix_smul`,
    `ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul` (the dilation pair, whose
    120-line pin blocks are also identical — ported once);
  - `ModularFormClass.qExpansion_heckeU_eq_heckeU`, `…qExpansion_heckeT_eq_heckeT`;
  - `ModularForm.qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne`;
  - `UpperHalfPlane.eq_of_forall_qCoeff_eq`;
  - the coefficient algebra `ModularForm.coeffHecke{T,U}_comm`,
    `…coeffHeckeT_coeffHeckeU_comm`, `…coeffHecke{T,U}_int`.

  `ModularFormClass.qCoeff` itself is the pin's definition from
  `Definitions/Def_FLTPrelim_Modularity.lean:19`, transcribed here (the port had
  not carried it before). The eigenform interface (`coeffHecke_eigenvalue_*`,
  `IsNormalizedEigenform`) is SET 4 and is **not** ported.

  Two shape notes. `UpperHalfPlane.qExpansion_coeff_unique` in mathlib `v4.34.0`
  is stated over `{F : Type*} [FunLike F ℍ ℂ]`; instantiating it at the bare
  function type `ℍ → ℂ` unfolds `DFunLike.coe` millions of times. The pin's primed
  form passes a bundled `ContinuousMap.mk g hcont` instead, which is the fixed
  shape and is kept. And `ModularForm.qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne`
  is proved here coefficientwise through `qExpansion_coeff_unique'` rather than
  through the pin's `ModularForm.exists_degeneracy_Gamma0` +
  `ModularCurve.laurent_qParam_coeff_unique`, neither of which the port has; the
  statement is unchanged.

  FLT provenance: `P2M/Sol/S_UpperHalfPlane_qCoeff_heckeU.lean` lines 156–345 (the
  shared tail), the four sibling `qCoeff` files, the two
  `qCoeff_comp_heckeDiagMatrix_smul` files (120 lines each),
  `S_ModularFormClass_qExpansion_hecke{U,T}_eq_hecke{T,U}.lean`,
  `S_UpperHalfPlane_eq_of_forall_qCoeff_eq.lean`, the five coefficient-algebra
  files and `S_ModularForm_qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne.lean`.
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

set_option autoImplicit false

noncomputable section

open Complex Function Filter
open UpperHalfPlane hiding I
open scoped Real MatrixGroups ModularForm Manifold Topology

namespace ModularFormClass

/-- The `n`-th `q`-coefficient of `f`. Transcribed from
`Definitions/Def_FLTPrelim_Modularity.lean:19`. -/
def qCoeff (f : ℍ → ℂ) (n : ℕ) : ℂ :=
  (qExpansion 1 f).coeff n

end ModularFormClass

open ModularForm ModularFormClass

/-! ## The shared tail (private)

The four pin files' identical tail, written once. The statements use the pin's
`MDiff` (`open scoped Manifold`) and explicit binders. -/

/-- The pin's `qExpansion_coeff_unique'`: a `HasSum` presentation pins the
coefficients, stated over `ℍ → ℂ` with a `Continuous` hypothesis (the historical
stall site). The bundled `ContinuousMap` is what keeps the `FunLike` instance
concrete. -/
private theorem qExpansion_coeff_unique' {g : ℍ → ℂ} (hcont : Continuous g) {c : ℕ → ℂ}
    (hg : AnalyticAt ℂ (cuspFunction 1 g) 0)
    (hs : ∀ τ : ℍ, HasSum (fun m ↦ c m • Periodic.qParam 1 τ ^ m) (g τ)) (m : ℕ) :
    c m = (qExpansion 1 g).coeff m :=
  UpperHalfPlane.qExpansion_coeff_unique (ContinuousMap.mk g hcont) one_pos hg hs m

/-- A function with a `q`-expansion has `qCoeff` as its `HasSum` coefficients. -/
private theorem hasSum_qCoeff {f : ℍ → ℂ} (hper : Periodic (f ∘ ofComplex) 1) (hhol : MDiff f)
    (hbdd : IsBoundedAtImInfty f) (τ : ℍ) :
    HasSum (fun m ↦ qCoeff f m • Periodic.qParam 1 τ ^ m) (f τ) :=
  hasSum_qExpansion one_pos hper hhol hbdd τ

/-- `qParam 1 z = exp (2πiz)`. -/
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

/-- The `p`-fold average: the coefficients of `f` on multiples of `p`. -/
private theorem hasSum_average {p : ℕ} (hp : p ≠ 0) {f : ℍ → ℂ}
    (hper : Periodic (f ∘ ofComplex) 1) (hhol : MDiff f) (hbdd : IsBoundedAtImInfty f) (τ : ℍ) :
    HasSum (fun l : ℕ ↦ qCoeff f (l * p) * Periodic.qParam 1 τ ^ l)
      ((p : ℂ)⁻¹ * ∑ j ∈ Finset.range p, f (heckeMatrix p j • τ)) := by
  have hF : ∀ τ' : ℍ, HasSum (fun m ↦ qCoeff f m • Periodic.qParam 1 τ' ^ m) (f τ') :=
    hasSum_qExpansion one_pos hper hhol hbdd

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
  exact h5

/-- The diagonal contribution to `T_p`. -/
private theorem hasSum_diag {p : ℕ} (hp : p ≠ 0) {f : ℍ → ℂ}
    (hper : Periodic (f ∘ ofComplex) 1) (hhol : MDiff f) (hbdd : IsBoundedAtImInfty f)
    (k : ℤ) (τ : ℍ) :
    HasSum (fun n : ℕ ↦ if p ∣ n then (p : ℂ) ^ (k - 1) * qCoeff f (n / p) * Periodic.qParam 1 τ ^ n
        else 0)
      ((p : ℂ) ^ (k - 1) * f (heckeDiagMatrix p • τ)) := by
  have hD := (hasSum_qExpansion one_pos hper hhol hbdd (heckeDiagMatrix p • τ)).mul_left
    ((p : ℂ) ^ (k - 1))
  rw [qParam_heckeDiagMatrix_smul hp τ] at hD
  have hinj : Function.Injective (fun l : ℕ ↦ l * p) := mul_left_injective₀ hp
  refine (hinj.hasSum_iff (fun m hm => by simp [not_dvd_of_not_mem_range hm])).mp ?_
  convert hD using 1
  funext l
  simp only [Function.comp_apply, ite_eq_left (dvd_mul_left p l),
    Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hp), smul_eq_mul, ModularFormClass.qCoeff]
  rw [← pow_mul, mul_comm l p, mul_assoc]

/-- `hasSum` presentation of `qCoeff` for `U_p`. -/
private theorem hasSum_heckeU {p : ℕ} (hp : p ≠ 0) {f : ℍ → ℂ}
    (hper : Periodic (f ∘ ofComplex) 1) (hhol : MDiff f) (hbdd : IsBoundedAtImInfty f)
    (k : ℤ) (τ : ℍ) :
    HasSum (fun n : ℕ ↦ coeffHeckeU p (qCoeff f) n • Periodic.qParam 1 τ ^ n)
      (heckeU k p f τ) := by
  rw [heckeU_apply k hp]
  simpa only [coeffHeckeU_apply, smul_eq_mul] using hasSum_average hp hper hhol hbdd τ

/-- `hasSum` presentation of `qCoeff` for `T_p`. -/
private theorem hasSum_heckeT {p : ℕ} (hp : p ≠ 0) {f : ℍ → ℂ}
    (hper : Periodic (f ∘ ofComplex) 1) (hhol : MDiff f) (hbdd : IsBoundedAtImInfty f)
    (k : ℤ) (τ : ℍ) :
    HasSum (fun n : ℕ ↦ coeffHeckeT k p (qCoeff f) n • Periodic.qParam 1 τ ^ n)
      (heckeT k p f τ) := by
  rw [heckeT_apply k hp]
  convert (hasSum_average hp hper hhol hbdd τ).add (hasSum_diag hp hper hhol hbdd k τ) using 1
  funext n
  rw [coeffHeckeT_apply, smul_eq_mul]
  split_ifs <;> ring

/-- The `U_p` coefficient identity, before its wrapper. -/
private theorem qCoeff_heckeU_bare {p : ℕ} (hp : p ≠ 0) {f : ℍ → ℂ}
    (hper : Periodic (f ∘ ofComplex) 1) (hhol : MDiff f) (hbdd : IsBoundedAtImInfty f)
    (k : ℤ) (n : ℕ) : qCoeff (heckeU k p f) n = coeffHeckeU p (qCoeff f) n :=
  (qExpansion_coeff_unique' (mdifferentiable_heckeU hhol k p).continuous
    (analyticAt_cuspFunction_zero one_pos (periodic_heckeU_comp_ofComplex hper k p)
      (mdifferentiable_heckeU hhol k p) (isBoundedAtImInfty_heckeU hbdd k p))
    (hasSum_heckeU hp hper hhol hbdd k) n).symm

/-- The `T_p` coefficient identity, before its wrapper. -/
private theorem qCoeff_heckeT_bare {p : ℕ} (hp : p ≠ 0) {f : ℍ → ℂ}
    (hper : Periodic (f ∘ ofComplex) 1) (hhol : MDiff f) (hbdd : IsBoundedAtImInfty f)
    (k : ℤ) (n : ℕ) : qCoeff (heckeT k p f) n = coeffHeckeT k p (qCoeff f) n :=
  (qExpansion_coeff_unique' (mdifferentiable_heckeT hhol k p).continuous
    (analyticAt_cuspFunction_zero one_pos (periodic_heckeT_comp_ofComplex hper k p)
      (mdifferentiable_heckeT hhol k p) (isBoundedAtImInfty_heckeT hbdd k p))
    (hasSum_heckeT hp hper hhol hbdd k) n).symm

/-- The `ModularFormClass` form of the `U_p` coefficient identity. -/
private theorem qCoeff_heckeU_class {F : Type*} [FunLike F ℍ ℂ]
    {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] {p : ℕ} (hp : p ≠ 0)
    (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (n : ℕ) :
    qCoeff (heckeU k p f) n = coeffHeckeU p (qCoeff f) n :=
  haveI : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  qCoeff_heckeU_bare hp (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ) (holo f)
    (bdd_at_infty f) k n

/-- The `ModularFormClass` form of the `T_p` coefficient identity. -/
private theorem qCoeff_heckeT_class {F : Type*} [FunLike F ℍ ℂ]
    {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] {p : ℕ} (hp : p ≠ 0)
    (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (n : ℕ) :
    qCoeff (heckeT k p f) n = coeffHeckeT k p (qCoeff f) n :=
  haveI : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  qCoeff_heckeT_bare hp (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ) (holo f)
    (bdd_at_infty f) k n

/-! ## The dilation block (private)

The two 120-line pin files (`qCoeff_comp_heckeDiagMatrix_smul`) are identical; the
argument is written once here. `isBoundedAtImInfty_comp_smul` computes the `im`
along the diagonal directly (`coe_heckeDiagMatrix_smul`), because the port's
`det_heckeDiagMatrix`/`denom_heckeDiagMatrix` are `private` in `Defs/HeckeOperator`. -/

private theorem heckeDiagMatrix_smul_ofComplex {d : ℕ} (hd : d ≠ 0) {z : ℂ} (hz : 0 < z.im) :
    heckeDiagMatrix d • ofComplex z = ofComplex ((d : ℂ) * z) := by
  have hz' : 0 < ((d : ℂ) * z).im := by
    rw [show ((d : ℂ) * z).im = d * z.im by simp]
    have : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
    positivity
  apply UpperHalfPlane.ext
  rw [coe_heckeDiagMatrix_smul hd, ofComplex_apply_of_im_pos hz, ofComplex_apply_of_im_pos hz']

private theorem periodic_comp_smul {d : ℕ} (hd : d ≠ 0) {F : ℍ → ℂ}
    (hper : Periodic (F ∘ ofComplex) 1) :
    Periodic ((fun τ ↦ F (heckeDiagMatrix d • τ)) ∘ ofComplex) 1 := by
  intro w
  by_cases hw : 0 < w.im
  · have hw1 : 0 < (w + 1).im := by simpa using hw
    simp only [comp_apply]
    rw [heckeDiagMatrix_smul_ofComplex hd hw1, heckeDiagMatrix_smul_ofComplex hd hw, mul_add, mul_one]
    have h := hper.nat_mul d ((d : ℂ) * w)
    simpa using h
  · push Not at hw
    have hw1 : (w + 1).im ≤ 0 := by simpa using hw
    simp only [comp_apply, ofComplex_apply_of_im_nonpos hw, ofComplex_apply_of_im_nonpos hw1]

private theorem mdifferentiable_comp_smul {d : ℕ} (hd : d ≠ 0) {F : ℍ → ℂ} (hhol : MDiff F) :
    MDiff (fun τ ↦ F (heckeDiagMatrix d • τ)) := by
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have h := (hhol.slash 0 (heckeDiagMatrix d)).const_smul (d : ℂ)
  convert h using 1
  funext τ
  rw [Pi.smul_apply, slash_heckeDiagMatrix_apply 0 hd, smul_eq_mul, zero_sub, zpow_neg_one,
    ← mul_assoc, mul_inv_cancel₀ hd', one_mul]

private theorem isBoundedAtImInfty_comp_smul {d : ℕ} (hd : d ≠ 0) {F : ℍ → ℂ}
    (hbdd : IsBoundedAtImInfty F) :
    IsBoundedAtImInfty (fun τ ↦ F (heckeDiagMatrix d • τ)) := by
  refine hbdd.comp_tendsto ?_
  rw [atImInfty, tendsto_comap_iff]
  have him : (UpperHalfPlane.im ∘ fun τ : ℍ ↦ heckeDiagMatrix d • τ) = fun τ ↦ (d : ℝ) * τ.im := by
    funext τ
    simp only [comp_apply]
    rw [UpperHalfPlane.im, coe_heckeDiagMatrix_smul hd]
    simp [Complex.mul_im]
  rw [him]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
  exact tendsto_comap.const_mul_atTop hd0

private theorem qCoeff_comp_smul {d : ℕ} (hd : d ≠ 0) {F : ℍ → ℂ}
    (hper : Periodic (F ∘ ofComplex) 1) (hhol : MDiff F) (hbdd : IsBoundedAtImInfty F) (n : ℕ) :
    qCoeff (fun τ ↦ F (heckeDiagMatrix d • τ)) n =
      if d ∣ n then qCoeff F (n / d) else 0 := by
  set G : ℍ → ℂ := fun τ ↦ F (heckeDiagMatrix d • τ) with hG
  have hGdiff : MDiff G := mdifferentiable_comp_smul hd hhol
  have han : AnalyticAt ℂ (cuspFunction 1 G) 0 :=
    analyticAt_cuspFunction_zero one_pos (periodic_comp_smul hd hper) hGdiff
      (isBoundedAtImInfty_comp_smul hd hbdd)

  set c : ℕ → ℂ := fun n ↦ if d ∣ n then (qExpansion 1 F).coeff (n / d) else 0 with hc
  have hsum : ∀ τ : ℍ, HasSum (fun m ↦ c m • Periodic.qParam 1 τ ^ m) (G τ) := by
    intro τ
    have hq : Periodic.qParam 1 ((heckeDiagMatrix d • τ : ℍ) : ℂ) = Periodic.qParam 1 τ ^ d := by
      simp only [Periodic.qParam, ← Complex.exp_nat_mul, coe_heckeDiagMatrix_smul hd]
      congr 1
      push_cast
      ring
    have hs := hasSum_qExpansion one_pos hper hhol hbdd (heckeDiagMatrix d • τ)
    simp_rw [hq, ← pow_mul] at hs
    have hinj : Injective (fun m : ℕ ↦ d * m) := mul_right_injective₀ hd
    have hsupp : ∀ x ∉ Set.range (fun m : ℕ ↦ d * m),
        (fun m ↦ c m • Periodic.qParam 1 τ ^ m) x = 0 := by
      intro x hx
      have : ¬ d ∣ x := by
        rintro ⟨e, rfl⟩
        exact hx ⟨e, rfl⟩
      simp [hc, this]
    refine (hinj.hasSum_iff hsupp).mp ?_
    convert hs using 1
    ext m
    simp [hc, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd)]
  have key := qExpansion_coeff_unique' hGdiff.continuous han hsum n
  show (qExpansion 1 G).coeff n = if d ∣ n then (qExpansion 1 F).coeff (n / d) else 0
  exact key.symm

private theorem qCoeff_comp_smul_of_modularFormClass {FF : Type*} [FunLike FF ℍ ℂ]
    {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [ModularFormClass FF Γ k] (f : FF)
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {d : ℕ} (hd : d ≠ 0) (n : ℕ) :
    qCoeff (fun τ ↦ f (heckeDiagMatrix d • τ)) n =
      if d ∣ n then qCoeff f (n / d) else 0 :=
  haveI : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  qCoeff_comp_smul hd (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ) (holo f)
    (bdd_at_infty f) n

/-! ## The public targets (verbatim from their wrappers)

The declarations are written with their **dotted** wrapper names (`theorem
UpperHalfPlane.qCoeff_heckeU …`, not inside the namespace). The checker matches
declarations by last name, and the same last name occurs in both the
`UpperHalfPlane` and the `ModularFormClass` wrapper; the dotted spelling routes
each copy through the checker's dotted fallback (the pin wrappers are themselves
dotted), so no `SOURCES` ordering can flip one onto the other. -/

/-- `U_p` acts on `q`-coefficients through `coeffHeckeU`. Stated verbatim from
`Theorems/Thm_UpperHalfPlane_qCoeff_heckeU.lean`. -/
theorem UpperHalfPlane.qCoeff_heckeU {f : UpperHalfPlane → ℂ} (hper : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) 1) (hhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f) (hbdd : UpperHalfPlane.IsBoundedAtImInfty f) (k : ℤ) {p : ℕ} (hp : p ≠ 0) (n : ℕ) : ModularFormClass.qCoeff (ModularForm.heckeU k p f) n = ModularForm.coeffHeckeU p (ModularFormClass.qCoeff f) n :=
  qCoeff_heckeU_bare hp hper hhol hbdd k n

/-- `T_p` acts on `q`-coefficients through `coeffHeckeT`. Stated verbatim from
`Theorems/Thm_UpperHalfPlane_qCoeff_heckeT.lean`. -/
theorem UpperHalfPlane.qCoeff_heckeT {f : UpperHalfPlane → ℂ} (hper : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) 1) (hhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f) (hbdd : UpperHalfPlane.IsBoundedAtImInfty f) (k : ℤ) {p : ℕ} (hp : p ≠ 0) (n : ℕ) : ModularFormClass.qCoeff (ModularForm.heckeT k p f) n = ModularForm.coeffHeckeT k p (ModularFormClass.qCoeff f) n :=
  qCoeff_heckeT_bare hp hper hhol hbdd k n

/-- The diagonal translate scales the `q`-parameter by `d`. Stated verbatim from
`Theorems/Thm_UpperHalfPlane_qCoeff_comp_heckeDiagMatrix_smul.lean`. -/
theorem UpperHalfPlane.qCoeff_comp_heckeDiagMatrix_smul {f : UpperHalfPlane → ℂ} (hper : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) 1) (hhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f) (hbdd : UpperHalfPlane.IsBoundedAtImInfty f) {d : ℕ} (hd : d ≠ 0) (n : ℕ) : ModularFormClass.qCoeff (fun τ ↦ f (ModularForm.heckeDiagMatrix d • τ)) n = if d ∣ n then ModularFormClass.qCoeff f (n / d) else 0 :=
  qCoeff_comp_smul hd hper hhol hbdd n

/-- Two periodic, holomorphic, bounded functions with equal `q`-coefficients are
equal. Stated verbatim from `Theorems/Thm_UpperHalfPlane_eq_of_forall_qCoeff_eq.lean`. -/
theorem UpperHalfPlane.eq_of_forall_qCoeff_eq {f g : UpperHalfPlane → ℂ} (hfper : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) 1) (hfhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f) (hfbdd : UpperHalfPlane.IsBoundedAtImInfty f) (hgper : Function.Periodic (g ∘ UpperHalfPlane.ofComplex) 1) (hghol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) g) (hgbdd : UpperHalfPlane.IsBoundedAtImInfty g) (h : ∀ n : ℕ, ModularFormClass.qCoeff f n = ModularFormClass.qCoeff g n) : f = g := by
  funext τ
  have hf := hasSum_qCoeff hfper hfhol hfbdd τ
  have hg := hasSum_qCoeff hgper hghol hgbdd τ
  simp only [h] at hf
  exact hf.unique hg

/-- The bundled form of `UpperHalfPlane.qCoeff_heckeU`. Stated verbatim from
`Theorems/Thm_ModularFormClass_qCoeff_heckeU.lean`. -/
theorem ModularFormClass.qCoeff_heckeU {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {p : ℕ} (hp : p ≠ 0) (n : ℕ) : ModularFormClass.qCoeff (ModularForm.heckeU k p f) n = ModularForm.coeffHeckeU p (ModularFormClass.qCoeff f) n :=
  qCoeff_heckeU_class hp f hΓ n

/-- The bundled form of `UpperHalfPlane.qCoeff_heckeT`. Stated verbatim from
`Theorems/Thm_ModularFormClass_qCoeff_heckeT.lean`. -/
theorem ModularFormClass.qCoeff_heckeT {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {p : ℕ} (hp : p ≠ 0) (n : ℕ) : ModularFormClass.qCoeff (ModularForm.heckeT k p f) n = ModularForm.coeffHeckeT k p (ModularFormClass.qCoeff f) n :=
  qCoeff_heckeT_class hp f hΓ n

/-- The bundled form of the diagonal dilation. Stated verbatim from
`Theorems/Thm_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul.lean`. -/
theorem ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {d : ℕ} (hd : d ≠ 0) (n : ℕ) : ModularFormClass.qCoeff (fun τ ↦ f (ModularForm.heckeDiagMatrix d • τ)) n = if d ∣ n then ModularFormClass.qCoeff f (n / d) else 0 :=
  qCoeff_comp_smul_of_modularFormClass f hΓ hd n

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

namespace ModularForm

/-! ### The level-one diagonal degeneration

The target identifies the diagonal translate with `ModularCurve.qExpand`. The pin
routes through `ModularForm.exists_degeneracy_Gamma0` and
`ModularCurve.laurent_qParam_coeff_unique`; neither is in the port, so the proof
below compares coefficients directly through the tail's
`qExpansion_coeff_unique'`. The first private lemma is the bridge
`qExpand ↦ PowerSeries.heckeV`. -/

/-- The `q`-expansion of a `PowerSeries` has no negative coefficients. -/
private theorem coe_powerSeries_coeff_of_neg (p : PowerSeries ℂ) {k : ℤ} (hk : k < 0) :
    ((p : LaurentSeries ℂ)).coeff k = 0 := by
  rw [show (p : LaurentSeries ℂ) = HahnSeries.ofPowerSeries ℤ ℂ p from rfl]
  rw [HahnSeries.ofPowerSeries_apply]
  exact HahnSeries.embDomain_of_notMem_range (by
    rintro ⟨m, rfl⟩
    exact absurd hk (not_lt.mpr (Int.natCast_nonneg m)))

/-- `qExpand` agrees with the formal dilation `PowerSeries.heckeV` on a power
series. -/
private theorem qExpand_coe_heckeV (N : ℕ) [NeZero N] (φ : PowerSeries ℂ) :
    ModularCurve.qExpand ℂ N ((φ : LaurentSeries ℂ))
      = ((PowerSeries.heckeV N φ : PowerSeries ℂ) : LaurentSeries ℂ) := by
  ext k
  rcases lt_or_ge k 0 with hk | hk
  · by_cases hdvd : (N : ℤ) ∣ k
    · obtain ⟨j, rfl⟩ := hdvd
      have hj : j < 0 := by
        have hN : (0 : ℤ) < N := by exact_mod_cast NeZero.pos N
        nlinarith
      have hNj : (N : ℤ) * j < 0 := by
        have hN : (0 : ℤ) < N := by exact_mod_cast NeZero.pos N
        nlinarith
      rw [ModularCurve.qExpand_coeff_mul (N := N) (f := (φ : LaurentSeries ℂ)),
        coe_powerSeries_coeff_of_neg _ hj, coe_powerSeries_coeff_of_neg _ hNj]
    · rw [ModularCurve.qExpand_coeff_of_not_dvd (N := N) (f := (φ : LaurentSeries ℂ)) hdvd,
        coe_powerSeries_coeff_of_neg _ hk]
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    by_cases h : N ∣ m
    · obtain ⟨j, rfl⟩ := h
      rw [show (((N * j : ℕ) : ℤ)) = (N : ℤ) * (j : ℤ) by push_cast; ring]
      rw [ModularCurve.qExpand_coeff_mul (N := N) (f := (φ : LaurentSeries ℂ)),
        show ((N : ℤ) * (j : ℤ)) = ((N * j : ℕ) : ℤ) by push_cast; ring,
        LaurentSeries.coeff_coe_powerSeries,
        LaurentSeries.coeff_coe_powerSeries, PowerSeries.coeff_heckeV]
      simp [Nat.mul_div_cancel_left j (Nat.pos_of_ne_zero (NeZero.ne N))]
    · rw [ModularCurve.qExpand_coeff_of_not_dvd (N := N) (f := (φ : LaurentSeries ℂ))
          (fun hdiv => h (Int.natCast_dvd_natCast.mp hdiv)),
        LaurentSeries.coeff_coe_powerSeries, PowerSeries.coeff_heckeV]
      simp [h]

/-- The diagonal translate's `q`-expansion is `PowerSeries.heckeV`. -/
private theorem qExpansion_heckeDiagMatrix_smul_coeff (N : ℕ) [NeZero N] {k : ℤ}
    (F : ModularForm 𝒮ℒ k) (m : ℕ) :
    (qExpansion 1 (fun τ : ℍ ↦ (F : ℍ → ℂ) (heckeDiagMatrix N • τ))).coeff m =
      if N ∣ m then (qExpansion 1 (F : ℍ → ℂ)).coeff (m / N) else 0 := by
  have hN : N ≠ 0 := NeZero.ne N
  have hΓ : (1 : ℝ) ∈ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := one_mem_strictPeriods_SL
  have hperF : Periodic ((F : ℍ → ℂ) ∘ ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex F hΓ
  have hholF : MDiff (F : ℍ → ℂ) := ModularFormClass.holo F
  have hbddF : IsBoundedAtImInfty (F : ℍ → ℂ) := ModularFormClass.bdd_at_infty F
  set G : ℍ → ℂ := fun τ ↦ (F : ℍ → ℂ) (heckeDiagMatrix N • τ) with hG
  have hGdiff : MDiff G := mdifferentiable_comp_smul hN hholF
  have han : AnalyticAt ℂ (cuspFunction 1 G) 0 :=
    analyticAt_cuspFunction_zero one_pos (periodic_comp_smul hN hperF) hGdiff
      (isBoundedAtImInfty_comp_smul hN hbddF)
  set c : ℕ → ℂ := fun m ↦ if N ∣ m then (qExpansion 1 (F : ℍ → ℂ)).coeff (m / N) else 0 with hc
  have hsum : ∀ τ : ℍ, HasSum (fun m ↦ c m • Periodic.qParam 1 τ ^ m) (G τ) := by
    intro τ
    have hq : Periodic.qParam 1 ((heckeDiagMatrix N • τ : ℍ) : ℂ) = Periodic.qParam 1 τ ^ N := by
      simp only [Periodic.qParam, ← Complex.exp_nat_mul, coe_heckeDiagMatrix_smul hN]
      congr 1
      push_cast
      ring
    have hs := UpperHalfPlane.hasSum_qExpansion one_pos hperF hholF hbddF (heckeDiagMatrix N • τ)
    simp_rw [hq, ← pow_mul] at hs
    have hinj : Injective (fun m : ℕ ↦ N * m) := mul_right_injective₀ hN
    have hsupp : ∀ x ∉ Set.range (fun m : ℕ ↦ N * m),
        (fun m ↦ c m • Periodic.qParam 1 τ ^ m) x = 0 := by
      intro x hx
      have : ¬ N ∣ x := by
        rintro ⟨e, rfl⟩
        exact hx ⟨e, rfl⟩
      simp [hc, this]
    refine (hinj.hasSum_iff hsupp).mp ?_
    convert hs using 1
    ext m
    simp [hc, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hN)]
  exact (qExpansion_coeff_unique' hGdiff.continuous han hsum m).symm

/-- The level-one diagonal degeneration. Stated verbatim from
`Theorems/Thm_ModularForm_qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne.lean`. -/
theorem qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne (N : ℕ) [NeZero N] {k : ℤ} (F : ModularForm 𝒮ℒ k) : ((qExpansion 1 (fun τ : ℍ => (F : ℍ → ℂ) (ModularForm.heckeDiagMatrix N • τ)) : PowerSeries ℂ) : LaurentSeries ℂ) = ModularCurve.qExpand ℂ N ((qExpansion 1 (F : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by
  have hps : (qExpansion 1 (fun τ : ℍ ↦ (F : ℍ → ℂ) (heckeDiagMatrix N • τ)) : PowerSeries ℂ)
      = PowerSeries.heckeV N (qExpansion 1 (F : ℍ → ℂ)) := by
    ext m
    rw [qExpansion_heckeDiagMatrix_smul_coeff N F m, PowerSeries.coeff_heckeV]
  change (((qExpansion 1 (fun τ : ℍ ↦ (F : ℍ → ℂ) (heckeDiagMatrix N • τ)) : PowerSeries ℂ)) :
      LaurentSeries ℂ) = ModularCurve.qExpand ℂ N (((qExpansion 1 (F : ℍ → ℂ)) : PowerSeries ℂ) :
      LaurentSeries ℂ)
  rw [hps]
  exact (qExpand_coe_heckeV N (qExpansion 1 (F : ℍ → ℂ))).symm

/-! ### The coefficient algebra

These depend only on `Defs/HeckeOperator.lean` and are stated verbatim from their
`Theorems/` wrappers. -/

/-- `U_p` and `U_q` commute on coefficient sequences. Stated verbatim from
`Theorems/Thm_ModularForm_coeffHeckeU_comm.lean`. -/
theorem coeffHeckeU_comm (p q : ℕ) (a : ℕ → ℂ) : ModularForm.coeffHeckeU p (ModularForm.coeffHeckeU q a) = ModularForm.coeffHeckeU q (ModularForm.coeffHeckeU p a) := by
  funext n
  simp only [coeffHeckeU_apply, Nat.mul_right_comm]

/-- `T_p` commutes with `U_q` for coprime `p`, `q`. Stated verbatim from
`Theorems/Thm_ModularForm_coeffHeckeT_coeffHeckeU_comm.lean`. -/
theorem coeffHeckeT_coeffHeckeU_comm (k : ℤ) {p q : ℕ} (hpq : Nat.Coprime p q) (a : ℕ → ℂ) : ModularForm.coeffHeckeT k p (ModularForm.coeffHeckeU q a) = ModularForm.coeffHeckeU q (ModularForm.coeffHeckeT k p a) := by
  funext n
  simp only [coeffHeckeT_apply, coeffHeckeU_apply]
  have hiff : p ∣ n * q ↔ p ∣ n := hpq.dvd_mul_right
  by_cases hpn : p ∣ n
  · rw [ite_eq_left hpn, ite_eq_left (hiff.mpr hpn), Nat.mul_right_comm, Nat.div_mul_right_comm hpn]
  · rw [ite_eq_right hpn, ite_eq_right (fun h => hpn (hiff.mp h)), Nat.mul_right_comm]

/-- `T_p` and `T_q` commute for coprime `p`, `q`. Stated verbatim from
`Theorems/Thm_ModularForm_coeffHeckeT_comm.lean`. -/
theorem coeffHeckeT_comm (k : ℤ) {p q : ℕ} (hpq : Nat.Coprime p q) (a : ℕ → ℂ) : ModularForm.coeffHeckeT k p (ModularForm.coeffHeckeT k q a) = ModularForm.coeffHeckeT k q (ModularForm.coeffHeckeT k p a) := by
  funext n
  simp only [coeffHeckeT_apply]
  have hq : q ∣ n * p ↔ q ∣ n := hpq.symm.dvd_mul_right
  have hp : p ∣ n * q ↔ p ∣ n := hpq.dvd_mul_right
  have hpq' : ∀ {m : ℕ}, p ∣ m → (q ∣ m / p ↔ p * q ∣ m) := fun h =>
    Nat.dvd_div_iff_mul_dvd h
  have hqp' : ∀ {m : ℕ}, q ∣ m → (p ∣ m / q ↔ q * p ∣ m) := fun h =>
    Nat.dvd_div_iff_mul_dvd h
  by_cases hpn : p ∣ n <;> by_cases hqn : q ∣ n
  ·
    have hpqn : p * q ∣ n := hpq.mul_dvd_of_dvd_of_dvd hpn hqn
    rw [ite_eq_left (hq.mpr hqn), ite_eq_left hpn, ite_eq_left ((hpq' hpn).mpr hpqn), ite_eq_left (hp.mpr hpn),
      ite_eq_left hqn, ite_eq_left ((hqp' hqn).mpr (mul_comm p q ▸ hpqn)),
      Nat.mul_right_comm, Nat.div_mul_right_comm hqn, Nat.div_mul_right_comm hpn,
      Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm q p]
    ring
  ·
    have h1 : ¬ q ∣ n / p := fun h => hqn (Nat.dvd_trans (Nat.dvd_mul_left q p) ((hpq' hpn).mp h))
    rw [ite_eq_right (fun h => hqn (hq.mp h)), ite_eq_left hpn, ite_eq_right h1, ite_eq_left (hp.mpr hpn), ite_eq_right hqn,
      Nat.mul_right_comm, Nat.div_mul_right_comm hpn]
    ring
  ·
    have h1 : ¬ p ∣ n / q := fun h => hpn (Nat.dvd_trans (Nat.dvd_mul_left p q) ((hqp' hqn).mp h))
    rw [ite_eq_left (hq.mpr hqn), ite_eq_right hpn, ite_eq_right (fun h => hpn (hp.mp h)), ite_eq_left hqn, ite_eq_right h1,
      Nat.mul_right_comm, Nat.div_mul_right_comm hqn]
    ring
  ·
    rw [ite_eq_right (fun h => hqn (hq.mp h)), ite_eq_right hpn, ite_eq_right (fun h => hpn (hp.mp h)), ite_eq_right hqn,
      Nat.mul_right_comm]

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
