/-
  The `E₄³ − E₆²` modular-polynomial tail: `Φ` vanishes at
  `(E₄(σ)³/Δ(σ), E₄(σ')³/Δ(σ'))` for the three levels of generality the pin
  needs.

  This is the last mathematical set of row S before the capstone.  It states, in
  `ModularCurve.ModularPolynomialData`:

  * `eval_E4_cube_div_discriminant_smul_eq_zero` — `σ' = N · σ`;
  * `eval_E4_cube_div_discriminant_coset_eq_zero` — `σ' = (aσ + b)/d` for a
    primitive coset triple `(a, b, d) ∈ primCosetReps N`;
  * `eval_jLattice_eq_zero_of_isAddCyclic` — the same for a `PeriodPair` pair
    `L, L'` satisfying S-3's hypotheses.

  The three are one proof at three levels of generality: the smul form is the
  `E₄³/Δ` `q`-expansion computation over the Hecke diagonal matrix; the coset
  form reduces the primitive coset to the smul form through
  `upperTriangularGL = γ₁ · heckeDiagMatrix N · γ₂` (the `SL₂(ℤ)` Smith leaf of
  `FLTForHuman/Algebra/SpecialLinearGroupSmith.lean`); the `jLattice` form feeds
  S-3's `(a, b, d, τ, σ)` into the coset form and rewrites both `jLattice`s by
  `PeriodPair.jLattice_ofTau`.

  Pin provenance, `anthropics/fermats-last-theorem@aa2d8b3`:

  * `P2M/Sol/S_ModularCurve_ModularPolynomialData_eval_E4_cube_div_discriminant_smul_eq_zero.lean`
    (`Theorems/Thm_ModularCurve_ModularPolynomialData_eval_E4_cube_div_discriminant_smul_eq_zero.lean`)
  * `P2M/Sol/S_ModularCurve_ModularPolynomialData_eval_E4_cube_div_discriminant_coset_eq_zero.lean`
    (`Theorems/Thm_ModularCurve_ModularPolynomialData_eval_E4_cube_div_discriminant_coset_eq_zero.lean`)
  * `P2M/Sol/S_ModularCurve_ModularPolynomialData_eval_jLattice_eq_zero_of_isAddCyclic.lean`
    (`Theorems/Thm_ModularCurve_ModularPolynomialData_eval_jLattice_eq_zero_of_isAddCyclic.lean`)

  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_ModularPolynomialData_eval_E4_cube_div_discriminant_smul_eq_zero.lean>

  The pin's three `S_` files carry their public helper surface at the namespaces
  `ModularCurve.DeepCosetAux` (the `E₄³`/`Δ` forms and the `q`-expansion
  bookkeeping) and `ModularCurve.CosetRootAux` (`jt` and the `upperTriangularGL`
  pair), which the port keeps verbatim; the helpers the pin declares `private`
  are not transcribed.  The pin's `attribute [-instance]`/`[-simp]` lines and its
  heartbeat bumps are not transcribed.  The heavy inputs are imported:
  `ModularForm.exists_degeneracy_Gamma0`, `heckeDiagMatrix`/`coe_heckeDiagMatrix_smul`,
  `upperTriangularGL`/`val_upperTriangularGL`/`val_heckeDiagMatrix`,
  `jqModC_eq_qExpansion_E4_cube_div_discriminant`, `primCosetReps`/`mem_primCosetReps`,
  `PeriodPair.jLattice_ofTau` and S-3's `exists_mem_primCosetReps_and_jLattice_eq_of_isAddCyclic`.
-/
import FLTForHuman.ModularCurve.ModularPolynomialAssembly
import FLTForHuman.ModularCurve.ModularPolynomialIrreducible
import FLTForHuman.ModularCurve.ModularPolynomialProperties
import FLTForHuman.ModularCurve.ModularPolynomialUniqueness
import FLTForHuman.ModularCurve.Defs.PrimCosetReps
import FLTForHuman.ModularCurve.JqIntegralRatios
import FLTForHuman.ModularForms.JInvariant
import FLTForHuman.ModularForms.DiscPow
import FLTForHuman.ModularForms.HeckeQExpansion
import FLTForHuman.ModularForms.HeckeQCoeff
import FLTForHuman.ModularForms.Level.Degeneracy
import FLTForHuman.ModularForms.Gamma1Vanishing
import FLTForHuman.ModularForms.Defs.HeckeOperator
import FLTForHuman.Algebra.SpecialLinearGroupSmith
import FLTForHuman.Elliptic.PeriodPair.PrimCosetReps
import FLTForHuman.Elliptic.PeriodPair.Lattice
import FLTForHuman.Elliptic.PeriodPair.JLine

set_option autoImplicit false

-- The pin's `haveI` walls and its `upperTriangularGL_eq` binder list are
-- load-bearing for the statement; keep them literal (port convention).
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
-- The pin's defensive `first | ... | ...` fallbacks (in `upperTriangularGL_eq`
-- and the `hformal` step) carry alternatives that the current mathlib makes
-- unreachable; they are transcribed as they stand.
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

noncomputable section

open UpperHalfPlane Polynomial
open scoped Matrix MatrixGroups

namespace ModularCurve

namespace DeepCosetAux

theorem gamma0_one_eq_top : CongruenceSubgroup.Gamma0 1 = ⊤ := by
  ext A
  simp [CongruenceSubgroup.Gamma0_mem, eq_iff_true_of_subsingleton]

theorem gamma0_one_coe :
    ((CongruenceSubgroup.Gamma0 1 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) = 𝒮ℒ := by
  simp [gamma0_one_eq_top, MonoidHom.range_eq_map]

theorem heckeDiagMatrix_one : ModularForm.heckeDiagMatrix 1 = 1 := by
  apply Units.ext
  simp [Matrix.one_fin_two]

theorem one_mem_sp (M : ℕ) : (1 : ℝ) ∈
    ((CongruenceSubgroup.Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma0]
  exact AddSubgroup.mem_zmultiples 1

def e4cubeSL : ModularForm 𝒮ℒ 12 :=
  ModularForm.mcast (by norm_num) ((ModularForm.E₄.mul ModularForm.E₄).mul ModularForm.E₄)

theorem coe_e4cubeSL : ⇑e4cubeSL = fun τ => (ModularForm.E₄ : ℍ → ℂ) τ ^ 3 := by
  funext τ
  show (((ModularForm.E₄.mul ModularForm.E₄).mul ModularForm.E₄ : ModularForm 𝒮ℒ _) : ℍ → ℂ) τ = _
  rw [ModularForm.coe_mul, ModularForm.coe_mul]
  simp only [Pi.mul_apply]
  ring

def deltaSL : ModularForm 𝒮ℒ 12 := CuspForm.toModularFormₗ CuspForm.discriminant

theorem coe_deltaSL : ⇑deltaSL = ModularForm.discriminant := by
  show ⇑(CuspForm.toModularFormₗ CuspForm.discriminant) = _
  rw [← CuspForm.coe_discriminant]
  rfl

def e4cube1 : ModularForm (CongruenceSubgroup.Gamma0 1) 12 := ModularForm.mcast rfl e4cubeSL gamma0_one_coe
def delta1 : ModularForm (CongruenceSubgroup.Gamma0 1) 12 := ModularForm.mcast rfl deltaSL gamma0_one_coe
theorem coe_e4cube1 : ⇑e4cube1 = ⇑e4cubeSL := rfl
theorem coe_delta1 : ⇑delta1 = ⇑deltaSL := rfl

/-! ### The pin's `q`-expansion bookkeeping

`An f` is "the `q`-expansion of `f` is analytic at `0`".  The two `Finset`
lemmas push `qExpansion 1` through finite products and finite `ℂ`-linear
combinations, `pow_mul_div_pow` is the elementary power bookkeeping, and the
`Mono` section builds the weight-`12 (m + n)` form whose `q`-expansion is
`(E₄³)^k Δ^(m-k) (E₄³(N·))^i Δ(N·)^(n-i)`. -/

def An (f : ℍ → ℂ) : Prop := AnalyticAt ℂ (cuspFunction 1 f) 0

theorem an_of_modularForm {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [Γ.HasDetPlusMinusOne]
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (f : ModularForm Γ k) : An ⇑f := by
  haveI : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  exact UpperHalfPlane.analyticAt_cuspFunction_zero one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ) (ModularFormClass.holo f)
    (ModularFormClass.bdd_at_infty f)

theorem An.mul {f g : ℍ → ℂ} (hf : An f) (hg : An g) : An (f * g) := by
  unfold An at *
  rw [UpperHalfPlane.cuspFunction_mul hf.continuousAt hg.continuousAt]
  exact hf.mul hg

theorem An.add {f g : ℍ → ℂ} (hf : An f) (hg : An g) : An (f + g) := by
  unfold An at *
  rw [UpperHalfPlane.cuspFunction_add hf.continuousAt hg.continuousAt]
  exact hf.add hg

theorem An.smul {f : ℍ → ℂ} (hf : An f) (c : ℂ) : An (c • f) := by
  unfold An at *
  rw [UpperHalfPlane.cuspFunction_smul hf.continuousAt]
  exact hf.const_smul

theorem qExpansion_finset_prod {ι : Type*} (s : Finset ι) (f : ι → ℍ → ℂ) (h : ∀ l ∈ s, An (f l))
    (h1 : An (1 : ℍ → ℂ)) :
    An (∏ l ∈ s, f l) ∧ qExpansion 1 (∏ l ∈ s, f l) = ∏ l ∈ s, qExpansion 1 (f l) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simpa using h1, by simp [UpperHalfPlane.qExpansion_one]⟩
  | insert a s ha ih =>
    obtain ⟨hA, hq⟩ := ih (fun l hl => h l (Finset.mem_insert_of_mem hl))
    have hfa : An (f a) := h a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact ⟨hfa.mul hA, by rw [UpperHalfPlane.qExpansion_mul hfa hA, hq]⟩

theorem qExpansion_finset_sum_smul {ι : Type*} (s : Finset ι) (c : ι → ℂ) (f : ι → ℍ → ℂ)
    (h : ∀ l ∈ s, An (f l)) (h0 : An (0 : ℍ → ℂ)) :
    An (∑ l ∈ s, c l • f l) ∧ qExpansion 1 (∑ l ∈ s, c l • f l) = ∑ l ∈ s, c l • qExpansion 1 (f l) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simpa using h0, by simp [UpperHalfPlane.qExpansion_zero]⟩
  | insert a s ha ih =>
    obtain ⟨hA, hq⟩ := ih (fun l hl => h l (Finset.mem_insert_of_mem hl))
    have hfa : An (c a • f a) := (h a (Finset.mem_insert_self a s)).smul (c a)
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine ⟨hfa.add hA, ?_⟩
    rw [UpperHalfPlane.qExpansion_add hfa hA, hq,
      UpperHalfPlane.qExpansion_smul (h a (Finset.mem_insert_self a s))]

theorem pow_mul_div_pow {K : Type*} [Field K] (x D : K) (hD : D ≠ 0) {k m : ℕ} (hk : k ≤ m) :
    D ^ m * (x / D) ^ k = x ^ k * D ^ (m - k) := by
  have hDk : D ^ k ≠ 0 := pow_ne_zero _ hD
  calc D ^ m * (x / D) ^ k = D ^ (k + (m - k)) * (x / D) ^ k := by rw [Nat.add_sub_cancel' hk]
    _ = D ^ (m - k) * (D ^ k * (x ^ k / D ^ k)) := by rw [_root_.pow_add, div_pow]; ring
    _ = D ^ (m - k) * x ^ k := by rw [mul_div_assoc', mul_div_cancel_left₀ _ hDk]
    _ = x ^ k * D ^ (m - k) := mul_comm _ _

section Mono

variable {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetPlusMinusOne]

def fam (e δ eN δN : ModularForm Γ 12) (m n i k : ℕ) : Fin m ⊕ Fin n → ModularForm Γ 12 :=
  Sum.elim (fun l : Fin m => if (l : ℕ) < k then e else δ) (fun l : Fin n => if (l : ℕ) < i then eN else δN)

theorem card_univ_mul (m n : ℕ) :
    (((Finset.univ : Finset (Fin m ⊕ Fin n)).card : ℕ) : ℤ) * 12 = 12 * ((m + n : ℕ) : ℤ) := by
  simp [Finset.card_univ, Fintype.card_sum, Fintype.card_fin]
  ring

def mono (e δ eN δN : ModularForm Γ 12) (m n i k : ℕ) : ModularForm Γ (12 * ((m + n : ℕ) : ℤ)) :=
  ModularForm.mcast (card_univ_mul m n) (ModularForm.prodEqualWeights (s := Finset.univ) (fam e δ eN δN m n i k))

theorem prod_ite_pow {M : Type*} [CommMonoid M] (p q : ℕ) (hpq : q ≤ p) (x y : M) :
    (∏ l : Fin p, if (l : ℕ) < q then x else y) = x ^ q * y ^ (p - q) := by
  rw [Fin.prod_univ_eq_prod_range (fun l => if l < q then x else y) p, Finset.prod_ite, Finset.prod_const,
    Finset.prod_const]
  congr 2
  · rw [show (Finset.range p).filter (fun l => l < q) = Finset.range q from by
      ext l; simp only [Finset.mem_filter, Finset.mem_range]; omega]
    exact Finset.card_range q
  · rw [show (Finset.range p).filter (fun l => ¬ l < q) = Finset.Ico q p from by
      ext l; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega]
    exact Nat.card_Ico q p

theorem coe_mono (e δ eN δN : ModularForm Γ 12) {m n i k : ℕ} (hi : i ≤ n) (hk : k ≤ m) :
    ⇑(mono e δ eN δN m n i k) = (⇑e) ^ k * (⇑δ) ^ (m - k) * ((⇑eN) ^ i * (⇑δN) ^ (n - i)) := by
  show ⇑(ModularForm.prodEqualWeights (s := Finset.univ) (fam e δ eN δN m n i k)) = _
  rw [ModularForm.coe_prodEqualWeights, Fintype.prod_sum_type]
  simp only [fam, Sum.elim_inl, Sum.elim_inr]
  rw [show (∏ l : Fin m, ⇑(if (l : ℕ) < k then e else δ)) = ∏ l : Fin m, (if (l : ℕ) < k then (⇑e) else (⇑δ)) from
      Finset.prod_congr rfl (fun l _ => by split_ifs <;> rfl),
    show (∏ l : Fin n, ⇑(if (l : ℕ) < i then eN else δN)) = ∏ l : Fin n, (if (l : ℕ) < i then (⇑eN) else (⇑δN)) from
      Finset.prod_congr rfl (fun l _ => by split_ifs <;> rfl),
    prod_ite_pow m k hk, prod_ite_pow n i hi]

def coeAddHom (k : ℤ) : ModularForm Γ k →+ (ℍ → ℂ) :=
  { toFun := fun f => ⇑f, map_zero' := rfl, map_add' := fun _ _ => rfl }

end Mono

end DeepCosetAux

namespace CosetRootAux

/-- The level-one modular function `j = E₄³ / Δ`, at the pin's local name. -/
def jt (z : ℍ) : ℂ := (ModularForm.E₄ : ℍ → ℂ) z ^ 3 / ModularForm.discriminant z

theorem sl_mem (γ : SL(2, ℤ)) : (γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩

theorem jt_smul (γ : SL(2, ℤ)) (z : ℍ) : jt ((γ : GL (Fin 2) ℝ) • z) = jt z := by
  unfold jt
  have h4 := SlashInvariantForm.slash_action_eqn'' (ModularForm.E₄) (sl_mem γ) z
  have h12 := SlashInvariantForm.slash_action_eqn'' (CuspForm.discriminant) (sl_mem γ) z
  rw [CuspForm.coe_discriminant] at h12
  have hd : denom (γ : GL (Fin 2) ℝ) (z : ℂ) ≠ 0 := UpperHalfPlane.denom_ne_zero _ z
  have hΔ : ModularForm.discriminant z ≠ 0 := ModularForm.discriminant_ne_zero z
  rw [show (ModularForm.E₄ : ℍ → ℂ) ((γ : GL (Fin 2) ℝ) • z) = ModularForm.E₄ ((γ : GL (Fin 2) ℝ) • z) from rfl, h4, h12]
  field_simp

theorem upperTriangularGL_eq {N a b d : ℕ} (hN : N ≠ 0) (had : a * d = N) (γ₁ γ₂ : SL(2, ℤ))
    (hM : !![(a : ℤ), b; 0, d] = (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) * !![(N : ℤ), 0; 0, 1] * (γ₂ : Matrix (Fin 2) (Fin 2) ℤ))
    (had' : (a : ℝ) * d ≠ 0) :
    ModularForm.upperTriangularGL a b d had' = (γ₁ : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix N * (γ₂ : GL (Fin 2) ℝ) := by
  apply Units.ext
  have hmap := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M.map (Int.castRingHom ℝ)) hM
  simp only [Matrix.map_mul] at hmap
  rw [Units.val_mul, Units.val_mul, ModularForm.val_upperTriangularGL, ModularForm.val_heckeDiagMatrix hN]
  convert hmap using 3 <;> first | rfl | (ext i j; fin_cases i <;> fin_cases j <;> simp) | (ext i j; fin_cases i <;> fin_cases j <;> rfl)

theorem coe_upperTriangularGL_smul {a b d : ℕ} (ha : 0 < a) (hd : 0 < d) (had' : (a : ℝ) * d ≠ 0) (τ : ℍ) :
    ((ModularForm.upperTriangularGL a b d had' • τ : ℍ) : ℂ) = ((a : ℂ) * τ + b) / d := by
  have hdet : 0 < ((ModularForm.upperTriangularGL (a : ℝ) b d had').det : ℝ) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, ModularForm.val_upperTriangularGL, Matrix.det_fin_two_of]
    have : (0 : ℝ) < a * d := mul_pos (by exact_mod_cast ha) (by exact_mod_cast hd)
    linarith
  rw [UpperHalfPlane.coe_smul_of_det_pos hdet]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, ModularForm.val_upperTriangularGL]

end CosetRootAux

namespace ModularPolynomialData

open DeepCosetAux

/-- **The smul form.** For `σ' = N · σ`, the modular polynomial `Φ` evaluated at
`(E₄(σ)³/Δ(σ), E₄(σ')³/Δ(σ'))` vanishes.  Statement verbatim from
`Theorems/Thm_ModularCurve_ModularPolynomialData_eval_E4_cube_div_discriminant_smul_eq_zero.lean`. -/
theorem eval_E4_cube_div_discriminant_smul_eq_zero (N : ℕ) [NeZero N]
    (data : ModularCurve.ModularPolynomialData N) (σ σ' : ℍ) (hσ' : (σ' : ℂ) = (N : ℂ) * σ) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom ℂ)
        ((ModularForm.E₄ : ℍ → ℂ) σ ^ 3 / ModularForm.discriminant σ))).eval
      ((ModularForm.E₄ : ℍ → ℂ) σ' ^ 3 / ModularForm.discriminant σ') = 0 := by
  classical
  have hN : N ≠ 0 := NeZero.ne N

  have hσ'pt : σ' = ModularForm.heckeDiagMatrix N • σ :=
    UpperHalfPlane.ext (by rw [hσ', ModularForm.coe_heckeDiagMatrix_smul hN])

  obtain ⟨e, he⟩ := ModularForm.exists_degeneracy_Gamma0 (show 1 * 1 ∣ N by simp) e4cube1
  obtain ⟨δ, hδ⟩ := ModularForm.exists_degeneracy_Gamma0 (show 1 * 1 ∣ N by simp) delta1
  obtain ⟨eN, heN⟩ := ModularForm.exists_degeneracy_Gamma0 (show N * 1 ∣ N by simp) e4cube1
  obtain ⟨δN, hδN⟩ := ModularForm.exists_degeneracy_Gamma0 (show N * 1 ∣ N by simp) delta1
  have he' : ⇑e = fun τ => (ModularForm.E₄ : ℍ → ℂ) τ ^ 3 := by
    rw [he, heckeDiagMatrix_one]; funext τ; rw [one_smul, coe_e4cube1, coe_e4cubeSL]
  have hδ' : ⇑δ = ModularForm.discriminant := by
    rw [hδ, heckeDiagMatrix_one]; funext τ; rw [one_smul, coe_delta1, coe_deltaSL]
  have heN' : ⇑eN = fun τ => e4cubeSL (ModularForm.heckeDiagMatrix N • τ) := by rw [heN]; rfl
  have hδN' : ⇑δN = fun τ => deltaSL (ModularForm.heckeDiagMatrix N • τ) := by rw [hδN]; rfl

  set A : LaurentSeries ℂ := ((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) with hA
  set D : LaurentSeries ℂ := ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
    with hD
  set J : LaurentSeries ℂ := jqModC ℂ with hJ
  have hJAD : J = A ^ 3 / D := ModularCurve.jqModC_eq_qExpansion_E4_cube_div_discriminant
  have hD0 : D ≠ 0 := by
    intro h0
    have : J = 0 := by rw [hJAD, h0, div_zero]
    have h1 : J.coeff (-1) = 1 := by
      rw [hJ, jqModC]
      have h := HahnSeries.coeff_single_mul_add (a := (0 : ℤ)) (b := (-1 : ℤ)) (r := (1 : ℂ))
        (x := HahnSeries.ofPowerSeries ℤ ℂ (jNum.map (Int.castRingHom ℂ)))
      rw [zero_add, one_mul] at h
      rw [h]
      have h0' := HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ) (jNum.map (Int.castRingHom ℂ)) 0
      rw [Nat.cast_zero] at h0'
      rw [h0', PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_jNum, map_one]
    rw [this, HahnSeries.coeff_zero] at h1
    exact zero_ne_one h1

  have hΓ := one_mem_sp N
  have hAn4 : An (ModularForm.E₄ : ℍ → ℂ) := an_of_modularForm one_mem_strictPeriods_SL ModularForm.E₄
  have hqe4cube : ((qExpansion 1 (e4cubeSL : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) = A ^ 3 := by
    have h3 : (e4cubeSL : ℍ → ℂ) = (ModularForm.E₄ : ℍ → ℂ) * (ModularForm.E₄ : ℍ → ℂ) * (ModularForm.E₄ : ℍ → ℂ) := by
      rw [coe_e4cubeSL]; funext τ; simp [pow_succ]
    rw [h3, UpperHalfPlane.qExpansion_mul (hAn4.mul hAn4) hAn4, UpperHalfPlane.qExpansion_mul hAn4 hAn4, hA]
    simp [pow_succ, PowerSeries.coe_mul]
  have hqe : ((qExpansion 1 (e : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) = A ^ 3 := by
    rw [show (e : ℍ → ℂ) = (e4cubeSL : ℍ → ℂ) from by rw [he', coe_e4cubeSL], hqe4cube]
  have hqδ : ((qExpansion 1 (δ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) = D := by rw [hδ']
  have hqeN : ((qExpansion 1 (eN : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) = qExpand ℂ N (A ^ 3) := by
    rw [heN', ModularForm.qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne N e4cubeSL, hqe4cube]
  have hqδN : ((qExpansion 1 (δN : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) = qExpand ℂ N D := by
    rw [hδN', ModularForm.qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne N deltaSL, coe_deltaSL]

  set n : ℕ := data.Φ.natDegree with hn
  set m : ℕ := (Finset.range (n + 1)).sup (fun i => (data.Φ.coeff i).natDegree) with hm
  have hmi : ∀ i ∈ Finset.range (n + 1), (data.Φ.coeff i).natDegree ≤ m := fun i hi =>
    Finset.le_sup (f := fun i => (data.Φ.coeff i).natDegree) hi
  set c : ℕ → ℕ → ℝ := fun i k => (((data.Φ.coeff i).coeff k : ℤ) : ℝ) with hc

  have an_mf : ∀ f : ModularForm (CongruenceSubgroup.Gamma0 N) 12, An ⇑f := fun f => an_of_modularForm hΓ f
  have qexp_pow : ∀ (f : ℍ → ℂ) (hf : An f) (p : ℕ), An (f ^ p) ∧ qExpansion 1 (f ^ p) = qExpansion 1 f ^ p := by
    intro f hf p
    have := qExpansion_finset_prod (Finset.range p) (fun _ => f) (fun _ _ => hf)
      (by simpa [ModularForm.one_coe_eq_one] using
        an_of_modularForm hΓ (1 : ModularForm (CongruenceSubgroup.Gamma0 N) 0))
    simpa [Finset.prod_const, Finset.card_range] using this
  have an_mf' : ∀ f : ModularForm (CongruenceSubgroup.Gamma0 N) (12 * ((m + n : ℕ) : ℤ)), An ⇑f :=
    fun f => an_of_modularForm hΓ f
  have qexp_mono : ∀ i k, i ≤ n → k ≤ m → An ((mono e δ eN δN m n i k) : ℍ → ℂ) ∧
      (((qExpansion 1 ((mono e δ eN δN m n i k) : ℍ → ℂ)) : PowerSeries ℂ) : LaurentSeries ℂ)
        = (A ^ 3) ^ k * D ^ (m - k) * ((qExpand ℂ N (A ^ 3)) ^ i * (qExpand ℂ N D) ^ (n - i)) := by
    intro i k hi hk
    refine ⟨an_mf' _, ?_⟩
    rw [coe_mono e δ eN δN hi hk]
    obtain ⟨a1, q1⟩ := qexp_pow _ (an_mf e) k
    obtain ⟨a2, q2⟩ := qexp_pow _ (an_mf δ) (m - k)
    obtain ⟨a3, q3⟩ := qexp_pow _ (an_mf eN) i
    obtain ⟨a4, q4⟩ := qexp_pow _ (an_mf δN) (n - i)
    rw [UpperHalfPlane.qExpansion_mul (a1.mul a2) (a3.mul a4), UpperHalfPlane.qExpansion_mul a1 a2,
      UpperHalfPlane.qExpansion_mul a3 a4, q1, q2, q3, q4]
    simp only [PowerSeries.coe_mul, PowerSeries.coe_pow]
    rw [hqe, hqδ, hqeN, hqδN]

  let idx : Finset (ℕ × ℕ) := Finset.range (n + 1) ×ˢ Finset.range (m + 1)
  let H : ModularForm (CongruenceSubgroup.Gamma0 N) (12 * ((m + n : ℕ) : ℤ)) :=
    ∑ p ∈ idx, c p.1 p.2 • mono e δ eN δN m n p.1 p.2
  have hidx : ∀ p ∈ idx, p.1 ≤ n ∧ p.2 ≤ m := by
    intro p hp
    simp only [idx, Finset.mem_product, Finset.mem_range] at hp
    omega

  have hHcoe : (H : ℍ → ℂ) = ∑ p ∈ idx, ((c p.1 p.2 : ℝ) : ℂ) • ((mono e δ eN δN m n p.1 p.2) : ℍ → ℂ) := by
    show coeAddHom _ H = _
    rw [map_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    show ⇑(c p.1 p.2 • mono e δ eN δN m n p.1 p.2) = _
    rw [FunLike.coe_smul]
    funext τ
    simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul]

  have hformal : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℂ)) J)).eval (qExpand ℂ N J) = 0 := by

    have h0 := data.eval_eq_zero
    have h1 := congrArg (coeffMap (algebraMap ℚ ℂ)) h0
    rw [map_zero, Polynomial.hom_eval₂] at h1
    have hcomp : (coeffMap (algebraMap ℚ ℂ)).comp evalAtJ
        = Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℂ)) J := by
      refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
      rw [RingHom.coe_comp, Function.comp_apply, evalAtJ_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
        hJ, ← jqModC_rat]
      exact map_jqModC (algebraMap ℚ ℂ)
    have hjN : coeffMap (algebraMap ℚ ℂ) (jqN N) = qExpand ℂ N J := by
      rw [hJ, ← map_jqModC (algebraMap ℚ ℂ) (K := ℚ), jqModC_rat]
      show coeffMap (algebraMap ℚ ℂ) (qExpand ℚ N jq) = qExpand ℂ N (coeffMap (algebraMap ℚ ℂ) jq)
      ext k
      by_cases hk : (N : ℤ) ∣ k
      · obtain ⟨r, rfl⟩ := hk
        rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
      · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd N _ hk, qExpand_coeff_of_not_dvd N _ hk, map_zero]
    rw [hcomp, hjN] at h1
    rw [Polynomial.eval_map]
    first
    | exact h1
    | exact h1.symm
  have hqH : qExpansion 1 (H : ℍ → ℂ) = 0 := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ)
    rw [map_zero]
    show (((qExpansion 1 (H : ℍ → ℂ)) : PowerSeries ℂ) : LaurentSeries ℂ) = 0
    rw [hHcoe]
    obtain ⟨-, hq⟩ := qExpansion_finset_sum_smul idx (fun p => ((c p.1 p.2 : ℝ) : ℂ))
      (fun p => ((mono e δ eN δN m n p.1 p.2) : ℍ → ℂ)) (fun p _ => an_mf' _)
      (by simpa [FunLike.coe_zero] using an_of_modularForm hΓ (0 : ModularForm (CongruenceSubgroup.Gamma0 N) 0))
    rw [hq, map_sum]
    have hterm : ∀ p ∈ idx, ((((c p.1 p.2 : ℝ) : ℂ) • qExpansion 1 ((mono e δ eN δN m n p.1 p.2) : ℍ → ℂ) : PowerSeries ℂ) :
        LaurentSeries ℂ) = D ^ m * (qExpand ℂ N D) ^ n *
          (HahnSeries.C ((c p.1 p.2 : ℝ) : ℂ) * J ^ p.2 * (qExpand ℂ N J) ^ p.1) := by
      intro p hp
      obtain ⟨hi, hk⟩ := hidx p hp
      rw [PowerSeries.coe_smul, (qexp_mono p.1 p.2 hi hk).2, hJAD, map_div₀, map_pow]
      have hDN0 : qExpand ℂ N D ≠ 0 := fun h => hD0 (qExpand_injective N (by rw [h, map_zero]))
      rw [← HahnSeries.C_mul_eq_smul]
      rw [show D ^ m * qExpand ℂ N D ^ n * (HahnSeries.C ((c p.1 p.2 : ℝ) : ℂ) * (A ^ 3 / D) ^ p.2 *
            ((qExpand ℂ N A) ^ 3 / qExpand ℂ N D) ^ p.1)
          = HahnSeries.C ((c p.1 p.2 : ℝ) : ℂ) * (D ^ m * (A ^ 3 / D) ^ p.2) *
            (qExpand ℂ N D ^ n * ((qExpand ℂ N A) ^ 3 / qExpand ℂ N D) ^ p.1) by ring,
        pow_mul_div_pow _ _ hD0 hk, pow_mul_div_pow _ _ hDN0 hi]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    suffices hsum : ∑ p ∈ idx, HahnSeries.C ((c p.1 p.2 : ℝ) : ℂ) * J ^ p.2 * (qExpand ℂ N J) ^ p.1 = 0 by
      rw [hsum, mul_zero]
    rw [← hformal, Polynomial.eval_map, Polynomial.eval₂_eq_sum_range' _ (Nat.lt_succ_self _), Finset.sum_product]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_sum_range' _ (Nat.lt_succ_of_le (hmi i hi)), Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [hc, eq_intCast, Complex.ofReal_intCast]
    rw [← map_intCast (HahnSeries.C : ℂ →+* LaurentSeries ℂ)]
    try ring

  have hH0 : H = 0 := (ModularForm.qExpansion_eq_zero_iff one_pos hΓ H).mp hqH
  have hpt : (H : ℍ → ℂ) σ = 0 := by rw [hH0]; rfl
  rw [hHcoe, Finset.sum_apply] at hpt
  have hterm' : ∀ p ∈ idx, ((((c p.1 p.2 : ℝ) : ℂ)) • ((mono e δ eN δN m n p.1 p.2) : ℍ → ℂ)) σ
      = ModularForm.discriminant σ ^ m * ModularForm.discriminant σ' ^ n *
        (((c p.1 p.2 : ℝ) : ℂ) * ((ModularForm.E₄ : ℍ → ℂ) σ ^ 3 / ModularForm.discriminant σ) ^ p.2 *
          ((ModularForm.E₄ : ℍ → ℂ) σ' ^ 3 / ModularForm.discriminant σ') ^ p.1) := by
    intro p hp
    obtain ⟨hi, hk⟩ := hidx p hp
    rw [Pi.smul_apply, coe_mono e δ eN δN hi hk, smul_eq_mul]
    simp only [Pi.mul_apply, Pi.pow_apply]
    rw [he', hδ', heN', hδN', coe_e4cubeSL, coe_deltaSL]
    simp only []
    rw [← hσ'pt]
    have hd1 : ModularForm.discriminant σ ≠ 0 := ModularForm.discriminant_ne_zero σ
    have hd2 : ModularForm.discriminant σ' ≠ 0 := ModularForm.discriminant_ne_zero σ'
    rw [show ModularForm.discriminant σ ^ m * ModularForm.discriminant σ' ^ n *
          ((((c p.1 p.2 : ℝ) : ℂ)) * ((ModularForm.E₄ : ℍ → ℂ) σ ^ 3 / ModularForm.discriminant σ) ^ p.2 *
            ((ModularForm.E₄ : ℍ → ℂ) σ' ^ 3 / ModularForm.discriminant σ') ^ p.1)
        = (((c p.1 p.2 : ℝ) : ℂ)) * (ModularForm.discriminant σ ^ m *
            ((ModularForm.E₄ : ℍ → ℂ) σ ^ 3 / ModularForm.discriminant σ) ^ p.2) *
          (ModularForm.discriminant σ' ^ n * ((ModularForm.E₄ : ℍ → ℂ) σ' ^ 3 / ModularForm.discriminant σ') ^ p.1) by ring,
      pow_mul_div_pow _ _ hd1 hk, pow_mul_div_pow _ _ hd2 hi]
    ring
  rw [Finset.sum_congr rfl hterm', ← Finset.mul_sum] at hpt
  have hnz : ModularForm.discriminant σ ^ m * ModularForm.discriminant σ' ^ n ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (ModularForm.discriminant_ne_zero σ)) (pow_ne_zero _ (ModularForm.discriminant_ne_zero σ'))
  have hsum0 := (mul_eq_zero.mp hpt).resolve_left hnz

  rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range' _ (Nat.lt_succ_self _)]
  rw [Finset.sum_product] at hsum0
  rw [← hsum0]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_sum_range' _ (Nat.lt_succ_of_le (hmi i hi)), Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [hc, eq_intCast, Complex.ofReal_intCast]

/-- **The primitive-coset form.** For a primitive coset triple `(a, b, d)` and
`τ' = (aτ + b)/d`, the modular polynomial `Φ` evaluated at
`(E₄(τ)³/Δ(τ), E₄(τ')³/Δ(τ'))` vanishes.  The leaf
`Matrix.SpecialLinearGroup.exists_eq_mul_diagonal_mul_of_gcd_eq_one` supplies the
`SL₂(ℤ)` sandwich that reduces this to the smul form.  Statement verbatim from
`Theorems/Thm_ModularCurve_ModularPolynomialData_eval_E4_cube_div_discriminant_coset_eq_zero.lean`. -/
theorem eval_E4_cube_div_discriminant_coset_eq_zero (N : ℕ) [NeZero N]
    (data : ModularCurve.ModularPolynomialData N) {a b d : ℕ} (habd : (a, b, d) ∈ ModularCurve.primCosetReps N)
    (τ τ' : ℍ) (hτ' : (τ' : ℂ) = ((a : ℂ) * τ + b) / d) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom ℂ)
        ((ModularForm.E₄ : ℍ → ℂ) τ ^ 3 / ModularForm.discriminant τ))).eval
      ((ModularForm.E₄ : ℍ → ℂ) τ' ^ 3 / ModularForm.discriminant τ') = 0 := by
  have hN : N ≠ 0 := NeZero.ne N
  rw [mem_primCosetReps hN] at habd
  obtain ⟨had, hbd, hgcd⟩ := habd
  have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; exact hN (by simpa using had.symm))
  have hd : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; exact hN (by simpa using had.symm))
  have had' : (a : ℝ) * d ≠ 0 := by exact_mod_cast (mul_pos ha hd).ne'
  obtain ⟨γ₁, γ₂, hM⟩ := Matrix.SpecialLinearGroup.exists_eq_mul_diagonal_mul_of_gcd_eq_one hN had hgcd
  set g : GL (Fin 2) ℝ := ModularForm.upperTriangularGL a b d had' with hg
  have hgeq : g = (γ₁ : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix N * (γ₂ : GL (Fin 2) ℝ) :=
    CosetRootAux.upperTriangularGL_eq hN had γ₁ γ₂ hM had'
  have hτ'pt : τ' = g • τ := UpperHalfPlane.ext (by rw [hτ', hg, CosetRootAux.coe_upperTriangularGL_smul ha hd had'])
  set σ : ℍ := (γ₂ : GL (Fin 2) ℝ) • τ with hσ
  have h1 : τ' = (γ₁ : GL (Fin 2) ℝ) • (ModularForm.heckeDiagMatrix N • σ) := by
    rw [hτ'pt, hgeq, mul_smul, mul_smul]

  change (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom ℂ) (CosetRootAux.jt τ))).eval (CosetRootAux.jt τ') = 0
  rw [h1, CosetRootAux.jt_smul, show CosetRootAux.jt τ = CosetRootAux.jt σ from by rw [hσ, CosetRootAux.jt_smul]]
  exact ModularCurve.ModularPolynomialData.eval_E4_cube_div_discriminant_smul_eq_zero N data σ _
    (ModularForm.coe_heckeDiagMatrix_smul hN σ)

/-- **The `jLattice` form.** For a `PeriodPair` pair `L, L'` with `L'` a
sublattice of `L` of index `N` and cyclic quotient, the modular polynomial `Φ`
evaluated at `(L.jLattice, L'.jLattice)` vanishes.  Statement verbatim from
`Theorems/Thm_ModularCurve_ModularPolynomialData_eval_jLattice_eq_zero_of_isAddCyclic.lean`. -/
theorem eval_jLattice_eq_zero_of_isAddCyclic
    (N : ℕ) [NeZero N] (data : ModularCurve.ModularPolynomialData N) (L L' : PeriodPair)
    (hsub : (L'.lattice : Set ℂ) ⊆ L.lattice) (hidx : PeriodPair.sublatticeIndex L L' = N)
    (hcyc : IsAddCyclic (PeriodPair.sublatticeQuotient L L')) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom ℂ) L.jLattice)).eval L'.jLattice = 0 := by
  obtain ⟨a, b, d, τ, σ, habd, hσ, hjL, hjL'⟩ :=
    PeriodPair.exists_mem_primCosetReps_and_jLattice_eq_of_isAddCyclic L L' hsub hidx hcyc
  rw [hjL, hjL', PeriodPair.jLattice_ofTau, PeriodPair.jLattice_ofTau]
  exact ModularCurve.ModularPolynomialData.eval_E4_cube_div_discriminant_coset_eq_zero
    N data habd τ σ hσ

end ModularPolynomialData

end ModularCurve

end
