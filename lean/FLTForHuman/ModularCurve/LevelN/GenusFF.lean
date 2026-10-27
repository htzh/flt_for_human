/-
  The head of the dimension tower: the index/genus inequality for `X(N)`.

  The subject is the pin's
  `ModularCurve.LevelN.twelve_mul_add_mul_index_le_genusFF`

  `12 * N + N * [SL(2, ℤ) : Γ(N) ⊔ ±1] ≤ 12 * N * genusFF ℂ K + 6 * [SL(2, ℤ) : Γ(N) ⊔ ±1]`

  for a field `K` that is a fraction field of `ModularCurve.LevelN.ring N` over `ℂ` — i.e. one
  model of the function field of the modular curve `X(N)`. The proof puts the three elliptic
  points `ρ = e^{2πi/3}`, `i` and `i∞` through the Galois orbit/stabiliser dictionary at a
  place (`ord_restrictAlong_eq_natCard_algHom_of_isGalois`), and feeds the three orbits into
  the Hurwitz bound `sum_ord_sub_one_le_two_mul_genusFF_of_isSeparable`. The three orbits have
  lengths `[SL(2,ℤ) : Γ] / 3`, `/ 2` and `/ N`; the `12` and `6` are the `lcm(2,3,N)` arithmetic
  that follows.

  This is the head of W4's dimension tower (checkpoint B1): the three bound modules
  `twelve_mul_add_mul_index_le_finrank_cuspForm_Gamma`,
  `finrank_parabolicHoms_Gamma_le_two_mul_finrank_cuspForm` and
  `finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup` consume it.

  FLT provenance, pinned `aa2d8b3`:
  The proof is `P2M/Sol/S_ModularCurve_LevelN_twelve_mul_add_mul_index_le_genusFF.lean`
  (lines 38–594, the whole `ModularCurve.LevelN.GenusBound` section plus `solution`), whose
  imports are exactly the seven premises below plus the `Def_*` layer already ported. Its two
  attribute-removal walls (`-instance`, `-simp`) are not transcribed (work order D3): the build
  is silent without them, and no declaration here needed one put back.
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_ModularCurve_LevelN_twelve_mul_add_mul_index_le_genusFF.lean

  Premises, all already public in the port (imported, not re-proved):
  * `ModularCurve.LevelN.exists_monoidHom_algEquiv_fixedField_eq_adjoin` — `LevelN/FieldGalois.lean`
  * `ModularCurve.LevelN.exists_place_ord_sub_pos_forall_smul_eq`,
    `ModularCurve.LevelN.exists_place_ord_neg_forall_smul_eq` — `LevelN/Places.lean`
  * `AlgebraicCurve.Place.ord_restrictAlong_eq_natCard_algHom_of_isGalois`,
    `AlgebraicCurve.sum_ord_sub_one_le_two_mul_genusFF_of_isSeparable` —
    `AlgebraicCurve/Genus/DegreeIdentity.lean`
  * `AlgebraicCurve.Place.min_ord_le_ord_add` — `AlgebraicCurve/Defs/PlaceCalculus.lean`
  * `AlgebraicCurve.Place.ord_algebraMap` — `AlgebraicCurve/Defs/Place.lean`

  The pin's `P2M/Sol` file also carries its own `abbrev Gpm (N : ℕ)` (its line 137), used only
  inside this proof; the port has the same subgroup, public, as
  `ModularCurve.LevelN.GaloisStructure.Gpm` (`LevelN/FieldGalois.lean:262`, `N` a section
  variable, so `GaloisStructure.Gpm N` elaborates from here). This file keeps the pin's local
  `private abbrev` — the pin's shape, and it lets the proof read as the pin's does. The pin's
  `Cusp` / `instFintypeCusp` / `width` do not occur in this file at all.

  spec-pin: Theorems/Thm_ModularCurve_LevelN_twelve_mul_add_mul_index_le_genusFF.lean
  spec-pin: P2M/Sol/S_ModularCurve_LevelN_twelve_mul_add_mul_index_le_genusFF.lean   -- comparable copy
  spec-pin: Theorems/Thm_ModularCurve_twelve_mul_add_mul_index_le_finrank_cuspForm_Gamma.lean
  spec-pin: P2M/Sol/S_ModularCurve_twelve_mul_add_mul_index_le_finrank_cuspForm_Gamma.lean   -- comparable copy
-/
import FLTForHuman.ModularCurve.LevelN.FieldGalois
import FLTForHuman.ModularCurve.LevelN.Places
import FLTForHuman.AlgebraicCurve.Genus.HurwitzBound
import FLTForHuman.AlgebraicCurve.Place.OrbitCardinality
import FLTForHuman.AlgebraicCurve.Defs.PlaceCalculus
import FLTForHuman.AlgebraicCurve.Defs.Place
import FLTForHuman.AlgebraicCurve.Genus.RatFunc
import FLTForHuman.AlgebraicCurve.Canonical.RegularDifferentialsFinrank
import FLTForHuman.ModularCurve.LevelN.Differentials

set_option autoImplicit false

noncomputable section

open UpperHalfPlane

open scoped MatrixGroups IntermediateField

namespace ModularCurve.LevelN

namespace GenusBound

/-! ### Three elliptic points

`ρ = (-1 + √3 i)/2`, `i`, and `i∞`.  The first two are the fixed points of the order-3 and
order-2 elliptic elements `S * T` and `S`; the third is the cusp.  `jAnalytic` takes the values
`0`, `1728` and `∞` there, which is what separates the three orbits. -/

private def rho : ℍ := ⟨-1 / 2 + (Real.sqrt 3 / 2 : ℝ) * Complex.I, by
  simp only [Complex.add_im, Complex.div_ofNat_im, Complex.neg_im, Complex.one_im, neg_zero,
    zero_div, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im,
    Complex.I_re, mul_zero, add_zero, zero_add]
  positivity⟩

private theorem coe_rho : ((rho : ℍ) : ℂ) = -1 / 2 + (Real.sqrt 3 / 2 : ℝ) * Complex.I := rfl

private theorem rho_sq : ((rho : ℍ) : ℂ) ^ 2 + (rho : ℂ) + 1 = 0 := by
  have h3 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  rw [coe_rho]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  linear_combination (-(1 / 4) : ℂ) * h3

private theorem ST_smul_rho : (ModularGroup.S * ModularGroup.T) • rho = rho := by
  have hρ := rho_sq
  have hne : ((rho : ℍ) : ℂ) + 1 ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    rw [coe_rho] at him
    simp at him
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.specialLinearGroup_apply]
  simp only [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S, ModularGroup.coe_T]
  simp only [Matrix.cons_mul, Matrix.vecMul_cons, Matrix.head_cons, Matrix.tail_cons,
    Matrix.empty_vecMul, Matrix.empty_mul]
  simp
  field_simp
  linear_combination -hρ

private theorem E₄_rho : ModularForm.E₄ rho = 0 := by
  set γ : SL(2, ℤ) := ModularGroup.S * ModularGroup.T with hγ
  have hmem : (γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  have h4 : (ModularForm.E₄ : ℍ → ℂ) ((γ : GL (Fin 2) ℝ) • rho) =
      denom (γ : GL (Fin 2) ℝ) rho ^ (4 : ℤ) * ModularForm.E₄ rho :=
    SlashInvariantForm.slash_action_eqn'' _ hmem rho
  rw [← ModularGroup.sl_moeb, hγ, ST_smul_rho] at h4
  have hden : denom ((ModularGroup.S * ModularGroup.T : SL(2, ℤ)) : GL (Fin 2) ℝ) rho =
      (rho : ℂ) + 1 := by
    simp [denom, ModularGroup.coe_S, ModularGroup.coe_T, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hden] at h4

  have hω : ((rho : ℂ) + 1) ^ 2 = ((rho : ℂ) + 1) - 1 := by linear_combination rho_sq
  have hω4 : ((rho : ℂ) + 1) ^ (4 : ℤ) = -((rho : ℂ) + 1) := by
    rw [show ((rho : ℂ) + 1) ^ (4 : ℤ) = (((rho : ℂ) + 1) ^ 2) ^ 2 by norm_cast; ring, hω]
    linear_combination rho_sq
  rw [hω4] at h4
  have hne : -((rho : ℂ) + 1) - 1 ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    rw [coe_rho] at him
    simp at him
  have : (-((rho : ℂ) + 1) - 1) * ModularForm.E₄ rho = 0 := by linear_combination -h4
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hne
  · exact h

private theorem jAnalytic_rho : jAnalytic rho = 0 := by
  rw [jAnalytic, E₄_rho]
  simp

private theorem S_smul_I : ModularGroup.S • UpperHalfPlane.I = UpperHalfPlane.I := by
  apply UpperHalfPlane.ext
  rw [modular_S_smul]
  change (-(UpperHalfPlane.I : ℂ))⁻¹ = (UpperHalfPlane.I : ℂ)
  rw [coe_I, Complex.inv_def]
  simp

private theorem E₆_I : ModularForm.E₆ UpperHalfPlane.I = 0 := by
  have hmem : ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨ModularGroup.S, rfl⟩
  have h6 : (ModularForm.E₆ : ℍ → ℂ)
        (((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ) • UpperHalfPlane.I) =
      denom ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ) UpperHalfPlane.I ^ (6 : ℤ) *
        ModularForm.E₆ UpperHalfPlane.I :=
    SlashInvariantForm.slash_action_eqn'' _ hmem UpperHalfPlane.I
  rw [← ModularGroup.sl_moeb, S_smul_I] at h6
  have hden : denom ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ) UpperHalfPlane.I = Complex.I := by
    simp [denom, ModularGroup.coe_S]
  rw [hden, show (Complex.I) ^ (6 : ℤ) = -1 by
    rw [show (6 : ℤ) = ((6 : ℕ) : ℤ) from rfl, zpow_natCast]
    rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, Complex.I_sq]; norm_num] at h6
  linear_combination h6 / 2

private theorem jAnalytic_I : jAnalytic UpperHalfPlane.I = 1728 := by
  have hΔ := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq UpperHalfPlane.I
  rw [E₆_I] at hΔ
  have hΔ0 := ModularForm.discriminant_ne_zero UpperHalfPlane.I
  have hE4 : ModularForm.E₄ UpperHalfPlane.I ≠ 0 := by
    intro h
    apply hΔ0
    rw [hΔ, h]
    norm_num
  rw [jAnalytic, hΔ]
  field_simp
  ring

/-! ### The kernel of `SL(2, ℤ) → SL(2, ℤ/N) ⊔ ±1`

The pin's own `abbrev Gpm` (its file line 137) — the port's `Gpm` of the same shape lives in
`LevelN.GaloisStructure` (implicit `N`) and is not the pin's spelling, so this file carries its
own copy, exactly as the pin does. `S * T` has order `3` modulo `±Γ(N)`, `S` has order `2`, and
`T` has order `N`; the three integer divisibility facts `3 ∣ n`, `2 ∣ n`, `N ∣ n` for an element
of `Gpm N` are what pins the orbit lengths to `[SL(2,ℤ) : Γ] / 3`, `/ 2` and `/ N`. -/

private abbrev Gpm (N : ℕ) : Subgroup SL(2, ℤ) :=
  CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))

private theorem mem_Gpm_imp (N : ℕ) {g : SL(2, ℤ)} (hg : g ∈ Gpm N) :
    g ∈ CongruenceSubgroup.Gamma N ∨ -g ∈ CongruenceSubgroup.Gamma N := by
  have : (CongruenceSubgroup.Gamma N).Normal := CongruenceSubgroup.Gamma_normal N
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have h2 : ((-1 : SL(2, ℤ)) ^ (2 : ℤ)) = 1 := by rw [zpow_two]; simp
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left
    rw [← two_mul, zpow_mul, h2, one_zpow, mul_one]
    exact hy
  · right
    rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one, mul_neg_one, neg_neg]
    exact hy

private theorem entry_10_eq_zero_of_mem_Gpm (N : ℕ) {g : SL(2, ℤ)} (hg : g ∈ Gpm N) :
    ((g 1 0 : ℤ) : ZMod N) = 0 := by
  rcases mem_Gpm_imp N hg with h | h
  · exact (CongruenceSubgroup.Gamma_mem.mp h).2.2.1
  · have := (CongruenceSubgroup.Gamma_mem.mp h).2.2.1
    rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg, neg_eq_zero] at this
    exact this

private theorem entry_01_eq_zero_of_mem_Gpm (N : ℕ) {g : SL(2, ℤ)} (hg : g ∈ Gpm N) :
    ((g 0 1 : ℤ) : ZMod N) = 0 := by
  rcases mem_Gpm_imp N hg with h | h
  · exact (CongruenceSubgroup.Gamma_mem.mp h).2.1
  · have := (CongruenceSubgroup.Gamma_mem.mp h).2.1
    rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg, neg_eq_zero] at this
    exact this

private theorem dvd_of_T_pow_mem (N : ℕ) {n : ℕ} (h : ModularGroup.T ^ n ∈ Gpm N) : N ∣ n := by
  have h01 := entry_01_eq_zero_of_mem_Gpm N h
  rw [← zpow_natCast, ModularGroup.coe_T_zpow] at h01
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Matrix.cons_val_zero, Int.cast_natCast] at h01
  exact (ZMod.natCast_eq_zero_iff n N).mp h01

private theorem one_ne_zero_zmod {N : ℕ} (hN : 2 ≤ N) : (1 : ZMod N) ≠ 0 := by
  have : Fact (1 < N) := ⟨hN⟩
  exact one_ne_zero

private theorem dvd_of_S_pow_mem {N : ℕ} (hN : 2 ≤ N) {n : ℕ} (h : ModularGroup.S ^ n ∈ Gpm N) :
    2 ∣ n := by
  by_contra hodd
  rw [Nat.two_dvd_ne_zero, ← Nat.odd_iff] at hodd
  obtain ⟨k, rfl⟩ := hodd
  have hS2 : (ModularGroup.S : SL(2, ℤ)) ^ 2 = -1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, ModularGroup.coe_S, Matrix.mul_apply, Fin.sum_univ_two]
  have hpow : (ModularGroup.S : SL(2, ℤ)) ^ (2 * k + 1) = (-1) ^ k * ModularGroup.S := by
    rw [pow_succ, pow_mul, hS2]
  rw [hpow] at h
  have h10 := entry_10_eq_zero_of_mem_Gpm N h
  rcases neg_one_pow_eq_or SL(2, ℤ) k with hk | hk
  · rw [hk, one_mul, ModularGroup.coe_S] at h10
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Int.cast_one] at h10
    exact one_ne_zero_zmod hN h10
  · rw [hk, neg_one_mul, Matrix.SpecialLinearGroup.coe_neg, ModularGroup.coe_S] at h10
    simp only [Matrix.neg_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Int.cast_neg, Int.cast_one, neg_eq_zero] at h10
    exact one_ne_zero_zmod hN h10

private theorem dvd_of_ST_pow_mem {N : ℕ} (hN : 2 ≤ N) {n : ℕ}
    (h : (ModularGroup.S * ModularGroup.T) ^ n ∈ Gpm N) : 3 ∣ n := by
  have hST : ((ModularGroup.S * ModularGroup.T : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![0, -1; 1, 1] := by
    rw [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S, ModularGroup.coe_T]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hST2 : (((ModularGroup.S * ModularGroup.T) ^ 2 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![-1, -1; 1, 0] := by
    rw [Matrix.SpecialLinearGroup.coe_pow, hST]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  have hST3 : (ModularGroup.S * ModularGroup.T : SL(2, ℤ)) ^ 3 = -1 := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_pow, hST]
    fin_cases i <;> fin_cases j <;>
      simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

  obtain ⟨q, r, hr, rfl⟩ : ∃ q r : ℕ, r < 3 ∧ n = 3 * q + r :=
    ⟨n / 3, n % 3, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 3).symm⟩
  have hpow : (ModularGroup.S * ModularGroup.T : SL(2, ℤ)) ^ (3 * q + r) =
      (-1) ^ q * (ModularGroup.S * ModularGroup.T) ^ r := by
    rw [pow_add, pow_mul, hST3]
  rw [hpow] at h
  have h10 := entry_10_eq_zero_of_mem_Gpm N h

  interval_cases r
  · exact ⟨q, by ring⟩
  · exfalso
    rcases neg_one_pow_eq_or SL(2, ℤ) q with hk | hk
    · rw [hk, one_mul, pow_one, hST] at h10
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Int.cast_one] at h10
      exact one_ne_zero_zmod hN h10
    · rw [hk, neg_one_mul, Matrix.SpecialLinearGroup.coe_neg, pow_one, hST] at h10
      simp only [Matrix.neg_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, Int.cast_neg, Int.cast_one,
        neg_eq_zero] at h10
      exact one_ne_zero_zmod hN h10
  · exfalso
    rcases neg_one_pow_eq_or SL(2, ℤ) q with hk | hk
    · rw [hk, one_mul, hST2] at h10
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Int.cast_one] at h10
      exact one_ne_zero_zmod hN h10
    · rw [hk, neg_one_mul, Matrix.SpecialLinearGroup.coe_neg, hST2] at h10
      simp only [Matrix.neg_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, Int.cast_neg, Int.cast_one,
        neg_eq_zero] at h10
      exact one_ne_zero_zmod hN h10

/-! ### The orbit/stabiliser package at one place

`orbit_package` is the pin's packaging of
`ord_restrictAlong_eq_natCard_algHom_of_isGalois` (first component) into the shape the Hurwitz
bound wants: a finite set `T` of places, all of them mapping `t` to the same `c` with the same
order `e`, with `T.card * e = [ℂ⟮t⟯ : ℂ]` and `m ∣ e` for any `m` killing `g`. -/

section Orbit

variable {L : Type*} [Field L] [Algebra ℂ L]

private def toSemi (E : IntermediateField ℂ L) : (L ≃ₐ[E] L) →* AlgebraicCurve.SemilinearAut ℂ L where
  toFun g := AlgebraicCurve.SemilinearAut.ofAlgAut (g.restrictScalars ℂ)
  map_one' := by ext <;> rfl
  map_mul' _ _ := by ext <;> rfl

private theorem toSemi_smul (E : IntermediateField ℂ L) (g : L ≃ₐ[E] L) (x : L) :
    toSemi E g • x = g x := rfl

private theorem toSemi_apply (E : IntermediateField ℂ L) (g : L ≃ₐ[E] L) :
    toSemi E g = AlgebraicCurve.SemilinearAut.ofAlgAut (g.restrictScalars ℂ) := rfl

private theorem orbit_package (t : L) [FiniteDimensional ℂ⟮t⟯ L] [IsGalois ℂ⟮t⟯ L]
    (hint : ∀ ψ : L →ₐ[ℂ] L, ψ t = t → ψ.toRingHom.IsIntegral)
    (W : AlgebraicCurve.Place ℂ L) (c : ℂ) (hW : 0 < W.ord (t - algebraMap ℂ L c))
    (g : L ≃ₐ[ℂ⟮t⟯] L) (hg : AlgebraicCurve.SemilinearAut.ofAlgAut (g.restrictScalars ℂ) • W = W)
    (m : ℕ) (hm : ∀ n : ℕ, g ^ n = 1 → m ∣ n) :
    ∃ (T : Finset (AlgebraicCurve.Place ℂ L)) (e : ℕ),
      (∀ P ∈ T, P.ord (t - algebraMap ℂ L c) = e) ∧ 0 < e ∧ m ∣ e ∧
        T.card * e = Module.finrank ℂ⟮t⟯ L := by
  classical
  let : MulAction (L ≃ₐ[ℂ⟮t⟯] L) (AlgebraicCurve.Place ℂ L) := MulAction.compHom _ (toSemi ℂ⟮t⟯)
  have hsmul : ∀ (g' : (L ≃ₐ[ℂ⟮t⟯] L)) (P : AlgebraicCurve.Place ℂ L),
      g' • P = toSemi ℂ⟮t⟯ g' • P := fun _ _ => rfl

  have hDH := (AlgebraicCurve.Place.ord_restrictAlong_eq_natCard_algHom_of_isGalois ℂ t t c
    (AlgHom.id ℂ L) rfl inferInstance inferInstance hint W hW).1
  set D := MulAction.stabilizer (L ≃ₐ[ℂ⟮t⟯] L) W with hD
  have hcardD : Nat.card {σ : (L ≃ₐ[ℂ⟮t⟯] L) //
        AlgebraicCurve.SemilinearAut.ofAlgAut (σ.restrictScalars ℂ) • W = W} =
      Nat.card D := Nat.card_congr (Equiv.subtypeEquivRight fun σ => by
        rw [hD, MulAction.mem_stabilizer_iff, hsmul, toSemi_apply])
  rw [hcardD] at hDH

  have hfin : (MulAction.orbit (L ≃ₐ[ℂ⟮t⟯] L) W).Finite := Set.finite_range _
  refine ⟨hfin.toFinset, Nat.card D, ?_, ?_, ?_, ?_⟩
  · intro P hP
    rw [Set.Finite.mem_toFinset, MulAction.mem_orbit_iff] at hP
    obtain ⟨g', rfl⟩ := hP
    rw [← hDH, hsmul]
    have hfix : toSemi ℂ⟮t⟯ g' • (t - algebraMap ℂ L c) = t - algebraMap ℂ L c := by
      rw [toSemi_smul, map_sub]
      congr 1
      · exact g'.commutes (⟨t, IntermediateField.mem_adjoin_simple_self ℂ t⟩ : ℂ⟮t⟯)
      · exact (g'.restrictScalars ℂ).commutes c
    conv_lhs => rw [← hfix]
    exact AlgebraicCurve.SemilinearAut.ord_smul _ _ _
  · have : (0 : ℤ) < Nat.card D := by rw [← hDH]; exact hW
    exact_mod_cast this
  · have hgD : g ∈ D := by
      rw [hD, MulAction.mem_stabilizer_iff, hsmul, toSemi_apply]
      exact hg
    exact (hm (orderOf g) (pow_orderOf_eq_one g)).trans (Subgroup.orderOf_dvd_natCard D hgD)
  · rw [← Set.ncard_eq_toFinset_card (MulAction.orbit (L ≃ₐ[ℂ⟮t⟯] L) W) hfin,
      ← MulAction.index_stabilizer, Subgroup.index_mul_card, IsGalois.card_aut_eq_finrank]

private theorem apply_eq_self_of_mem_adjoin (ψ : L →ₐ[ℂ] L) (t : L) (hψ : ψ t = t) {x : L}
    (hx : x ∈ ℂ⟮t⟯) : ψ x = x := by
  let S : IntermediateField ℂ L := (AlgHom.equalizer ψ (AlgHom.id ℂ L)).toIntermediateField
    (fun y hy => by
      rw [AlgHom.mem_equalizer] at hy ⊢
      simp only [AlgHom.coe_id, id_eq] at hy ⊢
      rw [map_inv₀, hy])
  have hle : ℂ⟮t⟯ ≤ S := by
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    change t ∈ AlgHom.equalizer ψ (AlgHom.id ℂ L)
    rw [AlgHom.mem_equalizer]
    simpa using hψ
  have := hle hx
  change x ∈ AlgHom.equalizer ψ (AlgHom.id ℂ L) at this
  rw [AlgHom.mem_equalizer] at this
  simpa using this

private theorem isIntegral_of_apply_eq (t : L) [FiniteDimensional ℂ⟮t⟯ L] (ψ : L →ₐ[ℂ] L)
    (hψ : ψ t = t) : ψ.toRingHom.IsIntegral := by
  intro y
  have hy : IsIntegral ℂ⟮t⟯ y := IsIntegral.of_finite ℂ⟮t⟯ y
  refine ⟨(minpoly ℂ⟮t⟯ y).map (algebraMap ℂ⟮t⟯ L), (minpoly.monic hy).map _, ?_⟩
  rw [Polynomial.eval₂_map]
  have hcomp : ψ.toRingHom.comp (algebraMap ℂ⟮t⟯ L) = algebraMap ℂ⟮t⟯ L := by
    ext e
    exact apply_eq_self_of_mem_adjoin ψ t hψ e.2
  rw [hcomp]
  exact minpoly.aeval ℂ⟮t⟯ y

private theorem adjoin_inv_eq (t : L) : ℂ⟮t⁻¹⟯ = ℂ⟮t⟯ := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact IntermediateField.inv_mem _ (IntermediateField.mem_adjoin_simple_self ℂ t)
  · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    have := IntermediateField.inv_mem _ (IntermediateField.mem_adjoin_simple_self ℂ t⁻¹)
    rwa [inv_inv] at this

private theorem finiteDimensional_congr {E₁ E₂ : IntermediateField ℂ L} (h : E₁ = E₂)
    [FiniteDimensional E₁ L] : FiniteDimensional E₂ L := by subst h; assumption

private theorem isGalois_congr {E₁ E₂ : IntermediateField ℂ L} (h : E₁ = E₂) [IsGalois E₁ L] :
    IsGalois E₂ L := by subst h; assumption

private theorem finrank_congr {E₁ E₂ : IntermediateField ℂ L} (h : E₁ = E₂) :
    Module.finrank E₁ L = Module.finrank E₂ L := by subst h; rfl

end Orbit

/-! ### Lifting a `ℂ`-automorphism that fixes a subfield down to `ℂ⟮t⟯` -/

section Lift

variable {L : Type*} [Field L] [Algebra ℂ L]

private def liftE (E' : IntermediateField ℂ L) (φ : L ≃ₐ[ℂ] L) (hφ : ∀ x ∈ E', φ x = x) :
    L ≃ₐ[E'] L :=
  { φ.toRingEquiv with commutes' := fun e => hφ e e.2 }

private theorem restrictScalars_liftE (E' : IntermediateField ℂ L) (φ : L ≃ₐ[ℂ] L)
    (hφ : ∀ x ∈ E', φ x = x) : (liftE E' φ hφ).restrictScalars ℂ = φ :=
  AlgEquiv.ext fun _ => rfl

private def liftHom {Γ : Type*} [Group Γ] (E' : IntermediateField ℂ L) (σ : Γ →* (L ≃ₐ[ℂ] L))
    (hσ : ∀ (γ : Γ), ∀ x ∈ E', σ γ x = x) : Γ →* (L ≃ₐ[E'] L) where
  toFun γ := liftE E' (σ γ) (hσ γ)
  map_one' := by ext x; simp [liftE]
  map_mul' γ δ := by ext x; simp [liftE]

private theorem restrictScalars_liftHom {Γ : Type*} [Group Γ] (E' : IntermediateField ℂ L)
    (σ : Γ →* (L ≃ₐ[ℂ] L)) (hσ : ∀ (γ : Γ), ∀ x ∈ E', σ γ x = x) (γ : Γ) :
    (liftHom E' σ hσ γ).restrictScalars ℂ = σ γ :=
  restrictScalars_liftE E' (σ γ) (hσ γ)

private theorem liftHom_pow_eq_one_iff {Γ : Type*} [Group Γ] (E' : IntermediateField ℂ L)
    (σ : Γ →* (L ≃ₐ[ℂ] L)) (hσ : ∀ (γ : Γ), ∀ x ∈ E', σ γ x = x) (γ : Γ) (n : ℕ) :
    liftHom E' σ hσ γ ^ n = 1 ↔ γ ^ n ∈ σ.ker := by
  rw [← map_pow, MonoidHom.mem_ker]
  constructor
  · intro h
    have := congrArg (AlgEquiv.restrictScalars ℂ) h
    rw [restrictScalars_liftHom] at this
    rw [this]
    ext x
    rfl
  · intro h
    ext x
    change σ (γ ^ n) x = x
    rw [h]
    rfl

end Lift

/-! ### The inequality -/

section Main

variable (N : ℕ) [NeZero N]
variable (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ring N) K] [IsScalarTower ℂ (ring N) K]
  [IsFractionRing (ring N) K]

private theorem main (hN : 2 ≤ N) :
    12 * N + N * (Gpm N).index ≤ 12 * N * AlgebraicCurve.genusFF ℂ K + 6 * (Gpm N).index := by
  classical
  obtain ⟨hst, σ, hσ, hker, hfix, htr, hfd, hrank, hgal⟩ :=
    ModularCurve.LevelN.exists_monoidHom_algEquiv_fixedField_eq_adjoin N K
  set jK : K := algebraMap (ring N) K (jGen N) with hjK
  have := hfd
  have := hgal

  have hσE : ∀ (γ : SL(2, ℤ)), ∀ x ∈ ℂ⟮jK⟯, σ γ x = x := fun γ x hx => by
    rw [← hfix] at hx
    exact (IntermediateField.mem_fixedField_iff σ.range x).mp hx (σ γ) ⟨γ, rfl⟩
  have hEinv : ℂ⟮jK⁻¹⟯ = ℂ⟮jK⟯ := adjoin_inv_eq jK
  have hσE' : ∀ (γ : SL(2, ℤ)), ∀ x ∈ ℂ⟮jK⁻¹⟯, σ γ x = x := by
    rw [hEinv]; exact hσE
  have hfd' : FiniteDimensional ℂ⟮jK⁻¹⟯ K := finiteDimensional_congr hEinv.symm
  have hgal' : IsGalois ℂ⟮jK⁻¹⟯ K := isGalois_congr hEinv.symm
  have hrank' : Module.finrank ℂ⟮jK⁻¹⟯ K = (Gpm N).index := by
    rw [finrank_congr hEinv]; exact hrank

  have hint : ∀ ψ : K →ₐ[ℂ] K, ψ jK = jK → ψ.toRingHom.IsIntegral :=
    fun ψ hψ => isIntegral_of_apply_eq jK ψ hψ
  have hint' : ∀ ψ : K →ₐ[ℂ] K, ψ jK⁻¹ = jK⁻¹ → ψ.toRingHom.IsIntegral := fun ψ hψ => by
    apply isIntegral_of_apply_eq jK ψ
    rw [map_inv₀] at hψ
    exact inv_injective hψ

  obtain ⟨W₀, hW₀, hW₀fix⟩ := ModularCurve.LevelN.exists_place_ord_sub_pos_forall_smul_eq N K rho
  obtain ⟨W₁, hW₁, hW₁fix⟩ :=
    ModularCurve.LevelN.exists_place_ord_sub_pos_forall_smul_eq N K UpperHalfPlane.I
  obtain ⟨W₂, hW₂, hW₂fix⟩ :=
    ModularCurve.LevelN.exists_place_ord_neg_forall_smul_eq N K (hst ModularGroup.T⁻¹)
  rw [jAnalytic_rho] at hW₀
  rw [jAnalytic_I] at hW₁
  change 0 < W₀.ord (jK - algebraMap ℂ K 0) at hW₀
  change 0 < W₁.ord (jK - algebraMap ℂ K 1728) at hW₁
  change W₂.ord jK < 0 at hW₂
  have hW₂' : 0 < W₂.ord (jK⁻¹ - algebraMap ℂ K 0) := by
    rw [map_zero, sub_zero, AlgebraicCurve.Place.ord_inv]; omega

  set g₀ := liftHom ℂ⟮jK⟯ σ hσE (ModularGroup.S * ModularGroup.T) with hg₀
  set g₁ := liftHom ℂ⟮jK⟯ σ hσE ModularGroup.S with hg₁
  set g₂ := liftHom ℂ⟮jK⁻¹⟯ σ hσE' ModularGroup.T with hg₂
  have hg₀W : AlgebraicCurve.SemilinearAut.ofAlgAut (g₀.restrictScalars ℂ) • W₀ = W₀ := by
    rw [hg₀, restrictScalars_liftHom]
    exact hW₀fix (ModularGroup.S * ModularGroup.T) ST_smul_rho (hst _) (σ _) (hσ _)
  have hg₁W : AlgebraicCurve.SemilinearAut.ofAlgAut (g₁.restrictScalars ℂ) • W₁ = W₁ := by
    rw [hg₁, restrictScalars_liftHom]
    exact hW₁fix ModularGroup.S S_smul_I (hst _) (σ _) (hσ _)
  have hg₂W : AlgebraicCurve.SemilinearAut.ofAlgAut (g₂.restrictScalars ℂ) • W₂ = W₂ := by
    rw [hg₂, restrictScalars_liftHom]
    exact hW₂fix (σ _) (hσ _)
  have hm₀ : ∀ n : ℕ, g₀ ^ n = 1 → 3 ∣ n := fun n hn => by
    rw [hg₀, liftHom_pow_eq_one_iff, hker] at hn
    exact dvd_of_ST_pow_mem hN hn
  have hm₁ : ∀ n : ℕ, g₁ ^ n = 1 → 2 ∣ n := fun n hn => by
    rw [hg₁, liftHom_pow_eq_one_iff, hker] at hn
    exact dvd_of_S_pow_mem hN hn
  have hm₂ : ∀ n : ℕ, g₂ ^ n = 1 → N ∣ n := fun n hn => by
    rw [hg₂, liftHom_pow_eq_one_iff, hker] at hn
    exact dvd_of_T_pow_mem N hn

  obtain ⟨T₀, e₀, hT₀, he₀, hm₀e, hc₀⟩ := orbit_package jK hint W₀ 0 hW₀ g₀ hg₀W 3 hm₀
  obtain ⟨T₁, e₁, hT₁, he₁, hm₁e, hc₁⟩ := orbit_package jK hint W₁ 1728 hW₁ g₁ hg₁W 2 hm₁
  obtain ⟨T₂, e₂, hT₂, he₂, hm₂e, hc₂⟩ := orbit_package jK⁻¹ hint' W₂ 0 hW₂' g₂ hg₂W N hm₂
  rw [hrank] at hc₀ hc₁
  rw [hrank'] at hc₂

  have hdisj : Disjoint T₀ T₁ := by
    rw [Finset.disjoint_left]
    intro P hP0 hP1
    have h0 := hT₀ P hP0
    have h1 := hT₁ P hP1
    rw [map_zero, sub_zero] at h0
    set y := jK - algebraMap ℂ K 1728 with hy
    have hy0 : y ≠ 0 := by
      intro h; rw [h, AlgebraicCurve.Place.ord_zero] at h1; omega
    have hsum : jK + -y = algebraMap ℂ K 1728 := by rw [hy]; ring
    have hne : jK + -y ≠ 0 := by
      rw [hsum]; exact (map_ne_zero _).mpr (by norm_num)
    have hle := AlgebraicCurve.Place.min_ord_le_ord_add P hne
    rw [hsum, AlgebraicCurve.Place.ord_algebraMap] at hle
    have hneg : P.ord (-y) = P.ord y := by
      rw [show -y = y * algebraMap ℂ K (-1) by rw [map_neg, map_one]; ring,
        P.ord_mul hy0 (by rw [map_neg, map_one]; exact neg_ne_zero.mpr one_ne_zero),
        AlgebraicCurve.Place.ord_algebraMap, add_zero]
    rw [hneg, h0, h1] at hle
    have : (0 : ℤ) < min (e₀ : ℤ) (e₁ : ℤ) :=
      lt_min (by exact_mod_cast he₀) (by exact_mod_cast he₁)
    omega

  have hH := AlgebraicCurve.sum_ord_sub_one_le_two_mul_genusFF_of_isSeparable ℂ jK htr hfd
    inferInstance (T₀ ∪ T₁) (fun P => if P ∈ T₀ then 0 else 1728)
    (fun P hP => by
      rcases Finset.mem_union.mp hP with h | h
      · simp only [h, ite_true]; rw [hT₀ P h]; exact_mod_cast he₀
      · have h' : P ∉ T₀ := fun h' => Finset.disjoint_left.mp hdisj h' h
        simp only [h', ite_false]; rw [hT₁ P h]; exact_mod_cast he₁)
    T₂ (fun P hP => by
      have := hT₂ P hP
      rw [map_zero, sub_zero, AlgebraicCurve.Place.ord_inv] at this
      omega)
  rw [Finset.sum_union hdisj, hrank] at hH
  have hs₀ : ∑ P ∈ T₀, (P.ord (jK - algebraMap ℂ K (if P ∈ T₀ then 0 else 1728)) - 1) =
      T₀.card • ((e₀ : ℤ) - 1) := by
    rw [← Finset.sum_const]
    apply Finset.sum_congr rfl
    intro P hP
    simp only [hP, ite_true]
    rw [hT₀ P hP]
  have hs₁ : ∑ P ∈ T₁, (P.ord (jK - algebraMap ℂ K (if P ∈ T₀ then 0 else 1728)) - 1) =
      T₁.card • ((e₁ : ℤ) - 1) := by
    rw [← Finset.sum_const]
    apply Finset.sum_congr rfl
    intro P hP
    have h' : P ∉ T₀ := fun h' => Finset.disjoint_left.mp hdisj h' hP
    simp only [h', ite_false]
    rw [hT₁ P hP]
  have hs₂ : ∑ P ∈ T₂, (-P.ord jK - 1) = T₂.card • ((e₂ : ℤ) - 1) := by
    rw [← Finset.sum_const]
    apply Finset.sum_congr rfl
    intro P hP
    have := hT₂ P hP
    rw [map_zero, sub_zero, AlgebraicCurve.Place.ord_inv] at this
    omega
  rw [hs₀, hs₁, hs₂] at hH
  simp only [nsmul_eq_mul] at hH

  obtain ⟨k₀, hk₀⟩ := hm₀e
  obtain ⟨k₁, hk₁⟩ := hm₁e
  obtain ⟨k₂, hk₂⟩ := hm₂e
  have hk₀p : 1 ≤ k₀ := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hk₀; omega
  have hk₁p : 1 ≤ k₁ := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hk₁; omega
  have hk₂p : 1 ≤ k₂ := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hk₂; omega
  have hr₀ : 3 * T₀.card ≤ (Gpm N).index := by
    calc 3 * T₀.card ≤ 3 * T₀.card * k₀ := Nat.le_mul_of_pos_right _ hk₀p
      _ = (Gpm N).index := by rw [← hc₀, hk₀]; ring
  have hr₁ : 2 * T₁.card ≤ (Gpm N).index := by
    calc 2 * T₁.card ≤ 2 * T₁.card * k₁ := Nat.le_mul_of_pos_right _ hk₁p
      _ = (Gpm N).index := by rw [← hc₁, hk₁]; ring
  have hr₂ : N * T₂.card ≤ (Gpm N).index := by
    calc N * T₂.card ≤ N * T₂.card * k₂ := Nat.le_mul_of_pos_right _ hk₂p
      _ = (Gpm N).index := by rw [← hc₂, hk₂]; ring

  have hc₀' : (T₀.card : ℤ) * e₀ = (Gpm N).index := by exact_mod_cast hc₀
  have hc₁' : (T₁.card : ℤ) * e₁ = (Gpm N).index := by exact_mod_cast hc₁
  have hc₂' : (T₂.card : ℤ) * e₂ = (Gpm N).index := by exact_mod_cast hc₂
  have hr₀' : 3 * (T₀.card : ℤ) ≤ (Gpm N).index := by exact_mod_cast hr₀
  have hr₁' : 2 * (T₁.card : ℤ) ≤ (Gpm N).index := by exact_mod_cast hr₁
  have hr₂' : (N : ℤ) * (T₂.card : ℤ) ≤ (Gpm N).index := by exact_mod_cast hr₂
  have hN0 : (0 : ℤ) ≤ N := by positivity
  simp only [mul_sub, mul_one] at hH
  rw [hc₀', hc₁', hc₂'] at hH
  have h1 : ((Gpm N).index : ℤ) + 2 ≤
      2 * (AlgebraicCurve.genusFF ℂ K : ℤ) + T₀.card + T₁.card + T₂.card := by linarith
  have hA := mul_le_mul_of_nonneg_left h1 hN0
  have hB := mul_le_mul_of_nonneg_left hr₀' (show (0 : ℤ) ≤ 2 * N by positivity)
  have hC := mul_le_mul_of_nonneg_left hr₁' (show (0 : ℤ) ≤ 3 * N by positivity)
  have key : (12 : ℤ) * N + N * (Gpm N).index ≤
      12 * N * (AlgebraicCurve.genusFF ℂ K : ℤ) + 6 * (Gpm N).index := by
    linear_combination 6 * hA + hB + hC + 6 * hr₂'
  exact_mod_cast key

end Main

end GenusBound

end ModularCurve.LevelN

open ModularCurve.LevelN in
/-- Pin `ModularCurve.LevelN.twelve_mul_add_mul_index_le_genusFF`
(`S_ModularCurve_LevelN_twelve_mul_add_mul_index_le_genusFF.lean:587`, its `solution`, at the
wrapper's statement). -/
theorem ModularCurve.LevelN.twelve_mul_add_mul_index_le_genusFF (N : ℕ) [NeZero N] (hN : 2 ≤ N)
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ModularCurve.LevelN.ring N) K]
    [IsScalarTower ℂ (ModularCurve.LevelN.ring N) K]
    [IsFractionRing (ModularCurve.LevelN.ring N) K] :
    12 * N + N * (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index ≤
      12 * N * AlgebraicCurve.genusFF ℂ K +
        6 * (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index :=
  ModularCurve.LevelN.GenusBound.main N K hN

/-! ### The inequality at a general level

`12 · N + N · [SL(2, ℤ) : Γ(N) ⊔ ±1] ≤ 12 · N · dim S₂(Γ(N)) + 6 · [SL(2, ℤ) : Γ(N) ⊔ ±1]`.

The transport of `twelve_mul_add_mul_index_le_genusFF` (above) from `genusFF` to the space of
cusp forms, through the two dimension facts `dim Ω¹_reg = g`
(`AlgebraicCurve.finite_and_finrank_regularDifferentials_eq_genus`, applied to the function
field of the level-`N` curve) and `Ω¹_reg ↪ S₂(Γ(N))`
(`ModularCurve.LevelN.exists_linearMap_regularDifferentials_cuspForm_injective`).  The pin's
own file is `P2M/Sol/S_ModularCurve_twelve_mul_add_mul_index_le_finrank_cuspForm_Gamma.lean`,
whose two private pieces are kept here: the `curve_package` bridge (`IsCurveOver`,
`EssFiniteType`, `DCoordGenerates`, `dim Ω¹_reg = g` from a transcendental generator — its
twelve `AlgebraicCurve` premises are *imported*, five of them from
`AlgebraicCurve/ResidueTheorem/RRAssembly.lean` and the rest from the single-node modules that
host them) and the `main` computation.  The pin's two `attribute` walls (`-instance`, `-simp`)
are not transcribed (work order D3: the module is silent without them), and neither is its
local `isDomain_ring` — the port has that public in `LevelN/FieldGalois.lean` (its own pin
node), so it is imported.  The pin's `Cusp`, `instFintypeCusp`, `width` tail does not occur in
this file. -/

namespace ModularCurve

namespace GenusBoundAssembly

open AlgebraicCurve ModularCurve.LevelN

section Bridge

variable {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]

private theorem curve_package {x : F} (htr : Transcendental K x)
    (hfd : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    ∃ (_ : IsCurveOver K F) (_ : Algebra.EssFiniteType K F)
      (_ : ∀ w : Place K F, w.DCoordGenerates),
      Module.Finite K ↥(regularDifferentials K F) ∧
        genusFF K F = Module.finrank K ↥(regularDifferentials K F) := by
  classical
  obtain ⟨t, ht, htfd, htsep⟩ :=
    AlgebraicCurve.exists_separating_transcendental_of_perfectField htr hfd
  have := htfd
  have := htsep
  have hC1 : IsCurveOver K F := isCurveOver_of_transcendental ht htfd htsep
  have hC2 : Algebra.EssFiniteType K F :=
    essFiniteType_of_transcendental_of_finiteDimensional ht htfd
  have : HasCanonicalDivisor (K := K) (F := F) := hasCanonicalDivisor_of_isCurveOver
  have hC3 : ∀ w : Place K F, w.DCoordGenerates := dCoordGenerates_of_isCurveOver

  set e : RatFunc K ≃ₐ[K] K⟮t⟯ := RatFunc.algEquivOfTranscendental t ht with he
  let : Algebra (RatFunc K) F := ((algebraMap K⟮t⟯ F).comp e.toAlgHom.toRingHom).toAlgebra
  have hsq : RingHom.comp (algebraMap (RatFunc K) F) (e.symm.toRingEquiv : K⟮t⟯ →+* RatFunc K)
      = RingHom.comp (RingEquiv.refl F : F →+* F) (algebraMap K⟮t⟯ F) := by
    refine RingHom.ext fun a => ?_
    show algebraMap K⟮t⟯ F (e (e.symm a)) = algebraMap K⟮t⟯ F a
    rw [e.apply_symm_apply]
  have : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq fun a => by
      show algebraMap K F a = algebraMap K⟮t⟯ F (e (algebraMap K (RatFunc K) a))
      rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  have : FiniteDimensional (RatFunc K) F :=
    Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  have : Algebra.IsSeparable (RatFunc K) F :=
    Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  have : Algebra.IsIntegral (RatFunc K) F := Algebra.IsIntegral.of_finite (RatFunc K) F
  have : IsCurveOver K (RatFunc K) := isCurveOver_ratFunc K
  have : FiniteDimensional (IntermediateField.adjoin K ({RatFunc.X} : Set (RatFunc K)))
      (RatFunc K) := by
    refine Module.Finite.of_surjective
      (Algebra.linearMap (IntermediateField.adjoin K ({RatFunc.X} : Set (RatFunc K)))
        (RatFunc K)) fun y => ?_
    refine ⟨⟨y, ?_⟩, rfl⟩
    rw [RatFunc.adjoin_X]
    exact IntermediateField.mem_top
  have : Algebra.EssFiniteType K (RatFunc K) :=
    essFiniteType_of_transcendental_of_finiteDimensional
      (RatFunc.transcendental_X (K := K)) inferInstance
  have : ∀ v : Place K (RatFunc K), v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  have hRR : FunctionFieldRiemannRoch K F := by
    unfold FunctionFieldRiemannRoch
    intro _ _ _ ω hω D
    exact functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver (K := K) (F := F) hω D
  have hC : ConstantsAreBase K F := constantsAreBase_of_isAlgClosed K F
  have hSG : StichtenothGenusExists K F := stichtenothGenusExists_of_isCurveOver hC
  have hWDA : WeilDualityAdelic K F :=
    weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists hRR hSG
  have hg : genus K F = genusFF K F := genus_eq_genusFF hRR hWDA hC
  obtain ⟨hfin, hdim⟩ := finite_and_finrank_regularDifferentials_eq_genus (K := K) (F := F)
  exact ⟨hC1, hC2, hC3, hfin, by rw [hdim, hg]⟩

end Bridge

private theorem main (N : ℕ) (hN : 2 ≤ N) :
    12 * N + N * (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index ≤
      12 * N * Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma N) 2) +
        6 * (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by
  classical
  have : NeZero N := ⟨by omega⟩
  have : IsDomain (ring N) := ModularCurve.LevelN.isDomain_ring N
  let K := FractionRing (ring N)
  obtain ⟨-, -, -, -, -, htr, hfd, -, -⟩ :=
    ModularCurve.LevelN.exists_monoidHom_algEquiv_fixedField_eq_adjoin N K
  have hgen := ModularCurve.LevelN.twelve_mul_add_mul_index_le_genusFF N hN K
  obtain ⟨Φ, hΦ⟩ :=
    ModularCurve.LevelN.exists_linearMap_regularDifferentials_cuspForm_injective N K
  obtain ⟨-, -, -, hfin, hg⟩ := curve_package (K := ℂ) (F := K) htr hfd
  have := hfin
  have : FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma N) 2) :=
    CuspForm.finiteDimensional_of_isArithmetic _ 2
  have hle : Module.finrank ℂ ↥(regularDifferentials ℂ K) ≤
      Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma N) 2) :=
    LinearMap.finrank_le_finrank_of_injective hΦ
  calc 12 * N + N * (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index
      ≤ 12 * N * genusFF ℂ K +
          6 * (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := hgen
    _ = 12 * N * Module.finrank ℂ ↥(regularDifferentials ℂ K) +
          6 * (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by rw [hg]
    _ ≤ 12 * N * Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma N) 2) +
          6 * (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by
        gcongr

end GenusBoundAssembly

end ModularCurve

/-- Pin `ModularCurve.twelve_mul_add_mul_index_le_finrank_cuspForm_Gamma`
(`S_ModularCurve_twelve_mul_add_mul_index_le_finrank_cuspForm_Gamma.lean:127`, its `main`, at
the wrapper's statement). -/
theorem ModularCurve.twelve_mul_add_mul_index_le_finrank_cuspForm_Gamma (N : ℕ) (hN : 2 ≤ N) :
    12 * N + N * (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index ≤
      12 * N * Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma N) 2) +
        6 * (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index :=
  ModularCurve.GenusBoundAssembly.main N hN
