/-
  The `Γ_H(M)` Hecke double cosets: the mathematics only.

  The module supplies three things, and nothing else:

  1. **the level pair** — `Γ_H(M) ⊓ g⁻¹ Γ_H(M) g = Γ_HUpper(M,H,q)` for `g = !![1,0;0,q]`, which is
     the (0,1)-entry read-off `b/q` (`stabiliser_eq`);
  2. **the cosets** — for `q ∣ M` the `q` matrices `heckeMatrix q x` (`x : ZMod q`) are one
     representative per left `Γ_H(M)`-coset of `Γ_H(M) g Γ_H(M)`: they lie in the double coset, they
     are pairwise distinct, and every element of the double coset is left-`Γ_H`-equivalent to one of
     them — the linear congruence `v 1 1 · x ≡ v 0 1 (mod q)` (`heckeUTransversal`);
  3. **the operator** — `U_q` is the double-coset operator of `Γ_H(M) g Γ_H(M)` on the level space
     (`sum_slash_heckeU_eq_doubleCosetOperator`), hence `Γ_H(M)`-invariant (`heckeU_slash_eq_self`).

  No representative system of the older layer is named here: the representatives are the matrices
  the operator is defined with, so the coset sum is `heckeU`'s own definition and there is nothing
  to reindex.

  Not wired (`spec-pin:` none); the module carries no statement of the pin. -/
import FLTForHuman.ModularForms.Defs.CohCarrierLevel
import FLTForHuman.ModularForms.Defs.HeckeOperator
import FLTForHuman.ModularForms.Defs.HeckeRepresentatives
import FLTForHuman.ModularForms.HeckeCosetSum

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm

open UpperHalfPlane CongruenceSubgroup CohCarrier
open ModularForm.Level (Gamma0Upper mem_Gamma0Upper_iff_dvd)
open ModularForm.HeckeRepresentatives

namespace HeckeCosetGammaH

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

/-! ## The level group -/

/-- The image of `Γ_H(M)` in `GL(2,ℝ)`: the level group the Hecke operator lives in. -/
abbrev levelGroup : Subgroup (GL (Fin 2) ℝ) := (GammaH M H).map (Matrix.SpecialLinearGroup.mapGL ℝ)

/-- `Γ_H(M)` is isomorphic to its image in `GL(2,ℝ)`. -/
noncomputable def levelEquiv : ↥(GammaH M H) ≃* ↥(levelGroup M H) :=
  (GammaH M H).equivMapOfInjective (Matrix.SpecialLinearGroup.mapGL ℝ)
    Matrix.SpecialLinearGroup.mapGL_injective

omit [NeZero M] in
@[simp] theorem coe_levelEquiv (x : ↥(GammaH M H)) :
    ((levelEquiv M H x : ↥(levelGroup M H)) : GL (Fin 2) ℝ) =
      (Matrix.SpecialLinearGroup.mapGL ℝ (x : SL(2, ℤ)) : GL (Fin 2) ℝ) := rfl

/-! ## Obligation 1: the level pair -/

omit [NeZero M] in
theorem conjUpperMat_mem_of_dvd {q : ℕ} [NeZero q] {x : ↥(GammaH M H)}
    (hx : (q : ℤ) ∣ ((x : SL(2, ℤ)) 0 1)) :
    conjUpperMat q (x : SL(2, ℤ)) hx ∈ GammaH M H := by
  obtain ⟨hx0, hxH⟩ := mem_GammaH_iff.mp x.2
  rw [mem_GammaH_iff]
  refine ⟨?_, ?_⟩
  · rw [Gamma0_mem, conjUpperMat_apply_10, Int.cast_mul, Gamma0_mem.mp hx0, zero_mul]
  · convert hxH using 1
    ext
    simp only [val_gamma0Units, Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk, conjUpperMat_apply_11]

omit [NeZero M] in
/-- `g x g⁻¹ = !![a, b/q; q c, d]` in the multiplicative form, which avoids inverting `g`. -/
theorem conjUpperMat_mul_heckeMatrix {q : ℕ} [NeZero q] {x : ↥(GammaH M H)}
    (hx : (q : ℤ) ∣ ((x : SL(2, ℤ)) 0 1)) :
    (Matrix.SpecialLinearGroup.mapGL ℝ (conjUpperMat q (x : SL(2, ℤ)) hx) : GL (Fin 2) ℝ) *
        ModularForm.heckeMatrix q 0 =
      ModularForm.heckeMatrix q 0 *
        (Matrix.SpecialLinearGroup.mapGL ℝ (x : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
  have hq : q ≠ 0 := NeZero.ne q
  have hcast : ((((((x : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1) / q : ℤ)) : ℝ) * (q : ℝ) =
      (((x : SL(2, ℤ)) 0 1 : ℤ) : ℝ) := by
    exact_mod_cast Int.ediv_mul_cancel hx
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ModularForm.val_heckeMatrix hq]
  have e1 : ((Matrix.SpecialLinearGroup.mapGL ℝ (conjUpperMat q (x : SL(2, ℤ)) hx) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) =
      ((conjUpperMat q (x : SL(2, ℤ)) hx : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map
        (algebraMap ℤ ℝ) := rfl
  have e2 : ((Matrix.SpecialLinearGroup.mapGL ℝ (x : SL(2, ℤ)) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) =
      ((x : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := rfl
  rw [e1, e2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjUpperMat, Matrix.mul_apply, Fin.sum_univ_two, hcast, mul_comm]

omit [NeZero M] in
/-- If `g y g⁻¹` is in the level group then `q` divides the upper-right entry of `y`. -/
theorem dvd_of_conj_mem {q : ℕ} [NeZero q] {y : ↥(GammaH M H)}
    (hy : ModularForm.heckeMatrix q 0 * (levelEquiv M H y : ↥(levelGroup M H)) *
        (ModularForm.heckeMatrix q 0)⁻¹ ∈ levelGroup M H) :
    (q : ℤ) ∣ ((y : SL(2, ℤ)) 0 1) := by
  obtain ⟨z, -, hzeq⟩ := Subgroup.mem_map.mp hy
  have h1 : (Matrix.SpecialLinearGroup.mapGL ℝ (z : SL(2, ℤ)) : GL (Fin 2) ℝ) *
      ModularForm.heckeMatrix q 0 =
      ModularForm.heckeMatrix q 0 *
        (Matrix.SpecialLinearGroup.mapGL ℝ (y : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
    rw [hzeq, coe_levelEquiv]
    group
  have h2 : ((z : SL(2, ℤ)) 0 1 : ℝ) * (q : ℝ) = ((y : SL(2, ℤ)) 0 1 : ℝ) := by
    have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 1)
      (congrArg (fun w : GL (Fin 2) ℝ => ((w : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) h1)
    simpa [Matrix.mul_apply, Fin.sum_univ_two, ModularForm.val_heckeMatrix (NeZero.ne q),
      Matrix.map_apply] using h
  have h3 : ((z : SL(2, ℤ)) 0 1 : ℤ) * (q : ℤ) = ((y : SL(2, ℤ)) 0 1 : ℤ) := by
    exact_mod_cast h2
  refine ⟨((z : SL(2, ℤ)) 0 1), ?_⟩
  rw [mul_comm]
  exact h3.symm

omit [NeZero M] in
/-- Conjugating a `Γ_H`-element with upper-right entry divisible by `q` keeps it in the level
group. -/
theorem conj_mem {q : ℕ} [NeZero q] {x : ↥(GammaH M H)} (hx : (q : ℤ) ∣ ((x : SL(2, ℤ)) 0 1)) :
    ModularForm.heckeMatrix q 0 * (levelEquiv M H x : ↥(levelGroup M H)) *
      (ModularForm.heckeMatrix q 0)⁻¹ ∈ levelGroup M H := by
  refine Subgroup.mem_map.mpr ⟨conjUpperMat q (x : SL(2, ℤ)) hx, conjUpperMat_mem_of_dvd M H hx, ?_⟩
  rw [coe_levelEquiv, ← conjUpperMat_mul_heckeMatrix M H hx]
  group

omit [NeZero M] in
/-- **The stabiliser of the `Γ_H` coset is `Γ_HUpper`.** -/
theorem stabiliser_eq {q : ℕ} [NeZero q] :
    HeckeCoset.Transversal.stabiliser (levelGroup M H) (ModularForm.heckeMatrix q 0) =
      (GammaHUpper M H q).map (levelEquiv M H).toMonoidHom := by
  refine le_antisymm ?_ ?_
  · intro y hy
    obtain ⟨-, hyconj⟩ := HeckeCoset.Transversal.mem_stabiliser.mp hy
    obtain ⟨x, rfl⟩ := (levelEquiv M H).surjective y
    exact Subgroup.mem_map.mpr ⟨x, by
      rw [Subgroup.mem_subgroupOf, mem_Gamma0Upper_iff_dvd]
      exact dvd_of_conj_mem M H hyconj, rfl⟩
  · intro y hy
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hy
    exact HeckeCoset.Transversal.mem_stabiliser.mpr ⟨(levelEquiv M H t).2,
      conj_mem M H (dvd_of_mem_GammaHUpper M H q ⟨t, ht⟩)⟩

/-! ## The representatives: `g` times a translation -/

omit [NeZero M] in
/-- The translation `T^n` lies in `Γ_H(M)`. -/
theorem T_zpow_mem (n : ℤ) : ModularGroup.T ^ n ∈ GammaH M H := by
  rw [mem_GammaH_iff]
  have h0 : ModularGroup.T ^ n ∈ Gamma0 M := by
    rw [Gamma0_mem, ModularGroup.coe_T_zpow]; simp
  refine ⟨h0, ?_⟩
  have h1 : gamma0Units M ⟨ModularGroup.T ^ n, h0⟩ = 1 := by
    ext; rw [val_gamma0Units]
    show (((ModularGroup.T ^ n) 1 1 : ℤ) : ZMod M) = ((1 : (ZMod M)ˣ) : ZMod M)
    rw [ModularGroup.coe_T_zpow]; simp
  rw [h1]; exact one_mem H

omit [NeZero M] in
/-- The translation, as an element of `Γ_H(M)`. -/
def transl (n : ℤ) : ↥(GammaH M H) := ⟨ModularGroup.T ^ n, T_zpow_mem M H n⟩

omit [NeZero M] in
theorem coe_transl (n : ℤ) :
    ((transl M H n : ↥(GammaH M H)) : SL(2, ℤ)) = ModularGroup.T ^ n := rfl

omit [NeZero M] in
/-- `!![1,0;0,q] · !![1,n;0,1] = !![1,n;0,q]`. -/
theorem heckeMatrix_eq_mul_transl {q : ℕ} [NeZero q] (n : ℕ) :
    ModularForm.heckeMatrix q 0 * (levelEquiv M H (transl M H (n : ℤ)) : ↥(levelGroup M H)) =
      ModularForm.heckeMatrix q n := by
  have hq : q ≠ 0 := NeZero.ne q
  apply Units.ext
  rw [Units.val_mul, ModularForm.val_heckeMatrix hq, ModularForm.val_heckeMatrix hq, coe_levelEquiv,
    coe_transl,
    show ((Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ ((n : ℕ) : ℤ)) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
      ((ModularGroup.T ^ ((n : ℕ) : ℤ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map
        (algebraMap ℤ ℝ) from rfl,
    ModularGroup.coe_T_zpow]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-! ## Obligation 2: the cosets of `!![1,0;0,q]`, for `q ∣ M` -/

variable (q : ℕ) [NeZero q]

omit [NeZero M] in
/-- **The count**: for `q ∣ M` every element of `Γ_H` lies in exactly one of the `q` cosets of the
translations, `a · T^{-x} ∈ Γ_HUpper`. -/
theorem transl_transversal (hqM : q ∣ M) (a : ↥(GammaH M H)) :
    ∃! x : ZMod q, a * (transl M H ((x : ZMod q).val : ℤ))⁻¹ ∈ GammaHUpper M H q := by
  obtain ⟨haΓ0, -⟩ := mem_GammaH_iff.mp a.2
  have ha10 : ((q : ℤ)) ∣ ((a : SL(2, ℤ)) 1 0) :=
    (Int.natCast_dvd_natCast.mpr hqM).trans
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp haΓ0))
  have hunit : ((a : SL(2, ℤ)) 0 0 : ZMod q) * ((a : SL(2, ℤ)) 1 1 : ZMod q) = 1 := by
    have hdet := Matrix.SpecialLinearGroup.det_coe (a : SL(2, ℤ))
    rw [Matrix.det_fin_two] at hdet
    have hh := congrArg (fun z : ℤ => (z : ZMod q)) hdet
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_one] at hh
    rw [show (((a : SL(2, ℤ)) 1 0 : ℤ) : ZMod q) = 0 from
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ha10, mul_zero, sub_zero] at hh
    exact hh
  set x : ZMod q := ((a : SL(2, ℤ)) 0 1 : ZMod q) * ((a : SL(2, ℤ)) 1 1 : ZMod q) with hx
  have key : ∀ n : ℕ, (((a * (transl M H ((n : ℕ) : ℤ))⁻¹ : ↥(GammaH M H))):
      SL(2, ℤ)) 0 1 =
      ((a : SL(2, ℤ)) 0 1 : ℤ) - (n : ℤ) * ((a : SL(2, ℤ)) 0 0 : ℤ) := by
    intro n
    have h1 : (((a * (transl M H ((n : ℕ) : ℤ))⁻¹ : ↥(GammaH M H))) : SL(2, ℤ)) =
        (a : SL(2, ℤ)) * ModularGroup.T ^ (-((n : ℕ) : ℤ)) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, coe_transl, ← zpow_neg]
    rw [h1, Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val', Matrix.cons_val_fin_one]
    ring
  have hmem : ∀ n : ℕ, (a * (transl M H ((n : ℕ) : ℤ))⁻¹ ∈ GammaHUpper M H q) ↔
      ((n : ℕ) : ZMod q) = x := by
    intro n
    rw [Subgroup.mem_subgroupOf, mem_Gamma0Upper_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd,
      key n]
    push_cast
    constructor
    · intro h
      have h1 : ((n : ℕ) : ZMod q) * ((a : SL(2, ℤ)) 0 0 : ZMod q) =
          ((a : SL(2, ℤ)) 0 1 : ZMod q) := by
        rw [← sub_eq_zero]
        linear_combination -h
      rw [hx]
      calc ((n : ℕ) : ZMod q)
          = ((n : ℕ) : ZMod q) * 1 := (mul_one _).symm
        _ = ((n : ℕ) : ZMod q) * (((a : SL(2, ℤ)) 0 0 : ZMod q) * ((a : SL(2, ℤ)) 1 1 : ZMod q)) :=
              by rw [hunit]
        _ = (((n : ℕ) : ZMod q) * ((a : SL(2, ℤ)) 0 0 : ZMod q)) * ((a : SL(2, ℤ)) 1 1 : ZMod q) :=
              by rw [mul_assoc]
        _ = ((a : SL(2, ℤ)) 0 1 : ZMod q) * ((a : SL(2, ℤ)) 1 1 : ZMod q) := by rw [h1]
    · intro h
      rw [h, hx, mul_assoc,
        show ((a : SL(2, ℤ)) 1 1 : ZMod q) * ((a : SL(2, ℤ)) 0 0 : ZMod q) = 1 from by
          rw [mul_comm]; exact hunit, mul_one, sub_self]
  refine ⟨x, (hmem x.val).mpr (by simp), ?_⟩
  intro y hy
  have h1 : ((y.val : ℕ) : ZMod q) = x := (hmem y.val).mp hy
  rwa [ZMod.natCast_zmod_val] at h1

omit [NeZero M] in
/-- **The count, at the level group**: the stabiliser cosets of the `q` translations. It is the
`Γ_H` statement `transl_transversal` transported along `levelEquiv`, using `stabiliser_eq`. -/
theorem transl_transversal_stab (hqM : q ∣ M) (a : ↥(levelGroup M H)) :
    ∃! x : ZMod q, a * (levelEquiv M H (transl M H ((x.val : ℕ) : ℤ)))⁻¹ ∈
      HeckeCoset.Transversal.stabiliser (levelGroup M H) (ModularForm.heckeMatrix q 0) := by
  obtain ⟨x, hx, huniq⟩ := transl_transversal M H q hqM ((levelEquiv M H).symm a)
  refine ⟨x, ?_, ?_⟩
  · have h : (levelEquiv M H
        (((levelEquiv M H).symm a) * (transl M H ((x.val : ℕ) : ℤ))⁻¹) : ↥(levelGroup M H)) ∈
        HeckeCoset.Transversal.stabiliser (levelGroup M H) (ModularForm.heckeMatrix q 0) := by
      rw [stabiliser_eq]
      exact Subgroup.mem_map_of_mem _ hx
    rwa [map_mul, map_inv, MulEquiv.apply_symm_apply] at h
  · intro y hy
    have h : ((levelEquiv M H).symm a) * (transl M H ((y.val : ℕ) : ℤ))⁻¹ ∈ GammaHUpper M H q := by
      have h2 : (levelEquiv M H
          (((levelEquiv M H).symm a) * (transl M H ((y.val : ℕ) : ℤ))⁻¹) :
            ↥(levelGroup M H)) ∈
          HeckeCoset.Transversal.stabiliser (levelGroup M H) (ModularForm.heckeMatrix q 0) := by
        rw [show (levelEquiv M H
            (((levelEquiv M H).symm a) * (transl M H ((y.val : ℕ) : ℤ))⁻¹) : ↥(levelGroup M H)) =
            a * (levelEquiv M H (transl M H ((y.val : ℕ) : ℤ)))⁻¹ from by
          rw [map_mul, map_inv, MulEquiv.apply_symm_apply]]
        exact hy
      rw [stabiliser_eq, Subgroup.mem_map] at h2
      obtain ⟨z, hz, hz2⟩ := h2
      have hz3 : z = ((levelEquiv M H).symm a) * (transl M H ((y.val : ℕ) : ℤ))⁻¹ :=
        (levelEquiv M H).injective hz2
      rwa [hz3] at hz
    exact huniq y h

omit [NeZero M] in
/-- **The `q` cosets of `Γ_H(M) · !![1,0;0,q] · Γ_H(M)`**: the `q` matrices `!![1,x;0,q]`. The
transversal is four lines: the index, the count, and nothing else. -/
noncomputable def heckeUTransversal (hqM : q ∣ M) :
    HeckeCoset.Transversal (levelGroup M H) (ModularForm.heckeMatrix q 0) (ZMod q) :=
  HeckeCoset.Transversal.ofLevel
    (u := fun x : ZMod q => levelEquiv M H (transl M H ((x.val : ℕ) : ℤ)))
    (hu := transl_transversal_stab M H q hqM)

omit [NeZero M] in
/-- The transversal's representatives are the family's own matrices. -/
theorem heckeUTransversal_r (hqM : q ∣ M) (x : ZMod q) :
    (heckeUTransversal M H q hqM).r x = ModularForm.heckeMatrix q x.val :=
  heckeMatrix_eq_mul_transl M H (q := q) x.val

omit [NeZero M] in
/-- **`U_q` is the double-coset operator of `Γ_H(M) · !![1,0;0,q] · Γ_H(M)`.** -/
theorem sum_slash_heckeU_eq_doubleCosetOperator (hqM : q ∣ M) (k : ℤ) {f : ℍ → ℂ}
    (hf : ∀ γ ∈ levelGroup M H, f ∣[k] γ = f) :
    ∑ x : ZMod q, f ∣[k] ModularForm.heckeMatrix q x.val =
      HeckeCoset.doubleCosetOperator k (levelGroup M H) (ModularForm.heckeMatrix q 0)
        (by
          rw [ModularForm.det_heckeMatrix (NeZero.ne q)]
          exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)) f := by
  have hsum : (∑ x : ZMod q, f ∣[k] ModularForm.heckeMatrix q x.val) =
      ∑ x : ZMod q, f ∣[k] (heckeUTransversal M H q hqM).r x :=
    Finset.sum_congr rfl fun x _ => by rw [heckeUTransversal_r M H q hqM x]
  rw [hsum]
  exact (heckeUTransversal M H q hqM).sum_eq_doubleCosetOperator hf
    (fun γ hγ => HeckeCoset.det_pos_of_mem_mapSL hγ)
    (by
      rw [ModularForm.det_heckeMatrix (NeZero.ne q)]
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q))

omit [NeZero M] in
/-- **`U_q` is `Γ_H(M)`-invariant.** -/
theorem heckeU_slash_eq_self (hqM : q ∣ M) (k : ℤ) {f : ℍ → ℂ}
    (hf : ∀ γ ∈ levelGroup M H, f ∣[k] γ = f) (γ : GL (Fin 2) ℝ) (hγ : γ ∈ levelGroup M H) :
    (ModularForm.heckeU k q f) ∣[k] γ = ModularForm.heckeU k q f := by
  rw [heckeU_eq_sum_zmod k f]
  have hsum : (∑ x : ZMod q, f ∣[k] ModularForm.heckeMatrix q x.val) =
      ∑ x : ZMod q, f ∣[k] (heckeUTransversal M H q hqM).r x :=
    Finset.sum_congr rfl fun x _ => by rw [heckeUTransversal_r M H q hqM x]
  rw [hsum]
  exact (heckeUTransversal M H q hqM).slash_invariant hγ hf

end HeckeCosetGammaH

end
