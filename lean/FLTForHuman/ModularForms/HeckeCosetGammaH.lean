/-
  The `Γ_H(M)` Hecke double cosets: the whole family, in the double-coset language.

  The double coset `Γ_H(M) · g · Γ_H(M)` (`g = !![1,0;0,q]`) is a disjoint union of the left cosets
  of `Γ_HUpper(M,H,q)`, and this module states that once — as
  `HeckeCoset.Transversal (levelGroup M H) g ι` — for the index each Hecke operator is *defined*
  with. Everything else about the family is then the generic theory of
  `ModularForms/HeckeCosetSum.lean`.

  **The level pair.** `Γ_H(M) ⊓ g⁻¹Γ_H(M)g = Γ_HUpper(M,H,q)` is the `(0,1)`-entry read-off `b/q`
  (`stabiliser_eq`), together with `mem_stabiliser_iff`, which reads the same statement through
  `levelEquiv` and lets any family state its index in `Γ_H(M)`'s own language.

  **The index, `q ∣ M`.** The `q` matrices `!![1,x;0,q]` (`x : ZMod q`) are one representative per
  left coset: they are `g · T^x` (`heckeMatrix_eq_mul_transl`), and `T^x` runs over a transversal of
  `Γ_HUpper` exactly when `q ∣ M` (`transl_transversal_stab`). The transversal is `heckeUTransversal`
  and its sum is `U_q` — `heckeU`'s own definition, nothing reindexed.

  **The index, `ℓ ∤ M`.** The cosets are the projective line `ℙ¹(ℤ/ℓ) = OnePoint (ZMod ℓ)`: the
  point `x` is `!![1,x;0,ℓ]`, and `∞` is `ρ_∞ · diag ℓ` with `ρ_∞ = !![u,v;-M,ℓ]` the Bézout matrix
  of `uℓ + vM = 1`. The count is the complementary pair of congruences
  `a 0 1 ≡ x · a 0 0`, `a 0 0 ≡ 0` (`onePoint_eq`), which is `heckeTTTransversal`; its sum is the
  pin's `U_ℓ + (·) ∣ (ρ · diag ℓ)` (`heckeU_add_slash_eq_sum`).

  **The pin's index.** The pin writes its sums over `Γ_H(M) ⧸ Γ_HUpper(M,H,q)`, with representative
  `beta c = g · (c.out)⁻¹`. That family is `betaTransversal`, and the two sums are identified with
  the ones above by `Transversal.sum_eq_sum` — representative-independence *is* the index
  bijection, so no sum is ever reindexed term by term.

  The pin source's formulas are stated here as the port's own (`sum_beta_eq_heckeU`,
  `sum_beta_eq_heckeU_add`, `sum_beta_slash_eq`, `sum_beta_eq_doubleCosetOperator`); the pin source
  itself is wired in `Reserve/ModularForms/HeckeCosetDecompositionDropped.lean`, and the module it
  used to verify (`ModularForms/HeckeCosetDecomposition.lean`) is gone. -/
import FLTForHuman.ModularForms.Defs.CohCarrierLevel
import FLTForHuman.ModularForms.Defs.HeckeOperator
import FLTForHuman.ModularForms.Defs.HeckeRepresentatives
import FLTForHuman.ModularForms.HeckeCosetSum

set_option autoImplicit false

set_option linter.style.haveILetI false

noncomputable section

open scoped MatrixGroups ModularForm OnePoint

open UpperHalfPlane CongruenceSubgroup CohCarrier
open ModularForm.Level (Gamma0Upper mem_Gamma0Upper_iff_dvd BezoutPair)
open ModularForm.HeckeRepresentatives

namespace HeckeCosetGammaH

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ)

/-! ## The level group -/

/-- The image of `Γ_H(M)` in `GL(2,ℝ)`: the level group the Hecke operator lives in. -/
abbrev levelGroup : Subgroup (GL (Fin 2) ℝ) := (GammaH M H).map (Matrix.SpecialLinearGroup.mapGL ℝ)

/-- `Γ_H(M)` is isomorphic to its image in `GL(2,ℝ)`. -/
noncomputable def levelEquiv : ↥(GammaH M H) ≃* ↥(levelGroup M H) :=
  (GammaH M H).equivMapOfInjective (Matrix.SpecialLinearGroup.mapGL ℝ)
    Matrix.SpecialLinearGroup.mapGL_injective

@[simp] theorem coe_levelEquiv (x : ↥(GammaH M H)) :
    ((levelEquiv M H x : ↥(levelGroup M H)) : GL (Fin 2) ℝ) =
      (Matrix.SpecialLinearGroup.mapGL ℝ (x : SL(2, ℤ)) : GL (Fin 2) ℝ) := rfl

/-! ## Obligation 1: the level pair -/

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

/-- Conjugating a `Γ_H`-element with upper-right entry divisible by `q` keeps it in the level
group. -/
theorem conj_mem {q : ℕ} [NeZero q] {x : ↥(GammaH M H)} (hx : (q : ℤ) ∣ ((x : SL(2, ℤ)) 0 1)) :
    ModularForm.heckeMatrix q 0 * (levelEquiv M H x : ↥(levelGroup M H)) *
      (ModularForm.heckeMatrix q 0)⁻¹ ∈ levelGroup M H := by
  refine Subgroup.mem_map.mpr ⟨conjUpperMat q (x : SL(2, ℤ)) hx, conjUpperMat_mem_of_dvd M H hx, ?_⟩
  rw [coe_levelEquiv, ← conjUpperMat_mul_heckeMatrix M H hx]
  group

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

/-- The translation, as an element of `Γ_H(M)`. -/
def transl (n : ℤ) : ↥(GammaH M H) := ⟨ModularGroup.T ^ n, T_zpow_mem M H n⟩

theorem coe_transl (n : ℤ) :
    ((transl M H n : ↥(GammaH M H)) : SL(2, ℤ)) = ModularGroup.T ^ n := rfl

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

/-- **The `q` cosets of `Γ_H(M) · !![1,0;0,q] · Γ_H(M)`**: the `q` matrices `!![1,x;0,q]`. The
transversal is four lines: the index, the count, and nothing else. -/
noncomputable def heckeUTransversal (hqM : q ∣ M) :
    HeckeCoset.Transversal (levelGroup M H) (ModularForm.heckeMatrix q 0) (ZMod q) :=
  HeckeCoset.Transversal.ofLevel
    (u := fun x : ZMod q => levelEquiv M H (transl M H ((x.val : ℕ) : ℤ)))
    (hu := transl_transversal_stab M H q hqM)

/-- The transversal's representatives are the family's own matrices. -/
theorem heckeUTransversal_r (hqM : q ∣ M) (x : ZMod q) :
    (heckeUTransversal M H q hqM).r x = ModularForm.heckeMatrix q x.val :=
  heckeMatrix_eq_mul_transl M H (q := q) x.val

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

/-- The level-space dictionary of the quotient family: `a` fixes the left coset of `g` modulo the
level subgroup exactly when its preimage times `y⁻¹` is in `Γ_HUpper`. This is
`stabiliser_eq` read through `levelEquiv`, and it is what lets a family state its index in
`Γ_H(M)`'s language. -/
theorem mem_stabiliser_iff {q : ℕ} [NeZero q] {a : ↥(levelGroup M H)} {y : ↥(GammaH M H)} :
    a * (levelEquiv M H y)⁻¹ ∈
        HeckeCoset.Transversal.stabiliser (levelGroup M H) (ModularForm.heckeMatrix q 0) ↔
      (levelEquiv M H).symm a * y⁻¹ ∈ GammaHUpper M H q := by
  rw [stabiliser_eq, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, hxeq⟩
    have hxeq' : levelEquiv M H x = a * (levelEquiv M H y)⁻¹ := hxeq
    have hx' : x = (levelEquiv M H).symm a * y⁻¹ := by
      apply (levelEquiv M H).injective
      rw [hxeq']
      show a * (levelEquiv M H y)⁻¹ = levelEquiv M H ((levelEquiv M H).symm a * y⁻¹)
      rw [map_mul, map_inv, MulEquiv.apply_symm_apply]
    rwa [hx'] at hx
  · intro h
    refine ⟨(levelEquiv M H).symm a * y⁻¹, h, ?_⟩
    show levelEquiv M H ((levelEquiv M H).symm a * y⁻¹) = a * (levelEquiv M H y)⁻¹
    rw [map_mul, map_inv, MulEquiv.apply_symm_apply]

/-! ## The `ℓ ∤ M` double coset: the projective-line index

For `ℓ` prime and `ℓ ∤ M` the double coset `Γ_H(M) · !![1,0;0,ℓ] · Γ_H(M)` is indexed by the
projective line `ℙ¹(ℤ/ℓ)`, i.e. `OnePoint (ZMod ℓ)` — the index `heckeRep` and
`heckeT_eq_sum_onePoint` already use. The point `x` is the matrix `!![1,x;0,ℓ] = g · T^x`; `∞` is
`ρ_∞ · diag ℓ`, with `ρ_∞ = !![u, v; -M, ℓ]` the Bézout matrix of `u ℓ + v M = 1`.

The two cases are complementary, and that is the whole count: `a` lies in the point coset of `x`
iff `a 0 1 ≡ x · a 0 0 (mod ℓ)`, which has a unique solution iff `a 0 0` is invertible mod `ℓ`, and
`∞` covers exactly the matrices with `a 0 0 ≡ 0`. Stated as the `∃!` hypothesis of
`Transversal.ofLevel`, this is the family's index. -/

section ProjectiveLine

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ} {ℓ : ℕ}

/-- The Bézout matrix `!![u, v; -M, ℓ]`, in `Γ₀(M)`: the `∞` representative modulo the level
element `gammaInf`. -/
private def rhoInf (M ℓ : ℕ) (B : ModularForm.Level.BezoutPair (ℓ : ℤ) (M : ℤ)) : Gamma0 M :=
  ⟨⟨!![B.u, B.v; -(M : ℤ), (ℓ : ℤ)], by rw [Matrix.det_fin_two_of]; linear_combination B.huv⟩,
    Gamma0_mem.mpr (by show ((-(M : ℤ) : ℤ) : ZMod M) = 0; simp)⟩

private theorem rhoInf_apply_11 (M ℓ : ℕ) (B : ModularForm.Level.BezoutPair (ℓ : ℤ) (M : ℤ)) :
    (((rhoInf M ℓ B : Gamma0 M) : SL(2, ℤ)) 1 1 : ℤ) = ℓ := rfl

variable (M H ℓ)

/-- The `∞` representative of the `ℓ`-coset, as an element of `Γ_H(M)`: the Bézout matrix
`!![1, -v; M, u ℓ]`. Its inverse is the `∞` coset representative `ρ_∞ · diag ℓ` up to `g`. -/
private noncomputable def gammaInf (B : ModularForm.Level.BezoutPair (ℓ : ℤ) (M : ℤ)) :
    ↥(GammaH M H) :=
  ⟨(⟨!![1, -B.v; (M : ℤ), B.u * ℓ], by rw [Matrix.det_fin_two_of]; linear_combination B.huv⟩ :
      SL(2, ℤ)), by
    refine mem_GammaH_iff.mpr ⟨?_, ?_⟩
    · exact Gamma0_mem.mpr (by show (((M : ℤ)) : ZMod M) = 0; simp)
    · have h0 : (⟨!![1, -B.v; (M : ℤ), B.u * ℓ],
          by rw [Matrix.det_fin_two_of]; linear_combination B.huv⟩ : SL(2, ℤ)) ∈ Gamma0 M :=
        Gamma0_mem.mpr (by show (((M : ℤ)) : ZMod M) = 0; simp)
      have h : gamma0Units M ⟨_, h0⟩ = 1 := by
        ext; rw [val_gamma0Units]
        show (((B.u * ℓ : ℤ)) : ZMod M) = ((1 : (ZMod M)ˣ) : ZMod M)
        have : (B.u * ℓ : ℤ) = 1 - B.v * M := by linear_combination B.huv
        rw [this]; push_cast; simp
      rw [h]; exact one_mem H⟩

/-- The `(0,1)` entry of `a · gammaInf`. -/
private theorem entry_mul_gammaInf (B : ModularForm.Level.BezoutPair (ℓ : ℤ) (M : ℤ))
    (a : ↥(GammaH M H)) :
    ((a * gammaInf M H ℓ B : ↥(GammaH M H)) : SL(2, ℤ)) 0 1
      = -B.v * (a : SL(2, ℤ)) 0 0 + B.u * ℓ * (a : SL(2, ℤ)) 0 1 := by
  rw [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  simp [gammaInf]
  ring

/-- The `(0,1)` entry of `a · T^{-x}`. -/
private theorem entry_mul_transl_inv (a : ↥(GammaH M H)) (n : ℤ) :
    ((a * (transl M H n)⁻¹ : ↥(GammaH M H)) : SL(2, ℤ)) 0 1
      = (a : SL(2, ℤ)) 0 1 - n * (a : SL(2, ℤ)) 0 0 := by
  have h1 : (((a * (transl M H n)⁻¹ : ↥(GammaH M H))) : SL(2, ℤ)) =
      (a : SL(2, ℤ)) * ModularGroup.T ^ (-n) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, coe_transl, ← zpow_neg]
  rw [h1, Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val', Matrix.cons_val_fin_one]
  ring

/-- Membership in `Γ_HUpper` read on the `(0,1)` entry modulo `ℓ`. -/
private theorem mem_GammaHUpper_iff {x : ↥(GammaH M H)} :
    x ∈ GammaHUpper M H ℓ ↔ (((x : SL(2, ℤ)) 0 1 : ℤ) : ZMod ℓ) = 0 := by
  rw [Subgroup.mem_subgroupOf, mem_Gamma0Upper_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- The family's `∞`-and-point representatives inside `Γ_H(M)`: `∞ ↦ gammaInf⁻¹`,
`x ↦ T^x`. Inverting `∞`'s is what makes `g · u` the concrete matrix `ρ_∞ · diag ℓ`. -/
private noncomputable def usalf (B : ModularForm.Level.BezoutPair (ℓ : ℤ) (M : ℤ)) :
    OnePoint (ZMod ℓ) → ↥(GammaH M H) :=
  fun o => Option.elim o (gammaInf M H ℓ B)⁻¹ fun x => transl M H ((x.val : ℕ) : ℤ)

private theorem usalf_infty (B : ModularForm.Level.BezoutPair (ℓ : ℤ) (M : ℤ)) :
    usalf M H ℓ B ∞ = (gammaInf M H ℓ B)⁻¹ := rfl

private theorem usalf_coe (B : ModularForm.Level.BezoutPair (ℓ : ℤ) (M : ℤ))
    (x : ZMod ℓ) : usalf M H ℓ B ↑x = transl M H ((x.val : ℕ) : ℤ) := rfl

/-- **The pin's `ρ` and the Bézout matrix differ by a level element.** This is the `hρ` hypothesis
read as a statement about `Γ_H(M)`: `ρ` and `ρ_∞` have the same `(1,1)` entry modulo `M`, hence the
same `Γ_H` character. -/
theorem mul_rhoInf_inv_mem_GammaH (B : ModularForm.Level.BezoutPair (ℓ : ℤ) (M : ℤ))
    {ρ : Gamma0 M} (hρ : (((ρ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = ℓ) :
    (ρ : SL(2, ℤ)) * (((rhoInf M ℓ B : Gamma0 M) : SL(2, ℤ)))⁻¹ ∈ GammaH M H := by
  rw [mem_GammaH_iff]
  refine ⟨(ρ * (rhoInf M ℓ B)⁻¹).2, ?_⟩
  have e1 : (⟨(ρ : SL(2, ℤ)) * ((rhoInf M ℓ B : Gamma0 M) : SL(2, ℤ))⁻¹,
      (ρ * (rhoInf M ℓ B)⁻¹).2⟩ : Gamma0 M) = ρ * (rhoInf M ℓ B)⁻¹ := rfl
  rw [e1, map_mul, map_inv]
  have hu : gamma0Units M ρ = gamma0Units M (rhoInf M ℓ B) := by
    ext; rw [val_gamma0Units, val_gamma0Units]
    show ((((ρ : SL(2, ℤ)) 1 1 : ℤ)) : ZMod M) =
      (((((rhoInf M ℓ B : Gamma0 M) : SL(2, ℤ)) 1 1 : ℤ)) : ZMod M)
    rw [hρ, rhoInf_apply_11, Int.cast_natCast]
  rw [hu, mul_inv_cancel]
  exact one_mem H



end ProjectiveLine

section ProjectiveLineField

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ} {ℓ : ℕ} [Fact ℓ.Prime]

local instance : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩

variable (M H ℓ)

/-- **The `∞` representative**: `g · gammaInf⁻¹ = ρ_∞ · diag ℓ`. -/
private theorem heckeMatrix_mul_gammaInf_inv (B : ModularForm.Level.BezoutPair (ℓ : ℤ) (M : ℤ)) :
    ModularForm.heckeMatrix ℓ 0 * (levelEquiv M H (gammaInf M H ℓ B) : ↥(levelGroup M H))⁻¹ =
      (Matrix.SpecialLinearGroup.mapGL ℝ ((rhoInf M ℓ B : Gamma0 M) : SL(2, ℤ)) :
          GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix ℓ := by
  have hℓ : ℓ ≠ 0 := NeZero.ne ℓ
  have e3 : ((↑(((levelEquiv M H (gammaInf M H ℓ B))⁻¹ : ↥(levelGroup M H))) : GL (Fin 2) ℝ)) =
      (Matrix.SpecialLinearGroup.mapGL ℝ (((gammaInf M H ℓ B : ↥(GammaH M H)) : SL(2, ℤ))⁻¹) :
        GL (Fin 2) ℝ) := by
    rw [Subgroup.coe_inv, coe_levelEquiv, map_inv]
  have e4 : ((Matrix.SpecialLinearGroup.mapGL ℝ ((rhoInf M ℓ B : Gamma0 M) : SL(2, ℤ)) :
        GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      ((((rhoInf M ℓ B : Gamma0 M) : SL(2, ℤ))) : Matrix (Fin 2) (Fin 2) ℤ).map
        (algebraMap ℤ ℝ) := rfl
  have e5 : ((Matrix.SpecialLinearGroup.mapGL ℝ (((gammaInf M H ℓ B : ↥(GammaH M H)) : SL(2, ℤ))⁻¹) :
        GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      ((((gammaInf M H ℓ B : ↥(GammaH M H)) : SL(2, ℤ))⁻¹ : SL(2, ℤ)) :
        Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := rfl
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ModularForm.val_heckeMatrix hℓ,
    ModularForm.val_heckeDiagMatrix hℓ, e3, e5, e4,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gammaInf, rhoInf, Matrix.mul_apply, Fin.sum_univ_two]
  · ring


/-- **The count**: every `a ∈ Γ_H(M)` lies in the coset of exactly one point of `ℙ¹(ℤ/ℓ)`. The
point case solves `x · a 0 0 ≡ a 0 1 (mod ℓ)` uniquely when `a 0 0` is a unit, and `∞` covers the
matrices with `a 0 0 ≡ 0` — for which the determinant makes `a 0 1` a unit, so no point case can
solve. -/
private theorem onePoint_eq (B : ModularForm.Level.BezoutPair (ℓ : ℤ) (M : ℤ))
    (a : ↥(GammaH M H)) :
    ∃! o : OnePoint (ZMod ℓ), a * (usalf M H ℓ B o)⁻¹ ∈ GammaHUpper M H ℓ := by
  have hdet : ((a : SL(2, ℤ)) 0 0 : ZMod ℓ) * ((a : SL(2, ℤ)) 1 1 : ZMod ℓ)
      - ((a : SL(2, ℤ)) 0 1 : ZMod ℓ) * ((a : SL(2, ℤ)) 1 0 : ZMod ℓ) = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe (a : SL(2, ℤ))
    rw [Matrix.det_fin_two] at h
    have h' := congrArg (fun z : ℤ => (z : ZMod ℓ)) h
    push_cast at h'
    exact h'
  have hv : ((B.v : ℤ) : ZMod ℓ) ≠ 0 := by
    intro h
    have h' := congrArg (fun z : ℤ => (z : ZMod ℓ)) B.huv
    push_cast at h'
    simp only [h, ZMod.natCast_self, mul_zero, zero_mul, add_zero] at h'
    exact zero_ne_one h'
  by_cases h0 : ((a : SL(2, ℤ)) 0 0 : ZMod ℓ) = 0
  · refine ⟨∞, ?_, ?_⟩
    · show a * (usalf M H ℓ B ∞)⁻¹ ∈ GammaHUpper M H ℓ
      rw [usalf_infty, inv_inv, mem_GammaHUpper_iff, entry_mul_gammaInf]
      push_cast
      simp only [h0, ZMod.natCast_self, mul_zero, zero_mul, add_zero]
    · intro o ho
      cases o with
      | infty => rfl
      | coe x =>
          exfalso
          have hx' : a * (usalf M H ℓ B ↑x)⁻¹ ∈ GammaHUpper M H ℓ := ho
          rw [usalf_coe, mem_GammaHUpper_iff, entry_mul_transl_inv] at hx'
          push_cast at hx'
          simp only [ZMod.natCast_val, ZMod.cast_id', id, h0, mul_zero, sub_zero] at hx'
          have h01 : ((a : SL(2, ℤ)) 0 1 : ZMod ℓ) ≠ 0 := by
            intro h
            simp only [h, h0, zero_mul, sub_zero] at hdet
            exact zero_ne_one hdet
          exact h01 hx'
  · set x₀ : ZMod ℓ :=
      ((a : SL(2, ℤ)) 0 1 : ZMod ℓ) * (((a : SL(2, ℤ)) 0 0 : ZMod ℓ))⁻¹ with hx₀
    refine ⟨↑x₀, ?_, ?_⟩
    · show a * (usalf M H ℓ B ↑x₀)⁻¹ ∈ GammaHUpper M H ℓ
      rw [usalf_coe, mem_GammaHUpper_iff, entry_mul_transl_inv]
      push_cast
      rw [ZMod.natCast_val, ZMod.cast_id', id, hx₀, mul_assoc, inv_mul_cancel₀ h0, mul_one,
        sub_self]
    · intro o ho
      cases o with
      | infty =>
          exfalso
          have hx' : a * (usalf M H ℓ B ∞)⁻¹ ∈ GammaHUpper M H ℓ := ho
          rw [usalf_infty, inv_inv, mem_GammaHUpper_iff, entry_mul_gammaInf] at hx'
          push_cast at hx'
          simp only [ZMod.natCast_self, mul_zero, zero_mul, add_zero] at hx'
          exact (mul_ne_zero (neg_ne_zero.mpr hv) h0) hx'
      | coe y =>
          have hx' : a * (usalf M H ℓ B ↑y)⁻¹ ∈ GammaHUpper M H ℓ := ho
          rw [usalf_coe, mem_GammaHUpper_iff, entry_mul_transl_inv] at hx'
          push_cast at hx'
          simp only [ZMod.natCast_val, ZMod.cast_id', id, sub_eq_zero] at hx'
          rw [OnePoint.coe_eq_coe, hx₀, hx', mul_assoc, mul_inv_cancel₀ h0, mul_one]

/-- **The `ℓ`-cosets of `Γ_H(M) · !![1,0;0,ℓ] · Γ_H(M)`**: the projective line `ℙ¹(ℤ/ℓ)`. -/
noncomputable def heckeTTTransversal (B : ModularForm.Level.BezoutPair (ℓ : ℤ) (M : ℤ)) :
    HeckeCoset.Transversal (levelGroup M H) (ModularForm.heckeMatrix ℓ 0) (OnePoint (ZMod ℓ)) :=
  HeckeCoset.Transversal.ofLevel
    (u := fun o => levelEquiv M H (usalf M H ℓ B o))
    (hu := by
      intro a
      obtain ⟨o, ho, huniq⟩ := onePoint_eq M H ℓ B ((levelEquiv M H).symm a)
      refine ⟨o, ?_, ?_⟩
      · show a * (levelEquiv M H (usalf M H ℓ B o))⁻¹ ∈
          HeckeCoset.Transversal.stabiliser (levelGroup M H) (ModularForm.heckeMatrix ℓ 0)
        rw [mem_stabiliser_iff M H]
        exact ho
      · intro o' ho'
        refine huniq o' ((mem_stabiliser_iff M H).mp ?_)
        exact ho')

theorem heckeTTTransversal_r_infty (B : ModularForm.Level.BezoutPair (ℓ : ℤ) (M : ℤ)) :
    (heckeTTTransversal M H ℓ B).r ∞ =
      (Matrix.SpecialLinearGroup.mapGL ℝ ((rhoInf M ℓ B : Gamma0 M) : SL(2, ℤ)) :
        GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix ℓ := by
  have h : (heckeTTTransversal M H ℓ B).r ∞ =
      ModularForm.heckeMatrix ℓ 0 *
        (levelEquiv M H (gammaInf M H ℓ B) : ↥(levelGroup M H))⁻¹ := by
    rw [show (heckeTTTransversal M H ℓ B).r ∞ =
        ModularForm.heckeMatrix ℓ 0 * ↑(levelEquiv M H (usalf M H ℓ B ∞)) from rfl,
      usalf_infty, map_inv, Subgroup.coe_inv]
  rw [h]
  exact heckeMatrix_mul_gammaInf_inv M H ℓ B

theorem heckeTTTransversal_r_coe (B : ModularForm.Level.BezoutPair (ℓ : ℤ) (M : ℤ))
    (x : ZMod ℓ) :
    (heckeTTTransversal M H ℓ B).r ↑x = ModularForm.heckeMatrix ℓ x.val := by
  rw [show (heckeTTTransversal M H ℓ B).r ↑x =
      ModularForm.heckeMatrix ℓ 0 * ↑(levelEquiv M H (usalf M H ℓ B ↑x)) from rfl, usalf_coe]
  exact heckeMatrix_eq_mul_transl M H x.val

/-- **`U_ℓ + f ∣ (ρ · diag ℓ)` is the coset sum over the projective line**, for `ℓ ∤ M`. The two
legs are the pin's: the point cosets are `heckeU`'s own summands, and the `∞` coset is
`ρ_∞ · diag ℓ`, which `mul_rhoInf_inv_mem_GammaH` turns into the pin's `ρ`. This is the `ℓ ∤ M`
counterpart of `heckeU_eq_sum_zmod`: the pin's summands *are* the transversal, so nothing is
reindexed. -/
theorem heckeU_add_slash_eq_sum (B : ModularForm.Level.BezoutPair (ℓ : ℤ) (M : ℤ)) (k : ℤ)
    {f : ℍ → ℂ} (hf : ∀ γ ∈ levelGroup M H, f ∣[k] γ = f) {ρ : Gamma0 M}
    (hρ : (((ρ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = ℓ) :
    ModularForm.heckeU k ℓ f +
        f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ) *
          ModularForm.heckeDiagMatrix ℓ) =
      ∑ o : OnePoint (ZMod ℓ), f ∣[k] (heckeTTTransversal M H ℓ B).r o := by
  have hsplit : (∑ o : OnePoint (ZMod ℓ), f ∣[k] (heckeTTTransversal M H ℓ B).r o) =
      f ∣[k] ((heckeTTTransversal M H ℓ B).r ∞) +
        ∑ x : ZMod ℓ, f ∣[k] ((heckeTTTransversal M H ℓ B).r ↑x) := by
    rw [show (∑ o : OnePoint (ZMod ℓ), f ∣[k] (heckeTTTransversal M H ℓ B).r o) =
        ∑ o : Option (ZMod ℓ), f ∣[k] (heckeTTTransversal M H ℓ B).r o from rfl,
      Fintype.sum_option]
    rfl
  have hdiag : f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ) *
        ModularForm.heckeDiagMatrix ℓ) =
      f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ ((rhoInf M ℓ B : Gamma0 M) : SL(2, ℤ)) :
        GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix ℓ) := by
    have hmem : (Matrix.SpecialLinearGroup.mapGL ℝ
        ((ρ : SL(2, ℤ)) * (((rhoInf M ℓ B : Gamma0 M) : SL(2, ℤ)))⁻¹) : GL (Fin 2) ℝ) ∈
        levelGroup M H :=
      Subgroup.mem_map_of_mem _ (mul_rhoInf_inv_mem_GammaH M H ℓ B hρ)
    conv_lhs =>
      rw [show (Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ) =
          (Matrix.SpecialLinearGroup.mapGL ℝ
              ((ρ : SL(2, ℤ)) * (((rhoInf M ℓ B : Gamma0 M) : SL(2, ℤ)))⁻¹) : GL (Fin 2) ℝ) *
            (Matrix.SpecialLinearGroup.mapGL ℝ ((rhoInf M ℓ B : Gamma0 M) : SL(2, ℤ)) :
              GL (Fin 2) ℝ) from by
        rw [← map_mul, inv_mul_cancel_right]]
    rw [mul_assoc, SlashAction.slash_mul, hf _ hmem]
  rw [hsplit, heckeTTTransversal_r_infty]
  simp only [heckeTTTransversal_r_coe]
  rw [hdiag, ← heckeU_eq_sum_zmod k f, add_comm]

end ProjectiveLineField


section

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (q : ℕ) [NeZero q]

noncomputable def beta (c : ↥(GammaH M H) ⧸ GammaHUpper M H q) : GL (Fin 2) ℝ :=
  ModularForm.heckeMatrix q 0 *
    (Matrix.SpecialLinearGroup.mapGL ℝ (((c.out : ↥(GammaH M H)) : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ)

theorem mapGL_conjL_mul_heckeMatrix (t : ↥(GammaHUpper M H q)) :
    (Matrix.SpecialLinearGroup.mapGL ℝ ((conjL M H q t : ↥(GammaH M H)) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
        ModularForm.heckeMatrix q 0 =
      ModularForm.heckeMatrix q 0 *
        (Matrix.SpecialLinearGroup.mapGL ℝ (((t : ↥(GammaH M H)) : SL(2, ℤ))) : GL (Fin 2) ℝ) := by
  have hq : q ≠ 0 := NeZero.ne q
  have hdvd : (q : ℤ) ∣ (((t : ↥(GammaH M H)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 :=
    dvd_of_mem_GammaHUpper M H q t
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ModularForm.val_heckeMatrix hq]
  have e1 : ((Matrix.SpecialLinearGroup.mapGL ℝ ((conjL M H q t : ↥(GammaH M H)) : SL(2, ℤ)) :
      GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      ((conjUpperMat q ((t : ↥(GammaH M H)) : SL(2, ℤ)) hdvd : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map
        (algebraMap ℤ ℝ) := rfl
  have e2 : ((Matrix.SpecialLinearGroup.mapGL ℝ ((t : ↥(GammaH M H)) : SL(2, ℤ)) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) =
      ((((t : ↥(GammaH M H)) : SL(2, ℤ))) : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := rfl
  have hcast : (((((t : ↥(GammaH M H)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 / q : ℤ) : ℝ) * q =
      (((((t : ↥(GammaH M H)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : ℝ) := by
    exact_mod_cast Int.ediv_mul_cancel hdvd
  rw [e1, e2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjUpperMat, Matrix.mul_apply, Fin.sum_univ_two, hcast, mul_comm]

/-! ## The `Γ_H` Hecke pair as a level quotient

`Γ_H(M)` and its level subgroup `Γ_HUpper(M,H,q) = Γ⁰(q) ⊓ Γ_H(M)` are a Hecke pair: the double
coset `Γ_H g Γ_H` is a disjoint union of left `Γ_H`-cosets indexed by `Γ_H ⧸ Γ_HUpper`. That is
`HeckeCoset.Transversal.ofLevel` at `K = Γ_H(M)`'s image in `GL(2,ℝ)` and `g = !![1,0;0,q]`, since
the stabiliser `K ⊓ g⁻¹Kg` *is* `Γ_HUpper` (`stabiliser_eq`). The family's
geometry is stated once, in `HeckeCosetGammaH`; what is built here is the pin's own index. -/

/-- **The `Γ_H` representatives are a transversal.** The three geometric fields — membership in
`Γ_H(M) · !![1,0;0,q] · Γ_H(M)`, distinctness and exhaustiveness — are the generic
`HeckeCoset.Transversal.ofLevel` construction: a family supplies its level pair and its index, and
the three fields follow. Here the index is the family's own `Γ_H(M) ⧸ Γ_HUpper(M,H,q)`, and the
unique-representation hypothesis is `stabiliser_eq`, the level-pair identity. -/
private noncomputable def betaTransversal [Fintype (↥(GammaH M H) ⧸ GammaHUpper M H q)] :
    HeckeCoset.Transversal (levelGroup M H) (ModularForm.heckeMatrix q 0)
      (↥(GammaH M H) ⧸ GammaHUpper M H q) :=
  HeckeCoset.Transversal.ofLevel (K := levelGroup M H) (g := ModularForm.heckeMatrix q 0)
    (u := fun c => (levelEquiv M H c.out)⁻¹)
    (hu := by
      intro a
      set a' : ↥(GammaH M H) := (levelEquiv M H).symm a with ha'
      set c : ↥(GammaH M H) ⧸ GammaHUpper M H q :=
        (QuotientGroup.mk (s := GammaHUpper M H q) a'⁻¹) with hc
      have hcls : a' * c.out ∈ GammaHUpper M H q := by
        have h : (QuotientGroup.mk (s := GammaHUpper M H q) a'⁻¹) =
            (QuotientGroup.mk (s := GammaHUpper M H q) c.out) := by
          rw [hc, QuotientGroup.out_eq']
        simpa using (QuotientGroup.eq.mp h)
      refine ⟨c, ?_, ?_⟩
      · change a * levelEquiv M H c.out ∈
          HeckeCoset.Transversal.stabiliser (levelGroup M H) (ModularForm.heckeMatrix q 0)
        rw [stabiliser_eq]
        exact Subgroup.mem_map.mpr ⟨a' * c.out, hcls, by simp [ha']⟩
      · intro d hd
        have hd' : a' * d.out ∈ GammaHUpper M H q := by
          simp only [inv_inv] at hd
          rw [stabiliser_eq] at hd
          obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp hd
          have hx' : x = a' * d.out := by
            apply (levelEquiv M H).injective
            have h1 : levelEquiv M H (a' * d.out) = a * levelEquiv M H d.out := by
              rw [map_mul, ha', MulEquiv.apply_symm_apply]
            rw [h1]
            simpa using hxeq
          rwa [hx'] at hx
        have h : (QuotientGroup.mk (s := GammaHUpper M H q) a'⁻¹) =
            (QuotientGroup.mk (s := GammaHUpper M H q) d.out) :=
          QuotientGroup.eq.mpr (by simpa using hd')
        rw [← QuotientGroup.out_eq' d, ← h, hc])

private theorem betaTransversal_r [Fintype (↥(GammaH M H) ⧸ GammaHUpper M H q)]
    (c : ↥(GammaH M H) ⧸ GammaHUpper M H q) :
    (betaTransversal M H q).r c = beta M H q c := by
  simp [betaTransversal, HeckeCoset.Transversal.ofLevel, beta]

/-- **The `Γ_H` coset sum is `Γ_H`-invariant**: the level invariance of a level-quotient
transversal, applied to `betaTransversal`. -/
theorem sum_beta_slash_eq (k : ℤ) {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (GammaH M H).map (Matrix.SpecialLinearGroup.mapGL ℝ), f ∣[k] γ = f)
    (γ : GL (Fin 2) ℝ) (hγ : γ ∈ (GammaH M H).map (Matrix.SpecialLinearGroup.mapGL ℝ)) :
    letI := (GammaHUpper M H q).fintypeQuotientOfFiniteIndex
    (∑ c : ↥(GammaH M H) ⧸ GammaHUpper M H q, f ∣[k] beta M H q c) ∣[k] γ =
      ∑ c : ↥(GammaH M H) ⧸ GammaHUpper M H q, f ∣[k] beta M H q c := by
  letI := (GammaHUpper M H q).fintypeQuotientOfFiniteIndex
  have h := (betaTransversal M H q).slash_invariant (k := k) hγ hf
  simpa only [betaTransversal_r] using h

/-- **The `Γ_H` coset sum is the double-coset operator.** -/
theorem sum_beta_eq_doubleCosetOperator (k : ℤ) {f : ℍ → ℂ}
    (hf : ∀ γ ∈ levelGroup M H, f ∣[k] γ = f) :
    letI := (GammaHUpper M H q).fintypeQuotientOfFiniteIndex
    (∑ c : ↥(GammaH M H) ⧸ GammaHUpper M H q, f ∣[k] beta M H q c)
      = HeckeCoset.doubleCosetOperator k (levelGroup M H) (ModularForm.heckeMatrix q 0)
          (by
            rw [ModularForm.det_heckeMatrix (NeZero.ne q)]
            exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)) f := by
  letI := (GammaHUpper M H q).fintypeQuotientOfFiniteIndex
  have h := (betaTransversal M H q).sum_eq_doubleCosetOperator (k := k) hf
    (fun γ hγ => HeckeCoset.det_pos_of_mem_mapSL hγ)
    (by
      rw [ModularForm.det_heckeMatrix (NeZero.ne q)]
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q))
  simpa only [betaTransversal_r] using h

end

section Affine

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (q : ℕ) [NeZero q]

/-- **The `Γ_H` coset sum is `U_q`.** Both sides are the coset sum of the same double coset
`Γ_H(M) · !![1,0;0,q] · Γ_H(M)`: the quotient-indexed family `beta` and the `q` matrices
`!![1,x;0,q]` are two transversals of it, so `Transversal.sum_eq_sum` identifies the sums on the
level space, and `heckeU_eq_sum_zmod` is the definition of `U_q` read over `ZMod q`. No reindexing
and no coset computation is needed: the index bijection is the theorem that two transversals have
the same sum. -/
theorem sum_beta_eq_heckeU (hqM : q ∣ M) (k : ℤ) {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (GammaH M H).map (Matrix.SpecialLinearGroup.mapGL ℝ), f ∣[k] γ = f) :
    letI := (GammaHUpper M H q).fintypeQuotientOfFiniteIndex
    (∑ c : ↥(GammaH M H) ⧸ GammaHUpper M H q, f ∣[k] beta M H q c) = ModularForm.heckeU k q f := by
  letI := (GammaHUpper M H q).fintypeQuotientOfFiniteIndex
  rw [ModularForm.HeckeRepresentatives.heckeU_eq_sum_zmod k f]
  calc ∑ c : ↥(GammaH M H) ⧸ GammaHUpper M H q, f ∣[k] beta M H q c
      = ∑ c : ↥(GammaH M H) ⧸ GammaHUpper M H q, f ∣[k] (betaTransversal M H q).r c := by
          simp only [betaTransversal_r]
    _ = ∑ x : ZMod q, f ∣[k] (heckeUTransversal M H q hqM).r x :=
          (betaTransversal M H q).sum_eq_sum (heckeUTransversal M H q hqM) hf
            (fun γ hγ => HeckeCoset.det_pos_of_mem_mapSL hγ) (by
              rw [ModularForm.det_heckeMatrix (NeZero.ne q)]
              exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q))
    _ = ∑ x : ZMod q, f ∣[k] ModularForm.heckeMatrix q x.val := by
          simp only [heckeUTransversal_r]

end Affine

section Projective

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [Fact ℓ.Prime]

scoped instance : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩

/-- A Bézout pair for `(ℓ, M)`, under the Hecke layer's name for it. -/
abbrev BezoutData (M ℓ : ℕ) := BezoutPair (ℓ : ℤ) (M : ℤ)

theorem exists_bezoutData (hℓM : ¬ ℓ ∣ M) : Nonempty (BezoutData M ℓ) := by
  have hcop : IsCoprime (ℓ : ℤ) (M : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hℓM)
  obtain ⟨u, v, h⟩ := hcop
  exact ⟨⟨u, v, by linear_combination h⟩⟩

variable {M ℓ}

/-- **The `Γ_H` coset sum is `U_ℓ + (·) ∣ (ρ · diag ℓ)`** for `ℓ ∤ M`. Both sides are the coset sum
of the same double coset: the quotient-indexed family `beta` and the projective-line family
`heckeTTTransversal` are two transversals of it, so `Transversal.sum_eq_sum`
identifies the sums on the level space, and `heckeU_add_slash_eq_sum` is the pin's reading of the
projective-line sum. The two per-term computations the earlier layer needed (`hterm`, `hinf`) are
gone: the point cosets' concrete matrices *are* the transversal's, so nothing is reindexed. -/
theorem sum_beta_eq_heckeU_add (B : BezoutData M ℓ) (ρ : Gamma0 M)
    (hρ : (((ρ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = ℓ) (k : ℤ) {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (GammaH M H).map (Matrix.SpecialLinearGroup.mapGL ℝ), f ∣[k] γ = f) :
    letI := (GammaHUpper M H ℓ).fintypeQuotientOfFiniteIndex
    (∑ c : ↥(GammaH M H) ⧸ GammaHUpper M H ℓ, f ∣[k] beta M H ℓ c) =
      ModularForm.heckeU k ℓ f +
        (f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ) *
          ModularForm.heckeDiagMatrix ℓ)) := by
  letI := (GammaHUpper M H ℓ).fintypeQuotientOfFiniteIndex
  have h := (betaTransversal M H ℓ).sum_eq_sum
    (heckeTTTransversal M H ℓ B) hf
    (fun γ hγ => HeckeCoset.det_pos_of_mem_mapSL hγ)
    (by
      rw [ModularForm.det_heckeMatrix (NeZero.ne ℓ)]
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne ℓ))
  rw [heckeU_add_slash_eq_sum M H ℓ B k hf hρ, ← h]
  simp only [betaTransversal_r]

end Projective


end HeckeCosetGammaH

end
