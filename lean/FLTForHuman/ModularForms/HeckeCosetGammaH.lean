/-
  The `Γ_H(M)` Hecke coset systems: the pin's representatives `beta`, the two indices, and the two
  sums that read `U_q` and `U_ℓ + (·) ∣ (ρ_∞ · diag ℓ)` off them.

  Everything is stated in `Γ_H(M)` and in `SL(2,ℤ)`. The quotient `Γ_H(M) ⧸ Γ_HUpper(M,H,q)` is the
  index the consumers already own (`heckeT` is its transfer), and each index is an `Equiv` with that
  quotient:

  * `translEquiv hqM : ZMod q ≃ Γ_H(M) ⧸ Γ_HUpper(M,H,q)`, for `q ∣ M`;
  * `onePointEquiv B : OnePoint (ZMod ℓ) ≃ Γ_H(M) ⧸ Γ_HUpper(M,H,ℓ)`, for `ℓ ∤ M` prime, the point
    `x` being `T^{-x}` and `∞` the Bézout matrix `gammaInf⁻¹`.

  The point is `T^{-x}` so that the two evaluations are the matrix identities
  `!![1,0;0,q] · T^x = !![1,x;0,q]` and `!![1,0;0,ℓ] · gammaInf = ρ_∞ · diag ℓ`: no summand is
  reindexed by hand. Both index equivalences are private; the public surface is the two sums, the
  representatives and the Bézout data. The `ℓ ∤ M` sum is stated with `ρ_∞ = rhoInf B`, the
  `Γ₀(M)`-factor of the `∞` coset; the pin's own `ρ` is a second name for that coset
  (`slash_rhoInf_diag`, available whenever `ρ 1 1 ≡ ℓ (mod M)`), which is how the pinned consumers
  state their operators.
-/
import FLTForHuman.ModularForms.Defs.CohCarrierLevel
import FLTForHuman.ModularForms.Defs.HeckeOperator
import FLTForHuman.ModularForms.Defs.HeckeRepresentatives
import FLTForHuman.GroupTheory.Corestriction

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm OnePoint

open UpperHalfPlane CongruenceSubgroup CohCarrier
open ModularForm.Level (BezoutPair mem_Gamma0Upper_iff_dvd)
open ModularForm.HeckeRepresentatives

namespace HeckeCosetGammaH

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ)

/-! ## The conjugation identity -/

/-- `conjUpperMat q A = !![a, b/q; qc, d]` conjugates `!![1,0;0,q]` back to `A`, in the
multiplicative form which avoids inverting the Hecke matrix. -/
private theorem conjUpperMat_mul_heckeMatrix {q : ℕ} [NeZero q] {A : SL(2, ℤ)}
    (hA : (q : ℤ) ∣ A 0 1) :
    (Matrix.SpecialLinearGroup.mapGL ℝ (conjUpperMat q A hA) : GL (Fin 2) ℝ) *
        ModularForm.heckeMatrix q 0 =
      ModularForm.heckeMatrix q 0 * (Matrix.SpecialLinearGroup.mapGL ℝ A : GL (Fin 2) ℝ) := by
  have hq : q ≠ 0 := NeZero.ne q
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ModularForm.val_heckeMatrix hq]
  have e1 : ((Matrix.SpecialLinearGroup.mapGL ℝ (conjUpperMat q A hA) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
      ((conjUpperMat q A hA : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := rfl
  have e2 : ((Matrix.SpecialLinearGroup.mapGL ℝ A : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      ((A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := rfl
  have hcast : (((((A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 / q : ℤ) : ℝ) * q) =
      (((A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) := by
    exact_mod_cast Int.ediv_mul_cancel hA
  rw [e1, e2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjUpperMat, Matrix.mul_apply, Fin.sum_univ_two, hcast, mul_comm]

/-- The same at the pin's spelling, `conjL`. -/
private theorem mapGL_conjL_mul_heckeMatrix {q : ℕ} [NeZero q] (t : ↥(GammaHUpper M H q)) :
    (Matrix.SpecialLinearGroup.mapGL ℝ ((conjL M H q t : ↥(GammaH M H)) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
        ModularForm.heckeMatrix q 0 =
      ModularForm.heckeMatrix q 0 *
        (Matrix.SpecialLinearGroup.mapGL ℝ (((t : ↥(GammaH M H)) : SL(2, ℤ))) : GL (Fin 2) ℝ) :=
  conjUpperMat_mul_heckeMatrix (dvd_of_mem_GammaHUpper M H q t)

/-! ## The translations -/

private theorem T_zpow_mem (n : ℤ) : ModularGroup.T ^ n ∈ GammaH M H := by
  rw [mem_GammaH_iff]
  have h0 : ModularGroup.T ^ n ∈ Gamma0 M := by
    rw [Gamma0_mem, ModularGroup.coe_T_zpow]; simp
  refine ⟨h0, ?_⟩
  have h1 : gamma0Units M ⟨ModularGroup.T ^ n, h0⟩ = 1 := by
    ext; rw [val_gamma0Units]
    show (((ModularGroup.T ^ n) 1 1 : ℤ) : ZMod M) = ((1 : (ZMod M)ˣ) : ZMod M)
    rw [ModularGroup.coe_T_zpow]; simp
  rw [h1]; exact one_mem H

/-- The translation `T^n`, as an element of `Γ_H(M)`. -/
private def transl (n : ℤ) : ↥(GammaH M H) := ⟨ModularGroup.T ^ n, T_zpow_mem M H n⟩

private theorem coe_transl (n : ℤ) :
    ((transl M H n : ↥(GammaH M H)) : SL(2, ℤ)) = ModularGroup.T ^ n := rfl

/-- `!![1,0;0,q] · T^x = !![1,x;0,q]`. -/
private theorem heckeMatrix_mul_transl {q : ℕ} [NeZero q] (x : ℕ) :
    ModularForm.heckeMatrix q 0 *
        (Matrix.SpecialLinearGroup.mapGL ℝ
          ((transl M H (((x : ℕ) : ℤ)) : ↥(GammaH M H)) : SL(2, ℤ)) : GL (Fin 2) ℝ) =
      ModularForm.heckeMatrix q x := by
  have hq : q ≠ 0 := NeZero.ne q
  apply Units.ext
  rw [Units.val_mul, ModularForm.val_heckeMatrix hq, ModularForm.val_heckeMatrix hq, coe_transl,
    show ((Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ ((x : ℕ) : ℤ)) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
      ((ModularGroup.T ^ ((x : ℕ) : ℤ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map
        (algebraMap ℤ ℝ) from rfl,
    ModularGroup.coe_T_zpow]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-! ## The pin's family and its cocycle -/

/-- The pin's coset representative `beta c = !![1,0;0,q] · c.out⁻¹`. -/
noncomputable def beta (q : ℕ) [NeZero q]
    (c : ↥(GammaH M H) ⧸ GammaHUpper M H q) : GL (Fin 2) ℝ :=
  ModularForm.heckeMatrix q 0 *
    (Matrix.SpecialLinearGroup.mapGL ℝ (((c.out : ↥(GammaH M H)) : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ)

/-- **The cocycle of the coset system.** Right multiplication by `γ` moves `beta c` to `beta (γ • c)`
up to the level element `conjL (transferAux γ c)`; this is the rearrangement of `transferAux`'s own
definition, and it is the only input of the invariance and of the period map. -/
theorem beta_mul (q : ℕ) [NeZero q] (γ : ↥(GammaH M H))
    (c : ↥(GammaH M H) ⧸ GammaHUpper M H q) :
    beta M H q (γ • c) * (Matrix.SpecialLinearGroup.mapGL ℝ (γ : SL(2, ℤ)) : GL (Fin 2) ℝ) =
      (Matrix.SpecialLinearGroup.mapGL ℝ
          ((conjL M H q (HeckeEis.transferAux (GammaHUpper M H q) γ c) : ↥(GammaH M H)) : SL(2, ℤ)) :
        GL (Fin 2) ℝ) * beta M H q c := by
  have key : (((γ • c).out : ↥(GammaH M H)) : SL(2, ℤ))⁻¹ * (γ : SL(2, ℤ)) =
      (((((HeckeEis.transferAux (GammaHUpper M H q) γ c : ↥(GammaHUpper M H q)) : ↥(GammaH M H))) :
          SL(2, ℤ))) * ((((c.out : ↥(GammaH M H))) : SL(2, ℤ)))⁻¹ := by
    simp only [HeckeEis.coe_transferAux, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  simp only [beta]
  rw [mul_assoc, ← map_mul, key, map_mul]
  conv_rhs => rw [← mul_assoc, mapGL_conjL_mul_heckeMatrix]
  group

/-- **The pin's coset sum is `Γ_H(M)`-invariant.** Right multiplication by `γ` permutes the cosets,
the transfer cocycle is a level element, and `f` is fixed by those. -/
theorem sum_beta_slash_eq (q : ℕ) [NeZero q] [Fintype (↥(GammaH M H) ⧸ GammaHUpper M H q)]
    (k : ℤ) {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (GammaH M H).map (Matrix.SpecialLinearGroup.mapGL ℝ), f ∣[k] γ = f)
    (γ : GL (Fin 2) ℝ) (hγ : γ ∈ (GammaH M H).map (Matrix.SpecialLinearGroup.mapGL ℝ)) :
    (∑ c : ↥(GammaH M H) ⧸ GammaHUpper M H q, f ∣[k] beta M H q c) ∣[k] γ =
      ∑ c : ↥(GammaH M H) ⧸ GammaHUpper M H q, f ∣[k] beta M H q c := by
  obtain ⟨γ₀, hγ₀, rfl⟩ := Subgroup.mem_map.mp hγ
  set γ₁ : ↥(GammaH M H) := ⟨γ₀, hγ₀⟩ with hγ₁
  have hcoe : (((γ₁ : ↥(GammaH M H))) : SL(2, ℤ)) = γ₀ := rfl
  rw [SlashAction.sum_slash]
  rw [show (Matrix.SpecialLinearGroup.mapGL ℝ γ₀ : GL (Fin 2) ℝ) =
      (Matrix.SpecialLinearGroup.mapGL ℝ ((γ₁ : ↥(GammaH M H)) : SL(2, ℤ)) : GL (Fin 2) ℝ) from by
    rw [hcoe]]
  rw [← Equiv.sum_comp (MulAction.toPerm γ₁) (fun c : ↥(GammaH M H) ⧸ GammaHUpper M H q =>
    (f ∣[k] beta M H q c) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ ((γ₁ : ↥(GammaH M H)) : SL(2, ℤ)) :
      GL (Fin 2) ℝ))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← SlashAction.slash_mul,
    show (MulAction.toPerm γ₁) c = γ₁ • c from rfl,
    beta_mul M H q γ₁ c, SlashAction.slash_mul,
    hf _ (Subgroup.mem_map_of_mem _
      (conjL M H q (HeckeEis.transferAux (GammaHUpper M H q) γ₁ c)).2)]

private theorem slash_beta_eq_of_mk (q : ℕ) [NeZero q] (k : ℤ) {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (GammaH M H).map (Matrix.SpecialLinearGroup.mapGL ℝ), f ∣[k] γ = f)
    (u : ↥(GammaH M H)) :
    f ∣[k] beta M H q (QuotientGroup.mk u) =
      f ∣[k] (ModularForm.heckeMatrix q 0 *
        (Matrix.SpecialLinearGroup.mapGL ℝ (((u : SL(2, ℤ)))⁻¹) : GL (Fin 2) ℝ)) := by
  obtain ⟨t, ht⟩ := QuotientGroup.mk_out_eq_mul (s := GammaHUpper M H q) u
  have key : beta M H q (QuotientGroup.mk u) =
      (Matrix.SpecialLinearGroup.mapGL ℝ ((conjL M H q t⁻¹ : ↥(GammaH M H)) : SL(2, ℤ)) :
          GL (Fin 2) ℝ) *
        (ModularForm.heckeMatrix q 0 *
          (Matrix.SpecialLinearGroup.mapGL ℝ (((u : SL(2, ℤ)))⁻¹) : GL (Fin 2) ℝ)) := by
    simp only [beta]
    rw [ht, Subgroup.coe_mul, mul_inv_rev, map_mul]
    conv_rhs => rw [← mul_assoc, mapGL_conjL_mul_heckeMatrix (t := t⁻¹)]
    rw [mul_assoc]
    rfl
  rw [key, SlashAction.slash_mul,
    hf _ (Subgroup.mem_map_of_mem _ (conjL M H q t⁻¹).2)]

/-! ## The index, `q ∣ M` -/

/-- `T^{-n}` inverted is `T^n`. -/
private theorem transl_neg_inv (n : ℤ) :
    (((transl M H (-n) : ↥(GammaH M H))) : SL(2, ℤ))⁻¹ = ((transl M H n : ↥(GammaH M H)) : SL(2, ℤ)) := by
  have h : (transl M H (-n))⁻¹ = transl M H n := by
    apply Subtype.ext
    rw [Subgroup.coe_inv, coe_transl, coe_transl, zpow_neg, inv_inv]
  rw [← Subgroup.coe_inv, h]

/-- **The index for `q ∣ M`**: the `q` translates `T^{-x}` are one representative per coset. -/
private def translEquiv {q : ℕ} [NeZero q] (hqM : q ∣ M) :
    ZMod q ≃ (↥(GammaH M H) ⧸ GammaHUpper M H q) :=
  Equiv.ofBijective
    (fun x : ZMod q => (QuotientGroup.mk (transl M H (-(((x.val : ℕ) : ℤ)))) :
      ↥(GammaH M H) ⧸ GammaHUpper M H q)) (by
    constructor
    · intro i j hij
      rw [QuotientGroup.eq] at hij
      rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, coe_transl, coe_transl,
        ← zpow_neg, ← zpow_add, mem_Gamma0Upper_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd,
        ModularGroup.coe_T_zpow] at hij
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Matrix.cons_val_zero] at hij
      have h1 : ((j.val : ℕ) : ZMod q) = ((i.val : ℕ) : ZMod q) := by
        push_cast at hij ⊢
        linear_combination -hij
      have h3 : j.val = i.val := by
        have h4 := (ZMod.natCast_eq_natCast_iff' j.val i.val q).mp h1
        rwa [Nat.mod_eq_of_lt (ZMod.val_lt j), Nat.mod_eq_of_lt (ZMod.val_lt i)] at h4
      exact ZMod.val_injective q h3.symm
    · intro c
      induction c using QuotientGroup.induction_on with
      | H a =>
      obtain ⟨h0, -⟩ := mem_GammaH_iff.mp a.2
      have hc : ((((a : SL(2, ℤ)) 1 0 : ℤ)) : ZMod q) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact (Int.natCast_dvd_natCast.mpr hqM).trans
          ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp h0))
      have hdet := Matrix.SpecialLinearGroup.det_coe (a : SL(2, ℤ))
      rw [Matrix.det_fin_two] at hdet
      have had : ((((a : SL(2, ℤ)) 0 0 : ℤ)) : ZMod q) * ((((a : SL(2, ℤ)) 1 1 : ℤ)) : ZMod q) = 1 := by
        have := congrArg (fun z : ℤ => (z : ZMod q)) hdet
        simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hc, mul_zero, sub_zero] at this
        exact this
      set jz : ZMod q := -((((a : SL(2, ℤ)) 0 1 : ℤ)) : ZMod q) * ((((a : SL(2, ℤ)) 0 0 : ℤ)) : ZMod q)
        with hjz
      refine ⟨jz, ?_⟩
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
        show (((transl M H (-(((jz.val : ℕ) : ℤ))) : ↥(GammaH M H))) : SL(2, ℤ))⁻¹ =
          ((transl M H (((jz.val : ℕ) : ℤ)) : ↥(GammaH M H)) : SL(2, ℤ)) from transl_neg_inv M H _,
        mem_Gamma0Upper_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
      simp only [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_transl,
        ModularGroup.coe_T_zpow, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.mul_apply, Fin.sum_univ_two]
      push_cast
      rw [ZMod.natCast_val, ZMod.cast_id', id, hjz]
      linear_combination (-((((a : SL(2, ℤ)) 0 1 : ℤ)) : ZMod q)) * had)

/-- **The `q ∣ M` evaluation**: the coset of `T^{-x}` is `U_q`'s own summand `!![1,x;0,q]`. -/
private theorem beta_translEquiv (q : ℕ) [NeZero q] (hqM : q ∣ M) (k : ℤ) {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (GammaH M H).map (Matrix.SpecialLinearGroup.mapGL ℝ), f ∣[k] γ = f)
    (x : ZMod q) :
    f ∣[k] beta M H q (translEquiv M H hqM x) = f ∣[k] ModularForm.heckeMatrix q x.val := by
  rw [show (translEquiv M H hqM) x = QuotientGroup.mk (transl M H (-(((x.val : ℕ) : ℤ)))) from rfl,
    slash_beta_eq_of_mk M H q k hf, transl_neg_inv]
  exact congrArg (fun w => f ∣[k] w) (heckeMatrix_mul_transl M H (q := q) x.val)

/-- **The pin's coset sum is `U_q`**, for `q ∣ M`. -/
theorem sum_beta_eq_heckeU (q : ℕ) [NeZero q] [Fintype (↥(GammaH M H) ⧸ GammaHUpper M H q)]
    (hqM : q ∣ M) (k : ℤ) {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (GammaH M H).map (Matrix.SpecialLinearGroup.mapGL ℝ), f ∣[k] γ = f) :
    (∑ c : ↥(GammaH M H) ⧸ GammaHUpper M H q, f ∣[k] beta M H q c) = ModularForm.heckeU k q f := by
  rw [ModularForm.HeckeRepresentatives.heckeU_eq_sum_zmod k f,
    ← Equiv.sum_comp (translEquiv M H hqM) (fun c : ↥(GammaH M H) ⧸ GammaHUpper M H q =>
      f ∣[k] beta M H q c)]
  exact Finset.sum_congr rfl fun x _ => beta_translEquiv M H q hqM k hf x

/-! ## The index, `ℓ ∤ M`: the projective line -/

section ProjectiveLine

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ} {ℓ : ℕ} [Fact ℓ.Prime]

local instance : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩

/-- The Bézout matrix `ρ_∞ = !![u, v; -M, ℓ]`, in `Γ₀(M)`: the `Γ₀(M)`-factor of the `∞` coset,
`β (∞) = ρ_∞ · diag ℓ`. -/
def rhoInf (M ℓ : ℕ) (B : BezoutPair (ℓ : ℤ) (M : ℤ)) : Gamma0 M :=
  ⟨⟨!![B.u, B.v; -(M : ℤ), (ℓ : ℤ)], by rw [Matrix.det_fin_two_of]; linear_combination B.huv⟩,
    Gamma0_mem.mpr (by show ((-(M : ℤ) : ℤ) : ZMod M) = 0; simp)⟩

private theorem rhoInf_apply_11 (M ℓ : ℕ) (B : BezoutPair (ℓ : ℤ) (M : ℤ)) :
    (((rhoInf M ℓ B : Gamma0 M) : SL(2, ℤ)) 1 1 : ℤ) = ℓ := rfl

variable (M H ℓ)

/-- The `∞` representative inside `Γ_H(M)`: the Bézout matrix `!![1, -v; M, u ℓ]`, whose inverse is
the `∞` coset representative. -/
private noncomputable def gammaInf (B : BezoutPair (ℓ : ℤ) (M : ℤ)) : ↥(GammaH M H) :=
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

/-- **The `∞` evaluation**: `!![1,0;0,ℓ] · gammaInf⁻¹ = ρ_∞ · diag ℓ`. -/
private theorem heckeMatrix_mul_gammaInf (B : BezoutPair (ℓ : ℤ) (M : ℤ)) :
    ModularForm.heckeMatrix ℓ 0 *
        (Matrix.SpecialLinearGroup.mapGL ℝ
          (((gammaInf M H ℓ B : ↥(GammaH M H)) : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) =
      (Matrix.SpecialLinearGroup.mapGL ℝ ((rhoInf M ℓ B : Gamma0 M) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
        ModularForm.heckeDiagMatrix ℓ := by
  have hℓ : ℓ ≠ 0 := NeZero.ne ℓ
  have e3 : ((Matrix.SpecialLinearGroup.mapGL ℝ
        (((gammaInf M H ℓ B : ↥(GammaH M H)) : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
      ((((gammaInf M H ℓ B : ↥(GammaH M H)) : SL(2, ℤ))⁻¹ : SL(2, ℤ)) :
        Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := rfl
  have e4 : ((Matrix.SpecialLinearGroup.mapGL ℝ ((rhoInf M ℓ B : Gamma0 M) : SL(2, ℤ)) :
        GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      ((((rhoInf M ℓ B : Gamma0 M) : SL(2, ℤ))) : Matrix (Fin 2) (Fin 2) ℤ).map
        (algebraMap ℤ ℝ) := rfl
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ModularForm.val_heckeMatrix hℓ, ModularForm.val_heckeDiagMatrix hℓ,
    e3, e4, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gammaInf, rhoInf, Matrix.mul_apply, Fin.sum_univ_two]
  · ring

/-- The representatives of `ℙ¹(ℤ/ℓ)` inside `Γ_H(M)`: `x ↦ T^{-x}` and `∞ ↦ gammaInf⁻¹`. -/
private def onePointRep (B : BezoutPair (ℓ : ℤ) (M : ℤ)) :
    OnePoint (ZMod ℓ) → ↥(GammaH M H) :=
  fun o => Option.elim o (gammaInf M H ℓ B) fun x => transl M H (-(((x.val : ℕ) : ℤ)))

/-- The `(0,1)` entry of `gammaInf⁻¹ · X`. -/
private theorem entry_gammaInf_inv_mul (B : BezoutPair (ℓ : ℤ) (M : ℤ)) (X : SL(2, ℤ)) :
    ((((gammaInf M H ℓ B : ↥(GammaH M H)) : SL(2, ℤ))⁻¹ * X : SL(2, ℤ))) 0 1 =
      B.u * (ℓ : ℤ) * (X 0 1 : ℤ) + B.v * (X 1 1 : ℤ) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  simp only [gammaInf, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

/-- The `(0,1)` entry of `T^n · X`. -/
private theorem entry_T_mul (n : ℤ) (X : SL(2, ℤ)) :
    (((ModularGroup.T ^ n * X : SL(2, ℤ)))) 0 1 = (X 0 1 : ℤ) + n * (X 1 1 : ℤ) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

/-- **The index for `ℓ ∤ M`**: the cosets are the projective line `ℙ¹(ℤ/ℓ)`, the point `x` being
`T^{-x}` and `∞` the Bézout matrix `gammaInf`. -/
private def onePointEquiv (B : BezoutPair (ℓ : ℤ) (M : ℤ)) :
    OnePoint (ZMod ℓ) ≃ (↥(GammaH M H) ⧸ GammaHUpper M H ℓ) :=
  Equiv.ofBijective
    (fun o : OnePoint (ZMod ℓ) => (QuotientGroup.mk (onePointRep M H ℓ B o) :
      ↥(GammaH M H) ⧸ GammaHUpper M H ℓ)) (by
    have hv : ((B.v : ℤ) : ZMod ℓ) ≠ 0 := by
      intro h
      have h' := congrArg (fun z : ℤ => (z : ZMod ℓ)) B.huv
      push_cast at h'
      simp only [h, ZMod.natCast_self, mul_zero, zero_mul, add_zero] at h'
      exact zero_ne_one h'
    constructor
    · rintro (_ | i) (_ | j) hij
      · rfl
      · exfalso
        simp only [onePointRep, Option.elim] at hij
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
          mem_Gamma0Upper_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd,
          entry_gammaInf_inv_mul, coe_transl, ModularGroup.coe_T_zpow] at hij
        simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one] at hij
        push_cast at hij
        exact hv (by simpa [ZMod.natCast_self] using hij)
      · exfalso
        simp only [onePointRep, Option.elim] at hij
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
          show (((transl M H (-(((i.val : ℕ) : ℤ))) : ↥(GammaH M H))) : SL(2, ℤ))⁻¹ =
            ((transl M H (((i.val : ℕ) : ℤ)) : ↥(GammaH M H)) : SL(2, ℤ)) from transl_neg_inv M H _,
          coe_transl, mem_Gamma0Upper_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd, entry_T_mul,
          gammaInf] at hij
        simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one] at hij
        push_cast at hij
        exact hv (neg_eq_zero.mp (by simpa [ZMod.natCast_self] using hij))
      · simp only [onePointRep, Option.elim] at hij
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, coe_transl,
          coe_transl, ← zpow_neg, ← zpow_add, mem_Gamma0Upper_iff_dvd,
          ← ZMod.intCast_zmod_eq_zero_iff_dvd, ModularGroup.coe_T_zpow] at hij
        simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one,
          Matrix.cons_val_zero] at hij
        have h1 : ((j.val : ℕ) : ZMod ℓ) = ((i.val : ℕ) : ZMod ℓ) := by
          push_cast at hij ⊢
          linear_combination -hij
        have h3 : j.val = i.val := by
          have h4 := (ZMod.natCast_eq_natCast_iff' j.val i.val ℓ).mp h1
          rwa [Nat.mod_eq_of_lt (ZMod.val_lt j), Nat.mod_eq_of_lt (ZMod.val_lt i)] at h4
        exact congrArg (fun x : ZMod ℓ => (some x : OnePoint (ZMod ℓ))) (ZMod.val_injective ℓ h3.symm)
    · intro c
      induction c using QuotientGroup.induction_on with
      | H a =>
      by_cases hd : ((((a : SL(2, ℤ)) 1 1 : ℤ)) : ZMod ℓ) = 0
      · refine ⟨∞, ?_⟩
        simp only [onePointRep, Option.elim]
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
          mem_Gamma0Upper_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd, entry_gammaInf_inv_mul]
        push_cast
        rw [ZMod.natCast_self, mul_zero, zero_mul, zero_add, hd, mul_zero]
      · refine ⟨↑(-((((a : SL(2, ℤ)) 0 1 : ℤ)) : ZMod ℓ) *
          ((((a : SL(2, ℤ)) 1 1 : ℤ)) : ZMod ℓ)⁻¹), ?_⟩
        set jz : ZMod ℓ := -((((a : SL(2, ℤ)) 0 1 : ℤ)) : ZMod ℓ) *
          ((((a : SL(2, ℤ)) 1 1 : ℤ)) : ZMod ℓ)⁻¹ with hjz
        simp only [onePointRep, Option.elim]
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
          show (((transl M H (-(((jz.val : ℕ) : ℤ))) : ↥(GammaH M H))) : SL(2, ℤ))⁻¹ =
            ((transl M H (((jz.val : ℕ) : ℤ)) : ↥(GammaH M H)) : SL(2, ℤ)) from transl_neg_inv M H _,
          coe_transl, mem_Gamma0Upper_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd, entry_T_mul]
        push_cast
        rw [ZMod.natCast_val, ZMod.cast_id', id, hjz]
        rw [mul_assoc, inv_mul_cancel₀ hd, mul_one, add_neg_cancel])

/-- The pin's `ρ` and the Bézout matrix differ by a level element: the hypothesis `hρ` read in
`Γ_H(M)`. -/
private theorem mul_rhoInf_inv_mem_GammaH (B : BezoutPair (ℓ : ℤ) (M : ℤ)) {ρ : Gamma0 M}
    (hρ : (((ρ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = ℓ) :
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

/-- **The point evaluation**: the coset of `T^{-x}` is `!![1,x;0,ℓ]`. -/
private theorem beta_onePointEquiv_coe (B : BezoutPair (ℓ : ℤ) (M : ℤ)) (k : ℤ) {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (GammaH M H).map (Matrix.SpecialLinearGroup.mapGL ℝ), f ∣[k] γ = f)
    (x : ZMod ℓ) :
    f ∣[k] beta M H ℓ (onePointEquiv M H ℓ B ↑x) = f ∣[k] ModularForm.heckeMatrix ℓ x.val := by
  rw [show (onePointEquiv M H ℓ B) ↑x =
      QuotientGroup.mk (transl M H (-(((x.val : ℕ) : ℤ)))) from rfl,
    slash_beta_eq_of_mk M H ℓ k hf, transl_neg_inv]
  exact congrArg (fun w => f ∣[k] w) (heckeMatrix_mul_transl M H (q := ℓ) x.val)

/-- **The `∞` evaluation**: the coset of `ρ_∞⁻¹` is `ρ_∞ · diag ℓ`. -/
private theorem beta_onePointEquiv_infty (B : BezoutPair (ℓ : ℤ) (M : ℤ)) (k : ℤ) {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (GammaH M H).map (Matrix.SpecialLinearGroup.mapGL ℝ), f ∣[k] γ = f) :
    f ∣[k] beta M H ℓ (onePointEquiv M H ℓ B ∞) =
      f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ ((rhoInf M ℓ B : Gamma0 M) : SL(2, ℤ)) :
        GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix ℓ) := by
  rw [show (onePointEquiv M H ℓ B) ∞ = QuotientGroup.mk (gammaInf M H ℓ B) from rfl,
    slash_beta_eq_of_mk M H ℓ k hf]
  exact congrArg (fun w => f ∣[k] w) (heckeMatrix_mul_gammaInf M H ℓ B)

end ProjectiveLine

section Projective

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [Fact ℓ.Prime]

scoped instance : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩

variable {M ℓ}

/-- **The pin's coset sum, `ℓ ∤ M`**: the `ℓ` finite cosets are `U_ℓ`, the `∞` coset is
`ρ_∞ · diag ℓ`. -/
theorem sum_beta_eq_heckeU_add [Fintype (↥(GammaH M H) ⧸ GammaHUpper M H ℓ)]
    (B : BezoutPair (ℓ : ℤ) (M : ℤ)) (k : ℤ) {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (GammaH M H).map (Matrix.SpecialLinearGroup.mapGL ℝ), f ∣[k] γ = f) :
    (∑ c : ↥(GammaH M H) ⧸ GammaHUpper M H ℓ, f ∣[k] beta M H ℓ c) =
      ModularForm.heckeU k ℓ f +
        (f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ ((rhoInf M ℓ B : Gamma0 M) : SL(2, ℤ)) :
          GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix ℓ)) := by
  calc ∑ c : ↥(GammaH M H) ⧸ GammaHUpper M H ℓ, f ∣[k] beta M H ℓ c
      = ∑ o : OnePoint (ZMod ℓ), f ∣[k] beta M H ℓ (onePointEquiv M H ℓ B o) :=
        (Equiv.sum_comp (onePointEquiv M H ℓ B) (fun c => f ∣[k] beta M H ℓ c)).symm
    _ = f ∣[k] beta M H ℓ (onePointEquiv M H ℓ B ∞) +
        ∑ x : ZMod ℓ, f ∣[k] beta M H ℓ (onePointEquiv M H ℓ B ↑x) := by
        rw [show (∑ o : OnePoint (ZMod ℓ), f ∣[k] beta M H ℓ (onePointEquiv M H ℓ B o)) =
            ∑ o : Option (ZMod ℓ), f ∣[k] beta M H ℓ (onePointEquiv M H ℓ B o) from rfl,
          Fintype.sum_option]
        rfl
    _ = f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ ((rhoInf M ℓ B : Gamma0 M) : SL(2, ℤ)) :
            GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix ℓ) +
        ∑ x : ZMod ℓ, f ∣[k] ModularForm.heckeMatrix ℓ x.val := by
        rw [beta_onePointEquiv_infty M H ℓ B k hf,
          Finset.sum_congr rfl fun x _ => beta_onePointEquiv_coe M H ℓ B k hf x]
    _ = f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ ((rhoInf M ℓ B : Gamma0 M) : SL(2, ℤ)) :
            GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix ℓ) + ModularForm.heckeU k ℓ f := by
        rw [ModularForm.HeckeRepresentatives.heckeU_eq_sum_zmod k f]
    _ = ModularForm.heckeU k ℓ f +
        (f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ ((rhoInf M ℓ B : Gamma0 M) : SL(2, ℤ)) :
          GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix ℓ)) := add_comm _ _

/-- **The pin's `ρ` names the `∞` coset.** `ρ 1 1 ≡ ℓ (mod M)` makes `ρ · diag ℓ` agree with
`ρ_∞ · diag ℓ` on a `Γ_H(M)`-invariant `f`: the two differ by `ρ · ρ_∞⁻¹ ∈ Γ_H(M)`. -/
theorem slash_rhoInf_diag (B : BezoutPair (ℓ : ℤ) (M : ℤ)) {ρ : Gamma0 M}
    (hρ : (((ρ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = ℓ) (k : ℤ) {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (GammaH M H).map (Matrix.SpecialLinearGroup.mapGL ℝ), f ∣[k] γ = f) :
    f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ) *
        ModularForm.heckeDiagMatrix ℓ) =
      f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ ((rhoInf M ℓ B : Gamma0 M) : SL(2, ℤ)) :
        GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix ℓ) := by
  have hmem := mul_rhoInf_inv_mem_GammaH M H ℓ B hρ
  have hfac : (Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ) =
      (Matrix.SpecialLinearGroup.mapGL ℝ
          ((ρ : SL(2, ℤ)) * (((rhoInf M ℓ B : Gamma0 M) : SL(2, ℤ)))⁻¹) : GL (Fin 2) ℝ) *
        (Matrix.SpecialLinearGroup.mapGL ℝ ((rhoInf M ℓ B : Gamma0 M) : SL(2, ℤ)) :
          GL (Fin 2) ℝ) := by
    rw [← map_mul, inv_mul_cancel_right]
  conv_lhs => rw [hfac]
  rw [SlashAction.slash_mul, SlashAction.slash_mul, SlashAction.slash_mul,
    hf _ (Subgroup.mem_map_of_mem _ hmem)]

end Projective

end HeckeCosetGammaH

end
