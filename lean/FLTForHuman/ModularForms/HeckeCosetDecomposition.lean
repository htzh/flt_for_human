/-
  The coset decomposition of `Γ_HUpper(M,ℓ)` over `Γ_H(M)`: the index, an explicit
  set of representatives, and the two coset sums that read the Hecke operators off it.

  The mathematics. `Γ_HUpper(M,ℓ)` is the intersection of `Γ_H(M)` with the
  `ℓ`-Hecke subgroup, so `Γ_H(M)` has finite index in it and the double coset
  `Γ_H(M) · diag(ℓ) · Γ_H(M)` is a finite disjoint union of `Γ_H(M)`-cosets. This
  module computes that decomposition in the two cases the operator calculus needs:

  * `q ∣ M`: the cosets of `Γ_HUpper(M,q)` are indexed by `Fin q` (`transl`,
    `bijective_transl`), and the resulting sum of slashes over them is `U_q`
    (`sum_slash_beta_eq_heckeU`);
  * `ℓ ∤ M`: the Bezout model `BezoutData`/`gammaInf`/`rhoInf` indexes the cosets by
    `Option (Fin ℓ)` (`bijective_option`), and the sum is
    `U_ℓ + (·) ∣ (ρ · diag ℓ)` (`sum_slash_beta_eq_heckeU_add`);

  with `sum_slash_beta_slash_eq` giving that each such coset sum is `Γ_H`-invariant.

  Why it is its own module. The pin copies this block verbatim into four of its `S_`
  files (nodes 8, 9, 1 and 2 of the wave): 19 names, ≈1,031 duplicated lines
  (`topics/aj/PLAN-W3b-hecke-equivariance.md` §5). It is written once here, at the
  pin's names in the namespace `HeckeCoset`: nodes 8 and 9
  (`ModularForms/HeckeInvariance.lean`) use the `sum_slash_beta_*` half, nodes 1 and
  2 (`ModularCurve/Period/PeriodMapHecke.lean`) the `GammaHUpper` half.

  It is unwired on purpose: the block has no pin statement, so there is no
  `spec-pin:` to carry, and the pin-line provenance below is its record. Seven
  helpers carry `omit [NeZero M] in` because the pin's `variable` block passes an
  unused instance; the statements are otherwise the pin's.

  Provenance: `P2M/Sol/S_ModularForm_heckeU_slash_eq_self_of_mem_GammaH.lean`
  lines 14–468, pinned `aa2d8b3`, which is byte-identical to the same range of
  `S_ModularForm_heckeU_add_slash_slash_eq_self_of_mem_GammaH.lean` (the two files
  differ only in their last nineteen lines, the two headlines).

  Contents:

  * `beta` — the coset representative `heckeMatrix q 0 * (mapGL ℝ c.out⁻¹)`, and
    `sum_slash_beta_slash_eq`: the coset sum is `Γ_H`-invariant;
  * `transl`, `bijective_transl`, `sum_slash_beta_eq_heckeU`: for `q ∣ M`, the
    cosets of `Γ_HUpper(M,q)` are indexed by `Fin q` and the sum is `heckeU`;
  * the Bezout model `BezoutData`/`gammaInf`/`rhoInf` for `ℓ ∤ M`,
    `bijective_option` (the cosets are `Option (Fin ℓ)`) and
    `sum_slash_beta_eq_heckeU_add`, the `U_ℓ + (·) ∣ (ρ · diag ℓ)` sum.

  It lives here, under `ModularForms/`, and not under `ModularCurve/Period/` beside
  nodes 1-3: `ModularForms/` is the lower of its two consumers (`ModularCurve/Period/
  PeriodLatticeSpan.lean` imports `ModularForms/EichlerShimura/ExistsEquivariantPrimitive`,
  so `ModularCurve/Period/` is above `ModularForms/`), and this block imports only
  `ModularForms/Defs/*`. Keeping it above `HeckeInvariance.lean` would have been the
  subject's one upward import.

  Statements are the pin's; the proofs are the pin's, adapted only where mathlib
  `v4.34.0` spells an API differently. The pin's `letI :=
  (GammaHUpper …).fintypeQuotientOfFiniteIndex` walls are kept literal: `letI`
  inlines its value, which is what makes the coset sum definitionally the Hecke
  operator in the two `sum_slash_beta_*` lemmas.
-/
import Mathlib.GroupTheory.Transfer
import Mathlib.FieldTheory.Finite.Basic
import FLTForHuman.ModularForms.Defs.CohCarrierLevel
import FLTForHuman.ModularForms.Defs.HeckeOperator

set_option autoImplicit false

-- The pin's `letI` walls are load-bearing (see the header); kept literal.
set_option linter.style.haveILetI false
-- No `maxHeartbeats` raise: the pin's 6,400,000 is not needed on mathlib `v4.34.0`,
-- and this module compiles in ≈6 s at the default limit (measured, 2026-10-26).

noncomputable section

open scoped MatrixGroups ModularForm
open UpperHalfPlane CongruenceSubgroup CohCarrier

namespace HeckeCoset

section

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (q : ℕ) [NeZero q]

noncomputable def beta (c : ↥(GammaH M H) ⧸ GammaHUpper M H q) : GL (Fin 2) ℝ :=
  ModularForm.heckeMatrix q 0 *
    (Matrix.SpecialLinearGroup.mapGL ℝ (((c.out : ↥(GammaH M H)) : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ)

omit [NeZero M] in
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

omit [NeZero M] in
theorem sum_slash_beta_slash_eq (k : ℤ) {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (GammaH M H).map (Matrix.SpecialLinearGroup.mapGL ℝ), f ∣[k] γ = f)
    (γ : GL (Fin 2) ℝ) (hγ : γ ∈ (GammaH M H).map (Matrix.SpecialLinearGroup.mapGL ℝ)) :
    letI := (GammaHUpper M H q).fintypeQuotientOfFiniteIndex
    (∑ c : ↥(GammaH M H) ⧸ GammaHUpper M H q, f ∣[k] beta M H q c) ∣[k] γ =
      ∑ c : ↥(GammaH M H) ⧸ GammaHUpper M H q, f ∣[k] beta M H q c := by
  letI := (GammaHUpper M H q).fintypeQuotientOfFiniteIndex
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ
  set g' : ↥(GammaH M H) := ⟨g, hg⟩ with hg'

  have hterm : ∀ c : ↥(GammaH M H) ⧸ GammaHUpper M H q,
      (f ∣[k] beta M H q c) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) =
        f ∣[k] beta M H q (g'⁻¹ • c) := by
    intro c
    set d := g'⁻¹ • c with hd
    have hmk : (QuotientGroup.mk (g'⁻¹ * c.out) : ↥(GammaH M H) ⧸ GammaHUpper M H q) = d := by
      rw [hd]
      conv_rhs => rw [← QuotientGroup.out_eq' c]
      rw [MulAction.Quotient.smul_mk]
      rfl
    obtain ⟨t, ht⟩ := QuotientGroup.mk_out_eq_mul (GammaHUpper M H q) (g'⁻¹ * c.out)
    rw [hmk] at ht

    have hrel : (((c.out : ↥(GammaH M H)) : SL(2, ℤ)))⁻¹ * g =
        (((t : ↥(GammaHUpper M H q)) : ↥(GammaH M H)) : SL(2, ℤ)) * (((d.out : ↥(GammaH M H)) : SL(2, ℤ)))⁻¹ := by
      have h1 : ((d.out : ↥(GammaH M H)) : SL(2, ℤ)) =
          (g⁻¹ * ((c.out : ↥(GammaH M H)) : SL(2, ℤ))) * (((t : ↥(GammaHUpper M H q)) : ↥(GammaH M H)) : SL(2, ℤ)) := by
        have := congrArg (fun x : ↥(GammaH M H) => (x : SL(2, ℤ))) ht
        simpa using this
      rw [h1]; group
    rw [← SlashAction.slash_mul]
    have hb : beta M H q c * (Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) =
        (Matrix.SpecialLinearGroup.mapGL ℝ ((conjL M H q t : ↥(GammaH M H)) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
          beta M H q d := by
      simp only [beta]
      rw [mul_assoc, ← map_mul, hrel, map_mul, ← mul_assoc, ← mapGL_conjL_mul_heckeMatrix, mul_assoc]
    rw [hb, SlashAction.slash_mul, hf _ (Subgroup.mem_map_of_mem _ (conjL M H q t).2)]
  classical
  have hsum : ∀ (s : Finset (↥(GammaH M H) ⧸ GammaHUpper M H q)) (F : (↥(GammaH M H) ⧸ GammaHUpper M H q) → ℍ → ℂ)
      (A : GL (Fin 2) ℝ), (∑ c ∈ s, F c) ∣[k] A = ∑ c ∈ s, (F c) ∣[k] A := by
    intro s F A
    induction s using Finset.induction_on with
    | empty => simp [SlashAction.zero_slash]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, SlashAction.add_slash, ih]
  rw [hsum]
  simp_rw [hterm]
  exact Fintype.sum_bijective (g'⁻¹ • ·) (MulAction.bijective g'⁻¹) _ _ (fun c => rfl)

end

section Affine

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (q : ℕ) [NeZero q]

def transl (n : ℤ) : ↥(GammaH M H) :=
  ⟨ModularGroup.T ^ n, by
    rw [mem_GammaH_iff]
    have h0 : ModularGroup.T ^ n ∈ Gamma0 M := by
      rw [Gamma0_mem, ModularGroup.coe_T_zpow]; simp
    refine ⟨h0, ?_⟩
    have : gamma0Units M ⟨ModularGroup.T ^ n, h0⟩ = 1 := by
      ext; rw [val_gamma0Units]
      show (((ModularGroup.T ^ n) 1 1 : ℤ) : ZMod M) = ((1 : (ZMod M)ˣ) : ZMod M)
      rw [ModularGroup.coe_T_zpow]; simp
    rw [this]; exact one_mem H⟩

omit [NeZero M] in
@[scoped simp] theorem coe_transl (n : ℤ) : ((transl M H n : ↥(GammaH M H)) : SL(2, ℤ)) = ModularGroup.T ^ n := rfl

theorem exists_add_neg_eq_mul (j : Fin q) : ∃ e : ℕ, (j : ℕ) + ((-j : Fin q) : ℕ) = e * q := by
  have h : ((j : ℕ) + ((-j : Fin q) : ℕ)) % q = 0 := by
    have := Fin.val_add j (-j)
    rw [add_neg_cancel, Fin.val_zero] at this
    exact this.symm
  exact ⟨((j : ℕ) + ((-j : Fin q) : ℕ)) / q, (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h)).symm⟩

theorem heckeMatrix_zero_mul_mapGL_T_zpow_neg (j : Fin q) (e : ℕ) (he : (j : ℕ) + ((-j : Fin q) : ℕ) = e * q) :
    ModularForm.heckeMatrix q 0 * (Matrix.SpecialLinearGroup.mapGL ℝ ((ModularGroup.T ^ ((j : ℕ) : ℤ))⁻¹) : GL (Fin 2) ℝ) =
      (Matrix.SpecialLinearGroup.mapGL ℝ ((ModularGroup.T ^ (e : ℤ))⁻¹) : GL (Fin 2) ℝ) *
        ModularForm.heckeMatrix q ((-j : Fin q) : ℕ) := by
  have hq : q ≠ 0 := NeZero.ne q
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ModularForm.val_heckeMatrix hq, ModularForm.val_heckeMatrix hq]
  have e1 : ∀ n : ℤ, ((Matrix.SpecialLinearGroup.mapGL ℝ ((ModularGroup.T ^ n)⁻¹) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = !![(1 : ℝ), (-n : ℝ); 0, 1] := by
    intro n
    rw [← zpow_neg, show ((Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ (-n))) : GL (Fin 2) ℝ) =
      ((ModularGroup.T ^ (-n) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) from rfl,
      ModularGroup.coe_T_zpow]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [e1, e1]
  have he' : ((j : ℕ) : ℝ) + (((-j : Fin q) : ℕ) : ℝ) = (e : ℝ) * (q : ℝ) := by exact_mod_cast he
  ext i k
  fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two]; linarith [he']

omit [NeZero M] in
theorem bijective_transl (hqM : q ∣ M) :
    Function.Bijective (fun j : Fin q => (QuotientGroup.mk (transl M H ((j : ℕ) : ℤ)) :
      ↥(GammaH M H) ⧸ GammaHUpper M H q)) := by
  have hq : q ≠ 0 := NeZero.ne q
  constructor
  · intro i j hij
    rw [QuotientGroup.eq] at hij
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, coe_transl, coe_transl, ← zpow_neg, ← zpow_add,
      mem_Gamma0Upper, ModularGroup.coe_T_zpow] at hij
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.cons_val_zero] at hij

    apply Fin.ext
    have h1 : ((j : ℕ) : ZMod q) = ((i : ℕ) : ZMod q) := by
      have : ((-(i : ℕ) + (j : ℕ) : ℤ) : ZMod q) = 0 := by exact_mod_cast hij
      push_cast at this
      linear_combination this
    have := (ZMod.natCast_eq_natCast_iff' (j : ℕ) (i : ℕ) q).mp h1
    rw [Nat.mod_eq_of_lt j.2, Nat.mod_eq_of_lt i.2] at this
    exact this.symm
  · intro c
    induction c using QuotientGroup.induction_on with
    | H γ =>
    obtain ⟨h0, -⟩ := mem_GammaH_iff.mp γ.2

    have hc : ((((γ : SL(2, ℤ)) 1 0 : ℤ)) : ZMod q) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact (Int.natCast_dvd_natCast.mpr hqM).trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp h0))
    have hdet := Matrix.SpecialLinearGroup.det_coe (γ : SL(2, ℤ))
    rw [Matrix.det_fin_two] at hdet
    have had : ((((γ : SL(2, ℤ)) 0 0 : ℤ)) : ZMod q) * ((((γ : SL(2, ℤ)) 1 1 : ℤ)) : ZMod q) = 1 := by
      have := congrArg (fun z : ℤ => (z : ZMod q)) hdet
      simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hc, mul_zero, sub_zero] at this
      exact this

    set jz : ZMod q := ((((γ : SL(2, ℤ)) 0 1 : ℤ)) : ZMod q) * ((((γ : SL(2, ℤ)) 0 0 : ℤ)) : ZMod q) with hjz
    refine ⟨⟨jz.val, ZMod.val_lt jz⟩, ?_⟩
    symm
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, coe_transl, mem_Gamma0Upper]

    have hentry : ((γ : SL(2, ℤ))⁻¹ * ModularGroup.T ^ (((jz.val : ℕ) : ℤ)) : SL(2, ℤ)) 0 1 =
        ((γ : SL(2, ℤ)) 1 1 : ℤ) * ((jz.val : ℕ) : ℤ) - ((γ : SL(2, ℤ)) 0 1 : ℤ) := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, ModularGroup.coe_T_zpow,
        Matrix.adjugate_fin_two]
      simp [Matrix.mul_apply, Fin.sum_univ_two]
      ring
    rw [hentry]
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id', id, hjz]
    linear_combination ((((γ : SL(2, ℤ)) 0 1 : ℤ)) : ZMod q) * had

omit [NeZero M] in
theorem sum_slash_beta_eq_heckeU (hqM : q ∣ M) (k : ℤ) {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (GammaH M H).map (Matrix.SpecialLinearGroup.mapGL ℝ), f ∣[k] γ = f) :
    letI := (GammaHUpper M H q).fintypeQuotientOfFiniteIndex
    (∑ c : ↥(GammaH M H) ⧸ GammaHUpper M H q, f ∣[k] beta M H q c) = ModularForm.heckeU k q f := by
  letI := (GammaHUpper M H q).fintypeQuotientOfFiniteIndex

  rw [← Fintype.sum_bijective _ (bijective_transl M H q hqM) (fun j => f ∣[k] beta M H q
      (QuotientGroup.mk (transl M H ((j : ℕ) : ℤ)))) _ (fun _ => rfl)]

  have hterm : ∀ j : Fin q, f ∣[k] beta M H q (QuotientGroup.mk (transl M H ((j : ℕ) : ℤ))) =
      f ∣[k] ModularForm.heckeMatrix q ((-j : Fin q) : ℕ) := by
    intro j
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (GammaHUpper M H q) (transl M H ((j : ℕ) : ℤ))
    obtain ⟨e, he⟩ := exists_add_neg_eq_mul q j
    have hb : beta M H q (QuotientGroup.mk (transl M H ((j : ℕ) : ℤ))) =
        (Matrix.SpecialLinearGroup.mapGL ℝ ((conjL M H q k⁻¹ : ↥(GammaH M H)) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
          (Matrix.SpecialLinearGroup.mapGL ℝ ((ModularGroup.T ^ (e : ℤ))⁻¹) : GL (Fin 2) ℝ) *
          ModularForm.heckeMatrix q ((-j : Fin q) : ℕ) := by
      simp only [beta]
      rw [hk, Subgroup.coe_mul, mul_inv_rev, map_mul, ← mul_assoc,
        show (((k : ↥(GammaHUpper M H q)) : ↥(GammaH M H)) : SL(2, ℤ))⁻¹ =
          (((k⁻¹ : ↥(GammaHUpper M H q)) : ↥(GammaH M H)) : SL(2, ℤ)) from rfl,
        ← mapGL_conjL_mul_heckeMatrix, mul_assoc, coe_transl,
        heckeMatrix_zero_mul_mapGL_T_zpow_neg q j e he, ← mul_assoc]
    have hmem1 : (Matrix.SpecialLinearGroup.mapGL ℝ ((conjL M H q k⁻¹ : ↥(GammaH M H)) : SL(2, ℤ)) :
        GL (Fin 2) ℝ) ∈ (GammaH M H).map (Matrix.SpecialLinearGroup.mapGL ℝ) :=
      Subgroup.mem_map_of_mem _ (conjL M H q k⁻¹).2
    have hmem2 : (Matrix.SpecialLinearGroup.mapGL ℝ ((ModularGroup.T ^ (e : ℤ))⁻¹) : GL (Fin 2) ℝ) ∈
        (GammaH M H).map (Matrix.SpecialLinearGroup.mapGL ℝ) := by
      refine Subgroup.mem_map_of_mem _ ?_
      rw [← zpow_neg]
      exact (transl M H (-(e : ℤ))).2
    rw [hb, SlashAction.slash_mul, SlashAction.slash_mul, hf _ hmem1,
      hf _ hmem2]
  simp_rw [hterm]
  rw [ModularForm.heckeU_def, ← Fin.sum_univ_eq_sum_range (fun i => f ∣[k] ModularForm.heckeMatrix q i) q]
  exact Fintype.sum_equiv (Equiv.neg (Fin q)) _ _ (fun j => rfl)

end Affine

section Projective

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [Fact ℓ.Prime]

scoped instance : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩

structure BezoutData where
  (u v : ℤ)
  (huv : u * ℓ + v * M = 1)

omit [NeZero M] in
theorem exists_bezoutData (hℓM : ¬ ℓ ∣ M) : Nonempty (BezoutData M ℓ) := by
  have hcop : IsCoprime (ℓ : ℤ) (M : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hℓM)
  obtain ⟨u, v, h⟩ := hcop
  exact ⟨⟨u, v, by linear_combination h⟩⟩

variable {M ℓ}

def gammaInf (B : BezoutData M ℓ) : ↥(GammaH M H) :=
  ⟨(⟨!![1, -B.v; (M : ℤ), B.u * ℓ], by rw [Matrix.det_fin_two_of]; linear_combination B.huv⟩ :
      SL(2, ℤ)), by
    -- `rw [mem_GammaH_iff]` does not fire here: `Matrix.SpecialLinearGroup` is a
    -- `def`, so the membership's element is only semireducibly the subtype, which
    -- `rw`'s implicit-transparency matching rejects (mathlib `v4.34.0`).
    refine mem_GammaH_iff.mpr ⟨?_, ?_⟩
    · exact Gamma0_mem.mpr (by show (((M : ℤ)) : ZMod M) = 0; simp)
    · have h0 : (⟨!![1, -B.v; (M : ℤ), B.u * ℓ],
          by rw [Matrix.det_fin_two_of]; linear_combination B.huv⟩ :
          SL(2, ℤ)) ∈ Gamma0 M :=
        Gamma0_mem.mpr (by show (((M : ℤ)) : ZMod M) = 0; simp)
      have h : gamma0Units M ⟨_, h0⟩ = 1 := by
        ext; rw [val_gamma0Units]
        show (((B.u * ℓ : ℤ)) : ZMod M) = ((1 : (ZMod M)ˣ) : ZMod M)
        have : (B.u * ℓ : ℤ) = 1 - B.v * M := by linear_combination B.huv
        rw [this]; push_cast; simp
      rw [h]; exact one_mem H⟩

def rhoInf (B : BezoutData M ℓ) : Gamma0 M :=
  ⟨⟨!![B.u, B.v; -(M : ℤ), (ℓ : ℤ)], by rw [Matrix.det_fin_two_of]; linear_combination B.huv⟩,
    Gamma0_mem.mpr (by show ((-(M : ℤ) : ℤ) : ZMod M) = 0; simp)⟩

omit [NeZero M] [Fact ℓ.Prime] in
theorem rhoInf_apply_11 (B : BezoutData M ℓ) : (((rhoInf B : Gamma0 M) : SL(2, ℤ)) 1 1 : ℤ) = ℓ := rfl

omit [NeZero M] in
theorem heckeMatrix_zero_mul_mapGL_gammaInf_inv (B : BezoutData M ℓ) :
    ModularForm.heckeMatrix ℓ 0 *
        (Matrix.SpecialLinearGroup.mapGL ℝ (((gammaInf H B : ↥(GammaH M H)) : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) =
      (Matrix.SpecialLinearGroup.mapGL ℝ ((rhoInf B : Gamma0 M) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
        ModularForm.heckeDiagMatrix ℓ := by
  have hℓ : ℓ ≠ 0 := NeZero.ne ℓ
  have e3 : ((Matrix.SpecialLinearGroup.mapGL ℝ (((gammaInf H B : ↥(GammaH M H)) : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
      ((((gammaInf H B : ↥(GammaH M H)) : SL(2, ℤ))⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := rfl
  have e4 : ((Matrix.SpecialLinearGroup.mapGL ℝ ((rhoInf B : Gamma0 M) : SL(2, ℤ)) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
      ((((rhoInf B : Gamma0 M) : SL(2, ℤ))) : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := rfl
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ModularForm.val_heckeMatrix hℓ, ModularForm.val_heckeDiagMatrix hℓ, e3, e4,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gammaInf, rhoInf, Matrix.mul_apply, Fin.sum_univ_two]
  · ring

omit [NeZero M] in
theorem bijective_option (B : BezoutData M ℓ) :
    Function.Bijective (fun o : Option (Fin ℓ) => (o.elim (QuotientGroup.mk (gammaInf H B))
      (fun j => QuotientGroup.mk (transl M H ((j : ℕ) : ℤ))) : ↥(GammaH M H) ⧸ GammaHUpper M H ℓ)) := by
  have hℓ : ℓ ≠ 0 := NeZero.ne ℓ
  haveI : Fact (1 < ℓ) := ⟨(Fact.out : ℓ.Prime).one_lt⟩
  have hvM : ((B.v : ℤ) : ZMod ℓ) * (M : ZMod ℓ) = 1 := by
    have := congrArg (fun z : ℤ => (z : ZMod ℓ)) B.huv
    push_cast at this
    rw [ZMod.natCast_self, mul_zero, zero_add] at this
    exact this
  have hv : ((B.v : ℤ) : ZMod ℓ) ≠ 0 := fun h => by rw [h, zero_mul] at hvM; exact zero_ne_one hvM

  have hinf_entry : ∀ X : SL(2, ℤ), (((gammaInf H B : ↥(GammaH M H)) : SL(2, ℤ))⁻¹ * X : SL(2, ℤ)) 0 1 =
      B.u * ℓ * (X 0 1 : ℤ) + B.v * (X 1 1 : ℤ) := by
    intro X
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp [gammaInf, Matrix.mul_apply, Fin.sum_univ_two]
  have hT_entry : ∀ (n : ℤ) (X : SL(2, ℤ)), ((X⁻¹ * ModularGroup.T ^ n : SL(2, ℤ)) 0 1 : ℤ) =
      (X 1 1 : ℤ) * n - (X 0 1 : ℤ) := by
    intro n X
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, ModularGroup.coe_T_zpow,
      Matrix.adjugate_fin_two]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  constructor
  · rintro (_ | i) (_ | j) hij
    · rfl
    ·
      exfalso
      simp only [Option.elim] at hij
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, coe_transl,
        mem_Gamma0Upper, hinf_entry, ModularGroup.coe_T_zpow] at hij
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] at hij
      push_cast at hij
      rw [ZMod.natCast_self, mul_zero, zero_mul, zero_add, mul_one] at hij
      exact hv hij
    · exfalso
      simp only [Option.elim] at hij
      rw [eq_comm, QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, coe_transl,
        mem_Gamma0Upper, hinf_entry, ModularGroup.coe_T_zpow] at hij
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] at hij
      push_cast at hij
      rw [ZMod.natCast_self, mul_zero, zero_mul, zero_add, mul_one] at hij
      exact hv hij
    · simp only [Option.elim] at hij
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, coe_transl, coe_transl,
        ← zpow_neg, ← zpow_add, mem_Gamma0Upper, ModularGroup.coe_T_zpow] at hij
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Matrix.cons_val_zero] at hij
      congr 1
      apply Fin.ext
      have h1 : ((j : ℕ) : ZMod ℓ) = ((i : ℕ) : ZMod ℓ) := by
        have : ((-(i : ℕ) + (j : ℕ) : ℤ) : ZMod ℓ) = 0 := by exact_mod_cast hij
        push_cast at this
        linear_combination this
      have := (ZMod.natCast_eq_natCast_iff' (j : ℕ) (i : ℕ) ℓ).mp h1
      rw [Nat.mod_eq_of_lt j.2, Nat.mod_eq_of_lt i.2] at this
      exact this.symm
  · intro c
    induction c using QuotientGroup.induction_on with
    | H γ =>
    by_cases hd : ((((γ : SL(2, ℤ)) 1 1 : ℤ)) : ZMod ℓ) = 0
    · refine ⟨none, ?_⟩
      simp only [Option.elim]
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, mem_Gamma0Upper,
        hinf_entry]
      push_cast
      rw [ZMod.natCast_self, mul_zero, zero_mul, zero_add, hd, mul_zero]
    · set jz : ZMod ℓ := ((((γ : SL(2, ℤ)) 0 1 : ℤ)) : ZMod ℓ) * (((((γ : SL(2, ℤ)) 1 1 : ℤ)) : ZMod ℓ))⁻¹ with hjz
      refine ⟨some ⟨jz.val, ZMod.val_lt jz⟩, ?_⟩
      simp only [Option.elim]
      symm
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, coe_transl,
        mem_Gamma0Upper, hT_entry]
      push_cast
      rw [ZMod.natCast_val, ZMod.cast_id', id, hjz, mul_comm, mul_assoc, inv_mul_cancel₀ hd, mul_one, sub_self]

omit [NeZero M] in
theorem sum_slash_beta_eq_heckeU_add (B : BezoutData M ℓ) (ρ : Gamma0 M) (hρ : (((ρ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = ℓ)
    (k : ℤ) {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (GammaH M H).map (Matrix.SpecialLinearGroup.mapGL ℝ), f ∣[k] γ = f) :
    letI := (GammaHUpper M H ℓ).fintypeQuotientOfFiniteIndex
    (∑ c : ↥(GammaH M H) ⧸ GammaHUpper M H ℓ, f ∣[k] beta M H ℓ c) =
      ModularForm.heckeU k ℓ f +
        (f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ) *
          ModularForm.heckeDiagMatrix ℓ)) := by
  letI := (GammaHUpper M H ℓ).fintypeQuotientOfFiniteIndex
  rw [← Fintype.sum_bijective _ (bijective_option H B) (fun o => f ∣[k] beta M H ℓ
      (o.elim (QuotientGroup.mk (gammaInf H B)) (fun j => QuotientGroup.mk (transl M H ((j : ℕ) : ℤ))))) _
      (fun _ => rfl), Fintype.sum_option]
  simp only [Option.elim]

  have hterm : ∀ j : Fin ℓ, f ∣[k] beta M H ℓ (QuotientGroup.mk (transl M H ((j : ℕ) : ℤ))) =
      f ∣[k] ModularForm.heckeMatrix ℓ ((-j : Fin ℓ) : ℕ) := by
    intro j
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (GammaHUpper M H ℓ) (transl M H ((j : ℕ) : ℤ))
    obtain ⟨e, he⟩ := exists_add_neg_eq_mul ℓ j
    have hb : beta M H ℓ (QuotientGroup.mk (transl M H ((j : ℕ) : ℤ))) =
        (Matrix.SpecialLinearGroup.mapGL ℝ ((conjL M H ℓ k⁻¹ : ↥(GammaH M H)) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
          (Matrix.SpecialLinearGroup.mapGL ℝ ((ModularGroup.T ^ (e : ℤ))⁻¹) : GL (Fin 2) ℝ) *
          ModularForm.heckeMatrix ℓ ((-j : Fin ℓ) : ℕ) := by
      simp only [beta]
      rw [hk, Subgroup.coe_mul, mul_inv_rev, map_mul, ← mul_assoc,
        show (((k : ↥(GammaHUpper M H ℓ)) : ↥(GammaH M H)) : SL(2, ℤ))⁻¹ =
          (((k⁻¹ : ↥(GammaHUpper M H ℓ)) : ↥(GammaH M H)) : SL(2, ℤ)) from rfl,
        ← mapGL_conjL_mul_heckeMatrix, mul_assoc, coe_transl,
        heckeMatrix_zero_mul_mapGL_T_zpow_neg ℓ j e he, ← mul_assoc]
    have hmem1 : (Matrix.SpecialLinearGroup.mapGL ℝ ((conjL M H ℓ k⁻¹ : ↥(GammaH M H)) : SL(2, ℤ)) :
        GL (Fin 2) ℝ) ∈ (GammaH M H).map (Matrix.SpecialLinearGroup.mapGL ℝ) :=
      Subgroup.mem_map_of_mem _ (conjL M H ℓ k⁻¹).2
    have hmem2 : (Matrix.SpecialLinearGroup.mapGL ℝ ((ModularGroup.T ^ (e : ℤ))⁻¹) : GL (Fin 2) ℝ) ∈
        (GammaH M H).map (Matrix.SpecialLinearGroup.mapGL ℝ) := by
      refine Subgroup.mem_map_of_mem _ ?_
      rw [← zpow_neg]
      exact (transl M H (-(e : ℤ))).2
    rw [hb, SlashAction.slash_mul, SlashAction.slash_mul, hf _ hmem1,
      hf _ hmem2]
  simp_rw [hterm]

  have hinf : f ∣[k] beta M H ℓ (QuotientGroup.mk (gammaInf H B)) =
      f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ) *
        ModularForm.heckeDiagMatrix ℓ) := by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (GammaHUpper M H ℓ) (gammaInf H B)
    have hb : beta M H ℓ (QuotientGroup.mk (gammaInf H B)) =
        (Matrix.SpecialLinearGroup.mapGL ℝ ((conjL M H ℓ k⁻¹ : ↥(GammaH M H)) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
          ((Matrix.SpecialLinearGroup.mapGL ℝ ((rhoInf B : Gamma0 M) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
            ModularForm.heckeDiagMatrix ℓ) := by
      simp only [beta]
      rw [hk, Subgroup.coe_mul, mul_inv_rev, map_mul, ← mul_assoc,
        show (((k : ↥(GammaHUpper M H ℓ)) : ↥(GammaH M H)) : SL(2, ℤ))⁻¹ =
          (((k⁻¹ : ↥(GammaHUpper M H ℓ)) : ↥(GammaH M H)) : SL(2, ℤ)) from rfl,
        ← mapGL_conjL_mul_heckeMatrix, mul_assoc, heckeMatrix_zero_mul_mapGL_gammaInf_inv]
    have hmem1 : (Matrix.SpecialLinearGroup.mapGL ℝ ((conjL M H ℓ k⁻¹ : ↥(GammaH M H)) : SL(2, ℤ)) :
        GL (Fin 2) ℝ) ∈ (GammaH M H).map (Matrix.SpecialLinearGroup.mapGL ℝ) :=
      Subgroup.mem_map_of_mem _ (conjL M H ℓ k⁻¹).2

    have hmem3 : (ρ : SL(2, ℤ)) * ((rhoInf B : Gamma0 M) : SL(2, ℤ))⁻¹ ∈ GammaH M H := by
      rw [mem_GammaH_iff]
      refine ⟨(ρ * (rhoInf B)⁻¹).2, ?_⟩
      have e1 : (⟨(ρ : SL(2, ℤ)) * ((rhoInf B : Gamma0 M) : SL(2, ℤ))⁻¹, (ρ * (rhoInf B)⁻¹).2⟩ : Gamma0 M) =
          ρ * (rhoInf B)⁻¹ := rfl
      rw [e1, map_mul, map_inv]
      have hu : gamma0Units M ρ = gamma0Units M (rhoInf B) := by
        ext; rw [val_gamma0Units, val_gamma0Units]
        show ((((ρ : SL(2, ℤ)) 1 1 : ℤ)) : ZMod M) = (((((rhoInf B : Gamma0 M) : SL(2, ℤ)) 1 1 : ℤ)) : ZMod M)
        rw [hρ, rhoInf_apply_11, Int.cast_natCast]
      rw [hu, mul_inv_cancel]
      exact one_mem H
    have hmem3' : (Matrix.SpecialLinearGroup.mapGL ℝ ((ρ : SL(2, ℤ)) * ((rhoInf B : Gamma0 M) : SL(2, ℤ))⁻¹) :
        GL (Fin 2) ℝ) ∈ (GammaH M H).map (Matrix.SpecialLinearGroup.mapGL ℝ) :=
      Subgroup.mem_map_of_mem _ hmem3
    rw [hb, SlashAction.slash_mul, hf _ hmem1]
    conv_rhs => rw [show ((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ)) =
      (Matrix.SpecialLinearGroup.mapGL ℝ ((ρ : SL(2, ℤ)) * ((rhoInf B : Gamma0 M) : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) *
        (Matrix.SpecialLinearGroup.mapGL ℝ ((rhoInf B : Gamma0 M) : SL(2, ℤ)) : GL (Fin 2) ℝ) from by
          rw [← map_mul, inv_mul_cancel_right], mul_assoc, SlashAction.slash_mul,
      hf _ hmem3']
  rw [hinf, add_comm, ModularForm.heckeU_def,
    ← Fin.sum_univ_eq_sum_range (fun i => f ∣[k] ModularForm.heckeMatrix ℓ i) ℓ]
  congr 1
  exact Fintype.sum_equiv (Equiv.neg (Fin ℓ)) _ _ (fun j => rfl)

end Projective

end HeckeCoset

end
