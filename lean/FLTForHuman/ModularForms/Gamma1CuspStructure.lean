/-  The structure of the `Γ₁` cusp form space: the `U_ℓ` operators commute, a primitive form's
  coefficients vanish off the indices a divisor misses, and the space has an integral basis and finite
  dimension.

  These are the finiteness facts the level-lowering argument reads a `Γ₁(N)` cusp form against: the
  commuting `U_ℓ` (so that a simultaneous eigenform exists), the vanishing criterion that makes a
  primitive form's coefficients a complete set of data, and the finite dimension with a basis whose two
  `q`-coefficients are integral.

  Transcribed from the pin's proof files (pinned `aa2d8b3`)
  `P2M/Sol/S_CuspForm_heckeULinH_comm.lean` (74 lines),
  `…_IsPrimitiveForm_qCoeff_eq_zero_of_dvd_div.lean` (69),
  `…_exists_basis_gamma1_two_qCoeff_mem_range_intCast.lean` (19) and
  `…_finiteDimensional_Gamma1.lean` (16), with the statements from their wrappers.

  spec-pin: Theorems/Thm_CuspForm_heckeULinH_comm.lean
  spec-pin: P2M/Sol/S_CuspForm_heckeULinH_comm.lean
  spec-pin: Theorems/Thm_CuspForm_IsPrimitiveForm_qCoeff_eq_zero_of_dvd_div.lean
  spec-pin: P2M/Sol/S_CuspForm_IsPrimitiveForm_qCoeff_eq_zero_of_dvd_div.lean
  spec-pin: Theorems/Thm_CuspForm_exists_basis_gamma1_two_qCoeff_mem_range_intCast.lean
  spec-pin: P2M/Sol/S_CuspForm_exists_basis_gamma1_two_qCoeff_mem_range_intCast.lean
  spec-pin: Theorems/Thm_CuspForm_finiteDimensional_Gamma1.lean
  spec-pin: P2M/Sol/S_CuspForm_finiteDimensional_Gamma1.lean
-/
import FLTForHuman.ModularForms.HeckeULevel
import FLTForHuman.ModularForms.Defs.GammaH
import FLTForHuman.ModularForms.Defs.PrimitiveFormGamma1
import FLTForHuman.ModularForms.WeightOne.Gamma1IntegralBasis
import Mathlib.NumberTheory.ModularForms.QExpansion

set_option autoImplicit false

open scoped Real

noncomputable section

open scoped MatrixGroups ModularForm
open ModularFormClass

namespace COMMq

theorem Gamma1_le_GammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) :
    CongruenceSubgroup.Gamma1 M ≤ CohCarrier.GammaH M H :=
  CohCarrier.Gamma1_le_GammaH M H

theorem one_mem_strictPeriods_GammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) :
    (1 : ℝ) ∈ ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  have hT : ModularGroup.T ∈ CohCarrier.GammaH M H := CohCarrier.translation_mem_GammaH M H
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
  exact AddSubgroup.mem_zmultiples 1

theorem qCoeff_def (f : UpperHalfPlane → ℂ) (n : ℕ) :
    qCoeff f n = (UpperHalfPlane.qExpansion 1 f).coeff n := rfl

theorem eq_of_forall_qCoeff_eq {Γ : Subgroup (GL (Fin 2) ℝ)} (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {k : ℤ}
    (F G : CuspForm Γ k) (h : ∀ n : ℕ, qCoeff F n = qCoeff G n) : F = G := by
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  have h1 : UpperHalfPlane.qExpansion 1 (⇑(F - G)) = 0 := by
    rw [FunLike.coe_sub, ModularForm.qExpansion_sub one_pos hΓ F G]
    ext n
    have := h n
    rw [qCoeff_def, qCoeff_def] at this
    simp [this]
  have h2 : (⇑(F - G) : UpperHalfPlane → ℂ) = 0 :=
    (UpperHalfPlane.qExpansion_eq_zero_iff one_pos
      (SlashInvariantFormClass.periodic_comp_ofComplex (F - G) hΓ) (ModularFormClass.holo (F - G))
      (ModularFormClass.bdd_at_infty (F - G))).mp h1
  have h3 : F - G = 0 := DFunLike.ext' (by rw [h2]; rfl)
  exact sub_eq_zero.mp h3

theorem qCoeff_heckeULinH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) {q : ℕ} (hq : q.Prime)
    (hqM : q ∣ M) (f : CuspForm (CohCarrier.GammaH M H) k) (n : ℕ) :
    qCoeff (CuspForm.heckeULinH k q f) n = qCoeff f (n * q) := by
  -- `CuspForm.stableU` (pin `S_CuspForm_stableU.lean`), re-proved here: its port lives in
  -- `ModularCurve/Period/HeckeStability.lean`, whose closure is not this module's.  The `Γ_H` case
  -- drops out of the `Γ₀`-coset argument of `ModularForm.heckeU_slash_mapGL`, because the cocycle
  -- `g'` of `heckeMatrix_mul_of_eq` keeps both the `Γ₀(M)` column and the `(1,1)` entry mod `M`.
  have hU : CuspForm.StableU M H k q := by
    intro F
    refine ⟨?_, ModularForm.mdifferentiable_heckeU (CuspFormClass.holo F) k q,
      fun c hc => CuspFormClass.isZeroAt_heckeU F q hc⟩
    intro γ hγ
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ
    have hg0 : g ∈ CongruenceSubgroup.Gamma0 M := CohCarrier.GammaH_le_Gamma0 H hg
    have h10M : ((g 1 0 : ℤ) : ZMod M) = 0 := CongruenceSubgroup.Gamma0_mem.mp hg0
    have hcM : (M : ℤ) ∣ g 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h10M
    have hcq : (q : ℤ) ∣ g 1 0 := (Int.natCast_dvd_natCast.mpr hqM).trans hcM
    have hc0q : ((g 1 0 : ℤ) : ZMod q) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hcq
    have hInv : ∀ γ' ∈ ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)),
        (⇑F : UpperHalfPlane → ℂ) ∣[k] γ' = ⇑F := fun γ' hγ' => SlashInvariantFormClass.slash_action_eq F γ' hγ'
    have : NeZero q := ⟨hq.ne_zero⟩
    rw [ModularForm.HeckeRepresentatives.heckeU_eq_sum_zmod k ⇑F, SlashAction.sum_slash]
    calc ∑ x : ZMod q, ((⇑F : UpperHalfPlane → ℂ) ∣[k]
            ModularForm.heckeMatrix q x.val) ∣[k]
            (Matrix.SpecialLinearGroup.mapGL ℝ g)
        = ∑ x : ZMod q, (⇑F : UpperHalfPlane → ℂ) ∣[k] ModularForm.heckeMatrix q
            (ModularForm.HeckeRepresentatives.affinePerm g hc0q x).val := by
          refine Finset.sum_congr rfl fun x _ => ?_
          obtain ⟨e, he⟩ := CuspForm.dvd_numerator (ℓ := q) hcq x.val
          have hperm : ∀ r : ZMod q,
              ModularForm.HeckeRepresentatives.affinePerm g hc0q r = CuspForm.perm q g r := by
            intro r
            rw [ModularForm.HeckeRepresentatives.affinePerm_apply]
            show ((g 1 1 : ℤ) : ZMod q) *
                (((g 0 1 : ℤ) : ZMod q) + ((g 1 1 : ℤ) : ZMod q) * r)
              = ((g 1 1 : ℤ) : ZMod q) *
                (((g 0 1 : ℤ) : ZMod q) + r * ((g 1 1 : ℤ) : ZMod q))
            rw [mul_comm ((g 1 1 : ℤ) : ZMod q) r]
          have hxe : (ModularForm.HeckeRepresentatives.affinePerm g hc0q x).val
              = (CuspForm.perm q g (x.val : ZMod q)).val := by
            rw [hperm x, ZMod.natCast_zmod_val]
          have hxeZ : ((ModularForm.HeckeRepresentatives.affinePerm g hc0q x).val : ℤ)
              = ((CuspForm.perm q g (x.val : ZMod q)).val : ℤ) := by rw [hxe]
          obtain ⟨g', hg'10, hg'11, hmul⟩ :=
            ModularForm.HeckeRepresentatives.heckeMatrix_mul_of_eq (p := q) hq.ne_zero g x.val
              (ModularForm.HeckeRepresentatives.affinePerm g hc0q x).val e (by
                rw [← hxeZ] at he
                linear_combination he)
          have hg'G0 : g' ∈ CongruenceSubgroup.Gamma0 M := by
            rw [CongruenceSubgroup.Gamma0_mem, hg'10]
            push_cast
            rw [h10M, mul_zero]
          have h11 : ((g' 1 1 : ℤ) : ZMod M) = ((g 1 1 : ℤ) : ZMod M) := by
            have h := congrArg (fun z : ℤ => (z : ZMod M)) hg'11
            push_cast at h
            simpa only [h10M, zero_mul, sub_zero] using h
          have hmem : g' ∈ CohCarrier.GammaH M H := by
            refine CohCarrier.mem_GammaH_iff.mpr ⟨hg'G0, ?_⟩
            have hu : CohCarrier.gamma0Units M ⟨g', hg'G0⟩ = CohCarrier.gamma0Units M ⟨g, hg0⟩ := by
              refine Units.ext ?_
              rw [CohCarrier.val_gamma0Units, CohCarrier.val_gamma0Units]
              exact h11
            rw [hu]
            exact (CohCarrier.mem_GammaH_iff.mp hg).2
          rw [← SlashAction.slash_mul, hmul, SlashAction.slash_mul,
            hInv _ (Subgroup.mem_map_of_mem (Matrix.SpecialLinearGroup.mapGL ℝ) hmem)]
      _ = ∑ x : ZMod q, (⇑F : UpperHalfPlane → ℂ) ∣[k] ModularForm.heckeMatrix q x.val :=
          Equiv.sum_comp (ModularForm.HeckeRepresentatives.affinePerm g hc0q)
            (fun x => (⇑F : UpperHalfPlane → ℂ) ∣[k] ModularForm.heckeMatrix q x.val)
  have hcoe : (⇑(CuspForm.heckeULinH k q f) : UpperHalfPlane → ℂ) = ModularForm.heckeU k q ⇑f :=
    CuspForm.coe_heckeULinH_apply k hU f
  have h1 : qCoeff (CuspForm.heckeULinH k q f) n = qCoeff (ModularForm.heckeU k q ⇑f) n := by
    rw [hcoe]
  rw [h1, ModularFormClass.qCoeff_heckeU f (one_mem_strictPeriods_GammaH M H) hq.ne_zero n,
    ModularForm.coeffHeckeU_apply]

end COMMq

namespace CuspForm

theorem heckeULinH_comm
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ)
    {q q' : ℕ} (hq : q.Prime) (hqM : q ∣ M) (hq' : q'.Prime) (hq'M : q' ∣ M)
    (f : CuspForm (CohCarrier.GammaH M H) k) :
    CuspForm.heckeULinH k q (CuspForm.heckeULinH k q' f) = CuspForm.heckeULinH k q' (CuspForm.heckeULinH k q f) := by
  apply COMMq.eq_of_forall_qCoeff_eq (COMMq.one_mem_strictPeriods_GammaH M H)
  intro n
  rw [COMMq.qCoeff_heckeULinH M H k hq hqM, COMMq.qCoeff_heckeULinH M H k hq' hq'M,
    COMMq.qCoeff_heckeULinH M H k hq' hq'M, COMMq.qCoeff_heckeULinH M H k hq hqM, mul_right_comm]

end CuspForm

open CongruenceSubgroup ModularFormClass

namespace LiThreeVanishing

theorem qCoeff_zero_fun (n : ℕ) : qCoeff (0 : UpperHalfPlane → ℂ) n = 0 := by
  rw [qCoeff, UpperHalfPlane.qExpansion_zero, map_zero]

theorem changeLevel_apply_natCast {M M' : ℕ} [NeZero M] (h : M' ∣ M)
    (χ : DirichletCharacter ℂ M') {p : ℕ} (hp : Nat.Coprime p M) :
    DirichletCharacter.changeLevel h χ (p : ZMod M) = χ (p : ZMod M') := by
  have hu : IsUnit (p : ZMod M) := (ZMod.isUnit_iff_coprime p M).mpr hp
  rw [← hu.unit_spec, DirichletCharacter.changeLevel_eq_cast_of_dvd χ h, hu.unit_spec,
    ZMod.cast_natCast h]

theorem main (M : ℕ) [NeZero M] (k : ℤ) {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (hqq : q ∣ M / q)
    (ε' : DirichletCharacter ℂ (M / q)) (g : CuspForm (Gamma1 M) k)
    (hg : CuspForm.IsPrimitiveForm (DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd hqM) ε') g) :
    qCoeff g q = 0 := by
  have hM0 : M ≠ 0 := NeZero.ne M
  obtain ⟨h, -, hcoef, hneb⟩ :=
    CuspForm.exists_gamma1_div_coe_eq_heckeU_of_dvd_div k hqM hqq ε' g hg.isEigenformWith.hasNebentypus
  have ha : qCoeff g q = qCoeff h 1 := by rw [hcoef 1, mul_one]
  rw [ha]
  by_contra hne
  have hh0 : h ≠ 0 := by
    intro h0; apply hne; rw [h0, FunLike.coe_zero, qCoeff_zero_fun]
  have hocc : CuspForm.EigenpacketOccursAt k (fun n => qCoeff g n)
      (fun n => DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd hqM) ε' (n : ZMod M)) (M / q) := by
    refine ⟨ε', h, hh0, hneb, M.primeFactors, fun p hp hpS => ?_⟩
    have hpM : ¬ p ∣ M := fun hd => hpS (Nat.mem_primeFactors.mpr ⟨hp, hd, hM0⟩)
    have hcop : Nat.Coprime p M := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpM
    refine ⟨(changeLevel_apply_natCast _ ε' hcop).symm, fun n => ?_⟩
    have hpq : ¬ p ∣ q := fun hd => hpM (hd.trans hqM)
    have hrel := hg.isEigenformWith.hecke_of_not_dvd hp hpM (q * n)
    rw [changeLevel_apply_natCast _ ε' hcop] at hrel
    rw [hcoef, hcoef, hcoef, mul_left_comm]
    have hiff : (p ∣ q * n ↔ p ∣ n) :=
      ⟨fun hd => (Nat.Coprime.dvd_of_dvd_mul_left ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpq) hd),
        fun hd => hd.mul_left q⟩
    by_cases hpn : p ∣ n
    · rw [ite_eq_left hpn]
      rw [ite_eq_left (hiff.mpr hpn), Nat.mul_div_assoc q hpn] at hrel
      exact hrel
    · rw [ite_eq_right hpn]
      rw [ite_eq_right (fun hd => hpn (hiff.mp hd))] at hrel
      exact hrel
  have hlt : M / q < M := Nat.div_lt_self (Nat.pos_of_ne_zero hM0) hq.one_lt
  exact hg.not_eigenpacketOccursAt (Nat.div_dvd_of_dvd hqM) hlt.ne hocc

end LiThreeVanishing

namespace CuspForm

theorem IsPrimitiveForm.qCoeff_eq_zero_of_dvd_div (M : ℕ) [NeZero M] (k : ℤ) {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (hqq : q ∣ M / q)
    (ε' : DirichletCharacter ℂ (M / q)) (g : CuspForm (CongruenceSubgroup.Gamma1 M) k)
    (hg : CuspForm.IsPrimitiveForm
      (DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd hqM) ε') g) :
    ModularFormClass.qCoeff g q = 0 :=
  LiThreeVanishing.main M k hq hqM hqq ε' g hg

end CuspForm

open scoped MatrixGroups ModularForm

namespace CuspForm

theorem exists_basis_gamma1_two_qCoeff_mem_range_intCast (M : ℕ) [NeZero M] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (CuspForm (CongruenceSubgroup.Gamma1 M) 2)),
      ∀ (i : Fin n) (m : ℕ), ModularFormClass.qCoeff (b i) m ∈ Set.range ((↑) : ℤ → ℂ) := by
  obtain ⟨n, b, hb⟩ := CuspForm.exists_basis_gamma1_qCoeff_slash_mem_range_intCast M 2
  refine ⟨n, b, fun i m => ?_⟩
  simpa using hb i 1 (Subgroup.one_mem _) m

end CuspForm

open scoped MatrixGroups

namespace CuspForm

theorem finiteDimensional_Gamma1 (M : ℕ) [NeZero M] (k : ℤ) :
    FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma1 M) k) := by
  have := ModularForm.finiteDimensional_of_isArithmetic
    (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k
  exact FiniteDimensional.of_injective
    (CuspForm.toModularFormₗ : CuspForm (CongruenceSubgroup.Gamma1 M) k →ₗ[ℂ] ModularForm (CongruenceSubgroup.Gamma1 M) k)
    CuspForm.toModularFormₗ_injective

end CuspForm
