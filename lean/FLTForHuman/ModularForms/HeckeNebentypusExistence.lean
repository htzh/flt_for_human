/-
  Existence of the nebentypus character of a Γ₁ Hecke eigenform.

  Transcribed from `P2M/Sol/S_CuspForm_exists_hasNebentypus_of_qCoeff_hecke_eigen.lean`
  (pinned `aa2d8b3`, 591 lines), one of the two headlines of the Γ₁/Nebentypus set
  (`topics/deligneSerre/WORKORDER-S8-nebentypus.md`).  The other is
  `HeckeNebentypusFricke.lean`; the two pin files are *not* twins (they differ at
  1,019 lines and share only a 118-line prelude).

  The pin's `dd`/Γ₁ prelude is imported from `ModularForms/HeckeEigenNebentypus.lean`
  (public after the WORKORDER-S8 promotion) and the analytic/Hecke vocabulary from
  `HeckePrelude`/`HeckeQCoeff`/`HeckeAnalytic`/`Gamma1Vanishing` and the `Defs`
  modules; `det_eq`/`det_mod`/`T_mem_Gamma1`/`T_pow_mem_Gamma1`/`conj_mem_Gamma1`/
  `periodic_smul`/`mapGL_apply` reuse their existing public homes.  Everything else —
  the general `slash_eq_smul_prime`, the `IsDiamondScalar` diamond-scalar calculus,
  `exists_dirichlet` and the assembly — is written `private` here; the only public
  declaration is the headline.

  FLT provenance, pinned `aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_exists_hasNebentypus_of_qCoeff_hecke_eigen.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_CuspForm_exists_hasNebentypus_of_qCoeff_hecke_eigen.lean

  spec-pin: Theorems/Thm_CuspForm_exists_hasNebentypus_of_qCoeff_hecke_eigen.lean
  spec-pin: P2M/Sol/S_CuspForm_exists_hasNebentypus_of_qCoeff_hecke_eigen.lean

-/
import FLTForHuman.ModularForms.Gamma1Vanishing
import FLTForHuman.ModularForms.HeckePrelude
import FLTForHuman.ModularForms.HeckeQCoeff
import FLTForHuman.ModularForms.HeckeAnalytic
import FLTForHuman.ModularForms.Defs.HeckeRepresentatives
import FLTForHuman.ModularForms.WeightOne.Defs.RatAt
import FLTForHuman.ModularForms.WeightOne.Defs.GammaRational
import FLTForHuman.ModularForms.WeightOne.FrickeFunction
import FLTForHuman.ModularForms.HeckeEigenNebentypus
import FLTForHuman.DeligneSerre.Relevement
import Mathlib.NumberTheory.DirichletCharacter.Basic

set_option autoImplicit false

noncomputable section

open CongruenceSubgroup ModularForm UpperHalfPlane Filter Function
open scoped ModularForm UpperHalfPlane MatrixGroups

open CuspForm.HeckeEigenNebentypus
open ModularForm.HeckeRepresentatives
open ModularForm.Level
open ModularForm.HeckeGamma1
open X1DiamondRational

namespace CuspForm

namespace NebentypusFromMultipliers

variable {M : ℕ}

local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

private theorem dd_one {N : ℕ} : dd (N := N) 1 = 1 := by simp [dd]

section Slash

variable {k : ℤ} {p : ℕ}

private theorem isBoundedAtImInfty_heckeU (hp : p ≠ 0) {F : ℍ → ℂ} (hF : IsBoundedAtImInfty F) :
    IsBoundedAtImInfty (heckeU k p F) := by
  rw [heckeU_def]
  induction (Finset.range p) using Finset.induction_on with
  | empty => (simp; exact (Filter.zero_zeroAtFilter atImInfty).boundedAtFilter)
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact (isBoundedAtImInfty_slash_heckeMatrix hp j hF).add ih

end Slash

section Prime

variable [NeZero M] {k : ℤ}

private theorem slash_eq_smul_prime (g : CuspForm Γ₁(M) k) (c : ℂ)
    {p : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ M)
    (heig : ∃ lam : ℂ, ∀ n : ℕ,
      ModularFormClass.qCoeff (⇑g) (n * p)
        + c * (p : ℂ) ^ (k - 1)
            * (if p ∣ n then ModularFormClass.qCoeff (⇑g) (n / p) else 0)
        = lam * ModularFormClass.qCoeff (⇑g) n)
    (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 M) (hσp : dd (N := M) σ = (p : ZMod M)) :
    (⇑g : ℍ → ℂ) ∣[k] σ = c • (⇑g : ℍ → ℂ) := by
  obtain ⟨lam, hlam⟩ := heig
  have hp0 : p ≠ 0 := hp.ne_zero

  have hgT : ∀ n : ℕ, (⇑g : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ n)) = ⇑g :=
    fun n => SlashInvariantFormClass.slash_action_eq g _ (Subgroup.mem_map_of_mem _ (T_pow_mem_Gamma1 M n))
  have hgper : Periodic (⇑g ∘ ofComplex) 1 := periodic_of_slash_T (by simpa using hgT 1)
  have hghol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (⇑g) := g.holo'
  have hgbdd : IsBoundedAtImInfty (⇑g) := ModularFormClass.bdd_at_infty g

  set gσ : ℍ → ℂ := (⇑g : ℍ → ℂ) ∣[k] σ with hgσ
  have hgσ_inv : ∀ γ : SL(2, ℤ), γ ∈ Gamma1 M → gσ ∣[k] γ = gσ := by
    intro γ hγ
    rw [hgσ, ← SlashAction.slash_mul, show σ * γ = (σ * γ * σ⁻¹) * σ by rw [inv_mul_cancel_right],
      SlashAction.slash_mul]
    congr 1
    exact SlashInvariantFormClass.slash_action_eq g _ (Subgroup.mem_map_of_mem _ (conj_mem_Gamma1 hσ hγ))

  set U : ℍ → ℂ := heckeU k p (⇑g) with hU
  set D : ℍ → ℂ := (⇑g : ℍ → ℂ) ∣[k] heckeDiagMatrix p with hD
  set T' : ℍ → ℂ := U + gσ ∣[k] heckeDiagMatrix p with hT'
  have hT'_inv : ∀ γ ∈ Γ₁(M), T' ∣[k] γ = T' := fun γ hγ =>
    ModularForm.heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1 k hp hpM
      (fun γ' hγ' => SlashInvariantFormClass.slash_action_eq g γ' hγ') σ hσ hσp γ hγ

  have hDT : D ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T) = D :=
    slash_heckeDiagMatrix_slash_T hp0 (hgT p)
  have hgσδT : (gσ ∣[k] heckeDiagMatrix p) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T)
      = gσ ∣[k] heckeDiagMatrix p :=
    slash_heckeDiagMatrix_slash_T hp0 (hgσ_inv _ (T_pow_mem_Gamma1 M p))
  have hUT : U ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T) = U := by
    have hUeq : U = T' - gσ ∣[k] heckeDiagMatrix p := by rw [hT', add_sub_cancel_right]
    rw [hUeq, sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash,
      hT'_inv _ (Subgroup.mem_map_of_mem _ (T_mem_Gamma1 M)), hgσδT]
  have hUper : Periodic (U ∘ ofComplex) 1 := periodic_of_slash_T hUT
  have hDper : Periodic (D ∘ ofComplex) 1 := periodic_of_slash_T hDT
  have hUhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) U :=
    mdifferentiable_heckeU hghol
  have hDhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) D :=
    hghol.slash k _
  have hUbdd : IsBoundedAtImInfty U := isBoundedAtImInfty_heckeU hp0 hgbdd
  have hDbdd : IsBoundedAtImInfty D := isBoundedAtImInfty_slash_heckeDiagMatrix hp0 hgbdd

  set φ : ℍ → ℂ := U + c • D with hφ
  have hφper : Periodic (φ ∘ ofComplex) 1 := UpperHalfPlane.periodic_add hUper (UpperHalfPlane.periodic_smul hDper c)
  have hφhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) φ :=
    hUhol.add (hDhol.const_smul c)
  have hφbdd : IsBoundedAtImInfty φ := hUbdd.add (hDbdd.smul c)

  have hanU := analyticAt_cuspFunction_zero one_pos hUper hUhol hUbdd
  have hancD : AnalyticAt ℂ (cuspFunction 1 (c • D)) 0 :=
    analyticAt_cuspFunction_zero one_pos (UpperHalfPlane.periodic_smul hDper c) (hDhol.const_smul c) (hDbdd.smul c)
  have hanD := analyticAt_cuspFunction_zero one_pos hDper hDhol hDbdd
  have hang := analyticAt_cuspFunction_zero one_pos hgper hghol hgbdd

  set G : ℍ → ℂ := fun τ => g (heckeDiagMatrix p • τ) with hG
  have hDG : D = ((p : ℂ) ^ (k - 1)) • G := by
    funext τ
    rw [hD, slash_heckeDiagMatrix_apply k hp0, Pi.smul_apply, smul_eq_mul]
  have hpk : ((p : ℂ) ^ (k - 1)) ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.mpr hp0)
  have hGD : G = ((p : ℂ) ^ (k - 1))⁻¹ • D := by
    rw [hDG, smul_smul, inv_mul_cancel₀ hpk, one_smul]
  have hanG : AnalyticAt ℂ (cuspFunction 1 G) 0 := by
    rw [hGD]
    exact analyticAt_cuspFunction_zero one_pos (UpperHalfPlane.periodic_smul hDper _) (hDhol.const_smul _)
      (hDbdd.smul _)
  have hqD : ∀ n, ModularFormClass.qCoeff D n
      = (p : ℂ) ^ (k - 1) * (if p ∣ n then ModularFormClass.qCoeff (⇑g) (n / p) else 0) := by
    intro n
    rw [ModularFormClass.qCoeff, hDG, qExpansion_smul hanG, map_smul, smul_eq_mul]
    congr 1
    exact UpperHalfPlane.qCoeff_comp_heckeDiagMatrix_smul hgper hghol hgbdd hp0 n
  have hqU : ∀ n, ModularFormClass.qCoeff U n = ModularFormClass.qCoeff (⇑g) (n * p) := by
    intro n
    rw [hU, UpperHalfPlane.qCoeff_heckeU hgper hghol hgbdd k hp0 n, coeffHeckeU_apply]
  have hqφ : ∀ n, ModularFormClass.qCoeff φ n = ModularFormClass.qCoeff (lam • (⇑g : ℍ → ℂ)) n := by
    intro n
    rw [ModularFormClass.qCoeff, ModularFormClass.qCoeff, hφ, qExpansion_add hanU hancD,
      qExpansion_smul hanD, qExpansion_smul hang, map_add, map_smul, map_smul, smul_eq_mul,
      smul_eq_mul]
    have h1 := hqU n
    have h2 := hqD n
    have h3 := hlam n
    simp only [ModularFormClass.qCoeff] at h1 h2 h3 ⊢
    rw [h1, h2, ← h3, mul_assoc]

  have hφeq : φ = lam • (⇑g : ℍ → ℂ) :=
    UpperHalfPlane.eq_of_forall_qCoeff_eq hφper hφhol hφbdd (UpperHalfPlane.periodic_smul hgper lam)
      (hghol.const_smul lam) (hgbdd.smul lam) hqφ

  set hf : ℍ → ℂ := gσ - c • (⇑g : ℍ → ℂ) with hhf
  have hσδ : UpperHalfPlane.σ (heckeDiagMatrix p) c = c := by
    rw [σ_heckeDiagMatrix]; rfl
  have hhfδ : hf ∣[k] heckeDiagMatrix p = T' - lam • (⇑g : ℍ → ℂ) := by
    rw [hhf, sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash, ModularForm.smul_slash,
      hσδ, ← hφeq, hφ, hT']
    abel
  have hhy : ∀ γ ∈ Γ₁(M), (hf ∣[k] heckeDiagMatrix p) ∣[k] γ = hf ∣[k] heckeDiagMatrix p := by
    intro γ hγ
    obtain ⟨γ₀, hγ₀, rfl⟩ := hγ
    rw [hhfδ, sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash,
      hT'_inv _ (Subgroup.mem_map_of_mem _ hγ₀)]
    congr 2
    change (lam • (⇑g : ℍ → ℂ)) ∣[k] γ₀ = lam • (⇑g : ℍ → ℂ)
    rw [ModularForm.SL_smul_slash]
    congr 1
    exact SlashInvariantFormClass.slash_action_eq g _ (Subgroup.mem_map_of_mem _ hγ₀)

  have hσSL : Matrix.SpecialLinearGroup.mapGL ℝ σ ∈ 𝒮ℒ := ⟨σ, rfl⟩
  let hC : CuspForm Γ₁(M) k :=
    { toFun := hf
      slash_action_eq' := by
        intro A hA
        obtain ⟨γ, hγ, rfl⟩ := hA
        change hf ∣[k] γ = hf
        rw [hhf, sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash, hgσ_inv γ hγ,
          ModularForm.SL_smul_slash]
        congr 3
        exact SlashInvariantFormClass.slash_action_eq g _ (Subgroup.mem_map_of_mem _ hγ)
      holo' := (hghol.slash k _).sub (hghol.const_smul c)
      zero_at_cusps' := by
        intro cusp hcusp A hA
        have hcusp' : IsCusp (Matrix.SpecialLinearGroup.mapGL ℝ σ • cusp) Γ₁(M) := by
          rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hcusp ⊢
          exact hcusp.smul_of_mem hσSL
        have h1 : IsZeroAtImInfty (gσ ∣[k] A) := by
          have := (OnePoint.IsZeroAt.smul_iff (g := Matrix.SpecialLinearGroup.mapGL ℝ σ)
            (c := cusp) (f := (⇑g : ℍ → ℂ)) (k := k)).mp (CuspFormClass.zero_at_cusps g hcusp')
          exact this A hA
        have h2 : IsZeroAtImInfty ((⇑g : ℍ → ℂ) ∣[k] A) := CuspFormClass.zero_at_cusps g hcusp A hA
        change IsZeroAtImInfty (hf ∣[k] A)
        rw [hhf, sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash, ModularForm.smul_slash]
        exact h1.add ((h2.smul _).neg) }
  have hC0 : hC = 0 :=
    CuspForm.eq_zero_of_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1 hp hpM k hC hhy
  have hf0 : hf = 0 := by
    have := congrArg (fun F : CuspForm Γ₁(M) k => (⇑F : ℍ → ℂ)) hC0
    exact this
  rw [hhf, sub_eq_zero] at hf0
  exact hf0

end Prime

section Character

variable [NeZero M] {k : ℤ}

private def IsDiamondScalar (g : CuspForm Γ₁(M) k) (σ : SL(2, ℤ)) (C : ℂ) : Prop :=
  (⇑g : ℍ → ℂ) ∣[k] σ = C • (⇑g : ℍ → ℂ)

set_option linter.unusedSectionVars false in
private theorem isDiamondScalar_one (g : CuspForm Γ₁(M) k) : IsDiamondScalar g 1 1 := by
  rw [IsDiamondScalar, SlashAction.slash_one, one_smul]

set_option linter.unusedSectionVars false in
private theorem IsDiamondScalar.mul {g : CuspForm Γ₁(M) k} {σ₁ σ₂ : SL(2, ℤ)} {C₁ C₂ : ℂ}
    (h₁ : IsDiamondScalar g σ₁ C₁) (h₂ : IsDiamondScalar g σ₂ C₂) :
    IsDiamondScalar g (σ₁ * σ₂) (C₁ * C₂) := by
  rw [IsDiamondScalar] at h₁ h₂ ⊢
  rw [SlashAction.slash_mul, h₁, ModularForm.SL_smul_slash, h₂, smul_smul]

private theorem IsDiamondScalar.pow {g : CuspForm Γ₁(M) k} {σ : SL(2, ℤ)} {C : ℂ}
    (h : IsDiamondScalar g σ C) (r : ℕ) : IsDiamondScalar g (σ ^ r) (C ^ r) := by
  induction r with
  | zero => simpa using isDiamondScalar_one g
  | succ r ih => rw [pow_succ, pow_succ]; exact ih.mul h

set_option linter.unusedSectionVars false in
private theorem IsDiamondScalar.of_inv_mul_mem {g : CuspForm Γ₁(M) k} {σ σ' : SL(2, ℤ)} {C : ℂ}
    (h : IsDiamondScalar g σ C) (hmem : σ⁻¹ * σ' ∈ Gamma1 M) : IsDiamondScalar g σ' C := by
  have hfix : (⇑g : ℍ → ℂ) ∣[k] (σ⁻¹ * σ') = ⇑g :=
    SlashInvariantFormClass.slash_action_eq g _ (Subgroup.mem_map_of_mem _ hmem)
  rw [IsDiamondScalar] at h ⊢
  rw [show σ' = σ * (σ⁻¹ * σ') by rw [mul_inv_cancel_left], SlashAction.slash_mul, h,
    ModularForm.SL_smul_slash, hfix]

set_option linter.unusedSectionVars false in
private theorem IsDiamondScalar.unique {g : CuspForm Γ₁(M) k} (hg : g ≠ 0) {σ : SL(2, ℤ)} {C C' : ℂ}
    (h : IsDiamondScalar g σ C) (h' : IsDiamondScalar g σ C') : C = C' := by
  rw [IsDiamondScalar] at h h'
  have hCC : (C - C') • (⇑g : ℍ → ℂ) = 0 := by rw [sub_smul, ← h, ← h', sub_self]
  by_contra hne
  apply hg
  have hg0 : (⇑g : ℍ → ℂ) = 0 := by
    have := congrArg (fun F : ℍ → ℂ => (C - C')⁻¹ • F) hCC
    simpa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hne)] using this
  exact DFunLike.ext g 0 fun τ => congrFun hg0 τ

private theorem exists_lift_isDiamondScalar (g : CuspForm Γ₁(M) k) (cp : ℕ → ℂ)
    (hprime : ∀ p : ℕ, p.Prime → ¬ p ∣ M → ∀ σ : SL(2, ℤ), σ ∈ Gamma0 M →
      dd (N := M) σ = (p : ZMod M) → IsDiamondScalar g σ (cp p))
    (n : ℕ) (hn : n.Coprime M) :
    ∃ σ : SL(2, ℤ), σ ∈ Gamma0 M ∧ dd (N := M) σ = (n : ZMod M) ∧ ∃ C : ℂ, IsDiamondScalar g σ C := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero =>
    have hM : M = 1 := by simpa using hn
    subst hM
    exact ⟨1, one_mem _, Subsingleton.elim _ _, 1, isDiamondScalar_one g⟩
  | one => exact ⟨1, one_mem _, by simp [dd], 1, isDiamondScalar_one g⟩
  | prime_pow p r hp hr =>
    have hpM : ¬ p ∣ M := by
      have : p.Coprime M := Nat.Coprime.coprime_dvd_left (dvd_pow_self p hr.ne') hn
      exact (Nat.Prime.coprime_iff_not_dvd hp).mp this
    obtain ⟨σ, hσ, hσd⟩ := exists_lift (M := M) p ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpM)
    have base := hprime p hp hpM σ hσ hσd
    refine ⟨σ ^ r, pow_mem hσ r, ?_, cp p ^ r, base.pow r⟩
    rw [dd_pow hσ, hσd, Nat.cast_pow]
  | coprime a b ha hb hab iha ihb =>
    obtain ⟨σa, hσa, hda, Ca, hsa⟩ := iha (Nat.Coprime.coprime_dvd_left (dvd_mul_right a b) hn)
    obtain ⟨σb, hσb, hdb, Cb, hsb⟩ := ihb (Nat.Coprime.coprime_dvd_left (dvd_mul_left b a) hn)
    refine ⟨σa * σb, mul_mem hσa hσb, ?_, Ca * Cb, hsa.mul hsb⟩
    rw [dd_mul hσa hσb, hda, hdb, Nat.cast_mul]

private theorem exists_isDiamondScalar (g : CuspForm Γ₁(M) k) (cp : ℕ → ℂ)
    (hprime : ∀ p : ℕ, p.Prime → ¬ p ∣ M → ∀ σ : SL(2, ℤ), σ ∈ Gamma0 M →
      dd (N := M) σ = (p : ZMod M) → IsDiamondScalar g σ (cp p))
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) : ∃ C : ℂ, IsDiamondScalar g γ C := by
  obtain ⟨u, hu⟩ := isUnit_dd hγ
  set n : ℕ := (dd (N := M) γ).val with hn
  have hncast : (n : ZMod M) = dd γ := ZMod.natCast_zmod_val _
  have hcop : n.Coprime M := by
    have := ZMod.val_coe_unit_coprime u
    rwa [hu] at this
  obtain ⟨σ, hσ, hdd, C, hC⟩ := exists_lift_isDiamondScalar g cp hprime n hcop
  exact ⟨C, hC.of_inv_mul_mem (inv_mul_mem_Gamma1 hσ hγ (hdd.trans hncast))⟩

private def diamondScalar (g : CuspForm Γ₁(M) k) (cp : ℕ → ℂ)
    (hprime : ∀ p : ℕ, p.Prime → ¬ p ∣ M → ∀ σ : SL(2, ℤ), σ ∈ Gamma0 M →
      dd (N := M) σ = (p : ZMod M) → IsDiamondScalar g σ (cp p))
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) : ℂ :=
  (exists_isDiamondScalar g cp hprime γ hγ).choose

private theorem isDiamondScalar_diamondScalar (g : CuspForm Γ₁(M) k) (cp : ℕ → ℂ)
    (hprime : ∀ p : ℕ, p.Prime → ¬ p ∣ M → ∀ σ : SL(2, ℤ), σ ∈ Gamma0 M →
      dd (N := M) σ = (p : ZMod M) → IsDiamondScalar g σ (cp p))
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) : IsDiamondScalar g γ (diamondScalar g cp hprime γ hγ) :=
  (exists_isDiamondScalar g cp hprime γ hγ).choose_spec

private theorem exists_dirichlet (g : CuspForm Γ₁(M) k) (hg : g ≠ 0) (cp : ℕ → ℂ)
    (hprime : ∀ p : ℕ, p.Prime → ¬ p ∣ M → ∀ σ : SL(2, ℤ), σ ∈ Gamma0 M →
      dd (N := M) σ = (p : ZMod M) → IsDiamondScalar g σ (cp p)) :
    ∃ ε : DirichletCharacter ℂ M,
      (∀ γ : SL(2, ℤ), γ ∈ Gamma0 M → IsDiamondScalar g γ (ε (dd (N := M) γ))) ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ M → ε (p : ZMod M) = cp p := by
  classical

  have hlift : ∀ u : (ZMod M)ˣ, ∃ σ : SL(2, ℤ), σ ∈ Gamma0 M ∧ dd (N := M) σ = (u : ZMod M) := by
    intro u
    have hcop : (u : ZMod M).val.Coprime M := ZMod.val_coe_unit_coprime u
    obtain ⟨σ, hσ, hd⟩ := exists_lift (M := M) (u : ZMod M).val hcop
    exact ⟨σ, hσ, hd.trans (ZMod.natCast_zmod_val _)⟩
  let lift : (ZMod M)ˣ → SL(2, ℤ) := fun u => (hlift u).choose
  have lift_mem : ∀ u, lift u ∈ Gamma0 M := fun u => (hlift u).choose_spec.1
  have lift_dd : ∀ u, dd (N := M) (lift u) = (u : ZMod M) := fun u => (hlift u).choose_spec.2
  let val : (ZMod M)ˣ → ℂ := fun u => diamondScalar g cp hprime (lift u) (lift_mem u)
  have hval : ∀ u, IsDiamondScalar g (lift u) (val u) := fun u =>
    isDiamondScalar_diamondScalar g cp hprime (lift u) (lift_mem u)

  have hany : ∀ (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (C : ℂ), IsDiamondScalar g γ C →
      C = val (isUnit_dd hγ).unit := by
    intro γ hγ C hC
    set u := (isUnit_dd hγ).unit with hu
    have hu' : (u : ZMod M) = dd γ := (isUnit_dd hγ).unit_spec
    have htrans : IsDiamondScalar g γ (val u) :=
      (hval u).of_inv_mul_mem (inv_mul_mem_Gamma1 (lift_mem u) hγ ((lift_dd u).trans hu'))
    exact hC.unique hg htrans

  have val_one : val 1 = 1 := by
    have := hany 1 (one_mem _) 1 (isDiamondScalar_one g)
    have h1 : (isUnit_dd (N := M) (one_mem (Gamma0 M))).unit = 1 := by
      ext; rw [IsUnit.unit_spec, Units.val_one, dd_one]
    rw [h1] at this
    exact this.symm
  have val_mul : ∀ u v, val (u * v) = val u * val v := by
    intro u v
    have hmem : lift u * lift v ∈ Gamma0 M := mul_mem (lift_mem u) (lift_mem v)
    have hsc : IsDiamondScalar g (lift u * lift v) (val u * val v) := (hval u).mul (hval v)
    have := hany _ hmem _ hsc
    have huv : (isUnit_dd (N := M) hmem).unit = u * v := by
      ext; rw [IsUnit.unit_spec, dd_mul (lift_mem u) (lift_mem v), lift_dd, lift_dd, Units.val_mul]
    rw [huv] at this
    exact this.symm
  have val_ne : ∀ u, val u ≠ 0 := by
    intro u h0
    have := val_mul u u⁻¹
    rw [mul_inv_cancel, val_one, h0, zero_mul] at this
    exact one_ne_zero this

  let φ : (ZMod M)ˣ →* ℂˣ :=
    { toFun := fun u => Units.mk0 (val u) (val_ne u)
      map_one' := by ext; simp [val_one]
      map_mul' := fun u v => by ext; simp [val_mul] }
  refine ⟨MulChar.ofUnitHom φ, ?_, ?_⟩
  · intro γ hγ
    obtain ⟨C, hC⟩ := exists_isDiamondScalar g cp hprime γ hγ
    have hCval := hany γ hγ C hC
    have hcoe : (MulChar.ofUnitHom φ) (dd (N := M) γ) = val (isUnit_dd hγ).unit := by
      conv_lhs => rw [← (isUnit_dd hγ).unit_spec, MulChar.ofUnitHom_coe]
      rfl
    rw [hcoe, ← hCval]
    exact hC
  · intro p hp hpM
    obtain ⟨σ, hσ, hσd⟩ := exists_lift (M := M) p ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpM)
    have hsc : IsDiamondScalar g σ (cp p) := hprime p hp hpM σ hσ hσd
    have hCval := hany σ hσ (cp p) hsc
    have hunit : IsUnit ((p : ℕ) : ZMod M) := by rw [← hσd]; exact isUnit_dd hσ
    have hcoe : (MulChar.ofUnitHom φ) ((p : ℕ) : ZMod M) = val (isUnit_dd hσ).unit := by
      have h1 : ((isUnit_dd (N := M) hσ).unit : ZMod M) = (p : ZMod M) := by
        rw [IsUnit.unit_spec, hσd]
      conv_lhs => rw [← h1, MulChar.ofUnitHom_coe]
      rfl
    rw [hcoe, ← hCval]

end Character

section Main

variable [NeZero M] {k : ℤ}

private theorem main (f : CuspForm Γ₁(M) k) (hf0 : f ≠ 0) (χ : ℕ → ℂ)
    (hf : ∀ p : ℕ, p.Prime → ¬ p ∣ M → ∃ lam : ℂ, ∀ n : ℕ,
        ModularFormClass.qCoeff f (p * n) +
            χ p * (if p ∣ n then ModularFormClass.qCoeff f (n / p) else 0) =
          lam * ModularFormClass.qCoeff f n) :
    ∃ ε : DirichletCharacter ℂ M, CuspForm.HasNebentypus ε f ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ M → ε (p : ZMod M) * (p : ℂ) ^ (k - 1) = χ p := by

  set cp : ℕ → ℂ := fun p => χ p * ((p : ℂ) ^ (k - 1))⁻¹ with hcp
  have hprime : ∀ p : ℕ, p.Prime → ¬ p ∣ M → ∀ σ : SL(2, ℤ), σ ∈ Gamma0 M →
      dd (N := M) σ = (p : ZMod M) → IsDiamondScalar f σ (cp p) := by
    intro p hp hpM σ hσ hσd
    have hpk : ((p : ℂ) ^ (k - 1)) ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero)
    refine slash_eq_smul_prime f (cp p) hp hpM ?_ σ hσ hσd
    obtain ⟨lam, hlam⟩ := hf p hp hpM
    refine ⟨lam, fun n => ?_⟩
    have h := hlam n
    rw [mul_comm p n] at h
    have hc : cp p * (p : ℂ) ^ (k - 1) = χ p := by
      rw [hcp]; simp only; rw [mul_assoc, inv_mul_cancel₀ hpk, mul_one]
    rw [hc]
    exact h
  obtain ⟨ε, hε, hεp⟩ := exists_dirichlet f hf0 cp hprime
  refine ⟨ε, ?_, ?_⟩
  ·
    intro γ hγ τ
    have hslash := hε γ hγ
    rw [IsDiamondScalar] at hslash
    have hpt := congrFun hslash τ
    rw [SL_slash_apply, Pi.smul_apply, smul_eq_mul] at hpt

    have hden : denom (Matrix.SpecialLinearGroup.toGL
        ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) (τ : ℂ)
        = ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) := by
      simp [denom]
    rw [hden] at hpt
    have hne : ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
      rw [← hden]; exact UpperHalfPlane.denom_ne_zero _ τ
    have hzk : (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ (-k) ≠ 0 := zpow_ne_zero _ hne

    have key : f (γ • τ) =
        ε (dd (N := M) γ) * f τ * ((((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ (-k))⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hzk]
      exact hpt
    rw [key, ← zpow_neg, neg_neg, dd]
    ring
  · intro p hp hpM
    have hpk : ((p : ℂ) ^ (k - 1)) ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero)
    rw [hεp p hp hpM, hcp]
    simp only
    rw [mul_assoc, inv_mul_cancel₀ hpk, mul_one]

end Main

end NebentypusFromMultipliers

end CuspForm

namespace CuspForm

/-- Pin `CuspForm.exists_hasNebentypus_of_qCoeff_hecke_eigen`, at the wrapper's statement:
existence of the nebentypus character from the `q`-coefficient Hecke-eigenvalue relation. -/
theorem exists_hasNebentypus_of_qCoeff_hecke_eigen
    (N : ℕ) [NeZero N] (k : ℤ) (f : CuspForm (Gamma1 N) k) (hf0 : f ≠ 0)
    (χ : ℕ → ℂ)
    (hf : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∃ lam : ℂ, ∀ n : ℕ,
        ModularFormClass.qCoeff f (p * n) +
            χ p * (if p ∣ n then ModularFormClass.qCoeff f (n / p) else 0) =
          lam * ModularFormClass.qCoeff f n) :
    ∃ ε : DirichletCharacter ℂ N, CuspForm.HasNebentypus ε f ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ N → ε (p : ZMod N) * (p : ℂ) ^ (k - 1) = χ p :=
  NebentypusFromMultipliers.main f hf0 χ hf

end CuspForm
