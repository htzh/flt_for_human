/-
  Commutation of the Hecke operators.

  The function-level commutations are proved by comparing `q`-coefficients: T5's
  `coeffHecke{T,U}_comm` etc. give
  `qCoeff (T_p (T_q f)) n = qCoeff (T_q (T_p f)) n`, and T5's
  `UpperHalfPlane.eq_of_forall_qCoeff_eq` closes. The bundled commutations reduce
  to the function-level ones pointwise. The five `LaurentSeries` commutations are
  the formal-series corner and reduce to the coefficient algebra on
  `LaurentSeries`; they are independent of the modular-forms side.

  The pin keeps a private copy of `eq_of_forall_qCoeff_eq` (as
  `W2WsF.eq_of_forall_qCoeff_eq`) plus `qCoeff_const_smul`/`periodic_const_smul`
  in each of the three function-level `S_` files. The port imports T5's public
  `UpperHalfPlane.eq_of_forall_qCoeff_eq` instead (the SET-1 `RealL` / SET-2 trace
  precedent) and drops the two `*_const_smul` helpers, which those files never
  use; the surviving side-condition transport is the private `mf_bdd` below.

  FLT provenance, pinned `aa2d8b3`:
  `P2M/Sol/S_ModularFormClass_hecke{U,U}.lean` (86 lines),
  `…_heckeT_heckeT_comm` (86), `…_heckeT_heckeU_comm` (90),
  `S_CuspForm_heckeTLin_comm` (13), `S_CuspForm_heckeULin_comm` (9),
  `S_CuspForm_heckeTLin_heckeULin_comm` (10), `S_ModularForm_heckeTLin_comm` (12)
  and the five `S_LaurentSeries_commute_*` (20 each).
-/
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import FLTForHuman.ModularForms.HeckeQCoeff
import FLTForHuman.ModularForms.HeckeOperatorForms
import FLTForHuman.ModularCurve.Defs.LaurentSeriesHecke

set_option autoImplicit false

noncomputable section

open Complex Function Filter
open UpperHalfPlane hiding I
open scoped Real MatrixGroups ModularForm Manifold Topology

open ModularForm ModularFormClass

/-! ## The function-level commutations -/

/-- `f`'s boundedness at `∞`, from its `ModularFormClass` instance. -/
private theorem mf_bdd {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    [ModularFormClass F Γ k] (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) :
    IsBoundedAtImInfty ⇑f :=
  haveI : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  bdd_at_infty f

private theorem heckeU_heckeU_comm_bare {f : ℍ → ℂ} (hper : Periodic (f ∘ ofComplex) 1)
    (hhol : MDiff f) (hbdd : IsBoundedAtImInfty f) (k : ℤ) (p q : ℕ) :
    heckeU k p (heckeU k q f) = heckeU k q (heckeU k p f) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  refine UpperHalfPlane.eq_of_forall_qCoeff_eq
    (periodic_heckeU_comp_ofComplex (periodic_heckeU_comp_ofComplex hper k q) k p)
    (mdifferentiable_heckeU (mdifferentiable_heckeU hhol k q) k p)
    (isBoundedAtImInfty_heckeU (isBoundedAtImInfty_heckeU hbdd k q) k p)
    (periodic_heckeU_comp_ofComplex (periodic_heckeU_comp_ofComplex hper k p) k q)
    (mdifferentiable_heckeU (mdifferentiable_heckeU hhol k p) k q)
    (isBoundedAtImInfty_heckeU (isBoundedAtImInfty_heckeU hbdd k p) k q) fun n ↦ ?_
  rw [UpperHalfPlane.qCoeff_heckeU (periodic_heckeU_comp_ofComplex hper k q)
      (mdifferentiable_heckeU hhol k q) (isBoundedAtImInfty_heckeU hbdd k q) k hp,
    UpperHalfPlane.qCoeff_heckeU (periodic_heckeU_comp_ofComplex hper k p)
      (mdifferentiable_heckeU hhol k p) (isBoundedAtImInfty_heckeU hbdd k p) k hq]
  have hq' : qCoeff (heckeU k q f) = coeffHeckeU q (qCoeff f) :=
    funext fun m ↦ UpperHalfPlane.qCoeff_heckeU hper hhol hbdd k hq m
  have hp' : qCoeff (heckeU k p f) = coeffHeckeU p (qCoeff f) :=
    funext fun m ↦ UpperHalfPlane.qCoeff_heckeU hper hhol hbdd k hp m
  rw [hq', hp', coeffHeckeU_comm]

private theorem heckeT_heckeT_comm_bare {f : ℍ → ℂ} (hper : Periodic (f ∘ ofComplex) 1)
    (hhol : MDiff f) (hbdd : IsBoundedAtImInfty f) (k : ℤ) {p q : ℕ} (hpq : p.Coprime q) :
    heckeT k p (heckeT k q f) = heckeT k q (heckeT k p f) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  refine UpperHalfPlane.eq_of_forall_qCoeff_eq
    (periodic_heckeT_comp_ofComplex (periodic_heckeT_comp_ofComplex hper k q) k p)
    (mdifferentiable_heckeT (mdifferentiable_heckeT hhol k q) k p)
    (isBoundedAtImInfty_heckeT (isBoundedAtImInfty_heckeT hbdd k q) k p)
    (periodic_heckeT_comp_ofComplex (periodic_heckeT_comp_ofComplex hper k p) k q)
    (mdifferentiable_heckeT (mdifferentiable_heckeT hhol k p) k q)
    (isBoundedAtImInfty_heckeT (isBoundedAtImInfty_heckeT hbdd k p) k q) fun n ↦ ?_
  rw [UpperHalfPlane.qCoeff_heckeT (periodic_heckeT_comp_ofComplex hper k q)
      (mdifferentiable_heckeT hhol k q) (isBoundedAtImInfty_heckeT hbdd k q) k hp,
    UpperHalfPlane.qCoeff_heckeT (periodic_heckeT_comp_ofComplex hper k p)
      (mdifferentiable_heckeT hhol k p) (isBoundedAtImInfty_heckeT hbdd k p) k hq]
  have hq' : qCoeff (heckeT k q f) = coeffHeckeT k q (qCoeff f) :=
    funext fun m ↦ UpperHalfPlane.qCoeff_heckeT hper hhol hbdd k hq m
  have hp' : qCoeff (heckeT k p f) = coeffHeckeT k p (qCoeff f) :=
    funext fun m ↦ UpperHalfPlane.qCoeff_heckeT hper hhol hbdd k hp m
  rw [hq', hp', coeffHeckeT_comm k hpq]

private theorem heckeT_heckeU_comm_bare {f : ℍ → ℂ} (hper : Periodic (f ∘ ofComplex) 1)
    (hhol : MDiff f) (hbdd : IsBoundedAtImInfty f) (k : ℤ) {p q : ℕ} (hpq : p.Coprime q) :
    heckeT k p (heckeU k q f) = heckeU k q (heckeT k p f) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  refine UpperHalfPlane.eq_of_forall_qCoeff_eq
    (periodic_heckeT_comp_ofComplex (periodic_heckeU_comp_ofComplex hper k q) k p)
    (mdifferentiable_heckeT (mdifferentiable_heckeU hhol k q) k p)
    (isBoundedAtImInfty_heckeT (isBoundedAtImInfty_heckeU hbdd k q) k p)
    (periodic_heckeU_comp_ofComplex (periodic_heckeT_comp_ofComplex hper k p) k q)
    (mdifferentiable_heckeU (mdifferentiable_heckeT hhol k p) k q)
    (isBoundedAtImInfty_heckeU (isBoundedAtImInfty_heckeT hbdd k p) k q) fun n ↦ ?_
  rw [UpperHalfPlane.qCoeff_heckeT (periodic_heckeU_comp_ofComplex hper k q)
      (mdifferentiable_heckeU hhol k q) (isBoundedAtImInfty_heckeU hbdd k q) k hp,
    UpperHalfPlane.qCoeff_heckeU (periodic_heckeT_comp_ofComplex hper k p)
      (mdifferentiable_heckeT hhol k p) (isBoundedAtImInfty_heckeT hbdd k p) k hq]
  have hq' : qCoeff (heckeU k q f) = coeffHeckeU q (qCoeff f) :=
    funext fun m ↦ UpperHalfPlane.qCoeff_heckeU hper hhol hbdd k hq m
  have hp' : qCoeff (heckeT k p f) = coeffHeckeT k p (qCoeff f) :=
    funext fun m ↦ UpperHalfPlane.qCoeff_heckeT hper hhol hbdd k hp m
  rw [hq', hp', coeffHeckeT_coeffHeckeU_comm k hpq]

/-- `U_p` and `U_q` commute on modular forms. Stated verbatim from
`Theorems/Thm_ModularFormClass_heckeU_heckeU_comm.lean`. -/
theorem ModularFormClass.heckeU_heckeU_comm {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (p q : ℕ) : ModularForm.heckeU k p (ModularForm.heckeU k q ⇑f) = ModularForm.heckeU k q (ModularForm.heckeU k p ⇑f) :=
  heckeU_heckeU_comm_bare (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)
    (ModularFormClass.holo f) (mf_bdd f hΓ) k p q

/-- `T_p` and `T_q` commute on modular forms for coprime `p`, `q`. Stated verbatim
from `Theorems/Thm_ModularFormClass_heckeT_heckeT_comm.lean`. -/
theorem ModularFormClass.heckeT_heckeT_comm {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {p q : ℕ} (hpq : Nat.Coprime p q) : ModularForm.heckeT k p (ModularForm.heckeT k q ⇑f) = ModularForm.heckeT k q (ModularForm.heckeT k p ⇑f) :=
  heckeT_heckeT_comm_bare (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)
    (ModularFormClass.holo f) (mf_bdd f hΓ) k hpq

/-- `T_p` and `U_q` commute on modular forms for coprime `p`, `q`. Stated verbatim
from `Theorems/Thm_ModularFormClass_heckeT_heckeU_comm.lean`. -/
theorem ModularFormClass.heckeT_heckeU_comm {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {p q : ℕ} (hpq : Nat.Coprime p q) : ModularForm.heckeT k p (ModularForm.heckeU k q ⇑f) = ModularForm.heckeU k q (ModularForm.heckeT k p ⇑f) :=
  heckeT_heckeU_comm_bare (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)
    (ModularFormClass.holo f) (mf_bdd f hΓ) k hpq

/-! ## The bundled commutations -/

namespace CuspForm

/-- The bundled `T_p` and `T_q` commute. Stated verbatim from
`Theorems/Thm_CuspForm_heckeTLin_comm.lean`. -/
theorem heckeTLin_comm {N : ℕ} (k : ℤ) {p q : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    (hq : q.Prime) (hqN : ¬ q ∣ N) :
    Commute (CuspForm.heckeTLin k hp hpN) (CuspForm.heckeTLin k hq hqN) := by
  by_cases hpq : p = q
  · subst hpq; exact Commute.refl _
  · rw [commute_iff_eq]; ext f τ
    simpa using congrFun (ModularFormClass.heckeT_heckeT_comm f (by simp)
      ((Nat.coprime_primes hp hq).mpr hpq)) τ

/-- The bundled `U_p` and `U_q` commute. Stated verbatim from
`Theorems/Thm_CuspForm_heckeULin_comm.lean`. -/
theorem heckeULin_comm {N : ℕ} [NeZero N] (k : ℤ) {p q : ℕ} (hpN : p ∣ N) (hqN : q ∣ N) :
    Commute (CuspForm.heckeULin k hpN) (CuspForm.heckeULin k hqN) := by
  rw [commute_iff_eq]; ext f τ
  simpa using congrFun (ModularFormClass.heckeU_heckeU_comm f (by simp) p q) τ

/-- The bundled `T_p` and `U_q` commute. Stated verbatim from
`Theorems/Thm_CuspForm_heckeTLin_heckeULin_comm.lean`. -/
theorem heckeTLin_heckeULin_comm {N : ℕ} [NeZero N] (k : ℤ) {p q : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) (hqN : q ∣ N) :
    Commute (CuspForm.heckeTLin k hp hpN) (CuspForm.heckeULin k hqN) := by
  rw [commute_iff_eq]; ext f τ
  simpa using congrFun (ModularFormClass.heckeT_heckeU_comm f (by simp)
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => hpN (h.trans hqN))) τ

end CuspForm

namespace ModularForm

/-- The bundled `T_p` and `T_q` commute on modular forms. Stated verbatim from
`Theorems/Thm_ModularForm_heckeTLin_comm.lean`. -/
theorem heckeTLin_comm {N : ℕ} (k : ℤ) {p q : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) (hq : q.Prime) (hqN : ¬ q ∣ N) :
    Commute (ModularForm.heckeTLin k hp hpN) (ModularForm.heckeTLin k hq hqN) := by
  by_cases hpq : p = q
  · subst hpq; exact Commute.refl _
  · rw [commute_iff_eq]; ext f τ
    simpa using congrFun (ModularFormClass.heckeT_heckeT_comm f (by simp)
      ((Nat.coprime_primes hp hq).mpr hpq)) τ

end ModularForm

/-! ## The formal-series commutations -/

namespace LaurentSeries

/-- `heckeU` commutes with itself. Stated verbatim from
`Theorems/Thm_LaurentSeries_commute_heckeU_heckeU.lean`. -/
theorem commute_heckeU_heckeU (R : Type*) [CommRing R] (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Commute (heckeU R a ha) (heckeU R b hb) := by
  ext f n
  simp only [Module.End.mul_apply, coeff_heckeU]
  ring_nf

/-- `heckeU` commutes with `heckeV` for coprime indices. Stated verbatim from
`Theorems/Thm_LaurentSeries_commute_heckeU_heckeV.lean`. -/
theorem commute_heckeU_heckeV (R : Type*) [CommRing R] (p ℓ : ℕ) (hp : 0 < p) (hℓ : 0 < ℓ)
    (hpl : Nat.Coprime p ℓ) :
    Commute (heckeU R p hp) (heckeV R ℓ hℓ) := by
  have cop : IsCoprime (ℓ : ℤ) (p : ℤ) := Nat.isCoprime_iff_coprime.mpr hpl.symm
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne'
  ext f n
  simp only [Module.End.mul_apply, coeff_heckeU, coeff_heckeV]
  by_cases h : (ℓ : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := h
    rw [ite_eq_left ⟨p * m, by ring⟩, ite_eq_left ⟨m, rfl⟩,
      show (p : ℤ) * (ℓ * m) = ℓ * (p * m) by ring,
      Int.mul_ediv_cancel_left _ hℓ0, Int.mul_ediv_cancel_left _ hℓ0]
  · rw [ite_eq_right h, ite_eq_right]
    intro h'
    exact h (cop.dvd_of_dvd_mul_left h')

/-- `heckeV` commutes with itself for coprime indices. Stated verbatim from
`Theorems/Thm_LaurentSeries_commute_heckeV_heckeV.lean`. -/
theorem commute_heckeV_heckeV (R : Type*) [CommRing R] (ℓ ℓ' : ℕ) (hℓ : 0 < ℓ) (hℓ' : 0 < ℓ')
    (h : Nat.Coprime ℓ ℓ') :
    Commute (heckeV R ℓ hℓ) (heckeV R ℓ' hℓ') := by
  have cop : IsCoprime (ℓ : ℤ) (ℓ' : ℤ) := Nat.isCoprime_iff_coprime.mpr h
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne'
  have hℓ0' : (ℓ' : ℤ) ≠ 0 := by exact_mod_cast hℓ'.ne'

  have key : ∀ (a b : ℕ) (ha : 0 < a) (hb : 0 < b), IsCoprime (a : ℤ) (b : ℤ) → (a : ℤ) ≠ 0 → (b : ℤ) ≠ 0 →
      ∀ (f : LaurentSeries R) (n : ℤ), (heckeV R a ha (heckeV R b hb f)).coeff n =
        if (a : ℤ) * b ∣ n then f.coeff (n / ((a : ℤ) * b)) else 0 := by
    intro a b ha hb hab ha0 hb0 f n
    rw [coeff_heckeV]
    by_cases h1 : (a : ℤ) ∣ n
    · obtain ⟨m, rfl⟩ := h1
      rw [ite_eq_left ⟨m, rfl⟩, Int.mul_ediv_cancel_left _ ha0, coeff_heckeV]
      by_cases h2 : (b : ℤ) ∣ m
      · obtain ⟨k, rfl⟩ := h2
        rw [ite_eq_left ⟨k, rfl⟩, Int.mul_ediv_cancel_left _ hb0, ite_eq_left ⟨k, by ring⟩,
          show (a : ℤ) * (b * k) = (a * b) * k by ring,
          Int.mul_ediv_cancel_left _ (mul_ne_zero ha0 hb0)]
      · rw [ite_eq_right h2, ite_eq_right]
        rintro ⟨k, hk⟩
        apply h2
        refine ⟨k, ?_⟩
        have : (a : ℤ) * m = a * (b * k) := by rw [hk]; ring
        exact mul_left_cancel₀ ha0 this
    · rw [ite_eq_right h1, ite_eq_right]
      rintro ⟨k, hk⟩
      exact h1 ⟨b * k, by rw [hk]; ring⟩
  ext f n
  rw [Module.End.mul_apply, Module.End.mul_apply, key ℓ ℓ' hℓ hℓ' cop hℓ0 hℓ0' f n,
    key ℓ' ℓ hℓ' hℓ cop.symm hℓ0' hℓ0 f n, mul_comm]

/-- `heckeU` commutes with `heckeT` for coprime indices. Stated verbatim from
`Theorems/Thm_LaurentSeries_commute_heckeU_heckeT.lean`. -/
theorem commute_heckeU_heckeT (R : Type*) [CommRing R] (p ℓ : ℕ) (hp : 0 < p) (hℓ : 0 < ℓ) (k : ℕ)
    (hpl : Nat.Coprime p ℓ) :
    Commute (heckeU R p hp) (heckeT R ℓ hℓ k) :=
  (commute_heckeU_heckeU R p ℓ hp hℓ).add_right ((commute_heckeU_heckeV R p ℓ hp hℓ hpl).smul_right _)

/-- `heckeT` commutes with itself for coprime indices. Stated verbatim from
`Theorems/Thm_LaurentSeries_commute_heckeT_heckeT.lean`. -/
theorem commute_heckeT_heckeT (R : Type*) [CommRing R] (ℓ ℓ' : ℕ) (hℓ : 0 < ℓ) (hℓ' : 0 < ℓ') (k : ℕ)
    (h : Nat.Coprime ℓ ℓ') :
    Commute (heckeT R ℓ hℓ k) (heckeT R ℓ' hℓ' k) := by
  have h1 := commute_heckeU_heckeU R ℓ ℓ' hℓ hℓ'
  have h2 := commute_heckeU_heckeV R ℓ ℓ' hℓ hℓ' h
  have h3 := (commute_heckeU_heckeV R ℓ' ℓ hℓ' hℓ h.symm).symm
  have h4 := commute_heckeV_heckeV R ℓ ℓ' hℓ hℓ' h
  exact (h1.add_right (h2.smul_right _)).add_left ((h3.add_right (h4.smul_right _)).smul_left _)

end LaurentSeries

end
