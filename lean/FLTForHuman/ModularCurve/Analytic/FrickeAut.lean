/-
  m5 — the Fricke automorphisms of `modularFunctionField N` / `...Full N`.

  `exists_isFrickeAut_of_modularPolynomialData` is the pin's `W2B` block: the
  `AdjoinRoot`/`IntermediateField.lift` construction of the `q ↦ q ^ N` swap from
  a modular polynomial datum. The three companions transport it to the full
  field and to `frickeInvolutionFull`; the third M8 headline and
  `coe_frickeInvolutionFull_modularUnitSeries`, deferred from m4 because they
  need `isFrickeAutFull_frickeInvolutionFull_prime`, are closed here.

  FLT provenance, pinned `aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_exists_isFrickeAut_of_modularPolynomialData.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_exists_isFrickeAutFull.lean
-/
import FLTForHuman.ModularCurve.Defs.AtkinLehner
import FLTForHuman.ModularCurve.Defs.PhiGen
import FLTForHuman.ModularCurve.Degree.PhiData
import FLTForHuman.ModularCurve.Degree.PhiDegree
import FLTForHuman.ModularCurve.Analytic.FrickeInvariance
import FLTForHuman.ModularCurve.Analytic.CuspBookkeeping
import FLTForHuman.ModularCurve.Analytic.ModularUnitQExpansion
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

set_option autoImplicit false

noncomputable section

open ModularCurve IntermediateField UpperHalfPlane
open scoped MatrixGroups

namespace ModularCurve

private instance instIsScalarTowerRatSubtypeMem {L : Type*} [Field L] [Algebra ℚ L]
    (F : IntermediateField ℚ L) : IsScalarTower ℚ F L :=
  IsScalarTower.of_algebraMap_eq' (by apply RingHom.ext_rat)

section Fricke

variable (N : ℕ) [NeZero N]

theorem algHom_ext_of_eq_on_gens {A : Type*} [DivisionRing A] [Algebra ℚ A]
    {f g : modularFunctionField N →ₐ[ℚ] A}
    (hj : f (⟨jq, jq_mem N⟩ : modularFunctionField N) = g (⟨jq, jq_mem N⟩ : modularFunctionField N)) (hjN : f (⟨jqN N, jqN_mem N⟩ : modularFunctionField N) = g (⟨jqN N, jqN_mem N⟩ : modularFunctionField N)) : f = g := by
  ext ⟨x, hx⟩
  induction hx using IntermediateField.adjoin_induction with
  | mem x hxS =>
      rcases hxS with rfl | rfl
      · exact hj
      · exact hjN
  | algebraMap r =>
      have hr : (⟨algebraMap ℚ (LaurentSeries ℚ) r,
          (modularFunctionField N).algebraMap_mem r⟩ : modularFunctionField N)
          = algebraMap ℚ (modularFunctionField N) r := by
        apply Subtype.ext
        show algebraMap ℚ (LaurentSeries ℚ) r
          = ((algebraMap ℚ (modularFunctionField N) r : modularFunctionField N) :
              LaurentSeries ℚ)
        rw [eq_ratCast (algebraMap ℚ (LaurentSeries ℚ)) r,
          eq_ratCast (algebraMap ℚ (modularFunctionField N)) r]
        norm_cast
      exact (congrArg f hr).trans
        ((f.commutes r).trans ((g.commutes r).symm.trans (congrArg g hr.symm)))
  | add x y hx hy ihx ihy =>
      show f (⟨x, hx⟩ + ⟨y, hy⟩) = g (⟨x, hx⟩ + ⟨y, hy⟩)
      rw [map_add, map_add, ihx, ihy]
  | inv x hx ih =>
      show f (⟨x, hx⟩⁻¹) = g (⟨x, hx⟩⁻¹)
      rw [map_inv₀, map_inv₀, ih]
  | mul x y hx hy ihx ihy =>
      show f (⟨x, hx⟩ * ⟨y, hy⟩) = g (⟨x, hx⟩ * ⟨y, hy⟩)
      rw [map_mul, map_mul, ihx, ihy]

variable {N}

theorem exists_isFrickeAut_of_endo (φ : modularFunctionField N →ₐ[ℚ] modularFunctionField N)
    (h1 : φ (⟨jq, jq_mem N⟩ : modularFunctionField N) = (⟨jqN N, jqN_mem N⟩ : modularFunctionField N)) (h2 : φ (⟨jqN N, jqN_mem N⟩ : modularFunctionField N) = (⟨jq, jq_mem N⟩ : modularFunctionField N)) :
    ∃ σ : modularFunctionField N ≃ₐ[ℚ] modularFunctionField N, IsFrickeAut N σ := by
  have hcomp : φ.comp φ = AlgHom.id ℚ (modularFunctionField N) := by
    refine algHom_ext_of_eq_on_gens N ?_ ?_
    · show φ (φ (⟨jq, jq_mem N⟩ : modularFunctionField N)) = (⟨jq, jq_mem N⟩ : modularFunctionField N)
      rw [h1, h2]
    · show φ (φ (⟨jqN N, jqN_mem N⟩ : modularFunctionField N)) = (⟨jqN N, jqN_mem N⟩ : modularFunctionField N)
      rw [h2, h1]
  exact ⟨AlgEquiv.ofAlgHom φ φ hcomp hcomp, h1, h2⟩

end Fricke

section Swap

variable {N : ℕ} [NeZero N] (data : ModularPolynomialData N)

theorem eval_swap_eq_zero (hsymm : EvalSymm data.Φ) :
    data.Φ.eval₂ (evalAtJqN N) jq = 0 := by
  rw [evalAtJqN_def, hsymm (jqN N) jq]
  exact data.eval_eq_zero

end Swap

section BaseMap

variable (N : ℕ) [NeZero N]

def frickeBaseHom : ℚ⟮jq⟯ →+* LaurentSeries ℚ :=
  (qExpand ℚ N).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ))

@[scoped simp]
theorem frickeBaseHom_jGen : frickeBaseHom N jGen = jqN N := rfl

theorem frickeBaseHom_comp_evalAtJGen :
    (frickeBaseHom N).comp evalAtJGen = evalAtJqN N := by
  refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
  show frickeBaseHom N (evalAtJGen Polynomial.X) = evalAtJqN N Polynomial.X
  rw [evalAtJqN_X]
  show frickeBaseHom N (Polynomial.eval₂ (Int.castRingHom ℚ⟮jq⟯) jGen Polynomial.X) = jqN N
  rw [Polynomial.eval₂_X]
  rfl

end BaseMap

section Lift

variable {N : ℕ} [NeZero N] (data : ModularPolynomialData N)

theorem eval₂_minpoly_frickeBaseHom (hsymm : EvalSymm data.Φ) (hirr : PhiIrreducible data) :
    (minpoly ℚ⟮jq⟯ (jqN N)).eval₂ (frickeBaseHom N) jq = 0 := by
  rw [ModularPolynomialData.minpoly_jqN_eq data hirr, ModularPolynomialData.toAdjoin, Polynomial.eval₂_map,
    frickeBaseHom_comp_evalAtJGen]
  exact eval_swap_eq_zero data hsymm

def frickeRelativeHom (hsymm : EvalSymm data.Φ) (hirr : PhiIrreducible data) :
    ℚ⟮jq⟯⟮jqN N⟯ →+* LaurentSeries ℚ :=
  (AdjoinRoot.lift (frickeBaseHom N) jq (eval₂_minpoly_frickeBaseHom data hsymm hirr)).comp
    (adjoinRootEquivAdjoin ℚ⟮jq⟯ data.isIntegral_jqN).symm.toAlgHom.toRingHom

theorem frickeRelativeHom_gen (hsymm : EvalSymm data.Φ) (hirr : PhiIrreducible data) :
    frickeRelativeHom data hsymm hirr (AdjoinSimple.gen ℚ⟮jq⟯ (jqN N)) = jq := by
  rw [frickeRelativeHom, RingHom.comp_apply]
  rw [show (adjoinRootEquivAdjoin ℚ⟮jq⟯ data.isIntegral_jqN).symm.toAlgHom.toRingHom
        (AdjoinSimple.gen ℚ⟮jq⟯ (jqN N))
      = AdjoinRoot.root (minpoly ℚ⟮jq⟯ (jqN N)) from
    adjoinRootEquivAdjoin_symm_apply_gen ℚ⟮jq⟯ data.isIntegral_jqN]
  exact AdjoinRoot.lift_root _

theorem frickeRelativeHom_algebraMap (hsymm : EvalSymm data.Φ) (hirr : PhiIrreducible data)
    (c : ℚ⟮jq⟯) :
    frickeRelativeHom data hsymm hirr (algebraMap ℚ⟮jq⟯ ℚ⟮jq⟯⟮jqN N⟯ c)
      = frickeBaseHom N c := by
  rw [frickeRelativeHom, RingHom.comp_apply]
  rw [show (adjoinRootEquivAdjoin ℚ⟮jq⟯ data.isIntegral_jqN).symm.toAlgHom.toRingHom
        (algebraMap ℚ⟮jq⟯ ℚ⟮jq⟯⟮jqN N⟯ c)
      = algebraMap ℚ⟮jq⟯ (AdjoinRoot (minpoly ℚ⟮jq⟯ (jqN N))) c from
    (adjoinRootEquivAdjoin ℚ⟮jq⟯ data.isIntegral_jqN).symm.commutes c]
  rw [AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.lift_of _

end Lift

section Absolute

variable (N : ℕ) [NeZero N]

theorem modularFunctionField_eq_restrictScalars :
    modularFunctionField N = (ℚ⟮jq⟯⟮jqN N⟯).restrictScalars ℚ :=
  (IntermediateField.adjoin_simple_adjoin_simple ℚ jq (jqN N)).symm

def relativeRingEquiv : ℚ⟮jq⟯⟮jqN N⟯ ≃+* modularFunctionField N where
  toFun x := ⟨(x : LaurentSeries ℚ),
    (SetLike.ext_iff.mp (modularFunctionField_eq_restrictScalars N) _).mpr x.2⟩
  invFun y := ⟨(y : LaurentSeries ℚ),
    (SetLike.ext_iff.mp (modularFunctionField_eq_restrictScalars N) _).mp y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

variable {N} (data : ModularPolynomialData N)

def frickeAbsoluteHom (hsymm : EvalSymm data.Φ) (hirr : PhiIrreducible data) :
    modularFunctionField N →+* LaurentSeries ℚ :=
  (frickeRelativeHom data hsymm hirr).comp (relativeRingEquiv N).symm.toRingHom

theorem frickeAbsoluteHom_jInF (hsymm : EvalSymm data.Φ) (hirr : PhiIrreducible data) :
    frickeAbsoluteHom data hsymm hirr (⟨jq, jq_mem N⟩ : modularFunctionField N) = jqN N := by
  show frickeRelativeHom data hsymm hirr ((relativeRingEquiv N).symm (⟨jq, jq_mem N⟩ : modularFunctionField N)) = jqN N
  rw [show (relativeRingEquiv N).symm (⟨jq, jq_mem N⟩ : modularFunctionField N) = algebraMap ℚ⟮jq⟯ ℚ⟮jq⟯⟮jqN N⟯ jGen from
    Subtype.ext rfl]
  rw [frickeRelativeHom_algebraMap]
  rfl

theorem frickeAbsoluteHom_jNInF (hsymm : EvalSymm data.Φ) (hirr : PhiIrreducible data) :
    frickeAbsoluteHom data hsymm hirr (⟨jqN N, jqN_mem N⟩ : modularFunctionField N) = jq := by
  show frickeRelativeHom data hsymm hirr ((relativeRingEquiv N).symm (⟨jqN N, jqN_mem N⟩ : modularFunctionField N)) = jq
  rw [show (relativeRingEquiv N).symm (⟨jqN N, jqN_mem N⟩ : modularFunctionField N) = AdjoinSimple.gen ℚ⟮jq⟯ (jqN N) from
    Subtype.ext rfl]
  exact frickeRelativeHom_gen data hsymm hirr

theorem mem_of_apply_gens_mem (f : modularFunctionField N →+* LaurentSeries ℚ)
    (E : IntermediateField ℚ (LaurentSeries ℚ))
    (hj : f (⟨jq, jq_mem N⟩ : modularFunctionField N) ∈ E) (hjN : f (⟨jqN N, jqN_mem N⟩ : modularFunctionField N) ∈ E) (x : modularFunctionField N) :
    f x ∈ E := by
  obtain ⟨x, hx⟩ := x
  induction hx using IntermediateField.adjoin_induction with
  | mem y hyS =>
      rcases hyS with rfl | rfl
      · exact hj
      · exact hjN
  | algebraMap r =>
      have hr : (⟨algebraMap ℚ (LaurentSeries ℚ) r,
          (modularFunctionField N).algebraMap_mem r⟩ : modularFunctionField N)
          = (r : modularFunctionField N) := by
        apply Subtype.ext
        show algebraMap ℚ (LaurentSeries ℚ) r
          = ((r : modularFunctionField N) : LaurentSeries ℚ)
        rw [eq_ratCast (algebraMap ℚ (LaurentSeries ℚ)) r]
        norm_cast
      have hmem : f (r : modularFunctionField N) ∈ E := by
        rw [map_ratCast]
        exact SubfieldClass.ratCast_mem E r
      exact (congrArg f hr).symm ▸ hmem
  | add x y hx hy ihx ihy =>
      show f (⟨x, hx⟩ + ⟨y, hy⟩) ∈ E
      rw [map_add]
      exact add_mem ihx ihy
  | inv x hx ih =>
      show f (⟨x, hx⟩⁻¹) ∈ E
      rw [map_inv₀]
      exact inv_mem ih
  | mul x y hx hy ihx ihy =>
      have key : (⟨x * y, mul_mem hx hy⟩ : modularFunctionField N) = ⟨x, hx⟩ * ⟨y, hy⟩ :=
        Subtype.ext ((modularFunctionField N).coe_mul ⟨x, hx⟩ ⟨y, hy⟩).symm
      have hmem : f (⟨x, hx⟩ * ⟨y, hy⟩) ∈ E := by
        rw [map_mul]
        exact mul_mem ihx ihy
      exact (congrArg f key).symm ▸ hmem

theorem frickeAbsoluteHom_mem (hsymm : EvalSymm data.Φ) (hirr : PhiIrreducible data)
    (x : modularFunctionField N) :
    frickeAbsoluteHom data hsymm hirr x ∈ modularFunctionField N := by
  refine mem_of_apply_gens_mem (frickeAbsoluteHom data hsymm hirr) (modularFunctionField N)
    ?_ ?_ x
  · rw [frickeAbsoluteHom_jInF data hsymm hirr]
    exact jqN_mem N
  · rw [frickeAbsoluteHom_jNInF data hsymm hirr]
    exact jq_mem N

end Absolute

section Endo

variable {N : ℕ} [NeZero N] (data : ModularPolynomialData N)

def frickeEndoRingHom (hsymm : EvalSymm data.Φ) (hirr : PhiIrreducible data) :
    modularFunctionField N →+* modularFunctionField N :=
  (frickeAbsoluteHom data hsymm hirr).codRestrict (modularFunctionField N)
    (frickeAbsoluteHom_mem data hsymm hirr)

def frickeEndoAlgHom (hsymm : EvalSymm data.Φ) (hirr : PhiIrreducible data) :
    modularFunctionField N →ₐ[ℚ] modularFunctionField N where
  toRingHom := frickeEndoRingHom data hsymm hirr
  commutes' r := by
    rw [eq_ratCast (algebraMap ℚ (modularFunctionField N)) r]
    exact map_ratCast (frickeEndoRingHom data hsymm hirr) r

theorem frickeEndoAlgHom_jInF (hsymm : EvalSymm data.Φ) (hirr : PhiIrreducible data) :
    frickeEndoAlgHom data hsymm hirr (⟨jq, jq_mem N⟩ : modularFunctionField N) = (⟨jqN N, jqN_mem N⟩ : modularFunctionField N) := by
  apply Subtype.ext
  exact frickeAbsoluteHom_jInF data hsymm hirr

theorem frickeEndoAlgHom_jNInF (hsymm : EvalSymm data.Φ) (hirr : PhiIrreducible data) :
    frickeEndoAlgHom data hsymm hirr (⟨jqN N, jqN_mem N⟩ : modularFunctionField N) = (⟨jq, jq_mem N⟩ : modularFunctionField N) := by
  apply Subtype.ext
  exact frickeAbsoluteHom_jNInF data hsymm hirr

theorem exists_isFrickeAut_of_modularPolynomialData {N : ℕ} [NeZero N]
    (data : ModularPolynomialData N) (hsymm : EvalSymm data.Φ)
    (hirr : PhiIrreducible data) :
    ∃ σ : modularFunctionField N ≃ₐ[ℚ] modularFunctionField N, IsFrickeAut N σ :=
  exists_isFrickeAut_of_endo (frickeEndoAlgHom data hsymm hirr)
    (frickeEndoAlgHom_jInF data hsymm hirr) (frickeEndoAlgHom_jNInF data hsymm hirr)

end Endo
/-! ## The transported automorphisms and the deferred m4 headline -/

theorem exists_isFrickeAut (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] :
    ∃ σ : modularFunctionField ℓ ≃ₐ[ℚ] modularFunctionField ℓ, IsFrickeAut ℓ σ := by
  obtain ⟨data, hirr, hsymm⟩ := exists_phiIrreducible_evalSymm ℓ
  exact exists_isFrickeAut_of_modularPolynomialData data hsymm hirr

private theorem cast_algEquiv_exists {E E' : IntermediateField ℚ (LaurentSeries ℚ)} (h : E = E')
    (σ : E ≃ₐ[ℚ] E) :
    ∃ σ' : E' ≃ₐ[ℚ] E', ∀ x : E', ((σ' x : E') : LaurentSeries ℚ) = σ ⟨x, h ▸ x.2⟩ := by
  subst h
  exact ⟨σ, fun _ => rfl⟩

theorem exists_isFrickeAutFull (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] :
    ∃ σ : modularFunctionFieldFull ℓ ≃ₐ[ℚ] modularFunctionFieldFull ℓ, IsFrickeAutFull ℓ σ := by
  have hℓp : ℓ.Prime := hℓ.out
  have : NeZero ℓ := ⟨hℓp.ne_zero⟩
  have hfull : modularFunctionFieldFull ℓ = modularFunctionField ℓ := full_eq_of_prime hℓp
  obtain ⟨σ, hσ⟩ := exists_isFrickeAut ℓ
  obtain ⟨σ', hσ'⟩ := cast_algEquiv_exists hfull.symm σ
  refine ⟨σ', ?_⟩
  intro a b hab _ _
  have hcases : a = 1 ∧ ℓ = b ∨ ℓ = a ∧ b = 1 := by
    have hprime : (a * b).Prime := hab ▸ hℓp
    rcases Nat.prime_mul_iff.mp hprime with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · right; exact ⟨hab.symm.trans (mul_one a), rfl⟩
    · left; exact ⟨rfl, hab.symm.trans (one_mul b)⟩
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have H : ∀ (y : LaurentSeries ℚ) (hy : y ∈ modularFunctionField ℓ), y = jq →
        ((σ ⟨y, hy⟩ : modularFunctionField ℓ) : LaurentSeries ℚ) = qExpand ℚ ℓ jq := by
      rintro y hy rfl
      exact congrArg Subtype.val hσ.1
    apply Subtype.ext
    rw [hσ']
    exact H _ _ (qExpand_one_apply jq)
  · have H : ∀ (y : LaurentSeries ℚ) (hy : y ∈ modularFunctionField ℓ), y = jqN ℓ →
        ((σ ⟨y, hy⟩ : modularFunctionField ℓ) : LaurentSeries ℚ) = qExpand ℚ 1 jq := by
      rintro y hy rfl
      exact (congrArg Subtype.val hσ.2).trans (qExpand_one_apply jq).symm
    apply Subtype.ext
    rw [hσ']
    exact H _ _ rfl

theorem isFrickeAutFull_frickeInvolutionFull_prime (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] :
    IsFrickeAutFull ℓ (frickeInvolutionFull ℓ) := by
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  exact isFrickeAutFull_frickeInvolutionFull ℓ (exists_isFrickeAutFull ℓ)

/-! The third M8 headline, deferred from `Analytic/FrickeInvariance.lean` because
it needs the Fricke automorphism above. -/

theorem coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant (ℓ : ℕ) [Fact (Nat.Prime ℓ)]
    (f g : LaurentSeries ℚ) (F : UpperHalfPlane → ℂ)
    (hF : ∀ τ : UpperHalfPlane, HasSum (fun m : ℤ => ((f.coeff m : ℚ) : ℂ) *
      Function.Periodic.qParam 1 (τ : ℂ) ^ m) (F τ))
    (hG : ∀ τ : UpperHalfPlane, HasSum (fun m : ℤ => ((g.coeff m : ℚ) : ℂ) *
      Function.Periodic.qParam ℓ (τ : ℂ) ^ m) (F (ModularGroup.S • τ)))
    (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma0 ℓ, ∀ τ : UpperHalfPlane, F (γ • τ) = F τ)
    (hf : f ∈ modularFunctionFieldFull ℓ) :
    ((frickeInvolutionFull ℓ ⟨f, hf⟩ : modularFunctionFieldFull ℓ) : LaurentSeries ℚ) = g := by
  have hℓp : ℓ.Prime := Fact.out
  have : NeZero ℓ := ⟨hℓp.ne_zero⟩
  have : NeZero ((ℓ : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr hℓp.ne_zero⟩
  have hcyc : IsCyclotomicExtension {ℓ} ℚ (CyclotomicField ℓ ℚ) :=
    CyclotomicField.isCyclotomicExtension (n := ℓ) (K := ℚ)
  have : FiniteDimensional ℚ (CyclotomicField ℓ ℚ) :=
    IsCyclotomicExtension.finiteDimensional {ℓ} ℚ (CyclotomicField ℓ ℚ)
  have : IsGalois ℚ (CyclotomicField ℓ ℚ) :=
    IsCyclotomicExtension.isGalois (S := {ℓ}) (K := ℚ) (L := CyclotomicField ℓ ℚ)
  obtain ⟨z, hz⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ (CyclotomicField ℓ ℚ)
    (Set.mem_singleton ℓ) hℓp.ne_zero
  have hzu : IsUnit z := hz.isUnit hℓp.ne_zero
  have hζ : IsPrimitiveRoot ((hzu.unit : (CyclotomicField ℓ ℚ)ˣ) : CyclotomicField ℓ ℚ) ℓ := by
    rw [hzu.unit_spec]; exact hz
  exact QExpN.fricke_transport ℓ hzu.unit hζ (QExpN.sigma ℓ hzu.unit hζ)
    (QExpN.sigma_zeta ℓ hzu.unit hζ) f g F hF hG hinv
    (frickeInvolutionFull ℓ) (isFrickeAutFull_frickeInvolutionFull_prime ℓ) hf

theorem coe_frickeInvolutionFull_modularUnitSeries (ℓ : ℕ) [Fact (Nat.Prime ℓ)]
    (hmem : modularUnitSeries ℓ ∈ modularFunctionFieldFull ℓ) :
    ((frickeInvolutionFull ℓ ⟨modularUnitSeries ℓ, hmem⟩ : modularFunctionFieldFull ℓ) :
      LaurentSeries ℚ) = (ℓ : ℚ) ^ 12 • (modularUnitSeries ℓ)⁻¹ := by
  have hℓp : ℓ.Prime := Fact.out
  have : NeZero ℓ := ⟨hℓp.ne_zero⟩
  exact coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant ℓ
    (modularUnitSeries ℓ) ((ℓ : ℚ) ^ 12 • (modularUnitSeries ℓ)⁻¹)
    (fun τ => ModularForm.discriminant τ
      / ModularForm.discriminant (ModularForm.heckeDiagMatrix ℓ • τ))
    (fun τ => hasSum_modularUnitSeries_qParam ℓ τ)
    (fun τ => hasSum_smul_modularUnitSeries_inv_qParam ℓ τ)
    (fun γ hγ τ => discriminant_div_discriminant_heckeDiagMatrix_smul ℓ γ hγ τ) hmem

end ModularCurve
