/-
  m4 — the Fricke/inclusion headlines and the `q ↦ q ^ ℓ` transport.

  This module carries the pin's third M8 file's distinctive block
  (`natDegree_interpPoly_lt`, `realL_jtN_S`, `realL_sum_qExpand_mul_jq_pow`,
  `coeffMap_castC_injective`, `embW` and the 137-content `fricke_transport`),
  plus the first two M8 headlines and the four small `modularUnitSeries` targets.
  The shared 651-content-line prelude lives once in
  `FLTForHuman/ModularCurve/Analytic/Gamma0InvariantCore.lean`.

  The third headline `coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant`
  and `coe_frickeInvolutionFull_modularUnitSeries` are **downstream of
  `exists_isFrickeAutFull`** (m5): the pin proves both through
  `isFrickeAutFull_frickeInvolutionFull_prime`, which is 5 lines on top of m5's
  `exists_isFrickeAutFull`. They are therefore delivered in m5
  (`Analytic/FrickeAut.lean`), after the Fricke automorphism exists. The
  transport itself (`fricke_transport`) is parametric in the automorphism and
  lives here.

  FLT provenance, pinned `aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_modularUnitSeries_mem_modularFunctionField.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_isIntegral_adjoin_jq_modularUnitSeries.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_isIntegral_adjoin_jq_modularUnitSeries_inv.lean
-/
import FLTForHuman.ModularCurve.Analytic.Gamma0InvariantCore
import FLTForHuman.ModularCurve.Analytic.ModularUnitQExpansion
import FLTForHuman.ModularCurve.Defs.AtkinLehner
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

set_option autoImplicit false

noncomputable section

open UpperHalfPlane Complex Filter Topology Function Polynomial
open scoped MatrixGroups

local notation "𝕢" => Function.Periodic.qParam

namespace ModularCurve

namespace QExpN

lemma natDegree_interpPoly_lt {L : Type*} [CommRing L] {n : ℕ} (H Y : Fin (n + 1) → L) :
    (interpPoly H Y).natDegree < n + 1 := by
  unfold interpPoly
  refine Nat.lt_succ_of_le (Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_)
  refine (Polynomial.natDegree_C_mul_le _ _).trans ((Polynomial.natDegree_prod_le _ _).trans ?_)
  refine (Finset.sum_le_sum fun m _ => Polynomial.natDegree_X_sub_C_le (Y m)).trans ?_
  simp [Finset.card_erase_of_mem (Finset.mem_univ i)]

variable {K : Type} [Field K] [Algebra ℚ K] [IsGalois ℚ K] [FiniteDimensional ℚ K]
  (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ) (σ : K →+* ℂ)
  (hσ : σ (ζ : K) = expRoot ℓ)
  (f g : LaurentSeries ℚ) (F : ℍ → ℂ)
  (hF : ∀ τ : ℍ, HasSum (fun m : ℤ => ((f.coeff m : ℚ) : ℂ) * 𝕢 1 (τ : ℂ) ^ m) (F τ))
  (hG : ∀ τ : ℍ, HasSum (fun m : ℤ => ((g.coeff m : ℚ) : ℂ) * 𝕢 ℓ (τ : ℂ) ^ m) (F (ModularGroup.S • τ)))
  (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma0 ℓ, ∀ τ : ℍ, F (γ • τ) = F τ)

lemma realL_jtN_S : RealL ℓ (coeffMap castC jq) (fun τ => jtN ℓ (ModularGroup.S • τ)) := by
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  intro τ

  have hpt : ModularForm.heckeDiagMatrix ℓ • ModularGroup.S • τ = ModularGroup.S • ModularForm.heckeMatrix ℓ 0 • τ := by
    have h := heckeDiag_smul_S_T_pow_smul ℓ 0 τ
    rwa [pow_zero, mul_one] at h
  have h := hasSum_qParam_heckeMatrix_smul ℓ 0 (coeffMap castC jq) jt realL_jqC τ
  have hval : jtN ℓ (ModularGroup.S • τ) = jt (ModularForm.heckeMatrix ℓ 0 • τ) := by
    simp only [jtN]
    rw [hpt]
    exact E4_cube_div_discriminant_smul ModularGroup.S _
  change HasSum _ (jtN ℓ (ModularGroup.S • τ))
  rw [hval]
  refine h.congr_fun fun m => ?_
  simp

lemma realL_sum_qExpand_mul_jq_pow (n : ℕ) (ξ : ℕ → LaurentSeries ℚ) (Ξ : ℕ → ℍ → ℂ)
    (hξ : ∀ k, RealL 1 (coeffMap castC (ξ k)) (Ξ k)) (hΞ : ∀ k (γ : SL(2, ℤ)) τ, Ξ k (γ • τ) = Ξ k τ) :
    RealL ℓ (coeffMap castC (∑ k ∈ Finset.range n, qExpand ℚ ℓ (ξ k) * jq ^ k))
      (fun τ => ∑ k ∈ Finset.range n, Ξ k (ModularGroup.S • τ) * jtN ℓ (ModularGroup.S • τ) ^ k) := by
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ.out.pos
  have hk : ∀ k ∈ Finset.range n, RealL ℓ (coeffMap castC (qExpand ℚ ℓ (ξ k) * jq ^ k))
      (fun τ => Ξ k (ModularGroup.S • τ) * jtN ℓ (ModularGroup.S • τ) ^ k) := by
    intro k _
    have h1 : RealL ℓ (coeffMap castC (qExpand ℚ ℓ (ξ k))) (fun τ => Ξ k (ModularGroup.S • τ)) := by
      have h := realL_qExpand_of_realL_one ℓ _ _ (hξ k)
      refine h.congr (coeffMap_qExpand _ _ _).symm fun τ => (hΞ k ModularGroup.S τ).symm
    have h2 : RealL ℓ (coeffMap castC (jq ^ k)) (fun τ => jtN ℓ (ModularGroup.S • τ) ^ k) := by
      have h := RealL.prod hℓpos (Finset.range k) (fun _ _ => realL_jtN_S ℓ)
      refine h.congr ?_ fun τ => ?_
      · rw [Finset.prod_const, Finset.card_range, map_pow]
      · simp [Finset.prod_const, Finset.card_range]
    exact (h1.mul hℓpos h2).congr (map_mul _ _ _).symm fun τ => rfl
  exact (RealL.sum (Finset.range n) hk).congr (map_sum _ _ _).symm fun τ => rfl

lemma coeffMap_castC_injective : Function.Injective (coeffMap castC : LaurentSeries ℚ → LaurentSeries ℂ) := by
  intro x y h
  ext m
  have hm := congrArg (fun z : LaurentSeries ℂ => z.coeff m) h
  simp only [coeffMap_coeff] at hm
  exact castC.injective hm

def embW (w : modularFunctionFieldFull ℓ ≃ₐ[ℚ] modularFunctionFieldFull ℓ) :
    modularFunctionFieldFull ℓ →+* LaurentSeries ℚ :=
  (algebraMap (modularFunctionFieldFull ℓ) (LaurentSeries ℚ)).comp (w : modularFunctionFieldFull ℓ →+* modularFunctionFieldFull ℓ)

omit hℓ in
lemma embW_apply (w : modularFunctionFieldFull ℓ ≃ₐ[ℚ] modularFunctionFieldFull ℓ) (x : modularFunctionFieldFull ℓ) :
    embW ℓ w x = ((w x : modularFunctionFieldFull ℓ) : LaurentSeries ℚ) := rfl

lemma embW_of_mem_adjoin (w : modularFunctionFieldFull ℓ ≃ₐ[ℚ] modularFunctionFieldFull ℓ)
    (hw : IsFrickeAutFull ℓ w) (ξ : LaurentSeries ℚ) (hξ : ξ ∈ Algebra.adjoin ℚ {jq})
    (hξ' : ξ ∈ modularFunctionFieldFull ℓ) : embW ℓ w ⟨ξ, hξ'⟩ = qExpand ℚ ℓ ξ := by
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  revert hξ'
  induction hξ using Algebra.adjoin_induction with
  | mem x hx =>
    intro hξ'
    rw [Set.mem_singleton_iff] at hx
    subst hx

    have h := hw 1 ℓ (one_mul ℓ) inferInstance inferInstance
    have h1 : (⟨qExpand ℚ 1 jq, jqd_mem_full ℓ (Dvd.intro ℓ (one_mul ℓ))⟩ : modularFunctionFieldFull ℓ) =
        ⟨jq, hξ'⟩ := Subtype.ext (qExpand_one_apply jq)
    rw [h1] at h
    rw [embW_apply, h]
  | algebraMap r =>
    intro hξ'

    have hR : qExpand ℚ ℓ (algebraMap ℚ (LaurentSeries ℚ) r) = algebraMap ℚ (LaurentSeries ℚ) r :=
      RingHom.congr_fun (RingHom.ext_rat ((qExpand ℚ ℓ).comp (algebraMap ℚ (LaurentSeries ℚ)))
        (algebraMap ℚ (LaurentSeries ℚ))) r
    let χ : ℚ →+* modularFunctionFieldFull ℓ := (algebraMap ℚ (LaurentSeries ℚ)).codRestrict
      (modularFunctionFieldFull ℓ) (fun x => IntermediateField.algebraMap_mem _ x)
    have hχ : χ = algebraMap ℚ (modularFunctionFieldFull ℓ) := RingHom.ext_rat _ _
    have he : (⟨algebraMap ℚ (LaurentSeries ℚ) r, hξ'⟩ : modularFunctionFieldFull ℓ) =
        algebraMap ℚ (modularFunctionFieldFull ℓ) r := by
      rw [← hχ]; rfl
    have hval : ((algebraMap ℚ (modularFunctionFieldFull ℓ) r : modularFunctionFieldFull ℓ) : LaurentSeries ℚ) =
        algebraMap ℚ (LaurentSeries ℚ) r := by
      rw [← he]
    rw [hR, he, embW_apply, AlgEquiv.commutes, hval]
  | add x y hx hy ihx ihy =>
    intro hξ'
    have hx' : x ∈ modularFunctionFieldFull ℓ := (Algebra.adjoin_le (S := (modularFunctionFieldFull ℓ).toSubalgebra)
      (Set.singleton_subset_iff.mpr (jq_mem_full ℓ))) hx
    have hy' : y ∈ modularFunctionFieldFull ℓ := (Algebra.adjoin_le (S := (modularFunctionFieldFull ℓ).toSubalgebra)
      (Set.singleton_subset_iff.mpr (jq_mem_full ℓ))) hy
    have : (⟨x + y, hξ'⟩ : modularFunctionFieldFull ℓ) = ⟨x, hx'⟩ + ⟨y, hy'⟩ := rfl
    rw [this, map_add, map_add, ihx hx', ihy hy']
  | mul x y hx hy ihx ihy =>
    intro hξ'
    have hx' : x ∈ modularFunctionFieldFull ℓ := (Algebra.adjoin_le (S := (modularFunctionFieldFull ℓ).toSubalgebra)
      (Set.singleton_subset_iff.mpr (jq_mem_full ℓ))) hx
    have hy' : y ∈ modularFunctionFieldFull ℓ := (Algebra.adjoin_le (S := (modularFunctionFieldFull ℓ).toSubalgebra)
      (Set.singleton_subset_iff.mpr (jq_mem_full ℓ))) hy
    have : (⟨x * y, hξ'⟩ : modularFunctionFieldFull ℓ) = ⟨x, hx'⟩ * ⟨y, hy'⟩ := rfl
    rw [this, map_mul, map_mul, ihx hx', ihy hy']

include hζ hσ hF hG hinv in

theorem fricke_transport (w : modularFunctionFieldFull ℓ ≃ₐ[ℚ] modularFunctionFieldFull ℓ)
    (hw : IsFrickeAutFull ℓ w) (hf : f ∈ modularFunctionFieldFull ℓ) :
    ((w ⟨f, hf⟩ : modularFunctionFieldFull ℓ) : LaurentSeries ℚ) = g := by
  classical
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ.out.pos
  have hadj : Algebra.adjoin ℚ {jq} ≤ (modularFunctionFieldFull ℓ).toSubalgebra :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr (jq_mem_full ℓ))
  have hFle := modularFunctionField_le_full ℓ

  choose ξ hξ using fun k => exists_interpK_coeff_eq ℓ ζ hζ f g k
  have h1F : ∀ τ : ℍ, HasSum (fun m : ℤ => (((1 : LaurentSeries ℚ).coeff m : ℚ) : ℂ) * 𝕢 1 (τ : ℂ) ^ m)
      ((fun _ : ℍ => (1 : ℂ)) τ) := by
    intro τ; have h := RealL.one 1 τ; rw [← map_one (coeffMap castC)] at h; exact h
  have h1G : ∀ τ : ℍ, HasSum (fun m : ℤ => (((1 : LaurentSeries ℚ).coeff m : ℚ) : ℂ) * 𝕢 ℓ (τ : ℂ) ^ m)
      ((fun _ : ℍ => (1 : ℂ)) (ModularGroup.S • τ)) := by
    intro τ; have h := RealL.one (ℓ : ℝ) τ; rw [← map_one (coeffMap castC)] at h; exact h
  have h1inv : ∀ γ ∈ CongruenceSubgroup.Gamma0 ℓ, ∀ τ : ℍ, (fun _ : ℍ => (1 : ℂ)) (γ • τ) = (fun _ : ℍ => (1 : ℂ)) τ :=
    fun _ _ _ => rfl
  choose ξ1 hξ1 using fun k => exists_interpK_coeff_eq ℓ ζ hζ (1 : LaurentSeries ℚ) 1 k
  have hξmem : ∀ k, ξ k ∈ Algebra.adjoin ℚ {jq} := fun k =>
    mem_adjoin_of_interpK_coeff_eq ℓ ζ σ hσ f g F hF hG hinv k (ξ k) (hξ k)
  have hξ1mem : ∀ k, ξ1 k ∈ Algebra.adjoin ℚ {jq} := fun k =>
    mem_adjoin_of_interpK_coeff_eq ℓ ζ σ hσ 1 1 (fun _ => 1) h1F h1G h1inv k (ξ1 k) (hξ1 k)

  have hreal : ∀ k, RealL 1 (coeffMap castC (ξ k)) (interpFun ℓ F k) := by
    intro k
    have h := RealL.interpPoly_coeff (h := (ℓ : ℝ)) hℓpos
      (fun i => realL_slotH ℓ ζ σ hσ f g F hF hG i) (fun i => realL_conj ℓ ζ σ hσ i) k
    have h' : RealL ℓ (coeffMap σ ((interpK ℓ ζ f g).coeff k)) (interpFun ℓ F k) := by
      refine h.congr ?_ fun τ => rfl
      rw [← Polynomial.coeff_map, interpK, interpPoly_map]; rfl
    rw [hξ k, coeffMap_sigma_coeffEmb, coeffMap_qExpand] at h'
    exact realL_one_of_realL_qExpand ℓ _ _ h'
  have hreal1 : ∀ k, RealL 1 (coeffMap castC (ξ1 k)) (interpFun ℓ (fun _ => (1 : ℂ)) k) := by
    intro k
    have h := RealL.interpPoly_coeff (h := (ℓ : ℝ)) hℓpos
      (fun i => realL_slotH ℓ ζ σ hσ 1 1 (fun _ => (1 : ℂ)) h1F h1G i) (fun i => realL_conj ℓ ζ σ hσ i) k
    have h' : RealL ℓ (coeffMap σ ((interpK ℓ ζ (1 : LaurentSeries ℚ) 1).coeff k)) (interpFun ℓ (fun _ => (1 : ℂ)) k) := by
      refine h.congr ?_ fun τ => rfl
      rw [← Polynomial.coeff_map, interpK, interpPoly_map]; rfl
    rw [hξ1 k, coeffMap_sigma_coeffEmb, coeffMap_qExpand] at h'
    exact realL_one_of_realL_qExpand ℓ _ _ h'

  set x : LaurentSeries ℚ := ∑ k ∈ Finset.range (ℓ + 1), ξ k * jqN ℓ ^ k with hx
  set d : LaurentSeries ℚ := ∑ k ∈ Finset.range (ℓ + 1), ξ1 k * jqN ℓ ^ k with hd
  set x' : LaurentSeries ℚ := ∑ k ∈ Finset.range (ℓ + 1), qExpand ℚ ℓ (ξ k) * jq ^ k with hx'
  set d' : LaurentSeries ℚ := ∑ k ∈ Finset.range (ℓ + 1), qExpand ℚ ℓ (ξ1 k) * jq ^ k with hd'
  have hxmem : x ∈ modularFunctionFieldFull ℓ :=
    sum_mem fun k _ => mul_mem (hadj (hξmem k)) (pow_mem (hFle (jqN_mem ℓ)) k)
  have hdmem : d ∈ modularFunctionFieldFull ℓ :=
    sum_mem fun k _ => mul_mem (hadj (hξ1mem k)) (pow_mem (hFle (jqN_mem ℓ)) k)

  have hιx : iota (K := K) ℓ x = iota ℓ f * dHat ℓ ζ := by
    have hdeg : (interpK ℓ ζ f g).natDegree < ℓ + 1 := natDegree_interpPoly_lt _ _
    rw [hx, map_sum]
    simp only [map_mul, map_pow, iota_jqN ℓ ζ, iota_apply, ← hξ]
    rw [← Polynomial.eval_eq_sum_range' hdeg, interpK, interpPoly_eval, ← slotH_zero ℓ ζ f g, dHat]
  have hιd : iota (K := K) ℓ d = dHat ℓ ζ := by
    have hdeg : (interpK ℓ ζ (1 : LaurentSeries ℚ) 1).natDegree < ℓ + 1 := natDegree_interpPoly_lt _ _
    rw [hd, map_sum]
    simp only [map_mul, map_pow, iota_jqN ℓ ζ, iota_apply, ← hξ1]
    rw [← Polynomial.eval_eq_sum_range' hdeg, interpK, interpPoly_eval, dHat, slotH_zero, map_one, map_one, one_mul]
  have hd0 : d ≠ 0 := by
    intro h0; exact dHat_ne_zero ℓ ζ hζ (by rw [h0, map_zero] at hιd; exact hιd.symm)
  have hfd : f * d = x := iota_injective (K := K) ℓ (by rw [map_mul, hιd, hιx])

  have hwx : embW ℓ w ⟨x, hxmem⟩ = x' := by
    have : (⟨x, hxmem⟩ : modularFunctionFieldFull ℓ) =
        ∑ k ∈ Finset.range (ℓ + 1), ⟨ξ k, hadj (hξmem k)⟩ * ⟨jqN ℓ, hFle (jqN_mem ℓ)⟩ ^ k := by
      apply Subtype.ext
      simp only [hx]
      push_cast
      rfl
    rw [this, map_sum, hx']
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, map_pow, embW_of_mem_adjoin ℓ w hw (ξ k) (hξmem k)]
    congr 1
    have h := hw ℓ 1 (mul_one ℓ) inferInstance inferInstance
    have h1 : (⟨qExpand ℚ 1 jq, jqd_mem_full ℓ (Dvd.intro_left ℓ (mul_one ℓ))⟩ : modularFunctionFieldFull ℓ) =
        ⟨jq, jq_mem_full ℓ⟩ := Subtype.ext (qExpand_one_apply jq)
    have h2 : (⟨qExpand ℚ ℓ jq, jqd_mem_full ℓ (Dvd.intro 1 (mul_one ℓ))⟩ : modularFunctionFieldFull ℓ) =
        ⟨jqN ℓ, hFle (jqN_mem ℓ)⟩ := Subtype.ext rfl
    rw [h1, h2] at h
    rw [embW_apply, h]
  have hwd : embW ℓ w ⟨d, hdmem⟩ = d' := by
    have : (⟨d, hdmem⟩ : modularFunctionFieldFull ℓ) =
        ∑ k ∈ Finset.range (ℓ + 1), ⟨ξ1 k, hadj (hξ1mem k)⟩ * ⟨jqN ℓ, hFle (jqN_mem ℓ)⟩ ^ k := by
      apply Subtype.ext
      simp only [hd]
      push_cast
      rfl
    rw [this, map_sum, hd']
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, map_pow, embW_of_mem_adjoin ℓ w hw (ξ1 k) (hξ1mem k)]
    congr 1
    have h := hw ℓ 1 (mul_one ℓ) inferInstance inferInstance
    have h1 : (⟨qExpand ℚ 1 jq, jqd_mem_full ℓ (Dvd.intro_left ℓ (mul_one ℓ))⟩ : modularFunctionFieldFull ℓ) =
        ⟨jq, jq_mem_full ℓ⟩ := Subtype.ext (qExpand_one_apply jq)
    have h2 : (⟨qExpand ℚ ℓ jq, jqd_mem_full ℓ (Dvd.intro 1 (mul_one ℓ))⟩ : modularFunctionFieldFull ℓ) =
        ⟨jqN ℓ, hFle (jqN_mem ℓ)⟩ := Subtype.ext rfl
    rw [h1, h2] at h
    rw [embW_apply, h]

  have hXpt : ∀ (Φ : ℍ → ℂ) (τ : ℍ), ∑ k ∈ Finset.range (ℓ + 1), interpFun ℓ Φ k τ * jtN ℓ τ ^ k =
      Φ τ * ∏ m ∈ Finset.univ.erase (0 : Fin (ℓ + 1)), (slotJ ℓ 0 τ - slotJ ℓ m τ) := by
    intro Φ τ
    have h1 := interpPoly_eval (fun i => slotF ℓ Φ i τ) (fun i => slotJ ℓ i τ) 0
    have h2 := Polynomial.eval_eq_sum_range'
      (natDegree_interpPoly_lt (fun i => slotF ℓ Φ i τ) (fun i => slotJ ℓ i τ)) ((fun i => slotJ ℓ i τ) 0)
    simp only [] at h1 h2
    have h0 : slotJ ℓ 0 τ = jtN ℓ τ := by simp [slotJ]
    have hF0 : slotF ℓ Φ 0 τ = Φ τ := by simp [slotF]
    simp only [interpFun]
    rw [← h0, ← h2, h1, hF0]
  have hrx' : RealL ℓ (coeffMap castC x') (fun τ => F (ModularGroup.S • τ) *
      ∏ m ∈ Finset.univ.erase (0 : Fin (ℓ + 1)), (slotJ ℓ 0 (ModularGroup.S • τ) - slotJ ℓ m (ModularGroup.S • τ))) := by
    have h := realL_sum_qExpand_mul_jq_pow ℓ (ℓ + 1) ξ (fun k => interpFun ℓ F k) hreal
      (fun k γ τ => interpFun_smul ℓ F hinv k γ τ)
    exact h.congr rfl fun τ => hXpt F (ModularGroup.S • τ)
  have hrd' : RealL ℓ (coeffMap castC d') (fun τ =>
      ∏ m ∈ Finset.univ.erase (0 : Fin (ℓ + 1)), (slotJ ℓ 0 (ModularGroup.S • τ) - slotJ ℓ m (ModularGroup.S • τ))) := by
    have h := realL_sum_qExpand_mul_jq_pow ℓ (ℓ + 1) ξ1 (fun k => interpFun ℓ (fun _ => (1 : ℂ)) k) hreal1
      (fun k γ τ => interpFun_smul ℓ (fun _ => (1 : ℂ)) h1inv k γ τ)
    refine h.congr rfl fun τ => ?_
    rw [hXpt (fun _ => (1 : ℂ)) (ModularGroup.S • τ), one_mul]
  have hrg : RealL ℓ (coeffMap castC g) (fun τ => F (ModularGroup.S • τ)) := fun τ => hG τ
  have hx'gd : x' = g * d' := by
    apply coeffMap_castC_injective
    rw [map_mul]
    exact laurent_qParam_coeff_unique ℓ hℓpos _ _ _ hrx' (hrg.mul hℓpos hrd')

  have hd'0 : d' ≠ 0 := by
    rw [← hwd, embW_apply]
    intro h0
    apply hd0
    have : (w ⟨d, hdmem⟩ : modularFunctionFieldFull ℓ) = 0 := Subtype.ext h0
    have := w.injective (this.trans (map_zero w).symm)
    exact congrArg Subtype.val this
  have hprod : (⟨f, hf⟩ : modularFunctionFieldFull ℓ) * ⟨d, hdmem⟩ = ⟨x, hxmem⟩ := Subtype.ext hfd
  have key : embW ℓ w ⟨f, hf⟩ * d' = g * d' := by
    rw [← hx'gd, ← hwx, ← hprod, map_mul, hwd]
  have := mul_right_cancel₀ hd'0 key
  rwa [embW_apply] at this


end QExpN

/-! ## The first two M8 headlines -/

theorem mem_modularFunctionField_of_hasSum_of_gamma0_invariant (ℓ : ℕ) [Fact (Nat.Prime ℓ)]
    (f g : LaurentSeries ℚ) (F : UpperHalfPlane → ℂ)
    (hF : ∀ τ : UpperHalfPlane, HasSum (fun m : ℤ => ((f.coeff m : ℚ) : ℂ) *
      Function.Periodic.qParam 1 (τ : ℂ) ^ m) (F τ))
    (hG : ∀ τ : UpperHalfPlane, HasSum (fun m : ℤ => ((g.coeff m : ℚ) : ℂ) *
      Function.Periodic.qParam ℓ (τ : ℂ) ^ m) (F (ModularGroup.S • τ)))
    (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma0 ℓ, ∀ τ : UpperHalfPlane, F (γ • τ) = F τ) :
    f ∈ modularFunctionField ℓ :=
  QExpN.mem_modularFunctionField ℓ f g F hF hG hinv

theorem isIntegral_adjoin_jq_of_hasSum_of_gamma0_invariant (ℓ : ℕ) [Fact (Nat.Prime ℓ)]
    (f g : LaurentSeries ℚ) (F : UpperHalfPlane → ℂ)
    (hF : ∀ τ : UpperHalfPlane, HasSum (fun m : ℤ => ((f.coeff m : ℚ) : ℂ) *
      Function.Periodic.qParam 1 (τ : ℂ) ^ m) (F τ))
    (hG : ∀ τ : UpperHalfPlane, HasSum (fun m : ℤ => ((g.coeff m : ℚ) : ℂ) *
      Function.Periodic.qParam ℓ (τ : ℂ) ^ m) (F (ModularGroup.S • τ)))
    (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma0 ℓ, ∀ τ : UpperHalfPlane, F (γ • τ) = F τ) :
    IsIntegral (Algebra.adjoin ℚ {jq}) f :=
  QExpN.isIntegral_adjoin_jq ℓ f g F hF hG hinv

/-! ## The small `modularUnitSeries` targets -/

theorem modularUnitSeries_mem_modularFunctionField (ℓ : ℕ) [Fact (Nat.Prime ℓ)] :
    modularUnitSeries ℓ ∈ modularFunctionField ℓ := by
  have : NeZero ℓ := ⟨(Fact.out : Nat.Prime ℓ).ne_zero⟩
  exact mem_modularFunctionField_of_hasSum_of_gamma0_invariant ℓ
    (modularUnitSeries ℓ) ((ℓ : ℚ) ^ 12 • (modularUnitSeries ℓ)⁻¹)
    (fun τ => ModularForm.discriminant τ
      / ModularForm.discriminant (ModularForm.heckeDiagMatrix ℓ • τ))
    (fun τ => hasSum_modularUnitSeries_qParam ℓ τ)
    (fun τ => hasSum_smul_modularUnitSeries_inv_qParam ℓ τ)
    (fun γ hγ τ => discriminant_div_discriminant_heckeDiagMatrix_smul ℓ γ hγ τ)

theorem modularUnitSeries_mem_modularFunctionFieldFull (N : ℕ) [NeZero N] :
    modularUnitSeries N ∈ modularFunctionFieldFull N := by
  suffices H : ∀ n : ℕ, ∀ _ : NeZero n,
      modularUnitSeries n ∈ modularFunctionFieldFull n from
    H N ‹NeZero N›
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hNZ
    have := hNZ
    have hn : n ≠ 0 := NeZero.ne n
    rcases eq_or_ne n 1 with rfl | hn1
    · rw [modularUnitSeries_one]
      exact one_mem _
    · obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd hn1
      obtain ⟨M, rfl⟩ := hdvd
      have hM : M ≠ 0 := by rintro rfl; exact hn (mul_zero p)
      have hp0 : p ≠ 0 := hp.ne_zero
      have : NeZero p := ⟨hp0⟩
      have : NeZero M := ⟨hM⟩
      have : NeZero (p * M) := ⟨mul_ne_zero hp0 hM⟩
      have : Fact p.Prime := ⟨hp⟩
      rw [modularUnitSeries_mul p M]
      refine mul_mem ?_ ?_
      · exact full_degeneracy_le (dvd_mul_right p M)
          (modularFunctionField_le_full p (modularUnitSeries_mem_modularFunctionField p))
      · have hMlt : M < p * M :=
          (lt_mul_iff_one_lt_left (Nat.pos_of_ne_zero hM)).mpr hp.one_lt
        have hmem := ih M hMlt ⟨hM⟩
        have h2 : qExpandₐ p (modularUnitSeries M)
            ∈ (modularFunctionFieldFull M).map (qExpandₐ p) :=
          ⟨_, hmem, rfl⟩
        have h3 := full_degeneracy_map_le M p h2
        rw [qExpandₐ_apply] at h3
        exact full_degeneracy_le (dvd_of_eq (mul_comm M p)) h3

theorem isIntegral_adjoin_jq_modularUnitSeries (ℓ : ℕ) [Fact (Nat.Prime ℓ)] :
    IsIntegral (Algebra.adjoin ℚ {jq}) (modularUnitSeries ℓ) := by
  have : NeZero ℓ := ⟨(Fact.out : Nat.Prime ℓ).ne_zero⟩
  exact isIntegral_adjoin_jq_of_hasSum_of_gamma0_invariant ℓ
    (modularUnitSeries ℓ) ((ℓ : ℚ) ^ 12 • (modularUnitSeries ℓ)⁻¹)
    (fun τ => ModularForm.discriminant τ
      / ModularForm.discriminant (ModularForm.heckeDiagMatrix ℓ • τ))
    (fun τ => hasSum_modularUnitSeries_qParam ℓ τ)
    (fun τ => hasSum_smul_modularUnitSeries_inv_qParam ℓ τ)
    (fun γ hγ τ => discriminant_div_discriminant_heckeDiagMatrix_smul ℓ γ hγ τ)

theorem isIntegral_adjoin_jq_modularUnitSeries_inv (ℓ : ℕ) [Fact (Nat.Prime ℓ)] :
    IsIntegral (Algebra.adjoin ℚ {jq}) (modularUnitSeries ℓ)⁻¹ := by
  have : NeZero ℓ := ⟨(Fact.out : Nat.Prime ℓ).ne_zero⟩
  refine isIntegral_adjoin_jq_of_hasSum_of_gamma0_invariant ℓ
    (modularUnitSeries ℓ)⁻¹ (((ℓ : ℚ) ^ 12)⁻¹ • modularUnitSeries ℓ)
    (fun τ => ModularForm.discriminant (ModularForm.heckeDiagMatrix ℓ • τ)
      / ModularForm.discriminant τ)
    (fun τ => hasSum_modularUnitSeries_inv_qParam ℓ τ)
    (fun τ => hasSum_smul_modularUnitSeries_qParam ℓ τ)
    (fun γ hγ τ => ?_)
  show ModularForm.discriminant (ModularForm.heckeDiagMatrix ℓ • γ • τ)
      / ModularForm.discriminant (γ • τ)
    = ModularForm.discriminant (ModularForm.heckeDiagMatrix ℓ • τ) / ModularForm.discriminant τ
  have h := congrArg Inv.inv
    (discriminant_div_discriminant_heckeDiagMatrix_smul ℓ γ hγ τ)
  rwa [inv_div, inv_div] at h

end ModularCurve
