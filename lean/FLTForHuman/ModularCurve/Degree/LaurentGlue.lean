/-
  m7 (first half) — the Laurent/`coeffEmb` glue: the eight short M4 nodes.

  These are the `coeffEmb`/`order`/`adjoin` bridges the relative-degree and roof
  arguments rewrite through. Everything here is transcribed from the pin's
  `P2M/Sol/S_ModularCurve_<node>.lean` `solution` (the `Theorems/` wrapper is the
  statement authority); the pin's private helpers are not written because the
  port already publishes their generic forms:
  `coeffMap_qExpand`/`coeffEmb_qExpand` (`Defs/Laurent.lean`, m1) replace the
  pin's local `map_qExpand_aux` and `CharLRows.coeffEmb_jq`.

  The two `order_*` nodes are also proved `private` inside
  `Analytic/CuspBookkeeping.lean` (m5, which could not import them yet); the
  public statements here are the wrapper targets and are the promoted home.

  FLT provenance, pinned `aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_coeffEmb_jq.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_coeffEmb_jqN.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_order_qExpand.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_order_coeffEmb.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_laurentBaseChange_adjoin.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_laurentBaseChange_modularFunctionField.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_laurentBaseChange_modularFunctionFieldFull.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_transcendental_jqN.lean
-/
import FLTForHuman.ModularCurve.Defs.Laurent
import FLTForHuman.ModularCurve.Defs.JqCoeff
import Mathlib.RingTheory.LaurentSeries

set_option autoImplicit false

noncomputable section

open HahnSeries IntermediateField Polynomial

namespace ModularCurve

/-! ## The `coeffEmb` bridges -/

theorem coeffEmb_jq (L : Type*) [Field L] [Algebra ℚ L] :
    coeffEmb L jq = jqModC L := by
  rw [← jqModC_rat]
  exact map_jqModC (algebraMap ℚ L)

theorem coeffEmb_jqN (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N] :
    coeffEmb L (jqN N) = jqNModC L N := by
  rw [jqN, jqNModC, coeffEmb_qExpand, coeffEmb_jq]

/-! ## The order computations -/

theorem order_qExpand {R : Type*} [CommRing R] (N : ℕ) [NeZero N] (f : LaurentSeries R) :
    (qExpand R N f).order = N * f.order := by
  rcases eq_or_ne f 0 with rfl | hf
  · rw [map_zero, HahnSeries.order_zero, mul_zero]
  have hc : (qExpand R N f).coeff ((N : ℤ) * f.order) ≠ 0 := by
    rw [qExpand_coeff_mul]
    exact HahnSeries.coeff_order_eq_zero.not.mpr hf
  have hne : qExpand R N f ≠ 0 := fun h0 => hc (by rw [h0]; rfl)
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hc) ?_
  by_contra! hlt
  have hk := HahnSeries.coeff_order_eq_zero.not.mpr hne
  by_cases hdvd : (N : ℤ) ∣ (qExpand R N f).order
  · obtain ⟨m, hm⟩ := hdvd
    rw [hm, qExpand_coeff_mul] at hk
    have hNpos : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    have hmlt : m < f.order := by
      rw [hm] at hlt
      exact lt_of_mul_lt_mul_left hlt hNpos.le
    exact hk (HahnSeries.coeff_eq_zero_of_lt_order hmlt)
  · exact hk (qExpand_coeff_of_not_dvd N f hdvd)

theorem order_coeffEmb (L : Type*) [Field L] [Algebra ℚ L] (x : LaurentSeries ℚ) :
    (coeffEmb L x).order = x.order := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero, HahnSeries.order_zero, HahnSeries.order_zero]
  have hLx : coeffEmb L x ≠ 0 := by
    intro h0
    have h1 : (coeffEmb L x).coeff x.order = 0 := by rw [h0]; rfl
    rw [coeffEmb_coeff, map_eq_zero_iff _ (algebraMap ℚ L).injective] at h1
    exact HahnSeries.coeff_order_eq_zero.not.mpr hx h1
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero ?_)
    (HahnSeries.order_le_of_coeff_ne_zero ?_)
  · rw [coeffEmb_coeff]
    exact fun h => HahnSeries.coeff_order_eq_zero.not.mpr hx
      ((map_eq_zero_iff _ (algebraMap ℚ L).injective).mp h)
  · intro h
    exact HahnSeries.coeff_order_eq_zero.not.mpr hLx (by rw [coeffEmb_coeff, h, map_zero])

/-! ## Base change of adjoins -/

theorem laurentBaseChange_adjoin (L : Type*) [Field L] [Algebra ℚ L]
    (S : Set (LaurentSeries ℚ)) :
    laurentBaseChange L (IntermediateField.adjoin ℚ S) =
      IntermediateField.adjoin L (coeffEmb L '' S) := by
  apply le_antisymm
  · rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, hy, rfl⟩
    have hle : (IntermediateField.adjoin ℚ S).toSubfield ≤
        (IntermediateField.adjoin L (coeffEmb L '' S)).toSubfield.comap (coeffEmb L) := by
      rw [IntermediateField.adjoin_toSubfield]
      refine Subfield.closure_le.mpr ?_
      rintro x (⟨c, rfl⟩ | hx)
      · rw [SetLike.mem_coe, Subfield.mem_comap]
        have : coeffEmb L (algebraMap ℚ (LaurentSeries ℚ) c)
            = algebraMap L (LaurentSeries L) (algebraMap ℚ L c) := by
          rw [algebraMap_apply_eq_single, coeffEmb, coeffMap_single,
            ← algebraMap_laurentSeries_eq_single]
        rw [this]
        exact (IntermediateField.adjoin L (coeffEmb L '' S)).algebraMap_mem _
      · rw [SetLike.mem_coe, Subfield.mem_comap]
        exact IntermediateField.subset_adjoin L _ ⟨x, hx, rfl⟩
    exact hle hy
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, hy, rfl⟩
    exact coeffEmb_mem_laurentBaseChange L (IntermediateField.subset_adjoin ℚ S hy)

theorem laurentBaseChange_modularFunctionField (L : Type*) [Field L] [Algebra ℚ L]
    (N : ℕ) [NeZero N] :
    laurentBaseChange L (modularFunctionField N) = modularFunctionFieldC L N := by
  apply le_antisymm
  · change IntermediateField.adjoin L (⇑(coeffEmb L) '' (modularFunctionField N : Set (LaurentSeries ℚ)))
      ≤ modularFunctionFieldC L N
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, hx, rfl⟩
    change x ∈ IntermediateField.adjoin ℚ {jq, qExpand ℚ N jq} at hx
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx =>
        rcases hx with rfl | rfl
        · rw [coeffEmb_jq]; exact jqModC_mem L N
        · rw [show qExpand ℚ N jq = jqN N from rfl, coeffEmb_jqN]; exact jqNModC_mem L N
    | algebraMap c =>
        have h : (coeffEmb L).comp (algebraMap ℚ (LaurentSeries ℚ))
            = (algebraMap L (LaurentSeries L)).comp (algebraMap ℚ L) := RingHom.ext_rat _ _
        have hc := congrArg (fun f : ℚ →+* LaurentSeries L => f c) h
        simp only [RingHom.coe_comp, Function.comp_apply] at hc
        simp only [SetLike.mem_coe, hc]
        exact (modularFunctionFieldC L N).algebraMap_mem _
    | add x y _ _ hx hy => simpa only [SetLike.mem_coe, map_add] using add_mem hx hy
    | inv x _ hx => simpa only [SetLike.mem_coe, map_inv₀] using inv_mem hx
    | mul x y _ _ hx hy => simpa only [SetLike.mem_coe, map_mul] using mul_mem hx hy
  · change IntermediateField.adjoin L {jqModC L, jqNModC L N}
      ≤ IntermediateField.adjoin L (⇑(coeffEmb L) '' (modularFunctionField N : Set (LaurentSeries ℚ)))
    apply IntermediateField.adjoin.mono
    rintro _ (rfl | rfl)
    · exact ⟨jq, jq_mem N, coeffEmb_jq L⟩
    · exact ⟨qExpand ℚ N jq, jqN_mem N, coeffEmb_jqN L N⟩

theorem laurentBaseChange_modularFunctionFieldFull (L : Type*) [Field L] [Algebra ℚ L]
    (N : ℕ) [NeZero N] :
    laurentBaseChange L (modularFunctionFieldFull N) =
      IntermediateField.adjoin L {x | ∃ (d : ℕ) (_ : NeZero d), d ∣ N ∧ x = jqNModC L d} := by
  rw [modularFunctionFieldFull, laurentBaseChange_adjoin]
  congr 1
  ext x
  simp only [Set.mem_image, divisorExpansions, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨y, ⟨d, hd, hdvd, rfl⟩, rfl⟩
    exact ⟨d, hd, hdvd, (coeffEmb_jqN L d)⟩
  · rintro ⟨d, hd, hdvd, rfl⟩
    exact ⟨qExpand ℚ d jq, ⟨d, hd, hdvd, rfl⟩, coeffEmb_jqN L d⟩

/-! ## Transcendence of `jqN` -/

theorem transcendental_jqN (N : ℕ) [NeZero N] : Transcendental ℚ (jqN N) := by
  refine transcendental_iff.mpr fun p hp => ?_
  refine aeval_jq_eq_zero (p := p) (qExpand_injective N ?_)
  rw [map_zero]
  calc qExpand ℚ N (Polynomial.aeval jq p)
      = qExpandₐ N (Polynomial.aeval jq p) := rfl
    _ = Polynomial.aeval (qExpandₐ N jq) p := (Polynomial.aeval_algHom_apply _ _ _).symm
    _ = Polynomial.aeval (jqN N) p := rfl
    _ = 0 := hp

end ModularCurve

end
