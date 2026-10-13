/-
  The unramified local zeta: shells and the local measure.

  The uniformizer unit `piUnit`, the shells `shellSet hϖ k` of exact order `k`
  (the `ϖ ^ k`-multiples of the completed integers with nothing deeper), their
  compactness, openness and measurability, `mem_shellSet_iff_ord_eq` identifying a
  shell with a level set of `ValuationOrd.ord`, and
  `measure_integers_lt_top`.

  Transcribed from the pin's `M4aLocalCFT.LocalZetaUnramified` block, declared
  lines 1556–1719 of file A, pinned `aa2d8b3`:
  `https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean`

  Chapter-prefix rename (work order §3.1): `M4aLocalCFT.LocalZetaUnramified`
  becomes `NumberField.TateGlobal.LocalZetaUnramified`; the sub-namespace is kept.
  The pin's empty `Integrand`/`Zeta` sections are kept with their `variable`s.

  Build notes: the pin's `p2m_*` scaffolding is dropped; no file-wide option beyond
  `set_option autoImplicit false`.
-/
import FLTForHuman.NumberTheory.NumberField.TateGlobal.DistribHaarChar
-- the local modulus `modulus`/`mulMeasure` (pin `Def_LanglandsTunnell_TateLocalZeta.lean`),
-- consumed by `MulHaar`/`ArchMulHaar`; the pin's block opens `LanglandsTunnell.TateLocal`
-- here.
import FLTForHuman.LanglandsTunnell.TateLocalZeta

set_option autoImplicit false

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing NumberField
open NumberField.AdelicLevel MeasureTheory Set Filter Topology TopologicalSpace
open LanglandsTunnell.TateLocal
open scoped NNReal ENNReal Pointwise NumberField.TateGlobal

section Fold_LocalZetaUnramified

noncomputable section

namespace NumberField

namespace TateGlobal

namespace LocalZetaUnramified

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

section Shells

variable {ϖ : v.adicCompletionIntegers F}

-- pin: coe_ne_zero_of_irreducible (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1556)
theorem coe_ne_zero_of_irreducible (hϖ : Irreducible ϖ) :
    ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 0 :=
  fun h => hϖ.ne_zero (Subtype.ext h)

-- pin: piUnit (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1560)
def piUnit (hϖ : Irreducible ϖ) : (v.adicCompletion F)ˣ := Units.mk0 _ (coe_ne_zero_of_irreducible hϖ)

-- pin: piUnit_val (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1562)
@[scoped simp] theorem piUnit_val (hϖ : Irreducible ϖ) :
    ((piUnit hϖ : (v.adicCompletion F)ˣ) : v.adicCompletion F)
      = ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) := rfl

-- pin: ord_piUnit (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1566)
theorem ord_piUnit (hϖ : Irreducible ϖ) :
    ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul (piUnit hϖ)) = 1 :=
  ValuationOrd.ord_ofMul_mk0_of_irreducible _ hϖ _

-- pin: ord_piUnit_pow (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1570)
theorem ord_piUnit_pow (hϖ : Irreducible ϖ) (k : ℕ) :
    ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul ((piUnit hϖ) ^ k)) = k := by
  have h : Additive.ofMul ((piUnit hϖ) ^ k) = k • Additive.ofMul (piUnit hϖ) := rfl
  rw [h, map_nsmul, ord_piUnit]
  simp

-- pin: shellSet (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1576)
def shellSet (hϖ : Irreducible ϖ) (k : ℕ) : Set (v.adicCompletion F) :=
  (((piUnit hϖ ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F)
      • (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    \ (((piUnit hϖ ^ (k + 1) : (v.adicCompletion F)ˣ) : v.adicCompletion F)
      • (v.adicCompletionIntegers F : Set (v.adicCompletion F)))

-- pin: isCompact_integers (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1582)
theorem isCompact_integers :
    IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
  NumberField.isCompactAdicCompletionIntegers F v

-- pin: isCompact_smul_integers (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1586)
theorem isCompact_smul_integers (c : v.adicCompletion F) :
    IsCompact (c • (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
  have h := (isCompact_integers (F := F) (v := v)).image (continuous_const_smul c)
  rwa [Set.image_smul] at h

-- pin: measurableSet_smul_integers (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1591)
theorem measurableSet_smul_integers [MeasurableSpace (v.adicCompletion F)]
    [BorelSpace (v.adicCompletion F)] (c : v.adicCompletion F) :
    MeasurableSet (c • (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
  (isCompact_smul_integers c).isClosed.measurableSet

-- pin: measurableSet_shellSet (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1596)
theorem measurableSet_shellSet [MeasurableSpace (v.adicCompletion F)]
    [BorelSpace (v.adicCompletion F)] (hϖ : Irreducible ϖ) (k : ℕ) :
    MeasurableSet (shellSet hϖ k) :=
  (measurableSet_smul_integers _).diff (measurableSet_smul_integers _)

-- pin: mem_smul_integers_iff (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1601)
theorem mem_smul_integers_iff {c x : v.adicCompletion F} :
    x ∈ c • (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      ↔ ∃ y : v.adicCompletionIntegers F, c * (y : v.adicCompletion F) = x := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, (smul_eq_mul c y).symm⟩
  · rintro ⟨y, hy⟩
    exact ⟨(y : v.adicCompletion F), y.2, by show c • (y : v.adicCompletion F) = x; rw [smul_eq_mul]; exact hy⟩

-- pin: shellSet_subset_integers (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1610)
theorem shellSet_subset_integers (hϖ : Irreducible ϖ) (k : ℕ) :
    shellSet hϖ k ⊆ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  intro x hx
  obtain ⟨y, hy⟩ := mem_smul_integers_iff.mp hx.1
  rw [← hy]
  push_cast [piUnit_val]
  exact mul_mem (pow_mem ϖ.2 k) y.2

-- pin: zero_notMem_shellSet (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1618)
theorem zero_notMem_shellSet (hϖ : Irreducible ϖ) (k : ℕ) : (0 : v.adicCompletion F) ∉ shellSet hϖ k := by
  intro h
  exact h.2 (mem_smul_integers_iff.mpr ⟨0, by push_cast; ring⟩)

-- pin: mem_shellSet_iff_ord_eq (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1622)
theorem mem_shellSet_iff_ord_eq (hϖ : Irreducible ϖ) (k : ℕ) {x : v.adicCompletion F} (hx : x ≠ 0) :
    x ∈ shellSet hϖ k
      ↔ ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul (Units.mk0 x hx))
          = k := by
  constructor
  · intro hmem
    obtain ⟨y, hy⟩ := mem_smul_integers_iff.mp hmem.1
    have hy0 : (y : v.adicCompletion F) ≠ 0 := by
      intro h0
      exact hx (by rw [← hy, h0, mul_zero])
    have hyunit : IsUnit y := by
      by_contra hnu
      have hymem : y ∈ maximalIdeal (v.adicCompletionIntegers F) := hnu
      rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hymem
      obtain ⟨z, hz⟩ := hymem
      refine hmem.2 (mem_smul_integers_iff.mpr ⟨z, ?_⟩)
      rw [← hy, hz]
      push_cast [pow_succ, piUnit_val]
      ring
    obtain ⟨u, hu⟩ := hyunit
    have hxfac : Units.mk0 x hx
        = piUnit hϖ ^ k
          * Units.map ((v.adicCompletionIntegers F).subtype.toMonoidHom) u := by
      ext
      rw [Units.val_mk0, ← hy]
      push_cast [piUnit_val, Units.coe_map]
      rw [← hu]
      rfl
    have hordu : ValuationOrd.ord (v.adicCompletionIntegers F)
        (Additive.ofMul (Units.map ((v.adicCompletionIntegers F).subtype.toMonoidHom) u))
          = 0 :=
      (ValuationOrd.ord_eq_zero_iff _ _).mpr ⟨u, rfl⟩
    have hsplit : Additive.ofMul (Units.mk0 x hx)
        = Additive.ofMul (piUnit hϖ ^ k)
          + Additive.ofMul (Units.map ((v.adicCompletionIntegers F).subtype.toMonoidHom) u) := by
      rw [hxfac]; rfl
    rw [hsplit, map_add, hordu, add_zero, ord_piUnit_pow]
  · intro hord
    set w : (v.adicCompletion F)ˣ := Units.mk0 x hx * (piUnit hϖ ^ k)⁻¹ with hwdef
    have hword : ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul w) = 0 := by
      have hsub : Additive.ofMul w = Additive.ofMul (Units.mk0 x hx)
          - Additive.ofMul (piUnit hϖ ^ k) := rfl
      rw [hsub, map_sub, hord, ord_piUnit_pow, sub_self]
    obtain ⟨u, hu⟩ := (ValuationOrd.ord_eq_zero_iff _ _).mp hword
    have hxw : x = ((piUnit hϖ ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F)
        * ((w : (v.adicCompletion F)ˣ) : v.adicCompletion F) := by
      have hfac : Units.mk0 x hx = piUnit hϖ ^ k * w := by
        rw [hwdef, mul_comm (Units.mk0 x hx) ((piUnit hϖ ^ k)⁻¹), mul_inv_cancel_left]
      calc x = ((Units.mk0 x hx : (v.adicCompletion F)ˣ) : v.adicCompletion F) := rfl
        _ = ((piUnit hϖ ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F)
            * ((w : (v.adicCompletion F)ˣ) : v.adicCompletion F) := by
              rw [hfac, Units.val_mul]
    constructor
    · have hwmem : ((w : (v.adicCompletion F)ˣ) : v.adicCompletion F)
          ∈ v.adicCompletionIntegers F := by
        rw [← hu]
        exact ((u : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F).2
      exact mem_smul_integers_iff.mpr
        ⟨⟨((w : (v.adicCompletion F)ˣ) : v.adicCompletion F), hwmem⟩, hxw.symm⟩
    · intro hnext
      obtain ⟨z, hz⟩ := mem_smul_integers_iff.mp hnext
      have hcan : ((piUnit hϖ ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F)
          * ((w : (v.adicCompletion F)ˣ) : v.adicCompletion F)
          = ((piUnit hϖ ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F)
            * (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) * (z : v.adicCompletion F)) := by
        rw [← hxw, ← hz]
        push_cast [pow_succ, piUnit_val]
        ring
      have hwz := mul_left_cancel₀ (Units.ne_zero (piUnit hϖ ^ k)) hcan
      have hwmem : ((w : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
        rw [hwz]; exact mul_mem ϖ.2 z.2
      obtain ⟨uw, huw⟩ := (ValuationOrd.ord_eq_zero_iff _ _).mp hword
      have huwO : ((uw : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F)
          = ϖ * z := by
        apply Subtype.coe_injective
        push_cast
        calc ((uw : (v.adicCompletionIntegers F)ˣ) : v.adicCompletion F)
            = ((Units.map ((v.adicCompletionIntegers F).subtype.toMonoidHom) uw
                : (v.adicCompletion F)ˣ) : v.adicCompletion F) := rfl
          _ = ((w : (v.adicCompletion F)ˣ) : v.adicCompletion F) := by rw [huw]
          _ = _ := by rw [hwz]
      have hunit : IsUnit ((ϖ : v.adicCompletionIntegers F) * z) := huwO ▸ uw.isUnit
      exact hϖ.not_isUnit (isUnit_of_mul_isUnit_left hunit)


end Shells

section Measures

variable [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]

variable {ϖ : v.adicCompletionIntegers F}

variable (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure] [μ.Regular]

-- pin: measure_integers_lt_top (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1718)
omit [BorelSpace (v.adicCompletion F)] [μ.Regular] in
theorem measure_integers_lt_top : μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) < ∞ :=
  (isCompact_integers (F := F) (v := v)).measure_lt_top


end Measures

section Integrand

variable {ϖ : v.adicCompletionIntegers F}

end Integrand

section Zeta

variable [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]

variable {ϖ : v.adicCompletionIntegers F}

variable (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure] [μ.Regular]

end Zeta

end LocalZetaUnramified

end TateGlobal

end NumberField

end

end Fold_LocalZetaUnramified
