/-
The Kähler-to-Weil differential and the residue-theorem predicate, after FLT's
`Definitions/Def_AlgebraicCurve_WeilOfKaehler.lean` (133 ln)
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_WeilOfKaehler.lean>).

Statements are transcribed textually; the pin's `import Mathlib` /
`Def_AlgebraicCurve_LocalResidue` are replaced by the port's `Defs.LocalResidue`.
-/
import FLTForHuman.AlgebraicCurve.Defs.LocalResidue
import Mathlib.RingTheory.Trace.Basic

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

variable [HasCanonicalLocalResidueKStar K F]

theorem kaehlerResidueTerm_eq_zero_of_adeleBdd_canonical
    [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
    [Nontrivial Ω[F⁄K]] {ω : Ω[F⁄K]} (hω : ω ≠ 0)
    {α : Place K F → F} (hα : α ∈ adeleBdd (canonicalDivisorOf hω)) (v : Place K F) :
    kaehlerResidueTerm ω α v = 0 := by
  refine kaehlerResidueTerm_eq_zero_of_ord_nonneg ?_
  rcases eq_or_ne (α v) 0 with h0 | h0
  · exact Or.inl (by rw [h0, zero_mul])
  · refine Or.inr ?_
    have hg := v.differentialCoeff_ne_zero hω
    rw [v.ord_mul h0 hg]

    have hαv : -(canonicalDivisorOf hω v) ≤ v.ord (α v) := by
      have hval := hα v
      rw [v.adicValuation_eq_exp_neg_ord h0] at hval
      exact neg_le_of_neg_le (WithZero.exp_le_exp.mp hval)
    rw [canonicalDivisorOf_apply hω v, Place.ordDifferential] at hαv
    linarith

theorem kaehlerResidueTerm_support_subset
    [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
    [Nontrivial Ω[F⁄K]] {ω : Ω[F⁄K]} (hω : ω ≠ 0)
    {D : Divisor K F} {α : Place K F → F} (hα : α ∈ adeleBdd D) :
    Function.support (kaehlerResidueTerm ω α) ⊆ ↑(D - canonicalDivisorOf hω).support := by
  intro v hv

  rw [Finset.mem_coe, Finsupp.mem_support_iff, Finsupp.sub_apply, ne_eq, sub_eq_zero]
  intro hDω
  apply hv
  refine kaehlerResidueTerm_eq_zero_of_ord_nonneg ?_
  rcases eq_or_ne (α v) 0 with h0 | h0
  · exact Or.inl (by rw [h0, zero_mul])
  · refine Or.inr ?_
    have hg := v.differentialCoeff_ne_zero hω
    rw [v.ord_mul h0 hg]
    have hαv : -(D v) ≤ v.ord (α v) := by
      have hval := hα v
      rw [v.adicValuation_eq_exp_neg_ord h0] at hval
      exact neg_le_of_neg_le (WithZero.exp_le_exp.mp hval)
    rw [hDω, canonicalDivisorOf_apply hω v, Place.ordDifferential] at hαv
    linarith

theorem kaehlerResidueTerm_support_finite
    [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
    [Nontrivial Ω[F⁄K]] {ω : Ω[F⁄K]} (hω : ω ≠ 0)
    {D : Divisor K F} {α : Place K F → F} (hα : α ∈ adeleBdd D) :
    (Function.support (kaehlerResidueTerm ω α)).Finite :=
  Set.Finite.subset (Finset.finite_toSet _) (kaehlerResidueTerm_support_subset hω hα)

theorem kaehlerResidueTerm_support_finite_of_adeleSpace
    [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
    [Nontrivial Ω[F⁄K]] {ω : Ω[F⁄K]} (hω : ω ≠ 0)
    {α : Place K F → F} (hα : α ∈ adeleSpace K F) :
    (Function.support (kaehlerResidueTerm ω α)).Finite := by
  obtain ⟨D, hD⟩ := mem_adeleSpace_iff.mp hα
  exact kaehlerResidueTerm_support_finite hω hD

variable [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
  [Nontrivial Ω[F⁄K]]

variable (K F) in

def weilOfKaehler {ω : Ω[F⁄K]} (hω : ω ≠ 0) : Module.Dual K (adeleSpace K F) where
  toFun α := ∑ᶠ v, kaehlerResidueTerm ω (α : Place K F → F) v
  map_add' α β := by
    have hsupα := kaehlerResidueTerm_support_finite_of_adeleSpace hω α.2
    have hsupβ := kaehlerResidueTerm_support_finite_of_adeleSpace hω β.2
    rw [← finsum_add_distrib hsupα hsupβ]
    refine finsum_congr fun v => ?_
    unfold kaehlerResidueTerm
    rw [Submodule.coe_add, Pi.add_apply, add_mul, map_add, map_add]
  map_smul' c α := by
    simp only [RingHom.id_apply]
    rw [smul_finsum]
    refine finsum_congr fun v => ?_
    unfold kaehlerResidueTerm
    rw [Submodule.coe_smul, Pi.smul_apply, Algebra.smul_def, mul_assoc,
      ← Algebra.smul_def, map_smul, map_smul]

theorem weilOfKaehler_apply {ω : Ω[F⁄K]} (hω : ω ≠ 0) (α : adeleSpace K F) :
    weilOfKaehler K F hω α = ∑ᶠ v, kaehlerResidueTerm ω (α : Place K F → F) v := rfl

theorem weilOfKaehler_vanish_adeleBdd_canonical {ω : Ω[F⁄K]} (hω : ω ≠ 0)
    {α : adeleSpace K F} (hα : (α : Place K F → F) ∈ adeleBdd (canonicalDivisorOf hω)) :
    weilOfKaehler K F hω α = 0 := by
  rw [weilOfKaehler_apply]
  exact finsum_eq_zero_of_forall_eq_zero
    (kaehlerResidueTerm_eq_zero_of_adeleBdd_canonical hω hα)

variable (K F)

def ResidueTheorem : Prop :=
  ∀ [HasPrincipalDivisors K F] {ω : Ω[F⁄K]} (hω : ω ≠ 0) (f : F),
    weilOfKaehler K F hω ⟨diagonalHom K F f, diagonal_mem_adeleSpace f⟩ = 0

variable {K F}

variable (K F)

def WeilKaehlerAgree : Prop :=
  ∀ [HasPrincipalDivisors K F] {ω : Ω[F⁄K]} (hω : ω ≠ 0),
    weilOfKaehler K F hω ≠ 0 ∧
    weilOfKaehler K F hω ∈ omegaSpace (canonicalDivisorOf hω) ∧
    ∀ D : Divisor K F, weilOfKaehler K F hω ∈ omegaSpace D → D ≤ canonicalDivisorOf hω

variable {K F}

variable (K F)

def ResiduePairingSurjective : Prop :=
  ∀ [HasPrincipalDivisors K F] (W D : Divisor K F)
    {φ : Module.Dual K (adeleSpace K F)} (hφ : φ ∈ omegaSpace W) (_hφ0 : φ ≠ 0)
    (_hWmax : ∀ E : Divisor K F, φ ∈ omegaSpace E → E ≤ W),
    Function.Surjective (residuePairing K F W D hφ)

end AlgebraicCurve

end

/-! ## The two proof-reached helper targets, promoted (refactor round)

`S_AlgebraicCurve_weilOfKaehler_mem_omegaSpace_of_residueTheorem.lean` (18 ln) and
`S_AlgebraicCurve_weilOfKaehler_ne_zero_and_maximal.lean` (199 ln), statements from
their `Theorems/` wrappers.  H3 re-provisioned them `private` in
`Canonical/WeilDifferential.lean` because the 14-`S_`-file measurement missed them;
the refactor round moves them here, upstream of their consumer, at the pin's public
names.  The support lemmas are the pin's own public declarations from the second
`S_` file; the three pin-`private` ones (`ord_nonneg_of_mem`,
`localResidue_mul_uniformizer_inv`, `exists_trace_residue_ne_zero`) stay `private`
here, exactly as the pin keeps them. -/

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

open IsDedekindDomain WithZero Module IsLocalRing

-- The pin's `ne_zero_and_maximal` helper file sets this (its section variables
-- are not all used by every declaration).
set_option linter.unusedSectionVars false

noncomputable section

namespace Place

variable (v : Place K F)

private theorem ord_nonneg_of_mem {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu; push_cast at h; rw [zpow_natCast]; exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]; exact Int.natCast_nonneg n

end Place

section SingleEval

variable [HasCanonicalLocalResidueKStar K F]

open scoped Classical in

theorem kaehlerResidueTerm_single_of_ne {ω : Ω[F⁄K]} {v : Place K F} {g : F}
    {w : Place K F} (hw : w ≠ v) :
    kaehlerResidueTerm ω (Pi.single v g) w = 0 := by
  unfold kaehlerResidueTerm
  rw [Pi.single_eq_of_ne hw, zero_mul, map_zero, map_zero]

variable [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
  [Nontrivial Ω[F⁄K]]

open scoped Classical in

theorem weilOfKaehler_single_s6 {ω : Ω[F⁄K]} (hω : ω ≠ 0) (v : Place K F) (g : F) :
    weilOfKaehler K F hω (adeleSingle v g)
      = Algebra.trace K v.ResidueField (v.localResidue (g * v.differentialCoeff ω)) := by
  rw [weilOfKaehler_apply, adeleSingle_coe]
  refine (finsum_eq_single _ v fun w hw => kaehlerResidueTerm_single_of_ne hw).trans ?_
  unfold kaehlerResidueTerm
  rw [Pi.single_eq_same]

end SingleEval

section SimplePoleProbe

variable [HasCanonicalLocalResidueKStar K F]

namespace Place

variable (v : Place K F)

private theorem localResidue_mul_uniformizer_inv (c : v.toValuationSubring) :
    v.localResidue ((c : F) * v.uniformizer⁻¹) = IsLocalRing.residue _ c := by
  have hmul : v.uniformizer * ((c : F) * v.uniformizer⁻¹) = (c : F) := by
    rw [mul_comm (c : F), ← mul_assoc, mul_inv_cancel₀ v.uniformizer_ne_zero, one_mul]
  have hmem : v.uniformizer * ((c : F) * v.uniformizer⁻¹) ∈ v.toValuationSubring := by
    rw [hmul]; exact c.2
  rw [v.localResidue_simplePole _ hmem]
  congr 1
  exact Subtype.ext hmul

end Place

variable [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
  [Nontrivial Ω[F⁄K]]

def simplePoleProbe {ω : Ω[F⁄K]} (_hω : ω ≠ 0) (v : Place K F)
    (c : v.toValuationSubring) : adeleSpace K F :=
  adeleSingle v ((c : F) * v.uniformizer⁻¹ * (v.differentialCoeff ω)⁻¹)

theorem weilOfKaehler_simplePoleProbe {ω : Ω[F⁄K]} (hω : ω ≠ 0) (v : Place K F)
    (c : v.toValuationSubring) :
    weilOfKaehler K F hω (simplePoleProbe hω v c)
      = Algebra.trace K v.ResidueField (IsLocalRing.residue _ c) := by
  unfold simplePoleProbe
  rw [weilOfKaehler_single_s6 hω,
    mul_assoc, inv_mul_cancel₀ (v.differentialCoeff_ne_zero hω), mul_one,
    v.localResidue_mul_uniformizer_inv]

open scoped Classical in

theorem simplePoleProbe_mem_adeleBdd {ω : Ω[F⁄K]} (hω : ω ≠ 0) (v : Place K F)
    (c : v.toValuationSubring) {D : Divisor K F} (hDv : canonicalDivisorOf hω v < D v) :
    (simplePoleProbe hω v c : Place K F → F) ∈ adeleBdd D := by
  unfold simplePoleProbe
  rw [adeleSingle_coe]
  refine single_mem_adeleBdd v _ D ?_
  rcases eq_or_ne (c : F) 0 with hc | hc
  · rw [hc, zero_mul, zero_mul, Valuation.map_zero]; exact zero_le'
  · set g : F := (c : F) * v.uniformizer⁻¹ * (v.differentialCoeff ω)⁻¹ with hg
    have hg0 : g ≠ 0 :=
      mul_ne_zero (mul_ne_zero hc (inv_ne_zero v.uniformizer_ne_zero))
        (inv_ne_zero (v.differentialCoeff_ne_zero hω))
    rw [v.adicValuation_eq_exp_neg_ord hg0, WithZero.exp_le_exp, neg_le]

    rw [hg, v.ord_mul (mul_ne_zero hc (inv_ne_zero v.uniformizer_ne_zero))
        (inv_ne_zero (v.differentialCoeff_ne_zero hω)),
      v.ord_mul hc (inv_ne_zero v.uniformizer_ne_zero),
      v.ord_inv, v.ord_uniformizer, v.ord_inv]
    have hcnn : 0 ≤ v.ord (c : F) := v.ord_nonneg_of_mem c.2
    rw [canonicalDivisorOf_apply hω v, Place.ordDifferential] at hDv
    linarith

end SimplePoleProbe

namespace Place

private theorem exists_trace_residue_ne_zero [HasSeparableResidue K F] (v : Place K F) :
    ∃ c : v.toValuationSubring,
      Algebra.trace K v.ResidueField (IsLocalRing.residue _ c) ≠ 0 := by
  have htr := HasSeparableResidue.trace_ne_zero (K := K) (F := F) v
  rw [ne_eq, LinearMap.ext_iff, not_forall] at htr
  obtain ⟨x, hx⟩ := htr
  obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective x
  exact ⟨c, by simpa using hx⟩

end Place

section Nonvanishing

variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
  [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

theorem weilOfKaehler_ne_zero_s6 [HasSeparableResidue K F] [Nonempty (Place K F)]
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) : weilOfKaehler K F hω ≠ 0 := by
  obtain ⟨v⟩ := ‹Nonempty (Place K F)›
  obtain ⟨c, hc⟩ := v.exists_trace_residue_ne_zero
  intro h
  apply hc
  rw [← weilOfKaehler_simplePoleProbe hω v c, h, LinearMap.zero_apply]

end Nonvanishing

section Maximality

variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
  [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

theorem trace_residueField_eq_zero_of_weilOfKaehler_mem {ω : Ω[F⁄K]} (hω : ω ≠ 0)
    {D : Divisor K F} (hD : weilOfKaehler K F hω ∈ omegaSpace D)
    {v : Place K F} (hDv : canonicalDivisorOf hω v < D v) :
    (Algebra.trace K v.ResidueField : _ →ₗ[K] K) = 0 := by
  ext x
  obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective x
  rw [LinearMap.zero_apply, ← weilOfKaehler_simplePoleProbe hω v c]
  exact omegaSpace_vanishBdd hD (simplePoleProbe_mem_adeleBdd hω v c hDv)

theorem weilOfKaehler_omegaSpace_le_canonical_s6 [HasSeparableResidue K F]
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) {D : Divisor K F}
    (hD : weilOfKaehler K F hω ∈ omegaSpace D) :
    D ≤ canonicalDivisorOf hω := by
  intro v
  rcases le_or_gt (D v) (canonicalDivisorOf hω v) with h | h
  · exact h
  · exact absurd (trace_residueField_eq_zero_of_weilOfKaehler_mem hω hD h)
      (HasSeparableResidue.trace_ne_zero v)

end Maximality

theorem weilOfKaehler_ne_zero_and_maximal_s6 [HasCanonicalLocalResidueKStar K F]
    [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
    [Nontrivial Ω[F⁄K]] [HasSeparableResidue K F] [Nonempty (Place K F)]
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    weilOfKaehler K F hω ≠ 0 ∧
      ∀ D : Divisor K F, weilOfKaehler K F hω ∈ omegaSpace D → D ≤ canonicalDivisorOf hω :=
  ⟨weilOfKaehler_ne_zero_s6 hω, fun _ hD => weilOfKaehler_omegaSpace_le_canonical_s6 hω hD⟩

/-! ### The two promoted targets -/

theorem weilOfKaehler_mem_omegaSpace_of_residueTheorem {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]] [HasPrincipalDivisors K F]
    (hRT : ResidueTheorem K F) {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    weilOfKaehler K F hω ∈ omegaSpace (canonicalDivisorOf hω) := by
  rw [omegaSpace, Submodule.mem_dualAnnihilator]
  intro α hα
  obtain ⟨β, hβ, γ, hγ, rfl⟩ := Submodule.mem_sup.mp hα
  rw [map_add, weilOfKaehler_vanish_adeleBdd_canonical hω (Submodule.mem_comap.mp hβ)]
  obtain ⟨f, hf⟩ := Submodule.mem_comap.mp hγ
  have hγ' : γ = ⟨diagonalHom K F f, diagonal_mem_adeleSpace f⟩ := Subtype.ext hf.symm
  rw [hγ', hRT hω f, add_zero]

theorem weilOfKaehler_ne_zero_and_maximal {K F : Type*} [Field K] [Field F] [Algebra K F]
    [HasCanonicalLocalResidueKStar K F]
    [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
    [Nontrivial Ω[F⁄K]] [HasSeparableResidue K F] [Nonempty (Place K F)]
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    weilOfKaehler K F hω ≠ 0 ∧
      ∀ D : Divisor K F, weilOfKaehler K F hω ∈ omegaSpace D → D ≤ canonicalDivisorOf hω :=
  weilOfKaehler_ne_zero_and_maximal_s6 hω

end

end AlgebraicCurve

