/-
The trace sum: `∑_P ord(g) • y_P^* ω = 0`.

This is the Abel-differential sum of the residue theorem along a finite cover.  For a
tower `K ⊆ F ⊆ FE`, `K ⊆ E ⊆ FE` with `FE` a curve over `E`, `F/K` of transcendence
degree one, `g ∈ FE` and a finite set `S` of places of `FE` with local `K`-algebra
sections `y` of the `F`-algebra structure, the sum over `S` of `ord_P(g)` times the
pull-back along `y_P` of a regular differential of `F/K` is zero.

The proof is the pin's: split the dual of `Ω[FE⁄E]` along a derivation `δ` of `E`,
transport `δ` to a derivation `Θ` of `FE` that respects the integral structure at every
place (the constant-field-extension lifting engine), and evaluate the general residue
theorem `ResidueTheorem E FE` at the adele `Θ g / g · a · h`.  The summand at a place of
`S` is then the trace of a local residue of an integral element, hence vanishes by
`trace_localResidue_eq_zero`; the finiteness of the support is the pin's `hrat` case
split.

The `logDer_*` block is the pin's, at its generality: an arbitrary derivation
`Θ : Derivation R L L` and a place of `L`, no integrality hypotheses beyond the one at
the place.

Sources:
`Theorems/Thm_AlgebraicCurve_Differential_sum_ord_smul_pullbackAlong_eq_zero.lean`
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Differential_sum_ord_smul_pullbackAlong_eq_zero.lean>),
proof `P2M/Sol/S_AlgebraicCurve_Differential_sum_ord_smul_pullbackAlong_eq_zero.lean`
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Differential_sum_ord_smul_pullbackAlong_eq_zero.lean>).
The pin's three `attribute [-instance]`/`[-simp]` walls are dropped (the port installs
none of those instances), and the `S_` file's `#check`/`#print axioms` tail is dropped.

spec-pin: Theorems/Thm_AlgebraicCurve_Differential_sum_ord_smul_pullbackAlong_eq_zero.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Differential_sum_ord_smul_pullbackAlong_eq_zero.lean

-/
import FLTForHuman.AlgebraicCurve.ResidueTheorem.GeneralFromK
import FLTForHuman.AlgebraicCurve.LocalResidue.Instance
import FLTForHuman.AlgebraicCurve.Canonical.HasCanonicalDivisor
import FLTForHuman.AlgebraicCurve.Canonical.DCoordGenerates
import FLTForHuman.AlgebraicCurve.Canonical.RegularDifferentialsFinrank
import FLTForHuman.AlgebraicCurve.Genus.RatFunc
import FLTForHuman.AlgebraicCurve.Differential.Coefficient
import FLTForHuman.AlgebraicCurve.Differential.ConstantFieldExtension
import FLTForHuman.AlgebraicCurve.Differential.RegularDiffs
import FLTForHuman.AlgebraicCurve.Differential.PushPull
import FLTForHuman.AlgebraicCurve.IsCurveOver.EssFiniteType
import FLTForHuman.AlgebraicCurve.Place.ConstantFieldExtension
import FLTForHuman.AlgebraicCurve.Place.FromValuationSubring
import FLTForHuman.AlgebraicCurve.Defs.Correspondence
import FLTForHuman.AlgebraicCurve.Defs.RegularDifferentials
import FLTForHuman.AlgebraicCurve.Defs.PolarDifferentials
import FLTForHuman.AlgebraicCurve.Defs.IsCurveOver
import FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisorUniformizer
import FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisor
import FLTForHuman.AlgebraicCurve.Defs.LocalResidue
import FLTForHuman.AlgebraicCurve.Defs.WeilOfKaehler
import FLTForHuman.AlgebraicCurve.Defs.AdelicIndex

set_option autoImplicit false

-- The pin's `haveI`/`letI` walls are load-bearing: the RatFunc instances in
-- `residueTheorem_of_curve` and `main` are built by `letI`/`haveI` at the point of use.
-- Keep them literal rather than weaken the proofs.
set_option linter.style.haveILetI false

noncomputable section

open AlgebraicCurve
open KaehlerDifferential

namespace AlgebraicCurve

section Toolkit

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

/-- The chosen irreducible of the valuation subring is irreducible. -/
theorem irreducible_unifElt :
    Irreducible (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose :=
  (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec

/-- Its coercion is the place's uniformizer. -/
theorem coe_unifElt :
    ((IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose : F)
      = v.uniformizer := rfl

/-- A unit of the valuation subring has order zero. -/
theorem ord_eq_zero_of_isUnit {a : v.toValuationSubring} (ha : IsUnit a) : v.ord (a : F) = 0 := by
  obtain ⟨u, rfl⟩ := ha
  exact v.ord_coe_unit u

/-- A non-unit of the valuation subring lies in its maximal ideal. -/
theorem mem_maximalIdeal_of_not_isUnit {a : v.toValuationSubring} (ha : ¬IsUnit a) :
    a ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
  rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

/-- Every non-zero element is a unit times a power of the uniformizer. -/
theorem exists_unit_mul_uniformizer_zpow {g : F} (hg : g ≠ 0) :
    ∃ u : v.toValuationSubringˣ,
      g = ((u : v.toValuationSubring) : F) * v.uniformizer ^ v.ord g := by
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hg (irreducible_unifElt v)
  exact ⟨u, hu⟩

/-- A positive-valuation element is the uniformizer times an integral one. -/
theorem exists_mem_eq_uniformizer_mul {z : F}
    (hz : v.toValuationSubring.valuation z < 1) :
    ∃ s ∈ v.toValuationSubring, z = v.uniformizer * s := by
  have hzO : z ∈ v.toValuationSubring :=
    (v.toValuationSubring.valuation_le_one_iff z).1 hz.le
  have hmax : (⟨z, hzO⟩ : v.toValuationSubring) ∈
      IsLocalRing.maximalIdeal v.toValuationSubring :=
    (v.toValuationSubring.valuation_lt_one_iff ⟨z, hzO⟩).2 hz
  rw [(irreducible_unifElt v).maximalIdeal_eq, Ideal.mem_span_singleton'] at hmax
  obtain ⟨s, hs⟩ := hmax
  refine ⟨s, s.2, ?_⟩
  have h := congrArg Subtype.val hs
  simp only [MulMemClass.coe_mul] at h
  rw [← h, coe_unifElt, mul_comm]

end Toolkit

/-! ## Logarithmic derivatives of an arbitrary derivation

The pin's `section LogDer`: the five lemmas are about a derivation `Θ` of a field `L`
over a commutative ring `R` and a place of `L`; they are the module's self-contained
prelude and are kept at that generality. -/

section LogDer

variable {R L : Type*} [CommRing R] [Field L] [Algebra R L] (Θ : Derivation R L L)

theorem logDer_mul {a b : L} (ha : a ≠ 0) (hb : b ≠ 0) :
    Θ (a * b) / (a * b) = Θ a / a + Θ b / b := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, div_add_div _ _ ha hb,
    div_eq_div_iff (mul_ne_zero ha hb) (mul_ne_zero ha hb)]
  ring

theorem logDer_zpow {a : L} (ha : a ≠ 0) (n : ℤ) :
    Θ (a ^ n) / a ^ n = (n : L) * (Θ a / a) := by
  rw [Derivation.leibniz_zpow, zpow_sub_one₀ ha, smul_eq_mul, zsmul_eq_mul,
    div_eq_iff (zpow_ne_zero n ha), div_eq_mul_inv]
  ring

variable {K : Type*} [Field K] [Algebra K L] (v : Place K L)

theorem logDer_mem_of_ord_eq_zero
    (hΘ : ∀ z ∈ v.toValuationSubring, Θ z ∈ v.toValuationSubring) {f : L} (hf : v.ord f = 0) :
    Θ f / f ∈ v.toValuationSubring := by
  rw [div_eq_mul_inv]
  refine mul_mem (hΘ _ ((Place.mem_iff_ord_nonneg_vs f).2 hf.ge))
    ((Place.mem_iff_ord_nonneg_vs _).2 ?_)
  rw [v.ord_inv, hf, neg_zero]

theorem logDer_eq (hΘ : ∀ z ∈ v.toValuationSubring, Θ z ∈ v.toValuationSubring)
    {g : L} (hg : g ≠ 0) :
    ∃ ℓ ∈ v.toValuationSubring,
      Θ g / g = ℓ + (v.ord g : L) * (Θ v.uniformizer / v.uniformizer) := by
  obtain ⟨u, hu⟩ := exists_unit_mul_uniformizer_zpow v hg
  have hU0 : ((u : v.toValuationSubring) : L) ≠ 0 := by
    intro h0
    apply hg
    rw [hu, h0, zero_mul]
  refine ⟨Θ (u : L) / (u : L), logDer_mem_of_ord_eq_zero Θ v hΘ (v.ord_coe_unit u), ?_⟩
  conv_lhs => rw [hu]
  rw [logDer_mul Θ hU0 (zpow_ne_zero _ v.uniformizer_ne_zero),
    logDer_zpow Θ v.uniformizer_ne_zero]

theorem logDer_uniformizer_mem (hΘ : ∀ z ∈ v.toValuationSubring, Θ z ∈ v.toValuationSubring)
    {p : L} (hp1 : v.ord p = 1) (hΘp : Θ p = 0) :
    Θ v.uniformizer / v.uniformizer ∈ v.toValuationSubring := by
  have hp0 : p ≠ 0 := by
    rintro rfl
    simp at hp1
  obtain ⟨w, hw⟩ := exists_unit_mul_uniformizer_zpow v hp0
  rw [hp1, zpow_one] at hw
  have hW0 : ((w : v.toValuationSubring) : L) ≠ 0 := by
    intro h0
    apply hp0
    rw [hw, h0, zero_mul]
  have h0 : Θ p / p = 0 := by rw [hΘp, zero_div]
  rw [hw, logDer_mul Θ hW0 v.uniformizer_ne_zero] at h0
  have h1 : Θ v.uniformizer / v.uniformizer
      = -(Θ (w : L) / (w : L)) := by
    linear_combination h0
  rw [h1]
  exact neg_mem (logDer_mem_of_ord_eq_zero Θ v hΘ (v.ord_coe_unit w))

end LogDer

section Residue

open KaehlerDifferential IntermediateField
open scoped Polynomial IntermediateField

variable {E FE : Type*} [Field E] [Field FE] [Algebra E FE]

/-- The trace of the local residue of an element with a simple pole of residue `r` is
`r`. -/
theorem trace_localResidue_eq [IsAlgClosed E] [IsCurveOver E FE]
    [HasCanonicalLocalResidueKStar E FE] (v : Place E FE) (r : E) {f : FE}
    (h : f - algebraMap E FE r * v.uniformizer⁻¹ ∈ v.toValuationSubring) :
    Algebra.trace E v.ResidueField (v.localResidue f) = r := by
  have hf : f = (f - algebraMap E FE r * v.uniformizer⁻¹) + r • v.uniformizer⁻¹ := by
    rw [Algebra.smul_def]; ring
  rw [hf, map_add, v.localResidue_of_mem h, zero_add, LinearMap.map_smul,
    v.gate_localResidue_uniformizer_inv, ← Algebra.algebraMap_eq_smul_one,
    Algebra.trace_algebraMap,
    show Module.finrank E v.ResidueField = 1 from IsCurveOver.deg_eq_one_of_isAlgClosed v,
    one_smul]

/-- The trace of the local residue of an integral element is zero. -/
theorem trace_localResidue_eq_zero [HasCanonicalLocalResidueKStar E FE] (v : Place E FE)
    {f : FE} (h : f ∈ v.toValuationSubring) :
    Algebra.trace E v.ResidueField (v.localResidue f) = 0 := by
  rw [v.localResidue_of_mem h, map_zero]

/-- The general residue theorem for a curve, at the pin's binders. -/
theorem residueTheorem_of_curve [IsAlgClosed E] [CharZero E] [IsCurveOver E FE]
    [HasCanonicalLocalResidueKStar E FE] [HasCanonicalDivisor (K := E) (F := FE)]
    [∀ v : Place E FE, v.DCoordGenerates]
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE) :
    ResidueTheorem E FE := by
  classical
  obtain ⟨t, ht, hfin⟩ := hfgE
  haveI := hfin
  haveI : PerfectField E := inferInstance
  haveI : Algebra.EssFiniteType E FE :=
    essFiniteType_of_transcendental_of_finiteDimensional ht hfin
  let e : RatFunc E ≃ₐ[E] E⟮t⟯ := RatFunc.algEquivOfTranscendental t ht
  letI : Algebra (RatFunc E) FE :=
    ((algebraMap E⟮t⟯ FE).comp e.toAlgHom.toRingHom).toAlgebra
  have hsq : RingHom.comp (algebraMap (RatFunc E) FE)
        (e.symm.toRingEquiv : E⟮t⟯ →+* RatFunc E)
      = RingHom.comp (RingEquiv.refl FE : FE →+* FE) (algebraMap E⟮t⟯ FE) := by
    refine RingHom.ext fun a => ?_
    show algebraMap E⟮t⟯ FE (e (e.symm a)) = algebraMap E⟮t⟯ FE a
    rw [e.apply_symm_apply]
  haveI : IsScalarTower E (RatFunc E) FE :=
    IsScalarTower.of_algebraMap_eq fun a => by
      show algebraMap E FE a = algebraMap E⟮t⟯ FE (e (algebraMap E (RatFunc E) a))
      rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  haveI : Module.Finite (RatFunc E) FE :=
    Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl FE) hsq
  haveI : Algebra.IsIntegral (RatFunc E) FE := Algebra.IsIntegral.of_finite _ _
  haveI : CharZero (RatFunc E) :=
    charZero_of_injective_algebraMap (algebraMap E (RatFunc E)).injective
  haveI : PerfectField (RatFunc E) := PerfectField.ofCharZero
  haveI : Algebra.IsSeparable (RatFunc E) FE := Algebra.IsSeparable.of_integral _ _
  haveI : IsCurveOver E (RatFunc E) := isCurveOver_ratFunc E
  haveI : Algebra.EssFiniteType E (RatFunc E) := by
    haveI : Algebra.EssFiniteType E[X] (RatFunc E) :=
      Algebra.EssFiniteType.of_isLocalization (RatFunc E) (nonZeroDivisors E[X])
    exact Algebra.EssFiniteType.comp E E[X] (RatFunc E)
  haveI : ∀ v : Place E (RatFunc E), v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  intro hPD ω hω f
  exact residueTheorem_of_isAlgClosed hω f

end Residue

section Main

open KaehlerDifferential IntermediateField

/-- The pin's `main`: the Abel-differential trace sum. -/
theorem main
    (K F E FE : Type*) [Field K] [Field F] [Field E] [Field FE]
    [Algebra K F] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
    [IsScalarTower K E FE] [IsScalarTower K F FE]
    [IsAlgClosed K] [CharZero K] [IsAlgClosed E]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    [IsCurveOver K F] [IsCurveOver E FE]
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (g : FE) (hg : g ≠ 0)
    (S : Finset (Place E FE)) (y : Place E FE → (F →ₐ[K] E))
    (hS : ∀ P ∈ S, ∀ f : F,
      P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (y P f)) < 1)
    (hrat : ∀ P : Place E FE, P ∉ S → P.ord g ≠ 0 →
      ∃ f : F, algebraMap F FE f ∉ P.toValuationSubring)
    (ω : Ω[F⁄K]) (hω : ω ∈ regularDifferentials K F) :
    ∑ P ∈ S, (P.ord g) • Differential.pullbackAlong (y P) ω = 0 := by
  classical

  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  haveI : PerfectField E := inferInstance
  obtain ⟨x, hx, hxfin⟩ := hfg
  haveI := hxfin
  obtain ⟨t, ht, htfin⟩ := hfgE
  haveI : Algebra.EssFiniteType E FE :=
    essFiniteType_of_transcendental_of_finiteDimensional ht htfin
  haveI hDC : ∀ w : Place E FE, w.DCoordGenerates := dCoordGenerates_of_isCurveOver
  haveI : HasCanonicalDivisor (K := E) (F := FE) := hasCanonicalDivisor_of_isCurveOver
  haveI hK : HasCanonicalLocalResidueK E FE := hasCanonicalLocalResidueK E FE
  letI : HasCanonicalLocalResidueKStar E FE :=
    ⟨fun v => (HasCanonicalLocalResidueK.exists_data v).some⟩

  obtain ⟨a, hωa⟩ : ∃ a : F, ω = a • D K F x := by
    obtain ⟨bF, hbF⟩ := HorizDeriv.exists_basis_D K F ⟨x, hx, hxfin⟩ hx
    refine ⟨bF.repr ω 0, ?_⟩
    have h := bF.sum_repr ω
    rw [Fin.sum_univ_one, hbF] at h
    exact h.symm

  refine (Module.forall_dual_apply_eq_zero_iff E _).1 fun lam => ?_
  let δ : Derivation K E E := lam.compDer (D K E)
  have hδ : ∀ e : E, δ e = lam (D K E e) := fun e => rfl
  have hlam : lam (∑ P ∈ S, (P.ord g) • Differential.pullbackAlong (y P) ω)
      = ∑ P ∈ S, ((P.ord g : ℤ) : E) * ((y P a) * δ (y P x)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [map_zsmul, hωa, Differential.pullbackAlong_smul, Differential.pullbackAlong_D,
      LinearMap.map_smul, smul_eq_mul, zsmul_eq_mul, hδ]
  rw [hlam]

  obtain ⟨Θ, hΘF, hΘE, hΘO⟩ :=
    exists_derivation_constantFieldExtension_map_mem K F E FE ⟨x, hx, hxfin⟩ ⟨t, ht, htfin⟩
      hgen δ

  obtain ⟨bE, -⟩ := HorizDeriv.exists_basis_D E FE ⟨t, ht, htfin⟩ ht
  have hω₀ : bE 0 ≠ 0 := bE.ne_zero 0
  obtain ⟨h, hDx⟩ : ∃ h : FE, D E FE (algebraMap F FE x) = h • bE 0 := by
    refine ⟨bE.repr (D E FE (algebraMap F FE x)) 0, ?_⟩
    have h := bE.sum_repr (D E FE (algebraMap F FE x))
    rw [Fin.sum_univ_one] at h
    exact h.symm
  have hcoef : ∀ v : Place E FE,
      h * v.differentialCoeff (bE 0) = coeffDer v (algebraMap F FE x) := by
    intro v
    rw [coeffDer_apply, hDx, Place.differentialCoeff_smul]

  have RT : ResidueTheorem E FE := residueTheorem_of_curve ⟨t, ht, htfin⟩
  have hRT := RT hω₀ (Θ g / g * algebraMap F FE a * h)
  rw [weilOfKaehler_apply] at hRT
  have hRT' : ∑ᶠ v, kaehlerResidueTerm (bE 0)
      (diagonalHom E FE (Θ g / g * algebraMap F FE a * h)) v = 0 := hRT
  have hTv : ∀ v : Place E FE,
      kaehlerResidueTerm (bE 0) (diagonalHom E FE (Θ g / g * algebraMap F FE a * h)) v
        = Algebra.trace E v.ResidueField (v.localResidue
            (Θ g / g * (algebraMap F FE a * coeffDer v (algebraMap F FE x)))) := by
    intro v
    show Algebra.trace E v.ResidueField (v.localResidue
      (Θ g / g * algebraMap F FE a * h * v.differentialCoeff (bE 0))) = _
    rw [mul_assoc, mul_assoc, hcoef v]

  have hEmem : ∀ (v : Place E FE) (e : E), algebraMap E FE e ∈ v.toValuationSubring :=
    fun v e => v.algebraMap_mem' e

  have hT_on : ∀ v ∈ S,
      kaehlerResidueTerm (bE 0) (diagonalHom E FE (Θ g / g * algebraMap F FE a * h)) v
        = -(((v.ord g : ℤ) : E) * ((y v a) * δ (y v x))) := by
    intro v hv
    rw [hTv]
    refine trace_localResidue_eq v _ ?_

    obtain ⟨s₁, hs₁, hs₁e⟩ := exists_mem_eq_uniformizer_mul v (hS v hv a)
    obtain ⟨s₂, hs₂, hs₂e⟩ := exists_mem_eq_uniformizer_mul v (hS v hv x)
    obtain ⟨ℓ, hℓ, hL⟩ := logDer_eq Θ v (hΘO v) hg
    have hπ : v.uniformizer ≠ 0 := v.uniformizer_ne_zero
    have hπi : v.uniformizer * v.uniformizer⁻¹ = 1 := mul_inv_cancel₀ hπ
    have ha' : algebraMap F FE a = algebraMap E FE (y v a) + v.uniformizer * s₁ := by
      linear_combination hs₁e
    have hx' : algebraMap F FE x = algebraMap E FE (y v x) + v.uniformizer * s₂ := by
      linear_combination hs₂e

    have hc : coeffDer v (algebraMap F FE x)
        = v.uniformizer * coeffDer v s₂ + s₂ := by
      rw [hx', map_add, Derivation.map_algebraMap, Derivation.leibniz, coeffDer_uniformizer,
        smul_eq_mul, smul_eq_mul, mul_one, zero_add]

    have h3 : Θ v.uniformizer * s₂ + v.uniformizer * Θ s₂
        + algebraMap E FE (δ (y v x)) = 0 := by
      have h0 := hΘF x
      rw [hx', map_add, hΘE, Derivation.leibniz, smul_eq_mul, smul_eq_mul] at h0
      linear_combination h0
    have hr : algebraMap E FE (-(((v.ord g : ℤ) : E) * ((y v a) * δ (y v x))))
        = -((v.ord g : FE) * (algebraMap E FE (y v a) * algebraMap E FE (δ (y v x)))) := by
      rw [map_neg, map_mul, map_mul, map_intCast]
    rw [hr, hL, ha', hc, div_eq_mul_inv]
    have key :
        (ℓ + (v.ord g : FE) * (Θ v.uniformizer * v.uniformizer⁻¹)) *
            ((algebraMap E FE (y v a) + v.uniformizer * s₁) *
              (v.uniformizer * coeffDer v s₂ + s₂)) -
          -((v.ord g : FE) * (algebraMap E FE (y v a) * algebraMap E FE (δ (y v x)))) *
            v.uniformizer⁻¹
        = ℓ * ((algebraMap E FE (y v a) + v.uniformizer * s₁) *
              (v.uniformizer * coeffDer v s₂ + s₂))
          + (v.ord g : FE) * (Θ v.uniformizer * (algebraMap E FE (y v a) * coeffDer v s₂
              + v.uniformizer * s₁ * coeffDer v s₂ + s₁ * s₂)
              - algebraMap E FE (y v a) * Θ s₂) := by
      linear_combination
        ((v.ord g : FE) * (Θ v.uniformizer * (algebraMap E FE (y v a) * coeffDer v s₂
              + v.uniformizer * s₁ * coeffDer v s₂ + s₁ * s₂)
              - algebraMap E FE (y v a) * Θ s₂)) * hπi
        + ((v.ord g : FE) * algebraMap E FE (y v a) * v.uniformizer⁻¹) * h3
    rw [key]
    have hcs : coeffDer v s₂ ∈ v.toValuationSubring := by
      rw [coeffDer_apply]; exact differentialCoeff_D_mem v hs₂
    have hπm : v.uniformizer ∈ v.toValuationSubring := Place.uniformizer_mem_toValuationSubring v
    have hA : algebraMap E FE (y v a) ∈ v.toValuationSubring := hEmem v _
    have hm : ((v.ord g : ℤ) : FE) ∈ v.toValuationSubring := intCast_mem _ _
    refine add_mem (mul_mem hℓ (mul_mem (add_mem hA (mul_mem hπm hs₁))
      (add_mem (mul_mem hπm hcs) hs₂))) (mul_mem hm (sub_mem (mul_mem (hΘO v _ hπm)
        (add_mem (add_mem (mul_mem hA hcs) (mul_mem (mul_mem hπm hs₁) hcs)) (mul_mem hs₁ hs₂)))
        (mul_mem hA (hΘO v _ hs₂))))

  have hT_off : ∀ v ∉ S,
      kaehlerResidueTerm (bE 0) (diagonalHom E FE (Θ g / g * algebraMap F FE a * h)) v = 0 := by
    intro v hv
    rw [hTv]
    refine trace_localResidue_eq_zero v ?_
    by_cases hnew : ∀ f : F, algebraMap F FE f ∈ v.toValuationSubring
    ·
      have hord : v.ord g = 0 := by
        by_contra hne
        obtain ⟨f, hf⟩ := hrat v hv hne
        exact hf (hnew f)
      refine mul_mem (logDer_mem_of_ord_eq_zero Θ v (hΘO v) hord) (mul_mem (hnew a) ?_)
      rw [coeffDer_apply]
      exact differentialCoeff_D_mem v (hnew x)
    ·
      push Not at hnew
      obtain ⟨f₀, hf₀⟩ := hnew
      have hwK : ∀ k : K, (algebraMap F FE : F →+* FE) (algebraMap K F k)
          ∈ v.toValuationSubring := by
        intro k
        have : (algebraMap F FE : F →+* FE) (algebraMap K F k)
            = algebraMap E FE (algebraMap K E k) := by
          show algebraMap F FE (algebraMap K F k) = _
          rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
        rw [this]
        exact hEmem v _
      obtain ⟨u, hu⟩ := Place.exists_toValuationSubring_eq_comap_ringHom (K := K) x
        (algebraMap F FE : F →+* FE) v.toValuationSubring hwK ⟨f₀, hf₀⟩
      have hmemF : ∀ f : F, f ∈ u.toValuationSubring ↔
          algebraMap F FE f ∈ v.toValuationSubring := by
        intro f
        rw [hu, ValuationSubring.mem_comap]
      obtain ⟨P', -, hP'ord, hP'uniq⟩ :=
        Place.exists_comap_algebraMap_eq_of_constantFieldExtension K F E FE ⟨x, hx, hxfin⟩
          ⟨t, ht, htfin⟩ hgen u
      have hvP' : v = P' := hP'uniq v hu.symm
      have hordF : ∀ f : F, v.ord (algebraMap F FE f) = u.ord f := by
        intro f; rw [hvP']; exact hP'ord f

      have hLg : Θ g / g ∈ v.toValuationSubring := by
        obtain ⟨ℓ, hℓ, hL⟩ := logDer_eq Θ v (hΘO v) hg
        rw [hL]
        refine add_mem hℓ (mul_mem (intCast_mem _ _) ?_)
        refine logDer_uniformizer_mem Θ v (hΘO v) (p := algebraMap F FE u.uniformizer) ?_ (hΘF _)
        rw [hordF, u.ord_uniformizer]

      obtain ⟨fu, hfu, hωu⟩ := (mem_regularDifferentials_iff).1 hω u
      have h1 : ∀ (c z : F), KaehlerDifferential.map K E F FE (c • D K F z)
          = algebraMap F FE c • D E FE (algebraMap F FE z) := by
        intro c z
        rw [LinearMap.map_smul, KaehlerDifferential.map_D, algebraMap_smul]
      have hmap : algebraMap F FE a • D E FE (algebraMap F FE x)
          = algebraMap F FE fu • D E FE (algebraMap F FE u.uniformizer) := by
        rw [← h1, ← h1, ← hωa, ← Place.dCoord_eq, ← hωu]
      have hreg : algebraMap F FE a * coeffDer v (algebraMap F FE x)
          = algebraMap F FE fu * coeffDer v (algebraMap F FE u.uniformizer) := by
        have h2 := congrArg v.differentialCoeff hmap
        rwa [Place.differentialCoeff_smul, Place.differentialCoeff_smul] at h2
      refine mul_mem hLg ?_
      rw [hreg]
      refine mul_mem ((hmemF fu).1 hfu) ?_
      rw [coeffDer_apply]
      exact differentialCoeff_D_mem v ((hmemF _).1 (Place.uniformizer_mem_toValuationSubring u))

  have hsupp : Function.support (kaehlerResidueTerm (bE 0)
      (diagonalHom E FE (Θ g / g * algebraMap F FE a * h))) ⊆ ↑S := by
    intro v hv
    by_contra hvS
    exact hv (hT_off v (by simpa using hvS))
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_congr rfl hT_on,
    Finset.sum_neg_distrib, neg_eq_zero] at hRT'
  exact hRT'

end Main

end AlgebraicCurve

namespace AlgebraicCurve

open AlgebraicCurve in
/-- The wrapper's headline: the trace sum of the residue theorem along a finite cover. -/
theorem Differential.sum_ord_smul_pullbackAlong_eq_zero
    (K F E FE : Type*) [Field K] [Field F] [Field E] [Field FE]
    [Algebra K F] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
    [IsScalarTower K E FE] [IsScalarTower K F FE]
    [IsAlgClosed K] [CharZero K] [IsAlgClosed E]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    [IsCurveOver K F] [IsCurveOver E FE]
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (g : FE) (hg : g ≠ 0)
    (S : Finset (Place E FE)) (y : Place E FE → (F →ₐ[K] E))
    (hS : ∀ P ∈ S, ∀ f : F,
      P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (y P f)) < 1)
    (hrat : ∀ P : Place E FE, P ∉ S → P.ord g ≠ 0 →
      ∃ f : F, algebraMap F FE f ∉ P.toValuationSubring)
    (ω : Ω[F⁄K]) (hω : ω ∈ regularDifferentials K F) :
    ∑ P ∈ S, (P.ord g) • Differential.pullbackAlong (y P) ω = 0 :=
  main K F E FE hfg hfgE hgen g hg S y hS hrat ω hω

end AlgebraicCurve
