/-
SET-1 gateway 1: the `IsogenyEndDatum` column "every nonzero endomorphism of the
formal group is the `pointEnd` of some isogeny datum".

Canonical sources: the pinned FLT `aa2d8b3`
`Theorems/Thm_WeierstrassCurve_Affine_IsogenyEndDatum_exists_pointEnd_eq_of_mem_isogenyEndSubring.lean`
(the statement authority for the headline) and
`P2M/Sol/S_WeierstrassCurve_Affine_IsogenyEndDatum_exists_pointEnd_eq_of_mem_isogenyEndSubring.lean`
(the proof, and the statement authority for the helper declarations the wrappers do
not carry).  Statements are transcribed verbatim; only the proof bodies are adapted
to mathlib `v4.34.0`.

What this module carries, and what it drops:

* the headline `IsogenyEndDatum.exists_pointEnd_eq_of_mem_isogenyEndSubring`, public;
* the pin's helper surface that the port's H5 engine does not already provide:
  `AlgebraicCurve.InertiaDegComp`, `AlgebraicCurve.Place.restrictInclusionAlong`,
  `...restrictResidueMapAlong`, `AlgebraicCurve.Pic0.pushforwardAlongHom_comp_apply`,
  the `IsogenyEndDatum` closure block (`isIntegral_comp_ι`, the private `comp`,
  `comp_pointEnd`, `geomMorph_compDatum`, `geomMorph_add_geomMorph_zero`,
  `geomMorph_sub`, `compDatum_pointEnd`, `mul_mem_range_pointEnd`,
  `one_mem_range_pointEnd`), the submonoid bridge (`isogenyEndSubmonoid`,
  `coe_isogenyEndSubmonoid`, `submonoid_closure_range_pointEnd`,
  `coe_submonoid_closure_range_pointEnd`,
  `mem_isogenyEndSubring_iff_mem_addSubgroup_closure`), and the `ModularCurve`
  foundation (`KwIsogenyEndDatumOfNonzeroEnd`, `Es1a1.es1a4_negDatum_pointEnd`,
  `kw_neg_mem_range_pointEnd`,
  `kw_zero_or_mem_range_pointEnd_of_mem_addSubgroup_closure`,
  `kw_isogenyEndDatumOfNonzeroEnd_of_addDatumSupply`);
* dropped as already present in the port (see the friction log and the checker
  report): the pin's `Divisor.pushforwardAlong_pushforwardAlong'` (private in the
  pin) is the port's public hypothesis-free
  `AlgebraicCurve.Divisor.pushforwardAlong_pushforwardAlong`
  (`AlgebraicCurve/WeilExchange/Transport.lean`), so the primed copy is not
  redeclared; the pin's three `scoped instance instFactNatPrime{2,3,7}_s13e2` are
  invisible to the statement checker (`DECL_RE` does not match `scoped instance`)
  and are not needed by the proof.  `IsogenyEndDatum.pointEnd'`,
  `normFormulaAlong_auto`, `geomMorph`, `placeOfPoint_geomMorph`, `compDatum`,
  `idDatum`, `idDatum_pointEnd`, `isIntegral_comp`, `finiteAlong_comp`,
  `es1a3_compDatum_pointEnd` and `exists_pointEnd_eq_add` belong to the ported H5
  engine (`IsogenyEndDatum/Engine.lean`, `DualEndData.lean`, `Vocabulary.lean`) and
  are imported, not redeclared.

Assumes from lower modules: `IsogenyEndDatum/Engine.lean` (the point-end engine),
`IsogenyEndDatum/Vocabulary.lean` (which carries
`IsogenyEndDatum.exists_pointEnd_eq_add`, used by the headline),
`WeierstrassCurve/Place/CoordinateRingDedekind.lean` (the shared coordinate-ring
pair), `WeierstrassCurve/Isogeny/ConditionalCurrency.lean` (`isogenyEndSubring`) and
`AlgebraicCurve/WeilExchange/Transport.lean` (the `Divisor.pushforwardAlong`
composite).  The work order names only `Engine` and `CoordinateRingDedekind`; the
extra `Vocabulary` import is required because the pin's `solution` invokes
`exists_pointEnd_eq_add`, which lives there.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_Affine_IsogenyEndDatum_exists_pointEnd_eq_of_mem_isogenyEndSubring.lean>
-/
import FLTForHuman.WeierstrassCurve.IsogenyEndDatum.Engine
import FLTForHuman.WeierstrassCurve.IsogenyEndDatum.Vocabulary
import FLTForHuman.WeierstrassCurve.Place.CoordinateRingDedekind
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

universe u

/-! ## The algebraic-curve side: the inertia-degree composite and the two `Along` maps -/

section InertiaDegComp

namespace AlgebraicCurve

variable {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F'']
  [Algebra K F] [Algebra K F'] [Algebra K F'']
variable (φ : F →ₐ[K] F') (χ : F' →ₐ[K] F'')

/-- The pin's `InertiaDegComp`: the multiplicativity of the inertia degree along a
composite of algebras. -/
def InertiaDegComp (hφ : φ.toRingHom.IsIntegral) (hχ : χ.toRingHom.IsIntegral)
    (hχφ : (χ.comp φ).toRingHom.IsIntegral) : Prop :=
  ∀ W : Place K F'',
    W.inertiaDegAlong (χ.comp φ) hχφ
      = W.inertiaDegAlong χ hχ * (W.restrictAlong χ hχ).inertiaDegAlong φ hφ

end AlgebraicCurve

end InertiaDegComp

section AlongMaps

namespace AlgebraicCurve

namespace Place

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

/-- The pin's `restrictInclusionAlong`, the `Place.restrictInclusion` of the place
restriction along `φ`. -/
def restrictInclusionAlong (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') :
    (w.restrictAlong φ hφ).toValuationSubring →+* w.toValuationSubring :=
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  Place.restrictInclusion F w

/-- The pin's `restrictResidueMapAlong`, the residue-field map of
`restrictInclusionAlong`. -/
def restrictResidueMapAlong (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') :
    (w.restrictAlong φ hφ).ResidueField →+* w.ResidueField :=
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  Place.restrictResidueMap F w

end Place

end AlgebraicCurve

end AlongMaps

section PushforwardAlongHomComp

namespace AlgebraicCurve

namespace Pic0

variable {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F'']
variable [Algebra K F] [Algebra K F'] [Algebra K F'']
variable (φ : F →ₐ[K] F') (χ : F' →ₐ[K] F'')
variable (hφ : φ.toRingHom.IsIntegral) (hχ : χ.toRingHom.IsIntegral)
variable (hχφ : (χ.comp φ).toRingHom.IsIntegral)
variable (hfinφ : FiniteAlong K φ) (hfinχ : FiniteAlong K χ) (hfinχφ : FiniteAlong K (χ.comp φ))
variable (hNφ : NormFormulaAlong K φ hfinφ) (hNχ : NormFormulaAlong K χ hfinχ)
variable (hNχφ : NormFormulaAlong K (χ.comp φ) hfinχφ)

/-- The pin's `Pic0.pushforwardAlongHom_comp_apply`: the composite of the `Pic0`
pushforwards is the pushforward of the composite.  The pin derives it from its
private `Divisor.pushforwardAlong_pushforwardAlong'`; the port's public
hypothesis-free `Divisor.pushforwardAlong_pushforwardAlong` has the same statement.
-/
theorem pushforwardAlongHom_comp_apply (c : Pic0 K F'') :
    Pic0.pushforwardAlongHom (χ.comp φ) hχφ hfinχφ hNχφ c
      = Pic0.pushforwardAlongHom φ hφ hfinφ hNφ
          (Pic0.pushforwardAlongHom χ hχ hfinχ hNχ c) := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective c
  rw [Pic0.pushforwardAlongHom_mk, Pic0.pushforwardAlongHom_mk, Pic0.pushforwardAlongHom_mk]
  exact congrArg Pic0.mk (Subtype.ext
    (Divisor.pushforwardAlong_pushforwardAlong φ χ hφ hχ hχφ D).symm)

end Pic0

end AlgebraicCurve

end PushforwardAlongHomComp

/-! ## The `IsogenyEndDatum` closure block -/

section IsogenyEndClosure

namespace WeierstrassCurve

namespace Affine

namespace IsogenyEndDatum

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable {W : Affine F} [W.IsElliptic]
variable [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W] [AbelTheorem W]

/-- The pin's `isIntegral_comp_ι`: integrality of the composite endomorphism. -/
theorem isIntegral_comp_ι (D₁ D₂ : IsogenyEndDatum W) :
    (D₂.ι.comp D₁.ι).toRingHom.IsIntegral :=
  isIntegral_comp W D₁ D₂

/-- The pin's private `IsogenyEndDatum.comp`, the composite datum. -/
private def comp (D₁ D₂ : IsogenyEndDatum W) : IsogenyEndDatum W where
  ι := D₂.ι.comp D₁.ι
  hι := isIntegral_comp_ι D₁ D₂
  hfin := finiteAlong_comp W D₁ D₂

/-- The pin's `comp_pointEnd`: the point end of the composite datum is the product
of the point ends. -/
theorem comp_pointEnd (D₁ D₂ : IsogenyEndDatum W) :
    (D₁.comp D₂).pointEnd' = D₁.pointEnd' * D₂.pointEnd' :=
  ModularCurve.Es1a1.es1a3_compDatum_pointEnd D₁ D₂

/-- The pin's `geomMorph_compDatum`: `geomMorph` composes contravariantly. -/
theorem geomMorph_compDatum (D₁ D₂ : IsogenyEndDatum W) (P : W.Point) :
    (compDatum W D₁ D₂).geomMorph P = D₁.geomMorph (D₂.geomMorph P) := by
  refine placeOfPoint_injective ?_
  rw [← placeOfPoint_geomMorph, ← placeOfPoint_geomMorph, ← placeOfPoint_geomMorph]
  exact Place.restrictAlong_comp D₁.ι D₂.ι D₁.hι D₂.hι (compDatum W D₁ D₂).hι (placeOfPoint P)

/-- The pin's `geomMorph_add_geomMorph_zero`. -/
theorem geomMorph_add_geomMorph_zero (D : IsogenyEndDatum W) (P Q : W.Point) :
    D.geomMorph (P + Q) + D.geomMorph 0 = D.geomMorph P + D.geomMorph Q := by
  rw [geomMorph_eq_pointEnd_add_geomMorph_zero D (P + Q),
    geomMorph_eq_pointEnd_add_geomMorph_zero D P,
    geomMorph_eq_pointEnd_add_geomMorph_zero D Q,
    show D.pointEnd' (P + Q) = D.pointEnd' P + D.pointEnd' Q from map_add _ P Q]
  abel

/-- The pin's `geomMorph_sub`. -/
theorem geomMorph_sub (D : IsogenyEndDatum W) (P Q : W.Point) :
    D.geomMorph (P - Q) = D.geomMorph P - D.geomMorph Q + D.geomMorph 0 := by
  have h := geomMorph_add_geomMorph_zero D (P - Q) Q
  rw [sub_add_cancel] at h
  rw [eq_sub_of_add_eq h.symm, add_sub_right_comm]

/-- The pin's `compDatum_pointEnd`: the point end of the composite datum is the
product of the point ends. -/
theorem compDatum_pointEnd (D₁ D₂ : IsogenyEndDatum W) :
    (compDatum W D₁ D₂).pointEnd' = D₁.pointEnd' * D₂.pointEnd' :=
  ModularCurve.Es1a1.es1a3_compDatum_pointEnd D₁ D₂

/-- The pin's `mul_mem_range_pointEnd`: the range of `pointEnd'` is closed under
multiplication. -/
theorem mul_mem_range_pointEnd {f g : AddMonoid.End W.Point}
    (hf : f ∈ Set.range (IsogenyEndDatum.pointEnd' (W := W)))
    (hg : g ∈ Set.range (IsogenyEndDatum.pointEnd' (W := W))) :
    f * g ∈ Set.range (IsogenyEndDatum.pointEnd' (W := W)) := by
  obtain ⟨D₁, rfl⟩ := hf
  obtain ⟨D₂, rfl⟩ := hg
  exact ⟨D₁.comp D₂, comp_pointEnd D₁ D₂⟩

/-- The pin's `one_mem_range_pointEnd`: the identity endomorphism is a point end. -/
theorem one_mem_range_pointEnd :
    (1 : AddMonoid.End W.Point) ∈ Set.range (IsogenyEndDatum.pointEnd' (W := W)) :=
  ⟨idDatum W, idDatum_pointEnd W⟩

end IsogenyEndDatum

end Affine

end WeierstrassCurve

end IsogenyEndClosure

/-! ## The submonoid bridge -/

section IsogenyEndSubmonoid

namespace WeierstrassCurve

namespace Affine

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable (W : Affine F) [W.IsElliptic]
variable [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W] [AbelTheorem W]

/-- The pin's `isogenyEndSubmonoid`: the range of `pointEnd'`, as a submonoid. -/
def isogenyEndSubmonoid : Submonoid (AddMonoid.End W.Point) where
  carrier := Set.range (IsogenyEndDatum.pointEnd' (W := W))
  one_mem' := IsogenyEndDatum.one_mem_range_pointEnd
  mul_mem' := IsogenyEndDatum.mul_mem_range_pointEnd

/-- The pin's `coe_isogenyEndSubmonoid`. -/
@[scoped simp] theorem coe_isogenyEndSubmonoid :
    (isogenyEndSubmonoid W : Set (AddMonoid.End W.Point))
      = Set.range (IsogenyEndDatum.pointEnd' (W := W)) := rfl

/-- The pin's `submonoid_closure_range_pointEnd`. -/
theorem submonoid_closure_range_pointEnd :
    Submonoid.closure (Set.range (IsogenyEndDatum.pointEnd' (W := W)))
      = isogenyEndSubmonoid W := by
  rw [← coe_isogenyEndSubmonoid]; exact Submonoid.closure_eq _

/-- The pin's `coe_submonoid_closure_range_pointEnd`. -/
theorem coe_submonoid_closure_range_pointEnd :
    (Submonoid.closure (Set.range (IsogenyEndDatum.pointEnd' (W := W)))
        : Set (AddMonoid.End W.Point))
      = Set.range (IsogenyEndDatum.pointEnd' (W := W)) :=
  congrArg SetLike.coe (submonoid_closure_range_pointEnd W)

/-- The pin's `mem_isogenyEndSubring_iff_mem_addSubgroup_closure`: the subring the
headline's hypothesis speaks about has the same elements as the additive closure of
the range of `pointEnd'`. -/
theorem mem_isogenyEndSubring_iff_mem_addSubgroup_closure {f : AddMonoid.End W.Point} :
    f ∈ isogenyEndSubring W (fun D => D.normFormulaAlong_auto) ↔
      f ∈ AddSubgroup.closure (Set.range (IsogenyEndDatum.pointEnd' (W := W))) := by
  rw [show f ∈ isogenyEndSubring W (fun D => D.normFormulaAlong_auto) ↔
      f ∈ Subring.closure (Set.range (IsogenyEndDatum.pointEnd' (W := W))) from Iff.rfl,
    Subring.mem_closure_iff, coe_submonoid_closure_range_pointEnd]

end Affine

end WeierstrassCurve

end IsogenyEndSubmonoid

/-! ## The `ModularCurve` foundation -/

section NegDatum

namespace ModularCurve

namespace Es1a1

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable (W : Affine F) [W.IsElliptic]
variable [WeierstrassCurve.Affine.GenusOnePlaceGate W]
variable [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W]

/-- The pin's `es1a4_negDatum_pointEnd`: the negation datum's point end is `-1`. -/
theorem es1a4_negDatum_pointEnd : (es1a4_negDatum W).pointEnd' = -1 := by
  refine AddMonoidHom.ext fun P => ?_
  exact (es1a4_negDatum W).pointEnd'_eq_of_seam (fun Q => -Q) _root_.neg_zero
    (fun Q => es1a4_negDatum_seam Q) P

end Es1a1

end ModularCurve

end NegDatum

section KwFoundation

namespace ModularCurve

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]

/-- The pin's `KwIsogenyEndDatumOfNonzeroEnd`: the gateway-1 conclusion, as a `Prop`
about the `pointEnd'` spelling of the endomorphism ring. -/
abbrev KwIsogenyEndDatumOfNonzeroEnd (W : Affine F) [W.IsElliptic]
    [WeierstrassCurve.Affine.GenusOnePlaceGate W]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W]
    [WeierstrassCurve.Affine.AbelTheorem W] : Prop :=
  ∀ ψ ∈ isogenyEndSubring W (fun D => D.normFormulaAlong_auto), ψ ≠ 0 →
    ∃ D' : IsogenyEndDatum W, D'.pointEnd' = ψ

variable (W : Affine F) [W.IsElliptic]
variable [WeierstrassCurve.Affine.GenusOnePlaceGate W]
variable [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W]

/-- The pin's `kw_neg_mem_range_pointEnd`: the range of `pointEnd'` is closed under
negation. -/
theorem kw_neg_mem_range_pointEnd {f : AddMonoid.End W.Point}
    (hf : f ∈ Set.range (IsogenyEndDatum.pointEnd' (W := W))) :
    -f ∈ Set.range (IsogenyEndDatum.pointEnd' (W := W)) := by
  obtain ⟨D, rfl⟩ := hf
  refine ⟨IsogenyEndDatum.compDatum W (Es1a1.es1a4_negDatum W) D, ?_⟩
  rw [IsogenyEndDatum.compDatum_pointEnd, Es1a1.es1a4_negDatum_pointEnd]
  exact neg_one_mul D.pointEnd'

/-- The pin's `kw_zero_or_mem_range_pointEnd_of_mem_addSubgroup_closure`: every
element of the additive closure of the range of `pointEnd'` is either zero or in
the range. -/
theorem kw_zero_or_mem_range_pointEnd_of_mem_addSubgroup_closure
    (hadd : KwIsogenyEndAddDatumSupply W) {ψ : AddMonoid.End W.Point}
    (hψ : ψ ∈ AddSubgroup.closure (Set.range (IsogenyEndDatum.pointEnd' (W := W)))) :
    ψ = 0 ∨ ψ ∈ Set.range (IsogenyEndDatum.pointEnd' (W := W)) := by
  refine AddSubgroup.closure_induction ?_ ?_ ?_ ?_ hψ
  · exact fun y hy => Or.inr hy
  · exact Or.inl rfl
  · rintro x y - - (rfl | ⟨D₁, rfl⟩) hy
    · simpa using hy
    · rcases hy with rfl | ⟨D₂, rfl⟩
      · exact Or.inr ⟨D₁, (add_zero _).symm⟩
      · by_cases h0 : D₁.pointEnd' + D₂.pointEnd' = 0
        · exact Or.inl h0
        · exact Or.inr (hadd D₁ D₂ h0)
  · rintro x - (rfl | hx)
    · exact Or.inl _root_.neg_zero
    · exact Or.inr (kw_neg_mem_range_pointEnd W hx)

/-- The pin's `kw_isogenyEndDatumOfNonzeroEnd_of_addDatumSupply`: the additive supply
implies gateway 1 in the `pointEnd'` spelling. -/
theorem kw_isogenyEndDatumOfNonzeroEnd_of_addDatumSupply
    (hadd : KwIsogenyEndAddDatumSupply W) :
    KwIsogenyEndDatumOfNonzeroEnd W := by
  intro ψ hψ hne
  have hcl := (mem_isogenyEndSubring_iff_mem_addSubgroup_closure W).mp hψ
  rcases kw_zero_or_mem_range_pointEnd_of_mem_addSubgroup_closure W hadd hcl with h0 | hD
  · exact absurd h0 hne
  · exact hD

end ModularCurve

end KwFoundation

/-! ## The headline -/

namespace WeierstrassCurve

namespace Affine

namespace IsogenyEndDatum

/-- The pin's `WeierstrassCurve.Affine.IsogenyEndDatum.exists_pointEnd_eq_of_mem_isogenyEndSubring`
(the gateway-1 headline): every nonzero endomorphism in `isogenyEndSubring W hNs` is
the `pointEnd` of some isogeny datum. -/
theorem exists_pointEnd_eq_of_mem_isogenyEndSubring
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    {W : WeierstrassCurve.Affine F} [W.IsElliptic]
    [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W] [AbelTheorem W]
    (hNs : ∀ D : IsogenyEndDatum W, NormFormulaAlong F D.ι D.hfin)
    (ψ : AddMonoid.End W.Point) (hψ : ψ ∈ isogenyEndSubring W hNs) (hne : ψ ≠ 0) :
    ∃ D : IsogenyEndDatum W, D.pointEnd (hNs D) = ψ := by
  have hadd : ModularCurve.KwIsogenyEndAddDatumSupply W := by
    intro D₁ D₂ h0
    obtain ⟨D₃, hN₃, h3⟩ :=
      IsogenyEndDatum.exists_pointEnd_eq_add D₁ (hNs D₁) D₂ (hNs D₂) h0
    exact ⟨D₃, h3⟩
  exact ModularCurve.kw_isogenyEndDatumOfNonzeroEnd_of_addDatumSupply W hadd ψ hψ hne

end IsogenyEndDatum

end Affine

end WeierstrassCurve
