/-
Regular prolongations and their place map.

Three rows of the regular-prolongation theory — the `AlgebraicCurve` machinery that realises a
place of the base-extended function field as a valuation on a ring of integral elements:

* `exists_regularProlongation_retraction_of_constantField_valuationSubring` — a retraction of
  the regular-prolongation map onto the constant field's valuation subring, for an algebraically
  closed base;
* `RegularProlongation.exists_of_forall_mem_adjoin_iff_of_isAlgebraic` — the **adjoin criterion**:
  a regular prolongation exists as soon as every element of an adjoin-generated intermediate
  field is integral at the place, in the *iff* form a caller needs;
* `exists_placeMap_mapDomain_eq_ord_of_good_constantReduction` — at a good constant reduction,
  the place map's underlying map agrees with the order, which is how a place propagates from the
  special fibre back to the generic one.

The engine is `AlgebraicCurve/RegularProlongation*.lean` (`RegularProlongation.lean` for the
construction, `…ResidueIntegralClosure`/`…PlaceMapOrd` for the two named premises), the constant
field extension of a curve (`IsCurveOver/ConstantFieldExtension.lean`), the valued-field toolbox
`FieldTheory/ValuationSubringValuedField.lean` (SET-AF103E), and the Chevalley extension
(`RingTheory/Valuation/ChevalleyExtension.lean`).

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_exists_regularProlongation_retraction_of_constantField_valuationSubring.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_of_forall_mem_adjoin_iff_of_isAlgebraic.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_exists_placeMap_mapDomain_eq_ord_of_good_constantReduction.lean>

spec-pin: Theorems/Thm_AlgebraicCurve_exists_regularProlongation_retraction_of_constantField_valuationSubring.lean
spec-pin: Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_of_forall_mem_adjoin_iff_of_isAlgebraic.lean
spec-pin: Theorems/Thm_AlgebraicCurve_exists_placeMap_mapDomain_eq_ord_of_good_constantReduction.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_exists_regularProlongation_retraction_of_constantField_valuationSubring.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_RegularProlongation_exists_of_forall_mem_adjoin_iff_of_isAlgebraic.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_exists_placeMap_mapDomain_eq_ord_of_good_constantReduction.lean

PORT NOTES (SET-AF105C).

* **Substitutions**: `port_advise` found the three headlines themselves already in the port — as
  the scaffolds' own `sorry`-bodied statements — and no engine row of these three rows: the
  300-row and the 59-row are single-declaration assembly over ported premises, and the 221-row's
  fourteen declarations are new (transcribed at the pin's names, in the subject namespace
  `AlgebraicCurve.RegularProlongation.AdjoinCriterion`).
* The pin's `p2m_open`/`p2m_export`/`p2m_reactivate` staging is dropped (the port opens the
  namespaces it needs directly); the generated inner namespace label
  `SolExistsOfForallMemAdjoinIffOfIsAlgebraic` becomes that subject namespace. The 59-row's pin
  `attribute [-instance]` / `[-simp]` walls and `import Mathlib` are *not* transcribed.
* **300-row**: the pin wraps its proof in `set_option maxHeartbeats 6400000`; that line is not
  transcribed (house policy) and the module needs no ladder at all — the pinned declaration
  elaborates inside the edit loop's 200 k cap. Measured pair, recorded and **not installed**:
  the whole module is silent at `-DmaxHeartbeats=80000` and first fails at `60000`, on this
  row's headline — `…:335:0: (deterministic) timeout at whnf, maximum number of heartbeats
  (60000)`. So the pin's 6.4 M ceiling was ~32× its need on the port's import graph (a
  Mathlib-wide instance search, not a spread-cost defect); the module carries no
  `set_option maxHeartbeats` / `synthInstance.maxHeartbeats` of its own. The pin's
  `import Mathlib` is replaced by the ported premise modules plus the tensor-product/algebra
  modules below.
* The pin's `residueFieldAlgebra` keeps its `@[reducible]`; the two `letI`-in-a-`Prop`
  declarations carry `set_option linter.style.haveILetI false in` (the port's idiom, not the
  pin's) so that the module reads silent at the edit loop.
-/
import FLTForHuman.AlgebraicCurve.IsCurveOver.ConstantFieldExtension
import FLTForHuman.AlgebraicCurve.RegularProlongation
import FLTForHuman.AlgebraicCurve.RegularProlongationPlaceMapOrd
import FLTForHuman.AlgebraicCurve.RegularProlongationResidueIntegralClosure
import FLTForHuman.FieldTheory.ValuationSubringValuedField
import FLTForHuman.RingTheory.Valuation.ChevalleyExtension
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section

namespace AlgebraicCurve

namespace RegularProlongation

namespace AdjoinCriterion

open IsLocalRing Polynomial

section Units

variable {F : Type*} [Field F]

theorem inv_mem_of_isUnit {V : ValuationSubring F} {x : F} {hx : x ∈ V}
    (hu : IsUnit (⟨x, hx⟩ : V)) : x⁻¹ ∈ V := by
  obtain ⟨y, hy⟩ := hu.exists_right_inv
  have hxy : x * (y : F) = 1 := by
    have := congrArg (fun z : V => (z : F)) hy
    simpa using this
  have : (y : F) = x⁻¹ := eq_inv_of_mul_eq_one_right hxy
  rw [← this]
  exact y.2

theorem isUnit_of_inv_mem {V : ValuationSubring F} {x : F} (hx : x ∈ V) (hx0 : x ≠ 0)
    (hinv : x⁻¹ ∈ V) : IsUnit (⟨x, hx⟩ : V) :=
  IsUnit.of_mul_eq_one (⟨x⁻¹, hinv⟩ : V) (Subtype.ext (mul_inv_cancel₀ hx0))

end Units

section Constants

variable {L : Type*} [Field L] (A : ValuationSubring L)
  {F : Type*} [Field F] [Algebra L F]
  (V : ValuationSubring F) (hV : ∀ x : L, algebraMap L F x ∈ V ↔ x ∈ A)

def toV : A →+* V where
  toFun a := ⟨algebraMap L F a, (hV a).mpr a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

@[scoped simp] theorem coe_toV (a : A) : ((toV A V hV a : V) : F) = algebraMap L F a := rfl

theorem isLocalHom_toV : IsLocalHom (toV A V hV) := by
  constructor
  intro a hu
  by_cases ha0 : (a : L) = 0
  · exfalso
    have h0 : toV A V hV a = 0 := Subtype.ext (by simp [ha0])
    rw [h0] at hu
    exact not_isUnit_zero hu
  · have hinvF : (algebraMap L F a)⁻¹ ∈ V := inv_mem_of_isUnit hu
    rw [← map_inv₀] at hinvF
    have hinvA : (a : L)⁻¹ ∈ A := (hV _).mp hinvF
    have : IsUnit (⟨(a : L), a.2⟩ : A) := isUnit_of_inv_mem a.2 ha0 hinvA
    simpa using this

theorem coe_eval_map_toV (P : A[X]) (x : V) :
    (((P.map (toV A V hV)).eval x : V) : F) =
      P.eval₂ ((algebraMap L F).comp A.subtype) (x : F) := by
  rw [Polynomial.eval_map]
  have h := Polynomial.hom_eval₂ P (toV A V hV) V.subtype x
  have hcomp : V.subtype.comp (toV A V hV) = (algebraMap L F).comp A.subtype := by
    ext a
    rfl
  rw [hcomp] at h
  exact h

theorem residue_eval_map_toV {E : Type*} [Field E] [Algebra (ResidueField A) E]
    (ρ : V →+* E)
    (hρ : ∀ a : A, ρ (toV A V hV a) = algebraMap (ResidueField A) E (IsLocalRing.residue A a))
    (P : A[X]) (x : V) :
    ρ ((P.map (toV A V hV)).eval x) = aeval (ρ x) (P.map (IsLocalRing.residue A)) := by
  rw [Polynomial.eval_map, Polynomial.hom_eval₂, Polynomial.aeval_def, Polynomial.eval₂_map]
  congr 1
  ext a
  simp [hρ]

theorem eval₂_mem_adjoin (P : A[X]) (x : F) :
    P.eval₂ ((algebraMap L F).comp A.subtype) x ∈ IntermediateField.adjoin L ({x} : Set F) := by
  have h : P.eval₂ ((algebraMap L F).comp A.subtype) x = aeval x (P.map A.subtype) := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
  rw [h]
  exact IntermediateField.algebra_adjoin_le_adjoin L _ (Polynomial.aeval_mem_adjoin_singleton L x)

end Constants

section Setting

variable {L : Type*} [Field L] {A : ValuationSubring L}
  {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
  (R : RegularProlongation A F Fbar) {f : F} (hfO : f ∈ R.integers)
  {W : ValuationSubring F}
  (hW : ∀ e : F, e ∈ IntermediateField.adjoin L ({f} : Set F) → (e ∈ W ↔ e ∈ R.integers))

include hW in

theorem algebraMap_mem_W_iff (x : L) : algebraMap L F x ∈ W ↔ x ∈ A :=
  (hW _ (IntermediateField.algebraMap_mem _ x)).trans (R.algebraMap_mem_iff x)

include hW hfO in

theorem f_mem_W : f ∈ W :=
  (hW f (IntermediateField.mem_adjoin_simple_self L f)).mpr hfO

@[reducible] noncomputable def residueFieldAlgebra : Algebra (ResidueField A) (ResidueField W) :=
  (@ResidueField.map A W _ _ _ _ (toV A W (algebraMap_mem_W_iff R hW))
    (isLocalHom_toV A W (algebraMap_mem_W_iff R hW))).toAlgebra

set_option linter.style.haveILetI false in
theorem residue_toV_eq (a : A) :
    letI := residueFieldAlgebra R hW
    IsLocalRing.residue W (toV A W (algebraMap_mem_W_iff R hW) a) =
      algebraMap (ResidueField A) (ResidueField W) (IsLocalRing.residue A a) := by
  letI := residueFieldAlgebra R hW
  show IsLocalRing.residue W (toV A W (algebraMap_mem_W_iff R hW) a) =
    @ResidueField.map A W _ _ _ _ (toV A W (algebraMap_mem_W_iff R hW))
      (isLocalHom_toV A W (algebraMap_mem_W_iff R hW)) (IsLocalRing.residue A a)
  exact (@ResidueField.map_residue A W _ _ _ _ (toV A W (algebraMap_mem_W_iff R hW))
    (isLocalHom_toV A W (algebraMap_mem_W_iff R hW)) a).symm

include hfO hW in

theorem transcendental_residue_W [Algebra (ResidueField A) (ResidueField W)]
    (hcompat : ∀ a : A, IsLocalRing.residue W (toV A W (algebraMap_mem_W_iff R hW) a) =
      algebraMap (ResidueField A) (ResidueField W) (IsLocalRing.residue A a))
    (htr : Transcendental (ResidueField A) (R.residue ⟨f, hfO⟩)) :
    Transcendental (ResidueField A) (IsLocalRing.residue W ⟨f, f_mem_W R hfO hW⟩) := by
  rw [transcendental_iff]
  intro p hp
  obtain ⟨P, rfl⟩ :=
    Polynomial.map_surjective (IsLocalRing.residue A) IsLocalRing.residue_surjective p

  set hOW := algebraMap_mem_W_iff R hW
  set fW : W := ⟨f, f_mem_W R hfO hW⟩
  set fO : R.integers := ⟨f, hfO⟩
  set yW : W := (P.map (toV A W hOW)).eval fW
  set yO : R.integers := (P.map (toV A R.integers R.algebraMap_mem_iff)).eval fO
  have hyW : (yW : F) = P.eval₂ ((algebraMap L F).comp A.subtype) f :=
    coe_eval_map_toV A W hOW P fW
  have hyO : (yO : F) = P.eval₂ ((algebraMap L F).comp A.subtype) f :=
    coe_eval_map_toV A R.integers R.algebraMap_mem_iff P fO

  have hres_W : IsLocalRing.residue W yW = 0 := by
    rw [residue_eval_map_toV A W hOW (IsLocalRing.residue W) hcompat P fW]
    exact hp
  have hyW_max : yW ∈ maximalIdeal W := (IsLocalRing.residue_eq_zero_iff _).mp hres_W

  by_contra hp0
  have hres_O : R.residue yO ≠ 0 := by
    rw [residue_eval_map_toV A R.integers R.algebraMap_mem_iff R.residue R.residue_algebraMap P fO]
    intro h0
    exact hp0 ((transcendental_iff.mp htr) _ h0)
  have hunitO : IsUnit yO := R.isUnit_of_residue_ne_zero hres_O
  have hy0 : (yO : F) ≠ 0 := by
    intro h0
    apply hres_O
    have : yO = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hinvO : (yO : F)⁻¹ ∈ R.integers := inv_mem_of_isUnit (hx := yO.2) (by simpa using hunitO)
  have hyK : (yO : F) ∈ IntermediateField.adjoin L ({f} : Set F) := by
    rw [hyO]
    exact eval₂_mem_adjoin A P f
  have hinvW : (yO : F)⁻¹ ∈ W := (hW _ (inv_mem hyK)).mpr hinvO
  have hunitW : IsUnit yW := by
    have hcoe : (yW : F) = (yO : F) := by rw [hyW, hyO]
    have h := isUnit_of_inv_mem (V := W) (x := (yO : F)) (hcoe ▸ yW.2) hy0 hinvW
    have hEq : (⟨(yO : F), hcoe ▸ yW.2⟩ : W) = yW := Subtype.ext hcoe.symm
    rwa [hEq] at h
  exact (IsLocalRing.mem_maximalIdeal _).mp hyW_max hunitW

end Setting

end AdjoinCriterion

end RegularProlongation

end AlgebraicCurve

open AlgebraicCurve IsLocalRing

set_option linter.style.haveILetI false in
theorem AlgebraicCurve.RegularProlongation.exists_of_forall_mem_adjoin_iff_of_isAlgebraic
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (f : F) (hfO : f ∈ R.integers)
    (htr : Transcendental (IsLocalRing.ResidueField A) (R.residue ⟨f, hfO⟩))
    [Algebra.IsAlgebraic (IntermediateField.adjoin L ({f} : Set F)) F]
    (W : ValuationSubring F)
    (hW : ∀ e : F, e ∈ IntermediateField.adjoin L ({f} : Set F) → (e ∈ W ↔ e ∈ R.integers)) :
    ∃ (_ : Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField W))
      (R' : RegularProlongation A F (IsLocalRing.ResidueField W)),
      R'.integers = W ∧ ∃ hf' : f ∈ R'.integers,
        Transcendental (IsLocalRing.ResidueField A) (R'.residue ⟨f, hf'⟩) := by
  letI := AlgebraicCurve.RegularProlongation.AdjoinCriterion.residueFieldAlgebra R hW
  have hOW := AlgebraicCurve.RegularProlongation.AdjoinCriterion.algebraMap_mem_W_iff R hW
  have hfW : f ∈ W := AlgebraicCurve.RegularProlongation.AdjoinCriterion.f_mem_W R hfO hW
  have hcompat := AlgebraicCurve.RegularProlongation.AdjoinCriterion.residue_toV_eq R hW
  have htrW : Transcendental (ResidueField A) (IsLocalRing.residue W ⟨f, hfW⟩) :=
    AlgebraicCurve.RegularProlongation.AdjoinCriterion.transcendental_residue_W R hfO hW hcompat htr
  have hreg : ∀ g : F, g ≠ 0 → ∃ c : L, ∃ h : c • g ∈ W, IsLocalRing.residue W ⟨c • g, h⟩ ≠ 0 :=
    fun g hg =>
      ValuationSubring.exists_smul_mem_of_transcendental_residue A W hOW (IsLocalRing.residue W)
        IsLocalRing.ker_residue hcompat f hfW htrW g hg
  refine ⟨AlgebraicCurve.RegularProlongation.AdjoinCriterion.residueFieldAlgebra R hW,
    { integers := W
      residue := IsLocalRing.residue W
      algebraMap_mem_iff := hOW
      residue_surjective := IsLocalRing.residue_surjective
      ker_residue := IsLocalRing.ker_residue
      residue_algebraMap := hcompat
      exists_smul_mem := hreg }, rfl, hfW, htrW⟩

open AlgebraicCurve

theorem AlgebraicCurve.exists_placeMap_mapDomain_eq_ord_of_good_constantReduction
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F] [IsCurveOver L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    [IsCurveOver (IsLocalRing.ResidueField A) Fbar]
    (O : ValuationSubring F) (res : O →+* Fbar)
    (hOA : ∀ c : L, algebraMap L F c ∈ O ↔ c ∈ A)
    (hsurj : Function.Surjective res)
    (hker : RingHom.ker res = IsLocalRing.maximalIdeal O)
    (hconst : ∀ a : A, res ⟨algebraMap L F a, (hOA a).mpr a.2⟩ =
      algebraMap (IsLocalRing.ResidueField A) Fbar (IsLocalRing.residue A a))
    (he : ∀ f : F, f ≠ 0 → ∃ c : L, ∃ h : c • f ∈ O, res ⟨c • f, h⟩ ≠ 0)
    (hreg : ∃ x : O, Transcendental (IsLocalRing.ResidueField A) (res x) ∧
      0 < Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({res x} : Set Fbar)) Fbar ∧
      Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
        Module.finrank
          (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({res x} : Set Fbar)) Fbar)
    (hgood : genusFF (IsLocalRing.ResidueField A) Fbar = genusFF L F) :
    ∃ r : Place L F → Place (IsLocalRing.ResidueField A) Fbar,
      ∀ f : O, res f ≠ 0 → ∀ D : Divisor L F, (∀ P, D P = P.ord (f : F)) →
        ∀ Q, Finsupp.mapDomain r D Q = Q.ord (res f) := by
  let R : RegularProlongation A F Fbar :=
    { integers := O
      residue := res
      algebraMap_mem_iff := hOA
      residue_surjective := hsurj
      ker_residue := hker
      residue_algebraMap := hconst
      exists_smul_mem := he }
  obtain ⟨x, hx, hfin, hdeg⟩ := hreg

  have hchart :
      (∀ h : Fbar, IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A) {R.residue x}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (f : F) ∧ R.residue f = h) ∧
      (∀ h : Fbar, IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A) {(R.residue x)⁻¹}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)⁻¹}) (f : F) ∧ R.residue f = h) :=
    RegularProlongation.residue_integralClosure_surjective_of_genusFF_eq
      A R x hx hfin hdeg hgood

  exact
    RegularProlongation.exists_placeMap_mapDomain_eq_ord_of_residue_integralClosure_surjective
      A R x hx hfin hdeg hchart

set_option linter.style.haveILetI false in
theorem AlgebraicCurve.exists_regularProlongation_retraction_of_constantField_valuationSubring
    (K F K' F' : Type*) [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (A : ValuationSubring K') (hK : ∀ c : K, algebraMap K K' c ∈ A) (σ : A →+* K)
    (hker : RingHom.ker σ = IsLocalRing.maximalIdeal A)
    (hsec : ∀ c : K, σ ⟨algebraMap K K' c, hK c⟩ = c) :
    ∃ (O : ValuationSubring F') (ρ : O →+* F),
      (∀ c : K', algebraMap K' F' c ∈ O ↔ c ∈ A) ∧
      RingHom.ker ρ = IsLocalRing.maximalIdeal O ∧
      (∀ a : A, ∃ h : algebraMap K' F' (a : K') ∈ O,
        ρ ⟨algebraMap K' F' (a : K'), h⟩ = algebraMap K F (σ a)) ∧
      (∀ f' : F', f' ≠ 0 → ∃ c : K', ∃ h : c • f' ∈ O, ρ ⟨c • f', h⟩ ≠ 0) ∧
      (∀ f : F, ∃ h : algebraMap F F' f ∈ O, ρ ⟨algebraMap F F' f, h⟩ = f) := by
  classical
  have hσsurj : Function.Surjective σ := fun c ↦ ⟨⟨algebraMap K K' c, hK c⟩, hsec c⟩
  letI : Algebra K A := ((algebraMap K K').codRestrict A.toSubring hK).toAlgebra
  have hσK : ∀ c : K, σ (algebraMap K A c) = c := hsec
  let hAtoF' : A →ₐ[K] F' :=
    { toRingHom := (algebraMap K' F').comp A.subtype
      commutes' := fun c ↦ (IsScalarTower.algebraMap_apply K K' F' c).symm }
  let Φ : TensorProduct K F A →ₐ[K] F' :=
    Algebra.TensorProduct.lift (IsScalarTower.toAlgHom K F F') hAtoF' (fun _ _ ↦ Commute.all _ _)
  have hAtoF'_apply : ∀ a : A, hAtoF' a = algebraMap K' F' (a : K') := fun a ↦ rfl
  let hσAlg : A →ₐ[K] F :=
    { toRingHom := (algebraMap K F).comp σ
      commutes' := fun c ↦ by simp [hσK c] }
  let Ψ : TensorProduct K F A →ₐ[K] F :=
    Algebra.TensorProduct.lift (AlgHom.id K F) hσAlg (fun _ _ ↦ Commute.all _ _)

  have hΦinj : Function.Injective Φ := by
    let e := Module.Basis.ofVectorSpace K F
    have hLD' : LinearIndependent K' (fun i ↦ algebraMap F F' (e i)) :=
      AlgebraicCurve.linearIndependent_of_constantFieldExtension_of_isAlgClosed
        K F K' F' hfg hfg' hgen e.linearIndependent
    let eqv : TensorProduct K F A ≃ₗ[K] _ →₀ A :=
      (LinearEquiv.rTensor A e.repr).trans (TensorProduct.finsuppScalarLeft K A _)
    rw [injective_iff_map_eq_zero]
    intro z hz
    set c := eqv z with hc_def
    have hsingle : ∀ i a, eqv.symm (Finsupp.single i a) = e i ⊗ₜ[K] a := by
      intro i a
      simp only [eqv, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
        TensorProduct.finsuppScalarLeft_symm_apply_single]
      change (LinearEquiv.rTensor A e.repr).symm _ = _
      rw [LinearEquiv.symm_rTensor, LinearEquiv.rTensor_tmul,
        Module.Basis.repr_symm_single_one]
    have key : Φ z = c.sum (fun i a ↦ algebraMap K' F' (a : K') * algebraMap F F' (e i)) := by
      conv_lhs => rw [show z = eqv.symm c from hc_def ▸ (eqv.symm_apply_apply z).symm,
        show c = c.sum Finsupp.single from (Finsupp.sum_single c).symm,
        map_finsuppSum, map_finsuppSum]
      simp only [hsingle, Φ, Algebra.TensorProduct.lift_tmul]
      exact Finsupp.sum_congr fun i a => mul_comm _ _
    have hc2 : (Finsupp.linearCombination K'
        (fun i ↦ algebraMap F F' (e i))) (c.mapRange (↑) (by simp)) = 0 := by
      rw [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (by simp), ← hz, key]
      exact Finsupp.sum_congr fun i _ ↦ by rw [Algebra.smul_def]
    have hcz : c.mapRange ((↑) : A → K') (by simp) = 0 :=
      linearIndependent_iff.mp hLD' _ hc2
    have hc0 : c = 0 := by
      ext i; have := DFunLike.congr_fun hcz i
      simp only [Finsupp.mapRange_apply, Finsupp.coe_zero, Pi.zero_apply] at this
      exact_mod_cast this
    rw [show z = eqv.symm c from hc_def ▸ (eqv.symm_apply_apply z).symm, hc0, map_zero]
  let R : Subring F' := Φ.range.toSubring
  have hFR : ∀ f : F, algebraMap F F' f ∈ R := fun f ↦
    ⟨f ⊗ₜ[K] 1, by simp [Φ, Algebra.TensorProduct.lift_tmul]⟩
  have hAR : ∀ a : A, algebraMap K' F' (a : K') ∈ R := fun a ↦
    ⟨(1 : F) ⊗ₜ[K] a, by simp [Φ, Algebra.TensorProduct.lift_tmul, hAtoF'_apply]⟩
  let eΦ : TensorProduct K F A ≃ₐ[K] Φ.range := AlgEquiv.ofInjective Φ hΦinj
  let φ : R →+* F := Ψ.toRingHom.comp eΦ.symm.toRingHom
  have heΦ : ∀ z, (eΦ z : F') = Φ z := fun z ↦ rfl
  have hφF : ∀ f : F, φ ⟨_, hFR f⟩ = f := by
    intro f
    show Ψ (eΦ.symm ⟨_, hFR f⟩) = f
    have : (⟨_, hFR f⟩ : Φ.range) = eΦ (f ⊗ₜ[K] 1) :=
      Subtype.ext (by simp [heΦ, Φ, Algebra.TensorProduct.lift_tmul])
    rw [this, AlgEquiv.symm_apply_apply]
    simp [Ψ, Algebra.TensorProduct.lift_tmul, hσAlg]
  have hφA : ∀ a : A, φ ⟨_, hAR a⟩ = algebraMap K F (σ a) := by
    intro a
    show Ψ (eΦ.symm ⟨_, hAR a⟩) = _
    have : (⟨_, hAR a⟩ : Φ.range) = eΦ ((1 : F) ⊗ₜ[K] a) :=
      Subtype.ext (by simp [heΦ, Φ, Algebra.TensorProduct.lift_tmul, hAtoF'_apply])
    rw [this, AlgEquiv.symm_apply_apply]
    simp [Ψ, Algebra.TensorProduct.lift_tmul, hσAlg]

  let Ω := AlgebraicClosure F
  let φΩ : R →+* Ω := (algebraMap F Ω).comp φ
  obtain ⟨O, hRO, ψ, hψφ, hψker⟩ :=
    ValuationSubring.exists_ringHom_extend_of_isAlgClosed R φΩ
  have hψF : ∀ f : F, ψ ⟨algebraMap F F' f, hRO (hFR f)⟩ = algebraMap F Ω f := fun f ↦ by
    have := RingHom.congr_fun hψφ ⟨_, hFR f⟩
    simp [φΩ, hφF f] at this
    exact this
  have hψA : ∀ a : A, ψ ⟨algebraMap K' F' (a : K'), hRO (hAR a)⟩ =
      algebraMap F Ω (algebraMap K F (σ a)) := fun a ↦ by
    have := RingHom.congr_fun hψφ ⟨_, hAR a⟩
    simp [φΩ, hφA a] at this
    exact this

  have hOK' : ∀ c : K', algebraMap K' F' c ∈ O ↔ c ∈ A := by
    intro c
    refine ⟨fun hc ↦ ?_, fun hc ↦ hRO (hAR ⟨c, hc⟩)⟩
    by_contra hcA
    have hc0 : c ≠ 0 := fun h ↦ hcA (h ▸ A.zero_mem)
    have hcinvA : c⁻¹ ∈ A := (A.mem_or_inv_mem c).resolve_left hcA

    have hcinvm : (⟨c⁻¹, hcinvA⟩ : A) ∈ maximalIdeal A := by
      rw [mem_maximalIdeal, mem_nonunits_iff]
      intro ⟨u, hu⟩
      apply hcA
      have hcval : ((u⁻¹ : Aˣ) : A).1 = c := by
        have h1 : ((u : A) : K') * ((u⁻¹ : Aˣ) : A).1 = 1 := by
          exact_mod_cast congrArg Subtype.val u.mul_inv
        rw [hu] at h1
        field_simp at h1
        exact h1
      exact hcval ▸ ((u⁻¹ : Aˣ) : A).2
    have hψcinv : ψ ⟨algebraMap K' F' c⁻¹, hRO (hAR ⟨c⁻¹, hcinvA⟩)⟩ = 0 := by
      rw [hψA ⟨c⁻¹, hcinvA⟩]
      have : σ ⟨c⁻¹, hcinvA⟩ = 0 := by rw [← RingHom.mem_ker, hker]; exact hcinvm
      simp [this]
    have hprod : (⟨algebraMap K' F' c⁻¹, hRO (hAR ⟨c⁻¹, hcinvA⟩)⟩ : O) *
        ⟨algebraMap K' F' c, hc⟩ = 1 :=
      Subtype.ext (show algebraMap K' F' c⁻¹ * algebraMap K' F' c = 1 by
        rw [← map_mul, inv_mul_cancel₀ hc0, map_one])
    have := congrArg ψ hprod
    rw [map_mul, hψcinv, zero_mul, map_one] at this
    exact one_ne_zero this.symm
  have hFO : ∀ f : F, algebraMap F F' f ∈ O := fun f ↦ hRO (hFR f)

  have hψR : ∀ r : R, ψ ⟨(r : F'), hRO r.2⟩ = algebraMap F Ω (φ r) := fun r ↦ by
    have := RingHom.congr_fun hψφ r; (simp [φΩ] at this; exact this)

  have hRscale : ∀ r : R, (r : F') ≠ 0 →
      ∃ c : K', c ≠ 0 ∧ ∃ hcr : c • (r : F') ∈ R, φ ⟨c • (r : F'), hcr⟩ ≠ 0 := by
    have hcontent := ValuationSubring.tensorProduct_exists_primitive_factor K F K' A hK σ hker hsec
    intro r hr0
    have hz0 : eΦ.symm r ≠ 0 := fun h ↦ hr0 (by
      have : r = eΦ (eΦ.symm r) := (eΦ.apply_symm_apply r).symm
      rw [this, h, map_zero]; rfl)
    obtain ⟨a, ha0, z', hzeq, hΨz'⟩ := hcontent (eΦ.symm r) hz0
    have hcrΦ : ((a : K'))⁻¹ • (r : F') = Φ z' := by
      have hr : (r : F') = Φ (eΦ.symm r) := by
        change (r : F') = (eΦ (eΦ.symm r) : F'); rw [eΦ.apply_symm_apply]
      rw [hr, hzeq, map_mul, Algebra.smul_def]
      have : Φ ((1 : F) ⊗ₜ[K] a) = algebraMap K' F' (a : K') := by
        simp [Φ, Algebra.TensorProduct.lift_tmul, hAtoF'_apply]
      rw [this, ← mul_assoc, ← map_mul, inv_mul_cancel₀ (by exact_mod_cast ha0), map_one,
        one_mul]
    have hcrR : ((a : K'))⁻¹ • (r : F') ∈ R := hcrΦ ▸ ⟨z', rfl⟩
    refine ⟨((a : K'))⁻¹, inv_ne_zero (by exact_mod_cast ha0), hcrR, ?_⟩
    intro hφ0
    apply hΨz'
    have heq : eΦ.symm ⟨_, hcrR⟩ = z' := by
      apply eΦ.injective; rw [eΦ.apply_symm_apply]; exact Subtype.ext hcrΦ
    rw [← heq]; exact hφ0

  have hFrac : ∀ f' : F', ∃ r s : R, (s : F') ≠ 0 ∧ f' * (s : F') = (r : F') := by
    have htop : Subfield.closure (R : Set F') = ⊤ := by
      have hK'sub : ∀ c : K', algebraMap K' F' c ∈ Subfield.closure (R : Set F') := fun c ↦ by
        rcases A.mem_or_inv_mem c with hc | hc
        · exact Subfield.subset_closure (hAR ⟨c, hc⟩)
        · rcases eq_or_ne c 0 with rfl | hc0
          · simp
          rw [show algebraMap K' F' c = (algebraMap K' F' c⁻¹)⁻¹ by rw [map_inv₀, inv_inv]]
          exact (Subfield.closure _).inv_mem (Subfield.subset_closure (hAR ⟨c⁻¹, hc⟩))
      rw [eq_top_iff]
      intro x _
      have : (IntermediateField.adjoin K' (Set.range (algebraMap F F'))).toSubfield ≤
          Subfield.closure (R : Set F') := by
        rw [IntermediateField.adjoin_toSubfield]
        exact Subfield.closure_le.mpr (Set.union_subset
          (Set.range_subset_iff.mpr hK'sub)
          (Set.range_subset_iff.mpr fun f ↦ Subfield.subset_closure (hFR f)))
      exact this (hgen ▸ trivial)
    intro f'
    have hf' : f' ∈ Subfield.closure (R : Set F') := htop ▸ Subfield.mem_top f'
    rw [Subfield.mem_closure_iff] at hf'
    obtain ⟨y, hy, z, hz, hyz⟩ := hf'
    rw [show Subring.closure (R : Set F') = R from Subring.closure_eq R] at hy hz
    rcases eq_or_ne z 0 with rfl | hz0
    · exact ⟨0, 1, one_ne_zero, by simp [← hyz]⟩
    · exact ⟨⟨y, hy⟩, ⟨z, hz⟩, hz0, ((div_eq_iff hz0).mp hyz).symm⟩

  have hRunit : ∀ {r : F'} (hr : r ∈ R), φ ⟨r, hr⟩ ≠ 0 →
      ∃ u : Oˣ, ((u : O) : F') = r ∧ ψ u = algebraMap F Ω (φ ⟨r, hr⟩) := by
    intro r hr hφr
    have hrO : r ∈ O := hRO hr
    have hψr : ψ ⟨r, hrO⟩ = algebraMap F Ω (φ ⟨r, hr⟩) := hψR ⟨r, hr⟩
    have hrU : IsUnit (⟨r, hrO⟩ : O) := by
      by_contra hnu
      have h0 : ψ ⟨r, hrO⟩ = 0 := RingHom.mem_ker.mp (hψker ▸ (mem_maximalIdeal _).mpr hnu)
      exact hφr ((algebraMap F Ω).injective (by rw [← hψr, h0, map_zero]))
    exact ⟨hrU.unit, rfl, hψr⟩
  have hUinv : ∀ u : Oˣ, (((u⁻¹ : Oˣ) : O) : F') = (((u : O) : F'))⁻¹ := fun u ↦
    eq_inv_of_mul_eq_one_left (by exact_mod_cast Units.inv_mul u)
  have hψUinv : ∀ u : Oˣ, ψ ((u⁻¹ : Oˣ) : O) = (ψ (u : O))⁻¹ := fun u ↦
    eq_inv_of_mul_eq_one_left (by
      have := congrArg ψ (Units.inv_mul u); rw [map_mul, map_one] at this; exact this)
  have hreg : ∀ f' : F', f' ≠ 0 → ∃ c : K', ∃ h : c • f' ∈ O, ψ ⟨c • f', h⟩ ≠ 0 := by
    intro f' hf'
    obtain ⟨r, s, hs0, hfs⟩ := hFrac f'
    have hr0 : (r : F') ≠ 0 := hfs ▸ mul_ne_zero hf' hs0
    obtain ⟨cr, hcr0, hcrR, hφcr⟩ := hRscale r hr0
    obtain ⟨cs, hcs0, hcsR, hφcs⟩ := hRscale s hs0
    obtain ⟨ur, hur, hψur⟩ := hRunit hcrR hφcr
    obtain ⟨us, hus, hψus⟩ := hRunit hcsR hφcs
    have hcs' : cs • (s : F') ≠ 0 := smul_ne_zero hcs0 hs0
    have heq : (cr * cs⁻¹) • f' = (((ur * us⁻¹ : Oˣ) : O) : F') := by
      have h1 : (((ur * us⁻¹ : Oˣ) : O) : F') = (cr • (r : F')) * (cs • (s : F'))⁻¹ := by
        push_cast; rw [hUinv, hur, hus]
      rw [h1, eq_mul_inv_iff_mul_eq₀ hcs', smul_mul_assoc, mul_smul_comm, hfs, smul_smul,
        mul_assoc, inv_mul_cancel₀ hcs0, mul_one]
    refine ⟨cr * cs⁻¹, heq ▸ ((ur * us⁻¹ : Oˣ) : O).2, ?_⟩
    have heqO : (⟨(cr * cs⁻¹) • f', heq ▸ ((ur * us⁻¹ : Oˣ) : O).2⟩ : O) = ((ur * us⁻¹ : Oˣ) : O) :=
      Subtype.ext heq
    rw [heqO]; push_cast; rw [map_mul, hψUinv, hψur, hψus]
    simp only [ne_eq, mul_eq_zero, inv_eq_zero, not_or]
    exact ⟨fun h ↦ hφcr ((algebraMap F Ω).injective (h.trans (map_zero _).symm)),
      fun h ↦ hφcs ((algebraMap F Ω).injective (h.trans (map_zero _).symm))⟩
  have himF : ∀ y : O, ψ y ∈ (algebraMap F Ω).range := by
    intro y
    obtain ⟨r, s, hs0, hys⟩ := hFrac (y : F')
    rcases eq_or_ne (r : F') 0 with hr0 | hr0
    · have hy0 : (y : F') = 0 := by
        exact (mul_eq_zero.mp (hys.trans hr0)).resolve_right hs0
      rw [show y = 0 from Subtype.ext hy0, map_zero]; exact ⟨0, map_zero _⟩
    obtain ⟨cr, hcr0, hcrR, hφcr⟩ := hRscale r hr0
    obtain ⟨cs, hcs0, hcsR, hφcs⟩ := hRscale s hs0
    obtain ⟨ur, hur, hψur⟩ := hRunit hcrR hφcr
    obtain ⟨us, hus, hψus⟩ := hRunit hcsR hφcs

    have hcr' : cr • (r : F') ≠ 0 := smul_ne_zero hcr0 hr0
    have heq : (y : F') = algebraMap K' F' (cs * cr⁻¹) * (((ur * us⁻¹ : Oˣ) : O) : F') := by
      have h1 : (((ur * us⁻¹ : Oˣ) : O) : F') = (cr • (r : F')) * (cs • (s : F'))⁻¹ := by
        push_cast; rw [hUinv, hur, hus]
      rw [h1, ← mul_assoc, eq_mul_inv_iff_mul_eq₀ (smul_ne_zero hcs0 hs0),
        mul_smul_comm, hys, ← Algebra.smul_def, smul_smul, mul_assoc,
        inv_mul_cancel₀ hcr0, mul_one]
    have hmemA : cs * cr⁻¹ ∈ A := by
      rw [← hOK']
      have heq2 : algebraMap K' F' (cs * cr⁻¹) = (y : F') * (((ur * us⁻¹)⁻¹ : Oˣ) : O).1 := by
        rw [heq, hUinv]; field_simp
      rw [heq2]; exact mul_mem y.2 ((((ur * us⁻¹)⁻¹ : Oˣ) : O).2)
    have hydec : y = (⟨algebraMap K' F' (cs * cr⁻¹), hRO (hAR ⟨_, hmemA⟩)⟩ : O) *
        ((ur * us⁻¹ : Oˣ) : O) := Subtype.ext (by rw [Subring.coe_mul]; exact heq)
    have hψa : ψ ⟨algebraMap K' F' (cs * cr⁻¹), hRO (hAR ⟨_, hmemA⟩)⟩ =
        algebraMap F Ω (algebraMap K F (σ ⟨_, hmemA⟩)) := hψA ⟨_, hmemA⟩
    refine ⟨algebraMap K F (σ ⟨_, hmemA⟩) * (φ ⟨_, hcrR⟩ * (φ ⟨_, hcsR⟩)⁻¹), ?_⟩
    have hψy : ψ y = algebraMap F Ω (algebraMap K F (σ ⟨_, hmemA⟩)) *
        (algebraMap F Ω (φ ⟨_, hcrR⟩) * (algebraMap F Ω (φ ⟨_, hcsR⟩))⁻¹) := by
      conv_lhs => rw [hydec]
      rw [map_mul, hψa, Units.val_mul, map_mul, hψUinv, hψur, hψus]
    rw [hψy, map_mul, map_mul, map_inv₀]

  let ψF : O →+* (algebraMap F Ω).range := ψ.codRestrict _ himF
  let eF : F ≃+* (algebraMap F Ω).range := RingEquiv.ofBijective (algebraMap F Ω).rangeRestrict
    ⟨fun a b h ↦ (algebraMap F Ω).injective (congrArg Subtype.val h),
     (algebraMap F Ω).rangeRestrict_surjective⟩
  let ρ : O →+* F := eF.symm.toRingHom.comp ψF
  have hρψ : ∀ y : O, algebraMap F Ω (ρ y) = ψ y := fun y ↦ by
    have h := eF.apply_symm_apply (ψF y)
    calc algebraMap F Ω (ρ y) = ((eF (ρ y) : (algebraMap F Ω).range) : Ω) := rfl
      _ = ((ψF y : (algebraMap F Ω).range) : Ω) := by
          rw [show eF (ρ y) = ψF y from h]
      _ = ψ y := rfl

  refine ⟨O, ρ, hOK', ?_, ?_, ?_, ?_⟩
  ·
    ext y
    rw [RingHom.mem_ker, ← (algebraMap F Ω).injective.eq_iff, map_zero, hρψ,
      ← RingHom.mem_ker, hψker]
  ·
    intro a
    refine ⟨hRO (hAR a), (algebraMap F Ω).injective ?_⟩
    rw [hρψ, hψA]
  ·
    intro f' hf'
    obtain ⟨c, h, hne⟩ := hreg f' hf'
    exact ⟨c, h, fun heq ↦ hne (by rw [← hρψ, heq, map_zero])⟩
  ·
    intro f
    refine ⟨hFO f, (algebraMap F Ω).injective ?_⟩
    rw [hρψ, hψF]
