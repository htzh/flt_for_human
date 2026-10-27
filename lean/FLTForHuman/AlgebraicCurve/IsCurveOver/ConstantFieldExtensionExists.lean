/-
The existence of a constant-field extension of a function field, after FLT's
`Theorems/Thm_AlgebraicCurve_exists_constantFieldExtension.lean` and its proof
`P2M/Sol/S_AlgebraicCurve_exists_constantFieldExtension.lean` (314 ln).

The mathematics: for a curve `F₀` over `K₀` with a separating transcendental `x`,
a field extension `K'` of `K₀`, and a prime `P` of the tensor product
`K' ⊗[K₀] F₀` avoiding the non-zero-divisors, `F' = Frac ((K' ⊗[K₀] F₀) ⧸ P)` is
a field containing both `K'` and `F₀` — the constant-field extension.  The
`Abstract` block transports transcendence (`incl τ x` stays transcendental when
`τ` is injective on `K'[x]`), integrality (`incl τ f` is integral over
`K'⟮incl τ x⟯`) and finiteness (`K'⟮incl τ x⟯` is finite-dimensional over `F'`)
along the map `F₀ → F'` encoded by `τ : K' ⊗[K₀] F₀ →ₐ[K'] F'`; the `Concrete`
block builds `P` by a maximal-ideal argument and transfers the two curve
structures: `IsCurveOver` from essential finite type plus the transported
transcendence data, and `HasCanonicalDivisor` from
`hasCanonicalDivisor_of_charZero`.

spec-pin: Theorems/Thm_AlgebraicCurve_exists_constantFieldExtension.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_exists_constantFieldExtension.lean   -- comparable copy
-/
import FLTForHuman.AlgebraicCurve.Canonical.HasCanonicalDivisor
import FLTForHuman.AlgebraicCurve.IsCurveOver.Transcendental
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.TensorProduct.Basic

set_option autoImplicit false

-- The pin's `haveI`/`letI` instance walls are transcribed literally; they carry
-- instances typeclass search needs.
set_option linter.style.haveILetI false

noncomputable section

open Polynomial TensorProduct

namespace AlgebraicCurve

universe u v w

/-! ### The prelude: the pin's generic block -/

theorem aeval_ofFinsupp_eq {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (x : A)
    (l : ℕ →₀ R) : aeval x (⟨.ofCoeff l⟩ : R[X]) = Finsupp.linearCombination R (fun n : ℕ => x ^ n) l := by
  simp only [aeval_def, eval₂_eq_sum, Polynomial.sum_def, Finsupp.linearCombination_apply, Finsupp.sum,
    support_ofFinsupp, coeff_ofFinsupp]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Algebra.smul_def]

theorem transcendental_iff_linearIndependent_pow {R A : Type*} [CommRing R] [Ring A]
    [Algebra R A] (x : A) :
    Transcendental R x ↔ LinearIndependent R (fun n : ℕ => x ^ n) := by
  rw [transcendental_iff, linearIndependent_iff]
  constructor
  · intro h l hl
    have := h ⟨.ofCoeff l⟩ (by rwa [aeval_ofFinsupp_eq])
    exact AddMonoidAlgebra.ofCoeff_eq_zero.1 (Polynomial.ofFinsupp_eq_zero.1 this)
  · intro h p hp
    obtain ⟨l⟩ := p
    have hl := h l.coeff (by rwa [← aeval_ofFinsupp_eq, AddMonoidAlgebra.ofCoeff_coeff])
    exact Polynomial.ofFinsupp_eq_zero.2 (AddMonoidAlgebra.coeff_eq_zero.1 hl)

theorem transcendental_one_tmul {K₀ : Type*} [Field K₀] (K' : Type*) [Field K'] [Algebra K₀ K']
    {F₀ : Type*} [Field F₀] [Algebra K₀ F₀] {x : F₀} (hx : Transcendental K₀ x) :
    Transcendental K' ((1 : K') ⊗ₜ[K₀] x) := by
  rw [transcendental_iff_linearIndependent_pow] at hx ⊢
  have := Module.Flat.linearIndependent_one_tmul (S := K') hx
  convert this using 1
  ext n
  simp [Algebra.TensorProduct.tmul_pow]

theorem essFiniteType_of_fg {K F : Type*} [Field K] [Field F] [Algebra K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    Algebra.EssFiniteType K F := by
  obtain ⟨x, -, hfin⟩ := hfg
  have h1 : Algebra.EssFiniteType K (IntermediateField.adjoin K ({x} : Set F)) :=
    IntermediateField.essFiniteType_iff.2
      (IntermediateField.fg_adjoin_of_finite (Set.finite_singleton x))
  have h2 : Algebra.EssFiniteType (IntermediateField.adjoin K ({x} : Set F)) F := inferInstance
  exact Algebra.EssFiniteType.comp K (IntermediateField.adjoin K ({x} : Set F)) F

section Abstract

variable {K₀ F₀ K' F' : Type*}
  [Field K₀] [Field F₀] [Field K'] [Field F'] [Algebra K₀ F₀] [Algebra K₀ K'] [Algebra K' F']
  (τ : K' ⊗[K₀] F₀ →ₐ[K'] F')

noncomputable def incl : F₀ →+* F' :=
  τ.toRingHom.comp (Algebra.TensorProduct.includeRight (R := K₀) (A := K')).toRingHom

theorem incl_apply (f : F₀) : incl τ f = τ ((1 : K') ⊗ₜ[K₀] f) := rfl

theorem incl_algebraMap (k : K₀) :
    incl τ (algebraMap K₀ F₀ k) = algebraMap K' F' (algebraMap K₀ K' k) := by
  rw [incl_apply, ← τ.commutes, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
    TensorProduct.smul_tmul]

theorem tau_tmul (k : K') (f : F₀) :
    τ (k ⊗ₜ[K₀] f) = algebraMap K' F' k * incl τ f := by
  have : k ⊗ₜ[K₀] f = algebraMap K' (K' ⊗[K₀] F₀) k * ((1 : K') ⊗ₜ[K₀] f) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [this, map_mul, AlgHom.commutes, incl_apply]

theorem tau_mem (L : IntermediateField K' F') (hL : ∀ f : F₀, incl τ f ∈ L)
    (a : K' ⊗[K₀] F₀) : τ a ∈ L := by
  induction a using TensorProduct.inductionOn with
  | tmul k f => rw [tau_tmul]; exact mul_mem (algebraMap_mem L k) (hL f)
  | add a b ha hb => rw [map_add]; exact add_mem ha hb

variable (hgen : ∀ z : F', ∃ a b : K' ⊗[K₀] F₀, τ a / τ b = z)

include hgen in
theorem eq_top_of_forall_incl_mem (L : IntermediateField K' F')
    (hL : ∀ f : F₀, incl τ f ∈ L) : L = ⊤ := by
  rw [eq_top_iff]
  intro z _
  obtain ⟨a, b, rfl⟩ := hgen z
  exact div_mem (tau_mem τ L hL a) (tau_mem τ L hL b)

include hgen in
theorem adjoin_range_incl_eq_top :
    IntermediateField.adjoin K' (Set.range (incl τ)) = ⊤ :=
  eq_top_of_forall_incl_mem τ hgen _ fun f => IntermediateField.subset_adjoin _ _ ⟨f, rfl⟩

variable [Algebra K₀ F'] [IsScalarTower K₀ K' F']

noncomputable def inclₐ : F₀ →ₐ[K₀] F' :=
  { incl τ with
    commutes' := fun k => by
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
        MonoidHom.coe_coe]
      rw [incl_algebraMap, ← IsScalarTower.algebraMap_apply] }

@[scoped simp] theorem inclₐ_apply (f : F₀) : inclₐ τ f = incl τ f := rfl

theorem incl_mem_adjoin_image {S : Set F₀} {f : F₀} (hf : f ∈ IntermediateField.adjoin K₀ S) :
    incl τ f ∈ IntermediateField.adjoin K' (incl τ '' S) := by
  have h1 : inclₐ τ f ∈ (IntermediateField.adjoin K₀ S).map (inclₐ τ) := ⟨f, hf, rfl⟩
  rw [IntermediateField.adjoin_map] at h1
  have h2 : IntermediateField.adjoin K₀ (inclₐ τ '' S) ≤
      (IntermediateField.adjoin K' (incl τ '' S)).restrictScalars K₀ :=
    IntermediateField.adjoin_le_iff.mpr (IntermediateField.subset_adjoin K' _)
  exact h2 h1

variable {x : F₀} (hx : Transcendental K₀ x)
  (hfin : FiniteDimensional (IntermediateField.adjoin K₀ ({x} : Set F₀)) F₀)
  (hker : ∀ p : K'[X], τ (aeval ((1 : K') ⊗ₜ[K₀] x) p) = 0 → p = 0)

include hker in
omit [Algebra K₀ F'] [IsScalarTower K₀ K' F'] in
theorem transcendental_incl : Transcendental K' (incl τ x) := by
  rw [transcendental_iff]
  intro p hp
  apply hker
  rw [← Polynomial.aeval_algHom_apply]
  exact hp

include hfin in
theorem isIntegral_incl (f : F₀) :
    IsIntegral (IntermediateField.adjoin K' ({incl τ x} : Set F')) (incl τ f) := by
  set E := IntermediateField.adjoin K' ({incl τ x} : Set F')
  have hmem : ∀ c : IntermediateField.adjoin K₀ ({x} : Set F₀), incl τ (c : F₀) ∈ E := by
    intro c
    have := incl_mem_adjoin_image τ (S := {x}) c.2
    rwa [Set.image_singleton] at this
  let ψ : IntermediateField.adjoin K₀ ({x} : Set F₀) →+* E :=
    ((incl τ).comp (algebraMap _ F₀)).codRestrict E hmem
  have hcomp : (algebraMap E F').comp ψ =
      (incl τ).comp (algebraMap (IntermediateField.adjoin K₀ ({x} : Set F₀)) F₀) := by
    ext c; rfl
  exact IsIntegral.map_of_comp_eq ψ (incl τ) hcomp (IsIntegral.of_finite _ f)

include hx hfin hgen in
theorem finiteDimensional_adjoin_incl :
    FiniteDimensional (IntermediateField.adjoin K' ({incl τ x} : Set F')) F' := by
  set E := IntermediateField.adjoin K' ({incl τ x} : Set F')
  have : Algebra.EssFiniteType K₀ F₀ := essFiniteType_of_fg ⟨x, hx, hfin⟩
  obtain ⟨s, hs⟩ := IntermediateField.fg_top K₀ F₀
  haveI : Finite (incl τ '' (s : Set F₀)) := Set.Finite.to_subtype ((s.finite_toSet).image _)
  have hLfin : FiniteDimensional E (IntermediateField.adjoin E (incl τ '' (s : Set F₀))) :=
    IntermediateField.finiteDimensional_adjoin fun z hz => by
      obtain ⟨f, -, rfl⟩ := hz
      exact isIntegral_incl τ hfin f
  have hLtop : IntermediateField.adjoin E (incl τ '' (s : Set F₀)) = ⊤ := by
    rw [← IntermediateField.restrictScalars_eq_top_iff (K := K'),
      IntermediateField.adjoin_adjoin_left]
    apply eq_top_of_forall_incl_mem τ hgen
    intro f
    have hf : f ∈ IntermediateField.adjoin K₀ (s : Set F₀) := by rw [hs]; trivial
    exact IntermediateField.adjoin.mono K' _ _ Set.subset_union_right (incl_mem_adjoin_image τ hf)
  rw [hLtop] at hLfin
  exact LinearEquiv.finiteDimensional (IntermediateField.topEquiv (F := E) (E := F')).toLinearEquiv

end Abstract

section Concrete

variable {K₀ : Type u} {F₀ : Type v} {K' : Type w}
  [Field K₀] [Field F₀] [Field K'] [Algebra K₀ F₀] [Algebra K₀ K']
  (P : Ideal (K' ⊗[K₀] F₀))

abbrev CFQ : Type (max v w) := (K' ⊗[K₀] F₀) ⧸ P

abbrev CFExt : Type (max v w) := FractionRing (CFQ P)

-- The pin wraps each of the four instances below in
-- `set_option synthInstance.maxHeartbeats 1600000 in`. That raise is dropped: the search runs
-- through three derived carriers (`TensorProduct` → `Ideal.Quotient` → `FractionRing`) against
-- the whole `Algebra` pool, but in this toolchain the two heaviest cost ~3–3.5k heartbeats
-- against the 20,000 default (measured 2026-10-27: the module elaborates with the cap at 3,500
-- and fails at 3,000). A raised cap buys search length, so leaving the default in place is what
-- keeps a future blow-up in this search visible as a build failure.
noncomputable scoped instance CFExt.algK' : Algebra K' (CFExt P) := inferInstance

noncomputable scoped instance CFExt.algK₀ : Algebra K₀ (CFExt P) := inferInstance

scoped instance CFExt.towerK : IsScalarTower K₀ K' (CFExt P) := inferInstance

scoped instance CFExt.towerQ : IsScalarTower K' (CFQ P) (CFExt P) := inferInstance

noncomputable def tau : K' ⊗[K₀] F₀ →ₐ[K'] CFExt P :=
  (IsScalarTower.toAlgHom K' (CFQ P) (CFExt P)).comp (Ideal.Quotient.mkₐ K' P)

theorem tau_apply (a : K' ⊗[K₀] F₀) :
    tau P a = IsScalarTower.toAlgHom K' (CFQ P) (CFExt P) (Ideal.Quotient.mk P a) := rfl

variable [P.IsPrime]

theorem tau_gen (z : CFExt P) : ∃ a b : K' ⊗[K₀] F₀, tau P a / tau P b = z := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := CFQ P) z
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact ⟨a, b, rfl⟩

omit [P.IsPrime] in
theorem tau_eq_zero_iff (a : K' ⊗[K₀] F₀) : tau P a = 0 ↔ a ∈ P := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, tau_apply, IsScalarTower.coe_toAlgHom',
    map_eq_zero_iff _ (IsFractionRing.injective (CFQ P) (CFExt P))]

omit [P.IsPrime] in

theorem exists_constantFieldExtension_core (K₀ : Type u) (F₀ : Type v) (K' : Type w)
    [Field K₀] [Field F₀] [Field K'] [Algebra K₀ F₀] [Algebra K₀ K']
    {x : F₀} (hx : Transcendental K₀ x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K₀ ({x} : Set F₀)) F₀) :
    ∃ (F' : Type (max v w)) (_ : Field F') (_ : Algebra K' F') (_ : Algebra F₀ F')
      (_ : Algebra K₀ F') (_ : IsScalarTower K₀ K' F') (_ : IsScalarTower K₀ F₀ F'),
      Transcendental K' (algebraMap F₀ F' x) ∧
      FiniteDimensional (IntermediateField.adjoin K' ({algebraMap F₀ F' x} : Set F')) F' ∧
      IntermediateField.adjoin K' (Set.range (algebraMap F₀ F')) = ⊤ := by
  classical
  have hxA_tr : Transcendental K' ((1 : K') ⊗ₜ[K₀] x) := transcendental_one_tmul K' hx
  let S : Submonoid (K' ⊗[K₀] F₀) :=
    (nonZeroDivisors K'[X]).map (aeval ((1 : K') ⊗ₜ[K₀] x) : K'[X] →ₐ[K'] K' ⊗[K₀] F₀)
  have hdisj : Disjoint ((⊥ : Ideal (K' ⊗[K₀] F₀)) : Set (K' ⊗[K₀] F₀)) S := by
    refine Set.disjoint_left.2 fun a ha hS => ?_
    have ha0 : a = 0 := by simpa using ha
    obtain ⟨p, hp, rfl⟩ := hS
    have : p = 0 := (transcendental_iff.1 hxA_tr) p ha0
    exact nonZeroDivisors.ne_zero hp this
  obtain ⟨P, hPprime, -, hPdisj⟩ :=
    Ideal.exists_le_prime_disjoint (⊥ : Ideal (K' ⊗[K₀] F₀)) S hdisj
  have hker : ∀ p : K'[X], tau P (aeval ((1 : K') ⊗ₜ[K₀] x) p) = 0 → p = 0 := by
    intro p hp
    rw [tau_eq_zero_iff] at hp
    by_contra hne
    have hS : aeval ((1 : K') ⊗ₜ[K₀] x) p ∈ S := ⟨p, mem_nonZeroDivisors_of_ne_zero hne, rfl⟩
    exact Set.disjoint_left.1 hPdisj hp hS
  letI algF₀ : Algebra F₀ (CFExt P) := (incl (tau P)).toAlgebra
  letI : SMul F₀ (CFExt P) := algF₀.toSMul
  haveI tF₀ : IsScalarTower K₀ F₀ (CFExt P) :=
    IsScalarTower.of_algebraMap_eq fun k => (incl_algebraMap (tau P) k).symm
  refine ⟨CFExt P, inferInstance, inferInstance, algF₀, inferInstance, inferInstance, tF₀,
    ?_, ?_, ?_⟩
  · exact transcendental_incl (tau P) hker
  · exact finiteDimensional_adjoin_incl (tau P) (tau_gen P) hx hfin
  · exact adjoin_range_incl_eq_top (tau P) (tau_gen P)

end Concrete

theorem hasCanonicalDivisor_of_charZero (K F : Type*) [Field K] [Field F] [Algebra K F]
    [CharZero K] [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    HasCanonicalDivisor (K := K) (F := F) := by
  haveI : Algebra.EssFiniteType K F := essFiniteType_of_fg hfg
  haveI : PerfectField K := PerfectField.ofCharZero
  exact AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver (K := K) (F := F)

theorem exists_constantFieldExtension (K₀ : Type u) (F₀ : Type v) (K' : Type w)
    [Field K₀] [Field F₀] [Field K'] [Algebra K₀ F₀] [Algebra K₀ K']
    [IsAlgClosed K₀] [CharZero K₀] [IsAlgClosed K']
    (hfg₀ : ∃ x : F₀, Transcendental K₀ x ∧
      FiniteDimensional (IntermediateField.adjoin K₀ ({x} : Set F₀)) F₀)
    [IsCurveOver K₀ F₀] [HasCanonicalDivisor (K := K₀) (F := F₀)] :
    ∃ (F' : Type (max v w)) (_ : Field F') (_ : Algebra K' F') (_ : Algebra F₀ F')
      (_ : Algebra K₀ F') (_ : IsScalarTower K₀ K' F') (_ : IsScalarTower K₀ F₀ F')
      (_ : IsCurveOver K' F') (_ : HasCanonicalDivisor (K := K') (F := F')),
      (∃ x : F', Transcendental K' x ∧
        FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F') ∧
      IntermediateField.adjoin K' (Set.range (algebraMap F₀ F')) = ⊤ := by
  obtain ⟨x, hx, hfin⟩ := hfg₀
  obtain ⟨F', _, _, _, _, _, _, htr, hfin', htop⟩ :=
    exists_constantFieldExtension_core K₀ F₀ K' hx hfin

  haveI : CharZero K' := charZero_of_injective_algebraMap (algebraMap K₀ K').injective
  haveI : CharZero F' := charZero_of_injective_algebraMap (algebraMap K' F').injective

  haveI : Algebra.IsSeparable (IntermediateField.adjoin K' ({algebraMap F₀ F' x} : Set F')) F' :=
    inferInstance
  haveI hC : IsCurveOver K' F' :=
    AlgebraicCurve.isCurveOver_of_transcendental_of_isSeparable K' F' (algebraMap F₀ F' x)
      htr hfin' inferInstance
  haveI hK : HasCanonicalDivisor (K := K') (F := F') :=
    hasCanonicalDivisor_of_charZero K' F' ⟨algebraMap F₀ F' x, htr, hfin'⟩
  exact ⟨F', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hC, hK, ⟨algebraMap F₀ F' x, htr, hfin'⟩, htop⟩

end AlgebraicCurve
