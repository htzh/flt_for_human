/-
The `RatFunc K →ₐ[K] F` layer of the function-field dictionary, after FLT's
`Theorems/Thm_AlgebraicCurve_FunctionField_exists_ratFuncAlgHom_apply_X_eq.lean`
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_FunctionField_exists_ratFuncAlgHom_apply_X_eq.lean>)
and `Theorems/Thm_AlgebraicCurve_FunctionField_finite_of_ratFuncAlgHom.lean`
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_FunctionField_finite_of_ratFuncAlgHom.lean>),
with the proofs of the corresponding `P2M/Sol/S_AlgebraicCurve_FunctionField_*` files.

The two directions of the layer:

* `exists_ratFuncAlgHom_apply_X_eq` — over an algebraically closed base, any
  element `g` transcendental over `K` (spelled `g ∉ Set.range (algebraMap K F)`)
  is the image of `RatFunc.X` under some `K`-algebra map `RatFunc K →ₐ[K] F`.
  The proof lifts `Polynomial.aeval g` through the fraction-ring structure of
  `RatFunc K`.
* `finite_of_ratFuncAlgHom` — for any `K`-algebra map `φ : RatFunc K →ₐ[K] F` with
  `F` finite-dimensional over `RatFunc K`, the module `F` is finite over
  `RatFunc K` when the scalars are restricted along `φ.toRingHom.toAlgebra`. The
  proof is the standard tower: `φ RatFunc.X` is transcendental over `K`, the
  intermediate field `K(φ X)` is a rational function field, `F` is finite and
  algebraic over it, and `RatFunc K → K(φ X)` is surjective, so `F` is finite over
  `RatFunc K`.

The pin's `import Mathlib` is replaced by the specific mathlib imports below; the
`P2M.Util` prelude the pin files carry contributes nothing to these proofs and is
dropped.

spec-pin: Theorems/Thm_AlgebraicCurve_FunctionField_exists_ratFuncAlgHom_apply_X_eq.lean
spec-pin: Theorems/Thm_AlgebraicCurve_FunctionField_finite_of_ratFuncAlgHom.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_FunctionField_exists_ratFuncAlgHom_apply_X_eq.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_FunctionField_finite_of_ratFuncAlgHom.lean
-/
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Adjoin.Polynomial.Basic

set_option autoImplicit false

-- The pin's `letI`/`haveI` instance walls are load-bearing at the tower steps below
-- (`RatFunc K → K(φ X) → F` and the `letI : Algebra (RatFunc K) F := φ.toRingHom.toAlgebra`
-- of the last line, which is the very module structure the statement names); they are
-- kept literal rather than restructured.
set_option linter.style.haveILetI false

noncomputable section

open Polynomial

namespace AlgebraicCurve.FunctionField

theorem exists_ratFuncAlgHom_apply_X_eq {K F : Type*} [Field K] [IsAlgClosed K] [Field F]
    [Algebra K F] {g : F} (hg : g ∉ Set.range (algebraMap K F)) :
    ∃ φ : RatFunc K →ₐ[K] F, φ RatFunc.X = g := by
  have htr : Transcendental K g := by
    intro halg
    apply hg
    have hint : IsIntegral K g := halg.isIntegral
    have hdeg : (minpoly K g).degree = 1 :=
      IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hint)
    obtain ⟨a, ha⟩ := minpoly.degree_eq_one_iff.mp hdeg
    exact ⟨a, ha⟩
  have hinj : Function.Injective (Polynomial.aeval (R := K) g) :=
    transcendental_iff_injective.mp htr
  refine ⟨RatFunc.liftAlgHom (Polynomial.aeval g) ?_, ?_⟩
  · intro p hp
    simp only [Submonoid.mem_comap]
    exact mem_nonZeroDivisors_of_ne_zero
      ((map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero hp))
  · rw [RatFunc.liftAlgHom_apply]
    simp

namespace RatFuncAlgHom

theorem isTranscendenceBasis_polynomial_X (K : Type*) [Field K] :
    IsTranscendenceBasis K ![(X : K[X])] := by
  rw [isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic]
  refine ⟨algebraicIndependent_iff_transcendental.mpr (transcendental_X K), ?_⟩
  have h : Algebra.adjoin K (Set.range ![(X : K[X])]) = ⊤ := by
    simp [Polynomial.adjoin_X]
  rw [h]
  exact ⟨fun x => isAlgebraic_algebraMap (⟨x, Algebra.mem_top⟩ : (⊤ : Subalgebra K K[X]))⟩

theorem isTranscendenceBasis_ratFunc_X (K : Type*) [Field K] :
    IsTranscendenceBasis K ![(RatFunc.X : RatFunc K)] := by
  haveI : Algebra.IsAlgebraic K[X] (RatFunc K) :=
    IsLocalization.isAlgebraic (RatFunc K) (nonZeroDivisors K[X])
  haveI : FaithfulSMul K[X] (RatFunc K) :=
    (faithfulSMul_iff_algebraMap_injective K[X] (RatFunc K)).mpr
      (IsFractionRing.injective K[X] (RatFunc K))
  have h := (isTranscendenceBasis_polynomial_X K).algebraMap_comp (A := RatFunc K)
  convert h using 1
  ext i
  fin_cases i
  simp [RatFunc.algebraMap_X]

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
  [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F]

theorem isTranscendenceBasis_t0 :
    IsTranscendenceBasis K ![algebraMap (RatFunc K) F RatFunc.X] := by
  haveI : Algebra.IsAlgebraic (RatFunc K) F := Algebra.IsAlgebraic.of_finite _ _
  have h := (isTranscendenceBasis_ratFunc_X K).algebraMap_comp (A := F)
  convert h using 1
  ext i
  fin_cases i
  simp

omit [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F] in
theorem transcendental_apply_X (φ : RatFunc K →ₐ[K] F) : Transcendental K (φ RatFunc.X) := by
  rw [transcendental_iff_injective]
  have hX : Function.Injective (aeval (R := K) (RatFunc.X : RatFunc K)) :=
    transcendental_iff_injective.mp RatFunc.transcendental_X
  intro p q hpq
  apply hX
  apply φ.toRingHom.injective
  simpa [aeval_algHom_apply] using hpq

theorem isTranscendenceBasis_apply_X (φ : RatFunc K →ₐ[K] F) :
    IsTranscendenceBasis K (Subtype.val : ({φ RatFunc.X} : Set F) → F) := by
  classical
  set g := φ RatFunc.X with hg
  set t₀ := algebraMap (RatFunc K) F RatFunc.X with ht₀

  have hbase_t : (AlgebraicIndependent.matroid K F).IsBase ({t₀} : Set F) := by
    rw [AlgebraicIndependent.matroid_isBase_iff]
    have h := (isTranscendenceBasis_t0 (K := K) (F := F)).to_subtype_range
    convert h using 2 <;> simp [ht₀]

  have hind_g : (AlgebraicIndependent.matroid K F).Indep ({g} : Set F) := by
    rw [AlgebraicIndependent.matroid_indep_iff]
    have h := (algebraicIndependent_iff_transcendental.mpr (transcendental_apply_X φ)).to_subtype_range
    have hr : Set.range ![g] = {g} := by simp
    rw [hr] at h
    exact h
  obtain ⟨B, hB, hgB⟩ := hind_g.exists_isBase_superset
  have hcard : B.ncard = 1 := by
    rw [hB.ncard_eq_ncard_of_isBase hbase_t, Set.ncard_singleton]
  obtain ⟨b, rfl⟩ := Set.ncard_eq_one.mp hcard
  have hgb : g = b := by simpa using hgB
  rw [← AlgebraicIndependent.matroid_isBase_iff, hgb]
  exact hB

omit [FiniteDimensional (RatFunc K) F] in
theorem algebraMap_polynomial_mem {E : Type*} [Field E] [Algebra K E] [Algebra E F]
    [IsScalarTower K E F] (T : IntermediateField E F)
    (ht : algebraMap (RatFunc K) F RatFunc.X ∈ T) (p : K[X]) :
    algebraMap (RatFunc K) F (algebraMap K[X] (RatFunc K) p) ∈ T := by
  have h1 : algebraMap K[X] (RatFunc K) p = aeval (RatFunc.X : RatFunc K) p := by
    rw [← RatFunc.algebraMap_X, aeval_algebraMap_apply, aeval_X_left_apply]
  rw [h1, ← aeval_algebraMap_apply]
  have h2 : Algebra.adjoin K {algebraMap (RatFunc K) F RatFunc.X}
      ≤ (T.restrictScalars K).toSubalgebra :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr ht)
  exact h2 (aeval_mem_adjoin_singleton K _)

theorem finite_over_adjoin (φ : RatFunc K →ₐ[K] F) :
    FiniteDimensional (IntermediateField.adjoin K ({φ RatFunc.X} : Set F)) F := by
  classical
  set g := φ RatFunc.X with hg
  set Kg := IntermediateField.adjoin K ({g} : Set F) with hKg
  have halg : Algebra.IsAlgebraic Kg F := by
    have h := (isTranscendenceBasis_apply_X φ).isAlgebraic_field
    have hr : Set.range (Subtype.val : ({g} : Set F) → F) = {g} := Subtype.range_coe
    rw [hr] at h
    exact h
  set t₀ := algebraMap (RatFunc K) F RatFunc.X with ht₀
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := RatFunc K) (M := F)
  let S : Set F := insert t₀ (s : Set F)
  haveI : Finite S := Set.finite_coe_iff.mpr ((s.finite_toSet).insert t₀)
  have hint : ∀ x ∈ S, IsIntegral Kg x := fun x _ => (halg.isAlgebraic x).isIntegral
  have hfin : FiniteDimensional Kg (IntermediateField.adjoin Kg S) :=
    IntermediateField.finiteDimensional_adjoin hint
  have ht₀S : t₀ ∈ IntermediateField.adjoin Kg S :=
    IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
  have htop : IntermediateField.adjoin Kg S = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hz : z ∈ Submodule.span (RatFunc K) (s : Set F) := by rw [hs]; trivial
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
    · intro x hx
      exact IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ hx)
    · exact zero_mem _
    · intro x y _ _ hx hy
      exact add_mem hx hy
    · intro c x _ hx
      rw [Algebra.smul_def]
      refine mul_mem ?_ hx
      rw [← RatFunc.num_div_denom c, map_div₀]
      exact div_mem (algebraMap_polynomial_mem _ ht₀S _) (algebraMap_polynomial_mem _ ht₀S _)
  rw [htop] at hfin
  exact LinearEquiv.finiteDimensional (IntermediateField.topEquiv (F := Kg) (E := F)).toLinearEquiv

end RatFuncAlgHom

theorem finite_of_ratFuncAlgHom {K F : Type*} [Field K] [Field F] [Algebra K F]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F]
    (φ : RatFunc K →ₐ[K] F) : @Module.Finite (RatFunc K) F _ _ (φ.toRingHom.toAlgebra).toModule := by
  classical
  set g := φ RatFunc.X with hg
  set Kg := IntermediateField.adjoin K ({g} : Set F) with hKg
  haveI hKF : FiniteDimensional Kg F := RatFuncAlgHom.finite_over_adjoin φ

  have hrange : ∀ c : RatFunc K, φ c ∈ Kg := by
    intro c
    have hpoly : ∀ p : K[X], φ (algebraMap K[X] (RatFunc K) p) ∈ Kg := by
      intro p
      have h1 : algebraMap K[X] (RatFunc K) p = aeval (RatFunc.X : RatFunc K) p := by
        rw [← RatFunc.algebraMap_X, aeval_algebraMap_apply, aeval_X_left_apply]
      rw [h1, ← aeval_algHom_apply]
      exact IntermediateField.algebra_adjoin_le_adjoin K _ (aeval_mem_adjoin_singleton K _)
    rw [← RatFunc.num_div_denom c, map_div₀]
    exact div_mem (hpoly _) (hpoly _)

  let φ' : RatFunc K →+* Kg := φ.toRingHom.codRestrict Kg.toSubalgebra.toSubring hrange
  have hsurj : Function.Surjective φ' := by
    have hle : Kg ≤ φ.fieldRange := by
      rw [hKg, IntermediateField.adjoin_le_iff]
      rintro _ rfl
      exact ⟨RatFunc.X, rfl⟩
    intro y
    obtain ⟨c, hc⟩ := hle y.2
    exact ⟨c, Subtype.ext hc⟩
  letI : Algebra (RatFunc K) Kg := φ'.toAlgebra
  letI algφ : Algebra (RatFunc K) F := φ.toRingHom.toAlgebra
  haveI : IsScalarTower (RatFunc K) Kg F := IsScalarTower.of_algebraMap_eq fun c => rfl
  haveI : Module.Finite (RatFunc K) Kg :=
    Module.Finite.of_surjective (Algebra.linearMap (RatFunc K) Kg) hsurj
  exact Module.Finite.trans Kg F

end AlgebraicCurve.FunctionField

end
