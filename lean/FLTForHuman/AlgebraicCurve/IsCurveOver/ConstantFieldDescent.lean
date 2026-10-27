/-
Descent to a countable algebraically closed constant field, after Lefschetz.

Let `K` be algebraically closed of characteristic zero and let `F/K` be a curve carrying a
transcendental `x` with `K⟮x⟯` finite over `F`.  The construction cuts `K` down to the
algebraic closure `K₀` of a finitely generated subfield of `K` — countable, algebraically
closed, and reached by an embedding `K₀ → ℂ` — and `F` down to a corresponding `F₀`, keeping
the transcendence and finiteness data: `K₀` is built from the coefficients of the polynomials
expressing a primitive element of `F/K⟮x⟯` over `K⟮x⟯`.  The engine is the rational-relation
criterion: if `y` satisfies `∑ j ∈ J, (r j x / s j x) y^j = 0` with one non-zero coefficient,
then `y` is algebraic over `k⟮x⟯`, so `k⟮x, y⟯` is finite over `k⟮x⟯`.  The three headlines
descend the curve structure, a prescribed finite set of constants, and a whole finite family
of correspondence roofs with their integral and finite models.

spec-pin: Theorems/Thm_AlgebraicCurve_exists_constantFieldDescent.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_exists_constantFieldDescent.lean
spec-pin: Theorems/Thm_AlgebraicCurve_exists_constantFieldDescent_finset.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_exists_constantFieldDescent_finset.lean
spec-pin: Theorems/Thm_AlgebraicCurve_exists_constantFieldDescent_correspondence.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_exists_constantFieldDescent_correspondence.lean
-/
import FLTForHuman.AlgebraicCurve.Defs.Correspondence
import FLTForHuman.AlgebraicCurve.IsCurveOver.ConstantFieldExtensionExists
import FLTForHuman.AlgebraicCurve.IsCurveOver.FinitenessTransfer
import FLTForHuman.FieldTheory.NonemptyRingHomComplex
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.Flat.Basic
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.SetTheory.Cardinal.Subfield

set_option autoImplicit false

-- The pin's `letI`/`haveI` instance walls are transcribed literally; they carry
-- instances typeclass search needs.
set_option linter.style.haveILetI false

noncomputable section

open Polynomial IntermediateField Cardinal

namespace AlgebraicCurve

open AlgebraicCurve

universe u v w x

namespace ConstantFieldDescent

/-! ### The prelude the pin copies into each of the three files

`nonempty_ringHom_complex` is the port's `Field.nonempty_ringHom_complex_of_countable`
(`FieldTheory/NonemptyRingHomComplex.lean`), imported rather than restated. -/


theorem isAlgebraic_of_rational_relation {k Φ : Type*} [Field k] [Field Φ] [Algebra k Φ]
    (x y : Φ) (J : Finset ℕ) (r s : ℕ → k[X])
    (hrel : ∑ j ∈ J, (aeval x (r j) / aeval x (s j)) * y ^ j = 0)
    (hne : ∃ j ∈ J, aeval x (r j) / aeval x (s j) ≠ 0) :
    IsAlgebraic k⟮x⟯ y := by
  classical
  have hmem : ∀ j, aeval x (r j) / aeval x (s j) ∈ k⟮x⟯ := fun j =>
    (mem_adjoin_simple_iff (F := k) _).2 ⟨r j, s j, rfl⟩
  let c : ℕ → k⟮x⟯ := fun j => ⟨_, hmem j⟩
  have hc : ∀ j, (c j : Φ) = aeval x (r j) / aeval x (s j) := fun j => rfl
  let q : k⟮x⟯[X] := ∑ j ∈ J, C (c j) * X ^ j
  have hcoeff : ∀ j ∈ J, q.coeff j = c j := by
    intro j hj
    simp only [q, finsetSum_coeff, coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd hj h
  refine ⟨q, ?_, ?_⟩
  · obtain ⟨j₀, hj₀, hne⟩ := hne
    intro hq
    apply hne
    have := hcoeff j₀ hj₀
    rw [hq, coeff_zero] at this
    rw [← hc, ← this]; rfl
  · simp only [q, map_sum, map_mul, map_pow, aeval_C, aeval_X]

    convert hrel using 2
    rw [← hc]; rfl

theorem descent_abstract {k F : Type*} [Field k] [Field F] [Algebra k F]
    {x y : F} (hx : Transcendental k x) (J : Finset ℕ) (r s : ℕ → k[X])
    (hrel : ∑ j ∈ J, (aeval x (r j) / aeval x (s j)) * y ^ j = 0)
    (hne : ∃ j ∈ J, aeval x (r j) / aeval x (s j) ≠ 0) :
    ∃ x₀ : k⟮x, y⟯, (x₀ : F) = x ∧ Transcendental k x₀ ∧
      FiniteDimensional k⟮x₀⟯ k⟮x, y⟯ := by
  classical
  set F₀ : IntermediateField k F := k⟮x, y⟯ with hF₀
  let x₀ : F₀ := ⟨x, subset_adjoin k _ (by simp)⟩
  let y₀ : F₀ := ⟨y, subset_adjoin k _ (by simp)⟩
  have hval : ∀ p : k[X], ((aeval x₀ p : F₀) : F) = aeval x p := by
    intro p
    rw [← IntermediateField.coe_val, ← aeval_algHom_apply]
    rfl
  have hx₀ : Transcendental k x₀ :=
    (transcendental_algebraMap_iff (R := k) (S := F₀) (A := F) (algebraMap F₀ F).injective).1 hx
  have hrel₀ : ∑ j ∈ J, (aeval x₀ (r j) / aeval x₀ (s j)) * y₀ ^ j = 0 := by
    apply (algebraMap F₀ F).injective
    rw [map_sum, map_zero, ← hrel]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_div₀, map_pow]
    change ((aeval x₀ (r j) : F₀) : F) / ((aeval x₀ (s j) : F₀) : F) * (y₀ : F) ^ j = _
    rw [hval, hval]
  have hne₀ : ∃ j ∈ J, aeval x₀ (r j) / aeval x₀ (s j) ≠ 0 := by
    obtain ⟨j, hj, hne⟩ := hne
    refine ⟨j, hj, fun h => hne ?_⟩
    have h' := congrArg (algebraMap F₀ F) h
    rw [map_div₀, map_zero] at h'
    change ((aeval x₀ (r j) : F₀) : F) / ((aeval x₀ (s j) : F₀) : F) = 0 at h'
    rwa [hval, hval] at h'
  have hyint : IsIntegral k⟮x₀⟯ y₀ :=
    (isAlgebraic_of_rational_relation x₀ y₀ J r s hrel₀ hne₀).isIntegral
  have htop₀ : k⟮x₀, y₀⟯ = (⊤ : IntermediateField k F₀) := by
    apply IntermediateField.lift_injective
    rw [lift_adjoin, lift_top]
    simp [Set.image_insert_eq, Set.image_singleton, x₀, y₀, hF₀]
  have hfin₀ : FiniteDimensional k⟮x₀⟯ F₀ := by
    have h1 : FiniteDimensional k⟮x₀⟯ k⟮x₀⟯⟮y₀⟯ := adjoin.finiteDimensional hyint
    have h2 : k⟮x₀⟯⟮y₀⟯ = ⊤ := by
      rw [← restrictScalars_eq_top_iff (K := k), adjoin_simple_adjoin_simple, htop₀]
    rw [h2] at h1
    exact LinearEquiv.finiteDimensional
      (IntermediateField.topEquiv (F := k⟮x₀⟯) (E := F₀)).toLinearEquiv
  exact ⟨x₀, rfl, hx₀, hfin₀⟩

theorem exists_constantFieldDescent_core (K : Type u) (F : Type v) [Field K] [Field F]
    [Algebra K F] [IsAlgClosed K] [CharZero K]
    {x : F} (hx : Transcendental K x) (hfin : FiniteDimensional K⟮x⟯ F) :
    ∃ (K₀ : Type u) (F₀ : Type v) (_ : Field K₀) (_ : Field F₀)
      (_ : Algebra K₀ F₀) (_ : Algebra K₀ K) (_ : Algebra F₀ F) (_ : Algebra K₀ F)
      (_ : IsScalarTower K₀ K F) (_ : IsScalarTower K₀ F₀ F) (_ : Algebra K₀ ℂ)
      (_ : IsAlgClosed K₀) (_ : Countable K₀) (_ : CharZero K₀),
      (∃ x₀ : F₀, Transcendental K₀ x₀ ∧ FiniteDimensional K₀⟮x₀⟯ F₀) ∧
      IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤ := by
  classical

  haveI := hfin
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  haveI : PerfectField K⟮x⟯ := PerfectField.ofCharZero
  haveI : Algebra.IsSeparable K⟮x⟯ F := Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨y, hy⟩ := Field.exists_primitive_element K⟮x⟯ F
  have hxy : K⟮x, y⟯ = ⊤ := by
    rw [← adjoin_simple_adjoin_simple, hy, restrictScalars_top]

  obtain ⟨q, hq0, hqy⟩ : IsAlgebraic K⟮x⟯ y := Algebra.IsAlgebraic.isAlgebraic y
  have hcoef : ∀ j, ∃ r s : K[X], (q.coeff j : F) = aeval x r / aeval x s := fun j =>
    (mem_adjoin_simple_iff (F := K) _).1 (q.coeff j).2
  choose r s hrs using hcoef
  set J := q.support with hJ
  have hrel : ∑ j ∈ J, (aeval x (r j) / aeval x (s j)) * y ^ j = 0 := by
    rw [aeval_def, eval₂_eq_sum, Polynomial.sum_def] at hqy
    simp_rw [← hrs]
    exact hqy
  have hne : ∃ j ∈ J, aeval x (r j) / aeval x (s j) ≠ 0 := by
    obtain ⟨j, hj⟩ := Polynomial.support_nonempty.2 hq0
    refine ⟨j, hj, ?_⟩
    rw [← hrs]
    exact fun h => (mem_support_iff.1 hj) (ZeroMemClass.coe_eq_zero.1 h)

  let C : Set K := ⋃ j ∈ J, (((r j).coeffs ∪ (s j).coeffs : Finset K) : Set K)
  have hCfin : C.Finite := Set.Finite.biUnion J.finite_toSet fun j _ => Finset.finite_toSet _
  let L : Subfield K := Subfield.closure C
  let K₀ : IntermediateField L K := algebraicClosure L K
  haveI : IsAlgClosed K₀ := IsAlgClosure.isAlgClosed L
  haveI : Countable L := by
    haveI : Countable C := hCfin.countable.to_subtype
    rw [← Cardinal.mk_le_aleph0_iff]
    exact (Subfield.cardinalMk_closure_le_max C).trans (max_le Cardinal.mk_le_aleph0 le_rfl)
  haveI : Countable K₀ := by
    rw [← Cardinal.mk_le_aleph0_iff]
    exact (Algebra.IsAlgebraic.cardinalMk_le_max L K₀).trans
      (max_le Cardinal.mk_le_aleph0 le_rfl)
  have hCK₀ : C ⊆ Set.range (algebraMap K₀ K) := by
    intro c hc
    exact ⟨⟨c, K₀.algebraMap_mem ⟨c, Subfield.subset_closure hc⟩⟩, rfl⟩

  have hlift : ∀ p : K[X], (p.coeffs : Set K) ⊆ C →
      ∃ p₀ : K₀[X], p₀.map (algebraMap K₀ K) = p := fun p hp =>
    (mem_lifts _).1 ((lifts_iff_coeffs_subset_range _).2 (hp.trans hCK₀))
  have hrC : ∀ j ∈ J, ((r j).coeffs : Set K) ⊆ C := fun j hj c hc =>
    Set.mem_biUnion hj (by simp [hc])
  have hsC : ∀ j ∈ J, ((s j).coeffs : Set K) ⊆ C := fun j hj c hc =>
    Set.mem_biUnion hj (by simp [hc])
  have hr₀ : ∀ j, ∃ p₀ : K₀[X], j ∈ J → p₀.map (algebraMap K₀ K) = r j := fun j => by
    by_cases hj : j ∈ J
    · obtain ⟨p₀, hp₀⟩ := hlift _ (hrC j hj); exact ⟨p₀, fun _ => hp₀⟩
    · exact ⟨0, fun h => absurd h hj⟩
  have hs₀ : ∀ j, ∃ p₀ : K₀[X], j ∈ J → p₀.map (algebraMap K₀ K) = s j := fun j => by
    by_cases hj : j ∈ J
    · obtain ⟨p₀, hp₀⟩ := hlift _ (hsC j hj); exact ⟨p₀, fun _ => hp₀⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose r₀ hr₀ using hr₀
  choose s₀ hs₀ using hs₀
  have hrel' : ∑ j ∈ J, (aeval x (r₀ j) / aeval x (s₀ j)) * y ^ j = 0 := by
    rw [← hrel]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← aeval_map_algebraMap K x (r₀ j), ← aeval_map_algebraMap K x (s₀ j), hr₀ j hj, hs₀ j hj]
  have hne' : ∃ j ∈ J, aeval x (r₀ j) / aeval x (s₀ j) ≠ 0 := by
    obtain ⟨j, hj, hne⟩ := hne
    refine ⟨j, hj, ?_⟩
    rwa [← aeval_map_algebraMap K x (r₀ j), ← aeval_map_algebraMap K x (s₀ j), hr₀ j hj,
      hs₀ j hj]

  obtain ⟨x₀, hx₀x, hx₀, hfin₀⟩ :=
    descent_abstract (hx.of_tower_top K₀) J r₀ s₀ hrel' hne'

  obtain ⟨ψ⟩ := Field.nonempty_ringHom_complex_of_countable K₀
  refine ⟨K₀, K₀⟮x, y⟯, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, ψ.toAlgebra, inferInstance, inferInstance,
    inferInstance, ⟨x₀, hx₀, hfin₀⟩, ?_⟩
  rw [eq_top_iff, ← hxy]
  refine adjoin.mono K _ _ ?_
  rintro z (rfl | h)
  · exact ⟨⟨z, subset_adjoin K₀ _ (by simp)⟩, rfl⟩
  · rw [Set.mem_singleton_iff.1 h]; exact ⟨⟨y, subset_adjoin K₀ _ (by simp)⟩, rfl⟩

theorem aeval_mem_of_lift {K₀ K F : Type*} [Field K₀] [Field K] [Field F] [Algebra K₀ K]
    [Algebra K F] [Algebra K₀ F] [IsScalarTower K₀ K F]
    {M : IntermediateField K₀ F} {x : F} (hx : x ∈ M) {p : K[X]}
    (hp : ∃ p₀ : K₀[X], p₀.map (algebraMap K₀ K) = p) : aeval x p ∈ M := by
  obtain ⟨p₀, rfl⟩ := hp
  rw [aeval_map_algebraMap]
  have : aeval x p₀ = M.val (aeval (⟨x, hx⟩ : M) p₀) := by
    rw [← aeval_algHom_apply]; rfl
  rw [this]
  exact SetLike.coe_mem _

theorem aeval_mem_of_repr {K₀ K F : Type*} [Field K₀] [Field K] [Field F] [Algebra K₀ K]
    [Algebra K F] [Algebra K₀ F] [IsScalarTower K₀ K F]
    {M : IntermediateField K₀ F} {x y : F} (hx : x ∈ M) (hy : y ∈ M)
    (P : K⟮x⟯[X]) (rp sp : ℕ → K[X])
    (hrep : ∀ i, ((P.coeff i : K⟮x⟯) : F) = aeval x (rp i) / aeval x (sp i))
    (hr : ∀ i ∈ P.support, ∃ r₀ : K₀[X], r₀.map (algebraMap K₀ K) = rp i)
    (hs : ∀ i ∈ P.support, ∃ s₀ : K₀[X], s₀.map (algebraMap K₀ K) = sp i) :
    aeval y P ∈ M := by
  rw [aeval_def, eval₂_eq_sum, Polynomial.sum_def]
  refine sum_mem fun i hi => mul_mem ?_ (pow_mem hy i)
  change ((P.coeff i : K⟮x⟯) : F) ∈ M
  rw [hrep i]
  exact div_mem (aeval_mem_of_lift hx (hr i hi)) (aeval_mem_of_lift hx (hs i hi))

theorem core (K : Type u) (F : Type v) [Field K] [Field F]
    [Algebra K F] [IsAlgClosed K] [CharZero K]
    {x : F} (hx : Transcendental K x) (hfin : FiniteDimensional K⟮x⟯ F) (t : Finset F) :
    ∃ (K₀ : Type u) (F₀ : Type v) (_ : Field K₀) (_ : Field F₀)
      (_ : Algebra K₀ F₀) (_ : Algebra K₀ K) (_ : Algebra F₀ F) (_ : Algebra K₀ F)
      (_ : IsScalarTower K₀ K F) (_ : IsScalarTower K₀ F₀ F) (_ : Algebra K₀ ℂ)
      (_ : IsAlgClosed K₀) (_ : Countable K₀) (_ : CharZero K₀),
      (∃ x₀ : F₀, Transcendental K₀ x₀ ∧ FiniteDimensional K₀⟮x₀⟯ F₀) ∧
      IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤ ∧
      (↑t : Set F) ⊆ Set.range (algebraMap F₀ F) := by
  classical

  haveI := hfin
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  haveI : PerfectField K⟮x⟯ := PerfectField.ofCharZero
  haveI : Algebra.IsSeparable K⟮x⟯ F := Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨y, hy⟩ := Field.exists_primitive_element K⟮x⟯ F
  have hxy : K⟮x, y⟯ = ⊤ := by
    rw [← adjoin_simple_adjoin_simple, hy, restrictScalars_top]

  obtain ⟨q, hq0, hqy⟩ : IsAlgebraic K⟮x⟯ y := Algebra.IsAlgebraic.isAlgebraic y
  have hcoef : ∀ j, ∃ r s : K[X], (q.coeff j : F) = aeval x r / aeval x s := fun j =>
    (mem_adjoin_simple_iff (F := K) _).1 (q.coeff j).2
  choose r s hrs using hcoef
  set J := q.support with hJ
  have hrel : ∑ j ∈ J, (aeval x (r j) / aeval x (s j)) * y ^ j = 0 := by
    rw [aeval_def, eval₂_eq_sum, Polynomial.sum_def] at hqy
    simp_rw [← hrs]
    exact hqy
  have hne : ∃ j ∈ J, aeval x (r j) / aeval x (s j) ≠ 0 := by
    obtain ⟨j, hj⟩ := Polynomial.support_nonempty.2 hq0
    refine ⟨j, hj, ?_⟩
    rw [← hrs]
    exact fun h => (mem_support_iff.1 hj) (ZeroMemClass.coe_eq_zero.1 h)

  have hrepr : ∀ z : F, ∃ P Q : K⟮x⟯[X], z = aeval y P / aeval y Q := fun z =>
    (mem_adjoin_simple_iff (F := K⟮x⟯) _).1 (by rw [hy]; exact mem_top)
  choose P Q hPQ using hrepr
  have hcoefP : ∀ z i, ∃ r s : K[X], ((P z).coeff i : F) = aeval x r / aeval x s :=
    fun z i => (mem_adjoin_simple_iff (F := K) _).1 ((P z).coeff i).2
  have hcoefQ : ∀ z i, ∃ r s : K[X], ((Q z).coeff i : F) = aeval x r / aeval x s :=
    fun z i => (mem_adjoin_simple_iff (F := K) _).1 ((Q z).coeff i).2
  choose rp sp hrsp using hcoefP
  choose rq sq hrsq using hcoefQ

  let C : Set K :=
    (⋃ j ∈ J, (((r j).coeffs ∪ (s j).coeffs : Finset K) : Set K)) ∪
      ⋃ z ∈ t, ⋃ i ∈ ((P z).support ∪ (Q z).support),
        (((rp z i).coeffs ∪ (sp z i).coeffs ∪ ((rq z i).coeffs ∪ (sq z i).coeffs) :
          Finset K) : Set K)
  have hCfin : C.Finite := by
    refine Set.Finite.union ?_ ?_
    · exact Set.Finite.biUnion J.finite_toSet fun j _ => Finset.finite_toSet _
    · exact Set.Finite.biUnion t.finite_toSet fun z _ =>
        Set.Finite.biUnion (Finset.finite_toSet _) fun i _ => Finset.finite_toSet _
  let L : Subfield K := Subfield.closure C
  let K₀ : IntermediateField L K := algebraicClosure L K
  haveI : IsAlgClosed K₀ := IsAlgClosure.isAlgClosed L
  haveI : Countable L := by
    haveI : Countable C := hCfin.countable.to_subtype
    rw [← Cardinal.mk_le_aleph0_iff]
    exact (Subfield.cardinalMk_closure_le_max C).trans (max_le Cardinal.mk_le_aleph0 le_rfl)
  haveI : Countable K₀ := by
    rw [← Cardinal.mk_le_aleph0_iff]
    exact (Algebra.IsAlgebraic.cardinalMk_le_max L K₀).trans
      (max_le Cardinal.mk_le_aleph0 le_rfl)
  have hCK₀ : C ⊆ Set.range (algebraMap K₀ K) := by
    intro c hc
    exact ⟨⟨c, K₀.algebraMap_mem ⟨c, Subfield.subset_closure hc⟩⟩, rfl⟩

  have hlift : ∀ p : K[X], (p.coeffs : Set K) ⊆ C →
      ∃ p₀ : K₀[X], p₀.map (algebraMap K₀ K) = p := fun p hp =>
    (mem_lifts _).1 ((lifts_iff_coeffs_subset_range _).2 (hp.trans hCK₀))
  have hrC : ∀ j ∈ J, ((r j).coeffs : Set K) ⊆ C := fun j hj c hc =>
    Set.mem_union_left _ (Set.mem_biUnion hj (by simp [hc]))
  have hsC : ∀ j ∈ J, ((s j).coeffs : Set K) ⊆ C := fun j hj c hc =>
    Set.mem_union_left _ (Set.mem_biUnion hj (by simp [hc]))
  have htC : ∀ z ∈ t, ∀ i ∈ (P z).support ∪ (Q z).support,
      ((rp z i).coeffs : Set K) ⊆ C ∧ ((sp z i).coeffs : Set K) ⊆ C ∧
        ((rq z i).coeffs : Set K) ⊆ C ∧ ((sq z i).coeffs : Set K) ⊆ C := by
    intro z hz i hi
    have hsub : (((rp z i).coeffs ∪ (sp z i).coeffs ∪ ((rq z i).coeffs ∪ (sq z i).coeffs) :
        Finset K) : Set K) ⊆ C := by
      intro c hc
      refine Set.mem_union_right _ ?_
      exact Set.mem_biUnion (Finset.mem_coe.2 hz) (Set.mem_biUnion (Finset.mem_coe.2 hi) hc)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro c hc <;> apply hsub <;> simp [hc]
  have hr₀ : ∀ j, ∃ p₀ : K₀[X], j ∈ J → p₀.map (algebraMap K₀ K) = r j := fun j => by
    by_cases hj : j ∈ J
    · obtain ⟨p₀, hp₀⟩ := hlift _ (hrC j hj); exact ⟨p₀, fun _ => hp₀⟩
    · exact ⟨0, fun h => absurd h hj⟩
  have hs₀ : ∀ j, ∃ p₀ : K₀[X], j ∈ J → p₀.map (algebraMap K₀ K) = s j := fun j => by
    by_cases hj : j ∈ J
    · obtain ⟨p₀, hp₀⟩ := hlift _ (hsC j hj); exact ⟨p₀, fun _ => hp₀⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose r₀ hr₀ using hr₀
  choose s₀ hs₀ using hs₀
  have hrel' : ∑ j ∈ J, (aeval x (r₀ j) / aeval x (s₀ j)) * y ^ j = 0 := by
    rw [← hrel]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← aeval_map_algebraMap K x (r₀ j), ← aeval_map_algebraMap K x (s₀ j), hr₀ j hj, hs₀ j hj]
  have hne' : ∃ j ∈ J, aeval x (r₀ j) / aeval x (s₀ j) ≠ 0 := by
    obtain ⟨j, hj, hne⟩ := hne
    refine ⟨j, hj, ?_⟩
    rwa [← aeval_map_algebraMap K x (r₀ j), ← aeval_map_algebraMap K x (s₀ j), hr₀ j hj,
      hs₀ j hj]

  obtain ⟨x₀, hx₀x, hx₀, hfin₀⟩ :=
    descent_abstract (hx.of_tower_top K₀) J r₀ s₀ hrel' hne'

  have hxM : x ∈ K₀⟮x, y⟯ := subset_adjoin K₀ _ (by simp)
  have hyM : y ∈ K₀⟮x, y⟯ := subset_adjoin K₀ _ (by simp)
  have htM : ∀ z ∈ t, z ∈ K₀⟮x, y⟯ := by
    intro z hz
    rw [hPQ z]
    refine div_mem ?_ ?_
    · exact aeval_mem_of_repr hxM hyM (P z) (rp z) (sp z) (hrsp z)
        (fun i hi => hlift _ (htC z hz i (Finset.mem_union_left _ hi)).1)
        (fun i hi => hlift _ (htC z hz i (Finset.mem_union_left _ hi)).2.1)
    · exact aeval_mem_of_repr hxM hyM (Q z) (rq z) (sq z) (hrsq z)
        (fun i hi => hlift _ (htC z hz i (Finset.mem_union_right _ hi)).2.2.1)
        (fun i hi => hlift _ (htC z hz i (Finset.mem_union_right _ hi)).2.2.2)

  obtain ⟨ψ⟩ := Field.nonempty_ringHom_complex_of_countable K₀
  refine ⟨K₀, K₀⟮x, y⟯, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, ψ.toAlgebra, inferInstance, inferInstance,
    inferInstance, ⟨x₀, hx₀, hfin₀⟩, ?_, ?_⟩
  · rw [eq_top_iff, ← hxy]
    refine adjoin.mono K _ _ ?_
    rintro z (rfl | h)
    · exact ⟨⟨z, hxM⟩, rfl⟩
    · rw [Set.mem_singleton_iff.1 h]; exact ⟨⟨y, hyM⟩, rfl⟩
  · intro z hz
    exact ⟨⟨z, htM z (Finset.mem_coe.1 hz)⟩, rfl⟩

section Tools

variable {k F F' : Type*} [Field k] [Field F] [Field F'] [Algebra k F] [Algebra k F']

theorem finiteDimensional_adjoin_map {x : F} (hfin : FiniteDimensional k⟮x⟯ F)
    (ψ : F →ₐ[k] F') (hψfin : FiniteAlong k ψ) : FiniteDimensional k⟮ψ x⟯ F' := by
  letI : Algebra F F' := algebraAlong ψ
  haveI := isScalarTower_along ψ
  haveI : Module.Finite F F' := hψfin
  haveI := hfin
  set Kx : IntermediateField k F := k⟮x⟯ with hKx
  set Ky : IntermediateField k F' := k⟮ψ x⟯ with hKy
  have hmap : ∀ z ∈ Kx, ψ z ∈ Ky := by
    intro z hz
    have hKxy : Kx.map ψ = Ky := by
      rw [hKx, IntermediateField.adjoin_map, Set.image_singleton]
    rw [← hKxy]
    exact ⟨z, hz, rfl⟩
  let f : Kx →+* Ky := ψ.toRingHom.restrict Kx Ky hmap
  letI algKxF' : Algebra Kx F' := ((algebraMap F F').comp (algebraMap Kx F)).toAlgebra
  haveI : IsScalarTower Kx F F' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite Kx F' := Module.Finite.trans F F'
  letI : Algebra Kx Ky := f.toAlgebra
  haveI : IsScalarTower Kx Ky F' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Module.Finite.of_restrictScalars_finite Kx Ky F'

noncomputable def restrictHom {k₀ : Type*} [Field k₀] [Algebra k₀ k] [Algebra k₀ F] [Algebra k₀ F']
    [IsScalarTower k₀ k F] [IsScalarTower k₀ k F']
    (σ : F →ₐ[k] F') (M : IntermediateField k₀ F) (N : IntermediateField k₀ F')
    (h : ∀ z ∈ M, σ z ∈ N) : M →ₐ[k₀] N where
  toFun z := ⟨σ (z : F), h z z.2⟩
  map_one' := Subtype.ext (map_one σ)
  map_mul' a b := Subtype.ext (map_mul σ (a : F) (b : F))
  map_zero' := Subtype.ext (map_zero σ)
  map_add' a b := Subtype.ext (map_add σ (a : F) (b : F))
  commutes' c := Subtype.ext (by
    show σ (algebraMap k₀ F c) = algebraMap k₀ F' c
    rw [IsScalarTower.algebraMap_apply k₀ k F, σ.commutes, ← IsScalarTower.algebraMap_apply])

@[scoped simp] theorem coe_restrictHom {k₀ : Type*} [Field k₀] [Algebra k₀ k] [Algebra k₀ F]
    [Algebra k₀ F'] [IsScalarTower k₀ k F] [IsScalarTower k₀ k F']
    (σ : F →ₐ[k] F') (M : IntermediateField k₀ F) (N : IntermediateField k₀ F')
    (h : ∀ z ∈ M, σ z ∈ N) (z : M) : ((restrictHom σ M N h z : N) : F') = σ (z : F) := rfl

theorem finiteAlong_of_isIntegral_of_adjoin_eq_top {A B : Type*} [Field A] [Field B]
    [Algebra k A] [Algebra k B] (φ : A →ₐ[k] B)
    (hφ : φ.toRingHom.IsIntegral) (T : Finset B)
    (hT : IntermediateField.adjoin k (T : Set B) = ⊤) : FiniteAlong k φ := by
  letI : Algebra A B := algebraAlong φ
  haveI := isScalarTower_along φ
  have hT' : IntermediateField.adjoin A (T : Set B) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hle : IntermediateField.adjoin k (T : Set B) ≤
        (IntermediateField.adjoin A (T : Set B)).restrictScalars k :=
      IntermediateField.adjoin_le_iff.2 (IntermediateField.subset_adjoin A _)
    have hy : y ∈ IntermediateField.adjoin k (T : Set B) := by rw [hT]; trivial
    exact hle hy
  haveI : FiniteDimensional A (IntermediateField.adjoin A (T : Set B)) :=
    IntermediateField.finiteDimensional_adjoin (fun t _ => hφ t)
  have e : (IntermediateField.adjoin A (T : Set B)) ≃ₗ[A] B :=
    ((IntermediateField.equivOfEq hT').trans IntermediateField.topEquiv).toLinearEquiv
  exact Module.Finite.equiv e

theorem finiteAlong_of_transcendental_image {A B : Type*} [Field A] [Field B]
    [Algebra k A] [Algebra k B] (σ₀ : A →ₐ[k] B)
    (T : Finset B) (hT : IntermediateField.adjoin k (T : Set B) = ⊤)
    (w : B) [FiniteDimensional k⟮w⟯ B]
    (a₀ : A) (ha₀ : Transcendental k (σ₀ a₀)) : FiniteAlong k σ₀ := by
  classical
  haveI hfd : FiniteDimensional k⟮σ₀ a₀⟯ B :=
    finiteDimensional_adjoin_of_transcendental w ha₀
  refine finiteAlong_of_isIntegral_of_adjoin_eq_top σ₀ ?_ T hT
  intro z

  have hzint : IsIntegral k⟮σ₀ a₀⟯ z := IsIntegral.of_finite _ z
  set m := minpoly k⟮σ₀ a₀⟯ z with hm
  have hmmonic : m.Monic := minpoly.monic hzint

  set m' : B[X] := m.map (algebraMap k⟮σ₀ a₀⟯ B) with hm'
  have hlifts : m' ∈ Polynomial.lifts σ₀.toRingHom := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [hm', Polynomial.coeff_map]
    have hmapeq : (k⟮a₀⟯).map σ₀ = k⟮σ₀ a₀⟯ := by
      rw [IntermediateField.adjoin_map, Set.image_singleton]
    have hc : ((m.coeff n : k⟮σ₀ a₀⟯) : B) ∈ (k⟮a₀⟯).map σ₀ := by
      rw [hmapeq]; exact (m.coeff n).2
    obtain ⟨d, -, hd⟩ := hc
    exact ⟨d, hd⟩
  have hm'monic : m'.Monic := hmmonic.map _
  obtain ⟨q, hqmap, -, hqmonic⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts hm'monic
  refine ⟨q, hqmonic, ?_⟩
  have h1 : Polynomial.eval₂ σ₀.toRingHom z q = (q.map σ₀.toRingHom).eval z := by
    rw [Polynomial.eval_map]
  rw [h1, hqmap, hm', Polynomial.eval_map, ← Polynomial.aeval_def]
  exact minpoly.aeval _ z

end Tools

namespace Correspondence

theorem descent_abstract {k F : Type*} [Field k] [Field F] [Algebra k F]
    {x y : F} (hx : Transcendental k x) (J : Finset ℕ) (r s : ℕ → k[X])
    (hrel : ∑ j ∈ J, (aeval x (r j) / aeval x (s j)) * y ^ j = 0)
    (hne : ∃ j ∈ J, aeval x (r j) / aeval x (s j) ≠ 0) :
    ∃ x₀ y₀ : k⟮x, y⟯, (x₀ : F) = x ∧ (y₀ : F) = y ∧ Transcendental k x₀ ∧
      FiniteDimensional k⟮x₀⟯ k⟮x, y⟯ ∧ k⟮x₀, y₀⟯ = ⊤ := by
  classical
  set F₀ : IntermediateField k F := k⟮x, y⟯ with hF₀
  let x₀ : F₀ := ⟨x, subset_adjoin k _ (by simp)⟩
  let y₀ : F₀ := ⟨y, subset_adjoin k _ (by simp)⟩
  have hval : ∀ p : k[X], ((aeval x₀ p : F₀) : F) = aeval x p := by
    intro p
    rw [← IntermediateField.coe_val, ← aeval_algHom_apply]
    rfl
  have hx₀ : Transcendental k x₀ :=
    (transcendental_algebraMap_iff (R := k) (S := F₀) (A := F) (algebraMap F₀ F).injective).1 hx
  have hrel₀ : ∑ j ∈ J, (aeval x₀ (r j) / aeval x₀ (s j)) * y₀ ^ j = 0 := by
    apply (algebraMap F₀ F).injective
    rw [map_sum, map_zero, ← hrel]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_div₀, map_pow]
    change ((aeval x₀ (r j) : F₀) : F) / ((aeval x₀ (s j) : F₀) : F) * (y₀ : F) ^ j = _
    rw [hval, hval]
  have hne₀ : ∃ j ∈ J, aeval x₀ (r j) / aeval x₀ (s j) ≠ 0 := by
    obtain ⟨j, hj, hne⟩ := hne
    refine ⟨j, hj, fun h => hne ?_⟩
    have h' := congrArg (algebraMap F₀ F) h
    rw [map_div₀, map_zero] at h'
    change ((aeval x₀ (r j) : F₀) : F) / ((aeval x₀ (s j) : F₀) : F) = 0 at h'
    rwa [hval, hval] at h'
  have hyint : IsIntegral k⟮x₀⟯ y₀ :=
    (isAlgebraic_of_rational_relation x₀ y₀ J r s hrel₀ hne₀).isIntegral
  have htop₀ : k⟮x₀, y₀⟯ = (⊤ : IntermediateField k F₀) := by
    apply IntermediateField.lift_injective
    rw [lift_adjoin, lift_top]
    simp [Set.image_insert_eq, Set.image_singleton, x₀, y₀, hF₀]
  have hfin₀ : FiniteDimensional k⟮x₀⟯ F₀ := by
    have h1 : FiniteDimensional k⟮x₀⟯ k⟮x₀⟯⟮y₀⟯ := adjoin.finiteDimensional hyint
    have h2 : k⟮x₀⟯⟮y₀⟯ = ⊤ := by
      rw [← restrictScalars_eq_top_iff (K := k), adjoin_simple_adjoin_simple, htop₀]
    rw [h2] at h1
    exact LinearEquiv.finiteDimensional
      (IntermediateField.topEquiv (F := k⟮x₀⟯) (E := F₀)).toLinearEquiv
  exact ⟨x₀, y₀, rfl, rfl, hx₀, hfin₀, htop₀⟩

end Correspondence

end ConstantFieldDescent

open ConstantFieldDescent

theorem exists_constantFieldDescent (K : Type u) (F : Type v) [Field K] [Field F]
    [Algebra K F] [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)] :
    ∃ (K₀ : Type u) (F₀ : Type v) (_ : Field K₀) (_ : Field F₀)
      (_ : Algebra K₀ F₀) (_ : Algebra K₀ K) (_ : Algebra F₀ F) (_ : Algebra K₀ F)
      (_ : IsScalarTower K₀ K F) (_ : IsScalarTower K₀ F₀ F) (_ : Algebra K₀ ℂ)
      (_ : IsAlgClosed K₀) (_ : Countable K₀)
      (_ : IsCurveOver K₀ F₀) (_ : HasCanonicalDivisor (K := K₀) (F := F₀)),
      (∃ x : F₀, Transcendental K₀ x ∧
        FiniteDimensional (IntermediateField.adjoin K₀ ({x} : Set F₀)) F₀) ∧
      IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤ := by
  obtain ⟨x, hx, hfin⟩ := hfg
  obtain ⟨K₀, F₀, _, _, _, _, _, _, _, _, algC, _, _, _, ⟨x₀, hx₀, hfin₀⟩, htop⟩ :=
    exists_constantFieldDescent_core K F hx hfin
  haveI : CharZero F₀ := charZero_of_injective_algebraMap (algebraMap K₀ F₀).injective

  haveI : Algebra.IsSeparable (IntermediateField.adjoin K₀ ({x₀} : Set F₀)) F₀ := inferInstance
  haveI hC : IsCurveOver K₀ F₀ :=
    isCurveOver_of_transcendental_of_isSeparable K₀ F₀ x₀ hx₀ hfin₀ inferInstance
  haveI hK : HasCanonicalDivisor (K := K₀) (F := F₀) :=
    hasCanonicalDivisor_of_charZero K₀ F₀ ⟨x₀, hx₀, hfin₀⟩
  exact ⟨K₀, F₀, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, algC, inferInstance, inferInstance, hC, hK,
    ⟨x₀, hx₀, hfin₀⟩, htop⟩

theorem exists_constantFieldDescent_finset (K : Type u) (F : Type v)
    [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    [IsCurveOver K F] (t : Finset F) :
    ∃ (K₀ : Type u) (F₀ : Type v) (_ : Field K₀) (_ : Field F₀)
      (_ : Algebra K₀ F₀) (_ : Algebra K₀ K) (_ : Algebra F₀ F) (_ : Algebra K₀ F)
      (_ : IsScalarTower K₀ K F) (_ : IsScalarTower K₀ F₀ F) (_ : Algebra K₀ ℂ)
      (_ : IsAlgClosed K₀) (_ : Countable K₀) (_ : IsCurveOver K₀ F₀),
      (∃ x : F₀, Transcendental K₀ x ∧
        FiniteDimensional (IntermediateField.adjoin K₀ ({x} : Set F₀)) F₀) ∧
      IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤ ∧
      (↑t : Set F) ⊆ Set.range (algebraMap F₀ F) := by
  obtain ⟨x, hx, hfin⟩ := hfg
  obtain ⟨K₀, F₀, _, _, _, _, _, _, _, _, algC, _, _, _, ⟨x₀, hx₀, hfin₀⟩, htop, ht⟩ :=
    core K F hx hfin t
  haveI : CharZero F₀ := charZero_of_injective_algebraMap (algebraMap K₀ F₀).injective

  haveI : Algebra.IsSeparable (IntermediateField.adjoin K₀ ({x₀} : Set F₀)) F₀ := inferInstance
  haveI hC : IsCurveOver K₀ F₀ :=
    isCurveOver_of_transcendental_of_isSeparable K₀ F₀ x₀ hx₀ hfin₀ inferInstance
  exact ⟨K₀, F₀, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, algC, inferInstance, inferInstance, hC,
    ⟨x₀, hx₀, hfin₀⟩, htop, ht⟩

-- The pin wraps this proof in `set_option maxHeartbeats 6400000` and
-- `set_option synthInstance.maxHeartbeats 1600000`; both raises are dropped, so a future
-- blow-up in this elaboration or in the `IsScalarTower` searches shows up as a failure.
-- `hφ` is one of the pin's hypotheses but is not consumed by its proof; the binder is kept
-- (the statement is the pin's) and the unused-variable linter silenced for this declaration.
set_option linter.unusedVariables false in
theorem exists_constantFieldDescent_correspondence
    (K : Type u) (F : Type v) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K]
    [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    {ι : Type w} [Finite ι] (F' : ι → Type x) [∀ i, Field (F' i)] [∀ i, Algebra K (F' i)]
    (φ ψ : ∀ i, F →ₐ[K] F' i)
    (hφ : ∀ i, (φ i).toRingHom.IsIntegral) (hfin : ∀ i, FiniteAlong K (ψ i)) :
    ∃ (K₀ : Type u) (F₀ : Type v) (F'₀ : ι → Type x)
      (_ : Field K₀) (_ : Field F₀) (_ : ∀ i, Field (F'₀ i))
      (_ : Algebra K₀ K) (_ : Algebra K₀ ℂ) (_ : IsAlgClosed K₀) (_ : Countable K₀)
      (_ : Algebra K₀ F₀) (_ : Algebra F₀ F) (_ : Algebra K₀ F)
      (_ : IsScalarTower K₀ K F) (_ : IsScalarTower K₀ F₀ F) (_ : IsCurveOver K₀ F₀)
      (_ : ∀ i, Algebra K₀ (F'₀ i)) (_ : ∀ i, Algebra (F'₀ i) (F' i)) (_ : ∀ i, Algebra K₀ (F' i))
      (_ : ∀ i, IsScalarTower K₀ K (F' i)) (_ : ∀ i, IsScalarTower K₀ (F'₀ i) (F' i))
      (_ : ∀ i, IsCurveOver K₀ (F'₀ i))
      (φ₀ ψ₀ : ∀ i, F₀ →ₐ[K₀] F'₀ i),
      (∃ x : F₀, Transcendental K₀ x ∧
        FiniteDimensional (IntermediateField.adjoin K₀ ({x} : Set F₀)) F₀) ∧
      IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤ ∧
      (∀ i, ∃ x : F'₀ i, Transcendental K₀ x ∧
        FiniteDimensional (IntermediateField.adjoin K₀ ({x} : Set (F'₀ i))) (F'₀ i)) ∧
      (∀ i, IntermediateField.adjoin K (Set.range (algebraMap (F'₀ i) (F' i))) = ⊤) ∧
      (∀ i (f : F₀), φ i (algebraMap F₀ F f) = algebraMap (F'₀ i) (F' i) (φ₀ i f)) ∧
      (∀ i (f : F₀), ψ i (algebraMap F₀ F f) = algebraMap (F'₀ i) (F' i) (ψ₀ i f)) ∧
      (∀ i, FiniteAlong K₀ (φ₀ i)) ∧ (∀ i, FiniteAlong K₀ (ψ₀ i)) := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  obtain ⟨x, hx, hxfin⟩ := hfg
  haveI := hxfin
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  haveI : ∀ i, CharZero (F' i) := fun i =>
    charZero_of_injective_algebraMap (algebraMap K (F' i)).injective

  haveI : PerfectField K⟮x⟯ := PerfectField.ofCharZero
  haveI : Algebra.IsSeparable K⟮x⟯ F := Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨y, hy⟩ := Field.exists_primitive_element K⟮x⟯ F
  have hxy : K⟮x, y⟯ = ⊤ := by
    rw [← adjoin_simple_adjoin_simple, hy, restrictScalars_top]
  obtain ⟨q, hq0, hqy⟩ : IsAlgebraic K⟮x⟯ y := Algebra.IsAlgebraic.isAlgebraic y
  have hcoef : ∀ j, ∃ r s : K[X], (q.coeff j : F) = aeval x r / aeval x s := fun j =>
    (mem_adjoin_simple_iff (F := K) _).1 (q.coeff j).2
  choose r s hrs using hcoef
  set J := q.support with hJ
  have hrel : ∑ j ∈ J, (aeval x (r j) / aeval x (s j)) * y ^ j = 0 := by
    rw [aeval_def, eval₂_eq_sum, Polynomial.sum_def] at hqy
    simp_rw [← hrs]
    exact hqy
  have hne : ∃ j ∈ J, aeval x (r j) / aeval x (s j) ≠ 0 := by
    obtain ⟨j, hj⟩ := Polynomial.support_nonempty.2 hq0
    refine ⟨j, hj, ?_⟩
    rw [← hrs]
    exact fun h => (mem_support_iff.1 hj) (ZeroMemClass.coe_eq_zero.1 h)

  have hxi : ∀ i, Transcendental K (ψ i x) := fun i h =>
    hx ((isAlgebraic_algHom_iff (ψ i) (ψ i).toRingHom.injective).mp h)
  haveI hfini : ∀ i, FiniteDimensional K⟮ψ i x⟯ (F' i) := fun i =>
    finiteDimensional_adjoin_map hxfin (ψ i) (hfin i)
  haveI : ∀ i, PerfectField K⟮ψ i x⟯ := fun i => PerfectField.ofCharZero
  haveI : ∀ i, Algebra.IsSeparable K⟮ψ i x⟯ (F' i) := fun i =>
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hprim : ∀ i, ∃ u : F' i, K⟮ψ i x⟯⟮u⟯ = ⊤ := fun i =>
    Field.exists_primitive_element K⟮ψ i x⟯ (F' i)
  choose u hu using hprim
  have hxu : ∀ i, K⟮ψ i x, u i⟯ = ⊤ := fun i => by
    rw [← adjoin_simple_adjoin_simple, hu i, restrictScalars_top]

  have halg : ∀ i, IsAlgebraic K⟮ψ i x⟯ (u i) := fun i => Algebra.IsAlgebraic.isAlgebraic (u i)
  choose qi hqi0 hqiu using halg
  have hcoefi : ∀ i j, ∃ r' s' : K[X], ((qi i).coeff j : F' i) = aeval (ψ i x) r' / aeval (ψ i x) s' :=
    fun i j => (mem_adjoin_simple_iff (F := K) _).1 ((qi i).coeff j).2
  choose ri si hrsi using hcoefi
  have hreli : ∀ i, ∑ j ∈ (qi i).support,
      (aeval (ψ i x) (ri i j) / aeval (ψ i x) (si i j)) * u i ^ j = 0 := fun i => by
    have h := hqiu i
    rw [aeval_def, eval₂_eq_sum, Polynomial.sum_def] at h
    simp_rw [← hrsi i]
    exact h
  have hnei : ∀ i, ∃ j ∈ (qi i).support,
      aeval (ψ i x) (ri i j) / aeval (ψ i x) (si i j) ≠ 0 := fun i => by
    obtain ⟨j, hj⟩ := Polynomial.support_nonempty.2 (hqi0 i)
    refine ⟨j, hj, ?_⟩
    rw [← hrsi i]
    exact fun h => (mem_support_iff.1 hj) (ZeroMemClass.coe_eq_zero.1 h)

  set tt : ∀ i, Fin 3 → F' i := fun i => ![φ i x, φ i y, ψ i y] with htt
  have hrepr : ∀ i (z : F' i), ∃ P Q : K⟮ψ i x⟯[X], z = aeval (u i) P / aeval (u i) Q :=
    fun i z => (mem_adjoin_simple_iff (F := K⟮ψ i x⟯) _).1 (by rw [hu i]; exact mem_top)
  choose P Q hPQ using hrepr
  have hcoefP : ∀ i (z : F' i) (n : ℕ), ∃ r' s' : K[X],
      (((P i z).coeff n : K⟮ψ i x⟯) : F' i) = aeval (ψ i x) r' / aeval (ψ i x) s' :=
    fun i z n => (mem_adjoin_simple_iff (F := K) _).1 ((P i z).coeff n).2
  have hcoefQ : ∀ i (z : F' i) (n : ℕ), ∃ r' s' : K[X],
      (((Q i z).coeff n : K⟮ψ i x⟯) : F' i) = aeval (ψ i x) r' / aeval (ψ i x) s' :=
    fun i z n => (mem_adjoin_simple_iff (F := K) _).1 ((Q i z).coeff n).2
  choose rp sp hrsp using hcoefP
  choose rq sq hrsq using hcoefQ

  let C₁ : Set K := ⋃ j ∈ J, (((r j).coeffs ∪ (s j).coeffs : Finset K) : Set K)
  let C₂ : Set K := ⋃ i : ι, ⋃ j ∈ (qi i).support,
    (((ri i j).coeffs ∪ (si i j).coeffs : Finset K) : Set K)
  let C₃ : Set K := ⋃ i : ι, ⋃ l : Fin 3,
    ⋃ n ∈ ((P i (tt i l)).support ∪ (Q i (tt i l)).support),
      (((rp i (tt i l) n).coeffs ∪ (sp i (tt i l) n).coeffs ∪
        ((rq i (tt i l) n).coeffs ∪ (sq i (tt i l) n).coeffs) : Finset K) : Set K)
  let C : Set K := C₁ ∪ (C₂ ∪ C₃)
  have hCfin : C.Finite := by
    refine Set.Finite.union ?_ (Set.Finite.union ?_ ?_)
    · exact Set.Finite.biUnion J.finite_toSet fun j _ => Finset.finite_toSet _
    · exact Set.finite_iUnion fun i =>
        Set.Finite.biUnion (Finset.finite_toSet _) fun j _ => Finset.finite_toSet _
    · exact Set.finite_iUnion fun i => Set.finite_iUnion fun l =>
        Set.Finite.biUnion (Finset.finite_toSet _) fun n _ => Finset.finite_toSet _
  let L : Subfield K := Subfield.closure C
  let K₀ : IntermediateField L K := algebraicClosure L K
  haveI : IsAlgClosed K₀ := IsAlgClosure.isAlgClosed L
  haveI : Countable L := by
    haveI : Countable C := hCfin.countable.to_subtype
    rw [← Cardinal.mk_le_aleph0_iff]
    exact (Subfield.cardinalMk_closure_le_max C).trans (max_le Cardinal.mk_le_aleph0 le_rfl)
  haveI : Countable K₀ := by
    rw [← Cardinal.mk_le_aleph0_iff]
    exact (Algebra.IsAlgebraic.cardinalMk_le_max L K₀).trans
      (max_le Cardinal.mk_le_aleph0 le_rfl)
  haveI : CharZero K₀ := charZero_of_injective_algebraMap (algebraMap L K₀).injective
  have hCK₀ : C ⊆ Set.range (algebraMap K₀ K) := by
    intro c hc
    exact ⟨⟨c, K₀.algebraMap_mem ⟨c, Subfield.subset_closure hc⟩⟩, rfl⟩

  have hlift : ∀ p : K[X], (p.coeffs : Set K) ⊆ C →
      ∃ p₀ : K₀[X], p₀.map (algebraMap K₀ K) = p := fun p hp =>
    (mem_lifts _).1 ((lifts_iff_coeffs_subset_range _).2 (hp.trans hCK₀))

  have hrC : ∀ j ∈ J, ((r j).coeffs : Set K) ⊆ C := fun j hj c hc =>
    Set.mem_union_left _ (Set.mem_biUnion hj (by simp [hc]))
  have hsC : ∀ j ∈ J, ((s j).coeffs : Set K) ⊆ C := fun j hj c hc =>
    Set.mem_union_left _ (Set.mem_biUnion hj (by simp [hc]))
  have hr₀ : ∀ j, ∃ p₀ : K₀[X], j ∈ J → p₀.map (algebraMap K₀ K) = r j := fun j => by
    by_cases hj : j ∈ J
    · obtain ⟨p₀, hp₀⟩ := hlift _ (hrC j hj); exact ⟨p₀, fun _ => hp₀⟩
    · exact ⟨0, fun h => absurd h hj⟩
  have hs₀ : ∀ j, ∃ p₀ : K₀[X], j ∈ J → p₀.map (algebraMap K₀ K) = s j := fun j => by
    by_cases hj : j ∈ J
    · obtain ⟨p₀, hp₀⟩ := hlift _ (hsC j hj); exact ⟨p₀, fun _ => hp₀⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose r₀ hr₀ using hr₀
  choose s₀ hs₀ using hs₀
  have hrel' : ∑ j ∈ J, (aeval x (r₀ j) / aeval x (s₀ j)) * y ^ j = 0 := by
    rw [← hrel]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← aeval_map_algebraMap K x (r₀ j), ← aeval_map_algebraMap K x (s₀ j), hr₀ j hj, hs₀ j hj]
  have hne' : ∃ j ∈ J, aeval x (r₀ j) / aeval x (s₀ j) ≠ 0 := by
    obtain ⟨j, hj, hne⟩ := hne
    refine ⟨j, hj, ?_⟩
    rwa [← aeval_map_algebraMap K x (r₀ j), ← aeval_map_algebraMap K x (s₀ j), hr₀ j hj,
      hs₀ j hj]

  have hriC : ∀ i, ∀ j ∈ (qi i).support, ((ri i j).coeffs : Set K) ⊆ C ∧
      ((si i j).coeffs : Set K) ⊆ C := by
    intro i j hj
    have hsub : (((ri i j).coeffs ∪ (si i j).coeffs : Finset K) : Set K) ⊆ C := by
      intro c hc
      refine Set.mem_union_right _ (Set.mem_union_left _ ?_)
      exact Set.mem_iUnion.2 ⟨i, Set.mem_biUnion (Finset.mem_coe.2 hj) hc⟩
    refine ⟨?_, ?_⟩ <;> intro c hc <;> apply hsub <;> simp [hc]
  have hri₀ : ∀ i j, ∃ p₀ : K₀[X], j ∈ (qi i).support → p₀.map (algebraMap K₀ K) = ri i j :=
    fun i j => by
    by_cases hj : j ∈ (qi i).support
    · obtain ⟨p₀, hp₀⟩ := hlift _ (hriC i j hj).1; exact ⟨p₀, fun _ => hp₀⟩
    · exact ⟨0, fun h => absurd h hj⟩
  have hsi₀ : ∀ i j, ∃ p₀ : K₀[X], j ∈ (qi i).support → p₀.map (algebraMap K₀ K) = si i j :=
    fun i j => by
    by_cases hj : j ∈ (qi i).support
    · obtain ⟨p₀, hp₀⟩ := hlift _ (hriC i j hj).2; exact ⟨p₀, fun _ => hp₀⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose ri₀ hri₀ using hri₀
  choose si₀ hsi₀ using hsi₀
  have hreli' : ∀ i, ∑ j ∈ (qi i).support,
      (aeval (ψ i x) (ri₀ i j) / aeval (ψ i x) (si₀ i j)) * u i ^ j = 0 := fun i => by
    rw [← hreli i]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← aeval_map_algebraMap K (ψ i x) (ri₀ i j), ← aeval_map_algebraMap K (ψ i x) (si₀ i j),
      hri₀ i j hj, hsi₀ i j hj]
  have hnei' : ∀ i, ∃ j ∈ (qi i).support,
      aeval (ψ i x) (ri₀ i j) / aeval (ψ i x) (si₀ i j) ≠ 0 := fun i => by
    obtain ⟨j, hj, hne⟩ := hnei i
    refine ⟨j, hj, ?_⟩
    rwa [← aeval_map_algebraMap K (ψ i x) (ri₀ i j), ← aeval_map_algebraMap K (ψ i x) (si₀ i j),
      hri₀ i j hj, hsi₀ i j hj]

  have htC : ∀ i (l : Fin 3), ∀ n ∈ (P i (tt i l)).support ∪ (Q i (tt i l)).support,
      ((rp i (tt i l) n).coeffs : Set K) ⊆ C ∧ ((sp i (tt i l) n).coeffs : Set K) ⊆ C ∧
        ((rq i (tt i l) n).coeffs : Set K) ⊆ C ∧ ((sq i (tt i l) n).coeffs : Set K) ⊆ C := by
    intro i l n hn
    have hsub : (((rp i (tt i l) n).coeffs ∪ (sp i (tt i l) n).coeffs ∪
        ((rq i (tt i l) n).coeffs ∪ (sq i (tt i l) n).coeffs) : Finset K) : Set K) ⊆ C := by
      intro c hc
      refine Set.mem_union_right _ (Set.mem_union_right _ ?_)
      exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨l, Set.mem_biUnion (Finset.mem_coe.2 hn) hc⟩⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro c hc <;> apply hsub <;> simp [hc]

  obtain ⟨x₀, y₀, hx₀x, hy₀y, hx₀, hfin₀, htop₀⟩ :=
    Correspondence.descent_abstract (hx.of_tower_top K₀) J r₀ s₀ hrel' hne'

  have hdesc' : ∀ i, ∃ x₀' u₀' : K₀⟮ψ i x, u i⟯, (x₀' : F' i) = ψ i x ∧ (u₀' : F' i) = u i ∧
      Transcendental K₀ x₀' ∧ FiniteDimensional K₀⟮x₀'⟯ K₀⟮ψ i x, u i⟯ ∧ K₀⟮x₀', u₀'⟯ = ⊤ :=
    fun i => Correspondence.descent_abstract ((hxi i).of_tower_top K₀) _ (ri₀ i) (si₀ i)
      (hreli' i) (hnei' i)
  choose x₀' u₀' hx₀'x hu₀'u hx₀' hfin₀' htop₀' using hdesc'

  have hxM : x ∈ K₀⟮x, y⟯ := subset_adjoin K₀ _ (by simp)
  have hyM : y ∈ K₀⟮x, y⟯ := subset_adjoin K₀ _ (by simp)
  have hxiM : ∀ i, ψ i x ∈ K₀⟮ψ i x, u i⟯ := fun i => subset_adjoin K₀ _ (by simp)
  have huiM : ∀ i, u i ∈ K₀⟮ψ i x, u i⟯ := fun i => subset_adjoin K₀ _ (by simp)

  have httM : ∀ i (l : Fin 3), tt i l ∈ K₀⟮ψ i x, u i⟯ := by
    intro i l
    rw [hPQ i (tt i l)]
    refine div_mem ?_ ?_
    · exact aeval_mem_of_repr (hxiM i) (huiM i) (P i (tt i l)) (rp i (tt i l)) (sp i (tt i l))
        (hrsp i (tt i l))
        (fun n hn => hlift _ (htC i l n (Finset.mem_union_left _ hn)).1)
        (fun n hn => hlift _ (htC i l n (Finset.mem_union_left _ hn)).2.1)
    · exact aeval_mem_of_repr (hxiM i) (huiM i) (Q i (tt i l)) (rq i (tt i l)) (sq i (tt i l))
        (hrsq i (tt i l))
        (fun n hn => hlift _ (htC i l n (Finset.mem_union_right _ hn)).2.2.1)
        (fun n hn => hlift _ (htC i l n (Finset.mem_union_right _ hn)).2.2.2)
  have hφxM : ∀ i, φ i x ∈ K₀⟮ψ i x, u i⟯ := fun i => by simpa [htt] using httM i 0
  have hφyM : ∀ i, φ i y ∈ K₀⟮ψ i x, u i⟯ := fun i => by simpa [htt] using httM i 1
  have hψyM : ∀ i, ψ i y ∈ K₀⟮ψ i x, u i⟯ := fun i => by simpa [htt] using httM i 2

  have hmapφ : ∀ i, ∀ z ∈ K₀⟮x, y⟯, φ i z ∈ K₀⟮ψ i x, u i⟯ := by
    intro i
    have hle : K₀⟮x, y⟯ ≤ K₀⟮ψ i x, u i⟯.comap ((φ i).restrictScalars K₀) := by
      rw [adjoin_le_iff]
      rintro z (rfl | h)
      · exact hφxM i
      · rw [Set.mem_singleton_iff.1 h]; exact hφyM i
    exact fun z hz => hle hz
  have hmapψ : ∀ i, ∀ z ∈ K₀⟮x, y⟯, ψ i z ∈ K₀⟮ψ i x, u i⟯ := by
    intro i
    have hle : K₀⟮x, y⟯ ≤ K₀⟮ψ i x, u i⟯.comap ((ψ i).restrictScalars K₀) := by
      rw [adjoin_le_iff]
      rintro z (rfl | h)
      · exact hxiM i
      · rw [Set.mem_singleton_iff.1 h]; exact hψyM i
    exact fun z hz => hle hz
  -- `let` rather than the pin's `set ... with`: neither equation lemma is used, and `set`
  -- additionally abstracts occurrences of its term in the goal, which here is the whole
  -- `∃`-pack.  The bodies must stay zeta-transparent, since the proof below reads `φ₀ i xF`
  -- definitionally as `φ i x`.
  let φ₀ : ∀ i, K₀⟮x, y⟯ →ₐ[K₀] K₀⟮ψ i x, u i⟯ :=
    fun i => restrictHom (φ i) (K₀⟮x, y⟯) (K₀⟮ψ i x, u i⟯) (hmapφ i)
  let ψ₀ : ∀ i, K₀⟮x, y⟯ →ₐ[K₀] K₀⟮ψ i x, u i⟯ :=
    fun i => restrictHom (ψ i) (K₀⟮x, y⟯) (K₀⟮ψ i x, u i⟯) (hmapψ i)

  let xF : K₀⟮x, y⟯ := ⟨x, hxM⟩
  have hxFtr : ∀ i, Transcendental K₀ (φ₀ i xF) := fun i h => by
    have h' : IsAlgebraic K₀ (φ i x) :=
      (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom K₀ K₀⟮ψ i x, u i⟯ (F' i))
        (algebraMap K₀⟮ψ i x, u i⟯ (F' i)).injective).2 h
    have hφx : Transcendental K (φ i x) := fun h'' =>
      hx ((isAlgebraic_algHom_iff (φ i) (φ i).toRingHom.injective).mp h'')
    exact (hφx.of_tower_top K₀) h'
  have hxFtrψ : ∀ i, Transcendental K₀ (ψ₀ i xF) := fun i h => by
    have h' : IsAlgebraic K₀ (ψ i x) :=
      (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom K₀ K₀⟮ψ i x, u i⟯ (F' i))
        (algebraMap K₀⟮ψ i x, u i⟯ (F' i)).injective).2 h
    exact ((hxi i).of_tower_top K₀) h'

  have hgen₀' : ∀ i, IntermediateField.adjoin K₀
      (({x₀' i, u₀' i} : Finset K₀⟮ψ i x, u i⟯) : Set K₀⟮ψ i x, u i⟯) = ⊤ := fun i => by
    rw [Finset.coe_insert, Finset.coe_singleton]
    exact htop₀' i
  haveI : ∀ i, FiniteDimensional K₀⟮x₀' i⟯ K₀⟮ψ i x, u i⟯ := hfin₀'
  have hfinφ₀ : ∀ i, FiniteAlong K₀ (φ₀ i) := fun i =>
    finiteAlong_of_transcendental_image (φ₀ i) _ (hgen₀' i) (x₀' i) xF (hxFtr i)
  have hfinψ₀ : ∀ i, FiniteAlong K₀ (ψ₀ i) := fun i =>
    finiteAlong_of_transcendental_image (ψ₀ i) _ (hgen₀' i) (x₀' i) xF (hxFtrψ i)

  haveI : CharZero K₀⟮x, y⟯ := charZero_of_injective_algebraMap (algebraMap K₀ K₀⟮x, y⟯).injective
  -- `hfin₀`/`hfin₀'` are ordinary hypotheses; registering them keeps the
  -- `Algebra.IsAlgebraic` search below from wandering (the pin raised
  -- `synthInstance.maxHeartbeats` instead).
  haveI hfd₀ : FiniteDimensional K₀⟮x₀⟯ K₀⟮x, y⟯ := hfin₀
  haveI : Algebra.IsAlgebraic K₀⟮x₀⟯ K₀⟮x, y⟯ :=
    Algebra.IsAlgebraic.of_finite ↥(K₀⟮x₀⟯) ↥(K₀⟮x, y⟯)
  haveI : Algebra.IsSeparable K₀⟮x₀⟯ K₀⟮x, y⟯ := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hC₀ : IsCurveOver K₀ K₀⟮x, y⟯ :=
    isCurveOver_of_transcendental_of_isSeparable K₀ K₀⟮x, y⟯ x₀ hx₀ hfin₀ inferInstance
  haveI : ∀ i, CharZero K₀⟮ψ i x, u i⟯ := fun i =>
    charZero_of_injective_algebraMap (algebraMap K₀ K₀⟮ψ i x, u i⟯).injective
  haveI : ∀ i, Algebra.IsAlgebraic K₀⟮x₀' i⟯ K₀⟮ψ i x, u i⟯ := fun i =>
    Algebra.IsAlgebraic.of_finite ↥(K₀⟮x₀' i⟯) ↥(K₀⟮ψ i x, u i⟯)
  haveI : ∀ i, Algebra.IsSeparable K₀⟮x₀' i⟯ K₀⟮ψ i x, u i⟯ := fun i =>
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hC₀' : ∀ i, IsCurveOver K₀ K₀⟮ψ i x, u i⟯ := fun i =>
    isCurveOver_of_transcendental_of_isSeparable K₀ K₀⟮ψ i x, u i⟯ (x₀' i) (hx₀' i)
      (hfin₀' i) inferInstance
  have hgenF : IntermediateField.adjoin K (Set.range (algebraMap K₀⟮x, y⟯ F)) = ⊤ := by
    rw [eq_top_iff, ← hxy]
    refine adjoin.mono K _ _ ?_
    rintro z (rfl | h)
    · exact ⟨⟨z, hxM⟩, rfl⟩
    · rw [Set.mem_singleton_iff.1 h]; exact ⟨⟨y, hyM⟩, rfl⟩
  have hgenF' : ∀ i, IntermediateField.adjoin K (Set.range (algebraMap K₀⟮ψ i x, u i⟯ (F' i))) = ⊤ := by
    intro i
    rw [eq_top_iff, ← hxu i]
    refine adjoin.mono K _ _ ?_
    rintro z (rfl | h)
    · exact ⟨⟨ψ i x, hxiM i⟩, rfl⟩
    · rw [Set.mem_singleton_iff.1 h]; exact ⟨⟨u i, huiM i⟩, rfl⟩

  obtain ⟨χ⟩ := Field.nonempty_ringHom_complex_of_countable K₀
  refine ⟨K₀, K₀⟮x, y⟯, fun i => K₀⟮ψ i x, u i⟯, inferInstance, inferInstance, inferInstance, inferInstance,
    χ.toAlgebra, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, hC₀, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hC₀', φ₀, ψ₀, ⟨x₀, hx₀, hfin₀⟩, hgenF, fun i => ⟨x₀' i, hx₀' i, hfin₀' i⟩,
    hgenF', fun i f => rfl, fun i f => rfl, hfinφ₀, hfinψ₀⟩

end AlgebraicCurve
