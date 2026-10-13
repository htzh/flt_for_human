/-
  Countability of the adèlic building blocks.

  The adèle ring `𝔸_K` is second countable: the ideal lattice of `𝓞_K` is countable,
  hence so is `HeightOneSpectrum`, and each completion is a second-countable valued
  field; the restricted product of second-countable factors over a countable index
  is second countable, and the infinite places contribute a countable product of
  second-countable completions. This is the countability input the place-measure and
  Bruhat-transversal layers need.

  Transcribed from `S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean`
  lines 24–142 (pinned `aa2d8b3`), the pin namespace `NumberField.AdelicCountability`
  kept. The pin's `import Mathlib` is replaced by specific mathlib modules.
-/
import FLTForHuman.LinearAlgebra.Countable
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact

set_option autoImplicit false

open MeasureTheory Complex NumberField NumberField.InfinitePlace IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum TopologicalSpace Filter
open scoped Pointwise ENNReal NNReal

noncomputable section

namespace NumberField

namespace AdelicCountability

-- pin: instCountableIdeal (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:29)
scoped instance instCountableIdeal (R : Type*) [CommRing R] [Countable R] [IsNoetherianRing R] :
    Countable (Ideal R) := by
  have hsurj : Function.Surjective (fun s : Finset R => Ideal.span (s : Set R)) := by
    intro I
    obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I)
    exact ⟨s, hs⟩
  exact hsurj.countable

-- pin: instCountableHeightOneSpectrum (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:37)
scoped instance instCountableHeightOneSpectrum (R : Type*) [CommRing R] [IsDedekindDomain R]
    [Countable R] : Countable (HeightOneSpectrum R) := by
  have hinj : Function.Injective (fun v : HeightOneSpectrum R => v.asIdeal) := by
    intro v w h
    exact HeightOneSpectrum.ext h
  exact hinj.countable

-- pin: instCountableValueGroup₀ (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:44)
scoped instance instCountableValueGroup₀ {R Γ₀ : Type*} [CommRing R] [LinearOrderedCommGroupWithZero Γ₀]
    [Countable Γ₀] (v : R →*₀ Γ₀) : Countable (MonoidWithZeroHom.ValueGroup₀ v) :=
  MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.injective.countable

-- pin: instCountableUnits (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:48)
scoped instance instCountableUnits {M : Type*} [Monoid M] [Countable M] : Countable Mˣ :=
  Units.val_injective.countable

-- pin: instCountableWithZero (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:51)
scoped instance instCountableWithZero {α : Type*} [Countable α] : Countable (WithZero α) := by
  classical
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat α
  refine ⟨⟨fun x => if h : x = 0 then 0 else f (WithZero.unzero h) + 1, fun a b hab => ?_⟩⟩
  dsimp only [] at hab
  by_cases ha : a = 0 <;> by_cases hb : b = 0
  · rw [ha, hb]
  · rw [dite_eq_left ha, dite_eq_right hb] at hab
    exact absurd hab.symm (Nat.succ_ne_zero _)
  · rw [dite_eq_right ha, dite_eq_left hb] at hab
    exact absurd hab (Nat.succ_ne_zero _)
  · rw [dite_eq_right ha, dite_eq_right hb] at hab
    rw [← WithZero.coe_unzero ha, ← WithZero.coe_unzero hb, hf (Nat.add_right_cancel hab)]

-- pin: isCountablyGenerated_uniformity_of_valued (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:65)
theorem isCountablyGenerated_uniformity_of_valued (R : Type*) (Γ₀ : Type*) [Ring R]
    [LinearOrderedCommGroupWithZero Γ₀] [Countable Γ₀] [vR : Valued R Γ₀] :
    (uniformity R).IsCountablyGenerated :=
  (Valued.hasBasis_uniformity R Γ₀).isCountablyGenerated

-- pin: instSecondCountableAdicCompletion (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:70)
scoped instance instSecondCountableAdicCompletion (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] [Countable K] (v : HeightOneSpectrum R) :
    SecondCountableTopology (v.adicCompletion K) := by
  have hcg : (uniformity (v.adicCompletion K)).IsCountablyGenerated :=
    isCountablyGenerated_uniformity_of_valued _ (WithZero (Multiplicative ℤ))
  have hsep : SeparableSpace (v.adicCompletion K) :=
    ⟨_, Set.countable_range _, HeightOneSpectrum.denseRange_algebraMap (K := K) (v := v)⟩
  exact UniformSpace.secondCountable_of_separable _

open RestrictedProduct Topology in
-- the pin's `haveI` is load-bearing: it feeds the instance search below.
set_option linter.style.haveILetI false in
-- pin: secondCountableTopology_restrictedProduct (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:79)
theorem secondCountableTopology_restrictedProduct {ι : Type*} [Countable ι]
    {R : ι → Type*} {B : ∀ i, Set (R i)}
    [∀ i, TopologicalSpace (R i)] [∀ i, SecondCountableTopology (R i)]
    (hBo : ∀ i, IsOpen (B i)) :
    SecondCountableTopology (Πʳ i, [R i, B i]_[Filter.cofinite]) := by

  have hprin : ∀ t : Finset ι, Filter.cofinite ≤ Filter.principal ((↑t : Set ι)ᶜ) := fun t =>
    Filter.le_principal_iff.mpr (Filter.mem_cofinite.mpr (by simp))

  have hpiece : ∀ t : Finset ι,
      SecondCountableTopology (Πʳ i, [R i, B i]_[Filter.principal ((↑t : Set ι)ᶜ)]) := fun t =>
    (isEmbedding_coe_of_principal).secondCountableTopology

  set U : Finset ι → Set (Πʳ i, [R i, B i]_[Filter.cofinite]) :=
    fun t => Set.range (inclusion R B (hprin t)) with hU
  have hUopen : ∀ t, IsOpen (U t) := fun t =>
    (isOpenEmbedding_inclusion_principal hBo (hprin t)).isOpen_range
  have hUsc : ∀ t, SecondCountableTopology (U t) := by
    intro t
    haveI := hpiece t
    exact (((isOpenEmbedding_inclusion_principal hBo (hprin t)).isEmbedding.toHomeomorph).symm).isEmbedding.secondCountableTopology
  have hcover : ⋃ t : Finset ι, U t = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    have hfin : {i | x.1 i ∉ B i}.Finite := Filter.eventually_cofinite.mp x.2
    refine ⟨hfin.toFinset, ⟨x.1, ?_⟩, rfl⟩
    rw [Filter.eventually_principal]
    intro i hi
    by_contra hmem
    exact hi (by simpa using hfin.mem_toFinset.mpr hmem)
  exact TopologicalSpace.secondCountableTopology_of_countable_cover hUopen hcover

open IsDedekindDomain in
open scoped RestrictedProduct in

-- the pin's `haveI` is load-bearing: it feeds the instance search below.
set_option linter.style.haveILetI false in
-- pin: instSecondCountableFiniteAdeleRing (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:115)
scoped instance instSecondCountableFiniteAdeleRing (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] [Countable R] [Countable K] :
    SecondCountableTopology (FiniteAdeleRing R K) := by
  haveI : SecondCountableTopology
      (Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]) :=
    secondCountableTopology_restrictedProduct fun v => Valued.isOpen_valuationSubring _
  exact inferInstanceAs <| SecondCountableTopology <|
    Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]

-- the pin's `haveI` walls are load-bearing: they feed the instance search below.
set_option linter.style.haveILetI false in
-- pin: instSecondCountableInfiniteAdeleRing (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:124)
scoped instance instSecondCountableInfiniteAdeleRing (K : Type*) [Field K] [NumberField K] :
    SecondCountableTopology (InfiniteAdeleRing K) := by
  haveI : ∀ v : InfinitePlace K, SecondCountableTopology v.Completion := by
    intro v
    haveI : Countable (WithAbs v.1) := (WithAbs.equiv v.1).toEquiv.injective.countable
    haveI : SecondCountableTopology v.1.Completion := UniformSpace.secondCountable_of_separable _
    exact (NumberField.InfinitePlace.Completion.isometryEquivCompletion v).toHomeomorph.secondCountableTopology
  exact inferInstanceAs <| SecondCountableTopology <| (v : InfinitePlace K) → v.Completion

-- pin: instSecondCountableAdeleRing (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:133)
scoped instance instSecondCountableAdeleRing (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [NumberField K] [Algebra R K] [IsFractionRing R K] [Countable R] :
    SecondCountableTopology (AdeleRing R K) :=
  inferInstanceAs <| SecondCountableTopology (InfiniteAdeleRing K × FiniteAdeleRing R K)

-- pin: instCountableRingOfIntegers (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:138)
scoped instance instCountableRingOfIntegers (K : Type*) [Field K] [NumberField K] :
    Countable (NumberField.RingOfIntegers K) :=
  Subtype.countable

end AdelicCountability

end NumberField

end
