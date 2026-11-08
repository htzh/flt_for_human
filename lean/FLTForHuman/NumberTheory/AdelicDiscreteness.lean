/-
  The diagonal image of `K` in `𝔸_K` meets a compact set finitely.

  `finite_setOf_algebraMap_mem_of_isCompact`: for a compact `C ⊆ 𝔸_K`, the set of `ξ : K` whose
  adelic image `algebraMap K 𝔸_K ξ` lies in `C` is **finite** — the discreteness of `K` in `𝔸_K`,
  stated in the form the measure theory consumes: a compact set meets the rational points finitely
  many times.

  The proof reads `𝔸_K = 𝔸_K^∞ × 𝔸_K^fin`. On the finite side an open subgroup of `𝔸_K^fin` cuts
  `C` into finitely many cosets `y + ∫_fin` (`elim_nhds_subcover`), the integral finite adèles;
  on the infinite side two points of the same coset differ by an element of the lattice `𝓞 K`
  inside the mixed space, and a discrete lattice meets a bounded closed set finitely
  (`Metric.finite_isBounded_inter_isClosed`). Then each coset contributes finitely many `ξ`.

  This is the engine of the closedness of the rational subgroups of `GL₂(𝔸_K)`
  (`AutomorphicForm/Adelic/RationalUnipotentClosed.lean`) and of the finiteness of the masses of
  the rational (centre-)unipotent Haar measures
  (`AutomorphicForm/Adelic/RationalUnipotentHaar.lean`).

  Transcribed from `Theorems/Thm_NumberField_AdeleRing_finite_setOf_algebraMap_mem_of_isCompact.lean`
  and `P2M/Sol/S_NumberField_AdeleRing_finite_setOf_algebraMap_mem_of_isCompact.lean` (pinned
  `aa2d8b3`, 123 lines); the `S_` file proves the headline through one 70-line engine
  `finite_setOf_algebraMap_mem` in its own `M4aP3B.Rows.DiscreteAdele` block. The module is new
  rather than an insertion into `NumberTheory/AdelicBox.lean` because the box is a hub with many
  in-tree importers and this is one self-contained subject above it.

  **Wiring.** `spec/check_port.py` owns the declarations here.
  spec-pin: Theorems/Thm_NumberField_AdeleRing_finite_setOf_algebraMap_mem_of_isCompact.lean
  spec-pin: P2M/Sol/S_NumberField_AdeleRing_finite_setOf_algebraMap_mem_of_isCompact.lean
-/
import FLTForHuman.NumberTheory.AdelicBox
import Mathlib.Algebra.Module.ZLattice.Basic

set_option autoImplicit false

open NumberField IsDedekindDomain NumberField.AdelicBox
open NumberField.AdelicLevel (integralFiniteAdeles)

noncomputable section

namespace NumberField.AdeleRing

variable (F : Type) [Field F] [NumberField F]

theorem fst_algebraMap (ξ : F) :
    (algebraMap F (AdeleRing (𝓞 F) F) ξ).1 = algebraMap F (InfiniteAdeleRing F) ξ := rfl

theorem zero_mem_integralFiniteAdeles' :
    (0 : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F :=
  fun _ => zero_mem _

theorem finite_setOf_algebraMap_mem {C : Set (AdeleRing (𝓞 F) F)} (hC : IsCompact C) :
    {ξ : F | algebraMap F (AdeleRing (𝓞 F) F) ξ ∈ C}.Finite := by
  classical
  have hO : IsOpen (integralFiniteAdeles (𝓞 F) F) :=
    NumberField.AdelicBox.isOpen_integralFiniteAdeles F
  have hCf : IsCompact (Prod.snd '' C) := hC.image continuous_snd
  obtain ⟨t, -, hcover⟩ := hCf.elim_nhds_subcover
    (fun y => (fun z => z - y) ⁻¹' integralFiniteAdeles (𝓞 F) F) fun y _ =>
      (hO.preimage (continuous_id.sub continuous_const)).mem_nhds
        (by simpa only [Set.mem_preimage, Pi.sub_apply, id_eq, sub_self]
          using zero_mem_integralFiniteAdeles' F)
  have hCinf : IsCompact (InfiniteAdeleRing.ringEquiv_mixedSpace F '' (Prod.fst '' C)) :=
    (hC.image continuous_fst).image (continuous_ringEquiv_mixedSpace F)
  have hD : IsCompact ((fun p : mixedEmbedding.mixedSpace F × mixedEmbedding.mixedSpace F =>
      p.1 - p.2) '' ((InfiniteAdeleRing.ringEquiv_mixedSpace F '' (Prod.fst '' C)) ×ˢ
        (InfiniteAdeleRing.ringEquiv_mixedSpace F '' (Prod.fst '' C)))) :=
    (hCinf.prod hCinf).image (continuous_fst.sub continuous_snd)
  have hLdisc : IsDiscrete
      ((mixedEmbedding.integerLattice F : Submodule ℤ (mixedEmbedding.mixedSpace F)) :
        Set (mixedEmbedding.mixedSpace F)) :=
    isDiscrete_iff_discreteTopology.mpr
      (inferInstanceAs (DiscreteTopology (mixedEmbedding.integerLattice F)))
  have hLclosed : IsClosed
      ((mixedEmbedding.integerLattice F : Submodule ℤ (mixedEmbedding.mixedSpace F)) :
        Set (mixedEmbedding.mixedSpace F)) :=
    AddSubgroup.isClosed_of_isDiscrete
      (mixedEmbedding.integerLattice F).toAddSubgroup hLdisc
  have hL : ((fun p : mixedEmbedding.mixedSpace F × mixedEmbedding.mixedSpace F => p.1 - p.2) ''
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F '' (Prod.fst '' C)) ×ˢ
        (InfiniteAdeleRing.ringEquiv_mixedSpace F '' (Prod.fst '' C))) ∩
      (mixedEmbedding.integerLattice F : Set (mixedEmbedding.mixedSpace F))).Finite :=
    Metric.finite_isBounded_inter_isClosed hLdisc hD.isBounded hLclosed

  have hT : ∀ y : FiniteAdeleRing (𝓞 F) F,
      {ξ : F | algebraMap F (AdeleRing (𝓞 F) F) ξ ∈ C ∧
        (algebraMap F (AdeleRing (𝓞 F) F) ξ).2 - y ∈ integralFiniteAdeles (𝓞 F) F}.Finite := by
    intro y
    rcases Set.eq_empty_or_nonempty {ξ : F | algebraMap F (AdeleRing (𝓞 F) F) ξ ∈ C ∧
        (algebraMap F (AdeleRing (𝓞 F) F) ξ).2 - y ∈ integralFiniteAdeles (𝓞 F) F} with
      h0 | ⟨ξ₀, hξ₀C, hξ₀y⟩
    · rw [h0]; exact Set.finite_empty
    refine (hL.preimage (f := fun ξ : F => mixedEmbedding F (ξ - ξ₀)) fun a _ b _ h =>
      sub_left_inj.1 (mixedEmbedding_injective F h)).subset ?_
    rintro ξ ⟨hξC, hξy⟩
    refine ⟨?_, ?_⟩
    ·
      refine ⟨(InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (AdeleRing (𝓞 F) F) ξ).1,
          InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (AdeleRing (𝓞 F) F) ξ₀).1),
        ⟨⟨(algebraMap F (AdeleRing (𝓞 F) F) ξ).1, ⟨_, hξC, rfl⟩, rfl⟩,
          ⟨(algebraMap F (AdeleRing (𝓞 F) F) ξ₀).1, ⟨_, hξ₀C, rfl⟩, rfl⟩⟩, ?_⟩
      show InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (AdeleRing (𝓞 F) F) ξ).1
          - InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (AdeleRing (𝓞 F) F) ξ₀).1
        = mixedEmbedding F (ξ - ξ₀)
      rw [map_sub, fst_algebraMap, fst_algebraMap,
        ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp,
        ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
    ·
      have h2 : (algebraMap F (AdeleRing (𝓞 F) F) (ξ - ξ₀)).2
          = (algebraMap F (AdeleRing (𝓞 F) F) ξ).2 - (algebraMap F (AdeleRing (𝓞 F) F) ξ₀).2 := by
        rw [map_sub]; rfl
      have hdiff : (algebraMap F (AdeleRing (𝓞 F) F) (ξ - ξ₀)).2 ∈ integralFiniteAdeles (𝓞 F) F := by
        rw [h2, ← sub_sub_sub_cancel_right _ _ y]
        exact fun v => sub_mem (hξy v) (hξ₀y v)
      have hval : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (ξ - ξ₀) ≤ 1 := fun v => by
        have h := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 (hdiff v)
        rwa [algebraMap_snd_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
      obtain ⟨o, ho⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F (ξ - ξ₀) hval
      show mixedEmbedding F (ξ - ξ₀) ∈
        (mixedEmbedding.integerLattice F : Set (mixedEmbedding.mixedSpace F))
      rw [← ho]
      exact ⟨o, rfl⟩

  refine (t.finite_toSet.biUnion fun y _ => hT y).subset fun ξ hξ => ?_
  have h2 : (algebraMap F (AdeleRing (𝓞 F) F) ξ).2 ∈ Prod.snd '' C := ⟨_, hξ, rfl⟩
  obtain ⟨y, hy, hyO⟩ := Set.mem_iUnion₂.1 (hcover h2)
  exact Set.mem_iUnion₂.2 ⟨y, hy, hξ, hyO⟩

theorem finite_setOf_algebraMap_mem_of_isCompact_impl (F : Type) [Field F] [NumberField F]
    {C : Set (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)} (hC : IsCompact C) :
    {ξ : F | algebraMap F (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) ξ ∈ C}.Finite :=
  finite_setOf_algebraMap_mem F hC

theorem gate_empty (F : Type) [Field F] [NumberField F] :
    {ξ : F | algebraMap F (AdeleRing (𝓞 F) F) ξ ∈ (∅ : Set (AdeleRing (𝓞 F) F))} = ∅ := by
  ext ξ; simp

theorem gate_univ_infinite (F : Type) [Field F] [NumberField F] :
    {ξ : F | algebraMap F (AdeleRing (𝓞 F) F) ξ ∈ (Set.univ : Set (AdeleRing (𝓞 F) F))}.Infinite := by
  simp only [Set.mem_univ, Set.ofPred_true]
  exact Set.infinite_univ

/-- **Discreteness of `K` in `𝔸_K`, in compact form.** A compact set of adèles contains the
image of finitely many elements of `K`. -/
theorem finite_setOf_algebraMap_mem_of_isCompact
    (F : Type) [Field F] [NumberField F]
    {C : Set (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)} (hC : IsCompact C) :
    {ξ : F | algebraMap F (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) ξ ∈ C}.Finite :=
  finite_setOf_algebraMap_mem_of_isCompact_impl F hC

end NumberField.AdeleRing

end
