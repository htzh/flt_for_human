/-
  Cross-module wire test for the adèlic Fourier transform of a pure tensor (`AF75B`).

  A `spec/` probe, not a library module. The whole zone is at the base field `F = ℚ`, where the
  pin's abstract objects have concrete shapes:

  * `𝓞 ℚ = ℤ` has `ℤ`-rank one, so the mixed space is a **single real coordinate**,
    `mixedEmbedding.mixedSpace ℚ ≃ (Fin 1 → ℝ)` — see `mixedSpaceEquivFinOne`;
  * the box `adelicBox ℚ` is the unit interval's fundamental domain times the integral finite
    adèles, and the origin lies in it (`zero_mem_adelicBox_rat`);
  * the covolume of the integer lattice is the volume of that fundamental domain, hence
    positive (`covolume_integerLattice_rat_pos`);
  * the change-of-variable law at `a = 1` must have module `1` (`fourierIntegral_comp_one_rat`).

  Every zone is a real composition — no `#check` — so deleting the module (or leaving a hole in
  it) breaks this file.
-/
import FLTForHuman.NumberTheory.AdelicFourier.Transform

set_option autoImplicit false

noncomputable section

open NumberField NumberField.AdelicBox NumberField.InfiniteAdeleRing NumberField.AdelicFourier
open IsDedekindDomain
open MeasureTheory
open scoped Classical NNReal ENNReal NumberField.AdelicCountability

namespace AdelicFourierSetAF75BConsumer

/-! ### The concrete shape of `mixedEmbedding.mixedSpace ℚ` -/

/-- `𝓞 ℚ = ℤ` has `ℤ`-rank one, so the `ℝ`-basis of the mixed space is indexed by a singleton:
`mixedSpace ℚ` is one real coordinate. -/
theorem card_chooseBasisIndex_rat :
    Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 ℚ)) = 1 := by
  rw [← Module.finrank_eq_card_chooseBasisIndex, NumberField.RingOfIntegers.rank]
  simp

/-- The concrete shape of the mixed space of `ℚ`: its `ℤ`-lattice basis, read in coordinates,
gives `mixedEmbedding.mixedSpace ℚ ≃ (Fin 1 → ℝ)`. -/
noncomputable def mixedSpaceEquivFinOne : mixedEmbedding.mixedSpace ℚ ≃ₗ[ℝ] (Fin 1 → ℝ) :=
  (mixedEmbedding.latticeBasis ℚ).equivFun.trans
    (LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFinOfCardEq card_chooseBasisIndex_rat).symm)

/-- The shape equivalence is linear, so it fixes the origin: the point of `mixedSpace ℚ` that the
box `adelicBox ℚ` and its fundamental domain are read at below. -/
@[simp] theorem mixedSpaceEquivFinOne_zero : mixedSpaceEquivFinOne 0 = 0 := by
  simp [mixedSpaceEquivFinOne]

/-! ### `split_image_adelicBox` at `F = ℚ`: the origin lies in the box -/

/-- `split_image_adelicBox` at `F = ℚ`, read at the concrete datum `(0, 0)` of the split space:
the origin of `mixedSpace ℚ` lies in the fundamental domain and `0` lies in the integral finite
adèles, so the origin of `𝔸_ℚ` lies in the box. -/
theorem zero_mem_adelicBox_rat : (0 : AdeleRing (𝓞 ℚ) ℚ) ∈ adelicBox ℚ := by
  have h0 : ((0 : mixedEmbedding.mixedSpace ℚ), (0 : FiniteAdeleRing (𝓞 ℚ) ℚ))
      ∈ ⇑(split ℚ) '' adelicBox ℚ := by
    rw [split_image_adelicBox]
    refine ⟨?_, fun v => zero_mem _⟩
    rw [ZSpan.mem_fundamentalDomain]
    intro i
    simp
  obtain ⟨x, hx, hx0⟩ := h0
  have hx0' : ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ) x.1, x.2)
      = ((0 : mixedEmbedding.mixedSpace ℚ), (0 : FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
    simpa only [split_apply] using hx0
  have hx1 : x.1 = 0 := by
    have h : (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ) x.1 = 0 := by
      simpa using congrArg Prod.fst hx0'
    refine (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).injective ?_
    rw [map_zero]
    exact h
  have hx2 : x.2 = 0 := by
    have h : x.2 = (0 : FiniteAdeleRing (𝓞 ℚ) ℚ) := by
      simpa using congrArg Prod.snd hx0'
    exact h
  have hxzero : x = 0 := Prod.ext hx1 hx2
  rwa [hxzero] at hx

/-! ### `covolume_integerLattice_eq_toReal` at `F = ℚ` -/

/-- `covolume_integerLattice_eq_toReal` at `F = ℚ`, read at concrete data: the covolume of
`mixedEmbedding.integerLattice ℚ` is the volume of the fundamental domain of the explicit basis
`mixedEmbedding.latticeBasis ℚ`, and that volume is a positive real number. -/
theorem covolume_integerLattice_rat_pos :
    0 < ZLattice.covolume (mixedEmbedding.integerLattice ℚ) volume := by
  have hne0 : volume (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis ℚ)) ≠ 0 :=
    ZSpan.measure_fundamentalDomain_ne_zero (μ := volume) (mixedEmbedding.latticeBasis ℚ)
  have hneTop : volume (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis ℚ)) ≠ ∞ :=
    (ZSpan.fundamentalDomain_isBounded (mixedEmbedding.latticeBasis ℚ)).measure_lt_top.ne
  rw [covolume_integerLattice_eq_toReal ℚ]
  exact ENNReal.toReal_pos hne0 hneTop

/-! ### `fourierIntegral_comp_mul_left` at `F = ℚ`, `a = 1` -/

/-- `fourierIntegral_comp_mul_left` at `F = ℚ` and `a = 1`: the module `distribHaarChar 𝔸_ℚ 1`
of the trivial unit idèle is `1`, so the change of variable `v ↦ 1 * v` is the identity on the
transform. -/
theorem fourierIntegral_comp_one_rat
    [MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)] [BorelSpace (AdeleRing (𝓞 ℚ) ℚ)]
    (μ : Measure (AdeleRing (𝓞 ℚ) ℚ)) [μ.IsAddHaarMeasure]
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (f : AdeleRing (𝓞 ℚ) ℚ → ℂ)
    (w : AdeleRing (𝓞 ℚ) ℚ) :
    fourierIntegral ψ μ
        (fun v => f ((↑(1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ) * v)) w
      = fourierIntegral ψ μ f w := by
  rw [fourierIntegral_comp_mul_left (F := ℚ) μ ψ f 1 w]
  simp

end AdelicFourierSetAF75BConsumer
