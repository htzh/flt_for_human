/-
  Local fields: the adic completion and its integral subring.

  For a place `v` of a number field, the adic completion `K_v` is a non-archimedean
  local field: its integral subring `𝒪_v` is open, its residue field is finite
  (when `𝓞_K` is finite free over `ℤ`), and `K_v` is proper with `𝒪_v` compact.
  These are the local inputs to the adelic topology and to the compactness of
  `GL₂(𝔸_K)`'s level subgroups.

  Transcribed verbatim from `Definitions/Def_NumberField_AdelicHaar.lean:12–116`
  (the pin's `Local` section, pinned `aa2d8b3`), the first of the three role
  modules the pin's single `AdelicHaar` node is split into (playbook §3.1).
-/
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic
import Mathlib.Topology.Algebra.Valued.LocallyCompact

set_option autoImplicit false

-- The pin's `haveI` walls are load-bearing: the hypotheses below are consumed by instance
-- search in the `exact`s, so `have` (which the style linter prefers for a `Prop` goal) does not
-- work.
set_option linter.style.haveILetI false

open IsDedekindDomain NumberField MeasureTheory
open scoped RestrictedProduct NNReal

noncomputable section

namespace NumberField.AdelicHaar

section Local

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

instance fact_isOpen_adicCompletionIntegers :
    Fact (∀ v : HeightOneSpectrum R,
      IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
  ⟨fun _ => Valued.isOpen_valuationSubring _⟩

theorem exists_valued_algebraMap_sub_lt_one (x : v.adicCompletionIntegers K) :
    ∃ a : R, Valued.v ((algebraMap R (v.adicCompletion K) a) - (x : v.adicCompletion K)) < 1 := by
  have hn : {z : v.adicCompletion K | Valued.v (z - (x : v.adicCompletion K)) < 1} ∈
      nhds (x : v.adicCompletion K) := by
    refine Valued.mem_nhds.mpr ⟨1, fun z hz => ?_⟩
    have hz' : Valued.v.restrict (z - (x : v.adicCompletion K)) < 1 := by
      rw [← Units.val_one]; exact hz
    exact (Valuation.restrict_lt_one_iff _).mp hz'
  obtain ⟨_, hz, y, rfl⟩ := mem_closure_iff_nhds.mp
    (HeightOneSpectrum.denseRange_algebraMap (K := K) (v := v) (x : v.adicCompletion K)) _ hn
  have hy1 : Valued.v (algebraMap K (v.adicCompletion K) y - (x : v.adicCompletion K)) < 1 := hz
  have hyint : v.valuation K y ≤ 1 := by
    have hx1 : Valued.v (x : v.adicCompletion K) ≤ 1 := x.2
    have h : Valued.v (algebraMap K (v.adicCompletion K) y) ≤ 1 := by
      have := Valuation.map_add (Valued.v : Valuation (v.adicCompletion K) _)
        (algebraMap K (v.adicCompletion K) y - (x : v.adicCompletion K)) (x : v.adicCompletion K)
      rw [sub_add_cancel] at this
      exact this.trans (max_le hy1.le hx1)
    rwa [show algebraMap K (v.adicCompletion K) y = (y : v.adicCompletion K) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
  obtain ⟨a, ha⟩ := HeightOneSpectrum.exists_valuation_sub_lt_of_integer v hyint 1
  refine ⟨a, ?_⟩
  have ha' : Valued.v ((algebraMap R (v.adicCompletion K) a) -
      algebraMap K (v.adicCompletion K) y) < 1 := by
    rw [IsScalarTower.algebraMap_apply R K (v.adicCompletion K) a, ← map_sub,
      show algebraMap K (v.adicCompletion K) (algebraMap R K a - y) =
        ((algebraMap R K a - y : K) : v.adicCompletion K) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact ha.trans_eq Units.val_one
  have := Valuation.map_add (Valued.v : Valuation (v.adicCompletion K) _)
    ((algebraMap R (v.adicCompletion K) a) - algebraMap K (v.adicCompletion K) y)
    (algebraMap K (v.adicCompletion K) y - (x : v.adicCompletion K))
  rw [sub_add_sub_cancel] at this
  exact lt_of_le_of_lt this (max_lt ha' hy1)

theorem mem_maximalIdeal_iff_valued_lt_one (d : v.adicCompletionIntegers K) :
    d ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ↔
      Valued.v (d : v.adicCompletion K) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  have hd : Valued.v (d : v.adicCompletion K) ≤ 1 := d.2
  exact ⟨fun h => lt_of_le_of_ne hd h, fun h => ne_of_lt h⟩

theorem residue_algebraMap_surjective :
    Function.Surjective (fun a : R =>
      IsLocalRing.residue (v.adicCompletionIntegers K)
        (algebraMap R (v.adicCompletionIntegers K) a)) := by
  intro z
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
  obtain ⟨a, ha⟩ := exists_valued_algebraMap_sub_lt_one R K v x
  refine ⟨a, ?_⟩
  show Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
  rw [Ideal.Quotient.eq, mem_maximalIdeal_iff_valued_lt_one]
  simpa [HeightOneSpectrum.algebraMap_adicCompletion] using ha

theorem residue_algebraMap_eq_zero_of_mem {a : R} (ha : a ∈ v.asIdeal) :
    IsLocalRing.residue (v.adicCompletionIntegers K)
      (algebraMap R (v.adicCompletionIntegers K) a) = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_iff_valued_lt_one]
  simp only [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
  exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v a).mpr ha

variable [Module.Free ℤ R] [Module.Finite ℤ R]

/-- mathlib's `instNormedFieldValuedAdicCompletion` (v4.34) needs
`[Ring.HasFiniteQuotients R] [Infinite R]`, and neither is an `inferInstance` from the pin's
`[Module.Free ℤ R] [Module.Finite ℤ R]`. Both are nevertheless derivable there — a finite free
`ℤ`-module over a domain is infinite (`Module.Free.infinite`), and a finite module over a ring
with finite quotients has finite quotients (`Ring.HasFiniteQuotients.of_module_finite`). Supplying
them here lets the *pin's* statement of `properSpace_adicCompletion` below elaborate against
mathlib's own normed-field instance, instead of a port-local rank-one rescaling that would make
`ProperSpace (v.adicCompletion K)` a different class value at `R = 𝓞 F`. -/
local instance hasFiniteQuotients_of_module_finite : Ring.HasFiniteQuotients R :=
  Ring.HasFiniteQuotients.of_module_finite ℤ R

local instance infinite_of_module_free : Infinite R :=
  Module.Free.infinite ℤ R

instance finite_residueField_adicCompletionIntegers :
    Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) := by
  haveI : Finite (R ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  let f : R ⧸ v.asIdeal → IsLocalRing.ResidueField (v.adicCompletionIntegers K) :=
    Ideal.Quotient.lift v.asIdeal
      ((IsLocalRing.residue (v.adicCompletionIntegers K)).comp
        (algebraMap R (v.adicCompletionIntegers K)))
      (fun a ha => residue_algebraMap_eq_zero_of_mem R K v ha)
  refine Finite.of_surjective f fun z => ?_
  obtain ⟨a, ha⟩ := residue_algebraMap_surjective R K v z
  exact ⟨Ideal.Quotient.mk _ a, ha⟩

open scoped Valued in

instance properSpace_adicCompletion : ProperSpace (v.adicCompletion K) := by
  haveI : IsDiscreteValuationRing 𝒪[v.adicCompletion K] :=
    inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers K))
  haveI : Finite 𝓀[v.adicCompletion K] :=
    inferInstanceAs (Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)))
  exact Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.mpr
    ⟨inferInstance, inferInstance, inferInstance⟩

open scoped Valued in

instance compactSpace_adicCompletionIntegers : CompactSpace (v.adicCompletionIntegers K) := by
  have h : CompactSpace 𝒪[v.adicCompletion K] :=
    Valued.integer.properSpace_iff_compactSpace_integer.mp inferInstance
  exact h

end Local

end NumberField.AdelicHaar

end
