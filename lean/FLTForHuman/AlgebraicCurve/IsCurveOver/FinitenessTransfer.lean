/-
  The finiteness transfer for a generator: if one generator `x` makes `F` finite over
  `K(x)`, so does any transcendental `t` — `K ⊆ K(t)` is algebraic when `t` is
  transcendental, hence so is `K(x) ⊆ K(t)`, and `[F : K(t)]` is finite by the tower
  law. This is the third `localParam` premise leaf (`AlgebraicCurve`, the
  `IsCurveOver` side): it lets a `localParam` be built from any transcendental
  generator, not just a fixed one.

  Statements are transcribed verbatim from the pinned FLT proof
  (`anthropics/fermats-last-theorem`, `aa2d8b3`); only proof bodies are adapted to
  mathlib `v4.34.0`. Three public declarations
  (`isAlgebraic_adjoin_of_transcendental'`,
  `finiteDimensional_adjoin_of_transcendental'` and the headline), as in the pin.
  The pin's `Theorems/` wrapper states the hypothesis `[FiniteDimensional …]` as an
  instance, unlike the *different* statement of the same last name in
  `ModularCurve.X1.FunctionFieldResidue`, which takes it as an argument; the
  `ModularCurve` copy is deliberately not imported here (layering).

  Role: tier 1, and a premise of the third `localParam` leaf
  (`exists_localParam_meromorphicOrderAt_evalAt_eq_ord_complex`, WORKORDER-LP4).

  spec-pin: Theorems/Thm_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental.lean
  spec-pin: P2M/Sol/S_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental.lean
-/
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

set_option autoImplicit false

open Set Cardinal

-- The pin's instance walls are kept literal: `haveI` is load-bearing here.
set_option linter.style.haveILetI false

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem isAlgebraic_adjoin_of_transcendental' (x : F)
    [halg : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]
    {t : F} (ht : Transcendental K t) :
    Algebra.IsAlgebraic (IntermediateField.adjoin K ({t} : Set F)) F := by

  have hx : Transcendental K x := by
    intro hxalg
    haveI : Algebra.IsAlgebraic K (IntermediateField.adjoin K ({x} : Set F)) :=
      IntermediateField.isAlgebraic_adjoin_simple hxalg.isIntegral
    haveI : Algebra.IsAlgebraic K F :=
      Algebra.IsAlgebraic.trans K (IntermediateField.adjoin K ({x} : Set F)) F
    exact ht (Algebra.IsAlgebraic.isAlgebraic t)

  have hbx : IsTranscendenceBasis K ![x] := by
    rw [isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic]
    refine ⟨algebraicIndependent_iff_transcendental.mpr hx, ?_⟩
    have : Set.range ![x] = {x} := by simp
    rw [this]
    exact (IntermediateField.isAlgebraic_adjoin_iff_top (F := K) (s := ({x} : Set F))).mp halg

  have hind : AlgebraicIndepOn K id ({t} : Set F) := by
    rw [AlgebraicIndepOn, algebraicIndependent_unique_type_iff]
    simpa using ht
  obtain ⟨S, htS, hS⟩ := exists_isTranscendenceBasis_superset hind

  have hcard := hS.lift_cardinalMk_eq hbx
  simp only [Cardinal.mk_fin, Nat.cast_one, Cardinal.lift_one, Cardinal.lift_eq_one] at hcard
  have hS_eq : S = {t} :=
    (Cardinal.mk_le_one_iff_set_subsingleton.mp hcard.le).eq_singleton_of_mem (htS rfl)
  subst hS_eq
  have h := hS.isAlgebraic_field
  rwa [Subtype.range_coe] at h

theorem finiteDimensional_adjoin_of_transcendental' (x : F)
    [hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    {t : F} (ht : Transcendental K t) :
    FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F := by
  haveI halg : Algebra.IsAlgebraic (IntermediateField.adjoin K ({t} : Set F)) F :=
    isAlgebraic_adjoin_of_transcendental' x ht
  set E := IntermediateField.adjoin K ({t} : Set F)
  set Kx := IntermediateField.adjoin K ({x} : Set F)

  let b := Module.finBasis Kx F
  let S : Set F := insert x (Set.range b)
  haveI : Finite S := Set.Finite.insert x (Set.finite_range b) |>.to_subtype

  haveI hM : FiniteDimensional E (IntermediateField.adjoin E S) :=
    IntermediateField.finiteDimensional_adjoin fun y _ => (halg.isAlgebraic y).isIntegral

  have htop : IntermediateField.adjoin E S = ⊤ := by
    rw [eq_top_iff]
    intro y _

    have hKx : ∀ c : Kx, (c : F) ∈ IntermediateField.adjoin E S := by
      intro c
      have hle : Kx ≤ (IntermediateField.adjoin E S).restrictScalars K := by
        rw [IntermediateField.adjoin_le_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact IntermediateField.subset_adjoin E S (Set.mem_insert _ _)
      exact hle c.2

    rw [← b.sum_repr y]
    refine Subfield.sum_mem _ fun i _ => ?_
    rw [IntermediateField.smul_def]
    exact mul_mem (hKx _) (IntermediateField.subset_adjoin E S (Set.mem_insert_of_mem _ ⟨i, rfl⟩))
  rw [htop] at hM
  exact (IntermediateField.topEquiv (F := E) (E := F)).toLinearEquiv.finiteDimensional

end AlgebraicCurve

namespace AlgebraicCurve

-- pin: AlgebraicCurve.finiteDimensional_adjoin_of_transcendental (Theorems/Thm_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental.lean:7)
theorem finiteDimensional_adjoin_of_transcendental {K F : Type*} [Field K] [Field F] [Algebra K F] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] {t : F} (ht : Transcendental K t) :
    FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F :=
  finiteDimensional_adjoin_of_transcendental' x ht

end AlgebraicCurve
