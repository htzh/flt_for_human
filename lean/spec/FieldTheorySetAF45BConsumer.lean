/-
  SET-AF45B consumer: the valuation subring as a PID, and the residue separation.

  **The zone.** Two independent rows, hence two compositions.

  Row B2 (`isPrincipalIdealRing_of_finiteDimensional_adjoin`) is applied at the concrete
  transcendental element of the rational function field. The order asks for `K[X] → Frac K[X]`;
  the port's mathlib spells `Frac K[X]` as `RatFunc K` and the image of `X` as `RatFunc.X`, and
  `RatFunc.adjoin_X` supplies the only hypothesis that is not a field-theoretic triviality — that
  `K⟮X⟯` is generated over `K` by `X` alone, so the intermediate field of the headline is `⊤` and
  the extension is finite-dimensional (of rank one). The conclusion is read twice: as the
  `IsPrincipalIdealRing O` instance itself, and as the explicit generator of an arbitrary ideal
  `I : Ideal O` through `Submodule.IsPrincipal.generator` and `Ideal.span_singleton_generator`.

  Row B1 (`exists_sub_mem_nonunits_of_finrank_le_card`) is applied at `ι = Fin 1` with the
  constant family `O' = fun _ => O` over the identity algebra `F → F`. The cardinality hypothesis
  `finrank F F ≤ card (Fin 1)` is `1 ≤ 1`, injectivity is subsingleton-ness of `Fin 1`, and the
  comap hypothesis is `O.comap (algebraMap F F) = O`. The separation `x - algebraMap F F y ∈ (O).nonunits`
  is then unfolded through `ValuationSubring.mem_nonunits_iff` to the valuation inequality
  `O.valuation (x - y) < 1`.

  This module is outside every library: it is a spec-side composition check, not part of the
  port's import graph.
-/
import FLTForHuman.FieldTheory.ValuationSubringFinrank
import Mathlib.FieldTheory.RatFunc.IntermediateField

set_option autoImplicit false

noncomputable section

open Polynomial

namespace ValuationSubring

/-- **Zone F.** Row B2 read at `x = RatFunc.X`, the transcendental generator of `Frac K[X]` over
`K`: the intermediate field `K⟮X⟯` is the top field, so the headline's finite-dimensionality
hypothesis is discharged by `RatFunc.adjoin_X`, and the conclusion yields both the
`IsPrincipalIdealRing` instance and a principal generator for every ideal. -/
theorem consumer_zoneF_pid_ratfunc {K : Type*} [Field K] (O : ValuationSubring (RatFunc K))
    (hK : ∀ a : K, algebraMap K (RatFunc K) a ∈ O) (hO : O ≠ ⊤) :
    IsPrincipalIdealRing O ∧ ∀ I : Ideal O, ∃ g, I = Ideal.span {g} := by
  have hfin : FiniteDimensional
      (IntermediateField.adjoin K ({RatFunc.X} : Set (RatFunc K))) (RatFunc K) := by
    rw [RatFunc.adjoin_X]
    exact FiniteDimensional.of_finrank_pos (by rw [IntermediateField.finrank_top]; norm_num)
  have hpid := isPrincipalIdealRing_of_finiteDimensional_adjoin (K := K) (F := RatFunc K)
    RatFunc.X O hK hO
  exact ⟨hpid, fun I => ⟨Submodule.IsPrincipal.generator I, (Ideal.span_singleton_generator I).symm⟩⟩

/-- **Zone G.** Row B1 read at `ι = Fin 1` with the constant family `O' = fun _ => O` over
`F → F`: there is `y ∈ O` with `x - y` non-integral, i.e. `O.valuation (x - y) < 1`. -/
theorem consumer_zoneG_separation_fin_one {F : Type*} [Field F] (O : ValuationSubring F)
    (x : F) (hx : x ∈ O) : ∃ y ∈ O, O.valuation (x - y) < 1 := by
  have hinj : Function.Injective (fun _ : Fin 1 => O) := fun i j _ => Subsingleton.elim i j
  have hcomap : ∀ _ : Fin 1, O.comap (algebraMap F F) = O := by
    intro _
    ext z
    simp
  have hcard : Module.finrank F F ≤ Fintype.card (Fin 1) := by simp
  obtain ⟨y, hy, hsep⟩ :=
    exists_sub_mem_nonunits_of_finrank_le_card (F' := F) O (fun _ : Fin 1 => O) hinj hcomap
      hcard 0 x hx
  refine ⟨y, hy, ?_⟩
  have := (mem_nonunits_iff O).mp hsep
  simpa using this

end ValuationSubring
