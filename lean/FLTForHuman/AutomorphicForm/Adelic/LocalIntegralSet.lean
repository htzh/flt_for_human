/-
  The local integral set at a finite place, as an invariant of the component.

  A unit-factorizable test function above `S` is a product of an archimedean factor, a finite
  factor and finitely many semi-local factors at the places of `S`; the finite factor is
  supported in the product of the local integral sets `localIntegralSet K v` for `v ∉ S`
  (`IsSemiLocalFactorization`). Hence at a place off `S` the finite component `glFin z` lies
  in that compact open subgroup whenever the test function does not vanish at `z`. That is
  the row: the local integral set at a finite place is an invariant of the component, and
  membership transfers along a non-vanishing value.

  The transposition used is the semi-local one: the finite component at `v` sits inside
  `semiLocalComponent K K v`, which for `K = K` is the base change to the completion, and
  `semiLocalIntegralSet` pulls back to `localIntegralSet` along its entries
  (`finComponent_mem_localIntegralSet_of_semiLocal`).

  spec-pin: P2M/Sol/S_AutomorphicForm_IsUnitFactorizableAbove_finComponent_glFin_mem_localIntegralSet_of_apply_ne_zero.lean

  ## Port deltas

  - Namespaces: the pin's workspace label `RS11UP` is dropped, so its seven engines sit
    directly in `AutomorphicForm`. The pin states them inside `namespace RS11UP` with
    `variable {K}`; the statements keep the pin's text verbatim (nothing in them is
    qualified through the label), so `check_port` hashes them to the pin's rows.
  - Public/private: the pin marks none of the eight declarations `private`, so all eight are
    transcribed public and `check_port` reads all eight `ok`.
  - `under_self` carries `omit [NumberField K] in`: the pin's proof of it uses only `𝓞 K` and the
    canonical map, so the section's `[NumberField K]` is an unused section variable
    (`linter.unusedSectionVars`), and the silence gate forbids the warning. The `omit` is outside
    the statement; `check_port` still hashes the statement to the pin's row.
  - Imports unchanged from the scaffold (`LocalOrbitalBase`, which holds
    `mem_localIntegralSet`/`mem_integralUnitsSet`, and `AdelicLevel/Projections`, which holds
    `finComponent_apply`, are both inside the `TwistedOrbital` closure).
  - No body deviation: the pin's proofs replay verbatim.

  ## Heartbeat probe (recorded, never installed — FR-0225)

  `lake env lean -DautoImplicit=false -DmaxHeartbeats=N
  FLTForHuman/AutomorphicForm/Adelic/LocalIntegralSet.lean` is **silent at N = 2 000** and
  **fails at N = 1 000** (`isDefEq` at the `rfl` of `semiLocalHomeomorph_apply`, `whnf` at the
  `rfl` of `semiLocalEval_apply`). The measured pair for the probe is 2 000 / 1 000. No
  `set_option maxHeartbeats` is in this module.
-/

import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.NumberTheory.NumberField.Basic
import FLTForHuman.AutomorphicForm.Adelic.TwistedOrbital
import FLTForHuman.NumberTheory.AdelicHaar.GeneralLinear

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel
open scoped TensorProduct

namespace AutomorphicForm

section Engines

variable {K : Type} [Field K] [NumberField K]

omit [NumberField K] in
/-- The place of `K` underlying itself is itself: the canonical extension of `v` to `K`. -/
theorem under_self (v : HeightOneSpectrum (𝓞 K)) : v.under (𝓞 K) = v := by
  apply HeightOneSpectrum.ext
  show Ideal.comap (algebraMap (𝓞 K) (𝓞 K)) v.asIdeal = v.asIdeal
  have h : algebraMap (𝓞 K) (𝓞 K) = RingHom.id (𝓞 K) := by
    ext x
    rfl
  rw [h, Ideal.comap_id]

/-- The canonical extension of a place of `K` to `K` itself. -/
def selfExt (v : HeightOneSpectrum (𝓞 K)) : v.Extension (𝓞 K) := ⟨v, under_self v⟩

theorem semiLocalHomeomorph_apply (v : HeightOneSpectrum (𝓞 K)) (y : K ⊗[K] v.adicCompletion K) :
    semiLocalHomeomorph K K v y = HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K K (𝓞 K) v y := rfl

theorem semiLocalEval_apply (v : HeightOneSpectrum (𝓞 K)) (x : FiniteAdeleRing (𝓞 K) K) :
    semiLocalEval K K v x = (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K K (𝓞 K) v).symm
      (fun w : v.Extension (𝓞 K) => x w.1) := rfl

/-- An entry of the semi-local component at the self-extension is the entry of `x` at `v`. -/
theorem mem_adicCompletionIntegers_of_semiLocalEval_mem (v : HeightOneSpectrum (𝓞 K)) (x : FiniteAdeleRing (𝓞 K) K)
    (hx : semiLocalEval K K v x ∈ semiLocalIntegers K K v) : x v ∈ v.adicCompletionIntegers K := by
  rw [semiLocalIntegers_eq_preimage] at hx
  rw [Set.mem_preimage, semiLocalHomeomorph_apply, semiLocalEval_apply, AlgEquiv.apply_symm_apply] at hx
  have h := hx (selfExt v) (Set.mem_univ _)
  exact h

theorem entry_semiLocalComponent (v : HeightOneSpectrum (𝓞 K)) (h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) (i j : Fin 2) :
    (semiLocalComponent K K v h : Matrix (Fin 2) (Fin 2) (K ⊗[K] v.adicCompletion K)) i j =
      semiLocalEval K K v ((h : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) := rfl

/-- The finite component at `v` of a semi-local integral element is locally integral at `v`. -/
theorem finComponent_mem_localIntegralSet_of_semiLocal (v : HeightOneSpectrum (𝓞 K))
    (h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) (hh : semiLocalComponent K K v h ∈ semiLocalIntegralSet K K v) :
    finComponent (𝓞 K) K v h ∈ localIntegralSet K v := by
  rw [mem_localIntegralSet]
  have hh' := (mem_integralUnitsSet.mp hh)
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [finComponent_apply]
    apply mem_adicCompletionIntegers_of_semiLocalEval_mem
    rw [← entry_semiLocalComponent]
    exact hh'.1 i j
  · rw [← map_inv, finComponent_apply]
    apply mem_adicCompletionIntegers_of_semiLocalEval_mem
    rw [← entry_semiLocalComponent, map_inv]
    exact hh'.2 i j

end Engines

theorem IsUnitFactorizableAbove.finComponent_glFin_mem_localIntegralSet_of_apply_ne_zero
    (K : Type) [Field K] [NumberField K]
    (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (hf : IsUnitFactorizableAbove K K U S f)
    (z : GL (Fin 2) (AdeleRing (𝓞 K) K)) (hz : f z ≠ 0)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
    finComponent (𝓞 K) K v (glFin (𝓞 K) K z) ∈ localIntegralSet K v := by
  obtain ⟨-, φa, φf, φS, -, -, -, -, hvanish, hfac⟩ := hf
  have hφf : φf (glFin (𝓞 K) K z) ≠ 0 := by
    intro h0
    apply hz
    rw [hfac z, h0, mul_zero]
  have hint : semiLocalComponent K K v (glFin (𝓞 K) K z) ∈ semiLocalIntegralSet K K v := by
    by_contra hnot
    exact hφf (hvanish _ ⟨v, hv, hnot⟩)
  exact finComponent_mem_localIntegralSet_of_semiLocal v _ hint

end AutomorphicForm

end
