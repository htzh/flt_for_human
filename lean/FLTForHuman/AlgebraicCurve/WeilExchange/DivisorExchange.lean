/-
The divisor-level Weil exchange identity — the capstone of the `AlgebraicCurve`
layer, and the declaration `ModularCurve.heckeOperatorsCommuteBar` calls (FLT
`P2M/Sol/S_ModularCurve_heckeOperatorsCommuteBar.lean:42`).

Statement: for the Hecke roof square
`F --a--> A`, `F --b--> B`, `A --a'--> E`, `B --b'--> E` with `b' ∘ b = a' ∘ a`,
finiteness and separability of `a' ∘ a`, generation `E = F(A, B)`, and the degree
identity `[E : F] = [A : F] [B : F]`,

  `pullback_b (pushforward_a D) = pushforward_b' (pullback_a' D)`

for every divisor `D` on `A`. The proof reduces, place by place, to the local
identity proved in `WeilExchange/LocalExchange.lean`, and the off-diagonal terms
vanish by the tower restriction `restrict_restrict`.

After FLT `P2M/Sol/S_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong.lean`
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong.lean>).
The pin's `BifibreWEX.restrict_restrict`, its third copy of the shared prelude
lemma, is not reproduced: the port imports `AlgebraicCurve.BifibreDev.restrict_restrict`
from `WeilExchange/Transport.lean`. This is the one topic reserved for the human
reviewer in `topics/algebraicCurve/TOPIC-t7-divisor-exchange.md`.
-/

import FLTForHuman.AlgebraicCurve.Defs.Correspondence
import FLTForHuman.AlgebraicCurve.WeilExchange.Transport
import FLTForHuman.AlgebraicCurve.WeilExchange.LocalExchange

set_option autoImplicit false
-- The pin's cone-algebra files, and SET 1's, disable this style lint rather than
-- rewriting the `letI`/`haveI` walls: the instances are load-bearing and the
-- wall is what keeps the port's proofs a transcription.
set_option linter.style.haveILetI false

noncomputable section

open AlgebraicCurve

namespace AlgebraicCurve

namespace Divisor

theorem pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong
    {K F A B E : Type*} [Field K] [Field F] [Field A] [Field B] [Field E]
    [Algebra K F] [Algebra K A] [Algebra K B] [Algebra K E]
    [HasPrincipalDivisors K B] [HasPrincipalDivisors K E]
    (a : F →ₐ[K] A) (b : F →ₐ[K] B) (a' : A →ₐ[K] E) (b' : B →ₐ[K] E)
    (ha : a.toRingHom.IsIntegral) (hb : b.toRingHom.IsIntegral)
    (ha' : a'.toRingHom.IsIntegral) (hb' : b'.toRingHom.IsIntegral)
    (hsq : b'.comp b = a'.comp a)
    (hfin : FiniteAlong K (a'.comp a)) (hsep : SeparableAlong K (a'.comp a))
    (hgen : Algebra.adjoin K (Set.range a' ∪ Set.range b') = ⊤)
    (hLD : finrankAlong K (a'.comp a) = finrankAlong K a * finrankAlong K b)
    (D : Divisor K A) :
    Divisor.pullbackAlong b hb (Divisor.pushforwardAlong a ha D) =
      Divisor.pushforwardAlong b' hb' (Divisor.pullbackAlong a' ha' D) := by
  classical

  letI : Algebra F A := algebraAlong a
  letI : Algebra F B := algebraAlong b
  letI : Algebra A E := algebraAlong a'
  letI : Algebra B E := algebraAlong b'
  letI : Algebra F E := algebraAlong (a'.comp a)
  haveI : IsScalarTower K F A := isScalarTower_along a
  haveI : IsScalarTower K F B := isScalarTower_along b
  haveI : IsScalarTower K A E := isScalarTower_along a'
  haveI : IsScalarTower K B E := isScalarTower_along b'
  haveI : IsScalarTower K F E := isScalarTower_along (a'.comp a)
  haveI : IsScalarTower F A E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower F B E :=
    IsScalarTower.of_algebraMap_eq fun x => (AlgHom.congr_fun hsq x).symm
  haveI : Algebra.IsIntegral F A := isIntegral_along a ha
  haveI : Algebra.IsIntegral F B := isIntegral_along b hb
  haveI : Algebra.IsIntegral A E := isIntegral_along a' ha'
  haveI : Algebra.IsIntegral B E := isIntegral_along b' hb'

  haveI : Module.Finite F E := hfin
  haveI : Algebra.IsIntegral F E := Algebra.IsIntegral.of_finite F E
  haveI : Algebra.IsSeparable F E := hsep
  haveI : FiniteDimensional A E := Module.Finite.of_restrictScalars_finite F A E
  haveI : FiniteDimensional B E := Module.Finite.of_restrictScalars_finite F B E
  haveI : FiniteDimensional F A := Module.Finite.left F A E
  haveI : FiniteDimensional F B := Module.Finite.left F B E

  have hgenF : Algebra.adjoin F (Set.range (algebraMap A E) ∪ Set.range (algebraMap B E)) = ⊤ := by
    have hs : Set.range (algebraMap A E) ∪ Set.range (algebraMap B E) =
        Set.range a' ∪ Set.range b' := rfl
    rw [hs, eq_top_iff]
    intro z _
    have hz : z ∈ Algebra.adjoin K (Set.range a' ∪ Set.range b') := hgen ▸ Algebra.mem_top
    have hle : Algebra.adjoin K (Set.range a' ∪ Set.range b') ≤
        (Algebra.adjoin F (Set.range a' ∪ Set.range b')).restrictScalars K :=
      Algebra.adjoin_le fun x hx =>
        (Subalgebra.mem_restrictScalars K).mpr (Algebra.subset_adjoin hx)
    exact (Subalgebra.mem_restrictScalars K).mp (hle hz)

  have eA : ∀ W : Place K E, Place.ramificationIndexAlong a' W = W.ramificationIndex A :=
    fun _ => rfl
  have fB : ∀ W : Place K E, W.inertiaDegAlong b' hb' = W.inertiaDeg B := fun _ => rfl
  have fF : ∀ w : Place K A, w.inertiaDegAlong a ha = w.inertiaDeg F := fun _ => rfl
  have eF : ∀ w : Place K B, Place.ramificationIndexAlong b w = w.ramificationIndex F :=
    fun _ => rfl

  suffices h : (Divisor.pullbackAlong b hb).comp (Divisor.pushforwardAlong a ha) =
      (Divisor.pushforwardAlong b' hb').comp (Divisor.pullbackAlong a' ha') from
    DFunLike.congr_fun h D
  refine Finsupp.addHom_ext fun wA n => ?_
  simp only [AddMonoidHom.coe_comp, Function.comp_apply]
  rw [Divisor.pushforwardAlong_single, Divisor.pullbackAlong_single, Divisor.pullbackAlong_single,
    map_sum]
  simp only [Divisor.pushforwardAlong_single]

  ext wB
  rw [Finset.sum_apply', Finset.sum_apply']
  simp only [Finsupp.single_apply, Finset.sum_ite_eq', eA, fB, fF, eF]
  by_cases hv : wB.restrictAlong b hb = wA.restrictAlong a ha
  ·
    rw [ite_eq_left (Place.mem_fiberAlong.mpr hv), ← Finset.sum_filter]
    have hT : ∀ W, W ∈ (Place.fiberAlong a' ha' wA).filter (fun W => W.restrictAlong b' hb' = wB)
        ↔ W.restrict A = wA ∧ W.restrict B = wB := fun W => by
      rw [Finset.mem_filter, Place.mem_fiberAlong]
      exact Iff.rfl
    have key := AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg_exchange
      (K := K) (F := F) (F₁ := A) (F₂ := B) (E := E) hgenF hLD (wA.restrictAlong a ha) wA wB
      rfl hv _ hT
    rw [Finset.sum_congr rfl fun W _ => mul_assoc n _ _, ← Finset.mul_sum, mul_assoc]
    congr 1
    exact_mod_cast key.symm
  ·
    rw [ite_eq_right (fun h => hv (Place.mem_fiberAlong.mp h))]
    symm
    refine Finset.sum_eq_zero fun W hW => ?_
    rw [ite_eq_right]
    intro hWB
    apply hv
    have h₁ : W.restrict A = wA := Place.mem_fiberAlong.mp hW
    have h₂ : W.restrict B = wB := hWB
    show wB.restrict F = wA.restrict F
    rw [← h₁, ← h₂, BifibreDev.restrict_restrict, BifibreDev.restrict_restrict]

end Divisor

end AlgebraicCurve
