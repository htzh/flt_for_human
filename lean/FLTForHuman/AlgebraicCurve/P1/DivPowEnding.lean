/-
DivPowEnding — the atom-3 headline of the ℙ¹ residue core.

Port of the gated headline
`RationalFunctionField.trace_localResidue_finitePlace_div_pow_eq_zero` from
`P2M/Sol/S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.lean`
(pin `anthropics/fermats-last-theorem@aa2d8b3`, the `P1Tower` theorem at lines
2016–2138 and the wrapper `solution` at 2140–2150), the last missing piece of
the atom-3 sibling tail. `P1/DivPow.lean` carries the whole `P1Tower` block
short of this headline; the proof additionally consumes the surviving
`AlgebraicCurve.residueTraceCompletionCommute`
(`Tate/TraceCompletionCommute.lean`) and
`AlgebraicCurve.completionTraceSum_of_isSeparable`
(`Tate/CompletionTraceSum.lean`) landed by set 3.4. The pin's `_v2` twin of the
first is dropped (PORTING-RR §3 name policy).

`kwHgfV352_localResidueCompletion_algebraMap` is the public fact stated in
`P1/DivPow.lean` about the public `kwHgfV352_localResidueCompletion` of
`Defs/TateResidueCurrency.lean`; the P3.2f/3.3 `private` `…_spec₀`/`…_algebraMap₀`
re-landings were deleted in the P3.2 refactor round (R5).
-/
import FLTForHuman.AlgebraicCurve.P1.DivPow
import FLTForHuman.AlgebraicCurve.Tate.TraceCompletionCommute
import FLTForHuman.AlgebraicCurve.Tate.CompletionTraceSum

noncomputable section
open Polynomial IsDedekindDomain WithZero IsLocalRing UniqueFactorizationMonoid
open Module
open KaehlerDifferential
open scoped IntermediateField
open AlgebraicCurve

namespace AlgebraicCurve

open RationalFunctionField

set_option autoImplicit false
set_option synthInstance.maxSize 4096


section SurjectiveResidueField

/-- Re-landed `private` from the pin `S_` file's own copy (line 1325), which is
stated without the `[CharZero K]` of the port's public
`P1/KaehlerIntegral.lean:474` (that section variable is the `AlgClosedDischarge`
specialisation). Only `v.deg = 1` is used. -/
private theorem surjective_algebraMap_residueField_of_deg_eq_one'
    (K F : Type*) [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hdeg : v.deg = 1) :
    Function.Surjective (algebraMap K v.ResidueField) := by
  intro z
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : v.ResidueField) one_ne_zero).mp
    (show Module.finrank K v.ResidueField = 1 from hdeg) z
  exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc⟩

end SurjectiveResidueField

section DivPowHeadline

variable (K : Type*) [Field K] [PerfectField K] [DecidableEq (RatFunc K)]
variable [IsCurveOver K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable (p : K[X]) (hp : 0 < p.natDegree)

namespace P1Tower

-- `gen` is imported from `P1/DivPow.lean`, where it is public since R6 of the
-- P3.2 refactor round; the headline keeps the pin's explicit `hp` via `include hp`.

include hp in

/-- The atom-3 finite-place vanishing headline, inside the `Kx`-tower: for
`2 ≤ m` and `c.degree < p.degree` the trace of the finite-place residue of
`(c / p ^ m) · dX` is zero. -/
theorem trace_localResidue_finitePlace_div_pow_eq_zero
    (hmon : p.Monic) (hirr : Irreducible p) {c : K[X]} (hc : c.degree < p.degree) {m : ℕ} (hm : 2 ≤ m) :
    Algebra.trace K (finitePlace K hirr).ResidueField
        ((finitePlace K hirr).localResidue
          (algebraMap K[X] (RatFunc K) c / algebraMap K[X] (RatFunc K) p ^ m
            * (finitePlace K hirr).differentialCoeff
                (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)))) = 0 := by
  classical
  have hsep : p.Separable := PerfectField.separable_of_irreducible hirr
  haveI := finiteDimensional_Kx K p hp hmon
  haveI := isIntegral_Kx K p hp hmon
  haveI := isSeparable_Kx K p hp hmon hsep
  haveI hPD : HasPrincipalDivisors K (RatFunc K) := instHasPrincipalDivisors

  set v0 : Place K (RatFunc K) := placeOfPoint K 0 with hv0
  let w : Place K (Kx K p hp) := (finitePlace K hirr : Place K (RatFunc K))
  have hw : w ∈ v0.fiber (Kx K p hp) := finitePlace_mem_fiber K p hp hirr
  have hfib : v0.fiber (Kx K p hp) = {w} := fiber_placeOfPoint_zero K p hp hirr

  set E := RatFunc K
  set t : RatFunc K := RatFunc.X with ht
  set ε : RatFunc K := v0.differentialCoeff (KaehlerDifferential.D K (RatFunc K) t) with hε
  have hε0 : ε ≠ 0 := v0.differentialCoeff_ne_zero (D_ratFuncX_ne_zero K)
  set P' : Kx K p hp := toKx K p hp (algebraMap K[X] (RatFunc K) (derivative p)) with hP'
  have hP'0 : P' ≠ 0 := by
    rw [hP']
    refine (_root_.map_ne_zero (toKx K p hp)).mpr ((map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr ?_)
    intro hd
    have : IsCoprime p (derivative p) := hsep
    rw [hd] at this
    exact not_isUnit_p K p hp (isCoprime_zero_right.mp this)
  set cX : Kx K p hp := toKx K p hp (algebraMap K[X] (RatFunc K) c) with hcX
  set f : Kx K p hp := toKx K p hp (algebraMap K[X] (RatFunc K) c / algebraMap K[X] (RatFunc K) p ^ m) with hf
  set g : Kx K p hp := f * algebraMap E (Kx K p hp) ε * P'⁻¹ with hg

  set ω : Ω[(Kx K p hp)⁄K] := kaehlerPullback K (Kx K p hp) E v0.dCoord with hω
  have hcotr : algebraMap E (Kx K p hp) ε • ω
      = P' • KaehlerDifferential.D K (Kx K p hp) (gen K p hp) := by
    have h1 : KaehlerDifferential.D K E t = ε • v0.dCoord := (v0.differentialCoeff_smul_dCoord _).symm
    have h2 : kaehlerPullback K (Kx K p hp) E (KaehlerDifferential.D K E t)
        = algebraMap E (Kx K p hp) ε • ω := by
      rw [h1, hω, kaehlerPullback, kaehlerPullback, LinearMap.map_smul, algebraMap_smul]
    have h3 : kaehlerPullback K (Kx K p hp) E (KaehlerDifferential.D K E t)
        = KaehlerDifferential.D K (Kx K p hp) (algebraMap E (Kx K p hp) t) := by
      rw [kaehlerPullback, KaehlerDifferential.map_D]
    have h4 : algebraMap E (Kx K p hp) t = aeval (gen K p hp) p := by
      rw [algebraMap_Kx_apply, ht, subst_X]
      exact (aeval_ratFuncX K p).symm
    rw [← h2, h3, h4, Derivation.map_aeval, hP', ← aeval_ratFuncX K (derivative p)]
    rfl

  have hcoeffω : w.differentialCoeff ω
      = (algebraMap E (Kx K p hp) ε)⁻¹ * P' * w.differentialCoeff (KaehlerDifferential.D K (Kx K p hp) (gen K p hp)) := by
    have hεK : algebraMap E (Kx K p hp) ε ≠ 0 := (_root_.map_ne_zero _).mpr hε0
    have : ω = ((algebraMap E (Kx K p hp) ε)⁻¹ * P') • KaehlerDifferential.D K (Kx K p hp) (gen K p hp) := by
      rw [mul_smul, ← hcotr, smul_smul, inv_mul_cancel₀ hεK, one_smul]
    rw [this, w.differentialCoeff_smul]
  have hgω : g * w.differentialCoeff ω = f * w.differentialCoeff (KaehlerDifferential.D K (Kx K p hp) (gen K p hp)) := by
    have hεK : algebraMap E (Kx K p hp) ε ≠ 0 := (_root_.map_ne_zero _).mpr hε0
    rw [hcoeffω, hg]; field_simp

  have hRTCC := residueTraceCompletionCommute (K := K) (F := Kx K p hp) (E := E) v0 w hw g
  have hCTS := completionTraceSum_of_isSeparable (K := K) (F := Kx K p hp) (E := E) v0 g
  have hsum : (∑ w' ∈ (v0.fiber (Kx K p hp)).attach,
        kwHgfV352_completionTraceAt v0 w'.1 w'.2 g)
      = kwHgfV352_completionTraceAt v0 w hw g := by
    have hone : ∀ w' : { x // x ∈ v0.fiber (Kx K p hp) }, (w' : Place K (Kx K p hp)) = w := fun w' => by
      have h : (w'.1 : Place K (Kx K p hp)) ∈ ({w} : Finset (Place K (Kx K p hp))) := hfib ▸ w'.2
      exact Finset.mem_singleton.mp h
    rw [Finset.sum_eq_single_of_mem (⟨w, hw⟩ : { x // x ∈ v0.fiber (Kx K p hp) }) (Finset.mem_attach _ _)
      (fun w' _ hne => (hne (Subtype.ext (hone w'))).elim)]
  rw [hsum] at hCTS
  rw [← hCTS, kwHgfV352_localResidueCompletion_algebraMap] at hRTCC

  have hLHS : kaehlerResidueTerm ω (diagonalHom K (Kx K p hp) g) w
      = Algebra.trace K (finitePlace K hirr).ResidueField
          ((finitePlace K hirr).localResidue
            (algebraMap K[X] (RatFunc K) c / algebraMap K[X] (RatFunc K) p ^ m
              * (finitePlace K hirr).differentialCoeff
                  (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)))) := by
    rw [kaehlerResidueTerm, diagonalHom_apply, hgω]
    rfl
  rw [← hLHS, hRTCC]

  have hc' : c.natDegree < p.natDegree := by
    rcases eq_or_ne c 0 with rfl | hc0
    · simpa using hp
    exact Polynomial.natDegree_lt_natDegree hc0 hc
  have htr : Algebra.trace E (Kx K p hp) g
      = ε * (t ^ m)⁻¹ * algebraMap K E (c.coeff (p.natDegree - 1)) := by
    have hf' : f = algebraMap E (Kx K p hp) ((t ^ m)⁻¹) * cX := by
      rw [algebraMap_Kx_apply, map_inv₀, map_pow, ht, subst_X, hf, hcX, ← map_mul (toKx K p hp)]
      congr 1
      rw [div_eq_mul_inv, mul_comm]
    have hg' : g = ((t ^ m)⁻¹ * ε) • (cX * P'⁻¹) := by
      rw [hg, hf', Algebra.smul_def, map_mul]; ring
    rw [hg', LinearMap.map_smul, smul_eq_mul, hcX, hP', trace_mul_inv_derivative K p hp hmon hsep hc']
    ring
  rw [htr]

  have hsurj : Function.Surjective (algebraMap K v0.ResidueField) :=
    surjective_algebraMap_residueField_of_deg_eq_one' K (RatFunc K) v0 (by rw [hv0, deg_placeOfPoint])
  have htord : v0.ord t = 1 := by
    rw [hv0, ht, ← RatFunc.algebraMap_X, ord_placeOfPoint_algebraMap 0 Polynomial.X_ne_zero]
    have h := (Polynomial.rootMultiplicity_X_sub_C : Polynomial.rootMultiplicity (0 : K) (X - C 0) = _)
    rw [map_zero, sub_zero, if_pos rfl] at h
    exact_mod_cast h
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hC1 := AlgebraicCurve.Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap
    v0 hsurj (fun h hh => ag9b13e_differentialCoeff_D_mem_of_mem_of_perfectField v0 hh)
    (HasCanonicalLocalResidueKStar.dataKStar v0) htord (n := n) (by omega)
  have hres : v0.localResidue (ε * (t ^ (n + 1))⁻¹ * algebraMap K E (c.coeff (p.natDegree - 1))) = 0 := by
    rw [mul_comm, ← Algebra.smul_def, LinearMap.map_smul]
    show _ • (HasCanonicalLocalResidueKStar.dataKStar v0).res _ = 0
    rw [hε, hC1, smul_zero]
  rw [hres, _root_.map_zero]

end P1Tower

namespace RationalFunctionField

/-- The atom-3 headline at the pin wrapper's binders: the trace of the
finite-place residue of `c / p ^ m · dX` vanishes for `2 ≤ m`. -/
theorem trace_localResidue_finitePlace_div_pow_eq_zero
    (K : Type*) [Field K] [PerfectField K] [DecidableEq (RatFunc K)]
    [AlgebraicCurve.IsCurveOver K (RatFunc K)]
    [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
    {p c : K[X]} (hmon : p.Monic) (hp : Irreducible p) (hc : c.degree < p.degree) {m : ℕ} (hm : 2 ≤ m) :
    Algebra.trace K (AlgebraicCurve.RationalFunctionField.finitePlace K hp).ResidueField
        ((AlgebraicCurve.RationalFunctionField.finitePlace K hp).localResidue
          (algebraMap K[X] (RatFunc K) c / algebraMap K[X] (RatFunc K) p ^ m
            * (AlgebraicCurve.RationalFunctionField.finitePlace K hp).differentialCoeff
                (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)))) = 0 :=
  AlgebraicCurve.P1Tower.trace_localResidue_finitePlace_div_pow_eq_zero K p hp.natDegree_pos hmon hp hc hm

end RationalFunctionField

end DivPowHeadline

end AlgebraicCurve
