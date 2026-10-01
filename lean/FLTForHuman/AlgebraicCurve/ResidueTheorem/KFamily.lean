/-
Row 6 (the K ending), assembly half — the general-curve producer of
`ResidueTheoremK` and its public headline.

Source, pinned to `anthropics/fermats-last-theorem@aa2d8b3`:
`P2M/Sol/S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean`
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean>).

The engine (the named `Prop` rows, `regularPoleSubmodule`, the Kähler-cotrace
bridge and the separator/polar-approximation block) is `KCotrace.lean`; this module
adds the residue-theorem chain that consumes it and the two `ResidueTheoremK`
producers, ending at the pin's `solution` body.  The `RatFunc` headline itself is
`KRatFunc.lean`.

The three pin-`private` `Prop` rows `KwF4R1V384aCompletionSemilocalBij`,
`KwF4R1V384aDistinctKernels` and `KwF4R1V384aFinrankCompletionEF` live `private`
in `Tate/CompletionTraceSum.lean`; the proofs here reach only the port's public
`completionTraceSum_of_isSeparable`, so they are not re-landed (recorded promotion
debt, pin `S_` 269/282/288).
-/
import FLTForHuman.AlgebraicCurve.ResidueTheorem.KCotrace
import FLTForHuman.AlgebraicCurve.ResidueTheorem.KRatFunc
import FLTForHuman.AlgebraicCurve.Tate.CompletionTraceSum
import FLTForHuman.AlgebraicCurve.Tate.TraceCompletionCommute

set_option autoImplicit false
set_option linter.unusedSectionVars false

open KaehlerDifferential LinearMap Submodule
open WithZero IsDedekindDomain IsLocalRing
open ModularCurve.KwF4R1V391a

noncomputable section

namespace AlgebraicCurve

namespace Place

section SumRamificationInertia

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

variable (v : Place K F)

/-- (pin 1178) The sum of ramification index times inertia degree over the fiber is
the degree of the extension. -/
theorem sum_ramificationIndex_mul_inertiaDeg [HasPrincipalDivisors K F'] :
    ∑ w ∈ v.fiber F', (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ)
      = (Module.finrank F F' : ℤ) := by
  classical
  have hkey := Ideal.sum_ramification_inertia (integralClosureAt F' v) F F'
    (p := IsLocalRing.maximalIdeal v.toValuationSubring) (maximalIdeal_ne_bot v)
  rw [← hkey]
  push_cast
  refine Finset.sum_bij
    (fun w hw => (fiberCenter F' v (Place.mem_fiber.mp hw)).asIdeal) ?_ ?_ ?_ ?_
  ·
    intro w hw
    rw [IsDedekindDomain.mem_primesOverFinset_iff (maximalIdeal_ne_bot v)]
    exact ⟨(fiberCenter F' v (Place.mem_fiber.mp hw)).isPrime,
      fiberCenter_liesOver (Place.mem_fiber.mp hw)⟩
  ·
    intro w hw w' hw' h
    exact eq_of_fiberCenter_eq (Place.mem_fiber.mp hw) (Place.mem_fiber.mp hw')
      (HeightOneSpectrum.ext h)
  ·
    intro P hP
    rw [IsDedekindDomain.mem_primesOverFinset_iff (maximalIdeal_ne_bot v)] at hP
    obtain ⟨hP1, hP2⟩ := hP
    have hPne : P ≠ ⊥ := by
      intro h
      apply maximalIdeal_ne_bot v
      have h2 := hP2.over
      rw [h, Ideal.under_def, Ideal.comap_bot_of_injective _
        (algebraMap_integralClosureAt_injective v)] at h2
      exact h2
    refine ⟨placeOfPrime ⟨P, hP1, hPne⟩,
      Place.mem_fiber.mpr (restrict_placeOfPrime ⟨P, hP1, hPne⟩), ?_⟩
    exact congrArg HeightOneSpectrum.asIdeal
      (fiberCenter_placeOfPrime (⟨P, hP1, hPne⟩ :
        HeightOneSpectrum (integralClosureAt F' v)))
  ·
    intro w hw
    rw [ramificationIndex_eq_ramificationIdx_fiberCenter (Place.mem_fiber.mp hw),
      inertiaDeg_eq_inertiaDeg_fiberCenter (Place.mem_fiber.mp hw)]

end SumRamificationInertia

section SubsingletonCriterion

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

variable (v : Place K F)

/-- (pin 2640) A surjective residue-field map makes the canonical local residue
datum subsingleton. -/
theorem subsingleton_canonicalLocalResidueDataK_of_surj
    (hsurj : Function.Surjective (algebraMap K v.ResidueField)) :
    Subsingleton v.CanonicalLocalResidueDataK := by
  constructor
  intro R₁ R₂
  have hres : R₁.res = R₂.res := by
    ext f
    obtain ⟨n, hn⟩ := v.exists_mem_poleSubmodule f
    exact v.canonicalLocalResidueDataK_agree_on_poleSubmodule_of_surj hsurj R₁ R₂ n hn
  obtain ⟨⟨r₁, h₁a, h₁b⟩, h₁c⟩ := R₁
  obtain ⟨⟨r₂, h₂a, h₂b⟩, h₂c⟩ := R₂
  congr 2

end SubsingletonCriterion

end Place

section FiberReindex

variable {K E F : Type*} [Field K] [Field E] [Field F]
variable [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F] [HasPrincipalDivisors K F]

variable {M : Type*} [AddCommMonoid M]

/-- (pin 2693) A finitely-supported sum over the places of `F` is the sum over the
places of `E` of the fiber sums. -/
theorem finsum_place_eq_finsum_fiber_sum (g : Place K F → M)
    (hg : (Function.support g).Finite) :
    ∑ᶠ w, g w = ∑ᶠ v : Place K E, ∑ w ∈ v.fiber F, g w := by
  classical
  set S := hg.toFinset with hS
  set T := S.image (fun w => w.restrict E) with hT

  rw [finsum_eq_finsetSum_of_support_subset g
    (s := S) (fun w hw => (hS ▸ hg.mem_toFinset.mpr hw))]

  have hsup : Function.support (fun v : Place K E => ∑ w ∈ v.fiber F, g w) ⊆ ↑T := by
    intro v hv
    simp only [Function.mem_support] at hv
    obtain ⟨w, hwfib, hwne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
    exact Finset.mem_coe.mpr (hT ▸ Finset.mem_image.mpr
      ⟨w, hS ▸ hg.mem_toFinset.mpr hwne, Place.mem_fiber.mp hwfib⟩)
  rw [finsum_eq_finsetSum_of_support_subset _ hsup]

  have hfib : ∀ v ∈ T, ∑ w ∈ v.fiber F, g w
      = ∑ w ∈ S with w.restrict E = v, g w := by
    intro v _
    refine (Finset.sum_subset ?_ ?_).symm
    · intro w hw
      exact Place.mem_fiber.mpr (Finset.mem_filter.mp hw).2
    · intro w hwfib hwfilt

      by_contra hgw
      exact hwfilt (Finset.mem_filter.mpr
        ⟨hS ▸ hg.mem_toFinset.mpr hgw, Place.mem_fiber.mp hwfib⟩)
  rw [Finset.sum_congr rfl hfib]

  exact (Finset.sum_fiberwise_of_maps_to
    (fun w hw => hT ▸ Finset.mem_image.mpr ⟨w, hw, rfl⟩) g).symm

end FiberReindex

section CotraceResidueIdentityK

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ w : Place K F, w.DCoordGenerates]
variable {E : Type*} [Field E] [Algebra K E]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalDivisor (K := K) (F := E)]
variable [∀ v : Place K E, v.DCoordGenerates]
variable [Algebra E F] [IsScalarTower K E F] [Algebra.IsIntegral E F]

/-- (pin 5578) The fiber-localized cotrace identity transports `ResidueTheoremK`
from `E` to `F`. -/
theorem residueTheoremK_of_cotraceResidueIdentityK
    [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
    (hE : ResidueTheoremK K E)
    {ωE₀ : Ω[E⁄K]} (hωE₀ : ωE₀ ≠ 0) (hgen : kaehlerPullback K F E ωE₀ ≠ 0)
    (hIdentK : FiberKaehlerCotraceResidueIdentityK K F E) :
    ResidueTheoremK K F := by
  intro RfamF _ ωF hωF f
  haveI : Nontrivial Ω[F⁄K] := ⟨ωF, 0, hωF⟩
  rcases isEmpty_or_nonempty (Place K F) with hempty | hne
  ·
    rw [weilOfKaehlerK_apply]
    exact finsum_eq_zero_of_forall_eq_zero fun w => (hempty.false w).elim
  obtain ⟨w₀⟩ := hne

  obtain ⟨RfamE, hident⟩ := hIdentK RfamF hωE₀ hgen

  have hcoeff : w₀.differentialCoeff (kaehlerPullback K F E ωE₀) ≠ 0 :=
    w₀.differentialCoeff_ne_zero hgen
  have hωF_eq : ωF = (w₀.differentialCoeff ωF
      * (w₀.differentialCoeff (kaehlerPullback K F E ωE₀))⁻¹)
        • kaehlerPullback K F E ωE₀ := by
    have key : (w₀.differentialCoeff ωF
        * (w₀.differentialCoeff (kaehlerPullback K F E ωE₀))⁻¹)
          • kaehlerPullback K F E ωE₀ = ωF := by
      calc (w₀.differentialCoeff ωF
            * (w₀.differentialCoeff (kaehlerPullback K F E ωE₀))⁻¹)
              • kaehlerPullback K F E ωE₀
          = (w₀.differentialCoeff ωF
              * (w₀.differentialCoeff (kaehlerPullback K F E ωE₀))⁻¹)
                • (w₀.differentialCoeff (kaehlerPullback K F E ωE₀) • w₀.dCoord) := by
            rw [w₀.differentialCoeff_smul_dCoord]
        _ = ((w₀.differentialCoeff ωF
              * (w₀.differentialCoeff (kaehlerPullback K F E ωE₀))⁻¹)
                * w₀.differentialCoeff (kaehlerPullback K F E ωE₀)) • w₀.dCoord := by
            rw [smul_smul]
        _ = w₀.differentialCoeff ωF • w₀.dCoord := by
            rw [mul_assoc, inv_mul_cancel₀ hcoeff, mul_one]
        _ = ωF := w₀.differentialCoeff_smul_dCoord ωF
    exact key.symm

  have hterm : ∀ w : Place K F,
      kaehlerResidueTermKFam RfamF ωF (diagonalHom K F f) w
        = kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE₀)
            (diagonalHom K F ((w₀.differentialCoeff ωF
              * (w₀.differentialCoeff (kaehlerPullback K F E ωE₀))⁻¹) * f)) w := by
    intro w
    conv_lhs => rw [hωF_eq]
    exact kaehlerResidueTermKFam_smul_diagonal RfamF _ (kaehlerPullback K F E ωE₀) f w

  have hsup : (Function.support (kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE₀)
      (diagonalHom K F ((w₀.differentialCoeff ωF
        * (w₀.differentialCoeff (kaehlerPullback K F E ωE₀))⁻¹) * f)))).Finite :=
    kaehlerResidueTermKFam_support_finite_of_adeleSpace RfamF hgen
      (diagonal_mem_adeleSpace _)

  calc weilOfKaehlerK RfamF hωF ⟨diagonalHom K F f, diagonal_mem_adeleSpace f⟩
      = ∑ᶠ w : Place K F, kaehlerResidueTermKFam RfamF ωF (diagonalHom K F f) w :=
        weilOfKaehlerK_apply RfamF hωF _
    _ = ∑ᶠ w : Place K F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE₀)
          (diagonalHom K F ((w₀.differentialCoeff ωF
            * (w₀.differentialCoeff (kaehlerPullback K F E ωE₀))⁻¹) * f)) w :=
        finsum_congr hterm
    _ = ∑ᶠ v : Place K E, ∑ w ∈ v.fiber F,
          kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE₀)
            (diagonalHom K F ((w₀.differentialCoeff ωF
              * (w₀.differentialCoeff (kaehlerPullback K F E ωE₀))⁻¹) * f)) w :=
        finsum_place_eq_finsum_fiber_sum (E := E) _ hsup
    _ = ∑ᶠ v : Place K E, kaehlerResidueTermKFam RfamE ωE₀
          (diagonalHom K E (Algebra.trace E F ((w₀.differentialCoeff ωF
            * (w₀.differentialCoeff (kaehlerPullback K F E ωE₀))⁻¹) * f))) v :=
        finsum_congr fun v => hident v _
    _ = 0 := by
        have h0 := hE RfamE hωE₀ (Algebra.trace E F ((w₀.differentialCoeff ωF
          * (w₀.differentialCoeff (kaehlerPullback K F E ωE₀))⁻¹) * f))
        rw [weilOfKaehlerK_apply] at h0
        exact h0

end CotraceResidueIdentityK

section RatFuncFloorSupply

variable {K F : Type*} [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
variable [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [HasCanonicalDivisor (K := K) (F := F)] [∀ w : Place K F, w.DCoordGenerates]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
variable [Algebra.IsIntegral (RatFunc K) F]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates]

/-- (pin 5533) The `RatFunc` headline, at the pin's row-6 name. -/
theorem p0n22_cpf_residueTheoremK_ratFunc_of_isAlgClosed
    (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K (RatFunc K)]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := RatFunc K)]
    [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates] :
    AlgebraicCurve.ResidueTheoremK K (RatFunc K) :=
  AlgebraicCurve.residueTheoremK_ratFunc_of_isAlgClosed K

/-- (pin 5666) The descent step: the ℙ¹ residue theorem plus the fiber-localized
cotrace identity gives the residue theorem for `F`. -/
theorem residueTheoremK_of_cotraceResidueIdentityK_ratFunc_isAlgClosed
    [HasPrincipalDivisors K F]
    (hgen : kaehlerPullback K F (RatFunc K) (dX K) ≠ 0)
    (hIdentK : FiberKaehlerCotraceResidueIdentityK K F (RatFunc K)) :
    ResidueTheoremK K F :=
  residueTheoremK_of_cotraceResidueIdentityK
    (p0n22_cpf_residueTheoremK_ratFunc_of_isAlgClosed K)
    (dX_ne_zero K) hgen hIdentK

end RatFuncFloorSupply

end AlgebraicCurve

namespace AlgebraicCurve

/-! ## Additivity of the residue term (pin 6111–6135) -/

section Additivity

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]

/-- (pin 6111) The residue term is additive in the diagonal representative. -/
theorem kaehlerResidueTermKFam_diagonal_add
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) (ω : Ω[F⁄K])
    (v : Place K F) (g₁ g₂ : F) :
    kaehlerResidueTermKFam Rfam ω (diagonalHom K F (g₁ + g₂)) v
      = kaehlerResidueTermKFam Rfam ω (diagonalHom K F g₁) v
        + kaehlerResidueTermKFam Rfam ω (diagonalHom K F g₂) v := by
  simp only [kaehlerResidueTermKFam_apply, diagonalHom_apply]
  rw [add_mul, map_add, map_add]

/-- (pin 6120) The residue term vanishes at the zero diagonal representative. -/
theorem kaehlerResidueTermKFam_diagonal_zero
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) (ω : Ω[F⁄K])
    (v : Place K F) :
    kaehlerResidueTermKFam Rfam ω (diagonalHom K F (0 : F)) v = 0 := by
  rw [kaehlerResidueTermKFam_apply, diagonalHom_apply, zero_mul, _root_.map_zero, _root_.map_zero]

end Additivity

/-! ## The fiber identity engine (pin 6136–6331) -/

section Engine

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable {E : Type*} [Field E] [Algebra K E] [HasCanonicalLocalResidueKStar K E]
variable [Algebra E F] [IsScalarTower K E F] [Algebra.IsIntegral E F]
variable [HasLocalResidue K E] [HasLocalResidue K F]

/-- (pin 6136) The fiber identity at the zero representative. -/
theorem cotraceFiberIdentityK_zero
    [HasPrincipalDivisors K F]
    (RfamF : ∀ w : Place K F, w.CanonicalLocalResidueDataK)
    (RfamE : ∀ v : Place K E, v.CanonicalLocalResidueDataK)
    (ωE : Ω[E⁄K]) (v : Place K E) :
    ∑ w ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
        (diagonalHom K F (0 : F)) w
      = kaehlerResidueTermKFam RfamE ωE (diagonalHom K E (Algebra.trace E F (0 : F))) v := by
  rw [Finset.sum_eq_zero (fun w _ => kaehlerResidueTermKFam_diagonal_zero RfamF _ w),
    _root_.map_zero (Algebra.trace E F), kaehlerResidueTermKFam_diagonal_zero RfamE ωE v]

/-- (pin 6147) The fiber identity is additive. -/
theorem cotraceFiberIdentityK_add
    [HasPrincipalDivisors K F]
    (RfamF : ∀ w : Place K F, w.CanonicalLocalResidueDataK)
    (RfamE : ∀ v : Place K E, v.CanonicalLocalResidueDataK)
    {ωE : Ω[E⁄K]} (v : Place K E) {g p : F}
    (hg : ∑ w ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
        (diagonalHom K F g) w
      = kaehlerResidueTermKFam RfamE ωE (diagonalHom K E (Algebra.trace E F g)) v)
    (hp : ∑ w ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
        (diagonalHom K F p) w
      = kaehlerResidueTermKFam RfamE ωE (diagonalHom K E (Algebra.trace E F p)) v) :
    ∑ w ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
        (diagonalHom K F (g + p)) w
      = kaehlerResidueTermKFam RfamE ωE (diagonalHom K E (Algebra.trace E F (g + p))) v := by
  calc ∑ w ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
          (diagonalHom K F (g + p)) w
      = ∑ w ∈ v.fiber F,
          (kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE) (diagonalHom K F g) w
            + kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
                (diagonalHom K F p) w) :=
        Finset.sum_congr rfl fun w _ =>
          kaehlerResidueTermKFam_diagonal_add RfamF (kaehlerPullback K F E ωE) w g p
    _ = (∑ w ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
            (diagonalHom K F g) w)
          + ∑ w ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
              (diagonalHom K F p) w :=
        Finset.sum_add_distrib
    _ = kaehlerResidueTermKFam RfamE ωE (diagonalHom K E (Algebra.trace E F g)) v
          + kaehlerResidueTermKFam RfamE ωE (diagonalHom K E (Algebra.trace E F p)) v := by
        rw [hg, hp]
    _ = kaehlerResidueTermKFam RfamE ωE
          (diagonalHom K E (Algebra.trace E F g + Algebra.trace E F p)) v :=
        (kaehlerResidueTermKFam_diagonal_add RfamE ωE v _ _).symm
    _ = kaehlerResidueTermKFam RfamE ωE
          (diagonalHom K E (Algebra.trace E F (g + p))) v := by
        rw [← map_add]

/-- (pin 6184) The uniform-layer induction: the fiber identity holds on a common
regular-pole layer. -/
theorem cotraceFiberIdentityK_of_uniform_layer
    [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
    (RfamF : ∀ w : Place K F, w.CanonicalLocalResidueDataK)
    (RfamE : ∀ v : Place K E, v.CanonicalLocalResidueDataK)
    {ωE : Ω[E⁄K]} (hωE : ωE ≠ 0) (hgen : kaehlerPullback K F E ωE ≠ 0)
    (hA' : ∀ (v : Place K E) (p : F),
        (∀ w₁ ∈ v.fiber F, ∀ w₂ ∈ v.fiber F,
          p ∉ w₁.regularSubmodule (kaehlerPullback K F E ωE) →
          p ∉ w₂.regularSubmodule (kaehlerPullback K F E ωE) → w₁ = w₂) →
        ∑ w ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
            (diagonalHom K F p) w
          = kaehlerResidueTermKFam RfamE ωE (diagonalHom K E (Algebra.trace E F p)) v)
    (hB : CotraceFiberLocalizedPolarApprox K F E)
    (v : Place K E) :
    ∀ (N : ℕ) (f : F),
      (∀ w ∈ v.fiber F, f ∈ w.regularPoleSubmodule (kaehlerPullback K F E ωE) N) →
      ∑ w ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
          (diagonalHom K F f) w
        = kaehlerResidueTermKFam RfamE ωE (diagonalHom K E (Algebra.trace E F f)) v := by
  intro N
  induction N with
  | zero =>
    intro f hf
    refine hA' v f ?_
    intro w₁ hw₁ w₂ hw₂ hp₁ hp₂
    exfalso
    have hreg := hf w₁ hw₁
    rw [Place.regularPoleSubmodule_zero] at hreg
    exact hp₁ hreg
  | succ N ih =>
    intro f hf
    classical

    choose! q hq1 hq2 using fun (w : Place K F) (hw : w ∈ v.fiber F) =>
      hB hωE hgen v w hw N f (hf w hw)

    have hrem : ∀ w₀ ∈ v.fiber F,
        f - ∑ w ∈ v.fiber F, q w
          ∈ w₀.regularPoleSubmodule (kaehlerPullback K F E ωE) N := by
      intro w₀ hw₀
      have hsplit : ∑ w ∈ v.fiber F, q w
          = q w₀ + ∑ w ∈ (v.fiber F).erase w₀, q w :=
        (Finset.add_sum_erase _ q hw₀).symm
      have heq : f - ∑ w ∈ v.fiber F, q w
          = (f - q w₀) - ∑ w ∈ (v.fiber F).erase w₀, q w := by
        rw [hsplit]; ring
      rw [heq]
      refine Submodule.sub_mem _ (hq1 w₀ hw₀) (Submodule.sum_mem _ ?_)
      intro w hw
      have hwfib : w ∈ v.fiber F := Finset.mem_of_mem_erase hw
      have hwne : w ≠ w₀ := Finset.ne_of_mem_erase hw
      have hq_reg : q w ∈ w₀.regularSubmodule (kaehlerPullback K F E ωE) :=
        hq2 w hwfib w₀ hw₀ (Ne.symm hwne)
      rw [← Place.regularPoleSubmodule_zero] at hq_reg
      exact w₀.regularPoleSubmodule_mono _ (Nat.zero_le N) hq_reg

    have hrem_ident := ih (f - ∑ w ∈ v.fiber F, q w) hrem

    have happrox_ident : ∀ w ∈ v.fiber F,
        ∑ w' ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
            (diagonalHom K F (q w)) w'
          = kaehlerResidueTermKFam RfamE ωE
              (diagonalHom K E (Algebra.trace E F (q w))) v := by
      intro w hw
      refine hA' v (q w) ?_
      intro w₁ hw₁ w₂ hw₂ hp₁ hp₂
      have h₁ : w₁ = w := by
        by_contra hne
        exact hp₁ (hq2 w hw w₁ hw₁ hne)
      have h₂ : w₂ = w := by
        by_contra hne
        exact hp₂ (hq2 w hw w₂ hw₂ hne)
      rw [h₁, h₂]

    have hsum_ident :
        ∑ w' ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
            (diagonalHom K F (∑ w ∈ v.fiber F, q w)) w'
          = kaehlerResidueTermKFam RfamE ωE
              (diagonalHom K E (Algebra.trace E F (∑ w ∈ v.fiber F, q w))) v :=
      Finset.sum_induction q
        (fun x => ∑ w' ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
            (diagonalHom K F x) w'
          = kaehlerResidueTermKFam RfamE ωE (diagonalHom K E (Algebra.trace E F x)) v)
        (fun a b ha hb => cotraceFiberIdentityK_add RfamF RfamE v ha hb)
        (cotraceFiberIdentityK_zero RfamF RfamE ωE v)
        happrox_ident

    have hcombined := cotraceFiberIdentityK_add RfamF RfamE v hrem_ident hsum_ident
    rwa [sub_add_cancel] at hcombined

/-- (pin 6274) Rows A and B assemble the fiber Kähler cotrace residue identity. -/
theorem fiberKaehlerCotraceResidueIdentityK_of_rowAK_rowB
    (hA : CotraceResidueIdentityOnFiberLocalizedK K F E)
    (hB : CotraceFiberLocalizedPolarApprox K F E) :
    FiberKaehlerCotraceResidueIdentityK K F E := by
  intro instE instF RfamF ωE hωE hgen
  obtain ⟨RfamE, hA'⟩ := hA RfamF hωE hgen
  refine ⟨RfamE, fun v f => ?_⟩
  classical

  choose nfun hnfun using fun w : Place K F =>
    w.exists_mem_regularPoleSubmodule (kaehlerPullback K F E ωE) f

  refine cotraceFiberIdentityK_of_uniform_layer RfamF RfamE hωE hgen hA' hB v
    (∑ w ∈ v.fiber F, nfun w) f (fun w hw => ?_)
  exact w.regularPoleSubmodule_mono _
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hw) (hnfun w)

end Engine

section RowBDischarged

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable {E : Type*} [Field E] [Algebra K E] [HasCanonicalLocalResidueKStar K E]
variable [Algebra E F] [IsScalarTower K E F] [Algebra.IsIntegral E F]
variable [HasLocalResidue K E] [HasLocalResidue K F]

/-- (pin 6301) Row B is discharged unconditionally, so row A alone gives the fiber
identity. -/
theorem fiberKaehlerCotraceResidueIdentityK_of_rowAK
    (hA : CotraceResidueIdentityOnFiberLocalizedK K F E) :
    FiberKaehlerCotraceResidueIdentityK K F E :=
  fiberKaehlerCotraceResidueIdentityK_of_rowAK_rowB hA
    (ModularCurve.GF24a9RRDx.gf24a9r_cotraceFiberLocalizedPolarApprox K F E)

end RowBDischarged

section CompositeRatFunc

variable {K F : Type*} [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
variable [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [HasCanonicalDivisor (K := K) (F := F)] [∀ w : Place K F, w.DCoordGenerates]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
variable [Algebra.IsIntegral (RatFunc K) F] [HasLocalResidue K F]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates]

/-- (pin 6332) Row A plus the ℙ¹ residue theorem gives the residue theorem for `F`. -/
theorem residueTheoremK_of_rowAK_ratFunc_isAlgClosed
    [HasPrincipalDivisors K F]
    (hgen : kaehlerPullback K F (RatFunc K) (dX K) ≠ 0)
    (hA : CotraceResidueIdentityOnFiberLocalizedK K F (RatFunc K)) :
    ResidueTheoremK K F :=
  residueTheoremK_of_cotraceResidueIdentityK_ratFunc_isAlgClosed hgen
    (fiberKaehlerCotraceResidueIdentityK_of_rowAK hA)

end CompositeRatFunc

/-! ## The data-`KStar` seam (pin 6383–6404) -/

section DataKStarSeam

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]

/-- (pin 6383) The family residue term at the canonical data is the canonical
residue term, definitionally. -/
theorem kaehlerResidueTermKFam_dataKStar (ω : Ω[F⁄K]) (α : Place K F → F) (v : Place K F) :
    kaehlerResidueTermKFam (HasCanonicalLocalResidueKStar.dataKStar) ω α v
      = kaehlerResidueTerm ω α v := rfl

/-- (pin 6387) A subsingleton datum makes the family residue term canonical. -/
theorem kaehlerResidueTermKFam_eq_of_subsingleton
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) (ω : Ω[F⁄K]) (α : Place K F → F)
    (v : Place K F) (hsub : Subsingleton v.CanonicalLocalResidueDataK) :
    kaehlerResidueTermKFam Rfam ω α v = kaehlerResidueTerm ω α v := by
  have hR : Rfam v = HasCanonicalLocalResidueKStar.dataKStar v := hsub.elim _ _
  rw [kaehlerResidueTermKFam_apply, hR]
  rfl

end DataKStarSeam

/-! ## The algebraically closed residue-field discharge (pin 6405–6433) -/

namespace Place

section AlgClosedSurj

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- (pin 6405) Over an algebraically closed field the residue field map is onto for
a finite-residue place. -/
theorem surjective_algebraMap_residueField_of_isAlgClosed_of_finiteResidue
    [IsAlgClosed K] (v : Place K F) [v.FiniteResidue] :
    Function.Surjective (algebraMap K v.ResidueField) := by
  have : Module.Finite K v.ResidueField := Place.FiniteResidue.finite
  have : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K)
    (K := v.ResidueField)).surjective

/-- (pin 6417) Over an algebraically closed field the canonical local residue datum
is subsingleton at a finite-residue place. -/
theorem subsingleton_canonicalLocalResidueDataK_of_isAlgClosed_of_finiteResidue
    [IsAlgClosed K] (v : Place K F) [v.FiniteResidue] :
    Subsingleton v.CanonicalLocalResidueDataK :=
  v.subsingleton_canonicalLocalResidueDataK_of_surj
    v.surjective_algebraMap_residueField_of_isAlgClosed_of_finiteResidue

end AlgClosedSurj

end Place

/-! ## The subsingleton bridge (pin 6434–6539) -/

section SubsingletonBridge

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable {E : Type*} [Field E] [Algebra K E] [HasCanonicalLocalResidueKStar K E]
variable [Algebra E F] [IsScalarTower K E F] [Algebra.IsIntegral E F]

/-- (pin 6434) A subsingleton F-side datum transports the canonical fiber-localized
identity to the `K`-family form. -/
theorem cotraceResidueIdentityOnFiberLocalizedK_of_committed
    (hsubF : ∀ w : Place K F, Subsingleton w.CanonicalLocalResidueDataK)
    (h : CotraceResidueIdentityOnFiberLocalized K F E) :
    CotraceResidueIdentityOnFiberLocalizedK K F E := by
  intro _ _ RfamF ωE hωE hgen
  refine ⟨HasCanonicalLocalResidueKStar.dataKStar, fun v p hloc => ?_⟩
  calc ∑ w ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
          (diagonalHom K F p) w
      = ∑ w ∈ v.fiber F, kaehlerResidueTerm (kaehlerPullback K F E ωE)
          (diagonalHom K F p) w := by
        refine Finset.sum_congr rfl fun w _ => ?_
        exact kaehlerResidueTermKFam_eq_of_subsingleton RfamF _ _ w (hsubF w)
    _ = kaehlerResidueTerm ωE (diagonalHom K E (Algebra.trace E F p)) v :=
        h hωE hgen v p hloc
    _ = kaehlerResidueTermKFam (HasCanonicalLocalResidueKStar.dataKStar) ωE
          (diagonalHom K E (Algebra.trace E F p)) v :=
        (kaehlerResidueTermKFam_dataKStar ωE _ v).symm

end SubsingletonBridge

end AlgebraicCurve

namespace AlgebraicCurve

/-! ## The FKCRI wire (pin 6638–6656) -/

section FKCRIWire

variable (K F : Type*) [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable (E : Type*) [Field E] [Algebra K E] [HasCanonicalLocalResidueKStar K E]
variable [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

/-- (pin 6638) The fiber Kähler cotrace residue identity gives the canonical
fiber-localized identity. -/
theorem kw_mlc_hrtCharP9_cotraceResidueIdentityOnFiberLocalized_of_fkcri
    (h : FiberKaehlerCotraceResidueIdentity K F E) :
    CotraceResidueIdentityOnFiberLocalized K F E := by
  intro _ _ ωE hωE hgen v p _
  exact h hωE hgen v p

end FKCRIWire

/-! ## The FKCRI production (pin 6657–6715) -/

section FKCRIProduction

variable {K F : Type*} [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
variable [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [HasCanonicalDivisor (K := K) (F := F)] [∀ w : Place K F, w.DCoordGenerates]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
variable [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
variable [HasLocalResidue K F]
variable [∀ w : Place K F, w.FiniteResidue]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates]

/-- (pin 6657) The fiber Kähler cotrace residue identity closes the residue theorem
for `F` via the ℙ¹ base case. -/
theorem residueTheoremK_of_fiberKaehlerCotraceResidueIdentity_ratFunc_isAlgClosed
    [HasPrincipalDivisors K F]
    (hgen : kaehlerPullback K F (RatFunc K) (dX K) ≠ 0)
    (hFKCRI : FiberKaehlerCotraceResidueIdentity K F (RatFunc K)) :
    ResidueTheoremK K F :=
  residueTheoremK_of_rowAK_ratFunc_isAlgClosed hgen
    (cotraceResidueIdentityOnFiberLocalizedK_of_committed
      (fun w => w.subsingleton_canonicalLocalResidueDataK_of_isAlgClosed_of_finiteResidue)
      (kw_mlc_hrtCharP9_cotraceResidueIdentityOnFiberLocalized_of_fkcri K F (RatFunc K)
        hFKCRI))

end FKCRIProduction

/-! ## The local residue completion is additive (pin 6756–6851) -/

section LocalResidueCompletion

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

variable [HasCanonicalLocalResidueKStar K E]

/-- (pin 6756) The completion residue is additive. -/
theorem kwHgfV352_localResidueCompletion_sum (v : Place K E) {ι : Type*}
    (s : Finset ι) (f : ι → v.adicCompletion) :
    kwHgfV352_localResidueCompletion v (∑ i ∈ s, f i)
      = ∑ i ∈ s, kwHgfV352_localResidueCompletion v (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [show (0 : v.adicCompletion) = algebraMap E v.adicCompletion 0 from (_root_.map_zero _).symm,
      kwHgfV352_localResidueCompletion_algebraMap, _root_.map_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, kwHgfV352_localResidueCompletion_add, ih,
      Finset.sum_insert ha]

end LocalResidueCompletion

/-! ## The differential-coefficient shift (pin 6960–7057) -/

section OmegaShift

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Nontrivial Ω[F⁄K]]

/-- (pin 6960) Shifting the pulled-back differential into the `dCoord` of `v`. -/
theorem kaehlerResidueTerm_kaehlerPullback_diagonal_eq_dCoord_shift
    [Nontrivial Ω[E⁄K]] (v : Place K E) [v.DCoordGenerates]
    (w : Place K F) [w.DCoordGenerates] (ωE : Ω[E⁄K]) (g : F) :
    kaehlerResidueTerm (kaehlerPullback K F E ωE) (diagonalHom K F g) w
      = kaehlerResidueTerm (kaehlerPullback K F E v.dCoord)
          (diagonalHom K F (g * algebraMap E F (v.differentialCoeff ωE))) w := by
  unfold kaehlerResidueTerm
  congr 2
  show g * w.differentialCoeff (kaehlerPullback K F E ωE)
    = g * algebraMap E F (v.differentialCoeff ωE)
        * w.differentialCoeff (kaehlerPullback K F E v.dCoord)
  rw [differentialCoeff_kaehlerPullback v w ωE, mul_assoc]

end OmegaShift

end AlgebraicCurve

/-! ## The trace coefficient linearity (pin 7058–7126) -/

namespace ModularCurve.KwF4R1V391a

open AlgebraicCurve AlgebraicCurve.Place

section CompletionTraceAtLinear

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F] [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
variable [FiniteDimensional E F]

/-- (pin 7058) The completion trace is `E`-semilinear. -/
theorem kwF4R1V391a_completionTraceF'_mul_algebraMap (w : Place K F) (g : F) (c : E) :
    kw_ffgc_completionTraceF' E w (g * algebraMap E F c)
      = kw_ffgc_completionTraceF' E w g
          * algebraMap E (w.restrict E).adicCompletion c := by
  rw [kw_ffgc_completionTraceF'_apply, kw_ffgc_completionTraceF'_apply, map_mul,
    kw_ffgc_adicCompletionComap_algebraMap_algebraMap E w c,
    mul_comm (algebraMap F w.adicCompletion g) _, ← Algebra.smul_def,
    LinearMap.map_smul, smul_eq_mul, mul_comm]

/-- (pin 7067) The fiber completion trace is `E`-semilinear. -/
theorem kwF4R1V391a_completionTraceAt_mul_algebraMap
    (v : Place K E) (w : Place K F) (hw : w ∈ v.fiber F) (g : F) (c : E) :
    kwHgfV352_completionTraceAt v w hw (g * algebraMap E F c)
      = kwHgfV352_completionTraceAt v w hw g * algebraMap E v.adicCompletion c := by
  have hv : w.restrict E = v := Place.mem_fiber.mp hw
  subst hv
  show (Place.mem_fiber.mp hw ▸ kw_ffgc_completionTraceF' E w (g * algebraMap E F c))
    = (Place.mem_fiber.mp hw ▸ kw_ffgc_completionTraceF' E w g)
        * algebraMap E (w.restrict E).adicCompletion c

  rw [kwF4R1V391a_completionTraceF'_mul_algebraMap w g c]

end CompletionTraceAtLinear

end ModularCurve.KwF4R1V391a

namespace AlgebraicCurve

/-! ## The RTCC + CTS assembly (pin 7929–8025) -/

section Headline

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [HasCanonicalLocalResidueKStar K F]
variable {E : Type*} [Field E] [Algebra K E]
variable [HasCanonicalLocalResidueKStar K E]
variable [Algebra E F] [IsScalarTower K E F] [Algebra.IsIntegral E F]
variable [∀ w : Place K F, w.FiniteResidue] [FiniteDimensional E F]
variable [Nontrivial Ω[E⁄K]] [∀ v : Place K E, v.DCoordGenerates]
variable [Nontrivial Ω[F⁄K]] [∀ w : Place K F, w.DCoordGenerates]

/-- (pin 7929) The trace-completion commutation plus the completion trace sum give
the fiber Kähler cotrace residue identity. -/
theorem kw_es_fiberKaehlerCotraceResidueIdentity_of_RTCC_CTS
    (hRTCC : KwF4R1V391aResidueTraceCompletionCommute K F E)
    (hCTS : KwHgfV352CompletionTraceSum K F E) :
    FiberKaehlerCotraceResidueIdentity K F E := by
  intro _ _ ωE _hωE _hωF v f
  calc ∑ w ∈ v.fiber F,
          kaehlerResidueTerm (kaehlerPullback K F E ωE) (diagonalHom K F f) w

      = ∑ w' ∈ (v.fiber F).attach,
          Algebra.trace K v.ResidueField
            (kwHgfV352_localResidueCompletion v
              (kwHgfV352_completionTraceAt v w'.1 w'.2 f
                * algebraMap E v.adicCompletion (v.differentialCoeff ωE))) := by
        rw [← Finset.sum_attach (v.fiber F)
          (fun w => kaehlerResidueTerm (kaehlerPullback K F E ωE) (diagonalHom K F f) w)]
        refine Finset.sum_congr rfl fun w' _ => ?_
        rw [kaehlerResidueTerm_kaehlerPullback_diagonal_eq_dCoord_shift v w'.1 ωE f,
          hRTCC v w'.1 w'.2 (f * algebraMap E F (v.differentialCoeff ωE)),
          kwF4R1V391a_completionTraceAt_mul_algebraMap v w'.1 w'.2 f
            (v.differentialCoeff ωE)]

    _ = Algebra.trace K v.ResidueField
          (kwHgfV352_localResidueCompletion v
            ((∑ w' ∈ (v.fiber F).attach, kwHgfV352_completionTraceAt v w'.1 w'.2 f)
              * algebraMap E v.adicCompletion (v.differentialCoeff ωE))) := by
        rw [Finset.sum_mul,
          kwHgfV352_localResidueCompletion_sum v (v.fiber F).attach _,
          map_sum]

    _ = Algebra.trace K v.ResidueField
          (kwHgfV352_localResidueCompletion v
            (algebraMap E v.adicCompletion (Algebra.trace E F f)
              * algebraMap E v.adicCompletion (v.differentialCoeff ωE))) := by
        rw [← hCTS v f]

    _ = Algebra.trace K v.ResidueField
          (v.localResidue (Algebra.trace E F f * v.differentialCoeff ωE)) := by
        rw [← map_mul, kwHgfV352_localResidueCompletion_algebraMap v]

    _ = kaehlerResidueTerm ωE (diagonalHom K E (Algebra.trace E F f)) v := by
        unfold kaehlerResidueTerm; rw [diagonalHom_apply]

end Headline

section Compose

variable {K F : Type*} [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
variable [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [HasCanonicalDivisor (K := K) (F := F)] [∀ w : Place K F, w.DCoordGenerates]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
variable [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
variable [HasLocalResidue K F]
variable [∀ w : Place K F, w.FiniteResidue]
variable [Nontrivial Ω[F⁄K]]

/-- (pin 7985) The trace-completion commutation closes the residue theorem, given the
separating differential. -/
theorem kw_es_residueTheoremK_of_RTCC_isAlgClosed
    [HasPrincipalDivisors K F] [Algebra.IsSeparable (RatFunc K) F]
    [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : Place K (RatFunc K), v.DCoordGenerates]
    (hgen : kaehlerPullback K F (RatFunc K) (dX K) ≠ 0)
    (hRTCC : KwF4R1V391aResidueTraceCompletionCommute K F (RatFunc K)) :
    ResidueTheoremK K F := by

  have hCTS : KwHgfV352CompletionTraceSum K F (RatFunc K) :=
    completionTraceSum_of_isSeparable (K := K) (F := F) (E := RatFunc K)

  exact residueTheoremK_of_fiberKaehlerCotraceResidueIdentity_ratFunc_isAlgClosed hgen
    (kw_es_fiberKaehlerCotraceResidueIdentity_of_RTCC_CTS hRTCC hCTS)

/-- (pin 7998) The separating differential is supplied by separability, so the
trace-completion commutation closes the residue theorem. -/
theorem kw_es_residueTheoremK_of_RTCC_isAlgClosed'
    [HasPrincipalDivisors K F] [Algebra.IsSeparable (RatFunc K) F]
    [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : Place K (RatFunc K), v.DCoordGenerates]
    (hRTCC : KwF4R1V391aResidueTraceCompletionCommute K F (RatFunc K)) :
    ResidueTheoremK K F :=
  kw_es_residueTheoremK_of_RTCC_isAlgClosed
    (kaehlerPullback_eq_kaehlerCotrace (K := K) (F := F) (E := RatFunc K) (dX K) ▸
      kaehlerCotrace_dX_ne_zero_of_isSeparable K F
        (AlgebraicCurve.RationalFunctionField.placeInfty K))
    hRTCC

end Compose

end AlgebraicCurve

/-! ## The pin's `solution` body (pin 8082–8104) -/

namespace ModularCurve.KwTateRR3

open AlgebraicCurve

variable {K F : Type*} [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
variable [Field F] [Algebra K F]
variable [HasCanonicalDivisor (K := K) (F := F)] [∀ w : Place K F, w.DCoordGenerates]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
variable [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
variable [HasLocalResidue K F]
variable [∀ w : Place K F, w.FiniteResidue]
variable [Nontrivial Ω[F⁄K]]
variable [IsCurveOver K F] [IsCurveOver K (RatFunc K)]
variable [∀ u : Place K (RatFunc K), u.FiniteResidue]

/-- (pin 8082) The residue theorem for `F`, from the trace-completion commutation of
the `RatFunc` extension (the pin's `kwTateRR3_RTCC_of_isSeparable`, the port's
`residueTraceCompletionCommute`). -/
theorem kwTateRR3_residueTheoremK_of_isAlgClosed
    [HasPrincipalDivisors K F] [Algebra.IsSeparable (RatFunc K) F]
    [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : Place K (RatFunc K), v.DCoordGenerates] :
    ResidueTheoremK K F :=
  kw_es_residueTheoremK_of_RTCC_isAlgClosed'
    (residueTraceCompletionCommute (E := RatFunc K))

end ModularCurve.KwTateRR3

/-! ## The public headline (pin `Thm_` wrapper) -/

theorem AlgebraicCurve.residueTheoremK_of_isAlgClosed
    {K F : Type*} [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
    [Field F] [Algebra K F]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    [∀ w : AlgebraicCurve.Place K F, w.DCoordGenerates]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
    [AlgebraicCurve.HasLocalResidue K F]
    [∀ w : AlgebraicCurve.Place K F, w.FiniteResidue]
    [Nontrivial Ω[F⁄K]]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver K (RatFunc K)]
    [∀ u : AlgebraicCurve.Place K (RatFunc K), u.FiniteResidue]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K F]
    [AlgebraicCurve.HasPrincipalDivisors K F] [Algebra.IsSeparable (RatFunc K) F]
    [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates] :
    AlgebraicCurve.ResidueTheoremK K F :=
  ModularCurve.KwTateRR3.kwTateRR3_residueTheoremK_of_isAlgClosed
