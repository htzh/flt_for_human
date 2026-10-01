/-
Core — part of the ℙ¹ residue core, split from
`Defs/P1ResidueCore.lean` (R1 of `topics/riemannRoch/PLAN-RECTIFY-DEFS.md`).
The original declaration order is preserved; import the preceding slice.
-/
import FLTForHuman.AlgebraicCurve.P1.PerfectResidue

noncomputable section
open Polynomial IsDedekindDomain WithZero IsLocalRing UniqueFactorizationMonoid
open Module
open AlgebraicCurve.RationalFunctionField
open KaehlerDifferential
open AlgebraicCurve.RationalFunctionField KaehlerDifferential
open scoped IntermediateField
open scoped IntermediateField Polynomial AlgebraicCurve AlgebraicCurve.RationalFunctionField
open KaehlerDifferential Module IntermediateField
open AlgebraicCurve

section
section

noncomputable section


namespace AlgebraicCurve

open RationalFunctionField



set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

section LemmaAPerfect

variable {K : Type*} [Field K] [PerfectField K]

theorem ag9b13e_ratFuncDXCoeff_uniformizer_ne_zero_and_ord_le_of_perfectField
    (v : Place K (RatFunc K)) {g : RatFunc K} (hg : g ∈ v.toValuationSubring) :
    ratFuncDXCoeff K v.uniformizer ≠ 0 ∧
      (ratFuncDXCoeff K g = 0 ∨
        v.ord (ratFuncDXCoeff K v.uniformizer) ≤ v.ord (ratFuncDXCoeff K g)) := by
  classical
  have hg0 : 0 ≤ v.ord g := v.ord_nonneg_of_mem hg
  rcases eq_or_ne g 0 with rfl | hgne
  · refine ⟨?_, Or.inl (ratFuncDXCoeff_zero (K := K))⟩
    rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
    · obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
      exact (ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one hp hwp
        (PerfectField.separable_of_irreducible hp)
        (Place.uniformizer_ne_zero _) (Place.ord_uniformizer _)).1
    · exact (ratFuncDXCoeff_ne_zero_and_ord_placeInfty_eq_two_of_ord_eq_one
        ((p1PlaceInfty K).uniformizer_ne_zero) ((p1PlaceInfty K).ord_uniformizer)).1
  · rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
    ·
      obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
      obtain ⟨hπne, hπord⟩ := ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one hp hwp
        (PerfectField.separable_of_irreducible hp)
        (Place.uniformizer_ne_zero _) (Place.ord_uniformizer _)
      refine ⟨hπne, ?_⟩
      rcases ratFuncDXCoeff_eq_zero_or_ord_nonneg_of_ord_nonneg hp hwp hgne hg0 with h0 | hge
      · exact Or.inl h0
      · exact Or.inr (by rw [hπord]; exact hge)
    ·
      obtain ⟨hπne, hπord⟩ :=
        ratFuncDXCoeff_ne_zero_and_ord_placeInfty_eq_two_of_ord_eq_one
          (f := (p1PlaceInfty K).uniformizer)
          ((p1PlaceInfty K).uniformizer_ne_zero) ((p1PlaceInfty K).ord_uniformizer)
      refine ⟨hπne, ?_⟩
      rcases ratFuncDXCoeff_eq_zero_or_two_le_ord_placeInfty_of_ord_nonneg hgne hg0
        with h0 | hge
      · exact Or.inl h0
      · exact Or.inr (by rw [hπord]; exact hge)

theorem ag9b13e_differentialCoeff_D_eq_ratFuncDXCoeff_div_of_perfectField
    (v : Place K (RatFunc K)) (f : RatFunc K)
    (hπ : ratFuncDXCoeff K v.uniformizer ≠ 0) :
    v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) f)
      = ratFuncDXCoeff K f / ratFuncDXCoeff K v.uniformizer :=
  v.differentialCoeff_unique (by
    rw [show v.dCoord = KaehlerDifferential.D K (RatFunc K) v.uniformizer from rfl,
      D_eq_ratFuncDXCoeff_smul_dX K v.uniformizer, D_eq_ratFuncDXCoeff_smul_dX K f,
      smul_smul, div_mul_cancel₀ _ hπ])

theorem ag9b13e_differentialCoeff_D_mem_of_mem_of_perfectField (v : Place K (RatFunc K))
    {g : RatFunc K} (hg : g ∈ v.toValuationSubring) :
    v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) g) ∈ v.toValuationSubring := by
  obtain ⟨hπne, hcase⟩ :=
    ag9b13e_ratFuncDXCoeff_uniformizer_ne_zero_and_ord_le_of_perfectField v hg
  rw [ag9b13e_differentialCoeff_D_eq_ratFuncDXCoeff_div_of_perfectField v g hπne]
  rcases hcase with h0 | hle
  · rw [h0, zero_div]; exact zero_mem _
  · rcases eq_or_ne (ratFuncDXCoeff K g) 0 with h0 | hgne'
    · rw [h0, zero_div]; exact zero_mem _
    · refine v.mem_of_ord_nonneg (div_ne_zero hgne' hπne) ?_
      rw [div_eq_mul_inv, v.ord_mul hgne' (inv_ne_zero hπne), v.ord_inv]
      omega

end LemmaAPerfect

section SimplePoleRowPerfect

variable (K : Type*) [Field K] [PerfectField K]

theorem ag9b13e_canonicalLocalResidueKSimplePoleCoordIndep_ratFunc_of_perfectField :
    CanonicalLocalResidueKSimplePoleCoordIndep K (RatFunc K) :=
  fun v _ hπ' R =>
    Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_inv_of_integral v
      (fun _ hh => ag9b13e_differentialCoeff_D_mem_of_mem_of_perfectField v hh) R hπ'

end SimplePoleRowPerfect

section ChainPerfect

variable (K : Type*) [Field K] [PerfectField K] [DecidableEq (RatFunc K)]

theorem ag9b13e_p1PlaceInftySimplePoleResidueEulerValueX_of_perfectField :
    P1PlaceInftySimplePoleResidueEulerValueX K :=
  p1PlaceInftySimplePoleResidueEulerValueX_of_simplePoleCoordIndep K
    (ag9b13e_canonicalLocalResidueKSimplePoleCoordIndep_ratFunc_of_perfectField K)

theorem ag9b13e_p1PlaceInftySimplePoleResidueEulerValueMonomial_of_perfectField :
    P1PlaceInftySimplePoleResidueEulerValueMonomial K :=
  p1PlaceInftySimplePoleResidueEulerValueMonomial_of_X K
    (ordDifferential_dX_placeInfty_of_perfectField K)
    (ag9b13e_p1PlaceInftySimplePoleResidueEulerValueX_of_perfectField K)

theorem ag9b13e_p1PlaceInftySimplePoleResidueEulerValue_of_perfectField :
    P1PlaceInftySimplePoleResidueEulerValue K :=
  p1PlaceInftySimplePoleResidueEulerValue_of_monomial K
    (ordDifferential_dX_placeInfty_of_perfectField K)
    (ag9b13e_p1PlaceInftySimplePoleResidueEulerValueMonomial_of_perfectField K)

end ChainPerfect

end AlgebraicCurve

namespace ModularCurve

open AlgebraicCurve

namespace MilneAvAg9bRd13X113FourRowUpgrade


set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

end MilneAvAg9bRd13X113FourRowUpgrade

end ModularCurve

end

end

end

section
section

set_option linter.unusedSectionVars false

noncomputable section


namespace AlgebraicCurve

open RationalFunctionField



section KernelEngine

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
variable [HasPrincipalDivisors K F]

def kaehlerResidueFunctionalK (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) : F →ₗ[K] K :=
  (weilOfKaehlerK Rfam hω).comp (principalAdele K F)

theorem kaehlerResidueFunctionalK_eq_finsum
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) {ω : Ω[F⁄K]} (hω : ω ≠ 0) (f : F) :
    kaehlerResidueFunctionalK Rfam hω f
      = ∑ᶠ v, kaehlerResidueTermKFam Rfam ω (diagonalHom K F f) v := rfl

theorem kaehlerResidueFunctionalK_eq_zero_of_term_zero_compl
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) {ω : Ω[F⁄K]} (hω : ω ≠ 0) {f : F}
    {T : Finset (Place K F)}
    (hcompl : ∀ v ∉ T, kaehlerResidueTermKFam Rfam ω (diagonalHom K F f) v = 0)
    (hsum : ∑ v ∈ T, kaehlerResidueTermKFam Rfam ω (diagonalHom K F f) v = 0) :
    kaehlerResidueFunctionalK Rfam hω f = 0 := by
  rw [kaehlerResidueFunctionalK_eq_finsum Rfam hω f,
    finsum_eq_finsetSum_of_support_subset _
      (fun v hv => by_contra fun hT => hv (hcompl v hT))]
  exact hsum

theorem kaehlerResidueFunctionalK_eq_zero_of_singleton
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) {ω : Ω[F⁄K]} (hω : ω ≠ 0) {f : F}
    {v₀ : Place K F}
    (hcompl : ∀ v, v ≠ v₀ → kaehlerResidueTermKFam Rfam ω (diagonalHom K F f) v = 0)
    (hv₀ : kaehlerResidueTermKFam Rfam ω (diagonalHom K F f) v₀ = 0) :
    kaehlerResidueFunctionalK Rfam hω f = 0 := by
  classical
  refine kaehlerResidueFunctionalK_eq_zero_of_term_zero_compl Rfam hω (T := {v₀}) ?_ ?_
  · intro v hv
    exact hcompl v (by simpa using hv)
  · simpa using hv₀

theorem kaehlerResidueFunctionalK_eq_zero_of_pair
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) {ω : Ω[F⁄K]} (hω : ω ≠ 0) {f : F}
    {v₀ v₁ : Place K F} (hne : v₀ ≠ v₁)
    (hcompl : ∀ v, v ≠ v₀ → v ≠ v₁ → kaehlerResidueTermKFam Rfam ω (diagonalHom K F f) v = 0)
    (hsum : kaehlerResidueTermKFam Rfam ω (diagonalHom K F f) v₀
      + kaehlerResidueTermKFam Rfam ω (diagonalHom K F f) v₁ = 0) :
    kaehlerResidueFunctionalK Rfam hω f = 0 := by
  classical
  refine kaehlerResidueFunctionalK_eq_zero_of_term_zero_compl Rfam hω (T := {v₀, v₁}) ?_ ?_
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
    exact hcompl v hv.1 hv.2
  · rw [Finset.sum_pair hne]
    exact hsum

end KernelEngine

section SimplePoleSeam

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]

theorem kaehlerResidueTermKFam_eq_of_mem_simplePoleSubmodule
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    {ω : Ω[F⁄K]} {f : F} {v : Place K F}
    (hmem : f * v.differentialCoeff ω ∈ v.simplePoleSubmodule) :
    kaehlerResidueTermKFam Rfam ω (diagonalHom K F f) v
      = Algebra.trace K v.ResidueField
          (v.simplePoleResidueAux ⟨f * v.differentialCoeff ω, hmem⟩) := by
  rw [kaehlerResidueTermKFam_apply, diagonalHom_apply,
    (Rfam v).res_simplePole (f * v.differentialCoeff ω) hmem]
  rfl

end SimplePoleSeam

section SmulReduction

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

theorem kaehlerResidueTermKFam_smul_diagonal
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    (g : F) (ω : Ω[F⁄K]) (f : F) (v : Place K F) :
    kaehlerResidueTermKFam Rfam (g • ω) (diagonalHom K F f) v
      = kaehlerResidueTermKFam Rfam ω (diagonalHom K F (g * f)) v := by
  simp only [kaehlerResidueTermKFam_apply, diagonalHom_apply]
  rw [v.differentialCoeff_smul,
    show f * (g * v.differentialCoeff ω) = g * f * v.differentialCoeff ω by ring]

variable [HasCanonicalDivisor (K := K) (F := F)]

theorem weilOfKaehlerK_smul_diagonal [HasPrincipalDivisors K F]
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) {g : F} {ω : Ω[F⁄K]}
    (hω : ω ≠ 0) (hgω : g • ω ≠ 0) (f : F) :
    weilOfKaehlerK Rfam hgω ⟨diagonalHom K F f, diagonal_mem_adeleSpace f⟩
      = weilOfKaehlerK Rfam hω
          ⟨diagonalHom K F (g * f), diagonal_mem_adeleSpace (g * f)⟩ := by
  rw [weilOfKaehlerK_apply, weilOfKaehlerK_apply]
  exact finsum_congr fun v => kaehlerResidueTermKFam_smul_diagonal Rfam g ω f v

end SmulReduction

section PerGenerator

variable {K : Type*} [Field K] [CharZero K] [DecidableEq (RatFunc K)]
variable [HasPrincipalDivisors K (RatFunc K)]

theorem kaehlerResidueFunctionalK_dX_X_pow
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK) (n : ℕ) :
    kaehlerResidueFunctionalK Rfam (dX_ne_zero K) ((RatFunc.X : RatFunc K) ^ n) = 0 := by
  refine kaehlerResidueFunctionalK_eq_zero_of_singleton Rfam (dX_ne_zero K)
    (v₀ := p1PlaceInfty K) ?_ ?_
  ·
    intro v hv
    refine kaehlerResidueTermKFam_eq_zero_of_ord_nonneg Rfam ?_
    rw [diagonalHom_apply]
    exact Or.inr (v.ord_nonneg_of_mem
      (pow_X_mul_mem_of_ne_placeInfty K hv n (p1DifferentialCoeffRegularFinite_dX K v hv)))
  ·
    exact residueTheoremK_placeInfty_clause_X_pow Rfam n

theorem kaehlerResidueTermKFam_atom_eq_zero_of_ne_of_ne
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK)
    {p : K[X]} (hpirr : Irreducible p) (c : K[X]) (m : ℕ) {v : Place K (RatFunc K)}
    (hvp : v ≠ finitePlace K hpirr) (hvinf : v ≠ p1PlaceInfty K) :
    kaehlerResidueTermKFam Rfam (dX K)
      (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c m)) v = 0 := by
  refine kaehlerResidueTermKFam_eq_zero_of_ord_nonneg Rfam ?_
  rw [diagonalHom_apply]
  exact Or.inr (v.ord_nonneg_of_mem
    (mul_mem (p1PrincipalPartAtom_mem_of_ne_finitePlace K hpirr c m hvp hvinf)
      (p1DifferentialCoeffRegularFinite_dX K v hvinf)))

theorem kaehlerResidueTermKFam_atom_placeInfty_eq_zero_of_two_le
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK)
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    {p : K[X]} (hpirr : Irreducible p) (c : K[X]) {m : ℕ}
    (hdeg : c.degree < p.degree) (hm : 2 ≤ m) :
    kaehlerResidueTermKFam Rfam (dX K)
      (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c m)) (p1PlaceInfty K) = 0 := by
  refine kaehlerResidueTermKFam_eq_zero_of_ord_nonneg Rfam ?_
  rw [diagonalHom_apply]
  rcases eq_or_ne c 0 with rfl | hc
  · left
    show algebraMap K[X] (RatFunc K) 0 / (algebraMap K[X] (RatFunc K) p) ^ m
        * (p1PlaceInfty K).differentialCoeff (dX K) = 0
    rw [_root_.map_zero, zero_div, zero_mul]
  · right
    have hatom0 : p1PrincipalPartAtom K p c m ≠ 0 :=
      p1PrincipalPartAtom_ne_zero K hpirr.ne_zero hc m
    have hd0 : (p1PlaceInfty K).differentialCoeff (dX K) ≠ 0 :=
      (p1PlaceInfty K).differentialCoeff_ne_zero (dX_ne_zero K)
    rw [(p1PlaceInfty K).ord_mul hatom0 hd0]
    have h2 : 2 ≤ (p1PlaceInfty K).ord (p1PrincipalPartAtom K p c m) :=
      two_le_ord_placeInfty_p1PrincipalPartAtom K hpirr hc hdeg hm
    have hordD : (p1PlaceInfty K).ord ((p1PlaceInfty K).differentialCoeff (dX K)) = -2 :=
      ordDifferential_placeInfty_D_ratFuncX K hwd
    omega

theorem kaehlerResidueTermKFam_atom_finitePlace_eq_zero_of_two_le
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK)
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K))
    (hHigh5 : P1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg K)
    {p c : K[X]} {m : ℕ} (hpmon : p.Monic) (hpirr : Irreducible p)
    (hdeg : c.degree < p.degree) (hm : 2 ≤ m) :
    kaehlerResidueTermKFam Rfam (dX K)
      (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c m)) (finitePlace K hpirr) = 0 := by
  rw [kaehlerResidueTermKFam_apply, diagonalHom_apply]
  exact p1FinitePlaceCanonicalResidueAtomMGeTwoTrace_of_coordIndep_higherDeg K hcoord hHigh5
    p c m hpmon hpirr hdeg hm (Rfam (finitePlace K hpirr))

theorem kaehlerResidueTermKFam_atom_mOne_two_place_sum
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK)
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    (hsp : CanonicalLocalResidueKSimplePoleCoordIndep K (RatFunc K))
    {p c : K[X]} (hpmon : p.Monic) (hpirr : Irreducible p) (hdeg : c.degree < p.degree) :
    kaehlerResidueTermKFam Rfam (dX K)
        (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c 1)) (finitePlace K hpirr)
      + kaehlerResidueTermKFam Rfam (dX K)
          (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c 1)) (p1PlaceInfty K) = 0 := by

  have hfmem := p1MOneAtom_mul_differentialCoeff_mem_simplePole_finitePlace K
    (dX_ne_zero K) (p1DifferentialCoeffUnitFinite_dX K) hpirr c hdeg
  have himem := p1MOneAtom_mul_differentialCoeff_mem_simplePole_placeInfty K
    (dX_ne_zero K) (ordDifferential_placeInfty_D_ratFuncX K hwd) hpirr c hdeg

  rw [kaehlerResidueTermKFam_eq_of_mem_simplePoleSubmodule Rfam hfmem,
    kaehlerResidueTermKFam_eq_of_mem_simplePoleSubmodule Rfam himem]

  exact p1PrincipalPartMOneSimplePoleCancel_of_simplePoleCoordIndep K hwd
    (dX_ne_zero K) rfl hsp p c hpmon hpirr hdeg hfmem himem

theorem kaehlerResidueFunctionalK_dX_atom
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK)
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K))
    (hsp : CanonicalLocalResidueKSimplePoleCoordIndep K (RatFunc K))
    (hHigh5 : P1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg K)
    {p c : K[X]} {m : ℕ} (hpmon : p.Monic) (hpirr : Irreducible p)
    (hdeg : c.degree < p.degree) (hm : 1 ≤ m) :
    kaehlerResidueFunctionalK Rfam (dX_ne_zero K) (p1PrincipalPartAtom K p c m) = 0 := by
  refine kaehlerResidueFunctionalK_eq_zero_of_pair Rfam (dX_ne_zero K)
    (finitePlace_ne_placeInfty hpirr)
    (fun v hvp hvinf => kaehlerResidueTermKFam_atom_eq_zero_of_ne_of_ne Rfam hpirr c m
      hvp hvinf) ?_

  rcases eq_or_lt_of_le hm with rfl | hm2
  ·
    exact kaehlerResidueTermKFam_atom_mOne_two_place_sum Rfam hwd hsp hpmon hpirr hdeg
  ·
    rw [kaehlerResidueTermKFam_atom_finitePlace_eq_zero_of_two_le Rfam hcoord hHigh5
        hpmon hpirr hdeg hm2,
      kaehlerResidueTermKFam_atom_placeInfty_eq_zero_of_two_le Rfam hwd hpirr c hdeg hm2,
      add_zero]

theorem kaehlerResidueFunctionalK_dX_eq_zero
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK)
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K))
    (hsp : CanonicalLocalResidueKSimplePoleCoordIndep K (RatFunc K))
    (hHigh5 : P1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg K)
    (h : RatFunc K) :
    kaehlerResidueFunctionalK Rfam (dX_ne_zero K) h = 0 := by

  have hker : Submodule.span K (P1PartialFractionGenerators K)
      ≤ LinearMap.ker (kaehlerResidueFunctionalK Rfam (dX_ne_zero K)) := by
    rw [Submodule.span_le]
    rintro s hs
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    rcases hs with hpoly | hatom
    · obtain ⟨n, rfl⟩ := hpoly
      exact kaehlerResidueFunctionalK_dX_X_pow Rfam n
    · obtain ⟨p, c, m, hpmon, hpirr, hdeg, hm, rfl⟩ := hatom
      exact kaehlerResidueFunctionalK_dX_atom Rfam hwd hcoord hsp hHigh5 hpmon hpirr hdeg hm

  have hh : h ∈ LinearMap.ker (kaehlerResidueFunctionalK Rfam (dX_ne_zero K)) := by
    apply hker
    rw [p1PartialFractionSpan_eq_top]
    exact Submodule.mem_top
  exact LinearMap.mem_ker.mp hh

end PerGenerator

section Engine

variable {K : Type*} [Field K] [CharZero K] [DecidableEq (RatFunc K)]

theorem residueTheoremK_ratFunc_of_subrows
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K))
    (hsp : CanonicalLocalResidueKSimplePoleCoordIndep K (RatFunc K))
    (hHigh5 : P1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg K) :
    ResidueTheoremK K (RatFunc K) := by
  intro Rfam instHPD ω hω f

  obtain ⟨g, hg, rfl⟩ := exists_smul_eq_of_ne_zero (p1PlaceInfty K) hω (dX_ne_zero K)
  calc weilOfKaehlerK Rfam hω
        ⟨diagonalHom K (RatFunc K) f, diagonal_mem_adeleSpace f⟩
      = weilOfKaehlerK Rfam (dX_ne_zero K)
          ⟨diagonalHom K (RatFunc K) (g * f), diagonal_mem_adeleSpace (g * f)⟩ :=
        weilOfKaehlerK_smul_diagonal Rfam (dX_ne_zero K) hω f
    _ = 0 := kaehlerResidueFunctionalK_dX_eq_zero Rfam hwd hcoord hsp hHigh5 (g * f)

end Engine

section AlgClosedDischarge

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] [DecidableEq (RatFunc K)]

theorem residueTheoremK_ratFunc_of_isAlgClosed_main : ResidueTheoremK K (RatFunc K) :=
  residueTheoremK_ratFunc_of_subrows
    (ordDifferentialWellDefined_ratFunc K)
    (canonicalLocalResidueKDifferentialCoordIndep_ratFunc_of_isAlgClosed K)
    (canonicalLocalResidueKSimplePoleCoordIndep_ratFunc K)
    (p1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg_of_algClosed K)

end AlgClosedDischarge

section BridgeCorollary

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] [DecidableEq (RatFunc K)]

end BridgeCorollary

end AlgebraicCurve

section AxiomAudit

end AxiomAudit

end

end

end

section
section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000
set_option synthInstance.maxSize 4096
set_option maxRecDepth 8000

noncomputable section


namespace AlgebraicCurve

open RationalFunctionField



section MOnePerfect

theorem p0n21_rtk_p1MOneSimplePoleCancel_dX_of_perfectField
    (K : Type*) [Field K] [PerfectField K] [DecidableEq (RatFunc K)] :
    P1PrincipalPartMOneSimplePoleCancel K (dX_ne_zero K) :=
  ag9b12c_p1MOneSimplePoleCancel_dX_of_inftyEulerValue_of_perfectField K
    (ag9b13e_p1PlaceInftySimplePoleResidueEulerValue_of_perfectField K)

end MOnePerfect

section PerGenerator

variable {K : Type*} [Field K] [PerfectField K] [DecidableEq (RatFunc K)]
variable [HasPrincipalDivisors K (RatFunc K)]

theorem p0n21_rtk_kaehlerResidueFunctionalK_dX_X_pow
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK)
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K)) (n : ℕ) :
    kaehlerResidueFunctionalK Rfam (dX_ne_zero K) ((RatFunc.X : RatFunc K) ^ n) = 0 := by
  refine kaehlerResidueFunctionalK_eq_zero_of_singleton Rfam (dX_ne_zero K)
    (v₀ := p1PlaceInfty K) ?_ ?_
  ·
    intro v hv
    refine kaehlerResidueTermKFam_eq_zero_of_ord_nonneg Rfam ?_
    rw [diagonalHom_apply]
    exact Or.inr (v.ord_nonneg_of_mem
      (pow_X_mul_mem_of_ne_placeInfty K hv n
        (p1DifferentialCoeffRegularFinite_dX_of_perfectField K v hv)))
  ·
    rw [kaehlerResidueTermKFam_apply]
    exact canonicalLocalResidueDataK_kaehlerResidueTerm_X_pow_of_coordIndep K hwd hcoord
      (Rfam (p1PlaceInfty K)) n

theorem p0n21_rtk_kaehlerResidueTermKFam_atom_eq_zero_of_ne_of_ne
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK)
    {p : K[X]} (hpirr : Irreducible p) (c : K[X]) (m : ℕ) {v : Place K (RatFunc K)}
    (hvp : v ≠ finitePlace K hpirr) (hvinf : v ≠ p1PlaceInfty K) :
    kaehlerResidueTermKFam Rfam (dX K)
      (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c m)) v = 0 := by
  refine kaehlerResidueTermKFam_eq_zero_of_ord_nonneg Rfam ?_
  rw [diagonalHom_apply]
  exact Or.inr (v.ord_nonneg_of_mem
    (mul_mem (p1PrincipalPartAtom_mem_of_ne_finitePlace K hpirr c m hvp hvinf)
      (p1DifferentialCoeffRegularFinite_dX_of_perfectField K v hvinf)))

theorem p0n21_rtk_kaehlerResidueTermKFam_atom_placeInfty_eq_zero_of_two_le
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK)
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    {p : K[X]} (hpirr : Irreducible p) (c : K[X]) {m : ℕ}
    (hdeg : c.degree < p.degree) (hm : 2 ≤ m) :
    kaehlerResidueTermKFam Rfam (dX K)
      (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c m)) (p1PlaceInfty K) = 0 := by
  refine kaehlerResidueTermKFam_eq_zero_of_ord_nonneg Rfam ?_
  rw [diagonalHom_apply]
  rcases eq_or_ne c 0 with rfl | hc
  · left
    show algebraMap K[X] (RatFunc K) 0 / (algebraMap K[X] (RatFunc K) p) ^ m
        * (p1PlaceInfty K).differentialCoeff (dX K) = 0
    rw [_root_.map_zero, zero_div, zero_mul]
  · right
    have hatom0 : p1PrincipalPartAtom K p c m ≠ 0 :=
      p1PrincipalPartAtom_ne_zero K hpirr.ne_zero hc m
    have hd0 : (p1PlaceInfty K).differentialCoeff (dX K) ≠ 0 :=
      (p1PlaceInfty K).differentialCoeff_ne_zero (dX_ne_zero K)
    rw [(p1PlaceInfty K).ord_mul hatom0 hd0]
    have h2 : 2 ≤ (p1PlaceInfty K).ord (p1PrincipalPartAtom K p c m) :=
      two_le_ord_placeInfty_p1PrincipalPartAtom K hpirr hc hdeg hm
    have hordD : (p1PlaceInfty K).ord ((p1PlaceInfty K).differentialCoeff (dX K)) = -2 :=
      ordDifferential_placeInfty_D_ratFuncX K hwd
    omega

theorem p0n21_rtk_kaehlerResidueTermKFam_atom_finitePlace_eq_zero_of_two_le
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK)
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K))
    (hHigh5 : P1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg K)
    {p c : K[X]} {m : ℕ} (hpmon : p.Monic) (hpirr : Irreducible p)
    (hdeg : c.degree < p.degree) (hm : 2 ≤ m) :
    kaehlerResidueTermKFam Rfam (dX K)
      (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c m)) (finitePlace K hpirr) = 0 := by
  rw [kaehlerResidueTermKFam_apply, diagonalHom_apply]
  exact p1FinitePlaceCanonicalResidueAtomMGeTwoTrace_of_coordIndep_higherDeg K hcoord hHigh5
    p c m hpmon hpirr hdeg hm (Rfam (finitePlace K hpirr))

theorem p0n21_rtk_kaehlerResidueTermKFam_atom_mOne_two_place_sum
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK)
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    {p c : K[X]} (hpmon : p.Monic) (hpirr : Irreducible p) (hdeg : c.degree < p.degree) :
    kaehlerResidueTermKFam Rfam (dX K)
        (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c 1)) (finitePlace K hpirr)
      + kaehlerResidueTermKFam Rfam (dX K)
          (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c 1)) (p1PlaceInfty K) = 0 := by
  have hfmem := p1MOneAtom_mul_differentialCoeff_mem_simplePole_finitePlace K
    (dX_ne_zero K) (p1DifferentialCoeffUnitFinite_dX_of_perfectField K) hpirr c hdeg
  have himem := p1MOneAtom_mul_differentialCoeff_mem_simplePole_placeInfty K
    (dX_ne_zero K) (ordDifferential_placeInfty_D_ratFuncX K hwd) hpirr c hdeg
  rw [kaehlerResidueTermKFam_eq_of_mem_simplePoleSubmodule Rfam hfmem,
    kaehlerResidueTermKFam_eq_of_mem_simplePoleSubmodule Rfam himem]
  exact p0n21_rtk_p1MOneSimplePoleCancel_dX_of_perfectField K p c hpmon hpirr hdeg hfmem himem

theorem p0n21_rtk_kaehlerResidueFunctionalK_dX_atom
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK)
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K))
    (hHigh5 : P1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg K)
    {p c : K[X]} {m : ℕ} (hpmon : p.Monic) (hpirr : Irreducible p)
    (hdeg : c.degree < p.degree) (hm : 1 ≤ m) :
    kaehlerResidueFunctionalK Rfam (dX_ne_zero K) (p1PrincipalPartAtom K p c m) = 0 := by
  refine kaehlerResidueFunctionalK_eq_zero_of_pair Rfam (dX_ne_zero K)
    (finitePlace_ne_placeInfty hpirr)
    (fun v hvp hvinf => p0n21_rtk_kaehlerResidueTermKFam_atom_eq_zero_of_ne_of_ne Rfam hpirr
      c m hvp hvinf) ?_
  rcases eq_or_lt_of_le hm with rfl | hm2
  · exact p0n21_rtk_kaehlerResidueTermKFam_atom_mOne_two_place_sum Rfam hwd hpmon hpirr hdeg
  · rw [p0n21_rtk_kaehlerResidueTermKFam_atom_finitePlace_eq_zero_of_two_le Rfam hcoord hHigh5
        hpmon hpirr hdeg hm2,
      p0n21_rtk_kaehlerResidueTermKFam_atom_placeInfty_eq_zero_of_two_le Rfam hwd hpirr c
        hdeg hm2,
      add_zero]

theorem p0n21_rtk_kaehlerResidueFunctionalK_dX_eq_zero
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK)
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K))
    (hHigh5 : P1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg K)
    (h : RatFunc K) :
    kaehlerResidueFunctionalK Rfam (dX_ne_zero K) h = 0 := by
  have hker : Submodule.span K (P1PartialFractionGenerators K)
      ≤ LinearMap.ker (kaehlerResidueFunctionalK Rfam (dX_ne_zero K)) := by
    rw [Submodule.span_le]
    rintro s hs
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    rcases hs with hpoly | hatom
    · obtain ⟨n, rfl⟩ := hpoly
      exact p0n21_rtk_kaehlerResidueFunctionalK_dX_X_pow Rfam hwd hcoord n
    · obtain ⟨p, c, m, hpmon, hpirr, hdeg, hm, rfl⟩ := hatom
      exact p0n21_rtk_kaehlerResidueFunctionalK_dX_atom Rfam hwd hcoord hHigh5 hpmon hpirr
        hdeg hm
  have hh : h ∈ LinearMap.ker (kaehlerResidueFunctionalK Rfam (dX_ne_zero K)) := by
    apply hker
    rw [p1PartialFractionSpan_eq_top]
    exact Submodule.mem_top
  exact LinearMap.mem_ker.mp hh

end PerGenerator

section EngineCharFree

variable {K : Type*} [Field K] [PerfectField K] [DecidableEq (RatFunc K)]

theorem p0n21_rtk_residueTheoremK_ratFunc_of_subrows_charFree
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K))
    (hHigh5 : P1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg K) :
    ResidueTheoremK K (RatFunc K) := by
  intro Rfam instHPD ω hω f
  obtain ⟨g, hg, rfl⟩ := exists_smul_eq_of_ne_zero (p1PlaceInfty K) hω (dX_ne_zero K)
  calc weilOfKaehlerK Rfam hω
        ⟨diagonalHom K (RatFunc K) f, diagonal_mem_adeleSpace f⟩
      = weilOfKaehlerK Rfam (dX_ne_zero K)
          ⟨diagonalHom K (RatFunc K) (g * f), diagonal_mem_adeleSpace (g * f)⟩ :=
        weilOfKaehlerK_smul_diagonal Rfam (dX_ne_zero K) hω f
    _ = 0 := p0n21_rtk_kaehlerResidueFunctionalK_dX_eq_zero Rfam hwd hcoord hHigh5 (g * f)

theorem p0n21_rtk_residueTheoremK_ratFunc_of_coordIndep_higherDeg_of_perfectField
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K))
    (hHigh5 : P1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg K) :
    ResidueTheoremK K (RatFunc K) :=
  p0n21_rtk_residueTheoremK_ratFunc_of_subrows_charFree
    (ordDifferentialWellDefined_ratFunc_of_perfectField K) hcoord hHigh5

end EngineCharFree

section AlgClosedAnyChar

theorem p0n21_rtk_residueTheoremK_ratFunc_of_isAlgClosed_of_coordIndep
    (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K)) :
    ResidueTheoremK K (RatFunc K) :=
  p0n21_rtk_residueTheoremK_ratFunc_of_coordIndep_higherDeg_of_perfectField hcoord
    (p1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg_of_algClosed K)

end AlgClosedAnyChar

section Bc2Carrier

local notation "Qbar" => AlgebraicClosure ℚ

end Bc2Carrier

section ResidualLocation

theorem p0n21_rtk_surjective_algebraMap_residueField_of_deg_eq_one
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hdeg : v.deg = 1) :
    Function.Surjective (algebraMap K v.ResidueField) := by
  intro z
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : v.ResidueField) one_ne_zero).mp
    (show Module.finrank K v.ResidueField = 1 from hdeg) z
  exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc⟩

theorem p0n21_rtk_surjective_algebraMap_residueField_ratFunc_of_isAlgClosed
    (K : Type*) [Field K] [IsAlgClosed K] (v : Place K (RatFunc K)) :
    Function.Surjective (algebraMap K v.ResidueField) := by
  classical
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  · obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
    refine p0n21_rtk_surjective_algebraMap_residueField_of_deg_eq_one _ ?_
    rw [deg_ofHeightOneSpectrum K hwp]
    have h := IsAlgClosed.degree_eq_one_of_irreducible K hp
    rw [degree_eq_natDegree hp.ne_zero] at h
    exact_mod_cast h
  · exact surjective_algebraMap_residueField_placeInfty K

end ResidualLocation

end AlgebraicCurve

end

end

end

section
section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000
set_option synthInstance.maxSize 4096
set_option maxRecDepth 8000

noncomputable section


namespace AlgebraicCurve

open RationalFunctionField



section CharFreeToolkit

variable {K : Type*} [Field K] [PerfectField K]

end CharFreeToolkit
section CharPCartier
variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [PerfectField K] [hKp : CharP K p]
end CharPCartier
section Headlines
theorem p0n22_cpf_canonicalLocalResidueKDifferentialCoordIndep_ratFunc_of_isAlgClosed
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K) :=
  fun v π' hπ' R _ hn =>
    p0n22_cpf_res_differentialCoeff_D_mul_pow_inv_of_surj (p := p) v
      (fun _ hh => ag9b13e_differentialCoeff_D_mem_of_mem_of_perfectField v hh)
      (p0n21_rtk_surjective_algebraMap_residueField_ratFunc_of_isAlgClosed K v)
      π' hπ' R hn

theorem p0n22_cpf_residueTheoremK_ratFunc_of_isAlgClosed_of_charP
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    [DecidableEq (RatFunc K)] :
    ResidueTheoremK K (RatFunc K) :=
  p0n21_rtk_residueTheoremK_ratFunc_of_isAlgClosed_of_coordIndep K
    (p0n22_cpf_canonicalLocalResidueKDifferentialCoordIndep_ratFunc_of_isAlgClosed K p)

theorem p0n22_cpf_residueTheoremK_ratFunc_of_isAlgClosed_main
    (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)] :
    ResidueTheoremK K (RatFunc K) := by
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hprime | hzero
  · haveI : Fact (ringChar K).Prime := ⟨hprime⟩
    exact p0n22_cpf_residueTheoremK_ratFunc_of_isAlgClosed_of_charP K (ringChar K)
  · haveI : CharP K 0 := hzero ▸ ringChar.charP K
    haveI : CharZero K := CharP.charP_to_charZero K
    exact residueTheoremK_ratFunc_of_isAlgClosed_main K

end Headlines

section Bc2Carrier

local notation "Qbar" => AlgebraicClosure ℚ

end Bc2Carrier

end AlgebraicCurve

end

end

end

set_option autoImplicit false

namespace AlgebraicCurve

open RationalFunctionField

theorem RationalFunctionField.placeInfty_eq_p1PlaceInfty (K : Type*) [Field K] [DecidableEq (RatFunc K)] :
    RationalFunctionField.placeInfty K = p1PlaceInfty K := rfl

namespace RationalFunctionField

theorem trace_localResidue_placeInfty_X_pow_eq_zero
    (K : Type*) [Field K] [PerfectField K] [DecidableEq (RatFunc K)]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K (RatFunc K)]
    [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
    (n : ℕ) :
    Algebra.trace K (AlgebraicCurve.RationalFunctionField.placeInfty K).ResidueField
        ((AlgebraicCurve.RationalFunctionField.placeInfty K).localResidue
          ((RatFunc.X : RatFunc K) ^ n
            * (AlgebraicCurve.RationalFunctionField.placeInfty K).differentialCoeff
                (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)))) = 0 := by
  rw [RationalFunctionField.placeInfty_eq_p1PlaceInfty]
  have hres : (RationalFunctionField.p1PlaceInfty K).localResidue ((RatFunc.X : RatFunc K) ^ n
      * (RationalFunctionField.p1PlaceInfty K).differentialCoeff
          (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K))) = 0 := by
    show (HasCanonicalLocalResidueKStar.dataKStar (RationalFunctionField.p1PlaceInfty K)).res _ = 0
    rw [X_pow_mul_differentialCoeff_D_X_eq_neg K n, _root_.map_neg, neg_eq_zero]
    exact AlgebraicCurve.Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap
      (RationalFunctionField.p1PlaceInfty K) (surjective_algebraMap_residueField_placeInfty K)
      (fun h hh => ag9b13e_differentialCoeff_D_mem_of_mem_of_perfectField (RationalFunctionField.p1PlaceInfty K) hh)
      (HasCanonicalLocalResidueKStar.dataKStar (RationalFunctionField.p1PlaceInfty K))
      (ord_placeInfty_X_inv K) (Nat.le_add_left 1 n)
  rw [hres, _root_.map_zero]

end RationalFunctionField

end AlgebraicCurve

end
