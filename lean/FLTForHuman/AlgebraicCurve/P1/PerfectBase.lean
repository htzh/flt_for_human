/-
PerfectBase — the perfect-field base case of the ℙ¹ residue theorem.

Port of `AlgebraicCurve.residueTheorem_ratFunc_of_perfectField` from
`P2M/Sol/S_AlgebraicCurve_residueTheorem_ratFunc_of_perfectField.lean`
(pin `anthropics/fermats-last-theorem@aa2d8b3`, the `solution` at lines
4314–4340 and its 38-declaration tail from 3574). The shared `P1/` engine is
imported, never re-proved; the sibling twins the pin repeats under its
`placeInfty` spelling are already declared in the port under `p1PlaceInfty`
(definitionally equal by `RationalFunctionField.placeInfty_eq_p1PlaceInfty`),
and `P1PrincipalPartTwoPlaceCancelMOne` is imported from `P1/TwoPlace.lean`.

The proof is the pin's own: a `K →ₗ[K] K` residue functional on `F`, a kernel
`Submodule K F`, the generator/partial-fraction decomposition of
`P1PartialFractionGenerators`, the named subrows, and the perfect-field
specialisations. It closes on the atom-2 and atom-3 headlines
(`P1/TwoPlace.lean`, `P1/DivPowEnding.lean`).

Declarations the pin repeats that are already public in the port are imported,
not re-declared: `P1PrincipalPartTwoPlaceCancelMOne` (`P1/TwoPlace.lean`),
`p1DifferentialCoeffUnitFinite_dX_of_perfectField` and
`p1DifferentialCoeffRegularFinite_dX_of_perfectField`
(`P1/PerfectField.lean`), `exists_ne_zero_smul_dX_of_uniformizer` and the
`scoped instance instDCoordGeneratesPerfectField` (`P1/PerfectField.lean`). The
p1-place twins (`pow_X_mul_mem_of_ne_placeInfty`, `p1PrincipalPartAtom_mem_of_ne_finitePlace`,
`finitePlace_ne_placeInfty`, `two_le_ord_placeInfty_p1PrincipalPartAtom`,
`ordDifferential_placeInfty_D_ratFuncX`) are stated at the port's `p1PlaceInfty`
and adapted with `RationalFunctionField.placeInfty_eq_p1PlaceInfty` where a
rewrite needs the pin's spelling.
-/
import FLTForHuman.AlgebraicCurve.P1.TwoPlace
import FLTForHuman.AlgebraicCurve.P1.DivPowEnding
import FLTForHuman.AlgebraicCurve.P1.PerfectField

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

section Engine

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

/-- Residue term of a scalar multiple: `g • ω` against the adele `α` equals `ω`
against the `g`-multiple of `α`. -/
theorem kaehlerResidueTerm_smul_left (g : F) (ω : Ω[F⁄K]) (α : Place K F → F)
    (v : Place K F) :
    kaehlerResidueTerm (g • ω) α v = kaehlerResidueTerm ω (mulAdele K g α) v := by
  unfold kaehlerResidueTerm
  rw [v.differentialCoeff_smul, mulAdele_apply, mul_left_comm, mul_assoc]

theorem weilSmul_weilOfKaehler [HasPrincipalDivisors K F] {g : F} {ω : Ω[F⁄K]}
    (hω : ω ≠ 0) (hgω : g • ω ≠ 0) :
    weilSmul K F g (weilOfKaehler K F hω) = weilOfKaehler K F hgω := by
  refine LinearMap.ext fun α => ?_
  rw [weilSmul_apply, weilOfKaehler_apply, weilOfKaehler_apply]
  exact finsum_congr fun v => (kaehlerResidueTerm_smul_left g ω α v).symm

theorem weilOfKaehler_smul_diagonal [HasPrincipalDivisors K F] {g : F} {ω : Ω[F⁄K]}
    (hω : ω ≠ 0) (hgω : g • ω ≠ 0) (f : F) :
    weilOfKaehler K F hgω ⟨diagonalHom K F f, diagonal_mem_adeleSpace f⟩
      = weilOfKaehler K F hω ⟨diagonalHom K F (g * f), diagonal_mem_adeleSpace (g * f)⟩ := by
  rw [← weilSmul_weilOfKaehler hω hgω, weilSmul_apply]
  exact congrArg _ (Subtype.ext (funext fun v => by
    simp only [adeleSpaceMul_coe, mulAdele_apply, diagonalHom_apply]))

theorem residueTheorem_iff_of_ne_zero (v : Place K F) {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) :
    ResidueTheorem K F ↔
      ∀ [HasPrincipalDivisors K F], ∀ f : F,
        weilOfKaehler K F hω₀ ⟨diagonalHom K F f, diagonal_mem_adeleSpace f⟩ = 0 := by
  constructor
  · intro hRT _ f; exact hRT hω₀ f
  · intro hsingle _ ω hω f
    obtain ⟨g, hg, rfl⟩ := exists_smul_eq_of_ne_zero v hω hω₀
    rw [weilOfKaehler_smul_diagonal hω₀ hω f]
    exact hsingle (g * f)

end Engine

section ResidueFunctional

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
variable [HasPrincipalDivisors K F]

variable (K F) in

/-- The Kähler residue functional `F →ₗ[K] K`. -/
def kaehlerResidueFunctional {ω : Ω[F⁄K]} (hω : ω ≠ 0) : F →ₗ[K] K :=
  (weilOfKaehler K F hω).comp (principalAdele K F)

variable (K F) in

/-- Its kernel, the submodule of `F` whose residue terms sum to zero. -/
def kaehlerResidueKernel {ω : Ω[F⁄K]} (hω : ω ≠ 0) : Submodule K F :=
  LinearMap.ker (kaehlerResidueFunctional (K := K) (F := F) hω)

theorem mem_kaehlerResidueKernel {ω : Ω[F⁄K]} (hω : ω ≠ 0) {f : F} :
    f ∈ kaehlerResidueKernel K F hω
      ↔ weilOfKaehler K F hω ⟨diagonalHom K F f, diagonal_mem_adeleSpace f⟩ = 0 :=
  Iff.rfl

theorem residueTheorem_iff_kaehlerResidueKernel_eq_top (v : Place K F)
    {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) :
    ResidueTheorem K F ↔ kaehlerResidueKernel K F hω₀ = ⊤ := by
  rw [residueTheorem_iff_of_ne_zero v hω₀, Submodule.eq_top_iff']
  exact ⟨fun h f => (mem_kaehlerResidueKernel hω₀).mpr (h f),
    fun h _ f => (mem_kaehlerResidueKernel hω₀).mp (h f)⟩

theorem residueTheorem_of_span_le_kernel (v : Place K F)
    {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) {S : Set F}
    (hspan : Submodule.span K S = ⊤) (hS : S ⊆ kaehlerResidueKernel K F hω₀) :
    ResidueTheorem K F := by
  rw [residueTheorem_iff_kaehlerResidueKernel_eq_top v hω₀]
  exact top_unique (hspan ▸ Submodule.span_le.mpr hS)

theorem residueTheorem_of_union_span_le_kernel (v : Place K F)
    {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) {S₁ S₂ : Set F}
    (hspan : Submodule.span K (S₁ ∪ S₂) = ⊤)
    (hS₁ : S₁ ⊆ kaehlerResidueKernel K F hω₀)
    (hS₂ : S₂ ⊆ kaehlerResidueKernel K F hω₀) :
    ResidueTheorem K F :=
  residueTheorem_of_span_le_kernel v hω₀ hspan (Set.union_subset hS₁ hS₂)

end ResidueFunctional

section P1NamedRows

variable (K : Type*) [Field K]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]

/-- The partial-fraction span of the ℙ¹ generators is everything. -/
def P1PartialFractionSpan : Prop :=
  Submodule.span K (P1PartialFractionGenerators K) = ⊤

/-- The polynomial generators lie in the residue kernel. -/
def P1ResiduePolynomialPart {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0) : Prop :=
  P1PolynomialGenerators K ⊆ kaehlerResidueKernel (K := K) (F := RatFunc K) hω₀

/-- The principal-part generators lie in the residue kernel. -/
def P1ResiduePrincipalPart {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0) : Prop :=
  P1PrincipalPartGenerators K ⊆ kaehlerResidueKernel (K := K) (F := RatFunc K) hω₀

variable {K}

theorem residueTheorem_ratFunc_of_partialFractions (v : Place K (RatFunc K))
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0)
    (hspan : P1PartialFractionSpan K)
    (hpoly : P1ResiduePolynomialPart K hω₀) (hprin : P1ResiduePrincipalPart K hω₀) :
    ResidueTheorem K (RatFunc K) :=
  residueTheorem_of_union_span_le_kernel v hω₀ hspan hpoly hprin

end P1NamedRows

section GeneratorsResidue

variable {K : Type*} [Field K]

theorem residueTheorem_ratFunc_of_generators_residue
    [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
    [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
    [HasPrincipalDivisors K (RatFunc K)]
    (v : Place K (RatFunc K)) {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0)
    (hpoly : P1ResiduePolynomialPart K hω₀) (hprin : P1ResiduePrincipalPart K hω₀) :
    ResidueTheorem K (RatFunc K) :=
  residueTheorem_ratFunc_of_partialFractions v hω₀ p1PartialFractionSpan_eq_top hpoly hprin

end GeneratorsResidue

section KernelFinsum

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
variable [HasPrincipalDivisors K F]

theorem mem_kaehlerResidueKernel_iff_finsum {ω : Ω[F⁄K]} (hω : ω ≠ 0) {f : F} :
    f ∈ kaehlerResidueKernel K F hω
      ↔ ∑ᶠ v, kaehlerResidueTerm ω (diagonalHom K F f) v = 0 :=
  Iff.rfl

theorem mem_kaehlerResidueKernel_of_term_zero_compl {ω : Ω[F⁄K]} (hω : ω ≠ 0) {f : F}
    {T : Finset (Place K F)}
    (hcompl : ∀ v ∉ T, kaehlerResidueTerm ω (diagonalHom K F f) v = 0)
    (hsum : ∑ v ∈ T, kaehlerResidueTerm ω (diagonalHom K F f) v = 0) :
    f ∈ kaehlerResidueKernel K F hω := by
  rw [mem_kaehlerResidueKernel_iff_finsum hω,
    finsum_eq_finsetSum_of_support_subset _
      (fun v hv => by_contra fun hT => hv (hcompl v hT))]
  exact hsum

theorem mem_kaehlerResidueKernel_of_singleton {ω : Ω[F⁄K]} (hω : ω ≠ 0) {f : F}
    {v₀ : Place K F}
    (hcompl : ∀ v, v ≠ v₀ → kaehlerResidueTerm ω (diagonalHom K F f) v = 0)
    (hv₀ : kaehlerResidueTerm ω (diagonalHom K F f) v₀ = 0) :
    f ∈ kaehlerResidueKernel K F hω := by
  refine mem_kaehlerResidueKernel_of_term_zero_compl hω (T := {v₀}) ?_ ?_
  · intro v hv
    exact hcompl v (by simpa using hv)
  · simpa using hv₀

theorem mem_kaehlerResidueKernel_of_pair {ω : Ω[F⁄K]} (hω : ω ≠ 0) {f : F}
    {v₀ v₁ : Place K F} (hne : v₀ ≠ v₁)
    (hcompl : ∀ v, v ≠ v₀ → v ≠ v₁ → kaehlerResidueTerm ω (diagonalHom K F f) v = 0)
    (hsum : kaehlerResidueTerm ω (diagonalHom K F f) v₀
      + kaehlerResidueTerm ω (diagonalHom K F f) v₁ = 0) :
    f ∈ kaehlerResidueKernel K F hω := by
  classical
  refine mem_kaehlerResidueKernel_of_term_zero_compl hω (T := {v₀, v₁}) ?_ ?_
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
    exact hcompl v hv.1 hv.2
  · rw [Finset.sum_pair hne]; exact hsum

end KernelFinsum

section P1PolynomialSubrows

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]

/-- Vanishing of the residue at `∞` on the polynomial generators. -/
def P1PolynomialResidueAtInfinity {ω₀ : Ω[(RatFunc K)⁄K]} (_hω₀ : ω₀ ≠ 0) : Prop :=
  ∀ n : ℕ, kaehlerResidueTerm ω₀
    (diagonalHom K (RatFunc K) ((RatFunc.X : RatFunc K) ^ n)) (placeInfty K) = 0

variable {K}

theorem p1ResiduePolynomialPart_of_subrows {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0)
    (hreg : P1DifferentialCoeffRegularFinite K hω₀)
    (hinf : P1PolynomialResidueAtInfinity K hω₀) :
    P1ResiduePolynomialPart K hω₀ := by
  rintro _ ⟨n, rfl⟩
  refine mem_kaehlerResidueKernel_of_singleton hω₀ (v₀ := placeInfty K) ?_ (hinf n)
  intro v hv
  refine kaehlerResidueTerm_eq_zero_of_ord_nonneg ?_
  rw [diagonalHom_apply]
  exact Or.inr (v.ord_nonneg_of_mem (pow_X_mul_mem_of_ne_placeInfty K hv n (hreg v hv)))

end P1PolynomialSubrows

section P1PrincipalPartSubrows

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]

/-- Off-support vanishing of the principal-part atom's residue. -/
def P1PrincipalPartTermZeroOffSupport {ω₀ : Ω[(RatFunc K)⁄K]} (_hω₀ : ω₀ ≠ 0) : Prop :=
  ∀ (p c : K[X]) (m : ℕ) (_ : p.Monic) (hpirr : Irreducible p), c.degree < p.degree → 1 ≤ m →
    ∀ v : Place K (RatFunc K), v ≠ finitePlace K hpirr → v ≠ placeInfty K →
      kaehlerResidueTerm ω₀
        (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c m)) v = 0

/-- The two-place cancellation of the principal-part atom's residue. -/
def P1PrincipalPartTwoPlaceCancel {ω₀ : Ω[(RatFunc K)⁄K]} (_hω₀ : ω₀ ≠ 0) : Prop :=
  ∀ (p c : K[X]) (m : ℕ) (_ : p.Monic) (hpirr : Irreducible p), c.degree < p.degree → 1 ≤ m →
    kaehlerResidueTerm ω₀ (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c m))
        (finitePlace K hpirr)
      + kaehlerResidueTerm ω₀ (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c m))
          (placeInfty K)
      = 0

variable {K}

theorem p1ResiduePrincipalPart_of_subrows {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0)
    (hoff : P1PrincipalPartTermZeroOffSupport K hω₀)
    (hcancel : P1PrincipalPartTwoPlaceCancel K hω₀) :
    P1ResiduePrincipalPart K hω₀ := by
  rintro _ ⟨p, c, m, hpmon, hpirr, hdeg, hm, rfl⟩
  exact mem_kaehlerResidueKernel_of_pair hω₀ (finitePlace_ne_placeInfty hpirr)
    (hoff p c m hpmon hpirr hdeg hm) (hcancel p c m hpmon hpirr hdeg hm)

end P1PrincipalPartSubrows

section P1Composed

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]

theorem residueTheorem_ratFunc_of_four_subrows
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0)
    (hreg : P1DifferentialCoeffRegularFinite K hω₀)
    (hinf : P1PolynomialResidueAtInfinity K hω₀)
    (hoff : P1PrincipalPartTermZeroOffSupport K hω₀)
    (hcancel : P1PrincipalPartTwoPlaceCancel K hω₀) :
    ResidueTheorem K (RatFunc K) :=
  residueTheorem_ratFunc_of_generators_residue (placeInfty K) hω₀
    (p1ResiduePolynomialPart_of_subrows hω₀ hreg hinf)
    (p1ResiduePrincipalPart_of_subrows hω₀ hoff hcancel)

end P1Composed

section P1Reduction

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]

theorem p1PrincipalPartTermZeroOffSupport_of_differentialCoeffRegularFinite
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0)
    (hreg : P1DifferentialCoeffRegularFinite K hω₀) :
    P1PrincipalPartTermZeroOffSupport K hω₀ := by
  intro p c m _hpmon hpirr _hdeg _hm v hvp hvinf
  refine kaehlerResidueTerm_eq_zero_of_ord_nonneg ?_
  rw [diagonalHom_apply]
  exact Or.inr (v.ord_nonneg_of_mem
    (mul_mem (p1PrincipalPartAtom_mem_of_ne_finitePlace K hpirr c m hvp hvinf) (hreg v hvinf)))

theorem residueTheorem_ratFunc_of_three_subrows
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0)
    (hreg : P1DifferentialCoeffRegularFinite K hω₀)
    (hinf : P1PolynomialResidueAtInfinity K hω₀)
    (hcancel : P1PrincipalPartTwoPlaceCancel K hω₀) :
    ResidueTheorem K (RatFunc K) :=
  residueTheorem_ratFunc_of_four_subrows hω₀ hreg hinf
    (p1PrincipalPartTermZeroOffSupport_of_differentialCoeffRegularFinite K hω₀ hreg) hcancel

end P1Reduction

section NamedSubrows

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]

/-- The order of `dX` at `∞` is `-2`. -/
def P1OrdDifferentialPlaceInftyEqNegTwo {ω₀ : Ω[(RatFunc K)⁄K]} (_hω₀ : ω₀ ≠ 0) : Prop :=
  (placeInfty K).ordDifferential ω₀ = -2

end NamedSubrows

section InftyVanish

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]

theorem kaehlerResidueTerm_placeInfty_eq_zero_of_two_le_m
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0)
    (hInfty : P1OrdDifferentialPlaceInftyEqNegTwo K hω₀)
    {p : K[X]} (hp : Irreducible p) (c : K[X]) {m : ℕ}
    (hdeg : c.degree < p.degree) (hm : 2 ≤ m) :
    kaehlerResidueTerm ω₀ (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c m))
      (placeInfty K) = 0 := by
  refine kaehlerResidueTerm_eq_zero_of_ord_nonneg ?_
  rw [diagonalHom_apply]
  rcases eq_or_ne c 0 with rfl | hc
  · left
    show algebraMap K[X] (RatFunc K) 0 / (algebraMap K[X] (RatFunc K) p) ^ m
        * (placeInfty K).differentialCoeff ω₀ = 0
    rw [map_zero, zero_div, zero_mul]
  · right
    have hatom0 : p1PrincipalPartAtom K p c m ≠ 0 := by
      simp only [p1PrincipalPartAtom, ne_eq, div_eq_zero_iff, not_or]
      exact ⟨(map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hc,
        pow_ne_zero _ ((map_ne_zero_iff _
          (IsFractionRing.injective K[X] (RatFunc K))).mpr hp.ne_zero)⟩
    have hd0 : (placeInfty K).differentialCoeff ω₀ ≠ 0 :=
      (placeInfty K).differentialCoeff_ne_zero hω₀
    rw [(placeInfty K).ord_mul hatom0 hd0]
    have h2 : 2 ≤ (placeInfty K).ord (p1PrincipalPartAtom K p c m) :=
      two_le_ord_placeInfty_p1PrincipalPartAtom K hp hc hdeg hm
    have hordD : (placeInfty K).ord ((placeInfty K).differentialCoeff ω₀) = -2 := hInfty
    omega

end InftyVanish

section NamedSubrow

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]

/-- Finite-place vanishing of the principal-part atom for `2 ≤ m`. -/
def P1FinitePlaceTermZeroMGeTwo {ω₀ : Ω[(RatFunc K)⁄K]} (_hω₀ : ω₀ ≠ 0) : Prop :=
  ∀ (p c : K[X]) (m : ℕ) (_ : p.Monic) (hpirr : Irreducible p), c.degree < p.degree → 2 ≤ m →
    kaehlerResidueTerm ω₀ (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c m))
      (finitePlace K hpirr) = 0

end NamedSubrow

section MOneReduction

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]

theorem p1PrincipalPartTwoPlaceCancel_of_mOne
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0)
    (hMOne : P1PrincipalPartTwoPlaceCancelMOne K hω₀)
    (hMGeTwo : P1FinitePlaceTermZeroMGeTwo K hω₀)
    (hInfty : P1OrdDifferentialPlaceInftyEqNegTwo K hω₀) :
    P1PrincipalPartTwoPlaceCancel K hω₀ := by
  intro p c m hpmon hpirr hdeg hm
  rcases Nat.lt_or_ge m 2 with h1 | h2
  ·
    obtain rfl : m = 1 := by omega
    exact hMOne p c hpmon hpirr hdeg
  ·
    rw [hMGeTwo p c m hpmon hpirr hdeg h2,
      kaehlerResidueTerm_placeInfty_eq_zero_of_two_le_m K hω₀ hInfty hpirr c hdeg h2, add_zero]

end MOneReduction

section PerfectDCoord

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

/-- The pin's `D_ratFuncX_ne_zero` is stated with the
`OrdDifferentialWellDefined` hypothesis (the port's `P1/DivPow.lean` copy, in
`P1Tower`, is the hypothesis-free variant). -/
theorem D_ratFuncX_ne_zero (hwd : OrdDifferentialWellDefined K (RatFunc K)) :
    KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K) ≠ 0 := by
  rw [D_ratFuncX_eq_neg_X_sq_smul_D_inv K, smul_ne_zero_iff]
  exact ⟨neg_ne_zero.mpr (pow_ne_zero 2 RatFunc.X_ne_zero), D_ratFuncX_inv_ne_zero K hwd⟩

end PerfectDCoord

section OrdDifferential

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

theorem p1OrdDifferentialPlaceInftyEqNegTwo_D_X
    [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
    [HasPrincipalDivisors K (RatFunc K)]
    (hwd : OrdDifferentialWellDefined K (RatFunc K)) :
    P1OrdDifferentialPlaceInftyEqNegTwo K (D_ratFuncX_ne_zero K hwd) :=
  ordDifferential_placeInfty_D_ratFuncX K hwd

end OrdDifferential

section MOneSplit

variable (K : Type*) [Field K] [CharZero K] [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]

omit [CharZero K] in

theorem p1PrincipalPartTwoPlaceCancel_dX_of_mOne_mGeTwo
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    (hMOne : P1PrincipalPartTwoPlaceCancelMOne K (dX_ne_zero K))
    (hMGeTwo : P1FinitePlaceTermZeroMGeTwo K (dX_ne_zero K)) :
    P1PrincipalPartTwoPlaceCancel K (dX_ne_zero K) :=
  p1PrincipalPartTwoPlaceCancel_of_mOne (dX_ne_zero K) hMOne hMGeTwo
    (p1OrdDifferentialPlaceInftyEqNegTwo_D_X K hwd)

end MOneSplit

section PerfectSubrows

variable (K : Type*) [Field K] [PerfectField K] [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)] [HasPrincipalDivisors K (RatFunc K)]

theorem residueTheorem_ratFunc_of_two_subrows_of_perfectField
    (hinf : P1PolynomialResidueAtInfinity K (dX_ne_zero K))
    (hcancel : P1PrincipalPartTwoPlaceCancel K (dX_ne_zero K)) :
    ResidueTheorem K (RatFunc K) :=
  residueTheorem_ratFunc_of_three_subrows K (dX_ne_zero K)
    (p1DifferentialCoeffRegularFinite_dX_of_perfectField K) hinf hcancel

theorem p1PrincipalPartTwoPlaceCancel_dX_of_mOne_mGeTwo_of_perfectField
    (hMOne : P1PrincipalPartTwoPlaceCancelMOne K (dX_ne_zero K))
    (hMGeTwo : P1FinitePlaceTermZeroMGeTwo K (dX_ne_zero K)) :
    P1PrincipalPartTwoPlaceCancel K (dX_ne_zero K) :=
  p1PrincipalPartTwoPlaceCancel_dX_of_mOne_mGeTwo K
    (ordDifferentialWellDefined_ratFunc_of_perfectField K) hMOne hMGeTwo

end PerfectSubrows

section Headline

/-- The ℙ¹ residue theorem over a perfect field, at the pin wrapper's binders. -/
theorem residueTheorem_ratFunc_of_perfectField
    (K : Type*) [Field K] [PerfectField K] [DecidableEq (RatFunc K)]
    [AlgebraicCurve.IsCurveOver K (RatFunc K)]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := RatFunc K)]
    [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates]
    [Nontrivial Ω[(RatFunc K)⁄K]] :
    AlgebraicCurve.ResidueTheorem K (RatFunc K) := by
  have hinf : P1PolynomialResidueAtInfinity K (dX_ne_zero K) := by
    intro n
    simp only [kaehlerResidueTerm, diagonalHom_apply]
    exact RationalFunctionField.trace_localResidue_placeInfty_X_pow_eq_zero K n
  have hMOne : P1PrincipalPartTwoPlaceCancelMOne K (dX_ne_zero K) := by
    intro p c hmon hpirr hdeg
    simp only [kaehlerResidueTerm, diagonalHom_apply, p1PrincipalPartAtom, pow_one]
    exact RationalFunctionField.trace_localResidue_finitePlace_add_trace_localResidue_placeInfty_eq_zero
      K hmon hpirr hdeg
  have hMGeTwo : P1FinitePlaceTermZeroMGeTwo K (dX_ne_zero K) := by
    intro p c m hmon hpirr hdeg hm
    simp only [kaehlerResidueTerm, diagonalHom_apply, p1PrincipalPartAtom]
    exact RationalFunctionField.trace_localResidue_finitePlace_div_pow_eq_zero K hmon hpirr hdeg hm
  intro _ ω hω f
  exact residueTheorem_ratFunc_of_two_subrows_of_perfectField K hinf
    (p1PrincipalPartTwoPlaceCancel_dX_of_mOne_mGeTwo_of_perfectField K hMOne hMGeTwo) hω f

end Headline

end AlgebraicCurve
