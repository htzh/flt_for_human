/-
The ℙ¹ residue core, chunk 1: declarations #0–#144 of FLT's master ℙ¹ file

`P2M/Sol/S_AlgebraicCurve_RationalFunctionField_trace_localResidue_placeInfty_X_pow_eq_zero.lean`
(pin lines 295–3387; 580 declarations in the file)
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_trace_localResidue_placeInfty_X_pow_eq_zero.lean#L295-L3387>

Set 3.2b of phase 3 (row 2 of `topics/PORTING-RR.md` §3). Later sets 3.2c–e
append to this same module, so the pin's names and namespaces are kept verbatim
and the landing order is not restructured.

Contents: the `FLT.EulerDualBasis` power-basis trace prelude,
`AlgebraicCurve.OrdDifferentialWellDefined`, the `Place`/`RationalFunctionField`
ord-valuation prelude, the `ValSubringKaehler*` model predicates, the
`principalAdele`/`P1*Generators` block, the finite-residue instances, the
`p1PrincipalPartAtom`/partial-fraction block and the residue gates.

Already-ported declarations are imported rather than re-proved: the
`ModularCurve.Lg37`/`Mp72a102T1`/`T2`/`T3` engine, the `uniformizerSubring`/
`simplePoleSubmodule`/`poleSubmodule`/`laurentTailCoeff` layer, the promoted ord
interface and the ℙ¹ dictionary (`Defs/{PushPull,P1Dictionary,RatFuncPlaces,
CanonicalLocalResidueInstanceV2,PlacesOverDVR}.lean`,
`PrincipalDivisors/{RatFuncDegree,Transcendence}.lean`,
`Canonical/HasCanonicalDivisor.lean`). The pin's `p1PlaceInfty` is the port's
`placeInfty` re-exported at the pin name (`@[reducible]`), so every pin statement
below lands verbatim. Pin-private helpers stay `private`; the pin's
`p2m_*`/`attribute` scaffolding is dropped.
-/
import FLTForHuman.AlgebraicCurve.Defs.P1Dictionary
import FLTForHuman.AlgebraicCurve.Defs.CanonicalLocalResidueInstanceV2
import FLTForHuman.AlgebraicCurve.Defs.LocalResidueCalculus
import FLTForHuman.AlgebraicCurve.Canonical.HasCanonicalDivisor
import FLTForHuman.AlgebraicCurve.PrincipalDivisors.Transcendence
import FLTForHuman.AlgebraicCurve.Defs.PlacesOverDVR
import Mathlib.RingTheory.PowerBasis
import Mathlib.FieldTheory.Minpoly.MinpolyDiv
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Algebra.BigOperators.Field

noncomputable section

open Polynomial IsDedekindDomain WithZero IsLocalRing UniqueFactorizationMonoid

namespace FLT
namespace EulerDualBasis

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]

omit [FiniteDimensional K L] [Algebra.IsSeparable K L] in
theorem coeff_minpolyDiv_dim_sub_one (pb : PowerBasis K L) :
    (minpolyDiv K pb.gen).coeff (pb.dim - 1) = 1 := by
  have h1 : (minpolyDiv K pb.gen).natDegree = pb.dim - 1 := by
    rw [natDegree_minpolyDiv, pb.natDegree_minpoly]
  rw [← h1]
  exact (minpolyDiv_monic pb.isIntegral_gen).coeff_natDegree

theorem traceDual_eq_one_div_of_val_eq (pb : PowerBasis K L) {j : Fin pb.dim}
    (hj : (j : ℕ) = pb.dim - 1) :
    pb.basis.traceDual j = 1 / aeval pb.gen (derivative (minpoly K pb.gen)) := by
  rw [Module.Basis.traceDual_powerBasis_eq]
  rw [hj, coeff_minpolyDiv_dim_sub_one]

theorem trace_pow_div_aeval_derivative_minpoly_of_lt (pb : PowerBasis K L) {k : ℕ}
    (hk : k < pb.dim - 1) :
    Algebra.trace K L
      (pb.gen ^ k / aeval pb.gen (derivative (minpoly K pb.gen))) = 0 := by
  have hd : 0 < pb.dim := by omega
  have hk' : k < pb.dim := by omega
  have hlt : pb.dim - 1 < pb.dim := by omega
  have key := pb.basis.trace_mul_traceDual ⟨k, hk'⟩ ⟨pb.dim - 1, hlt⟩
  rw [traceDual_eq_one_div_of_val_eq pb rfl, pb.basis_eq_pow, mul_one_div] at key
  rw [key, if_neg]
  simp only [Fin.mk.injEq]
  omega

theorem trace_pow_div_aeval_derivative_minpoly_self (pb : PowerBasis K L)
    (hd : 0 < pb.dim) :
    Algebra.trace K L
      (pb.gen ^ (pb.dim - 1) / aeval pb.gen (derivative (minpoly K pb.gen))) = 1 := by
  have hlt : pb.dim - 1 < pb.dim := by omega
  have key := pb.basis.trace_mul_traceDual ⟨pb.dim - 1, hlt⟩ ⟨pb.dim - 1, hlt⟩
  rw [traceDual_eq_one_div_of_val_eq pb rfl, pb.basis_eq_pow, mul_one_div] at key
  rw [key, if_pos rfl]

variable {F : Type*} [Field F] [CharZero F] {g : F[X]} [Fact (Irreducible g)]

theorem trace_root_pow_div_derivative_of_lt (hg : g.Monic) {k : ℕ}
    (hk : k < g.natDegree - 1) :
    Algebra.trace F (AdjoinRoot g)
      (AdjoinRoot.root g ^ k / aeval (AdjoinRoot.root g) (derivative g)) = 0 := by
  haveI : FiniteDimensional F (AdjoinRoot g) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hg.ne_zero).basis
  have hmin : minpoly F (AdjoinRoot.powerBasis hg.ne_zero).gen = g :=
    AdjoinRoot.minpoly_powerBasis_gen_of_monic hg
  have h := trace_pow_div_aeval_derivative_minpoly_of_lt
    (AdjoinRoot.powerBasis hg.ne_zero) (k := k)
    (by rwa [AdjoinRoot.powerBasis_dim])
  rwa [hmin, AdjoinRoot.powerBasis_gen] at h

theorem trace_root_pow_div_derivative_self (hg : g.Monic) (hd : 0 < g.natDegree) :
    Algebra.trace F (AdjoinRoot g)
      (AdjoinRoot.root g ^ (g.natDegree - 1) /
        aeval (AdjoinRoot.root g) (derivative g)) = 1 := by
  haveI : FiniteDimensional F (AdjoinRoot g) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hg.ne_zero).basis
  have hmin : minpoly F (AdjoinRoot.powerBasis hg.ne_zero).gen = g :=
    AdjoinRoot.minpoly_powerBasis_gen_of_monic hg
  have h := trace_pow_div_aeval_derivative_minpoly_self
    (AdjoinRoot.powerBasis hg.ne_zero)
    (by rwa [AdjoinRoot.powerBasis_dim])
  rwa [hmin, AdjoinRoot.powerBasis_gen, AdjoinRoot.powerBasis_dim] at h

end FLT.EulerDualBasis

namespace AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

def OrdDifferentialWellDefined : Prop :=
  ∀ (v : Place K F) (π π' : F), v.ord π = 1 → v.ord π' = 1 →
    ∃ u : F, v.ord u = 0 ∧
      KaehlerDifferential.D K F π' = u • KaehlerDifferential.D K F π

variable {K F}

namespace Place

variable (v : Place K F)

private theorem ord_add_eq_min {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (h : v.ord f ≠ v.ord g) :
    v.ord (f + g) = min (v.ord f) (v.ord g) := by
  have hval : v.adicValuation f ≠ v.adicValuation g := by
    intro hcon
    exact h (by simp only [ord, hcon])
  have h1 : v.adicValuation (f + g) = max (v.adicValuation f) (v.adicValuation g) :=
    Valuation.map_add_of_distinct_val _ hval
  have hfg : f + g ≠ 0 := by
    intro hcon
    rw [hcon, _root_.map_zero] at h1
    rcases max_cases (v.adicValuation f) (v.adicValuation g) with ⟨hmax, -⟩ | ⟨hmax, -⟩ <;>
      rw [hmax] at h1
    · exact v.adicValuation_ne_zero hf h1.symm
    · exact v.adicValuation_ne_zero hg h1.symm
  rcases max_cases (v.adicValuation f) (v.adicValuation g) with ⟨hmax, hle⟩ | ⟨hmax, hlt⟩ <;>
    rw [hmax] at h1
  ·
    have hlog := (WithZero.log_le_log (v.adicValuation_ne_zero hg)
      (v.adicValuation_ne_zero hf)).mpr hle
    have h2 : v.ord (f + g) = v.ord f := by simp only [ord, h1]
    simp only [ord] at hlog h2 ⊢
    omega
  · have hlog := (WithZero.log_le_log (v.adicValuation_ne_zero hf)
      (v.adicValuation_ne_zero hg)).mpr hlt.le
    have h2 : v.ord (f + g) = v.ord g := by simp only [ord, h1]
    simp only [ord] at hlog h2 ⊢
    omega

section RestrictPrelude

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F'] [Algebra F F']

private theorem algebraMap_ne_zero {f : F} (hf : f ≠ 0) : algebraMap F F' f ≠ 0 := by
  simpa using hf

variable (w : Place K F')

variable {w} in

theorem isUnit_mk_comap_iff {f : F} (hf : f ≠ 0)
    (hmem : f ∈ w.toValuationSubring.comap (algebraMap F F')) :
    IsUnit (⟨f, hmem⟩ : w.toValuationSubring.comap (algebraMap F F')) ↔
      w.ord (algebraMap F F' f) = 0 := by
  constructor
  · rintro h
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp h
    have hb' : f * (b : F) = 1 := by
      simpa [Subtype.ext_iff] using hb
    have hbne : (b : F) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hb'
      exact zero_ne_one hb'
    have hsum : w.ord (algebraMap F F' f) + w.ord (algebraMap F F' (b : F)) = 0 := by
      rw [← w.ord_mul (algebraMap_ne_zero hf) (algebraMap_ne_zero hbne), ← map_mul, hb',
        map_one, w.ord_one]
    have h1 : 0 ≤ w.ord (algebraMap F F' f) := (mem_comap_iff_ord_nonneg hf).mp hmem
    have h2 : 0 ≤ w.ord (algebraMap F F' (b : F)) := (mem_comap_iff_ord_nonneg hbne).mp b.2
    omega
  · intro h0
    have hinv : f⁻¹ ∈ w.toValuationSubring.comap (algebraMap F F') :=
      (mem_comap_iff_ord_nonneg (inv_ne_zero hf)).mpr (by rw [map_inv₀, w.ord_inv]; omega)
    exact ⟨⟨⟨f, hmem⟩, ⟨f⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hf),
      Subtype.ext (inv_mul_cancel₀ hf)⟩, rfl⟩

variable [Algebra.IsIntegral F F']

theorem isPrincipalIdealRing_comap :
    IsPrincipalIdealRing (w.toValuationSubring.comap (algebraMap F F')) := by
  obtain ⟨g, hg0, hge⟩ := w.exists_ord_eq_ramificationIndex (F := F)
  have hepos : 0 < ramificationIndex (F := F) w := w.ramificationIndex_pos (F := F)
  have hgmem : g ∈ w.toValuationSubring.comap (algebraMap F F') :=
    (mem_comap_iff_ord_nonneg hg0).mpr (by omega)
  refine (IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨⟨g, hgmem⟩, irreducible_mk_comap w hg0 hgmem hge, ?_⟩).toIsPrincipalIdealRing
  rintro ⟨f, hmem⟩ hx
  have hf : f ≠ 0 := by simpa [Subtype.ext_iff] using hx

  obtain ⟨c, hc⟩ := w.ramificationIndex_dvd_ord (F := F) hf
  have hnonneg : 0 ≤ w.ord (algebraMap F F' f) := (mem_comap_iff_ord_nonneg hf).mp hmem
  have hcnonneg : 0 ≤ c := by
    by_contra hneg
    have hcle : c ≤ -1 := by omega
    have : (ramificationIndex (F := F) w : ℤ) * c ≤ (ramificationIndex (F := F) w : ℤ) * -1 :=
      mul_le_mul_of_nonneg_left hcle (by omega)
    omega
  set n : ℕ := c.toNat with hn
  have hcn : (n : ℤ) = c := Int.toNat_of_nonneg hcnonneg
  refine ⟨n, ?_⟩

  have hgn : g ^ n ≠ 0 := pow_ne_zero _ hg0
  have hdiv0 : f / g ^ n ≠ 0 := div_ne_zero hf hgn
  have hu0 : w.ord (algebraMap F F' (f / g ^ n)) = 0 := by
    have hkey : algebraMap F F' (f / g ^ n)
        = algebraMap F F' f * (algebraMap F F' g) ^ (-(n : ℤ)) := by
      rw [div_eq_mul_inv, map_mul, map_inv₀, map_pow, ← zpow_natCast (algebraMap F F' g) n,
        ← _root_.zpow_neg]
    rw [hkey, w.ord_mul (algebraMap_ne_zero hf) (zpow_ne_zero _ (algebraMap_ne_zero hg0)),
      w.ord_zpow, hge, hc, ← hcn]
    ring
  have humem : f / g ^ n ∈ w.toValuationSubring.comap (algebraMap F F') :=
    (mem_comap_iff_ord_nonneg hdiv0).mpr (le_of_eq hu0.symm)
  have hu : IsUnit (⟨f / g ^ n, humem⟩ : w.toValuationSubring.comap (algebraMap F F')) :=
    (isUnit_mk_comap_iff hdiv0 humem).mpr hu0
  refine ⟨hu.unit, ?_⟩
  refine Subtype.ext ?_
  have hcoe : ((hu.unit : w.toValuationSubring.comap (algebraMap F F')) : F) = f / g ^ n := by
    rw [IsUnit.unit_spec]
  push_cast
  rw [hcoe, mul_comm, div_mul_cancel₀]
  exact hgn

end RestrictPrelude

section Ultrametric

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem ord_add_eq_left {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (h : v.ord f < v.ord g) :
    v.ord (f + g) = v.ord f := by

  have hfv := v.adicValuation_ne_zero hf
  have hgv := v.adicValuation_ne_zero hg
  have hlt : v.adicValuation g < v.adicValuation f := by
    rw [← exp_log hfv, ← exp_log hgv]
    have hlog : log (v.adicValuation g) < log (v.adicValuation f) := by
      simp only [ord] at h
      omega
    exact lt_of_le_of_ne (exp_le_exp.mpr hlog.le)
      fun hcon => hlog.ne (exp_injective hcon)
  have h1 : v.adicValuation (f + g) = max (v.adicValuation f) (v.adicValuation g) :=
    Valuation.map_add_of_distinct_val _ (ne_of_lt hlt).symm
  rw [max_eq_left hlt.le] at h1
  simp only [ord, h1]

end Ultrametric

end Place

namespace RationalFunctionField

variable (K : Type*) [Field K]

section PlaceInfty

variable [DecidableEq (RatFunc K)]

@[reducible] def p1PlaceInfty : Place K (RatFunc K) := placeInfty K

@[scoped simp]
theorem p1PlaceInfty_toValuationSubring :
    (p1PlaceInfty K).toValuationSubring = (RatFunc.inftyValuation K).valuationSubring := rfl

theorem p1PlaceInfty_ne_ofHeightOneSpectrum (w : HeightOneSpectrum K[X]) :
    p1PlaceInfty K ≠ Place.ofHeightOneSpectrum w :=
  placeInfty_ne_ofHeightOneSpectrum K w

end PlaceInfty

variable {K}

theorem finite_setOf_valuation_ne_one {f : RatFunc K} (hf : f ≠ 0) :
    {w : HeightOneSpectrum K[X] | w.valuation (RatFunc K) f ≠ 1}.Finite := by
  have hnum : (Ideal.span {f.num} : Ideal K[X]) ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using RatFunc.num_ne_zero hf
  have hden : (Ideal.span {f.denom} : Ideal K[X]) ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using f.denom_ne_zero
  refine Set.Finite.subset ((Ideal.finite_factors hnum).union (Ideal.finite_factors hden))
    fun w hw => ?_
  by_contra hcon
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, Ideal.dvd_span_singleton] at hcon
  refine hw ?_
  have h1 : w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) f.num) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem w).mpr hcon.1
  have h2 : w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) f.denom) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem w).mpr hcon.2
  rw [show f = algebraMap K[X] (RatFunc K) f.num / algebraMap K[X] (RatFunc K) f.denom from
    f.num_div_denom.symm, map_div₀, h1, h2]
  exact div_one 1

end RationalFunctionField

section EnginePrelude

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

omit [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)] [Nontrivial Ω[F⁄K]] in
theorem exists_smul_eq_of_ne_zero (v : Place K F) {ω ω₀ : Ω[F⁄K]}
    (hω : ω ≠ 0) (hω₀ : ω₀ ≠ 0) : ∃ g : F, g ≠ 0 ∧ ω = g • ω₀ := by
  set a := v.differentialCoeff ω with ha
  set b := v.differentialCoeff ω₀ with hb
  have h0 : b ≠ 0 := v.differentialCoeff_ne_zero hω₀
  refine ⟨a * b⁻¹, mul_ne_zero (v.differentialCoeff_ne_zero hω) (inv_ne_zero h0), ?_⟩
  have hω₀eq : ω₀ = b • v.dCoord := hb ▸ (v.differentialCoeff_smul_dCoord ω₀).symm
  rw [hω₀eq, smul_smul, mul_assoc, inv_mul_cancel₀ h0, mul_one]
  exact ha ▸ (v.differentialCoeff_smul_dCoord ω).symm

variable [HasPrincipalDivisors K F]

variable (K F) in
def principalAdele : F →ₗ[K] adeleSpace K F where
  toFun f := ⟨diagonalHom K F f, diagonal_mem_adeleSpace f⟩
  map_add' f g := Subtype.ext ((diagonalHom K F).map_add f g)
  map_smul' c f := Subtype.ext ((diagonalHom K F).map_smul c f)

end EnginePrelude

section P1NamedRows

variable (K : Type*) [Field K]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]

def P1PolynomialGenerators : Set (RatFunc K) := Set.range fun n : ℕ => RatFunc.X ^ n

def P1PrincipalPartGenerators : Set (RatFunc K) :=
  {f | ∃ (p c : K[X]) (m : ℕ), p.Monic ∧ Irreducible p ∧ c.degree < p.degree ∧ 1 ≤ m ∧
    f = algebraMap K[X] (RatFunc K) c / (algebraMap K[X] (RatFunc K) p) ^ m}

def P1PartialFractionGenerators : Set (RatFunc K) :=
  P1PolynomialGenerators K ∪ P1PrincipalPartGenerators K

variable {K}

end P1NamedRows

section P1Gates

variable {K : Type*} [Field K]

theorem gate_algebraMap_polynomial_mem_span_P1PolynomialGenerators (q : K[X]) :
    algebraMap K[X] (RatFunc K) q ∈ Submodule.span K (P1PolynomialGenerators K) := by

  rw [← Polynomial.sum_C_mul_X_pow_eq q, Polynomial.sum, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_mul, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X,
    ← RatFunc.smul_eq_C_mul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end P1Gates

namespace RationalFunctionField

variable (K : Type*) [Field K]

scoped instance instFiniteResidueOfHeightOneSpectrum (w : HeightOneSpectrum K[X]) :
    (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).FiniteResidue := by
  obtain ⟨p, hp, hw⟩ := exists_irreducible_span K w
  refine Place.finiteResidue_of_deg_pos _ ?_
  rw [deg_ofHeightOneSpectrum K hw]
  exact hp.natDegree_pos

scoped instance instFiniteResiduePlaceInfty [DecidableEq (RatFunc K)] :
    (p1PlaceInfty K).FiniteResidue :=
  Place.finiteResidue_of_deg_pos _ (by rw [deg_placeInfty K]; exact one_pos)

variable {K} in

scoped instance instFiniteResidue (v : Place K (RatFunc K)) : v.FiniteResidue := by
  classical
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  · exact instFiniteResidueOfHeightOneSpectrum K w
  · exact instFiniteResiduePlaceInfty K

end RationalFunctionField

section RatFuncIntegrality

open RationalFunctionField

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]

theorem algebraMap_polynomial_mem_of_ne_placeInfty'
    {v : Place K (RatFunc K)} (hv : v ≠ p1PlaceInfty K) (q : K[X]) :
    algebraMap K[X] (RatFunc K) q ∈ v.toValuationSubring := by
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  · exact RationalFunctionField.algebraMap_mem_ofHeightOneSpectrum K w q
  · exact absurd rfl hv

theorem pow_X_mem_of_ne_placeInfty
    {v : Place K (RatFunc K)} (hv : v ≠ p1PlaceInfty K) (n : ℕ) :
    (RatFunc.X : RatFunc K) ^ n ∈ v.toValuationSubring := by
  have h : algebraMap K[X] (RatFunc K) (Polynomial.X ^ n) ∈ v.toValuationSubring :=
    algebraMap_polynomial_mem_of_ne_placeInfty' K hv (Polynomial.X ^ n)
  rwa [map_pow, RatFunc.algebraMap_X] at h

theorem pow_X_mul_mem_of_ne_placeInfty
    {v : Place K (RatFunc K)} (hv : v ≠ p1PlaceInfty K) (n : ℕ)
    {g : RatFunc K} (hg : g ∈ v.toValuationSubring) :
    (RatFunc.X : RatFunc K) ^ n * g ∈ v.toValuationSubring :=
  mul_mem (pow_X_mem_of_ne_placeInfty K hv n) hg

end RatFuncIntegrality

section P1PolynomialSubrows

open RationalFunctionField

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]

def P1DifferentialCoeffRegularFinite {ω₀ : Ω[(RatFunc K)⁄K]} (_hω₀ : ω₀ ≠ 0) : Prop :=
  ∀ v : Place K (RatFunc K), v ≠ p1PlaceInfty K →
    v.differentialCoeff ω₀ ∈ v.toValuationSubring

variable {K}

end P1PolynomialSubrows

section P1PrincipalPartSubrows

open RationalFunctionField

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]

abbrev p1PrincipalPartAtom (p c : K[X]) (m : ℕ) : RatFunc K :=
  algebraMap K[X] (RatFunc K) c / (algebraMap K[X] (RatFunc K) p) ^ m

variable {K}

omit [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
  [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
  [HasPrincipalDivisors K (RatFunc K)] in

theorem finitePlace_ne_placeInfty {p : K[X]} (hp : Irreducible p) :
    finitePlace K hp ≠ p1PlaceInfty K :=
  fun h => p1PlaceInfty_ne_ofHeightOneSpectrum K _ h.symm

end P1PrincipalPartSubrows

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_algebraMap_base (a : K) : v.ord (algebraMap K F a) = 0 := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have h1 : 0 ≤ v.ord (algebraMap K F a) := v.ord_nonneg_of_mem (v.algebraMap_mem' a)
  have h2 : 0 ≤ v.ord (algebraMap K F a)⁻¹ := by
    rw [← map_inv₀]
    exact v.ord_nonneg_of_mem (v.algebraMap_mem' a⁻¹)
  rw [v.ord_inv] at h2
  omega

end Place

namespace RationalFunctionField

variable (K : Type*) [Field K]

theorem exists_ord_finitePlace_eq_nsmul {p : K[X]} (hp : Irreducible p) {q : K[X]}
    (hq : q ≠ 0) :
    ∃ m : ℕ, (finitePlace K hp).ord (algebraMap K[X] (RatFunc K) q)
      = m * (finitePlace K hp).ord (algebraMap K[X] (RatFunc K) p) := by
  obtain ⟨m, b, hb, rfl⟩ := WfDvdMonoid.max_power_factor hq hp
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hp0 : p ≠ 0 := hp.ne_zero
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hq (mul_zero _)
  have hordb : (finitePlace K hp).ord (algebraMap K[X] (RatFunc K) b) = 0 := by
    by_contra hcon
    exact hb ((ord_finitePlace_ne_zero_iff K hp hb0).mp hcon)
  refine ⟨m, ?_⟩
  rw [map_mul, map_pow,
    (finitePlace K hp).ord_mul (pow_ne_zero _ ((map_ne_zero_iff _ hinj).mpr hp0))
      ((map_ne_zero_iff _ hinj).mpr hb0),
    hordb, add_zero, ← zpow_natCast, (finitePlace K hp).ord_zpow]

theorem ord_finitePlace_dvd {p : K[X]} (hp : Irreducible p) {f : RatFunc K} (hf : f ≠ 0) :
    (finitePlace K hp).ord (algebraMap K[X] (RatFunc K) p) ∣ (finitePlace K hp).ord f := by
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  obtain ⟨a, ha⟩ := exists_ord_finitePlace_eq_nsmul K hp (RatFunc.num_ne_zero hf)
  obtain ⟨b, hb⟩ := exists_ord_finitePlace_eq_nsmul K hp f.denom_ne_zero
  have hnum' : algebraMap K[X] (RatFunc K) f.num ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr (RatFunc.num_ne_zero hf)
  have hden' : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr f.denom_ne_zero
  rw [show f = algebraMap K[X] (RatFunc K) f.num * (algebraMap K[X] (RatFunc K) f.denom)⁻¹ by
      rw [← div_eq_mul_inv, f.num_div_denom],
    (finitePlace K hp).ord_mul hnum' (inv_ne_zero hden'), (finitePlace K hp).ord_inv, ha, hb]
  exact ⟨(a : ℤ) - b, by ring⟩

theorem ord_finitePlace_self {p : K[X]} (hp : Irreducible p) :
    (finitePlace K hp).ord (algebraMap K[X] (RatFunc K) p) = 1 := by

  have hnonneg : 0 ≤ (finitePlace K hp).ord (algebraMap K[X] (RatFunc K) p) :=
    (finitePlace K hp).ord_nonneg_of_mem (algebraMap_mem_ofHeightOneSpectrum K _ p)

  obtain ⟨π, hπ⟩ :=
    IsDiscreteValuationRing.exists_irreducible (finitePlace K hp).toValuationSubring
  have hπ0 : (π : RatFunc K) ≠ 0 := by
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  have hdvd : (finitePlace K hp).ord (algebraMap K[X] (RatFunc K) p) ∣ 1 :=
    (finitePlace K hp).ord_coe_irreducible hπ ▸ ord_finitePlace_dvd K hp hπ0
  rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd) with h | h
  · exact h
  · omega

section PlaceInfty

variable [DecidableEq (RatFunc K)]

theorem ord_placeInfty_eq_zero_of_intDegree_eq_zero {f : RatFunc K} (hf : f ≠ 0)
    (h : f.intDegree = 0) : (p1PlaceInfty K).ord f = 0 := by
  rw [(p1PlaceInfty K).ord_eq_zero_iff_adicValuation_eq_one hf,
    ← (inftyValuation_isEquiv_adicValuation K).eq_one_iff_eq_one,
    RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero K hf, h]
  rfl

theorem ord_placeInfty_eq_intDegree_mul {f : RatFunc K} (hf : f ≠ 0) :
    (p1PlaceInfty K).ord f = f.intDegree * (p1PlaceInfty K).ord (RatFunc.X) := by
  have hinj := IsFractionRing.injective K[X] (RatFunc K)

  have hpoly : ∀ q : K[X], q ≠ 0 →
      (p1PlaceInfty K).ord (algebraMap K[X] (RatFunc K) q)
        = (q.natDegree : ℤ) * (p1PlaceInfty K).ord (RatFunc.X) := by
    intro q hq
    have hq' : algebraMap K[X] (RatFunc K) q ≠ 0 := (map_ne_zero_iff _ hinj).mpr hq
    have hX : (RatFunc.X : RatFunc K) ≠ 0 := RatFunc.X_ne_zero
    have hXpow : (RatFunc.X : RatFunc K) ^ q.natDegree ≠ 0 := pow_ne_zero _ hX

    have hXpoly : (RatFunc.X : RatFunc K) ^ q.natDegree
        = algebraMap K[X] (RatFunc K) (Polynomial.X ^ q.natDegree) := by
      rw [map_pow, RatFunc.algebraMap_X]
    have hdeg : (algebraMap K[X] (RatFunc K) q / RatFunc.X ^ q.natDegree).intDegree = 0 := by
      rw [RatFunc.intDegree_div hq' hXpow, RatFunc.intDegree_polynomial, hXpoly,
        RatFunc.intDegree_polynomial, natDegree_X_pow, sub_self]
    have hne : algebraMap K[X] (RatFunc K) q / RatFunc.X ^ q.natDegree ≠ 0 :=
      div_ne_zero hq' hXpow
    have h0 := ord_placeInfty_eq_zero_of_intDegree_eq_zero K hne hdeg
    have hsplit : algebraMap K[X] (RatFunc K) q
        = (algebraMap K[X] (RatFunc K) q / RatFunc.X ^ q.natDegree)
          * RatFunc.X ^ q.natDegree :=
      (div_mul_cancel₀ _ hXpow).symm
    rw [hsplit, (p1PlaceInfty K).ord_mul hne hXpow, h0, zero_add, ← zpow_natCast,
      (p1PlaceInfty K).ord_zpow]
  have hnum' : algebraMap K[X] (RatFunc K) f.num ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr (RatFunc.num_ne_zero hf)
  have hden' : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr f.denom_ne_zero
  rw [show f = algebraMap K[X] (RatFunc K) f.num * (algebraMap K[X] (RatFunc K) f.denom)⁻¹ by
      rw [← div_eq_mul_inv, f.num_div_denom],
    (p1PlaceInfty K).ord_mul hnum' (inv_ne_zero hden'), (p1PlaceInfty K).ord_inv,
    hpoly _ (RatFunc.num_ne_zero hf), hpoly _ f.denom_ne_zero, ← div_eq_mul_inv,
    RatFunc.intDegree_div hnum' hden', RatFunc.intDegree_polynomial,
    RatFunc.intDegree_polynomial]
  ring

theorem ord_placeInfty_algebraMap' {q : K[X]} (hq : q ≠ 0) :
    (p1PlaceInfty K).ord (algebraMap K[X] (RatFunc K) q) = -(q.natDegree : ℤ) := by
  have hq' : algebraMap K[X] (RatFunc K) q ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hq
  rw [ord_placeInfty_eq_intDegree_mul K hq', ord_placeInfty_X, RatFunc.intDegree_polynomial]
  ring

end PlaceInfty

end RationalFunctionField

namespace Place

section SupportTransfer

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F'] [Algebra F F']
  [FiniteDimensional F F']

variable (w : Place K F')

omit [FiniteDimensional F F'] in
private theorem aeval_mem {Q : Polynomial F} {x : F'}
    (hcoeff : ∀ i, algebraMap F F' (Q.coeff i) ∈ w.toValuationSubring)
    (hx : x ∈ w.toValuationSubring) :
    Polynomial.aeval x Q ∈ w.toValuationSubring := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range]
  exact sum_mem fun i _ => mul_mem (hcoeff i) (pow_mem hx i)

private theorem exists_coeff_ord_ne_zero {f : F'} (hf : f ≠ 0) (hford : w.ord f ≠ 0) :
    ∃ i < (minpoly F f).natDegree, (minpoly F f).coeff i ≠ 0 ∧
      w.ord (algebraMap F F' ((minpoly F f).coeff i)) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  set P := minpoly F f with hPdef
  have hint : IsIntegral F f := Algebra.IsIntegral.isIntegral f
  have hmonic : P.Monic := minpoly.monic hint
  have hdeg : 0 < P.natDegree := minpoly.natDegree_pos hint
  have hc0 : P.coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hf

  have hcoeff : ∀ i, algebraMap F F' (P.coeff i) ∈ w.toValuationSubring := by
    intro i
    rcases lt_trichotomy i P.natDegree with hi | hi | hi
    · rcases eq_or_ne (P.coeff i) 0 with h0 | h0
      · simp [h0]
      · exact w.mem_of_ord_nonneg (by simpa using h0) (by have := hcon i hi h0; omega)
    · subst hi
      simp [hmonic.coeff_natDegree]
    · simp [Polynomial.coeff_eq_zero_of_natDegree_lt hi]

  have hfmem : f ∈ w.toValuationSubring := by
    refine w.mem_of_eval_monic_eq_zero (P := P.map (algebraMap F F')) (hmonic.map _)
      (fun i => by simpa using hcoeff i) ?_
    rw [Polynomial.eval_map, ← Polynomial.aeval_def, hPdef, minpoly.aeval]

  have hfpos : 0 < w.ord f := lt_of_le_of_ne (w.ord_nonneg_of_mem hfmem) (Ne.symm hford)

  have hkey : algebraMap F F' (P.coeff 0) = -(f * Polynomial.aeval f P.divX) := by
    have hsplit : Polynomial.aeval f (Polynomial.X * P.divX + Polynomial.C (P.coeff 0))
        = (0 : F') := by rw [P.X_mul_divX_add]; exact minpoly.aeval F f
    rw [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at hsplit
    linear_combination hsplit
  have hcof_mem : Polynomial.aeval f P.divX ∈ w.toValuationSubring :=
    aeval_mem (w := w) (fun i => by rw [Polynomial.coeff_divX]; exact hcoeff (i + 1)) hfmem
  have hcof_ne : Polynomial.aeval f P.divX ≠ 0 := by
    intro h
    rw [h, mul_zero, neg_zero] at hkey
    exact hc0 (by simpa using hkey)

  have hpos0 : 0 < w.ord (algebraMap F F' (P.coeff 0)) := by
    rw [hkey, w.ord_neg, w.ord_mul hf hcof_ne]
    have := w.ord_nonneg_of_mem hcof_mem
    omega
  have := hcon 0 hdeg hc0
  omega

end SupportTransfer

section Chart

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
variable (w : Place K F)

private def chartHom (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) :
    R →+* w.toValuationSubring :=
  (algebraMap R F).codRestrict w.toValuationSubring.toSubring hw

omit [IsDedekindDomain R] [IsFractionRing R F] in

private theorem inv_algebraMap_mem (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring)
    {s : R} (hs : IsUnit (chartHom w hw s)) :
    (algebraMap R F s)⁻¹ ∈ w.toValuationSubring := by
  obtain ⟨u, hu⟩ := hs
  have hcoe : ((u : w.toValuationSubring) : F) = algebraMap R F s := by rw [hu]; rfl
  have h1 : (((u⁻¹ : w.toValuationSubringˣ) : w.toValuationSubring) : F)
      * algebraMap R F s = 1 := by
    have hmul := congrArg (fun a : w.toValuationSubring => (a : F)) u.inv_mul
    push_cast at hmul
    rwa [hcoe] at hmul
  rw [← eq_inv_of_mul_eq_one_left h1]
  exact SetLike.coe_mem _

end Chart

end Place

section Assembly

variable {K : Type*} [Field K] {F' : Type*} [Field F'] [Algebra K F']
  [Algebra (RatFunc K) F'] [IsScalarTower K (RatFunc K) F']
  [FiniteDimensional (RatFunc K) F'] [Algebra.IsSeparable (RatFunc K) F']

theorem finite_setOf_ord_ne_zero_of_finiteDimensional {f : F'} (hf : f ≠ 0) :
    {w : Place K F' | w.ord f ≠ 0}.Finite := by
  classical
  set P := minpoly (RatFunc K) f with hPdef

  refine Set.Finite.subset (Set.Finite.biUnion (Set.finite_Iio P.natDegree) (fun i _ =>
    Set.Finite.biUnion (s := {v : Place K (RatFunc K) | v.ord (P.coeff i) ≠ 0})
      ?_ (fun v _ => Place.finite_setOf_restrict_eq v))) ?_
  ·
    rcases eq_or_ne (P.coeff i) 0 with h0 | h0
    · simp [h0]
    · exact RationalFunctionField.finite_setOf_ord_ne_zero h0
  ·
    intro w hw
    obtain ⟨i, hi, hci, hord⟩ := w.exists_coeff_ord_ne_zero (F := RatFunc K) hf hw
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    refine ⟨i, hi, w.restrict (RatFunc K), ?_, rfl⟩
    intro h0
    apply hord
    rw [w.ord_restrict, h0, mul_zero]

end Assembly

section P1PartialFraction

variable {K : Type*} [Field K]

theorem exists_monic_irreducible_factorization {d : K[X]} (hd : d.Monic) :
    ∃ (s : Finset K[X]) (n : K[X] → ℕ),
      (∀ p ∈ s, p.Monic) ∧ (∀ p ∈ s, Irreducible p) ∧
      (Set.Pairwise (s : Set K[X]) fun i j => IsCoprime i j) ∧
      d = ∏ p ∈ s, p ^ n p := by
  classical
  refine ⟨(normalizedFactors d).toFinset,
    fun p => (normalizedFactors d).count p, ?_, ?_, ?_, ?_⟩
  ·
    intro p hp
    exact ((Polynomial.mem_normalizedFactors_iff hd.ne_zero).mp
      (Multiset.mem_toFinset.mp hp)).2.1
  ·
    intro p hp
    exact irreducible_of_normalized_factor p (Multiset.mem_toFinset.mp hp)
  ·
    intro p hp q hq hne
    have hp' := Multiset.mem_toFinset.mp hp
    have hq' := Multiset.mem_toFinset.mp hq
    rw [(irreducible_of_normalized_factor p hp').coprime_iff_not_dvd]
    exact fun hdvd => hne (normalizedFactors_eq_of_dvd d p hp' q hq' hdvd)
  ·
    calc d = (normalizedFactors d).prod := by
            rw [prod_normalizedFactors_eq hd.ne_zero, hd.normalize_eq_self]
      _ = ∏ p ∈ (normalizedFactors d).toFinset, p ^ (normalizedFactors d).count p :=
            Finset.prod_multiset_count _

theorem algebraMap_mem_span_P1PartialFractionGenerators (q : K[X]) :
    algebraMap K[X] (RatFunc K) q ∈ Submodule.span K (P1PartialFractionGenerators K) :=
  Submodule.span_mono (by intro x hx; exact Or.inl hx)
    (gate_algebraMap_polynomial_mem_span_P1PolynomialGenerators q)

theorem div_pow_mem_span_P1PartialFractionGenerators
    {p c : K[X]} (hpmon : p.Monic) (hpirr : Irreducible p)
    (hdeg : c.degree < p.degree) {m : ℕ} (hm : 1 ≤ m) :
    algebraMap K[X] (RatFunc K) c / (algebraMap K[X] (RatFunc K) p) ^ m
      ∈ Submodule.span K (P1PartialFractionGenerators K) := by
  exact Submodule.subset_span (Or.inr ⟨p, c, m, hpmon, hpirr, hdeg, hm, rfl⟩)

theorem ratFunc_mem_span_P1PartialFractionGenerators (f : RatFunc K) :
    f ∈ Submodule.span K (P1PartialFractionGenerators K) := by
  classical

  have hdenmon : f.denom.Monic := RatFunc.monic_denom f

  obtain ⟨s, n, hmon, hirr, hcop, hdfac⟩ :=
    exists_monic_irreducible_factorization hdenmon

  have hginv : ∀ p ∈ s,
      (algebraMap K[X] (RatFunc K) p)⁻¹ * algebraMap K[X] (RatFunc K) p = 1 :=
    fun p hp => inv_mul_cancel₀ (RatFunc.algebraMap_ne_zero (hmon p hp).ne_zero)

  obtain ⟨q, r, hr, hpfrac⟩ :=
    Polynomial.mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse
      (K := RatFunc K) f.num hmon hcop n hginv

  have hLHS : algebraMap K[X] (RatFunc K) f.num *
      ∏ p ∈ s, ((algebraMap K[X] (RatFunc K) p)⁻¹) ^ n p = f := by
    have hprod : ∏ p ∈ s, ((algebraMap K[X] (RatFunc K) p)⁻¹) ^ n p
        = (algebraMap K[X] (RatFunc K) f.denom)⁻¹ := by
      rw [hdfac, map_prod]
      rw [← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun p _ => by rw [map_pow, inv_pow]
    rw [hprod, ← div_eq_mul_inv, RatFunc.num_div_denom]
  rw [← hLHS, hpfrac]

  refine Submodule.add_mem _ (algebraMap_mem_span_P1PartialFractionGenerators q) ?_
  refine Submodule.sum_mem _ fun p hp => ?_
  refine Submodule.sum_mem _ fun j _ => ?_

  rw [inv_pow, ← div_eq_mul_inv]
  exact div_pow_mem_span_P1PartialFractionGenerators (hmon p hp) (hirr p hp)
    (hr p hp j) j.succ_pos

theorem p1PartialFractionSpan_eq_top :
    Submodule.span K (P1PartialFractionGenerators K) = ⊤ :=
  Submodule.eq_top_iff'.mpr ratFunc_mem_span_P1PartialFractionGenerators

end P1PartialFraction

section GateResidue

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem gate_localResidueData_uniformizer_inv (v : Place K F) (R : v.LocalResidueData) :
    R.res v.uniformizer⁻¹ = 1 := by
  rw [v.localResidueData_res_eq_simplePoleResidueAux R
      (gate_uniformizer_inv_mem_simplePoleSubmodule v).1,
    Place.simplePoleResidueAux_apply]
  have h1 :
      (⟨v.uniformizer * v.uniformizer⁻¹,
        (gate_uniformizer_inv_mem_simplePoleSubmodule v).1⟩ : v.toValuationSubring) = 1 :=
    Subtype.ext (mul_inv_cancel₀ v.uniformizer_ne_zero)
  rw [h1, map_one]

end GateResidue

section OrdIntegrand

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]

section OrdIntegrandInner

variable [CharZero K]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

omit [DecidableEq (RatFunc K)] [CharZero K]
  [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]] in

theorem p1PrincipalPartAtom_ne_zero {p : K[X]} (hp : p ≠ 0) {c : K[X]} (hc : c ≠ 0)
    (m : ℕ) : p1PrincipalPartAtom K p c m ≠ 0 := by
  simp only [p1PrincipalPartAtom, ne_eq, div_eq_zero_iff, not_or]
  exact ⟨(map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hc,
    pow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hp)⟩

end OrdIntegrandInner

end OrdIntegrand

end AlgebraicCurve

end

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.overlappingInstances false

noncomputable section

open Polynomial IsDedekindDomain WithZero IsLocalRing UniqueFactorizationMonoid
open scoped Polynomial

namespace AlgebraicCurve

namespace RationalFunctionField

variable {K : Type*} [Field K]

/-- Pin row #156. -/
scoped instance instHasPrincipalDivisors : HasPrincipalDivisors K (RatFunc K) where
  exists_divisor _ hf := ⟨principalDivisor hf, fun _ => rfl, degree_principalDivisor hf⟩

end RationalFunctionField

section RationalFunctionFieldDifferential

open RationalFunctionField

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]

omit [DecidableEq (RatFunc K)] in
/-- Pin row #157. -/
theorem D_ratFuncX_eq_neg_X_sq_smul_D_inv :
    KaehlerDifferential.D K (RatFunc K) RatFunc.X
      = (-(RatFunc.X : RatFunc K) ^ 2) •
          KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹ :=
  (KaehlerDifferential.D K (RatFunc K)).leibniz_of_mul_eq_one
    (mul_inv_cancel₀ RatFunc.X_ne_zero)

/-- Pin row #158. -/
theorem ord_placeInfty_X_inv : (p1PlaceInfty K).ord (RatFunc.X : RatFunc K)⁻¹ = 1 := by
  rw [(p1PlaceInfty K).ord_inv, ord_placeInfty_X, neg_neg]

/-- Pin row #159. -/
theorem ord_placeInfty_X_pow (n : ℕ) :
    (p1PlaceInfty K).ord ((RatFunc.X : RatFunc K) ^ n) = -(n : ℤ) := by
  rw [show ((RatFunc.X : RatFunc K) ^ n) = (RatFunc.X : RatFunc K) ^ (n : ℤ) from
    (zpow_natCast _ n).symm, (p1PlaceInfty K).ord_zpow, ord_placeInfty_X]
  ring

end RationalFunctionFieldDifferential

section RationalFunctionFieldNonVanishing

open RationalFunctionField

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

/-- Pin row #160. -/
theorem D_ratFuncX_inv_ne_zero (hwd : OrdDifferentialWellDefined K (RatFunc K)) :
    KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹ ≠ 0 := by
  obtain ⟨u, -, hueq⟩ :=
    hwd (p1PlaceInfty K) (RatFunc.X : RatFunc K)⁻¹ (p1PlaceInfty K).uniformizer
      (ord_placeInfty_X_inv K) (p1PlaceInfty K).ord_uniformizer
  intro h0
  refine (p1PlaceInfty K).dCoord_ne_zero ?_
  show KaehlerDifferential.D K (RatFunc K) (p1PlaceInfty K).uniformizer = 0
  rw [hueq, h0, smul_zero]

/-- Pin row #161. -/
theorem differentialCoeff_placeInfty_D_X_eq :
    (p1PlaceInfty K).differentialCoeff (KaehlerDifferential.D K (RatFunc K) RatFunc.X)
      = (-(RatFunc.X : RatFunc K) ^ 2) *
          (p1PlaceInfty K).differentialCoeff
            (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹) := by
  rw [D_ratFuncX_eq_neg_X_sq_smul_D_inv, (p1PlaceInfty K).differentialCoeff_smul]

/-- Pin row #162. -/
theorem ord_differentialCoeff_placeInfty_D_X_inv_eq_zero
    (hwd : OrdDifferentialWellDefined K (RatFunc K)) :
    (p1PlaceInfty K).ord
        ((p1PlaceInfty K).differentialCoeff
          (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹)) = 0 := by
  obtain ⟨u, hu0, hueq⟩ :=
    hwd (p1PlaceInfty K) (p1PlaceInfty K).uniformizer (RatFunc.X : RatFunc K)⁻¹
      (p1PlaceInfty K).ord_uniformizer (ord_placeInfty_X_inv K)
  rw [(p1PlaceInfty K).differentialCoeff_unique
    (show KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹
        = u • (p1PlaceInfty K).dCoord from hueq), hu0]

/-- Pin row #163. -/
theorem ordDifferential_placeInfty_D_ratFuncX
    (hwd : OrdDifferentialWellDefined K (RatFunc K)) :
    (p1PlaceInfty K).ordDifferential
        (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)) = -2 := by
  rw [Place.ordDifferential, differentialCoeff_placeInfty_D_X_eq K, neg_mul,
    (p1PlaceInfty K).ord_neg,
    (p1PlaceInfty K).ord_mul (pow_ne_zero 2 RatFunc.X_ne_zero)
      ((p1PlaceInfty K).differentialCoeff_ne_zero (D_ratFuncX_inv_ne_zero K hwd)),
    ord_placeInfty_X_pow K 2, ord_differentialCoeff_placeInfty_D_X_inv_eq_zero K hwd]
  norm_num

end RationalFunctionFieldNonVanishing

namespace Place

section Uniqueness

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)

/-- Pin row #164. -/
theorem eq_ord_of_addHom_of_nonneg_iff (φ : F → ℤ)
    (hmul : ∀ x y, x ≠ 0 → y ≠ 0 → φ (x * y) = φ x + φ y)
    (hone : ∃ t, t ≠ 0 ∧ φ t = 1)
    (hiff : ∀ x, x ≠ 0 → (0 ≤ φ x ↔ x ∈ w.toValuationSubring))
    {x : F} (hx : x ≠ 0) : φ x = w.ord x := by
  obtain ⟨t, ht0, ht1⟩ := hone

  have hφ1 : φ 1 = 0 := by
    have := hmul 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at this
    omega

  have hinv : ∀ y, y ≠ 0 → φ y⁻¹ = -φ y := by
    intro y hy
    have h1 : φ (y * y⁻¹) = φ y + φ y⁻¹ := hmul y y⁻¹ hy (inv_ne_zero hy)
    rw [mul_inv_cancel₀ hy, hφ1] at h1
    omega

  have hpow : ∀ (y : F), y ≠ 0 → ∀ m : ℕ, φ (y ^ m) = m * φ y := by
    intro y hy m
    induction m with
    | zero => simpa using hφ1
    | succ m ih =>
      rw [pow_succ, hmul _ _ (pow_ne_zero _ hy) hy, ih]
      push_cast
      ring
  have hzpow : ∀ (y : F) (n : ℤ), y ≠ 0 → φ (y ^ n) = n * φ y := by
    intro y n hy
    rcases n with m | m
    · simpa using hpow y hy m
    · rw [zpow_negSucc, hinv _ (pow_ne_zero _ hy), hpow y hy, Int.negSucc_eq]
      push_cast
      ring

  have hsign : ∀ y, y ≠ 0 → (0 ≤ φ y ↔ 0 ≤ w.ord y) := by
    intro y hy
    rw [hiff y hy, w.mem_iff_ord_nonneg hy]
  have hzero : ∀ y, y ≠ 0 → (φ y = 0 ↔ w.ord y = 0) := by
    intro y hy
    have h1 := hsign y hy
    have h2 := hsign y⁻¹ (inv_ne_zero hy)
    rw [hinv y hy, w.ord_inv] at h2
    omega

  have htord : 0 < w.ord t := by
    have h1 := (hsign t ht0).mp (by omega)
    have h2 := (hzero t ht0).not.mp (by omega)
    omega

  have hcancel : ∀ y, y ≠ 0 → w.ord y = φ y * w.ord t := by
    intro y hy
    have hyt : y * t ^ (-(φ y)) ≠ 0 := mul_ne_zero hy (zpow_ne_zero _ ht0)
    have h1 : φ (y * t ^ (-(φ y))) = 0 := by
      rw [hmul _ _ hy (zpow_ne_zero _ ht0), hzpow t _ ht0, ht1]
      ring
    have h2 : w.ord (y * t ^ (-(φ y))) = 0 := (hzero _ hyt).mp h1
    rw [w.ord_mul hy (zpow_ne_zero _ ht0), w.ord_zpow] at h2
    linarith

  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  have hπ0 : (π : F) ≠ 0 := by
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  have hπcancel := hcancel (π : F) hπ0
  rw [w.ord_coe_irreducible hπ] at hπcancel

  have htord1 : w.ord t = 1 := by
    have hdvd : w.ord t ∣ 1 := ⟨φ (π : F), by linarith⟩
    have := Int.le_of_dvd one_pos hdvd
    omega
  have := hcancel x hx
  rw [htord1, mul_one] at this
  exact this.symm

end Uniqueness

end Place

end AlgebraicCurve

end

noncomputable section

open Polynomial IsDedekindDomain WithZero IsLocalRing UniqueFactorizationMonoid
open scoped Polynomial

namespace AlgebraicCurve

namespace Place

section ResidueEngine

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem isSeparable_residueField_of_charZero_of_finiteResidue
    [CharZero K] [v.FiniteResidue] :
    Algebra.IsSeparable K (IsLocalRing.ResidueField v.toValuationSubring) := by
  haveI : Module.Finite K (IsLocalRing.ResidueField v.toValuationSubring) := Place.FiniteResidue.finite
  haveI : Algebra.IsAlgebraic K (IsLocalRing.ResidueField v.toValuationSubring) :=
    Algebra.IsAlgebraic.of_finite K _
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

private theorem subsingleton_polynomialKaehler_of_charZero_of_finite
    [CharZero K] [v.FiniteResidue]
    [Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄K]] :
    letI := v.polynomialAlgebra
    Subsingleton Ω[v.toValuationSubring⁄K[X]] := by
  haveI := v.isSeparable_residueField_of_charZero_of_finiteResidue
  exact v.subsingleton_polynomialKaehler_of_isSeparable_of_finite

end ResidueEngine

end Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem valSubringPolynomialFormallyUnramified_of_kaehlerFinite_of_charZero
    [CharZero K] [∀ v : Place K F, v.FiniteResidue]
    (hfin : ValSubringKaehlerFinite K F) :
    ValSubringPolynomialFormallyUnramified K F := by
  intro v
  haveI := hfin v
  exact v.subsingleton_polynomialKaehler_of_charZero_of_finite

theorem valSubringKaehlerSpanTop_of_kaehlerFinite_of_charZero
    [CharZero K] [∀ v : Place K F, v.FiniteResidue]
    (hfin : ValSubringKaehlerFinite K F) :
    ValSubringKaehlerSpanTop K F :=
  valSubringKaehlerSpanTop_of_polynomialFormallyUnramified
    (valSubringPolynomialFormallyUnramified_of_kaehlerFinite_of_charZero hfin)

end AlgebraicCurve

namespace ModularCurve

open AlgebraicCurve

namespace MilneAvAg9bRd15UnitNormalFormLaurentSeed

private theorem ag9b15u_eq_zero_or_one_le_ord_of_residue_eq_zero
    {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {g : F} (hg : g ∈ v.toValuationSubring)
    (h0 : IsLocalRing.residue _ (⟨g, hg⟩ : v.toValuationSubring) = 0) :
    g = 0 ∨ 1 ≤ v.ord g := by
  rcases eq_or_ne g 0 with rfl | hg0
  · exact Or.inl rfl
  right
  have hnn : 0 ≤ v.ord g := v.ord_nonneg_of_mem hg
  rcases eq_or_ne (v.ord g) 0 with hz | hnz
  · exfalso
    have hmemi : g⁻¹ ∈ v.toValuationSubring := by
      refine v.mem_of_ord_nonneg (inv_ne_zero hg0) ?_
      rw [v.ord_inv, hz, _root_.neg_zero]
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff] at h0
    exact h0 ⟨⟨⟨g, hg⟩, ⟨g⁻¹, hmemi⟩, Subtype.ext (mul_inv_cancel₀ hg0),
      Subtype.ext (inv_mul_cancel₀ hg0)⟩, rfl⟩
  · omega

private theorem ag9b15u_exists_unit_normal_form_of_surj
    {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    {w : F} (hw0 : w ≠ 0) (hw : v.ord w = 0) :
    ∃ (c : K) (s : F), c ≠ 0 ∧ (s = 0 ∨ 1 ≤ v.ord s) ∧
      w = algebraMap K F c * (1 + s) := by
  have hwmem : w ∈ v.toValuationSubring := v.mem_of_ord_nonneg hw0 hw.ge
  have hwinv : w⁻¹ ∈ v.toValuationSubring := by
    refine v.mem_of_ord_nonneg (inv_ne_zero hw0) ?_
    rw [v.ord_inv, hw, _root_.neg_zero]
  have hres0 : IsLocalRing.residue _ (⟨w, hwmem⟩ : v.toValuationSubring) ≠ 0 := by
    intro h0
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff] at h0
    exact h0 ⟨⟨⟨w, hwmem⟩, ⟨w⁻¹, hwinv⟩, Subtype.ext (mul_inv_cancel₀ hw0),
      Subtype.ext (inv_mul_cancel₀ hw0)⟩, rfl⟩
  obtain ⟨c, hc⟩ := hsurj (IsLocalRing.residue _ (⟨w, hwmem⟩ : v.toValuationSubring))
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [_root_.map_zero] at hc
    exact hres0 hc.symm
  have ha0 : algebraMap K F c ≠ 0 :=
    fun h => hc0 ((algebraMap K F).injective (h.trans (_root_.map_zero _).symm))
  refine ⟨c, w * (algebraMap K F c)⁻¹ - 1, hc0, ?_, ?_⟩
  · have hainv : (algebraMap K F c)⁻¹ ∈ v.toValuationSubring := by
      rw [← map_inv₀]
      exact v.algebraMap_mem' c⁻¹
    have hsmem : w * (algebraMap K F c)⁻¹ - 1 ∈ v.toValuationSubring :=
      sub_mem (mul_mem hwmem hainv) (one_mem _)
    refine ag9b15u_eq_zero_or_one_le_ord_of_residue_eq_zero v hsmem ?_
    have hfact : (⟨w * (algebraMap K F c)⁻¹ - 1, hsmem⟩ : v.toValuationSubring)
        = ⟨w, hwmem⟩ * ⟨(algebraMap K F c)⁻¹, hainv⟩ - 1 :=
      Subtype.ext (by push_cast; ring)
    have hainv_res : IsLocalRing.residue _
        ((⟨(algebraMap K F c)⁻¹, hainv⟩ : v.toValuationSubring))
        = (IsLocalRing.residue _ (⟨w, hwmem⟩ : v.toValuationSubring))⁻¹ := by
      have h1 : (⟨(algebraMap K F c)⁻¹, hainv⟩ : v.toValuationSubring)
          = algebraMap K v.toValuationSubring c⁻¹ :=
        Subtype.ext (by rw [v.coe_algebraMap, map_inv₀])
      rw [h1, ← IsLocalRing.ResidueField.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField,
        map_inv₀, hc, IsLocalRing.ResidueField.algebraMap_eq]
    rw [hfact, map_sub, map_mul, map_one, hainv_res, mul_inv_cancel₀ hres0, sub_self]
  · have hrw : (1 : F) + (w * (algebraMap K F c)⁻¹ - 1) = w * (algebraMap K F c)⁻¹ := by
      ring
    rw [hrw, mul_comm w (algebraMap K F c)⁻¹, ← mul_assoc,
      mul_inv_cancel₀ ha0, one_mul]

private theorem ag9b15u_exists_K_truncation_of_mem_poleSubmodule
    {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    (n : ℕ) {f : F} (hf : f ∈ v.poleSubmodule n) :
    ∃ c : ℕ → K,
      f - ∑ j ∈ Finset.range n, algebraMap K F (c j) * (v.uniformizer ^ (j + 1))⁻¹
        ∈ v.toValuationSubring := by
  induction n generalizing f with
  | zero =>
    refine ⟨0, ?_⟩
    rw [Finset.range_zero, Finset.sum_empty, sub_zero]
    rwa [← SetLike.mem_coe, v.coe_poleSubmodule_zero] at hf
  | succ n ih =>
    obtain ⟨ctop, hctop⟩ := hsurj (v.laurentTailCoeff (n + 1) ⟨f, hf⟩)
    have hclift : IsLocalRing.residue _ (algebraMap K v.toValuationSubring ctop)
        = v.laurentTailCoeff (n + 1) ⟨f, hf⟩ := by
      rw [← hctop, IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField,
        IsLocalRing.ResidueField.algebraMap_eq]
    have hrem : f - algebraMap K F ctop * (v.uniformizer ^ (n + 1))⁻¹
        ∈ v.poleSubmodule n := by
      have h := v.laurentTail_remainder_mem_poleSubmodule hf hclift
      rwa [v.coe_algebraMap] at h
    obtain ⟨c', hc'⟩ := ih hrem
    refine ⟨fun j => if j = n then ctop else c' j, ?_⟩
    have hstep : ∑ j ∈ Finset.range (n + 1),
        algebraMap K F (if j = n then ctop else c' j) * (v.uniformizer ^ (j + 1))⁻¹
        = (∑ j ∈ Finset.range n, algebraMap K F (c' j) * (v.uniformizer ^ (j + 1))⁻¹)
          + algebraMap K F ctop * (v.uniformizer ^ (n + 1))⁻¹ := by
      rw [Finset.sum_range_succ, ite_eq_left rfl]
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [ite_eq_right (Finset.mem_range.mp hj).ne]
    rw [hstep, show f - ((∑ j ∈ Finset.range n,
          algebraMap K F (c' j) * (v.uniformizer ^ (j + 1))⁻¹)
          + algebraMap K F ctop * (v.uniformizer ^ (n + 1))⁻¹)
        = f - algebraMap K F ctop * (v.uniformizer ^ (n + 1))⁻¹
          - ∑ j ∈ Finset.range n,
              algebraMap K F (c' j) * (v.uniformizer ^ (j + 1))⁻¹ from by ring]
    exact hc'

private theorem ag9b15u_differentialCoeff_D_unit_mul_uniformizer
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]] (w : F) :
    v.differentialCoeff (KaehlerDifferential.D K F (w * v.uniformizer))
      = w + v.uniformizer * v.differentialCoeff (KaehlerDifferential.D K F w) := by
  refine v.differentialCoeff_unique ?_
  calc KaehlerDifferential.D K F (w * v.uniformizer)
      = w • KaehlerDifferential.D K F v.uniformizer
        + v.uniformizer • KaehlerDifferential.D K F w := by
        rw [Derivation.leibniz]
    _ = w • v.dCoord + v.uniformizer •
          (v.differentialCoeff (KaehlerDifferential.D K F w) • v.dCoord) := by
        rw [show KaehlerDifferential.D K F v.uniformizer = v.dCoord from rfl,
          v.differentialCoeff_smul_dCoord]
    _ = (w + v.uniformizer * v.differentialCoeff (KaehlerDifferential.D K F w))
          • v.dCoord := by
        rw [smul_smul, add_smul]

end MilneAvAg9bRd15UnitNormalFormLaurentSeed

end ModularCurve

end

noncomputable section

open Polynomial IsDedekindDomain WithZero IsLocalRing KaehlerDifferential
open scoped Polynomial
open scoped AlgebraicCurve.RationalFunctionField

namespace AlgebraicCurve

open RationalFunctionField

variable (K : Type*) [Field K]

/-- Pin row #212. -/
abbrev dX : Ω[(RatFunc K)⁄K] := KaehlerDifferential.D K (RatFunc K) RatFunc.X

/-- Pin row #213. -/
theorem aeval_ratFuncX_eq_algebraMap (q : K[X]) :
    aeval (RatFunc.X : RatFunc K) q = algebraMap K[X] (RatFunc K) q := by
  rw [← RatFunc.algebraMap_X,
    show algebraMap K[X] (RatFunc K) X = IsScalarTower.toAlgHom K K[X] (RatFunc K) X from rfl,
    aeval_algHom_apply, aeval_X_left_apply]
  rfl

/-- Pin row #214. -/
theorem D_algebraMap_polynomial (q : K[X]) :
    KaehlerDifferential.D K (RatFunc K) (algebraMap K[X] (RatFunc K) q)
      = algebraMap K[X] (RatFunc K) q.derivative • dX K := by
  rw [← aeval_ratFuncX_eq_algebraMap K q, (D K (RatFunc K)).map_aeval q RatFunc.X,
    aeval_ratFuncX_eq_algebraMap K q.derivative]

/-- Pin row #215. -/
theorem denom_sq_smul_D_eq (f : RatFunc K) :
    (algebraMap K[X] (RatFunc K) f.denom) ^ 2 • KaehlerDifferential.D K (RatFunc K) f
      = algebraMap K[X] (RatFunc K)
          (f.num.derivative * f.denom - f.num * f.denom.derivative) • dX K := by
  have hd : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr f.denom_ne_zero
  have hDf : KaehlerDifferential.D K (RatFunc K) f
      = ((algebraMap K[X] (RatFunc K) f.denom)⁻¹ ^ 2) •
        (algebraMap K[X] (RatFunc K) f.denom • D K (RatFunc K) (algebraMap K[X] (RatFunc K) f.num)
          - algebraMap K[X] (RatFunc K) f.num
              • D K (RatFunc K) (algebraMap K[X] (RatFunc K) f.denom)) := by
    conv_lhs => rw [← f.num_div_denom, (D K (RatFunc K)).leibniz_div]
  rw [hDf, smul_smul, ← mul_pow, mul_inv_cancel₀ hd, one_pow, one_smul,
    D_algebraMap_polynomial K f.num, D_algebraMap_polynomial K f.denom,
    smul_smul, smul_smul, ← sub_smul]
  push_cast
  ring_nf

/-- Pin row #216. -/
theorem span_dX_eq_top :
    Submodule.span (RatFunc K) {dX K} = ⊤ := by
  rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨f, rfl⟩
  have hd : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr f.denom_ne_zero

  have hsq : ((algebraMap K[X] (RatFunc K) f.denom) ^ 2)⁻¹
        * (algebraMap K[X] (RatFunc K) f.denom) ^ 2 = 1 :=
    inv_mul_cancel₀ (pow_ne_zero 2 hd)
  refine Submodule.mem_span_singleton.mpr ⟨((algebraMap K[X] (RatFunc K) f.denom) ^ 2)⁻¹
    * algebraMap K[X] (RatFunc K)
        (f.num.derivative * f.denom - f.num * f.denom.derivative), ?_⟩
  rw [mul_smul, ← denom_sq_smul_D_eq K f, smul_smul, hsq, one_smul]

/-- Pin row #217. -/
theorem dX_ne_zero [Nontrivial Ω[(RatFunc K)⁄K]] : dX K ≠ 0 := by
  intro h0
  obtain ⟨ω, hω⟩ := exists_ne (0 : Ω[(RatFunc K)⁄K])
  have hω_mem : ω ∈ Submodule.span (RatFunc K) {dX K} :=
    span_dX_eq_top K ▸ Submodule.mem_top
  rw [h0, Submodule.span_zero_singleton] at hω_mem
  exact hω hω_mem

/-- Pin row #218. -/
theorem not_dvd_derivative_of_sq_not_dvd {p : K[X]} (hp : Irreducible p) (hsep : p.Separable)
    {q : K[X]} (hpq : p ∣ q) (hpq2 : ¬ p ^ 2 ∣ q) : ¬ p ∣ q.derivative := by
  obtain ⟨m, rfl⟩ := hpq
  have hpm : ¬ p ∣ m := fun ⟨r, hr⟩ => hpq2 ⟨r, by rw [hr]; ring⟩
  intro hpdvd
  rw [derivative_mul] at hpdvd
  have hpdvd' : p ∣ p.derivative * m := by
    have := dvd_sub hpdvd (dvd_mul_right p m.derivative)
    rwa [add_sub_cancel_right] at this
  rcases hp.prime.dvd_mul.mp hpdvd' with hpp' | hpm'
  ·
    exact hp.not_isUnit (hsep.isUnit_of_dvd' dvd_rfl hpp')
  · exact hpm hpm'

variable {K}

/-- Pin row #219. -/
theorem not_dvd_derivative_of_ord_eq_one {w : HeightOneSpectrum K[X]} {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) (hsep : p.Separable)
    {q : K[X]} (hq : q ≠ 0)
    (hord : (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
      (algebraMap K[X] (RatFunc K) q) = 1) :
    ¬ p ∣ q.derivative := by
  have hwmem : ∀ {r : K[X]}, r ≠ 0 →
      ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
        (algebraMap K[X] (RatFunc K) r) ≠ 0 ↔ p ∣ r) := fun {r} hr => by
    rw [Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w hr,
      hwp, Ideal.mem_span_singleton]
  have hordp : (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
      (algebraMap K[X] (RatFunc K) p) = 1 :=
    ord_ofHeightOneSpectrum_of_span w hp.ne_zero hwp
  refine not_dvd_derivative_of_sq_not_dvd K hp hsep
    ((hwmem hq).mp (hord ▸ one_ne_zero)) ?_

  rintro ⟨r, rfl⟩
  have hr : r ≠ 0 := fun h => hq (by simp [h])
  have : (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
      (algebraMap K[X] (RatFunc K) (p ^ 2 * r)) ≥ 2 := by
    have hp0 : algebraMap K[X] (RatFunc K) p ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hp.ne_zero
    have hr0 : algebraMap K[X] (RatFunc K) r ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hr
    rw [map_mul, map_pow,
      (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord_mul (pow_ne_zero 2 hp0) hr0,
      ← zpow_natCast, (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord_zpow,
      hordp, mul_one]
    have : 0 ≤ (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
        (algebraMap K[X] (RatFunc K) r) :=
      (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord_nonneg_of_mem
        (algebraMap_mem_ofHeightOneSpectrum K w r)
    omega
  omega

section NumDenom

variable {w : HeightOneSpectrum K[X]}

local notation "v" => Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w

/-- Pin row #220. -/
private theorem uniformizer_ne_zero' : (v).uniformizer ≠ 0 :=
  (v).uniformizer_ne_zero

/-- Pin row #221. -/
theorem ord_algebraMap_denom_uniformizer_eq_zero {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) :
    (v).ord (algebraMap K[X] (RatFunc K) (v).uniformizer.denom) = 0 := by
  set π := (v).uniformizer with hπ
  have hπne : π ≠ 0 := uniformizer_ne_zero'
  by_contra hne

  have hpd : p ∣ π.denom := by
    rw [← Ideal.mem_span_singleton, ← hwp]
    exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
      π.denom_ne_zero).mp hne
  have hpn : ¬ p ∣ π.num := fun hpn =>
    hp.not_isUnit (π.isCoprime_num_denom.isUnit_of_dvd' hpn hpd)
  have hordn : (v).ord (algebraMap K[X] (RatFunc K) π.num) = 0 := by
    by_contra h
    exact hpn (by
      rw [← Ideal.mem_span_singleton, ← hwp]
      exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
        (RatFunc.num_ne_zero hπne)).mp h)
  have hordd : 0 < (v).ord (algebraMap K[X] (RatFunc K) π.denom) :=
    lt_of_le_of_ne ((v).ord_nonneg_of_mem (algebraMap_mem_ofHeightOneSpectrum K w _)) (Ne.symm hne)

  have hnum0 : algebraMap K[X] (RatFunc K) π.num ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr (RatFunc.num_ne_zero hπne)
  have hden0 : algebraMap K[X] (RatFunc K) π.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr π.denom_ne_zero
  have hordπ : (v).ord π = 1 := (v).ord_uniformizer
  rw [← π.num_div_denom, div_eq_mul_inv, (v).ord_mul hnum0 (inv_ne_zero hden0),
    (v).ord_inv, hordn] at hordπ
  omega

/-- Pin row #222. -/
theorem ord_algebraMap_num_uniformizer_eq_one {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) :
    (v).ord (algebraMap K[X] (RatFunc K) (v).uniformizer.num) = 1 := by
  set π := (v).uniformizer with hπ
  have hπne : π ≠ 0 := uniformizer_ne_zero'
  have hnum0 : algebraMap K[X] (RatFunc K) π.num ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr (RatFunc.num_ne_zero hπne)
  have hden0 : algebraMap K[X] (RatFunc K) π.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr π.denom_ne_zero
  have hordπ : (v).ord π = 1 := (v).ord_uniformizer
  rw [← π.num_div_denom, div_eq_mul_inv, (v).ord_mul hnum0 (inv_ne_zero hden0),
    (v).ord_inv, ord_algebraMap_denom_uniformizer_eq_zero hp hwp] at hordπ
  omega

/-- Pin row #223. -/
theorem not_dvd_num'denom_sub_numdenom' {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) (hsep : p.Separable) :
    ¬ p ∣ ((v).uniformizer.num.derivative * (v).uniformizer.denom
            - (v).uniformizer.num * (v).uniformizer.denom.derivative) := by
  set π := (v).uniformizer with hπ
  have hπne : π ≠ 0 := uniformizer_ne_zero'
  have hpn' : ¬ p ∣ π.num.derivative :=
    not_dvd_derivative_of_ord_eq_one hp hwp hsep (RatFunc.num_ne_zero hπne)
      (ord_algebraMap_num_uniformizer_eq_one hp hwp)
  have hpd : ¬ p ∣ π.denom := fun hpd => by
    have := ord_algebraMap_denom_uniformizer_eq_zero (w := w) hp hwp
    rw [← Ideal.mem_span_singleton, ← hwp] at hpd
    exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
      π.denom_ne_zero).mpr hpd this
  have hpn : p ∣ π.num := by
    rw [← Ideal.mem_span_singleton, ← hwp]
    refine (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
      (RatFunc.num_ne_zero hπne)).mp ?_
    rw [ord_algebraMap_num_uniformizer_eq_one hp hwp]; exact one_ne_zero
  intro hdvd

  have hpnd' : p ∣ π.num * π.denom.derivative := hpn.mul_right _
  have hpn'd : p ∣ π.num.derivative * π.denom := by
    have := dvd_add hdvd hpnd'
    rwa [sub_add_cancel] at this
  rcases hp.prime.dvd_mul.mp hpn'd with h | h
  · exact hpn' h
  · exact hpd h

end NumDenom

section PerPlace

variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable {w : HeightOneSpectrum K[X]}

local notation "v" => Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w

/-- Pin row #224. -/
theorem ord_differentialCoeff_dX_ofHeightOneSpectrum {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) (hsep : p.Separable) :
    (v).ord ((v).differentialCoeff (dX K)) = 0 := by
  set π := (v).uniformizer with hπ
  have hπne : π ≠ 0 := uniformizer_ne_zero'
  set ξ : K[X] := π.num.derivative * π.denom - π.num * π.denom.derivative with hξ
  have hd0 : algebraMap K[X] (RatFunc K) π.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr π.denom_ne_zero

  have hcoord : (v).dCoord
      = (algebraMap K[X] (RatFunc K) ξ / (algebraMap K[X] (RatFunc K) π.denom) ^ 2) • dX K := by
    rw [div_eq_mul_inv, mul_comm, mul_smul, ← denom_sq_smul_D_eq K π, smul_smul,
      inv_mul_cancel₀ (pow_ne_zero 2 hd0), one_smul]
    rfl

  have hξ0 : ξ ≠ 0 := by
    intro h; rw [hξ] at h
    exact not_dvd_num'denom_sub_numdenom' hp hwp hsep (h ▸ dvd_zero p)
  have hcoeff0 : algebraMap K[X] (RatFunc K) ξ / (algebraMap K[X] (RatFunc K) π.denom) ^ 2 ≠ 0 :=
    div_ne_zero ((map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hξ0)
      (pow_ne_zero 2 hd0)

  have hcoeff : (v).differentialCoeff (dX K)
      = (algebraMap K[X] (RatFunc K) ξ / (algebraMap K[X] (RatFunc K) π.denom) ^ 2)⁻¹ := by
    refine (v).differentialCoeff_unique ?_
    rw [hcoord, smul_smul, inv_mul_cancel₀ hcoeff0, one_smul]

  have hordξ : (v).ord (algebraMap K[X] (RatFunc K) ξ) = 0 := by
    by_contra h
    refine not_dvd_num'denom_sub_numdenom' hp hwp hsep ?_
    rw [← Ideal.mem_span_singleton, ← hwp]
    exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w hξ0).mp h
  rw [hcoeff, (v).ord_inv, div_eq_mul_inv,
    (v).ord_mul ((map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hξ0)
      (inv_ne_zero (pow_ne_zero 2 hd0)),
    hordξ, (v).ord_inv, ← zpow_natCast, (v).ord_zpow,
    ord_algebraMap_denom_uniformizer_eq_zero hp hwp]
  ring

/-- Pin row #225. -/
theorem differentialCoeff_dX_mem_ofHeightOneSpectrum {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) (hsep : p.Separable) :
    (v).differentialCoeff (dX K) ∈ (v).toValuationSubring :=
  (v).mem_of_ord_nonneg ((v).differentialCoeff_ne_zero (dX_ne_zero K))
    (ord_differentialCoeff_dX_ofHeightOneSpectrum hp hwp hsep).ge

end PerPlace

section Discharge

variable (K)
variable [CharZero K] [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]

omit [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
  [HasPrincipalDivisors K (RatFunc K)] in

/-- Pin row #226. -/
theorem p1DifferentialCoeffRegularFinite_dX :
    P1DifferentialCoeffRegularFinite K (dX_ne_zero K) := by
  intro v hvinf
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  · obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
    exact differentialCoeff_dX_mem_ofHeightOneSpectrum hp hwp hp.separable
  · exact absurd rfl hvinf

end Discharge

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]

variable (K)

omit [DecidableEq (RatFunc K)] in

/-- Pin row #227. -/
theorem ord_ofHeightOneSpectrum_irreducible_eq_zero_of_ne
    (w : HeightOneSpectrum K[X]) {p : K[X]} (hp : Irreducible p)
    (hne : w ≠ heightOneSpectrumOfIrreducible K hp) :
    (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
      (algebraMap K[X] (RatFunc K) p) = 0 := by
  by_contra hord
  refine hne (HeightOneSpectrum.ext ?_)
  have hmem : p ∈ w.asIdeal :=
    (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w hp.ne_zero).mp hord

  exact ((PrincipalIdealRing.isMaximal_of_irreducible hp).eq_of_le
    (w.isPrime.isMaximal w.ne_bot).ne_top
    ((Ideal.span_singleton_le_iff_mem w.asIdeal).mpr hmem)).symm

/-- Pin row #228. -/
theorem ord_algebraMap_irreducible_eq_zero_of_ne
    {p : K[X]} (hp : Irreducible p) {v : Place K (RatFunc K)}
    (hvp : v ≠ finitePlace K hp) (hvinf : v ≠ p1PlaceInfty K) :
    v.ord (algebraMap K[X] (RatFunc K) p) = 0 := by
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  · refine ord_ofHeightOneSpectrum_irreducible_eq_zero_of_ne K w hp ?_
    rintro rfl; exact hvp rfl
  · exact absurd rfl hvinf

/-- Pin row #229. -/
theorem inv_algebraMap_pow_mem_of_ne_finitePlace
    {p : K[X]} (hp : Irreducible p) {v : Place K (RatFunc K)}
    (hvp : v ≠ finitePlace K hp) (hvinf : v ≠ p1PlaceInfty K) (m : ℕ) :
    ((algebraMap K[X] (RatFunc K) p) ^ m)⁻¹ ∈ v.toValuationSubring := by
  have hp0 : algebraMap K[X] (RatFunc K) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hp.ne_zero
  refine v.mem_of_ord_nonneg (inv_ne_zero (pow_ne_zero m hp0)) ?_
  rw [v.ord_inv, ← zpow_natCast, v.ord_zpow,
    ord_algebraMap_irreducible_eq_zero_of_ne K hp hvp hvinf, mul_zero, _root_.neg_zero]

/-- Pin row #230. -/
theorem p1PrincipalPartAtom_mem_of_ne_finitePlace
    {p : K[X]} (hp : Irreducible p) (c : K[X]) (m : ℕ) {v : Place K (RatFunc K)}
    (hvp : v ≠ finitePlace K hp) (hvinf : v ≠ p1PlaceInfty K) :
    p1PrincipalPartAtom K p c m ∈ v.toValuationSubring := by
  unfold p1PrincipalPartAtom
  rw [div_eq_mul_inv]
  exact mul_mem (algebraMap_polynomial_mem_of_ne_placeInfty' K hvinf c)
    (inv_algebraMap_pow_mem_of_ne_finitePlace K hp hvp hvinf m)

/-- Pin row #231. -/
theorem ord_placeInfty_p1PrincipalPartAtom
    {p : K[X]} (hp : p ≠ 0) {c : K[X]} (hc : c ≠ 0) (m : ℕ) :
    (p1PlaceInfty K).ord (p1PrincipalPartAtom K p c m)
      = (m : ℤ) * p.natDegree - c.natDegree := by
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hp' : algebraMap K[X] (RatFunc K) p ≠ 0 := (map_ne_zero_iff _ hinj).mpr hp
  have hc' : algebraMap K[X] (RatFunc K) c ≠ 0 := (map_ne_zero_iff _ hinj).mpr hc
  unfold p1PrincipalPartAtom
  rw [div_eq_mul_inv, (p1PlaceInfty K).ord_mul hc' (inv_ne_zero (pow_ne_zero m hp')),
    (p1PlaceInfty K).ord_inv, ← zpow_natCast, (p1PlaceInfty K).ord_zpow,
    ord_placeInfty_algebraMap' K hc, ord_placeInfty_algebraMap' K hp]
  ring

/-- Pin row #232. -/
theorem one_le_ord_placeInfty_p1PrincipalPartAtom
    {p : K[X]} (hp : Irreducible p) {c : K[X]} (hc : c ≠ 0) {m : ℕ}
    (hdeg : c.degree < p.degree) (hm : 1 ≤ m) :
    1 ≤ (p1PlaceInfty K).ord (p1PrincipalPartAtom K p c m) := by
  rw [ord_placeInfty_p1PrincipalPartAtom K hp.ne_zero hc]

  have hndeg : c.natDegree < p.natDegree :=
    Polynomial.natDegree_lt_natDegree hc hdeg
  have hpdeg : 1 ≤ (p.natDegree : ℤ) := by exact_mod_cast hp.natDegree_pos
  have hm' : 1 ≤ (m : ℤ) := by exact_mod_cast hm
  nlinarith

end AlgebraicCurve

end

noncomputable section

open Polynomial IsDedekindDomain WithZero IsLocalRing KaehlerDifferential
open scoped Polynomial
open scoped AlgebraicCurve.RationalFunctionField

namespace AlgebraicCurve

open RationalFunctionField

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

/-- Pin row #233. -/
def KaehlerRankOne : Prop :=
  Module.Free F Ω[F⁄K] ∧ Module.finrank F Ω[F⁄K] = 1

variable {K F}

namespace IsCurveOver

/-- Pin row #234. -/
theorem of_finiteResidue_of_kaehlerRankOne
    [HasPrincipalDivisors K F] [∀ v : Place K F, v.FiniteResidue]
    (hΩ : KaehlerRankOne K F) : IsCurveOver K F where
  finiteResidue v := Place.FiniteResidue.finite (v := v)
  kaehler_free_rank_one := hΩ

end IsCurveOver

namespace RationalFunctionField

variable (K : Type*) [Field K]

/-- Pin row #235. -/
theorem isCurveOver_of_kaehlerRankOne (hΩ : KaehlerRankOne K (RatFunc K)) :
    IsCurveOver K (RatFunc K) :=
  IsCurveOver.of_finiteResidue_of_kaehlerRankOne hΩ

end RationalFunctionField

section Identity

variable (K F F' : Type*) [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F']

/-- Pin row #236. -/
def RamificationInertiaIdentity : Prop :=
  ∀ (v : Place K F) (s : Finset (Place K F')), (∀ w : Place K F', w ∈ s ↔ w.restrict F = v) →
    ∑ w ∈ s, (w.ramificationIndex F : ℤ) * (w.deg : ℤ)
      = (Module.finrank F F' : ℤ) * (v.deg : ℤ)

variable {K F F'}

end Identity

namespace Place

/-- Pin `Place.ord_smul` (`Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean:314`):
ported against the ported `SemilinearAut` action. -/
private theorem ord_smul {K F : Type*} [Field K] [Field F] [Algebra K F]
    (σ : F ≃ₐ[K] F) (v : Place K F) (f : F) : (σ • v).ord (σ f) = v.ord f := by
  change (SemilinearAut.ofAlgAut σ • v).ord (σ f) = v.ord f
  exact SemilinearAut.ord_smul (SemilinearAut.ofAlgAut σ) v f

/-- Pin `Place.deg_smul` (`Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean:348`). -/
private theorem deg_smul {K F : Type*} [Field K] [Field F] [Algebra K F]
    (σ : F ≃ₐ[K] F) (v : Place K F) : (σ • v).deg = v.deg := by
  change (SemilinearAut.ofAlgAut σ • v).deg = v.deg
  exact SemilinearAut.deg_smul (SemilinearAut.ofAlgAut σ) v

end Place

namespace Divisor

section SmulAux

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- The `F ≃ₐ[K] F`-action on places as a `MulAction`, needed by the pin's
`Divisor` action (`Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean:359`). -/
private instance instMulActionAlgEquivPlace : MulAction (F ≃ₐ[K] F) (Place K F) where
  smul σ v := SemilinearAut.ofAlgAut σ • v
  one_smul v := by
    show SemilinearAut.ofAlgAut (1 : F ≃ₐ[K] F) • v = v
    rw [map_one, one_smul]
  mul_smul σ τ v := by
    show SemilinearAut.ofAlgAut (σ * τ) • v
      = SemilinearAut.ofAlgAut σ • (SemilinearAut.ofAlgAut τ • v)
    rw [map_mul, mul_smul]

/-- Pin `Divisor` instance (`Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean:359`). -/
private instance instDistribMulActionAlgEquivDivisor :
    DistribMulAction (F ≃ₐ[K] F) (Divisor K F) :=
  Finsupp.comapDistribMulAction

/-- Pin `Divisor.smul_def` (`Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean:361`). -/
private theorem smul_def (σ : F ≃ₐ[K] F) (D : Divisor K F) :
    σ • D = Finsupp.mapDomain (σ • ·) D := rfl

/-- Pin `Divisor.smul_single` (`Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean:364`). -/
@[simp]
private theorem smul_single (σ : F ≃ₐ[K] F) (v : Place K F) (n : ℤ) :
    σ • Finsupp.single v n = Finsupp.single (σ • v) n := by
  rw [smul_def, Finsupp.mapDomain_single]

/-- Pin `Divisor.smul_apply_smul` (`Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean:369`). -/
private theorem smul_apply_smul (σ : F ≃ₐ[K] F) (D : Divisor K F) (v : Place K F) :
    (σ • D) (σ • v) = D v := by
  rw [smul_def]
  exact Finsupp.mapDomain_apply_of_injective (MulAction.injective σ) D v

/-- Pin `Divisor.smul_apply` (`Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean:374`). -/
private theorem smul_apply (σ : F ≃ₐ[K] F) (D : Divisor K F) (w : Place K F) :
    (σ • D) w = D (σ⁻¹ • w) := by
  have : (σ • D) (σ • (σ⁻¹ • w)) = D (σ⁻¹ • w) := smul_apply_smul σ D (σ⁻¹ • w)
  rwa [smul_inv_smul] at this

/-- Pin `Divisor.degree_smul` (`Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean:380`). -/
@[simp]
private theorem degree_smul (σ : F ≃ₐ[K] F) (D : Divisor K F) : degree (σ • D) = degree D := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add v n D _ _ ih =>
      rw [smul_add, map_add, map_add, ih, smul_single, degree_single, degree_single,
        Place.deg_smul]

end SmulAux

section Pullback

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F']

-- Pin row #237 `Divisor.degree_eq_sum_support` is already provided by the
-- imported `FLTForHuman.AlgebraicCurve.Genus.Index` (`AlgebraicCurve.Divisor.
-- degree_eq_sum_support`, statement identical), so it is not restated here.

/-- Pin row #238. -/
theorem degree_eq_finrank_mul_of_forall_eq_ord_algebraMap
    (H : RamificationInertiaIdentity K F F') {g : F}
    {D' : Divisor K F'} (hD' : ∀ w : Place K F', D' w = w.ord (algebraMap F F' g))
    {D : Divisor K F} (hD : ∀ v : Place K F, D v = v.ord g) :
    degree D' = (Module.finrank F F' : ℤ) * degree D := by
  classical

  have hmaps : ∀ w ∈ D'.support, w.restrict F ∈ D.support := by
    intro w hw
    rw [Finsupp.mem_support_iff] at hw ⊢
    intro h0
    apply hw
    rw [hD' w, w.ord_restrict g, hD] at *
    rw [h0, mul_zero]

  have happ : ∀ w : Place K F', D' w = (w.ramificationIndex F : ℤ) * D (w.restrict F) := by
    intro w
    rw [hD' w, w.ord_restrict g, hD]

  rw [degree_eq_sum_support, degree_eq_sum_support,
    ← Finset.sum_fiberwise_of_maps_to hmaps fun w => D' w * (w.deg : ℤ), Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_

  have hfiber : ∀ w : Place K F',
      w ∈ D'.support.filter (fun w => w.restrict F = v) ↔ w.restrict F = v := by
    intro w
    simp only [Finset.mem_filter, Finsupp.mem_support_iff, and_iff_right_iff_imp]
    intro hw
    rw [happ w, hw]
    have he : 0 < w.ramificationIndex F := w.ramificationIndex_pos
    have hv0 : D v ≠ 0 := Finsupp.mem_support_iff.mp hv
    exact mul_ne_zero (by exact_mod_cast he.ne') hv0

  calc
    ∑ w ∈ D'.support with w.restrict F = v, D' w * (w.deg : ℤ)
        = D v * ∑ w ∈ D'.support.filter (fun w => w.restrict F = v),
            (w.ramificationIndex F : ℤ) * (w.deg : ℤ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun w hw => ?_
          rw [happ w, ((hfiber w).mp hw)]
          ring
    _ = D v * ((Module.finrank F F' : ℤ) * (v.deg : ℤ)) := by
          rw [H v _ hfiber]
    _ = (Module.finrank F F' : ℤ) * (D v * (v.deg : ℤ)) := by ring

end Pullback

section Galois

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']

/-- Pin row #239 (`private`). -/
private theorem _root_.AlgebraicCurve.Place.ord_prod {ι : Type*} (v : Place K F') (s : Finset ι)
    (g : ι → F') (hg : ∀ i ∈ s, g i ≠ 0) :
    v.ord (∏ i ∈ s, g i) = ∑ i ∈ s, v.ord (g i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih =>
    rw [Finset.prod_cons, Finset.sum_cons,
      v.ord_mul (hg i (Finset.mem_cons_self i s))
        (Finset.prod_ne_zero_iff.mpr fun j hj => hg j (Finset.mem_cons_of_mem hj)),
      ih fun j hj => hg j (Finset.mem_cons_of_mem hj)]

variable [FiniteDimensional F F']

/-- Pin row #240. -/
theorem sum_smul_apply_eq_ord_prod {f : F'} (hf : f ≠ 0)
    {D : Divisor K F'} (hD : ∀ w : Place K F', D w = w.ord f) (w : Place K F') :
    (∑ σ : F' ≃ₐ[F] F', (AlgEquiv.restrictScalars K σ) • D) w
      = w.ord (∏ σ : F' ≃ₐ[F] F', σ f) := by
  classical
  rw [w.ord_prod _ _ fun σ _ => by simpa using hf, Finset.sum_apply']
  refine Finset.sum_congr rfl fun σ _ => ?_

  rw [smul_apply, hD]
  have h := Place.ord_smul (AlgEquiv.restrictScalars K σ)
    ((AlgEquiv.restrictScalars K σ)⁻¹ • w) f
  rw [smul_inv_smul] at h
  exact h.symm

/-- Pin row #241. -/
theorem degree_eq_zero_of_isGalois [IsGalois F F'] [HasPrincipalDivisors K F]
    (H : RamificationInertiaIdentity K F F')
    {f : F'} {D : Divisor K F'} (hD : ∀ w : Place K F', D w = w.ord f) :
    degree D = 0 := by
  classical

  rcases eq_or_ne f 0 with rfl | hf
  · have : D = 0 := Finsupp.ext fun w => by simpa using hD w
    rw [this, _root_.map_zero]

  set E : Divisor K F' := ∑ σ : F' ≃ₐ[F] F', (AlgEquiv.restrictScalars K σ) • D with hE

  have hEord : ∀ w : Place K F', E w = w.ord (algebraMap F F' (Algebra.norm F f)) := by
    intro w
    rw [hE, sum_smul_apply_eq_ord_prod hf hD w, Algebra.norm_eq_prod_automorphisms F f]

  have hnorm : Algebra.norm F f ≠ 0 := (Algebra.norm_ne_zero_iff (R := F)).mpr hf
  obtain ⟨D₀, hD₀, hD₀deg⟩ := HasPrincipalDivisors.exists_divisor (K := K)
    (Algebra.norm F f) hnorm

  have hEdeg : degree E = 0 := by
    rw [degree_eq_finrank_mul_of_forall_eq_ord_algebraMap H hEord hD₀, hD₀deg, mul_zero]

  have hEdeg' : degree E = (Module.finrank F F' : ℤ) * degree D := by
    rw [hE, map_sum]
    simp only [degree_smul]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    congr 1
    exact_mod_cast (Nat.card_eq_fintype_card (α := F' ≃ₐ[F] F')).symm.trans
      (IsGalois.card_aut_eq_finrank F F')

  have hpos : (0 : ℤ) < (Module.finrank F F' : ℤ) := by
    exact_mod_cast Module.finrank_pos (R := F) (M := F')
  rw [hEdeg] at hEdeg'
  exact (mul_eq_zero.mp hEdeg'.symm).resolve_left hpos.ne'

end Galois

end Divisor

namespace RationalFunctionField

section Descent

variable {K : Type*} [Field K] {F' : Type*} [Field F'] [Algebra K F']
  [Algebra (RatFunc K) F'] [IsScalarTower K (RatFunc K) F']
  [FiniteDimensional (RatFunc K) F'] [Algebra.IsSeparable (RatFunc K) F']

/-- Pin row #242. -/
def principalDivisorOf {f : F'} (hf : f ≠ 0) : Divisor K F' :=
  ⟨(finite_setOf_ord_ne_zero_of_finiteDimensional hf).toFinset, fun w => w.ord f, fun w => by
    simp [Set.Finite.mem_toFinset]⟩

/-- Pin row #243. -/
theorem degree_eq_zero_of_forall_eq_ord_of_isGalois [IsGalois (RatFunc K) F']
    (H : RamificationInertiaIdentity K (RatFunc K) F')
    {f : F'} {D : Divisor K F'} (hD : ∀ w : Place K F', D w = w.ord f) :
    Divisor.degree D = 0 :=
  Divisor.degree_eq_zero_of_isGalois H hD

/-- Pin row #244. -/
theorem hasPrincipalDivisors_of_isGalois [IsGalois (RatFunc K) F']
    (H : RamificationInertiaIdentity K (RatFunc K) F') :
    HasPrincipalDivisors K F' where
  exists_divisor _ hf :=
    ⟨principalDivisorOf hf, fun _ => rfl,
      degree_eq_zero_of_forall_eq_ord_of_isGalois H fun _ => rfl⟩

end Descent

end RationalFunctionField

section SurjectivePlaceInfty

variable (K) [DecidableEq (RatFunc K)]

/-- Pin row #245. -/
theorem surjective_algebraMap_residueField_placeInfty :
    Function.Surjective (algebraMap K (p1PlaceInfty K).ResidueField) := by
  intro z
  obtain ⟨c, hc⟩ :=
    (finrank_eq_one_iff_of_nonzero' (1 : (p1PlaceInfty K).ResidueField) one_ne_zero).mp
      (show Module.finrank K (p1PlaceInfty K).ResidueField = 1 from deg_placeInfty K) z
  exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc⟩

end SurjectivePlaceInfty

section NamedRow

variable (K F)
variable [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

/-- Pin row #246. -/
def CanonicalLocalResidueKDifferentialCoordIndep : Prop :=
  ∀ (v : Place K F) (π' : F), v.ord π' = 1 →
    ∀ (R : v.CanonicalLocalResidueDataK) (n : ℕ), 1 ≤ n →
      R.res (v.differentialCoeff (KaehlerDifferential.D K F π') * ((π') ^ (n + 1))⁻¹) = 0

end NamedRow

section XInvCoordinate

variable (K) [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

omit [DecidableEq (RatFunc K)]
  [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]] in

/-- Pin row #247. -/
theorem ratFuncX_inv_pow_inv (m : ℕ) :
    (((RatFunc.X : RatFunc K)⁻¹) ^ m)⁻¹ = (RatFunc.X : RatFunc K) ^ m := by
  rw [inv_pow, inv_inv]

/-- Pin row #248. -/
theorem X_pow_mul_differentialCoeff_D_X_eq_neg (n : ℕ) :
    (RatFunc.X : RatFunc K) ^ n
        * (p1PlaceInfty K).differentialCoeff (KaehlerDifferential.D K (RatFunc K) RatFunc.X)
      = -((p1PlaceInfty K).differentialCoeff
            (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹)
          * (((RatFunc.X : RatFunc K)⁻¹) ^ (n + 2))⁻¹) := by
  rw [ratFuncX_inv_pow_inv, differentialCoeff_placeInfty_D_X_eq K]
  ring

end XInvCoordinate

section Bridge

variable (K) [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

/-- Pin row #249. -/
theorem canonicalLocalResidueDataK_res_X_pow_mul_D_X_of_coordIndep
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K))
    (R : (p1PlaceInfty K).CanonicalLocalResidueDataK) (n : ℕ) :
    R.res ((RatFunc.X : RatFunc K) ^ n
        * (p1PlaceInfty K).differentialCoeff
            (KaehlerDifferential.D K (RatFunc K) RatFunc.X)) = 0 := by
  rw [X_pow_mul_differentialCoeff_D_X_eq_neg K n, _root_.map_neg, neg_eq_zero]
  exact hcoord (p1PlaceInfty K) (RatFunc.X : RatFunc K)⁻¹ (ord_placeInfty_X_inv K) R (n + 1)
    (by omega)

/-- Pin row #250. -/
theorem canonicalLocalResidueDataK_kaehlerResidueTerm_X_pow_of_coordIndep
    (_hwd : OrdDifferentialWellDefined K (RatFunc K))
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K))
    (R : (p1PlaceInfty K).CanonicalLocalResidueDataK) (n : ℕ) :
    Algebra.trace K (p1PlaceInfty K).ResidueField
        (R.res (diagonalHom K (RatFunc K) ((RatFunc.X : RatFunc K) ^ n) (p1PlaceInfty K)
          * (p1PlaceInfty K).differentialCoeff
              (KaehlerDifferential.D K (RatFunc K) RatFunc.X))) = 0 := by
  rw [diagonalHom_apply,
    canonicalLocalResidueDataK_res_X_pow_mul_D_X_of_coordIndep K hcoord R n, _root_.map_zero]

end Bridge

end AlgebraicCurve

end

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.overlappingInstances false
noncomputable section

open Polynomial IsDedekindDomain WithZero IsLocalRing UniqueFactorizationMonoid
open scoped Polynomial

namespace AlgebraicCurve

open RationalFunctionField

namespace Place

/-- Local copy of the pin `private Place.ord_add_eq_left` (pin line 829); the
chunk-1 copy is `private` in this same module and not reachable by name. -/
private theorem ord_add_eq_left' {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (h : v.ord f < v.ord g) :
    v.ord (f + g) = v.ord f := by
  have hfv := v.adicValuation_ne_zero hf
  have hgv := v.adicValuation_ne_zero hg
  have hlt : v.adicValuation g < v.adicValuation f := by
    rw [← exp_log hfv, ← exp_log hgv]
    have hlog : log (v.adicValuation g) < log (v.adicValuation f) := by
      simp only [ord] at h
      omega
    exact lt_of_le_of_ne (exp_le_exp.mpr hlog.le)
      fun hcon => hlog.ne (exp_injective hcon)
  have h1 : v.adicValuation (f + g) = max (v.adicValuation f) (v.adicValuation g) :=
    Valuation.map_add_of_distinct_val _ (ne_of_lt hlt).symm
  rw [max_eq_left hlt.le] at h1
  simp only [ord, h1]

end Place

section WronskianBound

variable {K : Type*} [Field K]

theorem natDegree_numDenomWronskian_lt {n d : K[X]} (hn : n ≠ 0) (hd : d ≠ 0)
    (hW : n.derivative * d - n * d.derivative ≠ 0) :
    (n.derivative * d - n * d.derivative).natDegree < n.natDegree + d.natDegree := by
  have hdeg : (n.derivative * d - n * d.derivative).degree < (n * d).degree := by
    rw [Polynomial.degree_mul]
    refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt ?_ ?_)
    · refine lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_
      rw [WithBot.add_lt_add_iff_right (Polynomial.degree_ne_bot.mpr hd)]
      exact Polynomial.degree_derivative_lt hn
    · refine lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_
      rw [WithBot.add_lt_add_iff_left (Polynomial.degree_ne_bot.mpr hn)]
      exact Polynomial.degree_derivative_lt hd
  have h2 := Polynomial.natDegree_lt_natDegree hW hdeg
  rwa [Polynomial.natDegree_mul hn hd] at h2

end WronskianBound

section DXCoeff

variable (K : Type*) [Field K]

def ratFuncDXCoeff (f : RatFunc K) : RatFunc K :=
  algebraMap K[X] (RatFunc K) (f.num.derivative * f.denom - f.num * f.denom.derivative)
    / (algebraMap K[X] (RatFunc K) f.denom) ^ 2

theorem ratFuncDXCoeff_def (f : RatFunc K) :
    ratFuncDXCoeff K f
      = algebraMap K[X] (RatFunc K) (f.num.derivative * f.denom - f.num * f.denom.derivative)
        / (algebraMap K[X] (RatFunc K) f.denom) ^ 2 := rfl

theorem D_eq_ratFuncDXCoeff_smul_dX (f : RatFunc K) :
    KaehlerDifferential.D K (RatFunc K) f = ratFuncDXCoeff K f • dX K := by
  have hd : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero f.denom_ne_zero
  rw [ratFuncDXCoeff_def, div_eq_mul_inv, mul_comm, mul_smul, ← denom_sq_smul_D_eq K f,
    smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 hd), one_smul]

theorem wronskian_ne_zero_of_ratFuncDXCoeff_ne_zero {f : RatFunc K}
    (h : ratFuncDXCoeff K f ≠ 0) :
    f.num.derivative * f.denom - f.num * f.denom.derivative ≠ 0 := by
  intro h0
  exact h (by rw [ratFuncDXCoeff_def, h0, _root_.map_zero, zero_div])

end DXCoeff

section FinitePlaces

variable {K : Type*} [Field K]
variable {w : HeightOneSpectrum K[X]}

local notation "v" => Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w

theorem ord_algebraMap_denom_eq_zero_of_ord_eq_one {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) {f : RatFunc K}
    (hf : f ≠ 0) (hord : (v).ord f = 1) :
    (v).ord (algebraMap K[X] (RatFunc K) f.denom) = 0 := by
  by_contra hne

  have hpd : p ∣ f.denom := by
    rw [← Ideal.mem_span_singleton, ← hwp]
    exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
      f.denom_ne_zero).mp hne
  have hpn : ¬ p ∣ f.num := fun hpn =>
    hp.not_isUnit (f.isCoprime_num_denom.isUnit_of_dvd' hpn hpd)
  have hordn : (v).ord (algebraMap K[X] (RatFunc K) f.num) = 0 := by
    by_contra h
    exact hpn (by
      rw [← Ideal.mem_span_singleton, ← hwp]
      exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
        (RatFunc.num_ne_zero hf)).mp h)
  have hordd : 0 < (v).ord (algebraMap K[X] (RatFunc K) f.denom) :=
    lt_of_le_of_ne ((v).ord_nonneg_of_mem (algebraMap_mem_ofHeightOneSpectrum K w _))
      (Ne.symm hne)

  have hnum0 : algebraMap K[X] (RatFunc K) f.num ≠ 0 :=
    RatFunc.algebraMap_ne_zero (RatFunc.num_ne_zero hf)
  have hden0 : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero f.denom_ne_zero
  rw [← f.num_div_denom, div_eq_mul_inv, (v).ord_mul hnum0 (inv_ne_zero hden0),
    (v).ord_inv, hordn] at hord
  omega

theorem ord_algebraMap_num_eq_one_of_ord_eq_one {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) {f : RatFunc K}
    (hf : f ≠ 0) (hord : (v).ord f = 1) :
    (v).ord (algebraMap K[X] (RatFunc K) f.num) = 1 := by
  have hnum0 : algebraMap K[X] (RatFunc K) f.num ≠ 0 :=
    RatFunc.algebraMap_ne_zero (RatFunc.num_ne_zero hf)
  have hden0 : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero f.denom_ne_zero
  have h := hord
  rw [← f.num_div_denom, div_eq_mul_inv, (v).ord_mul hnum0 (inv_ne_zero hden0),
    (v).ord_inv, ord_algebraMap_denom_eq_zero_of_ord_eq_one hp hwp hf hord] at h
  omega

theorem not_dvd_wronskian_of_ord_eq_one {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) (hsep : p.Separable)
    {f : RatFunc K} (hf : f ≠ 0) (hord : (v).ord f = 1) :
    ¬ p ∣ (f.num.derivative * f.denom - f.num * f.denom.derivative) := by
  have hpn' : ¬ p ∣ f.num.derivative :=
    not_dvd_derivative_of_ord_eq_one hp hwp hsep (RatFunc.num_ne_zero hf)
      (ord_algebraMap_num_eq_one_of_ord_eq_one hp hwp hf hord)
  have hpd : ¬ p ∣ f.denom := fun hpd => by
    have h0 := ord_algebraMap_denom_eq_zero_of_ord_eq_one hp hwp hf hord
    rw [← Ideal.mem_span_singleton, ← hwp] at hpd
    exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
      f.denom_ne_zero).mpr hpd h0
  have hpn : p ∣ f.num := by
    rw [← Ideal.mem_span_singleton, ← hwp]
    refine (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
      (RatFunc.num_ne_zero hf)).mp ?_
    rw [ord_algebraMap_num_eq_one_of_ord_eq_one hp hwp hf hord]
    exact one_ne_zero
  intro hdvd

  have hpnd' : p ∣ f.num * f.denom.derivative := hpn.mul_right _
  have hpn'd : p ∣ f.num.derivative * f.denom := by
    have h1 := dvd_add hdvd hpnd'
    rwa [sub_add_cancel] at h1
  rcases hp.prime.dvd_mul.mp hpn'd with h | h
  · exact hpn' h
  · exact hpd h

theorem ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) (hsep : p.Separable)
    {f : RatFunc K} (hf : f ≠ 0) (hord : (v).ord f = 1) :
    ratFuncDXCoeff K f ≠ 0 ∧ (v).ord (ratFuncDXCoeff K f) = 0 := by
  have hW : ¬ p ∣ (f.num.derivative * f.denom - f.num * f.denom.derivative) :=
    not_dvd_wronskian_of_ord_eq_one hp hwp hsep hf hord
  have hξ0 : f.num.derivative * f.denom - f.num * f.denom.derivative ≠ 0 := fun h =>
    hW (h ▸ dvd_zero p)
  have hd0 : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero f.denom_ne_zero
  have hξ0' : algebraMap K[X] (RatFunc K)
      (f.num.derivative * f.denom - f.num * f.denom.derivative) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hξ0

  have hordξ : (v).ord (algebraMap K[X] (RatFunc K)
      (f.num.derivative * f.denom - f.num * f.denom.derivative)) = 0 := by
    by_contra h
    refine hW ?_
    rw [← Ideal.mem_span_singleton, ← hwp]
    exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w hξ0).mp h
  refine ⟨div_ne_zero hξ0' (pow_ne_zero 2 hd0), ?_⟩
  rw [ratFuncDXCoeff_def, div_eq_mul_inv,
    (v).ord_mul hξ0' (inv_ne_zero (pow_ne_zero 2 hd0)), (v).ord_inv, hordξ,
    ← zpow_natCast, (v).ord_zpow,
    ord_algebraMap_denom_eq_zero_of_ord_eq_one hp hwp hf hord]
  ring

end FinitePlaces

section PlaceInftySide

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]

theorem ord_placeInfty_ratFuncDXCoeff_ge {g : RatFunc K} (hg : g ≠ 0)
    (hW : g.num.derivative * g.denom - g.num * g.denom.derivative ≠ 0) :
    (p1PlaceInfty K).ord g + 1 ≤ (p1PlaceInfty K).ord (ratFuncDXCoeff K g) := by
  have hn0 : g.num ≠ 0 := RatFunc.num_ne_zero hg
  have hd0 : g.denom ≠ 0 := g.denom_ne_zero
  have hW' : algebraMap K[X] (RatFunc K)
      (g.num.derivative * g.denom - g.num * g.denom.derivative) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hW
  have hd' : algebraMap K[X] (RatFunc K) g.denom ≠ 0 := RatFunc.algebraMap_ne_zero hd0

  have hdeg : (g.num.derivative * g.denom - g.num * g.denom.derivative).natDegree
      < g.num.natDegree + g.denom.natDegree :=
    natDegree_numDenomWronskian_lt hn0 hd0 hW

  have hcoeff : (p1PlaceInfty K).ord (ratFuncDXCoeff K g)
      = 2 * (g.denom.natDegree : ℤ)
        - (g.num.derivative * g.denom - g.num * g.denom.derivative).natDegree := by
    rw [ratFuncDXCoeff_def, ord_placeInfty (div_ne_zero hW' (pow_ne_zero 2 hd')),
      RatFunc.intDegree_div hW' (pow_ne_zero 2 hd'), RatFunc.intDegree_polynomial,
      ← map_pow, RatFunc.intDegree_polynomial, Polynomial.natDegree_pow]
    push_cast
    ring

  have hgord : (p1PlaceInfty K).ord g = (g.denom.natDegree : ℤ) - g.num.natDegree := by
    rw [ord_placeInfty hg, RatFunc.intDegree]
    ring
  rw [hcoeff, hgord]
  omega

theorem exists_dXCoeff_ord_ge_two_of_ord_placeInfty_eq_zero {g : RatFunc K}
    (hg : g ≠ 0) (hord : (p1PlaceInfty K).ord g = 0) :
    ∃ e : RatFunc K, (e = 0 ∨ 2 ≤ (p1PlaceInfty K).ord e) ∧
      KaehlerDifferential.D K (RatFunc K) g = e • dX K := by

  have hmem : RatFunc.inftyValuation K g ≤ 1 := by
    have h1 : g ∈ (p1PlaceInfty K).toValuationSubring :=
      (p1PlaceInfty K).mem_of_ord_nonneg hg hord.symm.le
    rwa [p1PlaceInfty_toValuationSubring, Valuation.mem_valuationSubring_iff] at h1

  obtain ⟨c, hc⟩ := exists_sub_algebraMap_intDegree_neg K hmem

  have hDg : KaehlerDifferential.D K (RatFunc K) g
      = KaehlerDifferential.D K (RatFunc K) (g - algebraMap K (RatFunc K) c) := by
    rw [map_sub, Derivation.map_algebraMap (KaehlerDifferential.D K (RatFunc K)) c, sub_zero]
  rcases hc with hc0 | hcneg
  ·
    exact ⟨0, Or.inl rfl, by rw [hDg, hc0, _root_.map_zero, zero_smul]⟩
  ·
    have hg₁0 : g - algebraMap K (RatFunc K) c ≠ 0 := by
      intro h0
      rw [h0] at hcneg
      simp at hcneg
    refine ⟨ratFuncDXCoeff K (g - algebraMap K (RatFunc K) c), ?_,
      by rw [hDg, D_eq_ratFuncDXCoeff_smul_dX]⟩
    rcases eq_or_ne (ratFuncDXCoeff K (g - algebraMap K (RatFunc K) c)) 0 with h0 | h0
    · exact Or.inl h0
    · refine Or.inr ?_
      have hW := wronskian_ne_zero_of_ratFuncDXCoeff_ne_zero K h0
      have hge := ord_placeInfty_ratFuncDXCoeff_ge hg₁0 hW
      have hord₁ : 1 ≤ (p1PlaceInfty K).ord (g - algebraMap K (RatFunc K) c) := by
        rw [ord_placeInfty hg₁0]
        omega
      omega

theorem exists_unit_dXCoeff_of_ord_placeInfty_eq_neg_one {h : RatFunc K}
    (hh : h ≠ 0) (hord : (p1PlaceInfty K).ord h = -1) :
    ∃ b : RatFunc K, b ≠ 0 ∧ (p1PlaceInfty K).ord b = 0 ∧
      KaehlerDifferential.D K (RatFunc K) h = b • dX K := by
  have hX : (RatFunc.X : RatFunc K) ≠ 0 := RatFunc.X_ne_zero
  have hXinv : (RatFunc.X : RatFunc K)⁻¹ ≠ 0 := inv_ne_zero hX

  have hg0 : h * (RatFunc.X : RatFunc K)⁻¹ ≠ 0 := mul_ne_zero hh hXinv
  have hordg : (p1PlaceInfty K).ord (h * (RatFunc.X : RatFunc K)⁻¹) = 0 := by
    rw [(p1PlaceInfty K).ord_mul hh hXinv, (p1PlaceInfty K).ord_inv, ord_placeInfty_X, hord]
    ring
  obtain ⟨e, he, hDe⟩ := exists_dXCoeff_ord_ge_two_of_ord_placeInfty_eq_zero hg0 hordg

  have hh_eq : h = h * (RatFunc.X : RatFunc K)⁻¹ * RatFunc.X := by
    rw [mul_assoc, inv_mul_cancel₀ hX, mul_one]
  have hDh : KaehlerDifferential.D K (RatFunc K) h
      = (h * (RatFunc.X : RatFunc K)⁻¹ + RatFunc.X * e) • dX K := by
    conv_lhs => rw [hh_eq]
    rw [Derivation.leibniz, hDe, smul_smul,
      show KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K) = dX K from rfl,
      ← add_smul]
  rcases he with rfl | he2
  ·
    refine ⟨h * (RatFunc.X : RatFunc K)⁻¹ + RatFunc.X * 0, ?_, ?_, hDh⟩
    · rw [mul_zero, add_zero]
      exact hg0
    · rw [mul_zero, add_zero]
      exact hordg
  ·
    have he0 : e ≠ 0 := by
      intro h0
      rw [h0, (p1PlaceInfty K).ord_zero] at he2
      omega
    have hXe0 : (RatFunc.X : RatFunc K) * e ≠ 0 := mul_ne_zero hX he0
    have hlt : (p1PlaceInfty K).ord (h * (RatFunc.X : RatFunc K)⁻¹)
        < (p1PlaceInfty K).ord ((RatFunc.X : RatFunc K) * e) := by
      rw [hordg, (p1PlaceInfty K).ord_mul hX he0, ord_placeInfty_X]
      omega
    refine ⟨h * (RatFunc.X : RatFunc K)⁻¹ + RatFunc.X * e, ?_, ?_, hDh⟩
    ·
      intro hsum
      have hXe_eq : (RatFunc.X : RatFunc K) * e = -(h * (RatFunc.X : RatFunc K)⁻¹) := by
        linear_combination hsum
      rw [hXe_eq, (p1PlaceInfty K).ord_neg] at hlt
      exact lt_irrefl _ hlt
    · rw [(p1PlaceInfty K).ord_add_eq_left' hg0 hXe0 hlt]
      exact hordg

theorem exists_dXCoeff_ord_two_of_ord_placeInfty_eq_one {f : RatFunc K}
    (hf : f ≠ 0) (hord : (p1PlaceInfty K).ord f = 1) :
    ∃ e : RatFunc K, e ≠ 0 ∧ (p1PlaceInfty K).ord e = 2 ∧
      KaehlerDifferential.D K (RatFunc K) f = e • dX K := by

  have hf' : f⁻¹ ≠ 0 := inv_ne_zero hf
  have hord' : (p1PlaceInfty K).ord f⁻¹ = -1 := by
    rw [(p1PlaceInfty K).ord_inv, hord]
  obtain ⟨b, hb0, hbord, hDb⟩ := exists_unit_dXCoeff_of_ord_placeInfty_eq_neg_one hf' hord'
  refine ⟨-(f ^ 2 * b), neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 2 hf) hb0), ?_, ?_⟩
  · rw [(p1PlaceInfty K).ord_neg, (p1PlaceInfty K).ord_mul (pow_ne_zero 2 hf) hb0, hbord,
      add_zero, ← zpow_natCast, (p1PlaceInfty K).ord_zpow, hord]
    norm_num
  ·
    conv_lhs => rw [← inv_inv f]
    rw [(KaehlerDifferential.D K (RatFunc K)).leibniz_inv f⁻¹, hDb, inv_inv, smul_smul,
      neg_mul]

end PlaceInftySide

section Glue

variable {K : Type*} [Field K]

theorem exists_ord_zero_smul_of_smul_dX_eq {v : Place K (RatFunc K)} {π π' c c' : RatFunc K}
    (hc : c ≠ 0) (hc' : c' ≠ 0) (hord : v.ord c' = v.ord c)
    (hD : KaehlerDifferential.D K (RatFunc K) π = c • dX K)
    (hD' : KaehlerDifferential.D K (RatFunc K) π' = c' • dX K) :
    ∃ u : RatFunc K, v.ord u = 0 ∧
      KaehlerDifferential.D K (RatFunc K) π' = u • KaehlerDifferential.D K (RatFunc K) π := by
  refine ⟨c' / c, ?_, ?_⟩
  · rw [div_eq_mul_inv, v.ord_mul hc' (inv_ne_zero hc), v.ord_inv, hord]
    ring
  · rw [hD, hD', smul_smul, div_mul_cancel₀ _ hc]

end Glue

theorem ordDifferentialWellDefined_ratFunc (K : Type*) [Field K] [CharZero K] :
    OrdDifferentialWellDefined K (RatFunc K) := by
  classical
  intro v π π' hπ hπ'

  have hπ0 : π ≠ 0 := by
    intro h
    rw [h, v.ord_zero] at hπ
    exact zero_ne_one hπ
  have hπ'0 : π' ≠ 0 := by
    intro h
    rw [h, v.ord_zero] at hπ'
    exact zero_ne_one hπ'

  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  ·
    obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
    obtain ⟨h1ne, h1ord⟩ :=
      ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one hp hwp hp.separable hπ0 hπ
    obtain ⟨h2ne, h2ord⟩ :=
      ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one hp hwp hp.separable hπ'0 hπ'
    exact exists_ord_zero_smul_of_smul_dX_eq h1ne h2ne (h2ord.trans h1ord.symm)
      (D_eq_ratFuncDXCoeff_smul_dX K π) (D_eq_ratFuncDXCoeff_smul_dX K π')
  ·
    obtain ⟨e, he0, heord, hDe⟩ := exists_dXCoeff_ord_two_of_ord_placeInfty_eq_one hπ0 hπ
    obtain ⟨e', he'0, he'ord, hDe'⟩ := exists_dXCoeff_ord_two_of_ord_placeInfty_eq_one hπ'0 hπ'
    exact exists_ord_zero_smul_of_smul_dX_eq he0 he'0 (he'ord.trans heord.symm) hDe hDe'

section ConsumerGates

variable (K : Type*) [Field K] [CharZero K] [DecidableEq (RatFunc K)]
variable [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

end ConsumerGates

section NonVacuity

variable (K : Type*) [Field K]

end NonVacuity

section PrincipalPartAtoms

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]

variable (K)

theorem two_le_ord_placeInfty_p1PrincipalPartAtom
    {p : K[X]} (hp : Irreducible p) {c : K[X]} (hc : c ≠ 0) {m : ℕ}
    (hdeg : c.degree < p.degree) (hm : 2 ≤ m) :
    2 ≤ (p1PlaceInfty K).ord (p1PrincipalPartAtom K p c m) := by
  rw [ord_placeInfty_p1PrincipalPartAtom K hp.ne_zero hc]
  have hndeg : c.natDegree < p.natDegree :=
    Polynomial.natDegree_lt_natDegree hc hdeg
  have hpdeg : 1 ≤ (p.natDegree : ℤ) := by exact_mod_cast hp.natDegree_pos
  have hm' : 2 ≤ (m : ℤ) := by exact_mod_cast hm
  nlinarith

omit [DecidableEq (RatFunc K)] in

theorem not_dvd_of_degree_lt {p c : K[X]} (hc : c ≠ 0)
    (hdeg : c.degree < p.degree) : ¬ p ∣ c :=
  fun hdvd => not_lt.mpr (Polynomial.degree_le_of_dvd hdvd hc) hdeg

omit [DecidableEq (RatFunc K)] in

theorem ord_finitePlace_of_degree_lt {p : K[X]} (hp : Irreducible p) {c : K[X]} (hc : c ≠ 0)
    (hdeg : c.degree < p.degree) :
    (finitePlace K hp).ord (algebraMap K[X] (RatFunc K) c) = 0 :=
  not_ne_iff.mp fun h =>
    not_dvd_of_degree_lt K hc hdeg ((ord_finitePlace_ne_zero_iff K hp hc).mp h)

omit [DecidableEq (RatFunc K)] in

theorem ord_finitePlace_p1PrincipalPartAtom {p : K[X]} (hp : Irreducible p)
    {c : K[X]} (hc : c ≠ 0) (hdeg : c.degree < p.degree) (m : ℕ) :
    (finitePlace K hp).ord (p1PrincipalPartAtom K p c m) = -(m : ℤ) := by
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hp' : algebraMap K[X] (RatFunc K) p ≠ 0 := (map_ne_zero_iff _ hinj).mpr hp.ne_zero
  have hc' : algebraMap K[X] (RatFunc K) c ≠ 0 := (map_ne_zero_iff _ hinj).mpr hc
  unfold p1PrincipalPartAtom
  rw [div_eq_mul_inv, (finitePlace K hp).ord_mul hc' (inv_ne_zero (pow_ne_zero m hp')),
    (finitePlace K hp).ord_inv, ← zpow_natCast, (finitePlace K hp).ord_zpow,
    ord_finitePlace_of_degree_lt K hp hc hdeg, ord_finitePlace_self K hp]
  ring

end PrincipalPartAtoms

end AlgebraicCurve

end

noncomputable section

open Polynomial IsDedekindDomain WithZero IsLocalRing UniqueFactorizationMonoid
open Module

namespace AlgebraicCurve

section UnitFinite

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]

open RationalFunctionField

def P1DifferentialCoeffUnitFinite {ω₀ : Ω[(RatFunc K)⁄K]} (_hω₀ : ω₀ ≠ 0) : Prop :=
  ∀ v : Place K (RatFunc K), v ≠ p1PlaceInfty K → v.ord (v.differentialCoeff ω₀) = 0

variable {K}

theorem p1DifferentialCoeffRegularFinite_of_unitFinite
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0)
    (hunit : P1DifferentialCoeffUnitFinite K hω₀) :
    P1DifferentialCoeffRegularFinite K hω₀ :=
  fun v hv => v.mem_of_ord_nonneg (v.differentialCoeff_ne_zero hω₀) (hunit v hv).ge

end UnitFinite

section KaehlerRatFunc

variable (K : Type*) [Field K]

open KaehlerDifferential

def kaehlerPolynomialBasis : Basis Unit K[X] Ω[K[X]⁄K] :=
  (Basis.singleton Unit K[X]).map (KaehlerDifferential.polynomialEquiv K).symm

scoped instance instFormallyEtalePolynomialRatFunc : Algebra.FormallyEtale K[X] (RatFunc K) :=
  Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors K[X])

def kaehlerRatFuncBasis : Basis Unit (RatFunc K) Ω[(RatFunc K)⁄K] :=
  ((kaehlerPolynomialBasis K).baseChange (RatFunc K)).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K K[X] (RatFunc K))

theorem kaehlerRankOne_ratFunc : KaehlerRankOne K (RatFunc K) :=
  ⟨Module.Free.of_basis (kaehlerRatFuncBasis K),
    (Module.finrank_eq_card_basis (kaehlerRatFuncBasis K)).trans (by simp)⟩

scoped instance instIsCurveOverRatFunc : IsCurveOver K (RatFunc K) :=
  RationalFunctionField.isCurveOver_of_kaehlerRankOne K (kaehlerRankOne_ratFunc K)

end KaehlerRatFunc

namespace Place

attribute [local instance 0] valuationSubringAlgebra

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

theorem sum_ramificationIndex_mul_inertiaDeg_of_forall_mem_iff
    (v : Place K F) (s : Finset (Place K F'))
    (hs : ∀ w : Place K F', w ∈ s ↔ w.restrict F = v) :
    ∑ w ∈ s, (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ)
      = (Module.finrank F F' : ℤ) := by
  classical
  haveI hfin : Fintype ↥((IsLocalRing.maximalIdeal v.toValuationSubring).primesOver
      (integralClosureAt F' v)) :=
    (IsDedekindDomain.coe_primesOverFinset (maximalIdeal_ne_bot v) (integralClosureAt F' v)) ▸
      (IsDedekindDomain.primesOverFinset (IsLocalRing.maximalIdeal v.toValuationSubring)
        (integralClosureAt F' v)).finite_toSet.fintype
  have hkey := Ideal.sum_ramification_inertia_eq_finrank
    (p := IsLocalRing.maximalIdeal v.toValuationSubring) (integralClosureAt F' v)
  rw [← IsFractionRing.finrank_eq v.toValuationSubring F (integralClosureAt F' v) F'] at hkey
  have hconv : (∑ q : ↥((IsLocalRing.maximalIdeal v.toValuationSubring).primesOver
        (integralClosureAt F' v)),
        q.1.ramificationIdx v.toValuationSubring * q.1.inertiaDeg v.toValuationSubring)
      = ∑ P ∈ IsDedekindDomain.primesOverFinset (IsLocalRing.maximalIdeal v.toValuationSubring)
          (integralClosureAt F' v),
          P.ramificationIdx v.toValuationSubring * P.inertiaDeg v.toValuationSubring :=
    (Finset.sum_subtype
      (IsDedekindDomain.primesOverFinset (IsLocalRing.maximalIdeal v.toValuationSubring)
        (integralClosureAt F' v))
      (fun P => IsDedekindDomain.mem_primesOverFinset_iff (maximalIdeal_ne_bot v) (P := P))
      (fun P => P.ramificationIdx v.toValuationSubring * P.inertiaDeg v.toValuationSubring)).symm
  rw [← hkey]
  rw [hconv]
  push_cast
  refine Finset.sum_bij
    (fun w hw => (fiberCenter F' v ((hs w).mp hw)).asIdeal) ?_ ?_ ?_ ?_
  ·
    intro w hw
    rw [IsDedekindDomain.mem_primesOverFinset_iff (maximalIdeal_ne_bot v)]
    exact ⟨(fiberCenter F' v ((hs w).mp hw)).isPrime,
      fiberCenter_liesOver ((hs w).mp hw)⟩
  ·
    intro w hw w' hw' h
    exact eq_of_fiberCenter_eq ((hs w).mp hw) ((hs w').mp hw')
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
      (hs _).mpr (restrict_placeOfPrime ⟨P, hP1, hPne⟩), ?_⟩
    exact congrArg HeightOneSpectrum.asIdeal
      (fiberCenter_placeOfPrime (⟨P, hP1, hPne⟩ :
        HeightOneSpectrum (integralClosureAt F' v)))
  ·
    intro w hw
    have hwr := (hs w).mp hw
    haveI : (fiberCenter F' v hwr).asIdeal.LiesOver
        (IsLocalRing.maximalIdeal v.toValuationSubring) := fiberCenter_liesOver hwr
    rw [ramificationIndex_eq_ramificationIdx_fiberCenter hwr,
      inertiaDeg_eq_inertiaDeg_fiberCenter hwr,
      Ideal.ramificationIdx'_eq_ramificationIdx (IsLocalRing.maximalIdeal v.toValuationSubring)
        (fiberCenter F' v hwr).asIdeal (maximalIdeal_ne_bot v),
      Ideal.inertiaDeg'_eq_inertiaDeg _ _]

theorem sum_ramificationIndex_mul_deg_of_forall_mem_iff
    (v : Place K F) (s : Finset (Place K F'))
    (hs : ∀ w : Place K F', w ∈ s ↔ w.restrict F = v) :
    ∑ w ∈ s, (w.ramificationIndex F : ℤ) * (w.deg : ℤ)
      = (Module.finrank F F' : ℤ) * (v.deg : ℤ) := by
  have hsum := sum_ramificationIndex_mul_inertiaDeg_of_forall_mem_iff v s hs
  calc ∑ w ∈ s, (w.ramificationIndex F : ℤ) * (w.deg : ℤ)
      = ∑ w ∈ s, (v.deg : ℤ) * ((w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ)) := by
        refine Finset.sum_congr rfl fun w hw => ?_
        have hdeg : (w.restrict F).deg * w.inertiaDeg F = w.deg :=
          deg_restrict_mul_inertiaDeg (K := K) (F := F) (w := w)
        rw [(hs w).mp hw] at hdeg
        rw [← hdeg]
        push_cast
        ring
    _ = (v.deg : ℤ) * ∑ w ∈ s, (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ) := by
        rw [Finset.mul_sum]
    _ = (Module.finrank F F' : ℤ) * (v.deg : ℤ) := by rw [hsum]; ring

end Place

theorem ramificationInertiaIdentity_of_finiteDimensional
    (K F F' : Type*) [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F'] :
    RamificationInertiaIdentity K F F' := fun v s hs =>
  Place.sum_ramificationIndex_mul_deg_of_forall_mem_iff v s hs

section PCoordinateIdentity

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

open RationalFunctionField

theorem derivative_monic_natDegree_one_eq_one {p : K[X]} (hpmon : p.Monic)
    (hdeg : p.natDegree = 1) : derivative p = 1 := by
  rw [hpmon.eq_X_add_C hdeg, derivative_add, derivative_X, derivative_C, add_zero]

theorem D_algebraMap_polynomial_degOne {p : K[X]} (hpmon : p.Monic) (hdeg : p.natDegree = 1) :
    KaehlerDifferential.D K (RatFunc K) (algebraMap K[X] (RatFunc K) p) = dX K := by
  rw [D_algebraMap_polynomial K p, derivative_monic_natDegree_one_eq_one K hpmon hdeg, map_one,
    one_smul]

theorem eq_C_coeff_zero_of_degree_lt_degOne {p c : K[X]} (hpirr : Irreducible p)
    (hdeg : p.natDegree = 1) (hcdeg : c.degree < p.degree) : c = C (c.coeff 0) := by
  have hpdeg : p.degree = (1 : ℕ) := by
    rw [degree_eq_natDegree hpirr.ne_zero, hdeg]
  rw [hpdeg, Nat.cast_one] at hcdeg
  exact eq_C_of_degree_le_zero (Nat.WithBot.lt_one_iff_le_zero.mp hcdeg)

theorem p1PrincipalPartAtom_mul_differentialCoeff_dX_degOne
    {p c : K[X]} (hpmon : p.Monic) (hpirr : Irreducible p) (hdeg : p.natDegree = 1)
    (hcdeg : c.degree < p.degree) (m : ℕ) :
    p1PrincipalPartAtom K p c m * (finitePlace K hpirr).differentialCoeff (dX K)
      = c.coeff 0 • ((finitePlace K hpirr).differentialCoeff
            (KaehlerDifferential.D K (RatFunc K) (algebraMap K[X] (RatFunc K) p))
          * ((algebraMap K[X] (RatFunc K) p) ^ m)⁻¹) := by
  have hc : algebraMap K[X] (RatFunc K) c = algebraMap K (RatFunc K) (c.coeff 0) := by
    conv_lhs => rw [eq_C_coeff_zero_of_degree_lt_degOne K hpirr hdeg hcdeg]
    rw [C_eq_algebraMap, ← IsScalarTower.algebraMap_apply K K[X] (RatFunc K)]
  rw [D_algebraMap_polynomial_degOne K hpmon hdeg, Algebra.smul_def,
    show p1PrincipalPartAtom K p c m
      = algebraMap K[X] (RatFunc K) c / (algebraMap K[X] (RatFunc K) p) ^ m from rfl, hc]
  ring

end PCoordinateIdentity

section NamedHigherDeg

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

open RationalFunctionField

def P1FinitePlaceCanonicalResidueAtomMGeTwoHigherDeg : Prop :=
  ∀ (p c : K[X]) (m : ℕ) (_ : p.Monic) (hpirr : Irreducible p),
    c.degree < p.degree → 2 ≤ m → 2 ≤ p.natDegree →
    ∀ R : (finitePlace K hpirr).CanonicalLocalResidueDataK,
      R.res (p1PrincipalPartAtom K p c m * (finitePlace K hpirr).differentialCoeff (dX K)) = 0

end NamedHigherDeg

section DegOneDischarge

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

open RationalFunctionField

theorem p1FinitePlaceCanonicalResidueAtom_of_coordIndep_degOne
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K))
    {p c : K[X]} {m : ℕ} (hpmon : p.Monic) (hpirr : Irreducible p)
    (hcdeg : c.degree < p.degree) (hm : 2 ≤ m) (hdeg : p.natDegree = 1)
    (R : (finitePlace K hpirr).CanonicalLocalResidueDataK) :
    R.res (p1PrincipalPartAtom K p c m * (finitePlace K hpirr).differentialCoeff (dX K)) = 0 := by
  rw [p1PrincipalPartAtom_mul_differentialCoeff_dX_degOne K hpmon hpirr hdeg hcdeg m, map_smul,
    show m = (m - 1) + 1 from (Nat.sub_add_cancel (by omega)).symm,
    hcoord (finitePlace K hpirr) (algebraMap K[X] (RatFunc K) p) (ord_finitePlace_self K hpirr)
      R (m - 1) (by omega),
    smul_zero]

end DegOneDischarge

section AlgClosed

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [IsAlgClosed K]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

open RationalFunctionField

theorem p1FinitePlaceCanonicalResidueAtomMGeTwoHigherDeg_of_algClosed :
    P1FinitePlaceCanonicalResidueAtomMGeTwoHigherDeg K := by
  intro p c m _ hpirr _ _ hdeg
  have h1 : p.natDegree = 1 := by
    have h := IsAlgClosed.degree_eq_one_of_irreducible K hpirr
    rw [degree_eq_natDegree hpirr.ne_zero] at h
    exact_mod_cast h
  omega

end AlgClosed

end AlgebraicCurve

namespace ValuationSubring

variable {F : Type*} [Field F]

private theorem ofPrime_congr {R : ValuationSubring F} {P Q : Ideal R}
    [P.IsPrime] [Q.IsPrime] (h : P = Q) : R.ofPrime P = R.ofPrime Q := by
  subst h; congr

theorem eq_top_of_idealOfLE_eq_bot {R S : ValuationSubring F} (h : R ≤ S)
    (hbot : idealOfLE R S h = ⊥) : S = ⊤ :=
  eq_top_of_idealOfLE_eq_bot_s12 h hbot

theorem idealOfLE_ne_bot_of_ne_top {R S : ValuationSubring F} (h : R ≤ S)
    (hS : S ≠ ⊤) : idealOfLE R S h ≠ ⊥ :=
  idealOfLE_ne_bot_of_ne_top_s12 h hS

theorem eq_of_isDiscreteValuationRing_of_le {R S : ValuationSubring F}
    [IsDiscreteValuationRing R] (h : R ≤ S) (hS : S ≠ ⊤) : R = S :=
  eq_of_isDiscreteValuationRing_of_le_s12 h hS

end ValuationSubring

namespace AlgebraicCurve

section DedekindModel

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem valSubringKaehlerFinite_of_dedekindModel
    (hmodel : ValSubringDedekindModel K F) :
    ValSubringKaehlerFinite K F :=
  valSubringKaehlerFinite_of_essFiniteType
    (valSubringEssFiniteType_of_dedekindModel hmodel)

end DedekindModel

open RationalFunctionField

theorem ordDifferentialWellDefined_ratFunc_of_perfectField (K : Type*) [Field K]
    [PerfectField K] :
    OrdDifferentialWellDefined K (RatFunc K) := by
  classical
  intro v π π' hπ hπ'

  have hπ0 : π ≠ 0 := by
    intro h
    rw [h, v.ord_zero] at hπ
    exact zero_ne_one hπ
  have hπ'0 : π' ≠ 0 := by
    intro h
    rw [h, v.ord_zero] at hπ'
    exact zero_ne_one hπ'

  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  ·
    obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
    obtain ⟨h1ne, h1ord⟩ :=
      ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one hp hwp
        (PerfectField.separable_of_irreducible hp) hπ0 hπ
    obtain ⟨h2ne, h2ord⟩ :=
      ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one hp hwp
        (PerfectField.separable_of_irreducible hp) hπ'0 hπ'
    exact exists_ord_zero_smul_of_smul_dX_eq h1ne h2ne (h2ord.trans h1ord.symm)
      (D_eq_ratFuncDXCoeff_smul_dX K π) (D_eq_ratFuncDXCoeff_smul_dX K π')
  ·
    obtain ⟨e, he0, heord, hDe⟩ := exists_dXCoeff_ord_two_of_ord_placeInfty_eq_one hπ0 hπ
    obtain ⟨e', he'0, he'ord, hDe'⟩ := exists_dXCoeff_ord_two_of_ord_placeInfty_eq_one hπ'0 hπ'
    exact exists_ord_zero_smul_of_smul_dX_eq he0 he'0 (he'ord.trans heord.symm) hDe hDe'

section UnitFiniteDX

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [CharZero K]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

open RationalFunctionField

theorem p1DifferentialCoeffUnitFinite_dX :
    P1DifferentialCoeffUnitFinite K (dX_ne_zero K) := by
  intro v hvinf
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  · obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
    exact ord_differentialCoeff_dX_ofHeightOneSpectrum hp hwp hp.separable
  · exact absurd rfl hvinf

end UnitFiniteDX

section MOneSimplePoleBounds

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates]

open RationalFunctionField

theorem ord_finitePlace_mOneAtom_mul_differentialCoeff
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0)
    (hunit : ∀ v : Place K (RatFunc K), v ≠ p1PlaceInfty K → v.ord (v.differentialCoeff ω₀) = 0)
    {p : K[X]} (hp : Irreducible p) {c : K[X]} (hc : c ≠ 0)
    (hdeg : c.degree < p.degree) :
    (finitePlace K hp).ord
        (p1PrincipalPartAtom K p c 1 * (finitePlace K hp).differentialCoeff ω₀) = -1 := by
  have hatom0 : p1PrincipalPartAtom K p c 1 ≠ 0 := by
    simp only [p1PrincipalPartAtom, ne_eq, div_eq_zero_iff, not_or]
    exact ⟨(map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hc,
      pow_ne_zero _ ((map_ne_zero_iff _
        (IsFractionRing.injective K[X] (RatFunc K))).mpr hp.ne_zero)⟩
  rw [(finitePlace K hp).ord_mul hatom0 ((finitePlace K hp).differentialCoeff_ne_zero hω₀),
    ord_finitePlace_p1PrincipalPartAtom K hp hc hdeg 1,
    hunit (finitePlace K hp) (finitePlace_ne_placeInfty hp)]
  norm_num

theorem ord_placeInfty_mOneAtom_mul_differentialCoeff_ge_neg_one
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0)
    (hInfty : (p1PlaceInfty K).ordDifferential ω₀ = -2)
    {p : K[X]} (hp : Irreducible p) {c : K[X]} (hc : c ≠ 0)
    (hdeg : c.degree < p.degree) :
    -1 ≤ (p1PlaceInfty K).ord
        (p1PrincipalPartAtom K p c 1 * (p1PlaceInfty K).differentialCoeff ω₀) := by
  have hatom0 : p1PrincipalPartAtom K p c 1 ≠ 0 := by
    simp only [p1PrincipalPartAtom, ne_eq, div_eq_zero_iff, not_or]
    exact ⟨(map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hc,
      pow_ne_zero _ ((map_ne_zero_iff _
        (IsFractionRing.injective K[X] (RatFunc K))).mpr hp.ne_zero)⟩
  rw [(p1PlaceInfty K).ord_mul hatom0 ((p1PlaceInfty K).differentialCoeff_ne_zero hω₀)]
  have h1 : 1 ≤ (p1PlaceInfty K).ord (p1PrincipalPartAtom K p c 1) :=
    one_le_ord_placeInfty_p1PrincipalPartAtom K hp hc hdeg le_rfl
  have hordD : (p1PlaceInfty K).ord ((p1PlaceInfty K).differentialCoeff ω₀) = -2 := hInfty
  omega

theorem p1MOneAtom_mul_differentialCoeff_mem_simplePole_finitePlace
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0)
    (hunit : ∀ v : Place K (RatFunc K), v ≠ p1PlaceInfty K → v.ord (v.differentialCoeff ω₀) = 0)
    {p : K[X]} (hp : Irreducible p) (c : K[X]) (hdeg : c.degree < p.degree) :
    p1PrincipalPartAtom K p c 1 * (finitePlace K hp).differentialCoeff ω₀
      ∈ (finitePlace K hp).simplePoleSubmodule := by
  rcases eq_or_ne c 0 with rfl | hc
  · show algebraMap K[X] (RatFunc K) 0 / (algebraMap K[X] (RatFunc K) p) ^ 1
        * (finitePlace K hp).differentialCoeff ω₀ ∈ _
    rw [_root_.map_zero, zero_div, zero_mul]; exact zero_mem _
  · have hatom0 : p1PrincipalPartAtom K p c 1 ≠ 0 := by
      simp only [p1PrincipalPartAtom, ne_eq, div_eq_zero_iff, not_or]
      exact ⟨(map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hc,
        pow_ne_zero _ ((map_ne_zero_iff _
          (IsFractionRing.injective K[X] (RatFunc K))).mpr hp.ne_zero)⟩
    rw [← (finitePlace K hp).poleSubmodule_one, Place.mem_poleSubmodule, pow_one]
    refine (finitePlace K hp).mem_of_ord_nonneg
      (mul_ne_zero (finitePlace K hp).uniformizer_ne_zero
        (mul_ne_zero hatom0 ((finitePlace K hp).differentialCoeff_ne_zero hω₀))) ?_
    rw [(finitePlace K hp).ord_mul (finitePlace K hp).uniformizer_ne_zero
        (mul_ne_zero hatom0 ((finitePlace K hp).differentialCoeff_ne_zero hω₀)),
      (finitePlace K hp).ord_uniformizer,
      ord_finitePlace_mOneAtom_mul_differentialCoeff K hω₀ hunit hp hc hdeg]
    omega

theorem p1MOneAtom_mul_differentialCoeff_mem_simplePole_placeInfty
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0)
    (hInfty : (p1PlaceInfty K).ordDifferential ω₀ = -2)
    {p : K[X]} (hp : Irreducible p) (c : K[X]) (hdeg : c.degree < p.degree) :
    p1PrincipalPartAtom K p c 1 * (p1PlaceInfty K).differentialCoeff ω₀
      ∈ (p1PlaceInfty K).simplePoleSubmodule := by
  rcases eq_or_ne c 0 with rfl | hc
  · show algebraMap K[X] (RatFunc K) 0 / (algebraMap K[X] (RatFunc K) p) ^ 1
        * (p1PlaceInfty K).differentialCoeff ω₀ ∈ _
    rw [_root_.map_zero, zero_div, zero_mul]; exact zero_mem _
  · have hatom0 : p1PrincipalPartAtom K p c 1 ≠ 0 := by
      simp only [p1PrincipalPartAtom, ne_eq, div_eq_zero_iff, not_or]
      exact ⟨(map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hc,
        pow_ne_zero _ ((map_ne_zero_iff _
          (IsFractionRing.injective K[X] (RatFunc K))).mpr hp.ne_zero)⟩
    rw [← (p1PlaceInfty K).poleSubmodule_one, Place.mem_poleSubmodule, pow_one]
    refine (p1PlaceInfty K).mem_of_ord_nonneg
      (mul_ne_zero (p1PlaceInfty K).uniformizer_ne_zero
        (mul_ne_zero hatom0 ((p1PlaceInfty K).differentialCoeff_ne_zero hω₀))) ?_
    rw [(p1PlaceInfty K).ord_mul (p1PlaceInfty K).uniformizer_ne_zero
        (mul_ne_zero hatom0 ((p1PlaceInfty K).differentialCoeff_ne_zero hω₀)),
      (p1PlaceInfty K).ord_uniformizer]
    have h := ord_placeInfty_mOneAtom_mul_differentialCoeff_ge_neg_one K hω₀ hInfty hp hc hdeg
    omega

end MOneSimplePoleBounds

section MOneSimplePoleRow

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates]

open RationalFunctionField

def P1PrincipalPartMOneSimplePoleCancel {ω₀ : Ω[(RatFunc K)⁄K]} (_hω₀ : ω₀ ≠ 0) : Prop :=
  ∀ (p c : K[X]) (_ : p.Monic) (hpirr : Irreducible p), c.degree < p.degree →
    ∀ (hfmem : p1PrincipalPartAtom K p c 1 * (finitePlace K hpirr).differentialCoeff ω₀
        ∈ (finitePlace K hpirr).simplePoleSubmodule)
      (himem : p1PrincipalPartAtom K p c 1 * (p1PlaceInfty K).differentialCoeff ω₀
        ∈ (p1PlaceInfty K).simplePoleSubmodule),
    Algebra.trace K (finitePlace K hpirr).ResidueField
        ((finitePlace K hpirr).simplePoleResidueAux ⟨_, hfmem⟩)
      + Algebra.trace K (p1PlaceInfty K).ResidueField
          ((p1PlaceInfty K).simplePoleResidueAux ⟨_, himem⟩)
      = 0

end MOneSimplePoleRow

end AlgebraicCurve

namespace ModularCurve

section Corollaries

variable (K : Type*) [Field K]

scoped instance instHasPrincipalDivisorsRatFuncSelf : AlgebraicCurve.HasPrincipalDivisors K (RatFunc K) :=
  AlgebraicCurve.RationalFunctionField.hasPrincipalDivisors_of_isGalois
    (AlgebraicCurve.ramificationInertiaIdentity_of_finiteDimensional K (RatFunc K) (RatFunc K))

end Corollaries

end ModularCurve

namespace AlgebraicCurve

section TraceRow

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

open RationalFunctionField

def P1FinitePlaceCanonicalResidueAtomMGeTwoTrace : Prop :=
  ∀ (p c : K[X]) (m : ℕ) (_ : p.Monic) (hpirr : Irreducible p), c.degree < p.degree → 2 ≤ m →
    ∀ R : (finitePlace K hpirr).CanonicalLocalResidueDataK,
      Algebra.trace K (finitePlace K hpirr).ResidueField
          (R.res (p1PrincipalPartAtom K p c m
            * (finitePlace K hpirr).differentialCoeff (dX K))) = 0

def P1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg : Prop :=
  ∀ (p c : K[X]) (m : ℕ) (_ : p.Monic) (hpirr : Irreducible p),
    c.degree < p.degree → 2 ≤ m → 2 ≤ p.natDegree →
    ∀ R : (finitePlace K hpirr).CanonicalLocalResidueDataK,
      Algebra.trace K (finitePlace K hpirr).ResidueField
          (R.res (p1PrincipalPartAtom K p c m
            * (finitePlace K hpirr).differentialCoeff (dX K))) = 0

end TraceRow

section Monotonicity

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

open RationalFunctionField

theorem p1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg_of_higherDeg
    (h : P1FinitePlaceCanonicalResidueAtomMGeTwoHigherDeg K) :
    P1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg K :=
  fun p c m hpmon hpirr hdeg hm hpdeg R => by
    rw [h p c m hpmon hpirr hdeg hm hpdeg R, _root_.map_zero]

end Monotonicity

section DegOneDischargeTrace

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

open RationalFunctionField

theorem p1FinitePlaceCanonicalResidueAtomTrace_of_coordIndep_degOne
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K))
    {p c : K[X]} {m : ℕ} (hpmon : p.Monic) (hpirr : Irreducible p)
    (hcdeg : c.degree < p.degree) (hm : 2 ≤ m) (hdeg : p.natDegree = 1)
    (R : (finitePlace K hpirr).CanonicalLocalResidueDataK) :
    Algebra.trace K (finitePlace K hpirr).ResidueField
        (R.res (p1PrincipalPartAtom K p c m
          * (finitePlace K hpirr).differentialCoeff (dX K))) = 0 := by
  rw [p1FinitePlaceCanonicalResidueAtom_of_coordIndep_degOne K hcoord hpmon hpirr hcdeg hm
    hdeg R, _root_.map_zero]

theorem p1FinitePlaceCanonicalResidueAtomMGeTwoTrace_of_coordIndep_higherDeg
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K))
    (hHigh : P1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg K) :
    P1FinitePlaceCanonicalResidueAtomMGeTwoTrace K := by
  intro p c m hpmon hpirr hcdeg hm R
  have hpos := hpirr.natDegree_pos
  rcases Nat.lt_or_ge p.natDegree 2 with hdeg | hdeg
  · exact p1FinitePlaceCanonicalResidueAtomTrace_of_coordIndep_degOne K hcoord hpmon hpirr
      hcdeg hm (by omega) R
  · exact hHigh p c m hpmon hpirr hcdeg hm hdeg R

end DegOneDischargeTrace

section AlgClosedTrace

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [IsAlgClosed K] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

open RationalFunctionField

theorem p1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg_of_algClosed :
    P1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg K :=
  p1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg_of_higherDeg K
    (p1FinitePlaceCanonicalResidueAtomMGeTwoHigherDeg_of_algClosed K)

end AlgClosedTrace

namespace Place

section CenterNonzero

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
  (A : Subalgebra K F) (hA : (A : Set F) ⊆ (v.toValuationSubring : Set F))

private theorem inv_mem_of_not_mem_centerIdeal {a : A} (ha : a ∉ v.centerIdeal A hA) :
    ((a : F))⁻¹ ∈ v.toValuationSubring := by
  obtain ⟨u, hu⟩ := v.isUnit_modelInclusion_of_not_mem_centerIdeal A hA ha
  have huF : ((u : v.toValuationSubring) : F) = (a : F) :=
    congrArg (Subtype.val : v.toValuationSubring → F) hu
  have huinvF : ((u⁻¹ : v.toValuationSubringˣ).1 : F) * (a : F) = 1 := by
    have h1 : ((u⁻¹ : v.toValuationSubringˣ).1 : F) * ((u : v.toValuationSubring) : F)
        = ((1 : v.toValuationSubring) : F) :=
      congrArg (Subtype.val : v.toValuationSubring → F) u.inv_mul
    rw [huF] at h1; exact h1
  have : ((u⁻¹ : v.toValuationSubringˣ).1 : F) = (a : F)⁻¹ :=
    eq_inv_of_mul_eq_one_left huinvF
  exact this ▸ ((u⁻¹ : v.toValuationSubringˣ).1 : v.toValuationSubring).2

private theorem div_mem_of_not_mem_centerIdeal (r : A) {a : A}
    (ha : a ∉ v.centerIdeal A hA) :
    (r : F) / (a : F) ∈ v.toValuationSubring := by
  rw [div_eq_mul_inv]
  exact v.toValuationSubring.toSubring.mul_mem (hA r.2)
    (inv_mem_of_not_mem_centerIdeal v A hA ha)

end CenterNonzero

end Place

section DedekindFractionModel

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem valSubringKaehlerFinite_of_dedekindFractionModel
    (hfrac : ValSubringDedekindFractionModel K F) :
    ValSubringKaehlerFinite K F :=
  valSubringKaehlerFinite_of_dedekindModel
    (valSubringDedekindModel_of_dedekindFractionModel hfrac)

end DedekindFractionModel

section EulerGeneral

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [CharZero K] {p : K[X]} [Fact (Irreducible p)]

theorem aeval_root_eq_sum_range {c : K[X]} {d : ℕ} (hd : c.natDegree < d) :
    (aeval (AdjoinRoot.root p) c : AdjoinRoot p)
      = ∑ k ∈ Finset.range d, c.coeff k • AdjoinRoot.root p ^ k := by
  rw [aeval_def, eval₂_eq_sum_range' (algebraMap K (AdjoinRoot p)) hd]
  exact Finset.sum_congr rfl fun k _ => (Algebra.smul_def _ _).symm

theorem trace_adjoinRoot_mk_div_mk_derivative_of_degree_lt (hpmon : p.Monic)
    {c : K[X]} (hdeg : c.degree < p.degree) :
    Algebra.trace K (AdjoinRoot p)
        (AdjoinRoot.mk p c / AdjoinRoot.mk p (derivative p))
      = c.coeff (p.natDegree - 1) := by
  haveI : FiniteDimensional K (AdjoinRoot p) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hpmon.ne_zero).basis

  have hpd : 0 < p.natDegree := (Fact.out : Irreducible p).natDegree_pos
  have hcd : c.natDegree < p.natDegree := by
    rcases eq_or_ne c 0 with rfl | hc
    · simpa using hpd
    · exact natDegree_lt_natDegree hc hdeg
  rw [← AdjoinRoot.aeval_eq, ← AdjoinRoot.aeval_eq,
    aeval_root_eq_sum_range K hcd, Finset.sum_div, map_sum]

  trans ∑ k ∈ Finset.range p.natDegree,
      c.coeff k * Algebra.trace K (AdjoinRoot p)
        (AdjoinRoot.root p ^ k / aeval (AdjoinRoot.root p) (derivative p))
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, mul_div_assoc, ← Algebra.smul_def, map_smul, smul_eq_mul]

  rw [Finset.sum_eq_single (p.natDegree - 1)]
  ·
    rw [FLT.EulerDualBasis.trace_root_pow_div_derivative_self hpmon hpd, mul_one]
  ·
    intro k hk hkne
    have hk' : k < p.natDegree - 1 :=
      lt_of_le_of_ne (Nat.le_sub_one_of_lt (Finset.mem_range.mp hk)) hkne
    rw [FLT.EulerDualBasis.trace_root_pow_div_derivative_of_lt hpmon hk', mul_zero]
  ·
    intro h
    exact absurd (Finset.mem_range.mpr (Nat.sub_lt hpd one_pos)) h

end EulerGeneral

section AlgEquivAdjoinRoot

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable {p : K[X]} (hpirr : Irreducible p)

open RationalFunctionField

def finitePlaceResidueFieldAlgEquivAdjoinRoot :
    AdjoinRoot p ≃ₐ[K] (finitePlace K hpirr).ResidueField :=
  residueFieldEquivOfHeightOneSpectrum K (heightOneSpectrumOfIrreducible K hpirr)

theorem finitePlaceResidueFieldAlgEquivAdjoinRoot_mk (q : K[X]) :
    finitePlaceResidueFieldAlgEquivAdjoinRoot K hpirr (AdjoinRoot.mk p q)
      = IsLocalRing.residue _ ⟨algebraMap K[X] (RatFunc K) q,
          algebraMap_mem_ofHeightOneSpectrum K _ q⟩ :=
  rfl

end AlgEquivAdjoinRoot

section TraceTransport

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable {p : K[X]} (hpirr : Irreducible p)

open RationalFunctionField

theorem trace_finitePlace_residueField_eq_trace_adjoinRoot
    (y : (finitePlace K hpirr).ResidueField) :
    Algebra.trace K (finitePlace K hpirr).ResidueField y
      = Algebra.trace K (AdjoinRoot p)
          ((finitePlaceResidueFieldAlgEquivAdjoinRoot K hpirr).symm y) := by
  conv_lhs => rw [← (finitePlaceResidueFieldAlgEquivAdjoinRoot K hpirr).apply_symm_apply y]
  exact Algebra.trace_eq_of_algEquiv _ _

end TraceTransport

section BridgeRows

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates]

open RationalFunctionField

def P1FinitePlaceSimplePoleResidueAdjoinRootValue : Prop :=
  ∀ (p c : K[X]) (_ : p.Monic) (hpirr : Irreducible p), c.degree < p.degree →
    letI : Fact (Irreducible p) := ⟨hpirr⟩
    ∀ (hfmem : p1PrincipalPartAtom K p c 1 * (finitePlace K hpirr).differentialCoeff (dX K)
        ∈ (finitePlace K hpirr).simplePoleSubmodule),
    (finitePlaceResidueFieldAlgEquivAdjoinRoot K hpirr).symm
        ((finitePlace K hpirr).simplePoleResidueAux ⟨_, hfmem⟩)
      = AdjoinRoot.mk p c / AdjoinRoot.mk p (derivative p)

def P1PlaceInftySimplePoleResidueEulerValue : Prop :=
  ∀ (p c : K[X]) (_ : p.Monic) (_ : Irreducible p), c.degree < p.degree →
    ∀ (himem : p1PrincipalPartAtom K p c 1 * (p1PlaceInfty K).differentialCoeff (dX K)
        ∈ (p1PlaceInfty K).simplePoleSubmodule),
    Algebra.trace K (p1PlaceInfty K).ResidueField
        ((p1PlaceInfty K).simplePoleResidueAux ⟨_, himem⟩)
      = -(c.coeff (p.natDegree - 1))

end BridgeRows

section FinitePlaceTrace

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [CharZero K]
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates]

open RationalFunctionField

theorem trace_finitePlace_simplePoleResidue_of_adjoinRootValue
    (hbridge : P1FinitePlaceSimplePoleResidueAdjoinRootValue K)
    {p c : K[X]} (hpmon : p.Monic) (hpirr : Irreducible p) (hdeg : c.degree < p.degree)
    (hfmem : p1PrincipalPartAtom K p c 1 * (finitePlace K hpirr).differentialCoeff (dX K)
        ∈ (finitePlace K hpirr).simplePoleSubmodule) :
    Algebra.trace K (finitePlace K hpirr).ResidueField
        ((finitePlace K hpirr).simplePoleResidueAux ⟨_, hfmem⟩)
      = c.coeff (p.natDegree - 1) := by
  haveI : Fact (Irreducible p) := ⟨hpirr⟩
  have hval := hbridge p c hpmon hpirr hdeg
  rw [trace_finitePlace_residueField_eq_trace_adjoinRoot K hpirr, hval hfmem,
    trace_adjoinRoot_mk_div_mk_derivative_of_degree_lt K hpmon hdeg]

end FinitePlaceTrace

section HigherDegReduction

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [CharZero K]
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

open RationalFunctionField

theorem p1PrincipalPartMOneSimplePoleCancel_of_eulerBridge
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0) (heq : ω₀ = dX K)
    (hfin : P1FinitePlaceSimplePoleResidueAdjoinRootValue K)
    (hinf : P1PlaceInftySimplePoleResidueEulerValue K) :
    P1PrincipalPartMOneSimplePoleCancel K hω₀ := by
  subst heq
  intro p c hpmon hpirr hdeg hfmem himem
  rw [trace_finitePlace_simplePoleResidue_of_adjoinRootValue K hfin hpmon hpirr hdeg hfmem,
    hinf p c hpmon hpirr hdeg himem, add_neg_cancel]

end HigherDegReduction

section TwoAffineChartsKaehler

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem valSubringKaehlerFinite_of_twoAffineCharts
    (h : ValSubringTwoAffineCharts K F) :
    ValSubringKaehlerFinite K F :=
  valSubringKaehlerFinite_of_dedekindFractionModel
    (valSubringDedekindFractionModel_of_twoAffineCharts h)

end TwoAffineChartsKaehler

section SeparatingTranscendentalKaehler

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem valSubringKaehlerFinite_of_hasSeparatingTranscendental
    (h : HasSeparatingTranscendental K F) :
    ValSubringKaehlerFinite K F :=
  valSubringKaehlerFinite_of_twoAffineCharts
    (valSubringTwoAffineCharts_of_hasSeparatingTranscendental h)

end SeparatingTranscendentalKaehler

namespace Place

section ToKSubalgebra

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

@[reducible] private noncomputable def toKSubalgebra : Subalgebra K F where
  __ := v.toValuationSubring.toSubring
  algebraMap_mem' c := v.algebraMap_mem' c

end ToKSubalgebra

section SimplePoleAuxMul

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem simplePoleResidueAux_mul_of_mem {a : F} (ha : a ∈ v.toValuationSubring)
    {f : F} (hf : f ∈ v.simplePoleSubmodule)
    (haf : a * f ∈ v.simplePoleSubmodule) :
    v.simplePoleResidueAux ⟨a * f, haf⟩
      = IsLocalRing.residue _ ⟨a, ha⟩ * v.simplePoleResidueAux ⟨f, hf⟩ := by
  rw [simplePoleResidueAux_apply, simplePoleResidueAux_apply, ← map_mul]
  exact congrArg (IsLocalRing.residue _) (Subtype.ext (mul_left_comm _ _ _))

private theorem mul_mem_simplePoleSubmodule_of_mem {a : F} (ha : a ∈ v.toValuationSubring)
    {f : F} (hf : f ∈ v.simplePoleSubmodule) :
    a * f ∈ v.simplePoleSubmodule := by
  rw [mem_simplePoleSubmodule, mul_left_comm]
  exact mul_mem ha hf

end SimplePoleAuxMul

end Place

section DerivativeRegular

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]

open RationalFunctionField

theorem denom_notMem_of_mem_ofHeightOneSpectrum (w : HeightOneSpectrum K[X]) {f : RatFunc K}
    (hf : f ∈ (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).toValuationSubring) :
    f.denom ∉ w.asIdeal := by
  intro hd
  have hxval : w.valuation (RatFunc K) f ≤ 1 :=
    (Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := K)
      (F := RatFunc K) w).le_one_iff_le_one.mpr ((Place.mem_iff_adicValuation_le_one _).mp hf)
  have hden_ne : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr f.denom_ne_zero
  have hmul : f * algebraMap K[X] (RatFunc K) f.denom = algebraMap K[X] (RatFunc K) f.num :=
    ((div_eq_iff hden_ne).mp f.num_div_denom).symm
  have hnum : f.num ∉ w.asIdeal := by
    intro hn
    refine w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
    obtain ⟨a, b, hab⟩ := RatFunc.isCoprime_num_denom f
    exact hab ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ hn) (Ideal.mul_mem_left _ _ hd)
  have h1 : w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) f.num) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem w).mpr hnum
  refine absurd h1 (ne_of_lt ?_)
  calc w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) f.num)
      = w.valuation (RatFunc K) f
          * w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) f.denom) := by
        rw [← map_mul, hmul]
    _ ≤ w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) f.denom) :=
        mul_le_of_le_one_left' hxval
    _ < 1 := (HeightOneSpectrum.valuation_lt_one_iff_mem w f.denom).mpr hd

variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

open KaehlerDifferential

private theorem differentialCoeff_add' (v : Place K (RatFunc K)) (ω₁ ω₂ : Ω[(RatFunc K)⁄K]) :
    v.differentialCoeff (ω₁ + ω₂) = v.differentialCoeff ω₁ + v.differentialCoeff ω₂ :=
  v.differentialCoeff_unique
    (by rw [add_smul, v.differentialCoeff_smul_dCoord, v.differentialCoeff_smul_dCoord])

theorem differentialCoeff_D_algebraMap_polynomial (v : Place K (RatFunc K)) (q : K[X]) :
    v.differentialCoeff (D K (RatFunc K) (algebraMap K[X] (RatFunc K) q))
      = algebraMap K[X] (RatFunc K) q.derivative * v.differentialCoeff (dX K) := by
  rw [D_algebraMap_polynomial K q, v.differentialCoeff_smul]

theorem differentialCoeff_D_mem_finitePlace [CharZero K] {p : K[X]} (hpirr : Irreducible p)
    {f : RatFunc K} (hf : f ∈ (finitePlace K hpirr).toValuationSubring) :
    (finitePlace K hpirr).differentialCoeff (D K (RatFunc K) f)
      ∈ (finitePlace K hpirr).toValuationSubring := by
  set v := finitePlace K hpirr

  set ξ : K[X] := f.num.derivative * f.denom - f.num * f.denom.derivative
  have hd0 : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr f.denom_ne_zero
  have hcoeff : v.differentialCoeff (D K (RatFunc K) f)
      = algebraMap K[X] (RatFunc K) ξ * ((algebraMap K[X] (RatFunc K) f.denom) ^ 2)⁻¹
          * v.differentialCoeff (dX K) := by
    have hkey := denom_sq_smul_D_eq K f
    refine v.differentialCoeff_unique ?_
    rw [mul_smul, v.differentialCoeff_smul_dCoord, mul_comm, mul_smul, ← hkey, smul_smul,
      inv_mul_cancel₀ (pow_ne_zero 2 hd0), one_smul]
  rw [hcoeff]

  refine mul_mem (mul_mem ?_ ?_) ?_
  · exact algebraMap_mem_ofHeightOneSpectrum K _ ξ
  ·
    have hden_notmem : f.denom ∉ (heightOneSpectrumOfIrreducible K hpirr).asIdeal :=
      denom_notMem_of_mem_ofHeightOneSpectrum K _ hf
    have hordd : v.ord (algebraMap K[X] (RatFunc K) f.denom) = 0 := by
      by_contra h
      exact hden_notmem ((Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K)
        (F := RatFunc K) _ f.denom_ne_zero).mp h)
    refine v.mem_of_ord_nonneg (inv_ne_zero (pow_ne_zero 2 hd0)) ?_
    rw [v.ord_inv, ← zpow_natCast, v.ord_zpow, hordd, mul_zero, _root_.neg_zero]
  · exact v.mem_of_ord_nonneg (v.differentialCoeff_ne_zero (dX_ne_zero K))
      (ord_differentialCoeff_dX_ofHeightOneSpectrum hpirr
        (heightOneSpectrumOfIrreducible_asIdeal K hpirr) hpirr.separable).ge

end DerivativeRegular

section LeibnizCore

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)] [CharZero K]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

open RationalFunctionField KaehlerDifferential

theorem uniformizer_div_mem_finitePlace {p : K[X]} (hpirr : Irreducible p) :
    (finitePlace K hpirr).uniformizer / algebraMap K[X] (RatFunc K) p
      ∈ (finitePlace K hpirr).toValuationSubring := by
  set v := finitePlace K hpirr
  have hp0 : algebraMap K[X] (RatFunc K) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hpirr.ne_zero
  refine v.mem_of_ord_nonneg (div_ne_zero v.uniformizer_ne_zero hp0) ?_
  rw [div_eq_mul_inv, v.ord_mul v.uniformizer_ne_zero (inv_ne_zero hp0), v.ord_inv,
    v.ord_uniformizer, ord_finitePlace_self K hpirr]
  omega

theorem one_sub_uniformizer_div_mul_differentialCoeff_D
    {p : K[X]} (hpirr : Irreducible p) :
    (1 : RatFunc K) - (finitePlace K hpirr).uniformizer / algebraMap K[X] (RatFunc K) p
        * (finitePlace K hpirr).differentialCoeff
            (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p))
      = algebraMap K[X] (RatFunc K) p
          * (finitePlace K hpirr).differentialCoeff
              (D K (RatFunc K) ((finitePlace K hpirr).uniformizer
                / algebraMap K[X] (RatFunc K) p)) := by
  set v := finitePlace K hpirr
  have hp0 : algebraMap K[X] (RatFunc K) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hpirr.ne_zero

  have hleib : D K (RatFunc K) v.uniformizer
      = (v.uniformizer / algebraMap K[X] (RatFunc K) p)
            • D K (RatFunc K) (algebraMap K[X] (RatFunc K) p)
        + algebraMap K[X] (RatFunc K) p
            • D K (RatFunc K) (v.uniformizer / algebraMap K[X] (RatFunc K) p) := by
    have h := (D K (RatFunc K)).leibniz (a := v.uniformizer / algebraMap K[X] (RatFunc K) p)
      (b := algebraMap K[X] (RatFunc K) p)
    rw [div_mul_cancel₀ _ hp0] at h
    exact h

  have h1 : (1 : RatFunc K)
      = (v.uniformizer / algebraMap K[X] (RatFunc K) p)
            * v.differentialCoeff (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p))
        + algebraMap K[X] (RatFunc K) p
            * v.differentialCoeff
                (D K (RatFunc K) (v.uniformizer / algebraMap K[X] (RatFunc K) p)) := by
    have hcoord : D K (RatFunc K) v.uniformizer = v.dCoord := rfl
    rw [← v.differentialCoeff_dCoord, ← hcoord, hleib, differentialCoeff_add' K,
      v.differentialCoeff_smul, v.differentialCoeff_smul]
  linear_combination h1

theorem uniformizer_div_mul_differentialCoeff_D_mem_finitePlace
    {p : K[X]} (hpirr : Irreducible p) :
    (finitePlace K hpirr).uniformizer / algebraMap K[X] (RatFunc K) p
        * (finitePlace K hpirr).differentialCoeff
            (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p))
      ∈ (finitePlace K hpirr).toValuationSubring := by
  set v := finitePlace K hpirr
  have hp0 : algebraMap K[X] (RatFunc K) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hpirr.ne_zero
  refine mul_mem (uniformizer_div_mem_finitePlace K hpirr) ?_
  rw [differentialCoeff_D_algebraMap_polynomial K]
  exact mul_mem (algebraMap_mem_ofHeightOneSpectrum K _ p.derivative)
    (v.mem_of_ord_nonneg (v.differentialCoeff_ne_zero (dX_ne_zero K))
      (ord_differentialCoeff_dX_ofHeightOneSpectrum hpirr
        (heightOneSpectrumOfIrreducible_asIdeal K hpirr) hpirr.separable).ge)

theorem residue_uniformizer_div_mul_differentialCoeff_D_eq_one
    {p : K[X]} (hpirr : Irreducible p) :
    IsLocalRing.residue _ ⟨_, uniformizer_div_mul_differentialCoeff_D_mem_finitePlace K hpirr⟩
      = (1 : (finitePlace K hpirr).ResidueField) := by
  set v := finitePlace K hpirr
  rw [← sub_eq_zero, show (1 : v.ResidueField) = IsLocalRing.residue _ 1 by simp,
    ← map_sub, IsLocalRing.residue_eq_zero_iff]

  have hsubmem : (1 : RatFunc K) - (v.uniformizer / algebraMap K[X] (RatFunc K) p
      * v.differentialCoeff (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p)))
        ∈ v.toValuationSubring :=
    sub_mem (one_mem _) (uniformizer_div_mul_differentialCoeff_D_mem_finitePlace K hpirr)
  have hcoe : (⟨_, uniformizer_div_mul_differentialCoeff_D_mem_finitePlace K hpirr⟩
        - 1 : v.toValuationSubring)
      = -⟨_, hsubmem⟩ :=
    Subtype.ext (by push_cast; ring)
  rw [hcoe]
  refine neg_mem ?_

  have herr : (1 : RatFunc K) - (v.uniformizer / algebraMap K[X] (RatFunc K) p
      * v.differentialCoeff (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p)))
        = algebraMap K[X] (RatFunc K) p
          * v.differentialCoeff (D K (RatFunc K)
              (v.uniformizer / algebraMap K[X] (RatFunc K) p)) :=
    one_sub_uniformizer_div_mul_differentialCoeff_D K hpirr

  have hpmem : (⟨algebraMap K[X] (RatFunc K) p, algebraMap_mem_ofHeightOneSpectrum K _ p⟩
      : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
    rw [Place.mem_maximalIdeal_iff_adicValuation_lt_one]
    refine (Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := K)
      (F := RatFunc K) (heightOneSpectrumOfIrreducible K hpirr)).lt_one_iff_lt_one.mp ?_
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem _ p).mpr
      (Ideal.mem_span_singleton_self p)
  have hregmem : v.differentialCoeff (D K (RatFunc K)
        (v.uniformizer / algebraMap K[X] (RatFunc K) p)) ∈ v.toValuationSubring :=
    differentialCoeff_D_mem_finitePlace K hpirr (uniformizer_div_mem_finitePlace K hpirr)
  have hprod : (⟨_, hsubmem⟩ : v.toValuationSubring)
      = ⟨_, algebraMap_mem_ofHeightOneSpectrum K _ p⟩ * ⟨_, hregmem⟩ :=
    Subtype.ext herr
  rw [hprod]
  exact Ideal.mul_mem_right _ _ hpmem

end LeibnizCore

section BridgeDischarge

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)] [CharZero K]
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

open RationalFunctionField KaehlerDifferential

theorem residue_algebraMap_derivative_ne_zero {p : K[X]} (hpirr : Irreducible p) :
    IsLocalRing.residue _ ⟨algebraMap K[X] (RatFunc K) p.derivative,
        algebraMap_mem_ofHeightOneSpectrum K _ p.derivative⟩
      ≠ (0 : (finitePlace K hpirr).ResidueField) := by
  rw [ne_eq, IsLocalRing.residue_eq_zero_iff,
    Place.mem_maximalIdeal_iff_adicValuation_lt_one]
  intro hlt
  have hlt' := (Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := K)
    (F := RatFunc K) (heightOneSpectrumOfIrreducible K hpirr)).lt_one_iff_lt_one.mpr hlt
  rw [HeightOneSpectrum.valuation_lt_one_iff_mem,
    heightOneSpectrumOfIrreducible_asIdeal K hpirr, Ideal.mem_span_singleton] at hlt'
  exact hpirr.not_isUnit (hpirr.separable.isUnit_of_dvd' dvd_rfl hlt')

theorem simplePoleResidueAux_finitePlace_p1PrincipalPartAtom_mOne
    {p c : K[X]} (hpirr : Irreducible p)
    (hfmem : p1PrincipalPartAtom K p c 1 * (finitePlace K hpirr).differentialCoeff (dX K)
        ∈ (finitePlace K hpirr).simplePoleSubmodule) :
    (finitePlace K hpirr).simplePoleResidueAux ⟨_, hfmem⟩
      = IsLocalRing.residue _ ⟨algebraMap K[X] (RatFunc K) c,
            algebraMap_mem_ofHeightOneSpectrum K _ c⟩
        / IsLocalRing.residue _ ⟨algebraMap K[X] (RatFunc K) p.derivative,
            algebraMap_mem_ofHeightOneSpectrum K _ p.derivative⟩ := by
  set v := finitePlace K hpirr
  have hp0 : algebraMap K[X] (RatFunc K) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hpirr.ne_zero

  rw [Place.simplePoleResidueAux_apply, eq_div_iff (residue_algebraMap_derivative_ne_zero K hpirr)]

  have hkey : (v.uniformizer * (p1PrincipalPartAtom K p c 1 * v.differentialCoeff (dX K)))
        * algebraMap K[X] (RatFunc K) p.derivative
      = algebraMap K[X] (RatFunc K) c
        * (v.uniformizer / algebraMap K[X] (RatFunc K) p
            * v.differentialCoeff (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p))) := by
    rw [differentialCoeff_D_algebraMap_polynomial K]
    show v.uniformizer
        * (algebraMap K[X] (RatFunc K) c / algebraMap K[X] (RatFunc K) p ^ 1
            * v.differentialCoeff (dX K))
        * algebraMap K[X] (RatFunc K) (derivative p)
      = algebraMap K[X] (RatFunc K) c
        * (v.uniformizer / algebraMap K[X] (RatFunc K) p
            * (algebraMap K[X] (RatFunc K) (derivative p) * v.differentialCoeff (dX K)))
    rw [pow_one, div_mul_eq_mul_div, div_mul_eq_mul_div, mul_div_assoc, mul_div_assoc]
    ring_nf

  have hLHSmem : v.uniformizer * (p1PrincipalPartAtom K p c 1 * v.differentialCoeff (dX K))
      * algebraMap K[X] (RatFunc K) p.derivative ∈ v.toValuationSubring :=
    mul_mem hfmem (algebraMap_mem_ofHeightOneSpectrum K _ p.derivative)
  have hRHSmem : algebraMap K[X] (RatFunc K) c
      * (v.uniformizer / algebraMap K[X] (RatFunc K) p
          * v.differentialCoeff (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p)))
        ∈ v.toValuationSubring :=
    mul_mem (algebraMap_mem_ofHeightOneSpectrum K _ c)
      (uniformizer_div_mul_differentialCoeff_D_mem_finitePlace K hpirr)
  calc IsLocalRing.residue _ ⟨_, hfmem⟩ * IsLocalRing.residue _ ⟨_,
          algebraMap_mem_ofHeightOneSpectrum K _ p.derivative⟩
      = IsLocalRing.residue _ (⟨_, hfmem⟩ * ⟨_,
          algebraMap_mem_ofHeightOneSpectrum K _ p.derivative⟩) := (map_mul _ _ _).symm
    _ = IsLocalRing.residue _ ⟨_, hLHSmem⟩ :=
        congrArg (IsLocalRing.residue _) (Subtype.ext rfl)
    _ = IsLocalRing.residue _ ⟨_, hRHSmem⟩ :=
        congrArg (IsLocalRing.residue _) (Subtype.ext hkey)
    _ = IsLocalRing.residue _ (⟨_, algebraMap_mem_ofHeightOneSpectrum K _ c⟩
          * ⟨_, uniformizer_div_mul_differentialCoeff_D_mem_finitePlace K hpirr⟩) :=
        congrArg (IsLocalRing.residue _) (Subtype.ext rfl)
    _ = IsLocalRing.residue _ ⟨_, algebraMap_mem_ofHeightOneSpectrum K _ c⟩
          * IsLocalRing.residue _
              ⟨_, uniformizer_div_mul_differentialCoeff_D_mem_finitePlace K hpirr⟩ :=
        map_mul _ _ _
    _ = IsLocalRing.residue _ ⟨_, algebraMap_mem_ofHeightOneSpectrum K _ c⟩ := by
        rw [residue_uniformizer_div_mul_differentialCoeff_D_eq_one K hpirr, mul_one]

theorem p1FinitePlaceSimplePoleResidueAdjoinRootValue_dX :
    P1FinitePlaceSimplePoleResidueAdjoinRootValue K := by
  intro p c _ hpirr _
  letI : Fact (Irreducible p) := ⟨hpirr⟩
  intro hfmem
  rw [simplePoleResidueAux_finitePlace_p1PrincipalPartAtom_mOne K hpirr hfmem,
    AlgEquiv.symm_apply_eq, map_div₀,
    finitePlaceResidueFieldAlgEquivAdjoinRoot_mk K hpirr c,
    finitePlaceResidueFieldAlgEquivAdjoinRoot_mk K hpirr p.derivative]

end BridgeDischarge

section ComposedEngineInfty

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)] [CharZero K]
variable [HasCanonicalDivisor (K := K) (F := RatFunc K)] [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

open RationalFunctionField

theorem p1PrincipalPartMOneSimplePoleCancel_of_inftyBridge
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0) (heq : ω₀ = dX K)
    (hinf : P1PlaceInftySimplePoleResidueEulerValue K) :
    P1PrincipalPartMOneSimplePoleCancel K hω₀ :=
  p1PrincipalPartMOneSimplePoleCancel_of_eulerBridge K hω₀ heq
    (p1FinitePlaceSimplePoleResidueAdjoinRootValue_dX K) hinf

end ComposedEngineInfty

section LowDegRegular

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

open RationalFunctionField

theorem ord_placeInfty_mOneAtom_mul_differentialCoeff_dX
    (hInfty : (p1PlaceInfty K).ord ((p1PlaceInfty K).differentialCoeff (dX K)) = -2)
    {p c : K[X]} (hp : p ≠ 0) (hc : c ≠ 0) :
    (p1PlaceInfty K).ord
        (p1PrincipalPartAtom K p c 1 * (p1PlaceInfty K).differentialCoeff (dX K))
      = (p.natDegree : ℤ) - c.natDegree - 2 := by
  have hatom0 : p1PrincipalPartAtom K p c 1 ≠ 0 := by
    simp only [p1PrincipalPartAtom, ne_eq, div_eq_zero_iff, not_or]
    exact ⟨(map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hc,
      pow_ne_zero _ ((map_ne_zero_iff _
        (IsFractionRing.injective K[X] (RatFunc K))).mpr hp)⟩
  rw [(p1PlaceInfty K).ord_mul hatom0 ((p1PlaceInfty K).differentialCoeff_ne_zero (dX_ne_zero K)),
    ord_placeInfty_p1PrincipalPartAtom K hp hc 1, hInfty]
  push_cast; ring

theorem p1MOneAtom_mul_differentialCoeff_dX_mem_placeInfty
    (hInfty : (p1PlaceInfty K).ord ((p1PlaceInfty K).differentialCoeff (dX K)) = -2)
    {p c : K[X]} (hp : p ≠ 0) (hcdeg : c = 0 ∨ c.natDegree + 2 ≤ p.natDegree) :
    p1PrincipalPartAtom K p c 1 * (p1PlaceInfty K).differentialCoeff (dX K)
      ∈ (p1PlaceInfty K).toValuationSubring := by
  rcases hcdeg with rfl | hcdeg
  · show algebraMap K[X] (RatFunc K) 0 / (algebraMap K[X] (RatFunc K) p) ^ 1
        * (p1PlaceInfty K).differentialCoeff (dX K) ∈ _
    rw [_root_.map_zero, zero_div, zero_mul]; exact zero_mem _
  · rcases eq_or_ne c 0 with rfl | hc
    · show algebraMap K[X] (RatFunc K) 0 / (algebraMap K[X] (RatFunc K) p) ^ 1
          * (p1PlaceInfty K).differentialCoeff (dX K) ∈ _
      rw [_root_.map_zero, zero_div, zero_mul]; exact zero_mem _
    have hatom0 : p1PrincipalPartAtom K p c 1 ≠ 0 := by
      simp only [p1PrincipalPartAtom, ne_eq, div_eq_zero_iff, not_or]
      exact ⟨(map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hc,
        pow_ne_zero _ ((map_ne_zero_iff _
          (IsFractionRing.injective K[X] (RatFunc K))).mpr hp)⟩
    refine (p1PlaceInfty K).mem_of_ord_nonneg
      (mul_ne_zero hatom0 ((p1PlaceInfty K).differentialCoeff_ne_zero (dX_ne_zero K))) ?_
    rw [ord_placeInfty_mOneAtom_mul_differentialCoeff_dX K hInfty hp hc]
    omega

end LowDegRegular

section LowDegValue

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

open RationalFunctionField

theorem trace_placeInfty_simplePoleResidue_mOne_of_lowDeg
    (hInfty : (p1PlaceInfty K).ord ((p1PlaceInfty K).differentialCoeff (dX K)) = -2)
    {p c : K[X]} (hpirr : Irreducible p)
    (hcdeg : c = 0 ∨ c.natDegree + 2 ≤ p.natDegree)
    (himem : p1PrincipalPartAtom K p c 1 * (p1PlaceInfty K).differentialCoeff (dX K)
        ∈ (p1PlaceInfty K).simplePoleSubmodule) :
    Algebra.trace K (p1PlaceInfty K).ResidueField
        ((p1PlaceInfty K).simplePoleResidueAux ⟨_, himem⟩)
      = -(c.coeff (p.natDegree - 1)) := by

  have hreg := p1MOneAtom_mul_differentialCoeff_dX_mem_placeInfty K hInfty hpirr.ne_zero hcdeg
  have hLHS : (p1PlaceInfty K).simplePoleResidueAux ⟨_, himem⟩ = 0 :=
    (p1PlaceInfty K).simplePoleResidueAux_eq_zero_of_mem hreg
  rw [hLHS, _root_.map_zero]

  rcases hcdeg with rfl | hcdeg
  · simp
  · rw [coeff_eq_zero_of_natDegree_lt (by omega : c.natDegree < p.natDegree - 1), _root_.neg_zero]

end LowDegValue

section NamedCarriers

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

open RationalFunctionField

def P1PlaceInftySimplePoleResidueEulerValueTopDeg : Prop :=
  ∀ (p c : K[X]) (_ : p.Monic) (_ : Irreducible p), c ≠ 0 → c.natDegree + 1 = p.natDegree →
    ∀ (himem : p1PrincipalPartAtom K p c 1 * (p1PlaceInfty K).differentialCoeff (dX K)
        ∈ (p1PlaceInfty K).simplePoleSubmodule),
    Algebra.trace K (p1PlaceInfty K).ResidueField
        ((p1PlaceInfty K).simplePoleResidueAux ⟨_, himem⟩)
      = -(c.coeff (p.natDegree - 1))

def P1PlaceInftySimplePoleResidueEulerValueMonomial : Prop :=
  ∀ (p : K[X]) (_ : p.Monic) (_ : Irreducible p),
    ∀ (himem : p1PrincipalPartAtom K p (X ^ (p.natDegree - 1)) 1
          * (p1PlaceInfty K).differentialCoeff (dX K)
        ∈ (p1PlaceInfty K).simplePoleSubmodule),
    Algebra.trace K (p1PlaceInfty K).ResidueField
        ((p1PlaceInfty K).simplePoleResidueAux ⟨_, himem⟩)
      = -1

end NamedCarriers

section EraseLeadLinearity

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

open RationalFunctionField

theorem p1PrincipalPartAtom_add_mul_differentialCoeff (p c₁ c₂ : K[X]) (m : ℕ)
    (v : Place K (RatFunc K)) (ω : Ω[(RatFunc K)⁄K]) :
    p1PrincipalPartAtom K p (c₁ + c₂) m * v.differentialCoeff ω
      = p1PrincipalPartAtom K p c₁ m * v.differentialCoeff ω
        + p1PrincipalPartAtom K p c₂ m * v.differentialCoeff ω := by
  show algebraMap K[X] (RatFunc K) (c₁ + c₂) / (algebraMap K[X] (RatFunc K) p) ^ m
        * v.differentialCoeff ω
    = algebraMap K[X] (RatFunc K) c₁ / (algebraMap K[X] (RatFunc K) p) ^ m * v.differentialCoeff ω
      + algebraMap K[X] (RatFunc K) c₂ / (algebraMap K[X] (RatFunc K) p) ^ m
        * v.differentialCoeff ω
  rw [map_add]; ring

theorem p1PrincipalPartAtom_C_mul_mul_differentialCoeff (p c : K[X]) (a : K) (m : ℕ)
    (v : Place K (RatFunc K)) (ω : Ω[(RatFunc K)⁄K]) :
    p1PrincipalPartAtom K p (C a * c) m * v.differentialCoeff ω
      = a • (p1PrincipalPartAtom K p c m * v.differentialCoeff ω) := by
  show algebraMap K[X] (RatFunc K) (C a * c) / (algebraMap K[X] (RatFunc K) p) ^ m
        * v.differentialCoeff ω
    = a • (algebraMap K[X] (RatFunc K) c / (algebraMap K[X] (RatFunc K) p) ^ m
        * v.differentialCoeff ω)
  rw [map_mul, C_eq_algebraMap, ← IsScalarTower.algebraMap_apply K K[X] (RatFunc K),
    Algebra.smul_def]
  ring

theorem trace_placeInfty_simplePoleResidueAux_mOne_add
    {p c₁ c₂ : K[X]} {ω : Ω[(RatFunc K)⁄K]}
    (h1 : p1PrincipalPartAtom K p c₁ 1 * (p1PlaceInfty K).differentialCoeff ω
        ∈ (p1PlaceInfty K).simplePoleSubmodule)
    (h2 : p1PrincipalPartAtom K p c₂ 1 * (p1PlaceInfty K).differentialCoeff ω
        ∈ (p1PlaceInfty K).simplePoleSubmodule)
    (h12 : p1PrincipalPartAtom K p (c₁ + c₂) 1 * (p1PlaceInfty K).differentialCoeff ω
        ∈ (p1PlaceInfty K).simplePoleSubmodule) :
    Algebra.trace K (p1PlaceInfty K).ResidueField
        ((p1PlaceInfty K).simplePoleResidueAux ⟨_, h12⟩)
      = Algebra.trace K (p1PlaceInfty K).ResidueField
          ((p1PlaceInfty K).simplePoleResidueAux ⟨_, h1⟩)
        + Algebra.trace K (p1PlaceInfty K).ResidueField
            ((p1PlaceInfty K).simplePoleResidueAux ⟨_, h2⟩) := by
  have heq : (⟨_, h12⟩ : (p1PlaceInfty K).simplePoleSubmodule)
      = (⟨_, h1⟩ : (p1PlaceInfty K).simplePoleSubmodule) + ⟨_, h2⟩ :=
    Subtype.ext (p1PrincipalPartAtom_add_mul_differentialCoeff K p c₁ c₂ 1 _ ω)
  rw [heq, map_add, map_add]

theorem trace_placeInfty_simplePoleResidueAux_mOne_C_mul
    {p c : K[X]} {a : K} {ω : Ω[(RatFunc K)⁄K]}
    (hc : p1PrincipalPartAtom K p c 1 * (p1PlaceInfty K).differentialCoeff ω
        ∈ (p1PlaceInfty K).simplePoleSubmodule)
    (hac : p1PrincipalPartAtom K p (C a * c) 1 * (p1PlaceInfty K).differentialCoeff ω
        ∈ (p1PlaceInfty K).simplePoleSubmodule) :
    Algebra.trace K (p1PlaceInfty K).ResidueField
        ((p1PlaceInfty K).simplePoleResidueAux ⟨_, hac⟩)
      = a * Algebra.trace K (p1PlaceInfty K).ResidueField
          ((p1PlaceInfty K).simplePoleResidueAux ⟨_, hc⟩) := by
  have heq : (⟨_, hac⟩ : (p1PlaceInfty K).simplePoleSubmodule)
      = a • (⟨_, hc⟩ : (p1PlaceInfty K).simplePoleSubmodule) :=
    Subtype.ext (p1PrincipalPartAtom_C_mul_mul_differentialCoeff K p c a 1 _ ω)
  rw [heq, map_smul, map_smul, smul_eq_mul]

theorem p1PlaceInftySimplePoleResidueEulerValue_of_topDeg
    (hInfty : (p1PlaceInfty K).ord ((p1PlaceInfty K).differentialCoeff (dX K)) = -2)
    (htop : P1PlaceInftySimplePoleResidueEulerValueTopDeg K) :
    P1PlaceInftySimplePoleResidueEulerValue K := by
  intro p c hpmon hpirr hcdeg himem
  rcases eq_or_ne c 0 with rfl | hc
  · exact trace_placeInfty_simplePoleResidue_mOne_of_lowDeg K hInfty hpirr (.inl rfl) himem
  have hndeg : c.natDegree < p.natDegree := natDegree_lt_natDegree hc hcdeg
  rcases (by omega : c.natDegree + 2 ≤ p.natDegree ∨ c.natDegree + 1 = p.natDegree) with h | h
  · exact trace_placeInfty_simplePoleResidue_mOne_of_lowDeg K hInfty hpirr (.inr h) himem
  · exact htop p c hpmon hpirr hc h himem

theorem p1PlaceInftySimplePoleResidueEulerValueTopDeg_of_monomial
    (hInfty : (p1PlaceInfty K).ord ((p1PlaceInfty K).differentialCoeff (dX K)) = -2)
    (hmono : P1PlaceInftySimplePoleResidueEulerValueMonomial K) :
    P1PlaceInftySimplePoleResidueEulerValueTopDeg K := by
  intro p c hpmon hpirr hc hcnd himem

  have hInfty' : (p1PlaceInfty K).ordDifferential (dX K) = -2 := hInfty
  have hXd : (X ^ (p.natDegree - 1) : K[X]).degree < p.degree := by
    rw [degree_X_pow, degree_eq_natDegree hpirr.ne_zero]
    exact_mod_cast (by omega : p.natDegree - 1 < p.natDegree)
  have hXmem := p1MOneAtom_mul_differentialCoeff_mem_simplePole_placeInfty K
    (dX_ne_zero K) hInfty' hpirr (X ^ (p.natDegree - 1)) hXd
  have hCXmem : p1PrincipalPartAtom K p (C c.leadingCoeff * X ^ (p.natDegree - 1)) 1
        * (p1PlaceInfty K).differentialCoeff (dX K)
      ∈ (p1PlaceInfty K).simplePoleSubmodule := by
    rw [p1PrincipalPartAtom_C_mul_mul_differentialCoeff K]
    exact (p1PlaceInfty K).simplePoleSubmodule.smul_mem _ hXmem
  have hELdeg : c.eraseLead = 0 ∨ c.eraseLead.natDegree + 2 ≤ p.natDegree := by
    rcases Polynomial.eraseLead_natDegree_lt_or_eraseLead_eq_zero c with h | h
    · exact .inr (by omega)
    · exact .inl h
  have hELmem : p1PrincipalPartAtom K p c.eraseLead 1 * (p1PlaceInfty K).differentialCoeff (dX K)
      ∈ (p1PlaceInfty K).simplePoleSubmodule :=
    (p1PlaceInfty K).mem_simplePoleSubmodule_of_mem
      (p1MOneAtom_mul_differentialCoeff_dX_mem_placeInfty K hInfty hpirr.ne_zero hELdeg)

  have hcnd' : c.natDegree = p.natDegree - 1 := by omega
  have hcdecomp : c = C c.leadingCoeff * X ^ (p.natDegree - 1) + c.eraseLead := by
    conv_lhs => rw [← Polynomial.eraseLead_add_C_mul_X_pow c, add_comm, hcnd']

  have h12mem : p1PrincipalPartAtom K p
        (C c.leadingCoeff * X ^ (p.natDegree - 1) + c.eraseLead) 1
          * (p1PlaceInfty K).differentialCoeff (dX K)
      ∈ (p1PlaceInfty K).simplePoleSubmodule := by
    rw [p1PrincipalPartAtom_add_mul_differentialCoeff K]; exact add_mem hCXmem hELmem
  have heq : (⟨_, himem⟩ : (p1PlaceInfty K).simplePoleSubmodule) = ⟨_, h12mem⟩ := by
    refine Subtype.ext ?_
    show algebraMap K[X] (RatFunc K) c / (algebraMap K[X] (RatFunc K) p) ^ 1
          * (p1PlaceInfty K).differentialCoeff (dX K)
      = algebraMap K[X] (RatFunc K) (C c.leadingCoeff * X ^ (p.natDegree - 1) + c.eraseLead)
          / (algebraMap K[X] (RatFunc K) p) ^ 1 * (p1PlaceInfty K).differentialCoeff (dX K)
    rw [← hcdecomp]

  have hELcoeff : c.eraseLead.coeff (p.natDegree - 1) = 0 := by
    rcases hELdeg with h | h
    · rw [h, coeff_zero]
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  have hLead : c.leadingCoeff = c.coeff (p.natDegree - 1) := by
    rw [leadingCoeff, hcnd']
  rw [heq, trace_placeInfty_simplePoleResidueAux_mOne_add K hCXmem hELmem,
    trace_placeInfty_simplePoleResidueAux_mOne_C_mul K hXmem,
    hmono p hpmon hpirr hXmem,
    trace_placeInfty_simplePoleResidue_mOne_of_lowDeg K hInfty hpirr hELdeg hELmem,
    hELcoeff, _root_.neg_zero, add_zero, hLead]
  ring

theorem p1PlaceInftySimplePoleResidueEulerValue_of_monomial
    (hInfty : (p1PlaceInfty K).ord ((p1PlaceInfty K).differentialCoeff (dX K)) = -2)
    (hmono : P1PlaceInftySimplePoleResidueEulerValueMonomial K) :
    P1PlaceInftySimplePoleResidueEulerValue K :=
  p1PlaceInftySimplePoleResidueEulerValue_of_topDeg K hInfty
    (p1PlaceInftySimplePoleResidueEulerValueTopDeg_of_monomial K hInfty hmono)

end EraseLeadLinearity

section ComposedEngineInftyMonomial

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)] [CharZero K]
variable [HasCanonicalDivisor (K := K) (F := RatFunc K)] [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

open RationalFunctionField

theorem p1PrincipalPartMOneSimplePoleCancel_of_inftyMonomial
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0) (heq : ω₀ = dX K)
    (hmono : P1PlaceInftySimplePoleResidueEulerValueMonomial K) :
    P1PrincipalPartMOneSimplePoleCancel K hω₀ :=
  p1PrincipalPartMOneSimplePoleCancel_of_inftyBridge K hω₀ heq
    (p1PlaceInftySimplePoleResidueEulerValue_of_monomial K
      (ordDifferential_placeInfty_D_ratFuncX K hwd) hmono)

end ComposedEngineInftyMonomial

section AdjoinRingProperties

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem _root_.Transcendental.isPrincipalIdealRing_adjoin {t : F} (ht : Transcendental K t) :
    IsPrincipalIdealRing ↥(Algebra.adjoin K ({t} : Set F)) :=
  IsPrincipalIdealRing.of_surjective
    (Polynomial.algEquivOfTranscendental K t ht).toRingHom
    (Polynomial.algEquivOfTranscendental K t ht).surjective

private theorem _root_.Transcendental.isDedekindDomain_adjoin {t : F} (ht : Transcendental K t) :
    IsDedekindDomain ↥(Algebra.adjoin K ({t} : Set F)) :=
  haveI := ht.isPrincipalIdealRing_adjoin
  inferInstance

private theorem _root_.Transcendental.isIntegrallyClosed_adjoin {t : F} (ht : Transcendental K t) :
    IsIntegrallyClosed ↥(Algebra.adjoin K ({t} : Set F)) :=
  haveI := ht.isDedekindDomain_adjoin
  inferInstance

private theorem _root_.Transcendental.isNoetherianRing_adjoin {t : F} (ht : Transcendental K t) :
    IsNoetherianRing ↥(Algebra.adjoin K ({t} : Set F)) :=
  haveI := ht.isPrincipalIdealRing_adjoin
  inferInstance

private theorem _root_.Algebra.FiniteType.adjoin_singleton (t : F) :
    Algebra.FiniteType K ↥(Algebra.adjoin K ({t} : Set F)) :=
  Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton t)

private theorem _root_.Transcendental.inv {t : F} (ht : Transcendental K t) :
    Transcendental K t⁻¹ := by
  rw [Transcendental, IsAlgebraic.inv_iff]; exact ht

end AdjoinRingProperties

end AlgebraicCurve

namespace IntermediateField

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem adjoin_simple_inv (t : F) : K⟮t⁻¹⟯ = K⟮t⟯ := adjoin_simple_inv_s12 t

theorem algebraMap_comp_equivOfEq {S T : IntermediateField K F} (h : S = T) :
    (algebraMap T F).comp ((IntermediateField.equivOfEq h).toRingEquiv : S →+* T)
      = ((RingEquiv.refl F : F ≃+* F) : F →+* F).comp (algebraMap S F) :=
  algebraMap_comp_equivOfEq_s12 h

theorem finiteDimensional_of_eq {S T : IntermediateField K F} (h : S = T)
    [FiniteDimensional ↥S F] : FiniteDimensional ↥T F :=
  finiteDimensional_of_eq_s12 h

theorem isSeparable_of_eq {S T : IntermediateField K F} (h : S = T)
    [Algebra.IsSeparable ↥S F] : Algebra.IsSeparable ↥T F :=
  isSeparable_of_eq_s12 h

theorem finiteDimensional_adjoin_inv (t : F) [FiniteDimensional K⟮t⟯ F] :
    FiniteDimensional K⟮t⁻¹⟯ F :=
  finiteDimensional_adjoin_inv_s12 t

theorem isSeparable_adjoin_inv (t : F) [Algebra.IsSeparable K⟮t⟯ F] :
    Algebra.IsSeparable K⟮t⁻¹⟯ F :=
  isSeparable_adjoin_inv_s12 t

end IntermediateField

namespace AlgebraicCurve

open scoped IntermediateField

section CharZeroSeparable

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem isSeparable_of_charZero_of_finiteDimensional [CharZero K]
    (S : IntermediateField K F) [FiniteDimensional ↥S F] :
    Algebra.IsSeparable ↥S F :=
  haveI : CharZero ↥S := IntermediateField.charZero S
  Algebra.IsSeparable.of_integral ↥S F

theorem isSeparable_adjoin_of_charZero_of_finiteDimensional [CharZero K] (t : F)
    [FiniteDimensional K⟮t⟯ F] : Algebra.IsSeparable K⟮t⟯ F :=
  isSeparable_of_charZero_of_finiteDimensional K⟮t⟯

end CharZeroSeparable

section SeparatingTranscendentalCore

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

def HasSeparatingTranscendentalCore : Prop :=
  ∃ t : F, Transcendental K t ∧ FiniteDimensional K⟮t⟯ F

variable {K F}

theorem hasSeparatingTranscendental_of_core [CharZero K]
    (h : HasSeparatingTranscendentalCore K F) :
    HasSeparatingTranscendental K F := by
  obtain ⟨t, ht, hfin⟩ := h
  haveI : Algebra.IsSeparable K⟮t⟯ F :=
    isSeparable_adjoin_of_charZero_of_finiteDimensional t
  exact ⟨t, ht, hfin, ‹_›,
    IntermediateField.finiteDimensional_adjoin_inv t,
    IntermediateField.isSeparable_adjoin_inv t⟩

theorem valSubringKaehlerFinite_of_core [CharZero K]
    (h : HasSeparatingTranscendentalCore K F) :
    ValSubringKaehlerFinite K F :=
  valSubringKaehlerFinite_of_hasSeparatingTranscendental
    (hasSeparatingTranscendental_of_core h)

end SeparatingTranscendentalCore

section MonicRatioResidue

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]

open RationalFunctionField

theorem ord_placeInfty_X_pow_natDegree_div {p : K[X]} (hp : p ≠ 0) :
    (p1PlaceInfty K).ord
        (algebraMap K[X] (RatFunc K) (X ^ p.natDegree) / algebraMap K[X] (RatFunc K) p) = 0 := by
  have hp' : algebraMap K[X] (RatFunc K) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hp
  have hXd : (X ^ p.natDegree : K[X]) ≠ 0 := pow_ne_zero _ X_ne_zero
  have hXd' : algebraMap K[X] (RatFunc K) (X ^ p.natDegree) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hXd
  rw [div_eq_mul_inv, (p1PlaceInfty K).ord_mul hXd' (inv_ne_zero hp'),
    (p1PlaceInfty K).ord_inv, ord_placeInfty_algebraMap' K hXd, ord_placeInfty_algebraMap' K hp,
    natDegree_X_pow]
  ring

theorem X_pow_natDegree_div_mem_placeInfty {p : K[X]} (hp : p ≠ 0) :
    algebraMap K[X] (RatFunc K) (X ^ p.natDegree) / algebraMap K[X] (RatFunc K) p
      ∈ (p1PlaceInfty K).toValuationSubring := by
  have hp' : algebraMap K[X] (RatFunc K) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hp
  have hXd' : algebraMap K[X] (RatFunc K) (X ^ p.natDegree) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr
      (pow_ne_zero _ X_ne_zero)
  exact (p1PlaceInfty K).mem_of_ord_nonneg (div_ne_zero hXd' hp')
    (ord_placeInfty_X_pow_natDegree_div K hp).ge

theorem degree_X_pow_natDegree_sub_lt_of_monic {p : K[X]} (hpmon : p.Monic) :
    ((X : K[X]) ^ p.natDegree - p).degree < p.degree := by
  have hdeg : ((X : K[X]) ^ p.natDegree).degree = p.degree := by
    rw [degree_X_pow, degree_eq_natDegree hpmon.ne_zero]
  refine (Polynomial.degree_sub_lt_left hdeg (pow_ne_zero _ X_ne_zero) ?_).trans_le hdeg.le
  rw [Polynomial.leadingCoeff_X_pow, hpmon]

end MonicRatioResidue

end AlgebraicCurve


open scoped IntermediateField Polynomial AlgebraicCurve AlgebraicCurve.RationalFunctionField

open KaehlerDifferential Module IntermediateField

namespace AlgebraicCurve

open RationalFunctionField

open RationalFunctionField

private theorem _root_.AlgebraicCurve.Place.differentialCoeff_add''
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]] (ω₁ ω₂ : Ω[F⁄K]) :
    v.differentialCoeff (ω₁ + ω₂) = v.differentialCoeff ω₁ + v.differentialCoeff ω₂ :=
  v.differentialCoeff_unique (by
    rw [add_smul, v.differentialCoeff_smul_dCoord, v.differentialCoeff_smul_dCoord])

section MonicRatioResidueChunk4

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]

theorem residue_placeInfty_X_pow_natDegree_div_monic_eq_one {p : K[X]} (hpmon : p.Monic) :
    IsLocalRing.residue _ ⟨_, X_pow_natDegree_div_mem_placeInfty K hpmon.ne_zero⟩
      = (1 : (p1PlaceInfty K).ResidueField) := by
  rw [← sub_eq_zero, show (1 : (p1PlaceInfty K).ResidueField) = IsLocalRing.residue _ 1 from
      (map_one _).symm, ← map_sub, IsLocalRing.residue_eq_zero_iff]

  set d := p.natDegree
  have hp' : algebraMap K[X] (RatFunc K) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hpmon.ne_zero

  have hsubmem : algebraMap K[X] (RatFunc K) (X ^ d - p) / algebraMap K[X] (RatFunc K) p
      ∈ (p1PlaceInfty K).toValuationSubring := by
    rcases eq_or_ne ((X : K[X]) ^ d - p) 0 with h0 | h0
    · simp only [h0, _root_.map_zero, zero_div]; exact zero_mem _
    have h0' : algebraMap K[X] (RatFunc K) (X ^ d - p) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr h0
    refine (p1PlaceInfty K).mem_of_ord_nonneg (div_ne_zero h0' hp') ?_
    rw [div_eq_mul_inv, (p1PlaceInfty K).ord_mul h0' (inv_ne_zero hp'),
      (p1PlaceInfty K).ord_inv, ord_placeInfty_algebraMap' K h0,
      ord_placeInfty_algebraMap' K hpmon.ne_zero]
    have hlt : ((X : K[X]) ^ d - p).natDegree < d :=
      Polynomial.natDegree_lt_natDegree h0 (degree_X_pow_natDegree_sub_lt_of_monic K hpmon)
    omega
  have hcoe : (⟨_, X_pow_natDegree_div_mem_placeInfty K hpmon.ne_zero⟩
        - 1 : (p1PlaceInfty K).toValuationSubring)
      = ⟨_, hsubmem⟩ := by
    refine Subtype.ext ?_
    show algebraMap K[X] (RatFunc K) (X ^ d) / algebraMap K[X] (RatFunc K) p - 1
      = algebraMap K[X] (RatFunc K) (X ^ d - p) / algebraMap K[X] (RatFunc K) p
    rw [map_sub, sub_div, div_self hp']
  rw [hcoe, Place.mk_mem_maximalIdeal_iff]
  rcases eq_or_ne ((X : K[X]) ^ d - p) 0 with h0 | h0
  · exact .inl (by simp [h0])
  · refine .inr ?_
    have h0' : algebraMap K[X] (RatFunc K) (X ^ d - p) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr h0
    rw [div_eq_mul_inv, (p1PlaceInfty K).ord_mul h0' (inv_ne_zero hp'),
      (p1PlaceInfty K).ord_inv, ord_placeInfty_algebraMap' K h0,
      ord_placeInfty_algebraMap' K hpmon.ne_zero]
    have hlt : ((X : K[X]) ^ d - p).natDegree < d :=
      Polynomial.natDegree_lt_natDegree h0 (degree_X_pow_natDegree_sub_lt_of_monic K hpmon)
    omega

end MonicRatioResidueChunk4

section NamedCarrier

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]

variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

def P1PlaceInftySimplePoleResidueEulerValueX : Prop :=
  ∀ (himem : p1PrincipalPartAtom K (X : K[X]) 1 1 * (p1PlaceInfty K).differentialCoeff (dX K)
        ∈ (p1PlaceInfty K).simplePoleSubmodule),
    Algebra.trace K (p1PlaceInfty K).ResidueField
        ((p1PlaceInfty K).simplePoleResidueAux ⟨_, himem⟩)
      = -1

end NamedCarrier

section MonicRatioReduction

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]

variable [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

theorem p1MonomialAtom_eq_monicRatio_mul {p : K[X]} (hpdeg : 1 ≤ p.natDegree) :
    p1PrincipalPartAtom K p (X ^ (p.natDegree - 1)) 1 * (p1PlaceInfty K).differentialCoeff (dX K)
      = (algebraMap K[X] (RatFunc K) (X ^ p.natDegree) / algebraMap K[X] (RatFunc K) p)
        * (p1PrincipalPartAtom K (X : K[X]) 1 1
            * (p1PlaceInfty K).differentialCoeff (dX K)) := by
  show algebraMap K[X] (RatFunc K) (X ^ (p.natDegree - 1)) / algebraMap K[X] (RatFunc K) p ^ 1
        * (p1PlaceInfty K).differentialCoeff (dX K)
    = algebraMap K[X] (RatFunc K) (X ^ p.natDegree) / algebraMap K[X] (RatFunc K) p
        * (algebraMap K[X] (RatFunc K) 1 / algebraMap K[X] (RatFunc K) X ^ 1
            * (p1PlaceInfty K).differentialCoeff (dX K))
  have hXd : algebraMap K[X] (RatFunc K) (X ^ p.natDegree)
      = algebraMap K[X] (RatFunc K) (X ^ (p.natDegree - 1)) * algebraMap K[X] (RatFunc K) X := by
    rw [← map_mul, ← pow_succ, Nat.sub_add_cancel hpdeg]
  have hX0 : algebraMap K[X] (RatFunc K) (X : K[X]) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr X_ne_zero
  rw [pow_one, pow_one, map_one, hXd, one_div]
  field_simp

theorem p1XInvAtom_mul_differentialCoeff_dX_mem_simplePole_placeInfty
    (hInfty : (p1PlaceInfty K).ordDifferential (dX K) = -2) :
    p1PrincipalPartAtom K (X : K[X]) 1 1 * (p1PlaceInfty K).differentialCoeff (dX K)
      ∈ (p1PlaceInfty K).simplePoleSubmodule :=
  p1MOneAtom_mul_differentialCoeff_mem_simplePole_placeInfty K (dX_ne_zero K) hInfty
    irreducible_X 1 (by rw [degree_one, degree_X]; decide)

theorem simplePoleResidueAux_placeInfty_monomial_eq_X
    (hInfty : (p1PlaceInfty K).ordDifferential (dX K) = -2)
    {p : K[X]} (hpmon : p.Monic) (hpirr : Irreducible p)
    (himem : p1PrincipalPartAtom K p (X ^ (p.natDegree - 1)) 1
          * (p1PlaceInfty K).differentialCoeff (dX K)
        ∈ (p1PlaceInfty K).simplePoleSubmodule) :
    (p1PlaceInfty K).simplePoleResidueAux ⟨_, himem⟩
      = (p1PlaceInfty K).simplePoleResidueAux
          ⟨_, p1XInvAtom_mul_differentialCoeff_dX_mem_simplePole_placeInfty K hInfty⟩ := by
  set hXmem := p1XInvAtom_mul_differentialCoeff_dX_mem_simplePole_placeInfty K hInfty

  have hfact := p1MonomialAtom_eq_monicRatio_mul K hpirr.natDegree_pos
  have hRatioMem := X_pow_natDegree_div_mem_placeInfty K hpmon.ne_zero
  have hprodmem : (algebraMap K[X] (RatFunc K) (X ^ p.natDegree)
          / algebraMap K[X] (RatFunc K) p)
        * (p1PrincipalPartAtom K (X : K[X]) 1 1 * (p1PlaceInfty K).differentialCoeff (dX K))
      ∈ (p1PlaceInfty K).simplePoleSubmodule :=
    (p1PlaceInfty K).mul_mem_simplePoleSubmodule_of_mem hRatioMem hXmem
  have heq : (⟨_, himem⟩ : (p1PlaceInfty K).simplePoleSubmodule) = ⟨_, hprodmem⟩ :=
    Subtype.ext hfact
  rw [heq, (p1PlaceInfty K).simplePoleResidueAux_mul_of_mem hRatioMem hXmem,
    residue_placeInfty_X_pow_natDegree_div_monic_eq_one K hpmon, one_mul]

theorem p1PlaceInftySimplePoleResidueEulerValueMonomial_of_X
    (hInfty : (p1PlaceInfty K).ordDifferential (dX K) = -2)
    (hX : P1PlaceInftySimplePoleResidueEulerValueX K) :
    P1PlaceInftySimplePoleResidueEulerValueMonomial K := by
  intro p hpmon hpirr himem
  rw [simplePoleResidueAux_placeInfty_monomial_eq_X K hInfty hpmon hpirr himem]
  exact hX _

end MonicRatioReduction

section ComposedEngineInftyX

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]

variable [CharZero K]
variable [HasCanonicalDivisor (K := K) (F := RatFunc K)] [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

theorem p1PrincipalPartMOneSimplePoleCancel_of_inftyX
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0) (heq : ω₀ = dX K)
    (hX : P1PlaceInftySimplePoleResidueEulerValueX K) :
    P1PrincipalPartMOneSimplePoleCancel K hω₀ :=
  p1PrincipalPartMOneSimplePoleCancel_of_inftyMonomial K hwd hω₀ heq
    (p1PlaceInftySimplePoleResidueEulerValueMonomial_of_X K
      (ordDifferential_placeInfty_D_ratFuncX K hwd) hX)

end ComposedEngineInftyX

end AlgebraicCurve

section
section


namespace IntermediateField

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

theorem finiteDimensional_top : FiniteDimensional ↥(⊤ : IntermediateField K E) E :=
  Module.Finite.of_surjective (Algebra.linearMap (↥(⊤ : IntermediateField K E)) E)
    fun x => ⟨⟨x, mem_top⟩, rfl⟩

theorem adjoin_simple_gen_eq_top (α : E) :
    K⟮AdjoinSimple.gen K α⟯ = (⊤ : IntermediateField K ↥K⟮α⟯) :=
  (K⟮α⟯).lift_injective <| by
    rw [lift_adjoin_simple, AdjoinSimple.coe_gen, lift_top]

theorem transcendental_gen {α : E} (hα : Transcendental K α) :
    Transcendental K (AdjoinSimple.gen K α) := by
  rw [show α = algebraMap K⟮α⟯ E (AdjoinSimple.gen K α) from
    (AdjoinSimple.algebraMap_gen K α).symm] at hα
  exact (transcendental_algebraMap_iff (algebraMap K⟮α⟯ E).injective).mp hα

end IntermediateField

namespace AlgebraicCurve

open RationalFunctionField

section PurelyTranscendentalSimple

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

def IsPurelyTranscendentalSimple : Prop :=
  ∃ t : F, Transcendental K t ∧ K⟮t⟯ = (⊤ : IntermediateField K F)

variable {K F}

theorem hasSeparatingTranscendentalCore_of_isPurelyTranscendentalSimple
    (h : IsPurelyTranscendentalSimple K F) :
    HasSeparatingTranscendentalCore K F := by
  obtain ⟨t, ht, htop⟩ := h
  haveI : FiniteDimensional ↥(⊤ : IntermediateField K F) F :=
    IntermediateField.finiteDimensional_top
  exact ⟨t, ht, IntermediateField.finiteDimensional_of_eq htop.symm⟩

end PurelyTranscendentalSimple

section SelfAdjoinInstance

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

theorem isPurelyTranscendentalSimple_adjoin_simple {α : E} (hα : Transcendental K α) :
    IsPurelyTranscendentalSimple K ↥K⟮α⟯ :=
  ⟨AdjoinSimple.gen K α, IntermediateField.transcendental_gen hα,
    IntermediateField.adjoin_simple_gen_eq_top α⟩

end SelfAdjoinInstance

section TowerComposites

variable {K F F' : Type*} [Field K] [Field F] [Field F']
variable [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']

end TowerComposites

section AdjoinTowerComposites

variable {K E F' : Type*} [Field K] [Field E] [Field F']
variable [Algebra K E] [Algebra K F']

end AdjoinTowerComposites

end AlgebraicCurve

namespace ModularCurve

open AlgebraicCurve


variable (N : ℕ) [NeZero N]

end ModularCurve

namespace AlgebraicCurve

open RationalFunctionField

end AlgebraicCurve

namespace ModularCurve

open AlgebraicCurve


end ModularCurve

section AxiomAudits

end AxiomAudits

end

end

section
section

set_option linter.unusedSectionVars false

noncomputable section


namespace AlgebraicCurve

open RationalFunctionField


variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]

section NamedRow

variable (K F)
variable [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

def CanonicalLocalResidueKSimplePoleCoordIndep : Prop :=
  ∀ (v : Place K F) (π' : F), v.ord π' = 1 →
    ∀ (R : v.CanonicalLocalResidueDataK),
      R.res (v.differentialCoeff (KaehlerDifferential.D K F π') * (π')⁻¹) = 1

end NamedRow

section SATGate

variable [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

end SATGate

section XInvCoordinate

variable (K) [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

theorem p1XAtom_mul_differentialCoeff_dX_eq_neg :
    p1PrincipalPartAtom K (X : K[X]) 1 1 * (p1PlaceInfty K).differentialCoeff (dX K)
      = -((p1PlaceInfty K).differentialCoeff
            (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹)
          * ((RatFunc.X : RatFunc K)⁻¹)⁻¹) := by
  show algebraMap K[X] (RatFunc K) 1 / algebraMap K[X] (RatFunc K) X ^ 1
        * (p1PlaceInfty K).differentialCoeff (dX K)
      = -((p1PlaceInfty K).differentialCoeff
            (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹)
          * ((RatFunc.X : RatFunc K)⁻¹)⁻¹)
  rw [show (dX K) = KaehlerDifferential.D K (RatFunc K) RatFunc.X from rfl,
    differentialCoeff_placeInfty_D_X_eq K, RatFunc.algebraMap_X, map_one, pow_one, inv_inv,
    one_div]
  field_simp [RatFunc.X_ne_zero (K := K), sq, mul_comm]

end XInvCoordinate

section InftyXDischarge

variable (K) [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

theorem trace_placeInfty_residueField_one :
    Algebra.trace K (p1PlaceInfty K).ResidueField 1 = 1 := by
  rw [show (1 : (p1PlaceInfty K).ResidueField) = algebraMap K _ 1 from (map_one _).symm,
    Algebra.trace_algebraMap, show Module.finrank K (p1PlaceInfty K).ResidueField = 1 from
      deg_placeInfty K, one_smul]

theorem simplePoleResidueAux_placeInfty_p1XAtom_eq_neg_one
    (hsp : CanonicalLocalResidueKSimplePoleCoordIndep K (RatFunc K))
    (himem : p1PrincipalPartAtom K (X : K[X]) 1 1 * (p1PlaceInfty K).differentialCoeff (dX K)
        ∈ (p1PlaceInfty K).simplePoleSubmodule) :
    (p1PlaceInfty K).simplePoleResidueAux ⟨_, himem⟩ = -1 := by

  set R := (p1PlaceInfty K).canonicalLocalResidueDataKOfExtend
  rw [← (p1PlaceInfty K).localResidueData_res_eq_simplePoleResidueAux R.toLocalResidueData himem,
    show R.toLocalResidueData.res = R.res from rfl,
    p1XAtom_mul_differentialCoeff_dX_eq_neg K, _root_.map_neg,
    hsp (p1PlaceInfty K) (RatFunc.X : RatFunc K)⁻¹ (ord_placeInfty_X_inv K) R]

theorem p1PlaceInftySimplePoleResidueEulerValueX_of_simplePoleCoordIndep
    (hsp : CanonicalLocalResidueKSimplePoleCoordIndep K (RatFunc K)) :
    P1PlaceInftySimplePoleResidueEulerValueX K := by
  intro himem
  rw [simplePoleResidueAux_placeInfty_p1XAtom_eq_neg_one K hsp himem, _root_.map_neg,
    trace_placeInfty_residueField_one K]

end InftyXDischarge

section ComposedEngine

variable (K) [DecidableEq (RatFunc K)] [CharZero K]
variable [HasCanonicalDivisor (K := K) (F := RatFunc K)] [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

theorem p1PrincipalPartMOneSimplePoleCancel_of_simplePoleCoordIndep
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0) (heq : ω₀ = dX K)
    (hsp : CanonicalLocalResidueKSimplePoleCoordIndep K (RatFunc K)) :
    P1PrincipalPartMOneSimplePoleCancel K hω₀ :=
  p1PrincipalPartMOneSimplePoleCancel_of_inftyX K hwd hω₀ heq
    (p1PlaceInftySimplePoleResidueEulerValueX_of_simplePoleCoordIndep K hsp)

end ComposedEngine

section Monotonicity

variable (K) [DecidableEq (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

end Monotonicity

end AlgebraicCurve

section AxiomAudit

end AxiomAudit

end
end

end

section
section


namespace IntermediateField

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem adjoin_simple_map_algHom' (e : F →ₐ[K] F') (t : F) :
    (K⟮t⟯).map e = K⟮e t⟯ := by
  rw [adjoin_map, Set.image_singleton]

theorem adjoin_simple_eq_top_of_algEquiv (e : F ≃ₐ[K] F') {t : F}
    (htop : K⟮t⟯ = (⊤ : IntermediateField K F)) :
    K⟮e t⟯ = (⊤ : IntermediateField K F') := by
  have key : K⟮(e : F →ₐ[K] F') t⟯ = (⊤ : IntermediateField K F') := by
    rw [← adjoin_simple_map_algHom' (e : F →ₐ[K] F') t, htop,
      ← AlgHom.fieldRange_eq_map, AlgEquiv.fieldRange_eq_top]
  exact key

end IntermediateField

namespace AlgebraicCurve

open RationalFunctionField

section Congr

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem IsPurelyTranscendentalSimple.congr (e : F ≃ₐ[K] F')
    (h : IsPurelyTranscendentalSimple K F) : IsPurelyTranscendentalSimple K F' := by
  obtain ⟨t, ht, htop⟩ := h
  refine ⟨e t, ?_, IntermediateField.adjoin_simple_eq_top_of_algEquiv e htop⟩
  unfold Transcendental at ht ⊢
  rw [show (e t : F') = (e : F →ₐ[K] F') t from rfl,
    isAlgebraic_algHom_iff (e : F →ₐ[K] F') e.injective]
  exact ht

end Congr

section RatFuncInstance

variable (K : Type*) [Field K]

theorem isPurelyTranscendentalSimple_ratFunc :
    IsPurelyTranscendentalSimple K (RatFunc K) :=
  (isPurelyTranscendentalSimple_adjoin_simple (RatFunc.transcendental_X (K := K))).congr
    (RatFunc.algEquivOfTranscendental (RatFunc.X : RatFunc K)
      (RatFunc.transcendental_X (K := K))).symm

end RatFuncInstance

section Iff

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem isPurelyTranscendentalSimple_of_ratFuncAlgEquiv
    (h : Nonempty (RatFunc K ≃ₐ[K] F)) : IsPurelyTranscendentalSimple K F :=
  (isPurelyTranscendentalSimple_ratFunc K).congr h.some

end Iff

section CharZeroReflection

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

end CharZeroReflection

section TowerComposites

variable {K F F' : Type*} [Field K] [Field F] [Field F']
variable [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']

end TowerComposites

end AlgebraicCurve

namespace ModularCurve

open AlgebraicCurve


variable (N : ℕ) [NeZero N]

end ModularCurve

namespace AlgebraicCurve

open RationalFunctionField

end AlgebraicCurve

namespace ModularCurve

open AlgebraicCurve


end ModularCurve

section AxiomAudits

end AxiomAudits

end

end

section
section


namespace AlgebraicCurve

open RationalFunctionField

section AbstractEngine

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem Place.dCoordGenerates_of_valSubringKaehlerFinite_of_charZero
    [CharZero K] [∀ v : Place K F, v.FiniteResidue]
    (hfin : ValSubringKaehlerFinite K F) (v : Place K F) :
    v.DCoordGenerates :=
  Place.dCoordGenerates_of_valSubringKaehlerSpanTop
    (valSubringKaehlerSpanTop_of_kaehlerFinite_of_charZero hfin) v

end AbstractEngine

section ChainComposites

variable {K F F' : Type*} [Field K] [Field F] [Field F']
variable [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']

theorem Place.dCoordGenerates_of_isPurelyTranscendentalSimple
    [CharZero K] [∀ v : Place K F, v.FiniteResidue]
    (h : IsPurelyTranscendentalSimple K F) (v : Place K F) :
    v.DCoordGenerates :=
  Place.dCoordGenerates_of_valSubringKaehlerFinite_of_charZero
    (valSubringKaehlerFinite_of_core
      (hasSeparatingTranscendentalCore_of_isPurelyTranscendentalSimple h)) v

end ChainComposites

end AlgebraicCurve

namespace ModularCurve

open AlgebraicCurve


variable (N : ℕ) [NeZero N]

end ModularCurve

namespace ModularCurve

open AlgebraicCurve


variable (N : ℕ) [NeZero N]

theorem gate_dCoordGenerates_of_ratFunc_sat
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    [CharZero K] [∀ v : Place K F, v.FiniteResidue]
    (hRat : Nonempty (RatFunc K ≃ₐ[K] F)) (v : Place K F) :
    v.DCoordGenerates :=
  Place.dCoordGenerates_of_isPurelyTranscendentalSimple
    (isPurelyTranscendentalSimple_of_ratFuncAlgEquiv hRat) v

end ModularCurve

section AxiomAudits

end AxiomAudits

end

end

section
section

noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000


namespace AlgebraicCurve

open RationalFunctionField

namespace RationalFunctionField

variable {K : Type*} [Field K]

scoped instance (priority := low) instDCoordGenerates [CharZero K] (v : Place K (RatFunc K)) :
    v.DCoordGenerates :=
  ModularCurve.gate_dCoordGenerates_of_ratFunc_sat ⟨AlgEquiv.refl⟩ v

end RationalFunctionField

section TransportTwoRoutes

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K]

end TransportTwoRoutes

section ConsumerDemonstrations

variable {K : Type*} [Field K] [CharZero K]

end ConsumerDemonstrations

end AlgebraicCurve

namespace ModularCurve

open AlgebraicCurve


section RatBasePinned

end RatBasePinned

section RatBaseCrossing

end RatBaseCrossing

end ModularCurve

section AxiomAudits

end AxiomAudits

end
end

end

section
section

noncomputable section


namespace AlgebraicCurve

open RationalFunctionField


section Uniqueness

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

end Uniqueness

section Profile

variable (K : Type*) [Field K]

theorem exists_smul_dX_eq (ω : Ω[(RatFunc K)⁄K]) : ∃ c : RatFunc K, c • dX K = ω := by
  have hmem : ω ∈ Submodule.span (RatFunc K) {dX K} :=
    span_dX_eq_top K ▸ Submodule.mem_top
  exact Submodule.mem_span_singleton.mp hmem

section ProfileValues

variable [CharZero K] [DecidableEq (RatFunc K)]

theorem ordDifferential_dX_of_ne_placeInfty {v : Place K (RatFunc K)}
    (hv : v ≠ p1PlaceInfty K) : v.ordDifferential (dX K) = 0 := by
  rw [Place.ordDifferential]
  exact p1DifferentialCoeffUnitFinite_dX K v hv

theorem ordDifferential_dX_placeInfty :
    (p1PlaceInfty K).ordDifferential (dX K) = -2 :=
  ordDifferential_placeInfty_D_ratFuncX K (ordDifferentialWellDefined_ratFunc K)

theorem exists_divisor_smul_dX {c : RatFunc K} (hc : c ≠ 0) :
    ∃ D : Divisor K (RatFunc K),
      (∀ v : Place K (RatFunc K), D v = v.ordDifferential (c • dX K)) ∧
        Divisor.degree D = -2 := by
  obtain ⟨Dc, hDc, hDcdeg⟩ :=
    HasPrincipalDivisors.exists_divisor (K := K) (F := RatFunc K) c hc
  refine ⟨Dc + Finsupp.single (p1PlaceInfty K) (-2), fun v => ?_, ?_⟩
  ·
    rw [Finsupp.add_apply, hDc v,
      v.ordDifferential_smul hc (v.differentialCoeff_ne_zero (dX_ne_zero K))]
    rcases eq_or_ne v (p1PlaceInfty K) with rfl | hne
    · rw [ordDifferential_dX_placeInfty K, Finsupp.single_eq_same]
    · rw [ordDifferential_dX_of_ne_placeInfty K hne, Finsupp.single_eq_of_ne hne]
  ·
    rw [map_add, hDcdeg, zero_add, Divisor.degree_single, deg_placeInfty K, Nat.cast_one,
      mul_one]

end ProfileValues

section Instance

variable [CharZero K]

scoped instance instHasCanonicalDivisorRatFunc :
    HasCanonicalDivisor (K := K) (F := RatFunc K) where
  exists_divisor ω hω := by
    classical
    obtain ⟨c, hc⟩ := exists_smul_dX_eq K ω
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact hω hc.symm
    obtain ⟨D, hD, -⟩ := exists_divisor_smul_dX K hc0
    refine ⟨D, fun v => ?_⟩
    rw [← hc]
    exact hD v

end Instance

section ExactDivisor

variable [CharZero K] [DecidableEq (RatFunc K)]

end ExactDivisor

end Profile

section RatDiamond

end RatDiamond

end AlgebraicCurve

namespace ModularCurve

open AlgebraicCurve


end ModularCurve

section AxiomAudit

end AxiomAudit

end
end

end

section
section

set_option linter.unusedSectionVars false

noncomputable section


namespace AlgebraicCurve

open RationalFunctionField



section KaehlerToolbox

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]

namespace Place
variable (v : Place K F)
end Place
end KaehlerToolbox
section DXCoeffIntegrality
variable {K : Type*} [Field K]
theorem ratFuncDXCoeff_eq_of_D_eq_smul_dX {f e : RatFunc K}
    (h : KaehlerDifferential.D K (RatFunc K) f = e • dX K) : ratFuncDXCoeff K f = e := by
  have key : (ratFuncDXCoeff K f - e) • dX K = 0 := by
    rw [sub_smul, ← D_eq_ratFuncDXCoeff_smul_dX K f, h, sub_self]
  rcases smul_eq_zero.mp key with h' | h'
  · exact sub_eq_zero.mp h'
  · exact absurd h' (dX_ne_zero K)

theorem ratFuncDXCoeff_zero : ratFuncDXCoeff K (0 : RatFunc K) = 0 :=
  ratFuncDXCoeff_eq_of_D_eq_smul_dX (by rw [_root_.map_zero, zero_smul])

section FinitePlaces

variable {w : HeightOneSpectrum K[X]}

local notation "vw" => Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w

theorem ord_algebraMap_denom_eq_zero_of_ord_nonneg {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) {f : RatFunc K}
    (hf : f ≠ 0) (hord : 0 ≤ (vw).ord f) :
    (vw).ord (algebraMap K[X] (RatFunc K) f.denom) = 0 := by
  by_contra hne
  have hpd : p ∣ f.denom := by
    rw [← Ideal.mem_span_singleton, ← hwp]
    exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
      f.denom_ne_zero).mp hne
  have hpn : ¬ p ∣ f.num := fun hpn =>
    hp.not_isUnit (f.isCoprime_num_denom.isUnit_of_dvd' hpn hpd)
  have hordn : (vw).ord (algebraMap K[X] (RatFunc K) f.num) = 0 := by
    by_contra h
    exact hpn (by
      rw [← Ideal.mem_span_singleton, ← hwp]
      exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
        (RatFunc.num_ne_zero hf)).mp h)
  have hordd : 0 < (vw).ord (algebraMap K[X] (RatFunc K) f.denom) :=
    lt_of_le_of_ne ((vw).ord_nonneg_of_mem (algebraMap_mem_ofHeightOneSpectrum K w _))
      (Ne.symm hne)
  have hnum0 : algebraMap K[X] (RatFunc K) f.num ≠ 0 :=
    RatFunc.algebraMap_ne_zero (RatFunc.num_ne_zero hf)
  have hden0 : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero f.denom_ne_zero
  rw [← f.num_div_denom, div_eq_mul_inv, (vw).ord_mul hnum0 (inv_ne_zero hden0),
    (vw).ord_inv, hordn] at hord
  omega

theorem ratFuncDXCoeff_eq_zero_or_ord_nonneg_of_ord_nonneg {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) {g : RatFunc K}
    (hg : g ≠ 0) (hord : 0 ≤ (vw).ord g) :
    ratFuncDXCoeff K g = 0 ∨ 0 ≤ (vw).ord (ratFuncDXCoeff K g) := by
  rcases eq_or_ne (ratFuncDXCoeff K g) 0 with h0 | hne
  · exact Or.inl h0
  refine Or.inr ?_
  have hW : g.num.derivative * g.denom - g.num * g.denom.derivative ≠ 0 :=
    wronskian_ne_zero_of_ratFuncDXCoeff_ne_zero K hne
  have hW' : algebraMap K[X] (RatFunc K)
      (g.num.derivative * g.denom - g.num * g.denom.derivative) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hW
  have hd' : algebraMap K[X] (RatFunc K) g.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero g.denom_ne_zero
  have hWord : 0 ≤ (vw).ord (algebraMap K[X] (RatFunc K)
      (g.num.derivative * g.denom - g.num * g.denom.derivative)) :=
    (vw).ord_nonneg_of_mem (algebraMap_mem_ofHeightOneSpectrum K w _)
  have hden : (vw).ord (algebraMap K[X] (RatFunc K) g.denom) = 0 :=
    ord_algebraMap_denom_eq_zero_of_ord_nonneg hp hwp hg hord
  have key : (vw).ord (ratFuncDXCoeff K g)
      = (vw).ord (algebraMap K[X] (RatFunc K)
          (g.num.derivative * g.denom - g.num * g.denom.derivative))
        - 2 * (vw).ord (algebraMap K[X] (RatFunc K) g.denom) := by
    rw [ratFuncDXCoeff_def, div_eq_mul_inv,
      (vw).ord_mul hW' (inv_ne_zero (pow_ne_zero 2 hd')), (vw).ord_inv, ← zpow_natCast,
      (vw).ord_zpow]
    push_cast
    ring
  rw [key, hden]
  omega

end FinitePlaces

section PlaceInftySide

variable [DecidableEq (RatFunc K)]

theorem ratFuncDXCoeff_ne_zero_and_ord_placeInfty_eq_two_of_ord_eq_one
    {f : RatFunc K} (hf : f ≠ 0) (hord : (p1PlaceInfty K).ord f = 1) :
    ratFuncDXCoeff K f ≠ 0 ∧ (p1PlaceInfty K).ord (ratFuncDXCoeff K f) = 2 := by
  obtain ⟨e, he0, heord, hDe⟩ := exists_dXCoeff_ord_two_of_ord_placeInfty_eq_one hf hord
  rw [ratFuncDXCoeff_eq_of_D_eq_smul_dX hDe]
  exact ⟨he0, heord⟩

theorem ratFuncDXCoeff_eq_zero_or_two_le_ord_placeInfty_of_ord_nonneg
    {g : RatFunc K} (hg : g ≠ 0) (hord : 0 ≤ (p1PlaceInfty K).ord g) :
    ratFuncDXCoeff K g = 0 ∨ 2 ≤ (p1PlaceInfty K).ord (ratFuncDXCoeff K g) := by
  rcases eq_or_ne (ratFuncDXCoeff K g) 0 with h0 | hne
  · exact Or.inl h0
  refine Or.inr ?_
  rcases eq_or_lt_of_le hord with heq | hlt
  ·
    obtain ⟨e, he, hDe⟩ := exists_dXCoeff_ord_ge_two_of_ord_placeInfty_eq_zero hg heq.symm
    have hee := ratFuncDXCoeff_eq_of_D_eq_smul_dX hDe
    rcases he with rfl | h2
    · exact absurd hee hne
    · rw [hee]; exact h2
  ·
    have hW : g.num.derivative * g.denom - g.num * g.denom.derivative ≠ 0 :=
      wronskian_ne_zero_of_ratFuncDXCoeff_ne_zero K hne
    have h := ord_placeInfty_ratFuncDXCoeff_ge hg hW
    omega

end PlaceInftySide

end DXCoeffIntegrality

section LemmaA

variable {K : Type*} [Field K] [CharZero K]

theorem ratFuncDXCoeff_uniformizer_ne_zero_and_ord_le (v : Place K (RatFunc K))
    {g : RatFunc K} (hg : g ∈ v.toValuationSubring) :
    ratFuncDXCoeff K v.uniformizer ≠ 0 ∧
      (ratFuncDXCoeff K g = 0 ∨
        v.ord (ratFuncDXCoeff K v.uniformizer) ≤ v.ord (ratFuncDXCoeff K g)) := by
  classical
  have hg0 : 0 ≤ v.ord g := v.ord_nonneg_of_mem hg
  rcases eq_or_ne g 0 with rfl | hgne
  ·
    refine ⟨?_, Or.inl (ratFuncDXCoeff_zero (K := K))⟩
    rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
    · obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
      exact (ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one hp hwp hp.separable
        (Place.uniformizer_ne_zero _) (Place.ord_uniformizer _)).1
    · exact (ratFuncDXCoeff_ne_zero_and_ord_placeInfty_eq_two_of_ord_eq_one
        ((p1PlaceInfty K).uniformizer_ne_zero) ((p1PlaceInfty K).ord_uniformizer)).1
  · rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
    ·
      obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
      obtain ⟨hπne, hπord⟩ := ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one hp hwp
        hp.separable (Place.uniformizer_ne_zero _) (Place.ord_uniformizer _)
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

theorem differentialCoeff_D_eq_ratFuncDXCoeff_div (v : Place K (RatFunc K)) (f : RatFunc K)
    (hπ : ratFuncDXCoeff K v.uniformizer ≠ 0) :
    v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) f)
      = ratFuncDXCoeff K f / ratFuncDXCoeff K v.uniformizer :=
  v.differentialCoeff_unique (by
    rw [show v.dCoord = KaehlerDifferential.D K (RatFunc K) v.uniformizer from rfl,
      D_eq_ratFuncDXCoeff_smul_dX K v.uniformizer, D_eq_ratFuncDXCoeff_smul_dX K f,
      smul_smul, div_mul_cancel₀ _ hπ])

theorem differentialCoeff_D_mem_of_mem (v : Place K (RatFunc K))
    {g : RatFunc K} (hg : g ∈ v.toValuationSubring) :
    v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) g) ∈ v.toValuationSubring := by
  obtain ⟨hπne, hcase⟩ := ratFuncDXCoeff_uniformizer_ne_zero_and_ord_le v hg
  rw [differentialCoeff_D_eq_ratFuncDXCoeff_div v g hπne]
  rcases hcase with h0 | hle
  · rw [h0, zero_div]; exact zero_mem _
  · rcases eq_or_ne (ratFuncDXCoeff K g) 0 with h0 | hgne'
    · rw [h0, zero_div]; exact zero_mem _
    · refine v.mem_of_ord_nonneg (div_ne_zero hgne' hπne) ?_
      rw [div_eq_mul_inv, v.ord_mul hgne' (inv_ne_zero hπne), v.ord_inv]
      omega

end LemmaA

section ExactDifferentialEngine

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]

namespace Place

variable (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

theorem CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_of_surj [CharZero K]
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    (hint : ∀ h : F, h ∈ v.toValuationSubring →
      v.differentialCoeff (KaehlerDifferential.D K F h) ∈ v.toValuationSubring)
    (R : v.CanonicalLocalResidueDataK) (π' : F) {n : ℕ} (hn : 1 ≤ n) :
    R.res (v.differentialCoeff (KaehlerDifferential.D K F π') * ((π') ^ (n + 1))⁻¹) = 0 := by
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn

  have hres : R.res (v.differentialCoeff (KaehlerDifferential.D K F (((π') ^ (m + 1))⁻¹))) = 0 :=
    CanonicalLocalResidueDataK.res_differentialCoeff_D_of_surj v hsurj hint R _

  have hpow : v.differentialCoeff (KaehlerDifferential.D K F (((π') ^ (m + 1))⁻¹))
      = -((m + 1 : ℕ) : F) * (((π') ^ (m + 2))⁻¹
          * v.differentialCoeff (KaehlerDifferential.D K F π')) := by
    rw [D_pow_succ_inv, v.differentialCoeff_smul]
    ring

  have hne : -(((m + 1 : ℕ) : F)) ≠ 0 := by
    simp only [ne_eq, neg_eq_zero, Nat.cast_eq_zero]
    omega

  have hkey : v.differentialCoeff (KaehlerDifferential.D K F π') * ((π') ^ (1 + m + 1))⁻¹
      = (-((m + 1 : ℕ) : K))⁻¹
          • v.differentialCoeff (KaehlerDifferential.D K F (((π') ^ (m + 1))⁻¹)) := by
    rw [Algebra.smul_def, map_inv₀, _root_.map_neg, map_natCast, hpow,
      show 1 + m + 1 = m + 2 from by omega, inv_mul_cancel_left₀ hne]
    ring
  rw [hkey, map_smul, hres, smul_zero]

theorem CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_inv_of_integral
    (hint : ∀ h : F, h ∈ v.toValuationSubring →
      v.differentialCoeff (KaehlerDifferential.D K F h) ∈ v.toValuationSubring)
    (R : v.CanonicalLocalResidueDataK) {π' : F} (hπ' : v.ord π' = 1) :
    R.res (v.differentialCoeff (KaehlerDifferential.D K F π') * (π')⁻¹) = 1 := by
  have hπ'0 : π' ≠ 0 := by
    intro h
    rw [h, v.ord_zero] at hπ'
    exact zero_ne_one hπ'
  have hπv0 : v.uniformizer ≠ 0 := v.uniformizer_ne_zero

  set w : F := π' * (v.uniformizer)⁻¹ with hw_def
  have hw0 : w ≠ 0 := mul_ne_zero hπ'0 (inv_ne_zero hπv0)
  have hword : v.ord w = 0 := by
    rw [hw_def, v.ord_mul hπ'0 (inv_ne_zero hπv0), v.ord_inv, hπ', v.ord_uniformizer]
    ring
  have hwmem : w ∈ v.toValuationSubring := v.mem_of_ord_nonneg hw0 hword.ge
  have hwinvmem : w⁻¹ ∈ v.toValuationSubring := by
    refine v.mem_of_ord_nonneg (inv_ne_zero hw0) ?_
    rw [v.ord_inv, hword]
    omega

  have hπ'_eq : π' = v.uniformizer * w := by
    rw [hw_def, mul_comm π' (v.uniformizer)⁻¹, ← mul_assoc, mul_inv_cancel₀ hπv0, one_mul]

  have hD : KaehlerDifferential.D K F π'
      = v.uniformizer • KaehlerDifferential.D K F w
        + w • KaehlerDifferential.D K F v.uniformizer := by
    conv_lhs => rw [hπ'_eq]
    exact Derivation.leibniz _ _ _

  have hcoeff : v.differentialCoeff (KaehlerDifferential.D K F π')
      = v.uniformizer * v.differentialCoeff (KaehlerDifferential.D K F w) + w := by
    rw [hD, v.differentialCoeff_add'', v.differentialCoeff_smul, v.differentialCoeff_smul,
      show KaehlerDifferential.D K F v.uniformizer = v.dCoord from rfl,
      v.differentialCoeff_dCoord, mul_one]

  have hsplit : v.differentialCoeff (KaehlerDifferential.D K F π') * (π')⁻¹
      = v.differentialCoeff (KaehlerDifferential.D K F w) * w⁻¹ + (v.uniformizer)⁻¹ := by
    rw [hcoeff, hπ'_eq, mul_inv]
    field_simp
  rw [hsplit, map_add, gate_canonicalLocalResidueDataK_uniformizer_inv v R,
    R.res_of_mem _ (mul_mem (hint w hwmem) hwinvmem), zero_add]

end Place

end ExactDifferentialEngine

section RatFuncClauses

variable {K : Type*} [Field K] [CharZero K] [HasCanonicalLocalResidueKStar K (RatFunc K)]

theorem canonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_ratFunc
    (v : Place K (RatFunc K)) (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    (π' : RatFunc K) (R : v.CanonicalLocalResidueDataK) {n : ℕ} (hn : 1 ≤ n) :
    R.res (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) π')
      * ((π') ^ (n + 1))⁻¹) = 0 :=
  Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_of_surj v hsurj
    (fun _ hh => differentialCoeff_D_mem_of_mem v hh) R π' hn

theorem canonicalLocalResidueDataK_res_differentialCoeff_D_mul_inv_ratFunc
    (v : Place K (RatFunc K)) {π' : RatFunc K} (hπ' : v.ord π' = 1)
    (R : v.CanonicalLocalResidueDataK) :
    R.res (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) π') * (π')⁻¹) = 1 :=
  Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_inv_of_integral v
    (fun _ hh => differentialCoeff_D_mem_of_mem v hh) R hπ'

end RatFuncClauses

theorem canonicalLocalResidueKSimplePoleCoordIndep_ratFunc (K : Type*) [Field K] [CharZero K]
    [HasCanonicalLocalResidueKStar K (RatFunc K)] :
    CanonicalLocalResidueKSimplePoleCoordIndep K (RatFunc K) :=
  fun v _ hπ' R => canonicalLocalResidueDataK_res_differentialCoeff_D_mul_inv_ratFunc v hπ' R

section PlaceInftyConsumers

variable (K : Type*) [Field K] [CharZero K] [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)]

theorem canonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_placeInfty
    (π' : RatFunc K) (R : (p1PlaceInfty K).CanonicalLocalResidueDataK) {n : ℕ} (hn : 1 ≤ n) :
    R.res ((p1PlaceInfty K).differentialCoeff (KaehlerDifferential.D K (RatFunc K) π')
      * ((π') ^ (n + 1))⁻¹) = 0 :=
  canonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_ratFunc (p1PlaceInfty K)
    (surjective_algebraMap_residueField_placeInfty K) π' R hn

theorem canonicalLocalResidueDataK_res_X_pow_mul_D_X
    (R : (p1PlaceInfty K).CanonicalLocalResidueDataK) (n : ℕ) :
    R.res ((RatFunc.X : RatFunc K) ^ n
        * (p1PlaceInfty K).differentialCoeff
            (KaehlerDifferential.D K (RatFunc K) RatFunc.X)) = 0 := by
  rw [X_pow_mul_differentialCoeff_D_X_eq_neg K n, _root_.map_neg, neg_eq_zero]
  exact canonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_placeInfty K
    (RatFunc.X : RatFunc K)⁻¹ R (Nat.le_add_left 1 n)

theorem canonicalLocalResidueDataK_kaehlerResidueTerm_X_pow
    (R : (p1PlaceInfty K).CanonicalLocalResidueDataK) (n : ℕ) :
    Algebra.trace K (p1PlaceInfty K).ResidueField
        (R.res (diagonalHom K (RatFunc K) ((RatFunc.X : RatFunc K) ^ n) (p1PlaceInfty K)
          * (p1PlaceInfty K).differentialCoeff
              (KaehlerDifferential.D K (RatFunc K) RatFunc.X))) = 0 := by
  rw [diagonalHom_apply, canonicalLocalResidueDataK_res_X_pow_mul_D_X K R n, _root_.map_zero]

end PlaceInftyConsumers

section AlgClosedDischarge

variable (K : Type*) [Field K] [CharZero K] [HasCanonicalLocalResidueKStar K (RatFunc K)]

theorem surjective_algebraMap_residueField_of_deg_eq_one {F : Type*} [Field F] [Algebra K F]
    (v : Place K F) (hdeg : v.deg = 1) :
    Function.Surjective (algebraMap K v.ResidueField) := by
  intro z
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : v.ResidueField) one_ne_zero).mp
    (show Module.finrank K v.ResidueField = 1 from hdeg) z
  exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc⟩

theorem surjective_algebraMap_residueField_ratFunc_of_isAlgClosed [IsAlgClosed K]
    (v : Place K (RatFunc K)) :
    Function.Surjective (algebraMap K v.ResidueField) := by
  classical
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  · obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
    refine surjective_algebraMap_residueField_of_deg_eq_one K _ ?_
    rw [deg_ofHeightOneSpectrum K hwp]
    have h := IsAlgClosed.degree_eq_one_of_irreducible K hp
    rw [degree_eq_natDegree hp.ne_zero] at h
    exact_mod_cast h
  · exact surjective_algebraMap_residueField_placeInfty K

variable [IsAlgClosed K]

theorem canonicalLocalResidueKDifferentialCoordIndep_ratFunc_of_isAlgClosed :
    CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K) :=
  fun v π' _ R _ hn =>
    canonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_ratFunc v
      (surjective_algebraMap_residueField_ratFunc_of_isAlgClosed K v) π' R hn

end AlgClosedDischarge

end AlgebraicCurve

section AxiomAudit

end AxiomAudit

end

end

end

section
section

noncomputable section


namespace AlgebraicCurve

open RationalFunctionField


section PerfectDCoord

variable (K : Type*) [Field K] [PerfectField K]

theorem exists_ne_zero_smul_dX_of_uniformizer (v : Place K (RatFunc K)) :
    ∃ c : RatFunc K, c ≠ 0 ∧
      KaehlerDifferential.D K (RatFunc K) v.uniformizer = c • dX K := by
  classical
  have hord : v.ord v.uniformizer = 1 := v.ord_uniformizer
  have hpi0 : v.uniformizer ≠ 0 := v.uniformizer_ne_zero
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  ·
    obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
    obtain ⟨hne, -⟩ := ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one hp hwp
      (PerfectField.separable_of_irreducible hp) hpi0 hord
    exact ⟨ratFuncDXCoeff K _, hne, D_eq_ratFuncDXCoeff_smul_dX K _⟩
  ·
    obtain ⟨e, he0, -, hDe⟩ := exists_dXCoeff_ord_two_of_ord_placeInfty_eq_one hpi0 hord
    exact ⟨e, he0, hDe⟩

namespace RationalFunctionField

scoped instance (priority := low) instDCoordGeneratesPerfectField (v : Place K (RatFunc K)) :
    v.DCoordGenerates := by
  obtain ⟨c, hc0, hDc⟩ := exists_ne_zero_smul_dX_of_uniformizer K v
  refine ⟨?_⟩
  have hdc : v.dCoord = KaehlerDifferential.D K (RatFunc K) v.uniformizer := rfl
  rw [hdc, hDc, eq_top_iff, ← span_dX_eq_top K, Submodule.span_singleton_le_iff_mem]
  exact Submodule.mem_span_singleton.mpr
    ⟨c⁻¹, by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]⟩

end RationalFunctionField

end PerfectDCoord

section Profile

variable (K : Type*) [Field K]

section PerfectProfileValues

variable [PerfectField K] [DecidableEq (RatFunc K)]

theorem p1DifferentialCoeffUnitFinite_dX_of_perfectField :
    P1DifferentialCoeffUnitFinite K (dX_ne_zero K) := by
  intro v hvinf
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  · obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
    exact ord_differentialCoeff_dX_ofHeightOneSpectrum hp hwp
      (PerfectField.separable_of_irreducible hp)
  · exact absurd rfl hvinf

theorem p1DifferentialCoeffRegularFinite_dX_of_perfectField :
    P1DifferentialCoeffRegularFinite K (dX_ne_zero K) :=
  fun v hv => v.mem_of_ord_nonneg (v.differentialCoeff_ne_zero (dX_ne_zero K))
    (p1DifferentialCoeffUnitFinite_dX_of_perfectField K v hv).ge

theorem ordDifferential_dX_of_ne_placeInfty_of_perfectField {v : Place K (RatFunc K)}
    (hv : v ≠ p1PlaceInfty K) : v.ordDifferential (dX K) = 0 := by
  rw [Place.ordDifferential]
  exact p1DifferentialCoeffUnitFinite_dX_of_perfectField K v hv

theorem ordDifferential_dX_placeInfty_of_perfectField :
    (p1PlaceInfty K).ordDifferential (dX K) = -2 :=
  ordDifferential_placeInfty_D_ratFuncX K
    (ordDifferentialWellDefined_ratFunc_of_perfectField K)

theorem exists_divisor_smul_dX_of_perfectField {c : RatFunc K} (hc : c ≠ 0) :
    ∃ D : Divisor K (RatFunc K),
      (∀ v : Place K (RatFunc K), D v = v.ordDifferential (c • dX K)) ∧
        Divisor.degree D = -2 := by
  obtain ⟨Dc, hDc, hDcdeg⟩ :=
    HasPrincipalDivisors.exists_divisor (K := K) (F := RatFunc K) c hc
  refine ⟨Dc + Finsupp.single (p1PlaceInfty K) (-2), fun v => ?_, ?_⟩
  ·
    rw [Finsupp.add_apply, hDc v,
      v.ordDifferential_smul hc (v.differentialCoeff_ne_zero (dX_ne_zero K))]
    rcases eq_or_ne v (p1PlaceInfty K) with rfl | hne
    · rw [ordDifferential_dX_placeInfty_of_perfectField K, Finsupp.single_eq_same]
    · rw [ordDifferential_dX_of_ne_placeInfty_of_perfectField K hne,
        Finsupp.single_eq_of_ne hne]
  ·
    rw [map_add, hDcdeg, zero_add, Divisor.degree_single, deg_placeInfty K, Nat.cast_one,
      mul_one]

end PerfectProfileValues

section PerfectInstance

variable [PerfectField K]

scoped instance instHasCanonicalDivisorRatFuncPerfectField :
    HasCanonicalDivisor (K := K) (F := RatFunc K) where
  exists_divisor ω hω := by
    classical
    obtain ⟨c, hc⟩ := exists_smul_dX_eq K ω
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact hω hc.symm
    obtain ⟨D, hD, -⟩ := exists_divisor_smul_dX_of_perfectField K hc0
    refine ⟨D, fun v => ?_⟩
    rw [← hc]
    exact hD v

end PerfectInstance

section PerfectExactDivisor

variable [PerfectField K] [DecidableEq (RatFunc K)]

end PerfectExactDivisor

section CharZeroRoutes

variable [CharZero K]

end CharZeroRoutes

end Profile

section FiniteFieldReadings

end FiniteFieldReadings

end AlgebraicCurve

section AxiomAudit

end AxiomAudit

end
end

end

section
section

set_option maxHeartbeats 1600000

noncomputable section


namespace ModularCurve

open AlgebraicCurve

namespace MilneAvAg9bRd13T2CoordIndepChar3



end MilneAvAg9bRd13T2CoordIndepChar3
end ModularCurve
end
end
end
section
section
noncomputable section
namespace AlgebraicCurve

open RationalFunctionField
section ChoiceOpacity
variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
namespace Place
section BumpConstruction
variable (v : Place K F)
end BumpConstruction
end Place
end ChoiceOpacity
section CanonicalKResidueTerm
variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
section SupportMachinery
variable [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
variable (K F)
variable {K F}
section Bridge
variable [HasLocalResidue K F] [HasCanonicalLocalResidueKStar K F]
variable [Nontrivial Ω[F⁄K]]
end Bridge
end SupportMachinery
end CanonicalKResidueTerm
section RatFuncPlaceInftyClause
variable {K : Type*} [Field K] [CharZero K] [DecidableEq (RatFunc K)]
theorem residueTheoremK_placeInfty_clause_X_pow
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK) (n : ℕ) :
    kaehlerResidueTermKFam Rfam (KaehlerDifferential.D K (RatFunc K) RatFunc.X)
      (diagonalHom K (RatFunc K) ((RatFunc.X : RatFunc K) ^ n)) (p1PlaceInfty K) = 0 := by
  rw [kaehlerResidueTermKFam_apply]
  exact canonicalLocalResidueDataK_kaehlerResidueTerm_X_pow K (Rfam (p1PlaceInfty K)) n

end RatFuncPlaceInftyClause

section GenericGates

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]

end GenericGates

section AlgClosedGate

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
  [HasCanonicalDivisor (K := K) (F := RatFunc K)]

end AlgClosedGate

end AlgebraicCurve

section AxiomAudit

end AxiomAudit

end

end

end

section
section

noncomputable section


namespace AlgebraicCurve

open RationalFunctionField


variable (K : Type*) [Field K] [PerfectField K] [DecidableEq (RatFunc K)]

section EulerPerfectField

variable {p : K[X]} [Fact (Irreducible p)]

theorem ag9b12c_trace_root_pow_div_derivative_of_lt_of_perfectField (hpmon : p.Monic)
    {k : ℕ} (hk : k < p.natDegree - 1) :
    Algebra.trace K (AdjoinRoot p)
      (AdjoinRoot.root p ^ k / aeval (AdjoinRoot.root p) (derivative p)) = 0 := by
  haveI : FiniteDimensional K (AdjoinRoot p) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hpmon.ne_zero).basis
  have hmin : minpoly K (AdjoinRoot.powerBasis hpmon.ne_zero).gen = p :=
    AdjoinRoot.minpoly_powerBasis_gen_of_monic hpmon
  have h := FLT.EulerDualBasis.trace_pow_div_aeval_derivative_minpoly_of_lt
    (AdjoinRoot.powerBasis hpmon.ne_zero) (k := k)
    (by rwa [AdjoinRoot.powerBasis_dim])
  rwa [hmin, AdjoinRoot.powerBasis_gen] at h

theorem ag9b12c_trace_root_pow_div_derivative_self_of_perfectField (hpmon : p.Monic)
    (hd : 0 < p.natDegree) :
    Algebra.trace K (AdjoinRoot p)
      (AdjoinRoot.root p ^ (p.natDegree - 1) /
        aeval (AdjoinRoot.root p) (derivative p)) = 1 := by
  haveI : FiniteDimensional K (AdjoinRoot p) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hpmon.ne_zero).basis
  have hmin : minpoly K (AdjoinRoot.powerBasis hpmon.ne_zero).gen = p :=
    AdjoinRoot.minpoly_powerBasis_gen_of_monic hpmon
  have h := FLT.EulerDualBasis.trace_pow_div_aeval_derivative_minpoly_self
    (AdjoinRoot.powerBasis hpmon.ne_zero)
    (by rwa [AdjoinRoot.powerBasis_dim])
  rwa [hmin, AdjoinRoot.powerBasis_gen, AdjoinRoot.powerBasis_dim] at h

private theorem ag9b12c_aeval_root_eq_sum_range {c : K[X]} {d : ℕ} (hd : c.natDegree < d) :
    (aeval (AdjoinRoot.root p) c : AdjoinRoot p)
      = ∑ k ∈ Finset.range d, c.coeff k • AdjoinRoot.root p ^ k := by
  rw [aeval_def, eval₂_eq_sum_range' (algebraMap K (AdjoinRoot p)) hd]
  exact Finset.sum_congr rfl fun k _ => (Algebra.smul_def _ _).symm

theorem ag9b12c_trace_adjoinRoot_mk_div_mk_derivative_of_perfectField (hpmon : p.Monic)
    {c : K[X]} (hdeg : c.degree < p.degree) :
    Algebra.trace K (AdjoinRoot p)
        (AdjoinRoot.mk p c / AdjoinRoot.mk p (derivative p))
      = c.coeff (p.natDegree - 1) := by
  haveI : FiniteDimensional K (AdjoinRoot p) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hpmon.ne_zero).basis
  have hpd : 0 < p.natDegree := (Fact.out : Irreducible p).natDegree_pos
  have hcd : c.natDegree < p.natDegree := by
    rcases eq_or_ne c 0 with rfl | hc
    · simpa using hpd
    · exact natDegree_lt_natDegree hc hdeg
  rw [← AdjoinRoot.aeval_eq, ← AdjoinRoot.aeval_eq,
    ag9b12c_aeval_root_eq_sum_range K hcd, Finset.sum_div, map_sum]
  trans ∑ k ∈ Finset.range p.natDegree,
      c.coeff k * Algebra.trace K (AdjoinRoot p)
        (AdjoinRoot.root p ^ k / aeval (AdjoinRoot.root p) (derivative p))
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, mul_div_assoc, ← Algebra.smul_def, map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single (p.natDegree - 1)]
  · rw [ag9b12c_trace_root_pow_div_derivative_self_of_perfectField K hpmon hpd, mul_one]
  · intro k hk hkne
    have hk' : k < p.natDegree - 1 :=
      lt_of_le_of_ne (Nat.le_sub_one_of_lt (Finset.mem_range.mp hk)) hkne
    rw [ag9b12c_trace_root_pow_div_derivative_of_lt_of_perfectField K hpmon hk', mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.sub_lt hpd one_pos)) h

end EulerPerfectField

section DerivativeRegular

private theorem ag9b12c_differentialCoeff_add (v : Place K (RatFunc K))
    (ω₁ ω₂ : Ω[(RatFunc K)⁄K]) :
    v.differentialCoeff (ω₁ + ω₂) = v.differentialCoeff ω₁ + v.differentialCoeff ω₂ :=
  v.differentialCoeff_unique
    (by rw [add_smul, v.differentialCoeff_smul_dCoord, v.differentialCoeff_smul_dCoord])

theorem ag9b12c_differentialCoeff_D_mem_finitePlace {p : K[X]} (hpirr : Irreducible p)
    {f : RatFunc K} (hf : f ∈ (finitePlace K hpirr).toValuationSubring) :
    (finitePlace K hpirr).differentialCoeff (D K (RatFunc K) f)
      ∈ (finitePlace K hpirr).toValuationSubring := by
  set v := finitePlace K hpirr
  set ξ : K[X] := f.num.derivative * f.denom - f.num * f.denom.derivative
  have hd0 : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr f.denom_ne_zero
  have hcoeff : v.differentialCoeff (D K (RatFunc K) f)
      = algebraMap K[X] (RatFunc K) ξ * ((algebraMap K[X] (RatFunc K) f.denom) ^ 2)⁻¹
          * v.differentialCoeff (dX K) := by
    have hkey := denom_sq_smul_D_eq K f
    refine v.differentialCoeff_unique ?_
    rw [mul_smul, v.differentialCoeff_smul_dCoord, mul_comm, mul_smul, ← hkey, smul_smul,
      inv_mul_cancel₀ (pow_ne_zero 2 hd0), one_smul]
  rw [hcoeff]
  refine mul_mem (mul_mem ?_ ?_) ?_
  · exact algebraMap_mem_ofHeightOneSpectrum K _ ξ
  · have hden_notmem : f.denom ∉ (heightOneSpectrumOfIrreducible K hpirr).asIdeal :=
      denom_notMem_of_mem_ofHeightOneSpectrum K _ hf
    have hordd : v.ord (algebraMap K[X] (RatFunc K) f.denom) = 0 := by
      by_contra h
      exact hden_notmem ((Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K)
        (F := RatFunc K) _ f.denom_ne_zero).mp h)
    refine v.mem_of_ord_nonneg (inv_ne_zero (pow_ne_zero 2 hd0)) ?_
    rw [v.ord_inv, ← zpow_natCast, v.ord_zpow, hordd, mul_zero, _root_.neg_zero]
  · exact v.mem_of_ord_nonneg (v.differentialCoeff_ne_zero (dX_ne_zero K))
      (ord_differentialCoeff_dX_ofHeightOneSpectrum hpirr
        (heightOneSpectrumOfIrreducible_asIdeal K hpirr)
        (PerfectField.separable_of_irreducible hpirr)).ge

end DerivativeRegular

section LeibnizCore

theorem ag9b12c_uniformizer_div_mem_finitePlace {p : K[X]} (hpirr : Irreducible p) :
    (finitePlace K hpirr).uniformizer / algebraMap K[X] (RatFunc K) p
      ∈ (finitePlace K hpirr).toValuationSubring := by
  set v := finitePlace K hpirr
  have hp0 : algebraMap K[X] (RatFunc K) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hpirr.ne_zero
  refine v.mem_of_ord_nonneg (div_ne_zero v.uniformizer_ne_zero hp0) ?_
  rw [div_eq_mul_inv, v.ord_mul v.uniformizer_ne_zero (inv_ne_zero hp0), v.ord_inv,
    v.ord_uniformizer, ord_finitePlace_self K hpirr]
  omega

theorem ag9b12c_one_sub_uniformizer_div_mul_differentialCoeff_D
    {p : K[X]} (hpirr : Irreducible p) :
    (1 : RatFunc K) - (finitePlace K hpirr).uniformizer / algebraMap K[X] (RatFunc K) p
        * (finitePlace K hpirr).differentialCoeff
            (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p))
      = algebraMap K[X] (RatFunc K) p
          * (finitePlace K hpirr).differentialCoeff
              (D K (RatFunc K) ((finitePlace K hpirr).uniformizer
                / algebraMap K[X] (RatFunc K) p)) := by
  set v := finitePlace K hpirr
  have hp0 : algebraMap K[X] (RatFunc K) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hpirr.ne_zero
  have hleib : D K (RatFunc K) v.uniformizer
      = (v.uniformizer / algebraMap K[X] (RatFunc K) p)
            • D K (RatFunc K) (algebraMap K[X] (RatFunc K) p)
        + algebraMap K[X] (RatFunc K) p
            • D K (RatFunc K) (v.uniformizer / algebraMap K[X] (RatFunc K) p) := by
    have h := (D K (RatFunc K)).leibniz (a := v.uniformizer / algebraMap K[X] (RatFunc K) p)
      (b := algebraMap K[X] (RatFunc K) p)
    rw [div_mul_cancel₀ _ hp0] at h
    exact h
  have h1 : (1 : RatFunc K)
      = (v.uniformizer / algebraMap K[X] (RatFunc K) p)
            * v.differentialCoeff (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p))
        + algebraMap K[X] (RatFunc K) p
            * v.differentialCoeff
                (D K (RatFunc K) (v.uniformizer / algebraMap K[X] (RatFunc K) p)) := by
    have hcoord : D K (RatFunc K) v.uniformizer = v.dCoord := rfl
    rw [← v.differentialCoeff_dCoord, ← hcoord, hleib, ag9b12c_differentialCoeff_add K,
      v.differentialCoeff_smul, v.differentialCoeff_smul]
  linear_combination h1

theorem ag9b12c_uniformizer_div_mul_differentialCoeff_D_mem_finitePlace
    {p : K[X]} (hpirr : Irreducible p) :
    (finitePlace K hpirr).uniformizer / algebraMap K[X] (RatFunc K) p
        * (finitePlace K hpirr).differentialCoeff
            (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p))
      ∈ (finitePlace K hpirr).toValuationSubring := by
  set v := finitePlace K hpirr
  refine mul_mem (ag9b12c_uniformizer_div_mem_finitePlace K hpirr) ?_
  rw [differentialCoeff_D_algebraMap_polynomial K]
  exact mul_mem (algebraMap_mem_ofHeightOneSpectrum K _ p.derivative)
    (v.mem_of_ord_nonneg (v.differentialCoeff_ne_zero (dX_ne_zero K))
      (ord_differentialCoeff_dX_ofHeightOneSpectrum hpirr
        (heightOneSpectrumOfIrreducible_asIdeal K hpirr)
        (PerfectField.separable_of_irreducible hpirr)).ge)

theorem ag9b12c_residue_uniformizer_div_mul_differentialCoeff_D_eq_one
    {p : K[X]} (hpirr : Irreducible p) :
    IsLocalRing.residue _
        ⟨_, ag9b12c_uniformizer_div_mul_differentialCoeff_D_mem_finitePlace K hpirr⟩
      = (1 : (finitePlace K hpirr).ResidueField) := by
  set v := finitePlace K hpirr
  rw [← sub_eq_zero, show (1 : v.ResidueField) = IsLocalRing.residue _ 1 by simp,
    ← map_sub, IsLocalRing.residue_eq_zero_iff]
  have hsubmem : (1 : RatFunc K) - (v.uniformizer / algebraMap K[X] (RatFunc K) p
      * v.differentialCoeff (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p)))
        ∈ v.toValuationSubring :=
    sub_mem (one_mem _)
      (ag9b12c_uniformizer_div_mul_differentialCoeff_D_mem_finitePlace K hpirr)
  have hcoe : (⟨_, ag9b12c_uniformizer_div_mul_differentialCoeff_D_mem_finitePlace K hpirr⟩
        - 1 : v.toValuationSubring)
      = -⟨_, hsubmem⟩ :=
    Subtype.ext (by push_cast; ring)
  rw [hcoe]
  refine neg_mem ?_
  have herr : (1 : RatFunc K) - (v.uniformizer / algebraMap K[X] (RatFunc K) p
      * v.differentialCoeff (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p)))
        = algebraMap K[X] (RatFunc K) p
          * v.differentialCoeff (D K (RatFunc K)
              (v.uniformizer / algebraMap K[X] (RatFunc K) p)) :=
    ag9b12c_one_sub_uniformizer_div_mul_differentialCoeff_D K hpirr
  have hpmem : (⟨algebraMap K[X] (RatFunc K) p, algebraMap_mem_ofHeightOneSpectrum K _ p⟩
      : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
    rw [Place.mem_maximalIdeal_iff_adicValuation_lt_one]
    refine (Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := K)
      (F := RatFunc K) (heightOneSpectrumOfIrreducible K hpirr)).lt_one_iff_lt_one.mp ?_
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem _ p).mpr
      (Ideal.mem_span_singleton_self p)
  have hregmem : v.differentialCoeff (D K (RatFunc K)
        (v.uniformizer / algebraMap K[X] (RatFunc K) p)) ∈ v.toValuationSubring :=
    ag9b12c_differentialCoeff_D_mem_finitePlace K hpirr
      (ag9b12c_uniformizer_div_mem_finitePlace K hpirr)
  have hprod : (⟨_, hsubmem⟩ : v.toValuationSubring)
      = ⟨_, algebraMap_mem_ofHeightOneSpectrum K _ p⟩ * ⟨_, hregmem⟩ :=
    Subtype.ext herr
  rw [hprod]
  exact Ideal.mul_mem_right _ _ hpmem

end LeibnizCore

section BridgeDischarge

theorem ag9b12c_residue_algebraMap_derivative_ne_zero {p : K[X]} (hpirr : Irreducible p) :
    IsLocalRing.residue _ ⟨algebraMap K[X] (RatFunc K) p.derivative,
        algebraMap_mem_ofHeightOneSpectrum K _ p.derivative⟩
      ≠ (0 : (finitePlace K hpirr).ResidueField) := by
  rw [ne_eq, IsLocalRing.residue_eq_zero_iff,
    Place.mem_maximalIdeal_iff_adicValuation_lt_one]
  intro hlt
  have hlt' := (Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := K)
    (F := RatFunc K) (heightOneSpectrumOfIrreducible K hpirr)).lt_one_iff_lt_one.mpr hlt
  rw [HeightOneSpectrum.valuation_lt_one_iff_mem,
    heightOneSpectrumOfIrreducible_asIdeal K hpirr, Ideal.mem_span_singleton] at hlt'
  exact hpirr.not_isUnit
    ((PerfectField.separable_of_irreducible hpirr).isUnit_of_dvd' dvd_rfl hlt')

theorem ag9b12c_simplePoleResidueAux_finitePlace_p1PrincipalPartAtom_mOne
    {p c : K[X]} (hpirr : Irreducible p)
    (hfmem : p1PrincipalPartAtom K p c 1 * (finitePlace K hpirr).differentialCoeff (dX K)
        ∈ (finitePlace K hpirr).simplePoleSubmodule) :
    (finitePlace K hpirr).simplePoleResidueAux ⟨_, hfmem⟩
      = IsLocalRing.residue _ ⟨algebraMap K[X] (RatFunc K) c,
            algebraMap_mem_ofHeightOneSpectrum K _ c⟩
        / IsLocalRing.residue _ ⟨algebraMap K[X] (RatFunc K) p.derivative,
            algebraMap_mem_ofHeightOneSpectrum K _ p.derivative⟩ := by
  set v := finitePlace K hpirr
  rw [Place.simplePoleResidueAux_apply,
    eq_div_iff (ag9b12c_residue_algebraMap_derivative_ne_zero K hpirr)]
  have hkey : (v.uniformizer * (p1PrincipalPartAtom K p c 1 * v.differentialCoeff (dX K)))
        * algebraMap K[X] (RatFunc K) p.derivative
      = algebraMap K[X] (RatFunc K) c
        * (v.uniformizer / algebraMap K[X] (RatFunc K) p
            * v.differentialCoeff (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p))) := by
    rw [differentialCoeff_D_algebraMap_polynomial K]
    show v.uniformizer
        * (algebraMap K[X] (RatFunc K) c / algebraMap K[X] (RatFunc K) p ^ 1
            * v.differentialCoeff (dX K))
        * algebraMap K[X] (RatFunc K) (derivative p)
      = algebraMap K[X] (RatFunc K) c
        * (v.uniformizer / algebraMap K[X] (RatFunc K) p
            * (algebraMap K[X] (RatFunc K) (derivative p) * v.differentialCoeff (dX K)))
    rw [pow_one, div_mul_eq_mul_div, div_mul_eq_mul_div, mul_div_assoc, mul_div_assoc]
    ring_nf
  have hLHSmem : v.uniformizer * (p1PrincipalPartAtom K p c 1 * v.differentialCoeff (dX K))
      * algebraMap K[X] (RatFunc K) p.derivative ∈ v.toValuationSubring :=
    mul_mem hfmem (algebraMap_mem_ofHeightOneSpectrum K _ p.derivative)
  have hRHSmem : algebraMap K[X] (RatFunc K) c
      * (v.uniformizer / algebraMap K[X] (RatFunc K) p
          * v.differentialCoeff (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p)))
        ∈ v.toValuationSubring :=
    mul_mem (algebraMap_mem_ofHeightOneSpectrum K _ c)
      (ag9b12c_uniformizer_div_mul_differentialCoeff_D_mem_finitePlace K hpirr)
  calc IsLocalRing.residue _ ⟨_, hfmem⟩ * IsLocalRing.residue _ ⟨_,
          algebraMap_mem_ofHeightOneSpectrum K _ p.derivative⟩
      = IsLocalRing.residue _ (⟨_, hfmem⟩ * ⟨_,
          algebraMap_mem_ofHeightOneSpectrum K _ p.derivative⟩) := (map_mul _ _ _).symm
    _ = IsLocalRing.residue _ ⟨_, hLHSmem⟩ :=
        congrArg (IsLocalRing.residue _) (Subtype.ext rfl)
    _ = IsLocalRing.residue _ ⟨_, hRHSmem⟩ :=
        congrArg (IsLocalRing.residue _) (Subtype.ext hkey)
    _ = IsLocalRing.residue _ (⟨_, algebraMap_mem_ofHeightOneSpectrum K _ c⟩
          * ⟨_, ag9b12c_uniformizer_div_mul_differentialCoeff_D_mem_finitePlace K hpirr⟩) :=
        congrArg (IsLocalRing.residue _) (Subtype.ext rfl)
    _ = IsLocalRing.residue _ ⟨_, algebraMap_mem_ofHeightOneSpectrum K _ c⟩
          * IsLocalRing.residue _
              ⟨_, ag9b12c_uniformizer_div_mul_differentialCoeff_D_mem_finitePlace K hpirr⟩ :=
        map_mul _ _ _
    _ = IsLocalRing.residue _ ⟨_, algebraMap_mem_ofHeightOneSpectrum K _ c⟩ := by
        rw [ag9b12c_residue_uniformizer_div_mul_differentialCoeff_D_eq_one K hpirr, mul_one]

theorem ag9b12c_p1FinitePlaceSimplePoleResidueAdjoinRootValue_of_perfectField :
    P1FinitePlaceSimplePoleResidueAdjoinRootValue K := by
  intro p c _ hpirr _
  letI : Fact (Irreducible p) := ⟨hpirr⟩
  intro hfmem
  rw [ag9b12c_simplePoleResidueAux_finitePlace_p1PrincipalPartAtom_mOne K hpirr hfmem,
    AlgEquiv.symm_apply_eq, map_div₀,
    finitePlaceResidueFieldAlgEquivAdjoinRoot_mk K hpirr c,
    finitePlaceResidueFieldAlgEquivAdjoinRoot_mk K hpirr p.derivative]

end BridgeDischarge

section TraceValue

theorem ag9b12c_trace_finitePlace_simplePoleResidue_mOne_of_perfectField
    {p c : K[X]} (hpmon : p.Monic) (hpirr : Irreducible p) (hdeg : c.degree < p.degree)
    (hfmem : p1PrincipalPartAtom K p c 1 * (finitePlace K hpirr).differentialCoeff (dX K)
        ∈ (finitePlace K hpirr).simplePoleSubmodule) :
    Algebra.trace K (finitePlace K hpirr).ResidueField
        ((finitePlace K hpirr).simplePoleResidueAux ⟨_, hfmem⟩)
      = c.coeff (p.natDegree - 1) := by
  haveI : Fact (Irreducible p) := ⟨hpirr⟩
  have hval := ag9b12c_p1FinitePlaceSimplePoleResidueAdjoinRootValue_of_perfectField K
    p c hpmon hpirr hdeg
  rw [trace_finitePlace_residueField_eq_trace_adjoinRoot K hpirr, hval hfmem,
    ag9b12c_trace_adjoinRoot_mk_div_mk_derivative_of_perfectField K hpmon hdeg]

theorem ag9b12c_p1MOneSimplePoleCancel_dX_of_inftyEulerValue_of_perfectField
    (hinf : P1PlaceInftySimplePoleResidueEulerValue K) :
    P1PrincipalPartMOneSimplePoleCancel K (dX_ne_zero K) := by
  intro p c hpmon hpirr hdeg hfmem himem
  rw [ag9b12c_trace_finitePlace_simplePoleResidue_mOne_of_perfectField K
      hpmon hpirr hdeg hfmem,
    hinf p c hpmon hpirr hdeg himem, add_neg_cancel]

end TraceValue

end AlgebraicCurve

end
end

end

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
