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
import FLTForHuman.AlgebraicCurve.Canonical.HasCanonicalDivisor
import FLTForHuman.AlgebraicCurve.PrincipalDivisors.Transcendence
import FLTForHuman.AlgebraicCurve.Defs.PlacesOverDVR
import Mathlib.RingTheory.PowerBasis
import Mathlib.FieldTheory.Minpoly.MinpolyDiv
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.Algebra.Polynomial.PartialFractions

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

theorem gate_canonicalLocalResidueDataK_uniformizer_inv (v : Place K F)
    (R : v.CanonicalLocalResidueDataK) : R.res v.uniformizer⁻¹ = 1 :=
  gate_localResidueData_uniformizer_inv v R.toLocalResidueData

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
