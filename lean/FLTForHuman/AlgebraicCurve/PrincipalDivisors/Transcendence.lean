/-
`HasPrincipalDivisors` via transcendence, after FLT's
`P2M/Sol/S_AlgebraicCurve_hasPrincipalDivisors_of_transcendental.lean` and
`P2M/Sol/S_AlgebraicCurve_hasPrincipalDivisors_adjoin_of_transcendental.lean`
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_hasPrincipalDivisors_of_transcendental.lean>).

The route is the norm formula `ord_v(N_{F'/F} f) = ∑_{w | v} f(w)·ord_w(f)`,
built on the T2 fibre-centre dictionary and `Ideal.relNorm`, then transferred from
the `P¹` base case (T8). Two of the three nodes are public at their wrappers'

* `hasPrincipalDivisors_of_transcendental` — for `K` of characteristic zero and
  `F` finite-dimensional over `K(x)` with `x` transcendental;
* `hasPrincipalDivisors_adjoin_of_transcendental` — the `adjoin`-packaged form.

`hasPrincipalDivisors_of_finiteDimensional_ratFunc` is also public (risk 9's
shared finite-dimensional statement, the pin's out-of-cone duplicate); the pin's
`W2.hasPrincipalDivisors_adjoin` is kept public too, matching the pin's own
`namespace W2` copy. The norm block (ten declarations) is `private`.

The pin's `S_` file repeats T2's whole 350-line fibre dictionary (lines 36–386);
that is imported from `Defs/PlaceDictionary.lean`, never restated (SET-2 §0). The
remaining ≈290 lines are transcribed, with the v4.34 renames
`UniqueFactorizationMonoid.prime_of_normalized_factor`,
`IntermediateField.finiteDimensional_adjoin` and `Set.mem_ofPred_eq`. The T2
dictionary's `inertiaDeg_eq_inertiaDeg_fiberCenter` keeps the pin's *primed*
`Ideal.inertiaDeg'` text, so `relNorm_fiberCenter` bridges through the deprecated
`Ideal.inertiaDeg'_eq_inertiaDeg` (the v4.34 replacement
`Ideal.inertiaDeg_eq_of_isMaximal` has the different shape
`q.inertiaDeg R = finrank (R ⧸ p) (S ⧸ q)` and cannot replace it here); hence the
module-level `linter.deprecated false`, exactly as `PlaceDictionary.lean`.

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_hasPrincipalDivisors_of_transcendental.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_hasPrincipalDivisors_adjoin_of_transcendental.lean
-/
import FLTForHuman.AlgebraicCurve.Defs.PlaceDictionary
import FLTForHuman.AlgebraicCurve.PrincipalDivisors.RatFuncDegree
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.FieldTheory.Perfect
import Mathlib.Algebra.CharP.Algebra
import Mathlib.FieldTheory.RatFunc.AsPolynomial

set_option autoImplicit false

-- The pin's norm block mentions the deprecated primed `Ideal` constants
-- (`Ideal.inertiaDeg'`), both in the T2 dictionary statements it consumes and in
-- the one bridge `Ideal.inertiaDeg'_eq_inertiaDeg` whose new form does not fit.
-- All ten norm-block declarations are `private`, so the checker never sees them
-- (SET-2 §1.5, `TOPIC-t9-transcendence.md` §3).
set_option linter.deprecated false

-- The pin's `haveI`/`letI` walls are kept literal (SET-1 §3).
set_option linter.style.haveILetI false

noncomputable section

open IsDedekindDomain WithZero IsLocalRing UniqueFactorizationMonoid

namespace AlgebraicCurve

open Place Divisor

/-! ## Support transfer: the `minpoly` coefficient argument -/

section SupportTransfer

open Polynomial

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

/-! ## `ord` of a generator of a power of the maximal ideal -/

section DVR

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem ord_coe_eq_of_span_singleton_eq_pow_maximalIdeal {r : v.toValuationSubring} {n : ℕ}
    (h : Ideal.span {r} = IsLocalRing.maximalIdeal v.toValuationSubring ^ n) :
    v.ord (r : F) = n := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton] at h
  obtain ⟨u, hu⟩ := h

  have hr : r = ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) * π ^ n := by
    rw [mul_comm, Units.eq_mul_inv_iff_mul_eq]
    exact hu
  have hcoe : (r : F) = (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F)
      * (π : F) ^ (n : ℤ) := by
    rw [hr]
    push_cast
    rw [zpow_natCast]
  rw [hcoe, v.ord_unit_smul_zpow u⁻¹ hπ (n : ℤ)]

end DVR

/-! ## The ideal-norm and element-norm block -/

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [CharZero F]

namespace Place

private instance (v : Place K F) : CharZero v.toValuationSubring :=
  ⟨fun a b hab => Nat.cast_injective (R := F)
    (by simpa using congrArg (Subtype.val : v.toValuationSubring → F) hab)⟩

section IdealNorm

variable {v : Place K F} {w : Place K F'}

private theorem relNorm_fiberCenter (hw : w.restrict F = v) :
    Ideal.relNorm v.toValuationSubring (fiberCenter F' v hw).asIdeal
      = IsLocalRing.maximalIdeal v.toValuationSubring ^ w.inertiaDeg F := by
  haveI : (fiberCenter F' v hw).asIdeal.IsMaximal :=
    (fiberCenter F' v hw).isPrime.isMaximal (fiberCenter F' v hw).ne_bot
  haveI : (fiberCenter F' v hw).asIdeal.LiesOver
      (IsLocalRing.maximalIdeal v.toValuationSubring) := fiberCenter_liesOver hw
  rw [Ideal.relNorm_eq_pow_of_isMaximal (fiberCenter F' v hw).asIdeal
    (IsLocalRing.maximalIdeal v.toValuationSubring), inertiaDeg_eq_inertiaDeg_fiberCenter hw,
    Ideal.inertiaDeg'_eq_inertiaDeg]

omit [CharZero F] in

private theorem count_normalizedFactors_span_singleton
    (hw : w.restrict F = v) {c : integralClosureAt F' v} (hc : c ≠ 0) :
    (normalizedFactors (Ideal.span {c})).count (fiberCenter F' v hw).asIdeal
      = (w.ord (algebraMap (integralClosureAt F' v) F' c)).toNat := by
  haveI : (fiberCenter F' v hw).asIdeal.IsPrime := (fiberCenter F' v hw).isPrime

  have hord0 : 0 ≤ w.ord (algebraMap (integralClosureAt F' v) F' c) :=
    w.ord_nonneg_of_mem (forall_mem_of_restrict_eq hw c)
  refine Ideal.count_normalizedFactors_eq (p := (fiberCenter F' v hw).asIdeal)
    (x := Ideal.span {c})
    (n := (w.ord (algebraMap (integralClosureAt F' v) F' c)).toNat) ?_ ?_
  · rw [Ideal.span_singleton_le_iff_mem, ← le_ord_iff_mem_pow_fiberCenter hw hc]
    omega
  · rw [Ideal.span_singleton_le_iff_mem, ← le_ord_iff_mem_pow_fiberCenter hw hc]
    push_cast
    omega

private theorem relNorm_span_singleton {c : integralClosureAt F' v}
    (hc : c ≠ 0) :
    Ideal.relNorm v.toValuationSubring (Ideal.span {c})
      = IsLocalRing.maximalIdeal v.toValuationSubring
          ^ (∑ w ∈ v.fiberOver F',
              w.inertiaDeg F * (w.ord (algebraMap (integralClosureAt F' v) F' c)).toNat) := by
  have hspan : (Ideal.span {c} : Ideal (integralClosureAt F' v)) ≠ ⊥ := by simpa using hc
  set S : Multiset (Ideal (integralClosureAt F' v)) := normalizedFactors (Ideal.span {c})
    with hS

  have hfactor : ∀ Q ∈ S.toFinset, ∃ w' : Place K F', ∃ hw' : w'.restrict F = v,
      (fiberCenter F' v hw').asIdeal = Q := by
    intro Q hQ
    rw [Multiset.mem_toFinset] at hQ
    have hQprime : Prime Q := UniqueFactorizationMonoid.prime_of_normalized_factor Q hQ
    have hQbot : Q ≠ ⊥ := hQprime.ne_zero
    haveI : Q.IsPrime := Ideal.isPrime_of_prime hQprime
    exact ⟨placeOfPrime ⟨Q, inferInstance, hQbot⟩, restrict_placeOfPrime _,
      congrArg HeightOneSpectrum.asIdeal (fiberCenter_placeOfPrime
        (⟨Q, inferInstance, hQbot⟩ : HeightOneSpectrum (integralClosureAt F' v)))⟩

  set T : Finset (Ideal (integralClosureAt F' v)) := (v.fiberOver F').attach.image
    (fun w' => (fiberCenter F' v ((mem_fiberOver v).mp w'.2)).asIdeal) with hT
  have hsub : S.toFinset ⊆ T := by
    intro Q hQ
    obtain ⟨w', hw', rfl⟩ := hfactor Q hQ
    exact Finset.mem_image.mpr ⟨⟨w', (mem_fiberOver v).mpr hw'⟩, Finset.mem_attach _ _, rfl⟩
  have hinj : Set.InjOn (fun w' : {x // x ∈ v.fiberOver F'} =>
      (fiberCenter F' v ((mem_fiberOver v).mp w'.2)).asIdeal) (v.fiberOver F').attach := by
    intro w₁ _ w₂ _ h
    exact Subtype.ext (eq_of_fiberCenter_eq ((mem_fiberOver v).mp w₁.2) ((mem_fiberOver v).mp w₂.2)
      (HeightOneSpectrum.ext h))

  calc
    Ideal.relNorm v.toValuationSubring (Ideal.span {c})
        = Ideal.relNorm v.toValuationSubring (∏ Q ∈ S.toFinset, Q ^ S.count Q) := by
          rw [← Finset.prod_multiset_count, hS, Ideal.prod_normalizedFactors_eq_self hspan]
    _ = ∏ Q ∈ S.toFinset, Ideal.relNorm v.toValuationSubring Q ^ S.count Q := by
          rw [map_prod]
          exact Finset.prod_congr rfl fun Q _ => map_pow _ Q _
    _ = ∏ Q ∈ S.toFinset, IsLocalRing.maximalIdeal v.toValuationSubring
          ^ ((IsLocalRing.maximalIdeal v.toValuationSubring).inertiaDeg' Q * S.count Q) := by
          refine Finset.prod_congr rfl fun Q hQ => ?_
          obtain ⟨w', hw', rfl⟩ := hfactor Q hQ
          rw [relNorm_fiberCenter hw', ← pow_mul, inertiaDeg_eq_inertiaDeg_fiberCenter hw']
    _ = IsLocalRing.maximalIdeal v.toValuationSubring
          ^ (∑ Q ∈ S.toFinset,
              (IsLocalRing.maximalIdeal v.toValuationSubring).inertiaDeg' Q * S.count Q) :=
          Finset.prod_pow_eq_pow_sum S.toFinset
            (fun Q => (IsLocalRing.maximalIdeal v.toValuationSubring).inertiaDeg' Q * S.count Q)
            (IsLocalRing.maximalIdeal v.toValuationSubring)
    _ = IsLocalRing.maximalIdeal v.toValuationSubring
          ^ (∑ w ∈ v.fiberOver F',
              w.inertiaDeg F * (w.ord (algebraMap (integralClosureAt F' v) F' c)).toNat) := by
          congr 1

          calc
            ∑ Q ∈ S.toFinset,
                (IsLocalRing.maximalIdeal v.toValuationSubring).inertiaDeg' Q * S.count Q
                = ∑ Q ∈ T,
                    (IsLocalRing.maximalIdeal v.toValuationSubring).inertiaDeg' Q
                      * S.count Q := by
                  refine Finset.sum_subset hsub fun Q _ hQ => ?_
                  rw [Multiset.count_eq_zero_of_notMem
                    (fun h => hQ (Multiset.mem_toFinset.mpr h)), mul_zero]
            _ = ∑ w' ∈ (v.fiberOver F').attach,
                  (IsLocalRing.maximalIdeal v.toValuationSubring).inertiaDeg'
                      (fiberCenter F' v ((mem_fiberOver v).mp w'.2)).asIdeal
                    * S.count (fiberCenter F' v ((mem_fiberOver v).mp w'.2)).asIdeal := by
                  rw [hT, Finset.sum_image hinj]
            _ = ∑ w' ∈ (v.fiberOver F').attach, (w'.1.inertiaDeg F
                  * (w'.1.ord (algebraMap (integralClosureAt F' v) F' c)).toNat) := by
                  refine Finset.sum_congr rfl fun w' _ => ?_
                  rw [← inertiaDeg_eq_inertiaDeg_fiberCenter ((mem_fiberOver v).mp w'.2),
                    count_normalizedFactors_span_singleton ((mem_fiberOver v).mp w'.2) hc]
            _ = ∑ w ∈ v.fiberOver F',
                  w.inertiaDeg F
                    * (w.ord (algebraMap (integralClosureAt F' v) F' c)).toNat :=
                  Finset.sum_attach (v.fiberOver F') fun w =>
                    w.inertiaDeg F * (w.ord (algebraMap (integralClosureAt F' v) F' c)).toNat

end IdealNorm

section ElementNorm

variable (v : Place K F)

private theorem ord_norm_algebraMap_integralClosureAt
    {c : integralClosureAt F' v} (hc : c ≠ 0) :
    v.ord (Algebra.norm F (algebraMap (integralClosureAt F' v) F' c))
      = ∑ w ∈ v.fiberOver F', (w.inertiaDeg F : ℤ)
          * w.ord (algebraMap (integralClosureAt F' v) F' c) := by

  rw [← Algebra.algebraMap_intNorm (A := v.toValuationSubring) (K := F) (L := F')
    (B := integralClosureAt F' v)]

  have hrel := relNorm_span_singleton (v := v) hc
  rw [Ideal.relNorm_singleton] at hrel

  rw [ValuationSubring.algebraMap_apply, ord_coe_eq_of_span_singleton_eq_pow_maximalIdeal v hrel]

  push_cast
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [Int.toNat_of_nonneg
    (w.ord_nonneg_of_mem (forall_mem_of_restrict_eq ((mem_fiberOver v).mp hw) c))]

private theorem ord_norm_eq_sum_fiberOver {f : F'} (hf : f ≠ 0) :
    v.ord (Algebra.norm F f) = ∑ w ∈ v.fiberOver F', (w.inertiaDeg F : ℤ) * w.ord f := by

  obtain ⟨⟨c, s⟩, hcs⟩ := IsLocalization.surj
    (nonZeroDivisors (integralClosureAt F' v)) f
  have hs0 : (s : integralClosureAt F' v) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have hsF : algebraMap (integralClosureAt F' v) F' (s : integralClosureAt F' v) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (integralClosureAt F' v) F')).mpr hs0
  have hcF : algebraMap (integralClosureAt F' v) F' c ≠ 0 := by
    rw [← hcs]
    exact mul_ne_zero hf hsF
  have hc0 : c ≠ 0 := fun h => hcF (by rw [h, map_zero])

  have hintc := ord_norm_algebraMap_integralClosureAt v hc0
  have hints := ord_norm_algebraMap_integralClosureAt v hs0

  rw [← hcs, map_mul, v.ord_mul (Algebra.norm_ne_zero_iff.mpr hf)
    (Algebra.norm_ne_zero_iff.mpr hsF), hints] at hintc
  have hsplit : ∑ w ∈ v.fiberOver F', (w.inertiaDeg F : ℤ)
      * w.ord (f * algebraMap (integralClosureAt F' v) F' (s : integralClosureAt F' v))
        = (∑ w ∈ v.fiberOver F', (w.inertiaDeg F : ℤ) * w.ord f)
          + ∑ w ∈ v.fiberOver F', (w.inertiaDeg F : ℤ)
              * w.ord (algebraMap (integralClosureAt F' v) F' (s : integralClosureAt F' v)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [w.ord_mul hf hsF]
    ring
  rw [hsplit] at hintc
  omega

end ElementNorm

end Place

namespace Divisor

private theorem pushforwardNormFormula_of_finiteDimensional :
    Divisor.PushforwardNormFormula K F F' := by
  intro f hf D hD v
  classical
  rw [Divisor.pushforward_apply, Place.ord_norm_eq_sum_fiberOver v hf]
  calc
    ∑ w ∈ D.support, (if w.restrict F = v then D w * (w.inertiaDeg F : ℤ) else 0)
        = ∑ w ∈ D.support ∪ v.fiberOver F',
            (if w.restrict F = v then D w * (w.inertiaDeg F : ℤ) else 0) := by
          refine Finset.sum_subset Finset.subset_union_left fun w _ hw => ?_
          rw [Finsupp.notMem_support_iff.mp hw, zero_mul, ite_self]
    _ = ∑ w ∈ v.fiberOver F', (if w.restrict F = v then D w * (w.inertiaDeg F : ℤ) else 0) := by
          refine (Finset.sum_subset Finset.subset_union_right fun w _ hw => ?_).symm
          rw [if_neg fun h => hw ((Place.mem_fiberOver v).mpr h)]
    _ = ∑ w ∈ v.fiberOver F', (w.inertiaDeg F : ℤ) * w.ord f := by
          refine Finset.sum_congr rfl fun w hw => ?_
          rw [if_pos ((Place.mem_fiberOver v).mp hw), hD w, mul_comm]

end Divisor

/-! ## The finiteness of the `ord`-support over `K(t)` -/

section T029

variable {K : Type*} [Field K] {F' : Type*} [Field F'] [Algebra K F']
  [Algebra (RatFunc K) F'] [IsScalarTower K (RatFunc K) F']
  [FiniteDimensional (RatFunc K) F'] [Algebra.IsSeparable (RatFunc K) F']

private theorem finite_setOf_ord_ne_zero_of_finiteDimensional {f : F'} (hf : f ≠ 0) :
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
    obtain ⟨i, hi, hci, hord⟩ := exists_coeff_ord_ne_zero (w := w) (F := RatFunc K) hf hw
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    refine ⟨i, hi, w.restrict (RatFunc K), ?_, rfl⟩
    intro h0
    apply hord
    rw [w.ord_restrict, h0, mul_zero]

end T029

/-! ## The public nodes -/

theorem hasPrincipalDivisors_of_finiteDimensional_ratFunc (K : Type*) [Field K] [CharZero K]
    (F' : Type*) [Field F'] [Algebra K F'] [Algebra (RatFunc K) F']
    [IsScalarTower K (RatFunc K) F'] [FiniteDimensional (RatFunc K) F'] :
    HasPrincipalDivisors K F' := by
  haveI : CharZero (RatFunc K) :=
    charZero_of_injective_algebraMap (algebraMap K (RatFunc K)).injective
  constructor
  intro f hf
  classical
  have hfin : {w : Place K F' | w.ord f ≠ 0}.Finite :=
    finite_setOf_ord_ne_zero_of_finiteDimensional hf
  refine ⟨Finsupp.onFinset hfin.toFinset (fun w => w.ord f)
      (fun w hw => hfin.mem_toFinset.mpr hw), fun v => rfl, ?_⟩
  set D : Divisor K F' := Finsupp.onFinset hfin.toFinset (fun w => w.ord f)
      (fun w hw => hfin.mem_toFinset.mpr hw) with hDdef
  have hD : ∀ w : Place K F', D w = w.ord f := fun w => rfl
  have h0 : Divisor.degree (Divisor.pushforward (RatFunc K) D) = 0 :=
    RationalFunctionField.degree_eq_zero_of_forall_eq_ord _
      (fun v => Divisor.pushforwardNormFormula_of_finiteDimensional f hf D hD v)
  rw [← Divisor.degree_pushforward (F := RatFunc K) D]
  exact h0

theorem hasPrincipalDivisors_of_transcendental (K : Type*) [Field K] [CharZero K] {F : Type*}
    [Field F] [Algebra K F] (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] : HasPrincipalDivisors K F := by
  classical
  let e : RatFunc K ≃ₐ[K] ↥(IntermediateField.adjoin K ({x} : Set F)) :=
    RatFunc.algEquivOfTranscendental x hx
  letI : Algebra (RatFunc K) (↥(IntermediateField.adjoin K ({x} : Set F))) :=
    e.toAlgHom.toRingHom.toAlgebra
  letI : Algebra (RatFunc K) F :=
    ((algebraMap (↥(IntermediateField.adjoin K ({x} : Set F))) F).comp e.toAlgHom.toRingHom).toAlgebra
  haveI : IsScalarTower (RatFunc K) (↥(IntermediateField.adjoin K ({x} : Set F))) F :=
    IsScalarTower.of_algebraMap_eq fun q => rfl
  haveI : IsScalarTower K (RatFunc K) F := IsScalarTower.of_algebraMap_eq fun r => by
    show algebraMap K F r = algebraMap (↥(IntermediateField.adjoin K ({x} : Set F))) F (e (algebraMap K (RatFunc K) r))
    rw [AlgEquiv.commutes]
    exact IsScalarTower.algebraMap_apply K (↥(IntermediateField.adjoin K ({x} : Set F))) F r
  haveI : Module.Finite (RatFunc K) (↥(IntermediateField.adjoin K ({x} : Set F))) :=
    Module.Finite.of_surjective (Algebra.linearMap (RatFunc K) (↥(IntermediateField.adjoin K ({x} : Set F)))) e.surjective
  haveI : FiniteDimensional (RatFunc K) F := Module.Finite.trans (↥(IntermediateField.adjoin K ({x} : Set F))) F
  exact hasPrincipalDivisors_of_finiteDimensional_ratFunc K F

/-! ## The `adjoin` form -/

namespace W2

open IntermediateField

variable (K : Type*) [Field K] [CharZero K] {LF : Type*} [Field LF] [Algebra K LF]

theorem hasPrincipalDivisors_adjoin (x : LF) (hx : Transcendental K x) (T : Finset LF)
    (hT : ∀ t ∈ T, IsIntegral (IntermediateField.adjoin K ({x} : Set LF)) t) :
    HasPrincipalDivisors K (IntermediateField.adjoin K (insert x (T : Set LF))) := by
  set F : IntermediateField K LF := IntermediateField.adjoin K (insert x (T : Set LF)) with hF
  have hxF : x ∈ F := subset_adjoin K _ (Set.mem_insert x _)
  have hTF : ∀ t ∈ T, t ∈ F := fun t ht => subset_adjoin K _ (Set.mem_insert_of_mem x ht)
  set x' : F := ⟨x, hxF⟩ with hx'

  have hx't : Transcendental K x' :=
    (transcendental_algebraMap_iff (R := K) (S := F) (A := LF) Subtype.val_injective).mp hx

  set A : IntermediateField K F := IntermediateField.adjoin K ({x'} : Set F) with hA
  have hliftA : lift A = IntermediateField.adjoin K ({x} : Set LF) := by
    rw [hA, lift_adjoin_simple]

  let e : A ≃ₐ[K] IntermediateField.adjoin K ({x} : Set LF) :=
    (liftAlgEquiv A).trans (equivOfEq hliftA)
  have he : ∀ a : A, ((e a : IntermediateField.adjoin K ({x} : Set LF)) : LF) = ((a : F) : LF) := by
    intro a; rfl

  have hint : ∀ t (ht : t ∈ T), IsIntegral A (⟨t, hTF t ht⟩ : F) := by
    intro t ht

    have h1 : IsIntegral A (t : LF) := by
      refine (hT t ht).map_of_comp_eq (R := IntermediateField.adjoin K ({x} : Set LF)) (S := LF)
        (T := A) (U := LF)
        (e.symm : IntermediateField.adjoin K ({x} : Set LF) →+* A) (RingHom.id LF) ?_
      ext b
      change (((e.symm b : A) : F) : LF) = ((b : IntermediateField.adjoin K ({x} : Set LF)) : LF)
      rw [← he (e.symm b), AlgEquiv.apply_symm_apply]
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom A F LF) Subtype.val_injective).mp h1

  haveI : FiniteDimensional A F := by
    set T' : Set F := (fun t : T => (⟨(t : LF), hTF t t.2⟩ : F)) '' Set.univ with hT'
    haveI : Finite T' := Set.Finite.to_subtype ((Set.finite_univ).image _)
    have hT'int : ∀ y ∈ T', IsIntegral A y := by
      rintro _ ⟨t, -, rfl⟩; exact hint t t.2
    haveI : FiniteDimensional A (IntermediateField.adjoin A T') :=
      IntermediateField.finiteDimensional_adjoin hT'int

    have htop : IntermediateField.adjoin A T' = ⊤ := by
      apply restrictScalars_injective K
      rw [restrictScalars_adjoin, restrictScalars_top]
      apply lift_injective
      rw [lift_top, lift_adjoin]
      apply le_antisymm (adjoin_le_iff.mpr ?_) ?_
      · rintro _ ⟨y, hy, rfl⟩; exact y.2
      · show IntermediateField.adjoin K (insert x (T : Set LF)) ≤ _
        apply adjoin.mono
        intro z hz
        rcases hz with rfl | hz
        · exact ⟨x', Or.inl (subset_adjoin K _ (Set.mem_singleton _)), rfl⟩
        · exact ⟨⟨z, hTF z hz⟩, Or.inr ⟨⟨z, hz⟩, Set.mem_univ _, rfl⟩, rfl⟩
    rw [htop] at this
    exact LinearEquiv.finiteDimensional (IntermediateField.topEquiv (F := A) (E := F)).toLinearEquiv
  exact hasPrincipalDivisors_of_transcendental K x' hx't

end W2

theorem hasPrincipalDivisors_adjoin_of_transcendental (K : Type*) [Field K] [CharZero K]
    {LF : Type*} [Field LF] [Algebra K LF] (x : LF) (hx : Transcendental K x) (T : Finset LF)
    (hT : ∀ t ∈ T, IsIntegral (IntermediateField.adjoin K ({x} : Set LF)) t) :
    HasPrincipalDivisors K (IntermediateField.adjoin K (insert x (T : Set LF))) :=
  W2.hasPrincipalDivisors_adjoin K x hx T hT

end AlgebraicCurve
