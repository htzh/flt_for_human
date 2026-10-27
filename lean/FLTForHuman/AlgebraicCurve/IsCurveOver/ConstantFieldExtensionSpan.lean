/-
The constant-field-extension spanning node, after FLT's
`P2M/Sol/S_AlgebraicCurve_mem_span_range_algebraMap_of_constantFieldExtension.lean`
(859 ln)
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_mem_span_range_algebraMap_of_constantFieldExtension.lean>)
and its wrapper
`Theorems/Thm_AlgebraicCurve_mem_span_range_algebraMap_of_constantFieldExtension.lean`.

The mathematics: with `K` and `K'` algebraically closed, `K ⊆ F ⊆ F'`,
`K ⊆ K' ⊆ F'`, `F'` generated over `K'` by the image of `F`, and both fields
curves, an element `z ∈ F'` whose every place over a place of `F` has
non-negative order already lies in the `K'`-span of the image of `F`.

The proof is the pin's: choose a transcendence basis `x` from the `hfg` witness,
identify `F'/K'⟮x⟯` with the constant extension of `F/K⟮x⟯`, transport a `K⟮x⟯`-basis
along `algebraMap F F'` (`exists_basis`), and read a `z` as the trace sum against
the dual basis (`eq_sum_trace_mul`); regularity of `z` at the places of `K'⟮x⟯`
(`mem_span_of_regular`) makes every trace coefficient constant (`trace_mem`), so
the sum is a `K'`-combination of the images of `F`.

**Home.**  The node cannot be appended to
`IsCurveOver/ConstantFieldExtension.lean`: that module is *below*
`Place/ConstantFieldExtension.lean` (the P2 module imports it for
`linearIndependent_of_constantFieldExtension`), while this node needs the P2
module's `Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed` and
`Place.mem_maximalIdeal_of_ord_pos`/`Place.exists_sub_algebraMap_mem_maximalIdeal`.
It is therefore homed in this sibling module, above the P2 module, per
PLAN-W5 §3's fallback; the legacy module is untouched.

The pin's 60-line private prelude of `ord`/maximal-ideal rewrites is not repeated
here: it is imported (workorder §3/§2b) as `Place.ord_nonneg_of_mem_vs`,
`Place.mem_vs_of_ord_nonneg`, `ConstantFieldPlaceLift.ord_eq_zero_of_mem_of_inv_mem`,
`Place.ord_algebraMap_base`, `Place.LocalDerivation.isUnit_add_of_mem_maximalIdeal`,
`Place.mem_maximalIdeal_of_ord_pos` and `Place.exists_sub_algebraMap_mem_maximalIdeal`;
only the `w`-local aliases the pin's later proofs call by name are kept.  The
pin's `transcendental_algebraMap` is likewise the port's stronger
`ConstantFieldExtension.transcendental_algebraMap`
(`IsCurveOver/ConstantFieldExtension.lean`), wrapped in the pin's binder shape.

Mathlib search negatives (recorded): there is no `MvPolynomial`-free route to the
basis transport and none to the trace decomposition; the pin's own
`span_range_eq_adjoin` is needed because `Algebra.adjoin_eq_span` is stated for
the closure of a set, not for a range.

spec-pin: Theorems/Thm_AlgebraicCurve_mem_span_range_algebraMap_of_constantFieldExtension.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_mem_span_range_algebraMap_of_constantFieldExtension.lean   -- comparable copy
# `degree_eq_sum` (public here for P5, which needs it in its own descent proof) is also declared in
# the pin's P5 `isPrincipal` file; that is its second pin source.
spec-pin: P2M/Sol/S_AlgebraicCurve_Divisor_isPrincipal_of_constantFieldExtension.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_finrankAlong_eq_and_trace_eq_of_constantFieldExtension.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_finrankAlong_eq_and_trace_eq_of_constantFieldExtension.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_finrank_le_and_natCard_places_le_of_constantFieldExtension_adjoin.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_finrank_le_and_natCard_places_le_of_constantFieldExtension_adjoin.lean   -- comparable copy
-/
import FLTForHuman.AlgebraicCurve.IsCurveOver.ConstantFieldExtension
import FLTForHuman.AlgebraicCurve.Place.ConstantFieldExtension
import FLTForHuman.AlgebraicCurve.Place.FromValuationSubring
import FLTForHuman.AlgebraicCurve.Differential.CorrespondenceRegular
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Basis.VectorSpace

set_option autoImplicit false

noncomputable section

open Polynomial

namespace AlgebraicCurve

namespace W7XH

/-! ## The `ord` prelude, as `w`-local aliases

The pin repeats this block in five files; the port writes it once
(`Place/ConstantFieldExtension.lean`, `Defs/PushPull.lean`,
`Canonical/WeilDifferential.lean`, `P1/EnginePrelude.lean`). -/

section Basic

variable {k L : Type*} [Field k] [Field L] [Algebra k L] (w : Place k L)

private theorem ord_nonneg_of_mem {f : L} (hf : f ∈ w.toValuationSubring) : 0 ≤ w.ord f :=
  w.ord_nonneg_of_mem_vs hf

private theorem mem_of_ord_nonneg {f : L} (hf : 0 ≤ w.ord f) : f ∈ w.toValuationSubring :=
  w.mem_vs_of_ord_nonneg hf

private theorem not_mem_of_ord_neg {f : L} (hf : w.ord f < 0) : f ∉ w.toValuationSubring := fun h => by
  have := ord_nonneg_of_mem w h
  omega

private theorem ord_eq_zero_of_mem_of_inv_mem {f : L} (hf : f ∈ w.toValuationSubring)
    (hfi : f⁻¹ ∈ w.toValuationSubring) : w.ord f = 0 :=
  ConstantFieldPlaceLift.ord_eq_zero_of_mem_of_inv_mem w hf hfi

private theorem ord_algebraMap (a : k) : w.ord (algebraMap k L a) = 0 :=
  Place.ord_algebraMap_base (v := w) a

private theorem irreducible_coe_ne_zero {π : w.toValuationSubring} (hπ : Irreducible π) : (π : L) ≠ 0 := by
  intro h
  exact hπ.ne_zero (by exact_mod_cast h)

private theorem ord_coe_isUnit {X : w.toValuationSubring} (h : IsUnit X) : w.ord (X : L) = 0 := by
  obtain ⟨u, rfl⟩ := h
  exact w.ord_coe_unit u

private theorem isUnit_add_of_mem_maximalIdeal {X Y : w.toValuationSubring} (hX : IsUnit X)
    (hY : Y ∈ IsLocalRing.maximalIdeal w.toValuationSubring) : IsUnit (X + Y) :=
  Place.LocalDerivation.isUnit_add_of_mem_maximalIdeal hX hY

private theorem ord_algebraMap_add_eq_zero {a : k} (ha : a ≠ 0) {f : L} (hf : 0 < w.ord f) :
    w.ord (algebraMap k L a + f) = 0 := by
  have hfmem : f ∈ w.toValuationSubring := mem_of_ord_nonneg w hf.le
  have hX : IsUnit (algebraMap k w.toValuationSubring a) := (IsUnit.mk0 a ha).map _
  have hY : (⟨f, hfmem⟩ : w.toValuationSubring) ∈ IsLocalRing.maximalIdeal w.toValuationSubring :=
    Place.mem_maximalIdeal_of_ord_pos (w := w) (by simpa using hf)
  have h := ord_coe_isUnit w (isUnit_add_of_mem_maximalIdeal w hX hY)
  simpa using h

private theorem ord_mul_of_ord_eq_zero {f g : L} (hf : w.ord f = 0) (hf0 : f ≠ 0) :
    w.ord (f * g) = w.ord g := by
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  rw [w.ord_mul hf0 hg, hf, zero_add]

private theorem exists_ord_sub_algebraMap_pos [IsAlgClosed k] [IsCurveOver k L] {f : L}
    (hf : f ∈ w.toValuationSubring) :
    ∃ a : k, f = algebraMap k L a ∨ 0 < w.ord (f - algebraMap k L a) := by
  obtain ⟨a, ha⟩ := Place.exists_sub_algebraMap_mem_maximalIdeal (w := w) ⟨f, hf⟩
  refine ⟨a, ?_⟩
  by_cases h : f = algebraMap k L a
  · exact Or.inl h
  right
  have hne : (⟨f, hf⟩ - algebraMap k w.toValuationSubring a : w.toValuationSubring) ≠ 0 := by
    intro h0
    apply h
    have := congrArg Subtype.val h0
    simpa [sub_eq_zero] using this
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha
  have hord : w.ord ((⟨f, hf⟩ - algebraMap k w.toValuationSubring a : w.toValuationSubring) : L)
      ≠ 0 := by
    intro h0
    apply ha
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
    have hX0 : ((⟨f, hf⟩ - algebraMap k w.toValuationSubring a : w.toValuationSubring) : L) ≠ 0 :=
      fun h' => hne (by exact_mod_cast h')
    obtain ⟨u, hu⟩ := w.exists_unit_mul_zpow hX0 hπ
    rw [h0, zpow_zero, mul_one] at hu
    rw [Subtype.ext hu]
    exact Units.isUnit u
  have hnn := ord_nonneg_of_mem w
    ((⟨f, hf⟩ - algebraMap k w.toValuationSubring a : w.toValuationSubring)).2
  have : ((⟨f, hf⟩ - algebraMap k w.toValuationSubring a : w.toValuationSubring) : L)
      = f - algebraMap k L a := by simp
  rw [this] at hord hnn
  omega

theorem aeval_mem {t : L} (ht : t ∈ w.toValuationSubring) (p : k[X]) :
    aeval t p ∈ w.toValuationSubring := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | monomial n a =>
    rw [aeval_monomial]
    exact mul_mem (w.algebraMap_mem' a) (pow_mem ht n)

end Basic

section Algebra

theorem linearIndependent_pow_of_transcendental {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    {x : A} (hx : Transcendental R x) : LinearIndependent R fun n : ℕ => x ^ n := by
  rw [linearIndependent_iff]
  intro l hl
  have hinj := transcendental_iff_injective.mp hx
  have h0 : aeval x (Polynomial.ofFinsupp (.ofCoeff l)) = 0 := by
    rw [Finsupp.linearCombination_apply] at hl
    rw [aeval_def, eval₂_eq_sum, Polynomial.sum, Polynomial.support_ofFinsupp, AddMonoidAlgebra.coeff_ofCoeff]
    rw [Finsupp.sum] at hl
    convert hl using 2 with n hn
    rw [Polynomial.coeff_ofFinsupp, Algebra.smul_def]
  have h1 : (Polynomial.ofFinsupp (.ofCoeff l) : R[X]) = 0 := hinj (by rw [h0, map_zero])
  exact AddMonoidAlgebra.ofCoeff_eq_zero.mp (Polynomial.ofFinsupp_eq_zero.mp h1)

private theorem isIntegral_of_forall_mem_valuationSubring {R L : Type*} [CommRing R] [Field L]
    [Algebra R L] (w : L)
    (h : ∀ B : ValuationSubring L, (∀ r : R, algebraMap R L r ∈ B) → w ∈ B) :
    IsIntegral R w := by
  classical
  by_contra hni
  have hw0 : w ≠ 0 := by rintro rfl; exact hni isIntegral_zero

  set S : Subalgebra R L := Algebra.adjoin R {w⁻¹} with hS
  have hwS : w⁻¹ ∈ S := Algebra.subset_adjoin (Set.mem_singleton _)
  set A : Subring L := S.toSubring with hA
  set I : Ideal A := Ideal.span {(⟨w⁻¹, hwS⟩ : A)} with hI
  have hI : I ≠ ⊤ := by
    intro htop
    have h1 : (1 : A) ∈ I := htop ▸ Submodule.mem_top
    rw [hI, Ideal.mem_span_singleton'] at h1
    obtain ⟨a, ha⟩ := h1

    have haS : (a : L) ∈ S := a.2
    rw [hS, Algebra.adjoin_singleton_eq_range_aeval] at haS
    obtain ⟨f, hf⟩ := haS
    have haw : (a : L) * w⁻¹ = 1 := by
      have := congrArg Subtype.val ha
      simpa using this

    set n := f.natDegree with hn
    apply hni

    set g : R[X] := ∑ i ∈ Finset.range (n + 1), C (f.coeff i) * X ^ (n - i) with hg
    have hgdeg : g.degree < (n + 1 : ℕ) := by
      rw [hg]
      refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
      rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
      intro i hi
      refine lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) ?_
      exact_mod_cast Nat.lt_succ_of_le (Nat.sub_le n i)
    refine ⟨X ^ (n + 1) - g, monic_X_pow_sub hgdeg, ?_⟩

    have hfw : (aeval w⁻¹ f : L) = ∑ i ∈ Finset.range (n + 1), algebraMap R L (f.coeff i) * w⁻¹ ^ i := by
      rw [aeval_def, eval₂_eq_sum_range]
    have hkey : w ^ (n + 1) = ∑ i ∈ Finset.range (n + 1), algebraMap R L (f.coeff i) * w ^ (n - i) := by
      have h2 : w ^ (n + 1) = w ^ (n + 1) * ((a : L) * w⁻¹) := by rw [haw, mul_one]
      rw [h2, ← hf, show ((aeval w⁻¹).toRingHom f : L) = aeval w⁻¹ f from rfl, hfw,
        Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have : w ^ (n + 1) = w ^ (n - i) * w ^ i * w := by
        rw [← pow_add, Nat.sub_add_cancel hi', pow_succ]
      rw [this, inv_pow]
      have hwi : w ^ i ≠ 0 := pow_ne_zero _ hw0
      field_simp
    rw [← aeval_def, map_sub, map_pow, aeval_X, hg, map_sum]
    simp only [map_mul, aeval_C, map_pow, aeval_X]
    rw [hkey, sub_self]

  obtain ⟨B, hAB, hIB⟩ := Ideal.image_subset_nonunits_valuationSubring I hI
  have hwB : w⁻¹ ∈ B.nonunits := by
    apply hIB
    refine ⟨⟨w⁻¹, hwS⟩, ?_, rfl⟩
    exact Ideal.subset_span (Set.mem_singleton _)
  have hwB' : w ∉ B := by
    intro hw
    rw [ValuationSubring.mem_nonunits_iff] at hwB
    have h1 : B.valuation w ≤ 1 := (B.valuation_le_one_iff w).mpr hw
    have h2 : B.valuation w ≠ 0 := by
      rw [Valuation.ne_zero_iff]; exact hw0
    have h3 : B.valuation w⁻¹ = (B.valuation w)⁻¹ := map_inv₀ _ _
    rw [h3] at hwB
    have h4 : 1 ≤ (B.valuation w)⁻¹ := one_le_inv_iff₀.mpr ⟨zero_lt_iff.mpr h2, h1⟩
    exact absurd (lt_of_le_of_lt h4 hwB) (lt_irrefl _)
  apply hwB'
  apply h
  intro r
  apply hAB
  show algebraMap R L r ∈ S
  exact S.algebraMap_mem r

end Algebra

section CFE

variable {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F'] [Algebra K F]
  [Algebra K' F'] [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F']
  [IsScalarTower K F F']

theorem degree_eq_sum [IsAlgClosed K] [IsCurveOver K F] (E : Divisor K F) :
    E.degree = E.sum fun _ n => n := by
  simp [Divisor.degree, Finsupp.liftAddHom_apply, IsCurveOver.deg_eq_one_of_isAlgClosed]

private theorem algebraMap_mem_adjoin_simple {x a : F}
    (ha : a ∈ IntermediateField.adjoin K ({x} : Set F)) :
    algebraMap F F' a ∈ IntermediateField.adjoin K' ({algebraMap F F' x} : Set F') := by
  rw [IntermediateField.mem_adjoin_simple_iff] at ha ⊢
  obtain ⟨r, s, rfl⟩ := ha
  refine ⟨r.map (algebraMap K K'), s.map (algebraMap K K'), ?_⟩
  rw [aeval_map_algebraMap, aeval_map_algebraMap, map_div₀, aeval_algebraMap_apply,
    aeval_algebraMap_apply]

private theorem mem_range_of_isAlgebraic [IsAlgClosed K'] {t : F'} (ht : IsAlgebraic K' t) :
    t ∈ (algebraMap K' F').range := by
  have hint : IsIntegral K' t := ht.isIntegral
  exact minpoly.mem_range_of_degree_eq_one K' _
    (IsAlgClosed.degree_eq_one_of_irreducible K' (minpoly.irreducible hint))

/-- The pin's own `transcendental_algebraMap`, in the pin's binder shape, from the
port's stronger `ConstantFieldExtension.transcendental_algebraMap`. -/
private theorem transcendental_algebraMap [IsAlgClosed K] [CharZero K] [IsAlgClosed K']
    (_hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F]
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    {x : F} (_hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] :
    Transcendental K' (algebraMap F F' x) :=
  ConstantFieldExtension.transcendental_algebraMap (K := K) (x := x) hfg' hgen

private theorem algebraMap_mem_of_new [CharZero K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (W : Place K' F')
    (hW : ∀ v : Place K F, W.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring)
    (f : F) : algebraMap F F' f ∈ W.toValuationSubring := by
  by_contra hf
  set A := W.toValuationSubring.comap (algebraMap F F') with hA
  have hAK : ∀ a : K, algebraMap K F a ∈ A := fun a => by
    rw [hA, ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply K K' F']
    exact W.algebraMap_mem' _
  have hAtop : A ≠ ⊤ := by
    intro h
    apply hf
    have : f ∈ A := h ▸ Subring.mem_top f
    exact (ValuationSubring.mem_comap).1 this
  obtain ⟨v, hv⟩ := Place.exists_of_valuationSubring (K := K) x A hAK hAtop
  exact hW v hv.symm

set_option linter.style.haveILetI false in
private theorem exists_ord_sub_pos [IsAlgClosed K'] [IsCurveOver K' F']
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    {x' : F'} (hx' : Transcendental K' x') (c : K') :
    ∃ v' : Place K' F', 0 < v'.ord (x' - algebraMap K' F' c) := by
  classical
  obtain ⟨j, hj, hfin⟩ := id hfg'
  haveI := hfin
  set u := x' - algebraMap K' F' c with hu
  have hu_nmem : u ∉ (algebraMap K' F').range := by
    rintro ⟨a, ha⟩
    apply hx'
    have : x' = algebraMap K' F' (a + c) := by rw [map_add, ha, hu]; ring
    rw [this]
    exact isAlgebraic_algebraMap _
  have hu0 : u ≠ 0 := fun h => hu_nmem ⟨0, by rw [map_zero, h]⟩
  obtain ⟨v₀, hv₀⟩ : ∃ v : Place K' F', v.ord u ≠ 0 := by
    by_contra h
    push Not at h
    exact hu_nmem (Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed j hj h)
  by_contra hneg
  push Not at hneg
  obtain ⟨D, hD, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K') u hu0
  have hdeg' : (D.sum fun _ n => n) = 0 := by rw [← degree_eq_sum, hdeg]
  rw [Finsupp.sum] at hdeg'
  have hall := (Finset.sum_eq_zero_iff_of_nonpos (fun v _ => by rw [hD]; exact hneg v)).1 hdeg'
  have hv₀mem : v₀ ∈ D.support := by rw [Finsupp.mem_support_iff, hD]; exact hv₀
  exact hv₀ (by rw [← hD]; exact hall v₀ hv₀mem)

set_option linter.style.haveILetI false in
private theorem trace_mem [IsAlgClosed K] [CharZero K'] [IsCurveOver K F]
    {x : F} (hx : Transcendental K x)
    (hfg' : ∃ j : F', Transcendental K' j ∧
      FiniteDimensional (IntermediateField.adjoin K' ({j} : Set F')) F')
    [FiniteDimensional (IntermediateField.adjoin K' ({algebraMap F F' x} : Set F')) F']
    {c : K'} (hc : c ∉ Set.range (algebraMap K K'))
    (v' : Place K' F') (hv' : 0 < v'.ord (algebraMap F F' x - algebraMap K' F' c))
    (w : F')
    (hw : ∀ W : Place K' F',
      (∀ v : Place K F, W.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) →
        w ∈ W.toValuationSubring) :
    ((Algebra.trace (IntermediateField.adjoin K' ({algebraMap F F' x} : Set F')) F' w :
      IntermediateField.adjoin K' ({algebraMap F F' x} : Set F')) : F') ∈ v'.toValuationSubring := by
  set x' := algebraMap F F' x with hx'
  set kx' : IntermediateField K' F' := IntermediateField.adjoin K' ({x'} : Set F') with hkx'
  set R : ValuationSubring kx' := v'.toValuationSubring.comap (algebraMap kx' F') with hR
  have hRmem : ∀ g : kx', g ∈ R ↔ (g : F') ∈ v'.toValuationSubring := fun g =>
    ValuationSubring.mem_comap
  have hx'c_mem : x' - algebraMap K' F' c ∈ v'.toValuationSubring := mem_of_ord_nonneg v' hv'.le
  have hx'v' : x' ∈ v'.toValuationSubring := by
    have := add_mem hx'c_mem (v'.algebraMap_mem' c)
    simpa using this
  have hx'k : x' ∈ kx' := IntermediateField.mem_adjoin_simple_self K' x'

  have hnew : ∀ W : Place K' F',
      (∀ g : F', g ∈ kx' → g ∈ v'.toValuationSubring → g ∈ W.toValuationSubring) →
      ∀ v : Place K F, W.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring := by
    intro W hmemW v heq
    have hcomap : ∀ f : F, f ∈ v.toValuationSubring ↔ algebraMap F F' f ∈ W.toValuationSubring := by
      intro f
      rw [← heq, ValuationSubring.mem_comap]
    have hxv : x ∈ v.toValuationSubring := (hcomap x).2 (hmemW x' hx'k hx'v')
    obtain ⟨a, ha⟩ := exists_ord_sub_algebraMap_pos v hxv
    rcases ha with ha | ha
    · exact hx (ha ▸ isAlgebraic_algebraMap a)
    set u := x - algebraMap K F a with hu
    have hui : u⁻¹ ∉ v.toValuationSubring := not_mem_of_ord_neg v (by rw [v.ord_inv]; omega)
    apply hui
    rw [hcomap, map_inv₀]
    have hφu : algebraMap F F' u = x' - algebraMap K' F' (algebraMap K K' a) := by
      rw [hu, map_sub, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    have hca : c - algebraMap K K' a ≠ 0 := by
      intro h
      exact hc ⟨a, (sub_eq_zero.mp h).symm⟩
    have hord0 : v'.ord (algebraMap F F' u) = 0 := by
      rw [hφu]
      have : x' - algebraMap K' F' (algebraMap K K' a) =
          algebraMap K' F' (c - algebraMap K K' a) + (x' - algebraMap K' F' c) := by
        rw [map_sub]; ring
      rw [this]
      exact ord_algebraMap_add_eq_zero v' hca hv'
    apply hmemW
    · rw [hφu]
      exact inv_mem (sub_mem hx'k (kx'.algebraMap_mem _))
    · apply mem_of_ord_nonneg
      rw [v'.ord_inv, hord0, neg_zero]

  have hint : IsIntegral R w := by
    apply isIntegral_of_forall_mem_valuationSubring
    intro B hB
    have hB' : ∀ g : F', g ∈ kx' → g ∈ v'.toValuationSubring → g ∈ B := by
      intro g hg1 hg2
      exact hB ⟨⟨g, hg1⟩, (hRmem _).2 hg2⟩
    by_contra hwB
    have hBtop : B ≠ ⊤ := fun h => hwB (h ▸ Subring.mem_top w)
    have hBK : ∀ a : K', algebraMap K' F' a ∈ B := fun a =>
      hB' _ (kx'.algebraMap_mem a) (v'.algebraMap_mem' a)
    obtain ⟨j, hj, hfin⟩ := id hfg'
    haveI := hfin
    obtain ⟨W, hW⟩ := Place.exists_of_valuationSubring (K := K') j B hBK hBtop
    have hWnew := hnew W (fun g hg1 hg2 => by rw [hW]; exact hB' g hg1 hg2)
    exact hwB (hW ▸ hw W hWnew)
  have htr : IsIntegral R (Algebra.trace kx' F' w) := Algebra.isIntegral_trace hint
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := R) (K := kx')).mp htr
  have hmem : Algebra.trace kx' F' w ∈ R := hy ▸ y.2
  exact (hRmem _).1 hmem

end CFE

section PF

variable {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F'] [Algebra K F]
  [Algebra K' F'] [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F']
  [IsScalarTower K F F']

variable (F F') in

private theorem span_range_eq_adjoin (R : Type*) [CommSemiring R] [Algebra R F'] :
    Subalgebra.toSubmodule (Algebra.adjoin R (Set.range (algebraMap F F'))) =
      Submodule.span R (Set.range (algebraMap F F')) := by
  rw [Algebra.adjoin_eq_span]
  have : Set.range (algebraMap F F') = ((algebraMap F F').range.toSubmonoid : Set F') := by
    ext y; simp
  rw [this, Submonoid.closure_eq]

private theorem mem_span_of_regular [IsAlgClosed K'] [IsCurveOver K' F']
    (hfg' : ∃ j : F', Transcendental K' j ∧
      FiniteDimensional (IntermediateField.adjoin K' ({j} : Set F')) F')
    {x : F} (hx' : Transcendental K' (algebraMap F F' x))
    {t : F'} (ht : t ∈ IntermediateField.adjoin K' ({algebraMap F F' x} : Set F'))
    (hreg : ∀ c : K', c ∉ Set.range (algebraMap K K') →
      ∀ v' : Place K' F', 0 < v'.ord (algebraMap F F' x - algebraMap K' F' c) → 0 ≤ v'.ord t) :
    t ∈ Submodule.span K' (Set.range (algebraMap F F')) := by
  classical
  set x' := algebraMap F F' x with hx'def
  rcases eq_or_ne t 0 with rfl | ht0
  · exact zero_mem _
  rw [IntermediateField.mem_adjoin_simple_iff] at ht
  obtain ⟨p₀, q₀, hpq₀⟩ := ht
  have hq₀0 : q₀ ≠ 0 := by
    rintro rfl
    apply ht0
    rw [hpq₀, map_zero, div_zero]
  have haq₀ : aeval x' q₀ ≠ 0 := by
    intro h
    apply ht0
    rw [hpq₀, h, div_zero]

  set g := gcd p₀ q₀ with hg
  have hg0 : g ≠ 0 := fun h => hq₀0 ((gcd_eq_zero_iff p₀ q₀).1 h).2
  set p := p₀ / g with hp
  set q := q₀ / g with hq
  have hcop : IsCoprime p q := isCoprime_div_gcd_div_gcd hq₀0
  have hp₀ : p₀ = g * p := (EuclideanDomain.mul_div_cancel' hg0 (gcd_dvd_left _ _)).symm
  have hq₀' : q₀ = g * q := (EuclideanDomain.mul_div_cancel' hg0 (gcd_dvd_right _ _)).symm
  have hag : aeval x' g ≠ 0 := by
    intro h
    apply haq₀
    rw [hq₀', map_mul, h, zero_mul]
  have haq : aeval x' q ≠ 0 := by
    intro h
    apply haq₀
    rw [hq₀', map_mul, h, mul_zero]
  have hq0 : q ≠ 0 := by
    rintro h
    exact haq (by rw [h, map_zero])
  have ht' : t = aeval x' p / aeval x' q := by
    rw [hpq₀, hp₀, hq₀', map_mul, map_mul, mul_div_mul_left _ _ hag]
  have hap : aeval x' p ≠ 0 := by
    intro h
    apply ht0
    rw [ht', h, zero_div]

  have hroots : ∀ c ∈ q.roots, c ∈ Set.range (algebraMap K K') := by
    intro c hc
    by_contra hcK
    have hqc : q.IsRoot c := (mem_roots hq0).1 hc
    obtain ⟨v', hv'⟩ := exists_ord_sub_pos hfg' hx' c
    have h0t := hreg c hcK v' hv'
    have hsub_ne : x' - algebraMap K' F' c ≠ 0 := by
      intro h
      rw [h, Place.ord_zero] at hv'
      exact lt_irrefl _ hv'
    have hx'mem : x' ∈ v'.toValuationSubring := by
      have := add_mem (mem_of_ord_nonneg v' hv'.le) (v'.algebraMap_mem' c)
      simpa using this

    obtain ⟨q₂, hq₂⟩ := dvd_iff_isRoot.2 hqc
    have haq2_ne : aeval x' q₂ ≠ 0 := by
      intro h
      apply haq
      rw [hq₂, map_mul, h, mul_zero]
    have hordq : 1 ≤ v'.ord (aeval x' q) := by
      rw [hq₂, map_mul, map_sub, aeval_X, aeval_C, v'.ord_mul hsub_ne haq2_ne]
      have := ord_nonneg_of_mem v' (aeval_mem v' hx'mem q₂)
      omega

    have hpc : eval c p ≠ 0 := by
      intro h
      exact Polynomial.not_isUnit_X_sub_C c
        (hcop.isUnit_of_dvd' (dvd_iff_isRoot.2 h) (dvd_iff_isRoot.2 hqc))
    have hordp : v'.ord (aeval x' p) = 0 := by
      have hp_eq : p = C (eval c p) + (X - C c) * (p /ₘ (X - C c)) := by
        have := modByMonic_add_div p (X - C c)
        rw [modByMonic_X_sub_C_eq_C_eval] at this
        exact this.symm
      rcases eq_or_ne (aeval x' (p /ₘ (X - C c))) 0 with h2 | h2
      · rw [hp_eq, map_add, map_mul, h2, mul_zero, add_zero, aeval_C, ord_algebraMap]
      · rw [hp_eq, map_add, map_mul, aeval_C, map_sub, aeval_X, aeval_C]
        apply ord_algebraMap_add_eq_zero v' hpc
        rw [v'.ord_mul hsub_ne h2]
        have := ord_nonneg_of_mem v' (aeval_mem v' hx'mem (p /ₘ (X - C c)))
        omega
    have : v'.ord t = v'.ord (aeval x' p) - v'.ord (aeval x' q) := by
      rw [ht', div_eq_mul_inv, v'.ord_mul hap (inv_ne_zero haq), v'.ord_inv]
      ring
    omega

  set A : Subalgebra K' F' := Algebra.adjoin K' (Set.range (algebraMap F F')) with hA
  suffices hmem : t ∈ A by
    have : t ∈ Subalgebra.toSubmodule A := hmem
    rwa [span_range_eq_adjoin] at this
  have hφA : ∀ f : F, algebraMap F F' f ∈ A := fun f => Algebra.subset_adjoin ⟨f, rfl⟩
  have hx'A : x' ∈ A := hφA x
  have hpA : aeval x' p ∈ A := by
    rw [aeval_eq_sum_range]
    exact Subalgebra.sum_mem _ fun i _ => Subalgebra.smul_mem _ (Subalgebra.pow_mem _ hx'A _) _
  have hsplit : Multiset.card q.roots = q.natDegree :=
    splits_iff_card_roots.1 (IsAlgClosed.splits q)
  have hq_eq := C_leadingCoeff_mul_prod_multiset_X_sub_C hsplit
  have hlc : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hq0
  have hprod : aeval x' (q.roots.map fun c => X - C c).prod =
      (q.roots.map fun c => x' - algebraMap K' F' c).prod := by
    rw [map_multiset_prod, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro c _
    simp
  have hinvA : (aeval x' q)⁻¹ ∈ A := by
    rw [← hq_eq, map_mul, aeval_C, hprod, mul_inv, ← Multiset.prod_map_inv]
    refine Subalgebra.mul_mem _ ?_ ?_
    · rw [← map_inv₀]
      exact A.algebraMap_mem _
    · refine multiset_prod_mem _ (fun y hy => ?_)
      rw [Multiset.mem_map] at hy
      obtain ⟨c, hc, rfl⟩ := hy
      obtain ⟨a, rfl⟩ := hroots c hc
      have : (x' - algebraMap K' F' (algebraMap K K' a))⁻¹ =
          algebraMap F F' (x - algebraMap K F a)⁻¹ := by
        rw [map_inv₀, map_sub, ← IsScalarTower.algebraMap_apply,
          ← IsScalarTower.algebraMap_apply]
      rw [this]
      exact hφA _
  rw [ht', div_eq_mul_inv]
  exact A.mul_mem hpA hinvA

end PF

section BaseChange

variable {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F'] [Algebra K F]
  [Algebra K' F'] [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F']
  [IsScalarTower K F F']

variable (K K' F') in

private def iota (x : F) :
    IntermediateField.adjoin K ({x} : Set F) →+*
      IntermediateField.adjoin K' ({algebraMap F F' x} : Set F') where
  toFun a := ⟨algebraMap F F' a, algebraMap_mem_adjoin_simple a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

private theorem coe_iota (x : F) (a : IntermediateField.adjoin K ({x} : Set F)) :
    ((iota K K' F' x a : IntermediateField.adjoin K' ({algebraMap F F' x} : Set F')) : F') =
      algebraMap F F' a := rfl

private theorem algebraMap_smul (x : F) (a : IntermediateField.adjoin K ({x} : Set F)) (f : F) :
    algebraMap F F' (a • f) = iota K K' F' x a • algebraMap F F' f := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  rfl

set_option linter.style.haveILetI false in
theorem exists_basis [IsAlgClosed K] [CharZero K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F]
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    {x : F} (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    {n : ℕ} (y : Module.Basis (Fin n) (IntermediateField.adjoin K ({x} : Set F)) F) :
    ∃ y' : Module.Basis (Fin n) (IntermediateField.adjoin K' ({algebraMap F F' x} : Set F')) F',
      ∀ i, y' i = algebraMap F F' (y i) := by
  classical
  let kx : IntermediateField K F := IntermediateField.adjoin K ({x} : Set F)
  set x' := algebraMap F F' x with hx'def
  set kx' : IntermediateField K' F' := IntermediateField.adjoin K' ({x'} : Set F') with hkx'
  have hx' : Transcendental K' x' := transcendental_algebraMap hfg hfg' hgen hx

  have hli : LinearIndependent kx' (fun i => algebraMap F F' (y i)) := by
    rw [linearIndependent_iff']
    intro s r hr i hi
    have hden : ∀ i, ∃ b : K'[X], aeval x' b ≠ 0 ∧
        ∃ P : K'[X], aeval x' b * (r i : F') = aeval x' P := by
      intro i
      have hri : (r i : F') ∈ IntermediateField.adjoin K' ({x'} : Set F') := (r i).2
      rw [IntermediateField.mem_adjoin_simple_iff] at hri
      obtain ⟨P, b, hPb⟩ := hri
      by_cases hb : aeval x' b = 0
      · refine ⟨1, by simp, 0, ?_⟩
        rw [hPb, hb, div_zero]
        simp
      · exact ⟨b, hb, P, by rw [hPb, mul_div_cancel₀ _ hb]⟩
    choose b hb P hP using hden
    set B := ∏ j, aeval x' (b j) with hB
    have hB0 : B ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hb j
    set Q : Fin n → K'[X] := fun i => (∏ j ∈ Finset.univ.erase i, b j) * P i with hQ
    have hBQ : ∀ i, B * (r i : F') = aeval x' (Q i) := by
      intro i
      simp only [hQ]
      rw [map_mul, map_prod, ← hP i, ← mul_assoc, hB,
        Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    set N := (Finset.univ.sup fun i => (Q i).natDegree) + 1 with hN
    have hQN : ∀ i, (Q i).natDegree < N := fun i =>
      Nat.lt_succ_of_le (Finset.le_sup (f := fun i => (Q i).natDegree) (Finset.mem_univ i))
    have hrel : ∑ p ∈ Finset.range N ×ˢ s,
        algebraMap K' F' ((Q p.2).coeff p.1) * algebraMap F F' (x ^ p.1 * y p.2) = 0 := by
      have h0 : ∑ i ∈ s, (r i : F') * algebraMap F F' (y i) = 0 := by
        simpa [Algebra.smul_def] using hr
      have h1 : ∑ i ∈ s, aeval x' (Q i) * algebraMap F F' (y i) = 0 := by
        have : ∑ i ∈ s, aeval x' (Q i) * algebraMap F F' (y i) =
            B * ∑ i ∈ s, (r i : F') * algebraMap F F' (y i) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← hBQ, mul_assoc]
        rw [this, h0, mul_zero]
      rw [Finset.sum_product_right, ← h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [aeval_def, eval₂_eq_sum_range' _ (hQN i), Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_mul, map_pow]
      ring
    have hKind : LinearIndependent K (fun p : ℕ × Fin n => x ^ p.1 * y p.2) := by
      have hxk : Transcendental K (⟨x, IntermediateField.mem_adjoin_simple_self K x⟩ : kx) := by
        rw [← transcendental_algebraMap_iff (FaithfulSMul.algebraMap_injective kx F)]
        exact hx
      have h1 := linearIndependent_pow_of_transcendental hxk
      have h2 := linearIndependent_smul h1 y.linearIndependent
      convert h2 using 1
    have hK'ind := AlgebraicCurve.linearIndependent_of_constantFieldExtension K F K' F'
      hfg hfg' hgen hKind
    have hrel' : ∑ p ∈ Finset.range N ×ˢ s,
        (Q p.2).coeff p.1 • algebraMap F F' (x ^ p.1 * y p.2) = 0 := by
      simpa only [Algebra.smul_def] using hrel
    have hcoeff := (linearIndependent_iff'.1 hK'ind) _ _ hrel'
    have hQi : Q i = 0 := by
      ext a
      rw [coeff_zero]
      by_cases ha : a < N
      · exact hcoeff (a, i) (Finset.mk_mem_product (Finset.mem_range.2 ha) hi)
      · exact coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hQN i) (not_lt.1 ha))
    have h1 : B * (r i : F') = 0 := by rw [hBQ, hQi, map_zero]
    have h2 : (r i : F') = 0 := (mul_eq_zero.1 h1).resolve_left hB0
    exact_mod_cast h2

  have hsp : ⊤ ≤ Submodule.span kx' (Set.range fun i => algebraMap F F' (y i)) := by
    have hφ : ∀ f : F, algebraMap F F' f ∈
        Submodule.span kx' (Set.range fun i => algebraMap F F' (y i)) := by
      intro f
      rw [← y.sum_repr f, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [algebraMap_smul (K' := K') (F' := F')]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    haveI : Algebra.IsIntegral kx F := Algebra.IsIntegral.of_finite kx F
    have halg : ∀ g ∈ Set.range (algebraMap F F'), IsAlgebraic kx' g := by
      rintro _ ⟨f, rfl⟩
      have hint : IsIntegral kx f := Algebra.IsIntegral.isIntegral f
      have : IsIntegral kx' (algebraMap F F' f) := by
        refine ⟨(minpoly kx f).map (iota K K' F' x), (minpoly.monic hint).map _, ?_⟩
        rw [eval₂_map]
        have hcomp : (algebraMap kx' F').comp (iota K K' F' x) =
            (algebraMap F F').comp (algebraMap kx F) := by
          ext a
          rfl
        rw [hcomp, ← hom_eval₂, ← aeval_def, minpoly.aeval, map_zero]
      exact this.isAlgebraic
    have hmem : ∀ z : F', z ∈ Submodule.span kx' (Set.range (algebraMap F F')) := by
      intro z
      set E : IntermediateField kx' F' := IntermediateField.adjoin kx' (Set.range (algebraMap F F'))
        with hE
      have hzE : z ∈ E := by
        have hle : IntermediateField.adjoin K' (Set.range (algebraMap F F')) ≤
            IntermediateField.restrictScalars K' E :=
          IntermediateField.adjoin_le_iff.mpr (IntermediateField.subset_adjoin _ _)
        have := hle (hgen ▸ IntermediateField.mem_top (x := z))
        exact (IntermediateField.mem_restrictScalars K').1 this
      have hzA : z ∈ Algebra.adjoin kx' (Set.range (algebraMap F F')) := by
        rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg]
        exact hzE
      have : z ∈ Subalgebra.toSubmodule (Algebra.adjoin kx' (Set.range (algebraMap F F'))) := hzA
      rwa [span_range_eq_adjoin] at this
    intro z _
    have := hmem z
    refine (Submodule.span_le.2 ?_) this
    rintro _ ⟨f, rfl⟩
    exact hφ f
  exact ⟨Module.Basis.mk hli hsp, fun i => by rw [Module.Basis.mk_apply]⟩

private theorem trace_algebraMap {x : F} {n : ℕ}
    (y : Module.Basis (Fin n) (IntermediateField.adjoin K ({x} : Set F)) F)
    (y' : Module.Basis (Fin n) (IntermediateField.adjoin K' ({algebraMap F F' x} : Set F')) F')
    (hy : ∀ i, y' i = algebraMap F F' (y i)) (f : F) :
    Algebra.trace (IntermediateField.adjoin K' ({algebraMap F F' x} : Set F')) F'
        (algebraMap F F' f) =
      iota K K' F' x (Algebra.trace (IntermediateField.adjoin K ({x} : Set F)) F f) := by
  classical
  have hrepr : ∀ g : F, ∀ i, y'.repr (algebraMap F F' g) i = iota K K' F' x (y.repr g i) := by
    intro g i
    have : algebraMap F F' g = ∑ j, iota K K' F' x (y.repr g j) • y' j := by
      conv_lhs => rw [← y.sum_repr g, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [algebraMap_smul (K' := K') (F' := F'), hy]
    rw [this, y'.repr_sum_self]
  rw [Algebra.trace_eq_matrix_trace y, Algebra.trace_eq_matrix_trace y']
  simp only [Matrix.trace, Matrix.diag, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, hy, ← map_mul,
    hrepr]

private theorem eq_sum_trace_mul {x : F} {n : ℕ}
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F]
    (y : Module.Basis (Fin n) (IntermediateField.adjoin K ({x} : Set F)) F)
    (y' : Module.Basis (Fin n) (IntermediateField.adjoin K' ({algebraMap F F' x} : Set F')) F')
    (hy : ∀ i, y' i = algebraMap F F' (y i)) (z : F') :
    z = ∑ i, (Algebra.trace (IntermediateField.adjoin K' ({algebraMap F F' x} : Set F')) F'
        (z * algebraMap F F'
          ((Algebra.traceForm (IntermediateField.adjoin K ({x} : Set F)) F).dualBasis
            (traceForm_nondegenerate _ F) y i)) : F') * algebraMap F F' (y i) := by
  classical
  let kx : IntermediateField K F := IntermediateField.adjoin K ({x} : Set F)
  let kx' : IntermediateField K' F' := IntermediateField.adjoin K' ({algebraMap F F' x} : Set F')
  set yd := (Algebra.traceForm kx F).dualBasis (traceForm_nondegenerate kx F) y with hyd
  suffices h : ∀ i, y'.repr z i = Algebra.trace kx' F' (z * algebraMap F F' (yd i)) by
    conv_lhs => rw [← y'.sum_repr z]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h i, Algebra.smul_def, hy]
    rfl
  intro i
  let L₁ : F' →ₗ[kx'] kx' := y'.coord i
  let L₂ : F' →ₗ[kx'] kx' :=
    (Algebra.trace kx' F') ∘ₗ (LinearMap.mulRight kx' (algebraMap F F' (yd i)))
  have hL : L₁ = L₂ := by
    refine y'.ext fun j => ?_
    simp only [L₁, L₂, Module.Basis.coord_apply, Module.Basis.repr_self, LinearMap.comp_apply,
      LinearMap.mulRight_apply]
    rw [hy, ← map_mul, mul_comm, trace_algebraMap y y' hy, ← Algebra.traceForm_apply, hyd,
      LinearMap.BilinForm.apply_dualBasis_left]
    split_ifs with h
    · subst h
      simp
    · rw [map_zero, Finsupp.single_apply, ite_eq_right h]
  exact LinearMap.congr_fun hL z

end BaseChange

section Main

set_option linter.style.haveILetI false in
private theorem mem_span_range_algebraMap_of_constantFieldExtension
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [CharZero K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F] [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (z : F')
    (hz : ∀ v' : Place K' F',
      (∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) →
        z ∈ v'.toValuationSubring) :
    z ∈ Submodule.span K' (Set.range (algebraMap F F')) := by
  classical
  obtain ⟨x, hx, hfin⟩ := id hfg
  haveI := hfin
  set kx : IntermediateField K F := IntermediateField.adjoin K ({x} : Set F) with hkx
  set x' := algebraMap F F' x with hx'def
  set kx' : IntermediateField K' F' := IntermediateField.adjoin K' ({x'} : Set F') with hkx'
  haveI : CharZero K' := charZero_of_injective_algebraMap (algebraMap K K').injective
  haveI : CharZero kx := charZero_of_injective_algebraMap (algebraMap K kx).injective
  haveI : Algebra.IsSeparable kx F := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hx' : Transcendental K' x' := transcendental_algebraMap hfg hfg' hgen hx
  let y : Module.Basis (Fin (Module.finrank kx F)) kx F := Module.finBasis kx F
  obtain ⟨y', hy⟩ := exists_basis hfg hfg' hgen hx y
  haveI : FiniteDimensional kx' F' := Module.Finite.of_basis y'
  set yd := (Algebra.traceForm kx F).dualBasis (traceForm_nondegenerate kx F) y with hyd
  have ht : ∀ i, ((Algebra.trace kx' F' (z * algebraMap F F' (yd i)) : kx') : F') ∈
      Submodule.span K' (Set.range (algebraMap F F')) := by
    intro i
    refine mem_span_of_regular (K := K) hfg' hx' (Subtype.mem _) ?_
    intro c hc v' hv'
    apply ord_nonneg_of_mem
    apply trace_mem hx hfg' hc v' hv'
    intro W hW
    exact mul_mem (hz W hW) (algebraMap_mem_of_new x W hW _)
  have hA : ∀ t, t ∈ Submodule.span K' (Set.range (algebraMap F F')) → ∀ f : F,
      t * algebraMap F F' f ∈ Submodule.span K' (Set.range (algebraMap F F')) := by
    intro t ht f
    rw [← span_range_eq_adjoin] at ht ⊢
    exact (Algebra.adjoin K' _).mul_mem ht (Algebra.subset_adjoin ⟨f, rfl⟩)
  rw [eq_sum_trace_mul y y' hy z]
  exact Submodule.sum_mem _ fun i _ => hA _ (ht i) _

end Main

end W7XH

theorem mem_span_range_algebraMap_of_constantFieldExtension
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [CharZero K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F] [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (z : F')
    (hz : ∀ v' : Place K' F',
      (∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) →
        z ∈ v'.toValuationSubring) :
    z ∈ Submodule.span K' (Set.range (algebraMap F F')) :=
  W7XH.mem_span_range_algebraMap_of_constantFieldExtension K F K' F' hfg hfg' hgen z hz

/-! ## `finrankAlong` and the trace under a constant-field extension

`AlgebraicCurve.finrankAlong_eq_and_trace_eq_of_constantFieldExtension`, after
`P2M/Sol/S_AlgebraicCurve_finrankAlong_eq_and_trace_eq_of_constantFieldExtension.lean`
(407 ln) and its `Theorems/` wrapper.  A constant-field extension preserves
`finrankAlong` and commutes the trace with the algebra map. -/

namespace TraceBaseChangeProof

section Finite

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

set_option linter.style.haveILetI false in
private theorem exists_finset_adjoin_eq_top
    (hfg : ∃ x : F', Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F')) F') :
    ∃ G : Finset F', IntermediateField.adjoin K (G : Set F') = ⊤ := by
  classical
  obtain ⟨x, -, hxfin⟩ := hfg
  set Kx := IntermediateField.adjoin K ({x} : Set F')
  haveI := hxfin
  let b := Module.finBasis Kx F'
  refine ⟨insert x (Finset.univ.image b), ?_⟩
  have hset : ((insert x (Finset.univ.image b) : Finset F') : Set F') = {x} ∪ Set.range b := by
    ext y
    simp only [Finset.coe_insert, Finset.coe_image, Finset.coe_univ, Set.image_univ,
      Set.mem_insert_iff, Set.mem_range, Set.singleton_union]
  rw [hset, ← IntermediateField.adjoin_adjoin_left]
  have htop : IntermediateField.adjoin Kx (Set.range b) = ⊤ := by
    rw [eq_top_iff]
    intro f _
    have hspan : f ∈ Submodule.span Kx (Set.range b) := by
      rw [b.span_eq]; trivial
    have hle : Submodule.span Kx (Set.range b) ≤
        (IntermediateField.adjoin Kx (Set.range b)).toSubalgebra.toSubmodule :=
      Submodule.span_le.2 (fun y hy => IntermediateField.subset_adjoin Kx _ hy)
    exact hle hspan
  rw [htop]
  rfl

set_option linter.style.haveILetI false in
private theorem finiteAlong_of_isIntegral_of_adjoin_eq_top (φ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) (T : Finset F')
    (hT : IntermediateField.adjoin K (T : Set F') = ⊤) : FiniteAlong K φ := by
  letI : Algebra F F' := algebraAlong φ
  haveI := isScalarTower_along φ
  have hT' : IntermediateField.adjoin F (T : Set F') = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hle : IntermediateField.adjoin K (T : Set F') ≤
        (IntermediateField.adjoin F (T : Set F')).restrictScalars K :=
      IntermediateField.adjoin_le_iff.2 (IntermediateField.subset_adjoin F _)
    have hy : y ∈ IntermediateField.adjoin K (T : Set F') := by rw [hT]; trivial
    exact hle hy
  haveI : FiniteDimensional F (IntermediateField.adjoin F (T : Set F')) :=
    IntermediateField.finiteDimensional_adjoin (fun t _ => hφ t)
  have e : (IntermediateField.adjoin F (T : Set F')) ≃ₗ[F] F' :=
    ((IntermediateField.equivOfEq hT').trans IntermediateField.topEquiv).toLinearEquiv
  exact Module.Finite.equiv e

private theorem finiteAlong_of_hfg (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (hfg : ∃ x : F', Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F')) F') : FiniteAlong K φ := by
  obtain ⟨T, hT⟩ := exists_finset_adjoin_eq_top (K := K) (F' := F') hfg
  exact finiteAlong_of_isIntegral_of_adjoin_eq_top φ hφ T hT

end Finite

section Span

variable {K F E FE : Type*} [Field K] [Field F] [Field E] [Field FE]
  [Algebra K F] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
  [IsScalarTower K E FE] [IsScalarTower K F FE]

variable (E F FE) in

private def spanEF : Submodule E FE := Submodule.span E (Set.range (algebraMap F FE))

private theorem mul_mem_spanEF {a b : FE} (ha : a ∈ spanEF F E FE) (hb : b ∈ spanEF F E FE) :
    a * b ∈ spanEF F E FE := by
  unfold spanEF at *
  induction ha using Submodule.span_induction generalizing b with
  | mem x hx =>
      obtain ⟨f, rfl⟩ := hx
      induction hb using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨g, rfl⟩ := hy
          rw [← map_mul]
          exact Submodule.subset_span ⟨f * g, rfl⟩
      | zero => rw [mul_zero]; exact Submodule.zero_mem _
      | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
      | smul e y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ e hy
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ (hx hb) (hy hb)
  | smul e x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ e (hx hb)

private theorem one_mem_spanEF : (1 : FE) ∈ spanEF F E FE :=
  Submodule.subset_span ⟨1, map_one _⟩

private theorem algebraMap_E_mem_spanEF (e : E) : algebraMap E FE e ∈ spanEF F E FE := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem _ e one_mem_spanEF

private theorem prod_mem_spanEF {ι : Type*} (s : Finset ι) (q : ι → FE)
    (hq : ∀ i ∈ s, q i ∈ spanEF F E FE) :
    ∏ i ∈ s, q i ∈ spanEF F E FE := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty]; exact one_mem_spanEF
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact mul_mem_spanEF (hq a (Finset.mem_insert_self a s))
        (ih fun i hi => hq i (Finset.mem_insert_of_mem hi))

private def spanEFRing : Subring FE where
  carrier := spanEF F E FE
  mul_mem' ha hb := mul_mem_spanEF ha hb
  one_mem' := one_mem_spanEF
  add_mem' ha hb := Submodule.add_mem _ ha hb
  zero_mem' := Submodule.zero_mem _
  neg_mem' ha := Submodule.neg_mem _ ha

private theorem exists_div_of_adjoin_eq_top
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤) (z : FE) :
    ∃ p q : FE, p ∈ spanEF F E FE ∧ q ∈ spanEF F E FE ∧ q ≠ 0 ∧ z = p / q := by
  have hz : z ∈ IntermediateField.adjoin E (Set.range (algebraMap F FE)) := by rw [hgen]; trivial
  have hz' : z ∈ Subfield.closure (Set.range (algebraMap E FE) ∪ Set.range (algebraMap F FE)) := hz
  rw [Subfield.mem_closure_iff] at hz'
  obtain ⟨y, hy, w, hw, hyw⟩ := hz'
  have hsub : Subring.closure (Set.range (algebraMap E FE) ∪ Set.range (algebraMap F FE)) ≤
      (spanEFRing (E := E) (F := F) (FE := FE)) := by
    rw [Subring.closure_le]
    rintro a (⟨e, rfl⟩ | ⟨f, rfl⟩)
    · exact algebraMap_E_mem_spanEF e
    · exact Submodule.subset_span ⟨f, rfl⟩
  have hy' : y ∈ spanEF F E FE := hsub hy
  have hw' : w ∈ spanEF F E FE := hsub hw
  by_cases hw0 : w = 0
  · refine ⟨0, 1, Submodule.zero_mem _, one_mem_spanEF, one_ne_zero, ?_⟩
    rw [← hyw, hw0, div_zero, zero_div]
  · exact ⟨y, w, hy', hw', hw0, hyw.symm⟩

set_option linter.style.haveILetI false in
private theorem exists_linearIndependent_repr {d : ℕ} (c : Fin d → FE)
    (hc : ∀ j, c j ∈ spanEF F E FE) :
    ∃ (r : ℕ) (u : Fin r → F), LinearIndependent K u ∧
      ∀ j, ∃ e : Fin r → E, c j = ∑ m, e m • algebraMap F FE (u m) := by
  classical

  have hfin : ∀ j, ∃ S : Finset F, c j ∈
      Submodule.span E ((S.image (algebraMap F FE) : Finset FE) : Set FE) := by
    intro j
    obtain ⟨T, hT, hcT⟩ := Submodule.mem_span_finite_of_mem_span (hc j)
    obtain ⟨S, -, hS⟩ := Finset.subset_set_image_iff.1
      (show (T : Set FE) ⊆ algebraMap F FE '' Set.univ by rwa [Set.image_univ])
    exact ⟨S, by rwa [hS]⟩
  choose S hS using hfin
  set Sall : Finset F := Finset.univ.biUnion S with hSall

  set V : Submodule K F := Submodule.span K (Sall : Set F) with hV
  haveI : FiniteDimensional K V := FiniteDimensional.span_of_finite K Sall.finite_toSet
  set bV := Module.finBasis K V
  refine ⟨Module.finrank K V, fun m => (bV m : F), ?_, fun j => ?_⟩
  · exact bV.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  ·
    have hmem : ∀ f ∈ Sall, algebraMap F FE f ∈
        Submodule.span E (Set.range fun m => algebraMap F FE (bV m : F)) := by
      intro f hf
      have hfV : f ∈ V := Submodule.subset_span hf
      have hrepr := bV.sum_repr ⟨f, hfV⟩
      have hf' : f = ∑ m, bV.repr ⟨f, hfV⟩ m • (bV m : F) := by
        have := congrArg Subtype.val hrepr
        simpa only [Submodule.coe_sum, Submodule.coe_smul] using this.symm
      rw [hf', map_sum]
      refine Submodule.sum_mem _ fun m _ => ?_
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply K E FE, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
    have hle : Submodule.span E ((S j).image (algebraMap F FE) : Set FE) ≤
        Submodule.span E (Set.range fun m => algebraMap F FE (bV m : F)) := by
      rw [Submodule.span_le]
      intro a ha
      rw [Finset.coe_image] at ha
      obtain ⟨f, hf, rfl⟩ := ha
      exact hmem f (Finset.mem_biUnion.2 ⟨j, Finset.mem_univ j, hf⟩)
    have := hle (hS j)
    rw [Submodule.mem_span_range_iff_exists_fun] at this
    obtain ⟨e, he⟩ := this
    exact ⟨e, he.symm⟩

end Span

section Independence

variable {K F F' E FE F'E : Type*} [Field K] [Field F] [Field F'] [Field E] [Field FE] [Field F'E]
  [Algebra K F] [Algebra K F'] [Algebra K E]
  [Algebra E FE] [Algebra F FE] [Algebra K FE] [IsScalarTower K E FE] [IsScalarTower K F FE]
  [Algebra E F'E] [Algebra F' F'E] [Algebra K F'E] [IsScalarTower K E F'E] [IsScalarTower K F' F'E]

omit [Algebra K F'E] [IsScalarTower K E F'E] [IsScalarTower K F' F'E] in
set_option linter.style.haveILetI false in
private theorem linearIndependent_along_baseChange
    (φ : F →ₐ[K] F') (φE : FE →ₐ[E] F'E)
    (hφcomm : ∀ f : F, φE (algebraMap F FE f) = algebraMap F' F'E (φ f))
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (hli : ∀ {ι : Type} [Fintype ι] (g : ι → F'), LinearIndependent K g →
      LinearIndependent E (fun i => algebraMap F' F'E (g i)))
    {d : ℕ} (b : Fin d → F') (hb : letI := algebraAlong φ; LinearIndependent F b) :
    letI := algebraAlong φE
    LinearIndependent FE (fun j => algebraMap F' F'E (b j)) := by
  classical
  letI : Algebra F F' := algebraAlong φ
  letI : Algebra FE F'E := algebraAlong φE
  have hsmulF : ∀ (s : F) (y : F'), s • y = φ s * y := fun s y => rfl
  have hsmulFE : ∀ (s : FE) (y : F'E), s • y = φE s * y := fun s y => rfl

  have hcore : ∀ c : Fin d → FE, (∀ j, c j ∈ spanEF F E FE) →
      ∑ j, c j • algebraMap F' F'E (b j) = 0 → ∀ j, c j = 0 := by
    intro c hc hrel
    obtain ⟨r, u, hu, he⟩ := exists_linearIndependent_repr (K := K) c hc
    choose e he using he

    have hG : LinearIndependent K (fun mj : Fin r × Fin d => φ (u mj.1) * b mj.2) := by
      rw [Fintype.linearIndependent_iff]
      intro a ha
      have hsum : ∑ j, (∑ m, a (m, j) • u m) • b j = 0 := by
        have : ∑ mj : Fin r × Fin d, a mj • (φ (u mj.1) * b mj.2) =
            ∑ j, (∑ m, a (m, j) • u m) • b j := by
          rw [Fintype.sum_prod_type, Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hsmulF, map_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [map_smul, Algebra.smul_def, Algebra.smul_def, mul_assoc]
        rw [← this]; exact ha
      have h1 := Fintype.linearIndependent_iff.1 hb (fun j => ∑ m, a (m, j) • u m) hsum
      intro mj
      have h2 := Fintype.linearIndependent_iff.1 hu (fun m => a (m, mj.2)) (h1 mj.2) mj.1
      exact h2
    have hG' := hli _ hG

    have hrel' : ∑ mj : Fin r × Fin d,
        e mj.2 mj.1 • algebraMap F' F'E (φ (u mj.1) * b mj.2) = 0 := by
      have : ∑ mj : Fin r × Fin d, e mj.2 mj.1 • algebraMap F' F'E (φ (u mj.1) * b mj.2) =
          ∑ j, c j • algebraMap F' F'E (b j) := by
        rw [Fintype.sum_prod_type, Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hsmulFE, he j, map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [map_smul, hφcomm, map_mul, Algebra.smul_def, Algebra.smul_def, mul_assoc]
      rw [this]; exact hrel
    have h0 := Fintype.linearIndependent_iff.1 hG' (fun mj => e mj.2 mj.1) hrel'
    intro j
    rw [he j]
    refine Finset.sum_eq_zero fun m _ => ?_
    have h0' : e j m = 0 := h0 (m, j)
    rw [h0', zero_smul]

  rw [Fintype.linearIndependent_iff]
  intro c hrel
  choose p q hp hq hq0 hcpq using fun j => exists_div_of_adjoin_eq_top hgen (c j)
  set Q : FE := ∏ j, q j with hQ
  have hQ0 : Q ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hq0 j
  have hc' : ∀ j, c j * Q ∈ spanEF F E FE := by
    intro j
    have : c j * Q = p j * ∏ k ∈ Finset.univ.erase j, q k := by
      have hqj : q j ≠ 0 := hq0 j
      rw [hcpq j, hQ, ← Finset.prod_erase_mul Finset.univ q (Finset.mem_univ j)]
      field_simp
    rw [this]
    exact mul_mem_spanEF (hp j) (prod_mem_spanEF _ q fun k _ => hq k)
  have hrel' : ∑ j, (c j * Q) • algebraMap F' F'E (b j) = 0 := by
    have : ∑ j, (c j * Q) • algebraMap F' F'E (b j) =
        φE Q * ∑ j, c j • algebraMap F' F'E (b j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hsmulFE, hsmulFE, map_mul]; ring
    rw [this, hrel, mul_zero]
  intro j
  have := hcore (fun j => c j * Q) hc' hrel' j
  exact (mul_eq_zero.1 this).resolve_right hQ0

end Independence

end TraceBaseChangeProof

set_option linter.unusedVariables false in
set_option linter.style.haveILetI false in
open TraceBaseChangeProof in
/-- **A constant-field extension preserves `finrankAlong` and commutes the trace.**
Verbatim from
`Theorems/Thm_AlgebraicCurve_finrankAlong_eq_and_trace_eq_of_constantFieldExtension.lean`;
the pin's proof transports a `F`-basis of `F'` to an `FE`-basis of `F'E` by the
`E`-linear independence of `F'` over `F`. -/
theorem finrankAlong_eq_and_trace_eq_of_constantFieldExtension
    (K F : Type*) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K] [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (F' : Type*) [Field F'] [Algebra K F'] [IsCurveOver K F']
    (hfg' : ∃ x' : F', Transcendental K x' ∧
      FiniteDimensional (IntermediateField.adjoin K ({x'} : Set F')) F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (E FE : Type*) [Field E] [Field FE] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
    [IsScalarTower K E FE] [IsScalarTower K F FE] [IsAlgClosed E] [IsCurveOver E FE]
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (F'E : Type*) [Field F'E] [Algebra E F'E] [Algebra F' F'E] [Algebra K F'E]
    [IsScalarTower K E F'E] [IsScalarTower K F' F'E] [IsCurveOver E F'E]
    (hfgE' : ∃ x' : F'E, Transcendental E x' ∧
      FiniteDimensional (IntermediateField.adjoin E ({x'} : Set F'E)) F'E)
    (hgen' : IntermediateField.adjoin E (Set.range (algebraMap F' F'E)) = ⊤)
    (φE : FE →ₐ[E] F'E)
    (hφcomm : ∀ f : F, φE (algebraMap F FE f) = algebraMap F' F'E (φ f))
    (hφE : φE.toRingHom.IsIntegral) :
    FiniteAlong K φ ∧ FiniteAlong E φE ∧ finrankAlong E φE = finrankAlong K φ ∧
    ∀ u : F',
      (letI := algebraAlong φE; Algebra.trace FE F'E (algebraMap F' F'E u)) =
        algebraMap F FE (letI := algebraAlong φ; Algebra.trace F F' u) := by
  classical

  have hfinφ : FiniteAlong K φ := finiteAlong_of_hfg φ hφ hfg'
  have hfinφE : FiniteAlong E φE := finiteAlong_of_hfg φE hφE hfgE'
  letI : Algebra F F' := algebraAlong φ
  haveI : IsScalarTower K F F' := isScalarTower_along φ
  haveI : Module.Finite F F' := hfinφ
  letI : Algebra FE F'E := algebraAlong φE
  haveI : IsScalarTower E FE F'E := isScalarTower_along φE
  haveI : Module.Finite FE F'E := hfinφE
  have hsmulFE : ∀ (s : FE) (y : F'E), s • y = φE s * y := fun s y => rfl

  set b := Module.finBasis F F' with hb
  set d := Module.finrank F F' with hd

  have hli : LinearIndependent FE (fun j => algebraMap F' F'E (b j)) := by
    refine linearIndependent_along_baseChange (K := K) φ φE hφcomm hgen ?_ b b.linearIndependent
    intro ι _ g hg
    exact AlgebraicCurve.linearIndependent_of_constantFieldExtension K F' E F'E hfg' hfgE' hgen' hg

  have hspan : ⊤ ≤ Submodule.span FE (Set.range fun j => algebraMap F' F'E (b j)) := by

    have hF' : ∀ u : F', algebraMap F' F'E u ∈
        Submodule.span FE (Set.range fun j => algebraMap F' F'E (b j)) := by
      intro u
      have hu : u = ∑ j, b.repr u j • b j := (b.sum_repr u).symm
      rw [hu, map_sum]
      refine Submodule.sum_mem _ fun j _ => ?_
      have : algebraMap F' F'E (b.repr u j • b j) =
          (algebraMap F FE (b.repr u j)) • algebraMap F' F'E (b j) := by
        rw [hsmulFE, hφcomm, Algebra.smul_def, map_mul]; rfl
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

    haveI : Algebra.IsIntegral FE F'E := ⟨fun z => hφE z⟩
    haveI : Algebra.IsAlgebraic FE F'E := Algebra.IsIntegral.isAlgebraic
    set A : Subalgebra FE F'E := Algebra.adjoin FE (Set.range (algebraMap F' F'E)) with hA
    have hAfield : IsField A := Subalgebra.isField_of_algebraic A
    have hAinv : ∀ z ∈ A, z⁻¹ ∈ A := by
      intro z hz
      by_cases hz0 : z = 0
      · rw [hz0, inv_zero]; exact A.zero_mem
      · obtain ⟨w, hw⟩ := hAfield.mul_inv_cancel (a := ⟨z, hz⟩) (fun h => hz0 (congrArg Subtype.val h))
        have hw' : z * (w : F'E) = 1 := congrArg Subtype.val hw
        have : (w : F'E) = z⁻¹ :=
          (mul_eq_one_iff_eq_inv₀ hz0).1 (by rw [mul_comm]; exact hw')
        rw [← this]; exact w.2
    set A' : IntermediateField E F'E := (A.restrictScalars E).toIntermediateField
      (fun z hz => hAinv z hz) with hA'
    have hA'top : (⊤ : IntermediateField E F'E) ≤ A' := by
      rw [← hgen', IntermediateField.adjoin_le_iff]
      rintro _ ⟨u, rfl⟩
      show algebraMap F' F'E u ∈ A
      exact Algebra.subset_adjoin ⟨u, rfl⟩
    have hAtop : ∀ z : F'E, z ∈ A := fun z => hA'top (IntermediateField.mem_top (x := z))

    intro z _
    have hz : z ∈ Subalgebra.toSubmodule A := hAtop z
    rw [hA, Algebra.adjoin_eq_span] at hz
    have hclos : (Submonoid.closure (Set.range (algebraMap F' F'E)) : Set F'E) ⊆
        Set.range (algebraMap F' F'E) := by
      intro y hy
      have hle : Submonoid.closure (Set.range (algebraMap F' F'E)) ≤
          MonoidHom.mrange ((algebraMap F' F'E : F' →+* F'E) : F' →* F'E) :=
        Submonoid.closure_le.2 (by rintro _ ⟨u, rfl⟩; exact ⟨u, rfl⟩)
      obtain ⟨u, hu⟩ := hle hy
      exact ⟨u, hu⟩
    refine (Submodule.span_le.2 ?_) (Submodule.span_mono hclos hz)
    rintro _ ⟨u, rfl⟩
    exact hF' u
  set bE : Module.Basis (Fin d) FE F'E := Module.Basis.mk hli hspan with hbE
  have hbE_apply : ∀ j, bE j = algebraMap F' F'E (b j) := fun j => by
    rw [hbE, Module.Basis.mk_apply]

  have hdeg : finrankAlong E φE = finrankAlong K φ := by
    show Module.finrank FE F'E = Module.finrank F F'
    rw [Module.finrank_eq_card_basis bE, Fintype.card_fin]
  refine ⟨hfinφ, hfinφE, hdeg, fun u => ?_⟩

  show Algebra.trace FE F'E (algebraMap F' F'E u) = algebraMap F FE (Algebra.trace F F' u)
  rw [Algebra.trace_eq_matrix_trace bE, Algebra.trace_eq_matrix_trace b, Matrix.trace, Matrix.trace,
    map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul]

  have hexp : algebraMap F' F'E u * bE i =
      ∑ k, algebraMap F FE (b.repr (u * b i) k) • bE k := by
    rw [hbE_apply, ← map_mul]
    conv_lhs => rw [← b.sum_repr (u * b i)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hbE_apply, hsmulFE, hφcomm, Algebra.smul_def, map_mul]
    rfl
  rw [hexp, Module.Basis.repr_sum_self]

/-! ## The `finrank` and the number of places of an `adjoin`

`AlgebraicCurve.finrank_le_and_natCard_places_le_of_constantFieldExtension_adjoin`, after
`P2M/Sol/S_AlgebraicCurve_finrank_le_and_natCard_places_le_of_constantFieldExtension_adjoin.lean`
(348 ln) and its `Theorems/` wrapper: over an algebraically closed base, the finrank of
`k(y) ⊆ F` is at most that of `K'(t) ⊆ E`, and the poles and zeros of a nonzero `u ∈ F` do
not multiply along `F → E`. -/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped IntermediateField

namespace ConstantFieldAdjoin

section Main

private theorem linearIndependent_pow_of_transcendental {k A : Type*} [Field k] [Ring A] [Algebra k A]
    {Y : A} (hY : Transcendental k Y) (N : ℕ) :
    LinearIndependent k (fun n : Fin N => Y ^ (n : ℕ)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha m
  have hinj := transcendental_iff_injective.mp hY
  have hpoly : Polynomial.aeval Y (∑ n : Fin N, Polynomial.monomial (n : ℕ) (a n)) = 0 := by
    rw [map_sum]
    simpa [Polynomial.aeval_monomial, Algebra.smul_def] using ha
  have hzero : (∑ n : Fin N, Polynomial.monomial (n : ℕ) (a n)) = 0 :=
    hinj (by rw [hpoly, map_zero])
  have hcoeff := congrArg (fun p : Polynomial k => p.coeff (m : ℕ)) hzero
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at hcoeff
  rw [Finset.sum_eq_single m (fun n _ hn => ite_eq_right (fun h => hn (Fin.ext h))) (by simp)] at hcoeff
  simpa using hcoeff

variable {k : Type*} [Field k] [IsAlgClosed k] [CharZero k]
variable {F : Type*} [Field F] [Algebra k F]
variable {K' : Type*} [Field K'] [Algebra k K']
variable {L : Type*} [Field L] [Algebra K' L] (t : L) (E : IntermediateField K'⟮t⟯ L)
variable [Algebra F E] [Algebra k E] [IsScalarTower k K' E] [IsScalarTower k F E]

private theorem exists_mul_aeval_eq (l : K'⟮t⟯) :
    ∃ p q : Polynomial K', Polynomial.aeval t q ≠ 0 ∧ (l : L) * Polynomial.aeval t q = Polynomial.aeval t p := by
  obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff K' (l : L)).mp l.2
  by_cases hs : Polynomial.aeval t s = 0
  · refine ⟨0, 1, by simp, ?_⟩
    rw [hrs, hs, div_zero, zero_mul, map_zero]
  · refine ⟨r, s, hs, ?_⟩
    rw [hrs, div_mul_cancel₀ _ hs]

private theorem finrank_le_finrank (y : F) (hy : Transcendental k y) [FiniteDimensional k⟮y⟯ F]
    (hyt : (algebraMap F E y : L) = t)
    (hfg' : ∃ x : E, Transcendental K' x ∧ FiniteDimensional K'⟮x⟯ E)
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F E)) = ⊤)
    [FiniteDimensional K'⟮t⟯ E] :
    Module.finrank k⟮y⟯ F ≤ Module.finrank K'⟮t⟯ E := by
  classical
  set d := Module.finrank k⟮y⟯ F with hd
  let b := Module.finBasisOfFinrankEq k⟮y⟯ F hd.symm

  suffices hli : LinearIndependent K'⟮t⟯ (fun i : Fin d => algebraMap F E (b i)) by
    simpa using hli.fintype_card_le_finrank
  rw [Fintype.linearIndependent_iff]
  intro l hl

  have hpq : ∀ i, ∃ p q : Polynomial K', Polynomial.aeval t q ≠ 0 ∧
      ((l i : K'⟮t⟯) : L) * Polynomial.aeval t q = Polynomial.aeval t p := fun i => exists_mul_aeval_eq t (l i)
  choose p q hq hpq using hpq
  set Q : Polynomial K' := ∏ i, q i with hQ
  have hQ0 : Polynomial.aeval t Q ≠ 0 := by
    rw [hQ, map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hq i
  let P : Fin d → Polynomial K' := fun i => p i * ∏ j ∈ Finset.univ.erase i, q j
  have hP : ∀ i, ((l i : K'⟮t⟯) : L) * Polynomial.aeval t Q = Polynomial.aeval t (P i) := by
    intro i
    rw [hQ, ← Finset.mul_prod_erase Finset.univ q (Finset.mem_univ i), map_mul, ← mul_assoc, hpq i,
      ← map_mul]

  have hrelL : ∑ i, ((l i : K'⟮t⟯) : L) * (algebraMap F E (b i) : L) = 0 := by
    have := congrArg (fun e : E => (e : L)) hl
    simpa [IntermediateField.smul_def, smul_eq_mul] using this
  have hrelQ : ∑ i, Polynomial.aeval t (P i) * (algebraMap F E (b i) : L) = 0 := by
    have := congrArg (fun z : L => Polynomial.aeval t Q * z) hrelL
    simp only [mul_zero, Finset.mul_sum] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hP i]; ring

  set N : ℕ := (Finset.univ.sup fun i => (P i).natDegree) + 1 with hN
  have hdeg : ∀ i, (P i).natDegree < N := fun i =>
    Nat.lt_succ_of_le (Finset.le_sup (f := fun i => (P i).natDegree) (Finset.mem_univ i))

  have htn : ∀ n : ℕ, ((algebraMap F E (y ^ n) : E) : L) = t ^ n := by
    intro n
    rw [map_pow]
    push_cast
    rw [hyt]
  have hrel2 : ∑ pr : Fin N × Fin d,
      (P pr.2).coeff (pr.1 : ℕ) • ((algebraMap F E (y ^ (pr.1 : ℕ) * b pr.2) : E) : L) = 0 := by
    rw [← hrelQ, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.aeval_eq_sum_range' (hdeg i), Finset.sum_mul, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_mul, MulMemClass.coe_mul, htn, smul_mul_assoc]

  let Y : k⟮y⟯ := ⟨y, IntermediateField.mem_adjoin_simple_self k y⟩
  have hYt : Transcendental k Y := by
    have hinj : Function.Injective (algebraMap k⟮y⟯ F) := (algebraMap k⟮y⟯ F).injective
    rw [← transcendental_algebraMap_iff hinj]
    exact hy
  have hli1 : LinearIndependent k (fun pr : Fin N × Fin d => (Y ^ (pr.1 : ℕ)) • b pr.2) :=
    linearIndependent_smul (linearIndependent_pow_of_transcendental hYt N) b.linearIndependent
  have hfam : (fun pr : Fin N × Fin d => y ^ (pr.1 : ℕ) * b pr.2) =
      (fun pr : Fin N × Fin d => (Y ^ (pr.1 : ℕ)) • b pr.2) := by
    funext pr
    rw [IntermediateField.smul_def]
    rfl
  have hLD := AlgebraicCurve.linearIndependent_of_constantFieldExtension k F K' E
    ⟨y, hy, inferInstance⟩ hfg' hgen (b := fun pr : Fin N × Fin d => y ^ (pr.1 : ℕ) * b pr.2)
    (by rw [hfam]; exact hli1)
  have hLD' : LinearIndependent K'
      (fun pr : Fin N × Fin d => ((algebraMap F E (y ^ (pr.1 : ℕ) * b pr.2) : E) : L)) :=
    hLD.map' ((E.val.restrictScalars K').toLinearMap)
      (LinearMap.ker_eq_bot.mpr fun a b h => Subtype.ext h)
  have hcoeff : ∀ pr : Fin N × Fin d, (P pr.2).coeff (pr.1 : ℕ) = 0 :=
    Fintype.linearIndependent_iff.mp hLD' _ hrel2

  intro i
  have hPi : P i = 0 := by
    ext n
    rw [Polynomial.coeff_zero]
    rcases lt_or_ge n N with hn | hn
    · exact hcoeff (⟨n, hn⟩, i)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hdeg i) hn)
  have := hP i
  rw [hPi, map_zero, mul_eq_zero] at this
  rcases this with h | h
  · exact_mod_cast h
  · exact absurd h hQ0

private theorem natCard_places_le (y : F) (hy : Transcendental k y) [FiniteDimensional k⟮y⟯ F]
    [AlgebraicCurve.IsCurveOver k F]
    (hfg' : ∃ x : E, Transcendental K' x ∧ FiniteDimensional K'⟮x⟯ E)
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F E)) = ⊤)
    (u : F) (hu : u ≠ 0) :
    (Finite {P : AlgebraicCurve.Place K' E // 0 < P.ord (algebraMap F E u)} ∧
      Nat.card {P : AlgebraicCurve.Place K' E // 0 < P.ord (algebraMap F E u)} ≤
        Nat.card {P : AlgebraicCurve.Place k F // 0 < P.ord u}) ∧
      (Finite {P : AlgebraicCurve.Place K' E // P.ord (algebraMap F E u) < 0} ∧
      Nat.card {P : AlgebraicCurve.Place K' E // P.ord (algebraMap F E u) < 0} ≤
        Nat.card {P : AlgebraicCurve.Place k F // P.ord u < 0}) := by
  classical
  have hu' : algebraMap F E u ≠ 0 := (map_ne_zero (algebraMap F E)).mpr hu

  have hcomap : ∀ P : AlgebraicCurve.Place K' E, P.ord (algebraMap F E u) ≠ 0 →
      ∃ v : AlgebraicCurve.Place k F,
        v.toValuationSubring = P.toValuationSubring.comap (algebraMap F E) := by
    intro P hP
    refine AlgebraicCurve.Place.exists_toValuationSubring_eq_comap_ringHom (K := k) y (algebraMap F E)
      P.toValuationSubring (fun a => ?_) ?_
    · rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply k K' E]
      exact P.algebraMap_mem' _
    · rcases lt_or_gt_of_ne hP with h | h
      · exact ⟨u, fun hmem => by
          have := (AlgebraicCurve.Place.mem_iff_ord_nonneg_vs (v := P) (algebraMap F E u)).mp hmem; omega⟩
      · refine ⟨u⁻¹, fun hmem => ?_⟩
        rw [map_inv₀] at hmem
        have := (AlgebraicCurve.Place.mem_iff_ord_nonneg_vs (v := P) ((algebraMap F E u)⁻¹)).mp hmem
        rw [AlgebraicCurve.Place.ord_inv] at this
        omega

  have huniq : ∀ (v : AlgebraicCurve.Place k F) (P₁ P₂ : AlgebraicCurve.Place K' E),
      P₁.toValuationSubring.comap (algebraMap F E) = v.toValuationSubring →
      P₂.toValuationSubring.comap (algebraMap F E) = v.toValuationSubring → P₁ = P₂ := by
    intro v P₁ P₂ h₁ h₂
    obtain ⟨P', -, -, hP'⟩ :=
      AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension k F K' E
        ⟨y, hy, inferInstance⟩ hfg' hgen v
    rw [hP' P₁ h₁, hP' P₂ h₂]

  have hsign_pos : ∀ (P : AlgebraicCurve.Place K' E) (v : AlgebraicCurve.Place k F),
      v.toValuationSubring = P.toValuationSubring.comap (algebraMap F E) →
      (0 < P.ord (algebraMap F E u) ↔ 0 < v.ord u) := by
    intro P v hv
    have h1 : algebraMap F E u ∈ P.toValuationSubring ↔ u ∈ v.toValuationSubring := by
      rw [hv, ValuationSubring.mem_comap]
    have h2 : (algebraMap F E u)⁻¹ ∈ P.toValuationSubring ↔ u⁻¹ ∈ v.toValuationSubring := by
      rw [hv, ValuationSubring.mem_comap, map_inv₀]
    rw [AlgebraicCurve.Place.mem_iff_ord_nonneg_vs (v := P) (algebraMap F E u),
      AlgebraicCurve.Place.mem_iff_ord_nonneg_vs (v := v) u] at h1
    rw [AlgebraicCurve.Place.mem_iff_ord_nonneg_vs (v := P) ((algebraMap F E u)⁻¹),
      AlgebraicCurve.Place.mem_iff_ord_nonneg_vs (v := v) u⁻¹,
      AlgebraicCurve.Place.ord_inv, AlgebraicCurve.Place.ord_inv] at h2
    constructor
    · intro h; by_contra h'; have := h2.mpr (by omega); omega
    · intro h; by_contra h'; have := h2.mp (by omega); omega
  have hsign_neg : ∀ (P : AlgebraicCurve.Place K' E) (v : AlgebraicCurve.Place k F),
      v.toValuationSubring = P.toValuationSubring.comap (algebraMap F E) →
      (P.ord (algebraMap F E u) < 0 ↔ v.ord u < 0) := by
    intro P v hv
    have h1 : algebraMap F E u ∈ P.toValuationSubring ↔ u ∈ v.toValuationSubring := by
      rw [hv, ValuationSubring.mem_comap]
    rw [AlgebraicCurve.Place.mem_iff_ord_nonneg_vs (v := P) (algebraMap F E u),
      AlgebraicCurve.Place.mem_iff_ord_nonneg_vs (v := v) u] at h1
    constructor
    · intro h; by_contra h'; have := h1.mpr (by omega); omega
    · intro h; by_contra h'; have := h1.mp (by omega); omega

  obtain ⟨D, hD, -⟩ := AlgebraicCurve.HasPrincipalDivisors.exists_divisor (K := k) u hu
  have hfin_pos : Finite {P : AlgebraicCurve.Place k F // 0 < P.ord u} := by
    apply Finite.of_injective (fun P => (⟨P.1, by
      rw [Finsupp.mem_support_iff, hD]; exact P.2.ne'⟩ : D.support))
    intro P₁ P₂ h; exact Subtype.ext (congrArg (fun z : D.support => (z : AlgebraicCurve.Place k F)) h)
  have hfin_neg : Finite {P : AlgebraicCurve.Place k F // P.ord u < 0} := by
    apply Finite.of_injective (fun P => (⟨P.1, by
      rw [Finsupp.mem_support_iff, hD]; exact P.2.ne⟩ : D.support))
    intro P₁ P₂ h; exact Subtype.ext (congrArg (fun z : D.support => (z : AlgebraicCurve.Place k F)) h)
  constructor
  · let f : {P : AlgebraicCurve.Place K' E // 0 < P.ord (algebraMap F E u)} →
        {P : AlgebraicCurve.Place k F // 0 < P.ord u} := fun P =>
      ⟨(hcomap P.1 P.2.ne').choose,
        (hsign_pos P.1 _ (hcomap P.1 P.2.ne').choose_spec).mp P.2⟩
    suffices hf : Function.Injective f from
      ⟨Finite.of_injective f hf, Nat.card_le_card_of_injective f hf⟩
    intro P₁ P₂ h
    apply Subtype.ext
    have h' := congrArg (fun z : {P : AlgebraicCurve.Place k F // 0 < P.ord u} => z.1) h
    exact huniq _ P₁.1 P₂.1 (hcomap P₁.1 P₁.2.ne').choose_spec.symm
      (by rw [show (hcomap P₁.1 P₁.2.ne').choose = (hcomap P₂.1 P₂.2.ne').choose from h']
          exact (hcomap P₂.1 P₂.2.ne').choose_spec.symm)
  · let f : {P : AlgebraicCurve.Place K' E // P.ord (algebraMap F E u) < 0} →
        {P : AlgebraicCurve.Place k F // P.ord u < 0} := fun P =>
      ⟨(hcomap P.1 P.2.ne).choose,
        (hsign_neg P.1 _ (hcomap P.1 P.2.ne).choose_spec).mp P.2⟩
    suffices hf : Function.Injective f from
      ⟨Finite.of_injective f hf, Nat.card_le_card_of_injective f hf⟩
    intro P₁ P₂ h
    apply Subtype.ext
    have h' := congrArg (fun z : {P : AlgebraicCurve.Place k F // P.ord u < 0} => z.1) h
    exact huniq _ P₁.1 P₂.1 (hcomap P₁.1 P₁.2.ne).choose_spec.symm
      (by rw [show (hcomap P₁.1 P₁.2.ne).choose = (hcomap P₂.1 P₂.2.ne).choose from h']
          exact (hcomap P₂.1 P₂.2.ne).choose_spec.symm)

omit [IsAlgClosed k] [CharZero k] in

private theorem finiteDimensional_adjoin_of_coe_eq [FiniteDimensional K'⟮t⟯ E] (x : E) (hx : (x : L) = t) :
    FiniteDimensional K'⟮x⟯ E := by
  let f : E →ₐ[K'] L := E.val.restrictScalars K'
  have hmap : (K'⟮x⟯).map f = K'⟮t⟯ := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    congr 1
    rw [Set.singleton_eq_singleton_iff]
    exact hx
  let e : K'⟮x⟯ ≃ₐ[K'] K'⟮t⟯ := (IntermediateField.equivMap K'⟮x⟯ f).trans (IntermediateField.equivOfEq hmap)
  have he : ∀ z : K'⟮x⟯, ((e z : K'⟮t⟯) : L) = ((z : E) : L) := fun z => rfl
  refine Module.Finite.of_equiv_equiv (A₁ := K'⟮t⟯) (B₁ := E) (A₂ := K'⟮x⟯) (B₂ := E)
    e.symm.toRingEquiv (RingEquiv.refl E) ?_
  refine RingHom.ext fun l => Subtype.ext ?_
  change (((e.symm l : K'⟮x⟯) : E) : L) = ((algebraMap K'⟮t⟯ E l : E) : L)
  rw [← he (e.symm l), AlgEquiv.apply_symm_apply]
  rfl

omit [IsAlgClosed k] [CharZero k] in

private theorem adjoin_adjoin_subset {K' : Type*} [Field K'] {L : Type*} [Field L] [Algebra K' L] (S : Set L) (t : L)
    (ht : t ∈ IntermediateField.adjoin K' S) :
    ((IntermediateField.adjoin K'⟮t⟯ S : IntermediateField K'⟮t⟯ L) : Set L) ⊆
      ((IntermediateField.adjoin K' S : IntermediateField K' L) : Set L) := by
  have h1 : ((IntermediateField.adjoin K'⟮t⟯ S : IntermediateField K'⟮t⟯ L) : Set L) =
      (IntermediateField.restrictScalars K' (IntermediateField.adjoin K'⟮t⟯ S) : Set L) := rfl
  rw [h1, IntermediateField.restrictScalars_adjoin]
  have hle : IntermediateField.adjoin K' ((K'⟮t⟯ : Set L) ∪ S) ≤ IntermediateField.adjoin K' S := by
    rw [IntermediateField.adjoin_le_iff]
    apply Set.union_subset
    · have : K'⟮t⟯ ≤ IntermediateField.adjoin K' S := IntermediateField.adjoin_simple_le_iff.mpr ht
      exact SetLike.coe_subset_coe.mpr this
    · exact IntermediateField.subset_adjoin K' _
  exact SetLike.coe_subset_coe.mpr hle

omit [IsAlgClosed k] [CharZero k] in

private theorem adjoin_range_eq_top
    (hEle : (E : Set L) ⊆
      ((IntermediateField.adjoin K' (Set.range fun u : F => (algebraMap F E u : L)) :
        IntermediateField K' L) : Set L)) :
    IntermediateField.adjoin K' (Set.range (algebraMap F E)) = ⊤ := by
  let f : E →ₐ[K'] L := E.val.restrictScalars K'
  set A := IntermediateField.adjoin K' (Set.range (algebraMap F E)) with hA
  have hmapA : A.map f = IntermediateField.adjoin K' (Set.range fun u : F => (algebraMap F E u : L)) := by
    rw [hA, IntermediateField.adjoin_map, ← Set.range_comp]
    rfl
  rw [eq_top_iff]
  intro e _
  have he : (e : L) ∈ A.map f := by
    rw [hmapA]; exact hEle e.2
  obtain ⟨a, ha, hae⟩ := (IntermediateField.mem_map A).mp he
  have : a = e := Subtype.ext hae
  rw [← this]; exact ha

end Main

end ConstantFieldAdjoin

open scoped IntermediateField in
/-- **The finrank and the number of places of an `adjoin`.**  Verbatim from
`Theorems/Thm_AlgebraicCurve_finrank_le_and_natCard_places_le_of_constantFieldExtension_adjoin.lean`;
the pin's proof bounds `finrank k⟮y⟯ F` by the `K'⟮t⟯`-independence of the image of a
`k⟮y⟯`-basis, and counts the poles and zeros through the unique lift of a place. -/
theorem finrank_le_and_natCard_places_le_of_constantFieldExtension_adjoin
    {k : Type*} [Field k] [IsAlgClosed k] [CharZero k]
    {F : Type*} [Field F] [Algebra k F] [AlgebraicCurve.IsCurveOver k F]
    (y : F) (hy : Transcendental k y)
    [FiniteDimensional (IntermediateField.adjoin k ({y} : Set F)) F]
    {K' : Type*} [Field K'] [Algebra k K']
    {L : Type*} [Field L] [Algebra K' L] (t : L) (ht : Transcendental K' t)
    (E : IntermediateField (IntermediateField.adjoin K' ({t} : Set L)) L)
    [FiniteDimensional (IntermediateField.adjoin K' ({t} : Set L)) E]
    [Algebra F E] [Algebra k E] [IsScalarTower k K' E] [IsScalarTower k F E]
    (hyt : (algebraMap F E y : L) = t)
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F E)) = ⊤) :
    Module.finrank (IntermediateField.adjoin k ({y} : Set F)) F ≤
        Module.finrank (IntermediateField.adjoin K' ({t} : Set L)) E ∧
      ∀ u : F, u ≠ 0 →
        (Finite {P : AlgebraicCurve.Place K' E // 0 < P.ord (algebraMap F E u)} ∧
          Nat.card {P : AlgebraicCurve.Place K' E // 0 < P.ord (algebraMap F E u)} ≤
            Nat.card {P : AlgebraicCurve.Place k F // 0 < P.ord u}) ∧
        (Finite {P : AlgebraicCurve.Place K' E // P.ord (algebraMap F E u) < 0} ∧
          Nat.card {P : AlgebraicCurve.Place K' E // P.ord (algebraMap F E u) < 0} ≤
            Nat.card {P : AlgebraicCurve.Place k F // P.ord u < 0}) := by

  have hx : Transcendental K' (algebraMap F E y) := by
    haveI : IsScalarTower K' E L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    rw [← transcendental_algebraMap_iff (R := K') (A := L) (algebraMap E L).injective]
    change Transcendental K' ((algebraMap F E y : E) : L)
    rw [hyt]
    exact ht
  have hfg' : ∃ x : E, Transcendental K' x ∧ FiniteDimensional K'⟮x⟯ E :=
    ⟨algebraMap F E y, hx,
      ConstantFieldAdjoin.finiteDimensional_adjoin_of_coe_eq t E _ hyt⟩
  exact ⟨ConstantFieldAdjoin.finrank_le_finrank t E y hy hyt hfg' hgen,
    fun u hu => ConstantFieldAdjoin.natCard_places_le t E y hy hfg' hgen u hu⟩

end AlgebraicCurve
