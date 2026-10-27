/-
The general place calculus the `localParam` silos of the D-S cone re-prove: the
`ord`/`evalAt` interface through a place's valuation subring, its maximal ideal and
its residue field. Statements are transcribed verbatim from the pinned FLT
(`anthropics/fermats-last-theorem`, `aa2d8b3`), from the `FiniteCover` prelim
section of

* `P2M/Sol/S_AlgebraicCurve_Place_exists_finset_forall_exists_localParam_eq_complex.lean`

— the 23-lemma block the three `localParam` `S_` files of the D-S cone share: the
sibling `P2M/Sol/S_AlgebraicCurve_Place_localParam_eventually_eq_comp_evalAt_complex.lean`
re-proves 14 of them and
`…_exists_localParam_meromorphicOrderAt_evalAt_eq_ord_complex.lean` 9.

Only proof bodies are adapted to mathlib `v4.34.0`; the pin's declaration names and
statements are kept. The nine lemmas the port already carries are imported, not
re-proved:

* `Place.adicValuation_le_one_of_mem`, `Place.adicValuation_eq_exp_neg_ord`
  (`Defs/Repartitions.lean`);
* `Place.mem_of_ord_nonneg`, `Place.ord_nonneg_of_mem` (`Defs/PushPull.lean`);
* `Place.evalAt_algebraMap`, `Place.evalAt_mul` (`Defs/PlaceEvaluation.lean`);
* `Place.evalAt_zero`, `Place.ord_sub_evalAt_pos` (`Defs/PlaceCalculus.lean`);
* `Place.ord_algebraMap` (`Defs/Place.lean`).

The nineteen declared below are new: the thirteen of that block, and the six further
place lemmas the two sibling `S_` files carry — `evalAt_eq_of_ord_sub_algebraMap_eq_one`,
`mem_of_ord_sub_algebraMap_eq_one`, `ne_zero_of_ord_eq_one`, `evalAt_of_not_mem`,
`evalAt_eq_inv_evalAt_inv` and `eq_of_forall_ord_eq` — homed here because both siblings
need them and neither names a theory the other does not. `Place.sum_support_eq_zero`,
the one lemma of the block that is about divisors rather than places, is not here: it
is a lemma of the fibre argument and is homed with it in `Place/FiniteCover.lean`.

`Place.exists_ord_eq_one` is the wave's second pin-side root: a place's order function
takes the value `1`, because the valuation ring is a discrete valuation ring.

Wire: `spec/check_port.py` diffs every public declaration of this module against the
pin `S_` files named by the `spec-pin:` lines below.

spec-pin: P2M/Sol/S_AlgebraicCurve_Place_exists_finset_forall_exists_localParam_eq_complex.lean   -- comparable copy
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_localParam_eventually_eq_comp_evalAt_complex.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_Place_exists_ord_eq_one.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_exists_ord_eq_one.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_Place_ord_add_eq_of_lt.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_ord_add_eq_of_lt.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_Place_ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_isIntegral_adjoin_of_forall_ord_nonneg.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_isIntegral_adjoin_of_forall_ord_nonneg.lean   -- comparable copy
-/
import FLTForHuman.AlgebraicCurve.Defs.IsCurveOver
import FLTForHuman.AlgebraicCurve.Defs.Place
import FLTForHuman.AlgebraicCurve.Defs.PlaceCalculus
import FLTForHuman.AlgebraicCurve.Defs.PlaceEvaluation
import FLTForHuman.AlgebraicCurve.Defs.PushPull
import FLTForHuman.AlgebraicCurve.Defs.Repartitions
import FLTForHuman.AlgebraicCurve.Place.FromValuationSubring
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Ideal.Nonunits
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Valuation.ValuationSubring

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem not_mem_iff_ord_neg (v : Place K F) {f : F} (hf : f ≠ 0) :
    f ∉ v.toValuationSubring ↔ v.ord f < 0 := by
  constructor
  · intro h
    by_contra hle
    exact h (mem_of_ord_nonneg v hf (not_lt.mp hle))
  · intro h hmem
    have := ord_nonneg_of_mem v hmem
    omega

theorem ord_pos_of_mem_maximalIdeal (v : Place K F) {f : F} (hf0 : f ≠ 0)
    (hf : f ∈ v.toValuationSubring)
    (hmax : (⟨f, hf⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring) :
    0 < v.ord f := by
  have hle : v.adicValuation f ≤ 1 := adicValuation_le_one_of_mem v hf
  have hne : v.adicValuation f ≠ 1 := by
    intro h1
    have hu : IsUnit (⟨f, hf⟩ : v.toValuationSubring) :=
      (v.adicValuation_coe_eq_one_iff ⟨f, hf⟩).mp h1
    exact (IsLocalRing.mem_maximalIdeal _ |>.mp hmax) hu
  have hlt : v.adicValuation f < 1 := lt_of_le_of_ne hle hne
  rw [adicValuation_eq_exp_neg_ord v hf0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
  omega

theorem residue_eq_zero_of_ord_pos (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring)
    (h : 0 < v.ord f) :
    IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal]
  intro hu
  have h1 : v.adicValuation f = 1 := (v.adicValuation_coe_eq_one_iff ⟨f, hf⟩).mpr hu
  by_cases hf0 : f = 0
  · subst hf0; simp at h
  rw [adicValuation_eq_exp_neg_ord v hf0, ← WithZero.exp_zero] at h1
  have := WithZero.exp_injective h1
  omega

set_option linter.style.haveILetI false in
theorem isRational_of_isCurveOver [IsAlgClosed K] [IsCurveOver K F] (v : Place K F) :
    v.IsRational := by
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := v.ResidueField)).2

theorem residue_algebraMap (v : Place K F) (c : K) :
    IsLocalRing.residue v.toValuationSubring ⟨algebraMap K F c, v.algebraMap_mem' c⟩
      = algebraMap K v.ResidueField c := by
  have h : (⟨algebraMap K F c, v.algebraMap_mem' c⟩ : v.toValuationSubring)
      = algebraMap K v.toValuationSubring c := Subtype.ext (v.coe_algebraMap c).symm
  rw [h]; rfl

theorem evalAt_sub_algebraMap (v : Place K F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) (c : K) :
    v.evalAt (f - algebraMap K F c) = v.evalAt f - c := by
  have hc : algebraMap K F c ∈ v.toValuationSubring := v.algebraMap_mem' c
  have hfc : f - algebraMap K F c ∈ v.toValuationSubring := sub_mem hf hc
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv hfc, map_sub, v.algebraMap_evalAt hv hf,
    ← residue_algebraMap v c, ← map_sub]
  rfl

theorem evalAt_eq_zero_of_ord_pos (v : Place K F) {f : F} (hf0 : f ≠ 0) (h : 0 < v.ord f) :
    v.evalAt f = 0 := by
  have hf : f ∈ v.toValuationSubring := mem_of_ord_nonneg v hf0 h.le
  rw [v.evalAt_of_mem hf, residue_eq_zero_of_ord_pos v hf h, ← map_zero (algebraMap K _),
    v.residueInv_algebraMap]

theorem ord_pos_of_evalAt_eq_zero (v : Place K F) (hv : v.IsRational) {f : F} (hf0 : f ≠ 0)
    (hf : f ∈ v.toValuationSubring) (h0 : v.evalAt f = 0) : 0 < v.ord f := by
  refine ord_pos_of_mem_maximalIdeal v hf0 hf ?_
  rw [← IsLocalRing.residue_eq_zero_iff, ← v.algebraMap_evalAt hv hf, h0, map_zero]

theorem evalAt_eq_of_ord_sub_algebraMap_pos (w : Place K F) (hw : w.IsRational) (t : F) (c : K)
    (h : 0 < w.ord (t - algebraMap K F c)) : w.evalAt t = c := by
  have hne : t - algebraMap K F c ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at h; exact lt_irrefl _ h
  have hmem : t - algebraMap K F c ∈ w.toValuationSubring := mem_of_ord_nonneg w hne h.le
  have ht : t ∈ w.toValuationSubring := by
    simpa using add_mem hmem (w.algebraMap_mem' c)
  have h0 : w.evalAt (t - algebraMap K F c) = 0 := evalAt_eq_zero_of_ord_pos w hne h
  rw [evalAt_sub_algebraMap w hw ht c] at h0
  exact sub_eq_zero.mp h0

theorem mem_of_ord_sub_algebraMap_pos (w : Place K F) (t : F) (c : K)
    (h : 0 < w.ord (t - algebraMap K F c)) : t ∈ w.toValuationSubring := by
  have hne : t - algebraMap K F c ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at h; exact lt_irrefl _ h
  have hmem : t - algebraMap K F c ∈ w.toValuationSubring := mem_of_ord_nonneg w hne h.le
  simpa using add_mem hmem (w.algebraMap_mem' c)

theorem sub_algebraMap_mem_iff (v : Place K F) (f : F) (a : K) :
    f - algebraMap K F a ∈ v.toValuationSubring ↔ f ∈ v.toValuationSubring := by
  constructor
  · intro h; simpa using add_mem h (v.algebraMap_mem' a)
  · intro h; exact sub_mem h (v.algebraMap_mem' a)

theorem ord_sub_algebraMap_of_not_mem (v : Place K F) {f : F} (hf : f ∉ v.toValuationSubring)
    (a : K) : v.ord (f - algebraMap K F a) = v.ord f := by
  have hf0 : f ≠ 0 := fun h => hf (h ▸ zero_mem _)
  have hfa : f - algebraMap K F a ∉ v.toValuationSubring := by
    rwa [sub_algebraMap_mem_iff]
  have hfa0 : f - algebraMap K F a ≠ 0 := fun h => hfa (h ▸ zero_mem _)
  have hlt : v.adicValuation (algebraMap K F a) < v.adicValuation f := by
    have h1 : v.adicValuation (algebraMap K F a) ≤ 1 :=
      adicValuation_le_one_of_mem v (v.algebraMap_mem' a)
    have h2 : 1 < v.adicValuation f := by
      have hneg := (not_mem_iff_ord_neg v hf0).mp hf
      rw [adicValuation_eq_exp_neg_ord v hf0, ← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega
    exact h1.trans_lt h2
  have hval : v.adicValuation (f - algebraMap K F a) = v.adicValuation f :=
    Valuation.map_sub_eq_of_lt_left _ hlt
  unfold Place.ord
  rw [hval]

theorem exists_mem_and_not_mem {v w : Place K F} (hne : v ≠ w) :
    ∃ s : F, s ∈ v.toValuationSubring ∧ s ∉ w.toValuationSubring := by
  by_contra hcon
  push Not at hcon
  apply hne
  apply Place.ext
  refine le_antisymm (fun s hs => hcon s hs) fun x hx => ?_
  by_contra hxv
  have hx0 : x ≠ 0 := fun h => hxv (h ▸ zero_mem _)
  obtain ⟨y, hyw⟩ : ∃ y : F, y ∉ w.toValuationSubring := by
    by_contra hall
    push Not at hall
    exact w.ne_top' (eq_top_iff.mpr fun y _ => hall y)
  have hyv : y ∉ v.toValuationSubring := fun h => hyw (hcon y h)
  have hy0 : y ≠ 0 := fun h => hyw (h ▸ zero_mem _)
  have hxneg : v.ord x < 0 := (not_mem_iff_ord_neg v hx0).mp hxv
  have hyneg : v.ord y < 0 := (not_mem_iff_ord_neg v hy0).mp hyv
  set j : ℤ := -v.ord x with hj
  set k : ℤ := -v.ord y with hk
  set u : F := y ^ j * x⁻¹ ^ k with hu
  have hu0 : u ≠ 0 := mul_ne_zero (zpow_ne_zero _ hy0) (zpow_ne_zero _ (inv_ne_zero hx0))
  have hordu : v.ord u = 0 := by
    rw [hu, v.ord_mul (zpow_ne_zero _ hy0) (zpow_ne_zero _ (inv_ne_zero hx0)), v.ord_zpow,
      v.ord_zpow, v.ord_inv, hj, hk]
    ring
  have huinv : u⁻¹ ∈ w.toValuationSubring :=
    hcon _ (mem_of_ord_nonneg v (inv_ne_zero hu0) (by rw [v.ord_inv, hordu]; simp))
  have huw : u ∈ w.toValuationSubring := by
    have hyj : y ^ j = u * x ^ k := by
      rw [hu, mul_assoc, ← mul_zpow, inv_mul_cancel₀ hx0, one_zpow, mul_one]
    exact hcon _ (mem_of_ord_nonneg v hu0 hordu.ge)
  have hyj_mem : y ^ j ∈ w.toValuationSubring := by
    have hyj : y ^ j = u * x ^ k := by
      rw [hu, mul_assoc, ← mul_zpow, inv_mul_cancel₀ hx0, one_zpow, mul_one]
    rw [hyj]
    have hk0 : 0 ≤ k := by omega
    have hxk : x ^ k ∈ w.toValuationSubring := by
      rw [show k = ((k.toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg hk0).symm, zpow_natCast]
      exact pow_mem hx _
    exact mul_mem huw hxk
  have h1 : 0 ≤ w.ord (y ^ j) := ord_nonneg_of_mem w hyj_mem
  rw [w.ord_zpow] at h1
  have hj0 : 0 < j := by omega
  have h2 : 0 ≤ w.ord y := by
    by_contra hlt
    push Not at hlt
    have : j * w.ord y < 0 := mul_neg_of_pos_of_neg hj0 hlt
    omega
  exact hyw (mem_of_ord_nonneg w hy0 h2)

theorem evalAt_eq_of_ord_sub_algebraMap_eq_one (w : Place K F) (hw : w.IsRational) (t : F) (c : K)
    (h : w.ord (t - algebraMap K F c) = 1) : w.evalAt t = c := by
  have hne : t - algebraMap K F c ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at h; exact zero_ne_one h
  have hmem : t - algebraMap K F c ∈ w.toValuationSubring := mem_of_ord_nonneg w hne (by omega)
  have ht : t ∈ w.toValuationSubring := by
    simpa using add_mem hmem (w.algebraMap_mem' c)
  have h0 : w.evalAt (t - algebraMap K F c) = 0 := evalAt_eq_zero_of_ord_pos w hne (by omega)
  rw [evalAt_sub_algebraMap w hw ht c] at h0
  exact sub_eq_zero.mp h0

theorem mem_of_ord_sub_algebraMap_eq_one (w : Place K F) (t : F) (c : K)
    (h : w.ord (t - algebraMap K F c) = 1) : t ∈ w.toValuationSubring := by
  have hne : t - algebraMap K F c ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at h; exact zero_ne_one h
  have hmem : t - algebraMap K F c ∈ w.toValuationSubring := mem_of_ord_nonneg w hne (by omega)
  simpa using add_mem hmem (w.algebraMap_mem' c)

theorem ne_zero_of_ord_eq_one (w : Place K F) {t : F} (h : w.ord t = 1) : t ≠ 0 := by
  intro h0; rw [h0, Place.ord_zero] at h; exact zero_ne_one h

theorem evalAt_of_not_mem (v : Place K F) {f : F} (hf : f ∉ v.toValuationSubring) :
    v.evalAt f = 0 := dite_eq_right hf

theorem evalAt_eq_inv_evalAt_inv (v : Place K F) (hv : v.IsRational) {f : F} (hf0 : f ≠ 0)
    (hf : f⁻¹ ∈ v.toValuationSubring) : v.evalAt f = (v.evalAt f⁻¹)⁻¹ := by
  rcases (ord_nonneg_of_mem v hf).eq_or_lt with h0 | hpos
  ·
    have hf' : f ∈ v.toValuationSubring :=
      mem_of_ord_nonneg v hf0 (by rw [Place.ord_inv] at h0; omega)
    have h1 : v.evalAt f * v.evalAt f⁻¹ = 1 := by
      rw [← evalAt_mul v hv hf' hf, mul_inv_cancel₀ hf0, Place.evalAt_one]
    exact eq_inv_of_mul_eq_one_left h1
  ·
    have hnot : f ∉ v.toValuationSubring := by
      intro hmem
      have := ord_nonneg_of_mem v hmem
      rw [Place.ord_inv] at hpos; omega
    rw [evalAt_of_not_mem v hnot, evalAt_eq_zero_of_ord_pos v (inv_ne_zero hf0) hpos, inv_zero]

theorem eq_of_forall_ord_eq {v w : Place K F} (h : ∀ f : F, f ≠ 0 → v.ord f = w.ord f) :
    v = w := by
  apply Place.ext
  refine SetLike.ext fun f => ?_
  by_cases hf : f = 0
  · subst hf; simp
  exact ⟨fun hm => mem_of_ord_nonneg w hf (h f hf ▸ ord_nonneg_of_mem v hm),
    fun hm => mem_of_ord_nonneg v hf ((h f hf).symm ▸ ord_nonneg_of_mem w hm)⟩

/-- **Strict ultrametric equality**: the larger order wins, `ord (f + g) = ord f` when
`ord f < ord g`. Pin `Place.ord_add_eq_of_lt`
(`Theorems/Thm_AlgebraicCurve_Place_ord_add_eq_of_lt.lean`), which the ℙ¹ residue core
still carries privately in two places. -/
theorem ord_add_eq_of_lt (v : Place K F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0)
    (h : v.ord f < v.ord g) : v.ord (f + g) = v.ord f := by
  have hval : v.adicValuation g < v.adicValuation f := by
    have hf' := v.adicValuation_ne_zero hf
    have hg' := v.adicValuation_ne_zero hg
    rw [← WithZero.log_lt_log hg' hf']
    unfold Place.ord at h
    omega
  unfold Place.ord
  rw [Valuation.map_add_eq_of_lt_left _ hval]

/-- A place's order function takes the value `1`: a place's valuation ring is a discrete
valuation ring, so it has an irreducible `π`, and `ord π = 1` for it. -/
theorem exists_ord_eq_one {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) :
    ∃ t : F, v.ord t = 1 :=
  let ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  ⟨π, v.ord_coe_irreducible hπ⟩

/-- **Integrality transfers `ord_nonneg`.**  Verbatim from
`Theorems/Thm_AlgebraicCurve_Place_ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg.lean`;
the pin's `S_` proof is transcribed (the integrality criterion
`Place.mem_toValuationSubring_of_isIntegral_adjoin`). -/
theorem ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg {K F : Type*} [Field K] [Field F]
    [Algebra K F] (v : Place K F) {j u : F} (hu : IsIntegral (Algebra.adjoin K {j}) u)
    (hj : 0 ≤ v.ord j) : 0 ≤ v.ord u := by
  have hjmem : j ∈ v.toValuationSubring := by
    rcases eq_or_ne j 0 with rfl | hj0
    · exact zero_mem _
    · exact (v.mem_iff_ord_nonneg hj0).mpr hj
  exact v.ord_nonneg_of_mem (v.mem_toValuationSubring_of_isIntegral_adjoin hjmem hu)

end Place

/-! ## Integrality from `ord`-nonnegativity at the places of a transcendental generator

The pin keeps these two lemmas `private` inside
`P2M/Sol/S_AlgebraicCurve_isIntegral_adjoin_of_forall_ord_nonneg.lean`, in a nested
`namespace INTGlue`; they are transcribed here as private lemmas in the same
namespace, the second taking the subring `(Algebra.adjoin A {y}).toSubring` directly
(the pin's `Subalgebra` and its `toSubring` are interchangeable through the coercion
the pin relies on) so that `LocalSubring.ofPrime` sees an `Ideal` of a `Subring`. -/

namespace INTGlue

open Polynomial in
private theorem isIntegral_of_mem_adjoin_inv {A F : Type*} [CommRing A] [Field F] [Algebra A F]
    {z : F} (hz0 : z ≠ 0) (hmem : z ∈ Algebra.adjoin A ({z⁻¹} : Set F)) : IsIntegral A z := by
  classical
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem
  obtain ⟨p, hp⟩ := hmem
  have hp' : aeval z⁻¹ p = z := hp

  have hdeg : (∑ i ∈ Finset.range (p.natDegree + 1), C (p.coeff i) * X ^ (p.natDegree - i)).degree ≤
      (p.natDegree : WithBot ℕ) := by
    refine (Polynomial.degree_sum_le _ _).trans (Finset.sup_le fun i _ => ?_)
    exact (Polynomial.degree_C_mul_X_pow_le _ _).trans (by exact_mod_cast Nat.sub_le _ _)
  refine ⟨X ^ (p.natDegree + 1) - ∑ i ∈ Finset.range (p.natDegree + 1), C (p.coeff i) * X ^ (p.natDegree - i),
    Polynomial.monic_X_pow_sub (hdeg.trans_lt (by exact_mod_cast Nat.lt_succ_self _)), ?_⟩
  have hz : z = ∑ i ∈ Finset.range (p.natDegree + 1), algebraMap A F (p.coeff i) * z⁻¹ ^ i := by
    conv_lhs => rw [← hp']
    rw [Polynomial.aeval_eq_sum_range]
    simp only [Algebra.smul_def]
  have hzpow : ∀ i ∈ Finset.range (p.natDegree + 1), z ^ p.natDegree * z⁻¹ ^ i = z ^ (p.natDegree - i) := by
    intro i hi
    have hi' : i ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hi'
    rw [hk, Nat.add_sub_cancel_left, pow_add, mul_comm (z ^ i) (z ^ k), mul_assoc, ← mul_pow,
      mul_inv_cancel₀ hz0, one_pow, mul_one]
  rw [eval₂_sub, sub_eq_zero, eval₂_pow, eval₂_X, eval₂_finsetSum]
  simp only [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X]
  rw [pow_succ]
  conv_lhs => arg 2; rw [hz]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [mul_left_comm, hzpow i hi]

set_option linter.style.haveILetI false in
private theorem isIntegral_of_forall_valuationSubring {F : Type*} [Field F] (A : Subring F) (z : F)
    (h : ∀ V : ValuationSubring F, A ≤ V.toSubring → z ∈ V) : IsIntegral A z := by
  classical
  by_contra hnot
  have hz0 : z ≠ 0 := by rintro rfl; exact hnot isIntegral_zero
  set y : F := z⁻¹ with hy
  let Bs : Subring F := (Algebra.adjoin A ({y} : Set F)).toSubring
  have hyBs : y ∈ Bs := Algebra.subset_adjoin (Set.mem_singleton y)
  have hzBs : z ∉ Bs := fun hzB => hnot (isIntegral_of_mem_adjoin_inv hz0 hzB)

  have hyu : (⟨y, hyBs⟩ : Bs) ∈ nonunits Bs := by
    intro hu
    obtain ⟨u, hu⟩ := hu
    have h1 : ((u : Bs) : F) * ((u⁻¹ : Bsˣ) : Bs) = 1 := by
      rw [← Subring.coe_mul, Units.mul_inv]; rfl
    rw [hu] at h1
    have hinv : ((u⁻¹ : Bsˣ) : Bs).1 = z := by
      have hz1 : y⁻¹ = ((u⁻¹ : Bsˣ) : Bs).1 := inv_eq_of_mul_eq_one_right h1
      rw [← hz1, hy, inv_inv]
    exact hzBs (hinv ▸ ((u⁻¹ : Bsˣ) : Bs).2)
  obtain ⟨m, hm, hym⟩ := exists_max_ideal_of_mem_nonunits hyu

  haveI : m.IsMaximal := hm
  let L : LocalSubring F := LocalSubring.ofPrime Bs m
  obtain ⟨V, hV⟩ := L.exists_le_valuationSubring
  obtain ⟨hLV, hloc⟩ := LocalSubring.le_def.mp hV
  have hBL : Bs ≤ L.toSubring := LocalSubring.le_ofPrime Bs m
  have hAV : A ≤ V.toSubring := by
    intro a ha
    have hmem : (a : F) ∈ Bs := by
      show (a : F) ∈ Algebra.adjoin A ({y} : Set F)
      exact Subalgebra.algebraMap_mem (Algebra.adjoin A ({y} : Set F)) ⟨a, ha⟩
    exact hLV (hBL hmem)
  have hzV : z ∈ V := h V hAV

  have hyL : algebraMap Bs L.toSubring ⟨y, hyBs⟩ ∈ IsLocalRing.maximalIdeal L.toSubring :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff L.toSubring m ⟨y, hyBs⟩).mpr hym
  have hcoe : ((algebraMap Bs L.toSubring ⟨y, hyBs⟩ : L.toSubring) : F) = y := by
    show algebraMap L.toSubring F (algebraMap Bs L.toSubring ⟨y, hyBs⟩) = y
    rw [← IsScalarTower.algebraMap_apply Bs L.toSubring F]
    rfl
  have hyV' : ¬ IsUnit (Subring.inclusion hLV (algebraMap Bs L.toSubring ⟨y, hyBs⟩)) := by
    intro hu
    have hmax := (IsLocalRing.mem_maximalIdeal _).mp hyL
    exact hmax (hloc.map_nonunit _ hu)
  apply hyV'
  refine isUnit_iff_exists_inv.mpr ⟨⟨z, hzV⟩, ?_⟩
  ext
  simp only [Subring.coe_mul, Subring.coe_inclusion, hcoe, Subring.coe_one]
  rw [hy, inv_mul_cancel₀ hz0]

end INTGlue

set_option linter.unusedVariables false in
/-- **Integrality from the `ord`-nonnegativity of the generator.**  Verbatim from
`Theorems/Thm_AlgebraicCurve_isIntegral_adjoin_of_forall_ord_nonneg.lean`; the pin's
`S_` proof is transcribed, its `INTGlue` preliminaries included. -/
theorem isIntegral_adjoin_of_forall_ord_nonneg {K F : Type*} [Field K] [Field F] [Algebra K F]
    [CharZero K] (t : F) (ht : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F]
    [AlgebraicCurve.HasPrincipalDivisors K F] (z : F)
    (hz : ∀ v : AlgebraicCurve.Place K F, 0 ≤ v.ord t → 0 ≤ v.ord z) :
    IsIntegral (Algebra.adjoin K ({t} : Set F)) z := by
  classical
  have key : IsIntegral (Algebra.adjoin K ({t} : Set F)).toSubring z := by
    refine INTGlue.isIntegral_of_forall_valuationSubring _ z fun V hV => ?_
    by_cases hz0 : z = 0
    · rw [hz0]; exact V.zero_mem
    by_cases htop : V = ⊤
    · rw [htop]; exact ValuationSubring.mem_top z
    have hK : ∀ a : K, algebraMap K F a ∈ V := fun a =>
      hV (Subalgebra.algebraMap_mem (Algebra.adjoin K ({t} : Set F)) a)
    obtain ⟨v, hv⟩ := Place.exists_of_valuationSubring t V hK htop
    have htV : t ∈ v.toValuationSubring := by
      rw [hv]; exact hV (Algebra.subset_adjoin (Set.mem_singleton t))
    have h1 : 0 ≤ v.ord t := v.ord_nonneg_of_mem htV
    have h2 := v.mem_of_ord_nonneg hz0 (hz v h1)
    rwa [hv] at h2
  exact key

end AlgebraicCurve
