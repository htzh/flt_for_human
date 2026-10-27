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
-/
import FLTForHuman.AlgebraicCurve.Defs.IsCurveOver
import FLTForHuman.AlgebraicCurve.Defs.Place
import FLTForHuman.AlgebraicCurve.Defs.PlaceCalculus
import FLTForHuman.AlgebraicCurve.Defs.PlaceEvaluation
import FLTForHuman.AlgebraicCurve.Defs.PushPull
import FLTForHuman.AlgebraicCurve.Defs.Repartitions

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

/-- A place's order function takes the value `1`: a place's valuation ring is a discrete
valuation ring, so it has an irreducible `π`, and `ord π = 1` for it. -/
theorem exists_ord_eq_one {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) :
    ∃ t : F, v.ord t = 1 :=
  let ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  ⟨π, v.ord_coe_irreducible hπ⟩

end Place

end AlgebraicCurve
