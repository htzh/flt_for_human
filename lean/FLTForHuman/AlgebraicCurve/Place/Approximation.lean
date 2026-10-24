/-
Weak approximation at finitely many places.  For a finite set `T` of places of a
function field `F/K` and prescribed integers `n v`, there is `f ≠ 0` with
`ord_v f = n v` at every `v ∈ T`.

The proof separates the places pairwise: `exists_mem_and_not_mem` gives, for two
distinct places, an element integral at one and not at the other, and
`exists_ord_neg_and_ord_pos` turns that pair into an element negative at one place
and positive at the other.  An induction on `T` (with the `z ^ m` trick of
`exists_ord_neg_forall_ord_pos`) produces, for each `v ∈ T`, an element negative at
`v` and positive at all the other places of `T`; `exists_indicator` corrects such an
element to one that is `1` at `v` and `0` at the other places of `T` up to a
prescribed precision `B`; and a sum of `t v * e v` over `v ∈ T`, where `t v` is a
uniformizer power realizing `n v`, then has the prescribed orders (`exists_forall_ord_eq_of_sep`).

Statements are transcribed verbatim from the pinned FLT
(`anthropics/fermats-last-theorem`, `aa2d8b3`): the headline from the
`Theorems/` wrapper, the proof from the `S_` file.  The `S_` file's public helpers
have no consumer outside it (checked over the pin and the port), so they are
`private` here; the pairwise separation `Place.exists_mem_and_not_mem`, which the
port already carries publicly in `Place/OrdCalculus.lean`, is imported rather than
re-proved, as are the `ord`/`adicValuation` dictionary lemmas of `Defs/` — including
`Place.adicValuation_le_exp_iff`, whose `x ≠ 0` form is the `adicValuation x ≤
exp (-N) ↔ N ≤ ord x` step this proof writes inline.  The one helper whose only
consumer is that separation lemma is a reading copy in
`Reserve/AlgebraicCurve/Place/ApproximationDead.lean`.

* `Theorems/Thm_AlgebraicCurve_Place_exists_forall_ord_eq.lean` (the statement)
* `P2M/Sol/S_AlgebraicCurve_Place_exists_forall_ord_eq.lean` (the proof, 407 lines)

spec-pin: Theorems/Thm_AlgebraicCurve_Place_exists_forall_ord_eq.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_exists_forall_ord_eq.lean
-/
import FLTForHuman.AlgebraicCurve.Defs.PushPull
import FLTForHuman.AlgebraicCurve.Defs.Repartitions
import FLTForHuman.AlgebraicCurve.Place.OrdCalculus

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero

namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Two distinct places differ on some element: one integral at `v`, not at `w`. -/
private theorem exists_ord_neg_and_ord_pos {v w : Place K F} (hvw : v ≠ w) :
    ∃ a : F, v.ord a < 0 ∧ 0 < w.ord a := by
  obtain ⟨x, hxv, hxw⟩ := exists_mem_and_not_mem hvw
  obtain ⟨y, hyw, hyv⟩ := exists_mem_and_not_mem hvw.symm
  have hx0 : x ≠ 0 := fun h => hxw (h ▸ zero_mem _)
  have hy0 : y ≠ 0 := fun h => hyv (h ▸ zero_mem _)
  refine ⟨y * x⁻¹, ?_, ?_⟩
  · rw [v.ord_mul hy0 (inv_ne_zero hx0), v.ord_inv]
    have h1 : v.ord y < 0 := (v.not_mem_iff_ord_neg hy0).mp hyv
    have h2 : 0 ≤ v.ord x := (v.mem_iff_ord_nonneg hx0).mp hxv
    omega
  · rw [w.ord_mul hy0 (inv_ne_zero hx0), w.ord_inv]
    have h1 : 0 ≤ w.ord y := (w.mem_iff_ord_nonneg hy0).mp hyw
    have h2 : w.ord x < 0 := (w.not_mem_iff_ord_neg hx0).mp hxw
    omega

/-- At a place where `x` is positive, `1 + x` is a unit. -/
private theorem adicValuation_lt_one_iff_ord_pos (v : Place K F) {x : F} (hx : x ≠ 0) :
    v.adicValuation x < 1 ↔ 0 < v.ord x := by
  rw [v.adicValuation_eq_exp_neg_ord hx, ← WithZero.exp_zero, WithZero.exp_lt_exp, neg_lt_zero]

/-- At a place where `x` is negative, `1 + x` keeps `x`'s order. -/
private theorem one_lt_adicValuation_iff_ord_neg (v : Place K F) {x : F} (hx : x ≠ 0) :
    1 < v.adicValuation x ↔ v.ord x < 0 := by
  rw [v.adicValuation_eq_exp_neg_ord hx, ← WithZero.exp_zero, WithZero.exp_lt_exp, neg_pos]

/-- `1 + t` is nonzero with the same order as `t` when `t` has negative order. -/
private theorem one_add_ne_zero_and_ord_eq_of_ord_neg (v : Place K F) {t : F} (ht : v.ord t < 0) :
    1 + t ≠ 0 ∧ v.ord (1 + t) = v.ord t := by
  have ht0 : t ≠ 0 := by rintro rfl; simp at ht
  have hval : v.adicValuation 1 < v.adicValuation t := by
    rw [Valuation.map_one, v.adicValuation_eq_exp_neg_ord ht0, ← WithZero.exp_zero,
      WithZero.exp_lt_exp]
    omega
  have hsum : v.adicValuation (1 + t) = v.adicValuation t :=
    v.adicValuation.map_add_eq_of_lt_right hval
  have hne : (1 : F) + t ≠ 0 := by
    intro h
    rw [h, Valuation.map_zero] at hsum
    exact v.adicValuation_ne_zero ht0 hsum.symm
  refine ⟨hne, ?_⟩
  simp only [Place.ord]
  rw [hsum]

/-- `1 + t` is a unit when `t` has positive order. -/
private theorem ord_one_add_of_ord_pos (v : Place K F) {t : F} (ht : 0 < v.ord t) :
    v.ord (1 + t) = 0 := by
  have ht0 : t ≠ 0 := by rintro rfl; simp at ht
  have hval : v.adicValuation t < v.adicValuation 1 := by
    rw [Valuation.map_one, v.adicValuation_eq_exp_neg_ord ht0, ← WithZero.exp_zero,
      WithZero.exp_lt_exp]
    omega
  have hsum : v.adicValuation (1 + t) = v.adicValuation 1 :=
    v.adicValuation.map_add_eq_of_lt_left hval
  simp only [Place.ord]
  rw [hsum, Valuation.map_one, WithZero.log_one, neg_zero]

/-- For a finite set of places `T` not containing `v`, an element negative at `v`
and positive at every place of `T`. -/
private theorem exists_ord_neg_forall_ord_pos (T : Finset (Place K F)) {v : Place K F}
    (hv : v ∉ T) :
    ∃ z : F, v.ord z < 0 ∧ ∀ w ∈ T, 0 < w.ord z := by
  classical
  revert hv
  induction T using Finset.induction_on with
  | empty =>
      intro _
      obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
      refine ⟨((π : F))⁻¹, ?_, by simp⟩
      rw [v.ord_inv, v.ord_coe_irreducible hπ]
      omega
  | @insert w₀ s hw₀s ih =>
      intro hv
      have hvw₀ : v ≠ w₀ := fun h => hv (h ▸ Finset.mem_insert_self w₀ s)
      have hvs : v ∉ s := fun h => hv (Finset.mem_insert_of_mem h)
      obtain ⟨z, hzv, hzs⟩ := ih hvs
      obtain ⟨u, huv, huw₀⟩ := exists_ord_neg_and_ord_pos hvw₀
      have hz0 : z ≠ 0 := fun h => by simp [h] at hzv
      have hu0 : u ≠ 0 := fun h => by simp [h] at huv
      set m : ℕ := (s.sup fun w => (1 - w.ord u).toNat) + 1 with hmdef
      have hm1 : 1 ≤ m := Nat.le_add_left 1 _
      have hmw : ∀ w ∈ s, 1 ≤ (m : ℤ) + w.ord u := by
        intro w hw
        have h1 : (1 - w.ord u).toNat ≤ s.sup fun w => (1 - w.ord u).toNat :=
          Finset.le_sup (f := fun w => (1 - w.ord u).toNat) hw
        omega
      rcases lt_trichotomy (w₀.ord z) 0 with hc | hc | hc
      ·
        have ht0 : (z ^ (m : ℤ)) ≠ 0 := zpow_ne_zero _ hz0
        have htv : v.ord (z ^ (m : ℤ)) < 0 := by
          rw [v.ord_zpow]
          exact mul_neg_of_pos_of_neg (by omega) hzv
        have htw₀ : w₀.ord (z ^ (m : ℤ)) < 0 := by
          rw [w₀.ord_zpow]
          exact mul_neg_of_pos_of_neg (by omega) hc
        obtain ⟨hne, heqv⟩ := v.one_add_ne_zero_and_ord_eq_of_ord_neg htv
        have heqw₀ := (w₀.one_add_ne_zero_and_ord_eq_of_ord_neg htw₀).2
        refine ⟨z ^ (m : ℤ) * (1 + z ^ (m : ℤ))⁻¹ * u, ?_, ?_⟩
        · rw [v.ord_mul (mul_ne_zero ht0 (inv_ne_zero hne)) hu0,
            v.ord_mul ht0 (inv_ne_zero hne), v.ord_inv, heqv]
          omega
        · intro w hw
          rcases Finset.mem_insert.mp hw with h | hws
          · rw [h, w₀.ord_mul (mul_ne_zero ht0 (inv_ne_zero hne)) hu0,
              w₀.ord_mul ht0 (inv_ne_zero hne), w₀.ord_inv, heqw₀]
            omega
          · have hwz := hzs w hws
            have htw : 0 < w.ord (z ^ (m : ℤ)) := by
              rw [w.ord_zpow]
              exact mul_pos (by omega) hwz
            have h1t := w.ord_one_add_of_ord_pos htw
            rw [w.ord_mul (mul_ne_zero ht0 (inv_ne_zero hne)) hu0,
              w.ord_mul ht0 (inv_ne_zero hne), w.ord_inv, h1t, w.ord_zpow]
            have hb : (m : ℤ) * 1 ≤ (m : ℤ) * w.ord z :=
              mul_le_mul_of_nonneg_left (by omega) (by omega)
            have h2 := hmw w hws
            omega
      ·
        have ht0 : (z ^ (m : ℤ)) ≠ 0 := zpow_ne_zero _ hz0
        refine ⟨z ^ (m : ℤ) * u, ?_, ?_⟩
        · rw [v.ord_mul ht0 hu0, v.ord_zpow]
          have hb : (m : ℤ) * v.ord z ≤ (m : ℤ) * (-1) :=
            mul_le_mul_of_nonneg_left (by omega) (by omega)
          omega
        · intro w hw
          rcases Finset.mem_insert.mp hw with h | hws
          · rw [h, w₀.ord_mul ht0 hu0, w₀.ord_zpow, hc]
            omega
          · rw [w.ord_mul ht0 hu0, w.ord_zpow]
            have h1 := hzs w hws
            have hb : (m : ℤ) * 1 ≤ (m : ℤ) * w.ord z :=
              mul_le_mul_of_nonneg_left (by omega) (by omega)
            have h2 := hmw w hws
            omega
      ·
        exact ⟨z, hzv, fun w hw =>
          (Finset.mem_insert.mp hw).elim (fun h => h ▸ hc) (hzs w)⟩

/-- An element which is `1` at `v` and `0` at the other places of `T`, to precision
`B`. -/
private theorem exists_indicator (v : Place K F) (T : Finset (Place K F)) {z : F}
    (hzv : v.ord z < 0) (hzT : ∀ w ∈ T, w ≠ v → 0 < w.ord z) (N : ℤ) :
    ∃ e : F, v.adicValuation (e - 1) ≤ WithZero.exp (-N) ∧
      ∀ w ∈ T, w ≠ v → w.adicValuation e ≤ WithZero.exp (-N) := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [ord_zero] at hzv
    exact lt_irrefl _ hzv
  obtain ⟨k, hkN, hk1⟩ : ∃ k : ℕ, N ≤ k ∧ (1 : ℤ) ≤ k :=
    ⟨N.toNat + 1, by have := Int.self_le_toNat N; push_cast; omega, by push_cast; omega⟩
  have hy0 : z ^ k ≠ 0 := pow_ne_zero _ hz0
  have hordy : ∀ w : Place K F, w.ord (z ^ k) = k * w.ord z := fun w => by
    rw [← zpow_natCast, ord_zpow]
  have hvy : v.ord (z ^ k) < 0 := by
    rw [hordy]
    exact mul_neg_of_pos_of_neg (by exact_mod_cast hk1) hzv
  have hvy' : 1 < v.adicValuation (z ^ k) := (v.one_lt_adicValuation_iff_ord_neg hy0).mpr hvy
  have h1y : v.adicValuation (1 + z ^ k) = v.adicValuation (z ^ k) :=
    Valuation.map_add_eq_of_lt_right _ (by rwa [map_one])
  have h1y0 : 1 + z ^ k ≠ 0 := by
    intro h
    rw [h, map_zero] at h1y
    exact v.adicValuation_ne_zero hy0 h1y.symm
  refine ⟨z ^ k / (1 + z ^ k), ?_, fun w hw hwv => ?_⟩
  · have he : z ^ k / (1 + z ^ k) - 1 = -(1 + z ^ k)⁻¹ := by
      rw [div_sub_one h1y0, show z ^ k - (1 + z ^ k) = -1 by ring, neg_div, one_div]
    rw [he, Valuation.map_neg, map_inv₀, h1y, v.adicValuation_eq_exp_neg_ord hy0,
      ← WithZero.exp_neg, neg_neg, WithZero.exp_le_exp, hordy]
    nlinarith
  · have hwy : 0 < w.ord (z ^ k) := by
      rw [hordy]
      exact mul_pos (by exact_mod_cast hk1) (hzT w hw hwv)
    have hwy' : w.adicValuation (z ^ k) < 1 := (w.adicValuation_lt_one_iff_ord_pos hy0).mpr hwy
    rw [map_div₀, Valuation.map_one_add_of_lt _ hwy', div_one, w.adicValuation_eq_exp_neg_ord hy0,
      WithZero.exp_le_exp, neg_le_neg_iff, hordy]
    have hwz : 0 < w.ord z := hzT w hw hwv
    nlinarith

/-- Weak approximation, given the separation of the places of `T`. -/
private theorem exists_forall_ord_eq_of_sep (T : Finset (Place K F)) (n : Place K F → ℤ)
    (hsep : ∀ v ∈ T, ∃ z : F, v.ord z < 0 ∧ ∀ w ∈ T, w ≠ v → 0 < w.ord z) :
    ∃ f : F, f ≠ 0 ∧ ∀ v ∈ T, v.ord f = n v := by
  classical
  rcases T.eq_empty_or_nonempty with rfl | hT
  · exact ⟨1, one_ne_zero, by simp⟩

  have hunif : ∀ v : Place K F, ∃ π : F, π ≠ 0 ∧ v.ord π = 1 := fun v => by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
    refine ⟨ϖ, ?_, v.ord_coe_irreducible hϖ⟩
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hϖ.ne_zero
  choose π hπ0 hπ1 using hunif

  set t : Place K F → F := fun v => π v ^ n v with ht
  have ht0 : ∀ v, t v ≠ 0 := fun v => zpow_ne_zero _ (hπ0 v)
  have htord : ∀ v w : Place K F, w.ord (t v) = n v * w.ord (π v) := fun v w => by
    rw [ht, ord_zpow]
  have htv : ∀ v, v.ord (t v) = n v := fun v => by rw [htord, hπ1, mul_one]

  set B : ℤ := 1 + ∑ v ∈ T, ∑ w ∈ T, (|n v| + |v.ord (t w)|) with hBdef
  have hB : ∀ v ∈ T, ∀ w ∈ T, n v - v.ord (t w) + 1 ≤ B := by
    intro v hv w hw
    have h1 : |n v| + |v.ord (t w)| ≤ ∑ w' ∈ T, (|n v| + |v.ord (t w')|) :=
      Finset.single_le_sum (f := fun w' => |n v| + |v.ord (t w')|)
        (fun _ _ => by positivity) hw
    have h2 : ∑ w' ∈ T, (|n v| + |v.ord (t w')|)
        ≤ ∑ v' ∈ T, ∑ w' ∈ T, (|n v'| + |v'.ord (t w')|) :=
      Finset.single_le_sum (f := fun v' => ∑ w' ∈ T, (|n v'| + |v'.ord (t w')|))
        (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) hv
    have h3 : n v ≤ |n v| := le_abs_self _
    have h4 : -v.ord (t w) ≤ |v.ord (t w)| := neg_le_abs _
    omega

  have hind : ∀ v : Place K F, ∃ e : F, v ∈ T →
      (v.adicValuation (e - 1) ≤ WithZero.exp (-B) ∧
        ∀ w ∈ T, w ≠ v → w.adicValuation e ≤ WithZero.exp (-B)) := by
    intro v
    by_cases hv : v ∈ T
    · obtain ⟨z, hz, hzT⟩ := hsep v hv
      obtain ⟨e, he⟩ := exists_indicator v T hz hzT B
      exact ⟨e, fun _ => he⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose e he using hind

  have main : ∀ v ∈ T, v.adicValuation (∑ w ∈ T, t w * e w) = WithZero.exp (-(n v)) := by
    intro v hv
    have hsplit : ∑ w ∈ T, t w * e w = t v + (t v * (e v - 1) + ∑ w ∈ T.erase v, t w * e w) := by
      rw [← Finset.add_sum_erase T (fun w => t w * e w) hv]
      ring
    have hvt : v.adicValuation (t v) = WithZero.exp (-(n v)) := by
      rw [v.adicValuation_eq_exp_neg_ord (ht0 v), htv]
    have hsmall : v.adicValuation (t v * (e v - 1) + ∑ w ∈ T.erase v, t w * e w)
        ≤ WithZero.exp (-(n v + 1)) := by
      apply Valuation.map_add_le
      · rw [map_mul, hvt]
        calc WithZero.exp (-(n v)) * v.adicValuation (e v - 1)
            ≤ WithZero.exp (-(n v)) * WithZero.exp (-B) := mul_le_mul_right (he v hv).1 _
          _ = WithZero.exp (-(n v) + -B) := (WithZero.exp_add _ _).symm
          _ ≤ WithZero.exp (-(n v + 1)) := WithZero.exp_le_exp.mpr (by
              have h := hB v hv v hv
              rw [htv] at h
              omega)
      · apply Valuation.map_sum_le
        intro w hw
        obtain ⟨hwv, hwT⟩ := Finset.mem_erase.mp hw
        rw [map_mul, v.adicValuation_eq_exp_neg_ord (ht0 w)]
        calc WithZero.exp (-(v.ord (t w))) * v.adicValuation (e w)
            ≤ WithZero.exp (-(v.ord (t w))) * WithZero.exp (-B) :=
              mul_le_mul_right ((he w hwT).2 v hv hwv.symm) _
          _ = WithZero.exp (-(v.ord (t w)) + -B) := (WithZero.exp_add _ _).symm
          _ ≤ WithZero.exp (-(n v + 1)) := WithZero.exp_le_exp.mpr (by
              have h := hB v hv w hwT
              omega)
    rw [hsplit, Valuation.map_add_eq_of_lt_left _ (lt_of_le_of_lt hsmall ?_), hvt]
    rw [hvt, WithZero.exp_lt_exp]
    omega
  obtain ⟨v₀, hv₀⟩ := hT
  have hf0 : (∑ w ∈ T, t w * e w) ≠ 0 := by
    intro h0
    have h := main v₀ hv₀
    rw [h0, map_zero] at h
    exact WithZero.exp_ne_zero h.symm
  refine ⟨∑ w ∈ T, t w * e w, hf0, fun v hv => ?_⟩
  have h := main v hv
  rw [v.adicValuation_eq_exp_neg_ord hf0, WithZero.exp_inj] at h
  omega

/-- For a finite set `T` of places and prescribed integers `n v`, there is a nonzero
`f : F` with `ord_v f = n v` at every `v ∈ T`. -/
theorem exists_forall_ord_eq {K F : Type*} [Field K] [Field F] [Algebra K F]
    (T : Finset (Place K F)) (n : Place K F → ℤ) :
    ∃ f : F, f ≠ 0 ∧ ∀ v ∈ T, v.ord f = n v := by
  classical
  refine exists_forall_ord_eq_of_sep T n fun v hv => ?_
  obtain ⟨z, hzv, hzT⟩ :=
    exists_ord_neg_forall_ord_pos (K := K) (F := F) (T.erase v) (Finset.notMem_erase v T)
  exact ⟨z, hzv, fun w hw hwv => hzT w (Finset.mem_erase.mpr ⟨hwv, hw⟩)⟩

end Place

end AlgebraicCurve
