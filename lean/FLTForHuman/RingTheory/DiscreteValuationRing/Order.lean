/-
  The additive order on a discrete valuation ring, and its extension to the units of the
  fraction field.

  For a discrete valuation ring `A` inside a field `L`, `ordA A a` is the exponent `n` with
  `span {a} = maximalIdeal A ^ n`, `ordZ A x` is its extension to `x : Lˣ`, and
  `ord A : Additive Lˣ →+ ℤ` packages that extension as an additive homomorphism. The three
  ideal-power lemmas (`exists_span_eq_pow`, `pow_maximalIdeal_ne_of_lt`,
  `pow_maximalIdeal_injective`) are the uniqueness input.

  **Homed here 2026-10-13.** Nothing in this file mentions a number field, an adele ring or
  `NumberField.TateGlobal`: the whole development is quantified over an abstract
  `(A : ValuationSubring L) [IsDiscreteValuationRing A]`. It reached the port inside
  `NumberField/NumberField/TateGlobal/Ideles.lean` — under the namespace
  `NumberField.TateGlobal.ValuationOrd` — only because the pin copies it verbatim into sixteen
  of its `S_` files and that file was the first to need it. Its consumers are ten `TateGlobal`
  modules (35 reference sites) that instantiate it at `A := v.adicCompletionIntegers F`, i.e.
  exactly the pattern of a generic engine homed inside one of its consumers. This is the same
  correction the port already made for the generic measure-theoretic engines, homed under
  `MeasureTheory/` rather than `AutomorphicForm/` (playbook §3.1–§3.2: a module is a mathematical
  role, a directory is a theory). The namespace follows mathlib, which hosts its own DVR API
  (`addVal`, `idealOrderIsoENat`) in `Mathlib/RingTheory/DiscreteValuationRing/Basic.lean`; the
  last names are the pin's, so `unwired_register.py` still reads each `-- pin:` comment.

  **Which names to use.** The consumed API is `ord` (`Additive Lˣ →+ ℤ`) with `ord_spec` for
  its defining property, `ord_ofMul_of_mem` and `ord_ofMul_mk0_of_irreducible` for evaluating it
  on `Units.mk0` of an element of `A` (notably a uniformizer), and `ord_eq_zero_iff`. The other
  eleven — `ordA`, `ordZ`, `exists_rep`, `coe_mk_ne_zero`, `ordA_span`, `ordA_unique`, `ordA_mul`,
  `ordZ_spec`, `exists_span_eq_pow`, `pow_maximalIdeal_ne_of_lt`, `pow_maximalIdeal_injective` —
  are the *construction internals* of that API and have **no consumer in the port** (measured:
  `ord` 25 external sites, `ord_eq_zero_iff` 6, `ord_ofMul_mk0_of_irreducible` 3,
  `ord_ofMul_of_mem` 1, `ord_spec` 0, all eleven 0). The pin keeps those eleven `private` in every
  file that copies the prelude; they are public here only so that the statement checker diffs
  them. For a generic discrete-valuation-ring question, prefer mathlib's
  `IsDiscreteValuationRing.addVal` (the `ℕ∞`-valued additive valuation on the ring) and
  `idealOrderIsoENat` (`Ideal R ≃o ENatᵒᵈ`), which v4.34 supplies.

  Transcribed from `S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean`
  (pinned `aa2d8b3`, lines 107–290); the pin keeps the eleven helpers `private` per file, a
  file-scoping device for its copy-per-file prelude, and the port keeps them public in this
  single home.
-/
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring

set_option autoImplicit false

noncomputable section

namespace IsDiscreteValuationRing

open Ideal IsLocalRing

variable {L : Type*} [Field L] (A : ValuationSubring L) [IsDiscreteValuationRing A]

-- pin: exists_span_eq_pow (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:113)
theorem exists_span_eq_pow {a : A} (ha : a ≠ 0) :
    ∃ n, span {a} = maximalIdeal A ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha hϖ
  refine ⟨n, ?_⟩
  rw [span_singleton_eq_span_singleton.mpr hn, ← span_singleton_pow, ← hϖ.maximalIdeal_eq]

-- pin: pow_maximalIdeal_ne_of_lt (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:120)
theorem pow_maximalIdeal_ne_of_lt {n k : ℕ} (h : n < k) :
    (maximalIdeal A) ^ n ≠ maximalIdeal A ^ k := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  intro heq
  have hmem : ϖ ^ n ∈ maximalIdeal A ^ k := by
    rw [← heq, hϖ.maximalIdeal_eq, span_singleton_pow]
    exact mem_span_singleton_self _
  rw [hϖ.maximalIdeal_eq, span_singleton_pow, mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  have h1 : (1 : A) = ϖ ^ (k - n) * c := by
    refine mul_left_cancel₀ (pow_ne_zero n hϖ.ne_zero) ?_
    rw [mul_one, ← mul_assoc, ← pow_add]
    rw [show n + (k - n) = k from by omega]
    exact hc
  have hkn : k - n - 1 + 1 = k - n := by omega
  exact hϖ.not_isUnit (isUnit_of_dvd_one ⟨ϖ ^ (k - n - 1) * c, by
    rw [h1, ← mul_assoc, ← pow_succ', hkn]⟩)

-- pin: pow_maximalIdeal_injective (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:138)
theorem pow_maximalIdeal_injective {n k : ℕ}
    (h : (maximalIdeal A) ^ n = maximalIdeal A ^ k) : n = k := by
  rcases Nat.lt_trichotomy n k with hlt | heq | hgt
  · exact absurd h (pow_maximalIdeal_ne_of_lt A hlt)
  · exact heq
  · exact absurd h.symm (pow_maximalIdeal_ne_of_lt A hgt)

open Classical in
-- pin: ordA (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:146)
noncomputable def ordA (a : A) : ℕ :=
  if h : a = 0 then 0 else (exists_span_eq_pow A h).choose

-- pin: ordA_span (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:149)
theorem ordA_span {a : A} (ha : a ≠ 0) :
    span {a} = maximalIdeal A ^ ordA A a := by
  classical
  rw [ordA, dite_eq_right ha]
  exact (exists_span_eq_pow A ha).choose_spec

-- pin: ordA_unique (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:155)
theorem ordA_unique {a : A} (ha : a ≠ 0) {n : ℕ}
    (h : span {a} = maximalIdeal A ^ n) : ordA A a = n :=
  pow_maximalIdeal_injective A ((ordA_span A ha).symm.trans h)

-- pin: ordA_mul (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:159)
theorem ordA_mul {a b : A} (ha : a ≠ 0) (hb : b ≠ 0) :
    ordA A (a * b) = ordA A a + ordA A b := by
  refine ordA_unique A (mul_ne_zero ha hb) ?_
  rw [← span_singleton_mul_span_singleton, ordA_span A ha, ordA_span A hb, pow_add]

open Classical in
-- pin: ordZ (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:165)
noncomputable def ordZ (x : Lˣ) : ℤ :=
  if h : (x : L) ∈ A then (ordA A ⟨(x : L), h⟩ : ℤ)
  else -(ordA A ⟨((x⁻¹ : Lˣ) : L), by
    rw [Units.val_inv_eq_inv_val]
    exact (A.mem_or_inv_mem (x : L)).resolve_left h⟩ : ℤ)

omit [IsDiscreteValuationRing ↥A] in
-- pin: coe_mk_ne_zero (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:172)
theorem coe_mk_ne_zero (x : Lˣ) {y : L} (hy : y ∈ A) (hxy : y = (x : L)) :
    (⟨y, hy⟩ : A) ≠ 0 := by
  intro h0
  have : y = 0 := congrArg Subtype.val h0
  exact x.ne_zero (hxy ▸ this)

-- pin: ordZ_spec (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:178)
theorem ordZ_spec {x : Lˣ} {a b : A} (ha : a ≠ 0) (hb : b ≠ 0)
    (hx : (x : L) * (b : L) = (a : L)) : ordZ A x = (ordA A a : ℤ) - ordA A b := by
  classical
  by_cases h : (x : L) ∈ A
  · rw [ordZ, dite_eq_left h]
    have hab : (⟨(x : L), h⟩ : A) * b = a := Subtype.ext hx
    have hmul := ordA_mul A (coe_mk_ne_zero A x h rfl) hb
    rw [hab] at hmul
    omega
  · rw [ordZ, dite_eq_right h]
    set c : A := ⟨((x⁻¹ : Lˣ) : L), by
      rw [Units.val_inv_eq_inv_val]
      exact (A.mem_or_inv_mem (x : L)).resolve_left h⟩ with hc
    have hcx : (c : A) ≠ 0 := coe_mk_ne_zero A x⁻¹ _ rfl
    have hab : a * c = b := by
      refine Subtype.ext ?_
      push_cast
      have hcL : (c : L) = ((x : L))⁻¹ := by rw [hc]; exact Units.val_inv_eq_inv_val x
      rw [hcL, ← hx, mul_comm ((x : L)) ((b : L)), mul_assoc,
        mul_inv_cancel₀ x.ne_zero, mul_one]
    have hmul := ordA_mul A ha hcx
    rw [hab] at hmul
    omega

omit [IsDiscreteValuationRing ↥A] in
-- pin: exists_rep (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:203)
theorem exists_rep (x : Lˣ) :
    ∃ a b : A, a ≠ 0 ∧ b ≠ 0 ∧ (x : L) * (b : L) = (a : L) := by
  rcases A.mem_or_inv_mem (x : L) with h | h
  · exact ⟨⟨(x : L), h⟩, 1, coe_mk_ne_zero A x h rfl, one_ne_zero, by
      push_cast; exact mul_one _⟩
  · refine ⟨1, ⟨((x⁻¹ : Lˣ) : L), by rwa [Units.val_inv_eq_inv_val]⟩,
      one_ne_zero, coe_mk_ne_zero A x⁻¹ _ rfl, ?_⟩
    show (x : L) * ((x⁻¹ : Lˣ) : L) = (1 : L)
    exact x.mul_inv

-- pin: ord (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:213)
noncomputable def ord : Additive Lˣ →+ ℤ where
  toFun x := ordZ A x.toMul
  map_zero' := by
    show ordZ A (1 : Lˣ) = 0
    have h1 := ordZ_spec A (x := 1) (a := 1) (b := 1) one_ne_zero one_ne_zero
      (by rw [Units.val_one, one_mul])
    rw [h1]
    ring
  map_add' x y := by
    obtain ⟨a, b, ha, hb, hx⟩ := exists_rep A x.toMul
    obtain ⟨c, d, hc, hd, hy⟩ := exists_rep A y.toMul
    have hxy : (((x + y).toMul : Lˣ) : L) * ((b * d : A) : L) = ((a * c : A) : L) := by
      push_cast
      calc (x.toMul : L) * (y.toMul : L) * ((b : L) * (d : L))
          = ((x.toMul : L) * (b : L)) * ((y.toMul : L) * (d : L)) := by ring
        _ = (a : L) * (c : L) := by rw [hx, hy]
    show ordZ A (x + y).toMul = ordZ A x.toMul + ordZ A y.toMul
    rw [ordZ_spec A (mul_ne_zero ha hc) (mul_ne_zero hb hd) hxy,
      ordZ_spec A ha hb hx, ordZ_spec A hc hd hy, ordA_mul A ha hc, ordA_mul A hb hd]
    push_cast
    ring

-- pin: ord_spec (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:235)
theorem ord_spec {x : Lˣ} {a b : A} (ha : a ≠ 0) (hb : b ≠ 0)
    (hx : (x : L) * (b : L) = (a : L)) {na nb : ℕ}
    (hna : span {a} = maximalIdeal A ^ na) (hnb : span {b} = maximalIdeal A ^ nb) :
    ord A (.ofMul x) = (na : ℤ) - nb := by
  have := ordZ_spec A ha hb hx
  rw [ordA_unique A ha hna, ordA_unique A hb hnb] at this
  exact this

-- pin: ord_ofMul_of_mem (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:243)
theorem ord_ofMul_of_mem {x : Lˣ} (hx : (x : L) ∈ A) {n : ℕ}
    (hspan : span {(⟨(x : L), hx⟩ : A)} = maximalIdeal A ^ n) :
    ord A (.ofMul x) = n := by
  have h := ord_spec A (coe_mk_ne_zero A x hx rfl) one_ne_zero
    (b := 1) (by push_cast; exact mul_one _) hspan
    (by rw [span_singleton_eq_top.mpr isUnit_one, pow_zero, one_eq_top])
  simpa using h

-- pin: ord_ofMul_mk0_of_irreducible (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:251)
theorem ord_ofMul_mk0_of_irreducible {ϖ : A} (hϖ : Irreducible ϖ)
    (h0 : ((ϖ : A) : L) ≠ 0) :
    ord A (.ofMul (Units.mk0 ((ϖ : A) : L) h0)) = 1 := by
  refine ord_ofMul_of_mem A (x := Units.mk0 ((ϖ : A) : L) h0) (ϖ : A).2 ?_
  have hmk : (⟨((Units.mk0 ((ϖ : A) : L) h0 : Lˣ) : L), (ϖ : A).2⟩ : A) = ϖ :=
    Subtype.ext rfl
  rw [hmk, pow_one, ← hϖ.maximalIdeal_eq]

-- pin: ord_eq_zero_iff (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:259)
theorem ord_eq_zero_iff (x : Lˣ) :
    ord A (.ofMul x) = 0 ↔ x ∈ (Units.map (A.subtype.toMonoidHom)).range := by
  constructor
  · intro h
    obtain ⟨a, b, ha, hb, hx⟩ := exists_rep A x
    have hspec : ordZ A x = (ordA A a : ℤ) - ordA A b := ordZ_spec A ha hb hx
    have h0 : ordZ A x = 0 := h
    have hord : ordA A a = ordA A b := by omega
    have hassoc : Associated a b := span_singleton_eq_span_singleton.mp
      (by rw [ordA_span A ha, ordA_span A hb, hord])
    obtain ⟨u, hu⟩ := hassoc
    have haL : (a : L) ≠ 0 := fun hz => ha (Subtype.ext hz)
    have hab : (a : L) * (((u : Aˣ) : A) : L) = (b : L) := by
      exact_mod_cast congrArg (fun s : A => (s : L)) hu
    have h1 : (x : L) * (((u : Aˣ) : A) : L) = 1 := by
      have h2 : (x : L) * ((a : L) * (((u : Aˣ) : A) : L)) = (a : L) := by
        rw [hab]; exact hx
      have h3 : ((x : L) * (((u : Aˣ) : A) : L)) * (a : L) = 1 * (a : L) := by
        rw [one_mul]
        calc ((x : L) * (((u : Aˣ) : A) : L)) * (a : L)
            = (x : L) * ((a : L) * (((u : Aˣ) : A) : L)) := by ring
          _ = (a : L) := h2
      exact mul_right_cancel₀ haL h3
    have huL : (((u : Aˣ) : A) : L) * (((u⁻¹ : Aˣ) : A) : L) = 1 := by
      exact_mod_cast congrArg (fun s : A => (s : L)) u.mul_inv
    have hxinv : (x : L) = ((((u : Aˣ) : A) : L))⁻¹ := eq_inv_of_mul_eq_one_left h1
    have huinv : (((u⁻¹ : Aˣ) : A) : L) = ((((u : Aˣ) : A) : L))⁻¹ :=
      eq_inv_of_mul_eq_one_right huL
    refine ⟨u⁻¹, Units.ext ?_⟩
    show (((u⁻¹ : Aˣ) : A) : L) = (x : L)
    rw [huinv, hxinv]
  · rintro ⟨u, rfl⟩
    have hmem : ((Units.map (A.subtype.toMonoidHom) u : Lˣ) : L) ∈ A := by
      show ((A.subtype) ((u : Aˣ) : A) : L) ∈ A
      exact ((u : Aˣ) : A).2
    have hspan : span {(⟨((Units.map (A.subtype.toMonoidHom) u : Lˣ) : L), hmem⟩ : A)}
        = maximalIdeal A ^ 0 := by
      rw [show (⟨((Units.map (A.subtype.toMonoidHom) u : Lˣ) : L), hmem⟩ : A) = ((u : Aˣ) : A)
        from Subtype.ext rfl]
      rw [span_singleton_eq_top.mpr u.isUnit, pow_zero, one_eq_top]
    have := ord_ofMul_of_mem A hmem hspan
    simpa using this

end IsDiscreteValuationRing
