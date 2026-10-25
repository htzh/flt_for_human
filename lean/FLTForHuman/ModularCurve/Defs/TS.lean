/-
  Layer 0b — `TS`, math/010 §1's central notation.

  `TS K e u` is `j(u q ^ e)`: the `e`-th substituted and `u`-twisted `jq` over an
  arbitrary field `K`. It is the object math/010 §1 uses to state the conjugates
  and hence the splitting input.

  FLT provenance, pinned `aa2d8b3`:
  `P2M/Sol/S_ModularCurve_functionFieldGeneration.lean` lines 39–101 —
  a **solution** file, not one of the three `Definitions/` files Layer 0a
  transcribed. It was held out of the first layer and decided in for the second;
  the decision is recorded in `logs/ffg-port.md` §8.
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_functionFieldGeneration.lean#L39-L101

  **Recorded divergence (name, not mathematics).** FLT defines `TS` inside a
  `namespace W1` local to each solution file that needs it, so its full FLT name
  there is `ModularCurve.W1.TS`; it is never exported to `ModularCurve`. The work
  order promotes it to a `Definitions`-layer module at `ModularCurve.TS`, which
  is the name `spec/ModularCurveConsumer.lean` checks. The ten statements are
  FLT's verbatim.

  ## The field generality (2026-10-25)

  The pin states `TS` in **two** spellings, and the earlier port carried only the
  narrow one: over a `ℚ`-algebra `K` it is `qExpand K e (qTwist u (coeffEmb K jq))`
  (the FFG files, §8 above), over an arbitrary field it is
  `qExpand K e (qTwist u (jqModC K))` (`S_ModularCurve_PhiGen_splits_prime_of_-
  isPrimitiveRoot.lean` 33–122 and its at-slot twin). The two agree by
  `coeffEmb K jq = jqModC K` (`Defs/JqCoeff.lean`), so only the general one is
  stated here, at the pin's general text — which is what the char-`p` splitting
  and its at-slot roots API need, since neither has an `Algebra ℚ K` to spend.
  The declarations whose *statement* mentions `coeffEmb` (`iota_jqN`,
  `qExpand_qTwist_notMem_range_qExpand`, `coeffMap_TS`) keep their `Algebra ℚ K`
  binder and their pin text, and are the ones the checker matches against the FFG
  sources.

  Assumes `qExpand`/`coeffEmb` (`Defs/Laurent`), `qTwist` (`Defs/Twist`),
  `jq`/`coeff_jq_neg_one`/`coeff_jq_of_lt` (`Defs/Jq`), and
  `jqModC`/`coeffMap_jqModC`/`coeff_jqModC_neg_one`/`order_jqModC`/`coeffEmb_jq`
  (`Defs/JqCoeff`).

  spec-pin: P2M/Sol/S_ModularCurve_PhiGen_splits_prime_of_isPrimitiveRoot.lean
  spec-pin: P2M/Sol/S_ModularCurve_PhiGen_splits_prime_at_slot_of_isPrimitiveRoot.lean
  spec-pin: P2M/Sol/S_ModularCurve_finrank_adjoin_jqN_pow_succ_of_not_mem.lean
  spec-pin: P2M/Sol/S_ModularCurve_jqN_pow_not_mem_adjoin_full.lean
-/
import FLTForHuman.ModularCurve.Defs.Jq
import FLTForHuman.ModularCurve.Defs.JqCoeff
import FLTForHuman.ModularCurve.Defs.Twist

set_option autoImplicit false

noncomputable section

open PowerSeries HahnSeries IntermediateField

namespace ModularCurve

variable {K : Type*} [Field K]

/-- `j(u q ^ e)`, the substituted and twisted `j`-invariant over `K`. -/
def TS (K : Type*) [Field K] (e : ℕ) [NeZero e] (u : Kˣ) : LaurentSeries K :=
  qExpand K e (qTwist u (jqModC K))

theorem TS_coeff_mul (e : ℕ) [NeZero e] (u : Kˣ) (n : ℤ) :
    (TS K e u).coeff ((e : ℤ) * n) = ((u ^ n : Kˣ) : K) * (jqModC K).coeff n := by
  rw [TS, qExpand_coeff_mul, qTwist_coeff]

theorem TS_coeff_of_not_dvd (e : ℕ) [NeZero e] (u : Kˣ) {k : ℤ} (hk : ¬ (e : ℤ) ∣ k) :
    (TS K e u).coeff k = 0 := by
  exact qExpand_coeff_of_not_dvd (R := K) (N := e) _ hk

theorem TS_coeff_neg (e : ℕ) [NeZero e] (u : Kˣ) : (TS K e u).coeff (-(e : ℤ)) = ((u⁻¹ : Kˣ) : K) := by
  have h := TS_coeff_mul (K := K) e u (-1)
  rw [mul_neg_one] at h
  rw [h, coeff_jqModC_neg_one K, mul_one, zpow_neg_one]

theorem TS_coeff_of_lt (e : ℕ) [NeZero e] (u : Kˣ) {k : ℤ} (hk : k < -(e : ℤ)) : (TS K e u).coeff k = 0 := by
  by_cases hd : (e : ℤ) ∣ k
  · obtain ⟨n, rfl⟩ := hd
    have he : (0 : ℤ) < e := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne e)
    have hn : n < -1 := by
      by_contra hcon
      push Not at hcon
      have : -(e : ℤ) ≤ (e : ℤ) * n := by nlinarith
      exact absurd hk (not_lt.mpr this)
    have h0 : (jqModC K).coeff n = 0 := by
      apply HahnSeries.coeff_eq_zero_of_lt_order
      rw [order_jqModC]
      exact hn
    rw [TS_coeff_mul, h0, mul_zero]
  · exact TS_coeff_of_not_dvd e u hd

theorem TS_ne_zero (e : ℕ) [NeZero e] (u : Kˣ) : TS K e u ≠ 0 := by
  intro h
  have := TS_coeff_neg (K := K) e u
  rw [h, HahnSeries.coeff_zero] at this
  exact (u⁻¹).ne_zero this.symm

theorem TS_injective {e e' : ℕ} [NeZero e] [NeZero e'] {u u' : Kˣ} (h : TS K e u = TS K e' u') :
    e = e' ∧ u = u' := by
  have key : ∀ {a a' : ℕ} [NeZero a] [NeZero a'] {v v' : Kˣ}, TS K a v = TS K a' v' → a ≤ a' := by
    intro a a' _ _ v v' hh
    by_contra hlt
    push Not at hlt
    have h1 := TS_coeff_neg (K := K) a v
    have hlt' : (-(a : ℤ)) < -(a' : ℤ) := by
      have : (a' : ℤ) < a := by exact_mod_cast hlt
      omega
    have h2 : (TS K a' v').coeff (-(a : ℤ)) = 0 := TS_coeff_of_lt a' v' hlt'
    rw [← hh, h1] at h2
    exact (v⁻¹).ne_zero h2
  have hee : e = e' := le_antisymm (key h) (key h.symm)
  subst hee
  refine ⟨rfl, ?_⟩
  have h1 := TS_coeff_neg (K := K) e u
  rw [h, TS_coeff_neg] at h1
  exact (inv_injective (Units.val_injective h1)).symm

theorem qTwist_TS (v : Kˣ) (e : ℕ) [NeZero e] (u : Kˣ) : qTwist v (TS K e u) = TS K e (v ^ (e : ℤ) * u) := by
  rw [TS, qTwist_qExpand, qTwist_qTwist]; rfl

theorem qExpand_TS (m e : ℕ) [NeZero m] [NeZero e] (u : Kˣ) : qExpand K m (TS K e u) = TS K (m * e) u := by
  rw [TS, qExpand_qExpand]; rfl

theorem TS_congr {e e' : ℕ} [NeZero e] [NeZero e'] (h : e = e') (u : Kˣ) : TS K e u = TS K e' u := by
  subst h; rfl

/-- Twisting by a unit `ζ` with `ζ ^ p = 1` cycles the `p` finite `TS` roots:
`qTwist ζ (TS K 1 (ζ ^ b)) = TS K 1 (ζ ^ ((b + 1) % p))`. -/
theorem qTwist_TS_one_cycle (ζ : Kˣ) {p : ℕ} (hζp : ζ ^ p = 1) (b : ℕ) :
    qTwist ζ (TS K 1 (ζ ^ b)) = TS K 1 (ζ ^ ((b + 1) % p)) := by
  rw [qTwist_TS]
  congr 1
  have : ζ ^ ((1 : ℕ) : ℤ) * ζ ^ b = ζ ^ (b + 1) := by rw [zpow_natCast, pow_one, pow_succ']
  rw [this]
  conv_lhs => rw [← Nat.mod_add_div (b + 1) p, pow_add, pow_mul, hζp, one_pow, mul_one]

/-- Twisting then expanding a `TS` value is a `TS` value at the product level
with the twist picked up by `u ^ m`. -/
theorem qExpand_qTwist_TS (e : ℕ) [NeZero e] (u : Kˣ) (m : ℕ) [NeZero m] (w : Kˣ) :
    qExpand K e (qTwist u (TS K m w)) = TS K (e * m) (u ^ (m : ℤ) * w) := by
  rw [qTwist_TS, qExpand_TS]

/-! ## The `TS` spellings of `jqModC` / `jqNModC`

`j(q^d)` and `j(q)` read as `TS` values. The pin states them in the char-`p`
splitting files (105–116), where they are the bridge between the `jqModC`-flavoured
slot and the `TS`-flavoured one; the `finrank_adjoin_jqNModC_*`/`jqNModC_*` nodes are
their consumers. They are general in the field, like `TS` since 2026-10-25. -/

theorem jqModC_eq_TS : jqModC K = TS K 1 1 := by
  rw [TS, qTwist_one_apply, qExpand_one_apply]

theorem jqNModC_eq_TS (d : ℕ) [NeZero d] : jqNModC K d = TS K d 1 := by
  rw [jqNModC, TS, qTwist_one_apply]

theorem qExpand_jqNModC (A d : ℕ) [NeZero A] [NeZero d] :
    qExpand K A (jqNModC K d) = TS K (A * d) 1 := by
  rw [jqNModC_eq_TS, qExpand_TS]

theorem qExpand_jqModC_eq_TS (A : ℕ) [NeZero A] : qExpand K A (jqModC K) = TS K A 1 := by
  rw [TS, qTwist_one_apply]

/-! ## The `ℚ`-algebra members of the prelude

These three statements mention `coeffEmb` itself, so they keep the `Algebra ℚ K`
binder of the pin's FFG files (and their text there), even though `TS` no longer
does. `iota_jqN` is the bridge from `coeffEmb (qExpand ℚ N (jqN d))` to `TS`;
`qExpand_qTwist_notMem_range_qExpand` says a twisted `j`-slice misses a
non-matching `qExpand` range.

Verbatim from `P2M/Sol/S_ModularCurve_jqN_prime_not_mem_full.lean` lines 102–105
and `P2M/Sol/S_ModularCurve_jqN_pow_not_mem_adjoin_full.lean` lines 431–442. -/

section AlgHom

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- `coeffEmb K (qExpand ℚ N (jqN d)) = j(q ^ (N * d))`: the `TS` form of the
`N`-substituted `j(q ^ d)`. -/
theorem iota_jqN (N d : ℕ) [NeZero N] [NeZero d] :
    coeffEmb K (qExpand ℚ N (jqN d)) = TS K (N * d) 1 := by
  rw [jqN, coeffEmb_qExpand, coeffEmb_qExpand, qExpand_qExpand, coeffEmb_jq, TS,
    qTwist_one_apply]

/-- A twisted `j`-slice at exponent `e` misses the `qExpand K r` range when
`r ∤ e`: the `q ^ (-e)` coefficient of the slice is the nonzero `w⁻¹`, while
every element of the range has zero there. -/
theorem qExpand_qTwist_notMem_range_qExpand {r e : ℕ} [NeZero r] [NeZero e]
    (hre : ¬ ((r : ℤ) ∣ (e : ℤ))) (w : Kˣ) :
    qExpand K e (qTwist w (coeffEmb K jq)) ∉ (qExpand K r).range := by
  intro hmem
  obtain ⟨z, hz⟩ := RingHom.mem_range.mp hmem
  have h1 : (qExpand K e (qTwist w (coeffEmb K jq))).coeff (-(e : ℤ)) = ((w⁻¹ : Kˣ) : K) := by
    rw [coeffEmb_jq]
    exact TS_coeff_neg e w
  have h2 : (qExpand K r z).coeff (-(e : ℤ)) = 0 :=
    qExpand_coeff_of_not_dvd r z (by rwa [dvd_neg])
  rw [hz, h1] at h2
  exact (w⁻¹ : Kˣ).ne_zero h2

end AlgHom

/-! ## T16 — `coeffMap` against `TS`

FLT repeats this transport lemma across 14 files (the 2026-09-22 bridge audit);
it lives here, beside `TS`, because it mentions `TS`. Statement verbatim from
`S_ModularCurve_finrank_adjoin_jqN_pow_succ_of_not_mem.lean` (and
`S_ModularCurve_PhiGen_splits_of_prime.lean`). -/

section CoeffMapTS

variable {K₀ : Type*} [Field K₀] [Algebra ℚ K₀]

variable [Algebra ℚ K]

/-- `coeffMap` commutes with `TS`: pushing coefficients through a `ℚ`-algebra
homomorphism carries `TS K₀ e u` to `TS K e (Units.map σ u)`. -/
theorem coeffMap_TS (σ : K₀ →ₐ[ℚ] K) (e : ℕ) [NeZero e] (u : K₀ˣ) :
    coeffMap (σ : K₀ →+* K) (TS K₀ e u) = TS K e (Units.map (σ : K₀ →+* K).toMonoidHom u) := by
  rw [TS, TS, coeffMap_qExpand,
    coeffMap_qTwist σ u (Units.map (σ : K₀ →+* K).toMonoidHom u) rfl,
    coeffMap_jqModC]

end CoeffMapTS

end ModularCurve

end
