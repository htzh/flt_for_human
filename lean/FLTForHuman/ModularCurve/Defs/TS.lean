/-
  Layer 0b — `TS`, math/010 §1's central notation.

  `TS K e u` is `j(u q ^ e)`: the `e`-th substituted and `u`-twisted `jq` over a
  `ℚ`-algebra field `K`. It is the object math/010 §1 uses to state the
  conjugates and hence the splitting input.

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

  Assumes `qExpand`/`coeffEmb` (`Defs/Laurent`), `qTwist` (`Defs/Twist`), and
  `jq`/`coeff_jq_neg_one`/`coeff_jq_of_lt` (`Defs/Jq`).
-/
import FLTForHuman.ModularCurve.Defs.Jq
import FLTForHuman.ModularCurve.Defs.Twist

set_option autoImplicit false

noncomputable section

open PowerSeries HahnSeries IntermediateField

namespace ModularCurve

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- `j(u q ^ e)`, the substituted and twisted `j`-invariant over `K`. -/
def TS (K : Type*) [Field K] [Algebra ℚ K] (e : ℕ) [NeZero e] (u : Kˣ) : LaurentSeries K :=
  qExpand K e (qTwist u (coeffEmb K jq))

theorem TS_coeff_mul (e : ℕ) [NeZero e] (u : Kˣ) (n : ℤ) :
    (TS K e u).coeff ((e : ℤ) * n) = ((u ^ n : Kˣ) : K) * algebraMap ℚ K (jq.coeff n) := by
  rw [TS, qExpand_coeff_mul, qTwist_coeff, coeffEmb_coeff]

theorem TS_coeff_of_not_dvd (e : ℕ) [NeZero e] (u : Kˣ) {k : ℤ} (hk : ¬ (e : ℤ) ∣ k) :
    (TS K e u).coeff k = 0 := by
  exact qExpand_coeff_of_not_dvd (R := K) (N := e) _ hk

theorem TS_coeff_neg (e : ℕ) [NeZero e] (u : Kˣ) : (TS K e u).coeff (-(e : ℤ)) = ((u⁻¹ : Kˣ) : K) := by
  have h := TS_coeff_mul (K := K) e u (-1)
  rw [mul_neg_one] at h
  rw [h, coeff_jq_neg_one, map_one, mul_one, zpow_neg_one]

theorem TS_coeff_of_lt (e : ℕ) [NeZero e] (u : Kˣ) {k : ℤ} (hk : k < -(e : ℤ)) : (TS K e u).coeff k = 0 := by
  by_cases hd : (e : ℤ) ∣ k
  · obtain ⟨n, rfl⟩ := hd
    have he : (0 : ℤ) < e := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne e)
    have hn : n < -1 := by
      by_contra hcon
      push Not at hcon
      have : -(e : ℤ) ≤ (e : ℤ) * n := by nlinarith
      exact absurd hk (not_lt.mpr this)
    rw [TS_coeff_mul, coeff_jq_of_lt hn, map_zero, mul_zero]
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

end ModularCurve

end
