/-
  The unramified Whittaker model: the Hecke recursion sequence and its Euler polynomial.

  Three rows of the local unramified Whittaker model (`RepTheory/LocalLanglands/UnramifiedWhittaker.lean`
  carries `heckeRecursionSeq`, `torusFactor`, `placeEmbed`, `diagZ`, `unipotent` and the rest of the
  local dictionary):

  * `apply_mul_placeEmbed_diagZ_eq_mul_torusFactor`: the diagonal `placeEmbed v * diagZ π m` acts on the
    local component by `torusFactor N λ ω m` — the local Hecke operator's eigenvalue.
  * `summable_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow`: the pointwise product of two Hecke
    recursion sequences, with a power, is summable.
  * `tsum_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow_mul_rsEulerPoly_eval`: that sum is the Rankin–
    Selberg Euler polynomial at the product of the parameters — the identity that turns the local
    convolution into the Euler factor.

  ## The surface: eleven declarations, against the wire's twenty-three

  The three pins carry 23 *public* declarations — 1 + 11 + 11, `spec/statement_db.py` being the authority:
  `python3 lean/spec/check_port.py --force` on this module reads `11 ok, 0 mismatch, 0 missing, 0 own,
  0 kw`, and `tools/deps/scaffold_audit.py` reads `complete` over those 23. The difference is the pin's
  own duplication, not an omission:

  * the second and third pins share a byte-identical `namespace RS9` engine block (`:12-198` in both;
    `diff` empty): 10 declarations, proved twice in the pin, declared once here;
  * every pin ends in a `solution` wrapper that restates its row (`…diagZ…:348`, `…summable…:200`,
    `…tsum…:200`): the port's row *is* that statement, which is what the audit reports as `FOLDED`;
  * the first pin's `solution` (`:348`) and its `private` engine (`:300`) are the same statement; the
    port's row carries it, at the row's name.

  So 23 − 10 (the third pin's copies) − 2 (the analytic `solution`s) − 1 (the first pin's `solution`) = 10
  distinct statements, one of which is not in the `RS9` block: 11 declarations = 8 engines + 3 rows.
  (The work order quoted 26 for this module; that count read three `@[scoped simp] private theorem`s as
  public. Target corrected to `11 ok` + audit `complete` — FR-0226.)

  The shared engine block is homed in the subject namespace `EulerFactor`: the pin's `RS9` is a
  search-stage label, not mathematics, and "no tokens in names" drops it.

  ## The private engine

  The first pin's engine block (`…diagZ…:18-337`) is `private` in the pin, and is transcribed as such
  (13 declarations, the row being the pin's `:300`). Four declarations of that block have no consumer in
  the pin either, and `tools/deps/move_dead.py` reports them dead here, so they are dropped:
  `norm_heckeRecursionSeq_le` (`:51`), `tsum_heckeRecursionSeq_mul_heckePoly` (`:82`),
  `summable_heckeRecursionSeq` (`:117`, which those two feed) and `placeEmbed_mul_placeEmbed_comm`
  (`:283`). The norm bound survives: the public `EulerFactor.norm_pow_mul_heckeRecursionSeq_le` is its
  `N ^ m`-scaled form. The other three have no consumer anywhere (all are `private` in the pin), so
  dropping them removes nothing reachable.

  ## The heartbeat probe (recorded, not installed)

  No `set_option maxHeartbeats` in this module (playbook §3.5, FR-0225). Probe, run from `lean/`:

    lake env lean -DautoImplicit=false -DmaxHeartbeats=N FLTForHuman/RepTheory/LocalLanglands/WhittakerRecursion.lean

  silent at N = 10000, fails at N/2 = 5000 (a deterministic timeout at `whnf`, attributed to the
  module's largest declaration, `EulerFactor.tsum_mul_mul_pow_mul_eval_rsEulerPoly`).

  Transcribed from the three `S_` files below (pinned `aa2d8b3`, 380 + 205 + 207 lines).

  spec-pin: P2M/Sol/S_UnramifiedWhittaker_apply_mul_placeEmbed_diagZ_eq_mul_torusFactor.lean
  spec-pin: P2M/Sol/S_UnramifiedWhittaker_summable_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow.lean
  spec-pin: P2M/Sol/S_UnramifiedWhittaker_tsum_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow_mul_rsEulerPoly_eval.lean
-/
import FLTForHuman.RepTheory.LocalLanglands.UnramifiedWhittaker
import FLTForHuman.LanglandsTunnell.RankinSelberg.Euler
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

noncomputable section

open Polynomial Matrix
open IsDedekindDomain NumberField AdelicDock
open scoped Classical

namespace UnramifiedWhittaker

/-! ## The Rankin–Selberg Euler recursion

The pin's in-file engine block (`namespace RS9`, identical in its second and third files), minus the two
declarations that are rows: `tsum_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow_mul_rsEulerPoly_eval`
and `summable_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow`, which are declared once, at the row's
name, outside this namespace. -/

namespace EulerFactor

section Algebra

variable {R : Type*} [CommRing R]

theorem mul_mul_recursion_of_recursion (s p s' p' : R) (h h' : ℕ → R)
    (hh : ∀ m, h (m + 2) = s * h (m + 1) - p * h m)
    (hh' : ∀ m, h' (m + 2) = s' * h' (m + 1) - p' * h' m) (m : ℕ) :
    h (m + 4) * h' (m + 4) =
      s * s' * (h (m + 3) * h' (m + 3))
        - (s ^ 2 * p' + s' ^ 2 * p - 2 * p * p') * (h (m + 2) * h' (m + 2))
        + s * s' * p * p' * (h (m + 1) * h' (m + 1))
        - p ^ 2 * p' ^ 2 * (h m * h' m) := by
  have e2 : h (m + 2) = s * h (m + 1) - p * h m := hh m
  have e3 : h (m + 3) = s * h (m + 2) - p * h (m + 1) := hh (m + 1)
  have e4 : h (m + 4) = s * h (m + 3) - p * h (m + 2) := hh (m + 2)
  have f2 : h' (m + 2) = s' * h' (m + 1) - p' * h' m := hh' m
  have f3 : h' (m + 3) = s' * h' (m + 2) - p' * h' (m + 1) := hh' (m + 1)
  have f4 : h' (m + 4) = s' * h' (m + 3) - p' * h' (m + 2) := hh' (m + 2)
  rw [e4, f4, e3, f3, e2, f2]
  ring

theorem rsEulerPoly_zero_eq_prod (x₁ x₂ y₁ y₂ : R) :
    LanglandsTunnell.RankinSelberg.rsEulerPoly (x₁ + x₂) (x₁ * x₂) (y₁ + y₂) (y₁ * y₂) 0 =
      (C 1 - C (x₁ * y₁) * X) * (C 1 - C (x₁ * y₂) * X) *
        ((C 1 - C (x₂ * y₁) * X) * (C 1 - C (x₂ * y₂) * X)) := by
  simp only [LanglandsTunnell.RankinSelberg.rsEulerPoly, map_add, map_sub, map_neg, map_mul, map_pow,
    map_ofNat, map_one, map_zero]
  ring

theorem eval_rsEulerPoly_zero (s p s' p' x : R) :
    (LanglandsTunnell.RankinSelberg.rsEulerPoly s p s' p' 0).eval x =
      1 - s * s' * x + (s ^ 2 * p' + p * s' ^ 2 - 2 * p * p') * x ^ 2
        - s * p * s' * p' * x ^ 3 + p ^ 2 * p' ^ 2 * x ^ 4 := by
  simp only [LanglandsTunnell.RankinSelberg.rsEulerPoly, eval_add, eval_mul, eval_C, eval_X, eval_pow]
  ring

theorem eval_rsEulerPoly_scale (c a b e₁ e₂ e₃ x : R) :
    (LanglandsTunnell.RankinSelberg.rsEulerPoly (c * a) (c ^ 2 * b) e₁ e₂ e₃).eval x =
      (LanglandsTunnell.RankinSelberg.rsEulerPoly a b e₁ e₂ e₃).eval (c * x) := by
  simp only [LanglandsTunnell.RankinSelberg.rsEulerPoly, eval_add, eval_mul, eval_C, eval_X, eval_pow]
  ring

end Algebra

section Analytic

theorem tsum_mul_mul_pow_mul_eval_rsEulerPoly (s p s' p' : ℂ) (h h' : ℕ → ℂ)
    (h0 : h 0 = 1) (h1 : h 1 = s) (h0' : h' 0 = 1) (h1' : h' 1 = s')
    (hh : ∀ m, h (m + 2) = s * h (m + 1) - p * h m)
    (hh' : ∀ m, h' (m + 2) = s' * h' (m + 1) - p' * h' m)
    (x : ℂ) (hsum : Summable fun m : ℕ => h m * h' m * x ^ m) :
    (∑' m : ℕ, h m * h' m * x ^ m) *
        (LanglandsTunnell.RankinSelberg.rsEulerPoly s p s' p' 0).eval x =
      1 - p * p' * x ^ 2 := by
  set c : ℕ → ℂ := fun m => h m * h' m * x ^ m with hc
  have tail : ∀ k : ℕ, ∑' m, c (m + k) = (∑' m, c m) - ∑ i ∈ Finset.range k, c i := by
    intro k
    have := hsum.sum_add_tsum_nat_add k
    linear_combination this
  have hs : ∀ k : ℕ, Summable fun m => c (m + k) := fun k => (summable_nat_add_iff k).mpr hsum
  have hrec : ∀ m, c (m + 4) = s * s' * x * c (m + 3) - (s ^ 2 * p' + s' ^ 2 * p - 2 * p * p') * x ^ 2 * c (m + 2)
      + s * s' * p * p' * x ^ 3 * c (m + 1) - p ^ 2 * p' ^ 2 * x ^ 4 * c m := by
    intro m
    have key := mul_mul_recursion_of_recursion s p s' p' h h' hh hh' m
    simp only [hc]
    rw [key]
    ring
  have T4 : ∑' m, c (m + 4) =
      s * s' * x * ∑' m, c (m + 3) - (s ^ 2 * p' + s' ^ 2 * p - 2 * p * p') * x ^ 2 * ∑' m, c (m + 2)
        + s * s' * p * p' * x ^ 3 * ∑' m, c (m + 1) - p ^ 2 * p' ^ 2 * x ^ 4 * ∑' m, c m := by
    rw [show (fun m => c (m + 4)) = fun m =>
        s * s' * x * c (m + 3) - (s ^ 2 * p' + s' ^ 2 * p - 2 * p * p') * x ^ 2 * c (m + 2)
          + s * s' * p * p' * x ^ 3 * c (m + 1) - p ^ 2 * p' ^ 2 * x ^ 4 * c m from funext hrec]
    rw [((((hs 3).mul_left _).sub ((hs 2).mul_left _)).add ((hs 1).mul_left _)).tsum_sub
        (hsum.mul_left _)]
    rw [(((hs 3).mul_left _).sub ((hs 2).mul_left _)).tsum_add ((hs 1).mul_left _)]
    rw [((hs 3).mul_left _).tsum_sub ((hs 2).mul_left _)]
    rw [tsum_mul_left, tsum_mul_left, tsum_mul_left, tsum_mul_left]
  rw [tail 4, tail 3, tail 2, tail 1] at T4
  have h2 : h 2 = s * s - p := by rw [hh 0, h1, h0]; ring
  have h3 : h 3 = s * (s * s - p) - p * s := by rw [hh 1, h2, h1]
  have h2' : h' 2 = s' * s' - p' := by rw [hh' 0, h1', h0']; ring
  have h3' : h' 3 = s' * (s' * s' - p') - p' * s' := by rw [hh' 1, h2', h1']
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hc, h0, h1, h2, h3, h0', h1', h2', h3',
    zero_add, pow_zero, pow_one] at T4
  rw [eval_rsEulerPoly_zero]
  linear_combination T4

theorem pow_mul_heckeRecursionSeq_rec (N lam om : ℂ) (hN : N ≠ 0) :
    (N ^ 0 * heckeRecursionSeq N lam om 0 = 1) ∧ (N ^ 1 * heckeRecursionSeq N lam om 1 = lam) ∧
      ∀ m, N ^ (m + 2) * heckeRecursionSeq N lam om (m + 2) =
        lam * (N ^ (m + 1) * heckeRecursionSeq N lam om (m + 1))
          - N * om * (N ^ m * heckeRecursionSeq N lam om m) := by
  refine ⟨by simp [heckeRecursionSeq], by rw [heckeRecursionSeq, pow_one]; field_simp, fun m => ?_⟩
  rw [heckeRecursionSeq]
  field_simp
  ring

theorem conj_heckeRecursionSeq (N lam om : ℂ) (m : ℕ) :
    (starRingEnd ℂ) (heckeRecursionSeq N lam om m) =
      heckeRecursionSeq ((starRingEnd ℂ) N) ((starRingEnd ℂ) lam) ((starRingEnd ℂ) om) m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m, ih with
    | 0, _ => simp [heckeRecursionSeq]
    | 1, _ => simp [heckeRecursionSeq]
    | m + 2, ih =>
      rw [heckeRecursionSeq, heckeRecursionSeq, map_div₀, map_sub, map_mul, map_mul,
        ih (m + 1) (by omega), ih m (by omega)]

theorem norm_pow_mul_heckeRecursionSeq_le (N lam om : ℂ) (hN : N ≠ 0) (m : ℕ) :
    ‖N ^ m * heckeRecursionSeq N lam om m‖ ≤ (max 1 (‖lam‖ + ‖N * om‖)) ^ m := by
  obtain ⟨a0, a1, ha⟩ := pow_mul_heckeRecursionSeq_rec N lam om hN
  set M := max 1 (‖lam‖ + ‖N * om‖) with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hlam : ‖lam‖ ≤ M := le_trans (le_add_of_nonneg_right (norm_nonneg _)) (le_max_right _ _)
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m, ih with
    | 0, _ => simp [heckeRecursionSeq]
    | 1, _ => rw [a1, pow_one]; exact hlam
    | m + 2, ih =>
      rw [ha m]
      have i1 := ih (m + 1) (by omega)
      have i0 := ih m (by omega)
      calc ‖lam * (N ^ (m + 1) * heckeRecursionSeq N lam om (m + 1)) -
              N * om * (N ^ m * heckeRecursionSeq N lam om m)‖
          ≤ ‖lam‖ * M ^ (m + 1) + ‖N * om‖ * M ^ m := by
            refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
            · rw [norm_mul]; exact mul_le_mul_of_nonneg_left i1 (norm_nonneg _)
            · rw [norm_mul]; exact mul_le_mul_of_nonneg_left i0 (norm_nonneg _)
        _ ≤ ‖lam‖ * M ^ (m + 1) + ‖N * om‖ * M ^ (m + 1) := by
            have hp : M ^ m ≤ M ^ (m + 1) := pow_le_pow_right₀ hM1 (Nat.le_succ m)
            have := mul_le_mul_of_nonneg_left hp (norm_nonneg (N * om))
            linarith
        _ = (‖lam‖ + ‖N * om‖) * M ^ (m + 1) := by ring
        _ ≤ M * M ^ (m + 1) := by gcongr; exact le_max_right _ _
        _ = M ^ (m + 2) := by ring

end Analytic

end EulerFactor

/-! ## The local recursion: the coset recursion and the torus value

The pin's first file carries its engine block in `namespace UnramifiedWhittaker` (`…diagZ…:18-337`),
all of it `private` but for the `solution` at `:348`. It is transcribed here, private as the pin has it,
with two adjustments:

* the pin's `apply_mul_placeEmbed_diagZ_eq_mul_torusFactor` (`:300`) is the row of this module and is
  declared, public, in the last section — its `solution` at `:348` restates it and is the same statement,
  so nothing is duplicated;
* four declarations of the pin's block have no consumer *in the pin* either, and `move_dead.py` reports
  them dead in the port: `norm_heckeRecursionSeq_le` (`:51`), `tsum_heckeRecursionSeq_mul_heckePoly`
  (`:82`), `summable_heckeRecursionSeq` (`:117`, which is what the previous two feed) and
  `placeEmbed_mul_placeEmbed_comm` (`:283`). They are dropped; the norm bound survives as the public
  `EulerFactor.norm_pow_mul_heckeRecursionSeq_le`, its `N ^ m`-scaled form. -/

section Recursion

variable (N lam om : ℂ)

@[scoped simp] private theorem heckeRecursionSeq_zero : heckeRecursionSeq N lam om 0 = 1 := rfl

@[scoped simp] private theorem heckeRecursionSeq_one : heckeRecursionSeq N lam om 1 = lam / N := rfl

private theorem heckeRecursionSeq_add_two (m : ℕ) :
    heckeRecursionSeq N lam om (m + 2) =
      (lam * heckeRecursionSeq N lam om (m + 1) - om * heckeRecursionSeq N lam om m) / N := rfl

variable {N lam om}

private theorem eq_mul_heckeRecursionSeq (hN : N ≠ 0) {c : ℕ → ℂ} (h1 : N * c 1 = lam * c 0)
    (h2 : ∀ m, N * c (m + 2) = lam * c (m + 1) - om * c m) (m : ℕ) :
    c m = c 0 * heckeRecursionSeq N lam om m := by
  suffices H : c m = c 0 * heckeRecursionSeq N lam om m ∧
      c (m + 1) = c 0 * heckeRecursionSeq N lam om (m + 1) from H.1
  induction m with
  | zero =>
    refine ⟨by simp [heckeRecursionSeq_zero], ?_⟩
    rw [zero_add, heckeRecursionSeq_one]
    field_simp
    linear_combination h1
  | succ m ih =>
    refine ⟨ih.2, ?_⟩
    have h := h2 m
    rw [ih.1, ih.2] at h
    rw [show m + 1 + 1 = m + 2 from rfl, heckeRecursionSeq_add_two]
    field_simp
    linear_combination h

end Recursion

section Matrices

variable {K : Type*} [Field K]

variable (π : K) (hπ : π ≠ 0)

@[scoped simp] private theorem diagZ_zero : diagZ π hπ 0 = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [diagZ]

private theorem diagZ_mul_repSome (m : ℤ) (β : K) :
    diagZ π hπ m * repSome π hπ β = unipotent (π ^ m * β) * diagZ π hπ (m + 1) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [diagZ, repSome, unipotent, Matrix.mul_apply, Fin.sum_univ_two, zpow_add_one₀ hπ]

private theorem diagZ_succ_mul_repInf (m : ℤ) :
    diagZ π hπ (m + 1) * repInf π hπ = diagZ π hπ m * scalarPi π hπ := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [diagZ, repInf, scalarPi, Matrix.mul_apply, Fin.sum_univ_two, zpow_add_one₀ hπ]

private theorem diagZ_mul_unipotent (m : ℤ) (x : K) :
    diagZ π hπ m * unipotent x = unipotent (π ^ m * x) * diagZ π hπ m := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [diagZ, unipotent, Matrix.mul_apply, Fin.sum_univ_two]

end Matrices

section Torus

variable {R K G : Type*} [CommRing R] [Field K] [Algebra R K] [Group G]
variable (ι : GL (Fin 2) K →* G) (W : G → ℂ) (ψ : AddChar K ℂ) (ϖ : R)
  (hπ : algebraMap R K ϖ ≠ 0) (lam om : ℂ) (g₀ : G)

private def torusValue (m : ℤ) : ℂ := W (g₀ * ι (diagZ (algebraMap R K ϖ) hπ m))

variable {ι W ψ ϖ hπ lam om g₀}

private theorem torusValue_unipotent_mul
    (hN : ∀ (x : K) (g : G), W (ι (unipotent x) * g) = ψ x * W g)
    (hg₀ : ∀ x : GL (Fin 2) K, g₀ * ι x = ι x * g₀) (m : ℤ) (x : K) :
    W (g₀ * ι (diagZ (algebraMap R K ϖ) hπ m) * ι (unipotent x)) =
      ψ (algebraMap R K ϖ ^ m * x) * torusValue ι W ϖ hπ g₀ m := by
  rw [torusValue, mul_assoc, ← map_mul, diagZ_mul_unipotent, map_mul, ← mul_assoc, hg₀,
    mul_assoc, hN]

private theorem torusValue_eq_zero_of_neg
    (hN : ∀ (x : K) (g : G), W (ι (unipotent x) * g) = ψ x * W g)
    (hK : ∀ (r : R) (g : G), W (g * ι (unipotent (algebraMap R K r))) = W g)
    (hψ1 : ∃ r : R, ψ (algebraMap R K r / algebraMap R K ϖ) ≠ 1)
    (hg₀ : ∀ x : GL (Fin 2) K, g₀ * ι x = ι x * g₀) {m : ℤ} (hm : m < 0) :
    torusValue ι W ϖ hπ g₀ m = 0 := by
  obtain ⟨r, hr⟩ := hψ1
  obtain ⟨k, rfl⟩ := Int.eq_negSucc_of_lt_zero hm
  have h := hK (r * ϖ ^ k) (g₀ * ι (diagZ (algebraMap R K ϖ) hπ (Int.negSucc k)))
  rw [torusValue_unipotent_mul hN hg₀] at h
  have hx : algebraMap R K ϖ ^ (Int.negSucc k) * algebraMap R K (r * ϖ ^ k) =
      algebraMap R K r / algebraMap R K ϖ := by
    rw [zpow_negSucc, map_mul, map_pow]
    field_simp
    ring
  rw [hx] at h
  have hc : ψ (algebraMap R K r / algebraMap R K ϖ) * torusValue ι W ϖ hπ g₀ (Int.negSucc k) =
      torusValue ι W ϖ hπ g₀ (Int.negSucc k) := h
  have h' : (ψ (algebraMap R K r / algebraMap R K ϖ) - 1) * torusValue ι W ϖ hπ g₀ (Int.negSucc k)
      = 0 := by
    rw [sub_mul, one_mul, hc, sub_self]
  rcases mul_eq_zero.mp h' with h1 | h1
  · exact absurd (sub_eq_zero.mp h1) hr
  · exact h1

private theorem torusValue_recursion {I : Type*} [Fintype I] (b : I → R)
    (hψ0 : ∀ r : R, ψ (algebraMap R K r) = 1)
    (hN : ∀ (x : K) (g : G), W (ι (unipotent x) * g) = ψ x * W g)
    (hT : ∀ g : G, (∑ i, W (g * ι (repSome (algebraMap R K ϖ) hπ (algebraMap R K (b i))))) +
      W (g * ι (repInf (algebraMap R K ϖ) hπ)) = lam * W g)
    (hZ : ∀ g : G, W (g * ι (scalarPi (algebraMap R K ϖ) hπ)) = om * W g)
    (hg₀ : ∀ x : GL (Fin 2) K, g₀ * ι x = ι x * g₀) (m : ℕ) :
    lam * torusValue ι W ϖ hπ g₀ m =
      (Fintype.card I : ℂ) * torusValue ι W ϖ hπ g₀ (m + 1) +
        om * torusValue ι W ϖ hπ g₀ ((m : ℤ) - 1) := by
  have h := hT (g₀ * ι (diagZ (algebraMap R K ϖ) hπ m))
  have hsome : ∀ i, W (g₀ * ι (diagZ (algebraMap R K ϖ) hπ m) *
      ι (repSome (algebraMap R K ϖ) hπ (algebraMap R K (b i)))) = torusValue ι W ϖ hπ g₀ (m + 1) := by
    intro i
    rw [mul_assoc, ← map_mul, diagZ_mul_repSome, map_mul, ← mul_assoc, hg₀, mul_assoc, hN,
      zpow_natCast, ← map_pow, ← map_mul, hψ0, one_mul]
    rfl
  have hinf : W (g₀ * ι (diagZ (algebraMap R K ϖ) hπ m) * ι (repInf (algebraMap R K ϖ) hπ)) =
      om * torusValue ι W ϖ hπ g₀ ((m : ℤ) - 1) := by
    have e : diagZ (algebraMap R K ϖ) hπ m = diagZ (algebraMap R K ϖ) hπ ((m : ℤ) - 1 + 1) := by
      rw [sub_add_cancel]
    rw [e, mul_assoc, ← map_mul, diagZ_succ_mul_repInf, map_mul, ← mul_assoc, hZ]
    rfl
  rw [Finset.sum_congr rfl fun i _ => hsome i, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    hinf] at h
  exact h.symm

private theorem torusValue_eq_mul_heckeRecursionSeq {I : Type*} [Fintype I] [Nonempty I] (b : I → R)
    (hψ0 : ∀ r : R, ψ (algebraMap R K r) = 1)
    (hψ1 : ∃ r : R, ψ (algebraMap R K r / algebraMap R K ϖ) ≠ 1)
    (hN : ∀ (x : K) (g : G), W (ι (unipotent x) * g) = ψ x * W g)
    (hK : ∀ (r : R) (g : G), W (g * ι (unipotent (algebraMap R K r))) = W g)
    (hT : ∀ g : G, (∑ i, W (g * ι (repSome (algebraMap R K ϖ) hπ (algebraMap R K (b i))))) +
      W (g * ι (repInf (algebraMap R K ϖ) hπ)) = lam * W g)
    (hZ : ∀ g : G, W (g * ι (scalarPi (algebraMap R K ϖ) hπ)) = om * W g)
    (hg₀ : ∀ x : GL (Fin 2) K, g₀ * ι x = ι x * g₀) (m : ℕ) :
    torusValue ι W ϖ hπ g₀ m =
      W g₀ * heckeRecursionSeq (Fintype.card I) lam om m := by
  have hcard : (Fintype.card I : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h0 : torusValue ι W ϖ hπ g₀ ((0 : ℕ) : ℤ) = W g₀ := by
    simp [torusValue, diagZ_zero]
  have key := torusValue_recursion b hψ0 hN hT hZ hg₀
  have h := eq_mul_heckeRecursionSeq (N := (Fintype.card I : ℂ)) (lam := lam) (om := om) hcard
    (c := fun k : ℕ => torusValue ι W ϖ hπ g₀ k) ?_ ?_ m
  · rw [h0] at h
    exact h
  ·
    have k0 := key 0
    rw [torusValue_eq_zero_of_neg hN hK hψ1 hg₀ (by norm_num : ((0 : ℕ) : ℤ) - 1 < 0), mul_zero,
      add_zero] at k0
    simpa using k0.symm
  · intro k
    have k1 := key (k + 1)
    have e1 : (((k + 1 : ℕ) : ℤ) - 1) = (k : ℤ) := by push_cast; ring
    have e2 : (((k + 1 : ℕ) : ℤ) + 1) = ((k + 2 : ℕ) : ℤ) := by push_cast; ring
    rw [e1, e2] at k1
    linear_combination -k1

end Torus

/-! ## The rows -/

theorem summable_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow
    (N lam om lam' om' : ℂ) (hN : N ≠ 0) (y : ℂ)
    (hy : ‖y‖ * (max 1 (‖lam‖ + ‖N * om‖)) * (max 1 (‖lam'‖ + ‖N * om'‖)) < ‖N‖ ^ 2) :
    Summable fun m : ℕ => heckeRecursionSeq N lam om m * heckeRecursionSeq N lam' om' m * y ^ m := by
  set M := max 1 (‖lam‖ + ‖N * om‖)
  set M' := max 1 (‖lam'‖ + ‖N * om'‖)
  have hNn : 0 < ‖N‖ ^ 2 := by positivity
  set r : ℝ := ‖y‖ * M * M' / ‖N‖ ^ 2 with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by rw [hr, div_lt_one hNn]; exact hy
  refine Summable.of_norm_bounded (summable_geometric_of_lt_one hr0 hr1) (fun m => ?_)
  have e : heckeRecursionSeq N lam om m * heckeRecursionSeq N lam' om' m * y ^ m =
      (N ^ m * heckeRecursionSeq N lam om m) * (N ^ m * heckeRecursionSeq N lam' om' m) * (y / N ^ 2) ^ m := by
    rw [div_pow, ← pow_mul, mul_comm 2 m, pow_mul]
    field_simp
  rw [e, norm_mul, norm_mul, norm_pow, norm_div, norm_pow, hr,
    show (‖y‖ * M * M' / ‖N‖ ^ 2) ^ m = M ^ m * M' ^ m * (‖y‖ / ‖N‖ ^ 2) ^ m by ring]
  have b1 := EulerFactor.norm_pow_mul_heckeRecursionSeq_le N lam om hN m
  have b2 := EulerFactor.norm_pow_mul_heckeRecursionSeq_le N lam' om' hN m
  have : ‖N ^ m * heckeRecursionSeq N lam om m‖ * ‖N ^ m * heckeRecursionSeq N lam' om' m‖ ≤ M ^ m * M' ^ m :=
    mul_le_mul b1 b2 (norm_nonneg _) (by positivity)
  gcongr

theorem tsum_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow_mul_rsEulerPoly_eval
    (N lam om lam' om' : ℂ) (hN : N ≠ 0) (y : ℂ)
    (hsum : Summable fun m : ℕ => heckeRecursionSeq N lam om m * heckeRecursionSeq N lam' om' m * y ^ m) :
    (∑' m : ℕ, heckeRecursionSeq N lam om m * heckeRecursionSeq N lam' om' m * y ^ m) *
        (LanglandsTunnell.RankinSelberg.rsEulerPoly lam (N * om) lam' (N * om') 0).eval (y / N ^ 2) =
      1 - om * om' * (y / N) ^ 2 := by
  obtain ⟨a0, a1, ha⟩ := EulerFactor.pow_mul_heckeRecursionSeq_rec N lam om hN
  obtain ⟨b0, b1, hb⟩ := EulerFactor.pow_mul_heckeRecursionSeq_rec N lam' om' hN
  have hfun : (fun m : ℕ => heckeRecursionSeq N lam om m * heckeRecursionSeq N lam' om' m * y ^ m) =
      fun m : ℕ => (N ^ m * heckeRecursionSeq N lam om m) * (N ^ m * heckeRecursionSeq N lam' om' m) *
        (y / N ^ 2) ^ m := by
    funext m
    rw [div_pow, ← pow_mul, mul_comm 2 m, pow_mul]
    field_simp
  rw [hfun] at hsum ⊢
  rw [EulerFactor.tsum_mul_mul_pow_mul_eval_rsEulerPoly lam (N * om) lam' (N * om') _ _ a0 a1 b0 b1 ha hb _ hsum]
  field_simp

section Adelic

variable {R : Type*} (K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

variable {K}

theorem apply_mul_placeEmbed_diagZ_eq_mul_torusFactor (v : HeightOneSpectrum R)
    {W : GL (Fin 2) (AdeleRing R K) → ℂ} {ψ : AddChar (v.adicCompletion K) ℂ}
    {ϖ : v.adicCompletionIntegers K}
    (hπ : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0) {lam om : ℂ}
    {I : Type*} [Fintype I] [Nonempty I] (b : I → v.adicCompletionIntegers K)
    (hψ0 : ∀ r : v.adicCompletionIntegers K,
      ψ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r) = 1)
    (hψ1 : ∃ r : v.adicCompletionIntegers K,
      ψ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r /
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) ≠ 1)
    (hN : ∀ (x : v.adicCompletion K) (g : GL (Fin 2) (AdeleRing R K)),
      W (placeEmbed K v (unipotent x) * g) = ψ x * W g)
    (hK : ∀ (r : v.adicCompletionIntegers K) (g : GL (Fin 2) (AdeleRing R K)),
      W (g * placeEmbed K v (unipotent
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r))) = W g)
    (hT : ∀ g : GL (Fin 2) (AdeleRing R K),
      (∑ i, W (g * placeEmbed K v (repSome
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (b i))))) +
        W (g * placeEmbed K v (repInf
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ)) = lam * W g)
    (hZ : ∀ g : GL (Fin 2) (AdeleRing R K),
      W (g * placeEmbed K v (scalarPi
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ)) = om * W g)
    {g₀ : GL (Fin 2) (AdeleRing R K)}
    (hg₀ : ∀ x : GL (Fin 2) (v.adicCompletion K), g₀ * placeEmbed K v x = placeEmbed K v x * g₀)
    (m : ℤ) :
    W (g₀ * placeEmbed K v (diagZ
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ m)) =
      W g₀ * torusFactor (Fintype.card I) lam om m := by
  unfold torusFactor
  split_ifs with hm
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    have hn : ((n : ℤ)).toNat = n := by simp
    rw [hn]
    exact torusValue_eq_mul_heckeRecursionSeq b hψ0 hψ1 hN hK hT hZ hg₀ n
  · rw [mul_zero]
    exact torusValue_eq_zero_of_neg hN hK hψ1 hg₀ (not_le.mp hm)

end Adelic

end UnramifiedWhittaker

end
