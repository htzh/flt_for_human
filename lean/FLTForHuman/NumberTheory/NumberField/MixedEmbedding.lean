/-
The mixed-embedding leaves: trace, the norm-embedding lattice point, summability, and the
fractional ideal's weight.

Four mathlib-shaped rows over mathlib's `NumberField.mixedEmbedding` (the `K → ℝ^{r₁} × ℂ^{r₂}`
embedding of `Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic`), all of them graph leaves
with no `Definitions/` import in their `S_` file:

* `trace_mixedEmbedding` — `Algebra.trace ℝ (mixedSpace K) (mixedEmbedding K x)` is `trace ℚ K x`;
* `exists_forall_norm_embedding_sub_le` — the ring of integers is co-bounded in the `r₁`-real part:
  every real-compatible point of `ℝ^{r₁} × ℂ^{r₂}` is within a uniform `U` of an algebraic integer;
* `summable_norm_schwartzMap_ringOfIntegers_translate` — the translate of a Schwartz function by the
  image of `𝓞 F` is summable in norm;
* `exists_forall_tsum_fractionalIdeal_weight_le_rpow_neg` — the fractional ideal's weighted `ℓ¹` sum
  is bounded by `C t^{-N'}` uniformly for `N` large enough: the analytic input the ideal-lattice
  counting consumes.

Earlier sets deferred these as "blocked on a definition layer"; that reading does not survive the
`S_`-file check (FR-0298): the namespace is **mathlib's**, and no pin `Def_` module is imported. The
order's risk is therefore API drift (`v4.33.1` pin against the port's `v4.34.0`), which the scaffold
pass measures, not a missing port module.

## The rows

* `NumberField.mixedEmbedding.trace_mixedEmbedding` — 17 pin `S_` lines.
* `NumberField.mixedEmbedding.exists_forall_norm_embedding_sub_le` — 71 pin `S_` lines.
* `NumberField.mixedEmbedding.summable_norm_schwartzMap_ringOfIntegers_translate` — 67 pin `S_` lines.
* `NumberField.mixedEmbedding.exists_forall_tsum_fractionalIdeal_weight_le_rpow_neg` — 237 pin `S_` lines.

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_NumberField_mixedEmbedding_trace_mixedEmbedding.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_NumberField_mixedEmbedding_exists_forall_norm_embedding_sub_le.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_NumberField_mixedEmbedding_summable_norm_schwartzMap_ringOfIntegers_translate.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_NumberField_mixedEmbedding_exists_forall_tsum_fractionalIdeal_weight_le_rpow_neg.lean>

spec-pin: Theorems/Thm_NumberField_mixedEmbedding_trace_mixedEmbedding.lean
spec-pin: P2M/Sol/S_NumberField_mixedEmbedding_trace_mixedEmbedding.lean
spec-pin: Theorems/Thm_NumberField_mixedEmbedding_exists_forall_norm_embedding_sub_le.lean
spec-pin: P2M/Sol/S_NumberField_mixedEmbedding_exists_forall_norm_embedding_sub_le.lean
spec-pin: Theorems/Thm_NumberField_mixedEmbedding_summable_norm_schwartzMap_ringOfIntegers_translate.lean
spec-pin: P2M/Sol/S_NumberField_mixedEmbedding_summable_norm_schwartzMap_ringOfIntegers_translate.lean
spec-pin: Theorems/Thm_NumberField_mixedEmbedding_exists_forall_tsum_fractionalIdeal_weight_le_rpow_neg.lean
spec-pin: P2M/Sol/S_NumberField_mixedEmbedding_exists_forall_tsum_fractionalIdeal_weight_le_rpow_neg.lean

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_NumberField_mixedEmbedding_traceForm_mixedSpace_nondegenerate.lean>
  spec-pin: Theorems/Thm_NumberField_mixedEmbedding_traceForm_mixedSpace_nondegenerate.lean
  spec-pin: P2M/Sol/S_NumberField_mixedEmbedding_traceForm_mixedSpace_nondegenerate.lean

## Port notes (order AF107F, ported at pin `aa2d8b3` against the port's mathlib `v4.34.0`)

* **Surface = the pin's.** 12 declarations, 12 public / 0 private, against the pin's 16
  declaration entries across the four `Theorems/Thm_…` + four `P2M/Sol/S_…` files. The four
  extra pin entries are the same statements twice: every row appears as the generated
  `solution` in its `S_` file and again as the `Thm_…` wrapper. 16 − 4 = 12, name for name.
* **`check_port`**: 12 ok, 0 mismatch, 0 missing, 0 own, 0 kw.
* **Substitutions**: none. No port copy of any of these exists, and no import was added — the
  scaffold's import list carried every proof.
* **API drift** (`v4.33.1` → `v4.34.0`, this module's whole porting cost; the statements were
  already green): `Finset.one_le_prod` → `Finset.one_le_prod₀`, `Finset.prod_le_prod` →
  `Finset.prod_le_prod₀` (`ℝ` is not `MulLeftMono`, so v4.34.0 split the nonnegative form out),
  `Real.finset_prod_rpow` → `Real.finsetProd_rpow`, `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`,
  `push_neg` → `push Not`, and the pin's `haveI : IsEmpty {ξ // …}` (a `Prop`) became `have`
  per `linter.style.haveILetI` — nothing was silenced. The new `ZSpan` (`floor`/`fract` over an
  `ℝ`-basis) is what `latticeBasis` already is, so those proofs went through verbatim.
* **Namespaces**: the pin's generated `M4aP1R` and `B2dLattice` labels are replaced by
  `NumberField.mixedEmbedding` and `…IntegerTranslate`; the pin's own declaration names are kept.
* **Axioms**: all 12 public declarations depend on a subset of
  `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.
* **`dedup --within`**: 1 cluster, 7 lines — `exists_forall_norm_embedding_sub_le_impl` ↔
  `exists_forall_norm_embedding_sub_le` (identical statements). This is the pin's own
  headline↔engine pair, kept for faithfulness; it is the same duplicate the pin carries.
* **`move_dead --dry-run`**: 0 declarations, 0 lines.
* **Heartbeat probe (recorded, never installed; the module carries no `set_option`)**:
  downward ladder 40000 / 20000 / 10000 / 5000 / 1000 — **fails all five**, at
  `weight_le`'s `(Finset.univ : Finset {w : InfinitePlace F // w.IsReal})`, the error
  reported at the `one_add_mul_sum_le_prod` call (`whnf`). Bisected upward: fails at 80000, passes at 100000.
  Module floor (every proof `sorry`, statements verbatim): **passes at 1000**, so the cost is in
  the proof term, not in the types. No cap is installed; the module elaborates at the standard
  cap and at the edit loop's 200 k.

## Landing (AF108H) — the trace-form nondegeneracy row

A thirteenth declaration joins the twelve: `traceForm_mixedSpace_nondegenerate`,
`(Algebra.traceForm ℝ (mixedSpace K)).Nondegenerate`, the consumer of this module's own
`trace_mixedEmbedding` (22 pin `S_` lines). 479 lines now (471 before); `check_port`
**13 ok / 0 mismatch / 0 missing / 0 own / 0 kw**. No substitution and no import: the pin's
proof is the cheapest route (`LinearMap.BilinForm.nondegenerate_of_det_ne_zero (latticeBasis K)`,
the matrix identity `toMatrix = (traceMatrix ℚ (integralBasis K)).map (algebraMap ℚ ℝ)` through
`traceForm_toMatrix`/`traceMatrix_apply`/`trace_mixedEmbedding`, then
`Algebra.discr_not_zero_of_basis`); it elaborated at this mathlib unchanged.

* **Engine gate** over the same ten pin sources: pin decls **18**, module decls **13**;
  **13 by hash**, 0 by name (hash differs), **0 unaccounted**.
* **`dedup --within`**: the same **1** cluster as before this row
  (`exists_forall_norm_embedding_sub_le_impl` ↔ `…_sub_le`, the pin's own headline↔engine
  pair). **`move_dead --dry-run`**: 0 declarations, 0 lines.
* **Axioms**: all 13 public declarations, `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
* **Heartbeat probe**: unchanged by this row — fails at 80000 (`whnf`, in `Weight`'s
  `mul_le_mul`), passes at 100000, the module's bisector as AF107F recorded it. The new row is
  not the worst site.
-/

import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace Module
open scoped Classical SchwartzMap

set_option autoImplicit false

noncomputable section

namespace NumberField.mixedEmbedding

theorem trace_mixedEmbedding
    (K : Type*) [Field K] [NumberField K] (x : K) :
    Algebra.trace ℝ (mixedSpace K) (mixedEmbedding K x) = (Algebra.trace ℚ K x : ℝ) := by
  rw [Algebra.trace_eq_matrix_trace (latticeBasis K) (mixedEmbedding K x),
    Algebra.trace_eq_matrix_trace (integralBasis K) x, Matrix.trace, Matrix.trace, Rat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, latticeBasis_apply, ← map_mul, latticeBasis_repr_apply]

namespace IntegerTranslate

variable (K : Type*) [Field K] [NumberField K]

theorem exists_norm_sub_mixedEmbedding_le :
    ∃ U : ℝ, ∀ m : mixedSpace K, ∃ b : 𝓞 K, ‖m - mixedEmbedding K (b : K)‖ ≤ U := by
  classical
  let B := mixedEmbedding.latticeBasis K
  refine ⟨∑ i, ‖B i‖, fun m => ?_⟩
  have hv : m - ZSpan.fract B m ∈ mixedEmbedding.integerLattice K := by
    rw [← mem_span_latticeBasis]
    have h1 : m - ZSpan.fract B m = (ZSpan.floor B m : mixedSpace K) := by
      rw [ZSpan.fract_apply]; abel
    rw [h1]
    exact (ZSpan.floor B m).2
  obtain ⟨b, hb⟩ := LinearMap.mem_range.mp hv
  refine ⟨b, ?_⟩
  have hb' : mixedEmbedding K (b : K) = m - ZSpan.fract B m := hb
  rw [hb', sub_sub_cancel]
  exact ZSpan.norm_fract_le B m

theorem exists_forall_norm_embedding_sub_le_impl (K : Type*) [Field K]
    [NumberField K] : ∃ U : ℝ, ∀ ξ : NumberField.InfinitePlace K → ℂ,
      (∀ w : NumberField.InfinitePlace K, w.IsReal → (ξ w).im = 0) →
        ∃ b : NumberField.RingOfIntegers K, ∀ w : NumberField.InfinitePlace K,
          ‖w.embedding (b : K) - ξ w‖ ≤ U := by
  classical
  obtain ⟨U, hU⟩ := exists_norm_sub_mixedEmbedding_le K
  refine ⟨U, fun ξ hξ => ?_⟩
  let m : mixedSpace K := (fun w => (ξ w.val).re, fun w => ξ w.val)
  obtain ⟨b, hb⟩ := hU m
  refine ⟨b, fun w => ?_⟩
  by_cases hw : IsReal w
  · have h1 := (norm_le_pi_norm (m - mixedEmbedding K (b : K)).1 ⟨w, hw⟩).trans
      ((norm_fst_le _).trans hb)
    rw [Prod.fst_sub, Pi.sub_apply, mixedEmbedding_apply_isReal, Real.norm_eq_abs] at h1
    have hξw : ξ w = ((ξ w).re : ℂ) := by
      apply Complex.ext
      · simp
      · simp [hξ w hw]
    rw [hξw, ← embedding_of_isReal_apply hw, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_sub_comm]
    exact h1
  · have hc : IsComplex w := not_isReal_iff_isComplex.mp hw
    have h1 := (norm_le_pi_norm (m - mixedEmbedding K (b : K)).2 ⟨w, hc⟩).trans
      ((norm_snd_le _).trans hb)
    rw [Prod.snd_sub, Pi.sub_apply, mixedEmbedding_apply_isComplex] at h1
    rw [norm_sub_rev]
    exact h1

end IntegerTranslate

theorem exists_forall_norm_embedding_sub_le (K : Type*) [Field K]
    [NumberField K] : ∃ U : ℝ, ∀ ξ : NumberField.InfinitePlace K → ℂ,
      (∀ w : NumberField.InfinitePlace K, w.IsReal → (ξ w).im = 0) →
        ∃ b : NumberField.RingOfIntegers K, ∀ w : NumberField.InfinitePlace K,
          ‖w.embedding (b : K) - ξ w‖ ≤ U :=
  IntegerTranslate.exists_forall_norm_embedding_sub_le_impl K

theorem summable_norm_schwartzMap_ringOfIntegers_translate
    (F : Type*) [Field F] [NumberField F]
    (g : 𝓢(NumberField.mixedEmbedding.mixedSpace F, ℂ))
    (x : NumberField.mixedEmbedding.mixedSpace F) :
    Summable fun a : 𝓞 F => ‖g (x + NumberField.mixedEmbedding F (a : F))‖ := by
  classical

  let e : 𝓞 F ≃ mixedEmbedding.integerLattice F :=
    Equiv.ofBijective
      (fun a => ⟨mixedEmbedding F (a : F), LinearMap.mem_range.mpr ⟨a, rfl⟩⟩)
      ⟨fun a b hab => RingOfIntegers.coe_injective
          ((mixedEmbedding_injective F) (Subtype.ext_iff.mp hab)),
        fun z => by
          obtain ⟨a, ha⟩ := LinearMap.mem_range.mp z.2
          exact ⟨a, Subtype.ext ha⟩⟩
  have hes : ∀ lam : mixedEmbedding.integerLattice F,
      mixedEmbedding F ((e.symm lam : 𝓞 F) : F) = (lam : mixedSpace F) := fun lam =>
    Subtype.ext_iff.mp (e.apply_symm_apply lam)
  have hfunc : (fun a : 𝓞 F => ‖g (x + mixedEmbedding F (a : F))‖) ∘ e.symm
      = fun lam : mixedEmbedding.integerLattice F => ‖g (x + (lam : mixedSpace F))‖ := by
    funext lam; simp only [Function.comp_apply, hes]
  rw [← Equiv.summable_iff e.symm, hfunc]

  set d : ℕ := Module.finrank ℤ (mixedEmbedding.integerLattice F) + 1 with hd
  have hd_lt : Module.finrank ℤ (mixedEmbedding.integerLattice F) < d := Nat.lt_succ_self _

  have hsum : Summable fun lam : mixedEmbedding.integerLattice F =>
      ‖(lam : mixedSpace F) - (-x)‖⁻¹ ^ d := by
    have hr : (-(d : ℝ)) < -(Module.finrank ℤ (mixedEmbedding.integerLattice F) : ℝ) := by
      simp only [neg_lt_neg_iff]; exact_mod_cast hd_lt
    have hZ := ZLattice.summable_norm_sub_rpow (L := mixedEmbedding.integerLattice F)
      (r := -(d : ℝ)) hr (-x)
    refine hZ.congr fun lam => ?_
    rw [Real.rpow_neg (norm_nonneg _), Real.rpow_natCast, inv_pow]

  refine Summable.of_norm_bounded_eventually
    (g := fun lam : mixedEmbedding.integerLattice F =>
      SchwartzMap.seminorm ℝ d 0 g * ‖(lam : mixedSpace F) - (-x)‖⁻¹ ^ d)
    (hsum.mul_left _) ?_
  rw [Filter.eventually_cofinite]
  refine Set.Finite.subset
    (Set.Subsingleton.finite (s := {lam : mixedEmbedding.integerLattice F | (lam : mixedSpace F) = -x})
      fun a₁ h₁ a₂ h₂ => Subtype.coe_injective (h₁.trans h₂.symm)) ?_
  intro lam hlam
  simp only [Set.mem_ofPred_eq] at hlam ⊢
  by_contra hne
  apply hlam

  have hne0 : x + (lam : mixedSpace F) ≠ 0 := by
    intro h0; exact hne ((neg_eq_of_add_eq_zero_right h0).symm)
  have hpos : (0 : ℝ) < ‖x + (lam : mixedSpace F)‖ ^ d := pow_pos (norm_pos_iff.mpr hne0) _
  have hdecay := SchwartzMap.norm_pow_mul_le_seminorm ℝ g d (x + (lam : mixedSpace F))

  have hnorm : ‖(lam : mixedSpace F) - (-x)‖ = ‖x + (lam : mixedSpace F)‖ := by
    rw [sub_neg_eq_add, add_comm]
  rw [norm_norm, hnorm, inv_pow, ← div_eq_mul_inv, le_div_iff₀ hpos, mul_comm]
  exact hdecay

theorem one_add_mul_sum_le_prod {ι : Type*} (s : Finset ι) (a : ι → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (ha : ∀ i ∈ s, 0 ≤ a i) : 1 + t * ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 + t * a i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    have ha' : ∀ i ∈ s, 0 ≤ a i := fun i hi => ha i (Finset.mem_insert_of_mem hi)
    have hj0 : 0 ≤ a j := ha j (Finset.mem_insert_self j s)
    have hP : 1 ≤ ∏ i ∈ s, (1 + t * a i) :=
      Finset.one_le_prod₀ fun i hi => le_add_of_nonneg_right (mul_nonneg ht (ha' i hi))
    have h1 := ih ha'
    have : 0 ≤ t * a j := mul_nonneg ht hj0
    nlinarith [mul_nonneg this (sub_nonneg.mpr hP)]

section Weight

variable (F : Type) [Field F] [NumberField F]

theorem norm_le_sum_coords (x : mixedSpace F) :
    ‖x‖ ≤ (∑ w : {w : InfinitePlace F // w.IsReal}, |x.1 w|) + ∑ w : {w : InfinitePlace F // w.IsComplex}, ‖x.2 w‖ := by
  have h1 : ‖x.1‖ ≤ ∑ w : {w : InfinitePlace F // w.IsReal}, |x.1 w| := by
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun w _ => abs_nonneg _)).mpr fun w => ?_
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (f := fun w => |x.1 w|) (fun w _ => abs_nonneg _) (Finset.mem_univ w)
  have h2 : ‖x.2‖ ≤ ∑ w : {w : InfinitePlace F // w.IsComplex}, ‖x.2 w‖ := by
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun w _ => norm_nonneg _)).mpr fun w => ?_
    exact Finset.single_le_sum (f := fun w => ‖x.2 w‖) (fun w _ => norm_nonneg _) (Finset.mem_univ w)
  rw [Prod.norm_def]
  refine max_le (h1.trans (le_add_of_nonneg_right (Finset.sum_nonneg fun w _ => norm_nonneg _)))
    (h2.trans (le_add_of_nonneg_left (Finset.sum_nonneg fun w _ => abs_nonneg _)))

theorem normAtPlace_le_norm (w : InfinitePlace F) (x : mixedSpace F) : normAtPlace w x ≤ ‖x‖ := by
  by_cases hw : w.IsReal
  · rw [normAtPlace_apply_of_isReal hw]
    exact (norm_le_pi_norm _ _).trans (le_max_left _ _)
  · rw [normAtPlace_apply_of_isComplex (not_isReal_iff_isComplex.mp hw)]
    exact (norm_le_pi_norm _ _).trans (le_max_right _ _)

theorem abs_norm_le_norm_pow (ξ : F) :
    ((|Algebra.norm ℚ ξ| : ℚ) : ℝ) ≤ ‖mixedEmbedding F ξ‖ ^ Module.finrank ℚ F := by
  rw [← norm_eq_norm, mixedEmbedding.norm_apply, ← sum_mult_eq, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod₀ (fun w _ => pow_nonneg (normAtPlace_nonneg _ _) _) fun w _ => ?_
  exact pow_le_pow_left₀ (normAtPlace_nonneg _ _) (normAtPlace_le_norm F w _) _

theorem weight_le (N : ℕ) (t : ℝ) (ht : 0 < t) (x : mixedSpace F) (hx : x ≠ 0) :
    (∏ w : {w : InfinitePlace F // w.IsReal}, (1 + t * |x.1 w|) ^ (-(N : ℝ))) *
      ∏ w : {w : InfinitePlace F // w.IsComplex}, (1 + t * ‖x.2 w‖) ^ (-(2 * N : ℝ))
      ≤ (t * ‖x‖) ^ (-(N : ℝ)) := by
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx

  have hc : ∀ w : {w : InfinitePlace F // w.IsComplex},
      (1 + t * ‖x.2 w‖) ^ (-(2 * N : ℝ)) ≤ (1 + t * ‖x.2 w‖) ^ (-(N : ℝ)) := fun w =>
    Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_right (by positivity)) (by
      have : (0 : ℝ) ≤ N := N.cast_nonneg; linarith)
  have step1 : (∏ w : {w : InfinitePlace F // w.IsReal}, (1 + t * |x.1 w|) ^ (-(N : ℝ))) *
      ∏ w : {w : InfinitePlace F // w.IsComplex}, (1 + t * ‖x.2 w‖) ^ (-(2 * N : ℝ))
      ≤ (∏ w : {w : InfinitePlace F // w.IsReal}, (1 + t * |x.1 w|) ^ (-(N : ℝ))) *
        ∏ w : {w : InfinitePlace F // w.IsComplex}, (1 + t * ‖x.2 w‖) ^ (-(N : ℝ)) := by
    refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun w _ => by positivity) fun w _ => hc w)
      (Finset.prod_nonneg fun w _ => by positivity)
  refine step1.trans ?_
  rw [Real.finsetProd_rpow _ _ (fun w _ => by positivity), Real.finsetProd_rpow _ _ (fun w _ => by positivity),
    ← Real.mul_rpow (Finset.prod_nonneg fun w _ => by positivity) (Finset.prod_nonneg fun w _ => by positivity)]

  refine Real.rpow_le_rpow_of_nonpos (mul_pos ht hxn) ?_ (by have : (0 : ℝ) ≤ N := N.cast_nonneg; linarith)
  have hsum := norm_le_sum_coords F x
  have hP1 := one_add_mul_sum_le_prod (Finset.univ : Finset {w : InfinitePlace F // w.IsReal}) (fun w => |x.1 w|) t ht.le
    (fun w _ => abs_nonneg _)
  have hP2 := one_add_mul_sum_le_prod (Finset.univ : Finset {w : InfinitePlace F // w.IsComplex}) (fun w => ‖x.2 w‖) t ht.le
    (fun w _ => norm_nonneg _)
  have hA : 0 ≤ ∑ w : {w : InfinitePlace F // w.IsReal}, |x.1 w| := Finset.sum_nonneg fun w _ => abs_nonneg _
  have hB : 0 ≤ ∑ w : {w : InfinitePlace F // w.IsComplex}, ‖x.2 w‖ := Finset.sum_nonneg fun w _ => norm_nonneg _
  calc t * ‖x‖ ≤ t * ((∑ w : {w : InfinitePlace F // w.IsReal}, |x.1 w|) + ∑ w : {w : InfinitePlace F // w.IsComplex}, ‖x.2 w‖) :=
        mul_le_mul_of_nonneg_left hsum ht.le
    _ ≤ (1 + t * ∑ w : {w : InfinitePlace F // w.IsReal}, |x.1 w|) * (1 + t * ∑ w : {w : InfinitePlace F // w.IsComplex}, ‖x.2 w‖) := by
        nlinarith [mul_nonneg ht.le hA, mul_nonneg ht.le hB, mul_nonneg (mul_nonneg ht.le hA) (mul_nonneg ht.le hB)]
    _ ≤ _ := mul_le_mul hP1 hP2 (by positivity) ((Finset.prod_nonneg fun w _ => by positivity))

end Weight

theorem exists_pos_forall_le_norm {E : Type*} [NormedAddCommGroup E] (L : Submodule ℤ E) [DiscreteTopology L] :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ L, x ≠ 0 → δ ≤ ‖x‖ := by
  have h0 : IsOpen ({0} : Set L) := isOpen_discrete _
  rw [Metric.isOpen_iff] at h0
  obtain ⟨ε, hε, hball⟩ := h0 0 (Set.mem_singleton 0)
  refine ⟨ε, hε, fun x hx hx0 => ?_⟩
  by_contra hlt
  push Not at hlt
  have : (⟨x, hx⟩ : L) ∈ Metric.ball (0 : L) ε := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hlt
  have h := hball this
  rw [Set.mem_singleton_iff] at h
  exact hx0 (congrArg Subtype.val h)

theorem exists_forall_tsum_fractionalIdeal_weight_le_rpow_neg
    (F : Type) [Field F] [NumberField F]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (k N' : ℕ) (t₀ : ℝ) (ht₀ : 0 < t₀) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ C : ℝ, ∀ t : ℝ, t₀ ≤ t →
      Summable (fun ξ : {ξ : F // ξ ≠ 0 ∧ ξ ∈ I} =>
        (max 1 ((|Algebra.norm ℚ ξ.1| : ℚ) : ℝ)) ^ k *
          (∏ w : {w : InfinitePlace F // w.IsReal}, (1 + t * |(mixedEmbedding F ξ.1).1 w|) ^ (-(N : ℝ))) *
          ∏ w : {w : InfinitePlace F // w.IsComplex}, (1 + t * ‖(mixedEmbedding F ξ.1).2 w‖) ^ (-(2 * N : ℝ))) ∧
      ∑' ξ : {ξ : F // ξ ≠ 0 ∧ ξ ∈ I},
        (max 1 ((|Algebra.norm ℚ ξ.1| : ℚ) : ℝ)) ^ k *
          (∏ w : {w : InfinitePlace F // w.IsReal}, (1 + t * |(mixedEmbedding F ξ.1).1 w|) ^ (-(N : ℝ))) *
          ∏ w : {w : InfinitePlace F // w.IsComplex}, (1 + t * ‖(mixedEmbedding F ξ.1).2 w‖) ^ (-(2 * N : ℝ))
        ≤ C * t ^ (-(N' : ℝ)) := by
  set n : ℕ := Module.finrank ℚ F with hn
  by_cases hI : I = 0
  · have : IsEmpty {ξ : F // ξ ≠ 0 ∧ ξ ∈ I} := ⟨fun ξ => ξ.2.1 (by
      have h : (ξ.1 : F) ∈ (0 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := hI ▸ ξ.2.2
      exact (FractionalIdeal.mem_zero_iff _).mp h)⟩
    refine ⟨0, fun N _ => ⟨0, fun t _ => ⟨(hasSum_empty).summable, ?_⟩⟩⟩
    rw [tsum_empty, zero_mul]

  set Iu : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ := Units.mk0 I hI with hIu
  set L : Submodule ℤ (mixedSpace F) := mixedEmbedding.idealLattice F Iu with hL
  obtain ⟨δ, hδ0, hδ⟩ := exists_pos_forall_le_norm L
  have hrank : Module.finrank ℤ L = n := by rw [ZLattice.rank ℝ L, mixedEmbedding.finrank]
  refine ⟨n * k + n + N' + 1, fun N hN => ?_⟩

  set p : ℝ := (N : ℝ) - n * k with hp
  have hNr : ((n * k + n + N' + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
  push_cast at hNr
  have hpn : -p < -(Module.finrank ℤ L : ℝ) := by rw [hrank, hp]; linarith
  have hS := ZLattice.summable_norm_rpow L (-p) hpn
  set S : ℝ := ∑' x : L, ‖x‖ ^ (-p) with hSdef
  have hS0 : 0 ≤ S := tsum_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _

  set cδ : ℝ := max 1 (δ⁻¹ ^ n) with hcδ
  have hcδ1 : 1 ≤ cδ := le_max_left _ _
  set K₀ : ℝ := cδ ^ k * t₀ ^ (-((N : ℝ) - N')) with hK₀
  have hK₀0 : 0 ≤ K₀ := mul_nonneg (pow_nonneg (zero_le_one.trans hcδ1) _) (Real.rpow_nonneg ht₀.le _)
  refine ⟨K₀ * S, fun t ht => ?_⟩
  have ht0 : 0 < t := ht₀.trans_le ht

  let ι : {ξ : F // ξ ≠ 0 ∧ ξ ∈ I} → L := fun ξ =>
    ⟨mixedEmbedding F ξ.1, (mixedEmbedding.mem_idealLattice F Iu).mpr ⟨ξ.1, ξ.2.2, rfl⟩⟩
  have hι : Function.Injective ι := by
    intro a b hab
    have h := congrArg (fun z : L => (z : mixedSpace F)) hab
    exact Subtype.ext ((mixedEmbedding_injective F) h)
  have hιne : ∀ ξ : {ξ : F // ξ ≠ 0 ∧ ξ ∈ I}, (ι ξ : mixedSpace F) ≠ 0 := fun ξ h =>
    ξ.2.1 ((map_eq_zero_iff _ (mixedEmbedding_injective F)).mp h)
  have hιδ : ∀ ξ : {ξ : F // ξ ≠ 0 ∧ ξ ∈ I}, δ ≤ ‖(ι ξ : mixedSpace F)‖ := fun ξ =>
    hδ _ (ι ξ).2 (hιne ξ)

  set term : {ξ : F // ξ ≠ 0 ∧ ξ ∈ I} → ℝ := fun ξ =>
    (max 1 ((|Algebra.norm ℚ ξ.1| : ℚ) : ℝ)) ^ k *
      (∏ w : {w : InfinitePlace F // w.IsReal}, (1 + t * |(mixedEmbedding F ξ.1).1 w|) ^ (-(N : ℝ))) *
      ∏ w : {w : InfinitePlace F // w.IsComplex}, (1 + t * ‖(mixedEmbedding F ξ.1).2 w‖) ^ (-(2 * N : ℝ)) with hterm
  have hnn : ∀ ξ, 0 ≤ term ξ := fun ξ => by
    simp only [hterm]
    exact mul_nonneg (mul_nonneg (pow_nonneg (by positivity) _) (Finset.prod_nonneg fun w _ => by positivity))
      (Finset.prod_nonneg fun w _ => by positivity)

  have hpt : ∀ ξ, term ξ ≤ K₀ * t ^ (-(N' : ℝ)) * ‖(ι ξ : mixedSpace F)‖ ^ (-p) := by
    intro ξ
    set x : mixedSpace F := (ι ξ : mixedSpace F) with hxdef
    have hxmE : x = mixedEmbedding F ξ.1 := rfl
    have hxδ : δ ≤ ‖x‖ := hιδ ξ
    have hx0 : 0 < ‖x‖ := hδ0.trans_le hxδ

    have hA : (max 1 ((|Algebra.norm ℚ ξ.1| : ℚ) : ℝ)) ^ k ≤ cδ ^ k * ‖x‖ ^ (n * k) := by
      have h1 : max 1 ((|Algebra.norm ℚ ξ.1| : ℚ) : ℝ) ≤ cδ * ‖x‖ ^ n := by
        refine max_le ?_ ((abs_norm_le_norm_pow F ξ.1).trans ?_)
        ·
          have : 1 ≤ (δ⁻¹ * ‖x‖) ^ n := one_le_pow₀ (by rw [inv_mul_eq_div, le_div_iff₀ hδ0]; simpa using hxδ)
          rw [mul_pow] at this
          exact this.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (norm_nonneg _) _))
        · rw [← hxmE]
          exact le_mul_of_one_le_left (pow_nonneg (norm_nonneg _) _) hcδ1
      calc (max 1 ((|Algebra.norm ℚ ξ.1| : ℚ) : ℝ)) ^ k ≤ (cδ * ‖x‖ ^ n) ^ k :=
            pow_le_pow_left₀ (by positivity) h1 k
        _ = cδ ^ k * ‖x‖ ^ (n * k) := by rw [mul_pow, ← pow_mul]

    have hB := weight_le F N t ht0 x (hιne ξ)

    have hC : (t * ‖x‖) ^ (-(N : ℝ)) ≤ t ^ (-(N' : ℝ)) * t₀ ^ (-((N : ℝ) - N')) * ‖x‖ ^ (-(N : ℝ)) := by
      rw [Real.mul_rpow ht0.le (norm_nonneg _)]
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (norm_nonneg _) _)
      have hsplit : t ^ (-(N : ℝ)) = t ^ (-(N' : ℝ)) * t ^ (-((N : ℝ) - N')) := by
        rw [← Real.rpow_add ht0]; congr 1; ring
      rw [hsplit]
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg ht0.le _)
      have hnk : (0 : ℝ) ≤ (n : ℝ) * k := by positivity
      exact Real.rpow_le_rpow_of_nonpos ht₀ ht (by linarith)

    have hW : (∏ w : {w : InfinitePlace F // w.IsReal}, (1 + t * |(mixedEmbedding F ξ.1).1 w|) ^ (-(N : ℝ))) *
        ∏ w : {w : InfinitePlace F // w.IsComplex}, (1 + t * ‖(mixedEmbedding F ξ.1).2 w‖) ^ (-(2 * N : ℝ))
        ≤ t ^ (-(N' : ℝ)) * t₀ ^ (-((N : ℝ) - N')) * ‖x‖ ^ (-(N : ℝ)) := by
      rw [← hxmE]; exact hB.trans hC
    have hWnn : 0 ≤ (∏ w : {w : InfinitePlace F // w.IsReal}, (1 + t * |(mixedEmbedding F ξ.1).1 w|) ^ (-(N : ℝ))) *
        ∏ w : {w : InfinitePlace F // w.IsComplex}, (1 + t * ‖(mixedEmbedding F ξ.1).2 w‖) ^ (-(2 * N : ℝ)) :=
      mul_nonneg (Finset.prod_nonneg fun w _ => by positivity) (Finset.prod_nonneg fun w _ => by positivity)
    calc term ξ = (max 1 ((|Algebra.norm ℚ ξ.1| : ℚ) : ℝ)) ^ k *
          ((∏ w : {w : InfinitePlace F // w.IsReal}, (1 + t * |(mixedEmbedding F ξ.1).1 w|) ^ (-(N : ℝ))) *
            ∏ w : {w : InfinitePlace F // w.IsComplex}, (1 + t * ‖(mixedEmbedding F ξ.1).2 w‖) ^ (-(2 * N : ℝ))) := by
          simp only [hterm, mul_assoc]
      _ ≤ (cδ ^ k * ‖x‖ ^ (n * k)) * (t ^ (-(N' : ℝ)) * t₀ ^ (-((N : ℝ) - N')) * ‖x‖ ^ (-(N : ℝ))) :=
          mul_le_mul hA hW hWnn (by positivity)
      _ = K₀ * t ^ (-(N' : ℝ)) * (‖x‖ ^ (n * k) * ‖x‖ ^ (-(N : ℝ))) := by simp only [hK₀]; ring
      _ = K₀ * t ^ (-(N' : ℝ)) * ‖x‖ ^ (-p) := by
          rw [← Real.rpow_natCast ‖x‖ (n * k), ← Real.rpow_add hx0]
          congr 2
          push_cast
          simp only [hp]; ring

  have hmajS : Summable (fun ξ : {ξ : F // ξ ≠ 0 ∧ ξ ∈ I} => ‖(ι ξ : mixedSpace F)‖ ^ (-p)) := by
    have := hS.comp_injective hι
    exact this
  have hmaj : Summable (fun ξ : {ξ : F // ξ ≠ 0 ∧ ξ ∈ I} => K₀ * t ^ (-(N' : ℝ)) * ‖(ι ξ : mixedSpace F)‖ ^ (-p)) :=
    hmajS.mul_left _
  have hsum : Summable term := Summable.of_nonneg_of_le hnn hpt hmaj
  refine ⟨by simpa only [hterm] using hsum, ?_⟩
  have hle : ∑' ξ, term ξ ≤ K₀ * S * t ^ (-(N' : ℝ)) := by
    calc ∑' ξ, term ξ ≤ ∑' ξ : {ξ : F // ξ ≠ 0 ∧ ξ ∈ I}, K₀ * t ^ (-(N' : ℝ)) * ‖(ι ξ : mixedSpace F)‖ ^ (-p) :=
          hsum.tsum_le_tsum hpt hmaj
      _ = K₀ * t ^ (-(N' : ℝ)) * ∑' ξ : {ξ : F // ξ ≠ 0 ∧ ξ ∈ I}, ‖(ι ξ : mixedSpace F)‖ ^ (-p) := tsum_mul_left
      _ ≤ K₀ * t ^ (-(N' : ℝ)) * S := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hK₀0 (Real.rpow_nonneg ht0.le _))
          have hcmp := tsum_comp_le_tsum_of_inj (f := fun x : L => ‖x‖ ^ (-p)) hS
            (fun x => Real.rpow_nonneg (norm_nonneg _) _) hι
          exact hcmp
      _ = K₀ * S * t ^ (-(N' : ℝ)) := mul_right_comm _ _ _
  simpa only [hterm] using hle

end NumberField.mixedEmbedding

theorem NumberField.mixedEmbedding.traceForm_mixedSpace_nondegenerate
    (K : Type*) [Field K] [NumberField K] :
    (Algebra.traceForm ℝ (mixedSpace K)).Nondegenerate := by
  apply LinearMap.BilinForm.nondegenerate_of_det_ne_zero _ (latticeBasis K)
  have h : LinearMap.BilinForm.toMatrix (latticeBasis K) (Algebra.traceForm ℝ (mixedSpace K))
      = (Algebra.traceMatrix ℚ (integralBasis K)).map (algebraMap ℚ ℝ) := by
    ext i j
    rw [Algebra.traceForm_toMatrix, Matrix.map_apply, Algebra.traceMatrix_apply,
      latticeBasis_apply, latticeBasis_apply, ← map_mul, NumberField.mixedEmbedding.trace_mixedEmbedding,
      Algebra.traceForm_apply, eq_ratCast]
  rw [h, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← Algebra.discr_def, map_ne_zero]
  exact Algebra.discr_not_zero_of_basis ℚ (integralBasis K)
