/-
Every log-embedding vector is within `R` of a unit's.

`NumberField.Units.exists_forall_abs_sub_mult_mul_log_le`: for every `t : InfinitePlace F → ℝ` with
`∑ w, t w = 0` there is a unit `u : (𝓞 K)ˣ` whose log-embedding `w ↦ mult w * log (w u)` is within a
uniform `R` of `t`. It is the compactness of the log-unit lattice's fundamental parallelepiped — the
`ℓ∞` form of Dirichlet's unit theorem that the height machinery consumes.

Home `NumberTheory/NumberField/UnitsLog.lean` (new; the port has no `Units` module of its own).

## The rows

* `NumberField.Units.exists_forall_abs_sub_mult_mul_log_le` — 98 pin `S_` lines.

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_NumberField_Units_exists_forall_abs_sub_mult_mul_log_le.lean>

spec-pin: Theorems/Thm_NumberField_Units_exists_forall_abs_sub_mult_mul_log_le.lean
spec-pin: P2M/Sol/S_NumberField_Units_exists_forall_abs_sub_mult_mul_log_le.lean

## Port notes (order AF107F)

* **Surface = the pin's.** 3 declarations, 3 public / 0 private, against the pin's 4 entries
  (`Theorems/Thm_…` + `S_…`'s `exists_norm_sub_logEmbedding_le`,
  `exists_forall_abs_sub_mult_mul_log_le_impl`, `solution` — the last being the same statement
  as the `Thm_…` wrapper). 4 − 1 = 3.
* **`check_port`**: 3 ok, 0 mismatch, 0 missing, 0 own, 0 kw.
* **Substitutions**: none; the log-unit lattice engine these rows balance against
  (`logSpace`, `logEmbedding`, `unitLattice`, `w₀` and `ZSpan`) is mathlib's, and the scaffold's
  import list carried every proof, so no import was added.
* **API drift** (`v4.33.1` → `v4.34.0`): none. The pin's proof transcribes verbatim, including
  the new `ZSpan`/`Basis.ofZLatticeBasis` API it was written against. The pin's free `w₀` is
  mathlib's `NumberField.Units.dirichletUnitTheorem.w₀`, so nothing had to be invented.
* **Namespaces**: the pin's generated `M4aP1R` label is replaced by `NumberField.Units.UnitBalance`;
  the pin's declaration names are kept.
* **Axioms**: all 3 public declarations depend on a subset of
  `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.
* **`dedup --within`**: 1 cluster, 8 lines — `exists_forall_abs_sub_mult_mul_log_le_impl` ↔
  `exists_forall_abs_sub_mult_mul_log_le` (identical statements). This is the pin's own
  headline↔engine pair, kept for faithfulness.
* **`move_dead --dry-run`**: 0 declarations, 0 lines.
* **Heartbeat probe (recorded, never installed)**: downward ladder 40000 / 20000 / 10000 pass,
  5000 and 1000 fail — at `_impl`'s `(Fintype.card {w : InfinitePlace K // w ≠ w₀} : ℝ)` (`whnf`).
  Module floor passes at 1000, so the cost is in the proof term, not the types.
-/

import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

open NumberField NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem
open Module
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace NumberField.Units

namespace UnitBalance

variable (K : Type*) [Field K] [NumberField K]

theorem exists_norm_sub_logEmbedding_le :
    ∃ R₀ : ℝ, 0 ≤ R₀ ∧ ∀ t' : logSpace K, ∃ u : (𝓞 K)ˣ,
      ‖t' - logEmbedding K (Additive.ofMul u)‖ ≤ R₀ := by
  classical
  let L : Submodule ℤ (logSpace K) := unitLattice K
  let b := Module.Free.chooseBasis ℤ L
  let B : Basis _ ℝ (logSpace K) := b.ofZLatticeBasis ℝ L
  refine ⟨∑ i, ‖B i‖, Finset.sum_nonneg fun i _ => norm_nonneg _, fun t' => ?_⟩

  have hv : t' - ZSpan.fract B t' ∈ L := by
    have h1 : t' - ZSpan.fract B t' = (ZSpan.floor B t' : logSpace K) := by
      rw [ZSpan.fract_apply]; abel
    rw [h1]
    exact (b.ofZLatticeBasis_span ℝ L).le (ZSpan.floor B t').2
  obtain ⟨x, -, hx⟩ := Submodule.mem_map.mp hv
  refine ⟨Additive.toMul x, ?_⟩
  have hx' : logEmbedding K (Additive.ofMul (Additive.toMul x)) = t' - ZSpan.fract B t' := by
    rw [ofMul_toMul]; exact hx
  rw [hx', sub_sub_cancel]
  exact ZSpan.norm_fract_le B t'

end UnitBalance

open UnitBalance in
theorem UnitBalance.exists_forall_abs_sub_mult_mul_log_le_impl (K : Type*) [Field K]
    [NumberField K] : ∃ R : ℝ, ∀ t : NumberField.InfinitePlace K → ℝ, ∑ w, t w = 0 →
      ∃ u : (NumberField.RingOfIntegers K)ˣ, ∀ w : NumberField.InfinitePlace K,
        |t w - (w.mult : ℝ) * Real.log (w (u : K))| ≤ R := by
  classical
  obtain ⟨R₀, hR₀, hcov⟩ := exists_norm_sub_logEmbedding_le K
  refine ⟨(Fintype.card (InfinitePlace K)) * R₀, fun t ht => ?_⟩

  obtain ⟨u, hu⟩ := hcov (fun w => t w.val)
  refine ⟨u, fun w => ?_⟩

  have hdev : ∀ w' : {w : InfinitePlace K // w ≠ w₀},
      |t w'.val - (w'.val.mult : ℝ) * Real.log (w'.val (u : K))| ≤ R₀ := by
    intro w'
    have h1 := norm_le_pi_norm ((fun w => t w.val) - logEmbedding K (Additive.ofMul u)) w'
    rw [Pi.sub_apply, logEmbedding_component, Real.norm_eq_abs] at h1
    exact h1.trans hu
  have hcard1 : (1 : ℝ) ≤ Fintype.card (InfinitePlace K) := by
    exact_mod_cast Fintype.card_pos
  have hcard2 : (Fintype.card {w : InfinitePlace K // w ≠ w₀} : ℝ)
      ≤ Fintype.card (InfinitePlace K) := by
    exact_mod_cast Fintype.card_subtype_le _
  by_cases hw : w = w₀
  ·
    subst hw
    have hsumt : t w₀ + ∑ w' : {w : InfinitePlace K // w ≠ w₀}, t w'.val = 0 := by
      rw [← Fintype.sum_eq_add_sum_subtype_ne t w₀]; exact ht
    have hsumu : ∑ w' : {w : InfinitePlace K // w ≠ w₀},
        (w'.val.mult : ℝ) * Real.log (w'.val (u : K))
          = -((w₀ : InfinitePlace K).mult : ℝ) * Real.log (w₀ (u : K)) := by
      have := sum_logEmbedding_component u
      simpa [logEmbedding_component] using this
    have hkey : t w₀ - ((w₀ : InfinitePlace K).mult : ℝ) * Real.log (w₀ (u : K))
        = -∑ w' : {w : InfinitePlace K // w ≠ w₀},
            (t w'.val - (w'.val.mult : ℝ) * Real.log (w'.val (u : K))) := by
      rw [Finset.sum_sub_distrib, hsumu]; linarith
    rw [hkey, abs_neg]
    calc |∑ w' : {w : InfinitePlace K // w ≠ w₀},
            (t w'.val - (w'.val.mult : ℝ) * Real.log (w'.val (u : K)))|
        ≤ ∑ w' : {w : InfinitePlace K // w ≠ w₀},
            |t w'.val - (w'.val.mult : ℝ) * Real.log (w'.val (u : K))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _w' : {w : InfinitePlace K // w ≠ w₀}, R₀ := Finset.sum_le_sum fun w' _ => hdev w'
      _ = (Fintype.card {w : InfinitePlace K // w ≠ w₀} : ℝ) * R₀ := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      _ ≤ (Fintype.card (InfinitePlace K) : ℝ) * R₀ :=
          mul_le_mul_of_nonneg_right hcard2 hR₀
  · calc |t w - (w.mult : ℝ) * Real.log (w (u : K))|
        ≤ R₀ := hdev ⟨w, hw⟩
      _ = 1 * R₀ := (one_mul _).symm
      _ ≤ (Fintype.card (InfinitePlace K) : ℝ) * R₀ := mul_le_mul_of_nonneg_right hcard1 hR₀

open scoped Classical in
theorem exists_forall_abs_sub_mult_mul_log_le (K : Type*) [Field K]
    [NumberField K] : ∃ R : ℝ, ∀ t : NumberField.InfinitePlace K → ℝ, ∑ w, t w = 0 →
      ∃ u : (NumberField.RingOfIntegers K)ˣ, ∀ w : NumberField.InfinitePlace K,
        |t w - (w.mult : ℝ) * Real.log (w (u : K))| ≤ R :=
  UnitBalance.exists_forall_abs_sub_mult_mul_log_le_impl K

end NumberField.Units
