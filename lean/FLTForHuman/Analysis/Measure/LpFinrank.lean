/-
A uniform `L∞` bound forces finite dimension, with a quantitative bound.

`MeasureTheory.Lp.finiteDimensional_and_finrank_le_of_forall_ae_norm_le_mul_norm`: a submodule `V` of
`L²(μ)` all of whose elements are a.e. bounded by `C ‖φ‖` is finite-dimensional and
`finrank V ≤ C² μ(univ)`. It is the quantitative form of the `L²`-compactness lemma the spectral
arguments use, and the port has it nowhere.

Home `Analysis/Measure/` (new directory): the statement is pure measure theory and names no number
field.

## The rows

* `MeasureTheory.Lp.finiteDimensional_and_finrank_le_of_forall_ae_norm_le_mul_norm` — 148 pin `S_` lines.

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_MeasureTheory_Lp_finiteDimensional_and_finrank_le_of_forall_ae_norm_le_mul_norm.lean>

spec-pin: Theorems/Thm_MeasureTheory_Lp_finiteDimensional_and_finrank_le_of_forall_ae_norm_le_mul_norm.lean
spec-pin: P2M/Sol/S_MeasureTheory_Lp_finiteDimensional_and_finrank_le_of_forall_ae_norm_le_mul_norm.lean

## Port notes (order AF107F)

* **Surface = the pin's.** 5 declarations, 5 public / 0 private, against the pin's 6 entries
  (`Theorems/Thm_…` + `S_…`'s `coeFn_finset_sum`, `norm_sq_eq_integral`, `integrable_norm_sq`,
  `card_le_of_orthonormal`, `solution` — the last being the same statement as the `Thm_…`
  wrapper). 6 − 1 = 5.
* **`check_port`**: 5 ok, 0 mismatch, 0 missing, 0 own, 0 kw.
* **Substitutions**: none; the pin's own proof is the cheapest route and the scaffold's import
  list carried it — no import was added, and the pin's bare `import Mathlib` was **not**
  transcribed.
* **API drift** (`v4.33.1` → `v4.34.0`): `MemLp` became a `def` (`eLpNorm f p μ < ∞`) rather
  than a structure, so the pin's `(Lp.memLp φ).1` is now `(Lp.memLp φ).aestronglyMeasurable`;
  and the pin's `haveI : FiniteDimensional 𝕜 W` (a `Prop`) became `have` per
  `linter.style.haveILetI`. The pin's constant `C ^ 2 * μ(univ)` form needed no different
  `Lp`-API route — `card_le_of_orthonormal` proves it exactly as the pin does.
* **Axioms**: all 5 public declarations depend on a subset of
  `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.
* **`dedup --within`**: 0 clusters. **`move_dead --dry-run`**: 0 declarations, 0 lines.
* **Heartbeat probe (recorded, never installed)**: downward ladder 1000 / 5000 / 10000 / 20000
  fail, 40000 passes — the first failing site is `card_le_of_orthonormal`'s
  `Fin (Module.finrank 𝕜 W)` (`isDefEq`). Module floor **fails at 1000 and passes at
  2000** (its failing site is the type of `norm_sq_eq_integral`, an instance-search timeout), so
  part of this module's cost is in the statements, not only in the proofs.
-/

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate

set_option autoImplicit false

noncomputable section

namespace MeasureTheory.Lp

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {𝕜 : Type*} [RCLike 𝕜]

theorem coeFn_finset_sum {ι : Type*} {p : ℝ≥0∞} (s : Finset ι) (f : ι → Lp 𝕜 p μ) :
    (((∑ i ∈ s, f i : Lp 𝕜 p μ) : X → 𝕜)) =ᵐ[μ] fun x => ∑ i ∈ s, (f i : X → 𝕜) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero 𝕜 p μ] with x hx
    exact hx
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ s, f i), ih] with x hx hix
    rw [hx, Pi.add_apply, hix]

theorem norm_sq_eq_integral (φ : Lp 𝕜 2 μ) : ‖φ‖ ^ 2 = ∫ x, ‖(φ : X → 𝕜) x‖ ^ 2 ∂μ := by
  rw [← @inner_self_eq_norm_sq 𝕜, L2.inner_def]
  simp_rw [inner_self_eq_norm_sq_to_K]
  have : (fun a => ((‖(φ : X → 𝕜) a‖ : 𝕜) ^ 2)) = fun a => (((‖(φ : X → 𝕜) a‖ ^ 2 : ℝ)) : 𝕜) := by
    funext a; push_cast; rfl
  rw [this, integral_ofReal, RCLike.ofReal_re]

theorem integrable_norm_sq (φ : Lp 𝕜 2 μ) : Integrable (fun x => ‖(φ : X → 𝕜) x‖ ^ 2) μ :=
  (memLp_two_iff_integrable_sq_norm (Lp.memLp φ).aestronglyMeasurable).mp (Lp.memLp φ)

theorem card_le_of_orthonormal [IsFiniteMeasure μ] (C : ℝ) {m : ℕ} (e : Fin m → Lp 𝕜 2 μ) (he : Orthonormal 𝕜 e)
    (hb : ∀ c : Fin m → 𝕜, ∀ᵐ x ∂μ, ‖((∑ i, c i • e i : Lp 𝕜 2 μ) : X → 𝕜) x‖ ≤ C * ‖∑ i, c i • e i‖) :
    (m : ℝ) ≤ C ^ 2 * (μ Set.univ).toReal := by

  have hnorm : ∀ c : EuclideanSpace 𝕜 (Fin m), ‖∑ i, c i • e i‖ = ‖c‖ := by
    intro c
    have h1 : ‖∑ i, c i • e i‖ ^ 2 = ‖c‖ ^ 2 := by
      rw [← @inner_self_eq_norm_sq 𝕜, he.inner_sum, EuclideanSpace.norm_sq_eq, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [RCLike.conj_mul]; norm_cast
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1

  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq (EuclideanSpace 𝕜 (Fin m))
  have hae : ∀ᵐ x ∂μ, ∀ k, ‖∑ i, u k i * (e i : X → 𝕜) x‖ ≤ C * ‖u k‖ := by
    rw [ae_all_iff]
    intro k
    filter_upwards [hb (u k), coeFn_finset_sum Finset.univ (fun i => u k i • e i),
      ae_all_iff.mpr fun i => Lp.coeFn_smul (u k i) (e i)] with x hx hsum hsmul
    rw [hnorm] at hx
    rw [hsum] at hx
    simp only [hsmul, Pi.smul_apply, smul_eq_mul] at hx
    exact hx

  have hall : ∀ᵐ x ∂μ, ∀ c : EuclideanSpace 𝕜 (Fin m), ‖∑ i, c i * (e i : X → 𝕜) x‖ ≤ C * ‖c‖ := by
    filter_upwards [hae] with x hx
    have hclosed : IsClosed {c : EuclideanSpace 𝕜 (Fin m) | ‖∑ i, c i * (e i : X → 𝕜) x‖ ≤ C * ‖c‖} := by
      refine isClosed_le ?_ (by fun_prop)
      refine Continuous.norm (continuous_finsetSum _ fun i _ => ?_)
      exact (PiLp.continuous_apply 2 _ i).mul continuous_const
    intro c
    have hc : c ∈ closure (Set.range u) := by rw [hu.closure_range]; exact Set.mem_univ c
    exact hclosed.closure_subset_iff.mpr (Set.range_subset_iff.mpr hx) hc

  set s : X → ℝ := fun x => ∑ i, ‖(e i : X → 𝕜) x‖ ^ 2 with hs_def
  have hs_nonneg : ∀ x, 0 ≤ s x := fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hs : ∀ᵐ x ∂μ, s x ≤ C ^ 2 := by
    filter_upwards [hall] with x hx
    let c : EuclideanSpace 𝕜 (Fin m) := WithLp.toLp 2 fun i => conj ((e i : X → 𝕜) x)
    have hcx : ∑ i, c i * (e i : X → 𝕜) x = ((s x : ℝ) : 𝕜) := by
      simp only [hs_def, c]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      exact RCLike.conj_mul _
    have hcn : ‖c‖ = Real.sqrt (s x) := by
      rw [EuclideanSpace.norm_eq]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [c]
    have h := hx c
    rw [hcx, hcn, RCLike.norm_ofReal, abs_of_nonneg (hs_nonneg x)] at h

    by_cases h0 : s x = 0
    · rw [h0]; exact sq_nonneg C
    · have hpos : 0 < Real.sqrt (s x) := Real.sqrt_pos.mpr (lt_of_le_of_ne (hs_nonneg x) (Ne.symm h0))
      have hsq : Real.sqrt (s x) * Real.sqrt (s x) = s x := Real.mul_self_sqrt (hs_nonneg x)
      have hle : Real.sqrt (s x) ≤ C := by
        have : Real.sqrt (s x) * Real.sqrt (s x) ≤ C * Real.sqrt (s x) := by rw [hsq]; exact h
        exact le_of_mul_le_mul_right this hpos
      calc s x = Real.sqrt (s x) ^ 2 := by rw [sq, hsq]
        _ ≤ C ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hle 2

  have hint : Integrable s μ := integrable_finsetSum _ fun i _ => integrable_norm_sq (e i)
  have h1 : ∫ x, s x ∂μ = m := by
    simp only [hs_def]
    rw [integral_finsetSum _ fun i _ => integrable_norm_sq (e i)]
    simp_rw [← norm_sq_eq_integral, he.norm_eq_one]
    simp
  have h2 : ∫ x, s x ∂μ ≤ ∫ _x, C ^ 2 ∂μ := integral_mono_ae hint (integrable_const _) hs
  rw [h1, integral_const, smul_eq_mul, measureReal_def] at h2
  linarith

open scoped Classical in
theorem finiteDimensional_and_finrank_le_of_forall_ae_norm_le_mul_norm
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ] {𝕜 : Type*} [RCLike 𝕜]
    (V : Submodule 𝕜 (Lp 𝕜 2 μ)) (C : ℝ)
    (hV : ∀ φ ∈ V, ∀ᵐ x ∂μ, ‖(φ : X → 𝕜) x‖ ≤ C * ‖φ‖) :
    FiniteDimensional 𝕜 V ∧ (Module.finrank 𝕜 V : ℝ) ≤ C ^ 2 * (μ Set.univ).toReal := by

  set N : ℕ := ⌊C ^ 2 * (μ Set.univ).toReal⌋₊ with hN
  have hNN : (0 : ℝ) ≤ C ^ 2 * (μ Set.univ).toReal := mul_nonneg (sq_nonneg C) ENNReal.toReal_nonneg
  have key : ∀ s : Finset V, (LinearIndependent 𝕜 fun i : s => (i : V)) → s.card ≤ N := by
    intro s hs

    have hs' : LinearIndependent 𝕜 fun i : s => ((i : V) : Lp 𝕜 2 μ) :=
      hs.map' V.subtype (Submodule.ker_subtype V)
    set W : Submodule 𝕜 (Lp 𝕜 2 μ) := Submodule.span 𝕜 (Set.range fun i : s => ((i : V) : Lp 𝕜 2 μ)) with hW
    have hWV : W ≤ V := by
      rw [hW, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact (i : V).2
    have : FiniteDimensional 𝕜 W := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range _)
    have hfr : Module.finrank 𝕜 W = s.card := by
      rw [hW, finrank_span_eq_card hs']; simp

    let b := stdOrthonormalBasis 𝕜 W
    let e : Fin (Module.finrank 𝕜 W) → Lp 𝕜 2 μ := fun i => (b i : Lp 𝕜 2 μ)
    have he : Orthonormal 𝕜 e := (W.subtypeₗᵢ.orthonormal_comp_iff).mpr b.orthonormal
    have hmem : ∀ c : Fin (Module.finrank 𝕜 W) → 𝕜, (∑ i, c i • e i : Lp 𝕜 2 μ) ∈ V :=
      fun c => V.sum_mem fun i _ => V.smul_mem _ (hWV (b i).2)
    have hle := card_le_of_orthonormal C e he fun c => hV _ (hmem c)
    rw [hfr] at hle
    exact Nat.le_floor hle
  have hrank : Module.rank 𝕜 V ≤ N := rank_le key
  have hfin : Module.Finite 𝕜 V := by
    rw [← Module.rank_lt_aleph0_iff]
    exact lt_of_le_of_lt hrank (Cardinal.natCast_lt_aleph0 (n := N))
  refine ⟨hfin, ?_⟩
  calc (Module.finrank 𝕜 V : ℝ) ≤ N := by exact_mod_cast Module.finrank_le_of_rank_le hrank
    _ ≤ C ^ 2 * (μ Set.univ).toReal := Nat.floor_le hNN

end MeasureTheory.Lp
