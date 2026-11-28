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

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_MeasureTheory_finiteDimensional_and_finrank_le_of_forall_norm_le_mul_eLpNorm_restrict.lean>
  spec-pin: Theorems/Thm_MeasureTheory_finiteDimensional_and_finrank_le_of_forall_norm_le_mul_eLpNorm_restrict.lean
  spec-pin: P2M/Sol/S_MeasureTheory_finiteDimensional_and_finrank_le_of_forall_norm_le_mul_eLpNorm_restrict.lean

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

## Landing (AF108H) — the norm-`eLpNorm` restrict row

A sixth declaration joins the five:
`finiteDimensional_and_finrank_le_of_forall_norm_le_mul_eLpNorm_restrict`, the norm-`eLpNorm`
variant of this module's `∀ᵐ ‖φ x‖ ≤ C ‖φ‖` row — the same `L²`-compactness lemma in the form
the spectral arguments use. It is the honest derivation the order allowed for: the proof embeds
`V` into `Lp ℂ 2 (μ.restrict s)` and feeds the AE-form row, so no second version of the
compactness engine was needed. 275 lines (215 before); `check_port`
**6 ok / 0 mismatch / 0 missing / 0 own / 0 kw**. No substitution, no import added.

* **API drift, body only** (`v4.33.1` → `v4.34.0`, the same class the module's own row hit):
  `MemLp` is now the `def` `eLpNorm f p μ < ∞`, so the pin's structure witness
  `⟨hmeas φ hφ, htop⟩` is the single term `htop` and the measurability hypothesis (still in the
  statement) is consumed by an anonymous `have` at the head of `hW`, with the reason recorded
  there; `eLpNorm_eq_zero_iff` now takes only `p ≠ 0` (the `AEStronglyMeasurable` argument is
  gone); `haveI : IsFiniteMeasure (μ.restrict s)` and `haveI := hfin` became `have` per
  `linter.style.haveILetI`. No linter is silenced.
* **Engine gate**: pin sources 4, pin decls 8, module decls 6; **6 by hash**, 0 by name (hash
  differs), 0 unaccounted.
* **`dedup --within`**: 0 clusters. **`move_dead --dry-run`**: 0 declarations, 0 lines.
* **Axioms**: all six public declarations, `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
* **Heartbeat probe** (recorded, **never installed**): **silent at 40000, timeout at 20000**
  (`isDefEq`, `card_le_of_orthonormal`'s `Fin (Module.finrank 𝕜 W)`) — the pair AF107F recorded
  for this module, unchanged by the new row.
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

theorem MeasureTheory.finiteDimensional_and_finrank_le_of_forall_norm_le_mul_eLpNorm_restrict
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (s : Set X) (hsm : MeasurableSet s) (hs : μ s ≠ ⊤)
    (V : Submodule ℂ (X → ℂ))
    (hmeas : ∀ φ ∈ V, AEStronglyMeasurable φ (μ.restrict s))
    (hinj : ∀ φ ∈ V, (∀ x ∈ s, φ x = 0) → φ = 0)
    (C : ℝ)
    (hsup : ∀ φ ∈ V, ∀ x ∈ s, ‖φ x‖ ≤ C * (eLpNorm φ 2 (μ.restrict s)).toReal) :
    FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℝ) ≤ C ^ 2 * (μ s).toReal := by
  classical
  have hfinμ : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.mpr hs

  have hzero : ∀ φ ∈ V, eLpNorm φ 2 (μ.restrict s) = 0 → φ = 0 := by
    intro φ hφ h0
    refine hinj φ hφ fun x hx => ?_
    have h := hsup φ hφ x hx
    rw [h0, ENNReal.toReal_zero, mul_zero] at h
    exact norm_le_zero_iff.mp h

  have hW : ∀ φ ∈ V, MemLp φ 2 (μ.restrict s) := by
    intro φ hφ
    -- API drift (`v4.33.1` → `v4.34.0`): `MemLp` is now the `def` `eLpNorm f p μ < ∞`, so the pin's
    -- structure witness `⟨hmeas φ hφ, htop⟩` has one field left; the measurability hypothesis is
    -- consumed here instead (it is part of the statement, and the pin's `MemLp` carried it).
    have : AEStronglyMeasurable φ (μ.restrict s) := hmeas φ hφ
    by_cases htop : eLpNorm φ 2 (μ.restrict s) < ⊤
    · exact htop
    · have hinf : eLpNorm φ 2 (μ.restrict s) = ⊤ := not_lt_top_iff.mp htop
      have hφ0 : φ = 0 := by
        refine hinj φ hφ fun x hx => ?_
        have h := hsup φ hφ x hx
        rw [hinf, ENNReal.toReal_top, mul_zero] at h
        exact norm_le_zero_iff.mp h
      rw [hφ0]
      exact MemLp.zero

  let L : ↥V →ₗ[ℂ] ↥(Lp ℂ 2 (μ.restrict s)) :=
    { toFun := fun w => (hW w w.2).toLp (w : X → ℂ)
      map_add' := fun w w' => by
        have h := MemLp.toLp_add (hW w w.2) (hW w' w'.2)
        exact h
      map_smul' := fun c w => by
        have h := MemLp.toLp_const_smul c (hW w w.2)
        exact h }
  have hL : ∀ w : ↥V, L w = (hW w w.2).toLp (w : X → ℂ) := fun _ => rfl
  have hLinj : Function.Injective L := by
    intro w w' h
    have h0 : L (w - w') = 0 := by rw [map_sub, h, sub_self]
    have hae : ((w - w' : ↥V) : X → ℂ) =ᵐ[μ.restrict s] 0 := by
      have h1 : ((L (w - w') : ↥(Lp ℂ 2 (μ.restrict s))) : X → ℂ) =ᵐ[μ.restrict s] ((w - w' : ↥V) : X → ℂ) :=
        MemLp.coeFn_toLp (hW (w - w') (w - w').2)
      rw [h0] at h1
      exact h1.symm.trans (Lp.coeFn_zero ℂ 2 (μ.restrict s))
    have hnorm : eLpNorm ((w - w' : ↥V) : X → ℂ) 2 (μ.restrict s) = 0 :=
      (eLpNorm_eq_zero_iff two_ne_zero).mpr hae
    exact sub_eq_zero.mp (Subtype.ext (hzero _ (w - w').2 hnorm))

  have hVim : ∀ φ ∈ LinearMap.range L, ∀ᵐ x ∂(μ.restrict s), ‖(φ : X → ℂ) x‖ ≤ C * ‖φ‖ := by
    rintro _ ⟨w, rfl⟩
    rw [hL, Lp.norm_toLp]
    filter_upwards [MemLp.coeFn_toLp (hW w w.2), ae_restrict_mem hsm] with x hx hxs
    rw [hx]
    exact hsup _ w.2 x hxs
  obtain ⟨hfin, hrank⟩ :=
    MeasureTheory.Lp.finiteDimensional_and_finrank_le_of_forall_ae_norm_le_mul_norm (LinearMap.range L) C hVim
  have hfin' := hfin
  have hfinV : FiniteDimensional ℂ ↥V := Module.Finite.equiv (LinearEquiv.ofInjective L hLinj).symm
  refine ⟨hfinV, ?_⟩
  rw [← LinearMap.finrank_range_of_inj hLinj, ← Measure.restrict_apply_univ s]
  exact hrank
