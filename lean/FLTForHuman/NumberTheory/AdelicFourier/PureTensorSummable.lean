/-
A pure-tensor function is summable along the rational embedding.

`NumberField.AdelicFourier.summable_comp_algebraMap_of_mem_pureTensorSet` (86 pin lines): for a function
`f : AdeleRing (𝓞 F) F → ℂ` in the pure-tensor set, `ξ ↦ f (algebraMap F (𝓞 F) F ξ)` is summable over
`F` — the summability the Poisson-summation arguments take as their first input, and the reason the
`AdelicFourier` family exists.

The home is a new module of that family because the row cannot live in
`NumberTheory/AdelicFourier.lean` itself: its premise `AdelicBox.Measure` reaches that module through
`AdelicFourier/Transform.lean`, so the insertion is a cycle (measured).  This module sits above both.

## The rows

* `NumberField.AdelicFourier.summable_comp_algebraMap_of_mem_pureTensorSet` — 86 pin `S_` lines.

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_NumberField_AdelicFourier_summable_comp_algebraMap_of_mem_pureTensorSet.lean>

spec-pin: Theorems/Thm_NumberField_AdelicFourier_summable_comp_algebraMap_of_mem_pureTensorSet.lean
spec-pin: P2M/Sol/S_NumberField_AdelicFourier_summable_comp_algebraMap_of_mem_pureTensorSet.lean

## Landing (AF108H, pin `aa2d8b3` against the port's mathlib `v4.34.0`)

* **Surface.** One public declaration, the headline, at the wrapper's name; 106 lines against
  the pin's 86.
* **Substitutions**: none — no port copy of this statement existed. **No import was added**.
* **Drift (body and `open`s only).** Three `open`s the pin's own `S_` file carries were added
  to the scaffold's list — `IsDedekindDomain` (for `FiniteAdeleRing`),
  `NumberField.mixedEmbedding` (for `mixedSpace`) and `open scoped Classical`. Two `simp only`
  argument lists lost one argument each (`MonoidHom.coe_coe`, `Units.val_mk0`), measured
  unused by `linter.unusedSimpArgs` on this mathlib. Nothing else moved.
* **`check_port`**: **1 ok / 0 mismatch / 0 missing / 0 own / 0 kw**.
* **Engine gate**: pin sources 2, pin decls 2, module decls 1; **1 by hash**, 0 by name (hash
  differs), 0 unaccounted.
* **Axioms**: `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
* **`dedup --within`**: 0 clusters. **`move_dead --dry-run`**: 0 declarations, 0 lines.
* **Heartbeat probe** (recorded, **never installed**): **silent at 10000, timeout at 5000**
  (`isDefEq`, at the `show (↑dF)⁻¹ * (a : F) = κ` of the vanishing branch).
-/

import FLTForHuman.NumberTheory.AdelicBox.Measure
import FLTForHuman.NumberTheory.NumberField.MixedEmbedding
import FLTForHuman.NumberTheory.AdelicFourier
import Mathlib.Tactic

open NumberField NumberField.AdelicFourier MeasureTheory IsDedekindDomain NumberField.mixedEmbedding
open scoped SchwartzMap Classical

set_option autoImplicit false

theorem NumberField.AdelicFourier.summable_comp_algebraMap_of_mem_pureTensorSet
    {F : Type*} [Field F] [NumberField F]
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ pureTensorSet F) :
    Summable fun ξ : F => f (algebraMap F (AdeleRing (𝓞 F) F) ξ) := by
  classical
  obtain ⟨g, h, hlc, hcs, heq⟩ := hf
  subst heq

  have hmixed : ∀ κ : F,
      InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (AdeleRing (𝓞 F) F) κ).1
        = mixedEmbedding F κ := fun κ =>
    (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp (K := F) (x := κ)).symm
  have hsnd : ∀ κ : F, (algebraMap F (AdeleRing (𝓞 F) F) κ).2
      = algebraMap F (FiniteAdeleRing (𝓞 F) F) κ := fun _ => rfl
  simp only [hmixed, hsnd]

  obtain ⟨d, hd_ne, hd⟩ := NumberField.AdelicBox.exists_denom_of_hasCompactSupport hcs

  obtain ⟨M, hM⟩ : ∃ M, ∀ y, ‖h y‖ ≤ M := by
    obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hlc.continuous
    exact ⟨C, hC⟩

  have hdF_ne : (d : F) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hd_ne
  let dF : Fˣ := Units.mk0 (d : F) hdF_ne
  let c : (mixedSpace F)ˣ := (Units.map (mixedEmbedding F).toMonoidHom dF)⁻¹

  let mulC : mixedSpace F ≃L[ℝ] mixedSpace F :=
    { toFun := fun z => (c : mixedSpace F) * z
      invFun := fun z => ((c⁻¹ : (mixedSpace F)ˣ) : mixedSpace F) * z
      map_add' := mul_add _
      map_smul' := fun r z => mul_smul_comm r (c : mixedSpace F) z
      left_inv := fun z => by
        show ((c⁻¹ : (mixedSpace F)ˣ) : mixedSpace F) * ((c : mixedSpace F) * z) = z
        rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
      right_inv := fun z => by
        show (c : mixedSpace F) * (((c⁻¹ : (mixedSpace F)ˣ) : mixedSpace F) * z) = z
        rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
      continuous_toFun := continuous_const.mul continuous_id
      continuous_invFun := continuous_const.mul continuous_id }

  let g' : 𝓢(mixedSpace F, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ mulC g
  have hg' : ∀ z, g' z = g ((c : mixedSpace F) * z) := fun z => by
    simp [g', mulC, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]

  let e : 𝓞 F → F := fun a => (dF : F)⁻¹ * (a : F)
  have he_inj : Function.Injective e := fun a b hab =>
    RingOfIntegers.coe_injective (mul_left_cancel₀ (inv_ne_zero hdF_ne) hab)

  refine (he_inj.summable_iff (fun κ hκ => ?_)).mp ?_
  · rw [mul_eq_zero]; right
    by_contra hne
    obtain ⟨a, ha⟩ := hd κ hne
    refine hκ ⟨a, ?_⟩
    show (↑dF)⁻¹ * (a : F) = κ
    rw [← ha, Units.val_mk0, inv_mul_cancel_left₀ hdF_ne]

  refine Summable.of_norm_bounded
    ((summable_norm_schwartzMap_ringOfIntegers_translate F g' 0).mul_left M) (fun a => ?_)
  have hc_eq : (c : mixedSpace F) = mixedEmbedding F ((dF : F)⁻¹) := by
    have : ((Units.map (mixedEmbedding F).toMonoidHom dF)⁻¹ : (mixedSpace F)ˣ)
        = Units.map (mixedEmbedding F).toMonoidHom dF⁻¹ := (map_inv _ _).symm
    simp only [c, this, Units.coe_map, Units.val_inv_eq_inv_val]
    rfl
  have hme : mixedEmbedding F (e a) = (c : mixedSpace F) * mixedEmbedding F (a : F) := by
    simp only [e, map_mul, hc_eq]
  calc ‖g (mixedEmbedding F (e a)) * h (algebraMap F (FiniteAdeleRing (𝓞 F) F) (e a))‖
      = ‖g' (0 + mixedEmbedding F (a : F))‖
          * ‖h (algebraMap F (FiniteAdeleRing (𝓞 F) F) (e a))‖ := by
        rw [norm_mul, hg', zero_add, hme]
    _ ≤ ‖g' (0 + mixedEmbedding F (a : F))‖ * M :=
        mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
    _ = M * ‖g' (0 + mixedEmbedding F (a : F))‖ := mul_comm _ _
