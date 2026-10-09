/-
X₁'s `FunctionFieldInclusion`: the two headlines comparing the `K`-general
divisor-generated function field `modularFunctionFieldFullC` of `X₀(N)` with the
two-generator field `modularFunctionFieldC` and with the `q`-expansion function
field `qExpFunctionFieldC` of `Γ₀(M)`.

* `modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charZero` — over a
  characteristic-zero field `K`, every `j(q ^ d)` with `d ∣ N` already lies in
  `K(j(q), j(q ^ N))`, so the two fields coincide. The inclusion `≤` is
  `modularFunctionFieldC_le_full`; the converse transports the `ℚ`-statement
  `functionFieldGeneration` across `coeffMap (algebraMap ℚ K)`, coefficientwise.
  Wrapper 11 ln, `S_` 46 ln:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charZero.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charZero.lean

* `modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0` — over any field `K`,
  the divisor-generated field `K(j(q ^ d) : d ∣ M)` sits in the `q`-expansion
  function field of `Γ₀(M)`: each generator `qExpand K d (jqModC K)` is the
  `q ↦ q ^ d` stretch of `jqModC K = E₄³ / Δ`, and `Γ₀(M) ≤ Γ₀(d)` for `d ∣ M`
  lets that stretch descend.
  Wrapper 12 ln, `S_` 42 ln:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0.lean

Both `S_` files prove their `solution` inline, with no auxiliary declaration, so
nothing is transcribed into a local `private` namespace here; the two headlines
are the module's only public declarations, and the only local helpers are the
`have hmem`/`have hle`/`have hdet` of the pin's own proof bodies.

The pin's two `haveI := hned` / `haveI := hd` walls are **dropped**, not
suppressed: in this mathlib a local hypothesis of class type already serves
instance search, so the `NeZero d` hypothesis bound by the `rintro` pattern of
`divisorExpansionsC` is already available to `qExpand K d` and to the
`[NeZero ℓ]` argument of `qExpand_image_intFormRatiosC_subset`. With the walls
gone the module needs no `linter.style.haveILetI` suppression at all.

Dedup against the port: `modularFunctionFieldC_le_full`, `coeffMap_jqModC` and
the whole `…FullC…` layer come from `ModularCurve/X0/FunctionFieldFull.lean`;
`functionFieldGeneration` from `FunctionFieldGeneration/Capstone.lean`;
`coeffMap_qExpand`/`coeffMap_single`/`algebraMap_laurentSeries_eq_single` from
`ModularCurve/Defs/Laurent.lean`; `qExpFunctionFieldC`/`intFormRatiosC_subset`/
`jqModC_mem_intFormRatiosC` from `JqIntegralRatios.lean`; `intFormRatiosC_mono`
from `X1/Defs.lean`; and `qExpand_image_intFormRatiosC_subset` from
`X1/QExpandStretch.lean`. The pin's `import Mathlib` is replaced by the
specific imports below, plus the `linear_combination` tactic module for the
`hΓ'` determinant identity.
-/
import FLTForHuman.ModularCurve.X0.FunctionFieldFull
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Capstone
import FLTForHuman.ModularCurve.X1.Defs
import FLTForHuman.ModularCurve.X1.QExpandStretch
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

noncomputable section

open IntermediateField

namespace ModularCurve

/-- **The two-generator field is the full divisor field, over any
characteristic-zero field.** Verbatim from
`Theorems/Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charZero.lean`.

The pin's `S_` proof: `modularFunctionFieldC_le_full` gives `≤`, and conversely
each generator `qExpand K d (jqModC K)` is the coefficient extension of
`qExpand ℚ d jq`, which lies in `modularFunctionField N` by
`functionFieldGeneration`; the `ℚ`-subfield `modularFunctionField N` therefore
maps into `modularFunctionFieldC K N` under `coeffMap (algebraMap ℚ K)`, and
`adjoin_le_subfield` converts that into the desired inclusion. The pin's
`attribute [-instance]`/`attribute [-simp]` preamble is a proof-support
annotation, not part of the statement, and is not used here. -/
theorem modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charZero
    (K : Type*) [Field K] [CharZero K] (N : ℕ) [NeZero N] :
    modularFunctionFieldC K N = modularFunctionFieldFullC K N := by
  refine le_antisymm (modularFunctionFieldC_le_full K N) ?_
  rw [modularFunctionFieldFullC, adjoin_le_iff]
  rintro x ⟨d, hned, hdvd, rfl⟩
  rw [show qExpand K d (jqModC K) = coeffMap (algebraMap ℚ K) (qExpand ℚ d jq) from by
    rw [← jqModC_rat, coeffMap_qExpand, coeffMap_jqModC]]
  have hmem : qExpand ℚ d jq ∈ modularFunctionField N :=
    functionFieldGeneration N d hdvd ‹NeZero d›
  have hle : (modularFunctionField N).toSubfield ≤
      Subfield.comap (coeffMap (algebraMap ℚ K)) (modularFunctionFieldC K N).toSubfield := by
    rw [modularFunctionField]
    refine IntermediateField.adjoin_le_subfield ℚ _ ?_ ?_
    · rintro _ ⟨c, rfl⟩
      show coeffMap (algebraMap ℚ K) (algebraMap ℚ (LaurentSeries ℚ) c) ∈
        (modularFunctionFieldC K N).toSubfield
      rw [algebraMap_laurentSeries_eq_single, coeffMap_single,
        ← algebraMap_laurentSeries_eq_single]
      exact (modularFunctionFieldC K N).algebraMap_mem _
    · rintro y (rfl | rfl)
      · show coeffMap (algebraMap ℚ K) jq ∈ (modularFunctionFieldC K N).toSubfield
        rw [← jqModC_rat, coeffMap_jqModC]
        exact jqModC_mem K N
      · show coeffMap (algebraMap ℚ K) (qExpand ℚ N jq) ∈
          (modularFunctionFieldC K N).toSubfield
        rw [← jqModC_rat, coeffMap_qExpand, coeffMap_jqModC]
        exact jqNModC_mem K N
  exact hle hmem

/-- **The full divisor field sits in the `q`-expansion function field of
`Γ₀(M)`.** Verbatim from
`Theorems/Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0.lean`.

The pin's `S_` proof: a generator `qExpand K d (jqModC K)` with `d ∣ M` is the
stretch of `jqModC K ∈ intFormRatiosC K ⊤` along `q ↦ q ^ d`; since `d ∣ M` gives
`Γ₀(M) ≤ Γ₀(d)`, `intFormRatiosC_mono` descends the ratio set of `Γ₀(d)` to that
of `Γ₀(M)`, and `intFormRatiosC_subset` lands in `qExpFunctionFieldC K (Γ₀ M)`.
The pin's `attribute [-instance]`/`attribute [-simp]` preamble is a
proof-support annotation, not part of the statement, and is not used here. -/
theorem modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
    (K : Type*) [Field K] (M : ℕ) [NeZero M] :
    ModularCurve.modularFunctionFieldFullC K M ≤
      ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M) := by
  rw [ModularCurve.modularFunctionFieldFullC, IntermediateField.adjoin_le_iff]
  rintro x ⟨d, hd, hdM, rfl⟩
  refine ModularCurve.intFormRatiosC_subset K _ ?_

  have hle : CongruenceSubgroup.Gamma0 M ≤ CongruenceSubgroup.Gamma0 d := by
    intro γ hγ
    rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hγ ⊢
    exact (Int.natCast_dvd_natCast.mpr hdM).trans hγ
  refine ModularCurve.intFormRatiosC_mono K hle ?_

  refine ModularCurve.qExpand_image_intFormRatiosC_subset K (Γ := ⊤)
    (Γ' := CongruenceSubgroup.Gamma0 d) (Subgroup.mem_top _) d ?_
    ⟨_, ModularCurve.jqModC_mem_intFormRatiosC K ⊤, rfl⟩
  intro γ hγ
  rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hγ
  obtain ⟨c, hc⟩ := hγ
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    rw [← Matrix.det_fin_two]
    exact Matrix.SpecialLinearGroup.det_coe γ
  rw [hc] at hdet
  refine ⟨⟨!![γ 0 0, (d : ℤ) * γ 0 1; c, γ 1 1], ?_⟩, Subgroup.mem_top _, rfl, rfl, ?_, rfl⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet
  · show (d : ℤ) * c = γ 1 0
    rw [hc]

end ModularCurve

end
