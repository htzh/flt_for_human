/-
The field of ratios of `q`-expansions over `ℂ`, `qC` and its arithmetic, and the
`qC`-facing form of the level-raise/twist transport.

The pin writes this block into several `P2M/Sol/` files, in two spellings:

* `S` / `SField` / `mul_mem_S` … / `mem_S_of_mem` / `common_denominator`
  (`S_ModularCurve_relIndex_gamma0_le_relrank_adjoin_insert_jqNModC.lean:997-1113`,
  the `LeRelrank` body);
* `ratioSet` / `ratioField` / `mul_mem_ratioSet` … / `mem_ratioSet_of_mem_adjoin`
  (`S_ModularCurve_relrank_adjoin_qExpansion_div_le_relIndex.lean:274-391`,
  the `LeRelIndex` body);
* `ratioField` as a `Subfield` in
  `S_ModularCurve_JOne_degeneracyPullbackPair_comm_diamondOneBar.lean` and
  `S_ModularCurve_heckeDiamondInputsHAll.lean`, which the port carries as
  `ModularCurve.DiamondLift.ratioField` (`XH/DiamondLiftPrelude.lean:263`) and
  `ModularCurve.X1…ratioField` (`X1/DiamondAut.lean:322`).

One spelling is kept here (`ratioSet`/`ratioField`, the pin's majority form); the
`S`/`SField` spelling of the `LeRelrank` body is *not* reproduced
(`topics/TOPIC-dedup-refactoring.md` §3.1: two spellings of one predicate forty
lines apart is the failure mode, not the fix).

**Why this module does not import `ModularCurve.DiamondLift.IsRatio`.** Both
theorems of this set are stated for an arbitrary `Γ ≤ SL(2, ℤ)` containing `T`;
neither assumes `Γ` has finite index. `DiamondLift.IsRatio` and
`DiamondLift.ratioField` both carry a `[Γ.FiniteIndex]` argument, so neither is
usable here — the consumer would have to prove an instance the pin does not have.
`DiamondLift.qC` (the definition both sets are written with) is instance-free and
*is* imported, so `ratioSet Γ` unfolds to the very set literal the pin's headlines
use, which is what lets each body's `change` go through. Unifying the `Subfield`
version with this `IntermediateField` one, and the two `S`/`SField` copies of
`XH/Relrank.lean` and `X1/AtkinLehnerExchange.lean` with both, is a separate order
(`topics/TOPIC-dedup-refactoring.md` §6, fourth rule; §8 residue).

`qC` is `ModularCurve.DiamondLift.qC`; `restrictForm` is
`ModularCurve.restrictForm` (`JqIntegralRatios.lean:43`); `raise`/`twist`/`expU`/
`twRaiseFn` are `ModularCurve/RelIndex/LevelRaise.lean`'s.

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_relIndex_gamma0_le_relrank_adjoin_insert_jqNModC.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_relrank_adjoin_qExpansion_div_le_relIndex.lean
-/
import FLTForHuman.ModularCurve.XH.DiamondLiftPrelude
import FLTForHuman.ModularCurve.JqIntegralRatios
import FLTForHuman.ModularCurve.RelIndex.LevelRaise

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open scoped MatrixGroups

open UpperHalfPlane ModularForm HahnSeries IntermediateField

namespace ModularCurve

namespace RelIndex

open DiamondLift (qC)

/-! ## `qC` -/

theorem qC_ne_zero_iff {F : ℍ → ℂ} : qC F ≠ 0 ↔ qExpansion 1 F ≠ 0 := by
  rw [qC, Ne, Ne, ← map_zero (HahnSeries.ofPowerSeries ℤ ℂ),
    (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ)).eq_iff]

/-! ## The ratio set -/

/-- The set of ratios `qC f / qC g` of `q`-expansions of modular forms of a
common weight for `Γ`: the pin's `S Γ` / `ratioSet Γ`. -/
def ratioSet (Γ : Subgroup SL(2, ℤ)) : Set (LaurentSeries ℂ) :=
  {x : LaurentSeries ℂ | ∃ (k : ℤ) (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k),
    UpperHalfPlane.qExpansion 1 (⇑g) ≠ 0 ∧ x = qC ⇑f / qC ⇑g}

theorem mem_ratioSet {Γ : Subgroup SL(2, ℤ)} {k : ℤ}
    (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (hg : qExpansion 1 (⇑g) ≠ 0) : qC f / qC g ∈ ratioSet Γ := ⟨k, f, g, hg, rfl⟩

theorem ratioSet_mono {Γ Γ' : Subgroup SL(2, ℤ)} (h : Γ' ≤ Γ) :
    ratioSet Γ ⊆ ratioSet Γ' := by
  rintro _ ⟨k, f, g, hg, rfl⟩
  have h' : (Γ' : Subgroup (GL (Fin 2) ℝ)) ≤ (Γ : Subgroup (GL (Fin 2) ℝ)) := Subgroup.map_mono h
  exact ⟨k, restrictForm h' f, restrictForm h' g, hg, rfl⟩

/-! ## The `q`-expansion arithmetic of `qC` -/

variable {Γ : Subgroup SL(2, ℤ)}

theorem qC_mul (hT : ModularGroup.T ∈ Γ) {k₁ k₂ : ℤ}
    (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₁)
    (g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₂) : qC (f.mul g) = qC f * qC g := by
  rw [qC, ModularForm.coe_mul,
    ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods hT), map_mul]
  rfl

theorem qC_coe_mul (hT : ModularGroup.T ∈ Γ) {k₁ k₂ : ℤ}
    (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₁)
    (g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₂) :
    qC ((⇑f : ℍ → ℂ) * ⇑g) = qC ⇑f * qC ⇑g := by
  rw [qC, ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods hT), map_mul]
  rfl

theorem qC_add (hT : ModularGroup.T ∈ Γ) {k : ℤ}
    (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) : qC (⇑(f + g)) = qC f + qC g := by
  rw [qC, FunLike.coe_add,
    ModularForm.qExpansion_add one_pos (one_mem_strictPeriods hT) f g, map_add]
  rfl

theorem qC_neg (hT : ModularGroup.T ∈ Γ) {k : ℤ}
    (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) : qC (⇑(-f)) = -qC f := by
  rw [qC, qC, FunLike.coe_neg,
    ModularForm.qExpansion_neg one_pos (one_mem_strictPeriods hT), map_neg]

theorem qExpansion_const (hT : ModularGroup.T ∈ Γ) (c : ℂ) :
    qExpansion 1 (⇑(ModularForm.const c : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 0)) =
      PowerSeries.C c := by
  have hcoe : ((ModularForm.const c : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 0) : ℍ → ℂ) =
      c • ((1 : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 0) : ℍ → ℂ) := by
    funext z
    rw [Pi.smul_apply, ModularForm.const_apply, ModularForm.one_coe_eq_one, Pi.one_apply,
      smul_eq_mul, mul_one]
  rw [hcoe, ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods hT),
    ModularForm.qExpansion_one, PowerSeries.smul_eq_C_mul, mul_one]

theorem qC_const (hT : ModularGroup.T ∈ Γ) (c : ℂ) :
    qC (⇑(ModularForm.const c : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 0)) =
      HahnSeries.C c := by
  rw [qC, qExpansion_const hT, HahnSeries.ofPowerSeries_C]

/-! ## The ratio set is a field -/

theorem mul_mem_ratioSet (hT : ModularGroup.T ∈ Γ) {a b : LaurentSeries ℂ}
    (ha : a ∈ ratioSet Γ) (hb : b ∈ ratioSet Γ) : a * b ∈ ratioSet Γ := by
  obtain ⟨k₁, f₁, g₁, hg₁, rfl⟩ := ha
  obtain ⟨k₂, f₂, g₂, hg₂, rfl⟩ := hb
  refine ⟨k₁ + k₂, f₁.mul f₂, g₁.mul g₂, ?_, ?_⟩
  · rw [← qC_ne_zero_iff, qC_mul hT]
    exact mul_ne_zero (qC_ne_zero_iff.mpr hg₁) (qC_ne_zero_iff.mpr hg₂)
  · rw [qC_mul hT, qC_mul hT, div_mul_div_comm]

theorem add_mem_ratioSet (hT : ModularGroup.T ∈ Γ) {a b : LaurentSeries ℂ}
    (ha : a ∈ ratioSet Γ) (hb : b ∈ ratioSet Γ) : a + b ∈ ratioSet Γ := by
  obtain ⟨k₁, f₁, g₁, hg₁, rfl⟩ := ha
  obtain ⟨k₂, f₂, g₂, hg₂, rfl⟩ := hb
  refine ⟨k₁ + k₂, f₁.mul g₂ + g₁.mul f₂, g₁.mul g₂, ?_, ?_⟩
  · rw [← qC_ne_zero_iff, qC_mul hT]
    exact mul_ne_zero (qC_ne_zero_iff.mpr hg₁) (qC_ne_zero_iff.mpr hg₂)
  · have h1 : qC ⇑g₁ ≠ 0 := qC_ne_zero_iff.mpr hg₁
    have h2 : qC ⇑g₂ ≠ 0 := qC_ne_zero_iff.mpr hg₂
    rw [qC_add hT, qC_mul hT, qC_mul hT, qC_mul hT, div_add_div _ _ h1 h2]

theorem neg_mem_ratioSet (hT : ModularGroup.T ∈ Γ) {a : LaurentSeries ℂ}
    (ha : a ∈ ratioSet Γ) : -a ∈ ratioSet Γ := by
  obtain ⟨k, f, g, hg, rfl⟩ := ha
  exact ⟨k, -f, g, hg, by rw [qC_neg hT]; ring⟩

theorem inv_mem_ratioSet {a : LaurentSeries ℂ} (ha : a ∈ ratioSet Γ) : a⁻¹ ∈ ratioSet Γ := by
  obtain ⟨k, f, g, hg, rfl⟩ := ha
  by_cases hf : qExpansion 1 (⇑f) = 0
  · refine ⟨k, f, g, hg, ?_⟩
    rw [qC, hf, map_zero, zero_div, inv_zero]
  · exact ⟨k, g, f, hf, by rw [inv_div]⟩

theorem algebraMap_laurentSeries_eq_C (c : ℂ) :
    algebraMap ℂ (LaurentSeries ℂ) c = HahnSeries.C c := by
  have h1 : algebraMap ℂ (PowerSeries ℂ) c = PowerSeries.C c := by simp
  rw [HahnSeries.algebraMap_apply', h1, HahnSeries.ofPowerSeries_C]

theorem algebraMap_mem_ratioSet (hT : ModularGroup.T ∈ Γ) (c : ℂ) :
    algebraMap ℂ (LaurentSeries ℂ) c ∈ ratioSet Γ := by
  refine ⟨0, ModularForm.const c, ModularForm.const 1, ?_, ?_⟩
  · rw [qExpansion_const hT]; simp
  · rw [qC_const hT, qC_const hT, algebraMap_laurentSeries_eq_C]; simp

variable (Γ) in
/-- The field of ratios of `q`-expansions of modular forms for `Γ`: the pin's
`ratioField Γ` / `SField Γ`, as an `IntermediateField` so that
`IntermediateField.adjoin_le_iff` applies to it. -/
def ratioField (hT : ModularGroup.T ∈ Γ) : IntermediateField ℂ (LaurentSeries ℂ) where
  carrier := ratioSet Γ
  mul_mem' := mul_mem_ratioSet hT
  one_mem' := by simpa using algebraMap_mem_ratioSet hT 1
  add_mem' := add_mem_ratioSet hT
  zero_mem' := by simpa using algebraMap_mem_ratioSet hT 0
  algebraMap_mem' := algebraMap_mem_ratioSet hT
  inv_mem' _ := inv_mem_ratioSet

theorem mem_ratioSet_of_mem_adjoin (hT : ModularGroup.T ∈ Γ) {y : LaurentSeries ℂ}
    (hy : y ∈ IntermediateField.adjoin ℂ (ratioSet Γ)) : y ∈ ratioSet Γ := by
  have hle : IntermediateField.adjoin ℂ (ratioSet Γ) ≤ ratioField (Γ := Γ) hT :=
    IntermediateField.adjoin_le_iff.mpr (fun _ h => h)
  exact hle hy

/-! ## Common denominators -/

theorem common_denominator (hT : ModularGroup.T ∈ Γ) (n : ℕ) (c : Fin n → LaurentSeries ℂ)
    (hc : ∀ i, c i ∈ ratioSet Γ) :
    ∃ (k : ℤ) (g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
      (f : Fin n → ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k),
      qC g ≠ 0 ∧ ∀ i, c i * qC g = qC (f i) := by
  induction n with
  | zero =>
      refine ⟨0, 1, Fin.elim0, ?_, fun i => Fin.elim0 i⟩
      rw [qC, ModularForm.one_coe_eq_one, qExpansion_one, map_one]
      exact one_ne_zero
  | succ n ih =>
      obtain ⟨k, g, f, hg0, hf⟩ := ih (Fin.tail c) (fun i => hc i.succ)
      obtain ⟨k₀, f₀, g₀, hg₀, hc0⟩ := hc 0
      refine ⟨k₀ + k, g₀.mul g, Fin.cons (f₀.mul g) (fun i => g₀.mul (f i)), ?_, ?_⟩
      · rw [qC_mul hT]
        exact mul_ne_zero (qC_ne_zero_iff.mpr hg₀) hg0
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp only [Fin.cons_zero]
          have hq : qC ⇑g₀ ≠ 0 := qC_ne_zero_iff.mpr hg₀
          rw [hc0, qC_mul hT, qC_mul hT]
          field_simp
        · simp only [Fin.cons_succ]
          have h2 : c j.succ * qC g = qC (f j) := hf j
          rw [qC_mul hT, qC_mul hT, ← h2]
          ring

/-! ## A coefficient-sum helper used by both bodies -/

theorem coe_finset_sum {ι : Type*} {k' : ℤ} (s : Finset ι)
    (F : ι → ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k') :
    ((∑ i ∈ s, F i : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k') : ℍ → ℂ) =
      ∑ i ∈ s, (F i : ℍ → ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, FunLike.coe_add, ih]

/-! ## `qC` of a level-raise and of a twist -/

theorem qC_eq_qExpand_of_coeff {G F : ℍ → ℂ} (t : ℕ) [NeZero t]
    (h : ∀ n : ℕ, PowerSeries.coeff n (qExpansion 1 G) =
      if t ∣ n then PowerSeries.coeff (n / t) (qExpansion 1 F) else 0) :
    qC G = qExpand ℂ t (qC F) := by
  ext m
  rw [qC, qC]
  by_cases hdvd : (t : ℤ) ∣ m
  · obtain ⟨j, rfl⟩ := hdvd
    rw [qExpand_coeff_mul, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
    have ht0 : (0 : ℤ) < t := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne t)
    by_cases hj : j < 0
    · rw [ite_eq_left hj, ite_eq_left (mul_neg_of_pos_of_neg ht0 hj)]
    · rw [ite_eq_right hj, ite_eq_right (by push Not at hj ⊢; positivity)]
      rw [h]
      have h1 : ((t : ℤ) * j).natAbs = t * j.natAbs := by
        rw [Int.natAbs_mul, Int.natAbs_natCast]
      rw [h1, ite_eq_left (Dvd.intro _ rfl), Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne t))]
  · rw [qExpand_coeff_of_not_dvd t _ hdvd, PowerSeries.coeff_coe]
    split_ifs with hm
    · rfl
    · rw [h, ite_eq_right]
      rintro ⟨c, hc⟩
      apply hdvd
      refine ⟨c, ?_⟩
      have : (m.natAbs : ℤ) = m := Int.natAbs_of_nonneg (le_of_not_gt hm)
      rw [← this, hc]; push_cast; ring

theorem qC_raise {Γg : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (hΓ : (1 : ℝ) ∈ Γg.strictPeriods) (t : ℕ) [NeZero t] (f : ModularForm Γg k) :
    qC (raise t f) = qExpand ℂ t (qC f) :=
  qC_eq_qExpand_of_coeff t (coeff_qExpansion_raise hΓ t f)

theorem qC_twist {Γg : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (hΓ : (1 : ℝ) ∈ Γg.strictPeriods) (x : ℝ) (F : ModularForm Γg k) :
    qC (twist x F) = qTwist (expU x) (qC F) := by
  ext n
  rw [qTwist_coeff, qC, qC]
  by_cases hn : 0 ≤ n
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
      coeff_qExpansion_twist hΓ]
    rw [zpow_natCast, Units.val_pow_eq_pow_val, val_expU]
  · have h1 : (HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (twist x F))).coeff n = 0 := by
      rw [PowerSeries.coeff_coe, ite_eq_left (lt_of_not_ge hn)]
    have h2 : (HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 F)).coeff n = 0 := by
      rw [PowerSeries.coeff_coe, ite_eq_left (lt_of_not_ge hn)]
    rw [h1, h2, mul_zero]

theorem qC_twRaiseFn {Γg : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (hΓ : (1 : ℝ) ∈ Γg.strictPeriods) (x : ℝ) (t : ℕ) [NeZero t]
    (F : ModularForm Γg k) :
    qC (twRaiseFn x t F) = qExpand ℂ t (qTwist (expU x) (qC F)) := by
  rw [twRaiseFn_eq, qC_raise (one_mem_strictPeriods_twist hΓ x), qC_twist hΓ]

end RelIndex

end ModularCurve
