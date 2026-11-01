/-
  D — the special places of `X(N)`: the ramification of `j` over `1728`, `0` and `∞`.

  Three `ℂ`-places of the function field `K ⊇ LevelN.ring N` realize the three
  ramification phenomena of the level-`N` Hauptmodul:

  * a place where `j - 1728` has order in `{1, 2}` — the elliptic points of period `2`,
    where `j` takes the value `1728` with local degree `e = 2 / |Stab(i)|`;
  * a place where `j` has order in `{1, 2, 3}` — the elliptic points of period `3`,
    where `j` vanishes with local degree `e = 3 / |Stab(ρ)|`;
  * a place where `j` has a pole of order in `[1, N]` — the cusps of `X(N)`.

  The two elliptic bounds come from the analytic order of `j - j(τ₀)` at `τ₀`, which is
  `|Stab(τ₀)| / 2` by the meromorphic-order computation
  `meromorphicOrderAt_E4_cube_div_discriminant_sub_eq_card_stabilizer_div_two`, together
  with the place dictionary `LevelN.exists_place_analyticOrderAt_eq_mul_ord`.  The cusp
  bound comes from the Laurent-series model: the `q`-expansion of `j` has a simple pole and
  the model map is `N`-to-one on orders, so at the cusp place `j` has a pole of order `N`
  divided by the ramification index — at least one, and at most `N`.

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  `P2M/Sol/S_ModularCurve_LevelN_exists_place_ord_jGen_le_two_three_level.lean` (303
  lines, 26 declarations).  The public statement is the `Theorems/` wrapper, verbatim.

  ## Reused, not restated

  The level-one geometry (`E₄_smul`, `E₆_smul`, `S_smul_I`, `TinvS_smul_ρ`, `E₆_I`,
  `denom_TinvS_ρ`, `ρ_ne_one`, `E₄_ρ`, `natCard_stabilizer_I`, `natCard_stabilizer_ρ`,
  `jf_eq_of_E₆_eq_zero`) is public in `ModularCurve.JMultiplicity`
  (`TateSlots/Invariants.lean`); `jAnalytic` *is* `JMultiplicity.jf` by definition.  The
  four premises of the row are imported: `LevelN.exists_algHom_laurentSeries_qExpansion`
  (`LevelN/FieldGalois.lean`), `LevelN.exists_place_analyticOrderAt_eq_mul_ord`
  (`LevelN/Places.lean`),
  `meromorphicOrderAt_E4_cube_div_discriminant_sub_eq_card_stabilizer_div_two`
  (`TateSlots/Invariants.lean`) and
  `Place.exists_ord_mul_eq_order_of_algHom_laurentSeries`
  (`AlgebraicCurve/Place/LaurentSeriesModel.lean`).  The cusp computation needs the generic
  `order_qExpand` (`Degree/LaurentGlue.lean`) and the instance-free place dictionary
  `Place.exists_ord_mul_eq_order_of_ringHom`
  (`AlgebraicCurve/Place/LaurentSeriesRingHom.lean`), neither of which is in the four
  premises' closure; the latter takes the `ℂ`-algebra map of the Laurent model as a plain
  ring hom, so no `Algebra ℂ (LaurentSeries ℂ)` instance is involved.

  spec-pin: Theorems/Thm_ModularCurve_LevelN_exists_place_ord_jGen_le_two_three_level.lean
  spec-pin: P2M/Sol/S_ModularCurve_LevelN_exists_place_ord_jGen_le_two_three_level.lean
-/
import FLTForHuman.ModularCurve.LevelN.Places
import FLTForHuman.ModularCurve.LevelN.FieldGalois
import FLTForHuman.ModularCurve.TateSlots.Invariants
import FLTForHuman.AlgebraicCurve.Place.LaurentSeriesModel
import FLTForHuman.AlgebraicCurve.Place.LaurentSeriesRingHom
import FLTForHuman.ModularCurve.Degree.LaurentGlue

set_option autoImplicit false

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups IntermediateField Manifold

namespace ModularCurve

namespace LevelN

namespace SpecialRamification

/-- `S * T` fixes the primitive sixth root `ρ`, so it acts on `X(1)` with a fixed point
there: the elliptic point of period `3`. -/
theorem ST_smul_ρ : (ModularGroup.S * ModularGroup.T) • ρ = ρ :=
  ModularGroup.stabilizer_ρ.mpr (by simp)

/-- `j` vanishes at `ρ`. -/
theorem jAnalytic_ρ : LevelN.jAnalytic ρ = 0 := by
  rw [LevelN.jAnalytic, JMultiplicity.E₄_ρ]
  simp

/-- `j = 1728` at `i`. -/
theorem jAnalytic_I : LevelN.jAnalytic UpperHalfPlane.I = 1728 := by
  have hΔ := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq UpperHalfPlane.I
  rw [JMultiplicity.E₆_I] at hΔ
  have hΔ0 := ModularForm.discriminant_ne_zero UpperHalfPlane.I
  have hE4 : ModularForm.E₄ UpperHalfPlane.I ≠ 0 := by
    intro h
    apply hΔ0
    rw [hΔ, h]
    norm_num
  rw [LevelN.jAnalytic, hΔ]
  field_simp
  ring

/-- `j - c` is not the zero function: it takes different values at `ρ` and at `i`. -/
theorem jAnalytic_sub_ne_zero (c : ℂ) : (fun τ : ℍ => LevelN.jAnalytic τ - c) ≠ 0 := by
  intro h
  have h1 := congrFun h ρ
  have h2 := congrFun h UpperHalfPlane.I
  simp only [Pi.zero_apply, jAnalytic_ρ, jAnalytic_I] at h1 h2
  have : (1728 : ℂ) = 0 := by linear_combination h2 - h1
  norm_num at this

/-- The stabiliser of `i` in `SL(2, ℤ)` is `{±1, ±S}`, so it has at most four elements. -/
theorem natCard_stabilizer_I_le : Nat.card (MulAction.stabilizer SL(2, ℤ) UpperHalfPlane.I) ≤ 4 := by
  classical
  rw [Nat.card_congr (Equiv.subtypeEquivRight
    (q := fun g => g ∈ ({1, -1, ModularGroup.S, -ModularGroup.S} : Finset SL(2, ℤ)))
    (fun g => (MulAction.mem_stabilizer_iff).trans ModularGroup.stabilizer_I)),
    Nat.card_eq_finsetCard]
  exact Finset.card_le_four

/-- The stabiliser of `ρ` in `SL(2, ℤ)` is `{±1, ±ST, ±T⁻¹S}`, so it has at most six
elements. -/
theorem natCard_stabilizer_ρ_le : Nat.card (MulAction.stabilizer SL(2, ℤ) ρ) ≤ 6 := by
  classical
  rw [Nat.card_congr (Equiv.subtypeEquivRight
    (q := fun g => g ∈ ({1, -1, ModularGroup.S * ModularGroup.T, -(ModularGroup.S * ModularGroup.T),
      ModularGroup.T⁻¹ * ModularGroup.S, -(ModularGroup.T⁻¹ * ModularGroup.S)} : Finset SL(2, ℤ)))
    (fun g => (MulAction.mem_stabilizer_iff).trans ModularGroup.stabilizer_ρ)),
    Nat.card_eq_finsetCard]
  calc _ ≤ _ + 1 := Finset.card_insert_le _ _
    _ ≤ _ + 1 + 1 := by gcongr; exact Finset.card_insert_le _ _
    _ ≤ 4 + 1 + 1 := by gcongr; exact Finset.card_le_four
    _ = 6 := rfl

section Places

theorem mdifferentiable_jAnalytic : MDiff LevelN.jAnalytic := by
  have h4 : MDiff (ModularForm.E₄ : ℍ → ℂ) := ModularForm.E₄.holo'
  have hΔ : MDiff (ModularForm.discriminant : ℍ → ℂ) := CuspForm.discriminant.holo'
  have : LevelN.jAnalytic = fun τ => ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ := rfl
  rw [this]
  exact (h4.pow 3).div hΔ fun τ => ModularForm.discriminant_ne_zero τ

theorem analyticAt_comp_ofComplex {G : ℍ → ℂ} (hG : MDiff G) (τ : ℍ) :
    AnalyticAt ℂ (G ∘ ofComplex) τ := by
  have hd : DifferentiableOn ℂ (G ∘ ofComplex) {w : ℂ | 0 < w.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp hG
  exact (hd.analyticOnNhd isOpen_upperHalfPlaneSet) τ τ.im_pos

@[scoped simp] theorem comp_ofComplex_apply_coe (G : ℍ → ℂ) (τ : ℍ) : (G ∘ ofComplex) (τ : ℂ) = G τ := by
  simp [Function.comp_apply, ofComplex_apply]

/-- The analytic order of `j - j(τ₀)` at `τ₀` is half the cardinality of the stabiliser of
`τ₀`. -/
theorem analyticOrderAt_jsub (τ₀ : ℍ) :
    analyticOrderAt ((fun τ : ℍ => LevelN.jAnalytic τ - LevelN.jAnalytic τ₀) ∘ ofComplex) (τ₀ : ℂ) =
      ((Nat.card (MulAction.stabilizer SL(2, ℤ) τ₀) / 2 : ℕ) : ℕ∞) := by
  have hmero := ModularCurve.meromorphicOrderAt_E4_cube_div_discriminant_sub_eq_card_stabilizer_div_two τ₀
  have hfun : (fun z : ℂ => (ModularForm.E₄ : ℍ → ℂ) (ofComplex z) ^ 3 / ModularForm.discriminant (ofComplex z)
      - (ModularForm.E₄ : ℍ → ℂ) τ₀ ^ 3 / ModularForm.discriminant τ₀) =
      ((fun τ : ℍ => LevelN.jAnalytic τ - LevelN.jAnalytic τ₀) ∘ ofComplex) := by
    funext z; rfl
  rw [hfun] at hmero
  have han : AnalyticAt ℂ ((fun τ : ℍ => LevelN.jAnalytic τ - LevelN.jAnalytic τ₀) ∘ ofComplex) τ₀ :=
    analyticAt_comp_ofComplex ((mdifferentiable_jAnalytic).sub mdifferentiable_const) τ₀
  rw [han.meromorphicOrderAt_eq] at hmero
  generalize analyticOrderAt ((fun τ : ℍ => LevelN.jAnalytic τ - LevelN.jAnalytic τ₀) ∘ ofComplex)
    (τ₀ : ℂ) = n at hmero ⊢
  induction n using ENat.recTopCoe with
  | top => exact absurd hmero (by simp)
  | coe m =>
    simp only [ENat.map_natCast, WithTop.coe_eq_coe, Nat.cast_inj] at hmero
    exact_mod_cast hmero

variable (M : ℕ)

/-- The constant `c` as an element of `LevelN.ring M` is the constant function `c`. -/
theorem coe_algebraMap_ring (c : ℂ) :
    ((algebraMap ℂ (LevelN.ring M) c : LevelN.ring M) : ℍ → ℂ) = fun _ => c := by
  funext τ
  simp [Algebra.algebraMap_eq_smul_one]

/-- `j - c` is an element of the level-`N` ring. -/
theorem jsub_mem (c : ℂ) : (fun τ : ℍ => LevelN.jAnalytic τ - c) ∈ LevelN.ring M := by
  have : (fun τ : ℍ => LevelN.jAnalytic τ - c) =
      ((LevelN.jGen M - algebraMap ℂ (LevelN.ring M) c : LevelN.ring M) : ℍ → ℂ) := by
    funext τ
    simp [LevelN.coe_jGen, Algebra.algebraMap_eq_smul_one]
  rw [this]
  exact (LevelN.jGen M - algebraMap ℂ (LevelN.ring M) c).2

variable (K : Type*) [Field K] [Algebra ℂ K] [Algebra (LevelN.ring M) K]
  [IsScalarTower ℂ (LevelN.ring M) K]

/-- The image of `j` in `K`. -/
abbrev jK : K := algebraMap (LevelN.ring M) K (LevelN.jGen M)

/-- The image of `j - c` in `K` is `jK - c`. -/
theorem algebraMap_jsub (c : ℂ) :
    algebraMap (LevelN.ring M) K ⟨fun τ : ℍ => LevelN.jAnalytic τ - c, jsub_mem M c⟩ =
      jK M K - algebraMap ℂ K c := by
  have : (⟨fun τ : ℍ => LevelN.jAnalytic τ - c, jsub_mem M c⟩ : LevelN.ring M) =
      LevelN.jGen M - algebraMap ℂ (LevelN.ring M) c := by
    apply Subtype.ext
    funext τ
    simp [LevelN.coe_jGen, Algebra.algebraMap_eq_smul_one]
  rw [this, map_sub, ← IsScalarTower.algebraMap_apply]

variable [NeZero M] [IsFractionRing (LevelN.ring M) K]

/-- A place at which `j - j(τ₀)` has a positive order no larger than the analytic order of
`j - j(τ₀)` at `τ₀`, i.e. no larger than `|Stab(τ₀)| / 2`. -/
theorem exists_place_ord_sub_le (τ₀ : ℍ) :
    ∃ W : AlgebraicCurve.Place ℂ K,
      0 < W.ord (jK M K - algebraMap ℂ K (LevelN.jAnalytic τ₀)) ∧
      W.ord (jK M K - algebraMap ℂ K (LevelN.jAnalytic τ₀)) ≤
        (Nat.card (MulAction.stabilizer SL(2, ℤ) τ₀) / 2 : ℕ) := by
  obtain ⟨W, e, he, hW⟩ := ModularCurve.LevelN.exists_place_analyticOrderAt_eq_mul_ord M K τ₀
  refine ⟨W, ?_⟩
  obtain ⟨hfin, hord⟩ := hW (fun τ : ℍ => LevelN.jAnalytic τ - LevelN.jAnalytic τ₀)
    (jsub_mem M _) (jAnalytic_sub_ne_zero _)
  rw [algebraMap_jsub] at hord
  rw [analyticOrderAt_jsub] at hord hfin
  simp only [ENat.toNat_natCast] at hord

  have hpos : 0 < (Nat.card (MulAction.stabilizer SL(2, ℤ) τ₀) / 2 : ℕ) := by
    have h := analyticOrderAt_jsub τ₀
    have hne : analyticOrderAt ((fun τ : ℍ => LevelN.jAnalytic τ - LevelN.jAnalytic τ₀) ∘ ofComplex)
        (τ₀ : ℂ) ≠ 0 := by
      rw [analyticOrderAt_ne_zero]
      exact ⟨analyticAt_comp_ofComplex ((mdifferentiable_jAnalytic).sub mdifferentiable_const) τ₀,
        by simp⟩
    rw [h] at hne
    exact Nat.pos_of_ne_zero fun h0 => hne (by rw [h0]; rfl)
  set s := (Nat.card (MulAction.stabilizer SL(2, ℤ) τ₀) / 2 : ℕ)
  set a := W.ord (jK M K - algebraMap ℂ K (LevelN.jAnalytic τ₀))
  have he1 : (1 : ℤ) ≤ e := by exact_mod_cast he
  constructor
  · by_contra hle
    push Not at hle
    have : (e : ℤ) * a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by omega) hle
    omega
  · nlinarith

/-- A place at which `j` has a pole of order between `1` and `M`. -/
theorem exists_place_ord_neg_ge :
    ∃ W : AlgebraicCurve.Place ℂ K, W.ord (jK M K) < 0 ∧ -(M : ℤ) ≤ W.ord (jK M K) := by
  have hM0 : (0 : ℤ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  obtain ⟨E, hEj, -⟩ := ModularCurve.LevelN.exists_algHom_laurentSeries_qExpansion M K
  have hC : ∀ c : ℂ, E (algebraMap ℂ K c) = HahnSeries.C c := by
    intro c
    rw [E.commutes, HahnSeries.algebraMap_apply']
    simp
  have hordj : (E.toRingHom (algebraMap (ModularCurve.LevelN.ring M) K
      (ModularCurve.LevelN.jGen M))).order = -(M : ℤ) := by
    change (E (algebraMap (ModularCurve.LevelN.ring M) K
      (ModularCurve.LevelN.jGen M))).order = _
    rw [hEj, order_qExpand, order_jqModC]
    ring
  obtain ⟨W, γ, hγ, hW⟩ :=
    AlgebraicCurve.Place.exists_ord_mul_eq_order_of_ringHom (K := ℂ) (F := K) E.toRingHom hC
      ⟨algebraMap (ModularCurve.LevelN.ring M) K (ModularCurve.LevelN.jGen M),
        by rw [hordj]; omega⟩
  refine ⟨W, ?_, ?_⟩
  · have h := hW (jK M K)
    rw [hordj] at h
    by_contra hle
    push Not at hle
    have : 0 ≤ W.ord (jK M K) * (γ : ℤ) := mul_nonneg hle (by exact_mod_cast hγ.le)
    omega
  · have h := hW (jK M K)
    rw [hordj] at h
    have hγ1 : (1 : ℤ) ≤ γ := by exact_mod_cast hγ
    nlinarith

theorem main :
    (∃ W : AlgebraicCurve.Place ℂ K, 0 < W.ord (jK M K - 1728) ∧ W.ord (jK M K - 1728) ≤ 2) ∧
      (∃ W : AlgebraicCurve.Place ℂ K, 0 < W.ord (jK M K) ∧ W.ord (jK M K) ≤ 3) ∧
      (∃ W : AlgebraicCurve.Place ℂ K, W.ord (jK M K) < 0 ∧ -(M : ℤ) ≤ W.ord (jK M K)) := by
  refine ⟨?_, ?_, exists_place_ord_neg_ge M K⟩
  · obtain ⟨W, h1, h2⟩ := exists_place_ord_sub_le M K UpperHalfPlane.I
    rw [jAnalytic_I, map_ofNat] at h1 h2
    refine ⟨W, h1, h2.trans ?_⟩
    have h4 := natCard_stabilizer_I_le
    have : Nat.card (MulAction.stabilizer SL(2, ℤ) UpperHalfPlane.I) / 2 ≤ 2 := by omega
    exact_mod_cast this
  · obtain ⟨W, h1, h2⟩ := exists_place_ord_sub_le M K ρ
    rw [jAnalytic_ρ, map_zero, sub_zero] at h1 h2
    refine ⟨W, h1, h2.trans ?_⟩
    have h6 := natCard_stabilizer_ρ_le
    have : Nat.card (MulAction.stabilizer SL(2, ℤ) ρ) / 2 ≤ 3 := by omega
    exact_mod_cast this

end Places

end SpecialRamification

/-- **The special places of `X(N)`.** Over any fraction field `K` of the level-`N` ring, `j`
has a place of positive order at most `2` over `1728`, a place of positive order at most `3`
over `0`, and a place of pole order between `1` and `N`. -/
theorem exists_place_ord_jGen_le_two_three_level (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ModularCurve.LevelN.ring N) K]
    [IsScalarTower ℂ (ModularCurve.LevelN.ring N) K]
    [IsFractionRing (ModularCurve.LevelN.ring N) K] :
    (∃ W : AlgebraicCurve.Place ℂ K,
        0 < W.ord (algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N) - 1728) ∧
          W.ord (algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N) - 1728) ≤ 2) ∧
      (∃ W : AlgebraicCurve.Place ℂ K,
        0 < W.ord (algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N)) ∧
          W.ord (algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N)) ≤ 3) ∧
      (∃ W : AlgebraicCurve.Place ℂ K,
        W.ord (algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N)) < 0 ∧
          -(N : ℤ) ≤ W.ord (algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N))) :=
  SpecialRamification.main N K

end LevelN

end ModularCurve

end
