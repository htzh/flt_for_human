/-
  Consumer specification for the **RS3 ready shelf 3** wave (orders A, B, C).

  WHAT THIS FILE IS
  -----------------
  A written-down *use* of the three orders of
  `lean/topics/modularCurve/WORKORDER-RS3-ready-shelf3.md`, merged by the manager from the three
  per-order zones (`ModularCurveReady3Zone{A,B,C}.lean`, retired at landing). It is a
  deliverable measure, not a proof obligation, and it is deliberately **not part of any
  library**: nothing globs `spec/`, so it cannot break the verified build. Run it by hand:

      cd lean
      lake env lean spec/ModularCurveReady3Consumer.lean 2>&1 | grep -c error

  The error count is the metric; it is 0. The three blocks are the rows' own cross-module
  steps, in the order of the work order:

    [A] the Siegel product form: apply the 249 row to get `ϑ`, then the 469 row for `a` and the
        457 row for `m₀`, read the `S`-slash coefficient integrality at `n = m₀`, and compose
        the product with `SiegelUnit.prod_siegelFun_pow_specialLinearGroup_smul`.
    [B] the special-fibre bounds: instantiate the three inequalities at `X(2)` and compose them
        with the genus inequality of the same module and
        `LevelN.exists_place_ord_jGen_le_two_three_level`.
    [C] separability of `Φ₂` over `K(X)` at a field `K` with `(2 : K) ≠ 0`, from the new row,
        the level-two datum and the coset engine.
-/

import FLTForHuman.ModularCurve.SiegelUnit.ProductForm
import FLTForHuman.ModularCurve.LevelN.GenusFF
import FLTForHuman.ModularCurve.LevelN.SpecialRamification
import FLTForHuman.ModularCurve.ModularPolynomialCoset
import FLTForHuman.ModularCurve.ModularEquation.LevelTwo
import FLTForHuman.ModularCurve.ModularPolynomialFibreTwo
import FLTForHuman.ModularCurve.SiegelUnit.PeakedAuxiliary
import FLTForHuman.NumberTheory.ModularForms.CongruenceSubgroupLattice

-- ---------------------------------------------------------------------------
-- [A] the Siegel product form and its two q-expansion conclusions (249 / 469 / 457)
-- ---------------------------------------------------------------------------
noncomputable section

open Complex UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm

namespace ModularCurve.SiegelUnit

/-- The trivial exponent function: the Siegel product is `1`. -/
private def mZero (N : ℕ) : ZMod N → ZMod N → ℕ := fun _ _ => 0

private theorem mZero_zero (N : ℕ) [NeZero N] : mZero N 0 0 = 0 := rfl

private theorem mZero_row (N : ℕ) [NeZero N] (r s : ZMod N) : mZero N r (s + r) = mZero N r s := rfl

/-- The weight hypothesis `ht` of the 249 row holds for the trivial exponent function and
`t = 1`. -/
private theorem mZero_ht (N : ℕ) [NeZero N] :
    ∀ β : SL(2, ℤ),
      0 ≤ (∑ r : ZMod N, ∑ s : ZMod N, (mZero N r s : ℤ) *
          (6 * ((r * ((β 0 0 : ℤ) : ZMod N) + s * ((β 1 0 : ℤ) : ZMod N)).val : ℤ) ^ 2
            - 6 * (N : ℤ) * ((r * ((β 0 0 : ℤ) : ZMod N) + s * ((β 1 0 : ℤ) : ZMod N)).val : ℤ) +
            (N : ℤ) ^ 2)) + (N : ℤ) * 1 := by
  intro β
  have h0 : (∑ r : ZMod N, ∑ s : ZMod N, (mZero N r s : ℤ) *
      (6 * ((r * ((β 0 0 : ℤ) : ZMod N) + s * ((β 1 0 : ℤ) : ZMod N)).val : ℤ) ^ 2
        - 6 * (N : ℤ) * ((r * ((β 0 0 : ℤ) : ZMod N) + s * ((β 1 0 : ℤ) : ZMod N)).val : ℤ) +
        (N : ℤ) ^ 2)) = 0 := by
    simp [mZero]
  rw [h0, zero_add, mul_one]
  exact Int.natCast_nonneg N

/-- The `m₀` pinning hypothesis of the 457 row: `N * m₀ = Ord + N * t` with `m₀ = 1`. -/
private theorem mZero_hm₀ (N : ℕ) [NeZero N] :
    (N : ℤ) * 1 =
      (∑ r : ZMod N, ∑ s : ZMod N, (mZero N r s : ℤ) *
        (6 * (r.val : ℤ) ^ 2 - 6 * (N : ℤ) * (r.val : ℤ) + (N : ℤ) ^ 2)) + (N : ℤ) * 1 := by
  have h0 : (∑ r : ZMod N, ∑ s : ZMod N, (mZero N r s : ℤ) *
      (6 * (r.val : ℤ) ^ 2 - 6 * (N : ℤ) * (r.val : ℤ) + (N : ℤ) ^ 2)) = 0 := by
    simp [mZero]
  rw [h0, zero_add]

/-- **The three rows, chained.**  The Siegel product form exists, its width-`N`
`S`-slash has coefficients integral after a fixed power of `N`, and its width-`1`
expansion is pinned at `m₀ = 1`: it vanishes at `0`, is non-zero at `1`, and a fixed
power of `N` makes the `1`-st coefficient and its inverse integral. -/
theorem exists_prodForm_data (N : ℕ) [NeZero N] :
    ∃ (ϑ : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) (12 * (1 : ℤ)))
      (a a' : ℕ),
      (∀ τ : UpperHalfPlane, ϑ τ =
        (∏ r : ZMod N, ∏ s : ZMod N,
          siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * mZero N r s)) *
          ModularForm.discriminant τ ^ 1) ∧
      (∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ a * (UpperHalfPlane.qExpansion (N : ℝ)
        ((⇑ϑ : UpperHalfPlane → ℂ) ∣[12 * (1 : ℤ)] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff n)) ∧
      (UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff 0 = 0 ∧
      (UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff 1 ≠ 0 ∧
      IsIntegral ℤ ((N : ℂ) ^ a' *
        ((UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff 1)⁻¹) ∧
      IsIntegral ℤ ((N : ℂ) ^ a' *
        (UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff 1) := by
  classical
  obtain ⟨ϑ, hϑ, -⟩ :=
    exists_modularForm_gamma1_coe_eq_prod_siegelFun_pow_mul_discriminant_pow N (mZero N)
      (mZero_zero N) (mZero_row N) 1 (mZero_ht N)
  obtain ⟨a, ha⟩ :=
    isIntegral_qExpansion_slash_S_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow N
      (mZero N) 1 ϑ hϑ
  obtain ⟨a', hzero, hne, hinv, hint⟩ :=
    qExpansion_one_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow N (mZero N)
      (mZero_zero N) 1 ϑ hϑ 1 (mZero_hm₀ N)
  exact ⟨ϑ, a, a', hϑ, ha, hzero 0 (by norm_num), hne, hinv, hint 1⟩

/-- **Reading the `S`-slash integrality at `n = m₀`.**  The width-`N` conclusion of the
469 row applied at the order `m₀`. -/
theorem slash_coeff_integral_at_m₀ (N : ℕ) [NeZero N] (m : ZMod N → ZMod N → ℕ) (t m₀ : ℕ)
    (ϑ : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) (12 * (t : ℤ)))
    (hϑ : ∀ τ : UpperHalfPlane, ϑ τ =
      (∏ r : ZMod N, ∏ s : ZMod N,
          siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * m r s)) *
        ModularForm.discriminant τ ^ t) :
    ∃ a : ℕ, IsIntegral ℤ ((N : ℂ) ^ a * (UpperHalfPlane.qExpansion (N : ℝ)
      ((⇑ϑ : UpperHalfPlane → ℂ) ∣[12 * (t : ℤ)] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff m₀) := by
  obtain ⟨a, ha⟩ :=
    isIntegral_qExpansion_slash_S_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow N m t ϑ hϑ
  exact ⟨a, ha m₀⟩

/-- The `S`-law of `Δ`: `Δ(-1/τ) = Δ(τ) τ¹²`. -/
theorem discriminant_smul_S (τ : UpperHalfPlane) :
    ModularForm.discriminant ((ModularGroup.S : SL(2, ℤ)) • τ) =
      ModularForm.discriminant τ * (τ : ℂ) ^ (12 : ℕ) := by
  have hz : (τ : ℂ) ≠ 0 := τ.ne_zero
  have h := congrFun ModularForm.discriminant_S_invariant τ
  rw [ModularForm.SL_slash_apply, ModularGroup.denom_S] at h
  have h12 : ((τ : ℂ) ^ (-(12 : ℤ))) * (τ : ℂ) ^ (12 : ℕ) = 1 := by
    rw [zpow_neg, show ((12 : ℤ)) = ((12 : ℕ) : ℤ) by norm_num, zpow_natCast,
      inv_mul_cancel₀ (pow_ne_zero _ hz)]
  calc ModularForm.discriminant (ModularGroup.S • τ)
      = ModularForm.discriminant (ModularGroup.S • τ) *
          (((τ : ℂ) ^ (-(12 : ℤ))) * (τ : ℂ) ^ (12 : ℕ)) := by rw [h12, mul_one]
    _ = (ModularForm.discriminant (ModularGroup.S • τ) * (τ : ℂ) ^ (-(12 : ℤ))) *
          (τ : ℂ) ^ (12 : ℕ) := by ring
    _ = ModularForm.discriminant τ * (τ : ℂ) ^ (12 : ℕ) := by rw [h]

/-- **The product form at `S • τ`, in row-action form.**  The 249 row's `hϑ` read at
`S • τ`, composed with the pin's 191 row
(`prod_siegelFun_pow_specialLinearGroup_smul`), which transports the product along
`S` into the row action of `S` on the exponent matrix. -/
theorem prodForm_S_smul_value (N : ℕ) [NeZero N] (m : ZMod N → ZMod N → ℕ) (t : ℕ)
    (ϑ : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) (12 * (t : ℤ)))
    (hϑ : ∀ τ : UpperHalfPlane, ϑ τ =
      (∏ r : ZMod N, ∏ s : ZMod N,
          siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * m r s)) *
        ModularForm.discriminant τ ^ t) (τ : UpperHalfPlane) :
    ϑ ((ModularGroup.S : SL(2, ℤ)) • τ) =
      (∏ r : ZMod N, ∏ s : ZMod N,
        siegelFun N
            ((((r.val : ℤ) * (ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ) 0 0 +
                (s.val : ℤ) * (ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N).val : ℤ)
            ((((r.val : ℤ) * (ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ) 0 1 +
                (s.val : ℤ) * (ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N).val : ℤ)
            (τ : ℂ) ^ (12 * N * m r s)) *
        ModularForm.discriminant ((ModularGroup.S : SL(2, ℤ)) • τ) ^ t := by
  rw [hϑ, (prod_siegelFun_pow_specialLinearGroup_smul N m).1]

/-- The same value with `Δ(S • τ)` expanded by the `S`-law. -/
theorem prodForm_S_smul_value' (N : ℕ) [NeZero N] (m : ZMod N → ZMod N → ℕ) (t : ℕ)
    (ϑ : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) (12 * (t : ℤ)))
    (hϑ : ∀ τ : UpperHalfPlane, ϑ τ =
      (∏ r : ZMod N, ∏ s : ZMod N,
          siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * m r s)) *
        ModularForm.discriminant τ ^ t) (τ : UpperHalfPlane) :
    ϑ ((ModularGroup.S : SL(2, ℤ)) • τ) =
      (∏ r : ZMod N, ∏ s : ZMod N,
        siegelFun N
            ((((r.val : ℤ) * (ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ) 0 0 +
                (s.val : ℤ) * (ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N).val : ℤ)
            ((((r.val : ℤ) * (ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ) 0 1 +
                (s.val : ℤ) * (ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N).val : ℤ)
            (τ : ℂ) ^ (12 * N * m r s)) *
        (ModularForm.discriminant τ * (τ : ℂ) ^ (12 : ℕ)) ^ t := by
  rw [prodForm_S_smul_value N m t ϑ hϑ τ, discriminant_smul_S τ]

end ModularCurve.SiegelUnit

end

-- ---------------------------------------------------------------------------
-- [B] the special-fibre bounds for `j` on `X(N)` (1,123)
-- ---------------------------------------------------------------------------
noncomputable section

open UpperHalfPlane ModularCurve
open scoped MatrixGroups IntermediateField

namespace ModularCurve.Ready3ZoneB

/-- The concrete model of `X(2)`'s function field: a fraction field of the level-`2` ring. -/
abbrev K2 : Type := FractionRing (LevelN.ring 2)

/-- `ring 2` is a domain (`LevelN/FieldGalois.lean:61`), so the fraction ring above is a field. -/
instance : IsDomain (LevelN.ring 2) := LevelN.isDomain_ring 2

/-- The concrete level: the full congruence subgroup `Γ₁(2)`. -/
abbrev G2 : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ) := CongruenceSubgroup.Gamma1 2

/-- **The three special-fibre bounds at `X(2)`.**  The new headline of `GenusFF` at `M = 2` and
`Γ = Γ₁(2)`: the three double-coset counts of `Γ₁(2)` are bounded by the numbers of places over
`ℚ̄` where `j` is `0`, is `1728`, and has a pole. -/
theorem fibres (y : laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ G2))
    (hy : (y : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (hfull : Module.finrank
          (IntermediateField.adjoin (AlgebraicClosure ℚ)
            ({y} : Set (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ G2))))
          (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ G2)) =
        (G2 ⊔ Subgroup.zpowers (-1)).index) :
    Nat.card (DoubleCoset.Quotient (G2 : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
        (Subgroup.zpowers (ModularGroup.S * ModularGroup.T) :
          Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))) ≤
        Nat.card {P : AlgebraicCurve.Place (AlgebraicClosure ℚ)
          (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ G2)) //
            0 < P.ord y} ∧
      Nat.card (DoubleCoset.Quotient (G2 : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
          (Subgroup.zpowers ModularGroup.S : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))) ≤
        Nat.card {P : AlgebraicCurve.Place (AlgebraicClosure ℚ)
          (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ G2)) //
            0 < P.ord (y - 1728)} ∧
      Nat.card (DoubleCoset.Quotient (G2 : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
          ((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) :
              Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
            Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))) ≤
        Nat.card {P : AlgebraicCurve.Place (AlgebraicClosure ℚ)
          (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ G2)) //
            P.ord y < 0} :=
  natCard_doubleCoset_le_card_fibres_of_finrank_eq_index 2 G2 le_rfl y hy hfull

/-- **The genus inequality at the same level**, from the same module: the index/genus inequality
for `X(2)` over the concrete model `K2`. -/
theorem genus_two :
    12 * 2 + 2 * (CongruenceSubgroup.Gamma 2 ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index ≤
      12 * 2 * AlgebraicCurve.genusFF ℂ K2 +
        6 * (CongruenceSubgroup.Gamma 2 ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index :=
  LevelN.twelve_mul_add_mul_index_le_genusFF 2 (by norm_num) K2

/-- **The three special places of `X(2)`**, from `LevelN/SpecialRamification.lean`: `j` has a
place of positive order `≤ 2` over `1728`, one of positive order `≤ 3` over `0`, and a pole of
order between `-2` and `-1`. -/
theorem places_two :
    (∃ W : AlgebraicCurve.Place ℂ K2,
        0 < W.ord (algebraMap (LevelN.ring 2) K2 (LevelN.jGen 2) - 1728) ∧
          W.ord (algebraMap (LevelN.ring 2) K2 (LevelN.jGen 2) - 1728) ≤ 2) ∧
      (∃ W : AlgebraicCurve.Place ℂ K2,
        0 < W.ord (algebraMap (LevelN.ring 2) K2 (LevelN.jGen 2)) ∧
          W.ord (algebraMap (LevelN.ring 2) K2 (LevelN.jGen 2)) ≤ 3) ∧
        ∃ W : AlgebraicCurve.Place ℂ K2,
          W.ord (algebraMap (LevelN.ring 2) K2 (LevelN.jGen 2)) < 0 ∧
            -(2 : ℤ) ≤ W.ord (algebraMap (LevelN.ring 2) K2 (LevelN.jGen 2)) :=
  LevelN.exists_place_ord_jGen_le_two_three_level 2 K2

/-- **Composed consequence.**  The cusp pole of `j` on `X(2)` has order in `[-2, -1]`: the pin's
upper bound `-2 ≤ ord` and strict negativity combine to `ord ≤ -1`. -/
theorem cusp_pole_order :
    ∃ W : AlgebraicCurve.Place ℂ K2,
      W.ord (algebraMap (LevelN.ring 2) K2 (LevelN.jGen 2)) < 0 ∧
        -(2 : ℤ) ≤ W.ord (algebraMap (LevelN.ring 2) K2 (LevelN.jGen 2)) ∧
          W.ord (algebraMap (LevelN.ring 2) K2 (LevelN.jGen 2)) ≤ -1 := by
  obtain ⟨-, -, ⟨W, hWneg, hWge⟩⟩ := places_two
  exact ⟨W, hWneg, hWge, by omega⟩

/-- **Composed consequence.**  `j` is not identically zero in the function field of `X(2)`: the
special place of positive order forces it, since `ord 0 = 0`. -/
theorem jGen_two_ne_zero : algebraMap (LevelN.ring 2) K2 (LevelN.jGen 2) ≠ 0 := by
  obtain ⟨-, ⟨W, hW, -⟩, -⟩ := places_two
  intro h
  rw [h, AlgebraicCurve.Place.ord_zero] at hW
  exact lt_irrefl _ hW

/-- The zone's composite: the three special-fibre bounds at `X(2)`, the genus inequality and the
three special places, together with the two consequences drawn from them. -/
theorem zone (y : laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ G2))
    (hy : (y : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (hfull : Module.finrank
          (IntermediateField.adjoin (AlgebraicClosure ℚ)
            ({y} : Set (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ G2))))
          (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ G2)) =
        (G2 ⊔ Subgroup.zpowers (-1)).index) :
    (Nat.card (DoubleCoset.Quotient (G2 : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
        (Subgroup.zpowers (ModularGroup.S * ModularGroup.T) :
          Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))) ≤
        Nat.card {P : AlgebraicCurve.Place (AlgebraicClosure ℚ)
          (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ G2)) //
            0 < P.ord y}) ∧
      (12 * 2 + 2 * (CongruenceSubgroup.Gamma 2 ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index ≤
        12 * 2 * AlgebraicCurve.genusFF ℂ K2 +
          6 * (CongruenceSubgroup.Gamma 2 ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index) ∧
        (∃ W : AlgebraicCurve.Place ℂ K2,
          W.ord (algebraMap (LevelN.ring 2) K2 (LevelN.jGen 2)) < 0 ∧
            -(2 : ℤ) ≤ W.ord (algebraMap (LevelN.ring 2) K2 (LevelN.jGen 2)) ∧
              W.ord (algebraMap (LevelN.ring 2) K2 (LevelN.jGen 2)) ≤ -1) ∧
          algebraMap (LevelN.ring 2) K2 (LevelN.jGen 2) ≠ 0 :=
  ⟨(fibres y hy hfull).1, genus_two, cusp_pole_order, jGen_two_ne_zero⟩

end ModularCurve.Ready3ZoneB

-- ---------------------------------------------------------------------------
-- [C] separability of `Φ_N` over `K(X)` (128)
-- ---------------------------------------------------------------------------
noncomputable section

open Polynomial

namespace ModularCurve

/-- **Level-two separability of `Φ₂` over `K(X)`.**  For a field `K` with `(2 : K) ≠ 0`, the
classical modular polynomial `Φ₂` — the `Φ` of any level-two `ModularPolynomialData` datum —
has separable image in `K(X)`. -/
theorem separable_phiTwo_map_ratFunc (K : Type*) [Field K] (h2K : (2 : K) ≠ 0)
    (data : ModularPolynomialData 2) :
    ((phiTwo.map (Polynomial.mapRingHom (Int.castRingHom K))).map
      (algebraMap (Polynomial K) (RatFunc K))).Separable := by
  rw [← ModularPolynomialData.phi_eq_phiTwo data]
  exact ModularPolynomialData.separable_map_ratFunc_of_natCast_ne_zero K 2 data h2K

/-- The same at a field of characteristic not two, phrased as `(2 : K) ≠ 0` from `CharZero`. -/
theorem separable_phiTwo_map_ratFunc_charZero (K : Type*) [Field K] [CharZero K]
    (data : ModularPolynomialData 2) :
    ((phiTwo.map (Polynomial.mapRingHom (Int.castRingHom K))).map
      (algebraMap (Polynomial K) (RatFunc K))).Separable :=
  separable_phiTwo_map_ratFunc K (by norm_num) data

/-- **The coset polynomial at level two.**  The coset-root product
`cosetTwoVarPoly ζ 2 J` is separable over any field, for any primitive second root of unity
and any `J` with a simple pole at `q = 0` — the engine the separability row consumes. -/
theorem separable_cosetTwoVarPoly_two (K : Type*) [Field K] (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ 2)
    (J : LaurentSeries K) (hJ : J.coeff (-1) ≠ 0) (hJ' : ∀ m : ℤ, m < -1 → J.coeff m = 0) :
    (cosetTwoVarPoly ζ 2 J).Separable :=
  separable_cosetTwoVarPoly K 2 (by norm_num) ζ hζ J hJ hJ'

end ModularCurve

end

-- ---------------------------------------------------------------------------
-- [D] the peaked auxiliary form on `Γ₁(N)` (252, the row the wave made ready)
-- ---------------------------------------------------------------------------

/-
  The row is `ModularCurve.SiegelUnit.exists_gamma1_peaked_auxiliary_form_twelve_dvd`. This block
  instantiates it at `N = 4` — the least level at which the peak hypothesis is satisfiable, since a
  `β` must have `β 1 0 ∉ {0, 1, -1}` in `ZMod N` — and discharges that hypothesis at the concrete
  `β = !![1,0;2,1]`, using the port's subgroup dictionary
  `CongruenceSubgroup.mem_or_neg_mem_Gamma1_iff_and_exists_T_zpow_S_inv_iff` (the very premise the
  row's own proof consumes). The conclusion is not a restatement: it reads off the *exact* order of
  vanishing of the width-`1` expansion, the non-vanishing of the form itself (which the headline does
  not state), and the peak decay at that explicit `β`.
-/

namespace ModularCurve.Ready3ZoneD

open Filter Asymptotics
open scoped MatrixGroups ModularForm
open CongruenceSubgroup.LowerUnipotent

/-- `β = !![1,0;2,1] = Low 2` has `β 1 0 = 2`, so it lies outside `±Γ₁(4)` and so does every
`T`-translate — the two hypotheses the peak conjunct is stated under. -/
private theorem low_two_peak_hypotheses :
    ((Low 2 : SL(2, ℤ)) ∉ CongruenceSubgroup.Gamma1 4 ∧
        -(Low 2 : SL(2, ℤ)) ∉ CongruenceSubgroup.Gamma1 4) ∧
      ∀ j : ℤ, (Low 2 : SL(2, ℤ)) * ModularGroup.T ^ j * ModularGroup.S⁻¹ ∉
          CongruenceSubgroup.Gamma1 4 ∧
        -((Low 2 : SL(2, ℤ)) * ModularGroup.T ^ j * ModularGroup.S⁻¹) ∉
          CongruenceSubgroup.Gamma1 4 := by
  obtain ⟨hc1, hc2, -⟩ :=
    CongruenceSubgroup.mem_or_neg_mem_Gamma1_iff_and_exists_T_zpow_S_inv_iff 4 (Low 2)
  have hy0 : (((Low 2 : SL(2, ℤ)) 1 0 : ℤ) : ZMod 4) ≠ 0 := by
    rw [CongruenceSubgroup.LowerUnipotent.coe_Low]; decide +kernel
  have hy1 : (((Low 2 : SL(2, ℤ)) 1 0 : ℤ) : ZMod 4) ≠ 1 := by
    rw [CongruenceSubgroup.LowerUnipotent.coe_Low]; decide +kernel
  have hym1 : (((Low 2 : SL(2, ℤ)) 1 0 : ℤ) : ZMod 4) ≠ -1 := by
    rw [CongruenceSubgroup.LowerUnipotent.coe_Low]; decide +kernel
  refine ⟨⟨?_, ?_⟩, fun j => ⟨?_, ?_⟩⟩
  · intro h; exact hy0 (hc1.mp (Or.inl h)).1
  · intro h; exact hy0 (hc1.mp (Or.inr h)).1
  · intro h
    rcases hc2.mp ⟨j, Or.inl h⟩ with h' | h'
    · exact hy1 h'
    · exact hym1 h'
  · intro h
    rcases hc2.mp ⟨j, Or.inr h⟩ with h' | h'
    · exact hy1 h'
    · exact hym1 h'

/-- **The peaked auxiliary form at level `4`, read.**  Its width-`1` expansion vanishes exactly
below `m₀` and not at `m₀` (so the form is not zero), its weight is a multiple of `12`, its
width-`4` `S`-slash is integral after scaling by `4 ^ a`, and its `Low 2`-slash decays like
`exp (-2π (m₀ + δ) im)`. -/
theorem peaked_form_at_level_four :
    ∃ (w : ℤ) (m₀ a : ℕ) (δ : ℝ)
      (ϑ : ModularForm (CongruenceSubgroup.Gamma1 4 : Subgroup (GL (Fin 2) ℝ)) w),
      12 ∣ w ∧ 0 < δ ∧
      (∀ n : ℕ, n < m₀ → (UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff n = 0) ∧
      (UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff m₀ ≠ 0 ∧
      ϑ ≠ 0 ∧
      (∀ n : ℕ, IsIntegral ℤ ((4 : ℂ) ^ a * (UpperHalfPlane.qExpansion (4 : ℝ)
        ((⇑ϑ : UpperHalfPlane → ℂ) ∣[w] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff n)) ∧
      ((⇑ϑ : UpperHalfPlane → ℂ) ∣[w] ((Low 2 : SL(2, ℤ)) : GL (Fin 2) ℝ))
        =O[UpperHalfPlane.atImInfty]
        fun τ : UpperHalfPlane => Real.exp (-(2 * Real.pi * ((m₀ : ℝ) + δ)) * τ.im) := by
  obtain ⟨w, m₀, a, δ, ϑ, h12, -, hδ, hintN, hz, hne, -, -, hpeak⟩ :=
    ModularCurve.SiegelUnit.exists_gamma1_peaked_auxiliary_form_twelve_dvd 4 (by norm_num)
  refine ⟨w, m₀, a, δ, ϑ, h12, hδ, hz, hne, ?_, hintN, ?_⟩
  · intro hzero
    have : (UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff m₀ = 0 := by
      rw [hzero, FunLike.coe_zero, UpperHalfPlane.qExpansion_zero, map_zero]
    exact hne this
  · exact hpeak (Low 2) low_two_peak_hypotheses.1 low_two_peak_hypotheses.2

/-- **The odd-`k` branch, read.**  At level `4` and `k = 1` this row produces a form of **odd**
weight — the branch that multiplies the product form by the weight-three Eisenstein form — still with
the exact `m₀`-order of the width-`1` expansion, still non-zero, and still peaked at `Low 2`. -/
theorem peaked_form_odd_weight_at_level_four :
    ∃ (w : ℤ) (m₀ : ℕ) (δ : ℝ)
      (ϑ : ModularForm (CongruenceSubgroup.Gamma1 4 : Subgroup (GL (Fin 2) ℝ)) w),
      Odd w ∧ 0 < δ ∧ ϑ ≠ 0 ∧
      (∀ n : ℕ, n < m₀ → (UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff n = 0) ∧
      (UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff m₀ ≠ 0 ∧
      ((⇑ϑ : UpperHalfPlane → ℂ) ∣[w] ((Low 2 : SL(2, ℤ)) : GL (Fin 2) ℝ))
        =O[UpperHalfPlane.atImInfty]
        fun τ : UpperHalfPlane => Real.exp (-(2 * Real.pi * ((m₀ : ℝ) + δ)) * τ.im) := by
  obtain ⟨w, m₀, a, δ, ϑ, hEven, -, hδ, -, hz, hne, -, -, hpeak⟩ :=
    ModularCurve.exists_gamma1_peaked_auxiliary_form 4 (by norm_num) 1 (fun _ => by norm_num)
  obtain ⟨c, hc⟩ := hEven
  refine ⟨w, m₀, δ, ϑ, ⟨c - 1, by omega⟩, hδ, ?_, hz, hne,
    hpeak (Low 2) low_two_peak_hypotheses.1 low_two_peak_hypotheses.2⟩
  intro hzero
  have : (UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff m₀ = 0 := by
    rw [hzero, FunLike.coe_zero, UpperHalfPlane.qExpansion_zero, map_zero]
  exact hne this

end ModularCurve.Ready3ZoneD
