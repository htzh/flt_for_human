/-
  The ℘-torsion `q`-expansion vocabulary: the `q`-parameter powers `zetaN`/`qN`,
  the torsion series `wpTorsion`/`wpTorsionSeries`/`wpNorm`, the coefficient ring
  `kN` and the `wpMon*` coefficient model.  Interface lemmas that consume the
  headline `ModularForm.weierstrassP_torsion_qExpansion_package`, or the
  `r2_package` helper built on it, deliberately stay in the consumers (above the
  headline) rather than force a cycle.

  Shared by the `WLight` Fricke packages and `WeierstrassPTorsion`; lifted from the
  repeated `private` prelude (`P2M/Sol/S_WLight_frickeFunction_*`,
  `S_ModularForm_weierstrassP_torsion_qExpansion_package`, pinned `aa2d8b3`).
  Namespace `WLight`.
-/
import FLTForHuman.ModularForms.WeightOne.Defs.PeriodPair
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.Unramified.Field

noncomputable section

open Complex Real

open scoped UpperHalfPlane Manifold MatrixGroups ModularForm
open UpperHalfPlane hiding I
open ModularForm CuspForm ModularForm.CuspForm Polynomial Real.Polynomial Filter
open PeriodPair

namespace WLight

def zetaN (N : ℕ) : ℂ := cexp (2 * π * I / N)

def qN (N : ℕ) (τ : ℂ) : ℂ := cexp (2 * π * I * τ / N)

lemma zetaN_ne_zero (N : ℕ) : zetaN N ≠ 0 := Complex.exp_ne_zero _

def wpTail (N a₁ a₂ : ℕ) (p : ℕ+ × ℕ+) (τ : ℂ) : ℂ :=
  ((p.2 : ℕ) : ℂ) *
    (zetaN N ^ (a₂ * (p.2 : ℕ)) * qN N τ ^ (((p.1 : ℕ) * N + a₁) * (p.2 : ℕ)) +
      (zetaN N)⁻¹ ^ (a₂ * (p.2 : ℕ)) * qN N τ ^ (((p.1 : ℕ) * N - a₁) * (p.2 : ℕ)) -
        2 * qN N τ ^ ((p.1 : ℕ) * N * (p.2 : ℕ)))

def wpTorsion (N a₁ a₂ : ℕ) (τ : ℍ) : ℂ :=
  PeriodPair.weierstrassP (periodPairOfTau τ) (((a₁ : ℂ) * τ + a₂) / N)

def wpTorsionSeries (N a₁ a₂ : ℕ) (τ : ℂ) : ℂ :=
  (2 * π * I) ^ 2 *
    (zetaN N ^ a₂ * qN N τ ^ a₁ / (1 - zetaN N ^ a₂ * qN N τ ^ a₁) ^ 2 + 1 / 12 +
      ∑' p : ℕ+ × ℕ+, wpTail N a₁ a₂ p τ)

def kN (N : ℕ) : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {zetaN N}

lemma zetaN_mem_kN (N : ℕ) : zetaN N ∈ kN N :=
  IntermediateField.mem_adjoin_simple_self ℚ _

lemma zetaN_pow_mem_kN (N k : ℕ) : zetaN N ^ k ∈ kN N := pow_mem (zetaN_mem_kN N) k

lemma zetaN_inv_pow_mem_kN (N k : ℕ) : (zetaN N)⁻¹ ^ k ∈ kN N :=
  pow_mem (inv_mem (zetaN_mem_kN N)) k

lemma natCast_mem_kN (N m : ℕ) : (m : ℂ) ∈ kN N := natCast_mem _ m

lemma one_div_twelve_mem_kN (N : ℕ) : (1 / 12 : ℂ) ∈ kN N :=
  div_mem (one_mem _) (by exact_mod_cast natCast_mem_kN N 12)

def wpNormSeries (N a₁ a₂ : ℕ) (τ : ℂ) : ℂ :=
  zetaN N ^ a₂ * qN N τ ^ a₁ / (1 - zetaN N ^ a₂ * qN N τ ^ a₁) ^ 2 + 1 / 12 +
    ∑' p : ℕ+ × ℕ+, wpTail N a₁ a₂ p τ

lemma wpTorsionSeries_eq (N a₁ a₂ : ℕ) (τ : ℂ) :
    wpTorsionSeries N a₁ a₂ τ = (2 * π * I) ^ 2 * wpNormSeries N a₁ a₂ τ := rfl

def wpNorm (N a₁ a₂ : ℕ) (τ : ℍ) : ℂ := ((2 * π * I) ^ 2)⁻¹ * wpTorsion N a₁ a₂ τ

abbrev WpIdx : Type := Unit ⊕ ℕ+ ⊕ ((ℕ+ × ℕ+) × Fin 3)

def wpMonCoeff (N a₁ a₂ : ℕ) : WpIdx → ℂ
  | Sum.inl _ => 1 / 12 + if a₁ = 0 then zetaN N ^ a₂ / (1 - zetaN N ^ a₂) ^ 2 else 0
  | Sum.inr (Sum.inl m) => if a₁ = 0 then 0 else ((m : ℕ) : ℂ) * zetaN N ^ (a₂ * (m : ℕ))
  | Sum.inr (Sum.inr (p, i)) =>
      ![((p.2 : ℕ) : ℂ) * zetaN N ^ (a₂ * (p.2 : ℕ)),
        ((p.2 : ℕ) : ℂ) * (zetaN N)⁻¹ ^ (a₂ * (p.2 : ℕ)),
        -2 * ((p.2 : ℕ) : ℂ)] i

def wpMonExp (N a₁ : ℕ) : WpIdx → ℕ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl m) => if a₁ = 0 then (m : ℕ) else a₁ * (m : ℕ)
  | Sum.inr (Sum.inr (p, i)) =>
      ![((p.1 : ℕ) * N + a₁) * (p.2 : ℕ), ((p.1 : ℕ) * N - a₁) * (p.2 : ℕ),
        (p.1 : ℕ) * N * (p.2 : ℕ)] i

def wpQCoeff (N a₁ a₂ : ℕ) (n : ℕ) : ℂ :=
  ∑' i : (wpMonExp N a₁ ⁻¹' {n}), wpMonCoeff N a₁ a₂ i

lemma wpMonCoeff_mem_kN (N a₁ a₂ : ℕ) (i : WpIdx) : wpMonCoeff N a₁ a₂ i ∈ kN N := by
  rcases i with u | m | ⟨p, i⟩
  · simp only [wpMonCoeff]
    split_ifs
    · exact add_mem (one_div_twelve_mem_kN N) (div_mem (zetaN_pow_mem_kN N _)
        (pow_mem (sub_mem (one_mem _) (zetaN_pow_mem_kN N _)) 2))
    · exact add_mem (one_div_twelve_mem_kN N) (zero_mem _)
  · simp only [wpMonCoeff]
    split_ifs
    · exact zero_mem _
    · exact mul_mem (natCast_mem_kN N _) (zetaN_pow_mem_kN N _)
  · simp only [wpMonCoeff]
    fin_cases i
    · exact mul_mem (natCast_mem_kN N _) (zetaN_pow_mem_kN N _)
    · exact mul_mem (natCast_mem_kN N _) (zetaN_inv_pow_mem_kN N _)
    · simp only [Fin.reduceFinMk, Matrix.cons_val]
      exact mul_mem (neg_mem (by exact_mod_cast natCast_mem_kN N 2)) (natCast_mem_kN N _)

def frickeH (N a₁ a₂ : ℕ) : ℍ → ℂ := (⇑E₄ * ⇑E₆ : ℍ → ℂ) * wpNorm N a₁ a₂

end WLight
