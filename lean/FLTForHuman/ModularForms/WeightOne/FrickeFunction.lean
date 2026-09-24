/-
  The fricke-function packages (SET-8 order 2).

  Statements verbatim from the pinned wrappers
  `Theorems/Thm_WLight_frickeFunction_{modularity_package,orbit_package,intBaseChange}.lean`;
  proofs transcribed from the matching `P2M/Sol/S_WLight_frickeFunction_*` files
  (1,180 + 1,037 + 1,500 lines) and adapted to mathlib `v4.34.0`.  Each package's
  pin helpers are `private` in their own namespace inside `WLight`, so the three
  pin files' repeated definitions (`periodPairOfTau`, `zetaN`, `wpNorm`,
  `frickeF`, `KPoleAt`, `qExpansion_coeff_width`, ...) do not collide; the three
  headlines are the module's only public surface.

  The package-to-package edges are the pin's own: the orbit package consumes
  `WLight.frickeFunction_modularity_package` and `WLight.levelOne_hauptmodul_package`
  (SET-7), and `intBaseChange` consumes `frickeFunction_modularity_package`,
  `frickeFunction_orbit_package`, `WLight.exists_mdifferentiable_div_of_monicRel`
  (SET-8 order 1) and SET-5's `IsIntegral.mem_span_of_adjoin_simple_constants{,_transcendental}`.
  The torsion package is consumed through the already-ported public
  `ModularForm.weierstrassP_torsion_qExpansion_package`.

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WLight_frickeFunction_modularity_package.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WLight_frickeFunction_orbit_package.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WLight_frickeFunction_intBaseChange.lean

  v4.34 drifts hit here: `if_pos`/`if_neg` → `ite_eq_left`/`ite_eq_right`,
  `if_true` → `ite_true`, `ModularForm.coe_sub` → `FunLike.coe_sub`, an explicit
  `EisensteinSeries.` prefix for `E_qExpansion_coeff`, and the pin's local
  `set_option maxHeartbeats 3200000`/`synthInstance.maxHeartbeats 1600000` are
  **not** transcribed (the project's global cap is `4000000`, above both).
-/

import FLTForHuman.ModularForms.WeightOne.Basic
import FLTForHuman.ModularForms.WeightOne.MonicRel
import FLTForHuman.ModularForms.WeightOne.LevelOneHauptmodul
import FLTForHuman.ModularForms.WeightOne.WeierstrassPTorsion
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

set_option autoImplicit false

noncomputable section

open Complex Real
open scoped Topology Manifold MatrixGroups ModularForm UpperHalfPlane Polynomial

namespace WLight

namespace WLightFriMod

section B1_homogeneity

open PeriodPair

private def smulPeriodPair (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) : PeriodPair where
  ω₁ := a * L.ω₁
  ω₂ := a * L.ω₂
  indep := LinearIndependent.pair_iff.mpr fun s t hst => by
    refine LinearIndependent.pair_iff.mp L.indep s t ?_
    have h0 : a * (s • L.ω₁ + t • L.ω₂) = 0 := by
      rw [mul_add, mul_smul_comm, mul_smul_comm]; exact hst
    exact (mul_eq_zero.mp h0).resolve_left ha

@[scoped simp] private lemma smulPeriodPair_ω₁ (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) :
    (smulPeriodPair a ha L).ω₁ = a * L.ω₁ := rfl

@[scoped simp] private lemma smulPeriodPair_ω₂ (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) :
    (smulPeriodPair a ha L).ω₂ = a * L.ω₂ := rfl

private lemma mem_smulPeriodPair_lattice {a : ℂ} (ha : a ≠ 0) (L : PeriodPair) {x : ℂ} :
    x ∈ (smulPeriodPair a ha L).lattice ↔ ∃ y ∈ L.lattice, x = a * y := by
  simp only [mem_lattice, smulPeriodPair_ω₁, smulPeriodPair_ω₂]
  constructor
  · rintro ⟨m, n, h⟩
    exact ⟨(m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂, ⟨m, n, rfl⟩, by rw [← h]; ring⟩
  · rintro ⟨y, ⟨m, n, h⟩, rfl⟩
    exact ⟨m, n, by rw [← h]; ring⟩

private def smulLatticeEquiv (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) :
    L.lattice ≃ (smulPeriodPair a ha L).lattice where
  toFun l := ⟨a * l, (mem_smulPeriodPair_lattice ha L).mpr ⟨l, l.2, rfl⟩⟩
  invFun l := ⟨a⁻¹ * l, by
    obtain ⟨y, hy, hxy⟩ := (mem_smulPeriodPair_lattice ha L).mp l.2
    rw [hxy, inv_mul_cancel_left₀ ha]; exact hy⟩
  left_inv l := Subtype.ext (inv_mul_cancel_left₀ ha _)
  right_inv l := Subtype.ext (mul_inv_cancel_left₀ ha _)

@[scoped simp] private lemma smulLatticeEquiv_coe (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) (l : L.lattice) :
    ((smulLatticeEquiv a ha L) l : ℂ) = a * l := rfl

private theorem weierstrassP_smulPeriodPair (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) (z : ℂ) :
    weierstrassP (smulPeriodPair a ha L) (a * z) = a⁻¹ ^ 2 * weierstrassP L z := by
  have key : ∀ u : ℂ, 1 / (a * u) ^ 2 = a⁻¹ ^ 2 * (1 / u ^ 2) := fun u => by
    simp [one_div, mul_pow, inv_pow, mul_comm]
  simp only [weierstrassP]
  rw [← (smulLatticeEquiv a ha L).tsum_eq, ← tsum_mul_left]
  congr with l
  simp only [smulLatticeEquiv_coe]
  rw [show a * z - a * (l : ℂ) = a * (z - l) by ring, key, key, mul_sub]

end B1_homogeneity

section R4aFloor
open scoped UpperHalfPlane Manifold MatrixGroups
open UpperHalfPlane hiding I
open ModularForm ModularFormClass CuspForm ModularForm.CuspForm Polynomial Real.Polynomial Filter
open scoped ModularForm ModularFormClass CuspForm ModularForm.CuspForm Polynomial Real.Polynomial Filter

private def periodPairOfTau (τ : ℍ) : PeriodPair where
  ω₁ := (τ : ℂ)
  ω₂ := 1
  indep := LinearIndependent.pair_iff.mpr fun s t hst ↦ by
    have him : s * (τ : ℂ).im = 0 := by
      have := congrArg Complex.im hst
      simpa [Complex.add_im, Complex.smul_im, smul_eq_mul] using this
    have hs : s = 0 :=
      (mul_eq_zero.mp him).resolve_right (UpperHalfPlane.coe_im τ ▸ τ.im_ne_zero)
    subst hs
    simpa using hst

@[scoped simp] private lemma periodPairOfTau_ω₁ (τ : ℍ) : (periodPairOfTau τ).ω₁ = (τ : ℂ) := rfl
@[scoped simp] private lemma periodPairOfTau_ω₂ (τ : ℍ) : (periodPairOfTau τ).ω₂ = 1 := rfl

private def zetaN (N : ℕ) : ℂ := cexp (2 * π * I / N)

private def qN (N : ℕ) (τ : ℂ) : ℂ := cexp (2 * π * I * τ / N)

private lemma zetaN_ne_zero (N : ℕ) : zetaN N ≠ 0 := Complex.exp_ne_zero _

private def wpTail (N a₁ a₂ : ℕ) (p : ℕ+ × ℕ+) (τ : ℂ) : ℂ :=
  ((p.2 : ℕ) : ℂ) *
    (zetaN N ^ (a₂ * (p.2 : ℕ)) * qN N τ ^ (((p.1 : ℕ) * N + a₁) * (p.2 : ℕ)) +
      (zetaN N)⁻¹ ^ (a₂ * (p.2 : ℕ)) * qN N τ ^ (((p.1 : ℕ) * N - a₁) * (p.2 : ℕ)) -
        2 * qN N τ ^ ((p.1 : ℕ) * N * (p.2 : ℕ)))

private def wpTorsion (N a₁ a₂ : ℕ) (τ : ℍ) : ℂ :=
  PeriodPair.weierstrassP (periodPairOfTau τ) (((a₁ : ℂ) * τ + a₂) / N)

private def wpTorsionSeries (N a₁ a₂ : ℕ) (τ : ℂ) : ℂ :=
  (2 * π * I) ^ 2 *
    (zetaN N ^ a₂ * qN N τ ^ a₁ / (1 - zetaN N ^ a₂ * qN N τ ^ a₁) ^ 2 + 1 / 12 +
      ∑' p : ℕ+ × ℕ+, wpTail N a₁ a₂ p τ)

section RatCoeffClosure

private lemma ratCoeff_mul {p q : PowerSeries ℂ}
    (hp : ∀ n : ℕ, ∃ a : ℚ, p.coeff n = (a : ℂ)) (hq : ∀ n : ℕ, ∃ a : ℚ, q.coeff n = (a : ℂ)) :
    ∀ n : ℕ, ∃ a : ℚ, (p * q).coeff n = (a : ℂ) := by
  choose F hF using hp
  choose G hG using hq
  intro n
  refine ⟨∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, F ij.1 * G ij.2, ?_⟩
  rw [PowerSeries.coeff_mul]
  push_cast
  exact Finset.sum_congr rfl fun ij _ => by rw [hF, hG]

private lemma ratCoeff_sub {p q : PowerSeries ℂ}
    (hp : ∀ n : ℕ, ∃ a : ℚ, p.coeff n = (a : ℂ)) (hq : ∀ n : ℕ, ∃ a : ℚ, q.coeff n = (a : ℂ)) :
    ∀ n : ℕ, ∃ a : ℚ, (p - q).coeff n = (a : ℂ) := by
  intro n
  obtain ⟨a, ha⟩ := hp n
  obtain ⟨b, hb⟩ := hq n
  exact ⟨a - b, by rw [map_sub, ha, hb]; push_cast; ring⟩

end RatCoeffClosure

private def kN (N : ℕ) : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {zetaN N}

private lemma zetaN_mem_kN (N : ℕ) : zetaN N ∈ kN N :=
  IntermediateField.mem_adjoin_simple_self ℚ _

private lemma zetaN_pow_mem_kN (N k : ℕ) : zetaN N ^ k ∈ kN N := pow_mem (zetaN_mem_kN N) k

private lemma zetaN_inv_pow_mem_kN (N k : ℕ) : (zetaN N)⁻¹ ^ k ∈ kN N :=
  pow_mem (inv_mem (zetaN_mem_kN N)) k

private lemma natCast_mem_kN (N m : ℕ) : (m : ℂ) ∈ kN N := natCast_mem _ m

private lemma one_div_twelve_mem_kN (N : ℕ) : (1 / 12 : ℂ) ∈ kN N :=
  div_mem (one_mem _) (by exact_mod_cast natCast_mem_kN N 12)

private def wpNormSeries (N a₁ a₂ : ℕ) (τ : ℂ) : ℂ :=
  zetaN N ^ a₂ * qN N τ ^ a₁ / (1 - zetaN N ^ a₂ * qN N τ ^ a₁) ^ 2 + 1 / 12 +
    ∑' p : ℕ+ × ℕ+, wpTail N a₁ a₂ p τ

private lemma wpTorsionSeries_eq (N a₁ a₂ : ℕ) (τ : ℂ) :
    wpTorsionSeries N a₁ a₂ τ = (2 * π * I) ^ 2 * wpNormSeries N a₁ a₂ τ := rfl

private def wpNorm (N a₁ a₂ : ℕ) (τ : ℍ) : ℂ := ((2 * π * I) ^ 2)⁻¹ * wpTorsion N a₁ a₂ τ

private abbrev WpIdx : Type := Unit ⊕ ℕ+ ⊕ ((ℕ+ × ℕ+) × Fin 3)

private def wpMonCoeff (N a₁ a₂ : ℕ) : WpIdx → ℂ
  | Sum.inl _ => 1 / 12 + if a₁ = 0 then zetaN N ^ a₂ / (1 - zetaN N ^ a₂) ^ 2 else 0
  | Sum.inr (Sum.inl m) => if a₁ = 0 then 0 else ((m : ℕ) : ℂ) * zetaN N ^ (a₂ * (m : ℕ))
  | Sum.inr (Sum.inr (p, i)) =>
      ![((p.2 : ℕ) : ℂ) * zetaN N ^ (a₂ * (p.2 : ℕ)),
        ((p.2 : ℕ) : ℂ) * (zetaN N)⁻¹ ^ (a₂ * (p.2 : ℕ)),
        -2 * ((p.2 : ℕ) : ℂ)] i

private def wpMonExp (N a₁ : ℕ) : WpIdx → ℕ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl m) => if a₁ = 0 then (m : ℕ) else a₁ * (m : ℕ)
  | Sum.inr (Sum.inr (p, i)) =>
      ![((p.1 : ℕ) * N + a₁) * (p.2 : ℕ), ((p.1 : ℕ) * N - a₁) * (p.2 : ℕ),
        (p.1 : ℕ) * N * (p.2 : ℕ)] i

private def wpQCoeff (N a₁ a₂ : ℕ) (n : ℕ) : ℂ :=
  ∑' i : (wpMonExp N a₁ ⁻¹' {n}), wpMonCoeff N a₁ a₂ i

private lemma wpMonCoeff_mem_kN (N a₁ a₂ : ℕ) (i : WpIdx) : wpMonCoeff N a₁ a₂ i ∈ kN N := by
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

private def frickeH (N a₁ a₂ : ℕ) : ℍ → ℂ := (⇑E₄ * ⇑E₆ : ℍ → ℂ) * wpNorm N a₁ a₂

private theorem r2_package {N : ℕ} (hN : N ≠ 0) :
    (∀ a₁ a₂ : ℕ, a₁ < N → a₂ < N → (a₁ ≠ 0 ∨ a₂ ≠ 0) →
        MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (wpNorm N a₁ a₂)
        ∧ Function.Periodic ((wpNorm N a₁ a₂) ∘ ofComplex) (N : ℂ)
        ∧ IsBoundedAtImInfty (wpNorm N a₁ a₂)
        ∧ ∀ n, (qExpansion N (wpNorm N a₁ a₂)).coeff n ∈ kN N)
    ∧ (∀ a₁ a₂ b₁ b₂ : ℕ, a₁ < N → a₂ < N → (a₁ ≠ 0 ∨ a₂ ≠ 0) →
        b₁ < N → b₂ < N → (b₁ ≠ 0 ∨ b₂ ≠ 0) →
        wpNorm N a₁ a₂ = wpNorm N b₁ b₂ →
        (b₁ = a₁ ∧ b₂ = a₂) ∨ (b₁ = (N - a₁) % N ∧ b₂ = (N - a₂) % N))
    ∧ (∃ S : ℕ → ℕ → PowerSeries ↑(kN N),
        (∀ a₁ a₂ : ℕ, a₁ < N → a₂ < N → (a₁ ≠ 0 ∨ a₂ ≠ 0) →
          (S a₁ a₂).map (algebraMap ↑(kN N) ℂ) = qExpansion N (wpNorm N a₁ a₂))
        ∧ ∀ s : ℕ, s.Coprime N → ∀ φ : ↑(kN N) →+* ℂ,
            φ ⟨zetaN N, zetaN_mem_kN N⟩ = zetaN N ^ s →
            ∀ a₁ a₂ : ℕ, a₁ < N → a₂ < N → (a₁ ≠ 0 ∨ a₂ ≠ 0) →
              (S a₁ a₂).map φ = qExpansion N (wpNorm N a₁ (s * a₂ % N)))
    ∧ (∀ f : ℍ → ℂ, Function.Periodic (f ∘ ofComplex) (1 : ℂ) →
        MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → IsBoundedAtImInfty f →
        ∀ n, (qExpansion N f).coeff n =
          if N ∣ n then (qExpansion 1 f).coeff (n / N) else 0)
    ∧ (∀ n, ∃ q : ℚ, (qExpansion 1 (⇑ModularForm.E₄ : ℍ → ℂ)).coeff n = (q : ℂ))
    ∧ (∀ n, ∃ q : ℚ, (qExpansion 1 (⇑ModularForm.E₆ : ℍ → ℂ)).coeff n = (q : ℂ))
    ∧ (∀ n, ∃ q : ℚ,
        (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)).coeff n = (q : ℂ)) :=
  ModularForm.weierstrassP_torsion_qExpansion_package N hN periodPairOfTau fun _ ↦ ⟨rfl, rfl⟩

private theorem periodic_wpNorm {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N) (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) :
    Function.Periodic (wpNorm N a₁ a₂ ∘ ofComplex) N :=
  ((r2_package (by omega)).1 a₁ a₂ ha₁ ha₂ h0).2.1

private theorem mdifferentiable_wpNorm {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (wpNorm N a₁ a₂) :=
  ((r2_package (by omega)).1 a₁ a₂ ha₁ ha₂ h0).1

private theorem isBoundedAtImInfty_wpNorm {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) : IsBoundedAtImInfty (wpNorm N a₁ a₂) :=
  ((r2_package (by omega)).1 a₁ a₂ ha₁ ha₂ h0).2.2.1

private theorem qExpansion_wpNorm_coeff_mem_kN {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) (n : ℕ) : (qExpansion N (wpNorm N a₁ a₂)).coeff n ∈ kN N :=
  ((r2_package (by omega)).1 a₁ a₂ ha₁ ha₂ h0).2.2.2 n

private theorem wpNorm_eq_imp {N a₁ a₂ b₁ b₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (ha0 : a₁ ≠ 0 ∨ a₂ ≠ 0) (hb₁ : b₁ < N) (hb₂ : b₂ < N) (hb0 : b₁ ≠ 0 ∨ b₂ ≠ 0)
    (h : wpNorm N a₁ a₂ = wpNorm N b₁ b₂) :
    (b₁ = a₁ ∧ b₂ = a₂) ∨ (b₁ = (N - a₁) % N ∧ b₂ = (N - a₂) % N) :=
  (r2_package (by omega)).2.1 a₁ a₂ b₁ b₂ ha₁ ha₂ ha0 hb₁ hb₂ hb0 h

private theorem isBoundedAtImInfty_frickeH {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) : IsBoundedAtImInfty (frickeH N a₁ a₂) :=
  ((ModularFormClass.bdd_at_infty ModularForm.E₄).mul (ModularFormClass.bdd_at_infty ModularForm.E₆)).mul
    (isBoundedAtImInfty_wpNorm ha₁ ha₂ h0)

private theorem qExpansion_coeff_width (f : ℍ → ℂ) {N : ℕ} (hN : N ≠ 0)
    (hper : Function.Periodic (f ∘ ofComplex) 1) (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbd : IsBoundedAtImInfty f) (n : ℕ) :
    (qExpansion N f).coeff n =
      if N ∣ n then (qExpansion 1 f).coeff (n / N) else 0 :=
  (r2_package hN).2.2.2.1 f hper hhol hbd n

private theorem periodic_frickeH {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N) (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) :
    Function.Periodic (frickeH N a₁ a₂ ∘ ofComplex) N := by
  have h4 := (SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄
    one_mem_strictPeriods_SL).nat_mul N
  have h6 := (SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₆
    one_mem_strictPeriods_SL).nat_mul N
  have hw := periodic_wpNorm ha₁ ha₂ h0
  intro τ
  have e4 := h4 τ; have e6 := h6 τ; have ew := hw τ
  simp only [Complex.ofReal_one, mul_one, Function.comp_apply] at e4 e6 ew
  simp only [Function.comp_apply, frickeH, Pi.mul_apply, e4, e6, ew]

private theorem mdifferentiable_frickeH {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (frickeH N a₁ a₂) :=
  (ModularForm.E₄.holo'.mul ModularForm.E₆.holo').mul (mdifferentiable_wpNorm ha₁ ha₂ h0)

private theorem wpNorm_qExpansion_model {N : ℕ} (hN : N ≠ 0) :
    ∃ S : ℕ → ℕ → PowerSeries ↑(kN N),
      (∀ a₁ a₂ : ℕ, a₁ < N → a₂ < N → (a₁ ≠ 0 ∨ a₂ ≠ 0) →
        (S a₁ a₂).map (algebraMap ↑(kN N) ℂ) = qExpansion N (wpNorm N a₁ a₂)) ∧
      ∀ s : ℕ, s.Coprime N → ∀ φ : ↑(kN N) →+* ℂ,
        φ ⟨zetaN N, zetaN_mem_kN N⟩ = zetaN N ^ s →
        ∀ a₁ a₂ : ℕ, a₁ < N → a₂ < N → (a₁ ≠ 0 ∨ a₂ ≠ 0) →
          (S a₁ a₂).map φ = qExpansion N (wpNorm N a₁ (s * a₂ % N)) :=
  (r2_package hN).2.2.1

private theorem qExpansion_one_E4_rat (n : ℕ) :
    ∃ q : ℚ, (qExpansion 1 (⇑ModularForm.E₄ : ℍ → ℂ)).coeff n = (q : ℂ) :=
  (r2_package one_ne_zero).2.2.2.2.1 n

private theorem qExpansion_one_E6_rat (n : ℕ) :
    ∃ q : ℚ, (qExpansion 1 (⇑ModularForm.E₆ : ℍ → ℂ)).coeff n = (q : ℂ) :=
  (r2_package one_ne_zero).2.2.2.2.2.1 n

private lemma analyticAt_cuspFunction_zero_of {N : ℕ} [NeZero N] {g : ℍ → ℂ}
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (hper : Function.Periodic (g ∘ ofComplex) N)
    (hbd : IsBoundedAtImInfty g) :
    AnalyticAt ℂ (cuspFunction N g) 0 :=
  analyticAt_cuspFunction_zero (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)) hper hhol hbd

end R4aFloor

section B3_fricke

open PeriodPair
open scoped UpperHalfPlane MatrixGroups

private def latticeEquivOfEq {L L' : PeriodPair} (h : L.lattice = L'.lattice) :
    L.lattice ≃ L'.lattice where
  toFun l := ⟨l.1, h.le l.2⟩
  invFun l := ⟨l.1, h.ge l.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[scoped simp] private lemma latticeEquivOfEq_coe {L L' : PeriodPair} (h : L.lattice = L'.lattice)
    (l : L.lattice) : ((latticeEquivOfEq h l : L'.lattice) : ℂ) = (l : ℂ) := rfl

private theorem weierstrassP_of_lattice_eq {L L' : PeriodPair} (h : L.lattice = L'.lattice) (z : ℂ) :
    weierstrassP L z = weierstrassP L' z := by
  simp only [weierstrassP]
  rw [← (latticeEquivOfEq h).tsum_eq]
  rfl

private theorem G_of_lattice_eq {L L' : PeriodPair} (h : L.lattice = L'.lattice) (n : ℕ) :
    L.G n = L'.G n := by
  simp only [G]
  rw [← (latticeEquivOfEq h).tsum_eq]
  rfl

private theorem G_smulPeriodPair (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) (n : ℕ) :
    (smulPeriodPair a ha L).G n = a⁻¹ ^ n * L.G n := by
  simp only [G]
  rw [← (smulLatticeEquiv a ha L).tsum_eq, ← tsum_mul_left]
  congr with l
  simp only [smulLatticeEquiv_coe, mul_pow]
  rw [mul_inv, inv_pow]

private theorem g₂_smulPeriodPair (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) :
    (smulPeriodPair a ha L).g₂ = a⁻¹ ^ 4 * L.g₂ := by
  simp only [g₂, G_smulPeriodPair]; ring

private theorem g₃_smulPeriodPair (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) :
    (smulPeriodPair a ha L).g₃ = a⁻¹ ^ 6 * L.g₃ := by
  simp only [g₃, G_smulPeriodPair]; ring

private def latticeDisc (L : PeriodPair) : ℂ := L.g₂ ^ 3 - 27 * L.g₃ ^ 2

private theorem latticeDisc_smulPeriodPair (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) :
    latticeDisc (smulPeriodPair a ha L) = a⁻¹ ^ 12 * latticeDisc L := by
  simp only [latticeDisc, g₂_smulPeriodPair, g₃_smulPeriodPair]; ring

private theorem g₂_of_lattice_eq {L L' : PeriodPair} (h : L.lattice = L'.lattice) : L.g₂ = L'.g₂ := by
  simp [g₂, G_of_lattice_eq h]

private theorem g₃_of_lattice_eq {L L' : PeriodPair} (h : L.lattice = L'.lattice) : L.g₃ = L'.g₃ := by
  simp [g₃, G_of_lattice_eq h]

private theorem latticeDisc_of_lattice_eq {L L' : PeriodPair} (h : L.lattice = L'.lattice) :
    latticeDisc L = latticeDisc L' := by
  simp [latticeDisc, g₂_of_lattice_eq h, g₃_of_lattice_eq h]

private def frickePrefactor (L : PeriodPair) : ℂ := L.g₂ * L.g₃ / latticeDisc L

private theorem frickePrefactor_smulPeriodPair (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) :
    frickePrefactor (smulPeriodPair a ha L) = a ^ 2 * frickePrefactor L := by
  have h12 : (a : ℂ)⁻¹ ^ 12 ≠ 0 := pow_ne_zero _ (inv_ne_zero ha)
  simp only [frickePrefactor, g₂_smulPeriodPair, g₃_smulPeriodPair, latticeDisc_smulPeriodPair]
  field_simp

private theorem frickePrefactor_of_lattice_eq {L L' : PeriodPair} (h : L.lattice = L'.lattice) :
    frickePrefactor L = frickePrefactor L' := by
  simp [frickePrefactor, g₂_of_lattice_eq h, g₃_of_lattice_eq h, latticeDisc_of_lattice_eq h]

end B3_fricke

section B3_fricke_tier2

open PeriodPair Matrix
open scoped UpperHalfPlane MatrixGroups

private theorem span_SL2_basis_change {a b c d : ℤ} (hdet : a * d - b * c = 1) (ω₁ ω₂ : ℂ) :
    (Submodule.span ℤ {(a : ℂ) * ω₁ + (b : ℂ) * ω₂, (c : ℂ) * ω₁ + (d : ℂ) * ω₂} : Submodule ℤ ℂ)
      = Submodule.span ℤ {ω₁, ω₂} := by
  have hdetC : (a : ℂ) * d - b * c = 1 := by exact_mod_cast hdet
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
  · rw [Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨Submodule.mem_span_pair.mpr ⟨a, b, by simp [zsmul_eq_mul]⟩,
           Submodule.mem_span_pair.mpr ⟨c, d, by simp [zsmul_eq_mul]⟩⟩
  · rw [Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨Submodule.mem_span_pair.mpr ⟨d, -b, ?_⟩,
            Submodule.mem_span_pair.mpr ⟨-c, a, ?_⟩⟩
    · simp only [zsmul_eq_mul, Int.cast_neg]; linear_combination ω₁ * hdetC
    · simp only [zsmul_eq_mul, Int.cast_neg]; linear_combination ω₂ * hdetC

private def denomZ (γ : SL(2, ℤ)) (τ : ℂ) : ℂ := (γ 1 0 : ℤ) * τ + (γ 1 1 : ℤ)

private def numZ (γ : SL(2, ℤ)) (τ : ℂ) : ℂ := (γ 0 0 : ℤ) * τ + (γ 0 1 : ℤ)

private lemma denomZ_ne_zero (γ : SL(2, ℤ)) (τ : ℍ) : denomZ γ (τ : ℂ) ≠ 0 := by
  intro h
  have him : ((γ 1 0 : ℤ) : ℝ) * (τ : ℂ).im = 0 := by
    have := congrArg Complex.im h
    simp only [denomZ, Complex.add_im, Complex.mul_im, Complex.intCast_im, zero_mul,
      Complex.intCast_re, add_zero, Complex.zero_im] at this
    linarith
  have hc0 : (γ 1 0 : ℤ) = 0 := by
    rcases mul_eq_zero.mp him with h | h
    · exact_mod_cast h
    · exact absurd h (UpperHalfPlane.coe_im τ ▸ τ.im_ne_zero)
  have hd0 : (γ 1 1 : ℤ) = 0 := by
    have := h
    rw [denomZ, hc0] at this
    simpa using this
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2; rwa [Matrix.det_fin_two] at this
  rw [hc0, hd0] at hdet
  simp at hdet

private lemma coe_SL2Z_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    ((γ • τ : ℍ) : ℂ) = numZ γ (τ : ℂ) / denomZ γ (τ : ℂ) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply, numZ, denomZ]
  have hcast : ∀ i j : Fin 2, ((algebraMap ℤ ℝ (γ i j) : ℝ) : ℂ) = ((γ i j : ℤ) : ℂ) := by
    intro i j; simp [eq_intCast]
  rw [hcast, hcast, hcast, hcast]

private theorem mem_lattice_smul_SL2 (γ : SL(2, ℤ)) (τ : ℍ) (x : ℂ) :
    x ∈ (periodPairOfTau (γ • τ)).lattice
      ↔ denomZ γ τ * x ∈ (periodPairOfTau τ).lattice := by
  have hd : denomZ γ (τ : ℂ) ≠ 0 := denomZ_ne_zero γ τ
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2; rwa [Matrix.det_fin_two] at this
  have hspan := span_SL2_basis_change hdet (τ : ℂ) (1 : ℂ)
  simp only [mul_one] at hspan
  have hlatτ : (periodPairOfTau τ).lattice = Submodule.span ℤ {(τ : ℂ), 1} := rfl
  constructor
  · intro hx
    obtain ⟨m, n, hmn⟩ := PeriodPair.mem_lattice.mp hx
    simp only [periodPairOfTau_ω₁, periodPairOfTau_ω₂, mul_one, coe_SL2Z_smul] at hmn
    rw [hlatτ, ← hspan]
    refine Submodule.mem_span_pair.mpr ⟨m, n, ?_⟩
    have hdx : denomZ γ τ * x = (m : ℂ) * numZ γ τ + (n : ℂ) * denomZ γ τ := by
      rw [← hmn]; field_simp
    simp only [zsmul_eq_mul]
    rw [hdx, numZ, denomZ]
  · intro hx
    rw [hlatτ, ← hspan] at hx
    obtain ⟨p, q, hpq⟩ := Submodule.mem_span_pair.mp hx
    simp only [zsmul_eq_mul] at hpq
    refine PeriodPair.mem_lattice.mpr ⟨p, q, ?_⟩
    simp only [periodPairOfTau_ω₁, periodPairOfTau_ω₂, mul_one, coe_SL2Z_smul]
    have key : (p : ℂ) * numZ γ τ + (q : ℂ) * denomZ γ τ = denomZ γ τ * x := by
      rw [← hpq, numZ, denomZ]
    field_simp
    linear_combination key

private theorem periodPairOfTau_smul_lattice_eq (γ : SL(2, ℤ)) (τ : ℍ) :
    (periodPairOfTau (γ • τ)).lattice
      = (smulPeriodPair (denomZ γ τ)⁻¹ (inv_ne_zero (denomZ_ne_zero γ τ))
          (periodPairOfTau τ)).lattice := by
  have hd : denomZ γ (τ : ℂ) ≠ 0 := denomZ_ne_zero γ τ
  ext x
  rw [mem_lattice_smul_SL2, mem_smulPeriodPair_lattice]
  constructor
  · intro hx
    exact ⟨denomZ γ τ * x, hx, by field_simp⟩
  · rintro ⟨y, hy, rfl⟩
    rwa [mul_inv_cancel_left₀ hd]

private def frickeTorsionPt (N : ℕ) (a : Fin 2 → ZMod N) (τ : ℍ) : ℂ :=
  (((a 0).val : ℂ) * (τ : ℂ) + ((a 1).val : ℂ)) / (N : ℂ)

private lemma weierstrassP_torsionPt_lift_irrel {N : ℕ} [NeZero N] (a : Fin 2 → ZMod N) (τ : ℍ)
    (b₁ b₂ : ℤ) (h₁ : (b₁ : ZMod N) = a 0) (h₂ : (b₂ : ZMod N) = a 1) :
    weierstrassP (periodPairOfTau τ) (((b₁ : ℂ) * τ + (b₂ : ℂ)) / (N : ℂ))
      = weierstrassP (periodPairOfTau τ) (frickeTorsionPt N a τ) := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have cast_val : ∀ i : Fin 2, ((a i).val : ZMod N) = a i := fun i ↦ by
    rw [ZMod.natCast_val, ZMod.cast_id]
  have hdvd₁ : (N : ℤ) ∣ b₁ - ((a 0).val : ℤ) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by push_cast; rw [h₁, cast_val, sub_self])
  have hdvd₂ : (N : ℤ) ∣ b₂ - ((a 1).val : ℤ) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by push_cast; rw [h₂, cast_val, sub_self])
  obtain ⟨k₁, hk₁⟩ := hdvd₁
  obtain ⟨k₂, hk₂⟩ := hdvd₂
  have hmem : ((k₁ : ℂ) * (τ : ℂ) + (k₂ : ℂ)) ∈ (periodPairOfTau τ).lattice :=
    PeriodPair.mem_lattice.mpr ⟨k₁, k₂, by
      simp only [periodPairOfTau_ω₁, periodPairOfTau_ω₂, mul_one]⟩
  have e₁ : (b₁ : ℂ) = ((a 0).val : ℂ) + (N : ℂ) * (k₁ : ℂ) := by
    have hc : (b₁ : ℂ) - ((a 0).val : ℂ) = (N : ℂ) * (k₁ : ℂ) := by exact_mod_cast hk₁
    linear_combination hc
  have e₂ : (b₂ : ℂ) = ((a 1).val : ℂ) + (N : ℂ) * (k₂ : ℂ) := by
    have hc : (b₂ : ℂ) - ((a 1).val : ℂ) = (N : ℂ) * (k₂ : ℂ) := by exact_mod_cast hk₂
    linear_combination hc
  have step : ((b₁ : ℂ) * τ + (b₂ : ℂ)) / (N : ℂ)
      = frickeTorsionPt N a τ + ((k₁ : ℂ) * τ + (k₂ : ℂ)) := by
    unfold frickeTorsionPt; rw [e₁, e₂]; field_simp; ring
  rw [step, (periodPairOfTau τ).weierstrassP_add_coe _ ⟨_, hmem⟩]

private def frickeFn (N : ℕ) (a : Fin 2 → ZMod N) (τ : ℍ) : ℂ :=
  frickePrefactor (periodPairOfTau τ) *
    weierstrassP (periodPairOfTau τ) (frickeTorsionPt N a τ)

private def vecMulSL (N : ℕ) (a : Fin 2 → ZMod N) (γ : SL(2, ℤ)) : Fin 2 → ZMod N :=
  Matrix.vecMul a ((γ : Matrix (Fin 2) (Fin 2) ℤ).map ((↑) : ℤ → ZMod N))

private lemma vecMulSL_apply (N : ℕ) (a : Fin 2 → ZMod N) (γ : SL(2, ℤ)) (j : Fin 2) :
    vecMulSL N a γ j = a 0 * (γ 0 j : ℤ) + a 1 * (γ 1 j : ℤ) := by
  simp [vecMulSL, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.map_apply]

private theorem frickeFn_slash {N : ℕ} [NeZero N] (a : Fin 2 → ZMod N) (γ : SL(2, ℤ)) (τ : ℍ) :
    frickeFn N a (γ • τ) = frickeFn N (vecMulSL N a γ) τ := by
  have hd : denomZ γ (τ : ℂ) ≠ 0 := denomZ_ne_zero γ τ
  have hdi : (denomZ γ τ)⁻¹ ≠ 0 := inv_ne_zero hd
  unfold frickeFn
  have hlat := periodPairOfTau_smul_lattice_eq γ τ
  rw [frickePrefactor_of_lattice_eq hlat, weierstrassP_of_lattice_eq hlat,
      frickePrefactor_smulPeriodPair,
      show frickeTorsionPt N a (γ • τ)
        = (denomZ γ τ)⁻¹ * (denomZ γ τ * frickeTorsionPt N a (γ • τ)) by
          rw [inv_mul_cancel_left₀ hd],
      weierstrassP_smulPeriodPair, inv_inv]
  rw [show ((denomZ γ τ)⁻¹ ^ 2 * frickePrefactor (periodPairOfTau τ))
          * ((denomZ γ τ) ^ 2 * weierstrassP (periodPairOfTau τ)
              (denomZ γ τ * frickeTorsionPt N a (γ • τ)))
        = frickePrefactor (periodPairOfTau τ)
          * weierstrassP (periodPairOfTau τ) (denomZ γ τ * frickeTorsionPt N a (γ • τ)) by
      field_simp]
  congr 1
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)

  have hpt : denomZ γ τ * frickeTorsionPt N a (γ • τ)
      = ((((a 0).val : ℤ) * γ 0 0 + ((a 1).val : ℤ) * γ 1 0 : ℤ) * (τ : ℂ)
          + (((a 0).val : ℤ) * γ 0 1 + ((a 1).val : ℤ) * γ 1 1 : ℤ)) / (N : ℂ) := by
    have e : denomZ γ τ * frickeTorsionPt N a (γ • τ)
        = (((a 0).val : ℂ) * numZ γ τ + ((a 1).val : ℂ) * denomZ γ τ) / (N : ℂ) := by
      unfold frickeTorsionPt; rw [coe_SL2Z_smul]; field_simp
    rw [e, numZ, denomZ]; push_cast; ring
  rw [hpt]
  refine weierstrassP_torsionPt_lift_irrel (vecMulSL N a γ) τ _ _ ?_ ?_
  · rw [vecMulSL_apply]; push_cast; simp only [ZMod.natCast_val, ZMod.cast_id]
  · rw [vecMulSL_apply]; push_cast; simp only [ZMod.natCast_val, ZMod.cast_id]

private theorem weierstrassP_frickeTorsionPt_slash {N : ℕ} [NeZero N] (a : Fin 2 → ZMod N)
    (γ : SL(2, ℤ)) (τ : ℍ) :
    weierstrassP (periodPairOfTau (γ • τ)) (frickeTorsionPt N a (γ • τ))
      = (denomZ γ τ) ^ 2 *
          weierstrassP (periodPairOfTau τ) (frickeTorsionPt N (vecMulSL N a γ) τ) := by
  have hd := denomZ_ne_zero γ τ
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hlat := periodPairOfTau_smul_lattice_eq γ τ
  rw [weierstrassP_of_lattice_eq hlat,
      show frickeTorsionPt N a (γ • τ)
        = (denomZ γ τ)⁻¹ * (denomZ γ τ * frickeTorsionPt N a (γ • τ)) by
          rw [inv_mul_cancel_left₀ hd],
      weierstrassP_smulPeriodPair, inv_inv]
  congr 1
  have hpt : denomZ γ τ * frickeTorsionPt N a (γ • τ)
      = ((((a 0).val : ℤ) * γ 0 0 + ((a 1).val : ℤ) * γ 1 0 : ℤ) * (τ : ℂ)
          + (((a 0).val : ℤ) * γ 0 1 + ((a 1).val : ℤ) * γ 1 1 : ℤ)) / (N : ℂ) := by
    have e : denomZ γ τ * frickeTorsionPt N a (γ • τ)
        = (((a 0).val : ℂ) * numZ γ τ + ((a 1).val : ℂ) * denomZ γ τ) / (N : ℂ) := by
      unfold frickeTorsionPt; rw [coe_SL2Z_smul]; field_simp
    rw [e, numZ, denomZ]; push_cast; ring
  rw [hpt]
  refine weierstrassP_torsionPt_lift_irrel (vecMulSL N a γ) τ _ _ ?_ ?_
  · rw [vecMulSL_apply]; push_cast; simp only [ZMod.natCast_val, ZMod.cast_id]
  · rw [vecMulSL_apply]; push_cast; simp only [ZMod.natCast_val, ZMod.cast_id]

private lemma vecMulSL_of_mem_Gamma {N : ℕ} (a : Fin 2 → ZMod N) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma N) : vecMulSL N a γ = a := by
  obtain ⟨h₀₀, h₀₁, h₁₀, h₁₁⟩ := CongruenceSubgroup.Gamma_mem.mp hγ
  funext j
  fin_cases j <;> simp [vecMulSL_apply, h₀₀, h₀₁, h₁₀, h₁₁]

private theorem frickeFn_invariant_Gamma {N : ℕ} [NeZero N] (a : Fin 2 → ZMod N)
    {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma N) (τ : ℍ) :
    frickeFn N a (γ • τ) = frickeFn N a τ := by
  rw [frickeFn_slash, vecMulSL_of_mem_Gamma a hγ]

private lemma weierstrassP_frickeTorsionPt_neg {N : ℕ} [NeZero N] (a : Fin 2 → ZMod N) (τ : ℍ) :
    weierstrassP (periodPairOfTau τ) (frickeTorsionPt N (-a) τ)
      = weierstrassP (periodPairOfTau τ) (frickeTorsionPt N a τ) := by
  have h := weierstrassP_torsionPt_lift_irrel (N := N) (-a) τ
      (-((a 0).val : ℤ)) (-((a 1).val : ℤ))
      (by push_cast; simp [ZMod.natCast_val, ZMod.cast_id])
      (by push_cast; simp [ZMod.natCast_val, ZMod.cast_id])
  rw [← h, ← (periodPairOfTau τ).weierstrassP_neg]
  congr 1
  unfold frickeTorsionPt
  push_cast
  ring

private theorem frickeFn_neg {N : ℕ} [NeZero N] (a : Fin 2 → ZMod N) (τ : ℍ) :
    frickeFn N (-a) τ = frickeFn N a τ := by
  unfold frickeFn; rw [weierstrassP_frickeTorsionPt_neg]

end B3_fricke_tier2

section B3_spelling2

open scoped UpperHalfPlane Manifold MatrixGroups
open UpperHalfPlane hiding I
open Matrix.SpecialLinearGroup

private lemma denom_mapGL_eq_denomZ (γ : SL(2, ℤ)) (τ : ℍ) :
    denom (mapGL ℝ γ) τ = denomZ γ τ := by
  simp [denom, denomZ]

private def wpNormZ (N : ℕ) (a : Fin 2 → ZMod N) (τ : ℍ) : ℂ := wpNorm N (a 0).val (a 1).val τ

private lemma wpNormZ_eq (N : ℕ) (a : Fin 2 → ZMod N) (τ : ℍ) :
    wpNormZ N a τ = ((2 * π * I) ^ 2)⁻¹ *
      PeriodPair.weierstrassP (periodPairOfTau τ) (frickeTorsionPt N a τ) := by
  with_unfolding_all rfl

private theorem wpNormZ_slash {N : ℕ} [NeZero N] (a : Fin 2 → ZMod N) (γ : SL(2, ℤ)) (τ : ℍ) :
    wpNormZ N a (γ • τ) = denomZ γ τ ^ 2 * wpNormZ N (vecMulSL N a γ) τ := by
  rw [wpNormZ_eq, wpNormZ_eq, weierstrassP_frickeTorsionPt_slash]
  ring

private def frickeF (N : ℕ) (a : Fin 2 → ZMod N) (τ : ℍ) : ℂ :=
  -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * wpNormZ N a τ

private theorem frickeF_slash {N : ℕ} [NeZero N] (a : Fin 2 → ZMod N) (γ : SL(2, ℤ)) (τ : ℍ) :
    frickeF N a (γ • τ) = frickeF N (vecMulSL N a γ) τ := by
  have hγ : (mapGL ℝ γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  have h4 := SlashInvariantForm.slash_action_eqn'' ModularForm.E₄ hγ τ
  have h6 := SlashInvariantForm.slash_action_eqn'' ModularForm.E₆ hγ τ
  have hΔ := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hγ τ
  rw [CuspForm.coe_discriminant] at hΔ
  rw [show (mapGL ℝ γ) • τ = γ • τ from rfl, denom_mapGL_eq_denomZ] at h4 h6 hΔ
  have hd : denomZ γ τ ≠ 0 := denomZ_ne_zero γ τ
  have hΔ0 : ModularForm.discriminant τ ≠ 0 := ModularForm.discriminant_ne_zero τ
  unfold frickeF
  rw [h4, h6, hΔ, wpNormZ_slash, zpow_ofNat, zpow_ofNat, zpow_ofNat]
  field_simp

private theorem frickeF_invariant_Gamma {N : ℕ} [NeZero N] (a : Fin 2 → ZMod N) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma N) (τ : ℍ) : frickeF N a (γ • τ) = frickeF N a τ := by
  rw [frickeF_slash, vecMulSL_of_mem_Gamma a hγ]

private lemma vecMulSL_mul (N : ℕ) (a : Fin 2 → ZMod N) (γ δ : SL(2, ℤ)) :
    vecMulSL N a (γ * δ) = vecMulSL N (vecMulSL N a γ) δ := by
  have hmap : ((γ * δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map ((↑) : ℤ → ZMod N) =
      (γ : Matrix (Fin 2) (Fin 2) ℤ).map ((↑) : ℤ → ZMod N) *
        (δ : Matrix (Fin 2) (Fin 2) ℤ).map ((↑) : ℤ → ZMod N) := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    exact Matrix.map_mul (f := Int.castRingHom (ZMod N))
  simp only [vecMulSL, hmap, Matrix.vecMul_vecMul]

private lemma vecMulSL_one (N : ℕ) (a : Fin 2 → ZMod N) : vecMulSL N a 1 = a := by
  simp [vecMulSL]

private def vecMulSLEquiv (N : ℕ) (γ : SL(2, ℤ)) : Equiv.Perm (Fin 2 → ZMod N) where
  toFun a := vecMulSL N a γ
  invFun a := vecMulSL N a γ⁻¹
  left_inv a := by
    show vecMulSL N (vecMulSL N a γ) γ⁻¹ = a
    rw [← vecMulSL_mul, mul_inv_cancel, vecMulSL_one]
  right_inv a := by
    show vecMulSL N (vecMulSL N a γ⁻¹) γ = a
    rw [← vecMulSL_mul, inv_mul_cancel, vecMulSL_one]

private lemma vecMulSL_zero (N : ℕ) (γ : SL(2, ℤ)) : vecMulSL N 0 γ = 0 := by
  funext j; simp [vecMulSL_apply]

private lemma vecMulSL_ne_zero {N : ℕ} {a : Fin 2 → ZMod N} (ha : a ≠ 0) (γ : SL(2, ℤ)) :
    vecMulSL N a γ ≠ 0 := by
  intro h
  apply ha
  have := congrArg (fun b ↦ vecMulSL N b γ⁻¹) h
  simpa [← vecMulSL_mul, vecMulSL_one, vecMulSL_zero] using this

private abbrev FrickeIdx (N : ℕ) : Type := {a : Fin 2 → ZMod N // a ≠ 0}

private scoped instance (N : ℕ) [NeZero N] : Fintype (FrickeIdx N) := by unfold FrickeIdx; infer_instance

private def frickeIdxPerm (N : ℕ) (γ : SL(2, ℤ)) : Equiv.Perm (FrickeIdx N) :=
  (vecMulSLEquiv N γ).subtypeEquiv fun a ↦
    ⟨fun ha ↦ vecMulSL_ne_zero ha γ, fun h ha ↦ h (by rw [ha]; exact vecMulSL_zero N γ)⟩

private theorem frickeF_hperm {N : ℕ} [NeZero N] (γ : SL(2, ℤ)) :
    ∃ σ : Equiv.Perm (FrickeIdx N), ∀ (i : FrickeIdx N) (τ : ℍ),
      frickeF N i.1 (γ • τ) = frickeF N (σ i).1 τ :=
  ⟨frickeIdxPerm N γ, fun i τ ↦ frickeF_slash i.1 γ τ⟩

private lemma frickeIdx_hyps {N : ℕ} [NeZero N] (i : FrickeIdx N) :
    (i.1 0).val < N ∧ (i.1 1).val < N ∧ ((i.1 0).val ≠ 0 ∨ (i.1 1).val ≠ 0) := by
  refine ⟨ZMod.val_lt _, ZMod.val_lt _, ?_⟩
  by_contra h
  push Not at h
  apply i.2
  funext j
  fin_cases j
  · exact (ZMod.val_eq_zero _).mp h.1
  · exact (ZMod.val_eq_zero _).mp h.2

private theorem frickeF_mul_discriminant {N : ℕ} (a : Fin 2 → ZMod N) (τ : ℍ) :
    frickeF N a τ * CuspForm.discriminant τ = -(frickeH N (a 0).val (a 1).val τ) / 2592 := by
  rw [CuspForm.coe_discriminant]
  have hΔ0 : ModularForm.discriminant τ ≠ 0 := ModularForm.discriminant_ne_zero τ
  simp only [frickeF, frickeH, wpNormZ, Pi.mul_apply]
  field_simp

private theorem mdifferentiable_frickeF {N : ℕ} [NeZero N] (i : FrickeIdx N) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (frickeF N i.1) := by
  obtain ⟨h1, h2, h0⟩ := frickeIdx_hyps i
  have hW : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (wpNormZ N i.1) := mdifferentiable_wpNorm h1 h2 h0
  have hE : MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (fun τ ↦ ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) :=
    (ModularForm.E₄.holo'.mul ModularForm.E₆.holo').div CuspForm.discriminant.holo'
      ModularForm.discriminant_ne_zero
  have hc : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun _ : ℍ ↦ (-1 / 2592 : ℂ)) := mdifferentiable_const
  have heq : frickeF N i.1 = (fun _ : ℍ ↦ (-1 / 2592 : ℂ)) *
      (fun τ ↦ ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) *
        wpNormZ N i.1 := by
    funext τ
    simp only [frickeF, Pi.mul_apply]
    ring
  rw [heq]
  exact (hc.mul hE).mul hW

private theorem isBoundedAtImInfty_frickeF_mul_discriminant {N : ℕ} [NeZero N] (i : FrickeIdx N) :
    IsBoundedAtImInfty (frickeF N i.1 * ⇑CuspForm.discriminant) := by
  obtain ⟨h1, h2, h0⟩ := frickeIdx_hyps i
  have hH := isBoundedAtImInfty_frickeH h1 h2 h0
  have : (frickeF N i.1 * ⇑CuspForm.discriminant : ℍ → ℂ) =
      fun τ ↦ (-1 / 2592 : ℂ) * frickeH N (i.1 0).val (i.1 1).val τ := by
    funext τ
    rw [Pi.mul_apply, frickeF_mul_discriminant]
    ring
  rw [this]
  exact hH.const_mul_left _

private lemma qExpansion_E4E6_coeff_zero {N : ℕ} (hN : N ≠ 0) :
    (qExpansion N (⇑ModularForm.E₄ * ⇑ModularForm.E₆ : ℍ → ℂ)).coeff 0 = 1 := by
  have hper : Function.Periodic ((⇑ModularForm.E₄ * ⇑ModularForm.E₆ : ℍ → ℂ) ∘ ofComplex) 1 := by
    have h4 := SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄
      one_mem_strictPeriods_SL
    have h6 := SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₆
      one_mem_strictPeriods_SL
    intro τ
    have e4 := h4 τ
    have e6 := h6 τ
    simp only [Function.comp_apply, Pi.mul_apply, Complex.ofReal_one] at e4 e6 ⊢
    rw [e4, e6]
  rw [qExpansion_coeff_width _ hN hper (ModularForm.E₄.holo'.mul ModularForm.E₆.holo')
    ((ModularFormClass.bdd_at_infty ModularForm.E₄).mul
      (ModularFormClass.bdd_at_infty ModularForm.E₆)) 0,
    ite_eq_left (dvd_zero N), Nat.zero_div,
    ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_SL,
    PowerSeries.coeff_zero_eq_constantCoeff, map_mul, ← PowerSeries.coeff_zero_eq_constantCoeff,
    EisensteinSeries.E_qExpansion_coeff_zero (by norm_num) (by decide),
    EisensteinSeries.E_qExpansion_coeff_zero (by norm_num) (by decide), mul_one]

private lemma qExpansion_wpNorm_eq_of_frickeH_eq {N a₁ a₂ b₁ b₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (ha0 : a₁ ≠ 0 ∨ a₂ ≠ 0) (hb₁ : b₁ < N) (hb₂ : b₂ < N) (hb0 : b₁ ≠ 0 ∨ b₂ ≠ 0)
    (h : frickeH N a₁ a₂ = frickeH N b₁ b₂) :
    qExpansion N (wpNorm N a₁ a₂) = qExpansion N (wpNorm N b₁ b₂) := by
  have hN : N ≠ 0 := by omega
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hperE : Function.Periodic ((⇑ModularForm.E₄ * ⇑ModularForm.E₆ : ℍ → ℂ) ∘ ofComplex) N := by
    have h4 := (SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄
      one_mem_strictPeriods_SL).nat_mul N
    have h6 := (SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₆
      one_mem_strictPeriods_SL).nat_mul N
    intro τ
    have e4 := h4 τ; have e6 := h6 τ
    simp only [Complex.ofReal_one, mul_one, Function.comp_apply] at e4 e6
    simp only [Function.comp_apply, Pi.mul_apply, e4, e6]
  have hE : AnalyticAt ℂ (cuspFunction N (⇑ModularForm.E₄ * ⇑ModularForm.E₆ : ℍ → ℂ)) 0 :=
    analyticAt_cuspFunction_zero hN' hperE (ModularForm.E₄.holo'.mul ModularForm.E₆.holo')
      ((ModularFormClass.bdd_at_infty ModularForm.E₄).mul
        (ModularFormClass.bdd_at_infty ModularForm.E₆))
  have hWa : AnalyticAt ℂ (cuspFunction N (wpNorm N a₁ a₂)) 0 :=
    analyticAt_cuspFunction_zero hN' (periodic_wpNorm ha₁ ha₂ ha0)
      (mdifferentiable_wpNorm ha₁ ha₂ ha0) (isBoundedAtImInfty_wpNorm ha₁ ha₂ ha0)
  have hWb : AnalyticAt ℂ (cuspFunction N (wpNorm N b₁ b₂)) 0 :=
    analyticAt_cuspFunction_zero hN' (periodic_wpNorm hb₁ hb₂ hb0)
      (mdifferentiable_wpNorm hb₁ hb₂ hb0) (isBoundedAtImInfty_wpNorm hb₁ hb₂ hb0)
  have hq := congrArg (qExpansion (N : ℝ)) h
  rw [frickeH, frickeH, qExpansion_mul hE hWa, qExpansion_mul hE hWb] at hq
  have hne : qExpansion N (⇑ModularForm.E₄ * ⇑ModularForm.E₆ : ℍ → ℂ) ≠ 0 := by
    intro h0
    have := qExpansion_E4E6_coeff_zero hN
    rw [h0, map_zero] at this
    exact zero_ne_one this
  exact mul_left_cancel₀ hne hq

private lemma qExpansion_E4E6_rat {N : ℕ} (hN : N ≠ 0) (n : ℕ) :
    ∃ q : ℚ, (qExpansion N (⇑ModularForm.E₄ * ⇑ModularForm.E₆ : ℍ → ℂ)).coeff n = (q : ℂ) := by
  have hper : Function.Periodic ((⇑ModularForm.E₄ * ⇑ModularForm.E₆ : ℍ → ℂ) ∘ ofComplex) 1 := by
    have h4 := SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄
      one_mem_strictPeriods_SL
    have h6 := SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₆
      one_mem_strictPeriods_SL
    intro τ
    have e4 := h4 τ
    have e6 := h6 τ
    simp only [Function.comp_apply, Pi.mul_apply, Complex.ofReal_one] at e4 e6 ⊢
    rw [e4, e6]
  rw [qExpansion_coeff_width _ hN hper (ModularForm.E₄.holo'.mul ModularForm.E₆.holo')
    ((ModularFormClass.bdd_at_infty ModularForm.E₄).mul
      (ModularFormClass.bdd_at_infty ModularForm.E₆)) n]
  by_cases hdvd : N ∣ n
  · rw [ite_eq_left hdvd, ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_SL,
      PowerSeries.coeff_mul]
    refine ⟨∑ p ∈ Finset.HasAntidiagonal.antidiagonal (n / N),
      (qExpansion_one_E4_rat p.1).choose * (qExpansion_one_E6_rat p.2).choose, ?_⟩
    push_cast
    exact Finset.sum_congr rfl fun p _ =>
      congrArg₂ (· * ·) (qExpansion_one_E4_rat p.1).choose_spec
        (qExpansion_one_E6_rat p.2).choose_spec
  · exact ⟨0, by rw [ite_eq_right hdvd]; norm_num⟩

private theorem qExpansion_frickeH_coeff_mem_kN {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) (n : ℕ) :
    (qExpansion N (frickeH N a₁ a₂)).coeff n ∈ kN N := by
  have hN : N ≠ 0 := by omega
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hperE : Function.Periodic ((⇑ModularForm.E₄ * ⇑ModularForm.E₆ : ℍ → ℂ) ∘ ofComplex) N := by
    have h4 := (SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄
      one_mem_strictPeriods_SL).nat_mul N
    have h6 := (SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₆
      one_mem_strictPeriods_SL).nat_mul N
    intro τ
    have e4 := h4 τ
    have e6 := h6 τ
    simp only [Complex.ofReal_one, mul_one, Function.comp_apply] at e4 e6
    simp only [Function.comp_apply, Pi.mul_apply, e4, e6]
  have hE : AnalyticAt ℂ (cuspFunction N (⇑ModularForm.E₄ * ⇑ModularForm.E₆ : ℍ → ℂ)) 0 :=
    analyticAt_cuspFunction_zero hN' hperE (ModularForm.E₄.holo'.mul ModularForm.E₆.holo')
      ((ModularFormClass.bdd_at_infty ModularForm.E₄).mul
        (ModularFormClass.bdd_at_infty ModularForm.E₆))
  have hW : AnalyticAt ℂ (cuspFunction N (wpNorm N a₁ a₂)) 0 :=
    analyticAt_cuspFunction_zero hN' (periodic_wpNorm ha₁ ha₂ h0)
      (mdifferentiable_wpNorm ha₁ ha₂ h0) (isBoundedAtImInfty_wpNorm ha₁ ha₂ h0)
  rw [frickeH, qExpansion_mul hE hW, PowerSeries.coeff_mul]
  refine sum_mem fun ij _ ↦ mul_mem ?_ (qExpansion_wpNorm_coeff_mem_kN ha₁ ha₂ h0 _)
  obtain ⟨q, hq⟩ := qExpansion_E4E6_rat hN ij.1
  rw [hq, ← SubfieldClass.coe_ratCast (kN N) q]
  exact SetLike.coe_mem _

private lemma qExpansion_frickeH_conj {N : ℕ} [NeZero N] {s : ℕ} (hs : s.Coprime N)
    (φ : ↑(kN N) →+* ℂ) (hφ : φ ⟨zetaN N, zetaN_mem_kN N⟩ = zetaN N ^ s)
    {a₁ a₂ : ℕ} (h1 : a₁ < N) (h2 : a₂ < N) (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) (n : ℕ)
    (z : ↑(kN N)) (hz : (z : ℂ) = (qExpansion N (frickeH N a₁ a₂)).coeff n) :
    (qExpansion N (frickeH N a₁ (s * a₂ % N))).coeff n = φ z := by
  have hN : N ≠ 0 := NeZero.ne N
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have h2' : s * a₂ % N < N := Nat.mod_lt _ (Nat.pos_of_ne_zero hN)
  have h0' : a₁ ≠ 0 ∨ s * a₂ % N ≠ 0 := by
    rcases h0 with h | h
    · exact Or.inl h
    · refine Or.inr fun hmod => h ?_
      have hdvd0 : N ∣ s * a₂ := Nat.dvd_of_mod_eq_zero hmod
      have hdvd : N ∣ a₂ := Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm hs) hdvd0
      exact Nat.eq_zero_of_dvd_of_lt hdvd h2
  obtain ⟨S, hSmap, hSconj⟩ := wpNorm_qExpansion_model hN
  have hESm := qExpansion_E4E6_rat hN
  have hESmap : (PowerSeries.mk fun m => (((hESm m).choose : ℚ) : ↑(kN N))).map
      (algebraMap ↑(kN N) ℂ) = qExpansion N (⇑ModularForm.E₄ * ⇑ModularForm.E₆ : ℍ → ℂ) := by
    ext m
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, map_ratCast]
    exact ((hESm m).choose_spec).symm
  have hESφ : (PowerSeries.mk fun m => (((hESm m).choose : ℚ) : ↑(kN N))).map φ =
      qExpansion N (⇑ModularForm.E₄ * ⇑ModularForm.E₆ : ℍ → ℂ) := by
    ext m
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, map_ratCast]
    exact ((hESm m).choose_spec).symm
  have hperE : Function.Periodic ((⇑ModularForm.E₄ * ⇑ModularForm.E₆ : ℍ → ℂ) ∘ ofComplex) N := by
    have h4 := (SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄
      one_mem_strictPeriods_SL).nat_mul N
    have h6 := (SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₆
      one_mem_strictPeriods_SL).nat_mul N
    intro τ
    have e4 := h4 τ
    have e6 := h6 τ
    simp only [Complex.ofReal_one, mul_one, Function.comp_apply] at e4 e6
    simp only [Function.comp_apply, Pi.mul_apply, e4, e6]
  have hE : AnalyticAt ℂ (cuspFunction N (⇑ModularForm.E₄ * ⇑ModularForm.E₆ : ℍ → ℂ)) 0 :=
    analyticAt_cuspFunction_zero hN' hperE (ModularForm.E₄.holo'.mul ModularForm.E₆.holo')
      ((ModularFormClass.bdd_at_infty ModularForm.E₄).mul
        (ModularFormClass.bdd_at_infty ModularForm.E₆))
  have hWa : AnalyticAt ℂ (cuspFunction N (wpNorm N a₁ a₂)) 0 :=
    analyticAt_cuspFunction_zero hN' (periodic_wpNorm h1 h2 h0)
      (mdifferentiable_wpNorm h1 h2 h0) (isBoundedAtImInfty_wpNorm h1 h2 h0)
  have hWa' : AnalyticAt ℂ (cuspFunction N (wpNorm N a₁ (s * a₂ % N))) 0 :=
    analyticAt_cuspFunction_zero hN' (periodic_wpNorm h1 h2' h0')
      (mdifferentiable_wpNorm h1 h2' h0') (isBoundedAtImInfty_wpNorm h1 h2' h0')
  have hHa : qExpansion N (frickeH N a₁ a₂) =
      ((PowerSeries.mk fun m => (((hESm m).choose : ℚ) : ↑(kN N))) * S a₁ a₂).map
        (algebraMap ↑(kN N) ℂ) := by
    rw [frickeH, qExpansion_mul hE hWa, map_mul, hESmap, hSmap a₁ a₂ h1 h2 h0]
  have hHa' : qExpansion N (frickeH N a₁ (s * a₂ % N)) =
      ((PowerSeries.mk fun m => (((hESm m).choose : ℚ) : ↑(kN N))) * S a₁ a₂).map φ := by
    rw [frickeH, qExpansion_mul hE hWa', map_mul, hESφ, hSconj s hs φ hφ a₁ a₂ h1 h2 h0]
  have hz2 : z = ((PowerSeries.mk fun m => (((hESm m).choose : ℚ) : ↑(kN N))) * S a₁ a₂).coeff n := by
    have hinj : Function.Injective (algebraMap ↑(kN N) ℂ) := (algebraMap ↑(kN N) ℂ).injective
    apply hinj
    rw [← PowerSeries.coeff_map, ← hHa]
    exact_mod_cast hz
  rw [hHa', PowerSeries.coeff_map, ← hz2]

private theorem frickeF_eq_imp {N : ℕ} [NeZero N] (a b : FrickeIdx N)
    (h : frickeF N a.1 = frickeF N b.1) : b.1 = a.1 ∨ b.1 = -a.1 := by
  obtain ⟨ha₁, ha₂, ha0⟩ := frickeIdx_hyps a
  obtain ⟨hb₁, hb₂, hb0⟩ := frickeIdx_hyps b
  have hH : frickeH N (a.1 0).val (a.1 1).val = frickeH N (b.1 0).val (b.1 1).val := by
    funext τ
    have e := congrFun h τ
    have ea := frickeF_mul_discriminant a.1 τ
    have eb := frickeF_mul_discriminant b.1 τ
    rw [e] at ea
    rw [ea] at eb
    linear_combination (-2592) * eb
  have hq := qExpansion_wpNorm_eq_of_frickeH_eq ha₁ ha₂ ha0 hb₁ hb₂ hb0 hH

  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hfun : wpNorm N (a.1 0).val (a.1 1).val = wpNorm N (b.1 0).val (b.1 1).val := by
    funext τ
    have hsa := hasSum_qExpansion hNpos (periodic_wpNorm ha₁ ha₂ ha0)
      (mdifferentiable_wpNorm ha₁ ha₂ ha0) (isBoundedAtImInfty_wpNorm ha₁ ha₂ ha0) τ
    have hsb := hasSum_qExpansion hNpos (periodic_wpNorm hb₁ hb₂ hb0)
      (mdifferentiable_wpNorm hb₁ hb₂ hb0) (isBoundedAtImInfty_wpNorm hb₁ hb₂ hb0) τ
    rw [← hq] at hsb
    exact hsa.unique hsb
  rcases wpNorm_eq_imp ha₁ ha₂ ha0 hb₁ hb₂ hb0 hfun with ⟨e0, e1⟩ | ⟨e0, e1⟩
  · left
    have f0 : b.1 0 = a.1 0 := ZMod.val_injective N e0
    have f1 : b.1 1 = a.1 1 := ZMod.val_injective N e1
    funext j
    fin_cases j <;> simp [f0, f1]
  · right
    have f0 : b.1 0 = -a.1 0 := ZMod.val_injective N (by rw [e0, ZMod.neg_val'])
    have f1 : b.1 1 = -a.1 1 := ZMod.val_injective N (by rw [e1, ZMod.neg_val'])
    funext j
    fin_cases j <;> simp [f0, f1]

private theorem mem_Gamma_or_neg_mem_of_vecMulSL {N : ℕ} [NeZero N] (γ : SL(2, ℤ))
    (h : ∀ a : Fin 2 → ZMod N, a ≠ 0 → vecMulSL N a γ = a ∨ vecMulSL N a γ = -a) :
    γ ∈ CongruenceSubgroup.Gamma N ∨ -γ ∈ CongruenceSubgroup.Gamma N := by
  rcases Nat.lt_or_ge 1 N with hN | hN
  · have : Fact (1 < N) := ⟨hN⟩
    have h10 : (1 : ZMod N) ≠ 0 := one_ne_zero
    have r1 := h ![1, 0] (fun e ↦ h10 (by simpa using congrFun e 0))
    have r2 := h ![0, 1] (fun e ↦ h10 (by simpa using congrFun e 1))
    have r3 := h ![1, 1] (fun e ↦ h10 (by simpa using congrFun e 0))
    simp only [funext_iff, Fin.forall_fin_two, vecMulSL_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul, zero_mul, add_zero, zero_add,
      Pi.neg_apply, neg_zero] at r1 r2 r3
    have e01 : ((γ 0 1 : ℤ) : ZMod N) = 0 := by rcases r1 with ⟨_, e⟩ | ⟨_, e⟩ <;> exact e
    have e10 : ((γ 1 0 : ℤ) : ZMod N) = 0 := by rcases r2 with ⟨e, _⟩ | ⟨e, _⟩ <;> exact e
    have e0011 : ((γ 0 0 : ℤ) : ZMod N) = ((γ 1 1 : ℤ) : ZMod N) := by
      rcases r3 with ⟨c1, c2⟩ | ⟨c1, c2⟩ <;>
        (rw [e10, add_zero] at c1; rw [e01, zero_add] at c2; rw [c1, c2])
    rw [CongruenceSubgroup.Gamma_mem, CongruenceSubgroup.Gamma_mem]
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg, neg_eq_zero]
    rcases r1 with ⟨a1, _⟩ | ⟨a1, _⟩
    · left; exact ⟨a1, e01, e10, by rw [← e0011]; exact a1⟩
    · right; exact ⟨by rw [a1, neg_neg], e01, e10, by rw [← e0011, a1, neg_neg]⟩
  · have : N = 1 := by have := NeZero.ne N; omega
    subst this
    left
    simp [CongruenceSubgroup.Gamma_one_top]

private theorem frickeF_faithful {N : ℕ} [NeZero N] (γ : SL(2, ℤ))
    (h : ∀ i : FrickeIdx N, ∀ τ : ℍ, frickeF N i.1 (γ • τ) = frickeF N i.1 τ) :
    γ ∈ CongruenceSubgroup.Gamma N ∨ -γ ∈ CongruenceSubgroup.Gamma N := by
  refine mem_Gamma_or_neg_mem_of_vecMulSL γ fun a ha ↦ ?_
  have hfun : frickeF N a = frickeF N (vecMulSL N a γ) := by
    funext τ; rw [← frickeF_slash, h ⟨a, ha⟩ τ]
  rcases frickeF_eq_imp ⟨a, ha⟩ ⟨vecMulSL N a γ, vecMulSL_ne_zero ha γ⟩ hfun with e | e
  · exact Or.inl e
  · exact Or.inr e

end B3_spelling2

section R4aBridge

open WLight
open UpperHalfPlane hiding I
open scoped Manifold MatrixGroups ModularForm

private lemma periodPair_ext' {L₁ L₂ : PeriodPair} (h₁ : L₁.ω₁ = L₂.ω₁)
    (h₂ : L₁.ω₂ = L₂.ω₂) : L₁ = L₂ := by
  cases L₁; cases L₂; simp_all

end R4aBridge

open UpperHalfPlane hiding I in
open scoped UpperHalfPlane Manifold MatrixGroups ModularForm in
open WLight in
theorem _root_.WLight.frickeFunction_modularity_package (N : ℕ) [NeZero N]
    (L : ℍ → PeriodPair) (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1) :
    let f : (Fin 2 → ZMod N) → ℍ → ℂ := fun a τ =>
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 *
        (((2 * π * I) ^ 2)⁻¹ *
          PeriodPair.weierstrassP (L τ)
            ((((a 0).val : ℂ) * (τ : ℂ) + ((a 1).val : ℂ)) / (N : ℂ)))

    (∀ (a : Fin 2 → ZMod N) (γ : SL(2, ℤ)) (τ : ℍ), f a (γ • τ) =
        f (Matrix.vecMul a ((γ : Matrix (Fin 2) (Fin 2) ℤ).map ((↑) : ℤ → ZMod N))) τ) ∧

    (∀ a : Fin 2 → ZMod N, f (-a) = f a) ∧

    (∀ a : Fin 2 → ZMod N, a ≠ 0 → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f a)) ∧

    (∀ a : Fin 2 → ZMod N, a ≠ 0 →
      IsBoundedAtImInfty (f a * ModularForm.discriminant)) ∧

    (∀ a : Fin 2 → ZMod N, a ≠ 0 →
      Function.Periodic ((f a * ModularForm.discriminant) ∘ ofComplex) N ∧
      ∀ n : ℕ, (qExpansion N (f a * ModularForm.discriminant)).coeff n ∈
        IntermediateField.adjoin ℚ {cexp (2 * π * I / N)}) ∧

    (∀ a b : Fin 2 → ZMod N, a ≠ 0 → b ≠ 0 → f a = f b → b = a ∨ b = -a) ∧

    (∀ a : Fin 2 → ZMod N, ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ,
      f a (γ • τ) = f a τ) ∧

    (∀ s : ℕ, s.Coprime N →
      ∀ φ : ↑(IntermediateField.adjoin ℚ {cexp (2 * π * I / N)}) →+* ℂ,
        (∀ z : ↑(IntermediateField.adjoin ℚ {cexp (2 * π * I / N)}),
            (z : ℂ) = cexp (2 * π * I / N) → φ z = cexp (2 * π * I / N) ^ s) →
        ∀ a : Fin 2 → ZMod N, a ≠ 0 →
          ∀ (n : ℕ) (z : ↑(IntermediateField.adjoin ℚ {cexp (2 * π * I / N)})),
            (z : ℂ) = (qExpansion N (f a * ModularForm.discriminant)).coeff n →
            (qExpansion N (f ![a 0, (s : ZMod N) * a 1] * ModularForm.discriminant)).coeff n = φ z) := by
  intro f
  have hLpp : ∀ τ : ℍ, L τ = periodPairOfTau τ := fun τ =>
    periodPair_ext' ((hL τ).1.trans (periodPairOfTau_ω₁ τ).symm)
      ((hL τ).2.trans (periodPairOfTau_ω₂ τ).symm)
  have hfeq : ∀ (a : Fin 2 → ZMod N) (τ : ℍ), f a τ = frickeF N a τ := by
    intro a τ
    show -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 *
      (((2 * ↑Real.pi * Complex.I) ^ 2)⁻¹ *
        PeriodPair.weierstrassP (L τ) _) = _
    rw [hLpp τ]
    with_unfolding_all rfl
  have hfeq' : ∀ a : Fin 2 → ZMod N, f a = frickeF N a := fun a => funext (hfeq a)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro a γ τ
    rw [hfeq, hfeq]
    exact frickeF_slash a γ τ
  ·
    intro a
    funext τ
    rw [hfeq, hfeq]
    show frickeF N (-a) τ = frickeF N a τ
    simp only [frickeF]
    congr 1
    rw [wpNormZ_eq, wpNormZ_eq, weierstrassP_frickeTorsionPt_neg]
  ·
    intro a ha
    rw [hfeq' a]
    exact mdifferentiable_frickeF ⟨a, ha⟩
  ·
    intro a ha
    have hb := isBoundedAtImInfty_frickeF_mul_discriminant (⟨a, ha⟩ : FrickeIdx N)
    have hsh : (f a * ModularForm.discriminant : ℍ → ℂ) =
        frickeF N a * ⇑CuspForm.discriminant := by
      funext τ
      simp only [Pi.mul_apply, hfeq a τ]
      rw [show ModularForm.discriminant τ = (⇑CuspForm.discriminant) τ from
        (congrFun CuspForm.coe_discriminant τ).symm]
    rw [hsh]
    exact hb
  ·
    intro a ha
    obtain ⟨h1, h2, h0⟩ := frickeIdx_hyps (⟨a, ha⟩ : FrickeIdx N)
    have hshape : (f a * ModularForm.discriminant : ℍ → ℂ) =
        (-(1 / 2592) : ℂ) • frickeH N (a 0).val (a 1).val := by
      funext τ
      simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, hfeq a τ]
      rw [show ModularForm.discriminant τ = (⇑CuspForm.discriminant) τ from
        (congrFun CuspForm.coe_discriminant τ).symm, frickeF_mul_discriminant]
      ring
    constructor
    · rw [hshape]
      intro x
      have hx := periodic_frickeH h1 h2 h0 x
      simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul] at hx ⊢
      rw [hx]
    · intro n
      rw [hshape, qExpansion_smul (analyticAt_cuspFunction_zero_of
          (mdifferentiable_frickeH h1 h2 h0) (periodic_frickeH h1 h2 h0)
          (isBoundedAtImInfty_frickeH h1 h2 h0)), PowerSeries.coeff_smul, smul_eq_mul]
      refine mul_mem ?_ (qExpansion_frickeH_coeff_mem_kN h1 h2 h0 n)
      show ((-(1 / 2592) : ℂ)) ∈ IntermediateField.adjoin ℚ {Complex.exp (2 * ↑Real.pi * Complex.I / N)}
      simp
  ·
    intro a b ha hb hab
    exact frickeF_eq_imp ⟨a, ha⟩ ⟨b, hb⟩ (by rw [← hfeq' a, ← hfeq' b]; exact hab)
  ·
    intro a γ hγ τ
    rw [hfeq, hfeq]
    exact frickeF_invariant_Gamma a hγ τ
  ·
    intro s hs φ hφ a ha n z hz
    obtain ⟨h1, h2, h0⟩ := frickeIdx_hyps (⟨a, ha⟩ : FrickeIdx N)
    have hN : N ≠ 0 := NeZero.ne N
    have h2' : s * (a 1).val % N < N := Nat.mod_lt _ (Nat.pos_of_ne_zero hN)
    have h0' : (a 0).val ≠ 0 ∨ s * (a 1).val % N ≠ 0 := by
      rcases h0 with h | h
      · exact Or.inl h
      · refine Or.inr fun hmod => h ?_
        have hdvd0 : N ∣ s * (a 1).val := Nat.dvd_of_mod_eq_zero hmod
        have hdvd : N ∣ (a 1).val :=
          Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm hs) hdvd0
        exact Nat.eq_zero_of_dvd_of_lt hdvd h2
    have hsu : IsUnit ((s : ZMod N)) := (ZMod.isUnit_iff_coprime s N).mpr hs
    have ha' : (![a 0, (s : ZMod N) * a 1] : Fin 2 → ZMod N) ≠ 0 := by
      intro h00
      apply ha
      have e0 : a 0 = 0 := by simpa using congrFun h00 0
      have e1 : (s : ZMod N) * a 1 = 0 := by simpa using congrFun h00 1
      have e1' : a 1 = 0 := (hsu.mul_right_eq_zero).mp e1
      funext j
      fin_cases j <;> simp [e0, e1']
    have hval : ((s : ZMod N) * a 1).val = s * (a 1).val % N := by
      rw [ZMod.val_mul, ZMod.val_natCast]
      exact Nat.mod_mul_mod s (a 1).val N
    have hφg : φ ⟨zetaN N, zetaN_mem_kN N⟩ = zetaN N ^ s :=
      hφ ⟨zetaN N, zetaN_mem_kN N⟩ rfl
    have hshA : (f a * ModularForm.discriminant : ℍ → ℂ) =
        (-(1 / 2592) : ℂ) • frickeH N (a 0).val (a 1).val := by
      funext τ
      simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, hfeq a τ]
      rw [show ModularForm.discriminant τ = (⇑CuspForm.discriminant) τ from
        (congrFun CuspForm.coe_discriminant τ).symm, frickeF_mul_discriminant]
      ring
    have hshA' : (f ![a 0, (s : ZMod N) * a 1] * ModularForm.discriminant : ℍ → ℂ) =
        (-(1 / 2592) : ℂ) • frickeH N (a 0).val (s * (a 1).val % N) := by
      funext τ
      simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, hfeq (![a 0, (s : ZMod N) * a 1]) τ]
      rw [show ModularForm.discriminant τ = (⇑CuspForm.discriminant) τ from
        (congrFun CuspForm.coe_discriminant τ).symm, frickeF_mul_discriminant]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hval]
      ring
    have hanA := analyticAt_cuspFunction_zero_of (mdifferentiable_frickeH h1 h2 h0)
      (periodic_frickeH h1 h2 h0) (isBoundedAtImInfty_frickeH h1 h2 h0)
    have hanA' := analyticAt_cuspFunction_zero_of (mdifferentiable_frickeH h1 h2' h0')
      (periodic_frickeH h1 h2' h0') (isBoundedAtImInfty_frickeH h1 h2' h0')
    rw [hshA, qExpansion_smul hanA, PowerSeries.coeff_smul, smul_eq_mul] at hz
    rw [hshA', qExpansion_smul hanA', PowerSeries.coeff_smul, smul_eq_mul]
    have hmem := qExpansion_frickeH_coeff_mem_kN h1 h2 h0 n
    have htr := qExpansion_frickeH_conj hs φ hφg h1 h2 h0 n
      (⟨_, hmem⟩ : ↑(IntermediateField.adjoin ℚ {cexp (2 * π * I / N)})) rfl
    have hzrel : z = ((-(1/2592) : ℚ) : ↑(IntermediateField.adjoin ℚ {cexp (2 * π * I / N)})) *
        ⟨_, hmem⟩ := by
      apply Subtype.coe_injective
      show (z : ℂ) = ((-(1/2592) : ℚ) : ℂ) *
        (qExpansion N (frickeH N (a 0).val (a 1).val)).coeff n
      rw [hz]
      push_cast
      ring
    have hφz : φ z = ((-(1/2592) : ℚ) : ℂ) * φ ⟨_, hmem⟩ := by
      rw [hzrel, map_mul, map_ratCast]
    rw [htr, hφz]
    push_cast
    rfl

end WLightFriMod

namespace WLightFriOrbit

section R4bFloor
open scoped UpperHalfPlane Manifold MatrixGroups
open UpperHalfPlane hiding I
open ModularForm ModularFormClass CuspForm ModularForm.CuspForm Polynomial Real.Polynomial Filter
open scoped ModularForm ModularFormClass CuspForm ModularForm.CuspForm Polynomial Real.Polynomial Filter
variable {N : ℕ}

private def periodPairOfTau (τ : ℍ) : PeriodPair where
  ω₁ := (τ : ℂ)
  ω₂ := 1
  indep := LinearIndependent.pair_iff.mpr fun s t hst ↦ by
    have him : s * (τ : ℂ).im = 0 := by
      have := congrArg Complex.im hst
      simpa [Complex.add_im, Complex.smul_im, smul_eq_mul] using this
    have hs : s = 0 :=
      (mul_eq_zero.mp him).resolve_right (UpperHalfPlane.coe_im τ ▸ τ.im_ne_zero)
    subst hs
    simpa using hst

@[scoped simp] private lemma periodPairOfTau_ω₁ (τ : ℍ) : (periodPairOfTau τ).ω₁ = (τ : ℂ) := rfl
@[scoped simp] private lemma periodPairOfTau_ω₂ (τ : ℍ) : (periodPairOfTau τ).ω₂ = 1 := rfl

private def zetaN (N : ℕ) : ℂ := cexp (2 * π * I / N)

private def qN (N : ℕ) (τ : ℂ) : ℂ := cexp (2 * π * I * τ / N)

private lemma zetaN_ne_zero (N : ℕ) : zetaN N ≠ 0 := Complex.exp_ne_zero _

private def wpTail (N a₁ a₂ : ℕ) (p : ℕ+ × ℕ+) (τ : ℂ) : ℂ :=
  ((p.2 : ℕ) : ℂ) *
    (zetaN N ^ (a₂ * (p.2 : ℕ)) * qN N τ ^ (((p.1 : ℕ) * N + a₁) * (p.2 : ℕ)) +
      (zetaN N)⁻¹ ^ (a₂ * (p.2 : ℕ)) * qN N τ ^ (((p.1 : ℕ) * N - a₁) * (p.2 : ℕ)) -
        2 * qN N τ ^ ((p.1 : ℕ) * N * (p.2 : ℕ)))

private def wpTorsion (N a₁ a₂ : ℕ) (τ : ℍ) : ℂ :=
  PeriodPair.weierstrassP (periodPairOfTau τ) (((a₁ : ℂ) * τ + a₂) / N)

private def wpTorsionSeries (N a₁ a₂ : ℕ) (τ : ℂ) : ℂ :=
  (2 * π * I) ^ 2 *
    (zetaN N ^ a₂ * qN N τ ^ a₁ / (1 - zetaN N ^ a₂ * qN N τ ^ a₁) ^ 2 + 1 / 12 +
      ∑' p : ℕ+ × ℕ+, wpTail N a₁ a₂ p τ)

private def kN (N : ℕ) : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {zetaN N}

private lemma zetaN_mem_kN (N : ℕ) : zetaN N ∈ kN N :=
  IntermediateField.mem_adjoin_simple_self ℚ _

private lemma zetaN_pow_mem_kN (N k : ℕ) : zetaN N ^ k ∈ kN N := pow_mem (zetaN_mem_kN N) k

private lemma zetaN_inv_pow_mem_kN (N k : ℕ) : (zetaN N)⁻¹ ^ k ∈ kN N :=
  pow_mem (inv_mem (zetaN_mem_kN N)) k

private lemma natCast_mem_kN (N m : ℕ) : (m : ℂ) ∈ kN N := natCast_mem _ m

private lemma one_div_twelve_mem_kN (N : ℕ) : (1 / 12 : ℂ) ∈ kN N :=
  div_mem (one_mem _) (by exact_mod_cast natCast_mem_kN N 12)

private def wpNormSeries (N a₁ a₂ : ℕ) (τ : ℂ) : ℂ :=
  zetaN N ^ a₂ * qN N τ ^ a₁ / (1 - zetaN N ^ a₂ * qN N τ ^ a₁) ^ 2 + 1 / 12 +
    ∑' p : ℕ+ × ℕ+, wpTail N a₁ a₂ p τ

private lemma wpTorsionSeries_eq (N a₁ a₂ : ℕ) (τ : ℂ) :
    wpTorsionSeries N a₁ a₂ τ = (2 * π * I) ^ 2 * wpNormSeries N a₁ a₂ τ := rfl

private def wpNorm (N a₁ a₂ : ℕ) (τ : ℍ) : ℂ := ((2 * π * I) ^ 2)⁻¹ * wpTorsion N a₁ a₂ τ

private def j : ℍ → ℂ := fun z => E₄ z ^ 3 / ModularForm.discriminant z

private def frickeTorsionPt (N : ℕ) (a : Fin 2 → ZMod N) (τ : ℍ) : ℂ :=
  (((a 0).val : ℂ) * (τ : ℂ) + ((a 1).val : ℂ)) / (N : ℂ)

private def vecMulSL (N : ℕ) (a : Fin 2 → ZMod N) (γ : SL(2, ℤ)) : Fin 2 → ZMod N :=
  Matrix.vecMul a ((γ : Matrix (Fin 2) (Fin 2) ℤ).map ((↑) : ℤ → ZMod N))

private def wpNormZ (N : ℕ) (a : Fin 2 → ZMod N) (τ : ℍ) : ℂ := wpNorm N (a 0).val (a 1).val τ

private def frickeF (N : ℕ) (a : Fin 2 → ZMod N) (τ : ℍ) : ℂ :=
  -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * wpNormZ N a τ

private abbrev FrickeIdx (N : ℕ) : Type := {a : Fin 2 → ZMod N // a ≠ 0}

private def KPoleAt (K : IntermediateField ℚ ℂ) (N m : ℕ) (f : ℍ → ℂ) : Prop :=
  Function.Periodic ((f * ⇑CuspForm.discriminant ^ m) ∘ ofComplex) N ∧
    IsBoundedAtImInfty (f * ⇑CuspForm.discriminant ^ m) ∧
    ∀ n : ℕ, (qExpansion N (f * ⇑CuspForm.discriminant ^ m)).coeff n ∈ K

private def KPole (K : IntermediateField ℚ ℂ) (N : ℕ) (f : ℍ → ℂ) : Prop :=
  MDiff f ∧ ∃ m : ℕ, KPoleAt K N m f

open UpperHalfPlane hiding I

private scoped instance slFnAction : MulSemiringAction SL(2, ℤ) (ℍ → ℂ) where
  smul γ f := fun τ ↦ f (γ⁻¹ • τ)
  one_smul f := by funext τ; show f ((1 : SL(2, ℤ))⁻¹ • τ) = f τ; rw [inv_one, one_smul]
  mul_smul γ δ f := by
    funext τ
    show f ((γ * δ)⁻¹ • τ) = f (δ⁻¹ • (γ⁻¹ • τ))
    rw [mul_inv_rev, mul_smul]
  smul_zero γ := rfl
  smul_add γ f g := rfl
  smul_one γ := rfl
  smul_mul γ f g := rfl

private lemma sl_smul_apply (γ : SL(2, ℤ)) (f : ℍ → ℂ) (τ : ℍ) : (γ • f) τ = f (γ⁻¹ • τ) := rfl

private lemma sl_smul_def (γ : SL(2, ℤ)) (f : ℍ → ℂ) : γ • f = fun τ ↦ f (γ⁻¹ • τ) := rfl

private scoped instance slFn_smulCommClass : SMulCommClass SL(2, ℤ) ℂ (ℍ → ℂ) where
  smul_comm _ _ _ := rfl

private lemma sl_smul_const (γ : SL(2, ℤ)) (c : ℂ) : γ • (fun _ : ℍ ↦ c) = fun _ ↦ c := rfl

private lemma sl_smul_eq_self_iff (f : ℍ → ℂ) :
    (∀ γ : SL(2, ℤ), γ • f = f) ↔ ∀ (γ : SL(2, ℤ)) (τ : ℍ), f (γ • τ) = f τ := by
  constructor
  · intro h γ τ
    have := congrFun (h γ⁻¹) τ
    rwa [sl_smul_apply, inv_inv] at this
  · intro h γ
    funext τ
    rw [sl_smul_apply, h]

private def levelGen (N : ℕ) : Set (ℍ → ℂ) := insert j (Set.range fun i : FrickeIdx N ↦ frickeF N i.1)

private lemma hppT : ∀ τ : ℍ, (periodPairOfTau τ).ω₁ = (τ : ℂ) ∧ (periodPairOfTau τ).ω₂ = 1 :=
  fun τ => ⟨periodPairOfTau_ω₁ τ, periodPairOfTau_ω₂ τ⟩

private lemma coe_cuspDisc : ⇑CuspForm.discriminant = ModularForm.discriminant := rfl

private lemma frickeF_eq (N : ℕ) (a : Fin 2 → ZMod N) :
    frickeF N a = fun τ =>
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 *
        (((2 * π * I) ^ 2)⁻¹ *
          PeriodPair.weierstrassP (periodPairOfTau τ)
            ((((a 0).val : ℂ) * (τ : ℂ) + ((a 1).val : ℂ)) / (N : ℂ))) := by
  funext τ
  simp only [frickeF, wpNormZ, wpNorm, wpTorsion]

private theorem levelOne_holFn_eq_polynomial_j (m : ℕ) (h : ℍ → ℂ) (hol : MDiff h)
    (hinv : ∀ γ : SL(2, ℤ), h ∣[(0 : ℤ)] γ = h)
    (hbd : IsBoundedAtImInfty (h * ⇑CuspForm.discriminant ^ m)) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ m ∧ h = fun z => Polynomial.eval (j z) P := by
  rw [coe_cuspDisc] at hbd
  obtain ⟨P, hdeg, heq⟩ := levelOne_hauptmodul_package.1 m h hol hinv hbd
  exact ⟨P, hdeg, by simpa only [j] using heq⟩

private theorem kPole_invariant_eq_polynomial_j_mem {K : IntermediateField ℚ ℂ} [NeZero N]
    {a : ℍ → ℂ} (hk : KPole K N a) (hinv : ∀ γ : SL(2, ℤ), a ∣[(0 : ℤ)] γ = a) :
    ∃ P : Polynomial ℂ, (∀ i, P.coeff i ∈ K) ∧ a = fun τ => Polynomial.eval (j τ) P := by
  obtain ⟨hmd, m, hper, hbd, hcoef⟩ := hk
  rw [coe_cuspDisc] at hper hbd hcoef
  obtain ⟨P, _, hcoefP, heq⟩ :=
    levelOne_hauptmodul_package.2.1 K N (NeZero.ne N) m a hmd hinv hper hbd hcoef
  exact ⟨P, hcoefP, by simpa only [j] using heq⟩

private theorem mdifferentiable_frickeF {N : ℕ} [NeZero N] (i : FrickeIdx N) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (frickeF N i.1) := by
  rw [frickeF_eq]
  exact (frickeFunction_modularity_package N periodPairOfTau hppT).2.2.1 i.1 i.2

private theorem isBoundedAtImInfty_frickeF_mul_discriminant {N : ℕ} [NeZero N] (i : FrickeIdx N) :
    IsBoundedAtImInfty (frickeF N i.1 * ⇑CuspForm.discriminant) := by
  rw [frickeF_eq, coe_cuspDisc]
  exact (frickeFunction_modularity_package N periodPairOfTau hppT).2.2.2.1 i.1 i.2

private lemma vecMulSL_mul (N : ℕ) (a : Fin 2 → ZMod N) (γ δ : SL(2, ℤ)) :
    vecMulSL N (vecMulSL N a γ) δ = vecMulSL N a (γ * δ) := by
  simp only [vecMulSL, Matrix.vecMul_vecMul]
  congr 1
  ext i k
  simp [Matrix.map_apply, Matrix.mul_apply, Matrix.SpecialLinearGroup.coe_mul]

private lemma vecMulSL_one (N : ℕ) (a : Fin 2 → ZMod N) : vecMulSL N a 1 = a := by
  simp only [vecMulSL, Matrix.SpecialLinearGroup.coe_one,
    Matrix.map_one ((↑) : ℤ → ZMod N) Int.cast_zero Int.cast_one, Matrix.vecMul_one]

private lemma vecMulSL_zero (N : ℕ) (γ : SL(2, ℤ)) : vecMulSL N (0 : Fin 2 → ZMod N) γ = 0 := by
  simp [vecMulSL]

private lemma vecMulSL_ne_zero {N : ℕ} {a : Fin 2 → ZMod N} (ha : a ≠ 0) (γ : SL(2, ℤ)) :
    vecMulSL N a γ ≠ 0 := by
  intro h0
  apply ha
  have h1 : vecMulSL N (vecMulSL N a γ) γ⁻¹ = a := by
    rw [vecMulSL_mul, mul_inv_cancel, vecMulSL_one]
  rw [← h1, h0, vecMulSL_zero]

private theorem frickeF_hperm {N : ℕ} [NeZero N] (γ : SL(2, ℤ)) :
    ∃ σ : Equiv.Perm (FrickeIdx N), ∀ (i : FrickeIdx N) (τ : ℍ),
      frickeF N i.1 (γ • τ) = frickeF N (σ i).1 τ := by
  refine ⟨⟨fun i => ⟨vecMulSL N i.1 γ, vecMulSL_ne_zero i.2 γ⟩,
          fun i => ⟨vecMulSL N i.1 γ⁻¹, vecMulSL_ne_zero i.2 γ⁻¹⟩, ?_, ?_⟩, ?_⟩
  · intro i
    apply Subtype.ext
    simp only [vecMulSL_mul, mul_inv_cancel, vecMulSL_one]
  · intro i
    apply Subtype.ext
    simp only [vecMulSL_mul, inv_mul_cancel, vecMulSL_one]
  · intro i τ
    have h1 := (frickeFunction_modularity_package N periodPairOfTau hppT).1 i.1 γ τ
    rw [frickeF_eq, frickeF_eq]
    exact h1

private lemma smul_frickeF {N : ℕ} [NeZero N] (γ : SL(2, ℤ)) (a : Fin 2 → ZMod N) :
    γ • frickeF N a = frickeF N (vecMulSL N a γ⁻¹) := by
  funext τ
  rw [sl_smul_apply]
  have h1 := (frickeFunction_modularity_package N periodPairOfTau hppT).1 a γ⁻¹ τ
  rw [frickeF_eq, frickeF_eq]
  exact h1

private lemma smul_j (γ : SL(2, ℤ)) : γ • j = j := by
  refine (sl_smul_eq_self_iff j).mpr (fun δ τ => ?_) γ
  have hδ : (δ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨δ, rfl⟩
  have hE := SlashInvariantForm.slash_action_eqn'' ModularForm.E₄ hδ τ
  have hD := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hδ τ
  have hd0 : denom (δ : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ τ
  simp only [j]
  rw [show ModularForm.E₄ (δ • τ) = denom (↑δ : GL (Fin 2) ℝ) τ ^ (4 : ℤ) * ModularForm.E₄ τ
        from hE,
      show ModularForm.discriminant (δ • τ)
          = denom (↑δ : GL (Fin 2) ℝ) τ ^ (12 : ℤ) * ModularForm.discriminant τ from hD,
      mul_pow, show (denom (↑δ : GL (Fin 2) ℝ) τ ^ (4 : ℤ)) ^ (3 : ℕ)
      = denom (↑δ : GL (Fin 2) ℝ) τ ^ (12 : ℤ) from by
    rw [← zpow_natCast (denom (↑δ : GL (Fin 2) ℝ) τ ^ (4 : ℤ)) 3, ← zpow_mul]; norm_num]
  exact mul_div_mul_left _ _ (zpow_ne_zero _ hd0)

section KPoleClosure

private lemma ratCast_mem_K (K : IntermediateField ℚ ℂ) (q : ℚ) : (q : ℂ) ∈ K :=
  eq_ratCast (algebraMap ℚ ℂ) q ▸ IntermediateField.algebraMap_mem K q

private lemma hNposR (N : ℕ) [NeZero N] : (0 : ℝ) < N := by
  exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)

private lemma disc_hol : MDiff (⇑CuspForm.discriminant : ℍ → ℂ) := CuspForm.discriminant.holo'

private lemma disc_bdd : IsBoundedAtImInfty (⇑CuspForm.discriminant : ℍ → ℂ) :=
  (CuspFormClass.zero_at_infty CuspForm.discriminant).isBoundedAtImInfty

private lemma disc_per1 :
    Function.Periodic ((⇑CuspForm.discriminant : ℍ → ℂ) ∘ ofComplex) 1 := by
  simpa using SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant one_mem_strictPeriods_SL

private lemma E4_per1 :
    Function.Periodic ((⇑ModularForm.E₄ : ℍ → ℂ) ∘ ofComplex) 1 := by
  simpa using SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄ one_mem_strictPeriods_SL

private lemma E4_hol : MDiff (⇑ModularForm.E₄ : ℍ → ℂ) := ModularForm.E₄.holo'

private lemma E4_bdd : IsBoundedAtImInfty (⇑ModularForm.E₄ : ℍ → ℂ) :=
  ModularFormClass.bdd_at_infty ModularForm.E₄

private def NiceK (K : IntermediateField ℚ ℂ) (N : ℕ) (f : ℍ → ℂ) : Prop :=
  Function.Periodic (f ∘ ofComplex) (N : ℂ) ∧ MDiff f ∧ IsBoundedAtImInfty f ∧
    ∀ n, (qExpansion N f).coeff n ∈ K

private lemma NiceK.analytic {K : IntermediateField ℚ ℂ} {N : ℕ} [NeZero N] {f : ℍ → ℂ}
    (hf : NiceK K N f) : AnalyticAt ℂ (cuspFunction N f) 0 :=
  analyticAt_cuspFunction_zero (hNposR N) (by exact_mod_cast hf.1) hf.2.1 hf.2.2.1

private lemma perN_of_per1 {f : ℍ → ℂ} (hp : Function.Periodic (f ∘ ofComplex) 1) (N : ℕ) :
    Function.Periodic (f ∘ ofComplex) (N : ℂ) := by
  simpa using hp.nat_mul N

private lemma NiceK.mul {K : IntermediateField ℚ ℂ} {N : ℕ} [NeZero N] {f g : ℍ → ℂ}
    (hf : NiceK K N f) (hg : NiceK K N g) : NiceK K N (f * g) := by
  refine ⟨hf.1.mul hg.1, hf.2.1.mul hg.2.1, hf.2.2.1.mul hg.2.2.1, fun n => ?_⟩
  rw [qExpansion_mul hf.analytic hg.analytic, PowerSeries.coeff_mul]
  exact sum_mem fun p _ => mul_mem (hf.2.2.2 p.1) (hg.2.2.2 p.2)

private lemma NiceK.pow {K : IntermediateField ℚ ℂ} {N : ℕ} [NeZero N] {f : ℍ → ℂ}
    (hf : NiceK K N f) : ∀ k : ℕ, k ≠ 0 → NiceK K N (f ^ k)
  | 1, _ => by simpa using hf
  | (k + 2), _ => by
      rw [pow_succ]
      exact (NiceK.pow hf (k + 1) k.succ_ne_zero).mul hf

private lemma NiceK.add {K : IntermediateField ℚ ℂ} {N : ℕ} [NeZero N] {f g : ℍ → ℂ}
    (hf : NiceK K N f) (hg : NiceK K N g) : NiceK K N (f + g) := by
  refine ⟨hf.1.add hg.1, hf.2.1.add hg.2.1, hf.2.2.1.add hg.2.2.1, fun n => ?_⟩
  rw [qExpansion_add hf.analytic hg.analytic, map_add]
  exact add_mem (hf.2.2.2 n) (hg.2.2.2 n)

private lemma NiceK.disc {K : IntermediateField ℚ ℂ} {N : ℕ} [NeZero N] :
    NiceK K N (⇑CuspForm.discriminant : ℍ → ℂ) := by
  refine ⟨perN_of_per1 disc_per1 N, disc_hol, disc_bdd, fun n => ?_⟩
  have hd := (weierstrassP_torsion_qExpansion_package N (NeZero.ne N) periodPairOfTau
      hppT).2.2.2.1 (⇑CuspForm.discriminant : ℍ → ℂ) (by simpa using disc_per1) disc_hol disc_bdd n
  rw [hd]
  split_ifs
  · obtain ⟨q, hq⟩ := (weierstrassP_torsion_qExpansion_package N (NeZero.ne N) periodPairOfTau
        hppT).2.2.2.2.2.2 (n / N)
    rw [show (⇑CuspForm.discriminant : ℍ → ℂ) = (ModularForm.discriminant : ℍ → ℂ) from
      coe_cuspDisc, hq]
    exact ratCast_mem_K K q
  · exact zero_mem K

private lemma NiceK.E4 {K : IntermediateField ℚ ℂ} {N : ℕ} [NeZero N] :
    NiceK K N (⇑ModularForm.E₄ : ℍ → ℂ) := by
  refine ⟨perN_of_per1 E4_per1 N, E4_hol, E4_bdd, fun n => ?_⟩
  have hd := (weierstrassP_torsion_qExpansion_package N (NeZero.ne N) periodPairOfTau
      hppT).2.2.2.1 (⇑ModularForm.E₄ : ℍ → ℂ) (by simpa using E4_per1) E4_hol E4_bdd n
  rw [hd]
  split_ifs
  · obtain ⟨q, hq⟩ := (weierstrassP_torsion_qExpansion_package N (NeZero.ne N) periodPairOfTau
        hppT).2.2.2.2.1 (n / N)
    rw [hq]
    exact ratCast_mem_K K q
  · exact zero_mem K

private lemma cuspFunction_const (N : ℕ) (c : ℂ) :
    cuspFunction N (fun _ : ℍ => c) = fun _ => c := by
  funext q
  rcases eq_or_ne q 0 with rfl | hq
  · show Function.Periodic.cuspFunction N ((fun _ : ℍ => c) ∘ ofComplex) 0 = c
    rw [Function.Periodic.cuspFunction_zero_eq_limUnder_nhds_ne]
    refine Filter.Tendsto.limUnder_eq ?_
    refine Filter.Tendsto.congr' ?_ (tendsto_const_nhds :
      Filter.Tendsto (fun _ : ℂ => (c : ℂ)) (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) (nhds (c : ℂ)))
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact (Function.Periodic.cuspFunction_eq_of_nonzero (N : ℝ)
      ((fun _ : ℍ => (c : ℂ)) ∘ ofComplex) hq).symm
  · show Function.Periodic.cuspFunction N ((fun _ : ℍ => c) ∘ ofComplex) q = c
    rw [Function.Periodic.cuspFunction_eq_of_nonzero _ _ hq]
    rfl

private lemma NiceK.const {K : IntermediateField ℚ ℂ} {N : ℕ} [NeZero N] (c : ↥K) :
    NiceK K N (fun _ : ℍ => (c : ℂ)) := by
  refine ⟨fun x => rfl, ?_, ?_, fun n => ?_⟩
  · exact mdifferentiable_const
  · exact Filter.const_boundedAtFilter _ _
  · have hq : qExpansion N (fun _ : ℍ => (c : ℂ)) = PowerSeries.C (c : ℂ) := by
      ext m
      simp only [qExpansion_coeff, cuspFunction_const, iteratedDeriv_const, PowerSeries.coeff_C]
      rcases eq_or_ne m 0 with rfl | hm
      · simp
      · simp [hm]
    rw [hq]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [PowerSeries.coeff_C, hn]

private lemma kPoleAt_of_niceK {K : IntermediateField ℚ ℂ} {N : ℕ} [NeZero N] {f : ℍ → ℂ} {m : ℕ}
    (h : NiceK K N (f * ⇑CuspForm.discriminant ^ m)) : KPoleAt K N m f :=
  ⟨by exact_mod_cast h.1, h.2.2.1, h.2.2.2⟩

private lemma niceK_mul_disc_pow {K : IntermediateField ℚ ℂ} {N : ℕ} [NeZero N] {f : ℍ → ℂ} {m : ℕ}
    (hmd : MDiff f) (hf : KPoleAt K N m f) : NiceK K N (f * ⇑CuspForm.discriminant ^ m) :=
  ⟨by exact_mod_cast hf.1, hmd.mul (disc_hol.pow m), hf.2.1, hf.2.2⟩

private lemma kPole_const {K : IntermediateField ℚ ℂ} {N : ℕ} [NeZero N] (c : ↥K) :
    KPole K N (algebraMap ↥K (ℍ → ℂ) c) := by
  have hc : algebraMap ↥K (ℍ → ℂ) c = fun _ : ℍ => (c : ℂ) := rfl
  rw [hc]
  refine ⟨mdifferentiable_const, 0, kPoleAt_of_niceK ?_⟩
  simpa using NiceK.const c

private lemma kPole_add {K : IntermediateField ℚ ℂ} {N : ℕ} [NeZero N] {f g : ℍ → ℂ}
    (hf : KPole K N f) (hg : KPole K N g) : KPole K N (f + g) := by
  obtain ⟨hfm, mf, hfa⟩ := hf
  obtain ⟨hgm, mg, hga⟩ := hg
  have hf' : NiceK K N (f * ⇑CuspForm.discriminant ^ (mf + mg)) := by
    have : f * ⇑CuspForm.discriminant ^ (mf + mg)
        = (f * ⇑CuspForm.discriminant ^ mf) * ⇑CuspForm.discriminant ^ mg := by
      rw [mul_assoc, ← pow_add]
    rcases Nat.eq_zero_or_pos mg with rfl | hmg
    · simpa using niceK_mul_disc_pow hfm hfa
    · rw [this]
      exact (niceK_mul_disc_pow hfm hfa).mul (NiceK.disc.pow mg hmg.ne')
  have hg' : NiceK K N (g * ⇑CuspForm.discriminant ^ (mf + mg)) := by
    have : g * ⇑CuspForm.discriminant ^ (mf + mg)
        = (g * ⇑CuspForm.discriminant ^ mg) * ⇑CuspForm.discriminant ^ mf := by
      rw [mul_assoc, ← pow_add, Nat.add_comm]
    rcases Nat.eq_zero_or_pos mf with rfl | hmf
    · simpa using niceK_mul_disc_pow hgm hga
    · rw [this]
      exact (niceK_mul_disc_pow hgm hga).mul (NiceK.disc.pow mf hmf.ne')
  refine ⟨hfm.add hgm, mf + mg, kPoleAt_of_niceK ?_⟩
  have : (f + g) * ⇑CuspForm.discriminant ^ (mf + mg)
      = f * ⇑CuspForm.discriminant ^ (mf + mg) + g * ⇑CuspForm.discriminant ^ (mf + mg) :=
    add_mul f g _
  rw [this]
  exact hf'.add hg'

private lemma kPole_mul {K : IntermediateField ℚ ℂ} {N : ℕ} [NeZero N] {f g : ℍ → ℂ}
    (hf : KPole K N f) (hg : KPole K N g) : KPole K N (f * g) := by
  obtain ⟨hfm, mf, hfa⟩ := hf
  obtain ⟨hgm, mg, hga⟩ := hg
  refine ⟨hfm.mul hgm, mf + mg, kPoleAt_of_niceK ?_⟩
  have : (f * g) * ⇑CuspForm.discriminant ^ (mf + mg)
      = (f * ⇑CuspForm.discriminant ^ mf) * (g * ⇑CuspForm.discriminant ^ mg) := by
    rw [pow_add]; ring
  rw [this]
  exact (niceK_mul_disc_pow hfm hfa).mul (niceK_mul_disc_pow hgm hga)

private theorem kPole_of_mem_adjoin {K : IntermediateField ℚ ℂ} [NeZero N] {S : Set (ℍ → ℂ)}
    (hS : ∀ f ∈ S, KPole K N f) {a : ℍ → ℂ} (ha : a ∈ Algebra.adjoin ↥K S) : KPole K N a := by
  induction ha using Algebra.adjoin_induction with
  | mem f hf => exact hS f hf
  | algebraMap c => exact kPole_const c
  | add f g _ _ ihf ihg => exact kPole_add ihf ihg
  | mul f g _ _ ihf ihg => exact kPole_mul ihf ihg

private lemma kPole_j (K : IntermediateField ℚ ℂ) [NeZero N] : KPole K N j := by
  have hmd : MDiff j := by
    intro τ
    exact (((E4_hol τ).pow 3).div (disc_hol τ) (ModularForm.discriminant_ne_zero τ))
  refine ⟨hmd, 1, kPoleAt_of_niceK ?_⟩
  have hjd : j * ⇑CuspForm.discriminant ^ 1 = (⇑ModularForm.E₄ : ℍ → ℂ) ^ 3 := by
    funext τ
    simp only [Pi.mul_apply, Pi.pow_apply, pow_one, j, coe_cuspDisc]
    field_simp [ModularForm.discriminant_ne_zero τ]
  rw [hjd]
  exact NiceK.E4.pow 3 (by norm_num)

private lemma kPole_frickeF {K : IntermediateField ℚ ℂ} [NeZero N] (hK : kN N ≤ K) (i : FrickeIdx N) :
    KPole K N (frickeF N i.1) := by
  have pkg := frickeFunction_modularity_package N periodPairOfTau hppT
  have hmd : MDiff (frickeF N i.1) := mdifferentiable_frickeF i
  refine ⟨hmd, 1, ?_, ?_, ?_⟩
  · have hper := (pkg.2.2.2.2.1 i.1 i.2).1
    rw [frickeF_eq, coe_cuspDisc]
    simpa [pow_one] using hper
  · have hbd := pkg.2.2.2.1 i.1 i.2
    rw [frickeF_eq, coe_cuspDisc]
    simpa [pow_one] using hbd
  · intro n
    have hco := (pkg.2.2.2.2.1 i.1 i.2).2 n
    rw [frickeF_eq, coe_cuspDisc]
    refine hK ?_
    simpa [pow_one, kN, zetaN] using hco

end KPoleClosure

end R4bFloor

section B6_fixedFrac

variable {A : Type*} [CommRing A] {G : Type*} [Group G] [Fintype G] [MulSemiringAction G A]

private lemma smul_prod_smul_eq (v : A) (g₀ : G) : g₀ • (∏ g : G, g • v) = ∏ g : G, g • v := by
  rw [show g₀ • (∏ g : G, g • v) = MulSemiringAction.toRingHom G A g₀ (∏ g : G, g • v) from rfl,
    map_prod]
  simp only [MulSemiringAction.toRingHom_apply, smul_smul]
  exact Fintype.prod_equiv (Equiv.mulLeft g₀) _ _ fun g ↦ rfl

variable [IsDomain A] {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
  [MulSemiringAction G K]

private theorem exists_fixed_div_of_fixed
    (hcompat : ∀ (g : G) (a : A), g • algebraMap A K a = algebraMap A K (g • a))
    (x : K) (hx : ∀ g : G, g • x = x) :
    ∃ a b : A, (∀ g : G, g • a = a) ∧ (∀ g : G, g • b = b) ∧ algebraMap A K b ≠ 0 ∧
      x * algebraMap A K b = algebraMap A K a := by
  classical
  obtain ⟨u, v, hv, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  have hv0 : v ≠ 0 := nonZeroDivisors.ne_zero hv
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  set b : A := ∏ g : G, g • v with hb
  set a : A := u * ∏ g ∈ (Finset.univ : Finset G).erase 1, g • v with ha
  have hbfix : ∀ g : G, g • b = b := fun g ↦ smul_prod_smul_eq v g
  have hb0 : algebraMap A K b ≠ 0 := by
    rw [map_ne_zero_iff _ hinj, hb]
    exact Finset.prod_ne_zero_iff.mpr fun g _ ↦ (smul_ne_zero_iff_ne g).mpr hv0
  have hxb : algebraMap A K u / algebraMap A K v * algebraMap A K b = algebraMap A K a := by
    have hv0' : algebraMap A K v ≠ 0 := (map_ne_zero_iff _ hinj).mpr hv0
    rw [hb, ← Finset.mul_prod_erase _ _ (Finset.mem_univ (1 : G)), one_smul, ha, map_mul,
      map_mul]
    field_simp
  refine ⟨a, b, fun g ↦ ?_, hbfix, hb0, hxb⟩
  apply hinj
  rw [← hcompat, ← hxb, smul_mul', hx, hcompat, hbfix]

end B6_fixedFrac

section B6Engine

open UpperHalfPlane ModularForm SlashInvariantForm ModularFormClass CuspForm ModularForm.CuspForm Polynomial Real.Polynomial
open scoped UpperHalfPlane ModularForm SlashInvariantForm ModularFormClass CuspForm ModularForm.CuspForm Polynomial Real.Polynomial
open scoped MatrixGroups Manifold

variable {I : Type*} [Fintype I] (h : I → ℍ → ℂ) (m : ℕ)

private def orbitCoeff (k : ℕ) : ℍ → ℂ := fun τ => (∏ i, (X - C (h i τ))).coeff k

private lemma coeff_X_sub_C_mul (a : ℂ) (p : Polynomial ℂ) (k : ℕ) :
    ((X - C a) * p).coeff k = (if k = 0 then 0 else p.coeff (k - 1)) - a * p.coeff k := by
  rw [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
  congr 1
  cases k with
  | zero => simp [Polynomial.mul_coeff_zero]
  | succ k' => simp [Polynomial.coeff_X_mul]

omit [Fintype I] in
private lemma mdiff_orbitCoeff_prod (hhol : ∀ i, MDiff (h i)) (s : Finset I) (k : ℕ) :
    MDiff ((fun τ : ℍ => (∏ i ∈ s, (X - C (h i τ))).coeff k) : ℍ → ℂ) := by
  induction s using Finset.cons_induction generalizing k with
  | empty =>
    simp only [Finset.prod_empty, Polynomial.coeff_one]
    exact mdifferentiable_const
  | cons a s ha ih =>
    have hrw : ∀ τ : ℍ, (∏ i ∈ Finset.cons a s ha, (X - C (h i τ))).coeff k =
        (if k = 0 then 0 else (∏ i ∈ s, (X - C (h i τ))).coeff (k - 1)) -
          h a τ * (∏ i ∈ s, (X - C (h i τ))).coeff k := by
      intro τ
      rw [Finset.prod_cons, coeff_X_sub_C_mul]
    simp only [hrw]
    cases k with
    | zero =>
      exact mdifferentiable_const.sub ((hhol a).mul (ih 0))
    | succ k' =>
      simp only [ite_eq_right (Nat.succ_ne_zero k'), Nat.add_sub_cancel]
      exact (ih k').sub ((hhol a).mul (ih (k' + 1)))

omit [Fintype I] in
private lemma bounded_orbitCoeff_prod
    (hbd : ∀ i, IsBoundedAtImInfty (h i * ⇑CuspForm.discriminant ^ m)) (s : Finset I) (k : ℕ) :
    IsBoundedAtImInfty (fun τ =>
      (∏ i ∈ s, (X - C (h i τ))).coeff k * CuspForm.discriminant τ ^ ((s.card - k) * m)) := by
  induction s using Finset.cons_induction generalizing k with
  | empty =>
    simp only [Finset.prod_empty, Polynomial.coeff_one, Finset.card_empty, Nat.zero_sub,
      Nat.zero_mul, pow_zero, mul_one]
    exact Filter.const_boundedAtFilter _ _
  | cons a s ha ih =>
    have hdeg : ∀ τ : ℍ, (∏ i ∈ s, (X - C (h i τ))).natDegree = s.card := by
      intro τ
      rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C (h i τ))]
      simp
    cases k with
    | zero =>
      have hshape : (fun τ : ℍ =>
          (∏ i ∈ Finset.cons a s ha, (X - C (h i τ))).coeff 0 *
            CuspForm.discriminant τ ^ (((Finset.cons a s ha).card - 0) * m)) = fun τ : ℍ =>
          -((h a τ * CuspForm.discriminant τ ^ m) *
            ((∏ i ∈ s, (X - C (h i τ))).coeff 0 *
              CuspForm.discriminant τ ^ ((s.card - 0) * m))) := by
        funext τ
        rw [Finset.prod_cons, coeff_X_sub_C_mul, ite_eq_left rfl, Finset.card_cons, Nat.sub_zero,
          Nat.sub_zero, zero_sub, show (s.card + 1) * m = m + s.card * m by ring, pow_add]
        ring
      rw [hshape]
      exact ((hbd a).mul (ih 0)).neg
    | succ k' =>
      rcases Nat.lt_or_ge s.card (k' + 1) with hk | hk
      · have hzero : ∀ τ : ℍ, (∏ i ∈ s, (X - C (h i τ))).coeff (k' + 1) = 0 := fun τ =>
          coeff_eq_zero_of_natDegree_lt (by rw [hdeg τ]; exact hk)
        have hshape : (fun τ : ℍ =>
            (∏ i ∈ Finset.cons a s ha, (X - C (h i τ))).coeff (k' + 1) *
              CuspForm.discriminant τ ^ (((Finset.cons a s ha).card - (k' + 1)) * m)) =
            fun τ : ℍ =>
            (∏ i ∈ s, (X - C (h i τ))).coeff k' *
              CuspForm.discriminant τ ^ ((s.card - k') * m) := by
          funext τ
          rw [Finset.prod_cons, coeff_X_sub_C_mul, ite_eq_right (Nat.succ_ne_zero k'),
            Nat.add_sub_cancel, hzero τ, mul_zero, sub_zero, Finset.card_cons,
            Nat.succ_sub_succ]
        rw [hshape]
        exact ih k'
      · have he2 : (s.card - k') * m = m + (s.card - (k' + 1)) * m := by
          have h1 : s.card - k' = 1 + (s.card - (k' + 1)) := by omega
          rw [h1]
          ring
        have hshape : (fun τ : ℍ =>
            (∏ i ∈ Finset.cons a s ha, (X - C (h i τ))).coeff (k' + 1) *
              CuspForm.discriminant τ ^ (((Finset.cons a s ha).card - (k' + 1)) * m)) =
            fun τ : ℍ =>
            ((∏ i ∈ s, (X - C (h i τ))).coeff k' *
              CuspForm.discriminant τ ^ ((s.card - k') * m)) -
            ((h a τ * CuspForm.discriminant τ ^ m) *
              ((∏ i ∈ s, (X - C (h i τ))).coeff (k' + 1) *
                CuspForm.discriminant τ ^ ((s.card - (k' + 1)) * m))) := by
          funext τ
          rw [Finset.prod_cons, coeff_X_sub_C_mul, ite_eq_right (Nat.succ_ne_zero k'),
            Nat.add_sub_cancel, Finset.card_cons, Nat.succ_sub_succ, sub_mul]
          congr 1
          rw [he2, pow_add]
          ring
        rw [hshape]
        exact (ih k').sub ((hbd a).mul (ih (k' + 1)))

private theorem orbitCoeff_slash_invariant
    (hperm : ∀ γ : SL(2, ℤ), ∃ σ : Equiv.Perm I, ∀ i τ, h i (γ • τ) = h (σ i) τ)
    (k : ℕ) (γ : SL(2, ℤ)) : orbitCoeff h k ∣[(0 : ℤ)] γ = orbitCoeff h k := by
  obtain ⟨σ, hσ⟩ := hperm γ
  funext τ
  simp only [SL_slash_apply, neg_zero, zpow_zero, mul_one]
  show (∏ i, (X - C (h i (γ • τ)))).coeff k = (∏ i, (X - C (h i τ))).coeff k
  have hprod : (∏ i, (X - C (h i (γ • τ)))) = ∏ i, (X - C (h i τ)) := by
    calc ∏ i, (X - C (h i (γ • τ)))
        = ∏ i, (X - C (h (σ i) τ)) := by
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [hσ i τ]
      _ = ∏ i, (X - C (h i τ)) := Equiv.prod_comp σ (fun i' => X - C (h i' τ))
  rw [hprod]

private theorem exists_poly_j_orbitCoeff
    (hperm : ∀ γ : SL(2, ℤ), ∃ σ : Equiv.Perm I, ∀ i τ, h i (γ • τ) = h (σ i) τ)
    (hhol : ∀ i, MDiff (h i))
    (hbd : ∀ i, IsBoundedAtImInfty (h i * ⇑CuspForm.discriminant ^ m)) (k : ℕ) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ (Fintype.card I - k) * m ∧
      orbitCoeff h k = fun τ => Polynomial.eval (j τ) P := by
  refine levelOne_holFn_eq_polynomial_j ((Fintype.card I - k) * m) (orbitCoeff h k)
    (mdiff_orbitCoeff_prod h hhol Finset.univ k)
    (orbitCoeff_slash_invariant h hperm k) ?_
  have hb := bounded_orbitCoeff_prod h m hbd Finset.univ k
  rw [Finset.card_univ] at hb
  have hshape : ((orbitCoeff h k * ⇑CuspForm.discriminant ^ ((Fintype.card I - k) * m)
      : ℍ → ℂ)) =
      fun τ : ℍ => (∏ i, (X - C (h i τ))).coeff k *
        CuspForm.discriminant τ ^ ((Fintype.card I - k) * m) := by
    funext τ
    simp [orbitCoeff]
  rw [hshape]
  exact hb

private theorem orbit_integral_over_j
    (hperm : ∀ γ : SL(2, ℤ), ∃ σ : Equiv.Perm I, ∀ i τ, h i (γ • τ) = h (σ i) τ)
    (hhol : ∀ i, MDiff (h i))
    (hbd : ∀ i, IsBoundedAtImInfty (h i * ⇑CuspForm.discriminant ^ m)) :
    ∃ P : ℕ → Polynomial ℂ, (∀ k, (P k).natDegree ≤ (Fintype.card I - k) * m) ∧
      ∀ (i : I) (τ : ℍ), h i τ ^ Fintype.card I +
        ∑ k ∈ Finset.range (Fintype.card I),
          Polynomial.eval (j τ) (P k) * h i τ ^ k = 0 := by
  choose P hPdeg hP using fun k => exists_poly_j_orbitCoeff h m hperm hhol hbd k
  refine ⟨P, hPdeg, fun i τ => ?_⟩
  set Q : Polynomial ℂ := ∏ i', (X - C (h i' τ)) with hQ
  have hQmonic : Q.Monic := monic_prod_of_monic _ _ fun i' _ => monic_X_sub_C (h i' τ)
  have hQdeg : Q.natDegree = Fintype.card I := by
    rw [hQ, natDegree_prod_of_monic _ _ (fun i' _ => monic_X_sub_C (h i' τ))]
    simp
  have hroot : Polynomial.eval (h i τ) Q = 0 := by
    rw [hQ, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have hexp := Polynomial.eval_eq_sum_range' (n := Fintype.card I + 1)
    (by rw [hQdeg]; exact Nat.lt_succ_self _) (h i τ) (p := Q)
  rw [Finset.sum_range_succ] at hexp
  have hlead : Q.coeff (Fintype.card I) = 1 := by
    have := hQmonic.coeff_natDegree
    rwa [hQdeg] at this
  have hcoeffs : ∀ k, Q.coeff k = Polynomial.eval (j τ) (P k) := by
    intro k
    have := congrFun (hP k) τ
    simpa [orbitCoeff, hQ] using this
  rw [hroot.symm, hexp, hlead, one_mul, add_comm]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by rw [hcoeffs k]

end B6Engine

section B6Instance

open UpperHalfPlane ModularForm CuspForm ModularForm.CuspForm Polynomial Real.Polynomial
open scoped UpperHalfPlane ModularForm CuspForm ModularForm.CuspForm Polynomial Real.Polynomial
open scoped MatrixGroups Manifold

private theorem frickeF_integral_over_j (N : ℕ) [NeZero N] :
    ∃ P : ℕ → Polynomial ℂ,
      (∀ k, (P k).natDegree ≤ Fintype.card (FrickeIdx N) - k) ∧
      ∀ (i : FrickeIdx N) (τ : ℍ),
        frickeF N i.1 τ ^ Fintype.card (FrickeIdx N) +
          ∑ k ∈ Finset.range (Fintype.card (FrickeIdx N)),
            Polynomial.eval (j τ) (P k) * frickeF N i.1 τ ^ k = 0 := by
  have h := orbit_integral_over_j (fun i : FrickeIdx N => frickeF N i.1) 1
    (fun γ => frickeF_hperm γ)
    (fun i => mdifferentiable_frickeF i)
    (fun i => by rw [pow_one]; exact isBoundedAtImInfty_frickeF_mul_discriminant i)
  simpa [mul_one] using h

end B6Instance

section B6Ring

open UpperHalfPlane ModularForm SlashInvariantForm ModularFormClass CuspForm ModularForm.CuspForm Polynomial Real.Polynomial Filter
open scoped UpperHalfPlane ModularForm SlashInvariantForm ModularFormClass CuspForm ModularForm.CuspForm Polynomial Real.Polynomial Filter
open scoped MatrixGroups Manifold

private def PoleBounded (f : ℍ → ℂ) : Prop :=
  MDiff f ∧ ∃ m : ℕ, IsBoundedAtImInfty (f * ⇑CuspForm.discriminant ^ m)

private lemma isBoundedAtImInfty_discriminant : IsBoundedAtImInfty (⇑CuspForm.discriminant : ℍ → ℂ) :=
  (CuspFormClass.zero_at_infty CuspForm.discriminant).boundedAtFilter

private lemma isBoundedAtImInfty_discPow (n : ℕ) :
    IsBoundedAtImInfty (⇑CuspForm.discriminant ^ n : ℍ → ℂ) := by
  induction n with
  | zero => exact pow_zero (⇑CuspForm.discriminant : ℍ → ℂ) ▸ const_boundedAtFilter _ (1 : ℂ)
  | succ k ih =>
    rw [pow_succ]
    exact ih.mul isBoundedAtImInfty_discriminant

private lemma IsBoundedAtImInfty.mul_discPow_mono {f : ℍ → ℂ} {m m' : ℕ} (hm : m ≤ m')
    (h : IsBoundedAtImInfty (f * ⇑CuspForm.discriminant ^ m)) :
    IsBoundedAtImInfty (f * ⇑CuspForm.discriminant ^ m') := by
  have hshape : (f * ⇑CuspForm.discriminant ^ m' : ℍ → ℂ) =
      (f * ⇑CuspForm.discriminant ^ m) * ⇑CuspForm.discriminant ^ (m' - m) := by
    funext τ
    simp only [Pi.mul_apply, Pi.pow_apply]
    rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hm]
  rw [hshape]
  exact h.mul (isBoundedAtImInfty_discPow (m' - m))

private lemma poleBounded_algebraMap (r : ℂ) : PoleBounded (algebraMap ℂ (ℍ → ℂ) r) := by
  refine ⟨mdifferentiable_const, 0, ?_⟩
  have hshape : ((algebraMap ℂ (ℍ → ℂ) r) * ⇑CuspForm.discriminant ^ 0 : ℍ → ℂ) =
      fun _ => r := by
    funext τ
    simp
  rw [hshape]
  exact const_boundedAtFilter _ r

private lemma PoleBounded.add {f g : ℍ → ℂ} (hf : PoleBounded f) (hg : PoleBounded g) :
    PoleBounded (f + g) := by
  obtain ⟨hf1, m1, hf2⟩ := hf
  obtain ⟨hg1, m2, hg2⟩ := hg
  refine ⟨hf1.add hg1, max m1 m2, ?_⟩
  have hshape : ((f + g) * ⇑CuspForm.discriminant ^ max m1 m2 : ℍ → ℂ) =
      f * ⇑CuspForm.discriminant ^ max m1 m2 + g * ⇑CuspForm.discriminant ^ max m1 m2 := by
    funext τ
    simp [add_mul]
  rw [hshape]
  exact (IsBoundedAtImInfty.mul_discPow_mono (le_max_left _ _) hf2).add
    (IsBoundedAtImInfty.mul_discPow_mono (le_max_right _ _) hg2)

private lemma PoleBounded.mul {f g : ℍ → ℂ} (hf : PoleBounded f) (hg : PoleBounded g) :
    PoleBounded (f * g) := by
  obtain ⟨hf1, m1, hf2⟩ := hf
  obtain ⟨hg1, m2, hg2⟩ := hg
  refine ⟨hf1.mul hg1, m1 + m2, ?_⟩
  have hshape : ((f * g) * ⇑CuspForm.discriminant ^ (m1 + m2) : ℍ → ℂ) =
      (f * ⇑CuspForm.discriminant ^ m1) * (g * ⇑CuspForm.discriminant ^ m2) := by
    funext τ
    simp only [Pi.mul_apply, Pi.pow_apply, pow_add]
    ring
  rw [hshape]
  exact hf2.mul hg2

private theorem poleBounded_of_mem_adjoin {S : Set (ℍ → ℂ)} (hS : ∀ f ∈ S, PoleBounded f)
    {a : ℍ → ℂ} (ha : a ∈ Algebra.adjoin ℂ S) : PoleBounded a := by
  induction ha using Algebra.adjoin_induction with
  | mem f hf => exact hS f hf
  | algebraMap r => exact poleBounded_algebraMap r
  | add x y hx hy ihx ihy => exact ihx.add ihy
  | mul x y hx hy ihx ihy => exact ihx.mul ihy

private lemma poleBounded_j : PoleBounded j := by
  constructor
  · exact (ModularForm.E₄.holo'.pow 3).div CuspForm.discriminant.holo'
      ModularForm.discriminant_ne_zero
  · refine ⟨1, ?_⟩
    have hshape : (j * ⇑CuspForm.discriminant ^ 1 : ℍ → ℂ) = ⇑ModularForm.E₄ ^ 3 := by
      funext τ
      simp only [Pi.mul_apply, Pi.pow_apply, pow_one, j]
      rw [congrFun CuspForm.coe_discriminant τ]
      exact div_mul_cancel₀ _ (ModularForm.discriminant_ne_zero τ)
    rw [hshape]
    have h4 : IsBoundedAtImInfty (⇑ModularForm.E₄ : ℍ → ℂ) := ModularFormClass.bdd_at_infty _
    have hpow : (⇑ModularForm.E₄ ^ 3 : ℍ → ℂ) =
        ⇑ModularForm.E₄ * (⇑ModularForm.E₄ * ⇑ModularForm.E₄) := by
      funext τ
      simp only [Pi.pow_apply, Pi.mul_apply]
      ring
    rw [hpow]
    exact h4.mul (h4.mul h4)

private lemma poleBounded_frickeF {N : ℕ} [NeZero N] (i : FrickeIdx N) :
    PoleBounded (frickeF N i.1) := by
  refine ⟨mdifferentiable_frickeF i, 1, ?_⟩
  have hshape : (frickeF N i.1 * ⇑CuspForm.discriminant ^ 1 : ℍ → ℂ) =
      frickeF N i.1 * ⇑CuspForm.discriminant := by
    funext τ
    simp
  rw [hshape]
  exact isBoundedAtImInfty_frickeF_mul_discriminant i

private theorem eq_polynomial_j_of_invariant_of_mem_adjoin {S : Set (ℍ → ℂ)}
    (hS : ∀ f ∈ S, PoleBounded f) {a : ℍ → ℂ} (ha : a ∈ Algebra.adjoin ℂ S)
    (hinv : ∀ γ : SL(2, ℤ), a ∣[(0 : ℤ)] γ = a) :
    ∃ P : Polynomial ℂ, a = fun τ => Polynomial.eval (j τ) P := by
  obtain ⟨hol, m, hbd⟩ := poleBounded_of_mem_adjoin hS ha
  obtain ⟨P, -, hP⟩ := levelOne_holFn_eq_polynomial_j m a hol hinv hbd
  exact ⟨P, hP⟩

end B6Ring

section LevelRingK

open UpperHalfPlane ModularForm CuspForm ModularForm.CuspForm Polynomial Real.Polynomial
open scoped UpperHalfPlane ModularForm CuspForm ModularForm.CuspForm Polynomial Real.Polynomial
open scoped MatrixGroups Manifold

variable {N : ℕ}

private noncomputable def levelRingK (K : IntermediateField ℚ ℂ) (N : ℕ) : Subalgebra ↥K (ℍ → ℂ) :=
  Algebra.adjoin ↥K (levelGen N)

private lemma j_mem_levelRingK {K : IntermediateField ℚ ℂ} : j ∈ levelRingK K N :=
  Algebra.subset_adjoin (Set.mem_insert _ _)

private lemma frickeF_mem_levelRingK {K : IntermediateField ℚ ℂ} [NeZero N] (i : FrickeIdx N) :
    frickeF N i.1 ∈ levelRingK K N :=
  Algebra.subset_adjoin (Set.mem_insert_iff.mpr (Or.inr ⟨i, rfl⟩))

private theorem smul_mem_levelRingK {K : IntermediateField ℚ ℂ} [NeZero N] (γ : SL(2, ℤ)) {f : ℍ → ℂ}
    (hf : f ∈ levelRingK K N) : γ • f ∈ levelRingK K N := by
  induction hf using Algebra.adjoin_induction with
  | mem g hg =>
    rcases hg with rfl | ⟨i, rfl⟩
    · rw [smul_j]
      exact j_mem_levelRingK
    · rw [smul_frickeF]
      exact frickeF_mem_levelRingK ⟨vecMulSL N i.1 γ⁻¹, vecMulSL_ne_zero i.2 γ⁻¹⟩
  | algebraMap r =>
    have h : γ • (algebraMap ↥K (ℍ → ℂ) r) = algebraMap ↥K (ℍ → ℂ) r :=
      sl_smul_const γ (r : ℂ)
    rw [h]
    exact Subalgebra.algebraMap_mem _ r
  | add x y hx hy ihx ihy =>
    rw [smul_add]
    exact add_mem ihx ihy
  | mul x y hx hy ihx ihy =>
    rw [smul_mul']
    exact mul_mem ihx ihy

private theorem kPole_of_mem_levelRingK {K : IntermediateField ℚ ℂ} [NeZero N] (hK : kN N ≤ K)
    {f : ℍ → ℂ} (hf : f ∈ levelRingK K N) : KPole K N f :=
  kPole_of_mem_adjoin (fun g hg => by
    rcases hg with rfl | ⟨i, rfl⟩
    · exact kPole_j K
    · exact kPole_frickeF hK i) hf

private theorem levelRingK_invariant_eq_polynomial_j {K : IntermediateField ℚ ℂ} [NeZero N]
    (hK : kN N ≤ K) {f : ℍ → ℂ} (hf : f ∈ levelRingK K N)
    (hinv : ∀ γ : SL(2, ℤ), ∀ τ : ℍ, f (γ • τ) = f τ) :
    ∃ P : Polynomial ℂ, (∀ i, P.coeff i ∈ K) ∧ f = fun τ => Polynomial.eval (j τ) P := by
  refine kPole_invariant_eq_polynomial_j_mem (kPole_of_mem_levelRingK hK hf) ?_
  intro γ
  funext τ
  simp only [SL_slash_apply, neg_zero, zpow_zero, mul_one]
  exact hinv γ τ

end LevelRingK

section B6InstanceK

open UpperHalfPlane ModularForm CuspForm ModularForm.CuspForm Polynomial Real.Polynomial
open scoped UpperHalfPlane ModularForm CuspForm ModularForm.CuspForm Polynomial Real.Polynomial
open scoped MatrixGroups Manifold

variable {N : ℕ}

private lemma orbitCoeffOn_frickeF_mem_levelRingK [NeZero N] (s : Finset (FrickeIdx N)) (k : ℕ) :
    (fun τ : ℍ => (∏ i ∈ s, (X - C (frickeF N i.1 τ))).coeff k) ∈ levelRingK (kN N) N := by
  induction s using Finset.cons_induction generalizing k with
  | empty =>
    simp only [Finset.prod_empty, Polynomial.coeff_one]
    cases k with
    | zero => exact one_mem (levelRingK (kN N) N)
    | succ k' => exact zero_mem (levelRingK (kN N) N)
  | cons a s ha ih =>
    cases k with
    | zero =>
      have hrw : (fun τ : ℍ =>
          (∏ i ∈ Finset.cons a s ha, (X - C (frickeF N i.1 τ))).coeff 0) =
          -(frickeF N a.1 * fun τ : ℍ => (∏ i ∈ s, (X - C (frickeF N i.1 τ))).coeff 0) := by
        funext τ
        simp only [Finset.prod_cons, coeff_X_sub_C_mul, ite_true, Pi.neg_apply, Pi.mul_apply]
        ring
      rw [hrw]
      exact neg_mem (mul_mem (frickeF_mem_levelRingK a) (ih 0))
    | succ k' =>
      have hrw : (fun τ : ℍ =>
          (∏ i ∈ Finset.cons a s ha, (X - C (frickeF N i.1 τ))).coeff (k' + 1)) =
          ((fun τ : ℍ => (∏ i ∈ s, (X - C (frickeF N i.1 τ))).coeff k') -
            frickeF N a.1 * fun τ : ℍ =>
              (∏ i ∈ s, (X - C (frickeF N i.1 τ))).coeff (k' + 1)) := by
        funext τ
        simp only [Finset.prod_cons, coeff_X_sub_C_mul, ite_eq_right (Nat.succ_ne_zero k'),
          Nat.add_sub_cancel, Pi.sub_apply, Pi.mul_apply]
      rw [hrw]
      exact sub_mem (ih k') (mul_mem (frickeF_mem_levelRingK a) (ih (k' + 1)))

private theorem frickeF_integral_over_j_mem_kN (N : ℕ) [NeZero N] :
    ∃ P : ℕ → Polynomial ℂ,
      (∀ k i, (P k).coeff i ∈ kN N) ∧
      ∀ (i : FrickeIdx N) (τ : ℍ),
        frickeF N i.1 τ ^ Fintype.card (FrickeIdx N) +
          ∑ k ∈ Finset.range (Fintype.card (FrickeIdx N)),
            Polynomial.eval (j τ) (P k) * frickeF N i.1 τ ^ k = 0 := by
  have hdesc : ∀ k : ℕ, ∃ P : Polynomial ℂ, (∀ i, P.coeff i ∈ kN N) ∧
      orbitCoeff (fun i : FrickeIdx N => frickeF N i.1) k =
        fun τ => Polynomial.eval (j τ) P := by
    intro k
    have hmem : orbitCoeff (fun i : FrickeIdx N => frickeF N i.1) k ∈ levelRingK (kN N) N := by
      have h1 := orbitCoeffOn_frickeF_mem_levelRingK (N := N) Finset.univ k
      simp at h1
      exact h1
    exact kPole_invariant_eq_polynomial_j_mem (kPole_of_mem_levelRingK le_rfl hmem)
      (orbitCoeff_slash_invariant (fun i : FrickeIdx N => frickeF N i.1)
        (fun γ => frickeF_hperm γ) k)
  choose P hPmem hP using hdesc
  refine ⟨P, hPmem, fun i τ => ?_⟩
  set Q : Polynomial ℂ := ∏ i' : FrickeIdx N, (X - C (frickeF N i'.1 τ)) with hQ
  have hQmonic : Q.Monic := monic_prod_of_monic _ _ fun i' _ => monic_X_sub_C _
  have hQdeg : Q.natDegree = Fintype.card (FrickeIdx N) := by
    rw [hQ, natDegree_prod_of_monic _ _ (fun i' _ => monic_X_sub_C _)]
    simp
  have hroot : Polynomial.eval (frickeF N i.1 τ) Q = 0 := by
    rw [hQ, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have hexp := Polynomial.eval_eq_sum_range' (n := Fintype.card (FrickeIdx N) + 1)
    (by rw [hQdeg]; exact Nat.lt_succ_self _) (frickeF N i.1 τ) (p := Q)
  rw [Finset.sum_range_succ] at hexp
  have hlead : Q.coeff (Fintype.card (FrickeIdx N)) = 1 := by
    have h1 := hQmonic.coeff_natDegree
    rwa [hQdeg] at h1
  have hcoeffs : ∀ k, Q.coeff k = Polynomial.eval (j τ) (P k) := by
    intro k
    have h1 := congrFun (hP k) τ
    simpa [orbitCoeff, hQ] using h1
  rw [hroot.symm, hexp, hlead, one_mul, add_comm]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by rw [hcoeffs k]

end B6InstanceK

section R4bBridge

open WLight
open scoped WLight
open UpperHalfPlane hiding I
open scoped Manifold MatrixGroups ModularForm

private lemma periodPair_ext'' {L₁ L₂ : PeriodPair} (h₁ : L₁.ω₁ = L₂.ω₁)
    (h₂ : L₁.ω₂ = L₂.ω₂) : L₁ = L₂ := by
  cases L₁; cases L₂; simp_all

end R4bBridge

open UpperHalfPlane hiding I in
open scoped UpperHalfPlane Manifold MatrixGroups ModularForm in
open _root_.WLight in
theorem _root_.WLight.frickeFunction_orbit_package
    (N : ℕ) [NeZero N]
    (L : ℍ → PeriodPair) (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
    (W : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hW : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), W v τ = ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
      PeriodPair.weierstrassP (L τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)))
    (fricke : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hfricke : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), fricke v τ =
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * W v τ)
    (jf : ℍ → ℂ)
    (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) :

    (MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jf ∧
      ∃ m : ℕ, IsBoundedAtImInfty (jf * ModularForm.discriminant ^ m)) ∧

    (∀ v : Fin 2 → ZMod N, v ≠ 0 → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fricke v) ∧
      ∃ m : ℕ, IsBoundedAtImInfty (fricke v * ModularForm.discriminant ^ m)) ∧

    (∃ P : ℕ → Polynomial ℂ,
      (∀ k i, (P k).coeff i ∈
        IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / N)}) ∧
      ∀ v : Fin 2 → ZMod N, v ≠ 0 → ∀ τ : ℍ,
        fricke v τ ^ (N ^ 2 - 1) + ∑ k ∈ Finset.range (N ^ 2 - 1),
          (P k).eval (jf τ) * fricke v τ ^ k = 0) := by
  have hLpp : ∀ τ : ℍ, L τ = periodPairOfTau τ := fun τ =>
    periodPair_ext'' ((hL τ).1.trans (periodPairOfTau_ω₁ τ).symm)
      ((hL τ).2.trans (periodPairOfTau_ω₂ τ).symm)
  have hfr : ∀ v : Fin 2 → ZMod N, fricke v = frickeF N v := by
    intro v
    funext τ
    rw [hfricke v τ, hW v τ, hLpp τ]
    with_unfolding_all rfl
  have hjeq : jf = j := by
    funext τ
    rw [hjf τ]
    rfl
  have hcard : Fintype.card (FrickeIdx N) = N ^ 2 - 1 := by
    have h1 : Fintype.card (Fin 2 → ZMod N) = N ^ 2 := by
      rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    have h2 : Fintype.card {a : Fin 2 → ZMod N // a = 0} = 1 := Fintype.card_subtype_eq 0
    have h3 := Fintype.card_subtype_compl (fun a : Fin 2 → ZMod N => a = 0)
    rw [h1, h2] at h3
    exact h3
  refine ⟨?_, ?_, ?_⟩
  ·
    obtain ⟨h1, m, h2⟩ := poleBounded_j
    refine ⟨by rw [hjeq]; exact h1, m, ?_⟩
    rw [hjeq, ← CuspForm.coe_discriminant]
    exact h2
  ·
    intro v hv
    obtain ⟨h1, m, h2⟩ := poleBounded_frickeF (⟨v, hv⟩ : FrickeIdx N)
    refine ⟨by rw [hfr]; exact h1, m, ?_⟩
    rw [hfr, ← CuspForm.coe_discriminant]
    exact h2
  ·
    obtain ⟨P, hPmem, hPrel⟩ := frickeF_integral_over_j_mem_kN N
    refine ⟨P, fun k i => hPmem k i, fun v hv τ => ?_⟩
    have h := hPrel ⟨v, hv⟩ τ
    rw [hfr v, hjeq, ← hcard]
    exact h

end WLightFriOrbit

open Complex Real UpperHalfPlane ModularForm Polynomial Real.Polynomial
open scoped Topology Manifold MatrixGroups ModularForm

namespace WLightFriIntBC

namespace R8b

section Furniture

private theorem mdifferentiable_eq_zero_or_eq_zero_of_mul_eq_zero {f g : ℍ → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hfg : f * g = 0) : f = 0 ∨ g = 0 := by
  rw [UpperHalfPlane.mdifferentiable_iff] at hf hg
  have hU : IsOpen {z : ℂ | 0 < z.im} := isOpen_upperHalfPlaneSet
  have key := AnalyticOnNhd.eq_zero_or_eq_zero_of_mul_eq_zero (hf.analyticOnNhd hU)
    (hg.analyticOnNhd hU) (fun z hz ↦ by
      have := congrFun hfg (ofComplex z)
      simpa using this) (convex_halfSpace_im_gt 0).isPreconnected
  rcases key with k | k
  · left; funext τ; simpa [ofComplex_apply] using k (τ : ℂ) τ.im_pos
  · right; funext τ; simpa [ofComplex_apply] using k (τ : ℂ) τ.im_pos

private lemma mdiff_jf {jf : ℍ → ℂ}
    (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jf := by
  have : jf = fun τ => ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ := funext hjf
  rw [this]
  exact (ModularForm.E₄.holo'.pow 3).div CuspForm.discriminant.holo'
    ModularForm.discriminant_ne_zero

private def holSub : Subalgebra ℂ (ℍ → ℂ) where
  carrier := {f | MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f}
  mul_mem' ha hb := ha.mul hb
  add_mem' ha hb := ha.add hb
  algebraMap_mem' _ := mdifferentiable_const

private scoped instance : Nontrivial ↥holSub := ⟨⟨0, 1, fun h => by
  have := congrArg (fun f : ↥holSub => (f : ℍ → ℂ) UpperHalfPlane.I) h
  simp at this⟩⟩

private scoped instance : NoZeroDivisors ↥holSub := ⟨fun {a b} h => by
  rcases mdifferentiable_eq_zero_or_eq_zero_of_mul_eq_zero a.2 b.2 (congrArg Subtype.val h)
    with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)⟩

private scoped instance : IsDomain ↥holSub := NoZeroDivisors.to_isDomain _

private abbrev KK : Type := FractionRing ↥holSub

private abbrev ι : ↥holSub →+* KK := algebraMap ↥holSub KK

private lemma ι_injective : Function.Injective ι := IsFractionRing.injective _ _

private lemma ι_algebraMap (c : ℂ) : ι (algebraMap ℂ ↥holSub c) = algebraMap ℂ KK c :=
  (IsScalarTower.algebraMap_apply ℂ ↥holSub KK c).symm

private lemma adjoin_le_holSub {R : Type*} [CommSemiring R] [Algebra R ℂ] {T : Set (ℍ → ℂ)}
    (hT : T ⊆ holSub) {x : ℍ → ℂ} (hx : x ∈ Algebra.adjoin R T) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) x := by
  induction hx using Algebra.adjoin_induction with
  | mem g hg' => exact hT hg'
  | algebraMap r => exact mdifferentiable_const
  | add x y _ _ hx hy => exact hx.add hy
  | mul x y _ _ hx hy => exact hx.mul hy

end Furniture

section Generators

variable {N : ℕ} (jf : ℍ → ℂ) (fricke : (Fin 2 → ZMod N) → ℍ → ℂ)

private def gen : Option {v : Fin 2 → ZMod N // v ≠ 0} → ℍ → ℂ :=
  fun o => o.elim jf fun v => fricke v.1

private lemma range_gen : Set.range (gen jf fricke) =
    insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v} := by
  ext g
  constructor
  · rintro ⟨o, rfl⟩
    cases o with
    | none => exact Set.mem_insert _ _
    | some v => exact Set.mem_insert_of_mem _ ⟨v.1, v.2, rfl⟩
  · rintro (rfl | ⟨v, hv, rfl⟩)
    · exact ⟨none, rfl⟩
    · exact ⟨some ⟨v, hv⟩, rfl⟩

variable {jf fricke}

private structure GenMD (jf : ℍ → ℂ) (fricke : (Fin 2 → ZMod N) → ℍ → ℂ) : Prop where
  jmd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jf
  fmd : ∀ v : Fin 2 → ZMod N, v ≠ 0 → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fricke v)

private lemma GenMD.mdiff (hg : GenMD jf fricke) (o : Option {v : Fin 2 → ZMod N // v ≠ 0}) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (gen jf fricke o) := by
  cases o with
  | none => exact hg.jmd
  | some v => exact hg.fmd v.1 v.2

private lemma range_gen_subset_holSub (hg : GenMD jf fricke) :
    Set.range (gen jf fricke) ⊆ (holSub : Set (ℍ → ℂ)) := by
  rintro _ ⟨o, rfl⟩; exact hg.mdiff o

private def genH (hg : GenMD jf fricke) (o : Option {v : Fin 2 → ZMod N // v ≠ 0}) : ↥holSub :=
  ⟨gen jf fricke o, hg.mdiff o⟩

private def SK (hg : GenMD jf fricke) : Set KK := Set.range fun o => ι (genH hg o)

private def tK (hg : GenMD jf fricke) : KK := ι (genH hg none)

private lemma tK_mem_SK (hg : GenMD jf fricke) : tK hg ∈ SK hg := ⟨none, rfl⟩

private lemma SK_finite (hg : GenMD jf fricke) [NeZero N] : (SK hg).Finite := Set.finite_range _

end Generators

section Correspondence

variable (F : IntermediateField ℚ ℂ)

private theorem isIntegral_subring_iff (T : Subring KK) (y : KK) :
    IsIntegral ↥T y ↔ ∃ p : KK[X], p.Monic ∧ (∀ n, p.coeff n ∈ T) ∧ p.eval y = 0 := by
  constructor
  · rintro ⟨p, hm, hp⟩
    refine ⟨p.map (algebraMap ↥T KK), hm.map _, fun n ↦ ?_, ?_⟩
    · rw [Polynomial.coeff_map]; exact (p.coeff n).2
    · rwa [Polynomial.eval_map]
  · rintro ⟨p, hm, hc, hp⟩
    have hl : p ∈ Polynomial.lifts (algebraMap ↥T KK) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n; exact ⟨⟨p.coeff n, hc n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl hm
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.eval_map, hq, hp]

private theorem mem_closure_iff_exists_adjoin {T : Set (ℍ → ℂ)} (hT : T ⊆ holSub) (z : KK) :
    z ∈ Subring.closure (⇑(algebraMap ℂ KK) '' (F : Set ℂ) ∪
        (fun f : ↥holSub => ι f) '' {f | (f : ℍ → ℂ) ∈ T}) ↔
      ∃ a : ↥holSub, (a : ℍ → ℂ) ∈ Algebra.adjoin ↥F T ∧ ι a = z := by
  constructor
  · intro hz
    induction hz using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨c, hc, rfl⟩ | ⟨f, hf, rfl⟩
      · refine ⟨algebraMap ℂ ↥holSub c, ?_, ι_algebraMap c⟩
        exact Subalgebra.algebraMap_mem (Algebra.adjoin ↥F T) (⟨c, hc⟩ : ↥F)
      · exact ⟨f, Algebra.subset_adjoin hf, rfl⟩
    | zero => exact ⟨0, Subalgebra.zero_mem _, map_zero ι⟩
    | one => exact ⟨1, Subalgebra.one_mem _, map_one ι⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact ⟨a + b, Subalgebra.add_mem _ ha hb, map_add ι a b⟩
    | neg x _ hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      exact ⟨-a, Subalgebra.neg_mem _ ha, map_neg ι a⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact ⟨a * b, Subalgebra.mul_mem _ ha hb, map_mul ι a b⟩
  · rintro ⟨a, ha, rfl⟩
    suffices h : ∀ (x : ℍ → ℂ), x ∈ Algebra.adjoin ↥F T → ∀ hx : x ∈ holSub,
        ι ⟨x, hx⟩ ∈ Subring.closure (⇑(algebraMap ℂ KK) '' (F : Set ℂ) ∪
          (fun f : ↥holSub => ι f) '' {f | (f : ℍ → ℂ) ∈ T}) from h a ha a.2
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem g hg' => exact fun hx => Subring.subset_closure (Or.inr ⟨⟨g, hx⟩, hg', rfl⟩)
    | algebraMap r =>
      intro hx
      have : (⟨algebraMap ↥F (ℍ → ℂ) r, hx⟩ : ↥holSub) = algebraMap ℂ ↥holSub (r : ℂ) := rfl
      rw [this, ι_algebraMap]
      exact Subring.subset_closure (Or.inl ⟨r, r.2, rfl⟩)
    | add x y hx' hy' ihx ihy =>
      intro hxy
      have hx := adjoin_le_holSub (R := ↥F) hT hx'
      have hy := adjoin_le_holSub (R := ↥F) hT hy'
      have : (⟨x + y, hxy⟩ : ↥holSub) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [this, map_add]
      exact Subring.add_mem _ (ihx hx) (ihy hy)
    | mul x y hx' hy' ihx ihy =>
      intro hxy
      have hx := adjoin_le_holSub (R := ↥F) hT hx'
      have hy := adjoin_le_holSub (R := ↥F) hT hy'
      have : (⟨x * y, hxy⟩ : ↥holSub) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [this, map_mul]
      exact Subring.mul_mem _ (ihx hx) (ihy hy)

variable {N : ℕ} {jf : ℍ → ℂ} {fricke : (Fin 2 → ZMod N) → ℍ → ℂ} (hg : GenMD jf fricke)

private lemma SK_eq :
    SK hg = (fun f : ↥holSub => ι f) '' {f | (f : ℍ → ℂ) ∈ Set.range (gen jf fricke)} := by
  ext z
  constructor
  · rintro ⟨o, rfl⟩; exact ⟨genH hg o, ⟨o, rfl⟩, rfl⟩
  · rintro ⟨f, ⟨o, ho⟩, rfl⟩
    refine ⟨o, ?_⟩
    change ι (genH hg o) = ι f
    congr 1
    exact Subtype.ext ho

private lemma singleton_tK_eq : ({tK hg} : Set KK) =
    (fun f : ↥holSub => ι f) '' {f | (f : ℍ → ℂ) ∈ ({jf} : Set (ℍ → ℂ))} := by
  ext z
  constructor
  · rintro rfl; exact ⟨genH hg none, rfl, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    rw [Set.mem_singleton_iff]
    change ι f = ι (genH hg none)
    congr 1
    exact Subtype.ext hf

private theorem mem_closureS_iff (z : KK) :
    z ∈ Subring.closure (⇑(algebraMap ℂ KK) '' (F : Set ℂ) ∪ SK hg) ↔
      ∃ a : ↥holSub, (a : ℍ → ℂ) ∈ Algebra.adjoin ↥F (Set.range (gen jf fricke)) ∧ ι a = z := by
  rw [SK_eq, mem_closure_iff_exists_adjoin F (range_gen_subset_holSub hg)]

private theorem mem_closureT_iff (z : KK) :
    z ∈ Subring.closure (⇑(algebraMap ℂ KK) '' (F : Set ℂ) ∪ {tK hg}) ↔
      ∃ a : ↥holSub, (a : ℍ → ℂ) ∈ Algebra.adjoin ↥F ({jf} : Set (ℍ → ℂ)) ∧ ι a = z := by
  rw [singleton_tK_eq, mem_closure_iff_exists_adjoin F (by rintro _ rfl; exact hg.jmd)]

end Correspondence

section QKit

open Filter Function

variable {N : ℕ}

private lemma isBoundedAtImInfty_discriminant : IsBoundedAtImInfty (⇑CuspForm.discriminant : ℍ → ℂ) :=
  (CuspFormClass.zero_at_infty CuspForm.discriminant).boundedAtFilter

private lemma isBoundedAtImInfty_discPow (n : ℕ) :
    IsBoundedAtImInfty (⇑CuspForm.discriminant ^ n : ℍ → ℂ) := by
  induction n with
  | zero => exact pow_zero (⇑CuspForm.discriminant : ℍ → ℂ) ▸ Filter.const_boundedAtFilter _ (1 : ℂ)
  | succ k ih =>
    rw [pow_succ]
    exact ih.mul isBoundedAtImInfty_discriminant

private lemma IsBoundedAtImInfty.mul_discPow_mono {f : ℍ → ℂ} {m m' : ℕ} (hm : m ≤ m')
    (h : IsBoundedAtImInfty (f * ⇑CuspForm.discriminant ^ m)) :
    IsBoundedAtImInfty (f * ⇑CuspForm.discriminant ^ m') := by
  have hshape : (f * ⇑CuspForm.discriminant ^ m' : ℍ → ℂ) =
      (f * ⇑CuspForm.discriminant ^ m) * ⇑CuspForm.discriminant ^ (m' - m) := by
    funext τ
    simp only [Pi.mul_apply, Pi.pow_apply]
    rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hm]
  rw [hshape]
  exact h.mul (isBoundedAtImInfty_discPow (m' - m))

private def discPowForm (m : ℕ) : ModularForm 𝒮ℒ (12 * m) :=
  ModularForm.mcast (by ring) ((CuspForm.toModularFormₗ CuspForm.discriminant).pow m)

private lemma discPowForm_coe (m : ℕ) : ⇑(discPowForm m) = ⇑CuspForm.discriminant ^ m := by
  funext z
  simp [discPowForm, ModularForm.coe_mcast, ModularForm.coe_pow,
    CuspForm.toModularFormₗ_apply]

private lemma periodic_one_fn (c : ℝ) : Function.Periodic ((1 : ℍ → ℂ) ∘ ofComplex) c := fun _ => rfl

private lemma periodic_discPow_comp_ofComplex (k : ℕ) (N : ℕ) :
    Function.Periodic ((⇑CuspForm.discriminant ^ k : ℍ → ℂ) ∘ ofComplex) N := by
  have h1 : Function.Periodic (⇑CuspForm.discriminant ∘ ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant
      one_mem_strictPeriods_SL
  have hk : Function.Periodic ((⇑CuspForm.discriminant ^ k : ℍ → ℂ) ∘ ofComplex) 1 := by
    induction k with
    | zero => exact periodic_one_fn 1
    | succ k ih =>
      intro x
      have hx := (ih.mul h1) x
      simp only [Function.comp_apply, Pi.mul_apply, Pi.pow_apply] at hx ⊢
      rw [pow_succ, pow_succ]
      exact hx
  simpa using hk.nat_mul N

private lemma mdiff_discPow (k : ℕ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑CuspForm.discriminant ^ k : ℍ → ℂ) := by
  rw [← discPowForm_coe]
  exact (discPowForm k).holo'

private lemma mdiff_mul_discPow {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (m : ℕ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f * ⇑CuspForm.discriminant ^ m : ℍ → ℂ) :=
  hf.mul (mdiff_discPow m)

private lemma analyticAt_cuspFunction_zero_of [NeZero N] {g : ℍ → ℂ}
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hper : Function.Periodic (g ∘ ofComplex) N) (hbd : IsBoundedAtImInfty g) :
    AnalyticAt ℂ (cuspFunction N g) 0 :=
  analyticAt_cuspFunction_zero
    (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)) hper hhol hbd

private lemma qExpansion_one_discPowForm (k : ℕ) :
    qExpansion 1 (discPowForm k) = (qExpansion 1 ModularForm.discriminant) ^ k := by
  rw [discPowForm, ModularForm.qExpansion_mcast,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  have hco : (⇑(CuspForm.toModularFormₗ CuspForm.discriminant) : ℍ → ℂ) =
      ModularForm.discriminant := by
    funext z
    rw [CuspForm.toModularFormₗ_apply]
    exact congrFun CuspForm.coe_discriminant z
  rw [hco]

private lemma qExpansion_one_discPow (k : ℕ) :
    qExpansion 1 (⇑CuspForm.discriminant ^ k : ℍ → ℂ) =
      (qExpansion 1 ModularForm.discriminant) ^ k := by
  rw [← discPowForm_coe]
  exact qExpansion_one_discPowForm k

private lemma qParam_one_eq_pow {N : ℕ} (hN : N ≠ 0) (τ : ℂ) :
    Function.Periodic.qParam 1 τ = Function.Periodic.qParam N τ ^ N := by
  have : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one, Complex.ofReal_natCast]
  rw [← Complex.exp_nat_mul]
  congr 1
  field_simp

private theorem qExpansion_coeff_width (f : ℍ → ℂ) {N : ℕ} (hN : N ≠ 0)
    (hper : Function.Periodic (f ∘ ofComplex) 1) (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbd : IsBoundedAtImInfty f) (n : ℕ) :
    (qExpansion N f).coeff n =
      if N ∣ n then (qExpansion 1 f).coeff (n / N) else 0 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hperN : Function.Periodic (f ∘ ofComplex) N := by
    simpa using hper.nat_mul N
  let f' : C(ℍ, ℂ) := ⟨f, hhol.continuous⟩
  have hfan : AnalyticAt ℂ (cuspFunction N f') 0 :=
    analyticAt_cuspFunction_zero hN' hperN hhol hbd
  set c : ℕ → ℂ := fun n ↦ if N ∣ n then (qExpansion 1 f).coeff (n / N) else 0 with hc
  have hf : ∀ τ : ℍ, HasSum (fun m ↦ c m • Function.Periodic.qParam N τ ^ m) (f' τ) := by
    intro τ
    have h1 := hasSum_qExpansion one_pos hper hhol hbd τ
    have hinj : Function.Injective fun m : ℕ ↦ N * m := fun a b h ↦ by
      simpa [Nat.mul_right_inj hN] using h
    refine (hinj.hasSum_iff (f := fun m ↦ c m • Function.Periodic.qParam N τ ^ m) ?_).mp ?_
    · intro x hx
      have : ¬ N ∣ x := fun ⟨k, hk⟩ ↦ hx ⟨k, hk.symm⟩
      simp [hc, this]
    · refine h1.congr_fun fun m ↦ ?_
      simp only [Function.comp_apply, hc, Nat.dvd_mul_right, ite_true,
        Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hN), qParam_one_eq_pow hN, ← pow_mul]
  exact (qExpansion_coeff_unique f' hN' hfan hf n).symm

end QKit

section RatCoeff

open UpperHalfPlane ModularForm SlashInvariantForm ModularFormClass CuspForm ModularForm.CuspForm EisensteinSeries
open scoped UpperHalfPlane ModularForm SlashInvariantForm ModularFormClass CuspForm ModularForm.CuspForm EisensteinSeries
open scoped MatrixGroups ArithmeticFunction.sigma

private lemma ratCoeff_mul {p q : PowerSeries ℂ}
    (hp : ∀ n : ℕ, ∃ a : ℚ, p.coeff n = (a : ℂ)) (hq : ∀ n : ℕ, ∃ a : ℚ, q.coeff n = (a : ℂ)) :
    ∀ n : ℕ, ∃ a : ℚ, (p * q).coeff n = (a : ℂ) := by
  choose F hF using hp
  choose G hG using hq
  intro n
  refine ⟨∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, F ij.1 * G ij.2, ?_⟩
  rw [PowerSeries.coeff_mul]
  push_cast
  exact Finset.sum_congr rfl fun ij _ => by rw [hF, hG]

private lemma ratCoeff_sub {p q : PowerSeries ℂ}
    (hp : ∀ n : ℕ, ∃ a : ℚ, p.coeff n = (a : ℂ)) (hq : ∀ n : ℕ, ∃ a : ℚ, q.coeff n = (a : ℂ)) :
    ∀ n : ℕ, ∃ a : ℚ, (p - q).coeff n = (a : ℂ) := by
  intro n
  obtain ⟨a, ha⟩ := hp n
  obtain ⟨b, hb⟩ := hq n
  exact ⟨a - b, by rw [map_sub, ha, hb]; push_cast; ring⟩

private lemma ratCoeff_E {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) :
    ∀ n : ℕ, ∃ q : ℚ, (qExpansion 1 (E hk)).coeff n = (q : ℂ) := by
  intro n
  rw [EisensteinSeries.E_qExpansion_coeff hk hk2]
  by_cases hn : n = 0
  · exact ⟨1, by simp [hn]⟩
  · refine ⟨-(2 * k / _root_.bernoulli k) * (σ (k - 1) n : ℚ), ?_⟩
    rw [ite_eq_right hn]
    push_cast
    ring

private lemma ratCoeff_pow {p : PowerSeries ℂ}
    (hp : ∀ n : ℕ, ∃ a : ℚ, p.coeff n = (a : ℂ)) (k : ℕ) :
    ∀ n : ℕ, ∃ a : ℚ, (p ^ k).coeff n = (a : ℂ) := by
  induction k with
  | zero =>
    intro n
    rw [pow_zero]
    by_cases hn : n = 0
    · exact ⟨1, by simp [hn, PowerSeries.coeff_one]⟩
    · exact ⟨0, by simp [PowerSeries.coeff_one, hn]⟩
  | succ k ih =>
    rw [pow_succ]
    exact ratCoeff_mul ih hp

private def eCubeSubESq : ModularForm 𝒮ℒ 12 :=
  ModularForm.mcast (by decide) (E₄.pow 3) - ModularForm.mcast (by decide) (E₆.pow 2)

private lemma eCubeSubESq_qExpansion :
    qExpansion 1 eCubeSubESq = qExpansion 1 E₄ * qExpansion 1 E₄ * qExpansion 1 E₄ -
      qExpansion 1 E₆ * qExpansion 1 E₆ := by
  simp only [eCubeSubESq, FunLike.coe_sub, ModularForm.coe_mcast,
    ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  ring

private lemma discriminant_eq_smul_eCubeSubESq :
    ModularForm.discriminant = (1 / 1728 : ℂ) • eCubeSubESq := by
  ext z
  have h := discriminant_eq_E₄_cube_sub_E₆_sq z
  simp only [Pi.smul_apply, eCubeSubESq, FunLike.coe_sub, Pi.sub_apply,
    ModularForm.coe_mcast, ModularForm.coe_pow, Pi.pow_apply, smul_eq_mul]
  rw [h]
  ring

private lemma ratCoeff_discriminant :
    ∀ n : ℕ, ∃ q : ℚ, (qExpansion 1 ModularForm.discriminant).coeff n = (q : ℂ) := by
  have h4 : ∀ n : ℕ, ∃ q : ℚ, (qExpansion 1 E₄).coeff n = (q : ℂ) :=
    ratCoeff_E (by norm_num) (by decide)
  have h6 : ∀ n : ℕ, ∃ q : ℚ, (qExpansion 1 E₆).coeff n = (q : ℂ) :=
    ratCoeff_E (by norm_num) (by decide)
  have hmain := ratCoeff_sub (ratCoeff_mul (ratCoeff_mul h4 h4) h4) (ratCoeff_mul h6 h6)
  intro n
  obtain ⟨a, ha⟩ := hmain n
  refine ⟨(1 / 1728 : ℚ) * a, ?_⟩
  rw [discriminant_eq_smul_eCubeSubESq,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
    PowerSeries.coeff_smul, eCubeSubESq_qExpansion, smul_eq_mul, ha]
  push_cast
  ring

end RatCoeff

section KPoleAlgebra

open ModularForm

variable {N : ℕ}

private lemma mem_of_rat (K : IntermediateField ℚ ℂ) {x : ℂ} (h : ∃ q : ℚ, x = (q : ℂ)) : x ∈ K := by
  obtain ⟨q, rfl⟩ := h
  exact SubfieldClass.ratCast_mem K q

private def KPoleAt (K : IntermediateField ℚ ℂ) (N m : ℕ) (f : ℍ → ℂ) : Prop :=
  Function.Periodic ((f * ⇑CuspForm.discriminant ^ m) ∘ ofComplex) N ∧
    IsBoundedAtImInfty (f * ⇑CuspForm.discriminant ^ m) ∧
    ∀ n : ℕ, (qExpansion N (f * ⇑CuspForm.discriminant ^ m)).coeff n ∈ K

private lemma qExpansion_discPow_coeff_mem (K : IntermediateField ℚ ℂ) [NeZero N] (k n : ℕ) :
    (qExpansion N (⇑CuspForm.discriminant ^ k : ℍ → ℂ)).coeff n ∈ K := by
  have hper : Function.Periodic
      ((⇑CuspForm.discriminant ^ k : ℍ → ℂ) ∘ ofComplex) (1 : ℂ) := by
    have h := periodic_discPow_comp_ofComplex k 1
    simpa only [Nat.cast_one] using h
  rw [qExpansion_coeff_width _ (NeZero.ne N) hper (mdiff_discPow k)
    (isBoundedAtImInfty_discPow k), qExpansion_one_discPow]
  split
  · exact mem_of_rat K (ratCoeff_pow ratCoeff_discriminant k _)
  · exact zero_mem _

private lemma KPoleAt.pad {K : IntermediateField ℚ ℂ} [NeZero N] {f : ℍ → ℂ} {m m' : ℕ}
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hm : m ≤ m') (h : KPoleAt K N m f) :
    KPoleAt K N m' f := by
  obtain ⟨hper, hbd, hmem⟩ := h
  have hshape : (f * ⇑CuspForm.discriminant ^ m' : ℍ → ℂ) =
      (f * ⇑CuspForm.discriminant ^ m) * ⇑CuspForm.discriminant ^ (m' - m) := by
    funext τ
    simp only [Pi.mul_apply, Pi.pow_apply]
    rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hm]
  refine ⟨?_, ?_, ?_⟩
  · rw [hshape]
    exact hper.mul (periodic_discPow_comp_ofComplex (m' - m) N)
  · exact IsBoundedAtImInfty.mul_discPow_mono hm hbd
  · intro n
    rw [hshape, qExpansion_mul
      (analyticAt_cuspFunction_zero_of (mdiff_mul_discPow hhol m) hper hbd)
      (analyticAt_cuspFunction_zero_of (mdiff_discPow (m' - m))
        (periodic_discPow_comp_ofComplex (m' - m) N) (isBoundedAtImInfty_discPow (m' - m))),
      PowerSeries.coeff_mul]
    exact sum_mem fun ij _ => mul_mem (hmem ij.1) (qExpansion_discPow_coeff_mem K _ ij.2)

end KPoleAlgebra

private def KPole (K : IntermediateField ℚ ℂ) (N : ℕ) (f : ℍ → ℂ) : Prop :=
  MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ∧ ∃ m, KPoleAt K N m f

section KPoleAlgebra2

open Filter Function

variable {N : ℕ}

private lemma kPole_algebraMap {K : IntermediateField ℚ ℂ} [NeZero N] (c : ↥K) :
    KPole K N (algebraMap ↥K (ℍ → ℂ) c) := by
  have hshape : ((algebraMap ↥K (ℍ → ℂ) c) * ⇑CuspForm.discriminant ^ 0 : ℍ → ℂ) =
      (c : ℂ) • (1 : ℍ → ℂ) := by
    funext τ
    simp only [Pi.mul_apply, pow_zero, mul_one, Pi.smul_apply, Pi.one_apply,
      smul_eq_mul]
    rfl
  have hone_bd : IsBoundedAtImInfty (1 : ℍ → ℂ) := by
    have h1 : (1 : ℍ → ℂ) = fun _ : ℍ => (1 : ℂ) := rfl
    rw [h1]
    exact Filter.const_boundedAtFilter _ _
  refine ⟨mdifferentiable_const, 0, ?_, ?_, ?_⟩
  · rw [hshape]
    intro x
    rfl
  · rw [hshape]
    have hc : ((c : ℂ) • (1 : ℍ → ℂ)) = fun _ : ℍ => (c : ℂ) := by
      funext τ
      simp
    rw [hc]
    exact Filter.const_boundedAtFilter _ _
  · intro n
    have han : AnalyticAt ℂ (cuspFunction N (1 : ℍ → ℂ)) 0 :=
      analyticAt_cuspFunction_zero_of (g := (1 : ℍ → ℂ)) mdifferentiable_const
        (periodic_one_fn N) hone_bd
    rw [hshape, qExpansion_smul han,
      qExpansion_one, PowerSeries.coeff_smul, smul_eq_mul, PowerSeries.coeff_one]
    split
    · rw [mul_one]
      exact c.2
    · rw [mul_zero]
      exact zero_mem _

private lemma KPole.add {K : IntermediateField ℚ ℂ} [NeZero N] {f g : ℍ → ℂ}
    (hf : KPole K N f) (hg : KPole K N g) : KPole K N (f + g) := by
  obtain ⟨hf1, m1, hfd⟩ := hf
  obtain ⟨hg1, m2, hgd⟩ := hg
  obtain ⟨hfper, hfbd, hfmem⟩ := hfd.pad hf1 (le_max_left m1 m2)
  obtain ⟨hgper, hgbd, hgmem⟩ := hgd.pad hg1 (le_max_right m1 m2)
  have hshape : ((f + g) * ⇑CuspForm.discriminant ^ max m1 m2 : ℍ → ℂ) =
      f * ⇑CuspForm.discriminant ^ max m1 m2 + g * ⇑CuspForm.discriminant ^ max m1 m2 := by
    funext τ
    simp [add_mul]
  refine ⟨hf1.add hg1, max m1 m2, ?_, ?_, ?_⟩
  · rw [hshape]
    exact hfper.add hgper
  · rw [hshape]
    exact hfbd.add hgbd
  · intro n
    rw [hshape, qExpansion_add
      (analyticAt_cuspFunction_zero_of (mdiff_mul_discPow hf1 _) hfper hfbd)
      (analyticAt_cuspFunction_zero_of (mdiff_mul_discPow hg1 _) hgper hgbd),
      map_add]
    exact add_mem (hfmem n) (hgmem n)

private lemma KPole.mul {K : IntermediateField ℚ ℂ} [NeZero N] {f g : ℍ → ℂ}
    (hf : KPole K N f) (hg : KPole K N g) : KPole K N (f * g) := by
  obtain ⟨hf1, m1, hfper, hfbd, hfmem⟩ := hf
  obtain ⟨hg1, m2, hgper, hgbd, hgmem⟩ := hg
  have hshape : ((f * g) * ⇑CuspForm.discriminant ^ (m1 + m2) : ℍ → ℂ) =
      (f * ⇑CuspForm.discriminant ^ m1) * (g * ⇑CuspForm.discriminant ^ m2) := by
    funext τ
    simp only [Pi.mul_apply, Pi.pow_apply, pow_add]
    ring
  refine ⟨hf1.mul hg1, m1 + m2, ?_, ?_, ?_⟩
  · rw [hshape]
    exact hfper.mul hgper
  · rw [hshape]
    exact hfbd.mul hgbd
  · intro n
    rw [hshape, qExpansion_mul
      (analyticAt_cuspFunction_zero_of (mdiff_mul_discPow hf1 _) hfper hfbd)
      (analyticAt_cuspFunction_zero_of (mdiff_mul_discPow hg1 _) hgper hgbd),
      PowerSeries.coeff_mul]
    exact sum_mem fun ij _ => mul_mem (hfmem ij.1) (hgmem ij.2)

private lemma kPole_jf (K : IntermediateField ℚ ℂ) [NeZero N] {jf : ℍ → ℂ}
    (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) :
    KPole K N jf := by
  have hshape : (jf * ⇑CuspForm.discriminant ^ 1 : ℍ → ℂ) = ⇑(ModularForm.E₄.pow 3) := by
    funext τ
    rw [congrFun (ModularForm.coe_pow ModularForm.E₄ 3) τ, Pi.pow_apply]
    simp only [Pi.mul_apply, pow_one, hjf τ]
    rw [congrFun CuspForm.coe_discriminant τ]
    exact div_mul_cancel₀ _ (ModularForm.discriminant_ne_zero τ)
  have hhol3 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑(ModularForm.E₄.pow 3) : ℍ → ℂ) :=
    (ModularForm.E₄.pow 3).holo'
  have hbd3 : IsBoundedAtImInfty (⇑(ModularForm.E₄.pow 3) : ℍ → ℂ) :=
    ModularFormClass.bdd_at_infty (ModularForm.E₄.pow 3)
  have hper3 : Function.Periodic ((⇑(ModularForm.E₄.pow 3) : ℍ → ℂ) ∘ ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex (ModularForm.E₄.pow 3)
      one_mem_strictPeriods_SL
  have hjmd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jf := by
    have : jf = fun τ => ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ := funext hjf
    rw [this]
    exact (ModularForm.E₄.holo'.pow 3).div CuspForm.discriminant.holo'
      ModularForm.discriminant_ne_zero
  refine ⟨hjmd, 1, ?_, ?_, ?_⟩
  · rw [hshape]
    simpa using hper3.nat_mul N
  · rw [hshape]
    exact hbd3
  · intro n
    rw [hshape, qExpansion_coeff_width (⇑(ModularForm.E₄.pow 3) : ℍ → ℂ) (NeZero.ne N)
      hper3 hhol3 hbd3]
    split
    · have he : qExpansion 1 (⇑(ModularForm.E₄.pow 3) : ℍ → ℂ) =
          (qExpansion 1 ModularForm.E₄) ^ 3 :=
        ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL ModularForm.E₄ 3
      rw [he]
      exact mem_of_rat K (ratCoeff_pow (ratCoeff_E (by norm_num) (by decide)) 3 _)
    · exact zero_mem _

private lemma kPole_of_mem_adjoin {K : IntermediateField ℚ ℂ} [NeZero N] {T : Set (ℍ → ℂ)}
    (hT : ∀ g ∈ T, KPole K N g) {x : ℍ → ℂ} (hx : x ∈ Algebra.adjoin ↥K T) : KPole K N x := by
  induction hx using Algebra.adjoin_induction with
  | mem g hg' => exact hT g hg'
  | algebraMap r => exact kPole_algebraMap r
  | add x y _ _ hx hy => exact hx.add hy
  | mul x y _ _ hx hy => exact hx.mul hy

end KPoleAlgebra2

section Engine

open Filter Function

variable {N : ℕ} [NeZero N] {K : IntermediateField ℚ ℂ} {jf : ℍ → ℂ}
  {fricke : (Fin 2 → ZMod N) → ℍ → ℂ}

omit [NeZero N] in
private lemma KPoleAt.mono {F : IntermediateField ℚ ℂ} (h : K ≤ F) {m : ℕ} {f : ℍ → ℂ}
    (hf : KPoleAt K N m f) : KPoleAt F N m f :=
  ⟨hf.1, hf.2.1, fun n => h (hf.2.2 n)⟩

private lemma kPole_of_mem_adjoinF (hg : GenMD jf fricke)
    (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
    (hkp : ∀ v : Fin 2 → ZMod N, v ≠ 0 → KPoleAt K N 1 (fricke v))
    {F : IntermediateField ℚ ℂ} (hKF : K ≤ F) {x : ℍ → ℂ}
    (hx : x ∈ Algebra.adjoin ↥F (Set.range (gen jf fricke))) : KPole F N x := by
  refine kPole_of_mem_adjoin (fun g hg' => ?_) hx
  obtain ⟨o, rfl⟩ := hg'
  cases o with
  | none => exact kPole_jf F hjf
  | some v => exact ⟨hg.fmd v.1 v.2, 1, (hkp v.1 v.2).mono hKF⟩

omit [NeZero N] in
private lemma qExpansion_sum_smul {h : ℝ} {ι : Type} [Fintype ι] (c : ι → ℂ) (g : ι → ℍ → ℂ)
    (hg' : ∀ i, AnalyticAt ℂ (cuspFunction h (g i)) 0) (n : ℕ) :
    (qExpansion h (∑ i, c i • g i)).coeff n = ∑ i, c i * (qExpansion h (g i)).coeff n := by
  classical
  have key : ∀ s : Finset ι, AnalyticAt ℂ (cuspFunction h (∑ i ∈ s, c i • g i)) 0 ∧
      (qExpansion h (∑ i ∈ s, c i • g i)).coeff n = ∑ i ∈ s, c i * (qExpansion h (g i)).coeff n := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨?_, ?_⟩
      · simp only [Finset.sum_empty]
        rw [show cuspFunction h (0 : ℍ → ℂ) = 0 from by
          simp [cuspFunction, Periodic.cuspFunction]
          exact (tendsto_const_nhds.mono_left nhdsWithin_le_nhds).limUnder_eq]
        exact analyticAt_const
      · simp [qExpansion_zero]
    | insert a s ha ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have hsm : AnalyticAt ℂ (cuspFunction h (c a • g a)) 0 := by
        rw [cuspFunction_smul (hg' a).continuousAt]
        exact (hg' a).const_smul
      rw [Finset.sum_insert ha]
      refine ⟨?_, ?_⟩
      · rw [cuspFunction_add hsm.continuousAt ih1.continuousAt]
        exact hsm.add ih1
      · rw [qExpansion_add hsm ih1, map_add, ih2, qExpansion_smul (hg' a), Finset.sum_insert ha]
        simp
  exact (key Finset.univ).2

omit [NeZero N] in
private lemma periodic_of_kPoleAt {e : ℍ → ℂ} {m : ℕ} (h : KPoleAt K N m e) :
    Function.Periodic (e ∘ UpperHalfPlane.ofComplex) N := by
  intro w
  have h1 := h.1 w
  have h2 := periodic_discPow_comp_ofComplex m N w
  simp only [Function.comp_apply, Pi.mul_apply, Pi.pow_apply] at h1 h2 ⊢
  rw [h2] at h1
  exact mul_right_cancel₀ (pow_ne_zero m (by
    rw [CuspForm.coe_discriminant]; exact ModularForm.discriminant_ne_zero _)) h1

omit [NeZero N] in
private lemma combo_props {ι : Type} [Fintype ι] (c : ι → ℂ) (e : ι → ℍ → ℂ)
    {m : ℕ} (hm : ∀ i, KPoleAt K N m (e i)) :
    Function.Periodic ((∑ i, c i • e i) ∘ UpperHalfPlane.ofComplex) N ∧
      IsBoundedAtImInfty ((∑ i, c i • e i) * ⇑CuspForm.discriminant ^ m) ∧
      ((∑ i, c i • e i) * ⇑CuspForm.discriminant ^ m : ℍ → ℂ) =
        ∑ i, c i • (e i * ⇑CuspForm.discriminant ^ m) := by
  classical
  have hshape : ((∑ i, c i • e i) * ⇑CuspForm.discriminant ^ m : ℍ → ℂ) =
      ∑ i, c i • (e i * ⇑CuspForm.discriminant ^ m) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc]
  refine ⟨?_, ?_, hshape⟩
  · intro w
    simp only [Function.comp_apply, Finset.sum_apply, Pi.smul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show e i (UpperHalfPlane.ofComplex (w + N)) = e i (UpperHalfPlane.ofComplex w) from
      periodic_of_kPoleAt (hm i) w]
  · rw [hshape]
    have : ∀ s : Finset ι, IsBoundedAtImInfty (∑ i ∈ s, c i • (e i * ⇑CuspForm.discriminant ^ m)) := by
      intro s
      induction s using Finset.induction_on with
      | empty => (have h__af := (Filter.const_boundedAtFilter atImInfty (0 : ℂ)); simp at h__af; exact h__af)
      | insert a s ha ih =>
        rw [Finset.sum_insert ha]
        exact ((hm a).2.1.const_smul_left (c a)).add ih
    exact this Finset.univ

private theorem eq_zero_of_const_relation (hg : GenMD jf fricke)
    (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
    (hkp : ∀ v : Fin 2 → ZMod N, v ≠ 0 → KPoleAt K N 1 (fricke v))
    {F : IntermediateField ℚ ℂ} (hKF : K ≤ F) {c : ℂ} (hc : Transcendental ↥F c) {d : ℕ}
    (a : Fin d → ℍ → ℂ) (ha : ∀ i, a i ∈ Algebra.adjoin ↥F (Set.range (gen jf fricke)))
    (hrel : ∑ i : Fin d, c ^ (i : ℕ) • a i = 0) : ∀ i, a i = 0 := by
  classical
  have hdata := fun i => kPole_of_mem_adjoinF hg hjf hkp hKF (ha i)
  choose hhol m hm using hdata
  obtain ⟨M, hpad⟩ : ∃ M, ∀ i, KPoleAt F N M (a i) :=
    ⟨Finset.univ.sup m, fun i => (hm i).pad (hhol i) (Finset.le_sup (Finset.mem_univ i))⟩
  obtain ⟨hper, hbd, hshape⟩ := combo_props (fun i : Fin d => c ^ (i : ℕ)) a hpad
  have han : ∀ i, AnalyticAt ℂ (cuspFunction N (a i * ⇑CuspForm.discriminant ^ M)) 0 := fun i =>
    analyticAt_cuspFunction_zero_of (mdiff_mul_discPow (hhol i) M) (hpad i).1 (hpad i).2.1

  have hrow : ∀ n : ℕ, ∑ i : Fin d, c ^ (i : ℕ) *
      (qExpansion N (a i * ⇑CuspForm.discriminant ^ M)).coeff n = 0 := by
    intro n
    rw [← qExpansion_sum_smul _ _ han, ← hshape, hrel, zero_mul, qExpansion_zero, map_zero]

  have hcoeff0 : ∀ (i : Fin d) (n : ℕ), (qExpansion N (a i * ⇑CuspForm.discriminant ^ M)).coeff n = 0 := by
    intro i n
    set z : Fin d → ↥F := fun i' => ⟨(qExpansion N (a i' * ⇑CuspForm.discriminant ^ M)).coeff n,
      (hpad i').2.2 n⟩ with hz
    set P : Polynomial ↥F := ∑ i', C (z i') * X ^ (i' : ℕ) with hP
    have haeval : aeval c P = 0 := by
      rw [hP, map_sum, ← hrow n]
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [map_mul, aeval_C, map_pow, aeval_X, mul_comm]
      rfl
    have hP0 : P = 0 := (transcendental_iff.mp hc) P haeval
    have hcoeffP : P.coeff (i : ℕ) = z i := by
      rw [hP, Polynomial.finsetSum_coeff, Finset.sum_eq_single i]
      · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, ite_eq_left rfl, mul_one]
      · intro i' _ hne
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, ite_eq_right (fun h => hne (Fin.ext h).symm),
          mul_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
    have hzi : z i = 0 := by rw [← hcoeffP, hP0, Polynomial.coeff_zero]
    exact congrArg Subtype.val hzi
  intro i
  have hgz : a i * ⇑CuspForm.discriminant ^ M = 0 := by
    rw [← qExpansion_eq_zero_iff (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N)))
      (hpad i).1 (mdiff_mul_discPow (hhol i) M) (hpad i).2.1]
    ext n
    rw [hcoeff0 i n, map_zero]
  funext τ
  have hτ := congrFun hgz τ
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.zero_apply, mul_eq_zero] at hτ
  exact hτ.resolve_right (pow_ne_zero _ (by
    rw [CuspForm.coe_discriminant]; exact ModularForm.discriminant_ne_zero τ))

private theorem transcendental_closureS (hg : GenMD jf fricke)
    (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
    (hkp : ∀ v : Fin 2 → ZMod N, v ≠ 0 → KPoleAt K N 1 (fricke v))
    {F : IntermediateField ℚ ℂ} (hKF : K ≤ F) {c : ℂ} (hc : Transcendental ↥F c) :
    Transcendental ↥(Subfield.closure (⇑(algebraMap ℂ KK) '' (F : Set ℂ) ∪ SK hg))
      (algebraMap ℂ KK c) := by
  classical
  set gS : Set KK := ⇑(algebraMap ℂ KK) '' (F : Set ℂ) ∪ SK hg with hgS
  rw [transcendental_iff]
  intro p hpe
  by_contra hp0
  set d : ℕ := p.natDegree + 1 with hd

  have hy : ∀ i : Fin d, ∃ u ∈ Subring.closure gS, ∃ w ∈ Subring.closure gS,
      w ≠ 0 ∧ u / w = ((p.coeff i : ↥(Subfield.closure gS)) : KK) := by
    intro i
    obtain ⟨u, hu, w, hw, huw⟩ := Subfield.mem_closure_iff.mp (p.coeff (i : ℕ)).2
    by_cases hw0 : w = 0
    · refine ⟨0, Subring.zero_mem _, 1, Subring.one_mem _, one_ne_zero, ?_⟩
      rw [← huw, hw0, div_zero, zero_div]
    · exact ⟨u, hu, w, hw, hw0, huw⟩
  choose u hu w hw hw0 huw using hy
  set W : KK := ∏ i, w i with hW
  have hW0 : W ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hw0 i
  set A : Fin d → KK := fun i => u i * ∏ j ∈ Finset.univ.erase i, w j with hA
  have hAmem : ∀ i, A i ∈ Subring.closure gS := fun i =>
    Subring.mul_mem _ (hu i) (Subring.prod_mem _ fun j _ => hw j)
  have hAW : ∀ i, A i = ((p.coeff i : ↥(Subfield.closure gS)) : KK) * W := by
    intro i
    have hwi := hw0 i
    rw [← huw i, hW, ← Finset.mul_prod_erase Finset.univ w (Finset.mem_univ i)]
    simp only [hA]
    field_simp

  have hrel : ∑ i : Fin d, A i * algebraMap ℂ KK c ^ (i : ℕ) = 0 := by
    have h1 : (aeval (algebraMap ℂ KK c) p : KK) = 0 := hpe
    rw [Polynomial.aeval_eq_sum_range, Finset.sum_range] at h1
    have h2 : ∑ i : Fin d, A i * algebraMap ℂ KK c ^ (i : ℕ) =
        W * ∑ i : Fin d, p.coeff (i : ℕ) • algebraMap ℂ KK c ^ (i : ℕ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hAW, Algebra.smul_def,
        show algebraMap (↥(Subfield.closure gS)) KK (p.coeff i) = (p.coeff i : KK) from rfl]
      ring
    rw [h2, h1, mul_zero]

  choose aH haH hιa using fun i => (mem_closureS_iff F hg (A i)).mp (hAmem i)
  have hrelH : ∑ i : Fin d, (algebraMap ℂ ↥holSub c) ^ (i : ℕ) * aH i = 0 := by
    apply ι_injective
    rw [map_sum, map_zero, ← hrel]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, ι_algebraMap, hιa, mul_comm]
  have hrelF : ∑ i : Fin d, c ^ (i : ℕ) • (aH i : ℍ → ℂ) = 0 := by
    have h := congrArg (fun f : ↥holSub => (f : ℍ → ℂ)) hrelH
    simp only [ZeroMemClass.coe_zero, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul,
      SubmonoidClass.coe_pow] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    funext τ
    simp only [Pi.smul_apply, Pi.mul_apply, Pi.pow_apply, smul_eq_mul]
    rfl
  have hall := eq_zero_of_const_relation hg hjf hkp hKF hc (fun i => (aH i : ℍ → ℂ)) haH hrelF

  have hcoef : ∀ i : Fin d, p.coeff (i : ℕ) = 0 := by
    intro i
    have hA0 : A i = 0 := by
      rw [← hιa i, show aH i = 0 from Subtype.ext (hall i), map_zero]
    have hc0 : ((p.coeff i : ↥(Subfield.closure gS)) : KK) = 0 := by
      have := hAW i
      rw [hA0] at this
      exact (mul_eq_zero.mp this.symm).resolve_right hW0
    exact_mod_cast hc0
  apply hp0
  refine Polynomial.ext fun i => ?_
  rw [Polynomial.coeff_zero]
  by_cases hi : i < d
  · exact hcoef ⟨i, hi⟩
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

private lemma tendsto_atImInfty_of_levelOne {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    Tendsto (⇑f) atImInfty (𝓝 ((UpperHalfPlane.qExpansion 1 f).coeff 0)) := by
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL
  have hO := UpperHalfPlane.exp_decay_sub_atImInfty (f := ⇑f) one_pos hper f.holo'
    (ModularFormClass.bdd_at_infty f)
  have hv : valueAtInfty ⇑f = (UpperHalfPlane.qExpansion 1 f).coeff 0 :=
    (UpperHalfPlane.qExpansion_coeff_zero one_pos
      (ModularFormClass.analyticAt_cuspFunction_zero f one_pos one_mem_strictPeriods_SL)
      hper).symm
  have hexp : Tendsto (fun τ : ℍ ↦ Real.exp (-2 * π * τ.im / 1)) atImInfty (𝓝 0) := by
    have h2 := (UpperHalfPlane.qParam_tendsto_atImInfty one_pos).norm
    rw [norm_zero] at h2
    refine h2.congr fun τ ↦ ?_
    rw [Function.Periodic.norm_qParam, UpperHalfPlane.coe_im]
  have := hO.trans_tendsto hexp
  rw [tendsto_sub_nhds_zero_iff] at this
  rwa [← hv]

private lemma tendsto_E_atImInfty {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) :
    Tendsto (⇑(ModularForm.E hk)) atImInfty (𝓝 1) := by
  have h := tendsto_atImInfty_of_levelOne (ModularForm.E hk)
  rwa [EisensteinSeries.E_qExpansion_coeff_zero hk hk2] at h

private lemma aeval_pi_apply_C (p : Polynomial ℂ) (τ : ℍ) :
    (Polynomial.aeval jf p : ℍ → ℂ) τ = p.eval (jf τ) := by
  rw [Polynomial.aeval_def,
    show (Polynomial.eval₂ (algebraMap ℂ (ℍ → ℂ)) jf p) τ =
      (Pi.evalRingHom (fun _ : ℍ => ℂ) τ) (Polynomial.eval₂ (algebraMap ℂ (ℍ → ℂ)) jf p) from rfl,
    Polynomial.hom_eval₂]
  rfl

private theorem aeval_jf_eq_zero_imp (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
    (p : Polynomial ℂ) (hp : (Polynomial.aeval jf p : ℍ → ℂ) = 0) : p = 0 := by
  by_contra hp0
  set m := p.natDegree with hm
  have hE : Tendsto (fun τ : ℍ => ModularForm.E₄ τ) atImInfty (𝓝 1) :=
    tendsto_E_atImInfty (by norm_num) (by decide)
  have hΔ : Tendsto (ModularForm.discriminant : ℍ → ℂ) atImInfty (𝓝 0) := by
    have := CuspFormClass.zero_at_infty CuspForm.discriminant
    rw [CuspForm.coe_discriminant] at this
    exact this

  have hexp : ∀ τ : ℍ, p.eval (jf τ) * ModularForm.discriminant τ ^ m =
      ∑ k ∈ Finset.range (m + 1), p.coeff k * (ModularForm.E₄ τ ^ 3) ^ k *
        ModularForm.discriminant τ ^ (m - k) := by
    intro τ
    rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [hjf τ, div_pow, ← pow_mul]
    have hΔ0 : ModularForm.discriminant τ ^ k ≠ 0 := pow_ne_zero _ (ModularForm.discriminant_ne_zero τ)
    rw [show ModularForm.discriminant τ ^ m = ModularForm.discriminant τ ^ k *
      ModularForm.discriminant τ ^ (m - k) by rw [← pow_add, Nat.add_sub_cancel' hkm]]
    field_simp
  have hlim : Tendsto (fun τ : ℍ => p.eval (jf τ) * ModularForm.discriminant τ ^ m) atImInfty
      (𝓝 (∑ k ∈ Finset.range (m + 1), p.coeff k * (1 ^ 3) ^ k * (0 : ℂ) ^ (m - k))) := by
    simp_rw [hexp]
    exact tendsto_finsetSum _ fun k _ =>
      ((tendsto_const_nhds.mul ((hE.pow 3).pow k)).mul (hΔ.pow (m - k)))
  have hsum : ∑ k ∈ Finset.range (m + 1), p.coeff k * (1 ^ 3) ^ k * (0 : ℂ) ^ (m - k) =
      p.leadingCoeff := by
    rw [Finset.sum_eq_single m]
    · simp only [Nat.sub_self, pow_zero, mul_one, one_pow]
      rfl
    · intro k hk hkm
      have : m - k ≠ 0 := Nat.sub_ne_zero_of_lt (lt_of_le_of_ne
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hkm)
      simp [zero_pow this]
    · intro h; exact absurd (Finset.self_mem_range_succ m) h
  rw [hsum] at hlim
  have hzero : (fun τ : ℍ => p.eval (jf τ) * ModularForm.discriminant τ ^ m) = fun _ => 0 := by
    funext τ
    have := congrFun hp τ
    rw [aeval_pi_apply_C, Pi.zero_apply] at this
    rw [this, zero_mul]
  rw [hzero] at hlim
  have := tendsto_nhds_unique hlim tendsto_const_nhds
  exact hp0 (Polynomial.leadingCoeff_eq_zero.mp this)

omit [NeZero N] in
private theorem transcendental_tK (hg : GenMD jf fricke)
    (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) :
    Transcendental ℂ (tK hg) := by
  rw [transcendental_iff]
  intro p hp
  apply aeval_jf_eq_zero_imp hjf p
  have h1 : (Polynomial.aeval (tK hg) p : KK) = ι (Polynomial.aeval (genH hg none) p) := by
    rw [tK, show (ι : ↥holSub →+* KK) = (IsScalarTower.toAlgHom ℂ ↥holSub KK : ↥holSub →+* KK)
      from rfl]
    exact Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom ℂ ↥holSub KK) _ _
  rw [h1, map_eq_zero_iff _ ι_injective] at hp
  have h2 := congrArg (fun f : ↥holSub => (f : ℍ → ℂ)) hp
  simp only [Subalgebra.coe_zero] at h2
  rw [← h2]
  exact (Polynomial.aeval_algHom_apply holSub.val (genH hg none) p)

end Engine

section Chain

variable {N : ℕ} [NeZero N] (K : IntermediateField ℚ ℂ) {jf : ℍ → ℂ}
  {fricke : (Fin 2 → ZMod N) → ℍ → ℂ}

private def Gch : List ℂ → IntermediateField ℚ ℂ
  | [] => K
  | c :: l => (IntermediateField.adjoin ↥(Gch l) {c}).restrictScalars ℚ

omit [NeZero N] in
private lemma Gch_cons (c : ℂ) (l : List ℂ) :
    Gch K (c :: l) = (IntermediateField.adjoin ↥(Gch K l) {c}).restrictScalars ℚ := rfl

omit [NeZero N] in
private lemma le_adjoin_restrictScalars (F : IntermediateField ℚ ℂ) (c : ℂ) :
    F ≤ (IntermediateField.adjoin ↥F {c}).restrictScalars ℚ := fun x hx ↦
  IntermediateField.algebraMap_mem (IntermediateField.adjoin ↥F {c}) (⟨x, hx⟩ : ↥F)

private lemma Gch_le_cons (c : ℂ) (l : List ℂ) : Gch K l ≤ Gch K (c :: l) :=
  le_adjoin_restrictScalars _ c

private lemma K_le_Gch : ∀ l : List ℂ, K ≤ Gch K l
  | [] => le_rfl
  | c :: l => (K_le_Gch l).trans (Gch_le_cons K c l)

private lemma mem_Gch_of_mem : ∀ {l : List ℂ} {c : ℂ}, c ∈ l → c ∈ Gch K l
  | d :: l, c, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact IntermediateField.mem_adjoin_simple_self ↥(Gch K l) c
    · exact Gch_le_cons K d l (mem_Gch_of_mem h)

private lemma Gch_le {M : IntermediateField ℚ ℂ} (hk : K ≤ M) :
    ∀ {l : List ℂ}, (∀ c ∈ l, c ∈ M) → Gch K l ≤ M
  | [], _ => hk
  | c :: l, h => by
    intro x hx
    have ih : Gch K l ≤ M := Gch_le hk fun d hd ↦ h d (List.mem_cons_of_mem c hd)
    change x ∈ IntermediateField.adjoin ↥(Gch K l) {c} at hx
    rw [← IntermediateField.mem_toSubfield, IntermediateField.adjoin_toSubfield] at hx
    refine (Subfield.closure_le (t := M.toSubfield)).mpr ?_ hx
    rintro y (⟨z, rfl⟩ | hy)
    · exact ih z.2
    · rw [Set.mem_singleton_iff] at hy; subst hy; exact h _ List.mem_cons_self

private lemma Gch_le_append_left (l₁ l₂ : List ℂ) : Gch K l₁ ≤ Gch K (l₁ ++ l₂) :=
  Gch_le K (K_le_Gch K _) fun _ hc ↦ mem_Gch_of_mem K (List.mem_append_left l₂ hc)

private lemma Gch_le_append_right (l₁ l₂ : List ℂ) : Gch K l₂ ≤ Gch K (l₁ ++ l₂) :=
  Gch_le K (K_le_Gch K _) fun _ hc ↦ mem_Gch_of_mem K (List.mem_append_right l₁ hc)

omit [NeZero N] in

private lemma adjoin_subfield_mono {F F' : IntermediateField ℚ ℂ} (h : F ≤ F') (T : Set (ℍ → ℂ))
    {y : ℍ → ℂ} (hy : y ∈ Algebra.adjoin ↥F T) : y ∈ Algebra.adjoin ↥F' T := by
  induction hy using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin hx
  | algebraMap z => exact Subalgebra.algebraMap_mem (Algebra.adjoin ↥F' T) (⟨z, h z.2⟩ : ↥F')
  | add x y _ _ hx hy => exact Subalgebra.add_mem _ hx hy
  | mul x y _ _ hx hy => exact Subalgebra.mul_mem _ hx hy

private lemma exists_list_of_mem_adjoin {T : Set (ℍ → ℂ)} {y : ℍ → ℂ} (hy : y ∈ Algebra.adjoin ℂ T) :
    ∃ l : List ℂ, y ∈ Algebra.adjoin ↥(Gch K l) T := by
  induction hy using Algebra.adjoin_induction with
  | mem x hx => exact ⟨[], Algebra.subset_adjoin hx⟩
  | algebraMap z =>
    refine ⟨[z], ?_⟩
    have : algebraMap ℂ (ℍ → ℂ) z =
        algebraMap ↥(Gch K [z]) (ℍ → ℂ) ⟨z, mem_Gch_of_mem K List.mem_cons_self⟩ := rfl
    rw [this]
    exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ ihx ihy =>
    obtain ⟨l₁, h₁⟩ := ihx
    obtain ⟨l₂, h₂⟩ := ihy
    exact ⟨l₁ ++ l₂, Subalgebra.add_mem _ (adjoin_subfield_mono (Gch_le_append_left K l₁ l₂) T h₁)
      (adjoin_subfield_mono (Gch_le_append_right K l₁ l₂) T h₂)⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨l₁, h₁⟩ := ihx
    obtain ⟨l₂, h₂⟩ := ihy
    exact ⟨l₁ ++ l₂, Subalgebra.mul_mem _ (adjoin_subfield_mono (Gch_le_append_left K l₁ l₂) T h₁)
      (adjoin_subfield_mono (Gch_le_append_right K l₁ l₂) T h₂)⟩

variable (hg : GenMD jf fricke)

private def RS (F : IntermediateField ℚ ℂ) : Set KK :=
  {z : KK | z ∈ Subfield.closure (⇑(algebraMap ℂ KK) '' (F : Set ℂ) ∪ SK hg) ∧
    IsIntegral ↥(Subring.closure (⇑(algebraMap ℂ KK) '' (F : Set ℂ) ∪ {tK hg})) z}

variable {K hg}

omit [NeZero N] in

private lemma isIntegral_closureT_of_monicRel (F : IntermediateField ℚ ℂ) {f : ℍ → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) {d : ℕ} (p : Fin d → Polynomial ℂ)
    (hpF : ∀ (i : Fin d) (n : ℕ), (p i).coeff n ∈ F)
    (hrel : ∀ τ : ℍ, f τ ^ d + ∑ i : Fin d, (p i).eval (jf τ) * f τ ^ (i : ℕ) = 0) :
    IsIntegral ↥(Subring.closure (⇑(algebraMap ℂ KK) '' (F : Set ℂ) ∪ {tK hg})) (ι ⟨f, hf⟩) := by
  set T := Subring.closure (⇑(algebraMap ℂ KK) '' (F : Set ℂ) ∪ {tK hg}) with hT

  have hlift : ∀ i : Fin d, ∃ q : Polynomial ↥F, q.map (algebraMap ↥F ℂ) = p i := fun i => by
    rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
    exact fun n => ⟨⟨(p i).coeff n, hpF i n⟩, rfl⟩
  choose q hq using hlift
  have hcmem : ∀ i : Fin d, (Polynomial.aeval jf (q i) : ℍ → ℂ) ∈ holSub := fun i =>
    adjoin_le_holSub (R := ↥F) (T := {jf}) (by rintro _ rfl; exact hg.jmd)
      (Polynomial.aeval_mem_adjoin_singleton ↥F jf)
  have hcT : ∀ i : Fin d, ι ⟨_, hcmem i⟩ ∈ T := fun i =>
    (mem_closureT_iff F hg _).mpr ⟨⟨_, hcmem i⟩, Polynomial.aeval_mem_adjoin_singleton ↥F jf, rfl⟩
  have hcval : ∀ (i : Fin d) (τ : ℍ), (Polynomial.aeval jf (q i) : ℍ → ℂ) τ = (p i).eval (jf τ) := by
    intro i τ
    rw [Polynomial.aeval_def,
      show (Polynomial.eval₂ (algebraMap ↥F (ℍ → ℂ)) jf (q i)) τ =
        (Pi.evalRingHom (fun _ : ℍ => ℂ) τ) (Polynomial.eval₂ (algebraMap ↥F (ℍ → ℂ)) jf (q i))
        from rfl,
      Polynomial.hom_eval₂, ← hq i, Polynomial.eval_map]
    rfl
  let cT : Fin d → ↥T := fun i => ⟨ι ⟨_, hcmem i⟩, hcT i⟩
  refine ⟨X ^ d + ∑ i : Fin d, C (cT i) * X ^ (i : ℕ),
    Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _), ?_⟩
  rw [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum]
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow]
  have hrelH : (⟨f, hf⟩ : ↥holSub) ^ d + ∑ i : Fin d, ⟨_, hcmem i⟩ * (⟨f, hf⟩ : ↥holSub) ^ (i : ℕ) = 0 := by
    apply Subtype.ext
    simp only [AddMemClass.coe_add, SubmonoidClass.coe_pow, AddSubmonoidClass.coe_finsetSum,
      MulMemClass.coe_mul, ZeroMemClass.coe_zero]
    funext τ
    simp only [Pi.add_apply, Pi.pow_apply, Finset.sum_apply, Pi.mul_apply, Pi.zero_apply, hcval]
    exact hrel τ
  set a : ↥holSub := ⟨f, hf⟩ with ha
  have e1 : ι a ^ d = ι (a ^ d) := (map_pow ι a d).symm
  have e2 : ∀ x : Fin d, algebraMap (↥T) KK (cT x) * ι a ^ (x : ℕ) =
      ι (⟨_, hcmem x⟩ * a ^ (x : ℕ)) := fun x => by
    rw [map_mul ι, map_pow ι]
    rfl
  rw [e1, Finset.sum_congr rfl fun x _ => e2 x, ← map_sum ι,
    ← map_add ι (a ^ d) (∑ x : Fin d, ⟨_, hcmem x⟩ * a ^ (x : ℕ)), hrelH, map_zero ι]

omit [NeZero N] in

private lemma isIntegral_SK {F : IntermediateField ℚ ℂ} (hKF : K ≤ F)
    (hint : ∀ v : Fin 2 → ZMod N, v ≠ 0 → ∃ (d : ℕ) (p : Fin d → Polynomial ℂ),
      (∀ (i : Fin d) (n : ℕ), (p i).coeff n ∈ K) ∧
      ∀ τ : ℍ, fricke v τ ^ d + ∑ i : Fin d, (p i).eval (jf τ) * fricke v τ ^ (i : ℕ) = 0)
    {s : KK} (hs : s ∈ SK hg) :
    IsIntegral ↥(Subring.closure (⇑(algebraMap ℂ KK) '' (F : Set ℂ) ∪ {tK hg})) s := by
  obtain ⟨o, rfl⟩ := hs
  cases o with
  | none =>
    exact isIntegral_algebraMap (R := ↥(Subring.closure (⇑(algebraMap ℂ KK) '' (F : Set ℂ) ∪
      {tK hg}))) (A := KK) (x := ⟨tK hg, Subring.subset_closure (Or.inr rfl)⟩)
  | some v =>
    obtain ⟨d, p, hpK, hrel⟩ := hint v.1 v.2
    exact isIntegral_closureT_of_monicRel F (hg.fmd v.1 v.2) p (fun i n => hKF (hpK i n)) hrel

private def R7bShape : Prop :=
  ∀ (F : IntermediateField ℚ ℂ) (B S : Set KK), B ⊆ S → ∀ (c : ℂ), IsAlgebraic ↥F c → ∀ (y : KK),
    y ∈ Subfield.closure
      (⇑(algebraMap ℂ KK) '' (IntermediateField.adjoin ↥F {c} : Set ℂ) ∪ S) →
    IsIntegral ↥(Subring.closure
      (⇑(algebraMap ℂ KK) '' (IntermediateField.adjoin ↥F {c} : Set ℂ) ∪ B)) y →
    y ∈ Submodule.span ℂ {z : KK | z ∈ Subfield.closure (⇑(algebraMap ℂ KK) '' (F : Set ℂ) ∪ S) ∧
      IsIntegral ↥(Subring.closure (⇑(algebraMap ℂ KK) '' (F : Set ℂ) ∪ B)) z}

private def R8aShape : Prop :=
  ∀ (F : IntermediateField ℚ ℂ) (t : KK), Transcendental ℂ t → ∀ (S : Set KK), t ∈ S → S.Finite →
    (∀ s ∈ S, IsIntegral ↥(Subring.closure (⇑(algebraMap ℂ KK) '' (F : Set ℂ) ∪ {t})) s) →
    ∀ (c : ℂ), Transcendental ↥F c →
    Transcendental ↥(Subfield.closure (⇑(algebraMap ℂ KK) '' (F : Set ℂ) ∪ S)) (algebraMap ℂ KK c) →
    ∀ (y : KK),
    y ∈ Subfield.closure (⇑(algebraMap ℂ KK) '' (IntermediateField.adjoin ↥F {c} : Set ℂ) ∪ S) →
    IsIntegral ↥(Subring.closure
      (⇑(algebraMap ℂ KK) '' (IntermediateField.adjoin ↥F {c} : Set ℂ) ∪ {t})) y →
    y ∈ Submodule.span ℂ {z : KK | z ∈ Subfield.closure (⇑(algebraMap ℂ KK) '' (F : Set ℂ) ∪ S) ∧
      IsIntegral ↥(Subring.closure (⇑(algebraMap ℂ KK) '' (F : Set ℂ) ∪ {t})) z}

variable (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
  (hkp : ∀ v : Fin 2 → ZMod N, v ≠ 0 → KPoleAt K N 1 (fricke v))
  (hint : ∀ v : Fin 2 → ZMod N, v ≠ 0 → ∃ (d : ℕ) (p : Fin d → Polynomial ℂ),
    (∀ (i : Fin d) (n : ℕ), (p i).coeff n ∈ K) ∧
    ∀ τ : ℍ, fricke v τ ^ d + ∑ i : Fin d, (p i).eval (jf τ) * fricke v τ ^ (i : ℕ) = 0)
  (h7 : R7bShape) (h8 : R8aShape)
include hjf hkp hint h7 h8

private theorem RS_cons_subset_span (c : ℂ) (l : List ℂ) :
    RS hg (Gch K (c :: l)) ⊆ (Submodule.span ℂ (RS hg (Gch K l)) : Set KK) := by
  rintro y ⟨hyS, hyB⟩
  rw [Gch_cons, IntermediateField.coe_restrictScalars] at hyS hyB
  by_cases hc : IsAlgebraic ↥(Gch K l) c
  · exact h7 (Gch K l) {tK hg} (SK hg) (Set.singleton_subset_iff.mpr (tK_mem_SK hg)) c hc y hyS hyB
  · exact h8 (Gch K l) (tK hg) (transcendental_tK hg hjf) (SK hg) (tK_mem_SK hg) (SK_finite hg)
      (fun s hs => isIntegral_SK (K_le_Gch K l) hint hs) c hc
      (transcendental_closureS hg hjf hkp (K_le_Gch K l) hc) y hyS hyB

private theorem RS_Gch_subset_span (l : List ℂ) :
    RS hg (Gch K l) ⊆ (Submodule.span ℂ (RS hg K) : Set KK) := by
  induction l with
  | nil => exact Submodule.subset_span
  | cons c l ih =>
    exact (RS_cons_subset_span hjf hkp hint h7 h8 c l).trans (Submodule.span_le.mpr ih)

omit [NeZero N] hjf hkp hint h7 h8 in

private theorem exists_list_mem_RS {G a b : ℍ → ℂ} (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (ha : a ∈ Algebra.adjoin ℂ (Set.range (gen jf fricke)))
    (hb : b ∈ Algebra.adjoin ℂ (Set.range (gen jf fricke))) (hb0 : b ≠ 0) (hGb : G * b = a)
    {d : ℕ} (p : Fin d → Polynomial ℂ)
    (hprel : ∀ τ : ℍ, G τ ^ d + ∑ i : Fin d, (p i).eval (jf τ) * G τ ^ (i : ℕ) = 0) :
    ∃ l : List ℂ, ι ⟨G, hG⟩ ∈ RS hg (Gch K l) := by
  classical
  obtain ⟨la, hla⟩ := exists_list_of_mem_adjoin K ha
  obtain ⟨lb, hlb⟩ := exists_list_of_mem_adjoin K hb
  let lc : Fin d → List ℂ := fun i => (List.range ((p i).natDegree + 1)).map (p i).coeff
  set L : List ℂ := la ++ lb ++ (List.finRange d).flatMap lc with hL
  have hLa : Gch K la ≤ Gch K L := (Gch_le_append_left K la lb).trans (Gch_le_append_left K _ _)
  have hLb : Gch K lb ≤ Gch K L := (Gch_le_append_right K la lb).trans (Gch_le_append_left K _ _)
  have hLc : ∀ (i : Fin d) (n : ℕ), (p i).coeff n ∈ Gch K L := by
    intro i n
    by_cases hn : n ≤ (p i).natDegree
    · refine Gch_le_append_right K _ _ (mem_Gch_of_mem K ?_)
      exact List.mem_flatMap.mpr ⟨i, List.mem_finRange i,
        List.mem_map.mpr ⟨n, List.mem_range.mpr (Nat.lt_succ_of_le hn), rfl⟩⟩
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (not_le.mp hn)]
      exact zero_mem _
  have hamd : a ∈ holSub := adjoin_le_holSub (range_gen_subset_holSub hg) ha
  have hbmd : b ∈ holSub := adjoin_le_holSub (range_gen_subset_holSub hg) hb
  have haS := (mem_closureS_iff (Gch K L) hg _).mpr ⟨⟨a, hamd⟩, adjoin_subfield_mono hLa _ hla, rfl⟩
  have hbS := (mem_closureS_iff (Gch K L) hg _).mpr ⟨⟨b, hbmd⟩, adjoin_subfield_mono hLb _ hlb, rfl⟩
  have hb0' : ι ⟨b, hbmd⟩ ≠ 0 := fun h => hb0 (congrArg Subtype.val ((map_eq_zero_iff ι ι_injective).mp h))
  refine ⟨L, ?_, isIntegral_closureT_of_monicRel (Gch K L) hG p hLc hprel⟩
  have hGab : ι ⟨G, hG⟩ = ι ⟨a, hamd⟩ / ι ⟨b, hbmd⟩ :=
    eq_div_of_mul_eq hb0' ((map_mul ι ⟨G, hG⟩ ⟨b, hbmd⟩).symm.trans (congrArg ι (Subtype.ext hGb)))
  have haF : ι ⟨a, hamd⟩ ∈ Subfield.closure (⇑(algebraMap ℂ KK) '' ((Gch K L : IntermediateField ℚ ℂ) : Set ℂ) ∪ SK hg) :=
    Subfield.subring_closure_le _ haS
  have hbF : ι ⟨b, hbmd⟩ ∈ Subfield.closure (⇑(algebraMap ℂ KK) '' ((Gch K L : IntermediateField ℚ ℂ) : Set ℂ) ∪ SK hg) :=
    Subfield.subring_closure_le _ hbS
  rw [hGab]
  exact Subfield.div_mem _ haF hbF

end Chain

section Assembly

variable {N : ℕ} [NeZero N] {K : IntermediateField ℚ ℂ} {jf : ℍ → ℂ}
  {fricke : (Fin 2 → ZMod N) → ℍ → ℂ} {hg : GenMD jf fricke}

private def R6h2Shape : Prop :=
  ∀ {a b : ℍ → ℂ} {c : ℕ → ℍ → ℂ} {d : ℕ}, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) a →
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) b → b ≠ 0 → (∀ k < d, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (c k)) →
    a ^ d + ∑ k ∈ Finset.range d, c k * b ^ (d - k) * a ^ k = 0 →
    ∃ F : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F ∧ F * b = a

omit [NeZero N] in
private lemma aeval_pi_apply (q : Polynomial ↥K) (τ : ℍ) :
    (Polynomial.aeval jf q : ℍ → ℂ) τ = (q.map (algebraMap ↥K ℂ)).eval (jf τ) := by
  rw [Polynomial.aeval_def, Polynomial.eval_map,
    show (Polynomial.eval₂ (algebraMap ↥K (ℍ → ℂ)) jf q) τ =
      (Pi.evalRingHom (fun _ : ℍ => ℂ) τ) (Polynomial.eval₂ (algebraMap ↥K (ℍ → ℂ)) jf q) from rfl,
    Polynomial.hom_eval₂]
  rfl

omit [NeZero N] in

private theorem holRep (h6 : R6h2Shape) {z : KK} (hz : z ∈ RS hg K) :
    ∃ (Gf u w : ℍ → ℂ) (hGf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Gf),
      u ∈ Algebra.adjoin ↥K (Set.range (gen jf fricke)) ∧
      w ∈ Algebra.adjoin ↥K (Set.range (gen jf fricke)) ∧ w ≠ 0 ∧ Gf * w = u ∧ ι ⟨Gf, hGf⟩ = z ∧
      ∃ (D : ℕ) (q : Fin D → Polynomial ↥K), ∀ τ : ℍ,
        Gf τ ^ D + ∑ k : Fin D, ((q k).map (algebraMap ↥K ℂ)).eval (jf τ) * Gf τ ^ (k : ℕ) = 0 := by
  classical
  obtain ⟨hzS, hzB⟩ := hz

  obtain ⟨uH, huH, wH, hwH, hw0, hzuw⟩ : ∃ uH : ↥holSub,
      (uH : ℍ → ℂ) ∈ Algebra.adjoin ↥K (Set.range (gen jf fricke)) ∧ ∃ wH : ↥holSub,
      (wH : ℍ → ℂ) ∈ Algebra.adjoin ↥K (Set.range (gen jf fricke)) ∧ ι wH ≠ 0 ∧
      z = ι uH / ι wH := by
    obtain ⟨u, hu, w, hw, huw⟩ := Subfield.mem_closure_iff.mp hzS
    obtain ⟨uH, huH, rfl⟩ := (mem_closureS_iff K hg u).mp hu
    obtain ⟨wH, hwH, rfl⟩ := (mem_closureS_iff K hg w).mp hw
    by_cases hw0 : ι wH = 0
    · refine ⟨0, Subalgebra.zero_mem _, 1, Subalgebra.one_mem _, ?_, ?_⟩
      · rw [map_one ι]; exact one_ne_zero
      · rw [← huw, hw0, div_zero, map_zero ι, zero_div]
    · exact ⟨uH, huH, wH, hwH, hw0, huw.symm⟩
  have hwH0 : (wH : ℍ → ℂ) ≠ 0 := fun h => hw0 (by rw [show wH = 0 from Subtype.ext h, map_zero ι])
  have hzw : z * ι wH = ι uH := by rw [hzuw, div_mul_cancel₀ _ hw0]

  obtain ⟨P, hPm, hPc, hPz⟩ := (isIntegral_subring_iff _ _).mp hzB
  choose cH hcH hcHι using fun k => (mem_closureT_iff K hg (P.coeff k)).mp (hPc k)
  set D := P.natDegree with hD

  have hkey : ∀ k ≤ D, z ^ k * ι wH ^ D = ι uH ^ k * ι wH ^ (D - k) := fun k hk => by
    calc z ^ k * ι wH ^ D = z ^ k * (ι wH ^ k * ι wH ^ (D - k)) := by
          rw [← pow_add, Nat.add_sub_cancel' hk]
      _ = (z * ι wH) ^ k * ι wH ^ (D - k) := by rw [mul_pow, mul_assoc]
      _ = ι uH ^ k * ι wH ^ (D - k) := by rw [hzw]
  have hrelK : ι uH ^ D + ∑ k ∈ Finset.range D, ι (cH k) * ι wH ^ (D - k) * ι uH ^ k = 0 := by
    have h1 : (∑ k ∈ Finset.range (D + 1), P.coeff k * z ^ k) * ι wH ^ D = 0 := by
      rw [← Polynomial.eval_eq_sum_range, hPz, zero_mul]
    have h2 : ∑ k ∈ Finset.range D, P.coeff k * z ^ k * ι wH ^ D =
        ∑ k ∈ Finset.range D, ι (cH k) * ι wH ^ (D - k) * ι uH ^ k :=
      Finset.sum_congr rfl fun k hk => by
        rw [mul_assoc, hkey k (Finset.mem_range.mp hk).le, ← hcHι k]; ring
    rw [Finset.sum_mul, Finset.sum_range_succ, h2, show P.coeff D = 1 from hPm.coeff_natDegree,
      one_mul, hkey D le_rfl, Nat.sub_self, pow_zero, mul_one, add_comm] at h1
    exact h1

  have hrelH : uH ^ D + ∑ k ∈ Finset.range D, cH k * wH ^ (D - k) * uH ^ k = 0 := by
    apply ι_injective
    rw [map_zero ι, ← hrelK, map_add ι (uH ^ D) (∑ k ∈ Finset.range D, cH k * wH ^ (D - k) * uH ^ k),
      map_pow ι, map_sum ι]
    refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
    rw [map_mul ι, map_mul ι, map_pow ι, map_pow ι]
  have hrelF : (uH : ℍ → ℂ) ^ D +
      ∑ k ∈ Finset.range D, (cH k : ℍ → ℂ) * (wH : ℍ → ℂ) ^ (D - k) * (uH : ℍ → ℂ) ^ k = 0 := by
    have := congrArg Subtype.val hrelH
    simpa only [AddMemClass.coe_add, SubmonoidClass.coe_pow, AddSubmonoidClass.coe_finsetSum,
      MulMemClass.coe_mul, ZeroMemClass.coe_zero] using this

  obtain ⟨Gf, hGf, hGw⟩ := h6 uH.2 wH.2 hwH0 (fun k _ => (cH k).2) hrelF
  have hιG : ι ⟨Gf, hGf⟩ = z := by
    rw [hzuw, eq_div_iff hw0, ← map_mul ι ⟨Gf, hGf⟩ wH]
    exact congrArg ι (Subtype.ext hGw)

  choose q hq using fun k : Fin D => Algebra.adjoin_mem_exists_aeval _ _ (hcH k)

  have hg0 : (⟨Gf, hGf⟩ : ↥holSub) ^ D + ∑ k ∈ Finset.range D, cH k * ⟨Gf, hGf⟩ ^ k = 0 := by
    apply ι_injective
    have h1 : ∑ k ∈ Finset.range D, P.coeff k * ι ⟨Gf, hGf⟩ ^ k + ι ⟨Gf, hGf⟩ ^ D = 0 := by
      have := hPz
      rwa [Polynomial.eval_eq_sum_range, Finset.sum_range_succ,
        show P.coeff D = 1 from hPm.coeff_natDegree, one_mul, ← hιG] at this
    rw [map_zero ι, map_add ι ((⟨Gf, hGf⟩ : ↥holSub) ^ D)
      (∑ k ∈ Finset.range D, cH k * ⟨Gf, hGf⟩ ^ k), map_pow ι, map_sum ι, add_comm, ← h1]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul ι, map_pow ι, hcHι]
  refine ⟨Gf, uH, wH, hGf, huH, hwH, hwH0, hGw, hιG, D, q, fun τ => ?_⟩
  have h := congrArg (fun f : ↥holSub => (f : ℍ → ℂ) τ) hg0
  simp only [AddMemClass.coe_add, SubmonoidClass.coe_pow, AddSubmonoidClass.coe_finsetSum,
    MulMemClass.coe_mul, ZeroMemClass.coe_zero, Pi.add_apply, Pi.pow_apply, Finset.sum_apply,
    Pi.mul_apply, Pi.zero_apply] at h
  rw [Finset.sum_range] at h
  rw [← h]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← aeval_pi_apply, hq k]

include hg in

private theorem main (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
    (hkp : ∀ v : Fin 2 → ZMod N, v ≠ 0 → KPoleAt K N 1 (fricke v))
    (hint : ∀ v : Fin 2 → ZMod N, v ≠ 0 → ∃ (d : ℕ) (p : Fin d → Polynomial ℂ),
      (∀ (i : Fin d) (n : ℕ), (p i).coeff n ∈ K) ∧
      ∀ τ : ℍ, fricke v τ ^ d + ∑ i : Fin d, (p i).eval (jf τ) * fricke v τ ^ (i : ℕ) = 0)
    (h6 : R6h2Shape) (h7 : R7bShape) (h8 : R8aShape)
    {G a b : ℍ → ℂ} (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (ha : a ∈ Algebra.adjoin ℂ
      (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}))
    (hb : b ∈ Algebra.adjoin ℂ
      (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}))
    (hb0 : b ≠ 0) (hGb : G * b = a)
    {d : ℕ} (p : Fin d → Polynomial ℂ)
    (hprel : ∀ τ : ℍ, G τ ^ d + ∑ i : Fin d, (p i).eval (jf τ) * G τ ^ (i : ℕ) = 0) :
    ∃ (n : ℕ) (lam : Fin n → ℂ) (Gi : Fin n → (ℍ → ℂ))
      (Pi Qi : Fin n → (ℍ → ℂ))
      (di : Fin n → ℕ) (pi : ∀ i, Fin (di i) → Polynomial ℂ),
      (G = ∑ i, lam i • Gi i) ∧
      (∀ i, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Gi i)) ∧
      (∀ i, Pi i ∈ Algebra.adjoin ↥K
          (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}) ∧
        Qi i ∈ Algebra.adjoin ↥K
          (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}) ∧
        Qi i ≠ 0 ∧ Gi i * Qi i = Pi i) ∧
      (∀ i k m, (pi i k).coeff m ∈ K) ∧
      (∀ i τ, Gi i τ ^ di i +
        ∑ k : Fin (di i), (pi i k).eval (jf τ) * Gi i τ ^ (k : ℕ) = 0) := by
  rw [← range_gen jf fricke] at ha hb ⊢
  obtain ⟨Lc, hLc⟩ := exists_list_mem_RS (K := K) (hg := hg) hG ha hb hb0 hGb p hprel
  have hspan : ι ⟨G, hG⟩ ∈ Submodule.span ℂ (RS hg K) :=
    RS_Gch_subset_span hjf hkp hint h7 h8 Lc hLc
  obtain ⟨n, lam, z, hz⟩ := Submodule.mem_span_set'.mp hspan
  choose Gf u w hGf hu hw hw0 hGw hιG D q hrel using fun i => holRep h6 (z i).2
  refine ⟨n, lam, Gf, u, w, D, fun i k => (q i k).map (algebraMap ↥K ℂ), ?_, hGf,
    fun i => ⟨hu i, hw i, hw0 i, hGw i⟩, fun i k m => ?_, hrel⟩
  · have hH : (⟨G, hG⟩ : ↥holSub) = ∑ i, lam i • (⟨Gf i, hGf i⟩ : ↥holSub) := by
      apply ι_injective
      rw [map_sum ι, ← hz]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, Algebra.smul_def, map_mul ι, ι_algebraMap, hιG]
    have := congrArg Subtype.val hH
    simpa only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] using this
  · rw [Polynomial.coeff_map]
    exact ((q i k).coeff m).2

end Assembly

open UpperHalfPlane in
open scoped Manifold in
/-!
                                                                    -/
private theorem solutionInterim
    (N : ℕ) [NeZero N]
    (L : ℍ → PeriodPair) (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
    (W : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hW : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), W v τ = ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
      PeriodPair.weierstrassP (L τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)))
    (fricke : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hfricke : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), fricke v τ =
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * W v τ)
    (jf : ℍ → ℂ)
    (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
    {G a b : ℍ → ℂ} (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (ha : a ∈ Algebra.adjoin ℂ
      (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}))
    (hb : b ∈ Algebra.adjoin ℂ
      (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}))
    (hb0 : b ≠ 0) (hGb : G * b = a)
    {d : ℕ} (p : Fin d → Polynomial ℂ)
    (hprel : ∀ τ : ℍ, G τ ^ d + ∑ i : Fin d, (p i).eval (jf τ) * G τ ^ (i : ℕ) = 0)
    (K : IntermediateField ℚ ℂ)
    (hK : K = IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))})
    (hR4a : ∀ v : Fin 2 → ZMod N, v ≠ 0 → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fricke v))
    (hR4kp : ∀ v : Fin 2 → ZMod N, v ≠ 0 →
      Function.Periodic ((fricke v * ModularForm.discriminant ^ 1) ∘ UpperHalfPlane.ofComplex) N ∧
      IsBoundedAtImInfty (fricke v * ModularForm.discriminant ^ 1) ∧
      ∀ n : ℕ, (UpperHalfPlane.qExpansion N (fricke v * ModularForm.discriminant ^ 1)).coeff n ∈ K)
    (hR4int : ∀ v : Fin 2 → ZMod N, v ≠ 0 → ∃ (d : ℕ) (p : Fin d → Polynomial ℂ),
      (∀ (i : Fin d) (n : ℕ), (p i).coeff n ∈ K) ∧
      ∀ τ : ℍ, fricke v τ ^ d + ∑ i : Fin d, (p i).eval (jf τ) * fricke v τ ^ (i : ℕ) = 0)
    (hR6 : R6h2Shape) (hR7b : R7bShape) (hR8a : R8aShape) :
    letI kN : IntermediateField ℚ ℂ :=
      IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))}
    ∃ (n : ℕ) (lam : Fin n → ℂ) (Gi : Fin n → (ℍ → ℂ))
      (Pi Qi : Fin n → (ℍ → ℂ))
      (di : Fin n → ℕ) (pi : ∀ i, Fin (di i) → Polynomial ℂ),
      (G = ∑ i, lam i • Gi i) ∧
      (∀ i, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Gi i)) ∧
      (∀ i, Pi i ∈ Algebra.adjoin ↥kN
          (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}) ∧
        Qi i ∈ Algebra.adjoin ↥kN
          (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}) ∧
        Qi i ≠ 0 ∧ Gi i * Qi i = Pi i) ∧
      (∀ i k m, (pi i k).coeff m ∈ kN) ∧
      (∀ i τ, Gi i τ ^ di i +
        ∑ k : Fin (di i), (pi i k).eval (jf τ) * Gi i τ ^ (k : ℕ) = 0) := by
  have _hL := hL
  have _hW := hW
  have _hfricke := hfricke
  subst hK
  have hg : GenMD jf fricke := ⟨mdiff_jf hjf, hR4a⟩
  have hkp : ∀ v : Fin 2 → ZMod N, v ≠ 0 → KPoleAt
      (IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))})
      N 1 (fricke v) := fun v hv => by
    obtain ⟨h1, h2, h3⟩ := hR4kp v hv
    exact ⟨by simpa only [CuspForm.coe_discriminant] using h1,
      by simpa only [CuspForm.coe_discriminant] using h2,
      by simpa only [CuspForm.coe_discriminant] using h3⟩
  exact main (hg := hg) hjf hkp hR4int hR6 hR7b hR8a hG ha hb hb0 hGb p hprel

open UpperHalfPlane hiding I in
open scoped UpperHalfPlane Manifold MatrixGroups ModularForm in
open _root_.WLight in
theorem _root_.WLight.frickeFunction_intBaseChange
    (N : ℕ) [NeZero N]
    (L : ℍ → PeriodPair) (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
    (W : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hW : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), W v τ = ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
      PeriodPair.weierstrassP (L τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)))
    (fricke : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hfricke : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), fricke v τ =
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * W v τ)
    (jf : ℍ → ℂ)
    (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
    {G a b : ℍ → ℂ} (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (ha : a ∈ Algebra.adjoin ℂ
      (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}))
    (hb : b ∈ Algebra.adjoin ℂ
      (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}))
    (hb0 : b ≠ 0) (hGb : G * b = a)
    {d : ℕ} (p : Fin d → Polynomial ℂ)
    (hprel : ∀ τ : ℍ, G τ ^ d + ∑ i : Fin d, (p i).eval (jf τ) * G τ ^ (i : ℕ) = 0) :
    letI kN : IntermediateField ℚ ℂ :=
      IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))}
    ∃ (n : ℕ) (lam : Fin n → ℂ) (Gi : Fin n → (ℍ → ℂ))
      (Pi Qi : Fin n → (ℍ → ℂ))
      (di : Fin n → ℕ) (pi : ∀ i, Fin (di i) → Polynomial ℂ),
      (G = ∑ i, lam i • Gi i) ∧
      (∀ i, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Gi i)) ∧
      (∀ i, Pi i ∈ Algebra.adjoin ↥kN
          (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}) ∧
        Qi i ∈ Algebra.adjoin ↥kN
          (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}) ∧
        Qi i ≠ 0 ∧ Gi i * Qi i = Pi i) ∧
      (∀ i k m, (pi i k).coeff m ∈ kN) ∧
      (∀ i τ, Gi i τ ^ di i +
        ∑ k : Fin (di i), (pi i k).eval (jf τ) * Gi i τ ^ (k : ℕ) = 0):= by
  refine solutionInterim N L hL W hW fricke hfricke jf hjf hG ha hb hb0 hGb p hprel
      (IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))}) rfl
      ?_ ?_ ?_ ?_ ?_ ?_
  · intro v hv
    rw [show fricke v = fun τ : ℍ =>
        -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 *
          (((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ * PeriodPair.weierstrassP (L τ)
            ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ))) from
      funext fun τ => by rw [hfricke, hW]]
    exact (frickeFunction_modularity_package N L hL).2.2.1 v hv
  · intro v hv
    have pkg := frickeFunction_modularity_package N L hL
    have hfeq : fricke v = fun τ : ℍ =>
        -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 *
          (((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ * PeriodPair.weierstrassP (L τ)
            ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ))) :=
      funext fun τ => by rw [hfricke, hW]
    obtain ⟨hper, hco⟩ := pkg.2.2.2.2.1 v hv
    have hbd := pkg.2.2.2.1 v hv
    refine ⟨?_, ?_, ?_⟩
    · rw [pow_one, hfeq]; exact hper
    · rw [pow_one, hfeq]; exact hbd
    · intro n; rw [pow_one, hfeq]; exact hco n
  · intro v hv
    obtain ⟨P, hPco, hPrel⟩ :=
      (frickeFunction_orbit_package N L hL W hW fricke hfricke jf hjf).2.2
    refine ⟨N ^ 2 - 1, fun i => P (i : ℕ), fun i n => hPco (i : ℕ) n, fun τ => ?_⟩
    have h := hPrel v hv τ
    have hsum := Fin.sum_univ_eq_sum_range
      (fun k => Polynomial.eval (jf τ) (P k) * fricke v τ ^ k) (N ^ 2 - 1)
    rw [hsum]
    exact h
  · exact fun {a b c d} ha hb hb0 hc hrel =>
      exists_mdifferentiable_div_of_monicRel ha hb hb0 hc hrel
  · exact IsIntegral.mem_span_of_adjoin_simple_constants
  · exact IsIntegral.mem_span_of_adjoin_simple_constants_transcendental

end R8b

end WLightFriIntBC

end WLight
