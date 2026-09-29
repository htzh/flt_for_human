/-
  The standard period pair `(τ, 1)` and the period-lattice vocabulary.

  `periodPairOfTau τ` is mathlib's `PeriodPair`
  (`Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass`) with
  `ω₁ = (τ : ℂ)`, `ω₂ = 1`; its independence proof is the standard
  `(s·τ + t·1 = 0 ⇒ s = 0)` argument.  `smulPeriodPair a ha L` rescales a pair by
  `a ≠ 0`, with the induced equivalence of lattices and the homogeneity of
  mathlib's `weierstrassP` under it.

  **Why this module.**  The pin defines this prelude `private` once per `WLight`
  package (`P2M/Sol/S_WLight_*`, `S_ModularCurve_*`, `S_ModularForm_weierstrassP_*`,
  pinned `aa2d8b3`); the route-C′ port copied it into five modules.  It is real
  mathematics on a mathlib object, used by every weight-one package, so it is
  written once here.  Statements are the pin's, verbatim; only `private` →
  public.

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WLight_frickeFunction_modularity_package.lean
-/
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.LinearAlgebra.LinearIndependent.Basic

open PeriodPair
open scoped UpperHalfPlane

/-- The standard period pair `(τ, 1)` on the upper half plane. -/
def periodPairOfTau (τ : ℍ) : PeriodPair where
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

@[simp] lemma periodPairOfTau_ω₁ (τ : ℍ) : (periodPairOfTau τ).ω₁ = (τ : ℂ) := rfl

@[simp] lemma periodPairOfTau_ω₂ (τ : ℍ) : (periodPairOfTau τ).ω₂ = 1 := rfl

/-- Rescale a period pair by a nonzero complex number. -/
def smulPeriodPair (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) : PeriodPair where
  ω₁ := a * L.ω₁
  ω₂ := a * L.ω₂
  indep := LinearIndependent.pair_iff.mpr fun s t hst => by
    refine LinearIndependent.pair_iff.mp L.indep s t ?_
    have h0 : a * (s • L.ω₁ + t • L.ω₂) = 0 := by
      rw [mul_add, mul_smul_comm, mul_smul_comm]; exact hst
    exact (mul_eq_zero.mp h0).resolve_left ha

@[simp] lemma smulPeriodPair_ω₁ (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) :
    (smulPeriodPair a ha L).ω₁ = a * L.ω₁ := rfl

@[simp] lemma smulPeriodPair_ω₂ (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) :
    (smulPeriodPair a ha L).ω₂ = a * L.ω₂ := rfl

lemma mem_smulPeriodPair_lattice {a : ℂ} (ha : a ≠ 0) (L : PeriodPair) {x : ℂ} :
    x ∈ (smulPeriodPair a ha L).lattice ↔ ∃ y ∈ L.lattice, x = a * y := by
  simp only [mem_lattice, smulPeriodPair_ω₁, smulPeriodPair_ω₂]
  constructor
  · rintro ⟨m, n, h⟩
    exact ⟨(m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂, ⟨m, n, rfl⟩, by rw [← h]; ring⟩
  · rintro ⟨y, ⟨m, n, h⟩, rfl⟩
    exact ⟨m, n, by rw [← h]; ring⟩

/-- Rescaling identifies the two period lattices. -/
noncomputable def smulLatticeEquiv (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) :
    L.lattice ≃ (smulPeriodPair a ha L).lattice where
  toFun l := ⟨a * l, (mem_smulPeriodPair_lattice ha L).mpr ⟨l, l.2, rfl⟩⟩
  invFun l := ⟨a⁻¹ * l, by
    obtain ⟨y, hy, hxy⟩ := (mem_smulPeriodPair_lattice ha L).mp l.2
    rw [hxy, inv_mul_cancel_left₀ ha]; exact hy⟩
  left_inv l := Subtype.ext (inv_mul_cancel_left₀ ha _)
  right_inv l := Subtype.ext (mul_inv_cancel_left₀ ha _)

@[simp] lemma smulLatticeEquiv_coe (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) (l : L.lattice) :
    ((smulLatticeEquiv a ha L) l : ℂ) = a * l := rfl

/-- `weierstrassP` is homogeneous of degree `-2` under a rescaling of the pair. -/
theorem weierstrassP_smulPeriodPair (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) (z : ℂ) :
    weierstrassP (smulPeriodPair a ha L) (a * z) = a⁻¹ ^ 2 * weierstrassP L z := by
  have key : ∀ u : ℂ, 1 / (a * u) ^ 2 = a⁻¹ ^ 2 * (1 / u ^ 2) := fun u => by
    simp [one_div, mul_pow, inv_pow, mul_comm]
  simp only [weierstrassP]
  rw [← (smulLatticeEquiv a ha L).tsum_eq, ← tsum_mul_left]
  congr with l
  simp only [smulLatticeEquiv_coe]
  rw [show a * z - a * (l : ℂ) = a * (z - l) by ring, key, key, mul_sub]

/-- Two period pairs with the same `ω₁` and `ω₂` are equal. -/
lemma periodPair_eq_of_ω (P P' : PeriodPair) (h1 : P.ω₁ = P'.ω₁) (h2 : P.ω₂ = P'.ω₂) :
    P = P' := by
  rcases P with ⟨_, _, _⟩; rcases P' with ⟨_, _, _⟩
  simp only [PeriodPair.mk.injEq]; exact ⟨h1, h2⟩
