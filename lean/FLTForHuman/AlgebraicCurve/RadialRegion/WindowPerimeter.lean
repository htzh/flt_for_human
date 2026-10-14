/-
The public headline `AlgebraicCurve.RadialRegion.exists_window_perimeter`: the
boundary of a grid window is a radial region whose `N` counts the sides, with
pairwise-distinct arcs and the stated perimeter data.

Tier 1 over the tier-3 engine
`FLTForHuman/AlgebraicCurve/RadialRegion/Engine/WindowPerimeter.lean`. The
statement is the pin's
`Theorems/Thm_AlgebraicCurve_RadialRegion_exists_window_perimeter.lean` wrapper
verbatim — that wrapper, not the pin's `S_` section-implicit `solution`, is the
checker's statement authority — and the proof is the one-line application of the
engine's kernel
`AlgebraicCurve.RadialRegion.WindowPerimeter.exists_window_perimeter`, exactly as
the pin's `solution` forwards to it.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_RadialRegion_exists_window_perimeter.lean>
-/
import FLTForHuman.AlgebraicCurve.RadialRegion.Engine.WindowPerimeter

set_option autoImplicit false

open scoped Real
open AlgebraicCurve Set

namespace AlgebraicCurve.RadialRegion

-- pin: exists_window_perimeter (Theorems/Thm_AlgebraicCurve_RadialRegion_exists_window_perimeter.lean)
theorem exists_window_perimeter (o hm : ℝ) (hhm : 0 < hm) (jlo jhi klo khi : ℤ)
    (hj : jlo ≤ jhi) (hk : klo ≤ khi) (cy : ℤ × ℤ → ℝ)
    (hcy : ∀ p : ℤ × ℤ, o + p.2 * hm < cy p ∧ cy p < o + (p.2 + 1) * hm)
    (hx₀ : o + jlo * hm < 0) (hx₁ : 0 < o + (jhi + 1) * hm)
    (hy₀ : o + klo * hm < 0) (hy₁ : 0 < o + (khi + 1) * hm)
    (hcy0 : ∀ k : ℤ, o + k * hm < 0 → 0 < o + (k + 1) * hm → cy (jhi, k) = 0) :
    ∃ R : RadialRegion,
      R.q = 0 ∧
      R.K = {z : ℂ | z.re ∈ Icc (o + jlo * hm) (o + (jhi + 1) * hm) ∧
        z.im ∈ Icc (o + klo * hm) (o + (khi + 1) * hm)} ∧
      R.Kint = {z : ℂ | z.re ∈ Ioo (o + jlo * hm) (o + (jhi + 1) * hm) ∧
        z.im ∈ Ioo (o + klo * hm) (o + (khi + 1) * hm)} ∧
      R.N = 2 * (jhi - jlo + 1).toNat + 4 * (khi - klo + 1).toNat ∧
      (∀ k k' : Fin R.N, R.arcSet k = R.arcSet k' → k = k') ∧
      (∀ k : Fin R.N,
        (∃ j : ℤ, jlo ≤ j ∧ j ≤ jhi ∧
          R.arcSet k = {z : ℂ | z.im = o + klo * hm ∧ z.re ∈ Icc (o + j * hm) (o + (j + 1) * hm)} ∧
          R.loop (R.φs k.castSucc) = ⟨o + j * hm, o + klo * hm⟩ ∧
          R.loop (R.φs k.succ) = ⟨o + (j + 1) * hm, o + klo * hm⟩ ∧
          (∀ t ∈ R.arcIcc k, R.r t = (-Real.sin t / (-(o + klo * hm)))⁻¹) ∧
          R.arcIcc k ⊆ Ioo π (2 * π)) ∨
        (∃ j : ℤ, jlo ≤ j ∧ j ≤ jhi ∧
          R.arcSet k = {z : ℂ | z.im = o + (khi + 1) * hm ∧
            z.re ∈ Icc (o + j * hm) (o + (j + 1) * hm)} ∧
          R.loop (R.φs k.castSucc) = ⟨o + (j + 1) * hm, o + (khi + 1) * hm⟩ ∧
          R.loop (R.φs k.succ) = ⟨o + j * hm, o + (khi + 1) * hm⟩ ∧
          (∀ t ∈ R.arcIcc k, R.r t = (Real.sin t / (o + (khi + 1) * hm))⁻¹) ∧
          R.arcIcc k ⊆ Ioo 0 π) ∨
        (∃ k₀ : ℤ, klo ≤ k₀ ∧ k₀ ≤ khi ∧
          R.arcSet k = {z : ℂ | z.re = o + jlo * hm ∧ z.im ∈ Icc (cy (jlo, k₀)) (o + (k₀ + 1) * hm)} ∧
          R.loop (R.φs k.castSucc) = ⟨o + jlo * hm, o + (k₀ + 1) * hm⟩ ∧
          R.loop (R.φs k.succ) = ⟨o + jlo * hm, cy (jlo, k₀)⟩ ∧
          (∀ t ∈ R.arcIcc k, R.r t = (-Real.cos t / (-(o + jlo * hm)))⁻¹) ∧
          R.arcIcc k ⊆ Ioo (π / 2) (3 * π / 2)) ∨
        (∃ k₀ : ℤ, klo ≤ k₀ ∧ k₀ ≤ khi ∧
          R.arcSet k = {z : ℂ | z.re = o + jlo * hm ∧ z.im ∈ Icc (o + k₀ * hm) (cy (jlo, k₀))} ∧
          R.loop (R.φs k.castSucc) = ⟨o + jlo * hm, cy (jlo, k₀)⟩ ∧
          R.loop (R.φs k.succ) = ⟨o + jlo * hm, o + k₀ * hm⟩ ∧
          (∀ t ∈ R.arcIcc k, R.r t = (-Real.cos t / (-(o + jlo * hm)))⁻¹) ∧
          R.arcIcc k ⊆ Ioo (π / 2) (3 * π / 2)) ∨
        (∃ k₀ : ℤ, klo ≤ k₀ ∧ k₀ ≤ khi ∧
          R.arcSet k = {z : ℂ | z.re = o + (jhi + 1) * hm ∧ z.im ∈ Icc (o + k₀ * hm) (cy (jhi, k₀))} ∧
          R.loop (R.φs k.castSucc) = ⟨o + (jhi + 1) * hm, o + k₀ * hm⟩ ∧
          R.loop (R.φs k.succ) = ⟨o + (jhi + 1) * hm, cy (jhi, k₀)⟩ ∧
          (∀ t ∈ R.arcIcc k, R.r t = (Real.cos t / (o + (jhi + 1) * hm))⁻¹) ∧
          (R.arcIcc k ⊆ Ioo (-(π / 2)) (π / 2) ∨ R.arcIcc k ⊆ Ioo (3 * π / 2) (5 * π / 2))) ∨
        (∃ k₀ : ℤ, klo ≤ k₀ ∧ k₀ ≤ khi ∧
          R.arcSet k = {z : ℂ | z.re = o + (jhi + 1) * hm ∧
            z.im ∈ Icc (cy (jhi, k₀)) (o + (k₀ + 1) * hm)} ∧
          R.loop (R.φs k.castSucc) = ⟨o + (jhi + 1) * hm, cy (jhi, k₀)⟩ ∧
          R.loop (R.φs k.succ) = ⟨o + (jhi + 1) * hm, o + (k₀ + 1) * hm⟩ ∧
          (∀ t ∈ R.arcIcc k, R.r t = (Real.cos t / (o + (jhi + 1) * hm))⁻¹) ∧
          (R.arcIcc k ⊆ Ioo (-(π / 2)) (π / 2) ∨ R.arcIcc k ⊆ Ioo (3 * π / 2) (5 * π / 2)))) ∧
      (∀ j : ℤ, jlo ≤ j → j ≤ jhi → ∃ k : Fin R.N,
        R.arcSet k = {z : ℂ | z.im = o + klo * hm ∧ z.re ∈ Icc (o + j * hm) (o + (j + 1) * hm)}) ∧
      (∀ j : ℤ, jlo ≤ j → j ≤ jhi → ∃ k : Fin R.N,
        R.arcSet k = {z : ℂ | z.im = o + (khi + 1) * hm ∧ z.re ∈ Icc (o + j * hm) (o + (j + 1) * hm)}) ∧
      (∀ k₀ : ℤ, klo ≤ k₀ → k₀ ≤ khi → ∃ k : Fin R.N,
        R.arcSet k = {z : ℂ | z.re = o + jlo * hm ∧ z.im ∈ Icc (cy (jlo, k₀)) (o + (k₀ + 1) * hm)}) ∧
      (∀ k₀ : ℤ, klo ≤ k₀ → k₀ ≤ khi → ∃ k : Fin R.N,
        R.arcSet k = {z : ℂ | z.re = o + jlo * hm ∧ z.im ∈ Icc (o + k₀ * hm) (cy (jlo, k₀))}) ∧
      (∀ k₀ : ℤ, klo ≤ k₀ → k₀ ≤ khi → ∃ k : Fin R.N,
        R.arcSet k = {z : ℂ | z.re = o + (jhi + 1) * hm ∧ z.im ∈ Icc (o + k₀ * hm) (cy (jhi, k₀))}) ∧
      (∀ k₀ : ℤ, klo ≤ k₀ → k₀ ≤ khi → ∃ k : Fin R.N,
        R.arcSet k = {z : ℂ | z.re = o + (jhi + 1) * hm ∧
          z.im ∈ Icc (cy (jhi, k₀)) (o + (k₀ + 1) * hm)}) := by
  exact WindowPerimeter.exists_window_perimeter (o := o) (hm := hm) (hhm := hhm) (jlo := jlo) (jhi := jhi) (klo := klo) (khi := khi) (hj := hj) (hk := hk) (cy := cy) (hcy := hcy) (hx₀ := hx₀) (hx₁ := hx₁) (hy₀ := hy₀) (hy₁ := hy₁) (hcy0 := hcy0)

end AlgebraicCurve.RadialRegion
