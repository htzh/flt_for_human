/-
The public headline `AlgebraicCurve.RadialRegion.exists_grid_geometry`: a
rectangular grid of per-cell control points inside their squares is a radial
region whose arcs are the cell sides and whose geometry is the stated grid data.

Tier 1 over the tier-3 engine
`FLTForHuman/AlgebraicCurve/RadialRegion/Engine/GridGeometry.lean`. The statement
is the pin's `Theorems/Thm_AlgebraicCurve_RadialRegion_exists_grid_geometry.lean`
wrapper verbatim -- that wrapper, not the pin's `S_` top-level `solution`, is the
checker's statement authority -- and the proof is the one-line application of the
engine's kernel `AlgebraicCurve.RadialRegion.GridGeometry.exists_grid_geometry`,
exactly as the pin's `solution` forwards to it.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_RadialRegion_exists_grid_geometry.lean>
-/
import FLTForHuman.AlgebraicCurve.RadialRegion.Engine.GridGeometry

set_option autoImplicit false

open scoped Real
open AlgebraicCurve Set

namespace AlgebraicCurve.RadialRegion

-- pin: exists_grid_geometry (Theorems/Thm_AlgebraicCurve_RadialRegion_exists_grid_geometry.lean:8)
theorem exists_grid_geometry (o hm : ℝ) (hhm : 0 < hm) (jlo jhi klo khi : ℤ)
    (hjlt : jlo + 1 < jhi) (hklt : klo + 1 < khi) (ctr : ℤ × ℤ → ℂ)
    (hctr : ∀ p : ℤ × ℤ, (o + p.1 * hm < (ctr p).re ∧ (ctr p).re < o + (p.1 + 1) * hm) ∧
      (o + p.2 * hm < (ctr p).im ∧ (ctr p).im < o + (p.2 + 1) * hm))
    (hzero : (o + jlo * hm < 0 ∧ 0 < o + (jhi + 1) * hm) ∧ (o + klo * hm < 0 ∧
      0 < o + (khi + 1) * hm))
    (hcy0 : ∀ k : ℤ, o + k * hm < 0 → 0 < o + (k + 1) * hm → (ctr (jhi, k)).im = 0)
    (base : ℤ × ℤ → RadialRegion)
    (hbase : ∀ p : ℤ × ℤ,
      (base p).q = ctr p ∧ (base p).N = 6 ∧
      (base p).K = {z : ℂ | z.re ∈ Icc (o + p.1 * hm) (o + (p.1 + 1) * hm) ∧
        z.im ∈ Icc (o + p.2 * hm) (o + (p.2 + 1) * hm)} ∧
      (base p).Kint = {z : ℂ | z.re ∈ Ioo (o + p.1 * hm) (o + (p.1 + 1) * hm) ∧
        z.im ∈ Ioo (o + p.2 * hm) (o + (p.2 + 1) * hm)} ∧
      (∀ k : Fin (base p).N, k.val = 0 → (base p).arcSet k = {z : ℂ | z.re = (o + (p.1 + 1) * hm) ∧
        z.im ∈ Icc (ctr p).im (o + (p.2 + 1) * hm)}) ∧
      (∀ k : Fin (base p).N, k.val = 1 → (base p).arcSet k = {z : ℂ | z.im = (o + (p.2 + 1) * hm) ∧
        z.re ∈ Icc (o + p.1 * hm) (o + (p.1 + 1) * hm)}) ∧
      (∀ k : Fin (base p).N, k.val = 2 → (base p).arcSet k = {z : ℂ | z.re = (o + p.1 * hm) ∧
        z.im ∈ Icc (if p.1 = jlo then (ctr p).im else (ctr (p.1 - 1, p.2)).im)
          (o + (p.2 + 1) * hm)}) ∧
      (∀ k : Fin (base p).N, k.val = 3 → (base p).arcSet k = {z : ℂ | z.re = (o + p.1 * hm) ∧
        z.im ∈ Icc (o + p.2 * hm) (if p.1 = jlo then (ctr p).im else (ctr (p.1 - 1, p.2)).im)}) ∧
      (∀ k : Fin (base p).N, k.val = 4 → (base p).arcSet k = {z : ℂ | z.im = (o + p.2 * hm) ∧
        z.re ∈ Icc (o + p.1 * hm) (o + (p.1 + 1) * hm)}) ∧
      (∀ k : Fin (base p).N, k.val = 5 → (base p).arcSet k = {z : ℂ | z.re = (o + (p.1 + 1) * hm) ∧
        z.im ∈ Icc (o + p.2 * hm) (ctr p).im}) ∧
      (∀ k : Fin ((base p).N + 1), k.val = 0 →
        (base p).loop ((base p).φs k) = ⟨(o + (p.1 + 1) * hm), (ctr p).im⟩) ∧
      (∀ k : Fin ((base p).N + 1), k.val = 1 →
        (base p).loop ((base p).φs k) = ⟨(o + (p.1 + 1) * hm), (o + (p.2 + 1) * hm)⟩) ∧
      (∀ k : Fin ((base p).N + 1), k.val = 2 →
        (base p).loop ((base p).φs k) = ⟨(o + p.1 * hm), (o + (p.2 + 1) * hm)⟩) ∧
      (∀ k : Fin ((base p).N + 1), k.val = 3 →
        (base p).loop ((base p).φs k) = ⟨(o + p.1 * hm), (if p.1 = jlo then (ctr p).im else (ctr
          (p.1 - 1, p.2)).im)⟩) ∧
      (∀ k : Fin ((base p).N + 1), k.val = 4 →
        (base p).loop ((base p).φs k) = ⟨(o + p.1 * hm), (o + p.2 * hm)⟩) ∧
      (∀ k : Fin ((base p).N + 1), k.val = 5 →
        (base p).loop ((base p).φs k) = ⟨(o + (p.1 + 1) * hm), (o + p.2 * hm)⟩) ∧
      (∀ k : Fin ((base p).N + 1), k.val = 6 →
        (base p).loop ((base p).φs k) = ⟨(o + (p.1 + 1) * hm), (ctr p).im⟩) ∧
      (∀ k : Fin (base p).N, k.val = 0 ∨ k.val = 5 →
        (∀ t ∈ (base p).arcIcc k, (base p).r t = (Real.cos t / ((o + (p.1 + 1) * hm) - (ctr p).re))⁻¹)) ∧
      (∀ k : Fin (base p).N, k.val = 1 →
        ∀ t ∈ (base p).arcIcc k, (base p).r t = (Real.sin t / ((o + (p.2 + 1) * hm) - (ctr p).im))⁻¹) ∧
      (∀ k : Fin (base p).N, k.val = 2 ∨ k.val = 3 →
        (∀ t ∈ (base p).arcIcc k, (base p).r t = (-Real.cos t / ((ctr p).re - (o + p.1 * hm)))⁻¹)) ∧
      (∀ k : Fin (base p).N, k.val = 4 →
        ∀ t ∈ (base p).arcIcc k, (base p).r t = (-Real.sin t / ((ctr p).im - (o + p.2 * hm)))⁻¹) ∧
      (∀ k : Fin (base p).N, k.val = 0 → (base p).arcIcc k ⊆ Ico 0 (π / 2)) ∧
      (∀ k : Fin (base p).N, k.val = 1 → (base p).arcIcc k ⊆ Ioo 0 π) ∧
      (∀ k : Fin (base p).N, k.val = 2 ∨ k.val = 3 → (base p).arcIcc k ⊆ Ioo (π / 2) (3 * π / 2)) ∧
      (∀ k : Fin (base p).N, k.val = 4 → (base p).arcIcc k ⊆ Ioo π (2 * π)) ∧
      (∀ k : Fin (base p).N, k.val = 5 → (base p).arcIcc k ⊆ Ioc (3 * π / 2) (2 * π)) ∧
      (∀ z ∈ (base p).K, z ∉ (base p).Kint →
        (base p).loop (if Complex.arg (z - ctr p) < 0 then Complex.arg
          (z - ctr p) + 2 * π else Complex.arg (z - ctr p))
          = z) ∧
      (∀ (k : Fin (base p).N) (t₁ t₂ : ℝ), t₁ ∈ (base p).arcIcc k → t₂ ∈ (base p).arcIcc k →
        t₁ ≤ t₂ →
        (base p).loop '' Icc t₁ t₂ = segment ℝ ((base p).loop t₁) ((base p).loop t₂)))
    (winReg : RadialRegion)
    (hwin :
      winReg.q = 0 ∧
      winReg.K = {z : ℂ | z.re ∈ Icc (o + jlo * hm) (o + (jhi + 1) * hm) ∧
        z.im ∈ Icc (o + klo * hm) (o + (khi + 1) * hm)} ∧
      winReg.Kint = {z : ℂ | z.re ∈ Ioo (o + jlo * hm) (o + (jhi + 1) * hm) ∧
        z.im ∈ Ioo (o + klo * hm) (o + (khi + 1) * hm)} ∧
      winReg.N = 2 * (jhi - jlo + 1).toNat + 4 * (khi - klo + 1).toNat ∧
      (∀ k k' : Fin winReg.N, winReg.arcSet k = winReg.arcSet k' → k = k') ∧
      (∀ k : Fin winReg.N,
        (∃ j : ℤ, jlo ≤ j ∧ j ≤ jhi ∧
          winReg.arcSet k = {z : ℂ | z.im = o + klo * hm ∧
            z.re ∈ Icc (o + j * hm) (o + (j + 1) * hm)} ∧
          winReg.loop (winReg.φs k.castSucc) = ⟨o + j * hm, o + klo * hm⟩ ∧
          winReg.loop (winReg.φs k.succ) = ⟨o + (j + 1) * hm, o + klo * hm⟩ ∧
          (∀ t ∈ winReg.arcIcc k, winReg.r t = (-Real.sin t / (-(o + klo * hm)))⁻¹) ∧
          winReg.arcIcc k ⊆ Ioo π (2 * π)) ∨
        (∃ j : ℤ, jlo ≤ j ∧ j ≤ jhi ∧
          winReg.arcSet k = {z : ℂ | z.im = o + (khi + 1) * hm ∧
            z.re ∈ Icc (o + j * hm) (o + (j + 1) * hm)} ∧
          winReg.loop (winReg.φs k.castSucc) = ⟨o + (j + 1) * hm, o + (khi + 1) * hm⟩ ∧
          winReg.loop (winReg.φs k.succ) = ⟨o + j * hm, o + (khi + 1) * hm⟩ ∧
          (∀ t ∈ winReg.arcIcc k, winReg.r t = (Real.sin t / (o + (khi + 1) * hm))⁻¹) ∧
          winReg.arcIcc k ⊆ Ioo 0 π) ∨
        (∃ k₀ : ℤ, klo ≤ k₀ ∧ k₀ ≤ khi ∧
          winReg.arcSet k = {z : ℂ | z.re = o + jlo * hm ∧
            z.im ∈ Icc ((ctr (jlo, k₀)).im) (o + (k₀ + 1) * hm)} ∧
          winReg.loop (winReg.φs k.castSucc) = ⟨o + jlo * hm, o + (k₀ + 1) * hm⟩ ∧
          winReg.loop (winReg.φs k.succ) = ⟨o + jlo * hm, (ctr (jlo, k₀)).im⟩ ∧
          (∀ t ∈ winReg.arcIcc k, winReg.r t = (-Real.cos t / (-(o + jlo * hm)))⁻¹) ∧
          winReg.arcIcc k ⊆ Ioo (π / 2) (3 * π / 2)) ∨
        (∃ k₀ : ℤ, klo ≤ k₀ ∧ k₀ ≤ khi ∧
          winReg.arcSet k = {z : ℂ | z.re = o + jlo * hm ∧
            z.im ∈ Icc (o + k₀ * hm) ((ctr (jlo, k₀)).im)} ∧
          winReg.loop (winReg.φs k.castSucc) = ⟨o + jlo * hm, (ctr (jlo, k₀)).im⟩ ∧
          winReg.loop (winReg.φs k.succ) = ⟨o + jlo * hm, o + k₀ * hm⟩ ∧
          (∀ t ∈ winReg.arcIcc k, winReg.r t = (-Real.cos t / (-(o + jlo * hm)))⁻¹) ∧
          winReg.arcIcc k ⊆ Ioo (π / 2) (3 * π / 2)) ∨
        (∃ k₀ : ℤ, klo ≤ k₀ ∧ k₀ ≤ khi ∧
          winReg.arcSet k = {z : ℂ | z.re = o + (jhi + 1) * hm ∧
            z.im ∈ Icc (o + k₀ * hm) ((ctr (jhi, k₀)).im)} ∧
          winReg.loop (winReg.φs k.castSucc) = ⟨o + (jhi + 1) * hm, o + k₀ * hm⟩ ∧
          winReg.loop (winReg.φs k.succ) = ⟨o + (jhi + 1) * hm, (ctr (jhi, k₀)).im⟩ ∧
          (∀ t ∈ winReg.arcIcc k, winReg.r t = (Real.cos t / (o + (jhi + 1) * hm))⁻¹) ∧
          (winReg.arcIcc k ⊆ Ioo (-(π / 2)) (π / 2) ∨
            winReg.arcIcc k ⊆ Ioo (3 * π / 2) (5 * π / 2))) ∨
        (∃ k₀ : ℤ, klo ≤ k₀ ∧ k₀ ≤ khi ∧
          winReg.arcSet k = {z : ℂ | z.re = o + (jhi + 1) * hm ∧
            z.im ∈ Icc ((ctr (jhi, k₀)).im) (o + (k₀ + 1) * hm)} ∧
          winReg.loop (winReg.φs k.castSucc) = ⟨o + (jhi + 1) * hm, (ctr (jhi, k₀)).im⟩ ∧
          winReg.loop (winReg.φs k.succ) = ⟨o + (jhi + 1) * hm, o + (k₀ + 1) * hm⟩ ∧
          (∀ t ∈ winReg.arcIcc k, winReg.r t = (Real.cos t / (o + (jhi + 1) * hm))⁻¹) ∧
          (winReg.arcIcc k ⊆ Ioo (-(π / 2)) (π / 2) ∨
            winReg.arcIcc k ⊆ Ioo (3 * π / 2) (5 * π / 2)))) ∧
      (∀ j : ℤ, jlo ≤ j → j ≤ jhi → ∃ k : Fin winReg.N,
        winReg.arcSet k = {z : ℂ | z.im = o + klo * hm ∧
          z.re ∈ Icc (o + j * hm) (o + (j + 1) * hm)}) ∧
      (∀ j : ℤ, jlo ≤ j → j ≤ jhi → ∃ k : Fin winReg.N,
        winReg.arcSet k = {z : ℂ | z.im = o + (khi + 1) * hm ∧
          z.re ∈ Icc (o + j * hm) (o + (j + 1) * hm)}) ∧
      (∀ k₀ : ℤ, klo ≤ k₀ → k₀ ≤ khi → ∃ k : Fin winReg.N,
        winReg.arcSet k = {z : ℂ | z.re = o + jlo * hm ∧
          z.im ∈ Icc ((ctr (jlo, k₀)).im) (o + (k₀ + 1) * hm)}) ∧
      (∀ k₀ : ℤ, klo ≤ k₀ → k₀ ≤ khi → ∃ k : Fin winReg.N,
        winReg.arcSet k = {z : ℂ | z.re = o + jlo * hm ∧
          z.im ∈ Icc (o + k₀ * hm) ((ctr (jlo, k₀)).im)}) ∧
      (∀ k₀ : ℤ, klo ≤ k₀ → k₀ ≤ khi → ∃ k : Fin winReg.N,
        winReg.arcSet k = {z : ℂ | z.re = o + (jhi + 1) * hm ∧
          z.im ∈ Icc (o + k₀ * hm) ((ctr (jhi, k₀)).im)}) ∧
      (∀ k₀ : ℤ, klo ≤ k₀ → k₀ ≤ khi → ∃ k : Fin winReg.N,
        winReg.arcSet k = {z : ℂ | z.re = o + (jhi + 1) * hm ∧
          z.im ∈ Icc ((ctr (jhi, k₀)).im) (o + (k₀ + 1) * hm)})) :
    ∃ (sqbit : ∀ p : ℤ × ℤ, Fin (base p).N → Bool) (perbit : Fin winReg.N → Bool) (B₀ : Finset ℂ)
      (Shares : Option (ℤ × ℤ) → Set ℂ → Prop) (Contains : Option (ℤ × ℤ) → ℂ → Prop),
      (∀ (p : ℤ × ℤ) (k k' : Fin (base p).N), (base p).arcSet k = (base p).arcSet k' → k = k') ∧
      (∀ p p' : ℤ × ℤ, p ≠ p' → ∀ (k : Fin (base p).N) (k' : Fin (base p').N),
        (base p).arcSet k = (base p').arcSet k' → sqbit p' k' = !sqbit p k) ∧
      (∀ (p : ℤ × ℤ) (k : Fin (base p).N) (k₀ : Fin winReg.N),
        p ∈ Icc jlo jhi ×ˢ Icc klo khi → (base p).arcSet k = winReg.arcSet k₀ →
          perbit k₀ = !sqbit p k) ∧
      (∀ p p' : ℤ × ℤ, p ≠ p' → ∀ (k : Fin (base p).N) (k' : Fin (base p').N),
        (base p).arcSet k = (base p').arcSet k' → sqbit p k = true →
        ∃ ψ : ℝ → ℝ, StrictAntiOn ψ ((base p').arcIcc k') ∧ ContDiffOn ℝ 1 ψ ((base p').arcIcc k') ∧
          ψ ((base p').φs k'.castSucc) = (base p).φs k.succ ∧
          ψ ((base p').φs k'.succ) = (base p).φs k.castSucc ∧
          ∀ t ∈ (base p').arcIcc k', (base p').loop t = (base p).loop (ψ t)) ∧
      (∀ (p : ℤ × ℤ) (k : Fin (base p).N) (k₀ : Fin winReg.N),
        p ∈ Icc jlo jhi ×ˢ Icc klo khi → (base p).arcSet k = winReg.arcSet k₀ → sqbit p k = true →
        ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (winReg.arcIcc k₀) ∧ ContDiffOn ℝ 1 ψ (winReg.arcIcc k₀) ∧
          ψ (winReg.φs k₀.castSucc) = (base p).φs k.castSucc ∧
          ψ (winReg.φs k₀.succ) = (base p).φs k.succ ∧
          ∀ t ∈ winReg.arcIcc k₀, winReg.loop t = (base p).loop (ψ t)) ∧
      (∀ (p : ℤ × ℤ) (k : Fin (base p).N) (k₀ : Fin winReg.N),
        p ∈ Icc jlo jhi ×ˢ Icc klo khi → (base p).arcSet k = winReg.arcSet k₀ → sqbit p k = false →
        ∃ ψ : ℝ → ℝ, StrictMonoOn ψ ((base p).arcIcc k) ∧ ContDiffOn ℝ 1 ψ ((base p).arcIcc k) ∧
          ψ ((base p).φs k.castSucc) = winReg.φs k₀.castSucc ∧
          ψ ((base p).φs k.succ) = winReg.φs k₀.succ ∧
          ∀ t ∈ (base p).arcIcc k, (base p).loop t = winReg.loop (ψ t)) ∧
      (∀ (p : ℤ × ℤ) (Z : Set ℂ), Shares (some p) Z ↔
        p ∈ Icc jlo jhi ×ˢ Icc klo khi ∧ ∃ k : Fin (base p).N, (base p).arcSet k = Z) ∧
      (∀ Z : Set ℂ, Shares none Z ↔ ∃ k₀ : Fin winReg.N, winReg.arcSet k₀ = Z) ∧
      (∀ (p : ℤ × ℤ) (v : ℂ), Contains (some p) v ↔ p ∈ Icc jlo jhi ×ˢ Icc klo khi ∧
        v ∈ (base p).K) ∧
      (∀ v : ℂ, Contains none v ↔ v ∉ winReg.Kint) ∧
      (∀ (ρ : Option (ℤ × ℤ)) (Z : Set ℂ), Shares ρ Z →
        ∃ ρ' : Option (ℤ × ℤ), ρ' ≠ ρ ∧ Shares ρ' Z ∧
          ∀ ρ'' : Option (ℤ × ℤ), Shares ρ'' Z → ρ'' = ρ ∨ ρ'' = ρ') ∧
      (∀ (v : ℂ) (ρ ρ' : Option (ℤ × ℤ)), Contains ρ v → Contains ρ' v →
        Relation.ReflTransGen
          (fun ρ₁ ρ₂ : Option (ℤ × ℤ) => ∃ Z : Set ℂ, Shares ρ₁ Z ∧ Shares ρ₂ Z ∧ v ∈ Z) ρ ρ') ∧
      B₀.card = ((jhi - jlo + 1).toNat + 1) * ((khi - klo + 1).toNat + 1) +
        (jhi - jlo + 1).toNat * (khi - klo + 1).toNat + (khi - klo + 1).toNat ∧
      (∀ p ∈ Icc jlo jhi ×ˢ Icc klo khi, ∀ i : Fin ((base p).N + 1), (base p).loop
        ((base p).φs i) ∈ B₀) ∧
      (∀ i : Fin (winReg.N + 1), winReg.loop (winReg.φs i) ∈ B₀) ∧
      (∀ v ∈ B₀, ∃ p ∈ Icc jlo jhi ×ˢ Icc klo khi, ∃ k : Fin (base p).N,
        v = (base p).loop ((base p).φs k.castSucc) ∨ v = (base p).loop ((base p).φs k.succ)) ∧
      (∀ v ∈ B₀, ∃ j : ℤ, v.re - o = j * hm)
    := by
  exact GridGeometry.exists_grid_geometry (o := o) (hm := hm) (hhm := hhm) (jlo := jlo) (jhi := jhi) (klo := klo) (khi := khi) (hjlt := hjlt) (hklt := hklt) (ctr := ctr) (hctr := hctr) (hzero := hzero) (hcy0 := hcy0) (base := base) (hbase := hbase) (winReg := winReg) (hwin := hwin)

end AlgebraicCurve.RadialRegion
