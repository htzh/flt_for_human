/-
The trace/pull-back algebra of a separable `K`-algebra automorphism — the *shared* block of
the two `ModularCurve` Hecke-correspondence rows:

* `S_ModularCurve_coeffMap_diffQExp_correspondence_diamondAutBar_eq_qExpansion_diamondLinOne`
  (`AutTrace` section, lines 25–100), and
* `S_ModularCurve_coeff_diffQExp_correspondence_heckeBetaOneBar_heckeAlphaOneBar_of_not_dvd`
  (`AutTrace` section, lines 171–210, the same block with its field variable named `L`).

The pin proves this block twice; the port writes it **once**, here, and both row modules import
it. `pullbackAlong_pullbackAlong` is **not** re-declared here: the port already has it at
`AlgebraicCurve/Differential/PushPull.lean` (`TraceAtPoints.pullbackAlong_pullbackAlong`, the
same statement modulo binder order), and consumers use that one directly. No declaration in this
module is a re-statement of an existing port declaration.

**Deliberately unwired (tier 3).** A `spec-pin:` line for either `S_` file would make
`frontier.py --selfcheck` read that row's *headline* as ported (MD-001's failure mode: the
source tier maps an `S_` stem to its node), while this module carries only the block. The
statements below are the pin's text verbatim; the rectification order
(`WORKORDER-MC7d-rectify-engine-homes.md`) re-wires this module to the `S_` file once both rows
have landed, at which point the source claim is true.

Wired (2026-10-27, MC-7d D3) to the `S_` file of the 934 row now that the row is ported, so the
five statements are diffed instead of hand-read.  Not wired: the row's `Them_` wrapper — that
headline is MC-7b's declaration, not this module's.

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_coeffMap_diffQExp_correspondence_diamondAutBar_eq_qExpansion_diamondLinOne.lean
spec-pin: P2M/Sol/S_ModularCurve_coeffMap_diffQExp_correspondence_diamondAutBar_eq_qExpansion_diamondLinOne.lean
-/
import FLTForHuman.AlgebraicCurve.Differential.PushPull
import FLTForHuman.AlgebraicCurve.Defs.Correspondence

set_option autoImplicit false

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve

namespace Differential

section AutTrace

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem pullbackAlong_id (F₁ : Type*) [Field F₁] [Algebra K F₁] (η : Ω[F₁⁄K]) :
    pullbackAlong (AlgHom.id K F₁) η = η := by
  have key : ∀ η : Ω[F₁⁄K], η ∈ Submodule.span F₁ (Set.range (D K F₁)) → ∀ f : F₁,
      pullbackAlong (AlgHom.id K F₁) (f • η) = f • η := by
    intro η hη
    induction hη using Submodule.span_induction with
    | mem η h =>
      obtain ⟨g, rfl⟩ := h
      intro f
      rw [pullbackAlong_smul, pullbackAlong_D, AlgHom.id_apply, AlgHom.id_apply]
    | zero => intro f; simp
    | add x y _ _ hx hy =>
      intro f
      rw [smul_add, map_add, hx, hy]
    | smul a x _ hx => intro f; rw [smul_smul]; exact hx (f * a)
  simpa using key η (by rw [KaehlerDifferential.span_range_derivation]; trivial) 1

theorem separableAlong_algEquiv [CharZero F] (σ : F ≃ₐ[K] F) : SeparableAlong K (σ : F →ₐ[K] F) :=
  letI := algebraAlong (σ : F →ₐ[K] F)
  haveI : Algebra.IsIntegral F F :=
    isIntegral_along (σ : F →ₐ[K] F) (RingHom.isIntegral_of_surjective _ σ.surjective)
  Algebra.IsSeparable.of_integral F F

theorem trace_one_along_algEquiv (σ : F ≃ₐ[K] F) :
    (letI := algebraAlong (σ : F →ₐ[K] F); Algebra.trace F F (1 : F)) = 1 := by
  let inst : Algebra F F := algebraAlong (σ : F →ₐ[K] F)
  have hfr : @Module.finrank F F _ _ (@Algebra.toModule F F _ _ inst) = 1 := by
    refine (@finrank_eq_one_iff_of_nonzero' F F _ _ (@Algebra.toModule F F _ _ inst) (1 : F)
      one_ne_zero).mpr fun w => ⟨σ.symm w, ?_⟩
    show (σ : F →ₐ[K] F).toRingHom (σ.symm w) * 1 = w
    rw [mul_one]
    exact σ.apply_symm_apply w
  have h := @Algebra.trace_algebraMap F F _ _ inst _ _ (1 : F)
  rw [map_one, hfr, one_smul] at h
  exact h

theorem traceAlong_algEquiv [CharZero F] (σ : F ≃ₐ[K] F) (η : Ω[F⁄K]) :
    traceAlong (σ : F →ₐ[K] F) η = pullbackAlong (σ.symm : F →ₐ[K] F) η := by
  set θ := pullbackAlong (σ.symm : F →ₐ[K] F) η with hθ
  have hη : η = pullbackAlong (σ : F →ₐ[K] F) θ := by
    rw [hθ, TraceAtPoints.pullbackAlong_pullbackAlong, AlgEquiv.comp_symm, pullbackAlong_id]
  have h1 := traceAlong_smul_pullbackAlong (σ : F →ₐ[K] F) (separableAlong_algEquiv σ) 1 θ
  rw [one_smul] at h1
  rw [hη, h1, trace_one_along_algEquiv, one_smul]

theorem correspondence_algEquiv_id [CharZero F] (σ : F ≃ₐ[K] F) (η : Ω[F⁄K]) :
    Differential.correspondence (σ : F →ₐ[K] F) (AlgHom.id K F) η =
      pullbackAlong (σ.symm : F →ₐ[K] F) η := by
  rw [correspondence_apply, pullbackAlong_id, traceAlong_algEquiv]

end AutTrace

end Differential

end AlgebraicCurve
