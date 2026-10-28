/-
Push-forward and pull-back of Kähler differentials along an `K`-algebra map, and their
composite `Differential.correspondence`, after FLT's
`Definitions/Def_AlgebraicCurve_DifferentialPushPull.lean` (79 ln)
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DifferentialPushPull.lean>).

This is the differential-level analogue of `Defs/Correspondence.lean`'s divisor-level
`pullbackAlong`/`pushforwardAlong`/`correspondence`: `pullbackAlong φ` is
`KaehlerDifferential.map` restricted along `φ`, `traceAlong φ` is the trace of the
(separable) extension `F/F'`, and `correspondence φ ψ = traceAlong φ ∘ pullbackAlong ψ`.
It is the definition layer of `ModularCurve/Defs/HeckeDifferential.lean`'s `heckeDiffAlong`.

Statements are transcribed verbatim; the pin's `import Mathlib` is replaced by the
specific imports below, and its `import Definitions.Def_AlgebraicCurve_Correspondence`
by the ported `Defs.Correspondence` (which supplies `algebraAlong`,
`isScalarTower_along` and `SeparableAlong`).
spec-pin: Definitions/Def_AlgebraicCurve_DifferentialPushPull.lean
spec-pin: Theorems/Thm_AlgebraicCurve_Differential_pullbackAlong_traceAlong_eq_sum_lifts.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Differential_pullbackAlong_traceAlong_eq_sum_lifts.lean
-/
import FLTForHuman.AlgebraicCurve.Defs.Correspondence
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Trace.Defs
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.TensorProduct.Maps

set_option autoImplicit false

-- The pin's `letI`/`haveI` walls are load-bearing: `pullbackAlong` unfolds only with the
-- local `Algebra F F'`/`IsScalarTower K F F'` instances in scope, and `traceAlong`'s
-- `dite` defeq needs the local `IsSeparable`/`FormallyEtale` binders (SET-1 §3). Keep them
-- literal rather than weaken the proofs.
set_option linter.style.haveILetI false

noncomputable section

open KaehlerDifferential TensorProduct

namespace AlgebraicCurve

namespace Differential

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

def pullbackAlong (φ : F →ₐ[K] F') : Ω[F⁄K] →ₗ[K] Ω[F'⁄K] :=
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  (KaehlerDifferential.map K K F F').restrictScalars K

theorem pullbackAlong_D (φ : F →ₐ[K] F') (f : F) :
    pullbackAlong φ (D K F f) = D K F' (φ f) := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  exact KaehlerDifferential.map_D K K F F' f

theorem pullbackAlong_smul (φ : F →ₐ[K] F') (f : F) (ω : Ω[F⁄K]) :
    pullbackAlong φ (f • ω) = φ f • pullbackAlong φ ω := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  show KaehlerDifferential.map K K F F' (f • ω) = _
  rw [LinearMap.map_smul_of_tower]
  rfl

open Classical in

def traceAlong (φ : F →ₐ[K] F') : Ω[F'⁄K] →ₗ[K] Ω[F⁄K] :=
  if h : SeparableAlong K φ then
    letI := algebraAlong φ
    haveI := isScalarTower_along φ
    haveI : Algebra.IsSeparable F F' := h
    haveI : Algebra.FormallyEtale F F' := Algebra.FormallyEtale.of_isSeparable F F'
    ((TensorProduct.lid F Ω[F⁄K]).toLinearMap ∘ₗ
      (Algebra.trace F F').rTensor Ω[F⁄K] ∘ₗ
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K F F').symm.toLinearMap).restrictScalars K
  else 0

theorem traceAlong_smul_pullbackAlong (φ : F →ₐ[K] F') (h : SeparableAlong K φ) (u : F')
    (ω : Ω[F⁄K]) :
    traceAlong φ (u • pullbackAlong φ ω) =
      (letI := algebraAlong φ; Algebra.trace F F' u) • ω := by
  letI := algebraAlong φ
  have := isScalarTower_along φ
  have : Algebra.IsSeparable F F' := h
  haveI : Algebra.FormallyEtale F F' := Algebra.FormallyEtale.of_isSeparable F F'
  rw [traceAlong, dite_eq_left h]
  simp only [LinearMap.coe_restrictScalars, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply]
  have hsymm : (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K F F').symm
      (u • pullbackAlong φ ω) = u ⊗ₜ ω := by
    rw [LinearEquiv.symm_apply_eq, KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
      KaehlerDifferential.mapBaseChange_tmul]
    rfl
  rw [hsymm, LinearMap.rTensor_tmul, TensorProduct.lid_tmul]

theorem traceAlong_of_not (φ : F →ₐ[K] F') (h : ¬ SeparableAlong K φ) : traceAlong φ = 0 := by
  rw [traceAlong, dite_eq_right h]

def correspondence (φ ψ : F →ₐ[K] F') : Ω[F⁄K] →ₗ[K] Ω[F⁄K] :=
  traceAlong φ ∘ₗ pullbackAlong ψ

theorem correspondence_apply (φ ψ : F →ₐ[K] F') (ω : Ω[F⁄K]) :
    correspondence φ ψ ω = traceAlong φ (pullbackAlong ψ ω) := rfl

end Differential

/-! ## The trace/pull-back identity along a finite separable map

The leaf `pullbackAlong_traceAlong_eq_sum_lifts`: pulling back the trace along a
finite separable `φ` at `e` is the sum of the pull-backs along the lifts `σ` of `e`
through `φ`. The helpers below are the pin `S_` file's, kept at its names and in
its `TraceAtPoints` namespace. -/

namespace TraceAtPoints

variable {K F F' E : Type*} [Field K] [Field F] [Field F'] [Field E]
  [Algebra K F] [Algebra K F'] [Algebra K E]

theorem pullbackAlong_pullbackAlong (ψ : F →ₐ[K] F') (σ : F' →ₐ[K] E) (ω : Ω[F⁄K]) :
    Differential.pullbackAlong σ (Differential.pullbackAlong ψ ω) =
      Differential.pullbackAlong (σ.comp ψ) ω := by
  have hmem : ω ∈ Submodule.span F (Set.range (D K F)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hmem using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨f, rfl⟩ := hx
      simp only [Differential.pullbackAlong_D, AlgHom.coe_comp, Function.comp_apply]
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx =>
      rw [Differential.pullbackAlong_smul, Differential.pullbackAlong_smul,
        Differential.pullbackAlong_smul, hx]
      rfl

def liftsAlong (φ : F →ₐ[K] F') (e : F →ₐ[K] E) : Set (F' →ₐ[K] E) := {σ | σ.comp φ = e}

theorem mem_liftsAlong (φ : F →ₐ[K] F') (e : F →ₐ[K] E) (σ : F' →ₐ[K] E) :
    σ ∈ liftsAlong φ e ↔ σ.comp φ = e := Iff.rfl

theorem liftsAlong_eq_range (φ : F →ₐ[K] F') (e : F →ₐ[K] E)
    [Algebra F F'] [IsScalarTower K F F'] [Algebra F E] [IsScalarTower K F E]
    (hφ : ∀ x, algebraMap F F' x = φ x) (he : ∀ x, algebraMap F E x = e x) :
    liftsAlong φ e = Set.range (fun τ : F' →ₐ[F] E => τ.restrictScalars K) := by
  ext σ
  constructor
  · intro hσ
    refine ⟨{ σ.toRingHom with commutes' := fun x => ?_ }, ?_⟩
    · simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
        MonoidHom.coe_coe, hφ, he]
      exact congrArg (fun g : F →ₐ[K] E => g x) hσ
    · ext x; rfl
  · rintro ⟨τ, rfl⟩
    show (τ.restrictScalars K).comp φ = e
    ext x
    simp only [AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply]
    rw [← hφ, τ.commutes, he]

theorem sum_eq_sum_algHom (φ : F →ₐ[K] F') (e : F →ₐ[K] E)
    (S : Finset (F' →ₐ[K] E)) (hS : ∀ σ : F' →ₐ[K] E, σ ∈ S ↔ σ.comp φ = e)
    [Algebra F F'] [IsScalarTower K F F'] [Algebra F E] [IsScalarTower K F E]
    (hφ : ∀ x, algebraMap F F' x = φ x) (he : ∀ x, algebraMap F E x = e x)
    [Fintype (F' →ₐ[F] E)] {M : Type*} [AddCommMonoid M] (g : (F' →ₐ[K] E) → M) :
    ∑ σ ∈ S, g σ = ∑ τ : F' →ₐ[F] E, g (τ.restrictScalars K) := by
  classical
  have hset : S = Finset.univ.image (fun τ : F' →ₐ[F] E => τ.restrictScalars K) := by
    ext σ
    rw [hS, ← mem_liftsAlong, liftsAlong_eq_range φ e hφ he]
    simp only [Set.mem_range, Finset.mem_image, Finset.mem_univ, true_and]
  rw [hset, Finset.sum_image]
  intro τ₁ _ τ₂ _ h
  exact AlgHom.restrictScalars_injective K h

theorem pullbackAlong_traceAlong_eq_sum [IsAlgClosed E] (φ : F →ₐ[K] F')
    (hfin : FiniteAlong K φ) (hsep : SeparableAlong K φ) (e : F →ₐ[K] E)
    (S : Finset (F' →ₐ[K] E)) (hS : ∀ σ : F' →ₐ[K] E, σ ∈ S ↔ σ.comp φ = e)
    (ω' : Ω[F'⁄K]) :
    Differential.pullbackAlong e (Differential.traceAlong φ ω') =
      ∑ σ ∈ S, Differential.pullbackAlong σ ω' := by
  letI : Algebra F F' := algebraAlong φ
  haveI := isScalarTower_along φ
  letI : Algebra F E := e.toRingHom.toAlgebra
  haveI : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq (fun x => (e.commutes x).symm)
  haveI : Module.Finite F F' := hfin
  haveI : Algebra.IsSeparable F F' := hsep
  haveI : Algebra.FormallyEtale F F' := Algebra.FormallyEtale.of_isSeparable F F'
  obtain ⟨t, rfl⟩ := (tensorKaehlerEquivOfFormallyEtale K F F').surjective ω'
  induction t using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, Finset.sum_add_distrib]
  | tmul u ω =>
      have htm : (tensorKaehlerEquivOfFormallyEtale K F F') (u ⊗ₜ ω) =
          u • Differential.pullbackAlong φ ω := by
        rw [tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul]
        rfl
      rw [htm, Differential.traceAlong_smul_pullbackAlong φ hsep, Differential.pullbackAlong_smul]
      have hrhs : ∀ σ ∈ S,
          Differential.pullbackAlong σ (u • Differential.pullbackAlong φ ω) =
            σ u • Differential.pullbackAlong e ω := by
        intro σ hσ
        rw [Differential.pullbackAlong_smul, pullbackAlong_pullbackAlong, (hS σ).1 hσ]
      rw [Finset.sum_congr rfl hrhs, ← Finset.sum_smul,
        sum_eq_sum_algHom φ e S hS (fun _ => rfl) (fun _ => rfl) (fun σ => σ u)]
      congr 1
      have h := trace_eq_sum_embeddings E (K := F) (L := F') (x := u)
      simp only [AlgHom.coe_restrictScalars'] at h ⊢
      exact h

end TraceAtPoints

namespace Differential

theorem pullbackAlong_traceAlong_eq_sum_lifts
    (K F F' E : Type*) [Field K] [Field F] [Field F'] [Field E]
    [Algebra K F] [Algebra K F'] [Algebra K E] [IsAlgClosed E]
    (φ : F →ₐ[K] F') (hfin : FiniteAlong K φ) (hsep : SeparableAlong K φ)
    (e : F →ₐ[K] E) (S : Finset (F' →ₐ[K] E)) (hS : ∀ σ : F' →ₐ[K] E, σ ∈ S ↔ σ.comp φ = e)
    (ω' : Ω[F'⁄K]) :
    Differential.pullbackAlong e (Differential.traceAlong φ ω') =
      ∑ σ ∈ S, Differential.pullbackAlong σ ω' :=
  TraceAtPoints.pullbackAlong_traceAlong_eq_sum φ hfin hsep e S hS ω'

end Differential

end AlgebraicCurve

end
