/-
  Factorisable test functions on `GL₂(𝔸_K)`.

  A test function `f : GL₂(𝔸_K) → ℂ` is *factorisable* when it is a product of
  an archimedean factor `fa` and a finite factor `ff`, pulled back along the
  adelic projections `glArch`/`glFin`:
  `f g = fa (glArch g) * ff (glFin g)`. The archimedean factor is required to be
  a `C^∞` function of the mixed archimedean coordinates (`archEntries`) and
  compactly supported; the finite factor is locally constant and compactly
  supported. This is FLT's class of test functions for the adelic
  (Godement–Jacquet / Tate) constructions.

  Transcribed verbatim from
  `Definitions/Def_AutomorphicForm_FactorizableTestFn.lean:1–66` (pinned
  `aa2d8b3`). The `_zero` and `eq_zero_of_glArch`/`eq_zero_of_glFin` interface
  lemmas are carried with it: they are the cheap consequences downstream
  consumers use, and the target theorem's cone reaches `isFactorizableTestFn_zero`
  as its non-vacuity witness.

  The `archEntries` projection rests on mathlib's
  `NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace`, so the mixed archimedean
  coordinates are mathlib's `mixedEmbedding.mixedSpace`, adopted as the interface
  from the first declaration.
-/
import FLTForHuman.NumberTheory.AdelicLevel.Projections
import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.LocallyConstant.Basic

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped Classical

namespace AutomorphicForm

variable (F : Type) [Field F]

/-- The archimedean coordinates of `g : GL₂(K_∞)`: the `2 × 2` matrix of mixed
embeddings of its entries, via `ringEquiv_mixedSpace`. -/
def archEntries (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F :=
  fun i j => InfiniteAdeleRing.ringEquiv_mixedSpace F
    ((g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j)

theorem archEntries_apply (g : GL (Fin 2) (InfiniteAdeleRing F)) (i j : Fin 2) :
    archEntries F g i j = InfiniteAdeleRing.ringEquiv_mixedSpace F
      ((g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) :=
  rfl

variable [NumberField F]

/-- The archimedean test factor: a compactly supported `C^∞` function of the
mixed archimedean coordinates. -/
def IsArchTestFactor (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) : Prop :=
  (∃ Φ : (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ ∀ g, fa g = Φ (archEntries F g)) ∧
    HasCompactSupport fa

theorem isArchTestFactor_zero : IsArchTestFactor F (fun _ => 0) :=
  ⟨⟨fun _ => 0, contDiff_const, fun _ => rfl⟩, HasCompactSupport.zero⟩

/-- The finite test factor: locally constant and compactly supported. -/
def IsFinTestFactor (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) : Prop :=
  IsLocallyConstant ff ∧ HasCompactSupport ff

/-- A factorisable test function: a product of an archimedean and a finite test
factor, pulled back along the two adelic projections. -/
def IsFactorizableTestFn (f : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ) : Prop :=
  ∃ (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ),
    IsArchTestFactor F fa ∧ IsFinTestFactor F ff ∧
      ∀ g, f g = fa (AdelicLevel.glArch (𝓞 F) F g) * ff (AdelicLevel.glFin (𝓞 F) F g)

theorem isFinTestFactor_zero : IsFinTestFactor F (fun _ => 0) :=
  ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩

theorem isFactorizableTestFn_zero : IsFactorizableTestFn F (fun _ => 0) :=
  ⟨fun _ => 0, fun _ => 0, isArchTestFactor_zero F, isFinTestFactor_zero F,
    fun _ => (mul_zero _).symm⟩

theorem IsFactorizableTestFn.eq_zero_of_glArch {f : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ}
    {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hf : ∀ g, f g = fa (AdelicLevel.glArch (𝓞 F) F g) * ff (AdelicLevel.glFin (𝓞 F) F g))
    {g : GL (Fin 2) (AdeleRing (𝓞 F) F)} (hg : fa (AdelicLevel.glArch (𝓞 F) F g) = 0) :
    f g = 0 := by
  rw [hf g, hg, zero_mul]

theorem IsFactorizableTestFn.eq_zero_of_glFin {f : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ}
    {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hf : ∀ g, f g = fa (AdelicLevel.glArch (𝓞 F) F g) * ff (AdelicLevel.glFin (𝓞 F) F g))
    {g : GL (Fin 2) (AdeleRing (𝓞 F) F)} (hg : ff (AdelicLevel.glFin (𝓞 F) F g) = 0) :
    f g = 0 := by
  rw [hf g, hg, mul_zero]

end AutomorphicForm

end
