/-
The complex line-integral interface on the places of a curve: the coordinate
function `dCoordFn` and its two defining properties, the chart reading
`chartRead` of a function, the differential reading `readDifferential`, the
primitive-along-a-path predicate `IsPrimitiveAlong`, the path integral
`pathIntegral`, the Abel–Jacobi vector/divisor maps and the path-period
lattice, after FLT's
`Definitions/Def_AlgebraicCurve_ComplexLineIntegral.lean`
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_ComplexLineIntegral.lean>).

`v.dCoordFn` is the function realising the pin's `exists_ord_eq_one_and_dCoord_eq`
(`ord = 1` and `dCoord = D K F dCoordFn`), `v.chartRead f` reads `f` through the
extended chart at `v`, and `v.readDifferential ω` is the chart-pullback of `ω`
multiplied by the derivative of the coordinate. `pathIntegral ω γ` is the
endpoint difference of a primitive of `ω` along `γ` (and `0` when none exists);
`abelJacobiVec`/`abelJacobiDiv` assemble these into the Abel–Jacobi map of the
divisor group, whose image on loops spans the lattice `pathPeriodLattice`.

The pin's `import Mathlib` is replaced by specific mathlib imports; the pin's
names, namespaces, statements and proofs are kept verbatim.
-/
import FLTForHuman.AlgebraicCurve.Defs.PlaceEvaluation
import FLTForHuman.AlgebraicCurve.Defs.Divisor
import FLTForHuman.AlgebraicCurve.Defs.RegularDifferentials
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Topology.Path
import Mathlib.Topology.UnitInterval

set_option autoImplicit false

noncomputable section

open scoped Manifold Topology

namespace AlgebraicCurve

namespace Place

section general

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

def dCoordFn (v : Place K F) : F :=
  Classical.choose v.exists_ord_eq_one_and_dCoord_eq

theorem ord_dCoordFn (v : Place K F) : v.ord v.dCoordFn = 1 :=
  (Classical.choose_spec v.exists_ord_eq_one_and_dCoord_eq).1

theorem dCoord_eq_D_dCoordFn (v : Place K F) :
    v.dCoord = KaehlerDifferential.D K F v.dCoordFn :=
  (Classical.choose_spec v.exists_ord_eq_one_and_dCoord_eq).2

end general

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

def chartRead (v : Place ℂ F) (f : F) : ℂ → ℂ :=
  fun z => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f

theorem chartRead_apply (v : Place ℂ F) (f : F) (z : ℂ) :
    v.chartRead f z = Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f := rfl

def readDifferential (v : Place ℂ F) (ω : Ω[F⁄ℂ]) : ℂ → ℂ :=
  fun z => v.chartRead (v.differentialCoeff ω) z * deriv (v.chartRead v.dCoordFn) z

theorem readDifferential_apply (v : Place ℂ F) (ω : Ω[F⁄ℂ]) (z : ℂ) :
    v.readDifferential ω z =
      v.chartRead (v.differentialCoeff ω) z * deriv (v.chartRead v.dCoordFn) z := rfl

end Place

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

def IsPrimitiveAlong (ω : Ω[F⁄ℂ]) {P Q : Place ℂ F} (γ : Path P Q) (g : unitInterval → ℂ) :
    Prop :=
  ∀ t₀ : unitInterval, ∃ Φ : ℂ → ℂ,
    (∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) (γ t₀) (γ t₀)),
        HasDerivAt Φ ((γ t₀).readDifferential ω z) z) ∧
      ∀ᶠ t in 𝓝 t₀, g t = Φ (extChartAt 𝓘(ℂ, ℂ) (γ t₀) (γ t))

open Classical in

def pathIntegral (ω : Ω[F⁄ℂ]) {P Q : Place ℂ F} (γ : Path P Q) : ℂ :=
  if h : ∃ g, IsPrimitiveAlong ω γ g then h.choose 1 - h.choose 0 else 0

open Classical in
theorem pathIntegral_def (ω : Ω[F⁄ℂ]) {P Q : Place ℂ F} (γ : Path P Q) :
    pathIntegral ω γ = if h : ∃ g, IsPrimitiveAlong ω γ g then h.choose 1 - h.choose 0 else 0 :=
  rfl

open Classical in

def abelJacobiVec {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (P₀ P : Place ℂ F) : Fin n → ℂ :=
  if h : Nonempty (Path P₀ P) then fun i => pathIntegral (b i) (Classical.choice h) else 0

open Classical in
theorem abelJacobiVec_def {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (P₀ P : Place ℂ F) :
    abelJacobiVec b P₀ P =
      if h : Nonempty (Path P₀ P) then fun i => pathIntegral (b i) (Classical.choice h) else 0 :=
  rfl

def abelJacobiDiv {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (P₀ : Place ℂ F) :
    Divisor ℂ F →+ (Fin n → ℂ) :=
  Finsupp.liftAddHom fun v => zmultiplesHom (Fin n → ℂ) (abelJacobiVec b P₀ v)

@[simp]
theorem abelJacobiDiv_single {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (P₀ v : Place ℂ F) (m : ℤ) :
    abelJacobiDiv b P₀ (Finsupp.single v m) = m • abelJacobiVec b P₀ v := by
  simp [abelJacobiDiv]

theorem abelJacobiDiv_apply {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (P₀ : Place ℂ F) (D : Divisor ℂ F) :
    abelJacobiDiv b P₀ D = D.sum fun v m => m • abelJacobiVec b P₀ v := by
  simp only [abelJacobiDiv, Finsupp.liftAddHom_apply]
  rfl

def pathPeriodLattice {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) : Submodule ℤ (Fin n → ℂ) :=
  Submodule.span ℤ {u | ∃ (P : Place ℂ F) (γ : Path P P), u = fun i => pathIntegral (b i) γ}

theorem mem_pathPeriodLattice_of_loop {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) {P : Place ℂ F}
    (γ : Path P P) : (fun i => pathIntegral (b i) γ) ∈ pathPeriodLattice b :=
  Submodule.subset_span ⟨P, γ, rfl⟩

end AlgebraicCurve
