/-
The cell-dissection interface for the complex line integral on a curve: radial
regions (`RadialRegion` with its compact `K`, open `Kint`, boundary loops and
arcs), analytic charts (`AnalyticCoord` with `read`), cells (`Cell` with
`carrier`/`interior'`/`bdry`/`arc`), cell dissections (`CellDissection` with the
bijective side map, edge/vertex ends and reversal, the cover and incidence
conditions), the edge integrand `coeffIn`/`Cell.bdryIntegrand` and the
dissection's `arcOf`/`edgeInt`/`skeleton`, after FLT's
`Definitions/Def_AlgebraicCurve_CellDissection.lean`
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_CellDissection.lean>).

A `RadialRegion` is a star-shaped neighbourhood of `q` described by a
`2π`-periodic positive radius function cut into `N` angular pieces; `Cell` reads
one such region back into the curve through an analytic chart, and
`CellDissection` records a finite cover of the curve by cells whose sides are
identified along the sides of a graph (`side_bij`, `arc_ends`, `arc_rev`,
`cover`, `inter`, `conn`). `coeffIn` is the chart-coordinate coefficient of a
differential and `Cell.bdryIntegrand` its boundary pull-back, so
`CellDissection.edgeInt` is the integral over a graph edge and `skeleton` its
underlying set of arcs.

The pin's `import Mathlib` is replaced by specific mathlib imports; the pin's
names, namespaces, statements and proofs are kept verbatim.
-/
import FLTForHuman.AlgebraicCurve.Defs.PlaceEvaluation
import FLTForHuman.AlgebraicCurve.Defs.ComplexLineIntegral
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.Monotone.Defs
import Mathlib.Topology.OpenPartialHomeomorph.Defs

set_option autoImplicit false

open scoped Manifold ContDiff Topology Real
open Set Complex

namespace AlgebraicCurve

structure RadialRegion where
  q : ℂ
  r : ℝ → ℝ
  hcont : Continuous r
  hper : Function.Periodic r (2 * π)
  hpos : ∀ φ, 0 < r φ
  N : ℕ
  φs : Fin (N + 1) → ℝ
  hφ0 : φs 0 = 0
  hφN : φs (Fin.last N) = 2 * π
  hmono : StrictMono φs
  hC2 : ∀ i : Fin N, ContDiffOn ℝ 2 r (Icc (φs i.castSucc) (φs i.succ))

namespace RadialRegion

def K (R : RadialRegion) : Set ℂ := {z : ℂ | ‖z - R.q‖ ≤ R.r (arg (z - R.q))}

def Kint (R : RadialRegion) : Set ℂ := {z : ℂ | ‖z - R.q‖ < R.r (arg (z - R.q))}

noncomputable def loop (R : RadialRegion) (φ : ℝ) : ℂ := R.q + R.r φ * exp (φ * I)

noncomputable def loop' (R : RadialRegion) (φ : ℝ) : ℂ :=
  (((deriv R.r φ : ℝ) : ℂ) + R.r φ * I) * exp (φ * I)

def arcIcc (R : RadialRegion) (k : Fin R.N) : Set ℝ := Icc (R.φs k.castSucc) (R.φs k.succ)

def arcSet (R : RadialRegion) (k : Fin R.N) : Set ℂ := R.loop '' R.arcIcc k

end RadialRegion

structure AnalyticCoord (F : Type*) [Field F] [Algebra ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] where
  ζ : OpenPartialHomeomorph (Place ℂ F) ℂ
  analytic : ∀ P ∈ ζ.source,
    AnalyticAt ℂ (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) (extChartAt 𝓘(ℂ, ℂ) P P)
  deriv_ne : ∀ P ∈ ζ.source,
    deriv (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) (extChartAt 𝓘(ℂ, ℂ) P P) ≠ 0

namespace AnalyticCoord

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

noncomputable def read (A : AnalyticCoord F) (u : F) : ℂ → ℂ :=
  fun z => Place.evalAt (A.ζ.symm z) u

end AnalyticCoord

structure Cell (F : Type*) [Field F] [Algebra ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] extends AnalyticCoord F where
  R : RadialRegion
  hKt : R.K ⊆ ζ.target

namespace Cell

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

def carrier (C : Cell F) : Set (Place ℂ F) := C.ζ.symm '' C.R.K

def interior' (C : Cell F) : Set (Place ℂ F) := C.ζ.symm '' C.R.Kint

noncomputable def bdry (C : Cell F) (φ : ℝ) : Place ℂ F := C.ζ.symm (C.R.loop φ)

def arc (C : Cell F) (k : Fin C.R.N) : Set (Place ℂ F) := C.ζ.symm '' C.R.arcSet k

end Cell

structure CellDissection (F : Type*) [Field F] [Algebra ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] where

  ιC : Type
  ιE : Type
  ιV : Type
  [fintypeC : Fintype ιC]
  [fintypeE : Fintype ιE]
  [fintypeV : Fintype ιV]
  [decEqC : DecidableEq ιC]
  [decEqE : DecidableEq ιE]
  [decEqV : DecidableEq ιV]
  cell : ιC → Cell F

  side : (C : ιC) → Fin (cell C).R.N → ιE × Bool

  side_bij : Function.Bijective fun p : (Σ C : ιC, Fin (cell C).R.N) => side p.1 p.2

  ends : ιE → ιV × ιV
  vert : ιV → Place ℂ F

  arc_ends : ∀ (C : ιC) (k : Fin (cell C).R.N),
    (cell C).bdry ((cell C).R.φs k.castSucc) =
        vert (if (side C k).2 then (ends (side C k).1).1 else (ends (side C k).1).2) ∧
      (cell C).bdry ((cell C).R.φs k.succ) =
        vert (if (side C k).2 then (ends (side C k).1).2 else (ends (side C k).1).1)

  arc_rev : ∀ (C : ιC) (k : Fin (cell C).R.N) (C' : ιC) (k' : Fin (cell C').R.N),
    (side C k).1 = (side C' k').1 → (side C k).2 = true → (side C' k').2 = false →
    ∃ ψ : ℝ → ℝ,
      StrictAntiOn ψ ((cell C').R.arcIcc k') ∧ ContDiffOn ℝ 1 ψ ((cell C').R.arcIcc k') ∧
      ψ ((cell C').R.φs k'.castSucc) = (cell C).R.φs k.succ ∧
      ψ ((cell C').R.φs k'.succ) = (cell C).R.φs k.castSucc ∧
      ∀ t ∈ (cell C').R.arcIcc k', (cell C').bdry t = (cell C).bdry (ψ t)

  cover : ⋃ C, (cell C).carrier = univ

  inter : ∀ (C C' : ιC) (x : Place ℂ F), x ∈ (cell C).carrier → x ∈ (cell C').carrier →
    Relation.ReflTransGen
      (fun A B : ιC => ∃ (k : Fin (cell A).R.N) (k' : Fin (cell B).R.N),
        (side A k).1 = (side B k').1 ∧ x ∈ (cell A).arc k)
      C C'

  conn : ∀ C C' : ιC, Relation.ReflTransGen
    (fun A B : ιC => ∃ (k : Fin (cell A).R.N) (k' : Fin (cell B).R.N), (side A k).1 = (side B k').1)
    C C'

attribute [instance] CellDissection.fintypeC CellDissection.fintypeE CellDissection.fintypeV
  CellDissection.decEqC CellDissection.decEqE CellDissection.decEqV

section Integrals

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

noncomputable def coeffIn (ζ : OpenPartialHomeomorph (Place ℂ F) ℂ) (θ : Ω[F⁄ℂ]) (w : ℂ) : ℂ :=
  (ζ.symm w).readDifferential θ (extChartAt 𝓘(ℂ, ℂ) (ζ.symm w) (ζ.symm w)) *
    deriv (extChartAt 𝓘(ℂ, ℂ) (ζ.symm w) ∘ ζ.symm) w

noncomputable def Cell.bdryIntegrand (C : Cell F) (θ : Ω[F⁄ℂ]) (s : ℝ) : ℂ :=
  coeffIn C.ζ θ (C.R.loop s) * C.R.loop' s

noncomputable def CellDissection.arcOf (𝒟 : CellDissection F) (q : 𝒟.ιE × Bool) :
    Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N :=
  Function.surjInv 𝒟.side_bij.surjective q

noncomputable def CellDissection.edgeInt (𝒟 : CellDissection F) (θ : Ω[F⁄ℂ]) (e : 𝒟.ιE) : ℂ :=
  ∫ s in ((𝒟.cell (𝒟.arcOf (e, true)).1).R.φs (𝒟.arcOf (e, true)).2.castSucc)..
      ((𝒟.cell (𝒟.arcOf (e, true)).1).R.φs (𝒟.arcOf (e, true)).2.succ),
    (𝒟.cell (𝒟.arcOf (e, true)).1).bdryIntegrand θ s

def CellDissection.skeleton (𝒟 : CellDissection F) : Set (Place ℂ F) :=
  ⋃ p : (Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N), (𝒟.cell p.1).arc p.2

end Integrals

end AlgebraicCurve
