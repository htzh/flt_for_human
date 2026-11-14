/-
  SET-AF69B consumer: the two `AverageOperator` headlines, read where they can be *executed*.

  **The zone.** `FLTForHuman/Analysis/Group/AverageOperator.lean` closes the `ContinuousLinearMap`
  namespace with two rows about the integral representation of an averaging operator over a compact
  group:

  * **F** — `comp_eq_of_forall_apply_eq_integral_smul_apply_of_convolution`: two operators that are
    both given by the convolution integral `v ↦ ∫ c, w c • S c v` multiply to the double convolution;
    and the operator of the *unweighted* integral is an idempotent projection onto the common fixed
    space of the `S c`.
  * **G** — `exists_forall_apply_eq_integral_smul_apply_of_forall_norm_le_of_continuous`: the averaging
    operator `avg μ S B hSb hSc w hw` itself, with the norm bound `M * B * ‖v‖`, the invariance of a
    closed `S`-stable submodule, and the commutation with every `T` commuting with each `S c`.

  Both statements are `∀ …` over an arbitrary compact group, an arbitrary complex Hilbert space, an
  arbitrary continuous representation and an arbitrary probability Haar measure; nothing in them is
  executable until those are chosen. So the zone picks the smallest choice that makes every
  hypothesis inhabited and every integral computable:

  * `C = Unit` — the trivial group, with `μ = Measure.dirac ()`, the normalised Haar measure (the
    instance below), so every integral over `C` is evaluation at the identity;
  * `H = ℂ` with the trivial representation `S c = 1` — the *identity* operator, so `S` is a monoid
    homomorphism `Unit →* (ℂ →L[ℂ] ℂ)` and `B = 1` discharges `hSb` (`‖1‖ ≤ 1`);
  * the constant weight `w = 1`, and a second weight `w / 2` to give row F a non-trivial convolution
    to compute.

  Under that choice every convolution integral collapses and the two rows become statements about the
  concrete scalar operators `1` and `(1/2 : ℂ) • 1` on `ℂ`, which is the point of the zone: the
  abstract `∃`/`∀` is *discharged* and the composed operators are evaluated at a concrete `v`.

  **Zone F** runs `hconv` at `w₁ = 1`, `w₂ = 1/2`, so the double convolution `∫ d, w₁ d * w₂ (d⁻¹ * c)`
  is the constant `1/2`, and the conclusion `A₁.comp A₂ = A₁₂` is the executed composition
  `1.comp ((1/2) • 1) = (1/2) • 1`, evaluated at `v = 1`. Then `hone` is the unweighted clause
  `A.comp A = A` at `A = 1`.

  **Zone G** constructs `A = avg μ S 1 hSb hSc w hw` by `hG`, evaluates `A 1 = 1` (the average of the
  identity over a probability group is the identity), reads the norm bound at `M = 1`, and executes
  the commutation with `T = 2 • 1` at `v = 1`, i.e. the composition `T.comp A = A.comp T` is fired.

  This module is outside every library: it is a spec-side composition check, not part of the port's
  import graph.
-/
import FLTForHuman.Analysis.Group.AverageOperator

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ComplexConjugate InnerProductSpace

namespace AnalysisSetAF69BConsumer

/-- The Dirac mass at the identity of the trivial group is a Haar measure: it is finite on compacta,
it is left-invariant because `Unit` has one point, and every nonempty open set is the whole space. -/
instance : (Measure.dirac () : Measure Unit).IsHaarMeasure where
  map_mul_left_eq_self _ := by simp
  open_pos U _ hne := by
    obtain ⟨x, hx⟩ := hne
    have hx' : x = () := Subsingleton.elim x ()
    subst hx'
    simpa using hx

/-- The trivial representation: `S c = 1`, the identity operator on `ℂ`. -/
def Striv : Unit →* (ℂ →L[ℂ] ℂ) := 1

/-- The constant weight `w = 1`. -/
def wtriv : Unit → ℂ := fun _ => 1

theorem hSb_triv : ∀ c : Unit, ‖Striv c‖ ≤ 1 := by
  intro c
  simp [Striv]

theorem hSc_triv : ∀ v : ℂ, Continuous fun c : Unit => Striv c v := by
  intro v
  simpa [Striv] using (continuous_const : Continuous fun _ : Unit => v)

theorem hw_triv : Continuous wtriv := continuous_const

/-- The integral of a function over the trivial group is its value at the identity, so the unweighted
average of the trivial representation fixes every vector. -/
theorem integral_triv (g : Unit → ℂ) : (∫ c, g c ∂(Measure.dirac () : Measure Unit)) = g () := by
  simp

/-- **Zone F.** The convolution headline executed on `ℂ`: with weights `1` and `1/2`, the composed
operator `1.comp ((1/2) • 1)` is the double convolution `(1/2) • 1`, and the composition is evaluated
at the concrete vector `v = 1`. -/
theorem row_F :
    (1 : ℂ →L[ℂ] ℂ).comp ((1 / 2 : ℂ) • (1 : ℂ →L[ℂ] ℂ)) = ((1 / 2 : ℂ) • (1 : ℂ →L[ℂ] ℂ)) ∧
      ((1 : ℂ →L[ℂ] ℂ).comp ((1 / 2 : ℂ) • (1 : ℂ →L[ℂ] ℂ))) (1 : ℂ) = 1 / 2 ∧
        (1 : ℂ →L[ℂ] ℂ).comp (1 : ℂ →L[ℂ] ℂ) = 1 := by
  obtain ⟨hconv, hone⟩ :=
    ContinuousLinearMap.comp_eq_of_forall_apply_eq_integral_smul_apply_of_convolution
      (Measure.dirac () : Measure Unit) Striv 1 hSb_triv hSc_triv
  have h₁ : ∀ v : ℂ, (1 : ℂ →L[ℂ] ℂ) v
      = ∫ c, (fun _ => (1 : ℂ)) c • (Striv c) v ∂(Measure.dirac () : Measure Unit) := by
    intro v
    simp [Striv]
  have h₂ : ∀ v : ℂ, ((1 / 2 : ℂ) • (1 : ℂ →L[ℂ] ℂ)) v
      = ∫ c, (fun _ => (1 / 2 : ℂ)) c • (Striv c) v ∂(Measure.dirac () : Measure Unit) := by
    intro v
    simp [Striv]
  have h₁₂ : ∀ v : ℂ, ((1 / 2 : ℂ) • (1 : ℂ →L[ℂ] ℂ)) v
      = ∫ c, (∫ d, (fun _ => (1 : ℂ)) d * (fun _ => (1 / 2 : ℂ)) (d⁻¹ * c)
          ∂(Measure.dirac () : Measure Unit)) • (Striv c) v ∂(Measure.dirac () : Measure Unit) := by
    intro v
    simp [Striv]
  have hunw : ∀ v : ℂ, (1 : ℂ →L[ℂ] ℂ) v
      = ∫ c, (Striv c) v ∂(Measure.dirac () : Measure Unit) := by
    intro v
    simp [Striv]
  refine ⟨hconv (fun _ => (1 : ℂ)) (fun _ => (1 / 2 : ℂ)) continuous_const continuous_const
    (1 : ℂ →L[ℂ] ℂ) ((1 / 2 : ℂ) • (1 : ℂ →L[ℂ] ℂ)) ((1 / 2 : ℂ) • (1 : ℂ →L[ℂ] ℂ))
    h₁ h₂ h₁₂, ?_, (hone (1 : ℂ →L[ℂ] ℂ) hunw).2⟩
  simp

/-- **Zone G.** The averaging-operator headline executed on `ℂ`: the operator `avg μ S 1 hSb hSc w hw`
exists, sends the concrete vector `v = 1` to `1`, obeys the norm bound at `M = 1`, and the composition
`T.comp A = A.comp T` with `T = 2 • 1` is executed at `v = 1`. -/
theorem row_G :
    ∃ A : ℂ →L[ℂ] ℂ,
      A (1 : ℂ) = 1 ∧
        ‖A (1 : ℂ)‖ ≤ 1 * 1 * ‖(1 : ℂ)‖ ∧
          ((2 : ℂ) • (1 : ℂ →L[ℂ] ℂ)).comp A = A.comp ((2 : ℂ) • (1 : ℂ →L[ℂ] ℂ)) ∧
            (((2 : ℂ) • (1 : ℂ →L[ℂ] ℂ)).comp A) (1 : ℂ) = (A.comp ((2 : ℂ) • (1 : ℂ →L[ℂ] ℂ))) (1 : ℂ) := by
  obtain ⟨A, hA, hbound, -, hcomm⟩ :=
    ContinuousLinearMap.exists_forall_apply_eq_integral_smul_apply_of_forall_norm_le_of_continuous
      (Measure.dirac () : Measure Unit) Striv 1 hSb_triv hSc_triv wtriv hw_triv
  have hA1 : A (1 : ℂ) = 1 := by
    rw [hA]
    simp [Striv, wtriv]
  have hT : ∀ c : Unit, ((2 : ℂ) • (1 : ℂ →L[ℂ] ℂ)).comp (Striv c)
      = (Striv c).comp ((2 : ℂ) • (1 : ℂ →L[ℂ] ℂ)) := by
    intro c
    simp [Striv]
  have hcomm' := hcomm ((2 : ℂ) • (1 : ℂ →L[ℂ] ℂ)) hT
  exact ⟨A, hA1, by rw [hA1]; norm_num,
    hcomm', congrArg (fun R : ℂ →L[ℂ] ℂ => R (1 : ℂ)) hcomm'⟩

end AnalysisSetAF69BConsumer
