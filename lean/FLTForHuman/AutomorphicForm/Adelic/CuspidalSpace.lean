/-
  The cuspidal functions are closed under addition and scalar multiplication.

  `IsCuspidalFn μ u f` says that the constant term of `f` along the unipotent-orbit map `u`
  vanishes at every point. The constant term is an integral, hence additive and homogeneous
  in the function (Fubini's two linearity rules, in the form `integral_add`/`integral_smul`),
  and a linear functional that kills `f₁`, `f₂` also kills `f₁ + f₂` and `c • f`. These are the
  two obligations that make `{f | IsCuspidalFn μ u f}` a `Submodule` of `G → ℂ` — the object the
  cuspidal side of the port is built on — so they are stated even though they are short.

  spec-pin: P2M/Sol/S_AutomorphicForm_IsCuspidalFn_add.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_IsCuspidalFn_smul.lean

  ## Port deltas

  - Bodies: the pin's `IsCuspidalFn.add` rewrites with
    `AutomorphicForm.constantTerm_add μ u g (h₁ g) (h₂ g)` and its `smul` row with
    `constantTerm_smul`. Those two lemmas are not in this module's import closure (they landed
    with a different pin, in `AutomorphicForm/Adelic/Cusp/IsotypicVanishing.lean`), and that
    module's closure is 225 modules against this one's — so the same two integral-linearity
    steps are written out here (`integral_add`/`integral_smul` under
    `constantTerm = ∫ q, f (u q * g)`) instead of importing the heavy closure. Both rows are
    public, so `check_port` hashes their statements (not their bodies) to the pins: **2 ok**.
  - Wire: the two pin sources are the module's whole public surface (one declaration each),
    so `scaffold_audit` reads complete.
  - Duplicate landing, reported not resolved: `AutomorphicForm/Adelic/ProductionPinsTail.lean`
    already declares public `IsCuspidalFn.add`/`.smul` from these same two pin sources. This
    module is the order's landing of the same rows; the two must not be imported together
    (the names would clash), and the frontier should keep one of them as the owner.
  - Imports unchanged from the scaffold. No `private` markers (the pins mark nothing
    `private`).

  ## Heartbeat probe (recorded, never installed — FR-0225)

  `lake env lean -DautoImplicit=false -DmaxHeartbeats=N
  FLTForHuman/AutomorphicForm/Adelic/CuspidalSpace.lean` is **silent at N = 500** and **fails at
  N = 250** (`isDefEq` in the `smul` row's closing `rw`). The measured pair for the probe is
  500 / 250. No `set_option maxHeartbeats` is in this module.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.NumberTheory.NumberField.Basic
import FLTForHuman.AutomorphicForm.Adelic.ConstantTerm

set_option autoImplicit false

noncomputable section

open NumberField AutomorphicForm MeasureTheory

namespace AutomorphicForm

theorem IsCuspidalFn.add {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]
    {μ : Measure Q} {u : Q → G} {f₁ f₂ : G → ℂ}
    (hf₁ : IsCuspidalFn μ u f₁) (hf₂ : IsCuspidalFn μ u f₂)
    (h₁ : ∀ g, Integrable (constantTermIntegrand u f₁ g) μ)
    (h₂ : ∀ g, Integrable (constantTermIntegrand u f₂ g) μ) :
    IsCuspidalFn μ u (fun x => f₁ x + f₂ x) := by
  intro g
  have hadd : constantTerm μ u (fun x => f₁ x + f₂ x) g
      = constantTerm μ u f₁ g + constantTerm μ u f₂ g := by
    simp only [constantTerm, constantTermIntegrand]
    exact integral_add (h₁ g) (h₂ g)
  rw [hadd, hf₁ g, hf₂ g, add_zero]

theorem IsCuspidalFn.smul {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]
    {μ : Measure Q} {u : Q → G} {f : G → ℂ}
    (hf : IsCuspidalFn μ u f) (c : ℂ) : IsCuspidalFn μ u (fun x => c * f x) := by
  intro g
  have hsmul : constantTerm μ u (fun x => c * f x) g = c * constantTerm μ u f g := by
    simp only [constantTerm, constantTermIntegrand]
    simpa [smul_eq_mul] using integral_smul (μ := μ) c (fun q => f (u q * g))
  rw [hsmul, hf g, mul_zero]

end AutomorphicForm

end
