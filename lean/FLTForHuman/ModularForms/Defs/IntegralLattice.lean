/-
  The weight-2 auxiliary integral lattice and the `χ₋₃` bridge.

  This is the *weight-2* vocabulary (distinct from T9's all-weight `intLattice`):
  `qIntegralSet N` is the set of weight-2 cusp forms for `Γ₀(N)` with integral
  `q`-coefficients, `qIntegralLattice N` its `ℤ`-span, `HasIntegralBasis N` the
  assertion that this set spans. `bridgeProduct` multiplies a coefficient
  sequence by `e1Chi3In` (the `χ₋₃` Eisenstein series), and `IsLatticeRealized`
  records that a sequence is realized by a lattice form modulo `3·bridgeProduct`.

  Transcribed verbatim from `Definitions/Def_CuspForm_IntegralLattice.lean`
  (pinned `aa2d8b3`). This vocabulary feeds the `χ₋₃`/mod-`3` congruence
  machinery, not T10's full-rank existence proof.
-/
import FLTForHuman.ModularForms.HeckeQCoeff
import FLTForHuman.ModularForms.Defs.EisensteinChiNegThree

set_option autoImplicit false

open ModularFormClass CongruenceSubgroup EisensteinWeightOne

namespace CuspForm

/-- The weight-2 cusp forms with integral `q`-coefficients. -/
def qIntegralSet (N : ℕ) : Set (CuspForm (Gamma0 N) 2) :=
  {f | ∀ n : ℕ, ModularFormClass.qCoeff f n ∈ (⊥ : Subring ℂ)}

/-- The `ℤ`-span of `qIntegralSet`. -/
def qIntegralLattice (N : ℕ) : Submodule ℤ (CuspForm (Gamma0 N) 2) :=
  Submodule.span ℤ (qIntegralSet N)

/-- `qIntegralSet` spans the weight-2 cusp-form space. -/
def HasIntegralBasis (N : ℕ) : Prop :=
  Submodule.span ℂ (qIntegralSet N) = ⊤

end CuspForm

/-- `a` multiplied by the `χ₋₃` Eisenstein series. -/
noncomputable def bridgeProduct {R : Type*} [CommRing R] (a : ℕ → R) : PowerSeries R :=
  PowerSeries.mk a * e1Chi3In R

namespace CuspForm

/-- `a` is realized by a lattice form, modulo `3 · bridgeProduct a`. -/
def IsLatticeRealized (N : ℕ) (a : ℕ → ℤ) : Prop :=
  ∃ f : CuspForm (Gamma0 N) 2, f ∈ qIntegralSet N ∧
    ∃ af : ℕ → ℤ, (∀ n, (af n : ℂ) = ModularFormClass.qCoeff f n) ∧
      ∀ n, (3 : ℤ) ∣ af n - (bridgeProduct a).coeff n

end CuspForm
