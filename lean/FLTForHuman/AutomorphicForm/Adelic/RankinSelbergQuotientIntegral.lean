/-
  The Rankin-Selberg quotient integrand and integral, the shell it is cut down to, and the
  `S`-part of that integral.

  `quotientIntegrand K pins ψ x y φ w d₁ d₂ g` is the Rankin-Selberg integrand at `g:` the window
  indicator of `|det g| ∈ [d₁, d₂]`, the Whittaker coefficient of `x` times the conjugate of the
  Whittaker coefficient of `y`, the test function `φ`, and the weight `|det g|^{-w}`.
  `quotientIntegral K pins ψ x y φ w d₁ d₂` integrates it over the rational centre-unipotent
  quotient `GL₂(𝔸_K)/(Z(𝔸_K)·Kˣ·U(𝔸_K))`. `shellZeroOutside K S` is the **`S`-shell**: at every
  finite place `v ∉ S` the valuation of `det g` is the square of the maximum of the bottom row —
  equivalently (`Adelic/ShellMeasureIntegral.lean`, `shellZeroOutside_eq`) the Iwasawa shell index
  `iwasawaShellIndex K v g` vanishes at every `v ∉ S`. `sPartIntegral K S` is `quotientIntegral`
  restricted to that shell.

  This is the pin's whole `Definitions/` layer, transcribed body and all: four `def`s and no
  proofs, and hence nothing deferred. Its consumer is
  `AutomorphicForm/Adelic/ShellMeasureIntegral.lean`, whose row says the `S`-part measure
  (`NumberField.Idele.sPartMeasure K S`) integrates the shell exactly.

  spec-pin: Definitions/Def_AutomorphicForm_RankinSelbergQuotientIntegral.lean

## Port deltas

* **Namespace.** The pin's four `def`s live in `AutomorphicForm.RankinSelberg`; the scaffold had
  flattened them to `AutomorphicForm`. They are kept at the pin's own namespace — as the port's
  siblings `Adelic/WhittakerCoefficient.lean` and `Adelic/RankinSelbergSection.lean` do — so that
  the consumer's statement can name `AutomorphicForm.RankinSelberg.shellZeroOutside` verbatim, as
  the pin's `solution` does. `check_port --force` reads 4 ok on either spelling.
* **Visibility.** The pin declares all four public and they stay public: the wire reads 4 ok with
  nothing private.
* **No `attribute [local instance]` block.** The pin opens the module with `glBorel`/`adeleBorel`
  and their `BorelSpace` companions as local instances. It is not carried here: no body below
  names a measurable space or a measure through instance search (every measure is applied
  explicitly), and the module is silent without it. The consumer carries the block, because its
  statements do need it.

## Heartbeat probe (recorded, never installed — FR-0225)

`lake env lean -DautoImplicit=false -DmaxHeartbeats=N FLTForHuman/AutomorphicForm/Adelic/RankinSelbergQuotientIntegral.lean`
is **silent at N = 1 000** and **fails at N = 500** (= 1 000 / 2), at
`(deterministic) timeout at isDefEq` on the `shellZeroOutside` body — the coercion/tuple step
`((det g : (𝔸_K)ˣ) : 𝔸_K).2 v`. No `set_option maxHeartbeats` is in this module.

## Gates

* `check_port --force`: **4 ok, 0 mismatch, 0 missing, 0 own**.
* `scaffold_audit.py`: **complete** (4 pin public declarations on the wire, 4 declared here).
* silence: `lake env lean -DautoImplicit=false` prints nothing; one locked `lake build` succeeds.
* `#print axioms` on all four `def`s: `[propext, Classical.choice, Quot.sound]` (inherited from the
  quotient/measure vocabulary the bodies name; no proof is performed here).
* `dedup.py --within --module RankinSelbergQuotientIntegral`: **0 clusters** (4 declarations).
* `move_dead.py --dry-run`: **0 declarations, 0 lines**.
-/


import FLTForHuman.AutomorphicForm.Adelic.WhittakerCoefficient
import FLTForHuman.AutomorphicForm.Adelic.UnipotentQuotient
import FLTForHuman.NumberTheory.NumberField.TateGlobal.Defs

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory

namespace AutomorphicForm

namespace RankinSelberg


section
variable (K : Type) [Field K] [NumberField K]

def quotientIntegrand (pins : CarrierPins K) (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ)
    (x y φ : AdelicGL2 (𝓞 K) K → ℂ) (w d₁ d₂ : ℝ) (g : AdelicGL2 (𝓞 K) K) : ℂ :=
  ({g : AdelicGL2 (𝓞 K) K |
        NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}.indicator
      (fun _ => (1 : ℂ)) g) *
    whittakerCoefficient K pins ψ x 1 g * (starRingEnd ℂ) (whittakerCoefficient K pins ψ y 1 g) * φ g *
    ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-w) : ℝ) : ℂ)

end

section
variable (K : Type) [Field K] [NumberField K]

def quotientIntegral (pins : CarrierPins K) (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ)
    (x y φ : AdelicGL2 (𝓞 K) K → ℂ) (w d₁ d₂ : ℝ) : ℂ :=
  ∫ q : RationalCentreUnipotentQuotient K, quotientIntegrand K pins ψ x y φ w d₁ d₂ q.out
    ∂(rationalCentreUnipotentQuotientMeasure K)

end

section
variable (K : Type) [Field K] [NumberField K]

def shellZeroOutside (S : Finset (HeightOneSpectrum (𝓞 K))) : Set (AdelicGL2 (𝓞 K) K) :=
  {g | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
    Valued.v ((((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) =
      (max (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v))
           (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v))) ^ 2}

end

section
variable (K : Type) [Field K] [NumberField K]

def sPartIntegral (S : Finset (HeightOneSpectrum (𝓞 K))) (pins : CarrierPins K)
    (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (x y φ : AdelicGL2 (𝓞 K) K → ℂ) (w d₁ d₂ : ℝ) : ℂ :=
  ∫ q in {q : RationalCentreUnipotentQuotient K | q.out ∈ shellZeroOutside K S},
    quotientIntegrand K pins ψ x y φ w d₁ d₂ q.out ∂(rationalCentreUnipotentQuotientMeasure K)

end

end RankinSelberg

end AutomorphicForm

end
