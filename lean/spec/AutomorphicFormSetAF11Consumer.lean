/-
  Cross-module wire test for SET-AF11 (the Whittaker coefficient's API and its archimedean
  differentiability).

  A `spec/` probe, not a library module. **One zone**, and it is a real composition of two of the
  set's headlines on one and the same `φ`:

  * the **transformation law** (`whittakerCoefficient_unipotentGL2_mul`, row 1) rewrites the
    coefficient at a unipotent translate `n(x) · g` in terms of the coefficient at `g`, with the
    character factor `ψ (1 · x)`;
  * the **real differentiability identity**
    (`hasDerivAt_whittakerCoefficient_archFlow_of_continuous_archDerivAt`, row 8) differentiates
    `t ↦ whittakerCoefficient … φ 1 (g₀ · archRealGLAt hw (h · archFlowMatrix d t))` at `0`.

  The zone differentiates the *translated* coefficient. At every `t` the transformation law (applied
  with `g` the row-8 base point `g₀ · archRealGLAt hw (h · archFlowMatrix d t)`) identifies the
  translated value with `ψ (1 · x)` times row 8's function; differentiating that constant multiple
  and transporting along the pointwise identity gives the derivative of the translated function.
  The conclusion is neither headline: it is a derivative identity for
  `t ↦ whittakerCoefficient … φ 1 (unipotentGL2 x · g₀ · archRealGLAt hw (h · archFlowMatrix d t))`,
  whose derivative value is the *un-translated* row-8 derivative value scaled by `ψ (1 · x)`.

  One consumer-side hypothesis is needed and neither headline supplies it: the transformation law
  takes the invariance `∀ β u, φ (n (β + u) g) = φ (n u g)` at a *fixed* `g` (`hper`, row 1), while the
  flow moves `g`; `hper` below is the uniform left-unipotent invariance of `φ`
  (`∀ β g, φ (n β · g) = φ g`), which yields row 1's `hper` at every point of the flow. It is the
  standard invariance of an automorphic form under the principal unipotent subgroup, and it is
  recorded here rather than built into either headline.

  It imports only the module it composes.
-/
import FLTForHuman.AutomorphicForm.Adelic.WhittakerCoefficient

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField MeasureTheory
open AutomorphicForm NumberField.AdelicBox NumberField.AdelicLevel
  NumberField.AdelicHaar NumberField.AdelicVolume
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SmoothCusp
open LocalGL2 AdelicDock
open scoped ENNReal NNReal

namespace SetAF11WhittakerConsumer

/-- **The zone — the derivative of a unipotent translate of the coefficient.** Under the two
archimedean smoothness hypotheses of row 8 and the uniform left-unipotent invariance of `φ`, the
function `t ↦ whit π φ 1 (n(x) · g₀ · archRealGLAt hw (h · archFlowMatrix d t))` is differentiable at
`0`, with derivative `ψ (1 · x)` times the coefficient of `archDerivAt hw d φ` at `g₀ · archRealGLAt hw h`:
row 1 rewrites the value at each `t`, row 8 differentiates the un-translated function. -/
theorem hasDerivAt_whittakerCoefficient_unipotentGL2_mul_archFlow
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (w : InfinitePlace K) (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφc : Continuous φ) (hφs : IsArchSmoothAt hw φ)
    (hD1 : ∀ d : ArchDir, Continuous (archDerivAt hw d φ))
    (hD2 : ∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' φ)))
    (hper : ∀ (β : K) (g : AdelicGL2 (𝓞 K) K),
      φ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * g) = φ g)
    (g₀ : AdelicGL2 (𝓞 K) K) (x : AdeleRing (𝓞 K) K) (d : ArchDir) (h : GL (Fin 2) ℝ) :
    HasDerivAt (fun t : ℝ => whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1
        (unipotentGL2 x * (g₀ * archRealGLAt hw (h * archFlowMatrix d t))))
      (NumberField.StandardAddChar.stdAddChar K (algebraMap K (AdeleRing (𝓞 K) K) 1 * x) *
        whittakerCoefficient K (productionPinsOf K D
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) (archDerivAt hw d φ) 1
          (g₀ * archRealGLAt hw h)) 0 := by
  -- row 8: the derivative of the un-translated function
  have hrow8 := (hasDerivAt_whittakerCoefficient_archFlow_of_continuous_archDerivAt
    K D w hw φ hφc hφs hD1 hD2 g₀).1 d h
  -- scale it by the character factor `ψ (1 · x)` that row 1 will produce
  have hconst := hrow8.const_mul
    (NumberField.StandardAddChar.stdAddChar K (algebraMap K (AdeleRing (𝓞 K) K) 1 * x))
  -- row 1: at each `t`, the translated value is that constant multiple
  refine hconst.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  exact (whittakerCoefficient_unipotentGL2_mul K D
    (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
    (NumberField.StandardAddChar.stdAddChar K)
    (NumberField.StandardAddChar.adelicTraceData K).isGlobalAddChar_psiK.principalInvariant
    φ (g₀ * archRealGLAt hw (h * archFlowMatrix d t))
    (fun β u => by
      rw [unipotentGL2_add, mul_assoc]
      exact hper β (unipotentGL2 u * (g₀ * archRealGLAt hw (h * archFlowMatrix d t))))
    1 x)

end SetAF11WhittakerConsumer

end
