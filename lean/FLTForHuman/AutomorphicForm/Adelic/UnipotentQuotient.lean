/-
  The unipotent quotient of `GL₂(𝔸_K)` and its rational centre-unipotent and torus-unipotent
  variants.

  Three layers of subgroups of `AutomorphicForm.AdelicGL2 (𝓞 K) K`, each with the quotient it
  acts on and the measure theory the quotient carries:

  * **the unipotent radical** — `adelicUnipotent K` is the range of the unitriangular embedding
    `x ↦ !![1, x; 0, 1]` of the adèle ring, `unipotentHaar` is the additive Haar measure of `𝔸_K`
    normalised by the box `adelicBox`, pushed through it, and `unipotentQuotientMeasure` is the
    `HaarQuotient` measure it induces on `UnipotentQuotient`;
  * **the rational centre-unipotent** — `rationalCentre K` is the image of the scalars `Kˣ`,
    `rationalCentreUnipotent K = rationalCentre K ⊔ adelicUnipotent K`, and
    `rationalCentreUnipotentHaar` is the countable sum of the translates of `unipotentHaar` over
    `Kˣ` (the "measure of the rational points", one copy of the unipotent Haar per scalar);
  * **the rational torus-unipotent** — `rationalDiagOne K` is the image of `diagOne (a)`,
    `rationalTorus K = rationalCentre K ⊔ rationalDiagOne K`,
    `rationalTorusUnipotent K = rationalTorus K ⊔ adelicUnipotent K`, and
    `rationalTorusUnipotentHaar` the same construction summed over `Kˣ × Kˣ`.

  The measure-theoretic content — that `rationalTorusUnipotentHaar` and
  `rationalCentreUnipotentHaar` are Haar and right-invariant, and that the two subgroups are
  closed — is proved in `AutomorphicForm/Adelic/RationalUnipotentHaar.lean`.

  Transcribed whole from three pin role modules (pinned `aa2d8b3`):

  * `Definitions/Def_AutomorphicForm_UnipotentQuotient.lean` (5 declarations),
  * `Definitions/Def_AutomorphicForm_RationalCentreUnipotentQuotient.lean` (5 declarations),
  * `Definitions/Def_AutomorphicForm_RationalTorusUnipotentQuotient.lean` (6 declarations),

  which the pin chains by import and which live in one module here because they are one subject
  and one namespace. Every declaration is a `def`/`abbrev`; there is no proof in the layer.

  **Wiring.** `spec/check_port.py` owns the sixteen declarations here.
  spec-pin: Definitions/Def_AutomorphicForm_UnipotentQuotient.lean
  spec-pin: Definitions/Def_AutomorphicForm_RationalCentreUnipotentQuotient.lean
  spec-pin: Definitions/Def_AutomorphicForm_RationalTorusUnipotentQuotient.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.Basic
import FLTForHuman.AutomorphicForm.Adelic.ConstantTerm
import FLTForHuman.MeasureTheory.HaarQuotient
import FLTForHuman.NumberTheory.AdelicBox
import FLTForHuman.NumberTheory.AdelicHaar.GeneralLinear
import FLTForHuman.NumberTheory.AdelicLevel.HeckeGen

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox
open NumberField.AdelicLevel

noncomputable section

namespace AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

variable (K : Type*) [Field K] [NumberField K]

/-! ### The unipotent radical -/

/-- The unipotent radical of `GL₂(𝔸_K)`: the range of `x ↦ !![1, x; 0, 1]`. -/
abbrev adelicUnipotent : Subgroup (AdelicGL2 (𝓞 K) K) :=
  (unipotentGL2Hom (R := AdeleRing (𝓞 K) K)).range

/-- The quotient of `GL₂(𝔸_K)` by the unipotent radical. -/
abbrev UnipotentQuotient : Type _ :=
  MulAction.orbitRel.Quotient (adelicUnipotent K) (AdelicGL2 (𝓞 K) K)

/-- The unitriangular embedding with its codomain restricted to the range. -/
def toAdelicUnipotent (x : AdeleRing (𝓞 K) K) : adelicUnipotent K :=
  (unipotentGL2Hom (R := AdeleRing (𝓞 K) K)).rangeRestrict (Multiplicative.ofAdd x)

/-- The Haar measure of the unipotent radical: the additive Haar measure of `𝔸_K`, normalised
by the mass of the box, pushed through the unitriangular embedding. -/
def unipotentHaar : Measure (adelicUnipotent K) :=
  Measure.map (toAdelicUnipotent K)
    (((adelicAddHaar (𝓞 K) K) (adelicBox K))⁻¹ • adelicAddHaar (𝓞 K) K)

/-- The quotient measure on `GL₂(𝔸_K) / U`. -/
def unipotentQuotientMeasure : Measure (UnipotentQuotient K) :=
  HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) (adelicUnipotent K) (unipotentHaar K)

/-! ### The rational centre-unipotent subgroup -/

/-- The rational centre: the image of the scalars `Kˣ`. -/
abbrev rationalCentre : Subgroup (AdelicGL2 (𝓞 K) K) :=
  ((globalPoints (𝓞 K) K).comp
    (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom)).range

/-- The rational centre-unipotent subgroup `Z(𝔸_K) · Kˣ · U(𝔸_K)`. -/
abbrev rationalCentreUnipotent : Subgroup (AdelicGL2 (𝓞 K) K) :=
  rationalCentre K ⊔ adelicUnipotent K

/-- The quotient of `GL₂(𝔸_K)` by the rational centre-unipotent subgroup. -/
abbrev RationalCentreUnipotentQuotient : Type _ :=
  MulAction.orbitRel.Quotient (rationalCentreUnipotent K) (AdelicGL2 (𝓞 K) K)

/-- The "measure of the rational centre-unipotent subgroup": the countable sum over `Kˣ` of the
translates of the unipotent Haar measure. -/
def rationalCentreUnipotentHaar : Measure (rationalCentreUnipotent K) :=
  Measure.sum fun a : Kˣ =>
    Measure.map
      (fun n : adelicUnipotent K =>
        (⟨globalPoints (𝓞 K) K (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom a)
            * (n : AdelicGL2 (𝓞 K) K),
          Subgroup.mul_mem_sup ⟨a, rfl⟩ n.2⟩ : rationalCentreUnipotent K))
      (unipotentHaar K)

/-- The quotient measure on `GL₂(𝔸_K) / (Z·Kˣ·U)`. -/
def rationalCentreUnipotentQuotientMeasure : Measure (RationalCentreUnipotentQuotient K) :=
  HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) (rationalCentreUnipotent K)
    (rationalCentreUnipotentHaar K)

/-! ### The rational torus-unipotent subgroup -/

/-- The rational diagonal: the image of `diagOne` on `Kˣ`. -/
abbrev rationalDiagOne : Subgroup (AdelicGL2 (𝓞 K) K) :=
  ((globalPoints (𝓞 K) K).comp (diagOne (A := K))).range

/-- The rational torus `T(K)`, generated by the centre and the diagonal. -/
abbrev rationalTorus : Subgroup (AdelicGL2 (𝓞 K) K) :=
  rationalCentre K ⊔ rationalDiagOne K

/-- The rational torus-unipotent subgroup `Z(𝔸_K) · T(K) · U(𝔸_K)`. -/
abbrev rationalTorusUnipotent : Subgroup (AdelicGL2 (𝓞 K) K) :=
  rationalTorus K ⊔ adelicUnipotent K

/-- The quotient of `GL₂(𝔸_K)` by the rational torus-unipotent subgroup. -/
abbrev RationalTorusUnipotentQuotient : Type _ :=
  MulAction.orbitRel.Quotient (rationalTorusUnipotent K) (AdelicGL2 (𝓞 K) K)

/-- The "measure of the rational torus-unipotent subgroup": the countable sum over `Kˣ × Kˣ`
of the translates of the unipotent Haar measure. -/
def rationalTorusUnipotentHaar : Measure (rationalTorusUnipotent K) :=
  Measure.sum fun za : Kˣ × Kˣ =>
    Measure.map
      (fun n : adelicUnipotent K =>
        (⟨globalPoints (𝓞 K) K (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom za.1)
            * globalPoints (𝓞 K) K (diagOne za.2) * (n : AdelicGL2 (𝓞 K) K),
          Subgroup.mul_mem_sup
            (Subgroup.mul_mem_sup ⟨za.1, rfl⟩ ⟨za.2, rfl⟩) n.2⟩ : rationalTorusUnipotent K))
      (unipotentHaar K)

/-- The quotient measure on `GL₂(𝔸_K) / (Z·T(K)·U)`. -/
def rationalTorusUnipotentQuotientMeasure : Measure (RationalTorusUnipotentQuotient K) :=
  HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) (rationalTorusUnipotent K)
    (rationalTorusUnipotentHaar K)

end AutomorphicForm

end
