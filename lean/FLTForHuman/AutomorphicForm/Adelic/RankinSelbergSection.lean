/-
The Rankin–Selberg section and the separation of a monoid homomorphism.

Two induced-section facts: the diagonal reduction of the Rankin–Selberg section multiplies by the
`(s + 1/2)`-power of the idèle norm, and a continuous monoid homomorphism that is nontrivial on a
matrix entry is nontrivial on an open set. They are the section algebra the Rankin–Selberg
unfolding and its separations use.

  spec-pin: P2M/Sol/S_AutomorphicForm_RankinSelberg_section_diagOne_mul_eq_ideleNorm_cpow_mul_of_isInducedSection_etaFst_etaSnd.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_exists_continuous_monoidHom_matrix_apply_ne_one_of_ne_one.lean

  The two pins' public engines are transcribed at the pins' last names under the pins' own
  proof-block labels. The first pin's search-stage label `Ws50CH1` is renamed to the subject label
  `DiagOneBorel` (FR-0224, as `Ws1.L3` was renamed in `Cusp/BoundedGenuineRealization.lean`); the
  second pin's `SepPtsProof` is a mathematical label and is kept, like the port's other `…Proof`
  blocks.

  ## Port deltas

  - no import added: the scaffold's seven cover every premise (`diagOne_coe_apply`, `adelicBorel`,
    `borelDiagFst`/`borelDiagSnd`, `IsInducedSection`, `etaFst`/`etaSnd`, `cpowChar_apply_val`,
    `rowIsometrySubgroup₀`, `InfinitePlace.Completion.{extensionEmbedding,
    isometry_extensionEmbedding}`).
  - the pin's file-local `attribute [local instance] ….glBorel …` block is not carried: nothing
    here needs those instances under v4.34, and installing them would change instance search for
    the second row as well.
  - heartbeat probe (`lake env lean -DautoImplicit=false -DmaxHeartbeats=N`, never installed):
    silent at **2000**, first failure at **1500** (`whnf` in the `SepPtsProof` block), also at
    **1000**; the measured pair for the probe is 2000 / 1000.
-/
import FLTForHuman.AutomorphicForm.Adelic.WhittakerCoefficient
import FLTForHuman.AutomorphicForm.Adelic.ArchType
import FLTForHuman.AutomorphicForm.Adelic.ProductionPinsGeneral
import FLTForHuman.AutomorphicForm.Adelic.AdelicMaximalCompact
import FLTForHuman.NumberTheory.NumberField.IdeleProductMeasure
import FLTForHuman.AutomorphicForm.Adelic.IsotypicCuspSpace
import FLTForHuman.AutomorphicForm.Adelic.InducedSectionSpan

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped ENNReal NNReal BigOperators

namespace AutomorphicForm.RankinSelberg

namespace DiagOneBorel

theorem diagOne_mem_adelicBorel (K : Type) [Field K] [NumberField K] (t : (AdeleRing (𝓞 K) K)ˣ) :
    diagOne t ∈ adelicBorel (𝓞 K) K := by
  show ((diagOne t : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0
  rw [diagOne_coe_apply]
  exact Matrix.diagonal_apply_ne _ (by decide)

theorem borelDiagFst_diagOne (K : Type) [Field K] [NumberField K] (t : (AdeleRing (𝓞 K) K)ˣ)
    (hmem : diagOne t ∈ adelicBorel (𝓞 K) K) :
    borelDiagFst (⟨diagOne t, hmem⟩ : ↥(adelicBorel (𝓞 K) K)) = t := by
  apply Units.ext
  show ((diagOne t : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0 = (t : AdeleRing (𝓞 K) K)
  rw [diagOne_coe_apply, Matrix.diagonal_apply_eq]
  rfl

theorem borelDiagSnd_diagOne (K : Type) [Field K] [NumberField K] (t : (AdeleRing (𝓞 K) K)ˣ)
    (hmem : diagOne t ∈ adelicBorel (𝓞 K) K) :
    borelDiagSnd (⟨diagOne t, hmem⟩ : ↥(adelicBorel (𝓞 K) K)) = 1 := by
  apply Units.ext
  show ((diagOne t : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1 =
    ((1 : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)
  rw [diagOne_coe_apply, Matrix.diagonal_apply_eq, Units.val_one]
  rfl

end DiagOneBorel

theorem section_diagOne_mul_eq_ideleNorm_cpow_mul_of_isInducedSection_etaFst_etaSnd (K : Type) [Field K] [NumberField K] :
    let α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (φ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 K) K (etaFst 1 α hα s) (etaSnd 1 α hα s) (φ s)),
    ∀ (s : ℂ) (k : AdelicGL2 (𝓞 K) K), k ∈ adelicMaximalCompact K → ∀ t : (AdeleRing (𝓞 K) K)ˣ,
        φ s (diagOne t * k) = ((NumberField.TateGlobal.ideleNorm K t : ℝ) : ℂ) ^ (s + 1 / 2) * φ s k
  := by
  intro α hα φ hφ s k _ t
  have hαt : (((α t : ℝˣ) : ℝ) : ℂ) = ((NumberField.TateGlobal.ideleNorm K t : ℝ) : ℂ) := rfl
  rw [hφ s (diagOne t) (DiagOneBorel.diagOne_mem_adelicBorel K t) k, DiagOneBorel.borelDiagFst_diagOne,
    DiagOneBorel.borelDiagSnd_diagOne, map_one, Units.val_one, mul_one, etaFst_apply, MonoidHom.one_apply,
    one_mul, cpowChar_apply_val, hαt]

end AutomorphicForm.RankinSelberg

namespace AutomorphicForm

namespace SepPtsProof

variable (F : Type) [Field F]

noncomputable def stdRepAt (w₀ : InfinitePlace F) :
    (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* Matrix (Fin 2) (Fin 2) ℂ :=
  ((RingHom.mapMatrix (InfinitePlace.Completion.extensionEmbedding w₀)).toMonoidHom.comp
    (Units.coeHom (Matrix (Fin 2) (Fin 2) w₀.Completion))).comp
    ((rowIsometrySubgroup₀ w₀.Completion).subtype.comp (Pi.evalMonoidHom _ w₀))

theorem stdRepAt_apply (w₀ : InfinitePlace F) (κ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) (i j : Fin 2) :
    stdRepAt F w₀ κ i j =
      InfinitePlace.Completion.extensionEmbedding w₀ (((κ w₀ : GL (Fin 2) w₀.Completion) : Matrix (Fin 2) (Fin 2) w₀.Completion) i j) :=
  rfl

theorem continuous_stdRepAt (w₀ : InfinitePlace F) : Continuous (stdRepAt F w₀) := by
  refine continuous_matrix fun i j => ?_
  simp only [stdRepAt_apply]
  refine (InfinitePlace.Completion.isometry_extensionEmbedding w₀).continuous.comp ?_
  exact (Units.continuous_val.comp (continuous_subtype_val.comp (continuous_apply w₀))).matrix_elem i j

end SepPtsProof

theorem exists_continuous_monoidHom_matrix_apply_ne_one_of_ne_one
    (F : Type) [Field F] [NumberField F]
    (κ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) (hκ : κ ≠ 1) :
    ∃ (n : ℕ) (ρ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* Matrix (Fin n) (Fin n) ℂ),
      Continuous ρ ∧ ρ κ ≠ 1
  := by
  classical
  obtain ⟨w₀, hw₀⟩ : ∃ w₀, κ w₀ ≠ 1 := by
    by_contra h
    push Not at h
    exact hκ (funext h)
  refine ⟨2, SepPtsProof.stdRepAt F w₀, SepPtsProof.continuous_stdRepAt F w₀, fun h1 => hw₀ ?_⟩
  apply Subtype.ext
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  have hij := congrFun (congrFun h1 i) j
  rw [SepPtsProof.stdRepAt_apply] at hij
  have h1ij : (1 : Matrix (Fin 2) (Fin 2) ℂ) i j =
      InfinitePlace.Completion.extensionEmbedding w₀ ((1 : Matrix (Fin 2) (Fin 2) w₀.Completion) i j) := by
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [h1ij] at hij
  exact (InfinitePlace.Completion.extensionEmbedding w₀).injective hij

end AutomorphicForm

end
