/-
  SET-AF83B consumer: the finite-place integrality calculus, read at the identity.

  **The rows.** `FLTForHuman/AutomorphicForm/Adelic/FiniteIntegralConjugation.lean` carries four
  pin rows: the integrality half of the content/level bookkeeping
  (`exists_upperTriangular_globalPoints_mul_mul_scalar_mul_finIdeleDiag_inv_mem_finiteIntegralGL2`),
  the local Bruhat–Iwahori split (`exists_borel_mul_gl2Weyl_mul_unipotentGL2_eq_of_integral`), the
  uniform Haar bound on a centre-cut Siegel set
  (`exists_forall_adelicGLHaar_image2_unipotentGL2_mul_mul_le_of_isCompact`), and the exactness of
  membership in the rational-centre unipotent set under a Hecke conjugation
  (`mem_rationalCentreUnipotent_iff_heckeGen_mul_centralScalar_conj_mem`), with the two matrix
  identities it runs on.

  **What is concrete here.** The element `g = 1` (the identity matrix), the identity idèle
  `u = 1`, and the *engine* `diagOne_mul_unipotentGL2_mul_inv` used as a rewriting rule. Everything
  else stays the rows' own existential data, read out by `obtain`.

  **The readings.** Each zone is a cross-module composition, not a restatement:

  * Zone 1 — the Bruhat–Iwahori split at `1`: the row's two integrality hypotheses are discharged by
    the entries of the identity matrix, and what survives is an upper-triangular `β` and an integral
    unipotent parameter `x` with `1 = β · w · n(x)` (or that times `w⁻¹`).
  * Zone 2 — the Haar bound at an arbitrary point of the Siegel set: `≤ ofReal M₀` for one `M₀`
    uniform over the set.
  * Zone 3 — the same bound read as **finiteness**: the measure is `< ⊤` at every point of the set.
    This is the reading the measure-theoretic consumers need, and it is not in the row.
  * Zone 4 — membership: at `y = 1` the conjugated element is in the rational-centre unipotent set,
    so the exactness is not vacuous at the trivial element.
  * Zone 5 — the `centralScalar` parameter dropped: at `u = 1` the row specialises to invariance
    under `heckeGen v` alone.
  * Zone 6 — the engine as a rewriting rule: the conjugate of a unipotent matrix by `diagOne τ` is the
    unipotent matrix of `τ * x`. This is the module's own engine, spent rather than re-proved.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/AutomorphicFormSetAF83BConsumer.lean` and never enters the build.
-/
import FLTForHuman.AutomorphicForm.Adelic.FiniteIntegralConjugation

set_option autoImplicit false

noncomputable section

open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicBox NumberField.AdelicLevel
open NumberField.AdelicHaar AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped ENNReal Classical

namespace AutomorphicFormSetAF83BConsumer

/-! ### Zone 1 — the local Bruhat–Iwahori split of the identity matrix -/

/-- **Zone 1.** At `g = 1` the row's two integrality hypotheses are the entries of the identity
matrix, and the conclusion is an upper-triangular integral `β` and an integral `x` with
`1 = β * gl2Weyl * unipotentGL2 x` or that times `gl2Weyl⁻¹`. -/
theorem exists_upperTriangular_split_one (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ (β : GL (Fin 2) (v.adicCompletion F)) (x : v.adicCompletion F),
      (β : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0 ∧
      x ∈ v.adicCompletionIntegers F ∧
      ((1 : GL (Fin 2) (v.adicCompletion F)) = β * gl2Weyl * unipotentGL2 x ∨
        (1 : GL (Fin 2) (v.adicCompletion F)) = β * gl2Weyl * unipotentGL2 x * gl2Weyl⁻¹) := by
  have hmem : ∀ i j,
      ((1 : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈
        v.adicCompletionIntegers F := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp
  have hmem' : ∀ i j,
      (((1 : GL (Fin 2) (v.adicCompletion F))⁻¹ : GL (Fin 2) (v.adicCompletion F)) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F := by
    simp only [inv_one]
    exact hmem
  obtain ⟨β, x, htri, -, -, hint, hsplit⟩ :=
    exists_borel_mul_gl2Weyl_mul_unipotentGL2_eq_of_integral F v 1 hmem hmem'
  exact ⟨β, x, htri, hint, hsplit⟩

/-! ### Zone 2 — the uniform Haar bound on a centre-cut Siegel set -/

/-- **Zone 2.** The row hands back one constant `M₀` that bounds the additive Haar measure of
`unipotentGL2 '' closure(adelicBox K) · s · C` uniformly over the whole centre-cut Siegel set. -/
theorem exists_bound_on_centreCutSiegelSet (K : Type) [Field K] [NumberField K]
    (c' u' d₁' d₂' : ℝ) (hc' : 0 < c')
    {C : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hC : IsCompact C) :
    ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ s ∈ centreCutSiegelSet K c' u' d₁' d₂',
      adelicGLHaar (Fin 2) (𝓞 K) K
          (Set.image2 (fun (t : AdeleRing (𝓞 K) K) (c : GL (Fin 2) (AdeleRing (𝓞 K) K)) =>
            unipotentGL2 t * s * c) (closure (adelicBox K)) C)
        ≤ ENNReal.ofReal M₀ :=
  exists_forall_adelicGLHaar_image2_unipotentGL2_mul_mul_le_of_isCompact K c' u' d₁' d₂' hc' hC

/-! ### Zone 3 — the same bound, read as finiteness of the measure -/

/-- **Zone 3.** Cross-module reading: a bound by `ofReal M₀` is a finiteness statement, which is what
the measure-theoretic consumers need and what the row's `≤` does not say on its face. -/
theorem adelicGLHaar_image2_lt_top (K : Type) [Field K] [NumberField K]
    (c' u' d₁' d₂' : ℝ) (hc' : 0 < c')
    {C : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hC : IsCompact C)
    {s : GL (Fin 2) (AdeleRing (𝓞 K) K)} (hs : s ∈ centreCutSiegelSet K c' u' d₁' d₂') :
    adelicGLHaar (Fin 2) (𝓞 K) K
        (Set.image2 (fun (t : AdeleRing (𝓞 K) K) (c : GL (Fin 2) (AdeleRing (𝓞 K) K)) =>
          unipotentGL2 t * s * c) (closure (adelicBox K)) C)
      < ⊤ := by
  obtain ⟨M₀, -, hM₀⟩ := exists_bound_on_centreCutSiegelSet K c' u' d₁' d₂' hc' hC
  exact lt_of_le_of_lt (hM₀ s hs) ENNReal.ofReal_lt_top

/-! ### Zone 4 — the invariant membership is not vacuous -/

/-- **Zone 4.** At `y = 1` the row's exactness gives a genuine member of the rational-centre
unipotent set: the conjugate of the identity by `heckeGen v * centralScalar u`. -/
theorem one_mem_conj_heckeGen_mul_centralScalar (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (u : (AdeleRing (𝓞 K) K)ˣ) :
    (heckeGen (𝓞 K) K v * centralScalar (𝓞 K) K u) * 1 *
        (heckeGen (𝓞 K) K v * centralScalar (𝓞 K) K u)⁻¹ ∈
      rationalCentreUnipotent K :=
  (mem_rationalCentreUnipotent_iff_heckeGen_mul_centralScalar_conj_mem K v u 1).mp
    (Subgroup.one_mem _)

/-! ### Zone 5 — the central parameter dropped -/

/-- **Zone 5.** At `u = 1` the row specialises: membership in the rational-centre unipotent set is
invariant under conjugation by the Hecke element `heckeGen v` alone. This is the form the Hecke
operators use. -/
theorem mem_iff_heckeGen_conj_mem (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (y : AdelicGL2 (𝓞 K) K) :
    y ∈ rationalCentreUnipotent K ↔
      heckeGen (𝓞 K) K v * y * (heckeGen (𝓞 K) K v)⁻¹ ∈
        rationalCentreUnipotent K := by
  simpa using
    mem_rationalCentreUnipotent_iff_heckeGen_mul_centralScalar_conj_mem K v
      (1 : (AdeleRing (𝓞 K) K)ˣ) y

/-! ### Zone 6 — the module's own engine, spent as a rewriting rule -/

/-- **Zone 6.** The engine `diagOne_mul_unipotentGL2_mul_inv` is not merely an ingredient of the
row: it says the `diagOne`-conjugate of a unipotent matrix is the unipotent matrix of `τ * x`. -/
theorem conj_diagOne_unipotentGL2 (K : Type) [Field K] [NumberField K]
    (τ : (AdeleRing (𝓞 K) K)ˣ) (x : AdeleRing (𝓞 K) K) :
    diagOne τ * unipotentGL2 x * (diagOne τ)⁻¹ =
      unipotentGL2 ((τ : AdeleRing (𝓞 K) K) * x) :=
  diagOne_mul_unipotentGL2_mul_inv K τ x

end AutomorphicFormSetAF83BConsumer
