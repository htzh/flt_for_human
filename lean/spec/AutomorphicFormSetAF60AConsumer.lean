/-
  SET-AF60A consumer: the `Kf`-smooth predicate, spent.

  **The zone.** Two rows in one module, hence two executed compositions:

  * `FLTForHuman/AutomorphicForm/Adelic/KfSmoothReduction.lean` (A):
    `AutomorphicForm.apply_mul_eq_of_isKfSmooth_of_forall_placeEmbed_of_mem_maximalCompactAway`;
  * the same module (B):
    `AutomorphicForm.IsKfSmooth.exists_isCompact_isOpen_eq_inf_forall_apply_mul_eq`.

  **The readings.**

  * Zone A. The row is the invariance of a `Kf`-smooth function under a small
    maximal-compact-away element: for every `k` in the subgroup `maximalCompactAway K S` that the
    spherical hypothesis does not see, `φ (g * k) = φ g`. The consumer *spends* it as an invariance
    rather than as a formula: first it is packaged at a *given* element `k` of that subgroup (the
    reading the reduction needs, a right translation by a small element fixing the value), then it is
    spent at the inverse element — the row applied to `k⁻¹`, which the subgroup structure supplies —
    and finally composed with itself, `k₁` at `g` and `k₂` at `g * k₁`, so that the whole small
    subgroup acts trivially by right translation.
  * Zone A, concrete. The hypotheses of the row (`IsKfSmooth` and the spherical invariance) are
    properties of an arbitrary automorphic form, so they enter in hypothesis form in Zone A. To show
    the row is not vacuous, the same composition is executed on the module's own constant function,
    where both hypotheses are *discharged* — `isKfSmooth_const` for the first, `rfl` for the second
    — and no hypothesis survives.
  * Zone B. The row factors a `Kf`-smooth function through the finite variable: the invariance holds
    on a compact subgroup `U = O ⊓ finiteAdelicGL2Subgroup F` with `O` open. The consumer reads the
    factorization *at a point of the compact-open set*: every `k ∈ U` is in the finite-part subgroup,
    so `glArch k = 1`, and the value of `φ` at any two points
    `g * k₁`, `g * k₂` of the same `U`-coset is the same — the finite variable is invisible on `U`.
  * Zone B, concrete. As in Zone A the hypothesis is discharged on the constant function, where the
    row produces its compact-open `U` outright.

  This module is outside every library: it is a spec-side composition check, not part of the
  port's import graph.
-/
import FLTForHuman.AutomorphicForm.Adelic.KfSmoothReduction

noncomputable section

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm
open scoped Topology

namespace AutomorphicForm.SetAF60AConsumer

/-! ### Zone A: the small maximal-compact-away element, spent -/

section smallElement

variable (K : Type) [Field K] [NumberField K]

/-- **Zone A, the invariance at a point.**  The row applied at a given small element: a `Kf`-smooth
`φ` whose spherical hypothesis misses the set `S` is fixed by right translation by any `k` of
`maximalCompactAway K S`.  This is the invariance in the shape the reduction consumes it — a
translation of the argument that leaves the value alone. -/
theorem consumer_A_small_element_invariance
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφ : IsKfSmooth K φ)
    (hsph : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
        φ (g * UnramifiedWhittaker.placeEmbed K v
          (Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = φ g)
    {k : AdelicGL2 (𝓞 K) K} (hk : k ∈ maximalCompactAway K S) :
    ∀ g : AdelicGL2 (𝓞 K) K, φ (g * k) = φ g :=
  AutomorphicForm.apply_mul_eq_of_isKfSmooth_of_forall_placeEmbed_of_mem_maximalCompactAway
    K S φ hφ hsph k hk

/-- **Zone A, spent at the inverse.**  The subgroup structure of `maximalCompactAway K S` supplies
`k⁻¹`, and the row applied there gives the invariance under the inverse element.  So the invariance
is a subgroup invariance and not a one-element accident. -/
theorem consumer_A_invariant_under_inverse
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφ : IsKfSmooth K φ)
    (hsph : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
        φ (g * UnramifiedWhittaker.placeEmbed K v
          (Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = φ g)
    {k : AdelicGL2 (𝓞 K) K} (hk : k ∈ maximalCompactAway K S) :
    ∀ g : AdelicGL2 (𝓞 K) K, φ (g * k⁻¹) = φ g :=
  consumer_A_small_element_invariance K S φ hφ hsph (inv_mem hk)

/-- **Zone A, spent twice.**  The row is applied at `k₁` and then again at `k₂` from the translated
point `g * k₁`: the invariance composes, so the product of two small elements also fixes the
value. -/
theorem consumer_A_invariant_under_product
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφ : IsKfSmooth K φ)
    (hsph : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
        φ (g * UnramifiedWhittaker.placeEmbed K v
          (Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = φ g)
    {k₁ k₂ : AdelicGL2 (𝓞 K) K} (hk₁ : k₁ ∈ maximalCompactAway K S)
    (hk₂ : k₂ ∈ maximalCompactAway K S) :
    ∀ g : AdelicGL2 (𝓞 K) K, φ (g * (k₁ * k₂)) = φ g := by
  intro g
  rw [← mul_assoc, consumer_A_small_element_invariance K S φ hφ hsph hk₂ (g * k₁),
    consumer_A_small_element_invariance K S φ hφ hsph hk₁ g]

/-- **Zone A, the non-vacuous instance.**  The same invariance executed on the module's own constant
function: `IsKfSmooth` is discharged by `isKfSmooth_const` and the spherical hypothesis by `rfl`, so
the row hands back the invariance with no hypothesis of its own left over. -/
theorem consumer_A_concrete (c : ℂ) (S : Finset (HeightOneSpectrum (𝓞 K)))
    {k : AdelicGL2 (𝓞 K) K} (hk : k ∈ maximalCompactAway K S) :
    ∀ g : AdelicGL2 (𝓞 K) K, (fun _ : AdelicGL2 (𝓞 K) K => c) (g * k) = c :=
  consumer_A_small_element_invariance K S (fun _ => c) (isKfSmooth_const K c)
    (fun _ _ _ _ => rfl) hk

end smallElement

/-! ### Zone B: the factorization, read at a point of the compact-open set -/

section compactOpen

variable (F : Type) [Field F] [NumberField F]

/-- **Zone B, the compact-open subgroup.**  The row produces a compact `U = O ⊓ K_f` on which `φ` is
invariant; the consumer reads the factorization at a point of it: every `k ∈ U` is in the
finite-part subgroup, hence `glArch k = 1`, and the invariance holds there. -/
theorem consumer_B_compact_open_invariant
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsKfSmooth F φ) :
    ∃ U : Subgroup (AdelicGL2 (𝓞 F) F), IsCompact (U : Set (AdelicGL2 (𝓞 F) F)) ∧
      (∀ k ∈ U, glArch (𝓞 F) F k = 1) ∧
      ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, φ (g * k) = φ g := by
  obtain ⟨U, hUc, O, _hOo, hUO, hinv⟩ :=
    AutomorphicForm.IsKfSmooth.exists_isCompact_isOpen_eq_inf_forall_apply_mul_eq F φ hφ
  refine ⟨U, hUc, fun k hk => ?_, hinv⟩
  have hk' : k ∈ O ⊓ finiteAdelicGL2Subgroup F := hUO ▸ hk
  exact (mem_finiteAdelicGL2Subgroup_iff F k).mp (Subgroup.mem_inf.mp hk').2

/-- **Zone B, read at the points of a coset.**  The factorization says the finite variable is
invisible on `U`: two points `g * k₁` and `g * k₂` of the same `U`-coset carry the same value.  This
is the row used twice, at the two points of the compact-open set. -/
theorem consumer_B_constant_on_finite_coset
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsKfSmooth F φ) :
    ∃ U : Subgroup (AdelicGL2 (𝓞 F) F), IsCompact (U : Set (AdelicGL2 (𝓞 F) F)) ∧
      ∀ (g k₁ k₂ : AdelicGL2 (𝓞 F) F), k₁ ∈ U → k₂ ∈ U → φ (g * k₁) = φ (g * k₂) := by
  obtain ⟨U, hUc, _hUf, hinv⟩ := consumer_B_compact_open_invariant F φ hφ
  exact ⟨U, hUc, fun g k₁ k₂ h₁ h₂ => by rw [hinv g k₁ h₁, hinv g k₂ h₂]⟩

/-- **Zone B, the non-vacuous instance.**  On the constant function the row's hypothesis is
discharged, and it still produces a compact subgroup on which the finite variable is invisible. -/
theorem consumer_B_concrete (c : ℂ) :
    ∃ U : Subgroup (AdelicGL2 (𝓞 F) F), IsCompact (U : Set (AdelicGL2 (𝓞 F) F)) ∧
      ∀ (g k₁ k₂ : AdelicGL2 (𝓞 F) F), k₁ ∈ U → k₂ ∈ U →
        (fun _ : AdelicGL2 (𝓞 F) F => c) (g * k₁) = (fun _ : AdelicGL2 (𝓞 F) F => c) (g * k₂) :=
  consumer_B_constant_on_finite_coset F (fun _ => c) (isKfSmooth_const F c)

end compactOpen

end AutomorphicForm.SetAF60AConsumer
