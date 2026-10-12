/-
  Non-vanishing right convolution with a level-`N` factorisable test function.

  The headline of the `levelOne` column: a continuous non-zero `φ` invariant under
  `levelOne N ⊓ finiteAdelicGL2Subgroup K` admits a factorisable test function `f`,
  supported near the identity, whose right convolution with `φ` is non-zero. The proof
  assembles the `TestFnNearIdentity` prelude: a radius on which `φ` is nearly constant,
  the smooth test function `testFn`, and the integral bound `rightConv_ne_zero_of_bound`.

  Transcribed from the `solution` theorem of
  `P2M/Sol/S_AutomorphicForm_exists_isFactorizableTestFn_rightConv_ne_zero_of_levelOne_invariant.lean:481–508`
  (pinned `aa2d8b3`), at its `Theorems/` wrapper name; the shared prelude is the port's
  `AutomorphicForm.TestFnNearIdentity` (`topics/PORTING-AutomorphicForm.md`).
-/
import FLTForHuman.AutomorphicForm.Adelic.TestFnNearIdentity
import FLTForHuman.AutomorphicForm.Adelic.TestFnTop

set_option autoImplicit false

open NumberField NumberField.AdelicLevel
open IsDedekindDomain AutomorphicForm

open scoped Classical

noncomputable section

open AutomorphicForm.TestFnNearIdentity in

theorem AutomorphicForm.exists_isFactorizableTestFn_rightConv_ne_zero_of_levelOne_invariant
    (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hcont : Continuous φ) (hne : ∃ g, φ g ≠ 0)
    (hlev : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
      φ (g * k) = φ g) :
    ∃ f : AdelicGL2 (𝓞 K) K → ℂ,
      IsFactorizableTestFn K f ∧
      (∀ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ∀ x, f (k * x) = f x) ∧
      (∀ x, f x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 K) K,
        glFin (𝓞 K) K a = 1 ∧ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K ∧ x = a * k) ∧
      ∃ g, rightConv K φ f g ≠ 0 := by
  obtain ⟨g₀, hg₀⟩ := hne
  obtain ⟨ρ, hρ, hρε, hV⟩ := exists_radius_of_continuous K φ hcont g₀ hg₀
  have htier := isFactorizableTestFn_testFn K ρ hρ hρε hN
  refine ⟨testFn K ρ hρ N, htier, fun _ hk x => testFn_mul_of_mem K ρ hρ N hk x,
    fun x hx => testFn_support K ρ hρ N x hx, g₀, ?_⟩
  obtain ⟨hfc, hfs⟩ :=
    AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn K _ htier
  refine rightConv_ne_zero_of_bound K φ hcont g₀ hg₀ _ hfc hfs (testFnR K ρ hρ N)
    (testFn_eq_ofReal K ρ hρ hρε N) (testFnR_nonneg K ρ hρ N)
    (by rw [testFnR_one]; exact one_ne_zero) fun x hx => ?_
  obtain ⟨hdist, hfin⟩ := of_testFnR_ne_zero K ρ hρ N x hx
  have hx' : g₀ * x = (g₀ * adelicArchGLIncl K (glArch (𝓞 K) K x)) *
      ((adelicArchGLIncl K (glArch (𝓞 K) K x))⁻¹ * x) := by
    rw [mul_assoc, mul_inv_cancel_left]
  rw [hx', hlev _ _ (testFn_decomp K N x hfin)]
  exact hV _ hdist
