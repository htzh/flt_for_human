/-
  Two `q`-expansion facts the Sturm bound consumes.

  * `UpperHalfPlane.qExpansion_coeff_nat_mul` — multiplying the period by a
    positive `M` reindexes the coefficients: `n` is `M` times an index of the
    old expansion, and the others vanish. This is what turns the Sturm
    hypothesis on the period-`M` expansion into a statement about the period-`1`
    expansion.
  * `UpperHalfPlane.qExpansion_prod` — the `q`-expansion of a finite product is
    the product of the `q`-expansions, provided each factor is analytic at the
    cusp. The general-level Sturm bound applies this to
    `ModularForm.norm = ∏_q quotientFunc f q`.

  Both are proved from mathlib's `qExpansion_mul`/`cuspFunction_mul` and
  `qExpansion_coeff_unique`. The pin repeats `qExpansion_coeff_nat_mul` a second
  time inside `S_ModularForm_levelOne_eq_zero_of_lt_order_qExpansion.lean`; the
  port writes it once here.

  FLT provenance, pinned `aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_UpperHalfPlane_qExpansion_coeff_nat_mul.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_UpperHalfPlane_qExpansion_prod.lean
-/
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.PowerSeries.Order

set_option autoImplicit false

noncomputable section

open Complex Filter Function UpperHalfPlane ModularForm SlashInvariantFormClass ModularFormClass

open scoped Real MatrixGroups Topology Manifold

/-- A `FunLike` wrapper for a bare `ℍ → ℂ`. Mathlib's `qExpansion_coeff_unique`
is polymorphic in a `FunLike` type and its inference stalls on the bare function
type; wrapping it restores the coercion the lemma expects. -/
private def QExpansionFnLike : Type := ℍ → ℂ

private instance : FunLike QExpansionFnLike ℍ ℂ where
  coe f := f
  coe_injective _ _ h := h

/-- Coefficient of a `q`-expansion when the period is multiplied by `M`. -/
theorem UpperHalfPlane.qExpansion_coeff_nat_mul {h : ℝ} (hh : 0 < h) {F : ℍ → ℂ}
    (hper : Function.Periodic (F ∘ UpperHalfPlane.ofComplex) h) (hhol : MDiff F)
    (hbdd : UpperHalfPlane.IsBoundedAtImInfty F) {M : ℕ} (hM : 0 < M) (n : ℕ) :
    (qExpansion (M * h) F).coeff n = if M ∣ n then (qExpansion h F).coeff (n / M) else 0 := by
  have hMh : 0 < (M : ℝ) * h := by positivity
  have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hh0 : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hper' : Periodic (F ∘ ofComplex) (((M : ℝ) * h : ℝ) : ℂ) := by
    simpa using hper.nat_mul M
  have han : AnalyticAt ℂ (cuspFunction (M * h) F) 0 :=
    analyticAt_cuspFunction_zero hMh hper' hhol hbdd
  set c : ℕ → ℂ := fun n ↦ if M ∣ n then (qExpansion h F).coeff (n / M) else 0 with hc
  have hsum : ∀ τ : ℍ, HasSum (fun m ↦ c m • Periodic.qParam (M * h) τ ^ m) (F τ) := by
    intro τ
    have hq : Periodic.qParam h τ = Periodic.qParam (M * h) τ ^ M := by
      simp only [Periodic.qParam, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      field_simp
    have hs := hasSum_qExpansion hh hper hhol hbdd τ
    simp_rw [hq, ← pow_mul] at hs
    have hinj : Injective (fun m : ℕ ↦ M * m) := mul_right_injective₀ hM.ne'
    have hsupp : ∀ x ∉ Set.range (fun m : ℕ ↦ M * m),
        (fun m ↦ c m • Periodic.qParam (M * h) τ ^ m) x = 0 := by
      intro x hx
      have : ¬ M ∣ x := by
        rintro ⟨d, rfl⟩
        exact hx ⟨d, rfl⟩
      simp [hc, this]
    refine (hinj.hasSum_iff hsupp).mp ?_
    convert hs using 1
    ext m
    simp [hc, Nat.mul_div_cancel_left _ hM]
  have key := qExpansion_coeff_unique (F := QExpansionFnLike) (show QExpansionFnLike from F)
    hMh han hsum n
  exact key.symm

/-- The `q`-expansion of a finite product is the product of the `q`-expansions. -/
theorem UpperHalfPlane.qExpansion_prod {h : ℝ} {ι : Type*} (s : Finset ι) {F : ι → ℍ → ℂ}
    (hF : ∀ i ∈ s, AnalyticAt ℂ (cuspFunction h (F i)) 0) :
    qExpansion h (∏ i ∈ s, F i) = ∏ i ∈ s, qExpansion h (F i) := by
  suffices H : qExpansion h (∏ i ∈ s, F i) = ∏ i ∈ s, qExpansion h (F i) ∧
      AnalyticAt ℂ (cuspFunction h (∏ i ∈ s, F i)) 0 from H.1
  induction s using Finset.cons_induction with
  | empty =>
    have h1 : cuspFunction h (1 : ℍ → ℂ) = 1 := by
      ext q
      rcases eq_or_ne q 0 with rfl | hq
      · simp [cuspFunction, Periodic.cuspFunction]
        exact Filter.Tendsto.limUnder_eq tendsto_const_nhds
      · simp [cuspFunction, Periodic.cuspFunction_eq_of_nonzero h _ hq]
    refine ⟨by simpa using qExpansion_one h, ?_⟩
    rw [Finset.prod_empty, h1]
    exact analyticAt_const
  | cons a s ha ih =>
    have hFa : AnalyticAt ℂ (cuspFunction h (F a)) 0 := hF a (Finset.mem_cons_self a s)
    obtain ⟨ih1, ih2⟩ := ih fun i hi ↦ hF i (Finset.mem_cons_of_mem hi)
    rw [Finset.prod_cons, Finset.prod_cons, qExpansion_mul hFa ih2, ih1]
    refine ⟨rfl, ?_⟩
    rw [cuspFunction_mul hFa.continuousAt ih2.continuousAt]
    exact hFa.mul ih2

end
