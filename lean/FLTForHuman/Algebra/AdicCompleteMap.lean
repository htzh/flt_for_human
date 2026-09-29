/-
  `IsAdicComplete` descends along a surjective ring homomorphism.

  The generic adic-completion fact of the patching exit: if `R` is Noetherian and
  `I`-adically complete, then a surjective image `S = R ⧸ ker f` is
  `(I.map f)`-adically complete. The public statement is
  `Theorems/Thm_IsAdicComplete_map_of_surjective.lean` verbatim; the proof is
  transcribed from `P2M/Sol/S_IsAdicComplete_map_of_surjective.lean` (pinned
  `aa2d8b3`). The only helper, `smodEq_pow_smul_top_iff`, is `private`.

  **Dedup note (playbook §2).** The pin repeats the four-line
  `smodEq_pow_smul_top_iff` in `S_MvPowerSeries_isAdicComplete_maximalIdeal.lean`
  and `S_IsAdicComplete_map_of_surjective.lean`. The module split here puts the
  multivariate power-series copy in `FLTForHuman/Algebra/MvPowerSeriesRegular.lean`
  and this generic copy here; sharing would force one module to import the other
  and drag the power-series imports into a generic algebra file, so the helper is
  stated twice — the option the SET-5 work order §2 explicitly allows for this
  four-line lemma.
-/
import Mathlib.RingTheory.AdicCompletion.Noetherian

set_option autoImplicit false

universe u v

namespace IsAdicCompleteMap

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- `x ≡ y` modulo `I ^ n • ⊤` is `x - y ∈ I ^ n`. -/
private theorem smodEq_pow_smul_top_iff (I : Ideal R) (n : ℕ) (x y : R) :
    x ≡ y [SMOD (I ^ n • ⊤ : Submodule R R)] ↔ x - y ∈ I ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

/-- **`IsAdicComplete` descends along a surjective ring homomorphism.** If `R` is
Noetherian and `I`-adically complete then a surjective image `S` is complete at
`I.map f`. The pin's `isAdicComplete_map_of_surjective` (private here; the public
statement is the `Theorems/` wrapper). -/
private theorem isAdicComplete_map_of_surjective [IsNoetherianRing R] (I : Ideal R)
    [IsAdicComplete I R] (f : R →+* S)
    (hf : Function.Surjective f) : IsAdicComplete (I.map f) S := by
  have hI : I ≤ (⊥ : Ideal R).jacobson := IsAdicComplete.le_jacobson_bot I
  have hS : IsNoetherianRing S := isNoetherianRing_of_surjective R S f hf

  have hJ : I.map f ≤ (⊥ : Ideal S).jacobson := by
    intro x hx
    rw [Ideal.mem_map_iff_of_surjective f hf] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [Ideal.mem_jacobson_bot]
    intro y
    obtain ⟨b, rfl⟩ := hf y
    have hu := Ideal.mem_jacobson_bot.mp (hI ha) b
    simpa using hu.map f
  have hH : IsHausdorff (I.map f) S := IsHausdorff.of_le_jacobson _ _ hJ

  have hP : IsPrecomplete (I.map f) S := by
    refine ⟨fun g hg => ?_⟩

    have hdiff : ∀ n, ∃ d : R, d ∈ I ^ n ∧ f d = g (n + 1) - g n := by
      intro n
      have h := (smodEq_pow_smul_top_iff _ _ _ _).mp (hg (Nat.le_succ n)).symm
      rw [← Ideal.map_pow, Ideal.mem_map_iff_of_surjective f hf] at h
      exact h
    choose d hdI hdf using hdiff
    obtain ⟨r₀, hr₀⟩ := hf (g 0)

    let r : ℕ → R := fun n => Nat.rec r₀ (fun k acc => acc + d k) n
    have hr_succ : ∀ n, r (n + 1) = r n + d n := fun n => rfl
    have hfr : ∀ n, f (r n) = g n := by
      intro n
      induction n with
      | zero => exact hr₀
      | succ k ih => rw [hr_succ, map_add, ih, hdf]; ring
    have hcauchy : ∀ m n, m ≤ n → r n - r m ∈ I ^ m := by
      intro m n hmn
      induction n, hmn using Nat.le_induction with
      | base => simp
      | succ k hmk ih =>
        rw [hr_succ, show r k + d k - r m = (r k - r m) + d k by ring]
        exact Ideal.add_mem _ ih (Ideal.pow_le_pow_right hmk (hdI k))
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete I R) (f := r)
      (fun {m n} hmn => by
        rw [smodEq_pow_smul_top_iff]
        have := hcauchy m n hmn
        rwa [← neg_sub, Ideal.neg_mem_iff])
    refine ⟨f L, fun n => ?_⟩
    rw [smodEq_pow_smul_top_iff, ← hfr n, ← map_sub, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ ((smodEq_pow_smul_top_iff _ _ _ _).mp (hL n))
  exact ⟨⟩

end IsAdicCompleteMap

/-- **`IsAdicComplete` descends along a surjective ring homomorphism.** Stated
verbatim from `Theorems/Thm_IsAdicComplete_map_of_surjective.lean`. -/
theorem IsAdicComplete.map_of_surjective {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R] (f : R →+* S)
    (hf : Function.Surjective f) : IsAdicComplete (I.map f) S :=
  IsAdicCompleteMap.isAdicComplete_map_of_surjective I f hf
