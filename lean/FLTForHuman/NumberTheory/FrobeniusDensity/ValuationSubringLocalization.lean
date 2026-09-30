/-
  The localisation place of `ℚ̄` at a maximal ideal `Qt` of `𝓞 ℚ̄`: the valuation
  subring consisting of the fractions `a / s` with `s ∉ Qt`. It is the place of
  `ℚ̄` cut out by `Qt`, and the hypothesis `hA` of
  `ValuationSubring.isFrobeniusAt_of_forall_smul_sub_pow_mem` names it.

  Transcribed from `P2M/Sol/S_NumberField_exists_valuationSubring_eq_localization.lean`
  (pinned `aa2d8b3`, 109 lines): the pin's public `C6P1T3a` block (`carrier`,
  `mem_carrier`, `one_notMem`, `subring`, `comap_ne_bot`, `mem_or_inv_mem`,
  `valuationSubring`) is transcribed `private` here; only the target is public.
  The mathematics is math/018 §1.4.
-/
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.Algebra.Algebra.Rat
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Valuation.ValuationSubring

set_option autoImplicit false

-- The pin's proofs introduce instances with `haveI` in `Prop` goals; they are
-- transcribed verbatim, as in the other ported proof files.
set_option linter.style.haveILetI false

open scoped NumberField

namespace ValuationSubringLocalizationAux

variable (Qt : Ideal (𝓞 (AlgebraicClosure ℚ))) [Qt.IsMaximal]

/-- The carrier of the localisation of `𝓞 ℚ̄` at `Qt`. -/
private def carrier : Set (AlgebraicClosure ℚ) :=
  {x | ∃ s : 𝓞 (AlgebraicClosure ℚ), s ∉ Qt ∧
    ∃ a : 𝓞 (AlgebraicClosure ℚ), (s : AlgebraicClosure ℚ) * x = a}

omit [Qt.IsMaximal] in
private theorem mem_carrier {x : AlgebraicClosure ℚ} :
    x ∈ carrier Qt ↔ ∃ s : 𝓞 (AlgebraicClosure ℚ), s ∉ Qt ∧
      ∃ a : 𝓞 (AlgebraicClosure ℚ), (s : AlgebraicClosure ℚ) * x = a := Iff.rfl

private theorem one_notMem : (1 : 𝓞 (AlgebraicClosure ℚ)) ∉ Qt :=
  fun h => Ideal.IsPrime.ne_top' ((Ideal.eq_top_iff_one Qt).mpr h)

private noncomputable def subring : Subring (AlgebraicClosure ℚ) where
  carrier := carrier Qt
  mul_mem' := by
    rintro x y ⟨s, hs, a, ha⟩ ⟨t, ht, b, hb⟩
    refine ⟨s * t, fun h => ((Ideal.IsPrime.mem_or_mem inferInstance h).elim hs ht), a * b, ?_⟩
    simp only [NumberField.RingOfIntegers.coe_eq_algebraMap, map_mul] at ha hb ⊢
    rw [← ha, ← hb]; ring
  one_mem' := ⟨1, one_notMem Qt, 1, by simp only [map_one, mul_one]⟩
  add_mem' := by
    rintro x y ⟨s, hs, a, ha⟩ ⟨t, ht, b, hb⟩
    refine ⟨s * t, fun h => ((Ideal.IsPrime.mem_or_mem inferInstance h).elim hs ht), t * a + s * b, ?_⟩
    simp only [NumberField.RingOfIntegers.coe_eq_algebraMap, map_mul, map_add] at ha hb ⊢
    rw [← ha, ← hb]; ring
  zero_mem' := ⟨1, one_notMem Qt, 0, by simp only [map_one, map_zero, mul_zero]⟩
  neg_mem' := by
    rintro x ⟨s, hs, a, ha⟩
    refine ⟨s, hs, -a, ?_⟩
    simp only [NumberField.RingOfIntegers.coe_eq_algebraMap, map_neg] at ha ⊢
    rw [← ha]; ring

private theorem comap_ne_bot (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K] :
    Qt.comap (algebraMap (𝓞 K) (𝓞 (AlgebraicClosure ℚ))) ≠ ⊥ := by

  haveI : (Qt.under ℤ).IsMaximal := Ideal.IsMaximal.under ℤ Qt
  have hne : Qt.under ℤ ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField inferInstance Int.not_isField
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [Ideal.under_def, Ideal.mem_comap] at hn
  intro h
  have hmem : ((n : ℤ) : 𝓞 K) ∈ Qt.comap (algebraMap (𝓞 K) (𝓞 (AlgebraicClosure ℚ))) := by
    rw [Ideal.mem_comap, map_intCast]
    simpa using hn
  rw [h, Ideal.mem_bot] at hmem
  exact hn0 (by exact_mod_cast hmem)

private theorem mem_or_inv_mem (x : AlgebraicClosure ℚ) :
    x ∈ carrier Qt ∨ x⁻¹ ∈ carrier Qt := by

  have hx : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  let K : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.adjoin ℚ {x}
  haveI : FiniteDimensional ℚ K := IntermediateField.adjoin.finiteDimensional hx
  haveI : NumberField K := NumberField.mk
  have hxK : x ∈ K := IntermediateField.mem_adjoin_simple_self ℚ x

  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) :=
    ⟨Qt.comap (algebraMap (𝓞 K) (𝓞 (AlgebraicClosure ℚ))), Ideal.IsPrime.comap _, comap_ne_bot Qt K⟩

  obtain ⟨n, d, hnd⟩ :=
    IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_or_mul_eq (K := K) v ⟨x, hxK⟩
  have hd : algebraMap (𝓞 K) (𝓞 (AlgebraicClosure ℚ)) d ∉ Qt :=
    fun h => d.2 (Ideal.mem_comap.mpr h)
  have coe_alg : ∀ a : 𝓞 K,
      ((algebraMap (𝓞 K) (𝓞 (AlgebraicClosure ℚ)) a : 𝓞 (AlgebraicClosure ℚ)) : AlgebraicClosure ℚ)
        = ((algebraMap (𝓞 K) K a : K) : AlgebraicClosure ℚ) :=
    fun _ => rfl
  rcases hnd with h | h
  ·
    left
    refine ⟨algebraMap (𝓞 K) (𝓞 (AlgebraicClosure ℚ)) d, hd,
      algebraMap (𝓞 K) (𝓞 (AlgebraicClosure ℚ)) n, ?_⟩
    have := congrArg (fun y : K => (y : AlgebraicClosure ℚ)) h
    simp only [MulMemClass.coe_mul] at this
    rw [coe_alg, coe_alg, ← this, mul_comm]
  ·
    right
    have hK := congrArg (fun y : K => (y : AlgebraicClosure ℚ)) h
    simp only [MulMemClass.coe_mul] at hK
    have hx0 : x ≠ 0 := by
      rintro rfl
      apply d.2
      have hd0 : (algebraMap (𝓞 K) K (d : 𝓞 K) : K) = 0 := by
        apply Subtype.ext
        change ((algebraMap (𝓞 K) K (d : 𝓞 K) : K) : AlgebraicClosure ℚ) = 0
        rw [← hK]; simp
      have : (d : 𝓞 K) = 0 := (IsFractionRing.injective (𝓞 K) K) (by rw [hd0, map_zero])
      rw [this]; exact Ideal.zero_mem _
    refine ⟨algebraMap (𝓞 K) (𝓞 (AlgebraicClosure ℚ)) d, hd,
      algebraMap (𝓞 K) (𝓞 (AlgebraicClosure ℚ)) n, ?_⟩
    rw [coe_alg, coe_alg, ← hK, mul_comm x, mul_assoc, mul_inv_cancel₀ hx0, mul_one]

private noncomputable def valuationSubring : ValuationSubring (AlgebraicClosure ℚ) :=
  { subring Qt with
    mem_or_inv_mem' := mem_or_inv_mem Qt }

end ValuationSubringLocalizationAux

theorem NumberField.exists_valuationSubring_eq_localization
    (Qt : Ideal (𝓞 (AlgebraicClosure ℚ))) [Qt.IsMaximal] :
    ∃ A : ValuationSubring (AlgebraicClosure ℚ), ∀ x : AlgebraicClosure ℚ,
      x ∈ A ↔ ∃ s : 𝓞 (AlgebraicClosure ℚ), s ∉ Qt ∧ ∃ a : 𝓞 (AlgebraicClosure ℚ), (s : AlgebraicClosure ℚ) * x = a :=
  ⟨ValuationSubringLocalizationAux.valuationSubring Qt, fun _ => Iff.rfl⟩
