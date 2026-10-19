/-
  Membership in the integral level subgroup, and the rational points `ratGL`.

  `finiteIntegralGL2 R K` is the level-`⊤` congruence subgroup of `GL₂(𝔸_K^fin)`,
  and this module provides the entrywise membership toolbox for it: the integrality
  of `0`, `1` and of the identity matrix at a place, the fact that `unipotentGL2 a`,
  `lowerUnipGL2 a` and `diagTorusGL2 u` are integral whenever their parameters are
  `a.e.` integral (`unipotentGL2_mem`, `lowerUnipGL2_mem`, `diagTorusGL2_mem`), and the
  two denominator tools: `exists_sub_algebraMap_eq_mul_integral` (a finite adèle is
  its global part plus a fixed-denominator integral adèle, via the adèlic box) and
  `exists_common_denominator` (one `d ∈ R` clears the denominators of all
  `Fin 2 × Fin 2 × Fin 2 × Fin 2` entries of `γ⁻¹` and `γ` simultaneously, via
  `IsLocalization.exist_integer_multiples`).

  `ratGL` embeds `GL₂(K)` into `GL₂(𝔸_K^fin)` along `algebraMap K 𝔸^fin`, with its
  multiplicativity and its entry formulae for both `γ` and `γ⁻¹` — the shape every
  conjugation step of the engine rewrites to.

  Transcribed verbatim from
  `P2M/Sol/S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:130–300`
  (the pin's `Membership` block, pinned `aa2d8b3`). The two `NumberField.AdelicBox`
  prerequisites are the port's `AdelicBox.exists_algebraMap_add_mem_integralFiniteAdeles`
  and the `NumberField.AdelicLevel` copy of `algebraMap_mem_adicCompletionIntegers`;
  no statement is changed. The pin's `p2m_export` scaffolding is not transcribed.
-/
import FLTForHuman.NumberTheory.AdelicLevel.StrongApprox.Elementary
import FLTForHuman.NumberTheory.AdelicLevel.Level
import FLTForHuman.NumberTheory.AdelicLevel.IdealBall
import FLTForHuman.NumberTheory.AdelicBox

set_option autoImplicit false

open Matrix IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField AutomorphicForm

noncomputable section

namespace NumberField

namespace AdelicLevel

namespace GL2StrongApproxW8M

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

-- pin: algebraMap_finiteAdeleRing_apply (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:133)
theorem algebraMap_finiteAdeleRing_apply (x : K) (v : HeightOneSpectrum R) :
    (algebraMap K (FiniteAdeleRing R K) x) v = algebraMap K (v.adicCompletion K) x := rfl

-- pin: valued_algebraMap_finiteAdeleRing_apply (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:136)
theorem valued_algebraMap_finiteAdeleRing_apply (k : K) (v : HeightOneSpectrum R) :
    Valued.v ((algebraMap K (FiniteAdeleRing R K) k) v) = v.valuation K k := by
  rw [show (algebraMap K (FiniteAdeleRing R K) k) v = ((k : K) : v.adicCompletion K) from rfl]
  exact valuedAdicCompletion_eq_valuation' v k

-- pin: one_apply_mem (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:141)
theorem one_apply_mem (v : HeightOneSpectrum R) :
    (1 : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K := by
  rw [coe_one_apply]; exact one_mem _

-- pin: zero_apply_mem (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:145)
theorem zero_apply_mem (v : HeightOneSpectrum R) :
    (0 : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K := by
  rw [coe_zero_apply]; exact zero_mem _

-- pin: one_matrix_apply_mem (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:149)
theorem one_matrix_apply_mem (i j : Fin 2) (v : HeightOneSpectrum R) :
    (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j v ∈ v.adicCompletionIntegers K := by
  by_cases h : i = j
  · subst h
    rw [Matrix.one_apply_eq]
    exact one_apply_mem R K v
  · rw [Matrix.one_apply_ne h]
    exact zero_apply_mem R K v

-- pin: unipotentGL2_mem (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:158)
theorem unipotentGL2_mem {a : FiniteAdeleRing R K}
    (ha : ∀ v : HeightOneSpectrum R, a v ∈ v.adicCompletionIntegers K) :
    unipotentGL2 a ∈ finiteIntegralGL2 R K := by
  rw [mem_finiteIntegralGL2_iff]
  constructor
  · intro i j v
    fin_cases i <;> fin_cases j
    · exact one_apply_mem R K v
    · exact ha v
    · exact zero_apply_mem R K v
    · exact one_apply_mem R K v
  · intro i j v
    fin_cases i <;> fin_cases j
    · exact one_apply_mem R K v
    · show (-a) v ∈ v.adicCompletionIntegers K
      rw [coe_neg_apply]
      exact neg_mem (ha v)
    · exact zero_apply_mem R K v
    · exact one_apply_mem R K v

-- pin: lowerUnipGL2_mem (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:178)
theorem lowerUnipGL2_mem {a : FiniteAdeleRing R K}
    (ha : ∀ v : HeightOneSpectrum R, a v ∈ v.adicCompletionIntegers K) :
    lowerUnipGL2 a ∈ finiteIntegralGL2 R K := by
  rw [mem_finiteIntegralGL2_iff]
  constructor
  · intro i j v
    fin_cases i <;> fin_cases j
    · exact one_apply_mem R K v
    · exact zero_apply_mem R K v
    · exact ha v
    · exact one_apply_mem R K v
  · intro i j v
    fin_cases i <;> fin_cases j
    · exact one_apply_mem R K v
    · exact zero_apply_mem R K v
    · show (-a) v ∈ v.adicCompletionIntegers K
      rw [coe_neg_apply]
      exact neg_mem (ha v)
    · exact one_apply_mem R K v

-- pin: diagTorusGL2_mem (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:198)
theorem diagTorusGL2_mem {u : (FiniteAdeleRing R K)ˣ}
    (hu : ∀ v : HeightOneSpectrum R, (u : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K)
    (hu' : ∀ v : HeightOneSpectrum R,
      ((u⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K) :
    diagTorusGL2 u ∈ finiteIntegralGL2 R K := by
  rw [mem_finiteIntegralGL2_iff]
  constructor
  · intro i j v
    fin_cases i <;> fin_cases j
    · exact one_apply_mem R K v
    · exact zero_apply_mem R K v
    · exact zero_apply_mem R K v
    · exact hu v
  · intro i j v
    fin_cases i <;> fin_cases j
    · exact one_apply_mem R K v
    · exact zero_apply_mem R K v
    · exact zero_apply_mem R K v
    · exact hu' v

-- pin: exists_sub_algebraMap_eq_mul_integral (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:218)
theorem exists_sub_algebraMap_eq_mul_integral (a : FiniteAdeleRing R K) (d : K)
    (hd : d ≠ 0) :
    ∃ q : K, ∀ v : HeightOneSpectrum R,
      ∃ c ∈ v.adicCompletionIntegers K,
        a v - algebraMap K (v.adicCompletion K) q
          = algebraMap K (v.adicCompletion K) d * c := by
  have hdu : IsUnit (algebraMap K (FiniteAdeleRing R K) d) :=
    (Ne.isUnit hd).map (algebraMap K (FiniteAdeleRing R K))
  set a' : FiniteAdeleRing R K := ↑hdu.unit⁻¹ * a with ha'
  obtain ⟨k, hk⟩ := NumberField.AdelicBox.exists_algebraMap_add_mem_integralFiniteAdeles R K a'
  have hk' : ∀ v : HeightOneSpectrum R,
      (algebraMap K (FiniteAdeleRing R K) k + a') v ∈ v.adicCompletionIntegers K := hk
  refine ⟨d * (-k), fun v ↦ ⟨a' v - algebraMap K (v.adicCompletion K) (-k), ?_, ?_⟩⟩
  · have hkv : algebraMap K (v.adicCompletion K) k + a' v ∈ v.adicCompletionIntegers K := hk' v
    rw [map_neg, sub_neg_eq_add, add_comm]
    exact hkv
  have hda' : algebraMap K (FiniteAdeleRing R K) d * a' = a := by
    have h1 : algebraMap K (FiniteAdeleRing R K) d * ↑hdu.unit⁻¹ = 1 := by
      have h2 := hdu.unit.mul_inv
      rwa [hdu.unit_spec] at h2
    rw [ha', ← mul_assoc, h1, one_mul]
  calc a v - algebraMap K (v.adicCompletion K) (d * -k)
      = (algebraMap K (FiniteAdeleRing R K) d * a') v
          - algebraMap K (v.adicCompletion K) d * algebraMap K (v.adicCompletion K) (-k) := by
        rw [hda', map_mul]
    _ = algebraMap K (v.adicCompletion K) d * a' v
          - algebraMap K (v.adicCompletion K) d * algebraMap K (v.adicCompletion K) (-k) := by
        rw [coe_mul_apply, algebraMap_finiteAdeleRing_apply]
    _ = algebraMap K (v.adicCompletion K) d
          * (a' v - algebraMap K (v.adicCompletion K) (-k)) := by ring

-- pin: exists_common_denominator (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:249)
theorem exists_common_denominator (γ : GL (Fin 2) K) :
    ∃ d : R, d ≠ 0 ∧ ∀ i j k l : Fin 2,
      ∃ n : R, algebraMap R K d
          * (((γ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j
            * ((γ : Matrix (Fin 2) (Fin 2) K) k l))
        = algebraMap R K n := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R)
    (Finset.univ : Finset (Fin 2 × Fin 2 × Bool))
    (fun p ↦ if p.2.2 then ((γ : Matrix (Fin 2) (Fin 2) K) p.1 p.2.1)
      else (((γ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) p.1 p.2.1))
  have hb0 : (b : R) ≠ 0 := nonZeroDivisors.ne_zero b.2
  refine ⟨b * b, mul_ne_zero hb0 hb0, fun i j k l ↦ ?_⟩
  obtain ⟨n₁, hn₁⟩ := hb (i, j, false) (Finset.mem_univ _)
  obtain ⟨n₂, hn₂⟩ := hb (k, l, true) (Finset.mem_univ _)
  refine ⟨n₁ * n₂, ?_⟩
  have h₁ : algebraMap R K n₁
      = algebraMap R K b * (((γ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j) := by
    simpa [Algebra.smul_def] using hn₁
  have h₂ : algebraMap R K n₂
      = algebraMap R K b * ((γ : Matrix (Fin 2) (Fin 2) K) k l) := by
    simpa [Algebra.smul_def] using hn₂
  rw [map_mul, map_mul, h₁, h₂]
  ring

-- pin: ratGL (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:274)
abbrev ratGL (γ : GL (Fin 2) K) : GL (Fin 2) (FiniteAdeleRing R K) :=
  GeneralLinearGroup.map (algebraMap K (FiniteAdeleRing R K)) γ

-- pin: ratGL_mul (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:277)
theorem ratGL_mul (γ γ' : GL (Fin 2) K) : ratGL R K (γ * γ') = ratGL R K γ * ratGL R K γ' :=
  map_mul _ _ _

-- pin: ratGL_inv_mul_val (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:280)
theorem ratGL_inv_mul_val (γ : GL (Fin 2) K) :
    (((ratGL R K γ)⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K))
      * ((ratGL R K γ : GL (Fin 2) (FiniteAdeleRing R K)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

-- pin: ratGL_val_apply (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:287)
theorem ratGL_val_apply (γ : GL (Fin 2) K) (i j : Fin 2) :
    ((ratGL R K γ : GL (Fin 2) (FiniteAdeleRing R K)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j
      = algebraMap K (FiniteAdeleRing R K) ((γ : Matrix (Fin 2) (Fin 2) K) i j) :=
  GeneralLinearGroup.map_apply (algebraMap K (FiniteAdeleRing R K)) i j γ

-- pin: ratGL_inv_val_apply (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:293)
theorem ratGL_inv_val_apply (γ : GL (Fin 2) K) (i j : Fin 2) :
    (((ratGL R K γ)⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j
      = algebraMap K (FiniteAdeleRing R K)
          (((γ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j) := by
  rw [show (ratGL R K γ)⁻¹ = ratGL R K γ⁻¹ from
    (map_inv (GeneralLinearGroup.map (algebraMap K (FiniteAdeleRing R K))) γ).symm]
  exact GeneralLinearGroup.map_apply (algebraMap K (FiniteAdeleRing R K)) i j γ⁻¹

end GL2StrongApproxW8M

end AdelicLevel

end NumberField
