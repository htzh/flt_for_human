/-
  Conjugation of unipotent and lower-unipotent elements into the integral level.

  The engine of the strong-approximation proof: after fixing a rational point `γ` and
  a common denominator `d` of `γ⁻¹` and `γ`, an additive parameter `q ∈ K` can be
  chosen so that the conjugated unipotent
  `(ratGL γ)⁻¹ * unipotentGL2 (a - q) * ratGL γ`
  is integral at every finite place (`exists_conj_unipotent_mem`, and the same for
  `lowerUnipGL2`). The key local input is `conj_entry_mem`: a conjugated unipotent is
  the identity plus one rank-one term whose entries are `d`-multiples of integral
  adèles, so they are integral. `absorb_unipotent_left`/`absorb_lowerUnip_left` then
  move such a unipotent factor into the rational point by replacing `γ` with
  `unipotentGL2 q * γ`, which is what the Gauss decomposition needs.

  `exists_lowerUnip_translate_isUnit` is the translation step of the Gauss
  decomposition: for an integral adèle `t`, translating the lower-left entry of `g`
  by `t` along the last column (`g 1 0 + g 1 1 * t`, `mul_lowerUnip_apply_one_zero`)
  makes it a unit, and the valuation argument chooses `t` place by place as `1` or
  `0` according to the comparison of the two valuations (`Valuation.map_add_of_distinct_val`).
  `det_apply` is the entrywise determinant formula it needs.

  Transcribed verbatim from
  `P2M/Sol/S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:302–656`
  (the pin's `Conjugation` block, pinned `aa2d8b3`). One call site differs from the
  pin: `NumberField.AdelicBox.algebraMap_mem_adicCompletionIntegers R K v n` (pin:331)
  is written `algebraMap_mem_adicCompletionIntegers v n` here, because the port homes
  that lemma at `NumberField.AdelicLevel.algebraMap_mem_adicCompletionIntegers` with
  `(v) (r)` explicit (`NumberTheory/AdelicLevel/IdealBall.lean:87`). The statement is
  unchanged; no alias was added to `AdelicBox.lean`.
-/
import FLTForHuman.NumberTheory.AdelicLevel.StrongApprox.Membership

set_option autoImplicit false

open Matrix IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField AutomorphicForm

noncomputable section

namespace NumberField

namespace AdelicLevel

namespace GL2StrongApproxW8M

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

-- pin: conj_entry_mem (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:302)
theorem conj_entry_mem (γ : GL (Fin 2) K) (d : R)
    (hd : ∀ i j k l : Fin 2, ∃ n : R, algebraMap R K d
          * (((γ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j
            * ((γ : Matrix (Fin 2) (Fin 2) K) k l)) = algebraMap R K n)
    (b : FiniteAdeleRing R K)
    (hb : ∀ v : HeightOneSpectrum R, ∃ c ∈ v.adicCompletionIntegers K,
        b v = algebraMap K (v.adicCompletion K) (algebraMap R K d) * c)
    (x : FiniteAdeleRing R K) (hx : x = b ∨ x = -b) (i p q j : Fin 2)
    (v : HeightOneSpectrum R) :
    ((1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j
      + x * ((((ratGL R K γ)⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) :
                Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i p
             * ((ratGL R K γ : GL (Fin 2) (FiniteAdeleRing R K)) :
                Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) q j)) v
      ∈ v.adicCompletionIntegers K := by
  rw [coe_add_apply, coe_mul_apply, coe_mul_apply]
  refine add_mem (one_matrix_apply_mem R K i j v) ?_
  rw [ratGL_inv_val_apply, ratGL_val_apply, algebraMap_finiteAdeleRing_apply,
    algebraMap_finiteAdeleRing_apply, ← map_mul]
  obtain ⟨c, hcmem, hc⟩ := hb v
  obtain ⟨n, hn⟩ := hd i p q j
  have hkey : algebraMap K (v.adicCompletion K) (algebraMap R K d)
      * algebraMap K (v.adicCompletion K)
          ((((γ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i p
            * ((γ : Matrix (Fin 2) (Fin 2) K) q j)))
      = algebraMap K (v.adicCompletion K) (algebraMap R K n) := by
    rw [← map_mul, hn]
  have hint : c * algebraMap K (v.adicCompletion K) (algebraMap R K n)
      ∈ v.adicCompletionIntegers K :=
    mul_mem hcmem (algebraMap_mem_adicCompletionIntegers v n)
  have hxv : x v = algebraMap K (v.adicCompletion K) (algebraMap R K d) * c
      ∨ x v = -(algebraMap K (v.adicCompletion K) (algebraMap R K d) * c) := by
    rcases hx with hx | hx
    · exact Or.inl (by rw [hx, hc])
    · exact Or.inr (by rw [hx, coe_neg_apply, hc])
  rcases hxv with hxv | hxv
  · rw [hxv, show algebraMap K (v.adicCompletion K) (algebraMap R K d) * c
        * algebraMap K (v.adicCompletion K)
          ((((γ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i p
            * ((γ : Matrix (Fin 2) (Fin 2) K) q j)))
        = c * (algebraMap K (v.adicCompletion K) (algebraMap R K d)
          * algebraMap K (v.adicCompletion K)
            ((((γ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i p
              * ((γ : Matrix (Fin 2) (Fin 2) K) q j)))) from by ring, hkey]
    exact hint
  · rw [hxv, show -(algebraMap K (v.adicCompletion K) (algebraMap R K d) * c)
        * algebraMap K (v.adicCompletion K)
          ((((γ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i p
            * ((γ : Matrix (Fin 2) (Fin 2) K) q j)))
        = -(c * (algebraMap K (v.adicCompletion K) (algebraMap R K d)
          * algebraMap K (v.adicCompletion K)
            ((((γ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i p
              * ((γ : Matrix (Fin 2) (Fin 2) K) q j))))) from by ring, hkey]
    exact neg_mem hint

-- pin: exists_conj_unipotent_mem (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:357)
theorem exists_conj_unipotent_mem (γ : GL (Fin 2) K) (a : FiniteAdeleRing R K) :
    ∃ q : K,
      (ratGL R K γ)⁻¹ * unipotentGL2 (a - algebraMap K (FiniteAdeleRing R K) q) * ratGL R K γ
        ∈ finiteIntegralGL2 R K := by
  obtain ⟨d, hd0, hd⟩ := exists_common_denominator R K γ
  have hdK : algebraMap R K d ≠ 0 := fun hcontra ↦
    hd0 (IsFractionRing.injective R K (by rw [hcontra, map_zero]))
  obtain ⟨q, hq⟩ := exists_sub_algebraMap_eq_mul_integral R K a (algebraMap R K d) hdK
  refine ⟨q, ?_⟩
  set b : FiniteAdeleRing R K := a - algebraMap K (FiniteAdeleRing R K) q with hb
  have hbv : ∀ v : HeightOneSpectrum R, ∃ c ∈ v.adicCompletionIntegers K,
      b v = algebraMap K (v.adicCompletion K) (algebraMap R K d) * c := by
    intro v
    obtain ⟨c, hcmem, hc⟩ := hq v
    refine ⟨c, hcmem, ?_⟩
    rw [hb, coe_sub_apply, algebraMap_finiteAdeleRing_apply]
    exact hc
  have hAB := ratGL_inv_mul_val R K γ
  have hval : ((((ratGL R K γ)⁻¹ * unipotentGL2 b * ratGL R K γ :
      GL (Fin 2) (FiniteAdeleRing R K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)))
      = (((ratGL R K γ)⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) :
            Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) * !![1, b; 0, 1]
          * ((ratGL R K γ : GL (Fin 2) (FiniteAdeleRing R K)) :
            Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) := by
    rw [Units.val_mul, Units.val_mul, unipotentGL2_coe]
  have hinvval : ((((ratGL R K γ)⁻¹ * unipotentGL2 b * ratGL R K γ)⁻¹ :
      GL (Fin 2) (FiniteAdeleRing R K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K))
      = (((ratGL R K γ)⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) :
            Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) * !![1, -b; 0, 1]
          * ((ratGL R K γ : GL (Fin 2) (FiniteAdeleRing R K)) :
            Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) := by
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, unipotentGL2_inv, ← mul_assoc,
      Units.val_mul, Units.val_mul, unipotentGL2_coe]
  rw [mem_finiteIntegralGL2_iff]
  constructor
  · intro i j v
    rw [hval, conj_unipotent_entry hAB b i j]
    exact conj_entry_mem R K γ d hd b hbv b (Or.inl rfl) i 0 1 j v
  · intro i j v
    rw [hinvval, conj_unipotent_entry hAB (-b) i j]
    exact conj_entry_mem R K γ d hd b hbv (-b) (Or.inr rfl) i 0 1 j v

-- pin: exists_conj_lowerUnip_mem (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:399)
theorem exists_conj_lowerUnip_mem (γ : GL (Fin 2) K) (a : FiniteAdeleRing R K) :
    ∃ q : K,
      (ratGL R K γ)⁻¹ * lowerUnipGL2 (a - algebraMap K (FiniteAdeleRing R K) q) * ratGL R K γ
        ∈ finiteIntegralGL2 R K := by
  obtain ⟨d, hd0, hd⟩ := exists_common_denominator R K γ
  have hdK : algebraMap R K d ≠ 0 := fun hcontra ↦
    hd0 (IsFractionRing.injective R K (by rw [hcontra, map_zero]))
  obtain ⟨q, hq⟩ := exists_sub_algebraMap_eq_mul_integral R K a (algebraMap R K d) hdK
  refine ⟨q, ?_⟩
  set b : FiniteAdeleRing R K := a - algebraMap K (FiniteAdeleRing R K) q with hb
  have hbv : ∀ v : HeightOneSpectrum R, ∃ c ∈ v.adicCompletionIntegers K,
      b v = algebraMap K (v.adicCompletion K) (algebraMap R K d) * c := by
    intro v
    obtain ⟨c, hcmem, hc⟩ := hq v
    refine ⟨c, hcmem, ?_⟩
    rw [hb, coe_sub_apply, algebraMap_finiteAdeleRing_apply]
    exact hc
  have hAB := ratGL_inv_mul_val R K γ
  have hval : ((((ratGL R K γ)⁻¹ * lowerUnipGL2 b * ratGL R K γ :
      GL (Fin 2) (FiniteAdeleRing R K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)))
      = (((ratGL R K γ)⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) :
            Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) * !![1, 0; b, 1]
          * ((ratGL R K γ : GL (Fin 2) (FiniteAdeleRing R K)) :
            Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) := by
    rw [Units.val_mul, Units.val_mul, lowerUnipGL2_coe]
  have hinvval : ((((ratGL R K γ)⁻¹ * lowerUnipGL2 b * ratGL R K γ)⁻¹ :
      GL (Fin 2) (FiniteAdeleRing R K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K))
      = (((ratGL R K γ)⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) :
            Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) * !![1, 0; -b, 1]
          * ((ratGL R K γ : GL (Fin 2) (FiniteAdeleRing R K)) :
            Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) := by
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, lowerUnipGL2_inv, ← mul_assoc,
      Units.val_mul, Units.val_mul, lowerUnipGL2_coe]
  rw [mem_finiteIntegralGL2_iff]
  constructor
  · intro i j v
    rw [hval, conj_lowerUnip_entry hAB b i j]
    exact conj_entry_mem R K γ d hd b hbv b (Or.inl rfl) i 1 0 j v
  · intro i j v
    rw [hinvval, conj_lowerUnip_entry hAB (-b) i j]
    exact conj_entry_mem R K γ d hd b hbv (-b) (Or.inr rfl) i 1 0 j v

-- pin: absorb_unipotent_left (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:441)
theorem absorb_unipotent_left {X : GL (Fin 2) (FiniteAdeleRing R K)} {γ : GL (Fin 2) K}
    (hX : (ratGL R K γ)⁻¹ * X ∈ finiteIntegralGL2 R K) (a : FiniteAdeleRing R K) :
    ∃ q : K, (ratGL R K (unipotentGL2 q * γ))⁻¹ * (unipotentGL2 a * X)
      ∈ finiteIntegralGL2 R K := by
  obtain ⟨q, hq⟩ := exists_conj_unipotent_mem R K γ a
  refine ⟨q, ?_⟩
  have hsplit : unipotentGL2 (a - algebraMap K (FiniteAdeleRing R K) q)
      = (unipotentGL2 (algebraMap K (FiniteAdeleRing R K) q))⁻¹ * unipotentGL2 a := by
    rw [eq_inv_mul_iff_mul_eq, ← unipotentGL2_add]
    congr 1
    ring
  have key : (ratGL R K (unipotentGL2 q * γ))⁻¹ * (unipotentGL2 a * X)
      = ((ratGL R K γ)⁻¹ * unipotentGL2 (a - algebraMap K (FiniteAdeleRing R K) q)
          * ratGL R K γ) * ((ratGL R K γ)⁻¹ * X) := by
    rw [ratGL_mul, show ratGL R K (unipotentGL2 q)
        = unipotentGL2 (algebraMap K (FiniteAdeleRing R K) q) from map_unipotentGL2 _ _, hsplit]
    group
  rw [key]
  exact mul_mem hq hX

-- pin: absorb_lowerUnip_left (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:461)
theorem absorb_lowerUnip_left {X : GL (Fin 2) (FiniteAdeleRing R K)} {γ : GL (Fin 2) K}
    (hX : (ratGL R K γ)⁻¹ * X ∈ finiteIntegralGL2 R K) (a : FiniteAdeleRing R K) :
    ∃ q : K, (ratGL R K (lowerUnipGL2 q * γ))⁻¹ * (lowerUnipGL2 a * X)
      ∈ finiteIntegralGL2 R K := by
  obtain ⟨q, hq⟩ := exists_conj_lowerUnip_mem R K γ a
  refine ⟨q, ?_⟩
  have hsplit : lowerUnipGL2 (a - algebraMap K (FiniteAdeleRing R K) q)
      = (lowerUnipGL2 (algebraMap K (FiniteAdeleRing R K) q))⁻¹ * lowerUnipGL2 a := by
    rw [eq_inv_mul_iff_mul_eq, ← lowerUnipGL2_add]
    congr 1
    ring
  have key : (ratGL R K (lowerUnipGL2 q * γ))⁻¹ * (lowerUnipGL2 a * X)
      = ((ratGL R K γ)⁻¹ * lowerUnipGL2 (a - algebraMap K (FiniteAdeleRing R K) q)
          * ratGL R K γ) * ((ratGL R K γ)⁻¹ * X) := by
    rw [ratGL_mul, show ratGL R K (lowerUnipGL2 q)
        = lowerUnipGL2 (algebraMap K (FiniteAdeleRing R K) q) from map_lowerUnipGL2 _ _, hsplit]
    group
  rw [key]
  exact mul_mem hq hX

-- pin: mul_lowerUnip_apply_one_zero (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:481)
theorem mul_lowerUnip_apply_one_zero (g : GL (Fin 2) (FiniteAdeleRing R K))
    (t : FiniteAdeleRing R K) :
    ((g * lowerUnipGL2 t : GL (Fin 2) (FiniteAdeleRing R K)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) 1 0
      = (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) 1 0
        + (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) 1 1 * t := by
  rw [Units.val_mul, lowerUnipGL2_coe]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

-- pin: det_apply (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:490)
theorem det_apply (M : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) (v : HeightOneSpectrum R) :
    M.det v = M 0 0 v * M 1 1 v - M 0 1 v * M 1 0 v := by
  rw [Matrix.det_fin_two]; rfl

-- pin: exists_lowerUnip_translate_isUnit (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:494)
theorem exists_lowerUnip_translate_isUnit (g : GL (Fin 2) (FiniteAdeleRing R K)) :
    ∃ t : FiniteAdeleRing R K, (∀ v : HeightOneSpectrum R, t v ∈ v.adicCompletionIntegers K) ∧
      IsUnit ((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) 1 0
        + (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) 1 1 * t) := by
  classical
  set M : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K) :=
    (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) with hM
  set N : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K) :=
    ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) with hN

  have hMN : M.det * N.det = 1 := by
    rw [← Matrix.det_mul, hM, hN, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have hdetprod : ∀ v : HeightOneSpectrum R, M.det v * N.det v = 1 := by
    intro v
    rw [← coe_mul_apply, hMN]; rfl
  have hdet_ne : ∀ v : HeightOneSpectrum R, M.det v ≠ 0 := by
    intro v hzero
    have h1 := hdetprod v
    rw [hzero, zero_mul] at h1
    exact zero_ne_one h1

  have hrow : ∀ v : HeightOneSpectrum R, ¬(M 1 0 v = 0 ∧ M 1 1 v = 0) := by
    intro v ⟨h0, h1⟩
    apply hdet_ne v
    rw [det_apply R K M v, h0, h1, mul_zero, mul_zero, sub_zero]

  set tfun : (v : HeightOneSpectrum R) → v.adicCompletion K := fun v ↦
    if Valued.v (M 1 0 v) < Valued.v (M 1 1 v) then 1 else 0 with htfun
  have htfun_eval : ∀ v : HeightOneSpectrum R, tfun v
      = if Valued.v (M 1 0 v) < Valued.v (M 1 1 v) then (1 : v.adicCompletion K) else 0 :=
    fun v ↦ rfl
  have htint : ∀ v, tfun v ∈ v.adicCompletionIntegers K := by
    intro v
    rw [htfun_eval v]
    split
    · exact one_mem _
    · exact zero_mem _
  set t : FiniteAdeleRing R K :=
    ⟨tfun, Filter.Eventually.of_forall fun v ↦ htint v⟩ with ht
  have htv : ∀ v, t v = tfun v := fun v ↦ rfl
  refine ⟨t, fun v ↦ by rw [htv v]; exact htint v, ?_⟩

  set c : FiniteAdeleRing R K := M 1 0 + M 1 1 * t with hc
  have hcv : ∀ v, c v = M 1 0 v + M 1 1 v * tfun v := fun v ↦ rfl

  have hcne : ∀ v, c v ≠ 0 := by
    intro v
    rw [hcv v, htfun_eval v]
    split
    · rename_i hlt
      intro hzero
      have hne : Valued.v (M 1 0 v) ≠ Valued.v (M 1 1 v) := ne_of_lt hlt
      have hval : Valued.v (M 1 0 v + M 1 1 v) =
          max (Valued.v (M 1 0 v)) (Valued.v (M 1 1 v)) :=
        Valuation.map_add_of_distinct_val _ hne
      rw [mul_one] at hzero
      rw [hzero, Valuation.map_zero, max_eq_right (le_of_lt hlt)] at hval
      have hd0 : M 1 1 v = 0 := by
        have := hval.symm
        rwa [Valuation.zero_iff] at this
      have hc0 : M 1 0 v = 0 := by
        have := hzero
        rwa [hd0, add_zero] at this
      exact hrow v ⟨hc0, hd0⟩
    · rename_i hge
      rw [mul_zero, add_zero]
      intro hzero
      have hc0 : Valued.v (M 1 0 v) = 0 := by rw [hzero, Valuation.map_zero]
      have hd0 : Valued.v (M 1 1 v) = 0 := by
        have hle : Valued.v (M 1 1 v) ≤ Valued.v (M 1 0 v) := not_lt.mp hge
        rw [hc0] at hle
        exact le_zero_iff.mp hle
      rw [Valuation.zero_iff] at hd0
      exact hrow v ⟨hzero, hd0⟩

  have hcunit : ∀ᶠ v in Filter.cofinite, Valued.v (c v) = 1 := by
    have h00 : ∀ᶠ v in Filter.cofinite, M 0 0 v ∈ v.adicCompletionIntegers K := (M 0 0).2
    have h01 : ∀ᶠ v in Filter.cofinite, M 0 1 v ∈ v.adicCompletionIntegers K := (M 0 1).2
    have h10 : ∀ᶠ v in Filter.cofinite, M 1 0 v ∈ v.adicCompletionIntegers K := (M 1 0).2
    have h11 : ∀ᶠ v in Filter.cofinite, M 1 1 v ∈ v.adicCompletionIntegers K := (M 1 1).2
    have k00 : ∀ᶠ v in Filter.cofinite, N 0 0 v ∈ v.adicCompletionIntegers K := (N 0 0).2
    have k01 : ∀ᶠ v in Filter.cofinite, N 0 1 v ∈ v.adicCompletionIntegers K := (N 0 1).2
    have k10 : ∀ᶠ v in Filter.cofinite, N 1 0 v ∈ v.adicCompletionIntegers K := (N 1 0).2
    have k11 : ∀ᶠ v in Filter.cofinite, N 1 1 v ∈ v.adicCompletionIntegers K := (N 1 1).2
    filter_upwards [h00, h01, h10, h11, k00, k01, k10, k11] with v
      h00 h01 h10 h11 k00 k01 k10 k11
    have hMdetint : M.det v ∈ v.adicCompletionIntegers K := by
      rw [det_apply R K M v]
      exact sub_mem (mul_mem h00 h11) (mul_mem h01 h10)
    have hNdetint : N.det v ∈ v.adicCompletionIntegers K := by
      rw [det_apply R K N v]
      exact sub_mem (mul_mem k00 k11) (mul_mem k01 k10)
    have hdetone : Valued.v (M.det v) = 1 := by
      have hprodval : Valued.v (M.det v) * Valued.v (N.det v) = 1 := by
        rw [← Valuation.map_mul, hdetprod v, Valuation.map_one]
      have hMle : Valued.v (M.det v) ≤ 1 := by
        rwa [← mem_adicCompletionIntegers]
      have hNle : Valued.v (N.det v) ≤ 1 := by
        rwa [← mem_adicCompletionIntegers]
      have hge : (1 : WithZero (Multiplicative ℤ)) ≤ Valued.v (M.det v) := by
        calc (1 : WithZero (Multiplicative ℤ))
            = Valued.v (M.det v) * Valued.v (N.det v) := hprodval.symm
          _ ≤ Valued.v (M.det v) * 1 := mul_le_mul' le_rfl hNle
          _ = Valued.v (M.det v) := mul_one _
      exact le_antisymm hMle hge

    have hmax : (1 : WithZero (Multiplicative ℤ))
        ≤ max (Valued.v (M 1 0 v)) (Valued.v (M 1 1 v)) := by
      have hsub : Valued.v (M.det v)
          ≤ max (Valued.v (M 0 0 v * M 1 1 v)) (Valued.v (M 0 1 v * M 1 0 v)) := by
        rw [det_apply R K M v]
        exact Valuation.map_sub _ _ _
      have h1 : Valued.v (M 0 0 v * M 1 1 v) ≤ Valued.v (M 1 1 v) := by
        rw [Valuation.map_mul]
        calc Valued.v (M 0 0 v) * Valued.v (M 1 1 v) ≤ 1 * Valued.v (M 1 1 v) :=
              mul_le_mul' (by rwa [← mem_adicCompletionIntegers]) le_rfl
          _ = Valued.v (M 1 1 v) := one_mul _
      have h2 : Valued.v (M 0 1 v * M 1 0 v) ≤ Valued.v (M 1 0 v) := by
        rw [Valuation.map_mul]
        calc Valued.v (M 0 1 v) * Valued.v (M 1 0 v) ≤ 1 * Valued.v (M 1 0 v) :=
              mul_le_mul' (by rwa [← mem_adicCompletionIntegers]) le_rfl
          _ = Valued.v (M 1 0 v) := one_mul _
      calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (M.det v) := hdetone.symm
        _ ≤ max (Valued.v (M 0 0 v * M 1 1 v)) (Valued.v (M 0 1 v * M 1 0 v)) := hsub
        _ ≤ max (Valued.v (M 1 1 v)) (Valued.v (M 1 0 v)) := max_le_max h1 h2
        _ = max (Valued.v (M 1 0 v)) (Valued.v (M 1 1 v)) := max_comm _ _
    rw [hcv v, htfun_eval v]
    split
    · rename_i hlt
      rw [mul_one]
      have hne : Valued.v (M 1 0 v) ≠ Valued.v (M 1 1 v) := ne_of_lt hlt
      rw [Valuation.map_add_of_distinct_val _ hne]
      have hmaxeq : max (Valued.v (M 1 0 v)) (Valued.v (M 1 1 v)) = Valued.v (M 1 1 v) :=
        max_eq_right (le_of_lt hlt)
      rw [hmaxeq]
      refine le_antisymm (by rwa [← mem_adicCompletionIntegers]) ?_
      rw [hmaxeq] at hmax
      exact hmax
    · rename_i hge
      rw [mul_zero, add_zero]
      have hmaxeq : max (Valued.v (M 1 0 v)) (Valued.v (M 1 1 v)) = Valued.v (M 1 0 v) :=
        max_eq_left (not_lt.mp hge)
      refine le_antisymm (by rwa [← mem_adicCompletionIntegers]) ?_
      rw [hmaxeq] at hmax
      exact hmax

  set cinvfun : (v : HeightOneSpectrum R) → v.adicCompletion K := fun v ↦ (c v)⁻¹
    with hcinvfun
  have hcinv_ev : ∀ᶠ v in Filter.cofinite,
      cinvfun v ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    filter_upwards [hcunit] with v hv
    show (c v)⁻¹ ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K))
    rw [SetLike.mem_coe, mem_adicCompletionIntegers, Valuation.map_inv, hv]
    exact le_of_eq inv_one
  set cinv : FiniteAdeleRing R K := ⟨cinvfun, hcinv_ev⟩ with hcinv
  have hcinvv : ∀ v, cinv v = (c v)⁻¹ := fun v ↦ rfl
  have hmul : c * cinv = 1 := by
    have hkey : ∀ w : HeightOneSpectrum R, (c * cinv) w = (1 : FiniteAdeleRing R K) w := by
      intro w
      rw [coe_mul_apply, hcinvv w, mul_inv_cancel₀ (hcne w), coe_one_apply]
    exact Subtype.ext (funext fun w ↦ hkey w)
  exact ⟨⟨c, cinv, hmul, by rw [mul_comm]; exact hmul⟩, rfl⟩

end GL2StrongApproxW8M

end AdelicLevel

end NumberField
