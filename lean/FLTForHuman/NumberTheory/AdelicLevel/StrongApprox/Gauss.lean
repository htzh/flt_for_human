/-
  The determinant unit and the Gauss (LU) decomposition over the finite adèles.

  `detUnit` is the determinant of `g ∈ GL₂(𝔸_K^fin)` as a unit of the finite idèles
  (its inverse is the determinant of `g⁻¹`); it is the diagonal entry of the Gauss
  decomposition. `exists_gauss_decomposition` is that decomposition: after the
  translation `t` of `exists_lowerUnip_translate_isUnit` — which makes the translated
  lower-left entry `g 1 0 + g 1 1 * t` a unit `cu` — the matrix `g` factors as

      g = unipotentGL2 x * (lowerUnipGL2 cu * (unipotentGL2 z * (diagTorusGL2 (detUnit g) * lowerUnipGL2 (-t))))

  with the integrality of `t` recorded and the diagonal unit the determinant itself.
  This is the "every element of `GL₂` over a local ring is `L * U * D` with the
  lower-left entry a unit" statement, moved to the adèle ring place by place.

  Transcribed verbatim from
  `P2M/Sol/S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:658–719`
  (the pin's `Gauss` block, pinned `aa2d8b3`). It assumes the whole conjugation
  module: `exists_lowerUnip_translate_isUnit` for `t`, `gauss_factorization` for the
  matrix identity, and `lowerUnipGL2`/`unipotentGL2`/`diagTorusGL2` for the factors.
-/
import FLTForHuman.NumberTheory.AdelicLevel.StrongApprox.Conjugation

set_option autoImplicit false

open Matrix IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField AutomorphicForm

noncomputable section

namespace NumberField

namespace AdelicLevel

namespace GL2StrongApproxW8M

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

-- pin: detUnit (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:658)
def detUnit (g : GL (Fin 2) (FiniteAdeleRing R K)) : (FiniteAdeleRing R K)ˣ where
  val := ((g : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)).det
  inv := ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) :
    Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)).det
  val_inv := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  inv_val := by
    rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]

-- pin: detUnit_coe (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:667)
@[scoped simp] theorem detUnit_coe (g : GL (Fin 2) (FiniteAdeleRing R K)) :
    (detUnit R K g : FiniteAdeleRing R K)
      = ((g : GL (Fin 2) (FiniteAdeleRing R K)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)).det := rfl

-- pin: exists_gauss_decomposition (S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:672)
theorem exists_gauss_decomposition (g : GL (Fin 2) (FiniteAdeleRing R K)) :
    ∃ (t : FiniteAdeleRing R K) (x z : FiniteAdeleRing R K) (cu : (FiniteAdeleRing R K)ˣ),
      (∀ v : HeightOneSpectrum R, t v ∈ v.adicCompletionIntegers K) ∧
      g = unipotentGL2 x * (lowerUnipGL2 (cu : FiniteAdeleRing R K)
        * (unipotentGL2 z * (diagTorusGL2 (detUnit R K g) * lowerUnipGL2 (-t)))) := by
  obtain ⟨t, htint, hunit⟩ := exists_lowerUnip_translate_isUnit R K g
  set h : GL (Fin 2) (FiniteAdeleRing R K) := g * lowerUnipGL2 t with hh
  set M : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K) :=
    (h : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) with hM
  have hM10 : M 1 0 = (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) 1 0
      + (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) 1 1 * t := by
    rw [hM, hh, mul_lowerUnip_apply_one_zero]
  set cu : (FiniteAdeleRing R K)ˣ := hunit.unit with hcu
  have hcuval : (cu : FiniteAdeleRing R K)
      = (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) 1 0
        + (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) 1 1 * t := hunit.unit_spec
  have hc : M 1 0 = (cu : FiniteAdeleRing R K) := by rw [hM10, hcuval]
  have hdet : M.det = (detUnit R K g : FiniteAdeleRing R K) := by
    rw [hM, hh, Units.val_mul, Matrix.det_mul, lowerUnipGL2_coe, Matrix.det_fin_two_of]
    rw [detUnit_coe]
    ring
  have hfact := gauss_factorization M (cu : FiniteAdeleRing R K)
    ((cu⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K)
    (detUnit R K g : FiniteAdeleRing R K)
    (((detUnit R K g)⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K)
    hc cu.mul_inv hdet (detUnit R K g).mul_inv
  set x : FiniteAdeleRing R K :=
    (M 0 0 - 1) * ((cu⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) with hx
  set z : FiniteAdeleRing R K :=
    (M 1 1 * (((detUnit R K g)⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) - 1)
      * ((cu⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) with hz
  have hgroup : unipotentGL2 x * lowerUnipGL2 (cu : FiniteAdeleRing R K)
      * unipotentGL2 z * diagTorusGL2 (detUnit R K g) = h := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, unipotentGL2_coe, lowerUnipGL2_coe,
      unipotentGL2_coe, diagTorusGL2_coe]
    rw [hx, hz]
    exact hfact
  refine ⟨t, x, z, cu, htint, ?_⟩
  have hgh : g = h * (lowerUnipGL2 t)⁻¹ := by
    rw [hh, mul_assoc, mul_inv_cancel, mul_one]
  have hassoc : unipotentGL2 x * (lowerUnipGL2 (cu : FiniteAdeleRing R K)
      * (unipotentGL2 z * (diagTorusGL2 (detUnit R K g) * lowerUnipGL2 (-t))))
      = h * (lowerUnipGL2 t)⁻¹ := by
    rw [← hgroup, lowerUnipGL2_inv]
    group
  rw [hassoc]
  exact hgh

end GL2StrongApproxW8M

end AdelicLevel

end NumberField
