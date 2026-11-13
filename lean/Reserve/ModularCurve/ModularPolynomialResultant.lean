/-
  The resultant divisibility at a composite level, shelved out of the live theory.

  `ModularPolynomialData.dvd_resultant_of_mul` — the datum at `ℓ * M` divides the
  resultant of the data at `ℓ` and at `M` — has no live consumer in the port. Its proof
  is substantial independent mathematics (the resultant identity read over the algebraic
  closure), so it is kept here rather than deleted. The live module no longer carries it;
  the pins below record that the content is ported.

  spec-pin: Theorems/Thm_ModularCurve_ModularPolynomialData_dvd_resultant_of_mul.lean
  spec-pin: P2M/Sol/S_ModularCurve_ModularPolynomialData_dvd_resultant_of_mul.lean
-/
import FLTForHuman.ModularCurve.ModularPolynomialUniquenessIrreducible

set_option autoImplicit false

noncomputable section

open Polynomial IntermediateField

namespace ModularCurve.ModularPolynomialData

theorem dvd_resultant_of_mul
    (ℓ M : ℕ) [NeZero ℓ] [NeZero M]
    (dℓ : ModularPolynomialData ℓ) (dM : ModularPolynomialData M)
    (dN : ModularPolynomialData (ℓ * M)) :
    dN.Φ ∣ (dℓ.Φ.map (Polynomial.C : Polynomial ℤ →+* Polynomial (Polynomial ℤ))).resultant
      (dM.Φ.eval₂ (Polynomial.mapRingHom (Int.castRingHom (Polynomial (Polynomial ℤ))))
        (Polynomial.C Polynomial.X)) := by

  set B := Polynomial (Polynomial ℤ)
  set f : Polynomial B := dℓ.Φ.map (Polynomial.C : Polynomial ℤ →+* B) with hf
  set g : Polynomial B := dM.Φ.eval₂ (Polynomial.mapRingHom (Int.castRingHom B))
    (Polynomial.C Polynomial.X) with hg
  set R : B := f.resultant g with hR
  set L := LaurentSeries ℚ

  set Ξ : B →+* L := Polynomial.eval₂RingHom evalAtJ (jqN (ℓ * M)) with hΞ
  have hΞC : Ξ.comp Polynomial.C = evalAtJ := RingHom.ext fun a => by
    rw [RingHom.comp_apply, hΞ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
  have hΞX : Ξ Polynomial.X = jqN (ℓ * M) := by
    rw [hΞ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

  set f' : Polynomial L := dℓ.Φ.map evalAtJ with hf'
  set g' : Polynomial L := dM.Φ.eval₂ (Polynomial.mapRingHom (Int.castRingHom L))
    (Polynomial.C (jqN (ℓ * M))) with hg'
  have hff' : f.map Ξ = f' := by
    rw [hf, Polynomial.map_map, hΞC]
  have hgg' : g.map Ξ = g' := by
    rw [hg, ← Polynomial.coe_mapRingHom, Polynomial.hom_eval₂, hg']
    congr 1
    · refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
      simp
    · rw [Polynomial.coe_mapRingHom, Polynomial.map_C, hΞX]

  have hf'm : f'.Monic := dℓ.monic.map _
  have hdegf : f'.natDegree = f.natDegree := by
    rw [hf', hf, dℓ.monic.natDegree_map, dℓ.monic.natDegree_map]

  set z₀ : L := jqN ℓ with hz₀
  have hfz : f'.eval z₀ = 0 := by
    rw [hf', Polynomial.eval_map]
    exact dℓ.eval_eq_zero
  have hgz : g'.eval z₀ = 0 := by
    rw [hg', ← Polynomial.coe_evalRingHom, Polynomial.hom_eval₂, Polynomial.coe_evalRingHom,
      Polynomial.eval_C]
    have h1 : (Polynomial.evalRingHom z₀).comp (Polynomial.mapRingHom (Int.castRingHom L)) =
        Polynomial.eval₂RingHom (Int.castRingHom L) z₀ := by
      refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
      simp
    rw [h1, ← qExpand_comp_evalAtJ ℓ]
    have h2 : jqN (ℓ * M) = qExpand ℚ ℓ (jqN M) := by
      rw [jqN, jqN, qExpand_qExpand]
    rw [h2, ← Polynomial.hom_eval₂, dM.eval_eq_zero, map_zero]

  have hRes : f'.resultant g' f.natDegree g.natDegree = 0 := by
    set Lb := AlgebraicClosure L
    apply (algebraMap L Lb).injective
    rw [map_zero, ← Polynomial.resultant_map_map]
    have hsplit : (f'.map (algebraMap L Lb)).Splits := IsAlgClosed.splits _
    have hdeg1 : (f'.map (algebraMap L Lb)).natDegree = f.natDegree := by
      rw [Polynomial.natDegree_map, hdegf]
    have hdeg2 : (g'.map (algebraMap L Lb)).natDegree ≤ g.natDegree := by
      rw [Polynomial.natDegree_map, ← hgg']
      exact Polynomial.natDegree_map_le
    rw [← hdeg1, Polynomial.resultant_eq_prod_eval _ _ _ hdeg2 hsplit]
    have hz : algebraMap L Lb z₀ ∈ (f'.map (algebraMap L Lb)).roots := by
      rw [Polynomial.mem_roots (Polynomial.map_ne_zero hf'm.ne_zero), Polynomial.IsRoot.def,
        Polynomial.eval_map, Polynomial.eval₂_hom, hfz, map_zero]
    have hz' : Polynomial.eval (algebraMap L Lb z₀) (g'.map (algebraMap L Lb)) = 0 := by
      rw [Polynomial.eval_map, Polynomial.eval₂_hom, hgz, map_zero]
    rw [Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨_, hz, hz'⟩), mul_zero]
  have hΞR : Ξ R = 0 := by
    rw [hR, ← Polynomial.resultant_map_map, hff', hgg']
    exact hRes

  set θ : B →+* Polynomial ℚ⟮jq⟯ := Polynomial.mapRingHom evalAtJGen with hθ
  have hθinj : Function.Injective θ := Polynomial.map_injective _ evalAtJGen_injective
  have haeval : Polynomial.aeval (jqN (ℓ * M)) (θ R) = 0 := by
    rw [hθ, Polynomial.coe_mapRingHom, Polynomial.aeval_def, Polynomial.eval₂_map,
      algebraMap_comp_evalAtJGen]
    exact hΞR
  have hmin : minpoly ℚ⟮jq⟯ (jqN (ℓ * M)) = θ dN.Φ := by
    rw [← toAdjoin_eq_minpoly_all (ℓ * M) dN]
    rfl
  have hdvd : θ dN.Φ ∣ θ R := by
    rw [← hmin]
    exact minpoly.dvd _ _ haeval

  rw [← Polynomial.modByMonic_eq_zero_iff_dvd dN.monic]
  apply hθinj
  rw [map_zero, hθ, Polynomial.coe_mapRingHom, Polynomial.map_modByMonic _ dN.monic,
    Polynomial.modByMonic_eq_zero_iff_dvd (dN.monic.map _)]
  exact hdvd

end ModularCurve.ModularPolynomialData
