/-
  m6 — the Φ datum family: the squarefree existence, the `jqNModC`
  evaluation/integrality tail, and the prime generation facts.

  Five of the M5 nodes are one-liners over the ported Φ_p effort
  (`exists_phiIrreducible_evalSymm` in `ModularPolynomialProperties.lean`, the
  `gen_prime`/`functionFieldGeneration_iff_full_eq` pair, and the
  `toAdjoin`/`aeval_jqN_toAdjoin` API); two more are ~30-line transcriptions over
  the ported `coeffMap_qExpand`/`coeffMap_injective`; `nonempty_modularPolynomialData_of_squarefree`
  is the one real proof (the biresultant). The degree tail lives in
  `Degree/PhiDegree.lean`.

  FLT provenance, pinned `aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_nonempty_modularPolynomialData_of_squarefree.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_isIntegral_jqNModC_all_of_modularPolynomialFamily.lean
-/
import FLTForHuman.ModularCurve.Defs.JqCoeff
import FLTForHuman.ModularCurve.Defs.PhiGen
import FLTForHuman.ModularCurve.ModularPolynomialProperties
import FLTForHuman.ModularCurve.ModularPolynomialIrreducible
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Collapse
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

set_option autoImplicit false

noncomputable section

open Polynomial IntermediateField Finset Nat

namespace ModularCurve

/-! ## The one-liners over the ported Φ_p effort -/

theorem exists_modularPolynomialData_evalSymm (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] :
    ∃ data : ModularPolynomialData ℓ, EvalSymm data.Φ := by
  obtain ⟨data, _, hsymm⟩ := exists_phiIrreducible_evalSymm ℓ
  exact ⟨data, hsymm⟩

theorem modularPolynomialFamily : ModularPolynomialFamily := fun ℓ _ hℓ => by
  have : Fact (Nat.Prime ℓ) := ⟨hℓ⟩
  exact exists_modularPolynomialData_evalSymm ℓ

theorem functionFieldGeneration_of_prime {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) :
    FunctionFieldGeneration ℓ := by
  have : Fact (Nat.Prime ℓ) := ⟨hℓ⟩
  exact (functionFieldGeneration_iff_full_eq ℓ).mpr (gen_prime ℓ).symm

theorem full_eq_of_prime {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) :
    modularFunctionFieldFull ℓ = modularFunctionField ℓ :=
  (functionFieldGeneration_iff_full_eq ℓ).mp (functionFieldGeneration_of_prime hℓ)

namespace ModularPolynomialData

theorem isIntegral_jqN {N : ℕ} [NeZero N] (data : ModularPolynomialData N) :
    IsIntegral ℚ⟮jq⟯ (jqN N) :=
  ⟨data.toAdjoin, data.toAdjoin_monic, aeval_jqN_toAdjoin data⟩

end ModularPolynomialData

/-! ## The `jqNModC` evaluation tail -/

section EvalJqNModC

private theorem coeffMap_jqNModC {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ)
    [NeZero n] : coeffMap f (jqNModC R n) = jqNModC S n := by
  unfold jqNModC
  rw [coeffMap_qExpand]
  exact congrArg (qExpand S n) (map_jqModC f)

private theorem coeffMap_eval₂_jqNModC {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (Φ : Polynomial (Polynomial ℤ)) (d e : ℕ) [NeZero d] [NeZero e] :
    coeffMap f (Φ.eval₂ (aeval (R := ℤ) (jqNModC R d)).toRingHom (jqNModC R e))
      = Φ.eval₂ (aeval (R := ℤ) (jqNModC S d)).toRingHom (jqNModC S e) := by
  rw [Polynomial.hom_eval₂, coeffMap_jqNModC]
  congr 1
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp [coeffMap_jqNModC]

private theorem eval₂_rat_of_data {ℓ : ℕ} [NeZero ℓ] (data : ModularPolynomialData ℓ) (d : ℕ)
    [NeZero d] : data.Φ.eval₂ (aeval (R := ℤ) (jqNModC ℚ d)).toRingHom (jqNModC ℚ (d * ℓ)) = 0 := by
  have hcomp : (qExpand ℚ d).comp evalAtJ = (aeval (R := ℤ) (jqNModC ℚ d)).toRingHom := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp [evalAtJ]
    rfl
  have := congrArg (qExpand ℚ d) data.eval_eq_zero
  rw [map_zero, Polynomial.hom_eval₂, hcomp, jqN, qExpand_qExpand] at this
  exact this

namespace ModularPolynomialData

theorem eval_jqNModC_mul_eq_zero {ℓ : ℕ} [NeZero ℓ] (data : ModularPolynomialData ℓ) (K : Type*)
    [CommRing K] (d : ℕ) [NeZero d] :
    data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqNModC K d)).toRingHom (jqNModC K (d * ℓ)) = 0 := by
  have hZ : data.Φ.eval₂ (aeval (R := ℤ) (jqNModC ℤ d)).toRingHom (jqNModC ℤ (d * ℓ)) = 0 := by
    apply coeffMap_injective (f := Int.castRingHom ℚ) Int.cast_injective
    rw [coeffMap_eval₂_jqNModC, map_zero]
    exact eval₂_rat_of_data data d
  have := congrArg (coeffMap (Int.castRingHom K)) hZ
  rwa [coeffMap_eval₂_jqNModC, map_zero] at this

theorem eval_jqNModC_of_mul_eq_zero {ℓ : ℕ} [NeZero ℓ] (data : ModularPolynomialData ℓ)
    (hsymm : EvalSymm data.Φ) (K : Type*) [CommRing K] (d : ℕ) [NeZero d] :
    data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqNModC K (d * ℓ))).toRingHom (jqNModC K d) = 0 := by
  have hQ : data.Φ.eval₂ (aeval (R := ℤ) (jqNModC ℚ (d * ℓ))).toRingHom (jqNModC ℚ d) = 0 := by
    rw [hsymm]
    exact eval₂_rat_of_data data d
  have hZ : data.Φ.eval₂ (aeval (R := ℤ) (jqNModC ℤ (d * ℓ))).toRingHom (jqNModC ℤ d) = 0 := by
    apply coeffMap_injective (f := Int.castRingHom ℚ) Int.cast_injective
    rw [coeffMap_eval₂_jqNModC, map_zero]
    exact hQ
  have := congrArg (coeffMap (Int.castRingHom K)) hZ
  rwa [coeffMap_eval₂_jqNModC, map_zero] at this

end ModularPolynomialData

end EvalJqNModC

/-! ## The integrality tail -/

section Integrality

private theorem isIntegral_of_eval₂_eq_zero {L : Type*} [Field L]
    (F : IntermediateField L (LaurentSeries L)) {Φ : Polynomial (Polynomial ℤ)} (hΦ : Φ.Monic)
    {a b : LaurentSeries L} (ha : a ∈ F)
    (h : Φ.eval₂ (aeval (R := ℤ) a).toRingHom b = 0) : IsIntegral F b := by
  set ev : Polynomial ℤ →+* F := (aeval (R := ℤ) (⟨a, ha⟩ : F)).toRingHom with hev
  have hcomp : (algebraMap F (LaurentSeries L)).comp ev = (aeval (R := ℤ) a).toRingHom := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp [hev]
  refine ⟨Φ.map ev, hΦ.map ev, ?_⟩
  rw [Polynomial.eval₂_map, hcomp]
  exact h

theorem isIntegral_jqNModC_mul {K : Type*} [Field K] (F : IntermediateField K (LaurentSeries K))
    {ℓ : ℕ} [NeZero ℓ] (data : ModularPolynomialData ℓ) (d : ℕ) [NeZero d]
    (hd : jqNModC K d ∈ F) : IsIntegral F (jqNModC K (d * ℓ)) :=
  isIntegral_of_eval₂_eq_zero F data.monic hd (data.eval_jqNModC_mul_eq_zero K d)

end Integrality

section AllLevels

variable (K : Type*) [Field K]

local notation "L" => LaurentSeries K

local notation "F₀" => IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))

private theorem step {ℓ : ℕ} [NeZero ℓ] (data : ModularPolynomialData ℓ) (d : ℕ) [NeZero d]
    (hd : IsIntegral F₀ (jqNModC K d)) : IsIntegral F₀ (jqNModC K (d * ℓ)) := by
  set E : IntermediateField F₀ L := IntermediateField.adjoin F₀ ({jqNModC K d} : Set L) with hE
  have : FiniteDimensional F₀ E := IntermediateField.adjoin.finiteDimensional hd
  have hmem : jqNModC K d ∈ E.restrictScalars K := by
    rw [IntermediateField.mem_restrictScalars]
    exact IntermediateField.mem_adjoin_simple_self _ _
  have h1 : IsIntegral (E.restrictScalars K) (jqNModC K (d * ℓ)) := isIntegral_jqNModC_mul _ data d hmem
  have h2 : IsIntegral E (jqNModC K (d * ℓ)) := h1
  have : Algebra.IsIntegral F₀ E := Algebra.IsIntegral.of_finite F₀ E
  exact isIntegral_trans _ h2

private theorem base : IsIntegral F₀ (jqModC K) :=
  isIntegral_algebraMap (x := (⟨jqModC K, mem_adjoin_simple_self K (jqModC K)⟩ : F₀))

private theorem jqNModC_congr {M N : ℕ} [NeZero M] [NeZero N] (h : M = N) :
    jqNModC K M = jqNModC K N := by
  subst h; rfl

private theorem isIntegral_jqNModC_all (hΦ : ModularPolynomialFamily) :
    ∀ (N : ℕ) [NeZero N], IsIntegral F₀ (jqNModC K N) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hN
    rcases le_or_gt N 1 with hle | hlt
    · obtain rfl : N = 1 := le_antisymm hle (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
      rw [show jqNModC K 1 = jqModC K from qExpand_one_apply _]
      exact base K
    · have hp : N.minFac.Prime := Nat.minFac_prime (by omega)
      obtain ⟨d, hd⟩ := Nat.minFac_dvd N
      have hd0 : d ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hd
        exact absurd hd (by omega)
      have : NeZero d := ⟨hd0⟩
      have : NeZero N.minFac := ⟨hp.ne_zero⟩
      have hN' : N = d * N.minFac := hd.trans (mul_comm _ _)
      have hdlt : d < N := by
        have h2 : 2 ≤ N.minFac := hp.two_le
        have : d * 2 ≤ d * N.minFac := Nat.mul_le_mul_left d h2
        omega
      obtain ⟨data, -⟩ := hΦ N.minFac hp
      have hstepd : IsIntegral F₀ (jqNModC K (d * N.minFac)) := step K data d (ih d hdlt)
      rwa [jqNModC_congr K hN']

theorem isIntegral_jqNModC_all_of_modularPolynomialFamily (K : Type*) [Field K]
    (hΦ : ModularPolynomialFamily) (N : ℕ) [NeZero N] :
    IsIntegral (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (jqNModC K N) :=
  isIntegral_jqNModC_all K hΦ N

end AllLevels

/-! ## The squarefree existence (the biresultant) -/


section FibrePoly

variable {K : Type*} [Field K]

private def fibrePoly (Φ : Polynomial (Polynomial ℤ)) (a : K) : Polynomial K :=
  Φ.map (Polynomial.eval₂RingHom (Int.castRingHom K) a)

private theorem monic_fibrePoly {Φ : Polynomial (Polynomial ℤ)} (hΦ : Φ.Monic) (a : K) :
    (fibrePoly Φ a).Monic :=
  hΦ.map _

private theorem natDegree_fibrePoly {Φ : Polynomial (Polynomial ℤ)} (hΦ : Φ.Monic) (a : K) :
    (fibrePoly Φ a).natDegree = Φ.natDegree :=
  hΦ.natDegree_map _

private theorem card_roots_fibrePoly_of_monic [IsAlgClosed K]
    {Φ : Polynomial (Polynomial ℤ)} (hΦ : Φ.Monic) (a : K) :
    Multiset.card (fibrePoly Φ a).roots = Φ.natDegree := by
  rw [← (IsAlgClosed.splits (fibrePoly Φ a)).natDegree_eq_card_roots]
  exact natDegree_fibrePoly hΦ a

private def compositeFibrePoly (Φ Φ' : Polynomial (Polynomial ℤ)) (a : K) : Polynomial K :=
  ((fibrePoly Φ a).roots.map fun b => fibrePoly Φ' b).prod

private theorem compositeFibrePoly_def (Φ Φ' : Polynomial (Polynomial ℤ)) (a : K) :
    compositeFibrePoly Φ Φ' a
      = ((fibrePoly Φ a).roots.map fun b => fibrePoly Φ' b).prod :=
  rfl

private theorem monic_compositeFibrePoly {Φ Φ' : Polynomial (Polynomial ℤ)} (hΦ' : Φ'.Monic)
    (a : K) : (compositeFibrePoly Φ Φ' a).Monic :=
  monic_multiset_prod_of_monic _ _ fun _ _ => monic_fibrePoly hΦ' _

end FibrePoly

section Lifts

private def resLiftInner (Φ : Polynomial (Polynomial ℤ)) :
    Polynomial (Polynomial (Polynomial ℤ)) :=
  Φ.map (Polynomial.C : Polynomial ℤ →+* Polynomial (Polynomial ℤ))

private def resLiftOuter (Φ' : Polynomial (Polynomial ℤ)) :
    Polynomial (Polynomial (Polynomial ℤ)) :=
  Φ'.eval₂ (Polynomial.mapRingHom (Int.castRingHom (Polynomial (Polynomial ℤ))))
    (Polynomial.C (Polynomial.X : Polynomial (Polynomial ℤ)))

private def resLiftOuterK (K : Type*) [Field K] (Φ' : Polynomial (Polynomial ℤ)) :
    Polynomial (Polynomial K) :=
  Φ'.eval₂ (Polynomial.mapRingHom (Int.castRingHom (Polynomial K)))
    (Polynomial.C (Polynomial.X : Polynomial K))

end Lifts

section Specialize

variable {K : Type*} [Field K]

private def specializeAt (a : K) :
    Polynomial (Polynomial ℤ) →+* Polynomial K :=
  Polynomial.mapRingHom (Polynomial.eval₂RingHom (Int.castRingHom K) a)

private theorem specializeAt_eq_fibrePoly (a : K) (Ψ : Polynomial (Polynomial ℤ)) :
    specializeAt a Ψ = fibrePoly Ψ a :=
  rfl

private theorem map_resLiftInner (Φ : Polynomial (Polynomial ℤ)) (a : K) :
    (resLiftInner Φ).map (specializeAt a)
      = (fibrePoly Φ a).map (Polynomial.C : K →+* Polynomial K) := by
  have h : (specializeAt (K := K) a).comp
        (Polynomial.C : Polynomial ℤ →+* Polynomial (Polynomial ℤ))
      = (Polynomial.C : K →+* Polynomial K).comp
          (Polynomial.eval₂RingHom (Int.castRingHom K) a) := by
    refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
    simp [specializeAt]
  rw [resLiftInner, Polynomial.map_map, h, ← Polynomial.map_map]
  rfl

private theorem map_resLiftOuter (Φ' : Polynomial (Polynomial ℤ)) (a : K) :
    (resLiftOuter Φ').map (specializeAt a) = resLiftOuterK K Φ' := by
  have hF : (Polynomial.mapRingHom (specializeAt (K := K) a)).comp
        (Polynomial.mapRingHom (Int.castRingHom (Polynomial (Polynomial ℤ))))
      = Polynomial.mapRingHom (Int.castRingHom (Polynomial K)) := by
    refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
    simp [specializeAt]
  have hX : (Polynomial.mapRingHom (specializeAt (K := K) a))
        (Polynomial.C (Polynomial.X : Polynomial (Polynomial ℤ)))
      = Polynomial.C (Polynomial.X : Polynomial K) := by
    simp [specializeAt]
  calc (resLiftOuter Φ').map (specializeAt a)
      = (Polynomial.mapRingHom (specializeAt a))
          (Φ'.eval₂ (Polynomial.mapRingHom
            (Int.castRingHom (Polynomial (Polynomial ℤ))))
            (Polynomial.C (Polynomial.X : Polynomial (Polynomial ℤ)))) := rfl
    _ = Φ'.eval₂ ((Polynomial.mapRingHom (specializeAt a)).comp
          (Polynomial.mapRingHom (Int.castRingHom (Polynomial (Polynomial ℤ)))))
          ((Polynomial.mapRingHom (specializeAt a))
            (Polynomial.C (Polynomial.X : Polynomial (Polynomial ℤ)))) :=
        Polynomial.hom_eval₂ ..
    _ = resLiftOuterK K Φ' := by rw [hF, hX]; rfl

private theorem eval_C_resLiftOuterK (Φ' : Polynomial (Polynomial ℤ)) (b : K) :
    (resLiftOuterK K Φ').eval (Polynomial.C b) = fibrePoly Φ' b := by
  have hF : (Polynomial.evalRingHom (Polynomial.C b : Polynomial K)).comp
        (Polynomial.mapRingHom (Int.castRingHom (Polynomial K)))
      = (Polynomial.C : K →+* Polynomial K).comp
          (Polynomial.eval₂RingHom (Int.castRingHom K) b) := by
    refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
    simp
  have hX : (Polynomial.evalRingHom (Polynomial.C b : Polynomial K))
        (Polynomial.C (Polynomial.X : Polynomial K)) = Polynomial.X := by
    simp
  calc (resLiftOuterK K Φ').eval (Polynomial.C b)
      = (Polynomial.evalRingHom (Polynomial.C b))
          (Φ'.eval₂ (Polynomial.mapRingHom (Int.castRingHom (Polynomial K)))
            (Polynomial.C (Polynomial.X : Polynomial K))) := rfl
    _ = Φ'.eval₂ ((Polynomial.evalRingHom (Polynomial.C b)).comp
          (Polynomial.mapRingHom (Int.castRingHom (Polynomial K))))
          ((Polynomial.evalRingHom (Polynomial.C b))
            (Polynomial.C (Polynomial.X : Polynomial K))) := Polynomial.hom_eval₂ ..
    _ = fibrePoly Φ' b := by rw [hF, hX]; rfl

private theorem natDegree_resLiftOuterK_le (Φ' : Polynomial (Polynomial ℤ)) (a : K) :
    (resLiftOuterK K Φ').natDegree ≤ (resLiftOuter Φ').natDegree := by
  rw [← map_resLiftOuter Φ' a]
  exact Polynomial.natDegree_map_le

end Specialize

section BiResultant

private def biResultant (Φ Φ' : Polynomial (Polynomial ℤ)) : Polynomial (Polynomial ℤ) :=
  Polynomial.resultant (resLiftInner Φ) (resLiftOuter Φ')
    Φ.natDegree (resLiftOuter Φ').natDegree

variable {K : Type*} [Field K] [IsAlgClosed K]

private theorem fibrePoly_biResultant {Φ : Polynomial (Polynomial ℤ)}
    (Φ' : Polynomial (Polynomial ℤ)) (hΦ : Φ.Monic) (a : K) :
    fibrePoly (biResultant Φ Φ') a = compositeFibrePoly Φ Φ' a := by

  rw [← specializeAt_eq_fibrePoly, biResultant, ← Polynomial.resultant_map_map,
    map_resLiftInner, map_resLiftOuter]

  have hmono : ((fibrePoly Φ a).map (Polynomial.C : K →+* Polynomial K)).Monic :=
    (monic_fibrePoly hΦ a).map _
  have hdeg : ((fibrePoly Φ a).map (Polynomial.C : K →+* Polynomial K)).natDegree
      = Φ.natDegree :=
    ((monic_fibrePoly hΦ a).natDegree_map _).trans (hΦ.natDegree_map _)
  have hsplit : ((fibrePoly Φ a).map (Polynomial.C : K →+* Polynomial K)).Splits :=
    (IsAlgClosed.splits (fibrePoly Φ a)).map _

  rw [← hdeg, Polynomial.resultant_eq_prod_eval _ _ _
      (natDegree_resLiftOuterK_le Φ' a) hsplit, hmono.leadingCoeff, one_pow, one_mul]

  rw [(IsAlgClosed.splits (fibrePoly Φ a)).roots_map_of_injective Polynomial.C_injective,
    Multiset.map_map, compositeFibrePoly_def]

  congr 1
  exact Multiset.map_congr rfl fun b _ => eval_C_resLiftOuterK Φ' b

end BiResultant

section MonicDegree

private theorem natDegree_compositeFibrePoly {K : Type*} [Field K] [IsAlgClosed K]
    {Φ Φ' : Polynomial (Polynomial ℤ)} (hΦ : Φ.Monic) (hΦ' : Φ'.Monic) (a : K) :
    (compositeFibrePoly Φ Φ' a).natDegree = Φ.natDegree * Φ'.natDegree := by
  rw [compositeFibrePoly_def, natDegree_multiset_prod_of_monic _
    (fun _ hb => by
      obtain ⟨b, -, rfl⟩ := Multiset.mem_map.mp hb
      exact monic_fibrePoly hΦ' b)]
  rw [Multiset.map_map]
  have hsame : ((fibrePoly Φ a).roots.map fun b => (fibrePoly Φ' b).natDegree)
      = (fibrePoly Φ a).roots.map fun _ => Φ'.natDegree :=
    Multiset.map_congr rfl fun b _ => natDegree_fibrePoly hΦ' b
  rw [Function.comp_def, hsame, Multiset.map_const', Multiset.sum_replicate,
    card_roots_fibrePoly_of_monic hΦ a, smul_eq_mul]

local notation "ℚ̄" => AlgebraicClosure ℚ

private theorem intPoly_eq_C_of_forall_algebraicClosure_eval (p : Polynomial ℤ) (c : ℤ)
    (h : ∀ a : ℚ̄, p.eval₂ (Int.castRingHom ℚ̄) a = (c : ℚ̄)) :
    p = Polynomial.C c := by
  have hinj : Function.Injective (Int.castRingHom ℚ̄) := fun x y hxy =>
    Int.cast_injective (α := ℚ̄) hxy
  refine Polynomial.map_injective _ hinj ?_
  rw [Polynomial.map_C]
  refine Polynomial.funext fun a => ?_
  rw [Polynomial.eval_map, Polynomial.eval_C]
  exact h a

private theorem coeff_fibrePoly {K : Type*} [Field K] (Ψ : Polynomial (Polynomial ℤ))
    (a : K) (j : ℕ) :
    (fibrePoly Ψ a).coeff j = (Ψ.coeff j).eval₂ (Int.castRingHom K) a := by
  rw [fibrePoly, Polynomial.coeff_map, Polynomial.coe_eval₂RingHom]

private theorem eval₂_coeff_biResultant_eq_coeff_compositeFibrePoly {K : Type*} [Field K]
    [IsAlgClosed K] {Φ Φ' : Polynomial (Polynomial ℤ)} (hΦ : Φ.Monic) (a : K) (j : ℕ) :
    ((biResultant Φ Φ').coeff j).eval₂ (Int.castRingHom K) a
      = (compositeFibrePoly Φ Φ' a).coeff j := by
  rw [← fibrePoly_biResultant Φ' hΦ a, coeff_fibrePoly]

private theorem coeff_biResultant_natDegree_mul_natDegree
    {Φ Φ' : Polynomial (Polynomial ℤ)} (hΦ : Φ.Monic) (hΦ' : Φ'.Monic) :
    (biResultant Φ Φ').coeff (Φ.natDegree * Φ'.natDegree) = 1 := by
  have h := intPoly_eq_C_of_forall_algebraicClosure_eval
    ((biResultant Φ Φ').coeff (Φ.natDegree * Φ'.natDegree)) 1 ?_
  · simpa using h
  intro a
  rw [eval₂_coeff_biResultant_eq_coeff_compositeFibrePoly hΦ a, Int.cast_one,
    ← natDegree_compositeFibrePoly hΦ hΦ' a]
  exact (monic_compositeFibrePoly hΦ' a).coeff_natDegree

private theorem coeff_biResultant_eq_zero_of_natDegree_mul_lt
    {Φ Φ' : Polynomial (Polynomial ℤ)} (hΦ : Φ.Monic) (hΦ' : Φ'.Monic) {j : ℕ}
    (hj : Φ.natDegree * Φ'.natDegree < j) : (biResultant Φ Φ').coeff j = 0 := by
  have h := intPoly_eq_C_of_forall_algebraicClosure_eval ((biResultant Φ Φ').coeff j) 0 ?_
  · simpa using h
  intro a
  rw [eval₂_coeff_biResultant_eq_coeff_compositeFibrePoly hΦ a, Int.cast_zero]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt
    ((natDegree_compositeFibrePoly hΦ hΦ' a).symm ▸ hj)

private theorem monic_biResultant {Φ Φ' : Polynomial (Polynomial ℤ)}
    (hΦ : Φ.Monic) (hΦ' : Φ'.Monic) : (biResultant Φ Φ').Monic :=
  Polynomial.monic_of_natDegree_le_of_coeff_eq_one (Φ.natDegree * Φ'.natDegree)
    (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun _ hj =>
      coeff_biResultant_eq_zero_of_natDegree_mul_lt hΦ hΦ' hj)
    (coeff_biResultant_natDegree_mul_natDegree hΦ hΦ')

private theorem natDegree_biResultant {Φ Φ' : Polynomial (Polynomial ℤ)}
    (hΦ : Φ.Monic) (hΦ' : Φ'.Monic) :
    (biResultant Φ Φ').natDegree = Φ.natDegree * Φ'.natDegree :=
  Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun _ hj =>
      coeff_biResultant_eq_zero_of_natDegree_mul_lt hΦ hΦ' hj)
    (by rw [coeff_biResultant_natDegree_mul_natDegree hΦ hΦ']; exact one_ne_zero)

end MonicDegree

section Engine

private def evalModularPair {R : Type*} [CommRing R] (x y : R)
    (Φ : Polynomial (Polynomial ℤ)) : R :=
  Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom R) x) y

private theorem evalModularPair_eq_eval_fibrePoly {K : Type*} [Field K] (a b : K)
    (Φ : Polynomial (Polynomial ℤ)) :
    evalModularPair a b Φ = (fibrePoly Φ a).eval b := by
  rw [evalModularPair, fibrePoly, Polynomial.eval_map]

private theorem Polynomial.resultant_eq_zero_of_isRoot_isRoot {R : Type*} [CommRing R]
    {f g : R[X]} {b : R} (hf : f.IsRoot b) (hg : g.IsRoot b)
    {m n : ℕ} (hfm : f.natDegree ≤ m) (hgn : g.natDegree ≤ n) (hmn : m ≠ 0 ∨ n ≠ 0) :
    Polynomial.resultant f g m n = 0 := by
  obtain ⟨p, q, _, _, hbez⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant f g hfm hgn hmn
  have heval := congrArg (Polynomial.eval b) hbez
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, hf.eq_zero,
    hg.eq_zero, zero_mul, add_zero] at heval
  exact heval.symm

variable {K : Type*} [Field K]

private theorem eval_map_evalRingHom_resLiftOuterK (Φ' : Polynomial (Polynomial ℤ))
    (b c : K) :
    ((resLiftOuterK K Φ').map (Polynomial.evalRingHom c)).eval b
      = evalModularPair b c Φ' :=
  calc ((resLiftOuterK K Φ').map (Polynomial.evalRingHom c)).eval b
      = (resLiftOuterK K Φ').eval₂ (Polynomial.evalRingHom c)
          ((Polynomial.evalRingHom c) (Polynomial.C b)) := by
        rw [Polynomial.eval_map, Polynomial.coe_evalRingHom, Polynomial.eval_C]
    _ = (Polynomial.evalRingHom c) ((resLiftOuterK K Φ').eval (Polynomial.C b)) :=
        Polynomial.eval₂_hom _ _
    _ = evalModularPair b c Φ' := by
        rw [eval_C_resLiftOuterK, Polynomial.coe_evalRingHom,
          evalModularPair_eq_eval_fibrePoly]

private theorem evalModularPair_biResultant_eq_zero_of_common
    {Φ Φ' : Polynomial (Polynomial ℤ)} (hΦ : Φ.Monic) (hΦpos : Φ.natDegree ≠ 0)
    {a b c : K} (hab : evalModularPair a b Φ = 0) (hbc : evalModularPair b c Φ' = 0) :
    evalModularPair a c (biResultant Φ Φ') = 0 := by

  rw [evalModularPair_eq_eval_fibrePoly, ← specializeAt_eq_fibrePoly, biResultant,
    ← Polynomial.resultant_map_map, map_resLiftInner, map_resLiftOuter,
    show Polynomial.eval c
        = ⇑(Polynomial.evalRingHom c : Polynomial K →+* K) from rfl,
    ← Polynomial.resultant_map_map, Polynomial.map_map]

  rw [show (Polynomial.evalRingHom c).comp (Polynomial.C : K →+* Polynomial K)
        = RingHom.id K from
      RingHom.ext fun _ => Polynomial.eval_C,
    Polynomial.map_id]

  refine Polynomial.resultant_eq_zero_of_isRoot_isRoot
    (b := b)
    ?_ ?_ (natDegree_fibrePoly hΦ a).le ?_ (Or.inl hΦpos)
  · rw [Polynomial.IsRoot, ← evalModularPair_eq_eval_fibrePoly]
    exact hab
  · rw [Polynomial.IsRoot, eval_map_evalRingHom_resLiftOuterK]
    exact hbc
  · exact Polynomial.natDegree_map_le.trans (natDegree_resLiftOuterK_le Φ' a)

end Engine

section QExpansion

namespace ModularPolynomialData

private theorem eval₂_qExpand_eq_zero {N : ℕ} [NeZero N]
    (data : ModularPolynomialData N) (ℓ : ℕ) [NeZero ℓ] :
    data.Φ.eval₂ ((qExpand ℚ ℓ).comp evalAtJ) (jqN (ℓ * N)) = 0 := by
  have h := congrArg (qExpand ℚ ℓ) data.eval_eq_zero
  rw [map_zero, Polynomial.hom_eval₂] at h
  rwa [show qExpand ℚ ℓ (jqN N) = jqN (ℓ * N) from qExpand_qExpand N ℓ jq] at h

end ModularPolynomialData

private theorem evalAtJ_eq_eval₂RingHom_intCast_jq :
    evalAtJ = Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℚ)) jq := by
  refine Polynomial.ringHom_ext' ?_ ?_
  · exact Subsingleton.elim _ _
  · rw [evalAtJ_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

private theorem qExpand_comp_evalAtJ_eq_eval₂RingHom (m : ℕ) [NeZero m] :
    (qExpand ℚ m).comp evalAtJ
      = Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℚ)) (jqN m) := by
  refine Polynomial.ringHom_ext' ?_ ?_
  · exact Subsingleton.elim _ _
  · rw [RingHom.comp_apply, evalAtJ_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    rfl

namespace ModularPolynomialData

private theorem eval₂_biResultant_eq_zero {m n : ℕ} [NeZero m]
    [NeZero n] (data : ModularPolynomialData m) (data' : ModularPolynomialData n) :
    (biResultant data.Φ data'.Φ).eval₂ evalAtJ (jqN (m * n)) = 0 := by

  rw [evalAtJ_eq_eval₂RingHom_intCast_jq,
    show (biResultant data.Φ data'.Φ).eval₂
          (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℚ)) jq) (jqN (m * n))
        = evalModularPair jq (jqN (m * n)) (biResultant data.Φ data'.Φ) from rfl]

  have hmpos : data.Φ.natDegree ≠ 0 := by
    rw [data.natDegree_eq]
    exact (dedekindPsi_pos m (NeZero.ne m)).ne'

  refine evalModularPair_biResultant_eq_zero_of_common data.monic hmpos
    (b := jqN m) ?_ ?_
  ·
    show data.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℚ)) jq)
        (jqN m) = 0
    rw [← evalAtJ_eq_eval₂RingHom_intCast_jq]
    exact data.eval_eq_zero
  ·
    show data'.Φ.eval₂
        (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℚ)) (jqN m))
        (jqN (m * n)) = 0
    rw [← qExpand_comp_evalAtJ_eq_eval₂RingHom]
    exact data'.eval₂_qExpand_eq_zero m

end ModularPolynomialData
end QExpansion

namespace ModularPolynomialData

private def biResultantPacket {m n : ℕ} [NeZero m] [NeZero n]
    (data : ModularPolynomialData m) (data' : ModularPolynomialData n)
    (hmn : Nat.Coprime m n) :
    ModularPolynomialData (m * n) where
  Φ := biResultant data.Φ data'.Φ
  monic := monic_biResultant data.monic data'.monic
  natDegree_eq := by
    rw [natDegree_biResultant data.monic data'.monic, data.natDegree_eq, data'.natDegree_eq,
      dedekindPsi_mul_of_coprime m n hmn]
  eval_eq_zero := data.eval₂_biResultant_eq_zero data'

end ModularPolynomialData

private theorem nonempty_modularPolynomialData_mul_of_coprime {m n : ℕ} [NeZero m] [NeZero n]
    (data : ModularPolynomialData m) (data' : ModularPolynomialData n)
    (hmn : Nat.Coprime m n) : Nonempty (ModularPolynomialData (m * n)) :=
  ⟨data.biResultantPacket data' hmn⟩

private def castModularPolynomialData {M N : ℕ} [NeZero M] [NeZero N] (h : M = N)
    (d : ModularPolynomialData M) : ModularPolynomialData N where
  Φ := d.Φ
  monic := d.monic
  natDegree_eq := h ▸ d.natDegree_eq
  eval_eq_zero := h ▸ d.eval_eq_zero

private def primePacket (p : ℕ) [NeZero p] (hp : p.Prime) : ModularPolynomialData p :=
  (modularPolynomialFamily p hp).choose

private def modularPolynomialDataSquarefree (N : ℕ) [NeZero N] (hsf : Squarefree N)
    (hN : 1 < N) : ModularPolynomialData N :=
  let p := N.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpdvd : p ∣ N := Nat.minFac_dvd N
  have heq : p * (N / p) = N := Nat.mul_div_cancel' hpdvd
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  have hq_pos : 0 < N / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpdvd) hp.pos
  haveI : NeZero (N / p) := ⟨hq_pos.ne'⟩
  have hcop : Nat.Coprime p (N / p) := by
    rw [hp.coprime_iff_not_dvd]
    intro hd
    have h2 : p * p ∣ N := heq ▸ mul_dvd_mul_left p hd
    exact hp.ne_one (Nat.isUnit_iff.mp (hsf p h2))
  have hsf' : Squarefree (N / p) :=
    hsf.squarefree_of_dvd ⟨p, (Nat.div_mul_cancel hpdvd).symm⟩
  if h1 : N / p = 1 then
    castModularPolynomialData (by rw [h1, mul_one] at heq; exact heq) (primePacket p hp)
  else
    have hN' : 1 < N / p := by omega
    castModularPolynomialData heq
      ((primePacket p hp).biResultantPacket
        (modularPolynomialDataSquarefree (N / p) hsf' hN') hcop)
termination_by N
decreasing_by exact Nat.div_lt_self (by omega) hp.one_lt

theorem nonempty_modularPolynomialData_of_squarefree (N : ℕ) [NeZero N]
    (hsf : Squarefree N) (hN : 1 < N) : Nonempty (ModularPolynomialData N) :=
  ⟨modularPolynomialDataSquarefree N hsf hN⟩


end ModularCurve
