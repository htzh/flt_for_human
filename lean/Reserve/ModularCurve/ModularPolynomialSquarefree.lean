/-
  The squarefree existence of the modular-polynomial datum (the biresultant route),
  shelved out of `Degree/PhiData`.

  `nonempty_modularPolynomialData_of_squarefree` builds a datum at a squarefree `N` by
  iterating the biresultant of the prime data. The live theory now has the unconditional
  canonical datum at every level, so this alternate construction has no live consumer; it
  is kept here with its proof, and its pin records that the content is ported.

  spec-pin: P2M/Sol/S_ModularCurve_nonempty_modularPolynomialData_of_squarefree.lean
-/
import FLTForHuman.ModularCurve.Degree.PhiData

set_option autoImplicit false

noncomputable section

open Polynomial IntermediateField Finset Nat

namespace ModularCurve

/-! ## The squarefree existence (the biresultant) -/


section FibrePoly

variable {K : Type*} [Field K]

-- `monic_fibrePoly`, `natDegree_fibrePoly` and `card_roots_fibrePoly_of_monic`
-- are the pin's public facts and live at their pin names in
-- `FLTForHuman/ModularCurve/Defs/FibrePoly.lean` (imported above; dedup, no
-- second copy here).

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
    rw [← qExpand_comp_evalAtJ]
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

end
