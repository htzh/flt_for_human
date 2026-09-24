/-
  m10 — tower integrality/finiteness and the Hecke integrality predicates (M10).

  The two `finiteAlong_hecke*Bar_of_modularPolynomialData` heads are the real
  content: the target field is written as `adjoin L (gens L (N * ℓ))` with
  `gens L N = {jqNModC L d | d ∣ N}` (m7's
  `laurentBaseChange_modularFunctionFieldFull`), each generator is integral over
  the source (m6's `isIntegral_jqNModC_mul`, and
  `ModularPolynomialData.eval_jqNModC_of_mul_eq_zero` for the `q ↦ q ^ ℓ` image),
  and an integral f.g. algebra extension is finite. The `_of_prime` forms are the
  general ones at `exists_modularPolynomialData_evalSymm`; the tower forms are
  mathlib's inclusion integrality/finiteness (`RingHom.isIntegral_of_surjective`,
  `AlgebraicCurve.finiteAlong_of_surjective`, `finiteAlong_comp`) over the
  antisymmetry `towerInclBar_surjective_of_dvd_dvd`.

  FLT provenance, pinned `aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_finiteAlong_heckeAlphaBar_of_modularPolynomialData.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_finiteAlong_heckeBetaBar_of_modularPolynomialData.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_towerInclBar_isIntegral.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_towerSubstBar_isIntegral.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_towerInclBar_finiteAlong.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_towerSubstBar_finiteAlong.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_towerInclBar_surjective_of_dvd_dvd.lean
-/
import FLTForHuman.ModularCurve.Defs.HeckeOperator
import FLTForHuman.ModularCurve.Defs.DegeneracyTower
import FLTForHuman.ModularCurve.Defs.HeckeTotal
import FLTForHuman.ModularCurve.Degree.LaurentGlue
import FLTForHuman.ModularCurve.Degree.PhiData
import FLTForHuman.AlgebraicCurve.WeilExchange.Transport
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IntermediateField Polynomial

namespace ModularCurve

/-! ## The generator set `{jqNModC L d | d ∣ N}` and its integrality -/

section Gens

private theorem dvd_mul_prime_cases {N ℓ e : ℕ} (hℓ : ℓ.Prime) (he : e ∣ N * ℓ) :
    e ∣ N ∨ ∃ d : ℕ, d ∣ N ∧ e = d * ℓ := by
  by_cases hle : ℓ ∣ e
  · obtain ⟨d, rfl⟩ := hle
    right
    refine ⟨d, ?_, mul_comm ℓ d⟩
    rw [mul_comm N ℓ] at he
    exact (Nat.mul_dvd_mul_iff_left hℓ.pos).mp he
  · left
    exact Nat.Coprime.dvd_of_dvd_mul_right
      (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hle)) he

private def gens (L : Type*) [Field L] (N : ℕ) : Set (LaurentSeries L) :=
  {x | ∃ (d : ℕ) (_ : NeZero d), d ∣ N ∧ x = jqNModC L d}

private theorem gens_finite (L : Type*) [Field L] (N : ℕ) [NeZero N] : (gens L N).Finite := by
  classical
  refine ((Set.finite_Iic N).image fun d : ℕ => if h : d = 0 then (0 : LaurentSeries L)
    else @jqNModC L _ d ⟨h⟩).subset ?_
  rintro x ⟨d, hd, hdvd, rfl⟩
  exact ⟨d, Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hdvd, by simp [NeZero.ne d]⟩

private theorem jqNModC_mem_bar (L : Type*) [Field L] [Algebra ℚ L] {N d : ℕ} [NeZero N]
    [NeZero d] (hd : d ∣ N) : jqNModC L d ∈ laurentBaseChange L (modularFunctionFieldFull N) := by
  rw [← coeffEmb_jqN]
  exact coeffEmb_mem_laurentBaseChange L (jqd_mem_full N hd)

private theorem isIntegral_gens {L : Type*} [Field L] [Algebra ℚ L] {ℓ : ℕ} [NeZero ℓ]
    (data : ModularPolynomialData ℓ) (hℓ : ℓ.Prime) (N : ℕ) [NeZero N] {x : LaurentSeries L}
    (hx : x ∈ gens L (N * ℓ)) : IsIntegral (laurentBaseChange L (modularFunctionFieldFull N)) x := by
  obtain ⟨e, hne, hdvd, rfl⟩ := hx
  rcases dvd_mul_prime_cases hℓ hdvd with heM | ⟨d, hdM, rfl⟩
  · exact isIntegral_algebraMap (A := LaurentSeries L)
      (x := (⟨jqNModC L e, jqNModC_mem_bar L heM⟩ : laurentBaseChange L (modularFunctionFieldFull N)))
  · have : NeZero d := ⟨fun h => (NeZero.ne (d * ℓ)) (by rw [h, zero_mul])⟩
    exact isIntegral_jqNModC_mul _ data d (jqNModC_mem_bar L hdM)

end Gens

/-! ## The two general `FiniteAlong` forms -/

section Alpha

theorem finiteAlong_heckeAlphaBar_of_modularPolynomialData (L : Type*) [Field L] [Algebra ℚ L]
    {ℓ : ℕ} [NeZero ℓ] (data : ModularPolynomialData ℓ) (hℓ : ℓ.Prime) (N : ℕ) [NeZero N] :
    FiniteAlong L (heckeAlphaBar L N ℓ) := by
  let : Algebra (laurentBaseChange L (modularFunctionFieldFull N))
      (laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) := (heckeAlphaBar L N ℓ).toRingHom.toAlgebra
  let : Module (laurentBaseChange L (modularFunctionFieldFull N))
      (laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) := Algebra.toModule
  show Module.Finite (laurentBaseChange L (modularFunctionFieldFull N))
    (laurentBaseChange L (modularFunctionFieldFull (N * ℓ)))
  set valAlong : laurentBaseChange L (modularFunctionFieldFull (N * ℓ))
      →ₐ[laurentBaseChange L (modularFunctionFieldFull N)] LaurentSeries L :=
    ⟨algebraMap (laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) (LaurentSeries L), fun c => rfl⟩
    with hvalAlong
  have hval_inj : Function.Injective valAlong := fun a b h => Subtype.ext h
  set S : Set (laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) :=
    {y | (y : LaurentSeries L) ∈ gens L (N * ℓ)} with hS
  have hint : ∀ y ∈ S, IsIntegral (laurentBaseChange L (modularFunctionFieldFull N)) y := by
    intro y hyS
    refine (isIntegral_algHom_iff valAlong hval_inj).mp ?_
    exact isIntegral_gens data hℓ N hyS
  have hgen : laurentBaseChange L (modularFunctionFieldFull (N * ℓ)) =
      IntermediateField.adjoin L (gens L (N * ℓ)) :=
    laurentBaseChange_modularFunctionFieldFull L (N * ℓ)
  have hadj : IntermediateField.adjoin (laurentBaseChange L (modularFunctionFieldFull N)) S = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    set K := IntermediateField.adjoin (laurentBaseChange L (modularFunctionFieldFull N)) S with hK
    have hle : laurentBaseChange L (modularFunctionFieldFull (N * ℓ)) ≤ (K.map valAlong).restrictScalars L := by
      refine hgen.le.trans ?_
      refine IntermediateField.adjoin_le_iff.mpr fun x hx => ?_
      have hxmem : x ∈ laurentBaseChange L (modularFunctionFieldFull (N * ℓ)) :=
        hgen.ge (IntermediateField.subset_adjoin L _ hx)
      show x ∈ K.map valAlong
      exact (IntermediateField.mem_map _).mpr
        ⟨⟨x, hxmem⟩, IntermediateField.subset_adjoin _ _ (show _ ∈ S from hx), rfl⟩
    obtain ⟨w, hwK, hwz⟩ := (IntermediateField.mem_map _).mp (hle z.2)
    exact (Subtype.ext hwz : w = z) ▸ hwK
  have hSfin : S.Finite :=
    Set.Finite.preimage Subtype.val_injective.injOn (gens_finite L (N * ℓ))
  rw [Module.finite_def]
  have htop : Algebra.adjoin (laurentBaseChange L (modularFunctionFieldFull N)) S = ⊤ :=
    (IntermediateField.adjoin_eq_top_iff_of_isAlgebraic
      (fun x hx => (hint x hx).isAlgebraic)).mp hadj
  rw [← Algebra.top_toSubmodule, ← htop]
  exact fg_adjoin_of_finite hSfin hint

end Alpha

section Beta

private theorem qExpand_jqNModC (L : Type*) [Field L] (ℓ e : ℕ) [NeZero ℓ] [NeZero e] :
    qExpand L ℓ (jqNModC L e) = jqNModC L (e * ℓ) := by
  unfold jqNModC
  rw [qExpand_qExpand]
  exact qExpand_congr (mul_comm ℓ e) _

private theorem isIntegralElem_heckeBetaBar_gens {L : Type*} [Field L] [Algebra ℚ L] {ℓ : ℕ}
    [NeZero ℓ] (data : ModularPolynomialData ℓ) (hsymm : EvalSymm data.Φ) (hℓ : ℓ.Prime)
    (N : ℕ) [NeZero N] {x : LaurentSeries L}
    (hxmem : x ∈ laurentBaseChange L (modularFunctionFieldFull (N * ℓ)))
    (hx : x ∈ gens L (N * ℓ)) :
    (heckeBetaBar L N ℓ).toRingHom.IsIntegralElem
      (⟨x, hxmem⟩ : laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) := by
  obtain ⟨e, hne, hdvd, rfl⟩ := hx
  rcases dvd_mul_prime_cases hℓ hdvd with heM | ⟨d, hdM, rfl⟩
  · set ev : Polynomial ℤ →+* laurentBaseChange L (modularFunctionFieldFull N) :=
      (aeval (R := ℤ) (⟨jqNModC L e, jqNModC_mem_bar L heM⟩ :
        laurentBaseChange L (modularFunctionFieldFull N))).toRingHom with hev
    refine ⟨data.Φ.map ev, data.monic.map ev, ?_⟩
    rw [Polynomial.eval₂_map]
    refine Subtype.ext ?_
    have hcoe := Polynomial.hom_eval₂ data.Φ ((heckeBetaBar L N ℓ).toRingHom.comp ev)
      (algebraMap (laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) (LaurentSeries L))
      (⟨jqNModC L e, hxmem⟩ : laurentBaseChange L (modularFunctionFieldFull (N * ℓ)))
    refine hcoe.trans ?_
    have hcomp : (algebraMap (laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) (LaurentSeries L)).comp
        ((heckeBetaBar L N ℓ).toRingHom.comp ev) = (aeval (R := ℤ) (jqNModC L (e * ℓ))).toRingHom := by
      refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
      simp only [RingHom.coe_comp, Function.comp_apply, hev, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, aeval_X]
      show ((heckeBetaBar L N ℓ ⟨jqNModC L e, _⟩ :
          laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) : LaurentSeries L) = jqNModC L (e * ℓ)
      rw [coe_heckeBetaBar]
      exact qExpand_jqNModC L ℓ e
    rw [hcomp]
    exact data.eval_jqNModC_of_mul_eq_zero hsymm L e
  · have : NeZero d := ⟨fun h => (NeZero.ne (d * ℓ)) (by rw [h, zero_mul])⟩
    refine ⟨Polynomial.X - Polynomial.C ⟨jqNModC L d, jqNModC_mem_bar L hdM⟩, Polynomial.monic_X_sub_C _, ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, sub_eq_zero]
    refine Subtype.ext ?_
    show jqNModC L (d * ℓ) = ((heckeBetaBar L N ℓ ⟨jqNModC L d, _⟩ :
      laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) : LaurentSeries L)
    rw [coe_heckeBetaBar]
    exact (qExpand_jqNModC L ℓ d).symm

theorem finiteAlong_heckeBetaBar_of_modularPolynomialData (L : Type*) [Field L] [Algebra ℚ L]
    {ℓ : ℕ} [NeZero ℓ] (data : ModularPolynomialData ℓ) (hsymm : EvalSymm data.Φ)
    (hℓ : ℓ.Prime) (N : ℕ) [NeZero N] : FiniteAlong L (heckeBetaBar L N ℓ) := by
  let : Algebra (laurentBaseChange L (modularFunctionFieldFull N))
      (laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) := (heckeBetaBar L N ℓ).toRingHom.toAlgebra
  let : Module (laurentBaseChange L (modularFunctionFieldFull N))
      (laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) := Algebra.toModule
  show Module.Finite (laurentBaseChange L (modularFunctionFieldFull N))
    (laurentBaseChange L (modularFunctionFieldFull (N * ℓ)))
  set S : Set (laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) :=
    {y | (y : LaurentSeries L) ∈ gens L (N * ℓ)} with hS
  have hint : ∀ y ∈ S, IsIntegral (laurentBaseChange L (modularFunctionFieldFull N)) y := by
    rintro ⟨x, hxmem⟩ hyS
    exact isIntegralElem_heckeBetaBar_gens data hsymm hℓ N hxmem hyS
  have hgen : laurentBaseChange L (modularFunctionFieldFull (N * ℓ)) =
      IntermediateField.adjoin L (gens L (N * ℓ)) :=
    laurentBaseChange_modularFunctionFieldFull L (N * ℓ)
  set ι : laurentBaseChange L (modularFunctionFieldFull (N * ℓ)) →ₐ[L] LaurentSeries L :=
    (laurentBaseChange L (modularFunctionFieldFull (N * ℓ))).val with hι
  have hLadj : IntermediateField.adjoin L S = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    have hle : laurentBaseChange L (modularFunctionFieldFull (N * ℓ)) ≤ (IntermediateField.adjoin L S).map ι := by
      refine hgen.le.trans ?_
      refine IntermediateField.adjoin_le_iff.mpr fun x hx => ?_
      have hxmem : x ∈ laurentBaseChange L (modularFunctionFieldFull (N * ℓ)) :=
        hgen.ge (IntermediateField.subset_adjoin L _ hx)
      exact (IntermediateField.mem_map _).mpr
        ⟨⟨x, hxmem⟩, IntermediateField.subset_adjoin _ _ (show _ ∈ S from hx), rfl⟩
    obtain ⟨w, hwL, hwz⟩ := (IntermediateField.mem_map _).mp (hle z.2)
    exact (Subtype.ext hwz : w = z) ▸ hwL
  have hadj : IntermediateField.adjoin (laurentBaseChange L (modularFunctionFieldFull N)) S = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    have h1 : (IntermediateField.adjoin L S).toSubfield
        ≤ (IntermediateField.adjoin (laurentBaseChange L (modularFunctionFieldFull N)) S).toSubfield := by
      rw [IntermediateField.adjoin_toSubfield]
      refine Subfield.closure_le.mpr ?_
      rintro x (⟨c, rfl⟩ | hx)
      · have : algebraMap L (laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) c
            = heckeBetaBar L N ℓ (algebraMap L (laurentBaseChange L (modularFunctionFieldFull N)) c) :=
          ((heckeBetaBar L N ℓ).commutes c).symm
        rw [SetLike.mem_coe, IntermediateField.mem_toSubfield, this]
        exact (IntermediateField.adjoin (laurentBaseChange L (modularFunctionFieldFull N)) S).algebraMap_mem _
      · exact IntermediateField.subset_adjoin _ _ hx
    exact h1 (hLadj.ge IntermediateField.mem_top)
  have hSfin : S.Finite :=
    Set.Finite.preimage Subtype.val_injective.injOn (gens_finite L (N * ℓ))
  rw [Module.finite_def]
  have htop : Algebra.adjoin (laurentBaseChange L (modularFunctionFieldFull N)) S = ⊤ :=
    (IntermediateField.adjoin_eq_top_iff_of_isAlgebraic
      (fun x hx => (hint x hx).isAlgebraic)).mp hadj
  rw [← Algebra.top_toSubmodule, ← htop]
  exact fg_adjoin_of_finite hSfin hint

end Beta

/-! ## The general integrality predicates -/

section Integral

theorem heckeAlphaBarIntegral_of_modularPolynomialData (L : Type*) [Field L] [Algebra ℚ L]
    {ℓ : ℕ} [NeZero ℓ] (data : ModularPolynomialData ℓ) (hℓ : ℓ.Prime) (N : ℕ) [NeZero N] :
    HeckeAlphaBarIntegral L N ℓ := by
  let : Algebra (laurentBaseChange L (modularFunctionFieldFull N))
      (laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) := (heckeAlphaBar L N ℓ).toRingHom.toAlgebra
  let : Module (laurentBaseChange L (modularFunctionFieldFull N))
      (laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) := Algebra.toModule
  have : Module.Finite (laurentBaseChange L (modularFunctionFieldFull N))
      (laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) :=
    finiteAlong_heckeAlphaBar_of_modularPolynomialData L data hℓ N
  have : Algebra.IsIntegral (laurentBaseChange L (modularFunctionFieldFull N))
      (laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) := Algebra.IsIntegral.of_finite _ _
  exact fun x => Algebra.IsIntegral.isIntegral (R := laurentBaseChange L (modularFunctionFieldFull N)) x

theorem heckeBetaBarIntegral_of_modularPolynomialData (L : Type*) [Field L] [Algebra ℚ L]
    {ℓ : ℕ} [NeZero ℓ] (data : ModularPolynomialData ℓ) (hsymm : EvalSymm data.Φ)
    (hℓ : ℓ.Prime) (N : ℕ) [NeZero N] : HeckeBetaBarIntegral L N ℓ := by
  let : Algebra (laurentBaseChange L (modularFunctionFieldFull N))
      (laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) := (heckeBetaBar L N ℓ).toRingHom.toAlgebra
  let : Module (laurentBaseChange L (modularFunctionFieldFull N))
      (laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) := Algebra.toModule
  have : Module.Finite (laurentBaseChange L (modularFunctionFieldFull N))
      (laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) :=
    finiteAlong_heckeBetaBar_of_modularPolynomialData L data hsymm hℓ N
  have : Algebra.IsIntegral (laurentBaseChange L (modularFunctionFieldFull N))
      (laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) := Algebra.IsIntegral.of_finite _ _
  exact fun x => Algebra.IsIntegral.isIntegral (R := laurentBaseChange L (modularFunctionFieldFull N)) x

end Integral

/-! ## The prime forms -/

section Prime

theorem finiteAlong_heckeAlphaBar_of_prime (L : Type*) [Field L] [Algebra ℚ L] (N ℓ : ℕ)
    [NeZero N] [Fact ℓ.Prime] : FiniteAlong L (heckeAlphaBar L N ℓ) := by
  obtain ⟨data, _⟩ := exists_modularPolynomialData_evalSymm ℓ
  exact finiteAlong_heckeAlphaBar_of_modularPolynomialData L data Fact.out N

theorem finiteAlong_heckeBetaBar_of_prime (L : Type*) [Field L] [Algebra ℚ L] (N ℓ : ℕ)
    [NeZero N] [Fact ℓ.Prime] : FiniteAlong L (heckeBetaBar L N ℓ) := by
  obtain ⟨data, hsymm⟩ := exists_modularPolynomialData_evalSymm ℓ
  exact finiteAlong_heckeBetaBar_of_modularPolynomialData L data hsymm Fact.out N

theorem heckeAlphaBarIntegral_of_prime (L : Type*) [Field L] [Algebra ℚ L] (N ℓ : ℕ)
    [NeZero N] [Fact ℓ.Prime] : HeckeAlphaBarIntegral L N ℓ := by
  obtain ⟨data, _⟩ := exists_modularPolynomialData_evalSymm ℓ
  exact heckeAlphaBarIntegral_of_modularPolynomialData L data Fact.out N

theorem heckeBetaBarIntegral_of_prime (L : Type*) [Field L] [Algebra ℚ L] (N ℓ : ℕ)
    [NeZero N] [Fact ℓ.Prime] : HeckeBetaBarIntegral L N ℓ := by
  obtain ⟨data, hsymm⟩ := exists_modularPolynomialData_evalSymm ℓ
  exact heckeBetaBarIntegral_of_modularPolynomialData L data hsymm Fact.out N

end Prime

/-! ## The degeneracy-tower integrality and finiteness -/

section Tower

theorem towerInclBar_surjective_of_dvd_dvd (L : Type*) [Field L] [Algebra ℚ L] {N M : ℕ}
    [NeZero N] [NeZero M] (h : N ∣ M) (h' : M ∣ N) : Function.Surjective (towerInclBar L h) := by
  intro y
  refine ⟨towerInclBar L h' y, ?_⟩
  have e := congrArg (fun f => f y) (towerInclBar_comp_towerInclBar L h' h (dvd_refl M))
  simpa only [AlgHom.comp_apply, towerInclBar_self] using e

theorem towerInclBar_isIntegral (L : Type*) [Field L] [Algebra ℚ L] {N M : ℕ} [NeZero N]
    [NeZero M] (h : N ∣ M) : (towerInclBar L h).toRingHom.IsIntegral := by
  obtain ⟨k, hk⟩ := h
  induction k using Nat.strong_induction_on generalizing M with
  | _ k ih =>
    by_cases hk1 : k = 1
    · subst hk1
      exact RingHom.isIntegral_of_surjective _
        (towerInclBar_surjective_of_dvd_dvd L _ ⟨1, by rw [hk, mul_one, mul_one]⟩)
    · have hM0 : M ≠ 0 := NeZero.ne M
      have hk0 : k ≠ 0 := by rintro rfl; exact hM0 (by rw [hk, mul_zero])
      obtain ⟨p, hp, hpk⟩ := Nat.exists_prime_and_dvd hk1
      obtain ⟨k', rfl⟩ := hpk
      have hk'0 : k' ≠ 0 := by rintro rfl; exact hk0 (mul_zero p)
      have : Fact p.Prime := ⟨hp⟩
      have : NeZero (N * k') := ⟨mul_ne_zero (NeZero.ne N) hk'0⟩
      have hlt : k' < p * k' := lt_mul_left (Nat.pos_of_ne_zero hk'0) hp.one_lt
      have h₁ : N ∣ N * k' := ⟨k', rfl⟩
      have h₃ : N * k' * p ∣ M := ⟨1, by rw [hk]; ring⟩
      have h₃' : M ∣ N * k' * p := ⟨1, by rw [hk]; ring⟩
      have i₁ : (towerInclBar L h₁).toRingHom.IsIntegral := ih k' hlt rfl
      have i₂ : (heckeAlphaBar L (N * k') p).toRingHom.IsIntegral :=
        heckeAlphaBarIntegral_of_prime L (N * k') p
      have i₃ : (towerInclBar L h₃).toRingHom.IsIntegral :=
        RingHom.isIntegral_of_surjective _ (towerInclBar_surjective_of_dvd_dvd L h₃ h₃')
      have e : towerInclBar L (⟨p * k', hk⟩ : N ∣ M)
          = (towerInclBar L h₃).comp ((heckeAlphaBar L (N * k') p).comp (towerInclBar L h₁)) := by
        rw [heckeAlphaBar_eq_towerInclBar, towerInclBar_comp_towerInclBar L h₁ _
          ((dvd_mul_right N (k' * 1)).trans ⟨p, by ring⟩), towerInclBar_comp_towerInclBar]
      rw [e]
      exact RingHom.IsIntegral.trans _ _ (RingHom.IsIntegral.trans _ _ i₁ i₂) i₃

theorem towerSubstBar_isIntegral (L : Type*) [Field L] [Algebra ℚ L] {N M : ℕ} [NeZero N]
    [NeZero M] (ℓ : ℕ) [Fact ℓ.Prime] (h : N * ℓ ∣ M) :
    (towerSubstBar L N ℓ h).toRingHom.IsIntegral :=
  RingHom.IsIntegral.trans _ _ (heckeBetaBarIntegral_of_prime L N ℓ)
    (towerInclBar_isIntegral L h)

theorem towerInclBar_finiteAlong (L : Type*) [Field L] [Algebra ℚ L] {N M : ℕ} [NeZero N]
    [NeZero M] (h : N ∣ M) : FiniteAlong L (towerInclBar L h) := by
  obtain ⟨k, hk⟩ := h
  induction k using Nat.strong_induction_on generalizing M with
  | _ k ih =>
    by_cases hk1 : k = 1
    · subst hk1
      exact finiteAlong_of_surjective _
        (towerInclBar_surjective_of_dvd_dvd L _ ⟨1, by rw [hk, mul_one, mul_one]⟩)
    · have hM0 : M ≠ 0 := NeZero.ne M
      have hk0 : k ≠ 0 := by rintro rfl; exact hM0 (by rw [hk, mul_zero])
      obtain ⟨p, hp, hpk⟩ := Nat.exists_prime_and_dvd hk1
      obtain ⟨k', rfl⟩ := hpk
      have hk'0 : k' ≠ 0 := by rintro rfl; exact hk0 (mul_zero p)
      have : Fact p.Prime := ⟨hp⟩
      have : NeZero (N * k') := ⟨mul_ne_zero (NeZero.ne N) hk'0⟩
      have hlt : k' < p * k' := lt_mul_left (Nat.pos_of_ne_zero hk'0) hp.one_lt
      have h₁ : N ∣ N * k' := ⟨k', rfl⟩
      have h₃ : N * k' * p ∣ M := ⟨1, by rw [hk]; ring⟩
      have h₃' : M ∣ N * k' * p := ⟨1, by rw [hk]; ring⟩
      have i₁ : FiniteAlong L (towerInclBar L h₁) := ih k' hlt rfl
      have i₂ : FiniteAlong L (heckeAlphaBar L (N * k') p) :=
        finiteAlong_heckeAlphaBar_of_prime L (N * k') p
      have i₃ : FiniteAlong L (towerInclBar L h₃) :=
        finiteAlong_of_surjective _ (towerInclBar_surjective_of_dvd_dvd L h₃ h₃')
      have e : towerInclBar L (⟨p * k', hk⟩ : N ∣ M)
          = (towerInclBar L h₃).comp ((heckeAlphaBar L (N * k') p).comp (towerInclBar L h₁)) := by
        rw [heckeAlphaBar_eq_towerInclBar, towerInclBar_comp_towerInclBar L h₁ _
          ((dvd_mul_right N (k' * 1)).trans ⟨p, by ring⟩), towerInclBar_comp_towerInclBar]
      rw [e]
      exact finiteAlong_comp _ _ (finiteAlong_comp _ _ i₁ i₂) i₃

theorem towerSubstBar_finiteAlong (L : Type*) [Field L] [Algebra ℚ L] {N M : ℕ} [NeZero N]
    [NeZero M] (ℓ : ℕ) [Fact ℓ.Prime] (h : N * ℓ ∣ M) :
    FiniteAlong L (towerSubstBar L N ℓ h) := by
  rw [towerSubstBar]
  exact finiteAlong_comp _ _ (finiteAlong_heckeBetaBar_of_prime L N ℓ)
    (towerInclBar_finiteAlong L h)

end Tower

end ModularCurve

end
