/-
  m9 — the roof generation and the diagonal degree: the two field-theoretic
  hypotheses of `heckeExchangeAt_of_WEX`.

  - `heckeRoof_adjoin_range_union_eq_top` (418 content): the roof's two legs
    generate the top field over `L`.
  - `finrankAlong_towerSubstBar_comp_heckeAlphaBar` (441 content): the diagonal
    degree is the product of the two Hecke degrees.

  Both files' heads are the `TS`/`conj`/`phiAtSeed`/`roots_prime_at_slot`
  prelude, which the port already publishes (`Defs/TS.lean`,
  `Defs/PhiAtSlot.lean`, `PhiSlotRoots.lean`, `Defs/Cyclotomic.lean`,
  `Defs/Twist.lean`) and imports here; none of it is rewritten. The three
  generic `AlgebraicCurve.finrankAlong` helpers the pin defines privately in its
  file are proved `private` here and recorded as promotion candidates for
  `AlgebraicCurve/Defs/Correspondence.lean`.

  FLT provenance, pinned `aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_heckeRoof_adjoin_range_union_eq_top.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_finrankAlong_towerSubstBar_comp_heckeAlphaBar.lean
-/
import FLTForHuman.ModularCurve.Degree.Relfinrank
import FLTForHuman.ModularCurve.Degree.LaurentGlue
import FLTForHuman.ModularCurve.Degree.PhiData
import FLTForHuman.ModularCurve.Defs.DegeneracyTower
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Collapse
import FLTForHuman.AlgebraicCurve.Defs.Correspondence
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

set_option autoImplicit false

noncomputable section

open IntermediateField Polynomial

namespace AlgebraicCurve

section FinrankAlongHelpers

/-! ## The three generic `finrankAlong` helpers (promotion candidates)

The pin defines these `private` inside its two degree/roof `S_` files; the port's
`AlgebraicCurve/Defs/Correspondence.lean` publishes only `finrankAlong` itself.
They belong beside it and are recorded as promotion candidates. -/

private theorem finrankAlong_comp {K F F' F'' : Type*} [Field K] [Field F] [Field F']
    [Field F''] [Algebra K F] [Algebra K F'] [Algebra K F''] (φ : F →ₐ[K] F')
    (χ : F' →ₐ[K] F'') :
    finrankAlong K (χ.comp φ) = finrankAlong K φ * finrankAlong K χ := by
  let : Algebra F F' := algebraAlong φ
  let : Algebra F' F'' := algebraAlong χ
  let : Algebra F F'' := algebraAlong (χ.comp φ)
  have : IsScalarTower F F' F'' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  show Module.finrank F F'' = Module.finrank F F' * Module.finrank F' F''
  exact (Module.finrank_mul_finrank F F' F'').symm

private theorem finrankAlong_id {K F : Type*} [Field K] [Field F] [Algebra K F] :
    finrankAlong K (AlgHom.id K F) = 1 := by
  let : Algebra F F := algebraAlong (AlgHom.id K F)
  show Module.finrank F F = 1
  exact Module.finrank_self F

private theorem finrankAlong_eq_relfinrank_fieldRange {K E : Type*} [Field K] [Field E]
    [Algebra K E] (A B : IntermediateField K E) (φ : A →ₐ[K] B) :
    finrankAlong K φ = IntermediateField.relfinrank ((B.val.comp φ).fieldRange) B := by
  have hRB : (B.val.comp φ).fieldRange ≤ B := by
    rintro x ⟨a, rfl⟩
    exact (φ a).2
  rw [IntermediateField.relfinrank_eq_finrank_of_le hRB]
  let : Algebra A B := algebraAlong φ
  let i : A ≃+* ((B.val.comp φ).fieldRange) :=
    (AlgEquiv.ofInjectiveField (B.val.comp φ)).toRingEquiv
  let j : B ≃+* (IntermediateField.extendScalars hRB) := RingEquiv.refl _
  exact Algebra.finrank_eq_of_equiv_equiv i j (by
    refine RingHom.ext fun a => Subtype.ext ?_
    rfl)

end FinrankAlongHelpers

end AlgebraicCurve

namespace ModularCurve

section DiagonalDegree

private theorem full_congr {a b : ℕ} [NeZero a] [NeZero b] (h : a = b) :
    modularFunctionFieldFull a = modularFunctionFieldFull b := by
  subst h; rfl

private theorem dedekindPsi_pos' (A : ℕ) [NeZero A] : 0 < dedekindPsi A := by
  rw [dedekindPsi]
  have h1 : (1 : ℕ) ∈ A.divisors.filter (fun d => Squarefree d) := by
    rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨one_dvd A, NeZero.ne A⟩, squarefree_one⟩
  calc 0 < A / 1 := by
        rw [Nat.div_one]
        exact Nat.pos_of_ne_zero (NeZero.ne A)
  _ ≤ ∑ d ∈ A.divisors with Squarefree d, A / d :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) h1

private theorem fieldRange_heckeBetaBar (L : Type*) [Field L] [Algebra ℚ L] (A : ℕ) [NeZero A]
    (ℓ : ℕ) [NeZero ℓ] :
    (((laurentBaseChange L (modularFunctionFieldFull (A * ℓ))).val.comp
        (heckeBetaBar L A ℓ)).fieldRange)
      = laurentBaseChange L ((modularFunctionFieldFull A).map (qExpandₐ ℓ)) := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨a, rfl⟩
    show qExpand L ℓ (a : LaurentSeries L) ∈ _
    refine qExpand_mem_laurentBaseChange ℓ (fun y hy => ?_) a.2
    rw [IntermediateField.mem_map]
    exact ⟨y, hy, rfl⟩
  · rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    show coeffEmb L (qExpand ℚ ℓ y) ∈ _
    rw [coeffEmb_qExpand]
    exact ⟨⟨coeffEmb L y, coeffEmb_mem_laurentBaseChange L hy⟩, rfl⟩

private theorem finrankAlong_heckeBetaBar (L : Type*) [Field L] [Algebra ℚ L]
    (A : ℕ) [NeZero A] (ℓ : ℕ) [hl : Fact (Nat.Prime ℓ)] :
    AlgebraicCurve.finrankAlong L (heckeBetaBar L A ℓ) = if ℓ ∣ A then ℓ else ℓ + 1 := by
  classical
  have hB2 := AlgebraicCurve.finrankAlong_eq_relfinrank_fieldRange _ _ (heckeBetaBar L A ℓ)
  have hcong : IntermediateField.relfinrank
      (((laurentBaseChange L (modularFunctionFieldFull (A * ℓ))).val.comp
        (heckeBetaBar L A ℓ)).fieldRange)
      (laurentBaseChange L (modularFunctionFieldFull (A * ℓ)))
      = IntermediateField.relfinrank
          (laurentBaseChange L ((modularFunctionFieldFull A).map (qExpandₐ ℓ)))
          (laurentBaseChange L (modularFunctionFieldFull (A * ℓ))) :=
    congrArg (fun X : IntermediateField L (LaurentSeries L) =>
      IntermediateField.relfinrank X (laurentBaseChange L (modularFunctionFieldFull (A * ℓ))))
      (fieldRange_heckeBetaBar L A ℓ)
  refine (hB2.trans hcong).trans ?_

  have hmemJ : jqN ℓ ∈ (modularFunctionFieldFull A).map (qExpandₐ ℓ) := by
    rw [IntermediateField.mem_map]
    refine ⟨jq, ?_, by rw [qExpandₐ_apply, jqN]⟩
    have h := jqd_mem_full A (one_dvd A)
    rwa [qExpand_one_apply] at h
  have hanchor_le : IntermediateField.adjoin ℚ ({jqN ℓ} : Set (LaurentSeries ℚ))
      ≤ (modularFunctionFieldFull A).map (qExpandₐ ℓ) := by
    rw [IntermediateField.adjoin_le_iff]
    rintro x rfl
    exact hmemJ
  have hmap_le : (modularFunctionFieldFull A).map (qExpandₐ ℓ) ≤ modularFunctionFieldFull (A * ℓ) :=
    full_degeneracy_map_le A ℓ
  have hmemJ2 : jqN ℓ ∈ modularFunctionFieldFull (A * ℓ) := hmap_le hmemJ

  have hXeq : laurentBaseChange L (IntermediateField.adjoin ℚ ({jqN ℓ} : Set (LaurentSeries ℚ)))
      = IntermediateField.adjoin L ({coeffEmb L (jqN ℓ)} : Set (LaurentSeries L)) := by
    rw [laurentBaseChange_adjoin, Set.image_singleton]
  have hXR : laurentBaseChange L (IntermediateField.adjoin ℚ ({jqN ℓ} : Set (LaurentSeries ℚ)))
      ≤ laurentBaseChange L ((modularFunctionFieldFull A).map (qExpandₐ ℓ)) :=
    laurentBaseChange_mono L hanchor_le
  have hRB : laurentBaseChange L ((modularFunctionFieldFull A).map (qExpandₐ ℓ))
      ≤ laurentBaseChange L (modularFunctionFieldFull (A * ℓ)) :=
    laurentBaseChange_mono L hmap_le

  have hTR1a := relfinrank_laurentBaseChange L
    ((modularFunctionFieldFull A).map (qExpandₐ ℓ)) (jqN ℓ) hmemJ (transcendental_jqN ℓ)
  have hTR1b := relfinrank_laurentBaseChange L
    (modularFunctionFieldFull (A * ℓ)) (jqN ℓ) hmemJ2 (transcendental_jqN ℓ)

  have hanchor_val : IntermediateField.relfinrank
      (IntermediateField.adjoin ℚ ({jqN ℓ} : Set (LaurentSeries ℚ)))
      ((modularFunctionFieldFull A).map (qExpandₐ ℓ)) = dedekindPsi A := by
    have hmapmap := IntermediateField.relfinrank_map_map
      (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (modularFunctionFieldFull A)
      (qExpandₐ ℓ)
    rw [IntermediateField.adjoin_map, Set.image_singleton] at hmapmap
    rw [show qExpandₐ ℓ jq = jqN ℓ from by rw [qExpandₐ_apply, jqN]] at hmapmap
    rw [hmapmap]
    exact relfinrank_full_eq_dedekindPsi A
  have hQside : IntermediateField.relfinrank
      (IntermediateField.adjoin ℚ ({jqN ℓ} : Set (LaurentSeries ℚ)))
      (modularFunctionFieldFull (A * ℓ))
      = dedekindPsi A * (if ℓ ∣ A then ℓ else ℓ + 1) := by
    rw [← IntermediateField.relfinrank_mul_relfinrank hanchor_le hmap_le, hanchor_val,
      relfinrank_qExpand_full A ℓ]

  have hbar : IntermediateField.relfinrank
      (laurentBaseChange L (IntermediateField.adjoin ℚ ({jqN ℓ} : Set (LaurentSeries ℚ))))
      (laurentBaseChange L ((modularFunctionFieldFull A).map (qExpandₐ ℓ)))
      * IntermediateField.relfinrank
        (laurentBaseChange L ((modularFunctionFieldFull A).map (qExpandₐ ℓ)))
        (laurentBaseChange L (modularFunctionFieldFull (A * ℓ)))
      = IntermediateField.relfinrank
          (laurentBaseChange L (IntermediateField.adjoin ℚ ({jqN ℓ} : Set (LaurentSeries ℚ))))
          (laurentBaseChange L (modularFunctionFieldFull (A * ℓ))) :=
    IntermediateField.relfinrank_mul_relfinrank hXR hRB
  rw [hXeq] at hbar
  rw [hTR1a, hanchor_val] at hbar
  rw [hTR1b, hQside] at hbar

  exact Nat.eq_of_mul_eq_mul_left (dedekindPsi_pos' A) hbar

private theorem finrankAlong_towerInclBar_of_eq (L : Type*) [Field L] [Algebra ℚ L]
    (A B : ℕ) [NeZero A] [NeZero B] (hAB : A = B) (h : A ∣ B) :
    AlgebraicCurve.finrankAlong L (towerInclBar (N := A) (M := B) L h) = 1 := by
  subst hAB
  have hid : towerInclBar (N := A) (M := A) L h = AlgHom.id L
      (laurentBaseChange L (modularFunctionFieldFull A)) :=
    AlgHom.ext fun x => towerInclBar_self L h x
  exact (congrArg (fun φ => AlgebraicCurve.finrankAlong L φ) hid).trans
    AlgebraicCurve.finrankAlong_id

private theorem finrankAlong_towerSubstBar_roof (L : Type*) [Field L] [Algebra ℚ L]
    (N : ℕ) [NeZero N] (ℓ ℓ' M : ℕ) [hl : Fact (Nat.Prime ℓ)] [hl' : Fact (Nat.Prime ℓ')]
    [NeZero M] (hM : M = N * ℓ * ℓ') (hne : ℓ ≠ ℓ') :
    AlgebraicCurve.finrankAlong L (towerSubstBar L (N * ℓ') ℓ (dvd_of_eq_roof N ℓ ℓ' M hM).2)
      = AlgebraicCurve.finrankAlong L (heckeBetaBar L N ℓ) := by
  classical
  have hsubst_eq : towerSubstBar L (N * ℓ') ℓ (dvd_of_eq_roof N ℓ ℓ' M hM).2
      = (towerInclBar L (dvd_of_eq_roof N ℓ ℓ' M hM).2).comp (heckeBetaBar L (N * ℓ') ℓ) := rfl
  refine Eq.trans (congrArg (fun φ => AlgebraicCurve.finrankAlong L φ) hsubst_eq) ?_
  refine Eq.trans (AlgebraicCurve.finrankAlong_comp (heckeBetaBar L (N * ℓ') ℓ)
    (towerInclBar L (dvd_of_eq_roof N ℓ ℓ' M hM).2)) ?_
  have hlev : N * ℓ' * ℓ = M := by rw [hM]; ring
  rw [finrankAlong_towerInclBar_of_eq L (N * ℓ' * ℓ) M hlev
    (dvd_of_eq_roof N ℓ ℓ' M hM).2, mul_one]
  refine (finrankAlong_heckeBetaBar L (N * ℓ') ℓ).trans
    (Eq.trans ?_ (finrankAlong_heckeBetaBar L N ℓ).symm)
  have hiff : ℓ ∣ N * ℓ' ↔ ℓ ∣ N := by
    constructor
    · intro h
      exact (Nat.Coprime.dvd_of_dvd_mul_right
        ((Nat.coprime_primes hl.out hl'.out).mpr hne) h)
    · intro h
      exact h.mul_right ℓ'
  by_cases hd : ℓ ∣ N
  · rw [ite_eq_left hd, ite_eq_left (hiff.mpr hd)]
  · rw [ite_eq_right hd, ite_eq_right (fun h => hd (hiff.mp h))]

private theorem finrankAlong_towerSubstBar_comp_heckeAlphaBar_aux (L : Type*) [Field L]
    [Algebra ℚ L] (N : ℕ) [NeZero N] (ℓ ℓ' M : ℕ) [hl : Fact (Nat.Prime ℓ)]
    [hl' : Fact (Nat.Prime ℓ')] [NeZero M] (hM : M = N * ℓ * ℓ') (hne : ℓ ≠ ℓ') :
    AlgebraicCurve.finrankAlong L ((towerSubstBar L (N * ℓ') ℓ
        (dvd_of_eq_roof N ℓ ℓ' M hM).2).comp (heckeAlphaBar L N ℓ'))
      = AlgebraicCurve.finrankAlong L (heckeAlphaBar L N ℓ')
        * AlgebraicCurve.finrankAlong L (heckeBetaBar L N ℓ) := by
  refine Eq.trans (AlgebraicCurve.finrankAlong_comp (heckeAlphaBar L N ℓ')
    (towerSubstBar L (N * ℓ') ℓ (dvd_of_eq_roof N ℓ ℓ' M hM).2)) ?_
  exact congrArg
    (fun t => AlgebraicCurve.finrankAlong L (heckeAlphaBar L N ℓ') * t)
    (finrankAlong_towerSubstBar_roof L N ℓ ℓ' M hM hne)

theorem finrankAlong_towerSubstBar_comp_heckeAlphaBar (L : Type*) [Field L] [Algebra ℚ L]
    (N : ℕ) [NeZero N] (ℓ ℓ' M : ℕ) [hl : Fact (Nat.Prime ℓ)] [hl' : Fact (Nat.Prime ℓ')]
    [NeZero M] (hM : M = N * ℓ * ℓ') (hne : ℓ ≠ ℓ') :
    AlgebraicCurve.finrankAlong L ((towerSubstBar L (N * ℓ') ℓ (dvd_of_eq_roof N ℓ ℓ' M hM).2).comp
        (heckeAlphaBar L N ℓ'))
      = AlgebraicCurve.finrankAlong L (heckeAlphaBar L N ℓ')
        * AlgebraicCurve.finrankAlong L (heckeBetaBar L N ℓ) :=
  finrankAlong_towerSubstBar_comp_heckeAlphaBar_aux L N ℓ ℓ' M hM hne

end DiagonalDegree

section Roof

private theorem jqNModC_congr {L : Type*} [Field L] [Algebra ℚ L] {n m : ℕ} [NeZero n]
    [NeZero m] (h : n = m) : jqNModC L n = jqNModC L m := by
  subst h
  rfl

private theorem mem_range_towerInclBar_iff (L : Type*) [Field L] [Algebra ℚ L]
    {N M : ℕ} [NeZero N] [NeZero M] (h : N ∣ M)
    (x : laurentBaseChange L (modularFunctionFieldFull M)) :
    x ∈ Set.range (towerInclBar L h) ↔
      (x : LaurentSeries L) ∈ laurentBaseChange L (modularFunctionFieldFull N) := by
  constructor
  · rintro ⟨w, rfl⟩
    rw [coe_towerInclBar]
    exact w.2
  · intro hx
    exact ⟨⟨(x : LaurentSeries L), hx⟩, Subtype.ext (coe_towerInclBar L h _)⟩

private theorem laurentBaseChange_adjoin_pair (L : Type*) [Field L] [Algebra ℚ L]
    (M : ℕ) [NeZero M] (hgenQ : FunctionFieldGeneration M) :
    laurentBaseChange L (modularFunctionFieldFull M) =
      IntermediateField.adjoin L {jqModC L, jqNModC L M} := by
  rw [(functionFieldGeneration_iff_full_eq M).mp hgenQ, laurentBaseChange_modularFunctionField]
  rfl

theorem heckeRoof_adjoin_range_union_eq_top (L : Type*) [Field L] [Algebra ℚ L]
    (N ℓ ℓ' M : ℕ) [NeZero N] [NeZero ℓ] [NeZero ℓ'] [NeZero M]
    (hM : M = N * ℓ * ℓ') (hgenQ : FunctionFieldGeneration M)
    (data' : ModularPolynomialData ℓ') :
    Algebra.adjoin L
      (Set.range (towerSubstBar L (N * ℓ') ℓ (dvd_of_eq_roof N ℓ ℓ' M hM).2)
        ∪ Set.range (towerInclBar L (dvd_of_eq_roof N ℓ ℓ' M hM).1)) = ⊤ := by
  classical
  set h₁ : N * ℓ ∣ M := (dvd_of_eq_roof N ℓ ℓ' M hM).1 with hh₁
  set h₂ : N * ℓ' * ℓ ∣ M := (dvd_of_eq_roof N ℓ ℓ' M hM).2 with hh₂
  set A : Subalgebra L (laurentBaseChange L (modularFunctionFieldFull M)) :=
    Algebra.adjoin L
      (Set.range (towerSubstBar L (N * ℓ') ℓ h₂) ∪ Set.range (towerInclBar L h₁)) with hA

  have hmemC : ∀ (P d : ℕ) [NeZero P] [NeZero d], d ∣ P →
      jqNModC L d ∈ laurentBaseChange L (modularFunctionFieldFull P) := by
    intro P d _ _ hd
    rw [← coeffEmb_jqN]
    exact coeffEmb_mem_laurentBaseChange L (jqd_mem_full P hd)
  have hjqmem : ∀ (P : ℕ) [NeZero P],
      jqModC L ∈ laurentBaseChange L (modularFunctionFieldFull P) := by
    intro P _
    have h := hmemC P 1 (one_dvd P)
    rwa [jqNModC_one] at h
  have hNℓ'M : N * ℓ' ∣ M := ⟨ℓ, by rw [hM]; ring⟩

  set xM : laurentBaseChange L (modularFunctionFieldFull M) :=
    ⟨jqNModC L M, hmemC M M dvd_rfl⟩ with hxM
  have hxMsubst : xM ∈ Set.range (towerSubstBar L (N * ℓ') ℓ h₂) := by
    refine ⟨⟨jqNModC L (N * ℓ'), hmemC (N * ℓ') (N * ℓ') dvd_rfl⟩, Subtype.ext ?_⟩
    rw [coe_towerSubstBar]
    show qExpand L ℓ (jqNModC L (N * ℓ')) = jqNModC L M
    rw [jqNModC, qExpand_qExpand]
    show jqNModC L (ℓ * (N * ℓ')) = jqNModC L M
    exact jqNModC_congr (by rw [hM]; ring)

  set E₂s : IntermediateField L (LaurentSeries L) :=
    laurentBaseChange L (modularFunctionFieldFull (N * ℓ)) with hE₂s
  have hle : E₂s ≤ laurentBaseChange L (modularFunctionFieldFull M) :=
    laurentBaseChange_mono L (full_degeneracy_le h₁)

  have hunion : IntermediateField.adjoin L ((E₂s : Set (LaurentSeries L)) ∪ {jqNModC L M}) =
      laurentBaseChange L (modularFunctionFieldFull M) := by
    refine le_antisymm ?_ ?_
    · rw [IntermediateField.adjoin_le_iff]
      rintro y (hy | hy)
      · exact hle hy
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        exact hmemC M M dvd_rfl
    · rw [laurentBaseChange_adjoin_pair L M hgenQ]
      refine IntermediateField.adjoin.mono _ _ _ ?_
      rintro y (rfl | hy)
      · exact Set.mem_union_left _ (hjqmem (N * ℓ))
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        exact Set.mem_union_right _ rfl

  have hint : IsIntegral E₂s (jqNModC L M) := by
    have h := isIntegral_jqNModC_mul E₂s data' (N * ℓ) (hmemC (N * ℓ) (N * ℓ) dvd_rfl)
    rwa [jqNModC_congr (show N * ℓ * ℓ' = M from hM.symm)] at h

  have hring : Algebra.adjoin E₂s ({jqNModC L M} : Set (LaurentSeries L)) =
      (IntermediateField.adjoin E₂s ({jqNModC L M} : Set (LaurentSeries L))).toSubalgebra :=
    (IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic).symm
  have hcarrier : (IntermediateField.adjoin E₂s
      ({jqNModC L M} : Set (LaurentSeries L))).restrictScalars L =
      laurentBaseChange L (modularFunctionFieldFull M) :=
    (IntermediateField.restrictScalars_adjoin (F := L) (K := E₂s)
      (S := ({jqNModC L M} : Set (LaurentSeries L)))).trans hunion
  have hmemLFM : ∀ w, w ∈ Algebra.adjoin E₂s ({jqNModC L M} : Set (LaurentSeries L)) →
      w ∈ laurentBaseChange L (modularFunctionFieldFull M) := by
    intro w hw
    rw [hring] at hw
    rw [← hcarrier]
    exact hw

  have haux : ∀ y (hy : y ∈ Algebra.adjoin E₂s ({jqNModC L M} : Set (LaurentSeries L)))
      (hy' : y ∈ laurentBaseChange L (modularFunctionFieldFull M)),
      (⟨y, hy'⟩ : laurentBaseChange L (modularFunctionFieldFull M)) ∈ A := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem w hw =>
      intro hy'
      rw [Set.mem_singleton_iff] at hw
      subst hw
      have hxMeq :
          (⟨jqNModC L M, hy'⟩ : laurentBaseChange L (modularFunctionFieldFull M)) = xM :=
        Subtype.ext rfl
      rw [hxMeq]
      exact Algebra.subset_adjoin (Set.mem_union_left _ hxMsubst)
    | algebraMap e =>
      intro hy'
      exact Algebra.subset_adjoin (Set.mem_union_right _
        ((mem_range_towerInclBar_iff L h₁ ⟨_, hy'⟩).mpr e.2))
    | add u v hu hv ihu ihv =>
      intro hy'
      have hu' := hmemLFM u hu
      have hv' := hmemLFM v hv
      have hsplit : (⟨u + v, hy'⟩ : laurentBaseChange L (modularFunctionFieldFull M)) =
          ⟨u, hu'⟩ + ⟨v, hv'⟩ := rfl
      rw [hsplit]
      exact add_mem (ihu hu') (ihv hv')
    | mul u v hu hv ihu ihv =>
      intro hy'
      have hu' := hmemLFM u hu
      have hv' := hmemLFM v hv
      have hsplit : (⟨u * v, hy'⟩ : laurentBaseChange L (modularFunctionFieldFull M)) =
          ⟨u, hu'⟩ * ⟨v, hv'⟩ := rfl
      rw [hsplit]
      exact mul_mem (ihu hu') (ihv hv')

  rw [eq_top_iff]
  rintro ⟨z, hz⟩ -
  have hz' : z ∈ Algebra.adjoin E₂s ({jqNModC L M} : Set (LaurentSeries L)) := by
    rw [hring]
    have hmem : z ∈ (IntermediateField.adjoin E₂s
        ({jqNModC L M} : Set (LaurentSeries L))).restrictScalars L := by
      rw [hcarrier]
      exact hz
    exact hmem
  exact haux z hz' hz

end Roof

end ModularCurve

end
