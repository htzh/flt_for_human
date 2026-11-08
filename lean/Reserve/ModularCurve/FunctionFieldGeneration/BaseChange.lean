/-
  Base change for the level fields: the field degree is invariant under a coefficient extension.

  For `σ = coeffMap (algebraMap κ κ') : LaurentSeries κ →+* LaurentSeries κ'`, the relative degree
  `[κ'⟮j(q), j(q^d)⟯ : κ'⟮j(q)⟯]` equals `[κ⟮j(q), j(q^d)⟯ : κ⟮j(q)⟯]`: a level function field,
  defined over `κ`, keeps its degree over the base function field when the coefficients are
  extended. This is the one non-formal fact of the base-change dictionary ((5.2) of the any-field
  supplement); everything else in that dictionary is bookkeeping.

  ## What is here

  * `finrank_eq_relfinrank_restrictScalars` — the unconditional conversion between the
    `Module.finrank` spelling (`degreeAt`, `PkgAt`) and `IntermediateField.relfinrank`, which is what
    makes the tower argument possible: `Module.finrank ↥A ↥B` does not exist for two `κ`-based
    intermediate fields, `relfinrank` does.
  * `coeffMapAlg`, `constField`, `constEquiv`, `baseSigma`/`levelSigma`, the linear-disjointness
    family `linearDisjoint_const_map`/`_levelSigma`/`_baseSigma` (the constants `κ'` are linearly
    disjoint from every intermediate field of `LaurentSeries κ`: the coefficient separation,
    comparing `HahnSeries.coeff`), and `relfinrank_sup_const`: adjoining the constants multiplies
    the relative degree by `[κ' : κ]`.
  * the adjoin identifications `levelSeries_coeffMap`, `baseSigma_eq_adjoin`, `levelSigma_eq_adjoin`,
    `toSubfield_baseField_sigma`, `toSubfield_levelField_sigma`, `toSubfield_sup_baseSigma`,
    `toSubfield_sup_levelSigma`, `relfinrank_sigma_eq_sup`.
  * `finrank_levelField_coeffMap` — the theorem — and `degreeAt_coeffMap`, its `degreeAt` corollary:
    the package's degree clause transports along the coefficient extension.

  ## Why it is on the shelf

  Nothing in the port needs it. The slot product's hypothesis is the *source* package
  (`PkgAt jg M`, a fact about the `j`-series over `κ`), and the pushed minimal polynomial's degree is
  `ψ(M)` by `Monic.natDegree_map`, so no base-change degree fact appears anywhere in the ported
  proof. This module is what a *one-field* restatement of the slot product would consume — the
  optional collapse, deliberately not taken. Plan and decision:
  `lean/topics/functionFieldGeneration/TOPIC-ffg-refactor.md` §6.

  ## Tier

  No `spec-pin:` wire: every declaration is the port's own (the pin has no base-change statement),
  so a wire would diff nothing. Registered by `spec/unwired_register.py`.

  ## Traps (measured when this was written)

  * `baseField (σ jg)` is a **`κ'`-based** `IntermediateField` — `baseField`'s implicit `κ` unifies
    with the argument's coefficient field — so `C ⊔ baseSigma jg = baseField (σ jg)` is *not* an
    `IntermediateField` equality; the identification must happen on `Subfield`s, which is what
    `relfinrank_sigma_eq_sup` does.
  * `Module.finrank ↥A ↥B` for two `κ`-based intermediate fields does not elaborate (mathlib has
    `Algebra ↥S ↥T` only for `T : IntermediateField ↥S L`), so the tower law runs on `relfinrank`;
    and `relfinrank_map_map` applies only on the `κ`-based side, hence the `restrictScalars κ`.
  * `[FiniteDimensional κ κ']` is essential to this route: it is spent only through
    `Module.finrank_pos` in the cancellation, and with `[κ' : κ] = 0` the two tower equations carry
    no information.
-/
import Mathlib.FieldTheory.Relrank
import Mathlib.FieldTheory.LinearDisjoint
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Generic.LevelPackage

set_option autoImplicit false
noncomputable section
open Polynomial HahnSeries IntermediateField Module
open scoped IntermediateField

namespace ModularCurve

variable {κ κ' : Type*} [Field κ] [Field κ'] [Algebra κ κ']

theorem algebraMap_laurentSeries_eq_single' (c : κ) :
    algebraMap κ (LaurentSeries κ') c = HahnSeries.single (0:ℤ) (algebraMap κ κ' c) := by
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, HahnSeries.ofPowerSeries_C]
  rfl

theorem coeffMap_algebraMap_const (c : κ) :
    coeffMap (algebraMap κ κ') (algebraMap κ (LaurentSeries κ) c)
      = algebraMap κ (LaurentSeries κ') c := by
  rw [algebraMap_laurentSeries_eq_single κ c, algebraMap_laurentSeries_eq_single' (κ' := κ') c,
    coeffMap_single]

/-- The coefficient change `algebraMap κ κ'` extended coefficientwise, as a `κ`-algebra map. -/
def coeffMapAlg : LaurentSeries κ →ₐ[κ] LaurentSeries κ' where
  __ := coeffMap (algebraMap κ κ')
  commutes' c := coeffMap_algebraMap_const c

@[simp] theorem coeffMapAlg_apply (x : LaurentSeries κ) :
    coeffMapAlg x = coeffMap (algebraMap κ κ') x := rfl

theorem coeffMap_sum_mul_single_eq_zero {ι : Type*} {b : ι → κ'}
    (hb : LinearIndependent κ b) (s : Finset ι) {y : ι → LaurentSeries κ}
    (h : ∑ i ∈ s, coeffMap (algebraMap κ κ') (y i) * HahnSeries.single (0 : ℤ) (b i) = 0) :
    ∀ i ∈ s, y i = 0 := by
  intro i hi
  ext n
  have hcoe : ∑ j ∈ s, algebraMap κ κ' ((y j).coeff n) * b j = 0 := by
    have h1 := congrArg (fun z : LaurentSeries κ' => z.coeff n) h
    simpa [HahnSeries.coeff_mul_single_zero, HahnSeries.coeff_sum] using h1
  have hli : ∑ j ∈ s, ((y j).coeff n) • b j = 0 := by
    simpa [Algebra.smul_def] using hcoe
  exact linearIndependent_iff'.mp hb s (fun j => (y j).coeff n) hli i hi

/-- **Independence of `κ'`-constants over the `σ`-image of a subfield of `LaurentSeries κ`.** -/
theorem linearIndependent_single_const_map (K : IntermediateField κ (LaurentSeries κ))
    {ι : Type*} {b : ι → κ'} (hb : LinearIndependent κ b) :
    LinearIndependent ↥(K.map (coeffMapAlg (κ := κ) (κ' := κ')))
      (fun i => (HahnSeries.single (0:ℤ) (b i) : LaurentSeries κ')) := by
  classical
  rw [linearIndependent_iff'] at ⊢
  intro s g hg i hi
  set e : ↥K ≃ₐ[κ] ↥(K.map (coeffMapAlg (κ := κ) (κ' := κ'))) :=
    IntermediateField.equivMap K coeffMapAlg with he
  have hval : ∀ z : ↥K, ((e z : ↥(K.map coeffMapAlg)) : LaurentSeries κ')
      = coeffMap (algebraMap κ κ') (z : LaurentSeries κ) := fun z => rfl
  have hrel : ∑ j ∈ s, coeffMap (algebraMap κ κ') ((e.symm (g j) : ↥K) : LaurentSeries κ)
      * HahnSeries.single (0:ℤ) (b j) = 0 := by
    rw [← hg]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, IntermediateField.algebraMap_apply]
    congr 1
    rw [← hval, AlgEquiv.apply_symm_apply]
  have hzero := coeffMap_sum_mul_single_eq_zero hb s hrel i hi
  have hgj : g i = 0 := by
    apply e.symm.injective
    rw [map_zero]
    exact Subtype.ext hzero
  exact hgj


/-- The constants `κ'`, as a `κ`-algebra map into `LaurentSeries κ'`. -/
def constAlgHom : κ' →ₐ[κ] LaurentSeries κ' where
  __ := algebraMap κ' (LaurentSeries κ')
  commutes' c := by
    show algebraMap κ' (LaurentSeries κ') (algebraMap κ κ' c)
      = algebraMap κ (LaurentSeries κ') c
    rw [algebraMap_laurentSeries_eq_single (L := κ') (algebraMap κ κ' c),
      algebraMap_laurentSeries_eq_single' (κ' := κ') c]

/-- The field `κ'` of constants, viewed as an intermediate field of `LaurentSeries κ'` over `κ`. -/
noncomputable def constField : IntermediateField κ (LaurentSeries κ') :=
  IntermediateField.map (constAlgHom (κ := κ) (κ' := κ')) ⊤

noncomputable def constEquiv : κ' ≃ₐ[κ] ↥(constField (κ := κ) (κ' := κ')) :=
  (IntermediateField.topEquiv (F := κ) (E := κ')).symm.trans
    (IntermediateField.equivMap (⊤ : IntermediateField κ κ') (constAlgHom (κ := κ) (κ' := κ')))

theorem constEquiv_coe (c : κ') :
    ((constEquiv (κ := κ) (κ' := κ') c : ↥(constField (κ := κ) (κ' := κ'))) : LaurentSeries κ')
      = algebraMap κ' (LaurentSeries κ') c := rfl

section Level
variable (jg : LaurentSeries κ) (d : ℕ) [NeZero d]

theorem baseField_le_levelField :
    baseField jg ≤ IntermediateField.restrictScalars κ (levelField jg d) := by
  change IntermediateField.adjoin κ ({jg} : Set (LaurentSeries κ)) ≤ _
  rw [IntermediateField.adjoin_le_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  refine (IntermediateField.mem_restrictScalars κ).mpr ?_
  show y ∈ (levelField jg d : Set (LaurentSeries κ))
  rw [hy, coe_adjoin_baseField]
  exact IntermediateField.subset_adjoin κ _ (Set.mem_union_left _ rfl)

noncomputable def baseSigma : IntermediateField κ (LaurentSeries κ') :=
  IntermediateField.map (coeffMapAlg (κ := κ) (κ' := κ')) (baseField jg)

noncomputable def levelSigma : IntermediateField κ (LaurentSeries κ') :=
  IntermediateField.map (coeffMapAlg (κ := κ) (κ' := κ'))
    (IntermediateField.restrictScalars κ (levelField jg d))

theorem baseSigma_le_levelSigma :
    baseSigma (κ := κ) (κ' := κ') jg ≤ levelSigma (κ := κ) (κ' := κ') jg d :=
  IntermediateField.map_mono _ (baseField_le_levelField jg d)

end Level

section Disjoint
variable (jg : LaurentSeries κ) (d : ℕ) [NeZero d]

/-- **Linear disjointness.**  The constants `κ'` (viewed inside `LaurentSeries κ'` over `κ`) are
linearly disjoint from the `σ`-image of any intermediate field of `LaurentSeries κ`. -/
theorem linearDisjoint_const_map (K : IntermediateField κ (LaurentSeries κ)) :
    (constField (κ := κ) (κ' := κ')).LinearDisjoint
      ↥(IntermediateField.map (coeffMapAlg (κ := κ) (κ' := κ')) K) := by
  classical
  let b : Basis (Module.Free.ChooseBasisIndex κ κ') κ κ' := Module.Free.chooseBasis κ κ'
  let a : Basis (Module.Free.ChooseBasisIndex κ κ') κ ↥(constField (κ := κ) (κ' := κ')) :=
    b.map (constEquiv (κ := κ) (κ' := κ')).toLinearEquiv
  refine IntermediateField.LinearDisjoint.of_basis_left a ?_
  have hfam : ⇑(constField (κ := κ) (κ' := κ')).val ∘ ⇑a
      = fun i => (HahnSeries.single (0:ℤ) (b i) : LaurentSeries κ') := by
    funext i
    show ((constEquiv (κ := κ) (κ' := κ') (b i) :
      ↥(constField (κ := κ) (κ' := κ'))) : LaurentSeries κ') = _
    rw [constEquiv_coe, algebraMap_laurentSeries_eq_single]
  rw [hfam]
  exact linearIndependent_single_const_map K b.linearIndependent

theorem linearDisjoint_const_levelSigma :
    (constField (κ := κ) (κ' := κ')).LinearDisjoint ↥(levelSigma (κ := κ) (κ' := κ') jg d) :=
  linearDisjoint_const_map (IntermediateField.restrictScalars κ (levelField jg d))

theorem linearDisjoint_const_baseSigma :
    (constField (κ := κ) (κ' := κ')).LinearDisjoint ↥(baseSigma (κ := κ) (κ' := κ') jg) :=
  linearDisjoint_const_map (baseField jg)

end Disjoint

section Rank
variable (jg : LaurentSeries κ) (d : ℕ) [NeZero d] [FiniteDimensional κ κ']

local instance instFinConst : FiniteDimensional κ ↥(constField (κ := κ) (κ' := κ')) :=
  (constEquiv (κ := κ) (κ' := κ')).toLinearEquiv.finiteDimensional

local instance instAlgConst : Algebra.IsAlgebraic κ ↥(constField (κ := κ) (κ' := κ')) :=
  Algebra.IsAlgebraic.of_finite κ _

/-- `[κ'·σ(K) : σ(K)] = [κ' : κ]`. -/
theorem rank_adjoin_const (K : IntermediateField κ (LaurentSeries κ)) :
    Module.rank
      ↥(IntermediateField.map (coeffMapAlg (κ := κ) (κ' := κ')) K)
      ↥(IntermediateField.adjoin
        ↥(IntermediateField.map (coeffMapAlg (κ := κ) (κ' := κ')) K)
        (↑(constField (κ := κ) (κ' := κ')) : Set (LaurentSeries κ')))
      = Module.rank κ ↥(constField (κ := κ) (κ' := κ')) :=
  (linearDisjoint_const_map K).adjoin_rank_eq_rank_left_of_isAlgebraic (Or.inl inferInstance)

theorem finrank_adjoin_const (K : IntermediateField κ (LaurentSeries κ)) :
    Module.finrank
      ↥(IntermediateField.map (coeffMapAlg (κ := κ) (κ' := κ')) K)
      ↥(IntermediateField.adjoin
        ↥(IntermediateField.map (coeffMapAlg (κ := κ) (κ' := κ')) K)
        (↑(constField (κ := κ) (κ' := κ')) : Set (LaurentSeries κ')))
      = Module.finrank κ κ' := by
  rw [Module.finrank, rank_adjoin_const]
  exact (constEquiv (κ := κ) (κ' := κ')).toLinearEquiv.finrank_eq.symm

/-- Adjoining the constants multiplies the relative degree by `[κ' : κ]`. -/
theorem relfinrank_sup_const (K : IntermediateField κ (LaurentSeries κ)) :
    IntermediateField.relfinrank
      (IntermediateField.map (coeffMapAlg (κ := κ) (κ' := κ')) K)
      (constField (κ := κ) (κ' := κ') ⊔
        IntermediateField.map (coeffMapAlg (κ := κ) (κ' := κ')) K)
      = Module.finrank κ κ' := by
  have hle : IntermediateField.map (coeffMapAlg (κ := κ) (κ' := κ')) K
      ≤ (constField (κ := κ) (κ' := κ') ⊔
        IntermediateField.map (coeffMapAlg (κ := κ) (κ' := κ')) K :
          IntermediateField κ (LaurentSeries κ')) := le_sup_right
  rw [IntermediateField.relfinrank_eq_finrank_of_le hle]
  have hSet : (IntermediateField.adjoin
        ↥(IntermediateField.map (coeffMapAlg (κ := κ) (κ' := κ')) K)
        (↑(constField (κ := κ) (κ' := κ')) : Set (LaurentSeries κ'))
        : Set (LaurentSeries κ'))
      = (constField (κ := κ) (κ' := κ') ⊔
        IntermediateField.map (coeffMapAlg (κ := κ) (κ' := κ')) K :
          IntermediateField κ (LaurentSeries κ')) := by
    rw [← coe_restrictScalars κ
      (E := IntermediateField.adjoin
        ↥(IntermediateField.map (coeffMapAlg (κ := κ) (κ' := κ')) K)
        (↑(constField (κ := κ) (κ' := κ')) : Set (LaurentSeries κ')))]
    rw [restrictScalars_adjoin]
    rw [IntermediateField.sup_def, Set.union_comm]
  have hEq : IntermediateField.extendScalars hle
      = IntermediateField.adjoin
        ↥(IntermediateField.map (coeffMapAlg (κ := κ) (κ' := κ')) K)
        (↑(constField (κ := κ) (κ' := κ')) : Set (LaurentSeries κ')) := by
    refine SetLike.ext fun x => ?_
    change x ∈ (IntermediateField.extendScalars hle : Set (LaurentSeries κ'))
      ↔ x ∈ (IntermediateField.adjoin
        ↥(IntermediateField.map (coeffMapAlg (κ := κ) (κ' := κ')) K)
        (↑(constField (κ := κ) (κ' := κ')) : Set (LaurentSeries κ'))
        : Set (LaurentSeries κ'))
    rw [hSet]
    rfl
  rw [hEq]
  exact finrank_adjoin_const K

end Rank

section Identify
variable (jg : LaurentSeries κ) (d : ℕ) [NeZero d]

theorem coe_restrictScalars_levelField :
    (IntermediateField.restrictScalars κ (levelField jg d) : Set (LaurentSeries κ))
      = (IntermediateField.adjoin κ ({jg} ∪ {levelSeries jg d} : Set (LaurentSeries κ))
        : Set (LaurentSeries κ)) := by
  rw [coe_restrictScalars κ, ← coe_adjoin_baseField]

theorem restrictScalars_levelField :
    IntermediateField.restrictScalars κ (levelField jg d)
      = IntermediateField.adjoin κ ({jg} ∪ {levelSeries jg d} : Set (LaurentSeries κ)) :=
  SetLike.ext fun _ => iff_of_eq (congrArg (fun T : Set (LaurentSeries κ) => _ ∈ T)
    (coe_restrictScalars_levelField jg d))

theorem levelSeries_coeffMap :
    levelSeries ((coeffMap (algebraMap κ κ')) jg) d
      = (coeffMap (algebraMap κ κ')) (levelSeries jg d) :=
  (coeffMap_qExpand (algebraMap κ κ') d jg).symm

theorem baseSigma_eq_adjoin :
    baseSigma (κ := κ) (κ' := κ') jg
      = IntermediateField.adjoin κ ({coeffMapAlg (κ := κ) (κ' := κ') jg}
          : Set (LaurentSeries κ')) := by
  rw [baseSigma, baseField, IntermediateField.adjoin_map]
  simp

theorem levelSigma_eq_adjoin :
    levelSigma (κ := κ) (κ' := κ') jg d
      = IntermediateField.adjoin κ
          ({coeffMapAlg (κ := κ) (κ' := κ') jg,
            levelSeries (coeffMapAlg (κ := κ) (κ' := κ') jg) d}
            : Set (LaurentSeries κ')) := by
  rw [levelSigma, restrictScalars_levelField, IntermediateField.adjoin_map]
  simp only [Set.image_union, Set.image_singleton]
  rw [show levelSeries (coeffMapAlg (κ := κ) (κ' := κ') jg) d
      = coeffMapAlg (κ := κ) (κ' := κ') (levelSeries jg d) from
        (coeffMap_qExpand (algebraMap κ κ') d jg).symm]
  simp [Set.pair_comm]

end Identify




section Main
-- `[FiniteDimensional κ κ']` is deliberately *not* a variable of this section: nothing here uses it,
-- and including it would silently add an unused instance argument to every declaration below.
variable (jg : LaurentSeries κ) (d : ℕ) [NeZero d]

theorem algebraMap_eq_algebraMap' (c : κ) :
    algebraMap κ (LaurentSeries κ') c = algebraMap κ' (LaurentSeries κ') (algebraMap κ κ' c) := by
  rw [algebraMap_laurentSeries_eq_single' (κ' := κ') c,
    algebraMap_laurentSeries_eq_single (L := κ') (algebraMap κ κ' c)]

theorem range_algebraMap_subset :
    Set.range (algebraMap κ (LaurentSeries κ'))
      ⊆ Set.range (algebraMap κ' (LaurentSeries κ')) := by
  rintro _ ⟨c, rfl⟩
  exact ⟨algebraMap κ κ' c, (algebraMap_eq_algebraMap' (κ := κ) (κ' := κ') c).symm⟩

theorem coe_top_intermediateField (F : Type*) [Field F] (E : Type*) [Field E] [Algebra F E] :
    (↑(⊤ : IntermediateField F E) : Set E) = Set.univ := rfl

theorem constField_eq_adjoin :
    constField (κ := κ) (κ' := κ')
      = IntermediateField.adjoin κ
          (Set.range (algebraMap κ' (LaurentSeries κ'))) := by
  rw [constField, ← IntermediateField.adjoin_self κ (⊤ : IntermediateField κ κ'),
    IntermediateField.adjoin_map, IntermediateField.coe_top, Set.image_univ]
  rfl

theorem toSubfield_constField :
    (constField (κ := κ) (κ' := κ')).toSubfield
      = Subfield.closure (Set.range (algebraMap κ (LaurentSeries κ'))
          ∪ Set.range (algebraMap κ' (LaurentSeries κ'))) := by
  rw [constField_eq_adjoin, IntermediateField.adjoin_toSubfield]

theorem toSubfield_sup_adjoin (T : Set (LaurentSeries κ')) :
    (constField (κ := κ) (κ' := κ') ⊔ IntermediateField.adjoin κ T).toSubfield
      = Subfield.closure (Set.range (algebraMap κ' (LaurentSeries κ')) ∪ T) := by
  have hU : (Set.range (algebraMap κ (LaurentSeries κ'))
        ∪ Set.range (algebraMap κ' (LaurentSeries κ')) ∪ T)
      = (Set.range (algebraMap κ' (LaurentSeries κ')) ∪ T) := by
    ext x
    simp only [Set.mem_union]
    constructor
    · rintro ((hx | hx) | hx)
      · exact Or.inl (range_algebraMap_subset hx)
      · exact Or.inl hx
      · exact Or.inr hx
    · rintro (hx | hx)
      · exact Or.inl (Or.inr hx)
      · exact Or.inr hx
  rw [IntermediateField.sup_toSubfield, toSubfield_constField, IntermediateField.adjoin_toSubfield,
    ← Subfield.closure_union]
  rw [show (Set.range (algebraMap κ (LaurentSeries κ'))
        ∪ Set.range (algebraMap κ' (LaurentSeries κ')))
      ∪ (Set.range (algebraMap κ (LaurentSeries κ')) ∪ T)
      = (Set.range (algebraMap κ (LaurentSeries κ'))
        ∪ Set.range (algebraMap κ' (LaurentSeries κ')) ∪ T) from by
    ext x
    simp only [Set.mem_union]
    tauto]
  rw [hU]

theorem closure_insert_closure (X : Set (LaurentSeries κ')) (y : LaurentSeries κ') :
    Subfield.closure (Subfield.closure X ∪ {y}) = Subfield.closure (X ∪ {y}) := by
  refine le_antisymm ?_ ?_
  · refine Subfield.closure_le.mpr (Set.union_subset ?_ ?_)
    · exact fun x hx => Subfield.closure_mono Set.subset_union_left hx
    · exact fun x hx => Subfield.subset_closure (Set.mem_union_right _ hx)
  · refine Subfield.closure_le.mpr (Set.union_subset ?_ ?_)
    · exact fun x hx => Subfield.subset_closure (Set.mem_union_left _ (Subfield.subset_closure hx))
    · exact fun x hx => Subfield.subset_closure (Set.mem_union_right _ hx)

theorem toSubfield_baseField_sigma :
    (baseField (coeffMapAlg (κ := κ) (κ' := κ') jg)).toSubfield
      = Subfield.closure (Set.range (algebraMap κ' (LaurentSeries κ'))
          ∪ {coeffMapAlg (κ := κ) (κ' := κ') jg}) := by
  rw [baseField, IntermediateField.adjoin_toSubfield]

theorem toSubfield_levelField_sigma :
    (levelField (coeffMapAlg (κ := κ) (κ' := κ') jg) d).toSubfield
      = Subfield.closure (Set.range (algebraMap κ' (LaurentSeries κ'))
          ∪ {coeffMapAlg (κ := κ) (κ' := κ') jg} ∪ {levelSeries (coeffMapAlg (κ := κ) (κ' := κ') jg) d}) := by
  have hrange : Set.range (algebraMap ↥(baseField (coeffMapAlg (κ := κ) (κ' := κ') jg))
      (LaurentSeries κ'))
      = (baseField (coeffMapAlg (κ := κ) (κ' := κ') jg) : Set (LaurentSeries κ')) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩; exact y.2
    · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
  have hsub : ((baseField (coeffMapAlg (κ := κ) (κ' := κ') jg)).toSubfield : Subfield (LaurentSeries κ'))
      = Subfield.closure (Set.range (algebraMap κ' (LaurentSeries κ'))
          ∪ {coeffMapAlg (κ := κ) (κ' := κ') jg}) :=
    toSubfield_baseField_sigma (κ := κ) (κ' := κ') (jg := jg)
  have hB : (↑(baseField (coeffMapAlg (κ := κ) (κ' := κ') jg)) : Set (LaurentSeries κ'))
      = (Subfield.closure (Set.range (algebraMap κ' (LaurentSeries κ'))
          ∪ {coeffMapAlg (κ := κ) (κ' := κ') jg}) : Set (LaurentSeries κ')) := by
    rw [← IntermediateField.coe_toSubfield (baseField (coeffMapAlg (κ := κ) (κ' := κ') jg)),
      hsub]
  rw [levelField, IntermediateField.adjoin_toSubfield, hrange, hB, closure_insert_closure]

theorem toSubfield_sup_baseSigma :
    (constField (κ := κ) (κ' := κ') ⊔ baseSigma (κ := κ) (κ' := κ') jg).toSubfield
      = (baseField (coeffMapAlg (κ := κ) (κ' := κ') jg)).toSubfield := by
  rw [baseSigma_eq_adjoin, toSubfield_sup_adjoin, toSubfield_baseField_sigma]

theorem toSubfield_sup_levelSigma :
    (constField (κ := κ) (κ' := κ') ⊔ levelSigma (κ := κ) (κ' := κ') jg d).toSubfield
      = (levelField (coeffMapAlg (κ := κ) (κ' := κ') jg) d).toSubfield := by
  rw [levelSigma_eq_adjoin, toSubfield_sup_adjoin, toSubfield_levelField_sigma,
    Set.insert_eq, Set.union_assoc]

end Main





end ModularCurve

/-! ## Base change for level fields — invariance of the level degree

The degree `[levelField jg d : baseField jg]` is unchanged by the coefficient change
`σ = coeffMapAlg = coeffMap (algebraMap κ κ')` from `LaurentSeries κ` to `LaurentSeries κ'`.
The proof runs through `IntermediateField.relfinrank`, which — unlike `Module.finrank` — is
defined for any pair of intermediate fields and is multiplicative with no finiteness hypotheses,
so nothing about algebraicity or finiteness of `levelSeries jg d` is needed.
-/

/-- **Bridge between `Module.finrank` and `relfinrank`.**  For `K : IntermediateField F L` and
`E : IntermediateField ↥K L`, the degree of `E` over `K` is the relative degree of
`E.restrictScalars F` over `K`.  This is the unconditional conversion between the
`Module.finrank` spelling used by `PkgAt`/`degreeAt` and the `relfinrank` spelling on which the
tower argument runs. -/
theorem finrank_eq_relfinrank_restrictScalars {F L : Type*} [Field F] [Field L] [Algebra F L]
    (K : IntermediateField F L) (E : IntermediateField ↥K L) :
    Module.finrank ↥K ↥E = IntermediateField.relfinrank K (E.restrictScalars F) := by
  rw [IntermediateField.relfinrank_eq_finrank_of_le
    (show K ≤ E.restrictScalars F from fun x hx => E.algebraMap_mem ⟨x, hx⟩)]
  exact LinearEquiv.finrank_eq
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun _ _ => Subtype.ext rfl
      map_smul' := fun _ _ => Subtype.ext rfl
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }

namespace ModularCurve

variable {κ κ' : Type*} [Field κ] [Field κ'] [Algebra κ κ']

section Final

variable (jg : LaurentSeries κ) (d : ℕ) [NeZero d]

/-- **`relfinrank` is insensitive to the base field.**  The degree of the image level field over
the image base field (both read over `κ'`) equals the degree of `κ' · F_d` over `κ' · F_0` (both
read over `κ`).  `relfinrank` is defined on the underlying `Subfield`s, so these can be compared
even though the level fields live over `κ'` while the `σ`-images live over `κ`. -/
theorem relfinrank_sigma_eq_sup :
    IntermediateField.relfinrank (baseField (coeffMapAlg (κ := κ) (κ' := κ') jg))
        ((levelField (coeffMapAlg (κ := κ) (κ' := κ') jg) d).restrictScalars κ')
      = IntermediateField.relfinrank
          (constField (κ := κ) (κ' := κ') ⊔ baseSigma (κ := κ) (κ' := κ') jg)
          (constField (κ := κ) (κ' := κ') ⊔ levelSigma (κ := κ) (κ' := κ') jg d) := by
  change Subfield.relfinrank
      (baseField (coeffMapAlg (κ := κ) (κ' := κ') jg)).toSubfield
      ((levelField (coeffMapAlg (κ := κ) (κ' := κ') jg) d).restrictScalars κ').toSubfield
    = Subfield.relfinrank
      (constField (κ := κ) (κ' := κ') ⊔ baseSigma (κ := κ) (κ' := κ') jg).toSubfield
      (constField (κ := κ) (κ' := κ') ⊔ levelSigma (κ := κ) (κ' := κ') jg d).toSubfield
  rw [IntermediateField.restrictScalars_toSubfield,
    ← toSubfield_sup_baseSigma (κ := κ) (κ' := κ') (jg := jg),
    ← toSubfield_sup_levelSigma (κ := κ) (κ' := κ') (jg := jg) (d := d)]

end Final

section Degree

variable (jg : LaurentSeries κ) (d : ℕ) [NeZero d] [FiniteDimensional κ κ']

/-- **Invariance of the level degree under coefficient change.**  The degree of the level-`d`
field over the base field is unchanged when the j-series is pushed forward along
`algebraMap κ κ'`, for an arbitrary finite extension `κ' / κ`. -/
theorem finrank_levelField_coeffMap :
    Module.finrank (baseField (coeffMap (algebraMap κ κ') jg))
        (levelField (coeffMap (algebraMap κ κ') jg) d)
      = Module.finrank (baseField jg) (levelField jg d) := by
  have hσ : coeffMap (algebraMap κ κ') jg = coeffMapAlg (κ := κ) (κ' := κ') jg := rfl
  rw [hσ]
  -- convert both sides to relative degrees over `κ'` resp. `κ`
  rw [finrank_eq_relfinrank_restrictScalars (F := κ') (L := LaurentSeries κ')
      (baseField (coeffMapAlg (κ := κ) (κ' := κ') jg))
      (levelField (coeffMapAlg (κ := κ) (κ' := κ') jg) d),
    finrank_eq_relfinrank_restrictScalars (F := κ) (L := LaurentSeries κ)
      (baseField jg) (levelField jg d)]
  -- the `κ`-picture is the `σ`-image of the un-`σ`-ed one, by `relfinrank_map_map`
  have hmap : IntermediateField.relfinrank (baseField jg) ((levelField jg d).restrictScalars κ)
      = IntermediateField.relfinrank (baseSigma (κ := κ) (κ' := κ') jg)
          (levelSigma (κ := κ) (κ' := κ') jg d) :=
    (IntermediateField.relfinrank_map_map (baseField jg) ((levelField jg d).restrictScalars κ)
      (coeffMapAlg (κ := κ) (κ' := κ'))).symm
  rw [relfinrank_sigma_eq_sup (κ := κ) (κ' := κ') (jg := jg) (d := d), hmap]
  -- two tower laws and two applications of `relfinrank_sup_const`, then cancel `[κ' : κ] > 0`
  have h1 : IntermediateField.relfinrank (baseSigma (κ := κ) (κ' := κ') jg)
        (constField (κ := κ) (κ' := κ') ⊔ baseSigma (κ := κ) (κ' := κ') jg)
      * IntermediateField.relfinrank
          (constField (κ := κ) (κ' := κ') ⊔ baseSigma (κ := κ) (κ' := κ') jg)
          (constField (κ := κ) (κ' := κ') ⊔ levelSigma (κ := κ) (κ' := κ') jg d)
      = IntermediateField.relfinrank (baseSigma (κ := κ) (κ' := κ') jg)
          (constField (κ := κ) (κ' := κ') ⊔ levelSigma (κ := κ) (κ' := κ') jg d) :=
    IntermediateField.relfinrank_mul_relfinrank le_sup_right
      (sup_le_sup le_rfl (baseSigma_le_levelSigma (κ := κ) (κ' := κ') jg d))
  have h2 : IntermediateField.relfinrank (baseSigma (κ := κ) (κ' := κ') jg)
        (levelSigma (κ := κ) (κ' := κ') jg d)
      * IntermediateField.relfinrank (levelSigma (κ := κ) (κ' := κ') jg d)
          (constField (κ := κ) (κ' := κ') ⊔ levelSigma (κ := κ) (κ' := κ') jg d)
      = IntermediateField.relfinrank (baseSigma (κ := κ) (κ' := κ') jg)
          (constField (κ := κ) (κ' := κ') ⊔ levelSigma (κ := κ) (κ' := κ') jg d) :=
    IntermediateField.relfinrank_mul_relfinrank
      (baseSigma_le_levelSigma (κ := κ) (κ' := κ') jg d) le_sup_right
  have hn0 : IntermediateField.relfinrank (baseSigma (κ := κ) (κ' := κ') jg)
        (constField (κ := κ) (κ' := κ') ⊔ baseSigma (κ := κ) (κ' := κ') jg)
      = Module.finrank κ κ' :=
    relfinrank_sup_const (K := baseField jg)
  have hnd : IntermediateField.relfinrank (levelSigma (κ := κ) (κ' := κ') jg d)
        (constField (κ := κ) (κ' := κ') ⊔ levelSigma (κ := κ) (κ' := κ') jg d)
      = Module.finrank κ κ' :=
    relfinrank_sup_const (K := IntermediateField.restrictScalars κ (levelField jg d))
  have hn : 0 < Module.finrank κ κ' := Module.finrank_pos
  refine Nat.mul_left_cancel hn ?_
  calc Module.finrank κ κ'
        * (constField ⊔ baseSigma jg).relfinrank (constField ⊔ levelSigma jg d)
      = (baseSigma jg).relfinrank (constField ⊔ baseSigma jg)
          * (constField ⊔ baseSigma jg).relfinrank (constField ⊔ levelSigma jg d) := by
        rw [hn0]
    _ = (baseSigma jg).relfinrank (constField ⊔ levelSigma jg d) := h1
    _ = (baseSigma jg).relfinrank (levelSigma jg d)
          * (levelSigma jg d).relfinrank (constField ⊔ levelSigma jg d) := h2.symm
    _ = (baseSigma jg).relfinrank (levelSigma jg d) * Module.finrank κ κ' := by rw [hnd]
    _ = Module.finrank κ κ' * (baseSigma jg).relfinrank (levelSigma jg d) := Nat.mul_comm _ _

/-- **The degree clause `degreeAt` transfers along the coefficient change**, in both directions:
`PkgAt`/`degreeAt` for the image series is equivalent to `degreeAt` for the original one. -/
theorem degreeAt_coeffMap :
    degreeAt ((coeffMap (algebraMap κ κ')) jg) d ↔ degreeAt jg d := by
  simp only [degreeAt, finrank_levelField_coeffMap]

end Degree

end ModularCurve
