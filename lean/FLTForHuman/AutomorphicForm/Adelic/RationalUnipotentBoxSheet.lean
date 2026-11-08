/-
  The box sheets: fundamental domains for the rational centre-unipotent and torus-unipotent
  subgroups.

  `rationalTorusUnipotentHaar` was defined as the countable sum of the translates of the unipotent
  Haar measure over `Kˣ × Kˣ`; this module produces the set that makes that sum a *fundamental
  domain* statement. With

  `T = toAdelicUnipotent '' adelicBox`  (the box, read inside the unipotent subgroup),

  and `B = (borelSubgroup K).map (globalPoints (𝓞 K) K)` the image of the Borel subgroup:

  * `isFundamentalDomain_boxSheet_rationalTorusUnipotent`: `B ≤ rationalTorusUnipotent K`, `B` is
    countable, `T` is measurable, `T` is a fundamental domain for
    `B.subgroupOf (rationalTorusUnipotent K)` under `rationalTorusUnipotentHaar`, and integration
    over `T` is integration over the box against the normalised additive Haar measure;
  * `isFundamentalDomain_boxSheet_rationalCentreUnipotent`: the same with the torus `B` replaced by
    the centre-unipotent `P = rationalCentre K ⊔ (unipotentGL2Hom).range` and with
    `rationalCentreUnipotentHaar`.

  The "box sheet" is the set that turns the abstract sum-of-translates definition into a concrete
  domain: `𝔸_K / 𝓞 K` is the box, and the rational points act through the Borel.

  `existsUnique_diagOne_inv_mul_mem_scalar_sup_unipotent_of_mem_borelSubgroup` is the dictionary
  lemma both statements rest on: a Borel element has a **unique** diagonal part modulo the scalars
  and the unipotent radical — the Bruhat decomposition of the Borel.

  Transcribed from the pin's three `S_` files and their `Theorems/` wrappers (pinned `aa2d8b3`,
  440 + 340 + 108 lines). The chart dictionary these proofs use (`ratCentralHom`, `sheet`,
  `sheet_entries`, `exists_eq`, `continuous_toAdelicUnipotent`) is imported from
  `AutomorphicForm/Adelic/RationalUnipotentHaar.lean`, where it was first needed; the pin re-proves
  it in each file (the `port once` block of SET-AF21 §3).

  **Wiring.** `spec/check_port.py` owns the declarations here.
  spec-pin: Theorems/Thm_AutomorphicForm_existsUnique_diagOne_inv_mul_mem_scalar_sup_unipotent_of_mem_borelSubgroup.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_existsUnique_diagOne_inv_mul_mem_scalar_sup_unipotent_of_mem_borelSubgroup.lean
  spec-pin: Theorems/Thm_AutomorphicForm_isFundamentalDomain_boxSheet_rationalCentreUnipotent.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_isFundamentalDomain_boxSheet_rationalCentreUnipotent.lean
  spec-pin: Theorems/Thm_AutomorphicForm_isFundamentalDomain_boxSheet_rationalTorusUnipotent.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_isFundamentalDomain_boxSheet_rationalTorusUnipotent.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.BorelSubgroup
import FLTForHuman.AutomorphicForm.Adelic.RationalUnipotentHaar

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel
open Topology Filter
open scoped ENNReal Pointwise

noncomputable section

namespace AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

/-! ### The Bruhat decomposition of the Borel -/

section Bruhat

variable {K : Type*} [Field K]

/-- The upper-triangular matrices of `GL₂` whose diagonal entries are equal: the common
containment of the scalars and the unipotent radical. -/
def equalDiagBorel : Subgroup (GL (Fin 2) K) where
  carrier := {x | (x : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
    (x : Matrix (Fin 2) (Fin 2) K) 0 0 = (x : Matrix (Fin 2) (Fin 2) K) 1 1}
  mul_mem' := by
    intro x y hx hy
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    constructor
    · simp [Matrix.mul_apply, Fin.sum_univ_two, hx1, hy1]
    · simp [Matrix.mul_apply, Fin.sum_univ_two, hx1, hy1, hx2, hy2]
  one_mem' := by
    constructor <;> simp
  inv_mem' := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    constructor
    · rw [Matrix.GeneralLinearGroup.coe_inv, Matrix.inv_def]
      simp [Matrix.adjugate_fin_two, hx1]
    · rw [Matrix.GeneralLinearGroup.coe_inv, Matrix.inv_def]
      simp [Matrix.adjugate_fin_two, hx2]

/-- The scalars are diagonal with equal entries. -/
theorem scalar_le_equalDiagBorel :
    (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom).range ≤
      (equalDiagBorel : Subgroup (GL (Fin 2) K)) := by
  rintro _ ⟨a, rfl⟩
  constructor
  · show (Matrix.scalar (Fin 2) (a : K)) 1 0 = 0
    simp
  · show (Matrix.scalar (Fin 2) (a : K)) 0 0 = (Matrix.scalar (Fin 2) (a : K)) 1 1
    simp

/-- The unitriangular embedding, unfolded. -/
theorem unipotentGL2Hom_apply (β : K) :
    unipotentGL2Hom (R := K) (Multiplicative.ofAdd β) = unipotentGL2 β := rfl

/-- The unipotent radical is diagonal with equal entries. -/
theorem unipotent_le_equalDiagBorel :
    (unipotentGL2Hom (R := K)).range ≤ (equalDiagBorel : Subgroup (GL (Fin 2) K)) := by
  rintro _ ⟨t, rfl⟩
  have ht : unipotentGL2Hom (R := K) t = unipotentGL2 t.toAdd := rfl
  rw [ht]
  constructor
  · show ((unipotentGL2 t.toAdd : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
    simp [unipotentGL2_coe]
  · show ((unipotentGL2 t.toAdd : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 =
      ((unipotentGL2 t.toAdd : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1
    simp [unipotentGL2_coe]

/-- The entries of a diagonal translate: `(diagOne a)⁻¹ * b` multiplies the `i`-th row of `b` by
the `i`-th diagonal entry of `(diagOne a)⁻¹`. -/
theorem diagOne_inv_mul_apply (a : Kˣ) (b : GL (Fin 2) K) (i j : Fin 2) :
    (((diagOne a)⁻¹ * b : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j =
      (Matrix.diagonal ![((a⁻¹ : Kˣ) : K), 1] i i) * (b : Matrix (Fin 2) (Fin 2) K) i j := by
  rw [← map_inv, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, diagOne_coe_apply,
    diagOne_coe_apply]
  fin_cases i <;> simp

end Bruhat

/-- **The Bruhat decomposition of the Borel.** A Borel element `b` of `GL₂(K)` has a unique
diagonal `a` such that `(diagOne a)⁻¹ * b` lies in the scalars times the unipotent radical. -/
theorem existsUnique_diagOne_inv_mul_mem_scalar_sup_unipotent_of_mem_borelSubgroup
    (K : Type*) [Field K] (b : GL (Fin 2) K) (hb : b ∈ borelSubgroup K) :
    ∃! a : Kˣ, (diagOne a)⁻¹ * b ∈
      (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom).range ⊔
        (unipotentGL2Hom (R := K)).range := by
  have hb10 : (b : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := hb
  set d₁ : Kˣ := borelDiagFst (⟨b, hb⟩ : ↥(borelSubgroup K)) with hd₁
  set d₂ : Kˣ := borelDiagSnd (⟨b, hb⟩ : ↥(borelSubgroup K)) with hd₂
  have hd₁v : (d₁ : K) = (b : Matrix (Fin 2) (Fin 2) K) 0 0 := rfl
  have hd₂v : (d₂ : K) = (b : Matrix (Fin 2) (Fin 2) K) 1 1 := rfl
  have h00 : (b : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := hd₁v ▸ d₁.ne_zero
  have h11 : (b : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 := hd₂v ▸ d₂.ne_zero
  refine ⟨d₁ * d₂⁻¹, ?_, ?_⟩
  ·
    have key : (diagOne (d₁ * d₂⁻¹))⁻¹ * b =
        Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom d₂ *
          unipotentGL2Hom (R := K) (Multiplicative.ofAdd
            ((b : Matrix (Fin 2) (Fin 2) K) 0 1 / (b : Matrix (Fin 2) (Fin 2) K) 0 0)) := by
      apply Units.ext
      ext i j
      rw [diagOne_inv_mul_apply, unipotentGL2Hom_apply, Units.val_mul, Units.coe_map,
        unipotentGL2_coe]
      simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Matrix.scalar_apply]
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Matrix.diagonal_apply, hb10, hd₁v, hd₂v, h00]
      · field_simp
    show (diagOne (d₁ * d₂⁻¹))⁻¹ * b ∈ _
    rw [key]
    exact Subgroup.mul_mem_sup ⟨d₂, rfl⟩ ⟨_, rfl⟩
  · intro a' ha'
    have hE := (sup_le scalar_le_equalDiagBorel unipotent_le_equalDiagBorel) ha'
    obtain ⟨-, hdiag⟩ := hE
    rw [diagOne_inv_mul_apply, diagOne_inv_mul_apply] at hdiag
    simp at hdiag
    apply Units.ext
    rw [Units.val_mul, Units.val_inv_eq_inv_val, hd₁v, hd₂v]
    have ha0 : ((a' : Kˣ) : K) ≠ 0 := a'.ne_zero
    field_simp
    field_simp at hdiag
    linear_combination (-1 : K) * hdiag

/-! ### The box sheets -/

section BoxSheetPrelude

variable (K : Type) [Field K] [NumberField K]

/-- A number field is countable. -/
theorem countable_numberField : Countable K := by
  have e := (Module.finBasis ℚ K).equivFun.toEquiv
  exact e.symm.countable_iff.mp inferInstance

/-- The rational unipotent embedding commutes with the global-points map. -/
theorem globalPoints_unipotentGL2 (β : K) :
    globalPoints (𝓞 K) K (unipotentGL2 β) =
      unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) := by
  apply Units.ext
  ext i j
  rw [globalPoints_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

end BoxSheetPrelude

/-- The global `Kˣ`-component of the adèle ring is embedded injectively. -/
private theorem algebraMap_adeleRing_injective (K : Type) [Field K] [NumberField K] :
    Function.Injective (algebraMap K (AdeleRing (𝓞 K) K)) := by
  intro x y h
  have h1 : algebraMap K (InfiniteAdeleRing K) x = algebraMap K (InfiniteAdeleRing K) y := by
    simpa only [NumberField.AdeleRing.fst_algebraMap] using congrArg (fun z => z.1) h
  have h2 := congrArg (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K) h1
  rw [← NumberField.InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp,
    ← NumberField.InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp] at h2
  exact mixedEmbedding_injective K h2

namespace CentreUnipotent

variable (K : Type) [Field K] [NumberField K]

/-- Every element of `P = Z(K) ⊔ U(K)`, with `U(K)` the *rational* unipotent radical, is a
rational scalar times a unipotent matrix with rational coordinate. -/
theorem exists_eq_rational (h : AdelicGL2 (𝓞 K) K)
    (hh : h ∈ rationalCentre K ⊔ ((globalPoints (𝓞 K) K).comp (unipotentGL2Hom (R := K))).range) :
    ∃ (a : Kˣ) (β : K),
      h = ratCentralHom K a * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) := by
  rw [Subgroup.sup_eq_closure] at hh
  refine Subgroup.closure_induction
    (p := fun g _ => ∃ (a : Kˣ) (β : K),
      g = ratCentralHom K a * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β))
    ?_ ?_ ?_ ?_ hh
  · intro g hg
    rcases hg with hg | hg
    · obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hg
      exact ⟨a, 0, by rw [map_zero, unipotentGL2_zero, mul_one]; rfl⟩
    · obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hg
      refine ⟨1, Multiplicative.toAdd y, ?_⟩
      rw [map_one, one_mul, MonoidHom.comp_apply, ← globalPoints_unipotentGL2]
      rfl
  · exact ⟨1, 0, by rw [map_one, map_zero, unipotentGL2_zero, mul_one]⟩
  · rintro g g' _ _ ⟨a, y, rfl⟩ ⟨a', y', rfl⟩
    refine ⟨a * a', y + y', ?_⟩
    rw [map_mul, map_add, unipotentGL2_add, mul_assoc, ← mul_assoc (unipotentGL2 _),
      ← ratCentralHom_comm, mul_assoc, mul_assoc]
  · rintro g _ ⟨a, y, rfl⟩
    refine ⟨a⁻¹, -y, ?_⟩
    rw [mul_inv_rev, TorusUnipotent.unipotentGL2_inv K, ← map_inv, map_neg,
      (ratCentralHom_comm K a⁻¹ (unipotentGL2 _)).symm]

/-- The product of two scalar-unipotent elements, in normal form. -/
theorem ratCentral_mul_unipotent_mul (a a' : Kˣ) (y y' : AdeleRing (𝓞 K) K) :
    ratCentralHom K a' * unipotentGL2 y' * (ratCentralHom K a * unipotentGL2 y) =
      ratCentralHom K (a' * a) * unipotentGL2 (y' + y) := by
  rw [map_mul, unipotentGL2_add, mul_assoc, ← mul_assoc (unipotentGL2 y'), ← ratCentralHom_comm,
    mul_assoc, mul_assoc]

/-- The box read inside `rationalCentreUnipotent K`, entry-wise. -/
theorem coe_inclusion_toAdelicUnipotent (u : AdeleRing (𝓞 K) K) :
    ((Subgroup.inclusion (le_sup_right : adelicUnipotent K ≤ rationalCentreUnipotent K)
      (toAdelicUnipotent K u) : rationalCentreUnipotent K) : AdelicGL2 (𝓞 K) K) =
        unipotentGL2 u := rfl

/-- The unit sheet is the inclusion of the unipotent radical. -/
theorem sheet_one_eq_inclusion (n : adelicUnipotent K) :
    sheet K 1 n = Subgroup.inclusion (le_sup_right : adelicUnipotent K ≤ rationalCentreUnipotent K) n := by
  refine Subtype.ext ?_
  rw [sheet_coe, map_one, one_mul]
  rfl

/-- The matrix entries are continuous on `rationalCentreUnipotent K`. -/
theorem continuous_entry (i j : Fin 2) : Continuous fun h : rationalCentreUnipotent K =>
    (((h : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j) :=
  ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).matrix_elem i j).comp
    continuous_subtype_val

/-- The box sheet is cut out by two entry conditions: unit `(0,0)`-entry and box-valued
`(0,1)`-entry. -/
theorem boxSheet_eq :
    (fun u : AdeleRing (𝓞 K) K => Subgroup.inclusion
      (le_sup_right : adelicUnipotent K ≤ rationalCentreUnipotent K)
      (toAdelicUnipotent K u)) '' adelicBox K =
    {h : rationalCentreUnipotent K |
      (((h : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0) = 1 ∧
      (((h : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1) ∈ adelicBox K} := by
  ext h
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨?_, ?_⟩
    · show ((unipotentGL2 u : AdelicGL2 (𝓞 K) K) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0 = 1
      simp [unipotentGL2_coe]
    · show ((unipotentGL2 u : AdelicGL2 (𝓞 K) K) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1 ∈ adelicBox K
      simpa [unipotentGL2_coe] using hu
  · rintro ⟨h00, h01⟩
    obtain ⟨a, y, hay⟩ := exists_eq K h h.2
    have ha : algebraMap K (AdeleRing (𝓞 K) K) a = 1 := by
      rw [← (sheet_entries K a y).1, ← hay]; exact h00
    have ha1 : a = 1 := by
      apply Units.ext
      rw [Units.val_one]
      exact algebraMap_adeleRing_injective K (by rw [ha, map_one])
    have hy : (((h : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1) = y := by
      rw [hay, (sheet_entries K a y).2, ha, one_mul]
    refine ⟨y, hy ▸ h01, Subtype.ext ?_⟩
    rw [coe_inclusion_toAdelicUnipotent, hay, ha1, map_one, one_mul]

/-- The box sheet is measurable. -/
theorem measurableSet_boxSheet :
    MeasurableSet ((fun u : AdeleRing (𝓞 K) K => Subgroup.inclusion
      (le_sup_right : adelicUnipotent K ≤ rationalCentreUnipotent K)
      (toAdelicUnipotent K u)) '' adelicBox K) := by
  rw [boxSheet_eq]
  exact ((continuous_entry K 0 0).measurable (measurableSet_singleton 1)).inter
    ((continuous_entry K 0 1).measurable (measurableSet_adelicBox K))

end CentreUnipotent

section CentreSheet

open CentreUnipotent

/-- The box, read inside `rationalCentreUnipotent K`, is a fundamental domain for the
centre-unipotent subgroup itself. -/
theorem isFundamentalDomain_boxSheet_rationalCentreUnipotent
    (K : Type) [Field K] [NumberField K] :
    let P : Subgroup (AdelicGL2 (𝓞 K) K) :=
      rationalCentre K ⊔ ((globalPoints (𝓞 K) K).comp (unipotentGL2Hom (R := K))).range
    let T : Set (rationalCentreUnipotent K) :=
      (fun u : AdeleRing (𝓞 K) K => Subgroup.inclusion le_sup_right (toAdelicUnipotent K u)) '' adelicBox K
    P ≤ rationalCentreUnipotent K ∧ Countable P ∧ MeasurableSet T ∧
    IsFundamentalDomain (P.subgroupOf (rationalCentreUnipotent K)) T (rationalCentreUnipotentHaar K) ∧
    ∀ F : rationalCentreUnipotent K → ℝ≥0∞, Measurable F →
      ∫⁻ x in T, F x ∂(rationalCentreUnipotentHaar K) =
        ∫⁻ u in adelicBox K, F (Subgroup.inclusion le_sup_right (toAdelicUnipotent K u))
          ∂(((adelicAddHaar (𝓞 K) K) (adelicBox K))⁻¹ • adelicAddHaar (𝓞 K) K) := by
  intro P T
  have : Countable K := countable_numberField K
  have hT : MeasurableSet T := measurableSet_boxSheet K
  have hTeq : T = {h : rationalCentreUnipotent K |
      (((h : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0) = 1 ∧
      (((h : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1) ∈
        adelicBox K} := boxSheet_eq K
  have hmemP : ∀ (a' : Kˣ) (β' : K),
      ratCentralHom K a' * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β') ∈ P := fun a' β' =>
    Subgroup.mul_mem_sup ⟨a', rfl⟩ ⟨Multiplicative.ofAdd β', by
      rw [MonoidHom.comp_apply]
      change globalPoints (𝓞 K) K (unipotentGL2 β') = _
      rw [globalPoints_unipotentGL2]⟩
  have hle : P ≤ rationalCentreUnipotent K := by
    refine sup_le le_sup_left ?_
    rintro _ ⟨x, rfl⟩
    refine Subgroup.mem_sup_right
      ⟨Multiplicative.ofAdd (algebraMap K (AdeleRing (𝓞 K) K) x.toAdd), ?_⟩
    rw [MonoidHom.comp_apply]
    change unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) x.toAdd) =
      globalPoints (𝓞 K) K (unipotentGL2 x.toAdd)
    rw [globalPoints_unipotentGL2]
  have hcount : Countable P := by
    have : Countable Kˣ := Function.Injective.countable (f := (Units.val : Kˣ → K)) Units.val_injective
    let f : Kˣ × K → P := fun p =>
      ⟨ratCentralHom K p.1 * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) p.2), hmemP p.1 p.2⟩
    refine Function.Surjective.countable (f := f) fun g => ?_
    obtain ⟨a, β, h⟩ := exists_eq_rational K g g.2
    exact ⟨(a, β), Subtype.ext h.symm⟩
  refine ⟨hle, hcount, hT, ?_, ?_⟩
  ·
    refine IsFundamentalDomain.mk' hT.nullMeasurableSet fun x => ?_
    obtain ⟨a, y, hay⟩ := exists_eq K x x.2
    obtain ⟨β, hβ, hβu⟩ := existsUnique_algebraMap_add_mem_adelicBox K y
    let g₀ : P.subgroupOf (rationalCentreUnipotent K) :=
      ⟨⟨ratCentralHom K a⁻¹ * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β), hle (hmemP a⁻¹ β)⟩,
        Subgroup.mem_subgroupOf.mpr (hmemP a⁻¹ β)⟩
    have hval : ∀ g : P.subgroupOf (rationalCentreUnipotent K),
        (((g • x : rationalCentreUnipotent K)) : AdelicGL2 (𝓞 K) K) =
          ((g : rationalCentreUnipotent K) : AdelicGL2 (𝓞 K) K) * (x : AdelicGL2 (𝓞 K) K) :=
      fun g => rfl
    refine ⟨g₀, ?_, ?_⟩
    · show g₀ • x ∈ T
      rw [hTeq]
      have hv : (((g₀ • x : rationalCentreUnipotent K)) : AdelicGL2 (𝓞 K) K) =
          ratCentralHom K (a⁻¹ * a) * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β + y) := by
        rw [hval, hay]
        exact ratCentral_mul_unipotent_mul K a a⁻¹ y _
      rw [inv_mul_cancel] at hv
      refine ⟨?_, ?_⟩
      · rw [hv, (sheet_entries K 1 _).1, Units.val_one, map_one]
      · rw [hv, (sheet_entries K 1 _).2, Units.val_one, map_one, one_mul]
        exact hβ
    · intro g hg
      rw [hTeq] at hg
      obtain ⟨h00, h01⟩ := hg
      obtain ⟨a', β', ha'⟩ := exists_eq_rational K
        ((g : rationalCentreUnipotent K) : AdelicGL2 (𝓞 K) K) (Subgroup.mem_subgroupOf.mp g.2)
      have hv : (((g • x : rationalCentreUnipotent K)) : AdelicGL2 (𝓞 K) K) =
          ratCentralHom K (a' * a) * unipotentGL2
            (algebraMap K (AdeleRing (𝓞 K) K) β' + y) := by
        rw [hval, hay, ha']
        exact ratCentral_mul_unipotent_mul K a a' y _
      rw [hv, (sheet_entries K _ _).1] at h00
      rw [hv, (sheet_entries K _ _).2, h00, one_mul] at h01
      have ha'a : a' * a = 1 := by
        apply Units.ext
        rw [Units.val_one]
        exact algebraMap_adeleRing_injective K (by rw [h00, map_one])
      have ha'' : a' = a⁻¹ := eq_inv_of_mul_eq_one_left ha'a
      have hβ' : β' = β := hβu β' h01
      apply Subtype.ext
      apply Subtype.ext
      rw [ha', ha'', hβ']
  ·
    intro F hF
    have hind : Measurable (T.indicator F) := hF.indicator hT
    rw [← lintegral_indicator hT, rationalCentreUnipotentHaar_eq, lintegral_sum_measure]
    have hterm : ∀ a : Kˣ, ∫⁻ x, T.indicator F x ∂((unipotentHaar K).map (sheet K a)) =
        ∫⁻ n, T.indicator F (sheet K a n) ∂(unipotentHaar K) := fun a =>
      lintegral_map hind (measurable_sheet K a)
    simp_rw [hterm]
    have hzero : ∀ a : Kˣ, a ≠ 1 →
        ∫⁻ n, T.indicator F (sheet K a n) ∂(unipotentHaar K) = 0 := by
      intro a ha
      have : ∀ n, T.indicator F (sheet K a n) = 0 := by
        intro n
        apply Set.indicator_of_notMem
        rw [hTeq]
        rintro ⟨h00, -⟩
        obtain ⟨y, rfl⟩ := TorusUnipotent.exists_eq_toAdelicUnipotent K n
        rw [sheet_coe, TorusUnipotent.coe_toAdelicUnipotent, (sheet_entries K a y).1] at h00
        apply ha
        apply Units.ext
        rw [Units.val_one]
        exact algebraMap_adeleRing_injective K (by rw [h00, map_one])
      simp [this]
    rw [tsum_eq_single 1 hzero]
    have hm1 : Measurable (fun n : adelicUnipotent K => T.indicator F (sheet K 1 n)) :=
      hind.comp (measurable_sheet K 1)
    rw [unipotentHaar, lintegral_map hm1 (continuous_toAdelicUnipotent K).measurable,
      ← lintegral_indicator (measurableSet_adelicBox K)]
    refine lintegral_congr (fun y => ?_)
    rw [sheet_one_eq_inclusion K]
    have hmem : Subgroup.inclusion (le_sup_right : adelicUnipotent K ≤ rationalCentreUnipotent K)
        (toAdelicUnipotent K y) ∈ T ↔ y ∈ adelicBox K := by
      rw [hTeq, Set.mem_ofPred_eq, coe_inclusion_toAdelicUnipotent, unipotentGL2_coe]
      simp
    by_cases hy : y ∈ adelicBox K
    · rw [Set.indicator_of_mem (hmem.mpr hy), Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem (fun h => hy (hmem.mp h)), Set.indicator_of_notMem hy]

end CentreSheet

namespace TorusUnipotent

variable (K : Type) [Field K] [NumberField K]

/-- The product of two torus-unipotent elements, in normal form. -/
theorem torus_mul_unipotent_mul (za zb : Kˣ × Kˣ) (y y' : AdeleRing (𝓞 K) K) :
    torus K zb * unipotentGL2 y' * (torus K za * unipotentGL2 y) =
      torus K (zb * za) *
        unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ((za.2⁻¹ : Kˣ) : K) * y' + y) := by
  rw [mul_assoc, ← mul_assoc (unipotentGL2 y'), unipotentGL2_mul_torus, mul_assoc,
    ← unipotentGL2_add, ← mul_assoc, torus_mul]

omit [NumberField K] in
/-- The Bruhat decomposition of a Borel element, in explicit normal form. -/
theorem borel_eq (b : GL (Fin 2) K) (hb : b ∈ borelSubgroup K) :
    b = Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom
        (borelDiagSnd ⟨b, hb⟩) *
      diagOne (borelDiagFst ⟨b, hb⟩ * (borelDiagSnd ⟨b, hb⟩)⁻¹) *
      unipotentGL2 ((b : Matrix (Fin 2) (Fin 2) K) 0 1 / (b : Matrix (Fin 2) (Fin 2) K) 0 0) := by
  have hb10 : (b : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := hb
  have hd₁v : ((borelDiagFst (⟨b, hb⟩ : ↥(borelSubgroup K)) : Kˣ) : K) =
      (b : Matrix (Fin 2) (Fin 2) K) 0 0 := rfl
  have hd₂v : ((borelDiagSnd (⟨b, hb⟩ : ↥(borelSubgroup K)) : Kˣ) : K) =
      (b : Matrix (Fin 2) (Fin 2) K) 1 1 := rfl
  have h00 : (b : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 :=
    hd₁v ▸ (borelDiagFst (⟨b, hb⟩ : ↥(borelSubgroup K))).ne_zero
  have h11 : (b : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 :=
    hd₂v ▸ (borelDiagSnd (⟨b, hb⟩ : ↥(borelSubgroup K))).ne_zero
  apply Units.ext
  ext i j
  rw [Units.val_mul, Units.val_mul, Units.coe_map, unipotentGL2_coe]
  simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Matrix.scalar_apply]
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two, diagOne_coe_apply, diagOne_coe_apply, diagOne_coe_apply, diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;>
    simp [hb10, hd₁v, hd₂v, Units.val_mul]
  all_goals field_simp

/-- The image of a Borel element under the global points, in normal form. -/
theorem globalPoints_borel_eq (b : GL (Fin 2) K) (hb : b ∈ borelSubgroup K) :
    globalPoints (𝓞 K) K b =
      torus K (borelDiagSnd ⟨b, hb⟩, borelDiagFst ⟨b, hb⟩ * (borelDiagSnd ⟨b, hb⟩)⁻¹) *
        unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K)
          ((b : Matrix (Fin 2) (Fin 2) K) 0 1 / (b : Matrix (Fin 2) (Fin 2) K) 0 0)) := by
  conv_lhs => rw [borel_eq K b hb]
  rw [map_mul, map_mul, globalPoints_unipotentGL2]
  rfl

/-- The normal form of a Borel element lies in the image of the Borel. -/
theorem torus_mul_unipotent_mem_map (za : Kˣ × Kˣ) (β : K) :
    torus K za * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) ∈
      (borelSubgroup K).map (globalPoints (𝓞 K) K) := by
  refine ⟨Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom za.1 *
      diagOne za.2 * unipotentGL2 β, ?_, ?_⟩
  · refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) (unipotentGL2_mem_borelSubgroup β)
    · show (Matrix.scalar (Fin 2) ((za.1 : Kˣ) : K)) 1 0 = 0
      simp
    · show (diagOne za.2 : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
      rw [diagOne_coe_apply]; simp
  · rw [map_mul, map_mul, globalPoints_unipotentGL2]
    rfl

/-- Every element of the image of the Borel is a torus element times a rational unipotent one. -/
theorem exists_eq_of_mem_map (g : AdelicGL2 (𝓞 K) K)
    (hg : g ∈ (borelSubgroup K).map (globalPoints (𝓞 K) K)) :
    ∃ (za : Kˣ × Kˣ) (β : K),
      g = torus K za * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) := by
  obtain ⟨b, hb, rfl⟩ := hg
  exact ⟨_, _, globalPoints_borel_eq K b hb⟩

/-- The box read inside `rationalTorusUnipotent K`, entry-wise. -/
theorem coe_inclusion_toAdelicUnipotent (u : AdeleRing (𝓞 K) K) :
    ((Subgroup.inclusion (le_sup_right : adelicUnipotent K ≤ rationalTorusUnipotent K)
      (toAdelicUnipotent K u) : rationalTorusUnipotent K) : AdelicGL2 (𝓞 K) K) =
        unipotentGL2 u := rfl

/-- The unit sheet is the inclusion of the unipotent radical. -/
theorem sheet_one_eq_inclusion (n : adelicUnipotent K) :
    sheet K 1 n = Subgroup.inclusion (le_sup_right : adelicUnipotent K ≤ rationalTorusUnipotent K) n := by
  refine Subtype.ext ?_
  rw [sheet_coe, torus_one, one_mul]
  rfl

/-- The matrix entries are continuous on `rationalTorusUnipotent K`. -/
theorem continuous_entry (i j : Fin 2) : Continuous fun h : rationalTorusUnipotent K =>
    (((h : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j) :=
  ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).matrix_elem i j).comp
    continuous_subtype_val

/-- A torus-unipotent element whose two diagonal entries are `1` is the unit torus element. -/
theorem torus_eq_one_of_entries (za : Kˣ × Kˣ) (y : AdeleRing (𝓞 K) K)
    (h00 : (((torus K za * unipotentGL2 y : AdelicGL2 (𝓞 K) K)) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0 = 1)
    (h11 : (((torus K za * unipotentGL2 y : AdelicGL2 (𝓞 K) K)) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1 = 1) :
    za = 1 := by
  rw [(sheet_entries K za y).1] at h00
  rw [(sheet_entries K za y).2.2] at h11
  have hz : za.1 = 1 := by
    apply Units.ext
    rw [Units.val_one]
    exact algebraMap_adeleRing_injective K (by rw [h11, map_one])
  have hza : za.1 * za.2 = 1 := by
    apply Units.ext
    rw [Units.val_one]
    exact algebraMap_adeleRing_injective K (by rw [h00, map_one])
  rw [hz, one_mul] at hza
  exact Prod.ext hz hza

/-- The box sheet is cut out by three entry conditions: unit `(0,0)`- and `(1,1)`-entries and
box-valued `(0,1)`-entry. -/
theorem boxSheet_eq :
    (fun u : AdeleRing (𝓞 K) K => Subgroup.inclusion
      (le_sup_right : adelicUnipotent K ≤ rationalTorusUnipotent K)
      (toAdelicUnipotent K u)) '' adelicBox K =
    {h : rationalTorusUnipotent K |
      (((h : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0) = 1 ∧
      (((h : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1) = 1 ∧
      (((h : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1) ∈ adelicBox K} := by
  ext h
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · show ((unipotentGL2 u : AdelicGL2 (𝓞 K) K) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0 = 1
      simp [unipotentGL2_coe]
    · show ((unipotentGL2 u : AdelicGL2 (𝓞 K) K) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1 = 1
      simp [unipotentGL2_coe]
    · show ((unipotentGL2 u : AdelicGL2 (𝓞 K) K) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1 ∈ adelicBox K
      simpa [unipotentGL2_coe] using hu
  · rintro ⟨h00, h11, h01⟩
    obtain ⟨za, y, hay⟩ := exists_eq K h h.2
    have hza : za = 1 := torus_eq_one_of_entries K za y (hay ▸ h00) (hay ▸ h11)
    have hy : (((h : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1) = y := by
      rw [hay, (sheet_entries K za y).2.1, hza]
      simp
    refine ⟨y, hy ▸ h01, Subtype.ext ?_⟩
    rw [coe_inclusion_toAdelicUnipotent, hay, hza, torus_one, one_mul]

/-- The box sheet is measurable. -/
theorem measurableSet_boxSheet :
    MeasurableSet ((fun u : AdeleRing (𝓞 K) K => Subgroup.inclusion
      (le_sup_right : adelicUnipotent K ≤ rationalTorusUnipotent K)
      (toAdelicUnipotent K u)) '' adelicBox K) := by
  rw [boxSheet_eq]
  exact ((continuous_entry K 0 0).measurable (measurableSet_singleton 1)).inter
    (((continuous_entry K 1 1).measurable (measurableSet_singleton 1)).inter
      ((continuous_entry K 0 1).measurable (measurableSet_adelicBox K)))

end TorusUnipotent

section TorusSheet

open TorusUnipotent

/-- The box, read inside `rationalTorusUnipotent K` by the box sheet, is a fundamental domain for
the image of the Borel. -/
theorem isFundamentalDomain_boxSheet_rationalTorusUnipotent
    (K : Type) [Field K] [NumberField K] :
    let B : Subgroup (AdelicGL2 (𝓞 K) K) := (borelSubgroup K).map (globalPoints (𝓞 K) K)
    let T : Set (rationalTorusUnipotent K) :=
      (fun u : AdeleRing (𝓞 K) K => Subgroup.inclusion le_sup_right (toAdelicUnipotent K u)) '' adelicBox K
    B ≤ rationalTorusUnipotent K ∧ Countable B ∧ MeasurableSet T ∧
    IsFundamentalDomain (B.subgroupOf (rationalTorusUnipotent K)) T (rationalTorusUnipotentHaar K) ∧
    ∀ F : rationalTorusUnipotent K → ℝ≥0∞, Measurable F →
      ∫⁻ x in T, F x ∂(rationalTorusUnipotentHaar K) =
        ∫⁻ u in adelicBox K, F (Subgroup.inclusion le_sup_right (toAdelicUnipotent K u))
          ∂(((adelicAddHaar (𝓞 K) K) (adelicBox K))⁻¹ • adelicAddHaar (𝓞 K) K) := by
  intro B T
  have : Countable K := countable_numberField K
  have hT : MeasurableSet T := measurableSet_boxSheet K
  have hTeq : T = {h : rationalTorusUnipotent K |
      (((h : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0) = 1 ∧
      (((h : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1) = 1 ∧
      (((h : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1) ∈
        adelicBox K} := boxSheet_eq K
  have hmemB : ∀ (za : Kˣ × Kˣ) (β : K),
      torus K za * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) ∈ B :=
    torus_mul_unipotent_mem_map K
  have hle : B ≤ rationalTorusUnipotent K := by
    intro g hg
    obtain ⟨za, β, rfl⟩ := exists_eq_of_mem_map K g hg
    exact Subgroup.mul_mem _ (mem_torus K za) (mem_unipotent K _)
  have hcount : Countable B := by
    have : Countable Kˣ := Function.Injective.countable (f := (Units.val : Kˣ → K)) Units.val_injective
    let f : (Kˣ × Kˣ) × K → B := fun p =>
      ⟨torus K p.1 * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) p.2), hmemB p.1 p.2⟩
    refine Function.Surjective.countable (f := f) fun g => ?_
    obtain ⟨za, β, h⟩ := exists_eq_of_mem_map K g g.2
    exact ⟨(za, β), Subtype.ext h.symm⟩
  refine ⟨hle, hcount, hT, ?_, ?_⟩
  ·
    refine IsFundamentalDomain.mk' hT.nullMeasurableSet fun x => ?_
    obtain ⟨za, y, hay⟩ := exists_eq K x x.2
    obtain ⟨β₀, hβ₀, hβ₀u⟩ := existsUnique_algebraMap_add_mem_adelicBox K y
    let g₀ : B.subgroupOf (rationalTorusUnipotent K) :=
      ⟨⟨torus K za⁻¹ * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ((za.2 : K) * β₀)),
        hle (hmemB za⁻¹ _)⟩, Subgroup.mem_subgroupOf.mpr (hmemB za⁻¹ _)⟩
    have hval : ∀ g : B.subgroupOf (rationalTorusUnipotent K),
        (((g • x : rationalTorusUnipotent K)) : AdelicGL2 (𝓞 K) K) =
          ((g : rationalTorusUnipotent K) : AdelicGL2 (𝓞 K) K) * (x : AdelicGL2 (𝓞 K) K) :=
      fun g => rfl
    have hscale : ∀ β : K,
        algebraMap K (AdeleRing (𝓞 K) K) ((za.2⁻¹ : Kˣ) : K) *
          algebraMap K (AdeleRing (𝓞 K) K) β =
        algebraMap K (AdeleRing (𝓞 K) K) (((za.2⁻¹ : Kˣ) : K) * β) := fun β => by rw [map_mul]
    refine ⟨g₀, ?_, ?_⟩
    · show g₀ • x ∈ T
      rw [hTeq]
      have hv : (((g₀ • x : rationalTorusUnipotent K)) : AdelicGL2 (𝓞 K) K) =
          torus K (za⁻¹ * za) * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β₀ + y) := by
        rw [hval, hay]
        have hk : ((za.2⁻¹ : Kˣ) : K) * ((za.2 : K) * β₀) = β₀ := by
          rw [Units.val_inv_eq_inv_val, ← mul_assoc, inv_mul_cancel₀ za.2.ne_zero, one_mul]
        have := torus_mul_unipotent_mul K za za⁻¹ y
          (algebraMap K (AdeleRing (𝓞 K) K) ((za.2 : K) * β₀))
        rw [hscale, hk] at this
        exact this
      rw [inv_mul_cancel] at hv
      refine ⟨?_, ?_, ?_⟩
      · rw [hv, (sheet_entries K 1 _).1]; simp
      · rw [hv, (sheet_entries K 1 _).2.2]; simp
      · rw [hv, (sheet_entries K 1 _).2.1]; simpa using hβ₀
    · intro g hg
      rw [hTeq] at hg
      obtain ⟨h00, h11, h01⟩ := hg
      obtain ⟨zb, β', hb'⟩ := exists_eq_of_mem_map K
        ((g : rationalTorusUnipotent K) : AdelicGL2 (𝓞 K) K) (Subgroup.mem_subgroupOf.mp g.2)
      have hv : (((g • x : rationalTorusUnipotent K)) : AdelicGL2 (𝓞 K) K) =
          torus K (zb * za) * unipotentGL2
            (algebraMap K (AdeleRing (𝓞 K) K) (((za.2⁻¹ : Kˣ) : K) * β') + y) := by
        rw [hval, hay, hb', torus_mul_unipotent_mul, hscale]
      rw [hv] at h00 h11 h01
      have hw : zb * za = 1 := torus_eq_one_of_entries K _ _ h00 h11
      rw [hw, (sheet_entries K 1 _).2.1] at h01
      simp only [Prod.fst_one, Prod.snd_one, mul_one, Units.val_one, map_one, one_mul] at h01
      have hzb : zb = za⁻¹ := eq_inv_of_mul_eq_one_left hw
      have hβ' : ((za.2⁻¹ : Kˣ) : K) * β' = β₀ := hβ₀u _ h01
      have hβ'' : β' = (za.2 : K) * β₀ := by
        rw [← hβ', ← mul_assoc, Units.val_inv_eq_inv_val, mul_inv_cancel₀ za.2.ne_zero, one_mul]
      apply Subtype.ext
      apply Subtype.ext
      rw [hb', hzb, hβ'']
  ·
    intro F hF
    have hind : Measurable (T.indicator F) := hF.indicator hT
    rw [← lintegral_indicator hT, rationalTorusUnipotentHaar_eq, lintegral_sum_measure]
    have hterm : ∀ za : Kˣ × Kˣ, ∫⁻ x, T.indicator F x ∂((unipotentHaar K).map (sheet K za)) =
        ∫⁻ n, T.indicator F (sheet K za n) ∂(unipotentHaar K) := fun za =>
      lintegral_map hind (measurable_sheet K za)
    simp_rw [hterm]
    have hzero : ∀ za : Kˣ × Kˣ, za ≠ 1 →
        ∫⁻ n, T.indicator F (sheet K za n) ∂(unipotentHaar K) = 0 := by
      intro za hza
      have : ∀ n, T.indicator F (sheet K za n) = 0 := by
        intro n
        apply Set.indicator_of_notMem
        rw [hTeq]
        rintro ⟨h00, h11, -⟩
        obtain ⟨y, rfl⟩ := exists_eq_toAdelicUnipotent K n
        rw [sheet_coe, coe_toAdelicUnipotent] at h00 h11
        exact hza (torus_eq_one_of_entries K za y h00 h11)
      simp [this]
    rw [tsum_eq_single 1 hzero]
    have hm1 : Measurable (fun n : adelicUnipotent K => T.indicator F (sheet K 1 n)) :=
      hind.comp (measurable_sheet K 1)
    rw [unipotentHaar, lintegral_map hm1 (continuous_toAdelicUnipotent K).measurable,
      ← lintegral_indicator (measurableSet_adelicBox K)]
    refine lintegral_congr (fun y => ?_)
    rw [sheet_one_eq_inclusion K]
    have hmem : Subgroup.inclusion (le_sup_right : adelicUnipotent K ≤ rationalTorusUnipotent K)
        (toAdelicUnipotent K y) ∈ T ↔ y ∈ adelicBox K := by
      rw [hTeq, Set.mem_ofPred_eq, coe_inclusion_toAdelicUnipotent, unipotentGL2_coe]
      simp
    by_cases hy : y ∈ adelicBox K
    · rw [Set.indicator_of_mem (hmem.mpr hy), Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem (fun h => hy (hmem.mp h)), Set.indicator_of_notMem hy]

end TorusSheet

end AutomorphicForm

end
