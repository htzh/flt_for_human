/-
  The rational centre-unipotent and torus-unipotent subgroups of `GL₂(𝔸_K)` are closed.

  Two closedness statements, each the same two-step argument:

  * `isClosed_rationalCentreUnipotent`: `Z(𝔸_K) · Kˣ · U(𝔸_K)` is the set of unitriangular
    (`1 0`-entry `0`) matrices whose `(0,0)`-entry is a scalar matrix of a **rational** point,
    and that set is closed: the entry maps are continuous and the range of `K ↪ 𝔸_K` is closed in
    the adèle ring — which is where the discreteness of `K` enters
    (`NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact`).
  * `isClosed_rationalTorusUnipotent`: the same with both diagonal entries rational.

  `isClosed_range_algebraMap_adeleRing` is the shared engine. The pin proves it twice, once in
  each of the two `S_` files (19 lines, statements byte-identical); it is written once here, and
  the module carries both files' wires.

  The two Haar-measure headlines of the same subgroups — that `rationalCentreUnipotentHaar` and
  `rationalTorusUnipotentHaar` are Haar and right-invariant — are a separate subject and live in
  `AutomorphicForm/Adelic/RationalUnipotentHaar.lean`; nothing there is imported here.

  Transcribed from `Theorems/Thm_AutomorphicForm_isClosed_rational{,Torus}Unipotent.lean` and
  their two `S_` files (pinned `aa2d8b3`, 134 + 174 lines).

  **Wiring.** `spec/check_port.py` owns the declarations here.
  spec-pin: Theorems/Thm_AutomorphicForm_isClosed_rationalCentreUnipotent.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_isClosed_rationalCentreUnipotent.lean
  spec-pin: Theorems/Thm_AutomorphicForm_isClosed_rationalTorusUnipotent.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_isClosed_rationalTorusUnipotent.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.UnipotentQuotient
import FLTForHuman.NumberTheory.AdelicDiscreteness

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel
open Topology Filter

noncomputable section

namespace AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

variable (K : Type) [Field K] [NumberField K]

/-- The diagonal image of `K` in `𝔸_K` is closed — a compact set meets it finitely, so its range
is closed. -/
theorem isClosed_range_algebraMap_adeleRing : IsClosed (Set.range (algebraMap K (AdeleRing (𝓞 K) K))) := by
  set R := Set.range (algebraMap K (AdeleRing (𝓞 K) K)) with hR
  refine isClosed_of_closure_subset fun x hx => ?_
  obtain ⟨C, hC, hCx⟩ := exists_compact_mem_nhds x
  have hfin : (R ∩ C).Finite := by
    have h := NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact K hC
    have : R ∩ C = algebraMap K (AdeleRing (𝓞 K) K) '' {ξ : K | algebraMap K (AdeleRing (𝓞 K) K) ξ ∈ C} := by
      ext y; constructor
      · rintro ⟨⟨ξ, rfl⟩, hy⟩; exact ⟨ξ, hy, rfl⟩
      · rintro ⟨ξ, hξ, rfl⟩; exact ⟨⟨ξ, rfl⟩, hξ⟩
    rw [this]; exact h.image _
  have hx' : x ∈ closure (R ∩ C) := by
    rw [mem_closure_iff_nhds] at hx ⊢
    intro U hU
    obtain ⟨y, hyU, hyR⟩ := hx (U ∩ C) (inter_mem hU hCx)
    exact ⟨y, hyU.1, hyR, hyU.2⟩
  rw [hfin.isClosed.closure_eq] at hx'
  exact hx'.1

/-! ### The centre-unipotent row -/

/-- The unitriangular matrices with equal diagonal entries, that common entry rational: the
entry-side description of `Z(𝔸_K) · Kˣ · U(𝔸_K)`. -/
def scalarUnipotentSet : Set (AdelicGL2 (𝓞 K) K) :=
  {g | (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0 ∧
    (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0 = (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1 ∧
    (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0 ∈ Set.range (algebraMap K (AdeleRing (𝓞 K) K))}

/-- `scalarUnipotentSet K` is closed: a finite intersection of closed entry conditions. -/
theorem isClosed_scalarUnipotentSet : IsClosed (scalarUnipotentSet K) := by
  have hent : ∀ i j : Fin 2, Continuous fun g : AdelicGL2 (𝓞 K) K => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j :=
    fun i j => (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).matrix_elem i j
  simp only [scalarUnipotentSet, Set.ofPred_and]
  refine (isClosed_eq (hent 1 0) continuous_const).inter ((isClosed_eq (hent 0 0) (hent 1 1)).inter ?_)
  exact (isClosed_range_algebraMap_adeleRing K).preimage (hent 0 0)

/-- `scalarUnipotentSet K` is closed under multiplication. -/
theorem mul_mem_scalarUnipotentSet {g h : AdelicGL2 (𝓞 K) K} (hg : g ∈ scalarUnipotentSet K) (hh : h ∈ scalarUnipotentSet K) :
    g * h ∈ scalarUnipotentSet K := by
  obtain ⟨hg1, hg2, ξ, hξ⟩ := hg
  obtain ⟨hh1, hh2, η, hη⟩ := hh
  have e : ∀ i j : Fin 2, ((g * h : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j =
      (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i 0 * (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 j +
      (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i 1 * (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 j := by
    intro i j; rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨?_, ?_, ξ * η, ?_⟩
  · rw [e, hg1, hh1, zero_mul, mul_zero, add_zero]
  · rw [e, e, hh1, hg1, mul_zero, add_zero, zero_mul, zero_add, hg2, hh2]
  · rw [e, hh1, mul_zero, add_zero, map_mul, hξ, hη]

/-- The rational scalar matrices lie in `scalarUnipotentSet K`. -/
theorem globalPoints_scalar_mem_scalarUnipotentSet (a : Kˣ) :
    globalPoints (𝓞 K) K (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom a) ∈
      scalarUnipotentSet K := by
  refine ⟨?_, ?_, (a : K), ?_⟩ <;>
    simp [globalPoints, Matrix.GeneralLinearGroup.map, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.scalar_apply]

/-- The adèlic unitriangular matrices lie in `scalarUnipotentSet K`. -/
theorem unipotentGL2_mem_scalarUnipotentSet (x : AdeleRing (𝓞 K) K) :
    (unipotentGL2 x : AdelicGL2 (𝓞 K) K) ∈ scalarUnipotentSet K := by
  refine ⟨?_, ?_, 1, ?_⟩ <;> simp [unipotentGL2_coe]

/-- The rational centre-unipotent subgroup is the set of unitriangular matrices with a rational
scalar diagonal entry. -/
theorem coe_rationalCentreUnipotent_eq :
    (rationalCentreUnipotent K : Set (AdelicGL2 (𝓞 K) K)) = scalarUnipotentSet K := by
  apply Set.Subset.antisymm
  · intro g hg
    rw [SetLike.mem_coe, rationalCentreUnipotent, Subgroup.sup_eq_closure] at hg
    refine (Subgroup.closure_induction (p := fun g _ => g ∈ scalarUnipotentSet K ∧ g⁻¹ ∈ scalarUnipotentSet K)
      ?_ ?_ ?_ ?_ hg).1
    · intro g hg
      rcases hg with hg | hg
      · obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hg
        refine ⟨?_, ?_⟩
        · exact globalPoints_scalar_mem_scalarUnipotentSet K a
        · rw [MonoidHom.comp_apply, ← map_inv, ← map_inv]
          exact globalPoints_scalar_mem_scalarUnipotentSet K a⁻¹
      · obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hg
        exact ⟨unipotentGL2_mem_scalarUnipotentSet K _, by rw [← map_inv]; exact unipotentGL2_mem_scalarUnipotentSet K _⟩
    · have h1 : (1 : AdelicGL2 (𝓞 K) K) ∈ scalarUnipotentSet K := by
        rw [← unipotentGL2_zero]; exact unipotentGL2_mem_scalarUnipotentSet K 0
      exact ⟨h1, by rw [inv_one]; exact h1⟩
    · intro g h _ _ hg hh
      exact ⟨mul_mem_scalarUnipotentSet K hg.1 hh.1, by rw [mul_inv_rev]; exact mul_mem_scalarUnipotentSet K hh.2 hg.2⟩
    · intro g _ hg
      exact ⟨hg.2, by rw [inv_inv]; exact hg.1⟩
  · rintro g ⟨h10, hdiag, ξ, hξ⟩
    have : Nontrivial (AdeleRing (𝓞 K) K) := (NumberField.AdeleRing.algebraMap_injective (R := 𝓞 K) (K := K)).nontrivial
    have hξ0 : ξ ≠ 0 := by
      intro h0
      apply (Matrix.GeneralLinearGroup.det g).ne_zero
      rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h10, ← hdiag, ← hξ, h0, map_zero]
      ring
    set a : Kˣ := Units.mk0 ξ hξ0 with ha
    set x : AdeleRing (𝓞 K) K := algebraMap K (AdeleRing (𝓞 K) K) ξ⁻¹ * (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1
      with hx
    have hg : g = globalPoints (𝓞 K) K (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom a) *
        unipotentGL2 x := by
      refine Units.ext (Matrix.ext fun i j => ?_)
      rw [Matrix.GeneralLinearGroup.coe_mul]
      have hz : ∀ i j : Fin 2, ((globalPoints (𝓞 K) K (Units.map (Matrix.scalar (Fin 2) :
          K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom a) : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j =
          if i = j then algebraMap K (AdeleRing (𝓞 K) K) ξ else 0 := by
        intro i j
        change algebraMap K (AdeleRing (𝓞 K) K) ((Matrix.scalar (Fin 2) ((a : Kˣ) : K)) i j) = _
        rw [Matrix.scalar_apply, Matrix.diagonal_apply]
        split_ifs <;> simp [ha]
      rw [Matrix.mul_apply, Fin.sum_univ_two, hz, hz, unipotentGL2_coe]
      have hinv : algebraMap K (AdeleRing (𝓞 K) K) ξ * algebraMap K (AdeleRing (𝓞 K) K) ξ⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel₀ hξ0, map_one]
      fin_cases i <;> fin_cases j <;> simp [h10, ← hξ, hx, ← hdiag, ← mul_assoc, hinv]
    rw [hg]
    exact Subgroup.mul_mem_sup ⟨a, rfl⟩ ⟨Multiplicative.ofAdd x, rfl⟩

/-! ### The torus-unipotent row -/

/-- The unitriangular matrices with both diagonal entries rational: the entry-side description of
`Z(𝔸_K) · T(K) · U(𝔸_K)`. -/
def torusUnipotentSet : Set (AdelicGL2 (𝓞 K) K) :=
  {g | (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0 ∧
    (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0 ∈ Set.range (algebraMap K (AdeleRing (𝓞 K) K)) ∧
    (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1 ∈ Set.range (algebraMap K (AdeleRing (𝓞 K) K))}

/-- `torusUnipotentSet K` is closed: a finite intersection of closed entry conditions. -/
theorem isClosed_torusUnipotentSet : IsClosed (torusUnipotentSet K) := by
  have hent : ∀ i j : Fin 2, Continuous fun g : AdelicGL2 (𝓞 K) K => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j :=
    fun i j => (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).matrix_elem i j
  simp only [torusUnipotentSet, Set.ofPred_and]
  refine (isClosed_eq (hent 1 0) continuous_const).inter (IsClosed.inter ?_ ?_)
  · exact (isClosed_range_algebraMap_adeleRing K).preimage (hent 0 0)
  · exact (isClosed_range_algebraMap_adeleRing K).preimage (hent 1 1)

/-- `torusUnipotentSet K` is closed under multiplication. -/
theorem mul_mem_torusUnipotentSet {g h : AdelicGL2 (𝓞 K) K} (hg : g ∈ torusUnipotentSet K) (hh : h ∈ torusUnipotentSet K) :
    g * h ∈ torusUnipotentSet K := by
  obtain ⟨hg1, ⟨ξ, hξ⟩, ⟨ξ', hξ'⟩⟩ := hg
  obtain ⟨hh1, ⟨η, hη⟩, ⟨η', hη'⟩⟩ := hh
  have e : ∀ i j : Fin 2, ((g * h : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j =
      (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i 0 * (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 j +
      (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i 1 * (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 j := by
    intro i j; rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨?_, ⟨ξ * η, ?_⟩, ⟨ξ' * η', ?_⟩⟩
  · rw [e, hg1, hh1, zero_mul, mul_zero, add_zero]
  · rw [e, hh1, mul_zero, add_zero, map_mul, hξ, hη]
  · rw [e, hg1, zero_mul, zero_add, map_mul, hξ', hη']

/-- The rational scalar matrices lie in `torusUnipotentSet K`. -/
theorem globalPoints_scalar_mem (a : Kˣ) :
    globalPoints (𝓞 K) K (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom a) ∈
      torusUnipotentSet K := by
  refine ⟨?_, ⟨(a : K), ?_⟩, ⟨(a : K), ?_⟩⟩ <;>
    simp [globalPoints, Matrix.GeneralLinearGroup.map, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.scalar_apply]

/-- The rational diagonal generators lie in `torusUnipotentSet K`. -/
theorem globalPoints_diagOne_mem (a : Kˣ) :
    globalPoints (𝓞 K) K (diagOne a) ∈ torusUnipotentSet K := by
  refine ⟨?_, ⟨(a : K), ?_⟩, ⟨1, ?_⟩⟩ <;>
    simp [globalPoints, Matrix.GeneralLinearGroup.map, RingHom.mapMatrix_apply, Matrix.map_apply, diagOne_coe_apply]

/-- The adèlic unitriangular matrices lie in `torusUnipotentSet K`. -/
theorem unipotentGL2_mem (x : AdeleRing (𝓞 K) K) :
    (unipotentGL2 x : AdelicGL2 (𝓞 K) K) ∈ torusUnipotentSet K := by
  refine ⟨?_, ⟨1, ?_⟩, ⟨1, ?_⟩⟩ <;> simp [unipotentGL2_coe]

/-- Every element of the rational torus, and its inverse, is unitriangular with rational diagonal
entries. -/
theorem mem_of_mem_rationalTorus (g : AdelicGL2 (𝓞 K) K) (hg : g ∈ rationalTorus K) :
    g ∈ torusUnipotentSet K ∧ g⁻¹ ∈ torusUnipotentSet K := by
  rw [rationalTorus, Subgroup.sup_eq_closure] at hg
  refine Subgroup.closure_induction (p := fun g _ => g ∈ torusUnipotentSet K ∧ g⁻¹ ∈ torusUnipotentSet K)
    ?_ ?_ ?_ ?_ hg
  · intro g hg
    rcases hg with hg | hg
    · obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hg
      refine ⟨globalPoints_scalar_mem K a, ?_⟩
      rw [MonoidHom.comp_apply, ← map_inv, ← map_inv]
      exact globalPoints_scalar_mem K a⁻¹
    · obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hg
      refine ⟨globalPoints_diagOne_mem K a, ?_⟩
      rw [MonoidHom.comp_apply, ← map_inv, ← map_inv]
      exact globalPoints_diagOne_mem K a⁻¹
  · have h1 : (1 : AdelicGL2 (𝓞 K) K) ∈ torusUnipotentSet K := by
      rw [← unipotentGL2_zero]; exact unipotentGL2_mem K 0
    exact ⟨h1, by rw [inv_one]; exact h1⟩
  · intro g h _ _ hg hh
    exact ⟨mul_mem_torusUnipotentSet K hg.1 hh.1, by rw [mul_inv_rev]; exact mul_mem_torusUnipotentSet K hh.2 hg.2⟩
  · intro g _ hg
    exact ⟨hg.2, by rw [inv_inv]; exact hg.1⟩

/-- The rational torus-unipotent subgroup is the set of unitriangular matrices with both diagonal
entries rational. -/
theorem coe_rationalTorusUnipotent_eq :
    (rationalTorusUnipotent K : Set (AdelicGL2 (𝓞 K) K)) = torusUnipotentSet K := by
  apply Set.Subset.antisymm
  · intro g hg
    rw [SetLike.mem_coe, rationalTorusUnipotent, Subgroup.sup_eq_closure] at hg
    refine (Subgroup.closure_induction (p := fun g _ => g ∈ torusUnipotentSet K ∧ g⁻¹ ∈ torusUnipotentSet K)
      ?_ ?_ ?_ ?_ hg).1
    · intro g hg
      rcases hg with hg | hg
      · exact mem_of_mem_rationalTorus K g hg
      · obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hg
        exact ⟨unipotentGL2_mem K _, by rw [← map_inv]; exact unipotentGL2_mem K _⟩
    · have h1 : (1 : AdelicGL2 (𝓞 K) K) ∈ torusUnipotentSet K := by
        rw [← unipotentGL2_zero]; exact unipotentGL2_mem K 0
      exact ⟨h1, by rw [inv_one]; exact h1⟩
    · intro g h _ _ hg hh
      exact ⟨mul_mem_torusUnipotentSet K hg.1 hh.1, by rw [mul_inv_rev]; exact mul_mem_torusUnipotentSet K hh.2 hg.2⟩
    · intro g _ hg
      exact ⟨hg.2, by rw [inv_inv]; exact hg.1⟩
  ·
    rintro g ⟨h10, ⟨ξ, hξ⟩, ⟨η, hη⟩⟩
    have : Nontrivial (AdeleRing (𝓞 K) K) := (NumberField.AdeleRing.algebraMap_injective (R := 𝓞 K) (K := K)).nontrivial
    have hdet : (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)).det ≠ 0 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact (Matrix.GeneralLinearGroup.det g).ne_zero
    rw [Matrix.det_fin_two, h10, mul_zero, sub_zero, ← hξ, ← hη, ← map_mul] at hdet
    have hξη : ξ * η ≠ 0 := fun h0 => hdet (by rw [h0, map_zero])
    have hξ0 : ξ ≠ 0 := left_ne_zero_of_mul hξη
    have hη0 : η ≠ 0 := right_ne_zero_of_mul hξη
    set z : Kˣ := Units.mk0 η hη0 with hz
    set a : Kˣ := Units.mk0 ξ hξ0 * (Units.mk0 η hη0)⁻¹ with ha
    set x : AdeleRing (𝓞 K) K := algebraMap K (AdeleRing (𝓞 K) K) ξ⁻¹ * (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1
      with hx
    have hza : ∀ i j : Fin 2, ((globalPoints (𝓞 K) K (Units.map (Matrix.scalar (Fin 2) :
        K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom z) * globalPoints (𝓞 K) K (diagOne a) : AdelicGL2 (𝓞 K) K) :
          Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j =
        if i = j then (if i = 0 then algebraMap K (AdeleRing (𝓞 K) K) ξ else algebraMap K (AdeleRing (𝓞 K) K) η) else 0 := by
      intro i j
      rw [← map_mul]
      change algebraMap K (AdeleRing (𝓞 K) K) (((Matrix.scalar (Fin 2) ((z : Kˣ) : K)) * (diagOne a : Matrix (Fin 2) (Fin 2) K)) i j) = _
      rw [Matrix.scalar_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, Matrix.diagonal_apply,
        diagOne_coe_apply, diagOne_coe_apply]
      fin_cases i <;> fin_cases j <;> simp [hz, ha]
      rw [← map_mul, ← map_mul]
      congr 1
      field_simp
    have hg : g = globalPoints (𝓞 K) K (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom z) *
        globalPoints (𝓞 K) K (diagOne a) * unipotentGL2 x := by
      refine Units.ext (Matrix.ext fun i j => ?_)
      rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hza, hza, unipotentGL2_coe]
      have hinv : algebraMap K (AdeleRing (𝓞 K) K) ξ * algebraMap K (AdeleRing (𝓞 K) K) ξ⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel₀ hξ0, map_one]
      fin_cases i <;> fin_cases j <;> simp [h10, ← hξ, ← hη, hx, ← mul_assoc, hinv]
    rw [hg]
    exact Subgroup.mul_mem_sup (Subgroup.mul_mem_sup ⟨z, rfl⟩ ⟨a, rfl⟩) ⟨Multiplicative.ofAdd x, rfl⟩

/-- `Z(𝔸_K) · Kˣ · U(𝔸_K)` is closed in `GL₂(𝔸_K)`. -/
theorem isClosed_rationalCentreUnipotent :
    IsClosed (rationalCentreUnipotent K : Set (AdelicGL2 (𝓞 K) K)) := by
  rw [coe_rationalCentreUnipotent_eq]; exact isClosed_scalarUnipotentSet K

/-- `Z(𝔸_K) · T(K) · U(𝔸_K)` is closed in `GL₂(𝔸_K)`. -/
theorem isClosed_rationalTorusUnipotent :
    IsClosed (rationalTorusUnipotent K : Set (AdelicGL2 (𝓞 K) K)) := by
  rw [coe_rationalTorusUnipotent_eq]; exact isClosed_torusUnipotentSet K

end AutomorphicForm

end
