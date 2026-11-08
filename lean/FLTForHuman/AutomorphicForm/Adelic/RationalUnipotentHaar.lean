/-
  The rational centre-unipotent and torus-unipotent measures are Haar and right-invariant.

  `rationalCentreUnipotentHaar` (resp. `rationalTorusUnipotentHaar`) is the countable sum over
  `Kˣ` (resp. `Kˣ × Kˣ`) of the translates of the unipotent Haar measure; the two headlines here
  say that it is a **Haar measure** — left-invariant, finite on compacts, positive on open sets —
  and that it is **right-invariant**, which is what makes it descend to the quotient:

  * `isHaarMeasure_rationalCentreUnipotentHaar_and_isMulRightInvariant`,
  * `isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant`.

  The proof is one argument in two vocabularies. Left invariance is checked on the two generators:
  a rational scalar shifts the index `a ↦ a₀ * a` of the sum (the sum is over all of `Kˣ`) and a
  unipotent element acts on the unipotent Haar measure by an additive translation, which fixes it
  because that measure is an additive Haar measure. Commutativity of the subgroup moves the
  right-action to the left-action. Finiteness on compacts is where the discreteness of `K` in
  `𝔸_K` is used: the `(0,0)`-entry of a compact set is compact, so only finitely many `a` occur
  (`NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact`), and each sheet is a chart
  with a continuous left inverse. Positivity on open sets is the same chart argument.

  The closedness of the same two subgroups is the subject of
  `AutomorphicForm/Adelic/RationalUnipotentClosed.lean`; nothing there is imported here.

  Transcribed from `Theorems/Thm_AutomorphicForm_isHaarMeasure_rational{Centre,Torus}UnipotentHaar_and_isMulRightInvariant.lean`
  and their two `S_` files (pinned `aa2d8b3`, 186 + 335 lines). The pin duplicates its prelude —
  `ratCentralHom`, `ratCentralHom_apply_entry`, `ratCentralHom_comm`, `continuous_toAdelicUnipotent`
  — between the two files (26 lines); it is written once here, and the module carries both files'
  wires. The pin's `continuous_unipotentGL2` is the port's general statement in
  `AutomorphicForm/Adelic/ConstantTerm.lean` and is imported, not restated.

  **Wiring.** `spec/check_port.py` owns the declarations here.
  spec-pin: Theorems/Thm_AutomorphicForm_isHaarMeasure_rationalCentreUnipotentHaar_and_isMulRightInvariant.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_isHaarMeasure_rationalCentreUnipotentHaar_and_isMulRightInvariant.lean
  spec-pin: Theorems/Thm_AutomorphicForm_isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.UnipotentQuotient
import FLTForHuman.NumberTheory.AdelicDiscreteness
import FLTForHuman.NumberTheory.AdelicModulus

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel
open Topology Filter
open scoped ENNReal

noncomputable section

namespace AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

/-! ### The shared prelude -/

section Prelude

variable (K : Type) [Field K] [NumberField K]

/-- The rational scalars `Kˣ` as central elements of `GL₂(𝔸_K)`. -/
def ratCentralHom : Kˣ →* AdelicGL2 (𝓞 K) K :=
  (globalPoints (𝓞 K) K).comp
    (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom)

/-- The entries of a rational scalar are `a` on the diagonal and `0` elsewhere. -/
theorem ratCentralHom_apply_entry (a : Kˣ) (i j : Fin 2) :
    ((ratCentralHom K a : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j =
      if i = j then algebraMap K (AdeleRing (𝓞 K) K) a else 0 := by
  change algebraMap K (AdeleRing (𝓞 K) K) ((Matrix.scalar (Fin 2) (a : K)) i j) = _
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

/-- The rational scalars are the idelic scalars restricted to `Kˣ`. -/
theorem ratCentralHom_eq_centralScalar (a : Kˣ) :
    ratCentralHom K a =
      centralScalar (𝓞 K) K
        (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) := by
  have h : ((centralScalar (𝓞 K) K
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) :
        AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
      Matrix.scalar (Fin 2) (algebraMap K (AdeleRing (𝓞 K) K) (a : K)) := rfl
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [ratCentralHom_apply_entry, h, Matrix.scalar_apply, Matrix.diagonal_apply]

/-- Rational scalars commute with every adèlic matrix. -/
theorem ratCentralHom_comm (a : Kˣ) (g : AdelicGL2 (𝓞 K) K) :
    ratCentralHom K a * g = g * ratCentralHom K a := by
  rw [ratCentralHom_eq_centralScalar]
  exact Matrix.GeneralLinearGroup.scalar_commute _ g

/-- The unitriangular embedding is continuous in its additive coordinate. -/
theorem continuous_toAdelicUnipotent : Continuous (toAdelicUnipotent K) :=
  (continuous_unipotentGL2 (R := AdeleRing (𝓞 K) K)).subtype_mk _

end Prelude

/-! ### The rational centre-unipotent measure (index `Kˣ`) -/

namespace CentreUnipotent

variable (K : Type) [Field K] [NumberField K]

/-- The rational scalars sit in the rational centre-unipotent subgroup. -/
theorem mem_of (a : Kˣ) (y : AdeleRing (𝓞 K) K) :
    ratCentralHom K a * unipotentGL2 y ∈ rationalCentreUnipotent K :=
  Subgroup.mul_mem_sup ⟨a, rfl⟩ ⟨Multiplicative.ofAdd y, rfl⟩

/-- Every element of the rational centre-unipotent subgroup is a rational scalar times a
unipotent element. -/
theorem exists_eq (h : AdelicGL2 (𝓞 K) K) (hh : h ∈ rationalCentreUnipotent K) :
    ∃ (a : Kˣ) (y : AdeleRing (𝓞 K) K), h = ratCentralHom K a * unipotentGL2 y := by
  rw [rationalCentreUnipotent, Subgroup.sup_eq_closure] at hh
  refine Subgroup.closure_induction
    (p := fun g _ => ∃ (a : Kˣ) (y : AdeleRing (𝓞 K) K), g = ratCentralHom K a * unipotentGL2 y)
    ?_ ?_ ?_ ?_ hh
  · intro g hg
    rcases hg with hg | hg
    · obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hg
      exact ⟨a, 0, by rw [unipotentGL2_zero, mul_one]; rfl⟩
    · obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hg
      exact ⟨1, Multiplicative.toAdd y, by rw [map_one, one_mul]; rfl⟩
  · exact ⟨1, 0, by rw [map_one, unipotentGL2_zero, mul_one]⟩
  · rintro g g' _ _ ⟨a, y, rfl⟩ ⟨a', y', rfl⟩
    refine ⟨a * a', y + y', ?_⟩
    rw [map_mul, unipotentGL2_add, mul_assoc, ← mul_assoc (unipotentGL2 y), ← ratCentralHom_comm,
      mul_assoc, mul_assoc]
  · rintro g _ ⟨a, y, rfl⟩
    refine ⟨a⁻¹, -y, ?_⟩
    have hn : (unipotentGL2 y : AdelicGL2 (𝓞 K) K)⁻¹ = unipotentGL2 (-y) :=
      inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero])
    rw [mul_inv_rev, hn, ← map_inv, (ratCentralHom_comm K a⁻¹ (unipotentGL2 (-y))).symm]

/-- The rational centre-unipotent subgroup is commutative. -/
theorem comm (h h' : rationalCentreUnipotent K) : h * h' = h' * h := by
  obtain ⟨a, y, ha⟩ := exists_eq K h h.2
  obtain ⟨a', y', ha'⟩ := exists_eq K h' h'.2
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ha, ha']
  rw [mul_assoc, ← mul_assoc (unipotentGL2 y), ← ratCentralHom_comm, mul_assoc, ← unipotentGL2_add,
    mul_assoc, ← mul_assoc (unipotentGL2 y'), ← ratCentralHom_comm, mul_assoc, ← unipotentGL2_add,
    ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, mul_comm a a', add_comm y y']

/-- The `a`-th sheet of the rational centre-unipotent subgroup: the translate of the unipotent
radical by the rational scalar `a`. -/
def sheet (a : Kˣ) (n : adelicUnipotent K) : rationalCentreUnipotent K :=
  ⟨globalPoints (𝓞 K) K (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom a) *
    (n : AdelicGL2 (𝓞 K) K), Subgroup.mul_mem_sup ⟨a, rfl⟩ n.2⟩

theorem sheet_coe (a : Kˣ) (n : adelicUnipotent K) :
    ((sheet K a n : rationalCentreUnipotent K) : AdelicGL2 (𝓞 K) K) =
      ratCentralHom K a * (n : AdelicGL2 (𝓞 K) K) := rfl

theorem continuous_sheet (a : Kˣ) : Continuous (sheet K a) :=
  (continuous_const.mul continuous_subtype_val).subtype_mk _

theorem measurable_sheet (a : Kˣ) : Measurable (sheet K a) := (continuous_sheet K a).measurable

theorem rationalCentreUnipotentHaar_eq :
    rationalCentreUnipotentHaar K = Measure.sum (fun a : Kˣ => (unipotentHaar K).map (sheet K a)) :=
  rfl

/-- Left multiplication by a rational scalar permutes the sheets. -/
theorem map_mul_left_ratCentral (a₀ : Kˣ) :
    (rationalCentreUnipotentHaar K).map (fun h =>
        (⟨ratCentralHom K a₀, Subgroup.mem_sup_left ⟨a₀, rfl⟩⟩ : rationalCentreUnipotent K) * h) =
      rationalCentreUnipotentHaar K := by
  rw [rationalCentreUnipotentHaar_eq, Measure.map_sum (measurable_const_mul _).aemeasurable]
  have : (fun a : Kˣ => ((unipotentHaar K).map (sheet K a)).map
      (fun h => (⟨ratCentralHom K a₀, Subgroup.mem_sup_left ⟨a₀, rfl⟩⟩ : rationalCentreUnipotent K) * h)) =
      (fun a : Kˣ => (unipotentHaar K).map (sheet K a)) ∘ (Equiv.mulLeft a₀) := by
    funext a
    rw [Measure.map_map (measurable_const_mul _) (measurable_sheet K a)]
    simp only [Function.comp_apply, Equiv.coe_mulLeft]
    congr 1
    funext n
    refine Subtype.ext ?_
    change ratCentralHom K a₀ * (ratCentralHom K a * (n : AdelicGL2 (𝓞 K) K)) =
      ratCentralHom K (a₀ * a) * (n : AdelicGL2 (𝓞 K) K)
    rw [map_mul, mul_assoc]
  rw [this, Measure.sum_comp_equiv]

/-- Left multiplication by a unipotent element translates the additive coordinate. -/
theorem map_mul_left_unipotent (y₀ : AdeleRing (𝓞 K) K) :
    (rationalCentreUnipotentHaar K).map (fun h =>
        (⟨unipotentGL2 y₀, Subgroup.mem_sup_right ⟨Multiplicative.ofAdd y₀, rfl⟩⟩ :
          rationalCentreUnipotent K) * h) = rationalCentreUnipotentHaar K := by
  have := isAddHaarMeasure_adelicAddHaar (𝓞 K) K
  rw [rationalCentreUnipotentHaar_eq, Measure.map_sum (measurable_const_mul _).aemeasurable]
  congr 1
  funext a
  rw [Measure.map_map (measurable_const_mul _) (measurable_sheet K a)]
  have hcomp : (fun h => (⟨unipotentGL2 y₀, Subgroup.mem_sup_right ⟨Multiplicative.ofAdd y₀, rfl⟩⟩ :
        rationalCentreUnipotent K) * h) ∘ sheet K a =
      sheet K a ∘ (fun n : adelicUnipotent K => toAdelicUnipotent K y₀ * n) := by
    funext n
    refine Subtype.ext ?_
    change unipotentGL2 y₀ * (ratCentralHom K a * (n : AdelicGL2 (𝓞 K) K)) =
      ratCentralHom K a * (unipotentGL2 y₀ * (n : AdelicGL2 (𝓞 K) K))
    rw [← mul_assoc, ← ratCentralHom_comm, mul_assoc]
  rw [hcomp, ← Measure.map_map (measurable_sheet K a) (measurable_const_mul _)]
  congr 1
  rw [unipotentHaar,
    Measure.map_smul ((adelicAddHaar (𝓞 K) K) (adelicBox K))⁻¹
      (continuous_toAdelicUnipotent K).measurable.aemeasurable,
    Measure.map_smul ((adelicAddHaar (𝓞 K) K) (adelicBox K))⁻¹
      (measurable_const_mul (toAdelicUnipotent K y₀)).aemeasurable,
    Measure.map_map (measurable_const_mul _) (continuous_toAdelicUnipotent K).measurable]
  congr 1
  have h2 : (fun n : adelicUnipotent K => toAdelicUnipotent K y₀ * n) ∘ toAdelicUnipotent K =
      toAdelicUnipotent K ∘ (fun y => y₀ + y) := by
    funext y
    refine Subtype.ext ?_
    change unipotentGL2 y₀ * unipotentGL2 y = unipotentGL2 (y₀ + y)
    rw [unipotentGL2_add]
  rw [h2, ← Measure.map_map (continuous_toAdelicUnipotent K).measurable (measurable_const_add y₀),
    map_add_left_eq_self]

theorem isMulLeftInvariant : (rationalCentreUnipotentHaar K).IsMulLeftInvariant := by
  refine ⟨fun h => ?_⟩
  obtain ⟨a, y, hay⟩ := exists_eq K h h.2
  have : h = (⟨ratCentralHom K a, Subgroup.mem_sup_left ⟨a, rfl⟩⟩ : rationalCentreUnipotent K) *
      ⟨unipotentGL2 y, Subgroup.mem_sup_right ⟨Multiplicative.ofAdd y, rfl⟩⟩ := Subtype.ext hay
  rw [this]
  have hc : (fun x : rationalCentreUnipotent K => (⟨ratCentralHom K a, Subgroup.mem_sup_left ⟨a, rfl⟩⟩ :
        rationalCentreUnipotent K) *
      ⟨unipotentGL2 y, Subgroup.mem_sup_right ⟨Multiplicative.ofAdd y, rfl⟩⟩ * x) =
      (fun x => (⟨ratCentralHom K a, Subgroup.mem_sup_left ⟨a, rfl⟩⟩ : rationalCentreUnipotent K) * x) ∘
        (fun x => (⟨unipotentGL2 y, Subgroup.mem_sup_right ⟨Multiplicative.ofAdd y, rfl⟩⟩ :
          rationalCentreUnipotent K) * x) := by
    funext x; simp only [Function.comp_apply, mul_assoc]
  rw [hc, ← Measure.map_map (measurable_const_mul _) (measurable_const_mul _),
    map_mul_left_unipotent, map_mul_left_ratCentral]

theorem isMulRightInvariant : (rationalCentreUnipotentHaar K).IsMulRightInvariant := by
  have := isMulLeftInvariant K
  refine ⟨fun h => ?_⟩
  have : (fun x : rationalCentreUnipotent K => x * h) = fun x => h * x := funext fun x => comm K x h
  rw [this]; exact map_mul_left_eq_self _ h

theorem sheet_entries (a : Kˣ) (y : AdeleRing (𝓞 K) K) :
    (((ratCentralHom K a * unipotentGL2 y : AdelicGL2 (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0 =
        algebraMap K (AdeleRing (𝓞 K) K) a ∧
      (((ratCentralHom K a * unipotentGL2 y : AdelicGL2 (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1 =
        algebraMap K (AdeleRing (𝓞 K) K) a * y := by
  constructor <;>
  · rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      ratCentralHom_apply_entry, ratCentralHom_apply_entry, unipotentGL2_coe]
    simp

/-- The chart of the `a`-th sheet: unipotent coordinate `y ↦ sheet a (toAdelicUnipotent y)`. -/
def chart (a : Kˣ) (y : AdeleRing (𝓞 K) K) : rationalCentreUnipotent K :=
  sheet K a (toAdelicUnipotent K y)

theorem chart_coe (a : Kˣ) (y : AdeleRing (𝓞 K) K) :
    ((chart K a y : rationalCentreUnipotent K) : AdelicGL2 (𝓞 K) K) =
      ratCentralHom K a * unipotentGL2 y := rfl

theorem continuous_chart (a : Kˣ) : Continuous (chart K a) :=
  (continuous_sheet K a).comp (continuous_toAdelicUnipotent K)

theorem exists_leftInverse_chart (a : Kˣ) :
    ∃ ψ : rationalCentreUnipotent K → AdeleRing (𝓞 K) K, Continuous ψ ∧
      Function.LeftInverse ψ (chart K a) := by
  let ψ : rationalCentreUnipotent K → AdeleRing (𝓞 K) K := fun h =>
    algebraMap K (AdeleRing (𝓞 K) K) ((a⁻¹ : Kˣ) : K) *
      ((((h : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1)
  refine ⟨ψ, ?_, fun y => ?_⟩
  · exact continuous_const.mul
      ((((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).matrix_elem 0
        1).comp continuous_subtype_val))
  · change algebraMap K (AdeleRing (𝓞 K) K) ((a⁻¹ : Kˣ) : K) *
      (((ratCentralHom K a * unipotentGL2 y : AdelicGL2 (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1 = y
    rw [(sheet_entries K a y).2, ← mul_assoc, ← map_mul, Units.val_inv_eq_inv_val,
      inv_mul_cancel₀ a.ne_zero, map_one, one_mul]

theorem measure_sheet_preimage (a : Kˣ) (s : Set (rationalCentreUnipotent K))
    (hs : MeasurableSet s) :
    ((unipotentHaar K).map (sheet K a)) s =
      ((adelicAddHaar (𝓞 K) K) (adelicBox K))⁻¹ * (adelicAddHaar (𝓞 K) K) (chart K a ⁻¹' s) := by
  rw [Measure.map_apply (measurable_sheet K a) hs, unipotentHaar,
    Measure.map_smul ((adelicAddHaar (𝓞 K) K) (adelicBox K))⁻¹
      (continuous_toAdelicUnipotent K).measurable.aemeasurable,
    Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (continuous_toAdelicUnipotent K).measurable ((measurable_sheet K a) hs)]
  rfl

theorem isFiniteMeasureOnCompacts : IsFiniteMeasureOnCompacts (rationalCentreUnipotentHaar K) := by
  have := isAddHaarMeasure_adelicAddHaar (𝓞 K) K
  refine ⟨fun C hC => ?_⟩
  rw [rationalCentreUnipotentHaar_eq, Measure.sum_apply _ hC.measurableSet]
  have e00 : Continuous fun h : rationalCentreUnipotent K =>
      (((h : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0) :=
    ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).matrix_elem 0
      0).comp continuous_subtype_val
  have hfin : {ξ : K | algebraMap K (AdeleRing (𝓞 K) K) ξ ∈ (fun h : rationalCentreUnipotent K =>
      (((h : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0)) '' C}.Finite :=
    NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact K (hC.image e00)
  have hfinU : ((Units.val : Kˣ → K) ⁻¹' {ξ : K |
      algebraMap K (AdeleRing (𝓞 K) K) ξ ∈ (fun h : rationalCentreUnipotent K =>
        (((h : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0)) '' C}).Finite :=
    hfin.preimage Units.val_injective.injOn
  have hzero : ∀ a : Kˣ, a ∉ hfinU.toFinset → ((unipotentHaar K).map (sheet K a)) C = 0 := by
    intro a ha
    rw [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_ofPred_eq] at ha
    rw [Measure.map_apply (measurable_sheet K a) hC.measurableSet]
    have : sheet K a ⁻¹' C = ∅ := by
      ext n
      simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
      intro hn
      apply ha
      refine ⟨sheet K a n, hn, ?_⟩
      obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp n.2
      have : n = toAdelicUnipotent K (Multiplicative.toAdd y) := Subtype.ext hy.symm
      rw [this]
      exact (sheet_entries K a _).1
    rw [this, measure_empty]
  rw [tsum_eq_sum (s := hfinU.toFinset) (fun a ha => hzero a ha)]
  refine ENNReal.sum_lt_top.mpr fun a _ => ?_
  rw [measure_sheet_preimage K a C hC.measurableSet]
  obtain ⟨ψ, hψ, hleft⟩ := exists_leftInverse_chart K a
  have hsub : chart K a ⁻¹' C ⊆ ψ '' C := fun y hy => ⟨chart K a y, hy, hleft y⟩
  refine ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr
    (NumberField.AdelicBox.adelicAddHaar_adelicBox_pos K)) ?_
  exact lt_of_le_of_lt (measure_mono hsub) (hC.image hψ).measure_lt_top

theorem isOpenPosMeasure : (rationalCentreUnipotentHaar K).IsOpenPosMeasure := by
  have := isAddHaarMeasure_adelicAddHaar (𝓞 K) K
  refine ⟨fun U hU hne => ?_⟩
  obtain ⟨h₀, hh₀⟩ := hne
  obtain ⟨a, y, hay⟩ := exists_eq K h₀ h₀.2
  have hchart : chart K a y = h₀ := Subtype.ext hay.symm
  rw [rationalCentreUnipotentHaar_eq, Measure.sum_apply _ hU.measurableSet]
  refine ne_of_gt (lt_of_lt_of_le ?_ (ENNReal.le_tsum a))
  rw [measure_sheet_preimage K a U hU.measurableSet]
  refine ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr
    (NumberField.AdelicBox.adelicAddHaar_adelicBox_lt_top K).ne) ?_
  refine (hU.preimage (continuous_chart K a)).measure_ne_zero _ ⟨y, ?_⟩
  rw [Set.mem_preimage, hchart]; exact hh₀

theorem isHaarMeasure : (rationalCentreUnipotentHaar K).IsHaarMeasure := by
  have := isFiniteMeasureOnCompacts K
  have := isMulLeftInvariant K
  have := isOpenPosMeasure K
  exact ⟨⟩

end CentreUnipotent

/-! ### The rational torus-unipotent measure (index `Kˣ × Kˣ`) -/

namespace TorusUnipotent

variable (K : Type) [Field K] [NumberField K]

/-- The rational diagonal `a ↦ diag(a, 1)` of `GL₂(𝔸_K)`. -/
def diagHom : Kˣ →* AdelicGL2 (𝓞 K) K :=
  (globalPoints (𝓞 K) K).comp (diagOne (A := K))

theorem diagHom_apply_entry (a : Kˣ) (i j : Fin 2) :
    ((diagHom K a : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j =
      if i = j then (if i = 0 then algebraMap K (AdeleRing (𝓞 K) K) a else 1) else 0 := by
  change algebraMap K (AdeleRing (𝓞 K) K) ((diagOne a : Matrix (Fin 2) (Fin 2) K) i j) = _
  rw [diagOne_coe_apply, Matrix.diagonal_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem unipotentGL2_mul_diagHom (a : Kˣ) (y : AdeleRing (𝓞 K) K) :
    unipotentGL2 y * diagHom K a =
      diagHom K a *
        unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ((a⁻¹ : Kˣ) : K) * y) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply,
    Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two, diagHom_apply_entry, diagHom_apply_entry,
    diagHom_apply_entry, diagHom_apply_entry, unipotentGL2_coe]
  have hinv : algebraMap K (AdeleRing (𝓞 K) K) (a : K) *
      algebraMap K (AdeleRing (𝓞 K) K) ((a : K)⁻¹) = 1 := by
    rw [← map_mul, mul_inv_cancel₀ a.ne_zero, map_one]
  fin_cases i <;> fin_cases j <;> simp [← mul_assoc, hinv]

/-- The rational torus `T(K)`, as a map on `Kˣ × Kˣ`. -/
def torus (za : Kˣ × Kˣ) : AdelicGL2 (𝓞 K) K := ratCentralHom K za.1 * diagHom K za.2

theorem torus_mul (za zb : Kˣ × Kˣ) : torus K za * torus K zb = torus K (za * zb) := by
  simp only [torus, Prod.fst_mul, Prod.snd_mul, map_mul]
  rw [mul_assoc, ← mul_assoc (diagHom K za.2), ← ratCentralHom_comm, mul_assoc, mul_assoc]

theorem torus_one : torus K 1 = 1 := by
  simp [torus]

theorem torus_inv (za : Kˣ × Kˣ) : (torus K za)⁻¹ = torus K za⁻¹ :=
  inv_eq_of_mul_eq_one_right (by rw [torus_mul, mul_inv_cancel, torus_one])

theorem unipotentGL2_mul_torus (za : Kˣ × Kˣ) (y : AdeleRing (𝓞 K) K) :
    unipotentGL2 y * torus K za =
      torus K za *
        unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ((za.2⁻¹ : Kˣ) : K) * y) := by
  rw [torus, ← mul_assoc, ← ratCentralHom_comm, mul_assoc, unipotentGL2_mul_diagHom, mul_assoc]

theorem mem_torus (za : Kˣ × Kˣ) : torus K za ∈ rationalTorusUnipotent K :=
  Subgroup.mem_sup_left (Subgroup.mul_mem_sup ⟨za.1, rfl⟩ ⟨za.2, rfl⟩)

theorem mem_unipotent (y : AdeleRing (𝓞 K) K) :
    (unipotentGL2 y : AdelicGL2 (𝓞 K) K) ∈ rationalTorusUnipotent K :=
  Subgroup.mem_sup_right ⟨Multiplicative.ofAdd y, rfl⟩

theorem unipotentGL2_inv (y : AdeleRing (𝓞 K) K) :
    (unipotentGL2 y : AdelicGL2 (𝓞 K) K)⁻¹ = unipotentGL2 (-y) :=
  inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero])

theorem exists_eq_torus (g : AdelicGL2 (𝓞 K) K) (hg : g ∈ rationalTorus K) :
    ∃ za : Kˣ × Kˣ, g = torus K za := by
  rw [rationalTorus, Subgroup.sup_eq_closure] at hg
  refine Subgroup.closure_induction (p := fun g _ => ∃ za : Kˣ × Kˣ, g = torus K za) ?_ ?_ ?_ ?_ hg
  · intro g hg
    rcases hg with hg | hg
    · obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hg
      exact ⟨(a, 1), by show _ = ratCentralHom K a * diagHom K 1; rw [map_one, mul_one]; rfl⟩
    · obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hg
      exact ⟨(1, a), by show _ = ratCentralHom K 1 * diagHom K a; rw [map_one, one_mul]; rfl⟩
  · exact ⟨1, (torus_one K).symm⟩
  · rintro g g' _ _ ⟨za, rfl⟩ ⟨zb, rfl⟩
    exact ⟨za * zb, torus_mul K za zb⟩
  · rintro g _ ⟨za, rfl⟩
    exact ⟨za⁻¹, torus_inv K za⟩

theorem exists_eq (h : AdelicGL2 (𝓞 K) K) (hh : h ∈ rationalTorusUnipotent K) :
    ∃ (za : Kˣ × Kˣ) (y : AdeleRing (𝓞 K) K), h = torus K za * unipotentGL2 y := by
  rw [rationalTorusUnipotent, Subgroup.sup_eq_closure] at hh
  refine Subgroup.closure_induction
    (p := fun g _ => ∃ (za : Kˣ × Kˣ) (y : AdeleRing (𝓞 K) K), g = torus K za * unipotentGL2 y)
    ?_ ?_ ?_ ?_ hh
  · intro g hg
    rcases hg with hg | hg
    · obtain ⟨za, rfl⟩ := exists_eq_torus K g hg
      exact ⟨za, 0, by rw [unipotentGL2_zero, mul_one]⟩
    · obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hg
      exact ⟨1, Multiplicative.toAdd y, by rw [torus_one, one_mul]; rfl⟩
  · exact ⟨1, 0, by rw [torus_one, unipotentGL2_zero, mul_one]⟩
  · rintro g g' _ _ ⟨za, y, rfl⟩ ⟨zb, y', rfl⟩
    refine ⟨za * zb, algebraMap K (AdeleRing (𝓞 K) K) ((zb.2⁻¹ : Kˣ) : K) * y + y', ?_⟩
    rw [mul_assoc, ← mul_assoc (unipotentGL2 y), unipotentGL2_mul_torus, mul_assoc, ← unipotentGL2_add,
      ← mul_assoc, torus_mul]
  · rintro g _ ⟨za, y, rfl⟩
    refine ⟨za⁻¹, algebraMap K (AdeleRing (𝓞 K) K) (((za⁻¹).2⁻¹ : Kˣ) : K) * (-y), ?_⟩
    rw [mul_inv_rev, unipotentGL2_inv, torus_inv, unipotentGL2_mul_torus]

/-- The `za`-th sheet of the rational torus-unipotent subgroup. -/
def sheet (za : Kˣ × Kˣ) (n : adelicUnipotent K) : rationalTorusUnipotent K :=
  ⟨torus K za * (n : AdelicGL2 (𝓞 K) K),
    Subgroup.mul_mem_sup (Subgroup.mul_mem_sup ⟨za.1, rfl⟩ ⟨za.2, rfl⟩) n.2⟩

theorem sheet_coe (za : Kˣ × Kˣ) (n : adelicUnipotent K) :
    ((sheet K za n : rationalTorusUnipotent K) : AdelicGL2 (𝓞 K) K) =
      torus K za * (n : AdelicGL2 (𝓞 K) K) := rfl

theorem continuous_sheet (za : Kˣ × Kˣ) : Continuous (sheet K za) :=
  (continuous_const.mul continuous_subtype_val).subtype_mk _

theorem measurable_sheet (za : Kˣ × Kˣ) : Measurable (sheet K za) :=
  (continuous_sheet K za).measurable

theorem rationalTorusUnipotentHaar_eq :
    rationalTorusUnipotentHaar K = Measure.sum (fun za : Kˣ × Kˣ => (unipotentHaar K).map (sheet K za)) :=
  rfl

/-- Re-scaling the unipotent coordinate of a unipotent element. -/
def scaleN (c : AdeleRing (𝓞 K) K) (n : adelicUnipotent K) : adelicUnipotent K :=
  toAdelicUnipotent K
    (c * ((n : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1)

theorem scaleN_toAdelicUnipotent (c y : AdeleRing (𝓞 K) K) :
    scaleN K c (toAdelicUnipotent K y) = toAdelicUnipotent K (c * y) := by
  have h : ((toAdelicUnipotent K y : adelicUnipotent K) : AdelicGL2 (𝓞 K) K) = unipotentGL2 y := rfl
  simp only [scaleN, h, unipotentGL2_coe]
  congr 2

theorem continuous_scaleN (c : AdeleRing (𝓞 K) K) : Continuous (scaleN K c) :=
  (continuous_toAdelicUnipotent K).comp (continuous_const.mul
    ((((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).matrix_elem 0
      1).comp continuous_subtype_val)))

theorem coe_toAdelicUnipotent (y : AdeleRing (𝓞 K) K) :
    ((toAdelicUnipotent K y : adelicUnipotent K) : AdelicGL2 (𝓞 K) K) = unipotentGL2 y := rfl

theorem exists_eq_toAdelicUnipotent (n : adelicUnipotent K) :
    ∃ y : AdeleRing (𝓞 K) K, n = toAdelicUnipotent K y := by
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp n.2
  exact ⟨Multiplicative.toAdd y, Subtype.ext hy.symm⟩

theorem map_mul_left_principal_adelicAddHaar (u : Kˣ) :
    (adelicAddHaar (𝓞 K) K).map (fun y => algebraMap K (AdeleRing (𝓞 K) K) (u : K) * y) =
      adelicAddHaar (𝓞 K) K :=
  (NumberField.AdelicHaar.measurePreserving_mul_algebraMap_adelicAddHaar K (u : K) u.ne_zero).map_eq

theorem map_scaleN_unipotentHaar (u : Kˣ) :
    (unipotentHaar K).map (scaleN K (algebraMap K (AdeleRing (𝓞 K) K) (u : K))) = unipotentHaar K := by
  rw [unipotentHaar,
    Measure.map_smul ((adelicAddHaar (𝓞 K) K) (adelicBox K))⁻¹
      (continuous_toAdelicUnipotent K).measurable.aemeasurable,
    Measure.map_smul ((adelicAddHaar (𝓞 K) K) (adelicBox K))⁻¹
      (continuous_scaleN K _).measurable.aemeasurable,
    Measure.map_map (continuous_scaleN K _).measurable (continuous_toAdelicUnipotent K).measurable]
  congr 1
  have h2 : scaleN K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)) ∘ toAdelicUnipotent K =
      toAdelicUnipotent K ∘ (fun y => algebraMap K (AdeleRing (𝓞 K) K) (u : K) * y) := by
    funext y; exact scaleN_toAdelicUnipotent K _ y
  rw [h2, ← Measure.map_map (continuous_toAdelicUnipotent K).measurable (measurable_const_mul _),
    map_mul_left_principal_adelicAddHaar]

theorem map_mul_left_unipotentHaar (y₀ : AdeleRing (𝓞 K) K) :
    (unipotentHaar K).map (fun n : adelicUnipotent K => toAdelicUnipotent K y₀ * n) = unipotentHaar K := by
  have := isAddHaarMeasure_adelicAddHaar (𝓞 K) K
  rw [unipotentHaar,
    Measure.map_smul ((adelicAddHaar (𝓞 K) K) (adelicBox K))⁻¹
      (continuous_toAdelicUnipotent K).measurable.aemeasurable,
    Measure.map_smul ((adelicAddHaar (𝓞 K) K) (adelicBox K))⁻¹
      (measurable_const_mul (toAdelicUnipotent K y₀)).aemeasurable,
    Measure.map_map (measurable_const_mul _) (continuous_toAdelicUnipotent K).measurable]
  congr 1
  have h2 : (fun n : adelicUnipotent K => toAdelicUnipotent K y₀ * n) ∘ toAdelicUnipotent K =
      toAdelicUnipotent K ∘ (fun y => y₀ + y) := by
    funext y
    refine Subtype.ext ?_
    change unipotentGL2 y₀ * unipotentGL2 y = unipotentGL2 (y₀ + y)
    rw [unipotentGL2_add]
  rw [h2, ← Measure.map_map (continuous_toAdelicUnipotent K).measurable (measurable_const_add y₀),
    map_add_left_eq_self]

theorem map_mul_right_unipotentHaar (y₀ : AdeleRing (𝓞 K) K) :
    (unipotentHaar K).map (fun n : adelicUnipotent K => n * toAdelicUnipotent K y₀) = unipotentHaar K := by
  have : (fun n : adelicUnipotent K => n * toAdelicUnipotent K y₀) =
      fun n => toAdelicUnipotent K y₀ * n := by
    funext n
    obtain ⟨y, rfl⟩ := exists_eq_toAdelicUnipotent K n
    refine Subtype.ext ?_
    change unipotentGL2 y * unipotentGL2 y₀ = unipotentGL2 y₀ * unipotentGL2 y
    rw [← unipotentGL2_add, ← unipotentGL2_add, add_comm]
  rw [this, map_mul_left_unipotentHaar]

/-- Left multiplication by a rational torus element permutes the sheets. -/
theorem map_mul_left_torus (zb : Kˣ × Kˣ) :
    (rationalTorusUnipotentHaar K).map (fun h =>
        (⟨torus K zb, mem_torus K zb⟩ : rationalTorusUnipotent K) * h) =
      rationalTorusUnipotentHaar K := by
  rw [rationalTorusUnipotentHaar_eq, Measure.map_sum (measurable_const_mul _).aemeasurable]
  have : (fun za : Kˣ × Kˣ => ((unipotentHaar K).map (sheet K za)).map
      (fun h => (⟨torus K zb, mem_torus K zb⟩ : rationalTorusUnipotent K) * h)) =
      (fun za : Kˣ × Kˣ => (unipotentHaar K).map (sheet K za)) ∘ (Equiv.mulLeft zb) := by
    funext za
    rw [Measure.map_map (measurable_const_mul _) (measurable_sheet K za)]
    simp only [Function.comp_apply, Equiv.coe_mulLeft]
    congr 1
    funext n
    refine Subtype.ext ?_
    change torus K zb * (torus K za * (n : AdelicGL2 (𝓞 K) K)) =
      torus K (zb * za) * (n : AdelicGL2 (𝓞 K) K)
    rw [← torus_mul, mul_assoc]
  rw [this, Measure.sum_comp_equiv]

theorem map_mul_left_unipotent (y₀ : AdeleRing (𝓞 K) K) :
    (rationalTorusUnipotentHaar K).map (fun h =>
        (⟨unipotentGL2 y₀, mem_unipotent K y₀⟩ : rationalTorusUnipotent K) * h) =
      rationalTorusUnipotentHaar K := by
  rw [rationalTorusUnipotentHaar_eq, Measure.map_sum (measurable_const_mul _).aemeasurable]
  congr 1
  funext za
  rw [Measure.map_map (measurable_const_mul _) (measurable_sheet K za)]
  have hcomp : (fun h => (⟨unipotentGL2 y₀, mem_unipotent K y₀⟩ : rationalTorusUnipotent K) * h) ∘
      sheet K za =
      sheet K za ∘ (fun n : adelicUnipotent K =>
        toAdelicUnipotent K (algebraMap K (AdeleRing (𝓞 K) K) ((za.2⁻¹ : Kˣ) : K) * y₀) * n) := by
    funext n
    refine Subtype.ext ?_
    change unipotentGL2 y₀ * (torus K za * (n : AdelicGL2 (𝓞 K) K)) =
      torus K za * (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ((za.2⁻¹ : Kˣ) : K) * y₀) *
        (n : AdelicGL2 (𝓞 K) K))
    rw [← mul_assoc, unipotentGL2_mul_torus, mul_assoc]
  rw [hcomp, ← Measure.map_map (measurable_sheet K za) (measurable_const_mul _),
    map_mul_left_unipotentHaar]

theorem isMulLeftInvariant : (rationalTorusUnipotentHaar K).IsMulLeftInvariant := by
  refine ⟨fun h => ?_⟩
  obtain ⟨za, y, hay⟩ := exists_eq K h h.2
  have : h = (⟨torus K za, mem_torus K za⟩ : rationalTorusUnipotent K) *
      ⟨unipotentGL2 y, mem_unipotent K y⟩ := Subtype.ext hay
  rw [this]
  have hc : (fun x : rationalTorusUnipotent K => (⟨torus K za, mem_torus K za⟩ :
        rationalTorusUnipotent K) * ⟨unipotentGL2 y, mem_unipotent K y⟩ * x) =
      (fun x => (⟨torus K za, mem_torus K za⟩ : rationalTorusUnipotent K) * x) ∘
        (fun x => (⟨unipotentGL2 y, mem_unipotent K y⟩ : rationalTorusUnipotent K) * x) := by
    funext x; simp only [Function.comp_apply, mul_assoc]
  rw [hc, ← Measure.map_map (measurable_const_mul _) (measurable_const_mul _),
    map_mul_left_unipotent, map_mul_left_torus]

theorem map_mul_right_torus (zb : Kˣ × Kˣ) :
    (rationalTorusUnipotentHaar K).map (fun h =>
        h * (⟨torus K zb, mem_torus K zb⟩ : rationalTorusUnipotent K)) =
      rationalTorusUnipotentHaar K := by
  rw [rationalTorusUnipotentHaar_eq, Measure.map_sum (measurable_mul_const _).aemeasurable]
  have : (fun za : Kˣ × Kˣ => ((unipotentHaar K).map (sheet K za)).map
      (fun h => h * (⟨torus K zb, mem_torus K zb⟩ : rationalTorusUnipotent K))) =
      (fun za : Kˣ × Kˣ => (unipotentHaar K).map (sheet K za)) ∘ (Equiv.mulRight zb) := by
    funext za
    rw [Measure.map_map (measurable_mul_const _) (measurable_sheet K za)]
    simp only [Function.comp_apply, Equiv.coe_mulRight]
    have hcomp : (fun h => h * (⟨torus K zb, mem_torus K zb⟩ : rationalTorusUnipotent K)) ∘
        sheet K za =
        sheet K (za * zb) ∘ scaleN K (algebraMap K (AdeleRing (𝓞 K) K) ((zb.2⁻¹ : Kˣ) : K)) := by
      funext n
      obtain ⟨y, rfl⟩ := exists_eq_toAdelicUnipotent K n
      refine Subtype.ext ?_
      rw [Function.comp_apply, Function.comp_apply, scaleN_toAdelicUnipotent]
      change torus K za * unipotentGL2 y * torus K zb = torus K (za * zb) * unipotentGL2 _
      rw [mul_assoc, unipotentGL2_mul_torus, ← mul_assoc, torus_mul]
      rfl
    rw [hcomp, ← Measure.map_map (measurable_sheet K _) (continuous_scaleN K _).measurable,
      map_scaleN_unipotentHaar]
  rw [this, Measure.sum_comp_equiv]

theorem map_mul_right_unipotent (y₀ : AdeleRing (𝓞 K) K) :
    (rationalTorusUnipotentHaar K).map (fun h =>
        h * (⟨unipotentGL2 y₀, mem_unipotent K y₀⟩ : rationalTorusUnipotent K)) =
      rationalTorusUnipotentHaar K := by
  rw [rationalTorusUnipotentHaar_eq, Measure.map_sum (measurable_mul_const _).aemeasurable]
  congr 1
  funext za
  rw [Measure.map_map (measurable_mul_const _) (measurable_sheet K za)]
  have hcomp : (fun h => h * (⟨unipotentGL2 y₀, mem_unipotent K y₀⟩ : rationalTorusUnipotent K)) ∘
      sheet K za = sheet K za ∘ (fun n : adelicUnipotent K => n * toAdelicUnipotent K y₀) := by
    funext n
    refine Subtype.ext ?_
    change torus K za * (n : AdelicGL2 (𝓞 K) K) * unipotentGL2 y₀ =
      torus K za * ((n : AdelicGL2 (𝓞 K) K) * unipotentGL2 y₀)
    rw [mul_assoc]
  rw [hcomp, ← Measure.map_map (measurable_sheet K za) (measurable_mul_const _),
    map_mul_right_unipotentHaar]

theorem isMulRightInvariant : (rationalTorusUnipotentHaar K).IsMulRightInvariant := by
  refine ⟨fun h => ?_⟩
  obtain ⟨za, y, hay⟩ := exists_eq K h h.2
  have : h = (⟨torus K za, mem_torus K za⟩ : rationalTorusUnipotent K) *
      ⟨unipotentGL2 y, mem_unipotent K y⟩ := Subtype.ext hay
  rw [this]
  have hc : (fun x : rationalTorusUnipotent K => x * ((⟨torus K za, mem_torus K za⟩ :
        rationalTorusUnipotent K) * ⟨unipotentGL2 y, mem_unipotent K y⟩)) =
      (fun x => x * (⟨unipotentGL2 y, mem_unipotent K y⟩ : rationalTorusUnipotent K)) ∘
        (fun x => x * (⟨torus K za, mem_torus K za⟩ : rationalTorusUnipotent K)) := by
    funext x; simp only [Function.comp_apply, mul_assoc]
  rw [hc, ← Measure.map_map (measurable_mul_const _) (measurable_mul_const _), map_mul_right_torus,
    map_mul_right_unipotent]

theorem torus_apply_entry (za : Kˣ × Kˣ) (i j : Fin 2) :
    ((torus K za : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j =
      if i = j then (if i = 0 then algebraMap K (AdeleRing (𝓞 K) K) ((za.1 * za.2 : Kˣ) : K)
        else algebraMap K (AdeleRing (𝓞 K) K) (za.1 : K)) else 0 := by
  rw [torus, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    ratCentralHom_apply_entry, ratCentralHom_apply_entry, diagHom_apply_entry, diagHom_apply_entry]
  fin_cases i <;> fin_cases j <;> simp [map_mul]

theorem sheet_entries (za : Kˣ × Kˣ) (y : AdeleRing (𝓞 K) K) :
    (((torus K za * unipotentGL2 y : AdelicGL2 (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0 =
        algebraMap K (AdeleRing (𝓞 K) K) ((za.1 * za.2 : Kˣ) : K) ∧
      (((torus K za * unipotentGL2 y : AdelicGL2 (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1 =
        algebraMap K (AdeleRing (𝓞 K) K) ((za.1 * za.2 : Kˣ) : K) * y ∧
      (((torus K za * unipotentGL2 y : AdelicGL2 (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1 =
        algebraMap K (AdeleRing (𝓞 K) K) (za.1 : K) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, torus_apply_entry,
      torus_apply_entry, unipotentGL2_coe]
    simp

/-- The chart of the `za`-th sheet. -/
def chart (za : Kˣ × Kˣ) (y : AdeleRing (𝓞 K) K) : rationalTorusUnipotent K :=
  sheet K za (toAdelicUnipotent K y)

theorem continuous_chart (za : Kˣ × Kˣ) : Continuous (chart K za) :=
  (continuous_sheet K za).comp (continuous_toAdelicUnipotent K)

theorem exists_leftInverse_chart (za : Kˣ × Kˣ) :
    ∃ ψ : rationalTorusUnipotent K → AdeleRing (𝓞 K) K, Continuous ψ ∧
      Function.LeftInverse ψ (chart K za) := by
  let ψ : rationalTorusUnipotent K → AdeleRing (𝓞 K) K := fun h =>
    algebraMap K (AdeleRing (𝓞 K) K) (((za.1 * za.2)⁻¹ : Kˣ) : K) *
      ((((h : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1)
  refine ⟨ψ, ?_, fun y => ?_⟩
  · exact continuous_const.mul
      ((((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).matrix_elem 0
        1).comp continuous_subtype_val))
  · change algebraMap K (AdeleRing (𝓞 K) K) (((za.1 * za.2)⁻¹ : Kˣ) : K) *
      (((torus K za * unipotentGL2 y : AdelicGL2 (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1 = y
    rw [(sheet_entries K za y).2.1, ← mul_assoc, ← map_mul, Units.val_inv_eq_inv_val,
      inv_mul_cancel₀ (za.1 * za.2).ne_zero, map_one, one_mul]

theorem measure_sheet_preimage (za : Kˣ × Kˣ) (s : Set (rationalTorusUnipotent K))
    (hs : MeasurableSet s) :
    ((unipotentHaar K).map (sheet K za)) s =
      ((adelicAddHaar (𝓞 K) K) (adelicBox K))⁻¹ * (adelicAddHaar (𝓞 K) K) (chart K za ⁻¹' s) := by
  rw [Measure.map_apply (measurable_sheet K za) hs, unipotentHaar,
    Measure.map_smul ((adelicAddHaar (𝓞 K) K) (adelicBox K))⁻¹
      (continuous_toAdelicUnipotent K).measurable.aemeasurable,
    Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (continuous_toAdelicUnipotent K).measurable ((measurable_sheet K za) hs)]
  rfl

theorem isFiniteMeasureOnCompacts : IsFiniteMeasureOnCompacts (rationalTorusUnipotentHaar K) := by
  have := isAddHaarMeasure_adelicAddHaar (𝓞 K) K
  refine ⟨fun C hC => ?_⟩
  rw [rationalTorusUnipotentHaar_eq, Measure.sum_apply _ hC.measurableSet]
  have e00 : Continuous fun h : rationalTorusUnipotent K =>
      (((h : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0) :=
    ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).matrix_elem 0
      0).comp continuous_subtype_val
  have e11 : Continuous fun h : rationalTorusUnipotent K =>
      (((h : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1) :=
    ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).matrix_elem 1
      1).comp continuous_subtype_val
  set F₀ : Set K := {ξ : K | algebraMap K (AdeleRing (𝓞 K) K) ξ ∈ (fun h : rationalTorusUnipotent K =>
      (((h : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0)) '' C} with hF₀
  set F₁ : Set K := {ξ : K | algebraMap K (AdeleRing (𝓞 K) K) ξ ∈ (fun h : rationalTorusUnipotent K =>
      (((h : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1)) '' C} with hF₁
  have hfin₀ : F₀.Finite := NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact K (hC.image e00)
  have hfin₁ : F₁.Finite := NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact K (hC.image e11)
  set U₀ : Set Kˣ := (Units.val : Kˣ → K) ⁻¹' F₀ with hU₀
  set U₁ : Set Kˣ := (Units.val : Kˣ → K) ⁻¹' F₁ with hU₁
  have hfinU₀ : U₀.Finite := hfin₀.preimage Units.val_injective.injOn
  have hfinU₁ : U₁.Finite := hfin₁.preimage Units.val_injective.injOn
  set S : Set (Kˣ × Kˣ) := (fun p : Kˣ × Kˣ => (p.2, p.2⁻¹ * p.1)) '' (U₀ ×ˢ U₁) with hS
  have hfinS : S.Finite := (hfinU₀.prod hfinU₁).image _
  have hzero : ∀ za : Kˣ × Kˣ, za ∉ hfinS.toFinset → ((unipotentHaar K).map (sheet K za)) C = 0 := by
    intro za hza
    rw [Set.Finite.mem_toFinset] at hza
    rw [Measure.map_apply (measurable_sheet K za) hC.measurableSet]
    have : sheet K za ⁻¹' C = ∅ := by
      ext n
      simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
      intro hn
      apply hza
      obtain ⟨y, rfl⟩ := exists_eq_toAdelicUnipotent K n
      refine ⟨(za.1 * za.2, za.1), ⟨?_, ?_⟩, ?_⟩
      · show ((za.1 * za.2 : Kˣ) : K) ∈ F₀
        exact ⟨sheet K za (toAdelicUnipotent K y), hn, (sheet_entries K za y).1⟩
      · show ((za.1 : Kˣ) : K) ∈ F₁
        exact ⟨sheet K za (toAdelicUnipotent K y), hn, (sheet_entries K za y).2.2⟩
      · simp only
        rw [← mul_assoc, inv_mul_cancel, one_mul]
    rw [this, measure_empty]
  rw [tsum_eq_sum (s := hfinS.toFinset) (fun za hza => hzero za hza)]
  refine ENNReal.sum_lt_top.mpr fun za _ => ?_
  rw [measure_sheet_preimage K za C hC.measurableSet]
  obtain ⟨ψ, hψ, hleft⟩ := exists_leftInverse_chart K za
  have hsub : chart K za ⁻¹' C ⊆ ψ '' C := fun y hy => ⟨chart K za y, hy, hleft y⟩
  refine ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr
    (NumberField.AdelicBox.adelicAddHaar_adelicBox_pos K)) ?_
  exact lt_of_le_of_lt (measure_mono hsub) (hC.image hψ).measure_lt_top

theorem isOpenPosMeasure : (rationalTorusUnipotentHaar K).IsOpenPosMeasure := by
  have := isAddHaarMeasure_adelicAddHaar (𝓞 K) K
  refine ⟨fun U hU hne => ?_⟩
  obtain ⟨h₀, hh₀⟩ := hne
  obtain ⟨za, y, hay⟩ := exists_eq K h₀ h₀.2
  have hchart : chart K za y = h₀ := Subtype.ext hay.symm
  rw [rationalTorusUnipotentHaar_eq, Measure.sum_apply _ hU.measurableSet]
  refine ne_of_gt (lt_of_lt_of_le ?_ (ENNReal.le_tsum za))
  rw [measure_sheet_preimage K za U hU.measurableSet]
  refine ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr
    (NumberField.AdelicBox.adelicAddHaar_adelicBox_lt_top K).ne) ?_
  refine (hU.preimage (continuous_chart K za)).measure_ne_zero _ ⟨y, ?_⟩
  rw [Set.mem_preimage, hchart]; exact hh₀

theorem isHaarMeasure : (rationalTorusUnipotentHaar K).IsHaarMeasure := by
  have := isFiniteMeasureOnCompacts K
  have := isMulLeftInvariant K
  have := isOpenPosMeasure K
  exact ⟨⟩

end TorusUnipotent

/-- `rationalCentreUnipotentHaar` is a Haar measure, and it is right-invariant. -/
theorem isHaarMeasure_rationalCentreUnipotentHaar_and_isMulRightInvariant
    (K : Type) [Field K] [NumberField K] :
    (rationalCentreUnipotentHaar K).IsHaarMeasure ∧
      (rationalCentreUnipotentHaar K).IsMulRightInvariant :=
  ⟨CentreUnipotent.isHaarMeasure K, CentreUnipotent.isMulRightInvariant K⟩

/-- `rationalTorusUnipotentHaar` is a Haar measure, and it is right-invariant. -/
theorem isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant
    (K : Type) [Field K] [NumberField K] :
    (rationalTorusUnipotentHaar K).IsHaarMeasure ∧
      (rationalTorusUnipotentHaar K).IsMulRightInvariant :=
  ⟨TorusUnipotent.isHaarMeasure K, TorusUnipotent.isMulRightInvariant K⟩

end AutomorphicForm

end
