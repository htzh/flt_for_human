/-
The `archHeight`-truncated window has a compact cover modulo `GL₂(F)`.

`AutoForm.WindowedSiegel.exists_isCompact_cover_of_archHeight_le` (410 pin lines): for `c > 0` there is a
**compact** `K ⊆ AdelicGL₂(𝓞 F, F)` such that every point of the integral windowed Siegel set with
`archHeight ≤ T'` is a `GL₂(F)`-translate of an element of `K`.  It is the compactness input of every
`archHeight`-cut argument — a consumer replaces "bounded height" by "compact modulo the rational group" —
and its three premises are `Adelic/Siegel/WindowCriterion.lean` (the window's criterion) and the two
number-field leaves SET-AF107F landed (`UnitsLog`, `MixedEmbedding`).

The proof is the pin's `LowCover` engine: balance the archimedean local heights against the
`archHeight` by Dirichlet units, translate the `x`-coordinate by an algebraic integer, and cancel the
determinant by an archimedean idele whose component norms are prescribed.  The compact set is the
centre-cut Siegel set at the balanced window inside the capped height; the translate is upper
triangular, and the covering element is the archimedean idele.

## The rows

* `AutomorphicForm.WindowedSiegel.exists_isCompact_cover_of_archHeight_le` — 410 pin `S_` lines.

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AutomorphicForm_WindowedSiegel_exists_isCompact_cover_of_archHeight_le.lean>

spec-pin: Theorems/Thm_AutomorphicForm_WindowedSiegel_exists_isCompact_cover_of_archHeight_le.lean
spec-pin: P2M/Sol/S_AutomorphicForm_WindowedSiegel_exists_isCompact_cover_of_archHeight_le.lean

## Port notes (order AF108G, ported at pin `aa2d8b3` against the port's mathlib `v4.34.0`)

* **Namespaces.** The pin's generated label `M4aP1R` comes off; its `LowCover` is kept under the
  subject namespace the `Siegel/` directory uses, so the twelve helpers and the assembly row are
  `AutomorphicForm.WindowedSiegel.LowCover.*` and the headline stays
  `AutomorphicForm.WindowedSiegel.exists_isCompact_cover_of_archHeight_le` (the statement's own
  namespace, kept).  Pin declaration names are unchanged.
* **Substitutions (four, measured — not re-derived).**  The pin re-declares four helpers that the port
  already owns; the rows below import them instead of transcribing:
  - `archIdele` (pin `:34`, 12 lines) → `AutomorphicForm.Ws1.Cover.archIdele`
    (`AutomorphicForm/Adelic/Siegel/CentreCutCover.lean`), statement-identical;
  - `glFin_centralScalar_archIdele` (pin `:46`, 11 lines) → `AutomorphicForm.Ws1.Cover.…`, same body;
  - `algebraMap_coe_mem_integralFiniteAdeles` (pin `:89`, 7 lines) →
    `AutomorphicForm.Ws1.Cover.…`, statement-identical;
  - `exists_norm_eq` (pin `:23`, 11 lines) → `AutomorphicForm.exists_norm_eq`
    (`AutomorphicForm/Adelic/Siegel/DetWindowCover.lean`), statement-identical up to the binder name
    (`v` for the pin's `w`).
  Consequently the two modules above join the import list (`CentreCutCover`, `DetWindowCover`) —
  both sit *below* this new home and above nothing that imports it, so there is no cycle.
  `archComponent_centralScalar_archIdele_apply` is *not* substituted: the port's
  `Ws1.Cover.archComponent_centralScalar_archIdele` is the conjunction form, a different wire row, and
  the pin's `if i = j` form is derived here from that conjunction (`fin_cases` on the two indices).
* **Surface reduction (one, measured).** The pin's `solution` (`:398`) is a term-mode alias of
  `exists_isCompact_cover_of_archHeight_le_impl` **and** of the `Theorems/` wrapper's row — the same
  `nhash` (`5aa1facbae08cfa344dc`) three times.  As in order AF107F's `UnitsLog`, the alias is dropped
  and the headline carries the statement; 14 module declarations against the pin's 19
  (19 = 4 substitutions + 1 dropped alias + 14).
* **Proof adaptations (statements unchanged).**
  - the pin's `exists_norm_eq F w …` loses its explicit `F` at the substituted port name;
  - `xAt_im_of_isReal` is proved through the port's `Ws1.Cover.im_xCoord_eq_zero` /
    `im_extensionEmbedding_of_isReal` (the pin unfolds `xCoord` by hand);
  - `if_pos`/`if_neg` (deprecated in `v4.34.0`) are not used: the four `S`-entries are taken as the
    projections of the port's `archComponent_centralScalar_archIdele`;
  - `sum_mult_eq` is spelled `InfinitePlace.sum_mult_eq` (mathlib's, as in the pin).
* **`check_port`**: **14 ok, 0 mismatch, 0 missing, 0 own, 0 kw**.  Engine diff over the two
  `spec-pin:` sources: pin decls 19, module decls 14, **14 by hash, 0 by name, 0 unaccounted**
  (19 − 4 substitutions − 1 dropped alias = 14).
* **Axioms**: all 14 public declarations depend on a subset of
  `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.  Visibility is the pin's: 14 public,
  0 private, so there is no `private`-promotion question for this module.
* **`dedup --within`**: 1 cluster, 14 lines — `exists_isCompact_cover_of_archHeight_le_impl` ↔
  `exists_isCompact_cover_of_archHeight_le` (identical statements).  This is the pin's own
  headline↔engine pair (`S_…:384` against the `Theorems/` row; the pin spells the same statement a
  third time as `solution` at `:398`), kept for faithfulness.
* **`move_dead --dry-run`**: 0 declarations, 0 lines.
* **Heartbeat probe (recorded, never installed)**: the file is silent at the 200 k edit-loop cap and
  a locked `lake build` is warning-free, so **no `set_option maxHeartbeats` is needed or installed**.
  Bisected pair: **59000 heartbeats fail / 60000 pass**, both inside `lowRegion_cover` (`choose a ha
  using hr`, and the closing `linarith`s of `hbal`); the downward ladder's 40000 fails too, and
  70000 / 100000 / 200000 pass.  Module floor (the seven `:= by` proofs replaced by `sorry`, the four
  `:= rfl` entries and `def upperGL` kept): silent at cap **1000**, so the cost is in the proof, not
  in the types.
* **Collision probe**: `tmp/af108/collision-probe.lean` cannot yet run set-wide — order D's
  `ModularCurve/X1/RegularDifferentialsCuspForm.olean` does not exist.  With that one import removed
  (`tmp/af108/collision-probe-G.lean`) it prints nothing, so none of this module's 14 public full
  names collides with the port.
-/

import FLTForHuman.AutomorphicForm.Adelic.Siegel.WindowCriterion
import FLTForHuman.AutomorphicForm.Adelic.Siegel.CentreCutCover
import FLTForHuman.AutomorphicForm.Adelic.Siegel.DetWindowCover
import FLTForHuman.NumberTheory.NumberField.MixedEmbedding
import FLTForHuman.NumberTheory.NumberField.UnitsLog
import Mathlib.Tactic

open NumberField NumberField.InfinitePlace IsDedekindDomain Matrix Set

open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates
  AutomorphicForm.SiegelReduction AutomorphicForm.SiegelCovering NumberField.AdelicLevel
  NumberField.AdelicVolume NumberField.SiegelVolume

open AutomorphicForm.Ws1.Cover

set_option autoImplicit false

noncomputable section

namespace AutomorphicForm

namespace WindowedSiegel

namespace LowCover

variable {F : Type} [Field F] [NumberField F]

theorem archComponent_centralScalar_archIdele_apply (a : ∀ w : InfinitePlace F, (w.Completion)ˣ)
    (w : InfinitePlace F) (i j : Fin 2) :
    ((archComponent F w (glArch (𝓞 F) F (centralScalar (𝓞 F) F (archIdele F a))) :
        GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j
      = if i = j then (a w : w.Completion) else 0 := by
  obtain ⟨h00, h01, h10, h11⟩ := Ws1.Cover.archComponent_centralScalar_archIdele F w a
  fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]

section UpperGL

variable {L : Type*} [Field L]

def upperGL (e b : L) (he : e ≠ 0) : GL (Fin 2) L :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![e, b; 0, 1]
    (by rw [Matrix.det_fin_two_of]; simp [he])

@[scoped simp] theorem upperGL_apply_zero_zero (e b : L) (he : e ≠ 0) :
    (upperGL e b he : Matrix (Fin 2) (Fin 2) L) 0 0 = e := rfl
@[scoped simp] theorem upperGL_apply_zero_one (e b : L) (he : e ≠ 0) :
    (upperGL e b he : Matrix (Fin 2) (Fin 2) L) 0 1 = b := rfl
@[scoped simp] theorem upperGL_apply_one_zero (e b : L) (he : e ≠ 0) :
    (upperGL e b he : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := rfl
@[scoped simp] theorem upperGL_apply_one_one (e b : L) (he : e ≠ 0) :
    (upperGL e b he : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 := rfl

end UpperGL

theorem glFin_globalPoints_upperUnit_mem (ε : (𝓞 F)ˣ) (β : 𝓞 F)
    (hε : (((ε : 𝓞 F) : F)) ≠ 0) :
    glFin (𝓞 F) F (globalPoints (𝓞 F) F (upperGL ((ε : 𝓞 F) : F) (β : F) hε))
      ∈ finiteIntegralGL2 (𝓞 F) F := by
  set γ : GL (Fin 2) F := upperGL ((ε : 𝓞 F) : F) (β : F) hε with hγ

  have hε' : (((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) ≠ 0 :=
    RingOfIntegers.coe_ne_zero_iff.mpr (ε⁻¹).ne_zero
  have hεε' : (((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * ((ε : 𝓞 F) : F) = 1 := by
    rw [RingOfIntegers.coe_eq_algebraMap, RingOfIntegers.coe_eq_algebraMap, ← map_mul,
      show ((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * (ε : 𝓞 F) = 1 from ε.inv_mul, map_one]
  have hε'ε : ((ε : 𝓞 F) : F) * (((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) = 1 := by
    rw [mul_comm]; exact hεε'
  set γ' : GL (Fin 2) F := upperGL (((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F)
    (-((((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * β : 𝓞 F) : F)) hε' with hγ'
  have hinv : γ⁻¹ = γ' := by
    refine inv_eq_of_mul_eq_one_right ?_
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, Units.val_one]
    have hb : ((((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * β : 𝓞 F) : F)
        = (((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * (β : F) := by
      rw [RingOfIntegers.coe_eq_algebraMap, RingOfIntegers.coe_eq_algebraMap,
        RingOfIntegers.coe_eq_algebraMap, map_mul]
    fin_cases i <;> fin_cases j <;> simp [hγ, hγ', hb]
  rw [mem_finiteIntegralGL2_iff]
  constructor
  · intro i j
    rw [glFin_globalPoints_apply]
    fin_cases i <;> fin_cases j
    · exact algebraMap_coe_mem_integralFiniteAdeles F (ε : 𝓞 F)
    · exact algebraMap_coe_mem_integralFiniteAdeles F β
    · simpa [hγ] using algebraMap_coe_mem_integralFiniteAdeles F 0
    · simpa [hγ] using algebraMap_coe_mem_integralFiniteAdeles F 1
  · intro i j
    rw [← map_inv, ← map_inv, hinv, glFin_globalPoints_apply]
    fin_cases i <;> fin_cases j
    · exact algebraMap_coe_mem_integralFiniteAdeles F ((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F)
    · simpa [hγ'] using
        algebraMap_coe_mem_integralFiniteAdeles F (-(((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * β))
    · simpa [hγ'] using algebraMap_coe_mem_integralFiniteAdeles F 0
    · simpa [hγ'] using algebraMap_coe_mem_integralFiniteAdeles F 1

theorem xAt_im_of_isReal {w : InfinitePlace F} (hw : IsReal w) (g : AdelicGL2 (𝓞 F) F) :
    (xAt w g).im = 0 := by
  refine Ws1.Cover.im_xCoord_eq_zero _ fun i j => ?_
  rw [Matrix.map_apply]
  exact Ws1.Cover.im_extensionEmbedding_of_isReal F hw _

omit [NumberField F] in
theorem extensionEmbedding_coe_eq (w : InfinitePlace F) (x : F) :
    Completion.extensionEmbedding w (x : w.Completion) = w.embedding x := by
  exact Completion.extensionEmbedding_coe (v := w) (WithAbs.toAbs w.1 x)

omit [NumberField F] in
theorem embedding_im_of_isReal {w : InfinitePlace F} (hw : IsReal w) (x : F) :
    (w.embedding x).im = 0 := by
  rw [← embedding_of_isReal_apply hw]
  exact Complex.ofReal_im _

theorem place_laws (a : ∀ w : InfinitePlace F, (w.Completion)ˣ) {ε β : F} (hε : ε ≠ 0)
    (x : AdelicGL2 (𝓞 F) F) (w : InfinitePlace F) :
    let y := centralScalar (𝓞 F) F (archIdele F a) *
      (globalPoints (𝓞 F) F (upperGL ε β hε) * x)
    localHeight (archComponent F w (glArch (𝓞 F) F y))
        = w ε * localHeight (archComponent F w (glArch (𝓞 F) F x)) ∧
      xAt w y = w.embedding ε * xAt w x + w.embedding β ∧
      archDetNorm w y = ‖(a w : w.Completion)‖ ^ 2 * (w ε * archDetNorm w x) := by
  intro y
  set S := archComponent F w (glArch (𝓞 F) F (centralScalar (𝓞 F) F (archIdele F a))) with hS
  set G := archComponent F w (glArch (𝓞 F) F
    (globalPoints (𝓞 F) F (upperGL ε β hε))) with hG
  set X := archComponent F w (glArch (𝓞 F) F x) with hX
  have hy : archComponent F w (glArch (𝓞 F) F y) = S * (G * X) := by
    simp only [y, map_mul, hS, hG, hX]
  have ha0 : (a w : w.Completion) ≠ 0 := (a w).ne_zero
  have hS00 : (S : Matrix (Fin 2) (Fin 2) w.Completion) 0 0 = (a w : w.Completion) := by
    rw [hS]; exact (Ws1.Cover.archComponent_centralScalar_archIdele F w a).1
  have hS01 : (S : Matrix (Fin 2) (Fin 2) w.Completion) 0 1 = 0 := by
    rw [hS]; exact (Ws1.Cover.archComponent_centralScalar_archIdele F w a).2.1
  have hS10 : (S : Matrix (Fin 2) (Fin 2) w.Completion) 1 0 = 0 := by
    rw [hS]; exact (Ws1.Cover.archComponent_centralScalar_archIdele F w a).2.2.1
  have hS11 : (S : Matrix (Fin 2) (Fin 2) w.Completion) 1 1 = (a w : w.Completion) := by
    rw [hS]; exact (Ws1.Cover.archComponent_centralScalar_archIdele F w a).2.2.2
  have hG00 : (G : Matrix (Fin 2) (Fin 2) w.Completion) 0 0 = (ε : w.Completion) := by
    rw [hG, archComponent_globalPoints_apply, upperGL_apply_zero_zero]
  have hG01 : (G : Matrix (Fin 2) (Fin 2) w.Completion) 0 1 = (β : w.Completion) := by
    rw [hG, archComponent_globalPoints_apply, upperGL_apply_zero_one]
  have hG10 : (G : Matrix (Fin 2) (Fin 2) w.Completion) 1 0 = 0 := by
    rw [hG, archComponent_globalPoints_apply, upperGL_apply_one_zero]
    exact NumberField.InfinitePlace.Completion.ext (by simp)
  have hG11 : (G : Matrix (Fin 2) (Fin 2) w.Completion) 1 1 = 1 := by
    rw [hG, archComponent_globalPoints_apply, upperGL_apply_one_one]
    exact NumberField.InfinitePlace.Completion.ext (by simp)
  have hε0 : ((ε : F) : w.Completion) ≠ 0 := by
    rw [← norm_pos_iff, norm_coe_completion]; exact w.pos_iff.mpr hε
  refine ⟨?_, ?_, ?_⟩
  ·
    rw [hy, localHeight_upper_entries_mul ha0 hS00 hS10 hS11,
      localHeight_upper_entries_mul one_ne_zero hG00 hG10 hG11, div_self (norm_ne_zero_iff.mpr ha0),
      one_mul, norm_one, div_one, norm_coe_completion]
  ·
    set φ := Completion.extensionEmbedding w with hφ
    have hmat : ((S * (G * X) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2)
        w.Completion).map φ = ((Matrix.GeneralLinearGroup.map φ S *
          (Matrix.GeneralLinearGroup.map φ G * Matrix.GeneralLinearGroup.map φ X) :
            GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) := by
      simp only [Units.val_mul, coe_map, Matrix.map_mul]
    unfold xAt
    rw [hy, hmat]
    have e : ∀ (T : GL (Fin 2) w.Completion) (i j : Fin 2),
        ((Matrix.GeneralLinearGroup.map φ T : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) i j
          = φ ((T : Matrix (Fin 2) (Fin 2) w.Completion) i j) := by
      intro T i j; rw [coe_map, Matrix.map_apply]
    rw [xCoord_upper_entries_mul (s := Matrix.GeneralLinearGroup.map φ S)
        ((map_ne_zero φ).mpr ha0) (by rw [e, hS00]) (by rw [e, hS01, map_zero])
        (by rw [e, hS10, map_zero]) (by rw [e, hS11]),
      xCoord_upper_entries_mul (s := Matrix.GeneralLinearGroup.map φ G) (t := (1 : ℂ))
        one_ne_zero (by rw [e, hG00]) (by rw [e, hG01]) (by rw [e, hG10, map_zero])
        (by rw [e, hG11, map_one]),
      div_self ((map_ne_zero φ).mpr ha0), one_mul, zero_div, add_zero, div_one, div_one,
      ← hX, coe_map, hφ, extensionEmbedding_coe_eq, extensionEmbedding_coe_eq]
  ·
    unfold archDetNorm
    rw [hy, det_upper_entries_mul hS00 hS10 hS11, det_upper_entries_mul hG00 hG10 hG11, ← hX,
      norm_mul, norm_mul, norm_mul, norm_mul, norm_one, mul_one, norm_coe_completion]
    ring

open Real in

theorem lowRegion_cover (c u T' : ℝ) (hc : 0 < c) :
    ∃ K : Set (AdelicGL2 (𝓞 F) F), IsCompact K ∧
      ∀ x ∈ integralWindowedSiegelSet F c u, archHeight F (glArch (𝓞 F) F x) ≤ T' →
        ∃ γ : GL (Fin 2) F, ∃ z : (AdeleRing (𝓞 F) F)ˣ,
          (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
            globalPoints (𝓞 F) F γ * x * centralScalar (𝓞 F) F z ∈ K := by
  classical

  obtain ⟨R, hR⟩ := NumberField.Units.exists_forall_abs_sub_mult_mul_log_le F
  obtain ⟨U, hU⟩ := NumberField.mixedEmbedding.exists_forall_norm_embedding_sub_le F
  set n : ℝ := (Module.finrank ℚ F : ℝ) with hn
  have hnpos : 0 < n := by
    rw [hn]; exact_mod_cast Module.finrank_pos
  by_cases hT : T' < c
  · refine ⟨∅, isCompact_empty, fun x hx hxT => ?_⟩
    exact absurd (lt_of_le_of_lt (hx.2.1.trans hxT) hT) (lt_irrefl _)
  push Not at hT
  have hT0 : 0 < T' := hc.trans_le hT
  set lo : ℝ := Real.log c / n - R with hlo
  set hi : ℝ := Real.log T' / n + R with hhi
  refine ⟨centreCutSiegelSet F (Real.exp lo) U 1 1 ∩
      {g | ∀ w : InfinitePlace F,
        localHeight (archComponent F w (glArch (𝓞 F) F g)) ≤ Real.exp hi},
    isCompact_centreCutSiegelSet_inter_heightCap F
      (Real.exp_pos lo) one_pos, fun x hx hxT => ?_⟩
  obtain ⟨hfin, hHc, hwin⟩ := hx

  have hH0 : 0 < archHeight F (glArch (𝓞 F) F x) := hc.trans_le hHc
  have hh0 : ∀ w : InfinitePlace F, 0 < localHeight (archComponent F w (glArch (𝓞 F) F x)) :=
    fun w => localHeight_pos _
  have hlogH : Real.log (archHeight F (glArch (𝓞 F) F x))
      = ∑ w : InfinitePlace F,
          (w.mult : ℝ) * Real.log (localHeight (archComponent F w (glArch (𝓞 F) F x))) := by
    unfold archHeight
    rw [Real.log_prod]
    · refine Finset.sum_congr rfl fun w _ => ?_
      rw [Real.log_pow]
    · intro w _
      exact (pow_pos (hh0 w) _).ne'
  have hsum_mult : ∑ w : InfinitePlace F, (w.mult : ℝ) = n := by
    rw [hn, ← InfinitePlace.sum_mult_eq (K := F), Nat.cast_sum]

  set t : InfinitePlace F → ℝ := fun w =>
    (w.mult : ℝ) * (Real.log (archHeight F (glArch (𝓞 F) F x)) / n)
      - (w.mult : ℝ) * Real.log (localHeight (archComponent F w (glArch (𝓞 F) F x))) with htdef
  have ht : ∑ w, t w = 0 := by
    simp only [htdef]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum_mult, ← hlogH]
    have : n * (Real.log (archHeight F (glArch (𝓞 F) F x)) / n)
        = Real.log (archHeight F (glArch (𝓞 F) F x)) := by
      field_simp
    rw [this, sub_self]
  obtain ⟨ε, hε⟩ := hR t ht
  have he0 : (((ε : 𝓞 F) : F)) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr ε.ne_zero
  have hwe : ∀ w : InfinitePlace F, 0 < w ((ε : 𝓞 F) : F) := fun w => w.pos_iff.mpr he0
  have hR0 : 0 ≤ R := (abs_nonneg _).trans (hε (Classical.arbitrary _))

  have hbal : ∀ w : InfinitePlace F,
      Real.exp lo ≤ w ((ε : 𝓞 F) : F) * localHeight (archComponent F w (glArch (𝓞 F) F x)) ∧
      w ((ε : 𝓞 F) : F) * localHeight (archComponent F w (glArch (𝓞 F) F x)) ≤ Real.exp hi := by
    intro w
    have hm1 : (1 : ℝ) ≤ w.mult := one_le_mult
    have hy0 : 0 < w ((ε : 𝓞 F) : F) * localHeight (archComponent F w (glArch (𝓞 F) F x)) :=
      mul_pos (hwe w) (hh0 w)
    have hεw := hε w
    have hkey : t w - (w.mult : ℝ) * Real.log (w ((ε : 𝓞 F) : F))
        = (w.mult : ℝ) * (Real.log (archHeight F (glArch (𝓞 F) F x)) / n
          - Real.log (w ((ε : 𝓞 F) : F) *
              localHeight (archComponent F w (glArch (𝓞 F) F x)))) := by
      simp only [htdef]
      rw [Real.log_mul (hwe w).ne' (hh0 w).ne']
      ring
    rw [hkey, abs_le] at hεw
    obtain ⟨hlow, hup⟩ := hεw
    set d := Real.log (archHeight F (glArch (𝓞 F) F x)) / n
      - Real.log (w ((ε : 𝓞 F) : F) * localHeight (archComponent F w (glArch (𝓞 F) F x))) with hd
    have h1 : d ≤ R := by
      by_cases hd0 : 0 ≤ d
      · nlinarith
      · linarith
    have h2 : -R ≤ d := by
      by_cases hd0 : d ≤ 0
      · nlinarith
      · linarith
    have hLc : Real.log c / n ≤ Real.log (archHeight F (glArch (𝓞 F) F x)) / n :=
      div_le_div_of_nonneg_right (Real.log_le_log hc hHc) hnpos.le
    have hLT : Real.log (archHeight F (glArch (𝓞 F) F x)) / n ≤ Real.log T' / n :=
      div_le_div_of_nonneg_right (Real.log_le_log hH0 hxT) hnpos.le
    constructor
    · rw [← Real.exp_log hy0]
      exact Real.exp_le_exp.mpr (by rw [hlo]; linarith)
    · rw [← Real.exp_log hy0]
      exact Real.exp_le_exp.mpr (by rw [hhi]; linarith)

  set ξ : InfinitePlace F → ℂ := fun w => -(w.embedding ((ε : 𝓞 F) : F) * xAt w x) with hξdef
  have hξ : ∀ w : InfinitePlace F, w.IsReal → (ξ w).im = 0 := by
    intro w hw
    simp only [hξdef, Complex.neg_im, Complex.mul_im, embedding_im_of_isReal hw,
      xAt_im_of_isReal hw, mul_zero, zero_mul, add_zero, neg_zero]
  obtain ⟨β, hβ⟩ := hU ξ hξ

  have hD0 : ∀ w : InfinitePlace F, 0 < w ((ε : 𝓞 F) : F) * archDetNorm w x :=
    fun w => mul_pos (hwe w) (archDetNorm_pos w x)
  have hr : ∀ w : InfinitePlace F, ∃ aw : (w.Completion)ˣ,
      ‖(aw : w.Completion)‖ ^ 2 * (w ((ε : 𝓞 F) : F) * archDetNorm w x) = 1 := by
    intro w
    have hsq : 0 < Real.sqrt (w ((ε : 𝓞 F) : F) * archDetNorm w x) := Real.sqrt_pos.mpr (hD0 w)
    obtain ⟨a0, ha0⟩ := exists_norm_eq w
      (r := (Real.sqrt (w ((ε : 𝓞 F) : F) * archDetNorm w x))⁻¹) (by positivity)
    have ha0ne : a0 ≠ 0 := by
      rw [← norm_pos_iff, ha0]; positivity
    refine ⟨Units.mk0 a0 ha0ne, ?_⟩
    rw [Units.val_mk0, ha0, inv_pow, Real.sq_sqrt (hD0 w).le, inv_mul_cancel₀ (hD0 w).ne']
  choose a ha using hr

  refine ⟨upperGL ((ε : 𝓞 F) : F) (β : F) he0, archIdele F a, rfl, ?_⟩
  rw [SiegelCovering.mul_centralScalar_comm]
  have hlaw := fun w : InfinitePlace F =>
    place_laws (F := F) a (β := (β : F)) he0 x w
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  ·
    rw [map_mul, map_mul, glFin_centralScalar_archIdele, one_mul]
    exact (finiteIntegralGL2 (𝓞 F) F).mul_mem (glFin_globalPoints_upperUnit_mem ε β he0) hfin
  ·
    intro w
    rw [(hlaw w).1]
    exact (hbal w).1
  ·
    intro w
    rw [xWindowSq_eq_norm_xAt_sq, (hlaw w).2.1]
    have hb : ‖w.embedding ((ε : 𝓞 F) : F) * xAt w x + w.embedding (β : F)‖ ≤ U := by
      have : w.embedding (β : F) - ξ w
          = w.embedding ((ε : 𝓞 F) : F) * xAt w x + w.embedding (β : F) := by
        simp only [hξdef]; ring
      rw [← this]
      exact hβ w
    nlinarith [norm_nonneg (w.embedding ((ε : 𝓞 F) : F) * xAt w x + w.embedding (β : F)), hb]
  ·
    intro w
    rw [(hlaw w).2.2, ha w]
    exact ⟨le_rfl, le_rfl⟩
  ·
    intro w
    show localHeight _ ≤ Real.exp hi
    rw [(hlaw w).1]
    exact (hbal w).2

end LowCover

theorem LowCover.exists_isCompact_cover_of_archHeight_le_impl
    (F : Type) [Field F] [NumberField F] (c u T' : ℝ) (hc : 0 < c) :
    ∃ K : Set (AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers F) F),
      IsCompact K ∧
        ∀ x ∈ AutomorphicForm.WindowedSiegel.integralWindowedSiegelSet F c u,
          AutomorphicForm.WindowedSiegel.archHeight F
              (NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers F) F x) ≤ T' →
            ∃ γ : Matrix.GeneralLinearGroup (Fin 2) F,
              ∃ z : (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)ˣ,
                (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
                  AutomorphicForm.globalPoints (NumberField.RingOfIntegers F) F γ * x *
                      AutomorphicForm.centralScalar (NumberField.RingOfIntegers F) F z ∈ K :=
  LowCover.lowRegion_cover (F := F) c u T' hc

theorem exists_isCompact_cover_of_archHeight_le
    (F : Type) [Field F] [NumberField F] (c u T' : ℝ) (hc : 0 < c) :
    ∃ K : Set (AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers F) F),
      IsCompact K ∧
        ∀ x ∈ AutomorphicForm.WindowedSiegel.integralWindowedSiegelSet F c u,
          AutomorphicForm.WindowedSiegel.archHeight F
              (NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers F) F x) ≤ T' →
            ∃ γ : Matrix.GeneralLinearGroup (Fin 2) F,
              ∃ z : (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)ˣ,
                (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
                  AutomorphicForm.globalPoints (NumberField.RingOfIntegers F) F γ * x *
                      AutomorphicForm.centralScalar (NumberField.RingOfIntegers F) F z ∈ K :=
  LowCover.exists_isCompact_cover_of_archHeight_le_impl F c u T' hc

end WindowedSiegel

end AutomorphicForm

end
