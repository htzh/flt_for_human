/-
Counting in compact sets, the level-one lattice, and the finite-adelic trace.

Three facts about the adelic lattice: a compact set of adèles has a finite bound on how many
elements fall in a box scaled by a product of place norms; every finite adèle is left-multiplied
into `levelOne N` by a rational point whose archimedean components are positive; and the finite
trace of an adèle is the sum of the local traces over the places above a rational prime.

  spec-pin: P2M/Sol/S_NumberField_AdeleRing_exists_finset_forall_mem_and_card_le_mul_prod_pow_of_isCompact.lean
  spec-pin: P2M/Sol/S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_levelOne_rat.lean
  spec-pin: P2M/Sol/S_NumberField_AdelicTrace_traceFinHom_apply_eq_sum_trace.lean

## Port deltas

  import FLTForHuman.NumberTheory.AdelicLevel.ArchLevelLattice
    D2's engine `exists_glFin_globalPoints_mul_mem_finiteLevelOne_rat` (AF90's `finiteLevelOne`
    row) lives here; it is ported but was not in the scaffold's import closure
    (`tools/deps/premise_imports.py --nodes NumberField.AdelicLevel.exists_globalPoints_mul_mem_levelOne_rat`).

  Proof-side substitutions, statement-neutral (the three wire rows are untouched):

  * `Finset.prod_le_one` / `Finset.prod_le_prod` demand `[MulLeftMono ℝ]`, for which v4.34
    carries no `ℝ` instance; D1's two sites use `Finset.prod_le_one₀` / `Finset.prod_le_prod₀`
    (the same conclusion, taking the nonnegativity the pin supplied by hand).
  * `mul_lt_one_of_nonneg_of_lt_one_left` is `@[deprecated]` in v4.34 ("No replacement, use
    constituent lemmas from proof"); that site is spelled `(mul_le_of_le_one_right …).trans_lt`.
  * `letI`/`haveI` → `let`/`have` at the ten proof positions `linter.style.haveILetI` names
    (FR-0223); no replaced occurrence binds an instance that appears in a goal type, so
    FR-0235's exception does not apply.  The four statement-level `letI`s are the pin's own.
  * the pin's `attribute [-simp] unipotentGL2_zero constantTerm_const constantTerm_zero
    unipotentGL2_coe` (D2 pin `:8`) is dropped: it is proof-search tuning, and D2's proof
    replays without it.

## Heartbeat probe

Silent at `-DautoImplicit=false -DmaxHeartbeats=25000`; fails at half of it,
`-DmaxHeartbeats=12500`, with `error: (deterministic) timeout at 'whnf', maximum number of
heartbeats (12500) has been reached` at `private theorem localGlobal` (line 528).  The pair was measured
with `lake env lean` on this file; **no `set_option maxHeartbeats` is installed** (FR-0225).
-/
import FLTForHuman.NumberTheory.AdelicBox
import FLTForHuman.NumberTheory.AdelicLevel.ArchLevelLattice
import FLTForHuman.NumberTheory.AdelicLevel.Level
import FLTForHuman.NumberTheory.NumberField.AdelicTraceFin
import FLTForHuman.RingTheory.DedekindDomain.CompletionBaseChange
import FLTForHuman.AutomorphicForm.Adelic.Siegel.Reduction
import FLTForHuman.NumberTheory.NumberField.IntegralAdeles

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm Matrix NumberField.StandardAddChar
open scoped ENNReal BigOperators

namespace NumberField.AdeleRing

/-! ### D1 — counting a compact box

The pin's engine (`:15`–`:186`), transcribed at the pin's last names.  The pin's search-stage
namespace `AdelicBoxCount` folds into the subject namespace `NumberField.AdeleRing`. -/

section AdelicBoxCount

open AutomorphicForm.SiegelReduction NumberField.InfinitePlace

variable (K : Type) [Field K] [NumberField K]

private def boxCell (w : InfinitePlace K) (x : K) : ℤ × ℤ :=
  (⌊2 * (w.embedding x).re⌋, ⌊2 * (w.embedding x).im⌋)

private theorem apply_sub_lt_one_of_cell_eq {w : InfinitePlace K} {x y : K}
    (h : boxCell K w x = boxCell K w y) : w (x - y) < 1 := by
  have h1 : ⌊2 * (w.embedding x).re⌋ = ⌊2 * (w.embedding y).re⌋ := congrArg Prod.fst h
  have h2 : ⌊2 * (w.embedding x).im⌋ = ⌊2 * (w.embedding y).im⌋ := congrArg Prod.snd h
  have hre := Int.abs_sub_lt_one_of_floor_eq_floor h1
  have him := Int.abs_sub_lt_one_of_floor_eq_floor h2
  rw [← mul_sub, abs_mul, abs_two] at hre him
  rw [← norm_embedding_eq, map_sub]
  calc ‖w.embedding x - w.embedding y‖
      ≤ |(w.embedding x - w.embedding y).re| + |(w.embedding x - w.embedding y).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = |(w.embedding x).re - (w.embedding y).re| + |(w.embedding x).im - (w.embedding y).im| := by
        rw [Complex.sub_re, Complex.sub_im]
    _ < 1 := by linarith

private theorem eq_of_forall_cell_eq {x y : K} (hx : x ∈ (algebraMap (𝓞 K) K).range)
    (hy : y ∈ (algebraMap (𝓞 K) K).range) (h : ∀ w : InfinitePlace K, boxCell K w x = boxCell K w y) :
    x = y := by
  by_contra hne
  have hnorm : (1 : ℝ) ≤ |(Algebra.norm ℚ (x - y) : ℝ)| :=
    one_le_abs_norm_of_mem_range K (sub_mem hx hy) (sub_ne_zero.2 hne)
  have hprod := prod_eq_abs_norm (x - y)
  rw [Rat.cast_abs] at hprod
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace K) := inferInstance
  have hlt : ∏ w : InfinitePlace K, w (x - y) ^ w.mult < 1 := by
    classical
    rw [← Finset.mul_prod_erase Finset.univ (fun w : InfinitePlace K => w (x - y) ^ w.mult)
      (Finset.mem_univ w₀)]
    have ha1 : w₀ (x - y) ^ w₀.mult < 1 :=
      pow_lt_one₀ (apply_nonneg w₀ _) (apply_sub_lt_one_of_cell_eq K (h w₀))
        (by unfold mult; split_ifs <;> norm_num)
    have hb1 : (∏ w ∈ Finset.univ.erase w₀, w (x - y) ^ w.mult) ≤ 1 :=
      Finset.prod_le_one₀ (fun w _ => pow_nonneg (apply_nonneg w _) _) fun w _ =>
        pow_le_one₀ (apply_nonneg w _) (apply_sub_lt_one_of_cell_eq K (h w)).le
    exact (mul_le_of_le_one_right (pow_nonneg (apply_nonneg w₀ _) _) hb1).trans_lt ha1
  rw [hprod] at hlt
  exact absurd (hnorm.trans_lt hlt) (lt_irrefl _)

omit [NumberField K] in

private theorem im_embedding_eq_zero {w : InfinitePlace K} (hw : w.IsReal) (x : K) :
    (w.embedding x).im = 0 := by
  have hφ : ComplexEmbedding.IsReal w.embedding := isReal_iff.1 hw
  rw [← hφ.coe_embedding_apply, Complex.ofReal_im]

open Classical in

private def cellBox (w : InfinitePlace K) (r : ℝ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(⌊2 * r⌋ + 1)) ⌊2 * r⌋ ×ˢ
    (if w.IsReal then {0} else Finset.Icc (-(⌊2 * r⌋ + 1)) ⌊2 * r⌋)

private theorem floor_mem_Icc {t r : ℝ} (ht : |t| ≤ r) :
    ⌊2 * t⌋ ∈ Finset.Icc (-(⌊2 * r⌋ + 1)) ⌊2 * r⌋ := by
  obtain ⟨h1, h2⟩ := abs_le.1 ht
  rw [Finset.mem_Icc]
  constructor
  · have h3 : ⌊2 * (-r)⌋ ≤ ⌊2 * t⌋ := Int.floor_le_floor (by linarith)
    have h4 : ⌊2 * (-r)⌋ = -⌈2 * r⌉ := by rw [mul_neg, Int.floor_neg]
    have h5 := Int.ceil_le_floor_add_one (2 * r)
    omega
  · exact Int.floor_le_floor (by linarith)

omit [NumberField K] in

private theorem cell_mem_cellBox (w : InfinitePlace K) {r : ℝ} {x : K} (hx : w x ≤ r) :
    boxCell K w x ∈ cellBox K w r := by
  have hnorm : ‖w.embedding x‖ ≤ r := by rw [norm_embedding_eq]; exact hx
  unfold boxCell cellBox
  rw [Finset.mem_product]
  refine ⟨floor_mem_Icc ((Complex.abs_re_le_norm _).trans hnorm), ?_⟩
  split_ifs with hw
  · rw [im_embedding_eq_zero K hw x, mul_zero, Int.floor_zero]
    exact Finset.mem_singleton_self 0
  · exact floor_mem_Icc ((Complex.abs_im_le_norm _).trans hnorm)

omit [NumberField K] in

private theorem card_cellBox_le (w : InfinitePlace K) (r : ℝ) :
    ((cellBox K w r).card : ℝ) ≤ (6 * max 1 r) ^ w.mult := by
  have hI : ((Finset.Icc (-(⌊2 * r⌋ + 1)) ⌊2 * r⌋).card : ℝ) ≤ 6 * max 1 r := by
    rw [Int.card_Icc]
    have h1 : ((2 * ⌊2 * r⌋ + 2 : ℤ) : ℝ) ≤ 6 * max 1 r := by
      have h2 : ((⌊2 * r⌋ : ℤ) : ℝ) ≤ 2 * r := Int.floor_le _
      have h3 : r ≤ max 1 r := le_max_right _ _
      have h4 : (1 : ℝ) ≤ max 1 r := le_max_left _ _
      push_cast
      linarith
    have h5 : (0 : ℝ) ≤ 6 * max 1 r := by positivity
    have h6 : (((⌊2 * r⌋ + 1 - -(⌊2 * r⌋ + 1)).toNat : ℤ) : ℝ)
        = max (((2 * ⌊2 * r⌋ + 2 : ℤ) : ℝ)) 0 := by
      rw [Int.toNat_eq_max, Int.cast_max, Int.cast_zero]
      congr 2
      ring
    have h7 : (((⌊2 * r⌋ + 1 - -(⌊2 * r⌋ + 1)).toNat : ℕ) : ℝ)
        = (((⌊2 * r⌋ + 1 - -(⌊2 * r⌋ + 1)).toNat : ℤ) : ℝ) := (Int.cast_natCast _).symm
    rw [h7, h6]
    exact max_le h1 h5
  have h0 : (0 : ℝ) ≤ ((Finset.Icc (-(⌊2 * r⌋ + 1)) ⌊2 * r⌋).card : ℝ) := Nat.cast_nonneg _
  unfold cellBox
  rw [Finset.card_product, Nat.cast_mul]
  split_ifs with hw
  · have hm : w.mult = 1 := mult_isReal ⟨w, hw⟩
    rw [hm, pow_one, Finset.card_singleton, Nat.cast_one, mul_one]
    exact hI
  · have hm : w.mult = 2 := mult_isComplex ⟨w, not_isReal_iff_isComplex.1 hw⟩
    rw [hm, pow_two]
    exact mul_le_mul hI hI h0 (by positivity)

private theorem max_one_mul_le {a b : ℝ} (ha : 0 ≤ a) : max 1 (a * b) ≤ max 1 a * max 1 b := by
  have h1 : (1 : ℝ) ≤ max 1 a := le_max_left _ _
  have h2 : (1 : ℝ) ≤ max 1 b := le_max_left _ _
  refine max_le (one_le_mul_of_one_le_of_one_le h1 h2) ?_
  rcases le_or_gt 0 b with hb | hb
  · exact mul_le_mul (le_max_right _ _) (le_max_right _ _) hb (zero_le_one.trans h1)
  · calc a * b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha hb.le
      _ ≤ 1 := zero_le_one
      _ ≤ max 1 a * max 1 b := one_le_mul_of_one_le_of_one_le h1 h2

omit [NumberField K] in

private theorem card_cellBox_mul_le (w : InfinitePlace K) {c : ℝ} (hc : 0 ≤ c) (R : ℝ) :
    ((cellBox K w (c * R)).card : ℝ) ≤ (6 * max 1 c) ^ w.mult * max 1 R ^ w.mult := by
  refine (card_cellBox_le K w (c * R)).trans ?_
  rw [← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ _
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (max_one_mul_le hc) (by norm_num)

private theorem apply_sub_le (a : AdeleRing (𝓞 K) K) {R : InfinitePlace K → ℝ} {k k' : K}
    (hk : ∀ w : InfinitePlace K, ‖(algebraMap K (AdeleRing (𝓞 K) K) k - a).1 w‖ ≤ R w)
    (hk' : ∀ w : InfinitePlace K, ‖(algebraMap K (AdeleRing (𝓞 K) K) k' - a).1 w‖ ≤ R w)
    (w : InfinitePlace K) : w (k - k') ≤ 2 * R w := by
  have e : algebraMap K w.Completion (k - k')
      = (algebraMap K (AdeleRing (𝓞 K) K) k - a).1 w
        - (algebraMap K (AdeleRing (𝓞 K) K) k' - a).1 w := by
    rw [map_sub]
    show algebraMap K w.Completion k - algebraMap K w.Completion k'
      = (algebraMap K w.Completion k - a.1 w) - (algebraMap K w.Completion k' - a.1 w)
    ring
  have hn : ‖algebraMap K w.Completion (k - k')‖ = w (k - k') := norm_coe_completion K w (k - k')
  rw [← hn, e, two_mul]
  exact (norm_sub_le _ _).trans (add_le_add (hk w) (hk' w))

private theorem mul_sub_mem_range (a : AdeleRing (𝓞 K) K) {B : Set (FiniteAdeleRing (𝓞 K) K)}
    {d : 𝓞 K}
    (hd : ∀ y ∈ (fun p : FiniteAdeleRing (𝓞 K) K × FiniteAdeleRing (𝓞 K) K => p.1 - p.2) '' (B ×ˢ B),
      ∀ v : HeightOneSpectrum (𝓞 K),
        (algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) d * y) v ∈ v.adicCompletionIntegers K)
    {k k' : K} (hk : (algebraMap K (AdeleRing (𝓞 K) K) k - a).2 ∈ B)
    (hk' : (algebraMap K (AdeleRing (𝓞 K) K) k' - a).2 ∈ B) :
    algebraMap (𝓞 K) K d * (k - k') ∈ (algebraMap (𝓞 K) K).range := by
  refine mem_range_of_coe_mem_integralFiniteAdeles K fun v => ?_
  have e : algebraMap K (FiniteAdeleRing (𝓞 K) K) (algebraMap (𝓞 K) K d * (k - k'))
      = algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) d
        * ((algebraMap K (AdeleRing (𝓞 K) K) k - a).2 - (algebraMap K (AdeleRing (𝓞 K) K) k' - a).2) := by
    rw [map_mul, ← IsScalarTower.algebraMap_apply, map_sub]
    congr 1
    show algebraMap K (FiniteAdeleRing (𝓞 K) K) k - algebraMap K (FiniteAdeleRing (𝓞 K) K) k'
      = (algebraMap K (FiniteAdeleRing (𝓞 K) K) k - a.2) - (algebraMap K (FiniteAdeleRing (𝓞 K) K) k' - a.2)
    ring
  rw [e]
  exact hd _ ⟨((algebraMap K (AdeleRing (𝓞 K) K) k - a).2, (algebraMap K (AdeleRing (𝓞 K) K) k' - a).2),
    Set.mk_mem_prod hk hk', rfl⟩ v

end AdelicBoxCount

theorem exists_finset_forall_mem_and_card_le_mul_prod_pow_of_isCompact
    (K : Type) [Field K] [NumberField K]
    {B : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)} (hB : IsCompact B) :
    ∃ M : ℝ, ∀ (a : NumberField.AdeleRing (𝓞 K) K) (R : NumberField.InfinitePlace K → ℝ),
      ∃ s : Finset K,
        (∀ k : K, (algebraMap K (NumberField.AdeleRing (𝓞 K) K) k - a).2 ∈ B →
          (∀ w : NumberField.InfinitePlace K,
            ‖(algebraMap K (NumberField.AdeleRing (𝓞 K) K) k - a).1 w‖ ≤ R w) → k ∈ s) ∧
        (s.card : ℝ) ≤ M * ∏ w : NumberField.InfinitePlace K, max 1 (R w) ^ w.mult
  := by
  classical

  have hBB : IsCompact ((fun p : FiniteAdeleRing (𝓞 K) K × FiniteAdeleRing (𝓞 K) K => p.1 - p.2)
      '' (B ×ˢ B)) :=
    (hB.prod hB).image (continuous_fst.sub continuous_snd)
  obtain ⟨d, hd0, hd⟩ :=
    IsDedekindDomain.FiniteAdeleRing.exists_ne_zero_forall_mul_apply_mem_adicCompletionIntegers_of_isCompact
      (𝓞 K) K hBB
  have hc0 : algebraMap (𝓞 K) K d ≠ 0 := fun h => hd0 (IsFractionRing.injective (𝓞 K) K (by rw [h, map_zero]))
  have hcnn : ∀ w : InfinitePlace K, (0 : ℝ) ≤ 2 * w (algebraMap (𝓞 K) K d) :=
    fun w => by positivity
  refine ⟨∏ w : InfinitePlace K, (6 * max 1 (2 * w (algebraMap (𝓞 K) K d))) ^ w.mult, fun a R => ?_⟩
  have hMnn : (0 : ℝ) ≤ ∏ w : InfinitePlace K, (6 * max 1 (2 * w (algebraMap (𝓞 K) K d))) ^ w.mult :=
    Finset.prod_nonneg fun w _ => by positivity
  have hPnn : (0 : ℝ) ≤ ∏ w : InfinitePlace K, max 1 (R w) ^ w.mult :=
    Finset.prod_nonneg fun w _ => by positivity

  set S : Set K := {k | (algebraMap K (AdeleRing (𝓞 K) K) k - a).2 ∈ B ∧
    ∀ w : InfinitePlace K, ‖(algebraMap K (AdeleRing (𝓞 K) K) k - a).1 w‖ ≤ R w} with hSdef
  by_cases hS : S.Nonempty
  swap
  · refine ⟨∅, fun k h1 h2 => (hS ⟨k, h1, h2⟩).elim, ?_⟩
    rw [Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg hMnn hPnn
  obtain ⟨k₀, hk₀⟩ := hS

  set f : K → (InfinitePlace K → ℤ × ℤ) :=
    fun k w => boxCell K w (algebraMap (𝓞 K) K d * (k - k₀)) with hfdef
  set T : Finset (InfinitePlace K → ℤ × ℤ) :=
    Fintype.piFinset fun w : InfinitePlace K => cellBox K w (2 * w (algebraMap (𝓞 K) K d) * R w)
    with hTdef
  have hmaps : ∀ k ∈ S, f k ∈ T := by
    intro k hk
    rw [hTdef, Fintype.mem_piFinset]
    intro w
    refine cell_mem_cellBox K w ?_
    rw [map_mul]
    calc w (algebraMap (𝓞 K) K d) * w (k - k₀)
        ≤ w (algebraMap (𝓞 K) K d) * (2 * R w) :=
          mul_le_mul_of_nonneg_left (apply_sub_le K a hk.2 hk₀.2 w) (apply_nonneg w _)
      _ = 2 * w (algebraMap (𝓞 K) K d) * R w := by ring
  have hinj : S.InjOn f := by
    intro k hk k' hk' hkk'
    have h1 := mul_sub_mem_range K a hd hk.1 hk₀.1
    have h2 := mul_sub_mem_range K a hd hk'.1 hk₀.1
    have h3 := eq_of_forall_cell_eq K h1 h2 fun w => congrFun hkk' w
    have h4 := mul_left_cancel₀ hc0 h3
    exact sub_left_inj.1 h4
  have hfin : S.Finite :=
    Set.Finite.of_finite_image (T.finite_toSet.subset (by
      rintro _ ⟨k, hk, rfl⟩
      exact hmaps k hk)) hinj
  refine ⟨hfin.toFinset, fun k h1 h2 => hfin.mem_toFinset.2 ⟨h1, h2⟩, ?_⟩
  have hcard : hfin.toFinset.card ≤ T.card := by
    refine Finset.card_le_card_of_injOn f (fun k hk => hmaps k (hfin.mem_toFinset.1 hk)) ?_
    intro k hk k' hk' h
    exact hinj (hfin.mem_toFinset.1 hk) (hfin.mem_toFinset.1 hk') h
  calc (hfin.toFinset.card : ℝ) ≤ T.card := Nat.cast_le.2 hcard
    _ = ∏ w : InfinitePlace K, ((cellBox K w (2 * w (algebraMap (𝓞 K) K d) * R w)).card : ℝ) := by
        rw [hTdef, Fintype.card_piFinset, Nat.cast_prod]
    _ ≤ ∏ w : InfinitePlace K,
          (6 * max 1 (2 * w (algebraMap (𝓞 K) K d))) ^ w.mult * max 1 (R w) ^ w.mult :=
        Finset.prod_le_prod₀ (fun w _ => Nat.cast_nonneg _)
          fun w _ => card_cellBox_mul_le K w (hcnn w) (R w)
    _ = (∏ w : InfinitePlace K, (6 * max 1 (2 * w (algebraMap (𝓞 K) K d))) ^ w.mult)
          * ∏ w : InfinitePlace K, max 1 (R w) ^ w.mult := Finset.prod_mul_distrib


end NumberField.AdeleRing

namespace NumberField.AdelicLevel

open NumberField.InfinitePlace

/- ### The archimedean sign correction

The pin's own engine (`:19`–`:140`), transcribed at the pin's last names.  `realProj` reads an
adèlic matrix through the real place, and `eps` is the diagonal `diag(-1, 1)` that flips the sign
of the determinant without leaving `levelOne`. -/

def realProj (w : InfinitePlace ℚ) (hw : w.IsReal) :
    GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) →* GL (Fin 2) ℝ :=
  (Matrix.GeneralLinearGroup.map (Completion.ringEquivRealOfIsReal hw).toRingHom).comp
    ((archComponent ℚ w).comp (glArch (𝓞 ℚ) ℚ))

theorem realProj_apply (w : InfinitePlace ℚ) (hw : w.IsReal) (h : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    realProj w hw h = Matrix.GeneralLinearGroup.map (Completion.ringEquivRealOfIsReal hw).toRingHom
      (archComponent ℚ w (glArch (𝓞 ℚ) ℚ h)) := rfl

def ratToReal (w : InfinitePlace ℚ) (hw : w.IsReal) : ℚ →+* ℝ :=
  (Completion.ringEquivRealOfIsReal hw).toRingHom.comp
    ((archEval ℚ w).comp ((adeleArch (𝓞 ℚ) ℚ).comp (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ))))

theorem realProj_globalPoints_apply (w : InfinitePlace ℚ) (hw : w.IsReal) (γ : GL (Fin 2) ℚ)
    (i j : Fin 2) :
    ((realProj w hw (globalPoints (𝓞 ℚ) ℚ γ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j
      = ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j : ℝ) := by
  show ratToReal w hw ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j) = _
  exact eq_ratCast (ratToReal w hw) _

theorem det_realProj_globalPoints (w : InfinitePlace ℚ) (hw : w.IsReal) (γ : GL (Fin 2) ℚ) :
    (((realProj w hw (globalPoints (𝓞 ℚ) ℚ γ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)).det
      = ((γ : Matrix (Fin 2) (Fin 2) ℚ).det : ℝ) := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two, realProj_globalPoints_apply,
    realProj_globalPoints_apply, realProj_globalPoints_apply, realProj_globalPoints_apply]
  push_cast
  ring

def eps : GL (Fin 2) ℚ where
  val := !![-1, 0; 0, 1]
  inv := !![-1, 0; 0, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp

theorem eps_val : ((eps : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = !![-1, 0; 0, 1] := rfl

theorem eps_inv : eps⁻¹ = eps := by
  apply Units.ext; rfl

theorem det_eps : ((eps : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det = -1 := by
  rw [eps_val, Matrix.det_fin_two]; simp

theorem isLevelOneMatrix_eps (N : Ideal (𝓞 ℚ)) :
    IsLevelOneMatrix (𝓞 ℚ) ℚ N
      ((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ eps) : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
  have hentry : ∀ i j, ((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ eps) :
      GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j
        = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℚ) i j) :=
    fun _ _ => rfl
  have h00 : ((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ eps) : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 0 0 = -1 := by
    rw [hentry]; show algebraMap ℚ _ (-1) = -1; rw [map_neg, map_one]
  have h01 : ((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ eps) : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 0 1 = 0 := by
    rw [hentry]; show algebraMap ℚ _ 0 = 0; rw [map_zero]
  have h10 : ((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ eps) : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 0 = 0 := by
    rw [hentry]; show algebraMap ℚ _ 0 = 0; rw [map_zero]
  have h11 : ((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ eps) : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 = 1 := by
    rw [hentry]; show algebraMap ℚ _ 1 = 1; rw [map_one]
  have hneg1 : (-1 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
    rw [show (-1 : FiniteAdeleRing (𝓞 ℚ) ℚ) = 0 - 1 from (zero_sub 1).symm]
    exact sub_mem_integralFiniteAdeles zero_mem_integralFiniteAdeles one_mem_integralFiniteAdeles
  refine { integral := ?_, lowerLeft := ?_, lowerRight := ?_ }
  · refine Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩, Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩
    · rw [h00]; exact hneg1
    · rw [h01]; exact zero_mem_integralFiniteAdeles
    · rw [h10]; exact zero_mem_integralFiniteAdeles
    · rw [h11]; exact one_mem_integralFiniteAdeles
  · rw [h10]; exact zero_mem_idealBall N
  · rw [h11, sub_self]; exact zero_mem_idealBall N

theorem globalPoints_eps_mem_levelOne (N : Ideal (𝓞 ℚ)) :
    globalPoints (𝓞 ℚ) ℚ eps ∈ levelOne (𝓞 ℚ) ℚ N := by
  rw [mem_levelOne_iff, mem_finiteLevelOne_iff]
  refine ⟨isLevelOneMatrix_eps N, ?_⟩
  rw [← map_inv, ← map_inv, eps_inv]
  exact isLevelOneMatrix_eps N

theorem exists_globalPoints_mul_mem_levelOne_rat_impl
    {N : Ideal (𝓞 ℚ)} (hN : N ≠ ⊥) (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    ∃ γ : GL (Fin 2) ℚ,
      globalPoints (𝓞 ℚ) ℚ γ * g ∈ levelOne (𝓞 ℚ) ℚ N ∧
        ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
          Matrix.GeneralLinearGroup.map (Completion.ringEquivRealOfIsReal hw).toRingHom
              (archComponent ℚ w (glArch (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ * g)))
            ∈ Matrix.GLPos (Fin 2) ℝ := by

  obtain ⟨γ₁, hγ₁⟩ := NumberField.AdelicLevel.exists_glFin_globalPoints_mul_mem_finiteLevelOne_rat
    hN (glFin (𝓞 ℚ) ℚ g)
  have hg₁ : globalPoints (𝓞 ℚ) ℚ γ₁ * g ∈ levelOne (𝓞 ℚ) ℚ N := by
    rw [mem_levelOne_iff, map_mul]; exact hγ₁

  set w₀ : InfinitePlace ℚ := Rat.infinitePlace with hw₀_def
  have hw₀ : w₀.IsReal := Rat.isReal_infinitePlace
  have key : ∀ (γ : GL (Fin 2) ℚ),
      0 < (((realProj w₀ hw₀ (globalPoints (𝓞 ℚ) ℚ γ * g) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ)).det →
      ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
        Matrix.GeneralLinearGroup.map (Completion.ringEquivRealOfIsReal hw).toRingHom
            (archComponent ℚ w (glArch (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ * g)))
          ∈ Matrix.GLPos (Fin 2) ℝ := by
    intro γ hγ w hw
    obtain rfl : w = w₀ := Subsingleton.elim _ _
    rw [Matrix.mem_glpos, Matrix.GeneralLinearGroup.val_det_apply]
    exact hγ
  by_cases hsign : 0 < (((realProj w₀ hw₀ (globalPoints (𝓞 ℚ) ℚ γ₁ * g) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ)).det
  · exact ⟨γ₁, hg₁, key γ₁ hsign⟩
  · refine ⟨eps * γ₁, ?_, key (eps * γ₁) ?_⟩
    · rw [map_mul, mul_assoc]
      exact mul_mem (globalPoints_eps_mem_levelOne N) hg₁
    · have hne : (((realProj w₀ hw₀ (globalPoints (𝓞 ℚ) ℚ γ₁ * g) : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ)).det ≠ 0 := by
        rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _
      have hlt : (((realProj w₀ hw₀ (globalPoints (𝓞 ℚ) ℚ γ₁ * g) : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ)).det < 0 := lt_of_le_of_ne (not_lt.mp hsign) hne
      rw [map_mul (globalPoints (𝓞 ℚ) ℚ) eps γ₁, mul_assoc, map_mul (realProj w₀ hw₀), Units.val_mul,
        Matrix.det_mul, det_realProj_globalPoints, det_eps]
      push_cast
      linarith

theorem exists_globalPoints_mul_mem_levelOne_rat
    {N : Ideal (NumberField.RingOfIntegers ℚ)} (hN : N ≠ ⊥)
    (g : Matrix.GeneralLinearGroup (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) :
    ∃ γ : Matrix.GeneralLinearGroup (Fin 2) ℚ,
      AutomorphicForm.globalPoints (NumberField.RingOfIntegers ℚ) ℚ γ * g
          ∈ NumberField.AdelicLevel.levelOne (NumberField.RingOfIntegers ℚ) ℚ N ∧
        ∀ (w : NumberField.InfinitePlace ℚ) (hw : w.IsReal),
          Matrix.GeneralLinearGroup.map
              (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw).toRingHom
              (NumberField.AdelicLevel.archComponent ℚ w
                (NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers ℚ) ℚ
                  (AutomorphicForm.globalPoints (NumberField.RingOfIntegers ℚ) ℚ γ * g)))
            ∈ Matrix.GLPos (Fin 2) ℝ
  := by
  exact exists_globalPoints_mul_mem_levelOne_rat_impl hN g

end NumberField.AdelicLevel

namespace NumberField.AdelicTrace

/- ### D3 — the local-trace decomposition

The pin's engine (`:20`–`:248`), transcribed at the pin's last names.  The pin's search-stage
namespace `ComponentFormula` folds into the subject namespace `NumberField.AdelicTrace`; its
`p2m_open`/`p2m_export` bookkeeping lines have no port counterpart (the names are already in
`NumberField.AdelicTrace`). -/

section ComponentFormula

open scoped TensorProduct

private theorem trace_pi_apply {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    {S : ι → Type*} [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
    [∀ i, Module.Free R (S i)] [∀ i, Module.Finite R (S i)] (y : Π i, S i) :
    Algebra.trace R (Π i, S i) y = ∑ i, Algebra.trace R (S i) (y i) := by
  classical
  let b : Π i, Module.Basis (Module.Free.ChooseBasisIndex R (S i)) R (S i) :=
    fun i => Module.Free.chooseBasis R (S i)
  rw [Algebra.trace_eq_matrix_trace (Pi.basis b) y, Matrix.trace]
  simp_rw [Algebra.trace_eq_matrix_trace (b _), Matrix.trace, Matrix.diag_apply,
    Algebra.leftMulMatrix_eq_repr_mul, Pi.basis_repr, Pi.basis_apply]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => ?_
  rw [Pi.mul_apply, Pi.single_eq_same]

section fieldLevel

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v

private def piEquiv [Module.Finite (𝓞 K) (𝓞 L)] :
    Kv ⊗[K] L ≃ₐ[Kv] Π w : v.Extension (𝓞 L), w.1.adicCompletion L :=
  AlgEquiv.ofRingEquiv
    (f := (Algebra.TensorProduct.comm K Kv L).toRingEquiv.trans
      (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).toRingEquiv)
    (fun s => by
      funext w
      change HeightOneSpectrum.adicCompletion.baseChange K L (𝓞 L) v
          (Algebra.TensorProduct.comm K Kv L ((algebraMap Kv Kv s) ⊗ₜ[K] (1 : L))) w = _
      rw [Algebra.TensorProduct.comm_tmul, HeightOneSpectrum.adicCompletion.baseChange_tmul_apply, map_one,
        one_mul, Pi.algebraMap_apply]
      rfl)

private theorem piEquiv_one_tmul [Module.Finite (𝓞 K) (𝓞 L)] (a : L) (w : v.Extension (𝓞 L)) :
    piEquiv K L v ((1 : Kv) ⊗ₜ[K] a) w = algebraMap L (w.1.adicCompletion L) a := by
  change HeightOneSpectrum.adicCompletion.baseChange K L (𝓞 L) v
      (Algebra.TensorProduct.comm K Kv L ((1 : Kv) ⊗ₜ[K] a)) w = _
  rw [Algebra.TensorProduct.comm_tmul, HeightOneSpectrum.adicCompletion.baseChange_tmul_apply, map_one, mul_one]

private theorem trace_one_tmul (a : L) :
    Algebra.trace Kv (Kv ⊗[K] L) ((1 : Kv) ⊗ₜ[K] a) = algebraMap K Kv (Algebra.trace K L a) := by
  rw [Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange, ← Algebra.trace_apply]

private theorem localGlobal (a : L) :
    letI := HeightOneSpectrum.Extension.fintype (𝓞 K) K L (𝓞 L) v
    algebraMap K Kv (Algebra.trace K L a)
      = ∑ w : v.Extension (𝓞 L), Algebra.trace Kv (w.1.adicCompletion L) (algebraMap L (w.1.adicCompletion L) a) := by
  let fintype := HeightOneSpectrum.Extension.fintype (𝓞 K) K L (𝓞 L) v
  have : Module.Finite (𝓞 K) (𝓞 L) :=
    have := IsIntegralClosure.isNoetherian (𝓞 K) K L (𝓞 L)
    Module.IsNoetherian.finite (𝓞 K) (𝓞 L)
  have : ∀ w : v.Extension (𝓞 L), Module.Free Kv (w.1.adicCompletion L) :=
    fun w => Module.Free.of_divisionRing _ _
  have h1 := Algebra.trace_eq_of_algEquiv (piEquiv K L v) ((1 : Kv) ⊗ₜ[K] a)
  rw [trace_one_tmul, trace_pi_apply] at h1
  rw [← h1]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [piEquiv_one_tmul]

end fieldLevel

section integerLevel

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v
local notation "Ov" => HeightOneSpectrum.adicCompletionIntegers K v
local notation "Lw" => HeightOneSpectrum.adicCompletion L (Subtype.val w)
local notation "Ow" => HeightOneSpectrum.adicCompletionIntegers L (Subtype.val w)

private theorem algebraMap_integers_injective : Function.Injective (algebraMap Ov Ow) := by
  intro x y h
  apply Subtype.val_injective
  have h' := congrArg (fun z : Ow => (z : Lw)) h
  change (w.adicCompletionSemialgHom K L) x.val = (w.adicCompletionSemialgHom K L) y.val at h'
  exact (w.adicCompletionSemialgHom K L).toRingHom.injective h'

private scoped instance faithfulSMul_integers : FaithfulSMul Ov Ow :=
  (faithfulSMul_iff_algebraMap_injective Ov Ow).mpr (algebraMap_integers_injective K L v w)

private scoped instance isScalarTower_integers : IsScalarTower Ov Ow Lw :=
  .of_algebraMap_smul fun _ _ => rfl

private scoped instance free_integers [Module.Finite (𝓞 K) (𝓞 L)] : Module.Free Ov Ow :=
  Module.free_of_finite_type_torsion_free'

private scoped instance isIntegralClosure_integers [Module.Finite (𝓞 K) (𝓞 L)] : IsIntegralClosure Ow Ov Lw where
  algebraMap_injective := IsFractionRing.injective Ow Lw
  isIntegral_iff := by
    intro x
    constructor
    · intro hx
      exact IsIntegrallyClosed.isIntegral_iff.mp hx.tower_top
    · rintro ⟨y, rfl⟩
      exact (Algebra.IsIntegral.isIntegral (R := Ov) y).algebraMap

private theorem trace_coe_integer [Module.Finite (𝓞 K) (𝓞 L)] (y : Ow) :
    Algebra.trace Kv Lw (y : Lw) = algebraMap Ov Kv (Algebra.trace Ov Ow y) := by
  have : IsLocalization (Algebra.algebraMapSubmonoid Ow (nonZeroDivisors Ov)) Lw :=
    IsIntegralClosure.isLocalization Ov Kv Lw Ow
  exact Algebra.trace_localization Ov (nonZeroDivisors Ov) (Rₘ := Kv) (Sₘ := Lw) y

end integerLevel

section placewise

variable (K : Type) [Field K] [NumberField K]

private def placewiseTrace :
    (Π w : HeightOneSpectrum (𝓞 K), w.adicCompletionIntegers K)
      →+ (Π p : HeightOneSpectrum (𝓞 ℚ), p.adicCompletionIntegers ℚ) where
  toFun y p :=
    letI := HeightOneSpectrum.Extension.fintype (𝓞 ℚ) ℚ K (𝓞 K) p
    ∑ w : p.Extension (𝓞 K),
      Algebra.trace (p.adicCompletionIntegers ℚ) (w.1.adicCompletionIntegers K) (y w.1)
  map_zero' := by
    funext p
    simp only [Pi.zero_apply, map_zero, Finset.sum_const_zero]
  map_add' y z := by
    funext p
    simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]

private theorem placewiseTrace_apply_coe (y : Π w : HeightOneSpectrum (𝓞 K), w.adicCompletionIntegers K)
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    letI := HeightOneSpectrum.Extension.fintype (𝓞 ℚ) ℚ K (𝓞 K) p
    ((placewiseTrace K y p : p.adicCompletionIntegers ℚ) : p.adicCompletion ℚ)
      = ∑ w : p.Extension (𝓞 K),
          Algebra.trace (p.adicCompletion ℚ) (w.1.adicCompletion K) ((y w.1 : w.1.adicCompletion K)) := by
  let fintype := HeightOneSpectrum.Extension.fintype (𝓞 ℚ) ℚ K (𝓞 K) p
  have : Module.Finite (𝓞 ℚ) (𝓞 K) :=
    have := IsIntegralClosure.isNoetherian (𝓞 ℚ) ℚ K (𝓞 K)
    Module.IsNoetherian.finite (𝓞 ℚ) (𝓞 K)
  change ((algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ))
      (∑ w : p.Extension (𝓞 K),
        Algebra.trace (p.adicCompletionIntegers ℚ) (w.1.adicCompletionIntegers K) (y w.1))) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← trace_coe_integer ℚ K p w (y w.1)]

private theorem continuous_placewiseTrace : Continuous (placewiseTrace K) := by
  have : Module.Finite (𝓞 ℚ) (𝓞 K) :=
    have := IsIntegralClosure.isNoetherian (𝓞 ℚ) ℚ K (𝓞 K)
    Module.IsNoetherian.finite (𝓞 ℚ) (𝓞 K)
  apply continuous_pi
  intro p
  let fintype := HeightOneSpectrum.Extension.fintype (𝓞 ℚ) ℚ K (𝓞 K) p
  rw [continuous_induced_rng]
  have hfun : (Subtype.val ∘ fun y : (Π w : HeightOneSpectrum (𝓞 K), w.adicCompletionIntegers K) =>
        placewiseTrace K y p)
      = fun y => ∑ w : p.Extension (𝓞 K),
          Algebra.trace (p.adicCompletion ℚ) (w.1.adicCompletion K) ((y w.1 : w.1.adicCompletion K)) :=
    funext fun y => placewiseTrace_apply_coe K y p
  rw [hfun]
  refine continuous_finsetSum _ fun w _ => ?_
  have hc : Continuous fun y : (Π u : HeightOneSpectrum (𝓞 K), u.adicCompletionIntegers K) =>
      ((y w.1 : w.1.adicCompletion K)) :=
    continuous_subtype_val.comp (continuous_apply w.1)
  exact (IsModuleTopology.continuous_of_linearMap
    (Algebra.trace (p.adicCompletion ℚ) (w.1.adicCompletion K))).comp hc

private theorem placewiseTrace_diag (a : 𝓞 K) :
    placewiseTrace K (diag K a) = traceInt K (diag K a) := by
  funext p
  let fintype := HeightOneSpectrum.Extension.fintype (𝓞 ℚ) ℚ K (𝓞 K) p
  apply Subtype.val_injective
  rw [placewiseTrace_apply_coe, traceInt_diag]

  have hl : ∀ w : p.Extension (𝓞 K),
      ((diag K a w.1 : w.1.adicCompletionIntegers K) : w.1.adicCompletion K)
        = algebraMap K (w.1.adicCompletion K) (a : K) := fun w => by
    rw [diag_apply]
    rfl
  simp_rw [hl]
  rw [← localGlobal ℚ K p (a : K)]

  have hr : (((algebraMap ℤ (𝓞 ℚ) (Algebra.trace ℤ (𝓞 K) a) : 𝓞 ℚ) : ℚ)) = Algebra.trace ℚ K (a : K) := by
    rw [← Algebra.coe_trace_int, eq_intCast, RingOfIntegers.coe_eq_algebraMap, map_intCast]
  change _ = algebraMap ℚ (p.adicCompletion ℚ) (((algebraMap ℤ (𝓞 ℚ) (Algebra.trace ℤ (𝓞 K) a) : 𝓞 ℚ) : ℚ))
  rw [hr]

private theorem placewiseTrace_eq_traceInt : placewiseTrace K = traceInt K :=
  eq_traceInt K (continuous_placewiseTrace K) (placewiseTrace_diag K)

end placewise

section assembly

variable (K : Type) [Field K] [NumberField K]

private def sm (z : Π w : HeightOneSpectrum (𝓞 K), w.adicCompletionIntegers K) : FiniteAdeleRing (𝓞 K) K :=
  RestrictedProduct.structureMap (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K)
    (fun w => (w.adicCompletionIntegers K : Set (w.adicCompletion K))) Filter.cofinite z

private theorem sm_apply (z : Π w : HeightOneSpectrum (𝓞 K), w.adicCompletionIntegers K)
    (w : HeightOneSpectrum (𝓞 K)) : sm K z w = (z w : w.adicCompletion K) := rfl

private theorem traceFinHom_sm (z : Π w : HeightOneSpectrum (𝓞 K), w.adicCompletionIntegers K) :
    traceFinHom K (sm K z) = sm ℚ (traceInt K z) :=
  traceFinHom_structureMap K z

private theorem sub_apply' (a b : FiniteAdeleRing (𝓞 K) K) (w : HeightOneSpectrum (𝓞 K)) :
    (a - b) w = a w - b w := rfl

private theorem algebraMap_apply' (q : ℚ) (p : HeightOneSpectrum (𝓞 ℚ)) :
    (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q) p = algebraMap ℚ (p.adicCompletion ℚ) q := rfl

private theorem algebraMap_apply'' (k : K) (w : HeightOneSpectrum (𝓞 K)) :
    (algebraMap K (FiniteAdeleRing (𝓞 K) K) k) w = algebraMap K (w.adicCompletion K) k := rfl

private theorem main (x : FiniteAdeleRing (𝓞 K) K) (p : HeightOneSpectrum (𝓞 ℚ)) :
    letI := HeightOneSpectrum.Extension.fintype (𝓞 ℚ) ℚ K (𝓞 K) p
    (traceFinHom K x) p
      = ∑ w : p.Extension (𝓞 K), Algebra.trace (p.adicCompletion ℚ) (w.1.adicCompletion K) (x w.1) := by
  let fintype := HeightOneSpectrum.Extension.fintype (𝓞 ℚ) ℚ K (𝓞 K) p
  obtain ⟨k, hk⟩ := NumberField.AdelicBox.exists_algebraMap_add_mem_integralFiniteAdeles (𝓞 K) K x
  let y : Π w : HeightOneSpectrum (𝓞 K), w.adicCompletionIntegers K :=
    fun w => ⟨(algebraMap K (FiniteAdeleRing (𝓞 K) K) k + x) w, hk w⟩
  have hy : sm K y = algebraMap K (FiniteAdeleRing (𝓞 K) K) k + x :=
    RestrictedProduct.ext _ _ fun w => rfl
  have hx : x = sm K y - algebraMap K (FiniteAdeleRing (𝓞 K) K) k := by
    rw [hy, add_sub_cancel_left]
  rw [hx, map_sub, traceFinHom_sm, traceFinHom_algebraMap, sub_apply' ℚ, sm_apply, algebraMap_apply',
    ← placewiseTrace_eq_traceInt, placewiseTrace_apply_coe, localGlobal ℚ K p k, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← map_sub, sub_apply' K, sm_apply, algebraMap_apply'']

end assembly

end ComponentFormula

theorem traceFinHom_apply_eq_sum_trace
    (K : Type) [Field K] [NumberField K]
    (x : FiniteAdeleRing (𝓞 K) K)
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    letI := HeightOneSpectrum.Extension.fintype (𝓞 ℚ) ℚ K (𝓞 K) p
    (traceFinHom K x) p
      = ∑ w : p.Extension (𝓞 K),
          Algebra.trace (p.adicCompletion ℚ) (w.1.adicCompletion K) (x w.1)
  := main K x p

end NumberField.AdelicTrace

end
