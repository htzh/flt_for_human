/-
  The bottom-row indicator against the adelic height is an induced section.

  For the modulus character `α = distribHaarChar` read through `ℝ≥0 → ℝ`, a finite set `S` of places with
  exponents `n v > 0`, and `s : ℂ`, the function

  `g ↦ (if ∀ v ∈ S, |g₁₀(v)|_v ≤ |g₁₁(v)|_v · ϖ_v ^ (-n v) then (adelicHeight K g) ^ (s + 1/2) else 0)`

  — the indicator of a *bottom-row* (Borel-entry) congruence condition at `S`, times the height power — is
  an `IsInducedSection` for the character pair `(etaFst 1 α hα s, etaSnd 1 α hα s)`, it is continuous,
  archimedean-`K`-finite and `K_f`-smooth, and it satisfies the four invariance laws that the
  Weyl-integrand family of SET-AF33 needs: right invariance under the `S`-congruence subgroup of
  `finiteAdelicGL2Subgroup`, right invariance under the integral points at the places outside `S`, right
  invariance under the archimedean part when the finite part is trivial, and the `0/1`-valuedness on the
  integral archimedean-row-isometry subgroup. It is normalized by `φ₀ 1 = 1`.

  This is the explicit test section `phi0` on which the Weyl intertwining integral of the column is computed,
  the value side of that computation being the Weyl-translate evaluations of the same wave.

  Transcribed whole from the pin's proof file
  `P2M/Sol/S_AutomorphicForm_isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow.lean`
  (pinned `aa2d8b3`, 1,043 lines / 82 declarations) and its statement from the wrapper
  `Theorems/Thm_AutomorphicForm_isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow.lean`.
  Its first ~440 lines are the height/`flatOne` prelude already ported in
  `AutomorphicForm/Adelic/InducedSectionFlat.lean` (`flatOne`, `isInducedSection_flatOne`,
  `adelicHeight_mul_of_integral_of_rowIsometry`, …): 433 of the pin's 439 declaration lines are imported,
  not rewritten.

  spec-pin: Theorems/Thm_AutomorphicForm_isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.InducedSectionFlat
import FLTForHuman.AutomorphicForm.Adelic.EtaFamily
import FLTForHuman.AutomorphicForm.Adelic.SmoothAutomorphicFn
import FLTForHuman.AutomorphicForm.Adelic.ArchKFiniteFamilyTheorems
import FLTForHuman.AutomorphicForm.Adelic.WindowedSiegel.RowIsometry
import FLTForHuman.NumberTheory.AdelicHeight
import FLTForHuman.NumberTheory.AdelicLevel.IdealBall
import FLTForHuman.RepTheory.LocalLanglands.UnramifiedWhittaker
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHeight IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped NNReal Classical

noncomputable section

namespace AutomorphicForm

/-
  Pin block 1 of the transcription — `RS11SC`, pin lines 449–755, in the pin's order:
  `πv` 457, `πv_apply` 460, `continuous_πv` 462, `ent` 465, `ent_eq` 468, `continuous_ent` 471,
  `ent_mul` 475, `ent_one` 479, `ent_one_ne_zero` 486, `eps` 497, `eps_ne_zero` 500, `eps_le_one` 503,
  `eps_lt_one` 507, `exists_valued_eq_eps` 512, `CondAt` 516, `condAt_borel_mul_imp` 519,
  `condAt_borel_mul_iff` 529, `condAt_mul_of_cong` 536, `cong_inv` 590, `condAt_mul_iff_of_cong` 618,
  `condAt_mul_of_ent_eq_one` 627, `isOpen_setOf_condAt` 635, `isOpen_setOf_not_condAt` 690,
  `isClopen_setOf_cond` 744.
-/

namespace BorelIndicator

open MeasureTheory NumberField NumberField.AdelicHeight NumberField.AdelicLevel AutomorphicForm
  AutomorphicForm.WindowedSiegel IsDedekindDomain Matrix

open scoped NNReal Classical

variable {K : Type} [Field K] [NumberField K]

def πv (v : HeightOneSpectrum (𝓞 K)) : AdeleRing (𝓞 K) K →+* v.adicCompletion K :=
  (finAdeleEval (𝓞 K) K v).comp (adeleFin (𝓞 K) K)

theorem πv_apply (v : HeightOneSpectrum (𝓞 K)) (x : AdeleRing (𝓞 K) K) : πv v x = x.2 v := rfl

theorem continuous_πv (v : HeightOneSpectrum (𝓞 K)) : Continuous (πv (K := K) v) :=
  (continuous_finAdeleEval (𝓞 K) K v).comp (continuous_adeleFin (𝓞 K) K)

def ent (g : AdelicGL2 (𝓞 K) K) (i j : Fin 2) (v : HeightOneSpectrum (𝓞 K)) :
    v.adicCompletion K :=
  πv v ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)

theorem ent_eq (g : AdelicGL2 (𝓞 K) K) (i j : Fin 2) (v : HeightOneSpectrum (𝓞 K)) :
    ent g i j v = ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v := rfl

theorem continuous_ent (i j : Fin 2) (v : HeightOneSpectrum (𝓞 K)) :
    Continuous fun g : AdelicGL2 (𝓞 K) K => ent g i j v :=
  (continuous_πv v).comp (Units.continuous_val.matrix_elem i j)

theorem ent_mul (g h : AdelicGL2 (𝓞 K) K) (i j : Fin 2) (v : HeightOneSpectrum (𝓞 K)) :
    ent (g * h) i j v = ent g i 0 v * ent h 0 j v + ent g i 1 v * ent h 1 j v := by
  simp only [ent, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, map_add,
    map_mul]

theorem ent_one (i j : Fin 2) (v : HeightOneSpectrum (𝓞 K)) :
    ent (1 : AdelicGL2 (𝓞 K) K) i j v
      = (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j := by
  simp only [ent, Matrix.GeneralLinearGroup.coe_one]
  by_cases h : i = j
  · subst h; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
  · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h, map_zero]

theorem ent_one_ne_zero (g : AdelicGL2 (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K)) :
    ent g 1 0 v ≠ 0 ∨ ent g 1 1 v ≠ 0 := by
  by_contra h
  push Not at h
  have hdet : IsUnit ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)).det) :=
    g.isUnit.map Matrix.detMonoidHom
  have h2 := hdet.map (πv v)
  rw [Matrix.det_fin_two, map_sub, map_mul, map_mul] at h2
  change IsUnit (ent g 0 0 v * ent g 1 1 v - ent g 0 1 v * ent g 1 0 v) at h2
  rw [h.1, h.2, mul_zero, mul_zero, sub_zero] at h2
  exact not_isUnit_zero h2

def eps (n : HeightOneSpectrum (𝓞 K) → ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    WithZero (Multiplicative ℤ) :=
  ((Multiplicative.ofAdd (-(n v : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))

omit [NumberField K] in
theorem eps_ne_zero (n : HeightOneSpectrum (𝓞 K) → ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    eps n v ≠ 0 :=
  WithZero.coe_ne_zero

omit [NumberField K] in
theorem eps_le_one (n : HeightOneSpectrum (𝓞 K) → ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    eps n v ≤ 1 := by
  rw [eps, ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero,
    Multiplicative.ofAdd_le]
  omega

omit [NumberField K] in
theorem eps_lt_one {n : HeightOneSpectrum (𝓞 K) → ℕ} {v : HeightOneSpectrum (𝓞 K)}
    (hn : 0 < n v) : eps n v < 1 := by
  rw [eps, ← WithZero.coe_one, WithZero.coe_lt_coe, ← ofAdd_zero,
    Multiplicative.ofAdd_lt]
  omega

theorem exists_valued_eq_eps (n : HeightOneSpectrum (𝓞 K) → ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    ∃ t : v.adicCompletion K, t ≠ 0 ∧ Valued.v t = eps n v :=
  exists_valued_eq_exp_neg (K := K) v (n v)

abbrev CondAt (n : HeightOneSpectrum (𝓞 K) → ℕ) (v : HeightOneSpectrum (𝓞 K))
    (g : AdelicGL2 (𝓞 K) K) : Prop :=
  Valued.v (ent g 1 0 v) ≤ Valued.v (ent g 1 1 v) * eps n v

theorem condAt_borel_mul_imp {n : HeightOneSpectrum (𝓞 K) → ℕ} {v : HeightOneSpectrum (𝓞 K)}
    {b : AdelicGL2 (𝓞 K) K} (hb : b ∈ adelicBorel (𝓞 K) K) {g : AdelicGL2 (𝓞 K) K}
    (h : CondAt n v g) : CondAt n v (b * g) := by
  have h10 : ent b 1 0 v = 0 := by
    have : ((b : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0 := hb
    rw [ent, this, map_zero]
  unfold CondAt at h ⊢
  rw [ent_mul, ent_mul, h10, zero_mul, zero_add, zero_mul, zero_add, map_mul, map_mul, mul_assoc]
  exact mul_le_mul_right h _

theorem condAt_borel_mul_iff {n : HeightOneSpectrum (𝓞 K) → ℕ} {v : HeightOneSpectrum (𝓞 K)}
    {b : AdelicGL2 (𝓞 K) K} (hb : b ∈ adelicBorel (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K) :
    CondAt n v (b * g) ↔ CondAt n v g := by
  refine ⟨fun h => ?_, condAt_borel_mul_imp hb⟩
  have := condAt_borel_mul_imp (inv_mem hb) h
  rwa [inv_mul_cancel_left] at this

theorem condAt_mul_of_cong {n : HeightOneSpectrum (𝓞 K) → ℕ} {v : HeightOneSpectrum (𝓞 K)}
    (hn : 0 < n v) {g k : AdelicGL2 (𝓞 K) K}
    (hint : ∀ i j, Valued.v (ent k i j v) ≤ 1)
    (hcong : ∀ i j, Valued.v (ent k i j v - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j)
      ≤ eps n v)
    (h : CondAt n v g) : CondAt n v (g * k) := by
  unfold CondAt at h ⊢
  rw [ent_mul, ent_mul]
  set c := ent g 1 0 v with hc
  set d := ent g 1 1 v with hd
  have hε1 : eps n v < 1 := eps_lt_one hn

  have hk11 : Valued.v (ent k 1 1 v) = 1 := by
    have h1 := hcong 1 1
    rw [Matrix.one_apply_eq] at h1
    have hlt1 : Valued.v (ent k 1 1 v - 1) < Valued.v (1 : v.adicCompletion K) := by
      rw [Valuation.map_one]; exact lt_of_le_of_lt h1 hε1
    rw [← (Valuation.map_one Valued.v : Valued.v (1 : v.adicCompletion K) = 1)]
    exact Valuation.map_eq_of_sub_lt _ hlt1
  have hk10 : Valued.v (ent k 1 0 v) ≤ eps n v := by
    have h1 := hcong 1 0
    rwa [Matrix.one_apply_ne (by decide), sub_zero] at h1
  have hk01 : Valued.v (ent k 0 1 v) ≤ eps n v := by
    have h1 := hcong 0 1
    rwa [Matrix.one_apply_ne (by decide), sub_zero] at h1

  by_cases hd0 : Valued.v d = 0
  · have hc0 : Valued.v c = 0 := le_antisymm (by rw [hd0, zero_mul] at h; exact h) zero_le
    rw [(Valuation.zero_iff Valued.v).mp hc0, (Valuation.zero_iff Valued.v).mp hd0]
    simp
  · have hdnew : Valued.v (c * ent k 0 1 v + d * ent k 1 1 v) = Valued.v d := by
      have hlt : Valued.v (c * ent k 0 1 v) < Valued.v (d * ent k 1 1 v) := by
        rw [map_mul, map_mul, hk11, mul_one]
        calc Valued.v c * Valued.v (ent k 0 1 v) ≤ Valued.v d * eps n v * eps n v :=
              mul_le_mul' h hk01
          _ < Valued.v d := by
              rw [mul_assoc]
              calc Valued.v d * (eps n v * eps n v) < Valued.v d * 1 := by
                    apply mul_lt_mul_of_pos_left _ (zero_lt_iff.mpr hd0)
                    calc eps n v * eps n v ≤ eps n v * 1 := mul_le_mul_right (eps_le_one n v) _
                      _ = eps n v := mul_one _
                      _ < 1 := hε1
                _ = Valued.v d := mul_one _
      rw [Valuation.map_add_eq_of_lt_right _ hlt, map_mul, hk11, mul_one]
    rw [hdnew]
    calc Valued.v (c * ent k 0 0 v + d * ent k 1 0 v)
        ≤ max (Valued.v (c * ent k 0 0 v)) (Valued.v (d * ent k 1 0 v)) :=
          Valuation.map_add Valued.v _ _
      _ ≤ Valued.v d * eps n v := by
          apply max_le
          · rw [map_mul]
            calc Valued.v c * Valued.v (ent k 0 0 v) ≤ Valued.v d * eps n v * 1 :=
                  mul_le_mul' h (hint 0 0)
              _ = Valued.v d * eps n v := mul_one _
          · rw [map_mul]
            exact mul_le_mul_right hk10 _

theorem cong_inv {n : HeightOneSpectrum (𝓞 K) → ℕ} {v : HeightOneSpectrum (𝓞 K)}
    {k : AdelicGL2 (𝓞 K) K}
    (hint' : ∀ i j, Valued.v (ent k⁻¹ i j v) ≤ 1)
    (hcong : ∀ i j, Valued.v (ent k i j v - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j)
      ≤ eps n v) :
    ∀ i j, Valued.v (ent k⁻¹ i j v
      - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ eps n v := by
  intro i j

  have key : ent k⁻¹ i j v - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j =
      -(ent k⁻¹ i 0 v * (ent k 0 j v - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 j) +
        ent k⁻¹ i 1 v * (ent k 1 j v - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 j)) := by
    have h1 : ent (k⁻¹ * k) i j v = (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j := by
      rw [inv_mul_cancel, ent_one]
    rw [ent_mul] at h1
    have h2 : ent (k⁻¹ * 1) i j v = ent k⁻¹ i j v := by rw [mul_one]
    rw [ent_mul, ent_one, ent_one] at h2
    linear_combination h1 - h2
  rw [key, Valuation.map_neg]
  calc Valued.v (ent k⁻¹ i 0 v * (ent k 0 j v - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 j) +
        ent k⁻¹ i 1 v * (ent k 1 j v - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 j))
      ≤ max (Valued.v (ent k⁻¹ i 0 v * (ent k 0 j v - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 j)))
          (Valued.v (ent k⁻¹ i 1 v * (ent k 1 j v - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 j))) :=
        Valuation.map_add Valued.v _ _
    _ ≤ eps n v := by
        apply max_le <;> rw [map_mul]
        · calc _ ≤ 1 * eps n v := mul_le_mul' (hint' i 0) (hcong 0 j)
            _ = eps n v := one_mul _
        · calc _ ≤ 1 * eps n v := mul_le_mul' (hint' i 1) (hcong 1 j)
            _ = eps n v := one_mul _

theorem condAt_mul_iff_of_cong {n : HeightOneSpectrum (𝓞 K) → ℕ} {v : HeightOneSpectrum (𝓞 K)}
    (hn : 0 < n v) (g : AdelicGL2 (𝓞 K) K) {k : AdelicGL2 (𝓞 K) K}
    (hint : ∀ i j, Valued.v (ent k i j v) ≤ 1) (hint' : ∀ i j, Valued.v (ent k⁻¹ i j v) ≤ 1)
    (hcong : ∀ i j, Valued.v (ent k i j v - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j)
      ≤ eps n v) :
    CondAt n v (g * k) ↔ CondAt n v g := by
  refine ⟨fun h => ?_, condAt_mul_of_cong hn hint hcong⟩
  have := condAt_mul_of_cong (g := g * k) hn hint' (cong_inv hint' hcong) h
  rwa [mul_inv_cancel_right] at this

theorem condAt_mul_of_ent_eq_one {n : HeightOneSpectrum (𝓞 K) → ℕ} {v : HeightOneSpectrum (𝓞 K)}
    (g : AdelicGL2 (𝓞 K) K) {k : AdelicGL2 (𝓞 K) K}
    (hk : ∀ i j, ent k i j v = (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) :
    CondAt n v (g * k) ↔ CondAt n v g := by
  unfold CondAt
  rw [ent_mul, ent_mul, hk, hk, hk, hk]
  simp

theorem isOpen_setOf_condAt {n : HeightOneSpectrum (𝓞 K) → ℕ} {v : HeightOneSpectrum (𝓞 K)}
    (hn : 0 < n v) : IsOpen {g : AdelicGL2 (𝓞 K) K | CondAt n v g} := by
  have hε1 : eps n v < 1 := eps_lt_one hn
  obtain ⟨t, ht0, ht⟩ := exists_valued_eq_eps n v
  obtain ⟨ϖ, hϖ0, hϖ⟩ := exists_valued_eq_exp_neg (K := K) v 1
  have hϖ1 : Valued.v ϖ < 1 := by
    rw [hϖ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  change CondAt n v g at hg
  set c := ent g 1 0 v with hc
  set d := ent g 1 1 v with hd

  have hd0 : d ≠ 0 := by
    intro h0
    rcases ent_one_ne_zero g v with h1 | h1
    · apply h1
      unfold CondAt at hg
      rw [← hd, h0, Valuation.map_zero, zero_mul] at hg
      exact (Valuation.zero_iff Valued.v).mp (le_antisymm hg zero_le)
    · exact h1 h0
  have hvd : Valued.v d ≠ 0 := (Valuation.ne_zero_iff Valued.v).mpr hd0

  refine ⟨{g' | Valued.v (ent g' 1 1 v - d) ≤ Valued.v (d * ϖ)} ∩
    {g' | Valued.v (ent g' 1 0 v - c) ≤ Valued.v (d * t * ϖ)}, ?_, ?_, ?_⟩
  · rintro g' ⟨h1, h2⟩
    change Valued.v (ent g' 1 1 v - d) ≤ Valued.v (d * ϖ) at h1
    change Valued.v (ent g' 1 0 v - c) ≤ Valued.v (d * t * ϖ) at h2
    change CondAt n v g'
    unfold CondAt at hg ⊢
    have hd' : Valued.v (ent g' 1 1 v) = Valued.v d := by
      refine Valuation.map_eq_of_sub_lt Valued.v (lt_of_le_of_lt h1 ?_)
      rw [map_mul]
      calc Valued.v d * Valued.v ϖ < Valued.v d * 1 :=
            mul_lt_mul_of_pos_left hϖ1 (zero_lt_iff.mpr hvd)
        _ = Valued.v d := mul_one _
    rw [hd']
    have hsplit : ent g' 1 0 v = c + (ent g' 1 0 v - c) := by ring
    rw [hsplit]
    calc Valued.v (c + (ent g' 1 0 v - c))
        ≤ max (Valued.v c) (Valued.v (ent g' 1 0 v - c)) := Valuation.map_add Valued.v _ _
      _ ≤ Valued.v d * eps n v := by
          apply max_le hg
          calc Valued.v (ent g' 1 0 v - c) ≤ Valued.v (d * t * ϖ) := h2
            _ = Valued.v d * eps n v * Valued.v ϖ := by rw [map_mul, map_mul, ht]
            _ ≤ Valued.v d * eps n v * 1 := mul_le_mul_right hϖ1.le _
            _ = Valued.v d * eps n v := mul_one _
  · apply IsOpen.inter
    · exact (isOpen_setOf_valued_le v (d * ϖ) (mul_ne_zero hd0 hϖ0)).preimage
        ((continuous_ent 1 1 v).sub continuous_const)
    · exact (isOpen_setOf_valued_le v (d * t * ϖ) (mul_ne_zero (mul_ne_zero hd0 ht0) hϖ0)).preimage
        ((continuous_ent 1 0 v).sub continuous_const)
  · constructor
    · show Valued.v (ent g 1 1 v - d) ≤ Valued.v (d * ϖ)
      rw [← hd, sub_self, Valuation.map_zero]; exact zero_le
    · show Valued.v (ent g 1 0 v - c) ≤ Valued.v (d * t * ϖ)
      rw [← hc, sub_self, Valuation.map_zero]; exact zero_le

theorem isOpen_setOf_not_condAt {n : HeightOneSpectrum (𝓞 K) → ℕ} {v : HeightOneSpectrum (𝓞 K)}
    (hn : 0 < n v) : IsOpen {g : AdelicGL2 (𝓞 K) K | ¬ CondAt n v g} := by
  obtain ⟨t, ht0, ht⟩ := exists_valued_eq_eps n v
  obtain ⟨ϖ, hϖ0, hϖ⟩ := exists_valued_eq_exp_neg (K := K) v 1
  have hϖ1 : Valued.v ϖ < 1 := by
    rw [hϖ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hε1 : eps n v < 1 := eps_lt_one hn
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  change ¬ CondAt n v g at hg
  set c := ent g 1 0 v with hc
  set d := ent g 1 1 v with hd
  unfold CondAt at hg
  push Not at hg

  have hc0 : c ≠ 0 := by
    intro h0; rw [← hc, h0, Valuation.map_zero] at hg; exact (not_lt.mpr zero_le) hg
  have hvc : Valued.v c ≠ 0 := (Valuation.ne_zero_iff Valued.v).mpr hc0
  refine ⟨{g' | Valued.v (ent g' 1 0 v - c) ≤ Valued.v (c * ϖ)} ∩
    {g' | Valued.v (ent g' 1 1 v - d) ≤ Valued.v c}, ?_, ?_, ?_⟩
  · rintro g' ⟨h1, h2⟩
    change Valued.v (ent g' 1 0 v - c) ≤ Valued.v (c * ϖ) at h1
    change Valued.v (ent g' 1 1 v - d) ≤ Valued.v c at h2
    change ¬ CondAt n v g'
    unfold CondAt
    push Not
    have hc' : Valued.v (ent g' 1 0 v) = Valued.v c := by
      refine Valuation.map_eq_of_sub_lt Valued.v (lt_of_le_of_lt h1 ?_)
      rw [map_mul]
      calc Valued.v c * Valued.v ϖ < Valued.v c * 1 :=
            mul_lt_mul_of_pos_left hϖ1 (zero_lt_iff.mpr hvc)
        _ = Valued.v c := mul_one _
    rw [hc']
    have hsplit : ent g' 1 1 v = d + (ent g' 1 1 v - d) := by ring
    rw [hsplit]
    calc Valued.v (d + (ent g' 1 1 v - d)) * eps n v
        ≤ max (Valued.v d) (Valued.v (ent g' 1 1 v - d)) * eps n v :=
          mul_le_mul_left (Valuation.map_add Valued.v _ _) _
      _ < Valued.v c := by
          rcases le_total (Valued.v d) (Valued.v (ent g' 1 1 v - d)) with hle | hle
          · rw [max_eq_right hle]
            calc Valued.v (ent g' 1 1 v - d) * eps n v ≤ Valued.v c * eps n v :=
                  mul_le_mul_left h2 _
              _ < Valued.v c * 1 := mul_lt_mul_of_pos_left hε1 (zero_lt_iff.mpr hvc)
              _ = Valued.v c := mul_one _
          · rw [max_eq_left hle]; exact hg
  · apply IsOpen.inter
    · exact (isOpen_setOf_valued_le v (c * ϖ) (mul_ne_zero hc0 hϖ0)).preimage
        ((continuous_ent 1 0 v).sub continuous_const)
    · exact (isOpen_setOf_valued_le v c hc0).preimage ((continuous_ent 1 1 v).sub continuous_const)
  · constructor
    · show Valued.v (ent g 1 0 v - c) ≤ Valued.v (c * ϖ)
      rw [← hc, sub_self, Valuation.map_zero]; exact zero_le
    · show Valued.v (ent g 1 1 v - d) ≤ Valued.v c
      rw [← hd, sub_self, Valuation.map_zero]; exact zero_le

theorem isClopen_setOf_cond (S : Finset (HeightOneSpectrum (𝓞 K)))
    {n : HeightOneSpectrum (𝓞 K) → ℕ} (hn : ∀ v ∈ S, 0 < n v) :
    IsClopen {g : AdelicGL2 (𝓞 K) K | ∀ v ∈ S, CondAt n v g} := by
  have h : {g : AdelicGL2 (𝓞 K) K | ∀ v ∈ S, CondAt n v g}
      = ⋂ v ∈ S, {g | CondAt n v g} := by
    ext g; simp
  rw [h]
  refine ⟨?_, ?_⟩
  · refine isClosed_biInter fun v hv => ?_
    rw [← isOpen_compl_iff]
    exact isOpen_setOf_not_condAt (hn v hv)
  · exact S.finite_toSet.isOpen_biInter fun v hv => isOpen_setOf_condAt (hn v hv)

end BorelIndicator

noncomputable section

namespace BorelIndicator

open MeasureTheory NumberField NumberField.AdelicHeight NumberField.AdelicLevel AutomorphicForm
  AutomorphicForm.WindowedSiegel IsDedekindDomain Matrix AdelicDock FLT.SmoothVectors

open scoped NNReal Classical

variable {K : Type} [Field K] [NumberField K]

/-
  Pin block 2 — `RS11SC` continued (the place/entry dictionary, `phi0` and its invariance laws) and
  the headline's five conjuncts, pin lines 757–986: `ent_eq_finComponent` 769,
  `ent_eq_one_of_finComponent_eq_one` 773, `ent_eq_one_of_glFin_eq_one` 778, `placeEmbed_apply` 782,
  `glArch_placeEmbed` 785, `finComponent_placeEmbed_self` 789, `finComponent_placeEmbed_of_ne` 793,
  `phi0` 798, `phi0_of_cond` 804, `phi0_of_not_cond` 807, `phi0_eq_of` 809, `phi0_mul_of_cong` 817,
  `phi0_mul_placeEmbed` 844, `phi0_mul_of_arch` 877, `adelicHeight_eq_one_of_compact` 891,
  `cond_one` 902, `phi0_one` 908, `continuous_phi0` 911, `isArchKFinite_phi0` 920,
  `isKfSmooth_phi0` 934, `isInducedSection_phi0` 973. The pin's `P6B.JE2aFlat.*` helpers are the
  port's `FlatInducedSection.*` (`AutomorphicForm/Adelic/InducedSectionFlat.lean`).
-/
theorem ent_eq_finComponent (g : AdelicGL2 (𝓞 K) K) (i j : Fin 2)
    (v : HeightOneSpectrum (𝓞 K)) :
    ent g i j v
      = (finComponent (𝓞 K) K v (glFin (𝓞 K) K g) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j :=
  rfl

theorem ent_eq_one_of_finComponent_eq_one {g : AdelicGL2 (𝓞 K) K} {v : HeightOneSpectrum (𝓞 K)}
    (h : finComponent (𝓞 K) K v (glFin (𝓞 K) K g) = 1) (i j : Fin 2) :
    ent g i j v = (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j := by
  rw [ent_eq_finComponent, h, Matrix.GeneralLinearGroup.coe_one]

theorem ent_eq_one_of_glFin_eq_one {g : AdelicGL2 (𝓞 K) K} (h : glFin (𝓞 K) K g = 1)
    (v : HeightOneSpectrum (𝓞 K)) (i j : Fin 2) :
    ent g i j v = (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j :=
  ent_eq_one_of_finComponent_eq_one (by rw [h, map_one]) i j

theorem placeEmbed_apply (v : HeightOneSpectrum (𝓞 K)) (k : GL (Fin 2) (v.adicCompletion K)) :
    UnramifiedWhittaker.placeEmbed K v k
      = finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v k) := rfl

theorem glArch_placeEmbed (v : HeightOneSpectrum (𝓞 K)) (k : GL (Fin 2) (v.adicCompletion K)) :
    glArch (𝓞 K) K (UnramifiedWhittaker.placeEmbed K v k) = 1 := by
  rw [placeEmbed_apply, glArch_finEmbed]

theorem finComponent_placeEmbed_self (v : HeightOneSpectrum (𝓞 K))
    (k : GL (Fin 2) (v.adicCompletion K)) :
    finComponent (𝓞 K) K v (glFin (𝓞 K) K (UnramifiedWhittaker.placeEmbed K v k)) = k := by
  rw [placeEmbed_apply, glFin_finEmbed, finComponent_localEmbed_self]

theorem finComponent_placeEmbed_of_ne (v : HeightOneSpectrum (𝓞 K))
    (k : GL (Fin 2) (v.adicCompletion K)) {w : HeightOneSpectrum (𝓞 K)} (hw : w ≠ v) :
    finComponent (𝓞 K) K w (glFin (𝓞 K) K (UnramifiedWhittaker.placeEmbed K v k)) = 1 := by
  rw [placeEmbed_apply, glFin_finEmbed, finComponent_localEmbed_of_ne _ _ _ _ hw]

def phi0 (S : Finset (HeightOneSpectrum (𝓞 K))) (n : HeightOneSpectrum (𝓞 K) → ℕ) (s : ℂ)
    (g : AdelicGL2 (𝓞 K) K) : ℂ :=
  if ∀ v ∈ S, CondAt n v g then FlatInducedSection.flatOne K s g else 0

variable (S : Finset (HeightOneSpectrum (𝓞 K))) (n : HeightOneSpectrum (𝓞 K) → ℕ) (s : ℂ)

-- The pin spells the prelude's section `P6B.JE2aFlat.flatOne`; the port homes it at
-- `FlatInducedSection.flatOne`. The statement-level exception is registered in spec/decl_markers.tsv.
theorem phi0_of_cond {g : AdelicGL2 (𝓞 K) K} (h : ∀ v ∈ S, CondAt n v g) :
    phi0 S n s g = FlatInducedSection.flatOne K s g :=
  ite_eq_left h

theorem phi0_of_not_cond {g : AdelicGL2 (𝓞 K) K} (h : ¬ ∀ v ∈ S, CondAt n v g) :
    phi0 S n s g = 0 := ite_eq_right h

theorem phi0_eq_of (g g' : AdelicGL2 (𝓞 K) K)
    (hc : (∀ v ∈ S, CondAt n v g') ↔ ∀ v ∈ S, CondAt n v g)
    (hH : adelicHeight K g' = adelicHeight K g) : phi0 S n s g' = phi0 S n s g := by
  unfold phi0 FlatInducedSection.flatOne
  rw [hH]
  by_cases h : ∀ v ∈ S, CondAt n v g
  · rw [ite_eq_left h, ite_eq_left (hc.mpr h)]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (hc.mp h'))]

theorem phi0_mul_of_cong (hn : ∀ v ∈ S, 0 < n v) (g k : AdelicGL2 (𝓞 K) K)
    (hkf : k ∈ finiteAdelicGL2Subgroup K)
    (hki : glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K)
    (hkc : ∀ v ∈ S, ∀ i j : Fin 2,
      Valued.v ((((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j -
          (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v) ≤ eps n v) :
    phi0 S n s (g * k) = phi0 S n s g := by
  rw [mem_finiteIntegralGL2_iff] at hki
  have hint : ∀ (v : HeightOneSpectrum (𝓞 K)) (i j : Fin 2), Valued.v (ent k i j v) ≤ 1 := fun v i j =>
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hki.1 i j v)
  have hint' : ∀ (v : HeightOneSpectrum (𝓞 K)) (i j : Fin 2), Valued.v (ent k⁻¹ i j v) ≤ 1 :=
    fun v i j => by
      have := hki.2 i j v
      rw [← map_inv] at this
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp this
  have hcong : ∀ v ∈ S, ∀ i j : Fin 2,
      Valued.v (ent k i j v - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ eps n v := by
    intro v hv i j
    have h := hkc v hv i j
    rwa [← ent_one i j v, ent, ent, ← map_sub] at ⊢
  refine phi0_eq_of S n s g (g * k) (forall₂_congr fun v hv => condAt_mul_iff_of_cong (hn v hv) g
    (hint v) (hint' v) (hcong v hv)) ?_
  refine FlatInducedSection.adelicHeight_mul_of_integral_of_rowIsometry g k (fun v i j => ?_)
    (fun v i j => ?_) (fun w => ?_)
  · rw [finComponent_apply]
    exact norm_le_one_of_mem_adicCompletionIntegers (hki.1 i j v)
  · rw [← map_inv, finComponent_apply]
    exact norm_le_one_of_mem_adicCompletionIntegers (hki.2 i j v)
  · rw [(mem_finiteAdelicGL2Subgroup_iff K k).mp hkf, map_one]
    exact isRowIsometry_one

theorem phi0_mul_placeEmbed {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S)
    (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K) :
    phi0 S n s (g * UnramifiedWhittaker.placeEmbed K v
      (Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))
        kv)) = phi0 S n s g := by
  set k := UnramifiedWhittaker.placeEmbed K v
      (Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))
        kv) with hk
  refine phi0_eq_of S n s g (g * k) (forall₂_congr fun w hw => condAt_mul_of_ent_eq_one g fun i j =>
    ent_eq_one_of_finComponent_eq_one (finComponent_placeEmbed_of_ne v _ (fun h => hv (h ▸ hw))) i j) ?_
  refine FlatInducedSection.adelicHeight_mul_of_integral_of_rowIsometry g k (fun w i j => ?_)
    (fun w i j => ?_) (fun w => ?_)
  · by_cases hw : w = v
    · subst hw
      rw [hk, finComponent_placeEmbed_self]
      exact norm_le_one_of_mem_adicCompletionIntegers (by
        change (algebraMap (w.adicCompletionIntegers K) (w.adicCompletion K))
          ((kv : Matrix (Fin 2) (Fin 2) _) i j) ∈ _
        exact SetLike.coe_mem _)
    · rw [hk, finComponent_placeEmbed_of_ne v _ hw, Matrix.GeneralLinearGroup.coe_one]
      by_cases hij : i = j
      · subst hij; rw [Matrix.one_apply_eq, norm_one]
      · rw [Matrix.one_apply_ne hij, norm_zero]; exact zero_le_one
  · by_cases hw : w = v
    · subst hw
      rw [hk, ← map_inv, ← map_inv, ← map_inv, finComponent_placeEmbed_self]
      exact norm_le_one_of_mem_adicCompletionIntegers (by
        change (algebraMap (w.adicCompletionIntegers K) (w.adicCompletion K))
          (((kv⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) _) i j) ∈ _
        exact SetLike.coe_mem _)
    · rw [hk, ← map_inv, ← map_inv, ← map_inv, finComponent_placeEmbed_of_ne v _ hw,
        Matrix.GeneralLinearGroup.coe_one]
      by_cases hij : i = j
      · subst hij; rw [Matrix.one_apply_eq, norm_one]
      · rw [Matrix.one_apply_ne hij, norm_zero]; exact zero_le_one
  · rw [hk, glArch_placeEmbed, map_one]
    exact isRowIsometry_one

theorem phi0_mul_of_arch (g k : AdelicGL2 (𝓞 K) K) (hkf : glFin (𝓞 K) K k = 1)
    (hka : ∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) :
    phi0 S n s (g * k) = phi0 S n s g := by
  refine phi0_eq_of S n s g (g * k) (forall₂_congr fun w hw =>
    condAt_mul_of_ent_eq_one g (ent_eq_one_of_glFin_eq_one hkf w)) ?_
  refine FlatInducedSection.adelicHeight_mul_of_integral_of_rowIsometry g k (fun w i j => ?_)
    (fun w i j => ?_) hka
  · rw [hkf, map_one, Matrix.GeneralLinearGroup.coe_one]
    by_cases hij : i = j
    · subst hij; rw [Matrix.one_apply_eq, norm_one]
    · rw [Matrix.one_apply_ne hij, norm_zero]; exact zero_le_one
  · rw [hkf, inv_one, map_one, Matrix.GeneralLinearGroup.coe_one]
    by_cases hij : i = j
    · subst hij; rw [Matrix.one_apply_eq, norm_one]
    · rw [Matrix.one_apply_ne hij, norm_zero]; exact zero_le_one

theorem adelicHeight_eq_one_of_compact (k : AdelicGL2 (𝓞 K) K)
    (hki : glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K)
    (hka : ∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) :
    adelicHeight K k = 1 := by
  rw [mem_finiteIntegralGL2_iff] at hki
  have h := FlatInducedSection.adelicHeight_mul_of_integral_of_rowIsometry 1 k (fun v i j => ?_)
    (fun v i j => ?_) hka
  · rwa [one_mul, FlatInducedSection.adelicHeight_one] at h
  · rw [finComponent_apply]
    exact norm_le_one_of_mem_adicCompletionIntegers (hki.1 i j v)
  · rw [← map_inv, finComponent_apply]
    exact norm_le_one_of_mem_adicCompletionIntegers (hki.2 i j v)

theorem cond_one : ∀ v ∈ S, CondAt n v (1 : AdelicGL2 (𝓞 K) K) := by
  intro v _
  unfold CondAt
  rw [ent_one, Matrix.one_apply_ne (by decide), Valuation.map_zero]
  exact zero_le

theorem phi0_one : phi0 S n s 1 = 1 := by
  rw [phi0_of_cond S n s (cond_one S n), FlatInducedSection.flatOne_apply_one]

theorem continuous_phi0 (hn : ∀ v ∈ S, 0 < n v) : Continuous (phi0 (K := K) S n s) := by
  have hcl := isClopen_setOf_cond S hn
  have hflat : Continuous (FlatInducedSection.flatOne K s) :=
    FlatInducedSection.continuous_flatOne (NumberField.AdelicHeight.continuous_adelicHeight K) s
  unfold phi0
  refine continuous_if (fun a ha => ?_) hflat.continuousOn continuousOn_const
  rw [hcl.frontier_eq] at ha
  exact absurd ha (Set.notMem_empty a)

theorem isArchKFinite_phi0 : IsArchKFinite K (phi0 S n s) := by
  intro w
  refine ⟨{phi0 S n s}, ?_⟩
  rintro _ ⟨k, hk, rfl⟩
  have heq : (fun x => phi0 S n s (x * adelicArchGLInclAt K w (k : GL (Fin 2) w.Completion)))
      = phi0 S n s := by
    funext x
    have hfin : glFin (𝓞 K) K (adelicArchGLInclAt K w (k : GL (Fin 2) w.Completion)) = 1 := by
      rw [show adelicArchGLInclAt K w (k : GL (Fin 2) w.Completion) =
        adelicArchGLIncl K (archGLIncl K w (k : GL (Fin 2) w.Completion)) from rfl,
        glFin_adelicArchGLIncl]
    exact phi0_eq_of S n s x _
      (forall₂_congr fun v hv => condAt_mul_of_ent_eq_one x (ent_eq_one_of_glFin_eq_one hfin v))
      (FlatInducedSection.adelicHeight_mul_adelicArchGLInclAt w ⟨k, hk⟩ x)
  rw [heq]
  exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_singleton_self _))

theorem isKfSmooth_phi0 (hn : ∀ v ∈ S, 0 < n v) : IsKfSmooth K (phi0 S n s) := by
  rw [isKfSmooth_iff, isSmoothVector_iff_isOpen_stabilizer]

  choose t ht0 ht using fun v : HeightOneSpectrum (𝓞 K) => exists_valued_eq_eps n v

  set O : Set (AdelicGL2 (𝓞 K) K) :=
    {k | glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K} ∩
      ⋂ v ∈ S, ⋂ i : Fin 2, ⋂ j : Fin 2,
        {k | Valued.v (ent k i j v - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j)
          ≤ Valued.v (t v)} with hO
  have hOopen : IsOpen O := by
    refine IsOpen.inter ?_ ?_
    · exact (isOpen_finiteLevelZero (𝓞 K) K (N := ⊤) (by simp)).preimage (continuous_glFin (𝓞 K) K)
    · refine S.finite_toSet.isOpen_biInter fun v _ =>
        isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
      exact (isOpen_setOf_valued_le v (t v) (ht0 v)).preimage ((continuous_ent i j v).sub continuous_const)
  have hO1 : (1 : AdelicGL2 (𝓞 K) K) ∈ O := by
    refine ⟨?_, ?_⟩
    · show glFin (𝓞 K) K (1 : AdelicGL2 (𝓞 K) K) ∈ finiteIntegralGL2 (𝓞 K) K
      rw [map_one]; exact one_mem _
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    intro v _ i j
    rw [ent_one, sub_self, Valuation.map_zero]
    exact zero_le

  set G' := finiteAdelicGL2Subgroup K
  have hsub : ((↑) : G' → AdelicGL2 (𝓞 K) K) ⁻¹' O ⊆
      (MulAction.stabilizer G' (RightTranslationFn.mk (phi0 S n s)) : Set G') := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := hk
    simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hk2
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Subgroup.smul_def]
    refine RightTranslationFn.ext fun g => ?_
    rw [RightTranslationFn.toFun_smul, RightTranslationFn.toFun_mk]
    refine phi0_mul_of_cong S n s hn g k k.2 hk1 fun v hv i j => ?_
    have h := hk2 v hv i j
    rw [ht v] at h
    rwa [← ent_one i j v, ent, ent, ← map_sub] at h
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset ?_ hsub)
  exact (hOopen.preimage continuous_subtype_val).mem_nhds (by simpa using hO1)

theorem isInducedSection_phi0
    (α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (hflat : IsInducedSection (𝓞 K) K (etaFst 1 α hα s) (etaSnd 1 α hα s)
      (fun g : AdelicGL2 (𝓞 K) K => ((adelicHeight K g : ℝ) : ℂ) ^ (s + 1 / 2))) :
    IsInducedSection (𝓞 K) K (etaFst 1 α hα s) (etaSnd 1 α hα s) (phi0 S n s) := by
  intro b hb g
  by_cases h : ∀ v ∈ S, CondAt n v g
  · have h' : ∀ v ∈ S, CondAt n v (b * g) := fun v hv => condAt_borel_mul_imp hb (h v hv)
    rw [phi0_of_cond S n s h', phi0_of_cond S n s h]
    exact hflat b hb g
  · have h' : ¬ ∀ v ∈ S, CondAt n v (b * g) :=
      fun h' => h fun v hv => (condAt_borel_mul_iff hb g).mp (h' v hv)
    rw [phi0_of_not_cond S n s h', phi0_of_not_cond S n s h, mul_zero]

end BorelIndicator

end

theorem isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow
    (K : Type) [Field K] [NumberField K] :
    let α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ)
      (S : Finset (HeightOneSpectrum (𝓞 K))) (n : HeightOneSpectrum (𝓞 K) → ℕ)
      (_hn : ∀ v ∈ S, 0 < n v),
    let φ₀ : AdelicGL2 (𝓞 K) K → ℂ := fun g =>
      if ∀ v ∈ S,
          Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
            Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) *
              ((Multiplicative.ofAdd (-(n v : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
      then ((adelicHeight K g : ℝ) : ℂ) ^ (s + 1 / 2) else 0
    IsInducedSection (𝓞 K) K (etaFst 1 α hα s) (etaSnd 1 α hα s) φ₀ ∧
    Continuous φ₀ ∧ IsArchKFinite K φ₀ ∧ IsKfSmooth K φ₀ ∧
    (∀ (g k : AdelicGL2 (𝓞 K) K), k ∈ finiteAdelicGL2Subgroup K →
      glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
      (∀ v ∈ S, ∀ i j : Fin 2,
        Valued.v ((((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j -
            (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v) ≤
          ((Multiplicative.ofAdd (-(n v : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
      φ₀ (g * k) = φ₀ g) ∧
    (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
        φ₀ (g * UnramifiedWhittaker.placeEmbed K v
          (Matrix.GeneralLinearGroup.map
            (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = φ₀ g) ∧
    (∀ (g k : AdelicGL2 (𝓞 K) K), glFin (𝓞 K) K k = 1 →
      (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) →
      φ₀ (g * k) = φ₀ g) ∧
    (∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
      (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) →
      φ₀ k = 0 ∨ φ₀ k = 1) ∧
    φ₀ 1 = 1 := by
  intro α hα s S n hn φ₀
  have hφ : φ₀ = BorelIndicator.phi0 S n s := rfl
  rw [hφ]
  obtain ⟨-, -, hflat⟩ := isInducedSection_adelicHeight_cpow K
  refine ⟨BorelIndicator.isInducedSection_phi0 S n s α hα (hflat hα s),
    BorelIndicator.continuous_phi0 S n s hn, BorelIndicator.isArchKFinite_phi0 S n s,
    BorelIndicator.isKfSmooth_phi0 S n s hn,
    fun g k hkf hki hkc => BorelIndicator.phi0_mul_of_cong S n s hn g k hkf hki hkc,
    fun v hv kv g => BorelIndicator.phi0_mul_placeEmbed S n s hv kv g,
    fun g k hkf hka => BorelIndicator.phi0_mul_of_arch S n s g k hkf hka,
    fun k hki hka => ?_, BorelIndicator.phi0_one S n s⟩
  by_cases h : ∀ v ∈ S, BorelIndicator.CondAt n v k
  · right
    rw [BorelIndicator.phi0_of_cond S n s h, FlatInducedSection.flatOne,
      BorelIndicator.adelicHeight_eq_one_of_compact k hki hka, Complex.ofReal_one, Complex.one_cpow]
  · left
    exact BorelIndicator.phi0_of_not_cond S n s h

end AutomorphicForm
