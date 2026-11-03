/-
  The Bruhat Eisenstein series in the half-plane.

  A *flat section* at `s` is an induced section `φ s` with `etaFst μ α hα s` and `etaSnd ν α hα s`; the
  *flat Eisenstein series* it generates is

    `E (s) g = φ s g + ∑' ξ : F, φ s (adelicWeyl * unipotentGL2 (algebraMap F 𝔸 ξ) * g)`,

  the Bruhat expansion over the rational unipotent orbit. This module carries the three facts about
  `E` that the Rankin–Selberg and Bruhat-transversal developments consume, all in the half-plane
  `re s > 1/2`:

  * `bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family` — for a family of sections
    depending holomorphically on `s`, `E` is holomorphic on `{re s > 1/2}`, at every `g` (the sum over
    `ξ` converges locally uniformly there, by the transversal summand estimate);
  * `exists_flatEisenstein_mul_le_mul_archHeight_rpow_of_mem_centreCutSiegelSet` — on the centre-cut
    Siegel set, `‖E (s) (s · t)‖` is bounded by a constant times `archHeight (glArch s) ^ (σ + 1/2)`,
    uniformly for `re s = σ > 1/2` (the summand is summable and the bound is the local height
    comparison);
  * `constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral` — the constant term of `E`
    is the section plus the Weyl-intertwining integral:
    `constantTerm (φ + ∑' ξ φ (w n(ξ) ·)) g = φ g + (vol (adelicBox))⁻¹ * weylIntertwiningIntegral φ g`.

  The fourth row, `exists_flat_isInducedSection_family_eq_of_isInducedSection`, is the dictionary the
  other three quantify over: from one induced section `φ₀` at `s₀` that is archimedean-`K`-finite,
  `K_f`-smooth and continuous, it produces a whole family `ψ` of induced sections with `ψ s₀ = φ₀`,
  continuous in `(s, g)`, holomorphic in `s`, and constant on the `K`-translates at fixed `s`.

  Transcribed from the four pin `S_` files (pinned `aa2d8b3`), whose `Theorems/` wrappers carry the
  headlines' statements:

  * `P2M/Sol/S_AutomorphicForm_bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family.lean`
  * `P2M/Sol/S_AutomorphicForm_exists_flatEisenstein_mul_le_mul_archHeight_rpow_of_mem_centreCutSiegelSet.lean`
  * `P2M/Sol/S_AutomorphicForm_exists_flat_isInducedSection_family_eq_of_isInducedSection.lean`
  * `P2M/Sol/S_AutomorphicForm_constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral.lean`

  It rests on the port's section layer (`InducedSection`, `InducedSectionFlat`, `EtaFamily`), the Weyl
  integral (`WeylIntertwining`), the transversal summand estimate (`WeylIntegrable`) and the adelic
  height (`AdelicHeight`); the pin's file-level labels (`SolE_j1`, `Ws37EisMaj`, `BruhatCTSol`) are
  proof-search artefacts and are dropped from the namespaces. The pin's first `S_` file imports
  `Mathlib`; the port names the four mathlib modules it needs instead (`Integral.Pi`,
  `Log.Summable`, `InfiniteSum.Order`, and `Complex.LocallyUniformLimit` for the `tsum`
  differentiability step).

  **Visibility.** Helper visibility follows the pin's: the row-1 and row-2 preludes are `private`
  there and stay `private` here (the checker does not diff a private declaration, and making one
  public produces a `MISMATCH` no re-spelling fixes — FR-0128); the row-3 and row-4 helpers are
  public in the pin and are public here.

  **Wiring.** `spec/check_port.py` owns every public declaration here: the four `Theorems/` wrappers
  and the four `S_` files are the wire.
  spec-pin: Theorems/Thm_AutomorphicForm_bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family.lean
  spec-pin: Theorems/Thm_AutomorphicForm_exists_flatEisenstein_mul_le_mul_archHeight_rpow_of_mem_centreCutSiegelSet.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_exists_flatEisenstein_mul_le_mul_archHeight_rpow_of_mem_centreCutSiegelSet.lean
  spec-pin: Theorems/Thm_AutomorphicForm_exists_flat_isInducedSection_family_eq_of_isInducedSection.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_exists_flat_isInducedSection_family_eq_of_isInducedSection.lean
  spec-pin: Theorems/Thm_AutomorphicForm_constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.WeylIntertwining
import FLTForHuman.AutomorphicForm.Adelic.InducedSectionFlat
import FLTForHuman.AutomorphicForm.Adelic.EtaFamily
import FLTForHuman.AutomorphicForm.Adelic.ConstantTerm
import FLTForHuman.AutomorphicForm.Adelic.LsXi
import FLTForHuman.AutomorphicForm.Adelic.ArchKFinite
import FLTForHuman.AutomorphicForm.Adelic.SmoothAutomorphicFn
import FLTForHuman.AutomorphicForm.Adelic.WindowedSiegel.CentreCutSet
import FLTForHuman.AutomorphicForm.Adelic.WindowedSiegel.RowIsometry
import FLTForHuman.AutomorphicForm.Adelic.WeylIntegrable
import FLTForHuman.NumberTheory.AdelicHeight
import FLTForHuman.NumberTheory.AdelicLevel.Projections
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.Complex.LocallyUniformLimit

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.InfinitePlace NumberField.AdelicBox NumberField.AdelicLevel
open NumberField.AdelicHaar NumberField.AdelicHeight
open AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped NNReal

namespace AutomorphicForm

/-! ## The differentiability row

The summand `ξ ↦ φ s (w · n(ξ) · g)` is bounded by the `α`-weight of the `y`-coordinate of
`ξ`, uniformly on a compact `S ∋ s`, and the resulting majorant is summable in the
half-plane. That gives local uniform convergence of the `tsum`, hence its holomorphy. -/

namespace BruhatEisensteinDiff

open WeylIntegrable

section FamilyBox

variable {A : Type*} [CommRing A]

/-- The `S`-family form of `exists_bound_on_unitBox`: a continuous function on `ℂ × GL₂` is
bounded on `S × unitBox C` after right translation by `g`, uniformly in `(s, k)`. -/
private theorem exists_bound_on_unitBox_family [TopologicalSpace A] [IsTopologicalRing A]
    [T1Space A] {C : Set A} (hC : IsCompact C) {φ : ℂ → GL (Fin 2) A → ℂ}
    (hφ : Continuous (fun p : ℂ × GL (Fin 2) A => φ p.1 p.2)) {S : Set ℂ} (hS : IsCompact S)
    (g : GL (Fin 2) A) : ∃ B : ℝ, ∀ s ∈ S, ∀ k ∈ unitBox C, ‖φ s (k * g)‖ ≤ B := by
  have hpair : Continuous (fun p : ℂ × GL (Fin 2) A => (p.1, p.2 * g)) := by fun_prop
  obtain ⟨B, hB⟩ := (hS.prod (isCompact_unitBox hC)).exists_bound_of_continuousOn
    (hφ.comp hpair).continuousOn
  exact ⟨B, fun s hs k hk => hB (s, k) (Set.mk_mem_prod hs hk)⟩

end FamilyBox

/-- Two-sided exponent comparison: for `0 < t` and `a ≤ b ≤ c`, one of `t ^ (-a)`,
`t ^ (-c)` dominates `t ^ (-b)`, depending on which side of `1` the base lies. -/
private theorem rpow_neg_le_add {t : ℝ} (ht : 0 < t) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    t ^ (-b) ≤ t ^ (-a) + t ^ (-c) := by
  rcases le_or_gt 1 t with h1 | h1
  · exact (Real.rpow_le_rpow_of_exponent_le h1 (neg_le_neg hab)).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg ht.le _))
  · exact (Real.rpow_le_rpow_of_exponent_ge ht h1.le (neg_le_neg hbc)).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg ht.le _))

section Family

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F

/-- Uniform family bound for the Weyl–unipotent translates of a holomorphic family of
induced sections: on a compact `S ∋ s` the `M`-factor stays in the compact box
`unitBox (entrySet F)`, so the translate is bounded by a constant times the `α`-weight. -/
private theorem exists_family_bound (α : (𝔸)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (μ ν : (𝔸)ˣ →* ℂˣ) (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
    (hjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
    {S : Set ℂ} (hS : IsCompact S) (g : AdelicGL2 (𝓞 F) F) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ S, ∀ u : 𝔸,
      ‖φ s ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 u * g)‖ ≤
        B * ((α (yUnit (selRel F u.1 u.2)) : ℝˣ) : ℝ) ^ (-(2 * s.re + 1)) := by
  obtain ⟨B, hB⟩ := exists_bound_on_unitBox_family (isCompact_entrySet F) hjc hS g
  refine ⟨max B 0, le_max_right _ _, fun s hs u => ?_⟩
  rw [norm_apply_weyl_unipotent_eq F α hα μ ν s (φ s) hμ hν (hφ s) u g, mul_comm]
  exact mul_le_mul_of_nonneg_right
    ((hB s hs _ (mFactor_mem_unitBox F u.1 u.2)).trans (le_max_left _ _))
    (Real.rpow_nonneg (hα _).le _)

/-- Summability of the `α`-weight majorant in the half-plane: the section
`k ↦ adelicHeight k ^ (σ + 1/2)` is square-integrable enough that the transversal summand
estimate majorises the weight by `‖ψ (k₀ * g)‖⁻¹` times the summand norm. -/
private theorem summable_alpha_rpow (α : (𝔸)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (hone : IsUnitaryChar (𝓞 F) F (1 : (𝔸)ˣ →* ℂˣ))
    (hflat : ∀ s : ℂ, IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s)
      (fun k : AdelicGL2 (𝓞 F) F => ((adelicHeight F k : ℝ) : ℂ) ^ (s + 1 / 2)))
    (hsumm : ∀ (s : ℂ), 1 / 2 < s.re → ∀ (ψ : AdelicGL2 (𝓞 F) F → ℂ),
      IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) ψ → Continuous ψ →
      ∀ g : AdelicGL2 (𝓞 F) F, Summable (fun ξ : F =>
        ‖ψ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F 𝔸 ξ) * g)‖))
    (σ : ℝ) (hσ : 1 / 2 < σ) (g : AdelicGL2 (𝓞 F) F) :
    Summable (fun ξ : F =>
      ((α (yUnit (selRel F (algebraMap F 𝔸 ξ).1 (algebraMap F 𝔸 ξ).2)) : ℝˣ) : ℝ) ^
        (-(2 * σ + 1))) := by
  set ψ : AdelicGL2 (𝓞 F) F → ℂ := fun k => ((adelicHeight F k : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2)
    with hψ
  have hψc : Continuous ψ :=
    (Complex.continuous_ofReal.comp (continuous_adelicHeight F)).cpow continuous_const
      (fun k => Complex.ofReal_mem_slitPlane.2 (adelicHeight_pos k))
  have hsum := hsumm (σ : ℂ) (by simpa using hσ) ψ (hflat (σ : ℂ)) hψc g
  have hKc : IsCompact (unitBox (entrySet F)) := isCompact_unitBox (isCompact_entrySet F)
  have hne : (unitBox (entrySet F)).Nonempty := ⟨_, mFactor_mem_unitBox F 0 0⟩
  have hcont : ContinuousOn (fun k : AdelicGL2 (𝓞 F) F => ‖ψ (k * g)‖) (unitBox (entrySet F)) :=
    (hψc.comp (continuous_id.mul continuous_const)).norm.continuousOn
  obtain ⟨k₀, -, hmin⟩ := hKc.exists_isMinOn hne hcont
  have hm₀ : 0 < ‖ψ (k₀ * g)‖ := by
    simp only [hψ]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (adelicHeight_pos _)]
    exact Real.rpow_pos_of_pos (adelicHeight_pos _) _
  refine Summable.of_nonneg_of_le (fun ξ => Real.rpow_nonneg (hα _).le _) (fun ξ => ?_)
    (hsum.mul_left (‖ψ (k₀ * g)‖)⁻¹)
  show ((α (yUnit (selRel F (algebraMap F 𝔸 ξ).1 (algebraMap F 𝔸 ξ).2)) : ℝˣ) : ℝ) ^
      (-(2 * σ + 1)) ≤
    (‖ψ (k₀ * g)‖)⁻¹ * ‖ψ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F 𝔸 ξ) * g)‖
  have hid := norm_apply_weyl_unipotent_eq F α hα 1 1 (σ : ℂ) ψ hone hone (hflat (σ : ℂ))
    (algebraMap F 𝔸 ξ) g
  rw [adelicWeyl_inv' F, Complex.ofReal_re] at hid
  have hm : ‖ψ (k₀ * g)‖ ≤
      ‖ψ (mFactor F (algebraMap F 𝔸 ξ).1 (algebraMap F 𝔸 ξ).2 * g)‖ :=
    hmin (mFactor_mem_unitBox F _ _)
  rw [hid, ← div_eq_inv_mul, le_div_iff₀ hm₀]
  exact mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg (hα _).le _)

end Family

end BruhatEisensteinDiff

/-- For a family of induced sections depending holomorphically on `s`, the flat Eisenstein
series is holomorphic on the half-plane `re s > 1/2`, at every `g`. -/
theorem bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
      (g : AdelicGL2 (𝓞 F) F),
    DifferentiableOn ℂ
      (fun s : ℂ => φ s g + ∑' ξ : F, φ s (adelicWeyl (𝓞 F) F
        * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g))
      {z : ℂ | 1 / 2 < z.re} := by
  intro α hα μ ν hμ hν φ hφ hjc hhol g
  have hpack := isInducedSection_adelicHeight_cpow F
  obtain ⟨-, hone, hflat⟩ := hpack
  have hsumm : ∀ (s : ℂ), 1 / 2 < s.re → ∀ (ψ : AdelicGL2 (𝓞 F) F → ℂ),
      IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) ψ → Continuous ψ →
      ∀ g : AdelicGL2 (𝓞 F) F, Summable (fun ξ : F =>
        ‖ψ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)‖) :=
    fun s hs ψ hψ hψc g =>
      bruhatTransversal_summand_norm_summable_of_re_gt_half F hα 1 1 hone hone s hs ψ hψ hψc g
  intro s₀ hs₀
  have hre : (1 : ℝ) / 2 < s₀.re := hs₀
  obtain ⟨r, hr0, hσ₀⟩ : ∃ r : ℝ, 0 < r ∧ 1 / 2 < s₀.re - r :=
    ⟨(s₀.re - 1 / 2) / 2, by linarith, by linarith⟩
  obtain ⟨B, hB0, hB⟩ := BruhatEisensteinDiff.exists_family_bound F α hα μ ν hμ hν φ hφ
    hjc (isCompact_closedBall s₀ r) g
  have hsum₀ := BruhatEisensteinDiff.summable_alpha_rpow F α hα hone (hflat hα) hsumm
    (s₀.re - r) hσ₀ g
  have hsum₁ := BruhatEisensteinDiff.summable_alpha_rpow F α hα hone (hflat hα) hsumm
    (s₀.re + r) (by linarith) g
  have hM := (hsum₀.add hsum₁).mul_left B
  have hD : DifferentiableOn ℂ (fun s : ℂ => ∑' ξ : F,
      φ s (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g))
      (Metric.ball s₀ r) := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      (F := fun (ξ : F) (s : ℂ) =>
        φ s (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g))
      hM (fun ξ => (hhol _).differentiableOn) Metric.isOpen_ball (fun ξ s hs => ?_)
    have hwin : |s.re - s₀.re| < r := by
      have h1 : ‖s - s₀‖ < r := by simpa [Complex.dist_eq] using hs
      exact lt_of_le_of_lt (by simpa using Complex.abs_re_le_norm (s - s₀)) h1
    obtain ⟨hw₁, hw₂⟩ := abs_lt.1 hwin
    have hs' : s ∈ Metric.closedBall s₀ r := Metric.ball_subset_closedBall hs
    show ‖φ s (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)‖ ≤
      B * (((α (WeylIntegrable.yUnit (WeylIntegrable.selRel F
                (algebraMap F (AdeleRing (𝓞 F) F) ξ).1
                (algebraMap F (AdeleRing (𝓞 F) F) ξ).2)) : ℝˣ) : ℝ) ^
                  (-(2 * (s₀.re - r) + 1)) +
            ((α (WeylIntegrable.yUnit (WeylIntegrable.selRel F
                (algebraMap F (AdeleRing (𝓞 F) F) ξ).1
                (algebraMap F (AdeleRing (𝓞 F) F) ξ).2)) : ℝˣ) : ℝ) ^
                  (-(2 * (s₀.re + r) + 1)))
    refine le_trans ?_ (mul_le_mul_of_nonneg_left
      (BruhatEisensteinDiff.rpow_neg_le_add (hα _) (a := 2 * (s₀.re - r) + 1)
        (b := 2 * s.re + 1) (c := 2 * (s₀.re + r) + 1) (by linarith) (by linarith)) hB0)
    rw [← WeylIntegrable.adelicWeyl_inv' F]
    exact hB s hs' _
  have hall : DifferentiableOn ℂ (fun s : ℂ => φ s g + ∑' ξ : F,
      φ s (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g))
      (Metric.ball s₀ r) :=
    (hhol g).differentiableOn.add hD
  exact (hall.differentiableAt
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr0))).differentiableWithinAt

/-! ## The dictionary row

A family of flat sections is the `s`-dependence of a family of induced sections: from one
archimedean-`K`-finite, `K_f`-smooth, continuous induced section `φ₀` at `s₀`, multiplying by
`hpow (s - s₀)` produces the family `ψ`, with every property the dictionary promises. -/

namespace FlatSectionFamily

open WeylIntegrable FLT.SmoothVectors

variable {F : Type} [Field F] [NumberField F]

/-- The compact-open invariance package: `k` is `K_f`-integral and archimedean row-isometric
at every infinite place. -/
private def InK (k : AdelicGL2 (𝓞 F) F) : Prop :=
  glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
    ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))

/-- The adèlic height is invariant under the right action of `InK`. -/
private theorem adelicHeight_mul_of_inK (g : AdelicGL2 (𝓞 F) F) {k : AdelicGL2 (𝓞 F) F}
    (hk : InK k) : adelicHeight F (g * k) = adelicHeight F g := by
  obtain ⟨h1, h2⟩ := norm_finComponent_le_one_of_mem F hk.1
  unfold adelicHeight
  rw [map_mul, map_mul, archHeight_mul_rowIsometry F _ hk.2, finHeight_mul_integral _ _ h1 h2]

private theorem adelicHeight_one' : adelicHeight F 1 = 1 :=
  FlatInducedSection.adelicHeight_one F

/-- The height of an `InK` element is one. -/
private theorem adelicHeight_eq_one_of_inK {k : AdelicGL2 (𝓞 F) F} (hk : InK k) :
    adelicHeight F k = 1 := by
  have h := adelicHeight_mul_of_inK (1 : AdelicGL2 (𝓞 F) F) hk
  rwa [one_mul, adelicHeight_one'] at h

/-- The archimedean row-isometry subgroup at one place is an `InK` subgroup. -/
private theorem inK_of_mem_archRowIsometrySubgroup (w : InfinitePlace F) {k : AdelicGL2 (𝓞 F) F}
    (hk : k ∈ archRowIsometrySubgroup F w) : InK k := by
  obtain ⟨k₀, hk₀, rfl⟩ := Subgroup.mem_map.mp hk
  refine ⟨?_, fun v => ?_⟩
  · show glFin (𝓞 F) F (adelicArchGLIncl F (archGLIncl F w k₀)) ∈ finiteIntegralGL2 (𝓞 F) F
    rw [glFin_adelicArchGLIncl]
    exact one_mem _
  · show IsRowIsometry (archComponent F v (glArch (𝓞 F) F (adelicArchGLIncl F (archGLIncl F w k₀))))
    rw [glArch_adelicArchGLIncl]
    by_cases hvw : v = w
    · subst hvw
      rw [archComponent_archGLIncl_self]
      exact hk₀
    · rw [archComponent_archGLIncl_of_ne F hvw]
      exact isRowIsometry_one

/-- The finite-adelic integral subgroup is an `InK` subgroup. -/
private theorem inK_of_mem_finiteAdelic {u : AdelicGL2 (𝓞 F) F} (hu : u ∈ finiteAdelicGL2Subgroup F)
    (hi : glFin (𝓞 F) F u ∈ finiteIntegralGL2 (𝓞 F) F) : InK u := by
  refine ⟨hi, fun w => ?_⟩
  rw [(mem_finiteAdelicGL2Subgroup_iff F u).mp hu, map_one]
  exact isRowIsometry_one

/-- The pin's `hpow t g = adelicHeight g ^ t`: the flat section of exponent `t`, the shift of
`FlatInducedSection.flatOne` by `1/2`. -/
private def hpow (t : ℂ) (g : AdelicGL2 (𝓞 F) F) : ℂ := ((adelicHeight F g : ℝ) : ℂ) ^ t

private theorem hpow_mul_inK (t : ℂ) (g : AdelicGL2 (𝓞 F) F) {k : AdelicGL2 (𝓞 F) F}
    (hk : InK k) : hpow t (g * k) = hpow t g := by
  unfold hpow
  rw [adelicHeight_mul_of_inK g hk]

private theorem hpow_of_inK (t : ℂ) {k : AdelicGL2 (𝓞 F) F} (hk : InK k) : hpow t k = 1 := by
  unfold hpow
  rw [adelicHeight_eq_one_of_inK hk, Complex.ofReal_one, Complex.one_cpow]

private theorem hpow_zero (g : AdelicGL2 (𝓞 F) F) : hpow 0 g = 1 := by
  unfold hpow
  exact Complex.cpow_zero _

/-- `hpow t` is `K_f`-smooth: its stabilizer contains the preimage of the finite integral
subgroup, an open subgroup. -/
private theorem isKfSmooth_hpow (t : ℂ) : IsKfSmooth F (hpow t) := by
  rw [isKfSmooth_iff, isSmoothVector_iff_isOpen_stabilizer]
  refine Subgroup.isOpen_mono
    (H₁ := Subgroup.comap ((glFin (𝓞 F) F).comp (finiteAdelicGL2Subgroup F).subtype)
      (finiteIntegralGL2 (𝓞 F) F)) ?_ ?_
  · intro u hu
    rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def]
    refine RightTranslationFn.ext fun g => ?_
    rw [RightTranslationFn.toFun_smul]
    exact hpow_mul_inK t g (inK_of_mem_finiteAdelic u.2 hu)
  · exact (isOpen_finiteLevelZero (𝓞 F) F top_ne_bot).preimage
      ((continuous_glFin (𝓞 F) F).comp continuous_subtype_val)

/-- A `K_f`-smooth function remains `K_f`-smooth after multiplication by `hpow t` (the product
of two smooth vectors is smooth: the product stabilizer contains the intersection of the two
stabilizers, which is open). -/
private theorem isKfSmooth_mul_hpow (t : ℂ) {φ₀ : AdelicGL2 (𝓞 F) F → ℂ}
    (h : IsKfSmooth F φ₀) :
    IsKfSmooth F (fun g => φ₀ g * hpow t g) := by
  have h' : IsSmoothVector (finiteAdelicGL2Subgroup F) (RightTranslationFn.mk φ₀) := h
  have hh : IsSmoothVector (finiteAdelicGL2Subgroup F) (RightTranslationFn.mk (hpow t)) :=
    isKfSmooth_hpow t
  show IsSmoothVector (finiteAdelicGL2Subgroup F)
    (RightTranslationFn.mk (fun g => φ₀ g * hpow t g))
  rw [isSmoothVector_iff_isOpen_stabilizer] at h' hh ⊢
  refine Subgroup.isOpen_mono (H₁ := MulAction.stabilizer (finiteAdelicGL2Subgroup F)
      (RightTranslationFn.mk φ₀) ⊓ MulAction.stabilizer (finiteAdelicGL2Subgroup F)
        (RightTranslationFn.mk (hpow t))) ?_ (h'.inter hh)
  intro u hu
  have hu1 : u ∈ MulAction.stabilizer (finiteAdelicGL2Subgroup F) (RightTranslationFn.mk φ₀) :=
    hu.1
  have hu2 : u ∈ MulAction.stabilizer (finiteAdelicGL2Subgroup F)
      (RightTranslationFn.mk (hpow t)) := hu.2
  rw [MulAction.mem_stabilizer_iff] at hu1 hu2 ⊢
  refine RightTranslationFn.ext fun x => ?_
  rw [Subgroup.smul_def]
  have h1 := congrArg RightTranslationFn.toFun hu1
  have h2 := congrArg RightTranslationFn.toFun hu2
  rw [Subgroup.smul_def] at h1 h2
  have e1 : φ₀ (x * (u : AdelicGL2 (𝓞 F) F)) = φ₀ x := by
    simpa using congrFun h1 x
  have e2 : hpow t (x * (u : AdelicGL2 (𝓞 F) F)) = hpow t x := by
    simpa using congrFun h2 x
  show φ₀ (x * (u : AdelicGL2 (𝓞 F) F)) * hpow t (x * (u : AdelicGL2 (𝓞 F) F))
      = φ₀ x * hpow t x
  rw [e1, e2]

/-- Multiplication by `hpow t` preserves archimedean `K`-finiteness. -/
private theorem isArchKFinite_mul_hpow (t : ℂ) {φ₀ : AdelicGL2 (𝓞 F) F → ℂ}
    (h : IsArchKFinite F φ₀) : IsArchKFinite F (fun g => φ₀ g * hpow t g) := by
  intro w
  obtain ⟨S, hS⟩ := h w
  classical
  let m : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) :=
    { toFun := fun u => fun x => u x * hpow t x
      map_add' := by
        intro u v
        funext x
        simp only [Pi.add_apply, add_mul]
      map_smul' := by
        intro c u
        funext x
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc] }
  refine ⟨S.image m, fun k hk => ?_⟩
  have hkK : InK k := inK_of_mem_archRowIsometrySubgroup w hk
  have h2 : m (fun x => φ₀ (x * k)) ∈ Submodule.map m (Submodule.span ℂ (S : Set _)) :=
    Submodule.mem_map_of_mem (hS k hk)
  rw [Submodule.map_span] at h2
  have e : (fun x => (fun g => φ₀ g * hpow t g) (x * k)) = m (fun x => φ₀ (x * k)) := by
    funext x
    show φ₀ (x * k) * hpow t (x * k) = φ₀ (x * k) * hpow t x
    rw [hpow_mul_inK t x hkK]
  rw [e, Finset.coe_image]
  exact h2

private theorem continuous_mul_hpow {φ₀ : AdelicGL2 (𝓞 F) F → ℂ} (hc : Continuous φ₀) (s₀ : ℂ) :
    Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ₀ p.2 * hpow (p.1 - s₀) p.2) := by
  refine (hc.comp continuous_snd).mul ?_
  unfold hpow
  refine Continuous.cpow ?_ (continuous_fst.sub continuous_const) ?_
  · exact Complex.continuous_ofReal.comp ((continuous_adelicHeight F).comp continuous_snd)
  · intro p
    exact Complex.ofReal_mem_slitPlane.mpr (adelicHeight_pos p.2)

private theorem differentiable_mul_hpow (φ₀ : AdelicGL2 (𝓞 F) F → ℂ) (s₀ : ℂ)
    (g : AdelicGL2 (𝓞 F) F) : Differentiable ℂ (fun s => φ₀ g * hpow (s - s₀) g) := by
  unfold hpow
  have h0 : ((adelicHeight F g : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (adelicHeight_pos g).ne'
  exact ((differentiable_id.sub_const s₀).const_cpow (Or.inl h0)).const_mul _

/-- The pin's `alphaF`: the modulus character of the adèle ring read into `ℝˣ`. -/
private def alphaF (F : Type) [Field F] [NumberField F] : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
  ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
    (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits

private theorem split_fst (hα : ∀ x, 0 < ((alphaF F x : ℝˣ) : ℝ)) (s₀ s : ℂ)
    (x : (AdeleRing (𝓞 F) F)ˣ) :
    (((alphaF F x : ℝˣ) : ℝ) : ℂ) ^ (s + 1 / 2)
      = (((alphaF F x : ℝˣ) : ℝ) : ℂ) ^ (s₀ + 1 / 2)
        * (((alphaF F x : ℝˣ) : ℝ) : ℂ) ^ (s - s₀) := by
  rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (hα x).ne')]
  congr 1
  ring

private theorem split_snd (hα : ∀ x, 0 < ((alphaF F x : ℝˣ) : ℝ)) (s₀ s : ℂ)
    (x : (AdeleRing (𝓞 F) F)ˣ) :
    (((alphaF F x : ℝˣ) : ℝ) : ℂ) ^ (-(s + 1 / 2))
      = (((alphaF F x : ℝˣ) : ℝ) : ℂ) ^ (-(s₀ + 1 / 2))
        * (((alphaF F x : ℝˣ) : ℝ) : ℂ) ^ (-(s - s₀)) := by
  rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (hα x).ne')]
  congr 1
  ring

/-- The shifted section stays induced: the `etaFst`/`etaSnd` characters at `s` factor through
those at `s₀` times the increment `s - s₀`. -/
private theorem isInducedSection_mul_hpow (hα : ∀ x, 0 < ((alphaF F x : ℝˣ) : ℝ))
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (s₀ s : ℂ) {φ₀ : AdelicGL2 (𝓞 F) F → ℂ}
    (h₀ : IsInducedSection (𝓞 F) F (etaFst μ (alphaF F) hα s₀) (etaSnd ν (alphaF F) hα s₀) φ₀) :
    IsInducedSection (𝓞 F) F (etaFst μ (alphaF F) hα s) (etaSnd ν (alphaF F) hα s)
      (fun g => φ₀ g * hpow (s - s₀) g) := by
  intro b hb g
  have hH : ((adelicHeight F (b * g) : ℝ) : ℂ) ^ (s - s₀ - 1 / 2 + 1 / 2)
      = ((etaFst 1 (alphaF F) hα (s - s₀ - 1 / 2) (borelDiagFst ⟨b, hb⟩) : ℂˣ) : ℂ)
        * ((etaSnd 1 (alphaF F) hα (s - s₀ - 1 / 2) (borelDiagSnd ⟨b, hb⟩) : ℂˣ) : ℂ)
        * ((adelicHeight F g : ℝ) : ℂ) ^ (s - s₀ - 1 / 2 + 1 / 2) :=
    (isInducedSection_adelicHeight_cpow F).2.2 hα (s - s₀ - 1 / 2) b hb g
  have he : s - s₀ - 1 / 2 + 1 / 2 = s - s₀ := by ring
  simp only [etaFst_apply, etaSnd_apply, cpowChar_apply_val, MonoidHom.one_apply, one_mul, he] at hH
  have h₀' := h₀ b hb g
  simp only [etaFst_apply, etaSnd_apply, Units.val_mul, cpowChar_apply_val] at h₀'
  simp only [hpow, etaFst_apply, etaSnd_apply, Units.val_mul, cpowChar_apply_val]
  rw [hH, h₀', split_fst hα s₀ s, split_snd hα s₀ s]
  ring

end FlatSectionFamily

/-- A family of sections is (the restriction of) a family of induced sections: from one
archimedean-`K`-finite, `K_f`-smooth, continuous induced section at `s₀`, the shifts by
`hpow (s - s₀)` give a family with the same induced-section law, archimedean `K`-finiteness,
`K_f`-smoothness, joint continuity, holomorphy in `s`, and constancy on the `K`-translates. -/
theorem exists_flat_isInducedSection_family_eq_of_isInducedSection
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (s₀ : ℂ) (φ₀ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ₀ : IsInducedSection (𝓞 F) F (etaFst μ α hα s₀) (etaSnd ν α hα s₀) φ₀)
      (_hφ₀K : IsArchKFinite F φ₀)
      (_hφ₀f : IsKfSmooth F φ₀)
      (_hφ₀c : Continuous φ₀),
    ∃ ψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ,
      ψ s₀ = φ₀
      ∧ (∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (ψ s))
      ∧ (∀ s, IsArchKFinite F (ψ s))
      ∧ (∀ s, IsKfSmooth F (ψ s))
      ∧ Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψ p.1 p.2)
      ∧ (∀ g, Differentiable ℂ (fun s => ψ s g))
      ∧ ∀ (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
          glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
          ψ s k = ψ s' k := by
  intro α hα μ ν s₀ φ₀ hφ₀ hφ₀K hφ₀f hφ₀c
  refine ⟨fun s g => φ₀ g * FlatSectionFamily.hpow (s - s₀) g, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext g
    show φ₀ g * FlatSectionFamily.hpow (s₀ - s₀) g = φ₀ g
    rw [sub_self, FlatSectionFamily.hpow_zero, mul_one]
  · intro s
    exact FlatSectionFamily.isInducedSection_mul_hpow (F := F) hα μ ν s₀ s hφ₀
  · intro s
    exact FlatSectionFamily.isArchKFinite_mul_hpow (s - s₀) hφ₀K
  · intro s
    exact FlatSectionFamily.isKfSmooth_mul_hpow (s - s₀) hφ₀f
  · exact FlatSectionFamily.continuous_mul_hpow hφ₀c s₀
  · intro g
    exact FlatSectionFamily.differentiable_mul_hpow φ₀ s₀ g
  · intro s s' k hk1 hk2
    show φ₀ k * FlatSectionFamily.hpow (s - s₀) k
      = φ₀ k * FlatSectionFamily.hpow (s' - s₀) k
    rw [FlatSectionFamily.hpow_of_inK _ ⟨hk1, hk2⟩,
      FlatSectionFamily.hpow_of_inK _ ⟨hk1, hk2⟩]

namespace FlatEisensteinHeight

section Local

variable {K : Type*} [NormedField K]

def frobSq (M : Matrix (Fin 2) (Fin 2) K) : ℝ := topNormSq M + rowNormSq M

theorem frobSq_nonneg (M : Matrix (Fin 2) (Fin 2) K) : 0 ≤ frobSq M := by
  unfold frobSq topNormSq rowNormSq; positivity

def distort (g : GL (Fin 2) K) : ℝ := frobSq (g : Matrix (Fin 2) (Fin 2) K) / ‖(g : Matrix (Fin 2) (Fin 2) K).det‖

theorem det_norm_pos (g : GL (Fin 2) K) : 0 < ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ :=
  norm_pos_iff.mpr (Matrix.isUnits_det_units g).ne_zero

theorem distort_nonneg (g : GL (Fin 2) K) : 0 ≤ distort g :=
  div_nonneg (frobSq_nonneg _) (norm_nonneg _)

theorem cramer10 (A B : Matrix (Fin 2) (Fin 2) K) :
    B.det * A 1 0 = (A * B) 1 0 * B 1 1 - (A * B) 1 1 * B 1 0 := by
  simp only [Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; ring

theorem cramer11 (A B : Matrix (Fin 2) (Fin 2) K) :
    B.det * A 1 1 = (A * B) 1 1 * B 0 0 - (A * B) 1 0 * B 0 1 := by
  simp only [Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; ring

theorem norm_sub_mul_sq_le (a b c d : K) :
    ‖a * b - c * d‖ ^ 2 ≤ (‖a‖ ^ 2 + ‖c‖ ^ 2) * (‖b‖ ^ 2 + ‖d‖ ^ 2) := by
  have h1 : ‖a * b - c * d‖ ≤ ‖a‖ * ‖b‖ + ‖c‖ * ‖d‖ := by
    calc ‖a * b - c * d‖ ≤ ‖a * b‖ + ‖c * d‖ := norm_sub_le _ _
      _ = ‖a‖ * ‖b‖ + ‖c‖ * ‖d‖ := by rw [norm_mul, norm_mul]
  have h2 : ‖a * b - c * d‖ ^ 2 ≤ (‖a‖ * ‖b‖ + ‖c‖ * ‖d‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [sq_nonneg (‖a‖ * ‖d‖ - ‖c‖ * ‖b‖), norm_nonneg a, norm_nonneg b, norm_nonneg c, norm_nonneg d]

theorem det_sq_mul_rowNormSq_le (A B : Matrix (Fin 2) (Fin 2) K) :
    ‖B.det‖ ^ 2 * rowNormSq A ≤ rowNormSq (A * B) * frobSq B := by
  unfold rowNormSq frobSq topNormSq rowNormSq
  have e0 : ‖B.det‖ ^ 2 * ‖A 1 0‖ ^ 2 = ‖(A * B) 1 0 * B 1 1 - (A * B) 1 1 * B 1 0‖ ^ 2 := by
    rw [← cramer10, norm_mul, mul_pow]
  have e1 : ‖B.det‖ ^ 2 * ‖A 1 1‖ ^ 2 = ‖(A * B) 1 1 * B 0 0 - (A * B) 1 0 * B 0 1‖ ^ 2 := by
    rw [← cramer11, norm_mul, mul_pow]
  have i0 := norm_sub_mul_sq_le ((A * B) 1 0) (B 1 1) ((A * B) 1 1) (B 1 0)
  have i1 := norm_sub_mul_sq_le ((A * B) 1 1) (B 0 0) ((A * B) 1 0) (B 0 1)
  nlinarith [i0, i1, e0, e1, sq_nonneg ‖(A*B) 1 0‖, sq_nonneg ‖(A*B) 1 1‖, sq_nonneg ‖B 0 0‖,
    sq_nonneg ‖B 0 1‖, sq_nonneg ‖B 1 0‖, sq_nonneg ‖B 1 1‖]

theorem localHeight_mul_le (A B : GL (Fin 2) K) :
    localHeight (A * B) ≤ localHeight A * distort B := by
  have hrAB := rowNormSq_pos (A * B)
  have hrA := rowNormSq_pos A
  have hdB := det_norm_pos B
  have hdA : 0 ≤ ‖(A : Matrix (Fin 2) (Fin 2) K).det‖ := norm_nonneg _
  have key := det_sq_mul_rowNormSq_le (A : Matrix (Fin 2) (Fin 2) K) (B : Matrix (Fin 2) (Fin 2) K)
  have hdet : ‖((A * B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖
      = ‖(A : Matrix (Fin 2) (Fin 2) K).det‖ * ‖(B : Matrix (Fin 2) (Fin 2) K).det‖ := by
    rw [gl_coe_mul, Matrix.det_mul, norm_mul]
  rw [← gl_coe_mul] at key
  unfold localHeight distort
  rw [hdet, div_mul_div_comm, div_le_div_iff₀ hrAB (mul_pos hrA hdB)]
  calc ‖(A : Matrix (Fin 2) (Fin 2) K).det‖ * ‖(B : Matrix (Fin 2) (Fin 2) K).det‖
        * (rowNormSq (A : Matrix (Fin 2) (Fin 2) K) * ‖(B : Matrix (Fin 2) (Fin 2) K).det‖)
      = ‖(A : Matrix (Fin 2) (Fin 2) K).det‖ * (‖(B : Matrix (Fin 2) (Fin 2) K).det‖ ^ 2
          * rowNormSq (A : Matrix (Fin 2) (Fin 2) K)) := by ring
    _ ≤ ‖(A : Matrix (Fin 2) (Fin 2) K).det‖ * (rowNormSq ((A * B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
          * frobSq (B : Matrix (Fin 2) (Fin 2) K)) := mul_le_mul_of_nonneg_left key hdA
    _ = ‖(A : Matrix (Fin 2) (Fin 2) K).det‖ * frobSq (B : Matrix (Fin 2) (Fin 2) K)
          * rowNormSq ((A * B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by ring

theorem distort_le_mul_localHeight {c u : ℝ} (hc : 0 < c) (g : GL (Fin 2) K)
    (hH : c ≤ localHeight g) (hx : xWindowSq g ≤ u ^ 2) :
    distort g ≤ (1 + (u ^ 2 + 1) / c ^ 2) * localHeight g := by
  have hr := rowNormSq_pos g
  have hd := det_norm_pos g
  set r := rowNormSq (g : Matrix (Fin 2) (Fin 2) K) with hr_def
  set tp := topNormSq (g : Matrix (Fin 2) (Fin 2) K) with htp_def
  set d := ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ with hd_def
  have hHdef : localHeight g = d / r := rfl
  have hxdef : xWindowSq g = tp / r - (d / r) ^ 2 := rfl
  have hDdef : distort g = (tp + r) / d := rfl
  set H := localHeight g with hH_def
  have hHpos : 0 < H := localHeight_pos g

  have hX : xWindowSq g + H ^ 2 = tp / r := by rw [hxdef, hHdef]; ring
  have hD : distort g = (xWindowSq g + H ^ 2 + 1) / H := by
    rw [hX, hDdef, hHdef, div_add_one hr.ne', div_div_div_cancel_right₀ hr.ne']
  rw [hD, div_le_iff₀ hHpos]
  have hc2 : 0 < c ^ 2 := by positivity
  have hHc : c ^ 2 ≤ H ^ 2 := pow_le_pow_left₀ hc.le hH 2
  have hu : 0 ≤ u ^ 2 + 1 := by positivity

  have h1 : (u ^ 2 + 1) ≤ (u ^ 2 + 1) / c ^ 2 * H * H := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hc2]
    nlinarith
  nlinarith [hx, h1]

end Local

section UltraBase

variable {K : Type*} [NormedField K]

def maxEntry (M : Matrix (Fin 2) (Fin 2) K) : ℝ := max (max ‖M 0 0‖ ‖M 0 1‖) (max ‖M 1 0‖ ‖M 1 1‖)

theorem maxEntry_nonneg (M : Matrix (Fin 2) (Fin 2) K) : 0 ≤ maxEntry M :=
  (norm_nonneg _).trans ((le_max_left _ _).trans (le_max_left _ _))

theorem le_maxEntry (M : Matrix (Fin 2) (Fin 2) K) (i j : Fin 2) : ‖M i j‖ ≤ maxEntry M := by
  unfold maxEntry
  fin_cases i <;> fin_cases j <;> simp

def fdistort (g : GL (Fin 2) K) : ℝ := maxEntry (g : Matrix (Fin 2) (Fin 2) K) ^ 2 / ‖(g : Matrix (Fin 2) (Fin 2) K).det‖

theorem fdistort_nonneg (g : GL (Fin 2) K) : 0 ≤ fdistort g := div_nonneg (sq_nonneg _) (norm_nonneg _)

end UltraBase

section Ultra

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem det_mul_rowMaxNorm_le (A B : Matrix (Fin 2) (Fin 2) K) :
    ‖B.det‖ * rowMaxNorm A ≤ rowMaxNorm (A * B) * maxEntry B := by
  unfold rowMaxNorm
  have hM := maxEntry_nonneg B
  have hR : 0 ≤ max ‖(A * B) 1 0‖ ‖(A * B) 1 1‖ := (norm_nonneg _).trans (le_max_left _ _)
  have b00 := le_maxEntry B 0 0; have b01 := le_maxEntry B 0 1
  have b10 := le_maxEntry B 1 0; have b11 := le_maxEntry B 1 1
  have e0 : ‖B.det‖ * ‖A 1 0‖ ≤ max ‖(A * B) 1 0‖ ‖(A * B) 1 1‖ * maxEntry B := by
    rw [← norm_mul, cramer10, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]; exact mul_le_mul (le_max_left _ _) b11 (norm_nonneg _) hR
    · rw [norm_neg, norm_mul]; exact mul_le_mul (le_max_right _ _) b10 (norm_nonneg _) hR
  have e1 : ‖B.det‖ * ‖A 1 1‖ ≤ max ‖(A * B) 1 0‖ ‖(A * B) 1 1‖ * maxEntry B := by
    rw [← norm_mul, cramer11, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]; exact mul_le_mul (le_max_right _ _) b00 (norm_nonneg _) hR
    · rw [norm_neg, norm_mul]; exact mul_le_mul (le_max_left _ _) b01 (norm_nonneg _) hR
  rcases le_total ‖A 1 0‖ ‖A 1 1‖ with h | h
  · rw [max_eq_right h]; exact e1
  · rw [max_eq_left h]; exact e0

theorem finLocalHeight_mul_le (A B : GL (Fin 2) K) :
    finLocalHeight (A * B) ≤ finLocalHeight A * fdistort B := by
  have hrAB := rowMaxNorm_pos (A * B)
  have hrA := rowMaxNorm_pos A
  have hdB : 0 < ‖(B : Matrix (Fin 2) (Fin 2) K).det‖ := norm_pos_iff.mpr (Matrix.isUnits_det_units B).ne_zero
  have hdA : 0 ≤ ‖(A : Matrix (Fin 2) (Fin 2) K).det‖ := norm_nonneg _
  have key := det_mul_rowMaxNorm_le (A : Matrix (Fin 2) (Fin 2) K) (B : Matrix (Fin 2) (Fin 2) K)
  have key2 : ‖(B : Matrix (Fin 2) (Fin 2) K).det‖ ^ 2 * rowMaxNorm (A : Matrix (Fin 2) (Fin 2) K) ^ 2
      ≤ rowMaxNorm ((A * B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ^ 2 * maxEntry (B : Matrix (Fin 2) (Fin 2) K) ^ 2 := by
    rw [← mul_pow, ← mul_pow, gl_coe_mul]
    exact pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (rowMaxNorm_nonneg _)) key 2
  have hdet : ‖((A * B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖
      = ‖(A : Matrix (Fin 2) (Fin 2) K).det‖ * ‖(B : Matrix (Fin 2) (Fin 2) K).det‖ := by
    rw [gl_coe_mul, Matrix.det_mul, norm_mul]
  unfold finLocalHeight fdistort
  rw [hdet, div_mul_div_comm, div_le_div_iff₀ (pow_pos hrAB 2) (mul_pos (pow_pos hrA 2) hdB)]
  calc ‖(A : Matrix (Fin 2) (Fin 2) K).det‖ * ‖(B : Matrix (Fin 2) (Fin 2) K).det‖
        * (rowMaxNorm (A : Matrix (Fin 2) (Fin 2) K) ^ 2 * ‖(B : Matrix (Fin 2) (Fin 2) K).det‖)
      = ‖(A : Matrix (Fin 2) (Fin 2) K).det‖ * (‖(B : Matrix (Fin 2) (Fin 2) K).det‖ ^ 2
          * rowMaxNorm (A : Matrix (Fin 2) (Fin 2) K) ^ 2) := by ring
    _ ≤ ‖(A : Matrix (Fin 2) (Fin 2) K).det‖ * (rowMaxNorm ((A * B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ^ 2
          * maxEntry (B : Matrix (Fin 2) (Fin 2) K) ^ 2) := mul_le_mul_of_nonneg_left key2 hdA
    _ = ‖(A : Matrix (Fin 2) (Fin 2) K).det‖ * maxEntry (B : Matrix (Fin 2) (Fin 2) K) ^ 2
          * rowMaxNorm ((A * B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ^ 2 := by ring

theorem fdistort_eq_one (g : GL (Fin 2) K)
    (h : ∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1)
    (h' : ∀ i j, ‖((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1) : fdistort g = 1 := by
  have hd1 : ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ ≤ 1 := norm_det_le_one h
  have hdi : ‖((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖ ≤ 1 := norm_det_le_one h'
  have hprod : (g : Matrix (Fin 2) (Fin 2) K).det * ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [← Matrix.det_mul, ← gl_coe_mul, mul_inv_cancel]; simp
  have hd : ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ = 1 := by
    have hn : ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ * ‖((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖ = 1 := by
      rw [← norm_mul, hprod, norm_one]
    have hpos : 0 < ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ := norm_pos_iff.mpr (Matrix.isUnits_det_units g).ne_zero
    nlinarith [norm_nonneg (((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det)]
  have hM1 : maxEntry (g : Matrix (Fin 2) (Fin 2) K) ≤ 1 := by
    unfold maxEntry; exact max_le (max_le (h 0 0) (h 0 1)) (max_le (h 1 0) (h 1 1))

  have hM2 : 1 ≤ maxEntry (g : Matrix (Fin 2) (Fin 2) K) := by
    have hM := maxEntry_nonneg (g : Matrix (Fin 2) (Fin 2) K)
    have : ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ ≤ maxEntry (g : Matrix (Fin 2) (Fin 2) K) ^ 2 := by
      rw [Matrix.det_fin_two, sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [norm_mul, sq]; exact mul_le_mul (le_maxEntry _ 0 0) (le_maxEntry _ 1 1) (norm_nonneg _) hM
      · rw [norm_neg, norm_mul, sq]; exact mul_le_mul (le_maxEntry _ 0 1) (le_maxEntry _ 1 0) (norm_nonneg _) hM
    rw [hd] at this
    nlinarith
  have hM : maxEntry (g : Matrix (Fin 2) (Fin 2) K) = 1 := le_antisymm hM1 hM2
  rw [fdistort, hM, hd]; norm_num

end Ultra

section Global

open IsDedekindDomain

variable (F : Type) [Field F] [NumberField F]

def archDistort (g : AdelicGL2 (𝓞 F) F) : ℝ :=
  ∏ w : InfinitePlace F, distort (archComponent F w (glArch (𝓞 F) F g)) ^ w.mult

def finDistort (g : AdelicGL2 (𝓞 F) F) : ℝ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 F), fdistort (finComponent (𝓞 F) F v (glFin (𝓞 F) F g))

variable {F}

theorem archDistort_nonneg (g : AdelicGL2 (𝓞 F) F) : 0 ≤ archDistort F g :=
  Finset.prod_nonneg fun _ _ => pow_nonneg (distort_nonneg _) _

theorem fdistort_finComponent_eventually_eq_one (g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, fdistort (finComponent (𝓞 F) F v g) = 1 := by
  have hg : ∀ i j, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j v ∈ v.adicCompletionIntegers F :=
    fun i j => ((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j).2
  have hg' : ∀ i j, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j v ∈ v.adicCompletionIntegers F :=
    fun i j => (((g⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j).2
  have hall : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      (∀ i j, (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j v
        ∈ v.adicCompletionIntegers F)
      ∧ ∀ i j, ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j v ∈ v.adicCompletionIntegers F := by
    refine (Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr (hg i)).and
      (Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr (hg' i))
  filter_upwards [hall] with v hv
  refine fdistort_eq_one _ (fun i j => ?_) (fun i j => ?_)
  · rw [finComponent_apply]
    exact norm_le_one_of_mem_adicCompletionIntegers (hv.1 i j)
  · rw [← map_inv, finComponent_apply]
    exact norm_le_one_of_mem_adicCompletionIntegers (hv.2 i j)

theorem hasFiniteMulSupport_fdistort (g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    (fun v : HeightOneSpectrum (𝓞 F) => fdistort (finComponent (𝓞 F) F v g)).HasFiniteMulSupport :=
  Filter.eventually_cofinite.mp (fdistort_finComponent_eventually_eq_one g)

theorem finDistort_nonneg (g : AdelicGL2 (𝓞 F) F) : 0 ≤ finDistort F g :=
  finprod_induction (fun x : ℝ => 0 ≤ x) zero_le_one (fun _ _ => mul_nonneg) fun _ => fdistort_nonneg _

theorem finHeight_mul_le (h g : AdelicGL2 (𝓞 F) F) :
    finHeight F (glFin (𝓞 F) F (h * g)) ≤ finHeight F (glFin (𝓞 F) F h) * finDistort F g := by
  classical
  set a : HeightOneSpectrum (𝓞 F) → ℝ := fun v => finLocalHeight (finComponent (𝓞 F) F v (glFin (𝓞 F) F (h * g)))
  set b : HeightOneSpectrum (𝓞 F) → ℝ := fun v => finLocalHeight (finComponent (𝓞 F) F v (glFin (𝓞 F) F h))
  set d : HeightOneSpectrum (𝓞 F) → ℝ := fun v => fdistort (finComponent (𝓞 F) F v (glFin (𝓞 F) F g))
  have ha := hasFiniteMulSupport_finLocalHeight (glFin (𝓞 F) F (h * g))
  have hb := hasFiniteMulSupport_finLocalHeight (glFin (𝓞 F) F h)
  have hd := hasFiniteMulSupport_fdistort (glFin (𝓞 F) F g)
  set S : Finset (HeightOneSpectrum (𝓞 F)) := ha.toFinset ∪ hb.toFinset ∪ hd.toFinset with hS
  have hSa : Function.mulSupport a ⊆ S := by
    intro v hv
    have hv' : v ∈ (ha.toFinset : Set (HeightOneSpectrum (𝓞 F))) := by
      rw [Set.Finite.coe_toFinset (hs := ha)]
      exact hv
    rw [hS]
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hv')))
  have hSb : Function.mulSupport b ⊆ S := by
    intro v hv
    have hv' : v ∈ (hb.toFinset : Set (HeightOneSpectrum (𝓞 F))) := by
      rw [Set.Finite.coe_toFinset (hs := hb)]
      exact hv
    rw [hS]
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hv')))
  have hSd : Function.mulSupport d ⊆ S := by
    intro v hv
    have hv' : v ∈ (hd.toFinset : Set (HeightOneSpectrum (𝓞 F))) := by
      rw [Set.Finite.coe_toFinset (hs := hd)]
      exact hv
    rw [hS]
    exact Finset.mem_union.mpr (Or.inr hv')
  show ∏ᶠ v, a v ≤ (∏ᶠ v, b v) * ∏ᶠ v, d v
  rw [finprod_eq_prod_of_mulSupport_subset a hSa, finprod_eq_prod_of_mulSupport_subset b hSb,
    finprod_eq_prod_of_mulSupport_subset d hSd, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun v _ => (finLocalHeight_pos _).le) fun v _ => ?_
  show finLocalHeight (finComponent (𝓞 F) F v (glFin (𝓞 F) F (h * g)))
    ≤ finLocalHeight (finComponent (𝓞 F) F v (glFin (𝓞 F) F h)) * fdistort (finComponent (𝓞 F) F v (glFin (𝓞 F) F g))
  rw [map_mul, map_mul]
  exact finLocalHeight_mul_le _ _

theorem archHeight_mul_le (h g : AdelicGL2 (𝓞 F) F) :
    archHeight F (glArch (𝓞 F) F (h * g)) ≤ archHeight F (glArch (𝓞 F) F h) * archDistort F g := by
  unfold archHeight archDistort
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun w _ => pow_nonneg (localHeight_pos _).le _) fun w _ => ?_
  rw [← mul_pow, map_mul, map_mul]
  exact pow_le_pow_left₀ (localHeight_pos _).le (localHeight_mul_le _ _) _

theorem adelicHeight_mul_le (h g : AdelicGL2 (𝓞 F) F) :
    adelicHeight F (h * g) ≤ adelicHeight F h * (archDistort F g * finDistort F g) := by
  unfold adelicHeight
  calc archHeight F (glArch (𝓞 F) F (h * g)) * finHeight F (glFin (𝓞 F) F (h * g))
      ≤ (archHeight F (glArch (𝓞 F) F h) * archDistort F g) * (finHeight F (glFin (𝓞 F) F h) * finDistort F g) :=
        mul_le_mul (archHeight_mul_le h g) (finHeight_mul_le h g) (finHeight_pos _).le
          (mul_nonneg (archHeight_pos F _).le (archDistort_nonneg _))
    _ = _ := by ring

theorem finDistort_eq_one_of_mem {s : AdelicGL2 (𝓞 F) F} (hs : glFin (𝓞 F) F s ∈ finiteIntegralGL2 (𝓞 F) F) :
    finDistort F s = 1 := by
  rw [mem_finiteIntegralGL2_iff] at hs
  refine finprod_eq_one_of_forall_eq_one fun v => fdistort_eq_one _ (fun i j => ?_) (fun i j => ?_)
  · rw [finComponent_apply]
    exact norm_le_one_of_mem_adicCompletionIntegers (hs.1 i j v)
  · rw [← map_inv, finComponent_apply]
    exact norm_le_one_of_mem_adicCompletionIntegers (hs.2 i j v)

theorem archDistort_le_of_mem {c u d₁ d₂ : ℝ} (hc : 0 < c) {s : AdelicGL2 (𝓞 F) F}
    (hs : s ∈ centreCutSiegelSet F c u d₁ d₂) :
    archDistort F s ≤ (1 + (u ^ 2 + 1) / c ^ 2) ^ (∑ w : InfinitePlace F, w.mult) * archHeight F (glArch (𝓞 F) F s) := by
  obtain ⟨-, hfloor, hwin, -⟩ := mem_centreCutSiegelSet_iff.mp hs
  unfold archDistort archHeight
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun w _ => pow_nonneg (distort_nonneg _) _) fun w _ => ?_
  rw [← mul_pow]
  exact pow_le_pow_left₀ (distort_nonneg _) (distort_le_mul_localHeight hc _ (hfloor w) (hwin w)) _

end Global

end FlatEisensteinHeight

open FlatEisensteinHeight

theorem exists_flatEisenstein_mul_le_mul_archHeight_rpow_of_mem_centreCutSiegelSet
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (hc : 0 < c) (t : AdelicGL2 (𝓞 F) F)
    (σ : ℝ) (hσ : 1 / 2 < σ) :
    letI := adeleBorel (𝓞 F) F
    ∃ C : ℝ, ∀ s ∈ centreCutSiegelSet F c u d₁ d₂,
      Summable (fun ξ : F => adelicHeight F (adelicWeyl (𝓞 F) F
          * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * (s * t)) ^ (σ + 1 / 2)) ∧
      adelicHeight F (s * t) ^ (σ + 1 / 2)
          + ∑' ξ : F, adelicHeight F (adelicWeyl (𝓞 F) F
              * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * (s * t)) ^ (σ + 1 / 2)
        ≤ C * archHeight F (glArch (𝓞 F) F s) ^ (σ + 1 / 2) := by
  set p : ℝ := σ + 1 / 2 with hp
  have hp0 : 0 ≤ p := by rw [hp]; linarith

  obtain ⟨hα, hunit, hsec⟩ := AutomorphicForm.isInducedSection_adelicHeight_cpow F
  set φ : AdelicGL2 (𝓞 F) F → ℂ := fun g => ((adelicHeight F g : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2) with hφ
  have hφc : Continuous φ :=
    (Complex.continuous_ofReal.comp (NumberField.AdelicHeight.continuous_adelicHeight F)).cpow
      continuous_const fun g => Complex.ofReal_mem_slitPlane.mpr (adelicHeight_pos g)
  have hre : (1 : ℝ) / 2 < ((σ : ℂ) + 1 / 2).re - 1 / 2 + 1 / 2 := by simp; linarith
  have hsum0 := AutomorphicForm.bruhatTransversal_summand_norm_summable_of_re_gt_half F hα 1 1 hunit hunit
    (σ : ℂ) (by simpa using hσ) φ (hsec hα σ) hφc 1
  set base : F → ℝ := fun ξ => adelicHeight F (adelicWeyl (𝓞 F) F
      * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ)) ^ p with hbase
  have hnorm : ∀ g : AdelicGL2 (𝓞 F) F, ‖φ g‖ = adelicHeight F g ^ p := by
    intro g
    rw [hφ]; dsimp only
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (adelicHeight_pos g)]
    congr 1; simp [hp]
  have hsum : Summable base := by
    refine (hsum0.congr fun ξ => ?_)
    rw [mul_one, hnorm]
  set S₁ : ℝ := ∑' ξ : F, base ξ with hS₁
  have hbase0 : ∀ ξ, 0 ≤ base ξ := fun ξ => Real.rpow_nonneg (adelicHeight_pos _).le _
  have hS₁0 : 0 ≤ S₁ := tsum_nonneg hbase0

  set n : ℕ := ∑ w : InfinitePlace F, w.mult with hn
  set C₁ : ℝ := (1 + (u ^ 2 + 1) / c ^ 2) ^ n with hC₁
  set Dt : ℝ := archDistort F t * finDistort F t with hDt
  have hDt0 : 0 ≤ Dt := mul_nonneg (archDistort_nonneg _) (finDistort_nonneg _)
  refine ⟨(1 + S₁) * (C₁ * Dt) ^ p, fun s hs => ?_⟩
  have hsK : glFin (𝓞 F) F s ∈ finiteIntegralGL2 (𝓞 F) F := (mem_centreCutSiegelSet_iff.mp hs).1

  set Ds : ℝ := archDistort F s * finDistort F s with hDs
  have hDs0 : 0 ≤ Ds := mul_nonneg (archDistort_nonneg _) (finDistort_nonneg _)
  have hDs : Ds ≤ C₁ * archHeight F (glArch (𝓞 F) F s) := by
    rw [hDs, finDistort_eq_one_of_mem hsK, mul_one]
    exact archDistort_le_of_mem hc hs
  have hH0 : 0 ≤ archHeight F (glArch (𝓞 F) F s) := (archHeight_pos F _).le

  have hdom : ∀ h : AdelicGL2 (𝓞 F) F, adelicHeight F (h * (s * t)) ≤ adelicHeight F h * (Ds * Dt) := by
    intro h
    calc adelicHeight F (h * (s * t)) = adelicHeight F (h * s * t) := by rw [mul_assoc]
      _ ≤ adelicHeight F (h * s) * Dt := adelicHeight_mul_le _ _
      _ ≤ adelicHeight F h * Ds * Dt := mul_le_mul_of_nonneg_right (adelicHeight_mul_le _ _) hDt0
      _ = _ := by ring
  have hdomp : ∀ h : AdelicGL2 (𝓞 F) F,
      adelicHeight F (h * (s * t)) ^ p ≤ adelicHeight F h ^ p * (Ds * Dt) ^ p := by
    intro h
    rw [← Real.mul_rpow (adelicHeight_pos h).le (mul_nonneg hDs0 hDt0)]
    exact Real.rpow_le_rpow (adelicHeight_pos _).le (hdom h) hp0
  have hterm : ∀ ξ : F, adelicHeight F (adelicWeyl (𝓞 F) F
        * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * (s * t)) ^ p ≤ base ξ * (Ds * Dt) ^ p :=
    fun ξ => hdomp _
  have hsum_st : Summable (fun ξ : F => adelicHeight F (adelicWeyl (𝓞 F) F
        * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * (s * t)) ^ p) :=
    Summable.of_nonneg_of_le (fun ξ => Real.rpow_nonneg (adelicHeight_pos _).le _) hterm (hsum.mul_right _)
  refine ⟨hsum_st, ?_⟩

  have h1 : adelicHeight F (s * t) ^ p ≤ (Ds * Dt) ^ p := by
    have := hdomp 1
    rwa [one_mul, show adelicHeight F 1 = 1 by
      rw [adelicHeight, map_one, map_one, archHeight_one]
      simp [finHeight, map_one, finLocalHeight, rowMaxNorm], Real.one_rpow, one_mul] at this
  have h2 : ∑' ξ : F, adelicHeight F (adelicWeyl (𝓞 F) F
        * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * (s * t)) ^ p ≤ S₁ * (Ds * Dt) ^ p := by
    rw [hS₁, ← tsum_mul_right]
    exact hsum_st.tsum_le_tsum hterm (hsum.mul_right _)
  have hDD : (Ds * Dt) ^ p ≤ (C₁ * Dt) ^ p * archHeight F (glArch (𝓞 F) F s) ^ p := by
    rw [← Real.mul_rpow (mul_nonneg (by positivity) hDt0) hH0]
    refine Real.rpow_le_rpow (mul_nonneg hDs0 hDt0) ?_ hp0
    calc Ds * Dt ≤ (C₁ * archHeight F (glArch (𝓞 F) F s)) * Dt := mul_le_mul_of_nonneg_right hDs hDt0
      _ = C₁ * Dt * archHeight F (glArch (𝓞 F) F s) := by ring
  have hCD0 : 0 ≤ (C₁ * Dt) ^ p * archHeight F (glArch (𝓞 F) F s) ^ p :=
    mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hH0 _)
  calc adelicHeight F (s * t) ^ p + ∑' ξ : F, adelicHeight F (adelicWeyl (𝓞 F) F
          * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * (s * t)) ^ p
      ≤ (Ds * Dt) ^ p + S₁ * (Ds * Dt) ^ p := add_le_add h1 h2
    _ = (1 + S₁) * (Ds * Dt) ^ p := by ring
    _ ≤ (1 + S₁) * ((C₁ * Dt) ^ p * archHeight F (glArch (𝓞 F) F s) ^ p) :=
        mul_le_mul_of_nonneg_left hDD (by linarith)
    _ = (1 + S₁) * (C₁ * Dt) ^ p * archHeight F (glArch (𝓞 F) F s) ^ p := by ring


namespace BruhatConstantTerm

open WeylIntegrable Filter Topology
open scoped ENNReal

section Unfold

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "ι" => algebraMap F (AdeleRing (𝓞 F) F)

attribute [local instance] NumberField.AdelicHaar.adeleBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar
  NumberField.AdelicHaar.countable_principalSubgroup

scoped instance instNontrivialAdeleRing : Nontrivial 𝔸 := by
  have : Inhabited (InfinitePlace F) := Classical.inhabited_of_nonempty inferInstance
  have : Nontrivial (InfiniteAdeleRing F) :=
    inferInstanceAs (Nontrivial ((w : InfinitePlace F) → w.Completion))
  exact inferInstanceAs (Nontrivial (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

def principalEquiv : F ≃ AdeleRing.principalSubgroup (𝓞 F) F :=
  Equiv.ofBijective (fun k => ⟨ι k, k, rfl⟩)
    ⟨fun a b h => (algebraMap F 𝔸).injective (congrArg Subtype.val h), by rintro ⟨_, k, rfl⟩; exact ⟨k, rfl⟩⟩

variable (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]

theorem tsum_lintegral_adelicBox_comp_add (f : 𝔸 → ℝ≥0∞) :
    ∑' ξ : F, ∫⁻ t in adelicBox F, f (t + ι ξ) ∂μ = ∫⁻ t, f t ∂μ := by
  have hFD := isAddFundamentalDomain_adelicBox F μ
  rw [hFD.lintegral_eq_tsum'' f, ← (principalEquiv F).tsum_eq]
  refine tsum_congr fun ξ => lintegral_congr fun t => ?_
  show f (t + ι ξ) = f (ι ξ + t)
  rw [add_comm]

theorem tsum_integral_adelicBox_comp_add {Φ : 𝔸 → ℂ} (hΦ : Integrable Φ μ) :
    ∑' ξ : F, ∫ t in adelicBox F, Φ (t + ι ξ) ∂μ = ∫ t, Φ t ∂μ := by
  have hFD := isAddFundamentalDomain_adelicBox F μ
  rw [hFD.integral_eq_tsum'' Φ hΦ, ← (principalEquiv F).tsum_eq]
  refine tsum_congr fun ξ => integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show Φ (t + ι ξ) = Φ (ι ξ + t)
  rw [add_comm]

theorem integrableOn_and_setIntegral_tsum_translate {Φ : 𝔸 → ℂ} (hΦ : Integrable Φ μ) :
    IntegrableOn (fun t => ∑' ξ : F, Φ (t + ι ξ)) (adelicBox F) μ ∧
      ∫ t in adelicBox F, (∑' ξ : F, Φ (t + ι ξ)) ∂μ = ∫ t, Φ t ∂μ := by
  set ν : Measure 𝔸 := μ.restrict (adelicBox F) with hν
  have hT : ∀ ξ : F, Integrable (fun t => Φ (t + ι ξ)) μ := fun ξ => hΦ.comp_add_right (ι ξ)
  have hmeas : ∀ ξ : F, AEStronglyMeasurable (fun t => Φ (t + ι ξ)) ν := fun ξ =>
    (hT ξ).aestronglyMeasurable.restrict
  have hgmeas : AEMeasurable (fun t => ∑' ξ : F, ‖Φ (t + ι ξ)‖ₑ) ν := by
    simp_rw [ENNReal.tsum_eq_iSup_sum]
    exact AEMeasurable.iSup fun s => Finset.aemeasurable_fun_sum s fun ξ _ => (hmeas ξ).enorm
  have hsum : ∑' ξ : F, ∫⁻ t, ‖Φ (t + ι ξ)‖ₑ ∂ν = ∫⁻ t, ‖Φ t‖ₑ ∂μ := by
    rw [hν, tsum_lintegral_adelicBox_comp_add F μ (fun t => ‖Φ t‖ₑ)]
  have hglint : ∫⁻ t, (∑' ξ : F, ‖Φ (t + ι ξ)‖ₑ) ∂ν < ∞ := by
    rw [lintegral_tsum fun ξ => (hmeas ξ).enorm, hsum]
    exact hΦ.2
  have hgint : Integrable (fun t => ∑' ξ : F, ‖Φ (t + ι ξ)‖ₑ) ν :=
    ⟨hgmeas.aestronglyMeasurable, by
      rw [hasFiniteIntegral_iff_enorm]
      simpa only [enorm_eq_self] using hglint⟩
  have hae : ∀ᵐ t ∂ν, HasSum (fun ξ : F => Φ (t + ι ξ)) (∑' ξ : F, Φ (t + ι ξ)) := by
    filter_upwards [ae_lt_top' hgmeas hglint.ne] with t ht
    have hs : Summable fun ξ : F => (‖Φ (t + ι ξ)‖₊ : ℝ) := by
      rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
      simpa only [enorm_eq_nnnorm] using ht.ne
    exact (Summable.of_norm (by simpa only [coe_nnnorm] using hs)).hasSum
  have hPmeas : AEStronglyMeasurable (fun t => ∑' ξ : F, Φ (t + ι ξ)) ν :=
    aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset F))
      (f := fun s : Finset F => fun t => ∑ ξ ∈ s, Φ (t + ι ξ))
      (fun s => Finset.aestronglyMeasurable_fun_sum s fun ξ _ => hmeas ξ) hae
  refine ⟨hgint.mono'_enorm hPmeas (Filter.Eventually.of_forall fun t => enorm_tsum_le_tsum_enorm), ?_⟩

  have hfin : ∑' ξ : F, ∫⁻ t, ‖Φ (t + ι ξ)‖ₑ ∂ν ≠ ∞ := by
    rw [hsum]; exact hΦ.2.ne
  show ∫ t, (∑' ξ : F, Φ (t + ι ξ)) ∂ν = ∫ t, Φ t ∂μ
  rw [integral_tsum hmeas hfin, hν, tsum_integral_adelicBox_comp_add F μ hΦ]

end Unfold

section Core

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "ι" => algebraMap F (AdeleRing (𝓞 F) F)
local notation "G𝔸" => AdelicGL2 (𝓞 F) F

attribute [local instance] NumberField.AdelicHaar.adeleBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar
  NumberField.AdelicHaar.countable_principalSubgroup

theorem constantTerm_cond_adelicBox_eq (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] (φ : G𝔸 → ℂ)
    (hN : ∀ (x : 𝔸) (g : G𝔸), φ (unipotentGL2 x * g) = φ g) (w g : G𝔸)
    (hint : Integrable (fun u : 𝔸 => φ (w * unipotentGL2 u * g)) μ) :
    constantTerm (ProbabilityTheory.cond μ (adelicBox F)) unipotentGL2
        (fun g' => φ g' + ∑' ξ : F, φ (w * unipotentGL2 (ι ξ) * g')) g
      = φ g + ((μ (adelicBox F)).toReal : ℂ)⁻¹ * ∫ u, φ (w * unipotentGL2 u * g) ∂μ := by
  obtain ⟨hS, hunf⟩ := integrableOn_and_setIntegral_tsum_translate F μ hint

  have hE : (fun t : 𝔸 => φ (unipotentGL2 t * g) + ∑' ξ : F, φ (w * unipotentGL2 (ι ξ) * (unipotentGL2 t * g)))
      = fun t => φ g + ∑' ξ : F, φ (w * unipotentGL2 (t + ι ξ) * g) := by
    funext t
    rw [hN t g]
    congr 1
    refine tsum_congr fun ξ => ?_
    rw [add_comm t, unipotentGL2_add]
    simp only [mul_assoc]
  have hpos : 0 < μ (adelicBox F) := measure_adelicBox_pos F μ
  have hlt : μ (adelicBox F) < ∞ := measure_adelicBox_lt_top F μ
  have : IsFiniteMeasure (μ.restrict (adelicBox F)) := ⟨by rw [Measure.restrict_apply_univ]; exact hlt⟩
  have hm : ((μ (adelicBox F)).toReal : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ENNReal.toReal_ne_zero.mpr ⟨hpos.ne', hlt.ne⟩)
  show ∫ t, (φ (unipotentGL2 t * g) + ∑' ξ : F, φ (w * unipotentGL2 (ι ξ) * (unipotentGL2 t * g)))
      ∂(ProbabilityTheory.cond μ (adelicBox F)) = _
  rw [hE, ProbabilityTheory.cond, integral_smul_measure, integral_add (integrable_const _) hS, integral_const,
    measureReal_restrict_apply_univ, measureReal_def, hunf, ENNReal.toReal_inv]
  simp only [Complex.real_smul, Complex.ofReal_inv]
  rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hm, one_mul]

theorem constantTerm_bruhatEisenstein_core {χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (φ : G𝔸 → ℂ)
    (hφ : IsInducedSection (𝓞 F) F χ₁ χ₂ φ) (g : G𝔸)
    (hint : Integrable (fun u : 𝔸 => φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 u * g)) (adelicAddHaar (𝓞 F) F)) :
    constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) unipotentGL2
        (fun g' => φ g' + ∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (ι ξ) * g')) g
      = φ g + (((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
          weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g := by
  rw [WeylIntegrable.adelicWeyl_inv' F] at hint
  unfold weylIntertwiningIntegral
  rw [WeylIntegrable.adelicWeyl_inv' F]
  exact constantTerm_cond_adelicBox_eq F (adelicAddHaar (𝓞 F) F) φ (fun x g => isInducedSection_unipotent_mul hφ x g)
    (adelicWeyl (𝓞 F) F) g hint

end Core

section Row

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox
open scoped NNReal

theorem constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral_impl
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (s : ℂ) (_hs : 1 / 2 < s.re) (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφc : Continuous φ)
      (g : AdelicGL2 (𝓞 F) F),
    letI := adeleBorel (𝓞 F) F
    let E : AdelicGL2 (𝓞 F) F → ℂ := fun g' =>
      φ g' + ∑' ξ : F, φ (adelicWeyl (𝓞 F) F
        * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g')
    constantTerm
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F))
      unipotentGL2 E g
      = φ g
        + (((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹
          * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g := by
  intro α hα μ ν hμ hν s hs φ hφ hφc g
  exact constantTerm_bruhatEisenstein_core F φ hφ g
    (weylIntertwiningIntegrand_integrable_of_re_gt_half F hα μ ν hμ hν s hs φ hφ hφc g)

end Row
end BruhatConstantTerm

open BruhatConstantTerm

/-- The constant term of the flat Eisenstein series is the section plus the Weyl-intertwining
integral: `constantTerm (φ + ∑' ξ, φ (w n(ξ) ·)) g = φ g + (vol box)⁻¹ * W φ g`. -/
theorem constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (s : ℂ) (_hs : 1 / 2 < s.re) (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφc : Continuous φ)
      (g : AdelicGL2 (𝓞 F) F),
    letI := adeleBorel (𝓞 F) F
    let E : AdelicGL2 (𝓞 F) F → ℂ := fun g' =>
      φ g' + ∑' ξ : F, φ (adelicWeyl (𝓞 F) F
        * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g')
    constantTerm
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F))
      unipotentGL2 E g
      = φ g
        + (((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹
          * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g :=
  BruhatConstantTerm.constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral_impl F

end AutomorphicForm

end
