/-
  The Nebentypus exists.

  Every `Γ₁(N)` weight-one form is the lift of a form with a Nebentypus: reading the lift on the span
  of its right translates (`AdelicSpan`, `NumberLocalNewvector`'s carrier) produces a `Γ₁` cusp form
  whose Nebentypus character `ε` makes the lift equal to the nebentypus-twisted lift of the form.

  Transcribed from
  `P2M/Sol/S_DihedralWeightOne_exists_hasNebentypus_eq_weightOneLift_of_mem_span_of_apply_mul_finEmbed_eq_inv_mul.lean`
  (853 lines / 72 declarations). The shared prelude of the four Nebentypus / q-expansion pins lives in
  `WeightOneLiftLevel`; this module carries the row and the pin's row-local declarations at the pin's
  names and statements.

  spec-pin: P2M/Sol/S_DihedralWeightOne_exists_hasNebentypus_eq_weightOneLift_of_mem_span_of_apply_mul_finEmbed_eq_inv_mul.lean

  ## Port deltas

  - **Namespaces.** The pin's search-stage namespaces (`DescentEngine`, `DescentSupportB`,
    `GammaOneCuspAux`, `NebentypusDescent`) are flattened to `DihedralWeightOne`, as the received
    scaffold had them; every declaration keeps the pin's bare name. Everything the pin's proofs
    call that the shared prelude already carries (`slashHom`, `σ_apply_of_det_pos`,
    `continuous_slash`, `archPart`, `gl_ext_of_arch_fin`,
    `exists_eq_globalPoints_mul_mul_finEmbed_of_mem_finiteLevelOne`, `map_algebraMap_mem_finiteLevelZero`,
    `map_castHom_mapGL`, `mapGL_mem_GLPos`, …) resolves unqualified from
    `WeightOneLiftLevel`, which declares it in this same namespace.
  - **Bodies, two mathlib-`v4.34` substitutions (both statement-neutral).** In the row's first
    conjunct a `rfl` closes after the pin's own last `rw [hF₀, hval, hinvε,
    ModularGroup.denom_apply]`: this mathlib's `CuspForm.HasNebentypus` evaluates the character at
    `ModularForm.Level.dd γ`, a `def` that `rw` will not unfold at `implicit` transparency
    (FR-0238's class); the pin's `ε (γ 1 1)` spelling is that value by definition. And
    `CuspForm.coe_zero` is `FunLike.coe_zero` (deprecated in `v4.34`; the deprecation warning
    would break the module's silence, FR-0231's class).
  - **Scaffold sections left as generated.** The repeated `variable (p : ℕ) [hp : Fact p.Prime]`
    lines and the repeated `{M} {g} {φ}` / `{N} {ε} {y}` blocks are inert: no declaration in the
    module mentions `p`/`hp` (or repeats of the same variable), so they are dropped from every
    elaborated signature and no statement moves. Nothing was re-spelled.
  - No import was added or removed; the four imports are the scaffold's.

  ## Dead-surface note (two declarations kept)

  The dead-code sweep reports `2 declarations, 7 lines`: `isReal_rat_infinitePlace` (`:25`) and
  `ratArchHom` (`:27`), both `private`. **They are not deleted.** In the pin they are live — their
  users are the pin's `ratArchHom_apply` / `ratArch_mul` / `ratArch_inv` / `ratArch_globalPoints`
  (`:32`–`:63`), which the port houses in `LanglandsTunnell/WeightOneLiftLevel.lean` (at
  `DihedralWeightOne` names) and, under the same names, in `WeightOneLiftAdelic`'s `RatArch` block.
  Those users refer to the prelude's own copies, so the two are dead here *only because the port
  resolved the reference differently* — the CARRY-FORWARD rule of SET-AF94C says keep them.

  ## Heartbeat probe (never installed, FR-0225)

  The silence gate is `lake env lean -DautoImplicit=false` at the project's own
  `maxHeartbeats = 4000000` (silent, ~5.9 s wall). Probe pair: **silent at
  `-DmaxHeartbeats=6000`, failing at `-DmaxHeartbeats=3000`** (`deterministic timeout at whnf`);
  no `set_option maxHeartbeats` is carried in the file.
-/


import FLTForHuman.LanglandsTunnell.WeightOneLiftLevel
import FLTForHuman.LanglandsTunnell.WeightOneLiftNebentypus
import FLTForHuman.NumberTheory.LocalNewvector.AdelicSpan
import FLTForHuman.ModularForms.PrimitiveFormBasis

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm UpperHalfPlane
open LocalNewvector
open UpperHalfPlane Matrix
open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel Matrix
open Matrix Matrix.GeneralLinearGroup Matrix.SpecialLinearGroup
open CongruenceSubgroup ModularGroup
open AdelicDock
open NumberField.AdelicHaar
open HeckeIntegralSeam HeckePair
open AutomorphicForm.SmoothCusp IsDedekindDomain.HeightOneSpectrum
open CuspForm ModularFormClass ModularForm
open LanglandsTunnell.RatArch

open NumberField.AdelicLevel AutomorphicForm.WindowedSiegel NumberField.AdelicVolume
open MeasureTheory
open scoped Topology Manifold
open DihedralWeightOne LocalNewvector


namespace DihedralWeightOne



section

variable (p : ℕ) [hp : Fact p.Prime]

private theorem isReal_rat_infinitePlace (v : InfinitePlace ℚ) : v.IsReal := IsTotallyReal.isReal v

private noncomputable def ratArchHom : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) →* GL (Fin 2) ℝ :=
  (Matrix.GeneralLinearGroup.map
    (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom).comp
    ((archComponent ℚ default).comp (glArch (𝓞 ℚ) ℚ))

private theorem glFin_globalPoints_apply (γ : GL (Fin 2) ℚ) (i j : Fin 2) :
    (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j
      = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j) := rfl

end

section

variable (p : ℕ) [hp : Fact p.Prime]
variable (p : ℕ) [hp : Fact p.Prime]
variable (p : ℕ) [hp : Fact p.Prime]
variable {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma1 M) 1} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}

private noncomputable def slashSpan (g : CuspForm (CongruenceSubgroup.Gamma1 M) 1) : Submodule ℂ (UpperHalfPlane → ℂ) :=
  Submodule.span ℂ (Set.range fun β : GL (Fin 2) ℚ => (⇑g) ∣[(1 : ℤ)] β.map (Rat.castHom ℝ))

private theorem slash_map_mem_slashSpan (β : GL (Fin 2) ℚ) : (⇑g) ∣[(1 : ℤ)] β.map (Rat.castHom ℝ) ∈ slashSpan g :=
  Submodule.subset_span ⟨β, rfl⟩

private def HasReading (y : AdelicSpan φ) (F : UpperHalfPlane → ℂ) : Prop :=
  ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ h = 1 → LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
    (AdelicSpan.toFn φ y).toFn h = weightOneArchLift F (LanglandsTunnell.ratArchGL2 h)

private theorem weightOneArchLift_zero' (A : GL (Fin 2) ℝ) : weightOneArchLift (0 : UpperHalfPlane → ℂ) A = 0 := by
  unfold weightOneArchLift
  rw [SlashAction.zero_slash, Pi.zero_apply, zero_mul]

private theorem weightOneArchLift_add' (F₁ F₂ : UpperHalfPlane → ℂ) (A : GL (Fin 2) ℝ) :
    weightOneArchLift (F₁ + F₂) A = weightOneArchLift F₁ A + weightOneArchLift F₂ A := by
  unfold weightOneArchLift
  rw [SlashAction.add_slash, Pi.add_apply, add_mul]

private theorem weightOneArchLift_smul' (c : ℂ) (F : UpperHalfPlane → ℂ) {A : GL (Fin 2) ℝ} (hA : 0 < (A.det : ℝ)) :
    weightOneArchLift (c • F) A = c * weightOneArchLift F A := by
  unfold weightOneArchLift
  rw [ModularForm.smul_slash, Pi.smul_apply, σ_apply_of_det_pos hA, smul_eq_mul, mul_assoc]

private theorem weightOneArchLift_mul' (F : UpperHalfPlane → ℂ) (A B : GL (Fin 2) ℝ) :
    weightOneArchLift F (A * B) = (((A.det.val : ℝ)) : ℂ) * weightOneArchLift (F ∣[(1 : ℤ)] A) B := by
  unfold weightOneArchLift
  rw [SlashAction.slash_mul, map_mul, Units.val_mul, Complex.ofReal_mul, zpow_one, zpow_one]
  ring

private theorem hasReading_zero : HasReading (0 : AdelicSpan φ) (0 : UpperHalfPlane → ℂ) := by
  intro h _ _
  rw [weightOneArchLift_zero']
  rfl

private theorem HasReading.add {y₁ y₂ : AdelicSpan φ} {F₁ F₂ : UpperHalfPlane → ℂ} (h₁ : HasReading y₁ F₁)
    (h₂ : HasReading y₂ F₂) : HasReading (y₁ + y₂) (F₁ + F₂) := by
  intro h hh hpos
  rw [weightOneArchLift_add', ← h₁ h hh hpos, ← h₂ h hh hpos]
  rfl

private theorem HasReading.smul {y : AdelicSpan φ} {F : UpperHalfPlane → ℂ} (hy : HasReading y F) (c : ℂ) :
    HasReading (c • y) (c • F) := by
  intro h hh hpos
  rw [weightOneArchLift_smul' c F ((Matrix.mem_glpos _).mp hpos), ← hy h hh hpos]
  rfl

private theorem glFin_conj_eq_one (δ : GL (Fin 2) ℚ) {h : AdelicGL2 (𝓞 ℚ) ℚ} (hh : glFin (𝓞 ℚ) ℚ h = 1) :
    glFin (𝓞 ℚ) ℚ ((globalPoints (𝓞 ℚ) ℚ δ)⁻¹ * h * globalPoints (𝓞 ℚ) ℚ δ) = 1 := by
  rw [map_mul, map_mul, hh, mul_one, map_inv, inv_mul_cancel]

private theorem exists_hasReading_finEmbed_smul_self (hM : M ≠ 0)
    (hφleft : ∀ (γ : GL (Fin 2) ℚ) (x : AdelicGL2 (𝓞 ℚ) ℚ), φ (globalPoints (𝓞 ℚ) ℚ γ * x) = φ x)
    (hφlev : ∀ w ∈ finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel M), ∀ x : AdelicGL2 (𝓞 ℚ) ℚ,
      φ (x * finEmbed (𝓞 ℚ) ℚ w) = φ x)
    (hφeq : ∀ x : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ x = 1 →
      LanglandsTunnell.ratArchGL2 x ∈ Matrix.GLPos (Fin 2) ℝ → φ x = weightOneArchLift (⇑g) (LanglandsTunnell.ratArchGL2 x))
    (u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    ∃ F ∈ slashSpan g, HasReading ((finEmbed (𝓞 ℚ) ℚ u : AdelicGL2 (𝓞 ℚ) ℚ) • AdelicSpan.self φ) F := by
  obtain ⟨δ, a, w, ha, hapos, hw, hdec⟩ :=
    exists_eq_globalPoints_mul_mul_finEmbed_of_mem_finiteLevelOne hM (finEmbed (𝓞 ℚ) ℚ u)

  have harch : LanglandsTunnell.ratArchGL2 a = (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) δ)⁻¹ := by
    have h0 : LanglandsTunnell.ratArchGL2 (finEmbed (𝓞 ℚ) ℚ u) = 1 := ratArch_finEmbed _
    rw [hdec, ratArch_mul, ratArch_mul, ratArch_finEmbed, mul_one, ratArch_globalPoints] at h0
    exact eq_inv_of_mul_eq_one_right h0
  refine ⟨((((Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) δ⁻¹).det.val : ℝ)) : ℂ) •
      ((⇑g) ∣[(1 : ℤ)] δ⁻¹.map (Rat.castHom ℝ)),
    Submodule.smul_mem _ _ (slash_map_mem_slashSpan δ⁻¹), ?_⟩
  intro h hh hpos
  have hval : (AdelicSpan.toFn φ ((finEmbed (𝓞 ℚ) ℚ u : AdelicGL2 (𝓞 ℚ) ℚ) • AdelicSpan.self φ)).toFn h
      = φ (h * finEmbed (𝓞 ℚ) ℚ u) := by
    rw [AdelicSpan.toFn_smul, AdelicFnCarrier.toFn_smul, AdelicSpan.toFn_self, AdelicFnCarrier.toFn_mk]
  rw [hval, hdec, ← mul_assoc, ← mul_assoc, hφlev w hw]
  have hre : h * globalPoints (𝓞 ℚ) ℚ δ * a
      = globalPoints (𝓞 ℚ) ℚ δ * (((globalPoints (𝓞 ℚ) ℚ δ)⁻¹ * h * globalPoints (𝓞 ℚ) ℚ δ) * a) := by
    group
  have hh' : glFin (𝓞 ℚ) ℚ (((globalPoints (𝓞 ℚ) ℚ δ)⁻¹ * h * globalPoints (𝓞 ℚ) ℚ δ) * a) = 1 := by
    rw [map_mul, glFin_conj_eq_one δ hh, ha, mul_one]
  have hratarch : LanglandsTunnell.ratArchGL2 (((globalPoints (𝓞 ℚ) ℚ δ)⁻¹ * h * globalPoints (𝓞 ℚ) ℚ δ) * a)
      = (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) δ)⁻¹ * LanglandsTunnell.ratArchGL2 h := by
    rw [ratArch_mul, ratArch_mul, ratArch_mul, ratArch_inv, ratArch_globalPoints, harch, mul_assoc,
      mul_inv_cancel, mul_one]
  have hpos' : LanglandsTunnell.ratArchGL2 (((globalPoints (𝓞 ℚ) ℚ δ)⁻¹ * h * globalPoints (𝓞 ℚ) ℚ δ) * a)
      ∈ Matrix.GLPos (Fin 2) ℝ := by
    rw [hratarch, ← harch]
    exact Subgroup.mul_mem _ hapos hpos
  rw [hre, hφleft, hφeq _ hh' hpos', hratarch, weightOneArchLift_mul',
    weightOneArchLift_smul' _ _ ((Matrix.mem_glpos _).mp hpos),
    map_inv (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ)) δ, map_inv]

private theorem exists_hasReading_of_mem_span (hM : M ≠ 0)
    (hφleft : ∀ (γ : GL (Fin 2) ℚ) (x : AdelicGL2 (𝓞 ℚ) ℚ), φ (globalPoints (𝓞 ℚ) ℚ γ * x) = φ x)
    (hφlev : ∀ w ∈ finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel M), ∀ x : AdelicGL2 (𝓞 ℚ) ℚ,
      φ (x * finEmbed (𝓞 ℚ) ℚ w) = φ x)
    (hφeq : ∀ x : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ x = 1 →
      LanglandsTunnell.ratArchGL2 x ∈ Matrix.GLPos (Fin 2) ℝ → φ x = weightOneArchLift (⇑g) (LanglandsTunnell.ratArchGL2 x))
    {y : AdelicSpan φ}
    (hy : y ∈ Submodule.span ℂ (Set.range fun u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) =>
      (finEmbed (𝓞 ℚ) ℚ u : AdelicGL2 (𝓞 ℚ) ℚ) • AdelicSpan.self φ)) :
    ∃ F ∈ slashSpan g, HasReading y F := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, rfl⟩ := hy
    exact exists_hasReading_finEmbed_smul_self hM hφleft hφlev hφeq u
  | zero => exact ⟨0, Submodule.zero_mem _, hasReading_zero⟩
  | add y₁ y₂ _ _ ih₁ ih₂ =>
    obtain ⟨F₁, hF₁, h₁⟩ := ih₁
    obtain ⟨F₂, hF₂, h₂⟩ := ih₂
    exact ⟨F₁ + F₂, Submodule.add_mem _ hF₁ hF₂, h₁.add h₂⟩
  | smul c y _ ih =>
    obtain ⟨F, hF, h⟩ := ih
    exact ⟨c • F, Submodule.smul_mem _ c hF, h.smul c⟩

end

section

variable (p : ℕ) [hp : Fact p.Prime]
variable (p : ℕ) [hp : Fact p.Prime]
variable (p : ℕ) [hp : Fact p.Prime]
variable {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma1 M) 1} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
variable {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma1 M) 1}

private theorem continuous_of_mem_slashSpan {F : UpperHalfPlane → ℂ} (hF : F ∈ slashSpan g) : Continuous F := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨β, rfl⟩ := hF
    exact continuous_slash (CuspFormClass.holo g).continuous 1 _
  | zero => exact continuous_const
  | add F₁ F₂ _ _ h₁ h₂ => exact h₁.add h₂
  | smul c F _ h => exact h.const_smul c

private theorem eq_of_forall_weightOneArchLift_eq {F G : UpperHalfPlane → ℂ} (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ h = 1 → LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
      weightOneArchLift F (LanglandsTunnell.ratArchGL2 h) = weightOneArchLift G (LanglandsTunnell.ratArchGL2 h)) :
    F = G := by
  refine Continuous.ext_on dense_ratPoints hF hG ?_
  rintro z ⟨hx, hy⟩
  obtain ⟨h, hfin, hpos, hz⟩ := exists_glFin_eq_one_and_smul_I_eq z hx hy
  have hdet : (0 : ℝ) < (LanglandsTunnell.ratArchGL2 h).det.val := (Matrix.mem_glpos _).mp hpos
  have key := hFG h hfin hpos
  unfold weightOneArchLift at key
  rw [ModularForm.slash_apply, ModularForm.slash_apply, σ_apply_of_det_pos hdet, σ_apply_of_det_pos hdet, hz]
    at key
  have ha : ((|(LanglandsTunnell.ratArchGL2 h).det.val| : ℝ) : ℂ) ^ ((1 : ℤ) - 1) ≠ 0 :=
    zpow_ne_zero _ (by exact_mod_cast (abs_ne_zero.mpr hdet.ne'))
  have hb : UpperHalfPlane.denom (LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I ^ (-(1 : ℤ)) ≠ 0 :=
    zpow_ne_zero _ (UpperHalfPlane.denom_ne_zero _ _)
  have hd : (((LanglandsTunnell.ratArchGL2 h).det.val : ℝ) : ℂ) ^ (1 : ℤ) ≠ 0 :=
    zpow_ne_zero _ (by exact_mod_cast hdet.ne')
  exact mul_right_cancel₀ ha (mul_right_cancel₀ hb (mul_right_cancel₀ hd key))

end

section

variable (p : ℕ) [hp : Fact p.Prime]
variable (p : ℕ) [hp : Fact p.Prime]
variable (p : ℕ) [hp : Fact p.Prime]
variable {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma1 M) 1} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
variable {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma1 M) 1}
variable {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma1 M) 1} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}

private abbrev fn (y : AdelicSpan φ) : AdelicGL2 (𝓞 ℚ) ℚ → ℂ := (AdelicSpan.toFn φ y).toFn

private theorem fn_smul_self (u : AdelicGL2 (𝓞 ℚ) ℚ) (z : AdelicGL2 (𝓞 ℚ) ℚ) :
    fn (u • AdelicSpan.self φ) z = φ (z * u) := by
  rw [fn, AdelicSpan.toFn_smul, AdelicFnCarrier.toFn_smul, AdelicSpan.toFn_self, AdelicFnCarrier.toFn_mk]

private theorem fn_add (y₁ y₂ : AdelicSpan φ) (z : AdelicGL2 (𝓞 ℚ) ℚ) : fn (y₁ + y₂) z = fn y₁ z + fn y₂ z := rfl

private theorem fn_csmul (c : ℂ) (y : AdelicSpan φ) (z : AdelicGL2 (𝓞 ℚ) ℚ) : fn (c • y) z = c * fn y z := rfl

private theorem fn_zero (z : AdelicGL2 (𝓞 ℚ) ℚ) : fn (0 : AdelicSpan φ) z = 0 := rfl

private theorem hasReading_iff (y : AdelicSpan φ) (F : UpperHalfPlane → ℂ) :
    HasReading y F ↔ ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ h = 1 →
      LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
        fn y h = weightOneArchLift F (LanglandsTunnell.ratArchGL2 h) := Iff.rfl

end

section

variable (p : ℕ) [hp : Fact p.Prime]
variable (p : ℕ) [hp : Fact p.Prime]
variable (p : ℕ) [hp : Fact p.Prime]
variable {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma1 M) 1} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
variable {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma1 M) 1}
variable {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma1 M) 1} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
variable {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma1 M) 1} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}

private lemma isCusp_SL2Z_map_smul {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) (β : GL (Fin 2) ℚ) :
    IsCusp (β.map (Rat.castHom ℝ) • c) 𝒮ℒ := by
  rw [isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨c₀, rfl⟩ := hc
  refine ⟨β • c₀, ?_⟩
  have h := OnePoint.map_smul (Rat.castHom ℝ) β c₀
  simpa only [Rat.coe_castHom] using h

private lemma isCusp_SL2Z_of_isCusp_map {Γ : Subgroup SL(2, ℤ)} {c : OnePoint ℝ}
    (hc : IsCusp c (Subgroup.map (mapGL ℝ) Γ)) : IsCusp c 𝒮ℒ :=
  hc.mono (Subgroup.map_le_range _ _)

private lemma isZeroAt_slash_map {M : ℕ} [NeZero M] (g : CuspForm (CongruenceSubgroup.Gamma1 M) 1)
    (β : GL (Fin 2) ℚ) {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) :
    c.IsZeroAt ((⇑g) ∣[(1 : ℤ)] β.map (Rat.castHom ℝ)) 1 := by
  rw [← OnePoint.IsZeroAt.smul_iff]
  apply CuspFormClass.zero_at_cusps g
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]
  exact isCusp_SL2Z_map_smul hc β

private lemma isZeroAt_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → UpperHalfPlane → ℂ)
    {x : OnePoint ℝ} (hf : ∀ i ∈ s, x.IsZeroAt (f i) 1) :
    x.IsZeroAt (∑ i ∈ s, c i • f i) 1 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro γ _
    simp
    exact Filter.zero_zeroAtFilter _
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine OnePoint.IsZeroAt.add ?_ (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
    intro γ hγ
    rw [ModularForm.smul_slash]
    exact (hf a (Finset.mem_insert_self a s) γ hγ).smul _

private lemma mdifferentiable_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → UpperHalfPlane → ℂ)
    (hf : ∀ i ∈ s, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f i)) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (∑ i ∈ s, c i • f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => (simp; exact mdifferentiable_const)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact ((hf a (Finset.mem_insert_self a s)).const_smul _).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem exists_gamma1_cuspForm_coe_eq
    {M N : ℕ} [NeZero M] (g : CuspForm (CongruenceSubgroup.Gamma1 M) 1)
    {ι : Type} [Fintype ι] (c : ι → ℂ) (β : ι → GL (Fin 2) ℚ)
    (F : UpperHalfPlane → ℂ)
    (hF : F = ∑ i, c i • ((⇑g) ∣[(1 : ℤ)] (β i).map (Rat.castHom ℝ)))
    (hinv : ∀ γ ∈ Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma1 N),
      F ∣[(1 : ℤ)] γ = F) :
    ∃ h : CuspForm (CongruenceSubgroup.Gamma1 N) 1, ⇑h = F :=
  ⟨{ toFun := F
     slash_action_eq' := hinv
     holo' := by
       subst hF
       exact mdifferentiable_sum _ _ _ fun i _ => (CuspFormClass.holo g).slash _ _
     zero_at_cusps' := fun hc => by
       subst hF
       exact isZeroAt_sum _ _ _ fun i _ => isZeroAt_slash_map g (β i) (isCusp_SL2Z_of_isCusp_map hc) },
   rfl⟩

end

section

variable (p : ℕ) [hp : Fact p.Prime]
variable (p : ℕ) [hp : Fact p.Prime]
variable (p : ℕ) [hp : Fact p.Prime]
variable {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma1 M) 1} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
variable {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma1 M) 1}
variable {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma1 M) 1} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
variable {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma1 M) 1} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
variable {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma1 M) 1}
variable {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
variable {N : ℕ} {ε : DirichletCharacter ℂ N} {y : AdelicSpan Φ}

private theorem exists_eq_sum_of_mem_slashSpan' {F : UpperHalfPlane → ℂ} (hF : F ∈ slashSpan g) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℂ) (β : ι → GL (Fin 2) ℚ),
      F = ∑ i, c i • ((⇑g) ∣[(1 : ℤ)] (β i).map (Rat.castHom ℝ)) := by
  obtain ⟨l, hl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).mp hF
  refine ⟨l.support, inferInstance, fun i => l i, fun i => (i : GL (Fin 2) ℚ), ?_⟩
  rw [← hl, Finsupp.sum, ← Finset.sum_coe_sort]

private theorem fn_globalPoints_mul_of_mem_span
    (hΦleft : ∀ (γ : GL (Fin 2) ℚ) (x : AdelicGL2 (𝓞 ℚ) ℚ), Φ (globalPoints (𝓞 ℚ) ℚ γ * x) = Φ x)
    (hy : y ∈ Submodule.span ℂ (Set.range fun u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) =>
      (finEmbed (𝓞 ℚ) ℚ u : AdelicGL2 (𝓞 ℚ) ℚ) • AdelicSpan.self Φ))
    (γ : GL (Fin 2) ℚ) (z : AdelicGL2 (𝓞 ℚ) ℚ) :
    fn y (globalPoints (𝓞 ℚ) ℚ γ * z) = fn y z := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, rfl⟩ := hy
    rw [fn_smul_self, fn_smul_self, mul_assoc, hΦleft]
  | zero => rfl
  | add y₁ y₂ _ _ ih₁ ih₂ => rw [fn_add, fn_add, ih₁, ih₂]
  | smul c y _ ih => rw [fn_csmul, fn_csmul, ih]

private theorem fn_mul_finEmbed_of_mem_finiteLevelOne
    (hK0 : ∀ u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N), ∀ d : ℤ, IsCoprime d (N : ℤ) →
      (u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
          - algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (d : ℚ) ∈ idealBall (𝓞 ℚ) ℚ (ratLevel N) →
      ∀ z, fn y (z * finEmbed (𝓞 ℚ) ℚ u) = (ε (d : ZMod N))⁻¹ * fn y z)
    {u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hu : u ∈ finiteLevelOne (𝓞 ℚ) ℚ (ratLevel N))
    (z : AdelicGL2 (𝓞 ℚ) ℚ) : fn y (z * finEmbed (𝓞 ℚ) ℚ u) = fn y z := by
  have h := hK0 u (finiteLevelOne_le_finiteLevelZero (𝓞 ℚ) ℚ _ hu) 1 isCoprime_one_left (by
    rw [Int.cast_one, map_one]
    exact (mem_finiteLevelOne_iff.mp hu).1.lowerRight) z
  rwa [Int.cast_one, map_one, inv_one, one_mul] at h

private theorem slash_eq_inv_smul (hN : N ≠ 0) {F : UpperHalfPlane → ℂ} (hF : Continuous F)
    (hread : HasReading y F)
    (hleft : ∀ γ z, fn y (globalPoints (𝓞 ℚ) ℚ γ * z) = fn y z)
    (hK0 : ∀ u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N), ∀ d : ℤ, IsCoprime d (N : ℤ) →
      (u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
          - algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (d : ℚ) ∈ idealBall (𝓞 ℚ) ℚ (ratLevel N) →
      ∀ z, fn y (z * finEmbed (𝓞 ℚ) ℚ u) = (ε (d : ZMod N))⁻¹ * fn y z)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (hcop : IsCoprime (γ 0 0 : ℤ) (N : ℤ)) :
    F ∣[(1 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = (ε ((γ 0 0 : ℤ) : ZMod N))⁻¹ • F := by
  set δ : GL (Fin 2) ℚ := Matrix.SpecialLinearGroup.mapGL ℚ γ with hδ
  refine eq_of_forall_weightOneArchLift_eq (continuous_slash hF 1 _)
    (hF.const_smul ((ε ((γ 0 0 : ℤ) : ZMod N))⁻¹)) fun h hh hpos => ?_
  have hpos' : LanglandsTunnell.ratArchGL2 (archPart δ * h) ∈ Matrix.GLPos (Fin 2) ℝ := by
    rw [ratArch_archPart_mul, hδ, map_castHom_mapGL]
    exact Subgroup.mul_mem _ (mapGL_mem_GLPos γ) hpos
  have hread' := (hasReading_iff y F).mp hread
  have h1 := hread' (archPart δ * h) (glFin_archPart_mul hh δ) hpos'
  rw [ratArch_archPart_mul, hδ, map_castHom_mapGL, weightOneArchLift_mul'] at h1
  rw [← hδ] at h1
  have hdet1 : ((((Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)).det.val : ℝ) : ℂ) = 1 := by
    rw [Matrix.SpecialLinearGroup.det_mapGL]; simp
  rw [hdet1, one_mul] at h1
  have hG : glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ δ) ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N) :=
    glFin_globalPoints_mapGL_mem_finiteLevelZero hN hγ
  have h2 : archPart δ * h
      = globalPoints (𝓞 ℚ) ℚ δ * (h * finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ δ))⁻¹) := by
    rw [archPart, mul_assoc, ← map_inv, finEmbed_mul_comm_of_glFin_eq_one hh]

  have hval : (((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ δ))⁻¹ :
        GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
          - algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (((γ 0 0 : ℤ)) : ℚ)
      ∈ idealBall (𝓞 ℚ) ℚ (ratLevel N) := by
    have hentry : (((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ δ))⁻¹ :
        GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
          = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (((γ 0 0 : ℤ) : ℚ)) := by
      rw [← map_inv, ← map_inv, glFin_globalPoints_apply, hδ, ← map_inv]
      congr 1
      have hmat : ((Matrix.SpecialLinearGroup.mapGL ℚ γ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ)
          = ((γ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ) := rfl
      rw [hmat, Matrix.map_apply, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
      simp
    rw [hentry, sub_self]
    exact zero_mem_idealBall _
  rw [h2, hleft, hK0 _ (Subgroup.inv_mem _ hG) (γ 0 0) hcop hval] at h1
  rw [← h1, hread' h hh hpos, weightOneArchLift_smul' _ _ ((Matrix.mem_glpos _).mp hpos)]

private theorem eq_zero_of_hasReading_zero' (hN : N ≠ 0) (hread : HasReading y 0)
    (hleft : ∀ γ z, fn y (globalPoints (𝓞 ℚ) ℚ γ * z) = fn y z)
    (hK1 : ∀ u ∈ finiteLevelOne (𝓞 ℚ) ℚ (ratLevel N), ∀ z, fn y (z * finEmbed (𝓞 ℚ) ℚ u) = fn y z) :
    y = 0 := by
  refine AdelicSpan.ext _ (AdelicFnCarrier.ext fun z => ?_)
  obtain ⟨γ, h, u, hh, hpos, hu, rfl⟩ := exists_eq_globalPoints_mul_mul_finEmbed_of_mem_finiteLevelOne hN z
  change fn y _ = fn (0 : AdelicSpan Φ) _
  rw [fn_zero, hK1 u hu, hleft, (hasReading_iff y 0).mp hread h hh hpos, weightOneArchLift_zero']

private theorem isCoprime_and_mul_eq_one {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    IsCoprime (γ 0 0 : ℤ) (N : ℤ) ∧ ((γ 0 0 : ℤ) : ZMod N) * (γ 1 1 : ℤ) = 1 := by
  have hc : ((γ 1 0 : ℤ) : ZMod N) = 0 := CongruenceSubgroup.Gamma0_mem.mp hγ
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at this
    exact this
  refine ⟨?_, ?_⟩
  · obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc
    refine ⟨γ 1 1, -(γ 0 1 * m), ?_⟩
    rw [hm] at hdet
    linear_combination hdet
  · have := congrArg (fun z : ℤ => (z : ZMod N)) hdet
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hc, mul_zero, sub_zero] at this
    exact this

end

theorem exists_hasNebentypus_eq_weightOneLift_of_mem_span_of_apply_mul_finEmbed_eq_inv_mul
    {M : ℕ} [NeZero M] (h : CuspForm (CongruenceSubgroup.Gamma1 M) 1)
    {N : ℕ} [NeZero N] (ε : DirichletCharacter ℂ N)
    (y : LocalNewvector.AdelicSpan (weightOneLift (Ideal.span {(M : 𝓞 ℚ)}) (⇑h)))
    (hy : y ∈ Submodule.span ℂ (Set.range fun u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) =>
      (AdelicDock.finEmbed (𝓞 ℚ) ℚ u : AdelicGL2 (𝓞 ℚ) ℚ) •
        LocalNewvector.AdelicSpan.self (weightOneLift (Ideal.span {(M : 𝓞 ℚ)}) (⇑h))))
    (hK0 : ∀ u ∈ finiteLevelZero (𝓞 ℚ) ℚ (AdelicDock.ratLevel N), ∀ d : ℤ, IsCoprime d (N : ℤ) →
      (u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
          - algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (d : ℚ) ∈ idealBall (𝓞 ℚ) ℚ (AdelicDock.ratLevel N) →
      ∀ x : AdelicGL2 (𝓞 ℚ) ℚ,
        (LocalNewvector.AdelicSpan.toFn _ y).toFn (x * AdelicDock.finEmbed (𝓞 ℚ) ℚ u) =
          (ε (d : ZMod N))⁻¹ * (LocalNewvector.AdelicSpan.toFn _ y).toFn x) :
    ∃ F : CuspForm (CongruenceSubgroup.Gamma1 N) 1,
      CuspForm.HasNebentypus ε F ∧
      (LocalNewvector.AdelicSpan.toFn _ y).toFn = weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑F) ∧
      (F = 0 → y = 0) := by
  classical
  have hM : M ≠ 0 := NeZero.ne M
  have hN : N ≠ 0 := NeZero.ne N

  have hfh : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma1 M → (⇑h) ∣[(1 : ℤ)] (γ : GL (Fin 2) ℝ) = ⇑h :=
    fun γ hγ => SlashInvariantForm.slash_action_eqn h _ ⟨γ, hγ, rfl⟩
  obtain ⟨hφleft, hφlev, hφeq⟩ :=
    DihedralWeightOne.weightOneLift_globalPoints_mul_and_mul_finEmbed_and_eq_weightOneArchLift hM (⇑h) hfh

  have hleft : ∀ γ z, fn y (globalPoints (𝓞 ℚ) ℚ γ * z) = fn y z :=
    fun γ z => fn_globalPoints_mul_of_mem_span hφleft hy γ z
  have hK1 : ∀ u ∈ finiteLevelOne (𝓞 ℚ) ℚ (ratLevel N), ∀ z, fn y (z * finEmbed (𝓞 ℚ) ℚ u) = fn y z :=
    fun u hu z => fn_mul_finEmbed_of_mem_finiteLevelOne hK0 hu z

  obtain ⟨F, hFspan, hread⟩ := exists_hasReading_of_mem_span hM hφleft hφlev hφeq hy
  have hFcont : Continuous F := continuous_of_mem_slashSpan hFspan

  have hslash : ∀ γ ∈ CongruenceSubgroup.Gamma0 N,
      F ∣[(1 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = (ε ((γ 0 0 : ℤ) : ZMod N))⁻¹ • F :=
    fun γ hγ => slash_eq_inv_smul hN hFcont hread hleft hK0 hγ (isCoprime_and_mul_eq_one hγ).1

  have hinv : ∀ γ' ∈ Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma1 N),
      F ∣[(1 : ℤ)] γ' = F := by
    rintro γ' ⟨γ, hγ, rfl⟩
    have hγ0 : γ ∈ CongruenceSubgroup.Gamma0 _ := CongruenceSubgroup.Gamma1_in_Gamma0 _ hγ
    have ha1 : ((γ 0 0 : ℤ) : ZMod N) = 1 := ((CongruenceSubgroup.Gamma1_mem _ γ).mp hγ).1
    rw [hslash γ hγ0, ha1, map_one, inv_one, one_smul]
  obtain ⟨ι, _, c, β, hF⟩ := exists_eq_sum_of_mem_slashSpan' hFspan
  obtain ⟨F₀, hF₀⟩ := exists_gamma1_cuspForm_coe_eq h c β F hF hinv
  refine ⟨F₀, ?_, ?_, ?_⟩
  ·
    intro γ hγ τ
    obtain ⟨-, hmod⟩ := isCoprime_and_mul_eq_one hγ
    have hsl := congrFun (hslash γ hγ) τ
    have hSL : (F ∣[(1 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)) τ
        = F (γ • τ) * UpperHalfPlane.denom γ τ ^ (-(1 : ℤ)) := ModularForm.SL_slash_apply (k := 1) F γ τ
    rw [hSL, Pi.smul_apply, smul_eq_mul] at hsl
    have hden : UpperHalfPlane.denom γ τ ≠ 0 := UpperHalfPlane.denom_ne_zero γ τ
    have hval : F (γ • τ) = (ε ((γ 0 0 : ℤ) : ZMod N))⁻¹ * (UpperHalfPlane.denom γ τ ^ (1 : ℤ) * F τ) := by
      have := congrArg (fun z => z * UpperHalfPlane.denom γ τ ^ (1 : ℤ)) hsl
      rw [mul_assoc, ← zpow_add₀ hden, show (-(1 : ℤ)) + 1 = 0 by norm_num, zpow_zero, mul_one] at this
      rw [this]; ring
    have hinvε : (ε ((γ 0 0 : ℤ) : ZMod N))⁻¹ = ε ((γ 1 1 : ℤ) : ZMod N) := by
      symm
      apply eq_inv_of_mul_eq_one_right
      rw [← map_mul, hmod, map_one]
    rw [hF₀, hval, hinvε, ModularGroup.denom_apply]
    rfl
  ·
    have hfF : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma1 N → (⇑F₀) ∣[(1 : ℤ)] (γ : GL (Fin 2) ℝ) = ⇑F₀ :=
      fun γ hγ => SlashInvariantForm.slash_action_eqn F₀ _ ⟨γ, hγ, rfl⟩
    obtain ⟨hLleft, hLlev, hLeq⟩ :=
      DihedralWeightOne.weightOneLift_globalPoints_mul_and_mul_finEmbed_and_eq_weightOneArchLift hN (⇑F₀) hfF
    funext x
    obtain ⟨γ, x', u, hx', hpos', hu, rfl⟩ := exists_eq_globalPoints_mul_mul_finEmbed_of_mem_finiteLevelOne hN x
    change fn y _ = _
    rw [hK1 u hu, hleft, hLlev u hu, hLleft, hLeq x' hx' hpos', hF₀]
    exact hread x' hx' hpos'
  ·
    rintro rfl
    have hF0 : F = 0 := by rw [← hF₀, FunLike.coe_zero]
    exact eq_zero_of_hasReading_zero' hN (by simpa [hF0] using hread) hleft hK1

end DihedralWeightOne

end
