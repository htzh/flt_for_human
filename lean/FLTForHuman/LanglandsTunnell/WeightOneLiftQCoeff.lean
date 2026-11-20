/-
  The weight-one lift and the Hecke eigenvalues of its q-expansion.

  Two rows. First, the Hecke eigenvalue relation for the q-expansion coefficients of the
  cusp form `F` whose lift is an eigenfunction of the `ℓ`-th Hecke sum; then the sum identity
  that produces it: the `ℓ + 1` translates of the lift by the level-`ℓ` coset representatives
  add up to `λ` times the lift.

  Transcribed from
  `P2M/Sol/S_DihedralWeightOne_qCoeff_hecke_eq_of_hasNebentypus_of_sum_weightOneLift_mul_padicToAdelic_inv_eq.lean`
  (1,261 lines / 105 declarations) and
  `P2M/Sol/S_DihedralWeightOne_sum_weightOneLift_mul_padicToAdelic_inv_eq_mul_slash_apply_I_mul_det.lean`
  (928 lines / 82 declarations). The shared prelude of the four Nebentypus / q-expansion pins
  lives in `WeightOneLiftLevel`; the row-local declarations keep the pin's `private` visibility,
  names and statements.

  spec-pin: P2M/Sol/S_DihedralWeightOne_qCoeff_hecke_eq_of_hasNebentypus_of_sum_weightOneLift_mul_padicToAdelic_inv_eq.lean
  spec-pin: P2M/Sol/S_DihedralWeightOne_sum_weightOneLift_mul_padicToAdelic_inv_eq_mul_slash_apply_I_mul_det.lean

  ## Heartbeat probe

  `lake env lean -DautoImplicit=false -DmaxHeartbeats=N` (the project's default is 4,000,000):
  silent at N = 10,000, fails at N = 5,000 (inside `qCoeff…`'s `hFGℓ`/`norm_num` block). No
  `set_option maxHeartbeats` is installed (FR-0225).

  ## Port deltas

  - `import FLTForHuman.LanglandsTunnell.WeightOneLiftGlobalPoints`: both rows' proofs reach
    `weightOneLift_globalPoints_mul_and_mul_finEmbed_and_eq_weightOneArchLift` (through
    `lift_dictionary`), which is not in `WeightOneLiftLevel`'s closure.
  - `import FLTForHuman.ModularForms.HeckeDiagDegeneracy`: `qCoeff…`'s proof reaches
    `CuspForm.exists_degeneracy_gamma1_hasNebentypus` (pin `Theorems/…`, likewise not in the closure).
  - `haveI : NeZero (N * ℓ)` → `have : …` (the `haveILetI` linter, FR-0223); `linter.unusedSectionVars`
    on `continuous_heckeSide`'s dead `hp` is spent with `have _ := hp` rather than `omit` (FR-0208).
  - `padicPlace_ne_of_ne'`: the pin's `simp only [padicPlace, Equiv.apply_symm_apply]` does not replay
    at v4.34 (the coercion blocks the rewrite); replaced — body only — by
    `(primesEquiv (R := 𝓞 ℚ)).symm.injective heq` followed by `congrArg Subtype.val`.
  - `FunLike.coe_smul`, `FunLike.coe_sub` and `ite_eq_left` replace the pin's
    `CuspForm.IsGLPos.coe_smul`, `CuspForm.coe_sub` and `if_pos` (v4.34 deprecations, body only).
  - The prelude carries the *specialized* `sum_apply_eq_slash` of pin 1 `:1084` (statement hash
    `a0c443b0…`), not pin 2's `Ψ`-general form; so `sum_weightOneLift…`'s proof drops pin 2's
    `(isLift1_weightOneLift F)` argument and closes with `ring`, because pin 1's right-hand side is
    `… I * ((ℓ : ℂ) * det)` while this row's is `(ℓ : ℂ) * (… I * det)`.
  - The port declares 7 declarations (2 public rows, 5 private), not the pins' 187.

  ## Deferred pin surface

  Sixteen declarations are dropped here; `move_dead` on this module reads `0 declarations, 0 lines`
  after their removal. The manager registers them in `CARRY-FORWARD.md`.

  - Dead in the pins too (`move_dead --source` on pin 1 reports 17 dead of its 105 declarations):
    `repZ_of_lt` `:31`, `repZ_last` `:35`, `coe_finComponent` `:46`,
    `glEq_of_forall_finComponent_eq` `:56`, `commute_of_finComponent_eq_one` `:65`,
    `mapMatrix_injective` `:78`, `exists_glMap_eq` `:84`, `exists_finComponent_eq_padicGL_map` `:105`,
    `ι` `:149`, `ι_mem_padicK1_zero` `:152`, `coe_ι` `:155`, `sum_slash_map_repQ` `:550`,
    `padicPlace_ne_of_ne'` `:903` (all pin 1).
  - `det_mapGL_mul` (pin 1 `:989`): the prelude declares its own private copy
    (`WeightOneLiftLevel:908`) for `apply_mul_finEmbed_eq_of_mem_finiteLevelOne`, so this is a
    duplicate of a declaration that lives in the prelude.
  - `det_val_mapGL` (pin 2 `:727`) and `isLift1_weightOneLift` (pin 2 `:873`): pin 2's `Ψ`-general
    interface. They are dead here only because the port took pin 1 `:1084`'s specialized
    `sum_apply_eq_slash`, so nothing consumes `IsLift1`. `IsLift1` itself (pin 2 `:715`) is **kept**:
    `move_dead` treats a structure as API, and the statement is the pin's.
-/

import FLTForHuman.LanglandsTunnell.WeightOneLiftLevel
import FLTForHuman.LanglandsTunnell.WeightOneLiftAdelic
import FLTForHuman.LanglandsTunnell.WeightOneLiftGlobalPoints
import FLTForHuman.ModularForms.HeckeDiagDegeneracy

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm UpperHalfPlane
open UpperHalfPlane Matrix
open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel Matrix
open Matrix Matrix.GeneralLinearGroup
open CongruenceSubgroup ModularGroup
open AdelicDock
open NumberField.AdelicHaar
open HeckeIntegralSeam HeckePair
open AutomorphicForm.SmoothCusp IsDedekindDomain.HeightOneSpectrum
open LanglandsTunnell.RatArch

open NumberField.AdelicLevel AutomorphicForm.WindowedSiegel NumberField.AdelicVolume
open MeasureTheory
open scoped Topology Manifold
open DihedralWeightOne

namespace DihedralWeightOne

section

variable (p : ℕ) [hp : Fact p.Prime]
variable (p : ℕ) [hp : Fact p.Prime]
variable (p : ℕ) [hp : Fact p.Prime]
variable (p : ℕ) [hp : Fact p.Prime]
variable (p : ℕ) [hp : Fact p.Prime]
variable (p : ℕ) [hp : Fact p.Prime]
variable (p : ℕ) [hp : Fact p.Prime]
variable {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}

private theorem eq_of_forall_slash_apply_I {F G : UpperHalfPlane → ℂ} (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ h = 1 → LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
      (F ∣[(1 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I
        = (G ∣[(1 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I) :
    F = G := by
  refine Continuous.ext_on dense_ratPoints hF hG ?_
  rintro z ⟨hx, hy⟩
  obtain ⟨h, hfin, hpos, hz⟩ := exists_glFin_eq_one_and_smul_I_eq z hx hy
  have hdet : (0 : ℝ) < (LanglandsTunnell.ratArchGL2 h).det.val := (Matrix.mem_glpos _).mp hpos
  have key := hFG h hfin hpos
  rw [ModularForm.slash_apply, ModularForm.slash_apply, σ_apply_of_det_pos hdet, σ_apply_of_det_pos hdet, hz]
    at key
  have hne : |(LanglandsTunnell.ratArchGL2 h).det.val| ^ ((1 : ℤ) - 1)
      * UpperHalfPlane.denom (LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I ^ (-(1 : ℤ)) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast zpow_ne_zero _ (abs_ne_zero.mpr hdet.ne'))
      (zpow_ne_zero _ (UpperHalfPlane.denom_ne_zero _ _))
  rw [mul_assoc, mul_assoc] at key
  exact mul_right_cancel₀ hne key

end

section

variable (p : ℕ) [hp : Fact p.Prime]
variable (p : ℕ) [hp : Fact p.Prime]
variable (p : ℕ) [hp : Fact p.Prime]
variable (p : ℕ) [hp : Fact p.Prime]
variable (p : ℕ) [hp : Fact p.Prime]
variable (p : ℕ) [hp : Fact p.Prime]
variable (p : ℕ) [hp : Fact p.Prime]
variable {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
variable {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
variable (p : ℕ) [hp : Fact p.Prime]
variable {N : ℕ} {ε : DirichletCharacter ℂ N} {F : CuspForm (CongruenceSubgroup.Gamma1 N) 1}

private theorem lift_dictionary [NeZero N] :
    (∀ (γ : GL (Fin 2) ℚ) (x : AdelicGL2 (𝓞 ℚ) ℚ), weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑F) (globalPoints (𝓞 ℚ) ℚ γ * x) = weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑F) x) ∧
    (∀ u ∈ finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel N), ∀ x : AdelicGL2 (𝓞 ℚ) ℚ,
        weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑F) (x * AdelicDock.finEmbed (𝓞 ℚ) ℚ u) = weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑F) x) ∧
    ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ h = 1 →
      LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
        weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑F) h = weightOneArchLift (⇑F) (LanglandsTunnell.ratArchGL2 h) :=
  DihedralWeightOne.weightOneLift_globalPoints_mul_and_mul_finEmbed_and_eq_weightOneArchLift (NeZero.ne N) (⇑F)
    (fun γ hγ => SlashInvariantForm.slash_action_eqn F _ (Subgroup.mem_map.mpr ⟨γ, hγ, rfl⟩))

private theorem continuous_heckeSide (c : ℂ) :
    Continuous (c • ModularForm.heckeU 1 p ⇑F + (⇑F) ∣[(1 : ℤ)] ModularForm.heckeDiagMatrix p) := by
  have _ := hp
  have hF : Continuous (⇑F : UpperHalfPlane → ℂ) := (CuspFormClass.holo F).continuous
  refine Continuous.add ?_ (continuous_slash hF 1 _)
  refine Continuous.const_smul ?_ c
  rw [ModularForm.heckeU_def]
  have h : (∑ j ∈ Finset.range p, (⇑F) ∣[(1 : ℤ)] ModularForm.heckeMatrix p j)
      = fun τ => ∑ j ∈ Finset.range p, ((⇑F) ∣[(1 : ℤ)] ModularForm.heckeMatrix p j) τ := by
    funext τ; exact Finset.sum_apply τ _ _
  rw [h]
  exact continuous_finsetSum _ fun j _ => continuous_slash hF 1 _

end

section

variable (p : ℕ) [hp : Fact p.Prime]
variable (p : ℕ) [hp : Fact p.Prime]
variable (p : ℕ) [hp : Fact p.Prime]
variable (p : ℕ) [hp : Fact p.Prime]
variable (p : ℕ) [hp : Fact p.Prime]
variable (p : ℕ) [hp : Fact p.Prime]
variable (p : ℕ) [hp : Fact p.Prime]
variable {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
variable {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}

private theorem one_mem_strictPeriods_gamma1 (L : ℕ) :
    (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma1 L : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
      Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]
  exact AddSubgroup.mem_zmultiples 1

end

section

variable (p : ℕ) [hp : Fact p.Prime]
variable (p : ℕ) [hp : Fact p.Prime]
variable (p : ℕ) [hp : Fact p.Prime]
variable (p : ℕ) [hp : Fact p.Prime]
variable (p : ℕ) [hp : Fact p.Prime]
variable (p : ℕ) [hp : Fact p.Prime]
variable (p : ℕ) [hp : Fact p.Prime]
variable (p : ℕ) [hp : Fact p.Prime]
variable {N : ℕ} {ε : DirichletCharacter ℂ N} {F : CuspForm (CongruenceSubgroup.Gamma1 N) 1}
variable {Ψ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}

private structure IsLift1 (F : CuspForm (CongruenceSubgroup.Gamma1 N) 1) (Ψ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) : Prop where
  left_inv : ∀ (γ : GL (Fin 2) ℚ) (x : AdelicGL2 (𝓞 ℚ) ℚ), Ψ (globalPoints (𝓞 ℚ) ℚ γ * x) = Ψ x
  level_inv : ∀ u ∈ finiteLevelOne (𝓞 ℚ) ℚ (ratLevel N), ∀ x : AdelicGL2 (𝓞 ℚ) ℚ,
    Ψ (x * finEmbed (𝓞 ℚ) ℚ u) = Ψ x
  apply_eq : ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ h = 1 →
    LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
      Ψ h = DihedralWeightOne.weightOneArchLift (⇑F) (LanglandsTunnell.ratArchGL2 h)

end

theorem qCoeff_hecke_eq_of_hasNebentypus_of_sum_weightOneLift_mul_padicToAdelic_inv_eq
    {N : ℕ} [NeZero N] {ε : DirichletCharacter ℂ N} {F : CuspForm (CongruenceSubgroup.Gamma1 N) 1}
    (hε : CuspForm.HasNebentypus ε F)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (ρ : Fin (ℓ + 1) → GL (Fin 2) ℚ_[ℓ])
    (hρ : ∀ i : Fin (ℓ + 1), ((ρ i : GL (Fin 2) ℚ_[ℓ]) : Matrix (Fin 2) (Fin 2) ℚ_[ℓ]) =
      if (i : ℕ) < ℓ then !![(1 : ℚ_[ℓ]), ((i : ℕ) : ℚ_[ℓ]); 0, (ℓ : ℚ_[ℓ])]
      else !![(ℓ : ℚ_[ℓ]), 0; 0, 1])
    (lam : ℂ)
    (heig : ∀ x : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ x = 1 →
      LanglandsTunnell.ratArchGL2 x ∈ Matrix.GLPos (Fin 2) ℝ →
        ∑ i : Fin (ℓ + 1), weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑F) (x * AdelicDock.padicToAdelic ℓ (ρ i)⁻¹) =
          lam * weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑F) x)
    (n : ℕ) :
    ModularFormClass.qCoeff F (ℓ * n) +
        ε (ℓ : ZMod N) * (ℓ : ℂ) ^ ((1 : ℤ) - 1) *
          (if ℓ ∣ n then ModularFormClass.qCoeff F (n / ℓ) else 0) =
      ε (ℓ : ZMod N) * (ℓ : ℂ)⁻¹ * lam * ModularFormClass.qCoeff F n := by
  have hℓ : ℓ.Prime := Fact.out
  have hℓ0 : ℓ ≠ 0 := hℓ.ne_zero
  have hℓC : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ0
  have hcop : ℓ.Coprime N := (Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓN
  set eℓ : ℂ := ε (ℓ : ZMod N) with heℓ
  have heℓ0 : eℓ ≠ 0 := by
    rw [heℓ, ← ZMod.coe_unitOfCoprime ℓ hcop, ← MulChar.coe_toUnitHom]
    exact Units.ne_zero _
  obtain ⟨-, -, happly⟩ := lift_dictionary (F := F)

  have hF : Continuous (⇑F : UpperHalfPlane → ℂ) := (CuspFormClass.holo F).continuous
  have hfun : eℓ⁻¹ • ModularForm.heckeU 1 ℓ ⇑F + (⇑F) ∣[(1 : ℤ)] ModularForm.heckeDiagMatrix ℓ
      = (lam * (ℓ : ℂ)⁻¹) • ⇑F := by
    refine eq_of_forall_slash_apply_I (continuous_heckeSide ℓ _) (hF.const_smul (lam * (ℓ : ℂ)⁻¹)) fun h hh hpos => ?_
    have hdet : (0 : ℝ) < (LanglandsTunnell.ratArchGL2 h).det.val := (Matrix.mem_glpos _).mp hpos
    have hD : ((ℓ : ℂ) * (((LanglandsTunnell.ratArchGL2 h).det.val : ℝ) : ℂ)) ≠ 0 :=
      mul_ne_zero hℓC (Complex.ofReal_ne_zero.mpr hdet.ne')
    have key := heig h hh hpos
    rw [Finset.sum_congr rfl (fun i _ => by rw [eq_ρQ_of_coe_eq ℓ ρ hρ i]), sum_apply_eq_slash ℓ hε hℓN hh hpos,
      happly h hh hpos, weightOneArchLift_eq] at key
    rw [ModularForm.smul_slash, Pi.smul_apply, smul_eq_mul, σ_apply_of_det_pos hdet]
    apply mul_right_cancel₀ hD
    rw [key]
    field_simp

  have : NeZero (N * ℓ) := ⟨mul_ne_zero (NeZero.ne N) hℓ0⟩
  obtain ⟨G₁, hG₁, hG₁q, -⟩ := CuspForm.exists_degeneracy_gamma1_hasNebentypus (M := N) (N := N * ℓ) (d := 1)
    (by rw [mul_one]; exact Dvd.intro _ rfl) F
  obtain ⟨Gℓ, hGℓ, hGℓq, -⟩ := CuspForm.exists_degeneracy_gamma1_hasNebentypus (M := N) (N := N * ℓ) (d := ℓ)
    dvd_rfl F
  have hFG₁ : (⇑F : UpperHalfPlane → ℂ) = ⇑G₁ := by
    funext τ
    rw [hG₁ τ]
    congr 1
    apply UpperHalfPlane.ext
    rw [ModularForm.coe_heckeDiagMatrix_smul one_ne_zero]
    simp
  have hFGℓ : (⇑F) ∣[(1 : ℤ)] ModularForm.heckeDiagMatrix ℓ = ⇑Gℓ := by
    funext τ
    rw [ModularForm.slash_heckeDiagMatrix_apply 1 hℓ0, hGℓ τ]
    norm_num

  have hU : ModularForm.heckeU 1 ℓ ⇑F = ⇑(eℓ • ((lam * (ℓ : ℂ)⁻¹) • G₁ - Gℓ)) := by
    have h1 : ModularForm.heckeU 1 ℓ ⇑F
        = eℓ • ((lam * (ℓ : ℂ)⁻¹) • ⇑F - (⇑F) ∣[(1 : ℤ)] ModularForm.heckeDiagMatrix ℓ) := by
      rw [smul_sub, ← hfun, smul_add, ← mul_smul, mul_inv_cancel₀ heℓ0, one_smul, add_sub_cancel_right]
    rw [h1, hFGℓ, FunLike.coe_smul, FunLike.coe_sub, FunLike.coe_smul, ← hFG₁]

  have hΓ := one_mem_strictPeriods_gamma1 N
  have hΓ' := one_mem_strictPeriods_gamma1 (N * ℓ)
  have hcoefU : ModularFormClass.qCoeff (ModularForm.heckeU 1 ℓ ⇑F) n = ModularFormClass.qCoeff F (n * ℓ) := by
    rw [ModularFormClass.qCoeff_heckeU F hΓ hℓ0 n, ModularForm.coeffHeckeU_apply]
  have hcoefH : ModularFormClass.qCoeff (⇑(eℓ • ((lam * (ℓ : ℂ)⁻¹) • G₁ - Gℓ))) n
      = eℓ * ((lam * (ℓ : ℂ)⁻¹) * ModularFormClass.qCoeff G₁ n - ModularFormClass.qCoeff Gℓ n) := by
    simp only [ModularFormClass.qCoeff]
    rw [FunLike.coe_smul, ModularForm.qExpansion_smul one_pos hΓ' eℓ ((lam * (ℓ : ℂ)⁻¹) • G₁ - Gℓ),
      map_smul, smul_eq_mul, FunLike.coe_sub, ModularForm.qExpansion_sub one_pos hΓ' ((lam * (ℓ : ℂ)⁻¹) • G₁) Gℓ,
      map_sub, FunLike.coe_smul, ModularForm.qExpansion_smul one_pos hΓ' (lam * (ℓ : ℂ)⁻¹) G₁, map_smul,
      smul_eq_mul]
  have hG₁n : ModularFormClass.qCoeff G₁ n = ModularFormClass.qCoeff F n := by
    rw [hG₁q n, ite_eq_left (one_dvd n), Nat.div_one]
  have hmain : ModularFormClass.qCoeff F (n * ℓ)
      = eℓ * ((lam * (ℓ : ℂ)⁻¹) * ModularFormClass.qCoeff F n
          - (if ℓ ∣ n then ModularFormClass.qCoeff F (n / ℓ) else 0)) := by
    rw [← hcoefU, hU, hcoefH, hG₁n, hGℓq n]
  rw [mul_comm ℓ n, hmain, show ((1 : ℤ) - 1) = 0 by norm_num, zpow_zero]
  ring

theorem sum_weightOneLift_mul_padicToAdelic_inv_eq_mul_slash_apply_I_mul_det
    {N : ℕ} [NeZero N] {ε : DirichletCharacter ℂ N} {F : CuspForm (CongruenceSubgroup.Gamma1 N) 1}
    (hε : CuspForm.HasNebentypus ε F)
    (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (ρ : Fin (p + 1) → GL (Fin 2) ℚ_[p])
    (hρ : ∀ i : Fin (p + 1), ((ρ i : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) =
      if (i : ℕ) < p then !![(1 : ℚ_[p]), ((i : ℕ) : ℚ_[p]); 0, (p : ℚ_[p])]
      else !![(p : ℚ_[p]), 0; 0, 1])
    {h : AdelicGL2 (𝓞 ℚ) ℚ}
    (hh : glFin (𝓞 ℚ) ℚ h = 1)
    (hpos : LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ) :
    ∑ i : Fin (p + 1), weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑F) (h * AdelicDock.padicToAdelic p (ρ i)⁻¹) =
      (p : ℂ) *
        ((((ε (p : ZMod N))⁻¹ • ModularForm.heckeU 1 p ⇑F +
              (⇑F) ∣[(1 : ℤ)] ModularForm.heckeDiagMatrix p) ∣[(1 : ℤ)]
            LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I *
          (((LanglandsTunnell.ratArchGL2 h).det.val : ℝ) : ℂ)) := by
  have hcongr : (∑ i : Fin (p + 1),
        weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑F) (h * AdelicDock.padicToAdelic p (ρ i)⁻¹))
      = ∑ i : Fin (p + 1),
          weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑F) (h * AdelicDock.padicToAdelic p (ρQ p i)⁻¹) :=
    Finset.sum_congr rfl fun i _ => by rw [eq_ρQ_of_coe_eq p ρ hρ i]
  rw [hcongr, sum_apply_eq_slash p hε hpN hh hpos]
  ring

end DihedralWeightOne

end
