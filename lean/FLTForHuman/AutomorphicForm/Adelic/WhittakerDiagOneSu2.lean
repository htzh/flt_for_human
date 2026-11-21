/-
  The `diagOne` expansion of a complex-place su(2)-string family.

  For a `Fin (n + 1)` family `x` of archimedean-smooth functions at a complex place `w`, which is
  invariant under the rational points, transforms under the centre by a character `ξ` of weight
  `w₀`, is a union of circle-weight vectors, obeys the two circle actions by `E₁`, `E₂`, and is an
  eigenfamily of the two Casimir operators, every Whittaker coefficient of `x` at a diagonal point is
  a *fixed* multiple of its value at `diagOne`: the expansion

    `W x_p (g₀ * archComplexGLAt hw (h * a)) = χ(a) · W x_p (g₀ * archComplexGLAt hw h)`

  for the circle-weight factor `χ`, uniformly in the place of `p` in the string.

  The input is the su(2)-string Whittaker system of the coefficient at a complex place (each
  `x p` is one string position), and the output is the `diagOne` dictionary the cuspidal-constituent
  analysis reads: the value at an arbitrary diagonal point is the value at `diagOne` times the
  weight character, with no further dependence on the torus.

  spec-pin: P2M/Sol/S_AutomorphicForm_exists_forall_whittakerCoefficient_diagOne_eq_mul_of_isComplex_of_su2String.lean

  ## Shape

  One row from one 473-line pin (28 declarations, **none** private). **22 of the 27** helper rows are
  already in the port and are imported, not re-proved: `AutomorphicForm.DCFN`
  (`AutomorphicForm/Adelic/WhittakerDiagOne.lean`) carries `eC`, `iotaW`, `bprime`, `g0`, `W`,
  `Fstr`/`DFstr`/`DDstr`/`fstr`, `bprime_fst_self`/`_fst_of_ne`/`_snd`, `glInf_ext`,
  `archComplexGLAt_mul_comm_of_archComponent_eq_one`, `archComponent_glArch_g0`, `det_diagOne`,
  `ideleNorm_eq_norm_pow_mul_of_eq_off`, `exists_norm_W_diagOne_le_norm_rpow_of_gr`,
  `mult_eq_two_of_isComplex`, `norm_eC`, `norm_eC_symm` and `rpow_eq_rpow_mult`, each byte-identical
  to its pin row (`statement_db` `nhash`, measured). What is transcribed here is the residue of five,
  in the pin's own proof-block namespace with the pipeline number dropped (`UCplxFn35` → `UCplxFn`):
  the two combinatorial dependence lemmas, `fstr_eq`, `fstr_system` and the twisted growth row
  `exists_norm_fstr_le_of_twist` — the last three are the `fstr` rows the pin states on top of the
  complex system, so they cannot live beside their `DCFN` siblings (FR-0280's shape).

  **Why a separate module.** The natural home of the row's subject is `WhittakerDiagOne.lean`, but
  `fstr_system` needs the *complex* Whittaker system, which is `WhittakerSystem.lean`, which imports
  `WhittakerDiagOne.lean`. The import direction is not negotiable, so the residue sits here, above
  both; `WhittakerDiagOne.lean` itself gains nothing and is not touched.

  ## Drift (mathlib `v4.34.0`)

  Statements are the pin's, frozen. Proof deltas, all forced:

  * `dif_pos` is deprecated in favour of `dite_eq_left` (`fstr_eq`, pin `:288`).
  * `NumberField.InfinitePlace.Completion` is a *structure* here (a type synonym at the pin), so the
    pin's `show … Function.update (1 : InfiniteAdeleRing K) …` spells the pi type
    `(v : InfinitePlace K) → v.Completion` (`exists_norm_fstr_le_of_twist`, pin `:364`, `:370`,
    `:374`); `InfiniteAdeleRing` is a `def`, so the pin's spelling is not type-correct at `implicit`
    transparency (FR-0257/FR-0268).
  * The pin's `p2m_open` prelude is dropped and the pin's two names for the same dependence lemma are
    both transcribed: the unprimed one (`:33`, over a family `f : B → P → ℝ → ℂ`) and the primed one
    (`:249`, over `adm : B → A → Prop` and a projection `π`), which the headline uses.
  * `attribute [-ext] NumberField.InfinitePlace.Completion.ext` (pin `:15`) is already in the
    environment from `WhittakerDiagOne.lean`; not repeated.

  ## Heartbeat probe (never installed, FR-0225)

  A scratch copy of this module carrying `set_option maxHeartbeats 10000` after
  `set_option autoImplicit false` is silent; at `5000` exactly two declarations time out —
  `fstr_system` (at its `gl2Complex_whittaker_system_…` step) and the row itself (at the final
  `exists_forall_exists_eq_mul_of_twist_of_pairwise_dependent'` application) — and nothing else does.
  So every declaration costs under 10 k heartbeats and only those two exceed 5 k: a 1/400 margin on the
  lakefile's `4 000 000` cap and 1/20 on the `200 000` edit-loop default.
-/

import FLTForHuman.AutomorphicForm.Adelic.WhittakerSystem
import FLTForHuman.AutomorphicForm.Adelic.WhittakerDiagOne
import FLTForHuman.AutomorphicForm.Adelic.ArchWhittaker
import FLTForHuman.LanglandsTunnell.WhittakerODELinearDependence
import FLTForHuman.NumberTheory.NumberField.TateGlobal.IdeleNormValues

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain

open scoped Classical

namespace AutomorphicForm

open AutomorphicForm.DCFN

namespace UCplxFn

/-! ## The dependence core (pin `UCplxFn35`:33, `:249`)

Two statements of "a family that is a twist of a one-parameter family is a fixed multiple of one
member": the second is the first with the parameter read through a projection `π`. Both are the
pin's, including the case split on whether the family vanishes identically. -/

theorem exists_forall_exists_eq_mul_of_twist_of_pairwise_dependent
    {B P T : Type} (good : B → Prop) (adm : T → Prop) (r : T → ℝ) (hr : ∀ t, adm t → 0 < r t)
    (Tfun : B → P → T → ℂ) (f : B → P → ℝ → ℂ) (μ : P → T → ℂ)
    (htw : ∀ b, good b → ∀ p t, adm t → Tfun b p t = μ p t * f b p (r t))
    (hdep : ∀ b b', good b → good b' →
      ∃ c : ℂ × ℂ, c ≠ 0 ∧ ∀ p (y : ℝ), 0 < y → c.1 * f b p y + c.2 * f b' p y = 0) :
    ∃ φ : P → T → ℂ, ∀ b, good b → ∃ cb : ℂ, ∀ p t, adm t → Tfun b p t = cb * φ p t := by
  classical
  by_cases hex : ∃ b₀, good b₀ ∧ ∃ p, ∃ y : ℝ, 0 < y ∧ f b₀ p y ≠ 0
  · obtain ⟨b₀, hb₀, p₀, y₀, hy₀, hne⟩ := hex
    refine ⟨fun p t => μ p t * f b₀ p (r t), fun b hb => ?_⟩
    obtain ⟨c, hc, hrel⟩ := hdep b b₀ hb hb₀
    have hc1 : c.1 ≠ 0 := by
      intro h1
      have h2 : c.2 ≠ 0 := fun h2 => hc (Prod.ext h1 h2)
      have := hrel p₀ y₀ hy₀
      rw [h1, zero_mul, zero_add] at this
      exact hne ((mul_eq_zero.mp this).resolve_left h2)
    refine ⟨-(c.2 / c.1), fun p t ht => ?_⟩
    have key := hrel p (r t) (hr t ht)
    have hf : f b p (r t) = -(c.2 / c.1) * f b₀ p (r t) := by
      field_simp
      linear_combination key
    rw [htw b hb p t ht, hf]
    ring
  · push Not at hex
    refine ⟨fun _ _ => 0, fun b hb => ⟨0, fun p t ht => ?_⟩⟩
    rw [htw b hb p t ht, hex b hb p (r t) (hr t ht)]
    simp

open NumberField.TateGlobal NumberField.AdeleRing NumberField.InfinitePlace.Completion

variable {K : Type} [Field K] [NumberField K]

omit [Field K] [NumberField K] in
theorem exists_forall_exists_eq_mul_of_twist_of_pairwise_dependent'
    {B P A T : Type} (good : B → Prop) (adm : B → A → Prop) (π : A → T) (r : T → ℝ)
    (hr : ∀ b a, adm b a → 0 < r (π a))
    (Tfun : P → A → ℂ) (f : B → P → ℝ → ℂ) (μ : P → T → ℂ)
    (htw : ∀ b, good b → ∀ p a, adm b a → Tfun p a = μ p (π a) * f b p (r (π a)))
    (hdep : ∀ b b', good b → good b' →
      ∃ c : ℂ × ℂ, c ≠ 0 ∧ ∀ p (y : ℝ), 0 < y → c.1 * f b p y + c.2 * f b' p y = 0) :
    ∃ φ : P → T → ℂ, ∀ b, good b → ∃ cb : ℂ, ∀ p a, adm b a → Tfun p a = cb * φ p (π a) := by
  classical
  by_cases hex : ∃ b₀, good b₀ ∧ ∃ p, ∃ y : ℝ, 0 < y ∧ f b₀ p y ≠ 0
  · obtain ⟨b₀, hb₀, p₀, y₀, hy₀, hne⟩ := hex
    refine ⟨fun p t => μ p t * f b₀ p (r t), fun b hb => ?_⟩
    obtain ⟨c, hc, hrel⟩ := hdep b b₀ hb hb₀
    have hc1 : c.1 ≠ 0 := by
      intro h1
      have h2 : c.2 ≠ 0 := fun h2 => hc (Prod.ext h1 h2)
      have := hrel p₀ y₀ hy₀
      rw [h1, zero_mul, zero_add] at this
      exact hne ((mul_eq_zero.mp this).resolve_left h2)
    refine ⟨-(c.2 / c.1), fun p a ha => ?_⟩
    have key := hrel p (r (π a)) (hr b a ha)
    have hf : f b p (r (π a)) = -(c.2 / c.1) * f b₀ p (r (π a)) := by
      field_simp
      linear_combination key
    rw [htw b hb p a ha, hf]
    ring
  · push Not at hex
    refine ⟨fun _ _ => 0, fun b hb => ⟨0, fun p a ha => ?_⟩⟩
    rw [htw b hb p a ha, hex b hb p (r (π a)) (hr b a ha)]
    simp

variable (K)

/-! ## The `fstr` profile in the pin's coordinates (pin `:280`, `:291`, `:332`) -/

theorem fstr_eq (D : Set (AdelicGL2 (𝓞 K) K)) {w : InfinitePlace K} (hw : w.IsComplex) (b : (AdeleRing (𝓞 K) K)ˣ)
    {n : ℕ} (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ)) (p : Fin (n + 1)) (y : ℝ) :
    fstr D hw b x p y =
      whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1
        (diagOne (b * (NumberField.TateGlobal.archUnitHom w (NumberField.AdeleRing.infiniteUnitsComponent (𝓞 K) K w b))⁻¹) *
          archComplexGLAt hw (splitTorusGL2Complex ((Real.log y / 2 : ℝ) : ℂ))) := by
  simp only [fstr, dite_eq_left p.isLt, Fstr, Fin.eta]
  rfl

theorem fstr_system (D : Set (AdelicGL2 (𝓞 K) K)) (w : InfinitePlace K) (hw : w.IsComplex)
    (n : ℕ) (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ))
    (hxc : ∀ p, Continuous (x p))
    (hxG : ∀ p (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x p (globalPoints (𝓞 K) K γ * g) = x p g)
    (hreg : ∀ p (l : List ArchDirComplex),
      IsArchSmoothAtComplex hw (l.foldr (archDerivAtComplex hw) (x p)) ∧ Continuous (l.foldr (archDerivAtComplex hw) (x p)))
    (hwt : ∀ p : Fin (n + 1), HasCircleWeightAt hw ((n : ℤ) - 2 * (p : ℕ)) (x p))
    (E₁ E₂ : ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hE₁ : E₁ 0 = 1) (hE₂ : E₂ 0 = 1)
    (hE₁' : ∀ i j : Fin (n + 1), HasDerivAt (fun s : ℝ => E₁ s i j)
      (if (i : ℕ) = j + 1 then 1 else if (j : ℕ) = i + 1 then -((j : ℂ) * ((n : ℂ) + 1 - j)) else 0) 0)
    (hE₂' : ∀ i j : Fin (n + 1), HasDerivAt (fun s : ℝ => E₂ s i j)
      (if (i : ℕ) = j + 1 then Complex.I else if (j : ℕ) = i + 1 then Complex.I * ((j : ℂ) * ((n : ℂ) + 1 - j)) else 0) 0)
    (hK₁ : ∀ (p : Fin (n + 1)) (s : ℝ) (g : AdelicGL2 (𝓞 K) K),
      x p (g * archComplexLiftAt hw !![(Real.cos s : ℂ), -(Real.sin s : ℂ); (Real.sin s : ℂ), (Real.cos s : ℂ)]) = ∑ p' : Fin (n + 1), E₁ s p' p * x p' g)
    (hK₂ : ∀ (p : Fin (n + 1)) (s : ℝ) (g : AdelicGL2 (𝓞 K) K),
      x p (g * archComplexLiftAt hw !![(Real.cos s : ℂ), (Real.sin s : ℂ) * Complex.I; (Real.sin s : ℂ) * Complex.I, (Real.cos s : ℂ)]) = ∑ p' : Fin (n + 1), E₂ s p' p * x p' g)
    (lam lam' : ℂ)
    (hcas : ∀ p, archCasimirAtComplex hw (x p) = lam • x p ∧ archCasimirBarAtComplex hw (x p) = lam' • x p)
    (b : (AdeleRing (𝓞 K) K)ˣ) :
    ∀ p : Fin (n + 1),
      DifferentiableOn ℝ (fstr D hw b x p) (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv (fstr D hw b x p)) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        ((y : ℂ) ^ 2 * deriv (deriv (fstr D hw b x p)) y + (((n : ℂ) - 2 * (p : ℕ)) - 1) * (y : ℂ) * deriv (fstr D hw b x p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) - 4) / 4 + 4 * lam -
                16 * (Real.pi : ℂ) ^ 2 * ((‖(1 : ℂ)‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * fstr D hw b x p y +
            8 * (Real.pi : ℂ) * Complex.I * 1 * (y : ℂ) * fstr D hw b x ((p : ℕ) + 1) y = 0) ∧
        ((y : ℂ) ^ 2 * deriv (deriv (fstr D hw b x p)) y - (((n : ℂ) - 2 * (p : ℕ)) + 1) * (y : ℂ) * deriv (fstr D hw b x p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) + 4) / 4 + 4 * lam' -
                16 * (Real.pi : ℂ) ^ 2 * ((‖(1 : ℂ)‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * fstr D hw b x p y -
            8 * (Real.pi : ℂ) * Complex.I * (starRingEnd ℂ) 1 * ((p : ℕ) * ((n : ℂ) + 1 - (p : ℕ))) * (y : ℂ) *
              fstr D hw b x ((p : ℕ) - 1) y = 0) := by
  have hg0 : archComponent K w (glArch (𝓞 K) K (g0 w b)) = 1 := archComponent_glArch_g0 K w b
  obtain ⟨hD, hDD, hΩ, hΩ', hN, hM, hK1, hK2⟩ :=
    AutomorphicForm.whittakerCoefficient_su2String_gl2Complex_whittaker_system_hypotheses K D w hw (g0 w b) hg0 n x hxc hxG
      hreg hwt E₁ E₂ hK₁ hK₂ lam lam' hcas
  exact AutomorphicForm.gl2Complex_whittaker_system_of_casimir_pair_of_unipotent_covariant_of_circleWeight_of_ktype n
    (fun p h => W D (x p) (g0 w b * archComplexGLAt hw h)) 1 lam lam'
    (fun p d h => W D (archDerivAtComplex hw d (x p)) (g0 w b * archComplexGLAt hw h))
    (fun p d' d h => W D (archDerivAtComplex hw d' (archDerivAtComplex hw d (x p))) (g0 w b * archComplexGLAt hw h))
    hD hDD hΩ hΩ' hN hM E₁ E₂ hE₁ hE₂ hE₁' hE₂' hK1 hK2

theorem exists_norm_fstr_le_of_twist (D : Set (AdelicGL2 (𝓞 K) K)) (w₀ : ℝ)
    (w : InfinitePlace K) (hw : w.IsComplex)
    (n : ℕ) (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ))
    (hgr : ∀ p, ∃ C₀ : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (x p) 1 g‖ ≤ C₀ * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2))
    (μ : Fin (n + 1) → w.Completion → ℂ)
    (hμn : ∀ (p : Fin (n + 1)) (t : w.Completion), ‖μ p t‖ = ‖t‖ ^ ((w.mult : ℝ) * w₀ / 2))
    (b : (AdeleRing (𝓞 K) K)ˣ) (hb : ((b : AdeleRing (𝓞 K) K)).2 = 1)
    (hμ : ∀ (p : Fin (n + 1)) (a : (AdeleRing (𝓞 K) K)ˣ), ((a : AdeleRing (𝓞 K) K)).2 = 1 →
          (∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w') →
          whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (diagOne a) =
            μ p (((a : AdeleRing (𝓞 K) K)).1 w) * fstr D hw b x p ‖((a : AdeleRing (𝓞 K) K)).1 w‖) :
    ∃ C : ℝ, ∀ (p : Fin (n + 1)) (y : ℝ), 0 < y → ‖fstr D hw b x p y‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_W_diagOne_le_norm_rpow_of_gr K D w₀ w x hgr b
  refine ⟨C, fun p y hy => ?_⟩

  have hy0 : (eC hw).symm (y : ℂ) ≠ 0 := by
    intro h0
    have := congrArg (eC hw) h0
    rw [RingEquiv.apply_symm_apply, map_zero] at this
    exact hy.ne' (by exact_mod_cast this)
  set cy : (w.Completion)ˣ := Units.mk0 ((eC hw).symm (y : ℂ)) hy0 with hcy
  set a : (AdeleRing (𝓞 K) K)ˣ := bprime w b * archUnitHom w cy with hadef
  have ha2 : ((a : AdeleRing (𝓞 K) K)).2 = 1 := by
    show ((bprime w b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 * ((archUnitHom w cy : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 = 1
    rw [bprime_snd, hb, archUnitHom_apply, one_mul]; rfl
  have haw : ((a : AdeleRing (𝓞 K) K)).1 w = (eC hw).symm (y : ℂ) := by
    show ((bprime w b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w * ((archUnitHom w cy : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w = _
    rw [bprime_fst_self, one_mul, archUnitHom_apply]
    show Function.update (1 : (v : InfinitePlace K) → v.Completion) w (cy : w.Completion) w = _
    rw [Function.update_self]; rfl
  have hab : ∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w' := by
    intro w' hw'
    show ((bprime w b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w' * ((archUnitHom w cy : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w' = _
    rw [bprime_fst_of_ne hw', archUnitHom_apply]
    show _ * Function.update (1 : (v : InfinitePlace K) → v.Completion) w (cy : w.Completion) w' = _
    rw [Function.update_of_ne hw']; exact mul_one _
  have hnorm : ‖((a : AdeleRing (𝓞 K) K)).1 w‖ = y := by
    rw [haw, norm_eC_symm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy]
  have h7 := hμ p a ha2 hab
  have h8 := hC p a ha2 hab
  rw [h7, norm_mul, hμn, hnorm] at h8

  have hyw : 0 < y ^ ((w.mult : ℝ) * w₀ / 2) := Real.rpow_pos_of_pos hy _
  rw [mul_comm C] at h8
  exact le_of_mul_le_mul_left h8 hyw

end UCplxFn

/-! ## The row (pin `:385`)

Every `diagOne` value of the string family's coefficient is a fixed multiple of its value at the base
point: `fstr_system` turns each member of the string into a solution of the complex Whittaker system,
`exists_norm_fstr_le_of_twist` bounds it polynomially, the string dependence theorem makes two members
linearly dependent, and the `diagOne`/twist dictionary (`exists_…_of_hasCircleWeightAt`, `fstr_eq`)
reads the dependence back at an arbitrary diagonal point. -/

open UCplxFn NumberField.TateGlobal NumberField.AdeleRing NumberField.InfinitePlace.Completion in
theorem exists_forall_whittakerCoefficient_diagOne_eq_mul_of_isComplex_of_su2String
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (ξ : (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (w : InfinitePlace K) (hw : w.IsComplex)
    (n : ℕ) (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ))
    (hxc : ∀ p, Continuous (x p))
    (hxG : ∀ p (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x p (globalPoints (𝓞 K) K γ * g) = x p g)
    (hxZ : ∀ p (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      x p (centralScalar (𝓞 K) K z * g) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x p g)
    (hreg : ∀ p (l : List ArchDirComplex),
      IsArchSmoothAtComplex hw (l.foldr (archDerivAtComplex hw) (x p)) ∧ Continuous (l.foldr (archDerivAtComplex hw) (x p)))
    (hwt : ∀ p : Fin (n + 1), HasCircleWeightAt hw ((n : ℤ) - 2 * (p : ℕ)) (x p))
    (E₁ E₂ : ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hE₁ : E₁ 0 = 1) (hE₂ : E₂ 0 = 1)
    (hE₁' : ∀ i j : Fin (n + 1), HasDerivAt (fun s : ℝ => E₁ s i j)
      (if (i : ℕ) = j + 1 then 1 else if (j : ℕ) = i + 1 then -((j : ℂ) * ((n : ℂ) + 1 - j)) else 0) 0)
    (hE₂' : ∀ i j : Fin (n + 1), HasDerivAt (fun s : ℝ => E₂ s i j)
      (if (i : ℕ) = j + 1 then Complex.I else if (j : ℕ) = i + 1 then Complex.I * ((j : ℂ) * ((n : ℂ) + 1 - j)) else 0) 0)
    (hK₁ : ∀ (p : Fin (n + 1)) (s : ℝ) (g : AdelicGL2 (𝓞 K) K),
      x p (g * archComplexLiftAt hw !![(Real.cos s : ℂ), -(Real.sin s : ℂ); (Real.sin s : ℂ), (Real.cos s : ℂ)]) = ∑ p' : Fin (n + 1), E₁ s p' p * x p' g)
    (hK₂ : ∀ (p : Fin (n + 1)) (s : ℝ) (g : AdelicGL2 (𝓞 K) K),
      x p (g * archComplexLiftAt hw !![(Real.cos s : ℂ), (Real.sin s : ℂ) * Complex.I; (Real.sin s : ℂ) * Complex.I, (Real.cos s : ℂ)]) = ∑ p' : Fin (n + 1), E₂ s p' p * x p' g)
    (lam lam' : ℂ)
    (hcas : ∀ p, archCasimirAtComplex hw (x p) = lam • x p ∧ archCasimirBarAtComplex hw (x p) = lam' • x p)
    (hgr : ∀ p, ∃ C₀ : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (x p) 1 g‖ ≤ C₀ * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2)) :
    ∃ φ : Fin (n + 1) → w.Completion → ℂ,
      ∀ b : (AdeleRing (𝓞 K) K)ˣ, ((b : AdeleRing (𝓞 K) K)).2 = 1 → ∃ cb : ℂ, ∀ p : Fin (n + 1),
        ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
          (∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w') →
          whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (x p) 1
              (diagOne a) = cb * φ p (((a : AdeleRing (𝓞 K) K)).1 w)
  := by
  classical
  obtain ⟨μ, hμn, hμ⟩ :=
    AutomorphicForm.exists_whittakerCoefficient_diagOne_eq_mul_whittakerCoefficient_splitTorusGL2Complex_of_hasCircleWeightAt
      K D ξ w₀ hξ w hw n x hxZ hwt
  have hsys := fun b : (AdeleRing (𝓞 K) K)ˣ =>
    fstr_system K D w hw n x hxc hxG hreg hwt E₁ E₂ hE₁ hE₂ hE₁' hE₂' hK₁ hK₂ lam lam' hcas b

  have htw : ∀ b : (AdeleRing (𝓞 K) K)ˣ, ((b : AdeleRing (𝓞 K) K)).2 = 1 →
      ∀ (p : Fin (n + 1)) (a : (AdeleRing (𝓞 K) K)ˣ), ((a : AdeleRing (𝓞 K) K)).2 = 1 →
        (∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w') →
        whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (diagOne a) =
          μ p (((a : AdeleRing (𝓞 K) K)).1 w) * fstr D hw b x p ‖((a : AdeleRing (𝓞 K) K)).1 w‖ := by
    intro b hb p a ha hab
    rw [fstr_eq]
    exact hμ b hb p a ha hab

  have hgrow : ∀ b : (AdeleRing (𝓞 K) K)ˣ, ((b : AdeleRing (𝓞 K) K)).2 = 1 →
      ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖fstr D hw b x 0 y‖ ≤ C * y ^ N := by
    intro b hb
    obtain ⟨C, hC⟩ := exists_norm_fstr_le_of_twist K D w₀ w hw n x hgr μ hμn b hb (htw b hb)
    refine ⟨C, 0, fun y hy => ?_⟩
    rw [Real.rpow_zero, mul_one]
    exact hC 0 y (by linarith)

  have hdep : ∀ b b' : (AdeleRing (𝓞 K) K)ˣ, ((b : AdeleRing (𝓞 K) K)).2 = 1 → ((b' : AdeleRing (𝓞 K) K)).2 = 1 →
      ∃ c : ℂ × ℂ, c ≠ 0 ∧ ∀ (p : Fin (n + 1)) (y : ℝ), 0 < y →
        c.1 * fstr D hw b x p y + c.2 * fstr D hw b' x p y = 0 := fun b b' hb hb' =>
    LanglandsTunnell.linearDependent_string_of_gl2Complex_whittaker_system_of_moderateGrowth n 1 lam lam' one_ne_zero
      (fstr D hw b x) (fstr D hw b' x) (hsys b) (hsys b') (hgrow b hb) (hgrow b' hb')

  have hr : ∀ (b a : (AdeleRing (𝓞 K) K)ˣ), (((a : AdeleRing (𝓞 K) K)).2 = 1 ∧
      ∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w') →
      0 < ‖((a : AdeleRing (𝓞 K) K)).1 w‖ := by
    intro b a _
    have h := congrArg (fun z : AdeleRing (𝓞 K) K => z.1 w) a.mul_inv
    change ((a : AdeleRing (𝓞 K) K)).1 w * (((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w = 1 at h
    exact norm_pos_iff.2 (left_ne_zero_of_mul_eq_one h)
  obtain ⟨φ, hφ⟩ := exists_forall_exists_eq_mul_of_twist_of_pairwise_dependent'
    (B := (AdeleRing (𝓞 K) K)ˣ) (P := Fin (n + 1)) (A := (AdeleRing (𝓞 K) K)ˣ) (T := w.Completion)
    (fun b => ((b : AdeleRing (𝓞 K) K)).2 = 1)
    (fun b a => ((a : AdeleRing (𝓞 K) K)).2 = 1 ∧
      ∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w')
    (fun a => ((a : AdeleRing (𝓞 K) K)).1 w) (fun t => ‖t‖) hr
    (fun p a => whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (diagOne a))
    (fun b p y => fstr D hw b x p y) μ
    (fun b hb p a ha => htw b hb p a ha.1 ha.2) hdep
  exact ⟨φ, fun b hb => (hφ b hb).imp fun cb h p a ha hab => h p a ⟨ha, hab⟩⟩

end AutomorphicForm

end
