/-
The Hecke–diamond laws: `ModularCurve.diamondHBar_mul` on `J_H(M)` and
`ModularCurve.heckeDiamondCommuteBar` on `J₁(M)`.

This is the diamond sibling of `ModularCurve/HeckeCommuteBar.lean` (which hosts
`heckeOperatorsCommuteBar`), and the home of the two rows

* `ModularCurve.diamondHBar_mul` — the diamond operators on `J_H(M) = Pic⁰` form a
  representation of `(ZMod M)ˣ`: `⟨d * d'⟩ = ⟨d⟩ ∘ ⟨d'⟩`. Statement verbatim from
  `Theorems/Thm_ModularCurve_diamondHBar_mul.lean`, proof transcribed from
  `P2M/Sol/S_ModularCurve_diamondHBar_mul.lean` (410 lines, 33 declarations, five
  sections `Laurent`/`Group`/`Forms`/`Ratios`/`Diamond`).
* `ModularCurve.heckeDiamondCommuteBar` — all Hecke and diamond generators on `J₁(M)`
  commute pairwise. Statement verbatim from
  `Theorems/Thm_ModularCurve_heckeDiamondCommuteBar.lean`, proof transcribed from
  `P2M/Sol/S_ModularCurve_heckeDiamondCommuteBar.lean` (28 lines, one declaration).
  The row *assembles*: `HeckeDiamondCommuteBar M` unfolds to the pairwise commutation
  of `heckeDiamondGenBar M = Sum.elim heckeOperatorOneBar diamondOneBar`
  (`X1/HeckeModule.lean`), so the proof is the four-case `Sum` split over the three
  already-ported commutations `heckeOperatorOneBar_comm` (`X1/HeckeCommute.lean`),
  `heckeOperatorOneBar_comm_diamondOneBar` (`X1/DiamondLift.lean`) and
  `diamondOneBar_comm` (`X1/DiamondCorrespondence.lean`). No commutation is re-proved.

## Private / public split — resolved by the surface gate

The wire of this module is two headlines, and the first port kept every declaration of the
pin's `S_` file `private` in the pin's own file-local (root) namespace `XHDiaMul`. The
recipe §5 **surface gate** was then run on the module (drop `private`, re-run `check_port`,
read the three numbers) and it read **23 ok / 0 mismatch / 0 missing** — i.e. *every*
declaration of the pin's `S_` file is a pin-faithful statement the pin states publicly. So
the engine is **public** here: the `Group`/`Forms`/`Ratios` helpers for `Γ_H(M)`, the
generator `gen`, the predicate accessor `isDiamondAutHBar_apply`, the engine lemmas
`algEquiv_ext_of_ratios`, `isDiamondAutHBar_unique`, `isDiamondAutHBar_trans`, and the
`AlgEquiv` law `diamondAutHBar_mul` (proved *before* the pointwise headline, as in the pin),
alongside the two headlines `ModularCurve.diamondHBar_mul` and
`ModularCurve.heckeDiamondCommuteBar`. The checker's surface is therefore **23**, not 2.
The pin's `_root_.XHDiaMul.conj_mem_GammaH` keeps its root namespace, as the brief requires
(it is the pin's own spelling, and folding it into `ModularCurve` would collide with the
`X_H` side). The pin's
`_root_.XHDiaMul.conj_mem_GammaH` keeps its root namespace, as the brief requires (it
is the pin's own spelling, and folding it into `ModularCurve` would collide with the
`X_H` side).

Imported rather than restated (dedup, FR-0069 / trap 6 of the workorder):

* the pin's `Laurent` section is entirely ported vocabulary — `coeffMap_injective`
  (`Defs/Laurent.lean`), `coeffMap_ofPowerSeries` (`Frobenius/Defs.lean`),
  `ofPowerSeries_coeff_negSucc`, `coeffMap_intSeriesC`, `intSeriesC_C`,
  `intSeriesC_eq_of_isIntegralQExp` (`X1/DiamondCorrespondence.lean`),
  `intSeriesC_eq_zero_iff` (`JqIntegralRatios.lean`), `intSeriesC_add`
  (`X1/CoeffMap.lean`), `coeffEmb_injective` (`Defs/Laurent.lean`, general form);
* `coeGL_mul` and `entry_inv_mul` (both `Γ`-independent) are the ported
  `X1/DiamondCorrespondence.lean` lemmas;
* `mem_intFormRatiosC_of_mem` is the pin's one-liner over the ported
  `mem_qExpFunctionFieldC_rat_iff_mem_intFormRatiosC` (`X1/CoeffMap.lean`);
* `one_mem_strictPeriods` for `Γ_H(M)` is the pin's `zmultiples` one-liner over
  `CohCarrier.translation_mem_GammaH` (`ModularForms/Defs/GammaH.lean`).

Three of the pin's declarations are *unused* in the pin's own proof as well
(`intSeriesC_add`, `intSeriesC_C`, `coeffEmb_injective`: one occurrence each, the
declaration itself) and are not transcribed here.

Trap 4 of the workorder: the pin's namespace `XHDiaMul` is kept as a file-local
namespace, and `conj_mem_GammaH` lives in it (not in `ModularCurve`).

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_diamondHBar_mul.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_heckeDiamondCommuteBar.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_diamondHBar_mul.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_heckeDiamondCommuteBar.lean

spec-pin: Theorems/Thm_ModularCurve_diamondHBar_mul.lean
spec-pin: P2M/Sol/S_ModularCurve_diamondHBar_mul.lean
spec-pin: Theorems/Thm_ModularCurve_heckeDiamondCommuteBar.lean
spec-pin: P2M/Sol/S_ModularCurve_heckeDiamondCommuteBar.lean
-/
import FLTForHuman.ModularCurve.XH.Operators
import FLTForHuman.ModularCurve.XH.Inputs
import FLTForHuman.ModularCurve.X1.CoeffMap
import FLTForHuman.ModularCurve.X1.DiamondCorrespondence
import FLTForHuman.ModularCurve.X1.DiamondLift
import FLTForHuman.ModularCurve.X1.HeckeCommute
import FLTForHuman.ModularCurve.X1.HeckeModule

set_option autoImplicit false

noncomputable section

open UpperHalfPlane IntermediateField HahnSeries AlgebraicCurve CongruenceSubgroup
open scoped MatrixGroups ModularForm

local notation "ΓHℝ(" M ", " H ")" =>
  ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

namespace XHDiaMul

open ModularCurve

/-! ## The `Γ_H(M)` group helpers -/

section Group

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ}

/-- Every unit of `ZMod M` is the upper-left entry of some `Γ₀(M)`-matrix. -/
theorem exists_gamma0 [NeZero M] (d : (ZMod M)ˣ) :
    ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M ∧ ((γ 0 0 : ℤ) : ZMod M) = (d : ZMod M) := by
  obtain ⟨γ, hγ⟩ := CohCarrier.gamma0Units_surjective M d⁻¹
  refine ⟨(γ : SL(2, ℤ)), γ.2, ?_⟩
  have h : (((CohCarrier.gamma0Units M γ)⁻¹ : (ZMod M)ˣ) : ZMod M) =
      (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) := rfl
  rw [← h, hγ, inv_inv]

/-- `Γ_H(M)` is normalised by `Γ₀(M)`. -/
theorem conj_mem_GammaH {γ A : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M)
    (hA : A ∈ CohCarrier.GammaH M H) : γ * A * γ⁻¹ ∈ CohCarrier.GammaH M H :=
  CohCarrier.conj_mem_GammaH M H (⟨γ, hγ⟩ : Gamma0 M) ⟨A, hA⟩

open ConjAct Pointwise in
theorem gammaH_le_conj {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    ΓHℝ(M, H) ≤ toConjAct (γ : GL (Fin 2) ℝ)⁻¹ • ΓHℝ(M, H) := by
  intro x hx
  obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp hx
  rw [map_inv, Subgroup.mem_inv_pointwise_smul_iff, toConjAct_smul]
  refine Subgroup.mem_map.mpr ⟨γ * A * γ⁻¹, conj_mem_GammaH hγ hA, ?_⟩
  show Matrix.SpecialLinearGroup.mapGL ℝ (γ * A * γ⁻¹) =
    Matrix.SpecialLinearGroup.mapGL ℝ γ * Matrix.SpecialLinearGroup.mapGL ℝ A *
      (Matrix.SpecialLinearGroup.mapGL ℝ γ)⁻¹
  rw [map_mul, map_mul, map_inv]

end Group

/-! ## The `Γ_H(M)` forms

`conjForm` is the `γ`-slash of a `Γ_H(M)`-form, again a `Γ_H(M)`-form because
`Γ₀(M)` normalises `Γ_H(M)`; `slashQ` is its `q`-expansion as a Laurent series, and
the three vanishing lemmas turn `≠ 0` into a `q`-expansion statement. -/

section Forms

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ}

theorem one_mem_strictPeriods (M : ℕ) (H : Subgroup (ZMod M)ˣ) :
    (1 : ℝ) ∈ (ΓHℝ(M, H)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (CohCarrier.translation_mem_GammaH M H)]
  exact AddSubgroup.mem_zmultiples 1

open ConjAct Pointwise in
def conjForm {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M)
    (f : ModularForm ΓHℝ(M, H) k) : ModularForm ΓHℝ(M, H) k :=
  restrictForm (gammaH_le_conj hγ) (ModularForm.translate f (γ : GL (Fin 2) ℝ))

@[scoped simp]
theorem coe_conjForm {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M)
    (f : ModularForm ΓHℝ(M, H) k) :
    (⇑(conjForm γ hγ f) : ℍ → ℂ) = (⇑f) ∣[k] (γ : GL (Fin 2) ℝ) :=
  rfl

def slashQ (k : ℤ) (f : ℍ → ℂ) (γ : SL(2, ℤ)) : LaurentSeries ℂ :=
  ofPowerSeries ℤ ℂ (qExpansion 1 (f ∣[k] (γ : GL (Fin 2) ℝ)))

theorem slashQ_eq_conjForm {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M)
    (f : ModularForm ΓHℝ(M, H) k) :
    slashQ k f γ = ofPowerSeries ℤ ℂ (qExpansion 1 (conjForm γ hγ f)) :=
  rfl

theorem qexp_mul {a b : ℤ} (F : ModularForm ΓHℝ(M, H) a)
    (G : ModularForm ΓHℝ(M, H) b) :
    qExpansion 1 (⇑F * ⇑G) = qExpansion 1 F * qExpansion 1 G :=
  ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods M H) F G

theorem eq_of_qexp_eq {k : ℤ} {F G : ModularForm ΓHℝ(M, H) k}
    (h : qExpansion 1 (⇑F) = qExpansion 1 (⇑G)) : (⇑F : ℍ → ℂ) = ⇑G := by
  have h0 : F - G = 0 := by
    refine (ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods M H) (F - G)).mp ?_
    rw [FunLike.coe_sub, ModularForm.qExpansion_sub one_pos (one_mem_strictPeriods M H), h,
      sub_self]
  rw [sub_eq_zero.mp h0]

theorem ne_zero_of_isIntegralQExp {k : ℤ} {g : ModularForm ΓHℝ(M, H) k}
    {pg : PowerSeries ℤ} (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    g ≠ 0 := by
  intro h
  apply hg0
  rw [intSeriesC_eq_zero_iff]
  have h1 : qExpansion 1 (⇑g) = 0 := by rw [h, FunLike.coe_zero, qExpansion_zero]
  apply PowerSeries.map_injective (Int.castRingHom ℂ) Int.cast_injective
  rw [map_zero]
  exact hg.trans h1

theorem conjForm_ne_zero {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M)
    {g : ModularForm ΓHℝ(M, H) k} (hg : g ≠ 0) : conjForm γ hγ g ≠ 0 := by
  intro h
  apply hg
  have h1 : (⇑g : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ) = 0 := by
    rw [← coe_conjForm γ hγ g, h, FunLike.coe_zero]
  have h2 : (⇑g : ℍ → ℂ) = 0 := (SlashAction.slash_eq_zero_iff _ _ _).mp h1
  exact DFunLike.ext' (by rw [h2, FunLike.coe_zero])

theorem slashQ_ne_zero {k : ℤ} {g : ModularForm ΓHℝ(M, H) k} {pg : PowerSeries ℤ}
    (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma0 M) : slashQ k g γ ≠ 0 := by
  rw [slashQ_eq_conjForm γ hγ]
  refine (map_ne_zero_iff _ ofPowerSeries_injective).mpr ?_
  rw [Ne, ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods M H)]
  exact conjForm_ne_zero γ hγ (ne_zero_of_isIntegralQExp hg hg0)

theorem ofPowerSeries_qexp_ne_zero {k : ℤ} {g : ModularForm ΓHℝ(M, H) k}
    {pg : PowerSeries ℤ} (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    ofPowerSeries ℤ ℂ (qExpansion 1 (⇑g)) ≠ 0 := by
  change DiamondCorrespondence.QQ ⇑g ≠ 0
  rw [← DiamondCorrespondence.intSeriesC_eq_of_isIntegralQExp hg, Ne, intSeriesC_eq_zero_iff]
  exact fun h => hg0 (by rw [h, intSeriesC_zero])

end Forms

/-! ## The ratio form of `xHFunctionField` -/

section Ratios

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ}

theorem mem_intFormRatiosC_of_mem {y : LaurentSeries ℚ} (hy : y ∈ xHFunctionField M H) :
    y ∈ intFormRatiosC ℚ (CohCarrier.GammaH M H) :=
  (mem_qExpFunctionFieldC_rat_iff_mem_intFormRatiosC (CohCarrier.GammaH M H)
    (one_mem_strictPeriods M H) y).mp hy

end Ratios

/-! ## The diamond automorphisms of `X_H(M)` multiply

The engine: `gen` pushes a ratio of integral `q`-expansions to `xHFunctionFieldBar`;
`isDiamondAutHBar_apply` reads the predicate at it; `algEquiv_ext_of_ratios` reduces
equality of `ℚ̄`-automorphisms to agreement on the ratio set (two `adjoin_induction`s,
one over `ℚ`, one over `ℚ̄`); `isDiamondAutHBar_unique` and `isDiamondAutHBar_trans`
then give uniqueness and multiplicativity, and `diamondAutHBar_mul` is the
`AlgEquiv` law. -/

section Diamond

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ}

local notation "ℚbar" => AlgebraicClosure ℚ

def gen {k : ℤ} (f g : ModularForm ΓHℝ(M, H) k) {pf pg : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    xHFunctionFieldBar M H :=
  ⟨coeffEmb ℚbar (intSeriesC ℚ pf / intSeriesC ℚ pg),
    coeffEmb_mem_laurentBaseChange ℚbar (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩

theorem isDiamondAutHBar_apply {d : (ZMod M)ˣ}
    {σ : xHFunctionFieldBar M H ≃ₐ[ℚbar] xHFunctionFieldBar M H}
    (h : IsDiamondAutHBar M H d σ) (k : ℤ) (f g : ModularForm ΓHℝ(M, H) k)
    (pf pg : PowerSeries ℤ) (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC ℚ pg ≠ 0) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M)
    (hγd : ((γ 0 0 : ℤ) : ZMod M) = (d : ZMod M)) :
    ∃ y : LaurentSeries ℚ, y ∈ xHFunctionField M H ∧
      ((σ (gen f g hf hg hg0) : xHFunctionFieldBar M H) : LaurentSeries ℚbar) =
        coeffEmb ℚbar y ∧
      coeffMap (algebraMap ℚ ℂ) y * slashQ k g γ = slashQ k f γ :=
  h k f g pf pg hf hg hg0 γ hγ hγd

theorem algEquiv_ext_of_ratios {σ σ' : xHFunctionFieldBar M H ≃ₐ[ℚbar]
    xHFunctionFieldBar M H}
    (h : ∀ (x : LaurentSeries ℚ) (hx : x ∈ intFormRatiosC ℚ (CohCarrier.GammaH M H)),
      σ ⟨coeffEmb ℚbar x, coeffEmb_mem_laurentBaseChange ℚbar (intFormRatiosC_subset ℚ _ hx)⟩ =
        σ' ⟨coeffEmb ℚbar x,
          coeffEmb_mem_laurentBaseChange ℚbar (intFormRatiosC_subset ℚ _ hx)⟩) :
    σ = σ' := by
  have hF : ∀ (x : LaurentSeries ℚ) (hx : x ∈ xHFunctionField M H),
      σ ⟨coeffEmb ℚbar x, coeffEmb_mem_laurentBaseChange ℚbar hx⟩ =
        σ' ⟨coeffEmb ℚbar x, coeffEmb_mem_laurentBaseChange ℚbar hx⟩ := by
    intro x hxF
    have hx' : x ∈ IntermediateField.adjoin ℚ
        (intFormRatiosC ℚ (CohCarrier.GammaH M H)) := hxF
    induction hx' using IntermediateField.adjoin_induction with
    | mem x hx => exact h x hx
    | algebraMap r =>
        have e : (⟨coeffEmb ℚbar (algebraMap ℚ (LaurentSeries ℚ) r),
            coeffEmb_mem_laurentBaseChange ℚbar hxF⟩ :
            xHFunctionFieldBar M H) = (r : xHFunctionFieldBar M H) := by
          apply Subtype.ext
          rw [SubfieldClass.coe_ratCast]
          show coeffEmb ℚbar (algebraMap ℚ (LaurentSeries ℚ) r) = _
          rw [eq_ratCast, map_ratCast]
        rw [e, map_ratCast, map_ratCast]
    | add x x' hx hx' ihx ihx' =>
        have e : (⟨coeffEmb ℚbar (x + x'), coeffEmb_mem_laurentBaseChange ℚbar hxF⟩ :
            xHFunctionFieldBar M H) =
            ⟨coeffEmb ℚbar x, coeffEmb_mem_laurentBaseChange ℚbar hx⟩ +
              ⟨coeffEmb ℚbar x', coeffEmb_mem_laurentBaseChange ℚbar hx'⟩ :=
          Subtype.ext (map_add _ _ _)
        rw [e, map_add, map_add, ihx hx, ihx' hx']
    | inv x hx ihx =>
        have e : (⟨coeffEmb ℚbar x⁻¹, coeffEmb_mem_laurentBaseChange ℚbar hxF⟩ :
            xHFunctionFieldBar M H) =
            (⟨coeffEmb ℚbar x, coeffEmb_mem_laurentBaseChange ℚbar hx⟩)⁻¹ :=
          Subtype.ext (map_inv₀ _ _)
        rw [e, map_inv₀, map_inv₀, ihx hx]
    | mul x x' hx hx' ihx ihx' =>
        have e : (⟨coeffEmb ℚbar (x * x'), coeffEmb_mem_laurentBaseChange ℚbar hxF⟩ :
            xHFunctionFieldBar M H) =
            ⟨coeffEmb ℚbar x, coeffEmb_mem_laurentBaseChange ℚbar hx⟩ *
              ⟨coeffEmb ℚbar x', coeffEmb_mem_laurentBaseChange ℚbar hx'⟩ :=
          Subtype.ext (map_mul _ _ _)
        rw [e, map_mul, map_mul, ihx hx, ihx' hx']
  apply AlgEquiv.ext
  rintro ⟨z, hz⟩
  -- The second induction is stated over the adjoin presentation of `xHFunctionFieldBar`,
  -- with the subtype membership carried by `hbar`: the pin's proof terms are the same,
  -- and `hbar` keeps every `⟨x, _⟩` well typed at `implicit` transparency, which `rw`
  -- needs (the pin's lakefile compares at `.all`).
  have hbar : ∀ ⦃w : LaurentSeries ℚbar⦄,
      w ∈ laurentBaseChange ℚbar (xHFunctionField M H) → w ∈ xHFunctionFieldBar M H :=
    fun _ hw => hw
  have key : ∀ (w : LaurentSeries ℚbar)
      (hw : w ∈ laurentBaseChange ℚbar (xHFunctionField M H)),
      σ ⟨w, hbar hw⟩ = σ' ⟨w, hbar hw⟩ := by
    intro w hw
    induction hw using IntermediateField.adjoin_induction with
    | mem x hx =>
        obtain ⟨x₀, hx₀, rfl⟩ := hx
        exact hF x₀ hx₀
    | algebraMap c =>
        have e : (⟨algebraMap ℚbar (LaurentSeries ℚbar) c,
            hbar (IntermediateField.algebraMap_mem _ c)⟩ :
            xHFunctionFieldBar M H) = algebraMap ℚbar (xHFunctionFieldBar M H) c :=
          Subtype.ext rfl
        rw [e, AlgEquiv.commutes, AlgEquiv.commutes]
    | add x x' hx hx' ihx ihx' =>
        have e : (⟨x + x', hbar (add_mem hx hx')⟩ : xHFunctionFieldBar M H) =
            ⟨x, hbar hx⟩ + ⟨x', hbar hx'⟩ :=
          Subtype.ext rfl
        rw [e, map_add, map_add, ihx, ihx']
    | inv x hx ihx =>
        have e : (⟨x⁻¹, hbar (inv_mem hx)⟩ : xHFunctionFieldBar M H) =
            (⟨x, hbar hx⟩)⁻¹ :=
          Subtype.ext rfl
        rw [e, map_inv₀, map_inv₀, ihx]
    | mul x x' hx hx' ihx ihx' =>
        have e : (⟨x * x', hbar (mul_mem hx hx')⟩ : xHFunctionFieldBar M H) =
            ⟨x, hbar hx⟩ * ⟨x', hbar hx'⟩ :=
          Subtype.ext rfl
        rw [e, map_mul, map_mul, ihx, ihx']
  exact key z hz

theorem isDiamondAutHBar_unique [NeZero M] {d : (ZMod M)ˣ}
    {σ σ' : xHFunctionFieldBar M H ≃ₐ[ℚbar] xHFunctionFieldBar M H}
    (hσ : IsDiamondAutHBar M H d σ) (hσ' : IsDiamondAutHBar M H d σ') : σ = σ' := by
  obtain ⟨γ, hγ, hγd⟩ := exists_gamma0 (M := M) d
  refine algEquiv_ext_of_ratios fun x hx => ?_
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hx
  obtain ⟨y, -, hy, hyq⟩ := isDiamondAutHBar_apply hσ k f g pf pg hf hg hg0 γ hγ hγd
  obtain ⟨y', -, hy', hyq'⟩ := isDiamondAutHBar_apply hσ' k f g pf pg hf hg hg0 γ hγ hγd
  have hyy : y = y' := by
    apply coeffMap_injective (algebraMap ℚ ℂ).injective
    apply mul_right_cancel₀ (slashQ_ne_zero hg hg0 hγ)
    rw [hyq, hyq']
  apply Subtype.ext
  exact (hy.trans (by rw [hyy])).trans hy'.symm

theorem isDiamondAutHBar_trans [NeZero M] {d e : (ZMod M)ˣ}
    {σ τ : xHFunctionFieldBar M H ≃ₐ[ℚbar] xHFunctionFieldBar M H}
    (hσ : IsDiamondAutHBar M H d σ) (hτ : IsDiamondAutHBar M H e τ) :
    IsDiamondAutHBar M H (d * e) (σ.trans τ) := by
  intro k f g pf pg hf hg hg0 γ hγ hγde
  obtain ⟨γd, hγd, hγdd⟩ := exists_gamma0 (M := M) d
  set γe : SL(2, ℤ) := γd⁻¹ * γ with hγe_def
  have hγe : γe ∈ Gamma0 M := (Gamma0 M).mul_mem ((Gamma0 M).inv_mem hγd) hγ
  have hγee : ((γe 0 0 : ℤ) : ZMod M) = (e : ZMod M) :=
    DiamondCorrespondence.entry_inv_mul hγd hγ hγdd (by rw [hγde, Units.val_mul])
  have hγfac : (γd : GL (Fin 2) ℝ) * (γe : GL (Fin 2) ℝ) = (γ : GL (Fin 2) ℝ) := by
    rw [← DiamondCorrespondence.coeGL_mul, hγe_def, mul_inv_cancel_left]

  obtain ⟨y, hyF, hy, H1⟩ := isDiamondAutHBar_apply hσ k f g pf pg hf hg hg0 γd hγd hγdd
  obtain ⟨k', f', g', pf', pg', hf', hg', hg0', hyv⟩ := mem_intFormRatiosC_of_mem hyF
  have hgen : σ (gen f g hf hg hg0) = gen f' g' hf' hg' hg0' := by
    apply Subtype.ext
    rw [hy]
    show coeffEmb ℚbar y = coeffEmb ℚbar (intSeriesC ℚ pf' / intSeriesC ℚ pg')
    rw [hyv]
  obtain ⟨y'', hy''F, hy'', H2⟩ :=
    isDiamondAutHBar_apply hτ k' f' g' pf' pg' hf' hg' hg0' γe hγe hγee
  refine ⟨y'', hy''F, ?_, ?_⟩
  · show ((τ (σ (gen f g hf hg hg0)) : xHFunctionFieldBar M H) :
        LaurentSeries ℚbar) = coeffEmb ℚbar y''
    rw [hgen, hy'']

  set Fd := conjForm γd hγd f
  set Gd := conjForm γd hγd g
  set F'e := conjForm γe hγe f'
  set G'e := conjForm γe hγe g'
  set Fγ := conjForm γ hγ f
  set Gγ := conjForm γ hγ g

  have hyC : coeffMap (algebraMap ℚ ℂ) y =
      ofPowerSeries ℤ ℂ (qExpansion 1 (⇑f')) / ofPowerSeries ℤ ℂ (qExpansion 1 (⇑g')) := by
    rw [hyv, map_div₀, DiamondCorrespondence.coeffMap_intSeriesC,
      DiamondCorrespondence.coeffMap_intSeriesC,
      DiamondCorrespondence.intSeriesC_eq_of_isIntegralQExp hf',
      DiamondCorrespondence.intSeriesC_eq_of_isIntegralQExp hg']
  have hg'C := ofPowerSeries_qexp_ne_zero hg' hg0'
  rw [hyC, slashQ_eq_conjForm γd hγd, slashQ_eq_conjForm γd hγd,
    div_mul_eq_mul_div, div_eq_iff hg'C, ← map_mul, ← map_mul] at H1
  have H1' : qExpansion 1 (⇑f' * ⇑Gd) = qExpansion 1 (⇑g' * ⇑Fd) := by
    rw [qexp_mul, qexp_mul, mul_comm (qExpansion 1 (⇑g'))]
    exact ofPowerSeries_injective H1

  have E1 : (⇑f' : ℍ → ℂ) * ⇑Gd = ⇑g' * ⇑Fd := by
    have := eq_of_qexp_eq (F := f'.mul Gd) (G := g'.mul Fd)
      (by rw [ModularForm.coe_mul, ModularForm.coe_mul]; exact H1')
    rwa [ModularForm.coe_mul, ModularForm.coe_mul] at this
  have E2 : (⇑F'e : ℍ → ℂ) * ⇑Gγ = ⇑G'e * ⇑Fγ := by
    have := congrArg (fun F : ℍ → ℂ => F ∣[k' + k] γe) E1
    rw [ModularForm.mul_slash_SL2, ModularForm.mul_slash_SL2] at this
    simp only [ModularForm.SL_slash] at this
    simp only [Fd, Gd, coe_conjForm, ← SlashAction.slash_mul, hγfac] at this
    simpa only [F'e, G'e, Fγ, Gγ, coe_conjForm] using this

  have E3 : slashQ k' f' γe * slashQ k g γ = slashQ k' g' γe * slashQ k f γ := by
    rw [slashQ_eq_conjForm γe hγe, slashQ_eq_conjForm γe hγe, slashQ_eq_conjForm γ hγ,
      slashQ_eq_conjForm γ hγ, ← map_mul, ← map_mul, ← qexp_mul, ← qexp_mul]
    exact congrArg _ (congrArg _ E2)

  show coeffMap (algebraMap ℚ ℂ) y'' * slashQ k g γ = slashQ k f γ
  apply mul_right_cancel₀ (slashQ_ne_zero hg' hg0' hγe)
  linear_combination (slashQ k g γ) * H2 + E3

theorem diamondAutHBar_mul [NeZero M] (d d' : (ZMod M)ˣ) :
    diamondAutHBar M H (d * d') = diamondAutHBar M H d * diamondAutHBar M H d' := by
  have hin := (heckeDiamondInputsHAll M H).2
  have h1 : IsDiamondAutHBar M H (d' * d)
      ((diamondAutHBar M H d').trans (diamondAutHBar M H d)) :=
    isDiamondAutHBar_trans (isDiamondAutHBar_diamondAutHBar (hin d'))
      (isDiamondAutHBar_diamondAutHBar (hin d))
  rw [mul_comm d' d] at h1
  exact isDiamondAutHBar_unique (isDiamondAutHBar_diamondAutHBar (hin (d * d'))) h1

end Diamond

end XHDiaMul

namespace ModularCurve

open XHDiaMul in
/-- **The diamond operators multiply.** The diamond operators `⟨d⟩ = diamondHBar M H d` on
`J_H(M) = Pic⁰` form a representation of `(ZMod M)ˣ`: `⟨d * d'⟩ = ⟨d⟩ ∘ ⟨d'⟩`. Statement
verbatim from `Theorems/Thm_ModularCurve_diamondHBar_mul.lean`; proof after the pin's
`S_` file, through the `AlgEquiv` law `XHDiaMul.diamondAutHBar_mul`. -/
theorem diamondHBar_mul (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (d d' : (ZMod M)ˣ) (x : ModularCurve.JH M H) :
    ModularCurve.diamondHBar M H (d * d') x =
      ModularCurve.diamondHBar M H d (ModularCurve.diamondHBar M H d' x) := by
  rw [ModularCurve.diamondHBar_apply, ModularCurve.diamondHBar_apply,
    ModularCurve.diamondHBar_apply, XHDiaMul.diamondAutHBar_mul, map_mul, mul_smul]

/-- **The Hecke and diamond generators on `J₁(M)` commute pairwise.** Statement verbatim
from `Theorems/Thm_ModularCurve_heckeDiamondCommuteBar.lean`; proof after the pin's `S_`
file: the four `Sum` cases of `heckeDiamondGenBar = Sum.elim heckeOperatorOneBar
diamondOneBar` are the three already-ported commutations. -/
theorem heckeDiamondCommuteBar (M : ℕ) [NeZero M] : ModularCurve.HeckeDiamondCommuteBar M := by
  intro i j
  rcases i with ℓ | d <;> rcases j with ℓ' | e
  · rw [heckeDiamondGenBar_inl, heckeDiamondGenBar_inl]
    exact heckeOperatorOneBar_comm M ℓ ℓ'
  · rw [heckeDiamondGenBar_inl, heckeDiamondGenBar_inr]
    exact heckeOperatorOneBar_comm_diamondOneBar M ℓ e
  · rw [heckeDiamondGenBar_inl, heckeDiamondGenBar_inr]
    exact (heckeOperatorOneBar_comm_diamondOneBar M ℓ' d).symm
  · rw [heckeDiamondGenBar_inr, heckeDiamondGenBar_inr]
    exact diamondOneBar_comm M d e

end ModularCurve

end
