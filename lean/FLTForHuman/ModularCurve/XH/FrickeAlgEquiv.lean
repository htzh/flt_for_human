/-
The Fricke involution as an algebra equivalence of the `X_H` function field.

The Fricke (Atkin–Lehner) involution `w_N` acts on the modular curve `X_H` and on its function
field; this module proves that, at the level where the `q`-expansion model is algebraic, the
involution is realised by an **algebra equivalence**

  `XHFunctionFieldBar →ₐ[ℚ] XHFunctionFieldBar

whose effect on `q`-expansions is the Fricke slash (`qExpansion_slash_fricke`), and which therefore
commutes with the Hecke operators it is supposed to commute with.  That is what makes the
Atkin–Lehner symmetry of the Hecke algebra available on the function field rather than only on the
analytic model, and it is the input of the `X_H` Hecke-eigenvalue arguments.

The engine is the `XH` family (`ModularCurve/XH/{Inputs,FrickeGalois,Operators}.lean` — the latter
is the port of the pin's `Def_ModularCurve_XHOperators`), the Hecke `q`-coefficient algebra
(`ModularForms/HeckeQCoeff.lean`), the correspondence API (`AlgebraicCurve/Defs/Correspondence.lean`),
and the Frobenius-trace dictionary (`GaloisRep/Defs/FrobeniusTrace.lean`).

## The port (SET-AF106, order B) — a substitution case

This pin is the set's biggest substitution: of its 106 `S_` declarations (1,105 lines)
**70 (635 lines) were already public in the port**, and the module *imports* them instead of
re-proving them. `port_advise` matches **71** of the pin's rows: **63 imported**, **4 re-declared
here** (the port's copy is `private` — `LBC`, `val_frickeGL`, `val_scalarGL` — or a binder-shape
match, `frickeGL`), **2 the headline**, **1 the pin's private `hT'`** (ported as
`FrickeGalois.diamond_T_mem`) and **1 (`coe_gen`) not needed** — `gen_rep` is imported.

* `ModularCurve/XH/FrickeGalois.lean` — the pin's thirteen-section engine at the same
  `q`-expansion vocabulary: `frickeForm`, `frickeSqConst`, `scalarGL`, `slashForm`, `DiaP`
  (with `apply_rep`/`add`/`mul`/`neg`/`zero`/`inv`), `gen`, `gen_rep`, `algHom_ext_gen`, the
  `qC_*` ring laws, the ratio-field calculus (`ratioField`, `mem_ratios_of_mem`, …), the `Coeff`
  engine (`coeffMap_injective`, `coeffMap_C`, `coeffMap_coeffEmb_intSeriesC`), `frickeForm_ne_zero`,
  `qC_frickeForm_ne_zero`, `exists_gamma0_upperLeft`, `diaP_all`, and
  `exists_algEquiv_xHFunctionFieldBar_slash_fricke_and_galois_smul` — the pin's *other* headline,
  which supplies this module's `w`, its `FrickeSpec` and its Galois law;
* `ModularCurve/Defs/Laurent.lean` — `coeffMap_qExpand`;
* `ModularCurve/X1/FunctionField.lean` — the ratio-field membership lemmas the pin restates
  (`mul_mem_ratios`, `add_mem_ratios`, `neg_mem_ratios`, `inv_mem_ratios`, `intSeriesC_add'`,
  `intSeriesC_neg'`, `isIntegralQExp_const`, `algebraMap_mem_ratios`);
* `ModularCurve/X1/DiamondAut.lean` — `qC_one`, `qC_zero`;
* `ModularCurve/XH/{Operators,HeckeOperator,Inputs}.lean` — `IsDiamondAutHBar`,
  `diamondAutHBar`, `diamondHBar`, `heckeAlphaHBar`/`heckeBetaHBar` with `coe_*`,
  `HeckeBetaHDefined`, `heckePic0HBar`/`heckePic0HBarTranspose`, `HeckeDiamondInputsHAll`, and
  the diamond half `heckeDiamondInputsHAll` (the pin's `hin`);
* `AlgebraicCurve/Defs/Correspondence.lean` — `SemilinearAut.pic0_correspondence_swap_smul`
  (what the pin's `lawOne` pays off into);
* `GaloisRep/SemisimpleCriterion.lean` — `ValuationSubring.IsFrobeniusAt.apply_eq_pow_of_pow_eq_one`
  (the pin's `lawFour` input).

**Both `port_advise` suspects are rejected** (FR-0266/FR-0311 — read the body, one name at a time):

* `ratioField → ModularCurve.modularFunctionField` — the pin's `ratioField` is `intFormRatiosC ℚ Γ`
  as an `IntermediateField`, with the `q`-expansion calculus for its `mul_mem'`/`inv_mem'`; it is
  not `Defs/Fields.lean`'s `modularFunctionField`. The port already carries it, at that statement,
  as `FrickeGalois.ratioField`;
* `frickeGL → ModularForm.AtkinLehnerDatum.alGL` — type-only. The pin's `frickeGL` is
  `!![0, -1; M, 0]` in `GL(2, ℝ)`; `ALTraceIdentity.frickeGL M (NeZero.ne M)` *is* that matrix and
  is public, but at a different binder shape (`(M) (hM : M ≠ 0)`), so the pin's
  `variable (M) in def frickeGL [NeZero M]` is declared here at the pin's own text.

**Transcribed because the port's copy is `private`** (a private port declaration is not
importable): `val_frickeGL`, `coe_frickeForm` (`XH/FrickeSlash.lean`, `XH/FrickeGalois.lean`),
`val_scalarGL`, `LBC` and `frickeGL` (`XH/FrickeGalois.lean`). Two further declarations stay
`private` and are **adapters, not mathematics**: because the port's `frickeGL` is private, its
`slash_frickeGL_frickeGL` and `frickeGL_mul_mul_inv` are stated at that constant, so
`slash_frickeGL_frickeGL'` and `frickeGL_mul_mul_inv'` restate them at this module's public
`frickeGL` (one imported proof each; proof irrelevance relates the two matrices). Surface note (the
`private` policy of the preamble): all 34 public declarations read `ok` against the pin and the
module's only two `private` declarations are the adapters above (no pin counterpart), so there is
nothing for the surface gate to promote.

**One port-vs-pin shape difference is load-bearing.** The port's `xHFunctionField` is an `abbrev`
for the `def` `xHFunctionFieldC`, whereas the pin's is a single `def`; so `LBC Γ` and
`laurentBaseChange Qb (xHFunctionField Γ)` are only *default-transparency* defeq, not
instance-transparency defeq. `rw` therefore cannot bridge the two on its own, and
`leg_alpha`/`leg_beta` instantiate their rewrites explicitly (`coe_heckeAlphaHBar M H ℓ x₀`,
`hw' (heckeAlphaHBar Qb M H ℓ (w x))`). The same double delta is what prices the module's
heartbeat profile (the probe pair below); it is a spread cost in the *statement elaboration* of
`semilinear_twist` and `lawOne`, not a proof step.

## Gates (measured 2026-11-27, `check_port` corpus `aa2d8b3`)

* `check_port --force`: **34 ok / 0 mismatch / 0 missing / 0 own / 0 kw**, every declaration `ok`
  at the pin's statement.
* engine gate: pin sources 2 (`Theorems/` + `S_`), pin rows **108**, module rows **37**;
  **35 by statement hash, 0 by name only, 2 unaccounted** — the two `private` adapters. Of the
  pin's 108 rows, 35 are declared here (34 public + the anonymous `NeZero (M * ℓ)` instance) and
  73 are not: 71 substituted from the port (`XH/…`, `Defs/Laurent.lean`, `X1/FunctionField.lean`,
  `X1/DiamondAut.lean`), 1 the pin's `private hT'` (the port's `FrickeGalois.diamond_T_mem`), and
  1 `solution`, which is this module's headline verified against the `Theorems/` wire.
* `#print axioms`: 34 public declarations, all `[propext, Classical.choice, Quot.sound]` or a
  subset (`ofPowerSeries_eq_qExpand` is `[propext, Quot.sound]`), no `sorryAx`.
* `dedup.py --within`: **0 duplicate clusters**. `move_dead.py --dry-run`: **0 declarations,
  0 lines**. Silent at the edit loop; one locked `lake build` with **0 warning lines** from this
  file. The set's collision probe (`tmp/af106/collision-probe.lean`) prints nothing.
* **Heartbeat probe (recorded, never installed; FR-0225).** The edit-loop cap is 200000, where the
  module is silent. The downward ladder from 40000 fails at 40000, so the floor is above it and the
  bisector was run upward: at **100000** the first failure is `lawOne` (line 538, `whnf` timeout in
  the *statement*); at **40000** the first failure is `semilinear_twist` (line 523, `isDefEq`
  timeout in the statement); at **20000** it is `leg_alpha` (line 469). Rungs below 20000 are
  dominated (every one fails and the first failure can only move earlier — 20000 already fails
  before the module's second half). So the pair is **(silent at the 200000 edit-loop cap, fails at
  100000 with `lawOne`)**: the module floor lies between 100000 and 200000, nowhere near the
  lakefile's 4 M bound, and no `set_option maxHeartbeats` (module or instance) is carried. The
  pin's `attribute [-instance]` / `attribute [-simp]` walls are not transcribed either.
  `set_option autoImplicit false` is the pin's; `linter.unusedSectionVars` and
  `linter.style.haveILetI` are switched off for the pin's own dead section variables and for its
  load-bearing `haveI` in `Prop` goals (FR-0306), as `XH/Inputs.lean` does.

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_exists_frickeAlgEquiv_xHFunctionFieldBar.lean>

spec-pin: Theorems/Thm_ModularCurve_exists_frickeAlgEquiv_xHFunctionFieldBar.lean
spec-pin: P2M/Sol/S_ModularCurve_exists_frickeAlgEquiv_xHFunctionFieldBar.lean
-/
import FLTForHuman.AlgebraicCurve.Defs.Correspondence
import FLTForHuman.GaloisRep.Defs.FrobeniusTrace
import FLTForHuman.GaloisRep.SemisimpleCriterion
import FLTForHuman.ModularCurve.XH.FrickeGalois
import FLTForHuman.ModularCurve.XH.Inputs
import FLTForHuman.ModularCurve.XH.Operators
import FLTForHuman.ModularForms.HeckeQCoeff

set_option autoImplicit false
set_option linter.unusedSectionVars false
-- The pin's `haveI` in a `Prop` goal is load-bearing; keep it literal (FR-0306).
set_option linter.style.haveILetI false

noncomputable section

open UpperHalfPlane CongruenceSubgroup Matrix IntermediateField HahnSeries AlgebraicCurve
open scoped MatrixGroups ModularForm Pointwise

open ModularForm.Level (ΓGL)
open ModularCurve.FrickeGalois

namespace ModularCurve

namespace FrickeAlgEquiv

local notation "Qb" => AlgebraicClosure ℚ

section Groups

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ}

variable (M) in

/-- The Fricke matrix `!![0, -1; M, 0]` as an element of `GL(2, ℝ)`. -/
def frickeGL [NeZero M] : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0]
    (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M])

@[scoped simp]
theorem val_frickeGL [NeZero M] :
    ((frickeGL M : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0] := rfl

@[scoped simp]
theorem coe_frickeForm [NeZero M] {k : ℤ} (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    ⇑(frickeForm f) = ⇑f ∣[k] frickeGL M := rfl

@[scoped simp]
theorem val_scalarGL (a : ℝ) (ha : a ≠ 0) :
    ((scalarGL a ha : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a, 0; 0, a] := rfl

/- The port's `XH/FrickeGalois.lean` carries the Fricke matrix as a `private def`; the two
bridges below restate its two Fricke-matrix lemmas at *this* module's public `frickeGL`
(they are the same term up to proof irrelevance, so each bridge is the imported proof). -/
private theorem slash_frickeGL_frickeGL' [NeZero M] (k : ℤ) (φ : ℍ → ℂ) :
    (φ ∣[k] frickeGL M) ∣[k] frickeGL M = (fun _ => frickeSqConst M k) * φ :=
  slash_frickeGL_frickeGL k φ

private theorem frickeGL_mul_mul_inv' [NeZero M] (γ : SL(2, ℤ)) (h : (M : ℤ) ∣ γ 1 0) :
    frickeGL M * Matrix.SpecialLinearGroup.mapGL ℝ γ * (frickeGL M)⁻¹ =
      Matrix.SpecialLinearGroup.mapGL ℝ (CohCarrier.frickeMat M γ h) :=
  frickeGL_mul_mul_inv γ h

end Groups

section GroupIdentity

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ)

/-- The level-`M * ℓ` group induced by `H` along `M ∣ M * ℓ`. -/
def liftSub : Subgroup (ZMod (M * ℓ))ˣ :=
  H.comap (ZMod.unitsMap (Dvd.intro ℓ rfl : M ∣ M * ℓ))

theorem gammaH_inf_gamma0_eq :
    CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ) = CohCarrier.GammaH (M * ℓ) (liftSub M H ℓ) := by
  ext A
  simp only [Subgroup.mem_inf, CohCarrier.mem_GammaH_iff, liftSub, Subgroup.mem_comap]
  have hdvd : M ∣ M * ℓ := Dvd.intro ℓ rfl
  have key : ∀ (hA : A ∈ Gamma0 (M * ℓ)) (hA' : A ∈ Gamma0 M),
      ZMod.unitsMap hdvd (CohCarrier.gamma0Units (M * ℓ) ⟨A, hA⟩) =
        CohCarrier.gamma0Units M ⟨A, hA'⟩ := fun hA hA' => by
    ext
    rw [ZMod.unitsMap_val]
    change ZMod.cast (((A 1 1 : ℤ) : ZMod (M * ℓ))) = ((A 1 1 : ℤ) : ZMod M)
    rw [ZMod.cast_intCast hdvd]
  have h0 : ∀ hA : A ∈ Gamma0 (M * ℓ), A ∈ Gamma0 M := fun hA => by
    rw [Gamma0_mem] at hA ⊢
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hA
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ((Int.natCast_dvd_natCast.mpr hdvd).trans h)
  constructor
  · rintro ⟨⟨hA0, hH⟩, hAℓ⟩
    exact ⟨hAℓ, by rwa [key hAℓ hA0]⟩
  · rintro ⟨hAℓ, hH⟩
    exact ⟨⟨h0 hAℓ, by rwa [key hAℓ (h0 hAℓ)] at hH⟩, hAℓ⟩

end GroupIdentity

section QExp

variable {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ)

include hT

theorem qC_neg {k : ℤ} (f : ModularForm (ΓGL Γ) k) : qC (-⇑f) = -qC f := by
  rw [qC, qC, ModularForm.qExpansion_neg one_pos (one_mem_strictPeriods_of_T_mem hT) f, map_neg]

end QExp

section Coeff

theorem ofPowerSeries_eq_qExpand {ℓ : ℕ} [NeZero ℓ] (p p' : PowerSeries ℂ)
    (h : ∀ n, PowerSeries.coeff n p' = if ℓ ∣ n then PowerSeries.coeff (n / ℓ) p else 0) :
    ofPowerSeries ℤ ℂ p' = qExpand ℂ ℓ (ofPowerSeries ℤ ℂ p) := by
  ext m
  by_cases hdvd : (ℓ : ℤ) ∣ m
  · obtain ⟨j, rfl⟩ := hdvd
    rw [qExpand_coeff_mul, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
    have hℓ0 : (0 : ℤ) < ℓ := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne ℓ)
    by_cases hj : j < 0
    · rw [ite_eq_left hj, ite_eq_left (mul_neg_of_pos_of_neg hℓ0 hj)]
    · rw [ite_eq_right hj, ite_eq_right (by push Not at hj ⊢; positivity), h]
      have h1 : ((ℓ : ℤ) * j).natAbs = ℓ * j.natAbs := by
        rw [Int.natAbs_mul, Int.natAbs_natCast]
      rw [h1, ite_eq_left (Dvd.intro _ rfl), Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne ℓ))]
  · rw [qExpand_coeff_of_not_dvd ℓ _ hdvd, PowerSeries.coeff_coe]
    split_ifs with hm
    · rfl
    · rw [h, ite_eq_right]
      rintro ⟨c, hc⟩
      apply hdvd
      refine ⟨c, ?_⟩
      have : (m.natAbs : ℤ) = m := Int.natAbs_of_nonneg (le_of_not_gt hm)
      rw [← this, hc]; push_cast; ring

theorem qC_comp_heckeDiag {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ) {k : ℤ}
    (F : ModularForm (ΓGL Γ) k) (ℓ : ℕ) [NeZero ℓ] :
    qC (fun τ => F (ModularForm.heckeDiagMatrix ℓ • τ)) = qExpand ℂ ℓ (qC F) :=
  ofPowerSeries_eq_qExpand _ _ fun n =>
    ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul F (one_mem_strictPeriods_of_T_mem hT)
      (NeZero.ne ℓ) n

end Coeff

section LevelMatrices

variable {M : ℕ} [NeZero M] {ℓ : ℕ} [NeZero ℓ]

scoped instance : NeZero (M * ℓ) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne ℓ)⟩

theorem frickeGL_mul_heckeDiag :
    frickeGL M * ModularForm.heckeDiagMatrix ℓ = frickeGL (M * ℓ) := by
  ext i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, ModularForm.val_heckeDiagMatrix (NeZero.ne ℓ),
    val_frickeGL]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem heckeDiag_mul_frickeGL :
    ModularForm.heckeDiagMatrix ℓ * frickeGL (M * ℓ) =
      frickeGL M * scalarGL (ℓ : ℝ) (by exact_mod_cast NeZero.ne ℓ) := by
  ext i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, ModularForm.val_heckeDiagMatrix (NeZero.ne ℓ),
    val_frickeGL, val_scalarGL]
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_two]; try ring)

theorem slash_frickeGL_mul (k : ℤ) (φ : ℍ → ℂ) :
    φ ∣[k] frickeGL (M * ℓ) =
      (fun _ => ((ℓ : ℂ) ^ (k - 1))) *
        fun τ => (φ ∣[k] frickeGL M) (ModularForm.heckeDiagMatrix ℓ • τ) := by
  rw [← frickeGL_mul_heckeDiag, SlashAction.slash_mul]
  funext τ
  rw [ModularForm.slash_heckeDiagMatrix_apply k (NeZero.ne ℓ)]
  rfl

end LevelMatrices

section Spec

/-- Base change of the `q`-expansion function field of level `Γ` to `ℚ̄`. -/
abbrev LBC (Γ : Subgroup SL(2, ℤ)) : IntermediateField Qb (LaurentSeries Qb) :=
  laurentBaseChange Qb (qExpFunctionFieldC ℚ Γ)

/-- The `q`-expansion spec of a Fricke pull-back: it carries the relation
`coeffMap ι x * qC g = qC f` to the relation at the `W`-slash. -/
def FrickeSpec (Γ : Subgroup SL(2, ℤ)) (W : GL (Fin 2) ℝ) (ι : Qb →+* ℂ) (w : LBC Γ → LBC Γ) :
    Prop :=
  ∀ (x : LBC Γ) (k : ℤ) (f g : ModularForm (ΓGL Γ) k),
    coeffMap ι (x : LaurentSeries Qb) * qC g = qC f →
      coeffMap ι ((w x : LBC Γ) : LaurentSeries Qb) * qC (⇑g ∣[k] W) = qC (⇑f ∣[k] W)

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

theorem apply_apply_of_frickeSpec (ι : Qb →+* ℂ)
    {w : LBC (CohCarrier.GammaH M H) ≃ₐ[Qb] LBC (CohCarrier.GammaH M H)}
    (spec : FrickeSpec (CohCarrier.GammaH M H) (frickeGL M) ι w) (x : LBC (CohCarrier.GammaH M H)) :
    w (w x) = x := by
  have hT : ModularGroup.T ∈ CohCarrier.GammaH M H := CohCarrier.translation_mem_GammaH M H
  suffices h : (w.trans w).toAlgHom = AlgHom.id Qb _ from AlgHom.congr_fun h x
  refine algHom_ext_gen hT fun k f g pf pg hf hg hg0 => ?_
  change w (w (gen f g hf hg hg0)) = gen f g hf hg hg0
  set x₀ := gen f g hf hg hg0 with hx₀
  have hg' : qC g ≠ 0 := qC_ne_zero_of_witness hg hg0
  have h0 : coeffMap ι (x₀ : LaurentSeries Qb) * qC g = qC f := gen_rep ι f g hf hg hg0
  have h1 := spec x₀ k f g h0
  rw [← coe_frickeForm, ← coe_frickeForm] at h1
  have h2 := spec (w x₀) k (frickeForm f) (frickeForm g) h1
  rw [coe_frickeForm, coe_frickeForm, slash_frickeGL_frickeGL', slash_frickeGL_frickeGL',
    qC_const_mul hT, qC_const_mul hT, ← mul_assoc, mul_comm (coeffMap ι _), mul_assoc] at h2
  have h3 := mul_left_cancel₀ ((map_ne_zero_iff _ HahnSeries.C_injective).mpr
    (frickeSqConst_ne_zero (M := M) k)) h2
  rw [← h0] at h3
  exact Subtype.ext (ModularCurve.FrickeGalois.coeffMap_injective ι (mul_right_cancel₀ hg' h3))

end Spec

section Rep

variable {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ)

include hT

theorem rep_neg {X : LaurentSeries ℂ} {k : ℤ} {f g : ModularForm (ΓGL Γ) k}
    (h : X * qC g = qC f) : (-X) * qC g = qC (⇑(-f)) := by
  rw [FunLike.coe_neg, qC_neg hT, ← h]; ring

end Rep

section Diamond

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ}

@[scoped simp]
theorem coe_slashForm {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M)
    (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    ⇑(slashForm γ hγ f) = ⇑f ∣[k] (γ : GL (Fin 2) ℝ) := rfl

theorem coe_slashForm_add {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M)
    (f g : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    ⇑(slashForm γ hγ f + slashForm γ hγ g) = ⇑(f + g) ∣[k] (γ : GL (Fin 2) ℝ) := by
  simp only [coe_slashForm, FunLike.coe_add, SlashAction.add_slash]

theorem coe_slashForm_neg {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M)
    (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    ⇑(-slashForm γ hγ f) = ⇑(-f) ∣[k] (γ : GL (Fin 2) ℝ) := by
  simp only [coe_slashForm, FunLike.coe_neg, SlashAction.neg_slash]

end Diamond

section LawTwo

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

omit [NeZero M] in
theorem mul_frickeMat_mem {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    γ * CohCarrier.frickeMat M γ (CohCarrier.N_dvd_of_mem_Gamma0 M hγ) ∈ CohCarrier.GammaH M H := by
  rw [CohCarrier.mem_GammaH_iff]
  refine ⟨mul_mem hγ (CohCarrier.frickeMat_mem_Gamma0 M hγ), ?_⟩
  have h := CohCarrier.gamma0Units_frickeMat M ⟨γ, hγ⟩
  have : (⟨γ * CohCarrier.frickeMat M γ (CohCarrier.N_dvd_of_mem_Gamma0 M hγ),
      mul_mem hγ (CohCarrier.frickeMat_mem_Gamma0 M hγ)⟩ : Gamma0 M) =
      ⟨γ, hγ⟩ * ⟨CohCarrier.frickeMat M γ (CohCarrier.N_dvd_of_mem_Gamma0 M hγ),
        CohCarrier.frickeMat_mem_Gamma0 M hγ⟩ := rfl
  rw [this, map_mul, h, mul_inv_cancel]
  exact one_mem H

theorem slash_gamma_fricke_gamma {k : ℤ} (h : ModularForm (ΓGL (CohCarrier.GammaH M H)) k)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    ((⇑h ∣[k] (γ : GL (Fin 2) ℝ)) ∣[k] frickeGL M) ∣[k] (γ : GL (Fin 2) ℝ) =
      ⇑h ∣[k] frickeGL M := by
  have h10 := CohCarrier.N_dvd_of_mem_Gamma0 M hγ
  have hW : frickeGL M * Matrix.SpecialLinearGroup.mapGL ℝ γ =
      Matrix.SpecialLinearGroup.mapGL ℝ (CohCarrier.frickeMat M γ h10) * frickeGL M := by
    rw [← frickeGL_mul_mul_inv' γ h10, inv_mul_cancel_right]
  have hmat : (γ : GL (Fin 2) ℝ) * frickeGL M * (γ : GL (Fin 2) ℝ) =
      Matrix.SpecialLinearGroup.mapGL ℝ (γ * CohCarrier.frickeMat M γ h10) * frickeGL M := by
    rw [map_mul, ← mapGL_eq_coe, mul_assoc, hW, mul_assoc]
  rw [← SlashAction.slash_mul, ← SlashAction.slash_mul, ← mul_assoc, hmat, SlashAction.slash_mul]
  congr 1
  exact SlashInvariantForm.slash_action_eqn h _
    (Subgroup.mem_map_of_mem (Matrix.SpecialLinearGroup.mapGL ℝ) (mul_frickeMat_mem hγ))

theorem dia_fricke_dia (ι : Qb →+* ℂ)
    {w : LBC (CohCarrier.GammaH M H) ≃ₐ[Qb] LBC (CohCarrier.GammaH M H)}
    (spec : FrickeSpec (CohCarrier.GammaH M H) (frickeGL M) ι w)
    {D : LBC (CohCarrier.GammaH M H) ≃ₐ[Qb] LBC (CohCarrier.GammaH M H)} {d : (ZMod M)ˣ}
    (hDd : IsDiamondAutHBar M H d D) (x : LBC (CohCarrier.GammaH M H)) : D (w (D x)) = w x := by
  have hT : ModularGroup.T ∈ CohCarrier.GammaH M H := CohCarrier.translation_mem_GammaH M H
  obtain ⟨γ, hγ, hγd⟩ := exists_gamma0_upperLeft (M := M) d
  suffices h : (D.trans (w.trans D)).toAlgHom = w.toAlgHom from AlgHom.congr_fun h x
  refine algHom_ext_gen hT fun k f g pf pg hf hg hg0 => ?_
  change D (w (D (gen f g hf hg hg0))) = w (gen f g hf hg hg0)
  set x₀ := gen f g hf hg hg0
  have hall := fun y => diaP_all (ι := ι) (D := D) (γ := γ) (hγ := hγ) hDd hγd y
  have hg' : qC g ≠ 0 := qC_ne_zero_of_witness hg hg0
  have h0 : coeffMap ι (x₀ : LaurentSeries Qb) * qC g = qC f := gen_rep ι f g hf hg hg0
  have h1 := (hall x₀).apply_rep f g h0
  have h2 := spec (D x₀) k (slashForm γ hγ f) (slashForm γ hγ g) h1
  rw [← coe_frickeForm, ← coe_frickeForm] at h2
  have h3 := (hall (w (D x₀))).apply_rep (frickeForm (slashForm γ hγ f))
    (frickeForm (slashForm γ hγ g)) h2
  simp only [coe_slashForm, coe_frickeForm, slash_gamma_fricke_gamma _ hγ] at h3
  have h4 := spec x₀ k f g h0
  rw [← h4] at h3
  exact Subtype.ext (ModularCurve.FrickeGalois.coeffMap_injective ι (mul_right_cancel₀ (qC_frickeForm_ne_zero hg') h3))

theorem diamondAut_fricke_diamondAut (ι : Qb →+* ℂ)
    {w : xHFunctionFieldBar M H ≃ₐ[Qb] xHFunctionFieldBar M H}
    (spec : FrickeSpec (CohCarrier.GammaH M H) (frickeGL M) ι w) (d : (ZMod M)ˣ)
    (x : xHFunctionFieldBar M H) :
    diamondAutHBar M H d (w (diamondAutHBar M H d x)) = w x := by
  rcases Classical.em (∃ σ : xHFunctionFieldBar M H ≃ₐ[Qb] xHFunctionFieldBar M H,
      IsDiamondAutHBar M H d σ) with h | h
  · exact dia_fricke_dia ι spec (isDiamondAutHBar_diamondAutHBar h) x
  · rw [diamondAutHBar_of_not h]; rfl

end LawTwo

section LawOne

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {ℓ : ℕ} [NeZero ℓ]

theorem exists_top (ι : Qb →+* ℂ)
    (child : ∀ (M' : ℕ) [NeZero M'] (H' : Subgroup (ZMod M')ˣ),
      ∃ w : LBC (CohCarrier.GammaH M' H') ≃ₐ[Qb] LBC (CohCarrier.GammaH M' H'),
        FrickeSpec (CohCarrier.GammaH M' H') (frickeGL M') ι w) :
    ∃ w' : LBC (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) ≃ₐ[Qb]
        LBC (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)),
      FrickeSpec (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) (frickeGL (M * ℓ)) ι w' ∧
        ∀ x, w' (w' x) = x := by
  have key : ∀ Γ' : Subgroup SL(2, ℤ), Γ' = CohCarrier.GammaH (M * ℓ) (liftSub M H ℓ) →
      ∃ w' : LBC Γ' ≃ₐ[Qb] LBC Γ', FrickeSpec Γ' (frickeGL (M * ℓ)) ι w' ∧ ∀ x, w' (w' x) = x := by
    rintro _ rfl
    obtain ⟨w', spec'⟩ := child (M * ℓ) (liftSub M H ℓ)
    exact ⟨w', spec', apply_apply_of_frickeSpec ι spec'⟩
  exact key _ (gammaH_inf_gamma0_eq M H ℓ)

variable (ι : Qb →+* ℂ)
  {w : LBC (CohCarrier.GammaH M H) ≃ₐ[Qb] LBC (CohCarrier.GammaH M H)}
  {w' : LBC (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) ≃ₐ[Qb]
    LBC (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ))}

omit [NeZero M] [NeZero ℓ] in
variable (ℓ) in
theorem le_top_bot : ΓGL (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) ≤ ΓGL (CohCarrier.GammaH M H) :=
  Subgroup.map_mono inf_le_left

theorem qC_slash_frickeGL_mul {k : ℤ} (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    qC (⇑f ∣[k] frickeGL (M * ℓ)) =
      qExpand ℂ ℓ (HahnSeries.C ((ℓ : ℂ) ^ (k - 1)) * qC (⇑f ∣[k] frickeGL M)) := by
  have hT : ModularGroup.T ∈ CohCarrier.GammaH M H := CohCarrier.translation_mem_GammaH M H
  rw [slash_frickeGL_mul, ← coe_frickeForm, ← qC_smul hT, ← coe_smul_form,
    ← qC_comp_heckeDiag hT ((((ℓ : ℂ) ^ (k - 1))) • frickeForm f) ℓ]
  congr 1

theorem leg_alpha (hβ : HeckeBetaHDefined M H ℓ)
    (spec : FrickeSpec (CohCarrier.GammaH M H) (frickeGL M) ι w)
    (spec' : FrickeSpec (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) (frickeGL (M * ℓ)) ι w')
    (x : LBC (CohCarrier.GammaH M H)) :
    w' (heckeAlphaHBar Qb M H ℓ x) = heckeBetaHBar Qb M H ℓ (w x) := by
  have hT : ModularGroup.T ∈ CohCarrier.GammaH M H := CohCarrier.translation_mem_GammaH M H
  suffices h : w'.toAlgHom.comp (heckeAlphaHBar Qb M H ℓ) =
      (heckeBetaHBar Qb M H ℓ).comp w.toAlgHom from AlgHom.congr_fun h x
  refine algHom_ext_gen hT fun k f g pf pg hf hg hg0 => Subtype.ext ?_
  set x₀ := gen f g hf hg hg0
  change ((w' (heckeAlphaHBar Qb M H ℓ x₀) : LBC _) : LaurentSeries Qb) =
    ((heckeBetaHBar Qb M H ℓ (w x₀) : LBC _) : LaurentSeries Qb)
  have hg' : qC g ≠ 0 := qC_ne_zero_of_witness hg hg0
  have h0 : coeffMap ι (x₀ : LaurentSeries Qb) * qC g = qC f := gen_rep ι f g hf hg hg0

  have h4 := spec x₀ k f g h0

  have h0' : coeffMap ι ((heckeAlphaHBar Qb M H ℓ x₀ : LBC _) : LaurentSeries Qb) *
      qC (restrictForm (le_top_bot ℓ) g) = qC (restrictForm (le_top_bot ℓ) f) := by
    rw [coe_heckeAlphaHBar M H ℓ x₀]; exact h0
  have h5 := spec' _ k (restrictForm (le_top_bot ℓ) f) (restrictForm (le_top_bot ℓ) g) h0'
  rw [coe_restrictForm, coe_restrictForm, qC_slash_frickeGL_mul, qC_slash_frickeGL_mul] at h5

  apply ModularCurve.FrickeGalois.coeffMap_injective ι
  rw [coe_heckeBetaHBar (M := M) (H := H) (ℓ := ℓ) hβ (w x₀), coeffMap_qExpand]
  have hne : qExpand ℂ ℓ (HahnSeries.C ((ℓ : ℂ) ^ (k - 1)) * qC (⇑g ∣[k] frickeGL M)) ≠ 0 := by
    refine (map_ne_zero_iff (qExpand ℂ ℓ) (qExpand_injective ℓ)).mpr
      (mul_ne_zero ?_ (qC_frickeForm_ne_zero hg'))
    exact (map_ne_zero_iff _ HahnSeries.C_injective).mpr
      (zpow_ne_zero _ (by exact_mod_cast NeZero.ne ℓ))
  apply mul_right_cancel₀ hne
  rw [h5, ← map_mul, mul_left_comm, h4]

theorem leg_beta (hβ : HeckeBetaHDefined M H ℓ)
    (spec : FrickeSpec (CohCarrier.GammaH M H) (frickeGL M) ι w)
    (spec' : FrickeSpec (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) (frickeGL (M * ℓ)) ι w')
    (hw' : ∀ y, w' (w' y) = y) (x : LBC (CohCarrier.GammaH M H)) :
    w' (heckeBetaHBar Qb M H ℓ x) = heckeAlphaHBar Qb M H ℓ (w x) := by
  have h := leg_alpha ι hβ spec spec' (w x)
  rw [apply_apply_of_frickeSpec ι spec] at h
  rw [← h, hw' (heckeAlphaHBar Qb M H ℓ (w x))]

end LawOne

section LawFour

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

omit [NeZero M] in
theorem semilinear_twist (w D : xHFunctionFieldBar M H ≃ₐ[Qb] xHFunctionFieldBar M H)
    (σ : Qb ≃ₐ[ℚ] Qb)
    (h : ∀ x : xHFunctionFieldBar M H,
      w (arithmeticGalois (xHFunctionField M H) σ • x) =
        arithmeticGalois (xHFunctionField M H) σ • D (w x)) :
    SemilinearAut.ofAlgAut w * arithmeticGalois (xHFunctionField M H) σ =
      arithmeticGalois (xHFunctionField M H) σ * SemilinearAut.ofAlgAut D *
        SemilinearAut.ofAlgAut w := by
  refine Subtype.ext (Prod.ext (RingEquiv.ext fun x => ?_) ?_)
  · exact h x
  · change (1 : Qb ≃+* Qb) * σ.toRingEquiv = σ.toRingEquiv * 1 * 1
    rw [one_mul, mul_one, mul_one]

end LawFour

section Assembly

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} (ι : Qb →+* ℂ)
  {w : xHFunctionFieldBar M H ≃ₐ[Qb] xHFunctionFieldBar M H}

theorem lawOne (spec₀ : FrickeSpec (CohCarrier.GammaH M H) (frickeGL M) ι w)
    (child : ∀ (M' : ℕ) [NeZero M'] (H' : Subgroup (ZMod M')ˣ),
      ∃ w : LBC (CohCarrier.GammaH M' H') ≃ₐ[Qb] LBC (CohCarrier.GammaH M' H'),
        FrickeSpec (CohCarrier.GammaH M' H') (frickeGL M') ι w)
    (ℓ : ℕ) [Fact ℓ.Prime] (hβdef : HeckeBetaHDefined M H ℓ)
    (hα : HeckeAlphaHBarIntegral Qb M H ℓ) (hβ : HeckeBetaHBarIntegral Qb M H ℓ)
    [HasPrincipalDivisors Qb (laurentBaseChange Qb (xHTopFunctionFieldC ℚ M H (M * ℓ)))]
    (hFIβ : FundamentalIdentityAlong Qb (heckeBetaHBar Qb M H ℓ) hβ)
    (hfinα : FiniteAlong Qb (heckeAlphaHBar Qb M H ℓ))
    (hNα : NormFormulaAlong Qb (heckeAlphaHBar Qb M H ℓ) hfinα)
    (hFIα : FundamentalIdentityAlong Qb (heckeAlphaHBar Qb M H ℓ) hα)
    (hfinβ : FiniteAlong Qb (heckeBetaHBar Qb M H ℓ))
    (hNβ : NormFormulaAlong Qb (heckeBetaHBar Qb M H ℓ) hfinβ) (x : JH M H) :
    heckePic0HBarTranspose hα hβ hFIα hfinβ hNβ (SemilinearAut.ofAlgAut w • x)
      = SemilinearAut.ofAlgAut w • heckePic0HBar hα hβ hFIβ hfinα hNα x := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  obtain ⟨w', spec', hw'⟩ := exists_top (M := M) (H := H) (ℓ := ℓ) ι child
  let g' : SemilinearAut Qb (laurentBaseChange Qb (xHTopFunctionFieldC ℚ M H (M * ℓ))) :=
    SemilinearAut.ofAlgAut w'
  have h₁ : ∀ y : xHFunctionFieldBar M H,
      g' • heckeAlphaHBar Qb M H ℓ y = heckeBetaHBar Qb M H ℓ (SemilinearAut.ofAlgAut w • y) :=
    fun y => leg_alpha ι hβdef spec₀ spec' y
  have h₂ : ∀ y : xHFunctionFieldBar M H,
      g' • heckeBetaHBar Qb M H ℓ y = heckeAlphaHBar Qb M H ℓ (SemilinearAut.ofAlgAut w • y) :=
    fun y => leg_beta ι hβdef spec₀ spec' hw' y
  exact AlgebraicCurve.SemilinearAut.pic0_correspondence_swap_smul
    (heckeAlphaHBar _ M H ℓ) (heckeBetaHBar _ M H ℓ) hα hβ hFIα hfinβ hNβ hFIβ hfinα hNα h₁ h₂ x

theorem lawTwo (spec₀ : FrickeSpec (CohCarrier.GammaH M H) (frickeGL M) ι w) (d : (ZMod M)ˣ)
    (x : JH M H) :
    diamondHBar M H d (SemilinearAut.ofAlgAut w • diamondHBar M H d x) =
      SemilinearAut.ofAlgAut w • x := by
  have hDwD : diamondAutHBar M H d * w * diamondAutHBar M H d = w :=
    AlgEquiv.ext fun y => diamondAut_fricke_diamondAut ι spec₀ d y
  have key0 : SemilinearAut.ofAlgAut (diamondAutHBar M H d * w * diamondAutHBar M H d) =
      SemilinearAut.ofAlgAut w := congrArg _ hDwD
  rw [MonoidHom.map_mul, MonoidHom.map_mul] at key0
  rw [diamondHBar_apply, diamondHBar_apply]
  calc _ = (SemilinearAut.ofAlgAut (diamondAutHBar M H d) * SemilinearAut.ofAlgAut w *
        SemilinearAut.ofAlgAut (diamondAutHBar M H d)) • x := by rw [mul_smul, mul_smul]
    _ = _ := by rw [key0]

theorem lawThree (spec₀ : FrickeSpec (CohCarrier.GammaH M H) (frickeGL M) ι w) (x : JH M H) :
    SemilinearAut.ofAlgAut w • (SemilinearAut.ofAlgAut w • x) = x := by
  have hww : w * w = 1 := AlgEquiv.ext fun y => apply_apply_of_frickeSpec ι spec₀ y
  have key0 : SemilinearAut.ofAlgAut (w * w) =
      (1 : SemilinearAut Qb (xHFunctionFieldBar M H)) := by rw [hww, MonoidHom.map_one]
  rw [MonoidHom.map_mul] at key0
  rw [← mul_smul, key0, one_smul]

omit [NeZero M] in
theorem lawFour
    (hgal : ∀ (σ : Qb ≃ₐ[ℚ] Qb) (c : ℕ) (hc : c.Coprime M), (∀ ζ : Qb, ζ ^ M = 1 → σ ζ = ζ ^ c) →
      ∀ x : xHFunctionFieldBar M H,
        w (arithmeticGalois (xHFunctionField M H) σ • x) =
          arithmeticGalois (xHFunctionField M H) σ • diamondAutHBar M H (ZMod.unitOfCoprime c hc) (w x))
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (A : ValuationSubring Qb) (hA : A.LiesOverPrime ℓ)
    (σ : Qb ≃ₐ[ℚ] Qb) (hσ : A.IsFrobeniusAt σ ℓ) (x : JH M H) :
    SemilinearAut.ofAlgAut w • (σ • x)
      = σ • diamondHBar M H (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM))
          (SemilinearAut.ofAlgAut w • x) := by
  have hζ : ∀ ζ : Qb, ζ ^ M = 1 → σ ζ = ζ ^ ℓ := fun ζ hζ =>
    ValuationSubring.IsFrobeniusAt.apply_eq_pow_of_pow_eq_one A σ ℓ M hA hσ
      ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM).symm ζ hζ
  have key := semilinear_twist w _ σ (hgal σ ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM) hζ)
  have := congrArg (fun g => g • x) key
  simp only [mul_smul] at this
  rw [galois_smul_pic0_def, galois_smul_pic0_def, diamondHBar_apply]
  exact this

end Assembly

end FrickeAlgEquiv

open FrickeAlgEquiv in
theorem exists_frickeAlgEquiv_xHFunctionFieldBar (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) :
    ∃ w : xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H,
      (∀ (ℓ : ℕ) [Fact ℓ.Prime]
          (hα : HeckeAlphaHBarIntegral (AlgebraicClosure ℚ) M H ℓ)
          (hβ : HeckeBetaHBarIntegral (AlgebraicClosure ℚ) M H ℓ)
          [HasPrincipalDivisors (AlgebraicClosure ℚ)
            (laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ M H (M * ℓ)))]
          (hFIβ : FundamentalIdentityAlong (AlgebraicClosure ℚ)
            (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ) hβ)
          (hfinα : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ))
          (hNα : NormFormulaAlong (AlgebraicClosure ℚ)
            (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ) hfinα)
          (hFIα : FundamentalIdentityAlong (AlgebraicClosure ℚ)
            (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ) hα)
          (hfinβ : FiniteAlong (AlgebraicClosure ℚ) (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ))
          (hNβ : NormFormulaAlong (AlgebraicClosure ℚ)
            (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ) hfinβ)
          (x : JH M H),
        heckePic0HBarTranspose hα hβ hFIα hfinβ hNβ (SemilinearAut.ofAlgAut w • x)
          = SemilinearAut.ofAlgAut w • heckePic0HBar hα hβ hFIβ hfinα hNα x) ∧
      (∀ (d : (ZMod M)ˣ) (x : JH M H),
        diamondHBar M H d (SemilinearAut.ofAlgAut w • diamondHBar M H d x)
          = SemilinearAut.ofAlgAut w • x) ∧
      (∀ x : JH M H, SemilinearAut.ofAlgAut w • (SemilinearAut.ofAlgAut w • x) = x) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (A : ValuationSubring (AlgebraicClosure ℚ)),
        A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            ∀ x : JH M H,
              SemilinearAut.ofAlgAut w • (σ • x)
                = σ • diamondHBar M H
                    (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM))
                    (SemilinearAut.ofAlgAut w • x)) := by
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  let ι : AlgebraicClosure ℚ →+* ℂ :=
    ((IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] ℂ) : AlgebraicClosure ℚ →+* ℂ)

  have hin := fun (M' : ℕ) [NeZero M'] (H' : Subgroup (ZMod M')ˣ) =>
    ModularCurve.heckeDiamondInputsHAll M' H'

  obtain ⟨w, spec, hgal⟩ :=
    ModularCurve.exists_algEquiv_xHFunctionFieldBar_slash_fricke_and_galois_smul M H (hin M H).2 ι
      (FrickeAlgEquiv.frickeGL M) rfl
  have spec₀ : FrickeSpec (CohCarrier.GammaH M H) (FrickeAlgEquiv.frickeGL M) ι w :=
    fun x k f g h => spec x k f g h
  have child : ∀ (M' : ℕ) [NeZero M'] (H' : Subgroup (ZMod M')ˣ),
      ∃ w : LBC (CohCarrier.GammaH M' H') ≃ₐ[AlgebraicClosure ℚ] LBC (CohCarrier.GammaH M' H'),
        FrickeSpec (CohCarrier.GammaH M' H') (FrickeAlgEquiv.frickeGL M') ι w := fun M' _ H' => by
    obtain ⟨w', spec', -⟩ :=
      ModularCurve.exists_algEquiv_xHFunctionFieldBar_slash_fricke_and_galois_smul M' H'
        (hin M' H').2 ι (FrickeAlgEquiv.frickeGL M') rfl
    exact ⟨w', fun x k f g h => spec' x k f g h⟩
  refine ⟨w, fun ℓ _ hα hβ _ hFIβ hfinα hNα hFIα hfinβ hNβ x => ?_, fun d x => lawTwo ι spec₀ d x,
    fun x => lawThree ι spec₀ x,
    fun ℓ hℓ hℓM A hA σ hσ x => lawFour hgal ℓ hℓ hℓM A hA σ hσ x⟩
  obtain ⟨hβdef, -⟩ := (hin M H).1 ℓ Fact.out
  exact lawOne ι spec₀ child ℓ hβdef hα hβ hFIβ hfinα hNα hFIα hfinβ hNβ x

end ModularCurve

end
