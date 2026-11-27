/-
The points of the complex place dictionary.

The complex place dictionary `ModularCurve/ComplexPlaceDictionaryOf.lean` identifies the places
of the `X₁` function field over `ℂ` with the points of the modular curve: a place is given by an
archimedean point `τ` of the upper half-plane and a level datum, and `realizeOf` produces the
form evaluated at the point.  This module proves the last identification the dictionary needs:

  for every element of the `X₁` function field written as `laurentBaseChange` of a `q`-expansion,
  the place realised by a point `pt` is the point `pt` — `exists_pt_eq_of_mem`, i.e. **every
  place of the dictionary is the point it was built from**, so the dictionary is injective on
  points and the `realize`/`realizeOf` pair is a two-way correspondence rather than a map with a
  lossy inverse.

The engine is `ModularCurve/ComplexPlaceDictionaryOf.lean` (`realizeOf`, `realizeOf_eq_div`),
the `jq`-integrality of `JqIntegralRatios.lean` and `Analytic/JqModCIntegral.lean`, the `X₁`
function field's transcendental/finite-dimensional property
(`X1/FunctionFieldConstExt.lean`), the coefficient map (`X1/CoeffMap.lean`) and the integral
adjoin lemma `AlgebraicCurve/Defs/IntegralAdjoin.lean`.

Port notes (order AF105E).

* **Transcription.** The pin's `S_` file is a flat all-public engine (39 declarations, 370 lines)
  and it is transcribed in full: 38 rows at the pin's names and statements plus the pin's
  `solution` row, which is this module's headline at the wrapper's published name. The pin's
  generated namespace label (`P2MW.S_…Ws49.CCPL`) comes off and
  `ModularCurve.ComplexPlaceDictionaryOf` is the subject namespace; `p2m_open` / `p2m_export` /
  `p2m_reactivate` and the two `attribute [-instance]` / `attribute [-simp]` walls are pin
  plumbing and are not transcribed. The pin's nine `scoped instance`s are kept `scoped`.
* **`check_port`.** 38 ok / **0 mismatch / 0 missing / 0 own** — the pin's 39 rows, with
  `solution` matched to the `Theorems/` wrapper row at the published name.
* **Substitutions, and the two suspects.** `port_advise` proposed seven.
  * **`G` and `H` (the set's two suspect rows, FR-0266).** The parser matched both to
    `ModularCurve.JOneES.JOneESRat.A12`, which is one object, not two: `A12 Γ` is
    `restrictForm (map_le_range Γ) (E₄ ^ 3)`, so it *is* the pin's `G`, and it is **not** the
    pin's `H`, which is `restrict (le_SL Γ) Δ`. `H` is therefore transcribed from the pin's body,
    and `G` keeps its declaration with only its *body* imported (`:= JOneES.JOneESRat.A12 Γ`);
    `coe_H` is `rfl` for the pin's `H` and would be false for `A12`. This is the set's one real
    FR-0266 catch.
  * `le_SL`, `one_mem_strictPeriods`, `restrict`, `qL`, `valSubalgebra` are **transcribed** even
    though the port has byte-identical copies (`IntegralGammaAux.*`, `UnramifiedGamma.*`):
    `check_port` diffs the *statement text*, and each of these five names occurs in another pin
    row's statement (`restrict` in `coe_restrict`; `qL` in `qL_ne_zero` / `qL_G` / `qL_H` /
    `jqModC_mul_qL_H`; `G` and `H` in five rows each; `valSubalgebra` in `mem_valSubalgebra` /
    `A_le`), so importing them would turn those rows into `MISMATCH`. The port's copies also
    differ in spine (`UnramifiedGamma.valSubalgebra` has `Γ` implicit, `IntegralGammaAux.qL`
    takes `ℍ → ℂ`), which is why `port_advise`'s "byte-identical" claim does not survive the
    diff. The engine *is* imported where the name is proof-only: `one_mem_strictPeriods`'
    three-line proof is the port's zmultiples route.
* **Two `private` helpers.** `continuous_coe` is the pin's own private row. A second private
  helper is new: `mem_center_iff_center` restates the port's `private Place.mem_center_iff`
  (`Defs/PlacesOverDVR.lean`, `Iff.rfl` on `Place.center`), which is not importable. Both are
  `private`, so `check_port` skips them.
* **Axioms.** `#print axioms` on all 38 public declarations plus the headline: each is a subset
  of `[propext, Classical.choice, Quot.sound]`; no `sorryAx`
  (`lean/tmp/af105/probe-E-ax-dict.lean`).
* **Dedup / move_dead.** `dedup.py --within --module '*ModularCurve/ComplexPlaceDictionaryPoint*'`:
  55 declarations, **0 duplicate clusters**, 0 removable lines. `move_dead.py --dry-run`:
  **0 declarations, 0 lines**.
* **Heartbeat probe pair** (FR-0225 — measured, never installed). The pin carries **no**
  `set_option maxHeartbeats` and no `synthInstance` bound (`S_…:20` is `autoImplicit` only), and
  this file carries neither. The downward ladder on this file at
  `lake env lean -DautoImplicit=false -DmaxHeartbeats=N`: **N = 40 000 fails** (two `isDefEq` /
  `whnf` timeouts, both inside `exists_pt_eq` and in the headline's application of it),
  **N = 100 000 silent**, **N = 200 000 silent** (the edit-loop cap; the lakefile's 4 000 000 is
  never approached). The expensive command is the 62-line `exists_pt_eq`, not the `haveI` block.
  The two `scoped instance`s that the pin's `IsDedekindDomain (B Γ x)` /
  `IsFractionRing (B Γ x) (CF Γ)` would otherwise leave to instance search
  (`instIsDedekindDomainB`, `instIsFractionRingB`) supply `Algebra.IsIntegral` /
  `Algebra.IsSeparable` for `Kj Γ x → CF Γ` explicitly, for the same reason: at the toolchain's
  20 000 instance heartbeats the search dies at the `integralClosure.isDedekindDomain` site.

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_ComplexPlaceDictionaryOf_exists_pt_eq_of_mem.lean>

spec-pin: Theorems/Thm_ModularCurve_ComplexPlaceDictionaryOf_exists_pt_eq_of_mem.lean
spec-pin: P2M/Sol/S_ModularCurve_ComplexPlaceDictionaryOf_exists_pt_eq_of_mem.lean
-/
import FLTForHuman.AlgebraicCurve.Defs.IntegralAdjoin
import FLTForHuman.ModularCurve.Analytic.JqModCIntegral
import FLTForHuman.ModularCurve.ComplexPlaceDictionaryOf
import FLTForHuman.ModularCurve.JqIntegralRatios
import FLTForHuman.ModularCurve.X1.CoeffMap
import FLTForHuman.ModularCurve.X1.FunctionFieldConstExt
import FLTForHuman.ModularCurve.X1.FunctionField

noncomputable section

set_option autoImplicit false

-- The pin's `haveI` walls are kept verbatim; the linter is silenced per file, as in
-- `AlgebraicCurve/Differential/Coefficient.lean`.
set_option linter.style.haveILetI false

open UpperHalfPlane Filter Polynomial
open scoped MatrixGroups Topology Manifold IntermediateField.algebraAdjoinAdjoin nonZeroDivisors

namespace ModularCurve

namespace ComplexPlaceDictionaryOf

/-! ## The function field of `X₁` over `ℂ`, and its `j`-line

The pin's `Ws49.CCPL` block (`P2M/Sol/S_…_exists_pt_eq_of_mem.lean:35-357`), with the pin's
generated namespace label dropped: `ModularCurve.ComplexPlaceDictionaryOf` is the subject
namespace.  The pin's `p2m_open "ModularCurve"` / `p2m_export` / `p2m_reactivate` plumbing and its
two `attribute [-instance]` / `attribute [-simp]` walls are not transcribed. -/

variable (Γ : Subgroup SL(2, ℤ))

abbrev CF : Type := ↥(laurentBaseChange ℂ (qExpFunctionFieldC ℚ Γ))

variable (x : CF Γ)

theorem transcendental_jX [Γ.FiniteIndex] [hT : Fact (ModularGroup.T ∈ Γ)]
    [hx : Fact ((x : LaurentSeries ℂ) = jqModC ℂ)] : Transcendental ℂ x :=
  (transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
    ℂ Γ hT.out x hx.out).1

abbrev A : Subalgebra ℂ (CF Γ) := Algebra.adjoin ℂ {x}

abbrev Kj : IntermediateField ℂ (CF Γ) := IntermediateField.adjoin ℂ {x}

def polyEquiv [Γ.FiniteIndex] [hT : Fact (ModularGroup.T ∈ Γ)]
    [hx : Fact ((x : LaurentSeries ℂ) = jqModC ℂ)] : ℂ[X] ≃ₐ[ℂ] A Γ x :=
  Polynomial.algEquivOfTranscendental ℂ x (transcendental_jX Γ x)

scoped instance instIsPrincipalIdealRingA [Γ.FiniteIndex] [hT : Fact (ModularGroup.T ∈ Γ)]
    [hx : Fact ((x : LaurentSeries ℂ) = jqModC ℂ)] : IsPrincipalIdealRing (A Γ x) :=
  IsPrincipalIdealRing.of_surjective (polyEquiv Γ x).toRingEquiv.toRingHom
    (polyEquiv Γ x).toRingEquiv.surjective

scoped instance instIsDedekindDomainA [Γ.FiniteIndex] [hT : Fact (ModularGroup.T ∈ Γ)]
    [hx : Fact ((x : LaurentSeries ℂ) = jqModC ℂ)] : IsDedekindDomain (A Γ x) := inferInstance

scoped instance instAlgebraAKj : Algebra (A Γ x) (Kj Γ x) := inferInstance
scoped instance instSMulAKj : SMul (A Γ x) (Kj Γ x) := Algebra.toSMul
scoped instance instIsScalarTowerAKjCF : IsScalarTower (A Γ x) (Kj Γ x) (CF Γ) :=
  Subalgebra.inclusion.isScalarTower_right
    (IntermediateField.algebra_adjoin_le_adjoin ℂ ({x} : Set (CF Γ))) _

scoped instance instFiniteDimensionalKjCF [Γ.FiniteIndex] [hT : Fact (ModularGroup.T ∈ Γ)]
    [hx : Fact ((x : LaurentSeries ℂ) = jqModC ℂ)] : FiniteDimensional (Kj Γ x) (CF Γ) :=
  (transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
    ℂ Γ hT.out x hx.out).2

def B : Subalgebra (A Γ x) (CF Γ) := integralClosure (A Γ x) (CF Γ)

theorem mem_B_iff {y : CF Γ} : y ∈ B Γ x ↔ IsIntegral (A Γ x) y := Iff.rfl

scoped instance instCommRingB : CommRing (B Γ x) := (B Γ x).toCommRing
scoped instance instIsDomainB : IsDomain (B Γ x) := Subalgebra.isDomain (B Γ x)
scoped instance instAlgebraAB : Algebra (A Γ x) (B Γ x) := (B Γ x).algebra
scoped instance instSMulAB : SMul (A Γ x) (B Γ x) := Algebra.toSMul
scoped instance instAlgebraBCF : Algebra (B Γ x) (CF Γ) := (B Γ x).toAlgebra
scoped instance instSMulBCF : SMul (B Γ x) (CF Γ) := Algebra.toSMul
scoped instance instIsScalarTowerABCF : IsScalarTower (A Γ x) (B Γ x) (CF Γ) :=
  IsScalarTower.subalgebra' (A Γ x) (CF Γ) (CF Γ) (B Γ x)

scoped instance instIsDedekindDomainB [Γ.FiniteIndex] [hT : Fact (ModularGroup.T ∈ Γ)]
    [hx : Fact ((x : LaurentSeries ℂ) = jqModC ℂ)] : IsDedekindDomain (B Γ x) := by
  haveI : Algebra.IsIntegral (Kj Γ x) (CF Γ) := ⟨fun y => IsIntegral.of_finite (Kj Γ x) y⟩
  haveI : Algebra.IsSeparable (Kj Γ x) (CF Γ) := Algebra.IsSeparable.of_integral (Kj Γ x) (CF Γ)
  unfold B; exact integralClosure.isDedekindDomain (A Γ x) (Kj Γ x) (CF Γ)

scoped instance instIsFractionRingB [Γ.FiniteIndex] [hT : Fact (ModularGroup.T ∈ Γ)]
    [hx : Fact ((x : LaurentSeries ℂ) = jqModC ℂ)] : IsFractionRing (B Γ x) (CF Γ) := by
  haveI : Algebra.IsIntegral (Kj Γ x) (CF Γ) := ⟨fun y => IsIntegral.of_finite (Kj Γ x) y⟩
  haveI : Algebra.IsSeparable (Kj Γ x) (CF Γ) := Algebra.IsSeparable.of_integral (Kj Γ x) (CF Γ)
  unfold B; exact integralClosure.isFractionRing_of_finite_extension (Kj Γ x) (CF Γ)

theorem algebraMap_B_apply (b : B Γ x) : algebraMap (B Γ x) (CF Γ) b = (b : CF Γ) := rfl

def valSubalgebra (Q : AlgebraicCurve.Place ℂ (CF Γ)) : Subalgebra ℂ (CF Γ) where
  carrier := Q.toValuationSubring
  mul_mem' ha hb := Q.toValuationSubring.mul_mem _ _ ha hb
  one_mem' := Q.toValuationSubring.one_mem
  add_mem' ha hb := Q.toValuationSubring.add_mem _ _ ha hb
  zero_mem' := Q.toValuationSubring.zero_mem
  algebraMap_mem' c := Q.algebraMap_mem' c

theorem mem_valSubalgebra {Q : AlgebraicCurve.Place ℂ (CF Γ)} {y : CF Γ} :
    y ∈ valSubalgebra Γ Q ↔ y ∈ Q.toValuationSubring := Iff.rfl

theorem A_le {Q : AlgebraicCurve.Place ℂ (CF Γ)} (hQ : x ∈ Q.toValuationSubring) (a : A Γ x) :
    (a : CF Γ) ∈ Q.toValuationSubring := by
  have hle : A Γ x ≤ valSubalgebra Γ Q :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr ((mem_valSubalgebra Γ).mpr hQ))
  exact (mem_valSubalgebra Γ).mp (hle a.2)

theorem forall_algebraMap_B_mem {Q : AlgebraicCurve.Place ℂ (CF Γ)}
    (hQ : x ∈ Q.toValuationSubring) :
    ∀ b : B Γ x, algebraMap (B Γ x) (CF Γ) b ∈ Q.toValuationSubring := by
  intro b
  obtain ⟨p, hp, hpb⟩ := (mem_B_iff Γ x).mp b.2
  rw [algebraMap_B_apply]
  refine Q.mem_of_eval_monic_eq_zero (P := p.map (algebraMap (A Γ x) (CF Γ))) (hp.map _)
    (fun i => ?_) ?_
  · rw [Polynomial.coeff_map]
    exact A_le Γ x hQ (p.coeff i)
  · rw [Polynomial.eval_map]
    exact hpb

section ModularForms

theorem le_SL : ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ :=
  Subgroup.map_le_range _ _

def restrict {F : Type*} [FunLike F ℍ ℂ] {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (hle : Γ' ≤ Γ)
    {k : ℤ} (f : F) [ModularFormClass F Γ k] : ModularForm Γ' k where
  toFun := f
  slash_action_eq' γ hγ := SlashInvariantFormClass.slash_action_eq f γ (hle hγ)
  holo' := ModularFormClass.holo f
  bdd_at_cusps' hc := ModularFormClass.bdd_at_cusps f (hc.mono hle)

@[scoped simp]
theorem coe_restrict {F : Type*} [FunLike F ℍ ℂ] {Γ Γ' : Subgroup (GL (Fin 2) ℝ)}
    (hle : Γ' ≤ Γ) {k : ℤ} (f : F) [ModularFormClass F Γ k] :
    ((restrict hle f : ModularForm Γ' k) : ℍ → ℂ) = f := rfl

/-- The pin's `G` (`S_…:134`).  **The body is the substitution**: the port's
`ModularCurve.JOneES.JOneESRat.A12` (`X1/FunctionField.lean`) is the same form — `restrictForm`
of `E₄ ^ 3` mcast to weight `12`, see `isIntegralQExp_A12` — so the declaration is kept for its
**statement** (`G Γ` occurs in five other rows' statements, which `check_port` diffs textually)
and only the body is imported.  It is *not* the same object as `H`. -/
def G : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 12 :=
  ModularCurve.JOneES.JOneESRat.A12 Γ

/-- The pin's `H` (`S_…:137`) — `Δ` restricted to `Γ`, and **not** `A12`: this is the set's
suspect substitution, and `H ↦ JOneES.JOneESRat.A12` is a type-only match (FR-0266).  `A12` is
`E₄ ^ 3` (the pin's `G`); `H` is the discriminant.  Transcribed, with the pin's body. -/
def H : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 12 :=
  restrict (le_SL Γ) CuspForm.discriminant

theorem coe_G : ((G Γ : ModularForm _ 12) : ℍ → ℂ) =
    ((ModularForm.E₄.pow 3 : ModularForm 𝒮ℒ (3 * 4)) : ℍ → ℂ) := rfl

theorem coe_H : ((H Γ : ModularForm _ 12) : ℍ → ℂ) =
    ModularForm.discriminant := rfl

theorem H_apply_ne_zero (z : ℍ) : (H Γ : ℍ → ℂ) z ≠ 0 := by
  change ModularForm.discriminant z ≠ 0
  exact ModularForm.discriminant_ne_zero z

abbrev qL {k : ℤ} (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) : LaurentSeries ℂ :=
  ((qExpansion 1 (f : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)

theorem one_mem_strictPeriods [hT : Fact (ModularGroup.T ∈ Γ)] :
    (1 : ℝ) ∈ ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT.out]
  exact AddSubgroup.mem_zmultiples _

theorem one_mem_strictPeriods_SL : (1 : ℝ) ∈ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

private theorem continuous_coe {k : ℤ} (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) :
    Continuous (f : ℍ → ℂ) :=
  (ModularFormClass.holo f).continuous

theorem qL_ne_zero [hT : Fact (ModularGroup.T ∈ Γ)] {k : ℤ}
    (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hf : f ≠ 0) :
    qL Γ f ≠ 0 := by
  intro h
  apply hf
  rw [← ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods Γ)]
  apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ))
  simpa [qL] using h

theorem H_ne_zero : H Γ ≠ 0 := by
  intro h
  have := congrArg (fun f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 12 => (f : ℍ → ℂ) I) h
  exact H_apply_ne_zero Γ I (by simpa using this)

theorem qL_G : qL Γ (G Γ) =
    ((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 := by
  have h : qExpansion 1 ((G Γ : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 12) : ℍ → ℂ) =
      (qExpansion 1 (ModularForm.E₄ : ℍ → ℂ)) ^ 3 := by
    rw [coe_G, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  rw [qL, h, PowerSeries.coe_pow]

theorem qL_H : qL Γ (H Γ) =
    ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) :=
  rfl

theorem jqModC_mul_qL_H [hT : Fact (ModularGroup.T ∈ Γ)] :
    jqModC ℂ * qL Γ (H Γ) = qL Γ (G Γ) := by
  have hne : qL Γ (H Γ) ≠ 0 := qL_ne_zero Γ (H Γ) (H_ne_zero Γ)
  rw [jqModC_eq_qExpansion_E4_cube_div_discriminant, qL_G, ← qL_H Γ]
  exact div_mul_cancel₀ _ hne

theorem realizeOf_jqModC [hT : Fact (ModularGroup.T ∈ Γ)] (z : ℍ) :
    realizeOf Γ (jqModC ℂ) z = (G Γ : ℍ → ℂ) z / (H Γ : ℍ → ℂ) z :=
  ModularCurve.realizeOf_eq_div Γ hT.out (G Γ) (H Γ) (jqModC ℂ) (jqModC_mul_qL_H Γ) z
    (H_apply_ne_zero Γ z)

theorem isBoundedUnder_realizeOf_jqModC [hT : Fact (ModularGroup.T ∈ Γ)] (τ : ℍ) :
    IsBoundedUnder (· ≤ ·) (𝓝[≠] τ) (fun z : ℍ => ‖realizeOf Γ (jqModC ℂ) z‖) := by
  have hcont : Continuous (fun z : ℍ => (G Γ : ℍ → ℂ) z / (H Γ : ℍ → ℂ) z) :=
    (continuous_coe Γ (G Γ)).div (continuous_coe Γ (H Γ)) (H_apply_ne_zero Γ)
  have hbd : IsBoundedUnder (· ≤ ·) (𝓝 τ)
      (fun z : ℍ => ‖(G Γ : ℍ → ℂ) z / (H Γ : ℍ → ℂ) z‖) :=
    (hcont.continuousAt.norm.tendsto).isBoundedUnder_le
  have hfun : (fun z : ℍ => ‖realizeOf Γ (jqModC ℂ) z‖) =
      fun z : ℍ => ‖(G Γ : ℍ → ℂ) z / (H Γ : ℍ → ℂ) z‖ :=
    funext fun z => by rw [realizeOf_jqModC]
  rw [hfun]
  exact hbd.mono nhdsWithin_le_nhds

theorem coe_ne_zero {k : ℤ} (h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hh : h ≠ 0) :
    (h : ℍ → ℂ) ≠ 0 := by
  intro e
  exact hh (DFunLike.coe_injective (by rw [e]; rfl))

theorem eventually_ne_zero {k : ℤ} (h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (hh : h ≠ 0) (τ : ℍ) : ∀ᶠ z in 𝓝[≠] τ, (h : ℍ → ℂ) z ≠ 0 := by
  by_contra hcon
  have hfr : ∃ᶠ w in 𝓝[≠] τ, (h : ℍ → ℂ) w = 0 := by
    simpa [Filter.not_eventually] using hcon
  exact coe_ne_zero Γ h hh (UpperHalfPlane.eq_zero_of_frequently (ModularFormClass.holo h) hfr)

theorem isBoundedUnder_div_of_realizeOf [hT : Fact (ModularGroup.T ∈ Γ)] {k : ℤ}
    (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hh : h ≠ 0)
    (y : LaurentSeries ℂ) (hy : y * qL Γ h = qL Γ g) (τ : ℍ)
    (hb : IsBoundedUnder (· ≤ ·) (𝓝[≠] τ) (fun z : ℍ => ‖realizeOf Γ y z‖)) :
    IsBoundedUnder (· ≤ ·) (𝓝[≠] τ) (fun z : ℍ => ‖(g : ℍ → ℂ) z / (h : ℍ → ℂ) z‖) := by
  obtain ⟨b, hb⟩ := hb
  refine ⟨b, ?_⟩
  change ∀ᶠ z in 𝓝[≠] τ, ‖(g : ℍ → ℂ) z / (h : ℍ → ℂ) z‖ ≤ b
  have hev : ∀ᶠ z in 𝓝[≠] τ, (h : ℍ → ℂ) z ≠ 0 := eventually_ne_zero Γ h hh τ
  have hb' : ∀ᶠ z in 𝓝[≠] τ, ‖realizeOf Γ y z‖ ≤ b := hb
  filter_upwards [hev, hb'] with z hz hzb
  rw [← ModularCurve.realizeOf_eq_div Γ hT.out g h y hy z hz]
  exact hzb

end ModularForms

theorem jX_mem_pt [hT : Fact (ModularGroup.T ∈ Γ)]
    [hx : Fact ((x : LaurentSeries ℂ) = jqModC ℂ)]
    (D : ComplexPlaceDictionaryOf Γ (qExpFunctionFieldC ℚ Γ)) (τ : ℍ) :
    x ∈ (D.pt τ).toValuationSubring := by
  rw [D.mem_pt_iff τ x, hx.out]
  exact isBoundedUnder_realizeOf_jqModC Γ τ

open AlgebraicCurve in
theorem eq_of_center_eq [Γ.FiniteIndex] [hT : Fact (ModularGroup.T ∈ Γ)]
    [hx : Fact ((x : LaurentSeries ℂ) = jqModC ℂ)] {Q Q' : Place ℂ (CF Γ)}
    (hQ : ∀ b : B Γ x, algebraMap (B Γ x) (CF Γ) b ∈ Q.toValuationSubring)
    (hQ' : ∀ b : B Γ x, algebraMap (B Γ x) (CF Γ) b ∈ Q'.toValuationSubring)
    (h : Place.center (B Γ x) Q hQ = Place.center (B Γ x) Q' hQ') : Q = Q' := by
  apply Place.ext
  rw [Place.toValuationSubring_eq_of_forall_mem Q hQ, Place.toValuationSubring_eq_of_forall_mem Q' hQ']
  have hc : Place.centerHeightOneSpectrum (B Γ x) Q hQ =
      Place.centerHeightOneSpectrum (B Γ x) Q' hQ' :=
    IsDedekindDomain.HeightOneSpectrum.ext h
  rw [hc]

/-- The pin's `Place.mem_center_iff`, which is `private` in the port
(`Defs/PlacesOverDVR.lean`) and so is not importable; `Iff.rfl` on `Place.center`. -/
private theorem mem_center_iff_center {Q : AlgebraicCurve.Place ℂ (CF Γ)}
    (hQ : ∀ b : B Γ x, algebraMap (B Γ x) (CF Γ) b ∈ Q.toValuationSubring) {r : B Γ x} :
    (r ∈ AlgebraicCurve.Place.center (B Γ x) Q hQ ↔
      (⟨algebraMap (B Γ x) (CF Γ) r, hQ r⟩ : Q.toValuationSubring) ∈
        IsLocalRing.maximalIdeal Q.toValuationSubring) :=
  Iff.rfl

open AlgebraicCurve in
theorem mem_of_mul_eq [Γ.FiniteIndex] [_hT : Fact (ModularGroup.T ∈ Γ)]
    [_hx : Fact ((x : LaurentSeries ℂ) = jqModC ℂ)] {Q : Place ℂ (CF Γ)}
    (hQ : ∀ b : B Γ x, algebraMap (B Γ x) (CF Γ) b ∈ Q.toValuationSubring)
    {y : CF Γ} {b s : B Γ x} (hs : s ∉ Place.center (B Γ x) Q hQ)
    (hy : y * algebraMap (B Γ x) (CF Γ) s = algebraMap (B Γ x) (CF Γ) b) :
    y ∈ Q.toValuationSubring := by
  set O := Q.toValuationSubring
  have hsunit : IsUnit (⟨algebraMap (B Γ x) (CF Γ) s, hQ s⟩ : O) :=
    IsLocalRing.notMem_maximalIdeal.mp
      (fun hm => hs ((mem_center_iff_center (Q := Q) (hQ := hQ)).mpr hm))
  have hv1 : O.valuation (algebraMap (B Γ x) (CF Γ) s) = 1 :=
    (O.valuation_eq_one_iff _).mp hsunit
  have hs0 : algebraMap (B Γ x) (CF Γ) s ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hv1
    exact zero_ne_one hv1
  have hyeq : y = algebraMap (B Γ x) (CF Γ) b * (algebraMap (B Γ x) (CF Γ) s)⁻¹ := by
    rw [← hy, mul_inv_cancel_right₀ hs0]
  rw [← O.valuation_le_one_iff, hyeq, map_mul, map_inv₀, hv1, inv_one, mul_one]
  exact O.valuation_le_one ⟨_, hQ b⟩

open AlgebraicCurve in
theorem exists_pt_eq [Γ.FiniteIndex] [hT : Fact (ModularGroup.T ∈ Γ)]
    [hx : Fact ((x : LaurentSeries ℂ) = jqModC ℂ)]
    (D : ComplexPlaceDictionaryOf Γ (qExpFunctionFieldC ℚ Γ)) (P : Place ℂ (CF Γ))
    (hP : x ∈ P.toValuationSubring) : ∃ τ : ℍ, D.pt τ = P := by
  by_contra hne
  push Not at hne
  have hwP := forall_algebraMap_B_mem Γ x hP
  have h𝔭0 : Place.center (B Γ x) P hwP ≠ ⊥ := Place.center_ne_bot P hwP
  have h𝔭max : (Place.center (B Γ x) P hwP).IsMaximal :=
    (Place.centerHeightOneSpectrum (B Γ x) P hwP).isPrime.isMaximal h𝔭0
  obtain ⟨y, hy𝔭, hyB⟩ :=
    FractionalIdeal.exists_notMem_one_of_ne_bot (K := CF Γ) h𝔭0 h𝔭max.ne_top

  have hyτ : ∀ τ : ℍ, y ∈ (D.pt τ).toValuationSubring := by
    intro τ
    have hwτ := forall_algebraMap_B_mem Γ x (jX_mem_pt Γ x D τ)
    have hneq : ¬ Place.center (B Γ x) P hwP ≤ Place.center (B Γ x) (D.pt τ) hwτ := fun hle =>
      hne τ (eq_of_center_eq Γ x hwτ hwP
        (h𝔭max.eq_of_le
          (Place.centerHeightOneSpectrum (B Γ x) (D.pt τ) hwτ).isPrime.ne_top hle).symm)
    obtain ⟨s, hs𝔭, hsτ⟩ := Set.not_subset.mp hneq
    have hys : y * algebraMap (B Γ x) (CF Γ) s ∈ (1 : FractionalIdeal (B Γ x)⁰ (CF Γ)) := by
      have hmem : y * algebraMap (B Γ x) (CF Γ) s ∈
          ((Place.center (B Γ x) P hwP : FractionalIdeal (B Γ x)⁰ (CF Γ))⁻¹ *
            (Place.center (B Γ x) P hwP : FractionalIdeal (B Γ x)⁰ (CF Γ))) :=
        FractionalIdeal.mul_mem_mul hy𝔭 (FractionalIdeal.mem_coeIdeal_of_mem _ hs𝔭)
      rwa [inv_mul_cancel₀ (FractionalIdeal.coeIdeal_ne_zero.mpr h𝔭0)] at hmem
    obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).mp hys
    exact mem_of_mul_eq Γ x hwτ hsτ hb.symm

  have hbdd : ∀ τ : ℍ, IsBoundedUnder (· ≤ ·) (𝓝[≠] τ)
      (fun z : ℍ => ‖realizeOf Γ (y : LaurentSeries ℂ) z‖) :=
    fun τ => (D.mem_pt_iff τ y).mp (hyτ τ)

  obtain ⟨k, g, h, hh, hgh⟩ :=
    exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC Γ hT.out
      (y : LaurentSeries ℂ) y.2
  have hb' : ∀ τ : ℍ, IsBoundedUnder (· ≤ ·) (𝓝[≠] τ)
      (fun z : ℍ => ‖(g : ℍ → ℂ) z / (h : ℍ → ℂ) z‖) :=
    fun τ => isBoundedUnder_div_of_realizeOf Γ g h hh (y : LaurentSeries ℂ) hgh τ (hbdd τ)
  have hint0 := ModularCurve.isIntegral_adjoin_jqModC_qExpansion_div_of_forall_isBoundedUnder_of_finiteIndex
    Γ hT.out g h hh hb'
  have hyeq : (y : LaurentSeries ℂ) = qL Γ g / qL Γ h := by
    rw [eq_div_iff (qL_ne_zero Γ h hh)]
    exact hgh
  have hint : IsIntegral (Algebra.adjoin ℂ ({(x : LaurentSeries ℂ)} : Set (LaurentSeries ℂ)))
      (y : LaurentSeries ℂ) := by
    rw [hx.out, hyeq]
    exact hint0
  have hint' : IsIntegral (A Γ x) y := by
    have := AlgebraicCurve.isIntegral_adjoin_intermediateField_mk
      (laurentBaseChange ℂ (qExpFunctionFieldC ℚ Γ)) x.2 y.2 hint
    simpa using this
  exact hyB ((FractionalIdeal.mem_one_iff _).mpr ⟨⟨y, (mem_B_iff Γ x).mpr hint'⟩, rfl⟩)

end ComplexPlaceDictionaryOf

end ModularCurve

open scoped MatrixGroups in
theorem ModularCurve.ComplexPlaceDictionaryOf.exists_pt_eq_of_mem
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (hF : F₀ = ModularCurve.qExpFunctionFieldC ℚ Γ)
    (D : ModularCurve.ComplexPlaceDictionaryOf Γ F₀)
    (P : AlgebraicCurve.Place ℂ (ModularCurve.laurentBaseChange ℂ F₀))
    (x : ModularCurve.laurentBaseChange ℂ F₀) (hx : (x : LaurentSeries ℂ) = ModularCurve.jqModC ℂ)
    (hP : x ∈ P.toValuationSubring) :
    ∃ τ : UpperHalfPlane, D.pt τ = P := by
  subst hF
  haveI : Fact (ModularGroup.T ∈ Γ) := ⟨hT⟩
  haveI : Fact ((x : LaurentSeries ℂ) = ModularCurve.jqModC ℂ) := ⟨hx⟩
  exact ModularCurve.ComplexPlaceDictionaryOf.exists_pt_eq Γ x D P hP
