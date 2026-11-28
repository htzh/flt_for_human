/-
Fourier inversion on the finite adèle ring, and the Schwartz property of its Schwartz space.

Let `ν` be a Haar measure on `FiniteAdeleRing (𝓞 F) F` and `ψ` a global additive character whose
archimedean component is the standard character (`hψ_inf`). Then:

* `fourierIntegral` inverts on the locally constant compactly supported functions, up to the constant
  `|N(differentIdeal ℤ (𝓞 F))| · ν(integralFiniteAdeles)²` and the sign `y ↦ -y`;
* the Fourier transform of such a function is again locally constant with compact support.

The pin's proof reduces both to the indicator functions of the principal cosets of
`integralFiniteAdeles`, where the transform is computed in `FiniteCoset.lean` and the inversion is the
Poisson summation over a lattice.

Assumes, from earlier modules: `NumberTheory/AdelicFourier/Transform` (`fourierIntegral`),
`FiniteCoset`, `TraceDual`, `NumberTheory/AdelicBox`, and `NumberField/GlobalAddChar`
(`IsGlobalAddChar`).

Transcribed from the two pins below (pinned `aa2d8b3`, 394 + 260 `S_` lines).

## The rows

* `NumberField.AdelicFourier.fourierIntegral_fourierIntegral_finiteAdeleRing_eq` — 394 pin `S_` lines.
* `NumberField.AdelicFourier.isLocallyConstant_and_hasCompactSupport_fourierIntegral_finiteAdeleRing` — 260 pin `S_` lines.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_NumberField_AdelicFourier_fourierIntegral_fourierIntegral_finiteAdeleRing_eq.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_NumberField_AdelicFourier_isLocallyConstant_and_hasCompactSupport_fourierIntegral_finiteAdeleRing.lean>

spec-pin: Theorems/Thm_NumberField_AdelicFourier_fourierIntegral_fourierIntegral_finiteAdeleRing_eq.lean
spec-pin: P2M/Sol/S_NumberField_AdelicFourier_fourierIntegral_fourierIntegral_finiteAdeleRing_eq.lean
spec-pin: Theorems/Thm_NumberField_AdelicFourier_isLocallyConstant_and_hasCompactSupport_fourierIntegral_finiteAdeleRing.lean
spec-pin: P2M/Sol/S_NumberField_AdelicFourier_isLocallyConstant_and_hasCompactSupport_fourierIntegral_finiteAdeleRing.lean

## The two flat public surfaces

The pins are two `S_` preludes, and both are **flat public surfaces** (20 and 11 declarations), so their
helpers are transcribed public at the pin's names:

* `…fourierIntegral_fourierIntegral_finiteAdeleRing_eq.lean` — the annihilator subgroup
  (`annSubgroup` and its six lemmas), the multiplicative-additive dictionary (`mulEquiv`), the finite
  sum lemma, and the coset/measure computation closed by `fourierIntegral_fourierIntegral_eq`;
* `…isLocallyConstant_and_hasCompactSupport_fourierIntegral_finiteAdeleRing.lean` — the coset-translation
  dictionary (`add_mem_image_iff`, `sum_apply_add_eq`, `exists_mem_image_of_sum_ne_zero`) and the two
  halves of the Schwartz property.

The pins' generated label namespaces (`…Ws25FinInv`, `…Ws25.Sfin`) collapse into
`NumberField.AdelicFourier` — the two `S_` files declare disjoint names, so nothing collides.

## Substitutions (imported, not restated)

Five of the second pin's eleven declarations and one of the first pin's twenty already exist publicly in
the port; they are imported rather than re-proved (the `port_advise` *substitute* tier):

| pin row | port declaration |
|---|---|
| `addChar_neg_eq_one_iff` (file 1) | `NumberField.AdelicFourier.addChar_neg_eq_one_iff` (`FiniteCoset.lean`) |
| `add_mem_integralFiniteAdeles` | `NumberField.AdelicBox.BoxKernel.add_mem_integralFiniteAdeles` (`AdelicBox/Measure.lean`) |
| `neg_mem_integralFiniteAdeles` | `NumberField.AdelicBox.BoxKernel.neg_mem_integralFiniteAdeles` |
| `sub_mem_integralFiniteAdeles` | `NumberField.AdelicBox.BoxIndex.sub_mem'` |
| `mul_mem_integralFiniteAdeles` | `NumberField.AdelicFourier.mul_mem_integralFiniteAdeles` (`TraceDual.lean`) |
| `zero_mem_integralFiniteAdeles` | `NumberField.AdelicFourier.zero_mem_integralFiniteAdeles'` (`AdelicFourier/Space.lean`) |

The pin's `zero_mem_integralFiniteAdeles` is the `AdelicBox` set; `AdelicDiscreteness.lean`'s copy of the
name is the `AdelicLevel` set (`AdelicLevel.integralFiniteAdeles`), a different constant, so it is not
the substitute here.

## Port deltas (proof-level only, none a statement change)

* The pins' `p2m_open`/`p2m_export` scaffolding is pin machinery and is not transcribed; the namespace
  it simulated is this module's.
* The pin writes `Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure` and
  `Measure.addHaarScalarFactor`; both are the port's mathlib names.
* `Complex.real_smul` is `RCLike.real_smul_eq_coe_mul` in the port's mathlib `v4.34.0`.
* `AddEquiv.isAddHaarMeasure_map` takes the measure first and the equivalence second
  (`… ν (mulEquiv a b hab) he hes`), which is the pin's argument order; `Measure.addHaarScalarFactor`
  and `Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure` are the port's names.
* The two headlines keep their explicit `[MeasurableSpace …] [BorelSpace …]` binders (the pin writes
  them) and the `hψ_inf` hypothesis, which is **not** discharged here.
* `Set.mem_setOf_eq` is deprecated in the port's mathlib (2026-07-09) → `Set.mem_ofPred_eq`;
  `if_pos`/`if_neg` are deprecated → `ite_eq_left`/`ite_eq_right`; `def mulEquiv` must be written
  `noncomputable def` (its codomain carries the noncomputable `CommRing (FiniteAdeleRing _ _)`).
* The pin's `haveI : (_).IsAddHaarMeasure` is a `have` here: a local hypothesis of class type is
  already an instance (FR-0323), and `haveI` on a proposition trips `linter.style.haveILetI`.
* The pin's `key …` is applied at its point (`key … w`) before `rw [add_sub_cancel]`: the port's `rw`
  does not rewrite under a trailing `∀`.
* `Set.image_add_left` + `measure_preimage_add` (the pin's `hS` step) are the port's own
  `BoxIndex.measure_image_add_left` idiom; `BoxIndex.sub_mem'` and
  `BoxKernel.add_mem_integralFiniteAdeles` take `F` explicitly.

## Landing (SET-AF112C, pin `aa2d8b3` against the port's mathlib `v4.34.0`)

* **Surface.** **25** public declarations, no `private` prelude: 18 helpers + the row-1 headline from
  the first pin `S_` file, and 5 helpers + the row-2 headline from the second. The other **6** pin
  publics are the substitutions imported above (`addChar_neg_eq_one_iff` and the five
  `…_mem_integralFiniteAdeles` rows) — the pin's 20 + 11 = 31 surface, 25 declared + 6 imported.
* **Lines.** 674 against the pin's two `S_` blocks' 394 + 260 = 654 (the balance is the doc header and
  the two substitutions' table).
* **`check_port --force`.** **`25 ok, 0 mismatch, 0 missing, 0 own, 0 kw`** — every declaration matches
  its pin statement at `P2M/Sol/S_…:51–360` (file 1) and `:50–244` (file 2), and both headlines match
  their `Theorems/` wrappers. No `own:`/`pin:` marker is needed.
* **Edit loop.** `timeout 110 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` →
  **silent, exit 0**; no `sorry`, no deprecation, no linter warning. The pin's
  `set_option maxHeartbeats 1600000` is **not** installed and no ladder was run: nothing blew up.
* **`lake build`.** `flock tmp/af112/build.lock timeout 600 lake build
  FLTForHuman.NumberTheory.AdelicFourier.FourierInversion` → **exit 0**, `Built … (7.2s)`; log
  `tmp/af112/logs/C-fourierinversion-build.log`, no `warning` line in it.
* **Axioms.** `#print axioms` on both headlines → `[propext, Classical.choice, Quot.sound]`, no
  `sorryAx`.
* **`dedup`.** 25 declarations, **0 duplicate clusters, 0 removable lines** (within-module and cross);
  no wrapper-over-engine `shape` cluster arises because the pin's helpers are each used once.
* **`move_dead --dry-run --select dead`.** **0 declarations, 0 lines**; "live private helpers needed:
  0" — every helper is reachable from its headline.
* **Name sweep (FR-0274).** The only added last name with a namesake in the tree is `mulEquiv`, and
  the three namesakes sit in other namespaces (`AlgebraicCurve.…`, `private` in
  `NumberField/AdelicCompactness.lean`, `ModularGroup.FreeProduct.…`); every other added last name
  occurs only in this file.
-/
import FLTForHuman.NumberTheory.AdelicFourier.Transform
import FLTForHuman.NumberTheory.AdelicFourier.FiniteCoset
import FLTForHuman.NumberTheory.AdelicFourier.TraceDual
import FLTForHuman.NumberTheory.AdelicBox
import FLTForHuman.NumberTheory.NumberField.GlobalAddChar

set_option autoImplicit false

open NumberField NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm
open IsDedekindDomain MeasureTheory
open scoped Classical FourierTransform nonZeroDivisors NNReal ENNReal

namespace NumberField.AdelicFourier

section Inversion

variable {F : Type} [Field F] [NumberField F]

local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F
local notation "𝒪" => integralFiniteAdeles (𝓞 F) F
local notation "ι" => algebraMap F (FiniteAdeleRing (𝓞 F) F)

/-! ### The annihilator subgroup of the finite-adèle character -/

section Algebra

variable (ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ)

def annSubgroup (a : 𝔸f) : AddSubgroup 𝔸f where
  carrier := {w | ∀ z ∈ 𝒪, ψf (a * w * z) = 1}
  zero_mem' := by
    intro z _
    rw [mul_zero, zero_mul, AddChar.map_zero_eq_one]
  add_mem' := by
    intro x y hx hy z hz
    rw [mul_add, add_mul, AddChar.map_add_eq_mul, hx z hz, hy z hz, one_mul]
  neg_mem' := by
    intro x hx z hz
    rw [mul_neg, neg_mul, addChar_neg_eq_one_iff]
    exact hx z hz

theorem mem_annSubgroup (a w : 𝔸f) :
    w ∈ annSubgroup ψf a ↔ ∀ z ∈ 𝒪, ψf (a * w * z) = 1 := Iff.rfl

theorem coe_annSubgroup (a : 𝔸f) :
    (annSubgroup ψf a : Set 𝔸f) = (fun x => a * x) ⁻¹' {w | ∀ z ∈ 𝒪, ψf (w * z) = 1} := rfl

theorem coe_annSubgroup_one :
    (annSubgroup ψf 1 : Set 𝔸f) = {w | ∀ z ∈ 𝒪, ψf (w * z) = 1} := by
  ext w
  simp only [SetLike.mem_coe, mem_annSubgroup, one_mul, Set.mem_ofPred_eq]

theorem preimage_mul_eq_image_mul {a b : 𝔸f} (hab : a * b = 1) (E : Set 𝔸f) :
    (fun x => a * x) ⁻¹' E = (fun x => b * x) '' E := by
  have hba : b * a = 1 := by rw [mul_comm]; exact hab
  ext x
  simp only [Set.mem_preimage, Set.mem_image]
  constructor
  · intro hx
    exact ⟨a * x, hx, by rw [← mul_assoc, hba, one_mul]⟩
  · rintro ⟨w, hw, rfl⟩
    rwa [← mul_assoc, hab, one_mul]

theorem mul_right_injective_of_mul_eq_one {a b : 𝔸f} (hab : a * b = 1) :
    Function.Injective (fun x : 𝔸f => a * x) := by
  have hba : b * a = 1 := by rw [mul_comm]; exact hab
  intro x y hxy
  have h := congrArg (fun t => b * t) hxy
  simp only [← mul_assoc, hba, one_mul] at h
  exact h

end Algebra

/-! ### The finite sum, the indicator kernel, and the multiplicative dictionary -/

section Measure

variable [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
  (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
  (ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ)

omit [BorelSpace (FiniteAdeleRing (𝓞 F) F)] [ν.IsAddHaarMeasure] in

theorem fourierIntegral_finset_sum_smul (s : Finset F) (c : F → ℂ) (g : F → 𝔸f → ℂ) (w : 𝔸f)
    (hint : ∀ k ∈ s, Integrable (fun v => ψf (-(v * w)) * g k v) ν) :
    fourierIntegral ψf ν (∑ k ∈ s, c k • g k) w = ∑ k ∈ s, c k * fourierIntegral ψf ν (g k) w := by
  simp only [fourierIntegral_def]
  have hpt : (fun v => ψf (-(v * w)) * (∑ k ∈ s, c k • g k) v)
      = fun v => ∑ k ∈ s, c k * (ψf (-(v * w)) * g k v) := by
    funext v
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [hpt, integral_finsetSum s (fun k hk => (hint k hk).const_mul (c k))]
  exact Finset.sum_congr rfl (fun k _ => integral_const_mul _ _)

theorem integrable_kernel_mul_indicator (hcont : Continuous ψf) {E : Set 𝔸f} (hE : IsCompact E)
    {φ : 𝔸f → ℂ} (hφ : Continuous φ) (w : 𝔸f) :
    Integrable (fun v => ψf (-(v * w)) * E.indicator φ v) ν := by
  have hrw : (fun v => ψf (-(v * w)) * E.indicator φ v)
      = E.indicator (fun v => ψf (-(v * w)) * φ v) := by
    funext v
    exact (Set.indicator_mul_right E (fun v => ψf (-(v * w))) φ).symm
  rw [hrw, integrable_indicator_iff hE.isClosed.measurableSet]
  have hk : Continuous fun v : 𝔸f => ψf (-(v * w)) :=
    hcont.comp ((continuous_id.mul continuous_const).neg)
  exact ContinuousOn.integrableOn_compact hE (hk.mul hφ).continuousOn

noncomputable def mulEquiv (a b : 𝔸f) (hab : a * b = 1) : 𝔸f ≃+ 𝔸f where
  toFun x := a * x
  invFun x := b * x
  left_inv x := by
    show b * (a * x) = x
    rw [← mul_assoc, mul_comm b a, hab, one_mul]
  right_inv x := by
    show a * (b * x) = x
    rw [← mul_assoc, hab, one_mul]
  map_add' x y := mul_add a x y

omit [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] in
theorem coe_mulEquiv (a b : 𝔸f) (hab : a * b = 1) : ⇑(mulEquiv a b hab) = fun x => a * x := rfl

omit [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] in
theorem coe_mulEquiv_symm (a b : 𝔸f) (hab : a * b = 1) :
    ⇑(mulEquiv a b hab).symm = fun x => b * x := rfl

theorem exists_measure_preimage_mul (a b : 𝔸f) (hab : a * b = 1) :
    ∃ c : ℝ≥0∞, ∀ E : Set 𝔸f, IsCompact E → ν ((fun x => a * x) ⁻¹' E) = c * ν E := by
  have he : Continuous (mulEquiv a b hab) := by
    rw [coe_mulEquiv]; exact continuous_const.mul continuous_id
  have hes : Continuous (mulEquiv a b hab).symm := by
    rw [coe_mulEquiv_symm]; exact continuous_const.mul continuous_id
  have : (Measure.map (mulEquiv a b hab) ν).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map ν (mulEquiv a b hab) he hes
  refine ⟨Measure.addHaarScalarFactor (Measure.map (mulEquiv a b hab) ν) ν, fun E hE => ?_⟩
  have h := Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure
    (Measure.map (mulEquiv a b hab) ν) ν (s := E) (by rw [hE.isClosed.closure_eq]; exact hE)
  rw [Measure.map_apply he.measurable hE.isClosed.measurableSet, ENNReal.smul_def] at h
  exact h

end Measure

/-! ### The coset computation, and the inversion on a sum of indicators -/

section Main

variable [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
  (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
  (ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ)

local notation "Sk⟮" k ", " d "⟯" =>
  (fun z : FiniteAdeleRing (𝓞 F) F => algebraMap F (FiniteAdeleRing (𝓞 F) F) k
    + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F

theorem fourierIntegral_indicator_coset_eq_indicator (hcont : Continuous ψf)
    (d : 𝓞 F) (hd : d ≠ 0) (k : F) :
    fourierIntegral ψf ν (Sk⟮k, d⟯.indicator 1)
      = (annSubgroup ψf (ι (d : F)) : Set 𝔸f).indicator
          (fun w => ((ν Sk⟮k, d⟯).toReal : ℂ) * ψf (-(ι k * w))) := by
  funext w
  rw [fourierIntegral_indicator_principalCoset_finiteAdeleRing_apply F ν hcont d hd k w]
  by_cases hw : ∀ z ∈ 𝒪, ψf (ι (d : F) * w * z) = 1
  · rw [ite_eq_left hw, mul_one, mul_comm,
      Set.indicator_of_mem (show w ∈ (annSubgroup ψf (ι (d : F)) : Set 𝔸f) from hw)]
  · rw [ite_eq_right hw, mul_zero,
      Set.indicator_of_notMem (show w ∉ (annSubgroup ψf (ι (d : F)) : Set 𝔸f) from hw)]

omit [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] in

theorem isCompact_annSubgroup (hAc : IsCompact {w : 𝔸f | ∀ z ∈ 𝒪, ψf (w * z) = 1})
    {a b : 𝔸f} (hab : a * b = 1) : IsCompact (annSubgroup ψf a : Set 𝔸f) := by
  rw [coe_annSubgroup, preimage_mul_eq_image_mul hab]
  exact hAc.image (continuous_const.mul continuous_id)

omit [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] in

theorem forall_annSubgroup_iff_neg_mem
    (hbi : ∀ u : 𝔸f, (∀ w : 𝔸f, (∀ z ∈ 𝒪, ψf (w * z) = 1) → ψf (u * w) = 1) ↔ u ∈ 𝒪)
    (d : 𝓞 F) (hd : d ≠ 0) (k : F) (y : 𝔸f) :
    (∀ w ∈ annSubgroup ψf (ι (d : F)), ψf (-(ι k + y) * w) = 1) ↔ -y ∈ Sk⟮k, d⟯ := by
  have hd' : (d : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hd
  have hab : ι (d : F) * ι (d : F)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hd', map_one]
  have hba : ι (d : F)⁻¹ * ι (d : F) = 1 := by rw [mul_comm]; exact hab

  have h1 : (∀ w ∈ annSubgroup ψf (ι (d : F)), ψf (-(ι k + y) * w) = 1)
      ↔ (∀ w : 𝔸f, (∀ z ∈ 𝒪, ψf (w * z) = 1) → ψf ((ι k + y) * ι (d : F)⁻¹ * w) = 1) := by
    constructor
    · intro h w hw
      have hmem : ι (d : F)⁻¹ * w ∈ annSubgroup ψf (ι (d : F)) := by
        rw [mem_annSubgroup]
        intro z hz
        rw [← mul_assoc, hab, one_mul]
        exact hw z hz
      have h' := h _ hmem
      rw [neg_mul, addChar_neg_eq_one_iff, ← mul_assoc] at h'
      exact h'
    · intro h w hw
      rw [mem_annSubgroup] at hw
      have h' := h (ι (d : F) * w) hw
      rw [neg_mul, addChar_neg_eq_one_iff]
      have e : (ι k + y) * ι (d : F)⁻¹ * (ι (d : F) * w) = (ι k + y) * w := by
        rw [mul_assoc, ← mul_assoc (ι (d : F)⁻¹), hba, one_mul]
      rw [e] at h'
      exact h'
  rw [h1, hbi]

  constructor
  · intro hu
    refine ⟨-((ι k + y) * ι (d : F)⁻¹), fun v => neg_mem (hu v), ?_⟩
    show ι k + ι (d : F) * -((ι k + y) * ι (d : F)⁻¹) = -y
    have e : ι (d : F) * ((ι k + y) * ι (d : F)⁻¹) = ι k + y := by
      rw [mul_comm (ι k + y), ← mul_assoc, hab, one_mul]
    rw [mul_neg, e]
    ring
  · rintro ⟨z, hz, hzy⟩
    have e : (ι k + y) * ι (d : F)⁻¹ = -z := by
      have hzy' : ι k + ι (d : F) * z = -y := hzy
      have hy : y = -(ι k + ι (d : F) * z) := by rw [hzy', neg_neg]
      rw [hy]
      have : (ι k + -(ι k + ι (d : F) * z)) = -(ι (d : F) * z) := by ring
      rw [this, neg_mul, mul_comm (ι (d : F)) z, mul_assoc, hab, mul_one]
    rw [e]
    exact fun v => neg_mem (hz v)

theorem measure_coset_mul_measure_annSubgroup
    (hAc : IsCompact {w : 𝔸f | ∀ z ∈ 𝒪, ψf (w * z) = 1})
    (d : 𝓞 F) (hd : d ≠ 0) (k : F) :
    ν Sk⟮k, d⟯ * ν (annSubgroup ψf (ι (d : F)) : Set 𝔸f)
      = ν 𝒪 * ν {w : 𝔸f | ∀ z ∈ 𝒪, ψf (w * z) = 1} := by
  have hd' : (d : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hd
  have hab : ι (d : F) * ι (d : F)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hd', map_one]
  obtain ⟨c, hc⟩ := exists_measure_preimage_mul ν (ι (d : F)) (ι (d : F)⁻¹) hab
  have hO_cpt : IsCompact 𝒪 := isCompact_integralFiniteAdeles (K := F)

  have hB_cpt : IsCompact ((fun z => ι (d : F) * z) '' 𝒪) :=
    hO_cpt.image (continuous_const.mul continuous_id)
  have hS_eq : Sk⟮k, d⟯ = (fun b => ι k + b) '' ((fun z => ι (d : F) * z) '' 𝒪) :=
    (Set.image_image (fun b => ι k + b) (fun z => ι (d : F) * z) 𝒪).symm
  have hS : ν Sk⟮k, d⟯ = ν ((fun z => ι (d : F) * z) '' 𝒪) := by
    rw [hS_eq, Set.image_add_left, measure_preimage_add]

  have hO : ν 𝒪 = c * ν ((fun z => ι (d : F) * z) '' 𝒪) := by
    have h := hc _ hB_cpt
    rwa [Set.preimage_image_eq _ (mul_right_injective_of_mul_eq_one hab)] at h

  have hA : ν (annSubgroup ψf (ι (d : F)) : Set 𝔸f)
      = c * ν {w : 𝔸f | ∀ z ∈ 𝒪, ψf (w * z) = 1} := by
    rw [coe_annSubgroup]
    exact hc _ hAc
  rw [hS, hA, hO]
  ring

theorem fourierIntegral_fourierIntegral_indicator_coset (hcont : Continuous ψf)
    (hAc : IsCompact {w : 𝔸f | ∀ z ∈ 𝒪, ψf (w * z) = 1})
    (hbi : ∀ u : 𝔸f, (∀ w : 𝔸f, (∀ z ∈ 𝒪, ψf (w * z) = 1) → ψf (u * w) = 1) ↔ u ∈ 𝒪)
    (d : 𝓞 F) (hd : d ≠ 0) (k : F) (y : 𝔸f) :
    fourierIntegral ψf ν (fourierIntegral ψf ν (Sk⟮k, d⟯.indicator 1)) y
      = ((ν 𝒪).toReal : ℂ) * ((ν {w : 𝔸f | ∀ z ∈ 𝒪, ψf (w * z) = 1}).toReal : ℂ)
          * Sk⟮k, d⟯.indicator 1 (-y) := by
  have hd' : (d : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hd
  have hab : ι (d : F) * ι (d : F)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hd', map_one]
  have hKc : IsCompact (annSubgroup ψf (ι (d : F)) : Set 𝔸f) :=
    isCompact_annSubgroup ψf hAc hab
  have hKm : MeasurableSet (annSubgroup ψf (ι (d : F)) : Set 𝔸f) :=
    hKc.isClosed.measurableSet

  have h1 : fourierIntegral ψf ν (fourierIntegral ψf ν (Sk⟮k, d⟯.indicator 1)) y
      = ((ν Sk⟮k, d⟯).toReal : ℂ)
        * ∫ w in (annSubgroup ψf (ι (d : F)) : Set 𝔸f), ψf (-(ι k + y) * w) ∂ν := by
    rw [fourierIntegral_indicator_coset_eq_indicator ν ψf hcont d hd k, fourierIntegral_def,
      ← integral_const_mul, ← integral_indicator hKm]
    congr 1
    funext w
    by_cases hw : w ∈ (annSubgroup ψf (ι (d : F)) : Set 𝔸f)
    · rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw, mul_left_comm, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hw, mul_zero]

  have h2 := setIntegral_addChar_mul_eq_ite_of_isCompact F ν ψf (annSubgroup ψf (ι (d : F))) hKc
    (-(ι k + y))

  have h3 : ((ν Sk⟮k, d⟯).toReal : ℂ) * ((ν (annSubgroup ψf (ι (d : F)) : Set 𝔸f)).toReal : ℂ)
      = ((ν 𝒪).toReal : ℂ) * ((ν {w : 𝔸f | ∀ z ∈ 𝒪, ψf (w * z) = 1}).toReal : ℂ) := by
    have h := congrArg (fun t : ℝ≥0∞ => ((t.toReal : ℝ) : ℂ))
      (measure_coset_mul_measure_annSubgroup ν ψf hAc d hd k)
    simp only [ENNReal.toReal_mul, Complex.ofReal_mul] at h
    exact h
  rw [h1, h2]
  by_cases hy : -y ∈ Sk⟮k, d⟯
  · rw [ite_eq_left ((forall_annSubgroup_iff_neg_mem ψf hbi d hd k y).mpr hy),
      Set.indicator_of_mem hy, Pi.one_apply, mul_one]
    exact h3
  · rw [ite_eq_right (fun h => hy ((forall_annSubgroup_iff_neg_mem ψf hbi d hd k y).mp h)),
      Set.indicator_of_notMem hy, mul_zero, mul_zero]

theorem fourierIntegral_fourierIntegral_eq (hcont : Continuous ψf)
    (hAc : IsCompact {w : 𝔸f | ∀ z ∈ 𝒪, ψf (w * z) = 1})
    (hbi : ∀ u : 𝔸f, (∀ w : 𝔸f, (∀ z ∈ 𝒪, ψf (w * z) = 1) → ψf (u * w) = 1) ↔ u ∈ 𝒪)
    {h : 𝔸f → ℂ} (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h) (y : 𝔸f) :
    fourierIntegral ψf ν (fourierIntegral ψf ν h) y
      = ((ν 𝒪).toReal : ℂ) * ((ν {w : 𝔸f | ∀ z ∈ 𝒪, ψf (w * z) = 1}).toReal : ℂ) * h (-y) := by
  obtain ⟨d, hd, s, c, rfl⟩ := exists_eq_sum_indicator_image_integralFiniteAdeles F hlc hcs
  have hd' : (d : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hd
  have hab : ι (d : F) * ι (d : F)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hd', map_one]
  have hO_cpt : IsCompact 𝒪 := isCompact_integralFiniteAdeles (K := F)
  have hS_cpt : ∀ k : F, IsCompact Sk⟮k, d⟯ := fun k =>
    hO_cpt.image (continuous_const.add (continuous_const.mul continuous_id))

  have hinner : fourierIntegral ψf ν (∑ k ∈ s, c k • Sk⟮k, d⟯.indicator 1)
      = ∑ k ∈ s, c k • fourierIntegral ψf ν (Sk⟮k, d⟯.indicator 1) := by
    funext w
    rw [fourierIntegral_finset_sum_smul ν ψf s c _ w
      (fun k _ => integrable_kernel_mul_indicator ν ψf hcont (hS_cpt k) continuous_one w)]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

  have hKc : IsCompact (annSubgroup ψf (ι (d : F)) : Set 𝔸f) :=
    isCompact_annSubgroup ψf hAc hab
  have hint : ∀ k ∈ s, Integrable
      (fun w => ψf (-(w * y)) * fourierIntegral ψf ν (Sk⟮k, d⟯.indicator 1) w) ν := by
    intro k _
    rw [fourierIntegral_indicator_coset_eq_indicator ν ψf hcont d hd k]
    exact integrable_kernel_mul_indicator ν ψf hcont hKc
      (continuous_const.mul (hcont.comp ((continuous_const.mul continuous_id).neg))) y
  rw [hinner, fourierIntegral_finset_sum_smul ν ψf s c _ y hint]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [fourierIntegral_fourierIntegral_indicator_coset ν ψf hcont hAc hbi d hd k y]
  ring

end Main

/-! ### Row 1: the inversion on the locally constant compactly supported functions -/

end Inversion

theorem fourierIntegral_fourierIntegral_finiteAdeleRing_eq
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : MeasureTheory.Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    {h : FiniteAdeleRing (𝓞 F) F → ℂ} (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h)
    (y : FiniteAdeleRing (𝓞 F) F) :
    fourierIntegral (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) ν
        (fourierIntegral (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) ν h) y
      = ((Ideal.absNorm (differentIdeal ℤ (𝓞 F)) : ℂ)
          * ((ν (integralFiniteAdeles (𝓞 F) F)).toReal : ℂ) ^ 2) * h (-y) := by
  have happly : ∀ w : FiniteAdeleRing (𝓞 F) F,
      (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) w
        = ψ (0, w) := fun w => rfl
  have hcont : Continuous
      (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) :=
    (continuous_congr happly).mpr (hψ.continuous.comp (continuous_const.prodMk continuous_id))
  have hset : {w : FiniteAdeleRing (𝓞 F) F | ∀ z ∈ integralFiniteAdeles (𝓞 F) F,
      (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))
        (w * z) = 1}
      = {w : FiniteAdeleRing (𝓞 F) F | ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1} := by
    simp only [happly]
  have hAc := (isCompact_and_isOpen_setOf_forall_addChar_finitePart_mul_eq_one F hψ hψ_inf).1
  have hvol := measure_setOf_forall_addChar_finitePart_mul_eq_one F ν hψ hψ_inf
  have hbi := forall_addChar_finitePart_mul_eq_one_of_forall_iff_mem_integralFiniteAdeles F hψ hψ_inf
  have hmain := fourierIntegral_fourierIntegral_eq ν
    (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))
    hcont (by rw [hset]; exact hAc) (by simpa only [happly] using hbi) hlc hcs y
  rw [hmain, hset, hvol, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  push_cast
  ring

/-! ### The coset-translation dictionary, and the Schwartz property -/

section Schwartz

variable {F : Type} [Field F] [NumberField F]

theorem add_mem_image_iff (d : 𝓞 F) (k : F) {u : FiniteAdeleRing (𝓞 F) F}
    (hu : u ∈ integralFiniteAdeles (𝓞 F) F) (v : FiniteAdeleRing (𝓞 F) F) :
    v + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * u ∈
        (fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F
      ↔ v ∈ (fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F := by
  constructor
  · rintro ⟨z, hz, hzv⟩
    refine ⟨z - u, BoxIndex.sub_mem' F hz hu, ?_⟩
    simp only at hzv ⊢
    rw [mul_sub]
    linear_combination hzv
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z + u, BoxKernel.add_mem_integralFiniteAdeles F hz hu,
      by simp only; rw [mul_add, add_assoc]⟩

theorem exists_mem_image_of_sum_ne_zero (d : 𝓞 F) (s : Finset F) (c : F → ℂ)
    (v : FiniteAdeleRing (𝓞 F) F)
    (hv : (∑ k ∈ s, c k •
        ((fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) ''
            integralFiniteAdeles (𝓞 F) F).indicator (1 : FiniteAdeleRing (𝓞 F) F → ℂ)) v ≠ 0) :
    ∃ k ∈ s, v ∈ (fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F := by
  by_contra hcon
  apply hv
  rw [Finset.sum_apply]
  refine Finset.sum_eq_zero fun k hk => ?_
  have hk' : v ∉ (fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
      + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F :=
    fun hmem => hcon ⟨k, hk, hmem⟩
  rw [Pi.smul_apply, Set.indicator_apply, ite_eq_right hk', smul_zero]

theorem sum_apply_add_eq (d : 𝓞 F) (s : Finset F) (c : F → ℂ)
    {u : FiniteAdeleRing (𝓞 F) F} (hu : u ∈ integralFiniteAdeles (𝓞 F) F)
    (v : FiniteAdeleRing (𝓞 F) F) :
    (∑ k ∈ s, c k •
        ((fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) ''
            integralFiniteAdeles (𝓞 F) F).indicator (1 : FiniteAdeleRing (𝓞 F) F → ℂ))
        (v + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * u)
      = (∑ k ∈ s, c k •
        ((fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) ''
            integralFiniteAdeles (𝓞 F) F).indicator (1 : FiniteAdeleRing (𝓞 F) F → ℂ)) v := by
  rw [Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.smul_apply, Set.indicator_apply, Pi.one_apply, add_mem_image_iff d k hu v]

end Schwartz

section SchwartzMain

variable {F : Type} [Field F] [NumberField F]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
  (ν : MeasureTheory.Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
  {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
  (hψ_inf : ∀ x : InfiniteAdeleRing F,
      ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
  {h : FiniteAdeleRing (𝓞 F) F → ℂ} (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h)

include hψ hψ_inf hlc hcs

omit [BorelSpace (FiniteAdeleRing (𝓞 F) F)] [ν.IsAddHaarMeasure] in

theorem isLocallyConstant_fourierIntegral :
    IsLocallyConstant (fourierIntegral
        (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) ν h) := by
  set ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ :=
    ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) with hψf_def
  have hψf : ∀ x, ψf x = ψ (0, x) := fun _ => rfl

  have hO : ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψf z = 1 := by
    have h1 : ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, 1 * z) = 1 :=
      (NumberField.AdelicFourier.forall_addChar_finitePart_mul_eq_one_iff_exists_mem_traceDual
        F hψ hψ_inf 1).mpr
        ⟨1, (FractionalIdeal.one_le_dual_one ℤ ℚ) (FractionalIdeal.one_mem_one (𝓞 F)⁰),
          by rw [map_one, sub_self]; exact fun v => zero_mem _⟩
    intro z hz
    rw [hψf, ← one_mul z]
    exact h1 z hz

  obtain ⟨d, hd, s, c, rfl⟩ :=
    NumberField.AdelicBox.exists_eq_sum_indicator_image_integralFiniteAdeles F hlc hcs

  have key : ∀ t : FiniteAdeleRing (𝓞 F) F,
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * t ∈ integralFiniteAdeles (𝓞 F) F →
      (∀ k ∈ s, algebraMap F (FiniteAdeleRing (𝓞 F) F) k * t ∈ integralFiniteAdeles (𝓞 F) F) →
      ∀ (g : FiniteAdeleRing (𝓞 F) F → ℂ), (∀ v, g v ≠ 0 → ∃ k ∈ s, v ∈
          (fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
            + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F) →
      ∀ w, fourierIntegral ψf ν g (w + t) = fourierIntegral ψf ν g w := by
    intro t ht1 ht2 g hg w
    rw [fourierIntegral_def, fourierIntegral_def]
    congr 1 with v
    by_cases hv : g v = 0
    · simp only [hv, mul_zero]
    · obtain ⟨k, hk, z, hz, rfl⟩ := hg v hv
      have hvt : (algebraMap F (FiniteAdeleRing (𝓞 F) F) k
            + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) * t
          ∈ integralFiniteAdeles (𝓞 F) F := by
        rw [add_mul, mul_right_comm]
        exact BoxKernel.add_mem_integralFiniteAdeles F (ht2 k hk)
          (mul_mem_integralFiniteAdeles ht1 hz)
      simp only
      rw [mul_add, neg_add, AddChar.map_add_eq_mul,
        hO _ (BoxKernel.neg_mem_integralFiniteAdeles F hvt), mul_one]

  have hP : IsOpen ((fun t => algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * t) ⁻¹'
      integralFiniteAdeles (𝓞 F) F) :=
    (isOpen_integralFiniteAdeles F).preimage (continuous_const.mul continuous_id)
  have hQ : IsOpen (⋂ k ∈ s, (fun t => algebraMap F (FiniteAdeleRing (𝓞 F) F) k * t) ⁻¹'
      integralFiniteAdeles (𝓞 F) F) :=
    isOpen_biInter_finset fun k _ =>
      (isOpen_integralFiniteAdeles F).preimage (continuous_const.mul continuous_id)
  have hT := hP.inter hQ
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun w => ?_
  have hmem : (fun y => y - w) ⁻¹'
      (((fun t => algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * t) ⁻¹'
          integralFiniteAdeles (𝓞 F) F) ∩
        ⋂ k ∈ s, (fun t => algebraMap F (FiniteAdeleRing (𝓞 F) F) k * t) ⁻¹'
          integralFiniteAdeles (𝓞 F) F) ∈ nhds w := by
    refine (hT.preimage (continuous_sub_right w)).mem_nhds ?_
    rw [Set.mem_preimage, sub_self]
    refine ⟨?_, Set.mem_iInter₂.mpr fun k _ => ?_⟩
    · rw [Set.mem_preimage, mul_zero]; exact fun v => zero_mem _
    · rw [Set.mem_preimage, mul_zero]; exact fun v => zero_mem _
  refine Filter.mem_of_superset hmem fun y hy => ?_
  have hy1 : algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * (y - w)
      ∈ integralFiniteAdeles (𝓞 F) F := hy.1
  have hy2 : ∀ k ∈ s, algebraMap F (FiniteAdeleRing (𝓞 F) F) k * (y - w)
      ∈ integralFiniteAdeles (𝓞 F) F := fun k hk => Set.mem_iInter₂.mp hy.2 k hk
  have := key (y - w) hy1 hy2 _ (exists_mem_image_of_sum_ne_zero d s c) w
  rwa [add_sub_cancel] at this

theorem hasCompactSupport_fourierIntegral :
    HasCompactSupport (fourierIntegral
        (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) ν h) := by
  set ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ :=
    ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) with hψf_def
  have hψf : ∀ x, ψf x = ψ (0, x) := fun _ => rfl

  have hA :=
    (NumberField.AdelicFourier.isCompact_and_isOpen_setOf_forall_addChar_finitePart_mul_eq_one
      F hψ hψ_inf).1

  obtain ⟨d, hd, s, c, rfl⟩ :=
    NumberField.AdelicBox.exists_eq_sum_indicator_image_integralFiniteAdeles F hlc hcs
  have hdF : (d : F) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hd)

  have hK : IsCompact ((fun a => algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)⁻¹ * a) ''
      {w : FiniteAdeleRing (𝓞 F) F | ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1}) :=
    hA.image (continuous_const.mul continuous_id)
  refine HasCompactSupport.intro' hK hK.isClosed fun w hw => ?_
  by_contra hne
  apply hw
  refine ⟨algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * w, fun z hz => ?_, ?_⟩
  ·
    have hcomp : fourierIntegral ψf ν (∑ k ∈ s, c k •
        ((fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) ''
            integralFiniteAdeles (𝓞 F) F).indicator (1 : FiniteAdeleRing (𝓞 F) F → ℂ)) w
        = ψf (algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z * w) *
          fourierIntegral ψf ν (∑ k ∈ s, c k •
            ((fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
              + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) ''
                integralFiniteAdeles (𝓞 F) F).indicator (1 : FiniteAdeleRing (𝓞 F) F → ℂ)) w := by
      have hc := congrFun (fourierIntegral_comp_add_right ψf ν (∑ k ∈ s, c k •
        ((fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) ''
            integralFiniteAdeles (𝓞 F) F).indicator (1 : FiniteAdeleRing (𝓞 F) F → ℂ))
        (algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z)) w
      have hper : ((∑ k ∈ s, c k •
          ((fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
            + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) ''
              integralFiniteAdeles (𝓞 F) F).indicator (1 : FiniteAdeleRing (𝓞 F) F → ℂ)) ∘
            fun v => v + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z)
          = ∑ k ∈ s, c k •
            ((fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
              + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) ''
                integralFiniteAdeles (𝓞 F) F).indicator (1 : FiniteAdeleRing (𝓞 F) F → ℂ) :=
        funext fun v => sum_apply_add_eq d s c hz v
      rwa [hper] at hc
    have h1 : ψf (algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z * w) = 1 :=
      (mul_eq_right₀ hne).mp hcomp.symm
    rw [mul_right_comm] at h1
    exact h1
  · show algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)⁻¹
        * (algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * w) = w
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hdF, map_one, one_mul]

end SchwartzMain

/-! ### Row 2: the Schwartz property -/

theorem isLocallyConstant_and_hasCompactSupport_fourierIntegral_finiteAdeleRing
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : MeasureTheory.Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    {h : FiniteAdeleRing (𝓞 F) F → ℂ} (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h) :
    IsLocallyConstant (fourierIntegral
        (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) ν h)
      ∧ HasCompactSupport (fourierIntegral
        (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) ν h) :=
  ⟨isLocallyConstant_fourierIntegral ν hψ hψ_inf hlc hcs,
    hasCompactSupport_fourierIntegral ν hψ hψ_inf hlc hcs⟩

end NumberField.AdelicFourier
