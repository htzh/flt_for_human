/-
The complex-place dictionary in action: existence, the `Γ₀(M)` pull-back, and conjugation.

Three headlines, one theory.  A `ModularCurve.ComplexPlaceDictionaryOf Γ F₀` is a
`ℍ`-indexed family of places of `laurentBaseChange ℂ F₀`, tied to the function
`realizeOf Γ x` by the order law; this module produces such a dictionary and moves
its places under the two Galois actions that the later rows read:

* `ModularCurve.exists_complexPlaceDictionaryOf` — for `F₀ = qExpFunctionFieldC ℚ Γ`
  and `T ∈ Γ` there **is** a dictionary.  The proof builds the place at `τ : ℍ` from
  the meromorphic order function `mu τ` on the base-changed field (an order function
  in the sense of `AlgebraicCurve.Place.exists_of_orderMap`), the `Pres` presentation
  of an element as a ratio of two `q`-expansions supplying the algebra laws of `mu`.
* `ModularCurve.ComplexPlaceDictionaryOf.ofAlgAut_smul_pt_eq_pt_inv_smul` — the
  `Γ₀(M)` pull-back: if `σ` twists every integral q-expansion ratio by `γ ∈ Γ₀(M)`
  (`hσ`, a hypothesis: the pin's `IsPullbackAlong`), then at the level of places
  `SemilinearAut.ofAlgAut σ • D.pt τ = D.pt (γ⁻¹ • τ)`.
* `ModularCurve.ComplexPlaceDictionaryOf.arithmeticGalois_complexConjAlgEquiv_smul_pt`
  — conjugation: `arithmeticGalois F₀ complexConjAlgEquiv • D.pt τ = D.pt (J • τ)`.

## The one engine

The pin re-proves the same `qL`/`Pres`/`realize_*` prelude in each of its three `S_`
files (511 lines of duplication across
`S_ModularCurve_exists_complexPlaceDictionaryOf.lean`,
`S_ModularCurve_ComplexPlaceDictionaryOf_ofAlgAut_smul_pt_eq_pt_inv_smul.lean` and
`S_ModularCurve_ComplexPlaceDictionaryOf_arithmeticGalois_complexConjAlgEquiv_smul_pt.lean`;
161 lines are the once-cost).  It is written **once** here, in the single private
namespace `ModularCurve.PlaceDictionaryAction`:

* `Pres` — the presentation of `x : LaurentSeries ℂ` as a ratio `qL g / qL h` of two
  `q`-expansions of `Γ`-modular forms of one weight (`Pres.mul`, `Pres.add`,
  `Pres.const`, `Pres.inv` close it under the field operations);
* the coefficient-embedding bridge `map_coe_nhdsNE`, `eventually_nhdsNE_coe_iff`,
  `isBoundedUnder_nhdsNE_coe_iff`, `analyticAt_comp_ofComplex`, `coe_eq_zero_iff`,
  `eventually_ne_zero`, `eventually_ne_zero_ofComplex`,
  `meromorphicOrderAt_comp_ofComplex_ne_top`;
* the realizability layer `realize_eventuallyEq`, `meromorphicAt_div`,
  `meromorphicAt_realize`, `meromorphicOrderAt_realize_eq` and the transport of the
  ring laws `realize_{mul,add,const,smul,neg,inv}_eventuallyEq`;
* `CF`/`pres` (the base-changed field and a chosen presentation of each element) and,
  for the existence row, the order function `mu` with `mu_{mul,add,algebraMap}`,
  `mu_eq_top_iff`, `mu_ne_top`, `mu_one`, `mu_smul`, `mu_nonneg_iff`, the separating
  element `X`, `exists_mu_pos` and `exists_place`.

Only the three headlines are public: the engine is the pin's own private prelude, so
it is transcribed `private` here (the wire then reads exactly the three `Thm_`
statements, and promoting the engine later is a one-token edit).  The `qL` half of
the pin's prelude is *not* rewritten: `qL`, `one_mem_strictPeriods`, `qL_ne_zero`,
`qL_mul`, `qL_add`, `qL_one`, `qL_const`, `one_ne_zero'` and the product closure
`mul_ne_zero'` are the port's public copies in `ModularCurve.RatioFieldOfGroup`
(`ModularCurve/X1/CoeffMap.lean`), imported below and used under their pin names —
one home for the `q`-expansion algebra.  `Pres.inv` and the `realize_*` laws of the
`Presented` section come from the 684/648 copies, which are identical.

The pin's `set_option`s (`autoImplicit`, `linter.unusedSectionVars`) and its
`scoped instance nhdsNE_neBot` are not transcribed: the project sets `autoImplicit`
globally and mathlib `v4.34` already has the punctured-neighbourhood `NeBot`
instance.  `p2m_export`/`p2m_open`/`p2m_reactivate` are pin plumbing; the port uses
plain namespaces.

Deviations, recorded (none touches a statement):

* **Spellings of the two `S_` copies.**  The 684 and 648 files' private blocks are
  the same mathematics once each: the Möbius transport (`moeb`, `moeb_apply`,
  `tendsto_moeb_nhdsNE`, `eventually_smul_of_eventually`, `isBoundedUnder_comp_smul_iff`)
  is written once at `g : GL (Fin 2) ℝ` and used at `γ` (coerced) and at `J`, and so
  are `isBoundedUnder_congr_of_eventuallyEq` and `mem_smul_place_iff` (stated over a
  general `F₀`, which is the two pin spellings at the two fields).  The two `Key`
  blocks are different statements and are kept apart: the 684 one in
  `PlaceDictionaryAction`, the 648 one in `PlaceDictionaryAction.ConjPlaceTransport`
  (the pin re-uses the names `Key`, `key_*`, `smul_pt_eq` in both files; two `private`
  declarations of one name in one file would collide).
* **`SL(2, ℤ)` acting on `ℂ`.**  The pin writes `γ • ofComplex z` for `γ : SL(2, ℤ)`
  through its own `SMul` instance, which the port does not carry: the 684 `Key` laws
  are stated at the coerced action `((γ : GL (Fin 2) ℝ)) • ·` and bridged by
  `sl_smul_upperHalf` (`γ • τ = (↑γ) • τ`, `by simp`) where a `rw` needs the
  coercion.  The places themselves are untouched.
* **The instance discipline.**  `omit hT in` / `omit [NeZero M] in` replace the pin's
  `linter.unusedSectionVars false`, and `[NeZero M]` is dropped from the two private
  684 sections that never use it (the headline keeps its `[NeZero M]` verbatim).
  `haveI` under a proposition goal is refused by the project's
  `linter.style.haveILetI`, so the `Fact (ModularGroup.T ∈ Γ)` instance of the
  existence proof is supplied as the explicit instance argument of the private
  `dictionaryOf`, and the `Fact (IsCusp ∞ Γ)` instance of the conjugation block is a
  `local instance` (`instFactIsCusp`).
* **Proof-only refactors.**  `Pres.inv`'s inline `h_ne` argument is named
  `Pres.slash_pres_ne`; `dictionaryOf` is the existence record, so the headline is
  `⟨…⟩`.  Deprecated spellings are refreshed (`FunLike.coe_zero`, `FunLike.coe_add`,
  `FunLike.coe_smul` for `ModularForm.coe_zero`/`coe_add`/`IsGLPos.coe_smul`); the
  pin's `@[scoped simp]` on `coe_slashForm` is dropped (its one consumer rewrites
  explicitly).

Transcribed from the pin's three `S_` files (441 / 684 / 648 lines) and stated at the
pin's three `Theorems/` wrappers.

FLT provenance, pinned `aa2d8b3`:
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_exists_complexPlaceDictionaryOf.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_ComplexPlaceDictionaryOf_ofAlgAut_smul_pt_eq_pt_inv_smul.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_ComplexPlaceDictionaryOf_arithmeticGalois_complexConjAlgEquiv_smul_pt.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_exists_complexPlaceDictionaryOf.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_ComplexPlaceDictionaryOf_ofAlgAut_smul_pt_eq_pt_inv_smul.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_ComplexPlaceDictionaryOf_arithmeticGalois_complexConjAlgEquiv_smul_pt.lean>

spec-pin: Theorems/Thm_ModularCurve_exists_complexPlaceDictionaryOf.lean
spec-pin: P2M/Sol/S_ModularCurve_exists_complexPlaceDictionaryOf.lean
spec-pin: Theorems/Thm_ModularCurve_ComplexPlaceDictionaryOf_ofAlgAut_smul_pt_eq_pt_inv_smul.lean
spec-pin: P2M/Sol/S_ModularCurve_ComplexPlaceDictionaryOf_ofAlgAut_smul_pt_eq_pt_inv_smul.lean
spec-pin: Theorems/Thm_ModularCurve_ComplexPlaceDictionaryOf_arithmeticGalois_complexConjAlgEquiv_smul_pt.lean
spec-pin: P2M/Sol/S_ModularCurve_ComplexPlaceDictionaryOf_arithmeticGalois_complexConjAlgEquiv_smul_pt.lean
-/
import FLTForHuman.ModularCurve.ComplexPlaceDictionaryOf
import FLTForHuman.ModularCurve.X1.CoeffMap
import FLTForHuman.ModularCurve.XH.FunctionField
import FLTForHuman.ModularCurve.Defs.ArithmeticGalois
import FLTForHuman.ModularCurve.JqIntegralRatios
import FLTForHuman.AlgebraicCurve.Place.ValueDictionary
import FLTForHuman.GaloisRep.Defs.ComplexConjugation

set_option autoImplicit false

noncomputable section

open UpperHalfPlane Filter
open scoped MatrixGroups Topology Manifold ModularForm Pointwise ComplexConjugate

namespace ModularCurve

open ModularCurve.RatioFieldOfGroup

namespace PlaceDictionaryAction

section Engine

variable {Γ : Subgroup SL(2, ℤ)}

/-! ## The presentation of a Laurent series by two `q`-expansions -/

private structure Pres (Γ : Subgroup SL(2, ℤ)) (x : LaurentSeries ℂ) where
  k : ℤ
  g : ModularForm Γ k
  h : ModularForm Γ k
  h_ne : h ≠ 0
  eq : x * qL h = qL g

variable [hT : Fact (ModularGroup.T ∈ Γ)]

/-! ## The coefficient embedding of `ℍ` into `ℂ` -/

theorem map_coe_nhdsNE (τ : ℍ) :
    Filter.map ((↑) : ℍ → ℂ) (𝓝[≠] τ) = 𝓝[≠] (τ : ℂ) := by
  have h := isOpenEmbedding_coe.map_nhdsWithin_preimage_eq ({(τ : ℂ)}ᶜ) τ
  have hpre : ((↑) : ℍ → ℂ) ⁻¹' ({(τ : ℂ)}ᶜ : Set ℂ) = ({τ}ᶜ : Set ℍ) := by
    ext w
    simp
  rwa [hpre] at h

theorem eventually_nhdsNE_coe_iff {p : ℍ → Prop} {τ : ℍ} :
    (∀ᶠ z in 𝓝[≠] (τ : ℂ), p (ofComplex z)) ↔ ∀ᶠ w in 𝓝[≠] τ, p w := by
  rw [← map_coe_nhdsNE, Filter.eventually_map]
  simp only [ofComplex_apply]

theorem isBoundedUnder_nhdsNE_coe_iff {u : ℍ → ℝ} {τ : ℍ} :
    IsBoundedUnder (· ≤ ·) (𝓝[≠] (τ : ℂ)) (fun z : ℂ => u (ofComplex z)) ↔
      IsBoundedUnder (· ≤ ·) (𝓝[≠] τ) u := by
  rw [← map_coe_nhdsNE, Filter.isBoundedUnder_map_iff]
  simp only [Function.comp_def, ofComplex_apply]

omit hT in
theorem analyticAt_comp_ofComplex {k : ℤ} (f : ModularForm Γ k) (τ : ℍ) :
    AnalyticAt ℂ (fun z : ℂ => (f : ℍ → ℂ) (ofComplex z)) (τ : ℂ) := by
  have hf : DifferentiableOn ℂ ((f : ℍ → ℂ) ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp (ModularFormClass.holo f)
  exact hf.analyticAt (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)

omit hT in
theorem coe_eq_zero_iff {k : ℤ} (f : ModularForm Γ k) :
    (f : ℍ → ℂ) = 0 ↔ f = 0 := by
  constructor
  · intro h
    exact DFunLike.coe_injective (h.trans (FunLike.coe_zero).symm)
  · rintro rfl; rfl

omit hT in
theorem eventually_ne_zero {k : ℤ} (f : ModularForm Γ k)
    (hf : f ≠ 0) (τ : ℍ) : ∀ᶠ w in 𝓝[≠] τ, (f : ℍ → ℂ) w ≠ 0 := by
  by_contra hcon
  have hfr : ∃ᶠ w in 𝓝[≠] τ, (f : ℍ → ℂ) w = 0 := by
    simpa [Filter.not_eventually] using hcon
  exact hf ((coe_eq_zero_iff f).mp (eq_zero_of_frequently (ModularFormClass.holo f) hfr))

omit hT in
theorem eventually_ne_zero_ofComplex {k : ℤ} (f : ModularForm Γ k)
    (hf : f ≠ 0) (τ : ℍ) : ∀ᶠ z in 𝓝[≠] (τ : ℂ), (f : ℍ → ℂ) (ofComplex z) ≠ 0 :=
  eventually_nhdsNE_coe_iff.mpr (eventually_ne_zero f hf τ)

omit hT in
theorem meromorphicOrderAt_comp_ofComplex_ne_top {k : ℤ}
    (f : ModularForm Γ k) (hf : f ≠ 0) (τ : ℍ) :
    meromorphicOrderAt (fun z : ℂ => (f : ℍ → ℂ) (ofComplex z)) (τ : ℂ) ≠ ⊤ :=
  (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
    (analyticAt_comp_ofComplex f τ).meromorphicAt).mpr (eventually_ne_zero_ofComplex f hf τ)

/-! ## The realizability layer -/

theorem realize_eventuallyEq {x : LaurentSeries ℂ} (P : Pres Γ x) (τ : ℍ) :
    (fun z : ℂ => realizeOf Γ x (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z : ℂ => (P.g : ℍ → ℂ) (ofComplex z) / (P.h : ℍ → ℂ) (ofComplex z) := by
  filter_upwards [eventually_ne_zero_ofComplex P.h P.h_ne τ] with z hz
  exact ModularCurve.realizeOf_eq_div Γ hT.out P.g P.h x P.eq (ofComplex z) hz

omit hT in
theorem meromorphicAt_div (x : LaurentSeries ℂ) (P : Pres Γ x) (τ : ℍ) :
    MeromorphicAt (fun z : ℂ => (P.g : ℍ → ℂ) (ofComplex z) / (P.h : ℍ → ℂ) (ofComplex z))
      (τ : ℂ) :=
  (analyticAt_comp_ofComplex P.g τ).meromorphicAt.div (analyticAt_comp_ofComplex P.h τ).meromorphicAt

theorem meromorphicAt_realize {x : LaurentSeries ℂ} (P : Pres Γ x) (τ : ℍ) :
    MeromorphicAt (fun z : ℂ => realizeOf Γ x (ofComplex z)) (τ : ℂ) :=
  (meromorphicAt_div x P τ).congr (realize_eventuallyEq P τ).symm

theorem meromorphicOrderAt_realize_eq {x : LaurentSeries ℂ} (P : Pres Γ x) (τ : ℍ) :
    ∃ m : ℤ, 0 ≤ m ∧
      meromorphicOrderAt (fun z : ℂ => (P.h : ℍ → ℂ) (ofComplex z)) (τ : ℂ) = m ∧
      meromorphicOrderAt (fun z : ℂ => realizeOf Γ x (ofComplex z)) (τ : ℂ) =
        meromorphicOrderAt (fun z : ℂ => (P.g : ℍ → ℂ) (ofComplex z)) (τ : ℂ) +
          ((-m : ℤ) : WithTop ℤ) := by
  have hh := meromorphicOrderAt_comp_ofComplex_ne_top P.h P.h_ne τ
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hh
  have hm0 : 0 ≤ m := by
    have := (analyticAt_comp_ofComplex P.h τ).meromorphicOrderAt_nonneg
    rw [← hm] at this
    exact_mod_cast this
  refine ⟨m, hm0, hm.symm, ?_⟩
  rw [meromorphicOrderAt_congr (realize_eventuallyEq P τ)]
  have hdiv : (fun z : ℂ => (P.g : ℍ → ℂ) (ofComplex z) / (P.h : ℍ → ℂ) (ofComplex z)) =
      (fun z : ℂ => (P.g : ℍ → ℂ) (ofComplex z)) *
        (fun z : ℂ => (P.h : ℍ → ℂ) (ofComplex z))⁻¹ := by
    ext z; simp [div_eq_mul_inv]
  rw [hdiv, meromorphicOrderAt_mul (analyticAt_comp_ofComplex P.g τ).meromorphicAt
    (analyticAt_comp_ofComplex P.h τ).meromorphicAt.inv, meromorphicOrderAt_inv, ← hm]
  rfl

abbrev Pres.mul {x y : LaurentSeries ℂ} (P : Pres Γ x) (Q : Pres Γ y) :
    Pres Γ (x * y) where
  k := P.k + Q.k
  g := P.g.mul Q.g
  h := P.h.mul Q.h
  h_ne := mul_ne_zero' hT.out P.h Q.h P.h_ne Q.h_ne
  eq := by
    rw [qL_mul hT.out, qL_mul hT.out, ← P.eq, ← Q.eq]; ring

abbrev Pres.add {x y : LaurentSeries ℂ} (P : Pres Γ x) (Q : Pres Γ y) :
    Pres Γ (x + y) where
  k := P.k + Q.k
  g := P.g.mul Q.h + P.h.mul Q.g
  h := P.h.mul Q.h
  h_ne := mul_ne_zero' hT.out P.h Q.h P.h_ne Q.h_ne
  eq := by
    rw [qL_add hT.out, qL_mul hT.out, qL_mul hT.out, qL_mul hT.out, ← P.eq, ← Q.eq]; ring

theorem algebraMap_laurentSeries_eq_C (c : ℂ) :
    algebraMap ℂ (LaurentSeries ℂ) c = HahnSeries.C c := by
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq, HahnSeries.ofPowerSeries_C]

omit hT in
theorem coeffEmb_intSeriesC_eq_qL {k : ℤ} {f : ModularForm Γ k} {p : PowerSeries ℤ}
    (hf : IsIntegralQExp f p) : coeffEmb ℂ (intSeriesC ℚ p) = qL f := by
  rw [RatioFieldOfGroup.coeffEmb_intSeriesC p, RatioFieldOfGroup.intSeriesC_eq_qL hf]

private abbrev Pres.const (c : ℂ) : Pres Γ (algebraMap ℂ (LaurentSeries ℂ) c) where
  k := 0
  g := c • (1 : ModularForm Γ 0)
  h := 1
  h_ne := one_ne_zero'
  eq := by
    rw [qL_one, mul_one, qL_const hT.out]

private theorem Pres.slash_pres_ne {x : LaurentSeries ℂ} (P : Pres Γ x) (hx : x ≠ 0) :
    P.g ≠ 0 := by
  intro hg0
  have heq := P.eq
  rw [hg0, show qL (0 : ModularForm Γ P.k) = 0 by
    simp [qL, UpperHalfPlane.qExpansion_zero]] at heq
  exact (mul_ne_zero hx (qL_ne_zero hT.out P.h P.h_ne)) heq

abbrev Pres.inv {x : LaurentSeries ℂ} (P : Pres Γ x) (hx : x ≠ 0) : Pres Γ x⁻¹ where
  k := P.k
  g := P.h
  h := P.g
  h_ne := P.slash_pres_ne hx
  eq := by
    rw [← P.eq, mul_comm x, mul_comm x⁻¹, mul_assoc, mul_inv_cancel₀ hx, mul_one]

theorem realize_mul_eventuallyEq {x y : LaurentSeries ℂ} (P : Pres Γ x) (Q : Pres Γ y)
    (τ : ℍ) :
    (fun z : ℂ => realizeOf Γ (x * y) (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      (fun z : ℂ => realizeOf Γ x (ofComplex z)) * fun z : ℂ => realizeOf Γ y (ofComplex z) := by
  filter_upwards [realize_eventuallyEq (P.mul Q) τ, realize_eventuallyEq P τ,
    realize_eventuallyEq Q τ] with z h1 h2 h3
  rw [Pi.mul_apply, h2, h3, h1]
  rw [ModularForm.coe_mul, ModularForm.coe_mul, Pi.mul_apply, Pi.mul_apply, mul_div_mul_comm]

theorem realize_add_eventuallyEq {x y : LaurentSeries ℂ} (P : Pres Γ x) (Q : Pres Γ y)
    (τ : ℍ) :
    (fun z : ℂ => realizeOf Γ (x + y) (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      (fun z : ℂ => realizeOf Γ x (ofComplex z)) + fun z : ℂ => realizeOf Γ y (ofComplex z) := by
  filter_upwards [realize_eventuallyEq (P.add Q) τ, realize_eventuallyEq P τ,
    realize_eventuallyEq Q τ, eventually_ne_zero_ofComplex P.h P.h_ne τ,
    eventually_ne_zero_ofComplex Q.h Q.h_ne τ] with z h1 h2 h3 hP hQ
  rw [Pi.add_apply, h2, h3, h1]
  rw [FunLike.coe_add, Pi.add_apply, ModularForm.coe_mul, ModularForm.coe_mul,
    ModularForm.coe_mul, Pi.mul_apply, Pi.mul_apply, Pi.mul_apply, div_add_div _ _ hP hQ,
    mul_comm ((P.h : ℍ → ℂ) (ofComplex z)) ((Q.g : ℍ → ℂ) (ofComplex z))]

theorem realize_const_eventuallyEq (c : ℂ) (τ : ℍ) :
    (fun z : ℂ => realizeOf Γ (algebraMap ℂ (LaurentSeries ℂ) c) (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun _ => c := by
  filter_upwards [realize_eventuallyEq (Pres.const (Γ := Γ) c) τ] with z h1
  rw [h1, FunLike.coe_smul, ModularForm.one_coe_eq_one]
  simp

theorem realize_smul_eventuallyEq {x : LaurentSeries ℂ} (P : Pres Γ x)
    (γ : Γ) (τ : ℍ) :
    (fun z : ℂ => realizeOf Γ x ((((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)) • ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z : ℂ => realizeOf Γ x (ofComplex z) := by
  filter_upwards [eventually_ne_zero_ofComplex P.h P.h_ne τ] with z hz
  have hsm : (((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)) • ofComplex z = (γ : SL(2, ℤ)) • ofComplex z := by
    simp
  have hh : (P.h : ℍ → ℂ) ((γ : SL(2, ℤ)) • ofComplex z) =
      denom (γ : SL(2, ℤ)) (ofComplex z) ^ P.k * (P.h : ℍ → ℂ) (ofComplex z) :=
    SlashInvariantForm.slash_action_eqn_SL'' P.h γ.2 _
  have hg : (P.g : ℍ → ℂ) ((γ : SL(2, ℤ)) • ofComplex z) =
      denom (γ : SL(2, ℤ)) (ofComplex z) ^ P.k * (P.g : ℍ → ℂ) (ofComplex z) :=
    SlashInvariantForm.slash_action_eqn_SL'' P.g γ.2 _
  have hd : (denom (γ : SL(2, ℤ)) (ofComplex z) : ℂ) ^ P.k ≠ 0 :=
    zpow_ne_zero _ (denom_ne_zero _ _)
  have hne : (P.h : ℍ → ℂ) ((γ : SL(2, ℤ)) • ofComplex z) ≠ 0 := by
    rw [hh]; exact mul_ne_zero hd hz
  rw [hsm, ModularCurve.realizeOf_eq_div Γ hT.out P.g P.h x P.eq _ hne,
    ModularCurve.realizeOf_eq_div Γ hT.out P.g P.h x P.eq _ hz, hg, hh, mul_div_mul_left _ _ hd]

theorem realize_neg_eventuallyEq {x : LaurentSeries ℂ} (P : Pres Γ x) (τ : ℍ) :
    (fun z : ℂ => realizeOf Γ (-x) (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z : ℂ => -realizeOf Γ x (ofComplex z) := by
  have hneg : -x = algebraMap ℂ (LaurentSeries ℂ) (-1) * x := by rw [map_neg, map_one]; ring
  rw [hneg]
  filter_upwards [realize_mul_eventuallyEq (Pres.const (Γ := Γ) (-1)) P τ,
    realize_const_eventuallyEq (Γ := Γ) (-1) τ] with z h1 h2
  rw [h1, Pi.mul_apply, h2]
  ring

theorem realize_inv_eventuallyEq {x : LaurentSeries ℂ} (P : Pres Γ x) (τ : ℍ) :
    (fun z : ℂ => realizeOf Γ x⁻¹ (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z : ℂ => (realizeOf Γ x (ofComplex z))⁻¹ := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [inv_zero]
    filter_upwards [realize_const_eventuallyEq (Γ := Γ) 0 τ] with z hz
    rw [map_zero] at hz
    rw [hz, inv_zero]
  · filter_upwards [realize_eventuallyEq (P.inv hx) τ, realize_eventuallyEq P τ] with z h1 h2
    rw [h1, h2, inv_div]

/-! ## The base-changed field and a presentation of each of its elements -/

abbrev CF (Γ : Subgroup SL(2, ℤ)) : Type :=
  ↥(laurentBaseChange ℂ (qExpFunctionFieldC ℚ Γ))

def pres (x : CF Γ) : Pres Γ (x : LaurentSeries ℂ) :=
  let E := exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC_of_T_mem
    Γ hT.out (x : LaurentSeries ℂ) x.2
  ⟨E.choose, E.choose_spec.choose, E.choose_spec.choose_spec.choose,
    E.choose_spec.choose_spec.choose_spec.1, E.choose_spec.choose_spec.choose_spec.2⟩

/-! ## The order function `mu` and the place it defines -/

def mu (τ : ℍ) (x : CF Γ) : WithTop ℤ :=
  meromorphicOrderAt (fun z : ℂ => realizeOf Γ (x : LaurentSeries ℂ) (ofComplex z)) (τ : ℂ)

theorem meromorphicAt_realize' (x : CF Γ) (τ : ℍ) :
    MeromorphicAt (fun z : ℂ => realizeOf Γ (x : LaurentSeries ℂ) (ofComplex z)) (τ : ℂ) :=
  meromorphicAt_realize (pres x) τ

theorem mu_mul (τ : ℍ) (x y : CF Γ) : mu τ (x * y) = mu τ x + mu τ y := by
  show meromorphicOrderAt
      (fun z : ℂ => realizeOf Γ ((x : LaurentSeries ℂ) * (y : LaurentSeries ℂ)) (ofComplex z))
      (τ : ℂ) = _
  rw [meromorphicOrderAt_congr (realize_mul_eventuallyEq (pres x) (pres y) τ),
    meromorphicOrderAt_mul (meromorphicAt_realize' x τ) (meromorphicAt_realize' y τ)]
  rfl

theorem mu_add (τ : ℍ) (x y : CF Γ) : min (mu τ x) (mu τ y) ≤ mu τ (x + y) := by
  show _ ≤ meromorphicOrderAt
      (fun z : ℂ => realizeOf Γ ((x : LaurentSeries ℂ) + (y : LaurentSeries ℂ)) (ofComplex z))
      (τ : ℂ)
  rw [meromorphicOrderAt_congr (realize_add_eventuallyEq (pres x) (pres y) τ)]
  exact meromorphicOrderAt_add (meromorphicAt_realize' x τ) (meromorphicAt_realize' y τ)

theorem mu_algebraMap (τ : ℍ) (c : ℂ) (hc : c ≠ 0) :
    mu τ (algebraMap ℂ (CF Γ) c) = 0 := by
  classical
  show meromorphicOrderAt
      (fun z : ℂ => realizeOf Γ (algebraMap ℂ (LaurentSeries ℂ) c) (ofComplex z)) (τ : ℂ) = 0
  rw [meromorphicOrderAt_congr (realize_const_eventuallyEq c τ), meromorphicOrderAt_const]
  simp [hc]

theorem mu_eq_top_iff (τ : ℍ) (x : CF Γ) : mu τ x = ⊤ ↔ x = 0 := by
  obtain ⟨m, hm0, hmh, hmu⟩ := meromorphicOrderAt_realize_eq (pres x) τ
  constructor
  · intro hx
    unfold mu at hx
    rw [hx] at hmu
    have hg : meromorphicOrderAt (fun z : ℂ => ((pres x).g : ℍ → ℂ) (ofComplex z)) (τ : ℂ) = ⊤ := by
      rcases WithTop.add_eq_top.mp hmu.symm with h | h
      · exact h
      · exact absurd h WithTop.coe_ne_top
    have hg0 : (pres x).g = 0 := by
      by_contra hne
      exact meromorphicOrderAt_comp_ofComplex_ne_top _ hne τ hg
    have heq := (pres x).eq
    rw [hg0, show qL (0 : ModularForm Γ (pres x).k) = 0 by
      simp [qL, UpperHalfPlane.qExpansion_zero]] at heq
    have hx0 : (x : LaurentSeries ℂ) = 0 :=
      (mul_eq_zero.mp heq).resolve_right (qL_ne_zero hT.out _ (pres x).h_ne)
    exact_mod_cast hx0
  · rintro rfl
    have heq : (0 : LaurentSeries ℂ) * qL (pres (0 : CF Γ)).h = qL (pres (0 : CF Γ)).g :=
      (pres (0 : CF Γ)).eq
    rw [zero_mul] at heq
    have hg0 : (pres (0 : CF Γ)).g = 0 := by
      by_contra hne
      exact qL_ne_zero hT.out _ hne heq.symm
    unfold mu
    rw [hmu, hg0]
    have h0 : meromorphicOrderAt (fun z : ℂ =>
        ((0 : ModularForm Γ (pres (0 : CF Γ)).k) : ℍ → ℂ)
          (ofComplex z)) (τ : ℂ) = ⊤ :=
      meromorphicOrderAt_eq_top_iff.mpr (Filter.Eventually.of_forall fun _ => by simp)
    rw [h0, top_add]

theorem mu_ne_top (τ : ℍ) {x : CF Γ} (hx : x ≠ 0) : mu τ x ≠ ⊤ :=
  fun h => hx ((mu_eq_top_iff τ x).mp h)

theorem mu_one (τ : ℍ) : mu τ (1 : CF Γ) = 0 := by
  rw [← map_one (algebraMap ℂ (CF Γ))]
  exact mu_algebraMap τ 1 one_ne_zero

def X (Γ : Subgroup SL(2, ℤ)) : CF Γ :=
  ⟨coeffEmb ℂ (jqModC ℚ), coeffEmb_mem_laurentBaseChange ℂ
    (intFormRatiosC_subset ℚ Γ (ModularCurve.jqModC_mem_intFormRatiosC ℚ Γ))⟩

omit hT in
theorem X_ne_algebraMap (c : ℂ) : X Γ ≠ algebraMap ℂ (CF Γ) c := by
  intro h
  have h1 := congrArg (fun y : CF Γ => (y : LaurentSeries ℂ).coeff (-1)) h
  simp only [X] at h1
  rw [coeffEmb_coeff, jqModC_rat, coeff_jq_neg_one, map_one] at h1
  have h2 : ((algebraMap ℂ (CF Γ) c : CF Γ) : LaurentSeries ℂ) = algebraMap ℂ (LaurentSeries ℂ) c :=
    rfl
  rw [h2, algebraMap_laurentSeries_eq_C, HahnSeries.C_apply, HahnSeries.coeff_single_of_ne
    (by norm_num)] at h1
  exact one_ne_zero h1

omit hT in
theorem X_ne_zero : X Γ ≠ 0 := by
  simpa using X_ne_algebraMap (Γ := Γ) 0

theorem exists_mu_pos (τ : ℍ) : ∃ x : CF Γ, 0 < mu τ x ∧ mu τ x ≠ ⊤ := by
  have hXt := mu_ne_top τ (X_ne_zero (Γ := Γ))
  by_cases hneg : mu τ (X Γ) < 0
  · refine ⟨(X Γ)⁻¹, ?_, mu_ne_top τ (inv_ne_zero (X_ne_zero (Γ := Γ)))⟩
    have hsum : mu τ (X Γ)⁻¹ + mu τ (X Γ) = 0 := by
      rw [← mu_mul, inv_mul_cancel₀ (X_ne_zero (Γ := Γ)), mu_one]
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hXt
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (mu_ne_top τ (inv_ne_zero (X_ne_zero (Γ := Γ))))
    rw [← hm, ← hn, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_eq_coe] at hsum
    rw [← hm, ← WithTop.coe_zero, WithTop.coe_lt_coe] at hneg
    rw [← hn, ← WithTop.coe_zero, WithTop.coe_lt_coe]
    omega
  · rw [not_lt] at hneg
    obtain ⟨c, hc⟩ :=
      (tendsto_nhds_iff_meromorphicOrderAt_nonneg (meromorphicAt_realize' (X Γ) τ)).mpr hneg
    refine ⟨X Γ - algebraMap ℂ (CF Γ) c, ?_, mu_ne_top τ (sub_ne_zero.mpr (X_ne_algebraMap c))⟩
    apply (tendsto_zero_iff_meromorphicOrderAt_pos (meromorphicAt_realize' _ τ)).mp
    have hlim : Tendsto ((fun z : ℂ => realizeOf Γ ((X Γ : CF Γ) : LaurentSeries ℂ) (ofComplex z)) +
        fun _ => -c) (𝓝[≠] (τ : ℂ)) (𝓝 0) := by
      have h__af := hc.add (tendsto_const_nhds (x := -c))
      simp at h__af
      exact h__af
    refine hlim.congr' ?_
    have hcoe : ((X Γ - algebraMap ℂ (CF Γ) c : CF Γ) : LaurentSeries ℂ) =
        ((X Γ : CF Γ) : LaurentSeries ℂ) + algebraMap ℂ (LaurentSeries ℂ) (-c) := by
      rw [map_neg, ← sub_eq_add_neg]; rfl
    rw [hcoe]
    exact ((realize_add_eventuallyEq (pres (X Γ)) (Pres.const (Γ := Γ) (-c)) τ).trans
      (EventuallyEq.rfl.add (realize_const_eventuallyEq (-c) τ))).symm

theorem mu_smul (γ : Γ) (τ : ℍ) (x : CF Γ) :
    mu ((γ : SL(2, ℤ)) • τ) x = mu τ x := by
  unfold mu
  have hdet1 : (((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)).val.det = 1 := Matrix.SpecialLinearGroup.det_coe _
  have hdet : 0 < (((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)).val.det := by rw [hdet1]; exact one_pos
  rw [show ((((γ : SL(2, ℤ)) • τ : ℍ)) : ℂ) = ↑((((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)) • τ) by simp,
    ← meromorphicOrderAt_comp_smul hdet]
  exact meromorphicOrderAt_congr (realize_smul_eventuallyEq (pres x) γ τ)

theorem mu_nonneg_iff (τ : ℍ) (x : CF Γ) :
    0 ≤ mu τ x ↔
      IsBoundedUnder (· ≤ ·) (𝓝[≠] τ) (fun z : ℍ => ‖realizeOf Γ (x : LaurentSeries ℂ) z‖) := by
  rw [← isBoundedUnder_nhdsNE_coe_iff, mu,
    ← tendsto_nhds_iff_meromorphicOrderAt_nonneg (meromorphicAt_realize' x τ)]
  constructor
  · rintro ⟨c, hc⟩
    exact hc.norm.isBoundedUnder_le
  · intro hb
    by_contra hno
    have hneg : meromorphicOrderAt
        (fun z : ℂ => realizeOf Γ (x : LaurentSeries ℂ) (ofComplex z)) (τ : ℂ) < 0 := by
      rw [tendsto_nhds_iff_meromorphicOrderAt_nonneg (meromorphicAt_realize' x τ), not_le] at hno
      exact hno
    have hcob := (tendsto_cobounded_iff_meromorphicOrderAt_neg (meromorphicAt_realize' x τ)).mpr hneg
    rw [← tendsto_norm_atTop_iff_cobounded] at hcob
    exact Filter.not_isBoundedUnder_of_tendsto_atTop hcob hb

theorem exists_place (τ : ℍ) :
    ∃ (P : AlgebraicCurve.Place ℂ (CF Γ)) (e : ℕ), 0 < e ∧
      (∀ x, x ∈ P.toValuationSubring ↔ 0 ≤ mu τ x) ∧
      ∀ x, x ≠ 0 → mu τ x = (((e : ℤ) * P.ord x : ℤ) : WithTop ℤ) :=
  AlgebraicCurve.Place.exists_of_orderMap (mu τ) (mu_eq_top_iff τ) (mu_mul τ) (mu_add τ)
    (fun c hc => mu_algebraMap τ c hc) (exists_mu_pos τ)

end Engine

/-! ## The Möbius transport of the punctured neighbourhood

`γ` (for the `Γ₀(M)` pull-back) and `J` (for conjugation) are the same transport at
two group elements, so `moeb`, its continuity at a punctured neighbourhood, the
eventual transport of a predicate along it and the boundedness transfer are written
once, at `g : GL (Fin 2) ℝ`. -/

section Transport

private def moeb (g : GL (Fin 2) ℝ) : ℍ ≃ₜ ℍ := Homeomorph.smul g

private theorem moeb_apply (g : GL (Fin 2) ℝ) (τ : ℍ) : moeb g τ = g • τ := rfl

private theorem tendsto_moeb_nhdsNE (g : GL (Fin 2) ℝ) (τ : ℍ) :
    Tendsto (fun w : ℍ => g • w) (𝓝[≠] τ) (𝓝[≠] (g • τ)) := by
  have h := (moeb g).map_punctured_nhds_eq τ
  simpa [moeb] using h ▸ Filter.tendsto_map

private theorem eventually_smul_of_eventually {p : ℍ → Prop} (g : GL (Fin 2) ℝ) (τ : ℍ)
    (h : ∀ᶠ z in 𝓝[≠] (((g • τ : ℍ)) : ℂ), p (ofComplex z)) :
    ∀ᶠ z in 𝓝[≠] (τ : ℂ), p (g • ofComplex z) := by
  rw [eventually_nhdsNE_coe_iff] at h
  exact (eventually_nhdsNE_coe_iff (p := fun w => p (g • w))).mpr
    ((tendsto_moeb_nhdsNE g τ).eventually h)

private theorem isBoundedUnder_comp_smul_iff (g : GL (Fin 2) ℝ) (u : ℍ → ℝ) (τ : ℍ) :
    IsBoundedUnder (· ≤ ·) (𝓝[≠] τ) (fun w : ℍ => u (g • w)) ↔
      IsBoundedUnder (· ≤ ·) (𝓝[≠] (g • τ)) u := by
  have h : Filter.map (fun w : ℍ => g • w) (𝓝[≠] τ) = 𝓝[≠] (g • τ) :=
    (moeb g).map_punctured_nhds_eq τ
  have hfun : (fun w : ℍ => u (g • w)) = u ∘ (fun w : ℍ => g • w) := rfl
  rw [hfun, ← Filter.isBoundedUnder_map_iff, h]

private theorem sl_smul_upperHalf (γ : SL(2, ℤ)) (τ : ℍ) :
    γ • τ = ((γ : GL (Fin 2) ℝ)) • τ := by simp

theorem isBoundedUnder_congr_of_eventuallyEq {α β : Type*} {r : β → β → Prop}
    {l : Filter α} {u v : α → β} (h : u =ᶠ[l] v) : IsBoundedUnder r l u ↔ IsBoundedUnder r l v := by
  show (Filter.map u l).IsBounded r ↔ (Filter.map v l).IsBounded r
  rw [Filter.map_congr h]

private theorem mem_smul_place_iff {F₀ : IntermediateField ℚ (LaurentSeries ℚ)}
    (g : AlgebraicCurve.SemilinearAut ℂ ↥(laurentBaseChange ℂ F₀))
    (v : AlgebraicCurve.Place ℂ ↥(laurentBaseChange ℂ F₀))
    (x : ↥(laurentBaseChange ℂ F₀)) :
    x ∈ (g • v).toValuationSubring ↔ g⁻¹ • x ∈ v.toValuationSubring := by
  rw [AlgebraicCurve.SemilinearAut.smul_toValuationSubring]
  exact ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem

end Transport

/-! ## The `Γ₀(M)` pull-back: the `γ`-twist of every integral q-expansion ratio -/

section Diamond

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ}

theorem gammaH_le_conj (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) :
    (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) ≤
      ConjAct.toConjAct ((γ : GL (Fin 2) ℝ))⁻¹ •
        (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) := by
  intro A hA
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hA
  rw [map_inv, Subgroup.mem_inv_pointwise_smul_iff, ConjAct.toConjAct_smul]
  refine Subgroup.mem_map.mpr ⟨γ * a * γ⁻¹, ?_, ?_⟩
  · exact CohCarrier.conj_mem_GammaH M H ⟨γ, hγ⟩ ⟨a, ha⟩
  · show Matrix.SpecialLinearGroup.mapGL ℝ (γ * a * γ⁻¹) =
      Matrix.SpecialLinearGroup.mapGL ℝ γ * Matrix.SpecialLinearGroup.mapGL ℝ a *
        (Matrix.SpecialLinearGroup.mapGL ℝ γ)⁻¹
    rw [map_mul, map_mul, map_inv]

variable {k : ℤ}

private def slashForm (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M)
    (f : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k) :
    ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k :=
  restrictForm (gammaH_le_conj γ hγ) (ModularForm.translate f (γ : GL (Fin 2) ℝ))

private theorem coe_slashForm (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M)
    (f : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k) :
    (⇑(slashForm γ hγ f) : ℍ → ℂ) = (⇑f : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ) :=
  rfl

private theorem slashForm_apply (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M)
    (f : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k) (τ : ℍ) :
    slashForm γ hγ f τ = f (γ • τ) * (denom γ τ) ^ (-k) := by
  rw [show slashForm γ hγ f τ = ((⇑f : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ)) τ from rfl,
    ← ModularForm.SL_slash, ModularForm.SL_slash_apply]

private theorem slashForm_ne_zero (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M)
    (f : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k) (hf : f ≠ 0) :
    slashForm γ hγ f ≠ 0 := by
  intro h0
  apply hf
  have hfun : (⇑f : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ) = 0 := by
    rw [← coe_slashForm γ hγ f, h0]; rfl
  have : (⇑f : ℍ → ℂ) = 0 := by
    have h2 := congrArg (fun F : ℍ → ℂ => F ∣[k] ((γ : GL (Fin 2) ℝ))⁻¹) hfun
    simpa only [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one,
      SlashAction.zero_slash] using h2
  exact DFunLike.coe_injective (this.trans FunLike.coe_zero.symm)

def IsPullbackAlong (M : ℕ) (H : Subgroup (ZMod M)ˣ)
    (σ : ↥(laurentBaseChange ℂ (xHFunctionField M H)) ≃ₐ[ℂ]
      ↥(laurentBaseChange ℂ (xHFunctionField M H)))
    (γ : SL(2, ℤ)) : Prop :=
  ∀ (k : ℤ) (f g : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
    (pf pg : PowerSeries ℤ) (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC ℚ pg ≠ 0),
    ((σ ⟨coeffEmb ℂ (intSeriesC ℚ pf / intSeriesC ℚ pg),
          coeffEmb_mem_laurentBaseChange ℂ (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ :
        ↥(laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) *
        HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑g ∣[k] (γ : GL (Fin 2) ℝ))) =
      HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑f ∣[k] (γ : GL (Fin 2) ℝ)))

end Diamond

/-! ## The `Key` of the `Γ₀(M)` pull-back, propagated from the generators -/

section DiamondKey

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ}

private instance factT : Fact (ModularGroup.T ∈ CohCarrier.GammaH M H) :=
  ⟨CohCarrier.translation_mem_GammaH M H⟩

variable (σ : (laurentBaseChange ℂ (xHFunctionField M H)) ≃ₐ[ℂ]
    (laurentBaseChange ℂ (xHFunctionField M H))) (γ : SL(2, ℤ))

private def Key (y : (laurentBaseChange ℂ (xHFunctionField M H))) : Prop :=
  ∀ τ : ℍ, (fun z : ℂ => realizeOf (CohCarrier.GammaH M H)
      ((σ y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
    fun z : ℂ => realizeOf (CohCarrier.GammaH M H)
      ((y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) (γ • ofComplex z)

theorem key_algebraMap (c : ℂ) :
    Key σ γ (algebraMap ℂ (laurentBaseChange ℂ (xHFunctionField M H)) c) := by
  intro τ
  rw [AlgEquiv.commutes]
  have h1 := realize_const_eventuallyEq (Γ := CohCarrier.GammaH M H) c τ
  have h2 := eventually_smul_of_eventually (p := fun w => realizeOf (CohCarrier.GammaH M H)
    (algebraMap ℂ (LaurentSeries ℂ) c) w = c) ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) τ
    (realize_const_eventuallyEq (Γ := CohCarrier.GammaH M H) c (γ • τ))
  filter_upwards [h1, h2] with z e1 e2
  exact e1.trans e2.symm

theorem Key.add {x y : (laurentBaseChange ℂ (xHFunctionField M H))}
    (hx : Key σ γ x) (hy : Key σ γ y) : Key σ γ (x + y) := by
  intro τ
  rw [map_add]
  have h1 := realize_add_eventuallyEq (pres (σ x)) (pres (σ y)) τ
  have h2 := eventually_smul_of_eventually
    (p := fun w => realizeOf (CohCarrier.GammaH M H)
      (((x : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) +
        ((y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ)) w =
      realizeOf (CohCarrier.GammaH M H) ((x : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) w +
        realizeOf (CohCarrier.GammaH M H) ((y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) w)
    ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) τ (realize_add_eventuallyEq (pres x) (pres y) (γ • τ))
  filter_upwards [h1, h2, hx τ, hy τ] with z e1 e2 e3 e4
  show realizeOf (CohCarrier.GammaH M H)
      (((σ x : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) +
        ((σ y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ)) (ofComplex z) =
    realizeOf (CohCarrier.GammaH M H)
      (((x : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) +
        ((y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ)) (γ • ofComplex z)
  rw [e1, Pi.add_apply, e3, e4, sl_smul_upperHalf, e2]

theorem Key.mul {x y : (laurentBaseChange ℂ (xHFunctionField M H))}
    (hx : Key σ γ x) (hy : Key σ γ y) : Key σ γ (x * y) := by
  intro τ
  rw [map_mul]
  have h1 := realize_mul_eventuallyEq (pres (σ x)) (pres (σ y)) τ
  have h2 := eventually_smul_of_eventually
    (p := fun w => realizeOf (CohCarrier.GammaH M H)
      (((x : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) *
        ((y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ)) w =
      realizeOf (CohCarrier.GammaH M H) ((x : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) w *
        realizeOf (CohCarrier.GammaH M H) ((y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) w)
    ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) τ (realize_mul_eventuallyEq (pres x) (pres y) (γ • τ))
  filter_upwards [h1, h2, hx τ, hy τ] with z e1 e2 e3 e4
  show realizeOf (CohCarrier.GammaH M H)
      (((σ x : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) *
        ((σ y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ)) (ofComplex z) =
    realizeOf (CohCarrier.GammaH M H)
      (((x : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) *
        ((y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ)) (γ • ofComplex z)
  rw [e1, Pi.mul_apply, e3, e4, sl_smul_upperHalf, e2]

theorem Key.neg {x : (laurentBaseChange ℂ (xHFunctionField M H))}
    (hx : Key σ γ x) : Key σ γ (-x) := by
  intro τ
  rw [map_neg]
  have h1 := realize_neg_eventuallyEq (pres (σ x)) τ
  have h2 := eventually_smul_of_eventually
    (p := fun w => realizeOf (CohCarrier.GammaH M H)
      (-((x : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ)) w =
      -realizeOf (CohCarrier.GammaH M H) ((x : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) w)
    ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) τ (realize_neg_eventuallyEq (pres x) (γ • τ))
  filter_upwards [h1, h2, hx τ] with z e1 e2 e3
  show realizeOf (CohCarrier.GammaH M H)
      (-((σ x : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ)) (ofComplex z) =
    realizeOf (CohCarrier.GammaH M H)
      (-((x : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ)) (γ • ofComplex z)
  rw [e1, e3, sl_smul_upperHalf, e2]

theorem Key.inv {x : (laurentBaseChange ℂ (xHFunctionField M H))}
    (hx : Key σ γ x) : Key σ γ x⁻¹ := by
  intro τ
  rw [map_inv₀]
  have h1 := realize_inv_eventuallyEq (pres (σ x)) τ
  have h2 := eventually_smul_of_eventually
    (p := fun w => realizeOf (CohCarrier.GammaH M H)
      (((x : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ)⁻¹) w =
      (realizeOf (CohCarrier.GammaH M H)
        ((x : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) w)⁻¹)
    ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) τ (realize_inv_eventuallyEq (pres x) (γ • τ))
  filter_upwards [h1, h2, hx τ] with z e1 e2 e3
  show realizeOf (CohCarrier.GammaH M H)
      (((σ x : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ)⁻¹) (ofComplex z) =
    realizeOf (CohCarrier.GammaH M H)
      (((x : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ)⁻¹) (γ • ofComplex z)
  rw [e1, e3, sl_smul_upperHalf, e2]

variable (hγ : γ ∈ CongruenceSubgroup.Gamma0 M)

include hγ in
theorem key_generator
    (hσ : IsPullbackAlong M H σ γ)
    {k : ℤ} (f g : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
    (pf pg : PowerSeries ℤ) (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC ℚ pg ≠ 0) :
    Key σ γ ⟨coeffEmb ℂ (intSeriesC ℚ pf / intSeriesC ℚ pg),
      coeffEmb_mem_laurentBaseChange ℂ (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ := by
  intro τ
  have hgq : qL g ≠ 0 := by
    rw [← coeffEmb_intSeriesC_eq_qL hg]
    intro h0
    apply hg0
    have hinj : Function.Injective (coeffEmb ℂ : LaurentSeries ℚ → LaurentSeries ℂ) :=
      (coeffEmb ℂ).injective
    exact hinj (h0.trans (map_zero _).symm)
  have hgne : g ≠ 0 := by
    intro h; apply hgq; simp [qL, h, UpperHalfPlane.qExpansion_zero]
  set y : (laurentBaseChange ℂ (xHFunctionField M H)) :=
    ⟨coeffEmb ℂ (intSeriesC ℚ pf / intSeriesC ℚ pg),
      coeffEmb_mem_laurentBaseChange ℂ (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ with hydef
  have hpres : ((σ y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) *
      qL (slashForm γ hγ g) = qL (slashForm γ hγ f) :=
    hσ k f g pf pg hf hg hg0
  let Pσ : Pres (CohCarrier.GammaH M H)
      ((σ y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) :=
    ⟨k, slashForm γ hγ f, slashForm γ hγ g, slashForm_ne_zero γ hγ g hgne, hpres⟩
  have hy : ((y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) * qL g = qL f := by
    show coeffEmb ℂ (intSeriesC ℚ pf / intSeriesC ℚ pg) * qL g = qL f
    rw [map_div₀, coeffEmb_intSeriesC_eq_qL hf, coeffEmb_intSeriesC_eq_qL hg, div_mul_cancel₀ _ hgq]
  let Py : Pres (CohCarrier.GammaH M H)
      ((y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) := ⟨k, f, g, hgne, hy⟩
  have h1 := realize_eventuallyEq Pσ τ
  have h2 := eventually_smul_of_eventually
    (p := fun w => realizeOf (CohCarrier.GammaH M H)
      ((y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) w =
      (f : ℍ → ℂ) w / (g : ℍ → ℂ) w) ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) τ
    (by
      filter_upwards [realize_eventuallyEq Py (γ • τ)] with z hz
      exact hz)
  have h3 := eventually_smul_of_eventually (p := fun w => (g : ℍ → ℂ) w ≠ 0)
    ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) τ (eventually_ne_zero_ofComplex g hgne (γ • τ))
  filter_upwards [h1, h2, h3] with z e1 e2 e3
  rw [e1, sl_smul_upperHalf, e2]
  show (slashForm γ hγ f : ℍ → ℂ) (ofComplex z) / (slashForm γ hγ g : ℍ → ℂ) (ofComplex z) = _
  rw [slashForm_apply, slashForm_apply, sl_smul_upperHalf,
    mul_div_mul_right _ _ (zpow_ne_zero _ (denom_ne_zero γ (ofComplex z)))]

include hγ in
theorem key_all
    (hσ : IsPullbackAlong M H σ γ)
    (y : (laurentBaseChange ℂ (xHFunctionField M H))) : Key σ γ y := by
  obtain ⟨x, hx⟩ := y
  have inner : ∀ (w : LaurentSeries ℚ) (hw : w ∈ xHFunctionField M H),
      Key σ γ ⟨coeffEmb ℂ w, coeffEmb_mem_laurentBaseChange ℂ hw⟩ := by
    intro w hw
    have hw' : w ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪
        intFormRatiosC ℚ (CohCarrier.GammaH M H)) := hw
    induction hw' using Subfield.closure_induction with
    | mem z hz =>
        rcases hz with ⟨r, rfl⟩ | ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩
        · have : (⟨coeffEmb ℂ (algebraMap ℚ (LaurentSeries ℚ) r), coeffEmb_mem_laurentBaseChange ℂ hw⟩ :
              (laurentBaseChange ℂ (xHFunctionField M H))) =
              algebraMap ℂ (laurentBaseChange ℂ (xHFunctionField M H)) (r : ℂ) := by
            apply Subtype.ext
            show coeffEmb ℂ (algebraMap ℚ (LaurentSeries ℚ) r) = algebraMap ℂ (LaurentSeries ℂ) (r : ℂ)
            rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffEmb,
              coeffMap_single]
            simp
          rw [this]
          exact key_algebraMap σ γ (r : ℂ)
        · exact key_generator σ γ hγ hσ f g pf pg hf hg hg0
    | one =>
        have : (⟨coeffEmb ℂ 1, coeffEmb_mem_laurentBaseChange ℂ hw⟩ :
            (laurentBaseChange ℂ (xHFunctionField M H))) =
            algebraMap ℂ (laurentBaseChange ℂ (xHFunctionField M H)) 1 := by
          apply Subtype.ext; show coeffEmb ℂ 1 = algebraMap ℂ (LaurentSeries ℂ) 1; rw [map_one, map_one]
        rw [this]; exact key_algebraMap σ γ 1
    | add a b ha hb iha ihb =>
        have hmem_a : a ∈ xHFunctionField M H := ha
        have hmem_b : b ∈ xHFunctionField M H := hb
        have : (⟨coeffEmb ℂ (a + b), coeffEmb_mem_laurentBaseChange ℂ hw⟩ :
            (laurentBaseChange ℂ (xHFunctionField M H))) =
            (⟨coeffEmb ℂ a, coeffEmb_mem_laurentBaseChange ℂ hmem_a⟩ :
              (laurentBaseChange ℂ (xHFunctionField M H))) +
              ⟨coeffEmb ℂ b, coeffEmb_mem_laurentBaseChange ℂ hmem_b⟩ := by
          apply Subtype.ext; show coeffEmb ℂ (a + b) = coeffEmb ℂ a + coeffEmb ℂ b; rw [map_add]
        rw [this]; exact (iha hmem_a).add σ γ (ihb hmem_b)
    | neg a ha iha =>
        have hmem_a : a ∈ xHFunctionField M H := ha
        have : (⟨coeffEmb ℂ (-a), coeffEmb_mem_laurentBaseChange ℂ hw⟩ :
            (laurentBaseChange ℂ (xHFunctionField M H))) =
            -(⟨coeffEmb ℂ a, coeffEmb_mem_laurentBaseChange ℂ hmem_a⟩ :
              (laurentBaseChange ℂ (xHFunctionField M H))) := by
          apply Subtype.ext; show coeffEmb ℂ (-a) = -coeffEmb ℂ a; rw [map_neg]
        rw [this]; exact (iha hmem_a).neg σ γ
    | inv a ha iha =>
        have hmem_a : a ∈ xHFunctionField M H := ha
        have : (⟨coeffEmb ℂ a⁻¹, coeffEmb_mem_laurentBaseChange ℂ hw⟩ :
            (laurentBaseChange ℂ (xHFunctionField M H))) =
            (⟨coeffEmb ℂ a, coeffEmb_mem_laurentBaseChange ℂ hmem_a⟩ :
              (laurentBaseChange ℂ (xHFunctionField M H)))⁻¹ := by
          apply Subtype.ext; show coeffEmb ℂ a⁻¹ = (coeffEmb ℂ a)⁻¹; rw [map_inv₀]
        rw [this]; exact (iha hmem_a).inv σ γ
    | mul a b ha hb iha ihb =>
        have hmem_a : a ∈ xHFunctionField M H := ha
        have hmem_b : b ∈ xHFunctionField M H := hb
        have : (⟨coeffEmb ℂ (a * b), coeffEmb_mem_laurentBaseChange ℂ hw⟩ :
            (laurentBaseChange ℂ (xHFunctionField M H))) =
            (⟨coeffEmb ℂ a, coeffEmb_mem_laurentBaseChange ℂ hmem_a⟩ :
              (laurentBaseChange ℂ (xHFunctionField M H))) *
              ⟨coeffEmb ℂ b, coeffEmb_mem_laurentBaseChange ℂ hmem_b⟩ := by
          apply Subtype.ext; show coeffEmb ℂ (a * b) = coeffEmb ℂ a * coeffEmb ℂ b; rw [map_mul]
        rw [this]; exact (iha hmem_a).mul σ γ (ihb hmem_b)
  have hx' : x ∈ Subfield.closure (Set.range (algebraMap ℂ (LaurentSeries ℂ)) ∪
      (coeffEmb ℂ) '' (xHFunctionField M H : Set (LaurentSeries ℚ))) :=
    (mem_laurentBaseChange_iff).mp hx
  induction hx' using Subfield.closure_induction with
  | mem z hz =>
      rcases hz with ⟨c, rfl⟩ | ⟨w, hw, rfl⟩
      · have : (⟨algebraMap ℂ (LaurentSeries ℂ) c, hx⟩ :
          (laurentBaseChange ℂ (xHFunctionField M H))) =
          algebraMap ℂ (laurentBaseChange ℂ (xHFunctionField M H)) c := Subtype.ext rfl
        rw [this]; exact key_algebraMap σ γ c
      · exact inner w hw
  | one =>
      have : (⟨1, hx⟩ : (laurentBaseChange ℂ (xHFunctionField M H))) =
          algebraMap ℂ (laurentBaseChange ℂ (xHFunctionField M H)) 1 := Subtype.ext (by simp)
      rw [this]; exact key_algebraMap σ γ 1
  | add a b ha hb iha ihb =>
      have hma : a ∈ laurentBaseChange ℂ (xHFunctionField M H) := (mem_laurentBaseChange_iff).mpr ha
      have hmb : b ∈ laurentBaseChange ℂ (xHFunctionField M H) := (mem_laurentBaseChange_iff).mpr hb
      have : (⟨a + b, hx⟩ : (laurentBaseChange ℂ (xHFunctionField M H))) =
          (⟨a, hma⟩ : (laurentBaseChange ℂ (xHFunctionField M H))) + ⟨b, hmb⟩ := Subtype.ext rfl
      rw [this]; exact (iha hma).add σ γ (ihb hmb)
  | neg a ha iha =>
      have hma : a ∈ laurentBaseChange ℂ (xHFunctionField M H) := (mem_laurentBaseChange_iff).mpr ha
      have : (⟨-a, hx⟩ : (laurentBaseChange ℂ (xHFunctionField M H))) =
          -(⟨a, hma⟩ : (laurentBaseChange ℂ (xHFunctionField M H))) := Subtype.ext rfl
      rw [this]; exact (iha hma).neg σ γ
  | inv a ha iha =>
      have hma : a ∈ laurentBaseChange ℂ (xHFunctionField M H) := (mem_laurentBaseChange_iff).mpr ha
      have : (⟨a⁻¹, hx⟩ : (laurentBaseChange ℂ (xHFunctionField M H))) =
          (⟨a, hma⟩ : (laurentBaseChange ℂ (xHFunctionField M H)))⁻¹ := Subtype.ext rfl
      rw [this]; exact (iha hma).inv σ γ
  | mul a b ha hb iha ihb =>
      have hma : a ∈ laurentBaseChange ℂ (xHFunctionField M H) := (mem_laurentBaseChange_iff).mpr ha
      have hmb : b ∈ laurentBaseChange ℂ (xHFunctionField M H) := (mem_laurentBaseChange_iff).mpr hb
      have : (⟨a * b, hx⟩ : (laurentBaseChange ℂ (xHFunctionField M H))) =
          (⟨a, hma⟩ : (laurentBaseChange ℂ (xHFunctionField M H))) * ⟨b, hmb⟩ := Subtype.ext rfl
      rw [this]; exact (iha hma).mul σ γ (ihb hmb)

end DiamondKey

/-! ## The place-level `Γ₀(M)` pull-back -/

section DiamondPlace

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ}

theorem smul_pt_eq
    (D : ComplexPlaceDictionaryOf (CohCarrier.GammaH M H) (xHFunctionField M H))
    (σ : (laurentBaseChange ℂ (xHFunctionField M H)) ≃ₐ[ℂ]
      (laurentBaseChange ℂ (xHFunctionField M H))) (γ : SL(2, ℤ))
    (hkey : ∀ y : (laurentBaseChange ℂ (xHFunctionField M H)), Key σ γ y) (τ : ℍ) :
    AlgebraicCurve.SemilinearAut.ofAlgAut σ • D.pt τ = D.pt (γ⁻¹ • τ) := by
  suffices h : D.pt τ = (AlgebraicCurve.SemilinearAut.ofAlgAut σ)⁻¹ • D.pt (γ⁻¹ • τ) by
    rw [h, smul_inv_smul]
  apply AlgebraicCurve.Place.ext
  ext y
  rw [mem_smul_place_iff, inv_inv, D.mem_pt_iff, D.mem_pt_iff]
  have hσy : ((AlgebraicCurve.SemilinearAut.ofAlgAut σ • y :
      (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) =
      ((σ y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) := rfl
  rw [hσy]
  have hk := hkey y (γ⁻¹ • τ)
  have hk' : (fun z : ℂ => ‖realizeOf (CohCarrier.GammaH M H)
      ((y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) (γ • ofComplex z)‖) =ᶠ[𝓝[≠] (((γ⁻¹ • τ : ℍ)) : ℂ)]
      fun z : ℂ => ‖realizeOf (CohCarrier.GammaH M H)
        ((σ y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) (ofComplex z)‖ := by
    filter_upwards [hk] with z hz
    rw [hz]
  calc IsBoundedUnder (· ≤ ·) (𝓝[≠] τ)
        (fun w : ℍ => ‖realizeOf (CohCarrier.GammaH M H)
          ((y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) w‖)
      ↔ IsBoundedUnder (· ≤ ·) (𝓝[≠] (γ • (γ⁻¹ • τ)))
          (fun w : ℍ => ‖realizeOf (CohCarrier.GammaH M H)
            ((y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) w‖) := by
        rw [smul_inv_smul]
    _ ↔ IsBoundedUnder (· ≤ ·) (𝓝[≠] (γ⁻¹ • τ))
          (fun w : ℍ => ‖realizeOf (CohCarrier.GammaH M H)
            ((y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) (γ • w)‖) :=
        (isBoundedUnder_comp_smul_iff ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) _ _).symm
    _ ↔ IsBoundedUnder (· ≤ ·) (𝓝[≠] (((γ⁻¹ • τ : ℍ)) : ℂ))
          (fun z : ℂ => ‖realizeOf (CohCarrier.GammaH M H)
            ((y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) (γ • ofComplex z)‖) :=
        (isBoundedUnder_nhdsNE_coe_iff
          (u := fun w : ℍ => ‖realizeOf (CohCarrier.GammaH M H)
            ((y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) (γ • w)‖)).symm
    _ ↔ IsBoundedUnder (· ≤ ·) (𝓝[≠] (((γ⁻¹ • τ : ℍ)) : ℂ))
          (fun z : ℂ => ‖realizeOf (CohCarrier.GammaH M H)
            ((σ y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) (ofComplex z)‖) :=
        isBoundedUnder_congr_of_eventuallyEq hk'
    _ ↔ IsBoundedUnder (· ≤ ·) (𝓝[≠] (γ⁻¹ • τ))
          (fun w : ℍ => ‖realizeOf (CohCarrier.GammaH M H)
            ((σ y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) w‖) :=
        isBoundedUnder_nhdsNE_coe_iff (u := fun w : ℍ => ‖realizeOf (CohCarrier.GammaH M H)
          ((σ y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) w‖)

end DiamondPlace

namespace ConjPlaceTransport

/-! ## The conjugation action: `q`-parameters and integral q-expansions -/

theorem qParam_J_smul (τ : ℍ) :
    Function.Periodic.qParam 1 ((J • τ : ℍ) : ℂ) = conj (Function.Periodic.qParam 1 (τ : ℂ)) := by
  rw [UpperHalfPlane.coe_J_smul, Function.Periodic.qParam, Function.Periodic.qParam,
    ← Complex.exp_conj]
  congr 1
  simp only [Complex.ofReal_one, div_one, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  ring

variable {Γ : Subgroup SL(2, ℤ)} [hT : Fact (ModularGroup.T ∈ Γ)]

local instance instFactIsCusp : Fact (IsCusp OnePoint.infty (Γ : Subgroup (GL (Fin 2) ℝ))) :=
  ⟨(Γ : Subgroup (GL (Fin 2) ℝ)).isCusp_of_mem_strictPeriods one_pos
    (one_mem_strictPeriods hT.out)⟩

theorem conj_apply_J_smul_of_isIntegralQExp {k : ℤ} (f : ModularForm Γ k)
    {p : PowerSeries ℤ} (hf : IsIntegralQExp f p) (τ : ℍ) : conj (f (J • τ)) = f τ := by
  have h1 : (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := one_mem_strictPeriods hT.out
  have hper : Function.Periodic ((⇑f : ℍ → ℂ) ∘ ofComplex) (1 : ℝ) :=
    SlashInvariantFormClass.periodic_comp_ofComplex f h1
  have hsum := fun σ : ℍ =>
    UpperHalfPlane.hasSum_qExpansion one_pos hper (ModularFormClass.holo f)
      (ModularFormClass.bdd_at_infty f) σ
  have hcoeff : ∀ m : ℕ, conj ((qExpansion 1 (⇑f : ℍ → ℂ)).coeff m) =
      (qExpansion 1 (⇑f : ℍ → ℂ)).coeff m := by
    intro m
    rw [← hf.coeff m, map_intCast]
  have hJ := (hsum (J • τ)).star
  simp only [smul_eq_mul, star_mul', star_pow] at hJ
  have hJ' : HasSum (fun m : ℕ => (qExpansion 1 (⇑f : ℍ → ℂ)).coeff m *
      Function.Periodic.qParam 1 (τ : ℂ) ^ m) (conj (f (J • τ))) := by
    convert hJ using 2 with m
    all_goals try exact starRingEnd_apply _
    rw [show (star ((qExpansion 1 (⇑f : ℍ → ℂ)).coeff m) : ℂ) =
        conj ((qExpansion 1 (⇑f : ℍ → ℂ)).coeff m) from rfl, hcoeff m,
      show (star (Function.Periodic.qParam 1 ((J • τ : ℍ) : ℂ)) : ℂ) =
        conj (Function.Periodic.qParam 1 ((J • τ : ℍ) : ℂ)) from rfl, qParam_J_smul,
      Complex.conj_conj]
  have hτ := hsum τ
  simp only [smul_eq_mul] at hτ
  exact hJ'.unique hτ

/-! ## The `Key` of conjugation, propagated from the generators -/

variable (Γ : Subgroup SL(2, ℤ)) [hT : Fact (ModularGroup.T ∈ Γ)]

abbrev kappa : AlgebraicCurve.SemilinearAut ℂ (CF Γ) :=
  arithmeticGalois (qExpFunctionFieldC ℚ Γ) complexConjAlgEquiv

omit hT in
theorem coe_kappa_smul (y : CF Γ) :
    ((kappa Γ • y : CF Γ) : LaurentSeries ℂ) = coeffMap (starRingEnd ℂ) (y : LaurentSeries ℂ) := by
  rw [coe_arithmeticGalois_smul]
  exact coeffMap_congr (RingHom.ext fun _ => rfl) _

omit hT in
theorem kappa_smul_algebraMap (c : ℂ) :
    kappa Γ • algebraMap ℂ (CF Γ) c = algebraMap ℂ (CF Γ) (conj c) := by
  rw [AlgebraicCurve.SemilinearAut.smul_algebraMap, baseAut_arithmeticGalois]
  rfl

private def Key (y : CF Γ) : Prop :=
  ∀ τ : ℍ, (fun z : ℂ => realizeOf Γ ((kappa Γ • y : CF Γ) : LaurentSeries ℂ) (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
    fun z : ℂ => conj (realizeOf Γ ((y : CF Γ) : LaurentSeries ℂ) (J • ofComplex z))

theorem key_algebraMap (c : ℂ) : Key Γ (algebraMap ℂ (CF Γ) c) := by
  intro τ
  rw [kappa_smul_algebraMap]
  have h1 := realize_const_eventuallyEq (Γ := Γ) (conj c) τ
  have h2 := eventually_smul_of_eventually
    (p := fun w => realizeOf Γ (algebraMap ℂ (LaurentSeries ℂ) c) w = c) J τ
    (realize_const_eventuallyEq (Γ := Γ) c (J • τ))
  filter_upwards [h1, h2] with z e1 e2
  show realizeOf Γ (algebraMap ℂ (LaurentSeries ℂ) (conj c)) (ofComplex z) =
    conj (realizeOf Γ (algebraMap ℂ (LaurentSeries ℂ) c) (J • ofComplex z))
  rw [e1, e2]

theorem Key.add {x y : CF Γ} (hx : Key Γ x) (hy : Key Γ y) : Key Γ (x + y) := by
  intro τ
  rw [smul_add]
  have h1 := realize_add_eventuallyEq (pres (kappa Γ • x)) (pres (kappa Γ • y)) τ
  have h2 := eventually_smul_of_eventually
    (p := fun w => realizeOf Γ (((x : CF Γ) : LaurentSeries ℂ) + ((y : CF Γ) : LaurentSeries ℂ)) w =
      realizeOf Γ ((x : CF Γ) : LaurentSeries ℂ) w + realizeOf Γ ((y : CF Γ) : LaurentSeries ℂ) w)
    J τ (realize_add_eventuallyEq (pres x) (pres y) (J • τ))
  filter_upwards [h1, h2, hx τ, hy τ] with z e1 e2 e3 e4
  show realizeOf Γ (((kappa Γ • x : CF Γ) : LaurentSeries ℂ) + ((kappa Γ • y : CF Γ) : LaurentSeries ℂ))
      (ofComplex z) =
    conj (realizeOf Γ (((x : CF Γ) : LaurentSeries ℂ) + ((y : CF Γ) : LaurentSeries ℂ)) (J • ofComplex z))
  rw [e1, Pi.add_apply, e3, e4, e2, map_add]

theorem Key.mul {x y : CF Γ} (hx : Key Γ x) (hy : Key Γ y) : Key Γ (x * y) := by
  intro τ
  rw [smul_mul']
  have h1 := realize_mul_eventuallyEq (pres (kappa Γ • x)) (pres (kappa Γ • y)) τ
  have h2 := eventually_smul_of_eventually
    (p := fun w => realizeOf Γ (((x : CF Γ) : LaurentSeries ℂ) * ((y : CF Γ) : LaurentSeries ℂ)) w =
      realizeOf Γ ((x : CF Γ) : LaurentSeries ℂ) w * realizeOf Γ ((y : CF Γ) : LaurentSeries ℂ) w)
    J τ (realize_mul_eventuallyEq (pres x) (pres y) (J • τ))
  filter_upwards [h1, h2, hx τ, hy τ] with z e1 e2 e3 e4
  show realizeOf Γ (((kappa Γ • x : CF Γ) : LaurentSeries ℂ) * ((kappa Γ • y : CF Γ) : LaurentSeries ℂ))
      (ofComplex z) =
    conj (realizeOf Γ (((x : CF Γ) : LaurentSeries ℂ) * ((y : CF Γ) : LaurentSeries ℂ)) (J • ofComplex z))
  rw [e1, Pi.mul_apply, e3, e4, e2, map_mul]

theorem Key.neg {x : CF Γ} (hx : Key Γ x) : Key Γ (-x) := by
  intro τ
  rw [smul_neg]
  have h1 := realize_neg_eventuallyEq (pres (kappa Γ • x)) τ
  have h2 := eventually_smul_of_eventually
    (p := fun w => realizeOf Γ (-((x : CF Γ) : LaurentSeries ℂ)) w =
      -realizeOf Γ ((x : CF Γ) : LaurentSeries ℂ) w)
    J τ (realize_neg_eventuallyEq (pres x) (J • τ))
  filter_upwards [h1, h2, hx τ] with z e1 e2 e3
  show realizeOf Γ (-((kappa Γ • x : CF Γ) : LaurentSeries ℂ)) (ofComplex z) =
    conj (realizeOf Γ (-((x : CF Γ) : LaurentSeries ℂ)) (J • ofComplex z))
  rw [e1, e3, e2, map_neg]

theorem Key.inv {x : CF Γ} (hx : Key Γ x) : Key Γ x⁻¹ := by
  intro τ
  rw [smul_inv'']
  have h1 := realize_inv_eventuallyEq (pres (kappa Γ • x)) τ
  have h2 := eventually_smul_of_eventually
    (p := fun w => realizeOf Γ (((x : CF Γ) : LaurentSeries ℂ)⁻¹) w =
      (realizeOf Γ ((x : CF Γ) : LaurentSeries ℂ) w)⁻¹)
    J τ (realize_inv_eventuallyEq (pres x) (J • τ))
  filter_upwards [h1, h2, hx τ] with z e1 e2 e3
  show realizeOf Γ (((kappa Γ • x : CF Γ) : LaurentSeries ℂ)⁻¹) (ofComplex z) =
    conj (realizeOf Γ (((x : CF Γ) : LaurentSeries ℂ)⁻¹) (J • ofComplex z))
  rw [e1, e3, e2, map_inv₀]

theorem coeffMap_conj_coeffEmb (w : LaurentSeries ℚ) :
    coeffMap (starRingEnd ℂ) (coeffEmb ℂ w) = coeffEmb ℂ w := by
  ext n
  rw [coeffMap_coeff, coeffEmb_coeff]
  exact map_ratCast (starRingEnd ℂ) (w.coeff n)

theorem key_generator {k : ℤ} (f g : ModularForm Γ k) (pf pg : PowerSeries ℤ)
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    Key Γ ⟨coeffEmb ℂ (intSeriesC ℚ pf / intSeriesC ℚ pg),
      coeffEmb_mem_laurentBaseChange ℂ (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ := by
  intro τ
  have hgq : qL g ≠ 0 := by
    rw [← coeffEmb_intSeriesC_eq_qL hg]
    intro h0
    apply hg0
    exact (coeffEmb ℂ).injective (h0.trans (map_zero _).symm)
  have hgne : g ≠ 0 := by
    intro h; apply hgq; simp [qL, h, UpperHalfPlane.qExpansion_zero]
  set y : CF Γ := ⟨coeffEmb ℂ (intSeriesC ℚ pf / intSeriesC ℚ pg),
      coeffEmb_mem_laurentBaseChange ℂ (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ with hydef
  have hκy : (kappa Γ • y : CF Γ) = y := by
    apply Subtype.ext
    rw [coe_kappa_smul]
    exact coeffMap_conj_coeffEmb _
  have hy : ((y : CF Γ) : LaurentSeries ℂ) * qL g = qL f := by
    show coeffEmb ℂ (intSeriesC ℚ pf / intSeriesC ℚ pg) * qL g = qL f
    rw [map_div₀, coeffEmb_intSeriesC_eq_qL hf, coeffEmb_intSeriesC_eq_qL hg,
      div_mul_cancel₀ _ hgq]
  let Py : Pres Γ ((y : CF Γ) : LaurentSeries ℂ) := ⟨k, f, g, hgne, hy⟩
  rw [hκy]
  have h1 := realize_eventuallyEq Py τ
  have h2 := eventually_smul_of_eventually
    (p := fun w => realizeOf Γ ((y : CF Γ) : LaurentSeries ℂ) w = (f : ℍ → ℂ) w / (g : ℍ → ℂ) w) J τ
    (by
      filter_upwards [realize_eventuallyEq Py (J • τ)] with z hz
      exact hz)
  filter_upwards [h1, h2] with z e1 e2
  rw [e1, e2, map_div₀, conj_apply_J_smul_of_isIntegralQExp f hf,
    conj_apply_J_smul_of_isIntegralQExp g hg]

theorem key_all (y : CF Γ) : Key Γ y := by
  obtain ⟨x, hx⟩ := y
  have inner : ∀ (w : LaurentSeries ℚ) (hw : w ∈ qExpFunctionFieldC ℚ Γ),
      Key Γ ⟨coeffEmb ℂ w, coeffEmb_mem_laurentBaseChange ℂ hw⟩ := by
    intro w hw
    have hw' : w ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ intFormRatiosC ℚ Γ) := hw
    induction hw' using Subfield.closure_induction with
    | mem z hz =>
        rcases hz with ⟨r, rfl⟩ | ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩
        · have : (⟨coeffEmb ℂ (algebraMap ℚ (LaurentSeries ℚ) r),
              coeffEmb_mem_laurentBaseChange ℂ hw⟩ : CF Γ) =
              algebraMap ℂ (CF Γ) (r : ℂ) := by
            apply Subtype.ext
            show coeffEmb ℂ (algebraMap ℚ (LaurentSeries ℚ) r) = algebraMap ℂ (LaurentSeries ℂ) (r : ℂ)
            rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffEmb,
              coeffMap_single]
            simp
          rw [this]
          exact key_algebraMap Γ (r : ℂ)
        · exact key_generator Γ f g pf pg hf hg hg0
    | one =>
        have : (⟨coeffEmb ℂ 1, coeffEmb_mem_laurentBaseChange ℂ hw⟩ : CF Γ) =
            algebraMap ℂ (CF Γ) 1 :=
          Subtype.ext (by simp)
        rw [this]; exact key_algebraMap Γ 1
    | add a b ha hb iha ihb =>
        have hmem_a : a ∈ qExpFunctionFieldC ℚ Γ := ha
        have hmem_b : b ∈ qExpFunctionFieldC ℚ Γ := hb
        have : (⟨coeffEmb ℂ (a + b), coeffEmb_mem_laurentBaseChange ℂ hw⟩ : CF Γ) =
            (⟨coeffEmb ℂ a, coeffEmb_mem_laurentBaseChange ℂ hmem_a⟩ : CF Γ) +
              ⟨coeffEmb ℂ b, coeffEmb_mem_laurentBaseChange ℂ hmem_b⟩ := by
          apply Subtype.ext; show coeffEmb ℂ (a + b) = coeffEmb ℂ a + coeffEmb ℂ b; rw [map_add]
        rw [this]; exact (iha hmem_a).add Γ (ihb hmem_b)
    | neg a ha iha =>
        have hmem_a : a ∈ qExpFunctionFieldC ℚ Γ := ha
        have : (⟨coeffEmb ℂ (-a), coeffEmb_mem_laurentBaseChange ℂ hw⟩ : CF Γ) =
            -(⟨coeffEmb ℂ a, coeffEmb_mem_laurentBaseChange ℂ hmem_a⟩ : CF Γ) := by
          apply Subtype.ext; show coeffEmb ℂ (-a) = -coeffEmb ℂ a; rw [map_neg]
        rw [this]; exact (iha hmem_a).neg Γ
    | inv a ha iha =>
        have hmem_a : a ∈ qExpFunctionFieldC ℚ Γ := ha
        have : (⟨coeffEmb ℂ a⁻¹, coeffEmb_mem_laurentBaseChange ℂ hw⟩ : CF Γ) =
            (⟨coeffEmb ℂ a, coeffEmb_mem_laurentBaseChange ℂ hmem_a⟩ : CF Γ)⁻¹ := by
          apply Subtype.ext; show coeffEmb ℂ a⁻¹ = (coeffEmb ℂ a)⁻¹; rw [map_inv₀]
        rw [this]; exact (iha hmem_a).inv Γ
    | mul a b ha hb iha ihb =>
        have hmem_a : a ∈ qExpFunctionFieldC ℚ Γ := ha
        have hmem_b : b ∈ qExpFunctionFieldC ℚ Γ := hb
        have : (⟨coeffEmb ℂ (a * b), coeffEmb_mem_laurentBaseChange ℂ hw⟩ : CF Γ) =
            (⟨coeffEmb ℂ a, coeffEmb_mem_laurentBaseChange ℂ hmem_a⟩ : CF Γ) *
              ⟨coeffEmb ℂ b, coeffEmb_mem_laurentBaseChange ℂ hmem_b⟩ := by
          apply Subtype.ext; show coeffEmb ℂ (a * b) = coeffEmb ℂ a * coeffEmb ℂ b; rw [map_mul]
        rw [this]; exact (iha hmem_a).mul Γ (ihb hmem_b)
  have hx' : x ∈ Subfield.closure (Set.range (algebraMap ℂ (LaurentSeries ℂ)) ∪
      (coeffEmb ℂ) '' (qExpFunctionFieldC ℚ Γ : Set (LaurentSeries ℚ))) :=
    (mem_laurentBaseChange_iff).mp hx
  induction hx' using Subfield.closure_induction with
  | mem z hz =>
      rcases hz with ⟨c, rfl⟩ | ⟨w, hw, rfl⟩
      · have : (⟨algebraMap ℂ (LaurentSeries ℂ) c, hx⟩ : CF Γ) = algebraMap ℂ (CF Γ) c :=
          Subtype.ext rfl
        rw [this]; exact key_algebraMap Γ c
      · exact inner w hw
  | one =>
      have : (⟨1, hx⟩ : CF Γ) = algebraMap ℂ (CF Γ) 1 := Subtype.ext (by simp)
      rw [this]; exact key_algebraMap Γ 1
  | add a b ha hb iha ihb =>
      have hma : a ∈ laurentBaseChange ℂ (qExpFunctionFieldC ℚ Γ) := (mem_laurentBaseChange_iff).mpr ha
      have hmb : b ∈ laurentBaseChange ℂ (qExpFunctionFieldC ℚ Γ) := (mem_laurentBaseChange_iff).mpr hb
      have : (⟨a + b, hx⟩ : CF Γ) = (⟨a, hma⟩ : CF Γ) + ⟨b, hmb⟩ := Subtype.ext rfl
      rw [this]; exact (iha hma).add Γ (ihb hmb)
  | neg a ha iha =>
      have hma : a ∈ laurentBaseChange ℂ (qExpFunctionFieldC ℚ Γ) := (mem_laurentBaseChange_iff).mpr ha
      have : (⟨-a, hx⟩ : CF Γ) = -(⟨a, hma⟩ : CF Γ) := Subtype.ext rfl
      rw [this]; exact (iha hma).neg Γ
  | inv a ha iha =>
      have hma : a ∈ laurentBaseChange ℂ (qExpFunctionFieldC ℚ Γ) := (mem_laurentBaseChange_iff).mpr ha
      have : (⟨a⁻¹, hx⟩ : CF Γ) = (⟨a, hma⟩ : CF Γ)⁻¹ := Subtype.ext rfl
      rw [this]; exact (iha hma).inv Γ
  | mul a b ha hb iha ihb =>
      have hma : a ∈ laurentBaseChange ℂ (qExpFunctionFieldC ℚ Γ) := (mem_laurentBaseChange_iff).mpr ha
      have hmb : b ∈ laurentBaseChange ℂ (qExpFunctionFieldC ℚ Γ) := (mem_laurentBaseChange_iff).mpr hb
      have : (⟨a * b, hx⟩ : CF Γ) = (⟨a, hma⟩ : CF Γ) * ⟨b, hmb⟩ := Subtype.ext rfl
      rw [this]; exact (iha hma).mul Γ (ihb hmb)

/-! ## The place-level conjugation law -/

theorem J_smul_J_smul (τ : ℍ) : UpperHalfPlane.J • UpperHalfPlane.J • τ = τ := by
  rw [← mul_smul, ← sq, UpperHalfPlane.J_sq, one_smul]

omit hT in
theorem kappa_mul_kappa : kappa Γ * kappa Γ = 1 := by
  rw [kappa, ← map_mul, complexConjAlgEquiv_mul_self, map_one]

omit hT in
theorem kappa_inv : (kappa Γ)⁻¹ = kappa Γ :=
  inv_eq_of_mul_eq_one_right (kappa_mul_kappa Γ)

omit hT in
theorem smul_pt_eq (D : ComplexPlaceDictionaryOf Γ (qExpFunctionFieldC ℚ Γ))
    (hkey : ∀ y : CF Γ, Key Γ y) (τ : ℍ) : kappa Γ • D.pt τ = D.pt (J • τ) := by
  suffices h : D.pt (J • τ) = kappa Γ • D.pt τ from h.symm
  apply AlgebraicCurve.Place.ext
  ext y
  rw [mem_smul_place_iff, kappa_inv, D.mem_pt_iff, D.mem_pt_iff]
  have hk := hkey y τ
  have hk' : (fun z : ℂ => ‖realizeOf Γ ((kappa Γ • y : CF Γ) : LaurentSeries ℂ) (ofComplex z)‖)
      =ᶠ[𝓝[≠] ((τ : ℍ) : ℂ)]
      fun z : ℂ => ‖realizeOf Γ ((y : CF Γ) : LaurentSeries ℂ) (J • ofComplex z)‖ := by
    filter_upwards [hk] with z hz
    rw [hz, Complex.norm_conj]
  calc IsBoundedUnder (· ≤ ·) (𝓝[≠] (J • τ))
        (fun w : ℍ => ‖realizeOf Γ ((y : CF Γ) : LaurentSeries ℂ) w‖)
      ↔ IsBoundedUnder (· ≤ ·) (𝓝[≠] τ)
          (fun w : ℍ => ‖realizeOf Γ ((y : CF Γ) : LaurentSeries ℂ) (J • w)‖) :=
        (isBoundedUnder_comp_smul_iff J _ _).symm
    _ ↔ IsBoundedUnder (· ≤ ·) (𝓝[≠] ((τ : ℍ) : ℂ))
          (fun z : ℂ => ‖realizeOf Γ ((y : CF Γ) : LaurentSeries ℂ) (J • ofComplex z)‖) :=
        (isBoundedUnder_nhdsNE_coe_iff
          (u := fun w : ℍ => ‖realizeOf Γ ((y : CF Γ) : LaurentSeries ℂ) (J • w)‖)).symm
    _ ↔ IsBoundedUnder (· ≤ ·) (𝓝[≠] ((τ : ℍ) : ℂ))
          (fun z : ℂ => ‖realizeOf Γ ((kappa Γ • y : CF Γ) : LaurentSeries ℂ) (ofComplex z)‖) :=
        (isBoundedUnder_congr_of_eventuallyEq hk').symm
    _ ↔ IsBoundedUnder (· ≤ ·) (𝓝[≠] τ)
          (fun w : ℍ => ‖realizeOf Γ ((kappa Γ • y : CF Γ) : LaurentSeries ℂ) w‖) :=
        isBoundedUnder_nhdsNE_coe_iff
          (u := fun w : ℍ => ‖realizeOf Γ ((kappa Γ • y : CF Γ) : LaurentSeries ℂ) w‖)

end ConjPlaceTransport


end PlaceDictionaryAction

open PlaceDictionaryAction

/-! ## Existence of the dictionary -/

private def dictionaryOf (Γ : Subgroup SL(2, ℤ)) [hT : Fact (ModularGroup.T ∈ Γ)] :
    ComplexPlaceDictionaryOf Γ (qExpFunctionFieldC ℚ Γ) where
  pt := fun τ => (exists_place (Γ := Γ) τ).choose
  ramification := fun τ => (exists_place (Γ := Γ) τ).choose_spec.choose
  ramification_pos := fun τ => (exists_place (Γ := Γ) τ).choose_spec.choose_spec.1
  pt_smul := by
    intro γ τ
    apply AlgebraicCurve.Place.ext
    ext x
    rw [((exists_place (Γ := Γ) ((γ : SL(2, ℤ)) • τ)).choose_spec.choose_spec.2.1 x),
      ((exists_place (Γ := Γ) τ).choose_spec.choose_spec.2.1 x), mu_smul]
  mem_pt_iff := by
    intro τ x
    rw [((exists_place (Γ := Γ) τ).choose_spec.choose_spec.2.1 x), mu_nonneg_iff]
  meromorphicOrderAt_realizeOf := fun τ x hx =>
    (exists_place (Γ := Γ) τ).choose_spec.choose_spec.2.2 x hx

theorem exists_complexPlaceDictionaryOf
    (Γ : Subgroup SL(2, ℤ)) (hT : ModularGroup.T ∈ Γ)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (hF : F₀ = ModularCurve.qExpFunctionFieldC ℚ Γ) :
    Nonempty (ModularCurve.ComplexPlaceDictionaryOf Γ F₀) := by
  subst hF
  exact ⟨dictionaryOf (Γ := Γ) (hT := ⟨hT⟩)⟩

namespace ComplexPlaceDictionaryOf

/-! ## The `Γ₀(M)` pull-back of the dictionary -/

theorem ofAlgAut_smul_pt_eq_pt_inv_smul (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (D : ModularCurve.ComplexPlaceDictionaryOf (CohCarrier.GammaH M H)
      (ModularCurve.xHFunctionField M H))
    (σ : ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)) ≃ₐ[ℂ]
      ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M)
    (hσ : ∀ (k : ℤ) (f g : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
        (pf pg : PowerSeries ℤ) (hf : ModularCurve.IsIntegralQExp f pf)
        (hg : ModularCurve.IsIntegralQExp g pg) (hg0 : ModularCurve.intSeriesC ℚ pg ≠ 0),
        ((σ ⟨ModularCurve.coeffEmb ℂ
              (ModularCurve.intSeriesC ℚ pf / ModularCurve.intSeriesC ℚ pg),
              ModularCurve.coeffEmb_mem_laurentBaseChange ℂ
                (ModularCurve.div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ :
            ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H))) : LaurentSeries ℂ) *
            HahnSeries.ofPowerSeries ℤ ℂ
              (UpperHalfPlane.qExpansion 1 (⇑g ∣[k] (γ : GL (Fin 2) ℝ))) =
          HahnSeries.ofPowerSeries ℤ ℂ
            (UpperHalfPlane.qExpansion 1 (⇑f ∣[k] (γ : GL (Fin 2) ℝ))))
    (τ : UpperHalfPlane) :
    AlgebraicCurve.SemilinearAut.ofAlgAut σ • D.pt τ = D.pt (γ⁻¹ • τ) :=
  smul_pt_eq D σ γ (fun y => key_all σ γ hγ hσ y) τ

/-! ## Conjugation of the dictionary -/

theorem arithmeticGalois_complexConjAlgEquiv_smul_pt
    (Γ : Subgroup SL(2, ℤ)) (hT : ModularGroup.T ∈ Γ)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (hF : F₀ = ModularCurve.qExpFunctionFieldC ℚ Γ)
    (D : ModularCurve.ComplexPlaceDictionaryOf Γ F₀) (τ : UpperHalfPlane) :
    ModularCurve.arithmeticGalois F₀ complexConjAlgEquiv • D.pt τ =
      D.pt (UpperHalfPlane.J • τ) := by
  subst hF
  exact ConjPlaceTransport.smul_pt_eq (Γ := Γ) D
    (ConjPlaceTransport.key_all (Γ := Γ) (hT := ⟨hT⟩)) τ

end ComplexPlaceDictionaryOf

end ModularCurve
