/-
The `diagOne` Whittaker coefficient at `1`: vanishing beyond the level, and the principal-idèle expansion.

Two rows of the cusp-form Fourier expansion at the `diagOne` torus, `α = 1`:

* `exists_whittakerCoefficient_one_diagOne_eq_zero_of_exp_lt_valuation` (211): for a left-invariant,
  `Kf`-smooth `φ` there is a level vector `c` with finite support such that the coefficient at `1`,
  `diagOne b`, vanishes as soon as some place's value of `b` exceeds `exp (c v)` — the coefficient is
  supported in a level box;
* `hasSum_whittakerCoefficient_one_diagOne_principalIdeles_mul` (130): for a cuspidal `φ` whose `α = 0`
  coefficient vanishes, the coefficients at `1` along the **principal idèles** sum to `φ g`, the
  HasSum form of the Fourier expansion a cusp form satisfies.

Assumes: `WhittakerCoefficient` (`whittakerCoefficient_unipotentGL2_mul`,
`whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul`), `WhittakerSum`
(`hasSum_whittakerCoefficient`), SET-AF112's `WhittakerSmoothSummability`
(`whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff_mixedSpace`),
`WhittakerSystem` (`continuous_unipotentGL2`), and the `BorelUnfolding`/`ShellSurgery` dictionary.

Transcribed from the two pins below (pinned `aa2d8b3`, 211 + 130 `S_` lines).

## The rows

* `AutomorphicForm.exists_whittakerCoefficient_one_diagOne_eq_zero_of_exp_lt_valuation` — 211 pin `S_` lines.
* `AutomorphicForm.hasSum_whittakerCoefficient_one_diagOne_principalIdeles_mul` — 130 pin `S_` lines.

The two rows' helper blocks are transcribed too — nine declarations for the first row and four for the
second, all public and flat:

* `mul_finSingle`, `finSingle_mem_idealBall`, `finprod_finSingle`, `le_exp_of_lt_exp_add_one` — the pin's
  `Ws1.K5a` block beyond the three `finSingle` dictionary rows the port already has public in
  `NumberField.TateGlobal` (`finSingle`, `finSingle_apply_self`, `finSingle_apply_of_ne`) and the
  `diagOne`/unipotent identity it also already has public
  (`AutomorphicForm.RankinSelberg.ShellSurgery.diagOne_mul_unipotentGL2`);
* `globalPoints_diagOne`, `principalIdeles_equiv` — the pin's `Ws1.K4` block beyond
  `globalPoints_unipotentGL2`, public in `AutomorphicForm.BorelUnfolding`.

## Port deltas

* **`finSingle` is the port's `NumberField.TateGlobal.finSingle`** (the pin's `Ws1.K5a.finSingle`),
  applied at the pin's unqualified spelling under a scoped `open NumberField.TateGlobal`. No statement
  adaptation.
* `diagOne_mul_unipotentGL2` and `globalPoints_unipotentGL2` are the port's public copies
  (`RankinSelbergShellIndicator.lean`, `BorelFundamentalDomain.lean`), applied at the pin's arguments;
  the pin's `{A} [CommRing A]` version is the port's `AdeleRing`-specialised one, so the application
  site is unchanged.
* `principalIdeles_equiv` closes an injectivity goal with the port's `AdeleRing.algebraMap_injective`,
  the pin's `NumberField.AdeleRing.algebraMap_injective` (same name, same statement).
* `M4aHerbrand.principalIdeles` is the port's `IdeleClassVocab` carrier
  (`NumberTheory/NumberField/IdeleClass/Vocab.lean`), the range of the diagonal embedding, exactly as
  the pin's.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AutomorphicForm_exists_whittakerCoefficient_one_diagOne_eq_zero_of_exp_lt_valuation.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AutomorphicForm_hasSum_whittakerCoefficient_one_diagOne_principalIdeles_mul.lean>

spec-pin: Theorems/Thm_AutomorphicForm_exists_whittakerCoefficient_one_diagOne_eq_zero_of_exp_lt_valuation.lean
spec-pin: P2M/Sol/S_AutomorphicForm_exists_whittakerCoefficient_one_diagOne_eq_zero_of_exp_lt_valuation.lean
spec-pin: Theorems/Thm_AutomorphicForm_hasSum_whittakerCoefficient_one_diagOne_principalIdeles_mul.lean
spec-pin: P2M/Sol/S_AutomorphicForm_hasSum_whittakerCoefficient_one_diagOne_principalIdeles_mul.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.Basic
import FLTForHuman.AutomorphicForm.Adelic.InducedSection
import FLTForHuman.AutomorphicForm.Adelic.EtaFamily
import FLTForHuman.AutomorphicForm.Adelic.ArchKFinite
import FLTForHuman.AutomorphicForm.Adelic.SmoothAutomorphicFn
import FLTForHuman.AutomorphicForm.Adelic.ProductionPins
import FLTForHuman.AutomorphicForm.Adelic.WhittakerCoefficient
import FLTForHuman.AutomorphicForm.Adelic.AddCharLocalComponents
import FLTForHuman.AutomorphicForm.Adelic.ConstantTerm
import FLTForHuman.AutomorphicForm.Adelic.WeylIntertwining
import FLTForHuman.NumberTheory.AdelicBox
import FLTForHuman.NumberTheory.AdelicModulus
import FLTForHuman.NumberTheory.AdelicLevel.Level
import FLTForHuman.NumberTheory.NumberField.MixedEmbedding
import FLTForHuman.NumberTheory.NumberField.TateGlobal.Defs
import FLTForHuman.EisensteinGeneral.PieceFactorizationDatum
import FLTForHuman.EisensteinGeneral.PiecePartialEulerProduct
import FLTForHuman.AutomorphicForm.Adelic.WhittakerSum
import FLTForHuman.AutomorphicForm.Adelic.WhittakerSmoothSummability
import FLTForHuman.AutomorphicForm.Adelic.WhittakerSystem
import FLTForHuman.AutomorphicForm.Adelic.RankinSelbergShellIndicator
import FLTForHuman.AutomorphicForm.Adelic.BorelFundamentalDomain
import FLTForHuman.NumberTheory.NumberField.TateGlobal.FiniteSlab

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicBox NumberField.AdelicLevel
open MeasureTheory AutomorphicForm
open scoped Classical NNReal nonZeroDivisors

namespace AutomorphicForm

/-! ### The single-place embedding at the level box

The pin's `Ws1.K5a` block. `finSingle`, `finSingle_apply_self` and `finSingle_apply_of_ne` are the
port's public `NumberField.TateGlobal` copies; the multiplication and membership rows are stated here
at the pin's unqualified spelling. -/

section LevelBoxDictionary

variable {F : Type} [Field F] [NumberField F]

open NumberField.TateGlobal in
theorem mul_finSingle (v : HeightOneSpectrum (𝓞 F)) (x : FiniteAdeleRing (𝓞 F) F)
    (y : v.adicCompletion F) :
    x * finSingle v y = finSingle v (x v * y) := by
  apply RestrictedProduct.ext
  intro w
  by_cases hw : w = v
  · subst hw
    change x w * finSingle w y w = finSingle w (x w * y) w
    rw [finSingle_apply_self, finSingle_apply_self]
  · change x w * finSingle v y w = finSingle v (x v * y) w
    rw [finSingle_apply_of_ne v y hw, finSingle_apply_of_ne v _ hw, mul_zero]

open NumberField.TateGlobal in
theorem finSingle_mem_idealBall (v : HeightOneSpectrum (𝓞 F)) {y : v.adicCompletion F}
    {N : Ideal (𝓞 F)} (hy : Valued.v y ≤ idealBound (𝓞 F) N v) :
    finSingle v y ∈ idealBall (𝓞 F) F N := by
  intro w
  by_cases hw : w = v
  · subst hw
    rwa [finSingle_apply_self]
  · rw [finSingle_apply_of_ne v y hw, map_zero]
    exact zero_le

open NumberField.TateGlobal in
theorem finprod_finSingle (v : HeightOneSpectrum (𝓞 F))
    (ψv : (w : HeightOneSpectrum (𝓞 F)) → AddChar (w.adicCompletion F) ℂ) (y : v.adicCompletion F) :
    (∏ᶠ w : HeightOneSpectrum (𝓞 F), ψv w (finSingle v y w)) = ψv v y := by
  rw [finprod_eq_single (fun w => ψv w (finSingle v y w)) v]
  · rw [finSingle_apply_self]
  · intro w hw
    rw [finSingle_apply_of_ne v y hw, AddChar.map_zero_eq_one]

/-- A strict inequality against `exp (k + 1)` gives the non-strict one against `exp k`: the value
group `WithZero (Multiplicative ℤ)` is discrete. -/
theorem le_exp_of_lt_exp_add_one {x : WithZero (Multiplicative ℤ)} {k : ℤ}
    (h : x < WithZero.exp (k + 1)) : x ≤ WithZero.exp k := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_le
  · rw [← WithZero.exp_log hx] at h ⊢
    rw [WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

end LevelBoxDictionary

/-! ### The `globalPoints`/`diagOne` dictionary and the principal idèles

The pin's `Ws1.K4` block beyond `globalPoints_unipotentGL2`: the diagonal of a rational unit is the
diagonal of its image in the idèles, and the principal idèles are indexed by `Fˣ`. -/

section GlobalPointsDictionary

theorem globalPoints_diagOne (F : Type) [Field F] [NumberField F] (u : Fˣ) :
    globalPoints (𝓞 F) F (diagOne u) =
      diagOne (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) u) := by
  apply Units.ext
  ext i j
  simp only [globalPoints, Matrix.GeneralLinearGroup.map, diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp [RingHom.mapMatrix_apply, diagOne_coe_apply, Matrix.diagonal]

theorem principalIdeles_equiv (F : Type) [Field F] [NumberField F] :
    ∃ e : {α : F // α ≠ 0} ≃ ↥(M4aHerbrand.principalIdeles (𝓞 F) F),
      ∀ a : {α : F // α ≠ 0},
        ((e a : ↥(M4aHerbrand.principalIdeles (𝓞 F) F)) : (AdeleRing (𝓞 F) F)ˣ) =
        Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)
          (Units.mk0 a.1 a.2) := by
  classical
  let fwd : {α : F // α ≠ 0} → ↥(M4aHerbrand.principalIdeles (𝓞 F) F) := fun a =>
    ⟨Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)
        (Units.mk0 a.1 a.2), ⟨Units.mk0 a.1 a.2, rfl⟩⟩
  have hinj : Function.Injective fwd := by
    intro a b hab
    have h1 : ((fwd a : ↥(M4aHerbrand.principalIdeles (𝓞 F) F)) : (AdeleRing (𝓞 F) F)ˣ) = fwd b :=
      congrArg Subtype.val hab
    have h2 := congrArg (fun x : (AdeleRing (𝓞 F) F)ˣ => (x : AdeleRing (𝓞 F) F)) h1
    simp only [fwd, Units.coe_map, MonoidHom.coe_coe, Units.val_mk0] at h2
    exact Subtype.ext (AdeleRing.algebraMap_injective (𝓞 F) F h2)
  have hsurj : Function.Surjective fwd := by
    rintro ⟨_, u, rfl⟩
    refine ⟨⟨(u : F), u.ne_zero⟩, Subtype.ext ?_⟩
    simp only [fwd, Units.mk0_val]
  exact ⟨Equiv.ofBijective fwd ⟨hinj, hsurj⟩, fun a => rfl⟩

end GlobalPointsDictionary

theorem exists_whittakerCoefficient_one_diagOne_eq_zero_of_exp_lt_valuation
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hleft : ∀ (β : F) (g : AdelicGL2 (𝓞 F) F),
      φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g) = φ g)
    (hsm : IsKfSmooth F φ) :
    ∃ c : HeightOneSpectrum (𝓞 F) → ℤ,
      (∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, c v = 0) ∧
      ∀ b : (AdeleRing (𝓞 F) F)ˣ,
        (∃ v : HeightOneSpectrum (𝓞 F),
          WithZero.exp (c v) < Valued.v (((b : AdeleRing (𝓞 F) F).2) v)) →
        whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 1 (diagOne b) = 0 := by
  classical
  obtain ⟨𝔫, h𝔫, hinv⟩ := IsKfSmooth.exists_ideal_forall_apply_mul_conj_unipotentGL2_eq hsm
  obtain ⟨ψv, nψ, θr, θc, hlev, hnontriv, hfin, hprod, -, -, -⟩ :=
    exists_localComponents_of_isGlobalAddChar F ψ hψ
  refine ⟨fun v => nψ v - WithZero.log (idealBound (𝓞 F) 𝔫 v), ?_, ?_⟩
  · refine ⟨(hfin.union (finite_setOf_idealBound_ne_one (R := 𝓞 F) h𝔫)).toFinset, fun v hv => ?_⟩
    rw [Set.Finite.mem_toFinset, Set.mem_union, not_or] at hv
    have h1 : nψ v = 0 := by simpa [Function.mem_support] using hv.1
    have h2 : idealBound (𝓞 F) 𝔫 v = 1 := by simpa using hv.2
    show nψ v - WithZero.log (idealBound (𝓞 F) 𝔫 v) = 0
    rw [h1, h2, WithZero.log_one, sub_zero]
  · rintro b ⟨v, hv⟩
    by_contra hW
    have hper : ∀ (g : AdelicGL2 (𝓞 F) F) (β : F) (u : AdeleRing (𝓞 F) F),
        φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β + u) * g) = φ (unipotentGL2 u * g) := by
      intro g β u
      rw [unipotentGL2_add, mul_assoc, hleft]
    have key : ∀ y : v.adicCompletion F, Valued.v y ≤ idealBound (𝓞 F) 𝔫 v →
        ψv v (((b : AdeleRing (𝓞 F) F).2 v) * y) = 1 := by
      intro y hy
      set t : AdeleRing (𝓞 F) F := ((0 : InfiniteAdeleRing F),
        NumberField.TateGlobal.finSingle (F := F) v y) with htdef
      have ht0 : adeleArch (𝓞 F) F t = 0 := rfl
      have htf : adeleFin (𝓞 F) F t ∈ idealBall (𝓞 F) F 𝔫 :=
        finSingle_mem_idealBall v hy
      have h1 : whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 1
            (diagOne b * unipotentGL2 t)
          = whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 1 (diagOne b) := by
        unfold whittakerCoefficient
        congr 1
        funext x
        congr 1
        have h := hinv (unipotentGL2 x * diagOne b) 1 (by rw [map_one]; exact one_mem _) t ht0 htf
        rw [inv_one, one_mul, mul_one] at h
        rw [← mul_assoc]
        exact h
      have h2 : whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 1
            (diagOne b * unipotentGL2 t)
          = ψ ((b : AdeleRing (𝓞 F) F) * t) *
            whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 1 (diagOne b) := by
        rw [RankinSelberg.ShellSurgery.diagOne_mul_unipotentGL2]
        have h := whittakerCoefficient_unipotentGL2_mul F D U gen ψ hψ.principalInvariant φ (diagOne b)
          (fun β u => hper (diagOne b) β u) 1 ((b : AdeleRing (𝓞 F) F) * t)
        rwa [map_one, one_mul] at h
      have h3 : ψ ((b : AdeleRing (𝓞 F) F) * t) = 1 := by
        rw [h1] at h2
        exact (mul_eq_right₀ hW).mp h2.symm
      have hbt : (b : AdeleRing (𝓞 F) F) * t =
          AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
            (NumberField.TateGlobal.finSingle (F := F) v
              (((b : AdeleRing (𝓞 F) F).2 v) * y)) := by
        rw [htdef, ← mul_finSingle]
        refine Prod.ext ?_ ?_
        · show (b : AdeleRing (𝓞 F) F).1 * 0 = 0
          exact mul_zero _
        · rfl
      rw [hbt, hprod, finprod_finSingle] at h3
      exact h3
    obtain ⟨x, hxle, hxne⟩ := hnontriv v
    have hb0 : ((b : AdeleRing (𝓞 F) F).2 v) ≠ 0 := by
      intro h0
      have h := congrArg (fun z : AdeleRing (𝓞 F) F => z.2 v) b.mul_inv
      change ((b : AdeleRing (𝓞 F) F).2 v) * ((((b⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2) v)
        = (1 : v.adicCompletion F) at h
      rw [h0, zero_mul] at h
      exact zero_ne_one h
    have hx0 : x ≠ 0 := by
      intro h0
      apply hxne
      rw [h0, AddChar.map_zero_eq_one]
    set y : v.adicCompletion F := ((b : AdeleRing (𝓞 F) F).2 v)⁻¹ * x with hydef
    have hy0 : y ≠ 0 := mul_ne_zero (inv_ne_zero hb0) hx0
    have hy : Valued.v y ≤ idealBound (𝓞 F) 𝔫 v := by
      have hIB := idealBound_ne_zero h𝔫 v
      rw [← WithZero.exp_log hIB]
      apply le_exp_of_lt_exp_add_one
      have hvb : Valued.v ((b : AdeleRing (𝓞 F) F).2 v) ≠ 0 := (Valuation.ne_zero_iff _).mpr hb0
      have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx0
      have hvy : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy0
      have hmul : Valued.v ((b : AdeleRing (𝓞 F) F).2 v) * Valued.v y = Valued.v x := by
        rw [← map_mul, hydef, mul_inv_cancel_left₀ hb0]
      have hlogmul : WithZero.log (Valued.v ((b : AdeleRing (𝓞 F) F).2 v)) + WithZero.log (Valued.v y)
          = WithZero.log (Valued.v x) := by
        rw [← WithZero.log_mul hvb hvy, hmul]
      have hlogx : WithZero.log (Valued.v x) ≤ nψ v + 1 := by
        rw [← WithZero.exp_log hvx, WithZero.exp_le_exp] at hxle
        exact hxle
      have hlogb : nψ v - WithZero.log (idealBound (𝓞 F) 𝔫 v)
          < WithZero.log (Valued.v ((b : AdeleRing (𝓞 F) F).2 v)) := by
        rw [← WithZero.exp_log hvb, WithZero.exp_lt_exp] at hv
        exact hv
      rw [← WithZero.exp_log hvy, WithZero.exp_lt_exp]
      omega
    have h := key y hy
    rw [hydef, mul_inv_cancel_left₀ hb0] at h
    exact hxne h

theorem hasSum_whittakerCoefficient_one_diagOne_principalIdeles_mul
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hcont : Continuous φ)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (hsm : IsKfSmooth F φ)
    (harch : ∀ g : AdelicGL2 (𝓞 F) F,
      ContDiff ℝ (Module.finrank ℚ F + 1) (fun z : mixedEmbedding.mixedSpace F =>
        φ (unipotentGL2 (R := AdeleRing (𝓞 F) F)
          ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm z, 0) * g)))
    (hcusp : ∀ g : AdelicGL2 (𝓞 F) F,
      whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 0 g = 0)
    (g : AdelicGL2 (𝓞 F) F) :
    HasSum (fun γ : ↥(M4aHerbrand.principalIdeles (𝓞 F) F) =>
        whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 1
          (diagOne (γ : (AdeleRing (𝓞 F) F)ˣ) * g))
      (φ g) := by
  classical
  have hleftN : ∀ (β : F) (g : AdelicGL2 (𝓞 F) F),
      φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g) = φ g := by
    intro β g
    rw [← BorelUnfolding.globalPoints_unipotentGL2 (F := F) β]
    exact hleft _ g
  obtain ⟨-, hsumm⟩ :=
    whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff_mixedSpace
      F D U gen ψ hψ φ hleftN hsm harch
  have hslice : Continuous (fun x : AdeleRing (𝓞 F) F => φ (unipotentGL2 x * g)) :=
    hcont.comp (continuous_unipotentGL2.mul continuous_const)
  have hF : HasSum (fun α : F =>
      whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g) (φ g) :=
    hasSum_whittakerCoefficient F D U gen ψ hψ φ g hslice (hsumm g)
  have hsupp : Function.support
      (fun α : F => whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g)
      ⊆ {α : F | α ≠ 0} := by
    intro α hα
    simp only [Function.mem_support, ne_eq] at hα
    intro h0
    exact hα (h0 ▸ hcusp g)
  have hF' := (hasSum_subtype_iff_of_support_subset hsupp).mpr hF
  obtain ⟨e, he⟩ := principalIdeles_equiv F
  refine (e.hasSum_iff).mp ?_
  have key : ∀ a : {α : F // α ≠ 0},
      whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 1
          (diagOne (((e a : ↥(M4aHerbrand.principalIdeles (𝓞 F) F)) : (AdeleRing (𝓞 F) F)ˣ)) * g)
        = whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ (a : F) g := by
    intro a
    rw [he a, ← globalPoints_diagOne F,
      whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul F D U gen ψ hψ φ
        hleft (a : F) a.2 g]
  have hfun : ((fun γ : ↥(M4aHerbrand.principalIdeles (𝓞 F) F) =>
        whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 1
          (diagOne (γ : (AdeleRing (𝓞 F) F)ˣ) * g)) ∘ ⇑e)
      = (fun α : F =>
          whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g) ∘
        Subtype.val := by
    funext a
    exact key a
  rw [hfun]
  exact hF'

end AutomorphicForm
