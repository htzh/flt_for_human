/-
  Adèlic Hecke generators at a place.

  `diagOne` and `finIncl` embed units and the finite adèles into `GL₂(𝔸_K)`;
  `localUnit` is the idèle with value `t` at `v` and `1` elsewhere, and
  `heckeGenAt`/`heckeGen` are the corresponding diagonal Hecke elements, with
  `heckeGen` built from a uniformizer. Their key property is that conjugating
  `heckeGenAt t` by `heckeGenAt t'` lands in `levelOne` — the level compatibility
  of the adèlic Hecke action.

  Transcribed verbatim from `Definitions/Def_NumberField_AdelicLevel.lean:622–809`
  (the pin's `Gen` section, pinned `aa2d8b3`), one of the four role modules the pin
  node is split into (playbook §3.1).
-/
import FLTForHuman.NumberTheory.AdelicLevel.IdealBall
import FLTForHuman.NumberTheory.AdelicLevel.Projections
import FLTForHuman.NumberTheory.AdelicLevel.Level

set_option autoImplicit false

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField RestrictedProduct
open scoped RestrictedProduct Topology
open Topology

noncomputable section

namespace NumberField.AdelicLevel

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

section Gen

def diagOne {A : Type*} [CommRing A] : Aˣ →* GL (Fin 2) A where
  toFun a :=
    { val := Matrix.diagonal ![(a : A), 1]
      inv := Matrix.diagonal ![((a⁻¹ : Aˣ) : A), 1]
      val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp
      inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp }
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by ext i j; fin_cases i <;> fin_cases j <;> simp

theorem diagOne_coe_apply {A : Type*} [CommRing A] (a : Aˣ) (i j : Fin 2) :
    (diagOne a : Matrix (Fin 2) (Fin 2) A) i j = Matrix.diagonal ![(a : A), 1] i j := rfl

def finIncl : FiniteAdeleRing R K →* AdeleRing R K where
  toFun x := ((1 : InfiniteAdeleRing K), x)
  map_one' := rfl
  map_mul' _ _ := Prod.ext (one_mul _).symm rfl

theorem finIncl_apply_fst (x : FiniteAdeleRing R K) : (finIncl R K x).1 = 1 := rfl
theorem finIncl_apply_snd (x : FiniteAdeleRing R K) : (finIncl R K x).2 = x := rfl

variable (v : HeightOneSpectrum R)

open scoped Classical in

def localUnit : (v.adicCompletion K)ˣ →* (FiniteAdeleRing R K)ˣ where
  toFun t :=
    { val := ⟨Function.update 1 v (t : v.adicCompletion K),
        Filter.eventually_cofinite.mpr ((Set.finite_singleton v).subset fun w hw => by
          by_contra hwv
          exact hw (by rw [Function.update_of_ne hwv]; exact one_mem _))⟩
      inv := ⟨Function.update 1 v ((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K),
        Filter.eventually_cofinite.mpr ((Set.finite_singleton v).subset fun w hw => by
          by_contra hwv
          exact hw (by rw [Function.update_of_ne hwv]; exact one_mem _))⟩
      val_inv := by
        refine Subtype.ext (funext fun w => ?_)
        show Function.update (1 : ∀ w : HeightOneSpectrum R, w.adicCompletion K) v
            (t : v.adicCompletion K) w *
          Function.update (1 : ∀ w : HeightOneSpectrum R, w.adicCompletion K) v
            ((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) w = 1
        by_cases hw : w = v
        · subst hw; simp
        · simp [Function.update_of_ne hw]
      inv_val := by
        refine Subtype.ext (funext fun w => ?_)
        show Function.update (1 : ∀ w : HeightOneSpectrum R, w.adicCompletion K) v
            ((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) w *
          Function.update (1 : ∀ w : HeightOneSpectrum R, w.adicCompletion K) v
            (t : v.adicCompletion K) w = 1
        by_cases hw : w = v
        · subst hw; simp
        · simp [Function.update_of_ne hw] }
  map_one' := by
    refine Units.ext (Subtype.ext (funext fun w => ?_))
    show Function.update (1 : ∀ w : HeightOneSpectrum R, w.adicCompletion K) v 1 w = 1
    by_cases hw : w = v
    · subst hw; simp
    · simp [Function.update_of_ne hw]
  map_mul' t t' := by
    refine Units.ext (Subtype.ext (funext fun w => ?_))
    show Function.update (1 : ∀ w : HeightOneSpectrum R, w.adicCompletion K) v
        ((t * t' : (v.adicCompletion K)ˣ) : v.adicCompletion K) w =
      Function.update (1 : ∀ w : HeightOneSpectrum R, w.adicCompletion K) v
          (t : v.adicCompletion K) w *
        Function.update (1 : ∀ w : HeightOneSpectrum R, w.adicCompletion K) v
          (t' : v.adicCompletion K) w
    by_cases hw : w = v
    · subst hw; simp
    · simp [Function.update_of_ne hw]

open scoped Classical in
theorem localUnit_apply_self (t : (v.adicCompletion K)ˣ) :
    ((localUnit R K v t : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v = t := by
  show Function.update (1 : ∀ w : HeightOneSpectrum R, w.adicCompletion K) v
      (t : v.adicCompletion K) v = t
  simp

open scoped Classical in
theorem localUnit_apply_of_ne (t : (v.adicCompletion K)ˣ) {w : HeightOneSpectrum R} (hw : w ≠ v) :
    ((localUnit R K v t : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) w = 1 := by
  show Function.update (1 : ∀ w : HeightOneSpectrum R, w.adicCompletion K) v
      (t : v.adicCompletion K) w = 1
  simp [Function.update_of_ne hw]

def heckeGenAt : (v.adicCompletion K)ˣ →* GL (Fin 2) (AdeleRing R K) :=
  diagOne.comp ((Units.map (finIncl R K)).comp (localUnit R K v))

variable {R K v}

theorem heckeGenAt_fst (t : (v.adicCompletion K)ˣ) (i j : Fin 2) :
    ((heckeGenAt R K v t : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) i j).1
      = (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j := by
  fin_cases i <;> fin_cases j <;> rfl

theorem heckeGenAt_snd_apply_of_ne (t : (v.adicCompletion K)ˣ) {w : HeightOneSpectrum R}
    (hw : w ≠ v) (i j : Fin 2) :
    ((heckeGenAt R K v t : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) i j).2 w
      = (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion K)) i j := by
  fin_cases i <;> fin_cases j
  · show ((localUnit R K v t : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) w = 1
    exact localUnit_apply_of_ne R K v t hw
  · rfl
  · rfl
  · rfl

theorem heckeGenAt_snd_apply_self (t : (v.adicCompletion K)ˣ) (i j : Fin 2) :
    ((heckeGenAt R K v t : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) i j).2 v
      = Matrix.diagonal ![(t : v.adicCompletion K), 1] i j := by
  fin_cases i <;> fin_cases j
  · show ((localUnit R K v t : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v = t
    exact localUnit_apply_self R K v t
  · rfl
  · rfl
  · rfl

theorem heckeGenAt_inv_mul_heckeGenAt_mem_levelOne (t t' : (v.adicCompletion K)ˣ)
    (h : Valued.v (t : v.adicCompletion K) = Valued.v (t' : v.adicCompletion K)) (N : Ideal R) :
    (heckeGenAt R K v t)⁻¹ * heckeGenAt R K v t' ∈ levelOne R K N := by
  rw [← map_inv, ← map_mul]
  set u : (v.adicCompletion K)ˣ := t⁻¹ * t' with hu
  have ht0 : Valued.v (t : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).mpr t.ne_zero
  have hu1 : Valued.v (u : v.adicCompletion K) = 1 := by
    rw [hu, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, h, ← h,
      inv_mul_cancel₀ ht0]
  have hui : Valued.v ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hu1, inv_one]

  have hint : ∀ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 →
      ((localUnit R K v s : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K)
        ∈ integralFiniteAdeles R K := by
    intro s hs w
    classical
    by_cases hw : w = v
    · subst hw
      rw [localUnit_apply_self, HeightOneSpectrum.mem_adicCompletionIntegers, hs]
    · rw [localUnit_apply_of_ne R K v s hw]; exact one_mem _
  have key : ∀ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 →
      IsLevelOneMatrix R K N (glFin R K (heckeGenAt R K v s) : Matrix _ _ _) := by
    intro s hs
    refine ⟨⟨fun i j => ?_, ?_⟩, ?_⟩
    · fin_cases i <;> fin_cases j
      · exact hint s hs
      · exact zero_mem_integralFiniteAdeles
      · exact zero_mem_integralFiniteAdeles
      · exact one_mem_integralFiniteAdeles
    · exact zero_mem_idealBall N
    · show (1 : FiniteAdeleRing R K) - 1 ∈ idealBall R K N
      rw [sub_self]; exact zero_mem_idealBall N
  refine ⟨key u hu1, ?_⟩
  rw [← map_inv, ← map_inv]
  exact key u⁻¹ hui

variable (K v)

def uniformizer : R := Classical.choose v.intValuation_exists_uniformizer

theorem intValuation_uniformizer : v.intValuation (uniformizer v) = WithZero.exp (-1 : ℤ) :=
  Classical.choose_spec v.intValuation_exists_uniformizer

theorem valued_uniformizer :
    Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K (uniformizer v)))
      = WithZero.exp (-1 : ℤ) := by
  rw [valued_algebraMap, intValuation_uniformizer]

def uniformizerUnit : (v.adicCompletion K)ˣ :=
  Units.mk0 (algebraMap K (v.adicCompletion K) (algebraMap R K (uniformizer v))) fun h => by
    have := valued_uniformizer K v
    rw [h, map_zero] at this
    exact WithZero.exp_ne_zero this.symm

theorem valued_uniformizerUnit :
    Valued.v (uniformizerUnit K v : v.adicCompletion K) = WithZero.exp (-1 : ℤ) :=
  valued_uniformizer K v

variable (R)

def heckeGen : GL (Fin 2) (AdeleRing R K) := heckeGenAt R K v (uniformizerUnit K v)

variable {R K v}

theorem heckeGen_inv_mul_heckeGenAt_mem_levelOne (t : (v.adicCompletion K)ˣ)
    (ht : Valued.v (t : v.adicCompletion K) = WithZero.exp (-1 : ℤ)) (N : Ideal R) :
    (heckeGen R K v)⁻¹ * heckeGenAt R K v t ∈ levelOne R K N :=
  heckeGenAt_inv_mul_heckeGenAt_mem_levelOne _ _ ((valued_uniformizerUnit K v).trans ht.symm) N

end Gen

end NumberField.AdelicLevel

end
