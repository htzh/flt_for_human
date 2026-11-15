/-
  The finite-place integrality calculus of conjugates and translates.

  Four rows of the same subject — moving an element of `GL₂` into a fixed integral
  subgroup, the Borel, or the rational-centre unipotent set:

  * `exists_upperTriangular_globalPoints_mul_mul_scalar_mul_finIdeleDiag_inv_mem_finiteIntegralGL2`:
    for a finite-adelic `g` and units `a d` whose valuations and content class satisfy the
    stated conditions, some *global* upper-triangular `b` and finite idèle unit `s` put
    `glFin (globalPoints b) * g * scalar s * (glFin (finIdeleDiag a))⁻¹` into the finite
    integral subgroup `finiteIntegralGL2`. This is the integrality half of the level
    bookkeeping — the half that is not a statement about the content map `contentHomFin`
    alone.
  * `exists_borel_mul_gl2Weyl_mul_unipotentGL2_eq_of_integral`: a `GL₂(v.adicCompletion F)`
    element that is integral with integral inverse is `β * gl2Weyl * unipotentGL2 x`, or
    that times `gl2Weyl⁻¹`, with `β` upper triangular and integral both ways — the local
    Bruhat–Iwahori cell decomposition.
  * `exists_forall_adelicGLHaar_image2_unipotentGL2_mul_mul_le_of_isCompact`: the additive
    Haar measure of `unipotentGL2 '' (closure (adelicBox K)) · s · C` is uniformly bounded
    on a centre-cut Siegel set, for `C` compact.
  * `mem_rationalCentreUnipotent_iff_heckeGen_mul_centralScalar_conj_mem`: membership in the
    rational-centre unipotent set is invariant under conjugation by
    `heckeGen v * centralScalar u`, with the two engines `diagOne_mul_unipotentGL2_mul_inv`
    and `conj_mem_rationalCentreUnipotent`.

  Transcribed from the four `S_` files below (pinned `aa2d8b3`, 587 + 156 + 317 + 119 lines).
  The pin's `centralScalar_mul_comm` is **not** restated: the port has it publicly and more
  generally at the pin's own name in `AutomorphicForm/Adelic/Basic.lean` (arbitrary
  commutative ring `R`, not only `𝓞 K`).

  spec-pin: P2M/Sol/S_AutomorphicForm_exists_upperTriangular_globalPoints_mul_mul_scalar_mul_finIdeleDiag_inv_mem_finiteIntegralGL2.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_exists_borel_mul_gl2Weyl_mul_unipotentGL2_eq_of_integral.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_exists_forall_adelicGLHaar_image2_unipotentGL2_mul_mul_le_of_isCompact.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_mem_rationalCentreUnipotent_iff_heckeGen_mul_centralScalar_conj_mem.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.ProductionPinsGeneral
import FLTForHuman.AutomorphicForm.Adelic.Basic
import FLTForHuman.AutomorphicForm.Adelic.UnipotentQuotient
import FLTForHuman.AutomorphicForm.Adelic.WeylIntertwining
import FLTForHuman.AutomorphicForm.Adelic.WindowedSiegel.CentreCutSet
import FLTForHuman.NumberTheory.AdelicLevel.HeckeGen
import FLTForHuman.NumberTheory.AdelicHaar.GeneralLinear
import FLTForHuman.NumberTheory.AdelicBox

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicBox NumberField.AdelicHaar NumberField.AdelicLevel
open IsDedekindDomain AutomorphicForm.WindowedSiegel
open scoped ENNReal Classical nonZeroDivisors

namespace AutomorphicForm

/-! ### The content/valuation correction engine

Given finite idèles `a d` whose valuations are chosen as in the row, the class condition
`contentHomFin a * contentHomFin d ^ 2 = contentHomFin (det g)` lets both `s * d` and
`s * s * det g * a⁻¹` be written as a principal scalar times a unit idèle (`s` is chosen so
that `contentHomFin s = (contentHomFin d)⁻¹`, splitting the class difference into two squares).
The bottom row of `g`, scaled by `d⁻¹`, then has `Valued.v`-maximum `1` at every finite place;
an explicit Bézout splitting `σ c₀ + τ d₀ = 1` makes the top row correctable by a single
rational `ν`, which is what turns the assembled entries into integral ones. -/

section FiniteIntegralGL2Engine

variable {F : Type} [Field F] [NumberField F]

private theorem valued_eq_exp_neg (v : HeightOneSpectrum (𝓞 F))
    (δ : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    Valued.v ((δ : FiniteAdeleRing (𝓞 F) F) v) = WithZero.exp (-finIdeleExponentAt F v δ) := by
  have hne : Valued.v ((δ : FiniteAdeleRing (𝓞 F) F) v) ≠ 0 := by
    rw [ne_eq, map_eq_zero]
    intro h
    have : ((δ * δ⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v = 1 := by
      rw [mul_inv_cancel, Units.val_one, coe_one_apply]
    rw [Units.val_mul, coe_mul_apply, h, zero_mul] at this
    exact zero_ne_one this
  rw [finIdeleExponentAt, neg_neg, WithZero.exp_log hne]

private theorem count_spanSingleton_mk' (v : HeightOneSpectrum (𝓞 F)) {n : 𝓞 F} (hn : n ≠ 0)
    (d : (𝓞 F)⁰) :
    FractionalIdeal.count F v (FractionalIdeal.spanSingleton (𝓞 F)⁰ (IsLocalization.mk' F n d)) =
      ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {n} : Ideal (𝓞 F))).factors : ℤ)
        - (Associates.mk v.asIdeal).count
            (Associates.mk (Ideal.span {(d : 𝓞 F)} : Ideal (𝓞 F))).factors := by
  classical
  have hd : (d : 𝓞 F) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  have hspan : FractionalIdeal.spanSingleton (𝓞 F)⁰ (IsLocalization.mk' F n d) =
      ((Ideal.span {n} : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) *
        (((Ideal.span {(d : 𝓞 F)} : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F))⁻¹ := by
    rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_inv, FractionalIdeal.spanSingleton_mul_spanSingleton,
      IsFractionRing.mk'_eq_div, div_eq_mul_inv]
  have hn' : ((Ideal.span {n} : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
    rw [ne_eq, FractionalIdeal.coeIdeal_eq_zero, Ideal.span_singleton_eq_bot]; exact hn
  have hd' : ((Ideal.span {(d : 𝓞 F)} : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
    rw [ne_eq, FractionalIdeal.coeIdeal_eq_zero, Ideal.span_singleton_eq_bot]; exact hd
  rw [hspan, FractionalIdeal.count_mul F v hn' (inv_ne_zero hd'), FractionalIdeal.count_inv,
    FractionalIdeal.count_coe F v
      (by rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hn :
        (Ideal.span {n} : Ideal (𝓞 F)) ≠ 0),
    FractionalIdeal.count_coe F v
      (by rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hd :
        (Ideal.span {(d : 𝓞 F)} : Ideal (𝓞 F)) ≠ 0), sub_eq_add_neg]

private theorem valued_algebraMap_mk' (v : HeightOneSpectrum (𝓞 F)) {n : 𝓞 F} (hn : n ≠ 0)
    (d : (𝓞 F)⁰) :
    Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) (IsLocalization.mk' F n d)) v) =
      WithZero.exp (-(((Associates.mk v.asIdeal).count
          (Associates.mk (Ideal.span {n} : Ideal (𝓞 F))).factors : ℤ)
        - (Associates.mk v.asIdeal).count
            (Associates.mk (Ideal.span {(d : 𝓞 F)} : Ideal (𝓞 F))).factors)) := by
  have hd : (d : 𝓞 F) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    HeightOneSpectrum.valuation_of_mk', HeightOneSpectrum.intValuation_if_neg _ hn,
    HeightOneSpectrum.intValuation_if_neg _ hd, ← WithZero.exp_sub]
  congr 1
  ring

private theorem exists_eq_algebraMap_mul_of_contentHomFin_eq_one
    (x : (FiniteAdeleRing (𝓞 F) F)ˣ) (hx : contentHomFin F x = 1) :
    ∃ (k : F) (hk : k ≠ 0) (u : (FiniteAdeleRing (𝓞 F) F)ˣ),
      x = Units.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)).toMonoidHom (Units.mk0 k hk) * u ∧
      ∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((u : FiniteAdeleRing (𝓞 F) F) v) = 1 := by
  classical
  rw [contentHomFin_apply, ClassGroup.mk_eq_one_iff, Units.val_mk0,
    FractionalIdeal.isPrincipal_iff] at hx
  obtain ⟨k, hk⟩ := hx
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [FractionalIdeal.spanSingleton_zero] at hk
    exact finAssocFracIdeal_ne_zero F x hk
  obtain ⟨n, d, hnd⟩ := IsLocalization.exists_mk'_eq (𝓞 F)⁰ k
  have hn : n ≠ 0 := by
    rintro rfl
    rw [IsLocalization.mk'_zero] at hnd
    exact hk0 hnd.symm
  set kU : (FiniteAdeleRing (𝓞 F) F)ˣ :=
    Units.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)).toMonoidHom (Units.mk0 k hk0) with hkU
  refine ⟨k, hk0, kU⁻¹ * x, by rw [mul_inv_cancel_left], fun v => ?_⟩

  have hex : finIdeleExponentAt F v x =
      ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {n} : Ideal (𝓞 F))).factors : ℤ)
        - (Associates.mk v.asIdeal).count
            (Associates.mk (Ideal.span {(d : 𝓞 F)} : Ideal (𝓞 F))).factors := by
    rw [← count_finAssocFracIdeal, hk, ← hnd, count_spanSingleton_mk' v hn d]
  have hkv : Valued.v (((kU⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v) *
      Valued.v ((kU : FiniteAdeleRing (𝓞 F) F) v) = 1 := by
    rw [← map_mul, ← coe_mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      coe_one_apply, map_one]
  have hkval : Valued.v ((kU : FiniteAdeleRing (𝓞 F) F) v) =
      WithZero.exp (-(((Associates.mk v.asIdeal).count
          (Associates.mk (Ideal.span {n} : Ideal (𝓞 F))).factors : ℤ)
        - (Associates.mk v.asIdeal).count
            (Associates.mk (Ideal.span {(d : 𝓞 F)} : Ideal (𝓞 F))).factors)) := by
    rw [hkU]
    show Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) k) v) = _
    rw [← hnd]
    exact valued_algebraMap_mk' v hn d
  rw [Units.val_mul, coe_mul_apply, map_mul, valued_eq_exp_neg v x, hex]
  rw [hkval] at hkv

  set e : ℤ := ((Associates.mk v.asIdeal).count
      (Associates.mk (Ideal.span {n} : Ideal (𝓞 F))).factors : ℤ)
    - (Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span {(d : 𝓞 F)} : Ideal (𝓞 F))).factors with he
  have hinv : Valued.v (((kU⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v) =
      WithZero.exp e := by
    have h2 : WithZero.exp (-e) ≠ (0 : WithZero (Multiplicative ℤ)) := WithZero.exp_ne_zero
    calc Valued.v (((kU⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v)
        = Valued.v (((kU⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v) *
            WithZero.exp (-e) * (WithZero.exp (-e))⁻¹ := by rw [mul_inv_cancel_right₀ h2]
      _ = (WithZero.exp (-e))⁻¹ := by rw [hkv, one_mul]
      _ = WithZero.exp e := by rw [WithZero.exp_neg, inv_inv]
  rw [hinv, ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]

private theorem mem_integers_of_valued_eq_one {u : (FiniteAdeleRing (𝓞 F) F)ˣ}
    (hu : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((u : FiniteAdeleRing (𝓞 F) F) v) = 1)
    (v : HeightOneSpectrum (𝓞 F)) :
    (u : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F ∧
      ((u⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v
        ∈ v.adicCompletionIntegers F := by
  have hprod : Valued.v ((u : FiniteAdeleRing (𝓞 F) F) v) *
      Valued.v (((u⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v) = 1 := by
    rw [← map_mul, ← coe_mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      coe_one_apply, map_one]
  rw [hu v, one_mul] at hprod
  rw [HeightOneSpectrum.mem_adicCompletionIntegers,
    HeightOneSpectrum.mem_adicCompletionIntegers, hu v, hprod]
  exact ⟨le_rfl, le_rfl⟩

private theorem glFin_finIdeleDiag (δ : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    glFin (𝓞 F) F (finIdeleDiag F δ) = diagOne δ := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;> rfl

private theorem mem_integral_of_forall_valued_le {x : FiniteAdeleRing (𝓞 F) F}
    (hx : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (x v) ≤ 1) :
    x ∈ integralFiniteAdeles (𝓞 F) F :=
  fun v => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (hx v)

private theorem neg_mem_integral {x : FiniteAdeleRing (𝓞 F) F}
    (hx : x ∈ integralFiniteAdeles (𝓞 F) F) : -x ∈ integralFiniteAdeles (𝓞 F) F := by
  have h := sub_mem_integralFiniteAdeles zero_mem_integralFiniteAdeles hx
  rwa [zero_sub] at h

private theorem unit_mem_integral {u : (FiniteAdeleRing (𝓞 F) F)ˣ}
    (hu : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((u : FiniteAdeleRing (𝓞 F) F) v) = 1) :
    (u : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F :=
  fun v => (mem_integers_of_valued_eq_one hu v).1

private theorem unit_inv_mem_integral {u : (FiniteAdeleRing (𝓞 F) F)ˣ}
    (hu : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((u : FiniteAdeleRing (𝓞 F) F) v) = 1) :
    ((u⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F :=
  fun v => (mem_integers_of_valued_eq_one hu v).2

private theorem ne_zero_of_valued_eq_one {v : HeightOneSpectrum (𝓞 F)} {x : v.adicCompletion F}
    (hx : Valued.v x = 1) : x ≠ 0 := by
  rintro rfl
  rw [map_zero] at hx
  exact zero_ne_one hx

private theorem exists_unimodular_splitting (c₀ d₀ : FiniteAdeleRing (𝓞 F) F)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), max (Valued.v (c₀ v)) (Valued.v (d₀ v)) = 1) :
    ∃ σ τ : FiniteAdeleRing (𝓞 F) F, σ ∈ integralFiniteAdeles (𝓞 F) F ∧
      τ ∈ integralFiniteAdeles (𝓞 F) F ∧ σ * c₀ + τ * d₀ = 1 := by

  have hc : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (d₀ v) ≠ 1 → Valued.v (c₀ v) = 1 := by
    intro v hv
    rcases le_total (Valued.v (c₀ v)) (Valued.v (d₀ v)) with hle | hle
    · exact absurd (by rw [← h v, max_eq_right hle]) hv
    · rw [← h v, max_eq_left hle]

  have hσint : ∀ v : HeightOneSpectrum (𝓞 F),
      (if Valued.v (d₀ v) = 1 then (0 : v.adicCompletion F) else (c₀ v)⁻¹)
        ∈ v.adicCompletionIntegers F := by
    intro v
    split_ifs with hv
    · exact zero_mem _
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hc v hv, inv_one]
  have hτint : ∀ v : HeightOneSpectrum (𝓞 F),
      (if Valued.v (d₀ v) = 1 then (d₀ v)⁻¹ else (0 : v.adicCompletion F))
        ∈ v.adicCompletionIntegers F := by
    intro v
    split_ifs with hv
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv, inv_one]
    · exact zero_mem _
  refine ⟨⟨fun v => if Valued.v (d₀ v) = 1 then 0 else (c₀ v)⁻¹,
      Filter.Eventually.of_forall hσint⟩,
    ⟨fun v => if Valued.v (d₀ v) = 1 then (d₀ v)⁻¹ else 0,
      Filter.Eventually.of_forall hτint⟩, hσint, hτint, ?_⟩
  refine Subtype.ext (funext fun v => ?_)
  show (if Valued.v (d₀ v) = 1 then (0 : v.adicCompletion F) else (c₀ v)⁻¹) * c₀ v +
      (if Valued.v (d₀ v) = 1 then (d₀ v)⁻¹ else (0 : v.adicCompletion F)) * d₀ v = 1
  split_ifs with hv
  · rw [zero_mul, zero_add, inv_mul_cancel₀ (ne_zero_of_valued_eq_one hv)]
  · rw [zero_mul, add_zero, inv_mul_cancel₀ (ne_zero_of_valued_eq_one (hc v hv))]

private theorem mem_finiteIntegralGL2_of_coe_eq (n : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))
    (p q r t : FiniteAdeleRing (𝓞 F) F)
    (hn : (n : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) = !![p, q; r, t])
    (hp : p ∈ integralFiniteAdeles (𝓞 F) F) (hq : q ∈ integralFiniteAdeles (𝓞 F) F)
    (hr : r ∈ integralFiniteAdeles (𝓞 F) F) (ht : t ∈ integralFiniteAdeles (𝓞 F) F)
    (u : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hu : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((u : FiniteAdeleRing (𝓞 F) F) v) = 1)
    (hdet : p * t - q * r = u) : n ∈ finiteIntegralGL2 (𝓞 F) F := by
  have hui := unit_inv_mem_integral hu
  rw [mem_finiteIntegralGL2_iff]
  constructor
  · intro i j
    rw [hn]
    fin_cases i <;> fin_cases j
    · simpa using hp
    · simpa using hq
    · simpa using hr
    · simpa using ht
  · intro i j
    rw [Matrix.GeneralLinearGroup.coe_inv, hn, Matrix.inv_def, Matrix.det_fin_two_of, hdet,
      Ring.inverse_unit, Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases j
    · simpa using mul_mem_integralFiniteAdeles hui ht
    · simpa using mul_mem_integralFiniteAdeles hui (neg_mem_integral hq)
    · simpa using mul_mem_integralFiniteAdeles hui (neg_mem_integral hr)
    · simpa using mul_mem_integralFiniteAdeles hui hp

omit [NumberField F] in
private theorem coe_mkB (α μ δ : F) (h : Matrix.det !![α, μ; 0, δ] ≠ 0) :
    ((Matrix.GeneralLinearGroup.mkOfDetNeZero !![α, μ; 0, δ] h : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = !![α, μ; 0, δ] := rfl

private theorem coe_glFin_globalPoints_mkB (α μ δ : F) (h : Matrix.det !![α, μ; 0, δ] ≠ 0) :
    ((glFin (𝓞 F) F (globalPoints (𝓞 F) F
        (Matrix.GeneralLinearGroup.mkOfDetNeZero !![α, μ; 0, δ] h)) :
          GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) =
      !![algebraMap F (FiniteAdeleRing (𝓞 F) F) α, algebraMap F (FiniteAdeleRing (𝓞 F) F) μ;
         0, algebraMap F (FiniteAdeleRing (𝓞 F) F) δ] := by
  refine Matrix.ext fun i j => ?_
  rw [AutomorphicForm.SiegelReduction.glFin_globalPoints_apply, coe_mkB]
  fin_cases i <;> fin_cases j <;> simp

private theorem coe_scalar (s : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) s : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) =
      Matrix.scalar (Fin 2) (s : FiniteAdeleRing (𝓞 F) F) := rfl

private theorem coe_diagOne_inv (a : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    (((diagOne a)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) =
      Matrix.diagonal ![((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F), 1] := by
  rw [← map_inv]
  exact Matrix.ext fun i j => diagOne_coe_apply _ i j

private theorem coe_assembled (α μ δ : F) (h : Matrix.det !![α, μ; 0, δ] ≠ 0)
    (g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) (s a : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    ((glFin (𝓞 F) F (globalPoints (𝓞 F) F
          (Matrix.GeneralLinearGroup.mkOfDetNeZero !![α, μ; 0, δ] h)) * g *
        Matrix.GeneralLinearGroup.scalar (Fin 2) s * (glFin (𝓞 F) F (finIdeleDiag F a))⁻¹ :
          GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) =
      !![(algebraMap F (FiniteAdeleRing (𝓞 F) F) α *
              (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 0 +
            algebraMap F (FiniteAdeleRing (𝓞 F) F) μ *
              (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0) *
            (s : FiniteAdeleRing (𝓞 F) F) *
            ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F),
          (algebraMap F (FiniteAdeleRing (𝓞 F) F) α *
              (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 1 +
            algebraMap F (FiniteAdeleRing (𝓞 F) F) μ *
              (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1) *
            (s : FiniteAdeleRing (𝓞 F) F);
          algebraMap F (FiniteAdeleRing (𝓞 F) F) δ *
              (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0 *
            (s : FiniteAdeleRing (𝓞 F) F) *
            ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F),
          algebraMap F (FiniteAdeleRing (𝓞 F) F) δ *
              (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 *
            (s : FiniteAdeleRing (𝓞 F) F)] := by
  rw [glFin_finIdeleDiag, Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
    Matrix.GeneralLinearGroup.coe_mul, coe_glFin_globalPoints_mkB, coe_scalar, coe_diagOne_inv]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.scalar_apply] <;> ring

private theorem exists_upperTriangular_mul_scalar_diag_mem_finiteIntegralGL2
    (g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))
    (a d : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hd : ∀ v : HeightOneSpectrum (𝓞 F),
      Valued.v ((d : FiniteAdeleRing (𝓞 F) F) v) =
        max
          (Valued.v (((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0 *
            ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)) v))
          (Valued.v (((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1) v)))
    (hcls : contentHomFin F a * contentHomFin F d ^ 2 =
      contentHomFin F (Matrix.GeneralLinearGroup.det g)) :
    ∃ b : GL (Fin 2) F, (b : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      ∃ s : (FiniteAdeleRing (𝓞 F) F)ˣ,
        glFin (𝓞 F) F (globalPoints (𝓞 F) F b) * g * Matrix.GeneralLinearGroup.scalar (Fin 2) s *
          (glFin (𝓞 F) F (finIdeleDiag F a))⁻¹ ∈ finiteIntegralGL2 (𝓞 F) F := by

  obtain ⟨s, hs⟩ := contentHomFin_surjective F (contentHomFin F d)⁻¹

  have h1 : contentHomFin F (s * d) = 1 := by rw [map_mul, hs, inv_mul_cancel]
  obtain ⟨k₂, hk₂, u₂, hsd, hu₂⟩ := exists_eq_algebraMap_mul_of_contentHomFin_eq_one (s * d) h1
  have h2 : contentHomFin F (s * s * Matrix.GeneralLinearGroup.det g * a⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, hs, ← hcls, ← sq, inv_pow,
      mul_comm (contentHomFin F a) (contentHomFin F d ^ 2), ← mul_assoc, inv_mul_cancel, one_mul,
      mul_inv_cancel]
  obtain ⟨k₁, hk₁, u₁, hdet, hu₁⟩ :=
    exists_eq_algebraMap_mul_of_contentHomFin_eq_one (s * s * Matrix.GeneralLinearGroup.det g * a⁻¹) h2

  have E1 : (s : FiniteAdeleRing (𝓞 F) F) * d = algebraMap F (FiniteAdeleRing (𝓞 F) F) k₂ * u₂ := by
    have := congrArg Units.val hsd
    simpa using this
  have E2 : (s : FiniteAdeleRing (𝓞 F) F) * s *
      ((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 0 *
          (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 -
        (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 1 *
          (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0) *
      ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) =
      algebraMap F (FiniteAdeleRing (𝓞 F) F) k₁ * u₁ := by
    have := congrArg Units.val hdet
    simpa [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two] using this

  have hdd : (d : FiniteAdeleRing (𝓞 F) F) *
      ((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) = 1 := Units.mul_inv d
  have huu : (u₂ : FiniteAdeleRing (𝓞 F) F) *
      ((u₂⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) = 1 := Units.mul_inv u₂
  have hδ' : algebraMap F (FiniteAdeleRing (𝓞 F) F) k₂⁻¹ *
      algebraMap F (FiniteAdeleRing (𝓞 F) F) k₂ = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hk₂, map_one]
  have hαδk : algebraMap F (FiniteAdeleRing (𝓞 F) F) (k₂ / k₁) *
      algebraMap F (FiniteAdeleRing (𝓞 F) F) k₂⁻¹ * algebraMap F (FiniteAdeleRing (𝓞 F) F) k₁ = 1 := by
    rw [← map_mul, ← map_mul, show k₂ / k₁ * k₂⁻¹ * k₁ = 1 by field_simp, map_one]

  have hdv : ∀ v : HeightOneSpectrum (𝓞 F),
      Valued.v (((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v) =
        (Valued.v ((d : FiniteAdeleRing (𝓞 F) F) v))⁻¹ := by
    intro v
    have hprod : Valued.v ((d : FiniteAdeleRing (𝓞 F) F) v) *
        Valued.v (((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v) = 1 := by
      rw [← map_mul, ← coe_mul_apply, hdd, coe_one_apply, map_one]
    exact eq_inv_of_mul_eq_one_right hprod
  have hdne : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((d : FiniteAdeleRing (𝓞 F) F) v) ≠ 0 := by
    intro v
    rw [valued_eq_exp_neg]
    exact WithZero.exp_ne_zero
  have hcd : ∀ v : HeightOneSpectrum (𝓞 F),
      max (Valued.v (((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0 *
            ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) *
            ((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)) v))
        (Valued.v (((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 *
            ((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)) v)) = 1 := by
    intro v
    have e₁ : Valued.v (((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0 *
          ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) *
          ((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)) v) =
        Valued.v (((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0 *
          ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)) v) *
          (Valued.v ((d : FiniteAdeleRing (𝓞 F) F) v))⁻¹ := by
      rw [coe_mul_apply, map_mul, hdv v]
    have e₂ : Valued.v (((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 *
          ((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)) v) =
        Valued.v (((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1) v) *
          (Valued.v ((d : FiniteAdeleRing (𝓞 F) F) v))⁻¹ := by
      rw [coe_mul_apply, map_mul, hdv v]
    rw [e₁, e₂]
    have hm := hd v
    have hne := hdne v
    rcases le_total
        (Valued.v (((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0 *
          ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)) v))
        (Valued.v (((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1) v)) with hle | hle
    · rw [max_eq_right hle] at hm
      rw [← hm] at hle ⊢
      rw [mul_inv_cancel₀ hne]
      exact max_eq_right ((mul_le_mul_left hle _).trans_eq (mul_inv_cancel₀ hne))
    · rw [max_eq_left hle] at hm
      rw [← hm] at hle ⊢
      rw [mul_inv_cancel₀ hne]
      exact max_eq_left ((mul_le_mul_left hle _).trans_eq (mul_inv_cancel₀ hne))
  obtain ⟨σ, τ, hσ, hτ, hστ⟩ := exists_unimodular_splitting _ _ hcd
  have hc₀ : (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0 *
      ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) *
      ((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F :=
    mem_integral_of_forall_valued_le fun v => (le_max_left _ _).trans (hcd v).le
  have hd₀ : (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 *
      ((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F :=
    mem_integral_of_forall_valued_le fun v => (le_max_right _ _).trans (hcd v).le

  set c₀ : FiniteAdeleRing (𝓞 F) F := (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0 *
      ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) *
      ((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) with hc₀e
  set d₀ : FiniteAdeleRing (𝓞 F) F := (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 *
      ((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) with hd₀e
  set Y₁ : FiniteAdeleRing (𝓞 F) F := algebraMap F (FiniteAdeleRing (𝓞 F) F) (k₂ / k₁) *
      (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 0 *
      ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) * (s : FiniteAdeleRing (𝓞 F) F) *
      ((u₂⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) with hY₁e
  set Y₂ : FiniteAdeleRing (𝓞 F) F := algebraMap F (FiniteAdeleRing (𝓞 F) F) (k₂ / k₁) *
      (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 1 * (s : FiniteAdeleRing (𝓞 F) F) *
      ((u₂⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) with hY₂e

  obtain ⟨ν, hν⟩ := NumberField.AdelicBox.exists_algebraMap_add_mem_integralFiniteAdeles (𝓞 F) F
    (σ * Y₁ + τ * Y₂)
  have hμ : algebraMap F (FiniteAdeleRing (𝓞 F) F) (ν / k₂) * algebraMap F (FiniteAdeleRing (𝓞 F) F) k₂ =
      algebraMap F (FiniteAdeleRing (𝓞 F) F) ν := by
    rw [← map_mul, div_mul_cancel₀ ν hk₂]
  have hdetB : Matrix.det !![k₂ / k₁, ν / k₂; 0, k₂⁻¹] ≠ 0 := by
    rw [Matrix.det_fin_two_of]
    simp [hk₁, hk₂]

  have hdinv' : algebraMap F (FiniteAdeleRing (𝓞 F) F) k₂⁻¹ * (s : FiniteAdeleRing (𝓞 F) F) *
      ((u₂⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) =
      ((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) := by
    linear_combination (-(algebraMap F (FiniteAdeleRing (𝓞 F) F) k₂⁻¹ * (s : FiniteAdeleRing (𝓞 F) F) *
        ((u₂⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F))) * hdd +
      (((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) *
        ((u₂⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) *
        algebraMap F (FiniteAdeleRing (𝓞 F) F) k₂⁻¹) * E1 +
      (((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) * (u₂ : FiniteAdeleRing (𝓞 F) F) *
        ((u₂⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)) * hδ' +
      (((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)) * huu
  have hu₁' : (u₁ : FiniteAdeleRing (𝓞 F) F) =
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (k₂ / k₁) * algebraMap F (FiniteAdeleRing (𝓞 F) F) k₂⁻¹ *
        ((s : FiniteAdeleRing (𝓞 F) F) * s *
          ((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 0 *
              (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 -
            (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 1 *
              (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0) *
          ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)) := by
    rw [E2]
    linear_combination (-(u₁ : FiniteAdeleRing (𝓞 F) F)) * hαδk
  have hε : Y₁ * d₀ - Y₂ * c₀ = (u₁ : FiniteAdeleRing (𝓞 F) F) *
      ((u₂⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) *
      ((u₂⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) := by
    rw [hu₁', hY₁e, hY₂e, hc₀e, hd₀e]
    linear_combination (-(algebraMap F (FiniteAdeleRing (𝓞 F) F) (k₂ / k₁) * (s : FiniteAdeleRing (𝓞 F) F) *
        ((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 0 *
            (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 -
          (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 1 *
            (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0) *
        ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) *
        ((u₂⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F))) * hdinv'
  have n10 : algebraMap F (FiniteAdeleRing (𝓞 F) F) k₂⁻¹ *
        (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0 * (s : FiniteAdeleRing (𝓞 F) F) *
        ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) =
      (u₂ : FiniteAdeleRing (𝓞 F) F) * c₀ := by
    rw [hc₀e]
    linear_combination (-(algebraMap F (FiniteAdeleRing (𝓞 F) F) k₂⁻¹ *
        ((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0 *
          ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)) * (s : FiniteAdeleRing (𝓞 F) F))) * hdd +
      (((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0 *
          ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)) *
        ((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) *
        algebraMap F (FiniteAdeleRing (𝓞 F) F) k₂⁻¹) * E1 +
      (((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0 *
          ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)) *
        ((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) * (u₂ : FiniteAdeleRing (𝓞 F) F)) * hδ'
  have n11 : algebraMap F (FiniteAdeleRing (𝓞 F) F) k₂⁻¹ *
        (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 * (s : FiniteAdeleRing (𝓞 F) F) =
      (u₂ : FiniteAdeleRing (𝓞 F) F) * d₀ := by
    rw [hd₀e]
    linear_combination (-(algebraMap F (FiniteAdeleRing (𝓞 F) F) k₂⁻¹ *
        (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 * (s : FiniteAdeleRing (𝓞 F) F))) * hdd +
      ((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 *
        ((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) *
        algebraMap F (FiniteAdeleRing (𝓞 F) F) k₂⁻¹) * E1 +
      ((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 *
        ((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) * (u₂ : FiniteAdeleRing (𝓞 F) F)) * hδ'
  have n00 : (algebraMap F (FiniteAdeleRing (𝓞 F) F) (k₂ / k₁) *
          (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 0 +
        algebraMap F (FiniteAdeleRing (𝓞 F) F) (ν / k₂) *
          (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0) *
        (s : FiniteAdeleRing (𝓞 F) F) * ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) =
      (u₂ : FiniteAdeleRing (𝓞 F) F) * (Y₁ + algebraMap F (FiniteAdeleRing (𝓞 F) F) ν * c₀) := by
    rw [hY₁e, hc₀e]
    linear_combination (-(algebraMap F (FiniteAdeleRing (𝓞 F) F) (k₂ / k₁) *
        (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 0 * (s : FiniteAdeleRing (𝓞 F) F) *
        ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F))) * huu +
      ((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0 *
        ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) *
        ((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) * (u₂ : FiniteAdeleRing (𝓞 F) F)) * hμ +
      ((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0 *
        ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) *
        algebraMap F (FiniteAdeleRing (𝓞 F) F) (ν / k₂) *
        ((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)) * E1 +
      (-((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0 *
        ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) *
        algebraMap F (FiniteAdeleRing (𝓞 F) F) (ν / k₂) * (s : FiniteAdeleRing (𝓞 F) F))) * hdd
  have n01 : (algebraMap F (FiniteAdeleRing (𝓞 F) F) (k₂ / k₁) *
          (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 1 +
        algebraMap F (FiniteAdeleRing (𝓞 F) F) (ν / k₂) *
          (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1) * (s : FiniteAdeleRing (𝓞 F) F) =
      (u₂ : FiniteAdeleRing (𝓞 F) F) * (Y₂ + algebraMap F (FiniteAdeleRing (𝓞 F) F) ν * d₀) := by
    rw [hY₂e, hd₀e]
    linear_combination (-(algebraMap F (FiniteAdeleRing (𝓞 F) F) (k₂ / k₁) *
        (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 1 * (s : FiniteAdeleRing (𝓞 F) F))) * huu +
      ((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 *
        ((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) * (u₂ : FiniteAdeleRing (𝓞 F) F)) * hμ +
      ((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 *
        algebraMap F (FiniteAdeleRing (𝓞 F) F) (ν / k₂) *
        ((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)) * E1 +
      (-((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 *
        algebraMap F (FiniteAdeleRing (𝓞 F) F) (ν / k₂) * (s : FiniteAdeleRing (𝓞 F) F))) * hdd

  have hu₂i := unit_mem_integral hu₂
  have hεi : Y₁ * d₀ - Y₂ * c₀ ∈ integralFiniteAdeles (𝓞 F) F := by
    rw [hε]
    exact mul_mem_integralFiniteAdeles
      (mul_mem_integralFiniteAdeles (unit_mem_integral hu₁) (unit_inv_mem_integral hu₂))
      (unit_inv_mem_integral hu₂)
  have top1 : Y₁ + algebraMap F (FiniteAdeleRing (𝓞 F) F) ν * c₀ =
      τ * (Y₁ * d₀ - Y₂ * c₀) + (algebraMap F (FiniteAdeleRing (𝓞 F) F) ν + (σ * Y₁ + τ * Y₂)) * c₀ := by
    linear_combination (-Y₁) * hστ
  have top2 : Y₂ + algebraMap F (FiniteAdeleRing (𝓞 F) F) ν * d₀ =
      (-σ) * (Y₁ * d₀ - Y₂ * c₀) + (algebraMap F (FiniteAdeleRing (𝓞 F) F) ν + (σ * Y₁ + τ * Y₂)) * d₀ := by
    linear_combination (-Y₂) * hστ
  have h00 : Y₁ + algebraMap F (FiniteAdeleRing (𝓞 F) F) ν * c₀ ∈ integralFiniteAdeles (𝓞 F) F := by
    rw [top1]
    exact add_mem_integralFiniteAdeles (mul_mem_integralFiniteAdeles hτ hεi)
      (mul_mem_integralFiniteAdeles hν hc₀)
  have h01 : Y₂ + algebraMap F (FiniteAdeleRing (𝓞 F) F) ν * d₀ ∈ integralFiniteAdeles (𝓞 F) F := by
    rw [top2]
    exact add_mem_integralFiniteAdeles (mul_mem_integralFiniteAdeles (neg_mem_integral hσ) hεi)
      (mul_mem_integralFiniteAdeles hν hd₀)
  have hdetL : (u₂ : FiniteAdeleRing (𝓞 F) F) * (Y₁ + algebraMap F (FiniteAdeleRing (𝓞 F) F) ν * c₀) *
        ((u₂ : FiniteAdeleRing (𝓞 F) F) * d₀) -
      (u₂ : FiniteAdeleRing (𝓞 F) F) * (Y₂ + algebraMap F (FiniteAdeleRing (𝓞 F) F) ν * d₀) *
        ((u₂ : FiniteAdeleRing (𝓞 F) F) * c₀) = u₁ := by
    linear_combination ((u₂ : FiniteAdeleRing (𝓞 F) F) * u₂) * hε +
      ((u₁ : FiniteAdeleRing (𝓞 F) F) * ((u₂ : FiniteAdeleRing (𝓞 F) F) *
        ((u₂⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) + 1)) * huu

  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![k₂ / k₁, ν / k₂; 0, k₂⁻¹] hdetB, rfl, s, ?_⟩
  refine mem_finiteIntegralGL2_of_coe_eq _ _ _ _ _ ?_ (mul_mem_integralFiniteAdeles hu₂i h00)
    (mul_mem_integralFiniteAdeles hu₂i h01) (mul_mem_integralFiniteAdeles hu₂i hc₀)
    (mul_mem_integralFiniteAdeles hu₂i hd₀) u₁ hu₁ hdetL
  rw [coe_assembled, n00, n01, n10, n11]

end FiniteIntegralGL2Engine

theorem exists_upperTriangular_globalPoints_mul_mul_scalar_mul_finIdeleDiag_inv_mem_finiteIntegralGL2
    (F : Type) [Field F] [NumberField F]
    (g : Matrix.GeneralLinearGroup (Fin 2)
      (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F))
    (a d : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)ˣ)
    (hd : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
      Valued.v ((d : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F) v) =
        max
          (Valued.v (((g : Matrix (Fin 2) (Fin 2)
                (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) 1 0 *
              ((a⁻¹ : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)ˣ) :
                IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) v))
          (Valued.v (((g : Matrix (Fin 2) (Fin 2)
                (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) 1 1) v)))
    (hcls : AutomorphicForm.contentHomFin F a * AutomorphicForm.contentHomFin F d ^ 2 =
      AutomorphicForm.contentHomFin F (Matrix.GeneralLinearGroup.det g)) :
    ∃ b : Matrix.GeneralLinearGroup (Fin 2) F, (b : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      ∃ s : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)ˣ,
        NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers F) F
              (AutomorphicForm.globalPoints (NumberField.RingOfIntegers F) F b) * g *
            Matrix.GeneralLinearGroup.scalar (Fin 2) s *
          (NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers F) F
            (AutomorphicForm.finIdeleDiag F a))⁻¹
        ∈ NumberField.AdelicLevel.finiteIntegralGL2 (NumberField.RingOfIntegers F) F :=
  exists_upperTriangular_mul_scalar_diag_mem_finiteIntegralGL2 g a d hd hcls

theorem exists_borel_mul_gl2Weyl_mul_unipotentGL2_eq_of_integral
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (g : GL (Fin 2) (v.adicCompletion F))
    (_hg : ∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F)
    (_hg' : ∀ i j, ((g⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j
      ∈ v.adicCompletionIntegers F) :
    ∃ (β : GL (Fin 2) (v.adicCompletion F)) (x : v.adicCompletion F),
      (β : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0 ∧
      (∀ i j, (β : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F) ∧
      (∀ i j, ((β⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j
        ∈ v.adicCompletionIntegers F) ∧
      x ∈ v.adicCompletionIntegers F ∧
      (g = β * gl2Weyl * unipotentGL2 x ∨ g = β * gl2Weyl * unipotentGL2 x * gl2Weyl⁻¹) := by

  set a := (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 0 with ha
  set b := (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 1 with hb
  set c := (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 with hc
  set d := (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 with hd
  set p := ((g⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 0 with hp
  set q := ((g⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 1 with hq
  set r := ((g⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 with hr
  set t := ((g⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 with ht
  have hgm : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) = !![a, b; c, d] := by
    ext i j : 1; fin_cases i <;> fin_cases j <;> rfl
  have hgim : ((g⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) = !![p, q; r, t] := by
    ext i j : 1; fin_cases i <;> fin_cases j <;> rfl
  have hai : a ∈ v.adicCompletionIntegers F := _hg 0 0
  have hbi : b ∈ v.adicCompletionIntegers F := _hg 0 1
  have hci : c ∈ v.adicCompletionIntegers F := _hg 1 0
  have hdi : d ∈ v.adicCompletionIntegers F := _hg 1 1
  have hpi : p ∈ v.adicCompletionIntegers F := _hg' 0 0
  have hqi : q ∈ v.adicCompletionIntegers F := _hg' 0 1
  have hri : r ∈ v.adicCompletionIntegers F := _hg' 1 0
  have hti : t ∈ v.adicCompletionIntegers F := _hg' 1 1

  have hrow : c * q + d * t = 1 := by
    have h1 := congrArg (fun m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F) => m 1 1)
      (show ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
        * ((g⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) = 1) from by
          rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one])
    simp only [hgm, hgim, Matrix.mul_fin_two] at h1
    simpa using h1

  have mem_iff : ∀ y : v.adicCompletion F, y ∈ v.adicCompletionIntegers F ↔ Valued.v y ≤ 1 :=
    fun y => Iff.rfl
  by_cases hcu : Valued.v c = 1
  ·
    have hc0 : c ≠ 0 := by intro h; rw [h, map_zero] at hcu; exact zero_ne_one hcu
    set x : v.adicCompletion F := d / c with hx
    have hxi : x ∈ v.adicCompletionIntegers F := by
      rw [mem_iff, hx, map_div₀, hcu, div_one]; exact (mem_iff d).mp hdi
    set β : GL (Fin 2) (v.adicCompletion F) := g * (unipotentGL2 x)⁻¹ * gl2Weyl⁻¹ with hβ
    have hβm : (β : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) = !![b - a * x, a; d - c * x, c] := by
      rw [hβ, gl2Weyl_inv, Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, hgm, gl2Weyl_val]
      have : (((unipotentGL2 x)⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
          = !![1, -x; 0, 1] := rfl
      rw [this]
      simp only [Matrix.mul_fin_two]; ext i j : 1; fin_cases i <;> fin_cases j <;> simp <;> ring
    have hβim : ((β⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
        = !![r, t; p + x * r, q + x * t] := by
      rw [hβ, mul_inv_rev, mul_inv_rev, inv_inv, inv_inv, Matrix.GeneralLinearGroup.coe_mul,
        Matrix.GeneralLinearGroup.coe_mul, hgim, gl2Weyl_val, unipotentGL2_coe]
      simp only [Matrix.mul_fin_two]; ext i j : 1; fin_cases i <;> fin_cases j <;> simp
    have hdcx : d - c * x = 0 := by rw [hx, mul_div_cancel₀ _ hc0, sub_self]
    refine ⟨β, x, ?_, ?_, ?_, hxi, Or.inl ?_⟩
    · rw [hβm]; simp [hdcx]
    · intro i j
      rw [hβm]
      fin_cases i <;> fin_cases j
      · exact sub_mem hbi (mul_mem hai hxi)
      · exact hai
      · simp only [hdcx]; exact zero_mem _
      · exact hci
    · intro i j
      rw [hβim]
      fin_cases i <;> fin_cases j
      · exact hri
      · exact hti
      · exact add_mem hpi (mul_mem hxi hri)
      · exact add_mem hqi (mul_mem hxi hti)
    · rw [hβ]; simp only [mul_assoc, inv_mul_cancel, mul_one]
  ·
    have hclt : Valued.v c < 1 := lt_of_le_of_ne ((mem_iff c).mp hci) hcu
    have hdu : Valued.v d = 1 := by
      have hcq : Valued.v (c * q) < 1 := by
        rw [map_mul]
        calc Valued.v c * Valued.v q ≤ Valued.v c * 1 := mul_le_mul_right ((mem_iff q).mp hqi) _
          _ = Valued.v c := mul_one _
          _ < 1 := hclt
      have hdt : Valued.v (d * t) = 1 := by
        have h := hrow
        rw [add_comm] at h
        have : d * t = 1 - c * q := by rw [← h]; ring
        rw [this, Valuation.map_one_sub_of_lt _ hcq]
      rw [map_mul] at hdt
      have hd1 : Valued.v d ≤ 1 := (mem_iff d).mp hdi
      have ht1 : Valued.v t ≤ 1 := (mem_iff t).mp hti
      by_contra hne
      have hdlt : Valued.v d < 1 := lt_of_le_of_ne hd1 hne
      have : Valued.v d * Valued.v t < 1 := by
        calc Valued.v d * Valued.v t ≤ Valued.v d * 1 := mul_le_mul_right ht1 _
          _ = Valued.v d := mul_one _
          _ < 1 := hdlt
      rw [hdt] at this
      exact lt_irrefl _ this
    have hd0 : d ≠ 0 := by intro h; rw [h, map_zero] at hdu; exact zero_ne_one hdu
    set x : v.adicCompletion F := c / d with hx
    have hxi : x ∈ v.adicCompletionIntegers F := by
      rw [mem_iff, hx, map_div₀, hdu, div_one]; exact (mem_iff c).mp hci
    set β : GL (Fin 2) (v.adicCompletion F) := g * (gl2Weyl * unipotentGL2 x * gl2Weyl⁻¹)⁻¹ with hβ
    have hnm : ((gl2Weyl * unipotentGL2 x * gl2Weyl⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
        = !![1, 0; x, 1] := by
      rw [gl2Weyl_inv, Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, gl2Weyl_val, unipotentGL2_coe]
      simp only [Matrix.mul_fin_two]; ext i j : 1; fin_cases i <;> fin_cases j <;> simp
    have hnim : (((gl2Weyl * unipotentGL2 x * gl2Weyl⁻¹)⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
        = !![1, 0; -x, 1] := by
      rw [mul_inv_rev, mul_inv_rev, inv_inv, gl2Weyl_inv, ← mul_assoc, Matrix.GeneralLinearGroup.coe_mul,
        Matrix.GeneralLinearGroup.coe_mul, gl2Weyl_val]
      have : (((unipotentGL2 x)⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
          = !![1, -x; 0, 1] := rfl
      rw [this]
      simp only [Matrix.mul_fin_two]; ext i j : 1; fin_cases i <;> fin_cases j <;> simp
    have hβm : (β : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) = !![a - b * x, b; c - d * x, d] := by
      rw [hβ, Matrix.GeneralLinearGroup.coe_mul, hgm, hnim]
      simp only [Matrix.mul_fin_two]; ext i j : 1; fin_cases i <;> fin_cases j <;> simp <;> ring
    have hβim : ((β⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
        = !![p, q; x * p + r, x * q + t] := by
      rw [hβ, mul_inv_rev, inv_inv, Matrix.GeneralLinearGroup.coe_mul, hnm, hgim]
      simp only [Matrix.mul_fin_two]; ext i j : 1; fin_cases i <;> fin_cases j <;> simp
    have hcdx : c - d * x = 0 := by rw [hx, mul_div_cancel₀ _ hd0, sub_self]
    refine ⟨β, x, ?_, ?_, ?_, hxi, Or.inr ?_⟩
    · rw [hβm]; simp [hcdx]
    · intro i j
      rw [hβm]
      fin_cases i <;> fin_cases j
      · exact sub_mem hai (mul_mem hbi hxi)
      · exact hbi
      · simp only [hcdx]; exact zero_mem _
      · exact hdi
    · intro i j
      rw [hβim]
      fin_cases i <;> fin_cases j
      · exact hpi
      · exact hqi
      · exact add_mem (mul_mem hxi hpi) hri
      · exact add_mem (mul_mem hxi hqi) hti
    · rw [hβ]; simp only [mul_assoc, inv_mul_cancel, mul_one]

/-! ### The uniform bound on a translate of `unipotentGL2 · · s · C`

The measure of `unipotentGL2 '' (closure (adelicBox K)) · s · C` is bounded uniformly over the
centre-cut Siegel set: the conjugate `s⁻¹ · unipotentGL2 b · s` has entries bounded by
`1 + rB / c'` (the archimedean estimate) and integral (the finite estimate), so it lies in a fixed
compact `unimodularBall`, which absorbs the varying `C`. -/

section Image2Bound

variable (K : Type) [Field K] [NumberField K]

private theorem unipotentGL2_entry_eq {L : Type*} [NormedField L] (t : L) :
    ((unipotentGL2 t : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 = 1 ∧
    ((unipotentGL2 t : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 1 = t ∧
    ((unipotentGL2 t : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
    ((unipotentGL2 t : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 :=
  ⟨by rw [unipotentGL2_coe]; rfl, by rw [unipotentGL2_coe]; rfl,
    by rw [unipotentGL2_coe]; rfl, by rw [unipotentGL2_coe]; rfl⟩

private theorem conj_unipotentGL2_sub_one_apply {L : Type*} [NormedField L] (g : GL (Fin 2) L) (t : L)
    (i j : Fin 2) :
    ((g⁻¹ * unipotentGL2 t * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j
        - (1 : Matrix (Fin 2) (Fin 2) L) i j
      = t * ((g⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i 0
          * (g : Matrix (Fin 2) (Fin 2) L) 1 j := by
  obtain ⟨hN00, hN01, hN10, hN11⟩ := unipotentGL2_entry_eq (L := L) t
  have hval : ((g⁻¹ * unipotentGL2 t * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
      = ((g⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
          * ((unipotentGL2 t : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
          * (g : Matrix (Fin 2) (Fin 2) L) := by
    rw [Units.val_mul, Units.val_mul]
  have hone : (1 : Matrix (Fin 2) (Fin 2) L)
      = ((g⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) * (g : Matrix (Fin 2) (Fin 2) L) :=
    (Units.inv_mul g).symm
  rw [hval, hone]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, hN00, hN01, hN10, hN11]
  ring

private theorem norm_inv_apply_zero {L : Type*} [NormedField L] (g : GL (Fin 2) L)
    (i : Fin 2) :
    ‖((g⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i 0‖
      = ‖(g : Matrix (Fin 2) (Fin 2) L).det‖⁻¹ * ‖(g : Matrix (Fin 2) (Fin 2) L).adjugate i 0‖ := by
  have hcoe : ((g⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
      = ((g : Matrix (Fin 2) (Fin 2) L))⁻¹ := Matrix.coe_units_inv g
  rw [hcoe, Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, norm_smul, norm_inv]

private theorem mul_div_le_of_mul_le {T D x y R : ℝ} (hT : 0 ≤ T) (hD : 0 < D)
    (hxy : x * y ≤ R) : T * (D⁻¹ * x) * y ≤ T / (D / R) := by
  rw [div_div_eq_mul_div, le_div_iff₀ hD]
  calc T * (D⁻¹ * x) * y * D = T * (x * y) * (D⁻¹ * D) := by ring
    _ = T * (x * y) := by rw [inv_mul_cancel₀ hD.ne', mul_one]
    _ ≤ T * R := mul_le_mul_of_nonneg_left hxy hT

private theorem norm_conj_unipotentGL2_sub_one_apply_le {L : Type*} [NormedField L]
    (g : GL (Fin 2) L) (t : L) (i j : Fin 2) :
    ‖((g⁻¹ * unipotentGL2 t * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j
        - (1 : Matrix (Fin 2) (Fin 2) L) i j‖ ≤ ‖t‖ / localHeight g := by
  have hdet0 : (g : Matrix (Fin 2) (Fin 2) L).det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero g
  have hdetpos : 0 < ‖(g : Matrix (Fin 2) (Fin 2) L).det‖ := by
    rw [norm_pos_iff]
    exact hdet0
  have hA := sq_nonneg (‖(g : Matrix (Fin 2) (Fin 2) L) 1 0‖ - ‖(g : Matrix (Fin 2) (Fin 2) L) 1 1‖)
  have hB := sq_nonneg ‖(g : Matrix (Fin 2) (Fin 2) L) 1 0‖
  have hC := sq_nonneg ‖(g : Matrix (Fin 2) (Fin 2) L) 1 1‖
  rw [conj_unipotentGL2_sub_one_apply g t i j, norm_mul, norm_mul, norm_inv_apply_zero g i]
  refine mul_div_le_of_mul_le (norm_nonneg t) hdetpos ?_
  rw [Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j
  · show ‖(g : Matrix (Fin 2) (Fin 2) L) 1 1‖ * ‖(g : Matrix (Fin 2) (Fin 2) L) 1 0‖
      ≤ ‖(g : Matrix (Fin 2) (Fin 2) L) 1 0‖ ^ 2 + ‖(g : Matrix (Fin 2) (Fin 2) L) 1 1‖ ^ 2
    nlinarith [hA, hB, hC]
  · show ‖(g : Matrix (Fin 2) (Fin 2) L) 1 1‖ * ‖(g : Matrix (Fin 2) (Fin 2) L) 1 1‖
      ≤ ‖(g : Matrix (Fin 2) (Fin 2) L) 1 0‖ ^ 2 + ‖(g : Matrix (Fin 2) (Fin 2) L) 1 1‖ ^ 2
    nlinarith [hA, hB, hC]
  · show ‖-(g : Matrix (Fin 2) (Fin 2) L) 1 0‖ * ‖(g : Matrix (Fin 2) (Fin 2) L) 1 0‖
      ≤ ‖(g : Matrix (Fin 2) (Fin 2) L) 1 0‖ ^ 2 + ‖(g : Matrix (Fin 2) (Fin 2) L) 1 1‖ ^ 2
    rw [norm_neg]
    nlinarith [hA, hB, hC]
  · show ‖-(g : Matrix (Fin 2) (Fin 2) L) 1 0‖ * ‖(g : Matrix (Fin 2) (Fin 2) L) 1 1‖
      ≤ ‖(g : Matrix (Fin 2) (Fin 2) L) 1 0‖ ^ 2 + ‖(g : Matrix (Fin 2) (Fin 2) L) 1 1‖ ^ 2
    rw [norm_neg]
    nlinarith [hA, hB, hC]

private theorem norm_conj_unipotentGL2_apply_le {L : Type*} [NormedField L]
    (g : GL (Fin 2) L) (t : L) {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) (hcg : c ≤ localHeight g)
    (ht : ‖t‖ ≤ r) (i j : Fin 2) :
    ‖((g⁻¹ * unipotentGL2 t * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j‖ ≤ 1 + r / c := by
  have hsub := norm_conj_unipotentGL2_sub_one_apply_le g t i j
  have hone : ‖(1 : Matrix (Fin 2) (Fin 2) L) i j‖ ≤ 1 := by
    rw [Matrix.one_apply]
    split_ifs
    · exact norm_one.le
    · exact norm_zero.trans_le zero_le_one
  have hdiv : ‖t‖ / localHeight g ≤ r / c := div_le_div₀ hr ht hc hcg
  calc ‖((g⁻¹ * unipotentGL2 t * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j‖
      = ‖(((g⁻¹ * unipotentGL2 t * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j
          - (1 : Matrix (Fin 2) (Fin 2) L) i j) + (1 : Matrix (Fin 2) (Fin 2) L) i j‖ := by
        rw [sub_add_cancel]
    _ ≤ ‖((g⁻¹ * unipotentGL2 t * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j
          - (1 : Matrix (Fin 2) (Fin 2) L) i j‖ + ‖(1 : Matrix (Fin 2) (Fin 2) L) i j‖ :=
        norm_add_le _ _
    _ ≤ r / c + 1 := add_le_add (hsub.trans hdiv) hone
    _ = 1 + r / c := add_comm _ _

private theorem unipotentGL2_inv {R : Type*} [CommRing R] (x : R) :
    (unipotentGL2 x)⁻¹ = unipotentGL2 (-x) :=
  inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero])

private theorem archComponent_glArch_unipotentGL2 (w : InfinitePlace K) (b : AdeleRing (𝓞 K) K) :
    archComponent K w (glArch (𝓞 K) K (unipotentGL2 b)) = unipotentGL2 (b.1 w) := by
  ext i j
  rw [archComponent_apply, glArch_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> rfl

private theorem arch_entry_norm_le {c' u' d₁' d₂' rB : ℝ} (hc' : 0 < c') (hrB : 0 ≤ rB)
    {s : GL (Fin 2) (AdeleRing (𝓞 K) K)} (hs : s ∈ centreCutSiegelSet K c' u' d₁' d₂')
    {b : AdeleRing (𝓞 K) K} (hb : ∀ w : InfinitePlace K, ‖b.1 w‖ ≤ rB)
    (w : InfinitePlace K) (i j : Fin 2) :
    ‖(((s⁻¹ * unipotentGL2 b * s : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).1 w‖ ≤ 1 + rB / c' := by
  have hlh : c' ≤ localHeight (archComponent K w (glArch (𝓞 K) K s)) :=
    (mem_centreCutSiegelSet_iff.mp hs).2.1 w
  have hconj : archComponent K w (glArch (𝓞 K) K (s⁻¹ * unipotentGL2 b * s))
      = (archComponent K w (glArch (𝓞 K) K s))⁻¹ * unipotentGL2 (b.1 w)
          * archComponent K w (glArch (𝓞 K) K s) := by
    simp only [map_mul, map_inv, archComponent_glArch_unipotentGL2]
  have hentry : (((s⁻¹ * unipotentGL2 b * s : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).1 w
      = (archComponent K w (glArch (𝓞 K) K (s⁻¹ * unipotentGL2 b * s)) :
          Matrix (Fin 2) (Fin 2) w.Completion) i j := rfl
  rw [hentry, hconj]
  exact norm_conj_unipotentGL2_apply_le _ _ hc' hrB hlh (hb w) i j

private theorem glFin_unipotentGL2_mem {b : AdeleRing (𝓞 K) K}
    (hb : b.2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K) :
    glFin (𝓞 K) K (unipotentGL2 b) ∈ finiteIntegralGL2 (𝓞 K) K := by
  have hneg : (-b).2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
    rw [show (-b).2 = -b.2 from rfl, neg_eq_zero_sub]
    exact AdelicLevel.sub_mem_integralFiniteAdeles AdelicLevel.zero_mem_integralFiniteAdeles hb
  rw [mem_finiteIntegralGL2_iff, ← map_inv, unipotentGL2_inv]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [glFin_apply, unipotentGL2_coe]
    fin_cases i <;> fin_cases j
    · exact AdelicLevel.one_mem_integralFiniteAdeles
    · exact hb
    · exact AdelicLevel.zero_mem_integralFiniteAdeles
    · exact AdelicLevel.one_mem_integralFiniteAdeles
  · rw [glFin_apply, unipotentGL2_coe]
    fin_cases i <;> fin_cases j
    · exact AdelicLevel.one_mem_integralFiniteAdeles
    · exact hneg
    · exact AdelicLevel.zero_mem_integralFiniteAdeles
    · exact AdelicLevel.one_mem_integralFiniteAdeles

private theorem fin_entry_mem {s : GL (Fin 2) (AdeleRing (𝓞 K) K)}
    (hs : glFin (𝓞 K) K s ∈ finiteIntegralGL2 (𝓞 K) K) {b : AdeleRing (𝓞 K) K}
    (hb : b.2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K) (i j : Fin 2) :
    (((s⁻¹ * unipotentGL2 b * s : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2
      ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
  have hm : glFin (𝓞 K) K (s⁻¹ * unipotentGL2 b * s) ∈ finiteIntegralGL2 (𝓞 K) K := by
    rw [map_mul, map_mul, map_inv]
    exact mul_mem (mul_mem (inv_mem hs) (glFin_unipotentGL2_mem K hb)) hs
  have h := (mem_finiteIntegralGL2_iff.mp hm).1 i j
  rwa [glFin_apply] at h

private theorem isCompact_closure_adelicBox : IsCompact (closure (adelicBox K)) := by
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_adelicBox_subset K
  exact hC.closure_of_subset hsub

private theorem exists_arch_bound_of_mem_closure_adelicBox :
    ∃ rB : ℝ, 0 ≤ rB ∧ ∀ b ∈ closure (adelicBox K), ∀ w : InfinitePlace K, ‖b.1 w‖ ≤ rB := by
  have hcont : Continuous fun b : AdeleRing (𝓞 K) K => ∑ w : InfinitePlace K, ‖b.1 w‖ :=
    continuous_finsetSum _ fun w _ => ((continuous_archEval K w).comp continuous_fst).norm
  obtain ⟨r, hr⟩ := (isCompact_closure_adelicBox K).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max r 0, le_max_right _ _, fun b hb w => ?_⟩
  refine le_trans (Finset.single_le_sum (f := fun v : InfinitePlace K => ‖b.1 v‖)
    (fun v _ => norm_nonneg _) (Finset.mem_univ w)) ?_
  exact ((le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hr b hb))).trans (le_max_left _ _)

private theorem snd_mem_integralFiniteAdeles_of_mem_closure_adelicBox {b : AdeleRing (𝓞 K) K}
    (hb : b ∈ closure (adelicBox K)) : b.2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
  have hcl : IsClosed {y : AdeleRing (𝓞 K) K | y.2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K} :=
    (AdelicLevel.isClosed_integralFiniteAdeles (𝓞 K) K).preimage continuous_snd
  exact closure_minimal (fun y hy => hy.2) hcl hb

private def adeleBall (r : ℝ) : Set (AdeleRing (𝓞 K) K) :=
  {y | (∀ w : InfinitePlace K, ‖y.1 w‖ ≤ r) ∧ y.2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K}

private theorem mem_adeleBall {r : ℝ} {y : AdeleRing (𝓞 K) K} :
    y ∈ adeleBall K r ↔
      (∀ w : InfinitePlace K, ‖y.1 w‖ ≤ r) ∧ y.2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K :=
  Iff.rfl

private theorem isCompact_adeleBall (r : ℝ) : IsCompact (adeleBall K r) := by
  have : ∀ v : InfinitePlace K, ProperSpace v.Completion := fun v =>
    NumberField.AdelicBox.properSpace_completion K v
  have hS : IsCompact {x : InfiniteAdeleRing K | ∀ v, ‖x v‖ ≤ r} := by
    have : {x : InfiniteAdeleRing K | ∀ v, ‖x v‖ ≤ r} =
        Set.pi Set.univ fun v : InfinitePlace K => Metric.closedBall (0 : v.Completion) r := by
      ext x
      exact ⟨fun h v _ => mem_closedBall_zero_iff.mpr (h v),
        fun h v => mem_closedBall_zero_iff.mp (h v (Set.mem_univ v))⟩
    rw [this]
    exact isCompact_univ_pi fun v => isCompact_closedBall (0 : v.Completion) r
  have : IsCompact ({x : InfiniteAdeleRing K | ∀ v, ‖x v‖ ≤ r} ×ˢ
      AdelicLevel.integralFiniteAdeles (𝓞 K) K) :=
    hS.prod (AdelicLevel.isCompact_integralFiniteAdeles (𝓞 K) K)
  exact this

private def matBall (r : ℝ) : Set (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) :=
  Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 => adeleBall K r

private def unimodularBall (r : ℝ) : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)) :=
  Units.embedProduct (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) ⁻¹'
    (matBall K r ×ˢ (MulOpposite.op '' matBall K r))

private theorem isCompact_unimodularBall (r : ℝ) : IsCompact (unimodularBall K r) := by
  have hM : IsCompact (matBall K r) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_adeleBall K r
  exact Units.isClosedEmbedding_embedProduct.isCompact_preimage
    (hM.prod (hM.image MulOpposite.continuous_op))

private theorem mem_unimodularBall {r : ℝ} {m : GL (Fin 2) (AdeleRing (𝓞 K) K)}
    (h₁ : ∀ i j, (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j ∈ adeleBall K r)
    (h₂ : ∀ i j, ((m⁻¹ : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j ∈ adeleBall K r) :
    m ∈ unimodularBall K r := by
  rw [unimodularBall, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod]
  exact ⟨Set.mem_univ_pi.mpr fun i => Set.mem_univ_pi.mpr fun j => h₁ i j,
    ⟨((m⁻¹ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)),
      Set.mem_univ_pi.mpr fun i => Set.mem_univ_pi.mpr fun j => h₂ i j, rfl⟩⟩

private theorem conj_mem_unimodularBall {c' u' d₁' d₂' rB : ℝ} (hc' : 0 < c') (hrB : 0 ≤ rB)
    {s : GL (Fin 2) (AdeleRing (𝓞 K) K)} (hs : s ∈ centreCutSiegelSet K c' u' d₁' d₂')
    {b : AdeleRing (𝓞 K) K} (hb₁ : ∀ w : InfinitePlace K, ‖b.1 w‖ ≤ rB)
    (hb₂ : b.2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K) :
    s⁻¹ * unipotentGL2 b * s ∈ unimodularBall K (1 + rB / c') := by
  have hs₁ : glFin (𝓞 K) K s ∈ finiteIntegralGL2 (𝓞 K) K := (mem_centreCutSiegelSet_iff.mp hs).1
  have hnb₁ : ∀ w : InfinitePlace K, ‖(-b).1 w‖ ≤ rB := fun w => by
    rw [show (-b).1 w = -(b.1 w) from rfl, norm_neg]
    exact hb₁ w
  have hnb₂ : (-b).2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
    rw [show (-b).2 = -b.2 from rfl, neg_eq_zero_sub]
    exact AdelicLevel.sub_mem_integralFiniteAdeles AdelicLevel.zero_mem_integralFiniteAdeles hb₂
  have hinv : (s⁻¹ * unipotentGL2 b * s)⁻¹ = s⁻¹ * unipotentGL2 (-b) * s := by
    simp only [mul_inv_rev, inv_inv, unipotentGL2_inv, mul_assoc]
  refine mem_unimodularBall K (fun i j => (mem_adeleBall K).mpr ⟨fun w => ?_, ?_⟩)
    (fun i j => (mem_adeleBall K).mpr ?_)
  · exact arch_entry_norm_le K hc' hrB hs hb₁ w i j
  · exact fin_entry_mem K hs₁ hb₂ i j
  · rw [hinv]
    exact ⟨fun w => arch_entry_norm_le K hc' hrB hs hnb₁ w i j, fin_entry_mem K hs₁ hnb₂ i j⟩

private theorem exists_absorbing_compact_image {c' u' d₁' d₂' : ℝ} (hc' : 0 < c')
    {C : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hC : IsCompact C) :
    ∃ E : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)), IsCompact E ∧
      ∀ s ∈ centreCutSiegelSet K c' u' d₁' d₂',
        Set.image2 (fun (t : AdeleRing (𝓞 K) K) (c : GL (Fin 2) (AdeleRing (𝓞 K) K)) =>
            unipotentGL2 t * s * c) (closure (adelicBox K)) C
          ⊆ (fun y => s * y) '' E := by
  obtain ⟨rB, hrB, hbox⟩ := exists_arch_bound_of_mem_closure_adelicBox K
  refine ⟨Set.image2 (fun m c => m * c) (unimodularBall K (1 + rB / c')) C, ?_, fun s hs x hx => ?_⟩
  · rw [← Set.image_prod]
    exact ((isCompact_unimodularBall K _).prod hC).image (continuous_fst.mul continuous_snd)
  · obtain ⟨b, hb, c, hc, rfl⟩ := Set.mem_image2.mp hx
    refine ⟨s⁻¹ * unipotentGL2 b * s * c, Set.mem_image2_of_mem
      (conj_mem_unimodularBall K hc' hrB hs (hbox b hb) (snd_mem_integralFiniteAdeles_of_mem_closure_adelicBox K hb)) hc, ?_⟩
    show s * (s⁻¹ * unipotentGL2 b * s * c) = unipotentGL2 b * s * c
    simp only [← mul_assoc, mul_inv_cancel, one_mul]

private theorem exists_haar_image2_le (c' u' d₁' d₂' : ℝ) (hc' : 0 < c')
    {C : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hC : IsCompact C) :
    ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ s ∈ centreCutSiegelSet K c' u' d₁' d₂',
      adelicGLHaar (Fin 2) (𝓞 K) K
          (Set.image2 (fun (t : AdeleRing (𝓞 K) K) (c : GL (Fin 2) (AdeleRing (𝓞 K) K)) =>
            unipotentGL2 t * s * c) (closure (adelicBox K)) C)
        ≤ ENNReal.ofReal M₀ := by
  let : MeasurableSpace (GL (Fin 2) (AdeleRing (𝓞 K) K)) := glBorel (Fin 2) (𝓞 K) K
  have : BorelSpace (GL (Fin 2) (AdeleRing (𝓞 K) K)) := borelSpace_glBorel (Fin 2) (𝓞 K) K
  have : (adelicGLHaar (Fin 2) (𝓞 K) K).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  obtain ⟨E, hE, hsub⟩ := exists_absorbing_compact_image K (u' := u') (d₁' := d₁') (d₂' := d₂') hc' hC
  have hEtop : adelicGLHaar (Fin 2) (𝓞 K) K E ≠ ⊤ := hE.measure_lt_top.ne
  refine ⟨(adelicGLHaar (Fin 2) (𝓞 K) K E).toReal, ENNReal.toReal_nonneg, fun s hs => ?_⟩
  rw [ENNReal.ofReal_toReal hEtop]
  calc adelicGLHaar (Fin 2) (𝓞 K) K
        (Set.image2 (fun (t : AdeleRing (𝓞 K) K) (c : GL (Fin 2) (AdeleRing (𝓞 K) K)) =>
          unipotentGL2 t * s * c) (closure (adelicBox K)) C)
      ≤ adelicGLHaar (Fin 2) (𝓞 K) K ((fun y => s * y) '' E) := measure_mono (hsub s hs)
    _ = adelicGLHaar (Fin 2) (𝓞 K) K E := by
        rw [Set.image_mul_left, measure_preimage_mul]

end Image2Bound

theorem exists_forall_adelicGLHaar_image2_unipotentGL2_mul_mul_le_of_isCompact (K : Type) [Field K] [NumberField K]
    (c' u' d₁' d₂' : ℝ) (hc' : 0 < c')
    {C : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hC : IsCompact C) :
    ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ s ∈ centreCutSiegelSet K c' u' d₁' d₂',
      adelicGLHaar (Fin 2) (𝓞 K) K
          (Set.image2 (fun (t : AdeleRing (𝓞 K) K) (c : GL (Fin 2) (AdeleRing (𝓞 K) K)) =>
            unipotentGL2 t * s * c) (closure (adelicBox K)) C)
        ≤ ENNReal.ofReal M₀ :=
  exists_haar_image2_le K c' u' d₁' d₂' hc' hC


section

variable (K : Type) [Field K] [NumberField K]

theorem diagOne_mul_unipotentGL2_mul_inv (τ : (AdeleRing (𝓞 K) K)ˣ) (x : AdeleRing (𝓞 K) K) :
    diagOne τ * unipotentGL2 x * (diagOne τ)⁻¹ = unipotentGL2 ((τ : AdeleRing (𝓞 K) K) * x) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [← map_inv]
  change (Matrix.diagonal ![((τ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K), 1] * !![1, x; 0, 1] *
      Matrix.diagonal ![((τ⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K), 1]) i j =
    !![1, (τ : AdeleRing (𝓞 K) K) * x; 0, 1] i j
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_mul, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp

theorem conj_mem_rationalCentreUnipotent (τ u : (AdeleRing (𝓞 K) K)ˣ) (y : AdelicGL2 (𝓞 K) K)
    (hy : y ∈ rationalCentreUnipotent K) :
    (diagOne τ * centralScalar (𝓞 K) K u) * y * (diagOne τ * centralScalar (𝓞 K) K u)⁻¹ ∈ rationalCentreUnipotent K := by
  set c := diagOne τ * centralScalar (𝓞 K) K u with hc
  rw [rationalCentreUnipotent, Subgroup.sup_eq_closure] at hy ⊢
  refine Subgroup.closure_induction (p := fun y _ => c * y * c⁻¹ ∈
      Subgroup.closure ((rationalCentre K : Set (AdelicGL2 (𝓞 K) K)) ∪ (adelicUnipotent K : Set (AdelicGL2 (𝓞 K) K))))
    ?_ ?_ ?_ ?_ hy
  · intro y hy
    apply Subgroup.subset_closure
    rcases hy with hy | hy
    ·
      left
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hy
      have hcomm : c * (((globalPoints (𝓞 K) K).comp (Units.map (Matrix.scalar (Fin 2) :
          K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom)) a) = (((globalPoints (𝓞 K) K).comp
          (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom)) a) * c := by
        refine Units.ext ?_
        change (c : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) *
            (Matrix.scalar (Fin 2) (a : K)).map (algebraMap K (AdeleRing (𝓞 K) K)) =
          (Matrix.scalar (Fin 2) (a : K)).map (algebraMap K (AdeleRing (𝓞 K) K)) * (c : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
        have : (Matrix.scalar (Fin 2) (a : K)).map (algebraMap K (AdeleRing (𝓞 K) K)) =
            Matrix.scalar (Fin 2) (algebraMap K (AdeleRing (𝓞 K) K) (a : K)) := by
          ext i j
          rw [Matrix.map_apply, Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
          split_ifs <;> simp
        rw [this]
        exact ((Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq).symm
      rw [hcomm, mul_inv_cancel_right]
      exact MonoidHom.mem_range.mpr ⟨a, rfl⟩
    ·
      right
      obtain ⟨z, rfl⟩ := MonoidHom.mem_range.mp hy
      change c * unipotentGL2 (Multiplicative.toAdd z) * c⁻¹ ∈ adelicUnipotent K
      have hcn : c * unipotentGL2 (Multiplicative.toAdd z) * c⁻¹ =
          diagOne τ * unipotentGL2 (Multiplicative.toAdd z) * (diagOne τ)⁻¹ := by
        rw [hc, mul_inv_rev,
          show diagOne τ * centralScalar (𝓞 K) K u * unipotentGL2 (Multiplicative.toAdd z) *
              ((centralScalar (𝓞 K) K u)⁻¹ * (diagOne τ)⁻¹) =
            diagOne τ * (centralScalar (𝓞 K) K u * unipotentGL2 (Multiplicative.toAdd z) *
              (centralScalar (𝓞 K) K u)⁻¹) * (diagOne τ)⁻¹ by group,
          centralScalar_mul_comm u, mul_inv_cancel_right]
      rw [hcn, diagOne_mul_unipotentGL2_mul_inv]
      exact MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd ((τ : AdeleRing (𝓞 K) K) * Multiplicative.toAdd z), rfl⟩
  · rw [mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
  · intro x y _ _ hx hy
    change c * (x * y) * c⁻¹ ∈ _
    have : c * (x * y) * c⁻¹ = (c * x * c⁻¹) * (c * y * c⁻¹) := by group
    rw [this]; exact Subgroup.mul_mem _ hx hy
  · intro x _ hx
    change c * x⁻¹ * c⁻¹ ∈ _
    have : c * x⁻¹ * c⁻¹ = (c * x * c⁻¹)⁻¹ := by group
    rw [this]; exact Subgroup.inv_mem _ hx

theorem mem_rationalCentreUnipotent_iff_heckeGen_mul_centralScalar_conj_mem
    (v : HeightOneSpectrum (𝓞 K)) (u : (AdeleRing (𝓞 K) K)ˣ) (y : AdelicGL2 (𝓞 K) K) :
    y ∈ rationalCentreUnipotent K ↔
      (heckeGen (𝓞 K) K v * centralScalar (𝓞 K) K u) * y * (heckeGen (𝓞 K) K v * centralScalar (𝓞 K) K u)⁻¹ ∈
        rationalCentreUnipotent K := by

  set τ : (AdeleRing (𝓞 K) K)ˣ := Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v (uniformizerUnit K v)) with hτ
  have hgen : heckeGen (𝓞 K) K v = diagOne τ := rfl
  rw [hgen]
  set c := diagOne τ * centralScalar (𝓞 K) K u with hc
  constructor
  · exact conj_mem_rationalCentreUnipotent K τ u y
  · intro h
    have h' := conj_mem_rationalCentreUnipotent K τ⁻¹ u⁻¹ _ h
    have hinv : diagOne τ⁻¹ * centralScalar (𝓞 K) K u⁻¹ = c⁻¹ := by
      rw [map_inv, map_inv, ← mul_inv_rev, centralScalar_mul_comm u (diagOne τ), hc]
    rw [hinv, show c⁻¹ * (c * y * c⁻¹) * c⁻¹⁻¹ = y by group] at h'
    exact h'


end

end AutomorphicForm
