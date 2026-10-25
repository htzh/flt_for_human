/-
The Hecke-row commutativity on `J_H(M)`: the `X_H` half — the engine, and one headline.

`ModularCurve.heckeOperatorHAlong_comm` says that the `ℓ`- and `ℓ'`-Hecke correspondences
commute on `J_H(M)`; its `X₁` twin (`ModularCurve.heckeOperatorOneBar_comm`) is in
`ModularCurve/X1/HeckeCommute.lean`, which imports this module and shares the group-agnostic
prelude below rather than copying it.  The statement is **unconditional**: every prime `ℓ`,
including `ℓ ∣ M` (the `U_ℓ` case, where the `β` leg falls back to `α`) and `ℓ = ℓ'`
(trivial); no coprimality or distinctness is assumed.

The development is the pin's: the two covers `M ↦ Mℓ` and `M ↦ Mℓ'` are compared inside the
compositum level `Mℓℓ'`, where the roof square commutes (`hsq`), the push–pull exchange
(`AlgebraicCurve.Divisor.pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong`)
turns the square into an identity of correspondences, and the degree multiplicativity
(`relfinrank_xHHeckeCompositum_eq_mul`) makes the common leg cancel (`heckeDiv_heckeDiv`).
`Nice` packages what the square needs of an intermediate field, and the `HeckeInputs*Along`
predicates make both operators the zero map when their inputs fail, so commutativity is total.

**The `H = ⊥` reduction does not reach this layer.**  The port proves the *degree* twins
(`HeckeCompositum.lean`, `X1/HeckeDegree.lean`) by specialising `H := ⊥`, and that works
because those statements mention only `finrankAlong`/`relfinrank` of a map.  Here the
statements quantify over the maps themselves (`Divisor.correspondence (heckeBetaHBar …) …`,
`FundamentalIdentityAlong L (heckeBetaHBar …) hβ`), and `xHFunctionField M ⊥` is only
*propositionally* equal to `x1FunctionField M` (`CohCarrier.GammaH_bot` is a `le_antisymm`),
so `heckeAlphaHBar L M ⊥ ℓ = heckeAlphaOneBar L M ℓ` is not even a well-typed equation.  The
`X_H` block is therefore the engine and the `X₁` block is its transcription at the pin's `Γ₁`
vocabulary (`X1HeckeCommute`, `private`); the only shared text is the group-agnostic prelude
at the top (`XHHeckeCommute.Generic`).

The engine is public because the next consumer on this row data — the diamond/Tate Hecke
algebra — states its roof on the same fields.  Nothing here is re-proved from the ground: the
`Place` fibre-sum identity, the four `Divisor` transport lemmas, the compositum degree, the
`JOneES` transcendental generator, `qExpand`/`laurentBaseChange`, `coeffMap_qExpand` /
`coeffEmb_qExpand` / `laurentBaseChange_mono` / `qExpand_mem_laurentBaseChange`,
`fieldRange_val_comp_inclusion` / `finrankAlong_inclusion`, the `Γ₀` antitone and the
`X₁`/`X_H` row data (`heckeAlpha*Bar`, `heckeBeta*Bar`, `HeckeInputs*Along`,
`heckeOperator*Along`) are imported, not restated.

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_heckeOperatorHAlong_comm.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_heckeOperatorHAlong_comm.lean

  spec-pin: Theorems/Thm_ModularCurve_heckeOperatorHAlong_comm.lean
  spec-pin: P2M/Sol/S_ModularCurve_heckeOperatorHAlong_comm.lean
-/

import FLTForHuman.AlgebraicCurve.ResidueTheorem.KFamily
import FLTForHuman.AlgebraicCurve.WeilExchange.DivisorExchange
import FLTForHuman.AlgebraicCurve.WeilExchange.Transport
import FLTForHuman.ModularCurve.Defs.Laurent
import FLTForHuman.ModularCurve.HeckeCompositum
import FLTForHuman.ModularCurve.X1.FunctionFieldBaseChange
import FLTForHuman.ModularCurve.X1.HeckeModule
import FLTForHuman.ModularCurve.X1.HeckeOperator
import FLTForHuman.ModularCurve.X1.Inputs
import FLTForHuman.ModularCurve.X1.QExpandStretch
import FLTForHuman.ModularCurve.XH.FunctionField
import FLTForHuman.ModularCurve.XH.HeckeDegree
import FLTForHuman.ModularCurve.XH.HeckeInputs
import FLTForHuman.ModularCurve.XH.HeckeOperator
import FLTForHuman.ModularForms.Defs.GammaH
import FLTForHuman.NumberTheory.ModularForms.CongruenceSubgroupOrder


set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open scoped IntermediateField MatrixGroups

namespace ModularCurve

open AlgebraicCurve CohCarrier CongruenceSubgroup HahnSeries IntermediateField

open HeckeDegree


/- The `Algebra K ↥A` goals whose carrier is a *variable* intermediate field (`Nice.*`, the
prelude's `qExpTo`/`fieldRange_val_comp_qExpTo`) are the other half of the `algebra'` bill: no
`algebra_*` brick below can name them, and `IntermediateField.algebra'`'s conclusion is
`Algebra ?R ?S` with both arguments metavariables, so it is a candidate for *every* `Algebra` goal
and re-derives `SMul`/`Mul`/`Distrib`/`Semiring` from scratch (~250 ms) at each occurrence.  One
keyed instance (`Algebra K ↥?A`, key `Subtype`) answers all of them, in both halves. -/
private instance algebra_subtype {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : IntermediateField K L) : Algebra K ↥A := inferInstance

/-- The `[Semiring ↥A]` argument of every such goal is a search of its own (~25 ms: the derivation
runs `SubfieldClass`/`SubringClass`/`Subring` down to the ambient ring) and it is paid once per
*occurrence* of a carrier, so it gets the same treatment. -/
private instance semiring_subtype {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : IntermediateField K L) : Semiring ↥A := inferInstance

/-- `Algebra ℚ (LaurentSeries ℚ)` is a search of its own (~68 ms: `DivisionRing.toRatAlgebra` over
the Hahn-series fraction field) and the four `intFormRatiosC ℚ _` proofs (`qExpand_KK_subset`,
`qExpand_KT_subset`, `betaHDefined_input`) ask for it several times each, in both halves. -/
private instance algebra_laurent_rat : Algebra ℚ (LaurentSeries ℚ) := inferInstance

/-! ## The group-agnostic prelude (`XHHeckeCommute.Generic`)

The declarations whose statements never mention `Γ_H` or `Γ₁`: they are the same text in the
two `S_` files (and are stated identically in both), so they are written once here and both
halves of the module use them.  Five are the `Along`/`Divisor` lemmas —
`finiteDimensional_adjoin_of_le`, `finrankAlong_pos_of_finiteAlong`,
`pushforwardAlong_pullbackAlong`, `correspondence_comp_eq_smul`, `eq_of_zsmul_eq_zsmul`.  The
rest are the `q ↦ q ^ ℓ` substitution `qExpAlgHom` (the pin's name for the port's `qExpAlg`),
the two level `NeZero` instances and the characteristic-zero pair, the two `Transcendental`
transport lemmas, and the `qExpTo` leg of the substitution.

The pin's remaining group-agnostic lemmas already have a public home and are **imported**:
`correspondence_congr` (`AlgebraicCurve/WeilExchange/Transport.lean`),
`finiteAlong_of_transcendental` / `isIntegral_of_finiteAlong` (`ModularCurve/X1/Inputs.lean`),
`fieldRange_val_comp_inclusion` / `finrankAlong_inclusion` (`ModularCurve/XH/HeckeDegree.lean`),
and `coeffMap_qExpand` / `coeffEmb_qExpand` / `laurentBaseChange_mono` /
`qExpand_mem_laurentBaseChange` (`ModularCurve/Defs/Laurent.lean`). -/

namespace XHHeckeCommute

namespace Generic

section QExp

variable (L : Type*) [Field L] [Algebra ℚ L] (ℓ : ℕ) [NeZero ℓ]

/-- The pin's name for the `q ↦ q ^ ℓ` substitution as an `L`-algebra endomorphism:
it is the port's `ModularCurve.qExpAlg`, kept at the pin's name because `QQ_eq_map` states it. -/
def qExpAlgHom : LaurentSeries L →ₐ[L] LaurentSeries L := qExpAlg L ℓ

end QExp

section Level

variable (M : ℕ) [NeZero M] (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']

scoped instance neZero_mul_level : NeZero (M * ℓ) := ⟨mul_ne_zero (NeZero.ne M) (NeZero.ne ℓ)⟩
scoped instance neZero_top_level : NeZero (M * ℓ * ℓ') :=
  ⟨mul_ne_zero (mul_ne_zero (NeZero.ne M) (NeZero.ne ℓ)) (NeZero.ne ℓ')⟩

end Level

section Characteristic

variable (L : Type*) [Field L] [Algebra ℚ L]

theorem charZero_base : CharZero L :=
  charZero_of_injective_algebraMap (algebraMap ℚ L).injective

scoped instance charZero_sub (A : IntermediateField L (LaurentSeries L)) : CharZero A := by
  haveI : CharZero L := charZero_base L
  exact charZero_of_injective_algebraMap (algebraMap L A).injective

theorem transcendental_coe_iff {A : IntermediateField L (LaurentSeries L)} (x : A) :
    Transcendental L (x : LaurentSeries L) ↔ Transcendental L x :=
  transcendental_algebraMap_iff (R := L) (A := LaurentSeries L)
    (algebraMap A (LaurentSeries L)).injective

theorem transcendental_qExpand {x : LaurentSeries L} (hx : Transcendental L x) (ℓ : ℕ) [NeZero ℓ] :
    Transcendental L (qExpand L ℓ x) := fun h =>
  hx ((isAlgebraic_algHom_iff (qExpAlgHom L ℓ) (qExpand_injective (R := L) (N := ℓ))).mp h)

end Characteristic

section Legs

variable {L : Type*} [Field L] [Algebra ℚ L] (ℓ : ℕ) [NeZero ℓ]

def qExpTo (A B : IntermediateField L (LaurentSeries L))
    (h : qExpand L ℓ '' (A : Set (LaurentSeries L)) ⊆ B) : A →ₐ[L] B where
  toFun x := ⟨qExpand L ℓ x, h ⟨x, x.2, rfl⟩⟩
  map_one' := Subtype.ext (map_one (qExpand L ℓ))
  map_mul' _ _ := Subtype.ext (map_mul (qExpand L ℓ) _ _)
  map_zero' := Subtype.ext (map_zero (qExpand L ℓ))
  map_add' _ _ := Subtype.ext (map_add (qExpand L ℓ) _ _)
  commutes' a := Subtype.ext <| by
    show qExpand L ℓ (algebraMap L (LaurentSeries L) a) = algebraMap L (LaurentSeries L) a
    rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero]

@[scoped simp]
theorem coe_qExpTo {A B : IntermediateField L (LaurentSeries L)}
    (h : qExpand L ℓ '' (A : Set (LaurentSeries L)) ⊆ B) (x : A) :
    (qExpTo ℓ A B h x : LaurentSeries L) = qExpand L ℓ x := rfl

theorem fieldRange_val_comp_qExpTo {A B : IntermediateField L (LaurentSeries L)}
    (h : qExpand L ℓ '' (A : Set (LaurentSeries L)) ⊆ B) :
    (B.val.comp (qExpTo ℓ A B h)).fieldRange
      = IntermediateField.adjoin L (qExpand L ℓ '' (A : Set (LaurentSeries L))) := by
  have hmap : IntermediateField.adjoin L (qExpand L ℓ '' (A : Set (LaurentSeries L)))
      = A.map (qExpAlgHom L ℓ) := by
    rw [← IntermediateField.adjoin_self L A, IntermediateField.adjoin_map, IntermediateField.adjoin_self]
    rfl
  rw [hmap]
  ext x
  rw [AlgHom.mem_fieldRange, IntermediateField.mem_map]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, a.2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩

end Legs


section Exchange

variable {L E : Type*} [Field L] [Field E] [Algebra L E]
theorem finiteDimensional_adjoin_of_le {A B : IntermediateField L E} (h : A ≤ B) {x : E}
    (hxA : x ∈ A) (hfin : FiniteDimensional L⟮(⟨x, h hxA⟩ : B)⟯ B) :
    FiniteDimensional L⟮(⟨x, hxA⟩ : A)⟯ A := by
  haveI := hfin
  set xB : B := ⟨x, h hxA⟩ with hxB
  set xA : A := ⟨x, hxA⟩ with hxAd
  set F' : IntermediateField L B := L⟮xB⟯ with hF'
  set A' : IntermediateField L B := IntermediateField.restrict h with hA'
  have hle : F' ≤ A' := by
    rw [hF', IntermediateField.adjoin_simple_le_iff, hA', IntermediateField.mem_restrict]
    exact hxA
  set K' : IntermediateField F' B := IntermediateField.extendScalars hle with hK'
  haveI : FiniteDimensional F' K' := IntermediateField.finiteDimensional_left K'

  have hmemK' : ∀ z : B, z ∈ K' ↔ (z : E) ∈ A := by
    intro z
    rw [hK', IntermediateField.mem_extendScalars, hA', IntermediateField.mem_restrict]
  let eK : K' ≃+* A :=
    { toFun := fun z => ⟨(z.1 : E), (hmemK' z.1).mp z.2⟩
      invFun := fun a => ⟨⟨(a : E), h a.2⟩, (hmemK' ⟨(a : E), h a.2⟩).mpr a.2⟩
      left_inv := fun z => rfl
      right_inv := fun a => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }

  set φ : A →ₐ[L] B := IntermediateField.inclusion h with hφ
  have hmap : (L⟮xA⟯).map φ = F' := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  let e : L⟮xA⟯ ≃ₐ[L] F' := ((L⟮xA⟯).equivMap φ).trans (IntermediateField.equivOfEq hmap)
  have he : ∀ w : L⟮xA⟯, (((e w : F') : B) : E) = ((w : A) : E) := fun w => rfl
  refine Module.Finite.of_equiv_equiv (A₁ := F') (B₁ := K') (A₂ := L⟮xA⟯) (B₂ := A)
    e.symm.toRingEquiv eK ?_
  refine RingHom.ext fun z => ?_
  obtain ⟨w, rfl⟩ := e.surjective z
  apply Subtype.ext
  simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply]
  rw [show e.symm.toRingEquiv (e w) = w from e.symm_apply_apply w]
  show ((algebraMap F' K' (e w) : K').1 : E) = ((algebraMap L⟮xA⟯ A w : A) : E)
  exact he w
end Exchange
section Along

variable {L F F' : Type*} [Field L] [Field F] [Field F'] [Algebra L F] [Algebra L F']
theorem finrankAlong_pos_of_finiteAlong (φ : F →ₐ[L] F') (h : AlgebraicCurve.FiniteAlong L φ) :
    0 < AlgebraicCurve.finrankAlong L φ := by
  letI := AlgebraicCurve.algebraAlong φ
  haveI : Module.Finite F F' := h
  exact Module.finrank_pos
end Along
section PushPull

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
theorem pushforwardAlong_pullbackAlong (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    [HasPrincipalDivisors K F'] (hfin : FiniteAlong K φ) (hsep : SeparableAlong K φ)
    (D : Divisor K F) :
    Divisor.pushforwardAlong φ hφ (Divisor.pullbackAlong φ hφ D)
      = (finrankAlong K φ : ℤ) • D := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add v n D _ _ ih =>
    rw [map_add, map_add, smul_add, ih, Divisor.pullbackAlong_single, map_sum]
    congr 1
    have hrestr : ∀ W ∈ Place.fiberAlong φ hφ v, W.restrictAlong φ hφ = v := fun W hW =>
      Place.mem_fiberAlong.mp hW
    calc ∑ W ∈ Place.fiberAlong φ hφ v,
          Divisor.pushforwardAlong φ hφ (Finsupp.single W (n * (W.ramificationIndexAlong φ : ℤ)))
        = ∑ W ∈ Place.fiberAlong φ hφ v, Finsupp.single v
            (n * ((W.ramificationIndexAlong φ : ℤ) * (W.inertiaDegAlong φ hφ : ℤ))) := by
          refine Finset.sum_congr rfl fun W hW => ?_
          rw [Divisor.pushforwardAlong_single, hrestr W hW, mul_assoc]
      _ = Finsupp.single v (n * ∑ W ∈ Place.fiberAlong φ hφ v,
            ((W.ramificationIndexAlong φ : ℤ) * (W.inertiaDegAlong φ hφ : ℤ))) := by
          rw [Finset.mul_sum, Finsupp.single_finsetSum]
      _ = (finrankAlong K φ : ℤ) • Finsupp.single v n := by
          rw [Place.sum_ramificationIndexAlong_mul_inertiaDegAlong φ hφ hfin hsep v,
            Finsupp.smul_single, smul_eq_mul, mul_comm]
end PushPull
section Nested

variable {K F E₁ E₂ : Type*} [Field K] [Field F] [Field E₁] [Field E₂]
  [Algebra K F] [Algebra K E₁] [Algebra K E₂]

theorem correspondence_comp_eq_smul [HasPrincipalDivisors K E₁] [HasPrincipalDivisors K E₂]
    (p i : F →ₐ[K] E₁) (j : E₁ →ₐ[K] E₂)
    (hp : p.toRingHom.IsIntegral) (hi : i.toRingHom.IsIntegral) (hj : j.toRingHom.IsIntegral)
    (hjp : (j.comp p).toRingHom.IsIntegral) (hji : (j.comp i).toRingHom.IsIntegral)
    (hjfin : FiniteAlong K j) (hjsep : SeparableAlong K j) (D : Divisor K F) :
    Divisor.correspondence (j.comp p) (j.comp i) hjp hji D
      = (finrankAlong K j : ℤ) • Divisor.correspondence p i hp hi D := by
  rw [Divisor.correspondence_apply, Divisor.correspondence_apply,
    ← Divisor.pullbackAlong_pullbackAlong p j hp hj hjp,
    ← Divisor.pushforwardAlong_pushforwardAlong i j hi hj hji,
    pushforwardAlong_pullbackAlong j hj hjfin hjsep, map_zsmul]
theorem eq_of_zsmul_eq_zsmul {n : ℤ} (hn : n ≠ 0) {D D' : Divisor K F}
    (h : n • D = n • D') : D = D' := by
  refine Finsupp.ext fun W => ?_
  have hW : n • D W = n • D' W := by
    have := congrArg (fun D : Divisor K F => D W) h
    rwa [Finsupp.smul_apply, Finsupp.smul_apply] at this
  rw [Int.zsmul_eq_mul, Int.zsmul_eq_mul] at hW
  exact mul_left_cancel₀ hn hW
end Nested

/-- Swapping the transcendental generator of a finite field extension.  The
finite-dimensionality is an **explicit hypothesis**: the port spells the function field two
ways (`KT …` and its unfolding over `qExpFunctionFieldC`), the instance key does not see
through the `def`, and an instance binder leaves the search to burn its whole budget. -/
theorem finiteDimensional_adjoin_of_transcendental' {L E : Type*} [Field L] [Field E]
    [Algebra ℚ L] [Algebra L E]
    {x : E} (hx : Transcendental L x) (hfin : FiniteDimensional L⟮x⟯ E) {y : E}
    (hy : Transcendental L y) : FiniteDimensional L⟮y⟯ E := by
  haveI := hfin
  exact AlgebraicCurve.finiteDimensional_adjoin_of_transcendental x hy

end Generic

open Generic

open scoped Generic

section Groups

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ)

theorem T_mem_GammaH : ModularGroup.T ∈ CohCarrier.GammaH M H :=
  translation_mem_GammaH M H

theorem T_mem_GammaH_inf_Gamma0 (t : ℕ) : ModularGroup.T ∈ CohCarrier.GammaH M H ⊓ Gamma0 t := by
  have hT0 : ModularGroup.T ∈ Gamma0 t := by
    rw [Gamma0_mem]
    simp [ModularGroup.T]
  exact Subgroup.mem_inf.mpr ⟨T_mem_GammaH M H, hT0⟩

scoped instance finiteIndex_GammaH [NeZero M] : (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)

scoped instance finiteIndex_GammaH_inf_Gamma0 [NeZero M] (t : ℕ) [NeZero t] :
    (CohCarrier.GammaH M H ⊓ Gamma0 t).FiniteIndex := by
  infer_instance

theorem cocycle_inf {s ℓ t : ℕ} [NeZero ℓ] (hs : M ∣ s) (ht : t = s * ℓ) :
    ∀ γ ∈ CohCarrier.GammaH M H ⊓ Gamma0 t, ∃ γ₁ ∈ CohCarrier.GammaH M H ⊓ Gamma0 s,
      γ₁ 0 0 = γ 0 0 ∧ γ₁ 0 1 = (ℓ : ℤ) * γ 0 1 ∧ (ℓ : ℤ) * γ₁ 1 0 = γ 1 0 ∧ γ₁ 1 1 = γ 1 1 := by
  intro γ hγ
  obtain ⟨hγH, hγ0⟩ := Subgroup.mem_inf.mp hγ
  obtain ⟨hγ0M, hunit⟩ := CohCarrier.mem_GammaH_iff.mp hγH
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe; rwa [Matrix.det_fin_two] at this
  have htc : ((t : ℕ) : ℤ) ∣ γ 1 0 := by
    have := Gamma0_mem.mp hγ0; rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  obtain ⟨c', hc'⟩ := htc
  rw [ht, Nat.cast_mul] at hc'
  have hdet' : Matrix.det !![(γ 0 0 : ℤ), (ℓ : ℤ) * γ 0 1; (s : ℤ) * c', γ 1 1] = 1 := by
    rw [Matrix.det_fin_two_of]; linear_combination hdet + (γ 0 1 : ℤ) * hc'
  obtain ⟨m, hm⟩ := hs
  have h0M : (⟨_, hdet'⟩ : SL(2, ℤ)) ∈ Gamma0 M := by
    apply Gamma0_mem.mpr
    show (((s : ℤ) * c' : ℤ) : ZMod M) = 0
    rw [hm]; push_cast; rw [ZMod.natCast_self, zero_mul, zero_mul]
  refine ⟨⟨_, hdet'⟩, ?_, ?_, ?_, ?_, ?_⟩
  · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · refine CohCarrier.mem_GammaH_iff.mpr ⟨h0M, ?_⟩
      have : CohCarrier.gamma0Units M ⟨_, h0M⟩ = CohCarrier.gamma0Units M ⟨γ, hγ0M⟩ := by
        apply Units.ext
        rw [CohCarrier.val_gamma0Units, CohCarrier.val_gamma0Units]
        rfl
      rw [this]
      exact hunit
    · apply Gamma0_mem.mpr
      show (((s : ℤ) * c' : ℤ) : ZMod s) = 0
      push_cast; rw [ZMod.natCast_self, zero_mul]
  · rfl
  · rfl
  · show (ℓ : ℤ) * ((s : ℤ) * c') = γ 1 0
    linear_combination -hc'
  · rfl

theorem cocycle_one (ℓ : ℕ) [NeZero ℓ] : ∀ γ ∈ CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ), ∃ γ₁ ∈ CohCarrier.GammaH M H,
    γ₁ 0 0 = γ 0 0 ∧ γ₁ 0 1 = (ℓ : ℤ) * γ 0 1 ∧ (ℓ : ℤ) * γ₁ 1 0 = γ 1 0 ∧ γ₁ 1 1 = γ 1 1 := by
  intro γ hγ
  obtain ⟨γ₁, hγ₁, h⟩ := cocycle_inf M H (s := M) (ℓ := ℓ) (t := M * ℓ) dvd_rfl rfl γ hγ
  exact ⟨γ₁, (Subgroup.mem_inf.mp hγ₁).1, h⟩

end Groups

section Fields

variable (L : Type*) [Field L] [Algebra ℚ L] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

abbrev KK : IntermediateField L (LaurentSeries L) := laurentBaseChange L (xHFunctionField M H)

abbrev KT (t : ℕ) : IntermediateField L (LaurentSeries L) :=
  laurentBaseChange L (xHTopFunctionFieldC ℚ M H t)

theorem KK_le_KT (t : ℕ) : KK L M H ≤ KT L M H t :=
  laurentBaseChange_mono L (xHFunctionFieldC_le_top ℚ M H t)

theorem KT_mono {s t : ℕ} (h : s ∣ t) : KT L M H s ≤ KT L M H t :=
  laurentBaseChange_mono L (qExpFunctionFieldC_mono ℚ (inf_le_inf_left _ (Gamma0_le_of_dvd h)))

theorem qExpand_KK_subset (ℓ : ℕ) [NeZero ℓ] :
    qExpand L ℓ '' (KK L M H : Set (LaurentSeries L)) ⊆ KT L M H (M * ℓ) := by
  rintro _ ⟨x, hx, rfl⟩
  refine qExpand_mem_laurentBaseChange ℓ (fun y hy => ?_) hx
  have hsub := ModularCurve.qExpand_image_intFormRatiosC_subset ℚ (T_mem_GammaH M H) ℓ
    (cocycle_one M H ℓ)
  have hmap : (IntermediateField.adjoin ℚ (intFormRatiosC ℚ (CohCarrier.GammaH M H))).map (qExpandₐ ℓ)
      ≤ IntermediateField.adjoin ℚ (intFormRatiosC ℚ (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ))) := by
    rw [IntermediateField.adjoin_map]
    exact IntermediateField.adjoin.mono ℚ _ _ hsub
  exact hmap ⟨y, hy, rfl⟩

theorem qExpand_KT_subset {s ℓ t : ℕ} [NeZero s] [NeZero ℓ] (hs : M ∣ s) (ht : t = s * ℓ) :
    qExpand L ℓ '' (KT L M H s : Set (LaurentSeries L)) ⊆ KT L M H t := by
  rintro _ ⟨x, hx, rfl⟩
  refine qExpand_mem_laurentBaseChange ℓ (fun y hy => ?_) hx
  have hsub := ModularCurve.qExpand_image_intFormRatiosC_subset ℚ (T_mem_GammaH_inf_Gamma0 M H s) ℓ
    (cocycle_inf M H hs ht)
  have hmap : (IntermediateField.adjoin ℚ (intFormRatiosC ℚ (CohCarrier.GammaH M H ⊓ Gamma0 s))).map (qExpandₐ ℓ)
      ≤ IntermediateField.adjoin ℚ (intFormRatiosC ℚ (CohCarrier.GammaH M H ⊓ Gamma0 t)) := by
    rw [IntermediateField.adjoin_map]
    exact IntermediateField.adjoin.mono ℚ _ _ hsub
  exact hmap ⟨y, hy, rfl⟩

theorem betaHDefined_input (ℓ : ℕ) [NeZero ℓ] : HeckeBetaHDefined M H ℓ := by
  intro y hy
  have hsub := ModularCurve.qExpand_image_intFormRatiosC_subset ℚ (T_mem_GammaH M H) ℓ (cocycle_one M H ℓ)
  have hy' : y ∈ IntermediateField.adjoin ℚ (intFormRatiosC ℚ (CohCarrier.GammaH M H)) := hy
  have hmap : (IntermediateField.adjoin ℚ (intFormRatiosC ℚ (CohCarrier.GammaH M H))).map (qExpandₐ ℓ)
      ≤ IntermediateField.adjoin ℚ (intFormRatiosC ℚ (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ))) := by
    rw [IntermediateField.adjoin_map]
    exact IntermediateField.adjoin.mono ℚ _ _ hsub
  exact hmap ⟨y, hy', rfl⟩

theorem exists_transcendental_KK : ∃ x₀ : LaurentSeries L, x₀ ∈ KK L M H ∧ Transcendental L x₀ := by
  obtain ⟨x, hx, -⟩ :=
    ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange L (CohCarrier.GammaH M H)
      (T_mem_GammaH M H)
  refine ⟨x, x.2, ?_⟩
  exact (transcendental_algebraMap_iff (R := L) (A := LaurentSeries L)
    (algebraMap (KK L M H) (LaurentSeries L)).injective).mpr hx

theorem finiteDimensional_KT (t : ℕ) [NeZero t] {y : KT L M H t} (hy : Transcendental L y) :
    FiniteDimensional L⟮y⟯ (KT L M H t) := by
  obtain ⟨x, hx, hfin⟩ :=
    ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange L
      (CohCarrier.GammaH M H ⊓ Gamma0 t) (T_mem_GammaH_inf_Gamma0 M H t)
  exact XHHeckeCommute.Generic.finiteDimensional_adjoin_of_transcendental' (x := x) hx hfin hy

end Fields

variable (L : Type*) [Field L] [Algebra ℚ L] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']

abbrev QQ : IntermediateField L (LaurentSeries L) :=
  IntermediateField.adjoin L (qExpand L ℓ '' (KK L M H : Set (LaurentSeries L)))

abbrev roof : IntermediateField L (LaurentSeries L) :=
  KT L M H (M * ℓ) ⊔ IntermediateField.adjoin L (qExpand L ℓ '' (KT L M H (M * ℓ') : Set (LaurentSeries L)))

abbrev BB : IntermediateField L (LaurentSeries L) := KT L M H (M * ℓ * ℓ')

-- The `Algebra L ↥A` instance is derived through an unkeyed candidate (`algebra'`) whose
-- `≟` check has to unfold the field expression (`roof` through `⊔`/`adjoin`/`KT`, `KT` through
-- the `def xHTopFunctionFieldC`).  The trace shows the same goal re-searched at every occurrence
-- (~5 per proof, ~350 ms each).  Naming each one once makes every later occurrence an
-- assumption lookup.  `private`, so nothing here reaches the public API.
private instance algebra_KK : Algebra L ↥(KK L M H) := inferInstance

private instance algebra_KT : Algebra L ↥(KT L M H (M * ℓ)) := inferInstance

private instance algebra_KT' : Algebra L ↥(KT L M H (M * ℓ')) := inferInstance

theorem KT_le_roof : KT L M H (M * ℓ) ≤ roof L M H ℓ ℓ' := le_sup_left

theorem qExpand_KT_subset_roof :
    qExpand L ℓ '' (KT L M H (M * ℓ') : Set (LaurentSeries L)) ⊆ roof L M H ℓ ℓ' :=
  (IntermediateField.subset_adjoin L _).trans (SetLike.coe_subset_coe.mpr le_sup_right)

private instance algebra_QQ : Algebra L ↥(QQ L M H ℓ) := inferInstance

private instance algebra_roof : Algebra L ↥(roof L M H ℓ ℓ') := inferInstance

private instance algebra_BB : Algebra L ↥(BB L M H ℓ ℓ') := inferInstance

theorem KK_le_roof : KK L M H ≤ roof L M H ℓ ℓ' := (KK_le_KT L M H _).trans (KT_le_roof L M H ℓ ℓ')

theorem QQ_le_KT : QQ L M H ℓ ≤ KT L M H (M * ℓ) :=
  IntermediateField.adjoin_le_iff.mpr (qExpand_KK_subset L M H ℓ)

theorem QQ_le_roof : QQ L M H ℓ ≤ roof L M H ℓ ℓ' := (QQ_le_KT L M H ℓ).trans (KT_le_roof L M H ℓ ℓ')

theorem roof_le_BB : roof L M H ℓ ℓ' ≤ BB L M H ℓ ℓ' := by
  refine sup_le (KT_mono L M H ⟨ℓ', rfl⟩) (IntermediateField.adjoin_le_iff.mpr ?_)
  exact qExpand_KT_subset L M H (s := M * ℓ') (ℓ := ℓ) (t := M * ℓ * ℓ') ⟨ℓ', rfl⟩ (by ring)

theorem KK_le_BB : KK L M H ≤ BB L M H ℓ ℓ' := (KK_le_roof L M H ℓ ℓ').trans (roof_le_BB L M H ℓ ℓ')

structure Nice (A : IntermediateField L (LaurentSeries L)) : Prop where
  le : A ≤ BB L M H ℓ ℓ'
  tr : ∃ y ∈ A, Transcendental L y

variable {L M H ℓ ℓ'}

theorem Nice.klShape {A : IntermediateField L (LaurentSeries L)} (hA : Nice L M H ℓ ℓ' A)
    {y : LaurentSeries L} (hyA : y ∈ A) (hy : Transcendental L y) :
    FiniteDimensional L⟮(⟨y, hyA⟩ : A)⟯ A := by
  have hyB : y ∈ BB L M H ℓ ℓ' := hA.le hyA
  have hfin : FiniteDimensional L⟮(⟨y, hyB⟩ : BB L M H ℓ ℓ')⟯ (BB L M H ℓ ℓ') :=
    finiteDimensional_KT L M H (M * ℓ * ℓ') ((transcendental_coe_iff L (A := BB L M H ℓ ℓ') ⟨y, hyB⟩).mp hy)
  exact finiteDimensional_adjoin_of_le hA.le hyA hfin

theorem Nice.hasPrincipalDivisors {A : IntermediateField L (LaurentSeries L)} (hA : Nice L M H ℓ ℓ' A) :
    HasPrincipalDivisors L A := by
  haveI : CharZero L := charZero_base L
  obtain ⟨y, hyA, hy⟩ := hA.tr
  haveI := hA.klShape hyA hy
  exact AlgebraicCurve.hasPrincipalDivisors_of_transcendental L (⟨y, hyA⟩ : A)
    ((transcendental_coe_iff L (A := A) ⟨y, hyA⟩).mp hy)

theorem Nice.finiteAlong {A A' : IntermediateField L (LaurentSeries L)} (hA : Nice L M H ℓ ℓ' A)
    (hA' : Nice L M H ℓ ℓ' A') (φ : A →ₐ[L] A') : FiniteAlong L φ := by
  obtain ⟨y, hyA, hy⟩ := hA.tr
  obtain ⟨y', hyA', hy'⟩ := hA'.tr
  haveI := hA'.klShape hyA' hy'
  exact finiteAlong_of_transcendental φ ((transcendental_coe_iff L (A := A) ⟨y, hyA⟩).mp hy)
    ((transcendental_coe_iff L (A := A') ⟨y', hyA'⟩).mp hy')

theorem Nice.isIntegral {A A' : IntermediateField L (LaurentSeries L)} (hA : Nice L M H ℓ ℓ' A)
    (hA' : Nice L M H ℓ ℓ' A') (φ : A →ₐ[L] A') : φ.toRingHom.IsIntegral :=
  isIntegral_of_finiteAlong φ (hA.finiteAlong hA' φ)

theorem Nice.separableAlong {A A' : IntermediateField L (LaurentSeries L)} (hA : Nice L M H ℓ ℓ' A)
    (hA' : Nice L M H ℓ ℓ' A') (φ : A →ₐ[L] A') : SeparableAlong L φ :=
  AlgebraicCurve.separableAlong_of_charZero φ (hA.isIntegral hA' φ)

theorem Nice.finrankAlong_ne_zero {A A' : IntermediateField L (LaurentSeries L)} (hA : Nice L M H ℓ ℓ' A)
    (hA' : Nice L M H ℓ ℓ' A') (φ : A →ₐ[L] A') : finrankAlong L φ ≠ 0 :=
  (finrankAlong_pos_of_finiteAlong φ (hA.finiteAlong hA' φ)).ne'

theorem Nice.relfinrank_ne_zero {A A' : IntermediateField L (LaurentSeries L)} (hA : Nice L M H ℓ ℓ' A)
    (hA' : Nice L M H ℓ ℓ' A') (h : A ≤ A') : IntermediateField.relfinrank A A' ≠ 0 := by
  rw [← finrankAlong_inclusion h]
  exact hA.finrankAlong_ne_zero hA' _

theorem Nice.mono {A A' : IntermediateField L (LaurentSeries L)} (hA : Nice L M H ℓ ℓ' A)
    (h : A ≤ A') (h' : A' ≤ BB L M H ℓ ℓ') : Nice L M H ℓ ℓ' A' :=
  ⟨h', let ⟨y, hyA, hy⟩ := hA.tr; ⟨y, h hyA, hy⟩⟩

variable (L M H ℓ ℓ')

theorem nice_KK : Nice L M H ℓ ℓ' (KK L M H) :=
  ⟨KK_le_BB L M H ℓ ℓ', exists_transcendental_KK L M H⟩

theorem nice_KT : Nice L M H ℓ ℓ' (KT L M H (M * ℓ)) :=
  (nice_KK L M H ℓ ℓ').mono (KK_le_KT L M H _) ((KT_le_roof L M H ℓ ℓ').trans (roof_le_BB L M H ℓ ℓ'))

theorem nice_KT' : Nice L M H ℓ ℓ' (KT L M H (M * ℓ')) :=
  (nice_KK L M H ℓ ℓ').mono (KK_le_KT L M H _) (KT_mono L M H ⟨ℓ, by ring⟩)

theorem nice_QQ : Nice L M H ℓ ℓ' (QQ L M H ℓ) := by
  refine ⟨(QQ_le_roof L M H ℓ ℓ').trans (roof_le_BB L M H ℓ ℓ'), ?_⟩
  obtain ⟨y, hy, htr⟩ := exists_transcendental_KK L M H
  exact ⟨qExpand L ℓ y, IntermediateField.subset_adjoin L _ ⟨y, hy, rfl⟩, transcendental_qExpand L htr ℓ⟩

theorem nice_roof : Nice L M H ℓ ℓ' (roof L M H ℓ ℓ') :=
  (nice_KK L M H ℓ ℓ').mono (KK_le_roof L M H ℓ ℓ') (roof_le_BB L M H ℓ ℓ')

theorem nice_BB : Nice L M H ℓ ℓ' (BB L M H ℓ ℓ') :=
  (nice_KK L M H ℓ ℓ').mono (KK_le_BB L M H ℓ ℓ') le_rfl

theorem nice_symm {A : IntermediateField L (LaurentSeries L)} (hA : Nice L M H ℓ' ℓ A) : Nice L M H ℓ ℓ' A := by
  refine ⟨hA.le.trans ?_, hA.tr⟩
  exact KT_mono L M H ⟨1, by ring⟩

abbrev legU : KT L M H (M * ℓ) →ₐ[L] roof L M H ℓ ℓ' := IntermediateField.inclusion (KT_le_roof L M H ℓ ℓ')

abbrev legU' : KT L M H (M * ℓ') →ₐ[L] roof L M H ℓ ℓ' :=
  qExpTo ℓ (KT L M H (M * ℓ')) (roof L M H ℓ ℓ') (qExpand_KT_subset_roof L M H ℓ ℓ')

theorem coe_legU (y : KT L M H (M * ℓ)) : (legU L M H ℓ ℓ' y : LaurentSeries L) = y :=
  IntermediateField.coe_inclusion _ y

theorem coe_legU' (y : KT L M H (M * ℓ')) : (legU' L M H ℓ ℓ' y : LaurentSeries L) = qExpand L ℓ y :=
  coe_qExpTo ℓ _ y

theorem mem_algebraAdjoin_iff (x : LaurentSeries L) :
    x ∈ Algebra.adjoin L ((KT L M H (M * ℓ) : Set (LaurentSeries L)) ∪
        qExpand L ℓ '' (KT L M H (M * ℓ') : Set (LaurentSeries L))) ↔
      x ∈ Algebra.adjoin (KT L M H (M * ℓ)) (qExpand L ℓ '' (KT L M H (M * ℓ') : Set (LaurentSeries L))) := by
  constructor
  · intro hx
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
        rcases hy with hy | hy
        · exact Subalgebra.algebraMap_mem
            (Algebra.adjoin (KT L M H (M * ℓ)) (qExpand L ℓ '' (KT L M H (M * ℓ') : Set (LaurentSeries L))))
            (⟨y, hy⟩ : KT L M H (M * ℓ))
        · exact Algebra.subset_adjoin hy
    | algebraMap r =>
        have : algebraMap L (LaurentSeries L) r
            = algebraMap (KT L M H (M * ℓ)) (LaurentSeries L) (algebraMap L (KT L M H (M * ℓ)) r) :=
          (IsScalarTower.algebraMap_apply L (KT L M H (M * ℓ)) (LaurentSeries L) r)
        rw [this]
        exact Subalgebra.algebraMap_mem _ _
    | add y z _ _ hy hz => exact add_mem hy hz
    | mul y z _ _ hy hz => exact mul_mem hy hz
  · intro hx
    induction hx using Algebra.adjoin_induction with
    | mem y hy => exact Algebra.subset_adjoin (Or.inr hy)
    | algebraMap r => exact Algebra.subset_adjoin (Or.inl r.2)
    | add y z _ _ hy hz => exact add_mem hy hz
    | mul y z _ _ hy hz => exact mul_mem hy hz

theorem isAlgebraic_of_mem_BB {x : LaurentSeries L} (hx : x ∈ BB L M H ℓ ℓ') :
    IsAlgebraic (KT L M H (M * ℓ)) x := by
  have hle : KT L M H (M * ℓ) ≤ BB L M H ℓ ℓ' := (KT_le_roof L M H ℓ ℓ').trans (roof_le_BB L M H ℓ ℓ')
  let φ : KT L M H (M * ℓ) →ₐ[L] BB L M H ℓ ℓ' := IntermediateField.inclusion hle
  have hint : φ.toRingHom.IsIntegral := (nice_KT L M H ℓ ℓ').isIntegral (nice_BB L M H ℓ ℓ') φ
  obtain ⟨p, hp, hpx⟩ := hint ⟨x, hx⟩
  refine IsIntegral.isAlgebraic ⟨p, hp, ?_⟩
  have h := Polynomial.hom_eval₂ p φ.toRingHom (BB L M H ℓ ℓ').val.toRingHom ⟨x, hx⟩
  rw [hpx, map_zero] at h
  have hcomp : (BB L M H ℓ ℓ').val.toRingHom.comp φ.toRingHom
      = algebraMap (KT L M H (M * ℓ)) (LaurentSeries L) := RingHom.ext fun c => rfl
  rw [hcomp] at h
  exact h.symm

theorem inv_mem_algebraAdjoin {x : LaurentSeries L}
    (hx : x ∈ Algebra.adjoin L ((KT L M H (M * ℓ) : Set (LaurentSeries L)) ∪
        qExpand L ℓ '' (KT L M H (M * ℓ') : Set (LaurentSeries L)))) :
    x⁻¹ ∈ Algebra.adjoin L ((KT L M H (M * ℓ) : Set (LaurentSeries L)) ∪
        qExpand L ℓ '' (KT L M H (M * ℓ') : Set (LaurentSeries L))) := by
  have hx' := (mem_algebraAdjoin_iff L M H ℓ ℓ' x).mp hx
  have hxB : x ∈ BB L M H ℓ ℓ' := by
    have hle : Algebra.adjoin L ((KT L M H (M * ℓ) : Set (LaurentSeries L)) ∪
        qExpand L ℓ '' (KT L M H (M * ℓ') : Set (LaurentSeries L))) ≤ (roof L M H ℓ ℓ').toSubalgebra :=
      Algebra.adjoin_le (Set.union_subset (KT_le_roof L M H ℓ ℓ') (qExpand_KT_subset_roof L M H ℓ ℓ'))
    exact roof_le_BB L M H ℓ ℓ' (hle hx)
  have halg := isAlgebraic_of_mem_BB L M H ℓ ℓ' hxB
  have h := Subalgebra.inv_mem_of_algebraic
    (Algebra.adjoin (KT L M H (M * ℓ)) (qExpand L ℓ '' (KT L M H (M * ℓ') : Set (LaurentSeries L))))
    (x := ⟨x, hx'⟩) halg
  exact (mem_algebraAdjoin_iff L M H ℓ ℓ' x⁻¹).mpr h

theorem roof_toSubalgebra :
    (roof L M H ℓ ℓ').toSubalgebra = Algebra.adjoin L ((KT L M H (M * ℓ) : Set (LaurentSeries L)) ∪
        qExpand L ℓ '' (KT L M H (M * ℓ') : Set (LaurentSeries L))) := by
  have h : roof L M H ℓ ℓ' = IntermediateField.adjoin L ((KT L M H (M * ℓ) : Set (LaurentSeries L)) ∪
      qExpand L ℓ '' (KT L M H (M * ℓ') : Set (LaurentSeries L))) := by
    rw [IntermediateField.adjoin_union, IntermediateField.adjoin_self]
  rw [h]
  exact IntermediateField.adjoin_eq_algebra_adjoin L _ (fun x hx => inv_mem_algebraAdjoin L M H ℓ ℓ' hx)

theorem hgen : Algebra.adjoin L (Set.range (legU' L M H ℓ ℓ') ∪ Set.range (legU L M H ℓ ℓ')) = ⊤ := by
  have hle : Algebra.adjoin L ((KT L M H (M * ℓ) : Set (LaurentSeries L)) ∪
        qExpand L ℓ '' (KT L M H (M * ℓ') : Set (LaurentSeries L)))
      ≤ (Algebra.adjoin L (Set.range (legU' L M H ℓ ℓ') ∪ Set.range (legU L M H ℓ ℓ'))).map
          (roof L M H ℓ ℓ').val := by
    refine Algebra.adjoin_le ?_
    rintro y (hy | ⟨a, ha, rfl⟩)
    · exact ⟨legU L M H ℓ ℓ' ⟨y, hy⟩, Algebra.subset_adjoin (Or.inr ⟨_, rfl⟩), rfl⟩
    · exact ⟨legU' L M H ℓ ℓ' ⟨a, ha⟩, Algebra.subset_adjoin (Or.inl ⟨_, rfl⟩), rfl⟩
  refine eq_top_iff.mpr fun z _ => ?_
  have hz : (z : LaurentSeries L) ∈ (roof L M H ℓ ℓ').toSubalgebra := z.2
  rw [roof_toSubalgebra] at hz
  obtain ⟨w, hw, hwz⟩ := Subalgebra.mem_map.mp (hle hz)
  have hwz' : w = z := Subtype.ext hwz
  exact hwz' ▸ hw

theorem QQ_eq_map : QQ L M H ℓ = (KK L M H).map (qExpAlgHom L ℓ) := by
  have h := IntermediateField.adjoin_map L ((KK L M H : Set (LaurentSeries L))) (qExpAlgHom L ℓ)
  rw [IntermediateField.adjoin_self] at h
  exact h.symm

theorem finrankAlong_beta (h0 : HeckeBetaHDefined M H ℓ) :
    finrankAlong L (heckeBetaHBar L M H ℓ) = IntermediateField.relfinrank (QQ L M H ℓ) (KT L M H (M * ℓ)) := by
  refine (AlgebraicCurve.finrankAlong_eq_relfinrank_fieldRange (KK L M H) (KT L M H (M * ℓ))
    (heckeBetaHBar L M H ℓ)).trans ?_
  congr 1
  rw [QQ_eq_map]
  ext x
  rw [AlgHom.mem_fieldRange, IntermediateField.mem_map]
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨a, a.2, ?_⟩
    show qExpand L ℓ a = (heckeBetaHBar L M H ℓ a : LaurentSeries L)
    rw [coe_heckeBetaHBar M H ℓ h0]
  · rintro ⟨a, ha, rfl⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    show ((heckeBetaHBar L M H ℓ ⟨a, ha⟩ : KT L M H (M * ℓ)) : LaurentSeries L) = qExpand L ℓ a
    rw [coe_heckeBetaHBar M H ℓ h0]

theorem finrankAlong_alpha :
    finrankAlong L (heckeAlphaHBar L M H ℓ') = IntermediateField.relfinrank (KK L M H) (KT L M H (M * ℓ')) :=
  finrankAlong_inclusion (KK_le_KT L M H _)

theorem coe_legU'_alpha (a : KK L M H) :
    (((legU' L M H ℓ ℓ').comp (heckeAlphaHBar L M H ℓ')) a : LaurentSeries L) = qExpand L ℓ a := by
  rw [AlgHom.comp_apply, coe_legU', coe_heckeAlphaHBar]

theorem finrankAlong_diag :
    finrankAlong L ((legU' L M H ℓ ℓ').comp (heckeAlphaHBar L M H ℓ'))
      = IntermediateField.relfinrank (QQ L M H ℓ) (roof L M H ℓ ℓ') := by
  refine (AlgebraicCurve.finrankAlong_eq_relfinrank_fieldRange (KK L M H) (roof L M H ℓ ℓ')
    ((legU' L M H ℓ ℓ').comp (heckeAlphaHBar L M H ℓ'))).trans ?_
  congr 1
  rw [QQ_eq_map]
  ext x
  rw [AlgHom.mem_fieldRange, IntermediateField.mem_map]
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨a, a.2, ?_⟩
    show qExpand L ℓ a = (((legU' L M H ℓ ℓ').comp (heckeAlphaHBar L M H ℓ')) a : LaurentSeries L)
    rw [coe_legU'_alpha]
  · rintro ⟨a, ha, rfl⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    show (((legU' L M H ℓ ℓ').comp (heckeAlphaHBar L M H ℓ')) ⟨a, ha⟩ : LaurentSeries L) = qExpand L ℓ a
    rw [coe_legU'_alpha]

theorem hLD (hcop : Nat.Coprime ℓ ℓ') (h0 : HeckeBetaHDefined M H ℓ) :
    finrankAlong L ((legU' L M H ℓ ℓ').comp (heckeAlphaHBar L M H ℓ'))
      = finrankAlong L (heckeAlphaHBar L M H ℓ') * finrankAlong L (heckeBetaHBar L M H ℓ) := by
  rw [finrankAlong_diag, finrankAlong_alpha, finrankAlong_beta L M H ℓ h0]
  exact ModularCurve.relfinrank_xHHeckeCompositum_eq_mul L M H ℓ ℓ' hcop

theorem relfinrank_KK_roof (hcop : Nat.Coprime ℓ ℓ') :
    IntermediateField.relfinrank (KK L M H) (roof L M H ℓ ℓ')
      = IntermediateField.relfinrank (KK L M H) (KT L M H (M * ℓ))
        * IntermediateField.relfinrank (KK L M H) (KT L M H (M * ℓ')) := by
  have t1 := IntermediateField.relfinrank_mul_relfinrank (KK_le_KT L M H (M * ℓ)) (KT_le_roof L M H ℓ ℓ')
  have t2 := IntermediateField.relfinrank_mul_relfinrank (QQ_le_KT L M H ℓ) (KT_le_roof L M H ℓ ℓ')
  have hLD := ModularCurve.relfinrank_xHHeckeCompositum_eq_mul L M H ℓ ℓ' hcop
  have hne : IntermediateField.relfinrank (QQ L M H ℓ) (KT L M H (M * ℓ)) ≠ 0 :=
    (nice_QQ L M H ℓ ℓ').relfinrank_ne_zero (nice_KT L M H ℓ ℓ') (QQ_le_KT L M H ℓ)
  have key : IntermediateField.relfinrank (KT L M H (M * ℓ)) (roof L M H ℓ ℓ')
      = IntermediateField.relfinrank (KK L M H) (KT L M H (M * ℓ')) := by
    apply mul_left_cancel₀ hne
    rw [t2, hLD, mul_comm]
  rw [← t1, key]

theorem hsq (h0 : HeckeBetaHDefined M H ℓ) :
    (legU L M H ℓ ℓ').comp (heckeBetaHBar L M H ℓ) = (legU' L M H ℓ ℓ').comp (heckeAlphaHBar L M H ℓ') := by
  refine AlgHom.ext fun x => Subtype.ext ?_
  rw [AlgHom.comp_apply, AlgHom.comp_apply, coe_legU, coe_legU',
    coe_heckeBetaHBar M H ℓ h0, coe_heckeAlphaHBar]

theorem exchange (hcop : Nat.Coprime ℓ ℓ') (h0 : HeckeBetaHDefined M H ℓ)
    [HasPrincipalDivisors L (KT L M H (M * ℓ))] [HasPrincipalDivisors L (roof L M H ℓ ℓ')]
    (hβ : (heckeBetaHBar L M H ℓ).toRingHom.IsIntegral)
    (hα' : (heckeAlphaHBar L M H ℓ').toRingHom.IsIntegral)
    (hu : (legU L M H ℓ ℓ').toRingHom.IsIntegral) (hu' : (legU' L M H ℓ ℓ').toRingHom.IsIntegral)
    (D : Divisor L (KT L M H (M * ℓ'))) :
    Divisor.pullbackAlong (heckeBetaHBar L M H ℓ) hβ (Divisor.pushforwardAlong (heckeAlphaHBar L M H ℓ') hα' D)
      = Divisor.pushforwardAlong (legU L M H ℓ ℓ') hu (Divisor.pullbackAlong (legU' L M H ℓ ℓ') hu' D) := by
  have hfin : FiniteAlong L ((legU' L M H ℓ ℓ').comp (heckeAlphaHBar L M H ℓ')) :=
    (nice_KK L M H ℓ ℓ').finiteAlong (nice_roof L M H ℓ ℓ') _
  have hsep : SeparableAlong L ((legU' L M H ℓ ℓ').comp (heckeAlphaHBar L M H ℓ')) :=
    (nice_KK L M H ℓ ℓ').separableAlong (nice_roof L M H ℓ ℓ') _
  exact Divisor.pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong
    (heckeAlphaHBar L M H ℓ') (heckeBetaHBar L M H ℓ) (legU' L M H ℓ ℓ') (legU L M H ℓ ℓ')
    hα' hβ hu' hu (hsq L M H ℓ ℓ' h0) hfin hsep (hgen L M H ℓ ℓ') (hLD L M H ℓ ℓ' hcop h0) D

abbrev legP : KK L M H →ₐ[L] roof L M H ℓ ℓ' := (legU' L M H ℓ ℓ').comp (heckeBetaHBar L M H ℓ')

abbrev legI : KK L M H →ₐ[L] roof L M H ℓ ℓ' := (legU L M H ℓ ℓ').comp (heckeAlphaHBar L M H ℓ)

theorem coe_legP (h0' : HeckeBetaHDefined M H ℓ') (x : KK L M H) :
    (legP L M H ℓ ℓ' x : LaurentSeries L) = qExpand L (ℓ * ℓ') x := by
  rw [AlgHom.comp_apply, coe_legU', coe_heckeBetaHBar M H ℓ' h0', qExpand_qExpand]

theorem coe_legI (x : KK L M H) : (legI L M H ℓ ℓ' x : LaurentSeries L) = x := by
  rw [AlgHom.comp_apply, coe_legU, coe_heckeAlphaHBar]

theorem heckeDiv_heckeDiv (hcop : Nat.Coprime ℓ ℓ') (h0 : HeckeBetaHDefined M H ℓ)
    [HasPrincipalDivisors L (KT L M H (M * ℓ))] [HasPrincipalDivisors L (KT L M H (M * ℓ'))]
    [HasPrincipalDivisors L (roof L M H ℓ ℓ')]
    (hα : (heckeAlphaHBar L M H ℓ).toRingHom.IsIntegral) (hβ : (heckeBetaHBar L M H ℓ).toRingHom.IsIntegral)
    (hα' : (heckeAlphaHBar L M H ℓ').toRingHom.IsIntegral) (hβ' : (heckeBetaHBar L M H ℓ').toRingHom.IsIntegral)
    (hP : (legP L M H ℓ ℓ').toRingHom.IsIntegral) (hI : (legI L M H ℓ ℓ').toRingHom.IsIntegral)
    (D : Divisor L (KK L M H)) :
    Divisor.correspondence (heckeBetaHBar L M H ℓ) (heckeAlphaHBar L M H ℓ) hβ hα
        (Divisor.correspondence (heckeBetaHBar L M H ℓ') (heckeAlphaHBar L M H ℓ') hβ' hα' D)
      = Divisor.correspondence (legP L M H ℓ ℓ') (legI L M H ℓ ℓ') hP hI D := by
  have hu : (legU L M H ℓ ℓ').toRingHom.IsIntegral := (nice_KT L M H ℓ ℓ').isIntegral (nice_roof L M H ℓ ℓ') _
  have hu' : (legU' L M H ℓ ℓ').toRingHom.IsIntegral := (nice_KT' L M H ℓ ℓ').isIntegral (nice_roof L M H ℓ ℓ') _
  rw [Divisor.correspondence_apply, Divisor.correspondence_apply, Divisor.correspondence_apply,
    exchange L M H ℓ ℓ' hcop h0 hβ hα' hu hu',
    Divisor.pushforwardAlong_pushforwardAlong (heckeAlphaHBar L M H ℓ) (legU L M H ℓ ℓ') hα hu hI,
    Divisor.pullbackAlong_pullbackAlong (heckeBetaHBar L M H ℓ') (legU' L M H ℓ ℓ') hβ' hu' hP]

variable (L : Type*) [Field L] [Algebra ℚ L] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']

abbrev RR : IntermediateField L (LaurentSeries L) := roof L M H ℓ ℓ' ⊔ roof L M H ℓ' ℓ

theorem roof_le_RR : roof L M H ℓ ℓ' ≤ RR L M H ℓ ℓ' := le_sup_left

theorem roof'_le_RR : roof L M H ℓ' ℓ ≤ RR L M H ℓ ℓ' := le_sup_right

abbrev legJ : roof L M H ℓ ℓ' →ₐ[L] RR L M H ℓ ℓ' := IntermediateField.inclusion (roof_le_RR L M H ℓ ℓ')

abbrev legJ' : roof L M H ℓ' ℓ →ₐ[L] RR L M H ℓ ℓ' := IntermediateField.inclusion (roof'_le_RR L M H ℓ ℓ')

theorem coe_legJ (y : roof L M H ℓ ℓ') : (legJ L M H ℓ ℓ' y : LaurentSeries L) = y :=
  IntermediateField.coe_inclusion _ y

theorem coe_legJ' (y : roof L M H ℓ' ℓ) : (legJ' L M H ℓ ℓ' y : LaurentSeries L) = y :=
  IntermediateField.coe_inclusion _ y

theorem nice_RR : Nice L M H ℓ ℓ' (RR L M H ℓ ℓ') :=
  (nice_roof L M H ℓ ℓ').mono (roof_le_RR L M H ℓ ℓ')
    (sup_le (roof_le_BB L M H ℓ ℓ') ((nice_symm L M H ℓ ℓ' (nice_roof L M H ℓ' ℓ)).le))

theorem heckeDiv_comm (hcop : Nat.Coprime ℓ ℓ')
    [HasPrincipalDivisors L (KT L M H (M * ℓ))] [HasPrincipalDivisors L (KT L M H (M * ℓ'))]
    (hα : (heckeAlphaHBar L M H ℓ).toRingHom.IsIntegral) (hβ : (heckeBetaHBar L M H ℓ).toRingHom.IsIntegral)
    (hα' : (heckeAlphaHBar L M H ℓ').toRingHom.IsIntegral) (hβ' : (heckeBetaHBar L M H ℓ').toRingHom.IsIntegral)
    (D : Divisor L (KK L M H)) :
    Divisor.correspondence (heckeBetaHBar L M H ℓ) (heckeAlphaHBar L M H ℓ) hβ hα
        (Divisor.correspondence (heckeBetaHBar L M H ℓ') (heckeAlphaHBar L M H ℓ') hβ' hα' D)
      = Divisor.correspondence (heckeBetaHBar L M H ℓ') (heckeAlphaHBar L M H ℓ') hβ' hα'
        (Divisor.correspondence (heckeBetaHBar L M H ℓ) (heckeAlphaHBar L M H ℓ) hβ hα D) := by
  have h0 : HeckeBetaHDefined M H ℓ := betaHDefined_input M H ℓ
  have h0' : HeckeBetaHDefined M H ℓ' := betaHDefined_input M H ℓ'

  haveI : HasPrincipalDivisors L (roof L M H ℓ ℓ') := (nice_roof L M H ℓ ℓ').hasPrincipalDivisors
  haveI : HasPrincipalDivisors L (roof L M H ℓ' ℓ) := (nice_roof L M H ℓ' ℓ).hasPrincipalDivisors
  haveI : HasPrincipalDivisors L (RR L M H ℓ ℓ') := (nice_RR L M H ℓ ℓ').hasPrincipalDivisors
  have nK := nice_KK L M H ℓ ℓ'
  have nR := nice_roof L M H ℓ ℓ'
  have nR' : Nice L M H ℓ ℓ' (roof L M H ℓ' ℓ) := nice_symm L M H ℓ ℓ' (nice_roof L M H ℓ' ℓ)
  have nRR := nice_RR L M H ℓ ℓ'
  have hP := nK.isIntegral nR (legP L M H ℓ ℓ')
  have hI := nK.isIntegral nR (legI L M H ℓ ℓ')
  have hP' := nK.isIntegral nR' (legP L M H ℓ' ℓ)
  have hI' := nK.isIntegral nR' (legI L M H ℓ' ℓ)

  rw [heckeDiv_heckeDiv L M H ℓ ℓ' hcop h0 hα hβ hα' hβ' hP hI D,
    heckeDiv_heckeDiv L M H ℓ' ℓ hcop.symm h0' hα' hβ' hα hβ hP' hI' D]

  have hj := nR.isIntegral nRR (legJ L M H ℓ ℓ')
  have hj' := nR'.isIntegral nRR (legJ' L M H ℓ ℓ')
  have hjP := nK.isIntegral nRR ((legJ L M H ℓ ℓ').comp (legP L M H ℓ ℓ'))
  have hjI := nK.isIntegral nRR ((legJ L M H ℓ ℓ').comp (legI L M H ℓ ℓ'))
  have hjP' := nK.isIntegral nRR ((legJ' L M H ℓ ℓ').comp (legP L M H ℓ' ℓ))
  have hjI' := nK.isIntegral nRR ((legJ' L M H ℓ ℓ').comp (legI L M H ℓ' ℓ))
  have e1 := correspondence_comp_eq_smul (legP L M H ℓ ℓ') (legI L M H ℓ ℓ') (legJ L M H ℓ ℓ') hP hI hj hjP hjI
    (nR.finiteAlong nRR _) (nR.separableAlong nRR _) D
  have e2 := correspondence_comp_eq_smul (legP L M H ℓ' ℓ) (legI L M H ℓ' ℓ) (legJ' L M H ℓ ℓ') hP' hI' hj' hjP' hjI'
    (nR'.finiteAlong nRR _) (nR'.separableAlong nRR _) D

  have hPeq : (legJ L M H ℓ ℓ').comp (legP L M H ℓ ℓ') = (legJ' L M H ℓ ℓ').comp (legP L M H ℓ' ℓ) := by
    refine AlgHom.ext fun x => Subtype.ext ?_
    rw [AlgHom.comp_apply (legJ L M H ℓ ℓ') (legP L M H ℓ ℓ') x,
      AlgHom.comp_apply (legJ' L M H ℓ ℓ') (legP L M H ℓ' ℓ) x, coe_legJ, coe_legJ', coe_legP L M H ℓ ℓ' h0',
      coe_legP L M H ℓ' ℓ h0, qExpand_congr (Nat.mul_comm ℓ ℓ')]
  have hIeq : (legJ L M H ℓ ℓ').comp (legI L M H ℓ ℓ') = (legJ' L M H ℓ ℓ').comp (legI L M H ℓ' ℓ) := by
    refine AlgHom.ext fun x => Subtype.ext ?_
    rw [AlgHom.comp_apply (legJ L M H ℓ ℓ') (legI L M H ℓ ℓ') x,
      AlgHom.comp_apply (legJ' L M H ℓ ℓ') (legI L M H ℓ' ℓ) x, coe_legJ, coe_legJ', coe_legI, coe_legI]
  have e3 := Divisor.correspondence_congr hPeq hIeq hjP hjI hjP' hjI' D

  have hdeg : finrankAlong L (legJ L M H ℓ ℓ') = finrankAlong L (legJ' L M H ℓ ℓ') := by
    have d1 : finrankAlong L (legJ L M H ℓ ℓ') = IntermediateField.relfinrank (roof L M H ℓ ℓ') (RR L M H ℓ ℓ') :=
      finrankAlong_inclusion _
    have d2 : finrankAlong L (legJ' L M H ℓ ℓ') = IntermediateField.relfinrank (roof L M H ℓ' ℓ) (RR L M H ℓ ℓ') :=
      finrankAlong_inclusion _
    rw [d1, d2]
    have t1 := IntermediateField.relfinrank_mul_relfinrank (KK_le_roof L M H ℓ ℓ') (roof_le_RR L M H ℓ ℓ')
    have t2 := IntermediateField.relfinrank_mul_relfinrank (KK_le_roof L M H ℓ' ℓ) (roof'_le_RR L M H ℓ ℓ')
    have hs : IntermediateField.relfinrank (KK L M H) (roof L M H ℓ ℓ')
        = IntermediateField.relfinrank (KK L M H) (roof L M H ℓ' ℓ) := by
      rw [relfinrank_KK_roof L M H ℓ ℓ' hcop, relfinrank_KK_roof L M H ℓ' ℓ hcop.symm, mul_comm]
    have hne : IntermediateField.relfinrank (KK L M H) (roof L M H ℓ ℓ') ≠ 0 :=
      nK.relfinrank_ne_zero nR (KK_le_roof L M H ℓ ℓ')
    apply mul_left_cancel₀ hne
    rw [t1, hs, t2]
  have hne : (finrankAlong L (legJ L M H ℓ ℓ') : ℤ) ≠ 0 := by
    exact_mod_cast nR.finrankAlong_ne_zero nRR (legJ L M H ℓ ℓ')
  rw [e3, e2, ← hdeg] at e1
  exact eq_of_zsmul_eq_zsmul hne e1.symm

theorem heckeOperatorHAlong_comm' (hℓ : ℓ = ℓ' ∨ Nat.Coprime ℓ ℓ') (x : Pic0 L (KK L M H)) :
    heckeOperatorHAlong L M H ℓ (heckeOperatorHAlong L M H ℓ' x)
      = heckeOperatorHAlong L M H ℓ' (heckeOperatorHAlong L M H ℓ x) := by
  by_cases heq : ℓ = ℓ'
  · subst heq; rfl
  have hcop : Nat.Coprime ℓ ℓ' := hℓ.resolve_left heq
  by_cases h : HeckeInputsHAlong L M H ℓ
  swap
  · rw [heckeOperatorHAlong_of_not h]; simp
  by_cases h' : HeckeInputsHAlong L M H ℓ'
  swap
  · rw [heckeOperatorHAlong_of_not h']; simp
  obtain ⟨h0, hα, hβ, hPr, hfin, hFI, hN⟩ := h
  obtain ⟨h0', hα', hβ', hPr', hfin', hFI', hN'⟩ := h'
  haveI := hPr
  haveI := hPr'
  rw [heckeOperatorHAlong_eq h0 hα hβ hFI hfin hN, heckeOperatorHAlong_eq h0' hα' hβ' hFI' hfin' hN']
  exact AlgebraicCurve.Pic0.correspondence_correspondence_comm
    (heckeBetaHBar L M H ℓ) (heckeAlphaHBar L M H ℓ) (heckeBetaHBar L M H ℓ') (heckeAlphaHBar L M H ℓ')
    hβ hα hβ' hα' hFI hfin hN hFI' hfin' hN'
    (fun D => heckeDiv_comm L M H ℓ ℓ' hcop hα hβ hα' hβ' D) x

end XHHeckeCommute

/-- **The `X_H(M)` Hecke row commutes.**  For every prime `ℓ`, including `ℓ ∣ M` and `ℓ = ℓ'`.
Verbatim from `Theorems/Thm_ModularCurve_heckeOperatorHAlong_comm.lean:15-23`. -/
theorem heckeOperatorHAlong_comm (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (ℓ ℓ' : ℕ) [Fact ℓ.Prime] [Fact ℓ'.Prime] (P : ModularCurve.JH M H) :
    ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ
        (ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ' P) =
      ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ'
        (ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ P) := by
  have hp : ℓ.Prime := Fact.out
  have hp' : ℓ'.Prime := Fact.out
  haveI : NeZero ℓ := ⟨hp.ne_zero⟩
  haveI : NeZero ℓ' := ⟨hp'.ne_zero⟩
  have hℓ : ℓ = ℓ' ∨ Nat.Coprime ℓ ℓ' := by
    by_cases h : ℓ = ℓ'
    · exact Or.inl h
    · exact Or.inr ((Nat.coprime_primes hp hp').mpr h)
  exact XHHeckeCommute.heckeOperatorHAlong_comm' (AlgebraicClosure ℚ) M H ℓ ℓ' hℓ P

end ModularCurve

end
