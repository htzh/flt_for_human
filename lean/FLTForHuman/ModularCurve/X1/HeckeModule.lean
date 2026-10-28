/-
The X₁ Hecke–diamond layer on `J₁(M)`, from FLT's
`Definitions/Def_ModularCurve_X1HeckeModule.lean`
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X1HeckeModule.lean>).

Hosted here, statements verbatim with the pin:

* the polynomial Hecke algebra `ModularCurve.HeckeAlgOne = ℤ[X_ℓ, D_d]` with its
  generators `heckeGenOne`, `diamondGen` and the evaluation lemmas
  `aeval_heckeGenOne`, `aeval_diamondGen` (pin 16–30);
* the input bundle `HeckeDiamondInputsAll` (pin 58–65), the `ℤ`-linear Hecke operator
  `heckeOperatorOneBar` on `J₁(M) = Pic⁰` (pin 36–43), the generator family
  `heckeDiamondGenBar` with `heckeDiamondGenBar_inl`/`_inr` (pin 45–52) and the
  commuting hypothesis `HeckeDiamondCommuteBar` (pin 54–56);
* the `ℤ`-subalgebra consequence `isMulCommutative_adjoin_heckeDiamondGenBar` and the
  evaluation `heckeEvalOneBar : HeckeAlgOne →+* Module.End ℤ (JOne M)`, with
  `heckeEvalOneBar_apply`, `heckeEvalOneBarAux_X`, `heckeEvalOneBar_X`,
  `heckeEvalOneBar_heckeGenOne`, `heckeEvalOneBar_diamondGen`, `heckeEvalOneBar_C`
  (pin 67–120);
* the `HeckeAlgOne`-module structure `heckeModuleOneBar` on `J₁(M)`, with
  `heckeModuleOneBar_smul_def`, `_heckeGenOne_smul`, `_diamondGen_smul`, `_smul_of_not`,
  `_X_smul_of_not`, `_C_smul` (pin 122–170);
* MC-4c's row `JOne.galois_smul_heckeAlgOne_smul` (pin
  `Theorems/Thm_ModularCurve_JOne_galois_smul_heckeAlgOne_smul.lean`): the Galois action on
  `J₁(M)` commutes with the `HeckeAlgOne` action defined here. The pin's
  `JOneGaloisHeckeComm` engine (`P2M/Sol/S_…`, 254 lines: the α/β intertwining lemmas, the
  diamond commutation and the `MvPolynomial.induction_on` assembly over
  `heckeModuleOneBar_smul_def`) is kept `private`, because the wire has only the headline.
  Its `coeffMap_qExpand_comm` is the already-public `coeffMap_qExpand` of
  `ModularCurve/Defs/Laurent.lean` and is not restated.

Deferred, not transcribed: the pin's `Integral` (`tateHeckeRepOne`), `Rational`
(`rationalHeckeRepOne`, `rationalHeckeAlgebraOne`, `rationalDiamondOne`,
`rationalHeckeOne`) and `Predicate` (`RationalRankTwoNebentypusOf`,
`RationalRankTwoNebentypus`) sections. They rest on `TateModule`,
`RationalTateModule` and `rationalGaloisRep`, which are not in the port: the `p`-adic
Tate module definition layer is a separate deferred topic.

`heckeOperatorOneBar` is the `Module.End ℤ (JOne M)` wrapper of the ported
`heckeOperatorOneAlong`, which is total: it is `0` when `HeckeInputsOneAlong` fails.
The same wrapper shape is already used for the abstract `Bar` family in
`ModularCurve/Defs/HeckeModule.lean` (`heckeOperatorBar`).

  spec-pin: Definitions/Def_ModularCurve_X1HeckeModule.lean
  spec-pin: Theorems/Thm_ModularCurve_JOne_galois_smul_heckeAlgOne_smul.lean
  spec-pin: P2M/Sol/S_ModularCurve_JOne_galois_smul_heckeAlgOne_smul.lean

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X1HeckeModule.lean
-/
import FLTForHuman.ModularCurve.X1.HeckeOperator
import FLTForHuman.ModularCurve.X1.Diamond
import FLTForHuman.ModularCurve.Defs.ArithmeticGalois
import FLTForHuman.AlgebraicCurve.WeilExchange.GaloisRamification
import Mathlib.Algebra.MvPolynomial.CommRing

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open AlgebraicCurve

section Generators

abbrev HeckeAlgOne : Type := MvPolynomial (Nat.Primes ⊕ ℕ) ℤ

def heckeGenOne (ℓ : Nat.Primes) : HeckeAlgOne := MvPolynomial.X (Sum.inl ℓ)

def diamondGen (d : ℕ) : HeckeAlgOne := MvPolynomial.X (Sum.inr d)

@[simp] lemma aeval_heckeGenOne {A : Type*} [CommSemiring A] [Algebra ℤ A]
    (a : Nat.Primes ⊕ ℕ → A) (ℓ : Nat.Primes) :
    MvPolynomial.aeval a (heckeGenOne ℓ) = a (Sum.inl ℓ) :=
  MvPolynomial.aeval_X a _

@[simp] lemma aeval_diamondGen {A : Type*} [CommSemiring A] [Algebra ℤ A]
    (a : Nat.Primes ⊕ ℕ → A) (d : ℕ) :
    MvPolynomial.aeval a (diamondGen d) = a (Sum.inr d) :=
  MvPolynomial.aeval_X a _

end Generators

section Operators

variable (M : ℕ)

/-- The X₁ Hecke/diamond input bundle: the Hecke inputs for every prime `ℓ`, and
for every `d` coprime to `M` both a diamond automorphism and its base change to
`ℚ̄`. -/
def HeckeDiamondInputsAll : Prop :=
  (∀ ℓ : Nat.Primes,
      haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
      HeckeInputsOneAlong (AlgebraicClosure ℚ) M ℓ) ∧
    ∀ d : ℕ, Nat.Coprime d M →
      (∃ σ : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M, IsDiamondAut M d σ) ∧
        ∃ σ' : x1FunctionFieldBar M ≃ₐ[AlgebraicClosure ℚ] x1FunctionFieldBar M,
          IsBaseChangeAutOf (AlgebraicClosure ℚ) (diamondAut M d) σ'

/-- The `ℓ`-th Hecke operator on `J₁(M)`, as a `ℤ`-linear endomorphism: the
`Module.End ℤ` wrapper of `heckeOperatorOneAlong`. -/
def heckeOperatorOneBar (ℓ : Nat.Primes) : Module.End ℤ (JOne M) :=
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  (heckeOperatorOneAlong (AlgebraicClosure ℚ) M ℓ).toIntLinearMap

theorem heckeOperatorOneBar_apply (ℓ : Nat.Primes) (x : JOne M) :
    heckeOperatorOneBar M ℓ x =
      (haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩; heckeOperatorOneAlong (AlgebraicClosure ℚ) M ℓ x) :=
  rfl

/-- The Hecke generator and the diamond generator, bundled over the index type
`Nat.Primes ⊕ ℕ`. -/
def heckeDiamondGenBar : Nat.Primes ⊕ ℕ → Module.End ℤ (JOne M) :=
  Sum.elim (heckeOperatorOneBar M) (diamondOneBar M)

@[simp] theorem heckeDiamondGenBar_inl (ℓ : Nat.Primes) :
    heckeDiamondGenBar M (Sum.inl ℓ) = heckeOperatorOneBar M ℓ := rfl

@[simp] theorem heckeDiamondGenBar_inr (d : ℕ) :
    heckeDiamondGenBar M (Sum.inr d) = diamondOneBar M d := rfl

/-- The assumption that all Hecke and diamond generators commute pairwise. -/
def HeckeDiamondCommuteBar : Prop :=
  ∀ i j : Nat.Primes ⊕ ℕ,
    heckeDiamondGenBar M i * heckeDiamondGenBar M j = heckeDiamondGenBar M j * heckeDiamondGenBar M i

end Operators

section Eval

variable {M : ℕ}

theorem isMulCommutative_adjoin_heckeDiamondGenBar (h : HeckeDiamondCommuteBar M) :
    IsMulCommutative (Algebra.adjoin ℤ (Set.range (heckeDiamondGenBar M))) :=
  Algebra.isMulCommutative_adjoin ℤ (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact h i j)

open scoped IsMulCommutative in

/-- The evaluation of the polynomial Hecke algebra into the `ℤ`-subalgebra generated
by the Hecke and diamond operators, before forgetting the subalgebra. -/
def heckeEvalOneBarAux (h : HeckeDiamondCommuteBar M) :
    HeckeAlgOne →ₐ[ℤ] (Algebra.adjoin ℤ (Set.range (heckeDiamondGenBar M)) :
      Subalgebra ℤ (Module.End ℤ (JOne M))) :=
  haveI := isMulCommutative_adjoin_heckeDiamondGenBar h
  MvPolynomial.aeval fun i =>
    (⟨heckeDiamondGenBar M i, Algebra.subset_adjoin (Set.mem_range_self i)⟩ :
      Algebra.adjoin ℤ (Set.range (heckeDiamondGenBar M)))

/-- The evaluation of the polynomial Hecke algebra `HeckeAlgOne` into the
endomorphism ring of `J₁(M)`: `X_ℓ ↦ T_ℓ`, `D_d ↦ ⟨d⟩`. -/
def heckeEvalOneBar (h : HeckeDiamondCommuteBar M) : HeckeAlgOne →+* Module.End ℤ (JOne M) :=
  ((Algebra.adjoin ℤ (Set.range (heckeDiamondGenBar M))).val.comp (heckeEvalOneBarAux h)).toRingHom

theorem heckeEvalOneBar_apply (h : HeckeDiamondCommuteBar M) (t : HeckeAlgOne) :
    heckeEvalOneBar h t = (heckeEvalOneBarAux h t : Module.End ℤ (JOne M)) :=
  rfl

open scoped IsMulCommutative in
theorem heckeEvalOneBarAux_X (h : HeckeDiamondCommuteBar M) (i : Nat.Primes ⊕ ℕ) :
    heckeEvalOneBarAux h (MvPolynomial.X i) =
      ⟨heckeDiamondGenBar M i, Algebra.subset_adjoin (Set.mem_range_self i)⟩ :=
  haveI := isMulCommutative_adjoin_heckeDiamondGenBar h
  MvPolynomial.aeval_X _ i

theorem heckeEvalOneBar_X (h : HeckeDiamondCommuteBar M) (i : Nat.Primes ⊕ ℕ) :
    heckeEvalOneBar h (MvPolynomial.X i) = heckeDiamondGenBar M i := by
  rw [heckeEvalOneBar_apply, heckeEvalOneBarAux_X]

theorem heckeEvalOneBar_heckeGenOne (h : HeckeDiamondCommuteBar M) (ℓ : Nat.Primes) :
    heckeEvalOneBar h (heckeGenOne ℓ) = heckeOperatorOneBar M ℓ :=
  heckeEvalOneBar_X h (Sum.inl ℓ)

theorem heckeEvalOneBar_diamondGen (h : HeckeDiamondCommuteBar M) (d : ℕ) :
    heckeEvalOneBar h (diamondGen d) = diamondOneBar M d :=
  heckeEvalOneBar_X h (Sum.inr d)

theorem heckeEvalOneBar_C (h : HeckeDiamondCommuteBar M) (a : ℤ) :
    heckeEvalOneBar h (MvPolynomial.C a) = (a : Module.End ℤ (JOne M)) := by
  rw [← MvPolynomial.algebraMap_eq, eq_intCast, map_intCast]

end Eval

section TheModule

variable (M : ℕ)

open Classical in

@[implicit_reducible]
def heckeModuleOneBar : Module HeckeAlgOne (JOne M) :=
  if h : HeckeDiamondCommuteBar M then Module.compHom (JOne M) (heckeEvalOneBar h)
  else Module.compHom (JOne M)
    (MvPolynomial.eval₂Hom (Int.castRingHom ℤ) (0 : Nat.Primes ⊕ ℕ → ℤ))

variable {M}

theorem heckeModuleOneBar_smul_def (h : HeckeDiamondCommuteBar M) (t : HeckeAlgOne) (x : JOne M) :
    (letI := heckeModuleOneBar M; t • x) = heckeEvalOneBar h t x := by
  have e : heckeModuleOneBar M = Module.compHom (JOne M) (heckeEvalOneBar h) := dite_eq_left h
  rw [e]
  rfl

theorem heckeModuleOneBar_heckeGenOne_smul (h : HeckeDiamondCommuteBar M) (ℓ : Nat.Primes)
    (x : JOne M) : (letI := heckeModuleOneBar M; heckeGenOne ℓ • x) = heckeOperatorOneBar M ℓ x := by
  rw [heckeModuleOneBar_smul_def h, heckeEvalOneBar_heckeGenOne]

theorem heckeModuleOneBar_diamondGen_smul (h : HeckeDiamondCommuteBar M) (d : ℕ)
    (x : JOne M) : (letI := heckeModuleOneBar M; diamondGen d • x) = diamondOneBar M d x := by
  rw [heckeModuleOneBar_smul_def h, heckeEvalOneBar_diamondGen]

theorem heckeModuleOneBar_smul_of_not (h : ¬ HeckeDiamondCommuteBar M) (t : HeckeAlgOne) (x : JOne M) :
    (letI := heckeModuleOneBar M; t • x) = MvPolynomial.constantCoeff t • x := by
  have e : heckeModuleOneBar M =
      Module.compHom (JOne M)
        (MvPolynomial.eval₂Hom (Int.castRingHom ℤ) (0 : Nat.Primes ⊕ ℕ → ℤ)) :=
    dite_eq_right h
  rw [e]
  show (MvPolynomial.eval₂Hom (Int.castRingHom ℤ) (0 : Nat.Primes ⊕ ℕ → ℤ) t) • x = _
  rw [MvPolynomial.eval₂Hom_zero_apply, eq_intCast, Int.cast_id]

theorem heckeModuleOneBar_X_smul_of_not (h : ¬ HeckeDiamondCommuteBar M) (i : Nat.Primes ⊕ ℕ)
    (x : JOne M) : (letI := heckeModuleOneBar M; (MvPolynomial.X i : HeckeAlgOne) • x) = 0 := by
  rw [heckeModuleOneBar_smul_of_not h, MvPolynomial.constantCoeff_X, zero_zsmul]

theorem heckeModuleOneBar_C_smul (a : ℤ) (x : JOne M) :
    (letI := heckeModuleOneBar M; (MvPolynomial.C a : HeckeAlgOne) • x) = a • x := by
  by_cases h : HeckeDiamondCommuteBar M
  · rw [heckeModuleOneBar_smul_def h, heckeEvalOneBar_C, Module.End.intCast_apply]
  · rw [heckeModuleOneBar_smul_of_not h, MvPolynomial.constantCoeff_C]

end TheModule

/-! ## MC-4c — the Galois action commutes with the `HeckeAlgOne`-module structure

The pin's `P2M/Sol/S_ModularCurve_JOne_galois_smul_heckeAlgOne_smul.lean`, ported with
its `JOneGaloisHeckeComm` engine kept `private`:

* `intertwines_alpha`/`intertwines_beta`: the α/β degeneracy maps of `X₁(M) → X₁(M) ∩
  X₀(Mℓ)`, read through `arithmeticGalois`, commute with `arithmeticGalois` on the two
  function fields (the β case by `coeffMap_qExpand`, the pin's `coeffMap_qExpand_comm`,
  which the port already has);
* `galois_smul_heckeOperatorOneAlong`: the `X₁` Hecke operator commutes with the Galois
  action, through `SemilinearAut.pic0_correspondence_smul`;
* `mul_ofAlgAut_comm`/`smul_smul_comm_of_mul_comm`, `ringHom_apply_eq_of_eqOn`,
  `arithmeticRingAut_comm_of_rational` and the `Diamond` block: the arithmetic automorphism
  commutes with the diamond automorphism (the pin's generic "rational automorphism"
  argument, since `diamondAutBar` is a `Classical.choose`);
* the `Assembly` block: `MvPolynomial.induction_on` over `heckeModuleOneBar_smul_def`
  (and `heckeModuleOneBar_smul_of_not` in the `¬ HeckeDiamondCommuteBar` case).

The pin's `attribute [-simp] ModularForm.…` prelude is not reproduced (the port keeps
those global). -/

section GaloisHeckeComm

open IntermediateField HahnSeries

variable {L : Type*} [Field L] [Algebra ℚ L]

private theorem intertwines_alpha (M : ℕ) (ℓ : ℕ) (σ : L ≃ₐ[ℚ] L) :
    SemilinearAut.IntertwinesAlong (heckeAlphaOneBar L M ℓ).toRingHom
      (arithmeticGalois (x1FunctionField M) σ)
      (arithmeticGalois (x1x0FunctionFieldC ℚ M (M * ℓ)) σ) := by
  intro x
  apply Subtype.ext
  change ((arithmeticGalois (x1x0FunctionFieldC ℚ M (M * ℓ)) σ • heckeAlphaOneBar L M ℓ x :
      laurentBaseChange L (x1x0FunctionFieldC ℚ M (M * ℓ))) : LaurentSeries L) =
    ((heckeAlphaOneBar L M ℓ (arithmeticGalois (x1FunctionField M) σ • x) :
      laurentBaseChange L (x1x0FunctionFieldC ℚ M (M * ℓ))) : LaurentSeries L)
  rw [coe_arithmeticGalois_smul, coe_heckeAlphaOneBar, coe_heckeAlphaOneBar,
    coe_arithmeticGalois_smul]

private theorem intertwines_beta (M ℓ : ℕ) [NeZero ℓ] (σ : L ≃ₐ[ℚ] L) :
    SemilinearAut.IntertwinesAlong (heckeBetaOneBar L M ℓ).toRingHom
      (arithmeticGalois (x1FunctionField M) σ)
      (arithmeticGalois (x1x0FunctionFieldC ℚ M (M * ℓ)) σ) := by
  rcases Classical.em (HeckeBetaOneDefined M ℓ) with h | h
  · intro x
    apply Subtype.ext
    change ((arithmeticGalois (x1x0FunctionFieldC ℚ M (M * ℓ)) σ • heckeBetaOneBar L M ℓ x :
        laurentBaseChange L (x1x0FunctionFieldC ℚ M (M * ℓ))) : LaurentSeries L) =
      ((heckeBetaOneBar L M ℓ (arithmeticGalois (x1FunctionField M) σ • x) :
        laurentBaseChange L (x1x0FunctionFieldC ℚ M (M * ℓ))) : LaurentSeries L)
    rw [coe_arithmeticGalois_smul, coe_heckeBetaOneBar M ℓ h, coe_heckeBetaOneBar M ℓ h,
      coe_arithmeticGalois_smul, coeffMap_qExpand]
  · rw [heckeBetaOneBar_of_not M ℓ h]
    exact intertwines_alpha M ℓ σ

private theorem galois_smul_heckeOperatorOneAlong (M ℓ : ℕ) [NeZero ℓ] (σ : L ≃ₐ[ℚ] L)
    (P : Pic0 L (laurentBaseChange L (x1FunctionField M))) :
    σ • heckeOperatorOneAlong L M ℓ P = heckeOperatorOneAlong L M ℓ (σ • P) := by
  rcases Classical.em (HeckeInputsOneAlong L M ℓ) with h | h
  · obtain ⟨h0, hα, hβ, hP, hfin, hFI, hN⟩ := h
    exact haveI : (HasPrincipalDivisors L
          (laurentBaseChange L (x1x0FunctionFieldC ℚ M (M * ℓ)))) := hP
        (by
          rw [heckeOperatorOneAlong_eq h0 hα hβ hFI hfin hN, galois_smul_pic0_def,
            galois_smul_pic0_def]
          exact (SemilinearAut.pic0_correspondence_smul
            (g := arithmeticGalois (x1FunctionField M) σ)
            (g' := arithmeticGalois (x1x0FunctionFieldC ℚ M (M * ℓ)) σ)
            (heckeBetaOneBar L M ℓ) (heckeAlphaOneBar L M ℓ) hβ hα hFI hfin hN
            (intertwines_beta M ℓ σ) (intertwines_alpha M ℓ σ) P).symm)
  · rw [heckeOperatorOneAlong_of_not h, AddMonoidHom.zero_apply, AddMonoidHom.zero_apply,
      smul_zero]

section Semilinear

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem mul_ofAlgAut_comm (g : SemilinearAut K F) (τ : F ≃ₐ[K] F)
    (h : ∀ x : F, g • (τ x) = τ (g • x)) :
    g * SemilinearAut.ofAlgAut τ = SemilinearAut.ofAlgAut τ * g := by
  apply Subtype.ext
  apply Prod.ext
  · apply RingEquiv.ext
    intro x
    exact h x
  · apply RingEquiv.ext
    intro a
    change (SemilinearAut.baseAut g * 1) a = (1 * SemilinearAut.baseAut g) a
    rw [mul_one, one_mul]

private theorem smul_smul_comm_of_mul_comm (A B : SemilinearAut K F) (h : A * B = B * A)
    (P : Pic0 K F) : A • (B • P) = B • (A • P) := by
  rw [← mul_smul, ← mul_smul, h]

end Semilinear

section Rational

private theorem ringHom_apply_eq_of_eqOn {X : Type*} [DivisionRing X]
    {F₀ : IntermediateField ℚ (LaurentSeries ℚ)} (f₁ f₂ : laurentBaseChange L F₀ →+* X)
    (hconst : ∀ (a : L) (ha : algebraMap L (LaurentSeries L) a ∈ laurentBaseChange L F₀),
      f₁ ⟨algebraMap L (LaurentSeries L) a, ha⟩ = f₂ ⟨algebraMap L (LaurentSeries L) a, ha⟩)
    (hgen : ∀ (y : LaurentSeries ℚ) (hy : y ∈ F₀),
      f₁ ⟨coeffEmb L y, coeffEmb_mem_laurentBaseChange L hy⟩ =
        f₂ ⟨coeffEmb L y, coeffEmb_mem_laurentBaseChange L hy⟩)
    (x : laurentBaseChange L F₀) : f₁ x = f₂ x := by
  let T : Subfield (LaurentSeries L) :=
    (RingHom.eqLocusField f₁ f₂).map (SubringClass.subtype (laurentBaseChange L F₀))
  have hT : ∀ z : laurentBaseChange L F₀, f₁ z = f₂ z → (z : LaurentSeries L) ∈ T := fun z hz =>
    Subfield.mem_map.mpr ⟨z, hz, rfl⟩
  suffices hx : (x : LaurentSeries L) ∈ T by
    obtain ⟨x', hx', hx'x⟩ := Subfield.mem_map.mp hx
    have hxx : x' = x := Subtype.ext hx'x
    subst hxx
    exact hx'
  have hx := x.2
  rw [mem_laurentBaseChange_iff] at hx
  refine (Subfield.closure_le.mpr ?_) hx
  rintro _ (⟨a, rfl⟩ | ⟨z, hz, rfl⟩)
  · exact hT ⟨algebraMap L (LaurentSeries L) a, (laurentBaseChange L F₀).algebraMap_mem a⟩
      (hconst a _)
  · exact hT ⟨coeffEmb L z, coeffEmb_mem_laurentBaseChange L hz⟩ (hgen z hz)

private theorem arithmeticRingAut_comm_of_rational
    {F₀ : IntermediateField ℚ (LaurentSeries ℚ)}
    (τ : laurentBaseChange L F₀ →+* laurentBaseChange L F₀)
    (hτL : ∀ (a : L) (ha : algebraMap L (LaurentSeries L) a ∈ laurentBaseChange L F₀),
      τ ⟨algebraMap L (LaurentSeries L) a, ha⟩ = ⟨algebraMap L (LaurentSeries L) a, ha⟩)
    (hτ : ∀ (y : LaurentSeries ℚ) (hy : y ∈ F₀), ∃ y' : LaurentSeries ℚ,
      ((τ ⟨coeffEmb L y, coeffEmb_mem_laurentBaseChange L hy⟩ : laurentBaseChange L F₀) :
        LaurentSeries L) = coeffEmb L y')
    (σ : L ≃ₐ[ℚ] L) (x : laurentBaseChange L F₀) :
    arithmeticRingAut F₀ σ (τ x) = τ (arithmeticRingAut F₀ σ x) := by
  refine ringHom_apply_eq_of_eqOn (X := laurentBaseChange L F₀)
    ((arithmeticRingAut F₀ σ).toRingHom.comp τ) (τ.comp (arithmeticRingAut F₀ σ).toRingHom)
    ?_ ?_ x
  · intro a ha
    have h1 : ∀ (b : L) (hb : algebraMap L (LaurentSeries L) b ∈ laurentBaseChange L F₀),
        arithmeticRingAut F₀ σ ⟨algebraMap L (LaurentSeries L) b, hb⟩ =
          ⟨algebraMap L (LaurentSeries L) (σ b), (laurentBaseChange L F₀).algebraMap_mem (σ b)⟩ :=
      fun b hb => Subtype.ext (coeffMap_algebraMap (σ : L →+* L) b)
    change arithmeticRingAut F₀ σ (τ _) = τ (arithmeticRingAut F₀ σ _)
    rw [hτL a ha, h1, hτL]
  · intro y hy
    obtain ⟨y', hy'⟩ := hτ y hy
    have hfix : arithmeticRingAut F₀ σ
        (⟨coeffEmb L y, coeffEmb_mem_laurentBaseChange L hy⟩ : laurentBaseChange L F₀) =
          ⟨coeffEmb L y, coeffEmb_mem_laurentBaseChange L hy⟩ :=
      Subtype.ext (coeffMap_coeffEmb σ y)
    change arithmeticRingAut F₀ σ (τ _) = τ (arithmeticRingAut F₀ σ _)
    rw [hfix]
    apply Subtype.ext
    rw [coe_arithmeticRingAut_apply, hy', coeffMap_coeffEmb]

end Rational

section Diamond

private theorem isBaseChangeAutOf_rational (M : ℕ) {d : ℕ}
    {τ : x1FunctionFieldBar M ≃ₐ[AlgebraicClosure ℚ] x1FunctionFieldBar M}
    (hτ : IsBaseChangeAutOf (AlgebraicClosure ℚ) (diamondAut M d) τ)
    (y : LaurentSeries ℚ) (hy : y ∈ x1FunctionField M) :
    ∃ y' : LaurentSeries ℚ,
      (((τ : x1FunctionFieldBar M →+* x1FunctionFieldBar M)
          ⟨coeffEmb (AlgebraicClosure ℚ) y,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hy⟩ :
            x1FunctionFieldBar M) : LaurentSeries (AlgebraicClosure ℚ))
        = coeffEmb (AlgebraicClosure ℚ) y' :=
  ⟨((diamondAut M d ⟨y, hy⟩ : x1FunctionField M) : LaurentSeries ℚ), hτ ⟨y, hy⟩⟩

private theorem arithmeticRingAut_diamondAutBar_comm (M : ℕ) (d : ℕ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : x1FunctionFieldBar M) :
    arithmeticRingAut (x1FunctionField M) σ
        ((diamondAutBar M d : x1FunctionFieldBar M →+* x1FunctionFieldBar M) x) =
      (diamondAutBar M d : x1FunctionFieldBar M →+* x1FunctionFieldBar M)
        (arithmeticRingAut (x1FunctionField M) σ x) := by
  rcases Classical.em
      (∃ τ : x1FunctionFieldBar M ≃ₐ[AlgebraicClosure ℚ] x1FunctionFieldBar M,
        IsBaseChangeAutOf (AlgebraicClosure ℚ) (diamondAut M d) τ) with hex | hex
  · exact arithmeticRingAut_comm_of_rational
      (diamondAutBar M d : x1FunctionFieldBar M →+* x1FunctionFieldBar M)
      (fun a _ => (diamondAutBar M d).commutes a)
      (isBaseChangeAutOf_rational M (isBaseChangeAutOf_baseChangeAut hex)) σ x
  · have hrefl : diamondAutBar M d = AlgEquiv.refl := baseChangeAut_of_not hex
    rw [hrefl]
    rfl

private theorem arithmeticGalois_mul_ofAlgAut_diamondAutBar (M : ℕ) (d : ℕ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    arithmeticGalois (x1FunctionField M) σ * SemilinearAut.ofAlgAut (diamondAutBar M d) =
      SemilinearAut.ofAlgAut (diamondAutBar M d) * arithmeticGalois (x1FunctionField M) σ :=
  mul_ofAlgAut_comm _ _ (arithmeticRingAut_diamondAutBar_comm M d σ)

private theorem galois_smul_diamondOneBar (M : ℕ) (d : ℕ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (P : JOne M) :
    σ • diamondOneBar M d P = diamondOneBar M d (σ • P) := by
  rw [diamondOneBar_apply, diamondOneBar_apply, galois_smul_pic0_def, galois_smul_pic0_def]
  exact smul_smul_comm_of_mul_comm _ _ (arithmeticGalois_mul_ofAlgAut_diamondAutBar M d σ) P

end Diamond

section Assembly

private theorem galois_smul_heckeDiamondGenBar (M : ℕ) (i : Nat.Primes ⊕ ℕ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JOne M) :
    σ • heckeDiamondGenBar M i x = heckeDiamondGenBar M i (σ • x) := by
  cases i with
  | inl ℓ =>
      exact haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
        (by
          rw [heckeDiamondGenBar_inl, heckeOperatorOneBar_apply, heckeOperatorOneBar_apply]
          exact galois_smul_heckeOperatorOneAlong M ℓ σ x)
  | inr d =>
      rw [heckeDiamondGenBar_inr]
      exact galois_smul_diamondOneBar M d σ x

private theorem galois_smul_heckeEvalOneBar (M : ℕ) (h : HeckeDiamondCommuteBar M)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (t : HeckeAlgOne) :
    ∀ x : JOne M, σ • heckeEvalOneBar h t x = heckeEvalOneBar h t (σ • x) := by
  refine MvPolynomial.induction_on
    (motive := fun t => ∀ x : JOne M, σ • heckeEvalOneBar h t x = heckeEvalOneBar h t (σ • x))
    t ?_ ?_ ?_
  · intro a x
    rw [heckeEvalOneBar_C, Module.End.intCast_apply, Module.End.intCast_apply,
      galois_smul_pic0_def, galois_smul_pic0_def]
    exact SemilinearAut.smul_zsmul _ a x
  · intro p q hp hq x
    rw [RingHom.map_add, LinearMap.add_apply, LinearMap.add_apply, smul_add, hp, hq]
  · intro p i hp x
    rw [RingHom.map_mul, Module.End.mul_apply, Module.End.mul_apply, heckeEvalOneBar_X, hp,
      galois_smul_heckeDiamondGenBar]

private theorem galois_smul_hecke_smul (M : ℕ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (t : HeckeAlgOne) (x : JOne M) :
    (letI := heckeModuleOneBar M; σ • (t • x)) =
      (letI := heckeModuleOneBar M; t • (σ • x)) := by
  by_cases h : HeckeDiamondCommuteBar M
  · rw [heckeModuleOneBar_smul_def h, heckeModuleOneBar_smul_def h]
    exact galois_smul_heckeEvalOneBar M h σ t x
  · rw [heckeModuleOneBar_smul_of_not h, heckeModuleOneBar_smul_of_not h, galois_smul_pic0_def,
      galois_smul_pic0_def]
    exact SemilinearAut.smul_zsmul _ _ x

end Assembly

end GaloisHeckeComm

-- MC-4c's row (`Theorems/Thm_ModularCurve_JOne_galois_smul_heckeAlgOne_smul.lean`): with
-- `letI := heckeModuleOneBar M`, every `t : HeckeAlgOne` commutes with the Galois action.
namespace JOne

theorem galois_smul_heckeAlgOne_smul (M : ℕ) [NeZero M]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (t : ModularCurve.HeckeAlgOne)
    (x : ModularCurve.JOne M) :
    letI := ModularCurve.heckeModuleOneBar M
    σ • (t • x) = t • (σ • x) :=
  galois_smul_hecke_smul M σ t x

end JOne

end ModularCurve

end
