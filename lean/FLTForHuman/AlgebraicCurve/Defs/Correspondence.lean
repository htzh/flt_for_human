/-
The along-map correspondence layer: `algebraAlong`, the along-level
`FundamentalIdentity`/`FiniteAlong`/`NormFormulaAlong`/`SeparableAlong`
predicates, `Divisor.pullbackAlong`/`pushforwardAlong`/`correspondence`,
`Pic0.correspondence`, `Place.restrictAlong`/`ramificationIndexAlong`/
`inertiaDegAlong`, `fiberAlong`, and `IntertwinesAlong`, after FLT's
`Definitions/Def_AlgebraicCurve_Correspondence.lean`
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Correspondence.lean>).

`algebraAlong` is kept an `abbrev`: T4's `rfl` bridges and T7's `eA`/`fB`/`fF`/`eF`
identifications hold only while it unfolds definitionally (SET-1 §3).
spec-pin: Definitions/Def_AlgebraicCurve_Correspondence.lean
spec-pin: Theorems/Thm_AlgebraicCurve_SemilinearAut_pic0_correspondence_swap_smul.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_SemilinearAut_pic0_correspondence_swap_smul.lean
-/
import FLTForHuman.AlgebraicCurve.Defs.PushPull
import FLTForHuman.AlgebraicCurve.Defs.SemilinearAut
import Mathlib.FieldTheory.Relrank
import Mathlib.FieldTheory.Separable

set_option autoImplicit false

-- The pin's `letI`/`haveI` walls are load-bearing; keep them literal (SET-1 §3).
set_option linter.style.haveILetI false

noncomputable section

namespace AlgebraicCurve

section AlongHom

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

abbrev algebraAlong (φ : F →ₐ[K] F') : Algebra F F' := φ.toRingHom.toAlgebra

theorem isScalarTower_along (φ : F →ₐ[K] F') :
    letI := algebraAlong φ; IsScalarTower K F F' :=
  letI := algebraAlong φ
  IsScalarTower.of_algebraMap_eq fun k => (φ.commutes k).symm

theorem isIntegral_along (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) :
    letI := algebraAlong φ; Algebra.IsIntegral F F' :=
  letI := algebraAlong φ
  ⟨hφ⟩

variable (K) in

def FundamentalIdentityAlong (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    [HasPrincipalDivisors K F'] : Prop :=
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  FundamentalIdentity K F F'

variable (K) in

def FiniteAlong (φ : F →ₐ[K] F') : Prop :=
  letI := algebraAlong φ
  Module.Finite F F'

variable (K) in

def NormFormulaAlong (φ : F →ₐ[K] F') (hfin : FiniteAlong K φ) : Prop :=
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI : Module.Finite F F' := hfin
  Divisor.PushforwardNormFormula K F F'

variable (K) in

def finrankAlong (φ : F →ₐ[K] F') : ℕ :=
  letI := algebraAlong φ
  Module.finrank F F'

end AlongHom

/-! ## The generic `finrankAlong` helpers

Three lemmas the pin defines `private` inside its degree/roof `S_` files. They
belong beside `finrankAlong` and are public here; `ModularCurve/Degree/Roof.lean`
kept them `private` until mc-retrospective §8 item 2 promoted them. -/

section FinrankAlongHelpers

theorem finrankAlong_comp {K F F' F'' : Type*} [Field K] [Field F] [Field F']
    [Field F''] [Algebra K F] [Algebra K F'] [Algebra K F''] (φ : F →ₐ[K] F')
    (χ : F' →ₐ[K] F'') :
    finrankAlong K (χ.comp φ) = finrankAlong K φ * finrankAlong K χ := by
  let : Algebra F F' := algebraAlong φ
  let : Algebra F' F'' := algebraAlong χ
  let : Algebra F F'' := algebraAlong (χ.comp φ)
  have : IsScalarTower F F' F'' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  show Module.finrank F F'' = Module.finrank F F' * Module.finrank F' F''
  exact (Module.finrank_mul_finrank F F' F'').symm

theorem finrankAlong_id {K F : Type*} [Field K] [Field F] [Algebra K F] :
    finrankAlong K (AlgHom.id K F) = 1 := by
  let : Algebra F F := algebraAlong (AlgHom.id K F)
  show Module.finrank F F = 1
  exact Module.finrank_self F

theorem finrankAlong_eq_relfinrank_fieldRange {K E : Type*} [Field K] [Field E]
    [Algebra K E] (A B : IntermediateField K E) (φ : A →ₐ[K] B) :
    finrankAlong K φ = IntermediateField.relfinrank ((B.val.comp φ).fieldRange) B := by
  have hRB : (B.val.comp φ).fieldRange ≤ B := by
    rintro x ⟨a, rfl⟩
    exact (φ a).2
  rw [IntermediateField.relfinrank_eq_finrank_of_le hRB]
  let : Algebra A B := algebraAlong φ
  let i : A ≃+* ((B.val.comp φ).fieldRange) :=
    (AlgEquiv.ofInjectiveField (B.val.comp φ)).toRingEquiv
  let j : B ≃+* (IntermediateField.extendScalars hRB) := RingEquiv.refl _
  exact Algebra.finrank_eq_of_equiv_equiv i j (by
    refine RingHom.ext fun a => Subtype.ext ?_
    rfl)

end FinrankAlongHelpers

namespace Divisor

section AlongHom

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

section Pullback

variable [HasPrincipalDivisors K F'] (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)

def pullbackAlong : Divisor K F →+ Divisor K F' :=
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  Divisor.pullback F'

theorem isPrincipal_pullbackAlong {D : Divisor K F} (hD : D.IsPrincipal) :
    (pullbackAlong φ hφ D).IsPrincipal := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact Divisor.isPrincipal_pullback hD

theorem degree_pullbackAlong (hFI : FundamentalIdentityAlong K φ hφ) (D : Divisor K F) :
    degree (pullbackAlong φ hφ D) = (finrankAlong K φ : ℤ) * degree D := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  haveI : FundamentalIdentity K F F' := hFI
  exact Divisor.degree_pullback D

theorem pullbackAlong_mem_degZero (hFI : FundamentalIdentityAlong K φ hφ) {D : Divisor K F}
    (hD : D ∈ degZero (K := K) (F := F)) :
    pullbackAlong φ hφ D ∈ degZero (K := K) (F := F') := by
  rw [mem_degZero, degree_pullbackAlong φ hφ hFI, mem_degZero.mp hD, mul_zero]

end Pullback

section Pushforward

variable (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)

def pushforwardAlong : Divisor K F' →+ Divisor K F :=
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  Divisor.pushforward F

@[simp]
theorem degree_pushforwardAlong (D : Divisor K F') :
    degree (pushforwardAlong φ hφ D) = degree D := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact Divisor.degree_pushforward D

theorem pushforwardAlong_mem_degZero {D : Divisor K F'}
    (hD : D ∈ degZero (K := K) (F := F')) :
    pushforwardAlong φ hφ D ∈ degZero (K := K) (F := F) := by
  rwa [mem_degZero, degree_pushforwardAlong]

theorem isPrincipal_pushforwardAlong (hfin : FiniteAlong K φ)
    (hN : NormFormulaAlong K φ hfin) {D : Divisor K F'} (hD : D.IsPrincipal) :
    (pushforwardAlong φ hφ D).IsPrincipal := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  haveI : Module.Finite F F' := hfin
  exact Divisor.isPrincipal_pushforward_of_normFormula hN hD

end Pushforward

end AlongHom

section Correspondence

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable [HasPrincipalDivisors K F']
variable (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)

def correspondence : Divisor K F →+ Divisor K F :=
  (pushforwardAlong ψ hψ).comp (pullbackAlong φ hφ)

theorem correspondence_apply (D : Divisor K F) :
    correspondence φ ψ hφ hψ D = pushforwardAlong ψ hψ (pullbackAlong φ hφ D) :=
  rfl

theorem degree_correspondence (hFI : FundamentalIdentityAlong K φ hφ) (D : Divisor K F) :
    Divisor.degree (correspondence φ ψ hφ hψ D) = (finrankAlong K φ : ℤ) * Divisor.degree D := by
  rw [correspondence_apply, degree_pushforwardAlong, degree_pullbackAlong φ hφ hFI]

theorem correspondence_mem_degZero (hFI : FundamentalIdentityAlong K φ hφ) {D : Divisor K F}
    (hD : D ∈ degZero (K := K) (F := F)) :
    correspondence φ ψ hφ hψ D ∈ degZero (K := K) (F := F) :=
  pushforwardAlong_mem_degZero ψ hψ (pullbackAlong_mem_degZero φ hφ hFI hD)

theorem correspondence_mem_principal (hfin : FiniteAlong K ψ)
    (hN : NormFormulaAlong K ψ hfin) {D : Divisor K F}
    (hD : D ∈ principal (K := K) (F := F)) :
    correspondence φ ψ hφ hψ D ∈ principal (K := K) (F := F) :=
  isPrincipal_pushforwardAlong ψ hψ hfin hN (isPrincipal_pullbackAlong φ hφ hD)

end Correspondence

end Divisor

namespace Pic0

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable [HasPrincipalDivisors K F']
variable (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
variable (hFI : FundamentalIdentityAlong K φ hφ)
variable (hfin : FiniteAlong K ψ) (hN : NormFormulaAlong K ψ hfin)

def degZeroCorrespondence :
    Divisor.degZero (K := K) (F := F) →+ Divisor.degZero (K := K) (F := F) :=
  ((Divisor.correspondence φ ψ hφ hψ).domRestrict
    (Divisor.degZero (K := K) (F := F))).codRestrict _
    (fun D => Divisor.correspondence_mem_degZero φ ψ hφ hψ hFI D.2)

@[simp]
theorem coe_degZeroCorrespondence (D : Divisor.degZero (K := K) (F := F)) :
    (degZeroCorrespondence φ ψ hφ hψ hFI D : Divisor K F) =
      Divisor.correspondence φ ψ hφ hψ (D : Divisor K F) :=
  rfl

def correspondence : Pic0 K F →+ Pic0 K F :=
  QuotientAddGroup.map _ _ (degZeroCorrespondence φ ψ hφ hψ hFI) (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact Divisor.correspondence_mem_principal φ ψ hφ hψ hfin hN hD)

theorem correspondence_mk (D : Divisor.degZero (K := K) (F := F)) :
    correspondence φ ψ hφ hψ hFI hfin hN (mk D) =
      mk (degZeroCorrespondence φ ψ hφ hψ hFI D) :=
  rfl

end Pic0

end AlgebraicCurve

namespace AlgebraicCurve

section AlongPlaces

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

def Place.restrictAlong (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') :
    Place K F :=
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  w.restrict F

def Place.ramificationIndexAlong (φ : F →ₐ[K] F') (w : Place K F') : ℕ :=
  letI := algebraAlong φ
  w.ramificationIndex F

def Place.inertiaDegAlong (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') :
    ℕ :=
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  w.inertiaDeg F

theorem Place.ord_restrictAlong (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place K F') (f : F) :
    w.ord (φ f) = Place.ramificationIndexAlong φ w * (w.restrictAlong φ hφ).ord f := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact w.ord_restrict f

theorem Divisor.pullbackAlong_apply [HasPrincipalDivisors K F'] (φ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) (D : Divisor K F) (w : Place K F') :
    Divisor.pullbackAlong φ hφ D w
      = Place.ramificationIndexAlong φ w * D (w.restrictAlong φ hφ) := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact Divisor.pullback_apply D w

theorem Divisor.pushforwardAlong_single (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place K F') (n : ℤ) :
    Divisor.pushforwardAlong φ hφ (Finsupp.single w n)
      = Finsupp.single (w.restrictAlong φ hφ) (n * w.inertiaDegAlong φ hφ) := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact Divisor.pushforward_single w n

end AlongPlaces

end AlgebraicCurve

namespace AlgebraicCurve

variable {K F F₁ Z : Type*} [Field K] [Field F] [Field F₁] [Field Z]
  [Algebra K F] [Algebra K F₁] [Algebra K Z]

namespace Place

theorem restrictAlong_congr {φ φ' : F →ₐ[K] F₁} (h : φ = φ')
    (hφ : φ.toRingHom.IsIntegral) (hφ' : φ'.toRingHom.IsIntegral) (w : Place K F₁) :
    w.restrictAlong φ hφ = w.restrictAlong φ' hφ' := by
  subst h
  rfl

section Fiber

variable [HasPrincipalDivisors K Z]

def fiberAlong (u : F₁ →ₐ[K] Z) (hu : u.toRingHom.IsIntegral) (w₁ : Place K F₁) :
    Finset (Place K Z) :=
  letI := algebraAlong u
  haveI := isScalarTower_along u
  haveI := isIntegral_along u hu
  Place.fiber Z w₁

@[simp]
theorem mem_fiberAlong {u : F₁ →ₐ[K] Z} {hu : u.toRingHom.IsIntegral} {w₁ : Place K F₁}
    {W : Place K Z} : W ∈ fiberAlong u hu w₁ ↔ W.restrictAlong u hu = w₁ := by
  letI := algebraAlong u
  haveI := isScalarTower_along u
  haveI := isIntegral_along u hu
  exact Place.mem_fiber

theorem _root_.AlgebraicCurve.Divisor.pullbackAlong_single (u : F₁ →ₐ[K] Z)
    (hu : u.toRingHom.IsIntegral) (w₁ : Place K F₁) (n : ℤ) :
    Divisor.pullbackAlong u hu (Finsupp.single w₁ n)
      = ∑ W ∈ fiberAlong u hu w₁,
          Finsupp.single W (n * W.ramificationIndexAlong u) := by
  letI := algebraAlong u
  haveI := isScalarTower_along u
  haveI := isIntegral_along u hu
  exact Divisor.pullback_single w₁ n

end Fiber

end Place

end AlgebraicCurve

namespace AlgebraicCurve

section AlongTransport

variable {K F F₁ : Type*} [Field K] [Field F] [Field F₁] [Algebra K F] [Algebra K F₁]

variable (K) in

def SeparableAlong (φ : F →ₐ[K] F₁) : Prop :=
  letI := algebraAlong φ
  Algebra.IsSeparable F F₁

end AlongTransport

end AlgebraicCurve

namespace AlgebraicCurve

namespace SemilinearAut

section Intertwines

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

def IntertwinesAlong (ι : F →+* F') (g : SemilinearAut K F) (g' : SemilinearAut K F') : Prop :=
  ∀ x : F, g' • (ι x) = ι (g • x)

theorem IntertwinesAlong.inv {ι : F →+* F'} {g : SemilinearAut K F} {g' : SemilinearAut K F'}
    (h : IntertwinesAlong ι g g') : IntertwinesAlong ι g⁻¹ g'⁻¹ := fun x => by
  have hx := h (g⁻¹ • x)
  rw [smul_inv_smul] at hx
  rw [← hx, inv_smul_smul]

theorem IntertwinesAlong.one (ι : F →+* F') :
    IntertwinesAlong ι (1 : SemilinearAut K F) (1 : SemilinearAut K F') := fun x => by
  rw [one_smul, one_smul]

theorem IntertwinesAlong.mul {ι : F →+* F'} {g₁ g₂ : SemilinearAut K F}
    {g₁' g₂' : SemilinearAut K F'} (h₁ : IntertwinesAlong ι g₁ g₁')
    (h₂ : IntertwinesAlong ι g₂ g₂') : IntertwinesAlong ι (g₁ * g₂) (g₁' * g₂') := fun x => by
  rw [mul_smul, mul_smul, h₂ x, h₁ (g₂ • x)]

end Intertwines

end SemilinearAut

end AlgebraicCurve

namespace AlgebraicCurve

/-! ## The cross-intertwining pair and the transport laws for the along-maps

The pin's `S_AlgebraicCurve_SemilinearAut_pic0_correspondence_swap_smul` prelude: a pair
of semilinear automorphisms `g`, `g'` that is intertwined by *two* maps `φ`, `ψ` in
opposite directions (`CrossIntertwines φ ψ g g'` and `CrossIntertwines ψ φ g g'`), and the
laws the `pic0` correspondence needs — restriction of places, ramification index,
residue-field transport, inertia degree, and the pullback/pushforward of divisors along
`ψ` and `φ`, each transported by the pair. The pin keeps them in a machine namespace
`SwapSmul`; the port puts each beside the object it acts on.

The pin's `private SwapSmul.ord_smul` (the order law `(g' • w).ord (ψ f) = w.ord (φ (g⁻¹ • f))`
for the pair) is a three-line consequence of the public `SemilinearAut.ord_smul`, so it is
spelled inline where it is used rather than copied. -/

section CrossIntertwinesAlong

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable {g : SemilinearAut K F} {g' : SemilinearAut K F'}
variable {φ ψ : F →ₐ[K] F'}

namespace SemilinearAut

/-- Two semilinear automorphisms `g`, `g'` are cross-intertwined by `φ` and `ψ` when `g'`
carries `φ x` to `ψ (g x)` — the two-map version of `IntertwinesAlong`. -/
def CrossIntertwines (φ ψ : F →ₐ[K] F') (g : SemilinearAut K F) (g' : SemilinearAut K F') :
    Prop :=
  ∀ x : F, g' • (φ x) = ψ (g • x)

theorem CrossIntertwines.inv (h : CrossIntertwines φ ψ g g') :
    CrossIntertwines ψ φ g⁻¹ g'⁻¹ := by
  intro x
  have hx := h (g⁻¹ • x)
  rw [smul_inv_smul] at hx
  rw [← hx, inv_smul_smul]

end SemilinearAut

open SemilinearAut
open scoped Pointwise

namespace Place

theorem restrictAlong_smul (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (h : CrossIntertwines φ ψ g g') (w : Place K F') :
    (g' • w).restrictAlong ψ hψ = g • w.restrictAlong φ hφ := by
  apply Place.toValuationSubring_injective
  ext x
  change ψ x ∈ (g' • w).toValuationSubring ↔
    x ∈ (g • w.restrictAlong φ hφ).toValuationSubring
  rw [SemilinearAut.smul_toValuationSubring, SemilinearAut.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, h.inv x]
  rfl

theorem ramificationIndexAlong_smul (h : CrossIntertwines φ ψ g g') (w : Place K F') :
    (g' • w).ramificationIndexAlong ψ = w.ramificationIndexAlong φ := by
  unfold Place.ramificationIndexAlong Place.ramificationIndex
  change sInf {n : ℕ | 0 < n ∧ ∃ f : F, f ≠ 0 ∧ (g' • w).ord (ψ f) = n}
    = sInf {n : ℕ | 0 < n ∧ ∃ f : F, f ≠ 0 ∧ w.ord (φ f) = n}
  congr 1
  ext n
  simp only [Set.mem_ofPred_eq]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨f, hf, hford⟩
    refine ⟨g⁻¹ • f, by rwa [ne_eq, smul_eq_zero_iff_eq], ?_⟩
    have hord : (g' • w).ord (ψ f) = w.ord (φ (g⁻¹ • f)) := by
      have hψ : ψ f = g' • φ (g⁻¹ • f) := by rw [h, smul_inv_smul]
      rw [hψ, SemilinearAut.ord_smul]
    rw [← hord, hford]
  · rintro ⟨f, hf, hford⟩
    refine ⟨g • f, by rwa [ne_eq, smul_eq_zero_iff_eq], ?_⟩
    have hord : (g' • w).ord (ψ (g • f)) = w.ord (φ f) := by
      have hψ : ψ (g • f) = g' • φ (g⁻¹ • (g • f)) := by rw [h, smul_inv_smul]
      rw [hψ, SemilinearAut.ord_smul, inv_smul_smul]
    rw [hord, hford]

noncomputable def restrictEquiv (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (h : CrossIntertwines φ ψ g g') (w : Place K F') :
    (w.restrictAlong φ hφ).toValuationSubring ≃+*
      ((g' • w).restrictAlong ψ hψ).toValuationSubring where
  toFun x := ⟨g • (x : F), by
    have hx : φ (x : F) ∈ w.toValuationSubring := x.2
    show ψ (g • (x : F)) ∈ (g' • w).toValuationSubring
    rw [SemilinearAut.smul_toValuationSubring, ← h (x : F)]
    exact ValuationSubring.smul_mem_pointwise_smul g' _ _ hx⟩
  invFun y := ⟨g⁻¹ • (y : F), by
    have hy : ψ (y : F) ∈ (g' • w).toValuationSubring := y.2
    show φ (g⁻¹ • (y : F)) ∈ w.toValuationSubring
    rw [SemilinearAut.smul_toValuationSubring,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem] at hy
    rw [← h.inv (y : F)]
    exact hy⟩
  left_inv x := by ext; exact inv_smul_smul g (x : F)
  right_inv y := by ext; exact smul_inv_smul g (y : F)
  map_mul' x y := by ext; exact smul_mul' g (x : F) (y : F)
  map_add' x y := by ext; exact smul_add g (x : F) (y : F)

theorem inertiaDegAlong_smul (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (h : CrossIntertwines φ ψ g g') (w : Place K F') :
    (g' • w).inertiaDegAlong ψ hψ = w.inertiaDegAlong φ hφ := by
  letI iφ : Algebra (w.restrictAlong φ hφ).ResidueField w.ResidueField :=
    (letI := algebraAlong φ; haveI := isScalarTower_along φ; haveI := isIntegral_along φ hφ
     (Place.restrictResidueMap F w).toAlgebra)
  letI iψ : Algebra ((g' • w).restrictAlong ψ hψ).ResidueField (g' • w).ResidueField :=
    (letI := algebraAlong ψ; haveI := isScalarTower_along ψ; haveI := isIntegral_along ψ hψ
     (Place.restrictResidueMap F (g' • w)).toAlgebra)
  change Module.finrank ((g' • w).restrictAlong ψ hψ).ResidueField (g' • w).ResidueField
    = Module.finrank (w.restrictAlong φ hφ).ResidueField w.ResidueField
  refine (Algebra.finrank_eq_of_equiv_equiv
    (IsLocalRing.ResidueField.mapEquiv (restrictEquiv hφ hψ h w))
    (SemilinearAut.smulResidueRingEquiv g' w) ?_).symm
  refine RingHom.ext fun x => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change IsLocalRing.residue (g' • w).toValuationSubring
      (⟨ψ (g • (a : F)), _⟩ : (g' • w).toValuationSubring)
    = IsLocalRing.residue (g' • w).toValuationSubring
      (⟨g' • φ (a : F), _⟩ : (g' • w).toValuationSubring)
  exact congrArg (IsLocalRing.residue _) (Subtype.ext (h (a : F)).symm)

end Place

namespace Divisor

theorem pullbackAlong_smul [HasPrincipalDivisors K F'] (hφ : φ.toRingHom.IsIntegral)
    (hψ : ψ.toRingHom.IsIntegral) (h : CrossIntertwines φ ψ g g') (D : Divisor K F) :
    Divisor.pullbackAlong ψ hψ (g • D) = g' • Divisor.pullbackAlong φ hφ D := by
  ext w
  rw [Divisor.pullbackAlong_apply, SemilinearAut.divisor_smul_apply,
    SemilinearAut.divisor_smul_apply, Divisor.pullbackAlong_apply,
    Place.restrictAlong_smul hψ hφ h.inv w, Place.ramificationIndexAlong_smul h.inv w]

theorem pushforwardAlong_smul (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (h : CrossIntertwines φ ψ g g') (E : Divisor K F') :
    Divisor.pushforwardAlong ψ hψ (g' • E) = g • Divisor.pushforwardAlong φ hφ E := by
  induction E using Finsupp.induction with
  | zero => rw [smul_zero, map_zero, map_zero, smul_zero]
  | single_add w n D _ _ ih =>
    rw [smul_add, map_add, map_add, smul_add, ih]
    congr 1
    rw [SemilinearAut.smul_single, Divisor.pushforwardAlong_single,
      Divisor.pushforwardAlong_single, SemilinearAut.smul_single,
      Place.restrictAlong_smul hφ hψ h w, Place.inertiaDegAlong_smul hφ hψ h w]

theorem correspondence_smul_exchange [HasPrincipalDivisors K F']
    (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (h₁ : CrossIntertwines φ ψ g g') (h₂ : CrossIntertwines ψ φ g g') (D : Divisor K F) :
    Divisor.correspondence φ ψ hφ hψ (g • D) = g • Divisor.correspondence ψ φ hψ hφ D := by
  rw [Divisor.correspondence_apply, Divisor.correspondence_apply,
    pullbackAlong_smul hψ hφ h₂ D, pushforwardAlong_smul hφ hψ h₁]

end Divisor

namespace SemilinearAut

/-- **The `Pic0` correspondence commutes with the semilinear action, up to swapping the
pair**: for a cross-intertwined pair of maps `φ`, `ψ`, the correspondence in the direction
`φ → ψ` of the transported class is the transport of the correspondence in the direction
`ψ → φ`. Statement from
`Theorems/Thm_AlgebraicCurve_SemilinearAut_pic0_correspondence_swap_smul.lean`; proof
after the pin's `S_` file — a class is represented by a degree-zero divisor, and the
divisor-level `correspondence_smul_exchange` above. -/
theorem pic0_correspondence_swap_smul {K F F' : Type*} [Field K]
    [Field F] [Field F'] [Algebra K F] [Algebra K F'] {g : SemilinearAut K F}
    {g' : SemilinearAut K F'} [HasPrincipalDivisors K F'] (φ ψ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hFIφ : FundamentalIdentityAlong K φ hφ) (hfinψ : FiniteAlong K ψ)
    (hNψ : NormFormulaAlong K ψ hfinψ)
    (hFIψ : FundamentalIdentityAlong K ψ hψ) (hfinφ : FiniteAlong K φ)
    (hNφ : NormFormulaAlong K φ hfinφ)
    (h₁ : ∀ x : F, g' • (φ x) = ψ (g • x)) (h₂ : ∀ x : F, g' • (ψ x) = φ (g • x))
    (c : Pic0 K F) :
    Pic0.correspondence φ ψ hφ hψ hFIφ hfinψ hNψ (g • c)
      = g • Pic0.correspondence ψ φ hψ hφ hFIψ hfinφ hNφ c := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective c
  rw [SemilinearAut.pic0_smul_mk, Pic0.correspondence_mk, Pic0.correspondence_mk,
    SemilinearAut.pic0_smul_mk]
  refine congrArg Pic0.mk (Subtype.ext ?_)
  rw [Pic0.coe_degZeroCorrespondence, SemilinearAut.coe_degZeroSMulHom,
    SemilinearAut.coe_degZeroSMulHom, Pic0.coe_degZeroCorrespondence]
  exact Divisor.correspondence_smul_exchange hφ hψ h₁ h₂ (D : Divisor K F)

end SemilinearAut

end CrossIntertwinesAlong

end AlgebraicCurve
