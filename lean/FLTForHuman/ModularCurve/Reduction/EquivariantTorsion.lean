/-



The equivariant torsion reduction over the `j`-line: every automorphism of `E₀` is realised by an
element of the decomposition group at the `j`-value.

Over an algebraically closed field `K` of characteristic `p` and for an elliptic curve `E₀/K` with
`j(E₀) = j₀`, there are a field `M ⊇ K(t)` (`t` transcendental, `M/K(t)` finite Galois), a place
`W₀` of `M` with `W₀.ord (t - j₀) > 0`, and a group homomorphism `θ` from the `N`-torsion of the
`j`-model over `M` to `E₀[N]` which is injective on the part prime to `p`; and a representation `ρ`
of the decomposition group of `W₀` in the variable changes of `E₀` such that

* `ρ` is a monoid homomorphism and commutes with the Galois action through `θ`,
* **every** variable change `γ` of `E₀` is `ρ σ` for some `σ` in the decomposition group, up to sign,
* `ρ σ = 1` with `σ` in the decomposition group forces `σ = 1`.

This is the "the automorphism group of the curve is the decomposition group" half of the
Frey/Serre–Tate argument, and the direct consumer of the stabilizer count
(`Automorphism/StabilizerOrder.lean`), the exceptional normal forms
(`Automorphism/{NormalForm,DeuringForm}.lean`) and the inertia-equivariant reduction
(`Reduction/{InertiaReduction,InertiaFaithful}.lean`).

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_exists_equivariant_torsion_reduction_ofJ.lean>

spec-pin: Theorems/Thm_ModularCurve_exists_equivariant_torsion_reduction_ofJ.lean
spec-pin: P2M/Sol/S_ModularCurve_exists_equivariant_torsion_reduction_ofJ.lean

Port notes (AF103A).  The pin is an all-public flattened `S_` file, so the whole engine is
transcribed: 64 engine declarations at the pin's names (its generated label `P2MKcOfJTors` becomes
the subject namespace `ModularCurve.EquivariantTorsion`) plus the headline, which is the pin's
`solution` under the `Theorems/` wrapper's name and statement, its body being the pin's `main` (the
pin's own `main`↔`solution` pair — the statement occurs twice by construction, as in the pin).

* `check_port --force`: **65 ok, 0 mismatch, 0 missing, 0 own, 0 kw**.
* Engine diff (`statement_db.parse_file`): pin 65 rows, module 65 rows; **64/64 engine rows by
  statement hash**, the headline accounted by the wrapper's name (the pin's `solution` row renames
  to it); nothing unaccounted.
* One substitution: `exists_variableChange_of_j_eq` is mathlib's
  (`Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ`), imported and used at the pin's use site, not
  re-proved.  The 18 pin helpers that exist in the port only as `private` declarations
  (`P2MKcSerreTate.*` in `WeierstrassCurve/Reduction/InertiaReduction.lean`) are not importable, so
  the pin's rows are transcribed here (`castPt`…`vcInvAddHom`, `some_congr`, `map_vcYInv`,
  `heq_zero_of_eq`, `VariableChange.map_mul'`/`map_inv'`).
* `dedup --within`: **0 clusters**; `move_dead --dry-run`: **0 declarations, 0 lines**.
* The pin's `attribute [-instance]`/`[-simp]` walls are **not** transcribed (PORTING-AC/MC), its
  `set_option maxHeartbeats`/`synthInstance.maxHeartbeats` are **not** transcribed, and its
  `haveI`/`letI` became `have`/`let` where `linter.style.haveILetI` asked (proof-irrelevant).
* Five blocks are carved into `private` helpers with the pin's text, so each elaboration gets its own
  budget: `torsion_card_eq_sq` (the pin's `Nat.card` bullet), `gK_conj_mul` (pin `:773`–`:781`, the
  residue-induced variable change is multiplicative — the pin's `hc4`), `eq_of_forall_nsmul_eq_of_faithful`
  (pin `:830`–`:858`, the `hLfix` faithful-torsion block), `exists_good_model_route` (pin `:571`–`:622`,
  the `∃ m`/good-model route) and `stabilizer_card_bound` (pin `:1057`–`:1223`, the `key` stabilizer
  bound).  All are `private`, so the public surface stays the pin's 65 rows.

Heartbeat probe pair (recorded, never installed): the pin carries `set_option maxHeartbeats 16000000`
and `set_option synthInstance.maxHeartbeats 1600000` on `main`; this module carries neither.  Measured
ladder on `main`: 200000/400000/500000/750000/1 000 000/1 500 000 fail, **2 000 000 is silent**,
4 000 000 is silent.  `lakefile.lean` ships `maxHeartbeats := 4000000` for the package, so the module **builds**
(`lake build FLTForHuman.ModularCurve.Reduction.EquivariantTorsion`: 3 474 jobs, 0 warnings from this
file); the only cap it misses is the edit loop's 200 k discipline cap.  `main`'s named sites and the
carves are recorded in `lean/tmp/af103/AF103A-REPORT.md`.
-/
import FLTForHuman.AlgebraicCurve.Genus.Index
import FLTForHuman.AlgebraicCurve.Place.IsPrimeOverValuationSubring
import FLTForHuman.AlgebraicCurve.Place.OrbitCardinality
import FLTForHuman.Elliptic.TorsionZMod
import FLTForHuman.WeierstrassCurve.Automorphism.DeuringForm
import FLTForHuman.WeierstrassCurve.Automorphism.NormalForm
import FLTForHuman.WeierstrassCurve.Automorphism.StabilizerOrder
import FLTForHuman.WeierstrassCurve.Reduction.InertiaFaithful
import FLTForHuman.WeierstrassCurve.Reduction.InertiaReduction
import FLTForHuman.WeierstrassCurve.Torsion.DivisionField
import FLTForHuman.WeierstrassCurve.Velu.VariableChangePoint
import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point IsLocalRing
  ValuationSubring AlgebraicCurve

open scoped IntermediateField Pointwise

namespace ModularCurve

namespace EquivariantTorsion

section Cast

variable {R : Type*} [CommRing R]

def castPt {V₁ V₂ : Affine R} (h : V₁ = V₂) : V₁.Point → V₂.Point
  | .zero => .zero
  | .some x y hns => .some x y (h ▸ hns)

@[scoped simp] lemma castPt_zero {V₁ V₂ : Affine R} (h : V₁ = V₂) :
    castPt h (0 : V₁.Point) = 0 := rfl

lemma castPt_some {V₁ V₂ : Affine R} (h : V₁ = V₂) {x y : R} (hns : V₁.Nonsingular x y) :
    castPt h (.some x y hns) = .some x y (h ▸ hns) := rfl

lemma castPt_rfl {V : Affine R} (P : V.Point) : castPt rfl P = P := by
  cases P <;> rfl

lemma heq_castPt {V₁ V₂ : Affine R} (h : V₁ = V₂) (P : V₁.Point) : HEq P (castPt h P) := by
  subst h; rw [castPt_rfl]

lemma eq_castPt_of_heq {V₁ V₂ : Affine R} (h : V₁ = V₂) {P : V₁.Point} {Q : V₂.Point}
    (hPQ : HEq P Q) : Q = castPt h P := by
  subst h; rw [castPt_rfl]; exact (eq_of_heq hPQ).symm

lemma castPt_castPt {V₁ V₂ V₃ : Affine R} (h : V₁ = V₂) (h' : V₂ = V₃) (P : V₁.Point) :
    castPt h' (castPt h P) = castPt (h.trans h') P := by
  subst h h'; simp only [castPt_rfl]

lemma castPt_eq_zero_iff {V₁ V₂ : Affine R} (h : V₁ = V₂) (P : V₁.Point) :
    castPt h P = 0 ↔ P = 0 := by
  subst h; rw [castPt_rfl]

lemma castPt_injective {V₁ V₂ : Affine R} (h : V₁ = V₂) : Function.Injective (castPt h) := by
  subst h; intro P Q hPQ; rwa [castPt_rfl, castPt_rfl] at hPQ

lemma some_congr {V : Affine R} {x₁ x₂ y₁ y₂ : R} (hx : x₁ = x₂) (hy : y₁ = y₂)
    (h₁ : V.Nonsingular x₁ y₁) (h₂ : V.Nonsingular x₂ y₂) :
    Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

lemma heq_some_of_eq {V₁ V₂ : Affine R} (hV : V₁ = V₂) {x₁ x₂ y₁ y₂ : R} (hx : x₁ = x₂)
    (hy : y₁ = y₂) (h₁ : V₁.Nonsingular x₁ y₁) (h₂ : V₂.Nonsingular x₂ y₂) :
    HEq (Point.some x₁ y₁ h₁) (Point.some x₂ y₂ h₂) := by
  subst hV; subst hx; subst hy; rfl

lemma heq_zero_of_eq {V₁ V₂ : Affine R} (hV : V₁ = V₂) :
    HEq (0 : V₁.Point) (0 : V₂.Point) := by
  subst hV; rfl

variable {F' : Type*} [Field F'] [DecidableEq F']

lemma castPt_add {V₁ V₂ : Affine F'} (h : V₁ = V₂) (P Q : V₁.Point) :
    castPt h (P + Q) = castPt h P + castPt h Q := by
  subst h; simp only [castPt_rfl]

lemma castPt_neg {V₁ V₂ : Affine F'} (h : V₁ = V₂) (P : V₁.Point) :
    castPt h (-P) = -castPt h P := by
  subst h; simp only [castPt_rfl]

def castAddHom {V₁ V₂ : Affine F'} (h : V₁ = V₂) : V₁.Point →+ V₂.Point where
  toFun := castPt h
  map_zero' := castPt_zero h
  map_add' := castPt_add h

@[scoped simp] lemma castAddHom_apply {V₁ V₂ : Affine F'} (h : V₁ = V₂) (P : V₁.Point) :
    castAddHom h P = castPt h P := rfl

lemma castPt_nsmul {V₁ V₂ : Affine F'} (h : V₁ = V₂) (n : ℕ) (P : V₁.Point) :
    castPt h (n • P) = n • castPt h P :=
  map_nsmul (castAddHom h) n P

end Cast

section Coord

variable {K : Type*} [Field K]

lemma vcXInv_mul (C C' : VariableChange K) (x : K) :
    vcXInv (C * C') x = vcXInv C (vcXInv C' x) := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  have hu' : (C'.u : K) ≠ 0 := C'.u.ne_zero
  simp only [vcXInv, VariableChange.mul_def, Units.val_inv_eq_inv_val, Units.val_mul]
  field_simp
  ring

lemma vcYInv_mul (C C' : VariableChange K) (x y : K) :
    vcYInv (C * C') x y = vcYInv C (vcXInv C' x) (vcYInv C' x y) := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  have hu' : (C'.u : K) ≠ 0 := C'.u.ne_zero
  simp only [vcXInv, vcYInv, VariableChange.mul_def, Units.val_inv_eq_inv_val, Units.val_mul]
  field_simp
  ring

@[scoped simp] lemma vcXInv_one (x : K) : vcXInv (1 : VariableChange K) x = x := by
  simp [vcXInv, VariableChange.one_def]

@[scoped simp] lemma vcYInv_one (x y : K) : vcYInv (1 : VariableChange K) x y = y := by
  simp [vcYInv, VariableChange.one_def]

variable {K' : Type*} [Field K'] (φ : K →+* K')

lemma map_vcXInv (C : VariableChange K) (x : K) :
    φ (vcXInv C x) = vcXInv (C.map φ) (φ x) := by
  simp only [vcXInv, VariableChange.map, Units.coe_map_inv, map_mul, map_pow, map_sub]
  rfl

lemma map_vcYInv (C : VariableChange K) (x y : K) :
    φ (vcYInv C x y) = vcYInv (C.map φ) (φ x) (φ y) := by
  simp only [vcYInv, VariableChange.map, Units.coe_map_inv, map_mul, map_pow, map_sub]
  rfl

def negC (W : WeierstrassCurve K) : VariableChange K := ⟨-1, 0, -W.a₁, -W.a₃⟩

lemma negC_smul (W : WeierstrassCurve K) : negC W • W = W := by
  ext <;> simp [negC, variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆] <;> ring

lemma negC_ne_one (W : WeierstrassCurve K) [W.IsElliptic] : negC W ≠ 1 := by
  intro h
  have hu : ((-1 : Kˣ) : K) = 1 := by
    have := congrArg (fun C : VariableChange K => (C.u : K)) h; (simp [negC] at this; exact this)
  have hs : -W.a₁ = 0 := by
    have := congrArg VariableChange.s h; simpa [negC, VariableChange.one_def] using this
  have ht : -W.a₃ = 0 := by
    have := congrArg VariableChange.t h; simpa [negC, VariableChange.one_def] using this
  have h2 : (2 : K) = 0 := by
    have : (-1 : K) = 1 := by simpa using hu
    linear_combination -this
  have ha₁ : W.a₁ = 0 := by linear_combination -hs
  have ha₃ : W.a₃ = 0 := by linear_combination -ht
  apply W.isUnit_Δ.ne_zero
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, ha₁, ha₃]
  linear_combination (-8 * W.a₂ ^ 2 * (4 * W.a₂ * W.a₆ - W.a₄ ^ 2) - 32 * W.a₄ ^ 3
    - 216 * W.a₆ ^ 2 + 144 * W.a₂ * W.a₄ * W.a₆) * h2

lemma vcXInv_negC (W : WeierstrassCurve K) (x : K) : vcXInv (negC W) x = x := by
  simp [vcXInv, negC]

lemma vcYInv_negC (W : WeierstrassCurve K) (x y : K) :
    vcYInv (negC W) x y = W.toAffine.negY x y := by
  simp only [vcYInv, negC, Affine.negY, inv_neg, inv_one, Units.val_neg, Units.val_one]
  simp; ring

end Coord

section Frame

variable (K : Type*) [Field K] {M : Type*} [Field M] [Algebra (RatFunc K) M] [Algebra K M]
  [IsScalarTower K (RatFunc K) M]

def tt : M := algebraMap (RatFunc K) M RatFunc.X

lemma transcendental_tt : Transcendental K (tt K (M := M)) :=
  (transcendental_algebraMap_iff (algebraMap (RatFunc K) M).injective).mpr
    RatFunc.transcendental_X

lemma algebraMap_mem_adjoin (f : RatFunc K) : algebraMap (RatFunc K) M f ∈ K⟮tt K (M := M)⟯ := by
  rw [IntermediateField.mem_adjoin_simple_iff]
  refine ⟨f.num, f.denom, ?_⟩
  have key : ∀ p : Polynomial K, Polynomial.aeval (tt K (M := M)) p =
      algebraMap (RatFunc K) M (algebraMap (Polynomial K) (RatFunc K) p) := by
    intro p
    rw [tt, ← RatFunc.algebraMap_X, Polynomial.aeval_algebraMap_apply,
      Polynomial.aeval_algebraMap_apply, Polynomial.aeval_X_left_apply]
  rw [key, key, ← map_div₀, RatFunc.num_div_denom]

def toAdjoin : RatFunc K →+* K⟮tt K (M := M)⟯ where
  toFun f := ⟨algebraMap (RatFunc K) M f, algebraMap_mem_adjoin K f⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' f g := Subtype.ext (map_mul _ f g)
  map_zero' := Subtype.ext (map_zero _)
  map_add' f g := Subtype.ext (map_add _ f g)

@[scoped simp] lemma coe_toAdjoin (f : RatFunc K) :
    ((toAdjoin K f : K⟮tt K (M := M)⟯) : M) = algebraMap (RatFunc K) M f := rfl

lemma finiteDimensional_isGalois_adjoin [FiniteDimensional (RatFunc K) M] [IsGalois (RatFunc K) M] :
    FiniteDimensional K⟮tt K (M := M)⟯ M ∧ IsGalois K⟮tt K (M := M)⟯ M := by
  let : Algebra (RatFunc K) K⟮tt K (M := M)⟯ := (toAdjoin K).toAlgebra
  have : IsScalarTower (RatFunc K) K⟮tt K (M := M)⟯ M :=
    IsScalarTower.of_algebraMap_eq fun f => rfl
  exact ⟨Module.Finite.of_restrictScalars_finite (RatFunc K) _ M,
    IsGalois.tower_top_of_isGalois (RatFunc K) _ M⟩

def toRatFuncAlgEquiv (σ : M ≃ₐ[K⟮tt K (M := M)⟯] M) : M ≃ₐ[RatFunc K] M :=
  { (σ : M ≃+* M) with
    commutes' := fun f => σ.commutes (toAdjoin K f) }

@[scoped simp] lemma toRatFuncAlgEquiv_apply (σ : M ≃ₐ[K⟮tt K (M := M)⟯] M) (x : M) :
    toRatFuncAlgEquiv K σ x = σ x := rfl

lemma coe_toRatFuncAlgEquiv (σ : M ≃ₐ[K⟮tt K (M := M)⟯] M) :
    ((toRatFuncAlgEquiv K σ : M ≃ₐ[RatFunc K] M) : M →+* M) = (σ : M →+* M) := rfl

lemma toRatFuncAlgEquiv_eq_one_iff (σ : M ≃ₐ[K⟮tt K (M := M)⟯] M) :
    toRatFuncAlgEquiv K σ = 1 ↔ σ = 1 := by
  constructor <;> intro h <;> ext x
  · exact congrArg (fun τ : M ≃ₐ[RatFunc K] M => τ x) h
  · exact congrArg (fun τ : M ≃ₐ[K⟮tt K (M := M)⟯] M => τ x) h

lemma toRatFuncAlgEquiv_mem_decompositionSubgroup_iff (σ : M ≃ₐ[K⟮tt K (M := M)⟯] M)
    (A : ValuationSubring M) :
    toRatFuncAlgEquiv K σ ∈ A.decompositionSubgroup (RatFunc K) ↔
      σ ∈ A.decompositionSubgroup K⟮tt K (M := M)⟯ := by
  simp only [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff, SetLike.ext_iff,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  exact Iff.rfl

variable [IsAlgClosed K]

lemma adjoin_toSubring_eq_closure (t : M) :
    (Algebra.adjoin K ({t} : Set M)).toSubring =
      Subring.closure (Set.range ((algebraMap K M).comp (⊤ : ValuationSubring K).subtype) ∪ {t}) := by
  have hr : Set.range ((algebraMap K M).comp (⊤ : ValuationSubring K).subtype) =
      Set.range (algebraMap K M) := by
    ext x; constructor
    · rintro ⟨a, rfl⟩; exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩; exact ⟨⟨a, ValuationSubring.mem_top a⟩, rfl⟩
  rw [hr]
  ext x
  rw [Subalgebra.mem_toSubring, Algebra.mem_adjoin_iff]

lemma exists_place_ord_pos [FiniteDimensional K⟮tt K (M := M)⟯ M] [IsGalois K⟮tt K (M := M)⟯ M]
    (j₀ : K) : ∃ W₀ : Place K M, 0 < W₀.ord (tt K (M := M) - algebraMap K M j₀) := by
  set t : M := tt K (M := M) with ht
  have htr : Transcendental K t := transcendental_tt K
  let A : ValuationSubring K := ⊤
  let B : Subring M := (Algebra.adjoin K ({t} : Set M)).toSubring
  have hconst : ∀ a : A, algebraMap K M a ∈ B := fun a =>
    (Algebra.adjoin K ({t} : Set M)).algebraMap_mem a
  have htB : t ∈ B := Algebra.self_mem_adjoin_singleton K t
  have hint : ∀ b : B, IsIntegral
      (Subring.closure (Set.range ((algebraMap K M).comp A.subtype) ∪ {t})) (b : M) := by
    intro b
    have hb : (b : M) ∈ Subring.closure (Set.range ((algebraMap K M).comp A.subtype) ∪ {t}) := by
      rw [← adjoin_toSubring_eq_closure]; exact b.2
    exact isIntegral_algebraMap (A := M)
      (x := (⟨(b : M), hb⟩ : Subring.closure (Set.range ((algebraMap K M).comp A.subtype) ∪ {t})))

  let g : B := ⟨t, htB⟩ - ⟨algebraMap K M j₀, hconst ⟨j₀, ValuationSubring.mem_top j₀⟩⟩
  have hg : ¬ IsUnit g := by
    intro hu
    let e := Polynomial.algEquivOfTranscendental K t htr
    have hge : e (Polynomial.X - Polynomial.C j₀) = g := by
      apply Subtype.ext
      simp [e, g, Polynomial.algEquivOfTranscendental_apply]
    have : IsUnit (Polynomial.X - Polynomial.C j₀ : Polynomial K) := by
      rw [← hge] at hu
      exact (MulEquiv.isUnit_map e).mp hu
    exact Polynomial.not_isUnit_X_sub_C j₀ this
  obtain ⟨𝔮, h𝔮max, hg𝔮⟩ := Ideal.exists_le_maximal (Ideal.span {g}) (Ideal.span_singleton_ne_top hg)
  have : 𝔮.IsPrime := h𝔮max.isPrime
  have h𝔮A : ∀ a : A, a ∈ IsLocalRing.maximalIdeal A →
      (⟨algebraMap K M a, hconst a⟩ : B) ∈ 𝔮 := by
    intro a ha
    have ha0 : a = 0 := by
      by_contra hne
      apply (IsLocalRing.mem_maximalIdeal _).mp ha
      have hne' : (a : K) ≠ 0 := fun h => hne (Subtype.ext h)
      exact ⟨⟨a, ⟨(a : K)⁻¹, ValuationSubring.mem_top _⟩,
        Subtype.ext (mul_inv_cancel₀ hne'), Subtype.ext (inv_mul_cancel₀ hne')⟩, rfl⟩
    have : (⟨algebraMap K M a, hconst a⟩ : B) = 0 := by
      apply Subtype.ext; simp [ha0]
    rw [this]; exact 𝔮.zero_mem
  have hja : (⟨t, htB⟩ : B) - ⟨algebraMap K M ((⟨j₀, ValuationSubring.mem_top j₀⟩ : A) : K),
      hconst _⟩ ∈ 𝔮 := hg𝔮 (Ideal.mem_span_singleton_self g)
  obtain ⟨w, hw, -⟩ := AlgebraicCurve.Place.exists_of_isPrime_over_valuationSubring A htr hconst htB
    hint 𝔮 h𝔮A ⟨j₀, ValuationSubring.mem_top j₀⟩ hja
  exact ⟨w, hw⟩

end Frame

section Residue

variable {K : Type*} [Field K] [IsAlgClosed K] {M : Type*} [Field M] [Algebra K M]
  (W₀ : Place K M)

lemma bijective_algebraMap_residueField (hdeg : W₀.deg ≠ 0) :
    Function.Bijective (algebraMap K W₀.ResidueField) := by
  have : Module.Finite K W₀.ResidueField :=
    Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hdeg)
  have : Algebra.IsIntegral K W₀.ResidueField := Algebra.IsIntegral.of_finite K _
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

def resK (hdeg : W₀.deg ≠ 0) : W₀.ResidueField ≃+* K :=
  (RingEquiv.ofBijective (algebraMap K W₀.ResidueField)
    (bijective_algebraMap_residueField W₀ hdeg)).symm

lemma resK_algebraMap (hdeg : W₀.deg ≠ 0) (c : K) :
    resK W₀ hdeg (algebraMap K W₀.ResidueField c) = c :=
  (RingEquiv.ofBijective (algebraMap K W₀.ResidueField)
    (bijective_algebraMap_residueField W₀ hdeg)).symm_apply_apply c

lemma algebraMap_resK (hdeg : W₀.deg ≠ 0) (r : W₀.ResidueField) :
    algebraMap K W₀.ResidueField (resK W₀ hdeg r) = r :=
  (RingEquiv.ofBijective (algebraMap K W₀.ResidueField)
    (bijective_algebraMap_residueField W₀ hdeg)).apply_symm_apply r

def toK (hdeg : W₀.deg ≠ 0) : W₀.toValuationSubring →+* K :=
  (resK W₀ hdeg).toRingHom.comp (residue W₀.toValuationSubring)

lemma toK_apply (hdeg : W₀.deg ≠ 0) (a : W₀.toValuationSubring) :
    toK W₀ hdeg a = resK W₀ hdeg (residue _ a) := rfl

lemma toK_algebraMap (hdeg : W₀.deg ≠ 0) (c : K) :
    toK W₀ hdeg (algebraMap K W₀.toValuationSubring c) = c := by
  rw [toK_apply]
  exact resK_algebraMap W₀ hdeg c

lemma toK_eq_toK_of_sub_mem (hdeg : W₀.deg ≠ 0) {a b : W₀.toValuationSubring}
    (h : a - b ∈ IsLocalRing.maximalIdeal W₀.toValuationSubring) : toK W₀ hdeg a = toK W₀ hdeg b := by
  rw [toK_apply, toK_apply]
  congr 1
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  exact h

lemma mem_maximalIdeal_of_ord_pos {f : M} (hf : 0 < W₀.ord f) :
    ∃ hfA : f ∈ W₀.toValuationSubring, (⟨f, hfA⟩ : W₀.toValuationSubring) ∈
      IsLocalRing.maximalIdeal W₀.toValuationSubring := by
  have hf0 : f ≠ 0 := by rintro rfl; simp at hf
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W₀.toValuationSubring
  obtain ⟨u, hu⟩ := W₀.exists_unit_mul_zpow hf0 hπ
  have hn : W₀.ord f = (((W₀.ord f).toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg hf.le).symm
  have hn0 : (W₀.ord f).toNat ≠ 0 := by omega
  set a : W₀.toValuationSubring := (u : W₀.toValuationSubring) * π ^ (W₀.ord f).toNat with ha
  have hfa : f = (a : M) := by
    rw [hu, hn, zpow_natCast, ha]; push_cast; rfl
  refine ⟨hfa ▸ a.2, ?_⟩
  have : (⟨f, hfa ▸ a.2⟩ : W₀.toValuationSubring) = a := Subtype.ext hfa
  rw [this, ha]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ (hπ.maximalIdeal_eq ▸
    Ideal.mem_span_singleton_self π) _ (Nat.pos_of_ne_zero hn0))

lemma isUnit_of_ord_eq_zero {a : W₀.toValuationSubring} (ha : (a : M) ≠ 0) (h : W₀.ord (a : M) = 0) :
    IsUnit a := by
  by_contra hna
  have hmem : a ∈ IsLocalRing.maximalIdeal W₀.toValuationSubring :=
    (IsLocalRing.mem_maximalIdeal a).mpr hna
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W₀.toValuationSubring
  rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
  obtain ⟨b, hb⟩ := hmem
  have hb0 : (b : M) ≠ 0 := by
    intro h0; apply ha; rw [hb]; push_cast; rw [h0, mul_zero]
  have hπ0 : (π : M) ≠ 0 := by
    intro h0; exact hπ.ne_zero (Subtype.ext h0)
  have h1 : W₀.ord (a : M) = 1 + W₀.ord (b : M) := by
    rw [hb]; push_cast; rw [W₀.ord_mul hπ0 hb0, W₀.ord_coe_irreducible hπ]
  have h2 : 0 ≤ W₀.ord (b : M) := by
    obtain ⟨u, hu⟩ := W₀.exists_unit_mul_zpow hb0 hπ
    by_contra hneg
    push Not at hneg

    have hinv : ((π : M)⁻¹) ∈ W₀.toValuationSubring := by
      have hn : W₀.ord (b : M) = -(((-W₀.ord (b : M)).toNat : ℕ) : ℤ) := by omega
      set n := (-W₀.ord (b : M)).toNat with hn'
      have hn1 : 1 ≤ n := by omega
      have hb' : (b : M) * (π : M) ^ n = (u : W₀.toValuationSubring) := by
        rw [hu, hn, zpow_neg, zpow_natCast, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hπ0), mul_one]
      have hu' : ((u⁻¹ : W₀.toValuationSubringˣ) : W₀.toValuationSubring) * (b * π ^ n) = 1 := by
        apply Subtype.ext; push_cast; rw [hb']; norm_cast; simp
      have : (π : M)⁻¹ = ((u⁻¹ : W₀.toValuationSubringˣ) : W₀.toValuationSubring) * b * (π : M) ^ (n - 1) := by
        have h3 := congrArg (fun z : W₀.toValuationSubring => (z : M) * (π : M)⁻¹) hu'
        push_cast at h3
        rw [one_mul] at h3
        rw [← h3]
        rw [show (π : M) ^ n = (π : M) ^ (n - 1) * π by rw [← pow_succ]; congr 1; omega]
        field_simp
      rw [this]
      exact mul_mem (mul_mem (SetLike.coe_mem _) b.2) (pow_mem π.2 _)
    apply hπ.not_isUnit
    exact ⟨⟨π, ⟨(π : M)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hπ0),
      Subtype.ext (inv_mul_cancel₀ hπ0)⟩, rfl⟩
  omega

lemma ord_eq_zero_of_isUnit {a : W₀.toValuationSubring} (ha : IsUnit a) : W₀.ord (a : M) = 0 :=
  W₀.ord_coe_unit ha.unit

lemma mem_inertia_of_mem_decomposition (hdeg : W₀.deg ≠ 0) {E : Type*} [Field E] [Algebra K E]
    [Algebra E M] [IsScalarTower K E M] {σ : M ≃ₐ[E] M}
    (hσ : σ ∈ W₀.toValuationSubring.decompositionSubgroup E) :
    (⟨σ, hσ⟩ : W₀.toValuationSubring.decompositionSubgroup E) ∈
      W₀.toValuationSubring.inertiaSubgroup E := by
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
  apply RingEquiv.ext
  intro r
  show (⟨σ, hσ⟩ : W₀.toValuationSubring.decompositionSubgroup E) • r = r
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
  obtain ⟨c, hc⟩ := (bijective_algebraMap_residueField W₀ hdeg).2 (residue _ a)
  have hc' : residue _ a = residue _ (algebraMap K W₀.toValuationSubring c) := hc.symm
  rw [hc', ← IsLocalRing.ResidueField.residue_smul]
  congr 1
  apply Subtype.ext
  show σ (algebraMap K M c) = algebraMap K M c
  rw [IsScalarTower.algebraMap_apply K E M, σ.commutes]

end Residue

section Stab

variable {K : Type*} [Field K] {M : Type*} [Field M] [Algebra K M] {E : Type*} [Field E]
  [Algebra K E] [Algebra E M] [IsScalarTower K E M]

lemma smul_place_eq_iff (σ : M ≃ₐ[E] M) (W₀ : Place K M) :
    SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ ↔
      σ ∈ W₀.toValuationSubring.decompositionSubgroup E := by
  rw [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff, Place.ext_iff,
    SemilinearAut.smul_toValuationSubring]
  have key : SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀.toValuationSubring =
      σ • W₀.toValuationSubring := by
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, SemilinearAut.ofAlgAut_smul]
    rfl
  rw [key]

lemma isIntegral_of_apply_gen_eq (t : M) [FiniteDimensional K⟮t⟯ M] (ψ : K⟮t⟯ →ₐ[K] M)
    (hψ : ψ ⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ = t) : ψ.toRingHom.IsIntegral := by
  have hψ' : ψ = IntermediateField.val K⟮t⟯ := by
    apply IntermediateField.adjoin_algHom_ext K
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hψ
  rw [hψ']
  intro x
  exact Algebra.IsIntegral.isIntegral (R := K⟮t⟯) x

end Stab

section PointLemmas

variable {M : Type*} [Field M] [DecidableEq M]

lemma vcInvFun_eq_zero_iff (C : VariableChange M) (V : Affine M) (P : V.Point) :
    vcInvFun C V P = 0 ↔ P = 0 := by
  cases P with
  | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | some x y h => exact ⟨fun h => absurd h (Point.some_ne_zero _), fun h => absurd h (Point.some_ne_zero _)⟩

lemma vcInvFun_some (C : VariableChange M) (V : Affine M) {x y : M} (h : V.Nonsingular x y) :
    vcInvFun C V (.some x y h) = .some (vcXInv C x) (vcYInv C x y)
      ((nonsingular_variableChange_iff (vcXInv C x) (vcYInv C x y)).mpr
        (by rwa [vcX_vcXInv, vcY_vcYInv])) := rfl

def vcInvAddHom (C : VariableChange M) (V : Affine M) : V.Point →+ (C • V).toAffine.Point where
  toFun := vcInvFun C V
  map_zero' := vcInvFun_zero
  map_add' := vcInvFun_add C V

@[scoped simp] lemma vcInvAddHom_apply (C : VariableChange M) (V : Affine M) (P : V.Point) :
    vcInvAddHom C V P = vcInvFun C V P := rfl

lemma VariableChange.map_mul' {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (C C' : VariableChange R) : (C * C').map φ = C.map φ * C'.map φ :=
  (VariableChange.mapHom φ).map_mul C C'

lemma VariableChange.map_inv' {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (C : VariableChange R) : C⁻¹.map φ = (C.map φ)⁻¹ :=
  (VariableChange.mapHom φ).map_inv C

lemma map_ofJNe0Or1728 {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (j : R) :
    (ofJNe0Or1728 j).map φ = ofJNe0Or1728 (φ j) := by
  simp only [ofJNe0Or1728, WeierstrassCurve.map]
  ext <;> simp [map_ofNat]

end PointLemmas

section Main

universe u

variable (K : Type u) [Field K] [IsAlgClosed K] [DecidableEq K] (p : ℕ) [CharP K p]
    (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) (j₀ : K)
    (E₀ : WeierstrassCurve K) [E₀.IsElliptic] (hE₀ : E₀.j = j₀)

local notation "𝓕" => RatFunc K
local notation "𝓞" => AlgebraicClosure (RatFunc K)

omit [IsAlgClosed K] [DecidableEq K] [CharP K p] [NeZero N] [E₀.IsElliptic] in

lemma j_congr {R : Type*} [CommRing R] {V₁ V₂ : WeierstrassCurve R} [V₁.IsElliptic] [V₂.IsElliptic]
    (h : V₁ = V₂) : V₁.j = V₂.j := by subst h; rfl

private lemma torsion_card_eq_sq
    {Ω : Type u} [Field Ω] [DecidableEq Ω] [IsAlgClosed Ω] [Algebra K Ω]
    [Algebra (RatFunc K) Ω] [IsScalarTower K (RatFunc K) Ω]
    (Mi : IntermediateField (RatFunc K) Ω) (t : Mi) (E' : WeierstrassCurve K⟮t⟯)
    (EF : WeierstrassCurve (RatFunc K)) [EF.IsElliptic]
    (hEE' : (EF.baseChange Mi).toAffine = (E'.baseChange Mi).toAffine)
    (hNF : (N : RatFunc K) ≠ 0)
    (L₁ : IntermediateField (RatFunc K) Ω) (hL₁M : L₁ ≤ Mi)
    (hL₁card : Nat.card {P : (EF.baseChange L₁).toAffine.Point // N • P = 0} = N ^ 2) :
    Nat.card {P : (E'.baseChange Mi).toAffine.Point // N • P = 0} = N ^ 2 := by
  let ι₁ : L₁ →ₐ[𝓕] Mi := IntermediateField.inclusion hL₁M
  let f₁ : (EF.baseChange L₁).toAffine.Point →+ (E'.baseChange Mi).toAffine.Point :=
    (castAddHom hEE').comp (Point.map ι₁)
  have hf₁ : Function.Injective f₁ := (castPt_injective hEE').comp (Point.map_injective ι₁)
  let f₂ : (E'.baseChange Mi).toAffine.Point →+ (EF.baseChange Ω).toAffine.Point :=
    (Point.map (IntermediateField.val Mi)).comp (castAddHom hEE'.symm)
  have hf₂ : Function.Injective f₂ :=
    (Point.map_injective (IntermediateField.val Mi)).comp (castPt_injective hEE'.symm)
  let g₁ : {P : (EF.baseChange L₁).toAffine.Point // N • P = 0} →
      {P : (E'.baseChange Mi).toAffine.Point // N • P = 0} :=
    fun P => ⟨f₁ P.1, by rw [← map_nsmul, P.2, _root_.map_zero]⟩
  have hg₁ : Function.Injective g₁ := fun P Q h =>
    Subtype.ext (hf₁ (congrArg Subtype.val h))
  let g₂ : {P : (E'.baseChange Mi).toAffine.Point // N • P = 0} →
      {P : (EF.baseChange Ω).toAffine.Point // N • P = 0} :=
    fun P => ⟨f₂ P.1, by rw [← map_nsmul, P.2, _root_.map_zero]⟩
  have hg₂ : Function.Injective g₂ := fun P Q h =>
    Subtype.ext (hf₂ (congrArg Subtype.val h))
  have hNΩ : (N : Ω) ≠ 0 := by
    rw [show (N : Ω) = algebraMap 𝓕 Ω N by norm_num]
    exact (map_ne_zero _).mpr hNF
  obtain ⟨eΩ⟩ := WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
    (K := Ω) EF hNΩ
  have hTΩ : Nat.card {P : (EF.baseChange Ω).toAffine.Point // N • P = 0} = N ^ 2 := by
    have e2 : {P : (EF.baseChange Ω).toAffine.Point // N • P = 0} ≃
        Submodule.torsionBy ℤ (EF.baseChange Ω).toAffine.Point N :=
      Equiv.subtypeEquivRight fun P => by
        rw [Submodule.mem_torsionBy_iff, natCast_zsmul]
    rw [Nat.card_congr e2, ← Nat.card_congr eΩ.toEquiv, Nat.card_prod, Nat.card_zmod, sq]
  have : Finite {P : (EF.baseChange Ω).toAffine.Point // N • P = 0} :=
    Nat.finite_of_card_ne_zero (by rw [hTΩ]; exact pow_ne_zero _ (NeZero.ne N))
  have : Finite {P : (E'.baseChange Mi).toAffine.Point // N • P = 0} :=
    Finite.of_injective g₂ hg₂
  apply le_antisymm
  · calc Nat.card {P : (E'.baseChange Mi).toAffine.Point // N • P = 0}
        ≤ Nat.card {P : (EF.baseChange Ω).toAffine.Point // N • P = 0} :=
          Nat.card_le_card_of_injective g₂ hg₂
      _ = N ^ 2 := hTΩ
  · calc N ^ 2 = Nat.card {P : (EF.baseChange L₁).toAffine.Point // N • P = 0} := hL₁card.symm
      _ ≤ Nat.card {P : (E'.baseChange Mi).toAffine.Point // N • P = 0} :=
          Nat.card_le_card_of_injective g₁ hg₁

/-- The residue-induced variable change is multiplicative: `gK` is `g` followed by the residue map
and the identification of the residue field with `K`, and `g` is multiplicative in the inertia
subgroup, so the conjugate `γ₀ * gK σ * γ₀⁻¹` is multiplicative too. -/
private lemma gK_conj_mul
    {Ω : Type u} [Field Ω] [DecidableEq Ω] [Algebra K Ω] [Algebra (RatFunc K) Ω]
    [IsScalarTower K (RatFunc K) Ω]
    (Mi : IntermediateField (RatFunc K) Ω) (t : Mi) (W₀ : Place K Mi) (hdeg : W₀.deg ≠ 0)
    (g : (Mi ≃ₐ[K⟮t⟯] Mi) → VariableChange W₀.toValuationSubring)
    (gK : (Mi ≃ₐ[K⟮t⟯] Mi) → VariableChange K) (γ₀ : VariableChange K)
    (hgK : ∀ σ, gK σ =
      ((g σ).map (residue W₀.toValuationSubring)).map (resK W₀ hdeg).toRingHom)
    (hmul : ∀ (σ τ : Mi ≃ₐ[K⟮t⟯] Mi)
      (hσ : σ ∈ W₀.toValuationSubring.decompositionSubgroup K⟮t⟯)
      (hτ : τ ∈ W₀.toValuationSubring.decompositionSubgroup K⟮t⟯),
      (⟨σ, hσ⟩ : W₀.toValuationSubring.decompositionSubgroup K⟮t⟯) ∈
        W₀.toValuationSubring.inertiaSubgroup K⟮t⟯ →
      (⟨τ, hτ⟩ : W₀.toValuationSubring.decompositionSubgroup K⟮t⟯) ∈
        W₀.toValuationSubring.inertiaSubgroup K⟮t⟯ →
      (g (σ * τ)).map (residue W₀.toValuationSubring) =
        (g σ).map (residue W₀.toValuationSubring) * (g τ).map (residue W₀.toValuationSubring))
    (σ τ : Mi ≃ₐ[K⟮t⟯] Mi)
    (hσ : σ ∈ W₀.toValuationSubring.decompositionSubgroup K⟮t⟯)
    (hτ : τ ∈ W₀.toValuationSubring.decompositionSubgroup K⟮t⟯)
    (hσI : (⟨σ, hσ⟩ : W₀.toValuationSubring.decompositionSubgroup K⟮t⟯) ∈
      W₀.toValuationSubring.inertiaSubgroup K⟮t⟯)
    (hτI : (⟨τ, hτ⟩ : W₀.toValuationSubring.decompositionSubgroup K⟮t⟯) ∈
      W₀.toValuationSubring.inertiaSubgroup K⟮t⟯) :
    γ₀ * gK (σ * τ) * γ₀⁻¹ = (γ₀ * gK σ * γ₀⁻¹) * (γ₀ * gK τ * γ₀⁻¹) := by
  have h1 : gK (σ * τ) = gK σ * gK τ := by
    rw [hgK, hgK, hgK, hmul σ τ hσ hτ hσI hτI, VariableChange.map_mul']
  rw [h1]; group

/-- Faithful torsion action: if `τ` fixes the `n`-torsion points of `E` over `Mi`, and `L` is a
Galois intermediate field on which every twisting automorphism that fixes the `n`-torsion is trivial,
then `τ` fixes `L` pointwise. -/
private lemma eq_of_forall_nsmul_eq_of_faithful
    {F : Type u} {Ω : Type u} [Field F] [Field Ω] [Algebra F Ω] [DecidableEq Ω]
    (E : WeierstrassCurve F) [E.IsElliptic]
    (Mi : IntermediateField F Ω) (L : IntermediateField F Ω) [IsGalois F L] (hL : L ≤ Mi)
    (n : ℕ) (τ : Mi ≃ₐ[F] Mi)
    (faithful : ∀ τ' : L ≃ₐ[F] L, (∀ P : (E.baseChange L).toAffine.Point, n • P = 0 →
        Point.map (τ' : L →ₐ[F] L) P = P) → τ' = 1)
    (hfixQ : ∀ Q : (E.baseChange Mi).toAffine.Point, n • Q = 0 →
      Point.map (τ : Mi →ₐ[F] Mi) Q = Q)
    (x : Mi) (hx : (x : Ω) ∈ L) : τ x = x := by
  let ι : L →ₐ[F] Mi := IntermediateField.inclusion hL
  let : Algebra L Mi := (ι : L →+* Mi).toAlgebra
  have : IsScalarTower F L Mi := IsScalarTower.of_algebraMap_eq (fun z => (ι.commutes z).symm)
  let τ' : L ≃ₐ[F] L := τ.restrictNormal L
  have hτ' : ∀ z : L, ι (τ' z) = τ (ι z) := fun z => AlgEquiv.restrictNormal_commutes τ L z
  have hτ'1 : τ' = 1 := by
    apply faithful
    intro P hP
    apply Point.map_injective ι
    have h1 : Point.map ι (Point.map (τ' : L →ₐ[F] L) P) =
        Point.map (τ : Mi →ₐ[F] Mi) (Point.map ι P) := by
      rcases P with _ | ⟨x, y, hxy⟩
      · rfl
      · simp only [Point.map_some]
        exact some_congr (hτ' x) (hτ' y) _ _
    rw [h1]
    exact hfixQ _ (by rw [← map_nsmul, hP, _root_.map_zero])
  have h2 := hτ' ⟨x, hx⟩
  rw [hτ'1, AlgEquiv.one_apply] at h2
  have h3 : ι ⟨x, hx⟩ = x := Subtype.ext rfl
  rw [h3] at h2
  exact h2.symm

include hE₀ in
private lemma exists_good_model_route
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] [Algebra (RatFunc K) Ω]
    [Algebra.IsAlgebraic (RatFunc K) Ω]
    (EF : WeierstrassCurve (RatFunc K)) [EF.IsElliptic] :
    ∃ m : ℕ, (m : K) ≠ 0 ∧ (p = 2 → m = 3) ∧
      ∃ S : IntermediateField (RatFunc K) Ω, FiniteDimensional (RatFunc K) S ∧
        IsGalois (RatFunc K) S ∧
      ∀ (Mi : IntermediateField (RatFunc K) Ω), S ≤ Mi →
      ∀ (A : ValuationSubring Mi), IsUnit ((m : ℕ) : A) → algebraMap (RatFunc K) Mi EF.j ∈ A →
      ∃ (W : WeierstrassCurve A) (κ : VariableChange Mi),
        κ • EF.baseChange Mi = W.map A.subtype ∧ IsUnit W.Δ ∧
        ∀ (σ : Mi ≃ₐ[RatFunc K] Mi) (hσ : σ ∈ A.decompositionSubgroup (RatFunc K)),
          (⟨σ, hσ⟩ : A.decompositionSubgroup (RatFunc K)) ∈ A.inertiaSubgroup (RatFunc K) →
          (∀ P : (EF.baseChange Mi).toAffine.Point, m • P = 0 →
              Point.map (σ : Mi →ₐ[RatFunc K] Mi) P = P) →
          (∃ g : VariableChange A, g.map A.subtype = κ * (κ.map (σ : Mi →+* Mi))⁻¹ ∧
              g.map (residue A) = 1) →
          ∀ x : Mi, (x : Ω) ∈ S → σ x = x := by
  by_cases hp2 : p = 2
  · refine ⟨3, ?_, fun _ => rfl, ?_⟩
    · subst hp2
      intro h3
      have h32 : (2 : ℕ) ∣ 3 := (CharP.cast_eq_zero_iff K 2 3).mp (by exact_mod_cast h3)
      omega
    · have h3F : (3 : 𝓕) ≠ 0 := by
        subst hp2
        have : CharP 𝓕 2 := charP_of_injective_ringHom (algebraMap K 𝓕).injective 2
        intro h3
        have h32 : (2 : ℕ) ∣ 3 := (CharP.cast_eq_zero_iff 𝓕 2 3).mp (by exact_mod_cast h3)
        omega
      obtain ⟨S, hSfd, hSgal, hS⟩ :=
        WeierstrassCurve.exists_isGalois_goodModel_inertia_faithful_of_three_ne_zero (Ω := Ω) EF h3F
      refine ⟨S, hSfd, hSgal, fun Mi hMi A hmA hjA => ?_⟩
      exact hS Mi hMi A (by simpa using hmA) hjA
  · refine ⟨2, ?_, fun h => absurd h hp2, ?_⟩
    · intro h2
      have h22 : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h2)
      rcases (Nat.dvd_prime Nat.prime_two).mp h22 with h1 | h1
      · subst h1
        have h10 := CharP.cast_eq_zero K 1
        rw [Nat.cast_one] at h10
        exact one_ne_zero h10
      · exact hp2 h1
    · have h2F : (2 : 𝓕) ≠ 0 := by
        have : CharP 𝓕 p := charP_of_injective_ringHom (algebraMap K 𝓕).injective p
        intro h2
        have h22 : p ∣ 2 := (CharP.cast_eq_zero_iff 𝓕 p 2).mp (by exact_mod_cast h2)
        rcases (Nat.dvd_prime Nat.prime_two).mp h22 with h1 | h1
        · subst h1
          have h10 := CharP.cast_eq_zero K 1
          rw [Nat.cast_one] at h10
          exact one_ne_zero h10
        · exact hp2 h1
      obtain ⟨S, hSfd, hSgal, hS⟩ :=
        WeierstrassCurve.exists_isGalois_goodModel_inertia_faithful_of_two_ne_zero (Ω := Ω) EF h2F
      refine ⟨S, hSfd, hSgal, fun Mi hMi A hmA hjA => ?_⟩
      exact hS Mi hMi A (by simpa using hmA) hjA

include hE₀ in
private lemma stabilizer_card_bound
    {Ω : Type u} [Field Ω] [DecidableEq Ω] [Algebra K Ω] [Algebra (RatFunc K) Ω]
    [IsScalarTower K (RatFunc K) Ω]
    (Mi : IntermediateField (RatFunc K) Ω) (t : Mi) (htr : Transcendental K t)
    (EF : WeierstrassCurve (RatFunc K)) (hEF : EF = ofJNe0Or1728 (RatFunc.X : RatFunc K))
    (hXt : algebraMap (RatFunc K) Mi RatFunc.X = t)
    (E' : WeierstrassCurve K⟮t⟯) (hEE : EF.baseChange Mi = E'.baseChange Mi)
    (hEE' : (EF.baseChange Mi).toAffine = (E'.baseChange Mi).toAffine)
    (W₀ : Place K Mi) (e : ℕ)
    (hcardD : W₀.ord (t - algebraMap K Mi j₀) = e) (hepos : 0 < e)
    (htA : t ∈ W₀.toValuationSubring)
    (htjA : t - algebraMap K Mi j₀ ∈ W₀.toValuationSubring)
    (htj𝔪 : (⟨t - algebraMap K Mi j₀, htjA⟩ : W₀.toValuationSubring) ∈
      IsLocalRing.maximalIdeal W₀.toValuationSubring)
    (W : WeierstrassCurve W₀.toValuationSubring) (κ : VariableChange Mi)
    (hκ : κ • E'.baseChange Mi = W.map W₀.toValuationSubring.subtype) (hΔ : IsUnit W.Δ)
    (m : ℕ) (hmK : (m : K) ≠ 0) (hm3 : p = 2 → m = 3)
    (Lm : IntermediateField (RatFunc K) Ω) (hLmM : Lm ≤ Mi)
    (hLmcard : Nat.card {P : (EF.baseChange Lm).toAffine.Point //
      m • P = (0 : (EF.baseChange Lm).toAffine.Point)} = m ^ 2) :
    Nat.card (MulAction.stabilizer (VariableChange K) E₀) ≤ e ∨
      Nat.card (MulAction.stabilizer (VariableChange K) E₀) ≤ 2 := by
  let A : ValuationSubring Mi := W₀.toValuationSubring
  have ht0 : t ≠ 0 := fun h => htr (h ▸ isAlgebraic_zero)
  have ht1728 : (t : Mi) - 1728 ≠ 0 := by
    intro h; apply htr
    rw [sub_eq_zero.mp h, show (1728 : Mi) = algebraMap K Mi 1728 from (map_ofNat _ 1728).symm]
    exact isAlgebraic_algebraMap _
  have hΔE : (E'.baseChange Mi).Δ = t ^ 2 * (t - 1728) ^ 9 := by
    rw [← hEE, WeierstrassCurve.baseChange, hEF, map_ofJNe0Or1728, hXt, ofJNe0Or1728_Δ]
  have h12 : (12 : ℤ) ∣ (2 * W₀.ord t + 9 * W₀.ord (t - 1728)) := by
    have h1 := congrArg WeierstrassCurve.Δ hκ
    rw [variableChange_Δ, map_Δ, hΔE] at h1
    have h2 := congrArg W₀.ord h1
    rw [W₀.ord_mul (pow_ne_zero _ (Units.ne_zero _))
      (mul_ne_zero (pow_ne_zero _ ht0) (pow_ne_zero _ ht1728)),
      W₀.ord_mul (pow_ne_zero _ ht0) (pow_ne_zero _ ht1728)] at h2
    simp only [← zpow_natCast, Place.ord_zpow] at h2
    rw [show W₀.ord ((A.subtype) W.Δ) = 0 from ord_eq_zero_of_isUnit W₀ hΔ] at h2
    push_cast at h2
    rw [W₀.ord_inv] at h2
    exact ⟨W₀.ord ((κ.u : Miˣ) : Mi), by linarith⟩

  have hunitK : ∀ (a : A) (c : K), c ≠ 0 →
      a - algebraMap K A c ∈ IsLocalRing.maximalIdeal A → IsUnit a := by
    intro a c hc hm
    by_contra hna
    have ha : a ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).mpr hna
    have h1 : algebraMap K A c ∈ IsLocalRing.maximalIdeal A := by
      have := Ideal.sub_mem _ ha hm; rwa [sub_sub_cancel] at this
    exact (IsLocalRing.mem_maximalIdeal _).mp h1 ((IsUnit.mk0 c hc).map _)
  have hcoe1728 : ((algebraMap K A 1728 : A) : Mi) = 1728 := by
    rw [show algebraMap K A 1728 = (1728 : A) from map_ofNat _ 1728]; rfl
  by_cases h6 : (6 : K) = 0
  ·
    have hp23 : p = 2 ∨ p = 3 := by
      have h6' : p ∣ 2 * 3 := (CharP.cast_eq_zero_iff K p 6).mp (by exact_mod_cast h6)
      rcases CharP.char_is_prime_or_zero K p with hp | hp
      · rcases (Nat.Prime.dvd_mul hp).mp h6' with h | h
        · left; exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h
        · right; exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h
      · exfalso; rw [hp] at h6'; simp at h6'
    have h1728K : (1728 : K) = 0 := by
      rw [show (1728 : K) = 6 * 288 by norm_num, h6, zero_mul]
    have h1728M : (1728 : Mi) = 0 := by
      rw [show (1728 : Mi) = algebraMap K Mi 1728 from (map_ofNat _ 1728).symm, h1728K,
        _root_.map_zero]
    by_cases hj0 : j₀ = 0
    · left
      have hcardD' : W₀.ord t = e := by rw [← hcardD, hj0, _root_.map_zero, sub_zero]
      have h12e : 12 ∣ e := by
        rw [h1728M, sub_zero, hcardD'] at h12
        omega
      rcases hp23 with hp2 | hp3
      ·
        obtain ⟨-, h24⟩ := (WeierstrassCurve.finite_stabilizer_and_natCard_le_of_j E₀).2.2.2
          (by rw [← hp2]; exact ringChar.eq K p) (hE₀.trans hj0)
        have h8e : 8 ∣ e := by
          have hm : m = 3 := hm3 hp2
          have : CharP Mi 2 := by
            have hK : CharP K p := inferInstance
            rw [hp2] at hK
            exact charP_of_injective_ringHom (algebraMap K Mi).injective 2

          have h9 : 1 < Nat.card {P : (EF.baseChange Lm).toAffine.Point // m • P = 0} := by
            rw [hLmcard, hm]; norm_num
          have : Finite {P : (EF.baseChange Lm).toAffine.Point // m • P = 0} :=
            Nat.finite_of_card_ne_zero (by omega)
          have := Finite.one_lt_card_iff_nontrivial.mp h9
          obtain ⟨⟨P₃, hP₃⟩, hne⟩ := exists_ne
            (⟨0, by rw [smul_zero]⟩ : {P : (EF.baseChange Lm).toAffine.Point // m • P = 0})
          have hP₃ne : P₃ ≠ 0 := fun h => hne (Subtype.ext h)
          let ιm : Lm →ₐ[𝓕] Mi := IntermediateField.inclusion hLmM
          have hQ3 : (3 : ℕ) • castPt hEE' (Point.map ιm P₃) = 0 := by
            rw [← castPt_nsmul, ← map_nsmul, ← hm, hP₃, _root_.map_zero, castPt_zero]
          have hQne : castPt hEE' (Point.map ιm P₃) ≠ 0 := by
            intro h
            apply hP₃ne
            have h' : Point.map ιm P₃ = 0 := (castPt_eq_zero_iff hEE' _).mp h
            exact (Point.map_injective ιm) (h'.trans (_root_.map_zero _).symm)

          have h2M : (2 : Mi) = 0 := CharTwo.two_eq_zero
          have h36 : (36 : Mi) = 0 := by
            rw [show (36 : Mi) = 2 * 18 by norm_num, h2M, zero_mul]
          have hEV0 : E'.baseChange Mi = (⟨t, 0, 0, 0, t ^ 5⟩ : WeierstrassCurve Mi) := by
            rw [← hEE, WeierstrassCurve.baseChange, hEF, map_ofJNe0Or1728, hXt]
            simp only [ofJNe0Or1728, h1728M, sub_zero, h36, CharTwo.neg_eq]
            ext <;> simp
          have hEV : (E'.baseChange Mi).toAffine =
              (⟨t, 0, 0, 0, t ^ 5⟩ : WeierstrassCurve Mi).toAffine := hEV0
          rcases hQdef : castPt hEE' (Point.map ιm P₃) with _ | ⟨x₀, y₀, hxy⟩
          · exact absurd hQdef hQne
          · have hns : (⟨t, 0, 0, 0, t ^ 5⟩ : WeierstrassCurve Mi).toAffine.Nonsingular x₀ y₀ :=
              hEV ▸ hxy
            have h3P : (3 : ℕ) • (Point.some x₀ y₀ hns) = 0 := by
              have h1 : castPt hEV (castPt hEE' (Point.map ιm P₃)) = Point.some x₀ y₀ hns := by
                rw [hQdef, castPt_some]
              rw [← h1, ← castPt_nsmul, hQ3, castPt_zero]
            have htu : ¬ IsUnit (⟨t, htA⟩ : A) := by
              intro hu
              apply (IsLocalRing.mem_maximalIdeal _).mp _ hu
              have h1 : (⟨t, htA⟩ : A) = ⟨t - algebraMap K Mi j₀, htjA⟩ :=
                Subtype.ext (by simp [hj0])
              rw [h1]; exact htj𝔪
            obtain ⟨μ, u, hu, htμ⟩ :=
              WeierstrassCurve.exists_isUnit_mul_pow_eight_eq_of_charTwo A htA htu ht0 hns h3P
            have hu0 : ((u : A) : Mi) ≠ 0 := fun h => hu.ne_zero (Subtype.ext h)
            have hμ0 : μ ≠ 0 := by
              rintro rfl; apply ht0; rw [htμ]; simp
            have h8 : (e : ℤ) = 8 * W₀.ord μ := by
              rw [← hcardD', htμ, W₀.ord_mul hu0 (pow_ne_zero _ hμ0), ord_eq_zero_of_isUnit W₀ hu,
                zero_add, ← zpow_natCast, W₀.ord_zpow]
              push_cast; ring
            have : ((8 : ℕ) : ℤ) ∣ (e : ℤ) := ⟨W₀.ord μ, by rw [h8]; push_cast; ring⟩
            exact Int.natCast_dvd_natCast.mp this
        have h24e : 24 ∣ e := by omega
        exact h24.trans (Nat.le_of_dvd hepos h24e)
      · obtain ⟨-, h12le⟩ := (WeierstrassCurve.finite_stabilizer_and_natCard_le_of_j E₀).2.2.1
          (by rw [← hp3]; exact ringChar.eq K p) (hE₀.trans hj0)
        exact h12le.trans (Nat.le_of_dvd hepos h12e)
    · right
      have hchar : ringChar K = 2 ∨ ringChar K = 3 := by
        rcases hp23 with hp2 | hp3
        · left; rw [← hp2]; exact ringChar.eq K p
        · right; rw [← hp3]; exact ringChar.eq K p
      have hj : E₀.j ≠ 0 := by rw [hE₀]; exact hj0
      exact (WeierstrassCurve.natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_char_two_or_three
        hchar E₀ hj).le
  ·
    have h2 : (2 : K) ≠ 0 := fun h => h6 (by linear_combination 3 * h)
    have h3 : (3 : K) ≠ 0 := fun h => h6 (by linear_combination 2 * h)
    have h1728K : (1728 : K) ≠ 0 := by
      rw [show (1728 : K) = 2 ^ 6 * 3 ^ 3 by norm_num]
      exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)
    by_cases hj0 : j₀ = 0
    · left
      have hcardD' : W₀.ord t = e := by rw [← hcardD, hj0, _root_.map_zero, sub_zero]
      have hu : IsUnit (⟨t, htA⟩ - algebraMap K A 1728 : A) := by
        apply hunitK _ (-1728) (neg_ne_zero.mpr h1728K)
        have h1 : (⟨t, htA⟩ - algebraMap K A 1728 : A) - algebraMap K A (-1728) =
            ⟨t - algebraMap K Mi j₀, htjA⟩ := by
          apply Subtype.ext
          push_cast
          rw [hcoe1728, hj0, _root_.map_zero, sub_zero]
          ring
        rw [h1]; exact htj𝔪
      have hord0 : W₀.ord (t - 1728) = 0 := by
        have h1 := ord_eq_zero_of_isUnit W₀ hu
        have h2 : ((⟨t, htA⟩ - algebraMap K A 1728 : A) : Mi) = t - 1728 := by
          push_cast; rw [hcoe1728]
        rwa [h2] at h1
      have h6e : 6 ∣ e := by
        rw [hord0, mul_zero, add_zero, hcardD'] at h12
        omega
      obtain ⟨-, h6le⟩ := (WeierstrassCurve.finite_stabilizer_and_natCard_le_of_j E₀).1 h6
        (hE₀.trans hj0)
      exact h6le.trans (Nat.le_of_dvd hepos h6e)
    · by_cases hj1728 : j₀ = 1728
      · left
        have hcardD' : W₀.ord (t - 1728) = e := by rw [← hcardD, hj1728, map_ofNat]
        have hu : IsUnit (⟨t, htA⟩ : A) := by
          apply hunitK _ 1728 h1728K
          have h1 : (⟨t, htA⟩ : A) - algebraMap K A 1728 = ⟨t - algebraMap K Mi j₀, htjA⟩ := by
            apply Subtype.ext
            push_cast
            rw [hcoe1728, hj1728, map_ofNat]
          rw [h1]; exact htj𝔪
        have hord0 : W₀.ord t = 0 := ord_eq_zero_of_isUnit W₀ hu
        have h4e : 4 ∣ e := by
          rw [hord0, mul_zero, zero_add, hcardD'] at h12
          omega
        obtain ⟨-, h4le⟩ := (WeierstrassCurve.finite_stabilizer_and_natCard_le_of_j E₀).2.1 h6
          (hE₀.trans hj1728)
        exact h4le.trans (Nat.le_of_dvd hepos h4e)
      · right
        have hj0' : E₀.j ≠ 0 := by rw [hE₀]; exact hj0
        have hj1728' : E₀.j ≠ 1728 := by rw [hE₀]; exact hj1728
        exact (WeierstrassCurve.natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_j_ne_1728
          h2 h3 E₀ hj0' hj1728').le

include hN hE₀ in
theorem main :
    ∃ (M : Type u) (_ : Field M) (_ : DecidableEq M) (_ : Algebra K M) (t : M)
      (_ : Transcendental K t) (_ : FiniteDimensional K⟮t⟯ M) (_ : IsGalois K⟮t⟯ M)
      (W₀ : Place K M) (_ : 0 < W₀.ord (t - algebraMap K M j₀))
      (θ : ((WeierstrassCurve.ofJ
            (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point
          →+ E₀.toAffine.Point)
      (ρ : (M ≃ₐ[K⟮t⟯] M) → VariableChange K),
      Nat.card {P : ((WeierstrassCurve.ofJ
        (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point //
          N • P = 0} = N ^ 2 ∧
      (∀ (n : ℕ) (P : ((WeierstrassCurve.ofJ
          (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point),
          ¬ p ∣ n → n • P = 0 → θ P = 0 → P = 0) ∧
      (∀ σ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ →
          ρ σ • E₀ = E₀) ∧
      (∀ σ τ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ →
          SemilinearAut.ofAlgAut (τ.restrictScalars K) • W₀ = W₀ → ρ (σ * τ) = ρ σ * ρ τ) ∧
      (∀ σ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ →
          ∀ P, HEq (Point.vcInvFun (ρ σ) E₀.toAffine (θ P))
            (θ (WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M) P))) ∧
      (∀ γ : VariableChange K, γ • E₀ = E₀ →
          ∃ σ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ ∧
            ((∀ P, HEq (Point.vcInvFun γ E₀.toAffine (θ P))
                (θ (WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M) P))) ∨
             (∀ P, HEq (Point.vcInvFun γ E₀.toAffine (θ P))
                (-θ (WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M) P))))) ∧
      (∀ σ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ →
          ρ σ = 1 → σ = 1) := by

  let : DecidableEq 𝓕 := Classical.decEq _
  let : DecidableEq 𝓞 := Classical.decEq _
  let EF : WeierstrassCurve 𝓕 := WeierstrassCurve.ofJ (RatFunc.X : 𝓕)
  have hXne0 : (RatFunc.X : 𝓕) ≠ 0 := RatFunc.X_ne_zero
  have hXne1728 : (RatFunc.X : 𝓕) ≠ 1728 := by
    intro h
    apply RatFunc.transcendental_X (K := K)
    rw [h, show (1728 : 𝓕) = algebraMap K 𝓕 1728 from (map_ofNat (algebraMap K 𝓕) 1728).symm]
    exact isAlgebraic_algebraMap _
  have hEF : EF = ofJNe0Or1728 (RatFunc.X : 𝓕) := ofJ_ne_0_ne_1728 _ hXne0 hXne1728
  have hNF : (N : 𝓕) ≠ 0 := by
    rw [show (N : 𝓕) = algebraMap K 𝓕 N by norm_num]
    exact (map_ne_zero _).mpr hN

  obtain ⟨L₁, hL₁fd, hL₁gal, hL₁card, hL₁faith⟩ :=
    WeierstrassCurve.exists_intermediateField_isGalois_card_torsion_eq_sq (Ω := 𝓞) EF hNF
  obtain ⟨m, hmK, hm3, hroute⟩ := exists_good_model_route K p j₀ E₀ hE₀ (Ω := 𝓞) EF
  have hmF : (m : 𝓕) ≠ 0 := by
    rw [show (m : 𝓕) = algebraMap K 𝓕 m by norm_num]
    exact (map_ne_zero _).mpr hmK
  obtain ⟨Lm, hLmfd, hLmgal, hLmcard, hLmfaith⟩ :=
    WeierstrassCurve.exists_intermediateField_isGalois_card_torsion_eq_sq (Ω := 𝓞) EF hmF
  obtain ⟨S, hSfd, hSgal, hroute⟩ := hroute
  have := hL₁fd; have := hL₁gal; have := hLmfd; have := hLmgal; have := hSfd; have := hSgal
  let Mi : IntermediateField 𝓕 𝓞 := (L₁ ⊔ Lm) ⊔ S
  have hL₁M : L₁ ≤ Mi := le_sup_left.trans le_sup_left
  have hLmM : Lm ≤ Mi := le_sup_right.trans le_sup_left
  have hSM : S ≤ Mi := le_sup_right

  let t : Mi := tt K
  have htr : Transcendental K t := transcendental_tt K
  obtain ⟨hfd, hgal⟩ := finiteDimensional_isGalois_adjoin K (M := Mi)
  have := hfd; have := hgal
  obtain ⟨W₀, hW₀⟩ := exists_place_ord_pos K (M := Mi) j₀
  have hdeg : W₀.deg ≠ 0 := Place.deg_ne_zero_of_finiteDimensional_adjoin t htr W₀
  let A : ValuationSubring Mi := W₀.toValuationSubring
  obtain ⟨htjA, htj𝔪⟩ := mem_maximalIdeal_of_ord_pos W₀ hW₀
  have htA : t ∈ A := by
    have := add_mem htjA (W₀.algebraMap_mem' j₀)
    rwa [sub_add_cancel] at this

  set t' : K⟮t⟯ := ⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ with ht'_def
  have ht't : (t' : Mi) = t := rfl
  have halg_t' : algebraMap K⟮t⟯ Mi t' = t := rfl
  have htr' : Transcendental K t' := by
    rw [← transcendental_algebraMap_iff (algebraMap K⟮t⟯ Mi).injective, halg_t']
    exact htr
  have ht'0 : t' ≠ 0 := by
    rintro h; rw [h] at htr'; exact htr' isAlgebraic_zero
  have ht'1728 : t' ≠ 1728 := by
    rintro h; rw [h, show (1728 : K⟮t⟯) = algebraMap K K⟮t⟯ 1728 from
      (map_ofNat (algebraMap K K⟮t⟯) 1728).symm] at htr'
    exact htr' (isAlgebraic_algebraMap _)
  set E' : WeierstrassCurve K⟮t⟯ := WeierstrassCurve.ofJ t' with hE'_def
  have hE' : E' = ofJNe0Or1728 t' := ofJ_ne_0_ne_1728 _ ht'0 ht'1728
  have hXt : algebraMap 𝓕 Mi RatFunc.X = t := rfl
  have hE'ell : E'.IsElliptic := by rw [hE'_def]; infer_instance
  have hE'Mell : (E'.baseChange Mi).IsElliptic := instIsEllipticMap E' _
  have hEE : EF.baseChange Mi = E'.baseChange Mi := by
    rw [WeierstrassCurve.baseChange, hEF, map_ofJNe0Or1728, WeierstrassCurve.baseChange, hE',
      map_ofJNe0Or1728, hXt, halg_t']
  have hEE' : (EF.baseChange Mi).toAffine = (E'.baseChange Mi).toAffine := hEE

  have hmA : IsUnit ((m : ℕ) : A) := by
    have h1 : ((m : ℕ) : A) = algebraMap K A m := by simp
    rw [h1]
    exact (IsUnit.mk0 _ hmK).map _
  have hjA : algebraMap 𝓕 Mi EF.j ∈ A := by
    rw [show EF.j = RatFunc.X from ofJ_j _, hXt]; exact htA
  obtain ⟨W, κ, hκ, hΔ, hfaith⟩ := hroute Mi hSM A hmA hjA
  rw [hEE] at hκ

  let : DecidableEq (ResidueField A) := Classical.decEq _
  obtain ⟨θ₂, g, hinj, hequiv, hmul⟩ :=
    WeierstrassCurve.exists_inertia_equivariant_reduction_of_variableChange_eq_map
      (F := K⟮t⟯) (M := Mi) A E' W κ hκ hΔ

  let algAK : Algebra A K := (toK W₀ hdeg).toAlgebra
  have halgAK : algebraMap A K = toK W₀ hdeg := rfl
  have hWell : W.IsElliptic := ⟨hΔ⟩
  have hWKell : (W.baseChange K).IsElliptic := instIsEllipticMap W (algebraMap A K)
  set WK : WeierstrassCurve K := W.baseChange K with hWK_def
  have hWK : WK = (W.map (residue A)).map (resK W₀ hdeg).toRingHom := by
    rw [hWK_def, WeierstrassCurve.baseChange, WeierstrassCurve.map_map]; rfl
  have hjW : W.j = ⟨t, htA⟩ := by
    apply Subtype.ext
    have h1 : ((W.j : A) : Mi) = (W.map A.subtype).j := (W.map_j A.subtype).symm
    rw [h1, j_congr hκ.symm, variableChange_j]
    show (E'.map (algebraMap K⟮t⟯ Mi)).j = t
    rw [E'.map_j, j_congr hE'_def, ofJ_j]; rfl
  have hjWK : WK.j = E₀.j := by
    rw [j_congr hWK_def, show (W.baseChange K).j = algebraMap A K W.j from
      W.map_j (algebraMap A K), hjW, halgAK, hE₀,
      toK_eq_toK_of_sub_mem W₀ hdeg (b := algebraMap K A j₀) htj𝔪, toK_algebraMap]
  obtain ⟨γ₀, hγ₀⟩ := exists_variableChange_of_j_eq WK E₀ hjWK
  have hγ₀' : γ₀ • WK.toAffine = E₀.toAffine := hγ₀

  let eK : ResidueField A →ₐ[A] K :=
    { (resK W₀ hdeg).toRingHom with commutes' := fun a => rfl }
  have heK : ∀ r, eK r = resK W₀ hdeg r := fun r => rfl
  have hbc : (W.map (residue A)).toAffine = (W.baseChange (ResidueField A)).toAffine := rfl
  let π : (W.baseChange (ResidueField A)).toAffine.Point →+ WK.toAffine.Point := Point.map eK
  let θ : (E'.baseChange Mi).toAffine.Point →+ E₀.toAffine.Point :=
    (castAddHom hγ₀').comp ((vcInvAddHom γ₀ WK.toAffine).comp
      (π.comp ((castAddHom hbc).comp θ₂)))
  have hθ : ∀ P, θ P = castPt hγ₀' (vcInvFun γ₀ WK.toAffine (π (castPt hbc (θ₂ P)))) :=
    fun P => rfl
  let gK : (Mi ≃ₐ[K⟮t⟯] Mi) → VariableChange K := fun σ => (g σ).map (algebraMap A K)
  have hgK : ∀ σ, gK σ = ((g σ).map (residue A)).map (resK W₀ hdeg).toRingHom := by
    intro σ; simp only [gK, VariableChange.map_map]; rfl
  let ρ : (Mi ≃ₐ[K⟮t⟯] Mi) → VariableChange K := fun σ => γ₀ * gK σ * γ₀⁻¹

  have hD : ∀ σ : Mi ≃ₐ[K⟮t⟯] Mi, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ →
      ∃ hσ : σ ∈ A.decompositionSubgroup K⟮t⟯,
        (⟨σ, hσ⟩ : A.decompositionSubgroup K⟮t⟯) ∈ A.inertiaSubgroup K⟮t⟯ := fun σ h =>
    ⟨(smul_place_eq_iff σ W₀).mp h, mem_inertia_of_mem_decomposition W₀ hdeg _⟩

  have hgKfix : ∀ σ : Mi ≃ₐ[K⟮t⟯] Mi, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ →
      gK σ • WK = WK := by
    intro σ h
    obtain ⟨hσ, hI⟩ := hD σ h
    obtain ⟨-, hfix, -⟩ := hequiv σ hσ hI
    rw [hgK, hWK, map_variableChange, hfix]

  have hcharK : CharP (ResidueField A) p :=
    charP_of_injective_ringHom (algebraMap K (ResidueField A)).injective p

  have hθsome : ∀ (P : (E'.baseChange Mi).toAffine.Point) {x y : ResidueField A}
      (h : (W.map (residue A)).toAffine.Nonsingular x y), θ₂ P = .some x y h →
      ∃ h', θ P = .some (vcXInv γ₀ (resK W₀ hdeg x)) (vcYInv γ₀ (resK W₀ hdeg x) (resK W₀ hdeg y)) h' := by
    intro P x y h hP
    have hWKns : WK.toAffine.Nonsingular (resK W₀ hdeg x) (resK W₀ hdeg y) := by
      rw [hWK]
      exact (Affine.map_nonsingular _ (resK W₀ hdeg).toRingHom.injective x y).mpr h
    have h' : E₀.toAffine.Nonsingular (vcXInv γ₀ (resK W₀ hdeg x))
        (vcYInv γ₀ (resK W₀ hdeg x) (resK W₀ hdeg y)) := by
      rw [← hγ₀']
      exact (nonsingular_variableChange_iff _ _).mpr (by rwa [vcX_vcXInv, vcY_vcYInv])
    refine ⟨h', ?_⟩
    rw [hθ, hP, castPt_some]
    erw [Point.map_some]
    rw [vcInvFun_some, castPt_some]
    rfl
  have hθzero : ∀ (P : (E'.baseChange Mi).toAffine.Point), θ₂ P = 0 → θ P = 0 := by
    intro P hP
    rw [hθ, hP, castPt_zero, _root_.map_zero, vcInvFun_zero, castPt_zero]

  have hc2 : ∀ (n : ℕ) (P : (E'.baseChange Mi).toAffine.Point), ¬ p ∣ n → n • P = 0 → θ P = 0 → P = 0 := by
    intro n P hpn hnP hθP
    have hn : (n : ResidueField A) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff (ResidueField A) p n]; exact hpn
    apply hinj n P hn hnP
    rcases hQ : θ₂ P with _ | ⟨x, y, h⟩
    · rfl
    · exfalso
      obtain ⟨h', hθP'⟩ := hθsome P h hQ
      rw [hθP'] at hθP
      exact Point.some_ne_zero _ hθP

  have hc3 : ∀ σ : Mi ≃ₐ[K⟮t⟯] Mi, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ →
      ρ σ • E₀ = E₀ := by
    intro σ hσD
    show (γ₀ * gK σ * γ₀⁻¹) • E₀ = E₀
    rw [mul_smul, mul_smul, ← hγ₀, inv_smul_smul, hgKfix σ hσD]
  have hc3' : ∀ σ : Mi ≃ₐ[K⟮t⟯] Mi, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ →
      (ρ σ • E₀).toAffine = E₀.toAffine := fun σ h => hc3 σ h

  have hc4 : ∀ σ τ : Mi ≃ₐ[K⟮t⟯] Mi, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ →
      SemilinearAut.ofAlgAut (τ.restrictScalars K) • W₀ = W₀ → ρ (σ * τ) = ρ σ * ρ τ := by
    intro σ τ hσD hτD
    obtain ⟨hσ, hσI⟩ := hD σ hσD
    obtain ⟨hτ, hτI⟩ := hD τ hτD
    exact gK_conj_mul (K := K) (Mi := Mi) (t := t) (W₀ := W₀) (hdeg := hdeg)
      (g := g) (gK := gK) (γ₀ := γ₀) (hgK := hgK) (hmul := hmul) (σ := σ) (τ := τ)
      (hσ := hσ) (hτ := hτ) (hσI := hσI) (hτI := hτI)

  have hc5 : ∀ σ : Mi ≃ₐ[K⟮t⟯] Mi, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ →
      ∀ P, HEq (Point.vcInvFun (ρ σ) E₀.toAffine (θ P))
        (θ (Point.map (σ : Mi →ₐ[K⟮t⟯] Mi) P)) := by
    intro σ hσD P
    obtain ⟨hσ, hI⟩ := hD σ hσD
    obtain ⟨-, hfix, hheq⟩ := hequiv σ hσ hI
    have hfix' : (((g σ).map (residue A)) • W.map (residue A)).toAffine =
        (W.map (residue A)).toAffine := hfix
    have hσP : θ₂ (Point.map (σ : Mi →ₐ[K⟮t⟯] Mi) P) =
        castPt hfix' (vcInvFun ((g σ).map (residue A)) (W.map (residue A)).toAffine (θ₂ P)) :=
      eq_castPt_of_heq hfix' (hheq P)
    have hx : ∀ x : ResidueField A, resK W₀ hdeg (vcXInv ((g σ).map (residue A)) x) =
        vcXInv (gK σ) (resK W₀ hdeg x) := by
      intro x; rw [hgK]; exact map_vcXInv (resK W₀ hdeg).toRingHom _ x
    have hy : ∀ x y : ResidueField A, resK W₀ hdeg (vcYInv ((g σ).map (residue A)) x y) =
        vcYInv (gK σ) (resK W₀ hdeg x) (resK W₀ hdeg y) := by
      intro x y; rw [hgK]; exact map_vcYInv (resK W₀ hdeg).toRingHom _ x y
    rcases hQ : θ₂ P with _ | ⟨x, y, h⟩
    · have h1 : θ P = 0 := hθzero P hQ
      have h2 : θ (Point.map (σ : Mi →ₐ[K⟮t⟯] Mi) P) = 0 :=
        hθzero _ (by rw [hσP, hQ]; exact castPt_zero _)
      rw [h1, h2, vcInvFun_zero]
      exact heq_zero_of_eq (hc3' σ hσD)
    · obtain ⟨h₁, hθP⟩ := hθsome P h hQ
      have hQ' : θ₂ (Point.map (σ : Mi →ₐ[K⟮t⟯] Mi) P) =
          .some (vcXInv ((g σ).map (residue A)) x) (vcYInv ((g σ).map (residue A)) x y)
            (hfix' ▸ (nonsingular_variableChange_iff _ _).mpr (by rwa [vcX_vcXInv, vcY_vcYInv])) := by
        rw [hσP, hQ, vcInvFun_some, castPt_some]
      obtain ⟨h₂, hθσP⟩ := hθsome _ _ hQ'
      rw [hθP, hθσP, vcInvFun_some]
      apply heq_some_of_eq (hc3' σ hσD)
      · show vcXInv (γ₀ * gK σ * γ₀⁻¹) (vcXInv γ₀ (resK W₀ hdeg x)) = _
        rw [vcXInv_mul, vcXInv_mul, ← vcXInv_mul γ₀⁻¹ γ₀, inv_mul_cancel, vcXInv_one, hx]
      · show vcYInv (γ₀ * gK σ * γ₀⁻¹) (vcXInv γ₀ (resK W₀ hdeg x))
          (vcYInv γ₀ (resK W₀ hdeg x) (resK W₀ hdeg y)) = _
        rw [vcYInv_mul, vcYInv_mul, ← vcYInv_mul γ₀⁻¹ γ₀, ← vcXInv_mul γ₀⁻¹ γ₀,
          inv_mul_cancel, vcXInv_one, vcYInv_one, hx, hy]

  have hmapcast : ∀ (τ : Mi ≃ₐ[K⟮t⟯] Mi) (Q : (EF.baseChange Mi).toAffine.Point),
      castPt hEE' (Point.map (toRatFuncAlgEquiv K τ : Mi →ₐ[𝓕] Mi) Q) =
        Point.map (τ : Mi →ₐ[K⟮t⟯] Mi) (castPt hEE' Q) := by
    rintro τ (_ | ⟨x, y, hxy⟩)
    · rfl
    · simp only [castPt_some]
      erw [Point.map_some, Point.map_some]
      rfl

  have hLfix : ∀ (τ : Mi ≃ₐ[𝓕] Mi) (L : IntermediateField 𝓕 𝓞) [IsGalois 𝓕 L] (hL : L ≤ Mi) (n : ℕ),
      (∀ τ' : L ≃ₐ[𝓕] L, (∀ P : (EF.baseChange L).toAffine.Point, n • P = 0 →
        Point.map (τ' : L →ₐ[𝓕] L) P = P) → τ' = 1) →
      (∀ Q : (EF.baseChange Mi).toAffine.Point, n • Q = 0 →
        Point.map (τ : Mi →ₐ[𝓕] Mi) Q = Q) →
      ∀ x : Mi, (x : 𝓞) ∈ L → τ x = x :=
    fun τ L _ hL n faithful hfixQ x hx =>
      eq_of_forall_nsmul_eq_of_faithful (F := 𝓕) (Ω := 𝓞) EF Mi L hL n τ faithful hfixQ x hx
  have hc7 : ∀ σ : Mi ≃ₐ[K⟮t⟯] Mi, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ →
      ρ σ = 1 → σ = 1 := by
    intro σ hσD hρ
    obtain ⟨hσ, hI⟩ := hD σ hσD
    obtain ⟨hgM, hfix, hheq⟩ := hequiv σ hσ hI
    have hgK1 : gK σ = 1 := by
      have h1 : γ₀ * gK σ * γ₀⁻¹ = 1 := hρ
      calc gK σ = γ₀⁻¹ * (γ₀ * gK σ * γ₀⁻¹) * γ₀ := by group
        _ = 1 := by rw [h1]; group
    have hg1 : (g σ).map (residue A) = 1 := by
      apply VariableChange.map_injective (φ := (resK W₀ hdeg).toRingHom) (resK W₀ hdeg).injective
      show ((g σ).map (residue A)).map _ = (1 : VariableChange _).map _
      rw [← hgK, hgK1]
      exact ((VariableChange.mapHom (resK W₀ hdeg).toRingHom).map_one).symm

    have hθ₂fix : ∀ P, θ₂ (Point.map (σ : Mi →ₐ[K⟮t⟯] Mi) P) = θ₂ P := by
      intro P
      have hfix1 : ((1 : VariableChange (ResidueField A)) • W.map (residue A)).toAffine =
          (W.map (residue A)).toAffine := by rw [one_smul]
      have h := hheq P
      rw [hg1] at h
      rw [eq_castPt_of_heq hfix1 h]
      rcases θ₂ P with _ | ⟨x, y, hxy⟩
      · rfl
      · rw [vcInvFun_some, castPt_some]; exact some_congr (vcXInv_one x) (vcYInv_one x y) _ _

    have hfixT : ∀ n : ℕ, (n : K) ≠ 0 → ∀ P : (E'.baseChange Mi).toAffine.Point, n • P = 0 →
        Point.map (σ : Mi →ₐ[K⟮t⟯] Mi) P = P := by
      intro n hn P hP
      have hnk : (n : ResidueField A) ≠ 0 := by
        rw [show (n : ResidueField A) = algebraMap K _ n by simp]; exact (map_ne_zero _).mpr hn
      have h1 : n • (Point.map (σ : Mi →ₐ[K⟮t⟯] Mi) P - P) = 0 := by
        rw [smul_sub, ← map_nsmul, hP, _root_.map_zero, sub_zero]
      have h2 : θ₂ (Point.map (σ : Mi →ₐ[K⟮t⟯] Mi) P - P) = 0 := by
        rw [map_sub, hθ₂fix, sub_self]
      exact sub_eq_zero.mp (hinj n _ hnk h1 h2)

    set σF := toRatFuncAlgEquiv K σ with hσF_def
    have hσF : σF ∈ A.decompositionSubgroup 𝓕 :=
      (toRatFuncAlgEquiv_mem_decompositionSubgroup_iff K σ A).mpr hσ
    have hσFI := mem_inertia_of_mem_decomposition W₀ hdeg hσF
    have hfixTF : ∀ n : ℕ, (n : K) ≠ 0 → ∀ Q : (EF.baseChange Mi).toAffine.Point, n • Q = 0 →
        Point.map (σF : Mi →ₐ[𝓕] Mi) Q = Q := by
      intro n hn Q hQ
      apply castPt_injective hEE'
      rw [hmapcast]
      exact hfixT n hn _ (by rw [← castPt_nsmul, hQ, castPt_zero])

    have hSfix : ∀ x : Mi, (x : 𝓞) ∈ S → σF x = x :=
      hfaith σF hσF hσFI (hfixTF m hmK) ⟨g σ, hgM, hg1⟩

    have hL₁fix : ∀ x : Mi, (x : 𝓞) ∈ L₁ → σF x = x :=
      hLfix σF L₁ hL₁M N hL₁faith (hfixTF N hN)
    have hLmfix : ∀ x : Mi, (x : 𝓞) ∈ Lm → σF x = x :=
      hLfix σF Lm hLmM m hLmfaith (hfixTF m hmK)

    have hσF1 : σF = 1 := by
      let Fix : IntermediateField 𝓕 Mi :=
        (AlgHom.equalizer (σF : Mi →ₐ[𝓕] Mi) (AlgHom.id 𝓕 Mi)).toIntermediateField (by
          intro x hx
          rw [AlgHom.mem_equalizer] at hx ⊢
          rw [map_inv₀, hx]; rfl)
      have hmemFix : ∀ y : Mi, y ∈ Fix ↔ σF y = y := fun y => by
        show y ∈ AlgHom.equalizer _ _ ↔ _
        rw [AlgHom.mem_equalizer]; rfl
      have hle : Mi ≤ IntermediateField.lift Fix := by
        refine sup_le (sup_le ?_ ?_) ?_
        · intro y hy
          have hyM : y ∈ Mi := hL₁M hy
          exact (IntermediateField.mem_lift (⟨y, hyM⟩ : Mi)).mpr ((hmemFix _).mpr (hL₁fix _ hy))
        · intro y hy
          have hyM : y ∈ Mi := hLmM hy
          exact (IntermediateField.mem_lift (⟨y, hyM⟩ : Mi)).mpr ((hmemFix _).mpr (hLmfix _ hy))
        · intro y hy
          have hyM : y ∈ Mi := hSM hy
          exact (IntermediateField.mem_lift (⟨y, hyM⟩ : Mi)).mpr ((hmemFix _).mpr (hSfix _ hy))
      refine AlgEquiv.ext fun x => ?_
      have hx : x ∈ Fix := (IntermediateField.mem_lift x).mp (hle x.2)
      rw [AlgEquiv.one_apply]
      exact (hmemFix x).mp hx
    exact (toRatFuncAlgEquiv_eq_one_iff K σ).mp hσF1
  refine ⟨Mi, inferInstance, inferInstance, inferInstance, t, htr, hfd, hgal, W₀, hW₀, θ, ρ,
    ?_, hc2, hc3, hc4, hc5, ?_, ?_⟩
  · exact torsion_card_eq_sq (K := K) (N := N) (Mi := Mi) (t := t) (E' := E') (EF := EF)
      (hEE' := hEE') (hNF := hNF) (L₁ := L₁) (hL₁M := hL₁M) (hL₁card := hL₁card)
  ·
    intro γ hγ

    have hvt : (IntermediateField.val K⟮t⟯) t' = t := rfl
    have hB := Place.ord_restrictAlong_eq_natCard_algHom_of_isGalois K (F := K⟮t⟯) (M := Mi) t' t j₀
      (IntermediateField.val K⟮t⟯) hvt hfd hgal (isIntegral_of_apply_gen_eq t) W₀ hW₀
    obtain ⟨e, he_def⟩ : ∃ e : ℕ, Nat.card {σ : Mi ≃ₐ[K⟮t⟯] Mi //
      SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀} = e := ⟨_, rfl⟩
    have hcardD : W₀.ord (t - algebraMap K Mi j₀) = e := by rw [← he_def]; exact hB.1
    clear hB
    have hepos : 0 < e := by
      have : (0 : ℤ) < e := hcardD ▸ hW₀
      exact_mod_cast this

    have hStabfin : Finite (MulAction.stabilizer (VariableChange K) E₀) :=
      WeierstrassCurve.finite_stabilizer_variableChange K E₀
    have h1D : SemilinearAut.ofAlgAut ((1 : Mi ≃ₐ[K⟮t⟯] Mi).restrictScalars K) • W₀ = W₀ :=
      (smul_place_eq_iff (1 : Mi ≃ₐ[K⟮t⟯] Mi) W₀).mpr (one_mem _)
    have hρ1 : ρ 1 = 1 := by
      have h := hc4 1 1 h1D h1D
      rw [mul_one] at h
      exact mul_eq_left.mp h.symm

    let fD : {σ : Mi ≃ₐ[K⟮t⟯] Mi // SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀} →
        MulAction.stabilizer (VariableChange K) E₀ := fun σ => ⟨ρ σ.1, hc3 σ.1 σ.2⟩
    have hfD : Function.Injective fD := by
      rintro ⟨σ, hσ⟩ ⟨τ, hτ⟩ h
      have h' : ρ σ = ρ τ := congrArg (fun x : MulAction.stabilizer (VariableChange K) E₀ =>
        (x : VariableChange K)) h
      have hσ' := (smul_place_eq_iff σ W₀).mp hσ
      have hτ' := (smul_place_eq_iff τ W₀).mp hτ
      have hτinv : SemilinearAut.ofAlgAut ((τ⁻¹ : Mi ≃ₐ[K⟮t⟯] Mi).restrictScalars K) • W₀ = W₀ :=
        (smul_place_eq_iff _ W₀).mpr (inv_mem hτ')
      have hστ : SemilinearAut.ofAlgAut ((σ * τ⁻¹ : Mi ≃ₐ[K⟮t⟯] Mi).restrictScalars K) • W₀ = W₀ :=
        (smul_place_eq_iff _ W₀).mpr (mul_mem hσ' (inv_mem hτ'))
      have h1 : ρ (σ * τ⁻¹) = 1 := by
        rw [hc4 σ τ⁻¹ hσ hτinv, h', ← hc4 τ τ⁻¹ hτ hτinv, mul_inv_cancel, hρ1]
      have h2 := hc7 _ hστ h1
      exact Subtype.ext (mul_inv_eq_one.mp h2)

    have hHEqneg : ∀ (σ : Mi ≃ₐ[K⟮t⟯] Mi)
        (hσ : SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀) (P),
        HEq (Point.vcInvFun (negC E₀ * ρ σ) E₀.toAffine (θ P))
          (-θ (Point.map (σ : Mi →ₐ[K⟮t⟯] Mi) P)) := by
      intro σ hσ P
      have hcurve : ((negC E₀ * ρ σ) • E₀).toAffine = E₀.toAffine := by
        show (negC E₀ * ρ σ) • E₀ = E₀
        rw [mul_smul, hc3 σ hσ, negC_smul]
      have h5 := hc5 σ hσ P
      have hR : θ (Point.map (σ : Mi →ₐ[K⟮t⟯] Mi) P) =
          castPt (hc3' σ hσ) (vcInvFun (ρ σ) E₀.toAffine (θ P)) := eq_castPt_of_heq _ h5
      rw [hR]
      rcases θ P with _ | ⟨X, Y, hXY⟩
      · show HEq (0 : ((negC E₀ * ρ σ) • E₀).toAffine.Point) (-(0 : E₀.toAffine.Point))
        rw [_root_.neg_zero]
        exact heq_zero_of_eq hcurve
      · rw [vcInvFun_some, vcInvFun_some, castPt_some, Affine.Point.neg_some]
        apply heq_some_of_eq hcurve
        · rw [vcXInv_mul, vcXInv_negC]
        · rw [vcYInv_mul, vcYInv_negC]

    have key : Nat.card (MulAction.stabilizer (VariableChange K) E₀) ≤ e ∨
        Nat.card (MulAction.stabilizer (VariableChange K) E₀) ≤ 2 :=
      stabilizer_card_bound K p j₀ E₀ hE₀ Mi t htr EF hEF hXt E' hEE hEE' W₀ e hcardD hepos htA htjA htj𝔪
        W κ hκ hΔ m hmK hm3 Lm hLmM hLmcard
    rcases key with hle | hle2
    · have hbij := hfD.bijective_of_nat_card_le (he_def ▸ hle)
      obtain ⟨⟨σ, hσ⟩, hσγ⟩ := hbij.2 ⟨γ, hγ⟩
      have hργ : ρ σ = γ := congrArg Subtype.val hσγ
      exact ⟨σ, hσ, Or.inl fun P => by rw [← hργ]; exact hc5 σ hσ P⟩
    · have hγ' : γ = 1 ∨ γ = negC E₀ := by
        by_contra hcon
        push Not at hcon
        have := Fintype.ofFinite (MulAction.stabilizer (VariableChange K) E₀)
        have h3 : 2 < Nat.card (MulAction.stabilizer (VariableChange K) E₀) := by
          rw [Nat.card_eq_fintype_card, Fintype.two_lt_card_iff]
          exact ⟨⟨1, one_mem _⟩, ⟨negC E₀, negC_smul E₀⟩, ⟨γ, hγ⟩,
            fun h => negC_ne_one E₀ (congrArg Subtype.val h).symm,
            fun h => hcon.1 (congrArg Subtype.val h).symm,
            fun h => hcon.2 (congrArg Subtype.val h).symm⟩
        omega
      rcases hγ' with rfl | rfl
      · exact ⟨1, h1D, Or.inl fun P => by rw [← hρ1]; exact hc5 1 h1D P⟩
      · refine ⟨1, h1D, Or.inr fun P => ?_⟩
        have h := hHEqneg 1 h1D P
        rwa [hρ1, mul_one] at h
  ·
    exact hc7

end Main

end EquivariantTorsion

open EquivariantTorsion in
universe u in
theorem exists_equivariant_torsion_reduction_ofJ
    (K : Type u) [Field K] [IsAlgClosed K] [DecidableEq K] (p : ℕ) [CharP K p]
    (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) (j₀ : K)
    (E₀ : WeierstrassCurve K) [E₀.IsElliptic] (hE₀ : E₀.j = j₀) :
    ∃ (M : Type u) (_ : Field M) (_ : DecidableEq M) (_ : Algebra K M) (t : M)
      (_ : Transcendental K t) (_ : FiniteDimensional K⟮t⟯ M) (_ : IsGalois K⟮t⟯ M)
      (W₀ : Place K M) (_ : 0 < W₀.ord (t - algebraMap K M j₀))
      (θ : ((WeierstrassCurve.ofJ
            (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point
          →+ E₀.toAffine.Point)
      (ρ : (M ≃ₐ[K⟮t⟯] M) → VariableChange K),
      Nat.card {P : ((WeierstrassCurve.ofJ
        (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point //
          N • P = 0} = N ^ 2 ∧
      (∀ (n : ℕ) (P : ((WeierstrassCurve.ofJ
          (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point),
          ¬ p ∣ n → n • P = 0 → θ P = 0 → P = 0) ∧
      (∀ σ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ →
          ρ σ • E₀ = E₀) ∧
      (∀ σ τ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ →
          SemilinearAut.ofAlgAut (τ.restrictScalars K) • W₀ = W₀ → ρ (σ * τ) = ρ σ * ρ τ) ∧
      (∀ σ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ →
          ∀ P, HEq (Point.vcInvFun (ρ σ) E₀.toAffine (θ P))
            (θ (WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M) P))) ∧
      (∀ γ : VariableChange K, γ • E₀ = E₀ →
          ∃ σ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ ∧
            ((∀ P, HEq (Point.vcInvFun γ E₀.toAffine (θ P))
                (θ (WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M) P))) ∨
             (∀ P, HEq (Point.vcInvFun γ E₀.toAffine (θ P))
                (-θ (WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M) P))))) ∧
      (∀ σ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ →
          ρ σ = 1 → σ = 1) 
:= by
  exact main K p N hN j₀ E₀ hE₀


end ModularCurve
