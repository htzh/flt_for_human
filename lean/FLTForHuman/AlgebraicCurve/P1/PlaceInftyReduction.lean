/-
The degree formula for the places of `P¹`, from a reduction.

For the rational function field `K(X)` over a field `K`, the principal divisor of a polynomial
relation read at the place at infinity and at the point places gives

  `ord_placeInfty f = ord_placeInfty f + ∑_{p | f} ord_placeOfPoint p f`,

i.e. the degree formula `ord_∞ = -deg` restated as an identity of orders, obtained by
**reducing** each point place to the place at infinity: the reduction of `K[X]` modulo an
irreducible `p` is a finite ring, and the equality of the two orders is the statement that the
reduction's residue degree plus the orders at the roots of the reduction's polynomial add up to
the degree (the root count `ValuationSubring.natDegree_map_eq_card_roots_of_splits` of
SET-AF103E's valued-field toolbox is the engine).

The two named premises are `ord_placeInfty_X` and `ord_placeOfPoint_algebraMap`; the
subject's home is the `P¹` theory (`AlgebraicCurve/P1/`, whose `Dictionary.lean` holds the
two-place dictionary this row feeds) and the valued-field toolbox
(`FieldTheory/ValuationSubringValuedField.lean`).

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty_eq_ord_placeInfty_add_sum_ord_placeOfPoint_of_reduction.lean>

spec-pin: Theorems/Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty_eq_ord_placeInfty_add_sum_ord_placeOfPoint_of_reduction.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_RationalFunctionField_ord_placeInfty_eq_ord_placeInfty_add_sum_ord_placeOfPoint_of_reduction.lean

PORT NOTES (SET-AF105C).

* **Twelve of the pin's 34 declarations are `AlgebraicCurve.DeuringNormResidue`'s** and are
  *imported*, not transcribed: `sigma`, `sigmaFun`, `sigmaFun_spec`, `sigma_spec`,
  `valuation_algebraMap_eq_one`, `valuation_algebraMap_le_one`, `const_unique`, `constEmb`,
  `isUnit_iff_inv_mem`, `map_eq_zero_of_not_isUnit`, `isUnit_of_map_ne_zero` (11 rows) plus
  the pin's `polyEmb` — which is the one **rejected** substitution (FR-0266): its ported
  statement is only the bare type `A[X] →+* O`, while the ported *body* is
  `eval₂RingHom (constEmb …) ⟨_, X_mem …⟩` built from the general reduction's `hX`
  hypothesis `algebraMap (RatFunc E) FE X = algebraMap F FE (algebraMap (RatFunc K) F X)`.
  Instantiating that at `F = RatFunc K`, `FE = RatFunc E` needs an `Algebra (RatFunc K)
  (RatFunc E)` instance, which mathlib v4.34 does not have (checked: `inferInstance` fails),
  so the ported body is not usable here and the pin's `polyEmb` (from `hρ`) is transcribed.
* Two further substitutions the order did not list, found by `rg`: the pin's
  `ord_placeInfty_eq_neg_intDegree` and `ord_placeInfty_algebraMap` are the port's
  `AlgebraicCurve.RationalFunctionField.ord_placeInfty` and
  `…ord_placeInfty_algebraMap` — the pin rows are kept as one-line aliases so the pin's
  engine surface stays visible to `check_port`.
* The pin's inner wrapper namespace `P2MW.S_…` and its `p2m_reactivate` staging are dropped;
  the generated namespace label `DeuringRatFuncReduction` becomes the subject namespace
  `AlgebraicCurve.PlaceInftyReduction`. The pin's `attribute [-instance]`/`[-simp]` walls
  and `import Mathlib` are not transcribed; no `set_option maxHeartbeats` is transcribed.
* **Heartbeat probe pair** (recorded, NOT installed): the whole module is silent at
  `-DmaxHeartbeats=40000` and first fails at `20000`, on `main` — `…:334:0: (deterministic)
  timeout at whnf, maximum number of heartbeats (20000)`. So the module's own cost is ≤ 40 k,
  five times under the edit loop's 200 k cap and a hundred under the lakefile's 4 M; the pin
  carries no `set_option maxHeartbeats` either way, and nothing is installed here: the module
  carries no `set_option` at all.
-/
import FLTForHuman.AlgebraicCurve.DeuringNormResidue
import FLTForHuman.AlgebraicCurve.Defs.RatFuncPlaces
import FLTForHuman.AlgebraicCurve.Genus.Stichtenoth
import FLTForHuman.AlgebraicCurve.P1.Dictionary
import FLTForHuman.FieldTheory.ValuationSubringValuedField
import Mathlib.Tactic.Linarith

noncomputable section

open AlgebraicCurve AlgebraicCurve.RationalFunctionField
open scoped Polynomial

namespace AlgebraicCurve

namespace PlaceInftyReduction

open DeuringNormResidue

section RationalPlace

variable {K E : Type*} [Field K] [Field E] [Algebra K E]
  (A : ValuationSubring E) (hKA : ∀ k : K, algebraMap K E k ∈ A)
  (hArat : ∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1)

include hKA in
theorem sigmaFun_eq_iff (a : A) (k : K) :
    sigmaFun A hArat a = k ↔ A.valuation ((a : E) - algebraMap K E k) < 1 :=
  ⟨fun h => h ▸ sigmaFun_spec A hArat a, fun h => const_unique A hKA (sigmaFun_spec A hArat a) h⟩

theorem sigma_eq_iff (a : A) (k : K) :
    sigma A hKA hArat a = k ↔ A.valuation ((a : E) - algebraMap K E k) < 1 :=
  sigmaFun_eq_iff A hKA hArat a k

theorem ker_sigma : RingHom.ker (sigma A hKA hArat) = IsLocalRing.maximalIdeal A := by
  ext a
  rw [RingHom.mem_ker, sigma_eq_iff, map_zero, sub_zero]
  exact (A.valuation_lt_one_iff a).symm

end RationalPlace

theorem coeff_C_inv_mul_mem {E : Type*} [Field E] (A : ValuationSubring E) (f : E[X]) (c₀ : E)
    (hmax : ∀ c ∈ f.coeffs, A.valuation c ≤ A.valuation c₀) (n : ℕ) :
    (Polynomial.C c₀⁻¹ * f).coeff n ∈ A := by
  rw [Polynomial.coeff_C_mul]
  by_cases hn : f.coeff n = 0
  · rw [hn, mul_zero]; exact A.zero_mem
  rw [← A.valuation_le_one_iff, map_mul, map_inv₀, ← div_eq_inv_mul]
  exact div_le_one_of_le₀ (hmax _ (Polynomial.coeff_mem_coeffs hn)) zero_le

theorem exists_normalization {E : Type*} [Field E] (A : ValuationSubring E) (f : E[X])
    (hf : f ≠ 0) :
    ∃ (c : E) (f₁ : A[X]), c ≠ 0 ∧ f = Polynomial.C c * f₁.map (algebraMap A E) ∧
      ∃ n, f₁.coeff n = 1 := by
  classical
  have hne : f.coeffs.Nonempty :=
    ⟨f.leadingCoeff, Polynomial.coeff_mem_coeffs (Polynomial.leadingCoeff_ne_zero.mpr hf)⟩
  obtain ⟨c₀, hc₀T, hmax⟩ := Finset.exists_max_image f.coeffs (fun c => A.valuation c) hne
  obtain ⟨n₀, hn₀, hc₀⟩ := Polynomial.mem_coeffs_iff.mp hc₀T
  have hc₀0 : c₀ ≠ 0 := hc₀ ▸ Polynomial.mem_support_iff.mp hn₀
  have hA : ∀ n, (Polynomial.C c₀⁻¹ * f).coeff n ∈ A := coeff_C_inv_mul_mem A f c₀ hmax
  obtain ⟨f₁, hf₁⟩ : ∃ f₁ : A[X], f₁.map (algebraMap A E) = Polynomial.C c₀⁻¹ * f := by
    rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
    exact fun n => ⟨⟨_, hA n⟩, rfl⟩
  refine ⟨c₀, f₁, hc₀0, ?_, n₀, ?_⟩
  · rw [hf₁, ← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hc₀0, Polynomial.C_1, one_mul]
  · apply Subtype.ext
    have := congrArg (fun g => Polynomial.coeff g n₀) hf₁
    simp only [Polynomial.coeff_map, Polynomial.coeff_C_mul] at this
    rw [show ((f₁.coeff n₀ : A) : E) = algebraMap A E (f₁.coeff n₀) from rfl, this, ← hc₀,
      inv_mul_cancel₀ hc₀0]
    rfl

section OrdLemmas

variable (k : Type*) [Field k]

theorem ord_placeInfty_eq_neg_intDegree [DecidableEq (RatFunc k)] {f : RatFunc k} (hf : f ≠ 0) :
    (placeInfty k).ord f = -f.intDegree :=
  AlgebraicCurve.RationalFunctionField.ord_placeInfty hf

theorem ord_placeInfty_algebraMap [DecidableEq (RatFunc k)] {f : k[X]} (hf : f ≠ 0) :
    (placeInfty k).ord (algebraMap k[X] (RatFunc k) f) = -(f.natDegree : ℤ) :=
  AlgebraicCurve.RationalFunctionField.ord_placeInfty_algebraMap hf

theorem ord_placeOfPoint_div (β : k) {p q : k[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    (placeOfPoint k β).ord (algebraMap k[X] (RatFunc k) p / algebraMap k[X] (RatFunc k) q) =
      (p.rootMultiplicity β : ℤ) - q.rootMultiplicity β := by
  have hp' : algebraMap k[X] (RatFunc k) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hp
  have hq' : algebraMap k[X] (RatFunc k) q ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hq
  rw [div_eq_mul_inv, (placeOfPoint k β).ord_mul hp' (inv_ne_zero hq'), (placeOfPoint k β).ord_inv,
    ord_placeOfPoint_algebraMap β hp, ord_placeOfPoint_algebraMap β hq]
  ring

end OrdLemmas

section Counting

variable {E : Type*} [Field E] (A : ValuationSubring E)

open Classical in

theorem card_roots_map_eq (f : A[X]) (hf : f ≠ 0) :
    Multiset.card (f.map (algebraMap A E)).roots =
      Multiset.card f.roots +
        Multiset.card ((f.map (algebraMap A E)).roots.filter (fun β => β ∉ A)) := by
  set R := (f.map (algebraMap A E)).roots with hR
  have hι : Function.Injective (algebraMap A E) := Subtype.val_injective
  have h1 : R.filter (fun β => β ∈ A) = f.roots.map (algebraMap A E) := by
    refine Multiset.ext.mpr fun x => ?_
    by_cases hx : x ∈ A
    · rw [Multiset.count_filter_of_pos hx]
      have : x = algebraMap A E ⟨x, hx⟩ := rfl
      rw [this, Multiset.count_map_eq_count' _ _ hι, Polynomial.count_roots,
        Polynomial.count_roots]
      exact (Polynomial.eq_rootMultiplicity_map hι _).symm
    · rw [Multiset.count_filter_of_neg hx, eq_comm, Multiset.count_eq_zero]
      intro hmem
      obtain ⟨a, -, ha⟩ := Multiset.mem_map.mp hmem
      exact hx (ha ▸ a.2)
  have _ := hf
  conv_lhs => rw [← Multiset.filter_add_not (fun β => β ∈ A) R]
  rw [Multiset.card_add, h1, Multiset.card_map]

open Classical in

theorem sum_count_eq_card_filter (R : Multiset E) (T : Finset E)
    (hT : ∀ β ∈ R, β ∉ A → β ∈ T) (hTA : ∀ β ∈ T, β ∉ A) :
    ∑ β ∈ T, R.count β = Multiset.card (R.filter (fun β => β ∉ A)) := by
  set R' := R.filter (fun β => β ∉ A) with hR'
  have h1 : ∀ β ∈ T, R.count β = R'.count β :=
    fun β hβ => (Multiset.count_filter_of_pos (p := fun β => β ∉ A) (hTA β hβ)).symm
  rw [Finset.sum_congr rfl h1, ← Multiset.toFinset_sum_count_eq R']
  symm
  apply Finset.sum_subset
  · intro β hβ
    rw [Multiset.mem_toFinset, hR', Multiset.mem_filter] at hβ
    exact hT β hβ.1 hβ.2
  · intro β _ hβ
    rw [Multiset.mem_toFinset] at hβ
    exact Multiset.count_eq_zero.mpr hβ

end Counting

section Reduction

variable {K E L : Type*} [Field K] [Field E] [Field L] [Algebra K E] [Algebra (RatFunc K) L]
  (A : ValuationSubring E)
  (hKA : ∀ k : K, algebraMap K E k ∈ A)
  (hArat : ∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1)
  (O : ValuationSubring (RatFunc E)) (ρ : O →+* L)
  (hO : ∀ c : E, algebraMap E (RatFunc E) c ∈ O ↔ c ∈ A)
  (hker : RingHom.ker ρ = IsLocalRing.maximalIdeal O)
  (hρ : ∀ p : K[X], ∃ h : algebraMap E[X] (RatFunc E) (p.map (algebraMap K E)) ∈ O,
    ρ ⟨_, h⟩ = algebraMap (RatFunc K) L (algebraMap K[X] (RatFunc K) p))

include hρ in
theorem polyK_mem (p : K[X]) : algebraMap E[X] (RatFunc E) (p.map (algebraMap K E)) ∈ O := by
  obtain ⟨h, -⟩ := hρ p
  exact h

include hρ in
theorem rho_polyK (p : K[X]) (h : algebraMap E[X] (RatFunc E) (p.map (algebraMap K E)) ∈ O) :
    ρ ⟨_, h⟩ = algebraMap (RatFunc K) L (algebraMap K[X] (RatFunc K) p) := by
  obtain ⟨h', hh⟩ := hρ p
  exact hh

include hρ in
theorem X_mem : (RatFunc.X : RatFunc E) ∈ O := by
  have := polyK_mem O ρ hρ Polynomial.X
  rwa [Polynomial.map_X, RatFunc.algebraMap_X] at this

include hρ in
theorem rho_X (h : (RatFunc.X : RatFunc E) ∈ O) :
    ρ ⟨RatFunc.X, h⟩ = algebraMap (RatFunc K) L RatFunc.X := by
  have e : (⟨RatFunc.X, h⟩ : O) =
      ⟨algebraMap E[X] (RatFunc E) ((Polynomial.X : K[X]).map (algebraMap K E)),
        polyK_mem O ρ hρ _⟩ :=
    Subtype.ext (show (RatFunc.X : RatFunc E) =
        algebraMap E[X] (RatFunc E) ((Polynomial.X : K[X]).map (algebraMap K E)) by
      rw [Polynomial.map_X, RatFunc.algebraMap_X])
  rw [e, rho_polyK O ρ hρ, RatFunc.algebraMap_X]

@[scoped simp] theorem coe_constEmb (a : A) :
    ((constEmb A O hO a : O) : RatFunc E) = algebraMap E (RatFunc E) a :=
  DeuringNormResidue.coe_constEmb (E := E) (FE := RatFunc E) (A := A) (O := O) (hO := hO) a

include hKA hker hρ in

theorem rho_constEmb (a : A) :
    ρ (constEmb A O hO a) =
      algebraMap (RatFunc K) L (algebraMap K (RatFunc K) (sigma A hKA hArat a)) := by
  set k := sigma A hKA hArat a with hk_def
  have hk : A.valuation ((a : E) - algebraMap K E k) < 1 := sigma_spec A hKA hArat a
  have hmA : (a : E) - algebraMap K E k ∈ A := A.sub_mem a.2 (hKA k)

  have hconst : ρ (constEmb A O hO ⟨algebraMap K E k, hKA k⟩) =
      algebraMap (RatFunc K) L (algebraMap K (RatFunc K) k) := by
    have e1 : constEmb A O hO ⟨algebraMap K E k, hKA k⟩ =
        ⟨algebraMap E[X] (RatFunc E) ((Polynomial.C k).map (algebraMap K E)),
          polyK_mem O ρ hρ _⟩ :=
      Subtype.ext (show algebraMap E (RatFunc E) (algebraMap K E k) =
          algebraMap E[X] (RatFunc E) ((Polynomial.C k).map (algebraMap K E)) by
        rw [Polynomial.map_C, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C])
    rw [e1, rho_polyK O ρ hρ, RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C]

  have hinf : ρ (constEmb A O hO ⟨_, hmA⟩) = 0 := by
    by_cases hm0 : (a : E) - algebraMap K E k = 0
    · have : constEmb A O hO ⟨_, hmA⟩ = 0 := Subtype.ext (by simp [hm0])
      rw [this, map_zero]
    apply map_eq_zero_of_not_isUnit O ρ hker
    intro hu
    have hinv := (isUnit_iff_inv_mem O _ (by
      show algebraMap E (RatFunc E) ((a : E) - algebraMap K E k) ≠ 0
      exact (map_ne_zero _).mpr hm0)).mp hu
    simp only [coe_constEmb, ← map_inv₀] at hinv
    rw [hO] at hinv
    have hunitA : IsUnit (⟨_, hmA⟩ : A) :=
      (isUnit_iff_inv_mem A ⟨_, hmA⟩ hm0).mpr hinv
    have hmax : (⟨_, hmA⟩ : A) ∈ IsLocalRing.maximalIdeal A :=
      (ValuationSubring.valuation_lt_one_iff A _).mpr hk
    exact ((IsLocalRing.mem_maximalIdeal _).mp hmax) hunitA
  have hsplit : a = ⟨algebraMap K E k, hKA k⟩ + ⟨_, hmA⟩ := Subtype.ext (by simp)
  rw [hsplit, map_add, map_add, hconst, hinf, add_zero]

noncomputable def polyEmb : A[X] →+* O :=
  Polynomial.eval₂RingHom (constEmb A O hO) ⟨_, X_mem O ρ hρ⟩

theorem coe_polyEmb (p₀ : A[X]) :
    ((polyEmb A O ρ hO hρ p₀ : O) : RatFunc E) =
      algebraMap E[X] (RatFunc E) (p₀.map (algebraMap A E)) := by
  have hLR : O.subtype.comp (polyEmb A O ρ hO hρ) =
      (algebraMap E[X] (RatFunc E)).comp (Polynomial.mapRingHom (algebraMap A E)) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp only [polyEmb, RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
        Polynomial.coe_mapRingHom, Polynomial.map_C, RatFunc.algebraMap_C]
      rw [← RatFunc.algebraMap_eq_C]
      rfl
    · simp only [polyEmb, RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
        Polynomial.coe_mapRingHom, Polynomial.map_X, RatFunc.algebraMap_X]
      rfl
  have := DFunLike.congr_fun hLR p₀
  simpa using this

include hKA hArat hker in
theorem rho_polyEmb (p₀ : A[X]) :
    ρ (polyEmb A O ρ hO hρ p₀) =
      algebraMap (RatFunc K) L (algebraMap K[X] (RatFunc K) (p₀.map (sigma A hKA hArat))) := by
  have hLR : ρ.comp (polyEmb A O ρ hO hρ) =
      ((algebraMap (RatFunc K) L).comp (algebraMap K[X] (RatFunc K))).comp
        (Polynomial.mapRingHom (sigma A hKA hArat)) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp only [polyEmb, RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
        Polynomial.coe_mapRingHom, Polynomial.map_C, RatFunc.algebraMap_C]
      rw [rho_constEmb A hKA hArat O ρ hO hker hρ, ← RatFunc.algebraMap_eq_C]
    · simp only [polyEmb, RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
        Polynomial.coe_mapRingHom, Polynomial.map_X, RatFunc.algebraMap_X]
      exact rho_X O ρ hρ _
  have := DFunLike.congr_fun hLR p₀
  simpa using this

theorem map_sigma_ne_zero (f₁ : A[X]) (h1 : ∃ n, f₁.coeff n = 1) :
    f₁.map (sigma A hKA hArat) ≠ 0 := by
  obtain ⟨n, hn⟩ := h1
  intro h0
  have := congrArg (fun f => Polynomial.coeff f n) h0
  simp only [Polynomial.coeff_map, hn, map_one, Polynomial.coeff_zero] at this
  exact one_ne_zero this

include hKA hArat hker in

theorem isUnit_polyEmb (f₁ : A[X]) (h1 : ∃ n, f₁.coeff n = 1) :
    IsUnit (polyEmb A O ρ hO hρ f₁) := by
  apply isUnit_of_map_ne_zero O ρ hker
  rw [rho_polyEmb A hKA hArat O ρ hO hker hρ]
  exact fun h => map_sigma_ne_zero A hKA hArat f₁ h1 (IsFractionRing.injective K[X] (RatFunc K)
    ((algebraMap (RatFunc K) L).injective (by rw [h, map_zero, map_zero])))

include hKA hArat hO hker hρ in
theorem main [IsAlgClosed E] [DecidableEq (RatFunc K)] [DecidableEq (RatFunc E)]
    (G : O) (N : RatFunc K) (hN : N ≠ 0) (hGN : ρ G = algebraMap (RatFunc K) L N)
    (S : Finset E) (hSA : ∀ β ∈ S, β ∉ A)
    (hS : ∀ β : E, β ∉ A → (placeOfPoint E β).ord (G : RatFunc E) ≠ 0 → β ∈ S) :
    (placeInfty K).ord N =
      (placeInfty E).ord (G : RatFunc E) + ∑ β ∈ S, (placeOfPoint E β).ord (G : RatFunc E) := by
  classical

  have hσ : RingHom.ker (sigma A hKA hArat) = IsLocalRing.maximalIdeal A := ker_sigma A hKA hArat
  have hι : Function.Injective (algebraMap A E) := Subtype.val_injective
  have hιE : Function.Injective (algebraMap E[X] (RatFunc E)) := IsFractionRing.injective _ _
  have hιK : Function.Injective (algebraMap K[X] (RatFunc K)) := IsFractionRing.injective _ _
  set g : RatFunc E := (G : RatFunc E) with hg_def
  have hG0 : g ≠ 0 := by
    intro h
    apply hN
    have hG : G = 0 := Subtype.ext h
    rw [hG, map_zero, eq_comm, map_eq_zero_iff _ (algebraMap (RatFunc K) L).injective] at hGN
    exact hGN

  have hnum0 : g.num ≠ 0 := RatFunc.num_ne_zero hG0
  have hden0 : g.denom ≠ 0 := RatFunc.denom_ne_zero g
  obtain ⟨c₁, p, hc₁, hp, hp1⟩ := exists_normalization A g.num hnum0
  obtain ⟨c₂, q, hc₂, hq, hq1⟩ := exists_normalization A g.denom hden0
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [Polynomial.map_zero, mul_zero] at hp
    exact hnum0 hp
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [Polynomial.map_zero, mul_zero] at hq
    exact hden0 hq
  have hpE0 : p.map (algebraMap A E) ≠ 0 := (Polynomial.map_ne_zero_iff hι).mpr hp0
  have hqE0 : q.map (algebraMap A E) ≠ 0 := (Polynomial.map_ne_zero_iff hι).mpr hq0
  set P : O := polyEmb A O ρ hO hρ p with hP_def
  set Q : O := polyEmb A O ρ hO hρ q with hQ_def
  have hPu : IsUnit P := isUnit_polyEmb A hKA hArat O ρ hO hker hρ p hp1
  have hQu : IsUnit Q := isUnit_polyEmb A hKA hArat O ρ hO hker hρ q hq1
  have hPc : (P : RatFunc E) = algebraMap E[X] (RatFunc E) (p.map (algebraMap A E)) :=
    coe_polyEmb A O ρ hO hρ p
  have hQc : (Q : RatFunc E) = algebraMap E[X] (RatFunc E) (q.map (algebraMap A E)) :=
    coe_polyEmb A O ρ hO hρ q
  have hPv0 : (P : RatFunc E) ≠ 0 := by rw [hPc]; exact (map_ne_zero_iff _ hιE).mpr hpE0
  have hQv0 : (Q : RatFunc E) ≠ 0 := by rw [hQc]; exact (map_ne_zero_iff _ hιE).mpr hqE0

  have hgd : g * algebraMap E[X] (RatFunc E) g.denom = algebraMap E[X] (RatFunc E) g.num :=
    ((div_eq_iff ((map_ne_zero_iff _ hιE).mpr hden0)).mp (RatFunc.num_div_denom g)).symm
  have hE1 : g * (algebraMap E (RatFunc E) c₂ * (Q : RatFunc E)) =
      algebraMap E (RatFunc E) c₁ * (P : RatFunc E) := by
    rw [hPc, hQc, RatFunc.algebraMap_eq_C, ← RatFunc.algebraMap_C, ← RatFunc.algebraMap_C,
      ← map_mul, ← map_mul, ← hp, ← hq, hgd]

  set c : E := c₁ / c₂ with hc_def
  have hc0 : c ≠ 0 := div_ne_zero hc₁ hc₂
  have hcE2 : algebraMap E (RatFunc E) c₂ ≠ 0 := (map_ne_zero _).mpr hc₂
  have hcv : algebraMap E (RatFunc E) c = g * (Q : RatFunc E) * (P : RatFunc E)⁻¹ := by
    rw [hc_def, map_div₀, eq_mul_inv_iff_mul_eq₀ hPv0, div_mul_eq_mul_div,
      div_eq_iff hcE2, ← hE1]
    ring
  have hcO : algebraMap E (RatFunc E) c ∈ O := by
    rw [hcv]
    exact O.mul_mem _ _ (O.mul_mem _ _ G.2 Q.2) ((isUnit_iff_inv_mem O P hPv0).mp hPu)
  have hcA : c ∈ A := (hO c).mp hcO

  have hOid : constEmb A O hO ⟨c, hcA⟩ * P = G * Q := by
    apply Subtype.ext
    show algebraMap E (RatFunc E) c * (P : RatFunc E) = g * (Q : RatFunc E)
    rw [hcv, mul_assoc, inv_mul_cancel₀ hPv0, mul_one]
  have hred := congrArg ρ hOid
  rw [map_mul, map_mul, rho_constEmb A hKA hArat O ρ hO hker hρ, hGN, hP_def, hQ_def,
    rho_polyEmb A hKA hArat O ρ hO hker hρ, rho_polyEmb A hKA hArat O ρ hO hker hρ,
    ← map_mul, ← map_mul] at hred
  have hE2 : algebraMap K (RatFunc K) (sigma A hKA hArat ⟨c, hcA⟩) *
      algebraMap K[X] (RatFunc K) (p.map (sigma A hKA hArat)) =
        N * algebraMap K[X] (RatFunc K) (q.map (sigma A hKA hArat)) :=
    (algebraMap (RatFunc K) L).injective hred
  set pbar := p.map (sigma A hKA hArat) with hpbar
  set qbar := q.map (sigma A hKA hArat) with hqbar
  have hpbar0 : pbar ≠ 0 := map_sigma_ne_zero A hKA hArat p hp1
  have hqbar0 : qbar ≠ 0 := map_sigma_ne_zero A hKA hArat q hq1
  have hpbarv0 : algebraMap K[X] (RatFunc K) pbar ≠ 0 := (map_ne_zero_iff _ hιK).mpr hpbar0
  have hqbarv0 : algebraMap K[X] (RatFunc K) qbar ≠ 0 := (map_ne_zero_iff _ hιK).mpr hqbar0
  have hσc0 : sigma A hKA hArat ⟨c, hcA⟩ ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_mul] at hE2
    exact (mul_ne_zero hN hqbarv0) hE2.symm
  have hσcv0 : algebraMap K (RatFunc K) (sigma A hKA hArat ⟨c, hcA⟩) ≠ 0 :=
    (map_ne_zero _).mpr hσc0

  have hordN : (placeInfty K).ord N = (qbar.natDegree : ℤ) - pbar.natDegree := by
    have h1 := congrArg (placeInfty K).ord hE2
    rw [(placeInfty K).ord_mul hσcv0 hpbarv0, (placeInfty K).ord_mul hN hqbarv0,
      ord_placeInfty_algebraMap K hpbar0, ord_placeInfty_algebraMap K hqbar0,
      RatFunc.algebraMap_eq_C, ord_placeInfty_eq_neg_intDegree K
        (show (RatFunc.C (sigma A hKA hArat ⟨c, hcA⟩) : RatFunc K) ≠ 0 from
          RatFunc.algebraMap_eq_C (K := K) ▸ hσcv0),
      RatFunc.intDegree_C] at h1
    linarith

  have hsplitp : Multiset.card (p.map (algebraMap A E)).roots = p.natDegree := by
    rw [IsAlgClosed.card_roots_eq_natDegree, Polynomial.natDegree_map_eq_of_injective hι]
  have hsplitq : Multiset.card (q.map (algebraMap A E)).roots = q.natDegree := by
    rw [IsAlgClosed.card_roots_eq_natDegree, Polynomial.natDegree_map_eq_of_injective hι]
  have hdegp : pbar.natDegree = Multiset.card p.roots :=
    ValuationSubring.natDegree_map_eq_card_roots_of_splits A _ hσ p hpbar0 hsplitp
  have hdegq : qbar.natDegree = Multiset.card q.roots :=
    ValuationSubring.natDegree_map_eq_card_roots_of_splits A _ hσ q hqbar0 hsplitq
  set Rp := (p.map (algebraMap A E)).roots with hRp
  set Rq := (q.map (algebraMap A E)).roots with hRq
  have hcardp := card_roots_map_eq A p hp0
  have hcardq := card_roots_map_eq A q hq0

  have hordg : (placeInfty E).ord g = (q.natDegree : ℤ) - p.natDegree := by
    rw [ord_placeInfty_eq_neg_intDegree E hG0, RatFunc.intDegree, hp, hq,
      Polynomial.natDegree_C_mul hc₁, Polynomial.natDegree_C_mul hc₂,
      Polynomial.natDegree_map_eq_of_injective hι, Polynomial.natDegree_map_eq_of_injective hι]
    ring

  have hordβ : ∀ β : E, (placeOfPoint E β).ord g = (Rp.count β : ℤ) - Rq.count β := by
    intro β
    rw [← RatFunc.num_div_denom g, ord_placeOfPoint_div E β hnum0 hden0, hp, hq,
      ← Polynomial.count_roots, ← Polynomial.count_roots, Polynomial.roots_C_mul _ hc₁,
      Polynomial.roots_C_mul _ hc₂]

  set T : Finset E := S ∪ (Rp.filter (fun β => β ∉ A)).toFinset ∪
    (Rq.filter (fun β => β ∉ A)).toFinset with hT
  have hTA : ∀ β ∈ T, β ∉ A := by
    intro β hβ
    simp only [hT, Finset.mem_union, Multiset.mem_toFinset, Multiset.mem_filter] at hβ
    rcases hβ with (hβ | hβ) | hβ
    · exact hSA β hβ
    · exact hβ.2
    · exact hβ.2
  have hST : S ⊆ T := fun β hβ => by
    simp only [hT, Finset.mem_union]
    exact Or.inl (Or.inl hβ)
  have hsumST : ∑ β ∈ S, (placeOfPoint E β).ord g = ∑ β ∈ T, (placeOfPoint E β).ord g := by
    apply Finset.sum_subset hST
    intro β hβT hβS
    by_contra h
    exact hβS (hS β (hTA β hβT) h)
  have hTp : ∀ β ∈ Rp, β ∉ A → β ∈ T := by
    intro β hβ hβA
    simp only [hT, Finset.mem_union, Multiset.mem_toFinset, Multiset.mem_filter]
    exact Or.inl (Or.inr ⟨hβ, hβA⟩)
  have hTq : ∀ β ∈ Rq, β ∉ A → β ∈ T := by
    intro β hβ hβA
    simp only [hT, Finset.mem_union, Multiset.mem_toFinset, Multiset.mem_filter]
    exact Or.inr ⟨hβ, hβA⟩
  have hsump : ∑ β ∈ T, Rp.count β = Multiset.card (Rp.filter (fun β => β ∉ A)) :=
    sum_count_eq_card_filter A Rp T hTp hTA
  have hsumq : ∑ β ∈ T, Rq.count β = Multiset.card (Rq.filter (fun β => β ∉ A)) :=
    sum_count_eq_card_filter A Rq T hTq hTA
  have hsumT : ∑ β ∈ T, (placeOfPoint E β).ord g =
      (Multiset.card (Rp.filter (fun β => β ∉ A)) : ℤ) -
        Multiset.card (Rq.filter (fun β => β ∉ A)) := by
    rw [← hsump, ← hsumq, Finset.sum_congr rfl (fun β _ => hordβ β), Finset.sum_sub_distrib]
    push_cast
    ring

  rw [hordN, hordg, hsumST, hsumT, hdegp, hdegq]
  have e1 : (p.natDegree : ℤ) = Multiset.card p.roots +
      Multiset.card (Rp.filter (fun β => β ∉ A)) := by
    rw [← hsplitp, hRp]
    exact_mod_cast hcardp
  have e2 : (q.natDegree : ℤ) = Multiset.card q.roots +
      Multiset.card (Rq.filter (fun β => β ∉ A)) := by
    rw [← hsplitq, hRq]
    exact_mod_cast hcardq
  linarith

end Reduction

end PlaceInftyReduction

end AlgebraicCurve

open AlgebraicCurve.PlaceInftyReduction in
theorem AlgebraicCurve.RationalFunctionField.ord_placeInfty_eq_ord_placeInfty_add_sum_ord_placeOfPoint_of_reduction
    (K E L : Type*) [Field K] [Field E] [Field L] [Algebra K E] [IsAlgClosed E]
    [DecidableEq (RatFunc K)] [DecidableEq (RatFunc E)] [Algebra (RatFunc K) L]
    (A : ValuationSubring E)
    (hKA : ∀ k : K, algebraMap K E k ∈ A)
    (hArat : ∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1)
    (O : ValuationSubring (RatFunc E)) (ρ : O →+* L)
    (hO : ∀ c : E, algebraMap E (RatFunc E) c ∈ O ↔ c ∈ A)
    (hker : RingHom.ker ρ = IsLocalRing.maximalIdeal O)
    (hρ : ∀ p : K[X],
      ∃ h : algebraMap E[X] (RatFunc E) (p.map (algebraMap K E)) ∈ O,
        ρ ⟨_, h⟩ = algebraMap (RatFunc K) L (algebraMap K[X] (RatFunc K) p))
    (G : O) (N : RatFunc K) (hN : N ≠ 0) (hGN : ρ G = algebraMap (RatFunc K) L N)
    (S : Finset E) (hSA : ∀ β ∈ S, β ∉ A)
    (hS : ∀ β : E, β ∉ A → (placeOfPoint E β).ord (G : RatFunc E) ≠ 0 → β ∈ S) :
    (placeInfty K).ord N =
      (placeInfty E).ord (G : RatFunc E) + ∑ β ∈ S, (placeOfPoint E β).ord (G : RatFunc E) :=
  main A hKA hArat O ρ hO hker hρ G N hN hGN S hSA hS
