/-
  T14 — the modular polynomial at the slot: the conjugates as `TS` values,
  `phiProd`'s roots, and `phiAtSeed`.

  This is the shared prelude the pin repeats in up to thirteen of the seventeen
  remaining `functionFieldGeneration` files (the survey's counts: `phiAtSeed` in
  13 carriers at 26–74 uses each, `phiProd_conj_eq` in 12, `phiAtSeed_eval_symm`
  in 7). It is written **once** here so T15–T19 import it instead of each
  re-copying it.

  The module holds:

  * the three live bridges from `conj`/`coeffEmb ∘ qExpand` to `TS`
    (`iota_jq`, `conj_zero_eq`, `conj_succ_eq`) — promoted out of T13's
    `PhiGenSplits.lean`, which kept them `private`;
  * the conjugate product's expansion and roots (`phiProd_conj_eq`,
    `roots_phiProd_conj`, `roots_phiProd_conj_nodup`);
  * `phiAtSeed` — `Φ` evaluated at `X = x` as a polynomial in `Y` — and its
    naturality/monicity/degree/vanishing lemmas, plus the subfield and
    injectivity/symmetry corollaries.

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  `P2M/Sol/S_ModularCurve_jqN_prime_not_mem_full.lean` lines 106–194 and
  351–404, and `P2M/Sol/S_ModularCurve_jqN_pow_not_mem_adjoin_full.lean` lines
  400–430 (the `phiAtSeed_eval_symm`/`_down` and `aeval_intermediateField`
  block, which the sibling file carries publicly). All statements are the pin's
  verbatim.

  ## Layering

  `Defs/PhiAtSlot.lean` is upstream of the Φ_p cone: it imports only `Defs/` modules
  (`TS`, `Jq`, `PhiGen`, `Polynomial`) and mathlib. The at-slot roots API, which
  consumes T13's `PhiGen.splits_prime_at_slot`, is the separate downstream
  `ModularCurve/PhiSlotRoots.lean`. The three `TS`-arithmetic members of the
  prelude (`iota_jqN`, `qTwist_TS_one_cycle`, `qExpand_qTwist_TS`, and
  `qExpand_qTwist_notMem_range_qExpand`) live beside `TS` in `Defs/TS.lean`, and
  the twist-equivalence block lives in `Defs/Twist.lean`, because this module's
  prelude is not the only home for them.

  ## Assumptions

  `Defs/TS` (`TS`, `TS_injective`), `Defs/Jq` (`jq`, `jqN`, `evalAtJ`),
  `Defs/PhiGen` (`conj`, `phiProd`, `EvalSymm`), `Defs/Polynomial`
  (`ModularPolynomialData`); mathlib's polynomial/`MultiSet`/`IntermediateField`
  API.
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import FLTForHuman.ModularCurve.Defs.TS
import FLTForHuman.ModularCurve.Defs.Jq
import FLTForHuman.ModularCurve.Defs.PhiGen
import FLTForHuman.ModularCurve.Defs.Polynomial

set_option autoImplicit false

noncomputable section

open Polynomial HahnSeries IntermediateField

namespace ModularCurve

open PhiGen

variable {K : Type*} [Field K] [Algebra ℚ K]

/-! ## The `conj`/`TS` bridges -/

/-- `coeffEmb K (qExpand ℚ N jq) = j(q ^ N)` as a `TS` value. Promoted from
T13's private copy; the pin also has it public in
`S_ModularCurve_functionFieldGeneration.lean`. -/
theorem iota_jq (N : ℕ) [NeZero N] : coeffEmb K (qExpand ℚ N jq) = TS K N 1 := by
  rw [coeffEmb_qExpand, TS, qTwist_one_apply]

/-- The extra conjugate is `j(q ^ (p * p))`. -/
theorem conj_zero_eq (p : ℕ) [Fact p.Prime] (ζ : Kˣ) :
    conj p ζ (0 : Fin (p + 1)) = TS K (p * p) 1 := by
  rw [conj_zero, TS, qTwist_one_apply]

/-- The `b`-th finite conjugate is `j(ζ ^ b q)`. -/
theorem conj_succ_eq (p : ℕ) [Fact p.Prime] (ζ : Kˣ) (b : Fin p) :
    conj p ζ b.succ = TS K 1 (ζ ^ (b : ℕ)) := by
  rw [conj_succ, TS, qExpand_one_apply]

/-! ## The conjugate product -/

/-- The product over the `p + 1` conjugates expands as
`(X - j(q ^ p²)) · ∏_{b < p} (X - j(ζ ^ b q))`. -/
theorem phiProd_conj_eq (p : ℕ) [Fact p.Prime] (ζ : Kˣ) :
    phiProd p (conj p ζ) = (Polynomial.X - Polynomial.C (TS K (p * p) 1)) *
      ∏ b ∈ Finset.range p, (Polynomial.X - Polynomial.C (TS K 1 (ζ ^ b))) := by
  rw [phiProd, Fin.prod_univ_succ, conj_zero_eq]
  congr 1
  rw [← Fin.prod_univ_eq_prod_range (fun b => Polynomial.X - Polynomial.C (TS K 1 (ζ ^ b))) p]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [conj_succ_eq]

/-- The roots of `phiProd p (conj p ζ)` are exactly the `p + 1` conjugate
values. -/
theorem roots_phiProd_conj (p : ℕ) [Fact p.Prime] (ζ : Kˣ) :
    (phiProd p (conj p ζ)).roots =
      TS K (p * p) 1 ::ₘ (Multiset.range p).map (fun b => TS K 1 (ζ ^ b)) := by
  classical
  rw [phiProd_conj_eq]
  have h1 : (Polynomial.X - Polynomial.C (TS K (p * p) 1) : Polynomial (LaurentSeries K)) ≠ 0 :=
    Polynomial.X_sub_C_ne_zero _
  have h2 : (∏ b ∈ Finset.range p, (Polynomial.X - Polynomial.C (TS K 1 (ζ ^ b)))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun b _ => Polynomial.X_sub_C_ne_zero _
  rw [Polynomial.roots_mul (mul_ne_zero h1 h2), Polynomial.roots_X_sub_C, Finset.prod_eq_multiset_prod,
    Finset.range_val]
  have hm : (Multiset.map (fun b => Polynomial.X - Polynomial.C (TS K 1 (ζ ^ b))) (Multiset.range p)) =
      ((Multiset.range p).map (fun b => TS K 1 (ζ ^ b))).map (fun a => Polynomial.X - Polynomial.C a) := by
    rw [Multiset.map_map]; rfl
  rw [hm, Polynomial.roots_multiset_prod_X_sub_C, Multiset.singleton_add]

/-- Those `p + 1` roots are distinct when `ζ` is primitive: both the extra
conjugate (at level `p²`) and the finite ones (by `IsPrimitiveRoot.pow_inj`) are
separated. -/
theorem roots_phiProd_conj_nodup (p : ℕ) [hp : Fact p.Prime] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) p) :
    (TS K (p * p) 1 ::ₘ (Multiset.range p).map (fun b => TS K 1 (ζ ^ b))).Nodup := by
  refine Multiset.nodup_cons.mpr ⟨?_, ?_⟩
  · intro hmem
    obtain ⟨b, -, hb⟩ := Multiset.mem_map.mp hmem
    have := (TS_injective hb).1
    have h2 := hp.out.two_le
    nlinarith
  · refine (Multiset.nodup_range p).map_on fun b hb b' hb' hbb' => ?_
    rw [Multiset.mem_range] at hb hb'
    have hu := (TS_injective hbb').2
    have hζu : IsPrimitiveRoot ζ p := IsPrimitiveRoot.coe_units_iff.mp hζ
    exact hζu.pow_inj hb hb' hu

/-! ## `phiAtSeed` -/

/-- Evaluate `Φ` at `X = x`, as a polynomial in `Y`: the coefficient ring is
`R` via the unique `ℤ →+* R`. -/
def phiAtSeed {R : Type*} [CommRing R] {n : ℕ} [NeZero n] (data : ModularPolynomialData n) (x : R) :
    Polynomial R :=
  data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom R) x)

/-- `phiAtSeed` is natural in the coefficient ring. -/
theorem phiAtSeed_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ} [NeZero n]
    (data : ModularPolynomialData n) (x : R) (f : R →+* S) :
    (phiAtSeed data x).map f = phiAtSeed data (f x) := by
  rw [phiAtSeed, phiAtSeed, Polynomial.map_map]
  congr 1
  refine Polynomial.ringHom_ext' ?_ ?_
  · exact RingHom.ext_int _ _
  · simp

/-- `phiAtSeed` is monic. -/
theorem phiAtSeed_monic {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ} [NeZero n]
    (data : ModularPolynomialData n) (x : R) : (phiAtSeed data x).Monic :=
  data.monic.map _

/-- `phiAtSeed` has degree `ψ(n)`. -/
theorem phiAtSeed_natDegree {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ} [NeZero n]
    (data : ModularPolynomialData n) (x : R) : (phiAtSeed data x).natDegree = dedekindPsi n := by
  rw [phiAtSeed, data.monic.natDegree_map, data.natDegree_eq]

/-- `phiAtSeed` vanishes at `(jq, jqN n)`. -/
theorem phiAtSeed_jq_eval (n : ℕ) [NeZero n] (data : ModularPolynomialData n) :
    (phiAtSeed data jq).eval (jqN n) = 0 := by
  have h := data.eval_eq_zero
  rw [phiAtSeed, Polynomial.eval_map]
  convert h using 2; try rfl
  refine Polynomial.ringHom_ext' ?_ ?_
  · exact RingHom.ext_int _ _
  · simp [evalAtJ_X]

/-- A vanishing `phiAtSeed` value stays vanishing after any ring map. -/
theorem phiAtSeed_eval_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ} [NeZero n]
    (data : ModularPolynomialData n) (x y : R) (f : R →+* S) (h : (phiAtSeed data x).eval y = 0) :
    (phiAtSeed data (f x)).eval (f y) = 0 := by
  rw [← phiAtSeed_map, Polynomial.eval_map, Polynomial.eval₂_hom, h, map_zero]

/-- `phiAtSeed` vanishes at `(jqN M, jqN (M * n))`. -/
theorem phiAtSeed_jqN_eval (n : ℕ) [NeZero n] (data : ModularPolynomialData n) (M : ℕ) [NeZero M] :
    (phiAtSeed data (jqN M)).eval (jqN (M * n)) = 0 := by
  have h := phiAtSeed_eval_map data jq (jqN n) (qExpand ℚ M) (phiAtSeed_jq_eval n data)
  rwa [jqN, qExpand_qExpand] at h

/-- The coefficient-extended form of `phiAtSeed_jqN_eval`: it vanishes at
`(coeffEmb (qExpand ℚ A (jqN M)), coeffEmb (qExpand ℚ A (jqN (M * n))))`. -/
theorem phiAtSeed_iota_eval {K : Type*} [Field K] [Algebra ℚ K] (A : ℕ) [NeZero A] (n : ℕ) [NeZero n]
    (data : ModularPolynomialData n) (M : ℕ) [NeZero M] :
    (phiAtSeed data (coeffEmb K (qExpand ℚ A (jqN M)))).eval (coeffEmb K (qExpand ℚ A (jqN (M * n)))) = 0 :=
  phiAtSeed_eval_map data _ _ ((coeffEmb K).comp (qExpand ℚ A)) (phiAtSeed_jqN_eval n data M)

/-! ## `phiAtSeed` on a subfield, under injective maps, and the symmetric form -/

/-- An `aeval` that vanishes after embedding a subfield element vanishes before
it: the injection `E → L`. -/
theorem aeval_intermediateField_eq_zero {F₀ L : Type*} [Field F₀] [Field L]
    [Algebra F₀ L] {E : IntermediateField F₀ L} {P : Polynomial F₀} {x : E}
    (h : Polynomial.aeval (E.val x) P = 0) : Polynomial.aeval x P = 0 := by
  have h1 := Polynomial.aeval_algHom_apply E.val x P
  rw [h] at h1
  have h2 : E.val (Polynomial.aeval x P) = E.val 0 := by rw [← h1, map_zero]
  exact RingHom.injective (E.val : E →+* L) h2

/-- A vanishing `phiAtSeed` value pulls back along an injective ring map. -/
theorem phiAtSeed_eval_of_injective {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    [NeZero n] (data : ModularPolynomialData n) (x y : R) (f : R →+* S)
    (hf : Function.Injective f) (h : (phiAtSeed data (f x)).eval (f y) = 0) :
    (phiAtSeed data x).eval y = 0 := by
  rw [← phiAtSeed_map, Polynomial.eval_map, Polynomial.eval₂_hom] at h
  exact (injective_iff_map_eq_zero f).mp hf _ h

/-- `phiAtSeed` is symmetric when `Φ` is: `(phiAtSeed data x).eval y` and
`(phiAtSeed data y).eval x` agree. -/
theorem phiAtSeed_eval_symm {n : ℕ} [NeZero n] (data : ModularPolynomialData n)
    (hs : EvalSymm data.Φ) (x y : LaurentSeries ℚ) :
    (phiAtSeed data x).eval y = (phiAtSeed data y).eval x := by
  have hhom : ∀ z : LaurentSeries ℚ,
      Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℚ)) z
        = (Polynomial.aeval (R := ℤ) z).toRingHom := by
    intro z
    refine Polynomial.ringHom_ext' ?_ ?_
    · exact RingHom.ext_int _ _
    · simp [Polynomial.coe_eval₂RingHom]
  rw [phiAtSeed, phiAtSeed, Polynomial.eval_map, Polynomial.eval_map, hhom x, hhom y]
  exact hs x y

/-- The symmetric direction of `phiAtSeed_jqN_eval`: it also vanishes at
`(jqN (M * q), jqN M)`. -/
theorem phiAtSeed_jqN_eval_down (q : ℕ) [NeZero q] (data : ModularPolynomialData q)
    (hs : EvalSymm data.Φ) (M : ℕ) [NeZero M] :
    (phiAtSeed data (jqN (M * q))).eval (jqN M) = 0 := by
  rw [← phiAtSeed_eval_symm data hs]; exact phiAtSeed_jqN_eval q data M

end ModularCurve

end
