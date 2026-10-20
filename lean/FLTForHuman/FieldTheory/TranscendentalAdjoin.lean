/-
  A purely transcendental simple extension `L(x)` and the degree of a polynomial
  whose value lies in an adjoin:

      `IsIntegrallyClosed (Algebra.adjoin L {x})`                     (`x` transcendental)
      `aeval x c * (xⁿ)⁻¹ ∈ adjoin L {x⁻¹} → c.natDegree ≤ n`
      `aeval x c = (minpoly (adjoin L {x}) f).coeff j → c.natDegree ≤ (deg − j) * m`

  under the valuation hypothesis `f * (x ^ m)⁻¹ ∈ V` for every valuation subring
  `V` of `F` containing `L` but not `x`.

  The port of the three pin leaves

      `Subalgebra.isIntegrallyClosed_adjoin_singleton_of_transcendental` (36 pin lines),
      `Polynomial.natDegree_le_of_aeval_mul_inv_pow_mem_adjoin_inv` (53),
      `Polynomial.natDegree_aeval_symm_minpoly_adjoin_coeff_le_of_transcendental` (154),

  in the pin's own namespaces (`Subalgebra`, then `Polynomial`); the third node's
  proof uses the first two, which is why the three land in one module. Statements
  are the `Theorems/` wrappers', proofs the matching `P2M/Sol/S_…` files'; the
  pin's `solution` wrappers, `p2m_*` directives and `set_option maxHeartbeats` are
  not ported.

  The mathematics. `aeval x : L[X] →ₐ[L] adjoin L {x}` is bijective for
  transcendental `x`, so `adjoin L {x}` is a quotient-free image of a PID and hence
  a principal ideal ring — integrally closed in its fraction field, i.e.
  `IsIntegrallyClosed`. If `aeval x c · (xⁿ)⁻¹ = p(x⁻¹)` then clearing the
  denominators of the reversal `p.reflect N` (`N = max n (deg p)`) gives
  `p.reflect N = c · X^(N - n)`, and degrees compare. The main node replaces `x` by
  `x⁻¹` (transcendence and integral closedness are invariant), writes
  `g = f · (x^m)⁻¹`, notes that `g` is integral over `adjoin L {x⁻¹}` because it is
  integral at every valuation subring (`iInf_valuationSubring_superset`), and
  scales the minimal polynomial: `minpoly g = (minpoly f).scaleRoots (x^m)⁻¹`,
  whose `j`-th coefficient is `(minpoly f).coeff j · (x^m)^-(d - j)`; the degree
  bound on `c` is then the previous node at `n = (d - j) * m`.

  Assumes: mathlib `v4.34.0` only — nothing from earlier modules of the port.

  spec-pin: Theorems/Thm_Subalgebra_isIntegrallyClosed_adjoin_singleton_of_transcendental.lean
  spec-pin: P2M/Sol/S_Subalgebra_isIntegrallyClosed_adjoin_singleton_of_transcendental.lean
  spec-pin: Theorems/Thm_Polynomial_natDegree_le_of_aeval_mul_inv_pow_mem_adjoin_inv.lean
  spec-pin: P2M/Sol/S_Polynomial_natDegree_le_of_aeval_mul_inv_pow_mem_adjoin_inv.lean
  spec-pin: Theorems/Thm_Polynomial_natDegree_aeval_symm_minpoly_adjoin_coeff_le_of_transcendental.lean
  spec-pin: P2M/Sol/S_Polynomial_natDegree_aeval_symm_minpoly_adjoin_coeff_le_of_transcendental.lean
  Drift against `v4.34.0` — statements untouched. port:88, 124, 183, 190, 192: five
  `haveI` become `have` (`linter.style.haveILetI`'s own suggestion — `IsPrincipalIdealRing`,
  `Invertible` twice and `IsIntegrallyClosed` twice); instance search still resolves each
  local class hypothesis, which the build confirms. The pin's
  `set_option synthInstance.maxHeartbeats 800000 in` on the `scaleRoots` step is dropped:
  that step elaborates inside the 200,000-heartbeat edit-loop cap. The pin's
  `import Mathlib` becomes the seven named modules above.

-/

import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic

set_option autoImplicit false

open Polynomial
open scoped IntermediateField.algebraAdjoinAdjoin

namespace Subalgebra

/-- A simple extension of a field by a transcendental element is integrally closed:
it is isomorphic to a polynomial ring, hence a principal ideal ring, hence
integrally closed. -/
theorem isIntegrallyClosed_adjoin_singleton_of_transcendental
    {L : Type*} [Field L] {F : Type*} [CommRing F] [IsDomain F] [Algebra L F]
    (x : F) (hxL : Transcendental L x) :
    IsIntegrallyClosed (Algebra.adjoin L ({x} : Set F)) := by
  classical

  have hinj : Function.Injective (Polynomial.aeval (R := L) x) :=
    transcendental_iff_injective.mp hxL
  have hrange : (Polynomial.aeval (R := L) x).range = Algebra.adjoin L ({x} : Set F) :=
    (Algebra.adjoin_singleton_eq_range_aeval L x).symm
  let e : Polynomial L ≃ₐ[L] Algebra.adjoin L ({x} : Set F) :=
    (AlgEquiv.ofInjective (Polynomial.aeval (R := L) x) hinj).trans
      (Subalgebra.equivOfEq _ _ hrange)

  have : IsPrincipalIdealRing (Algebra.adjoin L ({x} : Set F)) := by
    constructor
    intro I

    obtain ⟨a, ha⟩ := IsPrincipalIdealRing.principal (I.comap e.toRingHom)
    refine ⟨e a, ?_⟩
    show I = Ideal.span {e a}
    rw [← Ideal.map_comap_of_surjective e.toRingHom e.surjective I,
      show Ideal.comap e.toRingHom I = Ideal.span {a} from ha,
      Ideal.map_span, Set.image_singleton]
    rfl

  infer_instance

end Subalgebra

namespace Polynomial

/-- If `aeval x c * (xⁿ)⁻¹` lies in `L(x⁻¹)` for transcendental `x ≠ 0`, then
`c.natDegree ≤ n`. -/
theorem natDegree_le_of_aeval_mul_inv_pow_mem_adjoin_inv
    {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]
    (x : F) (hxL : Transcendental L x) (hx0 : x ≠ 0)
    (c : Polynomial L) (n : ℕ)
    (h : Polynomial.aeval x c * (x ^ n)⁻¹ ∈ Algebra.adjoin L ({x⁻¹} : Set F)) :
    c.natDegree ≤ n := by
  classical
  by_cases hc0 : c = 0
  · simp [hc0]

  rw [Algebra.adjoin_singleton_eq_range_aeval L x⁻¹, AlgHom.mem_range] at h
  obtain ⟨p, hp⟩ := h
  set N : ℕ := max n p.natDegree with hN
  have hnN : n ≤ N := le_max_left _ _
  have hpN : p.natDegree ≤ N := le_max_right _ _

  have : Invertible (x⁻¹) := invertibleOfNonzero (inv_ne_zero hx0)
  have hxinvinv : ⅟(x⁻¹) = x := by rw [invOf_eq_inv, inv_inv]
  have hrefl : Polynomial.aeval x (p.reflect N) * (x⁻¹) ^ N = Polynomial.aeval x⁻¹ p := by
    rw [Polynomial.aeval_def, Polynomial.aeval_def]
    have := Polynomial.eval₂_reflect_mul_pow (algebraMap L F) x⁻¹ N p hpN
    rwa [hxinvinv] at this

  have heq : Polynomial.aeval x (p.reflect N) = Polynomial.aeval x (c * Polynomial.X ^ (N - n)) := by
    have hxN0 : (x ^ N : F) ≠ 0 := pow_ne_zero N hx0
    have h1 : Polynomial.aeval x (p.reflect N) * (x⁻¹) ^ N * x ^ N =
        Polynomial.aeval x c * (x ^ n)⁻¹ * x ^ N := by rw [hrefl, hp]
    rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hx0, one_pow, mul_one] at h1
    rw [h1, map_mul, Polynomial.aeval_X_pow, mul_assoc, mul_comm ((x ^ n)⁻¹) (x ^ N),
      ← pow_sub₀ x hx0 hnN]

  have hpoly : p.reflect N = c * Polynomial.X ^ (N - n) :=
    (transcendental_iff_injective.mp hxL) heq

  have hdeg : c.natDegree + (N - n) ≤ N := by
    have hXne : (Polynomial.X : Polynomial L) ^ (N - n) ≠ 0 :=
      pow_ne_zero _ Polynomial.X_ne_zero
    calc c.natDegree + (N - n)
        = (c * Polynomial.X ^ (N - n)).natDegree := by
          rw [Polynomial.natDegree_mul hc0 hXne, Polynomial.natDegree_X_pow]
      _ = (p.reflect N).natDegree := by rw [hpoly]
      _ ≤ max N p.natDegree := Polynomial.natDegree_reflect_le
      _ = N := max_eq_left hpN
  omega

end Polynomial

namespace Polynomial

/-- The `j`-th coefficient of the minimal polynomial of an integral `f`, read as a
polynomial over `L` at a transcendental `x`: the polynomial `c` representing it has
`c.natDegree ≤ (deg minpoly f − j) * m`, provided `f * (x^m)⁻¹` lies in every
valuation subring containing `L` but not `x`. -/
theorem natDegree_aeval_symm_minpoly_adjoin_coeff_le_of_transcendental
    {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]
    (x : F) (hxL : Transcendental L x) (hx0 : x ≠ 0)
    (f : F) (hint : IsIntegral (Algebra.adjoin L ({x} : Set F)) f) (m : ℕ)
    (h₂ : ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → x ∉ V →
      f * (x ^ m)⁻¹ ∈ V)
    (j : ℕ) (c : Polynomial L)
    (hc : Polynomial.aeval x c =
      (((minpoly (Algebra.adjoin L ({x} : Set F)) f).coeff j :
        Algebra.adjoin L ({x} : Set F)) : F)) :
    c.natDegree ≤ ((minpoly (Algebra.adjoin L ({x} : Set F)) f).natDegree - j) * m := by
  classical

  set q : Polynomial (Algebra.adjoin L ({x} : Set F)) :=
    minpoly (Algebra.adjoin L ({x} : Set F)) f with hq
  set d : ℕ := q.natDegree with hd
  set n : ℕ := (d - j) * m with hn
  set y : F := x⁻¹ with hy
  have hy0 : y ≠ 0 := inv_ne_zero hx0
  have hyL : Transcendental L y := by
    intro ⟨p, hp0, hpy⟩
    refine hxL ⟨p.reflect p.natDegree, fun h => hp0 (Polynomial.reflect_eq_zero_iff.mp h), ?_⟩
    have : Invertible y := invertibleOfNonzero hy0
    rw [Polynomial.aeval_def, show x = ⅟y by rw [invOf_eq_inv, hy, inv_inv],
      Polynomial.eval₂_reflect_eq_zero_iff (algebraMap L F) y p.natDegree p (le_refl _),
      ← Polynomial.aeval_def]
    exact hpy
  set g : F := f * (x ^ m)⁻¹ with hg

  have hICx : IsIntegrallyClosed (Algebra.adjoin L ({x} : Set F)) :=
    Subalgebra.isIntegrallyClosed_adjoin_singleton_of_transcendental x hxL
  have hICy : IsIntegrallyClosed (Algebra.adjoin L ({y} : Set F)) :=
    Subalgebra.isIntegrallyClosed_adjoin_singleton_of_transcendental y hyL

  have hfallV : ∀ V : ValuationSubring F,
      (Algebra.adjoin L ({x} : Set F) : Set F) ⊆ (V : Set F) → f ∈ V := by
    intro V hLxV
    have hiInf := iInf_valuationSubring_superset (K := F)
      (s := ((Algebra.adjoin L ({x} : Set F)).toSubring : Set F))
    rw [Subring.closure_eq] at hiInf
    have hfmem : f ∈ (integralClosure
        (Algebra.adjoin L ({x} : Set F)).toSubring F).toSubring := hint
    rw [← hiInf] at hfmem
    exact (Subring.mem_iInf.mp hfmem) ⟨V, hLxV⟩

  have hgint : IsIntegral (Algebra.adjoin L ({y} : Set F)) g := by
    set s : Set F := Set.range (algebraMap L F) ∪ {y} with hsdef
    have hmem : g ∈ (integralClosure (Subring.closure s) F).toSubring := by
      rw [← iInf_valuationSubring_superset]
      simp only [Subring.mem_iInf]
      rintro ⟨V, hsV⟩
      have hLV : ∀ a : L, algebraMap L F a ∈ V := fun a => hsV (Or.inl ⟨a, rfl⟩)
      have hyV : y ∈ V := hsV (Or.inr rfl)
      by_cases hxV : x ∈ V
      · have hLxV : (Algebra.adjoin L ({x} : Set F) : Set F) ⊆ (V : Set F) := by
          show ((Algebra.adjoin L ({x} : Set F)).toSubring : Set F) ⊆ (V : Set F)
          rw [← (Algebra.adjoin_eq_ring_closure ({x} : Set F)).symm]
          exact Subring.closure_le.mpr (Set.union_subset
            (Set.range_subset_iff.mpr hLV) (Set.singleton_subset_iff.mpr hxV))
        have hfV : f ∈ V := hfallV V hLxV
        have hxmV : (x ^ m)⁻¹ ∈ V := by
          rw [← inv_pow, ← hy]; exact pow_mem hyV m
        exact mul_mem hfV hxmV
      · exact h₂ V hLV hxV
    have hcls : Subring.closure s = (Algebra.adjoin L ({y} : Set F)).toSubring :=
      (Algebra.adjoin_eq_ring_closure _).symm
    refine (hmem : IsIntegral (Subring.closure s) g).map_of_comp_eq
      (Subring.inclusion hcls.le) (RingHom.id F) ?_
    ext a; exact (Subring.coe_inclusion hcls.le a).symm

  have hxK : x ∈ IntermediateField.adjoin L ({y} : Set F) := by
    rw [show x = y⁻¹ from (inv_inv x).symm ▸ congrArg Inv.inv hy.symm]
    exact inv_mem (IntermediateField.mem_adjoin_simple_self L y)
  have hyKx : y ∈ IntermediateField.adjoin L ({x} : Set F) := by
    rw [hy]; exact inv_mem (IntermediateField.mem_adjoin_simple_self L x)
  have hKeq : IntermediateField.adjoin L ({x} : Set F) = IntermediateField.adjoin L ({y} : Set F) :=
    le_antisymm
      (IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hxK))
      (IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hyKx))

  have hmpgLy : ∀ i, ((minpoly (IntermediateField.adjoin L ({y} : Set F)) g).coeff i : F) ∈
      Algebra.adjoin L ({y} : Set F) := by
    intro i
    have heq := minpoly.isIntegrallyClosed_eq_field_fractions'
      (R := Algebra.adjoin L ({y} : Set F)) (IntermediateField.adjoin L ({y} : Set F)) hgint
    rw [heq, Polynomial.coeff_map]
    exact ((minpoly (Algebra.adjoin L ({y} : Set F)) g).coeff i).2

  have hmpfq : minpoly (IntermediateField.adjoin L ({x} : Set F)) f =
      q.map (algebraMap (Algebra.adjoin L ({x} : Set F))
        (IntermediateField.adjoin L ({x} : Set F))) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' _ hint
  have hmpfd : (minpoly (IntermediateField.adjoin L ({x} : Set F)) f).natDegree = d := by
    rw [hmpfq, (minpoly.monic hint).natDegree_map, hd]

  have hxKmem : x ∈ IntermediateField.adjoin L ({x} : Set F) :=
    IntermediateField.mem_adjoin_simple_self L x
  set xK : IntermediateField.adjoin L ({x} : Set F) := ⟨x, hxKmem⟩ with hxK
  have hxK0 : xK ≠ 0 := fun h => hx0 (congrArg Subtype.val h)

  have hgsmul : g = (xK ^ m)⁻¹ • f := by
    rw [hg, Algebra.smul_def, map_inv₀, map_pow, mul_comm]
    rfl

  have hfintK : IsIntegral (IntermediateField.adjoin L ({x} : Set F)) f := hint.tower_top

  have hmpg_scale : minpoly (IntermediateField.adjoin L ({x} : Set F)) g =
      (minpoly (IntermediateField.adjoin L ({x} : Set F)) f).scaleRoots ((xK ^ m)⁻¹) := by
    rw [hgsmul]
    exact IsIntegrallyClosed.minpoly_smul (inv_ne_zero (pow_ne_zero m hxK0)) hfintK

  have hcoefj : (minpoly (IntermediateField.adjoin L ({x} : Set F)) g).coeff j =
      (minpoly (IntermediateField.adjoin L ({x} : Set F)) f).coeff j * ((xK ^ m)⁻¹) ^ (d - j) := by
    rw [hmpg_scale, Polynomial.coeff_scaleRoots, hmpfd]

  have hcoefF : ((minpoly (IntermediateField.adjoin L ({x} : Set F)) g).coeff j : F) =
      ((q.coeff j : Algebra.adjoin L ({x} : Set F)) : F) * (x ^ n)⁻¹ := by
    have hcast1 : ((minpoly (IntermediateField.adjoin L ({x} : Set F)) f).coeff j : F) =
        ((q.coeff j : Algebra.adjoin L ({x} : Set F)) : F) := by
      rw [hmpfq, Polynomial.coeff_map]; rfl
    have hcast2 : (((xK ^ m)⁻¹ ^ (d - j) :
        IntermediateField.adjoin L ({x} : Set F)) : F) = (x ^ n)⁻¹ := by
      push_cast
      rw [show ((xK : IntermediateField.adjoin L ({x} : Set F)) : F) = x from rfl,
        ← inv_pow, ← pow_mul, hn, mul_comm m (d - j), inv_pow]
    calc ((minpoly (IntermediateField.adjoin L ({x} : Set F)) g).coeff j : F)
        = ((minpoly (IntermediateField.adjoin L ({x} : Set F)) f).coeff j : F) *
            (((xK ^ m)⁻¹ ^ (d - j) : IntermediateField.adjoin L ({x} : Set F)) : F) := by
          rw [hcoefj]; push_cast; ring
      _ = ((q.coeff j : Algebra.adjoin L ({x} : Set F)) : F) * (x ^ n)⁻¹ := by
          rw [hcast1, hcast2]

  have hkey : ((q.coeff j : Algebra.adjoin L ({x} : Set F)) : F) * (x ^ n)⁻¹ ∈
      Algebra.adjoin L ({y} : Set F) := by
    rw [← hcoefF, hKeq]
    exact hmpgLy j

  rw [← hc] at hkey
  have hy2 : ({x⁻¹} : Set F) = {y} := by rw [hy]
  rw [← hy2] at hkey
  exact Polynomial.natDegree_le_of_aeval_mul_inv_pow_mem_adjoin_inv x hxL hx0 c n hkey

end Polynomial
