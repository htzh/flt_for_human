/-
The Riemann–Roch space of the Weierstrass coordinate ring and the degree of the
infinite place.

`CoordinateRing.RRSpace W n` is the image of the `F`-linear map sending a pair of
polynomials `(p, q)` with `deg p < n/2 + 1`, `deg q < (n-1)/2` to
`p • 1 + q • Y`; `mem_RRSpace_iff_degree_norm_le` identifies it with the elements
whose norm has degree at most `n`, and `RRSpace.finrank_eq` computes its
dimension as `n`.  The second block proves that two non-finite places of the
function field coincide, that such a place has degree one, that one exists, and
packages them into the `InfinitePlace` instance.

Transcribed verbatim from the pinned FLT `aa2d8b3`,
`P2M/Sol/S_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_and_abelTheorem.lean`
(lines 239–436 and 1511–1784; `exists_equation` at line 1700 is already ported in
`Place/Dictionary.lean` and is not rewritten).  Only proof bodies are adapted to
mathlib `v4.34.0`; declaration names, namespaces and kinds are kept.  The RR
basis work uses mathlib's affine-Point basis family (`smul_basis_eq_zero`,
`exists_smul_basis_eq`, `smul_basis_mul_Y`, `degree_norm_smul_basis`) rather than
the pin's private copy of it.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_and_abelTheorem.lean#L239-L436>
-/
import FLTForHuman.WeierstrassCurve.Place.Dictionary
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Basis.Basic

set_option autoImplicit false
-- The pin's `haveI` instance walls are transcribed literally.
set_option linter.style.haveILetI false

noncomputable section

open AlgebraicCurve WeierstrassCurve WeierstrassCurve.Affine
open Polynomial Module
open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine.CoordinateRing

universe u

variable {F : Type u} [Field F] {W : Affine F}

private lemma two_nsmul_le_coe_iff {d : WithBot ℕ} {n : ℕ} :
    2 • d ≤ (n : WithBot ℕ) ↔ d < ((n / 2 + 1 : ℕ) : WithBot ℕ) := by
  induction d using WithBot.recBotCoe with
  | bot => exact iff_of_true (by simp) (WithBot.bot_lt_coe _)
  | coe k =>
    show 2 • ((k : ℕ) : WithBot ℕ) ≤ (n : WithBot ℕ) ↔
      ((k : ℕ) : WithBot ℕ) < ((n / 2 + 1 : ℕ) : WithBot ℕ)
    rw [two_nsmul, ← Nat.cast_add]
    exact_mod_cast (by omega : k + k ≤ n ↔ k < n / 2 + 1)

private lemma two_nsmul_add_three_le_coe_iff {d : WithBot ℕ} {n : ℕ} :
    2 • d + 3 ≤ (n : WithBot ℕ) ↔ d < (((n - 1) / 2 : ℕ) : WithBot ℕ) := by
  induction d using WithBot.recBotCoe with
  | bot => exact iff_of_true (by simp) (WithBot.bot_lt_coe _)
  | coe k =>
    show 2 • ((k : ℕ) : WithBot ℕ) + 3 ≤ (n : WithBot ℕ) ↔
      ((k : ℕ) : WithBot ℕ) < (((n - 1) / 2 : ℕ) : WithBot ℕ)
    rw [two_nsmul, ← Nat.cast_add, show (3 : WithBot ℕ) = ((3 : ℕ) : WithBot ℕ) by norm_cast,
      ← Nat.cast_add]
    exact_mod_cast (by omega : k + k + 3 ≤ n ↔ k < (n - 1) / 2)

private lemma xCount_add_yCount (n : ℕ) (hn : 1 ≤ n) : n / 2 + 1 + (n - 1) / 2 = n := by
  omega

variable (W) in

noncomputable def rrParam (n : ℕ) :
    (degreeLT F (n / 2 + 1) × degreeLT F ((n - 1) / 2)) →ₗ[F] W.CoordinateRing :=
  LinearMap.coprod
    (((LinearMap.toSpanSingleton F[X] W.CoordinateRing 1).restrictScalars F).comp
      (Submodule.subtype _))
    (((LinearMap.toSpanSingleton F[X] W.CoordinateRing (mk W Y)).restrictScalars F).comp
      (Submodule.subtype _))

@[scoped simp] lemma rrParam_apply (n : ℕ)
    (pq : degreeLT F (n / 2 + 1) × degreeLT F ((n - 1) / 2)) :
    rrParam W n pq = (pq.1 : F[X]) • (1 : W.CoordinateRing) + (pq.2 : F[X]) • mk W Y :=
  rfl

lemma rrParam_injective (n : ℕ) : Function.Injective (rrParam W n) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨p, q⟩ h
  rw [rrParam_apply] at h
  obtain ⟨hp, hq⟩ := smul_basis_eq_zero h
  exact Prod.ext (Subtype.ext hp) (Subtype.ext hq)

variable (W) in

noncomputable def RRSpace (n : ℕ) : Submodule F W.CoordinateRing :=
  LinearMap.range (rrParam W n)

lemma mem_RRSpace_iff {f : W.CoordinateRing} {n : ℕ} :
    f ∈ RRSpace W n ↔ ∃ p q : F[X], p.degree < ((n / 2 + 1 : ℕ) : WithBot ℕ) ∧
      q.degree < (((n - 1) / 2 : ℕ) : WithBot ℕ) ∧
      p • (1 : W.CoordinateRing) + q • mk W Y = f := by
  constructor
  · rintro ⟨⟨p, q⟩, rfl⟩
    exact ⟨p, q, mem_degreeLT.mp p.2, mem_degreeLT.mp q.2, rfl⟩
  · rintro ⟨p, q, hp, hq, rfl⟩
    exact ⟨⟨⟨p, mem_degreeLT.mpr hp⟩, ⟨q, mem_degreeLT.mpr hq⟩⟩, rfl⟩

lemma smul_basis_mem_RRSpace_iff {p q : F[X]} {n : ℕ} :
    p • (1 : W.CoordinateRing) + q • mk W Y ∈ RRSpace W n ↔
      p.degree < ((n / 2 + 1 : ℕ) : WithBot ℕ) ∧
        q.degree < (((n - 1) / 2 : ℕ) : WithBot ℕ) := by
  refine ⟨fun h => ?_, fun ⟨hp, hq⟩ => mem_RRSpace_iff.mpr ⟨p, q, hp, hq, rfl⟩⟩
  obtain ⟨p', q', hp', hq', hf⟩ := mem_RRSpace_iff.mp h
  have h0 : (p' - p) • (1 : W.CoordinateRing) + (q' - q) • mk W Y = 0 := by
    rw [sub_smul, sub_smul, ← sub_eq_zero.mpr hf]
    abel
  obtain ⟨hp0, hq0⟩ := smul_basis_eq_zero h0
  rw [sub_eq_zero] at hp0 hq0
  exact ⟨hp0 ▸ hp', hq0 ▸ hq'⟩

theorem mem_RRSpace_iff_degree_norm_le {f : W.CoordinateRing} {n : ℕ} :
    f ∈ RRSpace W n ↔ (Algebra.norm F[X] f).degree ≤ (n : WithBot ℕ) := by
  obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq f
  rw [smul_basis_mem_RRSpace_iff, degree_norm_smul_basis, max_le_iff,
    two_nsmul_le_coe_iff, two_nsmul_add_three_le_coe_iff]

lemma RRSpace_mono {m n : ℕ} (h : m ≤ n) : RRSpace W m ≤ RRSpace W n := fun _ hf =>
  mem_RRSpace_iff_degree_norm_le.mpr <|
    (mem_RRSpace_iff_degree_norm_le.mp hf).trans <| by exact_mod_cast h

lemma one_mem_RRSpace (n : ℕ) : (1 : W.CoordinateRing) ∈ RRSpace W n :=
  mem_RRSpace_iff.mpr ⟨1, 0,
    by rw [degree_one]; exact_mod_cast (by omega : (0 : ℕ) < n / 2 + 1),
    by rw [degree_zero]; exact WithBot.bot_lt_coe _,
    by rw [one_smul, zero_smul, add_zero]⟩

lemma algebraMap_mem_RRSpace (a : F) (n : ℕ) :
    algebraMap F W.CoordinateRing a ∈ RRSpace W n := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem _ a (one_mem_RRSpace n)

lemma one_le_RRSpace (n : ℕ) : (1 : Submodule F W.CoordinateRing) ≤ RRSpace W n := by
  intro f hf
  obtain ⟨a, rfl⟩ := Submodule.mem_one.mp hf
  exact algebraMap_mem_RRSpace a n

namespace RRSpace

variable (W) in

noncomputable def basisAux (n : ℕ) :
    Basis (Fin (n / 2 + 1 + (n - 1) / 2)) F (RRSpace W n) :=
  (degreeLT.basisProd F (n / 2 + 1) ((n - 1) / 2)).map
    (LinearEquiv.ofInjective (rrParam W n) (rrParam_injective n))

theorem finrank_eq (n : ℕ) (hn : 1 ≤ n) : finrank F (RRSpace W n) = n := by
  rw [finrank_eq_card_basis (basisAux W n), Fintype.card_fin]
  exact xCount_add_yCount n hn

variable (W) in

noncomputable def finBasis (n : ℕ) (hn : 1 ≤ n) : Basis (Fin n) F (RRSpace W n) :=
  (basisAux W n).reindex (finCongr (xCount_add_yCount n hn))

end RRSpace

theorem RRSpace_zero : RRSpace W 0 = (1 : Submodule F W.CoordinateRing) := by
  refine le_antisymm ?_ (one_le_RRSpace 0)
  rintro f hf
  obtain ⟨p, q, hp, hq, rfl⟩ := mem_RRSpace_iff.mp hf

  have hq0 : q = 0 := by
    rw [← degree_eq_bot]
    simpa using hq
  have hp0 : p = C (p.coeff 0) := by
    refine degree_le_zero_iff.mp (Nat.WithBot.lt_one_iff_le_zero.mp ?_)
    simpa using hp
  rw [hq0, zero_smul, add_zero, hp0, smul, mul_one, ← algebraMap_eq_mk_C_C]
  exact Submodule.mem_one.mpr ⟨p.coeff 0, rfl⟩

end WeierstrassCurve.Affine.CoordinateRing

namespace WeierstrassCurve.Affine

universe u

variable {F : Type*} [Field F] {W : Affine F}
variable (v : AlgebraicCurve.Place F W.FunctionField)

theorem mem_iff_natDegree_norm_le (hv : ¬ IsFinitePlace v) {a b : W.CoordinateRing}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    algebraMap W.CoordinateRing W.FunctionField a
        / algebraMap W.CoordinateRing W.FunctionField b ∈ v.toValuationSubring
      ↔ (Algebra.norm F[X] a).natDegree ≤ (Algebra.norm F[X] b).natDegree := by
  have hA : v.ord (polyToFunctionField W X) < 0 := ord_X_neg_of_not_isFinitePlace v hv
  have ha' : algebraMap W.CoordinateRing W.FunctionField a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective W.CoordinateRing W.FunctionField)).mpr ha
  have hb' : algebraMap W.CoordinateRing W.FunctionField b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective W.CoordinateRing W.FunctionField)).mpr hb
  have hdiv : algebraMap W.CoordinateRing W.FunctionField a
      / algebraMap W.CoordinateRing W.FunctionField b ≠ 0 := div_ne_zero ha' hb'
  rw [v.mem_iff_ord_nonneg hdiv, div_eq_mul_inv, v.ord_mul ha' (inv_ne_zero hb'), v.ord_inv]
  have h1 := two_mul_ord_eq_of_not_isFinitePlace v hv ha
  have h2 := two_mul_ord_eq_of_not_isFinitePlace v hv hb
  constructor
  · intro h
    nlinarith
  · intro h
    have h3 : ((Algebra.norm F[X] a).natDegree : ℤ) ≤ ((Algebra.norm F[X] b).natDegree : ℤ) := by
      exact_mod_cast h
    nlinarith

theorem eq_of_not_isFinitePlace_of_not_isFinitePlace
    {v w : AlgebraicCurve.Place F W.FunctionField}
    (hv : ¬ IsFinitePlace v) (hw : ¬ IsFinitePlace w) : v = w := by
  refine AlgebraicCurve.Place.ext ?_
  ext z
  rcases eq_or_ne z 0 with rfl | hz
  · simp [v.toValuationSubring.zero_mem, w.toValuationSubring.zero_mem]
  obtain ⟨a, b, hb, hzab⟩ := IsFractionRing.div_surjective (A := W.CoordinateRing) z
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, _root_.map_zero, zero_div] at hzab
    exact hz hzab.symm
  rw [← hzab]
  rw [mem_iff_natDegree_norm_le v hv ha0 hb0, mem_iff_natDegree_norm_le w hw ha0 hb0]

theorem exists_smul_sub_natDegree_norm_lt {a b : W.CoordinateRing} (hb : b ≠ 0)
    (hab : (Algebra.norm F[X] a).natDegree ≤ (Algebra.norm F[X] b).natDegree) :
    ∃ c : F, a - c • b = 0 ∨
      (Algebra.norm F[X] (a - c • b)).natDegree < (Algebra.norm F[X] b).natDegree := by
  set n := (Algebra.norm F[X] b).natDegree with hndef

  have hbn : b ∈ CoordinateRing.RRSpace W n :=
    CoordinateRing.mem_RRSpace_iff_degree_norm_le.mpr
      (Polynomial.natDegree_le_iff_degree_le.mp le_rfl)
  have han : a ∈ CoordinateRing.RRSpace W n :=
    CoordinateRing.mem_RRSpace_iff_degree_norm_le.mpr
      (Polynomial.natDegree_le_iff_degree_le.mp hab)

  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · rw [hn0] at hbn han
    rw [CoordinateRing.RRSpace_zero] at hbn han
    obtain ⟨α, hα⟩ := Submodule.mem_one.mp han
    obtain ⟨β, hβ⟩ := Submodule.mem_one.mp hbn
    have hβ0 : β ≠ 0 := by
      rintro rfl
      rw [_root_.map_zero] at hβ
      exact hb hβ.symm
    refine ⟨α / β, Or.inl ?_⟩
    rw [← hα, ← hβ, Algebra.smul_def, ← map_mul, div_mul_cancel₀ _ hβ0, sub_self]

  rcases eq_or_ne n 1 with hn1 | hn1
  · exact absurd (hndef.symm.trans hn1) (CoordinateRing.natDegree_norm_ne_one b)

  have hn2 : 2 ≤ n := by omega
  have hn1' : 1 ≤ n - 1 := by omega
  haveI : FiniteDimensional F (CoordinateRing.RRSpace W n) :=
    Module.Finite.of_basis (CoordinateRing.RRSpace.finBasis W n (by omega))

  have hbnot : b ∉ CoordinateRing.RRSpace W (n - 1) := by
    intro hcon
    rw [CoordinateRing.mem_RRSpace_iff_degree_norm_le, ← Polynomial.natDegree_le_iff_degree_le]
      at hcon
    omega

  have hsup : CoordinateRing.RRSpace W (n - 1) ⊔ Submodule.span F {b}
      = CoordinateRing.RRSpace W n := by
    have hle : CoordinateRing.RRSpace W (n - 1) ⊔ Submodule.span F {b}
        ≤ CoordinateRing.RRSpace W n := by
      refine sup_le (CoordinateRing.RRSpace_mono (by omega)) ?_
      rw [Submodule.span_le, Set.singleton_subset_iff]
      exact hbn
    refine Submodule.eq_of_le_of_finrank_le hle ?_
    have hlt : CoordinateRing.RRSpace W (n - 1) < CoordinateRing.RRSpace W (n - 1)
        ⊔ Submodule.span F {b} := by
      refine lt_of_le_of_ne le_sup_left ?_
      intro hcon
      refine hbnot ?_
      rw [hcon]
      exact (le_sup_right (a := CoordinateRing.RRSpace W (n - 1)))
        (Submodule.mem_span_singleton_self b)
    haveI : FiniteDimensional F (CoordinateRing.RRSpace W (n - 1)
        ⊔ Submodule.span F {b} : Submodule F _) :=
      Submodule.finiteDimensional_of_le hle
    have h1 := Submodule.finrank_lt_finrank_of_lt hlt
    rw [CoordinateRing.RRSpace.finrank_eq (n - 1) hn1'] at h1
    rw [CoordinateRing.RRSpace.finrank_eq n (by omega)]
    omega

  obtain ⟨ℓ, hℓ, z, hz, hsum⟩ := Submodule.mem_sup.mp (hsup ▸ han)
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
  refine ⟨c, ?_⟩
  have hldef : a - c • b = ℓ := by rw [← hsum]; ring
  rcases eq_or_ne (a - c • b) 0 with h | h
  · exact Or.inl h
  · refine Or.inr ?_
    have hc : (Algebra.norm F[X] (a - c • b)).natDegree ≤ n - 1 := by
      rw [Polynomial.natDegree_le_iff_degree_le, ← CoordinateRing.mem_RRSpace_iff_degree_norm_le]
      exact hldef ▸ hℓ
    omega

theorem deg_eq_one_of_not_isFinitePlace (hv : ¬ IsFinitePlace v) : v.deg = 1 := by
  have hA : v.ord (polyToFunctionField W X) < 0 := ord_X_neg_of_not_isFinitePlace v hv
  refine AlgebraicCurve.Place.deg_eq_one_of_surjective v ?_
  intro z
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective z

  rcases eq_or_ne (g : W.FunctionField) 0 with hg0 | hg0
  · refine ⟨0, ?_⟩
    have hgz : g = 0 := Subtype.ext hg0
    subst hgz
    exact (_root_.map_zero _).trans (_root_.map_zero _).symm
  obtain ⟨a, b, hb, hzab⟩ := IsFractionRing.div_surjective (A := W.CoordinateRing)
    (g : W.FunctionField)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbL0 : algebraMap W.CoordinateRing W.FunctionField b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective W.CoordinateRing W.FunctionField)).mpr hb0
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, _root_.map_zero, zero_div] at hzab
    exact hg0 hzab.symm
  have hmem : (g : W.FunctionField) ∈ v.toValuationSubring := g.2
  rw [← hzab] at hmem
  have hab := (mem_iff_natDegree_norm_le v hv ha0 hb0).mp hmem

  obtain ⟨c, hc⟩ := exists_smul_sub_natDegree_norm_lt (W := W) hb0 hab
  refine ⟨c, ?_⟩

  rw [IsScalarTower.algebraMap_apply F v.toValuationSubring v.ResidueField,
    IsLocalRing.ResidueField.algebraMap_eq]
  refine (Ideal.Quotient.eq (I := IsLocalRing.maximalIdeal v.toValuationSubring)).mpr ?_
  have hcoe : ((algebraMap F v.toValuationSubring c : v.toValuationSubring) : W.FunctionField)
      = algebraMap F W.FunctionField c := v.coe_algebraMap c

  have hdiff : ((algebraMap F v.toValuationSubring c - g : v.toValuationSubring)
      : W.FunctionField) = algebraMap W.CoordinateRing W.FunctionField (c • b - a)
        / algebraMap W.CoordinateRing W.FunctionField b := by
    have h0 : ((algebraMap F v.toValuationSubring c - g : v.toValuationSubring)
        : W.FunctionField) = algebraMap F W.FunctionField c
          - algebraMap W.CoordinateRing W.FunctionField a
            / algebraMap W.CoordinateRing W.FunctionField b := by
      push_cast
      rw [hcoe, hzab]
    rw [h0, map_sub, eq_div_iff hbL0, sub_mul, div_mul_cancel₀ _ hbL0, Algebra.smul_def,
      map_mul, ← IsScalarTower.algebraMap_apply F W.CoordinateRing W.FunctionField]

  rcases eq_or_ne (a - c • b) 0 with hzero | hzero
  ·
    have h1 : c • b - a = 0 := by rw [← neg_sub a (c • b), hzero, _root_.neg_zero]
    have h2 : (algebraMap F v.toValuationSubring c - g : v.toValuationSubring)
        = (0 : v.toValuationSubring) := by
      ext
      rw [hdiff, h1, _root_.map_zero, zero_div]
      rfl
    rw [h2]
    exact (IsLocalRing.maximalIdeal v.toValuationSubring).zero_mem
  ·
    replace hc : (Algebra.norm F[X] (a - c • b)).natDegree
        < (Algebra.norm F[X] b).natDegree := hc.resolve_left hzero
    have hsub0 : c • b - a ≠ 0 := fun h =>
      hzero (by rw [show a - c • b = -(c • b - a) by ring, h, _root_.neg_zero])

    have hordswap : v.ord (algebraMap W.CoordinateRing W.FunctionField (c • b - a))
        = v.ord (algebraMap W.CoordinateRing W.FunctionField (a - c • b)) := by
      rw [show c • b - a = -(a - c • b) by ring, _root_.map_neg, v.ord_neg]
    have hordpos : 0 < v.ord (((algebraMap F v.toValuationSubring c - g
        : v.toValuationSubring)) : W.FunctionField) := by
      rw [hdiff, div_eq_mul_inv, v.ord_mul ((map_ne_zero_iff _
        (IsFractionRing.injective W.CoordinateRing W.FunctionField)).mpr hsub0)
        (inv_ne_zero hbL0), v.ord_inv, hordswap]
      have h1 := two_mul_ord_eq_of_not_isFinitePlace v hv hzero
      have h2 := two_mul_ord_eq_of_not_isFinitePlace v hv hb0
      have h3 : ((Algebra.norm F[X] (a - c • b)).natDegree : ℤ)
          < ((Algebra.norm F[X] b).natDegree : ℤ) := by exact_mod_cast hc
      nlinarith
    rcases eq_or_ne ((algebraMap F v.toValuationSubring c - g : v.toValuationSubring))
        (0 : v.toValuationSubring) with hzero' | hzero'
    · rw [hzero']
      exact (IsLocalRing.maximalIdeal v.toValuationSubring).zero_mem
    · have hzero'' : ((algebraMap F v.toValuationSubring c - g : v.toValuationSubring)
          : W.FunctionField) ≠ 0 := fun h => hzero' (Subtype.ext h)
      exact (v.mem_maximalIdeal_iff_ord_pos hzero''
        (algebraMap F v.toValuationSubring c - g).2).mpr hordpos

theorem exists_not_isFinitePlace [IsAlgClosed F] [IsDedekindDomain W.CoordinateRing]
    [AlgebraicCurve.HasPrincipalDivisors F W.FunctionField] :
    ∃ v : AlgebraicCurve.Place F W.FunctionField, ¬ IsFinitePlace v := by
  by_contra hcon
  push Not at hcon

  obtain ⟨y₀, hy₀⟩ := exists_equation W 0
  set v₀ : AlgebraicCurve.Place F W.FunctionField := placeOfEquation hy₀ with hv₀def

  set r : W.CoordinateRing := CoordinateRing.mk W (C X) with hrdef
  have hr0 : r ≠ 0 := by
    rw [hrdef]
    have h1 := CoordinateRing.XClass_ne_zero (W' := W) (0 : F)
    rw [CoordinateRing.XClass] at h1
    simpa using h1
  have hrL0 : algebraMap W.CoordinateRing W.FunctionField r ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective W.CoordinateRing W.FunctionField)).mpr hr0

  have hrmem : r ∈ (CoordinateRing.heightOneSpectrumOfEquation hy₀).asIdeal := by
    rw [CoordinateRing.heightOneSpectrumOfEquation_asIdeal]
    have h1 : CoordinateRing.XClass W (0 : F) ∈ CoordinateRing.XYIdeal W (0 : F) (C y₀) :=
      Ideal.subset_span (Set.mem_insert _ _)
    have h2 : CoordinateRing.XClass W (0 : F) = r := by
      rw [CoordinateRing.XClass, hrdef]
      norm_num
    exact h2 ▸ h1

  have hordpos : 0 < v₀.ord (algebraMap W.CoordinateRing W.FunctionField r) := by
    have h1 : v₀.ord (algebraMap W.CoordinateRing W.FunctionField r) ≠ 0 :=
      (AlgebraicCurve.Place.ord_ofHeightOneSpectrum_ne_zero_iff
        (CoordinateRing.heightOneSpectrumOfEquation hy₀) hr0).mpr hrmem
    have h2 : 0 ≤ v₀.ord (algebraMap W.CoordinateRing W.FunctionField r) :=
      v₀.ord_nonneg_of_mem (isFinitePlace_placeOfEquation hy₀ r)
    omega

  obtain ⟨D, hD, hDdeg⟩ := AlgebraicCurve.HasPrincipalDivisors.exists_divisor
    (K := F) (algebraMap W.CoordinateRing W.FunctionField r) hrL0

  have hDnonneg : ∀ w : AlgebraicCurve.Place F W.FunctionField, 0 ≤ D w := by
    intro w
    rw [hD w]
    exact w.ord_nonneg_of_mem (hcon w r)

  have hDpos : 0 < AlgebraicCurve.Divisor.degree D := by
    have hsum : AlgebraicCurve.Divisor.degree D = ∑ w ∈ D.support, D w * (w.deg : ℤ) := by
      simp only [AlgebraicCurve.Divisor.degree, Finsupp.liftAddHom_apply,
        AddMonoidHom.mulRight_apply, Finsupp.sum]
    rw [hsum]
    refine Finset.sum_pos' (fun w _ => mul_nonneg (hDnonneg w) (Int.natCast_nonneg _)) ?_
    refine ⟨v₀, ?_, ?_⟩
    · rw [Finsupp.mem_support_iff, hD v₀]
      omega
    · rw [hD v₀, deg_placeOfEquation hy₀]
      omega
  omega

variable (W) in

scoped instance instInfinitePlace [IsAlgClosed F] [IsDedekindDomain W.CoordinateRing]
    [AlgebraicCurve.HasPrincipalDivisors F W.FunctionField] : InfinitePlace W where
  place := (exists_not_isFinitePlace (W := W)).choose
  not_isFinitePlace := (exists_not_isFinitePlace (W := W)).choose_spec
  deg_eq_one := deg_eq_one_of_not_isFinitePlace _ (exists_not_isFinitePlace (W := W)).choose_spec
  eq_of_not_isFinitePlace _v hv :=
    eq_of_not_isFinitePlace_of_not_isFinitePlace hv
      (exists_not_isFinitePlace (W := W)).choose_spec

end WeierstrassCurve.Affine

end
