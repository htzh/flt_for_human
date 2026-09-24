/-
  m4 — the shared `Γ₀`-invariant core (M8's 651-content-line prelude), written once.

  The three pinned M8 files

  * `S_ModularCurve_mem_modularFunctionField_of_hasSum_of_gamma0_invariant`      (870 raw)
  * `S_ModularCurve_isIntegral_adjoin_jq_of_hasSum_of_gamma0_invariant`          (870 raw)
  * `S_ModularCurve_coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant`   (1155 raw)

  share the block at pin lines 50–861 / 50–861 / 53–863. The first two differ by
  12 lines (all `p2m_*` strings plus the final `solution`); the third's prelude
  differs from the first's by 2 lines. The port writes that block once, here,
  and the three headlines become short applications.

  The pin's `RealL` predicate and most of its closure are **imported** from
  `ModularForms/Hauptmodul.lean` (the level-one effort promoted them for exactly
  this reuse); only the three missing lemmas `RealL.sum`,
  `RealL.interpPoly_coeff`, `RealL.conjPoly_coeff` are written here, since
  `Hauptmodul.lean` is off-limits and does not carry them.

  FLT provenance, pinned `aa2d8b3` (the shared prelude is byte-identical in the
  first two files; the third differs by 2 lines):
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_mem_modularFunctionField_of_hasSum_of_gamma0_invariant.lean
-/
import FLTForHuman.ModularCurve.Defs.QAdicPlace
import FLTForHuman.ModularCurve.Defs.AtkinLehner
import FLTForHuman.ModularCurve.Defs.TS
import FLTForHuman.ModularCurve.Defs.Twist
import FLTForHuman.ModularCurve.Defs.PhiGen
import FLTForHuman.ModularCurve.PhiGenDescent
import FLTForHuman.ModularCurve.ModularPolynomialIrreducible
import FLTForHuman.ModularCurve.Analytic.QParamUnique
import FLTForHuman.ModularCurve.Analytic.Gamma0Cosets
import FLTForHuman.ModularForms.JqAnalyticModel
import FLTForHuman.ModularForms.Hauptmodul
import FLTForHuman.ModularForms.HeckeQExpansion
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic

set_option autoImplicit false

noncomputable section

open UpperHalfPlane Complex Filter Topology Function Polynomial
open scoped MatrixGroups

local notation "𝕢" => Function.Periodic.qParam

namespace ModularCurve

/-! ### Locally-restated `ΦGen`-descent helpers

`PhiGenDescent.lean` keeps the four helpers the pin's `ΦGen` descent exposes
(`mem_range_qExpand_of_qTwist_eq`, `mem_range_coeffEmb_of_forall_coeffMap_eq`,
`exists_galoisPerm`, `mem_range_coeffEmb_qExpand_of_mem_inter`) `private`, so
they are unreachable from here and the workspace rule forbids editing that
module. They (and the `qContract`/support-collapse machinery they need) are
restated `private` below, verbatim from
`FLTForHuman/ModularCurve/PhiGenDescent.lean`. -/

section CoreHelpers

private theorem coeff_eq_zero_of_qTwist_eq {K : Type*} [Field K] {ℓ : ℕ} {ζ : Kˣ}
    (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    {f : LaurentSeries K} (hf : qTwist ζ f = f) {m : ℤ} (hm : ¬ (ℓ : ℤ) ∣ m) :
    f.coeff m = 0 := by
  have h := congrArg (fun g => HahnSeries.coeff g m) hf
  simp only [qTwist_coeff] at h
  by_contra hc
  apply hm
  rw [← hζ.zpow_eq_one_iff_dvd]
  have hunit : ((ζ ^ m : Kˣ) : K) = (ζ : K) ^ m := Units.val_zpow_eq_zpow_val ζ m
  have hzero : (((ζ ^ m : Kˣ) : K) - 1) * f.coeff m = 0 := by
    rw [sub_mul, one_mul, h, sub_self]
  rcases mul_eq_zero.mp hzero with h1 | h1
  · rw [hunit] at h1
    linear_combination h1
  · exact absurd h1 hc

private def qContract {K : Type*} [Field K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)]
    (f : LaurentSeries K) : LaurentSeries K where
  coeff m := f.coeff ((ℓ : ℤ) * m)
  isPWO_support' := by
    have hsub : (Function.support fun m : ℤ => f.coeff ((ℓ : ℤ) * m)) ⊆
        (fun k : ℤ => k / (ℓ : ℤ)) '' f.support := by
      intro m hm
      refine ⟨(ℓ : ℤ) * m, hm, ?_⟩
      exact Int.mul_ediv_cancel_left m (Nat.cast_ne_zero.mpr hℓ.out.ne_zero)
    exact (f.isPWO_support'.image_of_monotone fun a b hab =>
      Int.ediv_le_ediv (Int.natCast_pos.mpr hℓ.out.pos) hab).mono hsub

private theorem qContract_coeff {K : Type*} [Field K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)]
    (f : LaurentSeries K) (m : ℤ) :
    (qContract ℓ f).coeff m = f.coeff ((ℓ : ℤ) * m) := rfl

private theorem qExpand_qContract {K : Type*} [Field K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)]
    {f : LaurentSeries K}
    (hf : ∀ m : ℤ, ¬ (ℓ : ℤ) ∣ m → f.coeff m = 0) :
    qExpand K ℓ (qContract ℓ f) = f := by
  ext k
  by_cases hk : (ℓ : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [qExpand_coeff_mul, qContract_coeff]
  · rw [qExpand_coeff_of_not_dvd ℓ _ hk, hf k hk]

private theorem mem_range_qExpand_of_qTwist_eq {K : Type*} [Field K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ) (f : LaurentSeries K) (hf : qTwist ζ f = f) :
    f ∈ Set.range (qExpand K ℓ) :=
  ⟨qContract ℓ f, qExpand_qContract fun _ hm => coeff_eq_zero_of_qTwist_eq hζ hf hm⟩

private theorem mem_range_coeffEmb_of_forall_coeffMap_eq {K : Type*} [Field K] [Algebra ℚ K]
    (hfix : ∀ c : K, (∀ σ : K ≃ₐ[ℚ] K, σ c = c) → ∃ r : ℚ, algebraMap ℚ K r = c)
    {f : LaurentSeries K} (hf : ∀ σ : K ≃ₐ[ℚ] K, coeffMap (σ : K →+* K) f = f) :
    f ∈ Set.range (coeffEmb K) := by
  have hcoeff : ∀ m : ℤ, ∃ r : ℚ, algebraMap ℚ K r = f.coeff m := fun m =>
    hfix (f.coeff m) fun σ => by
      have hcongr := congrArg (fun g => HahnSeries.coeff g m) (hf σ)
      simpa using hcongr
  choose r hr using hcoeff
  refine ⟨⟨r, ?_⟩, ?_⟩
  · refine f.isPWO_support'.mono fun m hm => ?_
    simp only [Function.mem_support] at hm ⊢
    intro h
    exact hm (FaithfulSMul.algebraMap_injective ℚ K (by rw [hr m, h, map_zero]))
  · ext m
    exact hr m

private theorem exists_galoisPerm {K : Type*} [Field K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)]
    {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) ℓ) (σ : K →+* K) :
    ∃ e : Fin ℓ ≃ Fin ℓ,
      ∀ b : Fin ℓ, σ ((ζ : K) ^ (b : ℕ)) = (ζ : K) ^ ((e b : Fin ℓ) : ℕ) := by
  have hσζ : (σ (ζ : K)) ^ ℓ = 1 := by
    rw [← map_pow, hζ.pow_eq_one, map_one]
  obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one hσζ
  set e₀ : Fin ℓ → Fin ℓ := fun b => ⟨(a * (b : ℕ)) % ℓ, Nat.mod_lt _ hℓ.out.pos⟩
  have hkey : ∀ b : Fin ℓ, σ ((ζ : K) ^ (b : ℕ)) = (ζ : K) ^ ((e₀ b : Fin ℓ) : ℕ) := by
    intro b
    show σ ((ζ : K) ^ (b : ℕ)) = (ζ : K) ^ ((a * (b : ℕ)) % ℓ)
    rw [map_pow, ← ha, ← pow_mul]
    exact pow_eq_pow_mod _ hζ.pow_eq_one
  have hinj : Function.Injective e₀ := by
    intro b b' hbb'
    have h1 : σ ((ζ : K) ^ (b : ℕ)) = σ ((ζ : K) ^ ((b' : Fin ℓ) : ℕ)) := by
      rw [hkey b, hkey b', hbb']
    exact Fin.ext (hζ.pow_inj b.isLt b'.isLt (σ.injective h1))
  exact ⟨Equiv.ofBijective e₀ (Finite.injective_iff_bijective.mp hinj), hkey⟩

private theorem mem_range_coeffEmb_qExpand_of_mem_inter {K : Type*} [Field K] [Algebra ℚ K]
    {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)]
    {f : LaurentSeries K} (h1 : f ∈ Set.range (qExpand K ℓ))
    (h2 : f ∈ Set.range (coeffEmb K)) :
    ∃ g : LaurentSeries ℚ, f = coeffEmb K (qExpand ℚ ℓ g) := by
  obtain ⟨h, hh⟩ := h2
  have hsupp : ∀ m : ℤ, ¬ (ℓ : ℤ) ∣ m → h.coeff m = 0 := by
    intro m hm
    obtain ⟨g, hg⟩ := h1
    refine FaithfulSMul.algebraMap_injective ℚ K ?_
    rw [map_zero, ← coeffEmb_coeff, hh, ← hg, qExpand_coeff_of_not_dvd ℓ g hm]
  refine ⟨qContract ℓ h, ?_⟩
  rw [qExpand_qContract hsupp]
  exact hh.symm

end CoreHelpers


namespace QExpN

section Generic

variable {L L' : Type*} [CommRing L] [CommRing L'] {n : ℕ}

def interpPoly (H Y : Fin n → L) : L[X] :=
  ∑ i, C (H i) * ∏ m ∈ Finset.univ.erase i, (X - C (Y m))

def conjPoly (H : Fin n → L) : L[X] := ∏ i, (X - C (H i))

omit [CommRing L'] in
lemma prod_erase_perm (e : Equiv.Perm (Fin n)) (G : Fin n → L[X]) (i : Fin n) :
    ∏ m ∈ Finset.univ.erase i, G (e m) = ∏ m ∈ Finset.univ.erase (e i), G m := by
  refine Finset.prod_equiv e (fun m => ?_) (fun m _ => rfl)
  simp [e.injective.eq_iff]

lemma interpPoly_map (φ : L →+* L') (H Y : Fin n → L) :
    (interpPoly H Y).map φ = interpPoly (φ ∘ H) (φ ∘ Y) := by
  simp only [interpPoly, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod,
    Polynomial.map_sub, Polynomial.map_X, Function.comp_apply]

lemma conjPoly_map (φ : L →+* L') (H : Fin n → L) : (conjPoly H).map φ = conjPoly (φ ∘ H) := by
  simp only [conjPoly, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Function.comp_apply]

omit [CommRing L'] in
lemma interpPoly_perm (e : Equiv.Perm (Fin n)) (H Y : Fin n → L) :
    interpPoly (H ∘ e) (Y ∘ e) = interpPoly H Y := by
  unfold interpPoly
  simp only [Function.comp_apply]
  rw [← Equiv.sum_comp e (fun j => C (H j) * ∏ m ∈ Finset.univ.erase j, (X - C (Y m)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [prod_erase_perm e (fun m => X - C (Y m)) i]

omit [CommRing L'] in
lemma conjPoly_perm (e : Equiv.Perm (Fin n)) (H : Fin n → L) : conjPoly (H ∘ e) = conjPoly H := by
  unfold conjPoly
  simp only [Function.comp_apply]
  exact Equiv.prod_comp e (fun j => X - C (H j))

omit [CommRing L'] in

lemma interpPoly_eval (H Y : Fin n → L) (i₀ : Fin n) :
    (interpPoly H Y).eval (Y i₀) = H i₀ * ∏ m ∈ Finset.univ.erase i₀, (Y i₀ - Y m) := by
  unfold interpPoly
  rw [Polynomial.eval_finsetSum, Finset.sum_eq_single i₀]
  · simp [Polynomial.eval_prod]
  · intro i _ hi
    rw [Polynomial.eval_mul, Polynomial.eval_prod]
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (i := i₀) (by simp [Ne.symm hi]) ?_)
    simp
  · intro h; exact absurd (Finset.mem_univ i₀) h

omit [CommRing L'] in
lemma conjPoly_eval (H : Fin n → L) (i₀ : Fin n) : (conjPoly H).eval (H i₀) = 0 := by
  unfold conjPoly
  rw [Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i₀) (by simp)

omit [CommRing L'] in
lemma conjPoly_monic [Nontrivial L] (H : Fin n → L) : (conjPoly H).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C (H i)

omit [CommRing L'] in
lemma conjPoly_natDegree [Nontrivial L] [NoZeroDivisors L] (H : Fin n → L) : (conjPoly H).natDegree = n := by
  unfold conjPoly
  rw [Polynomial.natDegree_prod _ _ fun i _ => Polynomial.X_sub_C_ne_zero (H i)]
  simp

lemma eval_eq_sum_coeff {p : L[X]} {N : ℕ} (hN : p.natDegree < N) (x : L) :
    p.eval x = ∑ k ∈ Finset.range N, p.coeff k * x ^ k := by
  rw [Polynomial.eval_eq_sum_range' hN]

end Generic

section Slots

variable {K : Type} [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ)
  (hζ : IsPrimitiveRoot (ζ : K) ℓ)

def slotH (f g : LaurentSeries ℚ) : Fin (ℓ + 1) → LaurentSeries K :=
  Fin.cases (coeffEmb K (qExpand ℚ ℓ f)) (fun b : Fin ℓ => qTwist (ζ ^ (b : ℕ)) (coeffEmb K g))

@[scoped simp] lemma slotH_zero (f g : LaurentSeries ℚ) : slotH ℓ ζ f g 0 = coeffEmb K (qExpand ℚ ℓ f) := by
  simp [slotH]

@[scoped simp] lemma slotH_succ (f g : LaurentSeries ℚ) (b : Fin ℓ) :
    slotH ℓ ζ f g b.succ = qTwist (ζ ^ (b : ℕ)) (coeffEmb K g) := by
  simp [slotH]

def liftPerm (e : Equiv.Perm (Fin ℓ)) : Equiv.Perm (Fin (ℓ + 1)) := Equiv.Perm.decomposeFin.symm (0, e)

omit hℓ in
@[scoped simp] lemma liftPerm_zero (e : Equiv.Perm (Fin ℓ)) : liftPerm ℓ e 0 = 0 :=
  Equiv.Perm.decomposeFin_symm_apply_zero 0 e

omit hℓ in
@[scoped simp] lemma liftPerm_succ (e : Equiv.Perm (Fin ℓ)) (b : Fin ℓ) : liftPerm ℓ e b.succ = (e b).succ := by
  rw [liftPerm, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply]

lemma coeffMap_qTwist {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (u : Rˣ) (x : LaurentSeries R) :
    coeffMap φ (qTwist u x) = qTwist (Units.map (φ : R →* S) u) (coeffMap φ x) := by
  ext k
  simp only [coeffMap_coeff, qTwist_coeff, map_mul]
  congr 1
  rw [← map_zpow (Units.map (φ : R →* S)) u k, Units.coe_map]
  rfl

omit hℓ [Algebra ℚ K] in
lemma units_map_zeta_pow (σ : K →+* K) (e : Equiv.Perm (Fin ℓ))
    (he : ∀ b : Fin ℓ, σ ((ζ : K) ^ (b : ℕ)) = (ζ : K) ^ ((e b : Fin ℓ) : ℕ)) (b : Fin ℓ) :
    Units.map (σ : K →* K) (ζ ^ (b : ℕ)) = ζ ^ ((e b : Fin ℓ) : ℕ) := by
  ext
  rw [Units.coe_map, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
  exact he b

lemma coeffMap_slotH (f g : LaurentSeries ℚ) (σ : K ≃ₐ[ℚ] K) (e : Equiv.Perm (Fin ℓ))
    (he : ∀ b : Fin ℓ, σ ((ζ : K) ^ (b : ℕ)) = (ζ : K) ^ ((e b : Fin ℓ) : ℕ)) (i : Fin (ℓ + 1)) :
    coeffMap (σ : K →+* K) (slotH ℓ ζ f g i) = slotH ℓ ζ f g (liftPerm ℓ e i) := by
  refine Fin.cases ?_ (fun b => ?_) i
  · rw [liftPerm_zero, slotH_zero, coeffMap_coeffEmb]
  · rw [liftPerm_succ, slotH_succ, slotH_succ, coeffMap_qTwist, coeffMap_coeffEmb,
      units_map_zeta_pow ℓ ζ (σ : K →+* K) e (fun b => he b) b]

lemma coeffMap_conj (σ : K ≃ₐ[ℚ] K) (e : Equiv.Perm (Fin ℓ))
    (he : ∀ b : Fin ℓ, σ ((ζ : K) ^ (b : ℕ)) = (ζ : K) ^ ((e b : Fin ℓ) : ℕ)) (i : Fin (ℓ + 1)) :
    coeffMap (σ : K →+* K) (PhiGen.conj ℓ ζ i) = PhiGen.conj ℓ ζ (liftPerm ℓ e i) := by
  refine Fin.cases ?_ (fun b => ?_) i
  · rw [liftPerm_zero, PhiGen.conj_zero, coeffMap_qExpand, coeffMap_coeffEmb]
  · rw [liftPerm_succ, PhiGen.conj_succ, PhiGen.conj_succ, coeffMap_qTwist, coeffMap_coeffEmb,
      units_map_zeta_pow ℓ ζ (σ : K →+* K) e (fun b => he b) b]

include hζ in
omit hℓ [Algebra ℚ K] in
lemma zeta_pow_ell : ζ ^ ℓ = 1 := by
  ext; rw [Units.val_pow_eq_pow_val, hζ.pow_eq_one, Units.val_one]

include hζ in
omit [Algebra ℚ K] in

lemma zeta_mul_zeta_pow (b : Fin ℓ) : ζ * ζ ^ (b : ℕ) = ζ ^ (((b + 1 : Fin ℓ)) : ℕ) := by
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  rw [← pow_succ', Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  conv_lhs => rw [← Nat.div_add_mod ((b : ℕ) + 1) ℓ, pow_add, pow_mul, zeta_pow_ell ℓ ζ hζ, one_pow, one_mul]

include hζ in

lemma qTwist_slotH (f g : LaurentSeries ℚ) (i : Fin (ℓ + 1)) :
    qTwist ζ (slotH ℓ ζ f g i) = slotH ℓ ζ f g (liftPerm ℓ (Equiv.addRight (1 : Fin ℓ)) i) := by
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  refine Fin.cases ?_ (fun b => ?_) i
  · rw [liftPerm_zero, slotH_zero, coeffEmb_qExpand, qTwist_qExpand, zpow_natCast, zeta_pow_ell ℓ ζ hζ,
      qTwist_one_apply]
  · rw [liftPerm_succ, slotH_succ, slotH_succ, qTwist_qTwist, Equiv.coe_addRight, zeta_mul_zeta_pow ℓ ζ hζ]

include hζ in
lemma qTwist_conj (i : Fin (ℓ + 1)) :
    qTwist ζ (PhiGen.conj ℓ ζ i) = PhiGen.conj ℓ ζ (liftPerm ℓ (Equiv.addRight (1 : Fin ℓ)) i) := by
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  refine Fin.cases ?_ (fun b => ?_) i
  · rw [liftPerm_zero, PhiGen.conj_zero, qTwist_qExpand]
    congr 1
    rw [show ((ℓ * ℓ : ℕ) : ℤ) = ((ℓ * ℓ : ℕ) : ℤ) from rfl, zpow_natCast, pow_mul, zeta_pow_ell ℓ ζ hζ, one_pow,
      qTwist_one_apply]
  · rw [liftPerm_succ, PhiGen.conj_succ, PhiGen.conj_succ, qTwist_qTwist, Equiv.coe_addRight,
      zeta_mul_zeta_pow ℓ ζ hζ]

def interpK (f g : LaurentSeries ℚ) : (LaurentSeries K)[X] := interpPoly (slotH ℓ ζ f g) (PhiGen.conj ℓ ζ)

def conjK (f g : LaurentSeries ℚ) : (LaurentSeries K)[X] := conjPoly (slotH ℓ ζ f g)

variable [IsGalois ℚ K] [FiniteDimensional ℚ K]

include hζ in

theorem exists_interpK_coeff_eq (f g : LaurentSeries ℚ) (k : ℕ) :
    ∃ ξ : LaurentSeries ℚ, (interpK ℓ ζ f g).coeff k = coeffEmb K (qExpand ℚ ℓ ξ) := by
  refine mem_range_coeffEmb_qExpand_of_mem_inter ?_ ?_
  ·
    refine mem_range_qExpand_of_qTwist_eq ℓ ζ hζ _ ?_
    rw [← Polynomial.coeff_map, interpK, interpPoly_map]
    have h1 : (⇑(qTwist ζ) ∘ slotH ℓ ζ f g) = slotH ℓ ζ f g ∘ liftPerm ℓ (Equiv.addRight (1 : Fin ℓ)) :=
      funext fun i => qTwist_slotH ℓ ζ hζ f g i
    have h2 : (⇑(qTwist ζ) ∘ PhiGen.conj ℓ ζ) = PhiGen.conj ℓ ζ ∘ liftPerm ℓ (Equiv.addRight (1 : Fin ℓ)) :=
      funext fun i => qTwist_conj ℓ ζ hζ i
    rw [h1, h2, interpPoly_perm]
  ·
    refine mem_range_coeffEmb_of_forall_coeffMap_eq
      (fun c hc => (IsGalois.mem_range_algebraMap_iff_fixed c).mpr hc) fun σ => ?_
    obtain ⟨e, he⟩ := exists_galoisPerm hζ (σ : K →+* K)
    rw [← Polynomial.coeff_map, interpK, interpPoly_map]
    have h1 : (⇑(coeffMap (σ : K →+* K)) ∘ slotH ℓ ζ f g) = slotH ℓ ζ f g ∘ liftPerm ℓ e :=
      funext fun i => coeffMap_slotH ℓ ζ f g σ e he i
    have h2 : (⇑(coeffMap (σ : K →+* K)) ∘ PhiGen.conj ℓ ζ) = PhiGen.conj ℓ ζ ∘ liftPerm ℓ e :=
      funext fun i => coeffMap_conj ℓ ζ σ e he i
    rw [h1, h2, interpPoly_perm]

include hζ in

theorem exists_conjK_coeff_eq (f g : LaurentSeries ℚ) (k : ℕ) :
    ∃ π : LaurentSeries ℚ, (conjK ℓ ζ f g).coeff k = coeffEmb K (qExpand ℚ ℓ π) := by
  refine mem_range_coeffEmb_qExpand_of_mem_inter ?_ ?_
  · refine mem_range_qExpand_of_qTwist_eq ℓ ζ hζ _ ?_
    rw [← Polynomial.coeff_map, conjK, conjPoly_map]
    have h1 : (⇑(qTwist ζ) ∘ slotH ℓ ζ f g) = slotH ℓ ζ f g ∘ liftPerm ℓ (Equiv.addRight (1 : Fin ℓ)) :=
      funext fun i => qTwist_slotH ℓ ζ hζ f g i
    rw [h1, conjPoly_perm]
  · refine mem_range_coeffEmb_of_forall_coeffMap_eq
      (fun c hc => (IsGalois.mem_range_algebraMap_iff_fixed c).mpr hc) fun σ => ?_
    obtain ⟨e, he⟩ := exists_galoisPerm hζ (σ : K →+* K)
    rw [← Polynomial.coeff_map, conjK, conjPoly_map]
    have h1 : (⇑(coeffMap (σ : K →+* K)) ∘ slotH ℓ ζ f g) = slotH ℓ ζ f g ∘ liftPerm ℓ e :=
      funext fun i => coeffMap_slotH ℓ ζ f g σ e he i
    rw [h1, conjPoly_perm]

end Slots

end QExpN

namespace RealL

variable {h : ℝ} {A B : LaurentSeries ℂ} {F G : ℍ → ℂ}

open QExpN

lemma sum {ι : Type} (s : Finset ι) {A : ι → LaurentSeries ℂ} {F : ι → ℍ → ℂ}
    (hAF : ∀ i ∈ s, RealL h (A i) (F i)) : RealL h (∑ i ∈ s, A i) (fun τ => ∑ i ∈ s, F i τ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa [Pi.zero_def] using zero h
  | insert a s ha ih =>
    have h1 := (hAF a (Finset.mem_insert_self a s)).add (ih fun i hi => hAF i (Finset.mem_insert_of_mem hi))
    refine h1.congr (Finset.sum_insert ha).symm fun τ => ?_
    simp [Finset.sum_insert ha]

lemma interpPoly_coeff (hh : 0 < h) {n : ℕ} {Hs Ys : Fin n → LaurentSeries ℂ} {η υ : Fin n → ℍ → ℂ}
    (hH : ∀ i, RealL h (Hs i) (η i)) (hY : ∀ i, RealL h (Ys i) (υ i)) (k : ℕ) :
    RealL h ((interpPoly Hs Ys).coeff k)
      (fun τ => (interpPoly (fun i => η i τ) (fun i => υ i τ)).coeff k) := by
  unfold interpPoly
  have h1 : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      RealL h ((Polynomial.C (Hs i) * ∏ m ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (Ys m))).coeff k)
        (fun τ => (Polynomial.C (η i τ) *
          ∏ m ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (υ m τ))).coeff k) := by
    intro i _
    refine ((hH i).mul hh (coeff_prod_X_sub_C hh (Finset.univ.erase i) (fun m _ => hY m) k)).congr
      ?_ fun τ => ?_
    · rw [Polynomial.coeff_C_mul]
    · simp only [Pi.mul_apply, Polynomial.coeff_C_mul]
  refine (sum Finset.univ h1).congr ?_ fun τ => ?_
  · rw [Polynomial.finsetSum_coeff]
  · simp only [Polynomial.finsetSum_coeff]

lemma conjPoly_coeff (hh : 0 < h) {n : ℕ} {Hs : Fin n → LaurentSeries ℂ} {η : Fin n → ℍ → ℂ}
    (hH : ∀ i, RealL h (Hs i) (η i)) (k : ℕ) :
    RealL h ((conjPoly Hs).coeff k) (fun τ => (conjPoly fun i => η i τ).coeff k) :=
  coeff_prod_X_sub_C hh Finset.univ (fun i _ => hH i) k

end RealL

namespace QExpN

section Periods

variable (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)]

lemma realL_one_of_realL_qExpand (x : LaurentSeries ℂ) (F : ℍ → ℂ) (hx : RealL ℓ (qExpand ℂ ℓ x) F) :
    RealL 1 x F := by
  intro τ
  have hinj : Function.Injective (fun n : ℤ => (ℓ : ℤ) * n) :=
    mul_right_injective₀ (by exact_mod_cast hℓ.out.ne_zero)
  have h := hx τ
  rw [← hinj.hasSum_iff] at h
  · refine h.congr_fun fun n => ?_
    simp only [Function.comp_apply, qExpand_coeff_mul]
    congr 1
    rw [zpow_mul, zpow_natCast]
    congr 1
    simp only [Periodic.qParam, Complex.ofReal_one, div_one, Complex.ofReal_natCast]
    rw [← Complex.exp_nat_mul]
    congr 1
    field_simp [(Nat.cast_ne_zero.mpr hℓ.out.ne_zero : (ℓ : ℂ) ≠ 0)]
  · intro m hm
    rw [qExpand_coeff_of_not_dvd ℓ _ (fun ⟨n, hn⟩ => hm ⟨n, hn.symm⟩), zero_mul]

lemma realL_qExpand_of_realL_one (x : LaurentSeries ℂ) (F : ℍ → ℂ) (hx : RealL 1 x F) :
    RealL ℓ (qExpand ℂ ℓ x) F := by
  intro τ
  have hinj : Function.Injective (fun n : ℤ => (ℓ : ℤ) * n) :=
    mul_right_injective₀ (by exact_mod_cast hℓ.out.ne_zero)
  rw [← hinj.hasSum_iff]
  · refine (hx τ).congr_fun fun n => ?_
    simp only [Function.comp_apply, qExpand_coeff_mul]
    congr 1
    rw [zpow_mul, zpow_natCast]
    congr 1
    simp only [Periodic.qParam, Complex.ofReal_one, div_one, Complex.ofReal_natCast]
    rw [← Complex.exp_nat_mul]
    congr 1
    field_simp [(Nat.cast_ne_zero.mpr hℓ.out.ne_zero : (ℓ : ℂ) ≠ 0)]
  · intro m hm
    rw [qExpand_coeff_of_not_dvd ℓ _ (fun ⟨n, hn⟩ => hm ⟨n, hn.symm⟩), zero_mul]

def expRoot : ℂ := Complex.exp (2 * Real.pi * Complex.I / ℓ)

lemma isPrimitiveRoot_expRoot : IsPrimitiveRoot (expRoot ℓ) ℓ :=
  Complex.isPrimitiveRoot_exp ℓ hℓ.out.ne_zero

omit hℓ in
lemma expRoot_pow_zpow (b : ℕ) (m : ℤ) :
    (expRoot ℓ ^ b) ^ m = Complex.exp (2 * Real.pi * Complex.I * b * m / ℓ) := by
  rw [expRoot, ← Complex.exp_nat_mul, ← Complex.exp_int_mul]
  congr 1
  ring

omit hℓ in

lemma qParam_T_pow_smul (b : ℕ) (τ : ℍ) :
    𝕢 ℓ (((ModularGroup.T ^ b • τ : ℍ)) : ℂ) = expRoot ℓ ^ b * 𝕢 ℓ (τ : ℂ) := by
  have h := modular_T_zpow_smul τ (b : ℤ)
  rw [zpow_natCast] at h
  rw [h, coe_vadd, expRoot, ← Complex.exp_nat_mul]
  simp only [Periodic.qParam, Complex.ofReal_natCast, Int.cast_natCast]
  rw [← Complex.exp_add]
  congr 1
  ring

omit hℓ in

lemma realL_twist (A : LaurentSeries ℂ) (G : ℍ → ℂ) (hA : RealL ℓ A G) (b : ℕ) (B : LaurentSeries ℂ)
    (hB : ∀ m : ℤ, B.coeff m = (expRoot ℓ ^ b) ^ m * A.coeff m) :
    RealL ℓ B (fun τ => G (ModularGroup.T ^ b • τ)) := by
  intro τ
  have h := hA (ModularGroup.T ^ b • τ)
  refine h.congr_fun fun m => ?_
  rw [hB m, qParam_T_pow_smul, mul_zpow]
  ring

end Periods

section Analytic

variable {K : Type} [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ)
  (hζ : IsPrimitiveRoot (ζ : K) ℓ) (σ : K →+* ℂ) (hσ : σ (ζ : K) = expRoot ℓ)

def jt (τ : ℍ) : ℂ := ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ

def jtN (τ : ℍ) : ℂ := jt (ModularForm.heckeDiagMatrix ℓ • τ)

abbrev castC : ℚ →+* ℂ := Rat.castHom ℂ

omit hℓ in

lemma coeffMap_sigma_coeffEmb (x : LaurentSeries ℚ) : coeffMap σ (coeffEmb K x) = coeffMap castC x := by
  ext m
  rw [coeffMap_coeff, coeffEmb_coeff, coeffMap_coeff, eq_ratCast, map_ratCast]
  rfl

def cosetRep (i : Fin (ℓ + 1)) : SL(2, ℤ) :=
  Fin.cases (1 : SL(2, ℤ)) (fun b : Fin ℓ => ModularGroup.S * ModularGroup.T ^ (b : ℕ)) i

omit hℓ in
@[scoped simp] lemma cosetRep_zero : cosetRep ℓ 0 = 1 := by simp [cosetRep]
omit hℓ in
@[scoped simp] lemma cosetRep_succ (b : Fin ℓ) : cosetRep ℓ b.succ = ModularGroup.S * ModularGroup.T ^ (b : ℕ) := by
  simp [cosetRep]

def slotF (F : ℍ → ℂ) (i : Fin (ℓ + 1)) (τ : ℍ) : ℂ := F (cosetRep ℓ i • τ)

def slotJ (i : Fin (ℓ + 1)) (τ : ℍ) : ℂ := jtN ℓ (cosetRep ℓ i • τ)

variable (f g : LaurentSeries ℚ) (F : ℍ → ℂ)
  (hF : ∀ τ : ℍ, HasSum (fun m : ℤ => ((f.coeff m : ℚ) : ℂ) * 𝕢 1 (τ : ℂ) ^ m) (F τ))
  (hG : ∀ τ : ℍ, HasSum (fun m : ℤ => ((g.coeff m : ℚ) : ℂ) * 𝕢 ℓ (τ : ℂ) ^ m) (F (ModularGroup.S • τ)))

include hF in
omit hℓ in
lemma realL_fC : RealL 1 (coeffMap castC f) F := fun τ => hF τ

include hG in
omit hℓ in
lemma realL_gC : RealL ℓ (coeffMap castC g) (fun τ => F (ModularGroup.S • τ)) := fun τ => hG τ

include hF hG hσ in

lemma realL_slotH (i : Fin (ℓ + 1)) :
    RealL ℓ (coeffMap σ (slotH ℓ ζ f g i)) (slotF ℓ F i) := by
  refine Fin.cases ?_ (fun b => ?_) i
  ·
    have h := realL_qExpand_of_realL_one ℓ _ _ (realL_fC f F hF)
    refine h.congr ?_ fun τ => ?_
    · rw [slotH_zero, coeffMap_sigma_coeffEmb, coeffMap_qExpand]
    · simp [slotF]
  ·
    have h := realL_twist ℓ _ _ (realL_gC ℓ g F hG) (b : ℕ) (coeffMap σ (slotH ℓ ζ f g b.succ)) fun m => by
      rw [slotH_succ, coeffMap_coeff, qTwist_coeff, map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀,
        Units.val_pow_eq_pow_val, map_pow, hσ, coeffEmb_coeff, eq_ratCast, map_ratCast, coeffMap_coeff]
      rfl
    refine h.congr rfl fun τ => ?_
    simp only [slotF, cosetRep_succ, mul_smul]

lemma coeffMap_conj_zero_eq : coeffMap σ (PhiGen.conj ℓ ζ 0) = qExpand ℂ (ℓ * ℓ) (coeffMap castC jq) := by
  rw [PhiGen.conj_zero, coeffMap_qExpand, coeffMap_sigma_coeffEmb]

omit hℓ in
lemma realL_jqC : RealL 1 (coeffMap castC jq) jt := fun τ => hasSum_jq_qParam τ

omit hℓ in

lemma heckeDiag_smul_S_T_pow_smul [NeZero ℓ] (b : ℕ) (τ : ℍ) :
    ModularForm.heckeDiagMatrix ℓ • (ModularGroup.S * ModularGroup.T ^ b) • τ =
      ModularGroup.S • ModularForm.heckeMatrix ℓ b • τ := by
  have hT : ((ModularGroup.T ^ b : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, (b : ℤ); 0, 1] := by
    have := ModularGroup.coe_T_zpow (b : ℤ)
    rwa [zpow_natCast] at this
  set g : SL(2, ℤ) := ModularGroup.S * ModularGroup.T ^ b with hg
  have hg' : (g : Matrix (Fin 2) (Fin 2) ℤ) = !![0, -1; 1, (b : ℤ)] := by
    rw [hg, Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S, hT]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have h00 : g 0 0 = 0 := congrFun (congrFun hg' 0) 0
  have h01 : g 0 1 = -1 := congrFun (congrFun hg' 0) 1
  have h10 : g 1 0 = 1 := congrFun (congrFun hg' 1) 0
  have h11 : g 1 1 = b := congrFun (congrFun hg' 1) 1
  clear_value g
  have hmat : ModularForm.heckeDiagMatrix ℓ * Matrix.SpecialLinearGroup.mapGL ℝ g =
      Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S * ModularForm.heckeMatrix ℓ b := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ModularForm.val_heckeDiagMatrix (NeZero.ne ℓ),
        ModularForm.val_heckeMatrix (NeZero.ne ℓ), ModularGroup.coe_S, h00, h01, h10, h11]
  have h1 : ModularForm.heckeDiagMatrix ℓ • g • τ =
      (ModularForm.heckeDiagMatrix ℓ * Matrix.SpecialLinearGroup.mapGL ℝ g) • τ := by
    rw [mul_smul]; rfl
  have h2 : ModularGroup.S • ModularForm.heckeMatrix ℓ b • τ =
      (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S * ModularForm.heckeMatrix ℓ b) • τ := by
    rw [mul_smul]; rfl
  rw [h1, h2, hmat]

include hσ in

lemma realL_conj (i : Fin (ℓ + 1)) : RealL ℓ (coeffMap σ (PhiGen.conj ℓ ζ i)) (slotJ ℓ i) := by
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  refine Fin.cases ?_ (fun b => ?_) i
  · intro τ
    have h := hasSum_qParam_heckeDiagMatrix_smul ℓ (coeffMap castC jq) jt realL_jqC τ
    rw [coeffMap_conj_zero_eq]
    simpa [slotJ, jtN] using h
  · intro τ
    have h := hasSum_qParam_heckeMatrix_smul ℓ (b : ℕ) (coeffMap castC jq) jt realL_jqC τ
    have hval : slotJ ℓ b.succ τ = jt (ModularForm.heckeMatrix ℓ (b : ℕ) • τ) := by
      rw [slotJ, jtN, cosetRep_succ, heckeDiag_smul_S_T_pow_smul]
      exact E4_cube_div_discriminant_smul ModularGroup.S _
    rw [hval]
    refine h.congr_fun fun m => ?_
    congr 1
    rw [PhiGen.conj_succ, coeffMap_coeff, qTwist_coeff, map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀,
      Units.val_pow_eq_pow_val, map_pow, hσ, expRoot_pow_zpow, coeffEmb_coeff, eq_ratCast, map_ratCast,
      coeffMap_coeff]
    rfl

def interpFun (k : ℕ) (τ : ℍ) : ℂ := (interpPoly (fun i => slotF ℓ F i τ) (fun i => slotJ ℓ i τ)).coeff k

def conjFun (k : ℕ) (τ : ℍ) : ℂ := (conjPoly fun i => slotF ℓ F i τ).coeff k

variable (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma0 ℓ, ∀ τ : ℍ, F (γ • τ) = F τ)

omit hℓ in

lemma jtN_smul [NeZero ℓ] (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 ℓ) (τ : ℍ) :
    jtN ℓ (γ • τ) = jtN ℓ τ := by
  obtain ⟨γ', hγ', -⟩ := exists_sl2_heckeDiagMatrix_smul_eq ℓ γ hγ
  rw [jtN, jtN, hγ' τ]
  exact E4_cube_div_discriminant_smul γ' _

include hinv in

lemma slots_smul (γ : SL(2, ℤ)) : ∃ e : Equiv.Perm (Fin (ℓ + 1)),
    (∀ i τ, slotF ℓ F i (γ • τ) = slotF ℓ F (e i) τ) ∧ (∀ i τ, slotJ ℓ i (γ • τ) = slotJ ℓ (e i) τ) := by
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  obtain ⟨e, he⟩ := exists_perm_gamma0_cosetReps ℓ γ
  have key : ∀ (i : Fin (ℓ + 1)) (τ : ℍ),
      cosetRep ℓ i • γ • τ = (cosetRep ℓ i * γ * (cosetRep ℓ (e i))⁻¹) • cosetRep ℓ (e i) • τ := by
    intro i τ
    simp only [smul_smul, inv_mul_cancel_right]
  have he' : ∀ i, cosetRep ℓ i * γ * (cosetRep ℓ (e i))⁻¹ ∈ CongruenceSubgroup.Gamma0 ℓ := he
  refine ⟨e, fun i τ => ?_, fun i τ => ?_⟩
  · rw [slotF, slotF, key, hinv _ (he' i)]
  · rw [slotJ, slotJ, key, jtN_smul ℓ _ (he' i)]

include hinv in
lemma interpFun_smul (k : ℕ) (γ : SL(2, ℤ)) (τ : ℍ) : interpFun ℓ F k (γ • τ) = interpFun ℓ F k τ := by
  obtain ⟨e, h1, h2⟩ := slots_smul ℓ F hinv γ
  unfold interpFun
  have hH : (fun i => slotF ℓ F i (γ • τ)) = (fun i => slotF ℓ F i τ) ∘ e := funext fun i => h1 i τ
  have hY : (fun i => slotJ ℓ i (γ • τ)) = (fun i => slotJ ℓ i τ) ∘ e := funext fun i => h2 i τ
  rw [hH, hY, interpPoly_perm]

include hinv in
lemma conjFun_smul (k : ℕ) (γ : SL(2, ℤ)) (τ : ℍ) : conjFun ℓ F k (γ • τ) = conjFun ℓ F k τ := by
  obtain ⟨e, h1, -⟩ := slots_smul ℓ F hinv γ
  unfold conjFun
  have hH : (fun i => slotF ℓ F i (γ • τ)) = (fun i => slotF ℓ F i τ) ∘ e := funext fun i => h1 i τ
  rw [hH, conjPoly_perm]

include hF hG hσ hinv in

lemma mem_adjoin_of_interpK_coeff_eq (k : ℕ) (ξ : LaurentSeries ℚ)
    (hξ : (interpK ℓ ζ f g).coeff k = coeffEmb K (qExpand ℚ ℓ ξ)) : ξ ∈ Algebra.adjoin ℚ {jq} := by

  have h1 : RealL ℓ (coeffMap σ ((interpK ℓ ζ f g).coeff k)) (interpFun ℓ F k) := by
    have h := RealL.interpPoly_coeff (h := (ℓ : ℝ)) (by exact_mod_cast hℓ.out.pos)
      (fun i => realL_slotH ℓ ζ σ hσ f g F hF hG i) (fun i => realL_conj ℓ ζ σ hσ i) k
    refine h.congr ?_ fun τ => rfl
    rw [← Polynomial.coeff_map, interpK, interpPoly_map]
    rfl
  rw [hξ, coeffMap_sigma_coeffEmb, coeffMap_qExpand] at h1
  have h2 := realL_one_of_realL_qExpand ℓ _ _ h1
  exact mem_adjoin_jq_of_hasSum_of_slash_invariant ξ (interpFun ℓ F k) h2
    (fun γ τ => interpFun_smul ℓ F hinv k γ τ)

include hF hG hσ hinv in
lemma mem_adjoin_of_conjK_coeff_eq (k : ℕ) (π : LaurentSeries ℚ)
    (hπ : (conjK ℓ ζ f g).coeff k = coeffEmb K (qExpand ℚ ℓ π)) : π ∈ Algebra.adjoin ℚ {jq} := by
  have h1 : RealL ℓ (coeffMap σ ((conjK ℓ ζ f g).coeff k)) (conjFun ℓ F k) := by
    have h := RealL.conjPoly_coeff (h := (ℓ : ℝ)) (by exact_mod_cast hℓ.out.pos)
      (fun i => realL_slotH ℓ ζ σ hσ f g F hF hG i) k
    refine h.congr ?_ fun τ => rfl
    rw [← Polynomial.coeff_map, conjK, conjPoly_map]
    rfl
  rw [hπ, coeffMap_sigma_coeffEmb, coeffMap_qExpand] at h1
  have h2 := realL_one_of_realL_qExpand ℓ _ _ h1
  exact mem_adjoin_jq_of_hasSum_of_slash_invariant π (conjFun ℓ F k) h2
    (fun γ τ => conjFun_smul ℓ F hinv k γ τ)

end Analytic

section Assembly

variable {K : Type} [Field K] [Algebra ℚ K] [IsGalois ℚ K] [FiniteDimensional ℚ K]
  (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ) (σ : K →+* ℂ)
  (hσ : σ (ζ : K) = expRoot ℓ)
  (f g : LaurentSeries ℚ) (F : ℍ → ℂ)
  (hF : ∀ τ : ℍ, HasSum (fun m : ℤ => ((f.coeff m : ℚ) : ℂ) * 𝕢 1 (τ : ℂ) ^ m) (F τ))
  (hG : ∀ τ : ℍ, HasSum (fun m : ℤ => ((g.coeff m : ℚ) : ℂ) * 𝕢 ℓ (τ : ℂ) ^ m) (F (ModularGroup.S • τ)))
  (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma0 ℓ, ∀ τ : ℍ, F (γ • τ) = F τ)

def iota : LaurentSeries ℚ →+* LaurentSeries K := (coeffEmb K).comp (qExpand ℚ ℓ)

omit [IsGalois ℚ K] [FiniteDimensional ℚ K] in
lemma iota_apply (x : LaurentSeries ℚ) : iota (K := K) ℓ x = coeffEmb K (qExpand ℚ ℓ x) := rfl

omit [IsGalois ℚ K] [FiniteDimensional ℚ K] in
lemma coeffEmb_injective' : Function.Injective (coeffEmb K : LaurentSeries ℚ → LaurentSeries K) := by
  intro x y h
  ext m
  have hm := congrArg (fun z : LaurentSeries K => z.coeff m) h
  simp only [coeffEmb_coeff] at hm
  exact (algebraMap ℚ K).injective hm

omit [IsGalois ℚ K] [FiniteDimensional ℚ K] in
lemma iota_injective : Function.Injective (iota (K := K) ℓ) :=
  coeffEmb_injective'.comp (qExpand_injective (R := ℚ) ℓ)

omit [IsGalois ℚ K] [FiniteDimensional ℚ K] in
lemma iota_eq_slotH_zero : iota ℓ f = slotH ℓ ζ f g 0 := by
  rw [iota_apply, slotH_zero]

omit [IsGalois ℚ K] [FiniteDimensional ℚ K] in
lemma iota_jqN : iota (K := K) ℓ (jqN ℓ) = PhiGen.conj ℓ ζ 0 := by
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  rw [iota_apply, jqN, qExpand_qExpand, PhiGen.conj_zero, coeffEmb_qExpand]

def dHat : LaurentSeries K := ∏ m ∈ Finset.univ.erase (0 : Fin (ℓ + 1)), (PhiGen.conj ℓ ζ 0 - PhiGen.conj ℓ ζ m)

include hζ in
omit [IsGalois ℚ K] [FiniteDimensional ℚ K] in
lemma dHat_ne_zero : dHat ℓ ζ ≠ 0 := by
  rw [dHat, Finset.prod_ne_zero_iff]
  intro m hm h0
  exact (Finset.ne_of_mem_erase hm) ((PhiGen.conj_injective ℓ ζ hζ (sub_eq_zero.mp h0)).symm)

include hζ in

lemma exists_sum_eq_mul_dHat (hmem : ∀ (k : ℕ) (ξ : LaurentSeries ℚ),
      (interpK ℓ ζ f g).coeff k = coeffEmb K (qExpand ℚ ℓ ξ) → ξ ∈ Algebra.adjoin ℚ {jq}) :
    ∃ x : LaurentSeries ℚ, x ∈ modularFunctionField ℓ ∧ iota ℓ x = iota ℓ f * dHat ℓ ζ := by
  classical
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  choose ξ hξ using fun k => exists_interpK_coeff_eq ℓ ζ hζ f g k
  have hadj : Algebra.adjoin ℚ {jq} ≤ (modularFunctionField ℓ).toSubalgebra :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr (jq_mem ℓ))
  refine ⟨∑ k ∈ Finset.range ((interpK ℓ ζ f g).natDegree + 1), ξ k * jqN ℓ ^ k, ?_, ?_⟩
  · refine sum_mem fun k _ => mul_mem (hadj (hmem k (ξ k) (hξ k))) (pow_mem (jqN_mem ℓ) k)
  · rw [map_sum]
    simp only [map_mul, map_pow, iota_jqN ℓ ζ, iota_apply, ← hξ]
    rw [← Polynomial.eval_eq_sum_range, interpK, interpPoly_eval, ← slotH_zero ℓ ζ f g, dHat]

include hζ hσ hF hG hinv in

theorem mem_modularFunctionField_of_data : f ∈ modularFunctionField ℓ := by
  classical
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩

  obtain ⟨x, hx, hιx⟩ := exists_sum_eq_mul_dHat ℓ ζ hζ f g
    (fun k ξ h => mem_adjoin_of_interpK_coeff_eq ℓ ζ σ hσ f g F hF hG hinv k ξ h)

  have h1F : ∀ τ : ℍ, HasSum (fun m : ℤ => (((1 : LaurentSeries ℚ).coeff m : ℚ) : ℂ) * 𝕢 1 (τ : ℂ) ^ m)
      ((fun _ : ℍ => (1 : ℂ)) τ) := by
    intro τ
    have h := RealL.one 1 τ
    rw [← map_one (coeffMap castC)] at h
    exact h
  have h1G : ∀ τ : ℍ, HasSum (fun m : ℤ => (((1 : LaurentSeries ℚ).coeff m : ℚ) : ℂ) * 𝕢 ℓ (τ : ℂ) ^ m)
      ((fun _ : ℍ => (1 : ℂ)) (ModularGroup.S • τ)) := by
    intro τ
    have h := RealL.one (ℓ : ℝ) τ
    rw [← map_one (coeffMap castC)] at h
    exact h
  obtain ⟨d, hd, hιd⟩ := exists_sum_eq_mul_dHat ℓ ζ hζ 1 1
    (fun k ξ h => mem_adjoin_of_interpK_coeff_eq ℓ ζ σ hσ 1 1 (fun _ => 1) h1F h1G (fun _ _ _ => rfl) k ξ h)
  rw [map_one, one_mul] at hιd
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact dHat_ne_zero ℓ ζ hζ (by rw [map_zero] at hιd; exact hιd.symm)
  have hfd : f * d = x := iota_injective (K := K) ℓ (by rw [map_mul, hιd, hιx])
  have hf : f = x * d⁻¹ := by rw [← hfd, mul_inv_cancel_right₀ hd0]
  rw [hf]
  exact mul_mem hx (inv_mem hd)

include hζ hσ hF hG hinv in

theorem isIntegral_of_data : IsIntegral (Algebra.adjoin ℚ {jq}) f := by
  classical
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  choose π hπ using fun k => exists_conjK_coeff_eq ℓ ζ hζ f g k
  have hπmem : ∀ k, π k ∈ Algebra.adjoin ℚ {jq} := fun k =>
    mem_adjoin_of_conjK_coeff_eq ℓ ζ σ hσ f g F hF hG hinv k (π k) (hπ k)
  have hdeg : (conjK ℓ ζ f g).natDegree = ℓ + 1 := conjPoly_natDegree _
  have hmon : (conjK ℓ ζ f g).Monic := conjPoly_monic _

  let p : Polynomial (Algebra.adjoin ℚ {jq}) :=
    ∑ k ∈ Finset.range (ℓ + 2),
      Polynomial.C (⟨π k, hπmem k⟩ : Algebra.adjoin ℚ {jq}) * (Polynomial.X : Polynomial (Algebra.adjoin ℚ {jq})) ^ k
  have hcoeffp : ∀ n, p.coeff n = if n < ℓ + 2 then (⟨π n, hπmem n⟩ : Algebra.adjoin ℚ {jq}) else 0 := by
    intro n
    simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one,
      mul_zero]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_range]
  have hmapmap : (p.map (algebraMap (Algebra.adjoin ℚ {jq}) (LaurentSeries ℚ))).map (iota ℓ) = conjK ℓ ζ f g := by
    rw [Polynomial.map_map]
    simp only [p, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
      RingHom.comp_apply]
    have hk : ∀ k, (iota (K := K) ℓ) ((algebraMap (Algebra.adjoin ℚ {jq}) (LaurentSeries ℚ)) ⟨π k, hπmem k⟩) =
        (conjK ℓ ζ f g).coeff k :=
      fun k => (hπ k).symm
    simp only [hk]
    exact (Polynomial.as_sum_range_C_mul_X_pow' _ (by rw [hdeg]; omega)).symm
  refine ⟨p, ?_, ?_⟩
  · refine Polynomial.monic_of_natDegree_le_of_coeff_eq_one (ℓ + 1) ?_ ?_
    · exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk =>
        (Polynomial.natDegree_C_mul_X_pow_le _ k).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    · rw [hcoeffp, ite_eq_left (by omega)]
      refine Subtype.ext ?_
      apply iota_injective (K := K) ℓ
      rw [iota_apply, ← hπ (ℓ + 1), ← hdeg, hmon.coeff_natDegree]
      exact (map_one (iota (K := K) ℓ)).symm
  · rw [Polynomial.eval₂_eq_eval_map]
    apply iota_injective (K := K) ℓ
    rw [map_zero]
    change (iota ℓ) (Polynomial.eval₂ (RingHom.id _) f
      ((p.map (algebraMap (Algebra.adjoin ℚ {jq}) (LaurentSeries ℚ))))) = 0
    rw [Polynomial.hom_eval₂, Polynomial.eval₂_eq_eval_map, ← Polynomial.map_map, Polynomial.map_id, hmapmap,
      iota_eq_slotH_zero ℓ ζ f g, conjK]
    exact conjPoly_eval _ 0

end Assembly

section Main

variable (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)]

def sigma (ζ : (CyclotomicField ℓ ℚ)ˣ) (hζ : IsPrimitiveRoot (ζ : CyclotomicField ℓ ℚ) ℓ) :
    CyclotomicField ℓ ℚ →+* ℂ :=
  letI : Algebra ℚ (CyclotomicField ℓ ℚ) := CyclotomicField.algebra ℓ ℚ
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  haveI := CyclotomicField.isCyclotomicExtension ℓ ℚ
  ((hζ.embeddingsEquivPrimitiveRoots ℂ (Polynomial.cyclotomic.irreducible_rat hℓ.out.pos)).symm
    ⟨expRoot ℓ, (mem_primitiveRoots hℓ.out.pos).mpr (isPrimitiveRoot_expRoot ℓ)⟩).toRingHom

lemma sigma_zeta (ζ : (CyclotomicField ℓ ℚ)ˣ) (hζ : IsPrimitiveRoot (ζ : CyclotomicField ℓ ℚ) ℓ) :
    sigma ℓ ζ hζ (ζ : CyclotomicField ℓ ℚ) = expRoot ℓ := by
  let : Algebra ℚ (CyclotomicField ℓ ℚ) := CyclotomicField.algebra ℓ ℚ
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  have := CyclotomicField.isCyclotomicExtension ℓ ℚ
  let e := hζ.embeddingsEquivPrimitiveRoots ℂ (Polynomial.cyclotomic.irreducible_rat hℓ.out.pos)
  let r : primitiveRoots ℓ ℂ := ⟨expRoot ℓ, (mem_primitiveRoots hℓ.out.pos).mpr (isPrimitiveRoot_expRoot ℓ)⟩
  have h := IsPrimitiveRoot.embeddingsEquivPrimitiveRoots_apply_coe hζ ℂ
    (Polynomial.cyclotomic.irreducible_rat hℓ.out.pos) (e.symm r)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

variable (f g : LaurentSeries ℚ) (F : ℍ → ℂ)
  (hF : ∀ τ : ℍ, HasSum (fun m : ℤ => ((f.coeff m : ℚ) : ℂ) * 𝕢 1 (τ : ℂ) ^ m) (F τ))
  (hG : ∀ τ : ℍ, HasSum (fun m : ℤ => ((g.coeff m : ℚ) : ℂ) * 𝕢 ℓ (τ : ℂ) ^ m) (F (ModularGroup.S • τ)))
  (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma0 ℓ, ∀ τ : ℍ, F (γ • τ) = F τ)

include hF hG hinv in

theorem mem_modularFunctionField : f ∈ modularFunctionField ℓ := by
  have : NeZero ((ℓ : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr hℓ.out.ne_zero⟩
  have hcyc : IsCyclotomicExtension {ℓ} ℚ (CyclotomicField ℓ ℚ) :=
    CyclotomicField.isCyclotomicExtension (n := ℓ) (K := ℚ)
  have : FiniteDimensional ℚ (CyclotomicField ℓ ℚ) :=
    IsCyclotomicExtension.finiteDimensional {ℓ} ℚ (CyclotomicField ℓ ℚ)
  have : IsGalois ℚ (CyclotomicField ℓ ℚ) :=
    IsCyclotomicExtension.isGalois (S := {ℓ}) (K := ℚ) (L := CyclotomicField ℓ ℚ)
  obtain ⟨z, hz⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ (CyclotomicField ℓ ℚ)
    (Set.mem_singleton ℓ) hℓ.out.ne_zero
  have hzu : IsUnit z := hz.isUnit hℓ.out.ne_zero
  have hζ : IsPrimitiveRoot ((hzu.unit : (CyclotomicField ℓ ℚ)ˣ) : CyclotomicField ℓ ℚ) ℓ := by
    rw [hzu.unit_spec]; exact hz
  exact mem_modularFunctionField_of_data ℓ hzu.unit hζ (sigma ℓ hzu.unit hζ) (sigma_zeta ℓ hzu.unit hζ)
    f g F hF hG hinv

include hF hG hinv in

theorem isIntegral_adjoin_jq : IsIntegral (Algebra.adjoin ℚ {jq}) f := by
  have : NeZero ((ℓ : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr hℓ.out.ne_zero⟩
  have hcyc : IsCyclotomicExtension {ℓ} ℚ (CyclotomicField ℓ ℚ) :=
    CyclotomicField.isCyclotomicExtension (n := ℓ) (K := ℚ)
  have : FiniteDimensional ℚ (CyclotomicField ℓ ℚ) :=
    IsCyclotomicExtension.finiteDimensional {ℓ} ℚ (CyclotomicField ℓ ℚ)
  have : IsGalois ℚ (CyclotomicField ℓ ℚ) :=
    IsCyclotomicExtension.isGalois (S := {ℓ}) (K := ℚ) (L := CyclotomicField ℓ ℚ)
  obtain ⟨z, hz⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ (CyclotomicField ℓ ℚ)
    (Set.mem_singleton ℓ) hℓ.out.ne_zero
  have hzu : IsUnit z := hz.isUnit hℓ.out.ne_zero
  have hζ : IsPrimitiveRoot ((hzu.unit : (CyclotomicField ℓ ℚ)ˣ) : CyclotomicField ℓ ℚ) ℓ := by
    rw [hzu.unit_spec]; exact hz
  exact isIntegral_of_data ℓ hzu.unit hζ (sigma ℓ hzu.unit hζ) (sigma_zeta ℓ hzu.unit hζ) f g F hF hG hinv

end Main

end QExpN

end ModularCurve
