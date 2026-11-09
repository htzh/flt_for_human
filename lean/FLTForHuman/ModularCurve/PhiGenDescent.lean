/-
  T11 — piece (a): the coefficients of the conjugate product descend to `ℚ((q))`.

  `PhiGenDescends ℓ ζ c` records that each `X`-coefficient of
  `phiProd ℓ (conj ℓ ζ)` lies in the image of the level substitution
  `coeffEmb K ∘ qExpand ℚ ℓ`; this module *produces* such a family `c`, from the
  two invariances of the product:

  * the nome twist `q ↦ ζ q` cycles the `ℓ` finite-slope roots and fixes the
    extra root `j(q ^ (ℓ * ℓ))`, so every coefficient is twist-fixed — hence lies
    in the range of `qExpand ℚ ℓ` (its support collapses onto multiples of `ℓ`);
  * every `σ : K ≃ₐ[ℚ] K` permutes the roots `ζ ^ b`, so every coefficient is
    Galois-fixed — hence lies in the range of `coeffEmb K`.

  Intersecting the two ranges (`mem_range_coeffEmb_qExpand_of_mem_inter`) gives
  the descent. This is base/006 §6.2 verbatim; no analysis is involved.

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  `P2M/Sol/S_ModularCurve_PhiGen_exists_phiGenDescends.lean` (315 lines). The pin
  keeps `exists_phiGenDescends` `private` and exposes it through its wrapper
  `Theorems/Thm_ModularCurve_PhiGen_exists_phiGenDescends.lean`; the port's one
  public statement is that wrapper verbatim. Every helper is `private`, because
  the module's surface is the single export (the pin makes most of them public,
  but nothing else consumes them).

  ## Assumptions

  `qExpand`, `qExpand_coeff_mul`, `qExpand_coeff_of_not_dvd`, `qExpand_qExpand`,
  `coeffMap`, `coeffMap_coeff`, `coeffEmb`, `coeffEmb_coeff`, `coeffMap_coeffEmb`,
  `coeffMap_qExpand` are the port's `Defs/Laurent`; `qTwist`, `qTwist_coeff`,
  `qTwist_one_apply`, `qTwist_qTwist`, `qTwist_qExpand`, `coeffMap_qTwist` the port's
  `Defs/Twist`;
  `jq`, `jqN` the port's `Defs/Jq`; `conj`, `conj_zero`, `conj_succ`, `phiProd`,
  `PhiGenDescends` the port's `Defs/PhiGen`. `IsGalois`/`FiniteDimensional` and
  `IsPrimitiveRoot` are mathlib's.
  Wired here, not in the frozen registry: the module left `PORT_FILES`
  (`spec/old_check_stmts.py`) on 2026-11-06 and carries its own `spec-pin:` wire.

  spec-pin: Theorems/Thm_ModularCurve_PhiGen_exists_phiGenDescends.lean
-/
import FLTForHuman.ModularCurve.Defs.PhiGen
import FLTForHuman.ModularCurve.Defs.Cyclotomic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.FieldTheory.Galois.Basic

set_option autoImplicit false

noncomputable section

open PowerSeries HahnSeries Polynomial

namespace ModularCurve
namespace PhiGen

section PermLemma

variable {K : Type*} [Field K] {ℓ : ℕ} {conj : Fin (ℓ + 1) → LaurentSeries K}

private theorem map_phiProd_of_perm (F : LaurentSeries K →+* LaurentSeries K)
    (e : Fin ℓ ≃ Fin ℓ) (h0 : F (conj 0) = conj 0)
    (hS : ∀ b : Fin ℓ, F (conj b.succ) = conj (e b).succ) :
    (phiProd ℓ conj).map F = phiProd ℓ conj := by
  rw [phiProd, Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ, h0]
  congr 1
  calc ∏ b : Fin ℓ, (Polynomial.X - Polynomial.C (F (conj b.succ)))
      = ∏ b : Fin ℓ, (Polynomial.X - Polynomial.C (conj (e b).succ)) := by
        refine Finset.prod_congr rfl fun b _ => ?_
        rw [hS b]
    _ = ∏ b : Fin ℓ, (Polynomial.X - Polynomial.C (conj b.succ)) :=
        e.prod_comp fun b => Polynomial.X - Polynomial.C (conj b.succ)

private theorem map_phiProd_coeff_of_perm (F : LaurentSeries K →+* LaurentSeries K)
    (e : Fin ℓ ≃ Fin ℓ) (h0 : F (conj 0) = conj 0)
    (hS : ∀ b : Fin ℓ, F (conj b.succ) = conj (e b).succ) (k : ℕ) :
    F ((phiProd ℓ conj).coeff k) = (phiProd ℓ conj).coeff k := by
  conv_rhs => rw [← map_phiProd_of_perm F e h0 hS]
  rw [Polynomial.coeff_map]

end PermLemma

section TwistRoot

variable {K : Type*} [Field K] {ℓ : ℕ} {ζ : Kˣ}

private theorem zeta_pow_mod (hζ : IsPrimitiveRoot (ζ : K) ℓ) (n : ℕ) :
    ζ ^ (n % ℓ) = ζ ^ n :=
  (pow_eq_pow_mod n (units_pow_eq_one_of_isPrimitiveRoot hζ)).symm

end TwistRoot

section TwistConj

variable {K : Type*} [Field K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)]
  {conj : Fin (ℓ + 1) → LaurentSeries K} {ζ : Kˣ} {J : LaurentSeries K}

private theorem qTwist_conj_zero (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    (hconj0 : conj 0 = qExpand K (ℓ * ℓ) J) : qTwist ζ (conj 0) = conj 0 := by
  rw [hconj0, qTwist_qExpand]
  congr 1
  rw [zpow_natCast, pow_mul, units_pow_eq_one_of_isPrimitiveRoot hζ, one_pow,
    qTwist_one_apply]

private theorem qTwist_conj_succ (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    (hconjS : ∀ b : Fin ℓ, conj b.succ = qTwist (ζ ^ (b : ℕ)) J) (b : Fin ℓ) :
    qTwist ζ (conj b.succ) = conj ((Equiv.addRight (1 : Fin ℓ)) b).succ := by
  rw [hconjS b, hconjS ((Equiv.addRight (1 : Fin ℓ)) b), qTwist_qTwist]
  congr 1
  simp only [Equiv.coe_addRight]
  have h1 : ((1 : Fin ℓ) : ℕ) = 1 := by
    rw [Fin.val_one']
    exact Nat.mod_eq_of_lt hℓ.out.one_lt
  rw [Fin.val_add, h1, zeta_pow_mod hζ ((b : ℕ) + 1), pow_succ, mul_comm ζ (ζ ^ (b : ℕ))]

end TwistConj

section SupportCollapse

variable {K : Type*} [Field K] {ℓ : ℕ} {ζ : Kˣ}

private theorem coeff_eq_zero_of_qTwist_eq (hζ : IsPrimitiveRoot (ζ : K) ℓ)
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

end SupportCollapse

section Contract

variable {K : Type*} [Field K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)]

private def qContract (f : LaurentSeries K) : LaurentSeries K where
  coeff m := f.coeff ((ℓ : ℤ) * m)
  isPWO_support' := by
    have hsub : (Function.support fun m : ℤ => f.coeff ((ℓ : ℤ) * m)) ⊆
        (fun k : ℤ => k / (ℓ : ℤ)) '' f.support := by
      intro m hm
      refine ⟨(ℓ : ℤ) * m, hm, ?_⟩
      exact Int.mul_ediv_cancel_left m (Nat.cast_ne_zero.mpr hℓ.out.ne_zero)
    exact (f.isPWO_support'.image_of_monotone fun a b hab =>
      Int.ediv_le_ediv (Int.natCast_pos.mpr hℓ.out.pos) hab).mono hsub

private theorem qContract_coeff (f : LaurentSeries K) (m : ℤ) :
    (qContract ℓ f).coeff m = f.coeff ((ℓ : ℤ) * m) := rfl

variable {ℓ}

private theorem qExpand_qContract {f : LaurentSeries K}
    (hf : ∀ m : ℤ, ¬ (ℓ : ℤ) ∣ m → f.coeff m = 0) :
    qExpand K ℓ (qContract ℓ f) = f := by
  ext k
  by_cases hk : (ℓ : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [qExpand_coeff_mul, qContract_coeff]
  · rw [qExpand_coeff_of_not_dvd ℓ _ hk, hf k hk]

private theorem mem_range_qExpand_of_qTwist_eq {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    {f : LaurentSeries K} (hf : qTwist ζ f = f) : f ∈ Set.range (qExpand K ℓ) :=
  ⟨qContract ℓ f, qExpand_qContract fun _ hm => coeff_eq_zero_of_qTwist_eq hζ hf hm⟩

end Contract

section GaloisPerm

variable {K : Type*} [Field K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ}

private theorem exists_galoisPerm (hζ : IsPrimitiveRoot (ζ : K) ℓ) (σ : K →+* K) :
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

end GaloisPerm

section GaloisConj

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- **A Galois automorphism fixes the conjugate at infinity**: `conj 0` is a plain `q`-expansion of
the coefficient field (`conj_zero`), so any `σ` that fixes `coeffEmb K jq` and commutes with
`qExpand` fixes it. No permutation of the finite cusps enters — this is the `h0` hypothesis of
`map_phiProd_coeff_of_perm`, and it holds for every `σ` and every `ℓ`, `ζ` alike. -/
private theorem coeffMap_conj_zero (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) (σ : K ≃ₐ[ℚ] K) :
    coeffMap (σ : K →+* K) (conj ℓ ζ 0) = conj ℓ ζ 0 := by
  calc coeffMap (σ : K →+* K) (conj ℓ ζ 0)
      = coeffMap (σ : K →+* K) (qExpand K (ℓ * ℓ) (coeffEmb K jq)) := by
        rw [conj_zero ℓ ζ]
    _ = qExpand K (ℓ * ℓ) (coeffMap (σ : K →+* K) (coeffEmb K jq)) := by
        rw [coeffMap_qExpand]
    _ = qExpand K (ℓ * ℓ) (coeffEmb K jq) := by
        rw [coeffMap_coeffEmb σ jq]
    _ = conj ℓ ζ 0 := by
        rw [← conj_zero ℓ ζ]

end GaloisConj

section FixedField

variable {K : Type*} [Field K] [Algebra ℚ K]

private theorem mem_range_coeffEmb_of_forall_coeffMap_eq [IsGalois ℚ K] [FiniteDimensional ℚ K]
    {f : LaurentSeries K} (hf : ∀ σ : K ≃ₐ[ℚ] K, coeffMap (σ : K →+* K) f = f) :
    f ∈ Set.range (coeffEmb K) := by
  have hfix : ∀ c : K, (∀ σ : K ≃ₐ[ℚ] K, σ c = c) → ∃ r : ℚ, algebraMap ℚ K r = c :=
    fun c hc => (IsGalois.mem_range_algebraMap_iff_fixed c).mpr hc
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

end FixedField

section Descent

variable {K : Type*} [Field K] [Algebra ℚ K]

private theorem mem_range_coeffEmb_qExpand_of_mem_inter {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)]
    {f : LaurentSeries K} (h1 : f ∈ Set.range (ModularCurve.qExpand K ℓ))
    (h2 : f ∈ Set.range (coeffEmb K)) :
    ∃ g : LaurentSeries ℚ, f = coeffEmb K (ModularCurve.qExpand ℚ ℓ g) := by
  obtain ⟨h, hh⟩ := h2

  have hsupp : ∀ m : ℤ, ¬ (ℓ : ℤ) ∣ m → h.coeff m = 0 := by
    intro m hm
    obtain ⟨g, hg⟩ := h1
    refine FaithfulSMul.algebraMap_injective ℚ K ?_
    rw [map_zero, ← coeffEmb_coeff, hh, ← hg, qExpand_coeff_of_not_dvd ℓ g hm]
  refine ⟨qContract ℓ h, ?_⟩
  rw [qExpand_qContract hsupp]
  exact hh.symm

end Descent

/-- **The coefficients of `phiProd ℓ (conj ℓ ζ)` descend to `ℚ((q))`**: each one is a `q ^ ℓ`
expansion (its support collapses onto multiples of `ℓ`) **and** rational (it is Galois-fixed), so it
lies in the intersection of those two ranges, which is the image of `coeffEmb K ∘ qExpand ℚ ℓ`
(`mem_range_coeffEmb_qExpand_of_mem_inter`); the descent is the choice of the preimage per
coefficient. The statement is the pin wrapper's
`Theorems/Thm_ModularCurve_PhiGen_exists_phiGenDescends.lean`. -/
theorem exists_phiGenDescends {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ)
    [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ)
    [IsGalois ℚ K] [FiniteDimensional ℚ K] (hζ : IsPrimitiveRoot (ζ : K) ℓ) :
    ∃ c : ℕ → LaurentSeries ℚ, PhiGenDescends ℓ ζ c := by
  have hmem : ∀ k : ℕ, ∃ g : LaurentSeries ℚ,
      (phiProd ℓ (conj ℓ ζ)).coeff k = coeffEmb K (qExpand ℚ ℓ g) := by
    intro k
    refine mem_range_coeffEmb_qExpand_of_mem_inter ?_ ?_
    · refine mem_range_qExpand_of_qTwist_eq hζ ?_
      exact map_phiProd_coeff_of_perm (qTwist ζ) (Equiv.addRight (1 : Fin ℓ))
        (qTwist_conj_zero hζ (conj_zero ℓ ζ)) (qTwist_conj_succ hζ (conj_succ ℓ ζ)) k
    · refine mem_range_coeffEmb_of_forall_coeffMap_eq fun σ => ?_
      obtain ⟨e, he⟩ := exists_galoisPerm hζ (σ : K →+* K)
      refine map_phiProd_coeff_of_perm (coeffMap (σ : K →+* K)) e
        (coeffMap_conj_zero ℓ ζ σ) ?_ k
      intro b
      calc coeffMap (σ : K →+* K) (conj ℓ ζ b.succ)
          = coeffMap (σ : K →+* K) (qTwist (ζ ^ (b : ℕ)) (coeffEmb K jq)) := by
            rw [conj_succ ℓ ζ b]
        _ = qTwist (ζ ^ ((e b : Fin ℓ) : ℕ)) (coeffMap (σ : K →+* K) (coeffEmb K jq)) := by
            rw [coeffMap_qTwist (σ : K →+* K) (ζ ^ (b : ℕ)) (ζ ^ ((e b : Fin ℓ) : ℕ))
                (by rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, he b])]
        _ = qTwist (ζ ^ ((e b : Fin ℓ) : ℕ)) (coeffEmb K jq) := by
            rw [coeffMap_coeffEmb σ jq]
        _ = conj ℓ ζ (e b).succ := by
            rw [← conj_succ ℓ ζ (e b)]
  choose c hc using hmem
  exact ⟨c, hc⟩

end PhiGen
end ModularCurve

end

