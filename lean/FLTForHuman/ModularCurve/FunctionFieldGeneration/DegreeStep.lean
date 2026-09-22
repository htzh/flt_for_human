/-
  T16 — the degree of one prime-power step.

  This is the degree half of the strong induction (math/010 §6), three theorems:

  * `finrank_adjoin_jqN_prime_of_not_mem` — the first prime power:
    `[F(j(q^p)) : F] = p + 1` for `jq ∈ F` and `jqN p ∉ F`. The minimal
    polynomial of `jqN p` divides `Φ_p(jq, Y)`, whose `p + 1` roots are cycled by
    the nome twist `qTwistEquiv ζ`; T4's
    `irreducible_of_transitive_ringAut` makes it irreducible, so its degree is
    `Φ_p`'s.
  * `finrank_adjoin_jqN_pow_succ_of_not_mem` — later prime powers:
    `[F(j(q^{p^{k+2}})) : F] = p`. Now `Q = Φ_p(j(q^{p^{k+1}}), Y)` has the root
    `j(q^{p^k}) ∈ F`, so it factors as `(X - j(q^{p^k})) · P` with `deg P = p`;
    the automorphism is no longer the twist but a **coefficient automorphism**
    `coeffMapEquiv τ` (`τ` from a generator of `(ZMod p)ˣ`), which cycles `P`'s
    `p` roots.
  * `relfinrank_full_eq_mul` — the tower dispatcher: the relative degree of one
    full prime-power step is `p + 1` when `a = 0` and `p` otherwise, by the two
    statements above plus `w1_relfinrank_insert`.

  The third is an `Inputs` field, so proving all three takes the conditional
  capstone's debt **5 → 4**.

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  `P2M/Sol/S_ModularCurve_finrank_adjoin_jqN_prime_of_not_mem.lean` (node
  293–344, helpers 268–284),
  `P2M/Sol/S_ModularCurve_finrank_adjoin_jqN_pow_succ_of_not_mem.lean` (node
  563–749, helpers 422–546) and
  `P2M/Sol/S_ModularCurve_relfinrank_full_eq_mul.lean` (node 49–72). All three
  statements are the `Theorems/` wrappers' verbatim.

  ## Dedup

  Most of the first two files is T14's prelude, written once in
  `Defs/PhiAtSlot.lean`/`PhiSlotRoots.lean`/`Defs/TS.lean` and not re-copied
  here. T16 also promotes the transport bridges
  (`coeffMap_qTwist`, `coeffMap_coeffEmb_algHom`, `coeffMap_TS`, `coeffMapEquiv`,
  `iota_injective`, `w1_relfinrank_insert`) to their `Defs/` homes and deletes
  the private twins in `PhiGenDescent.lean`/`PhiGenSplits.lean`/
  `PhiGenIntegrality.lean`. The redundant `coeffEmb_injective'` and the pin's
  `jqN_congr'`/`jqN_congr` are dropped in favour of the existing public
  `coeffEmb_injective` and `jqN_congr`.

  ## Assumptions

  T4's `Polynomial.irreducible_of_transitive_ringAut`; T12's
  `exists_phiIrreducible_evalSymm`; T13's `splits_of_prime`; T14's `phiAtSeed*`,
  `qTwistEquiv`/`_apply`, `qTwist_iota_of_pow_eq_one`, `qTwist_TS_one_cycle`,
  `phiProd`, `roots_phiProd_conj(_nodup)`, `roots_prime_at_slot*`, `iota_jqN`,
  `TS_congr`; the T16 promotions; mathlib's cyclotomic-automorphism API.
-/
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import FLTForHuman.FieldTheory.CommonRoot
import FLTForHuman.ModularCurve.Defs.PhiAtSlot
import FLTForHuman.ModularCurve.PhiSlotRoots
import FLTForHuman.ModularCurve.PhiGenSplits
import FLTForHuman.ModularCurve.ModularPolynomialProperties
import FLTForHuman.ModularCurve.Defs.Fields

set_option autoImplicit false
-- The pin installs the `Algebra F (LaurentSeries K)` instance (via `letI`) and
-- the cyclotomic `IsCyclotomicExtension` instance (via `haveI`); both are
-- consumed by typeclass search, so the style linter's `have` preference does not
-- apply. Same local disable as `PhiGenSplits.lean`/`Descent.lean`.
set_option linter.style.haveILetI false

noncomputable section

open Polynomial HahnSeries IntermediateField

namespace ModularCurve

open PhiGen

variable {K : Type*} [Field K] [Algebra ℚ K]

/-! ## The prime step -/

/-- The level-`p` datum read at the level-`p` nome is the conjugate product:
`phiAtSeed data (coeffEmb K (qExpand ℚ p jq)) = phiProd p (conj p ζ)`, from T13's
`splits_of_prime`. -/
private theorem phiAtSeed_iota_jq_eq_phiProd (p : ℕ) [Fact p.Prime] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) p) (data : ModularPolynomialData p) :
    phiAtSeed data (coeffEmb K (qExpand ℚ p jq)) = phiProd p (conj p ζ) := by
  rw [← PhiGen.splits_of_prime p ζ hζ data, phiAtSeed]
  congr 1
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp [evalAtJ_X]

/-- **The first prime-power degree step**: if `jq ∈ F` and `jqN p ∉ F`, then
`[F(j(q ^ p)) : F] = p + 1`. Verbatim from
`Theorems/Thm_ModularCurve_finrank_adjoin_jqN_prime_of_not_mem.lean`. -/
theorem finrank_adjoin_jqN_prime_of_not_mem (F : IntermediateField ℚ (LaurentSeries ℚ))
    (hj : jq ∈ F) (p : ℕ) [hp : Fact (Nat.Prime p)] (hpF : jqN p ∉ F) :
    Module.finrank F (IntermediateField.adjoin F ({jqN p} : Set (LaurentSeries ℚ))) = p + 1 := by
  classical
  obtain ⟨data, -, -⟩ := exists_phiIrreducible_evalSymm p
  set jF : F := ⟨jq, hj⟩ with hjF
  set P : Polynomial F := phiAtSeed data jF with hP
  have hPmonic : P.Monic := phiAtSeed_monic data jF
  have hPdeg : P.natDegree = p + 1 := by rw [hP, phiAtSeed_natDegree, dedekindPsi_prime hp.out]
  have hPmap : P.map (algebraMap F (LaurentSeries ℚ)) = phiAtSeed data jq := by
    rw [hP, phiAtSeed_map]; rfl
  have hProot : Polynomial.aeval (jqN p) P = 0 := by
    rw [← Polynomial.eval_map_algebraMap, hPmap]
    simpa using phiAtSeed_jqN_eval p data 1
  have hα : IsIntegral F (jqN p) := ⟨P, hPmonic, by rwa [Polynomial.aeval_def] at hProot⟩

  let K := CyclotomicField p ℚ
  let ζ : Kˣ := cycUnit p
  have hζ : IsPrimitiveRoot (ζ : K) p := cycUnit_spec p
  let ι : LaurentSeries ℚ →+* LaurentSeries K := (coeffEmb K).comp (qExpand ℚ p)
  letI : Algebra F (LaurentSeries K) := (ι.comp (algebraMap F (LaurentSeries ℚ))).toAlgebra
  have halg : ∀ a : F, algebraMap F (LaurentSeries K) a = ι a := fun a => rfl

  have hPmapL : P.map (algebraMap F (LaurentSeries K)) = phiProd p (conj p ζ) := by
    rw [RingHom.algebraMap_toAlgebra, ← Polynomial.map_map, hPmap, phiAtSeed_map]
    exact phiAtSeed_iota_jq_eq_phiProd p ζ hζ data

  have hirr : Irreducible P := by
    refine Polynomial.irreducible_of_transitive_ringAut P hPmonic ?_ (qTwistEquiv ζ) ?_ (TS K (p * p) 1)
      (fun b => TS K 1 (ζ ^ b)) p ?_ ?_ ?_ ?_
    · rw [hPmapL, phiProd]
      exact Polynomial.Splits.prod fun i _ => Polynomial.Splits.X_sub_C _
    · intro a
      rw [halg, qTwistEquiv_apply]
      exact qTwist_iota_of_pow_eq_one p ζ (cycUnit_pow p) a
    · rw [hPmapL, roots_phiProd_conj]
    · rw [hPmapL, roots_phiProd_conj]; exact roots_phiProd_conj_nodup p ζ hζ
    · intro i _
      rw [qTwistEquiv_apply]
      exact qTwist_TS_one_cycle ζ (cycUnit_pow p) i
    · rintro ⟨f, hf⟩
      rw [halg] at hf
      have : (f : LaurentSeries ℚ) = jqN p := by
        apply iota_injective (K := K) p
        change ι f = coeffEmb K (qExpand ℚ p (jqN p))
        rw [hf, iota_jqN]
      exact hpF (this ▸ f.2)

  have hmin : P = minpoly F (jqN p) := minpoly.eq_of_irreducible_of_monic hirr hProot hPmonic
  rw [IntermediateField.adjoin.finrank hα, ← hmin, hPdeg]

/-! ## The later prime-power step -/

private def rUnit (e : ℕ) [NeZero e] {p : ℕ} (ζ : Kˣ) (g : (ZMod p)ˣ) (i : ℕ) :
    LaurentSeries K :=
  TS K e (ζ ^ ((g ^ i : (ZMod p)ˣ) : ZMod p).val)

/-- Re-index the `p` roots `TS K e (ζ ^ b)` by the powers of a generator `g` of
`(ZMod p)ˣ`: the `b = 0` root is `TS K e 1` and the remaining `p - 1` are the
`rUnit e ζ g i`. Pure multiset re-indexing, transcribed from the pin. -/
private theorem range_map_eq_rUnit (p : ℕ) [hp : Fact (Nat.Prime p)] (e : ℕ) [NeZero e]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p) (g : (ZMod p)ˣ)
    (hg : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) :
    (Multiset.range p).map (fun b => TS K e (ζ ^ b))
      = TS K e 1 ::ₘ (Multiset.range (p - 1)).map (rUnit e ζ g) := by
  have hp1 : 0 < p - 1 := by have := hp.out.two_le; omega
  have horder : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units p]
  have hg1 : g ^ (p - 1) = 1 := by rw [← horder]; exact pow_orderOf_eq_one g
  have hgmod : ∀ a : ℕ, g ^ a = g ^ (a % (p - 1)) := by
    intro a
    conv_lhs => rw [← Nat.div_add_mod a (p - 1)]
    rw [pow_add, pow_mul, hg1, one_pow, one_mul]
  have hexp : ∀ {a b : ℕ}, a < p → b < p → ζ ^ a = ζ ^ b → a = b := by
    intro a b ha hb h
    refine hζ.pow_inj ha hb ?_
    have h2 := congrArg Units.val h
    rwa [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val] at h2
  have hnd1 : ((Multiset.range p).map (fun b => TS K e (ζ ^ b))).Nodup := by
    refine Multiset.Nodup.map_on ?_ (Multiset.nodup_range p)
    intro a ha b hb h
    rw [Multiset.mem_range] at ha hb
    exact hexp ha hb (TS_injective h).2
  have hnd2 : (TS K e 1 ::ₘ (Multiset.range (p - 1)).map (rUnit e ζ g)).Nodup := by
    rw [Multiset.nodup_cons]
    constructor
    · intro hmem
      rw [Multiset.mem_map] at hmem
      obtain ⟨i, hi, hTS⟩ := hmem
      rw [rUnit] at hTS
      have h0 : ζ ^ ((g ^ i : (ZMod p)ˣ) : ZMod p).val = ζ ^ (0 : ℕ) := by
        rw [pow_zero]
        exact (TS_injective hTS).2
      have he0 : ((g ^ i : (ZMod p)ˣ) : ZMod p).val = 0 :=
        hexp (ZMod.val_lt _) hp.out.pos h0
      have hz : ((g ^ i : (ZMod p)ˣ) : ZMod p) = 0 := by rwa [ZMod.val_eq_zero] at he0
      exact Units.ne_zero (g ^ i) hz
    · refine Multiset.Nodup.map_on ?_ (Multiset.nodup_range (p - 1))
      intro a ha b hb h
      rw [Multiset.mem_range] at ha hb
      rw [rUnit, rUnit] at h
      have hval : ((g ^ a : (ZMod p)ˣ) : ZMod p).val = ((g ^ b : (ZMod p)ˣ) : ZMod p).val :=
        hexp (ZMod.val_lt _) (ZMod.val_lt _) (TS_injective h).2
      have hcoe : ((g ^ a : (ZMod p)ˣ) : ZMod p) = ((g ^ b : (ZMod p)ˣ) : ZMod p) :=
        ZMod.val_injective p hval
      have hgab : (g ^ a : (ZMod p)ˣ) = g ^ b := Units.ext hcoe
      have ha' : a ∈ Set.Iio (orderOf g) := by rw [horder]; exact ha
      have hb' : b ∈ Set.Iio (orderOf g) := by rw [horder]; exact hb
      exact pow_injOn_Iio_orderOf ha' hb' hgab
  rw [Multiset.Nodup.ext hnd1 hnd2]
  intro x
  simp only [Multiset.mem_map, Multiset.mem_range, Multiset.mem_cons]
  constructor
  · rintro ⟨b, hb, rfl⟩
    rcases Nat.eq_zero_or_pos b with rfl | hb0
    · left
      rw [pow_zero]
    · right
      have hbp : ¬ p ∣ b := fun hdvd => absurd (Nat.le_of_dvd hb0 hdvd) (not_le.mpr hb)
      have hcop : Nat.Coprime b p := Nat.coprime_comm.mp (hp.out.coprime_iff_not_dvd.mpr hbp)
      obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp
        ((isOfFinOrder_of_finite g).mem_powers_iff_mem_zpowers.mpr
          (hg (ZMod.unitOfCoprime b hcop)))
      refine ⟨k % (p - 1), Nat.mod_lt _ hp1, ?_⟩
      rw [rUnit, ← hgmod, hk, ZMod.coe_unitOfCoprime, ZMod.val_cast_of_lt hb]
  · rintro (rfl | ⟨i, hi, rfl⟩)
    · exact ⟨0, hp.out.pos, by rw [pow_zero]⟩
    · rw [rUnit]
      exact ⟨((g ^ i : (ZMod p)ˣ) : ZMod p).val, ZMod.val_lt _, rfl⟩

/-- **The later prime-power degree step**: if `jqN (p ^ k)` and
`jqN (p ^ (k + 1))` lie in `F` but `jqN (p ^ (k + 2))` does not, then
`[F(j(q ^ (p ^ (k + 2)))) : F] = p`. The cyclotomic coefficient automorphism
`coeffMapEquiv τ` cycles the `p` roots of the peeled factor. Verbatim from
`Theorems/Thm_ModularCurve_finrank_adjoin_jqN_pow_succ_of_not_mem.lean`. -/
theorem finrank_adjoin_jqN_pow_succ_of_not_mem (F : IntermediateField ℚ (LaurentSeries ℚ))
    (p : ℕ) [hp : Fact (Nat.Prime p)] (k : ℕ) (h0 : jqN (p ^ k) ∈ F)
    (h1 : jqN (p ^ (k + 1)) ∈ F) (hF : jqN (p ^ (k + 2)) ∉ F) :
    Module.finrank F (IntermediateField.adjoin F ({jqN (p ^ (k + 2))} : Set (LaurentSeries ℚ))) = p := by
  classical

  obtain ⟨data, -, hs⟩ := exists_phiIrreducible_evalSymm p
  set jkF : F := ⟨jqN (p ^ k), h0⟩ with hjkF
  set jp1F : F := ⟨jqN (p ^ (k + 1)), h1⟩ with hjp1F
  set Q : Polynomial F := phiAtSeed data jp1F with hQdef
  have hQmonic : Q.Monic := phiAtSeed_monic data jp1F
  have hQdeg : Q.natDegree = p + 1 := by
    rw [hQdef, phiAtSeed_natDegree, dedekindPsi_prime hp.out]
  have hQmap : Q.map (algebraMap F (LaurentSeries ℚ)) = phiAtSeed data (jqN (p ^ (k + 1))) := by
    rw [hQdef, phiAtSeed_map]; rfl

  have hdown : (phiAtSeed data (jqN (p ^ k))).eval (jqN (p ^ (k + 1))) = 0 := by
    have h := phiAtSeed_jqN_eval p data (p ^ k)
    rwa [jqN_congr ((pow_succ p k).symm)] at h
  have hQj : Q.IsRoot jkF := by
    have h0m : algebraMap F (LaurentSeries ℚ) (Q.eval jkF) = algebraMap F (LaurentSeries ℚ) 0 := by
      rw [map_zero, ← Polynomial.eval₂_hom, ← Polynomial.eval_map, hQmap,
        phiAtSeed_eval_symm data hs]
      exact hdown
    exact (algebraMap F (LaurentSeries ℚ)).injective h0m
  set P : Polynomial F := Q /ₘ (Polynomial.X - Polynomial.C jkF) with hPdef
  have hfact : (Polynomial.X - Polynomial.C jkF) * P = Q :=
    Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hQj
  have hPmonic : P.Monic :=
    Polynomial.Monic.of_mul_monic_left (Polynomial.monic_X_sub_C jkF)
      (by rw [hfact]; exact hQmonic)
  have hPdeg : P.natDegree = p := by
    have h := congrArg Polynomial.natDegree hfact
    rw [Polynomial.Monic.natDegree_mul (Polynomial.monic_X_sub_C jkF) hPmonic,
      Polynomial.natDegree_X_sub_C, hQdeg] at h
    omega

  have hQroot : Polynomial.aeval (jqN (p ^ (k + 2))) Q = 0 := by
    rw [← Polynomial.eval_map_algebraMap, hQmap]
    have h := phiAtSeed_jqN_eval p data (p ^ (k + 1))
    rwa [jqN_congr ((pow_succ p (k + 1)).symm)] at h
  have hne2 : jqN (p ^ (k + 2)) ≠ jqN (p ^ k) := by
    intro h
    have hA : (jqN (p ^ (k + 2))).coeff (((p ^ (k + 2) : ℕ) : ℤ) * (-1)) = 1 := by
      rw [jqN, qExpand_coeff_mul]
      exact coeff_jq_neg_one
    have hidx : ((p ^ (k + 2) : ℕ) : ℤ) * (-1)
        = ((p ^ k : ℕ) : ℤ) * (((p * p : ℕ) : ℤ) * (-1)) := by
      push_cast
      ring
    have hB : (jqN (p ^ k)).coeff (((p ^ (k + 2) : ℕ) : ℤ) * (-1)) = 0 := by
      rw [jqN, hidx, qExpand_coeff_mul]
      apply coeff_jq_of_lt
      have h4 : (4 : ℕ) ≤ p * p := Nat.mul_le_mul hp.out.two_le hp.out.two_le
      have h4' : (4 : ℤ) ≤ ((p * p : ℕ) : ℤ) := by exact_mod_cast h4
      linarith
    rw [h] at hA
    rw [hA] at hB
    exact one_ne_zero hB
  have hProot : Polynomial.aeval (jqN (p ^ (k + 2))) P = 0 := by
    have h : Polynomial.aeval (jqN (p ^ (k + 2))) ((Polynomial.X - Polynomial.C jkF) * P) = 0 := by
      rw [hfact]; exact hQroot
    rw [map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C] at h
    rcases mul_eq_zero.mp h with h1' | h2'
    · exact absurd (sub_eq_zero.mp h1') hne2
    · exact h2'
  have hint : IsIntegral F (jqN (p ^ (k + 2))) :=
    ⟨P, hPmonic, by rwa [Polynomial.aeval_def] at hProot⟩

  let K := CyclotomicField p ℚ
  let ζ : Kˣ := cycUnit p
  have hζK : IsPrimitiveRoot (ζ : K) p := cycUnit_spec p
  let ι : LaurentSeries ℚ →+* LaurentSeries K := (coeffEmb K).comp (qExpand ℚ p)
  letI : Algebra F (LaurentSeries K) := (ι.comp (algebraMap F (LaurentSeries ℚ))).toAlgebra
  have halg : ∀ a : F, algebraMap F (LaurentSeries K) a = ι a := fun a => rfl

  have hseed : coeffEmb K (qExpand ℚ p (jqN (p ^ (k + 1))))
      = qExpand K (p * p ^ (k + 1)) (qTwist ((1 : Kˣ) ^ p) (coeffEmb K jq)) := by
    have h2 : TS K (p * p ^ (k + 1)) 1 = TS K (p * p ^ (k + 1)) ((1 : Kˣ) ^ p) := by
      rw [one_pow]
    exact (iota_jqN p (p ^ (k + 1))).trans h2
  have hQmapL : Q.map (algebraMap F (LaurentSeries K))
      = phiAtSeed data (qExpand K (p * p ^ (k + 1)) (qTwist ((1 : Kˣ) ^ p) (coeffEmb K jq))) := by
    rw [RingHom.algebraMap_toAlgebra, ← Polynomial.map_map, hQmap, phiAtSeed_map]
    exact congrArg (phiAtSeed data) hseed
  have hQroots : (Q.map (algebraMap F (LaurentSeries K))).roots
      = TS K (p * (p * p ^ (k + 1))) 1
        ::ₘ (Multiset.range p).map (fun b => TS K (p ^ (k + 1)) (ζ ^ b)) := by
    rw [hQmapL, phiAtSeed, roots_prime_at_slot p ζ hζK p (dvd_refl p) data (p ^ (k + 1)) 1]
    congr 1
    · show TS K (p * (p * p ^ (k + 1))) ((1 : Kˣ) ^ (p * p))
        = TS K (p * (p * p ^ (k + 1))) 1
      rw [one_pow]
    · show (Multiset.range p).map (fun b => TS K (p ^ (k + 1)) ((1 : Kˣ) * ζ ^ (b * (p / p))))
        = (Multiset.range p).map (fun b => TS K (p ^ (k + 1)) (ζ ^ b))
      refine Multiset.map_congr rfl fun b _ => ?_
      rw [Nat.div_self hp.out.pos, mul_one, one_mul]
  have hQnodup : (Q.map (algebraMap F (LaurentSeries K))).roots.Nodup := by
    rw [hQmapL, phiAtSeed]
    exact roots_prime_at_slot_roots_nodup p ζ hζK p (dvd_refl p) data (p ^ (k + 1)) 1

  have hjL : algebraMap F (LaurentSeries K) jkF = TS K (p ^ (k + 1)) 1 :=
    (iota_jqN p (p ^ k)).trans (TS_congr (pow_succ' p k).symm 1)
  have hQPmapL : Q.map (algebraMap F (LaurentSeries K))
      = (Polynomial.X - Polynomial.C (TS K (p ^ (k + 1)) 1))
        * P.map (algebraMap F (LaurentSeries K)) := by
    rw [← hfact, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hjL]
  have hQm0 : Q.map (algebraMap F (LaurentSeries K)) ≠ 0 := (hQmonic.map _).ne_zero
  have hsum : (Q.map (algebraMap F (LaurentSeries K))).roots
      = TS K (p ^ (k + 1)) 1 ::ₘ (P.map (algebraMap F (LaurentSeries K))).roots := by
    rw [hQPmapL, Polynomial.roots_mul (hQPmapL ▸ hQm0), Polynomial.roots_X_sub_C,
      Multiset.singleton_add]

  haveI : IsCyclotomicExtension {p} ℚ K := CyclotomicField.isCyclotomicExtension p ℚ
  have hirrcyc : Irreducible (Polynomial.cyclotomic p ℚ) :=
    Polynomial.cyclotomic.irreducible_rat hp.out.pos
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hp1 : 0 < p - 1 := by have := hp.out.two_le; omega
  have horder : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units p]
  have hg1 : g ^ (p - 1) = 1 := by rw [← horder]; exact pow_orderOf_eq_one g
  have hgmod : ∀ a : ℕ, g ^ a = g ^ (a % (p - 1)) := by
    intro a
    conv_lhs => rw [← Nat.div_add_mod a (p - 1)]
    rw [pow_add, pow_mul, hg1, one_pow, one_mul]
  have hsurj : Function.Surjective (hζK.autToPow ℚ) :=
    ((Nat.bijective_iff_injective_and_card _).mpr
      ⟨hζK.autToPow_injective (K := ℚ),
        Nat.card_congr (IsCyclotomicExtension.autEquivPow K hirrcyc).toEquiv⟩).2
  obtain ⟨τ, hτ⟩ := hsurj g
  have hτζ : τ (ζ : K) = (ζ : K) ^ ((g : ZMod p)).val := by
    have h := hζK.autToPow_spec ℚ τ
    rw [hτ] at h
    exact h.symm
  have hτζu : Units.map ((τ : K →ₐ[ℚ] K) : K →+* K).toMonoidHom ζ = ζ ^ ((g : ZMod p)).val :=
    Units.ext (by rw [Units.coe_map, Units.val_pow_eq_pow_val]; exact hτζ)
  have hζp1 : ζ ^ p = 1 := cycUnit_pow p
  have hζmod : ∀ a : ℕ, ζ ^ a = ζ ^ (a % p) := by
    intro a
    conv_lhs => rw [← Nat.div_add_mod a p]
    rw [pow_add, pow_mul, hζp1, one_pow, one_mul]
  have hstep : ∀ i : ℕ,
      coeffMapEquiv τ (rUnit (p ^ (k + 1)) ζ g i) = rUnit (p ^ (k + 1)) ζ g (i + 1) := by
    intro i
    rw [rUnit, rUnit, coeffMapEquiv_apply, coeffMap_TS (τ : K →ₐ[ℚ] K)]
    congr 1
    rw [map_pow, hτζu, ← pow_mul,
      hζmod (((g : ZMod p)).val * ((g ^ i : (ZMod p)ˣ) : ZMod p).val)]
    congr 1
    rw [pow_succ', Units.val_mul, ZMod.val_mul]

  have hreidx := range_map_eq_rUnit p (p ^ (k + 1)) ζ hζK g hg
  have hProots : (P.map (algebraMap F (LaurentSeries K))).roots
      = TS K (p * (p * p ^ (k + 1))) 1
        ::ₘ (Multiset.range (p - 1)).map (rUnit (p ^ (k + 1)) ζ g) := by
    have h := hsum.symm.trans hQroots
    rw [hreidx, Multiset.cons_swap] at h
    exact (Multiset.cons_inj_right _).mp h
  have hPnodup : (P.map (algebraMap F (LaurentSeries K))).roots.Nodup := by
    rw [hsum] at hQnodup
    exact (Multiset.nodup_cons.mp hQnodup).2
  have hPsplits : (P.map (algebraMap F (LaurentSeries K))).Splits := by
    rw [Polynomial.splits_iff_card_roots, hProots, Multiset.card_cons, Multiset.card_map,
      Multiset.card_range, hPmonic.natDegree_map, hPdeg]
    have := hp.out.two_le
    omega

  have hirr : Irreducible P := by
    refine Polynomial.irreducible_of_transitive_ringAut P hPmonic hPsplits (coeffMapEquiv τ) ?_
      (TS K (p * (p * p ^ (k + 1))) 1) (rUnit (p ^ (k + 1)) ζ g) (p - 1) hProots hPnodup ?_ ?_
    · intro a
      rw [halg, coeffMapEquiv_apply]
      exact coeffMap_coeffEmb_algHom (τ : K →ₐ[ℚ] K) (qExpand ℚ p (a : LaurentSeries ℚ))
    · intro i hi
      rw [hstep i, rUnit, rUnit]
      exact congrArg (fun u : (ZMod p)ˣ => TS K (p ^ (k + 1)) (ζ ^ ((u : ZMod p)).val))
        (hgmod (i + 1))
    · rintro ⟨f, hf⟩
      rw [halg] at hf
      have hval : (f : LaurentSeries ℚ) = jqN (p ^ (k + 2)) := by
        apply iota_injective (K := K) p
        change ι (f : LaurentSeries ℚ) = coeffEmb K (qExpand ℚ p (jqN (p ^ (k + 2))))
        rw [hf, iota_jqN]
        exact TS_congr (congrArg (p * ·) (pow_succ' p (k + 1)).symm) 1
      exact hF (hval ▸ f.2)

  have hmin : P = minpoly F (jqN (p ^ (k + 2))) :=
    minpoly.eq_of_irreducible_of_monic hirr hProot hPmonic
  rw [IntermediateField.adjoin.finrank hint, ← hmin, hPdeg]

/-! ## The tower dispatcher -/

/-- **The one-step relative degree**: for a full prime-power step
`F_n = ℚ(j(q ^ d) : d ∣ n)`, the relative degree of
`F_{M p ^ (a + 1)}` over `F_{M p ^ a}` is `p + 1` when `a = 0` and `p`
otherwise. Verbatim from
`Theorems/Thm_ModularCurve_relfinrank_full_eq_mul.lean`. -/
theorem relfinrank_full_eq_mul (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)] (a : ℕ)
    (hup : modularFunctionFieldFull (M * p ^ (a + 1)) =
      IntermediateField.adjoin ℚ
        (insert (jqN (p ^ (a + 1))) (modularFunctionFieldFull (M * p ^ a) :
          Set (LaurentSeries ℚ))))
    (hnm : jqN (p ^ (a + 1)) ∉ modularFunctionFieldFull (M * p ^ a)) :
    IntermediateField.relfinrank (modularFunctionFieldFull (M * p ^ a))
      (modularFunctionFieldFull (M * p ^ (a + 1))) = if a = 0 then p + 1 else p := by
  rw [hup, w1_relfinrank_insert]
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [ite_eq_left rfl]
    have e1 : p ^ (0 + 1) = p := by rw [zero_add, pow_one]
    have hj : jq ∈ modularFunctionFieldFull (M * p ^ 0) := by
      have h1 := jqd_mem_full (M * p ^ 0) (one_dvd _)
      rwa [qExpand_one_apply] at h1
    rw [jqN_congr e1]
    rw [jqN_congr e1] at hnm
    exact finrank_adjoin_jqN_prime_of_not_mem _ hj p hnm
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
    rw [ite_eq_right (Nat.succ_ne_zero k)]
    refine finrank_adjoin_jqN_pow_succ_of_not_mem _ p k ?_ ?_ hnm
    · exact jqd_mem_full _ (Dvd.dvd.mul_left (pow_dvd_pow p (Nat.le_succ k)) M)
    · exact jqd_mem_full _ (dvd_mul_left _ _)

end ModularCurve

end
