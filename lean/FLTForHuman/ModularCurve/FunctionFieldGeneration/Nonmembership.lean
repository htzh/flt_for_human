/-
  T17-a — the two non-membership facts the strong induction consumes.

  Both are side conditions on the induction's prime-power step — neither partakes in
  the step's structure — which is why they are stated together, and upstream of it:

  * `jqN_prime_not_mem_full` — `j(q ^ p) ∉ F_M^full` for `p ∤ M`, from `Hall M`.
    The proof reads the `ψ(M)` slot roots off the slot product, writes
    `j(q ^ p) = g(j(q ^ M))` with `deg g < ψ(M)`, shows `g` constant on the slots
    (T4's `mem_range_of_eval_eq_const`), so `j(q ^ p) ∈ ℚ(j)`, contradicting
    T16's `[ℚ(j)(j(q ^ p)) : ℚ(j)] = p + 1`.
  * `jqN_pow_not_mem_adjoin_full` — the **prime-power tower**:
    `j(q ^ (p ^ (a + 2))) ∉ ℚ(F_M^full, j(q ^ p), …, j(q ^ (p ^ (a + 1))))`. The proof
    builds the tower of intermediate fields
    `C_i = ℚ(F_M^full, j(q ^ (p ^ j)) : j ≤ i)` and, by strong induction on `a`, a
    compatible family of `ℚ`-algebra homs `σ_i : C_i → K((q))` whose images lie in a
    shrinking `qExpand` range. The modular equation `Φ_p` has both
    `j(q ^ (p ^ (a + 2)))` and `j(q ^ (p ^ a))` as roots of `Φ_p(j(q ^ (p ^ (a + 1))), ·)`;
    pushing it through `σ` forces both to the *same* root, and `σ` injective gives
    `j(q ^ (p ^ (a + 2))) = j(q ^ (p ^ a))`, contradicted by the `q ^ (-(p ^ a))`
    coefficient (1 vs 0).

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  `P2M/Sol/S_ModularCurve_jqN_prime_not_mem_full.lean` and
  `P2M/Sol/S_ModularCurve_jqN_pow_not_mem_adjoin_full.lean` (node 443–985; lines 400–442
  are T14's helpers). `jqN_pow_not_mem_adjoin_full` states its wrapper's text verbatim;
  `jqN_prime_not_mem_full` takes `Hall M` where the wrapper spells the induction's
  hypothesis out — the same hypothesis, and the retirement is recorded in
  `spec/decl_markers.tsv`.

  ## Homing

  The pin splits the non-membership over three files, and two of them carry a verbatim
  copy of the slot machinery (`rval_aux` at
  `S_ModularCurve_jqN_prime_not_mem_full.lean:832`, and again in the tower file). The port
  writes that machinery once, in `SlotProduct.lean`, and keeps here the two facts the
  induction consumes; the third pin statement, the public two-prime separation, consumes
  T16 and so is downstream, in `TwoPrimeSeparation.lean`. This ordering is what lets
  `DegreeStep.relfinrank_full_eq_mul` derive its non-membership hypothesis instead of
  demanding it from the caller.

  ## Dedup

  The non-membership section uses nine helpers of the slot machinery, exported by
  `SlotProduct.lean` for it (`slots`, `sv`, `sv_eq_TS`, `mem_adjoin_jqN_of_mem_mff`,
  `map_qExpand_minpoly_eq`, `nodup_slotValues_qExpand`, `isIntegral_adjoin_jqN`,
  `natDegree_minpoly_jqN`, `minpoly_jqN_map_eq_prod_slots`); the pin has them `private`
  only because it re-proves them per file. Nothing of T14's prelude is re-copied here.
  The pin's `set_option maxHeartbeats 3200000 in` are omitted — below the port's global
  4000000.

  ## Assumptions

  `SlotProduct`'s slot machinery; T4's `mem_range_of_eval_eq_const`
  (`FieldTheory/CommonRoot`); T12's `exists_phiIrreducible_evalSymm`; T13's
  `splits_prime_at_slot`; T14's `phiAtSeed*`, `isRoot_prime_at_slot_iff`,
  `roots_prime_at_slot*`, `iota_jq`, `iota_jqN`, `TS_congr`,
  `qExpand_qTwist_notMem_range_qExpand` (which also kills the twist branch of the level-`p`
  dichotomy at the top of the tower — `TS_injective` is no longer needed here); T16's
  `finrank_adjoin_jqN_prime_of_not_mem` and
  `finrank_adjoin_jqN_eq_of_prime`; T18's `gen_prime`; `Defs/Laurent`'s
  `coeffMap_injective`/`qExpand_injective`; `Defs/Cyclotomic`'s `cycUnit`/`cycUnit_spec`;
  `Defs/Fields`'s `modularFunctionFieldFull`/`jqd_mem_full`; `Defs/Jq`'s
  `coeff_jq_neg_one`/`jqN_one`/`jqN_congr`.
  spec-pin: Theorems/Thm_ModularCurve_jqN_prime_not_mem_full.lean
  spec-pin: Theorems/Thm_ModularCurve_jqN_pow_not_mem_adjoin_full.lean
-/
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import FLTForHuman.FieldTheory.CommonRoot
import FLTForHuman.ModularCurve.Defs.Laurent
import FLTForHuman.ModularCurve.Defs.PhiAtSlot
import FLTForHuman.ModularCurve.Defs.TS
import FLTForHuman.ModularCurve.Defs.Cyclotomic
import FLTForHuman.ModularCurve.Defs.Fields
import FLTForHuman.ModularCurve.Defs.Invariants
import FLTForHuman.ModularCurve.Defs.Jq
import FLTForHuman.ModularCurve.PhiSlotRoots
import FLTForHuman.ModularCurve.PhiGenSplits
import FLTForHuman.ModularCurve.ModularPolynomialProperties
import FLTForHuman.ModularCurve.ModularPolynomialUniqueness
import FLTForHuman.ModularCurve.FunctionFieldGeneration.SlotProduct

set_option autoImplicit false
-- The pin installs the `Algebra ℚ⟮jq⟯ (LaurentSeries K)` instance (via `letI`) and uses
-- `haveI` for various `NeZero`/`Fact` instances; they are consumed by typeclass search, so
-- the style linter's `have` preference does not apply. Same local disable as
-- `SlotProduct.lean`/`DegreeStep.lean`.
set_option linter.style.haveILetI false

noncomputable section

open Polynomial HahnSeries IntermediateField

-- The `algebraAdjoinAdjoin` scoped instances are what make the `Module.Free`/
-- `IsFractionRing` search on the adjoin towers cheap; the pin's `p2m_open` activated them.
open scoped IntermediateField.algebraAdjoinAdjoin

namespace ModularCurve

open PhiGen

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- **The expanded slots are distinct**: applying `qExpand K p` to the `ζ ^ p`-slots keeps
them distinct, `qExpand K p` being injective. -/
private theorem nodup_slotValues_qExpand {M p : ℕ} [NeZero p] {ζ : Kˣ} (hM0 : M ≠ 0)
    (hζ : IsPrimitiveRoot ((ζ ^ p : Kˣ) : K) M) :
    (slotValues M (fun a b => qExpand K p (sv K (ζ ^ p) a b))).Nodup := by
  refine nodup_slotValues fun a b a' b' ha ha' hb hb' h => ?_
  exact sv_inj_slot hζ hM0 (Nat.mem_divisors.mp ha).1 (Nat.mem_divisors.mp ha').1
    (Finset.mem_range.mp (Finset.mem_filter.mp hb).1)
    (Finset.mem_range.mp (Finset.mem_filter.mp hb').1)
    (RingHom.injective (qExpand K p) h)

/-! ## The `M`-arbitrary non-membership

`j(q ^ p) ∉ F_M^full` for `p ∤ M`, from `Hall M`. The `Hall` at `d = p` uses
T18's `gen_prime` (and `tight_one`/`gen_one` at `d = 1`) instead of the pin's
`functionFieldGeneration_of_squarefree p`, so no squarefree-block declaration is
pulled in; `mem_range_of_eval_eq_const` is T4's engine from
`FieldTheory/CommonRoot.lean`, not restated.

The slot product at `M` for the primitive root `ζ ^ p` gives the `ψ(M)` roots of the
pushed minimal polynomial, and they are exactly the `ψ(M)` distinct slot values
(`hroots`). Reading `j(q ^ p) = g (j(q ^ M))` with `deg g < ψ(M)`, the polynomial `g`
is constant on those slots (`eval_map_eq_of_mem_slotValues`), so its value lies in the
image of `(coeffEmb K).comp (qExpand ℚ (M * p))` (`mem_range_of_eval_eq_const`), which
forces `j(q ^ p)` into the base field. -/

section NonMem0

open IntermediateField

/-- **A conjugate maps the adjoin into the `qExpand K p`-image**: if `y` lies in the image of
`qExpand K p`, the push of scalars along `ψy` is the `coeffEmb` map, and
`qExpand K p` of a `coeffEmb`-image is a `coeffEmb`-image (`hιS`), then `ψy` sends *every*
element of `ℚ⟮jq⟯⟮jqN M⟯` into that image. The induction is over the simple extension. -/
private theorem map_mem_fieldRange {M p : ℕ} [NeZero M] [NeZero p] {y : LaurentSeries K}
    [Algebra ℚ⟮jq⟯ (LaurentSeries K)]
    {ψy : ℚ⟮jq⟯⟮jqN M⟯ →ₐ[ℚ⟮jq⟯] LaurentSeries K}
    (hψgen : ∀ h : jqN M ∈ IntermediateField.adjoin ℚ⟮jq⟯ ({jqN M} : Set (LaurentSeries ℚ)),
      ψy ⟨jqN M, h⟩ = y)
    (hyS : y ∈ (qExpand K p).fieldRange)
    (hιS : ∀ w : LaurentSeries ℚ, coeffEmb K (qExpand ℚ (M * p) w)
      = qExpand K p (coeffEmb K (qExpand ℚ M w)))
    (halg : algebraMap ℚ⟮jq⟯ (LaurentSeries K)
      = ((coeffEmb K).comp (qExpand ℚ (M * p))).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ))) :
    ∀ (x : LaurentSeries ℚ)
      (hx : x ∈ IntermediateField.adjoin ℚ⟮jq⟯ ({jqN M} : Set (LaurentSeries ℚ))),
      ψy ⟨x, hx⟩ ∈ (qExpand K p).fieldRange := by
  intro x hx
  induction hx using IntermediateField.adjoin_induction with
  | mem z hz =>
      rw [Set.mem_singleton_iff] at hz
      subst hz
      rw [hψgen]
      exact hyS
  | algebraMap z =>
      show ψy (algebraMap ℚ⟮jq⟯ ℚ⟮jq⟯⟮jqN M⟯ z) ∈ (qExpand K p).fieldRange
      rw [AlgHom.commutes, halg]
      show coeffEmb K (qExpand ℚ (M * p)
        ((algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)) z)) ∈ (qExpand K p).fieldRange
      rw [hιS]
      exact RingHom.mem_fieldRange.mpr ⟨_, rfl⟩
  | add x₁ x₂ hx₁ hx₂ ih₁ ih₂ =>
      show ψy ⟨x₁ + x₂, add_mem hx₁ hx₂⟩ ∈ (qExpand K p).fieldRange
      rw [show (⟨x₁ + x₂, add_mem hx₁ hx₂⟩ : ℚ⟮jq⟯⟮jqN M⟯)
        = ⟨x₁, hx₁⟩ + ⟨x₂, hx₂⟩ from rfl, map_add]
      exact Subfield.add_mem _ ih₁ ih₂
  | mul x₁ x₂ hx₁ hx₂ ih₁ ih₂ =>
      show ψy ⟨x₁ * x₂, mul_mem hx₁ hx₂⟩ ∈ (qExpand K p).fieldRange
      rw [show (⟨x₁ * x₂, mul_mem hx₁ hx₂⟩ : ℚ⟮jq⟯⟮jqN M⟯)
        = ⟨x₁, hx₁⟩ * ⟨x₂, hx₂⟩ from rfl, map_mul]
      exact Subfield.mul_mem _ ih₁ ih₂
  | inv x₁ hx₁ ih₁ =>
      show ψy ⟨x₁⁻¹, inv_mem hx₁⟩ ∈ (qExpand K p).fieldRange
      rw [show (⟨x₁⁻¹, inv_mem hx₁⟩ : ℚ⟮jq⟯⟮jqN M⟯)
        = (⟨x₁, hx₁⟩ : ℚ⟮jq⟯⟮jqN M⟯)⁻¹ from rfl, map_inv₀]
      exact Subfield.inv_mem _ ih₁
/-- **The `Hall` hypothesis at the prime `p`**: `Hall p`, i.e. for each divisor `d` of `p` the
degree and function-field conditions hold — `tight_one`/`gen_one` at `d = 1`, and
`finrank_adjoin_jqN_eq_of_prime`/`gen_prime` at `d = p`. -/
private theorem hall_prime (p : ℕ) [hp : Fact (Nat.Prime p)] : Hall p := by
  intro d hd _
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp.out d hd) with h1 | h2
  · subst h1
    exact ⟨tight_one, gen_one⟩
  · have h2' := h2.symm
    subst h2'
    constructor
    · unfold Tight
      rw [dedekindPsi_prime hp.out]
      exact finrank_adjoin_jqN_eq_of_prime p
    · exact gen_prime p

/-- **The distinguished slot.** Of the slots of the level-`p` equation over `ζ ^ M`, the only one
lying in the image of `qExpand K p` is the distinguished slot, `(α, β) = (p, 0)`, whose value is
`j(q ^ p)` read at the level-`M * p` nome. The branch `α = 1` dies because a `qExpand K p`-value
has no `q ^ (-M)` coefficient (`p ∤ M`) while the `ζ ^ M`-slot at `α = 1` has a unit one; the branch
`α = p` forces `β = 0` from `β < p / p`. -/
private theorem eq_seed_of_mem_slotValues_of_mem_fieldRange {M p : ℕ} [NeZero M] [NeZero p]
    [hp : Fact (Nat.Prime p)] {ζ : Kˣ} (hpM : ¬ p ∣ M)
    {y : LaurentSeries K}
    (hy : y ∈ slotValues p (fun α β => qExpand K M (sv K (ζ ^ M) α β)))
    (hyr : y ∈ (qExpand K p).fieldRange) :
    y = coeffEmb K (qExpand ℚ (M * p) (jqN p)) := by
  obtain ⟨α, β, hαmem, hβmem, hβ0⟩ := mem_slotValues.mp hy
  obtain ⟨hαdvd, -⟩ := Nat.mem_divisors.mp hαmem
  obtain ⟨hβr, -⟩ := Finset.mem_filter.mp hβmem
  rw [Finset.mem_range] at hβr
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp.out α hαdvd) with hα1 | hα2
  ·
    -- `α = 1`: the slot is `TS K M (ζ ^ (M * β))`, whose `-(M)`-coefficient is a unit,
    -- but any value in the image of `qExpand K p` vanishes there (`p ∤ M`).
    subst hα1
    exfalso
    haveI : NeZero (1 : ℕ) := ⟨one_ne_zero⟩
    have hv1 : qExpand K M (sv K (ζ ^ M) 1 β) = TS K M ((ζ ^ M) ^ (β * 1)) := by
      rw [sv_eq_TS, qExpand_TS]
      exact TS_congr' (by ring) rfl
    obtain ⟨w, hw⟩ := RingHom.mem_fieldRange.mp hyr
    have hw2 : qExpand K p w = TS K M ((ζ ^ M) ^ (β * 1)) := by
      rw [hw, hβ0, hv1]
    have hnd : ¬ ((p : ℤ) ∣ (-(M : ℤ))) := by
      rw [dvd_neg, Int.natCast_dvd_natCast]
      exact hpM
    have hz1 : (qExpand K p w).coeff (-(M : ℤ)) = 0 :=
      qExpand_coeff_of_not_dvd (R := K) (N := p) w hnd
    have hz2 : (TS K M ((ζ ^ M) ^ (β * 1))).coeff (-(M : ℤ))
        = ((((ζ ^ M) ^ (β * 1))⁻¹ : Kˣ) : K) :=
      TS_coeff_neg M _
    rw [hw2, hz2] at hz1
    exact Units.ne_zero _ hz1
  ·
    -- `α = p`, `β = 0`: the slot is the distinguished one.
    have hα2' := hα2.symm
    subst hα2'
    have hβ0' : β = 0 := by
      have h3 : p / p = 1 := Nat.div_self hp.out.pos
      omega
    subst hβ0'
    have hsp : qExpand K M (sv K (ζ ^ M) p 0) = coeffEmb K (qExpand ℚ (M * p) (jqN p)) := by
      rw [sv_eq_TS, qExpand_TS, iota_jqN (M * p) p]
      exact TS_congr' (by ring) (by rw [zero_mul, pow_zero])
    rw [hβ0, hsp]

/-- **`g` is constant on the slots**: if `j(q ^ p)` lies in `ℚ⟮jq⟯⟮jqN M⟯` and is
represented there by a polynomial `g'` (`hg'`), then `g'` takes the same value
`coeffEmb K (qExpand ℚ (M * p) (jqN p))` at every slot of the `ζ ^ p`-slot product. The
proof evaluates `g'` through a conjugate `ψy` at each slot `y`; `ψy` maps the whole field
into the image of `qExpand K p`, where the `Φ_p`-factorisation pins the value down. The
`Algebra` instance and `halg` are the pin's `letI`: the `(coeffEmb K ∘ qExpand ℚ (M * p))`
push of scalars. -/
private theorem eval_map_eq_of_mem_slotValues {M p : ℕ} [NeZero M] [NeZero p]
    [hp : Fact (Nat.Prime p)] {ζ : Kˣ} (hpM : ¬ p ∣ M)
    (hζ : IsPrimitiveRoot ((ζ : Kˣ) : K) (M * p))
    (hα : IsIntegral ℚ⟮jq⟯ (jqN M))
    (hroots : ((minpoly ℚ⟮jq⟯ (jqN M)).map (((coeffEmb K).comp (qExpand ℚ (M * p))).comp
        (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))).roots
      = slotValues M (fun a b => qExpand K p (sv K (ζ ^ p) a b)))
    (hmem : jqN p ∈ IntermediateField.adjoin ℚ⟮jq⟯ ({jqN M} : Set (LaurentSeries ℚ)))
    [Algebra ℚ⟮jq⟯ (LaurentSeries K)]
    (halg : algebraMap ℚ⟮jq⟯ (LaurentSeries K)
      = ((coeffEmb K).comp (qExpand ℚ (M * p))).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))
    {g' : Polynomial ℚ⟮jq⟯}
    (hg' : Polynomial.aeval (jqN M) g' = jqN p)
    {y : LaurentSeries K}
    (hy : y ∈ slotValues M (fun a b => qExpand K p (sv K (ζ ^ p) a b))) :
    Polynomial.aeval y g' = coeffEmb K (qExpand ℚ (M * p) (jqN p)) := by
  have hM0 : M ≠ 0 := NeZero.ne M
  have hp0 : p ≠ 0 := hp.out.ne_zero
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero hM0 hp0⟩
  have hζM : IsPrimitiveRoot ((ζ ^ p : Kˣ) : K) M := by
    have h1 := isPrimitiveRoot_pow_div hζ (⟨p, rfl⟩ : M ∣ M * p)
    have h2 : M * p / M = p := Nat.mul_div_cancel_left p (Nat.pos_of_ne_zero hM0)
    rwa [h2] at h1
  have hζp : IsPrimitiveRoot ((ζ ^ M : Kˣ) : K) p := by
    have h1 := isPrimitiveRoot_pow_div hζ (⟨M, Nat.mul_comm M p⟩ : p ∣ M * p)
    have h2 : M * p / p = M := Nat.mul_div_cancel M (Nat.pos_of_ne_zero hp0)
    rwa [h2] at h1
  have hιS : ∀ w : LaurentSeries ℚ, coeffEmb K (qExpand ℚ (M * p) w)
      = qExpand K p (coeffEmb K (qExpand ℚ M w)) := by
    intro w
    rw [← coeffEmb_qExpand, qExpand_qExpand]
    exact congrArg (coeffEmb K) (qExpand_congr (Nat.mul_comm M p) w)
  have hidpB := map_qExpand_minpoly_eq M rfl (ζ ^ M)
    (minpoly_jqN_map_eq_prod_slots p (ζ ^ M) hζp (hall_prime p))
  obtain ⟨a₀, b₀, ha₀, hb₀, hyval⟩ := mem_slotValues.mp hy
  have hyS : y ∈ (qExpand K p).fieldRange := by
    rw [hyval]
    exact RingHom.mem_fieldRange.mpr ⟨sv K (ζ ^ p) a₀ b₀, rfl⟩
  have hy_ar : y ∈ (minpoly ℚ⟮jq⟯ (jqN M)).aroots (LaurentSeries K) := by
    rw [Polynomial.aroots_def, halg, hroots]
    exact hy
  obtain ⟨ψy, hψy⟩ : ∃ ψy : ℚ⟮jq⟯⟮jqN M⟯ →ₐ[ℚ⟮jq⟯] LaurentSeries K,
      ψy (IntermediateField.AdjoinSimple.gen ℚ⟮jq⟯ (jqN M)) = y :=
    ⟨(IntermediateField.algHomAdjoinIntegralEquiv ℚ⟮jq⟯ hα).symm ⟨y, hy_ar⟩,
      IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen ℚ⟮jq⟯ hα ⟨y, hy_ar⟩⟩
  have hψgen : ∀ h : jqN M ∈ IntermediateField.adjoin ℚ⟮jq⟯
      ({jqN M} : Set (LaurentSeries ℚ)), ψy ⟨jqN M, h⟩ = y := by
    intro h
    exact hψy
  have himg := map_mem_fieldRange (K := K) hψgen hyS hιS halg
  have hx_pS : ψy ⟨jqN p, hmem⟩ ∈ (qExpand K p).fieldRange := himg _ hmem
  have hx_proot : ((minpoly ℚ⟮jq⟯ (jqN p)).map (((coeffEmb K).comp
      (qExpand ℚ (M * p))).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))).IsRoot
      (ψy ⟨jqN p, hmem⟩) := by
    have h1 : Polynomial.aeval (⟨jqN p, hmem⟩ : ℚ⟮jq⟯⟮jqN M⟯)
        (minpoly ℚ⟮jq⟯ (jqN p)) = 0 := by
      refine aeval_intermediateField_eq_zero ?_
      show Polynomial.aeval (jqN p) (minpoly ℚ⟮jq⟯ (jqN p)) = 0
      exact minpoly.aeval _ _
    have h2 := Polynomial.aeval_algHom_apply ψy (⟨jqN p, hmem⟩ : ℚ⟮jq⟯⟮jqN M⟯)
      (minpoly ℚ⟮jq⟯ (jqN p))
    rw [h1, map_zero] at h2
    rw [Polynomial.aeval_def, halg, Polynomial.eval₂_eq_eval_map] at h2
    exact h2
  -- Unpack the root of the level-`p` factorisation into a slot membership.
  rw [hidpB, Polynomial.IsRoot, Polynomial.eval_prod] at hx_proot
  obtain ⟨α, hαmem, hα0⟩ := Finset.prod_eq_zero_iff.mp hx_proot
  rw [Polynomial.eval_prod] at hα0
  obtain ⟨β, hβmem, hβ0⟩ := Finset.prod_eq_zero_iff.mp hα0
  rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hβ0
  have hy_slot : ψy ⟨jqN p, hmem⟩
      ∈ slotValues p (fun α β => qExpand K M (sv K (ζ ^ M) α β)) :=
    mem_slotValues.mpr ⟨α, β, hαmem, hβmem, hβ0⟩
  have hx_pval : ψy ⟨jqN p, hmem⟩ = coeffEmb K (qExpand ℚ (M * p) (jqN p)) :=
    eq_seed_of_mem_slotValues_of_mem_fieldRange (K := K) hpM hy_slot hx_pS
  have hgE : Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ⟮jq⟯ (jqN M)) g'
      = (⟨jqN p, hmem⟩ : ℚ⟮jq⟯⟮jqN M⟯) := by
    have h3 := Polynomial.aeval_algHom_apply (IntermediateField.val ℚ⟮jq⟯⟮jqN M⟯)
      (IntermediateField.AdjoinSimple.gen ℚ⟮jq⟯ (jqN M)) g'
    refine Subtype.ext ?_
    show ((Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ⟮jq⟯ (jqN M)) g' :
      ℚ⟮jq⟯⟮jqN M⟯) : LaurentSeries ℚ) = jqN p
    rw [show ((Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ⟮jq⟯ (jqN M)) g' :
      ℚ⟮jq⟯⟮jqN M⟯) : LaurentSeries ℚ)
      = (IntermediateField.val ℚ⟮jq⟯⟮jqN M⟯)
        (Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ⟮jq⟯ (jqN M)) g')
      from rfl, ← h3]
    exact hg'
  rw [← hψy, Polynomial.aeval_algHom_apply, hgE, hx_pval]

/-- A prime-level invariant is not rational: `j(q ^ r) ∉ ℚ⟮jq⟯` for prime `r`.
Membership would make `ℚ⟮jq⟯⟮jqN r⟯` trivial, contradicting its degree `r + 1`. -/
private theorem jqN_prime_not_mem_base (r : ℕ) [hr : Fact (Nat.Prime r)] :
    jqN r ∉ ℚ⟮jq⟯ := by
  intro hmem
  have hbot : IntermediateField.adjoin ℚ⟮jq⟯ ({jqN r} : Set (LaurentSeries ℚ))
      = (⊥ : IntermediateField ℚ⟮jq⟯ (LaurentSeries ℚ)) := by
    rw [IntermediateField.adjoin_simple_eq_bot_iff, IntermediateField.mem_bot]
    exact ⟨⟨jqN r, hmem⟩, rfl⟩
  have h1 : Module.finrank ℚ⟮jq⟯
      (IntermediateField.adjoin ℚ⟮jq⟯ ({jqN r} : Set (LaurentSeries ℚ))) = 1 := by
    rw [hbot]
    exact IntermediateField.finrank_bot
  have h2 := finrank_adjoin_jqN_eq_of_prime r
  rw [h1] at h2
  have h3 := hr.out.two_le
  omega

/-- **Prime non-membership in the adjoin**: for `p ∤ M` and `Hall M`, `jqN p` is not in
`ℚ⟮jq⟯⟮jqN M⟯`. The `ψ(M)` distinct slots of `rval_aux M (ζ ^ p)` are the roots of the
pushed minimal polynomial; `g'` of degree `< ψ(M)` is constant on them
(`eval_map_eq_of_mem_slotValues`), so `jqN p` is the image of a scalar. -/
private theorem jqN_prime_not_mem_adjoin (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)]
    (hpM : ¬ p ∣ M) (hallM : Hall M) :
    jqN p ∉ IntermediateField.adjoin ℚ⟮jq⟯ ({jqN M} : Set (LaurentSeries ℚ)) := by
  classical
  intro hmem
  have hM0 : M ≠ 0 := NeZero.ne M
  have hp0 : p ≠ 0 := hp.out.ne_zero
  haveI : NeZero p := ⟨hp0⟩
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero hM0 hp0⟩
  set K := CyclotomicField (M * p) ℚ with hK
  have hζ : IsPrimitiveRoot ((cycUnit (M * p) : Kˣ) : K) (M * p) := cycUnit_spec (M * p)
  have hζM : IsPrimitiveRoot (((cycUnit (M * p) : Kˣ) ^ p : Kˣ) : K) M := by
    have h1 := isPrimitiveRoot_pow_div hζ (⟨p, rfl⟩ : M ∣ M * p)
    have h2 : M * p / M = p := Nat.mul_div_cancel_left p (Nat.pos_of_ne_zero hM0)
    rwa [h2] at h1
  obtain ⟨htM, -⟩ := hallM M dvd_rfl
  have hα : IsIntegral ℚ⟮jq⟯ (jqN M) := isIntegral_adjoin_jqN htM
  have hdeg : (minpoly ℚ⟮jq⟯ (jqN M)).natDegree = dedekindPsi M := natDegree_minpoly_jqN htM
  have hidMB := map_qExpand_minpoly_eq p (show M * p = p * M from Nat.mul_comm M p)
    ((cycUnit (M * p) : Kˣ) ^ p)
    (minpoly_jqN_map_eq_prod_slots M ((cycUnit (M * p) : Kˣ) ^ p) hζM hallM)
  letI : Algebra ℚ⟮jq⟯ (LaurentSeries K) :=
    (((coeffEmb K).comp (qExpand ℚ (M * p))).comp
      (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ))).toAlgebra
  have halg : algebraMap ℚ⟮jq⟯ (LaurentSeries K)
      = ((coeffEmb K).comp (qExpand ℚ (M * p))).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)) :=
    RingHom.algebraMap_toAlgebra _
  have hroots : ((minpoly ℚ⟮jq⟯ (jqN M)).map (((coeffEmb K).comp
      (qExpand ℚ (M * p))).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))).roots
      = slotValues M (fun a b => qExpand K p (sv K ((cycUnit (M * p) : Kˣ) ^ p) a b)) := by
    rw [hidMB, ← prod_slotValues (K := K)]
    exact Polynomial.roots_multiset_prod_X_sub_C _
  have hTcard : (slotValues M (fun a b =>
      qExpand K p (sv K ((cycUnit (M * p) : Kˣ) ^ p) a b))).card = dedekindPsi M :=
    card_slotValues hM0 _
  have hTnodup : (slotValues M (fun a b =>
      qExpand K p (sv K ((cycUnit (M * p) : Kˣ) ^ p) a b))).Nodup :=
    nodup_slotValues_qExpand hM0 hζM
  have hscard : (slotValues M (fun a b =>
      qExpand K p (sv K ((cycUnit (M * p) : Kˣ) ^ p) a b))).toFinset.card = dedekindPsi M := by
    rw [Multiset.toFinset_card_of_nodup hTnodup]
    exact hTcard
  obtain ⟨g, hg⟩ : ∃ g : Polynomial ℚ⟮jq⟯, Polynomial.aeval (jqN M) g = jqN p := by
    have h1 := IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hα.isAlgebraic
    have h2 : jqN p ∈ Algebra.adjoin ℚ⟮jq⟯ ({jqN M} : Set (LaurentSeries ℚ)) := by
      rw [← h1]
      exact hmem
    rw [Algebra.adjoin_singleton_eq_range_aeval] at h2
    obtain ⟨g, hg⟩ := h2
    exact ⟨g, hg⟩
  set g' := g %ₘ (minpoly ℚ⟮jq⟯ (jqN M)) with hg'def
  have hg' : Polynomial.aeval (jqN M) g' = jqN p := by
    have hsplit := Polynomial.modByMonic_add_div g (minpoly ℚ⟮jq⟯ (jqN M))
    have h4 := congrArg (Polynomial.aeval (jqN M)) hsplit
    rw [map_add, map_mul, minpoly.aeval, zero_mul, add_zero] at h4
    rw [hg'def, h4]
    exact hg
  have hdegpos : 0 < (minpoly ℚ⟮jq⟯ (jqN M)).natDegree := by
    rw [hdeg]
    exact dedekindPsi_pos _ hM0
  have hg'deg : g'.natDegree < (slotValues M (fun a b =>
      qExpand K p (sv K ((cycUnit (M * p) : Kˣ) ^ p) a b))).toFinset.card := by
    rw [hscard, ← hdeg]
    rcases eq_or_ne g' 0 with h0 | h0
    · rw [h0, Polynomial.natDegree_zero]
      exact hdegpos
    · exact Polynomial.natDegree_lt_natDegree h0
        (Polynomial.degree_modByMonic_lt g (minpoly.monic hα))
  have hval : ∀ y ∈ (slotValues M (fun a b =>
      qExpand K p (sv K ((cycUnit (M * p) : Kˣ) ^ p) a b))).toFinset,
      Polynomial.aeval y g' = coeffEmb K (qExpand ℚ (M * p) (jqN p)) := by
    intro y hy
    exact eval_map_eq_of_mem_slotValues (K := K) hpM hζ hα hroots hmem halg hg'
      (Multiset.mem_toFinset.mp hy)
  obtain ⟨z, hz⟩ := mem_range_of_eval_eq_const g'
    (coeffEmb K (qExpand ℚ (M * p) (jqN p)))
    (slotValues M (fun a b => qExpand K p (sv K ((cycUnit (M * p) : Kˣ) ^ p) a b))).toFinset
    hg'deg hval
  rw [halg] at hz
  have hzval : (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)) z = jqN p := by
    apply RingHom.injective ((coeffEmb K).comp (qExpand ℚ (M * p)))
    exact hz
  have hjpF : jqN p ∈ ℚ⟮jq⟯ := by
    rw [← hzval]
    exact z.2
  exact jqN_prime_not_mem_base p hjpF

end NonMem0

/-! ## The public node -/

/-- **Prime non-membership**: `j(q ^ p) ∉ F_M^full` for `p ∤ M`, from `Hall M`. -/
theorem jqN_prime_not_mem_full (M : ℕ) [NeZero M] (p : ℕ)
    [hp : Fact (Nat.Prime p)] (hpM : ¬ p ∣ M) (hallM : Hall M) :
    jqN p ∉ modularFunctionFieldFull M := by
  intro hmem0
  obtain ⟨-, hgM⟩ := hallM M dvd_rfl
  have hmem : jqN p ∈ IntermediateField.adjoin
      (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
      ({jqN M} : Set (LaurentSeries ℚ)) := by
    rw [← hgM] at hmem0
    exact mem_adjoin_jqN_of_mem_mff hmem0
  exact jqN_prime_not_mem_adjoin M p hpM hallM hmem


/-! ## The prime-power tower -/

omit [Algebra ℚ K] in
private theorem mem_range_qExpand_of_mul {a b : ℕ} [NeZero a] [NeZero b] {z : LaurentSeries K}
    (h : z ∈ (qExpand K (a * b)).range) : z ∈ (qExpand K b).range := by
  obtain ⟨w, rfl⟩ := RingHom.mem_range.mp h
  refine RingHom.mem_range.mpr ⟨qExpand K a w, ?_⟩
  rw [qExpand_qExpand]
  exact qExpand_congr (Nat.mul_comm b a) _

omit [Algebra ℚ K] in
private theorem range_qExpand_congr {A A' : ℕ} [NeZero A] [NeZero A'] (h : A = A') :
    (qExpand K A).range = (qExpand K A').range := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩; exact ⟨w, (qExpand_congr h w).symm⟩
  · rintro ⟨w, rfl⟩; exact ⟨w, qExpand_congr h w⟩

private def chainField (M p : ℕ) [NeZero M] [NeZero p] (i : ℕ) :
    IntermediateField ℚ (LaurentSeries ℚ) :=
  IntermediateField.adjoin ℚ ((modularFunctionFieldFull M : Set (LaurentSeries ℚ))
    ∪ {x : LaurentSeries ℚ | ∃ j : ℕ, j ≤ i ∧ x = jqN (p ^ j)})

private theorem mem_chainField (M p : ℕ) [NeZero M] [NeZero p] {j i : ℕ} (hj : j ≤ i) :
    jqN (p ^ j) ∈ chainField M p i :=
  IntermediateField.subset_adjoin ℚ _ (Or.inr ⟨j, hj, rfl⟩)

private theorem full_le_chainField (M p : ℕ) [NeZero M] [NeZero p] (i : ℕ) :
    modularFunctionFieldFull M ≤ chainField M p i :=
  fun _ hx => IntermediateField.subset_adjoin ℚ _ (Or.inl hx)

private theorem chainField_zero (M p : ℕ) [NeZero M] [NeZero p] :
    chainField M p 0 = modularFunctionFieldFull M := by
  apply le_antisymm
  · rw [chainField, IntermediateField.adjoin_le_iff]
    rintro x (hx | ⟨j, hj, rfl⟩)
    · exact hx
    · rw [Nat.le_zero] at hj
      subst hj
      rw [show jqN (p ^ 0) = jq from (jqN_congr (pow_zero p)).trans jqN_one]
      have h2 := jqd_mem_full M (one_dvd M)
      rwa [qExpand_one_apply] at h2
  · exact full_le_chainField M p 0

private theorem chainField_mono (M p : ℕ) [NeZero M] [NeZero p] (i : ℕ) :
    chainField M p i ≤ chainField M p (i + 1) := by
  rw [chainField, chainField]
  refine IntermediateField.adjoin.mono ℚ _ _ (Set.union_subset_union_right _ ?_)
  rintro z ⟨j, hj, rfl⟩
  exact ⟨j, le_trans hj (Nat.le_succ i), rfl⟩

private theorem chainField_succ (M p : ℕ) [NeZero M] [NeZero p] (i : ℕ) :
    chainField M p (i + 1) = IntermediateField.adjoin ℚ
      ((chainField M p i : Set (LaurentSeries ℚ)) ∪ {jqN (p ^ i * p)}) := by
  apply le_antisymm
  · rw [chainField, IntermediateField.adjoin_le_iff]
    rintro x (hx | ⟨j, hj, rfl⟩)
    · exact IntermediateField.subset_adjoin ℚ _
        (Or.inl (full_le_chainField M p i hx))
    · rcases Nat.lt_or_ge j (i + 1) with h | h
      · exact IntermediateField.subset_adjoin ℚ _
          (Or.inl (mem_chainField M p (Nat.lt_succ_iff.mp h)))
      · have hje : j = i + 1 := le_antisymm hj h
        subst hje
        refine IntermediateField.subset_adjoin ℚ _ (Or.inr ?_)
        rw [Set.mem_singleton_iff]
        exact jqN_congr (pow_succ p i)
  · rw [IntermediateField.adjoin_le_iff]
    rintro x (hx | hx)
    · exact chainField_mono M p i hx
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [show jqN (p ^ i * p) = jqN (p ^ (i + 1)) from jqN_congr (pow_succ p i).symm]
      exact mem_chainField M p (le_refl (i + 1))

private theorem chain_extend (p e s : ℕ) [hpp : Fact (Nat.Prime p)] [NeZero e] [NeZero s]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) (p * e * s)) (dp : ModularPolynomialData p)
    (F : IntermediateField ℚ (LaurentSeries ℚ)) (σ : F →+* LaurentSeries K)
    (d : ℕ) [NeZero d] (hd_mem : jqN d ∈ F) (hx_not : jqN (d * p) ∉ F)
    (t : ℕ)
    (hσd : σ ⟨jqN d, hd_mem⟩
      = qExpand K (p * e) (qTwist (ζ ^ (t * (p * e))) (coeffEmb K jq)))
    (hrange : ∀ y : F, σ y ∈ (qExpand K (p * e)).range)
    (G : IntermediateField ℚ (LaurentSeries ℚ))
    (hG : G = IntermediateField.adjoin ℚ ((F : Set (LaurentSeries ℚ)) ∪ {jqN (d * p)})) :
    ∃ (σ' : G →+* LaurentSeries K) (t' : ℕ),
      (∀ (z : F) (hz : (z : LaurentSeries ℚ) ∈ G), σ' ⟨z, hz⟩ = σ z) ∧
      (∀ hx : jqN (d * p) ∈ G, σ' ⟨jqN (d * p), hx⟩
        = qExpand K e (qTwist (ζ ^ (t' * e)) (coeffEmb K jq))) ∧
      (∀ y : G, σ' y ∈ (qExpand K e).range) := by
  subst hG
  classical
  have hp0 : 0 < p := hpp.out.pos

  have hP_aeval : Polynomial.aeval (jqN (d * p)) (phiAtSeed dp (⟨jqN d, hd_mem⟩ : F)) = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, phiAtSeed_map]
    exact phiAtSeed_jqN_eval p dp d
  have hint : IsIntegral F (jqN (d * p)) :=
    ⟨phiAtSeed dp (⟨jqN d, hd_mem⟩ : F), phiAtSeed_monic dp _, by
      rwa [Polynomial.aeval_def] at hP_aeval⟩
  have hdvd : minpoly F (jqN (d * p)) ∣ phiAtSeed dp (⟨jqN d, hd_mem⟩ : F) :=
    minpoly.dvd F _ hP_aeval

  letI : Algebra F (LaurentSeries K) := σ.toAlgebra
  have halg : algebraMap F (LaurentSeries K) = σ := RingHom.algebraMap_toAlgebra σ
  have hpB : p ∣ p * e * s := ⟨e * s, by ring⟩
  have hBdiv : p * e * s / p = e * s := by
    rw [show p * e * s = p * (e * s) from by ring, Nat.mul_div_cancel_left _ hp0]
  have hunit_seed : ζ ^ (t * (p * e)) = (ζ ^ (t * e)) ^ p := by
    rw [← pow_mul]
    congr 1
    ring
  have hmapP : (phiAtSeed dp (⟨jqN d, hd_mem⟩ : F)).map (algebraMap F (LaurentSeries K))
      = phiAtSeed dp (qExpand K (p * e) (qTwist ((ζ ^ (t * e)) ^ p) (coeffEmb K jq))) := by
    rw [phiAtSeed_map, halg, hσd, hunit_seed]
  have hroots_iff : ∀ y : LaurentSeries K,
      Polynomial.aeval y (phiAtSeed dp (⟨jqN d, hd_mem⟩ : F)) = 0 ↔
      (y = qExpand K (p * (p * e)) (qTwist ((ζ ^ (t * e)) ^ (p * p)) (coeffEmb K jq)) ∨
        ∃ c < p, y = qExpand K e
          (qTwist (ζ ^ (t * e) * ζ ^ (c * (e * s))) (coeffEmb K jq))) := by
    intro y
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hmapP, phiAtSeed]
    have h := isRoot_prime_at_slot_iff (p * e * s) ζ hζ p hpB dp e (ζ ^ (t * e)) y
    rw [hBdiv] at h
    exact h

  have hPmap_ne : (phiAtSeed dp (⟨jqN d, hd_mem⟩ : F)).map (algebraMap F (LaurentSeries K)) ≠ 0 :=
    ((phiAtSeed_monic dp _).map _).ne_zero
  have hPmap_splits : ((phiAtSeed dp (⟨jqN d, hd_mem⟩ : F)).map
      (algebraMap F (LaurentSeries K))).Splits := by
    rw [hmapP, phiAtSeed, PhiGen.splits_prime_at_slot (p * e * s) ζ hζ p hpB dp e
      (ζ ^ (t * e))]
    exact (Polynomial.Splits.X_sub_C _).mul
      (Polynomial.Splits.prod fun b _ => Polynomial.Splits.X_sub_C _)
  have hPmap_nodup : ((phiAtSeed dp (⟨jqN d, hd_mem⟩ : F)).map
      (algebraMap F (LaurentSeries K))).roots.Nodup := by
    rw [hmapP, phiAtSeed]
    exact roots_prime_at_slot_roots_nodup (p * e * s) ζ hζ p hpB dp e (ζ ^ (t * e))
  have hm_dvd_map : (minpoly F (jqN (d * p))).map (algebraMap F (LaurentSeries K))
      ∣ (phiAtSeed dp (⟨jqN d, hd_mem⟩ : F)).map (algebraMap F (LaurentSeries K)) :=
    Polynomial.map_dvd _ hdvd
  have hm_roots_le : ((minpoly F (jqN (d * p))).map (algebraMap F (LaurentSeries K))).roots
      ≤ ((phiAtSeed dp (⟨jqN d, hd_mem⟩ : F)).map (algebraMap F (LaurentSeries K))).roots :=
    Polynomial.roots.le_of_dvd hPmap_ne hm_dvd_map
  have hm_splits : ((minpoly F (jqN (d * p))).map (algebraMap F (LaurentSeries K))).Splits :=
    hPmap_splits.of_dvd hPmap_ne hm_dvd_map
  have hm_deg : 2 ≤ ((minpoly F (jqN (d * p))).map (algebraMap F (LaurentSeries K))).natDegree := by
    rw [(minpoly.monic hint).natDegree_map, minpoly.two_le_natDegree_iff hint]
    intro hmem
    obtain ⟨w, hw⟩ := hmem
    rw [← hw] at hx_not
    exact hx_not w.2
  have hm_nodup : (((minpoly F (jqN (d * p))).map (algebraMap F (LaurentSeries K))).roots).Nodup :=
    Multiset.nodup_of_le hm_roots_le hPmap_nodup
  have hroot_trans : ∀ y ∈ ((minpoly F (jqN (d * p))).map (algebraMap F (LaurentSeries K))).roots,
      Polynomial.aeval y (phiAtSeed dp (⟨jqN d, hd_mem⟩ : F)) = 0 := by
    intro y hy
    have h1 : y ∈ ((phiAtSeed dp (⟨jqN d, hd_mem⟩ : F)).map
        (algebraMap F (LaurentSeries K))).roots := Multiset.mem_of_le hm_roots_le hy
    rw [Polynomial.mem_roots hPmap_ne] at h1
    rw [Polynomial.aeval_def, ← Polynomial.eval_map]
    exact h1

  have h2d : ∃ y₁ ∈ ((minpoly F (jqN (d * p))).map (algebraMap F (LaurentSeries K))).roots,
      ∃ y₂ ∈ ((minpoly F (jqN (d * p))).map (algebraMap F (LaurentSeries K))).roots, y₁ ≠ y₂ := by
    have hcard : 1 < (((minpoly F (jqN (d * p))).map
        (algebraMap F (LaurentSeries K))).roots).toFinset.card := by
      rw [Multiset.toFinset_card_of_nodup hm_nodup, ← hm_splits.natDegree_eq_card_roots]
      omega
    obtain ⟨y₁, hy₁, y₂, hy₂, hne⟩ := Finset.one_lt_card.mp hcard
    exact ⟨y₁, Multiset.mem_toFinset.mp hy₁, y₂, Multiset.mem_toFinset.mp hy₂, hne⟩
  obtain ⟨y₁, hy₁, y₂, hy₂, hne⟩ := h2d
  have hex_twist : ∃ c < p, qExpand K e (qTwist (ζ ^ (t * e) * ζ ^ (c * (e * s))) (coeffEmb K jq))
      ∈ ((minpoly F (jqN (d * p))).map (algebraMap F (LaurentSeries K))).roots := by
    rcases (hroots_iff y₁).mp (hroot_trans y₁ hy₁) with h1 | ⟨c, hc, h1⟩
    · rcases (hroots_iff y₂).mp (hroot_trans y₂ hy₂) with h2 | ⟨c, hc, h2⟩
      · exact absurd (h1.trans h2.symm) hne
      · exact ⟨c, hc, h2 ▸ hy₂⟩
    · exact ⟨c, hc, h1 ▸ hy₁⟩
  obtain ⟨c, hc, htwist_mem⟩ := hex_twist
  have htwist_aroots : qExpand K e (qTwist (ζ ^ (t * e) * ζ ^ (c * (e * s))) (coeffEmb K jq))
      ∈ (minpoly F (jqN (d * p))).aroots (LaurentSeries K) := htwist_mem

  obtain ⟨ψ, hψ_gen⟩ : ∃ ψ : IntermediateField.adjoin F ({jqN (d * p)} : Set (LaurentSeries ℚ))
        →ₐ[F] LaurentSeries K,
      ψ (IntermediateField.AdjoinSimple.gen F (jqN (d * p)))
        = qExpand K e (qTwist (ζ ^ (t * e) * ζ ^ (c * (e * s))) (coeffEmb K jq)) :=
    ⟨(IntermediateField.algHomAdjoinIntegralEquiv F hint).symm ⟨_, htwist_aroots⟩,
      IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen F hint ⟨_, htwist_aroots⟩⟩

  have hle : ∀ {z : LaurentSeries ℚ},
      z ∈ IntermediateField.adjoin ℚ ((F : Set (LaurentSeries ℚ)) ∪ {jqN (d * p)}) →
      z ∈ IntermediateField.adjoin F ({jqN (d * p)} : Set (LaurentSeries ℚ)) := by
    intro z hz
    induction hz using IntermediateField.adjoin_induction with
    | mem w hw =>
      rcases hw with hw | hw
      · exact (IntermediateField.adjoin F
          ({jqN (d * p)} : Set (LaurentSeries ℚ))).algebraMap_mem ⟨w, hw⟩
      · rw [Set.mem_singleton_iff] at hw
        subst hw
        exact IntermediateField.subset_adjoin F _ rfl
    | algebraMap q =>
      rw [eq_ratCast]
      exact SubfieldClass.ratCast_mem _ q
    | add x y hx hy ihx ihy => exact add_mem ihx ihy
    | inv x hx ihx => exact inv_mem ihx
    | mul x y hx hy ihx ihy => exact mul_mem ihx ihy
  refine ⟨{
    toFun := fun z => ψ ⟨z.1, hle z.2⟩
    map_one' := (congrArg ψ (Subtype.ext rfl)).trans (map_one ψ)
    map_mul' := fun z w => by
      have h1 : (⟨(z * w).1, hle (z * w).2⟩ :
          IntermediateField.adjoin F ({jqN (d * p)} : Set (LaurentSeries ℚ)))
          = ⟨z.1, hle z.2⟩ * ⟨w.1, hle w.2⟩ := Subtype.ext rfl
      rw [h1, map_mul]
    map_zero' := (congrArg ψ (Subtype.ext rfl)).trans (map_zero ψ)
    map_add' := fun z w => by
      have h1 : (⟨(z + w).1, hle (z + w).2⟩ :
          IntermediateField.adjoin F ({jqN (d * p)} : Set (LaurentSeries ℚ)))
          = ⟨z.1, hle z.2⟩ + ⟨w.1, hle w.2⟩ := Subtype.ext rfl
      rw [h1, map_add] }, t + c * s, ?_, ?_, ?_⟩
  ·
    intro z hz
    show ψ ⟨(z : LaurentSeries ℚ), _⟩ = σ z
    have h1 : (⟨(z : LaurentSeries ℚ), hle hz⟩ :
        IntermediateField.adjoin F ({jqN (d * p)} : Set (LaurentSeries ℚ)))
        = algebraMap F (IntermediateField.adjoin F ({jqN (d * p)} : Set (LaurentSeries ℚ))) z :=
      Subtype.ext rfl
    rw [h1, AlgHom.commutes, halg]
  ·
    intro hx
    show ψ ⟨jqN (d * p), _⟩ = _
    have h1 : (⟨jqN (d * p), hle hx⟩ :
        IntermediateField.adjoin F ({jqN (d * p)} : Set (LaurentSeries ℚ)))
        = IntermediateField.AdjoinSimple.gen F (jqN (d * p)) := Subtype.ext rfl
    have hu : ζ ^ (t * e) * ζ ^ (c * (e * s)) = ζ ^ ((t + c * s) * e) := by
      rw [← pow_add]
      congr 1
      ring
    rw [h1, hψ_gen, hu]
  ·
    intro z
    show ψ ⟨z.1, hle z.2⟩ ∈ (qExpand K e).range
    obtain ⟨g, hg⟩ := (IntermediateField.adjoin.powerBasis hint).exists_eq_aeval'
      (⟨z.1, hle z.2⟩ : IntermediateField.adjoin F ({jqN (d * p)} : Set (LaurentSeries ℚ)))
    rw [IntermediateField.adjoin.powerBasis_gen] at hg
    rw [hg, ← Polynomial.aeval_algHom_apply, hψ_gen, Polynomial.aeval_def,
      Polynomial.eval₂_eq_sum_range]
    refine sum_mem fun i _ => mul_mem ?_ (pow_mem ?_ i)
    · rw [halg]
      exact mem_range_qExpand_of_mul (hrange _)
    · exact RingHom.mem_range.mpr
        ⟨qTwist (ζ ^ (t * e) * ζ ^ (c * (e * s))) (coeffEmb K jq), rfl⟩

/-! ## The tower endgame -/

/-- **The spread root is unique.** A root of the level-`p` equation at the top of the tower that
lies in `(qExpand K (M * p)).range` is the spread value `qExpand K (p * (p * M)) (qTwist …)`: the
other root of the dichotomy is a twist at level `M` sitting inside `qExpand K (M * p)`'s range,
which `qExpand_qTwist_notMem_range_qExpand` forbids because `M * p ∤ M`. -/
private theorem eq_spread_of_eval_eq_zero_of_mem_range {M p a tt : ℕ} [NeZero M]
    [hp : Fact (Nat.Prime p)] {ζ : Kˣ} (dp : ModularPolynomialData p)
    (hMp_ne : ¬ (((M * p : ℕ) : ℤ) ∣ ((M : ℕ) : ℤ)))
    (hroots_top : ∀ y : LaurentSeries K,
      (phiAtSeed dp (qExpand K (M * p)
        (qTwist (ζ ^ (tt * (M * p))) (coeffEmb K jq)))).eval y = 0 ↔
      (y = qExpand K (p * (p * M)) (qTwist ((ζ ^ (tt * M)) ^ (p * p)) (coeffEmb K jq)) ∨
        ∃ c < p, y = qExpand K M
          (qTwist (ζ ^ (tt * M) * ζ ^ (c * (M * p ^ (a + 1)))) (coeffEmb K jq))))
    {y : LaurentSeries K}
    (hy : (phiAtSeed dp (qExpand K (M * p)
      (qTwist (ζ ^ (tt * (M * p))) (coeffEmb K jq)))).eval y = 0)
    (hyr : y ∈ (qExpand K (M * p)).range) :
    y = qExpand K (p * (p * M)) (qTwist ((ζ ^ (tt * M)) ^ (p * p)) (coeffEmb K jq)) := by
  rcases (hroots_top y).mp hy with h | ⟨c, hc, h⟩
  · exact h
  · exfalso
    rw [h] at hyr
    exact qExpand_qTwist_notMem_range_qExpand hMp_ne _ hyr

private theorem chain_endgame (M p : ℕ) [NeZero M] [hp : Fact (Nat.Prime p)] (a : ℕ)
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) (M * p ^ (a + 2)))
    (dp : ModularPolynomialData p) (hsp : EvalSymm dp.Φ)
    -- `hnot`: the level-`i` slot `jqN (p ^ i * p)` is not in `C_i`. It bundles `jqN p ∉ F_M^full`
    -- (the case `i = 0`) with the strong induction hypothesis (the case `i ≥ 1`); it is proved at
    -- the call site, where that hypothesis is what generates it, and it replaces the `hF`/`hIH`
    -- the body used to take separately.
    (hnot : ∀ i : ℕ, i ≤ a → jqN (p ^ i * p) ∉ chainField M p i)
    (hmem : jqN (p ^ (a + 2)) ∈ chainField M p (a + 1)) : False := by
  classical
  have hp0 : 0 < p := hp.out.pos
  have hp2 : 2 ≤ p := hp.out.two_le
  have hM0 : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)

  have chain : ∀ i : ℕ, i ≤ a + 1 →
      ∃ (σ : chainField M p i →+* LaurentSeries K) (t : ℕ),
        (σ ⟨jqN (p ^ i), mem_chainField M p (le_refl i)⟩
          = qExpand K (M * p ^ (a + 2 - i))
            (qTwist (ζ ^ (t * (M * p ^ (a + 2 - i)))) (coeffEmb K jq))) ∧
        (∀ y : chainField M p i, σ y ∈ (qExpand K (M * p ^ (a + 2 - i))).range) := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨((coeffEmb K).comp (qExpand ℚ (M * p ^ (a + 2)))).comp
        (algebraMap (chainField M p 0) (LaurentSeries ℚ)), 0, ?_, ?_⟩
      · show coeffEmb K (qExpand ℚ (M * p ^ (a + 2)) (jqN (p ^ 0))) = _
        rw [show jqN (p ^ 0) = jq from (jqN_congr (pow_zero p)).trans jqN_one, iota_jq,
          zero_mul, pow_zero, coeffEmb_jq]
        show TS K (M * p ^ (a + 2)) 1 = TS K (M * p ^ (a + 2 - 0)) 1
        exact TS_congr (by rw [Nat.sub_zero]) 1
      · intro y
        show coeffEmb K (qExpand ℚ (M * p ^ (a + 2)) (y : LaurentSeries ℚ)) ∈ _
        rw [coeffEmb_qExpand]
        rw [← range_qExpand_congr (show (M * p ^ (a + 2) : ℕ) = M * p ^ (a + 2 - 0) from by
          rw [Nat.sub_zero])]
        exact RingHom.mem_range.mpr ⟨coeffEmb K (y : LaurentSeries ℚ), rfl⟩
    | succ i ih =>
      intro hi
      obtain ⟨σ, t, hσtop, hσrange⟩ := ih (Nat.le_of_succ_le hi)
      have hpow_step : M * p ^ (a + 2 - i) = p * (M * p ^ (a + 2 - (i + 1))) := by
        rw [show a + 2 - i = (a + 2 - (i + 1)) + 1 from by omega, pow_succ]
        ring
      have hσtop' : σ ⟨jqN (p ^ i), mem_chainField M p (le_refl i)⟩
          = qExpand K (p * (M * p ^ (a + 2 - (i + 1))))
            (qTwist (ζ ^ (t * (p * (M * p ^ (a + 2 - (i + 1)))))) (coeffEmb K jq)) := by
        rw [hσtop]
        have h1 : ζ ^ (t * (M * p ^ (a + 2 - i)))
            = ζ ^ (t * (p * (M * p ^ (a + 2 - (i + 1))))) := by
          rw [hpow_step]
        rw [h1, coeffEmb_jq]
        show TS K (M * p ^ (a + 2 - i)) _ = TS K (p * (M * p ^ (a + 2 - (i + 1)))) _
        exact TS_congr hpow_step _
      have hζ' : IsPrimitiveRoot (ζ : K) (p * (M * p ^ (a + 2 - (i + 1))) * p ^ i) := by
        have hBs : M * p ^ (a + 2) = p * (M * p ^ (a + 2 - (i + 1))) * p ^ i := by
          have h1 : (1 : ℕ) + (a + 2 - (i + 1)) + i = a + 2 := by omega
          calc M * p ^ (a + 2) = M * p ^ (1 + (a + 2 - (i + 1)) + i) := by rw [h1]
            _ = p * (M * p ^ (a + 2 - (i + 1))) * p ^ i := by
                rw [pow_add, pow_add, pow_one]; ring
        exact hBs ▸ hζ
      have hσrange' : ∀ y : chainField M p i,
          σ y ∈ (qExpand K (p * (M * p ^ (a + 2 - (i + 1))))).range := by
        intro y
        have h := hσrange y
        rwa [range_qExpand_congr hpow_step] at h
      obtain ⟨σ', t', hcompat, hσ'new, hσ'range⟩ :=
        chain_extend p (M * p ^ (a + 2 - (i + 1))) (p ^ i) ζ hζ' dp (chainField M p i) σ
          (p ^ i) (mem_chainField M p (le_refl i)) (hnot i (Nat.le_of_succ_le_succ hi)) t
          hσtop' hσrange' (chainField M p (i + 1)) (chainField_succ M p i)
      refine ⟨σ', t', ?_, hσ'range⟩
      have hxmem : jqN (p ^ i * p) ∈ chainField M p (i + 1) := by
        rw [show jqN (p ^ i * p) = jqN (p ^ (i + 1)) from jqN_congr (pow_succ p i).symm]
        exact mem_chainField M p (le_refl (i + 1))
      have hmk : (⟨jqN (p ^ (i + 1)), mem_chainField M p (le_refl (i + 1))⟩ :
          chainField M p (i + 1)) = ⟨jqN (p ^ i * p), hxmem⟩ :=
        Subtype.ext (jqN_congr (pow_succ p i))
      rw [hmk]
      exact hσ'new hxmem

  -- The loop's last step *is* the step to `C_{a+1}`: no hand re-derivation.
  obtain ⟨σ, tt, hσtop, hrange_raw⟩ := chain (a + 1) (le_refl (a + 1))
  have hmem_a1 : jqN (p ^ (a + 1)) ∈ chainField M p (a + 1) :=
    mem_chainField M p (le_refl (a + 1))
  have hmem_a : jqN (p ^ a) ∈ chainField M p (a + 1) :=
    mem_chainField M p (Nat.le_succ a)
  have hpow_top : M * p ^ (a + 2 - (a + 1)) = M * p := by
    rw [show a + 2 - (a + 1) = 1 from by omega, pow_one]
  have hσ_a1 : σ ⟨jqN (p ^ (a + 1)), hmem_a1⟩
      = qExpand K (M * p) (qTwist (ζ ^ (tt * (M * p))) (coeffEmb K jq)) := by
    rw [hσtop]
    have h1 : ζ ^ (tt * (M * p ^ (a + 2 - (a + 1)))) = ζ ^ (tt * (M * p)) := by
      rw [hpow_top]
    rw [h1, coeffEmb_jq]
    show TS K (M * p ^ (a + 2 - (a + 1))) _ = TS K (M * p) _
    exact TS_congr hpow_top _
  have hrange : ∀ y : chainField M p (a + 1), σ y ∈ (qExpand K (M * p)).range := by
    intro y
    have h := hrange_raw y
    rwa [range_qExpand_congr hpow_top] at h

  have hrel_up_Ω : (phiAtSeed dp (jqN (p ^ (a + 1)))).eval (jqN (p ^ (a + 2))) = 0 := by
    have h := phiAtSeed_jqN_eval p dp (p ^ (a + 1))
    rwa [show jqN (p ^ (a + 1) * p) = jqN (p ^ (a + 2)) from
      jqN_congr (pow_succ p (a + 1)).symm] at h
  have hrel_dn_Ω : (phiAtSeed dp (jqN (p ^ (a + 1)))).eval (jqN (p ^ a)) = 0 := by
    have h := phiAtSeed_jqN_eval_down p dp hsp (p ^ a)
    rwa [show jqN (p ^ a * p) = jqN (p ^ (a + 1)) from jqN_congr (pow_succ p a).symm] at h
  have hrel_up_E : (phiAtSeed dp (⟨jqN (p ^ (a + 1)), hmem_a1⟩ : chainField M p (a + 1))).eval
      (⟨jqN (p ^ (a + 2)), hmem⟩ : chainField M p (a + 1)) = 0 :=
    phiAtSeed_eval_of_injective dp _ _
      (algebraMap (chainField M p (a + 1)) (LaurentSeries ℚ)) Subtype.val_injective hrel_up_Ω
  have hrel_dn_E : (phiAtSeed dp (⟨jqN (p ^ (a + 1)), hmem_a1⟩ : chainField M p (a + 1))).eval
      (⟨jqN (p ^ a), hmem_a⟩ : chainField M p (a + 1)) = 0 :=
    phiAtSeed_eval_of_injective dp _ _
      (algebraMap (chainField M p (a + 1)) (LaurentSeries ℚ)) Subtype.val_injective hrel_dn_Ω

  have hz_up : (phiAtSeed dp (qExpand K (M * p)
      (qTwist (ζ ^ (tt * (M * p))) (coeffEmb K jq)))).eval
      (σ ⟨jqN (p ^ (a + 2)), hmem⟩) = 0 := by
    have h := phiAtSeed_eval_map dp _ _
      (σ : chainField M p (a + 1) →+* LaurentSeries K) hrel_up_E
    rwa [hσ_a1] at h
  have hz_dn : (phiAtSeed dp (qExpand K (M * p)
      (qTwist (ζ ^ (tt * (M * p))) (coeffEmb K jq)))).eval
      (σ ⟨jqN (p ^ a), hmem_a⟩) = 0 := by
    have h := phiAtSeed_eval_map dp _ _
      (σ : chainField M p (a + 1) →+* LaurentSeries K) hrel_dn_E
    rwa [hσ_a1] at h

  have hpB : p ∣ M * p ^ (a + 2) := by
    refine ⟨M * p ^ (a + 1), ?_⟩
    rw [pow_succ]
    ring
  have hBdiv : M * p ^ (a + 2) / p = M * p ^ (a + 1) := by
    rw [show M * p ^ (a + 2) = M * p ^ (a + 1) * p from by rw [pow_succ]; ring]
    exact Nat.mul_div_cancel _ hp0
  have hseed_eq : qExpand K (M * p) (qTwist (ζ ^ (tt * (M * p))) (coeffEmb K jq))
      = qExpand K (p * M) (qTwist ((ζ ^ (tt * M)) ^ p) (coeffEmb K jq)) := by
    have h1 : ζ ^ (tt * (M * p)) = (ζ ^ (tt * M)) ^ p := by
      rw [← pow_mul]
      congr 1
      ring
    rw [h1, coeffEmb_jq]
    show TS K (M * p) _ = TS K (p * M) _
    exact TS_congr (Nat.mul_comm M p) _
  have hroots_top : ∀ y : LaurentSeries K,
      (phiAtSeed dp (qExpand K (M * p)
        (qTwist (ζ ^ (tt * (M * p))) (coeffEmb K jq)))).eval y = 0 ↔
      (y = qExpand K (p * (p * M)) (qTwist ((ζ ^ (tt * M)) ^ (p * p)) (coeffEmb K jq)) ∨
        ∃ c < p, y = qExpand K M
          (qTwist (ζ ^ (tt * M) * ζ ^ (c * (M * p ^ (a + 1)))) (coeffEmb K jq))) := by
    intro y
    rw [hseed_eq, phiAtSeed]
    have h := isRoot_prime_at_slot_iff (M * p ^ (a + 2)) ζ hζ p hpB dp M (ζ ^ (tt * M)) y
    rw [hBdiv] at h
    exact h

  have hMp_ne : ¬ (((M * p : ℕ) : ℤ) ∣ ((M : ℕ) : ℤ)) := by
    rw [Int.natCast_dvd_natCast]
    intro h
    have h1 := Nat.le_of_dvd hM0 h
    have h2 : M * 2 ≤ M * p := Nat.mul_le_mul_left M hp2
    omega
  have hz_up_spread : σ ⟨jqN (p ^ (a + 2)), hmem⟩
      = qExpand K (p * (p * M)) (qTwist ((ζ ^ (tt * M)) ^ (p * p)) (coeffEmb K jq)) :=
    eq_spread_of_eval_eq_zero_of_mem_range (M := M) (p := p) (a := a) (tt := tt) dp hMp_ne
      hroots_top hz_up (hrange ⟨jqN (p ^ (a + 2)), hmem⟩)

  have hz_dn_spread : σ ⟨jqN (p ^ a), hmem_a⟩
      = qExpand K (p * (p * M)) (qTwist ((ζ ^ (tt * M)) ^ (p * p)) (coeffEmb K jq)) :=
    eq_spread_of_eval_eq_zero_of_mem_range (M := M) (p := p) (a := a) (tt := tt) dp hMp_ne
      hroots_top hz_dn (hrange ⟨jqN (p ^ a), hmem_a⟩)

  have hsub : (⟨jqN (p ^ (a + 2)), hmem⟩ : chainField M p (a + 1))
      = ⟨jqN (p ^ a), hmem_a⟩ :=
    RingHom.injective σ (hz_up_spread.trans hz_dn_spread.symm)
  have hval : jqN (p ^ (a + 2)) = jqN (p ^ a) := Subtype.ext_iff.mp hsub
  have hc1 : (jqN (p ^ a)).coeff (-((p ^ a : ℕ) : ℤ)) = 1 := by
    show (qExpand ℚ (p ^ a) jq).coeff _ = 1
    have h := qExpand_coeff_mul (R := ℚ) (N := p ^ a) jq (-1)
    rw [mul_neg_one] at h
    rw [h, coeff_jq_neg_one]
  have hc2 : (jqN (p ^ (a + 2))).coeff (-((p ^ a : ℕ) : ℤ)) = 0 := by
    show (qExpand ℚ (p ^ (a + 2)) jq).coeff _ = 0
    apply qExpand_coeff_of_not_dvd
    rw [dvd_neg, Int.natCast_dvd_natCast]
    intro hdvd
    have hle2 := Nat.le_of_dvd (pow_pos hp0 a) hdvd
    have h1 : p ^ a < p ^ a * (p * p) :=
      lt_mul_of_one_lt_right (pow_pos hp0 a) (by nlinarith)
    have h2 : p ^ a * (p * p) = p ^ (a + 2) := by rw [pow_add]; ring
    omega
  rw [hval, hc1] at hc2
  exact one_ne_zero hc2

private theorem jqN_pow_not_mem_adjoin_full_key (M : ℕ) [NeZero M] (p : ℕ)
    [hp : Fact (Nat.Prime p)] (a : ℕ) (hF : jqN p ∉ modularFunctionFieldFull M) :
    jqN (p ^ (a + 2)) ∉ chainField M p (a + 1) := by
  induction a using Nat.strong_induction_on with
  | _ a IH =>
  intro hmem
  obtain ⟨dp, -, hsp⟩ := exists_phiIrreducible_evalSymm p
  have hnot : ∀ i : ℕ, i ≤ a → jqN (p ^ i * p) ∉ chainField M p i := by
    intro i hi
    rw [show jqN (p ^ i * p) = jqN (p ^ (i + 1)) from jqN_congr (pow_succ p i).symm]
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [chainField_zero]
      rw [show jqN (p ^ (0 + 1)) = jqN p from jqN_congr (by rw [zero_add, pow_one])]
      exact hF
    · have heq1 : jqN (p ^ (i + 1)) = jqN (p ^ (i - 1 + 2)) :=
        jqN_congr (congrArg (fun n => p ^ n) (by omega))
      have heq2 : chainField M p i = chainField M p (i - 1 + 1) :=
        congrArg (chainField M p) (by omega)
      rw [heq1, heq2]
      exact IH (i - 1) (by omega)
  exact chain_endgame M p a (cycUnit (M * p ^ (a + 2))) (cycUnit_spec (M * p ^ (a + 2)))
    dp hsp hnot hmem

/-- **The prime-power tower**: for `jqN p ∉ F_M^full`,
`j(q ^ (p ^ (a + 2))) ∉ ℚ(F_M^full, j(q ^ p), …, j(q ^ (p ^ (a + 1))))`. -/
theorem jqN_pow_not_mem_adjoin_full (M : ℕ) [NeZero M] (p : ℕ)
    [hp : Fact (Nat.Prime p)] (a : ℕ)
    (hF : jqN p ∉ modularFunctionFieldFull M) :
    jqN (p ^ (a + 2)) ∉ IntermediateField.adjoin ℚ
      ((modularFunctionFieldFull M : Set (LaurentSeries ℚ))
        ∪ {x : LaurentSeries ℚ | ∃ i : ℕ, i ≤ a + 1 ∧ x = jqN (p ^ i)}) :=
  jqN_pow_not_mem_adjoin_full_key M p a hF


end ModularCurve

end
