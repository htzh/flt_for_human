/-
  T19 wave 4 — the prime non-membership at a general coefficient field.

  `levelSeries jg p ∉ levelField jg M` for a prime `p ∤ M`: the level series at the prime is not in
  the level-`M` field, given the level-degree package at `M` and the same fact one level down (that
  it is not in the base field). This is the T19 half that says a new prime costs a new degree, and it
  is the shape the `C` layer's `jqNModC_prime_not_mem_fullC` and the `ℚ` `jqN_prime_not_mem_full` both
  want: two per-layer inputs, and the conclusion over `κ`.

  ## The seam

  The conclusion is over `κ`; the slots are computed in a carrier `κ'` reached by `ε`, with `ζ` a
  primitive `(M * p)`-th root there. Those three binders are the seam and not an accident: the proof
  reads the `ψ(M)` slot values of the level-`M` minimal polynomial in `κ'`, where the conjugates
  live, and the contradiction is then transported back along `ε` (injective, since `κ` is a field).
  `ℚ` manufactures the carrier as a cyclotomic field; the `C` layer is handed one by its own
  statement.

  ## The carrier premises

  The two conditions `hε : ε jg = jqModC κ'` and `hεq : ∀ N, ε (qExpand κ N x) = qExpand κ' N (ε x)`
  are *premises of the theorem*, not arguments: the slot theory reads `slotValue` through `TS` only
  under them (the same pair `SlotProductAt` carries). They are not derivable from anything else in
  the statement — `ε` is a free ring hom, and at `jg = 0` every slot value is `0` — and the
  `RingHom.id` instance (`κ' = κ`, `jg = jqModC κ`) discharges both by `rfl`. So the theorem carries
  no hypothesis on the prime level beyond the base non-membership: the pair it does carry is the
  carrier, and the nome it is read at is `p * M`, the one `pushedMinpolyAt_map_qExpand` hands over.

  ## The route

  The proof is the port's `Nonmembership` argument for the part that carries the seam: the pushed
  minimal polynomial at `M`, its slot multiset, the conjugate `ψy` out of `levelField jg M`
  (`exists_algHom_adjoin_of_isRoot`), and the induction that a conjugate maps the whole level field
  into the `qExpand κ' p`-range (`map_mem_fieldRange`). The classification of the conjugate uses the
  `Φ_p`-dichotomy instead of the level-`p` slot product:

  * the seed relation `Φ_p(j, j(q ^ p)) = 0` holds over `κ` (`seed_eval_zero` at `d = 1`) and is
    pushed along `ε`;
  * a root of `Φ_p` at a primitive `p`-th root is either the distinguished slot or one of the `p`
    twists (`isRoot_prime_at_slot_iff_of_isPrimitiveRoot`);
  * the twist branch dies on the `q ^ (-M)` coefficient, which a `qExpand κ' p`-value cannot carry
    when `p ∤ M` (`qExpand_coeff_of_not_dvd` against `TS_coeff_neg`).

  So the level-`p` package is never needed: there is no `degreeAt jg p` hypothesis, and no `PkgAt jg
  p` derivation. Both per-layer inputs are spent — the package at `M` gives the slot count and the
  generation, the base non-membership is the final contradiction.

  ## What the two instances supply

  | | `κ` | `κ'` | `ε` | `jg` | `ζ` | `hε` | `hεq` |
  |---|---|---|---|---|---|---|---|
  | `ℚ` | `ℚ` | `K = CyclotomicField (M * p) ℚ` | `coeffEmb K` | `jq` | `cycUnit (M * p)` | `coeffEmb_jq` | `coeffEmb_qExpand` |
  | any field | `K` | `K` | `RingHom.id` | `jqModC K` | the caller's root | `rfl` | `rfl` |
-/
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Generic.SlotProduct
import FLTForHuman.FieldTheory.CommonRoot

set_option autoImplicit false

noncomputable section

open Polynomial HahnSeries IntermediateField
open scoped IntermediateField

namespace ModularCurve

variable {κ κ' : Type*} [Field κ] [Field κ']

/-- **The expanded slots are distinct**: applying `qExpand κ' p` to the `ζ ^ p`-slots keeps them
distinct, `qExpand κ' p` being injective and the slots already distinct at the primitive root
`ζ ^ p` of order `M`. -/
private theorem nodup_slotValues_expanded (ε : LaurentSeries κ →+* LaurentSeries κ')
    (jg : LaurentSeries κ) (hε : ε jg = jqModC κ')
    {M p : ℕ} [NeZero p] {ζ : κ'ˣ} (hM0 : M ≠ 0)
    (hζ : IsPrimitiveRoot ((ζ ^ p : κ'ˣ) : κ') M) :
    (slotValues M (fun a b => qExpand κ' p (slotValue ε jg (ζ ^ p) a b))).Nodup := by
  refine nodup_slotValues fun a b a' b' ha ha' hb hb' h => ?_
  exact slotValue_inj_slot ε jg hε hζ hM0 (Nat.mem_divisors.mp ha).1 (Nat.mem_divisors.mp ha').1
    (Finset.mem_range.mp (Finset.mem_filter.mp hb).1)
    (Finset.mem_range.mp (Finset.mem_filter.mp hb').1)
    (RingHom.injective (qExpand κ' p) h)

/-- **A conjugate maps the level field into the `qExpand κ' p`-range**: if `y` lies in that range,
`ψy` sends the level-`M` generator to `y`, and `ε` of a level-`M` `q`-expansion is again a
`qExpand κ' p`-value (`hιS`), then `ψy` sends *every* element of `levelField jg M` into the range.
The induction is over the simple extension. -/
private theorem map_mem_fieldRange (ε : LaurentSeries κ →+* LaurentSeries κ')
    (jg : LaurentSeries κ) {M p : ℕ} [NeZero M] [NeZero p] {y : LaurentSeries κ'}
    [Algebra (baseField jg) (LaurentSeries κ')]
    {ψy : levelField jg M →ₐ[baseField jg] LaurentSeries κ'}
    (hψgen : ∀ h : levelSeries jg M ∈ (levelField jg M : Set (LaurentSeries κ)),
      ψy ⟨levelSeries jg M, h⟩ = y)
    (hyS : y ∈ (qExpand κ' p).fieldRange)
    (hιS : ∀ w : LaurentSeries κ, ε (qExpand κ (p * M) w) = qExpand κ' p (ε (qExpand κ M w)))
    (halg : algebraMap (baseField jg) (LaurentSeries κ') = nomeMap ε jg (p * M)) :
    ∀ (x : LaurentSeries κ) (hx : x ∈ (levelField jg M : Set (LaurentSeries κ))),
      ψy ⟨x, hx⟩ ∈ (qExpand κ' p).fieldRange := by
  intro x hx
  induction hx using IntermediateField.adjoin_induction with
  | mem z hz =>
      rw [Set.mem_singleton_iff] at hz
      subst hz
      rw [hψgen]
      exact hyS
  | algebraMap z =>
      show ψy (algebraMap (baseField jg) (levelField jg M) z) ∈ (qExpand κ' p).fieldRange
      rw [AlgHom.commutes, halg]
      show nomeMap ε jg (p * M) z ∈ (qExpand κ' p).fieldRange
      show ε (qExpand κ (p * M) (algebraMap (baseField jg) (LaurentSeries κ) z))
        ∈ (qExpand κ' p).fieldRange
      rw [hιS]
      exact RingHom.mem_fieldRange.mpr ⟨_, rfl⟩
  | add x₁ x₂ hx₁ hx₂ ih₁ ih₂ =>
      show ψy ⟨x₁ + x₂, add_mem hx₁ hx₂⟩ ∈ (qExpand κ' p).fieldRange
      rw [show (⟨x₁ + x₂, add_mem hx₁ hx₂⟩ : levelField jg M)
        = ⟨x₁, hx₁⟩ + ⟨x₂, hx₂⟩ from rfl, map_add]
      exact Subfield.add_mem _ ih₁ ih₂
  | mul x₁ x₂ hx₁ hx₂ ih₁ ih₂ =>
      show ψy ⟨x₁ * x₂, mul_mem hx₁ hx₂⟩ ∈ (qExpand κ' p).fieldRange
      rw [show (⟨x₁ * x₂, mul_mem hx₁ hx₂⟩ : levelField jg M)
        = ⟨x₁, hx₁⟩ * ⟨x₂, hx₂⟩ from rfl, map_mul]
      exact Subfield.mul_mem _ ih₁ ih₂
  | inv x₁ hx₁ ih₁ =>
      show ψy ⟨x₁⁻¹, inv_mem hx₁⟩ ∈ (qExpand κ' p).fieldRange
      rw [show (⟨x₁⁻¹, inv_mem hx₁⟩ : levelField jg M)
        = (⟨x₁, hx₁⟩ : levelField jg M)⁻¹ from rfl, map_inv₀]
      exact Subfield.inv_mem _ ih₁

/-- **The value at every slot**: if `levelSeries jg p` lies in `levelField jg M` and is represented
there by a polynomial `g'`, then `g'` takes the same value at every slot of the `ζ ^ p`-slot product,
namely the `ε`-image of `levelSeries jg p` read at the level-`(p * M)` nome. The proof evaluates
`g'` through a conjugate `ψy` at the slot `y`; `ψy` maps into the `qExpand κ' p`-range, where the
`Φ_p`-dichotomy pins the image down to the distinguished slot. -/
private theorem eval_map_eq_of_mem_slotValues (ε : LaurentSeries κ →+* LaurentSeries κ')
    (jg : LaurentSeries κ) (hε : ε jg = jqModC κ')
    (hεq : ∀ (N : ℕ) [NeZero N] (x : LaurentSeries κ), ε (qExpand κ N x) = qExpand κ' N (ε x))
    {M p : ℕ} [NeZero M] [NeZero p] [hp : Fact (Nat.Prime p)] {ζ : κ'ˣ}
    (hpM : ¬ p ∣ M) (hζ : IsPrimitiveRoot (ζ : κ') (M * p))
    (hα : IsIntegral (baseField jg) (levelSeries jg M))
    (hroots : ((minpoly (baseField jg) (levelSeries jg M)).map (nomeMap ε jg (p * M))).roots
      = slotValues M (fun a b => qExpand κ' p (slotValue ε jg (ζ ^ p) a b)))
    (hmem : levelSeries jg p ∈ (levelField jg M : Set (LaurentSeries κ)))
    [Algebra (baseField jg) (LaurentSeries κ')]
    (halg : algebraMap (baseField jg) (LaurentSeries κ') = nomeMap ε jg (p * M))
    {g' : Polynomial (baseField jg)}
    (hg' : Polynomial.aeval (levelSeries jg M) g' = levelSeries jg p)
    {y : LaurentSeries κ'}
    (hy : y ∈ slotValues M (fun a b => qExpand κ' p (slotValue ε jg (ζ ^ p) a b))) :
    Polynomial.aeval y g' = ε (qExpand κ (p * M) (levelSeries jg p)) := by
  have hM0 : M ≠ 0 := NeZero.ne M
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have : NeZero (M * p) := ⟨Nat.mul_ne_zero hM0 hp0⟩
  have hζM : IsPrimitiveRoot ((ζ ^ p : κ'ˣ) : κ') M := by
    have h1 := isPrimitiveRoot_pow_div hζ (⟨p, rfl⟩ : M ∣ M * p)
    have h2 : M * p / M = p := Nat.mul_div_cancel_left p (Nat.pos_of_ne_zero hM0)
    rwa [h2] at h1
  have hζp : IsPrimitiveRoot ((ζ ^ M : κ'ˣ) : κ') p := by
    have h1 := isPrimitiveRoot_pow_div hζ (⟨M, Nat.mul_comm M p⟩ : p ∣ M * p)
    have h2 : M * p / p = M := Nat.mul_div_cancel M (Nat.pos_of_ne_zero hp0)
    rwa [h2] at h1
  have hιS : ∀ w : LaurentSeries κ,
      ε (qExpand κ (p * M) w) = qExpand κ' p (ε (qExpand κ M w)) := by
    intro w
    rw [hεq (p * M) w, hεq M w, ← qExpand_qExpand]
  obtain ⟨a₀, b₀, ha₀, hb₀, hyval⟩ := mem_slotValues.mp hy
  have hyS : y ∈ (qExpand κ' p).fieldRange := by
    rw [hyval]
    exact RingHom.mem_fieldRange.mpr ⟨slotValue ε jg (ζ ^ p) a₀ b₀, rfl⟩
  have hPne : ((minpoly (baseField jg) (levelSeries jg M)).map (nomeMap ε jg (p * M))) ≠ 0 :=
    ((minpoly.monic hα).map (nomeMap ε jg (p * M))).ne_zero
  have hy_root : ((minpoly (baseField jg) (levelSeries jg M)).map
      (nomeMap ε jg (p * M))).IsRoot y :=
    (Polynomial.mem_roots hPne).mp (by rw [hroots]; exact hy)
  obtain ⟨ψy, hψygen, -⟩ :=
    exists_algHom_adjoin_of_isRoot ε jg (M := p * M) (d := M) (y := y) hα hy_root halg
  have hψgen : ∀ h : levelSeries jg M ∈ (levelField jg M : Set (LaurentSeries κ)),
      ψy ⟨levelSeries jg M, h⟩ = y := by
    intro h
    exact hψygen
  have himg := map_mem_fieldRange ε jg (p := p) hψgen hyS hιS halg
  have hx_pS : ψy ⟨levelSeries jg p, hmem⟩ ∈ (qExpand κ' p).fieldRange := himg _ hmem
  obtain ⟨dp, -, -⟩ := exists_phiIrreducible_evalSymm p
  have hrel : (phiAtSeed dp jg).eval (levelSeries jg p) = 0 := by
    have h1 := seed_eval_zero ε jg hε hεq p dp 1
    rw [show levelSeries jg (1 * p) = levelSeries jg p from qExpand_congr (by ring) jg,
      show levelSeries jg 1 = jg from qExpand_one_apply jg] at h1
    exact h1
  have h1 : Polynomial.aeval (⟨levelSeries jg p, hmem⟩ : levelField jg M)
      (phiAtSeed dp (⟨jg, IntermediateField.subset_adjoin κ ({jg} : Set (LaurentSeries κ))
        rfl⟩ : baseField jg)) = 0 := by
    refine aeval_intermediateField_eq_zero ?_
    show Polynomial.aeval (levelSeries jg p)
      (phiAtSeed dp (⟨jg, IntermediateField.subset_adjoin κ ({jg} : Set (LaurentSeries κ))
        rfl⟩ : baseField jg)) = 0
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, phiAtSeed_map]
    exact hrel
  have hseed : nomeMap ε jg (p * M)
      (⟨jg, IntermediateField.subset_adjoin κ ({jg} : Set (LaurentSeries κ)) rfl⟩ :
        baseField jg)
      = qExpand κ' (p * M) (qTwist (((1 : κ'ˣ)) ^ p) (jqModC κ')) := by
    show ε (qExpand κ (p * M) jg) = _
    rw [hεq (p * M) jg, hε, one_pow, qTwist_one_apply]
  have h2 : (phiAtSeed dp (qExpand κ' (p * M) (qTwist (((1 : κ'ˣ)) ^ p) (jqModC κ')))).eval
      (ψy ⟨levelSeries jg p, hmem⟩) = 0 := by
    have h3 := Polynomial.aeval_algHom_apply ψy (⟨levelSeries jg p, hmem⟩ : levelField jg M)
      (phiAtSeed dp (⟨jg, IntermediateField.subset_adjoin κ ({jg} : Set (LaurentSeries κ))
        rfl⟩ : baseField jg))
    rw [h1, map_zero] at h3
    rw [Polynomial.aeval_def, halg, Polynomial.eval₂_eq_eval_map, phiAtSeed_map] at h3
    rwa [hseed] at h3
  have h2' : (dp.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries κ'))
      (qExpand κ' (p * M) (qTwist (((1 : κ'ˣ)) ^ p) (jqModC κ'))))).IsRoot
      (ψy ⟨levelSeries jg p, hmem⟩) := h2
  rcases (isRoot_prime_at_slot_iff_of_isPrimitiveRoot p (ζ ^ M) hζp dp M 1
    (ψy ⟨levelSeries jg p, hmem⟩)).mp h2' with hdist | ⟨b, hb, htw⟩
  · have hεp : ε (qExpand κ p jg) = qExpand κ' p (jqModC κ') := by
      rw [hεq p jg, hε]
    have hεM : ε (qExpand κ (p * M) (levelSeries jg p))
        = qExpand κ' (p * M) (qExpand κ' p (jqModC κ')) := by
      rw [hεq (p * M) (levelSeries jg p)]
      show qExpand κ' (p * M) (ε (qExpand κ p jg))
        = qExpand κ' (p * M) (qExpand κ' p (jqModC κ'))
      rw [hεp]
    have hspd : qExpand κ' (p * (p * M)) (qTwist (((1 : κ'ˣ)) ^ (p * p)) (jqModC κ'))
        = ε (qExpand κ (p * M) (levelSeries jg p)) := by
      rw [one_pow, qTwist_one_apply, hεM, qExpand_qExpand]
      exact qExpand_congr (by ring) _
    have hx_pval : ψy ⟨levelSeries jg p, hmem⟩ = ε (qExpand κ (p * M) (levelSeries jg p)) := by
      rw [hdist, hspd]
    have hgE : Polynomial.aeval
        (IntermediateField.AdjoinSimple.gen (baseField jg) (levelSeries jg M)) g'
        = (⟨levelSeries jg p, hmem⟩ : levelField jg M) := by
      have h3 := Polynomial.aeval_algHom_apply (IntermediateField.val (levelField jg M))
        (IntermediateField.AdjoinSimple.gen (baseField jg) (levelSeries jg M)) g'
      refine Subtype.ext ?_
      show ((Polynomial.aeval
        (IntermediateField.AdjoinSimple.gen (baseField jg) (levelSeries jg M)) g' :
          levelField jg M) : LaurentSeries κ) = levelSeries jg p
      rw [show ((Polynomial.aeval
        (IntermediateField.AdjoinSimple.gen (baseField jg) (levelSeries jg M)) g' :
          levelField jg M) : LaurentSeries κ)
        = (IntermediateField.val (levelField jg M))
          (Polynomial.aeval
            (IntermediateField.AdjoinSimple.gen (baseField jg) (levelSeries jg M)) g')
        from rfl, ← h3]
      exact hg'
    rw [← hψygen, Polynomial.aeval_algHom_apply, hgE, hx_pval]
  · exfalso
    obtain ⟨w, hw⟩ := RingHom.mem_fieldRange.mp hx_pS
    have hw2 : qExpand κ' p w = TS κ' M ((ζ ^ M) ^ b) := by
      rw [hw, htw, one_mul, TS]
    have hnd : ¬ ((p : ℤ) ∣ (-(M : ℤ))) := by
      rw [dvd_neg, Int.natCast_dvd_natCast]
      exact hpM
    have hz1 : (qExpand κ' p w).coeff (-(M : ℤ)) = 0 :=
      qExpand_coeff_of_not_dvd (R := κ') (N := p) w hnd
    have hz2 : (TS κ' M ((ζ ^ M) ^ b)).coeff (-(M : ℤ))
        = (((((ζ ^ M) ^ b)⁻¹ : κ'ˣ)) : κ') :=
      TS_coeff_neg (K := κ') M _
    rw [hw2, hz2] at hz1
    exact Units.ne_zero _ hz1

/-- **Prime non-membership in the level field**: for `p ∤ M` and the level-degree package at `M`,
the level-`p` series is not in the level-`M` field, unless it is already in the base field. The
contradiction reads `levelSeries jg p` as `g'(levelSeries jg M)` with `deg g' < ψ(M)`, shows `g'`
constant on the `ψ(M)` slots, and concludes `levelSeries jg p ∈ baseField jg` — the hypothesis that
fails. The two carrier premises are the ones `SlotProductAt` carries; they are what lets the slots be
read through `TS`, and the `RingHom.id` instance discharges them by `rfl`. -/
theorem prime_notMem_levelField (ε : LaurentSeries κ →+* LaurentSeries κ')
    (jg : LaurentSeries κ) (hε : ε jg = jqModC κ')
    (hεq : ∀ (N : ℕ) [NeZero N] (x : LaurentSeries κ), ε (qExpand κ N x) = qExpand κ' N (ε x))
    {M p : ℕ} [NeZero M] [NeZero p] [hp : Fact (Nat.Prime p)]
    {ζ : κ'ˣ} (hζ : IsPrimitiveRoot (ζ : κ') (M * p)) (hpM : ¬ p ∣ M) (h : PkgAt jg M)
    (hbase : levelSeries jg p ∉ (baseField jg : Set (LaurentSeries κ))) :
    levelSeries jg p ∉ levelField jg M := by
  classical
  intro hmem
  have hM0 : M ≠ 0 := NeZero.ne M
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have : NeZero (M * p) := ⟨Nat.mul_ne_zero hM0 hp0⟩
  have hζM : IsPrimitiveRoot ((ζ ^ p : κ'ˣ) : κ') M := by
    have h1 := isPrimitiveRoot_pow_div hζ (⟨p, rfl⟩ : M ∣ M * p)
    have h2 : M * p / M = p := Nat.mul_div_cancel_left p (Nat.pos_of_ne_zero hM0)
    rwa [h2] at h1
  obtain ⟨htM, -⟩ := h M dvd_rfl
  have hα : IsIntegral (baseField jg) (levelSeries jg M) := isIntegral_levelSeries jg M htM
  have hdeg : (minpoly (baseField jg) (levelSeries jg M)).natDegree = _root_.dedekindPsi M :=
    natDegree_minpoly_levelSeries jg M htM
  have hprod : pushedMinpolyAt ε jg M (p * M)
      = (slotPolynomial ε jg M (ζ ^ p)).map (qExpand κ' p) := by
    rw [pushedMinpolyAt_map_qExpand ε jg hεq (m := M) (k := p), pushedMinpolyAt_self,
      pushedMinpoly_eq_slotPolynomial ε jg hε hεq M hζM h]
  have hroots : (pushedMinpolyAt ε jg M (p * M)).roots
      = slotValues M (fun a b => qExpand κ' p (slotValue ε jg (ζ ^ p) a b)) := by
    rw [hprod, map_slotPolynomial, ← prod_slotValues]
    exact Polynomial.roots_multiset_prod_X_sub_C _
  let : Algebra (baseField jg) (LaurentSeries κ') := (nomeMap ε jg (p * M)).toAlgebra
  have halg : algebraMap (baseField jg) (LaurentSeries κ') = nomeMap ε jg (p * M) :=
    RingHom.algebraMap_toAlgebra _
  have hTcard : (slotValues M (fun a b => qExpand κ' p (slotValue ε jg (ζ ^ p) a b))).card
      = dedekindPsi M := card_slotValues hM0 _
  have hTnodup : (slotValues M (fun a b => qExpand κ' p (slotValue ε jg (ζ ^ p) a b))).Nodup :=
    nodup_slotValues_expanded ε jg hε hM0 hζM
  have hscard : (slotValues M (fun a b => qExpand κ' p (slotValue ε jg (ζ ^ p) a b))).toFinset.card
      = dedekindPsi M := by
    rw [Multiset.toFinset_card_of_nodup hTnodup]
    exact hTcard
  obtain ⟨g, hg⟩ : ∃ g : Polynomial (baseField jg),
      Polynomial.aeval (levelSeries jg M) g = levelSeries jg p := by
    have h1 := IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hα.isAlgebraic
    have h2 : levelSeries jg p ∈ Algebra.adjoin (baseField jg)
        ({levelSeries jg M} : Set (LaurentSeries κ)) := by
      rw [← h1]
      exact hmem
    rw [Algebra.adjoin_singleton_eq_range_aeval] at h2
    obtain ⟨g, hg⟩ := h2
    exact ⟨g, hg⟩
  set g' := g %ₘ (minpoly (baseField jg) (levelSeries jg M)) with hg'def
  have hg' : Polynomial.aeval (levelSeries jg M) g' = levelSeries jg p := by
    have hsplit := Polynomial.modByMonic_add_div g (minpoly (baseField jg) (levelSeries jg M))
    have h4 := congrArg (Polynomial.aeval (levelSeries jg M)) hsplit
    rw [map_add, map_mul, minpoly.aeval, zero_mul, add_zero] at h4
    rw [hg'def, h4]
    exact hg
  have hdegpos : 0 < (minpoly (baseField jg) (levelSeries jg M)).natDegree := by
    rw [hdeg]
    exact dedekindPsi_pos M hM0
  have hg'deg : g'.natDegree
      < (slotValues M (fun a b => qExpand κ' p (slotValue ε jg (ζ ^ p) a b))).toFinset.card := by
    rw [hscard]
    show g'.natDegree < _root_.dedekindPsi M
    rw [← hdeg]
    rcases eq_or_ne g' 0 with h0 | h0
    · rw [h0, Polynomial.natDegree_zero]
      exact hdegpos
    · exact Polynomial.natDegree_lt_natDegree h0
        (Polynomial.degree_modByMonic_lt g (minpoly.monic hα))
  have hval : ∀ y ∈ (slotValues M (fun a b => qExpand κ' p (slotValue ε jg (ζ ^ p) a b))).toFinset,
      Polynomial.aeval y g' = ε (qExpand κ (p * M) (levelSeries jg p)) := by
    intro y hy
    exact eval_map_eq_of_mem_slotValues ε jg hε hεq hpM hζ hα hroots hmem halg hg'
      (Multiset.mem_toFinset.mp hy)
  obtain ⟨z, hz⟩ := mem_range_of_eval_eq_const g' (ε (qExpand κ (p * M) (levelSeries jg p)))
    (slotValues M (fun a b => qExpand κ' p (slotValue ε jg (ζ ^ p) a b))).toFinset hg'deg hval
  rw [halg] at hz
  have hzval : (algebraMap (baseField jg) (LaurentSeries κ)) z = levelSeries jg p := by
    apply RingHom.injective (ε.comp (qExpand κ (p * M)))
    exact hz
  have hjpF : levelSeries jg p ∈ baseField jg := by
    rw [← hzval]
    exact z.2
  exact hbase hjpF

end ModularCurve
