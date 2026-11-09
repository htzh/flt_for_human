/-
  T19 wave 5 — the prime step at a general coefficient field.

  `levelSeries jg M ∈ levelField jg (M * p)` for a prime `p`: the level-`M` series already lies
  in the level-`(M * p)` field. This is the `Gen` step of the divisor induction — a prime buys
  exactly one new degree, and the *new* level series is what pays for it — and it is the positive
  half of the pair whose negative half is `prime_notMem_levelField` (the old level series is not
  in the smaller field). Both pinned statements are its instances: `ℚ`'s
  `jqN_div_mem_modularFunctionField` is `jqN M ∈ modularFunctionField (M * p)`, and the `C` layer's
  `jqNModC_mem_modularFunctionFieldC_mul_prime` is `jqNModC K M ∈ modularFunctionFieldC K (M * p)`,
  the two named fields being the carrier set of `levelField` (`coe_adjoin_baseField`).

  ## The seam

  As in the non-membership: the conclusion is over `κ`, the comparison runs in the second
  coefficient field `κ'` (a section variable `[Algebra κ κ']`, never a parameter), and `ζ` is a
  primitive `(M * p)`-th root there. `ℚ` manufactures `κ'` as the cyclotomic field; the `C` layer
  is handed one by its own statement. The only source condition is `jg = jqModC κ`.

  ## The argument

  Two polynomials over `F := levelField jg (M * p)`, read in `κ'` at the level-`(M * p)` nome:

  * `A`, the level-`p` equation `Φ_p` seeded at the base `j`-series: its roots are the conjugate
    and the `p` twists (`exists_phiAtSeed_roots`);
  * `B`, the transported minimal polynomial of the level-`M` series: monic, split, squarefree,
    with `x₀ = σ (qExpand κ (M * p) (levelSeries jg M))` as a root and every root a slot value
    (`exists_transported_minpoly`, which is where the package is spent).

  A common root is therefore a slot value that is also a root of `A`; the comparison rules out
  the conjugate's index (`slotLevel_ne_conjLevel`), and the twists reduce to `(M, 0)` with unit
  `1`, so the twist index vanishes (`slotUnit_eq_one_of_twistLevel`, `eq_zero_of_pow_eq_one`).
  `Polynomial.mem_range_of_unique_common_root` then puts `x₀` in the nome range, and the
  injectivity of the coefficient extension carries the membership back to `κ`
  (`mem_of_mem_range_levelNome`).
-/
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Generic.SlotProduct
import FLTForHuman.FieldTheory.CommonRoot

set_option autoImplicit false

noncomputable section

open Polynomial HahnSeries IntermediateField
open scoped IntermediateField

-- The tower instances: `Algebra (levelField jg N) (LaurentSeries κ)` is what `levelNomeMap`
-- reads its scalars through, and it is an instance of the adjoin-adjoin tower.
open scoped IntermediateField.algebraAdjoinAdjoin

namespace ModularCurve

variable {κ κ' : Type*} [Field κ] [Field κ'] [Algebra κ κ']

/-- The coefficient extension acting on Laurent series: the canonical map of `[Algebra κ κ']`,
extended coefficientwise (see `Generic/SlotProduct.lean`). -/
local notation "σ" =>
  (coeffMap (algebraMap κ κ') : LaurentSeries κ →+* LaurentSeries κ')

/-- **The level-field nome map**: read the level-`N` field in the working field, along the
level-`N` `q`-expansion and the coefficient extension. The theory's `nomeMap` is this map at
`baseField`; `levelField` contains the base field, so the certificate needs the level form. -/
private def levelNomeMap (jg : LaurentSeries κ)
    (N : ℕ) [NeZero N] : levelField jg N →+* LaurentSeries κ' :=
  ((coeffMap (algebraMap κ κ')).comp (qExpand κ N)).comp
    (algebraMap (levelField jg N) (LaurentSeries κ))

/-- The level of the certificate's slot `a`: `p * a ^ 2`. -/
private abbrev slotLevel (p a : ℕ) : ℕ := p * (a * a)

/-- The level of the conjugate root of the level-`p` equation: the certificate's slot level at
`a = M * p`. -/
private abbrev conjLevel (M p : ℕ) : ℕ := p * (p * (M * p * M))

/-- The level of the `p` twists of the level-`p` equation: the certificate's slot level at
`a = M`. -/
private abbrev twistLevel (M p : ℕ) : ℕ := (M * p) * M

/-- The `M`-th root of unity the certificate's slots are read at: the primitive `(M * p)`-th
root raised to the `p`. -/
private abbrev slotUnit (ζ : κ'ˣ) (p : ℕ) : κ'ˣ := ζ ^ p

/-- The slot root is primitive of order `M`. -/
private theorem isPrimitiveRoot_slotUnit {M p : ℕ} [NeZero M] [NeZero p]
    {ζ : κ'ˣ} (hζ : IsPrimitiveRoot (ζ : κ') (M * p)) :
    IsPrimitiveRoot ((slotUnit ζ p : κ'ˣ) : κ') M := by
  have h := isPrimitiveRoot_pow_div hζ (dvd_mul_right M p)
  rwa [show M * p / M = p from Nat.mul_div_cancel_left p (NeZero.pos M)] at h

/-- No divisor of `M` is the conjugate's slot index. -/
private theorem slotLevel_ne_conjLevel {M p a : ℕ} [NeZero M] [hp : Fact (Nat.Prime p)]
    (haM : a ∣ M) : conjLevel M p ≠ slotLevel p a := by
  simp only [conjLevel, slotLevel]
  intro he
  have h1 : p * (M * p * M) = a * a := Nat.eq_of_mul_eq_mul_left hp.out.pos he
  have h2 : a * a = (M * p) * (M * p) := by rw [← h1]; ring
  have h3 : a = M * p := Nat.mul_self_inj.mp h2
  have h4 : a ≤ M := Nat.le_of_dvd (NeZero.pos M) haM
  rw [h3] at h4
  have h5 : M * 1 < M * p := Nat.mul_lt_mul_of_pos_left hp.out.one_lt (NeZero.pos M)
  omega

/-- The twist's level is the slot at `a = M`, whose slot index range is `1`, so the certificate's
unit there is `1`. -/
private theorem slotUnit_eq_one_of_twistLevel {M p a b : ℕ} [NeZero M]
    [hp : Fact (Nat.Prime p)] {ζ : κ'ˣ} (hb : b < M / a)
    (he : twistLevel M p = slotLevel p a) : slotUnit ζ p ^ (b * a) = 1 := by
  simp only [twistLevel, slotLevel] at he
  have h1 : a * a = M * M := Nat.eq_of_mul_eq_mul_left hp.out.pos (by rw [← he]; ring)
  have h2 : a = M := Nat.mul_self_inj.mp h1
  have hb1 : b < 1 := by
    have h3 : M / a = 1 := by rw [h2, Nat.div_self (NeZero.pos M)]
    rwa [h3] at hb
  have hb0 : b = 0 := by omega
  rw [hb0, zero_mul, pow_zero]

/-- `ζ ^ (b * M) = 1` with `b < p` forces `b = 0`, `ζ` having order `M * p`. -/
private theorem eq_zero_of_pow_eq_one {M p b : ℕ} [NeZero M] [hp : Fact (Nat.Prime p)]
    {ζ : κ'ˣ} (hζ : IsPrimitiveRoot (ζ : κ') (M * p)) (hb : b < p)
    (h : ζ ^ (b * M) = 1) : b = 0 := by
  have hM : 0 < M := NeZero.pos M
  have hbM : b * M < M * p := by
    rw [mul_comm M p]
    exact Nat.mul_lt_mul_of_pos_right hb hM
  have huK : ((ζ : κ'ˣ) : κ') ^ (b * M) = 1 := by
    rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  have hbM0 : b * M = 0 :=
    hζ.pow_inj hbM (NeZero.pos (M * p)) (by rw [huK, pow_zero])
  rcases Nat.mul_eq_zero.mp hbM0 with h0 | h0
  · exact h0
  · exact absurd h0 (NeZero.ne M)

/-- **The level-`p` equation at the seed**: over `levelField jg (M * p)` there is a monic `A`
whose roots, read at the level-`(M * p)` nome, are the conjugate `j(q ^ (conjLevel M p))` and
the `p` twists `j(ζ ^ (b * M) q ^ (twistLevel M p))`. -/
private theorem exists_phiAtSeed_roots (jg : LaurentSeries κ) (hjg : jg = jqModC κ)
    {M p : ℕ} [NeZero M] [NeZero p] [hp : Fact (Nat.Prime p)] {ζ : κ'ˣ}
    (hζ : IsPrimitiveRoot (ζ : κ') (M * p)) :
    ∃ A : Polynomial (levelField jg (M * p)),
      A.Monic ∧
        ∀ y : LaurentSeries κ', A.eval₂ (levelNomeMap (κ' := κ') jg (M * p)) y = 0 ↔
          y = TS κ' (conjLevel M p) 1 ∨
            ∃ b < p, y = TS κ' (twistLevel M p) (ζ ^ (b * M)) := by
  obtain ⟨data, -, -⟩ := exists_phiIrreducible_evalSymm p
  have hζp : IsPrimitiveRoot ((ζ ^ M : κ'ˣ) : κ') p := by
    have h1 := isPrimitiveRoot_pow_div hζ (dvd_mul_left p M)
    rwa [show M * p / p = M from Nat.mul_div_cancel M (NeZero.pos p)] at h1
  have hmem : levelSeries jg (M * p) ∈ levelField jg (M * p) :=
    IntermediateField.subset_adjoin (baseField jg) _ rfl
  refine ⟨phiAtSeed data ⟨levelSeries jg (M * p), hmem⟩, phiAtSeed_monic data _, ?_⟩
  intro y
  have hx : levelNomeMap (κ' := κ') jg (M * p) ⟨levelSeries jg (M * p), hmem⟩
      = qExpand κ' (p * (M * p * M)) (qTwist ((1 : κ'ˣ) ^ p) (jqModC κ')) := by
    show σ (qExpand κ (M * p) (qExpand κ (M * p) jg))
      = qExpand κ' (p * (M * p * M)) (qTwist ((1 : κ'ˣ) ^ p) (jqModC κ'))
    rw [qExpand_qExpand (M * p) (M * p) jg,
      coeffMap_qExpand (algebraMap κ κ') ((M * p) * (M * p)) jg, hjg, coeffMap_jqModC,
      one_pow, qTwist_one_apply]
    exact qExpand_congr (by ring) _
  rw [Polynomial.eval₂_eq_eval_map, phiAtSeed_map, hx]
  refine (isRoot_prime_at_slot_iff_of_isPrimitiveRoot p (ζ ^ M) hζp data (M * p * M) 1 y).trans ?_
  simp only [TS, conjLevel, twistLevel, one_pow, qTwist_one_apply, one_mul]
  refine or_congr Iff.rfl ?_
  refine exists_congr fun b => ?_
  rw [show ((ζ : κ'ˣ) ^ M) ^ b = ζ ^ (b * M) from by rw [← pow_mul, Nat.mul_comm]]

/-- **A nome map does not see the order of a product level**: `M * p` and `p * M` are the same
nome, since the level enters only through the `q`-expansion. -/
private theorem nomeMap_mul_comm (jg : LaurentSeries κ)
    {M p : ℕ} [NeZero M] [NeZero p] :
    nomeMap (κ' := κ') jg (M * p) = nomeMap (κ' := κ') jg (p * M) := by
  refine RingHom.ext fun x => ?_
  show σ (qExpand κ (M * p) (algebraMap (baseField jg) (LaurentSeries κ) x))
    = σ (qExpand κ (p * M) (algebraMap (baseField jg) (LaurentSeries κ) x))
  rw [qExpand_congr (M := M * p) (K := p * M) (Nat.mul_comm M p)]

/-- **The certificate**: the transported minimal polynomial of the level-`M` series, read at the
level-`(M * p)` nome — monic, split, squarefree, with `x₀` a root, and every root a slot value.
The package at `M` is spent here, for the degree and for the slot product. -/
private theorem exists_transported_minpoly (jg : LaurentSeries κ) (hjg : jg = jqModC κ)
    {M p : ℕ} [NeZero M] [NeZero p] [Fact (Nat.Prime p)] {ζ : κ'ˣ}
    (hζ : IsPrimitiveRoot (ζ : κ') (M * p)) (h : PkgAt jg M) :
    ∃ B : Polynomial (levelField jg (M * p)),
      B.Monic ∧ (B.map (levelNomeMap (κ' := κ') jg (M * p))).Splits ∧
        (B.map (levelNomeMap (κ' := κ') jg (M * p))).roots.Nodup ∧
        B.eval₂ (levelNomeMap (κ' := κ') jg (M * p))
          (σ (qExpand κ (M * p) (levelSeries jg M))) = 0 ∧
        ∀ y : LaurentSeries κ', B.eval₂ (levelNomeMap (κ' := κ') jg (M * p)) y = 0 →
          ∃ (a : ℕ) (_ : NeZero a), a ∣ M ∧ ∃ b : ℕ, b < M / a ∧
            y = qExpand κ' p (slotValue (σ jg) (ζ ^ p) a b) := by
  classical
  have hσ : σ jg = jqModC κ' := by rw [hjg, coeffMap_jqModC]
  have hα : IsIntegral (baseField jg) (levelSeries jg M) :=
    isIntegral_levelSeries jg M (h M dvd_rfl).1
  have hζM : IsPrimitiveRoot ((ζ ^ p : κ'ˣ) : κ') M :=
    isPrimitiveRoot_slotUnit hζ
  have hcomp : (levelNomeMap (κ' := κ') jg (M * p)).comp
      (algebraMap (baseField jg) (levelField jg (M * p)) : baseField jg →+*
        levelField jg (M * p)) = nomeMap (κ' := κ') jg (M * p) := by
    refine RingHom.ext fun x => ?_
    rw [RingHom.comp_apply]
    show σ (qExpand κ (M * p) (algebraMap (levelField jg (M * p)) (LaurentSeries κ)
        (algebraMap (baseField jg) (levelField jg (M * p)) x)))
      = σ (qExpand κ (M * p) (algebraMap (baseField jg) (LaurentSeries κ) x))
    rfl
  set B : Polynomial (levelField jg (M * p)) :=
    (minpoly (baseField jg) (levelSeries jg M)).map
      (algebraMap (baseField jg) (levelField jg (M * p))) with hBdef
  have hBmonic : B.Monic := by
    rw [hBdef]
    exact (minpoly.monic hα).map _
  have hprod : B.map (levelNomeMap (κ' := κ') jg (M * p))
      = ∏ a ∈ M.divisors, ∏ b ∈ (Finset.range (M / a)).filter
          (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1),
          (Polynomial.X - Polynomial.C (qExpand κ' p (slotValue (σ jg) (ζ ^ p) a b))) := by
    rw [hBdef, Polynomial.map_map, hcomp, nomeMap_mul_comm jg (M := M) (p := p)]
    rw [show (minpoly (baseField jg) (levelSeries jg M)).map (nomeMap jg (p * M))
        = pushedMinpolyAt jg M (p * M) from rfl,
      pushedMinpolyAt_map_qExpand jg (m := M) (k := p), pushedMinpolyAt_self,
      pushedMinpoly_eq_slotPolynomial jg M hjg hζM h,
      map_slotPolynomial (σ jg) M (ζ ^ p) (qExpand κ' p)]
  refine ⟨B, hBmonic, ?_, ?_, ?_, ?_⟩
  · rw [hprod]
    exact Polynomial.Splits.prod fun _ _ =>
      Polynomial.Splits.prod fun _ _ => Polynomial.Splits.X_sub_C _
  · rw [hprod, ← prod_slotValues M (fun a b => qExpand κ' p (slotValue (σ jg) (ζ ^ p) a b)),
      roots_multiset_prod_X_sub_C]
    exact nodup_slotValues fun a b a' b' ha ha' hb hb' hcon =>
      slotValue_inj_slot (σ jg) hσ hζM (NeZero.ne M)
        (Nat.mem_divisors.mp ha).1 (Nat.mem_divisors.mp ha').1
        (Finset.mem_range.mp (Finset.mem_filter.mp hb).1)
        (Finset.mem_range.mp (Finset.mem_filter.mp hb').1)
        (RingHom.injective (qExpand κ' p) hcon)
  · rw [hBdef, Polynomial.eval₂_map, hcomp]
    show (minpoly (baseField jg) (levelSeries jg M)).eval₂ (nomeMap jg (M * p))
      (σ (qExpand κ (M * p) (levelSeries jg M))) = 0
    rw [show nomeMap jg (M * p)
        = ((σ).comp (qExpand κ (M * p))).comp (algebraMap (baseField jg) (LaurentSeries κ)) from rfl,
      ← Polynomial.eval₂_map]
    show Polynomial.eval₂ ((σ).comp (qExpand κ (M * p)))
      (σ (qExpand κ (M * p) (levelSeries jg M)))
      ((minpoly (baseField jg) (levelSeries jg M)).map
        (algebraMap (baseField jg) (LaurentSeries κ))) = 0
    rw [show σ (qExpand κ (M * p) (levelSeries jg M))
        = ((σ).comp (qExpand κ (M * p))) (levelSeries jg M) from rfl,
      Polynomial.eval₂_hom, Polynomial.eval_map, ← Polynomial.aeval_def, minpoly.aeval, map_zero]
  · intro y hy
    have hne : B.map (levelNomeMap (κ' := κ') jg (M * p)) ≠ 0 := (hBmonic.map _).ne_zero
    have hroots : y ∈ (B.map (levelNomeMap (κ' := κ') jg (M * p))).roots :=
      (Polynomial.mem_roots hne).mpr (by rwa [Polynomial.eval₂_eq_eval_map] at hy)
    rw [hprod, ← prod_slotValues M (fun a b => qExpand κ' p (slotValue (σ jg) (ζ ^ p) a b)),
      roots_multiset_prod_X_sub_C] at hroots
    obtain ⟨a, b, ha, hb, rfl⟩ := mem_slotValues.mp hroots
    have ha0 : a ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors ha)
    exact ⟨a, ⟨ha0⟩, Nat.dvd_of_mem_divisors ha, b,
      Finset.mem_range.mp (Finset.mem_filter.mp hb).1, rfl⟩

/-- **Undoing the nome reading**: a level-`N` series whose `σ`-image at the level-`N` nome lies in
the range of the level nome map is in `levelField jg N`. -/
private theorem mem_of_mem_range_levelNome (jg : LaurentSeries κ)
    {N : ℕ} [NeZero N] {y : LaurentSeries κ}
    (hy : σ (qExpand κ N y) ∈ (levelNomeMap (κ' := κ') jg N).range) :
    y ∈ levelField jg N := by
  obtain ⟨f, hf⟩ := RingHom.mem_range.mp hy
  have hf' : σ (qExpand κ N ((f : LaurentSeries κ))) = σ (qExpand κ N y) := by
    rw [← hf, levelNomeMap]
    rfl
  have hval : (f : LaurentSeries κ) = y :=
    RingHom.injective ((σ).comp (qExpand κ N)) hf'
  rw [← hval]
  exact f.2

/-- **The prime step**: for `p` prime, the level-`M` series lies in the level-`(M * p)` field,
given the level-degree package at `M`. The only source condition is `jg = jqModC κ`; at the `C`
layer's `Algebra K K` instance it is discharged by `rfl`. -/
theorem levelSeries_mem_levelField_mul_prime (jg : LaurentSeries κ)
    (hjg : jg = jqModC κ)
    {M p : ℕ} [NeZero M] [NeZero p] [hp : Fact (Nat.Prime p)]
    {ζ : κ'ˣ} (hζ : IsPrimitiveRoot (ζ : κ') (M * p)) (h : PkgAt jg M) :
    levelSeries jg M ∈ levelField jg (M * p) := by
  have hσ : σ jg = jqModC κ' := by rw [hjg, coeffMap_jqModC]
  obtain ⟨A, -, hA⟩ := exists_phiAtSeed_roots jg hjg (M := M) (p := p) (ζ := ζ) hζ
  have hx0 : σ (qExpand κ (M * p) (levelSeries jg M)) = TS κ' (twistLevel M p) 1 := by
    rw [TS, qTwist_one_apply]
    show σ (qExpand κ (M * p) (qExpand κ M jg)) = qExpand κ' ((M * p) * M) (jqModC κ')
    rw [qExpand_qExpand M (M * p) jg,
      coeffMap_qExpand (algebraMap κ κ') ((M * p) * M) jg, hjg, coeffMap_jqModC]
  have hxA : A.eval₂ (levelNomeMap (κ' := κ') jg (M * p))
      (σ (qExpand κ (M * p) (levelSeries jg M))) = 0 :=
    (hA (σ (qExpand κ (M * p) (levelSeries jg M)))).mpr
      (Or.inr ⟨0, hp.out.pos, by rw [zero_mul, pow_zero]; exact hx0⟩)
  obtain ⟨B, hBmonic, hBs, hBnd, hxB, hB⟩ :=
    exists_transported_minpoly jg hjg (M := M) (p := p) (ζ := ζ) hζ h
  let : Algebra (levelField jg (M * p)) (LaurentSeries κ') :=
    (levelNomeMap (κ' := κ') jg (M * p)).toAlgebra
  have huniq : ∀ y : LaurentSeries κ', Polynomial.aeval y A = 0 → Polynomial.aeval y B = 0 →
      y = σ (qExpand κ (M * p) (levelSeries jg M)) := by
    intro y hyA hyB
    obtain ⟨a, ha0, haM, b', hb', hyB'⟩ := hB y hyB
    rcases (hA y).mp hyA with hyA | ⟨b, hb, hyA⟩
    · rw [hyA] at hyB'
      have hcon : TS κ' (conjLevel M p) 1
          = TS κ' (slotLevel p a) (slotUnit ζ p ^ (b' * a)) := by
        rw [hyB', slotValue_eq_TS (σ jg) (ζ ^ p) a b' hσ, qExpand_TS p (a * a)]
      exact absurd (TS_injective hcon).1 (slotLevel_ne_conjLevel haM)
    · rw [hyA] at hyB'
      have hcon : TS κ' (twistLevel M p) (ζ ^ (b * M))
          = TS κ' (slotLevel p a) (slotUnit ζ p ^ (b' * a)) := by
        rw [hyB', slotValue_eq_TS (σ jg) (ζ ^ p) a b' hσ, qExpand_TS p (a * a)]
      obtain ⟨he, hu⟩ := TS_injective hcon
      have hb0 : b = 0 :=
        eq_zero_of_pow_eq_one hζ hb (by rw [hu, slotUnit_eq_one_of_twistLevel hb' he])
      rw [hb0] at hyA
      rw [hyA, zero_mul, pow_zero, hx0]
  exact mem_of_mem_range_levelNome jg
    (Polynomial.mem_range_of_unique_common_root B A hBmonic.ne_zero hBs hBnd _
      hxB hxA fun y hyB hyA => huniq y hyA hyB)

end ModularCurve
