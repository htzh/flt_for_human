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

  The `Φ_p` datum is the one object the comparison takes from the `ℚ` layer
  (`ModularPolynomialProperties.exists_phiIrreducible_evalSymm`, imported directly below instead of
  left to `Generic/SlotProduct`'s cone). The `obtain` at the top of `exists_phiAtSeed_roots` keeps
  the datum and discards the other two components: neither is idle (irreducibility is what supplies
  the minimal polynomial's degree, hence the datum's uniqueness that
  `isRoot_prime_at_slot_iff_of_isPrimitiveRoot`'s proof reads, and the symmetry is spent by the slot
  product's induction), but nothing in this file reads them.

  ## The argument

  Two polynomials over `F := levelField jg (M * p)`, read in `κ'` at the level-`(M * p)` nome:

  * `A`, the level-`p` equation `Φ_p` seeded at the base `j`-series: its roots are the conjugate
    and the `p` twists (`exists_phiAtSeed_roots`);
  * `B`, the transported minimal polynomial of the level-`M` series: monic, split, squarefree,
    with `x₀` as a root and every root a slot value (`exists_transported_minpoly`, which is
    where the package is spent).

  A common root is therefore a slot value that is also a root of `A`; the comparison rules out
  the conjugate's index (`slotLevel_ne_conjLevel`), and the twists reduce to `(M, 0)` with unit
  `1`, so the twist index vanishes (`slotUnit_eq_one_of_twistLevel`, `eq_zero_of_pow_eq_one`).
  `Polynomial.mem_range_of_unique_common_root` then puts `x₀` in the nome range, and the
  injectivity of the coefficient extension carries the membership back to `κ`
  (`mem_of_mem_range_levelNome`).
-/
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Generic.SlotProduct
import FLTForHuman.ModularCurve.ModularPolynomialProperties
import FLTForHuman.FieldTheory.CommonRoot

set_option autoImplicit false

noncomputable section

open Polynomial HahnSeries IntermediateField
open scoped IntermediateField IntermediateField.algebraAdjoinAdjoin

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

/-- **The source condition at the working field**: `jg`'s own `j`-series condition pushes along
the coefficient extension, so every read in `κ'` may take `σ jg` to be the working field's
`j`-series. -/
private theorem coeffMap_jqModC' {jg : LaurentSeries κ} (hjg : jg = jqModC κ) :
    σ jg = jqModC κ' := by
  rw [hjg, coeffMap_jqModC]

/-- The element whose membership in `levelField jg (M * p)` is the theorem: the `j`-series at
the level `M`, read at the level-`(M * p)` nome. -/
private abbrev x₀ (jg : LaurentSeries κ) (M p : ℕ) [NeZero M] [NeZero p] : LaurentSeries κ' :=
  (coeffMap (algebraMap κ κ') : LaurentSeries κ →+* LaurentSeries κ')
    (qExpand κ (M * p) (levelSeries jg M))

/-- The slot root is primitive of order `M`. -/
private theorem isPrimitiveRoot_slotUnit {M p : ℕ} [NeZero M] [NeZero p]
    {ζ : κ'ˣ} (hζ : IsPrimitiveRoot (ζ : κ') (M * p)) :
    IsPrimitiveRoot ((slotUnit ζ p : κ'ˣ) : κ') M := by
  have h := isPrimitiveRoot_pow_div hζ (dvd_mul_right M p)
  rwa [show M * p / M = p from Nat.mul_div_cancel_left p (NeZero.pos M)] at h

/-- **The other `p`-root**: `ζ ^ M` is primitive of order `p`, `ζ` having order `M * p`. The two
roots the comparison reads the level-`p` equation at are this one and `slotUnit`; the level's own
arithmetic is `isPrimitiveRoot_pow_div` plus a division cancellation. -/
private theorem isPrimitiveRoot_pow_mul {M p : ℕ} [NeZero M] [NeZero p]
    {ζ : κ'ˣ} (hζ : IsPrimitiveRoot (ζ : κ') (M * p)) :
    IsPrimitiveRoot ((ζ ^ M : κ'ˣ) : κ') p := by
  have h := isPrimitiveRoot_pow_div hζ (dvd_mul_left p M)
  rwa [show M * p / p = M from Nat.mul_div_cancel M (NeZero.pos p)] at h

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

/-- **Reading a level series at a higher nome**: `j(q ^ m)`, read at the level `k`, is the
untwisted `(k * m)`-th twist `TS κ' (k * m) 1` — the nome only moves the exponent and the extension
only moves the coefficients. This is what makes both the seed of the level-`p` equation (`k = m`)
and `x₀` (`m = M`, `k = M * p`) `TS` values, so neither consumer recomputes it. -/
private theorem levelSeries_nome_eq_TS (jg : LaurentSeries κ) (hjg : jg = jqModC κ)
    {m k : ℕ} [NeZero m] [NeZero k] :
    σ (qExpand κ k (levelSeries jg m)) = TS κ' (k * m) 1 := by
  rw [levelSeries, qExpand_qExpand m k jg, coeffMap_qExpand (algebraMap κ κ') (k * m) jg,
    coeffMap_jqModC' hjg, qExpand_jqModC_eq_TS]

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
  have hζp := isPrimitiveRoot_pow_mul hζ
  have hmem : levelSeries jg (M * p) ∈ levelField jg (M * p) :=
    IntermediateField.subset_adjoin (baseField jg) _ rfl
  refine ⟨phiAtSeed data ⟨levelSeries jg (M * p), hmem⟩, phiAtSeed_monic data _, ?_⟩
  intro y
  have hx : levelNomeMap (κ' := κ') jg (M * p) ⟨levelSeries jg (M * p), hmem⟩
      = TS κ' (p * (M * p * M)) ((1 : κ'ˣ) ^ p) := by
    show σ (qExpand κ (M * p) (levelSeries jg (M * p)))
      = TS κ' (p * (M * p * M)) ((1 : κ'ˣ) ^ p)
    rw [one_pow, levelSeries_nome_eq_TS jg hjg (m := M * p) (k := M * p)]
    exact TS_congr (e := (M * p) * (M * p)) (e' := p * (M * p * M)) (by ring) 1
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

/-- **A root of the slot product, read as a `TS` value**: the slot product writes its factors
as `qExpand κ' p (slotValue (σ jg) (ζ ^ p) a b)`, because `slotValue` is total in `a`; at a slot
index `a ≠ 0` the same value is the `TS` value of the corresponding twist. This is the only place
the two spellings meet, and it is what lets the comparison run in the `TS` vocabulary that
`TS_injective` reads. -/
private theorem qExpand_slotValue_eq_TS (jg : LaurentSeries κ) (hjg : jg = jqModC κ)
    {ζ : κ'ˣ} (p a b : ℕ) [NeZero p] [NeZero a] :
    qExpand κ' p (slotValue (σ jg) (ζ ^ p) a b)
      = TS κ' (slotLevel p a) (slotUnit ζ p ^ (b * a)) := by
  rw [slotValue_eq_TS (σ jg) (ζ ^ p) a b (coeffMap_jqModC' hjg), qExpand_TS p (a * a)]

/-- **`x₀` is a root of the pushed minimal polynomial**: the level-`M` series satisfies its minimal
polynomial over the base field, and `x₀` is that same series read through the nome map the
polynomial is pushed along — so pushing and evaluating at `x₀` is `minpoly.aeval` followed by
`g 0 = 0`. -/
private theorem x₀_isRoot (jg : LaurentSeries κ) {M p : ℕ} [NeZero M] [NeZero p] :
    ((minpoly (baseField jg) (levelSeries jg M)).map (nomeMap (κ' := κ') jg (M * p))).IsRoot
      (x₀ jg M p) := by
  have hx : x₀ jg M p = ((σ).comp (qExpand κ (M * p))) (levelSeries jg M) := rfl
  rw [Polynomial.IsRoot, Polynomial.eval_map, nomeMap, ← Polynomial.eval₂_map, hx,
    Polynomial.eval₂_hom, Polynomial.eval_map, ← Polynomial.aeval_def, minpoly.aeval, map_zero]

/-- **The certificate**: the transported minimal polynomial of the level-`M` series, read at the
level-`(M * p)` nome — monic, split, squarefree, with `x₀` a root, and every root a slot value.
The package at `M` is spent here, for the degree and for the slot product. -/
private theorem exists_transported_minpoly (jg : LaurentSeries κ) (hjg : jg = jqModC κ)
    {M p : ℕ} [NeZero M] [NeZero p] [Fact (Nat.Prime p)] {ζ : κ'ˣ}
    (hζ : IsPrimitiveRoot (ζ : κ') (M * p)) (h : PkgAt jg M) :
    ∃ B : Polynomial (levelField jg (M * p)),
      B.Monic ∧ (B.map (levelNomeMap (κ' := κ') jg (M * p))).Splits ∧
        (B.map (levelNomeMap (κ' := κ') jg (M * p))).roots.Nodup ∧
        B.eval₂ (levelNomeMap (κ' := κ') jg (M * p)) (x₀ jg M p) = 0 ∧
        ∀ y : LaurentSeries κ', B.eval₂ (levelNomeMap (κ' := κ') jg (M * p)) y = 0 →
          ∃ (a : ℕ) (_ : NeZero a), a ∣ M ∧ ∃ b : ℕ, b < M / a ∧
            y = TS κ' (slotLevel p a) (slotUnit ζ p ^ (b * a)) := by
  classical
  have hσ : σ jg = jqModC κ' := coeffMap_jqModC' hjg
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
    have hspine : B.map (levelNomeMap (κ' := κ') jg (M * p))
        = (slotPolynomial (σ jg) M (ζ ^ p)).map (qExpand κ' p) := by
      calc B.map (levelNomeMap (κ' := κ') jg (M * p))
          = pushedMinpolyAt (κ' := κ') jg M (M * p) := by
            show B.map (levelNomeMap (κ' := κ') jg (M * p))
              = (minpoly (baseField jg) (levelSeries jg M)).map (nomeMap (κ' := κ') jg (M * p))
            rw [hBdef, Polynomial.map_map, hcomp]
        _ = pushedMinpolyAt (κ' := κ') jg M (p * M) := by
            rw [pushedMinpolyAt, pushedMinpolyAt, nomeMap_mul_comm jg (M := M) (p := p)]
        _ = (pushedMinpolyAt (κ' := κ') jg M M).map (qExpand κ' p) := by
            rw [← pushedMinpolyAt_map_qExpand jg (m := M) (k := p)]
        _ = (pushedMinpoly (κ' := κ') jg M).map (qExpand κ' p) := by
            rw [pushedMinpolyAt_self]
        _ = (slotPolynomial (σ jg) M (ζ ^ p)).map (qExpand κ' p) := by
            rw [pushedMinpoly_eq_slotPolynomial jg M hjg hζM h]
    rw [hspine, map_slotPolynomial (σ jg) M (ζ ^ p) (qExpand κ' p)]
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
  · rw [hBdef, Polynomial.eval₂_map, hcomp, Polynomial.eval₂_eq_eval_map]
    exact x₀_isRoot jg
  · intro y hy
    have hne : B.map (levelNomeMap (κ' := κ') jg (M * p)) ≠ 0 := (hBmonic.map _).ne_zero
    have hroots : y ∈ (B.map (levelNomeMap (κ' := κ') jg (M * p))).roots :=
      (Polynomial.mem_roots hne).mpr (by rwa [Polynomial.eval₂_eq_eval_map] at hy)
    rw [hprod, ← prod_slotValues M (fun a b => qExpand κ' p (slotValue (σ jg) (ζ ^ p) a b)),
      roots_multiset_prod_X_sub_C] at hroots
    obtain ⟨a, b, ha, hb, h⟩ := mem_slotValues.mp hroots
    have ha0 : a ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors ha)
    have : NeZero a := ⟨ha0⟩
    exact ⟨a, ⟨ha0⟩, Nat.dvd_of_mem_divisors ha, b,
      Finset.mem_range.mp (Finset.mem_filter.mp hb).1, by rw [h, qExpand_slotValue_eq_TS jg hjg]⟩

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
  obtain ⟨A, -, hA⟩ := exists_phiAtSeed_roots jg hjg (M := M) (p := p) (ζ := ζ) hζ
  have hxA : A.eval₂ (levelNomeMap (κ' := κ') jg (M * p)) (x₀ jg M p) = 0 :=
    (hA (x₀ jg M p)).mpr (Or.inr ⟨0, hp.out.pos, by
      simpa using levelSeries_nome_eq_TS jg hjg (m := M) (k := M * p)⟩)
  obtain ⟨B, hBmonic, hBs, hBnd, hxB, hB⟩ :=
    exists_transported_minpoly jg hjg (M := M) (p := p) (ζ := ζ) hζ h
  let : Algebra (levelField jg (M * p)) (LaurentSeries κ') :=
    (levelNomeMap (κ' := κ') jg (M * p)).toAlgebra
  have huniq : ∀ y : LaurentSeries κ', Polynomial.aeval y A = 0 → Polynomial.aeval y B = 0 →
      y = x₀ jg M p := by
    intro y hyA hyB
    obtain ⟨a, _, haM, b', hb', hyB⟩ := hB y hyB
    rcases (hA y).mp hyA with hyA | ⟨b, hb, hyA⟩
    · rw [hyA] at hyB
      exact absurd (TS_injective hyB).1 (slotLevel_ne_conjLevel haM)
    · rw [hyA] at hyB
      obtain ⟨he, hu⟩ := TS_injective hyB
      have hb0 : b = 0 :=
        eq_zero_of_pow_eq_one hζ hb (by rw [hu, slotUnit_eq_one_of_twistLevel hb' he])
      subst b
      simpa [levelSeries_nome_eq_TS jg hjg (m := M) (k := M * p)] using hyA
  exact mem_of_mem_range_levelNome jg
    (Polynomial.mem_range_of_unique_common_root B A hBmonic.ne_zero hBs hBnd _
      hxB hxA fun y hyB hyA => huniq y hyA hyB)

end ModularCurve
