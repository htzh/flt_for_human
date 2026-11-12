/-
  The slot product at a general coefficient field.

  ## The two fields

  The theory is read at **two** coefficient fields, `κ` (where the `j`-series and its minimal
  polynomial live) and `κ'` (where the roots of `Φ_p` live), joined by a section variable
  `[Algebra κ κ']`. The carrier map `σ := coeffMap (algebraMap κ κ')` extends the coefficient
  extension to Laurent series; it is *not* a parameter of the theory, and no statement carries it
  as an argument. It earns its place in exactly four facts, each a theorem and none a hypothesis:
  it is the canonical map of `[Algebra κ κ']`, it commutes with the nome (`coeffMap_qExpand`), it
  fixes the j-series (`coeffMap_jqModC`), and it is injective (`coeffMap_injective`, a field map).

  Where the two fields appear is deliberate: the pushed minimal polynomial (`nomeMap`,
  `pushedMinpolyAt`) is over the base field of `κ` and read in `κ'`, while the slot objects
  (`slotValue`, `slotPolynomial`, `TS`, the `Φ_p` root shapes) live at the **one** field that
  carries the root. So the slot objects are stated in `Generic/SlotValue.lean` at one field, and
  every two-field statement below reads them at `σ jg`.

  ## The objects

  Three terms were spelled out at every use in the `ℚ` layer, so each gets a name and the
  statements below are written in terms of them:

  * `nomeMap jg M` — read the base field at the level-`M` nome, in the working coefficient field:
    the coefficient extension, composed with the level-`M` `q`-expansion and the inclusion of the
    base field into `κ((q))`.
  * `pushedMinpoly jg M` — the minimal polynomial of the level-`M` series over the base, read in
    the working field along `nomeMap`.
  * `slotPolynomial (σ jg) ζ M` — the slot product: the product of `X - slotValue ζ a b` over the
    slot multiset. The object is the multiset product; its pin spelling — the iterated
    `∏ a ∈ M.divisors, ∏ b ∈ …` product — is `slotPolynomial_eq_prod`, and `map_slotPolynomial` is
    the same product mapped through an arbitrary carrier `LaurentSeries κ' →+* S`.

  ## The statements

  `SlotProductAt jg M ζ` is the induction statement — "if `jg` is the j-series, `ζ` is a primitive
  `M`-th root and the level-degree package holds at `M`, the pushed minimal polynomial is the slot
  polynomial" — and `pushedMinpoly_eq_slotPolynomial` is the headline it proves. The strong
  induction is `slotProductInduction`. The premises stay inside the `Prop` so that the induction
  statement and the headline keep one shape.

  ## The induction

  `slotProductInduction` is the abstracted form of the `ℚ` layer's `rval_aux`
  (`FunctionFieldGeneration/SlotProduct.lean`), with the source condition `jg = jqModC κ` supplying
  what `coeffEmb_jq` supplies there, `coeffMap_qExpand` supplying `coeffEmb_qExpand`, and `PkgAt`
  supplying the `Hall` conjunction. The steps, in the order the `ℚ` proof takes them, are
  `minpoly_map_eq_prod_slots_one` (the base case), `isRoot_map_minpoly_slot_top` (the `a = M`
  slot), `finrank_adjoin_mul_dedekindPsi` (the tower law at a divisor),
  `isRoot_qExpand_slot_of_slotProduct` (the descended slot, from the induction hypothesis) and
  `isRoot_map_minpoly_slot_of_descent` (the main case, resting on `slotValue_ne_image_of_dvd` and
  on the two prime cases `isRoot_map_minpoly_slot_of_dvd` and `…_of_not_dvd`);
  `isRoot_map_minpoly_slot` collects the slot roots, and `slotProductInduction` closes on the root
  count.

  Three imports are new relative to the object layer, and each is spent at exactly one step:

  * `PhiGenSplitsAnyField` for `PhiGen.splits_prime_at_slot_of_isPrimitiveRoot` — the field-generic
    `Φ_p` splitting, which takes the order-`p` primitive root `ζ ^ (M / p)` and reads the slot at
    `jqModC κ'`. The `ℚ` layer's `PhiGen.splits_prime_at_slot` spends `[Algebra ℚ K]` and is not
    available here.
  * `Degree/JqCyclotomicConjugates` for `phiAtSeed_jqNModC_eval` and its symmetric form — the
    modular relation `Φ_n(j(q ^ d), j(q ^ (d n))) = 0` over an arbitrary coefficient ring. The `ℚ`
    layer's `phiAtSeed_jqN_eval` and `phiAtSeed_eval_symm` are stated over `LaurentSeries ℚ`; here
    the relation is pulled back along `σ` (`seed_eval_zero`, `seed_eval_zero_symm`), which is
    injective because it is a coefficient extension of fields.
  * `ModularPolynomialProperties` for `exists_phiIrreducible_evalSymm` — the irreducible symmetric
    modular polynomial datum, which the descent uses as an input, as at `ℚ`.

  Every induction step is `private`: the theory's interface is the three objects, the two spelling
  bridges (`slotPolynomial_eq_prod`, `map_slotPolynomial`), `SlotProductAt` and the two headlines.
  `map_qExpand_slotPolynomial` — the descent's reading of individual factors after the `qExpand`
  push — is `map_slotPolynomial` at `g = qExpand κ' k`.

  `dedekindPsi` has two spellings in scope in this module — `_root_.dedekindPsi` (what `degreeAt`,
  `PkgAt` and `natDegree_minpoly_levelSeries` are stated with) and `ModularCurve.dedekindPsi`
  (`ModularCurve/Defs/DedekindPsi.lean`, a `def` alias that shadows the root name inside the
  namespace, and what `card_slotValues` is stated with). The new statements below write
  `_root_.dedekindPsi`; the one place the two meet is the closing squeeze, where the alias is
  `rfl`-equal to the root name.
-/
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Generic.SlotValue
import FLTForHuman.ModularCurve.ModularEquation.Split
import FLTForHuman.ModularCurve.Defs.PhiAtSlot
import FLTForHuman.ModularCurve.Defs.Cyclotomic
import FLTForHuman.ModularCurve.Degree.JqCyclotomicConjugates
import FLTForHuman.ModularCurve.ModularEquation.Existence

set_option autoImplicit false

noncomputable section

open Polynomial HahnSeries IntermediateField
open scoped IntermediateField

namespace ModularCurve

variable {κ κ' : Type*} [Field κ] [Field κ'] [Algebra κ κ']

/-- The coefficient extension acting on Laurent series: the canonical map of `[Algebra κ κ']`,
extended coefficientwise. Not a parameter of the theory — a notation for the one carrier map the
two fields induce. -/
local notation "σ" =>
  (coeffMap (algebraMap κ κ') : LaurentSeries κ →+* LaurentSeries κ')

/-- **Reading the `j`-line at the level-`M` nome**, in the working coefficient field: the
coefficient extension, then the level-`M` `q`-expansion, then the inclusion of the base field into
`κ((q))`. One of the two two-field definitions of the theory. -/
def nomeMap (jg : LaurentSeries κ) (M : ℕ) [NeZero M] : baseField jg →+* LaurentSeries κ' :=
  ((coeffMap (algebraMap κ κ')).comp (qExpand κ M)).comp
    (algebraMap (baseField jg) (LaurentSeries κ))

/-- **The pushed minimal polynomial**: the minimal polynomial of the level-`M` series over the base
field, read in the working field along `nomeMap`. The other two-field definition. -/
def pushedMinpoly (jg : LaurentSeries κ) (M : ℕ) [NeZero M] : Polynomial (LaurentSeries κ') :=
  (minpoly (baseField jg) (levelSeries jg M)).map (nomeMap jg M)

/-- **The pushed minimal polynomial read at a higher nome**: the minimal polynomial of the
level-`m` series over the base, read at the level-`N` nome of the working field. `pushedMinpoly` is
the diagonal case `N = m`; the descent needs the off-diagonal case `N = k * m`. -/
def pushedMinpolyAt (jg : LaurentSeries κ) (m : ℕ) [NeZero m] (N : ℕ) [NeZero N] :
    Polynomial (LaurentSeries κ') :=
  (minpoly (baseField jg) (levelSeries jg m)).map (nomeMap jg N)

/-- **The diagonal case**: reading the level-`m` minimal polynomial at the level-`m` nome is
`pushedMinpoly`. Definitional, so that the two-level object never drifts from the headline one. -/
theorem pushedMinpolyAt_self (jg : LaurentSeries κ) (m : ℕ) [NeZero m] :
    pushedMinpolyAt (κ' := κ') jg m m = pushedMinpoly (κ' := κ') jg m := rfl

/-- The source condition at the carrier: `jg`'s own j-series condition pushes to `σ jg`. -/
private theorem coeffMap_jqModC' {jg : LaurentSeries κ} (hjg : jg = jqModC κ) :
    σ jg = jqModC κ' := by
  rw [hjg, coeffMap_jqModC]

/-- **`nomeMap` at a composite nome**: the level-`m` nome map, followed by the `k`-fold
`q`-expansion in the working field, is the level-`(k * m)` nome map. The coefficient extension
moves the `q`-expansion through by `coeffMap_qExpand`; `qExpand_qExpand` then composes the levels. -/
private theorem nomeMap_comp_qExpand (jg : LaurentSeries κ) (k : ℕ) [NeZero k] {m : ℕ}
    [NeZero m] :
    (qExpand κ' k).comp (nomeMap jg m) = nomeMap jg (k * m) := by
  refine RingHom.ext fun x => ?_
  show qExpand κ' k (σ (qExpand κ m (algebraMap (baseField jg) (LaurentSeries κ) x)))
    = σ (qExpand κ (k * m) (algebraMap (baseField jg) (LaurentSeries κ) x))
  rw [coeffMap_qExpand (algebraMap κ κ') m (algebraMap (baseField jg) (LaurentSeries κ) x),
    qExpand_qExpand m k (σ (algebraMap (baseField jg) (LaurentSeries κ) x)),
    coeffMap_qExpand (algebraMap κ κ') (k * m) (algebraMap (baseField jg) (LaurentSeries κ) x)]

/-- **Reading the same minimal polynomial at a higher nome**: the level-`m` minimal polynomial
pushed at the level-`(k * m)` nome is the `k`-fold `q`-expansion of its level-`m` reading. This is
the `ℚ` layer's `map_qExpand_minpoly_eq` without the slot product; it spends no hypothesis. -/
theorem pushedMinpolyAt_map_qExpand (jg : LaurentSeries κ) {m k : ℕ} [NeZero m] [NeZero k] :
    pushedMinpolyAt (κ' := κ') jg m (k * m)
      = (pushedMinpolyAt (κ' := κ') jg m m).map (qExpand κ' k) := by
  have hcomp := nomeMap_comp_qExpand (κ' := κ') jg k (m := m)
  show (minpoly (baseField jg) (levelSeries jg m)).map (nomeMap jg (k * m))
    = ((minpoly (baseField jg) (levelSeries jg m)).map (nomeMap jg m)).map (qExpand κ' k)
  rw [Polynomial.map_map, hcomp]

/-- **The slot product**, as a polynomial: the product of `X - slotValue ζ a b` over the slot
multiset. One field — the field that carries `ζ` (see `Generic/SlotValue.lean`). -/
def slotPolynomial (jg : LaurentSeries κ) (M : ℕ) (ζ : κˣ) : Polynomial (LaurentSeries κ) :=
  ((slotValues M (fun a b => slotValue jg ζ a b)).map
    (fun r => Polynomial.X - Polynomial.C r)).prod

/-- **The slot product, iterated**: the multiset product above written as the pin's
`∏ a ∈ M.divisors, ∏ b ∈ (range (M / a)).filter (gcd (gcd a b) (M / a) = 1)` product. Public
because every consumer that keeps the pin's iterated spelling needs it, and it was the one bridge
standing between the `ℚ` surface and a one-line delegation: the two spellings are the same
polynomial, and no slot content is touched. -/
theorem slotPolynomial_eq_prod (jg : LaurentSeries κ) (M : ℕ) (ζ : κˣ) :
    slotPolynomial jg M ζ = ∏ a ∈ M.divisors, ∏ b ∈ (Finset.range (M / a)).filter
        (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1),
        (Polynomial.X - Polynomial.C (slotValue jg ζ a b)) :=
  prod_slotValues M _

/-- **Mapping the slot product through a ring hom**, iterated: the map acts on the slot values
factorwise, for a target `S` that need only be a commutative ring — so a consumer with its own
carrier (a `q`-expansion into a further field, a comparison map) reuses this instead of re-deriving
`Polynomial.map_prod` over the iterated spelling. A commutative *semiring* does not do: the factors
are `X - C ·`, and `Sub R[X]` needs `Ring R`. -/
theorem map_slotPolynomial (jg : LaurentSeries κ) (M : ℕ) (ζ : κˣ) {S : Type*} [CommRing S]
    (g : LaurentSeries κ →+* S) :
    (slotPolynomial jg M ζ).map g = ∏ a ∈ M.divisors, ∏ b ∈ (Finset.range (M / a)).filter
        (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1),
        (Polynomial.X - Polynomial.C (g (slotValue jg ζ a b))) := by
  rw [slotPolynomial_eq_prod, Polynomial.map_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Polynomial.map_prod]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]

/-- **The slot-product statement at `M`.** A `def`, not an `abbrev`: as an `abbrev` it would
re-unfold at every use, and the strong induction passes it around as a hypothesis.

The source condition comes first because the statement is false without it: `slotPolynomial` reads
the slots through `σ jg`, while `pushedMinpoly` reads the minimal polynomial through
`σ ∘ qExpand`. At `jg = 0`, for instance, the left side is `0` and the right side is `X ^ ψ(M)`.
Its premises are premises of the `Prop` rather than arguments so that the induction statement and
the headline keep one shape. -/
def SlotProductAt (jg : LaurentSeries κ) (M : ℕ) [NeZero M] (ζ : κ'ˣ) : Prop :=
  jg = jqModC κ →
    IsPrimitiveRoot (ζ : κ') M → PkgAt jg M →
      pushedMinpoly jg M = slotPolynomial (σ jg) M ζ

/-- **Transfer to the base field**: a root of the `ψ`-push of the minimal polynomial over
`levelField jg d` is a root of the `nomeMap jg M`-push of the minimal polynomial over
`baseField jg`: the base minimal polynomial maps into the level field as a multiple of the
level-minimal polynomial. -/
private theorem isRoot_map_minpoly_of_isRoot_subfield
    {jg : LaurentSeries κ} {M d : ℕ} [NeZero M] [NeZero d]
    {ψ : levelField jg d →+* LaurentSeries κ'}
    (hψcomp : ψ.comp (algebraMap (baseField jg) (levelField jg d)) = nomeMap jg M)
    {x : LaurentSeries κ'}
    (hroot : ((minpoly (levelField jg d) (levelSeries jg M)).map ψ).IsRoot x) :
    ((minpoly (baseField jg) (levelSeries jg M)).map (nomeMap jg M)).IsRoot x := by
  have htowdvd : minpoly (levelField jg d) (levelSeries jg M)
      ∣ (minpoly (baseField jg) (levelSeries jg M)).map
        (algebraMap (baseField jg) (levelField jg d)) :=
    minpoly.dvd_map_of_isScalarTower (baseField jg) (levelField jg d) (levelSeries jg M)
  have h1 := Polynomial.map_dvd ψ htowdvd
  rw [Polynomial.map_map] at h1
  rw [hψcomp] at h1
  exact Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero h1 hroot

/-- **A root of the pushed minimal polynomial extends to the level field**: if `y` is a root of
`minpoly (baseField jg) (levelSeries jg d)` read in the working field along `nomeMap jg M`, then `y`
is the image of the level-`d` generator under a `baseField jg`-algebra map `ψ` out of
`levelField jg d`, and the push of scalars along `ψ` is `nomeMap jg M`. The `AlgHom` needs the
`Algebra (baseField jg) (LaurentSeries κ')` of the caller, which is why it is taken as an instance
argument here.

The descent calls this at `d = a * d''` and at the expanded slot value; the non-membership calls it
at `d = M` and at an arbitrary slot of the pushed polynomial, which is why it is stated at a general
level and a general root. -/
theorem exists_algHom_adjoin_of_isRoot (jg : LaurentSeries κ) {M d : ℕ} [NeZero M] [NeZero d]
    {y : LaurentSeries κ'}
    (hα : IsIntegral (baseField jg) (levelSeries jg d))
    (hroot : ((minpoly (baseField jg) (levelSeries jg d)).map (nomeMap jg M)).IsRoot y)
    [Algebra (baseField jg) (LaurentSeries κ')]
    (halg : algebraMap (baseField jg) (LaurentSeries κ') = nomeMap jg M) :
    ∃ ψ : levelField jg d →ₐ[baseField jg] LaurentSeries κ',
      ψ (IntermediateField.AdjoinSimple.gen (baseField jg) (levelSeries jg d)) = y
        ∧ (ψ : levelField jg d →+* LaurentSeries κ').comp
            (algebraMap (baseField jg) (levelField jg d)) = nomeMap jg M := by
  have hy_mem : y ∈ (minpoly (baseField jg) (levelSeries jg d)).aroots (LaurentSeries κ') := by
    rw [Polynomial.mem_aroots]
    refine ⟨minpoly.ne_zero hα, ?_⟩
    rw [Polynomial.aeval_def, halg, Polynomial.eval₂_eq_eval_map]
    exact hroot
  obtain ⟨ψ, hψ⟩ : ∃ ψ : levelField jg d →ₐ[baseField jg] LaurentSeries κ',
      ψ (IntermediateField.AdjoinSimple.gen (baseField jg) (levelSeries jg d)) = y :=
    ⟨(IntermediateField.algHomAdjoinIntegralEquiv (baseField jg) hα).symm ⟨_, hy_mem⟩,
      IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen (baseField jg) hα ⟨_, hy_mem⟩⟩
  refine ⟨ψ, hψ, ?_⟩
  rw [AlgHom.comp_algebraMap]
  exact halg

/-- **The slot polynomial at a higher level**: the `k`-fold `q`-expansion of the slot polynomial is
the product of the expanded slot values — the public `map_slotPolynomial` at `g = qExpand κ k`,
restated in the descent's argument order so that its uses read as they did. -/
theorem map_qExpand_slotPolynomial (jg : LaurentSeries κ) (k : ℕ) [NeZero k] {M : ℕ} [NeZero M]
    (ζ : κˣ) :
    (slotPolynomial jg M ζ).map (qExpand κ k)
      = ∏ a ∈ M.divisors, ∏ b ∈ (Finset.range (M / a)).filter
          (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1),
          (Polynomial.X - Polynomial.C (qExpand κ k (slotValue jg ζ a b))) :=
  map_slotPolynomial jg M ζ (qExpand κ k)

/-- **The base case `M = 1`**: `levelSeries jg 1 = jg` already lies in the base field, so its minimal
polynomial is `X - C jg`; the slot product has the single slot `slotValue (σ jg) ζ 1 0 = σ jg`, and
the base field element is read at `σ jg` as well. No hypothesis is spent. -/
private theorem minpoly_map_eq_prod_slots_one (jg : LaurentSeries κ) (ζ : κ'ˣ) :
    pushedMinpoly jg 1 = slotPolynomial (σ jg) 1 ζ := by
  have hgen : levelSeries jg 1 = algebraMap (baseField jg) (LaurentSeries κ)
      (⟨jg, IntermediateField.subset_adjoin κ ({jg} : Set (LaurentSeries κ)) rfl⟩ :
        baseField jg) := by
    show qExpand κ 1 jg = jg
    rw [qExpand_one_apply]
  have hmin : minpoly (baseField jg) (levelSeries jg 1)
      = Polynomial.X - Polynomial.C
        (⟨jg, IntermediateField.subset_adjoin κ ({jg} : Set (LaurentSeries κ)) rfl⟩ :
          baseField jg) := by
    rw [hgen]
    exact minpoly.eq_X_sub_C (B := LaurentSeries κ) _
  rw [pushedMinpoly, hmin, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rw [slotPolynomial, prod_slotValues, Nat.divisors_one, Finset.prod_singleton,
    show (Finset.range (1 / 1)).filter
      (fun b => Nat.gcd (Nat.gcd 1 b) (1 / 1) = 1) = {0} from by decide,
    Finset.prod_singleton]
  have hnom : nomeMap jg 1
      (⟨jg, IntermediateField.subset_adjoin κ ({jg} : Set (LaurentSeries κ)) rfl⟩ :
        baseField jg) = σ jg := by
    show σ (qExpand κ 1 jg) = σ jg
    rw [qExpand_one_apply]
  have hslot : slotValue (σ jg) ζ 1 0 = σ jg := by
    unfold slotValue
    rw [dite_eq_right (NeZero.ne (1 : ℕ)), zero_mul, pow_zero, qTwist_one_apply]
    show qExpand κ' (1 * 1) (σ jg) = σ jg
    rw [qExpand_one_apply]
  rw [hnom, hslot]

/-- **The slot at the top divisor**: for `a = M` (i.e. `M / a = 1`) the only slot is `b = 0`, and
`slotValue (σ jg) ζ M 0` is the level-`M` nome of `levelSeries jg M` in the working field, so it is
a root of the pushed minimal polynomial by definition of `minpoly`. -/
private theorem isRoot_map_minpoly_slot_top (jg : LaurentSeries κ)
    {M a b : ℕ} [NeZero M] {ζ : κ'ˣ} (haM : a ∣ M) (hd1 : M / a = 1)
    (hb : b ∈ (Finset.range (M / a)).filter
      (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1)) :
    (pushedMinpoly jg M).IsRoot (slotValue (σ jg) ζ a b) := by
  have had : a * (M / a) = M := Nat.mul_div_cancel' haM
  have hbr : b < M / a := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
  have haM' : a = M := by rw [hd1, mul_one] at had; exact had
  have hb0 : b = 0 := by omega
  subst hb0
  rw [show slotValue (σ jg) ζ a 0 = slotValue (σ jg) ζ M 0 from by rw [haM'], slotValue_top]
  have hgx : ((σ).comp (qExpand κ M)) (levelSeries jg M) = qExpand κ' (M * M) (σ jg) := by
    show σ (qExpand κ M (qExpand κ M jg)) = qExpand κ' (M * M) (σ jg)
    rw [qExpand_qExpand M M jg, coeffMap_qExpand (algebraMap κ κ') (M * M) jg]
  rw [pushedMinpoly]
  show (((minpoly (baseField jg) (levelSeries jg M)).map
    (((σ).comp (qExpand κ M)).comp (algebraMap (baseField jg) (LaurentSeries κ))))).IsRoot
    (qExpand κ' (M * M) (σ jg))
  rw [← hgx, Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.hom_eval₂]
  have h0 : Polynomial.eval₂ (algebraMap (baseField jg) (LaurentSeries κ)) (levelSeries jg M)
      (minpoly (baseField jg) (levelSeries jg M)) = 0 := by
    rw [← Polynomial.aeval_def]
    exact minpoly.aeval _ _
  rw [h0, map_zero]

/-- **The degree step at a divisor**: adjoining `levelSeries jg M` to `levelField jg d` multiplies the
degree by `ψ(d)`, i.e. `[top : levelField jg d] * ψ(d) = ψ(M)`. The iterated adjoin collapses to
`levelField jg M` because `levelSeries jg d` already lies in it — the generation clause of the
package, read through `coe_adjoin_baseField`. -/
private theorem finrank_adjoin_mul_dedekindPsi {jg : LaurentSeries κ} {M d : ℕ} [NeZero M]
    [NeZero d] (hd : d ∣ M) (htM : degreeAt jg M) (hgM : generatedAt jg M) (htd : degreeAt jg d) :
    Module.finrank (levelField jg d) ((levelField jg d)⟮levelSeries jg M⟯) * _root_.dedekindPsi d
      = _root_.dedekindPsi M := by
  have hfreeMid : Module.Free (baseField jg) (levelField jg d) := Module.Free.of_divisionRing _ _
  have hfreeTop : Module.Free (levelField jg d) ((levelField jg d)⟮levelSeries jg M⟯) :=
    Module.Free.of_divisionRing _ _
  have htow := Module.finrank_mul_finrank (baseField jg) (levelField jg d)
    ((levelField jg d)⟮levelSeries jg M⟯)
  have hmem : levelSeries jg d ∈ (levelField jg M : Set (LaurentSeries κ)) := by
    have h1 : levelSeries jg d ∈ ((IntermediateField.adjoin (baseField jg)
        ({levelSeries jg M} : Set (LaurentSeries κ))) : Set (LaurentSeries κ)) := by
      rw [coe_adjoin_baseField, hgM]
      exact IntermediateField.subset_adjoin κ _ (Or.inr ⟨d, ‹NeZero d›, hd, rfl⟩)
    exact h1
  have habs : IntermediateField.adjoin (baseField jg)
      (({levelSeries jg d} : Set (LaurentSeries κ)) ∪ {levelSeries jg M})
      = levelField jg M := by
    refine le_antisymm (IntermediateField.adjoin_le_iff.mpr ?_)
      (IntermediateField.adjoin.mono _ _ _ Set.subset_union_right)
    rintro z (hz | hz)
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      exact hmem
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      exact IntermediateField.subset_adjoin _ _ rfl
  have htop : Module.finrank (baseField jg) ((levelField jg d)⟮levelSeries jg M⟯)
      = _root_.dedekindPsi M := by
    have h1 := IntermediateField.adjoin_adjoin_left (baseField jg)
      ({levelSeries jg d} : Set (LaurentSeries κ)) {levelSeries jg M}
    have h2 : Module.finrank (baseField jg)
        (IntermediateField.restrictScalars (baseField jg) ((levelField jg d)⟮levelSeries jg M⟯))
        = Module.finrank (baseField jg) ((levelField jg d)⟮levelSeries jg M⟯) := rfl
    rw [← h2, h1, habs]
    exact htM
  have htd' : Module.finrank (baseField jg) (levelField jg d) = _root_.dedekindPsi d := htd
  rw [← htd', ← htop, Nat.mul_comm]
  exact htow

/-- **The target slot**: for `M = a * d'' * p` and `b < M / a`, the `(b / d'')`-th finite conjugate
at the descended slot is the slot value `slotValue (σ jg) ζ a b` — the two exponents agree because
`b = b % d'' + (b / d'') * d''`. -/
private theorem qExpand_qTwist_slot_eq_slotValue (jg : LaurentSeries κ) (hjg : jg = jqModC κ)
    {M a b d'' p : ℕ} [NeZero M] [NeZero a] [NeZero p] {ζ : κ'ˣ}
    (hMp : M / p = a * d'') (hbsplit : b % d'' + b / d'' * d'' = b) :
    qExpand κ' (a * a)
        (qTwist ((ζ : κ'ˣ) ^ (b % d'' * a) * (ζ : κ'ˣ) ^ (b / d'' * (M / p))) (jqModC κ'))
      = slotValue (σ jg) ζ a b := by
  have hσ := coeffMap_jqModC' (κ' := κ') hjg
  rw [slotValue_eq_TS (σ jg) ζ a b hσ]
  show TS κ' (a * a) ((ζ : κ'ˣ) ^ (b % d'' * a) * (ζ : κ'ˣ) ^ (b / d'' * (M / p)))
    = TS κ' (a * a) ((ζ : κ'ˣ) ^ (b * a))
  refine congrArg (fun u : κ'ˣ => TS κ' (a * a) u) ?_
  rw [hMp, ← pow_add]
  congr 1
  rw [show b % d'' * a + b / d'' * (a * d'') = (b % d'' + b / d'' * d'') * a from by ring,
    hbsplit]

/-- **The `Φ_p`-factorisation at a slot**: the seed polynomial `Φ_p` evaluated at the slot
`qExpand κ' p (slotValue (σ jg) (ζ ^ p) a b)` splits as the extra conjugate at level `p * p` times
the `p` finite conjugates. The splitting is the field-generic
`PhiGen.splits_prime_at_slot_of_isPrimitiveRoot`, read at the order-`p` root `ζ ^ (M / p)` and at the
slot `jqModC κ'`; the source condition turns the slot value into its `TS` form. -/
private theorem phiAtSeed_slot_factor (jg : LaurentSeries κ) (hjg : jg = jqModC κ)
    {M a b p : ℕ} [NeZero M] [NeZero a] [NeZero p] {ζ : κ'ˣ}
    (hζ : IsPrimitiveRoot (ζ : κ') M) (hpp : p.Prime) (hpM : p ∣ M)
    (dp : ModularPolynomialData p) :
    phiAtSeed dp (qExpand κ' p (slotValue (σ jg) (ζ ^ p) a b))
      = (Polynomial.X - Polynomial.C (qExpand κ' (p * (p * (a * a)))
          (qTwist (((ζ : κ'ˣ) ^ (b * a)) ^ (p * p)) (jqModC κ'))))
        * ∏ c ∈ Finset.range p, (Polynomial.X - Polynomial.C (qExpand κ' (a * a)
          (qTwist ((ζ : κ'ˣ) ^ (b * a) * (ζ : κ'ˣ) ^ (c * (M / p))) (jqModC κ')))) := by
  have hσ := coeffMap_jqModC' (κ' := κ') hjg
  have hppF : Fact p.Prime := ⟨hpp⟩
  have hζp : IsPrimitiveRoot ((ζ ^ (M / p) : κ'ˣ) : κ') p := isPrimitiveRoot_pow_div hζ hpM
  have hseed : qExpand κ' p (slotValue (σ jg) (ζ ^ p) a b)
      = qExpand κ' (p * (a * a)) (qTwist (((ζ : κ'ˣ) ^ (b * a)) ^ p) (jqModC κ')) := by
    rw [slotValue_eq_TS (σ jg) (ζ ^ p) a b hσ, qExpand_TS]
    refine congrArg (fun u : κ'ˣ => TS κ' (p * (a * a)) u) ?_
    show ((ζ : κ'ˣ) ^ p) ^ (b * a) = ((ζ : κ'ˣ) ^ (b * a)) ^ p
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have hC5 := PhiGen.splits_prime_at_slot_of_isPrimitiveRoot p (ζ ^ (M / p)) hζp dp (a * a)
    ((ζ : κ'ˣ) ^ (b * a))
  have hC5' : phiAtSeed dp (qExpand κ' (p * (a * a))
        (qTwist (((ζ : κ'ˣ) ^ (b * a)) ^ p) (jqModC κ')))
      = (Polynomial.X - Polynomial.C (qExpand κ' (p * (p * (a * a)))
          (qTwist (((ζ : κ'ˣ) ^ (b * a)) ^ (p * p)) (jqModC κ'))))
        * ∏ c ∈ Finset.range p, (Polynomial.X - Polynomial.C (qExpand κ' (a * a)
          (qTwist ((ζ : κ'ˣ) ^ (b * a) * ((ζ ^ (M / p) : κ'ˣ)) ^ c) (jqModC κ')))) := hC5
  have hfac : (∏ c ∈ Finset.range p, (Polynomial.X - Polynomial.C (qExpand κ' (a * a)
        (qTwist ((ζ : κ'ˣ) ^ (b * a) * ((ζ ^ (M / p) : κ'ˣ)) ^ c) (jqModC κ')))))
      = ∏ c ∈ Finset.range p, (Polynomial.X - Polynomial.C (qExpand κ' (a * a)
        (qTwist ((ζ : κ'ˣ) ^ (b * a) * (ζ : κ'ˣ) ^ (c * (M / p))) (jqModC κ')))) := by
    refine Finset.prod_congr rfl fun c _ => ?_
    have h1 : ((ζ ^ (M / p) : κ'ˣ)) ^ c = (ζ : κ'ˣ) ^ (c * (M / p)) := by
      rw [← pow_mul, Nat.mul_comm]
    rw [h1]
  rw [hseed, hC5', hfac]

/-- **A level equation, at the level series**. -/
private theorem levelSeries_congr (jg : LaurentSeries κ) {M N : ℕ} [NeZero M] [NeZero N]
    (h : M = N) : levelSeries jg M = levelSeries jg N := by
  show qExpand κ M jg = qExpand κ N jg
  exact qExpand_congr h jg

/-- **A level equation, at the nome map**: the nome map depends on the level only through the
`q`-expansion, so equal levels give equal nome maps. -/
private theorem nomeMap_congr (jg : LaurentSeries κ) {M N : ℕ} [NeZero M] [NeZero N]
    (h : M = N) :
    nomeMap (κ' := κ') jg M = nomeMap (κ' := κ') jg N := by
  refine RingHom.ext fun x => ?_
  show σ (qExpand κ M (algebraMap (baseField jg) (LaurentSeries κ) x))
    = σ (qExpand κ N (algebraMap (baseField jg) (LaurentSeries κ) x))
  rw [qExpand_congr h]

/-- **The modular relation at a level**: `Φ_n` vanishes at `(levelSeries jg d, levelSeries jg (d * n))`.
One field: at `jg = jqModC κ` this *is* the coefficient field's
`phiAtSeed_jqNModC_eval`. -/
theorem seed_eval_zero (jg : LaurentSeries κ) (hjg : jg = jqModC κ)
    (n : ℕ) [NeZero n] (dp : ModularPolynomialData n) (d : ℕ) [NeZero d] :
    (phiAtSeed dp (levelSeries jg d)).eval (levelSeries jg (d * n)) = 0 := by
  subst hjg
  exact phiAtSeed_jqNModC_eval (R := κ) n dp d

/-- **The mirror modular relation**: `Φ_n` also vanishes at `(levelSeries jg (d * n), levelSeries jg d)`
when `Φ_n` is symmetric — the same one-field fact, from `phiAtSeed_jqNModC_eval_symm`. -/
private theorem seed_eval_zero_symm (jg : LaurentSeries κ) (hjg : jg = jqModC κ)
    (n : ℕ) [NeZero n] (dp : ModularPolynomialData n) (hsymm : EvalSymm dp.Φ) (d : ℕ) [NeZero d] :
    (phiAtSeed dp (levelSeries jg (d * n))).eval (levelSeries jg d) = 0 := by
  subst hjg
  exact phiAtSeed_jqNModC_eval_symm (R := κ) n dp hsymm d

/-- **The descended slot root, pushed up**: if the slot product holds at the level `d = a * d''` for
the primitive root `ζ ^ p` (the strong-induction hypothesis) and `M = p * (a * d'')`, then the
expanded slot value `qExpand κ' p (slotValue (σ jg) (ζ ^ p) a (b % d''))` is a root of the level-`M`
reading of the level-`(a * d'')` minimal polynomial: it is one of the slots of the slot product at
`a * d''`, read after `qExpand κ' p`. -/
private theorem isRoot_qExpand_slot_of_slotProduct (jg : LaurentSeries κ)
    {M a b d'' p : ℕ} [NeZero M] [NeZero a] [NeZero d''] [NeZero p] {ζ : κ'ˣ}
    (hM : M = p * (a * d''))
    (hprod : pushedMinpoly jg (a * d'') = slotPolynomial (σ jg) (a * d'') (ζ ^ p))
    (hb''lt : b % d'' < d'') (hprim' : Nat.gcd (Nat.gcd a (b % d'')) d'' = 1) :
    ((minpoly (baseField jg) (levelSeries jg (a * d''))).map (nomeMap jg M)).IsRoot
      (qExpand κ' p (slotValue (σ jg) (ζ ^ p) a (b % d''))) := by
  subst hM
  have hM'0 : a * d'' ≠ 0 := Nat.mul_ne_zero (NeZero.ne a) (NeZero.ne d'')
  have hMd : NeZero (a * d'') := ⟨hM'0⟩
  have hpp : NeZero (p * p) := ⟨Nat.mul_ne_zero (NeZero.ne p) (NeZero.ne p)⟩
  have hP : pushedMinpolyAt jg (a * d'') (p * (a * d''))
      = ∏ a' ∈ (a * d'').divisors, ∏ b' ∈ (Finset.range (a * d'' / a')).filter
          (fun b' => Nat.gcd (Nat.gcd a' b') (a * d'' / a') = 1),
          (Polynomial.X - Polynomial.C (qExpand κ' p (slotValue (σ jg) (ζ ^ p) a' b'))) := by
    rw [pushedMinpolyAt_map_qExpand jg (m := a * d'') (k := p), pushedMinpolyAt_self, hprod,
      map_qExpand_slotPolynomial (σ jg) p (ζ := ζ ^ p) (M := a * d'')]
  rw [show ((minpoly (baseField jg) (levelSeries jg (a * d''))).map (nomeMap jg (p * (a * d''))))
      = pushedMinpolyAt jg (a * d'') (p * (a * d'')) from rfl, hP,
    Polynomial.IsRoot, Polynomial.eval_prod]
  refine Finset.prod_eq_zero (i := a) (Nat.mem_divisors.mpr ⟨⟨d'', rfl⟩, hM'0⟩) ?_
  rw [Polynomial.eval_prod]
  have hM'a : a * d'' / a = d'' := Nat.mul_div_cancel_left d'' (Nat.pos_of_ne_zero (NeZero.ne a))
  refine Finset.prod_eq_zero (i := b % d'') ?_ ?_
  · rw [hM'a]
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hb''lt, hprim'⟩
  · rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]

/-- **The seed polynomial at the descended conjugate**: the symmetric modular relation at the level
`a * d''` descends to the element `⟨levelSeries jg m, _⟩` of `levelField jg (a * d'')`, and is then
pushed along `ψ` — so the seed polynomial at the descended slot is rooted at `ψ ⟨levelSeries jg m, _⟩`.
This is the ℚ layer's `isRoot_phiAtSeed_slot_apply`, with `phiAtSeed_eval_symm` replaced by the
pulled-back `seed_eval_zero_symm`. -/
private theorem isRoot_phiAtSeed_slot_apply (jg : LaurentSeries κ) (hjg : jg = jqModC κ)
    {a b d'' p m : ℕ} [NeZero a] [NeZero p] [NeZero (a * d'')] [NeZero m] {ζ : κ'ˣ}
    {dp : ModularPolynomialData p} (hdpsym : EvalSymm dp.Φ) (hm : a * d'' = p * m)
    {hmem : levelSeries jg m ∈ levelField jg (a * d'')}
    {ψ : levelField jg (a * d'') →+* LaurentSeries κ'}
    (hψ₁ : ψ (IntermediateField.AdjoinSimple.gen (baseField jg) (levelSeries jg (a * d'')))
      = qExpand κ' p (slotValue (σ jg) (ζ ^ p) a (b % d''))) :
    (phiAtSeed dp (qExpand κ' p (slotValue (σ jg) (ζ ^ p) a (b % d'')))).IsRoot
      (ψ ⟨levelSeries jg m, hmem⟩) := by
  have hlv : levelSeries jg (m * p) = levelSeries jg (a * d'') := by
    refine levelSeries_congr jg ?_
    rw [hm]
    ring
  have hdown : (phiAtSeed dp (levelSeries jg (a * d''))).eval (levelSeries jg m) = 0 := by
    have h1 := seed_eval_zero_symm jg hjg p dp hdpsym m
    rwa [hlv] at h1
  have hdownF₁ : (phiAtSeed dp (IntermediateField.AdjoinSimple.gen (baseField jg)
      (levelSeries jg (a * d'')))).eval
      (⟨levelSeries jg m, hmem⟩ : levelField jg (a * d'')) = 0 :=
    phiAtSeed_eval_of_injective dp _ _
      (algebraMap (levelField jg (a * d'')) (LaurentSeries κ)) (RingHom.injective _) hdown
  have h1 := phiAtSeed_eval_map dp _ _ ψ hdownF₁
  rwa [hψ₁] at h1

/-- **Separation at the descended point** (the case `p ∣ a * d''`): if `a * d'' = m * p` and
`m < M`, then the slot value `slotValue (σ jg) ζ a b` is not the image `ψ ⟨levelSeries jg m, _⟩` of the
descended conjugate. If it were, `TS`-injectivity applied to the level-`m` slot product (the
induction hypothesis, for the primitive root `ζ ^ (p * p)`) would force `p ∣ gcd (gcd a b) (M / a)`,
against the coprimality of the slot. -/
private theorem slotValue_ne_image_of_dvd (jg : LaurentSeries κ) (hjg : jg = jqModC κ)
    {M a b d'' p m : ℕ} [NeZero M] [NeZero a] [NeZero d''] [NeZero p] [NeZero m] {ζ : κ'ˣ}
    (hζ : IsPrimitiveRoot (ζ : κ') M) (hpp : p.Prime)
    (hMM' : M = a * d'' * p) (hm : a * d'' = p * m) (hm0 : m ≠ 0) (hmM : m ∣ M)
    (hmlt : m < M) (hbr : b < M / a) (haM : a ∣ M)
    (hbc : Nat.gcd (Nat.gcd a b) (M / a) = 1) (hdd : M / a = p * d'')
    (hmem : levelSeries jg m ∈ levelField jg (a * d''))
    {ψ : levelField jg (a * d'') →+* LaurentSeries κ'}
    (hroot : ((minpoly (baseField jg) (levelSeries jg m)).map (nomeMap jg M)).IsRoot
      (ψ ⟨levelSeries jg m, hmem⟩))
    (IH : ∀ (n : ℕ), n < M → ∀ [NeZero n] (ζ : κ'ˣ), SlotProductAt jg n ζ)
    (hall : PkgAt jg M) :
    slotValue (σ jg) ζ a b ≠ ψ ⟨levelSeries jg m, hmem⟩ := by
  have hσ := coeffMap_jqModC' (κ' := κ') hjg
  intro hcon
  have hζ'' : IsPrimitiveRoot ((ζ ^ (p * p) : κ'ˣ) : κ') m := by
    have h1 := isPrimitiveRoot_pow_div hζ hmM
    have h2 : M / m = p * p := by
      have hM : M = m * (p * p) := by rw [hMM', hm]; ring
      rw [hM]
      exact Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hm0)
    rwa [h2] at h1
  have hIH'' := IH m hmlt (ζ ^ (p * p)) hjg hζ''
    (fun e he'' _ => hall e (he''.trans hmM))
  have hIHM'' : ((minpoly (baseField jg) (levelSeries jg m)).map (nomeMap jg M))
      = ∏ a' ∈ m.divisors, ∏ b' ∈ (Finset.range (m / a')).filter
          (fun b' => Nat.gcd (Nat.gcd a' b') (m / a') = 1),
          (Polynomial.X - Polynomial.C (qExpand κ' (p * p) (slotValue (σ jg) (ζ ^ (p * p)) a' b'))) := by
    rw [nomeMap_congr jg (show M = p * p * m from by rw [hMM', hm]; ring)]
    show pushedMinpolyAt jg m (p * p * m) = _
    rw [pushedMinpolyAt_map_qExpand jg (m := m) (k := p * p), pushedMinpolyAt_self, hIH'',
      map_qExpand_slotPolynomial (σ jg) (p * p) (ζ := ζ ^ (p * p)) (M := m)]
  rw [hIHM'', Polynomial.IsRoot, Polynomial.eval_prod] at hroot
  obtain ⟨α, hαmem, hα0⟩ := Finset.prod_eq_zero_iff.mp hroot
  rw [Polynomial.eval_prod] at hα0
  obtain ⟨β, hβmem, hβ0⟩ := Finset.prod_eq_zero_iff.mp hα0
  rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hβ0
  obtain ⟨hαdvd, -⟩ := Nat.mem_divisors.mp hαmem
  obtain ⟨hβr, -⟩ := Finset.mem_filter.mp hβmem
  rw [Finset.mem_range] at hβr
  have hα0' : α ≠ 0 := by
    rintro rfl
    exact hm0 (Nat.eq_zero_of_zero_dvd hαdvd)
  have hαNe : NeZero α := ⟨hα0'⟩
  have hcoll : TS κ' (a * a) ((ζ : κ'ˣ) ^ (b * a))
      = TS κ' (p * p * (α * α)) ((ζ : κ'ˣ) ^ (p * p * (β * α))) := by
    calc TS κ' (a * a) ((ζ : κ'ˣ) ^ (b * a)) = slotValue (σ jg) ζ a b :=
          (slotValue_eq_TS (σ jg) ζ a b hσ).symm
      _ = ψ ⟨levelSeries jg m, hmem⟩ := hcon
      _ = qExpand κ' (p * p) (slotValue (σ jg) (ζ ^ (p * p)) α β) := hβ0
      _ = qExpand κ' (p * p) (TS κ' (α * α) (((ζ ^ (p * p) : κ'ˣ)) ^ (β * α))) := by
          rw [slotValue_eq_TS (σ jg) (ζ ^ (p * p)) α β hσ]
      _ = TS κ' (p * p * (α * α)) (((ζ ^ (p * p) : κ'ˣ)) ^ (β * α)) := qExpand_TS _ _ _
      _ = TS κ' (p * p * (α * α)) ((ζ : κ'ˣ) ^ (p * p * (β * α))) := by
          refine congrArg (fun u : κ'ˣ => TS κ' (p * p * (α * α)) u) ?_
          show ((ζ : κ'ˣ) ^ (p * p)) ^ (β * α) = (ζ : κ'ˣ) ^ (p * p * (β * α))
          rw [← pow_mul]
  obtain ⟨hexp, hunit⟩ := TS_injective hcoll
  have haα : a = p * α := by
    have h2 : a * a = (p * α) * (p * α) := by rw [hexp]; ring
    exact (mul_self_inj (Nat.zero_le _) (Nat.zero_le _)).mp h2
  have hpa : p ∣ a := ⟨α, haα⟩
  have hba : b * a < M := by
    calc b * a < M / a * a :=
        (Nat.mul_lt_mul_right (Nat.pos_of_ne_zero (NeZero.ne a))).mpr hbr
      _ = M := Nat.div_mul_cancel haM
  have hppβα : p * p * (β * α) < M := by
    have h1 : β * α < m := by
      calc β * α < m / α * α :=
          (Nat.mul_lt_mul_right (Nat.pos_of_ne_zero hα0')).mpr hβr
        _ ≤ m := Nat.div_mul_le_self m α
    calc p * p * (β * α) < p * p * m :=
        (Nat.mul_lt_mul_left (Nat.mul_pos hpp.pos hpp.pos)).mpr h1
      _ = M := by rw [hMM', hm]; ring
  have hvv : ((ζ : κ')) ^ (b * a) = ((ζ : κ')) ^ (p * p * (β * α)) := by
    have h1 := congrArg Units.val hunit
    rwa [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val] at h1
  have hexp2 : b * a = p * p * (β * α) := hζ.pow_inj hba hppβα hvv
  have hpb : p ∣ b := by
    refine ⟨β, ?_⟩
    rw [haα] at hexp2
    have h1 : b * (p * α) = p * β * (p * α) := by
      rw [hexp2]
      ring
    exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hpp.pos (Nat.pos_of_ne_zero hα0')) h1
  have hfinal : p ∣ Nat.gcd (Nat.gcd a b) (M / a) :=
    Nat.dvd_gcd (Nat.dvd_gcd hpa hpb) ⟨d'', hdd⟩
  rw [hbc] at hfinal
  exact hpp.ne_one (Nat.dvd_one.mp hfinal)

/-- **The root at a slot when `p ∣ a * d''`** (one case of the descent): the minimal polynomial of
`levelSeries jg M` over `levelField jg (a * d'')` has degree `p`, one less than the seed polynomial
`phiAtSeed dp` of degree `p + 1`; it is therefore the seed polynomial divided by the linear factor at
the descended conjugate. Evaluating the remaining `p` finite conjugates at the slot value gives a
root. -/
private theorem isRoot_map_minpoly_slot_of_dvd (jg : LaurentSeries κ) (hjg : jg = jqModC κ)
    {M a b d'' p m : ℕ} [NeZero M] [NeZero a] [NeZero d''] [NeZero p] [NeZero m] {ζ : κ'ˣ}
    (hζ : IsPrimitiveRoot (ζ : κ') M) (hpp : p.Prime) (hpM : p ∣ M)
    (dp : ModularPolynomialData p)
    (hα₁ : IsIntegral (levelField jg (a * d'')) (levelSeries jg M))
    (hdeg : (minpoly (levelField jg (a * d'')) (levelSeries jg M)).natDegree = p)
    (hmem : levelSeries jg m ∈ levelField jg (a * d''))
    (hmindvd : minpoly (levelField jg (a * d'')) (levelSeries jg M)
      ∣ phiAtSeed dp (IntermediateField.AdjoinSimple.gen (baseField jg) (levelSeries jg (a * d''))))
    (hc₀p : b / d'' < p) (hMp : M / p = a * d'') (hbsplit : b % d'' + b / d'' * d'' = b)
    {ψ : levelField jg (a * d'') →+* LaurentSeries κ'}
    (hψ₁ : ψ (IntermediateField.AdjoinSimple.gen (baseField jg) (levelSeries jg (a * d'')))
      = qExpand κ' p (slotValue (σ jg) (ζ ^ p) a (b % d'')))
    (hψx : (phiAtSeed dp (qExpand κ' p (slotValue (σ jg) (ζ ^ p) a (b % d'')))).IsRoot
      (ψ ⟨levelSeries jg m, hmem⟩))
    (hψxnotmin : ¬ ((minpoly (levelField jg (a * d'')) (levelSeries jg M)).map ψ).IsRoot
      (ψ ⟨levelSeries jg m, hmem⟩))
    (htarget_ne : slotValue (σ jg) ζ a b ≠ ψ ⟨levelSeries jg m, hmem⟩) :
    ((minpoly (levelField jg (a * d'')) (levelSeries jg M)).map ψ).IsRoot
      (slotValue (σ jg) ζ a b) := by
  have hΦfact := phiAtSeed_slot_factor jg hjg (M := M) (a := a) (b := b % d'') (p := p)
    hζ hpp hpM dp
  have htarget := qExpand_qTwist_slot_eq_slotValue jg hjg (M := M) (a := a) (b := b) (d'' := d'')
    (p := p) (ζ := ζ) hMp hbsplit
  have hQ : (Polynomial.X - Polynomial.C (ψ ⟨levelSeries jg m, hmem⟩)) *
      (phiAtSeed dp (qExpand κ' p (slotValue (σ jg) (ζ ^ p) a (b % d''))) /ₘ
        (Polynomial.X - Polynomial.C (ψ ⟨levelSeries jg m, hmem⟩)))
      = phiAtSeed dp (qExpand κ' p (slotValue (σ jg) (ζ ^ p) a (b % d''))) :=
    Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hψx
  have hΦmonic : (phiAtSeed dp (qExpand κ' p (slotValue (σ jg) (ζ ^ p) a (b % d'')))).Monic :=
    phiAtSeed_monic dp _
  have hQmonic : (phiAtSeed dp (qExpand κ' p (slotValue (σ jg) (ζ ^ p) a (b % d''))) /ₘ
      (Polynomial.X - Polynomial.C (ψ ⟨levelSeries jg m, hmem⟩))).Monic :=
    Polynomial.Monic.of_mul_monic_left (Polynomial.monic_X_sub_C _) (by rw [hQ]; exact hΦmonic)
  have hΦdeg : (phiAtSeed dp (qExpand κ' p (slotValue (σ jg) (ζ ^ p) a (b % d'')))).natDegree
      = p + 1 := by
    rw [phiAtSeed_natDegree]
    exact _root_.dedekindPsi_prime hpp
  have hQdeg : (phiAtSeed dp (qExpand κ' p (slotValue (σ jg) (ζ ^ p) a (b % d''))) /ₘ
      (Polynomial.X - Polynomial.C (ψ ⟨levelSeries jg m, hmem⟩))).natDegree = p := by
    have h1 : p + 1 = 1 + (phiAtSeed dp (qExpand κ' p (slotValue (σ jg) (ζ ^ p) a (b % d''))) /ₘ
        (Polynomial.X - Polynomial.C (ψ ⟨levelSeries jg m, hmem⟩))).natDegree := by
      rw [← hΦdeg]
      conv_lhs => rw [← hQ]
      rw [Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero _) hQmonic.ne_zero,
        Polynomial.natDegree_X_sub_C]
    omega
  have hP₁dvd : (minpoly (levelField jg (a * d'')) (levelSeries jg M)).map ψ
      ∣ phiAtSeed dp (qExpand κ' p (slotValue (σ jg) (ζ ^ p) a (b % d''))) := by
    have h1 := Polynomial.map_dvd ψ hmindvd
    rwa [phiAtSeed_map, hψ₁] at h1
  have hcop : IsCoprime (Polynomial.X - Polynomial.C (ψ ⟨levelSeries jg m, hmem⟩))
      ((minpoly (levelField jg (a * d'')) (levelSeries jg M)).map ψ) := by
    rw [(Polynomial.irreducible_X_sub_C _).coprime_iff_not_dvd]
    intro hcon
    exact hψxnotmin (Polynomial.dvd_iff_isRoot.mp hcon)
  have hP₁dvdQ : (minpoly (levelField jg (a * d'')) (levelSeries jg M)).map ψ
      ∣ phiAtSeed dp (qExpand κ' p (slotValue (σ jg) (ζ ^ p) a (b % d''))) /ₘ
        (Polynomial.X - Polynomial.C (ψ ⟨levelSeries jg m, hmem⟩)) := by
    have h1 := hP₁dvd
    rw [← hQ] at h1
    exact (hcop.symm).dvd_of_dvd_mul_left h1
  have hdeg₁ : ((minpoly (levelField jg (a * d'')) (levelSeries jg M)).map ψ).natDegree = p := by
    rw [Polynomial.Monic.natDegree_map (minpoly.monic hα₁)]
    exact hdeg
  have hmineqQ : (minpoly (levelField jg (a * d'')) (levelSeries jg M)).map ψ
      = phiAtSeed dp (qExpand κ' p (slotValue (σ jg) (ζ ^ p) a (b % d''))) /ₘ
        (Polynomial.X - Polynomial.C (ψ ⟨levelSeries jg m, hmem⟩)) :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le ((minpoly.monic hα₁).map _)
      hQmonic hP₁dvdQ (le_of_eq (hQdeg.trans hdeg₁.symm)) |>.symm
  have htargetΦ : (phiAtSeed dp (qExpand κ' p (slotValue (σ jg) (ζ ^ p) a (b % d'')))).IsRoot
      (slotValue (σ jg) ζ a b) := by
    rw [hΦfact, Polynomial.IsRoot, Polynomial.eval_mul]
    refine mul_eq_zero.mpr (Or.inr ?_)
    rw [Polynomial.eval_prod]
    refine Finset.prod_eq_zero (Finset.mem_range.mpr hc₀p) ?_
    rw [htarget, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]
  rw [hmineqQ, Polynomial.IsRoot]
  have h1 : ((Polynomial.X - Polynomial.C (ψ ⟨levelSeries jg m, hmem⟩)) *
      (phiAtSeed dp (qExpand κ' p (slotValue (σ jg) (ζ ^ p) a (b % d''))) /ₘ
        (Polynomial.X - Polynomial.C (ψ ⟨levelSeries jg m, hmem⟩)))).eval
        (slotValue (σ jg) ζ a b) = 0 := by
    rw [hQ]
    exact htargetΦ
  rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h1
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact absurd (sub_eq_zero.mp h2) htarget_ne
  · exact h2

/-- **The root at a slot when `p ∤ a * d''`** (the other case of the descent): the degree of
`levelSeries jg M` over `levelField jg (a * d'')` is `p + 1`, the degree of `phiAtSeed dp`; the two
monic polynomials coincide, and the slot value is one of the `p` finite conjugates of `Φ_p` at that
slot. -/
private theorem isRoot_map_minpoly_slot_of_not_dvd (jg : LaurentSeries κ) (hjg : jg = jqModC κ)
    {M a b d'' p : ℕ} [NeZero M] [NeZero a] [NeZero d''] [NeZero p] {ζ : κ'ˣ}
    (hζ : IsPrimitiveRoot (ζ : κ') M) (hpp : p.Prime) (hpM : p ∣ M)
    (dp : ModularPolynomialData p) (hpM' : ¬ p ∣ a * d'')
    (hstep : Module.finrank (levelField jg (a * d''))
        ((levelField jg (a * d''))⟮levelSeries jg M⟯) * _root_.dedekindPsi (a * d'')
      = _root_.dedekindPsi M)
    (hMM' : M = a * d'' * p) (hM'0 : a * d'' ≠ 0)
    (hα₁ : IsIntegral (levelField jg (a * d'')) (levelSeries jg M))
    (hmindvd : minpoly (levelField jg (a * d'')) (levelSeries jg M)
      ∣ phiAtSeed dp (IntermediateField.AdjoinSimple.gen (baseField jg) (levelSeries jg (a * d''))))
    (hc₀p : b / d'' < p) (hMp : M / p = a * d'') (hbsplit : b % d'' + b / d'' * d'' = b)
    {ψ : levelField jg (a * d'') →+* LaurentSeries κ'}
    (hψ₁ : ψ (IntermediateField.AdjoinSimple.gen (baseField jg) (levelSeries jg (a * d'')))
      = qExpand κ' p (slotValue (σ jg) (ζ ^ p) a (b % d''))) :
    ((minpoly (levelField jg (a * d'')) (levelSeries jg M)).map ψ).IsRoot
      (slotValue (σ jg) ζ a b) := by
  have hΦfact := phiAtSeed_slot_factor jg hjg (M := M) (a := a) (b := b % d'') (p := p)
    hζ hpp hpM dp
  have htarget := qExpand_qTwist_slot_eq_slotValue jg hjg (M := M) (a := a) (b := b) (d'' := d'')
    (p := p) (ζ := ζ) hMp hbsplit
  have hψM : _root_.dedekindPsi M = _root_.dedekindPsi (a * d'') * (p + 1) := by
    rw [hMM']
    exact _root_.dedekindPsi_mul_prime_not_dvd hpp hpM'
  have he : Module.finrank (levelField jg (a * d''))
      ((levelField jg (a * d''))⟮levelSeries jg M⟯) = p + 1 := by
    have h1 : Module.finrank (levelField jg (a * d''))
        ((levelField jg (a * d''))⟮levelSeries jg M⟯) * _root_.dedekindPsi (a * d'')
        = (p + 1) * _root_.dedekindPsi (a * d'') := by
      rw [hstep, hψM]
      ring
    exact Nat.eq_of_mul_eq_mul_right (_root_.dedekindPsi_pos _ hM'0) h1
  have hdeg₁ : (minpoly (levelField jg (a * d'')) (levelSeries jg M)).natDegree = p + 1 := by
    rw [← IntermediateField.adjoin.finrank hα₁]
    exact he
  have hΦdeg : (phiAtSeed dp (IntermediateField.AdjoinSimple.gen (baseField jg)
      (levelSeries jg (a * d'')))).natDegree = p + 1 := by
    rw [phiAtSeed_natDegree]
    exact _root_.dedekindPsi_prime hpp
  have hmineq : minpoly (levelField jg (a * d'')) (levelSeries jg M)
      = phiAtSeed dp (IntermediateField.AdjoinSimple.gen (baseField jg) (levelSeries jg (a * d''))) :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hα₁)
      (phiAtSeed_monic dp _) hmindvd (le_of_eq (hΦdeg.trans hdeg₁.symm)) |>.symm
  rw [hmineq, phiAtSeed_map, hψ₁, hΦfact, Polynomial.IsRoot, Polynomial.eval_mul]
  refine mul_eq_zero.mpr (Or.inr ?_)
  rw [Polynomial.eval_prod]
  refine Finset.prod_eq_zero (Finset.mem_range.mpr hc₀p) ?_
  rw [htarget, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]

/-- **The root at a descending slot** (the main case `M / a ≠ 1`): let `p = (M / a).minFac` and
`M / a = p * d''`. Replacing `M` by `a * d''` and `ζ` by `ζ ^ p` (the induction hypothesis), the slot
`(a, b % d'')` at level `a * d''` pushes up to a conjugate `ψ₁` of `levelSeries jg M` over
`levelField jg (a * d'')`; the value `slotValue (σ jg) ζ a b` is then read off the `Φ_p`-factorisation
at that conjugate, in the two cases `p ∣ a * d''` and `p ∤ a * d''`. -/
private theorem isRoot_map_minpoly_slot_of_descent (jg : LaurentSeries κ) (hjg : jg = jqModC κ)
    {M : ℕ} [NeZero M] (ζ : κ'ˣ) (hζ : IsPrimitiveRoot (ζ : κ') M)
    (hall : PkgAt jg M)
    (IH : ∀ (n : ℕ), n < M → ∀ [NeZero n] (ζ : κ'ˣ), SlotProductAt jg n ζ)
    {a b : ℕ} (haM : a ∣ M) (ha0 : a ≠ 0) (hd1 : M / a ≠ 1) (hbr : b < M / a)
    (hbc : Nat.gcd (Nat.gcd a b) (M / a) = 1) :
    (pushedMinpoly jg M).IsRoot (slotValue (σ jg) ζ a b) := by
  classical
  obtain ⟨htM_self, hgM_self⟩ := hall M dvd_rfl
  have had : a * (M / a) = M := Nat.mul_div_cancel' haM
  obtain ⟨p, d'', hpp, hd''0, hdd, hb''lt, hc₀p, hprim', hbsplit⟩ :=
    exists_slot_descent_data (NeZero.ne M) haM hd1 hbr hbc
  have hppF : Fact p.Prime := ⟨hpp⟩
  have hpm : NeZero p := ⟨hpp.ne_zero⟩
  have ham : NeZero a := ⟨ha0⟩
  have hd''m : NeZero d'' := ⟨hd''0⟩
  have hM'0 : a * d'' ≠ 0 := Nat.mul_ne_zero ha0 hd''0
  have hM'm : NeZero (a * d'') := ⟨hM'0⟩
  have hMM' : M = a * d'' * p := by rw [← had, hdd]; ring
  have hM'M : a * d'' ∣ M := ⟨p, hMM'⟩
  have hM'lt : a * d'' < M := by
    calc a * d'' = a * d'' * 1 := by ring
      _ < a * d'' * p := (Nat.mul_lt_mul_left (Nat.pos_of_ne_zero hM'0)).mpr hpp.one_lt
      _ = M := hMM'.symm
  have hpM : p ∣ M := by
    have hpd : p ∣ M / a := ⟨d'', hdd⟩
    exact hpd.trans (Nat.div_dvd_of_dvd haM)
  have hMp : M / p = a * d'' := by
    rw [hMM']
    exact Nat.mul_div_cancel _ hpp.pos
  have hζ' : IsPrimitiveRoot ((ζ ^ p : κ'ˣ) : κ') (a * d'') := by
    have h1 := isPrimitiveRoot_pow_div hζ hM'M
    have h2 : M / (a * d'') = p := by
      rw [hMM']
      exact Nat.mul_div_cancel_left p (Nat.pos_of_ne_zero hM'0)
    rwa [h2] at h1
  have hprod := IH (a * d'') hM'lt (ζ ^ p) hjg hζ'
    (fun e he _ => hall e (he.trans hM'M))
  have hroot' := isRoot_qExpand_slot_of_slotProduct jg
    (show M = p * (a * d'') from by rw [hMM']; ring) hprod hb''lt hprim'
  obtain ⟨htM', hgM'⟩ := hall (a * d'') hM'M
  have hα' : IsIntegral (baseField jg) (levelSeries jg (a * d'')) := isIntegral_levelSeries jg _ htM'
  let halgI : Algebra (baseField jg) (LaurentSeries κ') := (nomeMap jg M).toAlgebra
  have halg : algebraMap (baseField jg) (LaurentSeries κ') = nomeMap jg M :=
    RingHom.algebraMap_toAlgebra _
  obtain ⟨ψ₁, hψ₁, hψcomp⟩ := exists_algHom_adjoin_of_isRoot jg hα' hroot' halg
  obtain ⟨dp, -, hdpsym⟩ := exists_phiIrreducible_evalSymm p
  have hup : (phiAtSeed dp (levelSeries jg (a * d''))).eval (levelSeries jg M) = 0 := by
    have h1 := seed_eval_zero jg hjg p dp (a * d'')
    rwa [(levelSeries_congr jg hMM').symm] at h1
  have haev : Polynomial.aeval (levelSeries jg M)
      (phiAtSeed dp (IntermediateField.AdjoinSimple.gen (baseField jg)
        (levelSeries jg (a * d'')))) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, phiAtSeed_map]
    exact hup
  have hα₁ : IsIntegral (levelField jg (a * d'')) (levelSeries jg M) :=
    ⟨phiAtSeed dp (IntermediateField.AdjoinSimple.gen (baseField jg) (levelSeries jg (a * d''))),
      phiAtSeed_monic dp _, by rw [← Polynomial.aeval_def]; exact haev⟩
  have hmindvd : minpoly (levelField jg (a * d'')) (levelSeries jg M)
      ∣ phiAtSeed dp (IntermediateField.AdjoinSimple.gen (baseField jg)
        (levelSeries jg (a * d''))) :=
    minpoly.dvd _ _ haev
  have hstep := finrank_adjoin_mul_dedekindPsi hM'M htM_self hgM_self htM'
  by_cases hpM' : p ∣ a * d''
  · have hψM : _root_.dedekindPsi M = _root_.dedekindPsi (a * d'') * p := by
      rw [hMM']
      exact _root_.dedekindPsi_mul_prime_dvd hpp hpM'
    have he : Module.finrank (levelField jg (a * d''))
        ((levelField jg (a * d''))⟮levelSeries jg M⟯) = p := by
      have h1 : Module.finrank (levelField jg (a * d''))
          ((levelField jg (a * d''))⟮levelSeries jg M⟯) * _root_.dedekindPsi (a * d'')
          = p * _root_.dedekindPsi (a * d'') := by
        rw [hstep, hψM]
        ring
      exact Nat.eq_of_mul_eq_mul_right (_root_.dedekindPsi_pos _ hM'0) h1
    have hdeg : (minpoly (levelField jg (a * d'')) (levelSeries jg M)).natDegree = p := by
      rw [← IntermediateField.adjoin.finrank hα₁]
      exact he
    obtain ⟨m, hm⟩ := hpM'
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hm
      exact hM'0 hm
    have hmm : NeZero m := ⟨hm0⟩
    have hmM : m ∣ M := ⟨p * p, by rw [hMM', hm]; ring⟩
    have hmlt : m < M := by
      calc m ≤ a * d'' := by rw [hm]; exact Nat.le_mul_of_pos_left m hpp.pos
        _ < M := hM'lt
    have hmem : levelSeries jg m ∈ levelField jg (a * d'') := by
      have h1 : levelSeries jg m ∈ ((IntermediateField.adjoin (baseField jg)
          ({levelSeries jg (a * d'')} : Set (LaurentSeries κ))) : Set (LaurentSeries κ)) := by
        rw [coe_adjoin_baseField, hgM']
        exact IntermediateField.subset_adjoin κ _
          (Or.inr ⟨m, hmm, ⟨p, by rw [hm]; ring⟩, rfl⟩)
      exact h1
    have hxnotmin : ¬ (minpoly (levelField jg (a * d'')) (levelSeries jg M)).IsRoot
        (⟨levelSeries jg m, hmem⟩ : levelField jg (a * d'')) :=
      not_isRoot_minpoly_of_prime_deg p hpp hα₁ hdeg ⟨levelSeries jg m, hmem⟩
    have hψxnotmin : ¬ ((minpoly (levelField jg (a * d'')) (levelSeries jg M)).map
        (ψ₁ : levelField jg (a * d'') →+* LaurentSeries κ')).IsRoot
        (ψ₁ (⟨levelSeries jg m, hmem⟩ : levelField jg (a * d''))) := by
      intro hcon
      refine hxnotmin ?_
      rw [Polynomial.IsRoot, Polynomial.eval_map,
        show ψ₁ (⟨levelSeries jg m, hmem⟩ : levelField jg (a * d''))
          = (ψ₁ : levelField jg (a * d'') →+* LaurentSeries κ')
            (⟨levelSeries jg m, hmem⟩ : levelField jg (a * d'')) from rfl,
        Polynomial.eval₂_hom] at hcon
      exact (injective_iff_map_eq_zero _).mp
        (RingHom.injective (ψ₁ : levelField jg (a * d'') →+* LaurentSeries κ')) _ hcon
    have htarget_ne : slotValue (σ jg) ζ a b
        ≠ ψ₁ (⟨levelSeries jg m, hmem⟩ : levelField jg (a * d'')) := by
      intro hcon
      have hroot'' : ((minpoly (baseField jg) (levelSeries jg m)).map (nomeMap jg M)).IsRoot
          (ψ₁ (⟨levelSeries jg m, hmem⟩ : levelField jg (a * d''))) := by
        have h1 : Polynomial.aeval (⟨levelSeries jg m, hmem⟩ : levelField jg (a * d''))
            (minpoly (baseField jg) (levelSeries jg m)) = 0 := by
          refine aeval_intermediateField_eq_zero ?_
          show Polynomial.aeval (levelSeries jg m) (minpoly (baseField jg) (levelSeries jg m)) = 0
          exact minpoly.aeval _ _
        have h2 := Polynomial.aeval_algHom_apply ψ₁
          (⟨levelSeries jg m, hmem⟩ : levelField jg (a * d''))
          (minpoly (baseField jg) (levelSeries jg m))
        rw [h1, map_zero] at h2
        rw [Polynomial.aeval_def, halg, Polynomial.eval₂_eq_eval_map] at h2
        exact h2
      exact slotValue_ne_image_of_dvd jg hjg
        (ψ := (ψ₁ : levelField jg (a * d'') →+* LaurentSeries κ'))
        hζ hpp hMM' hm hm0 hmM hmlt hbr haM hbc hdd hmem hroot'' IH hall hcon
    have hψx : (phiAtSeed dp (qExpand κ' p (slotValue (σ jg) (ζ ^ p) a (b % d'')))).IsRoot
        (ψ₁ (⟨levelSeries jg m, hmem⟩ : levelField jg (a * d''))) :=
      isRoot_phiAtSeed_slot_apply jg hjg (dp := dp) (m := m) hdpsym hm
        (ψ := (ψ₁ : levelField jg (a * d'') →+* LaurentSeries κ')) hψ₁
    have hroot_step := isRoot_map_minpoly_slot_of_dvd jg hjg
      (ψ := (ψ₁ : levelField jg (a * d'') →+* LaurentSeries κ'))
      hζ hpp hpM dp hα₁ hdeg hmem hmindvd hc₀p hMp hbsplit hψ₁ hψx hψxnotmin htarget_ne
    exact isRoot_map_minpoly_of_isRoot_subfield hψcomp hroot_step
  · exact isRoot_map_minpoly_of_isRoot_subfield hψcomp
      (isRoot_map_minpoly_slot_of_not_dvd jg hjg
        (ψ := (ψ₁ : levelField jg (a * d'') →+* LaurentSeries κ'))
        hζ hpp hpM dp hpM' hstep hMM' hM'0 hα₁ hmindvd hc₀p hMp hbsplit hψ₁)

/-- **Every slot value is a root**: for a slot `(a, b)` of `M` (`a ∈ M.divisors`, `b < M / a` coprime
to `M / a`), the value `slotValue (σ jg) ζ a b` is a root of the pushed minimal polynomial of
`levelSeries jg M`. Either `a = M` (the top slot, `b = 0`), or the slot descends along the least prime
of `M / a` to the level `a * d''`. -/
private theorem isRoot_map_minpoly_slot (jg : LaurentSeries κ) (hjg : jg = jqModC κ)
    {M : ℕ} [NeZero M] (ζ : κ'ˣ) (hζ : IsPrimitiveRoot (ζ : κ') M)
    (hall : PkgAt jg M)
    (IH : ∀ (n : ℕ), n < M → ∀ [NeZero n] (ζ : κ'ˣ), SlotProductAt jg n ζ)
    {a b : ℕ} (ha : a ∈ M.divisors)
    (hb : b ∈ (Finset.range (M / a)).filter
      (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1)) :
    (pushedMinpoly jg M).IsRoot (slotValue (σ jg) ζ a b) := by
  obtain ⟨haM, -⟩ := Nat.mem_divisors.mp ha
  have hbr : b < M / a := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
  have hbc : Nat.gcd (Nat.gcd a b) (M / a) = 1 := (Finset.mem_filter.mp hb).2
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact NeZero.ne M (Nat.eq_zero_of_zero_dvd haM)
  by_cases hd1 : M / a = 1
  · exact isRoot_map_minpoly_slot_top jg haM hd1 hb
  · exact isRoot_map_minpoly_slot_of_descent jg hjg ζ hζ hall IH haM ha0 hd1 hbr hbc

/-- **The slot product** (strong induction on `M`): the pushed minimal polynomial of `levelSeries jg M`
is the product of `X - C (slotValue (σ jg) ζ a b)` over the slots — i.e. `SlotProductAt jg M ζ`. The
`ψ(M)` slot values are distinct roots (`isRoot_map_minpoly_slot`, `slotValue_inj_slot`) and
`ψ(M) = deg` of the pushed polynomial (`natDegree_minpoly_levelSeries`, transported along the monic
minimal polynomial, which needs no injectivity of the carrier), so they are exactly its roots. -/
theorem slotProductInduction (jg : LaurentSeries κ) :
    ∀ (M : ℕ) [NeZero M] (ζ : κ'ˣ), SlotProductAt jg M ζ := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M IH =>
  intro _ ζ hjg hζ hall
  have hσ := coeffMap_jqModC' (κ' := κ') hjg
  classical
  by_cases hM1 : M = 1
  · subst hM1
    exact minpoly_map_eq_prod_slots_one jg ζ
  · have hM0 : M ≠ 0 := NeZero.ne M
    obtain ⟨htM_self, -⟩ := hall M dvd_rfl
    have hα : IsIntegral (baseField jg) (levelSeries jg M) := isIntegral_levelSeries jg M htM_self
    have hdeg : (minpoly (baseField jg) (levelSeries jg M)).natDegree = _root_.dedekindPsi M :=
      natDegree_minpoly_levelSeries jg M htM_self
    have hPdeg : (pushedMinpoly (κ' := κ') jg M).natDegree = _root_.dedekindPsi M := by
      rw [pushedMinpoly, Polynomial.Monic.natDegree_map (minpoly.monic hα)]
      exact hdeg
    have hPne : pushedMinpoly (κ' := κ') jg M ≠ 0 :=
      ((minpoly.monic hα).map (nomeMap jg M)).ne_zero
    have hroot : ∀ a b : ℕ, a ∈ M.divisors →
        b ∈ (Finset.range (M / a)).filter
          (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1) →
        (pushedMinpoly jg M).IsRoot (slotValue (σ jg) ζ a b) :=
      fun a b ha hb =>
        isRoot_map_minpoly_slot jg hjg ζ hζ hall (fun n hn _ ζ' => IH n hn ζ') ha hb
    have hTnodup : (slotValues M (fun a b => slotValue (σ jg) ζ a b)).Nodup :=
      nodup_slotValues fun a b a' b' ha ha' hb hb' h =>
        slotValue_inj_slot (σ jg) hσ hζ hM0 (Nat.mem_divisors.mp ha).1 (Nat.mem_divisors.mp ha').1
          (Finset.mem_range.mp (Finset.mem_filter.mp hb).1)
          (Finset.mem_range.mp (Finset.mem_filter.mp hb').1) h
    have hTle : slotValues M (fun a b => slotValue (σ jg) ζ a b) ≤
        (pushedMinpoly jg M).roots :=
      slotValues_le_roots hPne hTnodup fun a b ha hb =>
        Polynomial.mem_roots'.mpr ⟨hPne, hroot a b ha hb⟩
    have hroots_eq : (pushedMinpoly jg M).roots
        = slotValues M (fun a b => slotValue (σ jg) ζ a b) := by
      refine (Multiset.eq_of_le_of_card_le hTle ?_).symm
      rw [card_slotValues hM0 _]
      calc Multiset.card (pushedMinpoly jg M).roots
          ≤ (pushedMinpoly jg M).natDegree := Polynomial.card_roots' _
        _ = _root_.dedekindPsi M := hPdeg
    have hsp : Polynomial.Splits (pushedMinpoly (κ' := κ') jg M) := by
      rw [Polynomial.splits_iff_card_roots, hroots_eq, card_slotValues hM0 _, hPdeg]
      rfl
    have hfact := hsp.eq_prod_roots_of_monic ((minpoly.monic hα).map (nomeMap jg M))
    rw [hfact, hroots_eq]
    rfl

/-- **The slot product**: for the j-series condition `jg = jqModC κ`, a primitive `M`-th root and the
level-degree package at `M`, the pushed minimal polynomial of the level-`M` series is the slot
polynomial. -/
theorem pushedMinpoly_eq_slotPolynomial (jg : LaurentSeries κ)
    (M : ℕ) [NeZero M] {ζ : κ'ˣ} (hjg : jg = jqModC κ) (hζ : IsPrimitiveRoot (ζ : κ') M)
    (h : PkgAt jg M) :
    pushedMinpoly jg M = slotPolynomial (σ jg) M ζ :=
  slotProductInduction jg M ζ hjg hζ h

end ModularCurve
