/-
  The abstraction probe for the generic function-field-generation layer.

  Every declaration of `FunctionFieldGeneration/Generic/` is stated at a general coefficient field,
  with the second field `κ'` a section variable `[Algebra κ κ']` (never a carrier parameter). This
  file instantiates the theory at `ZMod 5` — a field of characteristic five, which carries no
  `ℚ`-algebra structure — and both `#check`s the statements and *applies* them. If a `ℚ` fact has
  leaked into a section variable, a statement or an instance argument, this file stops elaborating:
  an `[Algebra ℚ κ']`, a `coeffEmb`, or a `CharZero` hypothesis cannot be met at `ZMod 5`.

  Both fields are `ZMod 5` here (the identity algebra), which is the shape the `C` layer uses; the
  two-field theory is exercised at the same time, since every statement still carries `κ` and `κ'`
  separately.

  It is a probe, not part of the library: it is elaborated on demand and has no consumers.
-/
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Generic.SlotProduct
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Generic.PrimeNonmembership
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Generic.PrimeStep

set_option autoImplicit false

noncomputable section

open Polynomial HahnSeries IntermediateField
open scoped IntermediateField

namespace ModularCurve

/-- Characteristic five: a field with no `ℚ`-algebra structure. -/
instance : Fact (Nat.Prime 5) := ⟨by decide⟩

example : Field (ZMod 5) := inferInstance

/-- The layer's vocabulary exists at a general field. -/
example : IntermediateField (ZMod 5) (LaurentSeries (ZMod 5)) := baseField (0 : LaurentSeries (ZMod 5))

/-- The package predicate is satisfied by nothing here; it must still *elaborate*. -/
example (jg : LaurentSeries (ZMod 5)) (M : ℕ) : PkgAt jg M → PkgAt jg M := id

/-- The slot value's `TS` bridge applies at `ZMod 5`, given the source condition. -/
example (jg : LaurentSeries (ZMod 5)) (ζ : (ZMod 5)ˣ) (a b : ℕ) [NeZero a]
    (hjg : jg = jqModC (ZMod 5)) :
    slotValue jg ζ a b = TS (ZMod 5) (a * a) (ζ ^ (b * a)) :=
  slotValue_eq_TS jg ζ a b hjg

/-- The slots are distinct at `ZMod 5`. -/
example (jg : LaurentSeries (ZMod 5)) (hjg : jg = jqModC (ZMod 5)) {M : ℕ} {ζ : (ZMod 5)ˣ}
    (hζ : IsPrimitiveRoot (ζ : ZMod 5) M) (hM0 : M ≠ 0)
    {a b a' b' : ℕ} (haM : a ∣ M) (haM' : a' ∣ M) (hb : b < M / a) (hb' : b' < M / a')
    (h : slotValue jg ζ a b = slotValue jg ζ a' b') :
    a = a' ∧ b = b' :=
  slotValue_inj_slot jg hjg hζ hM0 haM haM' hb hb' h

/-- The named objects exist at `ZMod 5`, and the headline applies — including its source condition,
which is what makes it a true statement. -/
example (jg : LaurentSeries (ZMod 5)) (hjg : jg = jqModC (ZMod 5))
    (M : ℕ) [NeZero M] (ζ : (ZMod 5)ˣ)
    (hζ : IsPrimitiveRoot (ζ : ZMod 5) M) (h : PkgAt jg M) :
    pushedMinpoly (κ' := ZMod 5) jg M
      = slotPolynomial (coeffMap (algebraMap (ZMod 5) (ZMod 5)) jg) M ζ :=
  pushedMinpoly_eq_slotPolynomial (κ' := ZMod 5) jg M hjg hζ h

/-- The slot polynomial's multiset spelling is the pin's iterated product (`prod_slotValues`). -/
example (jg : LaurentSeries (ZMod 5)) (M : ℕ) (ζ : (ZMod 5)ˣ) :
    slotPolynomial jg M ζ
      = ∏ a ∈ M.divisors, ∏ b ∈ (Finset.range (M / a)).filter
          (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1),
          (Polynomial.X - Polynomial.C (slotValue jg ζ a b)) :=
  prod_slotValues M _

/-- The nome map's type is purely `κ`-relative: no `ℚ`-algebra structure is asked for. -/
example (jg : LaurentSeries (ZMod 5)) (M : ℕ) [NeZero M] :
    baseField jg →+* LaurentSeries (ZMod 5) :=
  nomeMap (κ' := ZMod 5) jg M

/-- The package's two consequences apply at `ZMod 5`, from the degree clause alone. -/
example (jg : LaurentSeries (ZMod 5)) (M : ℕ) [NeZero M] (hf : degreeAt jg M) :
    IsIntegral (baseField jg) (levelSeries jg M) :=
  isIntegral_levelSeries jg M hf

example (jg : LaurentSeries (ZMod 5)) (M : ℕ) [NeZero M] (hf : degreeAt jg M) :
    (minpoly (baseField jg) (levelSeries jg M)).natDegree = dedekindPsi M :=
  natDegree_minpoly_levelSeries jg M hf

/-- The two prime facts apply at `ZMod 5`, from their stated hypotheses: the non-membership
(no degree bought by a prime that divides nothing already there) and the prime step (the level
series at `M` lies in the level-`M * p` field). Neither asks for a `ℚ`-algebra. -/
example (jg : LaurentSeries (ZMod 5)) (hjg : jg = jqModC (ZMod 5))
    {M p : ℕ} [NeZero M] [NeZero p] [hp : Fact (Nat.Prime p)] {ζ : (ZMod 5)ˣ}
    (hζ : IsPrimitiveRoot (ζ : ZMod 5) (M * p)) (hpM : ¬ p ∣ M) (h : PkgAt jg M)
    (hbase : levelSeries jg p ∉ (baseField jg : Set (LaurentSeries (ZMod 5)))) :
    levelSeries jg p ∉ levelField jg M ∧ levelSeries jg M ∈ levelField jg (M * p) :=
  ⟨prime_notMem_levelField (κ' := ZMod 5) jg hjg hζ hpM h hbase,
    levelSeries_mem_levelField_mul_prime (κ' := ZMod 5) jg hjg hζ h⟩

end ModularCurve
