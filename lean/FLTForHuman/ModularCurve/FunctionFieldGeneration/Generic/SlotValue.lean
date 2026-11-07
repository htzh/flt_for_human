/-
  The slot values at a general coefficient field.

  `slotValue ε jg ζ a b` is the value of `j` pushed to a twist of the level-`(a * a)` nome:
  the coefficient map `ε` carries the j-series into the target coefficient field, and the twist
  and the `q`-expansion act there. It is the general form of the `ℚ`-layer `sv`: at
  `ε = coeffEmb K`, `jg = jq` the two are the same function.

  Every statement that mentions two or more slots carries the **carrier condition**
  `ε jg = jqModC κ'`: it is what makes the slot values `TS` values, and the whole slot theory is
  read off `TS`. Without it the slot map is degenerate (`jg = 0` gives every slot `0`), so it is a
  genuine hypothesis, not bookkeeping.

  The public interface is `slotValue` and the five statements built on it: `slotValue_def` pins the
  shape of the definition, `slotValue_eq_TS` is the bridge to the `TS` vocabulary every slot
  computation runs on, `slotValue_inj` and `slotValue_inj_slot` are the separation of the slots (raw
  and slot bounds), and `slotValue_top` is the distinguished slot. The remaining spellings are
  `private`: `slotValue_eq` is `slotValue_def` on the nonzero branch, and
  `nodup_slotValues_slotValue` is `nodup_slotValues` applied to `slotValue_inj_slot`.

  The multiset API itself (`slotValues`, its cardinality, the product, the nodup criterion) is
  independent of the target field and is imported, not restated.

  The proofs are the `ℚ` ones of `FunctionFieldGeneration/SlotProduct.lean` with the carrier
  condition supplying what `coeffEmb_jq` supplies there; `slotValue_top` is the one statement whose
  `ℚ` form is a level-specific spelling, so its proof is a direct computation instead.
-/
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Generic.LevelPackage
import FLTForHuman.ModularCurve.FunctionFieldGeneration.SlotValues
import FLTForHuman.ModularCurve.Defs.TS
import FLTForHuman.ModularCurve.Defs.JqCoeff

set_option autoImplicit false

noncomputable section

open Polynomial HahnSeries IntermediateField
open scoped IntermediateField

namespace ModularCurve

variable {κ κ' : Type*} [Field κ] [Field κ']

/-- **The slot value.** The coefficient map carries the j-series up, then the twist `ζ ^ (b * a)`
and the `q`-expansion `q ↦ q ^ (a * a)` act in the working coefficient field. The `a = 0` branch is
`0`, as in the `ℚ` layer, so the function is total. -/
def slotValue (ε : LaurentSeries κ →+* LaurentSeries κ') (jg : LaurentSeries κ) (ζ : κ'ˣ)
    (a b : ℕ) : LaurentSeries κ' :=
  if h : a = 0 then 0 else
    letI : NeZero a := ⟨h⟩
    qExpand κ' (a * a) (qTwist (ζ ^ (b * a)) (ε jg))

/-- **The shape of the definition**, pinned: the dependent `if h : a = 0`, the
`letI : NeZero a := ⟨h⟩` of its else branch, and the exact argument order of `qExpand`/`qTwist`
around `ε jg`.

Its point is negative. The pinned `ℚ` statement `minpoly_jqN_map_eq_prod_slots` inlines this `dite`
as the spelling of its slot factor, and the layer's delegation closes only because `slotValue` *is*
that expression. A clean-up that left every theorem below true but changed the shape — a
non-dependent `if a = 0`, or the `NeZero` instance hoisted into the argument list — would make this
statement unprovable while the generic theory stayed silent. This lemma is the tripwire. -/
theorem slotValue_def (ε : LaurentSeries κ →+* LaurentSeries κ') (jg : LaurentSeries κ)
    (ζ : κ'ˣ) (a b : ℕ) :
    slotValue ε jg ζ a b =
      (if h : a = 0 then 0 else
        letI : NeZero a := ⟨h⟩
        qExpand κ' (a * a) (qTwist (ζ ^ (b * a)) (ε jg))) :=
  rfl

/-- The defining equation, on the nonzero branch. Private: it is the `dite` of the definition, and
only this module's proofs want it. -/
private theorem slotValue_eq (ε : LaurentSeries κ →+* LaurentSeries κ') (jg : LaurentSeries κ)
    (ζ : κ'ˣ) (a b : ℕ) [NeZero a] :
    slotValue ε jg ζ a b = qExpand κ' (a * a) (qTwist (ζ ^ (b * a)) (ε jg)) := by
  unfold slotValue
  rw [dite_eq_right (NeZero.ne a)]

/-- **The `TS` form**, given that `ε` carries the j-series to the target j-series. This is the form
the whole proof runs on: the slot is a twisted nome, and every slot computation is a `TS` one. -/
theorem slotValue_eq_TS (ε : LaurentSeries κ →+* LaurentSeries κ') (jg : LaurentSeries κ)
    (ζ : κ'ˣ) (a b : ℕ) [NeZero a] (hε : ε jg = jqModC κ') :
    slotValue ε jg ζ a b = TS κ' (a * a) (ζ ^ (b * a)) := by
  rw [slotValue_eq, hε]
  rfl

/-- **The slots separate their parameters**, in the raw bound form `b * a < M`. The carrier condition
is what makes the slot values `TS` values, and without it the statement is false: at `jg = 0` every
slot is `0`. Public because the pinned `ℚ` statement `sv_inj` is stated on these raw bounds, not on
the slot bounds the other callers hold, so the layer delegates here instead of to
`slotValue_inj_slot`. -/
theorem slotValue_inj (ε : LaurentSeries κ →+* LaurentSeries κ') (jg : LaurentSeries κ)
    (hε : ε jg = jqModC κ') {M : ℕ} {ζ : κ'ˣ} (hζ : IsPrimitiveRoot (ζ : κ') M) {a b a' b' : ℕ}
    (ha0 : a ≠ 0) (ha0' : a' ≠ 0) (hb : b * a < M) (hb' : b' * a' < M)
    (h : slotValue ε jg ζ a b = slotValue ε jg ζ a' b') : a = a' ∧ b = b' := by
  have : NeZero a := ⟨ha0⟩
  have : NeZero a' := ⟨ha0'⟩
  rw [slotValue_eq_TS ε jg ζ a b hε, slotValue_eq_TS ε jg ζ a' b' hε] at h
  obtain ⟨he, hu⟩ := TS_injective h
  have haa : a = a' := (mul_self_inj (Nat.zero_le a) (Nat.zero_le a')).mp he
  subst haa
  refine ⟨rfl, ?_⟩
  have hv : ((ζ : κ')) ^ (b * a) = ((ζ : κ')) ^ (b' * a) := by
    have h1 := congrArg Units.val hu
    rwa [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val] at h1
  have h2 : b * a = b' * a := hζ.pow_inj hb hb' hv
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero ha0) h2

/-- `slotValue_inj` with the slot bounds (`a ∣ M`, `b < M / a`) supplying `b * a < M`. -/
theorem slotValue_inj_slot (ε : LaurentSeries κ →+* LaurentSeries κ') (jg : LaurentSeries κ)
    (hε : ε jg = jqModC κ') {M : ℕ} {ζ : κ'ˣ} (hζ : IsPrimitiveRoot (ζ : κ') M) (hM0 : M ≠ 0)
    {a b a' b' : ℕ} (haM : a ∣ M) (haM' : a' ∣ M) (hb : b < M / a) (hb' : b' < M / a')
    (h : slotValue ε jg ζ a b = slotValue ε jg ζ a' b') : a = a' ∧ b = b' := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hM0 (Nat.eq_zero_of_zero_dvd haM)
  have ha0' : a' ≠ 0 := by
    rintro rfl
    exact hM0 (Nat.eq_zero_of_zero_dvd haM')
  have hba : b * a < M := by
    calc b * a < M / a * a :=
        (Nat.mul_lt_mul_right (Nat.pos_of_ne_zero ha0)).mpr hb
      _ = M := Nat.div_mul_cancel haM
  have hba' : b' * a' < M := by
    calc b' * a' < M / a' * a' :=
        (Nat.mul_lt_mul_right (Nat.pos_of_ne_zero ha0')).mpr hb'
      _ = M := Nat.div_mul_cancel haM'
  exact slotValue_inj ε jg hε hζ ha0 ha0' hba hba' h

/-- **The distinguished slot** `(a, b) = (M, 0)`: the `M`-fold `q`-expansion of the carried
j-series. With the level-commutation hypothesis this is `ε (qExpand κ M (levelSeries jg M))`, the
`ℚ` layer's `sv_top`. Public because its consumers are in the product's module — the base case and
the `a = M` root — not here; the `ℚ` analogue is `private` only because both live beside it. -/
theorem slotValue_top (ε : LaurentSeries κ →+* LaurentSeries κ') (jg : LaurentSeries κ)
    (M : ℕ) [NeZero M] (ζ : κ'ˣ) :
    slotValue ε jg ζ M 0 = qExpand κ' (M * M) (ε jg) := by
  rw [slotValue_eq, zero_mul, pow_zero, qTwist_one_apply]

/-- **The slots of a primitive root are distinct**: the slot multiset has no repetitions. Private: it is
`nodup_slotValues` applied to `slotValue_inj_slot` — the two halves are the interface. -/
private theorem nodup_slotValues_slotValue (ε : LaurentSeries κ →+* LaurentSeries κ')
    (jg : LaurentSeries κ) (hε : ε jg = jqModC κ') {M : ℕ} {ζ : κ'ˣ} (hM0 : M ≠ 0)
    (hζ : IsPrimitiveRoot (ζ : κ') M) :
    (slotValues M (fun a b => slotValue ε jg ζ a b)).Nodup := by
  refine nodup_slotValues fun a b a' b' ha ha' hb hb' h => ?_
  exact slotValue_inj_slot ε jg hε hζ hM0 (Nat.mem_divisors.mp ha).1 (Nat.mem_divisors.mp ha').1
    (Finset.mem_range.mp (Finset.mem_filter.mp hb).1)
    (Finset.mem_range.mp (Finset.mem_filter.mp hb').1) h

end ModularCurve
