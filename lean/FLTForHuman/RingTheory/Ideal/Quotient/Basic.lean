/-
  Mathlib supplement: `Ideal.Quotient.out_sub`.

  Backported from the pin's `Definitions/Def_Mathlib_RingTheory_Ideal_Quotient_Basic.lean`
  (pinned `aa2d8b3`), which mirrors the mathlib path
  `Mathlib/RingTheory/Ideal/Quotient/Basic.lean`; it therefore lives at that path under
  `FLTForHuman/`. `v4.34.0` does not carry it, so it is transcribed as stated, with the
  pin's section variables so the checker diffs the statement verbatim.
-/
import Mathlib.RingTheory.Ideal.Quotient.Basic

set_option autoImplicit false

variable {R : Type*} [Ring R] (I : Ideal R) [I.IsTwoSided]

-- pin: Ideal.Quotient.out_sub (Def_Mathlib_RingTheory_Ideal_Quotient_Basic.lean:7)
theorem Ideal.Quotient.out_sub (x : R) : (Ideal.Quotient.mk I x).out - x ∈ I := by
  rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out]
