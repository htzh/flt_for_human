/-
Finiteness of the `[n]`-fibres of an elliptic curve, after the pinned FLT
`P2M/Sol/S_WeierstrassCurve_Affine_fibSet_finite.lean` (57 ln) and its wrapper
`Theorems/Thm_WeierstrassCurve_Affine_fibSet_finite.lean`, published as
`WeierstrassCurve.Affine.fibSet_finite`
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_Affine_fibSet_finite.lean>).

The `n`-torsion of an elliptic curve over an algebraically closed field is finite
of order `n²`, so every fibre of multiplication by `n` — the set
`fibSet W K n Q = {P | n • P = Q}` from `WeilPairingFun.lean` — is either empty or
a translate of it, hence finite. This is the finiteness half of the fibre
dictionary the Weil-pairing construction rests on; `ncard_fibSet` and
`valuation_weilNum` are its next consumers.

`torsion_finite` and `card_torsion_toFinset` are a byte-identical private prelude
of **three** pin `S_` files (`fibSet_finite`, `ncard_fibSet`,
`valuation_weilNum`): they are promoted here, once, public at the pin's names, so
the later consumers import rather than re-prove them (playbook §2.4). The
module-local `fibSet_finite'` is the pin's public helper; the headline is
re-exported at the wrapper's name (`solution` → `fibSet_finite`).

Statements are transcribed verbatim from the pin (only proof bodies adapted to
mathlib `v4.34.0`; the pin's `WeierstrassCurve.card_torsion_of_isAlgClosed` is the
port's `FLTForHuman.Elliptic.card_torsion_of_isAlgClosed`).

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_Affine_fibSet_finite.lean>
-/
import FLTForHuman.WeierstrassCurve.WeilPairingFun
import FLTForHuman.Elliptic.TorsionCard
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Set.Finite.Basic

set_option autoImplicit false
set_option linter.style.haveILetI false

open WeierstrassCurve WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

namespace WeilDiv

variable {F : Type*} [Field F] {K : Type*} [Field K] [Algebra F K] [DecidableEq K] [IsAlgClosed K]
  (W : WeierstrassCurve F) [W.IsElliptic]

theorem torsion_finite {n : ℕ} (hn : (n : K) ≠ 0) :
    {S : (W⁄K).Point | (n : ℤ) • S = 0}.Finite := by
  have hcard := FLTForHuman.Elliptic.card_torsion_of_isAlgClosed (K := K) W hn
  have hn0 : n ≠ 0 := by rintro rfl; exact hn Nat.cast_zero
  haveI : Finite (Submodule.torsionBy ℤ (W⁄K).Point n) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hn0)
  have hset : {S : (W⁄K).Point | (n : ℤ) • S = 0} =
      ((Submodule.torsionBy ℤ (W⁄K).Point n : Submodule ℤ (W⁄K).Point) : Set (W⁄K).Point) := by
    ext S
    rw [Set.mem_ofPred_eq, SetLike.mem_coe, Submodule.mem_torsionBy_iff]
  rw [hset]
  exact Set.toFinite _

theorem card_torsion_toFinset {n : ℕ} (hn : (n : K) ≠ 0) :
    (torsion_finite W hn).toFinset.card = n ^ 2 := by
  rw [← FLTForHuman.Elliptic.card_torsion_of_isAlgClosed (K := K) W hn,
    ← Nat.card_eq_card_finite_toFinset]
  have hset : {S : (W⁄K).Point | (n : ℤ) • S = 0} =
      ((Submodule.torsionBy ℤ (W⁄K).Point n : Submodule ℤ (W⁄K).Point) : Set (W⁄K).Point) := by
    ext S
    rw [Set.mem_ofPred_eq, SetLike.mem_coe, Submodule.mem_torsionBy_iff]
  rw [hset]
  rfl

theorem fibSet_finite' {n : ℕ} (hn : (n : K) ≠ 0) (Q : (W⁄K).Point) :
    (fibSet W K n Q).Finite := by
  by_cases hne : ∃ P₀ : (W⁄K).Point, (n : ℤ) • P₀ = Q
  · obtain ⟨P₀, hP₀⟩ := hne
    refine ((torsion_finite W hn).image (· + P₀)).subset ?_
    intro P hP
    rw [mem_fibSet] at hP
    refine ⟨P - P₀, ?_, sub_add_cancel P P₀⟩
    show (n : ℤ) • (P - P₀) = 0
    rw [smul_sub, hP, hP₀, sub_self]
  · exact Set.finite_empty.subset fun P hP => (hne ⟨P, hP⟩).elim

end WeilDiv

theorem fibSet_finite {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K]
    [IsAlgClosed K] (W : WeierstrassCurve F) [W.IsElliptic] {n : ℕ} (hn : (n : K) ≠ 0)
    (Q : (W⁄K).Point) : (fibSet W K n Q).Finite := by
  exact WeilDiv.fibSet_finite' W hn Q

end WeierstrassCurve.Affine

#print axioms WeierstrassCurve.Affine.fibSet_finite
