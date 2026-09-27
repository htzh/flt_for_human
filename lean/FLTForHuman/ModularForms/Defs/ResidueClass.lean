/-
  The residue-class vocabulary of `ℤ` and `ZMod N`.

  `cls N b` is the set of integers in the residue class `b` mod `N`, `clsEquiv`
  and `clsNegEquiv` are the standard bijections `ℤ ≃ cls N b` and
  `cls N b ≃ cls N (-b)`, and `tsum_cls_split` decomposes a sum over `cls N b`
  into its zero, positive and negative parts.

  This is shared arithmetic vocabulary, not Eisenstein-specific: the pin writes
  the block `private` inside the `CardC` namespace of
  `P2M/Sol/S_EisensteinSeries_qExpansion_eisensteinG_coeff.lean` (pinned
  `aa2d8b3`). The port promotes it here so that a consumer of the general
  Eisenstein series (or of any other residue-class computation) can name it.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order

set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped Topology

namespace ResidueClass

variable {N : ℕ}

/-- The integers in the residue class `b` mod `N`. -/
abbrev cls (N : ℕ) (b : ZMod N) : Type := {d : ℤ // (d : ZMod N) = b}

section NeZero

variable [NeZero N]

/-- The bijection `ℤ ≃ cls N b` sending `j` to `b.val + N * j`. -/
def clsEquiv (b : ZMod N) : ℤ ≃ cls N b where
  toFun j := ⟨(b.val : ℤ) + N * j, by simp⟩
  invFun d := (d.1 - b.val) / N
  left_inv j := by
    have hN : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
    simp only [add_sub_cancel_left]
    exact Int.mul_ediv_cancel_left _ hN
  right_inv d := by
    apply Subtype.ext
    have hdvd : (N : ℤ) ∣ d.1 - b.val := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [d.2, ZMod.natCast_zmod_val, sub_self]
    simp only
    rw [Int.mul_ediv_cancel' hdvd]
    ring

end NeZero

/-- Negation as an equivalence `cls N b ≃ cls N (-b)`. -/
def clsNegEquiv (b : ZMod N) : cls N b ≃ cls N (-b) where
  toFun d := ⟨-d.1, by simp [d.2]⟩
  invFun d := ⟨-d.1, by simp [d.2]⟩
  left_inv d := by apply Subtype.ext; simp
  right_inv d := by apply Subtype.ext; simp

/-- A sum over the residue class `cls N b` splits into its zero, positive and
negative parts. -/
lemma tsum_cls_split (b : ZMod N) (F : ℤ → ℂ) (hF : Summable F) :
    ∑' c : cls N b, F c.1 =
      (if (0 : ZMod N) = b then F 0 else 0) +
        ∑' c : ℕ+, (if ((c : ℕ) : ZMod N) = b then F c else 0) +
        ∑' c : ℕ+, (if ((-((c : ℕ) : ℤ) : ℤ) : ZMod N) = b then F (-((c : ℕ) : ℤ)) else 0) := by
  set G : ℤ → ℂ := fun c => if ((c : ZMod N)) = b then F c else 0 with hG
  have hG' : Summable G := by
    have hGF : G = {c : ℤ | (c : ZMod N) = b}.indicator F := by
      funext c
      simp only [hG, Set.indicator_apply, Set.mem_ofPred_eq]
    rw [hGF]
    exact hF.indicator _
  have h1 : ∑' c : cls N b, F c.1 = ∑' c : ℤ, G c := by
    rw [show (∑' c : cls N b, F c.1) = ∑' c : ({c : ℤ | (c : ZMod N) = b} : Set ℤ), F c from rfl,
      tsum_subtype]
    refine tsum_congr fun c => ?_
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, hG]
  have hs1 : Summable fun n : ℕ => G n := hG'.comp_injective Nat.cast_injective
  have hs2 : Summable fun n : ℕ => G (-(n + 1)) :=
    hG'.comp_injective (i := fun n : ℕ => (-(n + 1) : ℤ)) (fun m n h => by simpa using h)
  rw [h1, tsum_of_nat_of_neg_add_one hs1 hs2, hs1.tsum_eq_zero_add]
  congr 1
  · congr 1
    · simp [hG]
    · rw [tsum_pnat_eq_tsum_succ (f := fun c : ℕ => if ((c : ℕ) : ZMod N) = b then F c else 0)]
      simp [hG]
  · rw [tsum_pnat_eq_tsum_succ (f := fun c : ℕ =>
      if ((-((c : ℕ) : ℤ) : ℤ) : ZMod N) = b then F (-((c : ℕ) : ℤ)) else 0)]
    refine tsum_congr fun c => ?_
    simp [hG]

end ResidueClass
