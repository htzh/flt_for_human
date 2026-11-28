/-
The residue span's finrank, bounded by the divisor's `ell`.

`AlgebraicCurve.RegularProlongation.exists_forall_finrank_residueSpan_inf_add_card_le` (638 pin lines,
43 declarations): in the same setup as the Krull-dimension-one row, for the divisors
`Db i w = max 0 (-w.ord (f i))` there is `M₀` such that for every `M ≥ M₀` the intersection of the
`f`-residue span with the `M`-twisted `f⁻¹`-residue span is finite dimensional and its finrank plus
`card ι` is at most `∑ i, ell (M • Db i)` plus the finrank of the untwisted intersection.

The engine is the `M`-window calculus (`mulEquiv`, `ordSub`, `Bsub`, `piEquiv`, `single_mem_window`,
`Bsub_le_iSup`) and the `ST`/`rv` residue submodules; it consumes SET-AF108B's monic-polynomial row
(`RegularProlongationResidueOrd.lean`), the residue basis' finite-dimensionality
(`RegularProlongationResidueBasis.lean`), `RegularProlongationResidueIntegralClosure`'s
`isAlgClosed_residueField`, the genus inputs (`Genus/Index`, `Genus/ConstantFieldExtensionConsequences`,
`IsCurveOver/Transcendental`, `LinearAlgebra/FinrankStableInequality`) and the `ord` calculus
(`Defs/Place`, `Defs/PlaceCalculus`). Again no existing module is above all of its premises, so the home
is new; the module is `RegularProlongationResidueKrullDim`'s sibling, not its consumer (their premise
sets are disjoint apart from the ord layer).

## The rows

* `AlgebraicCurve.RegularProlongation.exists_forall_finrank_residueSpan_inf_add_card_le` — 638 pin `S_` lines.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_forall_finrank_residueSpan_inf_add_card_le.lean>

## Transcription notes

Transcribed from `P2M/Sol/S_AlgebraicCurve_RegularProlongation_exists_forall_finrank_residueSpan_inf_add_card_le.lean`
(pinned `aa2d8b3`), 43 pin declarations, all public in the pin and all public here. The pin's generated
label `P2MW.S_…`/`CountAssembly` is dropped: everything sits in `AlgebraicCurve.RegularProlongation`,
and the pin's trailing `solution` (its `p2m_reactivate`d wrapper) becomes the headline. `p2m_reactivate`
and the pin's module-wide `attribute [-instance]`/`attribute [-simp]` prelude are not transcribed (this
module imports 15 narrow modules rather than `Mathlib`).

**Three declarations are substituted, not restated** (each is already public in the port, with the pin's
statement up to binder spelling):

| pin decl | pin line | port home |
|---|---|---|
| `ord_pow'` | `:107` | `AlgebraicCurve.RegularProlongation.DeuringMultiplicity.ord_pow` |
| `transcendental_inv` | `:333` | `AlgebraicCurve.transcendental_inv` (`Canonical/AffineChart.lean`) |
| `adjoin_inv_eq` | `:342` | `AlgebraicCurve.RegularProlongation.ResidueIntegralClosure.adjoin_inv_eq` |

The remaining 40 rows are the pin's own, verbatim. `ne_zero_of_transcendental` is the pin's and has no
port namesake. The substitutions named in `tools/deps`' substitutions table that were **rejected**:
`mulEquiv` (`GroupTheory/ModularGroup/FreeProduct.lean`) and `piEquiv`
(`NumberTheory/AdelicLevel/LatticeCounting.lean`, `private`) are type-only last-name matches — the
pin's are this module's `M`-window calculus; `core` (`AlgebraicCurve/DivisorPlaceReduction.lean`) is a
different theorem and is not substituted.

**Heartbeat site** (`core`; the pin installs `set_option maxHeartbeats 3200000` on it, not installed
here). Low-cap probe ladder (§"the house policies"), one run per value of
`lake env lean -DautoImplicit=false -DmaxHeartbeats=<cap>` on this module, `core`'s proof present:

| cap | verdict |
|---|---|
| `40000` | **ok**, silent, 11.5 s wall |
| `20000` | fail — `core` times out: the tactic in `hgen'` (the second `exists_forall_mem_span_pow_mul_of_forall_ord_nonneg` family) and `whnf` at the `core` signature |
| `10000` | fail — `whnf` at the `core` signature, `core` unbuildable |
| `5000` | fail — `isDefEq` in `hL0` (the `ell (0 : Divisor …) = 1` transport), `whnf` at the `core` signature |
| `1000` | fail — 20 errors, the whole window calculus gone |

So the module floor is between 20,000 and 40,000 heartbeats and it is **entirely inside `core`'s
proof**: everything else in the module — the whole `M`-window calculus, `rv`/`ST`, the field-theory
helpers — elaborates below the 20,000 run's first failure, so the cost is not in the statements. The
pin needed 3,200,000 for this declaration; the port needs under 40,000. Nothing is installed: there is
no `set_option maxHeartbeats` (or `synthInstance.maxHeartbeats`) anywhere in this file.

**Linter: declaration-scoped only.** `core` carries `set_option linter.style.haveILetI false in`. The
measured reason is the `FinrankStableInequality` precedent: its six `haveI`s (`IsAlgClosed 𝕜` from
the residue field, `hfd`, the per-`i` `hfa`/`hcurve`/`hL0`/`hL` families) are genuine *instance*
binders — the downstream instance searches (`IsCurveOver.toHasPrincipalDivisors`,
`finiteDimensional_lSpace`'s `[FiniteDimensional 𝕜 (LSpace 0)]`, the `[FiniteDimensional ⟮u i⟯]`
binders of `exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental` and
`exists_forall_mem_span_pow_mul_of_forall_ord_nonneg`) do not recover them from `have`, so the pin's
`haveI`s are kept and only the style warning is silenced. No other linter fires, so no other option is
used and no linter is silenced module-wide.

**No `private` helper** (the pin has none in this file), so no surface-gate decision: all 40 restated
rows are public, exactly as in the pin.

spec-pin: Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_forall_finrank_residueSpan_inf_add_card_le.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_RegularProlongation_exists_forall_finrank_residueSpan_inf_add_card_le.lean
-/
import FLTForHuman.AlgebraicCurve.ConstantReduction
import FLTForHuman.AlgebraicCurve.Defs.AdelicIndex
import FLTForHuman.AlgebraicCurve.Defs.Place
import FLTForHuman.AlgebraicCurve.Defs.PlaceCalculus
import FLTForHuman.AlgebraicCurve.Defs.Repartitions
import FLTForHuman.AlgebraicCurve.Genus.ConstantFieldExtensionConsequences
import FLTForHuman.AlgebraicCurve.Genus.Index
import FLTForHuman.AlgebraicCurve.IsCurveOver.ConstantFieldExtensionSpan
import FLTForHuman.AlgebraicCurve.IsCurveOver.Transcendental
import FLTForHuman.AlgebraicCurve.RegularProlongation
import FLTForHuman.AlgebraicCurve.RegularProlongationResidueBasis
import FLTForHuman.AlgebraicCurve.RegularProlongationResidueIntegralClosure
import FLTForHuman.AlgebraicCurve.RegularProlongationResidueOrd
import FLTForHuman.FieldTheory.ValuationSubringResidueField
import FLTForHuman.LinearAlgebra.FinrankStableInequality
import Mathlib.Tactic

set_option autoImplicit false

open AlgebraicCurve Polynomial IsLocalRing

noncomputable section

namespace AlgebraicCurve.RegularProlongation

universe u v w

section General

variable {k : Type u} [Field k] {ι : Type v} {Fb : ι → Type w} [∀ i, Field (Fb i)]
  [∀ i, Algebra k (Fb i)]

def mulEquiv (u : ∀ i, Fb i) (hu : ∀ i, u i ≠ 0) : (∀ i, Fb i) ≃ₗ[k] (∀ i, Fb i) where
  toFun x := u * x
  invFun x := u⁻¹ * x
  map_add' x y := mul_add u x y
  map_smul' c x := by
    ext i
    simp [Pi.smul_apply]
  left_inv x := by
    ext i
    simp [hu i]
  right_inv x := by
    ext i
    simp [hu i]

@[scoped simp] theorem mulEquiv_apply (u : ∀ i, Fb i) (hu : ∀ i, u i ≠ 0) (x : ∀ i, Fb i) :
    mulEquiv (k := k) u hu x = u * x := rfl

@[scoped simp] theorem mulEquiv_symm_apply (u : ∀ i, Fb i) (hu : ∀ i, u i ≠ 0) (x : ∀ i, Fb i) :
    (mulEquiv (k := k) u hu).symm x = u⁻¹ * x := rfl

theorem inv_ne_zero_pi {u : ∀ i, Fb i} (hu : ∀ i, u i ≠ 0) : ∀ i, u⁻¹ i ≠ 0 := fun i => by
  simpa using inv_ne_zero (hu i)

theorem mulEquiv_symm_eq (u : ∀ i, Fb i) (hu : ∀ i, u i ≠ 0) :
    ((mulEquiv (k := k) u hu).symm : (∀ i, Fb i) →ₗ[k] (∀ i, Fb i)) =
      (mulEquiv (k := k) u⁻¹ (inv_ne_zero_pi hu) : (∀ i, Fb i) →ₗ[k] (∀ i, Fb i)) :=
  LinearMap.ext fun _ => rfl

theorem mulEquiv_pow_apply (u : ∀ i, Fb i) (hu : ∀ i, u i ≠ 0) (M : ℕ) (x : ∀ i, Fb i) :
    ((mulEquiv (k := k) u hu : (∀ i, Fb i) →ₗ[k] (∀ i, Fb i)) ^ M) x = u ^ M * x := by
  induction M generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, LinearEquiv.coe_coe, mulEquiv_apply, ih, pow_succ]
    ring

theorem aeval_mulEquiv_apply (u : ∀ i, Fb i) (hu : ∀ i, u i ≠ 0) (c : k[X]) (x : ∀ i, Fb i) :
    Polynomial.aeval (mulEquiv (k := k) u hu : (∀ i, Fb i) →ₗ[k] (∀ i, Fb i)) c x =
      fun i => Polynomial.aeval (u i) c * x i := by
  induction c using Polynomial.induction_on' with
  | add p q hp hq =>
    ext i
    simp only [map_add, LinearMap.add_apply, hp, hq, Pi.add_apply, add_mul]
  | monomial n a =>
    ext i
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, mulEquiv_pow_apply,
      Module.algebraMap_end_apply, Polynomial.aeval_monomial]
    simp only [Pi.smul_apply, Pi.mul_apply, Pi.pow_apply, Algebra.smul_def]
    ring

def ordSub (s : ∀ i, Place k (Fb i) → Prop) : Submodule k (∀ i, Fb i) where
  carrier := {h | ∀ i (w : Place k (Fb i)), s i w → 0 ≤ w.ord (h i)}
  add_mem' {a b} ha hb i w hw := by
    rcases eq_or_ne (a i + b i) 0 with h0 | h0
    · rw [Pi.add_apply, h0, Place.ord_zero]
    rcases eq_or_ne (a i) 0 with ha0 | ha0
    · rw [Pi.add_apply, ha0, zero_add]; exact hb i w hw
    rcases eq_or_ne (b i) 0 with hb0 | hb0
    · rw [Pi.add_apply, hb0, add_zero]; exact ha i w hw
    exact (le_min (ha i w hw) (hb i w hw)).trans (Place.min_ord_le_ord_add w h0)
  zero_mem' i w _ := by rw [Pi.zero_apply, Place.ord_zero]
  smul_mem' c a ha i w hw := by
    rcases eq_or_ne c 0 with rfl | hc
    · rw [zero_smul, Pi.zero_apply, Place.ord_zero]
    rw [Pi.smul_apply, Place.ord_smul_of_ne_zero w hc]
    exact ha i w hw

@[scoped simp] theorem mem_ordSub {s : ∀ i, Place k (Fb i) → Prop} {h : ∀ i, Fb i} :
    h ∈ ordSub s ↔ ∀ i (w : Place k (Fb i)), s i w → 0 ≤ w.ord (h i) := Iff.rfl

end General

section Window

variable {k : Type u} [Field k] {ι : Type v} {Fb : ι → Type w} [∀ i, Field (Fb i)]
  [∀ i, Algebra k (Fb i)]

def Bsub (u : ∀ i, Fb i) : Submodule k (∀ i, Fb i) := ordSub fun i w => 0 ≤ w.ord (u i)

def Bsub' (u : ∀ i, Fb i) : Submodule k (∀ i, Fb i) := ordSub fun i w => w.ord (u i) ≤ 0

theorem mem_Bsub {u h : ∀ i, Fb i} :
    h ∈ Bsub (k := k) u ↔ ∀ i (w : Place k (Fb i)), 0 ≤ w.ord (u i) → 0 ≤ w.ord (h i) := Iff.rfl

theorem mem_Bsub' {u h : ∀ i, Fb i} :
    h ∈ Bsub' (k := k) u ↔ ∀ i (w : Place k (Fb i)), w.ord (u i) ≤ 0 → 0 ≤ w.ord (h i) := Iff.rfl

theorem Bsub_inv (u : ∀ i, Fb i) : Bsub (k := k) u⁻¹ = Bsub' u := by
  ext h
  simp only [mem_Bsub, mem_Bsub', Pi.inv_apply, Place.ord_inv, neg_nonneg]

theorem Bsub'_inv (u : ∀ i, Fb i) : Bsub' (k := k) u⁻¹ = Bsub u := by
  rw [← Bsub_inv, inv_inv]

theorem Bsub_map_le (u : ∀ i, Fb i) (hu : ∀ i, u i ≠ 0) :
    (Bsub u).map (mulEquiv (k := k) u hu : (∀ i, Fb i) →ₗ[k] (∀ i, Fb i)) ≤ Bsub u := by
  rintro _ ⟨h, hh, rfl⟩ i w hw
  change 0 ≤ w.ord ((u * h) i)
  rcases eq_or_ne (h i) 0 with h0 | h0
  · rw [Pi.mul_apply, h0, mul_zero, Place.ord_zero]
  rw [Pi.mul_apply, Place.ord_mul _ (hu i) h0]
  exact add_nonneg hw (hh i w hw)

theorem nsmul_divisor_apply (D : ∀ i, Divisor k (Fb i)) (M : ℕ) (i : ι) (w : Place k (Fb i)) :
    (M • D i) w = (M : ℤ) * D i w := by
  rw [Finsupp.smul_apply, nsmul_eq_mul]

theorem window_eq (u : ∀ i, Fb i) (hu : ∀ i, u i ≠ 0) (D : ∀ i, Divisor k (Fb i))
    (hD : ∀ i (w : Place k (Fb i)), D i w = max 0 (-w.ord (u i))) (M : ℕ) :
    Bsub u ⊓ (Bsub' u).map ((mulEquiv (k := k) u hu : (∀ i, Fb i) →ₗ[k] (∀ i, Fb i)) ^ M) =
      Submodule.pi Set.univ fun i => LSpace (M • D i) := by
  ext h
  simp only [Submodule.mem_inf, Submodule.mem_map, Submodule.mem_pi, Set.mem_univ, true_implies,
    mulEquiv_pow_apply]
  constructor
  · rintro ⟨hB, g, hg, rfl⟩ i
    rw [mem_lSpace_iff_ord]
    rcases eq_or_ne (g i) 0 with h0 | h0
    · left; simp [h0]
    right
    intro w
    rw [nsmul_divisor_apply, hD i w]
    rcases le_or_gt 0 (w.ord (u i)) with hw | hw
    · rw [max_eq_left (neg_nonpos.mpr hw), mul_zero, neg_zero]
      exact hB i w hw
    · rw [max_eq_right (neg_nonneg.mpr hw.le), Pi.mul_apply, Pi.pow_apply,
        Place.ord_mul _ (pow_ne_zero _ (hu i)) h0, DeuringMultiplicity.ord_pow]
      have := hg i w hw.le
      linarith
  · intro hh
    refine ⟨fun i w hw => ?_, ⟨(u ^ M)⁻¹ * h, fun i w hw => ?_, ?_⟩⟩
    · rcases (mem_lSpace_iff_ord.mp (hh i)) with h0 | h1
      · rw [h0, Place.ord_zero]
      · have := h1 w
        rw [nsmul_divisor_apply, hD i w, max_eq_left (neg_nonpos.mpr hw), mul_zero,
          neg_zero] at this
        exact this
    · rcases eq_or_ne (h i) 0 with h0 | h0
      · rw [Pi.mul_apply, h0, mul_zero, Place.ord_zero]
      rcases (mem_lSpace_iff_ord.mp (hh i)) with h0' | h1
      · exact absurd h0' h0
      have := h1 w
      rw [nsmul_divisor_apply, hD i w, max_eq_right (neg_nonneg.mpr hw)] at this
      rw [Pi.mul_apply, Pi.inv_apply, Pi.pow_apply,
        Place.ord_mul _ (inv_ne_zero (pow_ne_zero _ (hu i))) h0, Place.ord_inv,
        DeuringMultiplicity.ord_pow]
      linarith
    · ext i
      simp [hu i]

end Window

section WindowRank

variable {k : Type u} [Field k] {ι : Type v} {Fb : ι → Type w} [∀ i, Field (Fb i)]
  [∀ i, Algebra k (Fb i)]

def piEquiv (p : ∀ i, Submodule k (Fb i)) : ↥(Submodule.pi Set.univ p) ≃ₗ[k] ∀ i, ↥(p i) where
  toFun x i := ⟨x.1 i, x.2 i (Set.mem_univ i)⟩
  invFun y := ⟨fun i => y i, fun i _ => (y i).2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem finite_pi (p : ∀ i, Submodule k (Fb i)) [∀ i, FiniteDimensional k ↥(p i)] [Finite ι] :
    FiniteDimensional k ↥(Submodule.pi Set.univ p) :=
  Module.Finite.equiv (piEquiv p).symm

theorem finrank_pi (p : ∀ i, Submodule k (Fb i)) [∀ i, FiniteDimensional k ↥(p i)] [Fintype ι] :
    Module.finrank k ↥(Submodule.pi Set.univ p) = ∑ i, Module.finrank k ↥(p i) := by
  rw [(piEquiv p).finrank_eq, Module.finrank_pi_fintype]

theorem card_le_finrank_inf [Fintype ι] (u : ∀ i, Fb i)
    [FiniteDimensional k ↥(Bsub (k := k) u ⊓ Bsub' u)] :
    Fintype.card ι ≤ Module.finrank k ↥(Bsub (k := k) u ⊓ Bsub' u) := by
  let c : (ι → k) →ₗ[k] (∀ i, Fb i) :=
    LinearMap.pi fun i => (Algebra.linearMap k (Fb i)).comp (LinearMap.proj i)
  have hc : Function.Injective c := by
    intro a b hab
    ext i
    have := congr_fun hab i
    simpa [c] using this
  have hrange : LinearMap.range c ≤ Bsub u ⊓ Bsub' u := by
    rintro _ ⟨a, rfl⟩
    refine ⟨fun i w _ => ?_, fun i w _ => ?_⟩ <;> simp [c, Place.ord_algebraMap]
  calc Fintype.card ι = Module.finrank k (ι → k) := (Module.finrank_fintype_fun_eq_card k).symm
    _ = Module.finrank k ↥(LinearMap.range c) := (LinearMap.finrank_range_of_inj hc).symm
    _ ≤ _ := Submodule.finrank_mono hrange

theorem pow_mul_single [DecidableEq ι] (u : ∀ i, Fb i) (i : ι) (j : ℕ) (y : Fb i) :
    u ^ j * Pi.single i y = Pi.single i (u i ^ j * y) := by
  ext i'
  by_cases h : i' = i
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem single_mem_window [DecidableEq ι] (u : ∀ i, Fb i) (hu : ∀ i, u i ≠ 0)
    (D : ∀ i, Divisor k (Fb i)) (hD : ∀ i (w : Place k (Fb i)), D i w = max 0 (-w.ord (u i)))
    (M : ℕ) (i : ι) (y : Fb i) (hy : y ∈ LSpace (M • D i)) :
    Pi.single i y ∈
      Bsub u ⊓ (Bsub' u).map ((mulEquiv (k := k) u hu : (∀ i, Fb i) →ₗ[k] (∀ i, Fb i)) ^ M) := by
  rw [window_eq u hu D hD M, Submodule.mem_pi]
  intro i' _
  by_cases h : i' = i
  · subst h; simpa using hy
  · rw [Pi.single_eq_of_ne h]; exact Submodule.zero_mem _

theorem divisor_nonneg (u : ∀ i, Fb i) (D : ∀ i, Divisor k (Fb i))
    (hD : ∀ i (w : Place k (Fb i)), D i w = max 0 (-w.ord (u i))) (i : ι) : 0 ≤ D i :=
  fun w => by rw [hD i w]; exact le_max_left _ _

theorem nsmul_divisor_mono (u : ∀ i, Fb i) (D : ∀ i, Divisor k (Fb i))
    (hD : ∀ i (w : Place k (Fb i)), D i w = max 0 (-w.ord (u i))) (i : ι) {a b : ℕ}
    (hab : a ≤ b) : a • D i ≤ b • D i := fun w => by
  simp only [nsmul_divisor_apply]
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hab) (divisor_nonneg u D hD i w)

theorem Bsub_le_iSup (u : ∀ i, Fb i) (hu : ∀ i, u i ≠ 0)
    (D : ∀ i, Divisor k (Fb i)) (hD : ∀ i (w : Place k (Fb i)), D i w = max 0 (-w.ord (u i)))
    (M₁ : ℕ) [Fintype ι]
    (hspan : ∀ i, ∃ Mi : ℕ, Mi ≤ M₁ ∧ ∀ h : Fb i,
      (∀ w : Place k (Fb i), 0 ≤ w.ord (u i) → 0 ≤ w.ord h) →
        h ∈ Submodule.span k {g : Fb i | ∃ j : ℕ, ∃ y ∈ LSpace (Mi • D i), g = u i ^ j * y}) :
    Bsub u ≤ ⨆ j : ℕ, (Bsub u ⊓ (Bsub' u).map
      ((mulEquiv (k := k) u hu : (∀ i, Fb i) →ₗ[k] (∀ i, Fb i)) ^ M₁)).map
        ((mulEquiv (k := k) u hu : (∀ i, Fb i) →ₗ[k] (∀ i, Fb i)) ^ j) := by
  classical
  intro h hh
  rw [← Finset.univ_sum_single h]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨Mi, hMi, hsp⟩ := hspan i
  have hhi := hsp (h i) (fun w hw => hh i w hw)
  have hle : (Submodule.span k
      {g : Fb i | ∃ j : ℕ, ∃ y ∈ LSpace (Mi • D i), g = u i ^ j * y}).map
        (LinearMap.single k Fb i) ≤
      ⨆ j : ℕ, (Bsub u ⊓ (Bsub' u).map
        ((mulEquiv (k := k) u hu : (∀ i, Fb i) →ₗ[k] (∀ i, Fb i)) ^ M₁)).map
          ((mulEquiv (k := k) u hu : (∀ i, Fb i) →ₗ[k] (∀ i, Fb i)) ^ j) := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨g, ⟨j, y, hy, rfl⟩, rfl⟩
    refine Submodule.mem_iSup_of_mem j ⟨Pi.single i y,
      single_mem_window u hu D hD M₁ i y (lSpace_mono (nsmul_divisor_mono u D hD i hMi) hy), ?_⟩
    rw [mulEquiv_pow_apply, LinearMap.coe_single, pow_mul_single]
  exact hle ⟨h i, hhi, rfl⟩

end WindowRank

section Concrete

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {ι : Type*} {Fb : ι → Type*} [∀ i, Field (Fb i)]
  [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
  (R : ∀ i, RegularProlongation A F (Fb i))

local notation "𝕜" => IsLocalRing.ResidueField A

def rv (g : F) (hg : ∀ i, g ∈ (R i).integers) : ∀ i, Fb i := fun i => (R i).residue ⟨g, hg i⟩

@[scoped simp] theorem rv_apply (g : F) (hg : ∀ i, g ∈ (R i).integers) (i : ι) :
    rv R g hg i = (R i).residue ⟨g, hg i⟩ := rfl

def ST (g : F) : Submodule 𝕜 (∀ i, Fb i) :=
  Submodule.span 𝕜 {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
    (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → g ∈ V → u ∈ V) ∧
    ∀ i, (R i).residue ⟨u, hu i⟩ = h i}

variable {R}

theorem ne_zero_of_residue_ne_zero {g : F} {hg : ∀ i, g ∈ (R i).integers} {i : ι}
    (h : (R i).residue ⟨g, hg i⟩ ≠ 0) : g ≠ 0 := by
  rintro rfl
  apply h
  have h0 : (⟨(0 : F), hg i⟩ : (R i).integers) = 0 := Subtype.ext (by simp)
  rw [h0, map_zero]

theorem inv_mem_integers {g : F} {hg : ∀ i, g ∈ (R i).integers}
    (h : ∀ i, (R i).residue ⟨g, hg i⟩ ≠ 0) (i : ι) : g⁻¹ ∈ (R i).integers := by
  obtain ⟨b, hb⟩ := ((R i).isUnit_of_residue_ne_zero (h i)).exists_right_inv
  have hb' : g * (b : F) = 1 := by simpa using congrArg Subtype.val hb
  rw [inv_eq_of_mul_eq_one_right hb']
  exact b.2

theorem residue_inv {g : F} {hg : ∀ i, g ∈ (R i).integers}
    (h : ∀ i, (R i).residue ⟨g, hg i⟩ ≠ 0) (i : ι) :
    (R i).residue ⟨g⁻¹, inv_mem_integers h i⟩ = ((R i).residue ⟨g, hg i⟩)⁻¹ := by
  have hg0 : g ≠ 0 := ne_zero_of_residue_ne_zero (h i)
  have hmul : (⟨g, hg i⟩ : (R i).integers) * ⟨g⁻¹, inv_mem_integers h i⟩ = 1 :=
    Subtype.ext (by simp [hg0])
  have := congrArg (R i).residue hmul
  rw [map_mul, map_one] at this
  exact (inv_eq_of_mul_eq_one_right this).symm

theorem ne_zero_of_transcendental {K E : Type*} [Field K] [Field E] [Algebra K E] {x : E}
    (hx : Transcendental K x) : x ≠ 0 := by
  rintro rfl
  exact hx isAlgebraic_zero

theorem ST_map_le (g : F) (hg : ∀ i, g ∈ (R i).integers) (u : ∀ i, Fb i) (hu : ∀ i, u i ≠ 0)
    (hug : ∀ i, (R i).residue ⟨g, hg i⟩ = u i) :
    (ST R g).map (mulEquiv (k := 𝕜) u hu : (∀ i, Fb i) →ₗ[𝕜] (∀ i, Fb i)) ≤ ST R g := by
  rw [ST, Submodule.map_span_le]
  rintro h ⟨u', hu', hV', hres'⟩
  refine Submodule.subset_span ⟨g * u', fun i => mul_mem (hg i) (hu' i),
    fun V hL hgV => mul_mem hgV (hV' V hL hgV), fun i => ?_⟩
  rw [LinearEquiv.coe_coe, mulEquiv_apply, Pi.mul_apply, ← hug i, ← hres' i, ← map_mul]
  rfl

theorem setM_eq (f : F) (hf : ∀ i, f ∈ (R i).integers) (hf' : ∀ i, f⁻¹ ∈ (R i).integers)
    (hf0 : f ≠ 0) (M : ℕ) :
    {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
        (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f⁻¹ ∈ V →
          u * (f ^ M)⁻¹ ∈ V) ∧
        ∀ i, (R i).residue ⟨u, hu i⟩ = h i} =
    (fun h => rv R f hf ^ M * h) '' {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
        (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f⁻¹ ∈ V → u ∈ V) ∧
        ∀ i, (R i).residue ⟨u, hu i⟩ = h i} := by
  ext h
  constructor
  · rintro ⟨u, hu, hV, hres⟩
    have hm : ∀ i, u * (f ^ M)⁻¹ ∈ (R i).integers := fun i => by
      rw [← inv_pow]; exact mul_mem (hu i) (pow_mem (hf' i) M)
    refine ⟨fun i => (R i).residue ⟨u * (f ^ M)⁻¹, hm i⟩, ⟨u * (f ^ M)⁻¹, hm, hV, fun i => rfl⟩,
      ?_⟩
    ext i
    show (rv R f hf ^ M * fun i => (R i).residue ⟨u * (f ^ M)⁻¹, hm i⟩) i = h i
    rw [Pi.mul_apply, Pi.pow_apply, rv_apply, ← hres i, ← map_pow, ← map_mul]
    congr 1
    apply Subtype.ext
    push_cast
    rw [mul_left_comm, mul_inv_cancel₀ (pow_ne_zero M hf0), mul_one]
  · rintro ⟨h', ⟨u', hu', hV', hres'⟩, rfl⟩
    refine ⟨u' * f ^ M, fun i => mul_mem (hu' i) (pow_mem (hf i) M), fun V hL hfV => ?_,
      fun i => ?_⟩
    · rw [mul_inv_cancel_right₀ (pow_ne_zero M hf0)]
      exact hV' V hL hfV
    · show _ = (rv R f hf ^ M * h') i
      rw [Pi.mul_apply, Pi.pow_apply, rv_apply, ← hres' i, ← map_pow, ← map_mul]
      congr 1
      apply Subtype.ext
      push_cast
      ring

theorem span_setM_eq (f : F) (hf : ∀ i, f ∈ (R i).integers) (hf' : ∀ i, f⁻¹ ∈ (R i).integers)
    (hf0 : f ≠ 0) (hu : ∀ i, rv R f hf i ≠ 0) (M : ℕ) :
    Submodule.span 𝕜 {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
        (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f⁻¹ ∈ V →
          u * (f ^ M)⁻¹ ∈ V) ∧
        ∀ i, (R i).residue ⟨u, hu i⟩ = h i} =
    (ST R f⁻¹).map ((mulEquiv (k := 𝕜) (rv R f hf) hu : (∀ i, Fb i) →ₗ[𝕜] (∀ i, Fb i)) ^ M) := by
  rw [ST, Submodule.map_span, setM_eq f hf hf' hf0 M]
  congr 1
  refine Set.image_congr fun h _ => ?_
  exact (mulEquiv_pow_apply (k := 𝕜) (rv R f hf) hu M h).symm

theorem tor_of_pointwise {k : Type*} [Field k] [∀ i, Algebra k (Fb i)] (u : ∀ i, Fb i)
    (hu : ∀ i, u i ≠ 0) (P B : Submodule k (∀ i, Fb i))
    (h : ∀ y : ∀ i, Fb i, ∃ c : k[X], c.Monic ∧ (fun i => aeval (u i) c * y i) ∈ P) :
    ∀ y ∈ B, ∃ c : k[X], c.Monic ∧
      aeval (mulEquiv (k := k) u hu : (∀ i, Fb i) →ₗ[k] (∀ i, Fb i)) c y ∈ P := fun y _ => by
  obtain ⟨c, hc, hy⟩ := h y
  exact ⟨c, hc, by rwa [aeval_mulEquiv_apply]⟩

end Concrete

section Assembly

variable {L : Type*} [Field L] [IsAlgClosed L] {A : ValuationSubring L} {F : Type*} [Field F]
  [Algebra L F] {ι : Type*} [Fintype ι] {Fb : ι → Type*} [∀ i, Field (Fb i)]
  [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]

local notation "𝕜" => IsLocalRing.ResidueField A

set_option linter.style.haveILetI false in
theorem core (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (hfd : FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F)
    (htr : ∀ i, Transcendental 𝕜 ((R i).residue ⟨f, hf i⟩))
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin 𝕜
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (Db : ∀ i, Divisor 𝕜 (Fb i))
    (hDb : ∀ i, ∀ w : Place 𝕜 (Fb i), Db i w = max 0 (-w.ord ((R i).residue ⟨f, hf i⟩)))
    (u : ∀ i, Fb i) (hu_def : ∀ i, (R i).residue ⟨f, hf i⟩ = u i) (hu : ∀ i, u i ≠ 0) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      FiniteDimensional 𝕜 ↥(ST R f ⊓ (ST R f⁻¹).map
        ((mulEquiv (k := 𝕜) u hu : (∀ i, Fb i) →ₗ[𝕜] (∀ i, Fb i)) ^ M)) ∧
      Module.finrank 𝕜 ↥(ST R f ⊓ (ST R f⁻¹).map
        ((mulEquiv (k := 𝕜) u hu : (∀ i, Fb i) →ₗ[𝕜] (∀ i, Fb i)) ^ M)) + Fintype.card ι ≤
        (∑ i, ell (M • Db i)) + Module.finrank 𝕜 ↥(ST R f ⊓ ST R f⁻¹) := by
  classical
  haveI : IsAlgClosed 𝕜 := ValuationSubring.isAlgClosed_residueField A
  haveI := hfd
  have htru : ∀ i, Transcendental 𝕜 (u i) := fun i => hu_def i ▸ htr i
  haveI hfa : ∀ i, FiniteDimensional (IntermediateField.adjoin 𝕜 ({u i} : Set (Fb i))) (Fb i) :=
    fun i => by
      rw [← hu_def i]
      exact finiteDimensional_adjoin_residue_of_sum_finrank_eq A Fb R hR f hf htr heq i
  haveI hcurve : ∀ i, IsCurveOver 𝕜 (Fb i) := fun i =>
    isCurveOver_of_isAlgClosed_of_transcendental (u i) (htru i)
  have hDb' : ∀ i (w : Place 𝕜 (Fb i)), Db i w = max 0 (-w.ord (u i)) := fun i w => by
    rw [← hu_def i]; exact hDb i w
  haveI hL0 : ∀ i, FiniteDimensional 𝕜 ↥(LSpace (0 : Divisor 𝕜 (Fb i))) := fun i => by
    have h1 := (exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental (u i) (htru i) (Db i)
      (hDb' i)).1
    exact Module.finite_of_finrank_pos
      (by rw [show Module.finrank 𝕜 ↥(LSpace (0 : Divisor 𝕜 (Fb i))) = 1 from h1]; exact one_pos)
  haveI hL : ∀ i (D : Divisor 𝕜 (Fb i)), FiniteDimensional 𝕜 ↥(LSpace D) := fun i D =>
    finiteDimensional_lSpace D

  have hwin : ∀ M : ℕ, Bsub u ⊓ (Bsub' u).map
      ((mulEquiv (k := 𝕜) u hu : (∀ i, Fb i) →ₗ[𝕜] (∀ i, Fb i)) ^ M) =
      Submodule.pi Set.univ fun i => LSpace (M • Db i) := window_eq u hu Db hDb'
  have hfin : ∀ M : ℕ, FiniteDimensional 𝕜 ↥(Bsub u ⊓ (Bsub' u).map
      ((mulEquiv (k := 𝕜) u hu : (∀ i, Fb i) →ₗ[𝕜] (∀ i, Fb i)) ^ M)) := fun M => by
    rw [hwin M]; exact finite_pi _
  have hrank : ∀ M : ℕ, Module.finrank 𝕜 ↥(Bsub u ⊓ (Bsub' u).map
      ((mulEquiv (k := 𝕜) u hu : (∀ i, Fb i) →ₗ[𝕜] (∀ i, Fb i)) ^ M)) = ∑ i, ell (M • Db i) :=
    fun M => by rw [hwin M, finrank_pi]

  obtain ⟨hPa, hPb⟩ :=
    forall_ord_residueSpan_nonneg_and_exists_monic_of_isAlgClosed A Fb R hR f hf hfd htr heq
  have hPB : ST R f ≤ Bsub (k := 𝕜) u := fun h hh i w hw =>
    hPa h hh i w (by rw [hu_def i]; exact hw)
  have htor : ∀ y ∈ Bsub (k := 𝕜) u, ∃ c : 𝕜[X], c.Monic ∧
      aeval (mulEquiv (k := 𝕜) u hu : (∀ i, Fb i) →ₗ[𝕜] (∀ i, Fb i)) c y ∈ ST R f := by
    refine tor_of_pointwise u hu (ST R f) (Bsub u) fun y => ?_
    obtain ⟨c, hc, hy⟩ := hPb y
    refine ⟨c, hc, ?_⟩
    have : (fun i => aeval (u i) c * y i) = fun i => aeval ((R i).residue ⟨f, hf i⟩) c * y i :=
      funext fun i => by rw [hu_def i]
    rw [this]; exact hy

  have hu0 : ∀ i, (R i).residue ⟨f, hf i⟩ ≠ 0 := fun i => by rw [hu_def i]; exact hu i
  have hf' : ∀ i, f⁻¹ ∈ (R i).integers := inv_mem_integers hu0
  have hres_inv : ∀ i, (R i).residue ⟨f⁻¹, hf' i⟩ = u⁻¹ i := fun i => by
    rw [Pi.inv_apply, ← hu_def i]; exact residue_inv hu0 i
  have htr' : ∀ i, Transcendental 𝕜 ((R i).residue ⟨f⁻¹, hf' i⟩) := fun i => by
    rw [hres_inv i]; exact AlgebraicCurve.transcendental_inv (htru i)
  have hfd' : FiniteDimensional (IntermediateField.adjoin L ({f⁻¹} : Set F)) F := by
    rw [ResidueIntegralClosure.adjoin_inv_eq]; exact hfd
  have heq' : ∑ i, Module.finrank (IntermediateField.adjoin 𝕜
      ({(R i).residue ⟨f⁻¹, hf' i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f⁻¹} : Set F)) F := by
    rw [ResidueIntegralClosure.adjoin_inv_eq, ← heq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hres_inv i, Pi.inv_apply, ResidueIntegralClosure.adjoin_inv_eq, ← hu_def i]
  obtain ⟨hPa', hPb'⟩ :=
    forall_ord_residueSpan_nonneg_and_exists_monic_of_isAlgClosed A Fb R hR f⁻¹ hf' hfd' htr'
      heq'
  have hP'B' : ST R f⁻¹ ≤ Bsub' (k := 𝕜) u := fun h hh i w hw => by
    have := hPa' h hh i w
    rw [hres_inv i, Pi.inv_apply, Place.ord_inv, neg_nonneg] at this
    exact this hw
  have htor' : ∀ y ∈ Bsub' (k := 𝕜) u, ∃ c : 𝕜[X], c.Monic ∧
      aeval ((mulEquiv (k := 𝕜) u hu).symm : (∀ i, Fb i) →ₗ[𝕜] (∀ i, Fb i)) c y ∈ ST R f⁻¹ := by
    rw [mulEquiv_symm_eq]
    refine tor_of_pointwise u⁻¹ (inv_ne_zero_pi hu) (ST R f⁻¹) (Bsub' u) fun y => ?_
    obtain ⟨c, hc, hy⟩ := hPb' y
    refine ⟨c, hc, ?_⟩
    have : (fun i => aeval (u⁻¹ i) c * y i) =
        fun i => aeval ((R i).residue ⟨f⁻¹, hf' i⟩) c * y i :=
      funext fun i => by rw [hres_inv i]
    rw [this]; exact hy

  have hP : (ST R f).map (mulEquiv (k := 𝕜) u hu : (∀ i, Fb i) →ₗ[𝕜] (∀ i, Fb i)) ≤ ST R f :=
    ST_map_le f hf u hu hu_def
  have hB := Bsub_map_le (k := 𝕜) u hu
  have hP' : (ST R f⁻¹).map ((mulEquiv (k := 𝕜) u hu).symm : (∀ i, Fb i) →ₗ[𝕜] (∀ i, Fb i)) ≤
      ST R f⁻¹ := by
    rw [mulEquiv_symm_eq]; exact ST_map_le f⁻¹ hf' u⁻¹ (inv_ne_zero_pi hu) hres_inv
  have hB' : (Bsub' (k := 𝕜) u).map
      ((mulEquiv (k := 𝕜) u hu).symm : (∀ i, Fb i) →ₗ[𝕜] (∀ i, Fb i)) ≤ Bsub' u := by
    rw [mulEquiv_symm_eq, ← Bsub_inv]; exact Bsub_map_le u⁻¹ _

  have hgen : ∃ M₁ : ℕ, Bsub (k := 𝕜) u ≤ ⨆ j : ℕ, (Bsub u ⊓ (Bsub' u).map
      ((mulEquiv (k := 𝕜) u hu : (∀ i, Fb i) →ₗ[𝕜] (∀ i, Fb i)) ^ M₁)).map
        ((mulEquiv (k := 𝕜) u hu : (∀ i, Fb i) →ₗ[𝕜] (∀ i, Fb i)) ^ j) := by
    have hn : ∀ i, ∃ Mi : ℕ, ∀ h : Fb i, (∀ w : Place 𝕜 (Fb i), 0 ≤ w.ord (u i) → 0 ≤ w.ord h) →
        h ∈ Submodule.span 𝕜
          {g : Fb i | ∃ j : ℕ, ∃ y ∈ LSpace (Mi • Db i), g = u i ^ j * y} :=
      fun i => exists_forall_mem_span_pow_mul_of_forall_ord_nonneg (u i) (htru i) (Db i) (hDb' i)
    choose Mi hMi using hn
    exact ⟨Finset.univ.sup Mi, Bsub_le_iSup u hu Db hDb' _ fun i =>
      ⟨Mi i, Finset.le_sup (Finset.mem_univ i), hMi i⟩⟩
  have hgen' : ∃ M₁ : ℕ, Bsub' (k := 𝕜) u ≤ ⨆ j : ℕ, (Bsub' u ⊓ (Bsub u).map
      (((mulEquiv (k := 𝕜) u hu).symm : (∀ i, Fb i) →ₗ[𝕜] (∀ i, Fb i)) ^ M₁)).map
        (((mulEquiv (k := 𝕜) u hu).symm : (∀ i, Fb i) →ₗ[𝕜] (∀ i, Fb i)) ^ j) := by
    have hD'ex : ∀ i, ∃ D : Divisor 𝕜 (Fb i), ∀ w : Place 𝕜 (Fb i),
        D w = max 0 (-w.ord (u⁻¹ i)) := fun i => by
      obtain ⟨E, hE, -⟩ := HasPrincipalDivisors.exists_divisor (K := 𝕜) (u i) (hu i)
      exact ⟨E.mapRange (fun n => max 0 n) (by simp), fun w => by
        rw [Finsupp.mapRange_apply, hE w, Pi.inv_apply, Place.ord_inv, neg_neg]⟩
    choose D' hD' using hD'ex
    haveI : ∀ i, FiniteDimensional (IntermediateField.adjoin 𝕜 ({u⁻¹ i} : Set (Fb i))) (Fb i) :=
      fun i => by rw [Pi.inv_apply, ResidueIntegralClosure.adjoin_inv_eq]; exact hfa i
    have hn : ∀ i, ∃ Mi : ℕ, ∀ h : Fb i,
        (∀ w : Place 𝕜 (Fb i), 0 ≤ w.ord (u⁻¹ i) → 0 ≤ w.ord h) →
        h ∈ Submodule.span 𝕜
          {g : Fb i | ∃ j : ℕ, ∃ y ∈ LSpace (Mi • D' i), g = u⁻¹ i ^ j * y} :=
      fun i => exists_forall_mem_span_pow_mul_of_forall_ord_nonneg (u⁻¹ i)
        (AlgebraicCurve.transcendental_inv (htru i)) (D' i) (hD' i)
    choose Mi hMi using hn
    rw [mulEquiv_symm_eq, ← Bsub_inv u, ← Bsub'_inv u]
    exact ⟨Finset.univ.sup Mi, Bsub_le_iSup u⁻¹ (inv_ne_zero_pi hu) D' hD' _ fun i =>
      ⟨Mi i, Finset.le_sup (Finset.mem_univ i), hMi i⟩⟩

  obtain ⟨M₀, hM₀⟩ := LinearEquiv.exists_forall_finrank_inf_map_pow_add_finrank_inf_le
    (mulEquiv (k := 𝕜) u hu) (ST R f) (Bsub u) (ST R f⁻¹) (Bsub' u) hPB hP'B' hP hB hP' hB'
    hfin hgen hgen' htor htor'
  haveI : FiniteDimensional 𝕜 ↥(Bsub (k := 𝕜) u ⊓ Bsub' u) := by
    haveI := hfin 0
    refine Submodule.finiteDimensional_of_le (S₂ := Bsub (k := 𝕜) u ⊓ (Bsub' u).map
      ((mulEquiv (k := 𝕜) u hu : (∀ i, Fb i) →ₗ[𝕜] (∀ i, Fb i)) ^ 0)) fun x hx =>
      Submodule.mem_inf.mpr ⟨hx.1, Submodule.mem_map.mpr ⟨x, hx.2, ?_⟩⟩
    rw [pow_zero, Module.End.one_apply]
  have hcard := card_le_finrank_inf (k := 𝕜) u
  refine ⟨M₀, fun M hM => ⟨?_, ?_⟩⟩
  · haveI := hfin M
    exact Submodule.finiteDimensional_of_le (inf_le_inf hPB (Submodule.map_mono hP'B'))
  · have h1 := hM₀ M hM
    rw [hrank M] at h1
    omega

end Assembly

theorem exists_forall_finrank_residueSpan_inf_add_card_le
    {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htrL : Transcendental L f)
    (hfd : FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (Db : ∀ i, Divisor (IsLocalRing.ResidueField A) (Fb i))
    (hDb : ∀ i, ∀ w : Place (IsLocalRing.ResidueField A) (Fb i),
      Db i w = max 0 (-w.ord ((R i).residue ⟨f, hf i⟩))) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      FiniteDimensional (IsLocalRing.ResidueField A)
        ↥(Submodule.span (IsLocalRing.ResidueField A)
            {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
              (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → u ∈ V) ∧
              ∀ i, (R i).residue ⟨u, hu i⟩ = h i} ⊓
          Submodule.span (IsLocalRing.ResidueField A)
            {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
              (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f⁻¹ ∈ V →
                u * (f ^ M)⁻¹ ∈ V) ∧
              ∀ i, (R i).residue ⟨u, hu i⟩ = h i}) ∧
      Module.finrank (IsLocalRing.ResidueField A)
        ↥(Submodule.span (IsLocalRing.ResidueField A)
            {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
              (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → u ∈ V) ∧
              ∀ i, (R i).residue ⟨u, hu i⟩ = h i} ⊓
          Submodule.span (IsLocalRing.ResidueField A)
            {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
              (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f⁻¹ ∈ V →
                u * (f ^ M)⁻¹ ∈ V) ∧
              ∀ i, (R i).residue ⟨u, hu i⟩ = h i}) + Fintype.card ι ≤
      (∑ i, ell (M • Db i)) +
      Module.finrank (IsLocalRing.ResidueField A)
        ↥(Submodule.span (IsLocalRing.ResidueField A)
            {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
              (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → u ∈ V) ∧
              ∀ i, (R i).residue ⟨u, hu i⟩ = h i} ⊓
          Submodule.span (IsLocalRing.ResidueField A)
            {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
              (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f⁻¹ ∈ V → u ∈ V) ∧
              ∀ i, (R i).residue ⟨u, hu i⟩ = h i}) := by
  have hu : ∀ i, rv R f hf i ≠ 0 := fun i =>
    ne_zero_of_transcendental (htr i)
  have hf0 : f ≠ 0 := ne_zero_of_transcendental htrL
  have hf' : ∀ i, f⁻¹ ∈ (R i).integers := inv_mem_integers hu
  obtain ⟨M₀, hM₀⟩ := core R hR f hf hfd htr heq Db hDb (rv R f hf)
    (fun _ => rfl) hu
  refine ⟨M₀, fun M hM => ?_⟩
  rw [span_setM_eq f hf hf' hf0 hu M]
  exact hM₀ M hM

end AlgebraicCurve.RegularProlongation
