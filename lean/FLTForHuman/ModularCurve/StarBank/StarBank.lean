/-
The star bank: `j(𝔮ₚ)` is not in the adjoin of `j(𝔮)`.

`StarBank.starBank` is the `ℓ`-adic bank's closure statement: for `p ≠ ℓ`, the `q`-expansion
`jqNModC K p` of the `p`-th level-one `q`-expansion does not lie in the intermediate field generated
by `jqModC K` over `K` — the `q`-expansion form of the star-bank's separation of the two slots from
`E₄³/Δ`'s Hasse derivatives.

The engine is entirely in the port: `StarBank/Hasse.lean`'s `eisInt_series`, `eisInt_not_dvd_num`
and `starK`, `StarBank/Norm.lean`'s `deltaNorm` and `closure`, `ModularPolynomialStarBank.lean`'s
`press` and `delta_pow_ne`, AF106E's `hassePolyDescent`, and
`Degree/PrimeNonAdjoin.lean`'s `jqNModC_prime_not_mem_adjoin_of_forall_aeval_ne`. This module sits
above all of them — the third module of the `StarBank/` directory and its headline.

## The rows

* `ModularCurve.StarBank.starBank` — 453 pin `S_` lines.

## Port notes (order AF107D)

* **Transcription.** The pin's `S_` file is 15 declarations — 12 public, 3 private — in 453 lines, and
  it is transcribed in full at the pin's names.  Its `W1` prelude namespace is kept (`ModularCurve.W1`,
  the namespace `StarBank/Hasse.lean` and `ModularPolynomialHasseDescent.lean` already use), the
  generated `P2MW.S_…` label is dropped, and the pin's public `solution` (the wrapper alias of the
  private `starBank`) is this module's headline `ModularCurve.StarBank.starBank`, i.e. the wrapper's
  published name.  The `S_` file's own `ModularCurve.StarBank` block is the subject namespace, so it
  stays.  `P2M/Util.lean`'s macros, the pin's `attribute [-simp]` wall and its `#print axioms solution`
  are not transcribed.
* **Substitutions (2).** The substitution pass proposed `coeff_single_mul_ofPowerSeries_nonneg'` →
  `ModularCurve.W1.coeff_single_mul_ofPowerSeries_nonneg`
  (`ModularPolynomialHasseDescent.lean`); read against the pin's body, the port's copy is the same lemma
  at a *wider* hypothesis (`[Semiring K]` where the pin has `[Field K]`), so it is imported, not
  re-proved.  A second one the pass did not name: the pin's `algebraMap_laurent_eq_single'` is the
  port's `ModularCurve.W1.algebraMap_laurent_eq_single`
  (`ModularPolynomialHasseDescent.lean`) verbatim up to its binder name, and is likewise imported.  The
  other 13 rows are transcribed.
* **Deprecations rewritten, not silenced.** `haveI : NeZero ((p : K))` in `exists_primitiveRoot_units`
  and `haveI : CharP (AlgebraicClosure K) ℓ` in the headline are `Prop`-goal instances and are written
  `have` (the pin's precedent, per the set preamble); the pin's `if_pos` / `if_neg` steps in
  `endgame_read` and `hasse_input` are `ite_eq_left` / `ite_eq_right`.  The pin's
  `ModularForm.IsGLPos.coe_smul` does not exist in this mathlib — `hasse_input` uses `FunLike.coe_smul`
  for it, the same rename `ModularForms/LevelOneSlash.lean` records.
* **Visibility.** `check_port --force` on this module reads **10 ok / 0 mismatch / 0 missing / 0 own /
  0 kw**: the 9 public helpers and the headline.  With the pin's `private` dropped from its two private
  helpers (`laurentMapRingHom`, `starBank_core`) the same checker reads **12 ok / 0 / 0 / 0 / 0** — both
  are pin-faithful statements, and neither is promoted here because the pin keeps them private.
* **Axioms.** `#print axioms` on all 10 public declarations is a subset of
  `[propext, Classical.choice, Quot.sound]` — `natCast_prime_ne_zero` is the one at
  `[propext, Quot.sound]` — with no `sorryAx`.
* **Dedup / move_dead.** `dedup.py --within --module '*StarBank/StarBank*'`: 12 declarations,
  **0 duplicate clusters**, 0 removable lines.  `move_dead.py --dry-run`: **0 declarations, 0 lines**.
* **Heartbeat probe pair** (FR-0225 — measured, never installed).  Neither the pin's `S_` file nor this
  module carries `set_option maxHeartbeats` or `synthInstance.maxHeartbeats`.  Readings at the project's
  low cap: the edit loop is **silent at `-DmaxHeartbeats=200000`**, at `40000`, at `20000` and at `50000`, and
  it first fails at `-DmaxHeartbeats=10000` (`endgame_read`, `whnf`): the module's floor is in
  (10 000, 20 000], i.e. an order of magnitude under the cap, and nothing here is near it.

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_StarBank_starBank.lean>

spec-pin: Theorems/Thm_ModularCurve_StarBank_starBank.lean
spec-pin: P2M/Sol/S_ModularCurve_StarBank_starBank.lean
-/

import FLTForHuman.AutomorphicForm.Adelic.LsXiL2FundamentalDomain
import FLTForHuman.ModularCurve.Degree.PrimeNonAdjoin
import FLTForHuman.ModularCurve.ModularPolynomialHasseDescent
import FLTForHuman.ModularCurve.ModularPolynomialStarBank
import FLTForHuman.ModularCurve.StarBank.Hasse
import FLTForHuman.ModularCurve.StarBank.Norm
import Mathlib.RingTheory.HahnSeries.Basic
import Mathlib.Tactic

open Polynomial HahnSeries

set_option autoImplicit false

noncomputable section

namespace ModularCurve
namespace W1

section Kit

variable {K : Type*} [Field K]

theorem eq_C_leadingCoeff_mul_pow_of_forall_root [IsAlgClosed K] {G : Polynomial K} {β₀ : K}
    (huniq : ∀ β : K, G.IsRoot β → β = β₀) :
    G = Polynomial.C G.leadingCoeff * (Polynomial.X - Polynomial.C β₀) ^ G.natDegree := by
  have hcard : G.roots.card = G.natDegree :=
    Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits G)
  have hall : ∀ b ∈ G.roots, b = β₀ := fun b hb => huniq b (Polynomial.mem_roots'.mp hb).2
  have hrep : G.roots = Multiset.replicate G.natDegree β₀ := by
    have h1 := Multiset.eq_replicate_card.mpr hall
    rwa [hcard] at h1
  have h2 := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  rw [hrep, Multiset.map_replicate, Multiset.prod_replicate] at h2
  exact h2.symm

theorem dSeries_ne_zero :
    (HahnSeries.single (1 : ℤ) 1
        * HahnSeries.ofPowerSeries ℤ K
            (PowerSeries.map (Int.castRingHom K) ModularCurve.etaProd) ^ 24)
      ≠ 0 := by
  intro h0
  rw [show (HahnSeries.ofPowerSeries ℤ K
        (PowerSeries.map (Int.castRingHom K) ModularCurve.etaProd)) ^ 24
      = HahnSeries.ofPowerSeries ℤ K
          ((PowerSeries.map (Int.castRingHom K) ModularCurve.etaProd) ^ 24) from
    (map_pow _ _ _).symm] at h0
  have h3 : PowerSeries.constantCoeff
      (PowerSeries.map (Int.castRingHom K) ModularCurve.etaProd) = 1 := by
    have h4 := PowerSeries.coeff_map (Int.castRingHom K) 0 ModularCurve.etaProd
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, ModularCurve.constantCoeff_etaProd,
      map_one] at h4
    exact h4
  have h1 : (HahnSeries.single (1 : ℤ) (1 : K)
      * HahnSeries.ofPowerSeries ℤ K
          ((PowerSeries.map (Int.castRingHom K) ModularCurve.etaProd) ^ 24)).coeff
        ((1 : ℤ) + ((0 : ℕ) : ℤ)) = 1 := by
    rw [coeff_single_mul_ofPowerSeries_nonneg,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, h3, one_pow]
  rw [h0] at h1
  exact one_ne_zero
    (h1.symm.trans (show ((0 : LaurentSeries K)).coeff ((1 : ℤ) + ((0 : ℕ) : ℤ)) = 0 from rfl))

theorem endgame_read (p : ℕ) [NeZero p] (hp1 : 1 ≤ p) {β₀ γ : K} (hγ : γ ≠ 0)
    (honept : (jqModC K - HahnSeries.C β₀)
        * (HahnSeries.single (1 : ℤ) 1
            * HahnSeries.ofPowerSeries ℤ K
                (PowerSeries.map (Int.castRingHom K) ModularCurve.etaProd) ^ 24)
      = HahnSeries.C γ)
    (hpress : qExpand K p (jqModC K)
      = (jqModC K - HahnSeries.C β₀) ^ p + HahnSeries.C β₀) :
    (HahnSeries.single (1 : ℤ) 1
        * HahnSeries.ofPowerSeries ℤ K
            (PowerSeries.map (Int.castRingHom K) ModularCurve.etaProd) ^ 24) ^ p
      = HahnSeries.C (γ ^ (p - 1))
        * qExpand K p (HahnSeries.single (1 : ℤ) 1
            * HahnSeries.ofPowerSeries ℤ K
                (PowerSeries.map (Int.castRingHom K) ModularCurve.etaProd) ^ 24) := by
  set D : LaurentSeries K := HahnSeries.single (1 : ℤ) 1
    * HahnSeries.ofPowerSeries ℤ K
        (PowerSeries.map (Int.castRingHom K) ModularCurve.etaProd) ^ 24 with hD
  have hD0 : D ≠ 0 := dSeries_ne_zero
  have hCγ0 : (HahnSeries.C γ : LaurentSeries K) ≠ 0 := by
    intro h
    apply hγ
    have h1 := congrArg (fun z : LaurentSeries K => z.coeff 0) h
    rw [show (HahnSeries.C γ : LaurentSeries K) = HahnSeries.single 0 γ from rfl,
      HahnSeries.coeff_single, ite_eq_left rfl] at h1
    exact h1.trans rfl

  have hq := congrArg (qExpand K p) honept
  rw [map_mul, ModularCurve.qExpand_C] at hq
  have hqj : qExpand K p (jqModC K - HahnSeries.C β₀)
      = (jqModC K - HahnSeries.C β₀) ^ p := by
    rw [map_sub, ModularCurve.qExpand_C, hpress, add_sub_cancel_right]
  rw [hqj] at hq

  have hj : jqModC K - HahnSeries.C β₀ = HahnSeries.C γ * D⁻¹ := by
    rw [← honept]
    exact (mul_inv_cancel_right₀ hD0 _).symm
  rw [hj, mul_pow] at hq

  have h6 := congrArg (fun z : LaurentSeries K => z * D ^ p) hq
  rw [show HahnSeries.C γ ^ p * D⁻¹ ^ p * qExpand K p D * D ^ p
      = HahnSeries.C γ ^ p * qExpand K p D * (D⁻¹ * D) ^ p from by ring,
    inv_mul_cancel₀ hD0, one_pow, mul_one] at h6

  have h7 : HahnSeries.C γ * (HahnSeries.C (γ ^ (p - 1)) * qExpand K p D)
      = HahnSeries.C γ * D ^ p := by
    calc HahnSeries.C γ * (HahnSeries.C (γ ^ (p - 1)) * qExpand K p D)
        = HahnSeries.C γ ^ p * qExpand K p D := by
          rw [← mul_assoc, ← map_mul, ← pow_succ', Nat.sub_add_cancel hp1, map_pow]
      _ = HahnSeries.C γ * D ^ p := h6
  exact (mul_left_cancel₀ hCγ0 h7).symm

end Kit

section Descent

variable {K K' : Type*} [Field K] [Field K']

private def laurentMapRingHom (φ : K →+* K') : LaurentSeries K →+* LaurentSeries K' where
  toFun x := x.map φ
  map_one' := by
    ext g
    rw [HahnSeries.map_coeff,
      show (1 : LaurentSeries K) = HahnSeries.single 0 1 from HahnSeries.single_zero_one.symm,
      show (1 : LaurentSeries K') = HahnSeries.single 0 1 from HahnSeries.single_zero_one.symm,
      HahnSeries.coeff_single, HahnSeries.coeff_single]
    split_ifs
    · exact map_one φ
    · exact map_zero φ
  map_mul' x y := HahnSeries.map_mul φ.toNonUnitalRingHom
  map_zero' := by
    ext g
    rw [HahnSeries.map_coeff]
    exact map_zero φ
  map_add' x y := by
    ext g
    rw [HahnSeries.map_coeff, HahnSeries.coeff_add, HahnSeries.coeff_add,
      HahnSeries.map_coeff, HahnSeries.map_coeff]
    exact map_add φ _ _

end Descent

section Transport

variable {K K' : Type*} [Field K] [Field K']

theorem qExpand_map_comm (φ : K →+* K') (N : ℕ) [NeZero N] (f : LaurentSeries K) :
    (ModularCurve.qExpand K N f).map φ = ModularCurve.qExpand K' N (f.map φ) := by
  ext g
  rw [HahnSeries.map_coeff]
  by_cases hg : (N : ℤ) ∣ g
  · obtain ⟨k, hk⟩ := hg
    subst hk
    rw [ModularCurve.qExpand_coeff_mul, ModularCurve.qExpand_coeff_mul, HahnSeries.map_coeff]
  · rw [ModularCurve.qExpand_coeff_of_not_dvd (hk := hg),
      ModularCurve.qExpand_coeff_of_not_dvd (hk := hg), map_zero]

theorem jqNModC_map_comm (φ : K →+* K') (p : ℕ) [NeZero p] :
    (ModularCurve.jqNModC K p).map φ = ModularCurve.jqNModC K' p := by
  rw [ModularCurve.jqNModC, ModularCurve.jqNModC, qExpand_map_comm, ModularCurve.map_jqModC]

theorem aeval_jqModC_map_comm (φ : K →+* K') (R : Polynomial K) :
    (Polynomial.aeval (ModularCurve.jqModC K) R).map φ
      = Polynomial.aeval (ModularCurve.jqModC K') (R.map φ) := by
  have hcomp : (laurentMapRingHom φ).comp (algebraMap K (LaurentSeries K))
      = (algebraMap K' (LaurentSeries K')).comp φ := by
    refine RingHom.ext fun c => ?_
    show (algebraMap K (LaurentSeries K) c).map φ = algebraMap K' (LaurentSeries K') (φ c)
    rw [algebraMap_laurent_eq_single, algebraMap_laurent_eq_single]
    ext g
    rw [HahnSeries.map_coeff, HahnSeries.coeff_single, HahnSeries.coeff_single]
    split_ifs
    · rfl
    · exact map_zero φ
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map,
    show (Polynomial.eval₂ (algebraMap K (LaurentSeries K)) (ModularCurve.jqModC K) R).map φ
      = laurentMapRingHom φ
          (Polynomial.eval₂ (algebraMap K (LaurentSeries K)) (ModularCurve.jqModC K) R) from rfl,
    Polynomial.hom_eval₂, hcomp,
    show laurentMapRingHom φ (ModularCurve.jqModC K)
      = (ModularCurve.jqModC K).map φ from rfl,
    ModularCurve.map_jqModC]

end Transport

section PrimRoot

theorem natCast_prime_ne_zero (K : Type*) [Field K] {ℓ p : ℕ} [Fact ℓ.Prime] [Fact p.Prime]
    [CharP K ℓ] (hpℓ : p ≠ ℓ) : (p : K) ≠ 0 := by
  intro h
  rw [CharP.cast_eq_zero_iff K ℓ] at h
  exact hpℓ ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp h).symm

theorem exists_primitiveRoot_units (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ)
    [Fact p.Prime] (hp : (p : K) ≠ 0) : ∃ ζ : Kˣ, IsPrimitiveRoot ((ζ : Kˣ) : K) p := by
  have : NeZero ((p : K)) := ⟨hp⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K p
  obtain ⟨u, hu⟩ := hz.isUnit (Nat.Prime.ne_zero Fact.out)
  exact ⟨u, hu.symm ▸ hz⟩

end PrimRoot

section HasseDischarge

open scoped MatrixGroups

theorem hasse_input {ℓ : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) :
    ∃ (T : PowerSeries ℤ) (G : Polynomial ℤ),
      (∀ m, 1 ≤ m → (ℓ : ℤ) ∣ T.coeff m) ∧ ¬ (ℓ : ℤ) ∣ PowerSeries.constantCoeff T
      ∧ G.natDegree = ℓ - 1 ∧ G.coeff (ℓ - 1) = PowerSeries.constantCoeff T
      ∧ HahnSeries.ofPowerSeries ℤ ℤ T
          = Polynomial.aeval (ModularCurve.jqModC ℤ) G
            * (HahnSeries.single (1 : ℤ) (1 : ℤ)
                * HahnSeries.ofPowerSeries ℤ ℤ ModularCurve.etaProd ^ 24) ^ (ℓ - 1) := by
  have hk : 3 ≤ ℓ - 1 := by omega
  obtain ⟨T, hTmap, hTconst, hTdvd⟩ := ModularCurve.StarBank.eisInt_series hℓ5 hk
  have hnum0 : ¬ (ℓ : ℤ) ∣ (_root_.bernoulli (ℓ - 1)).num :=
    ModularCurve.StarBank.eisInt_not_dvd_num hℓ5

  have hmapZ : T.map (Int.castRingHom (ZMod ℓ))
      = PowerSeries.C (((_root_.bernoulli (ℓ - 1)).num : ZMod ℓ)) := by
    ext n
    rw [PowerSeries.coeff_map, PowerSeries.coeff_C]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [ite_eq_left rfl, PowerSeries.coeff_zero_eq_constantCoeff_apply, hTconst]
      rfl
    · rw [ite_eq_right (by omega)]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (hTdvd n hn)
  have hmapZ12 : (T ^ 12).map (Int.castRingHom (ZMod ℓ))
      = PowerSeries.C ((((_root_.bernoulli (ℓ - 1)).num : ZMod ℓ)) ^ 12) := by
    rw [map_pow, hmapZ, ← map_pow]
  have hnumZ : (((_root_.bernoulli (ℓ - 1)).num : ZMod ℓ)) ≠ 0 :=
    fun h => hnum0 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)

  have hdvd12 : ∀ m, 1 ≤ m → (ℓ : ℤ) ∣ (T ^ 12).coeff m := by
    intro m hm
    have h1 := congrArg (fun u : PowerSeries (ZMod ℓ) => PowerSeries.coeff m u) hmapZ12
    simp only [PowerSeries.coeff_map, PowerSeries.coeff_C] at h1
    rw [ite_eq_right (by omega : ¬ m = 0)] at h1
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h1

  have hconst12 : PowerSeries.constantCoeff (T ^ 12) = (_root_.bernoulli (ℓ - 1)).num ^ 12 := by
    rw [map_pow, hTconst]
  have hnot12 : ¬ (ℓ : ℤ) ∣ PowerSeries.constantCoeff (T ^ 12) := by
    rw [hconst12, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    exact pow_ne_zero 12 hnumZ

  have hw : ((12 : ℕ) : ℤ) * ((ℓ - 1 : ℕ) : ℤ) = 12 * ((ℓ - 1 : ℕ) : ℤ) := by norm_num
  have hT12 : (T ^ 12).map (Int.castRingHom ℂ)
      = UpperHalfPlane.qExpansion 1
          ⇑(ModularForm.mcast hw
              ((((_root_.bernoulli (ℓ - 1)).num : ℂ) • ModularForm.E hk).pow 12)) := by
    have h1 : UpperHalfPlane.qExpansion 1
        ⇑(ModularForm.mcast hw
            ((((_root_.bernoulli (ℓ - 1)).num : ℂ) • ModularForm.E hk).pow 12))
        = UpperHalfPlane.qExpansion 1
            ⇑((((_root_.bernoulli (ℓ - 1)).num : ℂ) • ModularForm.E hk).pow 12) := rfl
    rw [h1, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
      FunLike.coe_smul,
      ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL, map_pow, hTmap]
  have h0 : PowerSeries.constantCoeff (T ^ 12) ≠ 0 := by
    rw [hconst12]
    intro h
    exact hnum0 ((pow_eq_zero_iff (by norm_num : (12 : ℕ) ≠ 0)).mp h ▸ dvd_zero _)
  obtain ⟨G, hGdeg, hGcoeff, hGid⟩ := ModularCurve.StarBank.hassePolyDescent
    (ModularForm.mcast hw ((((_root_.bernoulli (ℓ - 1)).num : ℂ) • ModularForm.E hk).pow 12))
    hT12 h0
  exact ⟨T ^ 12, G, hdvd12, hnot12, hGdeg, hGcoeff, hGid⟩

end HasseDischarge

end W1

private theorem starBank_core {K : Type*} [Field K] [IsAlgClosed K] {ℓ p : ℕ}
    [Fact ℓ.Prime] [Fact p.Prime] [CharP K ℓ] (hpℓ : p ≠ ℓ)

    (hstarK : ∃ M : ℕ, 1 ≤ M ∧ (M : K) ≠ 0 ∧ ∃ G : Polynomial K, G.natDegree = M
      ∧ Polynomial.aeval (jqModC K) G
          * (HahnSeries.single (1 : ℤ) (1 : K)
              * HahnSeries.ofPowerSeries ℤ K
                  (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^ M = 1)

    (hpress : ∀ (ζ : Kˣ), IsPrimitiveRoot (ζ : K) p → ∀ {R : Polynomial K},
      Polynomial.aeval (jqModC K) R = jqNModC K p →
      R.Monic ∧ R.natDegree = p ∧
        R.map (algebraMap K (LaurentSeries K)) - Polynomial.C (jqNModC K p) =
          ∏ b ∈ Finset.range p,
            (Polynomial.X - Polynomial.C (qTwist (ζ ^ b) (jqModC K))))

    (hnorm : ∀ (ζ : Kˣ), IsPrimitiveRoot (ζ : K) p →
      (∏ b ∈ Finset.range p, qTwist (ζ ^ b)
          (HahnSeries.single (1 : ℤ) (1 : K) *
            HahnSeries.ofPowerSeries ℤ K
              (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24)) *
        qExpand K (p * p) (HahnSeries.single (1 : ℤ) (1 : K) *
            HahnSeries.ofPowerSeries ℤ K
              (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) =
      HahnSeries.C (((∏ b ∈ Finset.range p, ζ ^ b : Kˣ) : K)) *
        qExpand K p (HahnSeries.single (1 : ℤ) (1 : K) *
            HahnSeries.ofPowerSeries ℤ K
              (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^ (p + 1))

    (hclosure : ∀ (ζ : Kˣ) {M : ℕ} {G R : Polynomial K},
      Polynomial.aeval (jqModC K) G *
          (HahnSeries.single (1 : ℤ) (1 : K) *
            HahnSeries.ofPowerSeries ℤ K
              (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^ M = 1 →
      Polynomial.aeval (jqModC K) R = jqNModC K p →
      (R.map (algebraMap K (LaurentSeries K)) - Polynomial.C (jqNModC K p) =
          ∏ b ∈ Finset.range p,
            (Polynomial.X - Polynomial.C (qTwist (ζ ^ b) (jqModC K)))) →
      ((∏ b ∈ Finset.range p, qTwist (ζ ^ b)
          (HahnSeries.single (1 : ℤ) (1 : K) *
            HahnSeries.ofPowerSeries ℤ K
              (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24)) *
        qExpand K (p * p) (HahnSeries.single (1 : ℤ) (1 : K) *
            HahnSeries.ofPowerSeries ℤ K
              (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) =
      HahnSeries.C (((∏ b ∈ Finset.range p, ζ ^ b : Kˣ) : K)) *
        qExpand K p (HahnSeries.single (1 : ℤ) (1 : K) *
            HahnSeries.ofPowerSeries ℤ K
              (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^ (p + 1)) →
      ∃ c : K, c ≠ 0 ∧ G.comp R ∣ Polynomial.C c * G ^ (p + 1))

    (hcount : ∀ (_ : (p : K) ≠ 0) (_ : 2 ≤ p) {R G : Polynomial K} (_ : R.Monic)
      (_ : R.natDegree = p) (_ : 0 < G.natDegree) {c : K} (_ : c ≠ 0)
      (_ : G.comp R ∣ Polynomial.C c * G ^ (p + 1)),
      ∃ β₀ : K, (∀ β : K, G.IsRoot β → β = β₀) ∧
        R = (Polynomial.X - Polynomial.C β₀) ^ p + Polynomial.C β₀)

    (honepoint : ∀ {M : ℕ} (_ : (M : K) ≠ 0) {c : K} (_ : c ≠ 0) {β₀ : K}
      (_ : Polynomial.aeval (jqModC K)
            (Polynomial.C c * (Polynomial.X - Polynomial.C β₀) ^ M)
          * (HahnSeries.single (1 : ℤ) 1
              * HahnSeries.ofPowerSeries ℤ K
                  (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^ M
          = 1),
      ∃ γ : K, γ ≠ 0 ∧
        (jqModC K - HahnSeries.C β₀)
          * (HahnSeries.single (1 : ℤ) 1
              * HahnSeries.ofPowerSeries ℤ K
                  (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24)
          = HahnSeries.C γ)

    (hdelta : ∀ (γ : K),
      (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K
            (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^ p ≠
        HahnSeries.C γ * qExpand K p (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K
            (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24))

    {R : Polynomial K} (hRmem : Polynomial.aeval (jqModC K) R = jqNModC K p) : False := by
  have hp0 : (p : K) ≠ 0 := ModularCurve.W1.natCast_prime_ne_zero K hpℓ
  obtain ⟨ζ, hζ⟩ := ModularCurve.W1.exists_primitiveRoot_units K p hp0
  obtain ⟨hRmon, hRdeg, hRprod⟩ := hpress ζ hζ hRmem
  obtain ⟨M, hM1, hMK, G, hGdeg, hGstar⟩ := hstarK
  obtain ⟨c, hc, hdvd⟩ := hclosure ζ hGstar hRmem hRprod (hnorm ζ hζ)
  have hGpos : 0 < G.natDegree := by rw [hGdeg]; omega
  obtain ⟨β₀, huniq, hRform⟩ :=
    hcount hp0 (Nat.Prime.two_le Fact.out) hRmon hRdeg hGpos hc hdvd
  have hG0 : G ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_mul] at hGstar
    exact zero_ne_one hGstar
  have hlc : G.leadingCoeff ≠ 0 := fun h => hG0 (Polynomial.leadingCoeff_eq_zero.mp h)
  have hGfact := ModularCurve.W1.eq_C_leadingCoeff_mul_pow_of_forall_root huniq
  rw [hGfact, hGdeg] at hGstar
  obtain ⟨γ, hγ, honep⟩ := honepoint hMK hlc hGstar
  have hpressEq : qExpand K p (jqModC K)
      = (jqModC K - HahnSeries.C β₀) ^ p + HahnSeries.C β₀ := by
    have h1 : Polynomial.aeval (jqModC K) R
        = (jqModC K - HahnSeries.C β₀) ^ p + HahnSeries.C β₀ := by
      rw [hRform, map_add, map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
        ModularCurve.W1.algebraMap_laurent_eq_single]
      rfl
    rw [← h1, hRmem, ModularCurve.jqNModC]
  have hDp := ModularCurve.W1.endgame_read p ((Nat.Prime.one_lt (Fact.out : p.Prime)).le)
    hγ honep hpressEq
  exact hdelta (γ ^ (p - 1)) hDp

namespace StarBank

theorem starBank {K : Type*} [Field K] {ℓ : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] {p : ℕ} [Fact p.Prime] (hpℓ : p ≠ ℓ) :
    jqNModC K p ∉ IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)) := by
  apply ModularCurve.jqNModC_prime_not_mem_adjoin_of_forall_aeval_ne
  intro R0 hR0
  have : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective ℓ
  have hR1 : Polynomial.aeval (jqModC (AlgebraicClosure K))
      (R0.map (algebraMap K (AlgebraicClosure K)))
      = jqNModC (AlgebraicClosure K) p := by
    rw [← ModularCurve.W1.aeval_jqModC_map_comm, hR0, ModularCurve.W1.jqNModC_map_comm]
  exact starBank_core hpℓ
    (ModularCurve.StarBank.starK (AlgebraicClosure K) ModularCurve.W1.hasse_input)
    (ModularCurve.StarBank.press p) (ModularCurve.StarBank.deltaNorm p)
    (ModularCurve.StarBank.closure p) ModularCurve.StarBank.count
    ModularCurve.StarBank.onePoint
    (ModularCurve.StarBank.delta_pow_ne (AlgebraicClosure K) hpℓ) hR1

end StarBank

end ModularCurve

end
