/-
  The index of `Γ₀(N)` in `SL₂(ℤ)`: the coset bijection with the projective line
  `ℙ¹(ℤ/N)` and the count `[SL₂(ℤ) : Γ₀(N)] = ψ(N)`.

  This is SET-3 (l3) of `topics/PORTING-Level.md`. The mathematics is base/018 §5:
  the coset space `Γ₀(N)\SL₂(ℤ)` is the set of lines in `(ℤ/N)²`, the bijection is
  by the first column, and the count is the Dedekind psi function. The lifting
  statement `sl2_surj` (every `SL₂(ℤ/N)` element lifts to `SL₂(ℤ)`) is base/018
  §4.3.

  FLT provenance, pinned `aa2d8b3`:
  * `P2M/Sol/S_ModularCurve_Gamma0_index.lean` — the arithmetic/lifting block, the
    Borel-quotient bijection, (`CongruenceSubgroup.`)`Gamma0_eq_comap_borel` and
    the index computation. The pin keeps those helpers `private`; the port
    promotes `exists_sl2_int_lift` and `sl2_surj` because they are the
    mathematics, and keeps the rest `private`.
  * `P2M/Sol/S_ModularCurve_card_projectiveLine_zmod.lean` — the prime-power and
    Chinese-remainder count `#ℙ¹(ℤ/N) = ψ(N)`.
  * `P2M/Sol/S_ModularCurve_card_primCosetReps_eq_dedekindPsi.lean` — the
    independent count `(primCosetReps N).card = ψ(N)` by `divisorsAntidiagonal`.
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_Gamma0_index.lean

  The three public headlines are the pin's `Theorems/` wrappers verbatim:
  `Gamma0_index`, `card_projectiveLine_zmod`, `card_primCosetReps_eq_dedekindPsi`.
  `dedekindPsi` and its arithmetic lemmas live in `Defs/Jq.lean` and are imported,
  not re-ported. Statements are transcribed verbatim; proofs are adapted only for
  mathlib `v4.34.0` (and the pin's local `maxHeartbeats` bumps are not carried).
-/
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Units
import Mathlib.Tactic
import FLTForHuman.ModularCurve.Defs.ProjectiveLine
import FLTForHuman.ModularCurve.Defs.PrimCosetReps
import FLTForHuman.ModularCurve.Defs.Jq
import FLTForHuman.NumberTheory.DedekindPsiCount

set_option autoImplicit false

-- The pin's `haveI` walls are kept literal (as in `ModularForm.Level.Diamond`).
set_option linter.style.haveILetI false

noncomputable section

open ModularCurve Matrix CongruenceSubgroup Finset
open scoped MatrixGroups

namespace ModularCurve

section ArithmeticLemmas

private lemma natCast_dvd_int {p : ℕ} {z : ℤ} : (p : ℤ) ∣ z ↔ p ∣ z.natAbs :=
  Int.natCast_dvd

private def primeSel (c d : ℤ) : ℕ :=
  ∏ p ∈ c.natAbs.primeFactors, if p ∣ d.natAbs then 1 else p

private lemma dvd_primeSel {c d : ℤ} {p : ℕ} (hc : c ≠ 0) (hp : p.Prime)
    (hpc : (p : ℤ) ∣ c) (hpd : ¬(p : ℤ) ∣ d) : p ∣ primeSel c d := by
  have hmem : p ∈ c.natAbs.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, natCast_dvd_int.mp hpc, Int.natAbs_ne_zero.mpr hc⟩
  have h := Finset.dvd_prod_of_mem (fun q : ℕ => if q ∣ d.natAbs then 1 else q) hmem
  simp only [ite_eq_right (fun hcontra => hpd (natCast_dvd_int.mpr hcontra))] at h
  exact h

private lemma not_dvd_primeSel {c d : ℤ} {p : ℕ} (hp : p.Prime) (hpd : (p : ℤ) ∣ d) :
    ¬p ∣ primeSel c d := by
  intro hdvd
  obtain ⟨q, hq, hpq⟩ := (Nat.Prime.prime hp).dvd_finsetProd_iff _ |>.mp hdvd
  by_cases hqd : q ∣ d.natAbs
  · rw [ite_eq_left hqd] at hpq
    exact hp.one_lt.ne' (Nat.dvd_one.mp hpq)
  · rw [ite_eq_right hqd] at hpq
    have hq' : q.Prime := (Nat.mem_primeFactors.mp hq).1
    exact hqd (((Nat.prime_dvd_prime_iff_eq hp hq').mp hpq) ▸ natCast_dvd_int.mp hpd)

private theorem exists_coprime_lift (N : ℕ) [NeZero N] {c₀ d₀ : ℤ}
    (H : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ c₀ → (p : ℤ) ∣ d₀ → ¬(p : ℤ) ∣ (N : ℤ)) :
    ∃ γ δ : ℤ, Int.gcd γ δ = 1 ∧
      (γ : ZMod N) = (c₀ : ZMod N) ∧ (δ : ZMod N) = (d₀ : ZMod N) := by
  set γ : ℤ := if c₀ = 0 then (N : ℤ) else c₀ with hγ_def
  have hγ0 : γ ≠ 0 := by
    rw [hγ_def]; split
    · exact_mod_cast NeZero.ne N
    · assumption
  have hγc : (γ : ZMod N) = (c₀ : ZMod N) := by
    rw [hγ_def]; split
    · next h => simp [h]
    · rfl
  have Hγ : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ γ → (p : ℤ) ∣ d₀ → ¬(p : ℤ) ∣ (N : ℤ) := by
    intro p pp hpγ hpd
    refine H p pp ?_ hpd
    rw [hγ_def] at hpγ
    by_cases h : c₀ = 0
    · simp [h]
    · rwa [ite_eq_right h] at hpγ
  refine ⟨γ, d₀ + (primeSel γ d₀ : ℤ) * (N : ℤ), ?_, hγc, ?_⟩
  · by_contra hne
    obtain ⟨p, pp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    have h1 : (p : ℤ) ∣ γ :=
      natCast_dvd_int.mpr (hpdvd.trans (Nat.gcd_dvd_left _ _))
    have h2 : (p : ℤ) ∣ d₀ + (primeSel γ d₀ : ℤ) * (N : ℤ) :=
      natCast_dvd_int.mpr (hpdvd.trans (Nat.gcd_dvd_right _ _))
    by_cases hpd : (p : ℤ) ∣ d₀
    · have h3 : (p : ℤ) ∣ (primeSel γ d₀ : ℤ) * (N : ℤ) := by
        have := h2.sub hpd; rwa [add_sub_cancel_left] at this
      have h3' : p ∣ primeSel γ d₀ * N := by
        have : (p : ℤ) ∣ ((primeSel γ d₀ * N : ℕ) : ℤ) := by push_cast; exact h3
        exact_mod_cast this
      rcases (pp.prime.dvd_mul.mp h3') with h4 | h4
      · exact not_dvd_primeSel pp hpd h4
      · exact Hγ p pp h1 hpd (by exact_mod_cast h4)
    · have h3 : (p : ℤ) ∣ (primeSel γ d₀ : ℤ) :=
        natCast_dvd_int.mpr (dvd_primeSel hγ0 pp h1 hpd)
      refine hpd ?_
      have := h2.sub (h3.mul_right (N : ℤ)); rwa [add_sub_cancel_right] at this
  · push_cast; simp

theorem exists_sl2_int_lift {N : ℕ} [NeZero N] {a b c d : ZMod N}
    (h : a * d - b * c = 1) :
    ∃ α β γ δ : ℤ, α * δ - β * γ = 1 ∧
      (α : ZMod N) = a ∧ (β : ZMod N) = b ∧ (γ : ZMod N) = c ∧ (δ : ZMod N) = d := by
  set a₀ : ℤ := ZMod.cast a with ha₀
  set b₀ : ℤ := ZMod.cast b with hb₀
  set c₀ : ℤ := ZMod.cast c with hc₀
  set d₀ : ℤ := ZMod.cast d with hd₀
  have hcasta : ((a₀ : ℤ) : ZMod N) = a := ZMod.intCast_zmod_cast a
  have hcastb : ((b₀ : ℤ) : ZMod N) = b := ZMod.intCast_zmod_cast b
  have hcastc : ((c₀ : ℤ) : ZMod N) = c := ZMod.intCast_zmod_cast c
  have hcastd : ((d₀ : ℤ) : ZMod N) = d := ZMod.intCast_zmod_cast d
  have hdvd : (N : ℤ) ∣ a₀ * d₀ - b₀ * c₀ - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hcasta, hcastb, hcastc, hcastd]
    rw [sub_eq_zero]; exact h
  have H : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ c₀ → (p : ℤ) ∣ d₀ → ¬(p : ℤ) ∣ (N : ℤ) := by
    intro p pp hpc hpd hpN
    have hone : (p : ℤ) ∣ 1 := by
      have h1 : (p : ℤ) ∣ a₀ * d₀ - b₀ * c₀ - 1 := hpN.trans hdvd
      have h2 : (p : ℤ) ∣ a₀ * d₀ := hpd.mul_left a₀
      have h3 : (p : ℤ) ∣ b₀ * c₀ := hpc.mul_left b₀
      have key : (1 : ℤ) = a₀ * d₀ - b₀ * c₀ - (a₀ * d₀ - b₀ * c₀ - 1) := by ring
      rw [key]; exact (h2.sub h3).sub h1
    exact pp.one_lt.ne' (Nat.dvd_one.mp (by exact_mod_cast hone))
  obtain ⟨γ, δ, hγδ, hγ, hδ⟩ := exists_coprime_lift N H
  rw [hcastc] at hγ; rw [hcastd] at hδ
  set α₀ : ℤ := Int.gcdB γ δ with hα₀
  set β₀ : ℤ := -Int.gcdA γ δ with hβ₀
  have hdet₀ : α₀ * δ - β₀ * γ = 1 := by
    have hbez := Int.gcd_eq_gcd_ab γ δ
    rw [hγδ] at hbez; push_cast at hbez
    rw [hα₀, hβ₀]; linear_combination -hbez
  have hdet₀' : (α₀ : ZMod N) * d - (β₀ : ZMod N) * c = 1 := by
    have := congrArg (fun z : ℤ => (z : ZMod N)) hdet₀
    push_cast at this; rwa [hγ, hδ] at this
  set lam : ZMod N := b * (α₀ : ZMod N) - a * (β₀ : ZMod N) with hlam
  set l : ℤ := ZMod.cast lam with hl
  have hcastl : ((l : ℤ) : ZMod N) = lam := ZMod.intCast_zmod_cast lam
  refine ⟨α₀ + l * γ, β₀ + l * δ, γ, δ, ?_, ?_, ?_, hγ, hδ⟩
  · linear_combination hdet₀
  · push_cast; rw [hcastl, hγ, hlam]
    linear_combination (-(α₀ : ZMod N)) * h + a * hdet₀'
  · push_cast; rw [hcastl, hδ, hlam]
    linear_combination (-(β₀ : ZMod N)) * h + b * hdet₀'

private theorem sl2_surj (N : ℕ) [NeZero N] :
    Function.Surjective
      (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod N))) := by
  intro M
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    have hM := M.prop; rwa [Matrix.det_fin_two] at hM
  obtain ⟨α, β, γ, δ, h1, ha, hb, hc, hd⟩ := exists_sl2_int_lift hdet
  refine ⟨⟨!![α, β; γ, δ], by rw [Matrix.det_fin_two_of]; exact h1⟩, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simpa [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
      using ‹_›

end ArithmeticLemmas

section QuotientBorel

variable {R : Type*} [CommRing R]

private theorem isUnimodularRow_firstCol (A : SpecialLinearGroup (Fin 2) R) :
    IsUnimodularRow (A.1 0 0) (A.1 1 0) := by
  refine ⟨A.1 1 1, -A.1 0 1, ?_⟩
  have hdet : A.1 0 0 * A.1 1 1 - A.1 0 1 * A.1 1 0 = 1 := by
    have h := A.2; rwa [Matrix.det_fin_two] at h
  linear_combination hdet

private def firstColumnClass (A : SpecialLinearGroup (Fin 2) R) : ProjectiveLine R :=
  ⟦⟨(A.1 0 0, A.1 1 0), isUnimodularRow_firstCol A⟩⟧

private theorem firstColumnClass_eq_iff (A B : SpecialLinearGroup (Fin 2) R) :
    firstColumnClass A = firstColumnClass B ↔ A⁻¹ * B ∈ borel R := by
  constructor
  · intro hAB
    obtain ⟨u, h1, h2⟩ := Quotient.exact hAB
    have h1' : (u : R) * A.1 0 0 = B.1 0 0 := h1
    have h2' : (u : R) * A.1 1 0 = B.1 1 0 := h2
    show (A⁻¹ * B).1 1 0 = 0
    rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.SL2_inv_expl A,
      (Matrix.two_mul_expl _ B.1).2.2.1]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [← h1', ← h2']; ring
  · intro hAB
    have hB : B = A * (A⁻¹ * B) := (mul_inv_cancel_left A B).symm
    have hC10 : (A⁻¹ * B).1 1 0 = 0 := hAB
    have hCdet : (A⁻¹ * B).1 0 0 * (A⁻¹ * B).1 1 1 = 1 := by
      have h := (A⁻¹ * B).2; rw [Matrix.det_fin_two, hC10] at h; linear_combination h
    have hB00 : B.1 0 0 = A.1 0 0 * (A⁻¹ * B).1 0 0 + A.1 0 1 * (A⁻¹ * B).1 1 0 := by
      conv_lhs => rw [hB, SpecialLinearGroup.coe_mul]
      exact (Matrix.two_mul_expl A.1 (A⁻¹ * B).1).1
    have hB10 : B.1 1 0 = A.1 1 0 * (A⁻¹ * B).1 0 0 + A.1 1 1 * (A⁻¹ * B).1 1 0 := by
      conv_lhs => rw [hB, SpecialLinearGroup.coe_mul]
      exact (Matrix.two_mul_expl A.1 (A⁻¹ * B).1).2.2.1
    refine Quotient.sound ⟨⟨(A⁻¹ * B).1 0 0, (A⁻¹ * B).1 1 1, hCdet,
      (mul_comm _ _).trans hCdet⟩, ?_, ?_⟩
    · show (A⁻¹ * B).1 0 0 * A.1 0 0 = B.1 0 0; rw [hB00, hC10]; ring
    · show (A⁻¹ * B).1 0 0 * A.1 1 0 = B.1 1 0; rw [hB10, hC10]; ring

private theorem card_quotient_borel (R : Type*) [CommRing R] :
    Nat.card (SpecialLinearGroup (Fin 2) R ⧸ borel R) = Nat.card (ProjectiveLine R) := by
  have hwd : ∀ A B : SpecialLinearGroup (Fin 2) R, QuotientGroup.leftRel (borel R) A B →
      firstColumnClass A = firstColumnClass B := by
    intro A B hAB
    rw [QuotientGroup.leftRel_apply] at hAB
    exact (firstColumnClass_eq_iff A B).mpr hAB
  refine Nat.card_eq_of_bijective (fun q => Quotient.liftOn' q firstColumnClass hwd) ⟨?_, ?_⟩
  · intro q q'
    refine Quotient.inductionOn₂' q q' ?_
    intro A B hAB
    have hAB' : firstColumnClass A = firstColumnClass B := hAB
    exact (QuotientGroup.eq).mpr ((firstColumnClass_eq_iff A B).mp hAB')
  · intro q
    obtain ⟨v, rfl⟩ := Quotient.exists_rep q
    obtain ⟨x, y, hxy⟩ := v.2
    refine ⟨QuotientGroup.mk ⟨!![v.1.1, -y; v.1.2, x], by
      rw [Matrix.det_fin_two_of]; linear_combination hxy⟩, ?_⟩
    show firstColumnClass _ = ⟦v⟧
    refine Quotient.sound ⟨1, ?_, ?_⟩
    · show (1 : R) * !![v.1.1, -y; v.1.2, x] 0 0 = v.1.1; simp
    · show (1 : R) * !![v.1.1, -y; v.1.2, x] 1 0 = v.1.2; simp

end QuotientBorel

private theorem Gamma0_eq_comap_borel (N : ℕ) :
    Gamma0 N = (borel (ZMod N)).comap
      (SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod N))) := by
  ext A
  rw [Gamma0_mem, Subgroup.mem_comap, mem_borel_iff]
  constructor
  · intro hA
    show (Int.castRingHom (ZMod N)).mapMatrix A.1 1 0 = 0; simpa using hA
  · intro hA
    have hA' : (Int.castRingHom (ZMod N)).mapMatrix A.1 1 0 = 0 := hA; simpa using hA'

section PrimePower

private theorem isUnit_zmod_prime_pow_iff {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) (z : ZMod (p ^ k)) :
    IsUnit z ↔ ZMod.castHom (dvd_pow_self p hk) (ZMod p) z ≠ 0 := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.pos.ne'⟩
  haveI : Fact p.Prime := ⟨hp⟩
  constructor
  · intro h hzero
    exact (h.map (ZMod.castHom (dvd_pow_self p hk) (ZMod p))).ne_zero hzero
  · intro h
    by_contra hz
    apply h

    have hval : ¬z.val.Coprime (p ^ k) := fun hcop =>
      hz (by rw [← ZMod.natCast_zmod_val z]; exact (ZMod.isUnit_iff_coprime _ _).mpr hcop)
    have hdvd : p ∣ z.val := by
      by_contra hndvd
      exact hval (((hp.coprime_iff_not_dvd).mpr hndvd).symm.pow_right k)
    calc ZMod.castHom (dvd_pow_self p hk) (ZMod p) z
        = ZMod.castHom (dvd_pow_self p hk) (ZMod p) ((z.val : ℕ) : ZMod (p ^ k)) := by
          rw [ZMod.natCast_zmod_val]
      _ = ((z.val : ℕ) : ZMod p) := map_natCast _ _
      _ = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd

namespace IsUnimodularRow

private theorem isUnit_or_isUnit {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0)
    {a c : ZMod (p ^ k)} (h : IsUnimodularRow a c) : IsUnit a ∨ IsUnit c := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hcon
  rw [not_or] at hcon
  have ha : ZMod.castHom (dvd_pow_self p hk) (ZMod p) a = 0 := by
    by_contra hne
    exact hcon.1 ((isUnit_zmod_prime_pow_iff hp hk a).mpr hne)
  have hc : ZMod.castHom (dvd_pow_self p hk) (ZMod p) c = 0 := by
    by_contra hne
    exact hcon.2 ((isUnit_zmod_prime_pow_iff hp hk c).mpr hne)
  obtain ⟨x, y, hxy⟩ := h
  apply_fun ZMod.castHom (dvd_pow_self p hk) (ZMod p) at hxy
  rw [map_add, map_mul, map_mul, map_one, ha, hc, mul_zero, mul_zero, add_zero] at hxy
  exact zero_ne_one hxy

end IsUnimodularRow

private noncomputable def isUnitSubtypeEquivUnits (M : Type*) [Monoid M] :
    { z : M // IsUnit z } ≃ Mˣ where
  toFun z := z.2.unit
  invFun u := ⟨u, u.isUnit⟩
  left_inv z := Subtype.ext z.2.unit_spec
  right_inv u := Units.ext u.isUnit.unit_spec

private theorem card_not_isUnit_zmod_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    Nat.card { z : ZMod (p ^ k) // ¬IsUnit z } = p ^ (k - 1) := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.pos.ne'⟩
  classical

  have hsplit : Nat.card { z : ZMod (p ^ k) // IsUnit z } +
      Nat.card { z : ZMod (p ^ k) // ¬IsUnit z } = p ^ k := by
    rw [← Nat.card_sum, Nat.card_congr (Equiv.sumCompl (IsUnit ·)),
      Nat.card_eq_fintype_card, ZMod.card]

  have hunits : Nat.card { z : ZMod (p ^ k) // IsUnit z } = (p ^ k).totient := by
    rw [Nat.card_congr (isUnitSubtypeEquivUnits (ZMod (p ^ k))), Nat.card_eq_fintype_card,
      ZMod.card_units_eq_totient]

  have htot : (p ^ k).totient + p ^ (k - 1) = p ^ k := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hp1 : p - 1 + 1 = p := Nat.succ_pred_eq_of_pos hp.pos
    calc (p ^ (j + 1)).totient + p ^ (j + 1 - 1)
        = p ^ j * (p - 1) + p ^ j := by rw [Nat.totient_prime_pow_succ hp, Nat.add_sub_cancel]
      _ = p ^ j * (p - 1 + 1) := by ring
      _ = p ^ j * p := by rw [hp1]
      _ = p ^ (j + 1) := (pow_succ p j).symm
  omega

private theorem card_projectiveLine_prime_pow (p k : ℕ) (hp : p.Prime) (hk : k ≠ 0) :
    Nat.card (ProjectiveLine (ZMod (p ^ k))) = p ^ k + p ^ (k - 1) := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.pos.ne'⟩

  let f : ZMod (p ^ k) ⊕ { z : ZMod (p ^ k) // ¬IsUnit z } → ProjectiveLine (ZMod (p ^ k)) :=
    fun s => Sum.rec (fun t => ⟦⟨(1, t), isUnimodularRow_one_left t⟩⟧)
      (fun m => ⟦⟨(m.1, 1), isUnimodularRow_one_right m.1⟩⟧) s
  have hbij : Function.Bijective f := by
    constructor
    · rintro (t | m) (t' | m') hff
      ·
        obtain ⟨u, h1, h2⟩ := Quotient.exact hff
        have h1' : (u : ZMod (p ^ k)) * 1 = 1 := h1
        have h2' : (u : ZMod (p ^ k)) * t = t' := h2
        rw [mul_one] at h1'
        rw [h1', one_mul] at h2'
        exact congrArg Sum.inl h2'
      ·
        obtain ⟨u, h1, _⟩ := Quotient.exact hff
        have h1' : (u : ZMod (p ^ k)) * 1 = m'.1 := h1
        exact absurd (h1' ▸ (u.isUnit.mul isUnit_one)) m'.2
      ·
        obtain ⟨u, h1, _⟩ := Quotient.exact hff
        have h1' : (u : ZMod (p ^ k)) * m.1 = 1 := h1
        exact absurd ⟨⟨m.1, u, (mul_comm m.1 u).trans h1', h1'⟩, rfl⟩ m.2
      ·
        obtain ⟨u, h1, h2⟩ := Quotient.exact hff
        have h1' : (u : ZMod (p ^ k)) * m.1 = m'.1 := h1
        have h2' : (u : ZMod (p ^ k)) * 1 = 1 := h2
        rw [mul_one] at h2'
        rw [h2', one_mul] at h1'
        exact congrArg Sum.inr (Subtype.ext h1')
    · intro q
      obtain ⟨v, rfl⟩ := Quotient.exists_rep q
      by_cases ha : IsUnit v.1.1
      ·
        refine ⟨Sum.inl ((ha.unit⁻¹ : (ZMod (p ^ k))ˣ) * v.1.2), Quotient.sound ⟨ha.unit, ?_, ?_⟩⟩
        · show (ha.unit : ZMod (p ^ k)) * 1 = v.1.1
          rw [mul_one, ha.unit_spec]
        · show (ha.unit : ZMod (p ^ k)) * ((ha.unit⁻¹ : (ZMod (p ^ k))ˣ) * v.1.2) = v.1.2
          rw [Units.mul_inv_cancel_left]
      ·
        have hc : IsUnit v.1.2 := (v.2.isUnit_or_isUnit hp hk).resolve_left ha
        have hm : ¬IsUnit ((hc.unit⁻¹ : (ZMod (p ^ k))ˣ) * v.1.1) := fun hcon => by
          have : IsUnit ((hc.unit : ZMod (p ^ k)) * ((hc.unit⁻¹ : (ZMod (p ^ k))ˣ) * v.1.1)) :=
            hc.unit.isUnit.mul hcon
          rw [Units.mul_inv_cancel_left] at this
          exact ha this
        refine ⟨Sum.inr ⟨(hc.unit⁻¹ : (ZMod (p ^ k))ˣ) * v.1.1, hm⟩,
          Quotient.sound ⟨hc.unit, ?_, ?_⟩⟩
        · show (hc.unit : ZMod (p ^ k)) * ((hc.unit⁻¹ : (ZMod (p ^ k))ˣ) * v.1.1) = v.1.1
          rw [Units.mul_inv_cancel_left]
        · show (hc.unit : ZMod (p ^ k)) * 1 = v.1.2
          rw [mul_one, hc.unit_spec]
  rw [← Nat.card_eq_of_bijective f hbij, Nat.card_sum, Nat.card_eq_fintype_card, ZMod.card,
    card_not_isUnit_zmod_prime_pow hp hk]

end PrimePower

section CRT

private def crtFst (M N : ℕ) (h : M.Coprime N) : ZMod (M * N) →+* ZMod M :=
  (RingHom.fst (ZMod M) (ZMod N)).comp (ZMod.chineseRemainder h).toRingHom

private def crtSnd (M N : ℕ) (h : M.Coprime N) : ZMod (M * N) →+* ZMod N :=
  (RingHom.snd (ZMod M) (ZMod N)).comp (ZMod.chineseRemainder h).toRingHom

private theorem crtFst_apply (M N : ℕ) (h : M.Coprime N) (z : ZMod (M * N)) :
    crtFst M N h z = (ZMod.chineseRemainder h z).1 :=
  rfl

private theorem crtSnd_apply (M N : ℕ) (h : M.Coprime N) (z : ZMod (M * N)) :
    crtSnd M N h z = (ZMod.chineseRemainder h z).2 :=
  rfl

private theorem card_projectiveLine_mul (M N : ℕ) [NeZero M] [NeZero N] (h : M.Coprime N) :
    Nat.card (ProjectiveLine (ZMod (M * N))) =
      Nat.card (ProjectiveLine (ZMod M)) * Nat.card (ProjectiveLine (ZMod N)) := by
  haveI : NeZero (M * N) := ⟨mul_ne_zero (NeZero.ne M) (NeZero.ne N)⟩
  set e := ZMod.chineseRemainder h with he

  let F : ProjectiveLine (ZMod (M * N)) → ProjectiveLine (ZMod M) × ProjectiveLine (ZMod N) :=
    fun q => (ProjectiveLine.map (crtFst M N h) q, ProjectiveLine.map (crtSnd M N h) q)
  have hbij : Function.Bijective F := by
    constructor
    ·
      intro q q'
      refine Quotient.inductionOn₂ q q' ?_
      intro v w hvw
      obtain ⟨hM, hN⟩ := Prod.mk.injEq .. ▸ hvw
      obtain ⟨u₁, h1M, h2M⟩ := Quotient.exact hM
      obtain ⟨u₂, h1N, h2N⟩ := Quotient.exact hN
      have h1M' : (u₁ : ZMod M) * crtFst M N h v.1.1 = crtFst M N h w.1.1 := h1M
      have h2M' : (u₁ : ZMod M) * crtFst M N h v.1.2 = crtFst M N h w.1.2 := h2M
      have h1N' : (u₂ : ZMod N) * crtSnd M N h v.1.1 = crtSnd M N h w.1.1 := h1N
      have h2N' : (u₂ : ZMod N) * crtSnd M N h v.1.2 = crtSnd M N h w.1.2 := h2N

      have hUmul : e.symm (↑u₁, ↑u₂) * e.symm (↑u₁⁻¹, ↑u₂⁻¹) = 1 := by
        rw [← map_mul, Prod.mk_mul_mk, Units.mul_inv, Units.mul_inv]
        exact map_one e.symm
      have hUmul' : e.symm (↑u₁⁻¹, ↑u₂⁻¹) * e.symm (↑u₁, ↑u₂) = 1 :=
        (mul_comm _ _).trans hUmul

      have key : ∀ z z' : ZMod (M * N), (u₁ : ZMod M) * (e z).1 = (e z').1 →
          (u₂ : ZMod N) * (e z).2 = (e z').2 →
          e.symm (↑u₁, ↑u₂) * z = z' := by
        intro z z' hz1 hz2
        apply e.injective
        rw [map_mul, RingEquiv.apply_symm_apply]
        calc (((u₁ : ZMod M), (u₂ : ZMod N)) : ZMod M × ZMod N) * e z
            = (↑u₁ * (e z).1, ↑u₂ * (e z).2) := Prod.mk_mul_mk ..
          _ = ((e z').1, (e z').2) := by rw [hz1, hz2]
          _ = e z' := rfl
      exact Quotient.sound ⟨⟨e.symm (↑u₁, ↑u₂), e.symm (↑u₁⁻¹, ↑u₂⁻¹), hUmul, hUmul'⟩,
        key v.1.1 w.1.1 h1M' h1N', key v.1.2 w.1.2 h2M' h2N'⟩
    ·
      rintro ⟨x, y⟩
      obtain ⟨a, rfl⟩ := Quotient.exists_rep x
      obtain ⟨b, rfl⟩ := Quotient.exists_rep y
      obtain ⟨xa, ya, hab⟩ := a.2
      obtain ⟨xb, yb, hbb⟩ := b.2

      have hglue : IsUnimodularRow (e.symm (a.1.1, b.1.1)) (e.symm (a.1.2, b.1.2)) := by
        refine ⟨e.symm (xa, xb), e.symm (ya, yb), ?_⟩
        rw [← map_mul, ← map_mul, ← map_add, Prod.mk_mul_mk, Prod.mk_mul_mk, Prod.mk_add_mk,
          hab, hbb]
        exact map_one e.symm
      refine ⟨⟦⟨(e.symm (a.1.1, b.1.1), e.symm (a.1.2, b.1.2)), hglue⟩⟧, ?_⟩
      have e1 : crtFst M N h (e.symm (a.1.1, b.1.1)) = a.1.1 := by
        rw [crtFst_apply, RingEquiv.apply_symm_apply]
      have e2 : crtFst M N h (e.symm (a.1.2, b.1.2)) = a.1.2 := by
        rw [crtFst_apply, RingEquiv.apply_symm_apply]
      have e3 : crtSnd M N h (e.symm (a.1.1, b.1.1)) = b.1.1 := by
        rw [crtSnd_apply, RingEquiv.apply_symm_apply]
      have e4 : crtSnd M N h (e.symm (a.1.2, b.1.2)) = b.1.2 := by
        rw [crtSnd_apply, RingEquiv.apply_symm_apply]
      refine congrArg₂ Prod.mk (Quotient.sound ⟨1, ?_, ?_⟩) (Quotient.sound ⟨1, ?_, ?_⟩)
      · show (1 : ZMod M) * crtFst M N h (e.symm (a.1.1, b.1.1)) = a.1.1
        rw [one_mul, e1]
      · show (1 : ZMod M) * crtFst M N h (e.symm (a.1.2, b.1.2)) = a.1.2
        rw [one_mul, e2]
      · show (1 : ZMod N) * crtSnd M N h (e.symm (a.1.1, b.1.1)) = b.1.1
        rw [one_mul, e3]
      · show (1 : ZMod N) * crtSnd M N h (e.symm (a.1.2, b.1.2)) = b.1.2
        rw [one_mul, e4]
  rw [Nat.card_eq_of_bijective F hbij, Nat.card_prod]

end CRT

/-- The projective line over `ℤ/N` has `ψ(N)` points: the count
`#ℙ¹(ℤ/N) = ∏_{p^k ∥ N} (p^k + p^{k-1})`. -/
theorem card_projectiveLine_zmod (N : ℕ) (hN : N ≠ 0) :
    Nat.card (ProjectiveLine (ZMod N)) = dedekindPsi N := by
  induction N using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
      rw [card_projectiveLine_prime_pow p n hp hn.ne', dedekindPsi_prime_pow p n hp hn.ne']
  | zero => exact absurd rfl hN
  | one =>
      rw [dedekindPsi_one]
      have hrep : ∀ q : ProjectiveLine (ZMod 1),
          q = ⟦⟨((1 : ZMod 1), (0 : ZMod 1)), isUnimodularRow_one_left 0⟩⟧ := by
        intro q
        obtain ⟨v, rfl⟩ := Quotient.exists_rep q
        exact Quotient.sound ⟨1, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => (hrep a).trans (hrep b).symm⟩,
        ⟨⟦⟨((1 : ZMod 1), (0 : ZMod 1)), isUnimodularRow_one_left 0⟩⟧⟩⟩
  | coprime a b ha hb hab iha ihb =>
      haveI : NeZero a := ⟨by omega⟩
      haveI : NeZero b := ⟨by omega⟩
      rw [card_projectiveLine_mul a b hab, iha (by omega), ihb (by omega),
        dedekindPsi_mul_of_coprime a b hab]

/-- `[SL₂(ℤ) : Γ₀(N)] = ψ(N)`: the index of `Γ₀(N)` in the full modular group is
the Dedekind psi function. -/
theorem Gamma0_index (N : ℕ) [NeZero N] : (CongruenceSubgroup.Gamma0 N).index = dedekindPsi N := by
  have h1 : (Gamma0 N).index = (borel (ZMod N)).index := by
    rw [Gamma0_eq_comap_borel]
    exact Subgroup.index_comap_of_surjective _ (sl2_surj N)
  rw [h1, Subgroup.index_eq_card, card_quotient_borel,
    card_projectiveLine_zmod N (NeZero.ne N)]

namespace PrimCosetCount

/-- Local name for the shared Dedekind-`ψ` fibre value (`NumberTheory.dedekindPsiFibre`). -/
private def h (x : ℕ × ℕ) : ℕ := dedekindPsiFibre x

private theorem gcd_rotate (a b d : ℕ) : Nat.gcd a (Nat.gcd b d) = Nat.gcd (Nat.gcd a d) b := by
  rw [Nat.gcd_comm b d, ← Nat.gcd_assoc]

private theorem card_primCosetReps_eq_sum (N : ℕ) (hN : N ≠ 0) :
    (primCosetReps N).card = ∑ x ∈ N.divisorsAntidiagonal, h x := by
  classical
  have hσ : (primCosetReps N).card =
      (N.divisorsAntidiagonal.sigma (fun x => (range x.2).filter (fun b => Nat.Coprime (Nat.gcd x.1 x.2) b))).card := by
    refine Finset.card_nbij' (fun t => ⟨(t.1, t.2.2), t.2.1⟩) (fun s => (s.1.1, s.2, s.1.2)) ?_ ?_ ?_ ?_
    · rintro ⟨a, b, d⟩ ht
      rw [Finset.mem_coe, mem_primCosetReps hN] at ht
      obtain ⟨had, hbd, hgcd⟩ := ht
      rw [Finset.mem_coe, Finset.mem_sigma, Nat.mem_divisorsAntidiagonal, Finset.mem_filter, Finset.mem_range]
      exact ⟨⟨had, hN⟩, hbd, by rw [Nat.Coprime, ← gcd_rotate]; exact hgcd⟩
    · rintro ⟨⟨a, d⟩, b⟩ hs
      rw [Finset.mem_coe, Finset.mem_sigma, Nat.mem_divisorsAntidiagonal, Finset.mem_filter, Finset.mem_range] at hs
      obtain ⟨⟨had, -⟩, hbd, hcop⟩ := hs
      rw [Finset.mem_coe, mem_primCosetReps hN]
      exact ⟨had, hbd, by rw [gcd_rotate]; exact hcop⟩
    · rintro ⟨a, b, d⟩ _
      rfl
    · rintro ⟨⟨a, d⟩, b⟩ _
      rfl
  rw [hσ, Finset.card_sigma]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  exact card_fibre x.1 x.2

private theorem sum_divisorsAntidiagonal_mul_of_coprime {f : ℕ × ℕ → ℕ}
    (hf : ∀ a₁ d₁ a₂ d₂ : ℕ, Nat.Coprime (a₁ * d₁) (a₂ * d₂) →
      f (a₁ * a₂, d₁ * d₂) = f (a₁, d₁) * f (a₂, d₂))
    {m n : ℕ} (hmn : Nat.Coprime m n) :
    ∑ x ∈ (m * n).divisorsAntidiagonal, f x =
      (∑ x ∈ m.divisorsAntidiagonal, f x) * (∑ x ∈ n.divisorsAntidiagonal, f x) := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  symm
  refine Finset.sum_nbij' (fun p => (p.1.1 * p.2.1, p.1.2 * p.2.2))
    (fun z => ((Nat.gcd z.1 m, Nat.gcd z.2 m), (Nat.gcd z.1 n, Nat.gcd z.2 n))) ?_ ?_ ?_ ?_ ?_
  ·
    rintro ⟨⟨a₁, d₁⟩, ⟨a₂, d₂⟩⟩ hp
    rw [Finset.mem_product, Nat.mem_divisorsAntidiagonal, Nat.mem_divisorsAntidiagonal] at hp
    obtain ⟨⟨h₁, hm0⟩, ⟨h₂, hn0⟩⟩ := hp
    rw [Nat.mem_divisorsAntidiagonal]
    exact ⟨by rw [← h₁, ← h₂]; ring, Nat.mul_ne_zero hm0 hn0⟩
  ·
    rintro ⟨z₁, z₂⟩ hz
    rw [Nat.mem_divisorsAntidiagonal] at hz
    obtain ⟨hz, hmn0⟩ := hz
    have hm0 : m ≠ 0 := fun h0 => hmn0 (by rw [h0, zero_mul])
    have hn0 : n ≠ 0 := fun h0 => hmn0 (by rw [h0, mul_zero])
    rw [Finset.mem_product, Nat.mem_divisorsAntidiagonal, Nat.mem_divisorsAntidiagonal]
    refine ⟨⟨?_, hm0⟩, ⟨?_, hn0⟩⟩
    · exact Nat.gcd_mul_gcd_of_coprime_of_mul_eq_mul hmn hz
    · exact Nat.gcd_mul_gcd_of_coprime_of_mul_eq_mul hmn.symm (by rw [hz, mul_comm])
  ·
    rintro ⟨⟨a₁, d₁⟩, ⟨a₂, d₂⟩⟩ hp
    rw [Finset.mem_product, Nat.mem_divisorsAntidiagonal, Nat.mem_divisorsAntidiagonal] at hp
    obtain ⟨⟨h₁, hm0⟩, ⟨h₂, hn0⟩⟩ := hp

    have ha₂m : Nat.Coprime a₂ m := Nat.Coprime.coprime_dvd_left (Dvd.intro _ h₂) hmn.symm
    have hd₂m : Nat.Coprime d₂ m := Nat.Coprime.coprime_dvd_left (Dvd.intro_left _ h₂) hmn.symm
    have ha₁n : Nat.Coprime a₁ n := Nat.Coprime.coprime_dvd_left (Dvd.intro _ h₁) hmn
    have hd₁n : Nat.Coprime d₁ n := Nat.Coprime.coprime_dvd_left (Dvd.intro_left _ h₁) hmn
    dsimp only
    simp only [Prod.mk.injEq]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [mul_comm, Nat.Coprime.gcd_mul_left_cancel a₁ ha₂m, Nat.gcd_eq_left (Dvd.intro _ h₁)]
    · rw [mul_comm, Nat.Coprime.gcd_mul_left_cancel d₁ hd₂m, Nat.gcd_eq_left (Dvd.intro_left _ h₁)]
    · rw [Nat.Coprime.gcd_mul_left_cancel a₂ ha₁n, Nat.gcd_eq_left (Dvd.intro _ h₂)]
    · rw [Nat.Coprime.gcd_mul_left_cancel d₂ hd₁n, Nat.gcd_eq_left (Dvd.intro_left _ h₂)]
  ·
    rintro ⟨z₁, z₂⟩ hz
    rw [Nat.mem_divisorsAntidiagonal] at hz
    obtain ⟨hz, hmn0⟩ := hz
    dsimp only
    simp only [Prod.mk.injEq]
    constructor
    · rw [← Nat.Coprime.gcd_mul z₁ hmn, Nat.gcd_eq_left (Dvd.intro _ hz)]
    · rw [← Nat.Coprime.gcd_mul z₂ hmn, Nat.gcd_eq_left (Dvd.intro_left _ hz)]
  ·
    rintro ⟨⟨a₁, d₁⟩, ⟨a₂, d₂⟩⟩ hp
    rw [Finset.mem_product, Nat.mem_divisorsAntidiagonal, Nat.mem_divisorsAntidiagonal] at hp
    obtain ⟨⟨h₁, hm0⟩, ⟨h₂, hn0⟩⟩ := hp
    simp only
    rw [hf a₁ d₁ a₂ d₂ (by rw [h₁, h₂]; exact hmn)]

private theorem h_mul (a₁ d₁ a₂ d₂ : ℕ) (hcop : Nat.Coprime (a₁ * d₁) (a₂ * d₂)) :
    h (a₁ * a₂, d₁ * d₂) = h (a₁, d₁) * h (a₂, d₂) := by
  have ha₁a₂ : Nat.Coprime a₁ a₂ :=
    (Nat.Coprime.coprime_dvd_left (Dvd.intro _ rfl) hcop).coprime_dvd_right (Dvd.intro _ rfl)
  have ha₁d₂ : Nat.Coprime a₁ d₂ :=
    (Nat.Coprime.coprime_dvd_left (Dvd.intro _ rfl) hcop).coprime_dvd_right (Dvd.intro_left _ rfl)
  have hd₁a₂ : Nat.Coprime d₁ a₂ :=
    (Nat.Coprime.coprime_dvd_left (Dvd.intro_left _ rfl) hcop).coprime_dvd_right (Dvd.intro _ rfl)
  have hd₁d₂ : Nat.Coprime d₁ d₂ :=
    (Nat.Coprime.coprime_dvd_left (Dvd.intro_left _ rfl) hcop).coprime_dvd_right (Dvd.intro_left _ rfl)

  have hg : Nat.gcd (a₁ * a₂) (d₁ * d₂) = Nat.gcd a₁ d₁ * Nat.gcd a₂ d₂ := by
    rw [Nat.Coprime.gcd_mul _ hd₁d₂]
    rw [Nat.gcd_comm (a₁ * a₂) d₁, Nat.gcd_comm (a₁ * a₂) d₂,
      Nat.Coprime.gcd_mul _ ha₁a₂, Nat.Coprime.gcd_mul _ ha₁a₂,
      Nat.Coprime.gcd_eq_one hd₁a₂, (Nat.Coprime.gcd_eq_one ha₁d₂.symm), mul_one, one_mul,
      Nat.gcd_comm d₁ a₁, Nat.gcd_comm d₂ a₂]
  have hg₁ : Nat.gcd a₁ d₁ ∣ d₁ := Nat.gcd_dvd_right _ _
  have hg₂ : Nat.gcd a₂ d₂ ∣ d₂ := Nat.gcd_dvd_right _ _
  have hcopg : Nat.Coprime (Nat.gcd a₁ d₁) (Nat.gcd a₂ d₂) :=
    (hd₁d₂.coprime_dvd_left hg₁).coprime_dvd_right hg₂
  simp only [h, dedekindPsiFibre]
  rw [hg, Nat.totient_mul hcopg, ← Nat.div_mul_div_comm hg₁ hg₂]
  ring

private def G : ArithmeticFunction ℕ :=
  ⟨fun n => ∑ x ∈ n.divisorsAntidiagonal, h x, by simp⟩

private theorem G_apply (n : ℕ) : G n = ∑ x ∈ n.divisorsAntidiagonal, h x := rfl

private theorem isMultiplicative_G : G.IsMultiplicative := by
  refine ⟨?_, ?_⟩
  · rw [G_apply]
    simp [h, dedekindPsiFibre, Nat.divisorsAntidiagonal_one]
  · intro m n hmn
    rw [G_apply, G_apply, G_apply]
    exact sum_divisorsAntidiagonal_mul_of_coprime h_mul hmn

private theorem h_prime_pow {p : ℕ} (hp : p.Prime) (i j : ℕ) (hi : 0 < i) (hj : 0 < j) :
    h (p ^ i, p ^ j) + p ^ (j - 1) = p ^ j := by
  simp only [h, dedekindPsiFibre]
  rcases le_or_gt i j with hij | hij
  ·
    rw [Nat.gcd_eq_left (Nat.pow_dvd_pow p hij), Nat.pow_div hij hp.pos, Nat.totient_prime_pow hp hi]
    have : p ^ (j - i) * (p ^ (i - 1) * (p - 1)) + p ^ (j - 1) = p ^ j := by
      have e1 : p ^ (j - i) * p ^ (i - 1) = p ^ (j - 1) := by
        rw [← _root_.pow_add]; congr 1; omega
      have hp1 : 1 ≤ p := hp.one_le
      calc p ^ (j - i) * (p ^ (i - 1) * (p - 1)) + p ^ (j - 1)
          = p ^ (j - 1) * (p - 1) + p ^ (j - 1) := by rw [← mul_assoc, e1]
        _ = p ^ (j - 1) * (p - 1 + 1) := by ring
        _ = p ^ (j - 1) * p := by rw [Nat.sub_add_cancel hp1]
        _ = p ^ j := by rw [← pow_succ]; congr 1; omega
    exact this
  ·
    rw [Nat.gcd_eq_right (Nat.pow_dvd_pow p hij.le), Nat.div_self (pow_pos hp.pos j),
      Nat.totient_prime_pow hp hj, one_mul]
    have hp1 : 1 ≤ p := hp.one_le
    calc p ^ (j - 1) * (p - 1) + p ^ (j - 1) = p ^ (j - 1) * (p - 1 + 1) := by ring
      _ = p ^ (j - 1) * p := by rw [Nat.sub_add_cancel hp1]
      _ = p ^ j := by rw [← pow_succ]; congr 1; omega

private theorem h_one_left (d : ℕ) : h (1, d) = d := by
  simp [h, dedekindPsiFibre]

private theorem h_one_right (a : ℕ) : h (a, 1) = 1 := by
  simp [h, dedekindPsiFibre]

private theorem sum_h_prime_pow_partial {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ∀ J : ℕ, 1 ≤ J → J ≤ k → ∑ j ∈ range J, h (p ^ (k - j), p ^ j) = p ^ (J - 1) := by
  intro J hJ1 hJk
  induction J with
  | zero => omega
  | succ J ih =>
    rcases Nat.eq_zero_or_pos J with rfl | hJpos
    · simp [h_one_right]
    · rw [Finset.sum_range_succ, ih hJpos (by omega)]
      have := h_prime_pow hp (k - J) J (by omega) hJpos

      have e : J + 1 - 1 = J := by omega
      rw [e]
      omega

private theorem G_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) (hk : 0 < k) :
    G (p ^ k) = p ^ k + p ^ (k - 1) := by
  rw [G_apply, Nat.sum_divisorsAntidiagonal' (fun a d => h (a, d)), Nat.sum_divisors_prime_pow hp]

  have hterm : ∀ j ∈ range (k + 1), h (p ^ k / p ^ j, p ^ j) = h (p ^ (k - j), p ^ j) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [Nat.pow_div (by omega) hp.pos]
  rw [Finset.sum_congr rfl hterm, Finset.sum_range_succ, sum_h_prime_pow_partial hp k k hk le_rfl,
    Nat.sub_self, pow_zero, h_one_left, add_comm]

private def sqf : ArithmeticFunction ℕ :=
  ⟨fun n => if Squarefree n then 1 else 0, by simp [not_squarefree_zero]⟩

private theorem sqf_apply (n : ℕ) : sqf n = if Squarefree n then 1 else 0 := rfl

private theorem isMultiplicative_sqf : sqf.IsMultiplicative := by
  refine ⟨by simp [sqf_apply], ?_⟩
  intro m n hmn
  simp only [sqf_apply]
  by_cases hm : Squarefree m <;> by_cases hn : Squarefree n <;>
    simp [hm, hn, Nat.squarefree_mul hmn]

private def Psi : ArithmeticFunction ℕ := sqf * ArithmeticFunction.id

private theorem isMultiplicative_Psi : Psi.IsMultiplicative :=
  isMultiplicative_sqf.mul ArithmeticFunction.isMultiplicative_id

private theorem Psi_apply (n : ℕ) : Psi n = dedekindPsi n := by
  rw [Psi, ArithmeticFunction.mul_apply, dedekindPsi,
    Nat.sum_divisorsAntidiagonal (fun x y => sqf x * ArithmeticFunction.id y), Finset.sum_filter]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [sqf_apply, ArithmeticFunction.id_apply]
  split_ifs <;> simp

private theorem Psi_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) (hk : 0 < k) :
    Psi (p ^ k) = p ^ k + p ^ (k - 1) := by
  rw [Psi_apply, dedekindPsi, Finset.sum_filter, Nat.sum_divisors_prime_pow hp]

  have hterm : ∀ j ∈ range (k + 1),
      (if Squarefree (p ^ j) then p ^ k / p ^ j else 0) = if j = 0 then p ^ k else if j = 1 then p ^ (k - 1) else 0 := by
    intro j hj
    rw [Finset.mem_range] at hj
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · simp
    · rcases eq_or_ne j 1 with rfl | hj1
      · rw [pow_one, ite_eq_left (Irreducible.squarefree hp), ite_eq_right one_ne_zero, ite_eq_left rfl]
        exact Nat.div_eq_of_eq_mul_left hp.pos (by rw [← pow_succ]; congr 1; omega)
      · have : ¬ Squarefree (p ^ j) := by
          rw [Nat.squarefree_pow_iff hp.ne_one (by omega)]
          exact fun h => hj1 h.2
        simp [this, hj1, Nat.pos_iff_ne_zero.mp hjpos]
  rw [Finset.sum_congr rfl hterm]
  rw [Finset.sum_ite, Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
  have h0 : (range (k + 1)).filter (fun j => j = 0) = {0} := by
    ext j; simp
  have h1 : ((range (k + 1)).filter (fun j => ¬ j = 0)).filter (fun j => j = 1) = {1} := by
    ext j; simp; omega
  rw [h0, h1]
  simp

private theorem G_eq_Psi : G = Psi := by
  rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers G isMultiplicative_G Psi isMultiplicative_Psi]
  intro p i hp
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [pow_zero, isMultiplicative_G.map_one, isMultiplicative_Psi.map_one]
  · rw [G_prime_pow hp i hi, Psi_prime_pow hp i hi]

end PrimCosetCount

/-- `(primCosetReps N).card = ψ(N)`: the number of primitive coset
representatives equals the Dedekind psi function. -/
theorem card_primCosetReps_eq_dedekindPsi (N : ℕ) (hN : N ≠ 0) :
    (primCosetReps N).card = dedekindPsi N := by
  rw [PrimCosetCount.card_primCosetReps_eq_sum N hN, ← PrimCosetCount.G_apply,
    PrimCosetCount.G_eq_Psi, PrimCosetCount.Psi_apply]

end ModularCurve

end
