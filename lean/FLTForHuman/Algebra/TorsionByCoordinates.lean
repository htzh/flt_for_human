/-
  Coordinates in `(ZMod n)²` for an abelian group whose `n`-torsion is
  `(ZMod n)²`, under two explicit additive endomorphisms:

  * if `σ` twists the torsion module so that no `p`-torsion point is an
    eigenvector of `σ` modulo any prime `p ∣ n` (`hns`), then the `n`-torsion has a
    basis `P, σ P` (`exists_addEquiv_prod_torsionBy_apply_eq_of_forall_exists_ne_smul`);
  * if `α, β` satisfy the dicyclic relations `α² = -1`, `β² + β + 1 = 0`,
    `α β = β² α` and `3 ∤ n`, then `(M`-torsion) has coordinates in `P, β P` and in
    `P, α P` (`exists_torsionBy_coords_of_dicyclic_relations`).

  The port of the two pin leaves

      `AddCommGroup.exists_addEquiv_prod_torsionBy_apply_eq_of_forall_exists_ne_smul`
      (309 pin lines) and
      `AddCommGroup.exists_torsionBy_coords_of_dicyclic_relations` (331 pin lines),

  together with the statements of their `Theorems/` wrappers. The pin's `S_`
  developments are `namespace P2MKcCB` and `namespace P2MKcADAPT`, kept here under
  the pin's own namespaces and short names untouched. It is a faithful
  transcription: no statement is weakened, no route is generalised, and the pin's
  proofs are carried verbatim (`spec/check_port.py` diffs every public declaration
  below against the four files named here).

  The mathematics is determinant/coprimality bookkeeping. The first node turns the
  question into the coprimality of `d v = v₁ (σ v)₂ - v₂ (σ v)₁`: for a prime
  `p ∣ n` the reduction map `(ZMod n)² → (ZMod p)²` is used to find a vector whose
  determinant is not divisible by `p` (`exists_cast_d_ne_zero`, using the
  `p`-torsion witness of `hns`), and the Chinese remainder theorem
  (`Nat.chineseRemainderOfFinset`) assembles the local witnesses into a single
  vector with `IsUnit (d v)`; `exists_addEquiv_of_isUnit` then builds the basis
  change `φ` from the inverse determinant. The second node repeats the argument with
  the two explicit `2 × 2` matrices defining the dicyclic action (`det_eq_Q`,
  `exists_isUnit_Q`) and reads off the coordinate statement.

  Assumes: mathlib `v4.34.0` only — nothing from earlier modules of the port.

  Drift against mathlib `v4.34.0`, and two recorded deviations:

  * `omit [NeZero n]`/`omit [NeZero M] in` on the 15 declarations the pin's
    file-wide `set_option linter.unusedSectionVars false` suppressed; the two
    `haveI : Fact p.Prime` become `have`; `inv_mul_cancel₀ hγb` in
    `exists_cast_d_ne_zero`'s Bézout step no longer rewrites (the `ZMod p` and
    `GroupWithZero` multiplication paths do not unify), so that step is
    `… ; simp [hγb]`; and the three `Subtype.ext (by simp [h…])` in `main` need
    `coe_resT` named explicitly in the `simp` set (the pin relies on it as a
    `scoped simp` lemma, which is no longer in the default set).
  * **One residual `linter.unusedVariables` warning, unavoidable without a
    suppression**: `exists_isUnit_Q`'s hypothesis is
    `∀ (p : ℕ) (hp : p.Prime) (hpM : p ∣ M), ¬ …`, whose `hp` binder appears
    nowhere in the hypothesis' body — Lean's only repair is `_hp`, which changes the
    statement text and is reported `MISMATCH` by `spec/check_port.py` (verified:
    40 ok / 1 mismatch), so the pin's spelling is kept and the warning recorded.

  spec-pin: Theorems/Thm_AddCommGroup_exists_addEquiv_prod_torsionBy_apply_eq_of_forall_exists_ne_smul.lean
  spec-pin: Theorems/Thm_AddCommGroup_exists_torsionBy_coords_of_dicyclic_relations.lean
  spec-pin: P2M/Sol/S_AddCommGroup_exists_addEquiv_prod_torsionBy_apply_eq_of_forall_exists_ne_smul.lean
  spec-pin: P2M/Sol/S_AddCommGroup_exists_torsionBy_coords_of_dicyclic_relations.lean
-/

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.UniqueFactorizationDomain.Nat
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section

namespace P2MKcCB

variable {A : Type*} [AddCommGroup A] {n : ℕ} [NeZero n]

omit [NeZero n] in
theorem mem_T_iff {a : A} : a ∈ Submodule.torsionBy ℤ A n ↔ n • a = 0 := by
  rw [Submodule.mem_torsionBy_iff, natCast_zsmul]

def σT (σ : A →+ A) : Submodule.torsionBy ℤ A n →+ Submodule.torsionBy ℤ A n where
  toFun t := ⟨σ t, mem_T_iff.2 (by rw [← map_nsmul, mem_T_iff.1 t.2, map_zero])⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

omit [NeZero n] in
@[scoped simp] theorem coe_σT (σ : A →+ A) (t : Submodule.torsionBy ℤ A n) : (σT σ t : A) = σ t := rfl

variable (e : ZMod n × ZMod n ≃+ Submodule.torsionBy ℤ A n) (σ : A →+ A)

def Sg : ZMod n × ZMod n →+ ZMod n × ZMod n :=
  (e.symm.toAddMonoidHom.comp (σT σ)).comp e.toAddMonoidHom

omit [NeZero n] in
theorem coe_e_Sg (v : ZMod n × ZMod n) : ((e (Sg e σ v) : Submodule.torsionBy ℤ A n) : A) = σ (e v : A) := by
  simp [Sg]

theorem zsmul_eq_nsmul (c : ZMod n) (v : ZMod n × ZMod n) : c • v = c.val • v := by
  ext <;> simp [nsmul_eq_mul]

theorem Sg_smul (c : ZMod n) (v : ZMod n × ZMod n) : Sg e σ (c • v) = c • Sg e σ v := by
  rw [zsmul_eq_nsmul, map_nsmul, ← zsmul_eq_nsmul]

def d (v : ZMod n × ZMod n) : ZMod n := v.1 * (Sg e σ v).2 - v.2 * (Sg e σ v).1

omit [NeZero n] in
theorem exists_addEquiv_of_isUnit (v : ZMod n × ZMod n) (hv : IsUnit (d e σ v)) :
    ∃ e' : ZMod n × ZMod n ≃+ Submodule.torsionBy ℤ A n,
      ((e' (0, 1) : Submodule.torsionBy ℤ A n) : A) = σ ((e' (1, 0) : Submodule.torsionBy ℤ A n) : A) := by
  obtain ⟨u, hu⟩ := hv
  set s := Sg e σ v with hs
  have hd : (u : ZMod n) = v.1 * s.2 - v.2 * s.1 := hu
  set di : ZMod n := ((u⁻¹ : (ZMod n)ˣ) : ZMod n) with hdi
  have hdd : di * (v.1 * s.2 - v.2 * s.1) = 1 := by rw [← hd, hdi, Units.inv_mul]
  let φ : ZMod n × ZMod n ≃+ ZMod n × ZMod n :=
    { toFun := fun x => (x.1 * v.1 + x.2 * s.1, x.1 * v.2 + x.2 * s.2)
      invFun := fun y => (di * (s.2 * y.1 - s.1 * y.2), di * (-v.2 * y.1 + v.1 * y.2))
      left_inv := by
        rintro ⟨x, y⟩
        simp only [Prod.mk.injEq]
        constructor
        · linear_combination x * hdd
        · linear_combination y * hdd
      right_inv := by
        rintro ⟨y₁, y₂⟩
        simp only [Prod.mk.injEq]
        constructor
        · linear_combination y₁ * hdd
        · linear_combination y₂ * hdd
      map_add' := by
        rintro ⟨x, y⟩ ⟨x', y'⟩
        simp only [Prod.mk_add_mk, Prod.mk.injEq]
        constructor <;> ring }
  refine ⟨φ.trans e, ?_⟩
  have h10 : φ (1, 0) = v := by
    show ((1 : ZMod n) * v.1 + 0 * s.1, (1 : ZMod n) * v.2 + 0 * s.2) = v
    ext <;> simp
  have h01 : φ (0, 1) = s := by
    show ((0 : ZMod n) * v.1 + 1 * s.1, (0 : ZMod n) * v.2 + 1 * s.2) = s
    ext <;> simp
  rw [AddEquiv.trans_apply, AddEquiv.trans_apply, h10, h01, hs, coe_e_Sg]

section Local

variable {p : ℕ} (hpn : p ∣ n)
include hpn

theorem exists_eq_mul_of_cast_eq_zero (x : ZMod n) (hx : ZMod.castHom hpn (ZMod p) x = 0) :
    ∃ y : ZMod n, x = (p : ZMod n) * y := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff] at hx
  obtain ⟨m, hm⟩ := hx
  refine ⟨(m : ZMod n), ?_⟩
  rw [← ZMod.natCast_zmod_val x, hm, Nat.cast_mul]

omit [NeZero n] in
theorem cast_p_mul (y : ZMod n) : ZMod.castHom hpn (ZMod p) ((p : ZMod n) * y) = 0 := by
  rw [map_mul, map_natCast, ZMod.natCast_self, zero_mul]

theorem exists_eq_mul_of_p_mul_eq_zero (hp : p.Prime) (x : ZMod n) (hx : (p : ZMod n) * x = 0) :
    ∃ y : ZMod n, x = ((n / p : ℕ) : ZMod n) * y := by
  have h1 : n ∣ p * x.val := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_mul, ZMod.natCast_zmod_val]; exact hx
  have h2 : n / p ∣ x.val := by
    obtain ⟨m, hm⟩ := h1
    refine ⟨m, Nat.eq_of_mul_eq_mul_left hp.pos ?_⟩
    rw [hm, ← mul_assoc, Nat.mul_div_cancel' hpn]
  obtain ⟨m, hm⟩ := h2
  refine ⟨(m : ZMod n), ?_⟩
  rw [← ZMod.natCast_zmod_val x, hm, Nat.cast_mul]

omit [NeZero n] in
theorem q_mul_p : ((n / p : ℕ) : ZMod n) * (p : ZMod n) = 0 := by
  rw [← Nat.cast_mul, Nat.div_mul_cancel hpn, ZMod.natCast_self]

def rV : ZMod n × ZMod n →+ ZMod p × ZMod p :=
  (ZMod.castHom hpn (ZMod p)).toAddMonoidHom.prodMap (ZMod.castHom hpn (ZMod p)).toAddMonoidHom

omit [NeZero n] in
theorem rV_apply (v : ZMod n × ZMod n) :
    rV hpn v = (ZMod.castHom hpn (ZMod p) v.1, ZMod.castHom hpn (ZMod p) v.2) := rfl

theorem exists_eq_add_of_rV_eq {v v' : ZMod n × ZMod n} (h : rV hpn v = rV hpn v') :
    ∃ t : ZMod n × ZMod n, v = v' + (p : ZMod n) • t := by
  rw [rV_apply, rV_apply, Prod.mk.injEq] at h
  obtain ⟨t₁, ht₁⟩ := exists_eq_mul_of_cast_eq_zero hpn (v.1 - v'.1) (by rw [map_sub, h.1, sub_self])
  obtain ⟨t₂, ht₂⟩ := exists_eq_mul_of_cast_eq_zero hpn (v.2 - v'.2) (by rw [map_sub, h.2, sub_self])
  refine ⟨(t₁, t₂), ?_⟩
  ext
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]; linear_combination ht₁
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]; linear_combination ht₂

omit [NeZero n] in
theorem rV_p_smul (t : ZMod n × ZMod n) : rV hpn ((p : ZMod n) • t) = 0 := by
  rw [rV_apply]
  ext
  · simp only [Prod.smul_fst, smul_eq_mul, Prod.fst_zero]; exact cast_p_mul hpn _
  · simp only [Prod.smul_snd, smul_eq_mul, Prod.snd_zero]; exact cast_p_mul hpn _

theorem cast_d_eq_of_rV_eq {v v' : ZMod n × ZMod n} (h : rV hpn v = rV hpn v') :
    ZMod.castHom hpn (ZMod p) (d e σ v) = ZMod.castHom hpn (ZMod p) (d e σ v') := by
  obtain ⟨t, rfl⟩ := exists_eq_add_of_rV_eq hpn h
  have hS : rV hpn (Sg e σ (v' + (p : ZMod n) • t)) = rV hpn (Sg e σ v') := by
    rw [map_add, Sg_smul, map_add, rV_p_smul, add_zero]
  rw [rV_apply, rV_apply, Prod.mk.injEq] at h hS
  simp only [d, map_sub, map_mul, h.1, h.2, hS.1, hS.2]

theorem exists_cast_d_ne_zero (hp : p.Prime)
    (hns : ∃ a : A, addOrderOf a = p ∧ ∀ k : ℕ, σ a ≠ k • a) :
    ∃ u : ZMod n × ZMod n, ZMod.castHom hpn (ZMod p) (d e σ u) ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha, hna⟩ := hns
  have hpa : p • a = 0 := by rw [← ha]; exact addOrderOf_nsmul_eq_zero a
  have haT : a ∈ Submodule.torsionBy ℤ A n := by
    rw [mem_T_iff]
    obtain ⟨m, hm⟩ := hpn
    rw [hm, mul_comm, mul_nsmul', hpa, nsmul_zero]
  set w : ZMod n × ZMod n := e.symm ⟨a, haT⟩ with hw_def
  have hew : (e w : A) = a := by rw [hw_def, AddEquiv.apply_symm_apply]
  have hpw : (p : ZMod n) • w = 0 := by
    apply e.injective
    rw [zsmul_eq_nsmul, map_nsmul, map_zero, ZMod.val_natCast]
    apply Subtype.ext
    show (p % n) • ((e w : Submodule.torsionBy ℤ A n) : A) = 0
    rw [hew]
    have : (p % n) • a = p • a := by
      conv_rhs => rw [← Nat.mod_add_div p n]
      rw [add_nsmul, mul_comm, mul_nsmul', mem_T_iff.1 haT, nsmul_zero, add_zero]
    rw [this, hpa]
  have hw0 : w ≠ 0 := by
    intro h
    have : a = 0 := by
      rw [← hew, h, map_zero]; rfl
    rw [this, addOrderOf_zero] at ha
    exact hp.one_lt.ne ha
  have hSw : ∀ c : ZMod n, Sg e σ w ≠ c • w := by
    intro c hc
    apply hna c.val
    rw [← hew, ← coe_e_Sg, hc, zsmul_eq_nsmul, map_nsmul]
    rfl

  obtain ⟨u₁, hu₁⟩ := exists_eq_mul_of_p_mul_eq_zero hpn hp w.1
    (by have := congrArg Prod.fst hpw; simpa using this)
  obtain ⟨u₂, hu₂⟩ := exists_eq_mul_of_p_mul_eq_zero hpn hp w.2
    (by have := congrArg Prod.snd hpw; simpa using this)
  set q : ZMod n := ((n / p : ℕ) : ZMod n) with hq
  set u : ZMod n × ZMod n := (u₁, u₂) with hu
  have hwu : w = q • u := by ext <;> simp [hu, hu₁, hu₂]
  refine ⟨u, fun hdu => ?_⟩

  set r := ZMod.castHom hpn (ZMod p) with hr
  set ub : ZMod p × ZMod p := rV hpn u with hub
  set sb : ZMod p × ZMod p := rV hpn (Sg e σ u) with hsb
  have hdet : ub.1 * sb.2 - ub.2 * sb.1 = 0 := by
    have : r (d e σ u) = ub.1 * sb.2 - ub.2 * sb.1 := by
      simp only [d, map_sub, map_mul, hub, hsb, rV_apply, hr]
    rw [← this]; exact hdu
  have hdep : ∃ α β : ZMod p, (α ≠ 0 ∨ β ≠ 0) ∧ α • ub + β • sb = 0 := by
    by_cases hub0 : ub = 0
    · exact ⟨1, 0, Or.inl one_ne_zero, by rw [hub0, smul_zero, zero_smul, add_zero]⟩
    · by_cases h1 : ub.1 ≠ 0
      · refine ⟨-sb.1, ub.1, Or.inr h1, ?_⟩
        ext
        · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, Prod.fst_zero]; ring
        · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, Prod.snd_zero]; linear_combination hdet
      · push Not at h1
        have h2 : ub.2 ≠ 0 := by
          intro h2; exact hub0 (Prod.ext h1 h2)
        refine ⟨-sb.2, ub.2, Or.inr h2, ?_⟩
        ext
        · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, Prod.fst_zero]; linear_combination -hdet
        · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, Prod.snd_zero]; ring
  obtain ⟨αb, βb, hnz, hrel⟩ := hdep

  set α : ZMod n := (αb.val : ZMod n) with hα
  set β : ZMod n := (βb.val : ZMod n) with hβ
  have hrα : r α = αb := by rw [hα, map_natCast, ZMod.natCast_zmod_val]
  have hrβ : r β = βb := by rw [hβ, map_natCast, ZMod.natCast_zmod_val]
  have hz : rV hpn (α • u + β • Sg e σ u) = 0 := by
    have : rV hpn (α • u + β • Sg e σ u) = αb • ub + βb • sb := by
      rw [hub, hsb, rV_apply, rV_apply, rV_apply]
      ext
      · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, map_add, map_mul, ← hr, hrα, hrβ]
      · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, map_add, map_mul, ← hr, hrα, hrβ]
    rw [this, hrel]
  obtain ⟨t, ht⟩ := exists_eq_add_of_rV_eq hpn (v' := 0) (by rw [hz, map_zero])
  rw [zero_add] at ht
  have hstar : α • w + β • Sg e σ w = 0 := by
    have : q • (α • u + β • Sg e σ u) = 0 := by
      rw [ht, smul_smul, hq, q_mul_p hpn, zero_smul]
    rw [hwu, Sg_smul, smul_comm α q u, smul_comm β q, ← smul_add, this]
  have hpS : (p : ZMod n) • Sg e σ w = 0 := by rw [← Sg_smul, hpw, map_zero]

  have hinv : ∀ γb : ZMod p, γb ≠ 0 → ∀ γ : ZMod n, r γ = γb →
      ∃ γ' t' : ZMod n, γ' * γ = 1 + (p : ZMod n) * t' := by
    intro γb hγb γ hγ
    set γ' : ZMod n := ((γb⁻¹).val : ZMod n)
    have hr' : r γ' = γb⁻¹ := by simp [γ', hr]
    obtain ⟨t', ht'⟩ := exists_eq_mul_of_cast_eq_zero hpn (γ' * γ - 1)
      (by rw [map_sub, map_mul, map_one, ← hr, hr', hγ]; simp [hγb])
    exact ⟨γ', t', by linear_combination ht'⟩
  rcases hnz with hαb | hβb
  ·
    by_cases hβb : βb = 0
    · obtain ⟨tβ, htβ⟩ := exists_eq_mul_of_cast_eq_zero hpn β (by rw [← hr, hrβ, hβb])
      have hβS : β • Sg e σ w = 0 := by rw [htβ, mul_comm, ← smul_smul, hpS, smul_zero]
      rw [hβS, add_zero] at hstar
      obtain ⟨α', t', hα'⟩ := hinv αb hαb α hrα
      apply hw0
      calc w = (α' * α) • w - t' • ((p : ZMod n) • w) := by
              rw [hα', add_smul, one_smul, smul_smul, mul_comm t', add_sub_cancel_right]
        _ = 0 := by rw [← smul_smul, hstar, smul_zero, hpw, smul_zero, sub_zero]
    · obtain ⟨β', t', hβ'⟩ := hinv βb hβb β hrβ
      apply hSw (-(β' * α))
      have h1 : β' • (α • w + β • Sg e σ w) = 0 := by rw [hstar, smul_zero]
      rw [smul_add, smul_smul, smul_smul, hβ', add_smul, one_smul, mul_smul (p : ZMod n) t',
        smul_comm (p : ZMod n) t', hpS, smul_zero, add_zero] at h1
      rw [neg_smul]
      exact eq_neg_of_add_eq_zero_right h1
  · obtain ⟨β', t', hβ'⟩ := hinv βb hβb β hrβ
    apply hSw (-(β' * α))
    have h1 : β' • (α • w + β • Sg e σ w) = 0 := by rw [hstar, smul_zero]
    rw [smul_add, smul_smul, smul_smul, hβ', add_smul, one_smul, mul_smul (p : ZMod n) t',
      smul_comm (p : ZMod n) t', hpS, smul_zero, add_zero] at h1
    rw [neg_smul]
    exact eq_neg_of_add_eq_zero_right h1

end Local

theorem exists_isUnit_d
    (hns : ∀ p : ℕ, p.Prime → p ∣ n → ∃ a : A, addOrderOf a = p ∧ ∀ k : ℕ, σ a ≠ k • a) :
    ∃ v : ZMod n × ZMod n, IsUnit (d e σ v) := by
  classical

  have loc : ∀ p ∈ n.primeFactors, ∃ u : ZMod n × ZMod n, ∀ hpn : p ∣ n,
      ZMod.castHom hpn (ZMod p) (d e σ u) ≠ 0 := by
    intro p hp
    obtain ⟨u, hu⟩ := exists_cast_d_ne_zero e σ (Nat.dvd_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hp)
      (hns p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp))
    exact ⟨u, fun _ => hu⟩
  choose! uu huu using loc

  have hs : ∀ i ∈ n.primeFactors, (id i) ≠ 0 := fun i hi => (Nat.prime_of_mem_primeFactors hi).ne_zero
  have pp : Set.Pairwise (n.primeFactors : Set ℕ) (Function.onFun Nat.Coprime id) := by
    intro i hi j hj hij
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hi) (Nat.prime_of_mem_primeFactors hj)).2 hij
  obtain ⟨k₁, hk₁⟩ := Nat.chineseRemainderOfFinset (fun p => (uu p).1.val) id n.primeFactors hs pp
  obtain ⟨k₂, hk₂⟩ := Nat.chineseRemainderOfFinset (fun p => (uu p).2.val) id n.primeFactors hs pp
  refine ⟨((k₁ : ZMod n), (k₂ : ZMod n)), ?_⟩

  rw [← ZMod.natCast_zmod_val (d e σ _), ZMod.isUnit_iff_coprime]
  apply Nat.coprime_of_dvd
  intro p hp hpd hpn
  have hmem : p ∈ n.primeFactors := Nat.mem_primeFactors.2 ⟨hp, hpn, NeZero.ne n⟩
  apply huu p hmem hpn

  have hred : rV hpn ((k₁ : ZMod n), (k₂ : ZMod n)) = rV hpn (uu p) := by
    rw [rV_apply, rV_apply]
    have e1 : ZMod.castHom hpn (ZMod p) (k₁ : ZMod n) = ZMod.castHom hpn (ZMod p) (uu p).1 := by
      rw [map_natCast, ← ZMod.natCast_zmod_val (uu p).1, map_natCast, ZMod.natCast_eq_natCast_iff]
      exact hk₁ p hmem
    have e2 : ZMod.castHom hpn (ZMod p) (k₂ : ZMod n) = ZMod.castHom hpn (ZMod p) (uu p).2 := by
      rw [map_natCast, ← ZMod.natCast_zmod_val (uu p).2, map_natCast, ZMod.natCast_eq_natCast_iff]
      exact hk₂ p hmem
    rw [e1, e2]
  rw [← cast_d_eq_of_rV_eq e σ hpn hred, ZMod.castHom_apply, ZMod.cast_eq_val,
    ZMod.natCast_eq_zero_iff]
  exact hpd

end P2MKcCB

theorem AddCommGroup.exists_addEquiv_prod_torsionBy_apply_eq_of_forall_exists_ne_smul
    {A : Type*} [AddCommGroup A] (n : ℕ) [NeZero n]
    (e : ZMod n × ZMod n ≃+ Submodule.torsionBy ℤ A n) (σ : A →+ A)
    (hns : ∀ p : ℕ, p.Prime → p ∣ n → ∃ a : A, addOrderOf a = p ∧ ∀ k : ℕ, σ a ≠ k • a) :
    ∃ e' : ZMod n × ZMod n ≃+ Submodule.torsionBy ℤ A n,
      ((e' (0, 1) : Submodule.torsionBy ℤ A n) : A) =
        σ ((e' (1, 0) : Submodule.torsionBy ℤ A n) : A) := by
  obtain ⟨v, hv⟩ := P2MKcCB.exists_isUnit_d e σ hns
  exact P2MKcCB.exists_addEquiv_of_isUnit e σ v hv


namespace P2MKcADAPT

variable {M : ℕ} [NeZero M]

abbrev V (M : ℕ) : Type := ZMod M × ZMod M

omit [NeZero M] in
theorem nsmul_V (n : ℕ) (v : V M) : n • v = ((n : ZMod M) * v.1, (n : ZMod M) * v.2) := by
  ext <;> simp [nsmul_eq_mul]

theorem val_nsmul_V (u : ZMod M) (v : V M) : u.val • v = (u * v.1, u * v.2) := by
  rw [nsmul_V, ZMod.natCast_zmod_val]

theorem eq_val_smul_add (v : V M) : v = v.1.val • ((1 : ZMod M), (0 : ZMod M)) + v.2.val • ((0 : ZMod M), (1 : ZMod M)) := by
  rw [val_nsmul_V, val_nsmul_V]; ext <;> simp

theorem apply_eq (ψ : V M →+ V M) (r0 r1 : V M) (h0 : ψ (1, 0) = r0) (h1 : ψ (0, 1) = r1) (v : V M) :
    ψ v = (v.1 * r0.1 + v.2 * r1.1, v.1 * r0.2 + v.2 * r1.2) := by
  conv_lhs => rw [eq_val_smul_add v]
  rw [map_add, map_nsmul, map_nsmul, h0, h1, val_nsmul_V, val_nsmul_V]
  rfl

section Coords

variable {A : Type*} [AddCommGroup A] (e : ZMod M × ZMod M ≃+ Submodule.torsionBy ℤ A M)

def resT (φ : A →+ A) : Submodule.torsionBy ℤ A M →+ Submodule.torsionBy ℤ A M where
  toFun t := ⟨φ t, by
    rw [Submodule.mem_torsionBy_iff]
    have := t.2
    rw [Submodule.mem_torsionBy_iff] at this
    rw [← map_zsmul, this, map_zero]⟩
  map_zero' := by ext; simp
  map_add' s t := by ext; simp

omit [NeZero M] in
@[scoped simp]
theorem coe_resT (φ : A →+ A) (t : Submodule.torsionBy ℤ A M) : ((resT φ t : _) : A) = φ t := rfl

def toV (φ : A →+ A) : V M →+ V M :=
  e.symm.toAddMonoidHom.comp ((resT φ).comp e.toAddMonoidHom)

omit [NeZero M] in
theorem toV_apply (φ : A →+ A) (v : V M) : toV e φ v = e.symm (resT φ (e v)) := rfl

omit [NeZero M] in
theorem e_toV (φ : A →+ A) (v : V M) : e (toV e φ v) = resT φ (e v) := by
  rw [toV_apply, AddEquiv.apply_symm_apply]

omit [NeZero M] in
theorem coe_e_toV (φ : A →+ A) (v : V M) : ((e (toV e φ v) : _) : A) = φ (e v) := by
  rw [e_toV]; rfl

omit [NeZero M] in
theorem toV_toV (φ χ : A →+ A) (v : V M) : toV e φ (toV e χ v) = e.symm (resT φ (resT χ (e v))) := by
  rw [toV_apply, e_toV]

theorem coords_of_isUnit (φ : A →+ A) (w : V M)
    (hu : IsUnit (w.1 * (toV e φ w).2 - w.2 * (toV e φ w).1)) :
    ∃ P : A, (M : ℤ) • P = 0 ∧ ∀ T : A, (M : ℤ) • T = 0 →
      ∃! c : ZMod M × ZMod M, c.1.val • P + c.2.val • φ P = T := by
  set f : V M := toV e φ w with hf
  set P : A := ((e w : _) : A) with hP
  have hPmem : (M : ℤ) • P = 0 := by
    have := (e w).2
    rw [Submodule.mem_torsionBy_iff] at this
    exact this

  let L : V M → V M := fun c => c.1.val • w + c.2.val • f
  have hL : ∀ c, L c = (c.1 * w.1 + c.2 * f.1, c.1 * w.2 + c.2 * f.2) := by
    intro c
    show c.1.val • w + c.2.val • f = _
    rw [val_nsmul_V, val_nsmul_V]; rfl
  have hLinj : Function.Injective L := by
    intro c d hcd
    rw [hL, hL, Prod.mk.injEq] at hcd
    obtain ⟨h1, h2⟩ := hcd
    have e1 : (c.1 - d.1) * (w.1 * f.2 - w.2 * f.1) = 0 := by linear_combination f.2 * h1 - f.1 * h2
    have e2 : (c.2 - d.2) * (w.1 * f.2 - w.2 * f.1) = 0 := by linear_combination (-w.2) * h1 + w.1 * h2
    rw [hu.mul_left_eq_zero, sub_eq_zero] at e1 e2
    exact Prod.ext e1 e2
  have hLsurj : Function.Surjective L := Finite.injective_iff_surjective.mp hLinj

  have he : ∀ c : V M, ((e (L c) : _) : A) = c.1.val • P + c.2.val • φ P := by
    intro c
    show ((e (c.1.val • w + c.2.val • f) : _) : A) = _
    rw [map_add, map_nsmul, map_nsmul, Submodule.coe_add, AddSubmonoidClass.coe_nsmul,
      AddSubmonoidClass.coe_nsmul, hf, coe_e_toV]
  refine ⟨P, hPmem, fun T hT => ?_⟩
  have hTmem : T ∈ Submodule.torsionBy ℤ A M := by rw [Submodule.mem_torsionBy_iff]; exact hT
  obtain ⟨c, hc⟩ := hLsurj (e.symm ⟨T, hTmem⟩)
  refine ⟨c, ?_, fun d hd => ?_⟩
  · show c.1.val • P + c.2.val • φ P = T
    rw [← he, hc, AddEquiv.apply_symm_apply]
  · apply hLinj
    apply e.injective
    apply Subtype.ext
    rw [he, he, hd, ← he, hc, AddEquiv.apply_symm_apply]

end Coords

def Q {R : Type*} [CommRing R] (b00 b01 b10 b11 x y : R) : R :=
  b01 * x * x + (b11 - b00) * x * y - b10 * y * y

theorem det_eq_Q (ψ : V M →+ V M) (r0 r1 : V M) (h0 : ψ (1, 0) = r0) (h1 : ψ (0, 1) = r1) (w : V M) :
    w.1 * (ψ w).2 - w.2 * (ψ w).1 = Q r0.1 r0.2 r1.1 r1.2 w.1 w.2 := by
  rw [apply_eq ψ r0 r1 h0 h1, Q]
  ring

theorem map_Q {R S : Type*} [CommRing R] [CommRing S] (π : R →+* S) (b00 b01 b10 b11 x y : R) :
    π (Q b00 b01 b10 b11 x y) = Q (π b00) (π b01) (π b10) (π b11) (π x) (π y) := by
  simp [Q, map_sub, map_mul, map_add]

set_option linter.unusedVariables false in
theorem exists_isUnit_Q (b00 b01 b10 b11 : ZMod M)
    (hns : ∀ (p : ℕ) (hp : p.Prime) (hpM : p ∣ M),
      ¬ ((ZMod.castHom hpM (ZMod p)) b01 = 0 ∧ (ZMod.castHom hpM (ZMod p)) b10 = 0 ∧
          (ZMod.castHom hpM (ZMod p)) b00 = (ZMod.castHom hpM (ZMod p)) b11)) :
    ∃ x y : ZMod M, IsUnit (Q b00 b01 b10 b11 x y) := by
  classical

  have htest : ∀ p : ℕ, ∃ v : ℕ × ℕ, ∀ (hp : p.Prime) (hpM : p ∣ M),
      (ZMod.castHom hpM (ZMod p)) (Q b00 b01 b10 b11 (v.1 : ZMod M) (v.2 : ZMod M)) ≠ 0 := by
    intro p
    by_cases hp : p.Prime ∧ p ∣ M
    · obtain ⟨hp, hpM⟩ := hp
      set π := ZMod.castHom hpM (ZMod p) with hπ
      by_contra hcon
      push Not at hcon
      obtain ⟨_, _, h10⟩ := hcon (1, 0)
      obtain ⟨_, _, h01⟩ := hcon (0, 1)
      obtain ⟨_, _, h11⟩ := hcon (1, 1)
      rw [map_Q] at h10 h01 h11
      simp only [Nat.cast_one, Nat.cast_zero, map_one, map_zero] at h10 h01 h11
      simp only [Q] at h10 h01 h11
      apply hns p hp hpM
      refine ⟨?_, ?_, ?_⟩
      · linear_combination h10
      · linear_combination -h01
      · linear_combination h10 + h01 - h11
    · exact ⟨(0, 0), fun hp' hpM' => absurd ⟨hp', hpM'⟩ hp⟩
  choose pick hpick using htest

  set t : Finset ℕ := M.primeFactors with ht
  have hs : ∀ i ∈ t, (id i : ℕ) ≠ 0 := fun i hi => (Nat.prime_of_mem_primeFactors hi).ne_zero
  have hpw : (t : Set ℕ).Pairwise (Function.onFun Nat.Coprime id) := by
    intro i hi j hj hij
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hi) (Nat.prime_of_mem_primeFactors hj)).mpr hij
  obtain ⟨X, hX⟩ := Nat.chineseRemainderOfFinset (fun p => (pick p).1) id t hs hpw
  obtain ⟨Y, hY⟩ := Nat.chineseRemainderOfFinset (fun p => (pick p).2) id t hs hpw
  refine ⟨(X : ZMod M), (Y : ZMod M), ?_⟩
  set z := Q b00 b01 b10 b11 (X : ZMod M) (Y : ZMod M) with hz
  rw [← ZMod.natCast_zmod_val z]
  apply (ZMod.isUnit_iff_coprime _ _).mpr
  apply Nat.coprime_of_dvd
  intro k hk hkz hkM
  have hkt : k ∈ t := Nat.mem_primeFactors.mpr ⟨hk, hkM, NeZero.ne M⟩
  set π := ZMod.castHom hkM (ZMod k) with hπ
  have h1 : π z = 0 := by
    rw [← ZMod.natCast_zmod_val z, map_natCast, ZMod.natCast_eq_zero_iff]
    exact hkz
  have hXk : π (X : ZMod M) = ((pick k).1 : ZMod k) := by
    rw [map_natCast]
    have hh := hX k hkt
    simp only [id] at hh
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hh
  have hYk : π (Y : ZMod M) = ((pick k).2 : ZMod k) := by
    rw [map_natCast]
    have hh := hY k hkt
    simp only [id] at hh
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hh
  have h2 : π z = π (Q b00 b01 b10 b11 ((pick k).1 : ZMod M) ((pick k).2 : ZMod M)) := by
    rw [hz, map_Q, map_Q, hXk, hYk, map_natCast, map_natCast]
  exact hpick k hk hkM (h2 ▸ h1)

theorem not_scalar {p : ℕ} [Fact p.Prime] (h3 : (3 : ZMod p) ≠ 0)
    (a00 a01 a10 a11 b00 b01 b10 b11 : ZMod p)
    (hA1 : a00 * a00 + a01 * a10 = -1) (hA2 : a00 * a01 + a01 * a11 = 0)
    (hA3 : a10 * a00 + a11 * a10 = 0) (hA4 : a10 * a01 + a11 * a11 = -1)
    (hB1 : b00 * b00 + b01 * b10 + b00 + 1 = 0) (hB2 : b00 * b01 + b01 * b11 + b01 = 0)
    (hB3 : b10 * b00 + b11 * b10 + b10 = 0) (hB4 : b10 * b01 + b11 * b11 + b11 + 1 = 0)
    (hC1 : b00 * a00 + b01 * a10 = (a00 * b00 + a01 * b10) * b00 + (a00 * b01 + a01 * b11) * b10)
    (hC2 : b00 * a01 + b01 * a11 = (a00 * b00 + a01 * b10) * b01 + (a00 * b01 + a01 * b11) * b11)
    (hC3 : b10 * a00 + b11 * a10 = (a10 * b00 + a11 * b10) * b00 + (a10 * b01 + a11 * b11) * b10)
    (hC4 : b10 * a01 + b11 * a11 = (a10 * b00 + a11 * b10) * b01 + (a10 * b01 + a11 * b11) * b11) :
    ¬ (b01 = 0 ∧ b10 = 0 ∧ b00 = b11) ∧ ¬ (a01 = 0 ∧ a10 = 0 ∧ a00 = a11) := by
  have hβ : ¬ (b01 = 0 ∧ b10 = 0 ∧ b00 = b11) := by
    rintro ⟨h01, h10, hd⟩
    subst h01 h10
    subst hd

    have E1 : b00 * a00 - b00 * b00 * a00 = 0 := by linear_combination hC1
    have E3 : b00 * a10 - b00 * b00 * a10 = 0 := by linear_combination hC3
    have hk : b00 * b00 - b00 = 0 := by
      linear_combination (b00 * b00 - b00) * hA1 + a00 * E1 + a01 * E3
    apply h3
    linear_combination (3 - 2 * b00) * hB1 + (2 * b00 + 1) * hk
  refine ⟨hβ, ?_⟩
  rintro ⟨h01, h10, hd⟩
  subst h01 h10
  subst hd

  have S1 : b00 - (b00 * b00 + b01 * b10) = 0 := by
    linear_combination (-a00) * hC1 + (b00 - (b00 * b00 + b01 * b10)) * hA1
  have S2 : b01 - (b00 * b01 + b01 * b11) = 0 := by
    linear_combination (-a00) * hC2 + (b01 - (b00 * b01 + b01 * b11)) * hA1
  have S3 : b10 - (b10 * b00 + b11 * b10) = 0 := by
    linear_combination (-a00) * hC3 + (b10 - (b10 * b00 + b11 * b10)) * hA1
  have S4 : b11 - (b10 * b01 + b11 * b11) = 0 := by
    linear_combination (-a00) * hC4 + (b11 - (b10 * b01 + b11 * b11)) * hA1
  have F1 : 2 * b00 + 1 = 0 := by linear_combination hB1 + S1
  have F2 : 2 * b01 = 0 := by linear_combination hB2 + S2
  have F3 : 2 * b10 = 0 := by linear_combination hB3 + S3
  have F4 : 2 * b11 + 1 = 0 := by linear_combination hB4 + S4
  by_cases h2 : (2 : ZMod p) = 0
  · have : (1 : ZMod p) = 0 := by linear_combination F1 - b00 * h2
    exact one_ne_zero this
  · apply hβ
    refine ⟨(mul_eq_zero.mp F2).resolve_left h2, (mul_eq_zero.mp F3).resolve_left h2, ?_⟩
    have : 2 * (b00 - b11) = 0 := by linear_combination F1 - F4
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h2)

section Assembly

variable {A : Type*} [AddCommGroup A]

theorem main (hM : ¬ 3 ∣ M) (e : ZMod M × ZMod M ≃+ Submodule.torsionBy ℤ A M)
    (α β : A →+ A) (hα : ∀ T, α (α T) = -T) (hβ : ∀ T, β (β T) + β T + T = 0)
    (hαβ : ∀ T, α (β T) = β (β (α T))) :
    (∃ P : A, (M : ℤ) • P = 0 ∧ ∀ T : A, (M : ℤ) • T = 0 →
      ∃! c : ZMod M × ZMod M, c.1.val • P + c.2.val • β P = T) ∧
    (∃ P : A, (M : ℤ) • P = 0 ∧ ∀ T : A, (M : ℤ) • T = 0 →
      ∃! c : ZMod M × ZMod M, c.1.val • P + c.2.val • α P = T) := by
  set αV := toV e α with hαVdef
  set βV := toV e β with hβVdef

  have rαα : ∀ t : Submodule.torsionBy ℤ A M, resT α (resT α t) = -t := fun t =>
    Subtype.ext (by simp [coe_resT, hα])
  have rββ : ∀ t : Submodule.torsionBy ℤ A M, resT β (resT β t) + resT β t + t = 0 := fun t =>
    Subtype.ext (by simp [coe_resT, hβ])
  have rαβ : ∀ t : Submodule.torsionBy ℤ A M, resT α (resT β t) = resT β (resT β (resT α t)) := fun t =>
    Subtype.ext (by simp [coe_resT, hαβ])
  have hαV : ∀ v, αV (αV v) = -v := fun v => by
    rw [hαVdef, toV_toV, rαα, map_neg, AddEquiv.symm_apply_apply]
  have hβV : ∀ v, βV (βV v) + βV v + v = 0 := fun v => by
    rw [hβVdef, toV_toV, toV_apply]
    apply e.injective
    rw [map_add, map_add, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, map_zero]
    exact rββ (e v)
  have hαβV : ∀ v, αV (βV v) = βV (βV (αV v)) := fun v => by
    rw [hαVdef, hβVdef, toV_toV, toV_apply, toV_toV, AddEquiv.apply_symm_apply, rαβ]

  obtain ⟨a00, a01, ha0⟩ : ∃ a00 a01 : ZMod M, αV (1, 0) = (a00, a01) := ⟨_, _, rfl⟩
  obtain ⟨a10, a11, ha1⟩ : ∃ a10 a11 : ZMod M, αV (0, 1) = (a10, a11) := ⟨_, _, rfl⟩
  obtain ⟨b00, b01, hb0⟩ : ∃ b00 b01 : ZMod M, βV (1, 0) = (b00, b01) := ⟨_, _, rfl⟩
  obtain ⟨b10, b11, hb1⟩ : ∃ b10 b11 : ZMod M, βV (0, 1) = (b10, b11) := ⟨_, _, rfl⟩
  have eA := apply_eq αV _ _ ha0 ha1
  have eB := apply_eq βV _ _ hb0 hb1

  have hA := hαV (1, 0)
  have hA' := hαV (0, 1)
  have hB := hβV (1, 0)
  have hB' := hβV (0, 1)
  have hC := hαβV (1, 0)
  have hC' := hαβV (0, 1)
  simp only [eA, eB, Prod.mk.injEq, Prod.neg_mk, Prod.mk_add_mk, Prod.mk_eq_zero, one_mul, zero_mul,
    add_zero, zero_add, neg_zero] at hA hA' hB hB' hC hC'
  obtain ⟨hA1, hA2⟩ := hA
  obtain ⟨hA3, hA4⟩ := hA'
  obtain ⟨hB1, hB2⟩ := hB
  obtain ⟨hB3, hB4⟩ := hB'
  obtain ⟨hC1, hC2⟩ := hC
  obtain ⟨hC3, hC4⟩ := hC'

  have hns : ∀ (p : ℕ) (hp : p.Prime) (hpM : p ∣ M),
      ¬ ((ZMod.castHom hpM (ZMod p)) b01 = 0 ∧ (ZMod.castHom hpM (ZMod p)) b10 = 0 ∧
          (ZMod.castHom hpM (ZMod p)) b00 = (ZMod.castHom hpM (ZMod p)) b11) ∧
      ¬ ((ZMod.castHom hpM (ZMod p)) a01 = 0 ∧ (ZMod.castHom hpM (ZMod p)) a10 = 0 ∧
          (ZMod.castHom hpM (ZMod p)) a00 = (ZMod.castHom hpM (ZMod p)) a11) := by
    intro p hp hpM
    have : Fact p.Prime := ⟨hp⟩
    set π := ZMod.castHom hpM (ZMod p) with hπ
    have h3 : (3 : ZMod p) ≠ 0 := by
      intro h
      have h' : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at h'
      have : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h'
      subst this
      exact hM hpM
    have m := fun (x y : ZMod M) (h : x = y) => congrArg π h
    refine not_scalar h3 (π a00) (π a01) (π a10) (π a11) (π b00) (π b01) (π b10) (π b11)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simpa only [map_add, map_mul, map_neg, map_one] using m _ _ hA1
    · simpa only [map_add, map_mul, map_zero] using m _ _ hA2
    · simpa only [map_add, map_mul, map_zero] using m _ _ hA3
    · simpa only [map_add, map_mul, map_neg, map_one] using m _ _ hA4
    · simpa only [map_add, map_mul, map_one, map_zero] using m _ _ hB1
    · simpa only [map_add, map_mul, map_zero] using m _ _ hB2
    · simpa only [map_add, map_mul, map_zero] using m _ _ hB3
    · simpa only [map_add, map_mul, map_one, map_zero] using m _ _ hB4
    · simpa only [map_add, map_mul] using m _ _ hC1
    · simpa only [map_add, map_mul] using m _ _ hC2
    · simpa only [map_add, map_mul] using m _ _ hC3
    · simpa only [map_add, map_mul] using m _ _ hC4
  refine ⟨?_, ?_⟩
  · obtain ⟨x, y, hu⟩ := exists_isUnit_Q b00 b01 b10 b11 (fun p hp hpM => (hns p hp hpM).1)
    refine coords_of_isUnit e β (x, y) ?_
    rw [← hβVdef, det_eq_Q βV _ _ hb0 hb1]
    exact hu
  · obtain ⟨x, y, hu⟩ := exists_isUnit_Q a00 a01 a10 a11 (fun p hp hpM => (hns p hp hpM).2)
    refine coords_of_isUnit e α (x, y) ?_
    rw [← hαVdef, det_eq_Q αV _ _ ha0 ha1]
    exact hu

end Assembly

end P2MKcADAPT

theorem AddCommGroup.exists_torsionBy_coords_of_dicyclic_relations
    (M : ℕ) [NeZero M] (hM : ¬ 3 ∣ M) {A : Type*} [AddCommGroup A]
    (e : ZMod M × ZMod M ≃+ Submodule.torsionBy ℤ A M)
    (α β : A →+ A) (hα : ∀ T, α (α T) = -T) (hβ : ∀ T, β (β T) + β T + T = 0)
    (hαβ : ∀ T, α (β T) = β (β (α T))) :
    (∃ P : A, (M : ℤ) • P = 0 ∧ ∀ T : A, (M : ℤ) • T = 0 →
      ∃! c : ZMod M × ZMod M, c.1.val • P + c.2.val • β P = T) ∧
    (∃ P : A, (M : ℤ) • P = 0 ∧ ∀ T : A, (M : ℤ) • T = 0 →
      ∃! c : ZMod M × ZMod M, c.1.val • P + c.2.val • α P = T) :=
  P2MKcADAPT.main hM e α β hα hβ hαβ


end
