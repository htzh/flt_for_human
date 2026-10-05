/-
The ψ-counting lemmas and the cyclic-kernel enumeration (V1-SET-2).

Statements are transcribed verbatim from the pinned wrappers

* `Theorems/Thm_ZMod_natCard_isAddCyclic_addSubgroup_prod_eq_dedekindPsi.lean`,
* `Theorems/Thm_AddCommGroup_natCard_isAddCyclic_addSubgroup_eq_dedekindPsi_of_addEquiv_torsionBy.lean`,
* `Theorems/Thm_WeierstrassCurve_exists_enum_cyclicKernels_veluQuotient_discriminant_ne_zero.lean`,

and their proofs from the matching `P2M/Sol/S_*.lean` bodies (adapted to mathlib
`v4.34.0`).  The `ZMod` count routes through the port's promoted
`ModularCurve.card_projectiveLine_zmod` (`ModularCurve/Gamma0Index.lean`) — the
pin's route too — and the `AddCommGroup` count transports it along the torsion
classification; the enumeration consumes this set's
`veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq`.

All helpers of the two counting `S_` files are `private`: the pin re-exports them
into its `P2MW` namespace via `p2m_export`, but no `Theorems/` wrapper carries
them, so they are proof-local from the checker's point of view.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ZMod_natCard_isAddCyclic_addSubgroup_prod_eq_dedekindPsi.lean>
-/
import FLTForHuman.WeierstrassCurve.Velu.Discriminant
import FLTForHuman.Algebra.ZModTorsion
import FLTForHuman.Elliptic.TorsionZMod
import FLTForHuman.ModularCurve.Gamma0Index

set_option autoImplicit false

noncomputable section

open AddSubgroup

/-! ### `ZMod.natCard_isAddCyclic_addSubgroup_prod_eq_dedekindPsi`

The `ℙ¹(ℤ/n)` route: cyclic subgroups of `(ℤ/n)²` of order `n` are exactly the
lines. -/




namespace ModularCurve

open AddSubgroup

section OrderUnimodular

variable (N : ℕ)

private theorem nsmul_pair (n : ℕ) (x : ZMod N × ZMod N) :
    n • x = (n • x.1, n • x.2) :=
  Prod.ext (map_nsmul (AddMonoidHom.fst (ZMod N) (ZMod N)) n x)
    (map_nsmul (AddMonoidHom.snd (ZMod N) (ZMod N)) n x)

private theorem zsmul_pair_fst (k : ℤ) (x : ZMod N × ZMod N) :
    (k • x).1 = k • x.1 :=
  map_zsmul (AddMonoidHom.fst (ZMod N) (ZMod N)) k x

private theorem zsmul_pair_snd (k : ℤ) (x : ZMod N × ZMod N) :
    (k • x).2 = k • x.2 :=
  map_zsmul (AddMonoidHom.snd (ZMod N) (ZMod N)) k x

private theorem nsmul_eq_zero_of_dvd_mul_val {m : ℕ} {z : ZMod N} [NeZero N]
    (h : N ∣ m * z.val) : m • z = 0 :=
  calc m • z = (m : ZMod N) * z := nsmul_eq_mul m z
    _ = (m : ZMod N) * (z.val : ZMod N) := by rw [ZMod.natCast_zmod_val]
    _ = ((m * z.val : ℕ) : ZMod N) := (Nat.cast_mul _ _).symm
    _ = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h

variable [NeZero N]

omit [NeZero N] in

private theorem IsUnimodularRow.addOrderOf_eq {a c : ZMod N} (h : IsUnimodularRow a c) :
    addOrderOf ((a, c) : ZMod N × ZMod N) = N := by
  obtain ⟨x, y, hxy⟩ := h

  have hdvdN : addOrderOf ((a, c) : ZMod N × ZMod N) ∣ N := by
    refine addOrderOf_dvd_iff_nsmul_eq_zero.mpr ?_
    rw [nsmul_pair]
    have hza : N • a = 0 := by rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    have hzc : N • c = 0 := by rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    rw [hza, hzc]
    rfl

  have hN : N ∣ addOrderOf ((a, c) : ZMod N × ZMod N) := by
    have hsmul : addOrderOf ((a, c) : ZMod N × ZMod N) • ((a, c) : ZMod N × ZMod N) = 0 :=
      addOrderOf_nsmul_eq_zero _
    rw [nsmul_pair] at hsmul
    have ha : addOrderOf ((a, c) : ZMod N × ZMod N) • a = 0 := congrArg Prod.fst hsmul
    have hc : addOrderOf ((a, c) : ZMod N × ZMod N) • c = 0 := congrArg Prod.snd hsmul
    rw [nsmul_eq_mul] at ha hc
    have hzero : ((addOrderOf ((a, c) : ZMod N × ZMod N) : ℕ) : ZMod N) = 0 := by
      calc ((addOrderOf ((a, c) : ZMod N × ZMod N) : ℕ) : ZMod N)
          = (addOrderOf ((a, c) : ZMod N × ZMod N) : ZMod N) * (x * a + y * c) := by
            rw [hxy, mul_one]
        _ = x * ((addOrderOf ((a, c) : ZMod N × ZMod N) : ZMod N) * a)
              + y * ((addOrderOf ((a, c) : ZMod N × ZMod N) : ZMod N) * c) := by ring
        _ = 0 := by rw [ha, hc, mul_zero, mul_zero, add_zero]
    exact (ZMod.natCast_eq_zero_iff _ _).mp hzero
  exact Nat.dvd_antisymm hdvdN hN

private theorem isUnimodularRow_of_addOrderOf_eq {a c : ZMod N}
    (h : addOrderOf ((a, c) : ZMod N × ZMod N) = N) : IsUnimodularRow a c := by
  have hN0 : N ≠ 0 := NeZero.ne N
  set d : ℕ := Nat.gcd (Nat.gcd a.val c.val) N with hd
  have hdN : d ∣ N := Nat.gcd_dvd_right _ _
  have hdA : d ∣ a.val := dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _)
  have hdC : d ∣ c.val := dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)

  have hd1 : d = 1 := by
    have hkill : (N / d) • ((a, c) : ZMod N × ZMod N) = 0 := by
      rw [nsmul_pair]
      have hka : (N / d) • a = 0 := by
        refine nsmul_eq_zero_of_dvd_mul_val N ?_
        obtain ⟨A', hA'⟩ := hdA
        exact ⟨A', by rw [hA', ← mul_assoc, Nat.div_mul_cancel hdN]⟩
      have hkc : (N / d) • c = 0 := by
        refine nsmul_eq_zero_of_dvd_mul_val N ?_
        obtain ⟨C', hC'⟩ := hdC
        exact ⟨C', by rw [hC', ← mul_assoc, Nat.div_mul_cancel hdN]⟩
      rw [hka, hkc]
      rfl
    have horder : addOrderOf ((a, c) : ZMod N × ZMod N) ∣ N / d :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr hkill
    rw [h] at horder
    have hdivdvd : N / d ∣ N := Nat.div_dvd_of_dvd hdN
    have hNd : N / d = N := Nat.dvd_antisymm hdivdvd horder
    have hmul : d * (N / d) = N := Nat.mul_div_cancel' hdN
    rw [hNd] at hmul
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hN0) (hmul.trans (one_mul N).symm)

  have hcop : Nat.Coprime (Nat.gcd a.val c.val) N := hd1
  have hunit : IsUnit ((Nat.gcd a.val c.val : ℕ) : ZMod N) :=
    (ZMod.isUnit_iff_coprime _ N).mpr hcop
  obtain ⟨u, hu⟩ := hunit
  have hbez := Nat.gcd_eq_gcd_ab a.val c.val
  have hcast : ((Nat.gcd a.val c.val : ℕ) : ZMod N)
      = a * ((Nat.gcdA a.val c.val : ℤ) : ZMod N) + c * ((Nat.gcdB a.val c.val : ℤ) : ZMod N) := by
    have hℤ := congrArg (fun z : ℤ => (Int.castRingHom (ZMod N)) z) hbez
    simp only [map_add, map_mul, Int.coe_castRingHom] at hℤ
    rw [Int.cast_natCast, Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val] at hℤ
    exact hℤ
  refine ⟨((Nat.gcdA a.val c.val : ℤ) : ZMod N) * (↑u⁻¹ : ZMod N),
    ((Nat.gcdB a.val c.val : ℤ) : ZMod N) * (↑u⁻¹ : ZMod N), ?_⟩
  calc ((Nat.gcdA a.val c.val : ℤ) : ZMod N) * (↑u⁻¹ : ZMod N) * a
        + ((Nat.gcdB a.val c.val : ℤ) : ZMod N) * (↑u⁻¹ : ZMod N) * c
      = (a * ((Nat.gcdA a.val c.val : ℤ) : ZMod N)
          + c * ((Nat.gcdB a.val c.val : ℤ) : ZMod N)) * (↑u⁻¹ : ZMod N) := by ring
    _ = ((Nat.gcd a.val c.val : ℕ) : ZMod N) * (↑u⁻¹ : ZMod N) := by rw [← hcast]
    _ = (↑u : ZMod N) * (↑u⁻¹ : ZMod N) := by rw [hu]
    _ = 1 := u.mul_inv

private theorem isUnimodularRow_iff_addOrderOf_eq {a c : ZMod N} :
    IsUnimodularRow a c ↔ addOrderOf ((a, c) : ZMod N × ZMod N) = N :=
  ⟨IsUnimodularRow.addOrderOf_eq N, isUnimodularRow_of_addOrderOf_eq N⟩

end OrderUnimodular

section Scaling

variable (N : ℕ) [NeZero N]

private theorem zmultiples_unit_mul (u : (ZMod N)ˣ) (x : ZMod N × ZMod N) :
    AddSubgroup.zmultiples ((((u : ZMod N) * x.1, (u : ZMod N) * x.2)) : ZMod N × ZMod N)
      = AddSubgroup.zmultiples x := by
  have key : ∀ (w : (ZMod N)ˣ) (y : ZMod N × ZMod N),
      (((w : ZMod N) * y.1, (w : ZMod N) * y.2) : ZMod N × ZMod N) ∈ AddSubgroup.zmultiples y := by
    intro w y
    refine AddSubgroup.mem_zmultiples_iff.mpr ⟨((w : ZMod N).val : ℤ), ?_⟩
    refine Prod.ext ?_ ?_
    · show ((((w : ZMod N).val : ℤ)) • y).1 = (w : ZMod N) * y.1
      rw [zsmul_pair_fst, zsmul_eq_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
    · show ((((w : ZMod N).val : ℤ)) • y).2 = (w : ZMod N) * y.2
      rw [zsmul_pair_snd, zsmul_eq_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
  refine le_antisymm (AddSubgroup.zmultiples_le.mpr (key u x)) (AddSubgroup.zmultiples_le.mpr ?_)

  have hmem := key u⁻¹ (((u : ZMod N) * x.1, (u : ZMod N) * x.2) : ZMod N × ZMod N)
  have hx : ((((u⁻¹ : (ZMod N)ˣ) : ZMod N) * (((u : ZMod N) * x.1, (u : ZMod N) * x.2) : ZMod N × ZMod N).1,
      ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * (((u : ZMod N) * x.1, (u : ZMod N) * x.2) : ZMod N × ZMod N).2)
        : ZMod N × ZMod N) = x := by
    have h1 : ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * ((u : ZMod N) * x.1) = x.1 := by
      rw [← mul_assoc, u.inv_mul, one_mul]
    have h2 : ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * ((u : ZMod N) * x.2) = x.2 := by
      rw [← mul_assoc, u.inv_mul, one_mul]
    exact Prod.ext h1 h2
  rwa [hx] at hmem

omit [NeZero N] in

private theorem eq_of_mul_unimodularRow_eq {a c : ZMod N} (h : IsUnimodularRow a c) {r s : ZMod N}
    (h1 : r * a = s * a) (h2 : r * c = s * c) : r = s := by
  obtain ⟨x, y, hxy⟩ := h
  calc r = r * (x * a + y * c) := by rw [hxy, mul_one]
    _ = x * (r * a) + y * (r * c) := by ring
    _ = x * (s * a) + y * (s * c) := by rw [h1, h2]
    _ = s * (x * a + y * c) := by ring
    _ = s := by rw [hxy, mul_one]

omit [NeZero N] in

private theorem IsUnimodularRow.unit_mul {a c : ZMod N} (h : IsUnimodularRow a c) (u : (ZMod N)ˣ) :
    IsUnimodularRow ((u : ZMod N) * a) ((u : ZMod N) * c) := by
  obtain ⟨x, y, hxy⟩ := h
  refine ⟨x * ((u⁻¹ : (ZMod N)ˣ) : ZMod N), y * ((u⁻¹ : (ZMod N)ˣ) : ZMod N), ?_⟩
  calc x * ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * ((u : ZMod N) * a)
        + y * ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * ((u : ZMod N) * c)
      = (((u⁻¹ : (ZMod N)ˣ) : ZMod N) * (u : ZMod N)) * (x * a)
          + (((u⁻¹ : (ZMod N)ˣ) : ZMod N) * (u : ZMod N)) * (y * c) := by ring
    _ = x * a + y * c := by rw [u.inv_mul, one_mul, one_mul]
    _ = 1 := hxy

end Scaling

section Bijection

variable (N : ℕ) [NeZero N]

private def unimodularRowToCyclicAddSubgroup (v : UnimodularRow (ZMod N)) :
    {H : AddSubgroup (ZMod N × ZMod N) // IsAddCyclic H ∧ Nat.card H = N} :=
  ⟨AddSubgroup.zmultiples v.1,
    (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top _).mpr ⟨v.1, rfl⟩,
    by rw [Nat.card_zmultiples, IsUnimodularRow.addOrderOf_eq N v.2]⟩

private def projectiveLineToCyclicAddSubgroup :
    ProjectiveLine (ZMod N) → {H : AddSubgroup (ZMod N × ZMod N) // IsAddCyclic H ∧ Nat.card H = N} :=
  Quotient.lift (unimodularRowToCyclicAddSubgroup N) <| by
    rintro v w ⟨u, h1, h2⟩
    refine Subtype.ext ?_
    show AddSubgroup.zmultiples v.1 = AddSubgroup.zmultiples w.1
    have hw : w.1 = (((u : ZMod N) * v.1.1, (u : ZMod N) * v.1.2) : ZMod N × ZMod N) := by
      rw [h1, h2]
    rw [hw, zmultiples_unit_mul]

@[scoped simp]
private theorem projectiveLineToCyclicAddSubgroup_mk (v : UnimodularRow (ZMod N)) :
    projectiveLineToCyclicAddSubgroup N ⟦v⟧ = unimodularRowToCyclicAddSubgroup N v :=
  rfl

private theorem projectiveLineToCyclicAddSubgroup_injective :
    Function.Injective (projectiveLineToCyclicAddSubgroup N) := by
  intro q₁ q₂
  refine Quotient.inductionOn₂ q₁ q₂ ?_
  intro v w hvw
  have hsub : AddSubgroup.zmultiples v.1 = AddSubgroup.zmultiples w.1 :=
    congrArg Subtype.val hvw

  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp
    (hsub ▸ AddSubgroup.mem_zmultiples w.1)

  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp
    (hsub.symm ▸ AddSubgroup.mem_zmultiples v.1)
  have hk1 : ((k : ZMod N)) * v.1.1 = w.1.1 := by
    have h := congrArg Prod.fst hk; rwa [zsmul_pair_fst, zsmul_eq_mul] at h
  have hk2 : ((k : ZMod N)) * v.1.2 = w.1.2 := by
    have h := congrArg Prod.snd hk; rwa [zsmul_pair_snd, zsmul_eq_mul] at h
  have hm1 : ((m : ZMod N)) * w.1.1 = v.1.1 := by
    have h := congrArg Prod.fst hm; rwa [zsmul_pair_fst, zsmul_eq_mul] at h
  have hm2 : ((m : ZMod N)) * w.1.2 = v.1.2 := by
    have h := congrArg Prod.snd hm; rwa [zsmul_pair_snd, zsmul_eq_mul] at h

  have hmk : ((m : ZMod N)) * ((k : ZMod N)) = 1 := by
    refine eq_of_mul_unimodularRow_eq N v.2 ?_ ?_
    · rw [mul_assoc, hk1, hm1, one_mul]
    · rw [mul_assoc, hk2, hm2, one_mul]
  refine Quotient.sound ⟨⟨(k : ZMod N), (m : ZMod N), by rw [mul_comm]; exact hmk, hmk⟩, ?_, ?_⟩
  · exact hk1
  · exact hk2

private theorem projectiveLineToCyclicAddSubgroup_surjective :
    Function.Surjective (projectiveLineToCyclicAddSubgroup N) := by
  rintro ⟨H, hcyc, hcard⟩
  obtain ⟨g, hg⟩ := (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top H).mp hcyc
  have horder : addOrderOf g = N := by
    have := Nat.card_zmultiples g
    rw [hg, hcard] at this
    exact this.symm
  have hrow : IsUnimodularRow g.1 g.2 := by
    refine isUnimodularRow_of_addOrderOf_eq N ?_
    have hg' : ((g.1, g.2) : ZMod N × ZMod N) = g := rfl
    rw [hg', horder]
  refine ⟨⟦⟨(g.1, g.2), hrow⟩⟧, ?_⟩
  refine Subtype.ext ?_
  show AddSubgroup.zmultiples ((g.1, g.2) : ZMod N × ZMod N) = H
  have hg' : ((g.1, g.2) : ZMod N × ZMod N) = g := rfl
  rw [hg', hg]

private def projectiveLineEquivCyclicAddSubgroup :
    ProjectiveLine (ZMod N) ≃ {H : AddSubgroup (ZMod N × ZMod N) // IsAddCyclic H ∧ Nat.card H = N} :=
  Equiv.ofBijective (projectiveLineToCyclicAddSubgroup N)
    ⟨projectiveLineToCyclicAddSubgroup_injective N, projectiveLineToCyclicAddSubgroup_surjective N⟩

end Bijection

section Headline

variable (N : ℕ) [NeZero N]

private theorem card_cyclicAddSubgroup_eq_card_projectiveLine :
    Nat.card {H : AddSubgroup (ZMod N × ZMod N) // IsAddCyclic H ∧ Nat.card H = N}
      = Nat.card (ProjectiveLine (ZMod N)) :=
  (Nat.card_congr (projectiveLineEquivCyclicAddSubgroup N)).symm

private theorem card_cyclicAddSubgroup_eq_dedekindPsi :
    Nat.card {H : AddSubgroup (ZMod N × ZMod N) // IsAddCyclic H ∧ Nat.card H = N}
      = dedekindPsi N := by
  rw [card_cyclicAddSubgroup_eq_card_projectiveLine,
    card_projectiveLine_zmod N (NeZero.ne N)]

end Headline

end ModularCurve

namespace ZMod

theorem natCard_isAddCyclic_addSubgroup_prod_eq_dedekindPsi
    (n : ℕ) [NeZero n] :
    Nat.card {H : AddSubgroup (ZMod n × ZMod n) // IsAddCyclic H ∧ Nat.card H = n} = ModularCurve.dedekindPsi n :=
  ModularCurve.card_cyclicAddSubgroup_eq_dedekindPsi n

end ZMod


/-! ### `AddCommGroup.natCard_isAddCyclic_addSubgroup_eq_dedekindPsi_of_addEquiv_torsionBy`

Transport along the torsion classification of `Algebra/ZModTorsion.lean`. -/



namespace Transport

open AddSubgroup

variable (N : ℕ) {E A : Type*} [AddCommGroup E] [AddCommGroup A]

private theorem isAddCyclic_map_and_card_of_injective (f : A →+ E) (hf : Function.Injective f)
    {K : AddSubgroup A} (h : IsAddCyclic K ∧ Nat.card K = N) :
    IsAddCyclic (K.map f) ∧ Nat.card (K.map f) = N ∧ K.map f ≤ f.range := by
  obtain ⟨h1, h2⟩ := h
  haveI : IsAddCyclic K := h1
  refine ⟨?_, ?_, AddSubgroup.map_le_range f K⟩
  · exact isAddCyclic_of_surjective (K.equivMapOfInjective f hf)
      (K.equivMapOfInjective f hf).surjective
  · rw [← Nat.card_congr (K.equivMapOfInjective f hf).toEquiv, h2]

private theorem isAddCyclic_comap_and_card_of_le_range (f : A →+ E) (hf : Function.Injective f)
    {H : AddSubgroup E} (hcyc : IsAddCyclic H) (hcard : Nat.card H = N) (hle : H ≤ f.range) :
    IsAddCyclic (H.comap f) ∧ Nat.card (H.comap f) = N := by
  have hKmap : (H.comap f).map f = H := AddSubgroup.map_comap_eq_self hle
  rw [← hKmap] at hcyc hcard
  haveI : IsAddCyclic ((H.comap f).map f) := hcyc
  constructor
  · exact isAddCyclic_of_surjective ((H.comap f).equivMapOfInjective f hf).symm
      ((H.comap f).equivMapOfInjective f hf).symm.surjective
  · exact (Nat.card_congr ((H.comap f).equivMapOfInjective f hf).toEquiv).trans hcard

private def cyclicAddSubgroupMapEquiv (f : A →+ E) (hf : Function.Injective f) :
    {C : AddSubgroup A // IsAddCyclic C ∧ Nat.card C = N} ≃
      {H : AddSubgroup E // IsAddCyclic H ∧ Nat.card H = N ∧ H ≤ f.range} where
  toFun C := ⟨C.1.map f, isAddCyclic_map_and_card_of_injective N f hf C.2⟩
  invFun H := ⟨H.1.comap f,
    isAddCyclic_comap_and_card_of_le_range N f hf H.2.1 H.2.2.1 H.2.2.2⟩
  left_inv C := Subtype.ext (by
    show (C.1.map f).comap f = C.1
    exact AddSubgroup.comap_map_eq_self_of_injective hf C.1)
  right_inv H := Subtype.ext (by
    show (H.1.comap f).map f = H.1
    exact AddSubgroup.map_comap_eq_self H.2.2.2)

private theorem le_of_card_eq_of_nsmul_mem {H T : AddSubgroup E} (hcard : Nat.card H = N)
    (hT : ∀ x : E, N • x = 0 → x ∈ T) : H ≤ T := by
  intro x hx
  refine hT x (addOrderOf_dvd_iff_nsmul_eq_zero.mp ?_)
  rw [← hcard]
  exact AddSubgroup.addOrderOf_dvd_natCard H hx

end Transport

namespace AddCommGroup

theorem natCard_isAddCyclic_addSubgroup_eq_dedekindPsi_of_addEquiv_torsionBy
    (n : ℕ) [NeZero n] {A : Type*} [AddCommGroup A]
    (e : ZMod n × ZMod n ≃+ Submodule.torsionBy ℤ A n) :
    Nat.card {H : AddSubgroup A // IsAddCyclic H ∧ Nat.card H = n} = ModularCurve.dedekindPsi n := by

  let ι : ZMod n × ZMod n →+ A :=
    ((Submodule.torsionBy ℤ A n).toAddSubgroup.subtype).comp e.toAddMonoidHom
  have hι : Function.Injective ι :=
    (Submodule.torsionBy ℤ A n).toAddSubgroup.subtype_injective.comp e.injective
  have hrange : ∀ x : A, n • x = 0 → x ∈ ι.range := by
    intro x hx
    have hx' : x ∈ Submodule.torsionBy ℤ A n := by
      rw [Submodule.mem_torsionBy_iff, natCast_zsmul]; exact hx
    refine ⟨e.symm ⟨x, hx'⟩, ?_⟩
    simp [ι]

  rw [← ZMod.natCard_isAddCyclic_addSubgroup_prod_eq_dedekindPsi n,
    Nat.card_congr (Transport.cyclicAddSubgroupMapEquiv n ι hι)]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun H => ?_)
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2, Transport.le_of_card_eq_of_nsmul_mem n h2 hrange⟩
  · rintro ⟨h1, h2, -⟩
    exact ⟨h1, h2⟩

end AddCommGroup


/-! ### `exists_enum_cyclicKernels_veluQuotient_discriminant_ne_zero`

The `ℓ + 1` cyclic kernels of order `ℓ` on an elliptic curve over an
algebraically closed field, all with nonsingular Vélu quotient. -/



open WeierstrassCurve WeierstrassCurve.Affine

namespace WeierstrassCurve

theorem exists_enum_cyclicKernels_veluQuotient_discriminant_ne_zero
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hℓK : (ℓ : K) ≠ 0)
    (W : WeierstrassCurve K) [W.IsElliptic] :
    ∃ (ι : Type) (_ : Fintype ι), Fintype.card ι = ℓ + 1 ∧
      ∃ Q : ι → W.toAffine.Point, (∀ i, addOrderOf (Q i) = ℓ) ∧
        (Function.Injective fun i => AddSubgroup.zmultiples (Q i)) ∧
        ∀ i, (W.veluQuotient (W.oddOrderSummingSet (Q i) (ℓ / 2))).Δ ≠ 0 := by
  have hℓP : ℓ.Prime := Fact.out

  obtain ⟨e⟩ := WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
    (F := K) (K := K) W (n := ℓ) hℓK
  have hb : W.baseChange K = W := by cases W; rfl
  have htrans : ∀ (V : WeierstrassCurve K), V = W →
      (ZMod ℓ × ZMod ℓ ≃+ Submodule.torsionBy ℤ V.toAffine.Point ℓ) →
      Nonempty (ZMod ℓ × ZMod ℓ ≃+ Submodule.torsionBy ℤ W.toAffine.Point ℓ) := by
    intro V h e'; subst h; exact ⟨e'⟩
  obtain ⟨e⟩ := htrans _ hb e

  have hcard :=
    AddCommGroup.natCard_isAddCyclic_addSubgroup_eq_dedekindPsi_of_addEquiv_torsionBy ℓ e
  rw [ModularCurve.dedekindPsi_prime hℓP] at hcard
  set ι := {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = ℓ} with hιdef
  haveI : Finite ι := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  letI : Fintype ι := Fintype.ofFinite ι
  have hι : Fintype.card ι = ℓ + 1 := by rw [← Nat.card_eq_fintype_card, hcard]

  have hgen : ∀ H : ι, ∃ g : W.toAffine.Point,
      addOrderOf g = ℓ ∧ AddSubgroup.zmultiples g = H.1 := by
    rintro ⟨H, hcyc, hcardH⟩
    obtain ⟨g, hg⟩ := (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top H).mp hcyc
    refine ⟨g, ?_, hg⟩
    rw [← Nat.card_zmultiples g, hg]; exact hcardH
  choose Q hQord hQgen using hgen
  have hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i) := by
    intro i i' h
    apply Subtype.ext
    simp only at h
    rw [← hQgen i, ← hQgen i', h]

  have hodd : ∀ i, addOrderOf (Q i) = 2 * (ℓ / 2) + 1 := by
    intro i
    rw [hQord i]
    rcases hℓP.eq_two_or_odd' with h | h
    · exact absurd h hℓ2
    · exact (Nat.two_mul_div_two_add_one_of_odd h).symm
  have hΔ : ∀ i, (W.veluQuotient (W.oddOrderSummingSet (Q i) (ℓ / 2))).Δ ≠ 0 := fun i =>
    WeierstrassCurve.veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq
      W (ℓ / 2) (Q i) (hodd i)

  let f : Fin (ℓ + 1) ≃ ι := (Fintype.equivFinOfCardEq hι).symm
  exact ⟨Fin (ℓ + 1), inferInstance, Fintype.card_fin _, fun k => Q (f k), fun k => hQord _,
    fun k k' h => f.injective (hQinj h), fun k => hΔ _⟩

end WeierstrassCurve
