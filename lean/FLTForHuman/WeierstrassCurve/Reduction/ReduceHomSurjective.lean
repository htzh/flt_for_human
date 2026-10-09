/-
Surjectivity of reduction on the prime-to-`p` torsion (WORKORDER-W5-reducehom-surjective.md).

For a good-reduction model `W` of an elliptic curve over a valued field `L`, the reduction
map
`reduceHom hΔ : (W.map A.subtype).toAffine.Point →+ (W.map (residue A)).toAffine.Point`
is a bijection on `ℓ`-torsion whenever `ℓ` is invertible in the residue field; hence it is
surjective there.  This is the first half of story C of the Deligne–Serre route.

This module is the port of the pin's
`P2M/Sol/S_WeierstrassCurve_exists_reduceHom_eq_of_nsmul_eq_zero_of_natCast_ne_zero.lean`
(pinned `aa2d8b3`, 185 lines).  The pin's `main` (lines 106–172) is the engine: the
reduction map is injective on `ℓ`-torsion (`reduceHom_injOn'`, via
`X_mem_of_nsmul_eq_zero'` and `reducePoint_some_of_mem`), and a cardinality comparison of
the `ℓ`-torsion of `W` with that of the residue curve lifted along the algebraic closure
(`torsionMap`, `mapPointHom`) forces surjectivity.  The statement is the pin's
`Theorems/` wrapper verbatim; the pin's eight helpers stay `private` at the pin's leaf
names, so the headline is the module's only public declaration.

The pin's `import Mathlib`, its `attribute [-instance] …` / `attribute [-simp] …`
scaffolding (none of its names is in the port's cone) and its `maxHeartbeats` are not
transcribed.

Assumes, from the already-ported definition layer, imported and never redeclared:
`reduceHom`, `reducePoint`, `reducePoint_some_of_mem` (`Reduction/ReduceHom.lean`,
`Reduction/Point.lean`), `X_mem_of_nsmul_eq_zero'` (`Reduction/TorsionIntegral.lean`),
`map_residue_Δ_ne_zero_iff` (`Reduction/Point.lean`) and
`nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed` (`Elliptic/TorsionZMod.lean`).

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_exists_reduceHom_eq_of_nsmul_eq_zero_of_natCast_ne_zero.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_exists_reduceHom_eq_of_nsmul_eq_zero_of_natCast_ne_zero.lean>
-/
import FLTForHuman.Elliptic.TorsionZMod
import FLTForHuman.WeierstrassCurve.Reduction.ReduceHom

set_option autoImplicit false
-- The pin's `main` opens its local instances with `haveI`/`letI`; the port's newer
-- style linter would prefer `have`/`let` for a proposition goal, but the proof bodies
-- are transcribed verbatim.
set_option linter.style.haveILetI false

noncomputable section

open WeierstrassCurve IsLocalRing

namespace WeierstrassCurve

private theorem reduceHom_injOn' {L : Type*} [Field L] {A : ValuationSubring L}
    {W : WeierstrassCurve A} [DecidableEq L] [DecidableEq (ResidueField A)]
    (hΔ : (W.map (residue A)).Δ ≠ 0) {N : ℕ} (hN : (N : ResidueField A) ≠ 0)
    {P Q : (W.map A.subtype).toAffine.Point} (hP : N • P = 0) (hQ : N • Q = 0)
    (h : reduceHom hΔ P = reduceHom hΔ Q) : P = Q := by
  have h1 : N • (P - Q) = 0 := by rw [nsmul_sub, hP, hQ, sub_zero]
  have h2 : reducePoint hΔ (P - Q) = 0 := by
    show reduceHom hΔ (P - Q) = 0
    rw [map_sub, h, sub_self]
  have key : P - Q = 0 := by
    generalize hR : P - Q = R at h1 h2
    cases R with
    | zero => rfl
    | some x y hxy =>
      exfalso
      have hx : x ∈ A := X_mem_of_nsmul_eq_zero' W hN hxy h1
      rw [reducePoint_some_of_mem hΔ hxy hx] at h2
      exact Affine.Point.some_ne_zero _ h2
  exact sub_eq_zero.mp key

private def mapPointFun {F F' : Type*} [Field F] [Field F'] (f : F →+* F')
    (V : WeierstrassCurve F) : V.toAffine.Point → (V.map f).toAffine.Point
  | .zero => .zero
  | .some x y h => .some (f x) (f y) ((V.toAffine.map_nonsingular f.injective x y).mpr h)

private theorem mapPointFun_add {F F' : Type*} [Field F] [Field F'] [DecidableEq F]
    [DecidableEq F'] (f : F →+* F') (V : WeierstrassCurve F) (P Q : V.toAffine.Point) :
    mapPointFun f V (P + Q) = mapPointFun f V P + mapPointFun f V Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  any_goals rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = V.toAffine.negY x₂ y₂
  · rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2]
    show (Affine.Point.zero : (V.map f).toAffine.Point) =
      Affine.Point.some _ _ _ + Affine.Point.some _ _ _
    rw [Affine.Point.add_of_Y_eq (congrArg f hxy.1) (by rw [hxy.2, Affine.map_negY])]
    rfl
  · have hxy' : ¬(f x₁ = f x₂ ∧ f y₁ = (V.map f).toAffine.negY (f x₂) (f y₂)) := by
      rintro ⟨hx, hy⟩
      rw [Affine.map_negY] at hy
      exact hxy ⟨f.injective hx, f.injective hy⟩
    rw [Affine.Point.add_some hxy]
    show Affine.Point.some _ _ _ = Affine.Point.some _ _ _ + Affine.Point.some _ _ _
    rw [Affine.Point.add_some hxy']
    congr 1
    · rw [Affine.map_slope, Affine.map_addX]
    · rw [Affine.map_slope, Affine.map_addY]

private def mapPointHom {F F' : Type*} [Field F] [Field F'] [DecidableEq F] [DecidableEq F']
    (f : F →+* F') (V : WeierstrassCurve F) : V.toAffine.Point →+ (V.map f).toAffine.Point where
  toFun := mapPointFun f V
  map_zero' := rfl
  map_add' := mapPointFun_add f V

private theorem mapPointHom_injective {F F' : Type*} [Field F] [Field F'] [DecidableEq F]
    [DecidableEq F'] (f : F →+* F') (V : WeierstrassCurve F) :
    Function.Injective (mapPointHom f V) := by
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · exact absurd h.symm (Affine.Point.some_ne_zero _)
  · exact absurd h (Affine.Point.some_ne_zero _)
  · have h' : (Affine.Point.some (f x₁) (f y₁) _ : (V.map f).toAffine.Point) =
        Affine.Point.some (f x₂) (f y₂) _ := h
    rw [Affine.Point.some.injEq] at h'
    obtain ⟨hx, hy⟩ := h'
    have hx' := f.injective hx; have hy' := f.injective hy
    subst hx'; subst hy'; rfl

private def torsionMap {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (g : G →+ G')
    (n : ℕ) : Submodule.torsionBy ℤ G (n : ℤ) → Submodule.torsionBy ℤ G' (n : ℤ) :=
  fun P => ⟨g P, by
    have hP := P.2
    rw [Submodule.mem_torsionBy_iff] at hP ⊢
    rw [← map_zsmul, hP, map_zero]⟩

private theorem torsionMap_injective {G G' : Type*} [AddCommGroup G] [AddCommGroup G']
    (g : G →+ G') (n : ℕ)
    (hg : ∀ ⦃P Q : G⦄, n • P = 0 → n • Q = 0 → g P = g Q → P = Q) :
    Function.Injective (torsionMap g n) := by
  intro P Q h
  apply Subtype.ext
  have hP := P.2; have hQ := Q.2
  rw [Submodule.mem_torsionBy_iff, natCast_zsmul] at hP hQ
  exact hg hP hQ (congrArg Subtype.val h)

private theorem main {L : Type*} [Field L] [DecidableEq L] {A : ValuationSubring L}
    [DecidableEq (ResidueField A)] {W : WeierstrassCurve A} [IsAlgClosed L] [CharZero L]
    (hΔ : (W.map (residue A)).Δ ≠ 0)
    {ℓ : ℕ} (hℓ : (ℓ : ResidueField A) ≠ 0)
    (Q₀ : (W.map (residue A)).toAffine.Point) (hQ₀ : ℓ • Q₀ = 0) :
    ∃ Q : (W.map A.subtype).toAffine.Point, ℓ • Q = 0 ∧ reduceHom hΔ Q = Q₀ := by
  letI : DecidableEq (AlgebraicClosure (ResidueField A)) := Classical.decEq _
  haveI hEA : W.IsElliptic := ⟨(map_residue_Δ_ne_zero_iff W).mp hΔ⟩

  have hunit : IsUnit W.Δ := (map_residue_Δ_ne_zero_iff W).mp hΔ
  haveI hEL : (W.map A.subtype).IsElliptic := by
    refine ⟨?_⟩
    rw [WeierstrassCurve.map_Δ]
    exact (hunit.map A.subtype)
  haveI hEk : (W.map (residue A)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩

  let ι : ResidueField A →+* AlgebraicClosure (ResidueField A) :=
    algebraMap (ResidueField A) (AlgebraicClosure (ResidueField A))
  haveI hEkbar : ((W.map (residue A)).map ι).IsElliptic := by
    refine ⟨?_⟩; rw [WeierstrassCurve.map_Δ]; exact hEk.isUnit.map ι

  have hℓL : (ℓ : L) ≠ 0 := by
    intro h
    apply hℓ
    have : (ℓ : ResidueField A) = residue A (ℓ : A) := by simp
    rw [this]
    have hA : ((ℓ : A) : L) = 0 := by exact_mod_cast h
    have : (ℓ : A) = 0 := Subtype.ext hA
    rw [this, map_zero]
  have hℓk : (ℓ : AlgebraicClosure (ResidueField A)) ≠ 0 := by
    rw [← map_natCast ι]; exact (map_ne_zero ι).mpr hℓ

  have hZ : Nat.card (ZMod ℓ × ZMod ℓ) = ℓ ^ 2 := by
    rw [Nat.card_prod, Nat.card_zmod, sq]
  have hcL : Nat.card (Submodule.torsionBy ℤ (W.map A.subtype).toAffine.Point (ℓ : ℤ)) =
      ℓ ^ 2 := by
    obtain ⟨e⟩ := WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
      (F := L) (K := L) (W.map A.subtype) hℓL
    rw [← hZ]
    exact (Nat.card_congr e.toEquiv).symm
  have hck : Nat.card (Submodule.torsionBy ℤ ((W.map (residue A)).map ι).toAffine.Point (ℓ : ℤ))
      = ℓ ^ 2 := by
    obtain ⟨e⟩ := WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
      (F := ResidueField A) (K := AlgebraicClosure (ResidueField A)) (W.map (residue A)) hℓk
    rw [← hZ]
    exact (Nat.card_congr e.toEquiv).symm

  let r := torsionMap (reduceHom hΔ) ℓ
  let m := torsionMap (mapPointHom ι (W.map (residue A))) ℓ
  have hr : Function.Injective r :=
    torsionMap_injective _ _ (fun P Q hP hQ h => reduceHom_injOn' hΔ hℓ hP hQ h)
  have hm : Function.Injective m :=
    torsionMap_injective _ _ (fun P Q _ _ h => mapPointHom_injective ι _ h)

  have hℓ0 : ℓ ≠ 0 := by rintro rfl; exact hℓ (by simp)
  haveI : Finite (Submodule.torsionBy ℤ ((W.map (residue A)).map ι).toAffine.Point (ℓ : ℤ)) :=
    Nat.finite_of_card_ne_zero (by rw [hck]; exact pow_ne_zero _ hℓ0)
  have hmr : Function.Bijective (m ∘ r) :=
    (hm.comp hr).bijective_of_nat_card_le (by rw [hcL, hck])

  have hrs : Function.Surjective r := by
    intro y
    obtain ⟨x, hx⟩ := hmr.2 (m y)
    exact ⟨x, hm hx⟩
  obtain ⟨P, hP⟩ := hrs ⟨Q₀, by rw [Submodule.mem_torsionBy_iff, natCast_zsmul]; exact hQ₀⟩
  refine ⟨P.1, ?_, congrArg Subtype.val hP⟩
  have := P.2
  rw [Submodule.mem_torsionBy_iff, natCast_zsmul] at this
  exact this

/-- **Surjectivity of reduction on the prime-to-`p` torsion.** If `W` is a Weierstrass
model over a valuation ring `A ⊆ L` whose reduction is smooth (`hΔ`), then every
`ℓ`-torsion point of the residue curve with `ℓ` invertible in the residue field lifts
to an `ℓ`-torsion point of `W`. The pin
`WeierstrassCurve.exists_reduceHom_eq_of_nsmul_eq_zero_of_natCast_ne_zero` verbatim. -/
theorem exists_reduceHom_eq_of_nsmul_eq_zero_of_natCast_ne_zero
    {L : Type*} [Field L] [DecidableEq L] [IsAlgClosed L] [CharZero L]
    (A : ValuationSubring L) [DecidableEq (ResidueField A)]
    (W : WeierstrassCurve A) (hΔ : (W.map (residue A)).Δ ≠ 0)
    {ℓ : ℕ} (hℓ : (ℓ : ResidueField A) ≠ 0)
    (Q₀ : (W.map (residue A)).toAffine.Point) (hQ₀ : ℓ • Q₀ = 0) :
    ∃ Q : (W.map A.subtype).toAffine.Point, ℓ • Q = 0 ∧ reduceHom hΔ Q = Q₀ :=
  main hΔ hℓ Q₀ hQ₀

end WeierstrassCurve
