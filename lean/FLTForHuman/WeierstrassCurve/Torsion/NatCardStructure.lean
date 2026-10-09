/-
The count-`N²` structure theorem for the `N`-torsion of a Weierstrass curve over a
field that already carries all of it.

Statements are transcribed verbatim from the pinned FLT `aa2d8b3` wrapper
`Theorems/Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_natCard_torsion_eq_sq.lean`;
the proof follows
`P2M/Sol/S_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_natCard_torsion_eq_sq.lean`
(`torsionEquiv` at line 17, `main` at 24, `solution` at 63).  The pin's private
`torsionEquiv` and `main` stay `private` at the pin's leaf names; only the headline
is public.

The one premise is the already-ported
`WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed`
(`FLTForHuman/Elliptic/TorsionZMod.lean`), imported, never redeclared.  The pin's
`import Mathlib`, its `attribute [-instance] …` / `attribute [-simp] …` scaffolding
(names not in the port's cone) and its missing `set_option` list are not
transcribed.

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_natCard_torsion_eq_sq.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_natCard_torsion_eq_sq.lean>
-/
import FLTForHuman.Elliptic.TorsionZMod

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine

namespace WeierstrassCurve

/-- The pin's `torsionEquiv`: the `ℤ`-torsion submodule spelled as an `nsmul`-kernel. -/
private def torsionEquiv (A : Type*) [AddCommGroup A] (N : ℕ) :
    {P : A // N • P = 0} ≃ Submodule.torsionBy ℤ A N where
  toFun P := ⟨P.1, by rw [Submodule.mem_torsionBy_iff, natCast_zsmul]; exact P.2⟩
  invFun P := ⟨P.1, by have h := P.2; rw [Submodule.mem_torsionBy_iff, natCast_zsmul] at h; exact h⟩
  left_inv P := rfl
  right_inv P := rfl

private theorem main {k Ω : Type*} [Field k] [Field Ω] [DecidableEq Ω] [Algebra k Ω]
    (E : WeierstrassCurve k) [E.IsElliptic] (N : ℕ) [NeZero N] (hN : (N : k) ≠ 0)
    (hfull : Nat.card {P : (E.baseChange Ω).toAffine.Point // N • P = 0} = N ^ 2) :
    Nonempty (ZMod N × ZMod N ≃+ Submodule.torsionBy ℤ (E.baseChange Ω).toAffine.Point N) := by
  classical
  let Ωb := AlgebraicClosure Ω
  have hNb : (N : Ωb) ≠ 0 := fun h => hN ((algebraMap k Ωb).injective (by
    rw [map_natCast, map_zero]; exact h))
  obtain ⟨e₀⟩ := WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
    (K := Ωb) E hNb

  let ι : Ω →ₐ[k] Ωb := IsScalarTower.toAlgHom k Ω Ωb
  let f : (E.baseChange Ω).toAffine.Point →+ (E.baseChange Ωb).toAffine.Point := Point.map ι
  have hf : Function.Injective f := Point.map_injective ι
  let T := Submodule.torsionBy ℤ (E.baseChange Ω).toAffine.Point N
  let Tb := Submodule.torsionBy ℤ (E.baseChange Ωb).toAffine.Point N
  have hmem : ∀ P : T, f P.1 ∈ Tb := fun P => by
    have h := P.2
    rw [Submodule.mem_torsionBy_iff, natCast_zsmul] at h ⊢
    rw [← map_nsmul, h, map_zero]
  let g : T →+ Tb :=
    { toFun := fun P => ⟨f P.1, hmem P⟩
      map_zero' := by ext1; exact map_zero f
      map_add' := fun P Q => by ext1; exact map_add f P.1 Q.1 }
  have hg : Function.Injective g := fun P Q h => Subtype.ext (hf (congrArg Subtype.val h))

  have hT : Nat.card T = N ^ 2 := by rw [← hfull]; exact (Nat.card_congr (torsionEquiv _ N)).symm
  have hTb : Nat.card Tb = N ^ 2 := by
    rw [← Nat.card_congr e₀.toEquiv, Nat.card_prod, Nat.card_zmod, sq]
  have hTbfin : Finite Tb := Nat.finite_of_card_ne_zero (by rw [hTb]; exact pow_ne_zero 2 (NeZero.ne N))
  have hbij : Function.Bijective g :=
    @Function.Injective.bijective_of_nat_card_le T Tb hTbfin g hg (by rw [hT, hTb])
  exact ⟨e₀.trans (AddEquiv.ofBijective g hbij).symm⟩

/-- **The count-`N²` structure theorem.** If `N` is invertible in `k` and the base
change of `E` to `Ω` already carries all `N²` points of `E[N]`, then
`E(Ω)[N] ≅ (ℤ/N)²`. The pin
`WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_natCard_torsion_eq_sq`
verbatim. -/
theorem nonempty_torsionBy_addEquiv_zmod_prod_of_natCard_torsion_eq_sq
    {k Ω : Type*} [Field k] [Field Ω] [DecidableEq Ω] [Algebra k Ω] (E : WeierstrassCurve k)
    [E.IsElliptic] (N : ℕ) [NeZero N] (hN : (N : k) ≠ 0)
    (hfull : Nat.card {P : (E.baseChange Ω).toAffine.Point // N • P = 0} = N ^ 2) :
    Nonempty (ZMod N × ZMod N ≃+ Submodule.torsionBy ℤ (E.baseChange Ω).toAffine.Point N) :=
  main E N hN hfull

end WeierstrassCurve
