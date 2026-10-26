/-
  The lattice of parabolic homomorphisms: a basis, and the rank bound.

  `Period.parabolicHoms R Γ R` is the submodule of `Additive Γ →+ R` cut out by the parabolic
  cocycle condition — the target of the period map. Three facts about it as a lattice:

  * `exists_basis_parabolicHoms_of_isAddTorsionFree` — over `ℤ` the module is free, and **one**
    `ℤ`-basis serves every commutative torsion-free ring `R`: the `R`-basis has the same index
    and its elements are the `Int.castAddHom R`-images of the `ℤ`-basis elements.
  * `exists_basis_parabolicHoms_castAddHom_comp` — the same for fields of characteristic zero.
  * `finrank_parabolicHoms_add_natCard_le_finrank_addMonoidHom_add_one` — the rank inequality
    relating `finrank (parabolicHoms K Γ K)` to `finrank (Γ →+ K)` through the number of
    `T`-orbits on the cosets `SL(2, ℤ) ⧸ Γ`.

  The engine for the first two is the same: a parabolic hom on `Γ` is a hom on the abelianization
  that kills the additive subgroup spanned by the trace-`2` classes, hence a hom on the quotient
  `Q Γ`, which is a finitely generated abelian group; its free part supplies the coordinates. The
  first headline splits `Q Γ` as `(Fin n →₀ ℤ) × T` with `T` finite and kills the `T`-coordinates
  by torsion-freeness; the second reads the coordinates off a finite presentation of `Γ` and
  kills the relations by characteristic zero. The third headline is Bass–Serre: the values on the
  `T`-conjugates of `T` are constrained only by one vanishing sum, so the parabolic homs have
  codimension at most one in the homs vanishing on the orbit representatives.

  Transcribed from the pin's `P2M/Sol/S_ModularCurve_Period_*` files (pinned `aa2d8b3`, 919
  lines) and the matching `Theorems/` wrappers, which carry the statements. Every helper is
  `private`, so the checker diffs only the three headlines.

  spec-pin: Theorems/Thm_ModularCurve_Period_exists_basis_parabolicHoms_of_isAddTorsionFree.lean
  spec-pin: P2M/Sol/S_ModularCurve_Period_exists_basis_parabolicHoms_of_isAddTorsionFree.lean
  spec-pin: Theorems/Thm_ModularCurve_Period_exists_basis_parabolicHoms_castAddHom_comp.lean
  spec-pin: P2M/Sol/S_ModularCurve_Period_exists_basis_parabolicHoms_castAddHom_comp.lean
  spec-pin: Theorems/Thm_ModularCurve_Period_finrank_parabolicHoms_add_natCard_le_finrank_addMonoidHom_add_one.lean
  spec-pin: P2M/Sol/S_ModularCurve_Period_finrank_parabolicHoms_add_natCard_le_finrank_addMonoidHom_add_one.lean
-/
import FLTForHuman.GroupTheory.FreeGroup.SpecialLinearGroupGenerators
import FLTForHuman.ModularCurve.Period.ParabolicHoms
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.Schreier
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.FreeModule.PID

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups

namespace ModularCurve.Period

/-! ### `SL(2, ℤ)` is finitely generated

The pin's `S_` files establish this three separate ways (from `Γ(2)`'s free generators, and from
`S`, `T`); one private instance at the ambient group serves all three headlines. -/
private instance instGroupFG_SL2Z : Group.FG SL(2, ℤ) :=
  ⟨⟨{ModularGroup.S, ModularGroup.T}, by
    rw [Finset.coe_insert, Finset.coe_singleton]
    exact SpecialLinearGroup.SL2Z_generators⟩⟩

/-! ### A basis over every commutative torsion-free ring

Fix `Γ` of finite index. A parabolic hom `Γ → R` is a hom on the abelianization `Ab Γ` that
kills every trace-`2` class, so it factors through `Q Γ := Ab Γ ⧸ P Γ`, where `P Γ` is the
subgroup spanned by those classes. The structure theorem for finitely generated abelian groups
writes `Q Γ` as `(Fin n →₀ ℤ) × T` with `T` finite; torsion-freeness of `R` kills the
`T`-coordinates, and the `n` free coordinates are the basis. -/
namespace BasisTorsionFree

variable (Γ : Subgroup SL(2, ℤ))

/-- The abelianization of `Γ`, as an additive group. -/
private abbrev Ab : Type := Additive (Abelianization ↥Γ)

private instance instAddGroupFG_Ab [Γ.FiniteIndex] : AddGroup.FG (Ab Γ) :=
  GroupFG.iff_add_fg.mp
    (Group.fg_of_surjective (f := Abelianization.of) QuotientGroup.mk_surjective)

/-- The class of `γ` in `Ab Γ`. -/
private def cls (γ : ↥Γ) : Ab Γ := Additive.ofMul (Abelianization.of γ)

private theorem cls_mul (γ δ : ↥Γ) : cls Γ (γ * δ) = cls Γ γ + cls Γ δ := by
  simp [cls, ofMul_mul]

/-- The additive subgroup of `Ab Γ` spanned by the classes of the trace-`2` elements. -/
private def P : AddSubgroup (Ab Γ) :=
  AddSubgroup.closure
    {a | ∃ γ : ↥Γ, ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 ∧ a = cls Γ γ}

/-- The parabolic quotient: `Ab Γ` modulo the trace-`2` relations. -/
private abbrev Q : Type := Ab Γ ⧸ P Γ

private instance instAddGroupFG_Q [Γ.FiniteIndex] : AddGroup.FG (Q Γ) := inferInstance

/-- The class of `γ` in `Q Γ`. -/
private def π (γ : ↥Γ) : Q Γ := (cls Γ γ : Ab Γ)

private theorem π_mul (γ δ : ↥Γ) : π Γ (γ * δ) = π Γ γ + π Γ δ := by
  simp [π, cls_mul]

private theorem π_one : π Γ 1 = 0 := by
  have h := π_mul Γ 1 1
  rw [mul_one] at h
  have : π Γ 1 + π Γ 1 = π Γ 1 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel this

private theorem π_eq_zero_of_trace (γ : ↥Γ)
    (hγ : ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4) : π Γ γ = 0 := by
  show ((cls Γ γ : Ab Γ) : Q Γ) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  exact AddSubgroup.subset_closure ⟨γ, hγ, rfl⟩

private theorem π_surjective : Function.Surjective (π Γ) := by
  intro q
  induction q using QuotientAddGroup.induction_on with
  | H a =>
    obtain ⟨x, rfl⟩ : ∃ x : Abelianization ↥Γ, Additive.ofMul x = a := ⟨Additive.toMul a, rfl⟩
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨γ, rfl⟩

end BasisTorsionFree

namespace BasisTorsionFree

section Factor

variable {Γ : Subgroup SL(2, ℤ)} {R : Type*} [AddCommGroup R]

/-- A hom on `Γ` descends to the abelianization. -/
private def liftA (φ : Additive ↥Γ →+ R) : Ab Γ →+ R :=
  MonoidHom.toAdditiveLeft (Abelianization.lift (AddMonoidHom.toMultiplicativeRight φ))

private theorem liftA_cls (φ : Additive ↥Γ →+ R) (γ : ↥Γ) :
    liftA φ (cls Γ γ) = φ (Additive.ofMul γ) := by
  simp [liftA, cls, Abelianization.lift_apply_of]

private theorem P_le_ker (φ : Additive ↥Γ →+ R) (hφ : IsParabolicHom Γ φ) :
    P Γ ≤ (liftA φ).ker := by
  rw [P, AddSubgroup.closure_le]
  rintro a ⟨γ, hγ, rfl⟩
  show liftA φ (cls Γ γ) = 0
  rw [liftA_cls]
  exact hφ γ hγ

private def liftQ (φ : Additive ↥Γ →+ R) (hφ : IsParabolicHom Γ φ) : Q Γ →+ R :=
  QuotientAddGroup.lift (P Γ) (liftA φ) (P_le_ker φ hφ)

private theorem liftQ_π (φ : Additive ↥Γ →+ R) (hφ : IsParabolicHom Γ φ) (γ : ↥Γ) :
    liftQ φ hφ (π Γ γ) = φ (Additive.ofMul γ) := by
  show QuotientAddGroup.lift (P Γ) (liftA φ) (P_le_ker φ hφ) ((cls Γ γ : Ab Γ) : Q Γ) = _
  rw [QuotientAddGroup.lift_mk, liftA_cls]

/-- A hom out of a module into a torsion-free group kills finite-order elements. -/
private theorem apply_eq_zero_of_isOfFinAddOrder [IsAddTorsionFree R] {G : Type*}
    [AddCommGroup G] (f : G →+ R) (x : G) (hx : IsOfFinAddOrder x) : f x = 0 := by
  obtain ⟨n, hn, hnx⟩ := hx.exists_nsmul_eq_zero
  have h : n • f x = n • (0 : R) := by rw [← map_nsmul, hnx, map_zero, nsmul_zero]
  exact nsmul_right_injective hn.ne' h

end Factor

section Coord

variable (Γ : Subgroup SL(2, ℤ))

/-- A splitting of `Q Γ` into a free part `Fin n →₀ ℤ` and a finite part. -/
private structure Decomp where
  n : ℕ
  T : Type
  instT : AddCommGroup T
  finT : Finite T
  E : Q Γ ≃+ (Fin n →₀ ℤ) × T

private theorem nonempty_decomp [Γ.FiniteIndex] : Nonempty (Decomp Γ) := by
  obtain ⟨n, ι, hι, p, hp, e, ⟨E⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod (Q Γ)
  have hne : ∀ i, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  have hι' : Finite ι := Finite.of_fintype ι
  have hfin : Finite (DirectSum ι fun i => ZMod (p i ^ e i)) :=
    Finite.of_injective (fun x : DirectSum ι (fun i => ZMod (p i ^ e i)) =>
      (x : Π i, ZMod (p i ^ e i))) DFunLike.coe_injective
  exact ⟨⟨n, _, inferInstance, inferInstance, E⟩⟩

end Coord

section CoordMap

variable {Γ : Subgroup SL(2, ℤ)} (D : Decomp Γ)

attribute [instance] Decomp.instT Decomp.finT

/-- The `i`-th free coordinate of `Q Γ`. -/
private def coord (i : Fin D.n) : Q Γ →+ ℤ :=
  (Finsupp.applyAddHom i).comp ((AddMonoidHom.fst _ _).comp D.E.toAddMonoidHom)

private theorem coord_apply (i : Fin D.n) (q : Q Γ) : coord D i q = (D.E q).1 i := rfl

private def sect (v : Fin D.n →₀ ℤ) : Q Γ := D.E.symm (v, 0)

private theorem E_sect (v : Fin D.n →₀ ℤ) : D.E (sect D v) = (v, 0) := D.E.apply_symm_apply _

private theorem coord_sect (i : Fin D.n) (v : Fin D.n →₀ ℤ) : coord D i (sect D v) = v i := by
  rw [coord_apply, E_sect]

/-- The difference of `q` and its free part lies in the finite part. -/
private theorem isOfFinAddOrder_sub_sect (q : Q Γ) :
    IsOfFinAddOrder (q - sect D (D.E q).1) := by
  have h : D.E (q - sect D (D.E q).1) = (0, (D.E q).2) := by
    rw [map_sub, E_sect, Prod.ext_iff]
    simp
  have hfin : IsOfFinAddOrder ((0, (D.E q).2) : (Fin D.n →₀ ℤ) × D.T) := by
    have h2 : IsOfFinAddOrder (D.E q).2 := isOfFinAddOrder_of_finite _
    obtain ⟨m, hm, hm2⟩ := h2.exists_nsmul_eq_zero
    refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨m, hm, ?_⟩
    rw [Prod.ext_iff]
    exact ⟨by simp, by simpa using hm2⟩
  have hq : q - sect D (D.E q).1 = D.E.symm (0, (D.E q).2) := by
    apply D.E.injective; rw [h, AddEquiv.apply_symm_apply]
  rw [hq]
  exact D.E.symm.toAddMonoidHom.isOfFinAddOrder hfin

end CoordMap

section Basis

variable {Γ : Subgroup SL(2, ℤ)} (D : Decomp Γ) (R : Type*) [CommRing R]

/-- The `i`-th coordinate function on `Γ`, as a hom into `R`. -/
private def chi (i : Fin D.n) : Additive ↥Γ →+ R where
  toFun x := (coord D i (π Γ (Additive.toMul x)) : R)
  map_zero' := by
    show ((coord D i (π Γ 1) : ℤ) : R) = 0
    rw [π_one, map_zero, Int.cast_zero]
  map_add' x y := by
    show ((coord D i (π Γ (Additive.toMul x * Additive.toMul y)) : ℤ) : R) = _
    rw [π_mul, map_add, Int.cast_add]

private theorem chi_apply (i : Fin D.n) (γ : ↥Γ) :
    chi D R i (Additive.ofMul γ) = (coord D i (π Γ γ) : R) := rfl

private theorem chi_mem (i : Fin D.n) : chi D R i ∈ parabolicHoms R Γ R := by
  intro γ hγ
  rw [chi_apply, π_eq_zero_of_trace Γ γ hγ, map_zero, Int.cast_zero]

private theorem chi_int_cast (i : Fin D.n) :
    (Int.castAddHom R).comp (chi D ℤ i) = chi D R i := by
  refine AddMonoidHom.ext fun x => ?_
  simp [chi]

/-- The assembled coordinate map into the parabolic homs. -/
private def Θ : (Fin D.n → R) →ₗ[R] ↥(parabolicHoms R Γ R) where
  toFun c := ∑ i, c i • (⟨chi D R i, chi_mem D R i⟩ : ↥(parabolicHoms R Γ R))
  map_add' c c' := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.add_apply, add_smul]
  map_smul' r c := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply]

private theorem Θ_apply_apply (c : Fin D.n → R) (γ : ↥Γ) :
    ((Θ D R c : ↥(parabolicHoms R Γ R)) : Additive ↥Γ →+ R) (Additive.ofMul γ) =
      ∑ i, c i * (coord D i (π Γ γ) : R) := by
  simp only [Θ, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_sum, Submodule.coe_smul,
    AddMonoidHom.finsetSum_apply, AddMonoidHom.smul_apply, chi_apply, smul_eq_mul]

private theorem Θ_single (i : Fin D.n) :
    ((Θ D R (Pi.single i 1) : ↥(parabolicHoms R Γ R)) : Additive ↥Γ →+ R) = chi D R i := by
  refine AddMonoidHom.ext fun x => ?_
  obtain ⟨γ, rfl⟩ : ∃ γ, Additive.ofMul γ = x := ⟨Additive.toMul x, rfl⟩
  rw [Θ_apply_apply, chi_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hji; simp [Pi.single_eq_of_ne hji]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- Every free coordinate is attained by some element of `Γ`. -/
private theorem exists_coord_eq_single (j : Fin D.n) :
    ∃ γ : ↥Γ, ∀ i, coord D i (π Γ γ) = if i = j then 1 else 0 := by
  obtain ⟨γ, hγ⟩ := π_surjective Γ (sect D (Finsupp.single j 1))
  refine ⟨γ, fun i => ?_⟩
  rw [hγ, coord_sect]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

private theorem Θ_injective : Function.Injective (Θ D R) := by
  intro c c' h
  funext j
  obtain ⟨γ, hγ⟩ := exists_coord_eq_single D j
  have := congrArg (fun φ : ↥(parabolicHoms R Γ R) => (φ : Additive ↥Γ →+ R) (Additive.ofMul γ)) h
  simp only [Θ_apply_apply, hγ] at this
  simpa [Finset.sum_ite_eq', Finset.mem_univ] using this

private theorem Θ_surjective [IsAddTorsionFree R] : Function.Surjective (Θ D R) := by
  intro φ
  set ψ : Q Γ →+ R := liftQ (φ : Additive ↥Γ →+ R) φ.2 with hψ
  refine ⟨fun i => ψ (sect D (Finsupp.single i 1)), Subtype.ext ?_⟩
  refine AddMonoidHom.ext fun x => ?_
  obtain ⟨γ, rfl⟩ : ∃ γ, Additive.ofMul γ = x := ⟨Additive.toMul x, rfl⟩
  rw [Θ_apply_apply, ← liftQ_π (φ : Additive ↥Γ →+ R) φ.2 γ]
  set q := π Γ γ with hq
  have hkill : ψ (q - sect D (D.E q).1) = 0 :=
    apply_eq_zero_of_isOfFinAddOrder ψ _ (isOfFinAddOrder_sub_sect D q)
  have hq' : ψ q = ψ (sect D (D.E q).1) := by
    rw [map_sub, sub_eq_zero] at hkill; exact hkill
  rw [hq']
  have hv : sect D (D.E q).1 = ∑ i, ((D.E q).1 i) • sect D (Finsupp.single i 1) := by
    have hsect : ∀ v w : Fin D.n →₀ ℤ, sect D (v + w) = sect D v + sect D w := by
      intro v w; unfold sect; rw [← map_add, Prod.mk_add_mk, add_zero]
    have hsmul : ∀ (m : ℤ) (v : Fin D.n →₀ ℤ), sect D (m • v) = m • sect D v := by
      intro m v; unfold sect; rw [← map_zsmul, Prod.smul_mk, smul_zero]
    conv_lhs => rw [← Finsupp.univ_sum_single (D.E q).1]
    rw [show sect D (∑ i, Finsupp.single i ((D.E q).1 i)) =
        ∑ i, sect D (Finsupp.single i ((D.E q).1 i)) from map_sum
          (⟨⟨sect D, by unfold sect; rw [← map_zero D.E.symm]; rfl⟩, hsect⟩ :
            (Fin D.n →₀ ℤ) →+ Q Γ) _ _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hsmul, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hv, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, coord_apply, zsmul_eq_mul, mul_comm]

private theorem Θ_bijective [IsAddTorsionFree R] : Function.Bijective (Θ D R) :=
  ⟨Θ_injective D R, Θ_surjective D R⟩

private def basisR [IsAddTorsionFree R] : Module.Basis (Fin D.n) R ↥(parabolicHoms R Γ R) :=
  Module.Basis.map (Pi.basisFun R (Fin D.n))
    (LinearEquiv.ofBijective (Θ D R) (Θ_bijective D R))

private theorem coe_basisR [IsAddTorsionFree R] (i : Fin D.n) :
    ((basisR D R i : ↥(parabolicHoms R Γ R)) : Additive ↥Γ →+ R) = chi D R i := by
  rw [basisR, Module.Basis.map_apply, Pi.basisFun_apply, LinearEquiv.ofBijective_apply, Θ_single]

end Basis

end BasisTorsionFree

/-! ### The first headline -/

/-- **A `ℤ`-basis of the parabolic homs serves every commutative torsion-free ring.** The pin's
`ModularCurve.Period.exists_basis_parabolicHoms_of_isAddTorsionFree`: one `ℤ`-basis `b` of
`parabolicHoms ℤ Γ ℤ` whose `Int.castAddHom R`-images are an `R`-basis of
`parabolicHoms R Γ R`, index for index. -/
theorem exists_basis_parabolicHoms_of_isAddTorsionFree (Γ : Subgroup SL(2, ℤ))
    [Γ.FiniteIndex] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℤ (ModularCurve.Period.parabolicHoms ℤ Γ ℤ)),
      ∀ (R : Type*) [CommRing R] [IsAddTorsionFree R],
        ∃ bR : Module.Basis (Fin n) R (ModularCurve.Period.parabolicHoms R Γ R),
          ∀ i, (bR i : Additive Γ →+ R) = (Int.castAddHom R).comp (b i : Additive Γ →+ ℤ) := by
  obtain ⟨D⟩ := BasisTorsionFree.nonempty_decomp Γ
  refine ⟨D.n, BasisTorsionFree.basisR D ℤ, fun R _ _ => ⟨BasisTorsionFree.basisR D R, ?_⟩⟩
  intro i
  rw [BasisTorsionFree.coe_basisR, BasisTorsionFree.coe_basisR,
    BasisTorsionFree.chi_int_cast]

/-! ### The rank bound

Fix `Γ` of finite index and a field `K`. On the `T`-orbits of `SL(2, ℤ) ⧸ Γ` sits the
Bass–Serre cocycle `c ↦ γ_c`, where `γ_c = g⁻¹ T ^ n g` is the `T`-conjugate attached to a
coset representative `g` of `c` and `n` is the `T`-period of `c`. Evaluating a parabolic hom at
these `γ_c` gives a linear map `parabolicHoms K Γ K → (orbits → K)`; the only constraint on the
image is that the coordinates sum to zero (the `γ_c` bound a single `T`-orbit, so their sum in the
edge chain vanishes). Hence `finrank (parabolicHoms K Γ K) ≤ finrank (ker of the sum map)`, and
the sum map is onto `K`, so the kernel has dimension `#orbits - 1`. -/
namespace RankBound

variable (Γ : Subgroup SL(2, ℤ))

/-- The `T`-orbits on the cosets of `Γ`. -/
private abbrev Orbit : Type :=
  MulAction.orbitRel.Quotient (Subgroup.zpowers ModularGroup.T) (SL(2, ℤ) ⧸ Γ)

/-- The `T`-orbit of a coset. -/
private def mkOrbit (x : SL(2, ℤ) ⧸ Γ) : Orbit Γ :=
  Quotient.mk (MulAction.orbitRel (Subgroup.zpowers ModularGroup.T) _) x

private theorem mkOrbit_surjective : Function.Surjective (mkOrbit Γ) := Quotient.mk_surjective

/-- The `T`-period of a coset: the least `n > 0` with `T ^ n` stabilising it. -/
private def period (x : SL(2, ℤ) ⧸ Γ) : ℕ := Function.minimalPeriod (fun y => ModularGroup.T • y) x

/-- The `T`-conjugate attached to `g` lies in `Γ`. -/
private theorem conj_mem (g : SL(2, ℤ)) :
    g⁻¹ * ModularGroup.T ^ period Γ (g : SL(2, ℤ) ⧸ Γ) * g ∈ Γ := by
  have h0 : ModularGroup.T ^ period Γ (g : SL(2, ℤ) ⧸ Γ) • (g : SL(2, ℤ) ⧸ Γ)
      = (g : SL(2, ℤ) ⧸ Γ) :=
    (MulAction.pow_smul_eq_iff_minimalPeriod_dvd).mpr dvd_rfl
  have h1 : ((ModularGroup.T ^ period Γ (g : SL(2, ℤ) ⧸ Γ) * g : SL(2, ℤ)) : SL(2, ℤ) ⧸ Γ)
      = (g : SL(2, ℤ) ⧸ Γ) := h0
  rw [QuotientGroup.eq] at h1
  have h2 := Γ.inv_mem h1
  simpa only [_root_.mul_inv_rev, inv_inv, mul_assoc] using h2

/-- A coset representative of an orbit. -/
private def rep (c : Orbit Γ) : SL(2, ℤ) := Quotient.out (Quotient.out c)

private theorem mkOrbit_rep (c : Orbit Γ) : mkOrbit Γ (rep Γ c : SL(2, ℤ) ⧸ Γ) = c := by
  rw [rep, QuotientGroup.out_eq', mkOrbit]; exact Quotient.out_eq c

/-- The `T`-conjugate attached to the representative of an orbit. -/
private def generator (c : Orbit Γ) : Γ := ⟨_, conj_mem Γ (rep Γ c)⟩

private theorem trace_generator (c : Orbit Γ) :
    ((generator Γ c : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 2 := by
  show (((rep Γ c)⁻¹ * ModularGroup.T ^ period Γ (rep Γ c : SL(2, ℤ) ⧸ Γ) * rep Γ c : SL(2, ℤ)) :
      Matrix (Fin 2) (Fin 2) ℤ).trace = 2
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_comm, Matrix.SpecialLinearGroup.coe_mul,
    ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul, ← zpow_natCast, ModularGroup.coe_T_zpow]
  simp [Matrix.trace_fin_two]

variable (K : Type) [Field K]

/-- Evaluation of a hom at the `T`-conjugates, as a linear map. -/
private def evalAt : (Additive Γ →+ K) →ₗ[K] (Orbit Γ → K) where
  toFun φ c := φ (Additive.ofMul (generator Γ c))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem parabolicHoms_le_ker : parabolicHoms K Γ K ≤ LinearMap.ker (evalAt Γ K) := by
  intro φ hφ
  rw [LinearMap.mem_ker]
  funext c
  exact hφ (generator Γ c) (by rw [trace_generator]; norm_num)

/-- Summing the coordinates. -/
private def sumHom [Fintype (Orbit Γ)] : (Orbit Γ → K) →ₗ[K] K where
  toFun v := ∑ c, v c
  map_add' _ _ := by simp [Finset.sum_add_distrib]
  map_smul' _ _ := by simp [Finset.mul_sum]

/-- The vanishing-sum condition cuts out exactly the range of evaluation. -/
private theorem ker_sumHom_le_range [Γ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∈ Γ)
    [Fintype (Orbit Γ)] :
    LinearMap.ker (sumHom Γ K) ≤ LinearMap.range (evalAt Γ K) := by
  intro v hv
  rw [LinearMap.mem_ker] at hv
  have hv' : ∑ᶠ c, v c = 0 := by rw [finsum_eq_sum_of_fintype]; exact hv
  obtain ⟨φ, hφ⟩ :=
    Matrix.SpecialLinearGroup.exists_addMonoidHom_conj_T_pow_minimalPeriod_eq_of_finsum_eq_zero
      Γ hneg K v hv'
  refine ⟨φ, funext fun c => ?_⟩
  show φ (Additive.ofMul (generator Γ c)) = v c
  have key := hφ (rep Γ c) (conj_mem Γ (rep Γ c))
  exact key.trans (congrArg v (mkOrbit_rep Γ c))

private theorem finrank_ker_sumHom_add_one [Fintype (Orbit Γ)] :
    Module.finrank K (LinearMap.ker (sumHom Γ K)) + 1 = Fintype.card (Orbit Γ) := by
  classical
  have c₀ : Orbit Γ := mkOrbit Γ ((1 : SL(2, ℤ)) : SL(2, ℤ) ⧸ Γ)
  have hsurj : Function.Surjective (sumHom Γ K) := fun r =>
    ⟨Pi.single c₀ r, by simp [sumHom]⟩
  have h1 : Module.finrank K (LinearMap.range (sumHom Γ K)) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self]
  have h2 := LinearMap.finrank_range_add_finrank_ker (sumHom Γ K)
  rw [h1, Module.finrank_fintype_fun_eq_card] at h2
  omega

/-- `Additive Γ →+ K` is finite-dimensional, from a finite generating set of `Γ`. -/
private theorem moduleFinite_addMonoidHom [Γ.FiniteIndex] :
    Module.Finite K (Additive Γ →+ K) := by
  classical
  have hΓ : Group.FG Γ := Subgroup.fg_of_index_ne_zero Γ
  obtain ⟨s, hs⟩ := hΓ.out
  let e : (Additive Γ →+ K) →ₗ[K] (s → K) :=
    { toFun := fun φ i => φ (Additive.ofMul (i : Γ))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective e ?_
  intro φ ψ h
  have key : ∀ γ : Γ, φ (Additive.ofMul γ) = ψ (Additive.ofMul γ) := by
    intro γ
    have hγ : γ ∈ Subgroup.closure (s : Set Γ) := by rw [hs]; exact Subgroup.mem_top γ
    induction hγ using Subgroup.closure_induction with
    | mem x hx => exact congrFun h ⟨x, hx⟩
    | one => rw [ofMul_one, map_zero, map_zero]
    | mul x y _ _ hx hy => rw [ofMul_mul, map_add, map_add, hx, hy]
    | inv x _ hx => rw [ofMul_inv, map_neg, map_neg, hx]
  exact AddMonoidHom.ext fun x => key (Additive.toMul x)

private theorem main [Γ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∈ Γ) :
    Module.finrank K (parabolicHoms K Γ K) + Nat.card (Orbit Γ)
      ≤ Module.finrank K (Additive Γ →+ K) + 1 := by
  classical
  have hft : Fintype (Orbit Γ) := Fintype.ofFinite _
  have hfin : Module.Finite K (Additive Γ →+ K) := moduleFinite_addMonoidHom Γ K
  have h1 : Module.finrank K (parabolicHoms K Γ K) ≤ Module.finrank K (LinearMap.ker (evalAt Γ K)) :=
    Submodule.finrank_mono (parabolicHoms_le_ker Γ K)
  have h2 : Module.finrank K (LinearMap.ker (sumHom Γ K))
      ≤ Module.finrank K (LinearMap.range (evalAt Γ K)) :=
    Submodule.finrank_mono (ker_sumHom_le_range Γ K hneg)
  have h3 := finrank_ker_sumHom_add_one Γ K
  have h4 := LinearMap.finrank_range_add_finrank_ker (evalAt Γ K)
  rw [Nat.card_eq_fintype_card]
  omega

end RankBound

/-! ### The third headline -/

/-- **The rank inequality.** The pin's
`ModularCurve.Period.finrank_parabolicHoms_add_natCard_le_finrank_addMonoidHom_add_one`: the
dimension of the parabolic homs plus the number of `T`-orbits on the cosets is at most the
dimension of all the additive homs, plus one. -/
theorem finrank_parabolicHoms_add_natCard_le_finrank_addMonoidHom_add_one
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Γ) (K : Type) [Field K] :
    Module.finrank K (ModularCurve.Period.parabolicHoms K Γ K)
      + Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers ModularGroup.T)
          (Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ Γ))
      ≤ Module.finrank K (Additive Γ →+ K) + 1 :=
  RankBound.main (Γ := Γ) (K := K) hneg

/-! ### A basis over every field of characteristic zero

The same coordinates, read off a finite presentation instead of the structure theorem. Fix a
finite generating set `g : Fin n → Γ`; it presents `Γ` as a quotient of `FreeGroup (Fin n)`. A
hom `Γ →+ A` is the same as a `n`-tuple of values `ev φ`, and it is parabolic exactly when the
tuple is orthogonal (under `pair c z = ∑ c i • z i`) to the submodule `R` spanned by the
abelianized parabolic words. Since `R` has finite index in `ℤⁿ`, the quotient `ℤⁿ ⧸ R` is
finitely generated and, after killing its torsion, free of rank `t`; over a field of
characteristic zero the torsion dies, so `ev` becomes a bijection onto `Fin t → A`, and
`Basis.ofEquivFun` turns its inverse into a basis whose elements are
`Int.castAddHom`-images of the `ℤ`-basis. -/
namespace BasisField

section Generators

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

/-- A finite generating set of `Γ`, as a map out of a `Fin n`. -/
private theorem exists_generators :
    ∃ (n : ℕ) (g : Fin n → Γ), Subgroup.closure (Set.range g) = ⊤ := by
  obtain ⟨n, S, -, hS⟩ := Group.fg_iff'.1 (inferInstance : Group.FG Γ)
  exact ⟨S.card, Subtype.val ∘ S.equivFin.symm, by
    rw [Set.range_comp, Equiv.range_eq_univ, Set.image_univ, Subtype.range_coe_subtype]
    exact hS⟩

end Generators

section Presentation

variable {Γ : Subgroup SL(2, ℤ)} {n : ℕ} (g : Fin n → Γ)

/-- The presentation map `FreeGroup (Fin n) →* Γ`. -/
private def π : FreeGroup (Fin n) →* Γ := FreeGroup.lift g

private theorem π_surjective (hg : Subgroup.closure (Set.range g) = ⊤) :
    Function.Surjective (π g) := by
  rw [← MonoidHom.range_eq_top, π, FreeGroup.range_lift_eq_closure, hg]

/-- The abelianization map on words. -/
private def abHom : FreeGroup (Fin n) →* Multiplicative (Fin n → ℤ) :=
  FreeGroup.lift fun i => Multiplicative.ofAdd (Pi.single i 1)

/-- The exponent vector of a word. -/
private def ab (w : FreeGroup (Fin n)) : Fin n → ℤ := Multiplicative.toAdd (abHom w)

private theorem ab_of (i : Fin n) : ab (FreeGroup.of i) = Pi.single i 1 := by
  simp [ab, abHom]

/-- The pairing of an exponent vector with an `n`-tuple of group elements. -/
private def pair {A : Type*} [AddCommGroup A] (c : Fin n → ℤ) (z : Fin n → A) : A :=
  ∑ i, c i • z i

private theorem pair_eq_linearCombination {A : Type*} [AddCommGroup A] (c : Fin n → ℤ)
    (z : Fin n → A) : pair c z = Fintype.linearCombination ℤ z c := by
  rw [Fintype.linearCombination_apply]; rfl

private theorem pair_add_left {A : Type*} [AddCommGroup A] (c c' : Fin n → ℤ) (z : Fin n → A) :
    pair (c + c') z = pair c z + pair c' z := by
  simp only [pair_eq_linearCombination, map_add]

private theorem pair_smul_left {A : Type*} [AddCommGroup A] (k : ℤ) (c : Fin n → ℤ)
    (z : Fin n → A) : pair (k • c) z = k • pair c z := by
  simp only [pair_eq_linearCombination, map_zsmul]

private theorem pair_zero_left {A : Type*} [AddCommGroup A] (z : Fin n → A) :
    pair (0 : Fin n → ℤ) z = 0 := by
  simp only [pair_eq_linearCombination, map_zero]

private theorem pair_single {A : Type*} [AddCommGroup A] (i : Fin n) (z : Fin n → A) :
    pair (Pi.single i 1) z = z i := by
  classical
  simp [pair, Pi.single_apply]

private theorem pair_map {A : Type*} [AddCommGroup A] {B : Type*} [AddCommGroup B] (f : A →+ B)
    (c : Fin n → ℤ) (z : Fin n → A) : f (pair c z) = pair c (f ∘ z) := by
  simp [pair, map_sum, map_zsmul]

private def pairHom {A : Type*} [AddCommGroup A] (z : Fin n → A) : (Fin n → ℤ) →+ A where
  toFun c := pair c z
  map_zero' := pair_zero_left z
  map_add' c c' := pair_add_left c c' z

private def Lz {A : Type*} [AddCommGroup A] (z : Fin n → A) : FreeGroup (Fin n) →* Multiplicative A :=
  FreeGroup.lift fun i => Multiplicative.ofAdd (z i)

private theorem toAdd_Lz {A : Type*} [AddCommGroup A] (z : Fin n → A)
    (w : FreeGroup (Fin n)) : Multiplicative.toAdd (Lz z w) = pair (ab w) z := by
  have key : Lz z = (AddMonoidHom.toMultiplicative (pairHom z)).comp abHom := by
    refine FreeGroup.ext_hom _ _ fun i => ?_
    simp only [Lz, FreeGroup.lift_apply_of, MonoidHom.coe_comp, Function.comp_apply]
    show Multiplicative.ofAdd (z i) = Multiplicative.ofAdd (pairHom z (ab (FreeGroup.of i)))
    rw [ab_of]; show _ = Multiplicative.ofAdd (pair (Pi.single i 1) z); rw [pair_single]
  rw [key]; rfl

private theorem apply_π {A : Type*} [AddCommGroup A] (φ : Additive Γ →+ A)
    (w : FreeGroup (Fin n)) :
    φ (Additive.ofMul (π g w)) = pair (ab w) (fun i => φ (Additive.ofMul (g i))) := by
  have key : (AddMonoidHom.toMultiplicativeRight φ).comp (π g)
      = Lz (fun i => φ (Additive.ofMul (g i))) := by
    refine FreeGroup.ext_hom _ _ fun i => ?_
    simp only [MonoidHom.coe_comp, Function.comp_apply, π, FreeGroup.lift_apply_of, Lz]
    rfl
  have := congrArg (fun f => Multiplicative.toAdd (f w)) key
  simp only [MonoidHom.coe_comp, Function.comp_apply] at this
  rw [toAdd_Lz] at this
  exact this

/-- The parabolic condition on a group element, read on matrices. -/
private def IsPar (γ : Γ) : Prop := ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4

private theorem isPar_one : IsPar (1 : Γ) := by
  simp [IsPar]

/-- The relation submodule: the exponent vectors of the parabolic words. -/
private def R : Submodule ℤ (Fin n → ℤ) :=
  Submodule.span ℤ {c | ∃ w, IsPar (π g w) ∧ ab w = c}

private theorem ab_mem_R {w : FreeGroup (Fin n)} (hw : IsPar (π g w)) : ab w ∈ R g :=
  Submodule.subset_span ⟨w, hw, rfl⟩

private def ev {A : Type*} [AddCommGroup A] (φ : Additive Γ →+ A) : Fin n → A :=
  fun i => φ (Additive.ofMul (g i))

private theorem ev_perp {A : Type*} [AddCommGroup A] {φ : Additive Γ →+ A}
    (hφ : φ ∈ parabolicHoms ℤ Γ A) : ∀ c ∈ R g, pair c (ev g φ) = 0 := by
  intro c hc
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨w, hw, rfl⟩ := hc
    show pair (ab w) (fun i => φ (Additive.ofMul (g i))) = 0
    rw [← apply_π]; exact hφ _ hw
  | zero => exact pair_zero_left _
  | add c c' _ _ hc hc' => rw [pair_add_left, hc, hc', add_zero]
  | smul k c _ hc => rw [pair_smul_left, hc, smul_zero]

private theorem ev_injective {A : Type*} [AddCommGroup A]
    (hg : Subgroup.closure (Set.range g) = ⊤) {φ ψ : Additive Γ →+ A}
    (h : ev g φ = ev g ψ) : φ = ψ := by
  have : AddMonoidHom.toMultiplicativeRight φ = AddMonoidHom.toMultiplicativeRight ψ := by
    refine MonoidHom.eq_of_eqOn_dense hg ?_
    rintro _ ⟨i, rfl⟩
    exact congrArg Multiplicative.ofAdd (congrFun h i)
  exact AddMonoidHom.toMultiplicativeRight.injective this

variable {g}

private theorem Lz_eq_one_of_mem_ker {A : Type*} [AddCommGroup A] {z : Fin n → A}
    (hz : ∀ c ∈ R g, pair c z = 0) {w : FreeGroup (Fin n)} (hw : w ∈ (π g).ker) : Lz z w = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_Lz, toAdd_one]
  refine hz _ (ab_mem_R g ?_)
  rw [MonoidHom.mem_ker] at hw; rw [hw]; exact isPar_one

private theorem Lz_eq_of_π_eq {A : Type*} [AddCommGroup A] {z : Fin n → A}
    (hz : ∀ c ∈ R g, pair c z = 0) {w₁ w₂ : FreeGroup (Fin n)} (h : π g w₁ = π g w₂) :
    Lz z w₁ = Lz z w₂ := by
  have hk : w₁⁻¹ * w₂ ∈ (π g).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  have := Lz_eq_one_of_mem_ker hz hk
  rw [map_mul, map_inv, inv_mul_eq_one] at this
  exact this

variable (g)

private noncomputable def liftFun {A : Type*} [AddCommGroup A]
    (hg : Subgroup.closure (Set.range g) = ⊤) (z : Fin n → A) (γ : Γ) : A :=
  Multiplicative.toAdd (Lz z (Function.surjInv (π_surjective g hg) γ))

private theorem liftFun_π {A : Type*} [AddCommGroup A]
    (hg : Subgroup.closure (Set.range g) = ⊤) {z : Fin n → A}
    (hz : ∀ c ∈ R g, pair c z = 0) (w : FreeGroup (Fin n)) :
    liftFun g hg z (π g w) = pair (ab w) z := by
  rw [liftFun, ← toAdd_Lz]
  exact congrArg _ (Lz_eq_of_π_eq hz (Function.surjInv_eq (π_surjective g hg) _))

private noncomputable def liftHom {A : Type*} [AddCommGroup A]
    (hg : Subgroup.closure (Set.range g) = ⊤) (z : Fin n → A)
    (hz : ∀ c ∈ R g, pair c z = 0) : Additive Γ →+ A where
  toFun x := liftFun g hg z (Additive.toMul x)
  map_zero' := by
    show liftFun g hg z 1 = 0
    rw [← map_one (π g), liftFun_π g hg hz, ← toAdd_Lz, map_one, toAdd_one]
  map_add' x y := by
    obtain ⟨w₁, h₁⟩ := π_surjective g hg (Additive.toMul x)
    obtain ⟨w₂, h₂⟩ := π_surjective g hg (Additive.toMul y)
    show liftFun g hg z (Additive.toMul x * Additive.toMul y) = _
    rw [← h₁, ← h₂, ← map_mul, liftFun_π g hg hz, liftFun_π g hg hz, liftFun_π g hg hz,
      ← toAdd_Lz, ← toAdd_Lz, ← toAdd_Lz, map_mul, toAdd_mul]

private theorem liftHom_π {A : Type*} [AddCommGroup A]
    (hg : Subgroup.closure (Set.range g) = ⊤) {z : Fin n → A}
    (hz : ∀ c ∈ R g, pair c z = 0) (w : FreeGroup (Fin n)) :
    liftHom g hg z hz (Additive.ofMul (π g w)) = pair (ab w) z :=
  liftFun_π g hg hz w

private theorem liftHom_mem {A : Type*} [AddCommGroup A]
    (hg : Subgroup.closure (Set.range g) = ⊤) {z : Fin n → A}
    (hz : ∀ c ∈ R g, pair c z = 0) : liftHom g hg z hz ∈ parabolicHoms ℤ Γ A := by
  intro γ hγ
  obtain ⟨w, rfl⟩ := π_surjective g hg γ
  rw [liftHom_π]
  exact hz _ (ab_mem_R g hγ)

private theorem ev_liftHom {A : Type*} [AddCommGroup A]
    (hg : Subgroup.closure (Set.range g) = ⊤) {z : Fin n → A}
    (hz : ∀ c ∈ R g, pair c z = 0) : ev g (liftHom g hg z hz) = z := by
  funext i
  have := liftHom_π g hg hz (FreeGroup.of i)
  rw [π, FreeGroup.lift_apply_of, ab_of, pair_single] at this
  exact this

/-- The quotient of `ℤⁿ` by the parabolic relations. -/
private abbrev Q : Type := (Fin n → ℤ) ⧸ R g

/-- `Q` modulo its torsion: the free part. -/
private abbrev Qf : Type := Q g ⧸ Submodule.torsion ℤ (Q g)

private def proj : (Fin n → ℤ) →ₗ[ℤ] Qf g :=
  (Submodule.torsion ℤ (Q g)).mkQ ∘ₗ (R g).mkQ

private theorem proj_surjective : Function.Surjective (proj g) :=
  (Submodule.mkQ_surjective _).comp (Submodule.mkQ_surjective _)

/-- The rank of the free part. -/
private noncomputable def t : ℕ := Module.finrank ℤ (Qf g)

private noncomputable def ε : Module.Basis (Fin (t g)) ℤ (Qf g) := by
  have hQ : Module.Finite ℤ (Q g) := Module.Finite.quotient ℤ (R g)
  have hQf : Module.Finite ℤ (Qf g) := Module.Finite.quotient ℤ _
  have htf : Module.IsTorsionFree ℤ (Qf g) := Submodule.QuotientTorsion.instIsTorsionFree
  have hfree : Module.Free ℤ (Qf g) := Module.free_of_finite_type_torsion_free'
  exact Module.finBasis ℤ (Qf g)

private noncomputable def cLift (k : Fin (t g)) : Fin n → ℤ :=
  Function.surjInv (proj_surjective g) (ε g k)

private theorem proj_cLift (k : Fin (t g)) : proj g (cLift g k) = ε g k :=
  Function.surjInv_eq (proj_surjective g) _

variable {A : Type*} [AddCommGroup A]

/-- The coordinates of a tuple, in a basis of the free part. -/
private noncomputable def Λ (z : Fin n → A) : Fin (t g) → A := fun k => pair (cLift g k) z

private noncomputable def descend (hA : ∀ (a : ℤ) (x : A), a ≠ 0 → a • x = 0 → x = 0)
    (z : Fin n → A) (hz : ∀ c ∈ R g, pair c z = 0) : Qf g →ₗ[ℤ] A :=
  (Submodule.torsion ℤ (Q g)).liftQ
    ((R g).liftQ (Fintype.linearCombination ℤ z) (by
      intro c hc
      rw [LinearMap.mem_ker, ← pair_eq_linearCombination]
      exact hz c hc))
    (by
      intro x hx
      obtain ⟨⟨a, ha⟩, hax⟩ := (Submodule.mem_torsion_iff x).1 hx
      rw [LinearMap.mem_ker]
      refine hA a _ (nonZeroDivisors.ne_zero ha) ?_
      rw [← map_zsmul]
      change (R g).liftQ _ _ ((⟨a, ha⟩ : nonZeroDivisors ℤ) • x) = 0
      rw [hax, map_zero])

private theorem descend_proj (hA : ∀ (a : ℤ) (x : A), a ≠ 0 → a • x = 0 → x = 0)
    (z : Fin n → A) (hz : ∀ c ∈ R g, pair c z = 0) (c : Fin n → ℤ) :
    descend g hA z hz (proj g c) = pair c z := by
  show (Submodule.torsion ℤ (Q g)).liftQ _ _
    (Submodule.Quotient.mk (Submodule.Quotient.mk c)) = _
  rw [Submodule.liftQ_apply]
  erw [Submodule.liftQ_apply]
  rw [← pair_eq_linearCombination]

private theorem Λ_eq_descend (hA : ∀ (a : ℤ) (x : A), a ≠ 0 → a • x = 0 → x = 0)
    (z : Fin n → A) (hz : ∀ c ∈ R g, pair c z = 0) (k : Fin (t g)) :
    Λ g z k = descend g hA z hz (ε g k) := by
  rw [Λ, ← proj_cLift, descend_proj]

private theorem Λ_injective (hA : ∀ (a : ℤ) (x : A), a ≠ 0 → a • x = 0 → x = 0)
    {z z' : Fin n → A} (hz : ∀ c ∈ R g, pair c z = 0) (hz' : ∀ c ∈ R g, pair c z' = 0)
    (h : Λ g z = Λ g z') : z = z' := by
  have hd : descend g hA z hz = descend g hA z' hz' := by
    refine (ε g).ext fun k => ?_
    rw [← Λ_eq_descend, ← Λ_eq_descend, h]
  funext i
  have := congrArg (fun f => f (proj g (Pi.single i 1))) hd
  simp only [descend_proj, pair_single] at this
  exact this

private theorem pair_stdBasis (G : (Fin n → ℤ) →ₗ[ℤ] A) (c : Fin n → ℤ) :
    pair c (fun i => G (Pi.single i 1)) = G c := by
  classical
  simp only [pair, ← map_zsmul]
  rw [← map_sum]
  congr 1
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

private theorem Λ_surjective (y : Fin (t g) → A) :
    ∃ z : Fin n → A, (∀ c ∈ R g, pair c z = 0) ∧ Λ g z = y := by
  classical
  let F : Qf g →ₗ[ℤ] A := (ε g).constr ℤ y
  refine ⟨fun i => F (proj g (Pi.single i 1)), ?_, ?_⟩
  · intro c hc
    have h1 := pair_stdBasis (F ∘ₗ proj g) c
    simp only [LinearMap.coe_comp, Function.comp_apply] at h1
    rw [h1]
    have : proj g c = 0 := by
      have h0 : (R g).mkQ c = 0 := (Submodule.Quotient.mk_eq_zero (R g)).2 hc
      show (Submodule.torsion ℤ (Q g)).mkQ ((R g).mkQ c) = 0
      rw [h0, map_zero]
    rw [this, map_zero]
  · funext k
    show pair (cLift g k) _ = y k
    have h1 := pair_stdBasis (F ∘ₗ proj g) (cLift g k)
    simp only [LinearMap.coe_comp, Function.comp_apply] at h1
    rw [h1, proj_cLift]
    exact (ε g).constr_basis ℤ y k

private theorem coord_bijective (hg : Subgroup.closure (Set.range g) = ⊤)
    (hA : ∀ (a : ℤ) (x : A), a ≠ 0 → a • x = 0 → x = 0) :
    Function.Bijective
      (fun φ : parabolicHoms ℤ Γ A => Λ g (ev g (φ : Additive Γ →+ A))) := by
  constructor
  · intro φ ψ h
    exact Subtype.ext (ev_injective g hg (Λ_injective g hA (ev_perp g φ.2) (ev_perp g ψ.2) h))
  · intro y
    obtain ⟨z, hz, hy⟩ := Λ_surjective g y
    exact ⟨⟨liftHom g hg z hz, liftHom_mem g hg hz⟩, by simp only [ev_liftHom]; exact hy⟩

end Presentation

section Main

variable {Γ : Subgroup SL(2, ℤ)} {n : ℕ} (g : Fin n → Γ)

private theorem pair_add_right {A : Type*} [AddCommGroup A] (c : Fin n → ℤ) (z z' : Fin n → A) :
    pair c (z + z') = pair c z + pair c z' := by
  simp [pair, Finset.sum_add_distrib]

private theorem pair_smul_right {A : Type*} [AddCommGroup A] {S : Type*} [Monoid S]
    [DistribMulAction S A] [SMulCommClass ℤ S A] (c : Fin n → ℤ) (r : S) (z : Fin n → A) :
    pair c (r • z) = r • pair c z := by
  simp only [pair, Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => smul_comm (c i) r (z i)

private theorem Λ_add {A : Type*} [AddCommGroup A] (z z' : Fin n → A) :
    Λ g (z + z') = Λ g z + Λ g z' := by
  funext k; exact pair_add_right _ _ _

private theorem Λ_smul {A : Type*} [AddCommGroup A] {S : Type*} [Monoid S] [DistribMulAction S A]
    [SMulCommClass ℤ S A] (r : S) (z : Fin n → A) : Λ g (r • z) = r • Λ g z := by
  funext k; exact pair_smul_right _ _ _

private theorem int_tf : ∀ (a : ℤ) (x : ℤ), a ≠ 0 → a • x = 0 → x = 0 := fun a x ha h => by
  rw [smul_eq_mul] at h; exact (mul_eq_zero.1 h).resolve_left ha

private theorem field_tf (K : Type*) [Field K] [CharZero K] :
    ∀ (a : ℤ) (x : K), a ≠ 0 → a • x = 0 → x = 0 := fun a x ha h => by
  rw [zsmul_eq_mul] at h; exact (mul_eq_zero.1 h).resolve_left (Int.cast_ne_zero.2 ha)

private noncomputable def coordZlin :
    parabolicHoms ℤ Γ ℤ →ₗ[ℤ] (Fin (t g) → ℤ) where
  toFun φ := Λ g (ev g (φ : Additive Γ →+ ℤ))
  map_add' φ ψ := by
    show Λ g (ev g ((φ : Additive Γ →+ ℤ) + (ψ : Additive Γ →+ ℤ))) = _
    rw [← Λ_add]; rfl
  map_smul' m φ := by
    show Λ g (ev g (m • (φ : Additive Γ →+ ℤ))) = m • Λ g (ev g (φ : Additive Γ →+ ℤ))
    rw [← Λ_smul]; rfl

private noncomputable def coordZ (hg : Subgroup.closure (Set.range g) = ⊤) :
    parabolicHoms ℤ Γ ℤ ≃ₗ[ℤ] (Fin (t g) → ℤ) :=
  LinearEquiv.ofBijective (coordZlin g) (coord_bijective g hg int_tf)

private theorem coordZ_apply (hg : Subgroup.closure (Set.range g) = ⊤)
    (φ : parabolicHoms ℤ Γ ℤ) :
    coordZ g hg φ = Λ g (ev g (φ : Additive Γ →+ ℤ)) := rfl

private noncomputable def coordKlin (K : Type*) [Field K] :
    parabolicHoms K Γ K →ₗ[K] (Fin (t g) → K) where
  toFun φ := Λ g (ev g (φ : Additive Γ →+ K))
  map_add' φ ψ := by
    show Λ g (ev g ((φ : Additive Γ →+ K) + (ψ : Additive Γ →+ K))) = _
    rw [← Λ_add]; rfl
  map_smul' r φ := by
    show Λ g (ev g (r • (φ : Additive Γ →+ K))) = r • Λ g (ev g (φ : Additive Γ →+ K))
    rw [← Λ_smul]; rfl

private theorem coordK_bijective (hg : Subgroup.closure (Set.range g) = ⊤) (K : Type*)
    [Field K] [CharZero K] : Function.Bijective (coordKlin g K) := by
  have hb := coord_bijective g hg (field_tf K)
  refine ⟨fun φ ψ h => ?_, fun y => ?_⟩
  · have key := @hb.1
      ⟨(φ : Additive Γ →+ K), φ.2⟩
      ⟨(ψ : Additive Γ →+ K), ψ.2⟩ h
    exact Subtype.ext (congrArg Subtype.val key)
  · obtain ⟨φ, hφ⟩ := hb.2 y
    exact ⟨⟨(φ : Additive Γ →+ K), φ.2⟩, hφ⟩

private noncomputable def coordK (hg : Subgroup.closure (Set.range g) = ⊤) (K : Type*)
    [Field K] [CharZero K] : parabolicHoms K Γ K ≃ₗ[K] (Fin (t g) → K) :=
  LinearEquiv.ofBijective (coordKlin g K) (coordK_bijective g hg K)

private theorem coordK_apply (hg : Subgroup.closure (Set.range g) = ⊤) (K : Type*) [Field K]
    [CharZero K] (φ : parabolicHoms K Γ K) :
    coordK g hg K φ = Λ g (ev g (φ : Additive Γ →+ K)) := rfl

private theorem castAddHom_comp_mem (K : Type*) [Field K] {φ : Additive Γ →+ ℤ}
    (hφ : φ ∈ parabolicHoms ℤ Γ ℤ) :
    (Int.castAddHom K).comp φ ∈ parabolicHoms K Γ K := by
  intro γ hγ
  show ((φ (Additive.ofMul γ) : ℤ) : K) = 0
  rw [hφ γ hγ, Int.cast_zero]

private theorem main (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℤ (ModularCurve.Period.parabolicHoms ℤ Γ ℤ)),
      ∀ (K : Type*) [Field K] [CharZero K],
        ∃ bK : Module.Basis (Fin n) K (ModularCurve.Period.parabolicHoms K Γ K),
          ∀ i, (bK i : Additive Γ →+ K) = (Int.castAddHom K).comp (b i : Additive Γ →+ ℤ) := by
  obtain ⟨n, g, hg⟩ := exists_generators Γ
  refine ⟨t g, Module.Basis.ofEquivFun (coordZ g hg), fun K _ _ =>
    ⟨Module.Basis.ofEquivFun (coordK g hg K), fun i => ?_⟩⟩
  have hmem : (Int.castAddHom K).comp
      ((Module.Basis.ofEquivFun (coordZ g hg) i : parabolicHoms ℤ Γ ℤ) :
        Additive Γ →+ ℤ) ∈ parabolicHoms K Γ K :=
    castAddHom_comp_mem K (Module.Basis.ofEquivFun (coordZ g hg) i).2
  have hcoord : coordK g hg K ⟨_, hmem⟩ = Pi.single i 1 := by
    funext k
    rw [coordK_apply]
    show pair (cLift g k) ((Int.castAddHom K) ∘ ev g
      ((Module.Basis.ofEquivFun (coordZ g hg) i : parabolicHoms ℤ Γ ℤ) :
        Additive Γ →+ ℤ)) = _
    rw [← pair_map]
    rw [show pair (cLift g k) (ev g ((Module.Basis.ofEquivFun (coordZ g hg) i :
        parabolicHoms ℤ Γ ℤ) : Additive Γ →+ ℤ))
        = coordZ g hg (Module.Basis.ofEquivFun (coordZ g hg) i) k from rfl]
    rw [Module.Basis.coe_ofEquivFun, LinearEquiv.apply_symm_apply]
    simp [Pi.single_apply]
  calc ((Module.Basis.ofEquivFun (coordK g hg K) i : parabolicHoms K Γ K) :
        Additive Γ →+ K)
      = (((coordK g hg K).symm (Pi.single i 1) : parabolicHoms K Γ K) :
          Additive Γ →+ K) := by rw [Module.Basis.coe_ofEquivFun]
    _ = _ := by rw [← hcoord, LinearEquiv.symm_apply_apply]

end Main

end BasisField

/-! ### The second headline -/

/-- **The same coordinates over any characteristic-zero field.** The pin's
`ModularCurve.Period.exists_basis_parabolicHoms_castAddHom_comp`: one `ℤ`-basis `b` of
`parabolicHoms ℤ Γ ℤ` whose `Int.castAddHom K`-images are a `K`-basis of
`parabolicHoms K Γ K`, index for index. -/
theorem exists_basis_parabolicHoms_castAddHom_comp (Γ : Subgroup SL(2, ℤ))
    [Γ.FiniteIndex] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℤ (ModularCurve.Period.parabolicHoms ℤ Γ ℤ)),
      ∀ (K : Type*) [Field K] [CharZero K],
        ∃ bK : Module.Basis (Fin n) K (ModularCurve.Period.parabolicHoms K Γ K),
          ∀ i, (bK i : Additive Γ →+ K) = (Int.castAddHom K).comp (b i : Additive Γ →+ ℤ) :=
  BasisField.main Γ

end ModularCurve.Period
