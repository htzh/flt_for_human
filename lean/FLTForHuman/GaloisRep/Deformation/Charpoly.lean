/-
  Characteristic-polynomial rigidity under a ring endomorphism, and the descent of a
  matrix group homomorphism to a subring.

  Piece one of the pin node
  `Representation.exists_conj_eq_map_of_charpoly_coeff_mem_range_of_finite_of_span_range_eq_top`
  (pinned `aa2d8b3`), taken whole: pin lines 31–316, the `section PieceCS` and `section PieceNS`
  of the `S_` file. The node is one development in six pieces; it is re-cut here by piece
  *group* into three modules (§4 of the work order), this one holding charpoly fixing and the
  Galois twist (`PieceCS`) plus the descent carrier (`PieceNS`) that the other two consume.

  What it establishes. `Matrix.charpolyRev_map` transports the reversed characteristic
  polynomial along a ring hom, so a ring endomorphism `σ` that fixes every coefficient of
  `M.charpolyRev` fixes `(M.map σ).charpolyRev` — `charpolyRev_map_eq_of_coeff_fixed` — and the
  same statement for `charpoly` (`charpoly_map_eq_of_coeff_fixed`, through mathlib's
  `Matrix.charpoly_map`). `CharpolyCoeffsInSubfield φ k` records coefficientwise membership of
  every `φ g`'s reversed charpoly in a subring `k ⊆ k'`; `charpolyCoeffsInSubfield_of_frobeniusCoverage`
  discharges it from a covering set, and the two `*_galoisTwist_eq_of_coeffsInSubfield` lemmas turn
  the subfield hypothesis into twist-invariance of the characteristic polynomial — hypothesis (2)
  of the Brauer–Nesbitt clause below. `SubfieldDescentInputs φ k` is the pin's two-field interface
  (`brauerNesbitt`, `noSchurIndex`), and `lemma613_of_subfieldDescentInputs` is the descent step:
  the two fields together produce `ρ : G →* GL n k` and a conjugator with
  `Q⁻¹ * φ g * Q = (ρ g).map k.subtype`.

  The descent carrier. `Matrix.subringPreimage` moves a matrix with all entries in a subring down
  to the subring (`map_subringPreimage`, `subringPreimage_apply`, and injectivity of `M ↦ M.map
  k.subtype`); `subringDescentMatMap` / `subringDescentMonoidHom` / `subringDescentHom` reassemble
  a `ψ : G →* GL n k'` whose entries all lie in `k` into a `G →* GL n k`, with the coercion
  identities `map_subringDescentMatMap`, `map_subringDescentMonoidHom`, `coe_subringDescentHom`.
  `conjRep φ Q` is the conjugated representation `g ↦ Q⁻¹ * φ g * Q`, and
  `noSchurIndex_of_conjugatorIntoSubring` reads a conjugator with entries in `k` as a descent.
  `DescentConjugatorSupply φ k` is the pin's interface for the second field of
  `SubfieldDescentInputs`: a *single* Galois-twist conjugator whose entries lie in `k`, obtained
  from the twist-conjugators for every `σ` (`entries_mem_of_forall_map_conj_eq` is the
  coefficient-fixing criterion used by the finite-field wire).

  Source (pinned `aa2d8b3`):
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_Representation_exists_conj_eq_map_of_charpoly_coeff_mem_range_of_finite_of_span_range_eq_top.lean#L31-L316>
  and the statement authority
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_Representation_exists_conj_eq_map_of_charpoly_coeff_mem_range_of_finite_of_span_range_eq_top.lean>
  (the headline lands in `FiniteDescent.lean`; this module carries the pin's 25 public
  declarations of those two pieces and two of its eleven `private` helpers).

  Assumes: mathlib `v4.34.0` only — nothing from earlier modules of the port. The pin's
  `namespace Deformation` block (`matrixRepresentation`, `matrixRepresentation_apply`) is a copy
  of `Definitions/Def_Deformations_MatrixRepresentation.lean`, already public in
  `FLTForHuman/GaloisRep/Defs/MatrixRepresentation.lean`; it is not restated here and neither
  declaration is in this module's surface.

  Mathlib-first (2026-10-20, `rg` under `.lake/packages/mathlib/Mathlib`):
  * `Matrix.map_injective_of_injective` — **hit**, the statement is mathlib's `Matrix.map_injective`
    (`LinearAlgebra/Matrix/Defs.lean:155`); the proof is that lemma, and the private
    `map_subtype_injective` uses it directly as well;
  * `Matrix.charpolyRev_map` (private) — **negative**: mathlib has `Matrix.charpoly_map`
    (`LinearAlgebra/Matrix/Charpoly/Basic.lean:175`) and `Matrix.charpolyRev`
    (`.../Charpoly/Coeff.lean:291`) but no reverse-polynomial transport; the pin's
    `unfold Matrix.charpolyRev` + `RingHom.map_det` proof transcribes unchanged;
  * `charpolyRev_map_eq_of_coeff_fixed`, `charpoly_map_eq_of_coeff_fixed` — **negative** (one-line
    corollaries of the above through `Polynomial.coeff_map`);
  * `subringPreimage` and its three laws, `subringDescent*`, `conjRep`, `CharpolyCoeffsInSubfield`,
    `SubfieldDescentInputs`, `DescentConjugatorSupply` and the theorems built on them — **negative**:
    no subring-descent API for matrix representations in mathlib. The nearest vocabulary is
    conjugation (`MulAut.conj`, `Algebra/Group/End.lean`), which conjugates a group element rather
    than a matrix representation, so `conjRep` is kept as the pin states it.

  Drift against `v4.34.0` — no statement, binder or name changed; 0 warnings:
  * the pin's `p2m_open`/`p2m_export`/`p2m_reactivate`/`p2m_alias` lines and its
    `P2MW.S_…` wrapper namespace are dropped: the declarations sit in the pin's own inner
    namespaces (`Matrix`, `DeligneSerre`), as in the port's `GaloisRep/Deformation` siblings and
    `RepresentationTheory/BrauerNesbitt.lean`. The pin's `p2m_export "Matrix" …` list exists only
    because its `P2M….Matrix` namespace shadowed mathlib's; there is no shadowing here, so the
    export scaffold is not transcribed;
  * `import Mathlib` / `import P2M.Util` are not carried; the import list is the file's own
    (`-DautoImplicit=false` keeps the pin's `set_option autoImplicit false`).

  spec-pin: Theorems/Thm_Representation_exists_conj_eq_map_of_charpoly_coeff_mem_range_of_finite_of_span_range_eq_top.lean
  spec-pin: P2M/Sol/S_Representation_exists_conj_eq_map_of_charpoly_coeff_mem_range_of_finite_of_span_range_eq_top.lean
-/

import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.Tactic.Group

set_option autoImplicit false

universe u v

noncomputable section

open Polynomial Matrix

namespace DeligneSerre

section CharpolyRevMap

variable {R S : Type*} [CommRing R] [CommRing S] {n : Type*} [DecidableEq n] [Fintype n]

private theorem _root_.Matrix.charpolyRev_map (M : Matrix n n R) (f : R →+* S) :
    (M.map f).charpolyRev = M.charpolyRev.map f := by
  unfold Matrix.charpolyRev

  rw [← Polynomial.coe_mapRingHom, RingHom.map_det, RingHom.mapMatrix_apply]
  congr 1
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply,
    smul_eq_mul, coe_mapRingHom, Polynomial.map_sub, Polynomial.map_mul, map_X, map_C,
    apply_ite (Polynomial.map f), Polynomial.map_one, Polynomial.map_zero]

theorem charpolyRev_map_eq_of_coeff_fixed (M : Matrix n n R) (σ : R →+* R)
    (hfix : ∀ i, σ (M.charpolyRev.coeff i) = M.charpolyRev.coeff i) :
    (M.map σ).charpolyRev = M.charpolyRev := by
  rw [Matrix.charpolyRev_map]
  exact Polynomial.ext fun i => by rw [coeff_map]; exact hfix i

theorem charpoly_map_eq_of_coeff_fixed (M : Matrix n n R) (σ : R →+* R)
    (hfix : ∀ i, σ (M.charpoly.coeff i) = M.charpoly.coeff i) :
    (M.map σ).charpoly = M.charpoly := by
  rw [Matrix.charpoly_map]
  exact Polynomial.ext fun i => by rw [coeff_map]; exact hfix i

end CharpolyRevMap

section Clause6121

variable {k' : Type*} [CommRing k'] {n : Type*} [DecidableEq n] [Fintype n]
variable {G : Type*} [Group G]

def CharpolyCoeffsInSubfield (φ : G →* GeneralLinearGroup n k') (k : Subring k') : Prop :=
  ∀ g : G, ∀ i : ℕ, ((φ g : Matrix n n k').charpolyRev.coeff i) ∈ k

theorem charpolyCoeffsInSubfield_of_frobeniusCoverage
    (φ : G →* GeneralLinearGroup n k') (k : Subring k') (S : Set G)
    (hcov : ∀ g : G, ∃ s ∈ S, (φ g : Matrix n n k') = (φ s : Matrix n n k'))
    (hS : ∀ s ∈ S, ∀ i : ℕ, ((φ s : Matrix n n k').charpolyRev.coeff i) ∈ k) :
    CharpolyCoeffsInSubfield φ k := by
  intro g i
  obtain ⟨s, hs, heq⟩ := hcov g
  rw [heq]
  exact hS s hs i

theorem charpolyRev_galoisTwist_eq_of_coeffsInSubfield
    (φ : G →* GeneralLinearGroup n k') (k : Subring k')
    (h : CharpolyCoeffsInSubfield φ k) (σ : k' →+* k') (hσ : ∀ x ∈ k, σ x = x) (g : G) :
    ((φ g : Matrix n n k').map σ).charpolyRev = (φ g : Matrix n n k').charpolyRev :=
  charpolyRev_map_eq_of_coeff_fixed _ σ (fun i => hσ _ (h g i))

theorem charpoly_galoisTwist_eq_of_coeffsInSubfield
    (φ : G →* GeneralLinearGroup n k') (k : Subring k')
    (h : ∀ g i, ((φ g : Matrix n n k').charpoly.coeff i) ∈ k)
    (σ : k' →+* k') (hσ : ∀ x ∈ k, σ x = x) (g : G) :
    ((φ g : Matrix n n k').map σ).charpoly = (φ g : Matrix n n k').charpoly :=
  charpoly_map_eq_of_coeff_fixed _ σ (fun i => hσ _ (h g i))

end Clause6121

section Lemma613

variable {k' : Type*} [Field k'] {n : Type*} [DecidableEq n] [Fintype n]
variable {G : Type*} [Group G]

structure SubfieldDescentInputs (φ : G →* GeneralLinearGroup n k') (k : Subring k') : Prop where

  brauerNesbitt : ∀ σ : k' →+* k', (∀ x ∈ k, σ x = x) →
    (∀ g, ((φ g : Matrix n n k').map σ).charpoly = (φ g : Matrix n n k').charpoly) →
    ∃ Q : GeneralLinearGroup n k', ∀ g,
      (Q⁻¹ * φ g * Q : Matrix n n k') = (φ g : Matrix n n k').map σ

  noSchurIndex : (∀ σ : k' →+* k', (∀ x ∈ k, σ x = x) →
      ∃ Q : GeneralLinearGroup n k', ∀ g,
        (Q⁻¹ * φ g * Q : Matrix n n k') = (φ g : Matrix n n k').map σ) →
    ∃ ρ : G →* GeneralLinearGroup n k, ∃ Q : GeneralLinearGroup n k',
      ∀ g, (Q⁻¹ * φ g * Q : Matrix n n k') = (ρ g : Matrix n n k).map (k.subtype)

theorem lemma613_of_subfieldDescentInputs (φ : G →* GeneralLinearGroup n k') (k : Subring k')
    (h6121 : ∀ g i, ((φ g : Matrix n n k').charpoly.coeff i) ∈ k)
    (hinputs : SubfieldDescentInputs φ k) :
    ∃ ρ : G →* GeneralLinearGroup n k, ∃ Q : GeneralLinearGroup n k',
      ∀ g, (Q⁻¹ * φ g * Q : Matrix n n k') = (ρ g : Matrix n n k).map (k.subtype) := by
  refine hinputs.noSchurIndex (fun σ hσ => ?_)

  exact hinputs.brauerNesbitt σ hσ
    (charpoly_galoisTwist_eq_of_coeffsInSubfield φ k h6121 σ hσ)

end Lemma613

end DeligneSerre


open Matrix

namespace Matrix

open Matrix

variable {R : Type*} [Ring R] {n m : Type*}

def subringPreimage (k : Subring R) (M : Matrix n m R) (hM : ∀ i j, M i j ∈ k) :
    Matrix n m k :=
  fun i j => ⟨M i j, hM i j⟩

@[scoped simp]
theorem map_subringPreimage (k : Subring R) (M : Matrix n m R) (hM : ∀ i j, M i j ∈ k) :
    (subringPreimage k M hM).map (k.subtype) = M :=
  rfl

@[scoped simp]
theorem subringPreimage_apply (k : Subring R) (M : Matrix n m R) (hM : ∀ i j, M i j ∈ k)
    (i : n) (j : m) : (subringPreimage k M hM i j : R) = M i j :=
  rfl

theorem map_injective_of_injective {α β : Type*} {f : α → β}
    (hf : Function.Injective f) :
    Function.Injective (fun M : Matrix n m α => M.map f) :=
  Matrix.map_injective hf

end Matrix

namespace DeligneSerre

variable {k' : Type*} [Field k'] {n : Type*} [DecidableEq n] [Fintype n]
variable {G : Type*} [Group G]

section Engine

variable (ψ : G →* GeneralLinearGroup n k') (k : Subring k')
  (hψ : ∀ g i j, (ψ g : Matrix n n k') i j ∈ k)

def subringDescentMatMap : G → Matrix n n k :=
  fun g => Matrix.subringPreimage k (ψ g : Matrix n n k') (hψ g)

theorem map_subringDescentMatMap (g : G) :
    (subringDescentMatMap ψ k hψ g).map k.subtype = (ψ g : Matrix n n k') :=
  rfl

omit [DecidableEq n] [Fintype n] in

private theorem map_subtype_injective :
    Function.Injective (fun M : Matrix n n k => M.map (k.subtype)) :=
  Matrix.map_injective k.subtype_injective

def subringDescentMonoidHom : G →* Matrix n n k where
  toFun := subringDescentMatMap ψ k hψ
  map_one' := map_subtype_injective k <| by
    show (subringDescentMatMap ψ k hψ 1).map k.subtype = (1 : Matrix n n k).map k.subtype
    rw [map_subringDescentMatMap, map_one, Units.val_one,
      Matrix.map_one (k.subtype) (map_zero _) (map_one _)]
  map_mul' g g' := map_subtype_injective k <| by
    show (subringDescentMatMap ψ k hψ (g * g')).map k.subtype =
      (subringDescentMatMap ψ k hψ g * subringDescentMatMap ψ k hψ g').map k.subtype
    rw [map_subringDescentMatMap, Matrix.map_mul, map_subringDescentMatMap,
      map_subringDescentMatMap, map_mul, Units.val_mul]

@[scoped simp]
theorem map_subringDescentMonoidHom (g : G) :
    ((subringDescentMonoidHom ψ k hψ g : Matrix n n k).map k.subtype) =
      (ψ g : Matrix n n k') :=
  rfl

def subringDescentHom : G →* GeneralLinearGroup n k :=
  (subringDescentMonoidHom ψ k hψ).toHomUnits

@[scoped simp]
theorem coe_subringDescentHom (g : G) :
    ((subringDescentHom ψ k hψ g : Matrix n n k).map k.subtype) =
      (ψ g : Matrix n n k') :=
  rfl

end Engine

section SeamEngine

variable (φ : G →* GeneralLinearGroup n k') (k : Subring k')

def conjRep (Q : GeneralLinearGroup n k') : G →* GeneralLinearGroup n k' where
  toFun g := Q⁻¹ * φ g * Q
  map_one' := by simp
  map_mul' g g' := by simp only [map_mul]; group

@[scoped simp]
theorem conjRep_apply (Q : GeneralLinearGroup n k') (g : G) :
    conjRep φ Q g = Q⁻¹ * φ g * Q := rfl

theorem noSchurIndex_of_conjugatorIntoSubring
    (Q : GeneralLinearGroup n k')
    (hQ : ∀ g i j, (Q⁻¹ * φ g * Q : Matrix n n k') i j ∈ k) :
    ∃ ρ : G →* GeneralLinearGroup n k, ∃ Q' : GeneralLinearGroup n k',
      ∀ g, (Q'⁻¹ * φ g * Q' : Matrix n n k') = (ρ g : Matrix n n k).map (k.subtype) := by

  have hψ : ∀ g i j, (conjRep φ Q g : Matrix n n k') i j ∈ k := by
    intro g i j

    show ((Q⁻¹ * φ g * Q : GeneralLinearGroup n k') : Matrix n n k') i j ∈ k
    simp only [Units.val_mul] at hQ ⊢
    exact hQ g i j
  refine ⟨subringDescentHom (conjRep φ Q) k hψ, Q, fun g => ?_⟩
  rw [coe_subringDescentHom, conjRep_apply]
  simp only [Units.val_mul]

end SeamEngine

section Carrier

variable (φ : G →* GeneralLinearGroup n k') (k : Subring k')

def DescentConjugatorSupply : Prop :=
  (∀ σ : k' →+* k', (∀ x ∈ k, σ x = x) →
      ∃ Q : GeneralLinearGroup n k', ∀ g,
        (Q⁻¹ * φ g * Q : Matrix n n k') = (φ g : Matrix n n k').map σ) →
    ∃ Q : GeneralLinearGroup n k',
      ∀ g i j, (Q⁻¹ * φ g * Q : Matrix n n k') i j ∈ k

theorem noSchurIndex_of_descentConjugatorSupply (hsupply : DescentConjugatorSupply φ k) :
    (∀ σ : k' →+* k', (∀ x ∈ k, σ x = x) →
        ∃ Q : GeneralLinearGroup n k', ∀ g,
          (Q⁻¹ * φ g * Q : Matrix n n k') = (φ g : Matrix n n k').map σ) →
      ∃ ρ : G →* GeneralLinearGroup n k, ∃ Q : GeneralLinearGroup n k',
        ∀ g, (Q⁻¹ * φ g * Q : Matrix n n k') = (ρ g : Matrix n n k).map (k.subtype) := by
  intro hconj
  obtain ⟨Q, hQ⟩ := hsupply hconj
  exact noSchurIndex_of_conjugatorIntoSubring φ k Q hQ

theorem subfieldDescentInputs_of_supply
    (hBN : ∀ σ : k' →+* k', (∀ x ∈ k, σ x = x) →
      (∀ g, ((φ g : Matrix n n k').map σ).charpoly = (φ g : Matrix n n k').charpoly) →
      ∃ Q : GeneralLinearGroup n k', ∀ g,
        (Q⁻¹ * φ g * Q : Matrix n n k') = (φ g : Matrix n n k').map σ)
    (hsupply : DescentConjugatorSupply φ k) :
    SubfieldDescentInputs φ k where
  brauerNesbitt := hBN
  noSchurIndex := noSchurIndex_of_descentConjugatorSupply φ k hsupply

end Carrier

section BrauerConnection

theorem entries_mem_of_forall_map_conj_eq
    (φ : G →* GeneralLinearGroup n k') (k : Subring k') (Q : GeneralLinearGroup n k')
    (hQ : ∀ σ : k' →+* k', (∀ x ∈ k, σ x = x) →
      ∀ g, (Q⁻¹ * φ g * Q : Matrix n n k') =
        ((Q⁻¹ * φ g * Q : GeneralLinearGroup n k') : Matrix n n k').map σ)
    (hfix : ∀ x : k', (∀ σ : k' →+* k', (∀ y ∈ k, σ y = y) → σ x = x) → x ∈ k) :
    ∀ g i j, (Q⁻¹ * φ g * Q : Matrix n n k') i j ∈ k := by
  intro g i j
  refine hfix _ (fun σ hσ => ?_)
  have h := hQ σ hσ g

  have hentry : (Q⁻¹ * φ g * Q : Matrix n n k') i j =
      σ ((Q⁻¹ * φ g * Q : Matrix n n k') i j) := by
    conv_lhs => rw [h]
    simp only [Units.val_mul, Matrix.map_apply]
  exact hentry.symm

end BrauerConnection

end DeligneSerre

end
