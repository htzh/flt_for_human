/-
The Weil-pairing interface on the `n`-torsion of an affine Weierstrass curve,
after the pinned FLT `Definitions/Def_GaloisRep_WeilPairing.lean`
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_GaloisRep_WeilPairing.lean>),
40 lines / 2 declarations.

The pin does not construct the elliptic-curve pairing: it *assumes its laws*
existentially and proves things from the laws. `IsWeilPairing S W' n B` is a
`Prop`-valued structure whose six fields are the six defining laws of the pairing
on `Submodule.torsionBy ℤ (W'⁄K).Point n` with values in `Kˣ`:

* `mem_rootsOfUnity` — values are `n`-th roots of unity;
* `add_left` / `add_right` — bi-additivity;
* `alternate` — `B P P = 1`;
* `equivariant` — Galois-equivariance of `S`-linear automorphisms;
* `nondegenerate` — the form is not identically `1`.

`HasWeilPairing S K W' n` is the existential `∃ B, IsWeilPairing S W' n B`.

Imports the port's `GaloisRep/Defs/GaloisAction.lean` for the `K ≃ₐ[S] K`-action
on `(W'⁄K).Point` (the pin's `import Definitions.Def_FreyPackage_GaloisRep` is
replaced by the specific import). Statements are transcribed verbatim from the
pin; its `import Mathlib` is replaced by specific imports.

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_GaloisRep_WeilPairing.lean>
-/
import FLTForHuman.GaloisRep.Defs.GaloisAction
import Mathlib.RingTheory.RootsOfUnity.Basic

set_option autoImplicit false

namespace WeierstrassCurve.Affine.Point

open WeierstrassCurve

universe r s v

variable {R : Type r} {S : Type s} {K : Type v} [CommRing R] [CommRing S] [Field K]
  [DecidableEq K] {W' : Affine R} [Algebra R S] [Algebra R K] [Algebra S K]
  [IsScalarTower R S K]

variable (S) in

structure IsWeilPairing (W' : Affine R) (n : ℕ)
    (B : Submodule.torsionBy ℤ (W'⁄K).Point n → Submodule.torsionBy ℤ (W'⁄K).Point n → Kˣ) :
    Prop where

  mem_rootsOfUnity : ∀ P Q, B P Q ∈ rootsOfUnity n K

  add_left : ∀ P P' Q, B (P + P') Q = B P Q * B P' Q

  add_right : ∀ P Q Q', B P (Q + Q') = B P Q * B P Q'

  alternate : ∀ P, B P P = 1

  equivariant : ∀ (σ : K ≃ₐ[S] K) (P Q), σ ((B P Q : Kˣ) : K) = ((B (σ • P) (σ • Q) : Kˣ) : K)

  nondegenerate : ∃ P Q, B P Q ≠ 1

variable (S K) in

def HasWeilPairing (W' : Affine R) (n : ℕ) : Prop :=
  ∃ B : Submodule.torsionBy ℤ (W'⁄K).Point n → Submodule.torsionBy ℤ (W'⁄K).Point n → Kˣ,
    IsWeilPairing S W' n B

end WeierstrassCurve.Affine.Point
