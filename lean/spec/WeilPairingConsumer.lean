/-
  Consumer specification for the Weil-pairing entry points.

  WHAT THIS FILE IS
  -----------------
  A written-down *use* of the two ported Weil-pairing entry points: the six-law
  `IsWeilPairing` interface (`WeilPairing.lean`) and the `weilPairing0`
  construction (`WeilPairingFun.lean`, on the `placeOf`/`transEquiv` slice in
  `Place/PointPlace.lean`). It is a deliverable measure, not a proof obligation.

  It is deliberately **not part of any library**; run it by hand:

      cd lean
      lake env lean spec/WeilPairingConsumer.lean 2>&1 | grep -c error

  The error count is the metric.

  ZONES
  -----
    [interface]   ZONE A — `IsWeilPairing`. A real derivation from the six laws
                  that is *not* one of the fields: bilinearity plus alternation
                  give `B P Q * B Q P = 1`. Deleting `WeilPairing.lean` makes
                  this zone fail.
    [construction] ZONE B — `weilPairing0`. The two definitional branches of
                  `weilPairing0` (`transEquiv_weilFun`, `weilPairing0_of_not`)
                  and the `placeIdeal`/`fibSet` dictionary, composed across
                  `PointPlace.lean` and `WeilPairingFun.lean`. Deleting either
                  module makes this zone fail.
-/

import FLTForHuman.WeierstrassCurve.WeilPairing
import FLTForHuman.WeierstrassCurve.WeilPairingFun
import FLTForHuman.WeierstrassCurve.FibSetFinite

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

namespace WeilPairingConsumer

universe r s v

/-! ### ZONE A — the six-law interface (`WeilPairing.lean`) -/

section Interface

variable {R : Type r} {S : Type s} {K : Type v} [CommRing R] [CommRing S] [Field K]
  [DecidableEq K] {W' : Affine R} [Algebra R S] [Algebra R K] [Algebra S K]
  [IsScalarTower R S K] {n : ℕ}
  {B : Submodule.torsionBy ℤ (W'⁄K).Point n → Submodule.torsionBy ℤ (W'⁄K).Point n → Kˣ}

/-- **Antisymmetry is not a field.** Bilinearity and alternation alone force
`B P Q * B Q P = 1`: expand `B (P+Q) (P+Q)` both ways. This consumes three of
the six fields and is the shape the determinant argument (base/007 §2) uses. -/
example (h : IsWeilPairing S W' n B) (P Q : Submodule.torsionBy ℤ (W'⁄K).Point n) :
    B P Q * B Q P = 1 := by
  have h1 : B (P + Q) (P + Q) = 1 := h.alternate (P + Q)
  have h2 : B (P + Q) (P + Q) = B P (P + Q) * B Q (P + Q) := h.add_left P Q (P + Q)
  have h3 : B P (P + Q) = B P P * B P Q := h.add_right P P Q
  have h4 : B Q (P + Q) = B Q P * B Q Q := h.add_right Q P Q
  rw [h2, h3, h4, h.alternate P, h.alternate Q, one_mul, mul_one] at h1
  exact h1

/-- The existential is inhabited exactly by the six-law structure. -/
example (h : HasWeilPairing S K W' n) :
    ∃ B' : Submodule.torsionBy ℤ (W'⁄K).Point n → Submodule.torsionBy ℤ (W'⁄K).Point n → Kˣ,
      IsWeilPairing S W' n B' := h

end Interface

/-! ### ZONE B — the `weilPairing0` construction (`WeilPairingFun.lean`) -/

section Construction

variable {R : Type*} [Field R] (W : WeierstrassCurve R) (K : Type*) [Field K] [Algebra R K]
  [DecidableEq K]

/-- The `fibSet`/`mem_fibSet` dictionary, consumed across the module boundary. -/
example (n : ℤ) {Q P : (W⁄K).Point} (h : n • P = Q) : P ∈ fibSet W K n Q :=
  (mem_fibSet (W := W) (K := K)).mpr h

/-- `placeIdeal` at a nonzero point is the height-one spectrum of `placeOf`,
which itself is the coordinate-ring ideal of the pin's `Point.xc`/`yc`. -/
example {P : (W⁄K).Point} (hP : P ≠ 0) :
    placeIdeal W K P = (placeOf W K P hP).asIdeal :=
  placeIdeal_of_ne_zero W K hP

/-- The `1` branch of `weilPairing0`, stated in hypothesis form (the pin's
existential failure), consuming `transEquiv`/`weilFun`. -/
example [IsAlgClosed K] [W.IsElliptic] {n : ℤ} {S T : (W⁄K).Point}
    (h : ¬ ∃ c : Kˣ, transEquiv W K S (weilFun W K n T) =
      algebraMap K (W⁄K).FunctionField (c : K) * weilFun W K n T) :
    weilPairing0 W K n S T = 1 :=
  weilPairing0_of_not W K h

/-- The defining branch of `weilPairing0`, consuming both `transEquiv_weilFun`
and the `weilNum` generator lemma through `span_weilNum`. -/
example [IsAlgClosed K] [W.IsElliptic] {n : ℤ} {S T : (W⁄K).Point}
    (h : ∃ c : Kˣ, transEquiv W K S (weilFun W K n T) =
      algebraMap K (W⁄K).FunctionField (c : K) * weilFun W K n T) :
    transEquiv W K S (weilFun W K n T) =
      algebraMap K (W⁄K).FunctionField (weilPairing0 W K n S T : K) * weilFun W K n T :=
  transEquiv_weilFun W K h

/-- Non-vacuity of the construction's generator path: `weilNum` is a generator of
`fibIdeal` whenever that ideal is principal. -/
example {n : ℤ} {T : (W⁄K).Point} (h : (fibIdeal W K n T).IsPrincipal) :
    Ideal.span {weilNum W K n T} = fibIdeal W K n T :=
  span_weilNum W K h

end Construction

/-! ### ZONE C — the `[n]`-fibre finiteness (`FibSetFinite.lean`) -/

section Fibre

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K] [IsAlgClosed K]
  (W : WeierstrassCurve F) [W.IsElliptic]

/-- Every `[n]`-fibre is finite, and the `n`-torsion has `n²` elements: the fibre
dictionary (`fibSet`, `FibSetFinite.lean`) composed across the promoted
`torsion_finite`/`card_torsion_toFinset` and the torsion port. -/
example {n : ℕ} (hn : (n : K) ≠ 0) (Q : (W⁄K).Point) :
    (fibSet W K n Q).Finite ∧ (WeilDiv.torsion_finite W hn).toFinset.card = n ^ 2 :=
  ⟨fibSet_finite W hn Q, WeilDiv.card_torsion_toFinset W hn⟩

end Fibre

end WeilPairingConsumer
