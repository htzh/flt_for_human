/-
The Velo quotient after a residue map.

`WeierstrassCurve.exists_map_eq_veluQuotient_and_map_residue_eq_veluQuotient_reduceHom`: for a
`WeierstrassCurve A` over a valuation subring whose reduction is smooth and a residue field in which
`ℓ ≠ 0`, a point `Q` of order `ℓ` and `n < ℓ`, the quotient of `W` by the odd-order summing set
descends to `A` with the *same* reduction as the quotiented model — the map is both the base-change
of the Velo quotient and the reduction of a Velo quotient.

The definition layer is ported (`Def_WeierstrassCurve_{Velu,OddOrderSummingSet,ReduceHom}`:
29/30, 5/5, 17/18 public, the misses being structure fields), so this is a proof order and not a
gate. Home `WeierstrassCurve/Velu/Reduction.lean` (new; the `Velu/` directory has the quotient
calculus but no reduction module).

## The row

* `WeierstrassCurve.exists_map_eq_veluQuotient_and_map_residue_eq_veluQuotient_reduceHom` — 194 pin
  `S_` lines, transcribed below (`S_…:112–194` is the proof body; the helpers are `S_…:52–106`).

## The base-change prelude: transcribed, not imported

The pin's `VeluIntegralModel` block of five base-change lemmas (`S_…:14–50`) is **transcribed
`private` here at the pin's statements** (`map_veluT`, `map_veluW`, `map_veluTSum`, `map_veluWSum`,
`veluQuotient_map`, in the `section Velu` below; the pin's `VeluIntegralModel` scaffold label is
dropped).

*They are byte-identical copies of the port's public `TDescent.map_veluT` / `map_veluW` /
`map_veluTSum` / `map_veluWSum` / `veluQuotient_map`, in
`FLTForHuman/ModularCurve/ModularPolynomialVelu.lean`.*  They are **not** imported from there, on
purpose: `ModularPolynomialVelu` itself imports eight `WeierstrassCurve` modules, so a
`WeierstrassCurve/Velu/*` module importing it would put the Weierstrass layer above the modular-curve
layer — an import-direction inversion that every later consumer of `Velu/Reduction` would inherit.
The duplication is a **refactor-round item**: move those five rows down to a Weierstrass-level
module (they only need `WeierstrassCurve.veluT/veluW/veluTSum/veluWSum/veluQuotient`, i.e.
`Velu/Formula.lean`'s layer) and import them from both `ModularPolynomialVelu` and here.  Registered
in CARRY-FORWARD by the manager; the five rows below are then a deletion, not a change.

Read against the bodies (FR-0266): the five `TDescent` statements are stated for the
**`WeierstrassCurve`** Velo data (`W.veluT`, `W.veluQuotient T`, `W.map φ`) with the pin's own
`Set.InjOn (Prod.map φ φ) T` hypothesis — *not* for the modular-polynomial data the module's name
suggests — which is exactly why the copies below are verbatim.  (The *other* base-change block in the
port, `WeierstrassCurve.map_veluT` … `map_veluQuotient` in `Velu/Formula.lean`, is a different
statement pair and is not used here: it is stated in the opposite direction
(`(W.map f).veluT (f x) (f y) = f (W.veluT x y)`) with a global `Function.Injective f` and
`Finset.map` instead of the pin's `Set.InjOn` / `Finset.image`.  The copies below also shadow those
public names inside this file, which is harmless: this module needs only the pin's direction.)

The four remaining helpers (`eq_of_coordsOrZero_eq`, `nsmul_injOn_of_lt`, `reduceHom_injOn`,
`addOrderOf_reduceHom`) are transcribed at the pin's leaf names and made `public`, as in the pin.
`reduceHom_injOn` has a port-**`private`** twin (`WeierstrassCurve.reduceHom_injOn'`,
`Reduction/ReduceHomSurjective.lean:49`, the same proof at the same statement up to the
section-variable order); a `private` declaration is not importable, so the row is transcribed here
rather than substituted, and the twin stays where it is — its promotion is a carry-forward item.

`X_mem_of_nsmul_eq_zero'` (`Reduction/TorsionIntegral.lean:1159`), `reducePoint_some_of_mem`,
`Affine.Y_mem_of_X_mem`, `oddOrderSummingSet` (`Velu/Defs.lean:264`) and `reduceHom`
(`Reduction/ReduceHom.lean:496`) are imported, never redeclared.

The pin's `import Mathlib` is replaced by the specific imports below; the pin sets no `set_option`
and none is transcribed.  Nothing is silenced: the module is warning-free at the 200k cap.

**Engine diff** (pin-vs-module declaration diff, last-name indexed): 11 pin declarations over the
module's two `spec-pin:` sources, **10** module declarations; **10 by statement hash, 0 by name only,
0 unaccounted** — the five base-change copies included (they are statement-identical to the pin's
`VeluIntegralModel` rows).

**Gates.**  `check_port --force`: **5 ok, 0 mismatch, 0 missing, 0 own, 0 kw** — the four transcribed
helpers and the headline (the five base-change copies are `private`, so the checker skips them by
policy; with their `private` dropped they read `ok` too).  Edit loop silent at
`-DmaxHeartbeats=200000`, and silent at default options (the build's own invocation).  `lake build
FLTForHuman.WeierstrassCurve.Velu.Reduction`: no warning from this file.  `#print axioms` on all five
public declarations: `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.  `dedup --within`: 0
clusters (the five copies are `private`; the duplication against `TDescent.*` across modules is the
carry-forward item above).  `move_dead --dry-run`: 0 declarations, 0 lines.

**Heartbeat probe pair (measured, never installed).**  Silent at `-DmaxHeartbeats=100000`, `40000`,
`20000`, `10000`; first failure at `5000`, a `transform` timeout inside the headline's `hTinj` block
(`rw [hr h₁ hx₁ hP₁, hr h₂ hx₂ hP₂] at heq`), and at `1000` it fails earlier still, at `isDefEq`
inside the transcribed `map_veluT` (`simp`).  So the bisector is 5000/10000, inside the headline
proof, an order of magnitude under the 200k edit-loop cap.  No `set_option maxHeartbeats` is
installed.

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_exists_map_eq_veluQuotient_and_map_residue_eq_veluQuotient_reduceHom.lean>

spec-pin: Theorems/Thm_WeierstrassCurve_exists_map_eq_veluQuotient_and_map_residue_eq_veluQuotient_reduceHom.lean
spec-pin: P2M/Sol/S_WeierstrassCurve_exists_map_eq_veluQuotient_and_map_residue_eq_veluQuotient_reduceHom.lean
-/

import FLTForHuman.WeierstrassCurve.Reduction.ReduceHom
import FLTForHuman.WeierstrassCurve.Velu.CyclicQuotientJ
import FLTForHuman.WeierstrassCurve.Velu.Defs
import FLTForHuman.WeierstrassCurve.Velu.OddOrder
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Tactic

open WeierstrassCurve IsLocalRing

set_option autoImplicit false

noncomputable section

section Velu

variable {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (W : WeierstrassCurve R)

private theorem map_veluT (x y : R) : φ (W.veluT x y) = (W.map φ).veluT (φ x) (φ y) := by
  simp [WeierstrassCurve.veluT, WeierstrassCurve.veluGx, WeierstrassCurve.veluGy, map_ofNat]

private theorem map_veluW (x y : R) : φ (W.veluW x y) = (W.map φ).veluW (φ x) (φ y) := by
  simp [WeierstrassCurve.veluW, WeierstrassCurve.veluU, WeierstrassCurve.veluT,
    WeierstrassCurve.veluGx, WeierstrassCurve.veluGy, map_ofNat]

variable [DecidableEq S]

private theorem map_veluTSum (T : Finset (R × R)) (hφ : Set.InjOn (Prod.map φ φ) T) :
    φ (W.veluTSum T) = (W.map φ).veluTSum (T.image (Prod.map φ φ)) := by
  rw [WeierstrassCurve.veluTSum, WeierstrassCurve.veluTSum, Finset.sum_image hφ, map_sum]
  exact Finset.sum_congr rfl fun P _ => map_veluT φ W P.1 P.2

private theorem map_veluWSum (T : Finset (R × R)) (hφ : Set.InjOn (Prod.map φ φ) T) :
    φ (W.veluWSum T) = (W.map φ).veluWSum (T.image (Prod.map φ φ)) := by
  rw [WeierstrassCurve.veluWSum, WeierstrassCurve.veluWSum, Finset.sum_image hφ, map_sum]
  exact Finset.sum_congr rfl fun P _ => map_veluW φ W P.1 P.2

private theorem veluQuotient_map (T : Finset (R × R)) (hφ : Set.InjOn (Prod.map φ φ) T) :
    (W.veluQuotient T).map φ = (W.map φ).veluQuotient (T.image (Prod.map φ φ)) := by
  ext
  · rfl
  · rfl
  · rfl
  · show φ (W.a₄ - 5 * W.veluTSum T) = _
    rw [WeierstrassCurve.veluQuotient_a₄, map_sub, map_mul, map_ofNat, map_veluTSum φ W T hφ]
    rfl
  · show φ (W.a₆ - W.b₂ * W.veluTSum T - 7 * W.veluWSum T) = _
    rw [WeierstrassCurve.veluQuotient_a₆, map_sub, map_sub, map_mul, map_mul, map_ofNat,
      map_veluTSum φ W T hφ, map_veluWSum φ W T hφ, ← WeierstrassCurve.map_b₂]
    rfl

end Velu

namespace WeierstrassCurve

/-- A non-zero point is determined by its coordinate pair.  (The pin's `VeluIntegralModel`
helper; it needs no `DecidableEq` and no valuation.) -/
theorem eq_of_coordsOrZero_eq {F : Type*} [Field F] {V : WeierstrassCurve F}
    {P Q : V.toAffine.Point} (hP : P ≠ 0) (hQ : Q ≠ 0) (h : P.coordsOrZero = Q.coordsOrZero) :
    P = Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · exact absurd rfl hP
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · exact absurd rfl hQ
  simp only [Affine.Point.coordsOrZero_some, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

/-- Multiples of `g` below the order are injective (the pin's `VeluIntegralModel` helper). -/
theorem nsmul_injOn_of_lt {G : Type*} [AddGroup G] (g : G) {m₁ m₂ : ℕ}
    (h₁ : m₁ < addOrderOf g) (h₂ : m₂ < addOrderOf g) (h : m₁ • g = m₂ • g) : m₁ = m₂ := by
  wlog hle : m₁ ≤ m₂ generalizing m₁ m₂
  · exact (this h₂ h₁ h.symm (le_of_lt (not_le.mp hle))).symm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  have hd : d • g = 0 := by
    rw [add_nsmul] at h
    exact (add_eq_left.mp h.symm)
  have hdvd := addOrderOf_dvd_of_nsmul_eq_zero hd
  rcases Nat.eq_zero_or_pos d with rfl | hdpos
  · rfl
  · exact absurd (Nat.le_of_dvd hdpos hdvd) (by omega)

section Reduce

variable {L : Type*} [Field L] {A : ValuationSubring L} {W : WeierstrassCurve A}
variable [DecidableEq L] [DecidableEq (ResidueField A)] (hΔ : (W.map (residue A)).Δ ≠ 0)

/-- Reduction is injective on the `N`-torsion when `N` is invertible in the residue field
(the pin's `VeluIntegralModel.reduceHom_injOn`). -/
theorem reduceHom_injOn {N : ℕ} (hN : (N : ResidueField A) ≠ 0)
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

/-- The order of a point is preserved by reduction, for `N` invertible in the residue field
(the pin's `VeluIntegralModel.addOrderOf_reduceHom`). -/
theorem addOrderOf_reduceHom {N : ℕ} (hN : (N : ResidueField A) ≠ 0)
    {P : (W.map A.subtype).toAffine.Point} (hP : addOrderOf P = N) :
    addOrderOf (reduceHom hΔ P) = N := by
  apply Nat.dvd_antisymm
  · apply addOrderOf_dvd_of_nsmul_eq_zero
    rw [← map_nsmul, ← hP, addOrderOf_nsmul_eq_zero, map_zero]
  · rw [← hP]
    apply addOrderOf_dvd_of_nsmul_eq_zero
    refine reduceHom_injOn hΔ hN ?_ (smul_zero _) ?_
    · rw [smul_comm, ← hP, addOrderOf_nsmul_eq_zero, smul_zero]
    · rw [map_nsmul, addOrderOf_nsmul_eq_zero, map_zero]

end Reduce

theorem exists_map_eq_veluQuotient_and_map_residue_eq_veluQuotient_reduceHom
    {L : Type*} [Field L] [DecidableEq L] (A : ValuationSubring L) [DecidableEq (ResidueField A)]
    (W : WeierstrassCurve A) (hΔ : (W.map (residue A)).Δ ≠ 0)
    {ℓ : ℕ} (hℓ : (ℓ : ResidueField A) ≠ 0)
    (Q : (W.map A.subtype).toAffine.Point) (hQ : addOrderOf Q = ℓ) {n : ℕ} (hn : n < ℓ) :
    ∃ V : WeierstrassCurve A,
      V.map A.subtype = (W.map A.subtype).veluQuotient ((W.map A.subtype).oddOrderSummingSet Q n) ∧
      V.map (residue A) =
        (W.map (residue A)).veluQuotient ((W.map (residue A)).oddOrderSummingSet (reduceHom hΔ Q) n) := by
  classical
  have hQℓ : ℓ • Q = 0 := by rw [← hQ]; exact addOrderOf_nsmul_eq_zero Q
  have hQ₀ord : addOrderOf (reduceHom hΔ Q) = ℓ := addOrderOf_reduceHom hΔ hℓ hQ

  have hmem : ∀ m : ℕ, 1 ≤ m → m ≤ n → ∃ (x y : L) (h : (W.map A.subtype).toAffine.Nonsingular x y)
      (_ : x ∈ A), m • Q = .some x y h := by
    intro m hm1 hmn
    have hne : m • Q ≠ 0 := by
      intro h0
      have := addOrderOf_dvd_of_nsmul_eq_zero h0
      rw [hQ] at this
      exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
    rcases hP : m • Q with _ | ⟨x, y, h⟩
    · exact absurd hP hne
    · refine ⟨x, y, h, ?_, rfl⟩
      refine WeierstrassCurve.X_mem_of_nsmul_eq_zero' W hℓ h ?_
      rw [← hP, smul_smul, mul_comm, ← smul_smul, hQℓ, smul_zero]

  let sec : L → A := fun z => if hz : z ∈ A then ⟨z, hz⟩ else 0
  have hsec : ∀ {z : L} (hz : z ∈ A), sec z = ⟨z, hz⟩ := fun hz => dite_eq_left hz
  let TA : Finset (A × A) := (Finset.Icc 1 n).image fun m => Prod.map sec sec (m • Q).coordsOrZero

  have hTsub : TA.image (Prod.map A.subtype A.subtype) = (W.map A.subtype).oddOrderSummingSet Q n := by
    simp only [TA, WeierstrassCurve.oddOrderSummingSet, Finset.image_image]
    refine Finset.image_congr fun m hm => ?_
    rw [Finset.mem_coe, Finset.mem_Icc] at hm
    obtain ⟨x, y, h, hx, hP⟩ := hmem m hm.1 hm.2
    have hy : y ∈ A := WeierstrassCurve.Affine.Y_mem_of_X_mem W h.1 hx
    show Prod.map A.subtype A.subtype (Prod.map sec sec (m • Q).coordsOrZero) = (m • Q).coordsOrZero
    rw [hP, Affine.Point.coordsOrZero_some, Prod.map_apply, Prod.map_apply, hsec hx, hsec hy]
    rfl

  have hr : ∀ {m : ℕ} {x y : L} (h : (W.map A.subtype).toAffine.Nonsingular x y) (hx : x ∈ A),
      m • Q = .some x y h →
      Prod.map (residue A) (residue A) (Prod.map sec sec (m • Q).coordsOrZero)
        = (m • reduceHom hΔ Q).coordsOrZero := by
    intro m x y h hx hP
    have hy : y ∈ A := WeierstrassCurve.Affine.Y_mem_of_X_mem W h.1 hx
    rw [← map_nsmul, hP, Affine.Point.coordsOrZero_some, Prod.map_apply, Prod.map_apply, hsec hx, hsec hy]
    show _ = (WeierstrassCurve.reducePoint hΔ (Affine.Point.some x y h)).coordsOrZero
    rw [WeierstrassCurve.reducePoint_some_of_mem hΔ h hx, Affine.Point.coordsOrZero_some]

  have hTres : TA.image (Prod.map (residue A) (residue A)) =
      (W.map (residue A)).oddOrderSummingSet (reduceHom hΔ Q) n := by
    simp only [TA, WeierstrassCurve.oddOrderSummingSet, Finset.image_image]
    refine Finset.image_congr fun m hm => ?_
    rw [Finset.mem_coe, Finset.mem_Icc] at hm
    obtain ⟨x, y, h, hx, hP⟩ := hmem m hm.1 hm.2
    exact hr h hx hP

  have hTinj : Set.InjOn (Prod.map (residue A) (residue A)) ↑TA := by
    intro t₁ ht₁ t₂ ht₂ heq
    rw [Finset.mem_coe] at ht₁ ht₂
    simp only [TA, Finset.mem_image, Finset.mem_Icc] at ht₁ ht₂
    obtain ⟨m₁, hm₁, rfl⟩ := ht₁
    obtain ⟨m₂, hm₂, rfl⟩ := ht₂
    obtain ⟨x₁, y₁, h₁, hx₁, hP₁⟩ := hmem m₁ hm₁.1 hm₁.2
    obtain ⟨x₂, y₂, h₂, hx₂, hP₂⟩ := hmem m₂ hm₂.1 hm₂.2
    rw [hr h₁ hx₁ hP₁, hr h₂ hx₂ hP₂] at heq
    have hne : ∀ {m : ℕ}, 1 ≤ m → m ≤ n → m • reduceHom hΔ Q ≠ 0 := by
      intro m hm1 hmn h0
      have := addOrderOf_dvd_of_nsmul_eq_zero h0
      rw [hQ₀ord] at this
      exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
    have hmm : m₁ = m₂ :=
      nsmul_injOn_of_lt (reduceHom hΔ Q) (by rw [hQ₀ord]; omega) (by rw [hQ₀ord]; omega)
        (eq_of_coordsOrZero_eq (hne hm₁.1 hm₁.2) (hne hm₂.1 hm₂.2) heq)
    rw [hmm]

  refine ⟨W.veluQuotient TA, ?_, ?_⟩
  · rw [← hTsub]
    exact veluQuotient_map A.subtype W TA
      ((Function.Injective.prodMap A.subtype_injective A.subtype_injective).injOn)
  · rw [veluQuotient_map (residue A) W TA hTinj, hTres]

end WeierstrassCurve
