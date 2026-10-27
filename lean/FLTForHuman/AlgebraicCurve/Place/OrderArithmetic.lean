/-
The arithmetic of the order function at a place: prescribing orders at finitely many
places, the ramification index of a prime-degree Kummer cover at a place whose order
is divisible by the degree, and the order of the norm of a unit above a place.

Three statements, each transcribed from its `Theorems/` wrapper (the statement
authority) and proved after the corresponding `P2M/Sol/S_` file of the pinned FLT
(`anthropics/fermats-last-theorem`, `aa2d8b3`).

**Prescribed orders.** A place's order function is a discrete valuation, so for a
finite set `S` of places and any prescribed integers `n v` there is a single `g ≠ 0`
with `v.ord g = n v` at every `v ∈ S`. The proof is the strong-approximation argument
of the pin: for each `v` a separator `t v` is positive at `v` and negative at every
other place of `S` (`exists_separating`, built by induction from
`exists_ord_pos_ord_neg_of_ne` and an exponent large enough to dominate the orders
already prescribed), and `g` is the sum of the `n v`-th powers of the local
uniformisers scaled by `(1 + (t v)^P)⁻¹`, whose order at `v` is exactly `n v` and
which is dominated by the `v`-th term at every other place (`ord_finsetSum_gt`).
Two elementary lemmas carry the estimates: `add_ne_zero_of_ord_lt` and the port's
`Place.ord_add_eq_of_lt`, the strict ultrametric equality.

**Kummer covers.** Let `p` be prime, `α ^ p = f` with `f` not a `p`-th power in `F`
and `F⟮α⟯ = ⊤`, and suppose `p` divides `v.ord f` at every place. Then the cover is
unramified at every rational place of the extension: `w.ramificationIndex F = 1`.
One multiplies `f` by a `p`-th power so that `v.ord f₁ = 0`, replaces `α` by
`β = α * h`, divides by the constant `w.evalAt β`, and compares
`w.ord (β - c)` with the order of the norm `N(β - c) = (-1)^p (c^p - f₁)`: the
ramification index `e` satisfies `e * ord_v(f₂) = w.ord(β - c)`, while the
inequality `w.ord x ≤ ord_v(N x)` for an `x` whose conjugates are all integral
forces `e ≤ 1`.

**Norms of units.** If every place above `v` gives a nonzero `f` the order zero, then
`v.ord (Algebra.norm F f) = 0`: the norm's order is the inertia-weighted sum of the
orders above `v`.

Machine namespace `WC1bSolAW` of the pin is rectified: the prescribed-order
development lives directly in `AlgebraicCurve.Place`.

Wire: `spec/check_port.py` diffs every public declaration of this module against the
pin files named by the `spec-pin:` lines below.

spec-pin: Theorems/Thm_AlgebraicCurve_Place_exists_forall_ord_eq_finset.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_exists_forall_ord_eq_finset.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_Place_ramificationIndex_eq_one_of_forall_dvd_ord.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_ramificationIndex_eq_one_of_forall_dvd_ord.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_Place_ord_norm_eq_zero_of_forall_fiber.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_ord_norm_eq_zero_of_forall_fiber.lean   -- comparable copy
-/
import FLTForHuman.AlgebraicCurve.Defs.Place
import FLTForHuman.AlgebraicCurve.Defs.PlaceCalculus
import FLTForHuman.AlgebraicCurve.Defs.PlaceEvaluation
import FLTForHuman.AlgebraicCurve.Defs.PlaceEvaluationAlgebra
import FLTForHuman.AlgebraicCurve.Defs.PlacesOverDVR
import FLTForHuman.AlgebraicCurve.Defs.PushPull
import FLTForHuman.AlgebraicCurve.Place.OrdCalculus
import FLTForHuman.AlgebraicCurve.PrincipalDivisors.Transcendence
import FLTForHuman.AlgebraicCurve.WeilExchange.FiberOverCount
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.FieldTheory.KummerExtension

set_option autoImplicit false

-- The pin's deprecated primed `Ideal` spellings (`Ideal.inertiaDeg'`) now stay with the
-- imported norm block; the option is kept so that this module's lint surface does not
-- change with that import.
set_option linter.deprecated false

-- The pin's `haveI`/`letI` walls are kept literal.
set_option linter.style.haveILetI false

noncomputable section

open IsDedekindDomain WithZero IsLocalRing UniqueFactorizationMonoid
open Polynomial IntermediateField

namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-! ## The approximation argument -/

/-- **Strict triangle inequality, zero form**: a sum of two elements whose orders
differ cannot vanish. Pin `Place.add_ne_zero_of_ord_lt`, a helper of the
prescribed-order `S_` file. -/
theorem add_ne_zero_of_ord_lt (v : Place K F) {f g : F} (hlt : v.ord f < v.ord g) :
    f + g ≠ 0 := by
  intro h0
  rw [eq_neg_of_add_eq_zero_right h0, v.ord_neg] at hlt
  exact lt_irrefl _ hlt

/-- **Separation of two distinct places by a unit at one of them**: there is a
nonzero element of the first valuation ring outside the second. Pin
`Place.exists_mem_notMem_of_ne`, a helper of the prescribed-order `S_` file. -/
theorem exists_mem_notMem_of_ne {v w : Place K F} (hvw : v ≠ w) :
    ∃ x : F, x ≠ 0 ∧ x ∈ v.toValuationSubring ∧ x ∉ w.toValuationSubring := by
  have hle : ¬(v.toValuationSubring ≤ w.toValuationSubring) := fun hle =>
    hvw (Place.ext (ValuationSubring.eq_of_le_of_ne_top _ hle w.ne_top'))
  obtain ⟨x, hxv, hxw⟩ := SetLike.not_le_iff_exists.mp hle
  exact ⟨x, fun h0 => hxw (h0 ▸ w.toValuationSubring.zero_mem), hxv, hxw⟩

/-- **Two distinct places are separated by an element positive at one and negative
at the other.** Pin `Place.exists_ord_pos_ord_neg_of_ne`, a helper of the
prescribed-order `S_` file. -/
theorem exists_ord_pos_ord_neg_of_ne {v w : Place K F} (hvw : v ≠ w) :
    ∃ z : F, z ≠ 0 ∧ 0 < v.ord z ∧ w.ord z < 0 := by
  obtain ⟨x, hx0, hxv, hxw⟩ := exists_mem_notMem_of_ne hvw
  obtain ⟨y, hy0, hyw, hyv⟩ := exists_mem_notMem_of_ne hvw.symm
  have hy0' : y⁻¹ ≠ 0 := inv_ne_zero hy0
  refine ⟨x * y⁻¹, mul_ne_zero hx0 hy0', ?_, ?_⟩
  · rw [v.ord_mul hx0 hy0', v.ord_inv]
    have h1 := v.ord_nonneg_of_mem hxv
    have h2 := (not_mem_iff_ord_neg v hy0).mp hyv
    omega
  · rw [w.ord_mul hx0 hy0', w.ord_inv]
    have h1 := (not_mem_iff_ord_neg w hx0).mp hxw
    have h2 := w.ord_nonneg_of_mem hyw
    omega

/-- **A finite sum of terms all of order `> m` either vanishes or has order `> m`.**
Pin `Place.ord_finsetSum_gt`, a helper of the prescribed-order `S_` file. -/
theorem ord_finsetSum_gt {ι : Type*} (v : Place K F) (s : Finset ι) (g : ι → F) (m : ℤ) :
    (∀ i ∈ s, g i ≠ 0 ∧ m < v.ord (g i)) →
      s.sum g = 0 ∨ (s.sum g ≠ 0 ∧ m < v.ord (s.sum g)) := by
  classical
  induction s using Finset.cons_induction with
  | empty => exact fun _ => Or.inl Finset.sum_empty
  | cons i s hi ih =>
      intro h
      rw [Finset.sum_cons]
      obtain ⟨hgi0, hgim⟩ := h i (Finset.mem_cons.mpr (Or.inl rfl))
      rcases ih (fun j hj => h j (Finset.mem_cons.mpr (Or.inr hj))) with h0 | ⟨hne, hlt⟩
      · rw [h0, add_zero]
        exact Or.inr ⟨hgi0, hgim⟩
      · rcases eq_or_ne (g i + s.sum g) 0 with hz | hz
        · exact Or.inl hz
        · refine Or.inr ⟨hz, ?_⟩
          exact lt_of_lt_of_le (lt_min hgim hlt) (v.min_ord_le_ord_add hz)

/-- **Separating a finite set of places from one place**: an element of positive
order at `v` and negative order at every other place of `S`. Pin
`Place.exists_separating`, a helper of the prescribed-order `S_` file. -/
theorem exists_separating (v : Place K F) (S : Finset (Place K F)) :
    ∃ t : F, t ≠ 0 ∧ 0 < v.ord t ∧ ∀ w ∈ S, w ≠ v → w.ord t < 0 := by
  classical
  induction S using Finset.cons_induction with
  | empty =>
      obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
      have hπ0 : (π : F) ≠ 0 := by
        simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
      refine ⟨(π : F), hπ0, ?_, fun w hw => absurd hw (Finset.notMem_empty w)⟩
      rw [v.ord_coe_irreducible hπ]
      omega
  | cons w₀ S' hw₀ ih =>
      obtain ⟨t₁, ht₁0, ht₁v, ht₁S⟩ := ih
      rcases eq_or_ne w₀ v with heq | hw₀v
      · refine ⟨t₁, ht₁0, ht₁v, ?_⟩
        intro w hw hwv
        rcases Finset.mem_cons.mp hw with h | h
        · exact absurd (h.trans heq) hwv
        · exact ht₁S w h hwv
      · obtain ⟨t₂, ht₂0, ht₂v, ht₂w⟩ := exists_ord_pos_ord_neg_of_ne (Ne.symm hw₀v)
        set M : ℕ :=
          ((Finset.cons w₀ S' hw₀).sup fun w => (1 - w.ord t₁).toNat) + 1 with hM
        have hM1 : 1 ≤ (M : ℤ) := by
          rw [hM]; push_cast; omega
        have hMw : ∀ w ∈ Finset.cons w₀ S' hw₀, -(M : ℤ) < w.ord t₁ := by
          intro w hw
          have h1 : (1 - w.ord t₁).toNat
              ≤ (Finset.cons w₀ S' hw₀).sup fun w' => (1 - w'.ord t₁).toNat :=
            Finset.le_sup (f := fun w' => (1 - w'.ord t₁).toNat) hw
          have h3 : ((1 - w.ord t₁).toNat : ℤ)
              ≤ (((Finset.cons w₀ S' hw₀).sup fun w' => (1 - w'.ord t₁).toNat : ℕ) : ℤ) := by
            exact_mod_cast h1
          rw [hM]; push_cast; omega
        have hpow0 : t₂ ^ (M : ℤ) ≠ 0 := zpow_ne_zero _ ht₂0
        have hw₀lt : w₀.ord (t₂ ^ (M : ℤ)) < w₀.ord t₁ := by
          rw [w₀.ord_zpow]
          have h5 : (M : ℤ) * w₀.ord t₂ ≤ (M : ℤ) * (-1) :=
            mul_le_mul_of_nonneg_left (by omega) (by omega)
          have h6 := hMw w₀ (Finset.mem_cons.mpr (Or.inl rfl))
          linarith
        have hu0 : t₁ + t₂ ^ (M : ℤ) ≠ 0 := by
          have h := add_ne_zero_of_ord_lt w₀ hw₀lt
          rwa [add_comm (t₂ ^ (M : ℤ)) t₁] at h
        refine ⟨t₁ + t₂ ^ (M : ℤ), hu0, ?_, ?_⟩
        ·
          have hposM : 0 < v.ord (t₂ ^ (M : ℤ)) := by
            rw [v.ord_zpow]
            exact mul_pos (by omega) ht₂v
          exact lt_of_lt_of_le (lt_min ht₁v hposM) (v.min_ord_le_ord_add hu0)
        · intro w hw hwv
          rcases Finset.mem_cons.mp hw with heqw | hwS'
          ·
            rw [heqw, add_comm t₁ (t₂ ^ (M : ℤ)),
              w₀.ord_add_eq_of_lt hpow0 ht₁0 hw₀lt, w₀.ord_zpow]
            have h5 : (M : ℤ) * w₀.ord t₂ ≤ (M : ℤ) * (-1) :=
              mul_le_mul_of_nonneg_left (by omega) (by omega)
            linarith
          ·
            have hward := ht₁S w hwS' hwv
            rcases le_or_gt 0 (w.ord t₂) with hpos | hneg
            · have hlt : w.ord t₁ < w.ord (t₂ ^ (M : ℤ)) := by
                rw [w.ord_zpow]
                have h7 : 0 ≤ (M : ℤ) * w.ord t₂ := mul_nonneg (by omega) hpos
                linarith
              rw [w.ord_add_eq_of_lt ht₁0 hpow0 hlt]
              exact hward
            · have hlt : w.ord (t₂ ^ (M : ℤ)) < w.ord t₁ := by
                rw [w.ord_zpow]
                have h5 : (M : ℤ) * w.ord t₂ ≤ (M : ℤ) * (-1) :=
                  mul_le_mul_of_nonneg_left (by omega) (by omega)
                have h6 := hMw w (Finset.mem_cons.mpr (Or.inr hwS'))
                linarith
              rw [add_comm t₁ (t₂ ^ (M : ℤ)),
                w.ord_add_eq_of_lt hpow0 ht₁0 hlt, w.ord_zpow]
              have h5 : (M : ℤ) * w.ord t₂ ≤ (M : ℤ) * (-1) :=
                mul_le_mul_of_nonneg_left (by omega) (by omega)
              linarith

/-- **Prescribed orders at finitely many places.** For a finite set `S` of places of
the function field `F` over `K` and any integers `n v` there is `g ≠ 0` in `F` whose
order at each `v ∈ S` is `n v`. Statement from
`Theorems/Thm_AlgebraicCurve_Place_exists_forall_ord_eq_finset.lean`; proof after the
pin's `S_` file. -/
theorem exists_forall_ord_eq_finset (S : Finset (Place K F)) (n : Place K F → ℤ) :
    ∃ g : F, g ≠ 0 ∧ ∀ v ∈ S, v.ord g = n v := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hSne
  · exact ⟨1, one_ne_zero, fun v hv => absurd hv (Finset.notMem_empty v)⟩

  have hsep : ∀ v : Place K F, ∃ t : F, t ≠ 0 ∧ 0 < v.ord t ∧
      ∀ w ∈ S, w ≠ v → w.ord t < 0 := fun v => exists_separating v S
  choose t ht0 htv htS using hsep

  have hunif : ∀ v : Place K F, ∃ π : v.toValuationSubring, Irreducible π := fun v =>
    IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  choose π hπ using hunif
  have hπ0 : ∀ v : Place K F, ((π v : F)) ≠ 0 := by
    intro v
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using (hπ v).ne_zero
  set a : Place K F → F := fun v => ((π v : F)) ^ (n v) with ha
  have ha0 : ∀ v, a v ≠ 0 := by
    intro v
    simp only [ha]
    exact zpow_ne_zero _ (hπ0 v)
  have hav : ∀ v, v.ord (a v) = n v := by
    intro v
    simp only [ha]
    rw [v.ord_zpow, v.ord_coe_irreducible (hπ v), mul_one]

  set P : ℕ := (S.sup fun v => S.sup fun w => (n v - v.ord (a w)).toNat) + 1 with hP
  have hP1 : 1 ≤ (P : ℤ) := by
    rw [hP]; push_cast; omega
  have hPbound : ∀ v ∈ S, ∀ w ∈ S, n v - v.ord (a w) < (P : ℤ) := by
    intro v hv w hw
    have h1 : (n v - v.ord (a w)).toNat
        ≤ S.sup fun w' => (n v - v.ord (a w')).toNat :=
      Finset.le_sup (f := fun w' => (n v - v.ord (a w')).toNat) hw
    have h2 : (S.sup fun w' => (n v - v.ord (a w')).toNat)
        ≤ S.sup fun v' => S.sup fun w' => (n v' - v'.ord (a w')).toNat :=
      Finset.le_sup (f := fun v' => S.sup fun w' => (n v' - v'.ord (a w')).toNat) hv
    have h3 : ((n v - v.ord (a w)).toNat : ℤ)
        ≤ ((S.sup fun v' => S.sup fun w' => (n v' - v'.ord (a w')).toNat : ℕ) : ℤ) := by
      exact_mod_cast le_trans h1 h2
    rw [hP]; push_cast; omega

  have hpow0 : ∀ v : Place K F, t v ^ (P : ℤ) ≠ 0 := fun v => zpow_ne_zero _ (ht0 v)
  have hltden : ∀ v : Place K F, v.ord (1 : F) < v.ord (t v ^ (P : ℤ)) := by
    intro v
    rw [v.ord_one, v.ord_zpow]
    exact mul_pos (by omega) (htv v)
  have hden : ∀ v : Place K F, (1 : F) + t v ^ (P : ℤ) ≠ 0 := fun v =>
    add_ne_zero_of_ord_lt v (hltden v)
  have hdenord : ∀ v : Place K F, v.ord ((1 : F) + t v ^ (P : ℤ)) = 0 := by
    intro v
    rw [v.ord_add_eq_of_lt one_ne_zero (hpow0 v) (hltden v), v.ord_one]
  have hdenord' : ∀ v : Place K F, ∀ w ∈ S, w ≠ v →
      w.ord ((1 : F) + t v ^ (P : ℤ)) = (P : ℤ) * w.ord (t v) := by
    intro v w hw hwv
    have hneg : w.ord (t v ^ (P : ℤ)) < w.ord (1 : F) := by
      rw [w.ord_one, w.ord_zpow]
      have h1 := htS v w hw hwv
      have h5 : (P : ℤ) * w.ord (t v) ≤ (P : ℤ) * (-1) :=
        mul_le_mul_of_nonneg_left (by omega) (by omega)
      linarith
    rw [add_comm ((1 : F)) (t v ^ (P : ℤ)),
      w.ord_add_eq_of_lt (hpow0 v) one_ne_zero hneg, w.ord_zpow]

  set u : Place K F → F := fun v => a v * ((1 : F) + t v ^ (P : ℤ))⁻¹ with hu
  have hu0 : ∀ v, u v ≠ 0 := by
    intro v
    simp only [hu]
    exact mul_ne_zero (ha0 v) (inv_ne_zero (hden v))
  have huord : ∀ v, v.ord (u v) = n v := by
    intro v
    simp only [hu]
    rw [v.ord_mul (ha0 v) (inv_ne_zero (hden v)), v.ord_inv, hdenord v, hav v]
    omega
  have huord' : ∀ v : Place K F, ∀ w ∈ S, w ≠ v →
      w.ord (u v) = w.ord (a v) - (P : ℤ) * w.ord (t v) := by
    intro v w hw hwv
    simp only [hu]
    rw [w.ord_mul (ha0 v) (inv_ne_zero (hden v)), w.ord_inv, hdenord' v w hw hwv]
    ring

  have htail : ∀ v ∈ S, ∀ w ∈ S, w ≠ v → n v < v.ord (u w) := by
    intro v hv w hw hwv
    have h1 : v.ord (u w) = v.ord (a w) - (P : ℤ) * v.ord (t w) :=
      huord' w v hv (Ne.symm hwv)
    have h2 := htS w v hv (Ne.symm hwv)
    have h3 := hPbound v hv w hw
    have h5 : (P : ℤ) * v.ord (t w) ≤ (P : ℤ) * (-1) :=
      mul_le_mul_of_nonneg_left (by omega) (by omega)
    rw [h1]
    linarith

  have hmain : ∀ v ∈ S, S.sum u ≠ 0 ∧ v.ord (S.sum u) = n v := by
    intro v hv
    have hsplit : S.sum u = u v + (S.erase v).sum u :=
      (Finset.add_sum_erase S u hv).symm
    have hcond : ∀ w ∈ S.erase v, u w ≠ 0 ∧ n v < v.ord (u w) := by
      intro w hw
      obtain ⟨hwv, hwS⟩ := Finset.mem_erase.mp hw
      exact ⟨hu0 w, htail v hv w hwS hwv⟩
    rcases ord_finsetSum_gt v (S.erase v) u (n v) hcond with h0 | ⟨hne, hlt⟩
    · rw [hsplit, h0, add_zero]
      exact ⟨hu0 v, huord v⟩
    · have hltu : v.ord (u v) < v.ord ((S.erase v).sum u) := by
        rw [huord v]; exact hlt
      constructor
      · rw [hsplit]
        exact add_ne_zero_of_ord_lt v hltu
      · rw [hsplit, v.ord_add_eq_of_lt (hu0 v) hne hltu]
        exact huord v
  obtain ⟨v₀, hv₀⟩ := hSne
  exact ⟨S.sum u, (hmain v₀ hv₀).1, fun v hv => (hmain v hv).2⟩

/-! ## The norm inequality above a place

The sum formula itself — `Place.ord_norm_eq_sum_fiberOver`, in the divisor theory —
says that the order of a norm is the inertia-weighted sum of the orders at the places
above. What the ramification argument adds is the inequality `ord_w x ≤ ord_v (N x)`
for an `x` all of whose conjugates above `v` are integral: that is the sum formula read
term by term, since the single `w`-term already dominates `ord_w x` (the inertia degree
is positive) and every other term is nonnegative.
-/

section NormBlock

variable {K F L : Type*} [Field K] [Field F] [Field L]
  [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L]
  [FiniteDimensional F L] [Algebra.IsSeparable F L] [CharZero F]

/-- **A conjugate at a place above `v` is dominated by the order of the norm**: if
every place above `v` gives `x` nonnegative order, then the order of `x` at one of
them is at most the order of `N x` at `v`. Private helper of the pin's ramification
`S_` file. -/
private theorem ord_le_ord_norm_of_forall_ord_nonneg (v : Place K F) {x : L} (hx : x ≠ 0)
    (hnonneg : ∀ w' ∈ v.fiberOver L, 0 ≤ w'.ord x) {w : Place K L}
    (hw : w ∈ v.fiberOver L) :
    w.ord x ≤ v.ord (Algebra.norm F x) := by
  rw [ord_norm_eq_sum_fiberOver v hx]
  calc w.ord x ≤ (w.inertiaDeg F : ℤ) * w.ord x :=
        le_mul_of_one_le_left (hnonneg w hw)
          (by exact_mod_cast w.inertiaDeg_pos_of_finiteDimensional (F := F))
    _ ≤ ∑ w' ∈ v.fiberOver L, (w'.inertiaDeg F : ℤ) * w'.ord x :=
        Finset.single_le_sum (f := fun w' => (w'.inertiaDeg F : ℤ) * w'.ord x)
          (fun w' hw' => mul_nonneg (by positivity) (hnonneg w' hw')) hw

end NormBlock

/-! ## The Kummer cover of prime degree is unramified at a place of divisible order -/

section Kummer

variable {K F L : Type*} [Field K] [Field F] [Field L] [Algebra K F] [Algebra F L]

variable {p : ℕ} {f : F} {α : L}

private theorem forall_pow_ne_mul_pow (hf : ∀ g : F, g ^ p ≠ f) {h : F} (hh : h ≠ 0) :
    ∀ g : F, g ^ p ≠ f * h ^ p := by
  intro g hg
  apply hf (g / h)
  rw [div_pow, hg, mul_div_cancel_right₀ _ (pow_ne_zero p hh)]

private theorem mul_algebraMap_pow_eq (hα : α ^ p = algebraMap F L f) (h : F) :
    (α * algebraMap F L h) ^ p = algebraMap F L (f * h ^ p) := by
  rw [mul_pow, hα, ← map_pow, ← map_mul]

private theorem adjoin_mul_algebraMap_eq_top (htop : F⟮α⟯ = ⊤) {h : F} (hh : h ≠ 0) :
    F⟮α * algebraMap F L h⟯ = ⊤ := by
  rw [eq_top_iff, ← htop, adjoin_simple_le_iff]
  have h1 := mem_adjoin_simple_self F (α * algebraMap F L h)
  have h2 : algebraMap F L h⁻¹ ∈ F⟮α * algebraMap F L h⟯ := IntermediateField.algebraMap_mem _ _
  have h3 := mul_mem h1 h2
  rwa [mul_assoc, ← map_mul, mul_inv_cancel₀ hh, map_one, mul_one] at h3

private theorem not_mem_range_of_pow_eq (hf : ∀ g : F, g ^ p ≠ f) (hα : α ^ p = algebraMap F L f) :
    α ∉ Set.range (algebraMap F L) := by
  rintro ⟨a, rfl⟩
  rw [← map_pow] at hα
  exact hf a ((algebraMap F L).injective hα)

private theorem sub_algebraMap_ne_zero (hf : ∀ g : F, g ^ p ≠ f) (hα : α ^ p = algebraMap F L f)
    (c : F) : α - algebraMap F L c ≠ 0 := fun h =>
  not_mem_range_of_pow_eq hf hα ⟨c, (sub_eq_zero.mp h).symm⟩

end Kummer

section KummerPure

variable {F L : Type*} [Field F] [Field L] [Algebra F L]
variable {p : ℕ} [hp : Fact p.Prime] {f : F} {α : L}

private theorem irreducible_X_pow_sub_C (hf : ∀ g : F, g ^ p ≠ f) : Irreducible (X ^ p - C f) :=
  X_pow_sub_C_irreducible_of_prime hp.out hf

private theorem ne_zero_of_forall_pow_ne (hf : ∀ g : F, g ^ p ≠ f) : f ≠ 0 := by
  rintro rfl
  exact hf 0 (zero_pow hp.out.ne_zero)

private theorem isIntegral_of_pow_eq (hα : α ^ p = algebraMap F L f) : IsIntegral F α :=
  IsIntegral.of_pow hp.out.pos (hα ▸ isIntegral_algebraMap)

private theorem minpoly_eq_of_pow_eq (hf : ∀ g : F, g ^ p ≠ f) (hα : α ^ p = algebraMap F L f) :
    minpoly F α = X ^ p - C f :=
  (minpoly.eq_of_irreducible_of_monic (irreducible_X_pow_sub_C hf)
    (by simp only [map_sub, map_pow, aeval_X, aeval_C, hα, sub_self])
    (monic_X_pow_sub_C f hp.out.ne_zero)).symm

private theorem norm_root_sub_algebraMap (hf : ∀ g : F, g ^ p ≠ f) (hα : α ^ p = algebraMap F L f)
    (htop : F⟮α⟯ = ⊤) (c : F) :
    Algebra.norm F (α - algebraMap F L c) = (-1) ^ p * (c ^ p - f) := by
  have hxint : IsIntegral F (α - algebraMap F L c) :=
    (isIntegral_of_pow_eq hα).sub isIntegral_algebraMap
  have hminx : minpoly F (α - algebraMap F L c) = (X ^ p - C f).comp (X + C c) := by
    rw [minpoly.sub_algebraMap, minpoly_eq_of_pow_eq hf hα]
  have hxtop : F⟮α - algebraMap F L c⟯ = ⊤ := by
    rw [eq_top_iff, ← htop, adjoin_simple_le_iff]
    have h1 : α - algebraMap F L c ∈ F⟮α - algebraMap F L c⟯ := mem_adjoin_simple_self F _
    have h2 : algebraMap F L c ∈ F⟮α - algebraMap F L c⟯ := IntermediateField.algebraMap_mem _ c
    simpa using add_mem h1 h2
  let pb : PowerBasis F L := (adjoin.powerBasis hxint).map ((equivOfEq hxtop).trans topEquiv)
  have hgen : pb.gen = α - algebraMap F L c := by
    simp only [pb, PowerBasis.map_gen, adjoin.powerBasis_gen, AlgEquiv.trans_apply]
    rfl
  have hdim : pb.dim = p := by
    simp only [pb, PowerBasis.map_dim, adjoin.powerBasis_dim, hminx, natDegree_comp,
      natDegree_X_pow_sub_C, natDegree_X_add_C, mul_one]
  have key := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pb
  rw [hgen, hdim, hminx] at key
  rw [key, coeff_zero_eq_eval_zero, eval_comp]
  simp only [eval_add, eval_X, eval_C, zero_add, eval_sub, eval_pow]

end KummerPure

section KummerOrd

variable {K F L : Type*} [Field K] [Field F] [Field L] [Algebra K F] [Algebra F L]
variable {p : ℕ} [hp : Fact p.Prime] {f : F} {α : L}

private theorem ord_norm_root_sub_algebraMap (v : Place K F) (hf : ∀ g : F, g ^ p ≠ f)
    (hα : α ^ p = algebraMap F L f) (htop : F⟮α⟯ = ⊤) (c : F) :
    v.ord (Algebra.norm F (α - algebraMap F L c)) = v.ord (f - c ^ p) := by
  rw [norm_root_sub_algebraMap hf hα htop c]
  rcases neg_one_pow_eq_or F p with h | h <;> rw [h]
  · rw [one_mul, ← neg_sub, v.ord_neg]
  · rw [neg_one_mul, neg_sub]

end KummerOrd

section Normalize

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem exists_ord_mul_pow_eq_zero (v : Place K F) {p : ℕ} {f : F} (hf0 : f ≠ 0)
    (hord : (p : ℤ) ∣ v.ord f) : ∃ h : F, h ≠ 0 ∧ v.ord (f * h ^ p) = 0 := by
  obtain ⟨t, ht⟩ := v.exists_ord_eq_one
  obtain ⟨m, hm⟩ := hord
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [ord_zero] at ht
    exact zero_ne_one ht
  refine ⟨t ^ (-m), zpow_ne_zero _ ht0, ?_⟩
  rw [v.ord_mul hf0 (pow_ne_zero _ (zpow_ne_zero _ ht0)), ← zpow_natCast, ← zpow_mul,
    v.ord_zpow, ht, hm]
  ring

end Normalize

section FibreUnit

variable {K F L : Type*} [Field K] [Field F] [Field L] [Algebra K F] [Algebra K L]
  [Algebra F L] [IsScalarTower K F L] [Algebra.IsIntegral F L]

private theorem ord_eq_zero_of_pow_eq_of_ord_restrict_eq_zero (w : Place K L) {p : ℕ} (hp : p ≠ 0)
    {f₁ : F} {β : L} (hβ : β ^ p = algebraMap F L f₁) (h0 : (w.restrict F).ord f₁ = 0) :
    w.ord β = 0 := by
  have h := w.ord_restrict (F := F) f₁
  rw [h0, mul_zero, ← hβ, ← zpow_natCast, w.ord_zpow] at h
  exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast hp)

end FibreUnit

section OrdResidueKit

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem ord_eq_zero_iff_isUnit {g : F} (hg : g ≠ 0) (hmem : g ∈ v.toValuationSubring) :
    v.ord g = 0 ↔ IsUnit (⟨g, hmem⟩ : v.toValuationSubring) := by
  rw [v.ord_eq_zero_iff_adicValuation_eq_one hg]
  exact v.adicValuation_coe_eq_one_iff ⟨g, hmem⟩

private theorem ord_eq_zero_of_residue_ne_zero {g : F} (hg : g ≠ 0)
    (hmem : g ∈ v.toValuationSubring)
    (hres : residue v.toValuationSubring ⟨g, hmem⟩ ≠ 0) :
    v.ord g = 0 := by
  refine (v.ord_eq_zero_iff_isUnit hg hmem).mpr ?_
  by_contra hnotunit
  apply hres
  have : ¬IsUnit (⟨g, hmem⟩ : v.toValuationSubring) := hnotunit
  rwa [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal,
    ← Ideal.Quotient.eq_zero_iff_mem] at this

private theorem one_le_ord_of_residue_eq_zero {g : F} (hg : g ≠ 0)
    (hmem : g ∈ v.toValuationSubring)
    (hres : residue v.toValuationSubring ⟨g, hmem⟩ = 0) :
    1 ≤ v.ord g := by
  have hnonunit : ¬IsUnit (⟨g, hmem⟩ : v.toValuationSubring) := by
    rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal, ← Ideal.Quotient.eq_zero_iff_mem]
    exact hres
  have hne : v.ord g ≠ 0 := fun h => hnonunit ((v.ord_eq_zero_iff_isUnit hg hmem).mp h)
  have hnn : 0 ≤ v.ord g := v.ord_nonneg_of_mem hmem
  omega

private theorem one_le_ord_sub_evalAt (hv : v.IsRational) {g : F} (hg : g ≠ 0)
    (hord : v.ord g = 0) (hgc : g ≠ algebraMap K F (v.evalAt g)) :
    1 ≤ v.ord (g - algebraMap K F (v.evalAt g)) := by
  set c := v.evalAt g
  have hfmem : g ∈ v.toValuationSubring := v.mem_of_ord_nonneg hg hord.ge
  have hcmem : algebraMap K F c ∈ v.toValuationSubring := v.algebraMap_mem' c
  have hsubmem : g - algebraMap K F c ∈ v.toValuationSubring := sub_mem hfmem hcmem
  refine v.one_le_ord_of_residue_eq_zero (sub_ne_zero.mpr hgc) hsubmem ?_
  have h1 : residue v.toValuationSubring ⟨g, hfmem⟩ = algebraMap K _ c :=
    (v.algebraMap_evalAt hv hfmem).symm
  have h2 : residue v.toValuationSubring ⟨algebraMap K F c, hcmem⟩ = algebraMap K _ c := by
    have := (v.algebraMap_evalAt hv hcmem)
    rwa [v.evalAt_algebraMap_eq c] at this
  calc residue v.toValuationSubring ⟨g - algebraMap K F c, hsubmem⟩
      = residue v.toValuationSubring (⟨g, hfmem⟩ - ⟨algebraMap K F c, hcmem⟩) := by congr 1
    _ = residue v.toValuationSubring ⟨g, hfmem⟩
        - residue v.toValuationSubring ⟨algebraMap K F c, hcmem⟩ := map_sub _ _ _
    _ = 0 := by rw [h1, h2]; ring

end OrdResidueKit

section ResidueGeomSum

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem residue_geom_sum₂_of_residue_eq {x y : F} (hx : x ∈ v.toValuationSubring)
    (hy : y ∈ v.toValuationSubring) {r : v.ResidueField}
    (hxr : residue v.toValuationSubring ⟨x, hx⟩ = r)
    (hyr : residue v.toValuationSubring ⟨y, hy⟩ = r) (n : ℕ)
    (hS : (∑ j ∈ Finset.range n, x ^ j * y ^ (n - 1 - j)) ∈ v.toValuationSubring) :
    residue v.toValuationSubring ⟨∑ j ∈ Finset.range n, x ^ j * y ^ (n - 1 - j), hS⟩
      = n * r ^ (n - 1) := by
  have hcoe : (⟨∑ j ∈ Finset.range n, x ^ j * y ^ (n - 1 - j), hS⟩ : v.toValuationSubring)
      = ∑ j ∈ Finset.range n, (⟨x, hx⟩ : v.toValuationSubring) ^ j
          * (⟨y, hy⟩ : v.toValuationSubring) ^ (n - 1 - j) := by
    apply Subtype.ext
    push_cast
    rfl
  rw [hcoe, map_sum]
  simp only [map_mul, map_pow, hxr, hyr]
  exact geom_sum₂_self r n

end ResidueGeomSum

/-- **A prime-degree Kummer cover is unramified at a place whose order is divisible
by the degree.** With `p` prime, `α ^ p = f` for an `f` that is not a `p`-th power,
`F⟮α⟯ = ⊤`, and `p ∣ v.ord f` at every place of `F`, the ramification index of a
rational place of the extension is `1`. Statement from
`Theorems/Thm_AlgebraicCurve_Place_ramificationIndex_eq_one_of_forall_dvd_ord.lean`;
proof after the pin's `S_` file. -/
theorem ramificationIndex_eq_one_of_forall_dvd_ord {K F L : Type*} [Field K] [Field F] [Field L]
    [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L]
    [FiniteDimensional F L] [Algebra.IsSeparable F L]
    {p : ℕ} [Fact p.Prime] {f : F} {α : L} [CharZero F]
    (hf : ∀ g : F, g ^ p ≠ f)
    (hα : α ^ p = algebraMap F L f) (htop : F⟮α⟯ = ⊤)
    (hord : ∀ v : Place K F, (p : ℤ) ∣ v.ord f)
    (w : Place K L) (hw_rat : w.IsRational) :
    w.ramificationIndex F = 1 := by
  set v := w.restrict F

  obtain ⟨h, hh0, hf1ord⟩ :=
    exists_ord_mul_pow_eq_zero v (ne_zero_of_forall_pow_ne hf) (hord v)
  set f₁ := f * h ^ p with hf1def
  set β := α * algebraMap F L h with hβdef
  have hf₁ : ∀ g : F, g ^ p ≠ f₁ := forall_pow_ne_mul_pow hf hh0
  have hβ : β ^ p = algebraMap F L f₁ := mul_algebraMap_pow_eq hα h
  have hβtop : F⟮β⟯ = ⊤ := adjoin_mul_algebraMap_eq_top htop hh0
  have hβne : β ≠ 0 := by
    intro hz; apply ne_zero_of_forall_pow_ne hf₁
    have := hβ; rw [hz, zero_pow (Fact.out : p.Prime).ne_zero] at this
    exact ((algebraMap F L).injective (this.symm.trans (map_zero _).symm))

  have hβord0 : w.ord β = 0 :=
    ord_eq_zero_of_pow_eq_of_ord_restrict_eq_zero w (Fact.out : p.Prime).ne_zero hβ hf1ord

  set c := w.evalAt β
  have hc0 : c ≠ 0 := w.evalAt_ne_zero_of_ord_eq_zero hw_rat hβne hβord0
  have hβc : β ≠ algebraMap K L c := by
    intro heq
    exact sub_algebraMap_ne_zero hf₁ hβ (algebraMap K F c)
      (by rw [← IsScalarTower.algebraMap_apply K F L, ← heq]; ring)
  have hβc' : β ≠ algebraMap F L (algebraMap K F c) := by
    rw [← IsScalarTower.algebraMap_apply K F L]; exact hβc
  set cL := algebraMap K L c with hcLdef
  have hcLord : w.ord cL = 0 := w.ord_algebraMap c
  have hm0ge : 1 ≤ w.ord (β - cL) := by
    have := one_le_ord_sub_evalAt w hw_rat hβne hβord0 hβc
    simpa [hcLdef] using this
  set m₀ := w.ord (β - cL) with hm0def

  set cF := algebraMap K F c with hcFdef
  set S : L := ∑ j ∈ Finset.range p, β ^ j * cL ^ (p - 1 - j) with hSdef
  have hfact : β ^ p - cL ^ p = (β - cL) * S :=
    ((Commute.all β cL).mul_geom_sum₂ p).symm
  have hcLmem : cL ∈ w.toValuationSubring := w.algebraMap_mem' c
  have hβmem : β ∈ w.toValuationSubring := w.mem_of_ord_nonneg hβne hβord0.ge
  have hSmem : S ∈ w.toValuationSubring := by
    refine Subring.sum_mem _ fun j _ => ?_
    exact mul_mem (pow_mem hβmem _) (pow_mem hcLmem _)
  have hSres :
      residue w.toValuationSubring ⟨S, hSmem⟩ = (p : w.ResidueField) * algebraMap K _ c ^ (p - 1) := by
    have hβres : residue w.toValuationSubring ⟨β, hβmem⟩ = algebraMap K w.ResidueField c :=
      (w.algebraMap_evalAt hw_rat hβmem).symm
    have hcLres : residue w.toValuationSubring ⟨cL, hcLmem⟩ = algebraMap K w.ResidueField c := by
      have hmk : (⟨cL, hcLmem⟩ : w.toValuationSubring)
          = ⟨algebraMap K L c, w.algebraMap_mem' c⟩ := Subtype.ext hcLdef
      rw [hmk]; exact residue_algebraMap w c
    exact residue_geom_sum₂_of_residue_eq w hβmem hcLmem hβres hcLres p hSmem

  haveI : CharZero K :=
    (RingHom.charZero_iff (algebraMap K F).injective).mpr ‹CharZero F›
  haveI : CharZero w.ResidueField :=
    (RingHom.charZero_iff (algebraMap K w.ResidueField).injective).mp ‹CharZero K›
  have hSresne : residue w.toValuationSubring ⟨S, hSmem⟩ ≠ 0 := by
    rw [hSres]
    refine mul_ne_zero ?_ (pow_ne_zero _ ?_)
    · exact Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
    · exact (map_ne_zero_iff _ (algebraMap K w.ResidueField).injective).mpr hc0
  have hSne : S ≠ 0 := by
    intro hz; apply hSresne
    have : (⟨S, hSmem⟩ : w.toValuationSubring) = 0 := Subtype.ext hz
    simp [this]
  have hSord : w.ord S = 0 := ord_eq_zero_of_residue_ne_zero w hSne hSmem hSresne

  set f₂ := f₁ - cF ^ p with hf2def
  have hf2ne : f₂ ≠ 0 := by
    intro hz
    exact hf₁ cF (sub_eq_zero.mp hz).symm
  set K₀ := v.ord f₂ with hK0def
  have hkey : algebraMap F L f₂ = β ^ p - cL ^ p := by
    simp only [hf2def, map_sub, map_pow, ← hβ, hcLdef, hcFdef,
      ← IsScalarTower.algebraMap_apply K F L]
  have heK : (w.ramificationIndex F : ℤ) * K₀ = m₀ := by
    have hordrest := w.ord_restrict (F := F) f₂
    rw [hkey, hfact] at hordrest
    have hβcne : β - cL ≠ 0 := sub_ne_zero.mpr hβc
    rw [w.ord_mul hβcne hSne, hSord, add_zero] at hordrest
    simpa [hK0def, hm0def, v] using hordrest.symm

  have hβcLne : β - cL ≠ 0 := sub_ne_zero.mpr hβc
  have hcLeq : cL = algebraMap F L cF := by
    simp only [hcLdef, hcFdef, IsScalarTower.algebraMap_apply K F L]
  have hK0_eq_ordnorm : K₀ = v.ord (Algebra.norm F (β - cL)) := by
    rw [hcLeq, ord_norm_root_sub_algebraMap v hf₁ hβ hβtop cF, hK0def, hf2def]
  have hKge : m₀ ≤ K₀ := by
    rw [hK0_eq_ordnorm, hm0def]
    refine ord_le_ord_norm_of_forall_ord_nonneg v hβcLne (w := w) ?_ (restrict_mem_fiberOver w)

    intro w' hw'
    have hβord0' : w'.ord β = 0 :=
      ord_eq_zero_of_pow_eq_of_ord_restrict_eq_zero w' (Fact.out : p.Prime).ne_zero hβ
        (by rw [(mem_fiberOver v).mp hw']; exact hf1ord)
    have hβmem' : β ∈ w'.toValuationSubring := w'.mem_of_ord_nonneg hβne hβord0'.ge
    have hcLmem' : cL ∈ w'.toValuationSubring := hcLdef ▸ w'.algebraMap_mem' c
    exact w'.ord_nonneg_of_mem (sub_mem hβmem' hcLmem')

  have hepos : 0 < w.ramificationIndex F := w.ramificationIndex_pos (F := F)
  have hK0pos : 1 ≤ K₀ := by nlinarith [hm0ge, heK, hepos]
  have : (w.ramificationIndex F : ℤ) ≤ 1 := by
    have := heK.symm ▸ hKge
    nlinarith [hK0pos]
  omega

/-! ## The norm of a unit above a place has order zero -/

/-- **The norm of a unit above a place has order zero**: if every place of `F'` above
`v` gives a nonzero `f` the order zero, then so does `v` give the norm. Statement
from `Theorems/Thm_AlgebraicCurve_Place_ord_norm_eq_zero_of_forall_fiber.lean`; proof
after the pin's `S_` file. -/
theorem ord_norm_eq_zero_of_forall_fiber {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [CharZero F]
    [HasPrincipalDivisors K F'] {f : F'} (hf : f ≠ 0) (v : Place K F)
    (h : ∀ w ∈ v.fiber F', w.ord f = 0) : v.ord (Algebra.norm F f) = 0 := by
  rw [ord_norm_eq_sum_fiberOver v hf]
  refine Finset.sum_eq_zero fun w hw => ?_
  have hw' : w ∈ v.fiber F' := by
    rw [mem_fiber]
    exact (mem_fiberOver v).mp hw
  rw [h w hw', mul_zero]

end Place

end AlgebraicCurve
