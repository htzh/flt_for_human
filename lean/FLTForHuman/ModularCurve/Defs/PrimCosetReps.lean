/-
  The primitive coset representatives of `Γ₀(N)\SL₂(ℤ)`.

  `primCosetReps N` is the finite set of triples `(a, b, d)` with `a * d = N`,
  `b < d` and `gcd a (gcd b d) = 1`: the upper-triangular matrices
  `[[a, b], [0, d]]` of determinant `N`. It is the index set for the `q`-expansion
  of the level-`N` modular polynomial, and `card_primCosetReps_eq_dedekindPsi`
  (`Gamma0Index.lean`) counts it by `ψ(N)`.

  This is SET-3 (l3) of `topics/PORTING-Level.md`. `cosetSubst` (the substitution
  `q ↦ ζ ^ (a * b) q ^ (a * a)`) is already ported in `Defs/PhiGen.lean`, so it is
  imported, not re-ported.

  FLT provenance, pinned `aa2d8b3`:
  `Definitions/Def_ModularCurve_PrimCosetReps.lean` lines 8–45.
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_PrimCosetReps.lean

  Names are FLT's, verbatim, in FLT's `ModularCurve` namespace; `Finset`,
  `Polynomial` and `LaurentSeries` are mathlib's. Statements are verbatim; proofs
  are adapted only for mathlib `v4.34.0`.
-/
import Mathlib.Tactic
import FLTForHuman.ModularCurve.Defs.PhiGen

set_option autoImplicit false

namespace ModularCurve

/-- The primitive coset representatives of `Γ₀(N)\SL₂(ℤ)`: the triples
`(a, b, d)` with `a * d = N`, `b < d` and `gcd a (gcd b d) = 1`. -/
def primCosetReps (N : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  Finset.filter
    (fun t => t.1 * t.2.2 = N ∧ t.2.1 < t.2.2 ∧ Nat.gcd t.1 (Nat.gcd t.2.1 t.2.2) = 1)
    (Finset.range (N + 1) ×ˢ Finset.range (N + 1) ×ˢ Finset.range (N + 1))

theorem mem_primCosetReps {N a b d : ℕ} (hN : N ≠ 0) :
    (a, b, d) ∈ primCosetReps N ↔ a * d = N ∧ b < d ∧ Nat.gcd a (Nat.gcd b d) = 1 := by
  simp only [primCosetReps, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨_, had, hbd, hgcd⟩
    exact ⟨had, hbd, hgcd⟩
  · rintro ⟨had, hbd, hgcd⟩
    have hd0 : d ≠ 0 := by
      rintro rfl
      exact hN (by simpa using had.symm)
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hN (by simpa using had.symm)
    have haN : a ≤ N := had ▸ Nat.le_mul_of_pos_right a (Nat.pos_of_ne_zero hd0)
    have hdN : d ≤ N := had ▸ Nat.le_mul_of_pos_left d (Nat.pos_of_ne_zero ha0)
    exact ⟨⟨by omega, by omega, by omega⟩, had, hbd, hgcd⟩

section Conjugates

variable {K : Type*} [Field K]

/-- The conjugate `J` under the coset `(a, b, d)`; zero when `a = 0`. -/
noncomputable def cosetConj (ζ : Kˣ) (J : LaurentSeries K) (t : ℕ × ℕ × ℕ) : LaurentSeries K :=
  if h : t.1 = 0 then 0 else
    haveI : NeZero t.1 := ⟨h⟩
    cosetSubst ζ t.1 t.2.1 J

theorem cosetConj_eq (ζ : Kˣ) (J : LaurentSeries K) (a b d : ℕ) [NeZero a] :
    cosetConj ζ J (a, b, d) = cosetSubst ζ a b J := by
  unfold cosetConj
  rw [dite_eq_right (NeZero.ne a)]

/-- The degree-`#primCosetReps N` polynomial whose roots are the conjugates of
`J`; the `q`-expansion side of the level-`N` modular polynomial. -/
noncomputable def cosetTwoVarPoly (ζ : Kˣ) (N : ℕ) (J : LaurentSeries K) : Polynomial (LaurentSeries K) :=
  (primCosetReps N).prod fun t => Polynomial.X - Polynomial.C (cosetConj ζ J t)

end Conjugates

end ModularCurve
