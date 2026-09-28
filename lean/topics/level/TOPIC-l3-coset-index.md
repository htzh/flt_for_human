# TOPIC l3 — cosets, the projective line, and the index `ψ(N)`

Work order for SET-3 of [PORTING-Level.md](../PORTING-Level.md).
Target module: `FLTForHuman/ModularForms/Level/Coset.lean`, namespace
`ModularCurve.Coset` (or `ModularForm.Coset`), pinned `aa2d8b3`, mathlib
`v4.34.0`. Prerequisite: SET-1's `Defs/GammaH.lean`.

> **Build discipline — read this first.** Every build is bounded and a blow-up is
> quarantined, not waited on. `lake env lean <module>` **~4 s**, `lake build
> <module>` **~2–5 s**, a heartbeat timeout **~15–20 s then an error**, a healthy
> full `lake build` **seconds to about a minute**. Run every build under
> `timeout 60 lake env lean <file>` / `timeout 90 lake build <module>`; expect
> ≤ 30 s; never raise `maxHeartbeats`; tell a blow-up (high user CPU) from lock
> contention (~0 CPU) by `time`.

## The mathematics

The coset space `Γ₀(N)\SL₂(ℤ)` is the set of lines in `(ℤ/N)²`, i.e. the cyclic
subgroups of order `N` — the level datum of `(E, C)`. The bijection is by the
first column, giving `[SL₂(ℤ):Γ₀(N)] = #ℙ¹(ℤ/N) = ψ(N)`. The `q`-expansion uses
the upper-triangular representatives `[[a,b],[0,d]]` with `ad = N` and
`gcd(a,b,d) = 1`. Base note:
[base/018](../../../base/018-congruence-subgroups-and-invariance.md) §5.

## The declarations

**(a) The projective line** — a definitions port of
`Definitions/Def_ModularCurve_ProjectiveLine.lean` (93 lines), mathlib-only:

```lean
def IsUnimodularRow (a c : R) : Prop := ∃ x y : R, x * a + y * c = 1
abbrev UnimodularRow (R : Type*) [CommRing R] := { v : R × R // IsUnimodularRow v.1 v.2 }
instance unimodularRowSetoid (R : Type*) [CommRing R] : Setoid (UnimodularRow R)
def ProjectiveLine (R : Type*) [CommRing R] : Type _ := Quotient (unimodularRowSetoid R)
def ProjectiveLine.map (f : R →+* S) : ProjectiveLine R → ProjectiveLine S
def borel (R : Type*) [CommRing R] : Subgroup (SpecialLinearGroup (Fin 2) R)
theorem mem_borel_iff {A : SpecialLinearGroup (Fin 2) R} : A ∈ borel R ↔ A.1 1 0 = 0
```

**(b) The coset bijection** — the `private` block of
`P2M/Sol/S_ModularCurve_Gamma0_index.lean`, promoted public here:

```lean
private theorem exists_sl2_int_lift {N} [NeZero N] {a b c d : ZMod N} (h : a * d - b * c = 1) :
    ∃ α β γ δ : ℤ, α * δ - β * γ = 1 ∧ (α : ZMod N) = a ∧ … -- :88
private theorem sl2_surj (N) [NeZero N] :
    Function.Surjective (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N))) -- :137
private theorem Gamma0_eq_comap_borel (N) :
    Gamma0 N = (borel (ZMod N)).comap (map (Int.castRingHom (ZMod N))) -- :216
private def firstColumnClass (A : SpecialLinearGroup (Fin 2) R) : ProjectiveLine R -- :160
private theorem firstColumnClass_eq_iff (A B) : firstColumnClass A = firstColumnClass B ↔ A⁻¹ * B ∈ borel R -- :163
private theorem card_quotient_borel (R) [CommRing R] :
    Nat.card (SpecialLinearGroup (Fin 2) R ⧸ borel R) = Nat.card (ProjectiveLine R) -- :191
```

**(c) The headline statements** — public `Theorems/` wrappers, verbatim:

```lean
theorem ModularCurve.Gamma0_index (N) [NeZero N] : (Gamma0 N).index = dedekindPsi N
theorem ModularCurve.card_projectiveLine_zmod (N) (hN : N ≠ 0) : Nat.card (ProjectiveLine (ZMod N)) = dedekindPsi N
theorem ModularCurve.card_primCosetReps_eq_dedekindPsi (N) (hN : N ≠ 0) : (primCosetReps N).card = dedekindPsi N
```

**(d) The `q`-expansion representatives** — `Definitions/Def_ModularCurve_PrimCosetReps.lean`:

```lean
def primCosetReps (N : ℕ) : Finset (ℕ × ℕ × ℕ)
theorem mem_primCosetReps {N a b d} (hN : N ≠ 0) :
    (a, b, d) ∈ primCosetReps N ↔ a * d = N ∧ b < d ∧ Nat.gcd a (Nat.gcd b d) = 1
```

**(e) The `Γ_H`-upper index seam** (optional tail, once (a)–(c) land):

```lean
theorem CohCarrier.index_GammaHUpper_of_prime … : (GammaHUpper M H ℓ).index = ℓ + 1
theorem CohCarrier.index_GammaHUpper_of_dvd … : (GammaHUpper M H ℓ).index = ℓ
```

These need `GammaHUpper`/`Gamma0Upper` from `Def_CohCarrier_Level:90–210` and
the explicit `uElt`/`gElt` coset representatives of the two `S_` files; they are
the Hecke coset count, not the group vocabulary, so they close the topic rather
than open it.

## Notes

- **(b) is a promotion, not a transcription.** The pin keeps these `private`;
  the port makes them public because they are the mathematics
  (`sl2_surj` is the lifting statement that the whole mod-`N` discussion of
  base/018 §4.3 rests on). Add them to `OWN_PROOFS` with the reason "public
  promotion of pin-private declarations", or rely on the checker's dotted
  fallback (it reads the pin's `private` names).
- **The `dedekindPsi` interface already exists** in `Defs/Jq.lean`
  (`dedekindPsi`, `dedekindPsi_prime`, `dedekindPsi_mul_prime`, …). Do not
  re-port it.
- **`card_primCosetReps_eq_dedekindPsi` is independent of `Gamma0_index`.** The
  pin proves the two counts separately (one through `ProjectiveLine`, one
  through `divisorsAntidiagonal`); port both statements and record that the
  numerical coincidence is not reused.

## Verification

- `Def_ModularCurve_ProjectiveLine.lean`, `Def_ModularCurve_PrimCosetReps.lean`,
  `S_ModularCurve_Gamma0_index.lean`,
  `S_ModularCurve_card_projectiveLine_zmod.lean`, and the three `Theorems/`
  wrappers appended to `SOURCES`; the new module to `PORT_FILES`.
- Consumer `[coset]` zone: `#eval (primCosetReps 2).card` = 3,
  `Nat.card (ProjectiveLine (ZMod 2)) = 3`, and `Gamma0_index 2` composed with
  the ported `Gamma0_two_index_eq_three` if that lands here.
- `#print axioms` clean; full `lake build` green.

## Definition of done

Module green; checker 0/0; consumer 0 errors; `logs/level-port.md` §3;
`README.md` rows.
