# TOPIC l1 — the `Γ_H` vocabulary

Work order for [SET-1](SET-1.md) of [PORTING-Level.md](../PORTING-Level.md).
Target module: `FLTForHuman/ModularForms/Defs/GammaH.lean`, namespace
`CohCarrier`, pinned `aa2d8b3`, mathlib `v4.34.0`.

> **Build discipline — read this first.** Every build is bounded and a blow-up is
> quarantined, not waited on. Measured with mathlib prebuilt: `lake env lean
> <module>` **~4 s**, `lake build <module>` **~2–5 s**, a heartbeat timeout
> **~15–20 s then an error** (it does not hang), a healthy full `lake build`
> **seconds to about a minute**. Run every build under `timeout 60 lake env lean
> <file>` / `timeout 90 lake build <module>`; expect ≤ 30 s; a multi-minute build
> is a blow-up to bisect, never to wait on, and **never raise `maxHeartbeats`**.
> Tell a blow-up (high user CPU) from lock contention (~0 CPU) by `time`.

## The mathematics

`Γ_H(M) = {γ ∈ Γ₀(M) : γ₁₁ ∈ H}`, for `H ≤ (Z/M)ˣ`. It is the pullback along
the lower-right character `γ₀ : Γ₀(M) → (Z/M)ˣ`, which is a unit because
`det γ = 1` makes `γ₀₀` the inverse of `γ₁₁` mod `M`. The specialisations are
`Γ_⊤ = Γ₀`, `Γ_⊥ = Γ₁`, `Γ(N) ⊆ Γ_H ⊆ Γ₀`; `Γ_H` is normal in `Γ₀`, so `Γ₀`
acts on it by conjugation, and that conjugation is the group-theoretic source of
the diamond operator. The base note is
[base/018](../../../base/018-congruence-subgroups-and-invariance.md) §2.2, §4.

## The declarations, verbatim from the pin

Statements are copied from the pin's `Definitions/`; proofs are adapted to
mathlib `v4.34.0` only. `M`, `H`, `A` are section variables as the pin has them.

```lean
-- Definitions/Def_CohCarrier_Level.lean:111
theorem Gamma0_d_mul_a (γ : Gamma0 M) :
    ((γ.1 1 1 : ℤ) : ZMod M) * ((γ.1 0 0 : ℤ) : ZMod M) = 1

-- Definitions/Def_CohCarrier_Level.lean:121
def gamma0Units : Gamma0 M →* (ZMod M)ˣ

-- Definitions/Def_CohCarrier_Level.lean:130
@[simp] theorem val_gamma0Units (γ : Gamma0 M) : (gamma0Units M γ : ZMod M) = Gamma0Map M γ

-- Definitions/Def_CohCarrier_Level.lean:133
def GammaH (H : Subgroup (ZMod M)ˣ) : Subgroup SL(2, ℤ) :=
  (H.comap (gamma0Units M)).map (Gamma0 M).subtype

-- Definitions/Def_CohCarrier_Level.lean:138
theorem mem_GammaH_iff {H : Subgroup (ZMod M)ˣ} {A : SL(2, ℤ)} :
    A ∈ GammaH M H ↔ ∃ hA : A ∈ Gamma0 M, gamma0Units M ⟨A, hA⟩ ∈ H

-- Definitions/Def_CohCarrier_Level.lean:146
theorem GammaH_le_Gamma0 (H : Subgroup (ZMod M)ˣ) : GammaH M H ≤ Gamma0 M

-- Definitions/Def_CohCarrier_Level.lean:151
theorem GammaH_top : GammaH M ⊤ = Gamma0 M

-- Definitions/Def_ModularCurve_XH.lean:20
theorem translation_mem_GammaH : ModularGroup.T ∈ CohCarrier.GammaH M H

-- Definitions/Def_ModularCurve_XH.lean:32
theorem Gamma1_le_GammaH : Gamma1 M ≤ CohCarrier.GammaH M H

-- Definitions/Def_ModularCurve_XH.lean:46
theorem GammaH_bot : CohCarrier.GammaH M ⊥ = Gamma1 M

-- Definitions/Def_ModularCurve_XH.lean:64
theorem GammaH_mono {H H' : Subgroup (ZMod M)ˣ} (h : H ≤ H') :
    CohCarrier.GammaH M H ≤ CohCarrier.GammaH M H'

-- Definitions/Def_CohCarrier_Inst.lean:39
theorem gamma0Units_surjective [NeZero M] : Function.Surjective (gamma0Units M)

-- Definitions/Def_CuspForm_HeckeOperatorFormsGammaH.lean:18
theorem Gamma_le_GammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) : Gamma M ≤ CohCarrier.GammaH M H

-- Definitions/Def_CuspForm_HeckeOperatorFormsGammaH.lean:32
instance GammaH_finiteIndex (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (CohCarrier.GammaH M H).FiniteIndex

-- Definitions/Def_CuspForm_HeckeOperatorFormsGammaH.lean:36
def gammaLift (M : ℕ) [NeZero M] (d : (ZMod M)ˣ) : Gamma0 M :=
  Classical.choose (CohCarrier.gamma0Units_surjective M d)

-- Definitions/Def_CuspForm_HeckeOperatorFormsGammaH.lean:39
theorem gamma0Units_gammaLift (d : (ZMod M)ˣ) : CohCarrier.gamma0Units M (gammaLift M d) = d

-- Definitions/Def_CuspForm_HeckeOperatorFormsGammaH.lean:42
def unitOfPrimeNotDvd {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) : (ZMod M)ˣ

-- Definitions/Def_CuspForm_HeckeOperatorFormsGammaH.lean:45
theorem gammaLift_apply_11 {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) :
    ((((gammaLift M (unitOfPrimeNotDvd hℓ hℓM) : Gamma0 M) : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = ℓ

-- Definitions/Def_CuspForm_HeckeOperatorFormsGammaH.lean:51
theorem mul_inv_mem_GammaH_of_gamma0Units_eq (ρ σ : Gamma0 M)
    (h : CohCarrier.gamma0Units M ρ = CohCarrier.gamma0Units M σ) :
    (ρ : SL(2, ℤ)) * ((σ : SL(2, ℤ)))⁻¹ ∈ CohCarrier.GammaH M H

-- Definitions/Def_CuspForm_HeckeOperatorFormsGammaH.lean:60
theorem slash_mapGL_eq_of_gamma0Units_eq (k : ℤ) {f : UpperHalfPlane → ℂ}
    (hf : ∀ γ ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f)
    (ρ σ : Gamma0 M) (h : CohCarrier.gamma0Units M ρ = CohCarrier.gamma0Units M σ) (A : GL (Fin 2) ℝ) :
    f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ) * A) =
      f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ) * A)

-- Definitions/Def_CohCarrier_Level.lean:162
abbrev H1 : Type _ := Additive ↥(GammaH M H) →+ A

-- Definitions/Def_CohCarrier_Level.lean:261
theorem GammaH_normal_in_Gamma0 : ((GammaH M H).subgroupOf (Gamma0 M)).Normal

-- Definitions/Def_CohCarrier_Level.lean:275
theorem conj_mem_GammaH (σ : Gamma0 M) (γ : ↥(GammaH M H)) :
    (σ : SL(2, ℤ)) * (γ : SL(2, ℤ)) * (σ : SL(2, ℤ))⁻¹ ∈ GammaH M H

-- Definitions/Def_CohCarrier_Level.lean:284
def conjHom (σ : Gamma0 M) : ↥(GammaH M H) →* ↥(GammaH M H)

-- Definitions/Def_CohCarrier_Level.lean:291
def diamondRaw (σ : Gamma0 M) : H1 M H A →+ H1 M H A
```

## Route notes

- **`Val`/coercion discipline.** `Gamma0 M` is a `Subgroup SL(2, ℤ)`; write
  `γ.1` for the matrix and `(γ.1 i j : ℤ)` for an entry, exactly as the pin.
- **`gamma0Units_surjective`** is the one non-trivial proof: from a unit `u`, use
  `u⁻¹.val * u.val = 1` in `ZMod M`, turn it into `(M : ℤ) ∣ …` with
  `ZMod.intCast_zmod_eq_zero_iff_dvd`, and take the explicit lift
  `!![u⁻¹.val, k; M, u.val]`.
- **`GammaH_bot`** is an antisymmetry: `≤` from `Gamma1_le_GammaH ⊥`, and `≥` by
  reading `mem_GammaH_iff`, using `Subgroup.mem_bot` and `Gamma0_d_mul_a` to
  recover `a ≡ 1`.
- **`GammaH_normal_in_Gamma0`** is the pin's: conjugate, then use
  `map_mul`/`map_inv` and `mul_inv_cancel_comm` on `gamma0Units`.
- **`diamondRaw`** needs `H1`; it is `φ.comp (Additive.toMul (conjHom σ))`, so
  port `conjHom` immediately before it.
- **v4.34.0 renames to expect:** `if_pos`/`if_neg` → `ite_eq_left`/`ite_eq_right`;
  `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`.

## Wire test

In `spec/`, a real composition: `GammaH 2 ⊤ = Gamma0 2` (`GammaH_top`),
`GammaH 2 ⊥ = Gamma1 2` (`GammaH_bot`), and `gamma0Units (gammaLift 2 d) = d`
for a concrete `d : (ZMod 2)ˣ`, with `GammaH` imported from `Defs/GammaH.lean`
and `Gamma0`/`Gamma1` from mathlib. `#print axioms` clean.
