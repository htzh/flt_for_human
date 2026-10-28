# WORKORDER MC-5a — the Siegel unit: its `SL(2, ℤ)`-multiplier and its differentiability

**SET**: [SET-MC5.md](SET-MC5.md) §0–§5. **Story**: M4. **Silk**: 614 (390 + 224). **Net**: ≈548.
**Home**: **new** `lean/FLTForHuman/ModularCurve/SiegelUnit/Basic.lean`. Two headlines, one shared
private engine.

## The declarations

Both pin wrappers, verbatim:

```
theorem ModularCurve.siegelFun_specialLinearGroup_smul (N : ℕ)
    (α : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    ∃ μ : ℂ, μ ^ 12 = 1 ∧ ∀ (r s : ℤ) (τ : UpperHalfPlane),
      siegelFun N r s ((α • τ : UpperHalfPlane) : ℂ) =
        μ * siegelFun N (r * (α : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + s * (α : Matrix (Fin 2) (Fin 2) ℤ) 1 0)
          (r * (α : Matrix (Fin 2) (Fin 2) ℤ) 0 1 + s * (α : Matrix (Fin 2) (Fin 2) ℤ) 1 1) (τ : ℂ)

theorem ModularCurve.SiegelUnit.differentiableOn_siegelFun (N : ℕ) (r s : ℤ) :
    DifferentiableOn ℂ (fun z : ℂ => siegelFun N r s z) {z : ℂ | 0 < z.im} ∧
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : UpperHalfPlane => siegelFun N r s (τ : ℂ))
```

Pin proofs: `P2M/Sol/S_ModularCurve_siegelFun_specialLinearGroup_smul.lean` (390 lines) and
`P2M/Sol/S_ModularCurve_SiegelUnit_differentiableOn_siegelFun.lean` (224). Both files build the same
q-product prelude — `qq`/`qa`/`pref`/`sprod` and `siegelFun_eq : siegelFun N r s τ = pref N r s τ *
sprod N r s τ` — which this module writes **once**, `private`, then both proofs. The
`siegelFun_specialLinearGroup_smul` proof is the `S`/`T` decomposition of `α` with the multiplier `μ`
(its `μ ^ 12 = 1` is the eta-quotient weight count); the differentiability proof is uniform
convergence of the `∏'` on `{0 < im}` plus the chain rule through the coercion.

## Vocabulary

- `ModularCurve.siegelFun`, `siegelFun_def` — `ModularCurve/Defs/SiegelFunction.lean` (D6, landed).
- `jacobiTheta_two_eq_tprod` — `ModularForms/JacobiThetaTripleProduct.lean` (the one premise; import).
- mathlib's `tprod` API, `Complex.exp`, `UpperHalfPlane` action (`Matrix.SpecialLinearGroup • ℍ`).
- The port has **no** `qParam`/`tprod` wrapper of its own — use mathlib directly.

## Traps

1. The prelude is `private` (the wire has statements for the two headlines only); record that in the
   header, as the MC-4a module did.
2. `MDifferentiable` needs `open scoped Manifold` (the pin opens it at file top); `𝓘(ℂ)` is the
   model with corners for `ℂ`.
3. 390's `μ` must be *constructed*, not chosen: the pin's `μ` is a product over the
   `S`/`T`-decomposition, and `μ ^ 12 = 1` is proved from the weight-12 count. Do not weaken it.
4. `α • τ` is the `SpecialLinearGroup` action on `ℍ` and the statement coerces back to `ℂ`;
   keep the pin's coercion shape.
5. Do not transcribe the pin's `p2m_export`/`p2m_open`, the `P2MW.S_` namespace, or any
   `attribute [-simp]` prelude.

## Gates

1. `cd lean && lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 FLTForHuman/ModularCurve/SiegelUnit/Basic.lean` → silent, zero warnings.
2. `flock /tmp/lean-build.lock lake build FLTForHuman.ModularCurve.SiegelUnit.Basic` → success (use
   the background channel on a busy tree, FR-0060).
3. `python3 spec/check_port.py --force FLTForHuman/ModularCurve/SiegelUnit/Basic.lean` → both
   headlines `ok`, 0 mismatch / 0 missing.
4. `#print axioms` on both → `[propext, Classical.choice, Quot.sound]`.
5. Exactly **four** `spec-pin:` lines: the two `Thm_` wrappers and their `S_` copies.
6. `dedup.py --within --tier shape` → 0 clusters. No `sorry`/`admit`/`axiom`/`native_decide`, no
   `set_option`, no linter suppression, no other file, no git, no tree build; every command under 2
   minutes.
