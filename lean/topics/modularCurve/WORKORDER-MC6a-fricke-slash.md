# WORKORDER MC-6a — the slash-Fricke sum over rational q-expansions

**SET**: [SET-MC6.md](SET-MC6.md) §0–§5. **Story**: M9. **Silk**: 322. **Net**: ≈261.
**Home**: **new** `lean/FLTForHuman/ModularCurve/XH/FrickeSlash.lean`.

## The declaration

Pin wrapper `Theorems/Thm_ModularCurve_exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion.lean`:

```
theorem ModularCurve.exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) {k : ℤ}
    (f : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : ∀ n : ℕ, ∃ r : ℚ, (UpperHalfPlane.qExpansion 1 f).coeff n = (r : ℂ))
    (ι : AlgebraicClosure ℚ →+* ℂ) (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0]) :
    ∃ (n : ℕ) (c : Fin n → AlgebraicClosure ℚ)
      (g : Fin n → ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
      (p : Fin n → PowerSeries ℤ), (∀ i, ModularCurve.IsIntegralQExp (g i) (p i)) ∧
        (⇑f : UpperHalfPlane → ℂ) ∣[k] W = ∑ i, ι (c i) • (⇑(g i) : UpperHalfPlane → ℂ)
```

Pin proof: `P2M/Sol/S_ModularCurve_exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion.lean`
(322 lines): `frickeGL`/`frickeForm` (the Fricke translate), the q-expansion identity and the
conjugacy `conj ∘ slash` from `FrickeReciprocity`, the `PowerSeries` Galois descent over the rational
q-expansion, and `exists_isIntegralQExp_smul_of_ratCast_qExpansion` for the integrality of the
summands.

## Vocabulary

- `CohCarrier.GammaH`, `mem_GammaH_iff` — `ModularForms/Defs/GammaH.lean`.
- `ModularCurve.restrictForm` — `ModularCurve/X1/Defs.lean`; `ModularForm.translate`,
  `ModularForm.SL_smul_slash` — `ModularForms` (via `Level/Gamma1Slash.lean` for `ΓGL`).
- `ModularCurve.IsIntegralQExp` — `ModularCurve/X1/Integral.lean`.
- The three premises (import their modules): `ModularForms/FrickeReciprocity.lean`,
  `RingTheory/PowerSeries/GaloisDescent.lean`, `ModularForms/WeightOne/Gamma0Integral.lean`.
- `UpperHalfPlane.qExpansion`, `PowerSeries`, `AlgebraicClosure ℚ` — ported/mathlib.

## Traps

1. `frickeGL` and `frickeForm` are defined **inside the pin's `S_` file**, not in a `Def_` module:
   transcribe them (they are the row's engine). The pin's `frickeGL M = !![0, -1; M, 0]` as a `GL`
   and `frickeForm f = restrictForm le_conj_frickeGL (translate f (frickeGL M))`; `eq_frickeGL`
   identifies the wrapper's `W` with it from `hW`.
2. Keep the pin's `attribute [-simp] …` prelude **out** (the port keeps those global).
3. `ι : ℚ̄ →+* ℂ` is the coefficient embedding — do not specialise it to the identity.
4. The statement's `∑ i, ι (c i) • g i` is a `Finset.univ` sum over `Fin n`; keep the
   `∑ i` spelling the wrapper uses.
5. `NeZero M` and the `W`-matrix hypothesis `hW` are statement-level; do not drop either.

## Gates

As WORKORDER-MC5a's §Gates, with: `check_port` → the headline `ok`; **two** `spec-pin:` lines (its
`Thm_` wrapper and `S_` copy); one module build (background channel on a busy tree, FR-0060);
axioms; silent; `dedup.py --within --tier shape` 0 clusters; no `set_option`, no suppression, no
other file, no git, no tree build; every command under 2 minutes.
