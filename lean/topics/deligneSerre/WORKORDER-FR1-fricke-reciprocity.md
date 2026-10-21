# WORKORDER-FR1 — the Fricke reciprocity of the `q`-expansion

Port `ModularCurve.exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0` (1,307 pin
lines, 94 declarations) as **one module, one public declaration**.

The manager has already done the shared ground (WORKORDER §2). Do not re-open it.

## 1. What to deliver

`lean/FLTForHuman/ModularForms/FrickeReciprocity.lean`

* one public declaration — the headline, at the wrapper's name and statement, inside
  `namespace ModularCurve` (the pin's own namespace for it);
* everything else `private`.

The headline (pin `Theorems/Thm_ModularCurve_exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0.lean:9`,
the `FrickeRecip.solution` body at `P2M/Sol/S_…gamma0.lean:1290`):

```lean
theorem ModularCurve.exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0 (M : ℕ) [NeZero M]
    {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : ∀ n : ℕ, ∃ r : ℚ, (UpperHalfPlane.qExpansion 1 f).coeff n = (r : ℂ))
    (ι : AlgebraicClosure ℚ →+* ℂ) (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0]) :
    ∃ a : ℕ → AlgebraicClosure ℚ,
      (∀ n : ℕ, (UpperHalfPlane.qExpansion 1 ((⇑f : UpperHalfPlane → ℂ) ∣[k] W)).coeff n =
        ι (a n)) ∧
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ),
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c) →
        ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M → ((γ 1 1 : ℤ) : ZMod M) = c →
          ∀ n : ℕ, (UpperHalfPlane.qExpansion 1
            (((⇑f : UpperHalfPlane → ℂ) ∣[k] W) ∣[k] (γ : GL (Fin 2) ℝ))).coeff n = ι (σ (a n))
```

Note the statement mentions **nothing** from `FrickeRecip` — no `frickeGL`, no `IsRat`.
That is why the façade is statement-clean and why everything else can stay private.

## 2. The manager's pre-round — already landed, green, and frozen

| module | what | checker |
|---|---|---|
| `FLTForHuman/ModularForms/Level/Gamma1Slash.lean` | new: `ModularForm.Level.{ΓGL, T_mem_Gamma1, one_mem_strictPeriods, L_mem_strictPeriods_Gamma, Gamma_le_Gamma1, restrictF, coe_restrictF, resLevel, coe_resLevel, resSL, coe_resSL, le_conj_of_SL, slashForm, coe_slashForm, periodic_slash, mdifferentiable_slash, bdd_slash, analyticAt_slash}` | **18 ok** |
| `FLTForHuman/ModularForms/HeckeFrickeTrace.lean` | appended `ALTraceIdentity.frickeConj` (public, at the pin's signature; `pin:` row in `spec/decl_markers.tsv`) | **11 ok** |

**Both are frozen: do not edit them.** The namespace to open is `ModularForm.Level`.
`HeckeFrickeTrace` is `namespace ALTraceIdentity`.

## 3. Reuse map — import, never re-prove

| pin declaration(s) | port declaration to call |
|---|---|
| `ΓGL`, `T_mem_Gamma1`, `one_mem_strictPeriods`, `L_mem_strictPeriods_Gamma`, `Gamma_le_Gamma1`, `restrictF` + `coe_`, `resLevel` + `coe_`, `resSL` + `coe_`, `le_conj_of_SL`, `slashForm` + `coe_`, `periodic_slash`, `mdifferentiable_slash`, `bdd_slash`, `analyticAt_slash` | `ModularForm.Level.*` (the module above) |
| `frickeGL`, `val_frickeGL`, `det_frickeGL_pos`, `coe_frickeGL_smul` | `ALTraceIdentity.*` — signature is `(M : ℕ) (hM : M ≠ 0)`, so call `frickeGL M (NeZero.ne M)`; the pin's `[NeZero L]` is an instance binder |
| `frickeConj` | `ALTraceIdentity.frickeConj` |
| `qExpansion_coeff_unique'` | `UpperHalfPlaneAux.qExpansion_coeff_unique'`, `ModularForms/QExpansionCoeff.lean:139` |
| `qExpansion_coeff_mul_width` | the port's `UpperHalfPlane.qExpansion_coeff_mul_width`, `NumberTheory/ModularForms/QExpansionCoeff.lean:406` — **more general** than the pin's (`(m' : ℝ) * h₀` vs a variable `h'` with `h' = N * h`). Write the pin's statement as a wrapper and prove it from the port's in a few lines (`subst hh'`); do **not** transcribe the pin's 34-line proof |
| `IsRat`, `isRat_iff_exists_map`, `IsRat.mul`, `IsRat.pow`, `isRat_E4`, `isRat_E6`, `Eaux`, `coe_Eaux`, `isRat_Eaux`, `exists_weights` | `WLightS10.S_ModularCurve_exists_ratCast_qExpansion_slash_of_mem_Gamma0.X1DiamondRationalForms.*`, `ModularForms/WeightOne/Gamma0Integral.lean` (from `IsRat` at 1353 on). `open` that namespace and write the statements at the pin's spelling |
| `exists_of_mul_eq`, `exists_zeta_lift` | `ModularForms/WeightOne/RationalityDvd.lean` — note its `exists_zeta_lift` says `ζ ^ N = 1` / `zetaN N`, not `IsPrimitiveRoot`; restate at the pin's shape and derive |
| `Gamma1_le_of_dvd` | already inside `Gamma1Slash`'s import of `CongruenceSubgroupOrder` — use `Gamma1_le_of_dvd` |

**Hazard.** `Gamma0Integral.lean` carries a *second*, different `IsRat` at line 352
(`∃ p : PowerSeries ℚ, p.map (algebraMap ℚ ℂ) = φ`, `private`). It is not the pin's. Use the
public one at 1353 (`∀ n, ∃ r : ℚ, q.coeff n = (r : ℂ)`).

## 4. What to write — the body

Everything below is `private` in the new module, at the pin's own signatures (that keeps the
transcription honest and lets a later set promote what it needs).

**`Matrices` remainder** (`P2M/Sol/S_…gamma0.lean:38–174`): `eq_frickeGL`, `diagGL`,
`val_diagGL`, `det_diagGL`, `det_diagGL_pos`, `natCast_pos'`, `frickeGL_eq_S_mul`,
`frickeGL_eq_mul_diag`, `liftDiag` + `liftDiag_apply{00,01,10,11}`, `diagGL_mul_eq`,
`frickeGL_mul_mul_inv`, `frickeConj_mem_Gamma1`, `mulPt`, `coe_mulPt`, `im_mulPt`,
`diagGL_smul`, `slash_diagGL`, `smul_slash_of_det_pos`.

`diagGL (t : ℝ) (ht : 0 < t)` is `!![t,0;0,1]`, i.e. the real-parameter edition of
`ModularForm.heckeDiagMatrix` (which is `ℕ`-only, with an `if p = 0` guard) — a local copy is
right, and **do not** generalise the `Defs/HeckeOperator` hub. `mulPt t ht τ` is
`diagGL t ht • τ`; `coe_mulPt`/`im_mulPt`/`diagGL_smul` are one-liners.

**`Fourier` remainder** (`:191–298`): `mulPt_ofComplex`, `periodic_comp_mulPt`,
`mdifferentiable_comp_mulPt`, `tendsto_mulPt`, `bdd_comp_mulPt`, `qExpansion_comp_mulPt`,
and the `qExpansion_coeff_mul_width` wrapper of §3.

**`Level` remainder** (`:385–460`, `:468–558`): `le_conj_frickeGL`, `frickeForm`,
`coe_frickeForm`, `mul_inv_mem_Gamma1`, `frickeSlash_eq_of_apply_eq`, `slash_of_neg_mem`,
`fricke_slash_eq`, `fricke_eq`, `props_slash_comp_mulPt`, `props_of_eq_const_mul`,
`props_frickeSlash`, `props_fricke`, `analyticAt_of_props`, `props_comp_mulPt_nat`,
`coeff_comp_mulPt_nat`, `coeff_comp_mulPt_nat'`.

**`Rational`** (`:562–720`): the imports of §3, then `exists_lift_of_isRat` (`:707`) — the
one genuinely new lemma of the section.

**`Even` + `Odd`** (`:722–1281`, 610 lines): `evenS`, `card_of_even`, `exists_zeta_lift`,
`exists_exponent_ext`, `exists_diag_lift`, `kappa_eq`, `isRat_of_forall`, `card_of_odd`, and
the `solution` body. This is the reciprocity proper and the only part with no port
counterpart. `shapes.py` finds 81 distinct statement shapes in the pin file and no
repetition among them, so the parity split is two developments, not a twin pair — port it as
written.

## 5. Drifts already known at `v4.34.0`

* `ModularForm.translate` returns a `ModularForm`; its `toFun` is the **GL** slash while
  `⇑f ∣[k] β` for `β : SL(2, ℤ)` is the **SL** slash — bridge with
  `ModularForm.SL_slash` (`f ∣[k] γ = f ∣[k] toGL (map γ)`), e.g.
  `rw [coe_restrictF, ModularForm.coe_translate, ← ModularForm.SL_slash]`. This is the one
  place `Gamma1Slash.coe_slashForm` is not `rfl`; expect the same in `coe_frickeForm`.
* `analyticAt_cuspFunction_zero {h} {f} (hh : 0 < h) (hper) (hφ) (hbd)`.
* `ModularFormClass.bdd_at_infty` needs `[Fact (IsCusp ∞ Γ)]`; for `ΓGL (Γ₀(L))` it is found.
* `Matrix.SpecialLinearGroup.SL2_inv_expl` exists (used in `mul_inv_mem_Gamma1`).
* `strictPeriods` facts are `@[simp]` (`CongruenceSubgroup.strictPeriods_Gamma{0,1}`), so the
  pin's `strictPeriods_eq_zmultiples_one_of_T_mem` proofs are shorter in `v4.34`.
* The pin's `import P2M.Util` is nothing to port: `p2m_reactivate` is dropped, `p2m_open` is
  `open`, and `p2m_exact_reverting` does not appear here.

## 6. Build discipline

* Edit loop: `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>`
  from `lean/`. The 200k cap is a **diagnostic**: a declaration that exceeds it has an
  instance-inference defect — diagnose it, never raise the cap, never add a module-wide
  `set_option maxHeartbeats` (the pin has none here).
* When the file is done: `flock .lake/flt_build.lock timeout 300 lake build <module>`.
* **No tree `lake build`.**
* No `sorry`/`admit`/`axiom`/`native_decide`, no bare `import Mathlib` (name the imports).

## 7. Gates

```bash
cd lean
python3 spec/check_port.py --force FLTForHuman/ModularForms/FrickeReciprocity.lean
# expect: 1 ok, 0 mismatch, 0 missing, 0 own, 0 kw
```

plus `#print axioms` on the headline (`[propext, Classical.choice, Quot.sound]`), a `grep`
for the forbidden tokens, and `git status` showing only the new module.

The module header carries the wire:

```
spec-pin: Theorems/Thm_ModularCurve_exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0.lean
spec-pin: P2M/Sol/S_ModularCurve_exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0.lean
```

## 8. Stop conditions

* you need a `private` helper of a **frozen** module (`Gamma1Slash`, `HeckeFrickeTrace`) or of
  any other module → re-derive it locally and **report** it; do not edit the host;
* a statement or proof turns out to need a definition module that is not in the port → stop
  and report the missing gate;
* the headline does not close at the library cap → diagnose per §6 and report with the
  bisection, do not paper over it.

## 9. Report shape

Files written; the exact `check_port` line; the `lake build` job count and time; the axiom
line; which §3 reuse was actually taken and which was not (with the reason); every drift from
the pin's text; anything deferred. No prose beyond that.
