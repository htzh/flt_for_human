# WORKORDER-AF1-proofs — the carrier's harvest: three modules, eight headlines

**Status (closed 2026-11-02): landed and reviewed green.** One worker dispatch, three new modules,
**eight public headlines**, no blocker at any point:

| step | module (Δ lines) | checker | build | axioms |
|---|---|---|---:|---|
| B1 | `NumberTheory/NumberField/TateGlobal/NormExponent.lean` (**+246**, 21 decls) | **1 ok** / 0 / 0 | silent, 3.2 s | clean |
| C1–C5 | `AutomorphicForm/Adelic/Cusp/SpectrumCarrierAPI.lean` (**+330**, 5 decls) | **5 ok** / 0 / 0 | silent, 6.0 s | clean ×5 |
| D1–D2 | `AutomorphicForm/Adelic/Cusp/SpectrumPairing.lean` (**+281**, 2 decls) | **2 ok** / 0 / 0 | silent, 5.0 s | clean ×2 |

`dedup.py --within` 0 clusters on each; `spec/AutomorphicFormSetAF1Consumer.lean` extended to **252
lines / ten zones**, 0 errors; nothing frozen was touched. The landing record with the deviations —
B1's 21-for-24 declaration count (two pin-`private` helpers replaced by the port's public copies under
different names, which the pricing could not see), the `push Not` and `linter.unusedVariables` fixes,
D2's import-don't-reprove list — is [SET-AF1.md](SET-AF1.md) §1.5, and the post-landing re-read is its
§8. The original order follows.

**Status as issued (2026-11-02): the definition layer was landed; the proof bodies were this order.**
Scope: [SET-AF1.md](SET-AF1.md). The two definition modules the set turns on are **done and frozen**
by the manager (§2 of this order): do not edit them, do not rename their declarations, do not add
markers to them. What remains is the ground node **B1** and the seven ready rows **C1–C5, D1–D2** —
three new modules, eight public headlines.

**Audience.** A fresh coding session. Method: [porting-playbook.md](../../porting-playbook.md) §3–§5;
wire: the per-module protocol — a `spec-pin:` header per module and `spec/check_port.py`, no
in-source per-declaration marker.

**Do the three modules in the order below** (B1 → C → D): C5 needs B1's headline, and D is
independent of B1 but shares the gate. Log every build in `lean/tmp/`. **Report a blocker as soon as
one appears** (§6): do not grind a single proof for more than ~20 minutes, and never leave a
`sorry` in the tree.

## 1. What the two gates give you (frozen API)

`FLTForHuman/AutomorphicForm/Adelic/Cusp/SpectrumCarrier.lean` — 289 lines, **41 declarations, all
`ok`** against `Definitions/Def_AutomorphicForm_CuspidalSpectrumCarrier.lean` (pin `aa2d8b3`).
Namespace
`AutomorphicForm.CuspidalSpectrum`. `F` is an **explicit** argument of every declaration
(`variable (F : Type) [Field F] [NumberField F]`), as at the pin.

The API you will call: `IsSlabFundamentalDomain F α β Φ₀` (`pos`, `lt`, `subset`,
`isFundamentalDomain`), `fdPins F Φ₀`, `HasModulus F ξ σ`, `weight F σ`, `weightedMeasure F Φ₀ σ`,
`Carrier F Φ₀ σ`, `memberSubmodule F Φ₀ ξ`, `contMemberSubmodule F Φ₀ ξ`, `cuspMemberSubmodule F Φ₀ ξ`,
`memLp_weightedMeasure_of_mem F hΦ₀ σ hφ`, `toCarrier F hΦ₀ σ ξ`, `pairing F Φ₀ σ a b`,
`cuspSubcarrier F hΦ₀ σ ξ`, `toCuspSubcarrier F hΦ₀ σ ξ`, `cuspLevelSubcarrier`, `IsLift`, `flat`,
`isAutomorphicFnAt_fdPins_iff`, `mem_memberSubmodule_iff'`, `hasModulus_iff_units`.

`FLTForHuman/AutomorphicForm/Adelic/Cusp/SpectrumSubrep.lean` — 104 lines, **11 declarations, all
`ok`** against `Definitions/Def_AutomorphicForm_CuspidalSpectrumSubrep.lean`: `IsCuspLift` (+ `_iff`,
`_of_forall_exists`), `IsClosedCuspSubrep` (fields `isClosed`, `map_le_of_rightTranslate_fin`,
`map_le_of_rightTranslate_arch`, `map_le_of_rightConv`), `IsIrreducibleCuspSubrep`, and `top`/`bot`/
`not_…_bot`/`isClosedCuspSubrep`/`ne_bot`/`inf`.

A consumer probe already exercises both gates and must stay green:
`spec/AutomorphicFormSetAF1Consumer.lean` (`lake env lean`, 0 errors). It also shows the calling
convention (`AutomorphicForm.CuspidalSpectrum.toCarrier F hΦ₀ σ ξ …`).

## 2. Scope — three modules, eight headlines

Statements are the `Theorems/` **wrappers** verbatim; the proofs are the `S_` files' `solution`
block. Both files are in the pin clone `/home/haitao/proj/fermats-last-theorem` (pinned `aa2d8b3`).

### Module 1 — B1, the norm-exponent ground node (do this first)

`FLTForHuman/NumberTheory/NumberField/TateGlobal/NormExponent.lean` (new).

| | |
|---|---|
| pin proof | `P2M/Sol/S_NumberField_TateGlobal_exists_norm_apply_eq_ideleNorm_rpow.lean` (236 lines, 24 declarations) |
| pin statement | `Theorems/Thm_NumberField_TateGlobal_exists_norm_apply_eq_ideleNorm_rpow.lean` |
| headline | `NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow` |
| `spec-pin:` | both files (two lines, the `S_` one marked `-- comparable copy`) |

Transcribe the `solution` whole: 23 `private` helpers (`expUnit`, `coe_expUnit`, `expUnit_zero`,
`expUnit_add`, `continuous_expUnit`, `eq_expUnit_log`, `rayLog`, `rayLog_apply`, `continuous_rayLog`,
`apply_eq_rpow`, `modulus`, `modulus_apply`, `modulus_pos`, `continuous_modulus`, `modulus_principal`,
`ideleNormHom`, `ideleNormHom_apply`, `apply_eq_one_of_mem_normOneIdeles`, …) inside the pin's
`namespace IdeleClassCharacterModule` and `variable {K : Type} [Field K] [NumberField K]`, plus the
public headline at `NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow`. **Nothing of it is
in the port** (`twin_scan`: prelude 0/24) — this is all new, but it is a self-contained 219-line
transcription with no AF dependencies.

Imports: `FLTForHuman.NumberTheory.NumberField.TateGlobal.Defs`,
`…NumberField.TateGlobalCompactness`, `…NumberField.IdeleClass.Vocab`,
`…NumberTheory.AdelicHaar.PlaceMeasure`.

**Drop the pin's `attribute [-instance]` line** — it names mathlib `v4.30` instances with
`…_definitions` suffixes that do not exist at `v4.34.0`; the precedent and the wording are in the
header of `NumberTheory/RatIdele/ClassCharNorm.lean`. The ℚ analogue
(`RatIdele.exists_norm_apply_eq_ideleNorm_rpow`, `NumberTheory/RatIdele/ClassCharNorm.lean`) is
**not** an instance of this statement: do not try to reuse it.

### Module 2 — C1–C5, the carrier's API (needs the gate and B1)

`FLTForHuman/AutomorphicForm/Adelic/Cusp/SpectrumCarrierAPI.lean` (new). Two `spec-pin:` lines per
row (wrapper + `S_` with `-- comparable copy`). Namespace `AutomorphicForm.CuspidalSpectrum`.

| row | headline (`AutomorphicForm.CuspidalSpectrum.` dropped) | silo | state |
|---|---|---:|---|
| **C1** | `exists_isSlabFundamentalDomain` | 24 | 3-line proof from `exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc F 1 2`; take `α = 1, β = 2` |
| **C2** | `isotypicCuspSubmodule_le_cuspMemberSubmodule` | 29 | one `Submodule.span_le` + `isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre` |
| **C3** | `cuspKFiniteSubmodule_le_cuspMemberSubmodule` | 40 | same, plus the pin's saturation trick: `rintro φ ⟨hsat, hcont, -⟩`, `have h := hsat 1`, `rightTranslate F 1 φ = φ` |
| **C4** | `eq_zero_of_toCarrier_eq_zero` | 125 | injectivity of `toCarrier` on continuous members (§4's traps) |
| **C5** | `exists_hasModulus_of_isAutomorphicFnAt_of_continuous` | 89 | **needs B1**: `IsIdeleClassChar` + continuity of the modulus, then B1 |

Imports: `FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumCarrier`,
`…AutomorphicForm.Adelic.DetNormSlab`, `…AutomorphicForm.Adelic.DetNormSlabFundamentalDomain`,
`…NumberTheory.NumberField.TateGlobalContinuousIdeleNorm`,
`…NumberTheory.NumberField.TateGlobalNormSection`, and B1's module.

### Module 3 — D1, D2, the weighted pairing and the slab bound (needs the gate only)

`FLTForHuman/AutomorphicForm/Adelic/Cusp/SpectrumPairing.lean` (new). Two `spec-pin:` lines per row.
Namespace `AutomorphicForm.CuspidalSpectrum`.

| row | headline | silo | state |
|---|---|---:|---|
| **D1** | `rightTranslate_mem_and_pairing_rightTranslate_eq_of_ideleNorm_det_eq_one` | 198 | unit-norm right translation preserves `contMemberSubmodule`, and the weighted pairing is invariant |
| **D2** | `exists_forall_setLIntegral_le_mul_setLIntegral_of_isSlabFundamentalDomain_of_coversModCentre_ample` | 234 | **the carry-forward headline**; its 17 pin declarations are 14 importable + one ~12-line headline |

Imports: `FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumCarrier`,
`…AutomorphicForm.Adelic.IdeleNormDet`, `…NumberTheory.AdelicHaar.MulRightInvariant`,
`…AutomorphicForm.Adelic.Siegel.SlabCoveringTheorems`,
`…NumberTheory.NumberField.TateGlobalIdeleNormDet`,
`…AutomorphicForm.Adelic.WindowedSiegel.CentreCutSiegelSetAmple` (D2's covering hypothesis).

## 3. Build discipline (non-negotiable)

* **No tree build.** No `lake build` of the library target, ever.
* Edit loop: `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=1000000 <file>`, output
  into `lean/tmp/`. The module cap in `lakefile.toml` is 4M heartbeats; a file that needs more than
  `-DmaxHeartbeats=1000000` in the loop needs a narrower proof, not a `set_option`.
* Build: `flock .lake/flt_build.lock timeout 110 lake build <Module>` — one module at a time, from
  `lean/`. The project rule is that **no single tool call may run past two minutes**; the two gate
  modules built in 5.9 s and 3.9 s, so a module build that reaches the timeout is a reportable
  blocker, not something to retry in a loop. A `Replayed` line is not evidence that the `.olean`
  exists; force the module.
* **Zero warnings** in each module (`set_option` silences only the linter classes the pin itself
  forces, each with a one-line reason comment: `linter.style.haveILetI` when a `haveI`/`letI` wall
  feeds instance search, `linter.unusedVariables` only if a pin binder is genuinely unused).
* No `sorry`/`admit`/`axiom`/`native_decide`; no `import Mathlib`; no `set_option maxHeartbeats`.
* Do **not** edit any existing module, either gate module, or any `spec/` file the order does not
  name. If an existing module must change, stop and report (that is a manager decision).

## 4. Per-row traps (measured while scoping; SET-AF1 §5 has the full list)

* **C4** — `push_neg` in the pin is the deprecated spelling in this toolchain: write `push Not`
  (FR-0036). The four `Countable` instances (`F`, `Matrix (Fin 2) (Fin 2) F`, `GL₂(F)`, `Γ`) are
  built inline from `Module.finBasis ℚ F` and must stay `haveI`-local.
* **C2/C3** — read the argument order of
  `isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre` from the port
  (`DetNormSlab.lean`), not from the pin. C3's `hc`/`hd₁` are unused by the proof; keep them (they
  are the wrapper's statement, and an unused explicit hypothesis does not trip the linter).
* **C5** — the pin's `push_neg` again; `centralScalar` continuity is spelled through
  `NumberField.AdelicVolume.centralScalar_val` + `Units.continuous_iff`.
* **D1** — install `haveI : BorelSpace … := borelSpace_glBorel …`,
  `haveI := isHaarMeasure_adelicGLHaar …`, `haveI : (adelicGLHaar …).IsMulRightInvariant :=
  NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar F`; the `SMulInvariantMeasure` instance for
  `μ.restrict (detNormSlab α β)` is built by hand (`measure_preimage_mul`) and is the technical core.
* **D2** — **import the 14 declarations, do not re-prove them.** They are public in
  `AutomorphicForm/Adelic/PeterssonSlabPairing.lean` (the centre-cut trio's promotion):
  `setLIntegral_fd_le_sum_mul`, `cover_of_forall`, `setLIntegral_biUnion_translates_le`,
  `smulInvariantMeasure_restrict`, `slab`, `μH`, `Γp`, `dn`, `dn_mul`, `dn_globalPoints_mul`,
  `dn_subtype_mul`, `measurableSet_slab`, `subtype_mul_mem_slab`, `smulInvariantMeasure_slab`,
  `preimage_subtype_mul_slab`, `setLIntegral_fd_le_of_cover` — all in namespace
  `AutomorphicForm.PeterssonSlabPairing`. The pin's own two `FundamentalDomainSlab.*` copies differ
  only in binder spelling; use the `PeterssonSlabPairing` one.
* **B1** — `map_real_smul`, `QuotientGroup.lift`, `QuotientGroup.isQuotientMap_mk`,
  `isCompact_range`, `MonoidHom.mem_range`, `Subgroup.mem_subgroupOf`, `pow_unbounded_of_one_lt` are
  the whole compactness argument; `NumberField.TateGlobal.normOneIdeles` and
  `M4aHerbrand.principalIdeles` are ported (`TateGlobal/Defs.lean`, `IdeleClass/Vocab.lean`).

## 5. Gates, per module

1. `python3 spec/check_port.py --force <module>` → **0 mismatch, 0 missing**; every headline `ok`.
   Expect B1 `1 ok` (the headline; the 23 private helpers go through the pin-private fallback),
   module 2 `5 ok`, module 3 `2 ok`.
2. `#print axioms` on each of the eight headlines → `[propext, Classical.choice, Quot.sound]`
   (write the probe into `lean/tmp/`, not into the library).
3. The module's own `lake build` under `flock`/`timeout`, **silent**.
4. `python3 ../tools/deps/dedup.py --module <module> --within` → report clusters (expect none).
5. Extend `spec/AutomorphicFormSetAF1Consumer.lean` with one real composition per landed headline
   (no `#check`s) and keep it at **0 errors**; deleting any module it imports must break it.
6. Report, in your final message: per module — lines written, checker counts, build time, warnings,
   axioms, and any deviation from the pin (with the reason).

## 6. Early feedback

Send a blocker report **as soon as** any of these happens, with the failing command and the first
10 error lines:

* a module's own build exceeds ~2 minutes, or the edit loop exceeds `-DmaxHeartbeats=1000000`;
* a pin premise turns out not to be in the port at the statement the pin uses;
* a statement cannot be written at the wrapper's binders without changing it;
* an existing module would have to be edited.

Do not poll anyone; do not wait for a reply before continuing on another module.
