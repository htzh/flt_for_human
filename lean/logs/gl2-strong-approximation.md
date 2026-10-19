# GL₂ strong approximation over ℚ — five engine modules and one headline

**Status: landed 2026-10-18.** Six new files, green with 0 errors and 0 warnings:

* five tier-3 engine modules under `FLTForHuman/NumberTheory/AdelicLevel/StrongApprox/` —
  `Elementary.lean` (164 lines, 14 declarations), `Membership.lean` (234, 15),
  `Conjugation.lean` (416, 8), `Gauss.lean` (109, 3), `Approximation.lean` (213, 5) — 45 public
  declarations at the pin names, namespace `NumberField.AdelicLevel.GL2StrongApproxW8M`, each
  with a `-- pin:` line, registered in `spec/UNWIRED-PUBLIC.md`;
* the listed façade `FLTForHuman/NumberTheory/AdelicLevel/StrongApproxRat.lean` (49 lines),
  one headline.

Checker **10,344 identical** (was 10,343), 0 mismatched / 0 missing, 10,680 port declarations
checked: the delta **+1** is exactly the headline. `#print axioms` on it (and on three engine
theorems) is `[propext, Classical.choice, Quot.sound]`. **No existing module was edited** — no
promotion, no hub edit, no wave.

| | |
|---|---|
| headline | `NumberField.AdelicLevel.exists_globalPoints_mul_mem_finiteIntegralGL2_rat` |
| pin proof | `P2M/Sol/S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean` (898 lines, 46 declarations) |
| statement authority | `Theorems/Thm_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean` (10 lines) |
| net new math | **874 of 898** lines — 0 substitutions, the column's first pure transcription |
| structure | 45-declaration engine public tier 3, linear five-module chain; one wired headline |
| build | tier-0 all six modules exit 0 / 0 warnings (4.2–7.1 s each); tier-1 chain 3790 jobs |
| register | 129 → 134 modules, 4055 → 4100 public, 3751 → 3796 with a pin counterpart |

## 1. What the theorem says

Strong approximation for `GL₂` at the finite places, in the form the automorphic layer needs:
for every `g : GL₂(𝔸_f(ℚ))` there is a rational point `γ : GL₂(ℚ)` whose diagonal image
`glFin (globalPoints γ)` carries `g` into the integral level subgroup `finiteIntegralGL2`:

```
∃ γ : GL₂(ℚ), glFin (globalPoints γ) * g ∈ finiteIntegralGL2 𝓞 ℚ ℚ
```

Equivalently: the image of `GL₂(ℚ)` meets every coset of `finiteIntegralGL2` — the finite
idèles are covered by the rational points times the integral level. The pin proves it for a
general Dedekind `R` with `IsPrincipalIdealRing R` (`exists_map_mul_mem_finiteIntegralGL2`) and
specializes at `R = 𝓞 ℚ` through `classNumber_eq_one_iff.mp Rat.classNumber_eq`.

The node is a graph leaf (whole demand = itself), 0 in-cone / 5 whole-project direct
dependents; its closest structural consumer is the level-`N` variant
`NumberField.AdelicLevel.exists_glFin_globalPoints_mul_mem_finiteLevelOne_rat` (397 pin lines,
4 nodes / 1,618 raw `S_` lines before this landing).

## 2. The development, layer by layer

| layer | declarations | what it does |
|---|---|---|
| elementary matrices (pin 21–128) | `lowerUnipGL2`, `diagTorusGL2`, their `_coe`/`_inv`/`_add`/`_mul`/`map_` lemmas, `conj_{unipotent,lowerUnip}_entry`, `gauss_factorization` | the two unitriangular subgroups, the `1 × u` torus, the two rank-one conjugation-entry formulas, and the four-factor Gauss (LU) identity `U · L · U · diag δ = M` for `M₁₀ = c`, `det M = δ` both units |
| the integral level (pin 130–300) | `algebraMap_finiteAdeleRing_apply`, `{one,zero}_apply_mem`, `one_matrix_apply_mem`, `unipotentGL2_mem`, `lowerUnipGL2_mem`, `diagTorusGL2_mem`, `exists_sub_algebraMap_eq_mul_integral`, `exists_common_denominator`, `ratGL` + three entry lemmas | entrywise membership in `finiteIntegralGL2`; the adèlic-box approximation; one common denominator for all entries of `γ` and `γ⁻¹`; the embedding `ratGL` of `GL₂(K)` |
| conjugation (pin 302–494) | `conj_entry_mem`, `exists_conj_{unipotent,lowerUnip}_mem`, `absorb_{unipotent,lowerUnip}_left`, `mul_lowerUnip_apply_one_zero`, `det_apply`, `exists_lowerUnip_translate_isUnit` | conjugation by a rational point of an integral-scaled unipotent stays integral; the `absorb_*` reassembly; and the 164-line valuation core finding an integral `t` with `M₁₀ + M₁₁t` a unit, by comparing `Valued.v (M₁₀ v)` and `Valued.v (M₁₁ v)` place by place |
| Gauss + global profile (pin 658–800) | `detUnit`, `detUnit_coe`, `exists_gauss_decomposition`, `exists_primeGenerator`, `finiteIdele_exists_global_profile` | the Gauss decomposition `g = U x · L u · U z · diag (detUnit g) · L (-t)`; and the PID idèle-class input: for a finite idèle `δ` a global `α` with `α⁻¹δ` and `αδ⁻¹` integral everywhere |
| approximation (pin 802–874) | `exists_ratGL_inv_mul_mem_of_finiteIdele`, `exists_map_mul_mem_finiteIntegralGL2`, `glFin_globalPoints` | assemble: `γ⁻¹g` integral for some `γ`, then the headline at `R = 𝓞 ℚ` |

## 3. Structure and the two decisions

* **Five modules, not one.** The chain is linear (`Elementary → Membership → Conjugation →
  Gauss → Approximation`), each cut is a subject with its own import needs, and the two largest
  declarations (164 and 56 lines) sit in the middle. Five ~150–400-line files keep every tier-0
  loop short and a failure local; the price is five one-line import chains.
* **A separate listed façade.** The headline is the only statement the checker diffs; the 45
  engine declarations stay tier 3, public and registered. `StrongApproxRat.lean` sits beside
  the `StrongApprox/` directory so the listed surface is one file.

**The namespace is the pin's** (`NumberField.AdelicLevel.GL2StrongApproxW8M`; `W8M` is a p2m
chunk marker and nothing else reads it), consistent with
[../topics/PORTING-AutomorphicForm.md](../topics/PORTING-AutomorphicForm.md)'s namespace policy
for the `AdelicLevel` layer.

## 4. Verification

| check | result |
|---|---|
| tier-0 `lake env lean -DautoImplicit=false -DmaxHeartbeats=200000` on all six modules | exit 0, **0 warnings** (4.2–7.1 s each) |
| tier-1 `flock … lake build FLTForHuman.NumberTheory.AdelicLevel.StrongApproxRat` | green, 3790 jobs |
| checker before | 10,343 / 0 / 0 / 42 own / 294 registered (10,679) |
| checker after | **10,344** / 0 / 0 / 42 own / 294 registered (10,680) — delta **+1**, the headline |
| `#print axioms` | headline, `exists_map_mul_mem_finiteIntegralGL2`, `exists_gauss_decomposition`, `finiteIdele_exists_global_profile`: `[propext, Classical.choice, Quot.sound]` |
| forbidden tokens | none (`sorry`/`admit`/`axiom`/`native_decide`/bare `import Mathlib`/`maxHeartbeats`) |
| register | `unwired_register.py --check` current; five modules, 45 declarations, all with a pin line |
| `git status` | the six new modules, the topic and the order, `spec/check_flt_statements.py`, `spec/UNWIRED-PUBLIC.md` — nothing else |

Wiring: the wrapper appended last to `SOURCES`; the façade appended last to `PORT_FILES`; the
`solution` `S_` file **deliberately not** listed, so the 45 engine declarations stay tier 3
(the column's convention for every engine since `continuous_ideleNorm`).

## 5. Proof adaptations (pin → v4.34.0), statements verbatim

1. **One call-site rename.** The pin's `conj_entry_mem` (pin:331) calls
   `NumberField.AdelicBox.algebraMap_mem_adicCompletionIntegers R K v n`. The port has that
   lemma only as `NumberField.AdelicLevel.algebraMap_mem_adicCompletionIntegers`
   (`AdelicLevel/IdealBall.lean:87`, explicit arguments `(v) (r)`, `R K` implicit), and the pin
   spelling is genuinely absent (`#check` gives `Unknown constant` on an `AdelicBox` import).
   The ported proof calls it bare; no alias was added and no existing module was touched.
2. **One lint suppression, declaration-scoped.** `exists_primeGenerator` (pin:727) opens with
   `haveI := IsPrincipalIdealRing.principal v.asIdeal`; the port's `linter.style.haveILetI`
   fires (the `haveI` feeds instance search for `Ideal.span_singleton_generator`, so the
   `have`/`letI` rewrite the linter suggests is not available), and the declaration carries
   `set_option linter.style.haveILetI false in` stacked under the pin's
   `omit [IsFractionRing R K] in`. Not module-level, not a heartbeat override. This is the
   column's documented house style for a single-declaration suppression
   ([../topics/PORTING-DeligneSerre.md](../topics/PORTING-DeligneSerre.md) §9).
3. **The façade's instance is a `local instance`, not the pin's in-proof `haveI`.** The pin's
   `solution` (pin:891) does `haveI : IsPrincipalIdealRing (𝓞 ℚ) := …` inside the proof. That
   is the same lint, and here there is a clean alternative: the instance stands at file scope
   as `local instance : IsPrincipalIdealRing (NumberField.RingOfIntegers ℚ) := …` and the proof
   then starts with the `obtain`. `local` keeps it out of every importer (verified: importing
   the façade and asking for `inferInstance` of that instance fails), so nothing is polluted.
   This is strictly better than a suppression and is what landed.

Everything else transcribed verbatim and compiled first try — including the pin's
`linear_combination` block in `gauss_factorization` (no `ring_nf` fallback), the `filter_upwards`
/ `split` / `rename_i` structure of the 164-line `exists_lowerUnip_translate_isUnit`, and
`glFin_globalPoints`'s `ext i j; rfl`.

**Deviations from the work order, all deliberate.** Two imports the order did not list:
`Mathlib.Tactic` in `Elementary.lean` (entrywise `fin_cases`/`ring`/`linear_combination`;
`ConstantTerm` does not pull the tactic set in) and
`Mathlib.NumberTheory.NumberField.ClassNumber` in the façade (`classNumber_eq_one_iff`,
`Rat.classNumber_eq`). The order's conditional `Mathlib.Tactic`-free design was a guess; the
landing measured it.

## 6. Residuals

* The engine's declarations have exactly one importer today (the façade): the 5 whole-project
  dependents of the headline are the intended consumers, and the closest one is the level-`N`
  variant `exists_glFin_globalPoints_mul_mem_finiteLevelOne_rat` (397 pin lines; after this
  landing its demand is 3 nodes / ≈720 lines).
* `exists_common_denominator` (pin:249) shares a name with six `ModularCurve` PD-pairing
  declarations and `detUnit` with a `ℝˣ`-valued `private def` in
  `S_AutomorphicForm_bruhatEisenstein_sub_constantTerm_isRapidlyDecreasingOn.lean`; both are
  different statements, so neither is a home to share. Recorded so a later `port_advise` run
  does not read them as duplicates.
* `Def_AutomorphicForm_AdelicLsXi` is imported by the pin silo and named by nothing in it; the
  port neither imports nor needs it.

## 7. Reproduce

```bash
cd lean
for m in Elementary Membership Conjugation Gauss Approximation StrongApproxRat; do
  timeout 110 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 \
    FLTForHuman/NumberTheory/AdelicLevel/StrongApprox/$m.lean || break
done
flock .lake/flt_build.lock timeout 280 lake build FLTForHuman.NumberTheory.AdelicLevel.StrongApproxRat
timeout 600 python3 spec/check_flt_statements.py | tail -1   # 10344 identical
python3 tools/deps/unwired_register.py --check               # current
```
