# TOPIC — GL₂ strong approximation over ℚ: one leaf, five engine modules, one headline

**Status (landed 2026-10-18).** The order that ran this note is
[WORKORDER-T5-gl2-strong-approximation.md](WORKORDER-T5-gl2-strong-approximation.md). The
landing record is §7.

**Pin.** `anthropics/fermats-last-theorem` at `aa2d8b3`; the port's mathlib is `v4.34.0`.

**Method.** The six-step loop of
[../../PORTING-DeligneSerre.md](../../PORTING-DeligneSerre.md) §3, its §4, and
[porting-playbook.md](../../../porting-playbook.md) §2–§5.

**Companions.** [../PORTING-AutomorphicForm.md](../PORTING-AutomorphicForm.md) — the topic that
homed the definition layer this node is stated over (`Def_NumberField_AdelicLevel` →
`NumberTheory/AdelicLevel/{IdealBall,Projections,Level,HeckeGen}`, 813 pin lines, landed) and
that fixes the namespace policy (`NumberField.AdelicLevel` kept verbatim). The adelic-level
successor sets are that note's D-series; this node is the first *theorem* over that layer.

## 1. The node

| | |
|---|---|
| pin statement | `Theorems/Thm_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean` (10 lines) |
| pin proof | `P2M/Sol/S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean` (898 lines, 46 declarations) |
| statement | for every `g : GL₂(𝔸_f(ℚ))` there is `γ : GL₂(ℚ)` with `glFin (globalPoints γ) * g ∈ finiteIntegralGL2` |
| proof imports | `Def_NumberField_AdelicLevel`, `Def_NumberField_AdelicBox`, `Def_AutomorphicForm_ConstantTerm` (all homed), and `Def_AutomorphicForm_AdelicLsXi`, which the proof does **not** use |
| graph position | a leaf: the whole demand is the node (`frontier.py → needed 1 / 898 lines`) |
| fan-in | 0 in-cone direct dependents, 5 whole-project |

**The mathematics.** This is strong approximation for `GL₂` at the finite places, in the form
needed downstream: **the finite idèles of a number field are covered by the rational points
times the integral level subgroup**. The pin proves it for a general Dedekind `R` with fraction
field `K` and `IsPrincipalIdealRing R`, and then specializes to `R = 𝓞 ℚ` (a PID, by
`NumberField.classNumber_eq_one_iff.mp Rat.classNumber_eq`).

Four layers, each a pin section:

* **Elementary matrices.** `lowerUnipGL2 x = !![1,0;x,1]` and `diagTorusGL2 u = !![1,0;0,u]`
  with their functoriality, plus the **Gauss factorisation identity**
  `!![1, (M₀₀-1)c⁻¹; 0, 1] * !![1,0;c,1] * !![1,(M₁₁δ⁻¹-1)c⁻¹; 0, 1] * !![1,0;0,δ] = M`
  for any `M` with `M₁₀ = c`, `det M = δ`, `c, δ` units (`gauss_factorization`).
* **The integral level subgroup.** `finiteIntegralGL2` is `GL₂` of the integral finite idèles;
  the elementary matrices with integral entries lie in it (`unipotentGL2_mem`,
  `lowerUnipGL2_mem`, `diagTorusGL2_mem`), every fraction has a common denominator
  (`exists_common_denominator`), and rational points embed as `ratGL` with the expected
  matrix-entry lemmas.
* **Conjugation by rational points.** Given `γ`, an integral adèle `b` scaled by a common
  denominator `d`, the conjugated matrix `γ⁻¹ U(b) γ` has integral entries
  (`conj_entry_mem`); `exists_conj_unipotent_mem` / `exists_conj_lowerUnip_mem` produce the
  rational shift `q` that makes it so, and the `absorb_*` lemmas reassemble a product with a
  shifted rational point. `exists_lowerUnip_translate_isUnit` (164 lines) is the valuation
  core: one finds an integral `t` making `M₁₀ + M₁₁t` a unit, by comparing
  `Valued.v (M₁₀ v)` with `Valued.v (M₁₁ v)` place by place.
* **Gauss decomposition and the global profile.** `exists_gauss_decomposition` writes any
  `g : GL₂(𝔸_f)` as `U x · L u · U z · diag (detUnit g) · L (-t)` with `t` integral;
  `finiteIdele_exists_global_profile` is the PID/idèle-class input — for a finite idèle `δ`,
  a global `α ∈ Kˣ` with both `α⁻¹δ` and `αδ⁻¹` integral everywhere, built from prime
  generators (`exists_primeGenerator`) and the finite support of `δ`;
  `exists_ratGL_inv_mul_mem_of_finiteIdele` puts `g` times a rational point into the level
  subgroup, and the headline specializes to `ℚ`.

## 2. The measurement

```bash
cd tools/deps
python3 port_advise.py --target NumberField.AdelicLevel.exists_globalPoints_mul_mem_finiteIntegralGL2_rat \
  --json build/dsl_advise.json
python3 port_plan.py --json build/dsl_advise.json
```

| quantity | value |
|---|---:|
| raw `S_` lines | 898 |
| declaration lines / groups | 874 / 46 |
| duplicate copies inside the target | 0 |
| **substitutions into the port** | **0** |
| **net new math lines** | **874** |

This is the opposite reading from the two preceding cuts of the column (the norm section was
179 net new of 901; `continuous_ideleNorm` was 65 of 2,645). Here nothing is already in the
port: the silo is a genuine 874-line development, and the port's work is a full transcription,
not a reassembly. The one thing `--ready` cannot see is the definition layer the statements
live on; it is complete (§4), so the node is genuinely ready.

**Is it a dedup case?** No. Every one of the 45 engine names has exactly one pin copy — the
strong-approximation development exists only in this file. Two names are shared *by spelling*
and are not the same statement: `exists_common_denominator` also appears in six `ModularCurve`
PD-pairing files (a different lemma over a different ring), and `detUnit` appears in
`S_AutomorphicForm_bruhatEisenstein_sub_constantTerm_isRapidlyDecreasingOn.lean` as a
`ℝˣ`-valued `private def` of `-(gOf hw x).det`. Neither is a home this engine should share, and
neither justifies a family-wide engine: the engine's only consumer is the headline.

## 3. The port structure

Five tier-3 modules under `NumberTheory/AdelicLevel/StrongApprox/`, in the pin's order, plus a
thin listed façade:

| module | pin lines | decls | imports (beyond the previous module) |
|---|---|---:|---|
| `StrongApprox/Elementary.lean` | 21–128 | 14 | `AutomorphicForm/Adelic/ConstantTerm.lean` (`unipotentGL2`) |
| `StrongApprox/Membership.lean` | 130–300 | 15 | `AdelicLevel/{Level,IdealBall}`, `AdelicBox` |
| `StrongApprox/Conjugation.lean` | 302–494 | 8 | — |
| `StrongApprox/Gauss.lean` | 658–719 | 3 | — |
| `StrongApprox/Approximation.lean` | 721–874 | 5 | `AdelicLevel/Projections.lean` (`glFin`), `AutomorphicForm/Adelic/Basic.lean` (`globalPoints`) |
| `StrongApproxRat.lean` — **listed façade** | — | 1 headline | `Approximation` |

**Why five modules and not one.** The chain is linear (`Elementary → Membership → Conjugation →
Gauss → Approximation`), each cut is a self-contained subject with its own import needs, and
the two largest declarations (`exists_lowerUnip_translate_isUnit`, 164 lines, and
`conj_entry_mem`, 56) sit in the middle of it. Splitting keeps every tier-0 edit loop short and
keeps a failing declaration isolated to a ~150-line file, at the price of five one-line import
chains — the layout WORKORDER-T1 used for its 24 modules, and the same reason.

**Why the facade is a separate module.** The headline is the only statement the checker diffs;
the 45 engine declarations are public tier 3 and registered. `StrongApproxRat.lean` sits beside
`StrongApprox/` (not inside it) so the listed surface is one file, and a consumer of the
headline does not have to import a directory of `-- pin:`-marked engines it does not name.

**Namespace.** `NumberField.AdelicLevel.GL2StrongApproxW8M` kept verbatim (the `W8M` is a p2m
chunk marker; the port keeps such names when nothing else reads them —
[../PORTING-AutomorphicForm.md](../PORTING-AutomorphicForm.md) §"Namespace policy").

## 4. Recorded negatives

* **The definition layer is complete; the two name paths differ.** The pin's
  `NumberField.AdelicBox.algebraMap_mem_adicCompletionIntegers` is the port's
  `NumberField.AdelicLevel.algebraMap_mem_adicCompletionIntegers`
  (`AdelicLevel/IdealBall.lean:87`), and its explicit arguments are `(v) (r)` rather than
  `(R K v r)`. A call-site edit; the statement is the pin's. Everything else resolves by name
  (§4 of the order tabulates all of it, mathlib included:
  `FiniteAdeleRing.isUnit_iff`, `Valuation.map_add_of_distinct_val`, `WithZero.{exp,log}`,
  `IsLocalization.exist_integer_multiples`, `Rat.classNumber_eq`).
* **`Def_AutomorphicForm_AdelicLsXi` is imported by the silo and used by nothing in it.** No
  declaration of the 46 mentions `IsLsXiFunction` or `lsXi`; the wrapper's `attribute [-simp]`
  prelude lists only `unipotentGL2_*` and `constantTerm_*` (the latter unused too). The port
  does not reproduce the prelude: its `unipotentGL2_coe` is a plain `@[simp]` and no listed
  statement depends on the `-simp` set.
* **No promotion, no hub edit.** The five engine modules are new files; the two existing
  modules they name (`ConstantTerm.lean`, `Basic.lean`, `AdelicLevel/*`, `AdelicBox.lean`) are
  imported, never edited, so no wave is owed.

## 5. Reproduce

```bash
cd tools/deps

# the node and its budget (0 substitutions — a pure transcription)
python3 port_advise.py --target NumberField.AdelicLevel.exists_globalPoints_mul_mem_finiteIntegralGL2_rat \
  --json build/dsl_advise.json
python3 port_plan.py --json build/dsl_advise.json

# the leaf reading and its fan-in
python3 frontier.py --target NumberField.AdelicLevel.exists_globalPoints_mul_mem_finiteIntegralGL2_rat \
  --include-leaves --top 5

# is any of it shared? (it is not)
for n in lowerUnipGL2 diagTorusGL2 gauss_factorization exists_gauss_decomposition \
         exists_lowerUnip_translate_isUnit finiteIdele_exists_global_profile \
         exists_map_mul_mem_finiteIntegralGL2; do
  printf '%s  ' "$n"; grep -rlE "^(private )?(noncomputable )?(theorem|def) $n\b" \
    ~/proj/fermats-last-theorem/P2M/Sol/ | wc -l
done

cd ../lean
timeout 110 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 \
  FLTForHuman/NumberTheory/AdelicLevel/StrongApproxRat.lean
```

## 6. The frontier reading after the landing

The node is a leaf with 5 whole-project dependents, so — unlike the norm section, whose engine
nine sibling files will import — this landing unblocks little on its own: what it buys is that
the statements over the `AdelicLevel` layer now exist, which is the precondition for the
`AutomorphicForm` set that consumes `exists_globalPoints_mul_mem_finiteIntegralGL2_rat`
directly. The closest successor is the level-`N` variant
`NumberField.AdelicLevel.exists_glFin_globalPoints_mul_mem_finiteLevelOne_rat` (397 pin lines),
whose demand drops from 4 nodes / 1,618 raw `S_` lines to 3 nodes / ≈720; then
`AutomorphicForm.SiegelCovering.centreCutSiegelSet_coversModCentre_rat` and the two
`AutomorphicForm` coset/isotypic nodes. None of them is ready yet.

## 7. Landing record

| | |
|---|---|
| engine | `NumberTheory/AdelicLevel/StrongApprox/{Elementary,Membership,Conjugation,Gauss,Approximation}.lean` — 164 + 234 + 416 + 109 + 213 lines, 14 + 15 + 8 + 3 + 5 = 45 public declarations, tier 3 |
| façade | `NumberTheory/AdelicLevel/StrongApproxRat.lean` — 49 lines, 1 headline, listed |
| checker | **10,344 identical / 0 mismatched / 0 missing** / 42 own-proof exempted / 294 registered-unwired (was 10,343 / 0 / 0 / 42 / 294) |
| axioms | headline and three engine theorems `[propext, Classical.choice, Quot.sound]` |
| build | tier-0 all six modules exit 0 / 0 warnings; tier-1 chain green (3790 jobs) |
| register | 129 → 134 modules, 4055 → 4100 public declarations, 3751 → 3796 with a pin counterpart |
| net new | **874 of 898 lines** — 0 substitutions, the column's first pure transcription |
| existing modules edited | **none** — no promotion, no hub edit, no wave |

Three touches on the proofs, no statement changed: one call-site rename
(`AdelicBox.algebraMap_mem_adicCompletionIntegers R K v n` →
`AdelicLevel.algebraMap_mem_adicCompletionIntegers v n`, the pin spelling being genuinely
absent from the port); one declaration-scoped `linter.style.haveILetI` suppression on
`exists_primeGenerator`; and the façade's instance hoisted to a file-scope `local instance`
instead of the pin's in-proof `haveI` (no suppression needed there). Two extra imports beyond
the order (`Mathlib.Tactic` in `Elementary`, `Mathlib.NumberTheory.NumberField.ClassNumber` in
the façade). The full record is [logs/gl2-strong-approximation.md](../../../logs/gl2-strong-approximation.md)
and the results in [WORKORDER-T5-gl2-strong-approximation.md](WORKORDER-T5-gl2-strong-approximation.md)
§8.
