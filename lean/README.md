# lean/ — FLT fragments as a Lean project

Companion to the `base/` and `math/` notes. Where those explain a step in prose,
`lean/` re-runs selected pieces of the [FLT formalization][flt] as our own Lean
code: a claim can then be checked rather than taken on faith, and a proof can be
restated in a form we find easier to read.

## Ground rules

- **Fragments only.** We copy small, self-contained definitions and lemmas out of
  FLT and adapt them. We do **not** `require` the FLT project or `import` its
  modules — a single FLT import can pull in a very large dependency cone and a
  build measured in hours. Every module here imports mathlib only.
- **Adapt, do not mirror.** The FLT proof stays the source of truth for
  correctness ([PROOF-PATH.md][proof-path]: "Where this prose and the Lean
  differ, the Lean is right"), but the presentation is ours: we may restate a
  lemma, generalize it, split it, or take a different mathlib route.
- **Cite the origin.** Each module opens with a header comment naming the FLT
  file it came from, pinned to `aa2d8b3` (never `/main`), and saying what we
  changed.
- **No silent gaps.** A module either compiles or carries an explicit, commented
  `sorry`; nothing is left merely asserted.

## Toolchain and mathlib

| component | version | where |
|---|---|---|
| Lean | `leanprover/lean4:v4.34.0` | `lean-toolchain` |
| mathlib | `v4.34.0` | `lakefile.lean` |

We pin a **mathlib release tag** so `lake exe cache get` can fetch the
community-built `.olean`s instead of compiling mathlib from source (hours of
work). We deliberately do not track FLT's own mathlib pin (`v4.33.0`): since we
rewrite fragments rather than import them, matching FLT exactly buys nothing,
and the current release is the better long-term base.

## Building

```bash
cd lean
lake build                   # the default target, FLTForHuman (both efforts)
```

The prebuilt mathlib oleans are already in place for the pinned release, so a
build needs no download. On a fresh checkout, fetch them once first:

```bash
lake exe cache get   # one-off: download the prebuilt mathlib oleans
```

### The mathlib cache

`lake exe cache get` is the only step that uses the cache. It downloads `.ltar`
archives into a pool and decompresses the oleans into
`.lake/packages/mathlib/.lake/build/`. Builds read oleans from `.lake` and never
touch the pool, so **the pool's location does not affect `lake build`**.

The pool lives at the standard per-user location, `~/.cache/mathlib` — 8906
archives, ~450 MB, shared with any other mathlib4 checkout. The server is
missing 2 of the 8908 archives; those modules simply compile locally on the first
build.

A re-fetch is needed only when the mathlib revision changes or `lean/.lake` is
removed (mathlib's `post_update` hook also runs `cache get` automatically after
`lake update`). A session that cannot write to `~`, such as the sandboxed agent,
must point `MATHLIB_CACHE_DIR` at a writable directory for that one command:

```bash
MATHLIB_CACHE_DIR="$PWD/.cache/mathlib" lake exe cache get
```

Such an override creates a second, project-local pool; `.cache/` is gitignored
alongside `.lake/` in case it does.

## Layout

| module | topic | notes |
|---|---|---|
| `FLTForHuman/Elliptic/Basic.lean` | shared setup | base change preserves `IsElliptic`; the `W⟮S⟯` point-group notation |
| `FLTForHuman/Elliptic/Universal.lean` | universal curve | coefficients as indeterminates, `polyToField`, `ringEval`, `specialize`. Ported from `Def_WeierstrassCurve_EDSEngine.lean` |
| `FLTForHuman/Elliptic/DivisionPolynomial.lean` | `ω` extras | `invar`, `ψc` + `ψc_spec`, `invarNum`/`invarDenom`, `complEDSAux`, `redInvarNum`; the rest of the multiplication-formula bridge follows |
| `FLTForHuman/Elliptic/EDS.lean` | EDS plumbing | `map_invar*`, universal `Param` indices, `universalNormEDS`, `normEDS_eq_aeval` |
| `FLTForHuman/Elliptic/EllSequence.lean` | EDS relators | `addMulSub`/`rel₄`/`net` aliases to mathlib `atom`/`atomRel`/`rel`; `HaveSameParity₄`/`StrictAnti₄`/`avg₄` and the `transf` transfer lemmas; `IsEllipticSequence (normEDS b c d)` |
| `FLTForHuman/Elliptic/Complement.lean` | complement EDS | `normEDS_mul_complEDS` and `normEDS_mul_complEDS_div`: the complement witnesses `normEDS m ∣ normEDS (n*m)` |
| `FLTForHuman/Elliptic/RedInvar.lean` | `ω` denominator | `normEDS_six_eq_mul`, `redInvarDenom`, `invarDenom_eq_redInvarDenom_mul` |
| `FLTForHuman/Elliptic/Net.lean` | EDS net | `net_normEDS` (full `IsEllipticNet`), `invar_normEDS`, `invar₂_normEDS`, `redInvar_normEDS` |
| `FLTForHuman/Elliptic/Omega.lean` | `y`-numerator | `preΨ₄_add_Ψ₂Sq_sq`, `φ_mul_ψ`, `ωe` + `ωe_spec` + `two_mul_ωe` |
| `FLTForHuman/Elliptic/MulFormula.lean` | multiplication formula | evaluation at the universal point, `ψᵤ`, `smulX`/`smulY`, `zsmul_point_eq_smulX_smulY` |
| `FLTForHuman/Elliptic/JacobianMulFormula.lean` | projective form | `smulPoly`/`smulField`, `dblXYZ`/`addXYZ`, `zsmul_eq_smulEval` |
| `FLTForHuman/Elliptic/Bridge.lean` | torsion bridge | `evalEval_ψ_sq`, `evalEval_φ`, `smul_eq_zero_iff_evalEval_ψ` |
| `FLTForHuman/Elliptic/TorsionCard.lean` | `n`-torsion cardinality | the Wronskian coprimality, the double-fiber engine, and **`card_torsion_of_isAlgClosed`** (`#E[n] = n²`) |
| `FLTForHuman/ModularCurve/Defs/Laurent.lean` | q-substitution + coefficient change | `qExpand`, `qExpandₐ`, `coeffMap`, `coeffEmb`, `laurentBaseChange`, plus the interface lemmas `coeffMap_qExpand`, `coeffEmb_qExpand`, `coeffMap_injective`, `coeffEmb_injective`. FLT `Def_ModularCurve_X0` 25–105, `Def_ModularCurve_LaurentCoeff` 16–123 |
| `FLTForHuman/ModularCurve/Defs/Twist.lean` | the unit twist `q ↦ u q` | `qTwistFun`, `qTwist` + functoriality, `qTwist_qExpand`. FLT `Def_ModularCurve_PhiGen` 18–96 |
| `FLTForHuman/ModularCurve/Defs/Jq.lean` | the `j`-series | `eisenstein4`, `etaProd`, the `Δ` unit, `jNum`, `jq` + its pole lemmas, `jqN`, `dedekindPsi`, `evalAtJ`, plus the interface lemmas `dedekindPsi_prime`, `dedekindPsi_prime_pow`, `dedekindPsi_mul_of_coprime`, `aeval_jq_eq_zero`, `transcendental_jq`. FLT `Def_ModularCurve_X0` 111–212 |
| `FLTForHuman/ModularCurve/FunctionFieldGeneration/Target.lean` | the target statement | `FunctionFieldGeneration` and its `M = 1` case. FLT `Def_ModularCurve_X0` 233–242 |
| `FLTForHuman/ModularCurve/Defs/Polynomial.lean` | the polynomial datum | `ModularPolynomialData`, `modularPolynomialDataOne`. FLT `Def_ModularCurve_X0` 215–232 |
| `FLTForHuman/ModularCurve/Defs/Fields.lean` | the two function fields | `modularFunctionField`, `modularFunctionFieldFull`, `toAdjoin`, the degeneracy lemmas. FLT `Def_ModularCurve_X0` 246–348 |
| `FLTForHuman/ModularCurve/Defs/PhiGen.lean` | the slot vocabulary | `cosetSubst`, `conj`, `phiProd`, `EvalSymm`, `PhiGenDescends`, … — the vocabulary math/010 §3's splitting input must mention. FLT `Def_ModularCurve_PhiGen` 111–309 |
| `FLTForHuman/ModularCurve/Defs/TS.lean` | `j(u q ^ e)` | `TS` and its nine coefficient/substitution lemmas. FLT `P2M/Sol/S_ModularCurve_functionFieldGeneration` 39–101 (a *solution* file) |
| `FLTForHuman/ModularCurve/FunctionFieldGeneration/Collapse.lean` | the §2 collapse | `functionFieldGeneration_iff_full_eq`, Layer 0's only theorem. FLT `Thm_…_iff_full_eq` line 6 / `S_…_iff_full_eq` 11–21 |
| `FLTForHuman/ModularCurve/JqCoefficients.lean` | the low coefficients of `jq` | `coeff_jq_zero` (`744`), `coeff_jq_one` (`196884`). A *result*, not a definition: statement from base/004, proof by mathlib's pentagonal route (`tprod_one_sub_X_pow`) rather than FLT's cluster |
| `FLTForHuman/ModularCurve/FunctionFieldGeneration/Spine.lean` | the conditional capstone | `Tight`/`Gen`/`Hall`, the proved strong induction `hall_all`, the structure `Inputs` (FLT's 8 significant remaining statements), and `functionFieldGeneration_of (h : Inputs) : FunctionFieldGeneration N` — proved, with no `sorryAx` |

The port of `#E[n](K) = n²` (math/005) has its own working record:
[logs/card-torsion-port.md](logs/card-torsion-port.md) — dependency trace,
dropped clutter, and port order — with the reusable lessons (method, gotchas,
v4.34.0 API drift, and a checklist) in [porting-playbook.md](porting-playbook.md).
The `functionFieldGeneration` effort keeps its record in
[logs/ffg-port.md](logs/ffg-port.md).

`FLTForHuman/ModularCurve/` holds the definitions of `PORTING-FFG.md` Layer 0
(the `jq` / `qExpand` / `qTwist` objects of math/010), plus the two topic modules
that followed. It sits beside `FLTForHuman/Elliptic/` under the **single**
`FLTForHuman` library — Layer 0 landed with no `sorry`, so the separate build
target it used to have was no longer needed. There is no `import Mathlib` anywhere.
**Layer 0 and all three topics are done**: eleven modules (68 declarations in 0a,
69 in 0b, 24 in `JqCoefficients`, 25 in `Spine`, plus 9 public interface lemmas in
`Defs/Laurent.lean` and `Defs/Jq.lean`) are green with zero warnings and zero
`sorry`, and the deliverable measure
[spec/ModularCurveConsumer.lean](spec/ModularCurveConsumer.lean) reports **0
errors** with Zones A, B and C all bound. Its only remaining `sorry` is the
deferred theorem's capstone. `PORTING-FFG.md` records why the theorem itself stays
deferred; the consumer's tail carries the v4.34.0 friction list, and
[spec/check_flt_statements.py](spec/check_flt_statements.py) diffs every port
declaration's statement against the pinned source (146 of 146 identical, with the
own-proof declarations exempted explicitly).

Both Layer 0 work orders are gone: they were finished, their durable material
moved into §7 of [porting-playbook.md](porting-playbook.md) — the math-clarity
principles, the overlap with the first port, and the measured cost model — and
[logs/ffg-port.md](logs/ffg-port.md) carries the record and the calibration.
Both layers finished in a single goal round against a much larger budget.

The first topic is also complete:
[TOPIC-jq-coefficients.md](TOPIC-jq-coefficients.md) closed the last two consumer
items (`jq.coeff 0 = 744`, `jq.coeff 1 = 196884`) by a mathlib route FLT does not
use — the pentagonal theorem for `∏' n, (1 - X ^ (n+1))` — rather than the
modular-form cluster. It is the first topic whose proof is ours rather than a
transcription; [logs/ffg-port.md](logs/ffg-port.md) §2c and §8.3 carry its
measured cost and the finding that FLT's own proof of these coefficients is a
standalone 237-line file, not the cluster.

The second topic is complete too:
[TOPIC-conditional-capstone.md](TOPIC-conditional-capstone.md) checked the
*architecture* of the theorem — `hall_all`, the strong induction carrying
`Tight ∧ Gen` over the divisor lattice — with FLT's significant remaining
statements as the named fields of an `Inputs` structure, and proved
`functionFieldGeneration_of (h : Inputs)`. The auxiliaries turned out to be glue,
so what remains of the deferred theorem is now a list of fields to discharge
one at a time. [logs/ffg-port.md](logs/ffg-port.md) §2d carries its measured cost
and §8.4 the field list with the reason each survives.

The third topic is complete:
[TOPIC-interface-tier.md](TOPIC-interface-tier.md) added the cone's **outbound
interface** — the nine declarations the rest of FLT reaches this segment through,
`coeffMap_qExpand` (indeg 194) down to `coeffEmb_injective` (19) — as public
lemmas placed with the objects they concern. Two of them are also `Inputs` fields,
so it shrank the debt from 10 fields to 8 while exposing 520 of the cone's
≥5-indegree tier (which sums to 946, so 55%). The two surveys in
[studies/](../studies/) are why it exists; see
[logs/ffg-port.md](logs/ffg-port.md) §2e and §8.5, and `PORTING-FFG.md` §2.1.

## Sources

- FLT: <https://github.com/anthropics/fermats-last-theorem>, local clone pinned at
  `aa2d8b3`. Per-file raw URLs follow
  `https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/<path>`;
  the generated module glosses are served at
  <https://tianyipeng.github.io/fermats-last-theorem/>.
- mathlib at `v4.34.0`:
  <https://github.com/leanprover-community/mathlib4/tree/v4.34.0>.

[flt]: https://github.com/anthropics/fermats-last-theorem
[proof-path]: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/PROOF-PATH.md
