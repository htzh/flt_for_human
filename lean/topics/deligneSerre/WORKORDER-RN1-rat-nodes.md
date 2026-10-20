# WORKORDER-RN1 — the two `Rat*` proof nodes

**Dispatched 2026-10-20, one coding agent, two independent modules.** The two definition gates are
already landed and green, so the nodes that were blocked in the six-family audit are now
statement-ready. Each node is taken whole; there is **no shared prelude** between them
(`port_advise`: every declaration is new, no name is proved in both files).

## 1. Scope

1. `RatAdele.denseRange_algebraMap_add_adeleSingleAt` — 309 pin lines, 21 declarations
   (1 headline + 20 `private`), leaf: strong approximation for `ℚ` away from one finite place.
2. `RatIdele.exists_norm_apply_eq_ideleNorm_rpow` — 312 pin lines, 45 declarations
   (1 headline + private helpers, 4 private instances), the absolute value of an idèle-class
   character of `ℚ`.

**Not this topic.** Nothing else of the `RatAdele`/`RatIdele` families; no edits to existing
modules; the two gate modules are frozen inputs.

## 2. Source

Pin `~/proj/fermats-last-theorem` at `aa2d8b3`; port at mathlib `v4.34.0`.

| node | `S_` proof file | wrapper (statement authority) |
|---|---|---|
| `RatAdele.denseRange_algebraMap_add_adeleSingleAt` | `P2M/Sol/S_RatAdele_denseRange_algebraMap_add_adeleSingleAt.lean` | `Theorems/Thm_RatAdele_denseRange_algebraMap_add_adeleSingleAt.lean` |
| `RatIdele.exists_norm_apply_eq_ideleNorm_rpow` | `P2M/Sol/S_RatIdele_exists_norm_apply_eq_ideleNorm_rpow.lean` | `Theorems/Thm_RatIdele_exists_norm_apply_eq_ideleNorm_rpow.lean` |

The wrapper statements (reproduce exactly; `tmp/flt-statements/statements.tsv` is the corpus):

    theorem RatAdele.denseRange_algebraMap_add_adeleSingleAt
      (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
      DenseRange fun qy : ℚ × v.adicCompletion ℚ =>
        algebraMap ℚ (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) qy.1
          + NumberField.StandardAddChar.adeleSingleAt ℚ v qy.2

    theorem RatIdele.exists_norm_apply_eq_ideleNorm_rpow
      (μ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
      (hμ : AutomorphicForm.IsIdeleClassChar (𝓞 ℚ) ℚ μ) (hc : Continuous μ) :
      ∃ σ : ℝ, ∀ x : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
        ‖((μ x : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm ℚ x ^ σ

## 3. Deliverable

1. `lean/FLTForHuman/NumberTheory/RatAdele/DenseRange.lean` — headline at the wrapper name, the 20
   pin `private` helpers kept `private` (they are the pin's own privacy; do not hide new
   mathematics). The pin's `RatAdeleDensityAux` namespace may be kept.
2. `lean/FLTForHuman/NumberTheory/RatIdele/ClassCharNorm.lean` — headline at the wrapper name, the
   pin's private helper/instance block kept private, the pin's `ModuleOfIdeleClassCharacter`
   namespace may be kept.

Wire each module with `spec-pin:` for both its `S_` file and its `Thm` wrapper. No `-- pin:`
comments in Lean source; header prose in `/- … -/`.

## 4. Inputs (already homed — import, do not re-prove)

- `FLTForHuman/LanglandsTunnell/StandardLocalConstantsAt.lean` — `NumberField.StandardAddChar.adeleSingleAt`,
  `finAdeleSingleAt`, `psiLocal`, and the `LanglandsTunnell.TateLocal` block; checker 21 ok.
- `FLTForHuman/NumberTheory/RatIdele/Normalizer.lean` — `RatIdele.ρ`, `ρ_spec`, `ρ_ne_zero`,
  `IsNormalizer`, `archCoord`, `finPart`, `ordAt`, `unitAt`, `unitIntAt`; checker 63 ok.
- `FLTForHuman/NumberTheory/AdelicBox.lean` (`adelicBox`, `infiniteBox`, `integralFiniteAdeles`,
  `exists_algebraMap_add_mem_integralFiniteAdeles`, …), `NumberTheory/AdelicLevel/Level.lean`
  (`one_mem_integralFiniteAdeles`, `mul_mem_integralFiniteAdeles`, `isCompact_integralFiniteAdeles`),
  `NumberTheory/AdelicLevel/IdealBall.lean`.
- RatIdele's three theorem premises are ported: `NumberTheory/AdelicHaar/PlaceMeasure.lean`
  (`distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one`), `NumberTheory/AdelicModulus.lean`
  (`distribHaarChar_algebraMap`), `NumberTheory/NumberField/TateGlobalContinuousIdeleNorm.lean`
  (`continuous_ideleNorm`).
- mathlib `v4.34.0` for everything else (`WithZero`, `Valued`, `HeightOneSpectrum`, `FiniteAdeleRing`,
  `RestrictedProduct`, `TateGlobal.ideleNorm`, `AutomorphicForm.IsIdeleClassChar`).

**Drop the pin's scaffolding**: `import P2M.Util`, all `p2m_*` commands, and — in the `RatIdele`
file — the whole `attribute [-instance] …` line. That line names pin-mangled mathlib-4.30 instances
(`…_definitions` suffixes) that do not exist in `v4.34.0`; copying it will not elaborate. Try
without it first; only if instance search then diverges or times out, narrow it to the specific
`v4.34` instance names still present and record the drift in the module header and the log.
Similarly the `RatAdele` file's `open scoped RestrictedProduct` is only needed if the proof names
the scoped notation.

## 5. Route and risks

Mathlib map: `WithZero`/`Valued`/`HeightOneSpectrum` valuation API for the density proof;
`FiniteAdeleRing`/`AdelicBox`/`integralFiniteAdeles` for the compactness and box decomposition;
`distribHaarChar_*` and `continuous_ideleNorm` for the character norm. `port_advise` reports
**0 substitutions and 0 shared preludes** for the pair — this is transcription, not reuse.

Stop-early risks (short blocker message at first belief; keep working on the other module):
- the `attribute [-instance]` block (see above);
- `WithZero`/`Valuation.restrict` API drift in the density proof;
- the `AdelicBox.adelicBox` membership/decomposition API in v4.34;
- the exact form of the `distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one` premise (a registered
  `own:` marker is acceptable only if the statement really differs — report before using one);
- an instance-inference blow-up at `-DmaxHeartbeats=200000` — diagnose, never raise the cap.

Never weaken a statement, never edit an existing module, never add a `sorry`.

## 6. Build discipline

Edit loop: `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>`.
Per finished file: `flock /tmp/flt.lake.lock timeout 90 lake build FLTForHuman.<path>`.
**Another agent shares this tree**: always take the `flock`. Never a bare whole-tree `lake build`.
Each tool call must finish within 2 minutes; no loop to evade the bound. 0 warnings.

## 7. Verification

- `cd lean && python3 spec/check_port.py FLTForHuman/...` per module: **1 ok, 0 mismatch, 0 missing**
  each (the headline is the whole public surface; the pin's helpers are `private` on both sides).
- `lake build` per module, 0 warnings; `grep -c sorry` 0.
- `#print axioms` on both headlines: `[propext, Classical.choice, Quot.sound]`.
- Record `lean/logs/rat-nodes.md`: lines, declarations, build jobs/wall time, checker, axioms, every
  drift and the `attribute` decision; append frictions to `lean/logs/frictions.md` as they happen.
- Do not edit `topics/PORTING-DeligneSerre.md`, `spec/old_check_stmts.py`, `spec/decl_markers.tsv`,
  the two gate modules, or any legacy module. No `git commit` / `git push`.
