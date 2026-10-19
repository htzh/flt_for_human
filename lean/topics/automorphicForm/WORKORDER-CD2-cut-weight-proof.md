# WORKORDER-CD2 — the cut-vector weight decomposition (proof set)

One set, one module, one headline. Its six-module definition layer has landed
([WORKORDER-CD1-def-wave.md](WORKORDER-CD1-def-wave.md), checker `10,107 → 10,235`, +128); this
order is the 882-line proof over it. Mathematics and measurement:
[TOPIC-cut-weight-decomposition.md](TOPIC-cut-weight-decomposition.md) §1–§2.

## 1. Scope

Port one pin proof file, whole:

| | |
|---|---|
| pin statement authority | `Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_eq_sum_hasArchCharacterAt_archWeightCharAt_of_isCuspConstituent.lean` (39 lines) |
| pin proof | `P2M/Sol/S_AutomorphicForm_CuspidalConstituent_exists_eq_sum_hasArchCharacterAt_archWeightCharAt_of_isCuspConstituent.lean` (906 lines, 76 declarations) |
| net new math | **882 lines**, 77 declaration groups |
| public surface | **one theorem**, at the wrapper's exact name and statement |
| expected checker delta | **+1** |

**Not this set:** the definition layer (landed, frozen — do not edit those six modules); the
consumers of this theorem; the complex-place mirror; any wiring.

## 2. Deliverable

`FLTForHuman/AutomorphicForm/Adelic/Cusp/CutWeightDecomposition.lean`, beside the port's
`Cusp/Constituent.lean` and `Cusp/SmoothRealization.lean`:

* a docstring header stating the mathematics (a level-and-type cut vector in a cuspidal constituent
  splits into a finite sum of pure-archimedean-weight vectors at the real places) and
  "transcribed from `P2M/Sol/S_…` (pinned `aa2d8b3`, 906 lines, 76 declarations)";
* the pin's namespaces and names unchanged (`namespace AutomorphicForm.CuspidalConstituent`);
* the pin's leading `attribute [-ext] IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext` kept
  verbatim — it is a pin prelude, not a suppression of ours;
* **one public theorem**, at the wrapper's exact name
  `AutomorphicForm.CuspidalConstituent.exists_eq_sum_hasArchCharacterAt_archWeightCharAt_of_isCuspConstituent`,
  statement copied binder for binder from the wrapper; **everything else `private`** (the `S_` file
  has 76 declarations, 3 of which are substitutions, below);
* the pin's `p2m_export`/`p2m_exact` glue does not exist in the port: inline the `solution` body.

## 3. Reuse, do not re-prove

| pin declaration (in the `S_` file) | port declaration |
|---|---|
| `rotMat` (`:406`, 3 lines) | `AutomorphicForm.RealIwasawa.rot`, `FLTForHuman/AutomorphicForm/Iwasawa/Real/Core.lean` (tier 3) |
| `rotGL` (`:426`, 3 lines) | `AutomorphicForm.RealIwasawa.rotGL`, same module |
| third substitution | `port_advise` reports 3 declarations already in the port; take the list from `port_advise.py --target S_… --json` if the third is not obvious from the file |

`rotMat`/`rotGL` are the rotation matrices, and the port's are statement-identical; import them.
The other 73 declarations are new. `port_advise` reports **0 name clashes** with the port's public
surface.

## 4. What the proof needs from the port, and where it is

| need | home |
|---|---|
| `productionPinsOf`, `CarrierPins`, `levelInvariantSubmodule`, `IsCuspConstituent`, `archCutSubmodule`, `ArchTypeFamily` | `FLTForHuman/AutomorphicForm/Adelic/Cusp/Constituent.lean`, `…/CarrierPins.lean`, `…/ProductionPinsGeneral.lean` (all landed) |
| `archWeightCharAt`, `archWeightOneAt`, `HasArchCharacterAt₀` | `FLTForHuman/AutomorphicForm/Adelic/ArchType.lean`, `…/ArchWeightCharTransport.lean` (landed) |
| `whittakerCoefficient`, `IsGlobalAddChar` | `FLTForHuman/AutomorphicForm/Adelic/WhittakerCoefficient.lean` (**new this wave**) |
| `stdAddChar` and the trace data | `FLTForHuman/NumberTheory/NumberField/StandardGlobalAddChar{,Rat}.lean`, `…/AdelicTrace{,Fin,Producer}.lean`, `…/IntegralAdelicTrace.lean` (**new this wave**) |
| `integralFiniteAdeles` | `NumberField.AdelicLevel` — the port homes it there, not in `AdelicBox`; add to `open` if the pin's spelling needs it |

## 5. Known drift, recorded from the definition wave

Read §4 of [WORKORDER-CD1-def-wave.md](WORKORDER-CD1-def-wave.md) and the playbook's §7 table before
you start. The two that will recur here:

* **`AdeleRing` is a `def`**: a literal pair is an adele only at default transparency. Bind once —
  `set x : AdeleRing R K := (…) with hx` — then rewrite `x.1`/`x.2` via `show … from by rw [hx]`.
  Do not use `erw`; it unfolds the definition under study and the following projection rewrites
  find nothing.
* **Renames**: `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`; `if_pos`/`if_neg` → `ite_eq_left`/
  `ite_eq_right`; `dif_pos`/`dif_neg` → `dite_eq_left`/`dite_eq_right`; `zero_le'`/`not_lt_zero'` →
  `zero_le`/`not_lt_zero`; `exists_subset_nhds_of_isCompact'` now takes `U ∈ 𝓝ˢ (⋂ i, V i)` (wrap
  the pin's pointwise lambda in `mem_nhdsSet_iff_forall.mpr`).

The pin's `set_option linter.*`/`maxHeartbeats` preludes are dropped, not transcribed; an unused
section variable gets `omit […] in`, an unreferenced lambda binder becomes `_`.

## 6. Build discipline (copy in, verbatim)

> Edit loop `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` — the cap
> is **low on purpose**: a declaration that exceeds it has an instance-inference defect, and the low
> cap is what finds it. Never raise `maxHeartbeats`, never add a module `set_option maxHeartbeats`.
> `lake build <module>` per finished file, serialized with `flock` and bounded with `timeout`. Per
> wave, build only the wave's affected targets — **never a bare whole-tree `lake build`**. A
> whole-tree build happens once, at the session's end, and only with the user's permission.

Concretely: iterate on `CutWeightDecomposition.lean` at the low cap until exit 0 with **0 warnings**,
then `flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.AutomorphicForm.Adelic.Cusp.CutWeightDecomposition`.
No dependent module, no consumer, no checker run, no whole-tree build.

**Build-time blow-up protocol.** The named risks are the torus character decomposition (a
finite-dimensional weight splitting over `rowIsometrySubgroup₀`, with `Finset` sums and `ℂ`-module
algebra) and the cusp-constituent irreducibility steps (any place the pin pushes a submodule
inclusion through `iSup`). If a declaration hits the cap: reproduce it alone at the low cap with
`set_option diagnostics true` in `lean/tmp/`, fix the inference, re-run; never raise the cap.

## 7. Stop conditions (report, do not work around)

* The wrapper's statement will not elaborate against the landed layer → **stop**, report the
  declaration and the error; do not re-spell the statement. It is one line and enormous, and every
  hypothesis is a long applied term — the checker diffs it textually.
* A name is missing from the port that §4 says should be there → report it; do not stub.
* A declaration must be promoted from the pin's `private` for the proof to elaborate → stop and
  report (promotion is the manager's).
* A pin statement differs between the `S_` file and the wrapper → stop and report both.

## 8. Verification before stopping

| check | expected |
|---|---|
| tier-0 loop | exit 0, **0 warnings** |
| tier-1 build | green; jobs and wall/user time |
| `grep -nE "sorry\|admit\|^axiom\|native_decide\|import Mathlib\|maxHeartbeats\|set_option linter"` | no hits |
| public surface | exactly the one headline (`grep -c "^theorem "` = 1 outside comments; everything else `private`) |
| statement | diffed against the wrapper, binder for binder |
| `#print axioms` on the headline | `[propext, Classical.choice, Quot.sound]` (scratch under `lean/tmp/`) |
| `git status` | only the new module (+ `tmp/`) |

Do not wire, do not run the statement checker — the manager does both.

## 9. Report shape

Line count and declaration count against the pin's 76 (of which 3 reused, 73 new); the public
headline quoted; tier-0 and tier-1 results with timings; the axioms line; every drift fix as
`file:line → what`; anything re-derived locally or promoted (should be nothing); `git status`.
