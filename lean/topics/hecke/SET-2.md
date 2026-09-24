# SET 2 — the Fricke dedup and the analytic layer (T2–T4)

**Status (2026-09-23): work orders written, not started.** This is the run brief
for the **second** coding set of the Hecke-operator effort, written after
reviewing SET 1. It authorizes exactly three topics:

| order | work order | object | pin files | ≈ port | prereq |
|---|---|---|---|---|---|
| 1 | [TOPIC-t2-fricke-dedup.md](TOPIC-t2-fricke-dedup.md) | remove the Fricke pair's double development by reusing mathlib's trace | 2 (531) | 300–400 | T1 |
| 2 | [TOPIC-t3-analytic-regularity.md](TOPIC-t3-analytic-regularity.md) | `mdifferentiable`/`periodic`/`isBoundedAtImInfty` for `heckeU`/`heckeT` | 7 (2,127) | 250–350 | T1 |
| 3 | [TOPIC-t4-cusp-class.md](TOPIC-t4-cusp-class.md) | the `ModularFormClass`/`CuspFormClass` bounded/zero-at-cusp layer | 4 (528) | 150–200 | T1 |

SET 1's work order is [TOPIC-slash-invariance.md](TOPIC-slash-invariance.md) (it
keeps its original name). The three SET-2 topics are mutually independent — T2
reorganizes existing code, T3 and T4 add new theorems on top of T1's block — but
run them in the order above: T2 touches a file T3/T4 will import.

**Do not start the two deferred pieces.** They are SET 3:
- **the `q`-coefficient layer** (`UpperHalfPlane.qCoeff_heckeU`/`qCoeff_heckeT`,
  `qCoeff_comp_heckeDiagMatrix_smul`, `ModularFormClass.qCoeff_*`,
  `qExpansion_*_eq_*`, and the formal `PowerSeries.heckeU`/`heckeT` link), which
  indegrees of **59/35/18** make the highest-value remaining piece; it is the
  tail of the same 353-line `S_` block T3 ports the head of.
- **the bundling** (`heckeTLin`/`heckeULin` + `heckeAlgebra`, the survey's
  Stage C), which needs T3 and T4.

If a SET-2 topic turns out to need a SET-3 declaration, prove a local `private`
helper instead and record it in the log — do not open the SET-3 modules.

## 0. What SET 1 handed over (verified)

SET 1 is done and was independently re-verified by the reviewer: checker
**682 identical (34 promoted), 0 mismatched, 0 missing, 14 own-proof**; forced
full build green, 0 warnings, no `sorry`; `#print axioms` clean on the five
public theorems and the Tier-0 block; no commits. The exact surface SET 2 builds
on:

- **`FLTForHuman/ModularForms/Defs/HeckeOperator.lean`** (247 lines) — the
  Tier-0 operator block, verbatim from the pin's
  `Def_ModularForm_HeckeOperator.lean:72–200`: `σ_hecke*`,
  `slash_hecke*_apply`, `heckeU`/`heckeT`, the definitional/zero/`_apply`/
  `add`/`smul`/`neg`/`sub` lemmas, `coeffHeckeT`/`coeffHeckeU` + nine lemmas.
  `val_heckeMatrix` is public; the rest of the helpers stay private.
- **`FLTForHuman/ModularForms/Defs/HeckeRepresentatives.lean`** (353 lines,
  24 public decls, namespace `ModularForm.HeckeRepresentatives`) — `det_eq`,
  the four `_mul_of_eq` (with the pin's `g' 1 0 = …` conjuncts), `heckeRep`,
  `redMatrix`, `heckeRep_mul`, the `ZMod p` reindexing helpers, and the two
  workhorses `heckeU_slash_mapGL`/`heckeT_slash_mapGL`.
- **`FLTForHuman/ModularForms/HeckeInvariance.lean`** (653 lines) — the five
  Tier-1 statements (`heckeU_slash_eq_self_of_mem_Gamma0`,
  `heckeT_…_Gamma0`, `…_Gamma0_div`, `heckeU_add_slash_fricke_eq_zero`,
  `exists_levelOne_coe_eq_zpow_smul_add_heckeU_slash_fricke`), the second two
  in the private namespaces `HeckeFricke` (123–337) and `HeckeFrickeLevelOne`
  (358–637).
- **`spec/check_flt_statements.py`** has the five Tier-1 wrappers in `SOURCES`
  and the two new modules in `PORT_FILES`; `README.md` and `logs/hecke-port.md`
  are current.

SET 1's measured finding, which SET 2 acts on: **FLT duplicates a shared proof
block across the whole family, and the port has so far transcribed the
duplication.** T1 found it for the Γ₀ invariance files; T2–T4 find it again,
three more times.

## 1. The source of truth, and how to read it

- **Pin**: `anthropics/fermats-last-theorem@aa2d8b3`, cloned at
  `~/proj/fermats-last-theorem`. Read it; never modify it.
- For node *N* the **statement** is `Theorems/Thm_<dotted name, `_` for `.`>.lean`;
  the **proof** is `P2M/Sol/S_<same>.lean`. The wrapper is the statement
  authority — take its binders verbatim (playbook §7.4; the checker is textual).
- Definition modules are `Definitions/Def_*.lean`; their declarations have no
  `Thm_` wrapper and the checker diffs them against `Definitions/` directly.
- mathlib is the pinned `v4.34.0`; `ModularFormClass` and `CuspFormClass` are
  **mathlib** (`NumberTheory/ModularForms/Basic.lean`), as is
  `ModularForm.trace` (`NumberTheory/ModularForms/NormTrace.lean`), which T2
  reuses.
- The S-file duplication is real and large: **ten 353-line files** carry the same
  ~320-line block plus a different `solution` — six analytic (T3's:
  `mdifferentiable_heckeU/T`, `periodic_heckeU/T`, `isBoundedAtImInfty_heckeU/T`)
  and four `q`-coefficient (SET 3's: `UpperHalfPlane.qCoeff_heckeU/T`,
  `ModularFormClass.qCoeff_heckeU/T`) — and **four 132-line files** carry the same
  ~95-line block plus a different `solution`. Count before you port
  (playbook §7.5).

## 2. Build discipline — read this first

Every build is bounded and a blow-up is quarantined, not waited on. Measured in
this checkout with mathlib prebuilt (`v4.34.0`, `leanprover/lean4:v4.34.0`):
`lake env lean` on a small module **~6 s** warm (~20 s cold); the 653-line
`HeckeInvariance.lean` **~22 s**; `lake build <module>` with deps cached
**~4–6 s**; the full `lake build` is green at **4,039 jobs**, nearly all cached.

**This lakefile sets `maxHeartbeats` to 4,000,000 globally**
(`lean/lakefile.lean`), so a deterministic `whnf`/defeq blow-up does **not**
error quickly; the `timeout` bound is load-bearing.

- Run every build under a bound: `timeout 60 lake env lean <file>` and
  `timeout 180 lake build <module>`; a non-return at 120 s is a blow-up, not a
  slow build.
- On a timeout, quarantine immediately: comment the declaration out and bisect,
  or reproduce in the gitignored `Scratch.lean` with
  `set_option diagnostics true`. Do not re-run the same file hoping for a
  different result.
- **Never add a local `set_option maxHeartbeats`, and never raise the
  lakefile's.** The usual cause is a `FunLike`-quantified lemma instantiated at a
  bare function type (`DFunLike.coe` unfolds without bound) — restate the lemma
  over the concrete `ℍ → ℂ` (or the concrete `F`) instead. T1's block and T3's
  targets are already stated over concrete types; keep them that way.
- `Scratch*.lean` is gitignored. Use it for `#check` probes.
- Keep imports specific; do not `import Mathlib` unless the pin's own `S_` file
  does.
- T3/T4's likely stall points are the `Finset`/`Fintype` sums over `range p` and
  `OnePoint`, and any `[FunLike F ℍ ℂ]`-quantified lemma applied at a bare
  function — the pin's `ModularFormClass`/`CuspFormClass` theorems are over a
  class, so their instantiation is the risk.

## 3. Shared conventions

1. **Statements verbatim from the wrappers**, binders included. When the
   `S_` file's binder order differs from the wrapper's, the wrapper wins and the
   divergence goes in the log.
2. **Write each shared block once.** T2 is a pure dedup; T3 ports six files'
   common block once into one module; T4 ports four files' common block once.
   Deleting a private copy is a success, not a loss — record `grep -c` before and
   after.
3. **The checker.** Append each topic's wrappers to `SOURCES` (T3 seven, T4
   four; T2 adds none — its statements already verify). Append each new module
   to `PORT_FILES`. Target: **0 mismatched, 0 missing**; the identical count may
   move only by the new public declarations.
4. **No consumer zone.** This port has no Hecke consumer; the wire test is the
   checker plus a full `lake build`. If a topic wants a concrete
   `example`/`#check` landing, put it in `Scratch*.lean`, not the library.
5. **`logs/hecke-port.md`** is extended per topic (cost, drop counts, friction).
   `README.md`'s module table gains the new modules. The `SET`/`TOPIC` files are
   the manager's and are not rewritten by the coder.
6. **No commits.** The working tree is the hand-off.

## 4. Definition of done (per topic)

- Module(s) as named in the work order; statements verbatim from the wrappers;
  specific imports; namespace matching the pin.
- `timeout 90 lake build` green, **0 warnings**, no `sorry`/`admit`.
- `#print axioms` on the topic's public headlines: only
  `propext, Classical.choice, Quot.sound`.
- `spec/check_flt_statements.py`: the topic's sources appended; **0 mismatched,
  0 missing**.
- The dedup is demonstrated with `grep -c` counts (T2: the deleted private
  copies; T3/T4: the block exists in exactly one port module).
- `logs/hecke-port.md` section; `README.md` row(s).

## 5. What to report back

Report per topic and then for the set:

1. **The per-topic table** — modules, lines, declarations, build result, checker
   before/after.
2. **The compression** — T2's Fricke pair, T3's six-to-one, T4's four-to-one:
   pin lines vs port lines, measured. This is the set's headline: how much of
   FLT's duplication the port can remove.
3. **Which route assumptions held** — specifically, whether `ModularForm.trace`
   really discharges T2's hand-rolled trace block through the `coe_trace` +
   `sum_quotientFunc_eq` bridge, and whether any part of T3/T4's block was *not*
   shared across its files.
4. **Any statement that would not match its wrapper**, quoted rather than
   weakened.
5. **The SET-3 hand-off** — exactly what T3/T4 expose for the `q`-coefficient
   layer and the bundling, and any helper that had to stay local.
