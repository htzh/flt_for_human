# WORKORDER-AF2-proofs — the maximal compact's harvest: two modules, seven headlines

**Status (closed 2026-11-02): landed and reviewed green.** One worker dispatch, two new modules,
**seven public headlines**, no blocker at any point:

| step | module (Δ lines) | checker | build | axioms |
|---|---|---|---:|---|
| M1 | `Adelic/MaximalCompactFactors.lean` (**+439**, 5 public + 19 private) | **5 ok** / 0 / 0 | silent, 3.9 s | clean ×5 |
| M2 | `Adelic/InducedSectionMaximalCompact.lean` (**+722**, 2 public + 43 private) | **2 ok** / 0 / 0 | silent, 7.4 s | clean ×2 |

`dedup.py --within` 0 clusters on both (24 / 45 declarations); the consumer probe grew to **9 zones**,
0 errors; the gate and every existing module untouched; the two consumer modules do not import each
other. The landing record — the nine-name prelude (one more than the order priced), the `classical`
and `Disjoint` adaptations, and the new `if`/`dif` deprecation family — is
[SET-AF2.md](SET-AF2.md) §1.6, and the post-landing re-read is its §8. It also records what the
landing did *not* do: it manufactured a last-name shadow (a `private continuous_unipotentGL2`), which
FR-0095 makes the manager's post-landing correction. The original order follows.

**Status as issued (2026-11-02): the definition layer was landed; the proof bodies were this order.**
Scope: [SET-AF2.md](SET-AF2.md). The gate is **done and frozen** (§1): do not edit it, do not rename
its declarations, do not add markers to it. What remains is the two consumer modules — M1's five rows
and M2's two, seven public headlines in two new files.

**Audience.** A fresh coding session. Method: [porting-playbook.md](../../porting-playbook.md) §3–§5;
wire: the per-module protocol — a `spec-pin:` header per module and `spec/check_port.py`, no
in-source per-declaration marker.

**Do M1 first, then M2** (they are independent — M2 only needs the gate — but M1's prelude teaches the
`atPlace` idiom M2-1 reuses once). Log every build in `lean/tmp/`. Report a blocker as soon as one
appears (§6); never leave a `sorry` in the tree.

## 1. What the gate gives you (frozen API)

`FLTForHuman/AutomorphicForm/Adelic/AdelicMaximalCompact.lean` — 331 lines, **38 declarations, 37
public and `ok`** against `Definitions/Def_AutomorphicForm_AdelicMaximalCompact.lean` (pin `aa2d8b3`;
the one `private` declaration is `isClosed_ker_finComponent_comp_glFin`). Namespace
`AutomorphicForm` (**root**, not a sub-namespace), `K` an **explicit** argument of every declaration
(`variable (K : Type*) [Field K] [NumberField K]`), `S : Finset (HeightOneSpectrum (𝓞 K))` explicit
for the factor lemmas.

The API you will call: `adelicMaximalCompact K` (`mem_adelicMaximalCompact_iff`, `…_iff'`,
`glFin_mem_finiteIntegralGL2`, `isRowIsometry_archComponent`,
`archComponent_mem_rowIsometrySubgroup`, `valued_finComponent_apply_le_one`,
`valued_det_finComponent_eq_one`), `isClosed_adelicMaximalCompact`,
`WindowedSiegel.IsRowIsometry.norm_apply_le_one`, `isCompact_adelicMaximalCompact`,
`compactSpace_adelicMaximalCompact`, `maximalCompactHaar`, `measurable_subtype_val_adelicMaximalCompact`,
and the factor layer: `maximalCompactAt K S`, `maximalCompactAway K S`,
`mem_maximalCompactAt_iff`, `mem_maximalCompactAway_iff`, `maximalCompactAt_le`,
`maximalCompactAway_le`, `isClosed_maximalCompactAt`, `isClosed_maximalCompactAway`,
`isCompact_maximalCompactAt`, `isCompact_maximalCompactAway`, `compactSpace_maximalCompactAt`,
`compactSpace_maximalCompactAway`, `maximalCompactAtHaar`, `maximalCompactAwayHaar` and the four
Haar/probability instances.

A consumer probe already exercises the gate and must stay green:
`spec/AutomorphicFormSetAF2Consumer.lean` (`lake env lean`, 0 errors, 2 zones).

## 2. Scope — two modules, seven headlines

Statements are the `Theorems/` **wrappers** verbatim; proofs are the `S_` files' `solution` block.
Pin clone: `/home/haitao/proj/fermats-last-theorem` (pinned `aa2d8b3`).

### Module 1 — M1, the compact factors (five rows)

`FLTForHuman/AutomorphicForm/Adelic/MaximalCompactFactors.lean` (new). Two `spec-pin:` lines per row
(wrapper + `S_` marked `-- comparable copy`); keep the pin's `AutomorphicForm` root namespace.

| row | headline (`AutomorphicForm.` dropped) | pin lines | note |
|---|---|---:|---|
| **M1-1** | `exists_mem_maximalCompactAt_mul_mem_maximalCompactAway_eq` | 158 | `k = k₁ * k₂` with `k₁ ∈ maximalCompactAt S`, `k₂ ∈ maximalCompactAway S` |
| **M1-2** | `exists_mem_maximalCompactAt_erase_mul_eq_of_mem_maximalCompactAt` | 145 | one-place refinement, with `k' * kv = kv * k'` |
| **M1-3** | `exists_eq_mul_archSupportedAt_of_mem_maximalCompactAt_empty` | 114 | the archimedean mirror: commuting `k₁ k₂`, `k₁` supported at `w` |
| **M1-4** | `exists_maximalCompactAway_subset_of_mem_nhds_one` | 80 | every `W ∈ 𝓝 1` contains some `maximalCompactAway S₀` |
| **M1-5** | `isCompact_rowIsometrySubgroup_detOne` | 43 | `rowIsometrySubgroup₀ w.Completion` is compact |

Imports: `FLTForHuman.AutomorphicForm.Adelic.AdelicMaximalCompact`,
`FLTForHuman.NumberTheory.AdelicDock.LocalEmbedding`,
`FLTForHuman.AutomorphicForm.Adelic.ArchWeightChar` (M1-5), and the level projections M1-3 needs.

**The shared prelude — write it once, `private`, at the head of this module.** `port_advise` finds
eight names proved in ≥2 of the seven pin files (≈123 removable lines): `adelicGL2_ext` (3 copies / 30
lines), `finEntry_eq` (4 / 26), `atPlace` (2 / 4), `glArch_atPlace` (2 / 3),
`finComponent_atPlace_of_ne` (2 / 5), `localEmbed_entries_integral` (2 / 16), `atPlace_mem` (2 / 22),
`mul_atPlace_comm` (2 / 17). The strongest pair is M1-1 ↔ M1-2 (8 proofs / 93 lines). M1-3 shares none
of them. Before writing the third copy of `adelicGL2_ext`, check whether the port already has an
adelic `ext` under another name (`HeckeCharacter/Equality.lean` has adelic extensionality lemmas).

### Module 2 — M2, the induced-section consumers (two rows)

`FLTForHuman/AutomorphicForm/Adelic/InducedSectionMaximalCompact.lean` (new). Two `spec-pin:` lines
per row, same namespace.

| row | headline | pin lines | note |
|---|---|---:|---|
| **M2-1** | `flat_family_comp_mul_of_mem_adelicMaximalCompact` | 185 | a flat family over the finite-integral × row-isometry subgroup is constant in `s` there |
| **M2-2** | `exists_apply_weylInv_mul_unipotentGL2_ne_zero_of_isInducedSection_of_isKfSmooth` | 506 | the Weyl/unipotent non-vanishing; **the set's weight** (478 net lines) |

Imports: the gate, `FLTForHuman.AutomorphicForm.Adelic.{InducedSection,EtaFamily,WeylIntertwining,ArchKFinite,ArchType,SmoothAutomorphicFn}`,
`FLTForHuman.NumberTheory.AdelicHaar.PlaceMeasure`, and mathlib's `DistribChar`/`Meromorphic.Order`
modules the pin names.

**Do not let M2 import M1.** The two modules must stay independent; a shared helper found during the
work goes into the gate's module only if the *manager* agrees (report it instead of editing the gate).

## 3. Build discipline (non-negotiable)

* **No tree build.** Only `<module>` builds, from `lean/`, under `flock .lake/flt_build.lock` and
  `timeout 110`. The gate built in 3.5 s; a consumer module that reaches the timeout is a reportable
  blocker, not something to retry in a loop.
* Every tool call must finish within **2 minutes**; no loop or background job to get around it.
* Edit loop: `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=1000000 <file>`, logs to
  `lean/tmp/`.
* **Zero warnings** per module. Silence a linter only for a reason the pin forces, with a one-line
  comment: `linter.style.haveILetI` when a `haveI`/`letI` wall feeds instance search,
  `linter.unusedVariables` when a wrapper hypothesis is genuinely unused by the pin's proof (that does
  trip the linter at `v4.34`).
* No `sorry`/`admit`/`axiom`/`native_decide`; no `import Mathlib`; no `set_option maxHeartbeats`.
* Deprecated spellings at `v4.34`: `push_neg` → `push Not`; `Set.setOf_forall` → `Set.ofPred_forall`,
  `Set.setOf_and` → `Set.ofPred_and`, `Set.mem_setOf_eq` → `Set.mem_ofPred_eq` (the gate hit all
  three); the pin's `attribute [-instance]` line, where present, is dropped.

## 4. Traps

**M1-1 / M1-2.** Both are `Finset` inductions over `S`; the `S.erase v` case of M1-2 is where the
commutation hypothesis enters, and the statement's conjunction order (`k = k' * kv ∧ k' * kv = kv *
k'`) is the wrapper's — do not reorder it. `localEmbed` (the port's `AdelicDock.LocalEmbedding`) is
the engine of the finite-place bookkeeping: M1-1 uses it 8 times.

**M1-3.** The statement is a seven-conjunct existential (the `k₁` supported at `w`, the `k₂` with
trivial archimedean part at `w`, both in `maximalCompactAt ∅`); transcribe the conjuncts in the
wrapper's order, and note the hypotheses are named `_hk` (unused-flag names) — keep them.

**M1-4.** A `Finset`-choice over the neighbourhood filter: `W ∈ 𝓝 1` is refined to finitely many
places by the topology of the restricted product, then `S₀` is that finset. Pin's 68 net lines.

**M1-5.** `rowIsometrySubgroup₀` is the port's `ArchWeightCharTransport` name (the gate uses the
unprimed `rowIsometrySubgroup`); the statement is the compactness of the *determinant-one* row
isometries at one place. Its proof is a closed subset of the `‖entry‖ ≤ 1` compact set — the
archimedean half of the gate's own compactness argument, at one place.

**M2-1.** The statement is a chain of `_hφ…` hypotheses (`IsInducedSection`, `IsArchKFinite`,
`IsKfSmooth`, joint continuity, holomorphy in `s`, flatness over `adelicMaximalCompact`); keep the
wrapper's order. The flatness step is the row's only consumer of `mem_adelicMaximalCompact_iff`.

**M2-2.** The statement begins with a `let α := …` — the `let` is part of the statement the checker
hashes; keep it. The 478-line proof is the set's weight: if the edit loop needs more than
`-DmaxHeartbeats=1000000`, **report** it (the project cap is 4M and the row is the one that may need
it) rather than adding `set_option`.

## 5. Gates, per module

1. `python3 spec/check_port.py --force <module>` → **0 mismatch, 0 missing**; expect M1 **5 ok** and
   M2 **2 ok** (the pin's `private` helpers go through the pin-private fallback).
2. `#print axioms` on all seven headlines → `[propext, Classical.choice, Quot.sound]` (probe into
   `lean/tmp/`).
3. Each module's own `lake build` under `flock`/`timeout 110`, **silent**.
4. `python3 ../tools/deps/dedup.py --module <module> --within` → report clusters (M1 will show the
   `atPlace` prelude as its own cluster only if you write it twice — you should not).
5. Extend `spec/AutomorphicFormSetAF2Consumer.lean` with one real composition per landed headline
   (no `#check`s), keeping it at **0 errors**; the existing two zones stay.
6. Report per module: lines written, checker counts, build time, warnings, axioms, and every
   deviation from the pin with its reason.

## 6. Early feedback

Message a blocker **as soon as** any of these happens, with the failing command and the first ~10
error lines:

* a module's own build reaches the timeout, or the edit loop exceeds `-DmaxHeartbeats=1000000`;
* a pin premise turns out not to be in the port at the pin's statement;
* a statement cannot be written at the wrapper's binders without changing it;
* a helper seems to belong in the gate module (frozen) or in the other consumer module.

Do not poll anyone; do not wait for a reply before continuing on the other module.
