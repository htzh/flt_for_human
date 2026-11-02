# WORKORDER-AF3-proofs — the archimedean cut: two modules, four headlines

**Status (closed 2026-11-02): landed and reviewed green.** One worker dispatch, two new modules,
**four public headlines**, no blocker at any point:

| step | module (Δ lines) | checker | build | axioms |
|---|---|---:|---|---|
| M1–M3 | `Adelic/ArchCutSpan.lean` (**+482**, 3 public + 7 private) | **3 ok** / 0 / 0 | silent, 4.2 s | clean ×3 |
| M4 | `Adelic/ArchCutReproducer.lean` (**+567**, 1 public + 1 private) | **1 ok** / 0 / 0 | silent, 8.3 s | clean ×1 |

`dedup --within` 0 clusters on both; consumer probe `spec/AutomorphicFormSetAF3Consumer.lean` 2 zones,
0 errors, load-bearing; the ground untouched; the two modules do not import each other; neither pin
`set_option maxHeartbeats` transcribed. The landing record — the shared M2/M3 envelope and the absent
FD-only lemma, the `ArchRepAt`-only per-place lemma and the dual, the `typedCoeff` binder order, the
`Matrix.IsHermitian` spelling, four `…finset_sum` → `…finsetSum` renames — is
[SET-AF3.md](SET-AF3.md) §1.5, and the re-read is its §8 (every figure exact). The original order
follows unedited as the record of what was asked.

**Status as issued (2026-11-02): the ground is landed and frozen; the proof bodies are this order.**
Scope: [SET-AF3.md](SET-AF3.md). The ground module
`FLTForHuman/AutomorphicForm/Adelic/ArchComponentDictionary.lean` is **done** (2 declarations,
checker 2 ok / 0 mismatch / 0 missing, silent 3.1 s, `dedup --within` 0 clusters; §1 below). Do not
edit it, do not rename its declarations, do not add markers to it.

**Audience.** A fresh coding session. Method: [porting-playbook.md](../../porting-playbook.md) §3–§5;
wire: the per-module protocol — a `spec-pin:` header per module, `spec/check_port.py`, no in-source
per-declaration marker. Pin clone `/home/haitao/proj/fermats-last-theorem`, pinned `aa2d8b3`.

**Two new files, four public headlines, 1,863 raw pin lines, 1,098 net.** One module is the span
cluster (`ArchCutSpan.lean`: M1, M2, M3); the other is the reproducing kernel
(`ArchCutReproducer.lean`: M4). **They are independent** — neither imports the other — so do them in
whichever order goes green first; M4 is the set's weight (592 net) and M1–M3 are 527 net together.
Log every build in `lean/tmp/`. Report a blocker as soon as one appears (§6); never leave a `sorry` in
the tree.

## 1. What the ground gives you (frozen API)

`FLTForHuman/AutomorphicForm/Adelic/ArchComponentDictionary.lean` — 65 lines, **2 declarations**, both
public, both `ok` against the pin's pin-*private* copies (the checker's pin-private fallback), namespace
`AutomorphicForm`:

* `ext_archComponent {g g' : GL (Fin 2) (InfiniteAdeleRing F)} (h : ∀ v, archComponent F v g =
  archComponent F v g') : g = g'` — the archimedean projection is injective;
* `adelicArchGLIncl_iota_mulSingle [DecidableEq (InfinitePlace F)] (ι) (hι) (w) (k) :
  adelicArchGLIncl F (ι (Pi.mulSingle w k)) = rowIsometryInclAt₀ F w k` — the one-place factor of an
  arbitrary product `ι` lands on the port's row-isometry inclusion.

**Use them, do not re-prove them.** They are exactly the pin's `F4CutWords`/`TypeIdem` helpers; the
pin copies them into each `S_` file and the port writes them once.

## 2. Scope — two modules, four headlines

Statements are the `Theorems/` **wrappers** verbatim; proofs are the `S_` files' `solution` blocks,
replacing the port's engines by imports.

### Module 1 — M1, M2, M3: the span on the cut and the dual cut

`FLTForHuman/AutomorphicForm/Adelic/ArchCutSpan.lean` (new). Two `spec-pin:` lines per row (wrapper +
`S_` marked `-- comparable copy`); keep the pin's `AutomorphicForm` root namespace; headers in `/- … -/`
(the checker's namespace tracker mis-reads `--` header lines).

| row | headline (`AutomorphicForm.` dropped) | pin lines | net | one-line statement |
|---|---|---:|---:|---|
| **M1** | `finiteDimensional_span_translates_of_mem_archCutSubmodule` | 184 | 162 | for `ι` with `hι`, `tys`, `x` continuous in `archCutSubmodule`: the product-orbit span is finite-dimensional, continuous, inside the cut, and stable |
| **M2** | `finiteDimensional_span_rightTranslate_of_mem_archCutSubmodule` | 459 | 183 | `f ∈ archCutSubmodule` ⇒ the span of `rightTranslate F k f` over `k ∈ ⨆ w, (rowIsometryInclAt₀ F w).range` is finite-dimensional |
| **M3** | `finiteDimensional_span_rightTranslate_of_mem_archDualCutSubmodule` | 222 | 182 | the same for `archDualCutSubmodule` |

Imports: the ground, `FLTForHuman.AutomorphicForm.Adelic.ArchCutProjector`,
`FLTForHuman.AutomorphicForm.Adelic.ArchApproxIdentity.ArchInfra`,
`FLTForHuman.AutomorphicForm.Adelic.Cusp.ArchTypeSpan`,
`FLTForHuman.AutomorphicForm.Adelic.Cusp.Constituent`,
`FLTForHuman.AutomorphicForm.Adelic.IsotypicCuspSpace`. Do not import `TypeReproducer` here.

**The port engines you must import, not copy** (they are 642 of the set's 1,863 silo lines):

* `ArchCutProjector`: `placeOrbitSpan` (the pin's `orbW`), `placeOrbitSpan_mono_of_mem`,
  `finiteDimensional_placeOrbitSpan_of_mem_archTypeSubmoduleAt`,
  `finiteDimensional_placeOrbitSpan_of_mem_archCutSubmodule`, `orbitSpan_eq_span`,
  `rightTranslate_mem_of_mem_iSup_range'`, and the `Ecf`/`ρc` carrier.
* `ArchCompactOrbit`: `Ecf`, `ρc`, `orbitSpan`, `orbitSpanc`, `archRep`, `archProdIncl`,
  `archProdIncl_range`, `archRep_apply`, `ρc_apply_coe`, `continuous_archRep`,
  `continuous_dual_apply_of_separating`, `continuous_archProdIncl`,
  `isCompact_iSup_range_rowIsometryInclAt₀`, `continuous_finset_noncommProd`.
* `ArchInfra`: `isCompact_rowIsometrySubgroup₀` (it carries `[ProperSpace K]`; the pin proves its own
  34-line copy — use the port's).
* `Cusp/ArchTypeSpan`: `finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt` —
  M1's **only graph premise** (SET-AF2's `needs 1`), statement-diffed in the port.
* `Cusp/Constituent`: `rightTranslate` and its `add`/`zero`/`smul`/`comp` lemmas.

### Module 2 — M4: the reproducing kernel

`FLTForHuman/AutomorphicForm/Adelic/ArchCutReproducer.lean` (new). Two `spec-pin:` lines (wrapper +
`S_` `-- comparable copy`), same namespace.

| row | headline | pin lines | net |
|---|---|---:|---:|
| **M4** | `exists_continuous_conj_invariant_integral_mul_apply_mul_eq_of_finiteDimensional_of_le_archCutSubmodule` | 998 | 592 |

Imports: the ground, `FLTForHuman.RepTheory.TypeReproducer`,
`FLTForHuman.AutomorphicForm.Adelic.MaximalCompactFactors` (its `isCompact_rowIsometrySubgroup_detOne`
is the statement's sole graph premise), `IsotypicCuspSpace`, `Cusp/Constituent`. Do **not** import
`ArchCutSpan`.

**The engine is ported.** The pin's `AutomorphicForm.TypedCoeff` block (declarations
`exists_out_mul_eq`, `cosetCoord`, `cosetCoord_mul`, `mem_typeSubmodule_of_isRightEquivariantOn`,
`piRep`, `piRep_apply`, `piRep_single`, `typeSubmodule_piRep_le`,
`mem_iSup_typeSubmodule_of_isRightEquivariantOn_pi`, `coeffFun`, `dualCoeffFun`, `transRep`,
`coeffFun_transRep_mem_iSup`, `exists_isRightEquivariant_le_range_of_le_iSup_typeSubmodule`,
`dualCoeffFun_transRep_mem_iSup`) is `RepTheory/TypeReproducer.lean` under
`ArchApproxIdentity.*` — 15 declarations, 374 lines, tier 1. The pin's `TypeIdem.typedCoeff` (19 lines)
is the only `TypedCoeff`-level declaration not in the port; write it `private` at the head of this
module (it is a two-line composition of `coeffFun_transRep_mem_iSup` and
`dualCoeffFun_transRep_mem_iSup`).

## 3. Build discipline (non-negotiable)

* **No tree build.** Only `<module>` builds, from `lean/`, under `flock .lake/flt_build.lock` and
  `timeout 110`. A module that reaches the timeout is a reportable blocker, not something to retry in
  a loop.
* Every tool call must finish within **2 minutes**; no loop or background job to get around it.
* Edit loop: `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=1000000 <file>`, logs to
  `lean/tmp/`.
* **Zero warnings** per module. Silence a linter only for a reason the pin forces, with one line of
  comment: `linter.style.haveILetI` for an instance wall, `linter.unusedVariables` for a wrapper
  hypothesis the pin's proof does not use.
* No `sorry`/`admit`/`axiom`/`native_decide`; no `import Mathlib`; no `set_option maxHeartbeats`.
* Deprecated spellings at `v4.34`: `push_neg` → `push Not`; `Set.setOf_forall` → `Set.ofPred_forall`;
  `Set.setOf_and` → `Set.ofPred_and`; `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`; `if_pos`/`if_neg`/
  `dif_pos`/`dif_neg` → `ite_eq_left`/`ite_eq_right`/`dite_eq_left`/`dite_eq_right` (FR-0094).

## 4. Traps

**M1 (184).** (i) The row's body is the pin's private `spanOn` (5 lines: the translate span over the
products supported on a finite place set `s`) and `finiteDimensional_spanOn_and_le` (90 lines: a
`Finset` induction over `s`, whose `insert` step splits `κ = Pi.mulSingle w (κ w) * κ'` and applies the
ground's `adelicArchGLIncl_iota_mulSingle`, closing with the ported per-place
`CuspidalConstituent.finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt` and
`Submodule.finiteDimensional_iSup`). The `solution` (40 lines) instantiates at `s = univ` and repackages.
Keep both helpers `private`. (ii) `ι` and `hι` are hypotheses — do **not** instantiate
`ι := inclArch F`; the row is stated for an arbitrary product. (iii) The statement's span is over
`Set.range (fun κ => fun g => x (g * adelicArchGLIncl F (ι κ)))`, not a `⨆` — do not re-spell it.
(iv) `[DecidableEq (InfinitePlace F)]` is not one of this row's binders: write `classical` inside the
proof (the pin does), do not add a binder.

**M2 (459).** (i) `⨆ w, (rowIsometryInclAt₀ F w).range` lives in `AdelicGL2 (𝓞 F) F`, not in the
archimedean `GL₂`; the port's `ArchCutProjector.orbitSpan` is stated with the same index. (ii)
`rightTranslate` is `Cusp/Constituent`'s. (iii) `isCompact_rowIsometrySubgroup₀` is `ArchInfra`'s.
(iv) The pin's `finiteDimensional_orbitSpan_of_mem_archCutSubmodule` is
`ArchCutProjector.finiteDimensional_placeOrbitSpan_of_mem_archCutSubmodule` (per place) plus the
`iSup`/`Finset` bookkeeping — check the port's per-place lemma's statement before rewriting the
induction.

**M3 (222).** `orbW` is `placeOrbitSpan`; the two private inductions are the projector's
`finiteDimensional_placeOrbitSpan_of_mem_archTypeSubmoduleAt` and its `iSup` corollary. The dual cut's
membership normal form is `mem_archDualCutSubmodule_iff` (`IsotypicCuspSpace`), whose right side is the
`∀ w, f ∈ ⨆ i : Fin (tys.card w), archDualTypeSubmoduleAt F w (tys.rep w i)` — keep the `Fin (tys.card w)`
index and the pointwise `⨆`; the port's `archDualTypeSubmoduleAt` is `typeSubmodule … ρ.dual`.

**M4 (998).** (i) The six-conjunct `∃ e` body is the wrapper's — transcribe in order. (ii) The pin's
`set_option maxHeartbeats 3200000 in solution` is **not** transcribed: run at `-DmaxHeartbeats=1000000`
and report a wall rather than adding `set_option` (the project cap is 4M; this row may need it). (iii)
The kernel step averages `Pm` over the compact group by Haar: `Pm`, `Hm`, `Dm`, `Mint`, `one_mem_span_Dm`,
`exists_reproducer` are `TypeReproducer`'s — import them; if the port's `exists_reproducer` has the
right shape for the last step, use it and say so in the report. (iv) `hL2zero` is
`integrable_const` + `Integrable.mono'`; the port's `ArchApproxIdentity` file has the same argument as
a local lemma (`hint`) if you need the pattern. (v) The conj-invariance and inversion-reality steps
both go through right/left invariance of the Haar probability
(`integral_mul_right_eq_self`, `integral_mul_left_eq_self`).

## 5. Gates, per module

1. `python3 spec/check_port.py --force FLTForHuman/AutomorphicForm/Adelic/ArchCutSpan.lean` → **3 ok**,
   0 mismatch, 0 missing. Same for `…/ArchCutReproducer.lean` → **1 ok**.
2. `#print axioms` on the four headlines → `[propext, Classical.choice, Quot.sound]` (probe into
   `lean/tmp/`).
3. Each module's own `lake build` under `flock`/`timeout 110`, **silent**.
4. `python3 ../tools/deps/dedup.py --module <module> --within` → report clusters; do not write a
   helper twice.
5. Extend `spec/AutomorphicFormSetAF3Consumer.lean` with one real composition per landed headline
   (no `#check`s), at **0 errors**.
6. Report per module: lines written, checker counts, build time, warnings, axioms, and every
   deviation from the pin with its reason.

## 6. Early feedback

Message a blocker **as soon as** any of these happens, with the failing command and the first ~10
error lines:

* a module's own build reaches the timeout, or the edit loop exceeds `-DmaxHeartbeats=1000000`;
* a pin premise turns out not to be in the port at the pin's statement;
* a statement cannot be written at the wrapper's binders without changing it;
* a helper seems to belong in the ground (frozen), in the other module of the set, or in an existing
  port engine.

Do not poll anyone; do not wait for a reply before continuing on the other module. Report at the end
with the numbers of §5.6, and leave the tree silent.
