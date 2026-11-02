# WORKORDER-AF7 — finish the big-cell transcription, then dedup it

**Status as issued (2026-11-02).** Scope: [SET-AF7.md](SET-AF7.md) — read §0, §1 and §2 first; §1 is
what the manager already did, §2 is your list. One module is mechanically transcribed and **16 sites
from green**; your job is to close them, gate the module, then run the dedup pass.

**Audience.** A fresh coding session. Method: [porting-playbook.md](../../porting-playbook.md) §3–§5
(especially §3.8's dead-code rule, which §4 below applies); pin clone
`/home/haitao/proj/fermats-last-theorem`, pinned `aa2d8b3`.

**The file.** `lean/FLTForHuman/AutomorphicForm/Adelic/BigCellExpansion.lean` — **5,594 lines**, the
pin's 5,407-line `S_` file transcribed mechanically at the pin's namespaces, 471 `private`
declarations and 1 public headline (`AutomorphicForm.bigCell_eq_sum_pureTensor_of_flat_family`, the
`Theorems/` wrapper's statement). It is already `spec-pin:`-wired (two lines in the header), has 0
importers, and a full elaboration pass takes **19.4 s** — so iterate freely.

**Do not re-transcribe anything.** The body is the pin's text; every remaining failure is v4.34 drift
or a port-side rename. If a fix would change a *statement*, stop and report it (§6).

## 1. The 16 sites

`lake env lean FLTForHuman/AutomorphicForm/Adelic/BigCellExpansion.lean` reproduces them. All line
numbers are the current file's.

| # | site | error | class / suggested fix |
|---|---|---|---|
| 1 | 843:55 | `unsolved goals` | a `rw`/`simp` step whose deprecated lemma changed shape; close it by hand |
| 2–5 | 1998:16 (×2), 2004:16 (×2) | `rfl` failed: `(of (fun i j => (if i = j then 1 else 0, kffVal x.2 i j)) i j).1 v` vs `1` / `0` | v4.34 stopped unfolding `Matrix.of`'s coercion definitionally → `rfl` becomes `simp only [Matrix.of_apply]` (or the `Prod.fst` pair projection) |
| 6–7 | 2623:2, 2628:2 | `failed to synthesize BorelSpace w.Completion` | the pin's `attribute [-instance]` + `p2m_reactivate` pair, which the port drops: supply it locally (`haveI : BorelSpace w.Completion := …`) from the port's instance, at the two declarations' headers |
| 8–10 | 2650:0, 2651:69, 2662:2 | `Not a definitional equality: ((Φ F) y).1 i` vs `(Completion.extensionEmbeddingOfIsReal ⋯) (y ↑i)`; `MeasurableEquiv.piCongrLeft_apply_apply` type mismatch | the same class: `rfl` → `simp only […]` with the port's unfolding lemmas for `extensionEmbeddingOfIsReal` / `piCongrLeft_apply` |
| 11–12 | 3056:58, 3067:6 | `hst` has type `integralFiniteAdeles (𝓞 F) F ∩ ⋂ k, t k = ∅`; `Invalid rewrite argument … proof of ?a ∈ ⊥` | argument/`rw` shape drift: `rw [hst]` → `simp only [hst, Set.mem_empty_iff_false]`-style; check what `hst`'s own statement is now |
| 13 | 3105:8 | `Unknown identifier one_apply_eq` | mathlib rename → `Pi.one_apply_eq` (qualify; check `Finsupp`/`Pi` variant) |
| 14 | 3481:47 | `rewrite` pattern `∏ i ∈ ?s, if ?c i then 1 else 0` not found in `∏ w ∈ (levelPlaces F n).attach, if cellAt … then 1 else 0` | the `Finset`-prod-`if` simp lemma moved; rewrite with the current one (`Finset.prod_attach` + `Finset.prod_ite_one`-family) |
| 15 | 3639:8, 3641:19 | `Unknown constant NumberField.AdeleRing.val_finitePartUnits` | SET-AF4 landed `finitePartUnits` (`NumberTheory/NumberField/FiniteIdeles.lean`) but not this `val_` simp lemma: state it locally in your module (3 lines) and keep it `private` |
| 16 | 5201:6 + 5200:70 | `Unknown identifier LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm` + `unsolved goals` | the theorem is ported under `EisensteinGeneral/LocalRamShells.lean` (search the port for the name): import it and call it at its port home; then close the surrounding goal |

## 2. Then make the module honest

- **Remove `set_option linter.deprecated false`** from the header (it was a scaffold for the
  `if_pos`/`if_neg` rename) and fix any residue it was hiding.
- Keep `set_option linter.style.haveILetI false` (the pin's 85 `letI := glBorel` walls) and say so in
  the header.
- Drive **zero warnings**: the `Try this: letI` notes are silenced by the above; unused-`simp`-arg
  warnings must be fixed at the site (delete the unused argument) — do not add
  `linter.unusedSimpArgs` globally.

## 3. Build and check discipline

- iterate with `lake env lean FLTForHuman/AutomorphicForm/Adelic/BigCellExpansion.lean` (~20 s a pass);
- then `flock .lake/flt_build.lock timeout 280 lake build FLTForHuman.AutomorphicForm.Adelic.BigCellExpansion`;
  **no tree build**, no dependents (0 importers);
- log builds in `lean/tmp/`;
- `python3 spec/check_port.py --force FLTForHuman/AutomorphicForm/Adelic/BigCellExpansion.lean` →
  **1 ok / 0 mismatch / 0 missing**;
- `#print axioms AutomorphicForm.bigCell_eq_sum_pureTensor_of_flat_family` →
  `[propext, Classical.choice, Quot.sound]`;
- no `sorry`/`admit`/`axiom`/`native_decide`; no `set_option maxHeartbeats`.

## 4. The dedup pass (the point of the order)

1. **`dedup.py --within --module <the module>`** — 448 declarations in one module is exactly the case
   `dedup` exists for (`--min-cost` to filter). Report clusters; refactor only the clear ones (the
   recipe's shape/name tiers), and record the ones you deliberately keep.
2. **`dedup.py --cross`** for the module — the node's prelude overlaps 612 lines already in the port
   (`port_advise`'s 56 substitutions: `adelicHeight_*` in `InducedSectionFlat`, `ArchKFiniteFamily`,
   `ArchCompactOrbit`, `AdelicHaar/PlaceMeasure`). Where the port already states it, **import it and
   delete your copy** (FR-0101's rule: promote/import + delete in the same touch).
3. **`move_dead.py`** — the pin's text predicts **31 declarations / 833 lines** never referenced again
   (the manager measured it by occurrence count: `exists_const_bigCell_eq_mul_of_flat` 86,
   `exists_finset_sum_prod_eq_of_isKfSmooth` 69, `multi_real_expansion` 65, …). Triage by the rule:
   **dead mathematics → `Reserve/AutomorphicForm/Adelic/BigCellExpansionDead.lean`** via
   `--select dead --copy`; **a duplicate of a port statement, or plumbing, → delete.** Do not hand-cut
   spans (FR-0108: cut to the end of the *body*, or let the tool do it).
4. Re-run `lake env lean` after every step; the module must stay green throughout.

## 5. The consumer probe

New `lean/spec/AutomorphicFormSetAF7Consumer.lean`, one zone, a real composition (no `#check`): read
the headline at a concrete `s = 0`/`s = 1` and compose it with the port's `flatOne`/`ideleNorm`
machinery (e.g. the big-cell value at `ff ≡ 1` against `continuous_and_hasCompactSupport_of_isFactorizableTestFn`).
Error count is the metric: **0**.

## 6. Report and blockers

Report: the module's final line count; the checker's three numbers; the axioms line; the build time and
silence; the warning count; `dedup`'s clusters (kept and fixed, with the reason); the `move_dead`
report and where each declaration went; the consumer probe's error count; and every deviation from the
pin (a renamed mathlib lemma, a local instance, a locally stated simp lemma).

**Report a blocker immediately** — with the pin line, the Lean error verbatim and what you tried — if a
site needs a *statement* change, if a port theorem cannot be found at all, or if the dedup would move
declarations across a public surface you cannot verify. Do not spend the round on it, and never leave a
`sorry` in the tree.
