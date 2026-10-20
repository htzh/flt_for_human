# The `K`-span of right translates in finitely many archimedean types — landing record

The D-S demand's **rank #2 high-impact leaf** (813 silo lines), and the column's most reuse-heavy
landing yet — 31 of the pin's 39 declarations were **already in the port**:
`AutomorphicForm.CuspidalConstituent.finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt`,
the 813-line
`P2M/Sol/S_AutomorphicForm_CuspidalConstituent_finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt.lean`
(pinned `aa2d8b3`), landed as **one module, 125 lines, one statement-checked declaration**. Order:
[topics/automorphicForm/WORKORDER-ATS-arch-type-span.md](../topics/automorphicForm/WORKORDER-ATS-arch-type-span.md).

The statement: if `φ` lies in the supremum of finitely many archimedean type submodules
`archTypeSubmoduleAt F w (ρs i)` at an infinite place `w`, then the `ℂ`-span `S` of its row-isometry
right translates is finite-dimensional, stable under those right translations, and inside the same
supremum. The proof is the generic type-piece engine — a finite supremum of type pieces is one
`LinearMap.pi` piece, an equivariant map out of a finite product of the types carries the whole
translate span, hence finite-dimensionality — instantiated at `ι := rowIsometryInclAt₀ F w`.

## 1. Measured

```bash
cd lean
python3 spec/check_port.py --force FLTForHuman/AutomorphicForm/Adelic/Cusp/ArchTypeSpan.lean
# ArchTypeSpan.lean  [ok]  1 ok, 0 mismatch, 0 missing, 0 own, 0 kw
python3 spec/check_port.py --all
# 1816 ok, 0 mismatch, 0 missing, 4 own, 0 kw — 45 module(s), 584 exempt (PORT_FILES); corpus aa2d8b3
python3 spec/unwired_register.py --check
# unwired_register: register is current
```

* Tier-1 build **3,838 jobs**, 3.3 s, **0 warnings**. The edit loop is silent.
* `#print axioms AutomorphicForm.CuspidalConstituent.finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt`:
  `[propext, Classical.choice, Quot.sound]`.
* Grep sweep clean; one **narrow** `set_option linter.style.haveILetI false in` on `kspan_main` (the
  two `haveI`s are load-bearing `FiniteDimensional` instances), matching `TypeReproducer.lean`'s two
  sites. No file-wide suppression, no `maxHeartbeats` override.
* `kspan_main`'s body is **byte-identical** to the pin's `R5bE.kspan_main` (a `diff` shows no changed
  line); the transcription changed only the enclosing namespace and added `open Q09`.
* `git status` shows the one new module; no existing file was edited.
* `spec/old_check_stmts.py` is **not run** — `spec/check_port.py` is the checker, and nothing was
  appended to the frozen lists (see §4).

## 2. What this set is a case of: cross-silo reuse, 31 of 39 declarations

`port_advise` + `port_plan` on the pin file:

| quantity | value |
|---|---:|
| raw `S_` lines | 813 |
| declaration lines | 786 |
| **already in the port (vetted)** | **696** — 31 declarations, all tier 3 |
| byte-identical / shape-tier / suspect | **31 / 0 / 0** |
| **net new math lines** | **90** |

The rows are not the port's copies of *this* silo: they are the shared engine
`FLTForHuman/RepTheory/TypeReproducer.lean` (namespace `Q09`), which the archTestFactor landing
homed from a **different** pin `S_` file
(`S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean`,
sections `TypePiece`…`MultiPlace`). The pin writes that engine twice; the port wrote it once and
this leaf imports it. The remaining 90 lines are the pin's 59-line `kspan_main` and the headline.

Two consequences worth recording:

* **No promotion, no registration, no host edit.** The reuse is the one shape in which the
  substituted declarations are already public and already registered, so the landing touched
  nothing outside its own file.
* **A `rfl` bridge across two homings.** The proof's `hcut : (⨆ i, archTypeSubmoduleAt F w (ρs i))
  = ⨆ i, typeSubmodule ι (ρ i)` computes by `rfl` because the port's `archTypeSubmoduleAt` is
  literally `typeSubmodule (rowIsometryInclAt₀ F w) τ.ρ`. The pin relies on the same
  defeq; a future wrapper around `archTypeSubmoduleAt` would break it.

## 3. The definition imports were walked, and none was owed

The pin imports `Def_AutomorphicForm_FactorizableTestFn` (ported) and
`Def_AutomorphicForm_CuspidalSpectrumCarrier` (**unported**, 288 lines — the gate of the deferred
centre-cut slab bound). `fltdata.proof_defs` lists both as modules, so the graph cannot decide the
question; a declaration-level `grep` shows **zero** occurrences of any of the carrier module's 31
declarations and of the factorizable-test-function names in the `S_` file. The leaf is proved
entirely over `IsotypicCuspSpace.lean`'s type-piece API plus `Constituent.lean`'s `rightTranslate`.
So the carrier module is not homed here: it is not on this path (§4(a) in reverse).

## 4. Checker policy this landing applies

`spec/check_port.py` is the checker. The wire is the module's `spec-pin:` header — two lines, the
`Theorems/` wrapper for the statement and the `P2M/Sol/S_` file as the comparable copy. **No
in-source per-declaration marker**: the headline matches its wrapper by exact name and statement
hash, and there is no rename and no tier-2 statement to record, so `spec/decl_markers.tsv` gained
nothing either. `spec/old_check_stmts.py` was not run; its lists are the grandfathered registry.

## 5. Step-6 re-read (`frontier.py --ds …`)

```bash
cd tools/deps
python3 frontier.py --target AutomorphicForm.CuspidalConstituent.finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt --top 0
#   needed [F terminal] 0 nodes / 0 lines;  target hops to F ... target is ported
python3 frontier.py --ds --include-leaves --rank-by silo --top 0
python3 frontier.py --ds --rank-by silo --ready --top 0
```

* `needed` **1,366 → 1,365 nodes**, **507,224 → 506,411** raw `S_` lines — exactly the 813 silo
  lines; `F` 1,000 → 1,001 nodes (600,308 lines).
* The high-impact leaf shelf drops 445 → **444** candidates and its head moves from this row (813)
  to `HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen` (807).
* The ready shelf reads **88** candidates, and the one this landing creates is the successor
  `AutomorphicForm.finiteDimensional_span_translates_of_mem_archCutSubmodule`: its cone falls from
  997 to **184 lines, all its own**, and it appears on `--ready` (`used_by` 6 / 7). That is the next
  cut of this family. `inf_iSup_archTypeSubmoduleAt_le_iSup_inf_of_continuous` (cone 1,182) is
  still blocked on three nodes / 369 lines.

## 6. Residuals

* The other eight consumers are unported and each has its own gate (the work order lists them).
* `Def_AutomorphicForm_CuspidalSpectrumCarrier` remains unported and remains the gate of
  `CuspidalSpectrum.exists_forall_setLIntegral_le_mul_setLIntegral_…_ample` in
  [CARRY-FORWARD.md](../CARRY-FORWARD.md).
* The `Q09` engine now has two pin-silo consumers in the port (archTestFactor, this leaf) and
  remains registered tier 3 in [spec/UNWIRED-PUBLIC.md](../spec/UNWIRED-PUBLIC.md). `port_advise`
  reports it as `[tier 3, registered; pin: …]` at every name; no name was promoted by this set.
