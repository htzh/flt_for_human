# The explicit Hecke coset system at a finite place — landing record

The D-S demand's head leaf `HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen` — the
807-line `S_` file (pinned `aa2d8b3`), `cites 0`, cited by **40** theorems — landed with the
**definition gate it forced**: four modules, **94 statement-checked declarations**, one headline.
Order: [topics/automorphicForm/WORKORDER-HS1-hecke-coset-seam.md](../topics/automorphicForm/WORKORDER-HS1-hecke-coset-seam.md).

The statement: at a finite place `v`, the Hecke double coset of `heckeGen (𝓞 F) F v` splits into
`q_v + 1` right cosets modulo the level group — the upper-triangular `u(σ(c)) · diag(ϖ,1)` for the
`q_v` residue classes, and the Weyl-conjugate `w · diag(ϖ,1) · w` — with `IsHeckeCosetSystem` as
the conclusion.

## 1. Measured

```bash
cd lean
python3 spec/check_port.py --force FLTForHuman/RepTheory/LocalLanglands/IntegralSubgroup.lean    # 10 ok
python3 spec/check_port.py --force FLTForHuman/RepTheory/LocalLanglands/IntegralSubgroupOpen.lean #  4 ok
python3 spec/check_port.py --force FLTForHuman/RepTheory/LocalLanglands/HeckeCosetLocal.lean      # 31 ok
python3 spec/check_port.py --force FLTForHuman/AutomorphicForm/Adelic/HeckeCosetSeam.lean         # 49 ok
python3 spec/check_port.py --all
# 1916 ok, 0 mismatch, 0 missing, 4 own, 0 kw — 51 module(s), 583 exempt (PORT_FILES)
python3 spec/unwired_register.py --check
# unwired_register: register is current
```

* Tier-1 builds: gate 1,795 / 2,164 / 2,247 jobs, leaf 3,625 jobs / 5.9 s. **0 warnings** in all
  four modules (the two deprecations the transcription hit were fixed, not suppressed).
* Axioms on the headline: `[propext, Classical.choice, Quot.sound]`.
* Grep sweep clean. One file-level `set_option linter.style.haveILetI false`, the pin's own
  file-wide option (its instance walls are transcribed literally); no `maxHeartbeats` override.
* `git status`: the four new modules and the records. No existing module edited.

## 2. What this set is a case of

**A leaf whose whole cost is its definition gate.** `port_advise` on the leaf reports *nothing* in
the port and 0 substitutions, so the 807 lines are all new — but 584 of the pin's lines sit in
three `Definitions/` modules the port never homed, and nothing can be *stated* without them
(playbook §4(a)). The gate is therefore the first half of the work: `LocalGL2.integralSubgroup` and
its transpose/openness pair, and the local double-coset layer `diagPi`/`localRepSome`/`localRepInf`
with the covering lemma `exists_rep_of_mem_heckeMulSet`. All 45 declarations are transcribed
verbatim and verified, not promoted.

**The private engine, made public for its twin.** The pin writes the 807-line engine twice — this
leaf and the `_principalLevel` sibling (908 lines, 171 diff lines apart). The port makes the 48
pin-`private` declarations **public** so the sibling imports them instead of re-proving 800 lines;
that is why the leaf's checker surface is 49, not 1. It is the Frobenius-subfield choice
(WORKORDER-SU1) at a larger scale, and it is what makes the sibling a ~170-line order.

**The one real drift: `adicCompletion` is a structure.** mathlib `v4.34.0`'s `adicCompletion` is a
one-field structure wrapping the uniform-space completion, and `ext` now descends through
`toCompletion`, so three proof steps that compared matrix entries in `adicCompletion` now compare
their `.toCompletion` images in the underlying completion. The port adapts (a `change` in `hinj`,
`.toCompletion` in two `show` patterns) rather than restoring the pin's `attribute [-ext]
adicCompletion.ext`. Records the general lesson for the rest of the `AutomorphicForm/Adelic` cone:
a `Matrix.ext` on an `adicCompletion`-valued matrix is now an equality of completions.

## 3. The suspect `def` matches, recorded

`port_advise`'s parser reports five "type-only `def` matches" for the gate: `diagPi` ↔
`AutomorphicForm.gl2Weyl`, `unipotentR` ↔ `unipotentGL2`, `localRepInf` ↔ `gl2Weyl`,
`integralSubgroup` ↔ `rowIsometrySubgroup`, `weylInt` ↔ `gl2Weyl`. They are **wrong** — different
objects whose types normalize alike. Recorded here so a later run of the tool does not read them as
substitutions (the same warning the column note gives for the parser's suspect tier).

## 4. Step-6 re-read (`frontier.py --ds …`)

* `needed` **1,364 → 1,363** nodes, **505,956 → 505,149** raw `S_` lines: exactly the 807 silo
  lines. `F` 1,003 → 1,004.
* The demand's `HeckeIntegralSeam` residue is now **one node of 39 lines**
  (`heckeCosetSum_eq_of_isHeckeCosetSystem`, a co-input of ~178 theorems), plus the sibling silos of
  §5 of the order.
* Ready shelf: **90** candidates; this landing's contribution is
  `AutomorphicForm.SmoothCusp.not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup`
  (229), the first of the 40 consumers to become ready.

## 5. Residuals

* The `_principalLevel` sibling (~170 lines once the engine is imported, 1 citer) and the five
  smaller seam rows (39 + 35 + 72 + 111 + 137) are the family's remaining cuts.
* `exists_isHeckeCosetSystem_localRepSome_heckeGen_of_dvd` (957) is the other large sibling; it is
  the same coset engine with a `v ∣ N` hypothesis instead of `¬ v ∣ N`, so it should reuse the
  public engine too — checked when it is scheduled.
* The gate's `LocalGL2.integralSubgroup` is now the port's home for "the integral subgroup of GL₂
  over a DVR"; the `AutomorphicForm` layer's `finiteAdelicGL2Subgroup`/`levelOne` are the adelic
  counterparts and are not unified (their statements differ; the bridge is
  `mem_generalU_of_components`/`components_of_mem_generalU` in the leaf, which is where the two
  meet).

## 6. Addendum (2026-10-20): the 39-line coset-sum row, appended to the coset-system module

The demand's last `HeckeIntegralSeam` row — `HeckeIntegralSeam.heckeCosetSum_eq_of_isHeckeCosetSystem`,
39 pin lines, `cites 0`, 33 project citers — is the **well-definedness half** of the structure the
port already homes: for a right-`U`-invariant `φ`, the coset sum `∑ i, φ (g * reps i)` is the same
for any two `IsHeckeCosetSystem` families over the double coset. It therefore **fits**
`RepTheory/LocalLanglands/HeckeCosetSystem.lean` (which proves the disjoint-union, injectivity and
canonical-system lemmas) and is appended there rather than given a module of its own.

* **Priced as the hub edit it is**: `build_ladder --edit` → **34 dependent modules / 16,230 lines,
  ≈197 s** (`SmoothRealization` and the new `HeckeCosetSeam` both import it). One wave build, green
  (4,175 jobs).
* **The append is a handoff**: `spec-pin:` lines in (the module's own `Def_` source for its 14
  existing declarations, the coset-sum wrapper for the new one), `PORT_FILES` entry out. Measured:
  the module's checker surface goes 0 → **15 ok**, and the whole surface **1916 → 1931 ok** over
  **52** modules (582 exempt).
* The pin's `P1RepIndep.…_impl` helper and its `solution` alias are one public theorem, the helper
  inlined (`p2m` plumbing).
* One transcription lesson: the pin's binders are `HeckeIntegralSeam.IsHeckeCosetSystem`
  (fully qualified). Written bare inside `namespace HeckeIntegralSeam` the checker reports a
  `MISMATCH` — `norm` erases `ModularCurve.`/`AlgebraicCurve.`/`kw_` prefixes, not this one. Use the
  pin's own text.
* Axioms `[propext, Classical.choice, Quot.sound]`; imports added for `ℂ` and `∑`
  (`Mathlib.Basic.Complex.Basic`, `Mathlib.Algebra.BigOperators.Group.Finset.Basic`).

Step-6: `needed` 1,363 → 1,362 nodes, 505,149 → 505,110 lines (−39 exactly); `F` 1,004 → 1,005.
`frontier.py --ds --list` no longer shows any `HeckeIntegralSeam.` node: **the namespace is out of
the D-S demand**.

## 7. Addendum (2026-10-20): the `_principalLevel` sibling

The near twin (`908` pin lines, 56 declarations, 171 diff lines) is outside the D-S cone but
re-proves the same engine, so it was ported now to bank the dedup:
`AutomorphicForm/Adelic/HeckeCosetSeamPrincipal.lean`, **295 lines, 11 checked declarations** —
**45 of the twin's 56 declarations are imported** from `HeckeCosetSeam.lean` (42 byte-identical; the
two `l1U`-spelled membership lemmas are the parent's `(productionPinsGeneral F).U`-spelled ones,
since `(productionPinsGeneral F).U N = levelOne ⊓ finiteAdelicGL2Subgroup` by definition, so the
`l1U` abbreviation is unnecessary). The 11 restated are the ones whose statements really differ:
`prinU`, the five Weyl-conjugacy lemmas, four `prinU`-flavoured versions, and the headline.

* Homing: the pin's `Aux4SevenTN` namespace is taken by the now-public engine, so the variants live
  in `Aux4SevenTNPrincipal`; the headline is stated at the root (a first draft inside the namespace
  produced the full name `Aux4SevenTNPrincipal.HeckeIntegralSeam.…`, which the checker accepts but a
  consumer would never find).
* Checker **+11**, whole surface **1931 → 1942 ok / 53 modules**; build 3,627 jobs, 4.9 s, no
  warnings; axioms `[propext, Classical.choice, Quot.sound]`.
* Front: the twin reads `needed 0`; `F` 1,005 → 1,006 (the row is outside the D-S closure, so the
  `--ds` `needed` figure is unchanged — this landing is a dedup investment, not a demand cut).

What that leaves of the family, all outside the D-S cone:
`exists_isHeckeCosetSystem_localRepSome_heckeGen_of_dvd` (957 pin lines — the same engine under
`v ∣ N`, which will now be a ~150-line module on the public engine) and the four small rows (35, 72,
111, 137).

## 8. Addendum (2026-10-20): the `of_dvd` sibling — scoped, deferred

`HeckeIntegralSeam.exists_isHeckeCosetSystem_localRepSome_heckeGen_of_dvd` (957 pin lines, 55
declarations) was scoped. **No module drag**: every name the new block uses is inside
`HeckeCosetSeam`'s 105-module closure, and the wrapper's five extra `Definitions/` imports are inert
(0 occurrences in the `S_` file), so there is no definition gate. `port_advise`: 39 substitutions
(589 lines), residual **13 declarations / ≈320 lines** — about 1.4× the `_principalLevel` sibling's.

**Deferred anyway**, because the residual is not a transcription: `exists_localRepSome_inv_mul_mem`
(153 lines, half the residual) carries `set_option maxHeartbeats 3200000 in` in the pin, and its
~40 entrywise matrix steps do not close under `v4.34.0` — the draft's `simp; try ring` steps leave
unsolved goals and two `linear_combination` mismatches. Under the no-heartbeat-raise discipline this
is a diagnose-and-fix task, worth its own order. The draft is parked at
`lean/tmp/HeckeCosetSeamDvd.draft.lean` (git-ignored); the tree stays at **1942 ok / 53 modules**.
