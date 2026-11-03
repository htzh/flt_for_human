# WORKORDER-AF17 — right convolution as an operator: its adjoint, its derivatives, and what it preserves

**Issued 2026-11-02, one dispatch, three modules, three orders.** Scope: [SET-AF17.md](SET-AF17.md) —
§1 the four rows, §2 the price, §3 the definition gate, §4 the homes, §6 the risk register, and
**Appendix B, the per-declaration worklist**. This order states the work, the manager's landed layer, the
traps and the gates.

**Audience.** A fresh coding session. Wire: each target module carries its own `spec-pin:` header and
`spec/check_port.py` owns its public statements. **No per-declaration markers.** Pin clone
`/home/haitao/proj/fermats-last-theorem`, pinned `aa2d8b3`. Port mathlib `v4.34.0`.

**The size.** 4 rows, 1,434 silo, **1,317 lines in 103 declarations to write** (1,326 net by `port_plan`).
This is a **transcription** set: only 4 of its 1,330 declaration lines are in the port.

## 0. The manager's layer, landed (do not redo it)

1. **The three skeletons exist, build and are wired.**
   `…/Adelic/RightTranslateAdjoint.lean` (order A, 63 lines: two `spec-pin:` lines, seven imports),
   `…/Adelic/RightConvDerivatives.lean` (order B, 71 lines: four wires, ten imports) and
   `…/Adelic/RightConvStructurePreservation.lean` (order C, 65 lines: two wires, eleven imports). Each
   elaborates silent, each builds green (`flock`/`lake build <module>`, 3,864 jobs for the closure), and
   `check_port --force` reads **0 ok / 0 mismatch / 0 missing** on all three.
2. **The statements are verified.** `lean/tmp/probe-af17-statements.lean` states all **four** headlines
   verbatim from their wrappers as `example … := by sorry` and elaborates with **exactly four
   `declaration uses 'sorry'` warnings and nothing else**. Re-run it first. It settled two things, both
   already in the order's material:
   - **row 1's statement needs the adelic Borel space as a local instance**:
     `attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel`
     (the pin registers it at `Definitions/Def_AutomorphicForm_AdelicMaximalCompact.lean:11`; the port's
     own modules do the same, e.g. `DetNormSlabFundamentalDomain.lean:358`). The line is **already in the
     order-A skeleton** — keep it, and keep it out of the statement's text (an `attribute` is not part of
     a signature).
   - the probe needs the **union of the wrappers' opens**: `open NumberField.AdelicBox`,
     `open NumberField.AdelicHaar`, `open AutomorphicForm.SmoothCusp` and `open scoped ComplexConjugate`
     (row 4 spells `adelicBox`, `adelicAddHaar`, `IsHeckeCosetEigenfunctionAt` and `conj`). An `open` does
     not touch a statement's text.
3. **The imports are the mathematics'; one more may be needed and is a report, not a silent addition.**
   Order A's `DetNormSlabFundamentalDomain` is where the port produces
   `IsFundamentalDomain (globalPoints …).range` for a determinant window; order B's
   `FactorizableTestFnArchSmooth{,Complex,Left}` are the three arch-smoothness modules the pin's row-2
   file leans on; order C's `Cusp/SmoothRealization` carries `IsHeckeCosetEigenfunctionAt` and
   `ProductionPinsGeneral` carries `productionPinsOf`.
4. **§2.1's decision: import the one substitution, write everything else.** (At the landing, four more
imports were needed — `AdelicHaar/MulRightInvariant` in A, `ArchDerivRightConvComplex` + `ArchCasimirComplex`
in B, `TestFnTop` in C — each the port home of a lemma the pin's own `S_` file imports; and one
`set_option linter.unusedSectionVars false in` per affected declaration in B was kept as the pin's own
suppression. Both recorded in the brief's §5.1.)
   `continuous_archEntries` (row 2, pin `:121`, 4 lines) is `AutomorphicForm.IsFactorizableTestFn.lift_continuous_archEntries`
   (`FactorizableTestFnArchSmoothLeft.lean`), byte-identical and **public** — import it. There is **no**
   port-once block and no type-only `def` match in this set: the rest is new.
5. **Visibility follows the pin's, and it is the largest checked surface the column has attempted.**
   Row 2 is a flat public surface of **34** declarations and row 3 of **18**; rows 1 and 4 are private
   preludes (36 and 15) with one public headline each. So at the pin's visibility the set has **54**
   public declarations, and at the dropped-`private` reading **103**.
6. **Every headline is public at its pin name — `AutomorphicForm.<name>`** — not inside its helper
   namespace (FR-0135: `check_port` and the frontier both pass a headline under the wrong name, so the
   `#print axioms` step below is the check).
7. **No `Def_` node, no promotion, no migration, no legacy edit**: eleven `Def_` modules in the closure,
   **0 missing** in every one (heaviest `Def_AutomorphicForm_ArchDerivCasimirComplex`, 12/32 used).
8. **No `set_option`** beyond `autoImplicit false`; none of the four statements carries a top-level
   `letI`.

## 1. What you write

Appended below each skeleton's empty namespace. **Order A, then B, then C**; the three modules share no
declaration and no row of one order cites another's.

| order | row (`AutomorphicForm.` dropped) | namespace | work / decls | shape |
|---|---|---|---:|---|
| A | `rightTranslate_adjoint_weightedPairing_of_isLsXiFunction` | `WeightedPairingTranslate` | **397** / 37 | the Ls-Xi and `MemLp` transport of a right translate, the change of variables `x ↦ x y⁻¹` on `Φ₀`, the character factor `|det y|^σ` |
| B | `hasDerivAt_rightConv_mul_unipotentGL2_and_isFactorizableTestFn_leftDeriv_and_linear` | `UnipDeriv` | **360** / 30 | the one-parameter family through `unipotentGL2 (ringEquiv_mixedSpace.symm (t • v), 0)`, its derivative at `0`, the factorizability of the derivative, its linearity |
| B | `archCasimirAtComplex_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAtComplex` | `ComplexCasimirComm` (pin `CommConvC41`) | **288** / 18 | smoothness of `rightConv x f` in the archimedean sense, then the two Casimir commutations |
| C | `isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_of_isFactorizableTestFn_of_support_subset` | `RightConvPreserve` | **272** / 18 | cuspidality, `K_f`-smoothness, level invariance and the Hecke-coset eigen property of `rightConv R.toFun f` |

## 2. Traps

1. **Row 1 is an `MemLp` + Fubini argument.** Two `MemLp` conjuncts and one integral identity with the
   twist `|det x|^-σ` and the factor `|det y|^σ`; the fundamental-domain hypothesis `hFD` is used (the
   change of variables lives on it), and `hΦ₀` (the determinant window) is what gives the growth law.
2. **Row 2's statement is a three-way `∧` and its `t • v` spelling is part of it**:
   `unipotentGL2 (R := AdeleRing (𝓞 K) K) ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (t • v), 0)`,
   and the derivative is `rightConv K φ (fun y => deriv (fun t : ℝ => f (… (-(t • v)), 0) * y)) 0` — note
   the `-(t • v)` in the derivative's family. Copy the wrapper verbatim (FR-0123).
3. **Row 3 has six premises** (continuity and arch-smoothness of `x`, continuity of the first and second
   `archDerivAtComplex` derivatives, factorizability and arch-bi-finiteness of `f`) and its conclusion
   adds the same smoothness for `rightConv x f` plus the two Casimir commutations. `IsArchBiFinite` and
   `ArchTypeFamily` are in `IsotypicCuspSpace.lean`, not in the Casimir module.
4. **Row 4's conclusion is a four-way `∧` whose first conjunct is an `@`-applied `IsCuspidalFn`** with the
   measure and group arguments spelled out (`@IsCuspidalFn _ (adeleBorel …) _ _ (@ProbabilityTheory.cond …)`).
   Copy it exactly; the `hfs` support hypothesis is what makes the eigen property survive.
5. **54 declarations are pin-public**: at the pin reading a mis-transcription in a helper is visible (the
   good case); the dropped-`private` reading adds the other 49. Record both numbers.
6. **`dedup`/`move_dead`**: the pin's own headline-against-`main` structure stays with the reason
   recorded; the `attribute [local instance]` line in order A is load-bearing and stays.
7. **No `sorry`/`admit`/`axiom`/`native_decide`, zero warnings, no `import Mathlib`**, no hub edit, no new
   module.

## 3. Gates

Per module:

1. `timeout 200 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <module>` silent, then its own
   `flock .lake/flt_build.lock timeout 280 lake build FLTForHuman.AutomorphicForm.Adelic.<Module>`; **no
   tree build**, no dependents.
2. `python3 spec/check_port.py --force <module>` → **0 mismatch / 0 missing**, with the ok count measured
   at **both readings** (pin visibility: 1 / 48 / 1 for the three modules = 54 with row 2's 34 and row 3's
   18 public helpers; dropped-`private`: 103 in all). Record, then restore the pin's visibility.
3. `#print axioms` on all four headlines **at their pin-qualified names** → `[propext, Classical.choice,
   Quot.sound]`. A name that does not resolve is a naming defect (FR-0135), not a missing proof.
4. Zero warnings on all three modules.
5. `dedup.py --within` and `move_dead.py --source <path> --target /dev/null --dry-run` per module.
6. `spec/AutomorphicFormSetAF17Consumer.lean` — **one zone per order**, real compositions, no `#check`, no
   `sorry`:
   - **A**: apply the adjointness at a pair of Ls-Xi functions to read the pairing at `y` from the pairing
     at `y⁻¹` with the `|det y|^σ` factor explicit;
   - **B**: compose the unipotent derivative with the Casimir commutation — differentiate
     `archCasimirAtComplex (rightConv x f)` along the unipotent family and compare with
     `archCasimirAtComplex` of the derivative row's value, using the factorizability conjuncts as the side
     conditions;
   - **C**: feed the preservation row's output (`rightConv R.toFun f` cuspidal and `K_f`-smooth) into
     `IsCuspidalFn`'s definitional form and read the level invariance at a `k` in the level subgroup.
   Name whatever imports each zone needs; error count is the deliverable metric.
7. `lean/tmp/probe-af17-statements.lean` still elaborates with exactly four `sorry` warnings.

## 4. Report

Per row: lines written, declarations written and their namespace, every worklist entry dropped and why
(with the pin line), the pin line of every deviation, build time and silence, the checker counts at both
readings, the four `#print axioms` blocks, `dedup`'s clusters and `move_dead`'s dispositions, the consumer
zones' error count, and one paragraph each on order A (was the `MemLp`/Fubini argument the pin's or a
re-proof?) and order C (did the four-way conclusion and the `@IsCuspidalFn` spelling come over cleanly?).

**A blocker goes back immediately** — "blocked on `<decl>` at pin `:NNN`; likely needs `<X>`", with the
pin line and the error. Do not grind out a diagnosis, never work around a hub defect locally, and do not
add an import, a module, or a `set_option` silently (an import you genuinely need is a report).
