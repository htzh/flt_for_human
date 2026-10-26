# WORKORDER-W2b — home the free-product crossed-hom prelude

Status: ready to dispatch. Follow-on to [WORKORDER-W2-parabolic-homs.md](WORKORDER-W2-parabolic-homs.md)
§10 open item 3. **A refactor, not a port**: one new module, one edited module, no new mathematics, no
pin statement may change.

## 1. The problem

`FLTForHuman/ModularCurve/Period/ParabolicHomsDetermination.lean` carries, inline and `private`, the
pin's `P2mKuroshTor` prelude — crossed homomorphisms on a free product, Shapiro's lemma, the transfer,
and the cusp computation — as `namespace FreeProductCrossed`, **lines 672–1416** of that file
(`namespace FreeProductCrossed` at 672, `end FreeProductCrossed` at 1416). It is ~745 lines of general
group theory that has nothing to do with the parabolic-hom statement that consumes it
(`FreeProductCrossed.main` is called by the headline at line 1420), and the pin copies the same prelude
into several `S_` files, so it will be rediscovered by the next wave unless it gets a home now.

## 2. The move

* **Create `FLTForHuman/GroupTheory/FreeProductCrossed.lean`** and move the block **verbatim** (the
  whole `namespace FreeProductCrossed … end FreeProductCrossed`), with its own header, imports, `open`s
  and `set_option autoImplicit false`. Home is `GroupTheory/` because the subject is crossed
  homomorphisms on free products and Shapiro/transfer — the neighbour is
  `GroupTheory/BassSerre/` (`CosetGraph`, `MinimalPeriod`), which the determination module already
  imports.
* **Public API**: the declarations the determination module (and any future consumer) needs must be
  public — at minimum `main` and the crossed-hom/Shapiro layer above it. Keep a declaration `private`
  only if nothing outside the new module uses it; the test is that the determination module elaborates
  with an import and no other change to the prelude's uses.
* **Do not rename the mathematics.** The private names were already rectified in W2 (`Cu`→`Orbit`,
  `wd`→`period`, `genOf`→`generator`, `sumL`→`sumHom`, `tP`→`coprodT`); keep them. No `kw`/`Kw`
  token, no `P2m`, no pin-generated collision token in a *declaration name* (a comment citing the pin's
  `P2mKuroshTor` namespace is fine).
* **In `ParabolicHomsDetermination.lean`**: delete the moved block, add
  `import FLTForHuman.GroupTheory.FreeProductCrossed`, keep the three headlines and everything else
  untouched. The file should end up ~680 lines shorter and unchanged in its statements.

## 3. Do not touch

No other module. In particular do not edit `ModularCurve/Period/ParabolicHoms.lean` (just upgraded:
it now carries `spec-pin:` lines and three promoted helpers) and do not touch the frozen
`spec/old_check_stmts.py` — the `spec-pin:` header is the only wiring.

## 4. Verification

* `lake build FLTForHuman.GroupTheory.FreeProductCrossed` and
  `lake build FLTForHuman.ModularCurve.Period.ParabolicHomsDetermination` — green, 0 warnings, no
  `maxHeartbeats`/`maxRecDepth`, no `sorry`. Every command under 2 minutes; use
  `flock .lake/flt_build.lock timeout 110 lake env lean -DautoImplicit=false <file>` in the edit loop and
  log to `lean/tmp/w2b.log`. No tree build.
* `python3 spec/check_port.py FLTForHuman/ModularCurve/Period/ParabolicHomsDetermination.lean` must stay
  **3 ok / 0 mismatch / 0 missing** — the move must not perturb a statement. Do not wire the new
  `GroupTheory` module unless it contains a *pin node*: report any declaration that has a
  `Theorems/Thm_…` wrapper instead of guessing, and if there is none (expected — it is a re-derivation
  of a pin prelude, not a node), give it a `spec-pin:`-free header that says so.
* `#print axioms` on the three determination headlines unchanged:
  `[propext, Classical.choice, Quot.sound]`.

## 5. Report

New module path and line count, what stayed `private` vs became public and why; the determination
module's new line count; build wall/CPU for both; the checker result; the axioms; a `git status
--porcelain` with only the two files this refactor touches; and anything you could not move as-is
(quoted). If a declaration turns out to be a pin node with a `Theorems/` wrapper, stop and report it —
the manager wires pin nodes, not implementers.
