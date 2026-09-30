# Work order — R: refactor round (promote the private debts, dedup, unify)

**Status: ready to dispatch.** This is the playbook §3.4/§3.7 **refactor round**: the
one round allowed to reopen frozen modules. Its job is to delete the `private`
copies that let each set avoid editing a closed file, land the missed helper
targets publicly, and make the statement checker cover them. No mathematics
changes — statements stay verbatim.

All of D, H1a, H1b, H2, H3 are accepted; checker baseline **2920 identical / 0
mismatched / 0 missing / 30 own-proof** (2950 checked). Target: green with a higher
checked surface and no new `private` debt.

## 0. The debts, and why they exist

The 14-`S_`-file measurement missed declarations the target proofs reach (this is
now a recorded **method finding**, see §4). Each was resolved locally as `private`
per `PLAN-P1.md` §2, which was correct; this round promotes them.

### R1 — `IsCurveOver.exists_separating_transcendental` (biggest debt)

In `RiemannRoch/Assembly.lean:73–146`: `private kaehlerAdjoinBasis`,
`kaehlerOfSeparatingTranscendentalBasis`, `finrank_kaehler_eq_card_of_separating'`,
`trdeg_le_one`, `trdeg_eq_one_local`, `exists_separating_transcendental_local`.
The pin is public: `P2M/Sol/S_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.lean`
(229 ln), wrapper `Theorems/Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.lean:13`.

- **Home:** new `FLTForHuman/AlgebraicCurve/IsCurveOver/SeparatingTranscendental.lean`,
  declaring the pin's public `IsCurveOver.exists_separating_transcendental` (spell
  it from the wrapper) plus the support lemmas it needs (public, pin names where the
  pin names them). If a support lemma is genuinely pin-`private`, keep it `private`
  there.
- Rewire `Assembly.lean` to import it and **delete** the private block (keep a local
  alias only if a name changes). Update `PORT_FILES` (+ new module) and `SOURCES`
  (+ the wrapper, then the `S_` file).

### R2 — the missed helper targets

Two pin-public helper *targets* were reached by proofs but are in no `rr_homes.txt`
section. Promote both:

1. `exists_indexOfSpecialty_nsmul_single_eq_zero_of_genusReached` — currently
   `private` at `Assembly.lean:468`. Pin `S_AlgebraicCurve_exists_indexOfSpecialty_nsmul_single_eq_zero_of_genusReached.lean:17`,
   wrapper `…:13`. **Home:** extend `AlgebraicCurve/Genus/Index.lean`. Wire the
   wrapper **and** the `S_` file into `SOURCES`.
2. `weilOfKaehler_mem_omegaSpace_of_residueTheorem` (pin `S_AlgebraicCurve_weilOfKaehler_mem_omegaSpace_of_residueTheorem.lean:9`,
   wrapper `…:8`, 18 ln) and `weilOfKaehler_ne_zero_and_maximal` (pin
   `S_AlgebraicCurve_weilOfKaehler_ne_zero_and_maximal.lean:146–196`, wrapper, 199 ln)
   — currently `private` in `Canonical/WeilDifferential.lean`. **Home:** extend
   `AlgebraicCurve/Defs/WeilOfKaehler.lean`. Wire wrappers + `S_` files.

After each promotion, delete the private copy in the consumer and let it import.

### R3 — review the port's own private layer (playbook §2.4)

For **every** `private` declaration in the four new homes below, decide one of:
**promote** (pin-public, no public port copy, consumer-reachable), **dedup-delete**
(the port already has a public copy under another name/path), or **keep private
with a one-line reason** (pin-private, or adapter glue per playbook §5).

- `Genus/Index.lean`, `Genus/Stichtenoth.lean`, `RiemannRoch/Assembly.lean`,
  `Canonical/WeilDifferential.lean`.
- Named candidates from H1b: `instSumRamificationInertiaOfFiniteDimensional`
  (`Stichtenoth.lean:254`, adapter bridging `fiber`/`fiberOver` — `grep -c` its
  consumers first; keep private if only `Stichtenoth` uses it),
  `exists_ofHeightOneSpectrum_or_eq_placeInfty` (`:784`),
  `placeInfty_ne_ofHeightOneSpectrum'` (`:799`), `exists_restrict_eq` (`:928`) —
  check `PrincipalDivisors/RatFuncDegree.lean`, `WeilExchange/{Bifibre,LocalExchange}.lean`
  for public copies and delete if duplicate.
- Named candidate from H2: `stichtenothGenusExists_of_isCurveOver_port`
  (`Assembly.lean:552`) — promote under the pin's public name if the pin has a
  wrapper, else keep private with the reason.
- `main` (`Assembly.lean:590`) stays `private` (proof body of the headline).
- A promotion of a pin-`private` name verifies through the checker's dotted-name
  fallback; add an `OWN_PROOFS` entry **only** if the statement differs or the name
  is shadowed, with the reason.

### R4 — `Pic` placement

`abbrev Pic` was transcribed into `Defs/CanonicalDivisor.lean` (it was absent from
`Defs/Divisor.lean`). Move it beside `Pic0` in `Defs/Divisor.lean` and update
importers, **or** keep it with a recorded reason. It is a general curve object, so
the move is preferred; it is not urgent.

### R5 — `uniformizer` duplication

Set D's `Defs/CanonicalDivisor.lean` keeps `uniformizer` `private`;
`Defs/CanonicalDivisorUniformizer.lean` re-exposes a public copy. Unify: promote
the pin-`private` `uniformizer` once at its pin name in `Defs/CanonicalDivisor.lean`
and delete the re-exposure, or keep the re-exposure and record why. Do not leave
two copies without a reason.

### Not in this round

The checker's missing `class` branch (`DECL_RE` at `spec/check_flt_statements.py:2124`)
is a **separate tooling task**; note it, do not change the checker's kind set here.

## 1. Acceptance criteria

- Checker `0 mismatched / 0 missing`; the identical count **rises** by the number of
  promoted public declarations (the private copies are no longer the only home).
- Each promoted declaration's pin wrapper and `S_` file are in `SOURCES`, with the
  wrapper **first**.
- Every module that lost a private copy still builds and imports its replacement.
- `#print axioms` on the 14 headlines is unchanged
  (`[propext, Classical.choice, Quot.sound]`); no `sorry`/`admit`/`axiom`; no
  `import Mathlib`; no heartbeat override.
- The friction log records every promote/dedup-delete/keep-private decision with
  the reason.

## 2. Build and verification

Edit loop `timeout 120 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>`;
probe in `ScratchR.lean` (do not touch the other `Scratch*.lean`); one
`flock /tmp/flt_for_human.lock timeout 180 lake build` per **wave** of edits (this
round edits several existing modules, so group edits so each module is built once);
then the checker; then `#print axioms` on the 14 headlines. No whole-tree build. No
git commands.

```bash
cd lean
python3 spec/check_flt_statements.py
flock /tmp/flt_for_human.lock timeout 400 lake build FLTForHuman.AlgebraicCurve
```

(the `FLTForHuman.AlgebraicCurve` build is the refactor round's bounded wave — it
re-elaborates the reopened modules and their dependents, which is exactly this
round's cost).

## 3. Report shape

Per debt R1–R5: the decision (promote / dedup-delete / keep), the new home, the
checker move, and the friction entry. Plus the final checker line, the wave build
wall time, and `#print axioms` on the 14 headlines.

## 4. Method finding to record (for `PLAN-P1.md` §1 and the playbook)

The 14-`S_`-file `rr_homes.txt` measurement is accurate for the 14 **headlines** but
a lower bound on the **checked surface**: target proofs reach helper targets outside
the measured file set (three instances: `exists_indexOfSpecialty_nsmul_single_eq_zero_of_genusReached`,
`weilOfKaehler_mem_omegaSpace_of_residueTheorem`, `weilOfKaehler_ne_zero_and_maximal`),
and a curve-level prerequisite (`IsCurveOver.exists_separating_transcendental`) that
the sets did not name. A future measurement should close over the targets'
**proof-reached public wrappers**, not just their own `S_` files.
