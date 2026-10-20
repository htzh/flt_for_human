# WORKORDER-R1 — the characteristic-p / subfield descent of a matrix representation

**Status: landed 2026-10-20** (three modules, 103 checked; record
[logs/descent-charpoly.md](../../logs/descent-charpoly.md)). One pin node, taken whole; the largest
remaining ready leaf in the D-S cone's `Representation` family
(`TOPIC-ds-leaf-families.md` §7.5; `frontier.py --ds --include-leaves --ready` lists it).

## 1. Scope

`Representation.exists_conj_eq_map_of_charpoly_coeff_mem_range_of_finite_of_span_range_eq_top` —
"a matrix representation whose characteristic-polynomial coefficients lie in the image of
`algebraMap K L`, with spanning image, is conjugate over `L` to the base change of a representation
defined over that image" (1,692 pin lines, 105 public declarations). It is the `DeligneSerre`
deformation/descent development, not a small supplement: it is taken whole.

*Not this topic:* the five small `Representation.*` leaves (WORKORDER-R2); the `BrauerNesbitt`
node (`exists_linearEquiv_of_span_range_eq_top_of_trace_eq`), already ported; the deferred
`Def_ModularCurve_EigenformIdeal`.

## 2. Source (pin `aa2d8b3`, `/home/haitao/proj/fermats-last-theorem`)

| file | role |
|---|---|
| `P2M/Sol/S_Representation_exists_conj_eq_map_of_charpoly_coeff_mem_range_of_finite_of_span_range_eq_top.lean` | the proof (1,692 lines); the `solution` headline at line 1682 |
| `Theorems/Thm_Representation_exists_conj_eq_map_of_charpoly_coeff_mem_range_of_finite_of_span_range_eq_top.lean` | the statement authority (root name `Representation.…`) |

The pin file is one development in six pieces (line ranges, `rg -n '^section Piece'`):

| piece | lines | content |
|---|---|---|
| `PieceCS` | 31–137 | `CharpolyRevMap`, `Clause6121`, `Lemma613`: charpoly-rev/coefficient fixing, `CharpolyCoeffsInSubfield`, the Galois twist, `lemma613_of_subfieldDescentInputs` |
| `PieceNS` | 140–316 | `Matrix`, `Engine`, `SeamEngine`, `Carrier`, `BrauerConnection`: `subringPreimage`, `subringDescent*`, `conjRep`, `DescentConjugatorSupply`, `noSchurIndex_*`, `subfieldDescentInputs_of_supply` |
| `PieceDCS` | 319–762 | `Cocycle`, `Poincare`, `Dedekind`, `Span`, `Invertible`, `Hilbert90`, `PGLnAdjust`, `Wire` |
| `PieceSUA` | 765–903 | `SchurUniqueness`, `PGLnCocycle`, `GaloisBookkeeping` |
| `PieceGD` | 906–1136 | `Matrix` (trace/det/chapoly lemmas), `BrauerNesbitt` (the bridge to the ported node) |
| `PieceKF` | 1139–1677 | `ScalarBookkeeping`, `CyclicCocycle`, `NormOneNormalisation`, `FiniteFieldDescent` |

## 3. Advice, re-run to confirm (no Lean runs)

```bash
cd /home/haitao/proj/reasonix-sandbox/flt_for_human
python3 tools/deps/port_advise.py --nodes Representation.exists_conj_eq_map_of_charpoly_coeff_mem_range_of_finite_of_span_range_eq_top --json tmp/r1_advise.json
python3 tools/deps/port_plan.py --json tmp/r1_advise.json --section all
```

Recorded reading: 105 public declarations, 11 private helpers (97 lines), 143 distinct groups;
**~1,644 net new lines**. Substitutions (3 trusted, 1 suspect):

* `Deformation.matrixRepresentation`, `Deformation.matrixRepresentation_apply` — **already public**
  in `FLTForHuman/GaloisRep/Defs/MatrixRepresentation.lean`;
* `trace_eq_of_charpoly_eq` — port-**private** in `FLTForHuman/GaloisRep/RepConj.lean`
  (binder-spelling tier): promote it there, or state the pin's variant in the new module and
  import. The pin also has the sibling-file variant with different binders
  (`S_Representation_exists_conj_eq_of_charpoly_eq_of_finite_range.lean:130`) — take the wrapper's
  binders for the wire (§7.4);
* `DescentConjugatorSupply → PeriodPair.DiscriminantNeZero` is the parser's type-only `def`
  match. **Read, do not apply.**

The one cross-file premise, `BrauerNesbitt.exists_linearEquiv_of_span_range_eq_top_of_trace_eq`,
is ported in `FLTForHuman/RepresentationTheory/BrauerNesbitt.lean` — import it, do not restate.

## 4. Deliverable

Three modules under `FLTForHuman/GaloisRep/Deformation/` (re-cut by piece *group* — not by node —
if one module would exceed ~700 lines; record the re-cut in the module header):

| module | pin pieces | subject |
|---|---|---|
| `Charpoly.lean` | `PieceCS` + `PieceNS` | charpoly coefficients in a subfield, the Galois twist, the descent carrier (`subringDescentHom`, `conjRep`, `DescentConjugatorSupply`) |
| `Cocycle.lean` | `PieceDCS` + `PieceSUA` | the cocycle/Poincaré/Dedekind engine, Hilbert 90, PGLn adjust/wire, Schur uniqueness, Galois bookkeeping |
| `FiniteDescent.lean` | `PieceGD` + `PieceKF` + the headline | the Brauer–Nesbitt/trace bridge, norm-one normalisation, finite-field descent, `lemme613_realizable_of_finite_of_spanTop`, and the wrapper headline |

* keep the pin's `P2MW.S_…` namespace and declaration names **verbatim** (the checker matches by
  name and by statement hash); `p2m_export`/`p2m_open` become `open`/`namespace`/`variable`, never
  a macro;
* the pin's 11 `private` helpers stay `private`; no new public declaration that the pin does not
  have — if one is unavoidable, stop and report (it would need an `own:` row in
  `spec/decl_markers.tsv`, which the manager adds);
* each module carries `spec-pin:` for its S_ file and the wrapper file, and its header states the
  subject, the pin source, and the mathlib-first result for every declaration that has one (§6 of
  the playbook: the "mathlib-first negative" or the substitution used).

## 5. Route and risks

**mathlib first.** Before transcribing any declaration, search mathlib (`rg` in
`.lake/packages/mathlib/Mathlib`) for its statement — the charpoly/det/trace lemmas, Hilbert 90,
Schur, PGLn/`GeneralLinearGroup` bookkeeping, `IsCompl`, `Representation` duals. A mathlib proof
replaces the pin's proof (`exact`, or a three-line `simpa`); the pin's *statement* and name stay.
Record each hit in the module header.

**Stop-early risks, in order:** (i) the `p2m_export`/`p2m_reactivate` macro plumbing — transcribe
it as scopes, not as `open`-of-everything (the pin's exports are the `Matrix`/`BrauerNesbitt`
names); (ii) a `deformation`-flavoured `def` whose type-only match the parser reports as a
substitution (the suspect above); (iii) the `Finite`/`Nonempty n` and `Field L`/`Algebra K L`
binder order drifting from the wrapper (take the wrapper's); (iv) the headline's `solution` name
inside `P2MW.S_…` versus the wrapper's root name — declare both as the zlattice precedent does
(`Analysis/Fourier/PoissonSummationPi.lean` + its `section Euclidean`).
**Deviation protocol:** if a statement cannot be transcribed verbatim, stop and report — do not
weaken, rename or `own:` it.

## 6. Build discipline (copied)

Edit loop `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>`; the cap
is a **diagnostic**, never raised; `lake build <module>` per finished module, bounded and
serialized. **The R2 agent shares this tree: put every `lake env lean` and every `lake build`
under `flock .lake/flt_build.lock` (`flock .lake/flt_build.lock timeout 120 lake env lean …`).**
Never a bare whole-tree `lake build`; no `set_option maxHeartbeats`; 0 warnings.

If a declaration blows the diagnostic, use the probe ladder (`logs/poisson-summation-statements.md`,
playbook §3.5): statement vs proof, then labelled `example` probes at the low cap.

## 7. Verification and report

* `python3 spec/check_port.py FLTForHuman/GaloisRep/Deformation/<module>.lean` per module (and
  `--strict-markers` once): 0 mismatch, 0 missing; `own:` only with the manager's row.
* `lake build <module>` green, 0 warnings; `#print axioms` on the headline and on
  `lemme613_realizable_of_finite_of_spanTop` = `[propext, Classical.choice, Quot.sound]`;
  `grep -c sorry` = 0.
* Report: modules and lines, the wired/checked count per module, the mathlib substitutions used,
  the build wall times, any deviation/blocker, and the checker's exact line.
