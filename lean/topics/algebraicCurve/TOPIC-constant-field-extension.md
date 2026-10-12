# TOPIC — the constant-field-extension linear-independence pair

**Status (2026-10-12): scoping record; no work order written.** This is the
planning note for the two pin nodes

```
AlgebraicCurve.linearIndependent_of_constantFieldExtension_of_isAlgClosed
AlgebraicCurve.linearIndependent_of_constantFieldExtension
```

Pinned at `anthropics/fermats-last-theorem` `aa2d8b3`; the port's mathlib is
`v4.34.0`. Measurements are pin lines unless the row says otherwise; every command
used is in §12.

**Subject, in one sentence.** A `K`-linearly independent family in `F` stays
`K'`-linearly independent in `F'`: base change of a linearly independent family
along a constant field extension, for `K` algebraically closed.

**Provenance — why this note exists.** The `of_isAlgClosed` node is the **head of
the Deligne–Serre column's ready shelf** by silo lines: `frontier.py --ready
--rank-by silo` on `DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen`
reports it first at 583, `used_by` 4 (cone) / 9 (project), one hop above `F`.
[PORTING-DeligneSerre.md](../PORTING-DeligneSerre.md) §2 records the row and says
in the same paragraph that the `AlgebraicCurve` rows "are reached by the target
closure but are not `ModularCurve` rows, and are not this column's to cut". This
note takes the subject up where it belongs — the `AlgebraicCurve/IsCurveOver` layer
— and records what the Deligne–Serre column's instruments found, so the column that
cuts it does not have to re-run the scoping.

**Reading order.** §1–§2 are the subject and the pin inventory; §3 the measurements;
§4 what is genuinely new mathematics; §5 the deliverable; **§6 the promotions and
hub edits** (the only edits to existing modules in this cluster — there are none);
§7–§8 route and risks; §9–§10 build and verification.

**Companions.** [PORTING-DeligneSerre.md](../PORTING-DeligneSerre.md) §2–§4 (the
shelf, the workflow, the definition/hub rule);
[PORTING-AC.md](../PORTING-AC.md) (retired — the `AlgebraicCurve` layer's own
blueprint, whose `IsCurveOver/` vocabulary this cluster sits in);
[deligneSerre/TOPIC-definitions-and-homes.md](../deligneSerre/TOPIC-definitions-and-homes.md)
§2–§3 (the factor-out-block and promotion discipline);
[porting-playbook.md](../../porting-playbook.md) §2.1–§2.6, §3.3–§3.5, §4, §5.

## 1. The two nodes, and the third that shares a block

| node | pin `S_` file | pin wrapper | lines |
|---|---|---|---:|
| `…_of_isAlgClosed` | `P2M/Sol/S_AlgebraicCurve_linearIndependent_of_constantFieldExtension_of_isAlgClosed.lean` | `Theorems/Thm_AlgebraicCurve_linearIndependent_of_constantFieldExtension_of_isAlgClosed.lean` | 583 |
| `…` (the characteristic-zero twin) | `P2M/Sol/S_AlgebraicCurve_linearIndependent_of_constantFieldExtension.lean` | `Theorems/Thm_AlgebraicCurve_linearIndependent_of_constantFieldExtension.lean` | 579 |
| `AlgebraicCurve.genus_eq_of_constantFieldExtension_of_isAlgClosed` (shares 4 declarations) | `P2M/Sol/S_AlgebraicCurve_genus_eq_of_constantFieldExtension_of_isAlgClosed.lean` | `Theorems/Thm_AlgebraicCurve_genus_eq_of_constantFieldExtension_of_isAlgClosed.lean` | 539 |

Wrapper statements (the two the checker diffs); they differ only in the extra
`[CharZero K]`:

```lean
theorem AlgebraicCurve.linearIndependent_of_constantFieldExtension_of_isAlgClosed
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    {ι : Type*} {b : ι → F} (hb : LinearIndependent K b) :
    LinearIndependent K' (fun i => algebraMap F F' (b i))

theorem AlgebraicCurve.linearIndependent_of_constantFieldExtension
    … (same binders, plus [CharZero K]) … := …
```

The `of_isAlgClosed` node is the **strict generalisation**: `CharZero K` plus
`IsAlgClosed K` yields a separating transcendental, and the `of_isAlgClosed` proof
obtains one from the already-ported
`AlgebraicCurve.exists_separating_transcendental_of_perfectField`
(`IsCurveOver/PerfectField.lean:170`), where the twin assumes `[CharZero K]` and
derives separability from it. The two files differ by **45 diff lines total** (four
declarations plus import/namespace/`p2m_export` headers).

## 2. The pin's 21 declarations, and where they are shared

The `of_isAlgClosed` `S_` file has **21 declarations, zero `private`** — the whole
file is public surface, which is why `port_advise`'s drags section reports a public
surface of 21 and a same-file closure that adds nothing.

`shared` below is statement identity through the checker's own normaliser
(`check_flt_statements.raw_declarations`), not by eye; see §12 for the scan.

| # | declaration | pin lines | kind | shared with |
|---:|---|---:|---|---|
| 1 | `genericPoly` | 17–18 | `def` | twin |
| 2 | `genericPoly_map` | 20–22 | `theorem` | twin |
| 3 | `genericPoly_monic` | 24–26 | `theorem` | twin |
| 4 | `genericPoly_natDegree` | 28–33 | `theorem` | twin |
| 5 | `genericPoly_coeff_eq` | 35–52 | `theorem` | twin |
| 6 | `exists_factorisation_of_factorisation_map` | 54–135 | `theorem` | twin |
| 7 | `irreducible_map_of_isAlgClosed` | 137–192 | `theorem` | twin |
| 8 | `algebraMap_comp_aeval_gen` | 194–197 | `theorem` | twin |
| 9 | `aeval_gen_injective` | 199–205 | `theorem` | twin |
| 10 | `exists_common_denom` | 207–235 | `theorem` | twin |
| 11 | `exists_primitive_integral` | 237–328 | `theorem` | — (**`[IsSeparable]` here, `[CharZero K]` in the twin**) |
| 12 | `algebraMap_mem_adjoin` | 330–337 | `theorem` | twin **and** genus file |
| 13 | `exists_ringHom_adjoin` | 339–342 | `theorem` | twin **and** genus file |
| 14 | `isIntegral_algebraMap` | 344–351 | `theorem` | twin **and** genus file |
| 15 | `transcendental_algebraMap` | 353–369 | `theorem` | twin **and** genus file |
| 16 | `linearIndependent_pow_algebraMap` | 371–421 | `theorem` | twin |
| 17 | `eq_zero_of_sum_C_mul_map` | 423–439 | `theorem` | twin |
| 18 | `eq_zero_of_sum_aeval` | 440–448 | `theorem` | twin |
| 19 | `eq_zero_of_sum_mul_algebraMap` | 450–511 | `theorem` | — (binder differs) |
| 20 | `linearIndependent_algebraMap_of_fintype` | 513–561 | `theorem` | — (binder differs) |
| 21 | `solution` (the headline) | 563–583 | `theorem` | — (wrapper only) |

**The finding.** **17 of the 21 declarations are statement-identical in the
unported characteristic-zero twin**; the four that are not are exactly the three
whose statements carry `[CharZero K]` instead of `[Algebra.IsSeparable K⟮x⟯ F]`
(#11, #19, #20) and the headline. Four of the 17 (`#12–#15`) are *also*
statement-identical at `S_AlgebraicCurve_genus_eq_of_constantFieldExtension_of_isAlgClosed.lean:344/353/358/368`,
inside that file's `Extension` section. The pin proves the same development twice,
and the port should prove it once.

The two files' namespaces differ (`…AlgebraicCurve.LinDisjSol` in ours,
`…W7XGenusExt` in the genus file), so the pin has no name collision; **the port
will**, if both spellings of #11/#19/#20 are homed in one namespace (§6(c)).

## 3. Measurements

**Frontier** (`§12.1`). `--ready --rank-by silo` on the Deligne–Serre target
reports the shelf at **54 candidates**, headed by this node at silo 583 = own 583,
`used_by` 4 (cone) / 9 (project), hops 1. The conservative `--frontier sources`
reading — the one §9 of the Deligne–Serre note says to plan from where a last-name
pair might hide — gives the same 583, so there is no rename collision here. The
node's own target closure is 4 nodes / 1,201 lines (one node missing: itself, three
ported premises).

**Cone membership** (`§12.2`). In the Deligne–Serre cone (2,308 nodes, 1,673
`needed`), **both** nodes sit in `needed` and neither is ported:

| node | lines | in `needed` | cites | on `--ready` | on `--include-leaves` |
|---|---:|---|---|---|---|
| `…_of_isAlgClosed` | 583 | yes | `exists_separating_transcendental_of_perfectField` (ported) | **yes, rank 1** | — |
| `…` (twin) | 579 | yes | *nothing* (mathlib-only proof) | **no** | yes, `used_by` 16 / 19 |

The twin is a **graph leaf**: it cites no pin node, so `frontier.py`'s `--ready`
view drops it by design (the `i in hops` guard, `frontier.py:740–752`) — 566 leaves
are hidden on this cone at that reading. It is nevertheless *demanded* by 16 cone
nodes, including `AlgebraicCurve.mem_span_range_algebraMap_of_constantFieldExtension`,
`AlgebraicCurve.exists_derivation_constantFieldExtension_map_mem` and
`AlgebraicCurve.Pic0.natCard_torsion_eq_of_constantFieldExtension`. So the shelf
head is one half of a **two-node cluster**, and the second half is invisible to
§3 step 1 of the Deligne–Serre workflow as written.

**`port_advise.py --nodes AlgebraicCurve.linearIndependent_of_constantFieldExtension_of_isAlgClosed`** (`§12.3`),
2 target files / 22 declarations (21 + wrapper):

| section | result |
|---|---|
| 1. substitute | **none — every target declaration is new to the port** (0/22) |
| 2. port once | no name proved in ≥2 target files; no factor row touches the target set |
| 3. generalise | no target name carries two statements; **0 port name clashes** |
| 4. drags | S_: public surface 21, closure adds **0 helpers**; wrapper: 1, 0 |

The import list, hand-checked because `--ready` and `port_advise` never walk
imports (§3 step 3): `Mathlib`, `P2M.Util`, and
`Theorems/Thm_AlgebraicCurve_exists_separating_transcendental_of_perfectField.lean`.
No `Definitions/Def_*.lean` import, so §4(a)'s definition sweep is vacuous; and the
one premise is in the port, statement-identical (`IsCurveOver/PerfectField.lean:170`,
verified through the checker's normaliser).

**`twin_scan.py --node …`** (`§12.4`): `new=1`, `prelude 0/21`, over a port index of
539 modules / 8,893 public statements. The headline has no twin, public *or*
`private`, and no same-last-name relative; none of the file's own declarations is
already public in the port. Nothing to import, nothing to promote.

**`port_plan.py`** (`§12.5`): raw 583 / declaration span 567 / boilerplate 16 /
**21 declaration groups** / 0 already in the port / **net new math 567 lines**.
Its `siblings` section is empty only because the tool sees the single target: the
`X_of_Y` versus `X` pair it exists to report *is* §1's two nodes.

**Mathlib** (read against both the port's `v4.34.0` tree and the pin's own
`.lake/packages/mathlib`). Mathlib has the *converse* of the core
(`Polynomial.Monic.irreducible_of_irreducible_map*`, `RingTheory/Polynomial/IrreducibleRing.lean`),
and it has the assembly API (`FieldTheory.LinearDisjoint`: `linearIndependent_left`,
`linearIndependent_right'`, `of_basis_left`, …). It has no
`irreducible_map_of_isAlgClosed`, no `exists_factorisation_of_factorisation_map`, no
`genericPoly`, and no `IsRegular`-style producer of a `LinearDisjoint` instance from
these hypotheses (the only producers outside its own file are the
purely-inseparable/separable case in `PurelyInseparable/Tower.lean` and the
Galois-coprime-discriminant case over number fields). The `LinearDisjoint` API is
present in **both** mathlibs, so the pin's from-scratch route was a style choice,
not a gap.

## 4. What is new mathematics

* **The core, ~140 lines: `genericPoly` + `exists_factorisation_of_factorisation_map`
  + `irreducible_map_of_isAlgClosed`.** For `K` algebraically closed and a monic
  irreducible `m` in `K[X][X]`, the base change `m.map (mapRingHom (algebraMap K K'))`
  is irreducible. The pin proves it by specialising a *generic* factorisation: any
  factorisation of the base change lifts to one over `K` along a `K`-algebra map
  out of an `MvPolynomial` ring, realised by a maximal ideal and a
  `K`-rational point. This is the only genuinely new mechanism in the file, and it
  is not in mathlib in either direction of the statement. It is the reason the
  row is a real port rather than an import.
* **The tail, ~330 lines of assembly that is new to the port but not new
  mathematics.** `exists_common_denom` (a common denominator over
  `K⟮x⟯`), `exists_primitive_integral` (the primitive element `y` with an integral
  minimal polynomial and a spanning family), `linearIndependent_pow_algebraMap`
  (powers of `y` are a basis after base change, from the minpoly via the core), then
  the linear-algebra reduction `eq_zero_of_sum_mul_algebraMap` and the finite-index
  assembly `linearIndependent_algebraMap_of_fintype`. Structurally this last pair
  is `LinearDisjoint.linearIndependent_left` written out by hand; the port may take
  the mathlib route *if* it can exhibit the disjointness instance, which is the
  pin's own content, so the saving is at most the index bookkeeping of #19/#20, not
  the core.
* **Not new anywhere:** the four `K⟮x⟯`-versus-`K'⟮x'⟯` glue lemmas (#12–#15) and the
  two `aeval`/`AdjoinSimple` adapters (#8, #9) are 5–18-line wrappers around mathlib
  facts; the pin states them public and the port transcribes them public, but they
  carry no mathematics of their own.

## 5. Deliverable

**Home: one new module, no existing module touched.**

```
FLTForHuman/AlgebraicCurve/IsCurveOver/ConstantFieldExtension.lean
```

Its imports are the theory it needs (polynomials, `MvPolynomial`, `RatFunc`,
`IntermediateField`) plus, for the general headline,
`FLTForHuman.AlgebraicCurve.IsCurveOver.PerfectField` (the ported
`exists_separating_transcendental_of_perfectField`). The shared body does not need
`PerfectField` — only that one headline does.

**Declaration plan, public surface.** 25 public declarations, all transcribed from
the pin (21 for the `of_isAlgClosed` node + 4 for the twin):

* §1 of the module — the 17 shared declarations (#1–#10, #12–#18 above), verbatim.
* §2 — `exists_primitive_integral`, `eq_zero_of_sum_mul_algebraMap`,
  `linearIndependent_algebraMap_of_fintype` in their **`[Algebra.IsSeparable K⟮x⟯ F]`**
  spellings (the two files' statements differ only in these three and the headline),
  and the headline
  `AlgebraicCurve.linearIndependent_of_constantFieldExtension_of_isAlgClosed`.
* §3 — the characteristic-zero spellings for node 1919: the three helpers with
  `[CharZero K]`, each a short proof over its §2 counterpart (derive
  `CharZero K⟮x⟯` and `Algebra.IsSeparable K⟮x⟯ F`, then apply), and
  `AlgebraicCurve.linearIndependent_of_constantFieldExtension`, a one-liner over the
  `of_isAlgClosed` headline.

The pin's `solution` is not a declaration to write: it is the package-name
collision (`port_advise` drops it, `NOISE_NAMES`); the headline declaration serves
both the `S_` and the wrapper statement, as `PerfectField.lean` already does for
its node.

**Namespace.** The checker matches by *last name*, so namespaces are free — but
#11, #19 and #20 occur **twice in the pin with different statements**, so their two
port spellings need two namespaces (the same situation as the pin's
`ModularForm.heckeTLin` / `CuspForm.heckeTLin`). Suggested: the `[IsSeparable]`
block and the two headlines under `AlgebraicCurve` (the headlines must keep the
wrapper's last names), the `[CharZero K]` block under a sub-namespace such as
`AlgebraicCurve.ConstantFieldExtension.CharZero` — or the pin's own
`AlgebraicCurve.LinDisjSol` for that block, which is also what its consumers'
`open` lines will expect. This is a naming decision, not a promotion (§6(a)).

**Split, if the genus node lands first.** That node needs only #12–#15 from this
cluster, and it is otherwise a 539-line file of its own; it can import this module
and delete its four local copies. No prelude module is needed.

**What is explicitly *not* this set:** the genus node itself; the 16 cone consumers
of the twin (each is its own node); the `ModularCurve`/`Pic0`/`Place` rows that
consume the family; any `Definitions/Def_*.lean` (there is none in this import
list).

## 6. Promotions and hub edits

**This cluster needs neither a promotion nor a hub edit.** The evidence, spelled
out because the rule is what keeps the wave count at zero:

**(a) No promotion arises — there is nothing to promote.**
The pin `S_` file declares **zero `private` declarations** (all 21 are public), so
there is no pin-private prelude to lift — the case that drove the WeightOne
rectification does not occur here. `twin_scan` reports `twin_private` empty and
`prelude 0/21`: no statement-identical copy exists anywhere in the port, `private`
or public, so there is no port-`private` declaration to promote either. And
`port_advise` §3 finds **0 port name clashes**, so there is no `generalise`
reconciliation. The four declarations shared with the genus file (#12–#15) are
public in *both* pin files: giving them one home is a **placement** decision
(§5), not a visibility promotion, and it changes no statement.

**(b) The one name collision to be aware of, and its non-action.**
`exists_common_denom` (#10) shares a last name with a port `private`
`exists_common_denom` in
`ModularCurve/Degree/Relfinrank.lean:252` — a different statement (a
Laurent-series denominator over `K L t`, not a `K⟮x⟯` denominator) and `private`,
so there is no Lean-level conflict and no substitution. Do not "reconcile" them;
note it here so the next reader does not read the two as one.

**(c) The hub-edit question: none is required, and the alternative is priced.**
The tempting home — appending the shared block to
`FLTForHuman/AlgebraicCurve/IsCurveOver/PerfectField.lean`, the module that already
owns the separating-transcendental node — is an edit to an existing module and
therefore a wave:

| host (edit) | dependent cascade | wave |
|---|---|---|
| `IsCurveOver/PerfectField.lean` | 3 modules / 876 lines (`ModularCurve/Frobenius/QExpModL` 608, `ModularCurve/X1/Structure` 175, `IsCurveOver/Transcendental` 93) | ≈13 s, tier 1 `lake build FLTForHuman.AlgebraicCurve.IsCurveOver.PerfectField` |
| `IsCurveOver/Transcendental.lean` | 2 modules / 783 lines | ≈11 s |
| `AlgebraicCurve/Genus/Stichtenoth.lean` | 56 modules (2,299-line head alone) | do not |

A **new module has no cascade**: it is a leaf, nothing re-elaborates, and the
set's files stay unfrozen. §2 of
[deligneSerre/TOPIC-definitions-and-homes.md](../deligneSerre/TOPIC-definitions-and-homes.md)
is the precedent ("new files touch no existing module, so no cascade"). Appending
to `PerfectField.lean` costs only ~13 s, so the reason to prefer the new module is
not the seconds — it is that a hub edit freezes three more files for the duration
of the set and buys nothing mathematically. If a later node needs the block from
`PerfectField`'s own cone, add the import edge then; it is a one-line, cascade-free
change to the *new* module.

**(d) Adapters we invent stay `private` — and here is the mechanism.** Any helper
this port needs that is *not* a pin declaration (a binder bridge, a
`haveI`-extraction lemma, an unfolding adapter) is kept `private` in the module that
uses it. The checker iterates `PORT_FILES` and looks each **public** port
declaration up in `SOURCES` by last name; one with no pin counterpart is reported
`MISSING IN FLT` and the `0 missing` gate fails
(`spec/check_flt_statements.py`, the `missing` branch of `main`). `private`
declarations are invisible to that pass, which is exactly why they are the right
place for glue. Promote only for **math clarity**: a declaration another theory
will *state* and reuse (playbook §4(b)). The converse also holds and is worth
stating, because it looks like the same rule and is not: the pin's own public
5-line adapters (#8, #9, #2, #3, #4) are **transcribed public**, because they are
pin declarations and the port mirrors the pin's visibility. The `private` rule is
for helpers the port invents, not for thin pin statements.

**(e) Do not create a second copy of the premise.** The pin's file carries
`p2m_export "AlgebraicCurve" "exists_separating_transcendental_of_perfectField"`
and `p2m_open`. In the port that is an `import` of the already-public
`AlgebraicCurve.exists_separating_transcendental_of_perfectField`. Do not restate
it in the new namespace: it would add a redundant public declaration and a second
`identical` to the checker's count for no mathematics. Likewise the twin's
`exists_primitive_integral`/`eq_zero_of_sum_mul_algebraMap`/`linearIndependent_algebraMap_of_fintype`
are **the same last names with different statements** — they are the
characteristic-zero block of §5, not a rename of the `[IsSeparable]` one.

**(f) The checker wiring is part of the edit, and it is the manager's.** Four
appends, both pairs, `SOURCES` first and last (§8 of the Deligne–Serre note):

```
SOURCES      Theorems/Thm_AlgebraicCurve_linearIndependent_of_constantFieldExtension_of_isAlgClosed.lean
SOURCES      Theorems/Thm_AlgebraicCurve_linearIndependent_of_constantFieldExtension.lean
SOURCES      P2M/Sol/S_AlgebraicCurve_linearIndependent_of_constantFieldExtension_of_isAlgClosed.lean
SOURCES      P2M/Sol/S_AlgebraicCurve_linearIndependent_of_constantFieldExtension.lean
PORT_FILES   FLTForHuman/AlgebraicCurve/IsCurveOver/ConstantFieldExtension.lean
```

Both `S_` files are needed, not only the wrappers: the twin's three
differently-bound helpers are public only in its `S_` file, and the lookup that
finds them is the by-last-name map over all of `SOURCES`. Adding entries can only
*add* candidates to that map, so it cannot un-match an existing port declaration.

## 7. Route, alternatives, recorded negatives

**Route.** Transcribe the pin's 21 declarations verbatim, in the pin's dependency
order (the file is already layered: `Generic` → `Spec` → `FunctionField` → `Main`),
then the twin's four spellings as short derivations. Proofs are transcribed with
the port's mathlib spelling; statements are not adapted (§4).

**Alternatives considered.**

* *Import instead of port.* Rejected: `twin_scan` `new`, `port_advise` 0/22
  substitutions — no port declaration, public or private, has any of these
  statements. Nothing to import.
* *Route the tail through `FieldTheory.LinearDisjoint`.* Partially viable and the
  one real saving available: `linearIndependent_algebraMap_of_fintype` and
  `eq_zero_of_sum_mul_algebraMap` restate
  `LinearDisjoint.linearIndependent_left` plus a disjointness proof. But the
  disjointness is what the pin's core establishes, so the core (and the primitive
  element, #11, which feeds it) stays. Do this only if the `LinearDisjoint` spelling
  is *clearer*; it is not required, and the pin's own route keeps the file's
  statements unchanged. Recorded as a negative: **do not** rewrite #19/#20 unless
  the rewrite is shorter *and* the statements still match byte-for-byte.
* *Prove the twin from the general node only.* Adopted for the three helpers and
  the headline (§5 §3), not for the file as a whole: the twin's four declarations
  must still exist as stated, because 16 cone nodes cite them by name.
* *Port the twin as a separate 579-line transcription.* Rejected: 17 of its 21
  declarations would be duplicated lines.

**Recorded negatives.** No `Definitions/` import to port. No `p2m_export`
declaration to re-home. No mathlib theorem yields the headline from `IsAlgClosed`
alone: there is no regularity/disjointness producer to import, and the pin's
`irreducible_map_of_isAlgClosed` has no mathlib counterpart.

## 8. Risks and stop conditions

1. **The hidden half.** The shelf head is one node; the cluster is two. If the
   order is written against the `--ready` list alone, the twin's 579 lines never
   appear and its 16 consumers stall the cone later. Write the order against
   `--include-leaves` too, and record the twin in the order's scope.
2. **Statement drift on the separable swap.** #11/#19/#20 exist twice in the pin
   with `[CharZero K]` versus `[Algebra.IsSeparable K⟮x⟯ F]`. If the port writes
   only one spelling and names it as the other, the checker reports the mismatch —
   the two are *not* interchangeable statements. Stop and re-scope rather than
   "fix" a statement to make the checker green.
3. **The two `exists_common_denom`s.** §6(b). A reader who folds them together
   breaks one of the two consumers.
4. **`MISSING IN FLT` from a well-meant helper.** Any public helper the port
   invents trips the `0 missing` gate (§6(d)). Keep invented glue `private`.
5. **Do not edit `PerfectField.lean` unless the order says so.** It is a hub with
   three dependents (§6(c)); the new module needs only the import edge.

**Deviation protocol.** A declaration that does not transcribe — a mathlib rename
inside a proof, a missing `open`, a statement that will not match — stops the set
and returns to the manager with the declaration, the pin line and the diff. Do not
adapt a statement; do not edit a hub to make a proof compile.

## 9. Build discipline

* edit loop `timeout 300 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>`
  (writes no `.olean`, builds no dependent);
* `flock .lake/flt_build.lock timeout 300 lake build <module>` when a file is done
  (writes the `.olean`, builds dependencies, never dependents);
* **no bare whole-tree `lake build`** while a set is in flight; one at a milestone;
* every `lake build` serialized and bounded; never raise the heartbeat cap.

The module is one file of ~570 transcribed lines plus ~20 lines for the twin's four
spellings; tier 1
(`lake build FLTForHuman.AlgebraicCurve.IsCurveOver.ConstantFieldExtension`) is the
landing build, and it has no dependents of its own to re-elaborate. Every order
carries the **hub prohibition**: a subagent that needs a `private` helper re-derives
it locally and reports it; one that believes a promotion is genuinely required
**stops and reports** with the declaration, host and `build_ladder.py --edit` price.
The manager decides.

## 10. Verification and the expected checker delta

```bash
cd lean
timeout 300 python3 spec/check_flt_statements.py
flock .lake/flt_build.lock timeout 900 lake build
timeout 180 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false spec/DeligneSerreConsumer.lean
```

* **Checker.** The cluster's statements form **25 distinct (kind, statement)
  classes** over the two `S_` files and the two wrappers (measured, §12.6), so the
  expected delta is **+25 `identical`, 0 promoted, 0 renamed, 0 mismatched, 0
  missing** — node `of_isAlgClosed` alone is +21. The `identical` delta must equal
  the new public surface exactly; anything else is a bug (§6 of the Deligne–Serre
  note).
* **Axioms.** `#print axioms` on the two headlines:
  `[propext, Classical.choice, Quot.sound]`.
* **Mutation test.** One token on a headline (e.g. drop an `IsScalarTower`) must
  move exactly one `mismatched`; revert.
* **Sweep.** No `sorry`/`admit`/`axiom`/`native_decide`, no bare `import Mathlib`,
  no heartbeat override, no file-wide `set_option linter.*`.
* **Consumer.** None today: the 16 consumers are unported, so the wire test is the
  checker plus axioms; `spec/DeligneSerreConsumer.lean` is the column's own gate and
  is not touched by this module. Recording this is deliberate — it is the same
  posture as the `locKer`/`adjoinRoot'` residual in the Deligne–Serre topic (§9
  there): public, kept per the pin, with no port consumer yet.
* `git status` showing only the set's files (the module) plus the checker wiring.

## 11. What the landing unblocks

* The Deligne–Serre cone's `needed` set loses two nodes / 1,162 pin lines; the
  shelf head is consumed and its 4 cone consumers
  (`Place.exists_comap_algebraMap_eq_of_constantFieldExtension_of_isAlgClosed`,
  `ell_mapDomain_eq_of_constantFieldExtension_of_isAlgClosed`,
  `exists_regularProlongation_retraction_of_constant_field_valuationSubring`,
  `mem_span_range_algebraMap_of_constantFieldExtension_of_isAlgClosed`) become
  cuttable.
* The twin's 16 consumers become cuttable, including the three named in §3.
* The four shared declarations enter the port once; the genus node
  (`…genus_eq_of_constantFieldExtension_of_isAlgClosed`, 539 lines, unported) imports
  them instead of restating them when its turn comes.
* The step-6 re-read of the Deligne–Serre frontier should show this row replaced by
  its successors; per §3 step 6 of that note, record them in the work order.

## 12. Reproduce

```bash
cd tools/deps

# 1. the shelf the row heads (and the column's whole ready set)
python3 frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen \
  --rank-by silo --ready --top 0
# 2. the hidden leaf — the same cone with graph leaves shown
python3 frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen \
  --rank-by silo --ready --include-leaves --top 0
# 3. the substitution / sharing / drags table
python3 port_advise.py --nodes AlgebraicCurve.linearIndependent_of_constantFieldExtension_of_isAlgClosed \
  --json build/algcurve_linindep_advise.json
# 4. the statement-level twin test (the checker's own normaliser)
python3 twin_scan.py --node AlgebraicCurve.linearIndependent_of_constantFieldExtension_of_isAlgClosed
python3 twin_scan.py --node AlgebraicCurve.linearIndependent_of_constantFieldExtension
# 5. the budget
python3 port_plan.py --json build/algcurve_linindep_advise.json
# 6. the pin-side sharing scan (17/21 in the twin, 4 of those in the genus file)
#    and the cluster's distinct-statement count (the expected checker delta, §10)
python3 - <<'EOF'
import importlib.util, sys
spec = importlib.util.spec_from_file_location("ck", "../../lean/spec/check_flt_statements.py")
ck = importlib.util.module_from_spec(spec); sys.modules["ck"] = ck; spec.loader.exec_module(ck)
PIN = "/home/haitao/proj/fermats-last-theorem/"
A = PIN + "P2M/Sol/S_AlgebraicCurve_linearIndependent_of_constantFieldExtension_of_isAlgClosed.lean"
B = PIN + "P2M/Sol/S_AlgebraicCurve_linearIndependent_of_constantFieldExtension.lean"
C = PIN + "P2M/Sol/S_AlgebraicCurve_genus_eq_of_constantFieldExtension_of_isAlgClosed.lean"
W = [PIN + f"Theorems/Thm_AlgebraicCurve_linearIndependent_of_constantFieldExtension{s}.lean"
     for s in ("_of_isAlgClosed", "")]
def d(p):
    out = {}
    for raw, k, s in ck.raw_declarations(open(p, encoding="utf-8").read(), include_private=True):
        out.setdefault(raw.rsplit(".", 1)[-1], []).append((k, s))
    return out
a, b, c = d(A), d(B), d(C)
for n in a:
    same = lambda x: any(k1 == k2 and s1 == s2 for k1, s1 in a[n] for k2, s2 in x.get(n, []))
    print(f"{n:45} twin={b.get(n) is not None and same(b)}  genus={c.get(n) is not None and same(c)}")

# the port writes one declaration per distinct (kind, statement) over the cluster:
# both S_ files plus both wrappers, with `lemma` folded into `theorem`.
cls = {(k if k != "lemma" else "theorem", s)
       for p in [A, B] + W
       for _, k, s in ck.raw_declarations(open(p, encoding="utf-8").read(), include_private=True)}
print(f"\ndistinct (kind, statement) classes = {len(cls)}")
EOF
```
