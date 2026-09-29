# Deligne–Serre port order — definitions, then home blocks, then theorems

**Status: work order, not started (2026-09-29).** The cascade-aware port order for
the 54-node unconditional slice, and the friction/refactor protocol. It is the
first work order to read; the phase detail is in
[TOPIC-definitions-and-homes.md](TOPIC-definitions-and-homes.md) (phases D and H)
and [TOPIC-theorem-order.md](TOPIC-theorem-order.md) (phase T), and the
mathematics of the targets is in
[TOPIC-weight-one-lifting-and-assembly.md](TOPIC-weight-one-lifting-and-assembly.md).

## 0. The order, and why

**One rule:** a module is ported once, in its subject home, and later work imports
it rather than re-proving it.

**Four phases, strictly in order:**

| phase | what | why it is here |
|---|---|---|
| **D** | the 20 pin `Def_*` modules, in their own import order | they are the importees of everything; nothing can be stated without them |
| **H1** | the shared prelude blocks into **new** subject-home files | new files touch nothing, so no cascade |
| **H2** | the promotions/reconciliations in **existing** files | the only cascade phase; done in one pass, then those files are closed |
| **T** | the 54 theorem modules, level 0 upward | each level imports only levels below it |

The order is an **experiment**: it front-loads definitions and shared blocks so
the theorem phase is mostly new forward imports, instead of transcribing pin files
and re-elaborating large import cascades. The measurement is §3.

## 1. The phase sequence

1. **D1–D4** — definition modules, four import levels (see the definitions work
   order §1). Each level is one dispatch: port, `lake build`, statement-check,
   close.
2. **H1.1–H1.4** — the four new home files: cotangent calculus, `FrobeniusDensity`
   prelude, Galois/representation prelude, Hecke prelude (definitions work order
   §2).
3. **H2.1–H2.3** — promote the 7 port-private copies; reconcile the 22 name
   clashes; extend the two existing homes that must grow (definitions work order
   §3). One full `lake build` at the end, then close those files.
4. **T0–T9** — the ten theorem levels (theorem-order work order). Each level
   imports only closed files.

## 2. Freezing and the friction log

A file that has been ported and reviewed is **closed**. Later work must not edit
it. This is what keeps the order valid: a closed file cannot appear in a later
build's dependency cascade.

When a worker needs something from a closed file that it does not export, or finds
a block that belongs in a shared home, they do **not** reopen the file. They:

- resolve the need **locally** in the file they are working on — a `private` copy,
  or a local restatement of the missing fact;
- append an entry to `lean/logs/deligne-serre-friction.md` (create it on first
  use) with this shape:

  ```text
  ## <date>  <file being written>
  - wanted: <declaration / block>
    home it belongs in: <module>
    currently: <closed file it lives in / not ported>
    local workaround: <private copy name / local restatement, + lines>
    why not resolved here: <closed importee / needs an existing file touched>
  ```

- move on. The entry is the contract for the **refactor round**.

The point is not that promotion never happens; it is that promotion happens in a
dedicated round, not in the middle of a forward port where it would invalidate
already-built files. A deviation never re-opens finished work.

## 3. The refactor round

Run a refactor round **after phase H2 and after each theorem level that the log
touched**, or at latest at the end of the effort. A refactor round:

1. reads the friction log and groups the entries by destination home;
2. promotes the recorded lemmas into their homes (H2-style, one pass);
3. updates the local copies to import the promoted versions (or deletes them);
4. runs a full `lean build` and the statement checker.

The experiment's score is recorded per round: `(local copies added) × (rounds
before promotion)` versus the lines the refactor round moved. If the friction log
stays short, the order is working; if it grows, the home set is wrong and should be
extended before the next phase.

## 4. Verification per step

Every step (definition level, home file, theorem level) closes only when:

- `timeout 120 lake build <module>` is green, with no `sorry`/`admit`;
- the statement checker reports 0 mismatched / 0 missing for the step's files;
- `#print axioms` on the step's headlines is `[propext, Classical.choice,
  Quot.sound]`;
- the friction log has been appended to for anything resolved locally.

Do not start a step whose importees are not closed.
