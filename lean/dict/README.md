# `lean/dict` — notation dictionaries for the port

One file per Lean module, holding that module's **vocabulary**: which objects exist, which ring each
of them lives over, which map goes where, and what the names inside the main proof stand for. The
point is that a reader of a proof should not have to reconstruct the dictionary from the proof.

- **Mirror the module path.** A module `FLTForHuman/<A>/<B>/<C>.lean` has its entry at
  `lean/dict/<A>/<B>/<C>.md` (the library root `FLTForHuman/` is dropped). The entry for
  `FLTForHuman/ModularCurve/ModularPolynomialIrreducible.lean` is therefore
  `ModularCurve/ModularPolynomialIrreducible.md`.
- **A dictionary, not a note.** No proofs, no re-derivation, no plan or history: names, types,
  images, and one-line statements of what each named step says. The mathematics lives in
  [math/](../../math/) and the porting records in [topics/](../topics/); the Lean docstrings
  carry what belongs to a declaration.
- **Written from the code, kept with the code.** An entry is added when a module's notation stops
  being self-explanatory, and is corrected when the module's notation changes — a stale entry is
  worse than none. The module's own header does not point here (a header states the mathematics,
  its source and its assumptions).
- **Published.** These files are tracked, so they are public: cite mathlib and FLT by URL, never by
  a local path.
