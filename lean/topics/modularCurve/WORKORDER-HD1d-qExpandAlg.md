# WORKORDER-HD1d — C1: one `qExpandAlg`, and `qExpandₐ` as its `ℚ` specialisation

**Status: open (2026-10-22), one dispatch, small.** The C1 row of the dedup survey
([`tools/deps/README.md`](../../../tools/deps/README.md) §"Survey 2026-10-23", class C1; published
summary in [../TOPIC-dedup-refactoring.md](../TOPIC-dedup-refactoring.md) §10). It is the pass HD1c
pointed at as "the natural next micro-order", and it removes the last `own:` exemption in the degree
layer.

## 0. The finding, and the one decision

The port has **one map under two names and two proofs**:

* `ModularCurve.qExpandAlgHomC (K) [Field K] (N) [NeZero N] : LaurentSeries K →ₐ[K] LaurentSeries K`
  in `ModularCurve/Frobenius/Defs.lean:75` — the general one, transcribed from
  `Definitions/Def_ModularCurve_X0ModL.lean:77`;
* `ModularCurve.qExpandₐ (N) [NeZero N] : LaurentSeries ℚ →ₐ[ℚ] LaurentSeries ℚ` in
  `ModularCurve/Defs/Laurent.lean:152` — the same construction at `K = ℚ`, with the *same* proof term
  (`__ := qExpand _ N` + the `commutes'` step).

The pin is no better (four names: `qExpandAlg` in ≥5 `S_` files, `qExpandAlgHomC`, `qExpandAlgC`,
`qExpandₐ`). The port keeps exactly **two**:

* **`qExpandAlg`** — the general definition, at `[CommRing K]` (the proof uses only
  `algebraMap_laurentSeries_eq_single`, `qExpand_single`, `mul_zero`; invertibility is never used),
  homed in **`ModularCurve/Defs/Laurent.lean`** immediately after
  `algebraMap_laurentSeries_eq_single`, i.e. beside `qExpand`, `coeffMap` and `qExpandₐ`;
* **`qExpandₐ`** — kept, because it is a pin-public name with 41 uses and the `ₐ` subscript is the
  standard "algebra version" marker, but redefined as **`qExpandAlg ℚ N`** (its statement/type does
  not change).

`qExpandAlgHomC` and `qExpandAlgHomC_apply` are **deleted**; every use is renamed to
`qExpandAlg` / `qExpandAlg_apply`. No other spelling is introduced.

## 1. Edits

1. **`ModularCurve/Defs/Laurent.lean`**
   * Keep `algebraMap_apply_eq_single` (the `ℚ` one, with its `qExpandₐ` block) in place.
   * After `algebraMap_laurentSeries_eq_single` (:229), add the general
     ```lean
     /-- `qExpand` bundled as a `K`-algebra endomorphism. -/
     noncomputable def qExpandAlg (K : Type*) [CommRing K] (N : ℕ) [NeZero N] :
         LaurentSeries K →ₐ[K] LaurentSeries K where
       __ := qExpand K N
       commutes' c := by
         show qExpand K N (algebraMap K (LaurentSeries K) c) = algebraMap K (LaurentSeries K) c
         rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero]

     @[simp]
     theorem qExpandAlg_apply (f : LaurentSeries K) : qExpandAlg K N f = qExpand K N f := rfl
     ```
     and immediately after it `qExpandₐ`, `qExpandₐ_apply`, `qExpandₐ_comp` moved down from :152–168,
     with `qExpandₐ`'s body replaced by `qExpandAlg ℚ N` (its type unchanged, `_apply` still `rfl`,
     `_comp` unchanged modulo the new defeq).
   * One `spec-pin: Definitions/Def_ModularCurve_X0ModL.lean` line, so `qExpandAlg` is in the wire
     (the pin declaration there is `qExpandAlgHomC`; a `def`'s statement is its type, so the content
     tier matches — do not add a marker unless the checker says otherwise).
2. **`ModularCurve/Frobenius/Defs.lean`** — delete `qExpandAlgHomC` and `qExpandAlgHomC_apply`;
   rename the file's own uses (6) to `qExpandAlg`/`qExpandAlg_apply`; keep its header's dedup
   paragraph but correct the sentence that says `qExpandAlgHomC` is ported here (it now lives in
   `Defs/Laurent.lean`).
3. **`ModularCurve/X0/FunctionFieldFull.lean`** (5 uses), **`ModularCurve/X1/HeckeDegree.lean`**
   (5 uses), **`ModularCurve/XH/HeckeDegree.lean`** (8 uses): mechanical rename. In
   `XH/HeckeDegree.lean` the promoted `laurentBaseChange_map_qExpand` now spells
   `.map (qExpandAlg L ℓ)` — the pin's own text.
4. **`lean/spec/decl_markers.tsv`** — delete the row
   `FLTForHuman/ModularCurve/XH/HeckeDegree.lean  ModularCurve.HeckeDegree.laurentBaseChange_map_qExpand  own: …`;
   after step 3 the declaration diff is exact, so the exemption is no longer needed.
5. **Legacy hand-over (see §3): `ModularCurve/Frobenius/Defs.lean`.**
   Add its `spec-pin:` lines to the header —
   `Definitions/Def_ModularCurve_QExpFrobeniusModL.lean`,
   `Definitions/Def_ModularCurve_FrobeniusModL.lean`,
   `Definitions/Def_ModularCurve_X0ModL.lean` (its header says the three generic lemmas and
   `coeffMap_ofPowerSeries` come from the last two) — and delete its row from `PORT_FILES` in
   `lean/spec/old_check_stmts.py` (that one string line only; `SOURCES` untouched; the file must still
   parse). Then run the checker and add `pin:`/`own:` rows in `lean/spec/decl_markers.tsv` **only** for
   declarations the pin files genuinely spell differently; a same-name statement that differs is a
   bug in the transcription, not a marker.

## 2. Legacy question, answered

**One new legacy module is touched: `ModularCurve/Frobenius/Defs.lean`** — it is in
`PORT_FILES` and carries no `spec-pin:` lines, so it must be handed over in this pass (§1.5).

The rest of the touch set is already standard:

| module | `PORT_FILES` | `spec-pin:` | status |
|---|---|---:|---|
| `ModularCurve/Defs/Laurent.lean` | no (handed over earlier; the registry comment says so) | 13 | wired |
| `ModularCurve/X0/FunctionFieldFull.lean` | no (removed 2026-10-22) | 1 | wired |
| `ModularCurve/X1/HeckeDegree.lean` | no (new) | 4 | wired |
| `ModularCurve/XH/HeckeDegree.lean` | no (new) | 6 | wired |

## 3. Build and verification

* `cd lean && flock .lake/flt_build.lock timeout 110 lake build FLTForHuman.ModularCurve.Defs.Laurent FLTForHuman.ModularCurve.Frobenius.Defs FLTForHuman.ModularCurve.X0.FunctionFieldFull FLTForHuman.ModularCurve.X1.HeckeDegree FLTForHuman.ModularCurve.XH.HeckeDegree` — green, **0 warnings**, no heartbeat bump; `lake env lean` for the edit loop; never a whole-tree build.
* `python3 lean/spec/check_port.py --force` on all five: `Laurent` 13 → **14 ok**, `Frobenius/Defs` its own count (46 public declarations; expect 0 mismatch / 0 missing, with only genuinely-different spellings as `own:`), `X0/FunctionFieldFull` 15, `X1/HeckeDegree` 2, `XH/HeckeDegree` **43 ok, 0 own** (the `own:` row is gone).
* `grep -rn "qExpandAlgHomC" --include=*.lean lean/FLTForHuman` → **0**.
* `python3 tools/deps/dedup.py 'ModularCurve/Defs/Laurent' 'ModularCurve/Frobenius/Defs' 'ModularCurve/X0/FunctionFieldFull' 'ModularCurve/X1/HeckeDegree' 'ModularCurve/XH/HeckeDegree' --tier name --tier shape --tier body` → no cluster naming `qExpandAlg`/`qExpandₐ`, and no new cluster at all.
* `#print axioms` on the three degree-layer headlines unchanged; `grep -c "sorry\|admit"` 0 on the edited files; `frontier.py --ds --ready --nexus --fanin-min 10 --top 3` unchanged head.
* Whole-port reading after the pass: `python3 tools/deps/dedup.py --limit 0 --json tmp/dedup_all.json` — record the new total in **`tools/deps/README.md`** §"Survey 2026-10-23" (the C1 row becomes "closed", and the table's totals are updated), and mirror the one-line status change in `../TOPIC-dedup-refactoring.md` §10.

Stop-early: if `qExpandAlg`'s `commutes'` proof does not close over `[CommRing K]`, **do not** widen to
`[Field K]` silently — report it (the general hypothesis is part of the proposal). If the hand-over of
`Frobenius/Defs.lean` reports more than a handful of `MISMATCH`es, stop and report them: that module's
statements are Definitions-transcriptions and should be exact.
