# A correspondence preserves regular differentials — landing record

The D-S cone's next `AlgebraicCurve` leaf:
`AlgebraicCurve.Differential.correspondence_mem_regularDifferentials`, the 829-line
`S_` file
`P2M/Sol/S_AlgebraicCurve_Differential_correspondence_mem_regularDifferentials.lean`
(pinned `aa2d8b3`), landed as **one module, 653 lines, 19 statement-checked
declarations, one headline**. Order:
[topics/algebraicCurve/WORKORDER-DC1-correspondence-regular.md](../topics/algebraicCurve/WORKORDER-DC1-correspondence-regular.md).

The statement: for `φ ψ : F →ₐ[K] F'` integral, `FiniteAlong K ψ`, and `ω ∈
regularDifferentials K F`, the correspondence `correspondence φ ψ ω` — pull back along
`φ`, trace down along `ψ` — is again a regular differential. The proof is the three
blocks the module homes: the **trace-different bound** at a place
(`Place.TraceDifferentBound`: the different ideal's `le_pow` bound and `trace_mem_of_le_ord`),
the **local derivation** read at a place (`Place.LocalDerivation`: uniqueness up to a
unit, nonvanishing at a uniformiser, `span_D_eq_top`), and the two halves of the
correspondence (`pullbackAlong_mem`, `traceAlong_mem`), with `hfg_along` transporting
the transcendence hypothesis.

## 1. Measured

```bash
cd lean
python3 spec/check_port.py --changed
# 225 ok, 0 mismatch, 0 missing, 0 own — 11 module(s), 617 exempt (PORT_FILES); corpus aa2d8b3
timeout 280 python3 spec/old_check_stmts.py | tail -1
# 10473 identical (774 promoted, 83 renamed), 0 mismatched, 0 missing, 42 own (10809 checked)
```

* Tier-1 build **2,740 jobs**, 8.1 s, **0 warnings from the new module**. The build
  replays 11 pre-existing warnings from untouched dependency modules
  (`Genus/Stichtenoth.lean` 8, `Defs/LocalResidue.lean` 3; a control build of either
  alone prints the same) — they are not this set's, and the module's own edit loop is
  silent.
* `#print axioms AlgebraicCurve.Differential.correspondence_mem_regularDifferentials`:
  `[propext, Classical.choice, Quot.sound]`.
* Grep sweep clean; one module-level `set_option linter.style.haveILetI false` (house
  convention, load-bearing at 31 `haveI` sites — `Defs/PushPull`, `WeilExchange/Bifibre`,
  `Defs/PlaceDictionary`, `Genus/Stichtenoth` all carry it). **No**
  `attribute [-instance]`/`[-simp]` narrowing: the wrapper's 5 + 5 prelude is not copied
  and no proof needed it.
* Frozen checker unchanged at **10473**; the frontier reads `needed 0` for the node.

## 2. What this set is a case of

**The first set of the column where the byte tier of `port_advise` fires hard**: seven of
the 26 pin rows are byte-identical to declarations already in the tree, because the AC
column homed this prelude when it ported the fibre dictionary and the Riemann–Roch row —
219 lines imported, 581 net new. Two of the seven are *renamed* copies (`ord_nonneg_of_mem'`
→ `Place.ord_nonneg_of_mem`, `mem_of_ord_nonneg'` → `Place.mem_toValuationSubring_of_ord_nonneg_alt`),
which the byte tier finds by hash.

**One of the seven is a special case of a general theorem**, not a copy:
`Place.exists_restrict_eq` (pin 640) is the `M := F'` instance of
`AlgebraicCurve.Place.exists_restrict_eq` in `WeilExchange/Bifibre.lean:64` (`{K F' M}`,
`[Algebra F' M] [IsScalarTower] [FiniteDimensional] [Algebra.IsSeparable]` — the pin's
section context is the same list). The module calls it at `M := F'` and does not restate
the 25 lines. Recorded because the pin proves it inline, so a "port the file" reading
would have duplicated it.

**Two layering findings.** First, the byte tier pointed `ord_nonneg_of_mem'` at
`Canonical/WeilDifferential.lean`, which imports `Genus/Stichtenoth` and
`RiemannRoch/Assembly` — i.e. it would have put a `Differential/` module *above* the RR
assembly. `Defs/PushPull.lean` carries the same lemma in the wrapper's binder shape, so
the module takes that one (applied at `v`) and the import list stays in
`Defs/` + `Differential/`: the build fell from 2,775 to 2,740 jobs and the 7
`WeilDifferential` warnings left the log. Second, a *pre-existing* duplicate elsewhere:
`WeierstrassCurve/IsogenyEndDatum/DualEndData.lean:1537` carries
`Place.exists_restrict_eq_of_separable` with the pin's 640 statement — a second copy of
what `Bifibre.lean` has in general form. Not this set's to fix (it is the
WeierstrassCurve column's), and not imported here; noted for whoever next touches that
module.

## 3. Deviations

1. `Ideal.le_pow_ramificationIdx` → `Ideal.le_pow_ramificationIdx'` (unprimed alias
   deprecated 2026-07-01), in `differentIdeal_le_pow`.
2. `dif_pos` → `dite_eq_left` in `traceAlong_mem`'s `¬FiniteAlong` branch.
3. The pin's `(mem_center_iff v hR).mpr hmem` became the bare `hmem`: `mem_center_iff` is
   `private` in `Defs/PlacesOverDVR.lean` and is `Iff.rfl` (`center` is literally the
   `comap` of the `codRestrict` that *is* `φ`), so the propositions are definitionally
   equal. No helper, no promotion, zero lines — the §5.3 "re-derive locally if cheap"
   case resolved by reading.
4. **The pin's local `maxHeartbeats` raises are gone.** It raises
   `synthInstance.maxHeartbeats 1600000` and `maxHeartbeats 6400000` around
   `essFiniteType_of_mem`; the port's transcription elaborates under the set's
   200,000 cap. This is the discipline working as intended — the pin's raise is not
   inherited, and the declaration fits.
5. The headline's `-- pin:` marker cites the wrapper's `theorem` line (`:12`), not the
   first-binder line the order's snippet showed.
6. `Differential/TraceDiff.lean` is 36 lines and does *not* reach `Differential/PushPull.lean`;
   the latter is imported explicitly (the order's §4.2 parenthetical was wrong).
