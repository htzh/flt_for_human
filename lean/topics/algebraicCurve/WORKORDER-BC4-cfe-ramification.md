# WORKORDER BC4 — orders and ramification at places (two new modules)

Scope: port **five** pin nodes into **two new modules**, split by subject. Do not touch any
other file. Statements come from the `Theorems/` wrappers; proofs from the `S_` files.

## Pin sources (pinned `aa2d8b3`, clone at `~/proj/fermats-last-theorem`)

| node | wrapper (statement authority) | proof | goes in |
|---|---|---|---|
| `Place.exists_forall_ord_eq_finset` | `Theorems/Thm_AlgebraicCurve_Place_exists_forall_ord_eq_finset.lean` | `P2M/Sol/S_…exists_forall_ord_eq_finset.lean` (291) | module A |
| `Place.ramificationIndex_eq_one_of_forall_dvd_ord` | `…/Thm_AlgebraicCurve_Place_ramificationIndex_eq_one_of_forall_dvd_ord.lean` | `…/S_…ramificationIndex_eq_one_of_forall_dvd_ord.lean` (442) | module A |
| `Place.ord_norm_eq_zero_of_forall_fiber` | `…/Thm_AlgebraicCurve_Place_ord_norm_eq_zero_of_forall_fiber.lean` | `…/S_…ord_norm_eq_zero_of_forall_fiber.lean` (13) | module A |
| `Place.ncard_algHom_comp_eq_preimage_eq_ramificationIndexAlong` | `…/Thm_AlgebraicCurve_Place_ncard_algHom_comp_eq_preimage_eq_ramificationIndexAlong.lean` | `…/S_…ncard_algHom_comp_eq_preimage_eq_ramificationIndexAlong.lean` (474) | module B |
| `Place.ord_sum_algebraMap_mul_le_ord_of_linearIndependent_of_constantFieldExtension` | `…/Thm_AlgebraicCurve_Place_ord_sum_algebraMap_mul_le_ord_of_linearIndependent_of_constantFieldExtension.lean` | `…/S_…ord_sum_algebraMap_mul_le_ord_of_linearIndependent_of_constantFieldExtension.lean` (193) | module B |

**Module A — `FLTForHuman/AlgebraicCurve/Place/OrderArithmetic.lean`**: the arithmetic of the
order function at places — prescribing orders at finitely many places (a strong-approximation
argument built from `exists_separating`, `ord_finsetSum_gt`, `ord_add_eq_of_ord_lt`), a Kummer
cover of prime degree being unramified at a place whose order is divisible by the degree, and
the norm of a unit above a place having order zero. Subject: `Place` orders, not the constant
field extension.

**Module B — `FLTForHuman/AlgebraicCurve/Place/ConstantFieldExtensionRamification.lean`**: the
two places-over-a-constant-extension statements — the count of `K`-embeddings `F' →ₐ[K] E` above
a fixed place, computed as a preimage cardinality through `ramificationIndexAlong`, and the
non-cancellation of `K'`-weighted `F`-sums at a lifted place.

## Use the port, do not re-derive (21 importable declarations, ≈249 lines)

- `Place.mem_toValuationSubring_of_ord_nonneg_alt` (`mem_of_ord_nonneg`, 2 pin spellings),
  `Place.ord_nonneg_of_mem_vs` / `Place.ord_nonneg_of_mem`, `Place.ord_add_eq_of_lt`
  (`ord_add_eq_of_ord_lt`, binder spelling), `Place.evalAt_algebraMap_eq`, `Place.evalAt_ne_zero_of_ord_eq_zero`,
  `Place.mem_iff_ord_nonneg`, `Place.exists_restrict_eq` (binder spelling), `Place.isRational_of_isCurveOver`,
  `Place.ord_pos_of_mem_maximalIdeal`, `Place.ord_pos_of_evalAt_eq_zero`, `Place.evalAt_sub_algebraMap`,
  `Place.mem_toValuationSubring_of_ord_nonneg`, `Place.ord_nonneg_of_mem`, `Place.evalAt_algebraMap`,
  plus `essFiniteType_of_fg` / `hasCanonicalDivisor_of_charZero` if needed.
  `port_advise --nodes <the five>` lists them with their pin lines; import them.
- `Place.exists_forall_ord_eq_finset` in the pin file `exists_separating` is **not** the port's
  `exists_separating` — check the statement before importing; if it is the pin's own helper,
  transcribe it (it is public in the pin).

## Traps

1. **Statements are the wrappers'**, in particular the `ValuationSubring E`/embedding count in
   module B's first theorem and the `F⟮α⟯ = ⊤` Kummer shape in module A's second. Copy them
   character for character; universes are `Type*` throughout.
2. `exists_forall_ord_eq_finset`'s conclusion is `∃ g : F, g ≠ 0 ∧ ∀ v ∈ S, v.ord g = n v` — note
   `S : Finset (Place K F)` and `n : Place K F → ℤ`.
3. `ramificationIndex_eq_one_of_forall_dvd_ord` carries `[Fact p.Prime]`, `[CharZero F]`,
   `[FiniteDimensional F L]`, `[Algebra.IsSeparable F L]` in its section; the proof is the
   pin's Kummer argument — do not restate the hypotheses inline.
4. Machine namespaces to rectify: `WC1bSolAW` (module A's order file), `W7XChildL` (module B's
   sum file), `SpecialisationCount` is descriptive and may stay. Put both developments under
   `AlgebraicCurve.Place`, with the headlines at the wrappers' names.
5. `differentialCoeff`-free: nothing here needs the differential layer.

## Build and check discipline

- **Never a tree build.** Edit loop:
  `timeout 110 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` from `lean/`.
  Finished file: `flock .lake/flt_build.lock timeout 110 lake build <module>`.
- Every command under 2 minutes with its own `timeout`; no loops. Logs under `lean/tmp/`.
- Header of each module: `/- … -/` with one `spec-pin:` line per pin file it transcribes (both
  the wrapper and the `S_` file), prose on the mathematics, no cross-references.
  `set_option autoImplicit false`, `noncomputable section`.
- `python3 spec/check_port.py --force <module>` → **0 mismatch, 0 missing** for each module.
- `#print axioms` on all five headlines → `[propext, Classical.choice, Quot.sound]`; 0 warnings;
  no `sorry`/`admit`/`axiom`; no `set_option maxHeartbeats`.

## Report (one message)

per module: build + warnings, the checker summary line; then the axioms lines, the deviations
from the pin beyond a tactic rename, and blockers at first belief. Never weaken a statement,
never edit a hub module, never deliver a `sorry`.
