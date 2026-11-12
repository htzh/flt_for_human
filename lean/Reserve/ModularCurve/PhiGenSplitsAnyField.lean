/-
  GS1 — the prime splitting of `Φ_p` over an **arbitrary** field, with the at-slot
  roots API that reads it off.

  `PhiGen.splits_prime_of_isPrimitiveRoot` is `Φ_p(j(q^p), Y) = ∏_i (Y - conj_i)`
  over any field `K` (`[Field K]`, no `ℚ`-algebra structure), the level-`p` datum
  read at the level-`p` nome `jqModC K` splitting into its `p + 1` conjugates.
  `PhiGen.splits_prime_at_slot_of_isPrimitiveRoot` is the same identity at the
  general level datum `(e, u)`, and the roots API reads the root multiset, its
  distinctness and the `IsRoot` membership form off it.

  The proof is one transport engine. It applies the ported char-0 splitting
  `PhiGen.splits_of_prime` at `CyclotomicField p ℚ`, rewrites that statement's `X`
  slot as `phiAtSeed` and its `jq` as `jqModC`, **pulls the identity back** to the
  integral cyclotomic order `cyclRing ℤ p` along the injective
  `cyclRing ℤ p →+* CyclotomicField p ℚ` (injective because the cyclotomic
  polynomial is the minimal polynomial of the chosen primitive root), and **pushes
  it forward** to `K` along `AdjoinRoot.lift (Int.castRingHom K) (ζ : K)`. The
  at-slot form is the first identity pushed through `(qExpand K e).comp (qTwist u)`
  — the same move the char-0 `PhiGenSplits.splits_prime_at_slot` makes — and the
  second headline is its `e = u = 1` case, exactly as the pin proves it.

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  `P2M/Sol/S_ModularCurve_PhiGen_splits_prime_of_isPrimitiveRoot.lean` (607 lines)
  and `P2M/Sol/S_ModularCurve_PhiGen_splits_prime_at_slot_of_isPrimitiveRoot.lean`
  (607 lines). The two files are **byte-identical except for the 15 lines that
  spell their own name and the final `solution`**: one 607-line development, so
  one module. The declarations transcribed are pin 267–486 (the transport engine),
  426–484 (the two public engine theorems) and 496–589 (the two headlines and the
  roots API).

  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_PhiGen_splits_prime_of_isPrimitiveRoot.lean#L267-L589
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_PhiGen_splits_prime_at_slot_of_isPrimitiveRoot.lean#L267-L589

  The two headlines are the pin's `Theorems/` wrappers verbatim
  (`Theorems/Thm_ModularCurve_PhiGen_splits_prime_of_isPrimitiveRoot.lean:9` and
  `Theorems/Thm_ModularCurve_PhiGen_splits_prime_at_slot_of_isPrimitiveRoot.lean:9`);
  the engine theorems and the roots API are the `S_` file's verbatim.

  ## Twins this module is and is not

  It is the **any-field** twin of `PhiGenSplits.lean` (the splitting) and of
  `PhiSlotRoots.lean` (the roots read off it). It is **not** an instance of either:
  both of those spend an `Algebra ℚ K` and read the slot as `coeffEmb K jq`, which
  an arbitrary field does not have — and the pin's own graph makes
  `splits_of_prime` a *premise* of this module, which is exactly what the
  integrality step uses. The statements therefore differ in their slot
  (`jqModC K` here, `coeffEmb K jq` there) and in the `N`/`p ∣ N` bookkeeping of
  the roots API (there the slot is read at an `N`-th primitive root restricted to
  `ζ ^ (N / p)`; here `ζ` is primitive of order `p` outright).

  ## Names — four renames the pin's two namespaces hide

  The pin states the at-slot roots API **twice** (this file's char-`p` spelling at
  level `p`, and `PhiSlotRoots`' char-0 spelling at general `N`), each inside its
  own per-file namespace `P2MW.S_…`, so both keep the plain names. A single
  `ModularCurve` namespace cannot hold two declarations of one name — Lean refuses
  the *import* of both modules (`environment already contains
  'ModularCurve.isRoot_prime_at_slot_iff'`), which would make any module wanting
  both unbuildable. The char-0 copy was landed first and is what five modules call,
  so this module's four at-slot names take the pin's own disambiguator for the
  any-field variants of this development, `_of_isPrimitiveRoot` (the suffix of the
  two headlines and of the pin's file names):

  | ported name | pin name (same statement) |
  |---|---|
  | `roots_prime_at_slot_of_isPrimitiveRoot` | `roots_prime_at_slot` (518) |
  | `roots_prime_at_slot_nodup_of_isPrimitiveRoot` | `roots_prime_at_slot_nodup` (535) |
  | `roots_prime_at_slot_roots_nodup_of_isPrimitiveRoot` | `roots_prime_at_slot_roots_nodup` (558) |
  | `isRoot_prime_at_slot_iff_of_isPrimitiveRoot` | `isRoot_prime_at_slot_iff` (565) |

  The statements are the pin's verbatim, and the checker still verifies them — by
  content, with one `pin:` row each in [spec/decl_markers.tsv](../../spec/decl_markers.tsv).
  `prod_form_ne_zero` (pin 511) is `private` here, as in the pin: its public
  promoted home is `PhiSlotRoots`' more general copy, and `roots_phiAtSeed_TS` (pin
  584) keeps the pin's name because `PhiSlotRoots` has no such declaration.

  ## Layering

  This is the C-layer's entry to the at-slot roots (`roots_phiAtSeed_TS` has five
  consumers there), so it sits beside `PhiGenSplits`/`PhiSlotRoots` in
  `ModularCurve/`; it imports the definition layer and `PhiGenSplits`, and nothing
  imports it but the C layer.

  ## The prelude is imported, not re-written (pin 33–192, 269–281, 296–317, 355–364)

  The pin repeats its `TS`/`coeffMap`/`phiAtSeed` prelude in every `S_` file that
  needs it; the port gives each declaration one home, and this module imports them
  instead of transcribing them. `Defs/TS.lean` has `TS` and its coefficient API at
  `[Field K]` (including `TS_injective`, which `roots_prime_at_slot_nodup` needs,
  and `qTwist_TS`/`qExpand_TS`/`TS_congr`/`qExpand_qTwist_TS`); `Defs/PhiAtSlot.lean`
  has `phiAtSeed` and its API; `Defs/PhiGen.lean` has `conj`, `conj_zero`,
  `conj_succ`, `phiProd`; `Defs/Cyclotomic.lean` has `cycUnit`, `cycUnit_spec` and
  `isPrimitiveRoot_pow_div` (the pin's `ksplit_exists_isPrimitiveRoot`,
  `ksplitCycUnit`, `ksplitCycUnit_spec`); `Defs/KatzLevelPCusps.lean` has
  `cyclRing`, `cyclZeta`, `cyclRing_root_pow`, `val_cyclZeta` and
  `qTwist_qExpand_of_pow_eq_one` (the pin's `ksplit_root_pow`, `ksplitZeta`);
  `Defs/Laurent.lean` has `coeffEmb_qExpand` (the pin's `ksplit_coeffEmb_qExpand`)
  and `coeffMap_injective`; `Defs/JqCoeff.lean` has `coeffEmb_jq` (the pin's
  `ksplit_coeffEmb_jq`); `Defs/Twist.lean` has `coeffMap_qTwist` and
  `qTwistEquiv`; `X0/FunctionFieldFull.lean` has `coeff_jqModC_of_lt` (pin 44–47);
  `Defs/Cyclotomic.lean` has `units_pow_eq_one_of_isPrimitiveRoot` (pin 189–190).

  Four of the pin's prelude bridges are **not written anywhere in the port yet at
  these statements**, and are not this module's: `jqModC_eq_TS` (pin 105),
  `jqNModC_eq_TS` (108),
  `qExpand_jqNModC` (111) and `qExpand_jqModC_eq_TS` (114). Their consumers are the
  `finrank_adjoin_jqNModC_*` / `jqNModC_*` nodes, which own them; nothing here
  mentions them. `qTwistEquiv_apply` (163) and `coeff_qTwistEquiv` (165) are dead
  in the pin — `coeff_qTwistEquiv` has no consumer anywhere in the pin, and
  `qTwistEquiv`'s only other use is that projection.

  **Dropped, and why.** `roots_nodup_prime_at_slot_of_isPrimitiveRoot`
  (pin 596–598): `private`, a one-line alias of `roots_prime_at_slot_roots_nodup`,
  no consumer in the pin. The prelude above (pin 33–192, 269–281, 296–317,
  355–364), because it is imported. The pin's dead `qTwistEquiv` block
  (pin 151–167), whose one live member `qTwistEquiv` is `Defs/Twist.lean`'s. The
  pin's `ksplit_comp_evalAtJ` (283–290) is **kept** as `comp_evalAtJ`: it is the
  engine's own `evalAtJ` bridge and has no other home.

  ## Assumptions

  `PhiGenSplits.splits_of_prime` (the premise), `Defs/TS`, `Defs/PhiAtSlot`,
  `Defs/PhiGen`, `Defs/Cyclotomic`, `Defs/KatzLevelPCusps`, `Defs/Laurent`,
  `Defs/Twist`, `Defs/JqCoeff`; mathlib's `AdjoinRoot`, the cyclotomic roots API
  (`Polynomial.cyclotomic_eq_minpoly_rat`, `map_cyclotomic_int`,
  `IsPrimitiveRoot.isRoot_cyclotomic`) and `Polynomial.roots_*`.

  spec-pin: P2M/Sol/S_ModularCurve_PhiGen_splits_prime_of_isPrimitiveRoot.lean
  spec-pin: P2M/Sol/S_ModularCurve_PhiGen_splits_prime_at_slot_of_isPrimitiveRoot.lean
-/

-- Body retired: this module's content now lives in
-- `FLTForHuman.ModularCurve.ModularEquation.Split`.
