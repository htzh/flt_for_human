# TOPIC — T19 as one any-field theory

Status: **planned**, written 2026-11-06. Owner: whoever picks up the FFG refactor next.
Companions: `TOPIC-ffg-refactor.md` § *The T19 `C`-layer island is on the shelf* (the record of
the shelving and the do-not-re-port rule), `Reserve/README.md` § *The CL4 island*.

The goal is one proof of T19 — the slot product, its non-membership corollary, and the level-degree
package they run on — parameterized by the base field, with the `ℚ` and the arbitrary-field
statements as instantiations of it. No statement moves. This note is the plan; it records the
evidence for it, the exact shape, the traps, and the order of work.

## 1. Why now

T19 exists twice: `FunctionFieldGeneration/SlotProduct.lean` over a `ℚ`-algebra (1065 lines, the
refactored form) and the `C`-layer twin `SlotProductAnyField` (1355 lines, green on the shelf in
`Reserve/ModularCurve/FunctionFieldGeneration/`, with `MffCMulPrime` and `PrimePowerStepAnyField`
below it and the dead half `Reserve/ModularCurve/Degree/FinrankAdjoinJqNModCDead.lean`).

The twin is not an abandoned route. It is the **prelude of the char-`p` route**, and the pin's own
route to the main theorem:

    package_of_socket → finrank_adjoin_jqNModC_eq_dedekindPsi_of_socket
      → modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charP_pos
      → modularFunctionFieldC_eq_modularFunctionFieldFullC
      → exists_jZeroGoodReductionSpecialization_doorPredicates
      → mazurQuotientSpecialization_heckeModuleBar → mazurStepThree_not_inZeroComponentAt
      → FreyPackage.frey_no_cofixed_large → … → fermat_last_theorem

Pin consumers: `package_of_socket` 2, `…_of_socket` 9, `…_of_charZero` 3
(`tools/deps/explore.py <node>` reproduces this).

**It is in the D-S cone as well.** The closure of
`DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen` (`prune.FltPayoff.closure`, 2308
nodes) contains *every* node the shelved island ports — `minpoly_jqNModC_map_eq_prod_slots`,
`jqNModC_prime_not_mem_fullC`, `jqNModC_mem_modularFunctionFieldC_mul_prime`, `package_of_socket`,
`finrank_adjoin_jqNModC_eq_dedekindPsi_of_socket`, `modularFunctionFieldC_eq_modularFunctionFieldFullC`
and `…_of_charP_pos` — together with the two CL4 support nodes `map_intCast_pow_char_eq_qExpand` and
`qExpand_jqModC_eq_pow_unconditional` (both already ported, in `Defs/QExpandCharP.lean`). The `ℚ` T19
nodes are in the same cone (`minpoly_jqN_map_eq_prod_slots`, `jqN_prime_not_mem_full`,
`finrank_adjoin_jqN_eq_dedekindPsi`). What is *not* in it is the FLT-only tail above the char-`p`
degree facts: `…_of_charZero`, `exists_jZeroGoodReductionSpecialization_doorPredicates`,
`mazurQuotientSpecialization_heckeModuleBar`, `mazurStepThree_not_inZeroComponentAt`.

So a D-S-targeted port meets the same duplication: both statement sets are on its path. That makes
the parameter a D-S requirement, not a convenience of the main route — and it fixes which form each
side needs: D-S wants the **conditional** `…_of_socket` (base non-membership as a hypothesis), the
`…_of_charZero` specialization is FLT-only. In *this* port the route stops at
`_of_socket`: every declaration above it is unported, which is why the island is uncited here and
was shelved. So the port owns the prelude of a route it has not resumed — and the `ℚ` statement of
the same theorem is what `Descent` and `ModularPolynomialLeadingCoeff` cite today. Two statement
sets, one theorem: the duplication has to be removed by a parameter, not by picking a winner.

## 2. What is actually duplicated

Measured with `tools/deps` (`shapes.py`, `dedup.py`):

* 23 declarations occur under the same name in both modules; their *statements* differ only in the
  base field (`minpoly ℚ⟮jq⟯ (jqN M)` against `minpoly K⟮jqModC K⟯ (jqNModC K M)`, and the `hall`
  conjunction over the corresponding field).
* Only `sv_eq_TS`, `TS_congr'`, `sv_inj` are shape-identical across the two *pin* layers; in the
  port `sv_inj_slot`, `nodup_slotValues_sv` and `nodup_slotValues_qExpand` join them. `dedup.py`
  reports 6 name clusters / 89 removable lines — and misses everything else, because the
  difference sits inside the hypothesis *types*, not in instance arguments.
* The induction body (`rval_aux`, the `isRoot_map_minpoly_sv*` family, `phiAtSeed_slot_factor`,
  `qExpand_qTwist_slot_eq_sv`, `sv_ne_image_of_dvd`, `finrank_adjoin_mul_dedekindPsi`) is the same
  proof twice.

Conclusion: parameterize, do not re-derive. `dedup.py`'s 89 lines are the visible tip; the point of
this note is the other ~1200.

## 3. The master statement

The `ℚ` proof shape survives verbatim; four objects are abstracted — the base field, the
q-expansion ring it sits in, the working field, and the coefficient map:

```lean
variable {F A L : Type*} [Field F] [Field A] [Field L] [Algebra F A]
variable (ε : A →+* L)                     -- the coefficient map into the working field
variable (jg : F)                          -- the generator: the j-series, as an element of F
variable (J : ℕ → A)                       -- the level series: J M = qExpand A M (algebraMap F A jg)

def SlotProductAt (M : ℕ) [NeZero M] (ζ : Lˣ) : Prop :=
  IsPrimitiveRoot (ζ : L) M → PkgAt F M →
  (minpoly F (J M)).map ((ε.comp (qExpand A M)).comp (algebraMap F A))
    = ∏ a ∈ M.divisors, ∏ b ∈ (range (M / a)).filter (gcd (gcd a b) (M / a) = 1),
        (X - C (svA ε jg ζ a b))
```

with

```lean
svA ε jg ζ a b = ε (qExpand A (a * a) (qTwist (ζ ^ (b * a)) (algebraMap F A jg)))
```

and the master's hypotheses (all supplied per instance, none of them new mathematics):

1. `Function.Injective ε`;
2. `ε (algebraMap F A jg) = jqModC L` — the generator is carried to the working field's j-series;
3. `∀ N x, ε (qExpand A N x) = qExpand L N (ε x)` — the coefficient map commutes with level
   raising (`coeffEmb_qExpand` in one instance, `rfl` in the other);
4. `PkgAt F M` — the level-degree package at `F` (§4).

The conclusion is exactly today's `minpoly_jqN_map_eq_prod_slots` statement with the four objects
replaced, so the `ℚ` instance is definitional (§5).

## 4. `Pkg` — vocabulary, and why it must be generalized

The package `∀ d ∣ M, finrank at d = ψ(d) ∧ field generation at d` is written three times today:

| today | site | after |
|---|---|---|
| inline conjunction inside `SlotProductAt` | `SlotProduct.lean:308–320` | `PkgAt F M` |
| `abbrev Hall N := ∀ d ∣ N, Tight d ∧ Gen d` | `Defs/Fields.lean:237` | `Hall N := PkgAt ℚ⟮jq⟯ N` (or `Hall_iff`) |
| `hallM : Hall M` / `h : Hall N` | `Nonmembership.lean:367`, `:459`, `DegreeStep.lean:522`, `Capstone.lean:55`, `:92`, `:112` | `PkgAt F M` |

`Tight`/`Gen` (`Defs/Fields.lean:228`, `:233`) survive as the names of the two conjuncts' **proofs**
at `ℚ`; `Capstone.hall_all` still proves the package at `ℚ` and its corollaries
(`finrank_adjoin_jqN_eq_dedekindPsi`, `modularFunctionField_eq_full`) keep their consumers
(`Descent`, `ModularPolynomialLeadingCoeff`).

`Pkg` as it stands (`Defs/JqCoeff.lean:253`) hardcodes `adjoin K {jqModC K}`, i.e. the package at
the **big** field. Generalize it to a field-relative `PkgAt`:

```lean
abbrev PkgAt (F) (M : ℕ) : Prop :=
  ∀ d, d ∣ M → ∀ [NeZero d],
    Module.finrank F (adjoin F {J d}) = dedekindPsi d
    ∧ adjoin F {J d} = adjoin F {J d' | d' ∣ d}
```

and both spellings become definitional or two-rewrite instances:

* `Pkg K M` = `PkgAt (K⟮jqModC K⟯) M` — `rfl` (`modularFunctionFieldC K d` *is* `adjoin K {jqModC K, jqNModC K d}`);
* `Hall N` = `PkgAt (ℚ⟮jq⟯) N` — the finrank clause is `rfl`; the field clause is `adjoin_adjoin`
  twice (`modularFunctionField d = adjoin ℚ⟮jq⟯ {jqN d}`, and `modularFunctionFieldFull d =
  adjoin ℚ⟮jq⟯ {jqN d' | d' ∣ d}`).

**Trap — do not state the master's hypothesis as `Pkg K M`.** `Pkg K M` is the package at
`K⟨j(q)⟩`; the `ℚ` consumer has the package at `ℚ⟨j(q)⟩` and applying the headline at
`K = ℚ(ζ_N)` (`ModularPolynomialLeadingCoeff.lean:188`) would have to *prove* the degree clause over
`K`, i.e. geometric irreducibility of the modular equation, which is not in the tree and is not
wanted. The master's `F` must be the field the consumer actually has.

## 5. The two instantiations

Both are literal — no transport lemma on either side.

| | `F` | `A` | `L` | `ε` | `jg` / `J M` |
|---|---|---|---|---|---|
| `ℚ` (today's statements) | `ℚ⟮jq⟯` | `LaurentSeries ℚ` | `LaurentSeries K` | `coeffEmb K` | `jGen` / `jqN M` |
| any field (the shelved statements) | `K⟮jqModC K⟯` | `LaurentSeries K` | `LaurentSeries K` | `RingHom.id` | `jGenC` / `jqNModC K M` |

The `ℚ` side then keeps, byte for byte, the statements the rest of the port cites:

* `sv`, `sv_eq_TS`, `TS_congr'`, `sv_inj`, `sv_inj_slot`, `sv_top`, `sv_eq`
* `SlotProductAt`, `rval_aux`
* `minpoly_jqN_map_eq_prod_slots`, `mem_adjoin_jqN_of_mem_mff`
* `Nonmembership`'s `jqN_prime_not_mem_adjoin`, `jqN_prime_not_mem_full`, `jqN_prime_not_mem_base`
  (with `Hall M` → `PkgAt` at the same `F`)

`Descent.lean:331` and `ModularPolynomialLeadingCoeff.lean:188` keep their call sites. The `ℚ`
module shrinks to the instance plus the ε-glue; the master owns the induction.

The shelved side is **not** moved back. When the char-`p` route resumes, the two `C` headlines
(`minpoly_jqNModC_map_eq_prod_slots`, `jqNModC_prime_not_mem_fullC`) are replaced by the second
instantiation, and `PrimePowerStepAnyField`/`MffCMulPrime` come back warm because the chain above
needs them.

## 6. Order of work

Each step is green on its own; none needs a tree build.

1. **`PkgAt` and the two instances.** `Defs/JqCoeff.lean` (define `PkgAt`, redefine `Pkg`),
   `Defs/Fields.lean` (`Hall := PkgAt …`, keep `Tight`/`Gen`), then the ~10 hypothesis sites in
   `SlotProduct.lean`, `Nonmembership.lean`, `DegreeStep.lean`, `Capstone.lean`. No proof changes:
   the new form is definitionally the old one at the two fields. Verify: the same modules' build is
   silent and `python3 spec/check_port.py --force` on each keeps its verdicts.
2. **The ε-glue.** Generalize `coeffEmb_jq`, `coeffEmb_qExpand`, `iota_jqN`, `jqN`-of-level facts
   to the master's `(A, L, ε)` hypotheses; introduce `svA`. ~100 lines, all of it existing lemmas
   with the map abstracted. Verify by using the glue to restate one existing `ℚ` lemma.
3. **Parameterize the body** in a new master module (keep `SlotProduct.lean` as the instance, or
   move the body out and leave the instance there — see §9). The long pole: ~700 lines, mechanical,
   with the traps in §7.
4. **Instances and consumers.** Re-point `SlotProduct.lean`'s proofs to the instance, keep the
   statements, rebuild the `ℚ` cone (`Descent`, `Nonmembership`, `DegreeStep`, `Capstone`,
   `ModularPolynomialLeadingCoeff`, `ModularPolynomialFibreTwo`, the `X1`/`XH`/`Hecke`/`Weierstrass`
   dependents — 35 modules by `tools/deps/port_graph.py --dependents`). Then `dedup.py` and
   `move_dead.py` over the touched modules.

Expected end state: one induction, two ~150-line instance/transport modules, one `sv` block, one
`PkgAt`, `Hall`/`Pkg` as one-line definitions — and the `Reserve` island retired by instantiation
rather than by deletion.

## 7. Traps

* **The `Pkg K M` trap** (§4): the master's `F` must be the consumer's field, not the working
  field. This is the one design error that would force geometric irreducibility into the tree.
* **`Algebra F A` from an injection.** In the `ℚ` instance `algebraMap F A` is the *inclusion* of
  `ℚ⟮jq⟯` into `LaurentSeries ℚ`, while `ε ∘ algebraMap` is what composes with `coeffEmb`; write
  the master against `[Algebra F A]` and `ε`, not against a `Subfield` of `A`, so that the `ℚ`
  instance's `minpoly F (J M)` is literally today's `minpoly ℚ⟮jq⟯ (jqN M)`.
* **`F` is not an `IntermediateField K (LaurentSeries K)` in the `ℚ` instance** (it contains only
  `ℚ`'s constants). The `(F, A, L, ε)` form sidesteps the `Subfield`-vs-`IntermediateField`
  mismatch; do not "simplify" it back to a subfield of `L`.
* **The four measured traps from the last pass over these proofs**: `rw` does not see through an
  `abbrev` in the *goal* (`unfold` it, as `tight_one` does); `qExpand A (N * x)` cannot be
  re-associated because the `NeZero` argument breaks the motive (a level parameter must travel
  with it); `rw` cannot match through a `set` local; a universe bound in a *statement* is not the
  section's (keep the `∀ {K}` shape where it is).
* **Statement drift is the failure mode.** `check_port.py` hashes the printed statement: any
  `ok` → `own`/`mismatch` flip on `SlotProduct`/`Nonmembership` means the instance is not
  definitional any more. That is the regression test, not the build.
* **`Reserve` must stay import-free from `FLTForHuman`**, so the second instantiation cannot be
  imported from the shelf; it is written fresh from the master when the route resumes.

## 8. What stays per-layer (this is not duplication)

* The **degree theorems**: `Tight`/`Gen` at `ℚ` (`Capstone.hall_all`) versus `Pkg` at `K`
  (`PrimePowerStepAnyField`, the socket). Different theorems, one shape — the master takes the
  shape as a hypothesis.
* The **modular-polynomial link**: `data.Φ`, `toAdjoin_eq_minpoly_all`, the leading-coefficient
  census (`ModularPolynomialLeadingCoeff`) are `ℚ`-side objects with no any-field counterpart.
* The **`SlotValues` API** (`slotValues`, `card_slotValues`, `prod_slotValues`, `nodup_slotValues`),
  already shared and generic; untouched.

## 9. Open decisions

1. **Where the master lives.** Either `SlotProduct.lean` itself becomes the master with the `ℚ`
   instance in a new thin `SlotProductRat.lean`, or a new `SlotProductBase.lean` holds the body and
   `SlotProduct.lean` keeps its public statements as the instance. The second keeps the public
   module's diff small; the first keeps one file.
2. **Whether `Hall` survives.** `Hall N` as a one-line `abbrev` preserves the public vocabulary of
   `Nonmembership`/`DegreeStep`/`Capstone` at zero cost; deleting it in favour of `PkgAt` at the
   `ℚ` instance is cleaner but renames a hypothesis used across the cone. Recommendation: keep the
   `abbrev`.

## 10. Verification protocol

* Per module, never a tree build: `lake build <module>` (each must be silent: no `info:`, no
  `warning:` in that module's output).
* Statements: `python3 spec/check_port.py --force <module>` for `SlotProduct`,
  `Nonmembership`, and every FFG module touched; the `ok`/`own` rows must be **identical** to the
  pre-refactor run.
* Duplicates: `tools/deps/dedup.py` over the touched modules before and after — the six name
  clusters must disappear into one declaration each; the induction must show up as a single body.
* Dead code: `tools/deps/move_dead.py --select dead --dry-run` per touched module.
* The shelved island is out of scope except that `Reserve` keeps building and
  `Reserve.ModularCurve.FunctionFieldGeneration.SlotProductAnyField` keeps its `spec-pin` verdict.
