# WORKORDER-JQ1 — the prime non-adjoin twin, and the cyclotomic conjugates it shares

Status: **open**, dispatched 2026-10-25. Owner: the set's agent, reviewed by the manager.

The nodes:

| node | pin `S_` | pin lines | declares | frontier |
|---|---|---:|---|---|
| `ModularCurve.jqNModC_prime_not_mem_adjoin_of_charZero` | `S_ModularCurve_jqNModC_prime_not_mem_adjoin_of_charZero.lean` | 593 | 58 | needed 2 (itself + `order_jqModC`) |
| `ModularCurve.jqNModC_prime_not_mem_adjoin_of_forall_aeval_ne` | `…_of_forall_aeval_ne.lean` | 593 | 58 | needed 2 (itself + `order_jqModC`) |
| `ModularCurve.order_jqModC` | `S_ModularCurve_order_jqModC.lean` | 91 | 7 | a premise of both |

`order_jqModC` is a premise, not a headline of its own set: it is priced here so the twin's
demand closes at **2 nodes / 684 lines** instead of leaving a 91-line gate behind. Landing all
three takes the twin rows from `needed 2` to `needed 0`, "target is ported".

## 1. What the mathematics is

`j(q) = q⁻¹·u` with `u ∈ K[[q]]`, `u(0) = 1` (the ground, landed 2026-10-25 in
`Defs/JqCoeff.lean` § *The pole at the cusp*: `jqModC_pow`, `coeff_jqModC_pow_self`,
`coeff_jqModC_pow_of_lt`, `coeff_jqModC_neg_one`). From it, in order:

1. `j` is transcendental over `K` (`Degree/PhiDegree.lean`'s `transcendental_jqModC`, public);
2. `j(qᵖ)` is integral over `K[j(q)]` through the monic modular relation `Φ_p(j(q), Y) = 0`
   (`phiAtSeed_monic`, public in `Defs/PhiAtSlot.lean`);
3. `K[j(q)]` is a polynomial ring (`Transcendental.uniqueFactorizationMonoid_adjoin`), hence
   integrally closed, so a rational function that is integral **is** a polynomial — this is
   `jqNModC_not_mem_adjoin_of_forall_aeval_ne`, the engine: not a polynomial ⟹ not in `K(j(q))`;
4. `j(qᵖ) ≠ P(j(q))` for every `P` follows from the `q⁻ᵖ`-coefficient of `j(qᵖ)` being `1`
   while every `P(j(q))` has a different leading coefficient (`aeval_jqModC_ne_jqNModC`);
5. the characteristic-zero statement is step 4 with `p ≠ 0` in `K`.

So the twin is **one development written twice**: the two pin files are 593 lines each, **574
byte-identical**, and the 19 differing line pairs are 17 namespace renames plus the two lines of
the final `solution` theorem. In the pin's own text `charZero` *derives from* `forall_aeval_ne`
through two `private` wrappers (`_of_coeff_ne_zero` → the engine at `S_:512`). Port it once.

## 2. Module plan

Four parts, in this order. **Do not merge them**: the conjugates module is what `ModularPolynomialStarBank`
also needs, and the two façades must import it rather than re-derive it.

### P1 — `order_jqModC` appended to `ModularCurve/Defs/JqCoeff.lean`

Append `ModularCurve.order_jqModC` to the existing § *The pole at the cusp* section, after
`coeff_jqModC_neg_one`:

```lean
theorem order_jqModC (K : Type*) [CommRing K] [Nontrivial K] : (jqModC K).order = -1
```

The pin's statement is in `Theorems/Thm_ModularCurve_order_jqModC.lean`; the proof is
`S_ModularCurve_order_jqModC.lean` lines 70–85. It needs `coeff_jqModC_neg_one`,
`coeff_jqModC_pow_of_lt` (at `b = 1`, `m = order`), `HahnSeries.order_le_of_coeff_ne_zero`,
`HahnSeries.coeff_order_eq_zero` and `jqModC_ne_zero` (the last is a 3-line `private` helper in
the pin's block — write it locally `private`). Add

    spec-pin: Theorems/Thm_ModularCurve_order_jqModC.lean
    spec-pin: P2M/Sol/S_ModularCurve_order_jqModC.lean

to the module header. The home reads 17 ok today; it must read **18 ok**, 0 mismatch.

### P2 — `ModularCurve/Degree/JqCyclotomicConjugates.lean` (new, wired)

The cyclotomic conjugates of the `j`-series — the block the twin and the star-action node share.
Public declarations at the pin's
names and binders, in one namespace `ModularCurve` (no chapter tokens, no `W1`/`CharLRows`):

| declaration | pin span | note |
|---|---:|---|
| `coeff_algebraMap_mul` | 4 | constants multiply coefficientwise |
| `coeff_aeval_jqModC_of_lt` | 7 | `aeval` has no coefficients below `-natDegree` |
| `coeff_aeval_jqModC_neg_natDegree` | 18 | its leading coefficient is the polynomial's |
| `coeff_jqNModC_self` | 6 | `(jqNModC K p).coeff (-p) = 1` |
| `coeff_jqNModC_of_lt` | 6 | no coefficient below `q⁻ᵖ` |
| `ne_zero_of_aeval_eq` | 7 | |
| `natDegree_eq_of_aeval_eq` | 11 | the Vieta/degree step |
| `monic_of_aeval_eq` | 13 | |
| `jqNModC_congr` | 5 | |
| `units_pow_eq_one_of_isPrimitiveRoot` | 12 | |
| `qTwist_algebraMap` | 4 | |
| `qTwist_comp_algebraMap` | 6 | |
| `aeval_qTwist_jqModC_eq_of_aeval_eq` | 18 | the `p` conjugate roots |
| `qTwist_pow_jqModC_injective` | 10 | the `p` twists are distinct |
| `phiAtSeed_jqNModC_eval` | 7 | the `jqModC` analogue of `phiAtSeed_jq_eval` |
| `phiAtSeed_jqNModC_eval_symm` | 8 | |
| `phiAtSeed_TS_eval` | 6 | |
| `phiAtSeed_TS_eval_symm` | 17 | |
| `coeffMap_algebraMap'` | 4 | `private` in the pin; keep `private` here (no consumer) |
| `coeffMap_aeval_jqModC` | 9 | |
| `sum_qTwist_jqModC_eq_of_aeval_eq` | 54 | the conjugate sum: `Σ_b twist^b = 0` |
| `coeff_sum_qTwist_jqModC` | 12 | its `q^(-pm)` coefficient, `-w` |
| `aeval_jqModC_ne_jqNModC_of_isPrimitiveRoot` | 17 | |
| `aeval_jqModC_ne_jqNModC` | 31 | the hypothesis the engine consumes |

Wire it with both `S_` files (each statement appears in both, byte-identically):

    spec-pin: P2M/Sol/S_ModularCurve_jqNModC_prime_not_mem_adjoin_of_charZero.lean
    spec-pin: P2M/Sol/S_ModularCurve_jqNModC_prime_not_mem_adjoin_of_forall_aeval_ne.lean

The module docstring must record (a) what the block is, (b) that it is the block the pin's `W1` section writes
written twice, homed once, (c) that `ModularPolynomialStarBank`'s fourteen `private` copies are
replaced by this import, (d) the recorded residue (§6).

### P3 — `ModularCurve/Degree/PrimeNonAdjoin.lean` (new, wired)

The node itself. Three public declarations and one `private`:

| declaration | visibility | pin span | note |
|---|---|---|---|
| `jqNModC_not_mem_adjoin_of_forall_aeval_ne` | public | 45 | the engine, `S_:512` |
| `jqNModC_prime_not_mem_adjoin_of_forall_aeval_ne` | **public headline** | 5 | the pin's `private` wrapper at `S_:557`, promoted because it is a `Theorems/` headline |
| `jqNModC_prime_not_mem_adjoin_of_coeff_ne_zero` | private | 6 | |
| `jqNModC_prime_not_mem_adjoin_of_charZero` | **public headline** | 22 | the pin's `private` wrapper at `S_:568` |

The two headlines must be stated at their **`Theorems/` wrappers' binders** (the wrapper is the
checker's statement authority — the `S_` text spells them with section variables and the two
hashes differ; this cost the ground pass two `MISMATCH` readings):

    theorem ModularCurve.jqNModC_prime_not_mem_adjoin_of_charZero {K : Type*} [Field K] [CharZero K]
        (p : ℕ) [hp : Fact (Nat.Prime p)] :
        jqNModC K p ∉ IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))

    theorem ModularCurve.jqNModC_prime_not_mem_adjoin_of_forall_aeval_ne {K : Type*} [Field K]
        (p : ℕ) [hp : Fact (Nat.Prime p)]
        (h : ∀ P : Polynomial K, Polynomial.aeval (jqModC K) P ≠ jqNModC K p) :
        jqNModC K p ∉ IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))

Wire with all four files:

    spec-pin: Theorems/Thm_ModularCurve_jqNModC_prime_not_mem_adjoin_of_charZero.lean
    spec-pin: P2M/Sol/S_ModularCurve_jqNModC_prime_not_mem_adjoin_of_charZero.lean
    spec-pin: Theorems/Thm_ModularCurve_jqNModC_prime_not_mem_adjoin_of_forall_aeval_ne.lean
    spec-pin: P2M/Sol/S_ModularCurve_jqNModC_prime_not_mem_adjoin_of_forall_aeval_ne.lean

### P4 — `ModularCurve/ModularPolynomialStarBank.lean` (edit)

Delete the fourteen `private` declarations the conjugates module now owns —
`coeff_algebraMap_mul`, `coeff_aeval_jqModC_of_lt`, `coeff_aeval_jqModC_neg_natDegree`,
`coeff_jqNModC_self`, `coeff_jqNModC_of_lt`, `ne_zero_of_aeval_eq`, `natDegree_eq_of_aeval_eq`,
`monic_of_aeval_eq`, `units_pow_eq_one_of_isPrimitiveRoot`, `qTwist_algebraMap`,
`qTwist_comp_algebraMap`, `aeval_qTwist_jqModC_eq_of_aeval_eq`, `qTwist_pow_jqModC_injective`
plus `qTwist_qExpand_of_pow_eq_one` (already public in `Defs/KatzLevelPCusps.lean` — import it,
do not restate) — keep `press`, import `Degree/JqCyclotomicConjugates`, and update the header's *Reuse*
paragraph. `press`'s proof must be unchanged; if a name now resolves to the conjugates module, no edit is
needed. The module must still read **1 ok**, 0 mismatch, and its `#print axioms` line must print
`[propext, Classical.choice, Quot.sound]`.

## 3. What the port already has — import, do not restate

Verified on disk 2026-10-25. Every one of these is public and statement-checked:

| block | home | declarations the order uses |
|---|---|---|
| `TS` and its coefficients | `Defs/TS.lean` | `TS`, `TS_coeff_mul`, `TS_coeff_of_not_dvd`, `TS_coeff_neg`, `TS_coeff_of_lt`, `TS_ne_zero`, `TS_injective`, `TS_congr`, `qTwist_TS`, `qExpand_TS`, `qExpand_qTwist_TS`, `qTwist_TS_one_cycle`, `coeffMap_TS`, `jqModC_eq_TS`, `jqNModC_eq_TS`, `qExpand_jqNModC`, `qExpand_jqModC_eq_TS` |
| `qTwist` algebra | `Defs/Twist.lean` | `qTwistEquiv`, `coe_qTwistEquiv`, `coeffMap_qTwist`, `qTwist_coeff`, `qTwist_single`, `qTwist_one_apply`, `qTwist_qExpand`, `qTwist_qTwist` |
| `phiAtSeed` packet | `Defs/PhiAtSlot.lean` | `phiAtSeed`, `phiAtSeed_map`, `phiAtSeed_monic`, `phiAtSeed_natDegree`, `phiAtSeed_eval_map` |
| cyclotomic | `Defs/Cyclotomic.lean` | `isPrimitiveRoot_pow_div` |
| the pole at the cusp | `Defs/JqCoeff.lean` | `jqModC_pow`, `coeff_jqModC_pow_self`, `coeff_jqModC_pow_of_lt`, `coeff_jqModC_neg_one` |
| `qTwist` fixes an `A`-twisted expansion | `Defs/KatzLevelPCusps.lean` | `qTwist_qExpand_of_pow_eq_one` |
| the modular polynomial packet | `ModularPolynomialProperties.lean` | `exists_phiIrreducible_evalSymm` |
| transcendence | `Degree/PhiDegree.lean` | `transcendental_jqModC` |
| `ModularPolynomialData` | `Defs/Polynomial.lean` | the structure and its fields |

Mathlib supplies the rest, all verified present in the port's `v4.34.0`
(`.lake/packages/mathlib`): `exists_integer_of_is_root_of_monic`
(`Mathlib/RingTheory/Polynomial/RationalRoot.lean:119`) — the engine's key step;
`Transcendental.uniqueFactorizationMonoid_adjoin`
(`Mathlib/RingTheory/Algebraic/Basic.lean:629`, import `Mathlib.RingTheory.Algebraic.Basic`) —
`K[j(q)]` is a UFD; `IntermediateField.algebraAdjoinAdjoin` (`coe_algebraMap` and the scoped
`Algebra`/`IsFractionRing` instances, `Mathlib/FieldTheory/IntermediateField/Adjoin/Algebra.lean`;
`open scoped IntermediateField.algebraAdjoinAdjoin`); `HahnSeries.coeff_order_eq_zero` and
`HahnSeries.order_le_of_coeff_ne_zero` (`Mathlib/RingTheory/HahnSeries/Basic.lean:374/379`):
`Polynomial.eq_of_natDegree_lt_card_of_eval_eq`, `HahnSeries.coeff_single_mul`, and the
coefficient-elimination helper the pin's `Collapse` section uses.

## 4. Known drifts — read these before transcribing

1. **`p2m` scaffolding has no port analogue.** The pin wraps every section with
   `p2m_export`/`p2m_reactivate`/`p2m_open_scoped` and ends with a `theorem solution := …`
   dispatch plus `#print axioms solution`. None of that is ported. The `attribute [-simp]` line
   at the pin's line 22 (`ModularForm.val_heckeDiagMatrix` … `val_upperTriangularGL`) is also
   **not** ported: it exists because the pin's `import Mathlib` makes those `ModularForm`
   projections simp lemmas; the port's named imports do not, so a `simp` in the proof may need
   the lemma named explicitly. Check each `simp`/`simpa` at the first build.
2. **`coeffMap_qTwist` has a different binder block.** The pin's is
   `(σ : R →+* S) (u : Rˣ) (f : LaurentSeries R)`; the port's `Defs/Twist.lean:198` takes
   `(σ) (u) (v : Sˣ) (huv : (v : S) = σ u) (f)`. Do **not** restate the pin's form: call the
   port's with `v := Units.map σ.toMonoidHom u` and `rfl`, exactly as `Defs/TS.lean:169`
   (`coeffMap_TS`) does. That call is inside `coeffMap_TS`, which the conjugates module imports.
3. **`coeffMap_TS` exists at a `ℚ`-algebra binder** (`σ : K₀ →ₐ[ℚ] K`), while the twin's
   `phiAtSeed_TS_eval` is stated over an arbitrary `σ : L →+* K` (`[Field L] [Field K]`). If the
   pin's proof reaches `coeffMap_TS` with a bare ring hom, build the algebra hom from it
   (`CharZero`/`algebraMap ℚ`; `RingHom` between `ℚ`-algebras of characteristic zero is a
   `ℚ`-algebra hom) or state the two-line `private` bridge — record whichever you take.
4. **The pin imports ten `Theorems/` files** for the block it then re-proves; the port imports
   the equivalent public modules named in §3 instead. Do not import a `Theorems/` file.
5. **`ModularForm.discriminant` / `e4cube` / `delta`** appear only in the pin's *level-one* block,
   which is not part of either node: ignore it entirely.
6. **No heartbeat bumps.** The pin sets none for these files; the port's 200,000 cap is the
   budget. If a `simp only` or an `isDefEq` blows it, restructure (name the lemmas, split the
   step) rather than raising the cap — the column's rule is no `set_option maxHeartbeats`.

## 5. Gates (all must be green, and report the readings)

1. `lake env lean <file>` for each touched file, then `lake build FLTForHuman.<Module>` for the
   four modules (single-module builds only — **never a tree `lake build`**), **0 warnings**. The
   `#print axioms` line in `StarBank` must print `[propext, Classical.choice, Quot.sound]`; add
   the same line to the two new modules for the two headlines.
2. `cd lean && python3 spec/check_port.py <the four module paths>` (add `--force` to bypass the
   cache). Expected: `JqCoeff` **18 ok**, `JqCyclotomicConjugates` **24 ok**, `PrimeNonAdjoin` **3 ok**,
   `ModularPolynomialStarBank` **1 ok** — 46 ok, **0 mismatch / 0 missing / 0 own** except
   `X0/FunctionFieldFull`'s pre-existing marker, which is not in this order. Any `MISMATCH` on a
   headline means the binder block is wrong (§P3); any on a conjugates declaration means the pin's
   section-variable spelling is the one to use.
3. `cd tools/deps && python3 dedup.py --module '*Defs/JqCoeff*' --module '*JqCyclotomicConjugates*'
   --module '*PrimeNonAdjoin*' --module '*StarBank*'` — **0 clusters**.
4. `python3 tools/deps/move_dead.py --source <module> --target /tmp/shelf.lean --select dead`
   over the four modules — **0 declarations** each (the target is a throwaway; `--dry-run` is the
   default and writes nothing).
5. `tools/check_math_delimiters.py` on any Markdown you touch — no bare dollar sign (inline
   math in the backtick-dollar form, or a plain code span).

## 6. Recording (no closure logs in `CARRY-FORWARD.md`)

`CARRY-FORWARD.md` is **open issues only**. Do not add a "landed" entry to it. The order's record
goes in `topics/PORTING-DeligneSerre.md` §1 (a landing paragraph with every reading above) and in
this order's §7 below (a short result note). Residue to record, not open:

- `jqNModC_congr` gains a public home in the conjugates module while `Degree/PhiData.lean` and
  `Degree/Roof.lean` keep their `private` copies (both are frozen-registry modules; opening them
  is a separate pass);
- `coeff_algebraMap_mul` likewise against `Defs/QExpValuationReduction.lean`'s `private` copy;
- `coeffMap_qTwist`'s five-argument binder block is the port's one form and the pin's
  three-argument spelling is not restated — call sites pass `rfl`.

## 7. Result

Landed 2026-10-25. The twin reads `needed 0` in both rows, "target is ported".

**The four modules, and the line counts.** `ModularCurve/Defs/JqCoeff.lean` **222** lines (was
201: +21, P1's `order_jqModC` and its `private` `jqModC_ne_zero`);
`ModularCurve/Degree/JqCyclotomicConjugates.lean` **519** lines (new, P2: 24 pin declarations, 21 public,
1 `private` helper of the pin's and 2 `private` local bridges);
`ModularCurve/Degree/PrimeNonAdjoin.lean` **166** lines (new, P3: engine + two headlines + the
pin's `private` discharge); `ModularCurve/ModularPolynomialStarBank.lean` **123** lines (was 266:
the fourteen `private` copies deleted, `press` byte-identical to `HEAD`, header's *Reuse*
rewritten, import switched to the conjugates module).

**The statement checker** (`python3 spec/check_port.py --force`, corpus `aa2d8b3`, the four
modules in one run):

    FLTForHuman/ModularCurve/Defs/JqCoeff.lean                 [ok]  18 ok, 0 mismatch, 0 missing, 0 own, 0 kw
    FLTForHuman/ModularCurve/Degree/JqCyclotomicConjugates.lean        [ok]  21 ok, 0 mismatch, 0 missing, 2 own, 0 kw
    FLTForHuman/ModularCurve/Degree/PrimeNonAdjoin.lean        [ok]   3 ok, 0 mismatch, 0 missing, 0 own, 0 kw
    FLTForHuman/ModularCurve/ModularPolynomialStarBank.lean    [ok]   1 ok, 0 mismatch, 0 missing, 0 own, 0 kw
    43 ok, 0 mismatch, 0 missing, 2 own, 0 kw — 4 module(s), 4 checked, 0 cached

`JqCoeff` **18 ok** and `PrimeNonAdjoin` **3 ok** are the order's readings. `JqCyclotomicConjugates`
reads **21 ok / 2 own**, not **24 ok / 0 own**: the delta is exactly the two `phiAtSeed_TS_eval*`
statements (below) plus the one row the order asks to keep `private`
(`coeffMap_algebraMap'`, invisible to the checker by design: "keep `private` here (no consumer)").
So all 24 rows land, 22 of them statement-identical.

**The frontier, measured** (`python3 tools/deps/frontier.py --target <node>
--include-s-sources`): both twin rows read `needed [F terminal] 0 nodes / 0 lines`,
`target hops to F (shortest) 0 (target is ported)`; the port cone is 49 nodes / 9,965 lines.

**The two `own:` rows, and why they cannot be `ok`.** The port's `TS`
(`Defs/TS.lean:39`) is `qExpand K e (qTwist u (coeffEmb K jq))` — the `ℚ`-model spelling the
`functionFieldGeneration` layer needs — and its binder block carries `[Algebra ℚ K]`; the pin's
per-file `W1.TS` (`S_:37`) is `qExpand K e (qTwist u (jqModC K))` over an arbitrary `[Field K]`.
`phiAtSeed_TS_eval` / `_symm` *mention* `TS`, so at the pin's `[Field K]` binders the statement
does not elaborate in the port: `Algebra ℚ K` is not synthesizable from `[Field K]` (probed), and
no pin copy of the two statements exists at a `ℚ`-algebra binder (`grep` over the corpus), so no
`pin:` marker can reach one. They are stated over `[Algebra ℚ K]` — the same theorem, one
hypothesis stronger, the two `TS` spellings agreeing by `coeffEmb K jq = jqModC K` — and recorded
as `own:` rows in `spec/decl_markers.tsv` with that reason. Everything else in the block is at the
pin's names and binders, including the three declarations the pin proves *through* `TS`
(`coeff_jqNModC_self`, `coeff_jqNModC_of_lt`, `qTwist_pow_jqModC_injective`), which are stated at
the pin's binders and proved through `qExpand`'s coefficient API instead.

**Builds** (single-module, serialized with `flock`, `timeout 400` each, logs in `tmp/`):
`JqCoeff` 3,132 jobs; `JqCyclotomicConjugates` 4,022; `PrimeNonAdjoin` 4,027; `ModularPolynomialStarBank`
4,023 — all `Build completed successfully`, exit 0, **0 warnings** (`grep -c warning` = 0 over the
four logs; the only non-build lines are the `info:` lines the three `#print axioms` commands
print). The edit loop was `lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>`,
each file 0 errors / 0 warnings; **no `set_option maxHeartbeats`** anywhere in the four modules.

**The axioms.**

    'ModularCurve.jqNModC_prime_not_mem_adjoin_of_forall_aeval_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
    'ModularCurve.jqNModC_prime_not_mem_adjoin_of_charZero' depends on axioms: [propext, Classical.choice, Quot.sound]
    'ModularCurve.StarBank.press' depends on axioms: [propext, Classical.choice, Quot.sound]

**Redundancy gates.** `dedup.py --module '*Defs/JqCoeff*' --module '*JqCyclotomicConjugates*' --module
'*PrimeNonAdjoin*' --module '*StarBank*'`: `51 declarations in 4 module(s); 0 duplicate clusters`,
`removable: 0 lines total`. `move_dead.py --source <module> --target Reserve/DryRun.lean --select
dead` over each of the four: `0 declarations, 0 lines` each, `live private helpers needed: 0`.

**Drift taken beyond §4.**

1. **§4.3 bit in a different place than predicted.** The conjugates block never reaches `coeffMap_TS` (the
   pin's `phiAtSeed_jqNModC_eval` route through `data.eval_jqNModC_mul_eq_zero`, homed in
   `Degree/PhiData.lean`, needs no `TS` at all), so **no `ℚ`-algebra bridge was written and
   `coeffMap_qTwist`'s five-argument form is never called** from this block. The `ℚ`-algebra
   binder that did bite is on `TS` itself — see the `own:` rows above.
2. **Two `private` local bridges in the conjugates module**, `coeffEmb_jq_eq_jqModC` and
   `TS_one_eq_qExpand`, carry the two `TS` evaluations' `qExpand` spelling. They stay `private`
   because their public homes (`Degree/LaurentGlue.lean`'s `coeffEmb_jq`, `Defs/TS.lean`) pull
   `JqIntegralRatios`/`X1/Defs`/`ModularForms.JqAnalyticModel` into `ModularPolynomialStarBank`'s
   cone, which imports the conjugates module (§2.4's "do not merge when sharing would invert the import
   graph"). `move_dead` reads them live.
3. **The two `phiAtSeed` evaluation proofs** replace the pin's `convert h using 2` +
   `Polynomial.ringHom_ext' …` with a named `hhom : eval₂RingHom (Int.castRingHom _) x =
   (Polynomial.aeval (R := ℤ) x).toRingHom`, then `rw [phiAtSeed, hhom, Polynomial.eval_map]` and
   the pin's `h`. Statements identical (`ok`), proof shape only.
4. **v4.34 / lint renames** the transcription needed: the pin's `Polynomial.degree_sub_lt` is
   `Polynomial.degree_sub_lt_left` (as in `StarBank`), `if_neg` is deprecated in favour of
   `ite_eq_right` (both required for 0 warnings), and `haveI : NeZero ((p : ℕ) : K)` is `have`
   (the `haveILetI` linter; `have` registers for `Prop`-valued classes, verified).
5. **`qTwist_qExpand_of_pow_eq_one`** is called at its port binding
   (`Defs/KatzLevelPCusps.lean:141`), whose `R₀` is an implicit that the statement does not use,
   so the call is `qTwist_qExpand_of_pow_eq_one p (ζ ^ b) hvb (jqModC K)` — no extra hypothesis
   and no local restatement.
6. **The pin's `jqModC_ne_zero` helper** (`S_:66`) is written `private` in `JqCoeff.lean` as the
   order asks; the port also has a public `jqModC_ne_zero_of_nontrivial` in
   `X0/FunctionFieldFull.lean`, which `Defs/JqCoeff.lean` cannot import (import graph).
7. **`attribute [-simp]` (the pin's line 22) is not ported and nothing needed it.** The pin's list
   is `ModularForm.*` projections that only the pin's `import Mathlib` makes simp lemmas; the
   port's `ModularPolynomialStarBank`, the conjugates module and the façades never mention
   `ModularForm`, and no
   `simp`/`simpa` in the four modules had to name one (each `simp`/`simp only` was checked at the
   first build; the only `simp`-related change was `if_neg` → `ite_eq_right`, item 4).
8. **`Defs/TS.lean`, `Defs/PhiData.lean` and `Defs/QExpValuationReduction.lean` were not edited:**
   `jqNModC_congr` and `coeff_algebraMap_mul` gain their public home in the conjugates module and those
   modules keep their `private` copies (frozen-registry, §6 residue). `Degree/LaurentGlue.lean`'s
   `coeffEmb_jq` is likewise not imported, only cited.
