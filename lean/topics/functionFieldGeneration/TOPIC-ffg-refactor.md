# Topic: the FFG layer — the carrier as a section variable, and the A-side descent

**Status: landed (2026-11-08).** This file is the plan for the FFG layer's current correction, and
its §13 records what was actually built (the plan's own §5 was corrected on the way: the prime
non-membership stays two-field, for a reason §6.1 already gave). It
supersedes the earlier dated wave record of this path; that record, and the capstone refactor it
describes, are in git history, in [`../CASE-hall-all.md`](../CASE-hall-all.md) (the reusable case
study) and in [`PORTING-FFG.md`](../PORTING-FFG.md) (the porting record). The any-field layer's own
design record is [`TOPIC-t19-any-field.md`](TOPIC-t19-any-field.md); its §11 carries the same
revision.

**Audience.** Whoever next touches `FunctionFieldGeneration/Generic/`. Nothing below is new
mathematics: it decides *where the two coefficient fields appear*, and it is a correction of the
plan's own first version, which mistook a type adaptation for the content and put a base-change
lemma on the critical path.

**The subject in one paragraph.** The any-field layer is parameterized by a carrier
`ε : LaurentSeries κ →+* LaurentSeries κ'` — an arbitrary ring hom, with two premises — and that
parameter is threaded through the slot-value API, the minimal-polynomial objects and the
slot-product induction (48 signature positions and 54 `hεq` occurrences in the four `Generic/`
modules). The two coefficient fields are *not* the problem: the minimal polynomial of the level
series genuinely lives over the base field of `κ`, while the roots of `Φ_p` are read where a
primitive root exists, in `κ'`. What is removable is the **carrier as a parameter**: both
instances' carriers are coefficient extensions, so they are `coeffMap (algebraMap κ κ')`, and then
`hεq` is the theorem `coeffMap_qExpand` and `hε` is `coeffMap_jqModC`. The correction is to declare
`[Algebra κ κ']` and let the two fields live in the *types*, with `nomeMap` the single bridge.

---

## 1. The layer as it stands

```text
FunctionFieldGeneration/
  Generic/                     the theory, at two coefficient fields joined by a carrier ε
    LevelPackage.lean    121   levelSeries, baseField, levelField, degreeAt, generatedAt, PkgAt
                               + isIntegral_levelSeries, natDegree_minpoly_levelSeries
    SlotValue.lean       149   slotValue, slotValue_eq_TS, slotValue_inj, slotValue_inj_slot,
                               slotValue_top                       (all carry ε)
    SlotProduct.lean    1015   nomeMap, pushedMinpoly, pushedMinpolyAt, slotPolynomial,
                               SlotProductAt; the induction; the headline
    PrimeNonmembership.lean 354  prime_notMem_levelField (the prime non-membership)
    PrimeStep.lean       313   levelSeries_mem_levelField_mul_prime (the prime step / descent)
  Rat/                        the ℚ instance data
    LevelPackage.lean     60   Tight, Gen, Hall; hall_pkgAt, gen_iff_levelField
    SlotProduct.lean      73   pushedMinpoly_rat, pushedMinpolyAt_rat, minpoly_eq_prod_slotValues
  CharP/                      the any-field (C-layer) instance data
    LevelPackage.lean     70   modularFunctionFieldC_iff_generatedAt, pkg_pkgAt
    SlotProduct.lean      77   pushedMinpoly_anyField, minpoly_jqNModC_map_eq_prod_slots
    Nonmembership.lean    57   jqNModC_prime_not_mem_fullC
  SlotProduct.lean       249   the ℚ surface: sv, sv_eq_TS, sv_inj, sv_inj_slot,
                               map_qExpand_minpoly_eq, minpoly_jqN_map_eq_prod_slots
  Nonmembership.lean     687   jqN_prime_not_mem_full, the prime-power tower
  Descent.lean           179   jqN_div_mem_modularFunctionField, the one-prime reduction
```

The rule the layer is built on, and which the correction does not change: **definitions at the
most general field, one theorem per mathematical content at the most general hypothesis, and the
per-layer hypotheses (the package, the base non-membership) are exactly what that layer can
prove.** What the correction changes is how the two fields are *passed*, not what is assumed.

---

## 2. The diagnosis

### 2.1 What the carrier is doing, and which part is content

`ε` carries three jobs at once:

1. **Naming the field where the roots live.** The slot values are twiddled nomes; they need a
   primitive root of unity, which `κ` need not have (`κ = ℚ` never has one). Content.
2. **Carrying the source field's minimal polynomial into that field.** `pushedMinpolyAt` maps
   `minpoly (baseField jg) (levelSeries jg m)` along `nomeMap`. That polynomial is over a field of
   `LaurentSeries κ`; the roots are elements of `LaurentSeries κ'`. The map between them is content
   — this is the *relative* half of the theory (supplement §4), and it is why the package
   hypothesis can stay a fact about the `j`-series over `κ`.
3. **Relation bookkeeping.** `hεq : ∀ N, ε (qExpand κ N x) = qExpand κ' N (ε x)` is not a
   hypothesis about mathematics: it says `ε` commutes with the nome, which `coeffMap` does by
   construction. `hε : ε jg = jqModC κ'` likewise says "the carried series is the carrier's
   `j`-series", which for a coefficient extension follows from `jg = jqModC κ` by
   `coeffMap_jqModC`. Type adaptation.

Jobs 1 and 2 keep both fields in the types. Job 3 is what the correction deletes.

### 2.2 The role of `A` and `B` in the prime step

The prime step is `Polynomial.mem_range_of_unique_common_root A B`: `A` must be the **enumerated**
polynomial, `B` the witness. `exists_transported_minpoly` produces `B` with its slot list, and the
call `mem_range_of_unique_common_root B A` enumerates `B`. The supplement §3 names the two choices:

* **(a) `A = Φ_p` enumerated.** Monic of degree `p+1`, split with distinct roots over any field
  containing a primitive `p`-th root, root shape known (the extra conjugate and the `p` twists) —
  all intrinsic. It needs exactly two facts about the roots of `B`.
* **(b) `B` enumerated.** `B` is monic and squarefree *because* the slot product identifies it with
  the slots. `Φ_p` is then the witness.

The port took (b). That is correct — and it is *why* the slot product is stated through the carrier
(the slot list of the pushed minimal polynomial). The correction is (a), which is also the pin's own
decomposition of the node: a descent that takes two root-exclusion facts, and a slot product that
supplies them.

### 2.3 The measured surface of job 3

| module | decls | carrier binders | `hεq` occurrences |
|---|---|---|---|
| `Generic/SlotValue.lean` | 8 | 8 | — |
| `Generic/SlotProduct.lean` | 32 | 30 | 33 |
| `Generic/PrimeStep.lean` | 14 | 6 | 9 |
| `Generic/PrimeNonmembership.lean` | 4 | 4 | 12 |
| **total** | **58** | **48** | **54** |

### 2.4 What stays

The present shape moved arithmetic and type adaptations out of the main proof lines, and that is
right. In `Generic/PrimeStep.lean` the producers and the named index arithmetic stay:
`exists_phiAtSeed_roots`, `slotLevel`/`conjLevel`/`twistLevel`/`slotUnit` and the three lemmas
around them, `levelNomeMap`, `nomeMap_mul_comm`, `mem_of_mem_range_levelNome`. In
`Generic/SlotProduct.lean` the whole decomposition stays — producers, the two prime cases, the
descent, the closing squeeze. No proof line is rewritten for its own sake.

---

## 3. The corrected shape

Two coefficient fields in the **types**, no carrier **parameter**, one bridge.

```text
      definitions                qExpand, qTwist, TS, coeffMap, jqModC, phiAtSeed, Φ_p data
          │
      section variables          [Algebra κ κ'],   σ := coeffMap (algebraMap κ κ')
          │
      ┌───┴─────────────────────────────────────────────┐
   source side of κ                                    target side, κ'
   baseField jg, levelSeries jg d,                     slotValue (σ jg), slotPolynomial (σ jg),
   PkgAt jg, the tower law                             TS κ', the Φ_p root shape and factorisation
      └───────────────┬───────────────────────────────┘
                 nomeMap jg N   (the one bridge)
                      │
      the theorems:  pushedMinpolyAt jg m N  =  slotPolynomial (σ jg) N ζ
```

**Where the two fields appear, after the correction.**

| statement | shape | why |
|---|---|---|
| `nomeMap`, `pushedMinpolyAt` | source minpoly, target slots | §2.1 job 2: the minimal polynomial is over the base field of `κ`, its roots are in `κ'` |
| `slotValue`, `slotPolynomial`, `TS`, the `Φ_p` lemmas | one field (`κ'`) | the slots live where the root lives |
| `SlotProductAt`, the induction | one `Prop`, no `ε`, no `hεq`; hypothesis `PkgAt jg` on the **source** side | the package is a fact about the `j`-series over `κ`, which is what `ℚ` and `C` both supply |
| `levelSeries_mem_levelField_mul_prime` | two fields in the **conclusion** | a membership in a field of `κ` proved by reading roots in `κ'`; §2.1 job 1, irreducible |
| `prime_notMem_levelField` | one field, at a field with the root | its conclusion is a *non*-membership, which descends for free (§5) |
| `Generic/LevelPackage` | one field | unchanged |

**The carrier is a coefficient extension.** `[Algebra κ κ']` and `σ := coeffMap (algebraMap κ κ')`.
Both instances are of that shape (`Rat`: `Algebra ℚ K`, since `coeffEmb K = coeffMap (algebraMap ℚ K)`;
`CharP`: `Algebra K K`, the identity), so this loses nothing, and it makes `hεq` a theorem
(`coeffMap_qExpand`) and `hε` a theorem (`coeffMap_jqModC`).

**What this does and does not remove from the API.** A section variable is sugar for a binder, so
the pair *is* in the telescope of every declaration that uses it — `{κ} {κ'} [Field κ] [Field κ']
[Algebra κ κ']`, implicit and instance-implicit, never an explicit argument. What disappears is the
carrier as an *argument* and `hεq` as a *premise*; `hε` becomes `hjg : jg = jqModC κ` on the source.
The telescopes are mixed on purpose: the slot objects (`slotValue`, `slotPolynomial`, `TS`) mention
only the one field, because the slots need only the field with the root; the bridge (`nomeMap`,
`pushedMinpolyAt`) and the theorems mention both, because the minimal polynomial is over the source
base field. No call site names any of them — `κ` comes from `jg : LaurentSeries κ`, `κ'` from
`ζ : κ'ˣ` and from the goal, `[Algebra κ κ']` from instance search — so a call reads `f jq rfl …`
where today it reads
`f (coeffEmb K) jq (coeffEmb_jq K) (fun N _ x => coeffEmb_qExpand K N x) …`.

**What the coefficient map is still needed for.** The pair alone would be ill-posed: two series
rings with no relation cannot even state "the minimal polynomial over the source base field, read
where the roots live". The map earns its place in exactly four facts, and none of them is a
hypothesis:

| fact | how it appears today | content | after the fold |
|---|---|---|---|
| `coeffMap` is a ring hom | the `ε` binder, 48 positions | extension acts coefficientwise | the canonical map of `[Algebra κ κ']` |
| commutes with the nome | **54** `hεq` sites | the nome moves exponents, the extension moves coefficients | `coeffMap_qExpand` |
| fixes the `j`-series | **36** `hε` sites | `j(q)` has integral coefficients | `coeffMap_jqModC` (plus `jg = jqModC κ`) |
| is injective | **4** `RingHom.injective ε` sites | a field hom is injective: monic and degree survive the push, and the rational slice embeds faithfully | `coeffMap_injective` |

Everything else in the theory is one-field: the package and the tower law on the source side, the
slot values, `TS` and the `Φ_p` root shapes on the target side. And the map is used in only two
directions: *forward*, to push series and polynomials (everywhere in the statements), and
*backward*, in four places, to pull a membership in the range back to the source field and an
equation at the carrier back to the source. The backward direction is exactly where the two-field
form is stronger than the base-changed one: the conclusion returns along an injective map, not along
a trace.

**What is *not* in this shape.** There is no `Generic/BaseChange.lean`, and **no base-change degree
lemma is needed at all** — not on the critical path, not anywhere else (§6.1). What the port does use
of the supplement's §5 dictionary is (5.1)'s adjoin identities, and those it already writes inline
(`Descent.lean`'s `hset`, `Nonmembership.lean`'s field conversion).

---

## 4. `Generic/SlotValue.lean` and `Generic/SlotProduct.lean`

### 4.1 The slot side, at one field

```lean
def slotValue {κ : Type*} [Field κ] (jg : LaurentSeries κ) (ζ : κˣ) (a b : ℕ) : LaurentSeries κ :=
  if h : a = 0 then 0 else
    letI : NeZero a := ⟨h⟩
    qExpand κ (a * a) (qTwist (ζ ^ (b * a)) jg)
```

The `dite` shape is kept verbatim (it is what `slotValue_def` pins, and what the pin's `sv` names).
Every statement in `SlotValue` and in the slot half of `SlotProduct` is at one field; the only
premise it needs is the one that says `jg` is the `j`-series:

```lean
theorem slotValue_eq_TS (jg : LaurentSeries κ) (ζ : κˣ) (a b : ℕ) [NeZero a]
    (hjg : jg = jqModC κ) : slotValue jg ζ a b = TS κ (a * a) (ζ ^ (b * a))
```

At the theory's carrier this is `hjg := coeffMap_jqModC hjg : σ jg = jqModC κ'`.

### 4.2 The bridge and the pushed objects (the only two-field definitions)

```lean
/-- Read the source base field at the level-`N` nome, in the carrier. -/
def nomeMap {κ κ' : Type*} [Field κ] [Field κ'] [Algebra κ κ']
    {jg : LaurentSeries κ} (N : ℕ) [NeZero N] : baseField jg →+* LaurentSeries κ' :=
  ((coeffMap (algebraMap κ κ')).comp (qExpand κ N)).comp
    (algebraMap (baseField jg) (LaurentSeries κ))

/-- The pushed minimal polynomial: the source minimal polynomial read at the level-`N` nome. -/
def pushedMinpolyAt {κ κ' : Type*} [Field κ] [Field κ'] [Algebra κ κ']
    (jg : LaurentSeries κ) (m : ℕ) [NeZero m] (N : ℕ) [NeZero N] : Polynomial (LaurentSeries κ') :=
  (minpoly (baseField jg) (levelSeries jg m)).map (nomeMap N)

/-- The slot product: the induction statement. The premises stay inside the `Prop` so the
induction statement and the headline keep one shape. -/
def SlotProductAt {κ κ' : Type*} [Field κ] [Field κ'] [Algebra κ κ']
    (jg : LaurentSeries κ) (M : ℕ) [NeZero M] (ζ : κ'ˣ) : Prop :=
  jg = jqModC κ → IsPrimitiveRoot (ζ : κ') M → PkgAt jg M →
    pushedMinpolyAt jg M M = slotPolynomial (σ jg) M ζ
```

`pushedMinpoly` is the diagonal `pushedMinpolyAt jg M M`; the induction is
`slotProductInduction (jg) : ∀ (M) [NeZero M] (ζ : κ'ˣ), SlotProductAt jg M ζ`.

### 4.3 What disappears from the proofs

| gone | replaced by |
|---|---|
| the `ε` parameter (48 binders) | the section variable `[Algebra κ κ']` |
| `hε : ε jg = jqModC κ'` | `hjg : jg = jqModC κ` on the source; `coeffMap_jqModC` on the carrier |
| `hεq` (54 occurrences) | `coeffMap_qExpand` |
| `nomeMap_comp_qExpand` (a 13-line `RingHom.ext`) | `coeffMap_qExpand` + `qExpand_qExpand` |
| `map_levelSeries` | `levelSeries_coeffMap : σ (levelSeries jg d) = levelSeries (σ jg) d` (two lines from `coeffMap_qExpand`) |
| `seed_eval_zero` / `_symm` pulling the modular relation back along an injective `ε` | `phiAtSeed_jqNModC_eval` / `_eval_symm` at `κ'` directly |
| the `hεq` argument of `pushedMinpolyAt_map_qExpand` | `qExpand_qExpand` |
| `nomeMap_congr` with a carrier | `qExpand_congr` inside `nomeMap` |

The induction's body keeps its decomposition and its source-side algebra (`hall` at the source, the
tower law on the source level fields); its slot computations are already `κ'`-computations. This is
a signature-and-plumbing change: expect no new proof obligations, and no change to any statement's
mathematics.

### 4.4 What stays exactly as it is

`isRoot_map_minpoly_of_isRoot_subfield`, `exists_algHom_adjoin_of_isRoot` (public; its
`[Algebra (baseField jg) (LaurentSeries κ')]` shape is what the crossing uses),
`finrank_adjoin_mul_dedekindPsi`, `phiAtSeed_slot_factor`, the two prime cases, the descent and
`isRoot_map_minpoly_slot` need only the mechanical change of §4.3.

---

## 5. `Generic/PrimeNonmembership.lean`: one field

```lean
theorem prime_notMem_levelField {κ : Type*} [Field κ] (jg : LaurentSeries κ)
    (hjg : jg = jqModC κ) {M p : ℕ} [NeZero M] [NeZero p] [hp : Fact (Nat.Prime p)]
    {ζ : κˣ} (hζ : IsPrimitiveRoot (ζ : κ) (M * p)) (hpM : ¬ p ∣ M) (h : PkgAt jg M)
    (hbase : levelSeries jg p ∉ (baseField jg : Set (LaurentSeries κ))) :
    levelSeries jg p ∉ levelField jg M
```

Its proof is unchanged in content: the `ψ(M)`-slot multiset of the pushed minimal polynomial, the
`Φ_p` dichotomy at the conjugate, `mem_range_of_eval_eq_const`, and the pull-back to the base field.

**Correction (landed): it stays two-field.** As an *evaluation* the one-field form is what the `C`
layer wants, and that is what it gets. As the `ℚ` layer's route it does not close: the `ℚ` layer holds
`Hall M`, i.e. `PkgAt jq M`, but the `K`-side theorem needs `PkgAt (jqModC K) M`, and the missing
clause is exactly the level-degree clause at the carrier — transportable only by the banked
dictionary's `(5.2)` (§6.2), which §6.1 rules out. This is §6.1's own principle ("the carrier in the
slot product is what keeps the package on the source side") applied to the non-membership; the plan's
first version overlooked it. So the theorem keeps the source condition `jg = jqModC κ` and the
package at the source `jg`, with both fields as a section variable; `ℚ` is
`(κ := ℚ) (κ' := K)` with `coeffEmb` and `hjg := rfl`, and `C` is `(κ := κ' := K)` with `hjg := rfl`.
The free descent of a non-membership (supplement §4) is then not spent at all, which is simpler.

This is where the supplement's §4 asymmetry is spent: a non-membership's conclusion base-changes
for free. That is why the non-membership may be stated at one field and the membership may not.

---

## 6. The base-change dictionary: proved, and *not* on the critical path

### 6.1 Why the fold does not need it

One equivalence is worth stating once, because it is why this section is short:

> **The carrier in the slot product is what keeps the package hypothesis on the source side.**

The current (pushed) statement is `pushedMinpolyAt jg M M = slotPolynomial (σ jg) M ζ` with
hypothesis `PkgAt jg M`: the minimal polynomial is taken over `baseField jg` and merely *pushed*, so
its degree is `ψ(M)` by `Monic.natDegree_map` from the source package, and no base-change lemma
appears. A statement of the *same* mathematical content with the minimal polynomial taken over
`baseField (σ jg)` would have to hypothesis `PkgAt (σ jg) M` — the package at the carrier — which
`ℚ` cannot supply. So the fold keeps the pushed form on purpose, and `ℚ` and `C` stay
instantiations (§7, §8).

**And nothing else in the port needs it either.** Walk the three statements the `ℚ` layer cites:

* the pinned slot-product headline is the pushed headline at `(jg := jq, κ' := K)` — no base change;
* the prime step returns to `κ` through the range of `levelNomeMap` — no base change, and no `(5.4)`;
* the `ℚ` non-membership is the `K`-side one-field theorem (whose base hypothesis is
  `jqNModC_prime_not_mem_adjoin_of_charZero`, a live char-zero fact) plus the *free* descent of a
  non-membership, whose only base-change content is the adjoin identity of (5.1).

So (5.2) is not needed by any statement the port cites. It was needed only by this plan's own first
design, which stated (2.1) as a one-field theorem and thereby moved the package hypothesis from `ℚ`
to `K` — and that is the design the correction abandons (§11, first bullet).

### 6.2 What was proved anyway (`Reserve/ModularCurve/FunctionFieldGeneration/BaseChange.lean`)

A probe establishes the dictionary's one non-formal fact: the regularity of the level function field
over its coefficient field. It is proved and shelved as
`Reserve/ModularCurve/FunctionFieldGeneration/BaseChange.lean` — no `sorry`, no warnings, exit 0 in
~19 s, axioms `[propext, Classical.choice, Quot.sound]` — so the option below costs nothing to pick
up later:

```lean
/-- (5.2): adjoining the coefficient field does not change the relative degree. -/
theorem finrank_levelField_coeffMap {κ κ'} [Field κ] [Field κ'] [Algebra κ κ']
    [FiniteDimensional κ κ'] (jg : LaurentSeries κ) (d : ℕ) [NeZero d] :
    Module.finrank (baseField (coeffMap (algebraMap κ κ') jg))
        (levelField (coeffMap (algebraMap κ κ') jg) d)
      = Module.finrank (baseField jg) (levelField jg d)

/-- Its `degreeAt` corollary: the package's degree clause transports. -/
theorem degreeAt_coeffMap (jg) (d) : degreeAt (coeffMap (algebraMap κ κ') jg) d ↔ degreeAt jg d
```

with two supporting lemmas: a generic `finrank ↥K ↥E = relfinrank K (E.restrictScalars F)` bridge,
and `relfinrank_sigma_eq_sup` (the `Subfield`-level identification of the two `⊔`-forms). The
mathematics is the supplement's §5.1–§5.2: a `κ`-basis of `κ'` stays independent over the level
field, by comparing `HahnSeries.coeff` (the coefficient separation); then
`LinearDisjoint.adjoin_rank_eq_rank_left_of_isAlgebraic` at `d` and at `1`, two tower laws, and
cancellation of the finite `[κ' : κ]`. `[FiniteDimensional κ κ']` is essential to this route: it is
spent only through `Module.finrank_pos` in the cancellation, and cannot be dropped, since at
`[κ' : κ] = 0` the two tower equations carry no information.

**Traps, measured (do not repeat):**

1. `baseField (σ jg)` is a **`κ'`-based** `IntermediateField` — `baseField`'s implicit `κ` unifies
   with the argument's coefficient field. So `C ⊔ baseSigma jg = baseField (σ jg)` is *not* an
   `IntermediateField` equality (`toSubfield_inj` does not cross base fields); the identification
   must happen on `Subfield`s. That is what `relfinrank_sigma_eq_sup` is for.
2. `Module.finrank ↥A ↥B` for two `κ`-based intermediate fields with `A ≤ B` does not elaborate —
   mathlib only gives `Algebra ↥S ↥T` for `T : IntermediateField ↥S L`. The tower law must run on
   `relfinrank` (`relfinrank_mul_relfinrank`), not on `Module.finrank` over a shared bottom; and
   `relfinrank_map_map` applies only on the `κ`-based side, hence the `restrictScalars κ`.
3. `Nat.mul_right_cancel` rewrites the same numeral twice; use `Nat.mul_left_cancel` plus a `calc`.
4. A doc comment cannot directly precede `omit … in`; give the instance-free declaration its own
   section instead.

**Placement when it is promoted:** the generic bridge to `FieldTheory/`; the level-field form
(`relfinrank_sigma_eq_sup`, the target, `degreeAt_coeffMap`, and the ~200 lines they rest on —
`coeffMapAlg`, `constField`, `baseSigma`/`levelSigma`, `linearDisjoint_*`, `relfinrank_sup_const`,
`toSubfield_sup_*`) to a new `FunctionFieldGeneration/Generic/BaseChange.lean`. **`Defs/Laurent.lean`
needs nothing**: the only series fact used is `coeffMap_qExpand`, already there.

### 6.3 The optional follow-up it enables (not this wave)

With (5.2) and the minimal-polynomial transport (5.3: `minpoly` over the image base field is the
image of `minpoly` over the source — divisibility plus the degree equality of (5.2)), the pushed
form collapses to a genuinely one-field theorem at `κ'`,

```lean
theorem pushedMinpoly_eq_slotPolynomial (jg' : LaurentSeries κ') (hjg' : jg' = jqModC κ')
    (hζ) (hK : PkgAt jg' M) : pushedMinpoly jg' M = slotPolynomial jg' M ζ
```

and the pinned `ℚ` statement becomes *literally* that theorem as a base change, with
`Hall → PkgAt (jqModC K)` supplied by §6.2. The faithful descent that the one-field forms would
otherwise need (`(5.4)` of the supplement) is the *same* lemma in its intersection form, so the
collapse needs no trace theory either — see the supplement's §5.4 remark. Worth doing only if a
consumer wants the collapsed form, or if the `C`-layer statement and the `ℚ` statement are to become
one declaration. Until then the pushed form is both the pin's and the cheaper one.

---

## 7. `Generic/PrimeStep.lean`: the one statement whose conclusion crosses

### 7.1 The statement

```lean
theorem levelSeries_mem_levelField_mul_prime {κ κ' : Type*} [Field κ] [Field κ'] [Algebra κ κ']
    (jg : LaurentSeries κ) (hjg : jg = jqModC κ)
    {M p : ℕ} [NeZero M] [NeZero p] [hp : Fact (Nat.Prime p)] {ζ : κ'ˣ}
    (hζ : IsPrimitiveRoot (ζ : κ') (M * p)) (h : PkgAt jg M) :
    levelSeries jg M ∈ levelField jg (M * p)
```

No carrier parameter, no `hε`, no `hεq`. The package hypothesis stays **by default**, because the
default proof is the present one (§7.2); dropping it is a separate, optional decision (§7.3).

**This statement cannot be weakened to one field.** It is the one place where the two fields are in
the conclusion: the result is a membership in a field of `LaurentSeries κ`, and the argument has to
read the roots of `Φ_p` at a primitive `(M*p)`-th root, which `κ = ℚ` does not have. The one-field
form — `levelSeries (σ jg) M ∈ levelField (σ jg) (M*p)`, provable at `K` by the same argument — does
**not** imply it: passing from a membership in the `K`-level field to one in the `ℚ`-level field is
the faithful descent of the supplement's `(5.4)`, which the port neither has nor wants. So the
conclusion returns by `mem_of_mem_range_levelNome` (the image of `levelNomeMap`, hence a field of
`κ`), never by a trace.

### 7.2 The default proof: the B-side, with the carrier parameter gone

Today's proof stays. `exists_transported_minpoly` produces `B`, the pushed minimal polynomial with
its root list (the slot list, from the slot product at the carrier); `exists_phiAtSeed_roots`
produces `A = Φ_p` at the seed, whose root shape gives the case split in `huniq`; the cases are
decided by `TS_injective` plus the index arithmetic (`slotLevel_ne_conjLevel`,
`slotUnit_eq_one_of_twistLevel`, `eq_zero_of_pow_eq_one`); then
`mem_range_of_unique_common_root B A` and `mem_of_mem_range_levelNome`.

What changes in this wave is only the carrier: the two helpers that existed to relate the fields
(`map_levelSeries`, and the `hεq`-threading through every step) disappear, and the binders `ε`,
`hε`, `hεq` become the section variable plus `hjg`. Nothing in the argument is re-derived.

The cost of this choice, stated plainly: the descent's proof *enumerates* `B`, so `PrimeStep`
depends on the slot product's root list, and the membership keeps a hypothesis (`PkgAt`) that it
does not mathematically need. That is the design question of §2.2, and §7.3 is its other answer.

### 7.3 The optional A-side (not part of the de-noising)

If we also want the descent to stop enumerating `B`, the supplement's §3(a) applies: `A = Φ_p` is
the enumerated polynomial (monic, split, distinct roots, root shape — all intrinsic), `B` is a
witness, and uniqueness is the two root-exclusion facts instead of a slot comparison. The proof is
already in the tree, not a design (written on the shelf, moved back 2026-11-08):
`FunctionFieldGeneration/CharP/PrimePowerStep.lean`'s
`jqNModC_mem_of_div_primes`, `…_of_div_prime_of_mul_prime` and the divisor induction
(`jqNModC_mem_adjoin_top_insert`, `fullC_succ_eq_adjoin_insert_divSet`,
`fullC_mul_prime_eq_adjoin_insert_image`): two `Φ_p`'s, no minimal polynomial, uniqueness by
`TS_injective` plus level arithmetic. Ported with the target field being the statement's own
(`F := levelField jg (M * p)`, induction over `d ∣ M * p` on
`σ (levelSeries jg d) ∈ range (levelNomeMap)`), it concludes the statement directly and **drops
`PkgAt`**, which also removes `hall_pkgAt` from `Descent.lean`.

Why it is optional rather than part of this wave:

* the ε complaint is answered by §3–§5 without it — the carrier is gone as a *parameter* either
  way, and the B-side proof carries no `hεq` once the carrier is a coefficient extension;
* it changes a *statement* (`PkgAt` leaves) and a *proof* (the descent stops importing the slot
  product), i.e. two things a reader must re-verify, for no reduction in the ε surface;
* there is a second, independent reason for it, which the plan did not have at first: the
  unique-common-root principle needs a **split** polynomial, and `LaurentSeries κ'` is not a
  splitting field of `B` — `q` has no square root there, since squares have even valuation — so the
  B-side must obtain `B`'s splitting from (2.1) itself, exactly the equality it is trying to use.
  The A-side needs no splitting of `B` (`Φ_p` factorises over any field with a primitive `p`-th root,
  and `B` is a witness); that is why its relative input is two exclusions rather than an equality;
* one hazard this makes explicit: `minpoly` is total with junk value `0` off the integral locus, so
  `pushedMinpoly`/`pushedMinpolyAt` are *junk* unless the package's degree clause holds. Every
  statement that compares them must carry `degreeAt` — which `PkgAt` does — and the base-change
  transport is safe only because it is `Monic.natDegree_map` on a nonzero source minpoly
  (injectivity of `σ`), never a comparison of two possibly-zero polynomials;
* if it is taken, order the peel first and drop the hypothesis only when the induction compiles;
  and note that the shelf's `fullC`-induction targets the divisor adjoin, while the statement's
  target is the level field, so the induction's target is the statement's field, not `fullC`.

Do it when someone wants the package-free membership, or the pin's node structure (a descent that
is intrinsic and a slot product that supplies the two root facts) — not as part of de-noising.

---

## 8. The instances and the pinned spellings

### 8.1 `Rat/`, the flat `SlotProduct.lean`, and `sv`

The pinned `ℚ` statements keep their text and their names: `sv`, `sv_eq_TS`, `sv_inj`,
`sv_inj_slot`, `map_qExpand_minpoly_eq`, `minpoly_jqN_map_eq_prod_slots`. What changes is where their
proofs point, and (for `sv` alone) what its body names:

* `sv K ζ a b` becomes `slotValue (jqModC K) ζ a b` — the one-field object at the `ℚ` instance. The
  pin's text (`if a = 0 then 0 else qExpand K (a*a) (qTwist (ζ^(b*a)) (coeffEmb K jq))`) is
  recovered as one theorem `sv_eq_pin` (`coeffEmb_jq`): the pin's body is a proved equality, not a
  definition. `sv_eq_TS`/`sv_inj`/`sv_inj_slot` are the theory's statements at `hjg := rfl`.
* `pushedMinpoly_rat` / `pushedMinpolyAt_rat` are deleted: the pushed object now *is* the theory's
  object (`pushedMinpolyAt` at `jg := jq`, `κ' := K`), with no carrier to transcribe.
* `minpoly_eq_prod_slotValues` (the pinned headline) is one application of the headline at
  `(jg := jq, ζ, hall_pkgAt M hM)` plus the pin's iterated spelling (`prod_slotValues`) — which is
  what it is today, minus the two carrier arguments.

### 8.2 `CharP/` — the any-field instance, and the check that the shape is not `ℚ`-shaped

`CharP` is the diagonal case of §3: `[Algebra K K]` (found as `Algebra.id`), so
`σ = coeffMap (algebraMap K K) = RingHom.id`. It is also the layer that keeps this design honest,
because nothing in it mentions `ℚ` or characteristic zero. Checked on a probe:

* at `κ = κ' = K`, `nomeMap` and `pushedMinpolyAt` *are* the one-field nome map and the one-field
  pushed minimal polynomial (`simp`);
* the theory's hypothesis is `PkgAt (jqModC K) M`, which `pkg_pkgAt` supplies from the pin's
  `Pkg K M` — generic in `K`, no `ℚ`, no char-0;
* `σ = id`, so the slot side is `slotValue (jqModC K)` and the headline is the pinned
  `minpoly_jqNModC_map_eq_prod_slots` up to the iterated product.

Two adaptations this costs:

* the port has `coeffMap_id` only **pointwise** (`coeffMap (RingHom.id R) x = x`); the collapse needs
  its ring-hom-level form `coeffMap (RingHom.id K) = RingHom.id (LaurentSeries K)` — two lines,
  `RingHom.ext fun x => coeffMap_id x` — which belongs beside `coeffMap_id` in `Defs/Laurent.lean`;
* the C layer keeps its own package shape: `Pkg K M` is the pin's inline conjunction, converted by
  `pkg_pkgAt`. The design does not ask for a derivation of its degree clause — that is the socket,
  and it stays conditional, as today.

The three `CharP` modules then get shorter without changing their statements, and the A-side option
of §7.3 is any-field too: `CharP/PrimePowerStep` is precisely that proof at a general
field. One caveat, unchanged from today: if the characteristic equals the prime in play there is no
primitive root of that order, so the `Φ_p` step's hypotheses are unsatisfiable — vacuous, not wrong.

### 8.3 `Descent.lean` and `Nonmembership.lean`

* `Descent.lean`: `jqN_div_mem_modularFunctionField` calls §7.1 with
  `[Algebra ℚ (CyclotomicField (M * p) ℚ)]` and `ζ = cycUnit`; the `hall_pkgAt` plumbing goes with
  the package hypothesis. The `levelField`/`modularFunctionField` conversion stays (it is the only
  `ℚ` content in it).
* `Nonmembership.lean`: `jqN_prime_not_mem_adjoin` evaluates §5 at `κ = K` (§5's two bullets) and
  returns to `ℚ` by the free direction. The tower `jqN_pow_not_mem_adjoin_full` is untouched.
* `Generation.lean`, `DegreeStep.lean`, `Target.lean`, `Collapse.lean`, `Capstone.lean`: untouched.

---

## 9. How the refactor is measured

The porting playbook's rule for this phase: *once a node's consumers are ported, they hold the
interface; a refactor may respell the statement and the test is that every call site compiles
unchanged, not that the text still matches the pin* (`porting-playbook.md`, top matter; §4). So the
gates are the build, the consumers and the axioms — not the statement checker, not the unwired
register, not `dedup.py`.

* **Consumers.** `Descent.lean`, `Nonmembership.lean`, the flat `SlotProduct.lean`, `CharP/{SlotProduct,
  Nonmembership}.lean`, `Rat/{SlotProduct,LevelPackage}.lean` and the capstone cone must elaborate
  with their call sites unchanged *except* for the binders this wave deletes (`hε`, `hεq`, and
  `hall_pkgAt` if §7.3 is taken). That is the measurement.
* **`spec/GenericProbe.lean`** is the one spec-side file that must keep elaborating: it is the
  compile-time probe that the theory has no `ℚ`-algebra leak. Re-point it to the section-variable
  form (its statements lose the carrier arguments and take `[Algebra (ZMod 5) (ZMod 5)]`).
* **`spec-pin:` headers** stay as provenance; `check_port` is a sanity check, not a gate. The
  pinned statements' text does not change in this wave, so its counts should be unchanged — but a
  count moving is a fact to report, not a reason to reshape the code (`sv`'s *body* changes; its
  type and pin text do not, and the pin text lives on as the theorem `sv_eq_pin`).
* **Presentation.** `capstone.json` describes `Capstone`, which does not change; re-render only if a
  file/line it quotes moves.
* **Docs.** `TOPIC-t19-any-field.md` §11 carries the same revision; `TOPIC-descent.md` §2 stays the
  statement-retirement record; `math/010` and `math/010a` are the mathematics and are not edited.

## 10. Waves and gates

Each wave is green before the next. Per AGENTS.md: no tree `lake build`; targeted builds only, and
stop and report if a single `lake env lean` approaches two minutes.

**Wave 1 — the carrier becomes a section variable.** §4 and §5: `[Algebra κ κ']`, `σ`, the slot
side at `κ'`, the pushed objects, and the deletion of `hε`/`hεq`; the `ℚ`/`C`/flat call sites move
with it (the tree cannot be green between them: the pinned headline and the non-membership are the
theory's consumers). `PrimeStep` moves in the same change and keeps its present proof (§7.2). Gates:
every touched module silent; the consumer list of §9 elaborates; the probe elaborates.

**Wave 2 (optional) — the A-side prime step.** §7.3. Not required by this wave's purpose; take it
only with a reason on the record. Gate: the same consumers, the membership's `PkgAt` gone, and the
axiom probe below.

**Wave 3 — bookkeeping.** §9: the probe re-pointed, the presentation re-rendered if a quoted line
moved, and the notes updated.

**Global checks.**

```bash
cd lean
grep -rn "hεq" FLTForHuman/ModularCurve/FunctionFieldGeneration/      # expected: empty
grep -rn "ε : LaurentSeries" FLTForHuman/ModularCurve/FunctionFieldGeneration/   # expected: empty
grep -rn "sorry" FLTForHuman/ModularCurve/FunctionFieldGeneration/    # expected: empty
```

plus the axiom probe (in `lean/tmp/`):

```lean
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Capstone
#print axioms ModularCurve.jqN_div_mem_modularFunctionField
#print axioms ModularCurve.functionFieldGeneration
-- both: [propext, Classical.choice, Quot.sound]
```

## 11. Risks, and the decisions behind the plan

* **Decision taken: §3 as written, the section variable (row 2 below).** Measured on the four
  `Generic/` modules (58 declarations, hand-classified by whether the *type* mentions both series
  rings):

  | design | generic two-field declarations | what it costs |
  |---|---|---|
  | today (ε parameter) | 48 + 54 `hεq` | — |
  | §3 as written (section variable) | **30 of 58** (`SlotProduct` 22: the pushed objects, the induction and the two seamed statements; `PrimeStep` 6; `PrimeNonmembership` 2; `SlotValue` 0) | nothing; each of the 30 is *lighter* than today (0 explicit args, 1 premise instead of 3 args and 2 premises) |
  | certificate (abstract the pushed polynomial) | ~8–12 | statements become conditional on a `B`-bundle — the pattern §7.3/§17 withdrew twice |
  | one-field theory + the banked dictionary (§6.2/§6.3) | **~7** (the dictionary's transport lemmas + the membership) | the theory loses `[Algebra κ κ']` entirely; the `ℚ` headline and `ℚ` non-membership get their package from `PkgAt jg M → PkgAt (jqModC K) M` (§6.2 (5.1)+(5.2), proved), so the `ℚ` route rests on the dictionary rather than on `Hall` directly |

  The user picked row 2 (30 being the plan's hand count), and the build lands at **34 of 58**:
  `SlotProduct` 24 (the plan said 22 — `coeffMap_jqModC'` is a new named bridge, and
  `pushedMinpolyAt_self` survives), `PrimeStep` 6 (as measured), `PrimeNonmembership` 4 (the
  plan said 2: the one-field statement was withdrawn, §5, so its seamed helpers stay two-field),
  `SlotValue` 0. The extra rows are §3's shape, not a design change: every declaration that reads
  the source minimal polynomial in the carrier is two-field by content, and the one-field rows are
  the slot side plus the two `seed_eval_zero` facts.
  On the readability criterion the last row wins and is now affordable; on "the `ℚ` route should not
  rest on a base-change lemma" the second row wins. §6.3 describes row 4's promotion path.
* **The carrier parameter goes; the two fields stay in the types.** This is the decision this file
  corrects. The alternative — a literally one-field theory with the package hypothesis at the
  carrier — is available (§6.2/§6.3) and is *not* taken: it moves the hypothesis off the source
  field, so `ℚ` would have to derive `PkgAt (jqModC K) M` before it could state its own headline.
  Nothing about `ℚ` needs that.
* **`[Algebra κ κ']` is a statement change.** Both instances are coefficient extensions, so nothing
  is lost; `hεq` becomes a theorem and `hε` becomes `coeffMap_jqModC`. A caller passing a
  non-coefficient carrier would break — there is none, and the types (`LaurentSeries κ` vs
  `LaurentSeries κ'`) already force the extension shape.
* **Two independent decisions.** *Shape* (carrier parameter → section variable) is this wave and is
  mechanical. *Descent argument* (B-side default, A-side optional, §7.2/§7.3) is orthogonal to it: the
  B-side proof needs nothing from the shape, and the shape needs nothing from the B-side. The plan
  takes the shape now and leaves the descent argument as it is; the earlier draft coupled them, which
  is what put §6's dictionary on the critical path.
* **The `ℚ` non-membership changes its route** (`hbase` at `K` from
  `jqNModC_prime_not_mem_adjoin_of_charZero`, then the free descent). If a reviewer objects to the
  `Degree/PrimeNonAdjoin` dependency in the FFG cone, the alternative is to state the
  non-membership in the pushed form too — same proof, one more seamed statement, no new dependency.
* **`sv`'s body changes.** Its type and pin text do not; `sv_eq_pin` is the transcription record, and
  it is a *proved* equality rather than a definitional one. If the checker turns out to compare
  `def` bodies rather than types, revert `sv` to the pin's inline body and keep `sv_eq_pin` as the
  bridge to `slotValue`, and report that.
* **Private/public.** The fold deletes declarations; the survivors keep their visibility.
  `exists_algHom_adjoin_of_isRoot` stays public (the non-membership and the prime step both use it);
  `slotValue_eq_TS`/`slotValue_inj` stay public for the same reason. If a declaration loses its last
  consumer, it goes.

---

## 12. Definition of done

- [x] `grep -rn "hεq"` over `FunctionFieldGeneration/` is empty.
- [x] `ε : LaurentSeries` does not occur (not in `FLTForHuman/` either); the two fields occur only
      as types, with `[Algebra κ κ']` a section variable in `Generic/SlotProduct`,
      `Generic/PrimeStep` and `Generic/PrimeNonmembership`. `Generic/SlotValue` needs no second
      field at all, so it carries no such variable.
- [x] `Generic/SlotValue` and the slot half of `Generic/SlotProduct` are stated at one field;
      `nomeMap` and `pushedMinpolyAt` are the only two-field definitions (`pushedMinpoly` is the
      diagonal of `pushedMinpolyAt` and is stated with it).
- [ ] `prime_notMem_levelField` stays **two-field** with the source condition `jg = jqModC κ` — the
      one-field form was withdrawn on landing (§5). The `C` instance is `(κ := κ' := K)`, the `ℚ`
      instance `(κ := ℚ) (κ' := K)` (both `hjg := rfl`).
- [x] `levelSeries_mem_levelField_mul_prime` keeps both fields in its conclusion and its `PkgAt`
      hypothesis (the B-side proof); it carries no `ε`, `hε`, `hεq`, only `hjg`.
- [x] No `Generic/BaseChange.lean` in this wave, and no base-change degree lemma anywhere: nothing
      the port cites needs one (§6.1). The dictionary is banked, not needed, in
      `Reserve/ModularCurve/FunctionFieldGeneration/BaseChange.lean`, with its traps and placement
      (§6.2).
- [x] Every module builds silently; the pinned statements' `check_port` counts are unchanged; the
      probe elaborates; `#print axioms` on the `ℚ` headlines is
      `[propext, Classical.choice, Quot.sound]`.
- [x] The §9 consumer list elaborates with its call sites unchanged, and
      `TOPIC-t19-any-field.md` §11 agrees with this file.

---

## 13. Landed record (2026-11-08)

**Shape.** `ε : LaurentSeries κ →+* LaurentSeries κ'` is gone from the whole tree (0 occurrences of
`ε : LaurentSeries` in `FLTForHuman/` and `Reserve/`), and `hεq` from `FunctionFieldGeneration/`
(0 occurrences). The carrier is `σ := coeffMap (algebraMap κ κ')`, a `local notation` in each
two-field module, over a section variable `[Algebra κ κ']`. The two source facts became theorems
`coeffMap_qExpand` / `coeffMap_jqModC`, and the j-series condition `jg = jqModC κ` is the one premise
threaded through (at `κ = ℚ` and at the `C` layer it is `rfl`).

**What moved, module by module.**

| module | declarations | two-field | what changed |
|---|---|---|---|
| `Generic/SlotValue.lean` | 8 | 0 | `slotValue` at one field; the premise is `hjg : jg = jqModC κ` |
| `Generic/SlotProduct.lean` | 32 | 24 | `nomeMap`/`pushedMinpoly`/`pushedMinpolyAt` take `jg` only; `slotPolynomial` at one field; `map_levelSeries` deleted (the source relation is now `seed_eval_zero` at one field, from `phiAtSeed_jqNModC_eval` at `κ`); `coeffMap_jqModC'` added, the one named bridge from `hjg` to `σ jg = jqModC κ'` |
| `Generic/PrimeStep.lean` | 14 | 6 | `levelNomeMap` at `jg` only; `hιS`-style steps are `coeffMap_qExpand` + `qExpand_qExpand` |
| `Generic/PrimeNonmembership.lean` | 4 | 4 | as §5 corrected; `hιS` is proved inside `map_mem_fieldRange` instead of being a hypothesis |
| `Rat/SlotProduct.lean` | 3 | — | the two `rfl` transcriptions keep their names and lose the carrier (`pushedMinpoly (κ' := K) jq M`); the headline passes `hjg := rfl` |
| `CharP/SlotProduct.lean` | 2 | — | the identity algebra is collapsed by the new `coeffMap_id_ringHom` (`Defs/Laurent.lean`) |
| `CharP/Nonmembership.lean` | 1 | — | `prime_notMem_levelField (κ' := K) (jqModC K) rfl …` |
| flat `SlotProduct.lean` | — | — | `sv K ζ a b = slotValue (coeffEmb K jq) ζ a b` (still the pin's `if` body); `sv_eq_TS`/`sv_inj`/`sv_inj_slot` at `hjg := coeffEmb_jq`; `map_qExpand_minpoly_eq` at `(κ' := K)` |
| `Descent.lean`, `Nonmembership.lean` | — | — | one call site each, `(κ' := CyclotomicField (M * p) ℚ)` / `(κ' := K)`, `hjg := rfl` |
| `spec/GenericProbe.lean` | — | — | re-pointed: `κ = κ' = ZMod 5`, no carrier arguments |

**Gates run.**

| gate | result |
|---|---|
| `lake build` of the four `Generic/` modules, the five `ℚ`/`C` modules, `Descent`, `Capstone` | green, 0 warnings |
| the §9 consumer cone (`TwoPrimeSeparation`, `ModularPolynomialExistence`, `ModularPolynomialUniquenessIrreducible`, `Degree/Relfinrank`, `ModularPolynomialLeadingCoeff`, `X1/FunctionFieldInclusion`, `HeckeCommuteBar`, `FieldTheory/AdjoinTower`) | green |
| `Reserve.ModularCurve.FunctionFieldGeneration.SlotProductAnyField` | green (it uses only `SlotValues`, not the carrier API) |
| `lake env lean spec/GenericProbe.lean` | green |
| `check_port --force` on the flat `SlotProduct` | 7 ok / 0 mismatch / 0 missing / 1 own — unchanged |
| `check_port --changed` | 12009 ok, 0 mismatch; the one new public declaration (`coeffMap_id_ringHom`) is registered `own:` in `decl_markers.tsv` |
| `#print axioms` on `jqN_div_mem_modularFunctionField`, `functionFieldGeneration`, `jqN_prime_not_mem_full`, `minpoly_jqN_map_eq_prod_slots` | `[propext, Classical.choice, Quot.sound]` |
| `grep hεq`, `grep "ε : LaurentSeries"`, `grep sorry` | empty / empty / empty |

**Not done, deliberately.** Wave 2 (§7.3, the A-side prime step) is not taken — no reason was
recorded for it. `presentation/capstone.json` is untouched: `Capstone` did not change, and the
`line` fields it carries are already the *pin's* line numbers, not this tree's.
