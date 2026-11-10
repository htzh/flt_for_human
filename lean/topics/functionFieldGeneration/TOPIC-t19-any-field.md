# TOPIC — T19 as one any-field theory

Status: **planned**; written 2026-11-06, revised the same day after review (see §0), and revised
again on 2026-11-08 for the carrier fold — **§11 supersedes the carrier *parameter* used in §0.2,
§2, §3, §5 and §9.3**; those sections are kept as the record of the built state. Owner:
whoever picks up the FFG refactor next.
Companions: `TOPIC-ffg-refactor.md` (the plan of record for the fold and the prime step: where this
note and it disagree, its §1–§12 are normative), `TOPIC-ffg-refactor.md` § *The T19 `C`-layer island
is on the shelf* (the record of the shelving and the do-not-re-port rule), `Reserve/README.md`
§ *The CL4 island*.

The goal is one proof of T19 — the slot product, its non-membership corollary, and the level-degree
package they run on — parameterized by the coefficient field, with the `ℚ` and the arbitrary-field
statements as instantiations of it. The `ℚ` proof bodies are the ones that stay: they are the live,
refactored ones, and the shelved `C` twin is the instance the parameterization has to be able to
reproduce. No public statement moves (see §0.8). This note records the evidence for the plan, the
exact shape, the traps, and the order of work.

## 0. What the review changed

The first draft abstracted five objects — the base field `F`, the series ring `A`, the working ring
`L`, the coefficient map `ε` and a level-series function `J : ℕ → A` — and claimed both
instantiations are definitional. `A` and `L` were the wrong abstraction (`qExpand` and `qTwist` are
endomorphisms of `LaurentSeries κ`, so the parameter is the coefficient field), and `J` is not
needed at all. Every correction *shrinks* the master. The calls below are the ones to hold to;
§3–§5 spell them out.

1. **Two coefficient fields, not two series rings.** `qExpand (R)` and `qTwist (u : Rˣ)` are
   endomorphisms of `LaurentSeries R` parameterized by the *coefficient ring*, and the unit of
   `qTwist` lives in that ring (`Defs/Laurent.lean:80`, `Defs/Twist.lean:54`). So the master is
   parameterized by `κ` and `κ'` and abbreviates `A := LaurentSeries κ`, `L := LaurentSeries κ'`;
   it cannot be parameterized by `A` and `L` directly.
2. **The twist sits after `ε`.** In the draft's slot value the twist acted in `A`, so the `ℚ` instance
   would need a root of unity in `ℚ`, i.e. `M ≤ 2`. The slot value is
   `qExpand κ' (a * a) (qTwist (ζ ^ (b * a)) (ε jg))` — today's `sv` with `coeffEmb ↦ ε`.
3. **No `J`.** Every use of the level series is under a `NeZero` binder, so the master writes it
   inline as `qExpand κ N jg` (as `jqN` does). A total `J : ℕ → A` would force
   `fun d => if d = 0 then 0 else jqN d`, which is *not* definitionally `jqN` and would put a
   `dif_neg` rewrite in every instantiation, including `sv_top`.
4. **`F` is not a parameter.** In both instances the base field is the field the j-series generates
   (`ℚ⟮jq⟯` and `K⟮jqModC K⟯` are both `adjoin κ {jg}`). Deriving it removes an object, makes
   hypothesis (ε jg = jqModC κ') the only j-series hypothesis, and makes the `Pkg K M` trap (§4)
   impossible by construction.
5. **No `Function.Injective ε`.** The `ℚ` body's injectivities are `RingHom.injective` from a field
   domain (the IntermediateField inclusion, and the conjugate map `ψ₁`) and `TS_injective` /
   `qExpand` injectivity in the *target*; none of them is injectivity of the coefficient map.
6. **The generation clause is the relative-adjoin equality, and the package is one predicate.**
   The master's hypothesis must be field-generic, so it is `PkgAt`; at `ℚ` the package is `Hall`,
   whose conjuncts `Tight`/`Gen` are the `ℚ` spellings — so the only conversion is `hall_pkgAt`.
   The pin's inline `finrank ∧ modularFunctionField d = modularFunctionFieldFull d` is the same
   predicate written out, not a second statement, and is not carried (§5).
7. **The master's splitting input is the any-field twin.** The `ℚ` body calls
   `PhiGen.splits_prime_at_slot`, which spends `[Algebra ℚ K]`; an arbitrary `κ'` does not have it.
   The master uses `PhiGen.splits_prime_at_slot_of_isPrimitiveRoot` (`PhiGenSplitsAnyField.lean`,
   `[Field K]` only), which is *more general*: it takes the primitive root of order `p` directly, so
   the `ℚ` instance passes `ζ ^ (M / p)`.
8. **One theorem, one statement.** The ℚ layer keeps the statements the rest of the tree cites
   (`minpoly_jqN_map_eq_prod_slots`, `jqN_*_not_mem_*`, `sv`, …), each as a delegation to the theory;
   our own declarations (`SlotProductAt`, `rval_aux`, `sv_inj_slot`) move into the theory, where they
   are stated at `κ` instead of `ℚ`. A hypothesis is not carried in two spellings: the package is one
   predicate (`PkgAt`), and its `ℚ` conjunct spellings `Tight`/`Gen`/`Hall` are abbreviations, with
   `Hall → PkgAt` the only bridge. Whether a consumer's call site needs a line changed is a separate,
   deferred question (§5).
9. **Scope: the slot product is wave 1, the prime non-membership wave 2.** The prime-power tower
   `jqN_pow_not_mem_adjoin_full` is out of scope (§8).

The FFG refactor's conventions decide how much of this is allowed to move: name a declaration by its
mathematical role, delete a port device rather than keep two spellings, never carry one theorem in
two shapes. Within FFG the API may therefore move — hypothesis shape, abstraction, module split — as
long as the mathematics is clearer. Consumers outside FFG are *not* a design constraint (their call
sites are one-line changes and can be made when the mathematics is settled); what they do constrain
is that the ℚ theorem must still *be* the theorem they cite, which it is, being the instance of the
general one.

The signature, the slot value and both instance conclusions below were elaborated on a scratch module
(2026-11-06): the two conclusions and `sv`'s instance are `rfl`, the finrank half of `PkgAt` is
`rfl` against `Tight`, and the generation half needs `extendScalars_adjoin` (§4).

## 1. Why now

T19 exists twice: `FunctionFieldGeneration/SlotProduct.lean` over a `ℚ`-algebra (1065 lines, the
refactored form) and the `C`-layer twin `SlotProductAnyField` (1359 lines, on the shelf in
`Reserve/ModularCurve/FunctionFieldGeneration/`, with `MffCMulPrime` and `PrimePowerStepAnyField`
below it and `Reserve/ModularCurve/Degree/FinrankAdjoinJqNModCDead.lean`, whose "Dead" names its
abandoned *route* — it also holds `finrank_adjoin_jqNModC_eq_dedekindPsi_of_socket`, which this very
section counts in the D-S closure). §1–§2 are
the historical measurement that motivates the parameter; the arrangement in §6.1 treats that island
as deleted, so nothing below depends on it being in the tree.

The twin is not an abandoned route. It is the **prelude of the char-`p` route**, and the pin's own
route to the main theorem:

```
package_of_socket → finrank_adjoin_jqNModC_eq_dedekindPsi_of_socket
  → modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charP_pos
  → modularFunctionFieldC_eq_modularFunctionFieldFullC
  → exists_jZeroGoodReductionSpecialization_doorPredicates
  → mazurQuotientSpecialization_heckeModuleBar → mazurStepThree_not_inZeroComponentAt
  → FreyPackage.frey_no_cofixed_large → … → fermat_last_theorem
```

Pin consumers: `package_of_socket` 2, `…_of_socket` 9, `…_of_charZero` 3
(`tools/deps/explore.py <node>` reproduces this; the dependency tools live under the untracked
`tools/`).

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
`…_of_charZero` specialization is FLT-only. In *this* port the route stops at `_of_socket`: every
declaration above it is unported, which is why the island is uncited here and was shelved. So the
port owns the prelude of a route it has not resumed — and the `ℚ` statement of the same theorem is
what `Descent` and `ModularPolynomialLeadingCoeff` cite today. Two statement sets, one theorem: the
duplication has to be removed by a parameter, not by picking a winner.

## 2. What is actually duplicated

Measured with `tools/deps` (`shapes.py`, `dedup.py`):

* 19 declarations occur under the same name in both modules once the `C` suffix is normalized
  (`sv`/`svC`, `SlotProductAt`/`SlotProductAtC`, `rval_aux`/`rval_auxC`, the `isRoot_map_minpoly_sv*`
  family, `phiAtSeed_slot_factor`, `qExpand_qTwist_slot_eq_sv`, `finrank_adjoin_mul_dedekindPsi`,
  `nodup_slotValues_sv`, `map_qExpand_minpoly_eq`, …); their *statements* differ only in the base
  field — `minpoly ℚ⟮jq⟯ (jqN M)` against `minpoly K⟮jqModC K⟯ (jqNModC K M)`, and the `hall`
  conjunction over the corresponding field.
* Only `sv_eq_TS`, `TS_congr'`, `sv_inj` are shape-identical across the two *pin* layers; in the
  port `sv_inj_slot`, `nodup_slotValues_sv` and `nodup_slotValues_qExpand` join them. `dedup.py`
  reports 6 name clusters / 89 removable lines — and misses everything else, because the
  difference sits inside the hypothesis *types*, not in instance arguments.
* The induction body (`rval_aux`, the `isRoot_map_minpoly_sv*` family, `phiAtSeed_slot_factor`,
  `qExpand_qTwist_slot_eq_sv`, `sv_ne_image_of_dvd`, `finrank_adjoin_mul_dedekindPsi`) is the same
  proof twice.

The twin's own header states the residual duplication and its cause: the `sv` block is re-declared
there as `svC`/`svC_eq_TS`/`svC_inj`/`svC_inj_slot` because "the `ℚ` copy in `SlotProduct.lean` is
`[Algebra ℚ K]`-bound and its `sv_eq`/`sv_top` statements name `coeffEmb K jq`; unifying them would
edit a landed module's statements". Under the master both statements are preserved and the bodies
become the same definition, so this residue is exactly what the parameter removes.

Conclusion: parameterize, do not re-derive. The duplicate scan's 89 lines are the visible tip; the point of
this note is the other ~1200.

## 3. The master statement

The `ℚ` proof shape survives verbatim; four objects are abstracted — the two coefficient fields, the
coefficient map, and the j-series:

```lean
variable {κ κ' : Type*} [Field κ] [Field κ']

/-- the `N`-th level series `j(q ^ N)`, read in the coefficient field -/
def levelSeries (jg : LaurentSeries κ) (N : ℕ) [NeZero N] : LaurentSeries κ := qExpand κ N jg

/-- the base field is **not** a parameter: it is the field the j-series generates -/
abbrev baseField (jg : LaurentSeries κ) : IntermediateField κ (LaurentSeries κ) :=
  IntermediateField.adjoin κ ({jg} : Set (LaurentSeries κ))

/-- the slot value (singular; the multiset API `slotValues` in `SlotValues.lean` is unchanged):
`ε` carries the j-series up, then the twist and the `q`-expansion act in the working
coefficient field -/
def slotValue (ε : LaurentSeries κ →+* LaurentSeries κ') (jg : LaurentSeries κ)
    (ζ : κ'ˣ) (a b : ℕ) : LaurentSeries κ' :=
  if h : a = 0 then 0 else
    letI : NeZero a := ⟨h⟩
    qExpand κ' (a * a) (qTwist (ζ ^ (b * a)) (ε jg))

def SlotProductAt (ε : LaurentSeries κ →+* LaurentSeries κ') (jg : LaurentSeries κ)
    (M : ℕ) [NeZero M] (ζ : κ'ˣ) : Prop :=
  IsPrimitiveRoot (ζ : κ') M → PkgAt jg M →
    (minpoly (baseField jg) (levelSeries jg M)).map
        ((ε.comp (qExpand κ M)).comp (algebraMap (baseField jg) (LaurentSeries κ)))
      = ∏ a ∈ M.divisors, ∏ b ∈ (range (M / a)).filter (gcd (gcd a b) (M / a) = 1),
          (X - C (slotValue ε jg ζ a b))
```

The master's hypotheses — all supplied per instance, none of them new mathematics:

1. `ε jg = jqModC κ'` — the generator is carried to the working field's j-series
   (`coeffEmb_jq` in one instance, `rfl` in the other);
2. `∀ N [NeZero N] x, ε (qExpand κ N x) = qExpand κ' N (ε x)` — the coefficient map commutes with
   level raising (`coeffEmb_qExpand` in one instance, `rfl` in the other);
3. `PkgAt jg M` — the level-degree package (§4).

The conclusion is today's `minpoly_jqN_map_eq_prod_slots` statement with those four objects
replaced: at the `ℚ` instance the mapped minimal polynomial is `rfl`-equal to
`(minpoly ℚ⟮jq⟯ (jqN M)).map (((coeffEmb K).comp (qExpand ℚ M)).comp (algebraMap ℚ⟮jq⟯ _))` (§5).

Two design notes:

* **`Algebra (baseField jg) (LaurentSeries κ')` is not in the statement.** The *proof* needs the
  working field as an `F`-algebra (the conjugate `ψ₁ : ↥F⟮…⟯ →ₐ[F] LaurentSeries K`, `IsRoot` of
  the pushed polynomial, the degree count). Today's code threads it through three step lemmas as an
  instance argument plus the compatibility equation `halg : algebraMap _ _ = …`
  (`exists_algHom_adjoin_of_isRoot` at `SlotProduct.lean:511`, `map_mem_fieldRange` and
  `eval_map_eq_of_mem_slotValues` in `Nonmembership`), and the callers install it with
  `letI := (…).toAlgebra` (`SlotProduct.lean:849`, `Nonmembership.lean:387`). The master keeps that
  style — same three lemmas, same two install sites; the headline does not mention the instance, so
  its statement stays the pinned text.
* **The level series is stated under `[NeZero]`, never totalized** (§0.3). This is the same
  discipline as `sv`'s `if h : a = 0` form, and it is what keeps the instantiation definitional.

## 4. `PkgAt` — vocabulary, and why it must be generalized

The package "for every `d ∣ M`, `finrank` at `d` is `ψ(d)` and the level-`d` field is generated by
the `j`-series at the divisors of `d`" is written three times today:

| today | site | after |
|---|---|---|
| inline conjunction inside `SlotProductAt` | `SlotProduct.lean:310–318` | `PkgAt jg M` |
| `abbrev Hall N := ∀ d ∣ N, Tight d ∧ Gen d` | `Defs/Fields.lean:237` | unchanged (ℚ vocabulary) |
| `hallM : Hall M` / `h : Hall N` | `Nonmembership.lean:367`, `:459`, `DegreeStep.lean:522`, `Capstone.lean:55`, `:92`, `:112`, `Descent.lean:303`, `:390`, `:454` | unchanged |

`Pkg` as it stands (`Defs/JqCoeff.lean:253`) hardcodes `adjoin K {jqModC K}`, i.e. the package at
the **big** field. `PkgAt` is the same package relative to the base field the j-series generates:

```lean
abbrev PkgAt (jg : LaurentSeries κ) (M : ℕ) : Prop :=
  ∀ d : ℕ, d ∣ M → ∀ [NeZero d],
    Module.finrank (baseField jg)
        (IntermediateField.adjoin (baseField jg) ({levelSeries jg d} : Set (LaurentSeries κ)))
      = dedekindPsi d
    ∧ IntermediateField.adjoin (baseField jg) ({levelSeries jg d} : Set (LaurentSeries κ))
      = IntermediateField.adjoin (baseField jg)
          {x : LaurentSeries κ | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ d ∧ x = levelSeries jg d'}
```

How the three spellings relate — measured by elaboration (2026-11-06), not by eye:

* the **finrank half** is `rfl` against `Tight` (`finrank ℚ⟮jq⟯ (adjoin ℚ⟮jq⟯ {jqN d}) = ψ d`).
  A `simp only [Tight, …]` that tries to unfold `Tight` *in place* trips over the instance paths
  inside `Module.finrank`; the clause is definitionally equal, so close it with the term directly
  rather than through `simp`.
* the **generation half is not `rfl`** in either instance, for either spelling: `Gen d` is a
  statement about the named fields `modularFunctionField` / `modularFunctionFieldFull`, `Pkg`'s is
  about `modularFunctionFieldC K d`, and `PkgAt`'s is a relative adjoin. Each conversion is one
  lemma of ~10 lines with `IntermediateField.extendScalars_adjoin` — the tool `mem_adjoin_jqN_of_mem_mff`
  already uses (`SlotProduct.lean:203–230`) — plus the `Set.ext` for the `∃ (_ : NeZero d')` binder.
  So the two instances each need one bridge:
  `hall_pkgAt : Hall N → PkgAt jq N` and `pkg_pkgAt : Pkg K N → PkgAt (jqModC K) N`.
* the **generation clause stays an equality**, not the inclusion the body spends. The body only
  needs "for `d' ∣ d`, `levelSeries d'` lies in `adjoin F {levelSeries d}`"
  (`finrank_adjoin_mul_dedekindPsi` at `SlotProduct.lean:390–403`), but the equality is what both
  layers actually prove and what the term "level-degree package" means; weakening the hypothesis
  would buy a couple of rewrites and cost the hypothesis its mathematical content.

**Trap — do not state the master's hypothesis as `Pkg K M`.** `Pkg K M` is the package at
`K⟮jqModC K⟯`; the `ℚ` consumer has the package at `ℚ⟮jq⟯` and applying the headline at
`K = ℚ(ζ_N)` (`ModularPolynomialLeadingCoeff.lean:188`) would have to *prove* the degree clause over
`K`, i.e. geometric irreducibility of the modular equation, which is not in the tree and is not
wanted. Deriving the base field as `baseField jg` is what makes this trap unreachable: in the `ℚ`
instance it *is* `ℚ⟮jq⟯`, in the `C` instance it *is* `K⟮jqModC K⟯`, and neither can drift. If a
third consumer ever has the package at a strictly larger base, add `F` back as a parameter then —
with the same warning.

## 5. The two instantiations

| | `κ` | `κ'` | `ε` | `jg` | `baseField jg` |
|---|---|---|---|---|---|
| `ℚ` (today's statements) | `ℚ` | `K` | `coeffEmb K` | `jq` | `ℚ⟮jq⟯` |
| any field (the shelved statements) | `K` | `K` | `RingHom.id` | `jqModC K` | `K⟮jqModC K⟯` |

Both are literal, and what must hold at each of the four places the `ℚ` side lands on:

* `sv K ζ a b = slotValue (coeffEmb K) jq ζ a b` — `rfl` (same `if` form, `coeffEmb K jq` for `ε jg`).
  So `def sv` keeps its signature and its body becomes the instance.
* the `ℚ` headline's *conclusion* is the master's conclusion at the `ℚ` instance — `rfl`
  (`ℚ⟮jq⟯` is the macro `adjoin ℚ {jq}`, and `jqN M` is `qExpand ℚ M jq`).
* the same holds for a future any-field instance (`jqModC K` for `ε jg`, `RingHom.id` dropped) —
  `rfl` again, which is why `CharP/` is a few lines of data rather than a second development.
* hypothesis (1) is `coeffEmb_jq` at the `ℚ` instance and `rfl` at the any-field one; hypothesis
  (2) is `coeffEmb_qExpand` and `rfl`.

The `ℚ` layer states the same theorems at `ℚ`, each a delegation:

* `sv`, `sv_eq_TS`, `sv_inj`, `sv_top`, `map_qExpand_minpoly_eq`, `mem_adjoin_jqN_of_mem_mff`
  — the `ℚ` spellings of the theory's slot-value and level lemmas;
* `minpoly_jqN_map_eq_prod_slots` — the theory's headline at `(coeffEmb K, jq)`, hypothesis `Hall M`
  (the `ℚ` spelling of the package), so `hall_pkgAt` is the only conversion;
* `Nonmembership`'s `jqN_prime_not_mem_adjoin`, `jqN_prime_not_mem_full` — the same at the prime.

One delegation is not a one-liner: `sv_top`. The generic `slotValue_top` computes
`qExpand κ' (M * M) (ε jg)` — the direct form — while the `ℚ` statement is the level form
`coeffEmb K (qExpand ℚ M (jqN M))`; `coeffEmb_qExpand` and `qExpand_qExpand` bridge them. That is the
theory not having inherited a `ℚ` spelling, and the surface paying two rewrites for it.

Two spellings are deliberately *not* kept. `SlotProductAt`/`rval_aux` are the theory's predicate and
induction, so `ℚ` mentions them only through the headline. And the pin's inline `finrank ∧
modularFunctionField d = modularFunctionFieldFull d` is the same predicate as `Hall` written out —
one hypothesis object, not two statements.

**Consumers are deferred.** `Descent.lean:331` and `ModularPolynomialLeadingCoeff.lean:188` pass
`hallM` and the pair `⟨finrank_adjoin_jqN_eq_dedekindPsi d, modularFunctionField_eq_full d⟩`; the
first still works, the second becomes `hall_pkgAt (fun d hd _ => that pair)`. One line each, to be
made when this lands — not a reason to keep a second statement alive now.

The second instance is `CharP/` (§6.1b): its slot-product half and its prime non-membership are both
in the tree as delegations to this theory — the pinned any-field headlines, statement-checked
against their wrappers — and its prime step, `jqNModC_mem_modularFunctionFieldC_mul_prime`, is now
the `ℚ` descent's own theorem generalized (`Generic/PrimeStep.lean`, wave 6). That prime step is back
in the tree as `CharP/PrimeStep.lean` (moved out of the shelf 2026-11-08; the name mirrors
`Generic/PrimeStep.lean`), so all four C-layer modules now sit together. What has no
replacement on either side is the *socket*: `PrimePowerStepAnyField`'s `eFull` device, the
prime-power tower and `package_of_socket` are transcribed rather than re-derived (§6.1, §8.1).

## 6. Order of work

### 6.1 The arrangement (designed from scratch)

Layers top-down by generality. Each layer's declarations are at that layer's generality, and each
layer's hypotheses are exactly what that layer can prove — that is the whole design rule; no tooling
argument is involved.

| layer | content | generality |
|---|---|---|
| **definitions** | `qExpand`, `qTwist`, `TS`, `jqModC`, `jqNModC`, `Φ`, `ψ` | general coefficient field/ring |
| **theory** | base field from the j-series, level series, the level package (as a hypothesis), slot values, the slot product, the prime non-membership | `κ` |
| **instance** | one base field's data (`ε`, `jg`) and the bridge from that layer's own package spelling | `ℚ` (later `CharP`) |
| **`ℚ` mathematics** | `Tight`/`Gen`/`Hall` and `hall_all`, the `Φ_p` tower, the modular-polynomial link — the things only `ℚ` has | `ℚ` only |
| **assembly** | the capstone: the seven statements imply the function-field theorem | `ℚ` only |

The directories state the scope; the flat modules are the `ℚ` theorems consumers see.

```text
FunctionFieldGeneration/
  Generic/                    ← theory
    LevelPackage.lean         levelSeries, baseField, levelField, degreeAt, generatedAt, PkgAt
                              + isIntegral_levelSeries, natDegree_minpoly_levelSeries
    SlotValues.lean           the multiset API (slotValues, card, prod, nodup) — unchanged, moved
    SlotValue.lean            slotValue, slotValue_eq_TS, slotValue_inj_slot
    SlotProduct.lean          SlotProductAt, the induction, the generic headline
  Rat/                        ← instance data + ℚ-only mathematics
    LevelPackage.lean         Tight, Gen, Hall (out of Defs/Fields.lean: ℚ vocabulary, and a Def_*
                              module should not host proof-bearing invariants) + hall_pkgAt
    PowerTower.lean           the Φ_p chain — the one big ℚ-only proof in this region
  CharP/                      ← empty until the char-p route resumes; written fresh
  SlotProduct.lean            the ℚ theorems: headline + slot lemmas, each a delegation
  Nonmembership.lean          the ℚ theorems at the prime (+ the tower, ℚ-only)
  Target, Collapse, Descent, DegreeStep, Generation, Capstone, ModularPolynomialExistence
```

Four rules, each with its mathematical reason:

1. **One definition per object, at the most general field.** `jq`/`jqModC`, `jqN`/`jqNModC`,
   `modularFunctionField`/`modularFunctionFieldC`, `sv`/`svC`, `Pkg`/the inline conjunction are
   accretion, not design — every pair is `rfl`-equal already (`jqModC_rat`,
   `modularFunctionFieldC_rat` are `rfl`). Define at the general field; the `ℚ` name is an
   abbreviation. This is where the twin-lemma families come from, and it is independent of T19.
2. **One theorem per mathematical content, at the most general hypothesis.** T19's content is "the
   level package at the base field determines the slot product". The theory states it at `κ`; the
   `ℚ` layer states *the same theorem* with `ε := coeffEmb K, jg := jq`. It is not a second theorem
   with the package written out in `ℚ` vocabulary — that is the same predicate in a different
   spelling (`Tight`, `Gen`, `Hall` are its conjuncts' abbreviations), and carrying both is how the
   current duplication started.
3. **Every hypothesis is spent.** An unspent one means the abstraction was guessed rather than
   checked — the first draft's `Function.Injective ε` was exactly that (§0.5). The converse test: if
   a proof step needs a `ℚ` fact, the statement is at the wrong generality, and the fix is in the
   statement, not a hypothesis.
4. **Dependence follows the mathematics**: definitions → theory → instance → `ℚ` mathematics →
   assembly. Nothing points back up; the three pinned lemmas the induction body uses
   (`map_qExpand_minpoly_eq`, `mem_adjoin_jqN_of_mem_mff`, `sv_inj`) are the `ℚ` spellings of theory
   lemmas, so they sit *below* the induction, and the `ℚ` statements that name them are
   delegations.

**`Reserve` is not dead, and the arrangement has to say what it is *for*.** "Nothing imports it" is
vacuous: the rule *is* that `FLTForHuman` never imports `Reserve`, so the check is a tautology and
says nothing about whether the content is needed. The criterion that does work is the consumer — what
does a future FLT consumer need that the live tree does not have? By that test the island splits
three ways:

| part | fate |
|---|---|
| the slot product and prime non-membership (`SlotProductAnyField`'s core) | **deleted** (2026-11-08): both headlines are live in `CharP/SlotProduct.lean` and `CharP/Nonmembership.lean`, wired to the same pin files and statement-checked; only the retired inline `C`-layer induction went with it |
| `MffCMulPrime` (the `C` prime step) | **restored** (2026-11-08) as `CharP/PrimeStep.lean`: the pin's C-layer headline, a 68-line delegation to the general theorem (`Generic/PrimeStep.lean`); its `S_` engine stays retired |
| the socket degree half — `PrimePowerStepAnyField` (the `eFull` device, the prime-power tower, `package_of_socket`) | **restored** (2026-11-08) as `CharP/PrimePowerStep.lean`, with its degree half at `Degree/FinrankAdjoinJqNModC.lean`; no replacement was found for it — the `eFull` device runs the step with an arbitrary bound and the package is *conditional* there, so it is a different theorem proved by a different argument (§8.1) |
| about eight field-generic declarations (`relfinrank_adjoin_insert*`, `jqNModC_injective`, `qTwist_jqModC_eq_TS`, `mem_adjoin_of_mem`, `phiAtSeed_map_algebraMap`, `natDegree_minpoly_le_of_phiAtSeed_root`) | **paid (2026-11-08)**: the six content-bearing and base-case ones (the insertion identity, the `phiAtSeed` map/`aeval` bridges and the two `minpoly`-degree bounds) are in `Defs/PhiAtSlot.lean`, statement-checked against the two `C`-layer `S_` files they come from; the adapter wrappers stay in `CharP/PrimePowerStep.lean` with their only consumer |

The consumer test also showed how much of the D-S route existed *only* on the shelf:
`finrank_adjoin_jqNModC_eq_dedekindPsi_of_socket` was nowhere else, `package_of_socket` only there —
both are back in the tree now, and the two nodes above them
(`modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charP_pos`,
`exists_jZeroGoodReductionSpecialization_doorPredicates`) are absent from it entirely: that is
the unported tail, not shelf material.

The CL4 island closed on 2026-11-08: `Reserve/README.md` records the disposition of each of its
files, and the misplaced-declaration debt is settled — the six went to `Defs/PhiAtSlot.lean`,
the adapters stayed where the degree proof reads them.

So the deferral was right, for a reason other than inertness: **the shelf was the source and the
inventory for `CharP/`, not dead code.** "Written fresh" (§5) therefore meant fresh as *modules* and
free of compat debt; the degree half was transcribed, not re-derived. With the island closed
(2026-11-08) the one build target and the forward coupling to `SlotProduct`'s API (it borrows
`TS_congr'` and `card_slotFilter_eq_dedekindPsi`) are ordinary in-tree dependencies. The
`C`-suffixed shadow block went with it (it existed only because Lean refuses a `private`
declaration whose public name is imported).

That removes the `C`-suffixed shadow block (it existed only because Lean refuses a `private`
declaration whose public name is imported) and leaves the second instance unverifiable — so it is
replaced by a *specification*: (a) the char-`p` instance's hypothesis list written in the theory's
header — what it needs that the generic layer does not give (the socket's degree package, the `C`-side
base non-membership; `PhiGenSplitsAnyField` is already generic); (b) a compile-time probe that
`#check`s the theory's declarations at a field with **no `ℚ`-algebra structure** (`ZMod 5` say),
which fails the moment an `[Algebra ℚ κ']` or a `coeffEmb` leaks into a section variable; (c) when
the route resumes, `CharP/` is written fresh against the theory.

### 6.1b The skeleton that is in the tree, and the first port

Written statements-first, then proved in workordered stages — and now **complete**: five modules,
**zero `sorry`**, each building with 0 errors and 0 warnings, and eleven `#print axioms` checks (the
induction, the two headlines, the bridges, the slot value, the package consequences) all
`[propext, Classical.choice, Quot.sound]`. `Generic/SlotProduct` is 995 lines with 18 `private`
helpers; the public surface is the nine declarations of §6.1c–§6.1d. `spec/GenericProbe.lean` still
elaborates at `ZMod 5`, so no `ℚ` fact leaked into a statement or an instance argument.

| module | content |
|---|---|
| `Generic/LevelPackage.lean` | `levelSeries`, `baseField`, `levelField`, `degreeAt`, `generatedAt`, `PkgAt`; `isIntegral_levelSeries`, `natDegree_minpoly_levelSeries` |
| `Generic/SlotValue.lean` | `slotValue`; `slotValue_eq_TS`, `slotValue_inj_slot` (the defining equation, the raw-bound injection, the distinguished slot and the distinctness corollary are `private`) |
| `Generic/SlotProduct.lean` | `nomeMap`, `pushedMinpoly`, `slotPolynomial`, `SlotProductAt`; `slotProductInduction`, `pushedMinpoly_eq_slotPolynomial` |
| `Rat/LevelPackage.lean` | `gen_iff_levelField`, `hall_pkgAt` |
| `Rat/SlotProduct.lean` | `pushedMinpoly_rat` (`rfl`), `minpoly_eq_prod_slotValues` (the `ℚ` headline at `Hall M`) |
| `CharP/LevelPackage.lean` | `modularFunctionFieldC_iff_generatedAt`, `pkg_pkgAt` (the `C` layer's package spelling is `Pkg K M`) |
| `CharP/SlotProduct.lean` | `pushedMinpoly_anyField` (`rfl`), `minpoly_jqNModC_map_eq_prod_slots` (the pinned any-field headline) |
| `Generic/PrimeNonmembership.lean` | `prime_notMem_levelField`; three `private` helpers (`nodup_slotValues_expanded`, `map_mem_fieldRange`, `eval_map_eq_of_mem_slotValues`) |
| `CharP/Nonmembership.lean` | `jqNModC_prime_not_mem_fullC` (the pinned any-field prime non-membership) |
| `Generic/PrimeStep.lean` | `levelSeries_mem_levelField_mul_prime` (the prime step); `levelNomeMap`, two producers, the index facts and the transport as `private` |
| `Rat/Descent` / `CharP` | the two instances of the prime step, each a delegation (`Descent.lean` 473 → 179 lines, `Reserve/.../MffCMulPrime.lean` 249 → 68) |

Two checks, both done:

* every module builds (`lake build` on each: 0 errors, only the `sorry` warnings), and
  `Rat/SlotProduct` elaborating is itself the statement-level check that the theory instantiates at
  `(κ := ℚ, κ' := K, ε := coeffEmb K, jg := jq)` with `PkgAt` replaced by `Hall`;
* `spec/GenericProbe.lean` instantiates and *applies* the whole generic layer at `ZMod 5` — a field
  of characteristic five, hence with no `ℚ`-algebra structure. It elaborates, so no `ℚ` fact has
  leaked into a section variable, a statement or an instance argument. That probe is the
  compile-time stand-in for the absent second instance (§6.1).

Notes on the skeleton's shape:

* `slotValue_top` is stated as the honest computation `qExpand κ' (M * M) (ε jg)`, and the first
  port confirmed that this is the *right* statement rather than a weakened one: the `ℚ` `sv_top` is a
  level-form spelling proved through `iota_jqN` and `TS_congr'`, and it is the `ℚ` layer that will
  re-derive that form, not the theory that should inherit it (§5).
* The prime non-membership was once written as a one-theorem module and deleted (§6.1d); it is back
  with the three helpers its proof needs (§6.2 wave 4).
* `SlotValues.lean` is not moved: it is already generic (`slotValues`, its cardinality, the product,
  the nodup criterion are functions of the multiset, not of the target field), so moving it would
  only churn imports. It can move into `Generic/` when a wave touches its consumers anyway.

One collision, deliberate and temporary: `SlotProductAt` is declared both here and in the current
`FunctionFieldGeneration/SlotProduct.lean`. No module imports both, so the library builds; the
collision disappears with the first step of wave 5, which retires the `ℚ` copy of the induction (it
is the port's own statement, not the pin's). It is *forced*, not a choice: the `ℚ` surface cannot
import the theory until that copy is deleted, because Lean rejects the second declaration of the same
public name.

**Wave 5 — landed.** `FunctionFieldGeneration/SlotProduct.lean` went from 1065 to **254 lines**: 19
declarations and 810 lines deleted, five re-pointed as delegations, three untouched. The eight
surviving signatures are byte-identical (checked against `git HEAD`), the transitive cone of 30
modules builds, and `#print axioms` on the re-pointed headline, `map_qExpand_minpoly_eq`, `sv_eq_TS`,
`sv_inj_slot` and `sv_inj` is `[propext, Classical.choice, Quot.sound]` — the layer's statements now
rest on the theory and on nothing else. The duplicate scan reports 0 clusters over the region, and the
two `own:` rows for the deleted `SlotProductAt`/`rval_aux` are retired from `spec/decl_markers.tsv`.

The consumer map was traced before the work was dispatched, so the survive/delete split was measured,
not guessed:

* **deleted** — `SlotProductAt`, `rval_aux`, and the whole induction family (`isRoot_map_minpoly_sv*`,
  `minpoly_map_eq_prod_slots_one`, `phiAtSeed_slot_factor`, `qExpand_qTwist_slot_eq_sv`,
  `finrank_adjoin_mul_dedekindPsi`, `sv_ne_image_of_dvd`, `exists_slot_descent_data`,
  `exists_algHom_adjoin_of_isRoot`, `isRoot_map_minpoly_of_isRoot_subfield`,
  `isRoot_qExpand_sv_of_slot_product`, `isRoot_phiAtSeed_slot_apply`), plus the three `private`
  leftovers with no consumer once it goes: `sv_top`, `nodup_slotValues_sv`, and `sv_eq` if unused;
* **kept as delegations** — `sv` (body = `slotValue (coeffEmb K) jq`), `sv_eq_TS`, `sv_inj`,
  `sv_inj_slot`, `map_qExpand_minpoly_eq` (from `pushedMinpoly_rat` +
  `pushedMinpolyAt_map_qExpand` + the hypothesis + one re-derived product-map step) and
  `minpoly_jqN_map_eq_prod_slots` (from `minpoly_eq_prod_slotValues` + `pushedMinpoly_rat` +
  `prod_slotValues`);
* **untouched** — `mem_adjoin_jqN_of_mem_mff` (its proof is independent of the family), `TS_congr'`
  (pinned, generic, and now consumerless in the tree — a candidate for `Defs/TS.lean` later).

The consumer edits are two, both traced: `Nonmembership.lean:287` passes `rval_aux` as
`map_qExpand_minpoly_eq`'s hypothesis and substitutes the pinned headline (whose statement is
definitionally the same); `Descent.lean:276/278` unfolds `sv` and then must unfold `slotValue` too.
`Descent.lean:331` and `ModularPolynomialLeadingCoeff.lean` need nothing — the headline's hypothesis
stays the pin's own conjunction.

**Three layer-hygiene items wave 5 inherits.** (a) The theory imports `Degree/JqCyclotomicConjugates`
and `ModularPolynomialProperties` only for three declarations that belong in `Defs/` by the layer rule
— `phiAtSeed_jqNModC_eval`, `phiAtSeed_jqNModC_eval_symm` (field-generic, `[CommRing R]`) and
`exists_phiIrreducible_evalSymm`; moving those three down drops both imports. (b) The `dedekindPsi`
duplicate (§7) should be resolved at the same time — `SlotValues.card_slotValues` is the one spelling
on the alias. (c) `slotValue_eq` stays `private`; the base case unfolds `slotValue` by hand, one line,
cheaper than a public spelling of the definition.

**The `C` slot product — landed, and it is a delegation.** The pinned any-field headline
`minpoly_jqNModC_map_eq_prod_slots` is `CharP/SlotProduct.lean`'s one public theorem, and its proof is
`pushedMinpoly_eq_slotPolynomial` at `(ε := RingHom.id, jg := jqModC K)` composed with
`prod_slotValues`; the two carrier premises are `rfl`, and the package hypothesis is the pin's inline
conjunction, converted by `pkg_pkgAt`. The naming is a transcription, not a restatement:
`pushedMinpoly_anyField` is `rfl`. So the instance is *checked*, not asserted — the pin's `if`-form
slot value is `slotValue`'s body, `slotPolynomial_eq_prod` gives the iterated product, and
`spec/check_port.py` diffs the whole statement against the `Theorems/` wrapper and matches it.

Two things the port learned from it:

* `pkg_pkgAt` spends a bridge on the **generation** clause only — the set identity
  `{jqModC K, jqNModC K d} = {jqModC K} ∪ {jqNModC K d}` plus the absorption of `jqModC K` by the
  divisor set (`jqNModC K 1 = jqModC K`, `1 ∣ d`) — which is `gen_iff_levelField`'s proof with `jq`
  replaced by `jqModC K`. The degree clause is `rfl`-equal, so the alias `ModularCurve.dedekindPsi`
  in `Pkg` causes no trouble in a term-level `exact` (only `rw` would trip, §7). No base change is
  involved, because `generatedAt` is stated absolutely — the §6.1f fix is what makes the second
  instance cheap.
* The two pinned statements are **not symmetric in cost**. The slot product had a generic theorem to
  delegate to; the prime non-membership has none — wave 4 is still open (§6.2), the one-theorem
  module was deleted (§6.1d), and `jqNModC_prime_not_mem_fullC` needs the generic
  `prime_notMem_levelField` and its four helpers before it can be stated at `K` at all. It is not a
  delegation waiting to be written; it is a wave.

### 6.1b′ The induction, dispatched in two workordered stages

The last proof was ported by subagents, in two stages, each with a written workorder — both landed:

* **2a — the bridges** ✅ landed. Three facts the body needs exist today
  only as `ℚ` declarations: `map_qExpand_minpoly_eq`, `isRoot_map_minpoly_of_isRoot_subfield`,
  `exists_algHom_adjoin_of_isRoot`. Porting the first forced one interface addition: the descent reads
  the *same* minimal polynomial at a *higher* nome (`N = k * M'`), so the theory needs the two-level
  object `pushedMinpolyAt ε jg m N` ("the level-`m` minimal polynomial, read at the level-`N` nome"),
  of which `pushedMinpoly` is the diagonal — `pushedMinpolyAt_self : … := rfl`. With it the `ℚ`
  statement factors into something weaker and slot-free,
  `pushedMinpolyAt ε jg m (k * m) = (pushedMinpolyAt ε jg m m).map (qExpand κ' k)`, whose `ℚ` original
  is that identity composed with the slot product.
* **2b — the body** ✅ landed, `slotProductInduction` proved. Its real import cone is wider than §6.1
  predicted and worth knowing: besides `SlotValues` and the `Defs/*` it needs `PhiGenSplitsAnyField`
  (the splitting switch), `Defs/Cyclotomic` and `Defs/PhiAtSlot` (`phiAtSeed*`, `isPrimitiveRoot_pow_div`),
  `Degree/JqCyclotomicConjugates` (the field-generic `phiAtSeed_jqNModC_eval`/`_eval_symm`, which are
  what the `ℚ` descent's seed-vanishing does with its `ℚ`-only twins) and `ModularPolynomialProperties`
  (the `Φ_p` datum). None of it is `Defs/Fields` vocabulary, which is the rule that actually holds. Staged A (base case, tower collapse,
  `Φ_p` factorisation at a slot — where the `PhiGenSplitsAnyField` switch lands), B (the descent and
  the two prime cases), C (the closing squeeze). Report after stage A; acceptance is
  `#print axioms slotProductInduction = [propext, Classical.choice, Quot.sound]`, which is also the
  acceptance test for the whole layer. 2b checks for 2a's declarations by name and reports
  `BLOCKED: 2a not landed` rather than guessing.

### 6.1c The slot-product interface

The first cut of `slotProduct` stated the pin's spelling: a two-line pushed-minimal-polynomial term
and a two-line iterated slot product, both repeated across the statements, plus the nome composite
spelled out a third time. Refactored along `TOPIC-assembler-interfaces` §5.1–§5.2:

* three objects named — `nomeMap` (read the base field at the level-`M` nome, in the working
  field), `pushedMinpoly` (the minimal polynomial of the level series, pushed along `nomeMap`), and
  `slotPolynomial` (the slot product);
* the headline is one line, `pushedMinpoly ε jg M = slotPolynomial ε jg M ζ`, with the two
  hypotheses (`IsPrimitiveRoot`, `PkgAt`);
* `slotPolynomial` is the *multiset* product — the object — and the pin's iterated product is
  `slotPolynomial_eq_prod`, which is the general `prod_slotValues`; the expansion is derived, not
  definitional, and one rewrite away for a proof that wants it;
* the naming is *proved* to be a transcription rather than asserted: `pushedMinpoly_rat : … = rfl`
  says that at the `ℚ` instance the named object is the inline composite it replaces. This is the
  rule that a naming introduced this way must be definitionally the old spelling, checked in the
  tree.

This also discharges the remark in `TOPIC-assembler-interfaces` §11 that the slot product's
readable restatement was blocked because the slot vocabulary was `private` in its own module: the
public home is `Generic/SlotValue.lean`, and `Rat/SlotProduct.lean` is the readable statement the
pinned `minpoly_jqN_map_eq_prod_slots` can now delegate to.

### 6.1d The API audit

Every declaration of the two layers was read against `TOPIC-assembler-interfaces` §5 (fan-in vs
fan-out) and §8 (certificate test). Fan-in is what the reader must bring, fan-out what one
application delivers; the rule is that a low-fan-out declaration whose statement is another
declaration's statement modulo spelling is an adapter, and adapters are costs disguised as names.

| declaration | symptom | verdict |
|---|---|---|
| `isIntegral_levelSeries` | took the **whole package** to spend its `d = M` clause | hypothesis narrowed to `degreeAt jg M` |
| `natDegree_minpoly_levelSeries` | same | same |
| `levelField_le_of_dvd` | 2-in/1-out producer of an inclusion nothing consumes; the body wants *membership* | deleted |
| `slotValue_eq` | unfolding of the definition | `private` |
| `slotValue_inj` | 6-in/1-out, on raw bounds (`b * a < M`) no caller holds | `private`; the public form is the slot-bound `slotValue_inj_slot` |
| `slotValue_top` | 3-in/1-out computation | `private` |
| `nodup_slotValues_slotValue` | `nodup_slotValues` applied to `slotValue_inj_slot` | `private` |
| `slotPolynomial_eq_prod` | adapter over `prod_slotValues` — pure notation | deleted; the surface applies `prod_slotValues` |
| `tight_iff_finrank` | re-spelling of a definition: `Tight d` *is* `degreeAt jq d`, definitionally | deleted |
| `pkgAt_hall` | the converse of `hall_pkgAt`, no consumer | deleted (add when one appears) |
| `slotProductInduction_rat` | one application of the theory's induction | deleted; the surface delegates directly |

**The visibility rule, stated after tracing the consumers.** A lemma is `private` iff *every*
consumer — present, or named and planned — is in the same module; otherwise it is public. Applying
it to the slot-value API:

| declaration | consumers | |
|---|---|---|
| `slotValue` | `slotPolynomial` (product module) | public, and the only *present* library consumer in the module |
| `slotValue_eq` | `slotValue_eq_TS`, `slotValue_top`, both in-module | `private` |
| `slotValue_eq_TS` | the induction's slot computations (product module), `slotValue_inj` (in-module) | public |
| `slotValue_inj` | `slotValue_inj_slot` (in-module) | `private` |
| `slotValue_inj_slot` | the product's distinctness step, and the non-membership (wave 4) | public |
| `slotValue_top` | the product's base case and the `a = M` root — both in the product module | **was `private`; corrected to public** |
| `nodup_slotValues_slotValue` | the product's distinctness step — but it is `nodup_slotValues` applied to `slotValue_inj_slot`, i.e. a one-line composition the caller can write | `private` |

The tracing also names a category the audit needs: **pending consumer** — no consumer in the tree
today, but a named one in a wave that is already specified. Above `slotValue` in the dependency
order, the generic layer currently terminates in the `sorry`s of the product's induction, so
`slotValue_eq_TS`, `slotValue_inj_slot`, `slotValue_top` and the package's two consequences are all
*pendings*. `spec/GenericProbe.lean` — not part of the library — is their only present user, which is
what the probe is for. The expiry test: when the named wave lands and a declaration still has no
consumer, it is dead and goes.

The two package consequences have their consumers on the record, and the count is why they exist:

| declaration | planned consumers | what it is |
|---|---|---|
| `isIntegral_levelSeries` | the induction's root arguments (the `a = M` root and the descent case), the non-membership, and — outside the theory — the `ℚ` layer's `minpoly.monic` use; **4 sites, 3 of them generic** | content: the only place the finiteness of the level field is derived from the degree clause |
| `natDegree_minpoly_levelSeries` | the induction's closing squeeze, the non-membership's `hdeg`; **2 sites, in two different modules** | a composition of `IntermediateField.adjoin.finrank` with its sibling |

`natDegree_minpoly_levelSeries` is the weakest declaration in either layer: fan-in one, fan-out one,
and its statement is `adjoin.finrank` re-spelled through the hypothesis. It survives the adapter test
only because its conversion is needed in **two** modules — §5 option 3 (put the conversion at the
call site) is unavailable when there are two call sites in two modules, which is what makes it a
mathlib-supplement rather than an adapter. If the non-membership ever stops needing it, it becomes a
call-site two-liner and goes.

What survived, and why:

* `slotValue_eq_TS` — a notation bridge (slot vocabulary to `TS` vocabulary) with six binders, but it
  is the *one* bridge of its kind: every slot computation runs through `TS`, and the alternative
  would be the same unfolding at each of a dozen call sites.
* `slotValue_inj_slot` — 6-in/1-out, but the fan-in is what the consumers hold (slot membership and
  bounds); it is the shape `nodup_slotValues` and the non-membership already take.
* `pushedMinpoly_eq_slotPolynomial`, `minpoly_eq_prod_slotValues` — one-line delegations, but they are
  the *interface*: the pinned statements' destinations (§6.1c), so the delegation is the point.
* `pushedMinpoly_rat` — a `rfl` with no consumer yet; kept because its consumer is the pinned
  statement's delegation, and because §3 of the interface note requires a naming to be *proved*
  definitional in the tree rather than asserted.
* `prime_notMem_levelField` — five real hypotheses and one conclusion: the two carrier premises
  (`hε`, `hεq`), `hpM`, the package at `M` and the base non-membership, plus `hζ`. The fan-in is the
  content. Its target binders (`κ'`, `ε`, `ζ`) are a seam, not an accident — the conclusion is over
  `κ` while the slots are computed in a carrier — so the docstring says so, and each instance
  manufactures the carrier it needs (`ℚ` a cyclotomic field, `C` the root its own statement
  carries) instead of asking the theory for one.

**At module granularity the same test applies, and it deleted one file.**
`Generic/PrimeNonmembership.lean` held exactly one declaration — eleven binders, one conclusion, no
vocabulary, no companion, no consumer until wave 4 — and it was written only because the skeleton was
written all at once. The theorem is lawful (a seam funnel: its content lives nowhere else, §8's "one
lawful funnel per seam"), but a module is a unit of reading, and one `sorry`-shaped theorem is a note,
not a layer. **It is back (2026-11-07)** with three helpers — the seed equality and the slot constancy live
inside `eval_map_eq_of_mem_slotValues` — and the seam settled as a binder (§6.2), which is what makes
it a module.

Two declarations were *added* by the audit: `degreeAt` and `generatedAt` name the package's two
clauses. They appeared inline in `PkgAt`, in both consequences and in the `ℚ` bridge, they are the
`ℚ` layer's `Tight`/`Gen` split, and naming them is what lets `gen_iff_levelField` be three words
(`Gen d ↔ generatedAt jq d`) and removes the `Tight` bridge entirely (defeq does the job).

### 6.1e The water test: `Generic/SlotValue` ported

`Generic/SlotValue.lean` was the module chosen to test whether the `ℚ` proof bodies generalize:
six declarations, all with a live `ℚ` source, and the smallest module that still exercises the
carrier `ε`, the `TS` bridge and the injectivity argument. Result: 6/6, ported by a subagent from
`FunctionFieldGeneration/SlotProduct.lean` alone (`Reserve` was never opened), 0 errors, 0 warnings,
no new hypothesis, no helper needed. `Generic/LevelPackage.lean`'s two lemmas were ported in the same
pass from `Defs/Invariants.lean` and are equally clean.

What the port established:

1. **The carrier condition is the general form of a `ℚ` lemma.** The only content difference in the
   whole file is `slotValue_eq_TS`: the `ℚ` proof closes with `coeffEmb_jq : coeffEmb K jq = jqModC K`
   and the general proof with `hε : ε jg = jqModC κ'`. Everything downstream *passes `hε` through* —
   no lemma re-establishes it. That is the sharp form of the abstraction's validation: the `ℚ`
   layer's one hard fact about `ε` is exactly the one hypothesis the theory carries. The corollary is
   a work estimate: a `ℚ` module whose proof only ever uses `coeffEmb_jq` ports by threading `hε` and
   changing nothing else.
2. **`ε` being an arbitrary ring hom costs nothing.** No proof inspects it, and none of the six uses
   the field structure of the source `κ` at all; the slot-value lemmas read only `κ'` through `TS`.
3. **The one non-generalization is in a statement, not a proof.** `sv_top`'s generic counterpart is a
   different, simpler statement (§5): consumers of `sv_top` must expect to re-derive the level form
   rather than to find a matching lemma. This was visible in the skeleton and is now confirmed by
   construction.
4. **The skeleton's interfaces held.** No statement needed an extra hypothesis beyond the
   carrier condition already found pre-flight (§7), and no `private` helper was needed, which is
   evidence that the decomposition of §6.1c cuts where the `ℚ` proof cuts.
5. **The new modules carry no linter suppression.** They were written with the house
   `set_option linter.style.haveILetI false` copied from the older FFG modules; it is gone, and what
   it was hiding is two `haveI : NeZero a := ⟨ha0⟩` lines in the ported `slotValue_inj` — copied
   from the `ℚ` `sv_inj`. The linter's own fix (`have`) works: instance search uses local hypotheses
   of class type, and the inlining difference is irrelevant in a proof by proof irrelevance. So the
   older modules' rationale for the suppression ("the instances are consumed by typeclass search, so
   the linter's `have` preference does not apply") is simply wrong; wave 5 can drop the option
   there, and the comment with it. The lesson is the general one: a suppression travels further than
   the code it was written for.

### 6.1f The second water test: one `ℚ` consumer, and the interface it broke

The `ℚ` side's `gen_iff_levelField` (`Gen d ↔ generatedAt jq d`) was written on the skeleton's
interface, by hand, to find out whether the interface holds from the consumer's end. It did not, and
the failure was in the *spelling* of the generation clause, not in the mathematics.

**What broke.** The clause was stated relative to the derived base field —
`levelField jg d = adjoin (baseField jg) S` — while every instance proves it absolutely
(`Gen d` is `adjoin ℚ {jq, jqN d} = adjoin ℚ (divisors)`). Bridging the two needs
`restrictScalars`, and writing `.restrictScalars ℚ` on a term of type
`IntermediateField ↥(baseField jq) _` **does not elaborate**: mathlib's `restrictScalars` carries
its `[IsScalarTower ℚ ↥(baseField jq) _]` argument *before* the field argument, so instance search
runs while the source base is still a metavariable — and fails, even though the instance exists and
`inferInstance` for that exact type succeeds. Neither the dot form, nor the explicit function form,
nor naming the implicit argument fixes it; only applying `restrictScalars_adjoin` (whose own type
fixes the base) and transporting along `SetLike.coe` does. The consumer could be written that way,
but it is base-change plumbing repeated per instance — the theory's problem leaking into every
instance.

**The fix, in the theory.** The generation clause is now stated *absolutely*:
`adjoin κ ({jg} ∪ {levelSeries jg d}) = adjoin κ ({jg} ∪ {x | ∃ d' [NeZero d'], d' ∣ d ∧ x = levelSeries jg d'})`,
which is the language instances speak, plus one conversion lemma `coe_adjoin_baseField`
(`(adjoin (baseField jg) T : Set _) = (adjoin κ ({jg} ∪ T) : Set _)`), stated as an identity of
carrier sets so it rewrites inside `∈` too. The clause that needs the relative spelling — the
*degree* clause, whose consumer `Tight` is `finrank ℚ⟮jq⟯ (adjoin ℚ⟮jq⟯ {jqN d})` — keeps it, and
costs nothing because it is `rfl`-equal. So each clause is now in the spelling of the declaration
that finally consumes it (§5.2 of the interface note), and the asymmetry is deliberate.

**What the fix cost, and what it bought.** In the theory: one lemma (`coe_adjoin_baseField`), no
statement weakened. In the consumer: `gen_iff_levelField` went from un-writable to three set
identities and a `rw` (the two sides differ only in `{jq, jqN d}` vs `{jq} ∪ {jqN d}` and in the
absorption of `jq` by the divisor set, since `1 ∣ d`) — and `hall_pkgAt` became the one line the
audit predicted, `⟨(h d hd).1, (gen_iff_levelField d).mp (h d hd).2⟩`, whose `Tight` half elaborates
*straight into* `degreeAt jq d`. That is the audit's deletion of `tight_iff_finrank` confirmed in
the consumer rather than argued in prose.

Two lessons, both cheap to carry to the rest of the port:

1. **A clause's spelling is an interface decision, and the consumer is the test.** The relative
   spelling looked more "structured" (it named the base field) and was the one thing that made the
   consumer write a base change. The interface note's §5.2 rule — state the hypothesis in the form
   the consuming declaration already takes — would have caught it at design time.
2. **`restrictScalars` is not usable at a metavariable base.** Any theory statement over a *derived*
   `IntermediateField` should offer its own carrier-set conversion lemma; do not expect instance
   search to carry the base change at the shape a consumer writes it. `coe_adjoin_baseField` is that
   lemma for `baseField`; the next derived field will need its own.

### 6.1g The carrier conditions are premises, not arguments

The skeleton's `SlotProductAt` carried only the package — the plan's §3 had listed the two carrier
conditions (1) `ε jg = jqModC κ'` and (2) the level commutation, but the `Prop` did not. Phase 2a's
precondition exposed the hole: its bridges need (2), and the induction had nowhere to get it from; and
the statement is not merely unprovable but **false** without them — at `ε = 0` the left side is `0`
and the right side is `X ^ ψ(M)`, since `slotPolynomial` reads the slots through `ε jg` while
`pushedMinpoly` reads the minimal polynomial through `ε ∘ qExpand`.

Both are now *premises of the `Prop`*, in order, so the induction statement and the headline keep one
shape and the body begins `intro hε hεq hζ h`. The `ℚ` headline discharges them with `coeffEmb_jq`
and `coeffEmb_qExpand`, so its own statement is unchanged — which is why the deficit was invisible at
`ℚ` and why the two water tests missed it: both *applied* the headline under hypotheses, and nothing
had yet had to *prove* it. The lesson for the rest of the port is the same one §6.1f records: a
statement's hypotheses are only tested when something consumes it in a proof.

The premises are true for the instance and spent in the proof, so they are not decoration — but the
*carrier itself* is a separate question: whether to keep it, and with it the two premises everywhere,
or to state the theory at one coefficient field and let each instance transport, is §9.3.
**Decided 2026-11-08 (§11): the *parameter* is folded** — and note what that does to this section's
two premises: they are real, but for a coefficient extension they are theorems
(`coeffMap_qExpand` and `coeffMap_jqModC`), so they are no longer hypotheses of anything.

### 6.1h What the first consumer asked the theory to change

Wave 5 was the first time the theory was consumed by the real layer, and it came back with five
requests. All are interface, none is mathematics; the first four are small.

1. **Make the multiset→iterated bridge public.** The theory states the slot product as a *multiset*
   product; the pin (and the layer) iterate over `M.divisors`. The one bridge,
   `map_qExpand_slotPolynomial`, is `private`, so `map_qExpand_minpoly_eq`'s delegation re-derives
   `map` through an iterated `Finset` product — ten lines of `Polynomial.map_prod` that know nothing
   about slots. The audit deleted `slotPolynomial_eq_prod` as "an adapter over `prod_slotValues`"; the
   consumer shows it was the layer's *public* spelling of the theory's object. It comes back, with the
   map-through-product lemma beside it, stated for an arbitrary `g`.
2. **Make `slotValue_inj` public.** The visibility rule ("private iff every caller holds the slot
   bounds") missed the pin's `sv_inj`, which is stated on the raw bounds `b * a < M`. That single fact
   is why the layer still carries a 13-line proof of a theorem the theory already has — and why it
   keeps the last `TS_injective` use in its own file.
3. **Name the `if h : a = 0` shape.** The pinned headline inlines the slot's body down to
   `letI : NeZero a := ⟨h⟩`, and the delegation closes only because `slotValue`'s body is the same
   `dite`. No statement records this: hoisting `NeZero` into an instance argument, or making the `if`
   non-dependent, would keep every generic theorem true and silently make the pinned statement
   unprovable. A public `slotValue_def` pins the shape.
4. **`pushedMinpolyAt` needs its `ℚ` bridge.** `pushedMinpoly_rat` exists for the diagonal object
   only, so the off-diagonal reading is matched by a `show … from rfl` inside the consumer;
   `pushedMinpolyAt_rat` in `Rat/` removes it.
5. **The import cone is part of the interface** — the theory's `Degree/JqCyclotomicConjugates`
   import pulled a public `jqNModC_congr` into every importer's cone, and it collided with a
   `private` twin in `Degree/Roof.lean`, a module nobody would list as related. Resolved, but not by
   moving the import, and the attempt is worth recording because it corrected the rule:

   * **The `Defs/` move is withdrawn.** `phiAtSeed_jqNModC_eval`/`_symm` are *generic in statement*
     but their proofs rest on `Degree/PhiData`'s `eval_jqNModC_mul_eq_zero`, which is proved from the
     `ℚ`-side data facts (`eval₂_rat_of_data`, `coeffMap_eval₂_jqNModC`). A `Defs/` home would have to
     import `Degree/PhiData`, putting the bottom layer above the `Φ` machinery — worse than the
     coupling it was meant to remove. The rule the port should keep is therefore: **the theory may
     import a fact whose proof is layer-specific; it must not import layer vocabulary**
     (`Hall`/`Tight`/`Gen`/`modularFunctionField`, or the `ℚ` statements themselves). `ModularPolynomialProperties`
     stays for the same reason — `exists_phiIrreducible_evalSymm` is the `Φ_p` datum the theory
     consumes.
   * **The collision was resolved by deleting a declaration, not renaming one.** Since wave 5 put
     `jqNModC_congr` in `Roof`'s cone, `Roof` could simply *use* it: its private twin is gone, the two
     uses cite the public lemma, and the rename is gone with it. What remains is one copy in
     `Degree/JqCyclotomicConjugates` and one `private` copy in `Degree/PhiData` — which cannot see the
     public one, because `PhiData` sits below it; moving the public one down would put it in every
     `Defs/JqCoeff` importer's cone, and that is a tree-wide rebuild for one trivial lemma. Left as a
     recorded duplication rather than paid for.

Also learned, and cheap to carry: a theory's *definitions* collide with a consumer's `private` helpers
too — `Descent`'s `nomeMap` twin had to be deleted (a genuine dedup the theory enabled) — so a new
public name in the theory should be `git grep`ped across the importers before it lands.

**All five requests are being implemented in one wave** (workorder kept with the wave's scratch
files). Scoping them corrected two things in the report that prompted them:

* The collision is caused by the theory's *direct* import of `Degree/JqCyclotomicConjugates`: the
  mention of that module inside `PhiGenSplitsAnyField` is a docstring, not an import, so dropping the
  direct import does remove `Degree/` from the theory's cone. Only the two `phiAtSeed_jqNModC_eval`
  lemmas need moving, to `Defs/PhiAtSlot.lean` (their subject; their proofs are four lines each and use
  only `phiAtSeed`'s definition and two `ModularPolynomialData` fields).
* `ModularPolynomialProperties` does **not** import the `Degree/` module, and `exists_phiIrreducible_evalSymm`
  is the `Φ_p` datum the theory genuinely consumes. Moving it would drag the `Φ` existence proof into
  `Defs/`, which hosts no proofs — so it stays, and the theory keeps that one import deliberately.

Consequently `Degree/Roof.lean`'s rename (`jqNModC_congr_local`) is **reverted**, not kept: it existed
only because the collision did. Separately noted for a later dedup, not this wave: `jqNModC_congr`
exists three times in the tree — public in `Degree/JqCyclotomicConjugates`, `private` in
`Degree/PhiData` and `Degree/Roof`.

### 6.2 The waves

Waves 1–3 are the slot product; wave 4 is the non-membership; wave 5 is the integration and the
cleanup; wave 6 is the prime step (the `Gen` half, §6.2's item 6). Each step is green on its own;
none needs a tree build.

1. **The theory skeleton.** `Generic/LevelPackage.lean` (`baseField`, `levelSeries`, `PkgAt`) and
   `Generic/SlotValue.lean` (`slotValue`, the `rfl` lemmas of §5), then `Generic/SlotProduct.lean`
   (`SlotProductAt`). Then the two small generalizations that are new proof work:
   `isIntegral_levelSeries` and `natDegree_minpoly_levelSeries`, the
   `baseField`/`levelSeries` re-spellings of `isIntegral_adjoin_jqN` and `natDegree_minpoly_jqN`
   (`Defs/Invariants.lean:52`, `:65`). Both are already stated from the finrank clause, so the
   proofs are the same ~25 lines; they are used at `SlotProduct.lean:848` and `:991`.
   Verify: the module builds silently.
2. **The ε-glue.** The two hypotheses as section variables, plus the derived facts that the old
   `coeffEmb_*`/`iota_jqN` block supplied: the composite-level form of (2) (hypothesis 2 plus
   `qExpand_qExpand`, which is what `map_qExpand_minpoly_eq` needs),
   `ε (levelSeries jg d) = qExpand κ' d (jqModC κ')` (the `iota_jqN` analogue, from (1) and (2)),
   and `qExpand κ' e (qTwist u (ε jg)) = TS κ' e u` (definition of `TS` after (1)). ~40 lines, all
   of it existing lemmas with the map abstracted. Verify by restating one existing `ℚ` lemma through
   the glue (`rfl`).
3. **Parameterize the body.** The long pole: ~700 lines, mechanical, with the traps in §7. The
   source is the current `SlotProduct.lean`'s `rval_aux` family (the shelved twin is a cross-check
   only — §2 shows it is the same proof twice), with the three substitutions of §0 and the upstream
   swap of §0.7.
4. **The prime non-membership (second wave) — landed 2026-11-07.** The statement, with the carrier
   it needs and its two per-layer inputs:

   ```lean
   theorem prime_notMem_levelField (ε : LaurentSeries κ →+* LaurentSeries κ')
       (jg : LaurentSeries κ) (hε : ε jg = jqModC κ')
       (hεq : ∀ (N : ℕ) [NeZero N] (x : LaurentSeries κ), ε (qExpand κ N x) = qExpand κ' N (ε x))
       {M p : ℕ} [NeZero M] [NeZero p] [hp : Fact (Nat.Prime p)]
       {ζ : κ'ˣ} (hζ : IsPrimitiveRoot (ζ : κ') (M * p)) (hpM : ¬ p ∣ M) (h : PkgAt jg M)
       (hbase : levelSeries jg p ∉ (baseField jg : Set (LaurentSeries κ))) :
       levelSeries jg p ∉ levelField jg M
   ```

   The two carrier premises are not decoration: the first cut of this statement dropped them, and
   the body was unprovable — `hroots` is `pushedMinpolyAt_map_qExpand ε jg hεq …` and the slot
   theory reads `slotValue` through `TS` only under `hε`. It is the §6.1g lesson a second time, and
   the scaffolding-then-body order is what surfaced it cheaply (the three helpers already took the
   two explicitly, so only the headline changed).

   Two guesses of this section were wrong, and the wave corrected them:

   * **the seam stays a binder.** `κ'`, `ε` and `ζ` are in the statement because the slot argument
     runs in a field carrying a primitive `(M * p)`-th root, and no such root exists in a general
     `κ`. Each instance manufactures one — `ℚ` the cyclotomic field, `C` the root its own statement
     already carries — and the conclusion stays over `κ`. The audit's seam test is satisfied as the
     interface note states it (§8: the fan-in is the content); there is no target-free restatement to
     write, because there is no target-free proof.
   * **there is no `degreeAt jg p`**, and no `hall_prime`. The first cut classified the conjugate
     through the level-`p` slot product and therefore needed `PkgAt jg p`; the landed proof uses the
     `Φ_p`-dichotomy instead — the seed relation `Φ_p(levelSeries jg 1, levelSeries jg p) = 0`
     (`seed_eval_zero` at `d = 1`, pushed along `ε` with `phiAtSeed_eval_of_injective`), the at-slot
     root dichotomy `isRoot_prime_at_slot_iff_of_isPrimitiveRoot`, and the twist branch killed on the
     `q ^ (-M)` coefficient by `p ∤ M` (`qExpand_coeff_of_not_dvd` against `TS_coeff_neg`). So the
     per-layer inputs are `hbase` and the package at `M` — the pin's own two, and one fewer than
     this note predicted. The route was taken from the shelved `C` twin, not from the `ℚ` body; the
     carrier plumbing is the `ℚ` body's.

   The module is `Generic/PrimeNonmembership.lean`: 354 lines, three `private` helpers
   (`nodup_slotValues_expanded`, `map_mem_fieldRange`, `eval_map_eq_of_mem_slotValues`) and the
   headline, zero `sorry`, silent build, every declaration `[propext, Classical.choice,
   Quot.sound]`, and the statement elaborates at `ZMod 5`. Two hub edits made it fit: the
   `exists_algHom_adjoin_of_isRoot` of `Generic/SlotProduct` is now public and stated at a general
   level and root (the descent's single call site was updated, the change a strict generalization),
   and `seed_eval_zero` is public.

   Both instances are delegations: `CharP/Nonmembership.lean` states the pinned
   `jqNModC_prime_not_mem_fullC` in 20 lines (carrier premises `rfl`, `pkg_pkgAt`, then
   `mem_levelField_of_mem_divisorAdjoin` for the absolute-to-relative step — the new generic lemma),
   and `Nonmembership.lean`'s `jqN_prime_not_mem_adjoin` manufactures the cyclotomic carrier. The
   `ℚ` module went from 985 to 687 lines: the five private helpers
   (`nodup_slotValues_qExpand`, `map_mem_fieldRange`, `hall_prime`,
   `eq_seed_of_mem_slotValues_of_mem_fieldRange`, `eval_map_eq_of_mem_slotValues`) are gone,
   `jqN_prime_not_mem_base` stays as `hbase`, and the prime-power tower below is untouched.

5. **Instances, then consumers.** The `ℚ` theorems stay at their current paths, each a delegation;
   `rval_aux`, `SlotProductAt`, `sv_inj_slot` move to `Generic/`; the instance data and
   `hall_pkgAt` go to `Rat/LevelPackage.lean`. Then rebuild the `ℚ` cone (`Descent`,
   `Nonmembership`, `DegreeStep`, `Capstone`, `ModularPolynomialLeadingCoeff`,
   `ModularPolynomialFibreTwo`, the `X1`/`XH`/`Hecke`/`Weierstrass` dependents —
   `tools/deps/port_graph.py --dependents` gives 33 once `Reserve` is out of the tree), and fix the
   call sites that changed *by hand, last*: the hypothesis-spelling ones at
   `Descent.lean:331`/`ModularPolynomialLeadingCoeff.lean:188` (§5). `dedup.py` and `move_dead.py`
   over the touched modules.

6. **The prime step (wave 6) — landed 2026-11-07.** `levelSeries_mem_levelField_mul_prime` in
   `Generic/PrimeStep.lean`: `levelSeries jg M ∈ levelField jg (M * p)`, the `Gen` half of the
   divisor induction, with the same carrier premises and `ζ` seam as the non-membership. It is the
   `ℚ` descent's theorem (`Descent`'s former proof, refactored into two producers and three named
   index facts) generalized to `κ`; both instances are now delegations, and the `C` layer's `S_`
   engine `jqNModC_mem_mffC_mul_prime_of_prod` is retired with it (its hypothesis was the slot
   product, its only consumer was the headline). Numbers: the generic module is 313 lines — one
   public theorem, eight `private` lemmas and five `private` definitions (`levelNomeMap` and the
   four level abbreviations); `Descent.lean` went 473 → 179; `MffCMulPrime.lean` 249 → 68. Two facts the wave established that the earlier plan had wrong:

   * the certificate's polynomial lives over the **level** field, so the theory needs a nome map on
     `levelField jg N`, not only `SlotProduct`'s `nomeMap` on `baseField` — `levelNomeMap`. The
     workorder's `IntermediateField.inclusion` recipe does not typecheck: `baseField jg` and
     `levelField jg (M*p)` are `IntermediateField`s over different bases, so the inclusion is the
     `Algebra` instance itself;
   * `exists_phiAtSeed_roots` needs `hεq` (not only `hε`): the seed push is a statement about
     `qExpand κ' … (jqModC κ')`, i.e. inside the image of `ε`, so it needs level commutation. The
     workorder had listed `hε` alone; the body corrected it.

Expected end state: one induction, one slot-value definition, one package predicate, `Hall`/`Pkg`
untouched, `hall_pkgAt` as the only bridge, no `ℚ` vocabulary below `Rat/` — and no `C`-layer copy
anywhere: `Reserve` is deleted, and a future char-`p` instance is written fresh into `CharP/`.

## 7. Traps

* **`qExpand`/`qTwist` act in the coefficient field** (§0.1, §0.2). If the slot value is written with `ε`
  applied last, the `ℚ` instance needs a root of unity in `ℚ`; if `qExpand` is applied to `A` as a
  type, it is `qExpand (LaurentSeries κ)`, which is not the endomorphism meant.
* **The carrier condition is not a headline-only hypothesis.** The plan lists
  `ε jg = jqModC κ'` as one of the theory's hypotheses; the first port shows it must also be
  threaded into the *slot-value API*, because the slot theory is read off `TS` and only the carrier
  condition turns `slotValue` into a `TS` value. It is not bookkeeping: at `jg = 0` every slot is
  `0`, so equal slots would not separate their parameters and the injectivity statement is false.
  Every lemma that compares two slots carries it (`slotValue_eq_TS`, `slotValue_inj`,
  `slotValue_inj_slot`, `nodup_slotValues_slotValue`); the ones that only unfold or compute
  (`slotValue_eq`, `slotValue_top`) do not.
* **`dedekindPsi` resolves to two different constants.** `_root_.dedekindPsi`
  (`NumberTheory/DedekindPsi.lean`) is what `degreeAt`/`PkgAt`/`natDegree_minpoly_levelSeries` use;
  `ModularCurve/Defs/DedekindPsi.lean` declares a `def dedekindPsi N := _root_.dedekindPsi N` alias,
  which inside `namespace ModularCurve` *shadows* the root name. So in a module that imports
  `SlotValues` (which pulls the alias in) the unqualified identifier is the alias, and a `rw` against
  a `degreeAt` hypothesis silently fails to match. The theory's new statements write
  `_root_.dedekindPsi` explicitly. The alias is a follow-up: either delete it or make it an `abbrev`
  with a `rfl` lemma, so the two spellings cannot diverge by import order.
* **Coercions are part of the spelling.** `x ∈ adjoin κ S` and `x ∈ (adjoin κ S : Set _)` are not the
  same expression to `rw`, so `coe_adjoin_baseField` fires only on the explicit `(: Set _)` form — the
  `abbrev` trap, generalised to coercions.
* **`Module.Free` of a tower is not found by instance search** at the shape
  `Module.finrank_mul_finrank` wants (`Module.Free (baseField jg) (levelField jg d)`): the two
  `Module.Free.of_divisionRing` facts must be `have`d explicitly.
* **`letI` is unavailable for a local algebra instance; `let` works.** The descent installs
  `Algebra (baseField jg) (LaurentSeries κ')` from `(nomeMap ε jg M).toAlgebra`; inside a proof of a
  proposition the `haveILetI` linter demands `have`/`let`, and with `set_option` forbidden here the
  installation must be a plain `let` — which still registers for instance search (verified: the
  descent's `algebraMap` finds it, and `halg` closes by `RingHom.algebraMap_toAlgebra`). The same
  substitution is needed for `NeZero`, `Fact p.Prime` and `Module.Free` throughout the body.
* **`NeZero` bookkeeping.** The level series is stated under `[NeZero]`; the generation clause's
  set-builder needs the `∃ (d' : ℕ) (_ : NeZero d')` binder (as `Pkg` has it) if it is to be
  compared with `Pkg`/`modularFunctionFieldFull`, whose sets carry it; and `qExpand κ (N * x)`
  cannot be re-associated because the `NeZero` argument breaks the motive — a level parameter must
  travel with it.
* **The degree argument does not need `Injective ε`.** The induction's squeeze needs the degree of
  the *pushed* minimal polynomial, and the transfer from the unpushed one is
  `Polynomial.Monic.natDegree_map`, which is unconditional on a monic polynomial. That is why
  hypothesis (1) is the only fact about `ε` in the theory (and why no injectivity hypothesis was
  ever needed, §0.5) — worth knowing before anyone "fixes" it by adding one.
* **`Algebra (baseField jg) (LaurentSeries κ')` belongs to the proofs, not the statements** (§3).
  Passing it to the headline changes the statement; and it must *not* be installed as a section
  `local instance`, because in the any-field instance `κ' = κ` and the composite
  `(ε.comp (algebraMap _ _)).toAlgebra` would then compete with the `IntermediateField.toAlgebra`
  instance that `minpoly (baseField jg) (levelSeries jg M)` needs on the *source* side. Keep today's
  per-lemma `letI` + `halg` style; the lemmas that need it are named in §3.
* **The upstream swap is not free.** The `ℚ` body's splitting is `PhiGen.splits_prime_at_slot`,
  which spends `[Algebra ℚ K]`; the master's is
  `PhiGen.splits_prime_at_slot_of_isPrimitiveRoot`, which takes the order-`p` root `ζ ^ (M / p)`
  rather than an order-`M` root and reads the slot at `jqModC κ'` rather than `coeffEmb K jq`. The
  substitution is `(ζ ^ (M / p)) ^ b = ζ ^ (b * (M / p))` plus hypothesis (1); both `ℚ` facts
  (`coeffEmb_jq`, and the `T`-side `TS` rewrites) already exist.
* **No second spelling of anything.** The `C` twin's `svC`/`SlotProductAtC`/`rval_auxC` block
  existed for one reason: Lean refuses a `private` declaration whose public name is already
  imported, so shadowing forced a suffix. With the island deleted there is no name to shadow, and
  with one definition per object (Rule 1, §6.1) there is nothing to duplicate — a reappearing
  `svC`-shaped declaration is a signal that a `ℚ` fact leaked into the theory, not a naming
  problem.
* **No comments inside a body.** Prose lives in the module header, in the declaration's docstring, or
  in this note — never between the lines of a proof. A step that needs a sentence to explain it is a
  step that needs a name (a `private` lemma, whose docstring then carries the sentence), and an
  explanation of *why* a statement is shaped as it is belongs in the note. The first consumer test
  produced exactly one such comment, in `gen_iff_levelField`'s proof; it moved into the docstring,
  where a reader arriving from the name sees it.
* **Do not copy a `set_option` into a new module.** The new generic and `ℚ` modules carry only
  `set_option autoImplicit false` (project-wide anyway); no linter is suppressed. A suppression
  copied from a neighbour hides whatever *your* code does — the first port already produced two
  real lint warnings from one, the `haveI`/`have` pair in `slotValue_inj` (`have` is the fix:
  instance search uses local hypotheses of class type, and the inlining difference is irrelevant in
  a proof). The older FFG modules' rationale for suppressing that linter is wrong for the same
  reason; wave 5 can drop the option and the comment with it.
* **The four measured traps from the last pass over these proofs**: `rw` does not see through an
  `abbrev` in the *goal* (`unfold` it, as `tight_one` does); `qExpand A (N * x)` cannot be
  re-associated (see above); `rw` cannot match through a `set` local; a universe bound in a
  *statement* is not the section's (keep the `∀ {K}` shape where it is).
## 8. What stays per-layer (this is not duplication)

* The **socket degree theorems**: `Tight`/`Gen` at `ℚ` (`Capstone.hall_all`) versus `Pkg` at `K`
  (`PrimePowerStepAnyField`, the socket). Different theorems, one shape — the master takes the
  shape as a hypothesis. This is *not* the prime step: that one (`jqN(q^M) ∈ F_{M·p}`) is the same
  theorem in both layers and is shared (`Generic/PrimeStep.lean`, wave 6, §6.2).
* **The base non-membership**: `jqN_prime_not_mem_base` at `ℚ`, the `hbase` hypothesis at `C`.
  That is the theory's `hbase` and the only non-membership input — the *degree* at the prime is not
  one (§6.2: the `Φ_p`-dichotomy route spends no `PkgAt jg p`). Each layer keeps its own base
  non-membership proof, which is exactly the `…_of_socket` shape D-S wants.
* **The prime-power tower** `jqN_pow_not_mem_adjoin_full` (`Nonmembership.lean:676`): the `Φ_p`
  chain of fields `C_i`, the compatible family `σ_i`, `eq_spread_of_eval_eq_zero_of_mem_range`. It
  is `ℚ`-modular-equation mathematics with no generic counterpart, and nothing in the theory needs
  it.
* **The general-`N` roots API** (`PhiSlotRoots`): the tower's input. The master's slot product uses
  the level-`p` any-field API instead (§0.7).
* The **modular-polynomial link**: `data.Φ`, `toAdjoin_eq_minpoly_all`, the leading-coefficient
  census (`ModularPolynomialLeadingCoeff`) are `ℚ`-side objects with no any-field counterpart.
* The **`SlotValues` API** (`slotValues`, `card_slotValues`, `prod_slotValues`, `nodup_slotValues`),
  already shared and generic; untouched.

### 8.1 The C degree layer's `ℚ` correspondence

The shelved `PrimePowerStepAnyField` (1555 lines) is the twin of **three** live modules at once, not
of one — which is why the *socket* degree layer is the natural boundary of this refactor rather than
another target for it. Its neighbour `MffCMulPrime` was the exception: it is one theorem, the `ℚ`
descent's, and wave 6 shared it (§6.2).

| C declaration | `ℚ` counterpart |
|---|---|
| `jqNModC_mem_modularFunctionFieldC_mul_prime` | `Descent.jqN_div_mem_modularFunctionField` — **one theorem**, shared as `Generic/PrimeStep.lean` (wave 6); the row is no longer a twin |
| `jqNModC_mem_of_div_primes`, `jqNModC_mem_of_div_prime_of_mul_prime` | `Generation.jqN_mem_of_div_primes` |
| `jqNModC_mem_adjoin_top_insert`, `fullC_succ_eq_adjoin_insert_divSet`, `fullC_mul_prime_eq_adjoin_insert_image`, `mffC_eq_fullC_of_steps` | `Generation.full_eq_adjoin_full_div_prime`, the `Gen` half of `Capstone.hall_all` |
| `finrank_adjoin_jqNModC_prime_of_not_mem'` | `DegreeStep.finrank_adjoin_jqN_prime_of_not_mem` |
| `relfinrank_fullC_prime_pow_tower` | `DegreeStep.finrank_adjoin_jqN_pow_succ_of_not_mem` |
| `relfinrank_fullC_mul_prime_pow` | `DegreeStep.relfinrank_full_eq_mul` |
| `tight_iff_relfinrank_fullC` | the definition of `Tight` |
| `pkg_of_socket`, `package_of_socket` | `Capstone.hall_all` — but **conditional** on the socket, while `ℚ` derives the package outright |

Where it is *not* a twin, and why the degree layer stays per-layer (§8):

* `divSet`, `fullC`, `eFull`, `qExpandₐK` are C-layer vocabulary with no `ℚ` carrier; the `eFull`
  tower (`natDegree_minpoly_jqModC_eFull_le*`, `le_natDegree_minpoly_jqModC_eFull`,
  `relfinrank_eFull_fullC_eq_natDegree`, the `relfinrank_fullC_succ_*` bound chain) is the device
  that runs the prime-power step with an arbitrary bound `b`, which the `ℚ` statement `p ^ a` does
  not need. So it is a *more general statement proved by a different argument*, not a respelling.
* the package is conditional there (`package_of_socket`) and unconditional here (`hall_all`), because
  the char-`p` route takes its input from the geometric side and `ℚ` proves it.

The corollary for the theory is §8's first bullet, now with evidence behind it: **do not grow
`Generic/` to cover `Tight`/`Pkg`.** Two proofs, two devices, one shape — the shape is the
hypothesis.

What to fish out of that file when the char-`p` route resumes: about eight declarations are
field-generic and have no `ℚ` twin at all, and belong in `Generic/` or `Defs/` rather than in a
C-layer module — `relfinrank_adjoin_insert`, `relfinrank_adjoin_insert_eq_natDegree`,
`relfinrank_fullC_insert_eq_natDegree`, `jqNModC_injective`, `qTwist_jqModC_eq_TS`,
`mem_adjoin_of_mem`, `phiAtSeed_map_algebraMap`, `natDegree_minpoly_le_of_phiAtSeed_root`. The
first three are relative-degree lemmas the `ℚ` side does not have and would probably want. The rest
of the module (`eFull`, the socket, `fullC`) is `CharP/`.

## 9. What is still the owner's call

1. ~~Whether wave 4 (the prime non-membership) lands with waves 1–3 or when the char-`p` route
   resumes.~~ **Landed** 2026-11-07 as `Generic/PrimeNonmembership.lean` (§6.2 item 4), with
   `Generic/PrimeStep.lean` (wave 6) as its positive twin.
2. **Whether `Reserve` is deleted now or left in place until the next wave.** The arrangement above
   assumes it is gone (git is the record); leaving it costs build time, four `port_graph`
   modules, and it keeps the `C`-suffix naming pressure alive. Since waves 4 and 6, the shelf's
   remaining unique content is the socket degree half (`PrimePowerStepAnyField`'s `eFull` tower and
   `package_of_socket`); its `MffCMulPrime` is a delegation and its `SlotProductAnyField` headlines
   are duplicated by `CharP/` (the two `dedup` clusters left in the region).
3. ~~**Whether the carrier should be folded away — deferred, and not urgent.**~~ **Taken up
   2026-11-08, but only as §11.1 states it:** the carrier *parameter* is folded (the two fields stay
   as types), while the one-field theory that this item prices is **not** taken — its price is the
   package at the carrier, the base non-membership at the carrier, and the faithful descent of the
   conclusion, and none of the three is paid. What *was* established is the lemma the item names
   first, the linear disjointness of the coefficient field and the level function field; §11.4
   records it, marks it as not needed by any statement the port cites, and it is what the optional
   one-field collapse would consume.

   The analysis the decision was made on: both seamed theorems
   take a carrier `ε : κ((q)) → κ'((q))` with `hε`/`hεq` (§6.1g), because the slots are read where a
   primitive `(M*p)`-th root exists while the conclusion is over `κ`. The `C` instance is
   `ε = RingHom.id` (both premises `rfl`); the `ℚ` instance is `coeffEmb` into the `(M*p)`-th
   cyclotomic field, and it *needs* a carrier because `ℚ` has no such root.

   **The gain.** Folding it in — state the theory at one coefficient field with `ζ : κˣ` and let
   each instance transport — removes `κ'`, `ε`, `hε`, `hεq` from the theory and from every helper,
   including the two `rfl`s in the `C` delegation. That is a real simplification: the carrier is
   threaded through the slot-value API, both producers and both headlines, and it is the one thing
   in the theory that is not stated in the conclusion's frame.

   **The price is one lemma, not per-instance series work.** The `ℚ` instance would instantiate at
   `κ = ℚ(ζ_{M*p})` and must then supply, in `K`, the package at `M`, the base non-membership, and
   the *descent* of the conclusion — the last of which is the hard-looking one, because the prime
   step's conclusion is a membership and does not descend by an adjoin induction. All three follow
   from one function-field statement: **`K` and the level function field are linearly disjoint over
   `ℚ` inside `K((q))`** (equivalently `K · Mff(M) ∩ ℚ((q)) = Mff(M)` and
   `[K · Mff : Mff] = [K : ℚ]`). The mathematics is easy — `K/ℚ` is Galois, `K ∩ ℚ(q) = ℚ` since the
   algebraic elements of a purely transcendental extension are the constants, then a basis-of-`K`
   argument — but its Lean form is not in the tree: `IntermediateField.LinearDisjoint` and
   `LinearDisjoint.inf_eq_bot` are, while the *descend through a subfield* form and the
   adjoin-image generation lemma are not (~60–120 lines, once). The K-side generation clause is the
   cheap one either way: the `K`-generators are the `coeffEmb`-images of the `ℚ`-generators
   (`coeffEmb_jq`, `coeffEmb_qExpand`), so it is adjoin monotonicity, not a new proof.

   **What this is, and is not.** It changes no statement's mathematics; it decides *where the
   embedding is quantified* — in the theory once, or in each instance. And it does not by itself
   give the function-first formulation, which would also replace the theory's `jg` parameter by the
   base field `F` plus an embedding, i.e. revisit §4's "`F` is not a parameter". The two decisions
   belong together: the same function-field view that makes the base field a derived object is the
   one that makes the carrier an instance's business.

   **No urgency.** Both theorems are proved, green and axiom-clean; the fold is a simplification of
   the theory, not a fix. If it is taken up, the order is the linear-disjointness lemma first (with
   its two consequences stated), then the fold, statements first and bodies dispatched as in waves
   4–6 — and the `ℚ` instance re-verified against the same pinned statements.

Everything else is settled by §6.1: the theory is
`Generic/{LevelPackage,SlotValues,SlotValue,SlotProduct,PrimeNonmembership,PrimeStep}.lean`, the
instance data and the bridges (`hall_pkgAt`, `pkg_pkgAt`) are `Rat/LevelPackage.lean` and
`CharP/LevelPackage.lean`, the `ℚ` and `C` theorems stay at the current paths as delegations, and the
identifiers are `baseField`, `levelSeries`, `levelField`, `slotValue`, `PkgAt`, `SlotProductAt`.

## 10. What to check

* Per module, never a tree build: `lake build <module>`, silent (no `info:`, no `warning:`). The
  induction is a fresh ~700-line proof; if one build approaches two minutes, stop and report rather
  than reaching for the tree.
* **The instance is the theorem** — an equality of statements, not a diff of text: the `ℚ`
  conclusion and `sv`'s instance are `rfl` against the theory's (§5), the finrank clause of `PkgAt`
  is `rfl` against `Tight`, and the generation clause is one `extendScalars_adjoin` rewrite. If any
  of those stops being `rfl`, the theory has picked up a `ℚ` fact.
* **The abstraction probe** (§6.1): `#check` the theory's declarations at a field with no
  `ℚ`-algebra structure. It must elaborate.
* **No `sorryAx` behind a clean build.** A ported declaration must print
  `#print axioms … = [propext, Classical.choice, Quot.sound]`; a `sorry` deeper in the file shows up
  here through the declarations that consume it, which a 0-warning build alone does not catch when
  the consumers are still skeletons.
* **One body, one definition.** `tools/deps/dedup.py` over the region: the twin families
  (`sv`/`svC`, `jq`/`jqModC`, `map_qExpand_minpoly_eq`/`…C`) must be gone, and the induction must
  appear once. `tools/deps/move_dead.py --select dead --dry-run` per touched module.
* **The mathematics**, by reading: the headline's hypothesis is the level package and nothing else;
  no hypothesis is unspent; the per-layer inputs of §8 (the prime degree, the base non-membership)
  are hypotheses of the non-membership, not hypotheses of the slot product.

---

## 11. Revision 2026-11-08: the carrier is a section variable, not a parameter

**Status: landed (2026-11-08); the measured record is
[`TOPIC-ffg-refactor.md`](TOPIC-ffg-refactor.md) §13.** The plan of record is that file's §1–§12;
this section states the same revision in this note's vocabulary and records which of the note's
earlier decisions it replaces. It changes no mathematics: the same theorems, with the two
coefficient fields passed as *types* instead of through a carrier *argument*. One part of it was
corrected on landing — the prime non-membership stays two-field (§11.6 below — the correction is
recorded there and in §13).

### 11.1 What the fold changes, and what it does not

§0.1–§0.7 built the master at two coefficient fields `κ`, `κ'` joined by a carrier
`ε : LaurentSeries κ →+* LaurentSeries κ'`, with two premises (`hε : ε jg = jqModC κ'` and
`hεq : ∀ N, ε (qExpand κ N x) = qExpand κ' N (ε x)`). That was the right generalization of the pin's
`ℚ` statements, and the two instances do instantiate it (`Rat`: `coeffEmb` into the `(M*p)`-th
cyclotomic field; `CharP`: the identity). What it cost is measurable in the built tree: the carrier
sits in **48** signature positions of the four `Generic/` modules and `hεq` in **54**.

The carrier does three jobs, and only the third is removable:

1. **Naming the field where the roots live** — content: `ℚ` has no root of unity.
2. **Carrying the source minimal polynomial into that field** — content, and the reason the
   *package hypothesis can stay a fact about the `j`-series over `κ`*. This is the relative half of
   the theory (supplement §4), and it is what the pin's `ℚ` statements do.
3. **Relating the two fields' names** — `hεq` (commutation with the nome) and `hε` (the carried
   series is the carrier's `j`-series). For a coefficient extension these are *theorems*:
   `coeffMap_qExpand` and `coeffMap_jqModC`. Type adaptation.

Both instances' carriers are coefficient extensions, so the fold is: declare `[Algebra κ κ']`, take
`σ := coeffMap (algebraMap κ κ')`, and delete the parameter. Jobs 1 and 2 then live in the *types* —
`baseField jg`, `levelSeries jg d`, `PkgAt jg` on the source side; `slotValue (σ jg)`,
`slotPolynomial (σ jg)`, `TS κ'` on the target side — with `nomeMap` the single bridge.

**Not removed, deliberately: the source-side package hypothesis.** There is an equivalence worth
stating once: *the carrier in the slot product is what keeps `PkgAt` on the source side.* The pushed
headline takes `minpoly (baseField jg) (levelSeries jg m)` and *maps* it, so its degree is `ψ(M)` by
`Monic.natDegree_map` from the source package. A statement of the same content with the minimal
polynomial taken over the carrier would have to hypothesis the package *there*, which `ℚ` cannot
supply — that is §11.4's dictionary, and it is not needed.

### 11.2 Where the two fields appear after the fold

| statement | shape | its content |
|---|---|---|
| `nomeMap`, `pushedMinpolyAt` | source minpoly, target slots | the relative half: the minimal polynomial is over the base field of `κ`, its roots are in `κ'` |
| `slotValue`, `slotPolynomial`, `TS`, the `Φ_p` lemmas | one field (`κ'`) | the slots live where the root lives |
| `SlotProductAt`, the induction | one `Prop`, hypothesis `PkgAt jg` on the **source** side; no `ε`, no `hεq` | the package is a fact about the `j`-series over `κ` |
| `levelSeries_mem_levelField_mul_prime` | two fields in the **conclusion** | a membership in a field of `κ`, proved by reading roots in `κ'`; irreducible (§11.5) |
| `prime_notMem_levelField` | two fields, package at the **source** (like the slot product) | the conclusion is over `κ`, the conjugate classification is in `κ'`; a one-field statement would move `PkgAt` to the carrier, which `ℚ` cannot supply (§11.6) |
| `Generic/LevelPackage` | one field | it never had a carrier |

This is §0.8's rule ("one theorem, one statement") applied to the carrier rather than to the
package: there is no second spelling of `hεq` and no carrier argument to pass.

### 11.3 The carrier is a coefficient extension

The declared variables are `[Algebra κ κ']` with `σ := coeffMap (algebraMap κ κ')` — not an
arbitrary ring hom. Both instances are of that shape, so nothing is lost; and `hεq` becomes the
theorem `coeffMap_qExpand` (leaving the signature and all 54 call sites) and `hε` becomes
`coeffMap_jqModC`.

### 11.4 The dictionary: proved, and not on the critical path

`(5.2)` — adjoining the coefficient field does not change the level field's relative degree — is the
dictionary's one non-formal fact, and it is proved and shelved as
`Reserve/ModularCurve/FunctionFieldGeneration/BaseChange.lean` (exit 0 in ~19 s, no `sorry`, no
warnings, axioms `[propext, Classical.choice, Quot.sound]`): `finrank_levelField_coeffMap` (with
`[FiniteDimensional κ κ']`, which is essential to that route) plus its `degreeAt` corollary
`degreeAt_coeffMap : degreeAt (σ jg) d ↔ degreeAt jg d`.

The route is this note's §9.3 estimate realised: a `κ`-basis of `κ'` stays independent over the level
field (coefficient separation, `HahnSeries.coeff`), then
`LinearDisjoint.adjoin_rank_eq_rank_left_of_isAlgebraic` at `d` and at `1`, two tower laws, and
cancellation of `[κ' : κ]`. The measured traps are in
[`TOPIC-ffg-refactor.md`](TOPIC-ffg-refactor.md) §6.2 — chiefly that `baseField (σ jg)` is a
**`κ'`-based** intermediate field (so the identifications must go through `Subfield`s), and that
`Module.finrank ↥A ↥B` is unavailable for two `κ`-based fields (so the tower runs on `relfinrank`).

**But it is not needed — by the fold, or by anything else the port cites.** §9.3's third item priced
the one-field theory at "the package at `M`, the base non-membership, and the descent of the
conclusion". None of the three is bought: the package stays the *source* package (§11.1), the base
non-membership is evaluated at one field (§11.6), and the descent of the conclusion is exactly what
the surviving two-field membership buys — the range of `levelNomeMap` instead of the faithfulness
`(5.4)`. Walk the `ℚ` layer's three statements: the pinned slot-product headline is the pushed
headline at `(jg := jq, κ' := K)`; the prime step returns through the range of the nome map; the
non-membership is the `K`-side theorem plus the *free* descent, whose only base-change content is the
adjoin identity of (5.1). So nothing the port cites needs (5.2) (or (5.3), or (5.4)) — the dictionary
is the price of a one-field *formulation*, and the port does not want that formulation. The
supplement says the same in its §6 ("the dictionary is optional").

What the dictionary is good for is the *optional* collapse: with (5.2) and the minimal-polynomial
transport (5.3), the pushed form becomes a genuinely one-field theorem at `κ'` and the pinned `ℚ`
statement becomes literally that theorem as a base change. That is a follow-up, not this wave; see
[`TOPIC-ffg-refactor.md`](TOPIC-ffg-refactor.md) §6.3.

### 11.5 The prime step: the B-side stays by default, the A-side is the option

The prime step's statement is the one place where the two fields are in the *conclusion*: a
membership in a field of `LaurentSeries κ`, argued by reading roots in `κ'`. **That is not a
weakness to be removed:** the one-field form (`levelSeries (σ jg) M ∈ levelField (σ jg) (M*p)`, which
the same argument gives at `κ = K`) does **not** imply it — returning from a membership in the
`K`-level field to one in the `ℚ`-level field is the faithful descent `(5.4)`, which the port neither
has nor wants. So the statement keeps both fields, and its conclusion returns through the range of
`levelNomeMap`.

What is *optional* is the proof, and it is the §2.2/§3(b) question:

* **Default (today's proof, minus the carrier).** `exists_transported_minpoly` enumerates `B`, the
  pushed minimal polynomial with its slot list (from the slot product at the carrier);
  `exists_phiAtSeed_roots` supplies `A = Φ_p`'s root shape as the case split; `huniq` compares the
  two shapes by `TS_injective` plus the index arithmetic. It needs the package (`PkgAt jg M`) and
  `PrimeStep` keeps importing the slot product. In the fold it loses only `hε`/`hεq` and the two
  helpers that related the fields (`map_levelSeries`, the `hεq`-threading).
* **Option (the supplement's §3(a)).** Enumerate `A = Φ_p` instead; `B` becomes a witness, and
  uniqueness is the two root-exclusion facts. The proof is not new: it is the any-field peeling in
  `Reserve/ModularCurve/FunctionFieldGeneration/PrimePowerStepAnyField.lean` —
  `jqNModC_mem_of_div_primes`, `jqNModC_mem_of_div_prime_of_mul_prime` (two `Φ_p`'s, **no minimal
  polynomial**), built into the divisor induction by `jqNModC_mem_adjoin_top_insert`,
  `fullC_succ_eq_adjoin_insert_divSet`, `fullC_mul_prime_eq_adjoin_insert_image`; uniqueness is
  `TS_injective` plus level arithmetic (`unique_common_root_two_prime_slots`,
  `unique_common_root_of_prime_step_and_mul_prime_slot`), and the root shapes are the any-field ones
  already public in `PhiGenSplitsAnyField.lean`. Ported with the target field being the statement's
  own (`F := levelField jg (M * p)`, strong induction over `d ∣ M * p`), it concludes the statement
  directly and **drops `PkgAt`**, which also removes `hall_pkgAt` from `Descent.lean`.

Why the option is not part of the fold: the ε complaint is answered by the section-variable shape
(§11.1–§11.3) without it; the B-side proof carries no `hεq` once the carrier is a coefficient
extension; and the A-side changes both a statement (`PkgAt` leaves) and a proof (the descent stops
importing the slot product), i.e. two things a reader must re-verify, for no reduction in the ε
surface. Take it when someone wants the package-free membership or the pin's node structure — and
note that the shelf's `fullC`-induction targets the divisor adjoin, while the statement's target is
the level field, so the induction's target is the statement's field, not `fullC`.

One consequence worth recording either way: **the generation clause of the package has a proof in
the tree**, at one field, in that same peeling with the divisor-adjoin target. Promoting it so that
`PkgAt` shrinks to its degree clause is *not* this wave (§6.1's layer rule says the theory may state
what it cannot yet prove; the promotion belongs with the char-`p` resumption), but the peeling must
not be re-derived a third time.

### 11.6 The prime non-membership: two fields, as landed

**Correction (landed). This one does *not* go to one field.** The plan stated it at `κ` with `ζ : κˣ`,
`PkgAt jg M` and the base non-membership, and proposed `ℚ` evaluate it at `κ = K`:

* its hypothesis, `jqNModC K p ∉ adjoin K {jqModC K}`, is
  `ModularCurve.jqNModC_prime_not_mem_adjoin_of_charZero`, unconditional in characteristic zero;
* its conclusion would then return to `ℚ` by the *free* direction of the supplement's §4.

That evaluation cannot be reached. The `K`-side theorem needs `PkgAt (jqModC K) M`, while the `ℚ`
layer holds `Hall M`, i.e. `PkgAt jq M`; the missing clause is the **level-degree clause at the
carrier**, and transporting it is exactly `(5.2)` of §11.4 — the banked dictionary, which §11.4
correctly rules out. (The generation clause does transport by an adjoin-image argument; the degree
clause does not.) This is the same principle as §11.1's — *the package stays on the source side* —
which the plan applied to the slot product and not to the non-membership.

So the statement keeps both fields (`[Algebra κ κ']`, source condition `jg = jqModC κ`, package
`PkgAt jg M` at the source), and both instances are evaluations instead:

| | `κ` | `κ'` | `hjg` |
|---|---|---|---|
| `ℚ` | `ℚ` | `CyclotomicField (M * p) ℚ` | `rfl` |
| `C` | `K` | `K` | `rfl` |

The free descent of a non-membership is therefore not spent, and `Nonmembership.lean` keeps its
current route (the base non-membership at `ℚ` is `jqN_prime_not_mem_base`).

`Reserve` is not imported, and `Degree/PrimeNonAdjoin` is not needed either — the plan's objection
to the `ℚ` route disappears with the one-field form it was paying for.

### 11.7 What this supersedes, section by section

| section | status |
|---|---|
| §0.1–§0.7 | stand, read with the two fields as *types* (§11.2) rather than through a carrier argument; §0.3's slot value is `slotValue (σ jg) ζ a b` |
| §0.8, §0.9 | stand, unchanged |
| §2 (the master statement) | **superseded by §11.2**: no `κ'`, no `ε`, no `hεq` in the signature; the source package hypothesis stays, and the minpoly stays on the source side |
| §3 (`SlotProductAt`) | **superseded**: one `Prop`, premise `jg = jqModC κ` and `IsPrimitiveRoot ζ M` and `PkgAt jg M` |
| §4 (`PkgAt`) | stands: `PkgAt` is unchanged, and §11.5 records that its generation clause has a proof |
| §5 (the two instantiations) | **partly superseded**: the `ℚ` instance is the pushed headline at `(jg := jq, κ' := K)` — *not* a base change (§11.4 is the base-change route, and it is optional); `sv` becomes the one-field slot value and `sv_eq_pin` records the pin's inline body |
| §6.1 (the arrangement) | stands; a `Generic/BaseChange.lean` is a *follow-up* module (§11.4), not part of the fold |
| §6.1b–§6.1h (the waves, the interfaces, the audit, the water tests) | the record of the built state; §6.1c–§6.1d's interface decisions stand, the carrier-parameter signatures they describe do not |
| §6.1g (the carrier premises) | **superseded in part**: the premises are real, but they are theorems about `coeffMap` (`coeffMap_qExpand`, `coeffMap_jqModC`), so they are not hypotheses of anything |
| §7 (traps) | stands: the `Fact`/`NeZero` chain, the `p ^ k * M` orientation, `subst`'s direction, the checker's parsed names — all still paid. Add the two from the (5.2) probe if the dictionary is ever promoted ([`TOPIC-ffg-refactor.md`](TOPIC-ffg-refactor.md) §6.2) |
| §8 (per-layer) | stands |
| §9.3 (the fold) | **taken up, with its third price item *not* bought**: see the banner there and §11.1/§11.4 |
| §10 (checks) | stands, and the fold adds: `grep -rn "hεq"` over `FunctionFieldGeneration/` must be empty; `ε : LaurentSeries` must not occur |

### 11.8 Order of work

0. ~~The linear-disjointness lemma first.~~ **Not on the critical path**: it is established and
   shelved (`Reserve/ModularCurve/FunctionFieldGeneration/BaseChange.lean`, §11.4), and the fold does
   not consume it. Banked, not scheduled.
1. The fold: declare `[Algebra κ κ']`/`σ`, move the slot side to `κ'`, keep the pushed objects,
   delete `hε`/`hεq`; the flat `Rat`/`CharP`/`Descent`/`Nonmembership` call sites move with them.
   `PrimeStep` moves in the same change and keeps its present proof (§11.5, default).
2. (Optional, only with a reason on the record) the A-side prime step: port the peeling, drop
   `PkgAt` from the membership, delete the slot-list clause of `exists_transported_minpoly` and the
   `huniq` that consumed it.
3. Bookkeeping: the compile-time probe re-pointed, the presentation re-rendered if a quoted line
   moved, the notes updated. The refactor is measured by its consumers, not by the statement
   checker or the unwired register (`porting-playbook.md`, top matter).

### 11.9 What is *not* part of the fold

`PkgAt` keeps both clauses; `Tight`/`Gen`/`Hall` keep their names and are not rewritten; the
`PkgAt`-vs-`Hall` bridge (`hall_pkgAt`, `gen_iff_levelField`, `pkg_pkgAt`) is untouched; the
prime-power tower (`Nonmembership.lean`), `DegreeStep`, `Generation` and the capstone are
untouched; `Defs/` is unchanged; the base-change dictionary is *shelved* (§11.4), not written into
the theory, and (5.3) is not written; and no pinned statement's text changes (`sv`'s *body* changes; its type does not, and its pin text is the theorem
`sv_eq_pin`).
