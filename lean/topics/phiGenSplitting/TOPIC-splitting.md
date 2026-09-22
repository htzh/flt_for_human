# Topic 13: the consequence — uniqueness and the splitting

**Status: executed plan (2026-09-22) — T13 is done and the Φₚ splitting cone is
closed.** This was the **last topic of the cone**. T11 built the datum, T12 proved
its properties, and T13 drew the consequence: the datum is unique, and it splits
into the `p+1` conjugates. The cone's headline `PhiGen.splits_prime_at_slot` is a
ported theorem and the 44-node closure of
[PORTING-PhiGen.md](../PORTING-PhiGen.md) is discharged. The execution record
is §10 below and [logs/phiGen-port.md](../../logs/phiGen-port.md) §13.

The plan is [PORTING-PhiGen.md](../PORTING-PhiGen.md) §5–§6; the mathematics is
[math/010](../../../math/010-function-field-generation.md) §3 and
[base/006](../../../base/006-the-modular-equation.md) §3 and §6 steps 4–5.

> **Build discipline — read this first.** Every build is bounded and a blow-up is
> quarantined, not waited on. Measured with mathlib prebuilt: a green
> `lake env lean <module>` of this size is **~4 s**, `lake build <module>` with
> deps cached **~2–5 s**, and a `whnf`/heartbeat timeout at the default cap
> **errors in ~15–20 s** — it does not hang.
>
> - Run every build under a bound: `timeout 60 lake env lean <file>`,
>   `timeout 120 lake build <module>`. Non-return at 60 s is a blow-up.
> - **Quarantine immediately.** On a timeout, comment the declaration out and
>   bisect, or reproduce in the gitignored `Scratch.lean` with
>   `set_option diagnostics true`. Do not re-run the same file hoping for a
>   different result.
> - **Never raise `maxHeartbeats`.** The cap already fails in under 20 s; raising
>   it turns that into an unbounded wait. The usual cause is a `FunLike`-quantified
>   lemma instantiated at a bare function type (`DFunLike.coe` unfolds without
>   bound) — restate it over the concrete function instead. T5's log §2.2 has the
>   worked example.

**Audience.** A fresh session taking this topic. Read, in this order:

1. [PORTING-PhiGen.md](../PORTING-PhiGen.md) §1 (the wrapper), §3(f) and §5;
2. [base/006 §3 and §6 steps 4–5](../../../base/006-the-modular-equation.md) —
   uniqueness and the general-`N` step;
3. [math/010 §3](../../../math/010-function-field-generation.md) — the splitting
   statement of record;
4. [TOPIC-irreducibility-symmetry.md](TOPIC-irreducibility-symmetry.md) (T12, the
   immediate predecessor) and [logs/phiGen-port.md](../../logs/phiGen-port.md)
   §12 — T12's interfaces and the wrapper-spelling rule;
5. [porting-playbook.md](../../porting-playbook.md) §2 (deduplicate at the
   source), §3.9 and §3.11.

## 1. The mathematics in one page

### 1.1 Uniqueness and the degree

`ModularPolynomialData p` bundles a monic `Φ ∈ ℤ[X][Y]` of `Y`-degree
`ψ(p) = p+1` with `Φ(j(q), j(q^p)) = 0`. Two such data are equal:

```lean
theorem ModularCurve.ModularPolynomialData.eq_of_prime (p : ℕ) [hp : Fact (Nat.Prime p)]
    (d d' : ModularPolynomialData p) : d = d'
```

Both `toAdjoin` images are monic, annihilate `j(q^p)` (so are divisible by its
minimal polynomial), and have degree `p+1 = ψ(p)`; a monic polynomial of minimal
degree annihilating an element *is* its minimal polynomial, so both equal
`` $`\mathrm{minpoly}_{\mathbb{Q}(j)}(j(q^p))`$ `. The degree input is
`finrank_adjoin_jqN_eq_of_prime`:

```lean
theorem ModularCurve.finrank_adjoin_jqN_eq_of_prime (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] :
    Module.finrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
      (IntermediateField.adjoin (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
        ({jqN ℓ} : Set (LaurentSeries ℚ))) = ℓ + 1
```

which reads `` $`[\mathbb{Q}(j)(j(q^\ell)) : \mathbb{Q}(j)] = \ell+1`$ `` off the
irreducible datum T12's `exists_phiIrreducible_evalSymm` supplies and
`dedekindPsi_prime`. Both files are small (52 + 73 pin lines) and are pure glue
over T11/T12.

### 1.2 The splitting at a prime

```lean
theorem ModularCurve.PhiGen.splits_of_prime {K : Type*} [Field K] [Algebra ℚ K]
    (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p)
    (data : ModularPolynomialData p) :
    data.Φ.map (((coeffEmb K).comp (qExpand ℚ p)).comp evalAtJ) = phiProd p (conj p ζ)
```

This is base/006 §3's identity: `` $`\Phi_p(j(q^p), Y)`$ `` — the `X`-slot is
`j(q^p)`, because `qExpand ℚ p` acts on the `X`-coefficients — equals the
conjugate product `` $`\prod_i (Y - \mathrm{conj}_i)`$ ``, whose roots are
`` $`j(q^{p^2})`$ `` (the slot the twist fixes) and `` $`\zeta^b\,j(q)`$ `` for
`b < p`. The proof is the join of the whole cone:

- **over `CyclotomicField p ℚ`** (`splits_of_prime_cyclotomicField`), with
  `ζ₀ = cycUnit p` a primitive root: T11's (a) `exists_phiGenDescends` gives the
  descended family `c`; T9's `PhiGenDescends.intCoeffs` gives `IntCoeffs`; T8's
  `mem_adjoin_jq_of_phiGenDescends` gives membership in `ℚ[jq]`; T11's
  `exists_modularPolynomialData_coeff_eq` assembles a datum `data₀` with
  `evalAtJ (data₀.Φ.coeff k) = c k`; **`eq_of_prime` identifies `data` with
  `data₀`**; and T11's `splits_of_coeff_evalAtJ_eq` rewrites the product into
  `phiProd p (conj p ζ₀)`. So `eq_of_prime` is not a side lemma — it is the step
  that makes the *arbitrary* input `data` the *constructed* one.
- **for arbitrary `K` and `ζ`**: an algebra embedding
  `` $`\sigma : \mathrm{CyclotomicField}\,p\,\mathbb{Q} \to_{\mathbb{Q}} K`$ ``
  with `σ ζ₀ = ζ` (from `IsPrimitiveRoot.embeddingsEquivPrimitiveRoots` and
  `Polynomial.cyclotomic.irreducible_rat`), and the cyclotomic identity pushed
  through `coeffMap σ`. The transport needs
  `coeffMap (qTwist u f) = qTwist (σ u) (coeffMap σ f)`,
  `coeffMap σ (coeffEmb x) = coeffEmb x` and `coeffMap σ (conj p ζ i) = conj p (σ ζ) i`.

### 1.3 The splitting at a general slot

```lean
theorem ModularCurve.PhiGen.splits_prime_at_slot {K : Type*} [Field K] [Algebra ℚ K]
    (N : ℕ) [NeZero N] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N) (p : ℕ)
    [hp : Fact (Nat.Prime p)] (hpN : p ∣ N) (data : ModularPolynomialData p)
    (e : ℕ) [NeZero e] (u : Kˣ) :
    data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
      (qExpand K (p * e) (qTwist (u ^ p) (coeffEmb K jq)))) =
      (Polynomial.X - Polynomial.C (qExpand K (p * (p * e)) (qTwist (u ^ (p * p)) (coeffEmb K jq)))) *
        ∏ b ∈ Finset.range p,
          (Polynomial.X - Polynomial.C (qExpand K e (qTwist (u * ζ ^ (b * (N / p))) (coeffEmb K jq))))
```

The cone's headline, math/010 §3's formula with the level datum `(e, u)`:
`` $`\Phi_p(j(u^p q^{pe}), Y) = (Y - j(u^{p^2} q^{p^2e}))\prod_b (Y - j(u\zeta^b q^e))`$ ``.
It is a one-step transport of `splits_of_prime`: `ζ^(N/p)` is a primitive `p`-th
root (`isPrimitiveRoot_pow_div`), and the identity is pushed through the ring hom
`(qExpand K e) ∘ qTwist u`, with
`` $`\mathrm{TS}\,K\,m\,w = j(w\,q^m)`$ `` (`Defs/TS.lean`) rewriting the
arguments. The three substitutions are exactly `iota_jq`, `qExpand_qTwist_TS`,
and the `conj_zero_eq`/`conj_succ_eq` readings of the conjugates as `TS` values.

## 2. The scouted inventory

| pin file | lines | content |
|---|---|---|
| `S_ModularCurve_finrank_adjoin_jqN_eq_of_prime.lean` | 52 | `finrank_adjoin_jqN_eq_of_prime` |
| `S_ModularCurve_ModularPolynomialData_eq_of_prime.lean` | 73 | `eq_of_prime` (+ `phiIrreducible_of_prime`) |
| `S_ModularCurve_PhiGen_splits_of_prime.lean` | 353 | `splits_of_prime` + a large prelude |
| `S_ModularCurve_PhiGen_splits_prime_at_slot.lean` | 288 | `splits_prime_at_slot` + a large prelude |

Out of scope: the two char-`p` variants
`S_ModularCurve_PhiGen_splits_prime_at_slot_of_isPrimitiveRoot.lean` and
`S_ModularCurve_PhiGen_splits_prime_of_isPrimitiveRoot.lean` (607 lines each and
byte-identical to each other except the final `solution`, over `jqModC`,
`[Field K]` with no `[Algebra ℚ K]`). They are not in the 44-node closure, the
cone's headline does not import them, and `jqModC` is not ported at all; they
belong to the Characteristic-`p` model effort, not this cone. Their distinctive
content is roughly 550–600 lines plus the `jqModC` interface files, so they are
a separate future topic, not T13.

### 2.1 The shared prelude, mapped — and how much of it is dead

Both big files open with the same `TS` prelude. The port already carries its core
in `Defs/TS.lean` (`TS`, `TS_coeff_mul`, `TS_coeff_of_not_dvd`, `TS_coeff_neg`,
`TS_coeff_of_lt`, `TS_ne_zero`, `TS_injective`, `qTwist_TS`, `qExpand_TS`,
`TS_congr` — ten declarations, verbatim from the same pin block), and
`coeffEmb_qExpand` is `Defs/Laurent.lean`'s. Of the rest:

| declaration | in `splits_of_prime` | in `splits_prime_at_slot` | live? |
|---|---|---|---|
| `iota_jqN` | 95 | 93 | **dead in both** (never used) |
| `iota_jq` | 99 | 97 | used by `splits_prime_at_slot` (154) |
| `conj_zero_eq` | 102 | 100 | used (transport and at-slot) |
| `conj_succ_eq` | 105 | 103 | used (transport and at-slot) |
| `qTwist_iota_of_pow_eq_one` | 108 | 106 | **dead in both** |
| `qTwistEquiv`, `coe_qTwistEquiv` | 123–140 | — | **dead** |
| `qTwist_TS_one_cycle` | 142 | — | **dead** |
| `phiProd_conj_eq`, `roots_phiProd_conj`, `roots_phiProd_conj_nodup` | 150–186 | — | **dead** (self-contained chain) |
| `phiAtSeed` + 7 lemmas | 214–257 | — | **dead** (never referenced after 257) |
| `exists_isPrimitiveRoot_cyclotomicField`, `cycUnit`, `cycUnit_spec`, `cycUnit_pow` | 188–203 | — | used by `splits_of_prime` |
| `coeffMap_qTwist`, `coeffMap_coeffEmb_algHom`, `coeffMap_TS`, `coeffMap_conj`, `map_coeffMap_phiProd` | 273–301 | — | used |
| `isPrimitiveRoot_pow_div` | — | 123 | used |
| `qExpand_qTwist_TS` | — | 135 | used |
| `prod_form_ne_zero`, `roots_prime_at_slot*`, `isRoot_prime_at_slot_iff` | — | 189–284 | **dead for the headline** (the theorem ends at 180; the block is a self-contained root-description chain for other consumers) |

So the pin spends ~200 lines of prelude on declarations the cone's two exported
theorems never use. They are not cone nodes (`PORTING-PhiGen.md`'s Appendix A
lists none of them); the char-`p` variants and the FFG root-description topic
carry their own copies. **T13 ports the live part and records the dropped
declarations**; a later FFG topic that wants `roots_phiProd_conj*` or
`roots_prime_at_slot*` ports them from its own source.

### 2.2 The public statements

Verbatim from their wrappers: `finrank_adjoin_jqN_eq_of_prime` and
`eq_of_prime` (above), `splits_of_prime` (above), and `splits_prime_at_slot`
(above). All four are wrapper-backed; the shared prelude declarations are hidden
and stay `private` in the port.

## 3. The mathlib-first audit and redundancy removal

Audited against `v4.34.0`. This is the cone's smallest big topic: almost all the
mathematics is already in T8–T12; T13 is assembly plus one transport.

| pin piece | mathlib / port | verdict |
|---|---|---|
| `eq_of_prime`, `finrank_adjoin_jqN_eq` | `minpoly.dvd`, `minpoly.eq_of_irreducible_of_monic`, `Polynomial.eq_of_monic_of_dvd_of_natDegree_le`, `Polynomial.map_injective`, `IntermediateField.adjoin.finrank`; T11's `evalAtJ_injective`, T12's `exists_phiIrreducible_evalSymm`, `dedekindPsi_prime` | port (glue, ~60 lines) |
| the `TS` core | **already public in `Defs/TS.lean`** (ten declarations) | import |
| `coeffEmb_qExpand` | **already public in `Defs/Laurent.lean`** | import |
| `iota_jq`, `conj_zero_eq`, `conj_succ_eq` | `qExpand_coeff_mul`, `qTwist_one_apply`, `conj_zero`/`conj_succ`, `TS` | port once (~10 lines) |
| `coeffMap_*` transport | `coeffMap`, `coeffMap_qExpand`, `coeffMap_qTwist` (mathlib-free, port's `Defs/Laurent`), `Polynomial.map_map` | port (~35 lines) |
| `cycUnit`/`exists_isPrimitiveRoot_cyclotomicField` | `CyclotomicField.isCyclotomicExtension`, `IsCyclotomicExtension.exists_isPrimitiveRoot` | port (short) |
| `splits_of_prime_cyclotomicField`, `splits_of_prime` | T8–T12's outputs + `IsPrimitiveRoot.embeddingsEquivPrimitiveRoots`, `Polynomial.cyclotomic.irreducible_rat` | port (~60 lines) |
| `splits_prime_at_slot` | `isPrimitiveRoot_pow_div` (`IsPrimitiveRoot.pow_of_dvd`), the `TS` rewrites | port (~55 lines) |
| dropped prelude | — | **do not port** (§2.1) |

**Redundancy removal, concretely:**

1. **The `TS` core is already ported.** T13 imports `Defs/TS.lean`; it must not
   re-declare `TS_coeff_*`/`TS_injective`/`qTwist_TS`/`qExpand_TS`/`TS_congr`.
2. **The shared prelude is written once.** `iota_jq`, `conj_zero_eq`,
   `conj_succ_eq` appear in both pin files; the port writes them once in the
   splits module.
3. **~200 lines of dead prelude are dropped** (§2.1). This is the topic's main
   saving and should be reported with the per-declaration list.
4. **`eq_of_prime`'s private `evalAtJGen_injective`/`aeval_jqN_toAdjoin`** are T12's
   public declarations; import them (the pin's 52/73-line files each re-prove or
   re-import small helpers).
5. **The `attribute [-simp]` pragma** the toolchain emits is not ported.
6. **Wrapper spellings.** Any public declaration the checker verifies is matched
   against the `Theorems/` wrapper, not the `S_` file's section variables — the
   rule T7–T12 each had to re-learn (T12's log §12.4).
7. **Promote the cyclotomic helpers.** `FunctionFieldGeneration/Spine.lean`
   carries private twins of the pin's `exists_isPrimitiveRoot_cyclotomicField`,
   `cycUnit`, `cycUnit_spec` and `isPrimitiveRoot_pow_div` (the FFG spine proves
   them for its own use). Promote them, with the new `cycUnit_pow`, to a shared
   `Defs/` module so the spine, T13 and the future `jqModC` topic use one copy.
8. **Promote `coeffMap_qTwist`.** It is a private twin in
   `PhiGenIntegrality.lean` and `PhiGenDescent.lean`; the `of_prime` transport
   block wants its general form. State it once in `Defs/Twist.lean`.

## 4. Dependencies and the division

T13 is the join of the whole cone. Its imports are all landed:

| needs | from |
|---|---|
| `exists_phiGenDescends` | T11 `PhiGenDescent.lean` |
| `PhiGenDescends.intCoeffs` | T9 `PhiGenIntegrality.lean` |
| `mem_adjoin_jq_of_phiGenDescends` | T8 `ModularForms/PhiGenDescends.lean` |
| `exists_modularPolynomialData_coeff_eq`, `splits_of_coeff_evalAtJ_eq` | T11 `ModularPolynomialAssembly.lean` |
| `exists_phiIrreducible_evalSymm`, `evalAtJGen_injective`, `aeval_jqN_toAdjoin`, `minpoly_jqN_eq` | T12 `ModularPolynomialProperties.lean` / `ModularPolynomialIrreducible.lean` |
| `evalAtJ_injective` | T11 `PhiGenDescendsStructure.lean` |
| `TS` and its API | `Defs/TS.lean` |
| `coeffMap`/`coeffEmb`/`qExpand`/`qTwist` API | `Defs/Laurent.lean`, `Defs/Twist.lean` |

There is nothing left for a later topic in this cone. T13 hands the *FFG* effort
(not this one) a ported `splits_prime_at_slot`; PORTING-FFG §7.8's T14–T19 then
prove the `Inputs` fields from it.

## 5. Verification and the wire test

1. **`#print axioms`** on all four public declarations: only
   `propext, Classical.choice, Quot.sound`.
2. **Statement checker.** Add the four `Theorems/` wrappers
   (`Thm_ModularCurve_finrank_adjoin_jqN_eq_of_prime`,
   `Thm_ModularCurve_ModularPolynomialData_eq_of_prime`,
   `Thm_ModularCurve_PhiGen_splits_of_prime`,
   `Thm_ModularCurve_PhiGen_splits_prime_at_slot`). T12 left the count at **233**;
   T13 raises it to **237**, 0 mismatched. If any shared-prelude declaration is
   exported rather than kept `private`, add
   `P2M/Sol/S_ModularCurve_PhiGen_splits_prime_at_slot.lean` as its comparable
   copy; prefer keeping them `private`.
3. **`PORT_FILES`** gains T13's modules.
4. **The wire test — the capstone of the cone.** T13 has the first wire that
   closes the whole chain unconditionally: take `p = 2`, `N = 2`, `e = 1`, `u = 1`
   and `ζ := cycUnit 2` (or any primitive square root in `ℂ`), and let `data` come
   from T12's `exists_phiIrreducible_evalSymm 2`. Then
   `splits_prime_at_slot 2 ζ (cycUnit_spec 2) 2 dvd_rfl data 1 1` is a genuine
   instance of the cone's headline, with no unported hypothesis. `eq_of_prime`
   (two data from `exists_phiIrreducible_evalSymm 2` are equal) and
   `finrank_adjoin_jqN_eq_of_prime 2` are likewise unconditional and give smaller
   concrete checks.
5. **Consumer.** Add **Zone K** for T13 (T12 took Zone J); the file is
   `spec/ModularCurveConsumer.lean`, run by hand, 0 errors. The consumer's one
   remaining `sorry` — the *unconditional* `FunctionFieldGeneration N` — is the
   FFG `Inputs` gap, not this cone's; T13 changes it only by making the cone's
   input a theorem. Say so explicitly in the zone's comment.

## 6. Dedup

- **The shared `TS` prelude:** the port already has `Defs/TS.lean`'s ten
  declarations; the three live extras (`iota_jq`, `conj_zero_eq`, `conj_succ_eq`)
  are written once for both theorems.
- **~200 lines of dead prelude dropped** (§2.1): `iota_jqN`,
  `qTwist_iota_of_pow_eq_one`, `qTwistEquiv`/`coe_qTwistEquiv`,
  `qTwist_TS_one_cycle`, `phiProd_conj_eq`/`roots_phiProd_conj`/`roots_phiProd_conj_nodup`,
  `phiAtSeed` + its seven lemmas, and `prod_form_ne_zero`/`roots_prime_at_slot*`/
  `isRoot_prime_at_slot_iff`.
- **The 2× duplication of the prelude** between the two pin files disappears: one
  shared module.
- **The cone's node list is complete:** after T13 every one of the 44 nodes is
  public and every wrapper is verified; the topic's report should mark the cone
  closed.
- **Two cross-topic promotions** (§3.7–3.8): the cyclotomic helpers, currently
  private twins in the FFG spine, and `coeffMap_qTwist`, private twins in T9/T11,
  become shared `Defs/` lemmas and are reused by the spine and later topics.

## 7. Module split (recommended)

| module | public surface | pin |
|---|---|---|
| `FLTForHuman/ModularCurve/ModularPolynomialUniqueness.lean` | `finrank_adjoin_jqN_eq_of_prime`, `ModularPolynomialData.eq_of_prime` (+ `phiIrreducible_of_prime` if useful) | 52 + 73 |
| `FLTForHuman/ModularCurve/PhiGenSplits.lean` | the shared `iota_jq`/`conj_zero_eq`/`conj_succ_eq` (private), `splits_of_prime`, `splits_prime_at_slot` | the live part of 353 + 288 |

The names are suggestions. `PhiGenSplits.lean` imports
`ModularPolynomialUniqueness.lean`, `Defs/TS.lean`, T8–T12's modules, and
`Mathlib.NumberTheory.Cyclotomic.Basic` +
`Mathlib.RingTheory.Polynomial.Cyclotomic.Roots` (for the embedding reduction).

## 8. Budget and stop-early

Distinctive pin content is `52 + 73 + 353 + 288 = 766` lines, but ~200 are dead
(§2.1); the live port is plausibly **300–400 lines** including headers and the
`Defs/TS.lean` import, ratio ≈ 0.5–0.6 — the cone's cheapest topic. Budget **1–2
goal rounds** (T11 and T12 each took one).

**Stop early on:** the embedding reduction
(`IsPrimitiveRoot.embeddingsEquivPrimitiveRoots` + `Polynomial.cyclotomic.irreducible_rat`)
not elaborating in the port's `v4.34.0` spelling; `Units.map`/`coeffMap` coercion
mismatches in the transport; `Polynomial.ringHom_ext'` needing the
`RingHom.ext_int` shape the pin uses; or `Polynomial.eval₂RingHom`'s
`Int.castRingHom` argument not matching `evalAtJ`. If the cyclotomic-to-`K`
reduction is the sticking point, spike it in `Scratch.lean` first: it is the only
place in T13 with genuine transport content. Two smaller shape notes: installing
`IsCyclotomicExtension`/`IsGalois`/`FiniteDimensional` at `CyclotomicField p ℚ` in
`splits_of_prime_cyclotomicField` is the heaviest single step (the pin needs three
`haveI`s; T12's `exists_phiIrreducible_evalSymm` already does exactly this and can
be copied), and the port's `coeffEmb_qExpand` takes the field explicitly — call
`coeffEmb_qExpand K n x`, as `ModularPolynomialIrreducible.lean` does.

## 9. Definition of done

- [ ] `FLTForHuman/ModularCurve/ModularPolynomialUniqueness.lean`:
      `finrank_adjoin_jqN_eq_of_prime` and `ModularPolynomialData.eq_of_prime`
      public and verbatim.
- [ ] `FLTForHuman/ModularCurve/PhiGenSplits.lean`:
      `PhiGen.splits_of_prime` and `PhiGen.splits_prime_at_slot` public and
      verbatim; the shared prelude private and written once.
- [ ] the ~200 lines of dead pin prelude are **not** ported, and the log lists
      them with their pin lines.
- [ ] `lake build` green, 0 warnings, no `sorry`.
- [ ] `#print axioms` clean on all four public declarations.
- [ ] `spec/check_flt_statements.py`: four wrappers added, 233 → 237, 0
      mismatched; `PORT_FILES` gains the two modules.
- [ ] the capstone wire from §5.4 recorded, green in Zone K, with a note that the
      consumer's remaining `sorry` is the FFG `Inputs` gap.
- [ ] `PORTING-PhiGen.md` §5 marks T13 done and **the cone closed**; §2's node
      table is complete; the log gains T13's cost and the dead-code list; README
      module table gains the two modules and the cone's completion.
- [ ] report in the §10 shape.

## 10. Reporting back

1. **The dead prelude** — confirmed, and nothing in the list was needed. The port
   writes only `iota_jq`, `conj_zero_eq`, `conj_succ_eq` (private) on top of the
   already-ported `Defs/TS.lean`; the dropped declarations are `iota_jqN`,
   `qTwist_iota_of_pow_eq_one`, `qTwistEquiv`/`_apply`/`coe_qTwistEquiv`,
   `qTwist_TS_one_cycle`, `phiProd_conj_eq`, `roots_phiProd_conj`,
   `roots_phiProd_conj_nodup`, `phiAtSeed` + 7 lemmas, and the at-slot roots API
   (`prod_form_ne_zero`, `roots_prime_at_slot*`, `isRoot_prime_at_slot_iff`) —
   ~200 lines.
2. **The cost** — **1 goal round**, 4 public + 12 `private`, **407 lines**
   (133 + 274), ratio **407/766 = 0.53**. Plus the promotion: 5 public cyclotomic
   roots in the new `Defs/Cyclotomic.lean` (58 lines), with both private twins
   deleted; checker 233 → 237 → 242.
3. **The capstone wire** — closed. `splits_prime_at_slot` instantiates at
   `K = CyclotomicField 2 ℚ`, `N = p = 2`, `e = u = 1`; the embedding reduction
   (`IsPrimitiveRoot.embeddingsEquivPrimitiveRoots` +
   `Polynomial.cyclotomic.irreducible_rat`) elaborated in the pin's spelling on
   the first build. Module 2's first build had no proof errors, only linter
   clean-up.
4. **The cone closed** — build 3863 jobs green, 0 warnings, no `sorry`; all four
   `#print axioms` clean; consumer Zone K 0 errors; checker 242 identical, 0
   mismatched, 0 missing. All 44 nodes are ported.
5. **Carried forward** — `coeffMap_qTwist` (T13's private copy duplicates T9's
   more general private one; T11's is a different statement) is left for a
   dedicated cleanup of the T9/T11 surfaces.

## 11. Where this sits

The topic is done. The cone's mathematics — (a) descent, (b) integrality and pole
bounds, (c) membership in `ℚ[j]`, (d) assembly and uniqueness, (e) irreducibility
and symmetry, (f) the splitting — is complete in `FLTForHuman/`, and every one of
the 44 nodes below `PhiGen.splits_prime_at_slot` is a ported theorem. The FFG
effort's remaining `Inputs` fields (PORTING-FFG §7.8's T14–T19) can now be proved
using `splits_prime_at_slot` as a theorem rather than an input.

Sizes are the deduplicated pin lines from
[PORTING-PhiGen.md](../PORTING-PhiGen.md) §6; the measured ratios across the
cone (T5–T13) are 0.53–1.79, and the cone's last topic is its cheapest.
