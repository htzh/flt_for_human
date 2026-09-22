# Topic 4: the generic kernel

**Audience.** A fresh session taking the fourth topic of the
`functionFieldGeneration` effort. Layer 0, the `jq`-coefficients topic, the
conditional capstone and the interface tier are done
([logs/ffg-port.md](../../logs/ffg-port.md) §0). Read
[studies/flt-ffg-field-theory.md](../../../studies/flt-ffg-field-theory.md) §0–§4 first —
this topic is that survey's recommendation — then
[porting-playbook.md](../../porting-playbook.md) §3–§5 and §7 for the method.

**Goal.** Two things:

1. a new generic module, `FLTForHuman/FieldTheory/CommonRoot.lean` (name
   suggestive), holding the three `Polynomial.*` lemmas that are the mathematical
   engine of this segment — stated over an arbitrary `F ⊆ L`, mathlib-only,
   `sorry`-free, with statements verbatim from their pin wrappers;
2. prove `relfinrank_modularFunctionField` outright, discharging it from
   `Spine.lean`'s `Inputs` (**8 → 7** fields).

## 1. Why this topic, and what is settled

The survey measured where the segment's mathematics actually lives: the generic
kernel is **~166 lines, mathlib-absent, and is the engine of the whole proof** —
math/010 §4 *is* the unique-common-root principle, §6's non-membership *is*
"constant on enough points", and §6's `p+1`/`p` degree steps *are* the
cyclic-automorphism criterion. It sits **under** the 24-node remainder and under
`Spine`'s `Inputs`, and it is currently in neither mathlib nor the port. It is the
highest insight-per-line artifact available in this segment.

- **Settled: a new top-level area, `FLTForHuman/FieldTheory/`.** The three lemmas
  are generic over `F ⊆ L` and mention no curve, so they are the port's first
  *shared* material — the place for anything that is neither `Elliptic/` nor
  `ModularCurve/`. This also settles where a future `ModularCurve` theory's
  generic prerequisites go: here, not into a theory directory.
- **Settled: statements are the pin's, verbatim.** Each has a `Theorems/` wrapper,
  so `spec/check_flt_statements.py` verifies them rather than exempting them. Add
  the three wrappers to `SOURCES`.
- **Settled: Tier 1's generic restatements are *not* ported.** The survey's Tier 1
  is FLT's monomorphic restatement of mathlib's `IntermediateField` API, and it
  is *duplicated and private inside the big proof files* (`w1_relfinrank_insert`
  appears in two files; `aeval_intermediateField_eq_zero` in several). It has **no
  consumer** until a remainder peel needs it, and this port's own rule is that a
  lemma whose only consumer is itself is not ported. It belongs with the peel that
  uses it. The one exception is the next item.
- **Settled: `relfinrank_modularFunctionField` *is* in scope**, because it is the
  one Tier-1 bridge with a live consumer — it is the third `cites = 0` `Inputs`
  field, 31 lines, and `Spine`'s `relfinrank_full_of` calls it. Proving it shrinks
  the debt.
- **Settled: the other seven `Inputs` fields are untouched.**

## 2. The scouted inventory

### The generic kernel

All three live in **one** pin file, `P2M/Sol/S_Polynomial_mem_range_of_unique_common_root.lean`
(182 lines) — the other two `S_Polynomial_*` files are copies of it — and none
uses a private helper, so each is self-contained.

| declaration | pin lines | indeg | mathlib's nearest, and why it is not a substitute |
|---|---|---|---|
| `Polynomial.mem_range_of_unique_common_root` | 11–56 | 10 | `Splits.mem_range_of_isRoot` handles *one* root of *one* splitting polynomial; this is the two-polynomial common-root criterion |
| `Polynomial.mem_range_of_eval_eq_const` | 57–75 | <5 | `eq_zero_of_natDegree_lt_card_of_eval_eq_zero'` is the zero case; this is the "the constant value lies in the base" corollary |
| `Polynomial.irreducible_of_transitive_ringAut` | 76–178 | 5 | mathlib has irreducibility via `natDegree` divisors and via the Galois/`Normal` API, not this cyclic-automorphism criterion |

The statements, verbatim from the wrappers:

```lean
theorem Polynomial.mem_range_of_unique_common_root {F L : Type*} [Field F] [Field L]
    [Algebra F L] (A B : Polynomial F) (hA : A ≠ 0)
    (hAs : (A.map (algebraMap F L)).Splits) (hAnd : (A.map (algebraMap F L)).roots.Nodup)
    (x : L) (hxA : Polynomial.aeval x A = 0) (hxB : Polynomial.aeval x B = 0)
    (huniq : ∀ y : L, Polynomial.aeval y A = 0 → Polynomial.aeval y B = 0 → y = x) :
    x ∈ (algebraMap F L).range

theorem Polynomial.mem_range_of_eval_eq_const {F L : Type*} [Field F] [Field L]
    [Algebra F L] (g : Polynomial F) (x : L) (s : Finset L)
    (hcard : g.natDegree < s.card) (hval : ∀ y ∈ s, Polynomial.aeval y g = x) :
    x ∈ (algebraMap F L).range

theorem Polynomial.irreducible_of_transitive_ringAut {F L : Type*} [Field F] [Field L]
    [Algebra F L] (P : Polynomial F) (hP : P.Monic)
    (hPs : (P.map (algebraMap F L)).Splits) (σ : L ≃+* L)
    (hσ : ∀ a : F, σ (algebraMap F L a) = algebraMap F L a) (y₀ : L) (r : ℕ → L) (n : ℕ)
    (hroots : (P.map (algebraMap F L)).roots = y₀ ::ₘ (Multiset.range n).map r)
    (hnodup : (P.map (algebraMap F L)).roots.Nodup)
    (hcycle : ∀ i < n, σ (r i) = r ((i + 1) % n))
    (hy₀ : y₀ ∉ (algebraMap F L).range) : Irreducible P
```

Notes for the transcription, so none of it has to be rediscovered:

- the module needs `Mathlib.Algebra.Polynomial.Splits`,
  `…FieldDivision` (the pin's imports); nothing from the port;
- the third is the substantial one at ~103 lines; the first is ~46 and the second
  ~19. The `RingAut` argument is `L ≃+* L` (a *ring* equivalence fixing `F`
  pointwise), not `L ≃ₐ[F] L` — keep the pin's form;
- docstrings should name the transported principle ("split squarefree with a
  unique common root ⇒ the root is rational", "constant on enough points",
  "a base-fixing automorphism cycling all but one root ⇒ irreducible") and point
  at math/010 §4 / §6, since those are where the lemmas are consumed.

### The peel

`relfinrank_modularFunctionField`, pin `S_ModularCurve_relfinrank_modularFunctionField.lean`
(31 lines), `cites = 0`, indeg 7:

```lean
theorem relfinrank_modularFunctionField (N : ℕ) [NeZero N] :
    IntermediateField.relfinrank ℚ⟮jq⟯ (modularFunctionField N) =
      Module.finrank ℚ⟮jq⟯ (IntermediateField.adjoin ℚ⟮jq⟯ ({jqN N} : Set (LaurentSeries ℚ)))
```

Its pin proof is `relfinrank_eq_finrank_of_le` + `IntermediateField.extendScalars_adjoin`
(both mathlib) applied to our `adjoin_jq_le` (`Defs/Fields.lean`) — so it needs
nothing new. It is *instantiated*, so it goes in `Defs/Fields.lean` beside the
fields, **not** in `FieldTheory/`.

## 3. What is different about this topic

- **It is the port's first generic module.** Everything so far has been
  transcribed from a pinned source that dictates the statements; here the
  statements are still the pin's, but the *content* is a general principle about
  field extensions that would be at home in mathlib. If any of the three proves
  to need an assumption the pin's statement does not carry, that is a finding
  worth reporting, not a licence to restate it.
- **The consumer is the remainder, and the remainder is not being proved.** So
  the lemmas' immediate use in this port is `relfinrank_modularFunctionField`
  (via the Tier-1 bridges *it* needs, which are mathlib's) and the wire tests in
  §4. Do not be tempted into the 2,002-line descent file: this topic proves the
  engine, not the machine.
- **`Spine.lean` changes only by subtraction.** `Inputs` loses one field and
  `relfinrank_full_of` calls the real lemma instead of a field. Nothing else in
  the structure moves; the capstone keeps its shape.

## 4. Verification and the wire test

Beyond the standard checks, two wire tests, because "the module compiles" has
twice in this project said nothing about whether anything is *connected*:

1. **Instantiation.** For each of the three, a small concrete use over a real
   extension — e.g. `ℚ ⊆ ℂ`, or a quadratic extension — that exercises the
   hypotheses and shows the lemma is non-vacuous. These belong in
   `spec/ModularCurveConsumer.lean`'s Zone A style (a checked example, not a
   `sorry`), or in the module's own `#check`-style section; say in the report
   which you chose.
2. **The peel, cross-module.** `relfinrank_modularFunctionField` proved in
   `Defs/Fields.lean` and *used* by `Spine.lean` — which is a genuine
   cross-module composition and the thing that reduces `Inputs`.

## 5. Budget

**2 goal rounds, checkpoint at 1.** The three lemmas are ~166 lines and the peel
is 31; the record has one round covering 9, 24, 29 and 69 declarations. One round
is plausible, two is the "something structural is wrong" threshold — and the
likeliest cause would be the irreducibility lemma, which is the only one of the
three with real length.

**Stop early on**: a statement that will not match its wrapper; the
`RingAut`/`AlgEquiv` distinction forcing a restatement; or the peel needing
anything beyond mathlib's two `IntermediateField` lemmas.

## 6. Definition of done

- [ ] `FLTForHuman/FieldTheory/CommonRoot.lean` with the three lemmas, public,
      statements verbatim from the pin wrappers, docstrings naming each principle
      and pointing at math/010 §4 / §6.
- [ ] `relfinrank_modularFunctionField` public in `Defs/Fields.lean`;
      `Spine.lean`'s `Inputs` down to **7** fields, `relfinrank_full_of` calling
      the real lemma.
- [ ] `lake build` green, 0 warnings, no `sorry`; `#print axioms` on
      `functionFieldGeneration_of` still only `propext, Classical.choice,
      Quot.sound`.
- [ ] `spec/check_flt_statements.py`: the three `Thm_Polynomial_*` wrappers plus
      `Thm_ModularCurve_relfinrank_modularFunctionField` added to `SOURCES`;
      verified count 146 → **~150**, 0 mismatched; `OWN_PROOFS` unchanged.
- [ ] both wire tests from §4, with the instantiation's location named.
- [ ] Consumer unchanged (0 errors, one `sorry`) except any prose that states a
      field count.
- [ ] `logs/ffg-port.md` gains a §2f (cost) and updates the §8.4 field table
      8 → 7 with the discharged row struck through; README module table (a new
      `FieldTheory/` area) and PORTING-FFG status updated.
- [ ] A note in the log on the new area: `FLTForHuman/` now has `Elliptic/`,
      `ModularCurve/` and `FieldTheory/`, the last being where future generic
      prerequisites live.

## 7. Reporting back

Same shape as the previous topics. Three things specifically:

1. **Was the kernel as self-contained as scouted?** The survey says the three
   lemmas are one 182-line file with no private helpers; if any of them turned out
   to need support, name it — that is the difference between "the generic core is
   180 lines" and "it looked like 180 lines".
2. **The engine mapping, checked.** The survey asserts that math/010 §4 *is*
   principle 1, §6's non-membership *is* principle 2, and §6's degree steps *are*
   principle 3. Having now read the three lemmas, say whether that holds — a
   mismatch would mean the remainder's real engine is somewhere else, which is
   the single most useful thing this topic could discover.
3. **What the peel cost**, and whether `Inputs` at 7 changes the shape of the
   remaining debt (the 1,000–2,000-line nodes are now a larger fraction of what is
   assumed).
