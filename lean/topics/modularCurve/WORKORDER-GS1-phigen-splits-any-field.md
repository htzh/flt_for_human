# WORKORDER-GS1 — the char-`p` (any-field) prime splitting of `Φ_p`, its roots API, and the ground that made it one module

Status: **landed 2026-10-25** (dispatched to the set's agent, reviewed by the manager).
Result: `ModularCurve/PhiGenSplitsAnyField.lean`, 489 lines, 19 declarations (9 public), build
6.9 s / 0 warnings, checker **9 ok / 0 mismatch / 0 missing / 0 own** (`--strict-markers`),
axioms `[propext, Classical.choice, Quot.sound]`, dedup 0 clusters; demand −2 nodes / −1,214 raw
lines. One deviation from this order: **four at-slot declarations are renamed** (§4 of the
record) because the pin's twin roots API cannot keep its plain names in one `ModularCurve`
namespace — Lean refuses the import of both modules. Record: [logs/phigen-splits-any-field.md](../../logs/phigen-splits-any-field.md).
Ground: [logs/ts-general-field.md](../../logs/ts-general-field.md).

The nodes (both in the D-S `--ds` demand):

| node | pin `S_` | raw lines | declares | citers |
|---|---|---:|---|---:|
| `ModularCurve.PhiGen.splits_prime_at_slot_of_isPrimitiveRoot` | `S_ModularCurve_PhiGen_splits_prime_at_slot_of_isPrimitiveRoot.lean` | 607 | 62 | 9 |
| `ModularCurve.PhiGen.splits_prime_of_isPrimitiveRoot` | `S_ModularCurve_PhiGen_splits_prime_of_isPrimitiveRoot.lean` | 607 | 62 | 2 |

The two `S_` files are **byte-identical** except for the 15 lines that spell their own name and
the final `solution`: one 607-line development, not two. Priced as one set with
`port_advise` + `port_plan`: 1,214 raw → 1,150 declaration lines → 579 removable duplicate
copies → 571 once-cost → 174 already in the port → **397 net new**, 44 trusted substitutions.
Part of that 397 was the `TS` prelude, which the manager has now removed from the bill (see §2).

## 1. What the mathematics is — and why it is not a duplicate of the ported pair

`ModularCurve.PhiGen.splits_of_prime` (`PhiGenSplits.lean`, ported) says
`Φ_p(j(q^p), Y) = ∏_i (Y - conj_i)` over a **`ℚ`-algebra** field. The two nodes here say the
same identity over an **arbitrary** field (`[Field K]`, no `[Algebra ℚ K]`), with the slot read
as `jqModC K` instead of `coeffEmb K jq`. They are therefore not instances of the ported
theorem — and the pin's own graph makes `splits_of_prime` a *premise* of both, which is exactly
what the proof does.

The proof is one transport engine (`ksplit*`, pin 267–486):

1. apply the ported `splits_of_prime` at `CyclotomicField p ℚ` with `cycUnit p`;
2. rewrite its `X`-slot as `phiAtSeed` (`ksplit_comp_evalAtJ`) and its `jq` as `jqModC`
   (`coeffEmb_jq`);
3. **pull the identity back** to the integral cyclotomic order
   `O := AdjoinRoot (cyclotomic p ℤ)` along the injective `O → CyclotomicField p ℚ`
   (`ksplitIota`, injective by `minpoly.dvd` + `map_cyclotomic_int`), using
   `coeffMap_injective` — this is `ksplit_integral`, the 47-line core;
4. **push it forward** to `K` along `AdjoinRoot.lift (Int.castRingHom K) ζ`
   (`ksplitLift`, `ksplitLift_root`, `ksplitLift_units_zeta`);
5. the at-slot form is step 1's conclusion pushed through `(qExpand K e).comp (qTwist u)`
   (`phiAtSeed_slot_prime_eq`), which is the same move the port's `splits_prime_at_slot` makes.

The second headline `splits_prime_of_isPrimitiveRoot` is the `e = u = 1` case of the at-slot one
(`qTwist_one_apply`, `qExpand_one_apply`, `Nat.mul_one`, `qExpand_congr`) — the same relation the
port already homes for the char-0 pair — and the pin proves it that way, from
`phiAtSeed_qExpand_prime_eq`.

## 2. The ground already landed (do not re-derive, do not re-open)

Landed by the manager on 2026-10-25, all green, all statement-checked:

1. **`Defs/TS.lean` is now general in the field.** `TS K e u := qExpand K e (qTwist u (jqModC K))`
   over `[Field K]` — the pin's own text at
   `S_ModularCurve_PhiGen_splits_prime_of_isPrimitiveRoot.lean:33` — with the whole API
   (`TS_coeff_mul` … `TS_injective`, `qTwist_TS`, `qExpand_TS`, `TS_congr`,
   `qExpand_qTwist_TS`, `coeffMap_TS`). The module gained its `spec-pin:` lines, left
   `PORT_FILES`, and `check_port.py` reads **15 ok / 0 mismatch / 0 own**. So **the char-`p`
   `TS` prelude of the pin files (lines 33–192) is now an import, not a transcription** —
   in particular `TS_injective` at `[Field K]`, which `roots_prime_at_slot_nodup` needs.
2. **`coeffEmb L jq = jqModC L` has one home in the definition layer**,
   `Defs/JqCoeff.lean`'s `coeffEmb_jq` (statement-checked against
   `Theorems/Thm_ModularCurve_coeffEmb_jq.lean:7`; the two `private` twins in
   `Analytic/CuspDichotomy.lean` and `Degree/JqCyclotomicConjugates.lean` are deleted, the
   `own:` rows of the latter's two `phiAtSeed_TS_eval*` are gone because those statements are
   now at the pin's general binders).
3. **The integral order exists**: `Defs/KatzLevelPCusps.lean` has
   `cyclRing R₀ p := AdjoinRoot (Polynomial.cyclotomic p R₀)`, `cyclRing_root_pow`,
   `cyclZeta : (cyclRing R₀ p)ˣ` with `@[simp] val_cyclZeta` and `cyclZeta_pow_eq_one` — over a
   general `CommRing R₀`. So the pin's `ksplit_root_pow` and `ksplitZeta` (23 lines) are **not
   written**: use `cyclRing ℤ p`, `cyclZeta ℤ p`, `cyclRing_root_pow ℤ p`, `val_cyclZeta`.
4. **The cyclotomic root of `CyclotomicField`**: `Defs/Cyclotomic.lean` has
   `exists_isPrimitiveRoot_cyclotomicField`, `cycUnit`, `cycUnit_spec`, `cycUnit_pow`,
   `isPrimitiveRoot_pow_div` — the pin's `ksplit_exists_isPrimitiveRoot`/`ksplitCycUnit`/
   `ksplitCycUnit_spec` (14 lines) are **not** written.
5. **The `TS` bridges and `phiAtSeed` API** are already public and general where it matters:
   `Defs/PhiAtSlot.lean` (`phiAtSeed`, `phiAtSeed_map`, `phiAtSeed_monic`,
   `phiAtSeed_natDegree`, `phiAtSeed_eval_map`, `phiAtSeed_eval_of_injective`,
   `phiAtSeed_jq_eval`, `phiAtSeed_jqN_eval`, `phiAtSeed_iota_eval`, the roots of `phiProd`),
   `Defs/PhiGen.lean` (`conj`, `conj_zero`, `conj_succ`, `phiProd`), `Defs/Laurent.lean`
   (`coeffMap_qExpand` — the pin's `ksplit_coeffEmb_qExpand` is its instance at
   `algebraMap ℚ L`; `coeffMap_injective`), `Defs/Twist.lean` (`coeffMap_qTwist`, `qTwist`,
   `qTwist_one_apply`, `qTwist_qExpand`, `qTwist_qTwist`), `Defs/JqCoeff.lean`
   (`map_jqModC`, `coeffMap_jqModC`, `coeffEmb_jq`, `jqModC`, `jqNModC`, `jqModC_rat`),
   `Defs/Laurent.lean` (`qExpand_qExpand`, `qExpand_congr`, `qExpand_one_apply`,
   `coeffMap_coeff`).
6. **The engine's premise** is `PhiGenSplits.lean`'s `splits_of_prime`.

**Still genuinely new** (the whole point of the module): `ksplit_comp_evalAtJ`,
`ksplitIota`/`_root`/`_units_zeta`/`_injective`, `ksplit_integral`, `ksplitLift`/`_root`/`_units_zeta`,
and the two push-forward theorems `phiAtSeed_qExpand_prime_eq` / `phiAtSeed_slot_prime_eq`.

## 3. Module plan — one new module, one façade

`FLTForHuman/ModularCurve/PhiGenSplitsAnyField.lean` (new, wired). Home by role: it is the
any-field twin of `PhiGenSplits.lean` (the splitting) **and** of `PhiSlotRoots.lean` (the roots
read off it) — the pin writes both in the one file, and the C-layer files
(`TOPIC-qexp-function-field-c.md`) import exactly that file. Do **not** edit `PhiGenSplits.lean`
or `PhiSlotRoots.lean`.

Header requirements: the usual docstring (provenance with the two pin URLs at `aa2d8b3`,
the byte-identical twin note, the twin relation to `PhiGenSplits`/`PhiSlotRoots`, layering,
assumptions), `spec-pin:` lines for

    P2M/Sol/S_ModularCurve_PhiGen_splits_prime_of_isPrimitiveRoot.lean
    P2M/Sol/S_ModularCurve_PhiGen_splits_prime_at_slot_of_isPrimitiveRoot.lean

(and nothing else — `TS`, `PhiAtSlot`, `Cyclotomic`, `KatzLevelPCusps`, `JqCoeff` carry their own),
imports (`PhiGenSplits`, `Defs/TS`, `Defs/PhiAtSlot`, `Defs/Cyclotomic`,
`Defs/KatzLevelPCusps`, `Defs/JqCoeff`, `Mathlib.RingTheory.AdjoinRoot`,
`Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots`,
`Mathlib.RingTheory.Polynomial.Cyclotomic.Roots`, `Mathlib.Algebra.Polynomial.Roots`),
`set_option autoImplicit false`, `noncomputable section`, `namespace ModularCurve` /
`namespace PhiGen` (the headlines are `ModularCurve.PhiGen.*`; the roots API of the pin is
`ModularCurve.*`), and no chapter tokens (`W1`, `ksplit` is fine as a *private* engine prefix —
the port keeps descriptive private names, never `W1`/`CharLRows`).

### 3.1 The engine — `private`, transcribed from pin 267–486

| port name | pin | lines |
|---|---|---:|
| `comp_evalAtJ` | `ksplit_comp_evalAtJ` | 13 |
| `iota` (`cyclRing ℤ p →+* CyclotomicField p ℚ`, `AdjoinRoot.lift`) | `ksplitIota` | 6 |
| `iota_root`, `iota_units_zeta`, `iota_injective` | same names | 5 + 5 + 21 |
| `integral` (the core) | `ksplit_integral` | 47 |
| `lift`, `lift_root`, `lift_units_zeta` | `ksplitLift*` | 5 + 4 + 4 |

`iota_units_zeta`/`lift_units_zeta` state `Units.map f.toMonoidHom (cyclZeta ℤ p) = cycUnit p`
resp. `= ζ`, proved `Units.ext (by rw [Units.coe_map, val_cyclZeta]; exact AdjoinRoot.lift_root _)`.
`integral`'s statement (pin text, `O := cyclRing ℤ p`):

```lean
  private theorem integral (data : ModularPolynomialData p) :
      phiAtSeed data (qExpand (cyclRing ℤ p) p (jqModC (cyclRing ℤ p)))
        = (Polynomial.X - Polynomial.C (qExpand (cyclRing ℤ p) (p * p)
            (jqModC (cyclRing ℤ p))))
          * ∏ b : Fin p, (Polynomial.X - Polynomial.C (qTwist ((cyclZeta ℤ p) ^ (b : ℕ))
              (jqModC (cyclRing ℤ p))))
```

### 3.2 The two public engine theorems — pin text verbatim (they are `public` in the pin)

```lean
theorem phiAtSeed_qExpand_prime_eq (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p) (data : ModularPolynomialData p) :
    phiAtSeed data (qExpand K p (jqModC K))
      = (Polynomial.X - Polynomial.C (qExpand K (p * p) (jqModC K)))
        * ∏ b ∈ Finset.range p, (Polynomial.X - Polynomial.C (qTwist (ζ ^ b) (jqModC K)))

theorem phiAtSeed_slot_prime_eq (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p) (data : ModularPolynomialData p)
    (e : ℕ) [NeZero e] (u : Kˣ) :
    phiAtSeed data (qExpand K (p * e) (qTwist (u ^ p) (jqModC K)))
      = (Polynomial.X - Polynomial.C (qExpand K (p * (p * e)) (qTwist (u ^ (p * p)) (jqModC K))))
        * ∏ b ∈ Finset.range p, (Polynomial.X - Polynomial.C (qExpand K e (qTwist (u * ζ ^ b) (jqModC K))))
```

Keep the pin's *section-variable* shape for these two: `variable {K : Type*} [Field K]` and
`variable (p : ℕ) [hp : Fact (Nat.Prime p)]`, so the checker's parsed text matches the pin's.

### 3.3 The two headlines — at the **wrapper** binders, verbatim

```lean
theorem splits_prime_of_isPrimitiveRoot {K : Type*} [Field K] (p : ℕ) [hp : Fact (Nat.Prime p)]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p) (data : ModularPolynomialData p) :
    data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) (qExpand K p (jqModC K)))
      = (Polynomial.X - Polynomial.C (qExpand K (p * p) (jqModC K)))
        * ∏ b ∈ Finset.range p, (Polynomial.X - Polynomial.C (qTwist (ζ ^ b) (jqModC K)))

theorem splits_prime_at_slot_of_isPrimitiveRoot {K : Type*} [Field K] (p : ℕ) [hp : Fact (Nat.Prime p)]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p) (data : ModularPolynomialData p)
    (e : ℕ) [NeZero e] (u : Kˣ) :
    data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
        (qExpand K (p * e) (qTwist (u ^ p) (jqModC K))))
      = (Polynomial.X - Polynomial.C (qExpand K (p * (p * e)) (qTwist (u ^ (p * p)) (jqModC K))))
        * ∏ b ∈ Finset.range p, (Polynomial.X - Polynomial.C (qExpand K e (qTwist (u * ζ ^ b) (jqModC K))))
```

The first is definitionally `phiAtSeed_qExpand_prime_eq` (`phiAtSeed` unfolds to that `eval₂RingHom`
map), so its proof is the pin's one line `phiAtSeed_qExpand_prime_eq p ζ hζ data`. If the
unfolding does not go through at `[Field K]`, insert a `phiAtSeed`-unfolding lemma; do **not**
weaken the statement. The second is the pin's `phiAtSeed_slot_prime_eq p ζ hζ data e u` plus the
same unfolding, or the push-forward argument of `PhiGenSplits.splits_prime_at_slot` if that is
cleaner — either way the statement above is fixed.

### 3.4 The roots API — pin text verbatim, at `[Field K]` (pin 504–592)

`prod_form_ne_zero` (private in the pin, **promoted** here: the port writes its prelude once),
`roots_prime_at_slot`, `roots_prime_at_slot_nodup`, `roots_prime_at_slot_roots_nodup`,
`isRoot_prime_at_slot_iff`, `roots_phiAtSeed_TS` — statements exactly as in the pin `S_` file
lines 511–589 (they use `jqModC K`, `Finset.range p`, `Multiset.range p` and `ζ ^ b`, with
`(p) [Fact p.Prime] (ζ) (hζ : IsPrimitiveRoot ζ p)` and no `N`). Their proofs are the pin's;
`roots_prime_at_slot_nodup` needs `TS_injective` (now available at `[Field K]`) and
`IsPrimitiveRoot.pow_inj`. `roots_phiAtSeed_TS` has five C-layer consumers — keep it.

**Dropped, with the reason in the header:** `roots_nodup_prime_at_slot_of_isPrimitiveRoot`
(pin 596–598, `private`, a one-line alias of `roots_prime_at_slot_roots_nodup`, no consumer) and
the whole `TS`/`coeffMap`/`qTwistEquiv`/`phiAtSeed` prelude of the pin file (now imported — §2),
including the dead `qTwistEquiv`, `qTwist_TS_one_cycle`-copies and `iota_jqN`-copies.

## 4. Build and verification discipline

- Bound **every** build: `flock -n /tmp/flt-build.lock timeout 170 lake build FLTForHuman.ModularCurve.PhiGenSplitsAnyField`;
  a `lake env lean <file>` for the edit loop (≈3–6 s after the deps are warm). Log to `lean/tmp/`.
  Never raise `maxHeartbeats`; a 200k timeout is a diagnostic — the cause is almost always an
  instance/unification shape problem, so restate the offending lemma over the concrete function.
- Green means **0 errors and 0 warnings**, no `sorry`, no `admit`.
- `#print axioms` on both headlines: only `[propext, Classical.choice, Quot.sound]`.
- Statement check: `python3 spec/check_port.py --force FLTForHuman/ModularCurve/PhiGenSplitsAnyField.lean`
  must read **0 mismatch / 0 missing / 0 own**. Expected `ok` count ≈ 11 (2 headlines + 2 engine
  theorems + 6 roots API + `prod_form_ne_zero`, which the checker accepts through its
  promoted-from-pin-private fallback). If a declaration reports `own`, stop and report — the
  statement is wrong.
- Do **not** edit any other module. If an import is missing, add it to this module only. If a
  ground module turns out to need a change (e.g. a missing bridge), **stop and report** — the
  manager owns ground edits.
- `python3 tools/deps/dedup.py --tier name,shape --min-cost 1 --module FLTForHuman/ModularCurve/PhiGenSplitsAnyField.lean`
  should read 0 clusters; if it flags a twin, report it rather than deleting a public statement.

## 5. Known friction, in order of likelihood

1. **`AdjoinRoot.lift`'s side condition**: `AdjoinRoot.lift (Int.castRingHom K) (ζ : K) (…)` wants
   `eval₂ (Int.castRingHom K) ζ (cyclotomic p ℤ) = 0`; the pin gets it from
   `Polynomial.eval₂_eq_eval_map`, `Polynomial.map_cyclotomic_int` and
   `Polynomial.IsRoot.eq_zero (hζ.isRoot_cyclotomic hp.out.pos)`.
2. **`iota_injective`**: `Polynomial.cyclotomic_eq_minpoly_rat (cycUnit_spec p) hp.out.pos`,
   `minpoly.dvd ℚ _ hq`, then `map_dvd_map (Int.castRingHom ℚ) Int.cast_injective
   (Polynomial.cyclotomic.monic p ℤ)`; the `AdjoinRoot.mk_surjective`/`mk_eq_zero` dance is the
   pin's and should transcribe.
3. **`phiAtSeed` unfolding at `[Field K]`** (§3.3) — the one place the port differs from the pin's
   text shape, because the pin's headline is stated against `phiAtSeed` and the wrapper's is not.
4. **`Fin p` vs `Finset.range p`**: `Fin.prod_univ_eq_prod_range`; and `Fin.prod_univ_succ` for
   the `p + 1` product.
5. **`Polynomial.ringHom_ext'`/`ringHom_ext` + `RingHom.ext_int`** for the `comp_evalAtJ` shape.

## 6. Report

Report: the modules written, written-line count vs the 397 priced (minus the `TS` share now
imported), the build jobs/time, the checker reading, the axioms, the dedup reading, and every
declaration dropped (with its pin lines and the reason). Friction goes to
`lean/instance-friction.md` only if instance search is the cause.
