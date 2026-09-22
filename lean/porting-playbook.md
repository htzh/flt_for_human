# Porting FLT to mathlib — a playbook

Written after the first port, `#E[n](K) = n²`, whose record is
[logs/card-torsion-port.md](logs/card-torsion-port.md). Read that file for *what* that port
did; read this one before starting the next one. The second effort already has a
blueprint in [PORTING-FFG.md](PORTING-FFG.md).

Everything below is measured from the first port or hit while doing it.

## 1. What the effort cost

| | |
|---|---|
| modules | 13 under `FLTForHuman/Elliptic/` |
| lines written | 3362 |
| declarations | 292 |
| FLT cone consumed | engine 1869 lines / 304 decls; `S_…` 1335 lines / 36 decls |
| rounds | 33 |

Where the 3362 lines went:

| layer | modules | lines | decls |
|---|---|---|---|
| setup | `Basic`, `Universal` | 274 | 41 |
| EDS + `ω` engine | `DivisionPolynomial`, `EDS`, `EllSequence`, `Complement`, `RedInvar`, `Net`, `Omega` | 1207 | 128 |
| multiplication bridge | `MulFormula`, `JacobianMulFormula`, `Bridge` | 717 | 92 |
| counting | `Fiber` | 1164 | 31 |

Two things this table says that are worth internalising:

- **Cost tracks mathlib gaps, not FLT line count.** The counting argument is the
  single biggest module (1164 lines) and was the *cheapest* per line: it is
  ordinary field/root algebra with no API archaeology. The expensive part was the
  ~1200 lines of engine, because mathlib dropped the `ω` division polynomial and
  the general complement multiplication property, so those had to be re-derived
  against the parts mathlib *did* keep (`atom`, `atomRel`, `rel`, `normEDS`,
  `complEDS`).
- **A faithful port is not line-for-line smaller.** 3362 written against a cone
  of 3671 lines (3331 once the 340-line 4.30-compat shim is set aside). The saving is not in the volume of mathematics — it is in what never
  had to be written (below) and in the fact that 13 focused modules were written
  instead of 197+ importers inheriting a 1869-line engine.

## 2. Clutter removed, and how each was found

| removed / never written | size | detection method |
|---|---|---|
| `Def_Compat_Mathlib430.lean` (separate file) | 340 lines, 197 importers | we are on the version its renames target, so the unprimed names exist |
| odd-only `smul_surjective` + `card_smul_fiber` (452–550) | 98 | the `_all` versions at 955/1052 have the *same proof*, and `hodd` is unused |
| `smul_surjective_all` + `card_smul_fiber_all` (955–1052) | 98 | byte-identical to the above ⇒ generalise one copy instead of porting two |
| `ΨSq_odd_eq_sq` + `smul_eq_zero_iff_preΨ'_eval` (269–306) | 38 | occurrence count 1: referenced only by themselves |
| `nTorsion` (308–321) + the `solution` bridge (1331–1335) | 20 | it *is* `Submodule.torsionBy` |
| `p2m_exact_reverting` + the `_light` Sol file + 2 `Thm_` files | 44 | we state and prove the theorem directly |
| `evalEval_ωe` (1306) + `polyEval_cusp_ωe` (1329) | 10 | occurrence count 1 |
| inherited import list | ~half of 21 imports | copied from the engine, unused here |

That is ~310 lines of the cone itself (measured spans, not estimates) plus a
340-line compat shim with 197 importers, out of a 3671-line cone.

Two lessons.

**Removing a wrapper is a design decision, not a deletion.** FLT wraps the torsion
in a local `nTorsion` `AddSubgroup` and reconciles with mathlib's
`Submodule.torsionBy` only in the final `solution`. Porting the wrapper would have
meant porting the reconciliation too. Stating every counting lemma over
`Submodule.torsionBy` *from the first lemma* made the capstone a one-line alias.
The cost of that choice was one adaptation — `AddSubgroup.addOrderOf_coe` applied
to `(Submodule.torsionBy …).toAddSubgroup` — against ~30 lines and a whole bridge.
When a target type exists in mathlib, adopt it as the port's interface immediately
rather than mirroring FLT's internal one.

**Deduplicate at the source, not after.** Two FLT declarations with the same proof
should become one general lemma, not two ports. Diff the proofs before porting the
second.

**Caveat, learned the hard way.** I declared `coords` dead code from a
`grep … | head -20` whose output was truncated, and it turned out to be load-bearing
in `exists_double_fiber_card`. Count occurrences (`grep -c`) before dropping
anything; a truncated listing is not evidence.

## 3. Approaches that carried the port

### 3.1 Map to mathlib before writing anything

Build a FLT → mathlib table *first*, and test the entries for **definitional**
equality with `rfl`, not just mathematical agreement. Here `compl₂EDS` is `rfl`-equal
to `complEDS₂`, `addMulSub`/`rel₄`/`net` to `atom`/`atomRel`/`rel` — which is what
makes aliases legal instead of re-proving. The table in
[logs/card-torsion-port.md §3](logs/card-torsion-port.md) is the template.

### 3.2 Trace the capstone top-down with a "nature" column

Walking the dependency tree from the theorem and labelling each node
**plumbing** / **math** / **already mathlib** is what exposed that most of the
height was scaffolding, and it produced the port order. Do this before porting.

### 3.3 Prove for the universal object, then transfer by `aeval`

mathlib has no `IsEllipticSequence (normEDS b c d)`. FLT's trick, reused here for
`normEDS_isEllipticSequence`, `normEDS_mul_complEDS`, `invar₂_normEDS` and
`redInvar_normEDS`: prove the statement for the *universal* EDS over
`MvPolynomial Param ℤ`, where every coefficient is a non-zero-divisor so
cancellation is legal, then push along `aeval`. The transfer lemmas are the
`*_eq_aeval` pair plus the `map_*` lemmas.

If the transfer does not typecheck, it is usually the coercions: `MvPolynomial.aeval`
is an `AlgHom` while the `map_*` lemmas want a `RingHom`.
`simpa only [AlgHom.coe_toRingHom, …] using h` fixes it.

### 3.4 Do not state the goal against an abstract `*_aux` lemma

FLT often ends a computation with `exact foo_aux h`. Ported literally that can blow
the defeq budget — one instance here was a **299 s deterministic `whnf` timeout**.
The fix is to *not* unify the whole goal against the abstract statement: push
everything into normal form first and finish with `field_simp; ring`, supplying the
non-zero hypotheses `field_simp` needs explicitly:

```lean
simp only [polyToField_sub, polyToField_neg, map_add, map_mul, map_pow, map_ofNat,
  polyToField_polynomial, mul_zero, pointedCurve_a₁, pointedCurve_a₃, ψ_two, ψ₂]
have hψ2 : polyToField curve.polynomialY ≠ 0 := by
  simpa [ψᵤ, ψ_two, ψ₂] using ψᵤ_ne_zero two_ne_zero
field_simp
ring
```

Corollary: when a build suddenly takes minutes, suspect a defeq check inside
`exact`/`convert`, not the tactics that came before it.

### 3.5 Monomorphic helper lemmas close the rewrite-search gap

The single most repeated obstacle. mathlib's *generic* `map_sub`, `map_neg`,
`Jacobian.comp_smul`, `Jacobian.map_neg` do **not** fire under `rw`/`simp` when the
function argument leaves implicit instances unresolved, even though the pattern
looks identical:

```lean
-- works:
example (P : Fin 3 → Poly) : polyToField ∘ (u • P) = polyToField u • (polyToField ∘ P) :=
  Jacobian.comp_smul polyToField P u
-- silently makes no progress:
example (P : Fin 3 → Poly) : polyToField ∘ (u • P) = polyToField u • (polyToField ∘ P) := by
  rw [Jacobian.comp_smul]   -- "did not find an occurrence of ⇑?f ∘ (?u • ?P)"
```

The remedy is a monomorphic helper proved by `exact`, which then rewrites fine:

```lean
lemma polyToField_comp_smul (P : Fin 3 → Poly) (u : Poly) :
    polyToField ∘ (u • P) = polyToField u • (polyToField ∘ P) :=
  Jacobian.comp_smul polyToField P u
```

Reach for this the moment a `rw` or `simp only` reports "no progress" on a goal you
can see the pattern in.

### 3.6 Prove the equality once, then rewrite through it

A relative of 3.5: when a lemma is stated with a different but definitionally equal
head (`Jacobian.map curvePoly polyToField` vs `curveField`), `rw` cannot match it.
Prove the identification once by `rfl` and rewrite *through* it so the target
becomes syntactically matchable:

```lean
lemma jacobian_map_curvePoly_polyToField :
    Jacobian.map curvePoly polyToField = curveField := rfl
-- then: rw [dblXYZ_Z, ← jacobian_map_curvePoly_polyToField, Jacobian.map_dblZ …]
```

Trying to `change` the goal to the unfolded form instead can cost a several-minute
`whnf` (it did here).

### 3.7 `rw` and `simp_rw` do not unfold `abbrev`s

Repeatedly bit us (`smlPoly`, `smlRing`, `smlField`, `rel₄`, `net`, `addMulSub`).
Use `change` to state the unfolded goal, or `simp only [name]`.

### 3.8 Pick mathlib's API as the port's interface

See §2: `Submodule.torsionBy` from the first lemma. The same applies to
`Submodule.mem_torsionBy_iff`, `AddSubgroup.card_bot`, `Cubic.*`,
`twoTorsionPolynomial` — mathlib usually already has the shape, and adopting it
early is what keeps the capstone short.

### 3.9 Iterate in a gitignored scratch file

`lake env lean Scratch.lean` (~3 s) against `lake build <module>` (~5 s) and a full
`import Mathlib`-wide build (~150 s). Put experiments, `#check` probes and
type-hunting in `Scratch.lean`, which `lean/.gitignore` excludes. The single most
useful probe when a rewrite or instance fails is a `#check @name` on the lemma you
think you are using.

### 3.10 Keep the friction log *while* you hit friction

The API-drift list in §4 was only cheap to write because it was appended to during
the port. It is the highest-value artefact for the next effort — more than the
module list, because the module list is derivable from the code and the drift list
is not.

## 4. v4.34.0 drift checklist

Renames and shape changes hit during this port, with the replacement:

| old / expected | v4.34.0 |
|---|---|
| `if_pos h`, `if_neg h` | `ite_eq_left h`, `ite_eq_right h` |
| `dif_neg h` | `dite_eq_right h` |
| `Polynomial.finite_setOf_isRoot` | `Polynomial.finite_setOfPred_isRoot` |
| `Set.mem_setOf_eq` | `Set.mem_ofPred_eq` |
| `Affine.Nonsingular x y` | `W.toAffine.Nonsingular x y` (curve is explicit) |
| `Submodule.card_bot` | does not exist — use `AddSubgroup.card_bot` |
| `Submodule.mem_torsionBy_iff.mp` | takes explicit args: `(… _ _).mp` |
| `mul_cancel_left_mem_nonZeroDivisors` | does not exist — `mul_left_cancel₀` in a domain |
| `Jacobian.map` | a *separate* def from `WeierstrassCurve.map` (they are defeq) |
| `Affine.Point.some_ne_zero` | does not exist — `cases` on the equality |
| `ext i` on `Fin 3 → MvPolynomial …` | recurses into `MvPolynomial.ext`; use `funext i` |
| `nTorsion n` (`n : ℕ`) | `Submodule.torsionBy ℤ M n` takes `n : ℤ`, so `↑2` ≠ `2` syntactically |

Also: `Submodule.torsionBy.zmodModule` supersedes FLT's `instModuleZModTorsionBy`,
and `(W.map f).IsElliptic` is all a base-change `IsElliptic` instance needs.

## 5. Checklist for the next port

1. **Measure the cone first** — files, lines, declarations, importers. Decide from
   those numbers whether the port is a port, a re-derivation, or a both.
2. **Build the FLT → mathlib table** and test each entry with `rfl` where you hope
   for definitional equality.
3. **Trace the capstone top-down**, labelling plumbing / math / already-mathlib.
4. **Adopt mathlib's types as the interface** from the first declaration.
5. **Port bottom-up, build after every module.** Do not batch modules before
   building; a broken layer is much cheaper to bisect than a broken tree.
6. **Grep -c before dropping anything.** Never trust a truncated listing.
7. **Diff before porting a second similar lemma** — generalise one instead.
8. **Expect the rewrite-search gap (§3.5) and the `abbrev` gap (§3.7).** They are
   not bugs in your proof; they are a tactic-level mismatch.
9. **Watch the build clock.** A jump from seconds to minutes is a defeq blowup; go
   looking for an `exact`/`convert` against an abstract statement.
10. **Keep the friction log current**, and at the end split the record from the
    playbook the way this pair is split: one file says what *this* port did, the
    other says what *the next* port should know.

## 6. Open questions

Recorded honestly, because they are the parts of the method that are not settled:

- **Hybrid vs faithful is a per-layer choice, and we only ever tested one layer
  mix.** Here the engine was re-derived and the bridge was ported. Nobody has
  measured what happens when mathlib absorbs the *core* but not the periphery, or
  the reverse — which is exactly the situation
  [PORTING-FFG.md](PORTING-FFG.md) describes for the second port.
- **Round counts are not a good cost model.** They depend on how often the agent
  stalled on a defeq or a name. The line and declaration counts in §1 are the
  stable measurements.
- **Nothing here was validated against a third-party port**; the "removed clutter"
  numbers are what this effort avoided writing, measured from FLT's own files, not
  an independent audit of whether the dropped items were truly dead.
