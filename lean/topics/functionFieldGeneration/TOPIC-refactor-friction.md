# Lean and tooling friction met in the FFG refactor

**Status: methods note, written from wave 7 (2026-11-04).** Each entry is a place the
refactor lost a build round, with the error as it appears, the cause, and the idiom that
avoids it. §1 is the one that needed a shelf file to settle
([`Reserve/Example/FactPrimeNeZero.lean`](../../Reserve/Example/FactPrimeNeZero.lean));
the rest are one-liners. The wave itself, its measurements and its decisions are
[TOPIC-ffg-refactor.md](TOPIC-ffg-refactor.md) §13–§15; the interface method is
[../TOPIC-assembler-interfaces.md](../TOPIC-assembler-interfaces.md).

## 1. A hypothesis is not an instance (`Fact`, `NeZero`)

**Symptom.** `hall_all` carries, twice, `have hp : p.Prime := …` followed by
`have : Fact (Nat.Prime p) := ⟨hp⟩`. The second line looks like a restatement of the
first, and deleting it as redundant fails the build — but *not* where the reader expects:

```text
error: failed to synthesize instance of type class
  NeZero (M * p ^ a)
```

**Cause.** `Fact` is a class, so a `have` of that type registers a **local instance**;
`hp : p.Prime` is a hypothesis, and instance search never reads hypotheses. The `NeZero`
side conditions of the divisor induction do not come from a local `NeZero` — they come
through the chain

```text
Fact (Nat.Prime p)  --Nat.Prime.one_lt'-->  Fact (1 < p)  --NeZero.of_gt'-->  NeZero p
```

hence `NeZero (p ^ a)`, hence `NeZero (M * p ^ a)`. So the line is doing two jobs: it
satisfies the `[Fact (Nat.Prime p)]` binders of the called statements, and it makes the
whole `NeZero` tower discoverable.

**Why the error misleads.** It names only the outermost class. Two instances down the
missing link can be something else entirely: `NeZero.of_gt'` also wants `Preorder ℕ` and
`IsBotZeroClass ℕ`, so under `import Mathlib.Data.Nat.Prime.Basic` alone even the
`[Fact (Nat.Prime p)]` binder form fails, for a reason unrelated to `Fact`. Only

```lean
set_option trace.Meta.synthInstance true in
example (p : ℕ) [hp : Fact (Nat.Prime p)] : NeZero p := inferInstance
```

shows which link is absent. Suspect the order/`Zero` instances before the primality.

**Scope.** A local instance lives to the end of its block, which is why `hall_all` states
it twice: each half introduces its own prime (`hgen`'s hypothesis, and `d.minFac`).

**Guard.** `Reserve/Example/FactPrimeNeZero.lean` has the chain in both directions, with
three `fail_if_success` examples asserting that the hypothesis alone gets nowhere. They
are re-runnable: if a future mathlib gives `p.Prime` an instance route to `NeZero`, they
fail loudly instead of quietly making the port's `have` lines redundant.

## 2. Decomposition and arithmetic traps

**`Nat.exists_eq_pow_mul_and_not_dvd` returns `d = p ^ k * M`.** The prime power comes
*first* and the non-divisible factor last — the opposite of how one writes it from the
divisor side. Stating a helper as `M * p ^ k` typechecks at the definition and fails at
the call site only. State helpers in the orientation the decomposition produces (or
`rw [mul_comm]` once, deliberately). `NumberTheory/DedekindPsi.lean`'s own
`dedekindPsi_mul_prime` proof takes the same orientation, so the module is consistent.

**`mul_one` versus `one_mul` after substituting the exponent.** With `k = 0`, the
hypothesis `d = p ^ k * M` becomes `d = p ^ 0 * M` and then `d = 1 * M`: the rewrite is
`one_mul`, not `mul_one`. Writing `mul_one` leaves `p ∣ 1 * M` in the context and the
goal unclosed. The pin's inline version of this step also uses `one_mul`; it is a known
trap, not a typo to be fixed twice.

**`omega` can close a side condition you thought needed an argument.** The `hprop`
closure's `m ≠ 0` was `exact absurd hlt (by have := Nat.pos_of_ne_zero hN; omega)`. It is
`rintro rfl; omega`: with `m = 0` the *divisor* hypothesis becomes `0 ∣ d`, i.e. `d = 0`,
contradicting `hlt : 0 < d`, and `omega` preprocesses the divisibility. Trace the goal
state before assuming which hypotheses are needed.

**Corollary: a hypothesis the body ignores can still be load-bearing.** `hprop` was
`∀ m, m ∣ d → m < d → Hall m := fun m _ hlt => …` — the divisibility proof sits in a `_`
pattern and is never named. Dropping it as dead weight makes the closure *unprovable*:
`m < d` alone does not exclude `m = 0` (`m = 0, d = 1` satisfies it), and the `omega` in
the body was getting the exclusion from `0 ∣ d`. The refusal was the useful signal, and
the resolution was not to put the hypothesis back but to skip the wrapper: both call sites
can produce `m ≠ 0` directly (`NeZero.ne M` in one, `mul_ne_zero hM0 (pow_ne_zero …)` in
the other), so `ih` is applied directly and `hprop` disappears. A `_` in a lambda body is
where this hides: grep for `fun … _ …` before deleting a hypothesis.

**The strategy, in one line: an induction body should read as mathematics.** The case
split, the induction hypothesis, the comparison, the conclusion — nothing else. Every
arithmetic fact it mentions becomes a named lemma, and the test for "does this group of
`have`s belong together" is *closure*: if a group of local facts is consumed only by each
other and by one or two downstream lemmas, the whole group is a helper's body, not setup.
Applied twice to `hall_all`, this took it from 71 lines to 40.

**Level arithmetic in an induction body belongs in a named helper — all of it.** The
`Tight` half of `hall_all` opened with nine lines of setup — `set p := d.minFac`,
`Nat.minFac_prime`, `Nat.exists_eq_pow_mul_and_not_dvd`, a nonzero derivation, the
`p ^ k * M → p ^ (a + 1) * M` successor step, a re-oriented equation, a strict bound and a
divisibility witness — every line existing only to feed one of the level bounds. The tell
is that the facts form a *closed* set: nothing outside the block consumes `hdM`, `hM0` or
the divisibility witness, so the block can be replaced by one `obtain`. It now reads

```lean
obtain ⟨M, p, a, hp, hpM, hM0, hdM'⟩ := exists_eq_mul_pow_succ_of_ne_one h1
have : NeZero M := ⟨hM0⟩
have : Fact (Nat.Prime p) := ⟨hp⟩
have hlow_lt : M * p ^ a < d := lt_of_eq_mul_pow_succ hM0 hp hdM'
have hall_low : Hall (M * p ^ a) := ih _ hlow_lt (mul_ne_zero hM0 (pow_ne_zero _ hp.ne_zero))
```

with two module-local helpers carrying the arithmetic
(`exists_eq_mul_pow_succ_of_ne_one` for the decomposition, `lt_of_eq_mul_pow_succ` for the
bound).

**Cheap number theory does not belong to the module that uses it once.** The last block,
the `ψ` recurrence at a prime power, was five lines of case split over `a = 0`/`a ≠ 0`. It
is not proof plumbing, it is *number theory* — and the place a reader looks for it is the
`ψ` module, not a function-field induction. It is now
`dedekindPsi_mul_prime_pow_succ` in `NumberTheory/DedekindPsi.lean`, beside the two
prime-step case splits it combines, and the proof ends with one `rw` and one `exact`. The
"unfamiliar content" objection cuts both ways: an unfamiliar-but-standard computation is
exactly what should carry a name and a home, because the next module that needs it will not
find it inside a proof.

The dividing line used here: **`private` in the consumer** when the statement is about this
proof's own data (the `d = M * p ^ (a + 1)` decomposition and the strict bound below it),
**public upstream** when it is standard arithmetic on the objects the upstream module
already owns (`ψ`'s recurrence, the prime-power shape). `hall_all` went **71 → 40 lines**.

## 3. Rewriting traps

**`▸` and `rw` rewrite every occurrence, including the ones inside a term you are using.**
`hdM ▸ Nat.minFac_dvd d` with `hdM : d = M` has to choose between the `d` in `d.minFac`
and the `d` on the right, and can land on `M.minFac ∣ M` where `p ∣ M` was wanted. The
safe idiom names the fact first and rewrites in the hypothesis:

```lean
have hpd : p ∣ d := Nat.minFac_dvd d
rw [h] at hpd
exact hpM hpd
```

The same trap bites `rw` when the variable appears under a projection or an application.
`by rw [hdM, mul_comm]` where `hdM : d = d.minFac ^ (a + 1) * M` rewrites the `d` inside
`d.minFac` too, and the goal becomes `M * (M * d.minFac ^ (a + 1)).minFac ^ (a + 1) = …`.
The error names no hypothesis, only a mangled goal, so it reads like a statement bug. Build
the equation instead of rewriting into it: `hdM.trans (mul_comm _ M)`.

**The same trap again, one node down.** `exists_mul_prime_lt_of_dvd_of_ne` — the level step
of `modularFunctionField_eq_full_of` — writes `N = d * m′` and then wants the level
`m′ = m′.minFac * m` inside it. `rw [hm]` also hits the `m′` in the `m′.minFac` on the other
side of the goal and leaves `d * m′.minFac * m = d * m * (m′.minFac * m).minFac`. The idiom
that works is to confine the substitution to the side that still has the raw `m′`:

```lean
have hNm : N = (d * m) * m′.minFac := by
  conv_lhs => rw [hm', hm]
  ring
```

(`trans`/`congrArg` — build the equation, never rewrite into the term you are using — does the
same without `conv`; `conv_lhs` is the shorter spelling and is used elsewhere in the port.)

**`subst` eliminates the right-hand side of the equation, not the left.** `rcases eq_or_ne d N
with rfl | …` *is* a `subst`, so at `d = N` it eliminates `N` and keeps `d` — the opposite of
what a node wants when `N` is the theorem's subject: its `NeZero` instance, the level every
`modularFunctionField` in the goal is applied to. (Both sides are variables here; with
`N = d` the same tactic eliminates `d`.) The branch stays provable and silently reads
backwards; the goal at `d = N` in `modularFunctionField_eq_full_of` was

```text
hdN : d ∣ d
⊢ (qExpand ℚ d) jq ∈ ↑(modularFunctionField d)
```

while the second branch kept `N`. Naming the equation and substituting the side you mean keeps
the goal at `N`:

```lean
rcases eq_or_ne d N with hd | hd
· subst d -- keeps `N`, the theorem's subject
  exact IntermediateField.subset_adjoin ℚ _ (Set.mem_insert_of_mem _ rfl)
```

Both orientations exist — `d = N` eliminates `N`, `N = d` eliminates `d` — but which side a
`rcases … with rfl` keeps is not something a reader looks for in a case split. Say it.

**`IsRoot` is `eval = 0` by definition.** `have hy' : P.IsRoot y := hy` typechecks in
either direction without a rewrite, which is what let the descent's statement be respelled
while keeping the pin's 60-line proof: only `hBev`'s declared type and the two hypothesis
applications changed. But `rw`/`simp` will not unfold `IsRoot` for you — convert with
`have`/`exact` (defeq), not with a rewrite rule.

**When `rw` refuses an equation that `exact` accepts, the difference is instance matching.**
The `ψ` recurrence's conclusion is the lemma stated backwards in the goal. `rw [hdM', ← lemma]`
failed with "did not find an occurrence of the pattern
`dedekindPsi (M * p ^ ?m) * if ?m = 0 then p + 1 else p`" — the pattern *is* the left-hand
side of the goal. `rw`'s matcher is syntactic up to reducible defeq and is fussy about the
`Decidable`/instance arguments inside an `if`; `exact` goes through full `isDefEq`. The fix
is the two-line form: `rw [hdM']` then `exact (lemma hp hpM).symm`. Rule of thumb: if a
rewrite "cannot find" a term you can see, stop rewriting and `exact` the oriented statement.

**`abbrev` unfolds under `rw`; `def` does not.** `rw [← hfull]` where
`hfull : Gen (d * m')` works only because `Gen` is an `abbrev`; `rw` whnfs the hypothesis
and sees the equation. The same `Gen` as a `def` would need `unfold Gen at hfull` first.

**`simp only [someDef]` is the way to unfold a `def` on both sides of a goal.** The
composition bridge in `Descent` is one line — `simpa only [nomeMap] using
nomeMap_qExpand K M p` — because the general lemma is stated with the `def` and the local
obligation is stated with its body.

**An implicit argument binds to the context's variable of the same name.** The descent's
proof (`jqN_div_mem_modularFunctionField`) used to call
`isPrimitiveRoot_pow_div (cycUnit_spec (M * p)) ⟨p, rfl⟩` inside a context whose `p` is
the level's prime. The lemma's implicit `{p}` is its *target order*, and it binds to
`M`; the outer `p` is the `Dvd` witness `M * p = M * p`. The call reads as "the `p`-th
power" and denotes the `((M * p) / M)`-th one, and nothing in a type error would say
so. Pass the divisor as the visible argument — `isPrimitiveRoot_pow_div hζ
(dvd_mul_right M p)` — and the target order is what the reader sees. Same family as the
`Nat.minFac_dvd` orientation note (§2): a call that reads correctly and denotes
something else.

**`open` does not resolve relative to the enclosing namespace.** `open Nome` inside
`namespace ModularCurve` is an error (`unknown namespace 'Nome'`); write
`open ModularCurve.Nome`. One build round, every time.

**A `haveI` that search does not need fails the linter.** `haveI : NeZero (M * p ^ a)`
in the ψ case split produced `linter.style.haveILetI`: the instance was synthesizable
anyway, so the line was warning-and-nothing. Drop it. When a `haveI` is genuinely needed
by search the linter stays quiet, so "build not silent" is the diagnostic. The port
disables the linter at module level only where the instance really is consumed
(`set_option linter.style.haveILetI false`, with the reason in the header).

## 4. Tooling friction

**A failed module leaves no `.olean`.** After a deliberately broken experiment,
`lake env lean probe.lean` fails with

```text
error: object file '…/Capstone.olean' of module … does not exist
```

That is not a stale-file problem: some module failed earlier in the same run. Rebuild the
module, then re-run the probe.

**Editing a `Defs/` module is a cascade, not an edit.** Adding two lemmas to
`NumberTheory/DedekindPsi.lean` (indeg ≈ 20) or `Defs/PhiAtSlot.lean` rebuilds the whole
function-field cone — measured: `SlotProduct` 38 s, `PhiSlotRoots` 12 s, `Capstone`’s
dependency chain in between. A two-line helper is never a two-line change if it lands
upstream. Decide the home first (§7 of the interface note) and defer the tree build
explicitly; do not discover the cascade halfway.

**`check_port`'s "identical statement at … (not in this wire)" note is a hint, and acting
on it can lose.** Wiring `S_ModularCurve_exists_phiIrreducible.lean` fixed
`dedekindPsi_mul_prime_not_dvd` and flipped its same-named sibling `dedekindPsi_mul_prime_dvd`
to **mismatch** — that file's declaration has a different statement. Net: 14 ok became
13 ok + 1 mismatch. Both case splits went to `own:` rows instead. A wire is worth adding
only if it improves the count.

**The `own:` row keys on the name the checker parses.** `spec/check_port.py --json`
reports it — sometimes fully qualified (`ModularCurve.Nome.nomeMap`), and in one probe an
unqualified name for a declaration at a module's end. Type nothing: read the name. A wrong
spelling is reported as `STALE MARKER` *and* leaves the declaration `missing`, so the
module still fails and the marker did nothing.

## 5. The order to try things

1. Read the error's *goal*, not its summary: `trace_state` at the failure point, or
   `set_option trace.Meta.synthInstance true in` for a synthesis failure (§1).
2. Ask whether the missing thing is a hypothesis or an instance (§1), and whether the
   failure is really about the class it names (it often is not).
3. Check for `one_mul`/`mul_one` and for a decomposition's orientation (§2) before
   touching the proof structure.
4. Convert with `exact`/`have` where the two terms are defeq (§3) instead of adding a
   rewrite rule.
5. Only then reach for a helper or a shared home — and price the home, not the helper (§4).

## 6. Pointers

- The arc this friction came from, as a reusable case study:
  [../CASE-hall-all.md](../CASE-hall-all.md).
- The shelf example: [`Reserve/Example/FactPrimeNeZero.lean`](../../Reserve/Example/FactPrimeNeZero.lean).
- The instance chain's mathlib ends: `Nat.Prime.one_lt'` (`Mathlib/Data/Nat/Prime/Defs.lean`)
  and `NeZero.of_gt'` (Lean core); the `Preorder`/`IsBotZeroClass` requirements come from
  the latter.
- The wave's measurements and the two regularised legacy modules:
  [TOPIC-ffg-refactor.md](TOPIC-ffg-refactor.md) §15.
- Checker mechanics (`own:`, tiers, the parsed-name rule):
  [../TOPIC-assembler-interfaces.md](../TOPIC-assembler-interfaces.md) §6.
