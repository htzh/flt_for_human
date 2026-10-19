# WORKORDER LI-2 — `integral_smoothWeylIntegrand_adicCompletion`

Set **LI-2** of the `AutomorphicForm.LocalIntertwining` column: the smooth twin of the already-landed
[set LI-1](WORKORDER-LI1-weyl-unramified.md). Plan: [TOPIC-local-intertwining-weyl-integrand.md](TOPIC-local-intertwining-weyl-integrand.md)
§6. Playbook [porting-playbook.md](../../porting-playbook.md) §2.3, §3.3–§3.5, §4. Frictions
[logs/frictions.md](../../logs/frictions.md) — read FR-0014 through FR-0018 before starting, append yours.

Pin `anthropics/fermats-last-theorem@aa2d8b3`. Port mathlib `v4.34.0`.

## 1. Scope

Port the pin's `FinGKFold_SmoothShell_Main` section and its headline, in **one new module**. The
prelude is already in the port — import it, do not re-carry it.

**In scope**: `P2M/Sol/S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.lean`
lines 1420–2015 — `SetBridges` (1436–1572), `Substitution` (1575–1627), `Regularity` (1630–1770),
`Tail` (1773–1887), `Main` (1890–2005) — and the headline at the wrapper's binders.

**Not this set**: the file's own prelude (lines 1–1419 is the same T1 text LI-1 already homed), the
other seventeen `LocalIntertwining` nodes, and **any edit to an existing module**. `TateGlobal/WeylPrelude.lean`,
`WeylShell.lean` and `WeylUnramified.lean` are frozen; a needed `private` there is a stop condition.

## 2. Sources

* **Proof**: the pin file above, lines 1420–2015. The pin's implementation lemma is **`private`**
  (`integral_smoothWeylIntegrand_impl`, line 1894) and the only public object is the headline
  (`solution`, line 2019). Unlike LI-1, nothing of the implementation is part of the pin's surface:
  keep the port's helpers `private` too, and expose only the headline.
* **Statement**: `Theorems/Thm_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.lean`.
  Binders come from the wrapper, never from the `S_` file's section-variable form.
* The pin writes `ValuationOrd.ord`; the port's name is `IsDiscreteValuationRing.ord (v.adicCompletionIntegers F)`.
* Provenance: `-- pin: <name> (<full pin filename>:<line>)` above every declaration, filename **in full**
  ([logs/frictions.md](../../logs/frictions.md) FR-0011).

## 3. Already in the port — import it, do not re-prove it

* The whole T1 prelude, as in [WORKORDER-LI1](WORKORDER-LI1-weyl-unramified.md) §3.
* Set LI-1's two modules: `TateGlobal/WeylShell.lean` (29 public — the residual prelude: the shell and
  measure API, `charExt_of_mem_shellSet`, `setIntegral_shellSet_const`, the negShell measure block, the
  generic `ord` refinements) and `TateGlobal/WeylUnramified.lean`. Both are public and importable.
* **67 of this file's 94 helpers are statement-identical to LI-1's.** `port_advise`'s `drags` list for
  the smooth file (`… --drags-full`) names them with their flags; anything marked `[in-port, …]` or
  that resolves into `WeylShell`/`WeylPrelude`/`MulHaar`/`LocalZetaUnramified` is an import.
* `ofReal_pow_cpow` is the one deliberate re-proof: the port carries the name twice
  (`CompletedDedekindZeta/Mellin.lean:115` is a different identity; `TateGlobal/EulerFactors.lean:80` is
  the same identity with binders `(x) (m) (s)`), and `WeylShell` re-proves the pin's 8-line version
  `private`. A `private` declaration is not importable, so re-derive it `private` here as well — do not
  widen `WeylShell`'s (FR-0015/FR-0017).

## 4. Deliverables

* A new module, e.g. `FLTForHuman/NumberTheory/NumberField/TateGlobal/WeylSmooth.lean`, holding the
  headline (public, at the wrapper's binders) and its private development.
* Every helper that is local to this set stays `private` **with a content name**; anything a later
  set will need goes in `WeylShell.lean` — but that file is frozen, so report it instead.
* Append your friction entries to `logs/frictions.md` in the template there (newest at the bottom).

## 5. Route and risks

* **The headline's character hypothesis is a depth condition**, not LI-1's unramified one:
  `hχ : ∃ c : ℕ, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v c, χ u = 1`. The pin's
  `apply_inv_eq_apply_zero_of_depth` and `continuous_of_depth` are what turn it into the substitution
  and regularity steps; port them as the section order gives them.
* The engine is `setIntegral_lowShell` / `setIntegral_tailShell` / `setIntegral_norm_tailShell`,
  `modulus_of_mem_genShell`, `genShell_neg_eq_smul`, `genShell_zero_eq`, `setOf_valued_eq_genShell`,
  `distribHaarChar_inv_pow`, `ord_inv_pow`, `modulus_inv_pow_mul`, `integrableOn_genShell`, then
  `integral_smoothWeylIntegrand_impl`.
* Do **not** transcribe the pin's `maxHeartbeats`/`synthInstance.maxHeartbeats` overrides: every one met
  so far has fitted the low cap once the inference was fixed (LI-1 confirmed it for
  `integers_diff_zero_eq_iUnion`). Diagnose an overrun, do not raise the cap.
* Pin-verbatim proofs will collect v4.34 deprecation warnings (`diff` → `sdiff` and friends): adapt them,
  do not investigate (FR-0016). The module must be warning-free.

## 6. Build discipline (copy verbatim into the report)

> Edit loop `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` — the cap is
> **low on purpose**: a declaration that exceeds it has an instance-inference defect. Never raise
> `maxHeartbeats`, never add a module `set_option maxHeartbeats`. `lake build <module>` per finished
> file, serialized with `flock` and bounded with `timeout`. Per wave, build only the wave's affected
> targets — **never a bare whole-tree `lake build`**. A whole-tree build happens once, at the session's
> end, only after the user agrees to it, and never on the agent's own initiative.

## 7. Stop conditions

**Stop and report** when: a needed declaration is `private` in a frozen module (name it — the manager
promotes it); a fix needs an edit to any existing module (name the host and the `build_ladder.py --edit`
price); a declaration cannot fit the low cap after a genuine instance-inference fix; or a statement's
binders cannot be taken from the wrapper. Do not touch `spec/old_check_stmts.py`, do not add to
`SOURCES`/`PORT_FILES`, do not edit the three `Weyl*` modules.

## 8. Report shape

* the module written, its declaration counts (public / private), and the tier-1 build line;
* the list of helpers that were **imported** from LI-1 rather than written, and the list of those
  genuinely new;
* `#print axioms` on the headline;
* the exact public declaration list for the checker wiring (expected: the headline, and nothing else);
* what was left unported and why; the friction entries appended, by id; the build-discipline block.
