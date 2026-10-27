# Mathlib API drift, mathlib `v4.34.0`

**Status: the port's drift checklist, moved out of the playbook's §7 (2026-10-23).** Re-run it when a
new pin is taken, and append here — a drift row belongs in this table, not in a work order. Bare
section numbers (§3.5, §4, §6) refer to [porting-playbook.md](../porting-playbook.md); the pin's own
conventions are in the same file's §4.

API drift is the recurring real cost. **The pin is not on this line**:
`anthropics/fermats-last-theorem@aa2d8b3` is Lean `v4.33.1` / mathlib `db584cd6`, the port Lean
`v4.34.0` / mathlib `v4.34.0`. Do not write "the pin is on the same mathlib line" into a work order.

| old / expected | `v4.34.0` |
|---|---|
| `if_pos h`, `if_neg h` | `ite_eq_left h`, `ite_eq_right h` |
| `dif_neg h`, `dif_pos h` | `dite_eq_right h`, `dite_eq_left h` (the four are `@[deprecated]` since 2026-07-21; 14 sites in `RegularProlongationFinrank`) |
| `Polynomial.finite_setOf_isRoot` | `Polynomial.finite_setOfPred_isRoot` |
| `Polynomial.finset_sum_coeff` | `Polynomial.finsetSum_coeff` (v4.34 rename; the old name is a `@[deprecated]` alias — `DeuringNormResidue:193`) |
| `Set.mem_setOf_eq` | `Set.mem_ofPred_eq` |
| `Affine.Nonsingular x y` | `W.toAffine.Nonsingular x y` (curve explicit) |
| `Submodule.card_bot` | does not exist — `AddSubgroup.card_bot` |
| `Submodule.mem_torsionBy_iff.mp` | takes explicit args: `(… _ _).mp` |
| `mul_cancel_left_mem_nonZeroDivisors` | `mul_left_cancel₀` in a domain |
| `Jacobian.map` | a separate def from `WeierstrassCurve.map` (defeq) |
| `Affine.Point.some_ne_zero` | does not exist — `cases` on the equality |
| `ext i` on `Fin 3 → MvPolynomial …` | recurses; use `funext i` |
| `nTorsion n` (`n : ℕ`) | `Submodule.torsionBy ℤ M n` takes `n : ℤ` |
| `HahnSeries.embDomain_notin_range` | `HahnSeries.embDomain_of_notMem_range` |
| `isIntegral_algebraMap_iff` | takes `FaithfulSMul`, not an injectivity proof |
| `Submodule.torsionBy.zmodModule` | does **not** exist — the instance is `AddSubgroup.torsionBy.zmodModule`; keep the pin's local instance under its own name |
| `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal` | argument order changed: `(f) (hf) (I)` |
| `Monoid`/`Group`/`Ring` projection chains `.1.1.1` | use `g.mul`, or `(g.mul, g.add)` |
| `Equiv.module` / `Equiv.linearEquiv` | `AddEquiv.*`, with instance diamonds needing explicit instance arguments |
| `TFAE.out` | 1-based: `.out 0 2` → `.out 1 3` |
| `continuous_add_right a` | does not exist — `continuous_id.add continuous_const` |
| `eventually_of_mem h …` | namespace-qualified: `Filter.eventually_of_mem h …` |
| `unfold yGen` (a `def` wrapping another `def`) | `unfold yGen yCoord` — the pin's one-name unfold leaves the inner `def` folded |
| `Polynomial.induction_on`'s `monomial` step | v4.34 states the step `motive (C a * X ^ n) → motive (C a * X ^ (n + 1))`; the pin's `monomial n a ih` proof transcribes unchanged |
| `range f`, `mem_univ`, `isPreconnected_univ` | `Set.range f` / `Set.mem_univ` unless the module `open Set`s (the pin does); `isPreconnected_univ` is unqualified |
| `Uncountable ℝ` (for `Complex.ofReal_injective.uncountable`) | an instance only once `Mathlib/Analysis/Real/Cardinality.lean` is imported, which is **not** transitive through `Analysis/Complex/Basic`; add the specific module |
| `Equiv.infinite_iff` | for `e : α ≃ β` it reads `Infinite α ↔ Infinite β`; check the direction at the call site |
| `Prime.dvd_finset_prod_iff` | `Prime.dvd_finsetProd_iff` |
| `ModularForm.coe_smul`, `ModularForm.coe_zero` | `FunLike.coe_smul`, `FunLike.coe_zero` (the `ModularForm.*` names are deprecated aliases) |
| `Finite.of_equiv` / `Set.toFinite` | `Nat.finite_of_card_ne_zero`, with the `Finite` instance passed explicitly |
| `Nat.card_zmod` | no longer needs `NeZero m` — the pin's `haveI : NeZero m` is dropped, not suppressed |
| `Isometry.antilipschitz.properSpace` | `Isometry.antilipschitzWith.properSpace` (same proof, warning-free) |
| a "statement-identical" substitute offered by `port_advise` | check the **direction**: the port's `RealIwasawa.rot θ` is the transpose of the pin's local `rotMat θ` (= `rot (-θ)`). Substituting at `+θ` compiles and silently flips every downstream character identity; substitute at `-θ` and let the pin's statements stay verbatim |
| a short last name (`add`, `smul`, `zero`, `sum`) on a pin-**public** declaration | a pin source that carries an unrelated `add` of its own makes it a `MISMATCH`, and an `own:` row would only hide the collision: keep those `private` (they are structure lemmas of a local namespace) and say so in the note |
| `exists_subset_nhds_of_isCompact'` with a pointwise `(hU : ∀ x ∈ ⋂ i, V i, U ∈ 𝓝 x)` | v4.34 takes set-relative `(hU : U ∈ 𝓝ˢ (⋂ i, V i))`; wrap the pin's lambda in `mem_nhdsSet_iff_forall.mpr` — the proof content is unchanged |
| `zero_le'`, `not_lt_zero'` | `zero_le`, `not_lt_zero` (the primed forms are deprecated aliases) |
| a literal pair passed where `AdeleRing R K` is expected, and `.1`/`.2` of it taken by `rfl` | `AdeleRing` is a plain `def` (`InfiniteAdeleRing K × FiniteAdeleRing R K`), so the pair is an adele only at *default* transparency: `rw`/`simp` fail with "not type-correct under the implicit transparency level". Bind it once — `set x : AdeleRing R K := (…) with hx` — then rewrite on `x.1`/`x.2` via `show … from by rw [hx]` (`by rw [hx]` already closes it). `erw` is a trap: it unfolds far enough to also unfold the definition under study, and the following projection rewrites then find nothing |
| `⟨dConjMat ℓ γ, ⋯⟩` as an `SL(2, ℤ)` element inside a `Subgroup` membership goal | `Matrix.SpecialLinearGroup` is a semireducible `def` (a `Subtype`) in v4.34, so the anonymous constructor elaborates at `{A // A.det = 1}` and the following `rw [Gamma_mem]` fails with "target expression is not type-correct under the implicit transparency level". Bind it first — `let x : SL(2, ℤ) := ⟨…, h⟩` — then `rw [Gamma_mem]` (or `mem_Lam0`) and `show` the entrywise conjunction; it also removes the pin's `simp only [Matrix.SpecialLinearGroup.coe_mk, …]` blocks |
| `TensorProduct.induction_on` (with a `| zero =>` branch) | `TensorProduct.inductionOn`, and it has **no `zero` case** — drop the branch (that case is the internal `tmul 0 0`), so the pin's case split loses an arm, not only a name |
| a `def` structure value whose projections must reduce inside `change`/`rw` (a prolongation built by `⟨…⟩`, then `(gaussProlongation hT A).integers`) | a plain `def` does **not** reduce at `implicit` transparency ("target expression is not type-correct under the implicit transparency level"): declare it an `abbrev`. The `AdeleRing` and `SpecialLinearGroup` rows above are the same class with the other cure — there the value is bound once, here the definition itself must unfold |
| `rw [← hα]` where `hα : IsLocalRing.residue A α = κ` and the term sits under `Algebra.smul` (`RegularProlongationFinrank.mem_of_mem_span`) | `ResidueField A` is a `def` (an `Ideal.Quotient`), so the rewrite installs the *quotient* spelling of the scalar, and `SMul (A ⧸ maximalIdeal A) Fbar` only resolves at default transparency → "target expression is not type-correct under the implicit transparency level". Keep the scalar syntactic: `have hα' : IsLocalRing.residue A α = κ := hα`, then `rw […, hα', Algebra.smul_def]` |
| `Submodule.linearProjOfIsCompl` (+ `_apply_left`/`_apply_right`/`_range`, `IsCompl.projection*`) | `@[deprecated (since := "2026-05-04")]` aliases of `Submodule.projectionOnto` / `projection` / `projection_apply_left` / `projection_range` — use the new family; the substitution is proof-side only, the pin's statements stay verbatim (`ArchCutProjector.projCA*`) |
| `push_neg at h` | `push Not at h` in `v4.34.0` — `push_neg` is the deprecated alias and warns, so a pin that already writes `push Not` (the v4.33 spelling of the same tactic) transcribes **unchanged**. Check the pin's spelling before "adapting" it: `BaseChangeCorrespondence` needed no change here |
| the pin's `variable (F) in` … `def foo : Prop` (a declaration whose binder block is a `variable … in` prefix) | transcribe the prefix **verbatim**, with the docstring *after* it (`variable (F) in` newline `/-- … -/` newline `def foo`). The checker extracts the statement without the prefix, so spelling the binders inline builds but reports `MISMATCH`; and putting the docstring *before* the prefix does not parse (the docstring attaches to the `variable` command). Both were hit on `Place/ComplexDictionary.lean`'s `OrderHypothesis` |
| the pin's `set x … with hx` (a named local, equation lemma unused) | v4.34 has **three** binding forms with different defeq behaviour, and the wrong one is a `whnf` blow-up: a `have`-bound value is *not* zeta-transparent (`have a : ℕ := 5; rfl : a = 5` fails), `set` additionally **abstracts every occurrence in the goal** — with the whole `∃`-pack abstracted, the correspondence-descent headline ran past 200k heartbeats — and `let` is both transparent and cheap. Use `let` when the pin's named local must reduce (`S_…constantFieldDescent_correspondence`) |
| the pin's `beta_reduce` in a `Finset.sum_bij` block | `v4.34.0` presents that goal already beta-reduced, so `beta_reduce` trips `linter.unusedTactic`; delete it — a no-op step, not a missing normalization |
| a `simp only [ …, Matrix.of_apply, … ]` (or `change`) that must reduce the `Matrix.of` entries of an `AdeleRing`-valued component | the entries are projections of the product `def`, so keyed `rw`/`simp` matching at `implicit` transparency cannot see through `x.1`/`x.2` and the goal silently does not change — same class as the `AdeleRing` pair row above, with the other cure: **restate the goal at default transparency instead of hunting for a lemma**, `rw [show ∑ k : Fin 2, … = ∑ k : Fin 2, ka … from rfl]`, or a function `show …` before the `rw`. Five sites in `IwasawaWeylUnipotent` (four branches of `kMat_mul_kMatInv`/`kMatInv_mul_kMat`, one in `glArch_kappa_eq`); the pin's own `rw […]` / `split_ifs <;> rfl` tails then transcribe unchanged |

The recurring *shapes*, beyond a rename:

- **A rename is not a re-typed or re-ordered lemma**: an API move can change argument order, its
  module, and the shape of a sum. A pin statement kept under a reasoned
  `set_option linter.deprecated false` is a residual item, not a silent pass.
- **A lemma can *narrow*: same name, stronger hypotheses** (e.g. `Integrable.mul_prod` gaining
  `[SFinite ν]`), and the gap can run through a whole API. Then the pin statement has no route
  through mathlib: isolate the missing input, keep a port-only lemma, defer with a
  [CARRY-FORWARD.md](../CARRY-FORWARD.md) entry — never weaken the statement.
- **A module path is not always a module** (`Mathlib.LinearAlgebra.Quotient` is a directory —
  import `.Basic`), and **blanket `import Mathlib` hides transitive dependencies** (expect 3–5
  missing per file).
- **An unused *statement* binder** (a hypothesis the pin's proof never uses) is silenced by
  `have _ := h` in the proof, not by `clear h` — the linter counts the binding, and `clear` removes
  it. Renaming the binder is the one thing not to do: the checker diffs the statement text.
- **An unused variable is a warning, not a defect**: a pin lemma that does not use
  `[NumberField F]` (e.g. a `rfl`-shaped identity) needs `omit [NumberField F] in` above it, not a
  weaker signature (19 such sites in `IwasawaWeylUnipotent`, all still diff `ok` — the prefix is not
  statement text); and a lambda whose binder is unreferenced (`fun v => rfl` in a `∀ v, …` slot)
  becomes `fun _ => rfl`. Both are `linter.unusedVariables` in v4.34.0 and neither touches the
  statement.
- **Tactics and terms change shape silently**: `convert h2 using 1` reorders goals (use
  `h2.congr_deriv`), `congr(...)` yields a different equation, a non-reducible `def` stops
  unfolding (bind with `let`), and `open` can create ambiguity — qualify instead.
- **Self-base-change is not definitional in `v4.34.0`**: carry `have hb : (E F).baseChange F = E
  F` and transport with `hb ▸ ⟨e⟩`.
- **Transcribe the pin's `linter.*` suppressions exactly; never its `maxHeartbeats`** (86 landed
  modules carry `set_option linter.unusedSectionVars false`). The gate is a warning-free tier-1
  elaboration, and classes the pin does *not* suppress are real — fix those as proof edits; the
  `haveI` style-linter fix is not universal, so suppress locally rather than weaken the proof.
- **A pin's `set_option maxHeartbeats N in` and its `synthInstance.maxHeartbeats` bump are claims
  to re-measure, not facts**; every one met elaborated at the low cap once the inference was
  found — and some needed no inference found at all: a transparency setting
  (`backward.isDefEq.respectTransparency false`) or a bulk budget was carrying an ill-shaped proof,
  and the fix was to restructure the proof, not to supply an instance. A *statement*-level cost is
  neither: the pin's `16000000` on the `PeriodizeLift` section was precaution (the library's 4M
  already sufficed, at 429 s), no inference fix moves it, and the fix is a named hypothesis type
  plus registered `own:` rows (§3.5, [../logs/poisson-summation-statements.md](../logs/poisson-summation-statements.md)). A library theorem can
  be cheap while its *concrete-instance* use is not: keep a `spec/` capstone zone hypothesis-form
  and put concreteness in the ground field. Two more confirmations from the descent wave: the
  pin's `maxHeartbeats 6400000` **and** `synthInstance.maxHeartbeats 1600000` on
  `exists_constantFieldDescent_correspondence` both go, the proof meeting the defaults once the
  two `hfin₀` models are `haveI`-registered and `Algebra.IsAlgebraic.of_finite` is supplied
  explicitly at each level (the `Algebra.IsAlgebraic ↥K₀⟮x₀⟯ ↥K₀⟮x,y⟯` search does exceed the
  default 20000 — so this one bump was a real search cost, met by the explicit instance rather
  than a budget).
- **`time` under-reports `lake env lean`** (the forked grandchild's CPU is not charged).
- **`end A.B` closes *both* nested scopes**, silently de-nesting every later declaration; write
  two bare `end`s, since the symptom appears downstream. (Naming every `section` is the safer
  house style: a bare `end` immediately followed by `end Name` is also mis-read by
  `spec/lean_parser.ENCLOSE_RE` until that is fixed — [CARRY-FORWARD.md](../CARRY-FORWARD.md).)

Two cross-cutting facts: `CuspForm` does not extend `ModularForm` (bridge with
`CuspForm.toModularFormₗ`), and `(W.map f).IsElliptic` is all a base-change `IsElliptic` instance
needs.
