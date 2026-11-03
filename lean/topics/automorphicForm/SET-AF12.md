# SET-AF12 — the local Whittaker profile: the Casimir equation at a real and a complex place

**Status: LANDED 2026-11-02** — the manager's layer plus one dispatch, both orders, all gates green;
**§5.1 records the landing and the re-read**. The order is
[WORKORDER-AF12-whittaker-local.md](WORKORDER-AF12-whittaker-local.md). Read off the D–S shelf with
the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md), on the tree
SET-AF11 left. It is the **twelfth** `AutomorphicForm`-serving set, and the column's return to the
**local** side: after four sets about adelic objects (the archimedean derivative algebra, the cusp
subrepresentation, the complex Casimir, and the coefficient's API), this one is about the
one-variable function the coefficient's Fourier expansion is built from — the archimedean Whittaker
profile — and about the second-order equation the Casimir forces on it.

The set is **3 rows / 1,126 silo, 1,033 lines to write in 63 declarations** (1,070 net by
`port_plan`), in two orders: the local equation at a real and at a complex place, and the one row
SET-AF11 readied.

| order | rows | silo | work | home |
|---|---:|---:|---:|---|
| A — the local Whittaker Casimir pair | 2 | 1,042 | 965 | new `AutomorphicForm/Adelic/ArchWhittaker.lean` |
| B — the row SET-AF11 readied | 1 | 84 | 68 | `AutomorphicForm/Adelic/WhittakerCoefficient.lean` |
| | **3** | **1,126** | **1,033** | two files, one dispatch |

## 0. The read

### 0.1 The figures

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf-af11-landed.json
python3 frontier.py --selfcheck
```

| figure | value | SET-AF11 §5.1 (at its landing) |
|---|---:|---:|
| `needed [F terminal]` | **868 / 353,051** | 868 / 353,051 |
| `needed [literal]` | 881 / 356,526 | 881 / 356,526 |
| frontier F | **1,547 / 774,315** | 1,547 / 774,315 |
| ready rows, all namespaces | 67 / 17,980 | 67 / 17,980 |
| ready rows, `AutomorphicForm` | **38 / 12,636** | 38 / 12,636 |
| leaves, all namespaces | 234 / 59,837 | 234 / 59,837 |
| leaves, `AutomorphicForm` | **65 / 13,798** | 65 / 13,798 |
| withheld by the FR-0044 guard | 4 / 831 | 4 / 831 |
| avoided by `--ds` (the prunable set R) | 140 / 74,620 | 140 / 74,620 |
| `--selfcheck` | **PASS** (4 checks; 1,366 `Thm_` sources, 1,547 declared names) | PASS |
| correction | **none needed** | none needed |

The read is SET-AF11's landing read to the line — the two readings are the same tree, so the only
thing this pass adds is the disposition. Both blocks are quoted whole and every row accounted for in
Appendix A: 38 ready rows / 12,636 and 65 leaves / 13,798, of which 3 are this set's and 100 deferred
(§7 gives the reasons by group; the rest are one-line `deferred`). The withheld block is the same
four rows as at AF11's scoping (two `ModularCurve` Tate-module rows, two `AlgebraicCurve` Pic₀ rows,
831 lines): the prunable subject's work, not this column's.

### 0.2 Why the local equation, and not the three larger ready rows

The three largest ready rows are still the Weyl-integrand pair (1,349 + 1,291) and
`isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow` (1,043). Each is a set of its own and
each is *bigger* than this one: the pair is one story at **2,640 silo** — two orders — and the 1,043
row drags the flat Eisenstein/induced-section development (with
`exists_flat_isInducedSection_family_eq_of_isInducedSection` 325,
`constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral` 257 and
`exists_flatEisenstein_mul_le_mul_archHeight_rpow_of_mem_centreCutSiegelSet` 431 and
`bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family` 624, a 2,680-silo block). Both are
correct next sets; neither is this one.

The local pair is the cut because it is the **engine of the column's next analytic subject**, and
because for the first time the port's archimedean algebra makes it cheap:

- it is the missing premise of **three unported rows**: the two `su2String` consumers
  (`exists_forall_whittakerCoefficient_diagOne_eq_mul_of_isComplex_of_su2String`, 473, and
  `exists_norm_whittakerCoefficient_diagOne_le_min_norm_rpow_of_isComplex_of_su2String`, **1,827** —
  the Whittaker bound) and
  `whittakerCoefficient_diagOne_satisfies_whittaker_ode_of_archCasimirAt_eq_smul_of_hasArchCharacterAt`
  (306). Those are the steps where the *global* coefficient is controlled by its local equation,
  which is the analytic heart of the Rankin–Selberg step the column is building towards;
- **it is the return on AF9's engine.** The rows are phrased entirely in the archimedean calculus
  AF9 landed (`archFlowMatrix`/`archFlowMatrixComplex`, `splitTorusGL2`/`splitTorusGL2Complex`,
  `circleGL2`, `rowIsometrySubgroup₀`, `archWeightCharℝ`, `ArchDir`/`ArchDirComplex`); before AF9
  this set would have been an engine build, now it is a transcription of the pin's own computation;
- its own leverage is small (**2/2** and **1/1** project consumers) and that is expected: each of
  the three consumers above is a single large row, so a 1,042-silo engine feeding 2,606 silo of
  consumer reads as two citers. AF9's "26-line leaf, 33 consumers" is the *other* pole; the defence
  here is the consumer list, not the leverage column.

**The honest cost of that defence: the immediate return is zero rows.** Each of the three consumers
needs more than this set's two rows:

| consumer | other unported premises |
|---|---|
| `whittakerCoefficient_diagOne_satisfies_whittaker_ode_…` (306) | the real ODE row (this set), `NumberField.StandardAddChar.stdAddChar_single_infinitePlace_of_isReal`, `NumberField.AdelicLevel.diagOne_mul_archRealGLAt_unipotent_eq_and_stdAddChar_single_half` — **neither is ported** |
| `exists_forall_whittakerCoefficient_diagOne_eq_mul_of_isComplex_of_su2String` (473) | the complex system (this set), `whittakerCoefficient_su2String_gl2Complex_whittaker_system_hypotheses`, `LanglandsTunnell.linearDependent_string_of_gl2Complex_whittaker_system_of_moderateGrowth`, a `TateGlobal` idele-norm row |
| `exists_norm_whittakerCoefficient_diagOne_le_min_norm_rpow_of_isComplex_of_su2String` (1,827) | the complex system (this set), the `su(2)` leaf (755), four `LanglandsTunnell` `torus_system`/`bessel_ode` rows and a `TateGlobal` idele-norm row |

So this set readies **no** row; it removes one premise from three, and the readiness arrives with the
`su2String` hypotheses row, which needs the `su(2)` leaf. That is a *delayed* return, and it is the
main argument against this cut. The argument for it: the engine is a premise of all three, no other
set can supply it, it is 965 lines with a free definition gate, and the alternative cuts (the Weyl
pair 2,640, the flat-Eisenstein block 2,680) are two orders each. If the reviewer prefers an
immediate-return set, the Weyl pair is the choice; if the column wants the analytic engine in place
before the Rankin–Selberg step, this one is.

### 0.3 Why this is a transcription set, and what it costs

The two `S_` files are flat: `port_plan` finds **1** duplicate line and 36 boilerplate lines out of
1,042 raw, **no port-once block** (the two target files share no declaration), and no siblings. So
the work is the pin's proofs: **1,076 declaration lines, 43 imported, 1,033 to write in 63
declarations**. The shape is unusual for this column and worth stating:

- the **real** row is 330 declaration lines in **10** declarations, of which the headline's
  `solution` is 235 — a single long computation;
- the **complex** row is 678 declaration lines in **52** declarations, the largest declaration count
  on the shelf after SET-AF11's diagonal reduction. Its prelude is the special-function and Iwasawa
  calculus of one complex place (`exp (±t/2)`, `log`, `sqrt`, `arctan`, the `z ↦ exp (z I)` circle
  chart), not adelic analysis — the pin writes it as 51 small public lemmas and one 162-line
  `solution`;
- the **rider** is 68 lines in one declaration, and its single premise is SET-AF11's transformation
  law.

The 43 imported declarations are the archimedean API the port already has (the `ArchDir` →
`archDirMatrix` dictionary, `splitTorusGL2_mul`, the `circleGL2`/weight lemmas). They are imported,
never restated — but see §2: the *five* declarations the substitution tier claims are already in
the port are all unusable, so the practical import count is what the worklist says and no more.

### 0.4 The return on AF11, and why order B is 68 lines

SET-AF11 consumed nine rows and readied exactly one:
`whittakerCoefficient_finset_sum_mul_unipotentGL2_diagOne_mul` (**84** silo, 1 premise, leverage
2/3), whose one premise is `whittakerCoefficient_unipotentGL2_mul` — AF11's own transformation law.
It states the unipotent average at a `diagOne` point: for `G` invariant under the left unipotent and
a finite set `ι` of adelic parameters whose unipotent translates commute with `g`,

`whittakerCoefficient (∑ y ∈ ι, c y • G (· * n y)) α (diagOne a * g)`
`  = (∑ y ∈ ι, c y * ψ (α (a y))) * whittakerCoefficient G α (diagOne a * g)`,

which is the identity a Rankin–Selberg unfolding uses to read a coefficient at `diagOne` off a sum of
translates. It is 68 lines in one declaration and lands in the coefficient's module, so order B is
one wire line and one proof: the cheapest honest way to record that AF11's fan-in argument produced
something, and it does not touch order A's file. If order A overruns, order B is droppable without
re-cutting the set (its wire is independent).

## 1. The three rows

| row (`AutomorphicForm.` dropped) | silo | work | decls | prem | lev | what it states |
|---|---:|---:|---:|---:|---:|---|
| `gl2Real_whittaker_ode_of_casimir_of_unipotent_covariant_of_weight` | 347 | **315** | 10 | 0 | 1/1 | for `F : GL₂(ℝ) → ℂ` with Casimir eigenvalue `lam`, unipotent character `e^{2πiεx}` and `K`-weight `n`, the profile `f(y) = F (diag (√y, 1/√y))` is twice differentiable on `y > 0` and satisfies the classical Whittaker equation `y²f'' + (1/4 − ν² + 2π ε n y − 4π² y²) f = 0`, with `ν² = 1/4 − lam` |
| `gl2Complex_whittaker_system_of_casimir_pair_of_unipotent_covariant_of_circleWeight_of_ktype` | 695 | **650** | 52 | 0 | 2/2 | the complex twin, vector-valued: for `F : Fin (n+1) → GL₂(ℂ) → ℂ` with the two Casimir eigenvalues `lam`, `lam'`, unipotent character of frequency `2κ`, circle weight `n − 2p`, and the two weight-`n` matrix families `E₁`, `E₂` of the maximal compact, the profiles `f p y = F p (diag (√y, 1/√y))` satisfy **two coupled second-order equations per `p`**, the first raising `p → p+1` and the second lowering `p → p−1` (a finite band, with `‖κ‖²` and `κ`, `κ̄` in the coefficients) |
| `whittakerCoefficient_finset_sum_mul_unipotentGL2_diagOne_mul` | 84 | **68** | 1 | 1 | 2/3 | the unipotent average at a `diagOne` point is the character-weighted sum times the coefficient of the un-averaged function (§0.4) |

The complex row's conclusion is a **long conjunction**: differentiability of each profile and of its
derivative on `Set.Ioi 0`, then the two equations at every `p`. Its hypotheses are six
conjunct-wise families (`hD`, `hDD`, `hΩ`, `hΩ'`, `hN`, `hM`) plus the two matrix identities (`hE₁'`,
`hE₂'`) and the two covariance laws (`hK₁`, `hK₂`) — the weight-`n` representation of the maximal
compact, written out. Copy the wrapper binder for binder; the statement probe (§5) is the check.

## 2. The price

```bash
cd tools/deps
python3 port_advise.py --nodes AutomorphicForm.gl2Real_whittaker_ode_of_casimir_of_unipotent_covariant_of_weight \
  --nodes AutomorphicForm.gl2Complex_whittaker_system_of_casimir_pair_of_unipotent_covariant_of_circleWeight_of_ktype \
  --json build/af12-advise.json
python3 port_plan.py --json build/af12-advise.json
python3 build/af-worklist.py whittakerCoefficient_finset_sum_mul_unipotentGL2_diagOne_mul \
  gl2Real_whittaker_ode_of_casimir_of_unipotent_covariant_of_weight \
  gl2Complex_whittaker_system_of_casimir_pair_of_unipotent_covariant_of_circleWeight_of_ktype
```

**`port_plan` (order A).** raw **1,042** → declaration lines **1,006** → −1 duplicate copy → 1,005
once-cost → −2 already in the port → **NET NEW 1,003**; boilerplate 36. **No** port-once block and
**no** siblings block: the two rows share nothing and neither generalises the other. **Order B:**
raw 84 → 67 declaration lines → **67 net**, 0 duplicates, 0 in the port, 0 substitutions.

**The five `port_advise` substitutions are all unusable, and the reading of them is the pass's one
real finding.** The tool reports 5 (`2 trusted / 3 suspect`); read one by one they are:

| pin declaration | pin line | claimed port copy | why it is not usable |
|---|---|---|---|
| `rotS` (12) | `:44` | `ArchCasimirComplex.rotGL` | **different matrix**: `rotS s = !![cos s, I sin s; I sin s, cos s]`, `rotGL` is the real rotation; and the port's `rotGL` is `private`, so it is not importable |
| `rotR` (10) | `:34` | `ArchCasimirComplex.rotGL` | same matrix, but `private` in another module: not importable |
| `sqrt_one_add_sq_pos` (2) | `:64` | `RealIwasawa.HARCHR.sqrt_pos'` | `private`, not importable |
| `zeta` (2) | `:229` | `ModularCurve.RelIndex.expU` | **different function**: `zeta t = exp (t I)`, the port's `expU x = exp (2π i x)` — substituting it would silently change the character |
| `sqrt_one_add_sq_pos` (1) | `S_…gl2Real…:52` | `RealIwasawa.HARCHR.sqrt_pos'` | `private`, not importable |

So **0 substitutions are importable**; the handful of lines involved (`rotR`, `rotS`, `zeta`,
`sqrt_one_add_sq_pos`) are written here at the pin's statements. This is the recipe's own warning
about `def`-shaped matches, measured: a type-only match can be a *private* copy or a *different
function*, and both read as "trusted".

**The per-declaration worklist** (Appendix B): 1,076 declaration lines, **43 imported**, **1,033 to
write in 63 declarations**. The two largest single blocks are the real row's 235-line `solution` and
the complex row's 162-line one; the largest prelude items are `deriv_iwasawa_sum` (40) and `sum_M2`
(31) at the complex place.

## 3. The definition gate

`spec/gate_scan.py` over the three `Def_` modules the two wrappers' closure reaches, both rows:

| pin `Def_` module | port home | used (max) | missing |
|---|---|---|---:|
| `Def_AutomorphicForm_ArchDerivCasimir` | `…/Adelic/ArchDerivCasimir.lean` | 2/56 | **0** |
| `Def_AutomorphicForm_ArchWeightChar` | `…/Adelic/ArchWeightChar.lean` | 9/19 | **0** |
| `Def_AutomorphicForm_ArchDerivCasimirComplex` | `…/Adelic/ArchDerivCasimirComplex.lean` | 3/32 | **0** |

Two things about that table are worth recording, because the first is the FR-0117 class again and
the second is new:

- **the real wrapper's statement names `archWeightCharℝ` and `rowIsometrySubgroup₀`, and its
  `import` list does not name `Def_AutomorphicForm_ArchWeightChar`.** The module enters through
  `Def_AutomorphicForm_ArchDerivCasimir`'s own imports. A closure read off the wrapper's `import`
  lines sees two `Def_` modules, not three; the per-module `gate_scan` over the *union* is what sees
  the 9/19 row. Run it per `Def_` module, not per import line;
- **`ArchWeightChar.lean` is legacy** (`PORT_FILES`, no `spec-pin:`). It is imported, not edited, so
  no migration is owed (the recipe's own rule: a legacy module migrates when a set *edits* it). If a
  proof needs one of its `private` helpers, that is a promotion for the manager — not a local copy.

**The mathlib side.** The pin's `S_` files import
`Mathlib.Analysis.SpecialFunctions.{Log.Deriv, Pow.Deriv, Sqrt, Trigonometric.Deriv,
Trigonometric.Arctan, ExpDeriv, Log.Basic}`; all exist at `v4.34.0` and are the only imports the port
module needs beyond the two Casimir homes. Recorded negatives: the port has **no** Whittaker-equation
engine (`AutomorphicForm/Iwasawa/Real/Continuation.lean` has the archimedean chart, but its lemmas
are `private` and it is about the Iwasawa integral, not the profile), and mathlib has no
Bessel/Kummer class of solutions — the pin's computation is the route.

## 4. The homes

**Order A — a new module, `AutomorphicForm/Adelic/ArchWhittaker.lean`.** The subject is the
archimedean Whittaker profile and the equation the Casimir forces on it; nothing in the port is about
that object (`WhittakerCoefficient.lean` is the *global adelic* coefficient; `ArchSpherical.lean` is
the spherical test-function predicate; `IwasawaWeylUnipotent.lean` is the Iwasawa calculus). The
module is cascade-free, imports `ArchDerivCasimir` and `ArchDerivCasimirComplexAPI`, and wires the
two `Theorems/` wrappers **and the two `S_` files**.

**The surface decision, and it differs from SET-AF11's.** The pin's two `S_` files are a **flat
public surface**: 57 public declarations in the complex file and 13 in the real one, with **no
`private` prelude** (`port_advise`'s drags section: "same-file closure adds 0 helpers"). AF11's
helpers were the pin's per-file *private* preludes, hence private here; these are the pin's public
development, and the recipe's surface gate says the checked surface should equal the mathematics
claimed. So the engine is **public at the pin's names** and the two `S_` files are in the wire:
`check_port` should read **69 ok**, not 2 — measured at landing, and seven more than this set's
estimate: Appendix B omits the seven chart declarations the pin states outside the worklist's
declaration list (`kIw`, `rotR`, `rotS`, `zeta`, `aT` and one `sqrt_one_add_sq_pos` per place), each of
which hashes at its own pin site. A `MISSING` there is a port-side helper the pin does not have (keep
it private), and a `MISMATCH` on an engine declaration is a spelling to fix, not a name to privatise.

**Import direction, measured.** The closures of `ArchDerivCasimir` and `ArchDerivCasimirComplexAPI`
are 16 and 18 modules; both contain `ArchWeightChar` (via `ArchWeightCharTransport`) and neither
contains `WhittakerCoefficient`, so a module above both is acyclic and can host both rows. There is
no legacy edit and no promotion in this set.

**Order B — `AutomorphicForm/Adelic/WhittakerCoefficient.lean`**, the coefficient's own module (its
"API, VII" section). One wire line:
`spec-pin: Theorems/Thm_AutomorphicForm_whittakerCoefficient_finset_sum_mul_unipotentGL2_diagOne_mul.lean`
(11 lines total), and the module's checker count goes 13 → **14**.

## 5. The cut

**Two orders, one worker, disjoint files:** order A writes a new module (1,003 net math lines in the
`port_plan` count, 965 by the worklist, 62 declarations), order B appends one declaration to the
coefficient's module (68 lines). The files do not import each other in either direction, so the
worker builds each once and never pays a cascade across them; only the build lock is shared.

**Order.** A first, B second: B is the cheap rider and must not delay the engine; if A raises a
blocker, B is droppable without re-cutting anything (§0.4).

**The manager's layer** is: the two new wires in the coefficient module and the four in the new
module, the new module's skeleton, **a statements probe** of all three headlines against the intended
homes, and the `Def_`/legacy question of §3. No `Def_` node, no promotion, no migration. The probe is
the check that has caught a missing `open` in every set since AF8, and this set's statements are the
most binder-heavy on the shelf (the complex one has ten hypothesis families).

**Gates.** No tree build; each module's own `lake env lean -DautoImplicit=false
-DmaxHeartbeats=200000` silent and its own `flock`/`timeout 280 lake build`; `check_port --force` →
`0 mismatch / 0 missing` (the coefficient module 13 → **14**; the new module **69**, measured, and the
recipe's surface gate applied: with `private` dropped on everything the pin has public, read the
three numbers again); `#print axioms` on all three headlines → `[propext, Classical.choice,
Quot.sound]`; zero warnings; `dedup`/`move_dead` per module; and one
`spec/AutomorphicFormSetAF12Consumer.lean` zone that composes order A with AF11's
**differentiability** row: instantiate the real ODE at the local component of the coefficient,
`F h := whittakerCoefficient stdAddChar φ 1 (g₀ * archRealGLAt hw h)`, reading `hD` from row 8's
derivative identity and `hΩ` from its Casimir conjunct, and conclude that
`y ↦ whittakerCoefficient … (g₀ * archRealGLAt hw (splitTorusGL2 (log y / 2)))` satisfies the
Whittaker equation — the classical statement that the local equation holds for the adelic
coefficient's local component, which is what the three consumer rows need.

### 5.1 The landing (2026-11-02)

**Files.** `AutomorphicForm/Adelic/ArchWhittaker.lean` 63 (skeleton) → **1,073** (+1,010);
`AutomorphicForm/Adelic/WhittakerCoefficient.lean` 1,404 → **1,474** (+66 declaration lines);
`spec/AutomorphicFormSetAF12Consumer.lean` (123, new). **70 declarations: 69 public in the new engine
(12 at the real place, 57 at the complex one) and 1 public in the coefficient module — no `private`
anywhere**, which is the surface decision of §4 taken seriously: the pin's two `S_` files are a flat
public surface, so the port's surface is the pin's.

**69, not 62, and why.** Appendix B lists 62 declarations to write; the pin's two `S_` files also state
seven chart declarations the worklist's declaration list does not carry (`kIw`, `rotR`, `rotS`,
`zeta`, `aT`, and one `sqrt_one_add_sq_pos` per place). All seven are written at the pin's statements —
in particular `zeta t = exp (t · I)` and `rotS s = !![cos s, I sin s; I sin s, cos s]`, the two names
the substitution tier claimed were already in the port (§2: one is a *different function*, the other
a *different matrix* plus a `private` copy). The checker reads **69 ok**, so every one of them hashes
at its own pin site.

**Gates, re-run by the manager.** Edit loop at `-DmaxHeartbeats=200000` **silent** (9.8 s / 6.9 s);
own `flock`/`timeout 280 lake build` green (3,609 jobs, no warnings); `check_port --force` **69 ok / 0
mismatch / 0 missing** and **14 ok / 0 / 0**; `#print axioms` on the three headlines
`[propext, Classical.choice, Quot.sound]`; the three-statement probe still exactly three `sorry`
warnings; the consumer zone 0 errors, 0 warnings; `dedup --within` 0 clusters on the coefficient
module and **one 1-line cluster** on the engine (`sqrt_one_add_sq_pos`, the pin's own duplication at
real `:52` and complex `:64`) — **kept**, because the two files are independent flat public surfaces
and each copy hashes at its own pin site, so merging would make the complex chart depend on the real
chart's namespace; `move_dead` 0/0/0 on both; the whole wired corpus `check_port --changed` **10,583
ok / 0 mismatch / 0 missing** (467 modules); the frozen checker unchanged at 6,886 identical / 3
mismatched / 18 missing (all pre-existing in `AlgebraicCurve/`).

**Deviations from the pin, all recorded.** The two label name spaces are renamed by subject
(`IwasawaAux` → `IwasawaChart`, `IwasawaC41` → `IwasawaChartComplex`; the `41` is a pipeline id — no
tokened name survives in code, and the header quotes the pin's labels only to say they were
dropped). `splitTorusGL2_coe'` is not restated: the port's `splitTorusGL2_coe` states it and is used
at all three pin sites. The rest are proof *shape* under the zero-warning gate (FR-0127): the pin's
`all_goals first | rfl | skip` is a `linter.unusedTactic` no-op wherever nothing closes by `rfl`
(~19 sites dropped) and its `convert … <;> first | …` becomes `convert … using 1` +
`all_goals first | …` (~8 sites — the linter's own `;` suggestion is unsound for goal-list-sensitive
`first` and broke two proofs when tried); `push_cast` no-ops and `simp [hre]` → `simp`; the
`if/dif` family → `ite/dite`; `open Complex Matrix` inside the complex namespace. The **statements
are byte-identical** — the checker's 69 ok is the proof, not the report.

**The complex chart transcribed cleanly.** 488 pin lines of one-place `exp (∓ t/2)` / `arctan` / `log`
/ `sqrt` calculus and the `E₁`/`E₂` matrix families went through structurally unchanged over the
port's `archFlowMatrixComplex`/`splitTorusGL2Complex`/`circleGL2` dictionary; no lemma needed a new
route, and the 162-line `solution` — its `sum_M1`/`sum_M2` index bookkeeping and the `p ± 1` band
coupling — ports verbatim apart from the `dif_pos` → `dite_eq_left` rename. The risk register's
"52-declaration prelude is the whole risk" was right about *where* the time goes and wrong about
*how much*: two compile iterations, 49 style warnings then silence.

**The consumer zone, and the set's forecast made precise.** The zone instantiates the real ODE at the
coefficient's local component, `F h := whittakerCoefficient … φ 1 (g₀ * archRealGLAt hw h)`, reading
`hD`/`hDHH`/`hDEF` from AF11's differentiability headline and `hΩ` from its Casimir conjunct composed
with the eigenvalue relation. It needs three hypotheses neither headline supplies, all stated and
reported, none papered over: the Casimir eigen-relation at the coefficient level (`hΩφ`, obtained
from the ODE's `hΩ` hypothesis through this set's additivity row at `m = 1`), the unipotent character
`hN`, and the weight-`n` law `hK`. **`hN` cannot be derived inside the set**: it needs
`NumberField.StandardAddChar.stdAddChar_single_infinitePlace_of_isReal`, which §0.2 already lists as
unported and which is the reason the 306 row is *not* readied below.

**Plan against actual.** Lines: **1,076 declaration lines written** (1,010 + 66) against the
worklist's 1,033 and `port_plan`'s 1,070 net — +0.6 % on the plan, and the excess is the seven chart
declarations Appendix B omits. Declarations: **70** against 63 (+7, same cause). Checker: 69 + 14,
with order B exact. No build-time incident: the largest declaration is far under the 200,000 cap.

**The re-read. It is exact on the demand side and it readies nothing.** The set's silo leaves the
figure to the line; the ready shelf loses exactly the rider and the leaves lose exactly the two ODE
rows, and **no row becomes ready**:

| figure | before | **after** | Δ |
|---|---:|---:|---:|
| `needed [F terminal]` | 868 / 353,051 | **865 / 351,925** | −3 / −1,126 ✓ (the three rows' silo, exact) |
| `needed [literal]` | 881 / 356,526 | **878 / 355,400** | −3 / −1,126 ✓ |
| frontier F | 1,547 / 774,315 | **1,550 / 775,441** | +3 / +1,126 ✓ |
| ready rows, all namespaces | 67 / 17,980 | **66 / 17,896** | −1 / −84 (the rider leaves) |
| `AutomorphicForm` ready rows | 38 / 12,636 | **37 / 12,552** | −1 / −84 |
| leaves, all namespaces | 234 / 59,837 | **232 / 58,795** | −2 / −1,042 (the two ODE rows) |
| `AutomorphicForm` leaves | 65 / 13,798 | **63 / 12,756** | −2 / −1,042 ✓ |
| withheld by the FR-0044 guard | 4 / 831 | 4 / 831 | — |
| `--selfcheck` | PASS (1,366 / 1,547) | **PASS** (1,369 `Thm_` sources, 1,550 declared names) | — |

The three consumer rows stay off the shelf (473, 1,827, 306 — §0.2's table lists their other
premises), so this is a set whose return is **a premise removed from three rows, not a row readied**:
the mirror image of AF10's narrow return and the second consecutive set whose ready-shelf delta is at
most one row. What is in place is the *engine*: the archimedean Whittaker equation is now port API, so
the next set can take the `su(2)`/circle-weight leaf (755, still a leaf) and then the three consumer
rows together — they are one story ("the coefficient at a `diagOne` point obeys the local equation and
is bounded by its solutions") and they are 2,606 silo.

## 6. Risk register

1. **The 52-declaration complex prelude is the whole risk.** It is a transcription of the pin's
   one-place calculus (`exp (±t/2)` chart, `arctan`, `log`, `sqrt`, the `circleGL2` parametrisation)
   with no adelic content, so it should transcribe cleanly — but it is 488 lines in 51 small
   declarations, and the `E₁`/`E₂` matrix families are part of the *statement*. Read the pin's `S_`
   file in dependency order (the `flow*` abbreviations and `psiK` first, then the `hasDerivAt_*`
   block, then the `sum_M*`/`deriv*_torus` block, then `solution`).
2. **The five false substitutions (§2).** Especially `zeta` vs `expU`: same type, different
   function. Write `zeta` (2 lines) and the two rotation helpers at the pin's statements.
3. **`sqrt_one_add_sq_pos` is `private` in `Iwasawa/Real/Continuation.lean`** — a 2-line re-statement
   here (or `Real.sqrt_pos.2 (by positivity)` inline). Do not promote it for this.
4. **Binder shadowing for the checker.** The headlines must spell the wrappers' binders inline
   (`(F : GL (Fin 2) ℝ → ℂ)`, `(n : ℕ)`, …): the checker hashes the signature text (FR-0123). The
   probe is the check, not the count.
5. **`linter.style.haveILetI` is live** (FR-0121): the pin's `letI`/`haveI` preludes become `let`/
   `have`, or one file-local `attribute [local instance]` block where a measurable structure is
   genuinely needed (this set needs none: it is archimedean, not adelic).
6. **`archFlowMatrix`/`archFlowMatrixComplex` are the port's flows** (`archFlowAt hw d t =
   archRealGLAt hw (archFlowMatrix d t)`), so the pin's `flowH`/`flowE`/… one-liners become the
   port's `archDirMatrix`/`ArchDir` dictionary; the `rfl`-level coefficient lemmas may need the
   port's `archMatrixUpdate` spelling (AF11 hit this in rows 8/9).
7. No `set_option`, no `native_decide`, no `sorry`/`admit`/`axiom`; zero warnings; no tree build; no
   new import beyond the two Casimir homes and the special-function modules named above.

## 7. What this set does not do

- **It does not take the Weyl-integrand pair** — `weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half`
  (1,349) and `LocalIntertwining.integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod`
  (1,291) — **2,640 silo**, one story and two orders. It is the natural *next* set: the integrability
  of the unramified Weyl integrand on a finite-adèle slice and the finiteness of its integral, the
  step the `LocalIntertwining` development has been building since AF6.
- **It does not take the flat-Eisenstein / induced-section block** —
  `isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow` (1,043),
  `bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family` (624),
  `exists_flatEisenstein_mul_le_mul_archHeight_rpow_of_mem_centreCutSiegelSet` (431),
  `exists_flat_isInducedSection_family_eq_of_isInducedSection` (325) and
  `constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral` (257) — **2,680 silo**, two
  orders (the height bound and the induced-section/constant-term layer are separable).
- **It does not take the `LocalIntertwining` archimedean atom cluster** — the two Gamma-factor leaves
  (`integral_one_add_sq_cpow_neg_eq_GammaReal_div` 362,
  `integral_one_add_norm_sq_cpow_neg_eq_pi_div` 102), the four integrability/tendsto leaves
  (`integrable_complexAtom_and_integrable_moebiusShift` 219,
  `integrable_realAtom_and_integrable_moebiusShift` 179,
  `tendsto_integral_normSq_rpow_sub_one_mul_complexAtom_nhdsGT_one_half` 170,
  `tendsto_integral_sq_rpow_sub_one_mul_realAtom_nhdsGT_one_half` 147) and
  `exists_bound_norm_integral_mixedSpace_archAtom_prod` (116) — **1,295 silo**. Same *technique* as
  this set (an archimedean integral evaluated in special functions), different *subject* (the local
  intertwining operator's atoms, not the Whittaker profile); it belongs with the Weyl pair.
- **It does not take the `su(2)`/circle-weight leaf**
  `su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional` (755): the
  representation-theoretic engine the two `su2String` consumer rows need, a set of its own (it is
  `su(2)`-representation theory, not analysis), and the row that makes the 473 and 1,827 consumers
  writable.
- **It does not take the three consumer rows it feeds** — `whittakerCoefficient_diagOne_satisfies_whittaker_ode_of_archCasimirAt_eq_smul_of_hasArchCharacterAt`
  (306) and the two `su2String` bounds (473, 1,827). They are the *point* of this set and they are
  not in it: each needs a global coefficient hypothesis this set's local rows do not supply, and
  the 1,827-line one needs the `su(2)` leaf above. They are the re-read's first question.
- **It does not take the high-fan-in API tail** — the ready rows with leverage ≥ 2 that are neither
  in this set nor named above: `exists_mem_adelicBorel_mul_eq` (372, **14/63**),
  `isKfSmooth_rightConv` (70, 7/21), `isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule` (242, 2/27),
  `SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine` (199,
  7/20), `exists_isFundamentalDomain_globalPoints_range` (165, 1/11),
  `isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_of_isFactorizableTestFn_of_support_subset`
  (290, 2/11) — plus the factorizable-test-function, `KfSmooth`-seam and constituent/spectrum tails.
  That is **85 further rows / 17,938 silo**, all `deferred` in Appendix A: an "API II" set, not this
  one, and the next scoping reads them again.
- **The 4 withheld rows / 831 silo** remain the prunable complex-analytic subject (FR-0044).
- **No `Def_` node, no promotion, no migration**: three `Def_` modules are consumed and all three are
  already ported (§3); `ArchWeightChar.lean` is legacy and is imported, not edited; the coefficient's
  module gains one wire and the new module is a new file.

## Appendix A — the shelf, every row accounted for

Generated from `build/shelf-af11-landed.json` by `build/af12-shelf-appendix.py` (silo, premises,
leverage, disposition).

### The ready block — **38 rows / 12636 silo**

| row | silo | prem | lev | disposition |
|---|---:|---:|---:|---|
| `weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half` | 1349 | 1 | 1/1 | deferred (§7) |
| `LocalIntertwining.integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod` | 1291 | 2 | 1/1 | deferred (§7) |
| `isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow` | 1043 | 3 | 1/3 | deferred (§7) |
| `bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family` | 624 | 3 | 2/5 | deferred (§7) |
| `SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_isGenuineCuspRealizationAt` | 527 | 2 | 1/2 | deferred (§7) |
| `SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_continuous` | 513 | 2 | 1/1 | deferred (§7) |
| `a_mul_conj_b_eq_and_norm_b_eq_of_sesqForm_covariant_of_ne_zero` | 468 | 2 | 2/4 | deferred (§7) |
| `rightTranslate_adjoint_weightedPairing_of_isLsXiFunction` | 433 | 4 | 4/10 | deferred (§7) |
| `exists_flatEisenstein_mul_le_mul_archHeight_rpow_of_mem_centreCutSiegelSet` | 431 | 3 | 1/5 | deferred (§7) |
| `hasDerivAt_rightConv_mul_unipotentGL2_and_isFactorizableTestFn_leftDeriv_and_linear` | 390 | 2 | 1/2 | deferred (§7) |
| `exists_mem_adelicBorel_mul_eq` | 372 | 1 | 14/63 | deferred (§7) |
| `SmoothCuspRealizationAt.exists_twist_rpow_absNorm_exceptionalSet_eq_toFun_eq_ideleNorm_det_rpow_mul` | 367 | 4 | 1/6 | deferred (§7) |
| `apply_weylInv_unipotent_mul_archSupportedAt_eq_norm_cpow_mul_apply` | 360 | 1 | 1/1 | deferred (§7) |
| `exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq` | 333 | 1 | 1/1 | deferred (§7) |
| `exists_flat_isInducedSection_family_eq_of_isInducedSection` | 325 | 2 | 4/15 | deferred (§7) |
| `archCasimirAtComplex_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAtComplex` | 321 | 6 | 1/1 | deferred (§7) |
| `isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_of_isFactorizableTestFn_of_support_subset` | 290 | 2 | 2/11 | deferred (§7) |
| `LocalIntertwining.integrable_smoothAtom_and_integrable_weylShift_adicCompletion` | 283 | 2 | 2/2 | deferred (§7) |
| `CuspidalSpectrum.isArchTestFactor_conj_inv_mul_ideleNorm_det_rpow` | 282 | 1 | 1/1 | deferred (§7) |
| `constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral` | 257 | 1 | 3/20 | deferred (§7) |
| `isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule` | 242 | 1 | 2/27 | deferred (§7) |
| `SmoothCusp.not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup` | 229 | 1 | 1/1 | deferred (§7) |
| `apply_weylInv_unipotent_mul_localWeyl_eq_modulus_cpow_mul_apply` | 217 | 2 | 1/1 | deferred (§7) |
| `CuspidalConstituent.inf_iSup_archTypeSubmoduleAt_le_iSup_inf_of_continuous` | 214 | 3 | 2/4 | deferred (§7) |
| `apply_mul_eq_of_isKfSmooth_of_forall_placeEmbed_of_mem_maximalCompactAway` | 209 | 1 | 1/3 | deferred (§7) |
| `peterssonIntegral_self_ne_zero_of_isFundamentalDomain_of_continuous` | 192 | 2 | 5/8 | deferred (§7) |
| `lintegral_rationalCentreUnipotentHaar_comp_heckeGen_mul_centralScalar_conj` | 179 | 1 | 1/1 | deferred (§7) |
| `cosetSum_rightConv_of_isLevelSphericalOfType` | 173 | 1 | 2/2 | deferred (§7) |
| `exists_isFundamentalDomain_globalPoints_range` | 165 | 3 | 1/11 | deferred (§7) |
| `heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps` | 138 | 1 | 2/5 | deferred (§7) |
| `whittakerCoefficient_finset_sum_mul_unipotentGL2_diagOne_mul` | 84 | 1 | 2/3 | **SET-AF12** (order B, rider) |
| `isKfSmooth_rightConv` | 70 | 1 | 7/21 | deferred (§7) |
| `CuspidalSpectrum.isFinTestFactor_conj_inv_mul_ideleNorm_det_rpow` | 59 | 1 | 1/1 | deferred (§7) |
| `CuspidalConstituent.exists_inf_archCutSubmodule_ofChar_ne_bot_of_ne_bot` | 56 | 1 | 1/1 | deferred (§7) |
| `isFinTestFactor_integral_mul_of_isFinTestFactor_of_hasCompactSupport` | 48 | 1 | 1/1 | deferred (§7) |
| `CuspidalSpectrum.exists_hasModulus_of_isCuspConstituent` | 37 | 1 | 3/8 | deferred (§7) |
| `CuspidalConstituent.rightConv_rightTranslate_eq_rightTranslate_rightConv_conj` | 35 | 1 | 2/3 | deferred (§7) |
| `SiegelCovering.centreCutSiegelSet_coversModCentre_rat` | 30 | 1 | 1/6 | deferred (§7) |

### The leaves block — **65 leaves / 13798 silo**

| leaf | silo | lev | disposition |
|---|---:|---:|---|
| `su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional` | 755 | 3/4 | deferred (§7) |
| `gl2Complex_whittaker_system_of_casimir_pair_of_unipotent_covariant_of_circleWeight_of_ktype` | 695 | 2/2 | **SET-AF12** (order A) |
| `CuspidalConstituent.exists_forall_le_archTypeSubmoduleAt_of_isSimple_of_le_iSup` | 646 | 2/4 | deferred (§7) |
| `exists_upperTriangular_globalPoints_mul_mul_scalar_mul_finIdeleDiag_inv_mem_finiteIntegralGL2` | 587 | 1/1 | deferred (§7) |
| `exists_sum_prod_mul_of_rightTranslatesSpanFinite` | 576 | 2/2 | deferred (§7) |
| `exists_coversModCentre_centreCutSiegelSetAmple` | 520 | 1/3 | deferred (§7) |
| `exists_depth_forall_apply_mul_lowerUnipotentGL2_eq_of_sum_translate` | 445 | 1/2 | deferred (§7) |
| `isFundamentalDomain_boxSheet_rationalTorusUnipotent` | 440 | 2/15 | deferred (§7) |
| `memLp_iUnion_centreCutSiegelSet_of_detWindow_le` | 432 | 2/7 | deferred (§7) |
| `WindowedSiegel.exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mul_centralScalar_mem` | 386 | 3/4 | deferred (§7) |
| `exists_norm_a_le_absNorm_rpow_and_norm_b_le_of_smoothCuspRealizationAt_of_peterssonPairing` | 384 | 1/2 | deferred (§7) |
| `exists_isArchBiFinite_rightConv_comp_inv` | 376 | 1/1 | deferred (§7) |
| `LocalIntertwining.integral_one_add_sq_cpow_neg_eq_GammaReal_div` | 362 | 1/1 | deferred (§7) |
| `gl2Real_whittaker_ode_of_casimir_of_unipotent_covariant_of_weight` | 347 | 1/1 | **SET-AF12** (order A) |
| `not_coversModCentre_iUnion_centreCutSiegelSet_of_eq_zero` | 346 | 1/2 | deferred (§7) |
| `isFundamentalDomain_boxSheet_rationalCentreUnipotent` | 340 | 2/3 | deferred (§7) |
| `IsKfSmooth.exists_ideal_forall_apply_mul_conj_unipotentGL2_eq` | 328 | 3/4 | deferred (§7) |
| `exists_forall_adelicGLHaar_image2_unipotentGL2_mul_mul_le_of_isCompact` | 317 | 1/1 | deferred (§7) |
| `CuspidalSpectrum.exists_isArchBiFinite_flat` | 304 | 1/1 | deferred (§7) |
| `WindowedSiegel.isCompact_centreCutSiegelSet_inter_heightCap` | 282 | 5/10 | deferred (§7) |
| `CuspidalConstituent.exists_isFactorizableTestFn_isArchBiFinite_conj` | 245 | 1/1 | deferred (§7) |
| `LocalIntertwining.integrable_complexAtom_and_integrable_moebiusShift` | 219 | 1/1 | deferred (§7) |
| `SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine` | 199 | 7/20 | deferred (§7) |
| `integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat` | 196 | 4/5 | deferred (§7) |
| `exists_eq_mul_mem_levelOne_inf_finiteAdelicGL2Subgroup_commute_placeEmbed_of_forall_mem_localIntegralSet` | 192 | 1/1 | deferred (§7) |
| `IsFactorizableTestFn.comp_mul_unipotentGL2_mul_mem_pureTensorSet` | 189 | 1/4 | deferred (§7) |
| `exists_coordMatrix_rightTranslate_rot_of_linearIndependent_of_span_stable` | 184 | 1/1 | deferred (§7) |
| `LocalIntertwining.integrable_realAtom_and_integrable_moebiusShift` | 179 | 1/1 | deferred (§7) |
| `isArchTestFactor_integral_mul_of_isArchTestFactor_of_hasCompactSupport` | 177 | 1/1 | deferred (§7) |
| `LocalIntertwining.tendsto_integral_normSq_rpow_sub_one_mul_complexAtom_nhdsGT_one_half` | 170 | 1/1 | deferred (§7) |
| `isArchTestFactor_of_contDiff_of_hasCompactSupport_of_tsupport_subset_isUnit_det` | 165 | 1/5 | deferred (§7) |
| `exists_borel_mul_gl2Weyl_mul_unipotentGL2_eq_of_integral` | 156 | 1/1 | deferred (§7) |
| `CuspidalConstituent.continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule` | 154 | 8/19 | deferred (§7) |
| `typeSubmodule_inf_typeSubmodule_eq_bot` | 152 | 1/2 | deferred (§7) |
| `coversModCentre_of_le_of_lt_of_coversModCentre` | 150 | 4/8 | deferred (§7) |
| `CuspidalConstituent.forall_apply_mul_archRealGLAt_eq_of_isCuspConstituent_of_exists` | 148 | 2/2 | deferred (§7) |
| `LocalIntertwining.tendsto_integral_sq_rpow_sub_one_mul_realAtom_nhdsGT_one_half` | 147 | 1/1 | deferred (§7) |
| `constantTerm_adelicBox_unipotentGL2_mul` | 144 | 1/14 | deferred (§7) |
| `coversModCentre_iUnion_centreCutSiegelSet_of_detWindow` | 136 | 1/3 | deferred (§7) |
| `mem_rationalCentreUnipotent_iff_heckeGen_mul_centralScalar_conj_mem` | 119 | 1/1 | deferred (§7) |
| `LocalIntertwining.exists_bound_norm_integral_mixedSpace_archAtom_prod` | 116 | 1/1 | deferred (§7) |
| `existsUnique_diagOne_inv_mul_mem_scalar_sup_unipotent_of_mem_borelSubgroup` | 108 | 2/3 | deferred (§7) |
| `LocalIntertwining.integral_one_add_norm_sq_cpow_neg_eq_pi_div` | 102 | 1/1 | deferred (§7) |
| `isFactorizableTestFn_sum_mul_comp_mul_mul` | 98 | 1/1 | deferred (§7) |
| `norm_rightConv_le_eLpNorm_mul_eLpNorm_restrict_image_mul` | 78 | 2/2 | deferred (§7) |
| `IsUnitFactorizableAbove.finComponent_glFin_mem_localIntegralSet_of_apply_ne_zero` | 78 | 1/1 | deferred (§7) |
| `CuspidalSpectrum.isClosedCuspSubrep_topologicalClosure_map_toCuspSubcarrier_of_isCuspSubrep` | 75 | 2/4 | deferred (§7) |
| `isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous` | 71 | 3/22 | deferred (§7) |
| `exists_isRightEquivariant_comp_subtype_eq_of_injective` | 70 | 3/8 | deferred (§7) |
| `exists_smoothCuspRealizationAt_productionPinsOf_toFun_eq_of_isBoundedOnSiegelWindows_of_coversModCentre` | 69 | 1/1 | deferred (§7) |
| `RankinSelberg.section_diagOne_mul_eq_ideleNorm_cpow_mul_of_isInducedSection_etaFst_etaSnd` | 66 | 1/1 | deferred (§7) |
| `existsUnique_bruhatRepresentative_mul_mem_borelSubgroup` | 65 | 2/3 | deferred (§7) |
| `isCompact_levelOne_inf_finiteAdelicGL2Subgroup` | 62 | 2/14 | deferred (§7) |
| `isLocallyConstant_iwasawaShellIndex_and_measurable` | 62 | 2/2 | deferred (§7) |
| `CuspidalConstituent.isCuspConstituent_productionPinsOf_mono` | 62 | 1/2 | deferred (§7) |
| `exists_continuous_monoidHom_matrix_apply_ne_one_of_ne_one` | 55 | 1/1 | deferred (§7) |
| `isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn` | 51 | 5/18 | deferred (§7) |
| `iwasawaShellIndex_mul_of_mem_rationalCentreUnipotent` | 46 | 2/2 | deferred (§7) |
| `IsKfSmooth.finite_smul_image_of_isCompact` | 40 | 3/4 | deferred (§7) |
| `CuspidalConstituent.eq_of_isCuspConstituent_of_exists_mem_ne_zero` | 33 | 1/2 | deferred (§7) |
| `IsIsotypicCuspFormAt.exists_smoothCuspRealizationAt_toFun_eq_of_ne_bot` | 30 | 2/10 | deferred (§7) |
| `exists_iUnion_centreCutSiegelSet_mem_nhds` | 25 | 1/1 | deferred (§7) |
| `eq_zero_of_isLsXiFunction_of_coversModCentre_of_forall_mem_eq_zero` | 23 | 1/1 | deferred (§7) |
| `constantTerm_add` | 13 | 1/2 | deferred (§7) |
| `constantTerm_smul` | 11 | 1/1 | deferred (§7) |

## Appendix B — the per-row worklist

Generated by `build/af-worklist.py` from the port's statement index: per row, every declaration whose
statement is not in the port, with its pin line and span.

| row | decl lines | imported | to write | decls |
|---|---:|---:|---:|---:|
| `whittakerCoefficient_finset_sum_mul_unipotentGL2_diagOne_mul` | 68 | 0 | 68 | 1 |
| `gl2Real_whittaker_ode_of_casimir_of_unipotent_covariant_of_weight` | 330 | 15 | 315 | 10 |
| `gl2Complex_whittaker_system_of_casimir_pair_of_unipotent_covariant_of_circleWeight_of_ktype` | 678 | 28 | 650 | 52 |
| **3 rows** | **1076** | **43** | **1033** | **63** |

### `whittakerCoefficient_finset_sum_mul_unipotentGL2_diagOne_mul`

68 declaration lines, 0 imported, **68 to write** in 1 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `solution` | 68 | 18 | theorem |

### `gl2Real_whittaker_ode_of_casimir_of_unipotent_covariant_of_weight`

330 declaration lines, 15 imported, **315 to write** in 10 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `solution` | 235 | 114 | theorem |
| `lowerUnipotentGL2_iwasawa` | 31 | 83 | theorem |
| `kIw_mem` | 14 | 62 | theorem |
| `splitTorusGL2_mul_unipotentGL2` | 8 | 26 | theorem |
| `det_kIw` | 7 | 55 | theorem |
| `archWeightCharℝ_kIw` | 7 | 76 | theorem |
| `splitTorusGL2_mul` | 5 | 21 | theorem |
| `inv_sqrt_mul_inv_sqrt` | 3 | 34 | theorem |
| `kIw_coe` | 3 | 49 | theorem |
| `sq_sqrt_one_add_sq` | 2 | 53 | theorem |

### `gl2Complex_whittaker_system_of_casimir_pair_of_unipotent_covariant_of_circleWeight_of_ktype`

678 declaration lines, 28 imported, **650 to write** in 52 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `solution` | 162 | 535 | theorem |
| `deriv_iwasawa_sum` | 40 | 362 | theorem |
| `sum_M2` | 31 | 504 | theorem |
| `deriviFm_torus` | 26 | 424 | theorem |
| `derivFm_torus` | 22 | 402 | theorem |
| `sum_M1` | 22 | 482 | theorem |
| `lowerUnipotent_imag_iwasawa` | 21 | 104 | theorem |
| `lowerUnipotent_real_iwasawa` | 18 | 86 | theorem |
| `sum_ite_val_eq` | 18 | 452 | theorem |
| `hasDerivAt_psiK_real` | 17 | 175 | theorem |
| `hasDerivAt_psiK_imag` | 17 | 192 | theorem |
| `weight_deriviH` | 17 | 280 | theorem |
| `hasDerivAt_psiK_negI` | 17 | 325 | theorem |
| `covariant_deriv` | 13 | 156 | theorem |
| `weight_derivH` | 13 | 267 | theorem |
| `mul_sum_ite_pred` | 12 | 470 | theorem |
| `hasDerivAt_torus` | 11 | 143 | theorem |
| `derivE_torus` | 10 | 209 | theorem |
| `deriviE_torus` | 10 | 219 | theorem |
| `hasDerivAt_zeta_zpow` | 10 | 242 | theorem |
| `hasDerivAt_psiK_xIw` | 10 | 315 | theorem |
| `hasDerivAt_psiK_negI_xIw` | 10 | 342 | theorem |
| `psiK_zero` | 10 | 352 | theorem |
| `deriviH_of_weight` | 9 | 252 | theorem |
| `splitTorus_mul_unipotent` | 8 | 22 | theorem |
| `cexp_neg_log_half` | 7 | 66 | theorem |
| `cexp_neg_neg_log_half` | 7 | 73 | theorem |
| `aT_mul_unipotent` | 6 | 169 | theorem |
| `flowiH_eq_circle` | 6 | 236 | theorem |
| `circle_mul_splitTorus` | 6 | 261 | theorem |
| `aT_mul_aIw` | 6 | 297 | theorem |
| `hasDerivAt_xIw` | 6 | 303 | theorem |
| `hasDerivAt_uIw` | 6 | 309 | theorem |
| `hasDerivAt_log_half` | 5 | 138 | theorem |
| `splitTorus_mul_splitTorus` | 4 | 30 | theorem |
| `rotR_coe` | 4 | 56 | theorem |
| `rotS_coe` | 4 | 60 | theorem |
| `aT_mul_flowH` | 4 | 134 | theorem |
| `splitTorusGL2Complex_coe'` | 3 | 19 | theorem |
| `cos_arctan'` | 3 | 80 | theorem |
| `sin_arctan'` | 3 | 83 | theorem |
| `flowiFm` | 2 | 132 | theorem |
| `psiK` | 2 | 154 | def |
| `zeta_inv_coe` | 2 | 232 | theorem |
| `norm_zeta` | 2 | 234 | theorem |
| `extN` | 2 | 450 | def |
| `flowH` | 1 | 127 | theorem |
| `flowiH` | 1 | 128 | theorem |
| `flowE` | 1 | 129 | theorem |
| `flowiE` | 1 | 130 | theorem |
| `flowFm` | 1 | 131 | theorem |
| `zeta_coe` | 1 | 231 | theorem |

## Appendix C — reproduce

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf-af11-landed.json
python3 frontier.py --selfcheck
python3 port_advise.py --nodes AutomorphicForm.gl2Real_whittaker_ode_of_casimir_of_unipotent_covariant_of_weight \
  --nodes AutomorphicForm.gl2Complex_whittaker_system_of_casimir_pair_of_unipotent_covariant_of_circleWeight_of_ktype \
  --json build/af12-advise.json
python3 port_plan.py --json build/af12-advise.json     # 1,042 raw / 1,006 decl / 1,003 net
python3 build/af-worklist.py whittakerCoefficient_finset_sum_mul_unipotentGL2_diagOne_mul \
  gl2Real_whittaker_ode_of_casimir_of_unipotent_covariant_of_weight \
  gl2Complex_whittaker_system_of_casimir_pair_of_unipotent_covariant_of_circleWeight_of_ktype
cd ../lean
python3 spec/gate_scan.py --pin Definitions/Def_AutomorphicForm_ArchDerivCasimir.lean \
  --rows Theorems/Thm_AutomorphicForm_gl2Real_whittaker_ode_of_casimir_of_unipotent_covariant_of_weight.lean
python3 spec/gate_scan.py --pin Definitions/Def_AutomorphicForm_ArchWeightChar.lean \
  --rows Theorems/Thm_AutomorphicForm_gl2Real_whittaker_ode_of_casimir_of_unipotent_covariant_of_weight.lean
python3 spec/gate_scan.py --pin Definitions/Def_AutomorphicForm_ArchDerivCasimirComplex.lean \
  --rows Theorems/Thm_AutomorphicForm_gl2Complex_whittaker_system_of_casimir_pair_of_unipotent_covariant_of_circleWeight_of_ktype.lean
```

**Forecast on landing** (read at §0.1): `needed` **868 / 353,051 → 865 / 351,925** (−3 / −1,126, the
three rows' silo), frontier **1,547 / 774,315 → 1,550 / 775,441**. The ready shelf should **not
rise**: §0.2's table lists the other unported premises of all three consumers, so the honest
expectation is **zero new ready rows**, and the re-read's question is whether one of the three
changed *hop count* rather than readiness. That is the mirror image of AF10's "narrow return" and it
should be recorded as such — a set whose return is a premise removed from three rows, not a row
readied.

**Measured at landing (§5.1):** exact on every figure. `needed` 868 / 353,051 → **865 / 351,925**,
frontier **1,550 / 775,441**, ready 67 / 17,980 → **66 / 17,896** (the rider leaves), leaves
234 / 59,837 → **232 / 58,795** (the two ODE rows), withheld and avoided unchanged, `--selfcheck`
PASS (1,369 / 1,550) — and **no row readied**, as forecast: the three consumers each still need
another unported premise, and the 306 row's is
`NumberField.StandardAddChar.stdAddChar_single_infinitePlace_of_isReal`, which the consumer zone hit
directly.
