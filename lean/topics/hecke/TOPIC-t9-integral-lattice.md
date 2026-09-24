# Topic 9: the integral lattice and the lattice action

**Status: planned (not started).** Second topic of [SET-4](SET-4.md). It ports the
pin's integral-lattice vocabulary and the fact that the Hecke algebra preserves
it — the prerequisite for T10's `Module.Finite`/`Free` and for the survey's
integrality route.

**Audience.** A fresh session taking the second SET-4 topic. Read
[SET-4.md](SET-4.md) §0–§3; the pin's
`Definitions/Def_CuspForm_IntegralStructure.lean` (8 lines) and the three lattice
`S_` files; and [porting-playbook.md](../../porting-playbook.md) §3, §7.

**Goal.** One definition module and four targets:

- `FLTForHuman/ModularForms/Defs/IntegralStructure.lean`:
  ```lean
  def CuspForm.intLattice (N : ℕ) (k : ℤ) : Submodule ℤ (CuspForm (CongruenceSubgroup.Gamma0 N) k) :=
    Submodule.span ℤ {f | ∀ n : ℕ, ∃ m : ℤ, ModularFormClass.qCoeff f n = (m : ℂ)}
  def CuspForm.HasIntegralStructure (N : ℕ) (k : ℤ) : Prop :=
    Submodule.span ℂ ((CuspForm.intLattice N k : Submodule ℤ _) : Set _) = ⊤
  ```
- `FLTForHuman/ModularForms/HeckeLattice.lean` — the lattice action:
  - `CuspForm.mem_intLattice_of_mem_heckeAlgebra`,
  - `CuspForm.mem_intLattice_of_coe_eq_heckeT`,
  - `CuspForm.mem_intLattice_of_coe_eq_heckeU`.

The three statements, verbatim from their wrappers (the last two are stated for a
pair `f g` with `⇑g = heckeT k p ⇑f`):

```lean
theorem CuspForm.mem_intLattice_of_mem_heckeAlgebra {N : ℕ} [NeZero N] {k : ℤ} (hk : 1 ≤ k)
    {S : Set ℕ} {t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k)}
    (ht : t ∈ CuspForm.heckeAlgebra N k S) {f : CuspForm (CongruenceSubgroup.Gamma0 N) k}
    (hf : f ∈ CuspForm.intLattice N k) : t f ∈ CuspForm.intLattice N k
theorem CuspForm.mem_intLattice_of_coe_eq_heckeT {N : ℕ} {k : ℤ} (hk : 1 ≤ k) {p : ℕ} (hp : p ≠ 0)
    {f g : CuspForm (CongruenceSubgroup.Gamma0 N) k} (hg : ⇑g = ModularForm.heckeT k p ⇑f)
    (hf : f ∈ CuspForm.intLattice N k) : g ∈ CuspForm.intLattice N k
-- …_heckeU is the same with heckeU and no `hk`
```

## 1. Why this topic, and what is settled

- **The vocabulary is two definitions.** `intLattice N k` is the `ℤ`-span of the
  forms with integral `q`-coefficients; `HasIntegralStructure N k` says that span
  is all of the `ℂ`-space (the lattice is full-rank). Port them verbatim; T10
  supplies the existence (`hasIntegralStructure_of_two_le`) and the finiteness.
- **The two `_coe_eq_` targets are T5's integrality, lifted.** `coeffHeckeT_int`
  / `coeffHeckeU_int` (T5) say the transformed coefficient sequence stays
  integral; the pin then shows the transformed form lies in the `ℤ`-span. The
  route is a `Submodule.span` induction / `Submodule.mem_span` unpack, not new
  arithmetic.
- **The algebra target is the generation induction.** `mem_int_heckeAlgebra`
  unfolds `heckeAlgebra = Algebra.adjoin ℤ heckeGenerators` and inducts on the
  `Subalgebra` closure, dispatching each generator to the `T`/`U` case. T7's
  `heckeGenerators`, `commute_of_mem_heckeGenerators` and the two
  `*_mem_heckeGenerators` lemmas are the API.
- **The weight-2 auxiliary vocabulary is T10's, not T9's.** `qIntegralSet`,
  `qIntegralLattice`, `HasIntegralBasis`, `bridgeProduct`, `IsLatticeRealized`
  (from `Def_CuspForm_IntegralLattice.lean`) exist only for the existence proof
  of `HasIntegralStructure`; T9 does not need them. Do not open them here.

**Settled: module placement.** The two definitions go in `Defs/IntegralStructure.lean`
(the pin's name); the lattice-action targets are results and go in
`ModularForms/HeckeLattice.lean`. `HasIntegralStructure`'s *existence* is T10.

## 2. The scouted inventory

| target | pin file (lines) | note |
|---|---|---|
| `CuspForm.intLattice`, `CuspForm.HasIntegralStructure` | `Def_CuspForm_IntegralStructure` (8) | definitions, verbatim |
| `CuspForm.mem_intLattice_of_mem_heckeAlgebra` | 31 | the algebra induction |
| `CuspForm.mem_intLattice_of_coe_eq_heckeT` | 74 | uses T5 `coeffHeckeT_int` |
| `CuspForm.mem_intLattice_of_coe_eq_heckeU` | 74 | uses T5 `coeffHeckeU_int` |

Route notes:

- `intLattice` is a `Submodule.span ℤ`; proving `g ∈ intLattice` from an integral
  coefficient sequence is `Submodule.subset_span` on the defining set, and linear
  combinations use `Submodule.add_mem`/`smul_mem`. The `_coe_eq_` proofs unpack
  `f ∈ span` and push the Hecke operator through the (T6) linear map.
- `mem_intlattice_of_mem_heckeAlgebra` needs `hk : 1 ≤ k` (the `p^{k-1}`
  exponent must be a natural power for integrality) but **not** `[NeZero N]`'s
  `p` hypotheses; keep the wrapper's binders.
- The pin's `mem_intLattice_of_coe_eq_heckeT` imports the `heckeU` version and
  vice versa (`S_CuspForm_mem_intLattice_of_mem_heckeAlgebra.lean` imports both);
  port them in either order but declare both before the algebra target.
- Do not confuse `intLattice` (all `k`) with the weight-2 `qIntegralLattice`
  (T10); they are different objects with different names.

## 3. What is different about this topic

- **It is vocabulary + two lifts.** The only proof content is the `ℤ`-span
  bookkeeping; if a target needs new coefficient arithmetic, the integrality
  belongs in T5, not here.
- **It is the prerequisite for T10**, which cannot state `Module.Finite` over the
  lattice without `intLattice`/`HasIntegralStructure`.
- **The existence of `HasIntegralStructure` is deliberately absent**, so a T9
  consumer that assumes it must take it as a hypothesis (`hN : HasIntegralStructure N k`)
  — which is exactly how the pin's `HasIntegralStructure.moduleFinite_heckeAlgebra`
  is stated.

## 4. Budget

**1–2 goal rounds.** The definitions are 8 lines; the two `_coe_eq_` targets are
span inductions; the algebra target is a closure induction.

**Stop early on**: a target needing `qIntegralLattice`/`HasIntegralBasis` (that is
T10 — report it); a statement mismatch; or the `Submodule.span` induction needing
a `Module.Finite` fact (it should not).

## 5. Definition of done

**Reviewed and ticked (2026-09-23), independently re-verified by the reviewer.**
Checker **802 identical, 0 mismatched, 0 missing**; full `lake build` exit 0
(4054 jobs), 0 warnings, no `sorry`; `#print axioms` clean on the three targets.
`grep -c qIntegralLattice` = 0 in both modules, as required. The route in §2 was
superseded by a cleaner one (below) and the statements still match their wrappers.

- [x] `FLTForHuman/ModularForms/Defs/IntegralStructure.lean` created, verbatim.
- [x] `FLTForHuman/ModularForms/HeckeLattice.lean` created; the three targets
      verbatim from their wrappers.
- [x] the weight-2 auxiliary vocabulary is **absent** (`grep -c qIntegralLattice` = 0).
- [x] `timeout 180 lake build` green, 0 warnings, no `sorry`.
- [x] checker: the three wrappers appended to `SOURCES`, both modules to
      `PORT_FILES`, **0 mismatched, 0 missing**.
- [x] `#print axioms` on the three clean.
- [x] `logs/hecke-port.md` §T9: the span-induction shape, the T10 hand-off.
- [x] `README.md` rows.

**Reviewer's route note (replace §2's `Submodule.span` sketch).** The runner
proved the defining set is a `ℤ`-submodule (`intSubmodule`, via
`qCoeff_add`/`qCoeff_zero'`/`qCoeff_zsmul`), so `Submodule.span_eq` gives
`intLattice = intSubmodule` and a usable membership lemma `mem_intLattice_iff`
(`f ∈ intLattice ↔ ∀ n, ∃ m : ℤ, qCoeff f n = ↑m`). The two `_coe_eq_` targets
then transport T5's `coeffHecke{T,U}_int`, and the algebra target is an
`Algebra.adjoin_induction` over `heckeGenerators`. This is the shape a
re-derivation should use.

## 6. Reporting back

1. The span-induction shape actually used for the two `_coe_eq_` targets.
2. Whether the `Subalgebra` closure induction needed any T7 lemma the wrapper does
   not export.
3. The T10 hand-off: the exact lattice API and the `HasIntegralStructure`
   hypothesis shape T10 will consume.
