# Topic 12, SET 2: the eigenform-extraction chain

**Status: planned (not started).** Second set of T12, the driver port of
[../../studies/t-side-driver.md](../../studies/t-side-driver.md). SET 1 (the
surjection half) is complete —
[TOPIC-t12-set1-surjection.md](TOPIC-t12-set1-surjection.md), record
[../../logs/t-side-port.md](../../logs/t-side-port.md) §§6–11. This set ports the
nine nodes that turn a Hecke character into a **normalised eigenform**: the three
generic character/eigenvector lemmas, the degeneracy map, and the six
`CuspForm.*` extraction statements. SET 3 (the conditional capstone) consumes
them.

**Mathematics.** [../../math/018-t-side-definitions.md](../../math/018-t-side-definitions.md)
§3.2–§4. **Driver plan.** [../../studies/t-side-driver.md](../../studies/t-side-driver.md)
§2–§4.

**Audience.** A fresh session taking SET 2. Read
[porting-playbook.md](../../porting-playbook.md) (all of it; §2 dedup, §3.11,
§5, §7.1/§9), then the nine pin files of §0 and their `Theorems/` wrappers.

**Build discipline — read this first.** Every build is bounded and a blow-up is
quarantined, not waited on. Measured with mathlib prebuilt: a green
`lake env lean <module>` of this size is **~4 s**, `lake build <module>` with
deps cached **~2–5 s**, and a `whnf`/heartbeat timeout at the default cap
**errors in ~15–20 s** — it does not hang. A healthy full `lake build` of this
tree is **seconds to about a minute**.

- Run every build under a hard bound: `timeout 60 lake env lean <file>`,
  `timeout 90 lake build <module>`, `timeout 180 lake build`. **A multi-minute
  build is never acceptable, not even while experimenting.**
- **Expect ≤ 30 s.** Any single build past ~60 s is a blow-up: bisect it, do not
  watch it.
- **Quarantine immediately.** On a non-return, comment the declaration out and
  bisect, or reproduce in the gitignored `Scratch.lean` with
  `set_option diagnostics true` and `set_option maxHeartbeats 20000`.
- **Never raise `maxHeartbeats` (or `maxRecDepth`).**
- **Tell a blow-up from contention by CPU time** (`time` / `/usr/bin/time -v`):
  high user CPU + timeout is real; ~0 CPU is another agent's build — re-run idle,
  and never build concurrently.

## 0. The cone

Nine nodes / ~917 pin `S_` lines, all unported. Statements verbatim from the
`Theorems/` wrappers.

```lean
theorem RingHom.exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed {A B K : Type*}
    [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B] [Field K] [IsAlgClosed K]
    (χ : A →+* K) (hker : RingHom.ker (algebraMap A B) ≤ RingHom.ker χ) :
    ∃ ψ : B →+* K, ψ.comp (algebraMap A B) = χ

theorem Ideal.exists_ringHom_integralClosure_ker_eq {T : Type*} [CommRing T]
    [Module.Finite ℤ T] (𝔓 : Ideal T) (h𝔓 : 𝔓.IsPrime)
    (hint : ∀ n : ℤ, (n : T) ∈ 𝔓 → n = 0) :
    ∃ f : T →+* integralClosure ℤ ℂ, RingHom.ker f = 𝔓

theorem Module.End.exists_ne_zero_forall_apply_eq_smul_of_ringHom {K V T : Type*}
    [Field K] [CharZero K] [AddCommGroup V] [Module K V] [CommRing T]
    (ρ : T →+* Module.End K V) (L : Submodule ℤ V) (hL : L.FG)
    (hstab : ∀ (t : T), ∀ x ∈ L, ρ t x ∈ L)
    (hfaith : ∀ t : T, (∀ x ∈ L, ρ t x = 0) → t = 0)
    (hfree : ∀ (n : ℕ) (y : Fin n → V), (∀ i, y i ∈ L) → LinearIndependent ℤ y →
      LinearIndependent K y) (χ : T →+* K) :
    ∃ v : V, v ≠ 0 ∧ ∀ t : T, ρ t v = χ t • v

theorem CuspForm.exists_degeneracy_Gamma0 {k : ℤ} {M N d : ℕ} [NeZero N]
    (hd : d * M ∣ N) (f : CuspForm (CongruenceSubgroup.Gamma0 M) k) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma0 N) k,
      ⇑g = fun τ ↦ f (ModularForm.heckeDiagMatrix d • τ)

theorem CuspForm.exists_isNormalizedEigenform_level_mul {M : ℕ} [NeZero M]
    (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (hf : f.IsNormalizedEigenform)
    {p : ℕ} (hp : p.Prime) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma0 (M * p)) 2, g.IsNormalizedEigenform ∧
      ∀ n : ℕ, ¬ p ∣ n → ModularFormClass.qCoeff g n = ModularFormClass.qCoeff f n

theorem CuspForm.exists_isNormalizedEigenform_of_dvd {M N : ℕ} [NeZero N] (hMN : M ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (hf : f.IsNormalizedEigenform) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma0 N) 2, g.IsNormalizedEigenform ∧
      ∀ n : ℕ, n.Coprime N → ModularFormClass.qCoeff g n = ModularFormClass.qCoeff f n

theorem CuspForm.linearIndependent_of_mem_intLattice {N : ℕ} [NeZero N] {k : ℤ} (n : ℕ)
    (f : Fin n → CuspForm (CongruenceSubgroup.Gamma0 N) k)
    (hf : ∀ i, f i ∈ CuspForm.intLattice N k) (h : LinearIndependent ℤ f) :
    LinearIndependent ℂ f

theorem CuspForm.HasIntegralStructure.exists_ne_zero_forall_apply_eq_smul {N : ℕ} [NeZero N]
    {k : ℤ} (hN : CuspForm.HasIntegralStructure N k) (hk : 1 ≤ k) {S : Set ℕ}
    (χ : CuspForm.heckeAlgebra N k S →+* ℂ) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) k, f ≠ 0 ∧
      ∀ t : CuspForm.heckeAlgebra N k S,
        (t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k)) f = χ t • f

theorem CuspForm.HasIntegralStructure.exists_isNormalizedEigenform_qCoeff_eq {N : ℕ} [NeZero N]
    (hN : CuspForm.HasIntegralStructure N 2) {S : Set ℕ}
    (χ : CuspForm.heckeAlgebra N 2 S →+* ℂ) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) 2, f.IsNormalizedEigenform ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
        ModularFormClass.qCoeff f ℓ = χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) ∧
      ∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (hqS : q ∉ S),
        ModularFormClass.qCoeff f q = χ (CuspForm.heckeAlgebra.U hq hqN hqS)
```

## 1. Layout — natural subject homes

Generic material goes to `FLTForHuman/Algebra/`; the modular-forms material to
`FLTForHuman/ModularForms/`; nothing T-side is created here.

| pin source | port module | why |
|---|---|---|
| `S_RingHom_exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed` (30 L) | `FLTForHuman/Algebra/IntegralExtensionCharacters.lean` | generic algebra: extending a character along an integral extension |
| `S_Ideal_exists_ringHom_integralClosure_ker_eq` (76 L) | same module | generic: primes of finite `ℤ`-algebras are kernels of `ℤ̄`-valued characters |
| `S_Module_End_exists_ne_zero_forall_apply_eq_smul_of_ringHom` (246 L) | `FLTForHuman/Algebra/FaithfulLatticeEigenvector.lean` | generic: a faithful lattice representation has an eigenvector for every character |
| `S_CuspForm_exists_degeneracy_Gamma0` (115 L) | `FLTForHuman/ModularForms/Level/Degeneracy.lean` | the level map `f(τ) ↦ f(dτ)`; `Level/` already holds `Diamond.lean` |
| `S_CuspForm_exists_isNormalizedEigenform_level_mul` (147 L) | `FLTForHuman/ModularForms/EigenformLevel.lean` | p-stabilisation of an eigenform |
| `S_CuspForm_exists_isNormalizedEigenform_of_dvd` (39 L) | same module | induction over the level divisibility, using the `_level_mul` step |
| `S_CuspForm_linearIndependent_of_mem_intLattice` (95 L) | `FLTForHuman/ModularForms/EigenformExtraction.lean` | the lattice's `ℤ`-independence implies `ℂ`-independence |
| `S_CuspForm_HasIntegralStructure_exists_ne_zero_forall_apply_eq_smul` (25 L) | same module | the eigenvector from the faithful lattice |
| `S_CuspForm_HasIntegralStructure_exists_isNormalizedEigenform_qCoeff_eq` (144 L) | same module | the eigenvalue system becomes a normalised eigenform |

Reuse the ported `CuspForm.heckeAlgebra`/`heckeTLin`/`heckeULin`,
`CuspForm.intLattice`/`HasIntegralStructure`/`mem_intLattice_*`/`intLattice_fg`,
`IsNormalizedEigenform` and the `HeckeQCoeff`/`HeckeEigenform` dictionaries.
Import T11 only where needed (`FLTForHuman.GaloisRep.Defs.Adic` is not needed
here).

## 2. Redundancy to reduce — read this before writing any `trunc`

**The port already has the truncation machinery twice, and the pin re-derives it
a third time.**

- `ModularForms/HeckeLattice.lean` has **private** `sturmB` (line 153),
  `trunc` (156, `ℤ`-linear into `Fin (sturmB N k + 1) → ℂ`) and `trunc_injective`
  (167) — the exact Sturm-truncation argument.
- `ModularForms/SturmBound.lean` has `qCoeffTrunc` (line 401, `ℂ`-linear into
  `Fin d → ℂ`) and `Gamma0_eq_zero_of_qExpansion_coeff_eq_zero`.
- The pin's `S_CuspForm_linearIndependent_of_mem_intLattice` introduces a third
  copy in its `FrobChareqC2` namespace: `sturmB`, `trunc` (ℂ-linear) and
  `trunc_injective`.

**Do not write a third copy.** Either promote `HeckeLattice.sturmB`/`trunc`/
`trunc_injective` to a shared public home (or add the `ℂ`-linear variant there),
or derive the pin's `trunc`/`trunc_injective` directly from the ported
`SturmBound.qCoeffTrunc` + `Gamma0_eq_zero_of_qExpansion_coeff_eq_zero`. The
target is that `linearIndependent_of_mem_intLattice` becomes a short argument
over an **existing** truncation, with no new `sturmB`/`trunc`. Measure the saving
and record it.

Other redundancy to check before porting, with `#check` against the port
(playbook §2, §5.6):

- The `FrobChareqC2` q-coefficient helpers in
  `S_CuspForm_HasIntegralStructure_exists_isNormalizedEigenform_qCoeff_eq`
  (`qCoeff_zero'`, `qCoeff_smul`, `qCoeff_heckeTLin_one`, `qCoeff_heckeULin_one`)
  look like the ported `HeckeQCoeff`/`UpperHalfPlane` coefficient lemmas
  (`qCoeff_zero`, `qCoeff_heckeT`, `qCoeff_heckeU`, `qCoeff_zsmul`). Reuse or
  keep `private`; do not re-prove what exists.
- `S_CuspForm_exists_degeneracy_Gamma0`'s `DegeneracyPort` block
  (`restrictMF`, `restrictCF`, `Gamma0_le_conj_Gamma0`, `exists_modularForm`,
  `exists_cuspForm`) is private; check `restrictMF`/`restrictCF` against any
  ported level-restriction API and inline if trivial.
- The pin's `p2m_open` / `p2m_exact_reverting` boilerplate is **dropped** (state
  and prove directly), and unused `import Mathlib` lines are replaced by the
  specific mathlib modules actually used (SET 1's friction item 1).

## 3. Port order (build after every module, playbook §5.5)

1. `Algebra/IntegralExtensionCharacters.lean` — the `RingHom` and `Ideal`
   statements. The `Ideal` one uses `IsAlgClosed.lift` and the
   HopkinsLevitzki/associated-prime imports; `#check` the mathlib names first.
2. `Algebra/FaithfulLatticeEigenvector.lean` — the 246-line `Module.End`
   statement, with its private `FrobChareqEngine.engine3/4/5a` block. This is the
   heaviest file; bisect if a build blows up.
3. `ModularForms/Level/Degeneracy.lean` — `exists_degeneracy_Gamma0`.
4. `ModularForms/EigenformLevel.lean` — `exists_isNormalizedEigenform_level_mul`
   (private `PStab` arithmetic block) then `…_of_dvd`.
5. `ModularForms/EigenformExtraction.lean` — `linearIndependent_of_mem_intLattice`
   (reusing §2's truncation), then
   `HasIntegralStructure.exists_ne_zero_forall_apply_eq_smul` (apply step 2), then
   `HasIntegralStructure.exists_isNormalizedEigenform_qCoeff_eq` (apply the
   previous node and step 1's `RingHom.exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed`).

## 4. Wiring

- Append to `SOURCES` the nine `Theorems/Thm_*` wrappers of §0; append the five
  new port modules to `PORT_FILES`.
- Any public promotion created by §2's truncation dedup (e.g. a public
  `CuspForm.sturmB`/`trunc`/`trunc_injective` if promoted from `HeckeLattice`)
  goes in `OWN_PROOFS` with the reason, or is verified by adding its pin carrier
  to `SOURCES` if one exists. Keep the public surface to the nine §0 statements
  plus any genuinely reused promotion.
- Add a SET-2 zone to `spec/TsideSet1Consumer.lean` or a new
  `spec/TsideSet2Consumer.lean` with a **real cross-module composition**: build a
  Hecke character, apply
  `HasIntegralStructure.exists_isNormalizedEigenform_qCoeff_eq` (EigenformExtraction)
  and feed the result to `IsNormalizedEigenform.heckeTLin_apply_eq_qCoeff_smul`
  (the ported HeckeEigenform dictionary). The composition must import from two
  different new modules.

## 5. Verification gates

1. `cd lean && timeout 180 lake build` — green, no `sorry`/`admit`.
2. `python3 spec/check_flt_statements.py` — the nine new statements identical,
   **0 mismatched, 0 missing**; mutate one token of one new statement and confirm
   `1 mismatched`, then revert.
3. `#print axioms` on `exists_isNormalizedEigenform_qCoeff_eq`,
   `Module.End.exists_ne_zero_forall_apply_eq_smul_of_ringHom` and
   `exists_degeneracy_Gamma0` — only `propext, Classical.choice, Quot.sound`.
4. The consumer zone builds with 0 errors.
5. Record a SET-2 section in `logs/t-side-port.md` and update `README.md`'s
   module table.

## 6. Risks

- **`Module.End.exists_ne_zero_forall_apply_eq_smul_of_ringHom` (246 L)** is the
  one heavy file: associated primes, minimal primes, Hopkins–Levitzki, tensor
  products. Expect mathlib API drift; probe with `#check @name` in `Scratch.lean`.
- **`Ideal.exists_ringHom_integralClosure_ker_eq`** uses `IsAlgClosed.lift`; its
  `hint` hypothesis is what makes `ℤ → D` injective, and the proof is
  `IsAlgClosed.lift` + `codRestrict`. Verify the `IsAlgClosed.lift` signature
  first.
- **Truncation dedup (§2) is a design decision, not a deletion** (playbook §2):
  promoting `HeckeLattice`'s private block touches a ported module. Prefer adding
  the `ℂ`-linear variant beside it or deriving from `SturmBound.qCoeffTrunc`,
  and keep the change additive; do not renumber or rename existing public
  declarations.
- **Do not raise `maxHeartbeats`; do not build concurrently with another agent.**
- **Do not touch** T11, the Hecke port modules (except the additive §2
  promotion), WeightOne, the FFG modules, or `studies/`.

## 7. Pointers

- [../../studies/t-side-driver.md](../../studies/t-side-driver.md) §2–§4 — the
  estimate (this set is the 9-node / ~917-line remainder of the conditional
  capstone, after SET 1) and the SET decomposition.
- [../../math/018-t-side-definitions.md](../../math/018-t-side-definitions.md)
  §3.2 (the lattice), §3.3 (`T_θ`), §4 (the T package).
- [TOPIC-t12-set1-surjection.md](TOPIC-t12-set1-surjection.md) — the previous
  set, and the format this file follows. This set is independent of it except for
  the ported Hecke vocabulary; its own first module
  (`RingHom.exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed`) is what its
  last node consumes.
- [../../logs/t-side-port.md](../../logs/t-side-port.md) §§10–11 — SET 1's
  friction log and hand-off.
