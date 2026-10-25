/-
 The prime-power step of the divisor-generated function field, over an arbitrary
 field `K`.

 Two headlines, the `C`-layer twins of `DegreeStep.lean` and of the socket's
 assembly layer:

 * `relfinrank_fullC_mul_prime_pow` — for `p ∤ M`,
   `[F^fullC_{M p ^ (a+1)} : F^fullC_{M p ^ a}] = p + 1` when `a = 0` and `p`
   otherwise, where `F^fullC_L` is the intermediate field of `LaurentSeries K`
   generated over `K` by the `jqNModC K d` with `d ∣ L`. The proof is the strong
   induction step: `F^fullC_{M p ^ (a+1)}` is generated over `F^fullC_{M p ^ a}`
   by the single element `jqNModC K (p ^ (a+1))` (the two-prime descent), whose
   minimal polynomial has degree `p + 1` at `a = 0` and `p` afterwards — the two
   bounds come respectively from an irreducibility count (`Φ_p` at the slot,
   transported through the `qTwist`-conjugates) and from `Φ_p`'s degree minus the
   one root it already has in the base field.
 * `package_of_socket` — the same degree, at *every* divisor `d` of a level `M`,
   as the `hall` package `Pkg`: `[K⟮j(q)⟯⟮j(q ^ d)⟯ : K⟮j(q)⟯] = ψ(d)` together
   with `modularFunctionFieldC K d = K⟮j(q ^ d') ∣ d' ∣ d⟯`. This is the induction
   over the divisors, consuming the prime step `hKG1` and the `(p + 1) · p ^ a`
   tower above (§7).

 ## Source

 FLT `anthropics/fermats-last-theorem@aa2d8b3`:
 `P2M/Sol/S_ModularCurve_relfinrank_fullC_mul_prime_pow.lean` (1,175 lines; the
 node is 354–1175) and its statement authority
 `Theorems/Thm_ModularCurve_relfinrank_fullC_mul_prime_pow.lean`. Statements are
 the pin's verbatim, the field general. Public copy at
 <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_ModularCurve_relfinrank_fullC_mul_prime_pow.lean>
 (rendered:
 <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_relfinrank_fullC_mul_prime_pow.lean#L354-L1175>).

 The pin writes the `divSet` / `fullC` / `eFull` / `qExpandₐK` block **twice** —
 once here and once in `P2M/Sol/S_ModularCurve_package_of_socket.lean` (the
 `diff` is 4 lines) — and re-declares it locally on top of
 `IntermediateField.adjoin K {x | ∃ d, d ∣ L ∧ x = jqNModC K d}`. Here it is
 homed once: the ground module `X0/FunctionFieldFull.lean` carries the two
 fields at a general index (`divisorExpansionsC`, `modularFunctionFieldFullC`,
 with no `[NeZero N]` on the index, which is what lets the statements below be
 stated at `M * p ^ a` and `L₀ * p` at all).

 ## The three respellings

 The pin's local spellings are kept as one-line `abbrev`s — `divSet` is
 `divisorExpansionsC`, `fullC` is `modularFunctionFieldFullC`, `qExpandₐK` is
 `qExpandAlg` — so that every statement below is the pin's text **verbatim**
 rather than a restatement over the port's homed names. They are `rfl`-aliases,
 not copies: nothing else in the port may import them (a second consumer would
 be a promotion for the manager, not a second copy). `qExpandₐK` exists because
 the pin's `_apply` lemma and the `eFull` vocabulary are stated with it;
 `qExpandAlg_apply` is the ported home of the same fact.

 ## Layering

 Imported, not restated (the pin's prelude — `TS`, `qTwist`, `phiAtSeed`, the
 at-slot roots API, `coeffMap_*`, `qTwistEquiv*`, ~32 declarations, 264 lines):

 * `fullC` vocabulary — `X0/FunctionFieldFull.lean`: `divisorExpansionsC`,
   `modularFunctionFieldFullC`, `mem_divisorExpansionsC`, `jqModCd_mem_full`,
   `jqModC_mem_full`, `full_degeneracyC_le`;
 * `qExpand` algebra — `Defs/Laurent.lean`: `qExpand`, `qExpandAlg`,
   `qExpandAlg_apply`, `qExpand_qExpand`, `qExpand_congr`, `qExpand_one_apply`,
   `qExpand_injective`;
 * `jqModC`/`jqNModC` — `Defs/JqCoeff.lean`: `jqModC`, `jqNModC`,
   `jqNModC_eq_TS`, `jqNModC_one`, `modularFunctionFieldC`;
 * `TS` API — `Defs/TS.lean`: `TS`, `TS_injective`, `TS_congr`,
   `qExpand_jqNModC`, `qTwist_TS_one_cycle`;
 * `qTwist` — `Defs/Twist.lean`: `qTwist`, `qTwist_one_apply`,
   `qTwist_qExpand`, `qTwist_qTwist`, `qTwistEquiv`, `qTwistEquiv_apply`,
   `coe_qTwistEquiv`; and `Defs/KatzLevelPCusps.lean`:
   `qTwist_qExpand_of_pow_eq_one`;
 * `phiAtSeed` — `Defs/PhiAtSlot.lean`: `phiAtSeed`, `phiAtSeed_map`,
   `phiAtSeed_monic`, `phiAtSeed_natDegree`, `phiAtSeed_jqNModC_eval_symm`;
 * the at-slot splitting and roots — `PhiGenSplitsAnyField.lean`:
   `PhiGen.splits_prime_at_slot_of_isPrimitiveRoot`, `roots_prime_at_slot`,
   `roots_prime_at_slot_roots_nodup`, `isRoot_prime_at_slot_iff`,
   `roots_phiAtSeed_TS`;
 * conjugates — `Degree/JqCyclotomicConjugates.lean`:
   `units_pow_eq_one_of_isPrimitiveRoot`, `jqNModC_congr` (the pin's `private`
   copy at `S_:360` is **not** ported), `phiAtSeed_jqNModC_eval`;
 * `ψ` — `NumberTheory/DedekindPsi.lean`, `ModularCurve/Defs/DedekindPsi.lean`:
   `dedekindPsi_prime` and friends;
 * the irreducible symmetric datum —
   `ModularCurve/ModularPolynomialProperties.lean`:
   `exists_phiIrreducible_evalSymm`;
 * the generic engines — `FieldTheory/CommonRoot.lean`:
   `Polynomial.mem_range_of_unique_common_root`,
   `Polynomial.irreducible_of_transitive_ringAut`.

 `eFull K n L = K⟮(qExpandAlg K n) '' divSet K L⟯` — the field in which the `p`
 `qTwist`-conjugates of `jqModC K` are conjugate — is the vocabulary the next
 `C`-layer node imports: `ModularCurve.package_of_socket` reads
 `eFull`/`eFull_eq_map`/`eFull_mono`/`eFull_le_fullC` from here (the pin
 re-declares them in its own `S_` file for exactly that reason).

 ## Dropped

 * `jqNModC_congr` (pin `S_:360`) — its public home is
   `Degree/JqCyclotomicConjugates.lean:173`;
 * the pin's prelude lines 34–337 (`TS`, `qTwist`, `phiAtSeed`, the at-slot
   roots API, `coeffMap_*`, `qTwistEquiv*` — 40 declarations, all already homed
   in the port), per `## Layering` above;
 * the pin's `solution` / `#print axioms` / `p2m_*` tail: the `solution` copy of
   the headline is statement-identical to it and the pin's own copy is
   `private`, so the public `relfinrank_fullC_mul_prime_pow` below is the one
   transcription;
 * the pin's two `private` re-exports at `S_:1153` and `S_:1159`
   (`fullC_mul_prime_pow_eq_adjoin`, `finrank_adjoin_jqNModC_prime_of_not_mem`):
   dead in the pin as well as in the port — `grep` over the whole pin tree
   returns exactly one occurrence of each (its own declaration), and each states
   what a public declaration above already states
   (`fullC_succ_eq_adjoin_insert_divSet` past one
   `IntermediateField.adjoin_insert_adjoin`, and
   `finrank_adjoin_jqNModC_prime_of_not_mem'` verbatim). They are the pin's
   namespace-re-export idiom, not mathematics.

 Nothing else is dropped: every `divSet`/`eFull`-layer declaration has a
 consumer inside the module.

 ## 7. The socket assembly (CL4)

The module's second headline, `package_of_socket`, is the pin's
`S_ModularCurve_package_of_socket.lean` tail (its lines 781–1003): `Pkg`, the
induction over the divisors of a level, and the public wrapper. `Pkg` itself is
**not** declared here — it is `ModularCurve.Pkg`, an `abbrev` beside the level
fields it is about (`Defs/JqCoeff.lean`), and its reducibility is what lets the
induction apply `Pkg`-typed data as the conjunction it is. The section's new
input is the *prime step* `jqNModC_mem_modularFunctionFieldC_mul_prime` (JQ2),
which `pkg_of_socket` takes as the hypothesis `hKG1` and `package_of_socket`
fills; the rest is the tower arithmetic already in §6 plus
`dedekindPsi_prime_pow`/`dedekindPsi_mul_of_coprime`.

So the module now carries the whole `C`-layer degree story: the prime-power
step of the divisor field (§6) and the assembly that turns the prime step into
`hall` for every divisor (§7). Its two `Theorems/` statements are
`relfinrank_fullC_mul_prime_pow` and `package_of_socket`.

  spec-pin: P2M/Sol/S_ModularCurve_relfinrank_fullC_mul_prime_pow.lean
  spec-pin: Theorems/Thm_ModularCurve_relfinrank_fullC_mul_prime_pow.lean
  spec-pin: P2M/Sol/S_ModularCurve_package_of_socket.lean
  spec-pin: Theorems/Thm_ModularCurve_package_of_socket.lean
-/
import FLTForHuman.FieldTheory.CommonRoot
import FLTForHuman.ModularCurve.Defs.Cyclotomic
import FLTForHuman.ModularCurve.Defs.DedekindPsi
import FLTForHuman.ModularCurve.Defs.JqCoeff
import FLTForHuman.ModularCurve.Defs.KatzLevelPCusps
import FLTForHuman.ModularCurve.Defs.Laurent
import FLTForHuman.ModularCurve.Defs.PhiAtSlot
import FLTForHuman.ModularCurve.Defs.TS
import FLTForHuman.ModularCurve.Defs.Twist
import FLTForHuman.ModularCurve.Degree.JqCyclotomicConjugates
import FLTForHuman.ModularCurve.FunctionFieldGeneration.MffCMulPrime
import FLTForHuman.ModularCurve.ModularPolynomialProperties
import FLTForHuman.ModularCurve.PhiGenSplitsAnyField
import FLTForHuman.ModularCurve.X0.FunctionFieldFull

set_option autoImplicit false
-- The pin installs the `Algebra F (LaurentSeries K)` instance (via `letI`) and
-- the `NeZero`/`Fact` instances of its peeling steps (via `haveI`); both are
-- consumed by typeclass search, so the style linter's `have` preference does
-- not apply. Same local disable as `Generation.lean`/`DegreeStep.lean`.
set_option linter.style.haveILetI false

noncomputable section

open Polynomial HahnSeries IntermediateField

namespace ModularCurve

variable {K : Type*} [Field K]

/-! ## 1. Vocabulary

The pin's local `S_` spellings of the three objects the port homes elsewhere
(`divisorExpansionsC`, `modularFunctionFieldFullC`, `qExpandAlg`), plus the one
new object `eFull` and its API. The `abbrev`s are `rfl`-aliases, so every
statement below is the pin's text verbatim. -/

/-- The pin's local `S_` spelling of `divisorExpansionsC`: the set of `jqNModC K d`
over the `d ∣ L`. -/
abbrev divSet (K : Type*) [Field K] (L : ℕ) : Set (LaurentSeries K) := divisorExpansionsC K L

/-- The pin's local `S_` spelling of `modularFunctionFieldFullC`: the field
generated over `K` by the `jqNModC K d` with `d ∣ L`. -/
abbrev fullC (K : Type*) [Field K] (L : ℕ) : IntermediateField K (LaurentSeries K) :=
  modularFunctionFieldFullC K L

/-- `jqNModC K d ∈ divSet K L` for `d ∣ L`. -/
theorem jqNModC_mem_divSet {d L : ℕ} [NeZero d] (hd : d ∣ L) : jqNModC K d ∈ divSet K L :=
  ⟨d, inferInstance, hd, rfl⟩

/-- `divSet` is monotone in the index. -/
theorem divSet_mono {L L' : ℕ} (h : L ∣ L') : divSet K L ⊆ divSet K L' := by
  rintro x ⟨d, hd0, hdL, rfl⟩
  exact ⟨d, hd0, hdL.trans h, rfl⟩

/-- `jqNModC K d ∈ fullC K L` for `d ∣ L`. -/
theorem jqNModC_mem_fullC {d L : ℕ} [NeZero d] (hd : d ∣ L) : jqNModC K d ∈ fullC K L :=
  IntermediateField.subset_adjoin K _ (jqNModC_mem_divSet hd)

/-- `jqModC K` itself is in every `fullC K L` (it is `jqNModC K 1`). -/
theorem jqModC_mem_fullC (L : ℕ) : jqModC K ∈ fullC K L := by
  have h := jqNModC_mem_fullC (K := K) (d := 1) (one_dvd L)
  rwa [jqNModC_one] at h

/-- `fullC` is monotone in the index. -/
theorem fullC_mono {L L' : ℕ} (h : L ∣ L') : fullC K L ≤ fullC K L' :=
  IntermediateField.adjoin.mono K _ _ (divSet_mono h)

/-- Membership in `fullC K L`, generator by generator: enough to test the
`jqNModC K d` with `d ∣ L`. -/
theorem fullC_le_iff {L : ℕ} {F : IntermediateField K (LaurentSeries K)} :
    fullC K L ≤ F ↔ ∀ (d : ℕ) [NeZero d], d ∣ L → jqNModC K d ∈ F := by
  rw [fullC, modularFunctionFieldFullC, IntermediateField.adjoin_le_iff]
  constructor
  · intro h d _ hd
    exact h (jqNModC_mem_divSet hd)
  · rintro h x ⟨d, hd0, hdL, rfl⟩
    exact h d hdL

/-- `jqNModC K ·` is injective on nonzero indices. -/
theorem jqNModC_injective {d d' : ℕ} [NeZero d] [NeZero d'] (h : jqNModC K d = jqNModC K d') :
    d = d' := by
  rw [jqNModC_eq_TS, jqNModC_eq_TS] at h
  exact (TS_injective h).1

/-- A twisted `jqModC K` is a `TS` value, `qTwist u (jqModC K) = TS K 1 u`. -/
theorem qTwist_jqModC_eq_TS (u : Kˣ) : qTwist u (jqModC K) = TS K 1 u := by
  rw [TS, qExpand_one_apply]

/-- The pin's local `S_` spelling of the ported `qExpandAlg`: `q ↦ q ^ n` as a
`K`-algebra endomorphism of `LaurentSeries K`. -/
abbrev qExpandₐK (K : Type*) [Field K] (n : ℕ) [NeZero n] : LaurentSeries K →ₐ[K] LaurentSeries K :=
  qExpandAlg K n

@[scoped simp] theorem qExpandₐK_apply (n : ℕ) [NeZero n] (f : LaurentSeries K) :
    qExpandₐK K n f = qExpand K n f := rfl

/-- `qExpandₐK` sends `jqNModC K d` to `jqNModC K (n * d)`. -/
theorem qExpandₐK_jqNModC (n d : ℕ) [NeZero n] [NeZero d] :
    qExpandₐK K n (jqNModC K d) = jqNModC K (n * d) := by
  rw [qExpandₐK_apply, jqNModC, jqNModC, qExpand_qExpand]

/-- The `q`-expansion-pushed divisor field: the image of `fullC K L` under
`qExpandₐK K n`, as an adjoin of the pushed generators. It is the field in which
the `n` `qTwist`-conjugates of `jqModC K` are conjugate, which is what makes the
degree computable. -/
def eFull (K : Type*) [Field K] (n : ℕ) [NeZero n] (L : ℕ) :
    IntermediateField K (LaurentSeries K) :=
  IntermediateField.adjoin K ((qExpandₐK K n) '' divSet K L)

/-- `eFull K n L` is the image of `fullC K L` under `qExpandₐK K n`. -/
theorem eFull_eq_map (n : ℕ) [NeZero n] (L : ℕ) : eFull K n L = (fullC K L).map (qExpandₐK K n) := by
  rw [eFull, fullC, modularFunctionFieldFullC, IntermediateField.adjoin_map]

/-- `eFull` is monotone in the index. -/
theorem eFull_mono (n : ℕ) [NeZero n] {L L' : ℕ} (h : L ∣ L') : eFull K n L ≤ eFull K n L' :=
  IntermediateField.adjoin.mono K _ _ (Set.image_mono (divSet_mono h))

/-- `jqNModC K (n * d) ∈ eFull K n L` for `d ∣ L`. -/
theorem jqNModC_mul_mem_eFull (n : ℕ) [NeZero n] {d L : ℕ} [NeZero d] (hd : d ∣ L) :
    jqNModC K (n * d) ∈ eFull K n L :=
  IntermediateField.subset_adjoin K _ ⟨jqNModC K d, jqNModC_mem_divSet hd, qExpandₐK_jqNModC n d⟩

/-- Every element of `eFull K n L` is a `qExpand K n` of something. -/
theorem exists_eq_qExpand_of_mem_eFull (n : ℕ) [NeZero n] {L : ℕ} {x : LaurentSeries K}
    (hx : x ∈ eFull K n L) : ∃ y : LaurentSeries K, qExpand K n y = x := by
  rw [eFull_eq_map, IntermediateField.mem_map] at hx
  obtain ⟨y, -, hy⟩ := hx
  exact ⟨y, hy⟩

/-- A unit twist of order dividing `n` fixes `eFull K n L` pointwise — this is
what makes the `n` conjugates of a root of the pushed minimal polynomial. -/
theorem qTwist_eq_self_of_mem_eFull (n : ℕ) [NeZero n] {L : ℕ} {v : Kˣ} (hv : v ^ n = 1)
    {x : LaurentSeries K} (hx : x ∈ eFull K n L) : qTwist v x = x := by
  obtain ⟨y, rfl⟩ := exists_eq_qExpand_of_mem_eFull n hx
  exact qTwist_qExpand_of_pow_eq_one n v hv y

/-- `eFull K n L` sits inside `fullC K (L * n)`. -/
theorem eFull_le_fullC (n : ℕ) [NeZero n] (L : ℕ) : eFull K n L ≤ fullC K (L * n) := by
  rw [eFull, IntermediateField.adjoin_le_iff]
  rintro x ⟨y, ⟨d, hd0, hdL, rfl⟩, rfl⟩
  rw [qExpandₐK_apply, qExpand_qExpand]
  have h : n * d ∣ L * n := by
    rw [Nat.mul_comm n d]
    exact mul_dvd_mul_right hdL n
  exact jqNModC_mem_fullC h

/-! ## 2. Insertion algebra

Inserting one generator into an adjoin tower, and reading the relative degree as
the degree of a minimal polynomial. `IntermediateField` bookkeeping only. -/

/-- An element of `E` lies in any further adjoin over `E`. -/
theorem mem_adjoin_of_mem {E : IntermediateField K (LaurentSeries K)} {x : LaurentSeries K}
    (hx : x ∈ E) (T : Set (LaurentSeries K)) : x ∈ IntermediateField.adjoin E T :=
  (IntermediateField.adjoin E T).algebraMap_mem ⟨x, hx⟩

/-- Inserting one generator: the relative degree of `K⟮insert α T⟯` over `K⟮T⟯`
is the degree of `K⟮T⟯⟮α⟯` over `K⟮T⟯`. -/
theorem relfinrank_adjoin_insert (T : Set (LaurentSeries K)) (α : LaurentSeries K) :
    IntermediateField.relfinrank (IntermediateField.adjoin K T) (IntermediateField.adjoin K (insert α T))
      = Module.finrank (IntermediateField.adjoin K T)
          (IntermediateField.adjoin (IntermediateField.adjoin K T) ({α} : Set (LaurentSeries K))) := by
  have h : IntermediateField.adjoin K T ≤ IntermediateField.adjoin K (insert α T) :=
    IntermediateField.adjoin.mono _ _ _ (Set.subset_insert α T)
  have hEq : IntermediateField.adjoin (IntermediateField.adjoin K T) (insert α T)
      = IntermediateField.adjoin (IntermediateField.adjoin K T) ({α} : Set (LaurentSeries K)) := by
    refine le_antisymm ?_ ?_
    · rw [IntermediateField.adjoin_le_iff]
      rintro x (rfl | hxT)
      · exact IntermediateField.subset_adjoin _ _ rfl
      · exact mem_adjoin_of_mem (IntermediateField.subset_adjoin K T hxT) _
    · exact IntermediateField.adjoin.mono _ _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert α T))
  rw [IntermediateField.relfinrank_eq_finrank_of_le h, IntermediateField.extendScalars_adjoin h, hEq]

/-- The same, read as the degree of the minimal polynomial. -/
theorem relfinrank_adjoin_insert_eq_natDegree (T : Set (LaurentSeries K)) {α : LaurentSeries K}
    (hα : IsIntegral (IntermediateField.adjoin K T) α) :
    IntermediateField.relfinrank (IntermediateField.adjoin K T) (IntermediateField.adjoin K (insert α T))
      = (minpoly (IntermediateField.adjoin K T) α).natDegree := by
  rw [relfinrank_adjoin_insert, IntermediateField.adjoin.finrank hα]

/-- The `fullC` instance of the insertion form. -/
theorem relfinrank_fullC_insert_eq_natDegree (L : ℕ) {α : LaurentSeries K}
    (hα : IsIntegral (fullC K L) α) :
    IntermediateField.relfinrank (fullC K L) (IntermediateField.adjoin K (insert α (divSet K L)))
      = (minpoly (fullC K L) α).natDegree :=
  relfinrank_adjoin_insert_eq_natDegree (divSet K L) hα

/-- The `eFull` instance of the insertion form. -/
theorem relfinrank_eFull_insert_eq_natDegree (n : ℕ) [NeZero n] (L : ℕ) {α : LaurentSeries K}
    (hα : IsIntegral (eFull K n L) α) :
    IntermediateField.relfinrank (eFull K n L)
        (IntermediateField.adjoin K (insert α ((qExpandₐK K n) '' divSet K L)))
      = (minpoly (eFull K n L) α).natDegree :=
  relfinrank_adjoin_insert_eq_natDegree _ hα

/-! ## 3. Integrality of `jqModC K`

`phiAtSeed data x` is monic of degree `ψ(p)`, so any root `t` of it is integral
over the base field and has `deg minpoly ≤ ψ(p)`; if `Φ_p` already has another
root `r` in the base field, dividing out `(X - r)` drops the bound to `ψ(p) - 1`.
This section is uniform in the intermediate field `F`. -/

section packetBounds

variable {F : IntermediateField K (LaurentSeries K)} {p : ℕ} [NeZero p]

theorem phiAtSeed_map_algebraMap (data : ModularPolynomialData p) {s : LaurentSeries K} (hs : s ∈ F) :
    (phiAtSeed data (⟨s, hs⟩ : F)).map (algebraMap F (LaurentSeries K)) = phiAtSeed data s := by
  rw [phiAtSeed_map]; rfl

theorem aeval_phiAtSeed_eq_zero (data : ModularPolynomialData p) {s : LaurentSeries K} (hs : s ∈ F)
    {t : LaurentSeries K} (ht : (phiAtSeed data s).eval t = 0) :
    Polynomial.aeval t (phiAtSeed data (⟨s, hs⟩ : F)) = 0 := by
  rw [← Polynomial.eval_map_algebraMap, phiAtSeed_map_algebraMap]
  exact ht

theorem isIntegral_of_phiAtSeed_root (data : ModularPolynomialData p) {s : LaurentSeries K} (hs : s ∈ F)
    {t : LaurentSeries K} (ht : (phiAtSeed data s).eval t = 0) : IsIntegral F t :=
  ⟨phiAtSeed data (⟨s, hs⟩ : F), phiAtSeed_monic data _, by
    rw [← Polynomial.aeval_def]; exact aeval_phiAtSeed_eq_zero data hs ht⟩

theorem natDegree_minpoly_le_dedekindPsi_of_phiAtSeed_root (data : ModularPolynomialData p)
    {s : LaurentSeries K} (hs : s ∈ F) {t : LaurentSeries K}
    (ht : (phiAtSeed data s).eval t = 0) :
    (minpoly F t).natDegree ≤ dedekindPsi p := by
  have h := minpoly.degree_le_of_ne_zero F t (phiAtSeed_monic data (⟨s, hs⟩ : F)).ne_zero
    (aeval_phiAtSeed_eq_zero data hs ht)
  have h2 := Polynomial.natDegree_le_natDegree h
  rwa [phiAtSeed_natDegree] at h2

/-- The `ψ(p) - 1` bound: if `Φ_p` at the seed has a root `r ∈ F` and `t ≠ r`, then
`deg minpoly_F t ≤ ψ(p) - 1` — `(X - r)` divides `Φ_p` and `t` cannot be a root of
`(X - r)` as well. -/
theorem natDegree_minpoly_le_of_phiAtSeed_root_of_root_mem (data : ModularPolynomialData p)
    {s : LaurentSeries K} (hs : s ∈ F) {r : LaurentSeries K} (hr : r ∈ F)
    (hrroot : (phiAtSeed data s).eval r = 0) {t : LaurentSeries K}
    (ht : (phiAtSeed data s).eval t = 0) (htr : t ≠ r) :
    (minpoly F t).natDegree ≤ dedekindPsi p - 1 := by
  set P : Polynomial F := phiAtSeed data (⟨s, hs⟩ : F) with hPdef
  set rF : F := ⟨r, hr⟩ with hrF
  have hPr : P.IsRoot rF := by
    rw [Polynomial.IsRoot.def]
    apply (algebraMap F (LaurentSeries K)).injective
    rw [map_zero, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, hPdef, phiAtSeed_map_algebraMap]
    exact hrroot
  set Q : Polynomial F := P /ₘ (Polynomial.X - Polynomial.C rF) with hQdef
  have hPQ : (Polynomial.X - Polynomial.C rF) * Q = P :=
    Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hPr
  have hQne : Q ≠ 0 := by
    intro h0
    have hP0 : P ≠ 0 := (phiAtSeed_monic data (⟨s, hs⟩ : F)).ne_zero
    rw [← hPQ, h0, mul_zero] at hP0
    exact hP0 rfl
  have hQdeg : Q.natDegree = dedekindPsi p - 1 := by
    rw [hQdef, Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C rF),
      Polynomial.natDegree_X_sub_C, hPdef, phiAtSeed_natDegree]
  have htP : Polynomial.aeval t P = 0 := aeval_phiAtSeed_eq_zero data hs ht
  have htQ : Polynomial.aeval t Q = 0 := by
    rw [← hPQ, map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C] at htP
    rcases mul_eq_zero.mp htP with h1 | h1
    · exfalso
      exact htr (sub_eq_zero.mp h1)
    · exact h1
  have h := Polynomial.natDegree_le_natDegree (minpoly.degree_le_of_ne_zero F t hQne htQ)
  rwa [hQdeg] at h

end packetBounds

/-! ## 4. Generation

`fullC K (M * p ^ (a + 1))` is generated over `fullC K (M * p ^ a)` by the single
element `jqNModC K (p ^ (a + 1))`. The engine is the **two-prime descent**: if
`jqNModC K (d / p)` and `jqNModC K (d / q)` both lie in `F`, then `jqNModC K d`
does — `jqNModC K d` is the unique common root of the level-`p` and level-`q`
slot polynomials read at the level-`N` nome. -/

/- The slot calculus used by both descent steps. `phiAtSeed data s` is `data.Φ` read
at the slot `s`, so the at-slot roots API (`PhiGenSplitsAnyField`) states, at a
general slot level `e`, that the pushed level-`p` slot polynomial has exactly the
`p + 1` `TS`-conjugates as roots, and that they are simple. Reading those four
statements off the API once keeps both descents down to the level bookkeeping. -/

/-- **The roots of the level-`p` slot**: `y` is a root of the level-`p` slot
polynomial pushed to the slot `qExpand K (p * e) (qTwist 1 (jqModC K))` exactly when
it is the `p`-th conjugate `qExpand K (p * (p * e)) (qTwist 1 ^ (p * p) (jqModC K))`
or one of the `p` finite conjugates `qExpand K e (qTwist (ζ ^ b) (jqModC K))` with
`b < p`. -/
private lemma eval_phiAtSeed_prime_slot_iff {p : ℕ} [hp : Fact (Nat.Prime p)]
    (data : ModularPolynomialData p) (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p) (e : ℕ) [NeZero e]
    (y : LaurentSeries K) :
    ((data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
      (qExpand K (p * e) (qTwist ((1 : Kˣ) ^ p) (jqModC K))))).eval y = 0) ↔
      (y = qExpand K (p * (p * e)) (qTwist ((1 : Kˣ) ^ (p * p)) (jqModC K)) ∨
        ∃ b < p, y = qExpand K e (qTwist (1 * ζ ^ b) (jqModC K))) :=
  isRoot_prime_at_slot_iff_of_isPrimitiveRoot p ζ hζ data e 1 y

/-- The pushed level-`p` slot polynomial splits over `K`: it is `(X - ·)` at the
`p`-th conjugate times the `p` linear factors of the finite conjugates. -/
private lemma splits_phiAtSeed_prime_slot {p : ℕ} [hp : Fact (Nat.Prime p)]
    (data : ModularPolynomialData p) (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p) (e : ℕ) [NeZero e] :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
      (qExpand K (p * e) (qTwist ((1 : Kˣ) ^ p) (jqModC K))))).Splits := by
  rw [ModularCurve.PhiGen.splits_prime_at_slot_of_isPrimitiveRoot p ζ hζ data e 1]
  exact (Polynomial.Splits.X_sub_C _).mul
    (Polynomial.Splits.prod fun _ _ => Polynomial.Splits.X_sub_C _)

/-- The `p + 1` roots of the pushed level-`p` slot are distinct: the extra one sits
at level `p * (p * e)` and the `p` finite ones at level `e`. -/
private lemma roots_nodup_phiAtSeed_prime_slot {p : ℕ} [hp : Fact (Nat.Prime p)]
    (data : ModularPolynomialData p) (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p) (e : ℕ) [NeZero e] :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
      (qExpand K (p * e) (qTwist ((1 : Kˣ) ^ p) (jqModC K))))).roots.Nodup :=
  roots_prime_at_slot_roots_nodup_of_isPrimitiveRoot p ζ hζ data e 1

/-- The level arithmetic of a prime slot: for `p ∣ N` and `p ∣ d` the two `TS`
levels of the level-`p` slot read at the level-`N` nome, `N / p * (d / p)` and its
`p`-th power, which is `N * d`. -/
private lemma prime_slot_level_arith {N d p : ℕ} (hpN : p ∣ N) (hpd : p ∣ d) :
    p * (N / p * (d / p)) = N * (d / p) ∧ p * (p * (N / p * (d / p))) = N * d := by
  have hE : p * (N / p * (d / p)) = N * (d / p) := by
    rw [← mul_assoc, Nat.mul_div_cancel' hpN]
  exact ⟨hE, by rw [hE, mul_left_comm, Nat.mul_div_cancel' hpd]⟩

/-- **The respelling of a prime slot**: at the level-`N` nome, `j(q ^ (d / p))` is
the level-`p` slot at level `N / p * (d / p)` and `j(q ^ d)` is its `p`-th
conjugate at level `p * (p * (N / p * (d / p)))`. -/
private lemma qExpand_jqNModC_div_prime_eq_slot {N d p : ℕ} [NeZero N] [NeZero p] [NeZero d]
    [NeZero (d / p)] [NeZero (N / p)] (hpN : p ∣ N) (hpd : p ∣ d) :
    qExpand K N (jqNModC K (d / p))
        = qExpand K (p * (N / p * (d / p))) (qTwist ((1 : Kˣ) ^ p) (jqModC K)) ∧
      qExpand K N (jqNModC K d)
        = qExpand K (p * (p * (N / p * (d / p)))) (qTwist ((1 : Kˣ) ^ (p * p)) (jqModC K)) := by
  obtain ⟨hE, hE2⟩ := prime_slot_level_arith hpN hpd
  constructor
  · have h2 : TS K (N * (d / p)) 1 = TS K (p * (N / p * (d / p))) ((1 : Kˣ) ^ p) := by
      rw [one_pow]
      exact TS_congr hE.symm 1
    exact (qExpand_jqNModC N (d / p)).trans h2
  · have h2 : TS K (N * d) 1 = TS K (p * (p * (N / p * (d / p)))) ((1 : Kˣ) ^ (p * p)) := by
      rw [one_pow]
      exact TS_congr hE2.symm 1
    exact (qExpand_jqNModC N d).trans h2

/-- **The unique common root of two prime slots**: for distinct primes `p, q` both
dividing `d` at the level-`N` nome, the level-`p` slot at `jqNModC K (d / p)` and
the level-`q` slot at `jqNModC K (d / q)` have the single common root
`qExpand K N (jqNModC K d)`. Any other pair of roots sits at two different levels,
and `p * p = q * q` is impossible for distinct primes. -/
private lemma unique_common_root_two_prime_slots {N d p q : ℕ} [NeZero N] [NeZero d]
    [NeZero (d / p)] [NeZero (d / q)] [NeZero (N / p)] [NeZero (N / q)] [Fact (Nat.Prime p)]
    [Fact (Nat.Prime q)] (hpq : p ≠ q) (hpN : p ∣ N) (hqN : q ∣ N) (hpd : p ∣ d) (hqd : q ∣ d)
    (ζp : Kˣ) (ζq : Kˣ) :
    ∀ y : LaurentSeries K,
      (y = qExpand K (p * (p * (N / p * (d / p)))) (qTwist ((1 : Kˣ) ^ (p * p)) (jqModC K)) ∨
        ∃ b < p, y = qExpand K (N / p * (d / p)) (qTwist (1 * ζp ^ b) (jqModC K))) →
      (y = qExpand K (q * (q * (N / q * (d / q)))) (qTwist ((1 : Kˣ) ^ (q * q)) (jqModC K)) ∨
        ∃ c < q, y = qExpand K (N / q * (d / q)) (qTwist (1 * ζq ^ c) (jqModC K))) →
      y = qExpand K N (jqNModC K d) := by
  obtain ⟨-, hdist_p⟩ := qExpand_jqNModC_div_prime_eq_slot (K := K) (p := p) hpN hpd
  obtain ⟨-, hdist_q⟩ := qExpand_jqNModC_div_prime_eq_slot (K := K) (p := q) hqN hqd
  obtain ⟨-, hpe2⟩ := prime_slot_level_arith hpN hpd
  obtain ⟨-, hqe2⟩ := prime_slot_level_arith hqN hqd
  intro y hyA hyB
  rcases hyA with hy1 | ⟨b, _, hy1⟩
  · exact hy1.trans hdist_p.symm
  · rcases hyB with hy2 | ⟨c, _, hy2⟩
    · exact hy2.trans hdist_q.symm
    · exfalso
      have hTS : TS K (N / p * (d / p)) (1 * ζp ^ b) = TS K (N / q * (d / q)) (1 * ζq ^ c) :=
        hy1.symm.trans hy2
      have he : N / p * (d / p) = N / q * (d / q) := (TS_injective hTS).1
      have h1 : p * p * (N / p * (d / p)) = q * q * (N / p * (d / p)) := by
        rw [mul_assoc, hpe2, mul_assoc, he, hqe2]
      have h2 : p * p = q * q :=
        Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (NeZero.ne (N / p * (d / p)))) h1
      have h3 : q ∣ p * p := by rw [h2]; exact dvd_mul_right q q
      have h4 : q ∣ p := ((Nat.Prime.dvd_mul (Fact.out : Nat.Prime q)).mp h3).elim id id
      exact hpq (((Nat.prime_dvd_prime_iff_eq (Fact.out : Nat.Prime q)
        (Fact.out : Nat.Prime p)).mp h4).symm)

/-- The second slot of the single-prime step: `qExpand K N` of `jqNModC K (p * d)`
is the level-`p` slot at level `N * d`. -/
private lemma qExpand_jqNModC_mul_prime_eq_slot {N d p : ℕ} [NeZero N] [NeZero p] [NeZero d]
    [NeZero (p * d)] :
    qExpand K N (jqNModC K (p * d))
      = qExpand K (p * (N * d)) (qTwist ((1 : Kˣ) ^ p) (jqModC K)) := by
  have h2 : TS K (N * (p * d)) 1 = TS K (p * (N * d)) ((1 : Kˣ) ^ p) := by
    rw [one_pow]
    exact TS_congr (Nat.mul_left_comm N p d) 1
  exact (qExpand_jqNModC N (p * d)).trans h2

/-- **The unique common root of a prime slot and a multiplied slot**: the level-`l`
slot at `jqNModC K (d / l)` and the level-`p` slot at `jqNModC K (p * d)` have the
single common root `qExpand K N (jqNModC K d)`. The only candidate pair is the finite
root of the second slot at level `N * d` against the extra root of the first at
level `l * (l * (N / l * (d / l)))`, and `l ≥ 2` makes those two levels differ. -/
private lemma unique_common_root_of_prime_slot_and_mul_prime_slot {N d l p : ℕ} [NeZero N]
    [NeZero d] [NeZero (d / l)] [NeZero (p * d)] [NeZero (N / l)] [Fact (Nat.Prime l)]
    [Fact (Nat.Prime p)] (hlN : l ∣ N) (hld : l ∣ d) (ζl : Kˣ) (ζp : Kˣ) :
    ∀ y : LaurentSeries K,
      (y = qExpand K (l * (l * (N / l * (d / l)))) (qTwist ((1 : Kˣ) ^ (l * l)) (jqModC K)) ∨
        ∃ b < l, y = qExpand K (N / l * (d / l)) (qTwist (1 * ζl ^ b) (jqModC K))) →
      (y = qExpand K (p * (p * (N * d))) (qTwist ((1 : Kˣ) ^ (p * p)) (jqModC K)) ∨
        ∃ c < p, y = qExpand K (N * d) (qTwist (1 * ζp ^ c) (jqModC K))) →
      y = qExpand K N (jqNModC K d) := by
  obtain ⟨-, hdist_l⟩ := qExpand_jqNModC_div_prime_eq_slot (K := K) (p := l) hlN hld
  obtain ⟨-, hle2⟩ := prime_slot_level_arith hlN hld
  have he0 : 0 < N / l * (d / l) := Nat.pos_of_ne_zero (NeZero.ne _)
  set e₁ := N / l * (d / l) with he₁
  haveI : NeZero e₁ := ⟨by rw [he₁]; exact he0.ne'⟩
  have hl2 : 2 ≤ l := (Fact.out : Nat.Prime l).two_le
  have hp2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have hbig1 : 2 * (2 * e₁) ≤ l * (l * e₁) := Nat.mul_le_mul hl2 (Nat.mul_le_mul hl2 le_rfl)
  have hbig2 : 2 * (2 * (l * (l * e₁))) ≤ p * (p * (l * (l * e₁))) :=
    Nat.mul_le_mul hp2 (Nat.mul_le_mul hp2 le_rfl)
  intro y hyA hyB
  rcases hyA with hy1 | ⟨b, _, hy1⟩
  · exact hy1.trans hdist_l.symm
  · exfalso
    rcases hyB with hy2 | ⟨c, _, hy2⟩
    · have hTS : TS K e₁ (1 * ζl ^ b) = TS K (p * (p * (N * d))) ((1 : Kˣ) ^ (p * p)) :=
        hy1.symm.trans hy2
      have he : e₁ = p * (p * (N * d)) := (TS_injective hTS).1
      rw [← hle2] at he
      omega
    · have hTS : TS K e₁ (1 * ζl ^ b) = TS K (N * d) (1 * ζp ^ c) := hy1.symm.trans hy2
      have he : e₁ = N * d := (TS_injective hTS).1
      rw [← hle2] at he
      omega

/-- **The two-prime descent**: if `j(q ^ (d / p))` and `j(q ^ (d / q))` lie in a
subfield `F ≤ LaurentSeries K`, then `j(q ^ d)` does. The unique-common-root
principle (`Polynomial.mem_range_of_unique_common_root`) applied to the level-`p`
and level-`q` data read at the level-`N` nome; `j(q ^ d)` is the unique common
root, by `TS_injective` on the twist levels. -/
theorem jqNModC_mem_of_div_primes {N : ℕ} [NeZero N] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N)
    {F : IntermediateField K (LaurentSeries K)} {d : ℕ} [NeZero d] (hdN : d ∣ N)
    {p q : ℕ} (pp : Nat.Prime p) (qq : Nat.Prime q) (hpq : p ≠ q) (hpd : p ∣ d) (hqd : q ∣ d)
    [NeZero (d / p)] [NeZero (d / q)] (hmp : jqNModC K (d / p) ∈ F)
    (hmq : jqNModC K (d / q) ∈ F) : jqNModC K d ∈ F := by
  haveI : Fact (Nat.Prime p) := ⟨pp⟩
  haveI : Fact (Nat.Prime q) := ⟨qq⟩
  have hpN : p ∣ N := hpd.trans hdN
  have hqN : q ∣ N := hqd.trans hdN
  haveI : NeZero (N / p) := ⟨fun h0 => NeZero.ne N (by rw [← Nat.div_mul_cancel hpN, h0, zero_mul])⟩
  haveI : NeZero (N / q) := ⟨fun h0 => NeZero.ne N (by rw [← Nat.div_mul_cancel hqN, h0, zero_mul])⟩
  have hζp : IsPrimitiveRoot ((ζ ^ (N / p) : Kˣ) : K) p := isPrimitiveRoot_pow_div hζ hpN
  have hζq : IsPrimitiveRoot ((ζ ^ (N / q) : Kˣ) : K) q := isPrimitiveRoot_pow_div hζ hqN
  obtain ⟨data_p, -, -⟩ := ModularCurve.exists_phiIrreducible_evalSymm p
  obtain ⟨data_q, -, -⟩ := ModularCurve.exists_phiIrreducible_evalSymm q
  -- the level-`N` nome pushes the two seeds into the two level-`p` / level-`q` slots
  letI : Algebra F (LaurentSeries K) := ((qExpand K N).comp (algebraMap F (LaurentSeries K))).toAlgebra
  have hmapA : (phiAtSeed data_p (⟨jqNModC K (d / p), hmp⟩ : F)).map (algebraMap F (LaurentSeries K))
      = phiAtSeed data_p (qExpand K N (jqNModC K (d / p))) :=
    phiAtSeed_map data_p _ _
  have hmapB : (phiAtSeed data_q (⟨jqNModC K (d / q), hmq⟩ : F)).map (algebraMap F (LaurentSeries K))
      = phiAtSeed data_q (qExpand K N (jqNModC K (d / q))) :=
    phiAtSeed_map data_q _ _
  obtain ⟨hslot_p, hdist_p⟩ := qExpand_jqNModC_div_prime_eq_slot (K := K) (p := p) hpN hpd
  obtain ⟨hslot_q, hdist_q⟩ := qExpand_jqNModC_div_prime_eq_slot (K := K) (p := q) hqN hqd
  -- both pushed slots are split with simple roots
  have hsplit : ((phiAtSeed data_p (⟨jqNModC K (d / p), hmp⟩ : F)).map
        (algebraMap F (LaurentSeries K))).Splits ∧
      ((phiAtSeed data_p (⟨jqNModC K (d / p), hmp⟩ : F)).map
        (algebraMap F (LaurentSeries K))).roots.Nodup := by
    rw [hmapA, hslot_p]
    exact ⟨splits_phiAtSeed_prime_slot data_p _ hζp _,
      roots_nodup_phiAtSeed_prime_slot data_p _ hζp _⟩
  -- and their roots are read off the two slots
  have hrootP : ∀ y : LaurentSeries K,
      Polynomial.aeval y (phiAtSeed data_p (⟨jqNModC K (d / p), hmp⟩ : F)) = 0 ↔
        (y = qExpand K (p * (p * (N / p * (d / p)))) (qTwist ((1 : Kˣ) ^ (p * p)) (jqModC K)) ∨
          ∃ b < p, y = qExpand K (N / p * (d / p)) (qTwist (1 * (ζ ^ (N / p)) ^ b) (jqModC K))) := by
    intro y
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hmapA, hslot_p]
    exact eval_phiAtSeed_prime_slot_iff data_p _ hζp _ y
  have hrootQ : ∀ y : LaurentSeries K,
      Polynomial.aeval y (phiAtSeed data_q (⟨jqNModC K (d / q), hmq⟩ : F)) = 0 ↔
        (y = qExpand K (q * (q * (N / q * (d / q)))) (qTwist ((1 : Kˣ) ^ (q * q)) (jqModC K)) ∨
          ∃ c < q, y = qExpand K (N / q * (d / q)) (qTwist (1 * (ζ ^ (N / q)) ^ c) (jqModC K))) := by
    intro y
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hmapB, hslot_q]
    exact eval_phiAtSeed_prime_slot_iff data_q _ hζq _ y
  -- `j(q ^ d)` is their unique common root, so it is fixed by the level-`N` nome
  have huniq : ∀ y : LaurentSeries K,
      Polynomial.aeval y (phiAtSeed data_p (⟨jqNModC K (d / p), hmp⟩ : F)) = 0 →
      Polynomial.aeval y (phiAtSeed data_q (⟨jqNModC K (d / q), hmq⟩ : F)) = 0 →
      y = qExpand K N (jqNModC K d) :=
    fun y hyA hyB => unique_common_root_two_prime_slots hpq hpN hqN hpd hqd _ _ y
      ((hrootP y).mp hyA) ((hrootQ y).mp hyB)
  obtain ⟨f, hf⟩ := RingHom.mem_range.mp
    (Polynomial.mem_range_of_unique_common_root (phiAtSeed data_p (⟨jqNModC K (d / p), hmp⟩ : F))
      (phiAtSeed data_q (⟨jqNModC K (d / q), hmq⟩ : F)) (phiAtSeed_monic data_p _).ne_zero hsplit.1
      hsplit.2 (qExpand K N (jqNModC K d)) ((hrootP _).mpr (Or.inl hdist_p))
      ((hrootQ _).mpr (Or.inl hdist_q)) huniq)
  have hval : (f : LaurentSeries K) = jqNModC K d := qExpand_injective N hf
  rw [← hval]
  exact f.2
/-- **The single-prime peeling step**: if `j(q ^ (d / l))` and `j(q ^ (p * d))`
lie in `F`, so does `j(q ^ d)`. The second slot sits at level `p * d` (the
`c = 0` finite conjugate of the level-`p` slot at `N * d`), so the unique common
root of the level-`l` and level-`p` polynomials is `j(q ^ d)` — a level mismatch
excludes every other pair, by `TS_injective` and `omega`. -/
theorem jqNModC_mem_of_div_prime_of_mul_prime {N : ℕ} [NeZero N] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) N) {F : IntermediateField K (LaurentSeries K)} {d : ℕ} [NeZero d]
    {l p : ℕ} (ll : Nat.Prime l) (pp : Nat.Prime p) (hlN : l ∣ N) (hpN : p ∣ N) (hld : l ∣ d)
    [NeZero (d / l)] [NeZero (p * d)] (hml : jqNModC K (d / l) ∈ F)
    (hmp : jqNModC K (p * d) ∈ F) : jqNModC K d ∈ F := by
  haveI : Fact (Nat.Prime l) := ⟨ll⟩
  haveI : Fact (Nat.Prime p) := ⟨pp⟩
  haveI : NeZero (N / l) := ⟨fun h0 => NeZero.ne N (by rw [← Nat.div_mul_cancel hlN, h0, zero_mul])⟩
  have hζl : IsPrimitiveRoot ((ζ ^ (N / l) : Kˣ) : K) l := isPrimitiveRoot_pow_div hζ hlN
  have hζp : IsPrimitiveRoot ((ζ ^ (N / p) : Kˣ) : K) p := isPrimitiveRoot_pow_div hζ hpN
  obtain ⟨data_l, -, -⟩ := ModularCurve.exists_phiIrreducible_evalSymm l
  obtain ⟨data_p, -, -⟩ := ModularCurve.exists_phiIrreducible_evalSymm p
  -- the level-`N` nome pushes the two seeds into the level-`l` and level-`p` slots
  letI : Algebra F (LaurentSeries K) := ((qExpand K N).comp (algebraMap F (LaurentSeries K))).toAlgebra
  have hmapA : (phiAtSeed data_l (⟨jqNModC K (d / l), hml⟩ : F)).map (algebraMap F (LaurentSeries K))
      = phiAtSeed data_l (qExpand K N (jqNModC K (d / l))) :=
    phiAtSeed_map data_l _ _
  have hmapB : (phiAtSeed data_p (⟨jqNModC K (p * d), hmp⟩ : F)).map (algebraMap F (LaurentSeries K))
      = phiAtSeed data_p (qExpand K N (jqNModC K (p * d))) :=
    phiAtSeed_map data_p _ _
  obtain ⟨hslot_l, hdist_l⟩ := qExpand_jqNModC_div_prime_eq_slot (K := K) (p := l) hlN hld
  have hslot_p : qExpand K N (jqNModC K (p * d))
      = qExpand K (p * (N * d)) (qTwist ((1 : Kˣ) ^ p) (jqModC K)) :=
    qExpand_jqNModC_mul_prime_eq_slot
  have hdist_p : qExpand K N (jqNModC K d)
      = qExpand K (N * d) (qTwist (1 * (ζ ^ (N / p)) ^ 0) (jqModC K)) := by
    rw [pow_zero, mul_one]
    exact qExpand_jqNModC N d
  have hsplit : ((phiAtSeed data_l (⟨jqNModC K (d / l), hml⟩ : F)).map
        (algebraMap F (LaurentSeries K))).Splits ∧
      ((phiAtSeed data_l (⟨jqNModC K (d / l), hml⟩ : F)).map
        (algebraMap F (LaurentSeries K))).roots.Nodup := by
    rw [hmapA, hslot_l]
    exact ⟨splits_phiAtSeed_prime_slot data_l _ hζl _,
      roots_nodup_phiAtSeed_prime_slot data_l _ hζl _⟩
  have hrootP : ∀ y : LaurentSeries K,
      Polynomial.aeval y (phiAtSeed data_l (⟨jqNModC K (d / l), hml⟩ : F)) = 0 ↔
        (y = qExpand K (l * (l * (N / l * (d / l)))) (qTwist ((1 : Kˣ) ^ (l * l)) (jqModC K)) ∨
          ∃ b < l, y = qExpand K (N / l * (d / l)) (qTwist (1 * (ζ ^ (N / l)) ^ b) (jqModC K))) := by
    intro y
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hmapA, hslot_l]
    exact eval_phiAtSeed_prime_slot_iff data_l _ hζl _ y
  have hrootQ : ∀ y : LaurentSeries K,
      Polynomial.aeval y (phiAtSeed data_p (⟨jqNModC K (p * d), hmp⟩ : F)) = 0 ↔
        (y = qExpand K (p * (p * (N * d))) (qTwist ((1 : Kˣ) ^ (p * p)) (jqModC K)) ∨
          ∃ c < p, y = qExpand K (N * d) (qTwist (1 * (ζ ^ (N / p)) ^ c) (jqModC K))) := by
    intro y
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hmapB, hslot_p]
    exact eval_phiAtSeed_prime_slot_iff data_p _ hζp _ y
  -- `j(q ^ d)` is their unique common root, so it is fixed by the level-`N` nome
  have huniq : ∀ y : LaurentSeries K,
      Polynomial.aeval y (phiAtSeed data_l (⟨jqNModC K (d / l), hml⟩ : F)) = 0 →
      Polynomial.aeval y (phiAtSeed data_p (⟨jqNModC K (p * d), hmp⟩ : F)) = 0 →
      y = qExpand K N (jqNModC K d) :=
    fun y hyA hyB => unique_common_root_of_prime_slot_and_mul_prime_slot hlN hld _ _ y
      ((hrootP y).mp hyA) ((hrootQ y).mp hyB)
  obtain ⟨f, hf⟩ := RingHom.mem_range.mp
    (Polynomial.mem_range_of_unique_common_root (phiAtSeed data_l (⟨jqNModC K (d / l), hml⟩ : F))
      (phiAtSeed data_p (⟨jqNModC K (p * d), hmp⟩ : F)) (phiAtSeed_monic data_l _).ne_zero hsplit.1
      hsplit.2 (qExpand K N (jqNModC K d)) ((hrootP _).mpr (Or.inl hdist_l))
      ((hrootQ _).mpr (Or.inr ⟨0, pp.pos, hdist_p⟩)) huniq)
  have hval : (f : LaurentSeries K) = jqNModC K d := qExpand_injective N hf
  rw [← hval]
  exact f.2
/-- **The coprime split of the divisor**: if `p ∤ M` and `d ∣ M * p ^ (a + 1)` does not
divide `M * p ^ a`, then the `p`-part of `d` is exactly `p ^ (a + 1)`. With
`m = gcd d M` one has `d = m * p ^ (a + 1)`, `m ∣ M` and `m ≠ 0`. -/
private lemma exists_gcd_mul_prime_pow_of_not_dvd {M d p a : ℕ} [NeZero M] (hp : Nat.Prime p)
    (hpM : ¬ p ∣ M) (hdN : d ∣ M * p ^ (a + 1)) (hbase : ¬ d ∣ M * p ^ a) :
    ∃ m : ℕ, m ∣ M ∧ m ≠ 0 ∧ d = m * p ^ (a + 1) := by
  set g := Nat.gcd d M with hgdef
  have hgM : g ∣ M := Nat.gcd_dvd_right d M
  have hg0 : g ≠ 0 := fun h0 => NeZero.ne M (Nat.eq_zero_of_zero_dvd (h0 ▸ hgM))
  have hcop : Nat.Coprime M (p ^ (a + 1)) :=
    (Nat.Coprime.pow_right _ (((Nat.Prime.coprime_iff_not_dvd hp).mpr hpM).symm))
  have hsplit : g * Nat.gcd d (p ^ (a + 1)) = d :=
    (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hcop).mpr hdN
  obtain ⟨j, hj, hpj⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_right d (p ^ (a + 1)))
  have hd : d = g * p ^ j := by rw [← hsplit, hpj]
  have hja : j = a + 1 := by
    by_contra hja
    exact hbase (hd ▸ mul_dvd_mul hgM (pow_dvd_pow p (by omega)))
  rw [hja] at hd
  exact ⟨g, hgM, hg0, hd⟩

/-- **The descent case of the generation walk** (`m ≠ 1`): a prime `q = minFac m`,
which is not `p`, divides `d`, and the two-prime descent gives `jqNModC K d` from
`d / p` (a divisor of `M * p ^ a`, hence in the target) and `d / q` (smaller, hence
the strong induction hypothesis). -/
private lemma jqNModC_mem_adjoin_top_insert_of_gcd_ne_one (M : ℕ) [NeZero M] (p : ℕ)
    [hp : Fact (Nat.Prime p)] (a : ℕ) (hpM : ¬ p ∣ M) (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) (M * p ^ (a + 1))) {d m : ℕ} [NeZero d]
    (hdN : d ∣ M * p ^ (a + 1)) (hmM : m ∣ M) (hm0 : m ≠ 0) (hd : d = m * p ^ (a + 1))
    (hm1 : m ≠ 1)
    (ih : ∀ (d' : ℕ), d' < d → ∀ [NeZero d'], d' ∣ M * p ^ (a + 1) →
      jqNModC K d' ∈ IntermediateField.adjoin K
        (insert (jqNModC K (p ^ (a + 1))) (divSet K (M * p ^ a)))) :
    jqNModC K d ∈ IntermediateField.adjoin K
      (insert (jqNModC K (p ^ (a + 1))) (divSet K (M * p ^ a))) := by
  set q := m.minFac with hqdef
  have hq : q.Prime := Nat.minFac_prime hm1
  have hqm : q ∣ m := Nat.minFac_dvd m
  have hqp : p ≠ q := fun h => hpM ((h ▸ hqm).trans hmM)
  have hpd : p ∣ d := hd ▸ Dvd.dvd.mul_left (dvd_pow_self p (Nat.succ_ne_zero a)) m
  have hqd : q ∣ d := hd ▸ (hqm.trans (dvd_mul_right m (p ^ (a + 1))))
  obtain ⟨m', hm'⟩ := hqm
  have hm'0 : m' ≠ 0 := fun h0 => hm0 (by rw [hm', h0, Nat.mul_zero])
  have hdp : d / p = m * p ^ a := by
    rw [hd, pow_succ, ← Nat.mul_assoc, Nat.mul_div_cancel _ hp.out.pos]
  have hdq : d / q = m' * p ^ (a + 1) := by
    rw [hd, hm', Nat.mul_assoc, Nat.mul_div_cancel_left _ hq.pos]
  haveI : NeZero (d / p) :=
    ⟨by rw [hdp]; exact Nat.mul_ne_zero hm0 (pow_ne_zero _ hp.out.ne_zero)⟩
  haveI : NeZero (d / q) :=
    ⟨by rw [hdq]; exact Nat.mul_ne_zero hm'0 (pow_ne_zero _ hp.out.ne_zero)⟩
  have hmem_p : jqNModC K (d / p) ∈
      IntermediateField.adjoin K (insert (jqNModC K (p ^ (a + 1))) (divSet K (M * p ^ a))) := by
    refine IntermediateField.subset_adjoin K _ (Set.mem_insert_of_mem _ (jqNModC_mem_divSet ?_))
    rw [hdp]
    exact mul_dvd_mul hmM dvd_rfl
  have hmem_q : jqNModC K (d / q) ∈
      IntermediateField.adjoin K (insert (jqNModC K (p ^ (a + 1))) (divSet K (M * p ^ a))) := by
    exact ih (d / q) (Nat.div_lt_self (Nat.pos_of_ne_zero (NeZero.ne d)) hq.one_lt)
      ((Nat.div_dvd_of_dvd hqd).trans hdN)
  exact jqNModC_mem_of_div_primes ζ hζ hdN hp.out hq hqp hpd hqd hmem_p hmem_q

/-- **The generation walk**: every `jqNModC K d` with `d ∣ M * p ^ (a + 1)` lies in
`K⟮insert (jqNModC K (p ^ (a + 1))) (divSet K (M * p ^ a))⟯`. Strong induction on
`d`: either `d` already divides `M * p ^ a`, or a prime `q ≠ p` divides its
`M`-part and the two-prime descent applies to `d / p` (in the target) and `d / q`
(smaller, so the induction hypothesis). -/
theorem jqNModC_mem_adjoin_top_insert (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)] (a : ℕ)
    (hpM : ¬ p ∣ M) (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) (M * p ^ (a + 1))) :
    ∀ (d : ℕ) [NeZero d], d ∣ M * p ^ (a + 1) →
      jqNModC K d ∈ IntermediateField.adjoin K
        (insert (jqNModC K (p ^ (a + 1))) (divSet K (M * p ^ a))) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd0 hdN
    by_cases hbase : d ∣ M * p ^ a
    · exact IntermediateField.subset_adjoin K _ (Set.mem_insert_of_mem _ (jqNModC_mem_divSet hbase))
    · obtain ⟨m, hmM, hm0, hd⟩ := exists_gcd_mul_prime_pow_of_not_dvd hp.out hpM hdN hbase
      rcases eq_or_ne m 1 with hm1 | hm1
      · rw [jqNModC_congr (show d = p ^ (a + 1) by rw [hd, hm1, one_mul])]
        exact IntermediateField.subset_adjoin K _ (Set.mem_insert _ _)
      · exact jqNModC_mem_adjoin_top_insert_of_gcd_ne_one M p a hpM ζ hζ hdN hmM hm0 hd hm1 ih
/-- **One new generator per prime power**:
`fullC K (M * p ^ (a + 1)) = K⟮insert (jqNModC K (p ^ (a + 1))) (divSet K (M * p ^ a))⟯`. -/
theorem fullC_succ_eq_adjoin_insert_divSet (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)] (a : ℕ)
    (hpM : ¬ p ∣ M) (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) (M * p ^ (a + 1))) :
    fullC K (M * p ^ (a + 1))
      = IntermediateField.adjoin K (insert (jqNModC K (p ^ (a + 1))) (divSet K (M * p ^ a))) := by
  refine le_antisymm ?_ ?_
  · rw [fullC_le_iff]
    intro d hd0 hd
    exact jqNModC_mem_adjoin_top_insert M p a hpM ζ hζ d hd
  · rw [IntermediateField.adjoin_le_iff]
    rintro x (rfl | hx)
    · exact jqNModC_mem_fullC (dvd_mul_left _ _)
    · exact fullC_mono (mul_dvd_mul_left M (pow_dvd_pow p (Nat.le_succ a)))
        (IntermediateField.subset_adjoin K _ hx)

/-- **The `p ∣ d` case of the `L₀ * p` generation walk**: `d = p * d'` with `d' ∣ L₀`, so
`jqNModC K d` is the pushed generator `qExpandₐK K p (jqNModC K d')` of the target. -/
private lemma jqNModC_mem_adjoin_insert_image_of_dvd (L₀ : ℕ) (p : ℕ) [hp : Fact (Nat.Prime p)]
    {d : ℕ} [NeZero d] (hdL : d ∣ L₀ * p) (hpd : p ∣ d) :
    jqNModC K d ∈ IntermediateField.adjoin K
      (insert (jqModC K) ((qExpandₐK K p) '' divSet K L₀)) := by
  obtain ⟨d', rfl⟩ := hpd
  have hd'L : d' ∣ L₀ := by
    have h := hdL
    rw [Nat.mul_comm L₀ p] at h
    exact Nat.dvd_of_mul_dvd_mul_left hp.out.pos h
  haveI : NeZero d' := ⟨fun h0 => NeZero.ne (p * d') (by rw [h0, Nat.mul_zero])⟩
  exact IntermediateField.subset_adjoin K _
    (Set.mem_insert_of_mem _ ⟨jqNModC K d', jqNModC_mem_divSet hd'L, qExpandₐK_jqNModC p d'⟩)

/-- **The `p ∤ d` case of the `L₀ * p` generation walk**: `d` then divides `L₀` and is not
`1`, so its least prime `l` (which is not `p`) gives `jqNModC K d` by the single-prime
step, from `d / l` (smaller, the induction hypothesis) and `p * d` (the pushed image
of `d`). -/
private lemma jqNModC_mem_adjoin_insert_image_of_not_dvd (L₀ : ℕ) [NeZero L₀] (p : ℕ)
    [hp : Fact (Nat.Prime p)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) (L₀ * p)) {d : ℕ} [NeZero d] (hdL : d ∣ L₀ * p)
    (hpd : ¬ p ∣ d)
    (ih : ∀ (d' : ℕ), d' < d → ∀ [NeZero d'], d' ∣ L₀ * p →
      jqNModC K d' ∈ IntermediateField.adjoin K
        (insert (jqModC K) ((qExpandₐK K p) '' divSet K L₀))) :
    jqNModC K d ∈ IntermediateField.adjoin K
      (insert (jqModC K) ((qExpandₐK K p) '' divSet K L₀)) := by
  have hdL₀ : d ∣ L₀ :=
    Nat.Coprime.dvd_of_dvd_mul_right (((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpd).symm) hdL
  rcases eq_or_ne d 1 with hd1 | hd1
  · subst hd1
    rw [jqNModC_one]
    exact IntermediateField.subset_adjoin K _ (Set.mem_insert _ _)
  · set l := d.minFac with hldef
    have hl : l.Prime := Nat.minFac_prime hd1
    obtain ⟨d₁, hd₁⟩ := (Nat.minFac_dvd d : l ∣ d)
    have hd₁0 : d₁ ≠ 0 := fun h0 => NeZero.ne d (by rw [hd₁, h0, Nat.mul_zero])
    have hdl : d / l = d₁ := by rw [hd₁, Nat.mul_div_cancel_left _ hl.pos]
    haveI : NeZero (d / l) := ⟨by rw [hdl]; exact hd₁0⟩
    have hld : l ∣ d := ⟨d₁, hd₁⟩
    have hmem_l : jqNModC K (d / l) ∈ IntermediateField.adjoin K
        (insert (jqModC K) ((qExpandₐK K p) '' divSet K L₀)) := by
      exact ih (d / l) (Nat.div_lt_self (Nat.pos_of_ne_zero (NeZero.ne d)) hl.one_lt)
        ((Nat.div_dvd_of_dvd hld).trans hdL)
    have hmem_p : jqNModC K (p * d) ∈ IntermediateField.adjoin K
        (insert (jqModC K) ((qExpandₐK K p) '' divSet K L₀)) :=
      IntermediateField.subset_adjoin K _
        (Set.mem_insert_of_mem _ ⟨jqNModC K d, jqNModC_mem_divSet hdL₀, qExpandₐK_jqNModC p d⟩)
    exact jqNModC_mem_of_div_prime_of_mul_prime ζ hζ hl hp.out (hld.trans hdL) (dvd_mul_left p L₀)
      hld hmem_l hmem_p

/-- **The reverse inclusion**: both generators of
`K⟮insert (jqModC K) ((qExpandₐK K p) '' divSet K L₀)⟯` lie in `fullC K (L₀ * p)` —
`jqModC K` is `jqNModC K 1`, and `qExpandₐK K p` sends `jqNModC K d` with `d ∣ L₀` to
`jqNModC K (p * d)` with `p * d ∣ L₀ * p`. -/
private lemma adjoin_insert_jqModC_image_le_fullC (L₀ : ℕ) [NeZero L₀] (p : ℕ)
    [hp : Fact (Nat.Prime p)] :
    IntermediateField.adjoin K (insert (jqModC K) ((qExpandₐK K p) '' divSet K L₀))
      ≤ fullC K (L₀ * p) := by
  rw [IntermediateField.adjoin_le_iff]
  rintro x (rfl | ⟨y, ⟨d, hd0, hdL, rfl⟩, rfl⟩)
  · exact jqModC_mem_fullC _
  · rw [qExpandₐK_apply, qExpand_qExpand]
    have h : p * d ∣ L₀ * p := by
      rw [Nat.mul_comm p d]
      exact mul_dvd_mul_right hdL p
    exact jqNModC_mem_fullC h

/-- **The `L₀ * p` generation step**:
`fullC K (L₀ * p) = K⟮insert (jqModC K) ((qExpandₐK K p) '' divSet K L₀)⟯`. The
strong induction on `d ∣ L₀ * p` peels a prime `l` from `d` (`l = p` lands in the
image, `l ≠ p` uses the single-prime step with the `M`-part of `d`). -/
theorem fullC_mul_prime_eq_adjoin_insert_image (L₀ : ℕ) [NeZero L₀] (p : ℕ) [hp : Fact (Nat.Prime p)]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) (L₀ * p)) :
    fullC K (L₀ * p) = IntermediateField.adjoin K (insert (jqModC K) ((qExpandₐK K p) '' divSet K L₀)) := by
  refine le_antisymm ?_ (adjoin_insert_jqModC_image_le_fullC L₀ p)
  rw [fullC_le_iff]
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd0 hdL
    by_cases hpd : p ∣ d
    · exact jqNModC_mem_adjoin_insert_image_of_dvd L₀ p hdL hpd
    · exact jqNModC_mem_adjoin_insert_image_of_not_dvd L₀ p ζ hζ hdL hpd ih
/-! ## 5. The `eFull` degree block

This is the node's genuinely new mathematics (no `ℚ` counterpart anywhere): the
`p` `qTwist`-conjugates of `jqModC K` are distinct roots of the pushed minimal
polynomial over `eFull K p L₀`, because `eFull` is `qTwist`-fixed. Combined with
§3's upper bound this pins `[fullC K (L₀ * p) : eFull K p L₀]`. -/

section eFullDegree

variable (L₀ : ℕ) (p : ℕ) [hp : Fact (Nat.Prime p)]

theorem jqNModC_prime_mem_eFull : jqNModC K p ∈ eFull K p L₀ := by
  have h := jqNModC_mul_mem_eFull (K := K) p (d := 1) (one_dvd L₀)
  rwa [jqNModC_congr (Nat.mul_one p)] at h

omit hp in
/-- `Φ_p` at the seed `jqNModC K p` annihilates `jqModC K` (the symmetric form). -/
theorem phiAtSeed_jqNModC_prime_eval_jqModC [NeZero p] (data : ModularPolynomialData p)
    (hsymm : EvalSymm data.Φ) : (phiAtSeed data (jqNModC K p)).eval (jqModC K) = 0 := by
  have h := phiAtSeed_jqNModC_eval_symm (R := K) p data hsymm 1
  rwa [jqNModC_congr (Nat.one_mul p), jqNModC_one] at h

theorem isIntegral_jqModC_eFull : IsIntegral (eFull K p L₀) (jqModC K) := by
  obtain ⟨data, -, hsymm⟩ := ModularCurve.exists_phiIrreducible_evalSymm p
  exact isIntegral_of_phiAtSeed_root data (jqNModC_prime_mem_eFull L₀ p)
    (phiAtSeed_jqNModC_prime_eval_jqModC p data hsymm)

theorem natDegree_minpoly_jqModC_eFull_le : (minpoly (eFull K p L₀) (jqModC K)).natDegree ≤ p + 1 := by
  obtain ⟨data, -, hsymm⟩ := ModularCurve.exists_phiIrreducible_evalSymm p
  have h := natDegree_minpoly_le_dedekindPsi_of_phiAtSeed_root data
    (jqNModC_prime_mem_eFull (K := K) L₀ p)
    (phiAtSeed_jqNModC_prime_eval_jqModC (K := K) p data hsymm)
  rwa [ModularCurve.dedekindPsi_prime hp.out] at h

theorem natDegree_minpoly_jqModC_eFull_le_of_dvd (hpL : p ∣ L₀) :
    (minpoly (eFull K p L₀) (jqModC K)).natDegree ≤ p := by
  obtain ⟨data, -, hsymm⟩ := ModularCurve.exists_phiIrreducible_evalSymm p
  have hr : jqNModC K (p * p) ∈ eFull K p L₀ := jqNModC_mul_mem_eFull p hpL
  have hrroot : (phiAtSeed data (jqNModC K p)).eval (jqNModC K (p * p)) = 0 :=
    phiAtSeed_jqNModC_eval (R := K) p data p
  have hne : jqModC K ≠ jqNModC K (p * p) := by
    intro h
    have h1 : (1 : ℕ) = p * p := jqNModC_injective (by rw [jqNModC_one]; exact h)
    nlinarith [hp.out.two_le]
  have h := natDegree_minpoly_le_of_phiAtSeed_root_of_root_mem data
    (jqNModC_prime_mem_eFull (K := K) L₀ p) hr hrroot
    (phiAtSeed_jqNModC_prime_eval_jqModC (K := K) p data hsymm) hne
  rw [ModularCurve.dedekindPsi_prime hp.out] at h
  omega

/-- **The lower bound**: `p ≤ deg minpoly_{eFull K p L₀} (jqModC K)`. The `p`
elements `qTwist (ζ ^ b) (jqModC K)` (`b < p`) are fixed into `eFull`'s scalar
map by `qTwist_eq_self_of_mem_eFull`, hence `p` distinct roots of the pushed
minimal polynomial. -/
theorem le_natDegree_minpoly_jqModC_eFull (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p) :
    p ≤ (minpoly (eFull K p L₀) (jqModC K)).natDegree := by
  classical
  have hint : IsIntegral (eFull K p L₀) (jqModC K) := isIntegral_jqModC_eFull L₀ p
  have hζp : ζ ^ p = 1 := units_pow_eq_one_of_isPrimitiveRoot hζ
  have hroot : ∀ b : ℕ,
      Polynomial.aeval (qTwist (ζ ^ b) (jqModC K)) (minpoly (eFull K p L₀) (jqModC K)) = 0 := by
    intro b
    have hvb : (ζ ^ b) ^ p = 1 := by rw [← pow_mul, Nat.mul_comm, pow_mul, hζp, one_pow]
    have hfix : (qTwist (ζ ^ b)).comp (algebraMap (eFull K p L₀) (LaurentSeries K))
        = algebraMap (eFull K p L₀) (LaurentSeries K) := by
      refine RingHom.ext fun x => ?_
      rw [RingHom.comp_apply]
      exact qTwist_eq_self_of_mem_eFull p hvb x.2
    have h0 := minpoly.aeval (eFull K p L₀) (jqModC K)
    rw [Polynomial.aeval_def] at h0 ⊢
    have h1 := Polynomial.hom_eval₂ (minpoly (eFull K p L₀) (jqModC K))
      (algebraMap (eFull K p L₀) (LaurentSeries K)) (qTwist (ζ ^ b)) (jqModC K)
    rw [hfix, h0, map_zero] at h1
    exact h1.symm
  have hmne : (minpoly (eFull K p L₀) (jqModC K)).map (algebraMap (eFull K p L₀) (LaurentSeries K))
      ≠ 0 := ((minpoly.monic hint).map _).ne_zero
  have hmem : ∀ b : ℕ, qTwist (ζ ^ b) (jqModC K)
      ∈ ((minpoly (eFull K p L₀) (jqModC K)).map
          (algebraMap (eFull K p L₀) (LaurentSeries K))).roots.toFinset := by
    intro b
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hmne, Polynomial.IsRoot.def,
      Polynomial.eval_map_algebraMap]
    exact hroot b
  have hinj : Set.InjOn (fun b : ℕ => qTwist (ζ ^ b) (jqModC K)) ↑(Finset.range p) := by
    intro b hb b' hb' h
    rw [Finset.coe_range, Set.mem_Iio] at hb hb'
    have h0 : qTwist (ζ ^ b) (jqModC K) = qTwist (ζ ^ b') (jqModC K) := h
    rw [qTwist_jqModC_eq_TS, qTwist_jqModC_eq_TS] at h0
    have h2 : ζ ^ b = ζ ^ b' := (TS_injective h0).2
    have h3 : ((ζ : Kˣ) : K) ^ b = ((ζ : Kˣ) : K) ^ b' := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, h2]
    exact hζ.pow_inj hb hb' h3
  have hcard : ((Finset.range p).image (fun b : ℕ => qTwist (ζ ^ b) (jqModC K))).card = p := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hsub : (Finset.range p).image (fun b : ℕ => qTwist (ζ ^ b) (jqModC K))
      ⊆ ((minpoly (eFull K p L₀) (jqModC K)).map
          (algebraMap (eFull K p L₀) (LaurentSeries K))).roots.toFinset := by
    intro x hx
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hx
    exact hmem b
  calc p = ((Finset.range p).image (fun b : ℕ => qTwist (ζ ^ b) (jqModC K))).card := hcard.symm
    _ ≤ ((minpoly (eFull K p L₀) (jqModC K)).map
          (algebraMap (eFull K p L₀) (LaurentSeries K))).roots.toFinset.card :=
        Finset.card_le_card hsub
    _ ≤ ((minpoly (eFull K p L₀) (jqModC K)).map
          (algebraMap (eFull K p L₀) (LaurentSeries K))).roots.card :=
        Multiset.toFinset_card_le _
    _ ≤ ((minpoly (eFull K p L₀) (jqModC K)).map
          (algebraMap (eFull K p L₀) (LaurentSeries K))).natDegree :=
        Polynomial.card_roots' _
    _ = (minpoly (eFull K p L₀) (jqModC K)).natDegree := (minpoly.monic hint).natDegree_map _

/-- The relative degree of `fullC K (L₀ * p)` over `eFull K p L₀` is the degree of
`jqModC K`'s minimal polynomial there. -/
theorem relfinrank_eFull_fullC_eq_natDegree [NeZero L₀] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) (L₀ * p)) :
    IntermediateField.relfinrank (eFull K p L₀) (fullC K (L₀ * p))
      = (minpoly (eFull K p L₀) (jqModC K)).natDegree := by
  rw [fullC_mul_prime_eq_adjoin_insert_image L₀ p ζ hζ]
  exact relfinrank_eFull_insert_eq_natDegree p L₀ (isIntegral_jqModC_eFull L₀ p)

end eFullDegree

/-! ## 6. The prime-power step -/

/-- **The first prime-power degree step**: if `jqModC K ∈ F` and `jqNModC K p ∉ F`,
then `[F⟮jqNModC K p⟯ : F] = p + 1`. `Φ_p` at the seed `(jqModC K, ·)` is monic of
degree `p + 1`, `jqNModC K p` is a root, and it is irreducible because the `p + 1`
roots are cycled by `qTwistEquiv ζ` and the extra one is not in `F`'s range. -/
theorem finrank_adjoin_jqNModC_prime_of_not_mem' (F : IntermediateField K (LaurentSeries K))
    (hj : jqModC K ∈ F) (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p)
    (hpF : jqNModC K p ∉ F) :
    Module.finrank F (IntermediateField.adjoin F ({jqNModC K p} : Set (LaurentSeries K))) = p + 1 := by
  classical
  obtain ⟨data, -, -⟩ := ModularCurve.exists_phiIrreducible_evalSymm p
  have hζp : ζ ^ p = 1 := units_pow_eq_one_of_isPrimitiveRoot hζ
  have hrel : (phiAtSeed data (jqModC K)).eval (jqNModC K p) = 0 := by
    have h := phiAtSeed_jqNModC_eval (R := K) p data 1
    rwa [jqNModC_one, jqNModC_congr (Nat.one_mul p)] at h
  have hPmonic : (phiAtSeed data (⟨jqModC K, hj⟩ : F)).Monic := phiAtSeed_monic data _
  have hPdeg : (phiAtSeed data (⟨jqModC K, hj⟩ : F)).natDegree = p + 1 := by
    rw [phiAtSeed_natDegree, ModularCurve.dedekindPsi_prime hp.out]
  have hProot : Polynomial.aeval (jqNModC K p) (phiAtSeed data (⟨jqModC K, hj⟩ : F)) = 0 :=
    aeval_phiAtSeed_eq_zero data hj hrel
  have hα : IsIntegral F (jqNModC K p) := isIntegral_of_phiAtSeed_root data hj hrel
  have hseed : qExpand K p (jqModC K) = qExpand K (p * 1) (qTwist ((1 : Kˣ) ^ p) (jqModC K)) := by
    rw [one_pow, qTwist_one_apply]
    exact qExpand_congr (Nat.mul_one p).symm _
  have hspread : qExpand K p (jqNModC K p)
      = qExpand K (p * (p * 1)) (qTwist ((1 : Kˣ) ^ (p * p)) (jqModC K)) := by
    rw [one_pow, qTwist_one_apply, jqNModC, qExpand_qExpand]
    exact qExpand_congr (by ring) _
  have hirr : Irreducible (phiAtSeed data (⟨jqModC K, hj⟩ : F)) := by
    letI : Algebra F (LaurentSeries K) := ((qExpand K p).comp (algebraMap F (LaurentSeries K))).toAlgebra
    have halg : ∀ x : F, algebraMap F (LaurentSeries K) x = qExpand K p (x : LaurentSeries K) :=
      fun _ => rfl
    have hPmapL : (phiAtSeed data (⟨jqModC K, hj⟩ : F)).map (algebraMap F (LaurentSeries K))
        = phiAtSeed data (qExpand K (p * 1) (qTwist ((1 : Kˣ) ^ p) (jqModC K))) := by
      rw [← hseed]
      exact phiAtSeed_map data _ _
    have hPs : ((phiAtSeed data (⟨jqModC K, hj⟩ : F)).map (algebraMap F (LaurentSeries K))).Splits := by
      rw [hPmapL, phiAtSeed, ModularCurve.PhiGen.splits_prime_at_slot_of_isPrimitiveRoot p ζ hζ data 1 1]
      exact (Polynomial.Splits.X_sub_C _).mul (Polynomial.Splits.prod fun _ _ => Polynomial.Splits.X_sub_C _)
    have hroots : ((phiAtSeed data (⟨jqModC K, hj⟩ : F)).map (algebraMap F (LaurentSeries K))).roots
        = qExpand K (p * (p * 1)) (qTwist ((1 : Kˣ) ^ (p * p)) (jqModC K)) ::ₘ
            (Multiset.range p).map (fun b => qExpand K 1 (qTwist (1 * ζ ^ b) (jqModC K))) := by
      rw [hPmapL]
      exact roots_prime_at_slot_of_isPrimitiveRoot p ζ hζ data 1 1
    have hnodup : ((phiAtSeed data (⟨jqModC K, hj⟩ : F)).map
        (algebraMap F (LaurentSeries K))).roots.Nodup := by
      rw [hPmapL, phiAtSeed]
      exact roots_prime_at_slot_roots_nodup_of_isPrimitiveRoot p ζ hζ data 1 1
    have hσ : ∀ x : F, qTwistEquiv ζ (algebraMap F (LaurentSeries K) x) = algebraMap F (LaurentSeries K) x := by
      intro x
      rw [halg, qTwistEquiv_apply]
      exact qTwist_qExpand_of_pow_eq_one p ζ hζp _
    have hcycle : ∀ i < p, qTwistEquiv ζ (qExpand K 1 (qTwist (1 * ζ ^ i) (jqModC K)))
        = qExpand K 1 (qTwist (1 * ζ ^ ((i + 1) % p)) (jqModC K)) := by
      intro i _
      show qTwist ζ (TS K 1 (1 * ζ ^ i)) = TS K 1 (1 * ζ ^ ((i + 1) % p))
      rw [one_mul, one_mul]
      exact qTwist_TS_one_cycle ζ hζp i
    have hy₀ : qExpand K (p * (p * 1)) (qTwist ((1 : Kˣ) ^ (p * p)) (jqModC K))
        ∉ (algebraMap F (LaurentSeries K)).range := by
      rintro ⟨f, hf⟩
      rw [halg] at hf
      have h3 : (f : LaurentSeries K) = jqNModC K p := qExpand_injective p (hf.trans hspread.symm)
      exact hpF (h3 ▸ f.2)
    exact Polynomial.irreducible_of_transitive_ringAut _ hPmonic hPs (qTwistEquiv ζ) hσ _ _ p hroots hnodup
      hcycle hy₀
  have hmin : phiAtSeed data (⟨jqModC K, hj⟩ : F) = minpoly F (jqNModC K p) :=
    minpoly.eq_of_irreducible_of_monic hirr hProot hPmonic
  rw [IntermediateField.adjoin.finrank hα, ← hmin, hPdeg]

/-- **The `a = 0` step**: `[fullC K (M * p) : fullC K M] = p + 1`. The new generator is
`jqNModC K p`, whose minimal polynomial over `fullC K M` is `Φ_p` at `jqModC K`: monic
of degree `p + 1`, and irreducible because the extra root `jqNModC K p` is not in
`fullC K M`. -/
private lemma relfinrank_fullC_zero_step {M p : ℕ} [NeZero M] [hp : Fact (Nat.Prime p)]
    (hpM : ¬ p ∣ M) (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) (M * p ^ (0 + 1)))
    (hnm : jqNModC K p ∉ fullC K M) :
    IntermediateField.relfinrank (fullC K (M * p ^ 0)) (fullC K (M * p ^ (0 + 1))) = p + 1 := by
  classical
  obtain ⟨data, -, -⟩ := ModularCurve.exists_phiIrreducible_evalSymm p
  have hup := fullC_succ_eq_adjoin_insert_divSet M p 0 hpM ζ hζ
  have hs : jqNModC K (p ^ 0) ∈ fullC K (M * p ^ 0) := jqNModC_mem_fullC (dvd_mul_left _ _)
  have hup_rel : (phiAtSeed data (jqNModC K (p ^ 0))).eval (jqNModC K (p ^ (0 + 1))) = 0 := by
    have h := phiAtSeed_jqNModC_eval (R := K) p data (p ^ 0)
    rwa [jqNModC_congr (pow_succ p 0).symm] at h
  have hint : IsIntegral (fullC K (M * p ^ 0)) (jqNModC K (p ^ (0 + 1))) :=
    isIntegral_of_phiAtSeed_root data hs hup_rel
  rw [show IntermediateField.relfinrank (fullC K (M * p ^ 0)) (fullC K (M * p ^ (0 + 1)))
      = (minpoly (fullC K (M * p ^ 0)) (jqNModC K (p ^ (0 + 1)))).natDegree from by
    rw [hup]
    exact relfinrank_fullC_insert_eq_natDegree _ hint]
  have hF : fullC K (M * p ^ 0) = fullC K M := by rw [pow_zero, Nat.mul_one]
  have hpF : jqNModC K p ∉ fullC K (M * p ^ 0) := by
    rw [hF]
    exact hnm
  have hcongr : jqNModC K (p ^ (0 + 1)) = jqNModC K p := jqNModC_congr (by rw [zero_add, pow_one])
  rw [hcongr] at hint ⊢
  rw [← IntermediateField.adjoin.finrank hint]
  exact finrank_adjoin_jqNModC_prime_of_not_mem' _ (jqModC_mem_fullC _) p _
    (isPrimitiveRoot_pow_div hζ (Dvd.dvd.mul_left (dvd_pow_self p (Nat.succ_ne_zero 0)) M)) hpF

/-- **The `eFull` tower has the `fullC` degrees**: the induction hypothesis `hprev`,
transported along `eFull_eq_map` and `relfinrank_map_map`, gives the same relative
degree for the `eFull` tower — the two towers differ by the `qExpand`-image. -/
private lemma relfinrank_eFull_succ_eq {M p b : ℕ} [NeZero M] [Fact (Nat.Prime p)]
    (hprev : IntermediateField.relfinrank (fullC K (M * p ^ b)) (fullC K (M * p ^ (b + 1)))
      = if b = 0 then p + 1 else p) :
    IntermediateField.relfinrank (eFull K p (M * p ^ b)) (eFull K p (M * p ^ (b + 1)))
      = if b = 0 then p + 1 else p := by
  rw [eFull_eq_map, eFull_eq_map, IntermediateField.relfinrank_map_map]
  exact hprev

/-- **The `fullC` step is at most the `eFull` step**: `[fullC K (M p ^ (b + 1)) : eFull K p (M p ^ b)]`
is the degree of `jqModC K`'s minimal polynomial over `eFull K p (M p ^ b)`, which §5
bounds by `p + 1` at `b = 0` and by `p` as soon as `p ∣ M p ^ b`. -/
private lemma relfinrank_fullC_succ_le_eFull {M p b : ℕ} [NeZero M] [Fact (Nat.Prime p)]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) (M * p ^ b * p)) :
    IntermediateField.relfinrank (eFull K p (M * p ^ b)) (fullC K (M * p ^ (b + 1)))
      ≤ if b = 0 then p + 1 else p := by
  rw [show M * p ^ (b + 1) = M * p ^ b * p from by ring,
    relfinrank_eFull_fullC_eq_natDegree (M * p ^ b) p ζ hζ]
  split_ifs with hb
  · exact natDegree_minpoly_jqModC_eFull_le (M * p ^ b) p
  · exact natDegree_minpoly_jqModC_eFull_le_of_dvd (M * p ^ b) p
      (Dvd.dvd.mul_left (dvd_pow_self p hb) M)

/-- **The lower bound at the second step**: `p ≤ [fullC K (M p ^ (b + 2)) : eFull K p (M p ^ (b + 1))]` —
that degree is the degree of `jqModC K`'s minimal polynomial, and §5 exhibits `p`
distinct `qTwist`-conjugates of `jqModC K` as roots of it. -/
private lemma le_relfinrank_eFull_fullC_succ {M p b : ℕ} [NeZero M] [Fact (Nat.Prime p)]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) (M * p ^ (b + 1 + 1))) :
    p ≤ IntermediateField.relfinrank (eFull K p (M * p ^ (b + 1)))
      (fullC K (M * p ^ (b + 1 + 1))) := by
  have hL1 : M * p ^ (b + 1 + 1) = M * p ^ (b + 1) * p := by ring
  have hpL1 : p ∣ M * p ^ (b + 1 + 1) := Dvd.dvd.mul_left (dvd_pow_self p (Nat.succ_ne_zero _)) M
  have hζ1 : IsPrimitiveRoot (ζ : K) (M * p ^ (b + 1) * p) := by
    rw [← hL1]
    exact hζ
  rw [hL1, relfinrank_eFull_fullC_eq_natDegree (M * p ^ (b + 1)) p ζ hζ1]
  exact le_natDegree_minpoly_jqModC_eFull (M * p ^ (b + 1)) p _
    (isPrimitiveRoot_pow_div hζ hpL1)

/-- **The upper bound at the second step**: `[fullC K (M p ^ (b + 2)) : fullC K (M p ^ (b + 1))] ≤ p`:
`jqNModC K (p ^ (b + 2))` is a root of the level-`p` slot at the seed `jqNModC K (p ^ (b + 1))`,
and that slot already has the other root `jqNModC K (p ^ b)` in the base field, so the
`ψ(p) - 1` bound of §3 applies. -/
private lemma relfinrank_fullC_succ_le {M p b : ℕ} [NeZero M] [Fact (Nat.Prime p)]
    (hpM : ¬ p ∣ M) (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) (M * p ^ (b + 1 + 1))) :
    IntermediateField.relfinrank (fullC K (M * p ^ (b + 1))) (fullC K (M * p ^ (b + 1 + 1)))
      ≤ p := by
  classical
  obtain ⟨data, -, hsymm⟩ := ModularCurve.exists_phiIrreducible_evalSymm p
  have hup := fullC_succ_eq_adjoin_insert_divSet M p (b + 1) hpM ζ hζ
  have hs : jqNModC K (p ^ (b + 1)) ∈ fullC K (M * p ^ (b + 1)) :=
    jqNModC_mem_fullC (dvd_mul_left _ _)
  have hup_rel : (phiAtSeed data (jqNModC K (p ^ (b + 1)))).eval (jqNModC K (p ^ (b + 1 + 1))) = 0 := by
    have h := phiAtSeed_jqNModC_eval (R := K) p data (p ^ (b + 1))
    rwa [jqNModC_congr (pow_succ p (b + 1)).symm] at h
  have hint : IsIntegral (fullC K (M * p ^ (b + 1))) (jqNModC K (p ^ (b + 1 + 1))) :=
    isIntegral_of_phiAtSeed_root data hs hup_rel
  rw [show IntermediateField.relfinrank (fullC K (M * p ^ (b + 1)))
        (fullC K (M * p ^ (b + 1 + 1)))
      = (minpoly (fullC K (M * p ^ (b + 1))) (jqNModC K (p ^ (b + 1 + 1)))).natDegree from by
    rw [hup]
    exact relfinrank_fullC_insert_eq_natDegree _ hint]
  have hr : jqNModC K (p ^ b) ∈ fullC K (M * p ^ (b + 1)) :=
    jqNModC_mem_fullC (Dvd.dvd.mul_left (pow_dvd_pow p (Nat.le_succ b)) M)
  have hrroot : (phiAtSeed data (jqNModC K (p ^ (b + 1)))).eval (jqNModC K (p ^ b)) = 0 := by
    have h := phiAtSeed_jqNModC_eval_symm (R := K) p data hsymm (p ^ b)
    rwa [jqNModC_congr (pow_succ p b).symm] at h
  have htr : jqNModC K (p ^ (b + 1 + 1)) ≠ jqNModC K (p ^ b) := by
    intro h
    have h1 := Nat.pow_right_injective (Fact.out : Nat.Prime p).two_le (jqNModC_injective h)
    omega
  have h := natDegree_minpoly_le_of_phiAtSeed_root_of_root_mem data hs hr hrroot hup_rel htr
  rw [ModularCurve.dedekindPsi_prime (Fact.out : Nat.Prime p)] at h
  omega

/-- **The inclusions of the step's towers**: at `a = b + 1`, `eFull K p (M p ^ b)` sits in
`eFull K p (M p ^ (b + 1))`, both sit in `fullC K (M p ^ (b + 1))` and in
`fullC K (M p ^ (b + 2))`, and `fullC` is monotone in the index. -/
private lemma eFull_fullC_tower_inclusions {M p b : ℕ} [NeZero M] [Fact (Nat.Prime p)] :
    eFull K p (M * p ^ b) ≤ eFull K p (M * p ^ (b + 1)) ∧
      eFull K p (M * p ^ b) ≤ fullC K (M * p ^ (b + 1)) ∧
      eFull K p (M * p ^ (b + 1)) ≤ fullC K (M * p ^ (b + 1 + 1)) ∧
      fullC K (M * p ^ (b + 1)) ≤ fullC K (M * p ^ (b + 1 + 1)) := by
  have hL0 : M * p ^ (b + 1) = M * p ^ b * p := by ring
  have hL1 : M * p ^ (b + 1 + 1) = M * p ^ (b + 1) * p := by ring
  refine ⟨eFull_mono (K := K) p (mul_dvd_mul_left M (pow_dvd_pow p (Nat.le_succ b))), ?_, ?_, ?_⟩
  · rw [hL0]
    exact eFull_le_fullC (K := K) p _
  · rw [hL1]
    exact eFull_le_fullC (K := K) p _
  · exact fullC_mono (K := K) (mul_dvd_mul_left M (pow_dvd_pow p (Nat.le_succ _)))

/-- **The squeeze of the step**: with the `eFull` step `δ = [E_{b+1} : E_b]`, the two tower
identities `[E_b : F_{b+2}] = [E_b : F_{b+1}] * [F_{b+1} : F_{b+2}]` and
`[E_b : F_{b+2}] = [E_b : E_{b+1}] * [E_{b+1} : F_{b+2}]` squeeze `[F_{b+2} : F_{b+1}]`:
`p ≤ [F_{b+2} : F_{b+1}]` from the lower bound `p ≤ [F_{b+2} : E_{b+1}]`, and
`[F_{b+2} : F_{b+1}] ≤ p` from §3. -/
private lemma relfinrank_fullC_succ_eq_of_bounds {M p b δ : ℕ} [NeZero M] [Fact (Nat.Prime p)]
    (hδ : IntermediateField.relfinrank (eFull K p (M * p ^ b)) (eFull K p (M * p ^ (b + 1))) = δ)
    (hδpos : 0 < δ)
    (hx : IntermediateField.relfinrank (eFull K p (M * p ^ b)) (fullC K (M * p ^ (b + 1))) ≤ δ)
    (hy : p ≤ IntermediateField.relfinrank (eFull K p (M * p ^ (b + 1)))
      (fullC K (M * p ^ (b + 1 + 1))))
    (hdle : IntermediateField.relfinrank (fullC K (M * p ^ (b + 1)))
      (fullC K (M * p ^ (b + 1 + 1))) ≤ p) :
    IntermediateField.relfinrank (fullC K (M * p ^ (b + 1))) (fullC K (M * p ^ (b + 1 + 1)))
      = p := by
  obtain ⟨hGE, hG0, hE1, h01⟩ :
      eFull K p (M * p ^ b) ≤ eFull K p (M * p ^ (b + 1)) ∧
        eFull K p (M * p ^ b) ≤ fullC K (M * p ^ (b + 1)) ∧
        eFull K p (M * p ^ (b + 1)) ≤ fullC K (M * p ^ (b + 1 + 1)) ∧
        fullC K (M * p ^ (b + 1)) ≤ fullC K (M * p ^ (b + 1 + 1)) :=
    eFull_fullC_tower_inclusions (K := K) (M := M) (p := p) (b := b)
  have t1 : IntermediateField.relfinrank (eFull K p (M * p ^ b)) (fullC K (M * p ^ (b + 1)))
        * IntermediateField.relfinrank (fullC K (M * p ^ (b + 1)))
            (fullC K (M * p ^ (b + 1 + 1)))
      = IntermediateField.relfinrank (eFull K p (M * p ^ b)) (fullC K (M * p ^ (b + 1 + 1))) :=
    IntermediateField.relfinrank_mul_relfinrank hG0 h01
  have t2 : IntermediateField.relfinrank (eFull K p (M * p ^ b)) (eFull K p (M * p ^ (b + 1)))
        * IntermediateField.relfinrank (eFull K p (M * p ^ (b + 1)))
            (fullC K (M * p ^ (b + 1 + 1)))
      = IntermediateField.relfinrank (eFull K p (M * p ^ b)) (fullC K (M * p ^ (b + 1 + 1))) :=
    IntermediateField.relfinrank_mul_relfinrank hGE hE1
  have hsq : δ * p ≤ δ * IntermediateField.relfinrank (fullC K (M * p ^ (b + 1)))
      (fullC K (M * p ^ (b + 1 + 1))) := by
    calc δ * p
        = IntermediateField.relfinrank (eFull K p (M * p ^ b)) (eFull K p (M * p ^ (b + 1))) * p := by
          rw [hδ]
      _ ≤ IntermediateField.relfinrank (eFull K p (M * p ^ b)) (eFull K p (M * p ^ (b + 1)))
            * IntermediateField.relfinrank (eFull K p (M * p ^ (b + 1)))
                (fullC K (M * p ^ (b + 1 + 1))) := Nat.mul_le_mul le_rfl hy
      _ = IntermediateField.relfinrank (eFull K p (M * p ^ b)) (fullC K (M * p ^ (b + 1 + 1))) :=
          t2
      _ = IntermediateField.relfinrank (eFull K p (M * p ^ b)) (fullC K (M * p ^ (b + 1)))
            * IntermediateField.relfinrank (fullC K (M * p ^ (b + 1)))
                (fullC K (M * p ^ (b + 1 + 1))) := t1.symm
      _ ≤ δ * IntermediateField.relfinrank (fullC K (M * p ^ (b + 1)))
            (fullC K (M * p ^ (b + 1 + 1))) := Nat.mul_le_mul hx le_rfl
  exact le_antisymm hdle (Nat.le_of_mul_le_mul_left hsq hδpos)

/-- **The strong induction step**: `[fullC K (M p ^ (a+1)) : fullC K (M p ^ a)] = p + 1`
when `a = 0` and `p` otherwise, given the induction hypothesis `hprev` for the
`eFull` tower and the base non-membership `hnm`. -/
theorem relfinrank_fullC_step (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)] (a : ℕ)
    (hpM : ¬ p ∣ M) (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) (M * p ^ (a + 1)))
    (hprev : ∀ b : ℕ, a = b + 1 →
      IntermediateField.relfinrank (fullC K (M * p ^ b)) (fullC K (M * p ^ (b + 1)))
        = if b = 0 then p + 1 else p)
    (hnm : a = 0 → jqNModC K p ∉ fullC K M) :
    IntermediateField.relfinrank (fullC K (M * p ^ a)) (fullC K (M * p ^ (a + 1)))
      = if a = 0 then p + 1 else p := by
  classical
  rcases a with _ | b
  · rw [ite_eq_left rfl]
    exact relfinrank_fullC_zero_step hpM ζ hζ (hnm rfl)
  · rw [ite_eq_right (Nat.succ_ne_zero b)]
    have hL0 : M * p ^ (b + 1) = M * p ^ b * p := by ring
    have hL1 : M * p ^ (b + 1 + 1) = M * p ^ (b + 1) * p := by ring
    have hζ0 : IsPrimitiveRoot
        ((ζ ^ (M * p ^ (b + 1 + 1) / (M * p ^ b * p)) : Kˣ) : K) (M * p ^ b * p) :=
      isPrimitiveRoot_pow_div hζ (by rw [← hL0]; exact mul_dvd_mul_left M (pow_dvd_pow p (Nat.le_succ _)))
    have hδ : IntermediateField.relfinrank (eFull K p (M * p ^ b)) (eFull K p (M * p ^ (b + 1)))
        = if b = 0 then p + 1 else p := relfinrank_eFull_succ_eq (hprev b rfl)
    have hδpos : 0 < (if b = 0 then p + 1 else p) := by
      have hp0 : 0 < p := (Fact.out : Nat.Prime p).pos
      split_ifs <;> omega
    have hx : IntermediateField.relfinrank (eFull K p (M * p ^ b)) (fullC K (M * p ^ (b + 1)))
        ≤ if b = 0 then p + 1 else p :=
      relfinrank_fullC_succ_le_eFull (ζ ^ (M * p ^ (b + 1 + 1) / (M * p ^ b * p))) hζ0
    exact relfinrank_fullC_succ_eq_of_bounds hδ hδpos hx
      (le_relfinrank_eFull_fullC_succ (M := M) (p := p) (b := b) ζ hζ)
      (relfinrank_fullC_succ_le hpM ζ hζ)

/-- **The prime-power step of the divisor field over an arbitrary field.** For
`p ∤ M`, the relative degree of `F^fullC_{M p ^ (a+1)}` over `F^fullC_{M p ^ a}`
is `p + 1` at `a = 0` and `p` otherwise, where `F^fullC_L` is the intermediate
field of `LaurentSeries K` generated over `K` by the `jqNModC K d` with `d ∣ L`.
Verbatim from `Theorems/Thm_ModularCurve_relfinrank_fullC_mul_prime_pow.lean`. -/
theorem relfinrank_fullC_mul_prime_pow {K : Type*} [Field K] (M : ℕ) [NeZero M] (p : ℕ)
    [hp : Fact (Nat.Prime p)] (a : ℕ) (hpM : ¬ p ∣ M) (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) (M * p ^ (a + 1)))
    (hprev : ∀ b : ℕ, a = b + 1 → IntermediateField.relfinrank
        (IntermediateField.adjoin K {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'),
          d' ∣ M * p ^ b ∧ x = jqNModC K d'})
        (IntermediateField.adjoin K {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'),
          d' ∣ M * p ^ (b + 1) ∧ x = jqNModC K d'})
      = if b = 0 then p + 1 else p)
    (hnm : a = 0 → jqNModC K p ∉ IntermediateField.adjoin K
        {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ M ∧ x = jqNModC K d'}) :
    IntermediateField.relfinrank
      (IntermediateField.adjoin K {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'),
        d' ∣ M * p ^ a ∧ x = jqNModC K d'})
      (IntermediateField.adjoin K {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'),
        d' ∣ M * p ^ (a + 1) ∧ x = jqNModC K d'})
    = if a = 0 then p + 1 else p :=
  relfinrank_fullC_step M p a hpM ζ hζ hprev hnm

/-! ## 7. The socket assembly

The pin's `S_ModularCurve_package_of_socket.lean` proves `Pkg K M` — the `hall`
statement of the `C`-layer engines — by strong induction over the divisors of
`M`. The induction peels a prime `q = m.minFac` off a divisor `d = e * q`, gets
`jqNModC K (e * q') ∈ modularFunctionFieldC K d` from the prime step `hKG1`
(applied at the smaller level `e * q'`), rewrites the level-`e q'` field as the
divisor field `fullC` by the induction hypothesis, and finishes with the
`fullC_mono` inclusion.

The degree half then reads `tight_iff_relfinrank_fullC` backwards: at `d = 1`
it is `dedekindPsi_one`; at `d = M * p ^ (a + 1)` it is the product of the
induction hypothesis, the `(p + 1) · p ^ a` tower of §6, and `ψ`'s multiplicativity
across coprime factors.

`Pkg` itself is `Defs/JqCoeff.lean`'s `abbrev`, not a local definition: the
`abbrev` is what lets the induction hand `Pkg`-typed data to `hKG1` and still
apply it as the conjunction it is. The four `congr`/`containment` helpers below
are `private` in the pin and stay so here. -/

/-- Level-index congruence for `modularFunctionFieldC`. -/
private theorem mffC_congr {n m : ℕ} [NeZero n] [NeZero m] (h : n = m) :
    modularFunctionFieldC K n = modularFunctionFieldC K m := by
  subst h; rfl

/-- Level-index congruence for `fullC`. -/
private theorem fullC_congr' {n m : ℕ} (h : n = m) : fullC K n = fullC K m := by
  subst h; rfl

/-- The base field `K⟮j(q)⟯` sits in every divisor field. -/
private theorem adjoin_jqModC_le_fullC (M : ℕ) :
    IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)) ≤ fullC K M :=
  IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (jqModC_mem_fullC M))

/-- At the level `1` the divisor field is the base field (the only divisor of `1`
is `1`, and `j(q ^ 1) = j(q)`). -/
private theorem fullC_one : fullC K 1 = IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)) := by
  refine le_antisymm ?_ (adjoin_jqModC_le_fullC 1)
  rw [fullC_le_iff]
  intro e _ he
  rw [Nat.dvd_one] at he
  subst he
  rw [jqNModC_one]
  exact IntermediateField.subset_adjoin K _ rfl

/-- **The degree half of `Pkg` agrees with the relative degree of `fullC`**, when
the level field is the divisor field. The statement `Pkg` carries is the
`Module.finrank` of the one-generator extension over `K⟮j(q)⟯`; this is the same
number read as a `relfinrank` of `fullC K m`. -/
theorem tight_iff_relfinrank_fullC (m : ℕ) [NeZero m] (hgen : modularFunctionFieldC K m = fullC K m) :
    (Module.finrank (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
        (IntermediateField.adjoin (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
          ({jqNModC K m} : Set (LaurentSeries K))) = dedekindPsi m)
      ↔ IntermediateField.relfinrank (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (fullC K m)
          = dedekindPsi m := by
  rw [← hgen, modularFunctionFieldC, Set.pair_comm, relfinrank_adjoin_insert]

/-- **The level field is the divisor field, one prime at a time.** If adding any
prime `q` with `M q = d` keeps `j(q ^ M)` inside the level-`d` field (`hstep`),
and every proper divisor's level field is its divisor field (`hgen'`), then the
level-`d` field is the divisor field. The two hypotheses are the induction's
interface: `hstep` is what the prime-step engine supplies, `hgen'` the induction
hypothesis at the smaller level `e * q'`. -/
theorem mffC_eq_fullC_of_steps (d : ℕ) [NeZero d]
    (hstep : ∀ (M : ℕ) [NeZero M] (q : ℕ), q.Prime → M * q = d → jqNModC K M ∈ modularFunctionFieldC K d)
    (hgen' : ∀ (M : ℕ) [NeZero M] (q : ℕ), q.Prime → M * q = d → modularFunctionFieldC K M = fullC K M) :
    modularFunctionFieldC K d = fullC K d := by
  refine le_antisymm ?_ ?_
  · rw [modularFunctionFieldC, IntermediateField.adjoin_le_iff]
    rintro _ (rfl | rfl)
    · exact jqModC_mem_fullC d
    · exact jqNModC_mem_fullC dvd_rfl
  · rw [fullC_le_iff]
    intro e _ heD
    rcases eq_or_ne e d with rfl | hne
    · exact jqNModC_mem K _
    · obtain ⟨m, hm⟩ := heD
      have hm1 : m ≠ 1 := fun h1 => hne (by rw [hm, h1, Nat.mul_one])
      have hm0 : m ≠ 0 := fun h0 => NeZero.ne d (by rw [hm, h0, Nat.mul_zero])
      have hq : m.minFac.Prime := Nat.minFac_prime hm1
      obtain ⟨m', hm'⟩ := (Nat.minFac_dvd m : m.minFac ∣ m)
      have hm'0 : m' ≠ 0 := fun h0 => hm0 (by rw [hm', h0, Nat.mul_zero])
      haveI : NeZero (e * m') := ⟨Nat.mul_ne_zero (NeZero.ne e) hm'0⟩
      have hprod : e * m' * m.minFac = d := by
        rw [Nat.mul_assoc, Nat.mul_comm m' m.minFac, ← hm', ← hm]
      have hmemM : jqNModC K (e * m') ∈ modularFunctionFieldC K d := hstep (e * m') m.minFac hq hprod
      have hfull : modularFunctionFieldC K (e * m') = fullC K (e * m') := hgen' (e * m') m.minFac hq hprod
      have hle : modularFunctionFieldC K (e * m') ≤ modularFunctionFieldC K d := by
        rw [modularFunctionFieldC, IntermediateField.adjoin_le_iff]
        rintro _ (rfl | rfl)
        · exact jqModC_mem K d
        · exact hmemM
      refine hle ?_
      rw [hfull]
      exact jqNModC_mem_fullC (dvd_mul_right e m')

/-- **The `(p + 1) · p ^ a` tower**: for `p ∤ M` and a primitive `M p ^ (a+1)`-th
root `ξ`, the relative degree of `fullC K (M p ^ (a+1))` over `fullC K M` is
`(p + 1) * p ^ a`, given that `j(q ^ p)` is still outside `fullC K M`. The proof
multiplies the step function `[F_{i+1} : F_i]` (`p + 1` at `i = 0`, `p`
afterwards, §6) over the `a + 1` steps by `relfinrank_mul_relfinrank`. -/
theorem relfinrank_fullC_prime_pow_tower (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)] (a : ℕ) (hpM : ¬ p ∣ M)
    (ξ : Kˣ) (hξ : IsPrimitiveRoot (ξ : K) (M * p ^ (a + 1))) (hnm : jqNModC K p ∉ fullC K M) :
    IntermediateField.relfinrank (fullC K M) (fullC K (M * p ^ (a + 1))) = (p + 1) * p ^ a := by
  have hstep : ∀ i, i ≤ a →
      IntermediateField.relfinrank (fullC K (M * p ^ i)) (fullC K (M * p ^ (i + 1))) = if i = 0 then p + 1 else p := by
    intro i
    induction i with
    | zero =>
      intro _
      have hξ0 : IsPrimitiveRoot ((ξ ^ (M * p ^ (a + 1) / (M * p ^ (0 + 1))) : Kˣ) : K) (M * p ^ (0 + 1)) :=
        isPrimitiveRoot_pow_div hξ (mul_dvd_mul_left M (pow_dvd_pow p (by omega)))
      have h := ModularCurve.relfinrank_fullC_mul_prime_pow M p 0 hpM _ hξ0
        (fun b hb => absurd hb (Nat.succ_ne_zero b).symm) (fun _ => hnm)
      exact h
    | succ i ihi =>
      intro hi
      have hξi : IsPrimitiveRoot ((ξ ^ (M * p ^ (a + 1) / (M * p ^ (i + 1 + 1))) : Kˣ) : K) (M * p ^ (i + 1 + 1)) :=
        isPrimitiveRoot_pow_div hξ (mul_dvd_mul_left M (pow_dvd_pow p (by omega)))
      have h := ModularCurve.relfinrank_fullC_mul_prime_pow M p (i + 1) hpM _ hξi
        (fun b hb => by
          obtain rfl : b = i := by omega
          exact ihi (by omega))
        (fun h0 => absurd h0 (Nat.succ_ne_zero i))
      exact h
  have hprod : ∀ i, i ≤ a →
      IntermediateField.relfinrank (fullC K M) (fullC K (M * p ^ (i + 1))) = (p + 1) * p ^ i := by
    intro i
    induction i with
    | zero =>
      intro _
      have h0 := hstep 0 (Nat.zero_le a)
      rw [ite_eq_left rfl, fullC_congr' (show M * p ^ 0 = M by rw [pow_zero, Nat.mul_one])] at h0
      rw [h0, pow_zero, Nat.mul_one]
    | succ i ihi =>
      intro hi
      have h1 := hstep (i + 1) hi
      rw [ite_eq_right (Nat.succ_ne_zero i)] at h1
      have hle1 : fullC K M ≤ fullC K (M * p ^ (i + 1)) := fullC_mono (Dvd.intro _ rfl)
      have hle2 : fullC K (M * p ^ (i + 1)) ≤ fullC K (M * p ^ (i + 1 + 1)) :=
        fullC_mono (mul_dvd_mul_left M (pow_dvd_pow p (Nat.le_succ _)))
      rw [← IntermediateField.relfinrank_mul_relfinrank hle1 hle2, ihi (Nat.le_of_succ_le hi), h1, pow_succ,
        Nat.mul_assoc]
  exact hprod a le_rfl

/-- **The socket**: `Pkg K L` follows from the prime step. `hbase` says no prime
`p ∣ L` already has `j(q ^ p)` in the base field `K⟮j(q)⟯`; `hKG1` is the prime
step (JQ2), stated for an arbitrary `Pkg`-carrying level. The proof is the strong
induction over the divisors, with `hKG1` at `e * q'` and the `(p + 1) · p ^ a`
tower for the degree. -/
theorem pkg_of_socket (L : ℕ) [NeZero L] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) L)
    (hbase : ∀ (p : ℕ) [Fact (Nat.Prime p)], p ∣ L →
      jqNModC K p ∉ IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
    (hKG1 : ∀ (M : ℕ) [NeZero M] (q : ℕ) [Fact (Nat.Prime q)] (ξ : Kˣ), IsPrimitiveRoot (ξ : K) (M * q) → Pkg K M →
      jqNModC K M ∈ modularFunctionFieldC K (M * q)) :
    Pkg K L := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hdL hd0
    have hLpos : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)

    have pkg_lt : ∀ m : ℕ, m < d → m ∣ L → Pkg K m := fun m hm hmL e he _ =>
      ih e (lt_of_le_of_lt (Nat.le_of_dvd (Nat.pos_of_dvd_of_pos hmL hLpos) he) hm) (he.trans hmL)
    have hζd : IsPrimitiveRoot ((ζ ^ (L / d) : Kˣ) : K) d := isPrimitiveRoot_pow_div hζ hdL

    have hgen : modularFunctionFieldC K d = fullC K d := by
      refine mffC_eq_fullC_of_steps d ?_ ?_
      · intro M _ q hq hMq
        haveI : Fact (Nat.Prime q) := ⟨hq⟩
        have hMd : M < d := by
          rw [← hMq]
          exact lt_mul_of_one_lt_right (Nat.pos_of_ne_zero (NeZero.ne M)) hq.one_lt
        have hML : M ∣ L := (Dvd.intro q hMq).trans hdL
        have hξ : IsPrimitiveRoot ((ζ ^ (L / d) : Kˣ) : K) (M * q) := by
          rw [hMq]
          exact hζd
        have h := hKG1 M q _ hξ (pkg_lt M hMd hML)
        rwa [mffC_congr hMq] at h
      · intro M _ q hq hMq
        have hMd : M < d := by
          rw [← hMq]
          exact lt_mul_of_one_lt_right (Nat.pos_of_ne_zero (NeZero.ne M)) hq.one_lt
        have hML : M ∣ L := (Dvd.intro q hMq).trans hdL
        exact (pkg_lt M hMd hML M dvd_rfl).2

    refine ⟨?_, hgen⟩
    rw [tight_iff_relfinrank_fullC d hgen]
    rcases eq_or_ne d 1 with rfl | hd1
    · rw [fullC_one, IntermediateField.relfinrank_self, dedekindPsi_one]
    · obtain ⟨p, hp, hpd⟩ : ∃ p : ℕ, p.Prime ∧ p ∣ d := ⟨d.minFac, Nat.minFac_prime hd1, Nat.minFac_dvd d⟩
      haveI : Fact (Nat.Prime p) := ⟨hp⟩
      obtain ⟨e, M, hpM, hdeM⟩ := Nat.exists_eq_pow_mul_and_not_dvd (NeZero.ne d) p hp.ne_one
      have hM0 : M ≠ 0 := fun h0 => NeZero.ne d (by rw [hdeM, h0, Nat.mul_zero])
      haveI : NeZero M := ⟨hM0⟩
      obtain ⟨a, rfl⟩ : ∃ a, e = a + 1 := by
        rcases e with _ | a
        · exfalso
          rw [pow_zero, one_mul] at hdeM
          exact hpM (hdeM ▸ hpd)
        · exact ⟨a, rfl⟩
      have hd' : d = M * p ^ (a + 1) := by rw [hdeM, Nat.mul_comm]
      subst hd'
      have hMd : M < M * p ^ (a + 1) :=
        lt_mul_of_one_lt_right (Nat.pos_of_ne_zero hM0) (Nat.one_lt_pow (Nat.succ_ne_zero a) hp.one_lt)
      have hML : M ∣ L := (Dvd.intro (p ^ (a + 1)) rfl).trans hdL
      have pkgM : Pkg K M := pkg_lt M hMd hML
      obtain ⟨htM, hgM⟩ := pkgM M dvd_rfl
      have hpL : p ∣ L := hpd.trans hdL
      have hξp : IsPrimitiveRoot (((ζ ^ (L / (M * p ^ (a + 1)))) ^ (M * p ^ (a + 1) / (M * p)) : Kˣ) : K) (M * p) :=
        isPrimitiveRoot_pow_div hζd (mul_dvd_mul_left M (dvd_pow_self p (Nat.succ_ne_zero a)))
      have hnm : jqNModC K p ∉ fullC K M :=
        ModularCurve.jqNModC_prime_not_mem_fullC M p hpM _ hξp pkgM (hbase p hpL)
      have htower := relfinrank_fullC_prime_pow_tower M p a hpM _ hζd hnm
      have hM : IntermediateField.relfinrank (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (fullC K M)
          = dedekindPsi M :=
        (tight_iff_relfinrank_fullC M hgM).mp htM
      have hcop : Nat.Coprime M (p ^ (a + 1)) := hp.coprime_pow_of_not_dvd hpM
      rw [← IntermediateField.relfinrank_mul_relfinrank (adjoin_jqModC_le_fullC M) (fullC_mono (Dvd.intro (p ^ (a + 1)) rfl)), htower,
        hM, ModularCurve.dedekindPsi_mul_of_coprime M (p ^ (a + 1)) hcop,
        ModularCurve.dedekindPsi_prime_pow p (a + 1) hp (Nat.succ_ne_zero a), Nat.add_sub_cancel]
      ring

/-- **The socket headline**: for a level `M` with a primitive `M`-th root `ζ` and
no prime `p ∣ M` already at the base field, the whole `hall` package holds at
`M`. The prime step `hKG1` of `pkg_of_socket` is discharged here by JQ2's
`jqNModC_mem_modularFunctionFieldC_mul_prime`, so the statement has no
hypothesis beyond the level data. Verbatim from
`Theorems/Thm_ModularCurve_package_of_socket.lean:9` (the pin's own copy at
`S_:975` is `private` and byte-identical; ported once). -/
theorem package_of_socket {K : Type*} [Field K] (M : ℕ) [NeZero M] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) M)
    (hbase : ∀ (p : ℕ) [Fact (Nat.Prime p)], p ∣ M →
      jqNModC K p ∉ IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) :
    ∀ d : ℕ, d ∣ M → ∀ [NeZero d],
      Module.finrank (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
          (IntermediateField.adjoin (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
            ({jqNModC K d} : Set (LaurentSeries K))) = dedekindPsi d
        ∧ modularFunctionFieldC K d = IntermediateField.adjoin K
            {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ d ∧ x = jqNModC K d'} :=
  pkg_of_socket M ζ hζ hbase fun (M' : ℕ) [NeZero M'] (q : ℕ) [Fact (Nat.Prime q)] (ξ : Kˣ) hξ hall =>
    ModularCurve.jqNModC_mem_modularFunctionFieldC_mul_prime M' q ξ hξ hall

end ModularCurve

end
