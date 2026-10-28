/-
  The StarBank: the star action on the `j`-series (`StarBank.press`) and `Δ` in
  characteristic `p` (`StarBank.delta_pow_ne`, §`Δ` in characteristic `p` below).

  ## The star action on the `j`-series: `StarBank.press`

  The diamond/star action of the `p`-th cyclotomic twist on `j(q)`: if a
  polynomial `R` over a field `K` satisfies `aeval (jqModC K) R = jqNModC K p`,
  then `R` is monic of degree `p` and, after extending scalars to the Laurent
  series,

    `R.map (algebraMap K (LaurentSeries K)) - C (jqNModC K p)`
      `= ∏ b ∈ range p, (X - C (qTwist (ζ ^ b) (jqModC K)))`.

  The proof compares the two sides at the `p` distinct values
  `qTwist (ζ ^ b) (jqModC K)` and invokes mathlib's
  `Polynomial.eq_of_natDegree_lt_card_of_eval_eq`.

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  `P2M/Sol/S_ModularCurve_StarBank_press.lean` (209 lines). The public statement is
  the `Theorems/` wrapper verbatim. **Recorded deviation:** the pin's two
  anonymous `example` probes (its lines 191–197) are regression checks of
  *imported* lemmas — `IsPrimitiveRoot.pow_inj` and `qTwist_one_apply` — not of
  this node's mathematics; they carry no consumer, and transcribing them would
  pull in `Mathlib.Tactic.Omega` for seven lines of non-mathematics, so they are
  dropped (playbook §2.3 residue, §3.1 "no self-consumed lemmas"). They elaborate
  unchanged in the port under this module's imports, so nothing is lost by it.

  ## Reuse

  `press` reads only `Degree/JqCyclotomicConjugates.lean`, the one home for the
  conjugates' structure: `monic_of_aeval_eq`, `natDegree_eq_of_aeval_eq`,
  `qTwist_pow_jqModC_injective` and `aeval_qTwist_jqModC_eq_of_aeval_eq` are
  public there at the pin's names and binders, together with the whole
  `coeff_jqNModC_*` / `qTwist_*` forcing block the pin re-derives `private` in
  every solution file that uses it. The fourteen `private` copies that used to
  live in this module are gone; `qTwist_qExpand_of_pow_eq_one` is public in
  `Defs/KatzLevelPCusps.lean`, which that module imports. The pin-imported
  `coeff_jqModC_*` trio is three pin headlines and lives, public, in
  `Defs/JqCoeff.lean` (the pole at the cusp), also reached through it.

  ## Assumptions

  `Defs/Jq`'s `jNum`/`constantCoeff_jNum`/`ofPowerSeries_coeff_of_neg`;
  `Defs/JqCoeff`'s `jqModC`/`jqNModC`/`jqModC_pow`/`coeff_jqModC_pow_self`/
  `coeff_jqModC_pow_of_lt`/`coeff_jqModC_neg_one`; `Defs/Laurent`'s `qExpand`/
  `qExpand_coeff_mul`/`qExpand_coeff_of_not_dvd`/`algebraMap_laurentSeries_eq_single`;
  `Defs/Twist`'s `qTwist`/`qTwist_coeff`/`qTwist_single`/`qTwist_one_apply`/
  `qTwist_qExpand`; mathlib's `Polynomial.eq_of_natDegree_lt_card_of_eval_eq`.

  spec-pin: P2M/Sol/S_ModularCurve_StarBank_press.lean
  spec-pin: Theorems/Thm_ModularCurve_StarBank_press.lean

  ## `Δ` in characteristic `p`

  The second node here is `StarBank.delta_pow_ne`: for a commutative ring `K` of
  characteristic `ℓ` and a prime `p ≠ ℓ`, the `p`-th power of `Δ = q · η ^ 24`
  (as a Laurent series) is not `C γ · qExpand K p Δ`, for any `γ : K`.

  One coefficient comparison proves it. Write `24 = ℓ ^ c · m` with `ℓ ∤ m` (the
  `ℓ`-part of `24`, i.e. `c = 0` unless `ℓ ∈ {2, 3}`). In characteristic `ℓ` the
  `ℓ ^ c`-th power is `qExpand K (ℓ ^ c)` — the CL4 node
  `map_intCast_pow_char_eq_qExpand`, iterated through the exponents (this is the
  pin's `etaC_pow_char_pow`). So the left side's coefficient at `ℓ ^ c` is that of
  `𝓔 ^ (m · p)` at `1`, where `𝓔 = η(q) = 1 - q - ⋯`, and it is the linear term of
  a power: `(𝓔 ^ N).coeff 1 = -(N : K)` (the pin's `coeff_one_etaC_pow`). The right
  side's coefficient at `ℓ ^ c` vanishes, because `qExpand K p` is supported on the
  multiples of `p` and `p ∤ ℓ ^ c` for `p ≠ ℓ` prime. So `-(m p) = 0` in `K`, which
  forces `ℓ ∣ m` or `ℓ = p`, both excluded — and `(p : K) ≠ 0` is exactly the
  hypothesis the pin carries as `hp`.

  ## Source (`delta_pow_ne`)

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  `P2M/Sol/S_ModularCurve_StarBank_delta_pow_ne.lean` (254 lines), with the
  statement authority of `Theorems/Thm_ModularCurve_StarBank_delta_pow_ne.lean`.
  The pin declares `delta_pow_ne` `private` in its `S_` file and restates it in the
  public `Thm_` wrapper (whose statement the port takes); the port states it once,
  public, at the wrapper's name. `etaProd_pow_ne` is public in the pin's `S_` file
  (the same inequality with `Δ` replaced by `𝓔 ^{24 p}`, which is where the
  coefficient argument happens) and stays public here.

  ## Reuse (`delta_pow_ne`)

  The pin's `W1` prelude (its lines 22–123) is transcribed only where it is this
  node's own mathematics:

  * `coeff_one_mul` is mathlib's `PowerSeries.coeff_one_mul` (the same statement
    with the product commuted) — dropped.
  * `coeff_one_pow_of_shape` is mathlib's `PowerSeries.coeff_one_pow` — dropped.
  * `constantCoeff_etaProd` is the port's, public, in `Defs/Jq.lean`; the pin's
    `constantCoeff_etaProd_map` and `coeff_one_etaProd_map` are the two coefficient
    maps of that fact and are inlined in `coeff_one_etaC_pow`.
  * `coeff_one_etaProd` (`η`'s linear coefficient `-1`) is transcribed from the
    pin, topological-product proof included: it needs only mathlib's
    `PowerSeries.WithPiTopology.multipliable_one_sub_X_pow` and the continuity of
    `PowerSeries.coeff`, both already in the cone. (The port's other route to the
    same coefficient — mathlib's pentagonal number theorem, which
    `ModularCurve/JqCoefficients.lean` uses for its `private` `coeff_etaProd_one` —
    needs `Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries`, outside this
    work order's single-import budget.) The port holds that same fact `private`
    there, for `jNum`'s low coefficients; the natural public home is `Defs/Jq.lean`,
    beside `constantCoeff_etaProd`, which this work order does not touch, so the
    copy here is `private` as well.
  * `ofPowerSeries_map` — the naturality of `HahnSeries.ofPowerSeries` in the
    coefficient ring — is the port's `ModularCurve.map_ofPowerSeries`
    (`ModularCurve/JqIntegralRatios.lean`, public; `coeffMap_ofPowerSeries` is the
    same statement in `coeffMap` spelling), reached through
    `Defs/QExpandCharP` → `Frobenius/Defs.lean`. Used, not restated.
  * `map_intCast_pow_char_eq_qExpand` is the CL4 node (`Defs/QExpandCharP.lean`).
    Used, not restated. The pin's general `map_intCast_pow_char_pow_eq_qExpand`
    (any integral Laurent series, iterated through `ℓ ^ c`) has exactly one
    consumer, the `𝓔`-instantiation; the port proves that instantiation directly
    (`etaC_pow_char_pow`, by the same iteration) and does not carry the general
    form.
  * The pin's `etaC_pow_char` (the `c = 1` case of `etaC_pow_char_pow`) has no
    consumer in the node — dropped.
  * The pin's `section Falsifier` (four anonymous `example`s, its lines 209–240)
    probes the boundary cases `p = ℓ` and `p = 1`; anonymous, node-local, consumed
    by nothing — dropped (the decision this module already records for
    `StarBank.press`'s probes).

  The four lemmas that remain are `private`: each has exactly one consumer, this
  node's proof, and each adapts another module's mathematics to this node's carrier
  (`η`'s coefficients from `Defs/Jq`, the `𝓔`-form of the Frobenius from
  `Defs/QExpandCharP`) rather than stating mathematics of its own. Their natural
  public homes — `Defs/Jq.lean` beside `constantCoeff_etaProd`, and
  `Defs/QExpandCharP.lean` — are outside this work order's single-module edit
  surface; the pin's own homes for them (`ModularCurve.W1.coeff_one_etaProd`,
  `ModularCurve.W1.etaC_pow_char{,_pow}`) are generated `p2m_` scaffolding.

  ## Assumptions (`delta_pow_ne`)

  `Defs/Jq`'s `etaProd`/`constantCoeff_etaProd`; `Defs/Laurent`'s `qExpand`/
  `qExpand_coeff_mul`/`qExpand_coeff_of_not_dvd`/`qExpand_single`/
  `qExpand_congr`/`qExpand_qExpand`/`qExpand_one_apply`; `Defs/QExpandCharP`'s
  `map_intCast_pow_char_eq_qExpand`; `JqIntegralRatios`'s `map_ofPowerSeries`;
  mathlib's `PowerSeries.coeff_one_pow`,
  `PowerSeries.WithPiTopology.multipliable_one_sub_X_pow` and
  `PowerSeries.WithPiTopology.continuous_coeff` (the topological product's
  truncations), `HahnSeries.ofPowerSeries_apply_coeff`, `HahnSeries.single_pow`,
  `HahnSeries.C_mul_eq_smul`, `Nat.exists_eq_pow_mul_and_not_dvd`,
  `Nat.dvd_prime_pow`, `Nat.prime_dvd_prime_iff_eq`, `CharP.cast_eq_zero_iff`.

  spec-pin: Theorems/Thm_ModularCurve_StarBank_delta_pow_ne.lean
  spec-pin: P2M/Sol/S_ModularCurve_StarBank_delta_pow_ne.lean
-/
import FLTForHuman.ModularCurve.Defs.QExpandCharP
import FLTForHuman.ModularCurve.Degree.JqCyclotomicConjugates
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

set_option autoImplicit false

noncomputable section

open Polynomial HahnSeries Finset

namespace ModularCurve

namespace StarBank

/-- The star action: `R` is the minimal-degree annihilator of `jqModC K` at
`jqNModC K p`, so it is monic of degree `p` and the scalar-extended
`R - C (jqNModC K p)` factors over the `p` distinct twists of `jqModC K`.
Verbatim from the pin wrapper `Theorems/Thm_ModularCurve_StarBank_press.lean`. -/
theorem press {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) p) {R : Polynomial K}
    (hR : Polynomial.aeval (jqModC K) R = jqNModC K p) :
    R.Monic ∧ R.natDegree = p ∧
      R.map (algebraMap K (LaurentSeries K)) - Polynomial.C (jqNModC K p) =
        ∏ b ∈ Finset.range p, (Polynomial.X - Polynomial.C (qTwist (ζ ^ b) (jqModC K))) := by
  have hp : Fact p.Prime := inferInstance
  refine ⟨monic_of_aeval_eq hR, natDegree_eq_of_aeval_eq hR, ?_⟩

  set A : Polynomial (LaurentSeries K) := R.map (algebraMap K (LaurentSeries K)) with hA
  set B : Polynomial (LaurentSeries K) :=
    ∏ b : Fin p, (Polynomial.X - Polynomial.C (qTwist (ζ ^ (b : ℕ)) (jqModC K))) with hB
  have hAmonic : A.Monic := (monic_of_aeval_eq hR).map _
  have hAdeg : A.natDegree = p := by
    rw [hA, (monic_of_aeval_eq hR).natDegree_map, natDegree_eq_of_aeval_eq hR]
  have hBmonic : B.Monic :=
    Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _
  have hBdeg : B.natDegree = p := by
    rw [hB, Polynomial.natDegree_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _]
    simp
  have key : A - B = Polynomial.C (jqNModC K p) := by
    refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _
      (qTwist_pow_jqModC_injective hζ) (fun b => ?_) ?_
    · have hAev : A.eval (qTwist (ζ ^ (b : ℕ)) (jqModC K)) = jqNModC K p := by
        rw [hA, Polynomial.eval_map_algebraMap]
        exact aeval_qTwist_jqModC_eq_of_aeval_eq hζ hR b
      have hBev : B.eval (qTwist (ζ ^ (b : ℕ)) (jqModC K)) = 0 := by
        rw [hB, Polynomial.eval_prod]
        exact Finset.prod_eq_zero (Finset.mem_univ b) (by simp)
      simp only [Polynomial.eval_sub, Polynomial.eval_C, hAev, hBev, sub_zero]
    · rw [Fintype.card_fin]
      refine max_lt ?_ (by rw [Polynomial.natDegree_C]; exact hp.out.pos)
      by_cases hAB : A = B
      · rw [hAB, sub_self, Polynomial.natDegree_zero]; exact hp.out.pos
      · refine lt_of_lt_of_eq (Polynomial.natDegree_lt_natDegree (sub_ne_zero.mpr hAB) ?_) hAdeg
        exact Polynomial.degree_sub_lt_left
          (by rw [Polynomial.degree_eq_natDegree hAmonic.ne_zero,
            Polynomial.degree_eq_natDegree hBmonic.ne_zero, hAdeg, hBdeg])
          hAmonic.ne_zero (by rw [hAmonic.leadingCoeff, hBmonic.leadingCoeff])

  have hconcl : A - Polynomial.C (jqNModC K p) = B := by
    rw [← key]; ring
  rw [hconcl, hB, Finset.prod_range]

/-! ## `Δ` in characteristic `p`

`η(q) = Δ(q)^{1/24}` as a Laurent series: the same integral `q`-expansion, scalars
extended from `ℤ`. The four `private` lemmas below are the pin's `W1` prelude,
reduced to what this node's argument actually needs — the module header records
which declarations of that prelude the port drops (four of them, plus the pin's
anonymous falsifier probes) and which it reuses from existing homes. -/

section DeltaPowNe

open scoped PowerSeries.WithPiTopology

local notation "𝓔[" K "]" =>
  HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd)

/-- The linear coefficient of `η`: `η = 1 - q - q ^ 2 - ⋯`. Transcribed from the
pin's `W1.coeff_one_etaProd`, which reads it off the topological product (its
truncations are `1` mod `q ^ 2` times `1 - q`). -/
private theorem coeff_one_etaProd : PowerSeries.coeff 1 etaProd = -1 := by
  have hmul := PowerSeries.WithPiTopology.multipliable_one_sub_X_pow ℤ
  have ht : Filter.Tendsto
      (fun s : Finset ℕ => PowerSeries.coeff 1
        (∏ i ∈ s, ((1 : PowerSeries ℤ) - PowerSeries.X ^ (i + 1))))
      Filter.atTop (nhds (PowerSeries.coeff 1 etaProd)) :=
    ((PowerSeries.WithPiTopology.continuous_coeff ℤ 1).tendsto _).comp hmul.hasProd
  rw [nhds_discrete ℤ, Filter.tendsto_pure] at ht
  obtain ⟨s₀, hs₀⟩ := Filter.eventually_atTop.mp ht
  have hsub : s₀ ⊆ insert 0 (s₀.erase 0) := Finset.subset_insert_iff.mpr (subset_refl _)
  have key : PowerSeries.coeff 1
      (∏ i ∈ insert 0 (s₀.erase 0), ((1 : PowerSeries ℤ) - PowerSeries.X ^ (i + 1))) =
        PowerSeries.coeff 1 etaProd := hs₀ _ hsub
  rw [← key, Finset.prod_insert (Finset.notMem_erase 0 s₀)]

  obtain ⟨r, hr⟩ : ∃ r : PowerSeries ℤ,
      ∏ i ∈ s₀.erase 0, ((1 : PowerSeries ℤ) - PowerSeries.X ^ (i + 1)) =
        1 + PowerSeries.X ^ 2 * r := by
    refine Finset.prod_induction _ (fun Q => ∃ r : PowerSeries ℤ, Q = 1 + PowerSeries.X ^ 2 * r)
      ?_ ?_ ?_
    · rintro a b ⟨u, rfl⟩ ⟨v, rfl⟩
      exact ⟨u + v + PowerSeries.X ^ 2 * u * v, by ring⟩
    · exact ⟨0, by ring⟩
    · intro i hi
      cases i with
      | zero => exact absurd hi (Finset.notMem_erase 0 s₀)
      | succ k => exact ⟨-PowerSeries.X ^ k, by ring⟩
  have hexp : ((1 : PowerSeries ℤ) - PowerSeries.X ^ (0 + 1)) * (1 + PowerSeries.X ^ 2 * r) =
      1 - PowerSeries.X + PowerSeries.X ^ 2 * (r - PowerSeries.X * r) := by
    ring
  rw [hr, hexp, map_add, map_sub, PowerSeries.coeff_one, PowerSeries.coeff_one_X,
    PowerSeries.coeff_X_pow_mul']
  simp

/-- The linear coefficient of `𝓔 ^ N` is `-N`: `𝓔 = 1 - q - ⋯`, so
`𝓔 ^ N = 1 - N q - ⋯`. This is the pin's `coeff_one_etaC_pow`, on top of mathlib's
`PowerSeries.coeff_one_pow` in place of the pin's `coeff_one_pow_of_shape`, with
the pin's two coefficient-map lemmas inlined. -/
private theorem coeff_one_etaC_pow (K : Type*) [CommRing K] (N : ℕ) :
    (𝓔[K] ^ N).coeff 1 = -(N : K) := by
  have h0 : PowerSeries.constantCoeff (PowerSeries.map (Int.castRingHom K) etaProd) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_etaProd, map_one]
  have h1 : PowerSeries.coeff 1 (PowerSeries.map (Int.castRingHom K) etaProd) = -1 := by
    rw [PowerSeries.coeff_map, coeff_one_etaProd, map_neg, map_one]
  rw [← map_pow]
  have h := HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ)
    (PowerSeries.map (Int.castRingHom K) etaProd ^ N) 1
  rw [Nat.cast_one] at h
  rw [h, PowerSeries.coeff_one_pow, h0, h1, one_pow, mul_neg, mul_one, mul_one]

/-- `𝓔 ^ ℓ = qExpand K ℓ 𝓔`: the CL4 node `map_intCast_pow_char_eq_qExpand`, moved
through `HahnSeries.ofPowerSeries`. -/
private theorem etaC_pow_char (K : Type*) [CommRing K] (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ] :
    𝓔[K] ^ ℓ = qExpand K ℓ 𝓔[K] := by
  rw [← map_ofPowerSeries]
  exact map_intCast_pow_char_eq_qExpand ℓ _

/-- `𝓔 ^ ℓ ^ c = qExpand K (ℓ ^ c) 𝓔`: iterate the previous lemma. The exponent is
never rewritten under `qExpand`'s `[NeZero]` argument; the changes of exponent go
through `qExpand_congr` and `qExpand_qExpand`. -/
private theorem etaC_pow_char_pow (K : Type*) [CommRing K] (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]
    (c : ℕ) : 𝓔[K] ^ (ℓ ^ c) = qExpand K (ℓ ^ c) 𝓔[K] := by
  induction c with
  | zero =>
      rw [show 𝓔[K] ^ (ℓ ^ 0) = 𝓔[K] by rw [pow_zero, pow_one]]
      exact ((qExpand_congr (pow_zero ℓ) 𝓔[K]).trans (qExpand_one_apply 𝓔[K])).symm
  | succ c ih =>
      have hsplit : 𝓔[K] ^ (ℓ ^ (c + 1)) = (𝓔[K] ^ (ℓ ^ c)) ^ ℓ := by
        rw [pow_succ ℓ c, pow_mul]
      rw [hsplit, ih, ← map_pow, etaC_pow_char K ℓ, qExpand_qExpand]
      exact qExpand_congr (pow_succ ℓ c).symm 𝓔[K]

/-- **`Δ ^ p` is not `C γ · qExpand p Δ`, in the `η`-power form.** Verbatim from
the pin's `S_ModularCurve_StarBank_delta_pow_ne.lean:130`. -/
theorem etaProd_pow_ne (K : Type*) [CommRing K] {ℓ : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] (p : ℕ) [NeZero p] (hp : (p : K) ≠ 0) (hp1 : p ≠ 1) (γ : K) :
    HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ (24 * p) ≠
      HahnSeries.C γ * qExpand K p
        (HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) := by
  have hℓ : ℓ.Prime := Fact.out
  have hℓp : ¬ ℓ ∣ p := fun h => hp ((CharP.cast_eq_zero_iff K ℓ p).2 h)
  obtain ⟨c, m, hm, h24⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (show (24 : ℕ) ≠ 0 by decide) ℓ hℓ.one_lt.ne'
  intro h
  have key : (HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^
        (24 * p)).coeff ((ℓ ^ c : ℕ) : ℤ) =
      (HahnSeries.C γ * qExpand K p
        (HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24)).coeff
          ((ℓ ^ c : ℕ) : ℤ) := by
    rw [h]

  have hL : (HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^
        (24 * p)).coeff ((ℓ ^ c : ℕ) : ℤ) = -((m * p : ℕ) : K) := by
    have e1 : HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^
          (24 * p) =
        qExpand K (ℓ ^ c)
          (HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^
            (m * p)) := by
      rw [h24, show ℓ ^ c * m * p = ℓ ^ c * (m * p) by ring, pow_mul,
        etaC_pow_char_pow K ℓ c, map_pow]
    have e2 := qExpand_coeff_mul (R := K) (ℓ ^ c)
      (HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ (m * p)) 1
    rw [mul_one] at e2
    rw [e1, e2, coeff_one_etaC_pow]

  have hR : (HahnSeries.C γ * qExpand K p
      (HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24)).coeff
        ((ℓ ^ c : ℕ) : ℤ) = 0 := by
    rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, qExpand_coeff_of_not_dvd, smul_zero]
    rw [Int.natCast_dvd_natCast]
    intro hd
    obtain ⟨k, -, hpk⟩ := (Nat.dvd_prime_pow hℓ).1 hd
    cases k with
    | zero => exact hp1 (by simpa using hpk)
    | succ k =>
      rw [hpk] at hℓp
      exact hℓp (dvd_pow_self ℓ (Nat.succ_ne_zero k))
  rw [hL, hR, neg_eq_zero] at key
  rcases (Nat.Prime.dvd_mul hℓ).1 ((CharP.cast_eq_zero_iff K ℓ (m * p)).1 key) with h1 | h2
  · exact hm h1
  · exact hℓp h2

/-- **The StarBank's `Δ` in characteristic `p`**: for a commutative ring `K` of
characteristic `ℓ` and a prime `p ≠ ℓ`, `(q · η ^ 24) ^ p` is not
`C γ · qExpand K p (q · η ^ 24)`, for any `γ : K`. Verbatim from
`Theorems/Thm_ModularCurve_StarBank_delta_pow_ne.lean:6`. -/
theorem delta_pow_ne (K : Type*) [CommRing K] {ℓ : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] {p : ℕ} [Fact p.Prime] (hpℓ : p ≠ ℓ) (γ : K) :
    (HahnSeries.single (1 : ℤ) (1 : K) *
        HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^ p ≠
      HahnSeries.C γ * qExpand K p (HahnSeries.single (1 : ℤ) (1 : K) *
        HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) := by
  have hp : p.Prime := Fact.out
  have hℓ : ℓ.Prime := Fact.out
  have hpK : (p : K) ≠ 0 := fun h0 =>
    hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).1 ((CharP.cast_eq_zero_iff K ℓ p).1 h0)).symm
  intro h
  apply etaProd_pow_ne K p hpK hp.ne_one γ
  have hu : HahnSeries.single (-(p : ℤ)) (1 : K) * HahnSeries.single (p : ℤ) (1 : K) = 1 := by
    rw [HahnSeries.single_mul_single, neg_add_cancel, mul_one, HahnSeries.single_zero_one]
  have hsp : HahnSeries.single (1 : ℤ) (1 : K) ^ p = HahnSeries.single (p : ℤ) (1 : K) := by
    rw [HahnSeries.single_pow, one_pow, nsmul_eq_mul, mul_one]
  calc HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ (24 * p)
      = HahnSeries.single (-(p : ℤ)) (1 : K) * (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^ p := by
        rw [mul_pow, hsp, ← mul_assoc, hu, one_mul, pow_mul]
    _ = HahnSeries.single (-(p : ℤ)) (1 : K) * (HahnSeries.C γ * qExpand K p
          (HahnSeries.single (1 : ℤ) (1 : K) *
            HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24)) := by
        rw [h]
    _ = HahnSeries.C γ * qExpand K p
          (HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) := by
        rw [map_mul, qExpand_single, mul_one, mul_left_comm,
          ← mul_assoc (HahnSeries.single (-(p : ℤ)) (1 : K)), hu, one_mul]

end DeltaPowNe

end StarBank

end ModularCurve

end

#print axioms ModularCurve.StarBank.press
#print axioms ModularCurve.StarBank.etaProd_pow_ne
#print axioms ModularCurve.StarBank.delta_pow_ne
