/-
  The descent by one prime, with its slot hypotheses discharged, and the one-prime
  reduction of `Gen`.

  `jqN_div_mem_modularFunctionField` is the descent of math/010 §4: under `Hall M`,
  `j(q ^ M)` lies in `ℚ(j(q), j(q ^ (M * p)))`. Its engine is the unique-common-root
  argument on the level-`p` modular equation and the pushed minimal polynomial of
  `j(q ^ M)`; the two root conditions that argument needs are *derived* here, from
  T19's slot product (`minpoly_jqN_map_eq_prod_slots`) plus `Hall M`, at the root of
  unity `cycUnit (M * p)`. So the statement names no splitting field, no root of unity
  and no root predicate: a caller supplies `Hall M` and nothing else. The engine, which
  does name them, has no statement of its own: it is applied in the body of that theorem,
  with its certificate produced by the private `exists_transported_minpoly`. Nothing in
  the port exposes it.

  The one genuinely algebraic input is that `j(q ^ M)` is *integral* over the `j`-line, of
  degree `ψ(M)` — the `Tight` half of `Hall M`. It is not left implicit: it enters
  `exists_transported_minpoly` as the monicity and the degree of the certificate, and is
  consumed there as the equation `B.map nomeAlgebra = pushedMinpoly`; `nomeMap_injective`
  turns that into the nonvanishing of the pushed minimal polynomial, which `root_shape`
  takes as a hypothesis because `Polynomial.roots` of the zero polynomial is empty.

  The layers, in dependency order:

  * the pushed minimal polynomial `pushedMinpoly` with the nome map `nomeMap` it is read
    through, and `nomeAlgebra`, the level-`N` reading of the function field that the
    descent installs as its `Algebra` structure on `LaurentSeries K`;
  * `nomeMap_injective`: the reading of the `j`-line at a nome loses nothing;
  * `exists_transported_minpoly`: the engine's certificate `B` — the conjugate equation of
    `j(q ^ M)`, monic of degree `ψ(M)`, with its roots read at the level-`N` nome — its
    transport equation `B.map nomeAlgebra = pushedMinpoly` and the fact that the nome image
    of `j(q ^ M)` is one of its roots. It takes only `Tight M`;
  * `mem_of_mem_range_nome`: the other half of the transport, turning membership in the
    image of the function field back into `j(q ^ M) ∈ F`;
  * `qExpand_qTwist_coeffEmb`, `iota_jqN_seed`: the translation between the `TS` spelling of
    a slot and the `qExpand`/`qTwist` spelling the level-`p` slot description uses, so that
    no proof step unfolds `TS` or `coeffEmb jq` by hand;
  * `phi_p_roots`: the root list of the level-`p` equation at the level-`M * p` invariant —
    the extra conjugate `j(q ^ (p * (p * (M * p * M))))` and the `p` twists
    `j(ζ ^ (b * M) q ^ ((M * p) * M))`;
  * `slot_inj`, `pushedMinpoly_eq_prod_slots`, `pushedMinpoly_splits`,
    `pushedMinpoly_roots_nodup`: the certificate's own root theory — T19's slot product read
    at the level-`M * p` nome, its splitting, and the distinctness of the `ψ(M)` slot values
    (the slot parameter `(a, b)` is recoverable from the value). The engine therefore runs on
    the certificate, and the level-`p` equation enters only as its companion;
  * `root_shape`: every root of `pushedMinpoly K M (M * p)` (a multiset, so nonvanishing is
    a hypothesis) is a slot value `j(ζ ^ (b * a) q ^ (a * a))` with `a ∣ M`, `b < M / a`
    (the slot list of the level-`M` minimal polynomial, read at the level-`M * p` nome);
  * `htw_of` / `hsp_of`: the two root conditions, by index arithmetic on that shape and
    `TS_injective`;
  * `jqN_div_mem_modularFunctionField`: the descent — its certificate, its engine, and
    a statement over `ℚ` only. The uniqueness (`huniq`) is the theorem's content and stays
    in its body: a root of the level-`p` equation is the extra conjugate (no root of the
    certificate, by `hsp`) or a twist (untwisted, hence the untwisted slot, by `htw` and
    `iota_jqN`).

  Its second subject is the one-prime reduction of `Gen`, in the same `Hall` form:
  `modularFunctionField_eq_full_of` takes the strong induction hypothesis itself
  (`∀ m < N, m ≠ 0 → Hall m`) and derives what it consumes — the level `m < N` that a
  proper divisor `d` divides with `N = m * p`, `Hall m`, `jqN m ∈ F_N` from the descent
  above, and `Gen m` from `Hall m`. The pin instead passes two facts per factorization;
  the caller passes `ih` unchanged.

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:

  * `P2M/Sol/S_ModularCurve_modularFunctionField_eq_full_of.lean` lines 553–690 — the
    descent, `private` in the pin and stated with `ζ`, `hζ` and the two root conditions.
    That text is the body of the descent here, at `ζ = cycUnit (M * p)`; the pin's
    hypotheses are discharged in its first four lines and the statement takes `Hall M`;
  * the same file, lines 694–727 — the one-prime reduction, whose two hypothesis
    applications (`hstep`, `hgen'`) become the derivation of what they carry;
  * `P2M/Sol/S_ModularCurve_functionFieldGeneration.lean` lines 541–613 — `root_shape`,
    `htw_of` and `hsp_of`, `private` in the pin and consumed only by the pin's
    `hall_all`. They live here because this is the layer where T15 and T19 meet: the
    discharge needs T19's slot product, and the descent does not (the pin proves it
    without).

  ## Verification tier

  No `spec-pin:` header, deliberately: the public statements are the port's own. The
  descent's engine is the pin's text with its hypotheses folded into the statement, and
  the reduction's text was retired to the `Hall` form, so a wire would diff nothing.
  Registered by `spec/unwired_register.py`.

  If a future public declaration in this module transcribes a pin statement, it needs a
  `spec-pin:` line, and this note is then wrong.

  ## Assumptions

  T4's `Polynomial.mem_range_of_unique_common_root`; T12's
  `exists_phiIrreducible_evalSymm`; T14's `phiAtSeed`/`phiAtSeed_map`,
  `isRoot_prime_at_slot_iff`, `iota_jqN`, `TS_congr`; `Defs/Laurent`'s
  `coeffMap_injective` and `qExpand_injective`; `Defs/PhiAtSlot`'s `pushedMinpoly`,
  `Defs/TS`'s `TS` and `TS_injective`, `Defs/Cyclotomic`'s `cycUnit`,
  `Defs/Fields`'s `modularFunctionField`, `adjoin_jq_le`, `jqN_mem` and `jqd_mem_full`;
  `SlotValues`'s `slotValues`/`prod_slotValues`/`nodup_slotValues`; T19's
  `minpoly_jqN_map_eq_prod_slots`; `NumberTheory/DedekindPsi`'s `lt_of_mul_prime_eq`.
-/
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import FLTForHuman.FieldTheory.CommonRoot
import FLTForHuman.NumberTheory.DedekindPsi
import FLTForHuman.ModularCurve.Defs.Invariants
import FLTForHuman.ModularCurve.Defs.PhiAtSlot
import FLTForHuman.ModularCurve.Defs.TS
import FLTForHuman.ModularCurve.Defs.Cyclotomic
import FLTForHuman.ModularCurve.Defs.Fields
import FLTForHuman.ModularCurve.PhiSlotRoots
import FLTForHuman.ModularCurve.PhiGenSplits
import FLTForHuman.ModularCurve.ModularPolynomialProperties
import FLTForHuman.ModularCurve.FunctionFieldGeneration.SlotProduct

set_option autoImplicit false

noncomputable section

open Polynomial HahnSeries IntermediateField

namespace ModularCurve

variable {K : Type} [Field K] [Algebra ℚ K]

/-! ## The pushed minimal polynomial, private to this module

The two names the descent's engine is stated in. Both are spellings of expressions the pin
writes inline at every use: `nomeMap K N` is the composite `coeffEmb K ∘ qExpand ℚ N ∘
(ℚ⟮jq⟯ ↪ ℚ((q)))`, which *reads a function of `ℚ(j(q))` at the level-`N` nome*, and
`pushedMinpoly K M N` is the minimal polynomial of `j(q ^ M)` read through it. They are
private here because the public statement below names neither: the certificate stays inside
the module, and nothing outside reads these terms. -/

/-- Read a function of `ℚ(j(q))` at the level-`N` nome `q ↦ q ^ N`, with coefficients
extended to `K`. -/
private def nomeMap (K : Type*) [Field K] [Algebra ℚ K] (N : ℕ) [NeZero N] :
    ℚ⟮jq⟯ →+* LaurentSeries K :=
  ((coeffEmb K).comp (qExpand ℚ N)).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ))

/-- The level-`N` reading of the function field, as a ring hom: `j(q) ↦ j(q ^ N)`, with
coefficients extended to `K`. The descent builds its `Algebra` structure on `LaurentSeries K`
from this map, and reads every root through it. -/
private def nomeAlgebra (N : ℕ) [NeZero N] : ↥(modularFunctionField N) →+* LaurentSeries K :=
  ((coeffEmb K).comp (qExpand ℚ N)).comp (algebraMap ↥(modularFunctionField N) (LaurentSeries ℚ))

/-- The minimal polynomial of `j(q ^ M)` over `ℚ(j(q))`, pushed to the level-`N` nome: the
polynomial whose roots the descent compares with those of the level-`p` modular equation. -/
private def pushedMinpoly (K : Type*) [Field K] [Algebra ℚ K] (M : ℕ) [NeZero M] (N : ℕ) [NeZero N] :
    Polynomial (LaurentSeries K) :=
  (minpoly ℚ⟮jq⟯ (jqN M)).map (nomeMap K N)

/-- Reading at the level `M` and then at the level `e` is reading at the level `M * e`. -/
private theorem nomeMap_qExpand (K : Type*) [Field K] [Algebra ℚ K] (M e : ℕ) [NeZero M] [NeZero e] :
    (qExpand K e).comp (nomeMap K M) = nomeMap K (M * e) := by
  refine RingHom.ext fun z => ?_
  simp only [RingHom.comp_apply, nomeMap]
  rw [coeffEmb_qExpand, coeffEmb_qExpand, qExpand_qExpand]
  exact qExpand_congr (mul_comm e M) _

/-- The nome reading of functions of `j(q)` loses nothing: `nomeMap` is injective. -/
private theorem nomeMap_injective (N : ℕ) [NeZero N] : Function.Injective (nomeMap (K := K) N) := by
  have hemb : Function.Injective (coeffEmb K) := coeffMap_injective ((algebraMap ℚ K).injective)
  intro x y h
  have h1 : qExpand ℚ N ((algebraMap ↥ℚ⟮jq⟯ (LaurentSeries ℚ)) x)
      = qExpand ℚ N ((algebraMap ↥ℚ⟮jq⟯ (LaurentSeries ℚ)) y) :=
    hemb (by simpa only [nomeMap, RingHom.comp_apply] using h)
  exact Subtype.ext (qExpand_injective N h1)

/-! ## The coefficient transport of the minimal polynomial

The descent's second polynomial lives over `F`, but the polynomial whose roots are known lives
over the `j`-line `ℚ⟮jq⟯`. Moving the coefficients along `ℚ⟮jq⟯ ≤ F` changes neither the roots nor
their values, so each direction of the transport is stated once: producing the certificate,
and undoing the reading at the end of the descent. -/

/-- **The certificate.** The conjugate equation of `jqN M` over the level-`N` field: the minimal
polynomial of `jqN M` over the `j`-line, with coefficients transported over that field. It is
monic of degree `ψ(M)` — `Tight M` is the algebraic input, through integrality — and its roots,
read in `LaurentSeries K` at the level-`N` nome, are the roots of the pushed minimal polynomial,
the nome image of `jqN M` among them. -/
private theorem exists_transported_minpoly {N : ℕ} [NeZero N] (M : ℕ) [NeZero M] (htM : Tight M) :
    ∃ B : Polynomial (modularFunctionField N),
      B.Monic ∧ B.natDegree = dedekindPsi M ∧
        B.map (nomeAlgebra (K := K) N) = pushedMinpoly K M N ∧
        (∀ y : LaurentSeries K,
          Polynomial.eval₂ (nomeAlgebra (K := K) N) y B = 0 ↔ (pushedMinpoly K M N).IsRoot y) ∧
          Polynomial.eval₂ (nomeAlgebra (K := K) N) (coeffEmb K (qExpand ℚ N (jqN M))) B = 0 := by
  have hmonic : (minpoly ℚ⟮jq⟯ (jqN M)).Monic := minpoly.monic (isIntegral_adjoin_jqN htM)
  have hcomp : (nomeAlgebra (K := K) N).comp (IntermediateField.inclusion (adjoin_jq_le N))
      = nomeMap K N := by
    refine RingHom.ext fun x => ?_
    simp only [nomeAlgebra, RingHom.comp_apply, nomeMap]
    rfl
  refine ⟨(minpoly ℚ⟮jq⟯ (jqN M)).map (IntermediateField.inclusion (adjoin_jq_le N)),
    hmonic.map _, ?_, ?_, ?_, ?_⟩
  · exact (Polynomial.natDegree_map_eq_of_injective
      (IntermediateField.inclusion_injective (adjoin_jq_le N)) _).trans (natDegree_minpoly_jqN htM)
  · rw [Polynomial.map_map, hcomp, pushedMinpoly]
  · intro y
    rw [Polynomial.IsRoot.def, pushedMinpoly, Polynomial.eval₂_map, hcomp,
      Polynomial.eval₂_eq_eval_map]
  · have hx : coeffEmb K (qExpand ℚ N (jqN M))
        = ((coeffEmb K).comp (qExpand ℚ N)) (jqN M) := rfl
    rw [Polynomial.eval₂_map, hcomp, nomeMap, ← Polynomial.eval₂_map, hx, Polynomial.eval₂_hom,
      Polynomial.eval_map, ← Polynomial.aeval_def, minpoly.aeval, map_zero]

/-- **Undoing the nome reading.** If the level-`N` nome image of `y` is rational over the
level-`N` function field, then `y` itself is an element of it: reading the field at a nome is
injective on it. This is the descent's last step, where the transport of the coefficients is
undone. -/
private theorem mem_of_mem_range_nome {N : ℕ} [NeZero N] {y : LaurentSeries ℚ}
    (hy : coeffEmb K (qExpand ℚ N y) ∈ (nomeAlgebra (K := K) N).range) :
    y ∈ modularFunctionField N := by
  obtain ⟨f, hf⟩ := RingHom.mem_range.mp hy
  have hf' : coeffEmb K (qExpand ℚ N ((f : LaurentSeries ℚ))) = coeffEmb K (qExpand ℚ N y) := by
    rw [← hf, nomeAlgebra]
    rfl
  have hemb : Function.Injective (coeffEmb K) :=
    coeffMap_injective ((algebraMap ℚ K).injective)
  have hval : (f : LaurentSeries ℚ) = y := qExpand_injective N (hemb hf')
  rw [← hval]
  exact f.2

/-! ## Slot spellings of the `j`-slices

`root_shape` yields roots as `TS` values, while the level-`p` slot description writes the
same values as `qExpand`/`qTwist` of `coeffEmb jq`. These three lemmas are that translation. -/

/-- A twisted `j`-slice read over a `ℚ`-algebra is the `TS` value at the same level: `TS` is
this very expression with `jqModC` in place of `coeffEmb jq`. -/
private theorem qExpand_qTwist_coeffEmb (e : ℕ) [NeZero e] (u : Kˣ) :
    qExpand K e (qTwist u (coeffEmb K jq)) = TS K e u := by
  rw [TS, coeffEmb_jq]

/-- **The seed of the level-`p` equation.** The level-`M * p` invariant `j(q ^ (M * p))`, read at
that same nome, spelled the way the slot description writes its seed. -/
private theorem iota_jqN_seed (M p : ℕ) [NeZero M] [NeZero p] :
    coeffEmb K (qExpand ℚ (M * p) (jqN (M * p)))
      = qExpand K (p * (M * p * M)) (qTwist ((1 : Kˣ) ^ p) (coeffEmb K jq)) := by
  rw [one_pow, iota_jqN, qExpand_qTwist_coeffEmb]
  exact TS_congr (by ring) 1

/-! ## The shape of a root of the pushed minimal polynomial -/

/-- **Every root is a slot value.** A root `x` of `pushedMinpoly K M (M * p)` is
`j(ζ ^ (b * a) q ^ (a * a))` for some `a ∣ M` and `b < M / a`: the slot description
of the level-`M` minimal polynomial (T19), read at the level-`M * p` nome. Nonvanishing is
`Tight M`'s, and is what lets the multiset of roots be spoken about at all. -/
private theorem root_shape (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) M) (hallM : Hall M)
    (hne : pushedMinpoly K M (M * p) ≠ 0) (x : LaurentSeries K)
    (hx : x ∈ (pushedMinpoly K M (M * p)).roots) :
    ∃ a : ℕ, ∃ _ : NeZero a, a ∣ M ∧ ∃ b : ℕ, b < M / a ∧
      x = TS K (p * (a * a)) (ζ ^ (b * a)) := by
  have hid := minpoly_jqN_map_eq_prod_slots (K := K) M ζ hζ hallM
  have hcomp : (qExpand K p).comp (((coeffEmb K).comp (qExpand ℚ M)).comp
      (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))
      = ((coeffEmb K).comp (qExpand ℚ (M * p))).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)) := by
    simpa only [nomeMap] using nomeMap_qExpand K M p
  have hx' : Polynomial.eval x ((minpoly ℚ⟮jq⟯ (jqN M)).map
      (((coeffEmb K).comp (qExpand ℚ (M * p))).comp
        (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))) = 0 := (Polynomial.mem_roots hne).mp hx
  rw [← hcomp, ← Polynomial.map_map, hid, Polynomial.eval_map,
    Polynomial.eval₂_finsetProd] at hx'
  obtain ⟨a, ha, hx'⟩ := Finset.prod_eq_zero_iff.mp hx'
  rw [Polynomial.eval₂_finsetProd] at hx'
  obtain ⟨b, hb, hx'⟩ := Finset.prod_eq_zero_iff.mp hx'
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, sub_eq_zero] at hx'
  have ha0 : a ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors ha)
  rw [dite_eq_right ha0] at hx'
  have : NeZero a := ⟨ha0⟩
  refine ⟨a, ⟨ha0⟩, Nat.dvd_of_mem_divisors ha, b,
    (Finset.mem_range.mp (Finset.mem_filter.mp hb).1), ?_⟩
  rw [hx', coeffEmb_jq]
  exact qExpand_TS p (a * a) (ζ ^ (b * a))

/-! ## The two slot facts -/

/-- **`htw`.** At nome-level `(M * p) * M` the only root of the pushed minimal
polynomial is the untwisted one: comparing the level in `root_shape` with `M²p`
forces `a = M`, and the twist index `b < M / a = 1` forces `b = 0`. -/
private theorem htw_of (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) M) (hallM : Hall M)
    (hne : pushedMinpoly K M (M * p) ≠ 0) (w : Kˣ)
    (hw : (pushedMinpoly K M (M * p)).IsRoot (TS K ((M * p) * M) w)) : w = 1 := by
  obtain ⟨a, _, haM, b, hb, heq⟩ :=
    root_shape M p ζ hζ hallM hne _ ((Polynomial.mem_roots hne).mpr hw)
  obtain ⟨he, hu⟩ := TS_injective heq
  have he' : p * (a * a) = p * (M * M) := by rw [← he]; ring
  have haM' : a = M := Nat.mul_self_inj.mp (Nat.eq_of_mul_eq_mul_left hp.out.pos he')
  subst haM'
  have hb0 : b = 0 := by
    rw [Nat.div_self (Nat.pos_of_ne_zero (NeZero.ne a))] at hb
    omega
  subst hb0
  rw [zero_mul, pow_zero] at hu
  exact hu

/-- **`hsp`.** The extra conjugate `j(q ^ (p * (p * (M * p * M))))` of the level-`p`
equation is not a root: a root at that level would have `a² = (M p)²` by the same
comparison, hence `a = M p > M`, contradicting `a ∣ M`. -/
private theorem hsp_of (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) M) (hallM : Hall M)
    (hne : pushedMinpoly K M (M * p) ≠ 0) :
    ¬ (pushedMinpoly K M (M * p)).IsRoot (TS K (p * (p * (M * p * M))) 1) := by
  intro hx
  obtain ⟨a, _, haM, b, _, heq⟩ :=
    root_shape M p ζ hζ hallM hne _ ((Polynomial.mem_roots hne).mpr hx)
  obtain ⟨he, _⟩ := TS_injective heq
  have hp2 : 2 ≤ p := hp.out.two_le
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have ha : a ≤ M := Nat.le_of_dvd hM haM
  have h1 : a * a = (M * p) * (M * p) := by
    have h2 : p * (a * a) = p * ((M * p) * (M * p)) := by rw [← he]; ring
    exact Nat.eq_of_mul_eq_mul_left hp.out.pos h2
  have h2 : a = M * p := Nat.mul_self_inj.mp h1
  have : M * p ≤ M := h2 ▸ ha
  have : M * 2 ≤ M * p := Nat.mul_le_mul_left M hp2
  omega

/-! ## The root list of the level-`p` equation -/

/-- **The roots of `Φ_p` at the level-`M * p` invariant.** Read over `LaurentSeries K`, the roots
are the extra conjugate `j(q ^ (p * (p * (M * p * M))))` and, for `b < p`, the twists
`j(ζ ^ (b * M) q ^ ((M * p) * M))`. -/
private theorem phi_p_roots (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)]
    (data : ModularPolynomialData p) (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) (M * p)) :
    ∀ y : LaurentSeries K,
      Polynomial.eval y (phiAtSeed data (coeffEmb K (qExpand ℚ (M * p) (jqN (M * p))))) = 0 ↔
        (y = TS K (p * (p * (M * p * M))) 1 ∨
          ∃ b < p, y = TS K (M * p * M) (ζ ^ (b * (M * p / p)))) := by
  intro y
  rw [iota_jqN_seed M p]
  refine (isRoot_prime_at_slot_iff (M * p) ζ hζ p (dvd_mul_left p M) data (M * p * M) 1 y).trans ?_
  simp only [qExpand_qTwist_coeffEmb, one_pow, one_mul]

/-! ## The conjugate equation's roots

The slot product T19, read at the level-`M * p` nome: the conjugate equation of `jqN M` is the
product of `X - C` over the `ψ(M)` slot values, and those values are distinct because the slot
parameter `(a, b)` is recoverable from the value. -/

/-- The slot values of the conjugate equation at the level-`M * p` nome, with the `a = 0` guard
the slot product carries. -/
private def slotTS (p : ℕ) [NeZero p] (ζ : Kˣ) (a b : ℕ) : LaurentSeries K :=
  if h : a = 0 then 0 else letI : NeZero a := ⟨h⟩; TS K (p * (a * a)) (ζ ^ (b * a))

omit [Algebra ℚ K] in
/-- The slot parameter is recoverable from the `p`-scaled slot value. -/
private theorem slot_inj {M p : ℕ} [NeZero M] [NeZero p] {ζ : Kˣ}
    (hζ : IsPrimitiveRoot (ζ : K) M) {a a' b b' : ℕ} (haM : a ∣ M) (haM' : a' ∣ M)
    (hb : b < M / a) (hb' : b' < M / a')
    (h : slotTS (K := K) p ζ a b = slotTS (K := K) p ζ a' b') : a = a' ∧ b = b' := by
  have ha0 : a ≠ 0 := Nat.ne_of_gt (Nat.pos_of_dvd_of_pos haM (NeZero.pos M))
  have ha0' : a' ≠ 0 := Nat.ne_of_gt (Nat.pos_of_dvd_of_pos haM' (NeZero.pos M))
  unfold slotTS at h
  rw [dite_eq_right ha0, dite_eq_right ha0'] at h
  obtain ⟨he, hu⟩ :=
    letI : NeZero a := ⟨ha0⟩
    letI : NeZero a' := ⟨ha0'⟩
    TS_injective h
  have haa : a * a = a' * a' := Nat.eq_of_mul_eq_mul_left (NeZero.pos p) he
  have haa' : a = a' := Nat.mul_self_inj.mp haa
  subst haa'
  have ha0pos : 0 < a := Nat.pos_of_ne_zero ha0
  have hbM : b * a < M := by
    rw [← Nat.div_mul_cancel haM]
    exact Nat.mul_lt_mul_of_pos_right hb ha0pos
  have hbM' : b' * a < M := by
    rw [← Nat.div_mul_cancel haM]
    exact Nat.mul_lt_mul_of_pos_right hb' ha0pos
  have hu' : (ζ : K) ^ (b * a) = (ζ : K) ^ (b' * a) := by
    simpa using congrArg Units.val hu
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right ha0pos (hζ.pow_inj hbM hbM' hu')⟩

/-- **The conjugate equation, factored.** T19's slot product at the level-`M * p` nome: the
pushed minimal polynomial of `jqN M` is the product of `X - C` over the `ψ(M)` slot values. -/
private theorem pushedMinpoly_eq_prod_slots {M p : ℕ} [NeZero M] [NeZero p]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) M) (hallM : Hall M) :
    pushedMinpoly K M (M * p)
      = ∏ a ∈ M.divisors, ∏ b ∈ (Finset.range (M / a)).filter
          (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1),
          (Polynomial.X - Polynomial.C (slotTS (K := K) p ζ a b)) := by
  rw [pushedMinpoly, ← nomeMap_qExpand (K := K) M p, ← Polynomial.map_map, nomeMap,
    minpoly_jqN_map_eq_prod_slots (K := K) M ζ hζ hallM, Polynomial.map_prod]
  refine Finset.prod_congr rfl fun a ha => ?_
  rw [Polynomial.map_prod]
  refine Finset.prod_congr rfl fun b hb => ?_
  have ha0 : a ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors ha)
  simp only [slotTS, dite_eq_right ha0, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    qExpand_qTwist_coeffEmb, qExpand_TS]

/-- The conjugate equation splits: it is a product of linear factors. -/
private theorem pushedMinpoly_splits {M p : ℕ} [NeZero M] [NeZero p]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) M) (hallM : Hall M) :
    (pushedMinpoly K M (M * p)).Splits := by
  rw [pushedMinpoly_eq_prod_slots (M := M) (p := p) ζ hζ hallM]
  exact Polynomial.Splits.prod fun a _ =>
    Polynomial.Splits.prod fun b _ => Polynomial.Splits.X_sub_C _

/-- The conjugate equation has distinct roots: the slot parameter is recoverable from the slot
value, so the multiset of slots has no repetitions. -/
private theorem pushedMinpoly_roots_nodup {M p : ℕ} [NeZero M] [NeZero p]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) M) (hallM : Hall M) :
    (pushedMinpoly K M (M * p)).roots.Nodup := by
  rw [pushedMinpoly_eq_prod_slots (M := M) (p := p) ζ hζ hallM,
    ← prod_slotValues M (slotTS (K := K) p ζ), roots_multiset_prod_X_sub_C]
  exact nodup_slotValues fun a b a' b' ha ha' hb hb' h => slot_inj hζ
    (Nat.dvd_of_mem_divisors ha) (Nat.dvd_of_mem_divisors ha')
    (Finset.mem_range.mp (Finset.mem_filter.mp hb).1)
    (Finset.mem_range.mp (Finset.mem_filter.mp hb').1) h

/-! ## The descent -/



/-- **Descent by one prime**: under `Hall M` and `p` prime, `j(q ^ M)` lies in
`ℚ(j(q), j(q ^ (M * p)))`.

The unique-common-root argument it runs needs two conditions on the roots of the
pushed minimal polynomial of `j(q ^ M)` read at the level-`M * p` nome; `htw_of` and
`hsp_of` derive both from T19's slot product at the root of unity `cycUnit (M * p) ^
((M * p) / M)`. That is why the statement names neither a splitting field nor a root
predicate: `Hall M` is the whole input, and the certificate stays inside. -/
theorem jqN_div_mem_modularFunctionField (M : ℕ) [NeZero M] (p : ℕ)
    [hp : Fact (Nat.Prime p)] (hallM : Hall M) :
    jqN M ∈ modularFunctionField (M * p) := by
  set K := CyclotomicField (M * p) ℚ
  set ζ : Kˣ := cycUnit (M * p)
  have hζ : IsPrimitiveRoot (ζ : K) (M * p) :=
    cycUnit_spec (M * p)
  have hζM : IsPrimitiveRoot ((ζ ^ ((M * p) / M) : Kˣ) : K) M :=
    isPrimitiveRoot_pow_div hζ (dvd_mul_right M p)
  classical
  obtain ⟨data, -, -⟩ := exists_phiIrreducible_evalSymm p

  set F := modularFunctionField (M * p)
  have hjNmem : jqN (M * p) ∈ F := jqN_mem (M * p)
  let : Algebra F (LaurentSeries K) := (nomeAlgebra (K := K) (M * p)).toAlgebra

  set A : Polynomial F := phiAtSeed data (⟨jqN (M * p), hjNmem⟩ : F)

  have hmapA : A.map (algebraMap F (LaurentSeries K))
      = phiAtSeed data (coeffEmb K (qExpand ℚ (M * p) (jqN (M * p)))) :=
    phiAtSeed_map data _ _
  have hrootA : ∀ y : LaurentSeries K,
      Polynomial.aeval y A = 0 ↔
        (y = TS K (p * (p * (M * p * M))) 1 ∨
          ∃ b < p, y = TS K (M * p * M) (ζ ^ (b * (M * p / p)))) := by
    intro y
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hmapA]
    exact phi_p_roots M p data ζ hζ y

  set x₀ : LaurentSeries K := coeffEmb K (qExpand ℚ (M * p) (jqN M))

  obtain ⟨B, hBmonic, hBdeg, hBmap, hB, hxB⟩ :=
    exists_transported_minpoly (K := K) (N := M * p) (M := M) (hallM M dvd_rfl).1
  have hne : pushedMinpoly K M (M * p) ≠ 0 := by
    rw [← hBmap]
    exact (hBmonic.map (nomeAlgebra (K := K) (M * p))).ne_zero
  have htw : ∀ w : Kˣ, (pushedMinpoly K M (M * p)).IsRoot (TS K ((M * p) * M) w) → w = 1 :=
    htw_of M p (ζ ^ ((M * p) / M)) hζM hallM hne
  have hsp : ¬ (pushedMinpoly K M (M * p)).IsRoot (TS K (p * (p * (M * p * M))) 1) :=
    hsp_of M p (ζ ^ ((M * p) / M)) hζM hallM hne
  have hxA : Polynomial.aeval x₀ A = 0 :=
    (hrootA x₀).mpr (Or.inr ⟨0, hp.out.pos, by
      rw [Nat.zero_mul, pow_zero]
      exact iota_jqN (M * p) M⟩)
  have huniq : ∀ y : LaurentSeries K,
      Polynomial.aeval y A = 0 → (pushedMinpoly K M (M * p)).IsRoot y → y = x₀ := by
    intro y hyA hyB
    rcases (hrootA y).mp hyA with hy1 | ⟨b, _, hy1⟩
    · exact (hsp (hy1 ▸ hyB)).elim
    · have hw : ζ ^ (b * (M * p / p)) = 1 := htw _ (hy1 ▸ hyB)
      rw [hy1, hw]
      exact (iota_jqN (M * p) M).symm

  have hB0 : B ≠ 0 := hBmonic.ne_zero
  have hBs : (B.map (algebraMap F (LaurentSeries K))).Splits := by
    rw [show B.map (algebraMap F (LaurentSeries K)) = pushedMinpoly K M (M * p) from hBmap]
    exact pushedMinpoly_splits (ζ ^ ((M * p) / M)) hζM hallM
  have hBnd : (B.map (algebraMap F (LaurentSeries K))).roots.Nodup := by
    rw [show B.map (algebraMap F (LaurentSeries K)) = pushedMinpoly K M (M * p) from hBmap]
    exact pushedMinpoly_roots_nodup (ζ ^ ((M * p) / M)) hζM hallM

  have hrange := Polynomial.mem_range_of_unique_common_root B A hB0 hBs hBnd x₀ hxB hxA
    fun y hyB hyA => huniq y hyA ((hB y).mp hyB)
  exact mem_of_mem_range_nome (N := M * p) hrange
/-! ## The one-prime reduction -/

/-- **The step down the divisor lattice.** A proper divisor `d` of `N` divides a level `m`
that is properly below `N`, and `N / m` is prime: writing `N = d * m'` and taking
`p := m'.minFac`, that level is `m = d * (m' / p)`.

This is the arithmetic that opens any prime-by-prime strong induction over the divisors of a
level. It stays private here because it is arithmetic about this reduction's own data: `m` is
the level the induction hypothesis is taken at, and `p` the prime its step is taken by. -/
private theorem exists_mul_prime_lt_of_dvd_of_ne {N : ℕ} [NeZero N] {d : ℕ} [NeZero d]
    (hdN : d ∣ N) (hd : d ≠ N) :
    ∃ m p : ℕ, p.Prime ∧ NeZero m ∧ d ∣ m ∧ N = m * p ∧ m < N := by
  obtain ⟨m', hm'⟩ := hdN
  have hm'1 : m' ≠ 1 := fun h1 => hd (by rw [hm', h1, Nat.mul_one])
  have hm'0 : m' ≠ 0 := fun h0 => NeZero.ne N (by rw [hm', h0, Nat.mul_zero])
  obtain ⟨m, hm⟩ := Nat.minFac_dvd m'
  have hp : m'.minFac.Prime := Nat.minFac_prime hm'1
  have hm0 : m ≠ 0 := fun h0 => hm'0 (by rw [hm, h0, Nat.mul_zero])
  have hdm : d * m ≠ 0 := Nat.mul_ne_zero (NeZero.ne d) hm0
  have hNm : N = (d * m) * m'.minFac := by
    conv_lhs => rw [hm', hm]
    ring
  exact ⟨d * m, m'.minFac, hp, ⟨hdm⟩, dvd_mul_right d m, hNm,
    lt_of_mul_prime_eq hdm hp hNm.symm⟩

/-- **The one-prime reduction of `Gen`**: if the invariants hold at every level below
`N`, then `modularFunctionField N` is the full divisor field.

The hypothesis is the strong induction hypothesis *in the shape the induction gives it*
(`∀ m < N, m ≠ 0 → Hall m`), so the caller passes it unchanged. Everything the reduction
consumes for a proper divisor `d` is derived here: a level `m < N` divisible by `d` with
`N = m * p` (the private `exists_mul_prime_lt_of_dvd_of_ne`), `Hall m`, `jqN m ∈ F_N` from
the Hall-level descent, and `Gen m` from `Hall m`. The pin instead passes two facts per
factorization, with `Gen` unfolded; the port's earlier text conjoined them; both shapes made
the caller assemble what this statement can derive.

The statement is the port's; this module carries no `spec-pin:` wire, and the header
records why. -/
theorem modularFunctionField_eq_full_of (N : ℕ) [NeZero N]
    (h : ∀ m : ℕ, m < N → m ≠ 0 → Hall m) :
    modularFunctionField N = modularFunctionFieldFull N := by
  refine le_antisymm (modularFunctionField_le_full N) ?_
  rw [modularFunctionFieldFull, IntermediateField.adjoin_le_iff]
  rintro x ⟨d, hd0, hdN, rfl⟩
  rcases eq_or_ne d N with hd | hd
  · subst d
    exact IntermediateField.subset_adjoin ℚ _ (Set.mem_insert_of_mem _ rfl)
  · obtain ⟨m, p, hp, hm0, hdm, hNm, hmlt⟩ := exists_mul_prime_lt_of_dvd_of_ne hdN hd
    have : Fact (Nat.Prime p) := ⟨hp⟩
    have hallm : Hall m := h m hmlt (NeZero.ne m)
    have hmem : jqN m ∈ modularFunctionField N := by
      rw [mff_congr hNm]
      exact jqN_div_mem_modularFunctionField m p hallm
    have hle : modularFunctionFieldFull m ≤ modularFunctionField N := by
      rw [← (hallm m dvd_rfl).2, modularFunctionField, IntermediateField.adjoin_le_iff,
        Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨IntermediateField.subset_adjoin ℚ _ (Set.mem_insert _ _), hmem⟩
    exact hle (jqd_mem_full m hdm)

end ModularCurve

end
