/-
  The generic kernel of the `functionFieldGeneration` segment.

  Three lemmas about a polynomial over an arbitrary field extension `F ⊆ L`, with
  no curve and no `j`-invariant anywhere. They are the mathematical engine of the
  segment's descent: read against math/010,

  * `Polynomial.mem_range_of_unique_common_root` **is** §4, "descent by one
    prime" — a split squarefree `A` and a `B` whose only common root is `x` force
    `x` to be rational;
  * `Polynomial.mem_range_of_eval_eq_const` **is** §6's non-membership step — a
    polynomial of degree `< card s` that is constant on `s` has its constant
    value in the base field;
  * `Polynomial.irreducible_of_transitive_ringAut` **is** §6's `p + 1` / `p`
    degree step — a split monic polynomial whose roots are cycled by a
    base-fixing ring automorphism, with one root outside the base, is
    irreducible.

  None of the three is in mathlib (a name search over `Mathlib/` returns
  nothing), and each is stated exactly as FLT states it: the statements below are
  verbatim from the `Theorems/Thm_Polynomial_*.lean` wrappers of
  `anthropics/fermats-last-theorem@aa2d8b3`, whose `solution` declarations
  re-export them. The proofs are the pin's, transcribed; the pin's own file is
  `P2M/Sol/S_Polynomial_mem_range_of_unique_common_root.lean`, which also carries
  the other two lemmas (the three `S_Polynomial_*` files are copies of it, so the
  segment has one 182-line generic file, not three).

  FLT provenance, pinned `aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_Polynomial_mem_range_of_unique_common_root.lean

  This is the port's first generic module and the first member of
  `FLTForHuman/FieldTheory/`: nothing here mentions `jq`, `qExpand`,
  `LaurentSeries` or the port at all, and the module imports only mathlib (the
  pin's two imports, plus `Mathlib.Analysis.Complex.Basic` for the concrete
  instantiations in the last section). It is where future generic prerequisites
  of a `ModularCurve` theory belong, rather than inside a theory directory.
-/
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

noncomputable section

namespace Polynomial

/-- **A split squarefree polynomial with a unique common root has a rational
root.** Let `F ⊆ L` be fields, `A ≠ 0` a polynomial over `F` whose image in `L`
splits with distinct roots, and `x ∈ L` the *unique* common root of `A` and `B`.
Then `x` is in the image of `F`.

The principle is math/010 §4: the minimal polynomial of `x` over `F` divides both
`A` and `B`, so if `x` were not rational that minimal polynomial would have a
second root, also common to `A` and `B`.

The proof works with `g = gcd A B`: `g` has `x` as its only root in `L`, so
`g.natDegree = 1` and `g` splits, and `Splits.mem_range_of_isRoot` puts `x` in
`F`. -/
theorem mem_range_of_unique_common_root {F L : Type*} [Field F] [Field L] [Algebra F L]
    (A B : Polynomial F) (hA : A ≠ 0) (hAs : (A.map (algebraMap F L)).Splits)
    (hAnd : (A.map (algebraMap F L)).roots.Nodup) (x : L) (hxA : Polynomial.aeval x A = 0)
    (hxB : Polynomial.aeval x B = 0) (huniq : ∀ y : L, Polynomial.aeval y A = 0 → Polynomial.aeval y B = 0 → y = x) :
    x ∈ (algebraMap F L).range := by
  classical
  set i := algebraMap F L with hi
  set g := EuclideanDomain.gcd A B with hg
  have hg0 : g ≠ 0 := fun h => hA (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  have hgA : g ∣ A := EuclideanDomain.gcd_dvd_left _ _
  have hgB : g ∣ B := EuclideanDomain.gcd_dvd_right _ _
  have hAm0 : A.map i ≠ 0 := (Polynomial.map_ne_zero_iff i.injective).mpr hA
  have hgm0 : g.map i ≠ 0 := (Polynomial.map_ne_zero_iff i.injective).mpr hg0

  have hxg : Polynomial.aeval x g = 0 := by
    rw [hg, EuclideanDomain.gcd_eq_gcd_ab A B, map_add, map_mul, map_mul, hxA, hxB, zero_mul, zero_mul,
      add_zero]

  have hroot_eq : ∀ y ∈ (g.map i).roots, y = x := by
    intro y hy
    rw [Polynomial.mem_roots hgm0, Polynomial.IsRoot.def, Polynomial.eval_map_algebraMap] at hy
    refine huniq y ?_ ?_
    · obtain ⟨c, hc⟩ := hgA
      rw [hc, map_mul, hy, zero_mul]
    · obtain ⟨c, hc⟩ := hgB
      rw [hc, map_mul, hy, zero_mul]
  have hxmem : x ∈ (g.map i).roots := by
    rw [Polynomial.mem_roots hgm0, Polynomial.IsRoot.def, Polynomial.eval_map_algebraMap]; exact hxg

  have hle : (g.map i).roots ≤ (A.map i).roots := Polynomial.roots.le_of_dvd hAm0 (Polynomial.map_dvd i hgA)
  have hnd : (g.map i).roots.Nodup := Multiset.nodup_of_le hle hAnd
  have hcount : (g.map i).roots.count x = Multiset.card (g.map i).roots :=
    Multiset.count_eq_card.mpr fun y hy => (hroot_eq y hy).symm
  have hcard : Multiset.card (g.map i).roots = 1 := by
    have h1 : (g.map i).roots.count x ≤ 1 := Multiset.nodup_iff_count_le_one.mp hnd x
    have h2 : 0 < (g.map i).roots.count x := Multiset.count_pos.mpr hxmem
    omega

  have hgs : (g.map i).Splits := Polynomial.Splits.of_dvd hAs hAm0 (Polynomial.map_dvd i hgA)
  have hdeg : g.natDegree = 1 := by
    rw [← Polynomial.natDegree_map i, hgs.natDegree_eq_card_roots, hcard]
  have hgsF : g.Splits := Polynomial.Splits.of_natDegree_eq_one hdeg
  exact hgsF.mem_range_of_isRoot hg0 ((Polynomial.mem_roots hgm0).mp hxmem)

/-- **A polynomial constant on enough points is constant on the base field.** Let
`g ∈ F[Y]`, `x ∈ L` and a finite set `s ⊆ L` with `g.natDegree < s.card`. If
`aeval y g = x` for every `y ∈ s`, then `x` is in the image of `F`.

The principle is math/010 §6's non-membership step: `g - C x` vanishes on `s`,
and a polynomial with more roots than its degree is zero, so `g` is the constant
`x` — a base-field constant. -/
theorem mem_range_of_eval_eq_const {F L : Type*} [Field F] [Field L] [Algebra F L]
    (g : Polynomial F) (x : L) (s : Finset L) (hcard : g.natDegree < s.card)
    (hval : ∀ y ∈ s, Polynomial.aeval y g = x) : x ∈ (algebraMap F L).range := by
  classical
  set i := algebraMap F L
  set Q : Polynomial L := g.map i - Polynomial.C x with hQ
  have hQdeg : Q.natDegree ≤ g.natDegree := by
    refine (Polynomial.natDegree_sub_le _ _).trans ?_
    rw [Polynomial.natDegree_map, Polynomial.natDegree_C, max_eq_left (Nat.zero_le _)]
  have hQ0 : Q = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' Q s (fun y hy => ?_) (hQdeg.trans_lt hcard)
    rw [hQ, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_map_algebraMap, hval y hy, sub_self]
  have hconst : g.map i = Polynomial.C x := sub_eq_zero.mp hQ0
  refine ⟨g.coeff 0, ?_⟩
  have := congrArg (fun P : Polynomial L => P.coeff 0) hconst
  simpa only [Polynomial.coeff_map, Polynomial.coeff_C_zero] using this

/-- **A base-fixing automorphism cycling all but one root forces
irreducibility.** Let `P` be monic over `F` and split with distinct roots over
`L`; let `σ : L ≃+* L` fix the image of `F` pointwise and cycle the roots
`r 0, …, r (n-1)` (the `Multiset.range n`) by `i ↦ (i + 1) % n`; and let the
remaining root `y₀` be outside the image of `F`. Then `P` is irreducible over
`F`.

The principle is math/010 §6's degree step: `Φ_p`'s roots are `j(q^{p²})`, fixed
by the nome-multiplication automorphism, together with the `p` roots
`j(ζ_p^b q)`, which it cycles, and `j(q^{p²})` is not in the base field — so the
minimal polynomial has degree `p + 1` (and, after peeling the known rational
factor, `p` for the later prime powers).

The proof counts roots. Any monic factorisation `P = f * g` puts the roots of `g`
inside the cycle; if `y₀` is a root of `f` then `g` cannot contain `y₀` (the roots
are distinct), and `σ`-stability of the root set of `g` then forces the whole cycle
into it. So `n ≤ g.natDegree`, while `f.natDegree ≥ 1` because `f` has the
non-rational root `y₀`; from
`f.natDegree + g.natDegree = n + 1` both are pinned, `g.natDegree = 0` follows,
and that is the `natDegree` criterion for irreducibility. -/
theorem irreducible_of_transitive_ringAut {F L : Type*} [Field F] [Field L] [Algebra F L]
    (P : Polynomial F) (hP : P.Monic) (hPs : (P.map (algebraMap F L)).Splits) (σ : L ≃+* L)
    (hσ : ∀ a : F, σ (algebraMap F L a) = algebraMap F L a) (y₀ : L) (r : ℕ → L) (n : ℕ)
    (hroots : (P.map (algebraMap F L)).roots = y₀ ::ₘ (Multiset.range n).map r)
    (hnodup : (P.map (algebraMap F L)).roots.Nodup) (hcycle : ∀ i < n, σ (r i) = r ((i + 1) % n))
    (hy₀ : y₀ ∉ (algebraMap F L).range) : Irreducible P := by
  classical
  set i := algebraMap F L with hi
  have hσi : (σ : L →+* L).comp i = i := RingHom.ext fun a => hσ a
  have hPm0 : P.map i ≠ 0 := (Polynomial.map_ne_zero_iff i.injective).mpr hP.ne_zero
  have hPdeg : P.natDegree = n + 1 := by
    rw [← Polynomial.natDegree_map i, hPs.natDegree_eq_card_roots, hroots, Multiset.card_cons, Multiset.card_map,
      Multiset.card_range]

  have hy₀_notin : y₀ ∉ (Multiset.range n).map r := by
    rw [hroots] at hnodup; exact (Multiset.nodup_cons.mp hnodup).1
  have hr_nodup : ((Multiset.range n).map r).Nodup := by
    rw [hroots] at hnodup; exact (Multiset.nodup_cons.mp hnodup).2

  have key : ∀ f g : Polynomial F, f.Monic → g.Monic → f * g = P → y₀ ∈ (f.map i).roots → g.natDegree = 0 := by
    intro f g hf hg hfg hyf
    have hfm0 : f.map i ≠ 0 := (Polynomial.map_ne_zero_iff i.injective).mpr hf.ne_zero
    have hgm0 : g.map i ≠ 0 := (Polynomial.map_ne_zero_iff i.injective).mpr hg.ne_zero
    have hsplit : (P.map i).roots = (f.map i).roots + (g.map i).roots := by
      rw [← hfg, Polynomial.map_mul, Polynomial.roots_mul (mul_ne_zero hfm0 hgm0)]
    have hgle : (g.map i).roots ≤ (P.map i).roots := by rw [hsplit]; exact Multiset.le_add_left _ _
    have hg_nd : (g.map i).roots.Nodup := Multiset.nodup_of_le hgle hnodup

    have hy₀g : y₀ ∉ (g.map i).roots := by
      intro hyg
      have h2 : 2 ≤ (P.map i).roots.count y₀ := by
        rw [hsplit, Multiset.count_add]
        have := Multiset.count_pos.mpr hyf; have := Multiset.count_pos.mpr hyg; omega
      have h1 := Multiset.nodup_iff_count_le_one.mp hnodup y₀
      omega

    have hgsub : ∀ y ∈ (g.map i).roots, y ∈ (Multiset.range n).map r := by
      intro y hy
      have : y ∈ (P.map i).roots := Multiset.mem_of_le hgle hy
      rw [hroots, Multiset.mem_cons] at this
      rcases this with rfl | h
      · exact absurd hy hy₀g
      · exact h

    have hgs : (g.map i).Splits := Polynomial.Splits.of_dvd hPs hPm0 (by rw [← hfg, Polynomial.map_mul]; exact dvd_mul_left _ _)
    have hstable : ((g.map i).roots).map (σ : L →+* L) = (g.map i).roots := by
      rw [← hgs.roots_map (σ : L →+* L), Polynomial.map_map, hσi]
    have hmemσ : ∀ y ∈ (g.map i).roots, σ y ∈ (g.map i).roots := by
      intro y hy
      rw [← hstable]; exact Multiset.mem_map.mpr ⟨y, hy, rfl⟩

    by_contra hgdeg
    have hgroots_ne : (g.map i).roots ≠ 0 := by
      intro h0
      apply hgdeg
      rw [← Polynomial.natDegree_map i, hgs.natDegree_eq_card_roots, h0, Multiset.card_zero]
    obtain ⟨y, hy⟩ := Multiset.exists_mem_of_ne_zero hgroots_ne
    obtain ⟨j₀, hj₀, rfl⟩ := Multiset.mem_map.mp (hgsub y hy)
    rw [Multiset.mem_range] at hj₀
    have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hj₀
    have horbit : ∀ k : ℕ, r ((j₀ + k) % n) ∈ (g.map i).roots := by
      intro k
      induction k with
      | zero => rwa [add_zero, Nat.mod_eq_of_lt hj₀]
      | succ k ih =>
        have h1 := hmemσ _ ih
        rw [hcycle _ (Nat.mod_lt _ hnpos), Nat.mod_add_mod, add_assoc] at h1
        exact h1
    have hall : ∀ j < n, r j ∈ (g.map i).roots := by
      intro j hj
      have := horbit (j + n - j₀)
      have e : (j₀ + (j + n - j₀)) % n = j := by
        rw [show j₀ + (j + n - j₀) = j + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
      rwa [e] at this
    have hle : (Multiset.range n).map r ≤ (g.map i).roots := by
      rw [Multiset.le_iff_subset hr_nodup]
      intro y hy
      obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.mp hy
      exact hall j (Multiset.mem_range.mp hj)
    have hgdeg_ge : n ≤ g.natDegree := by
      rw [← Polynomial.natDegree_map i, hgs.natDegree_eq_card_roots]
      simpa using Multiset.card_le_card hle

    have hsum : f.natDegree + g.natDegree = n + 1 := by rw [← hf.natDegree_mul hg, hfg, hPdeg]
    have hfdeg_pos : 1 ≤ f.natDegree := by
      rw [← Polynomial.natDegree_map i]
      have := Polynomial.card_roots' (f.map i)
      have hpos : 0 < Multiset.card (f.map i).roots := Multiset.card_pos_iff_exists_mem.mpr ⟨y₀, hyf⟩
      omega
    have hfdeg : f.natDegree = 1 := by omega
    have hfs : f.Splits := Polynomial.Splits.of_natDegree_eq_one hfdeg
    exact hy₀ (hfs.mem_range_of_isRoot hf.ne_zero ((Polynomial.mem_roots hfm0).mp hyf))

  rw [hP.irreducible_iff_natDegree]
  refine ⟨fun h1 => by simp [h1] at hPdeg, fun f g hf hg hfg => ?_⟩
  have hfm0 : f.map i ≠ 0 := (Polynomial.map_ne_zero_iff i.injective).mpr hf.ne_zero
  have hgm0 : g.map i ≠ 0 := (Polynomial.map_ne_zero_iff i.injective).mpr hg.ne_zero
  have hy₀P : y₀ ∈ (P.map i).roots := by rw [hroots]; exact Multiset.mem_cons_self _ _
  rw [← hfg, Polynomial.map_mul, Polynomial.roots_mul (mul_ne_zero hfm0 hgm0), Multiset.mem_add] at hy₀P
  rcases hy₀P with h | h
  · exact Or.inr (key f g hf hg hfg h)
  · exact Or.inl (key g f hg hf (by rw [mul_comm]; exact hfg) h)

end Polynomial

/-! ## The wire test: concrete instantiations

Three checked `example`s over `ℚ ⊆ ℂ`, one per lemma, exercising every hypothesis
and showing the lemma is non-vacuous. They live here rather than in
`spec/ModularCurveConsumer.lean` so that the consumer stays untouched (the topic's
definition of done), and they are `example`s rather than named declarations so
`spec/check_flt_statements.py` sees nothing new. This is also the reason the
module carries `Mathlib.Analysis.Complex.Basic`: the three lemmas themselves need
only the pin's two imports.

For the third lemma the chosen automorphism is `RingEquiv.refl`; a nontrivial
`σ` instance needs a cubic with exactly one real root (so that complex
conjugation fixes that root and 2-cycles the other two), and mathlib has no
explicit real cube roots, so that instance is not available cheaply. The
hypotheses `hσ` and `hcycle` are nevertheless satisfied and used with `n = 1`. -/

namespace Polynomial

/-- `mem_range_of_unique_common_root` at `A = (X - 1)(X - 2)`, `B = X - 1`:
`1` is the unique common root, and it is rational. -/
example : (1 : ℂ) ∈ (algebraMap ℚ ℂ).range := by
  refine mem_range_of_unique_common_root (F := ℚ) (L := ℂ)
    ((X - C 1) * (X - C 2)) (X - C 1) ?_ ?_ ?_ 1 ?_ ?_ ?_
  · exact mul_ne_zero (X_sub_C_ne_zero 1) (X_sub_C_ne_zero 2)
  · have h : map (algebraMap ℚ ℂ) ((X - C 1) * (X - C 2))
        = (X - C 1) * (X - C 2) := by simp
    rw [h]
    exact Splits.mul (Splits.X_sub_C (1 : ℂ)) (Splits.X_sub_C (2 : ℂ))
  · have h : map (algebraMap ℚ ℂ) ((X - C 1) * (X - C 2))
        = (X - C 1) * (X - C 2) := by simp
    rw [h, roots_mul (mul_ne_zero (X_sub_C_ne_zero (1 : ℂ)) (X_sub_C_ne_zero (2 : ℂ))),
      roots_X_sub_C, roots_X_sub_C]
    norm_num [Multiset.nodup_cons]
  · simp
  · simp
  · intro y hy hz
    simpa [sub_eq_zero] using hz

/-- `mem_range_of_eval_eq_const`: the constant polynomial `3/2` takes the value
`3/2` on the three points `0, 1, 2`, and `0 < 3 = card`. -/
example : ((3 : ℚ) / 2 : ℂ) ∈ (algebraMap ℚ ℂ).range := by
  refine mem_range_of_eval_eq_const (F := ℚ) (L := ℂ) (C ((3 : ℚ) / 2)) ((3 : ℚ) / 2 : ℂ)
    {0, 1, 2} ?_ ?_
  · simp
  · intro y hy
    simp

/-- `irreducible_of_transitive_ringAut`: `X² + 1` splits over `ℂ` with the two
distinct roots `I` and `-I`; the base-fixing automorphism `RingEquiv.refl` sends
`-I` to itself (the `n = 1` cycle), `I ∉ ℚ`, and the conclusion is that `X² + 1`
is irreducible over `ℚ`. -/
example : Irreducible (X ^ 2 + C (1 : ℚ)) := by
  have hI : (C Complex.I : ℂ[X]) ^ 2 = -(1 : ℂ[X]) := by
    rw [← Polynomial.C_pow, sq, Complex.I_mul_I]
    simp
  have hfac : (X ^ 2 + C (1 : ℂ) : ℂ[X]) = (X - C Complex.I) * (X + C Complex.I) := by
    ring_nf
    simp only [Polynomial.C_1]
    rw [hI]
    ring
  have hmap : map (algebraMap ℚ ℂ) (X ^ 2 + C (1 : ℚ)) = (X ^ 2 + C (1 : ℂ) : ℂ[X]) := by
    simp
  have h : map (algebraMap ℚ ℂ) (X ^ 2 + C (1 : ℚ)) = (X - C Complex.I) * (X + C Complex.I) :=
    hmap.trans hfac
  have hne : ¬ Complex.I = -Complex.I := by
    intro hh
    have h2 : (2 : ℂ) * Complex.I = 0 := by
      rw [two_mul]; nth_rewrite 1 [hh]; exact neg_add_cancel _
    rcases mul_eq_zero.mp h2 with h | h
    · exact two_ne_zero h
    · exact Complex.I_ne_zero h
  have hroots' : ((X - C Complex.I) * (X + C Complex.I) : ℂ[X]).roots
      = Complex.I ::ₘ (Multiset.range 1).map (fun _ => -Complex.I) := by
    rw [roots_mul (mul_ne_zero (X_sub_C_ne_zero Complex.I) (X_add_C_ne_zero Complex.I)),
      roots_X_sub_C, roots_X_add_C, Multiset.singleton_add]
    simp
  have hnod : ((X - C Complex.I) * (X + C Complex.I) : ℂ[X]).roots.Nodup := by
    rw [hroots']
    simp [Multiset.nodup_cons, Multiset.mem_singleton, hne]
  refine irreducible_of_transitive_ringAut (F := ℚ) (L := ℂ)
    (X ^ 2 + C 1) (monic_X_pow_add_C (a := (1 : ℚ)) (n := 2) (by norm_num)) ?_
    (RingEquiv.refl ℂ) (fun a => rfl) Complex.I (fun _ => -Complex.I) 1 ?_ ?_ ?_ ?_
  · rw [h]
    exact Splits.mul (Splits.X_sub_C Complex.I) (Splits.X_add_C Complex.I)
  · rw [h]; exact hroots'
  · rw [h]; exact hnod
  · intro i hi
    simp
  · rintro ⟨q, hq⟩
    have := congrArg Complex.im hq
    simp [Complex.I_im] at this

end Polynomial

end
