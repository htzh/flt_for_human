/-
  Coefficients of a factor, forced by the coefficients of a product: two
  coefficient-membership statements about `PowerSeries`.

  1. `PowerSeries.coeff_mem_subring_of_coeff_mul_mem` — dividing by a unit-led power
     series keeps coefficients in a subring.  If the coefficients of `U` lie in a
     subring `R ⊆ K`, `U` vanishes below `m₀` and its `m₀`-th coefficient is a unit of
     `R`, and the coefficients of `P * U` lie in `R` below `L`, then the coefficients
     of `P` lie in `R` below `L - m₀`.  The proof is strong induction on the index:
     the `(n + m₀)`-th coefficient of `P * U` is `coeff n P * coeff m₀ U` plus a sum
     over the rest of the antidiagonal, whose terms are either already known (below
     `n`) or vanish (`U` below `m₀`).
  2. `PowerSeries.exists_sum_smul_eq_of_forall_coeff_mem` — coefficient descent.  A
     `K₀`-linear combination `∑ c i • g i` of series `g i` with coefficients in a
     subfield `K₀ ⊆ L` that happens to have all its coefficients in `K₀` is the same
     element as a `K₀`-linear combination whose coefficients lie in `K₀`.  The proof
     splits the injection `K₀ → L` of `K₀`-vector spaces with a linear left inverse
     `π` and replaces `c i` by `π (c i)`.

  FLT provenance, pinned `aa2d8b3`: the union of two pin leaves,
  `P2M/Sol/S_PowerSeries_coeff_mem_subring_of_coeff_mul_mem.lean` (41 lines) and
  `P2M/Sol/S_PowerSeries_exists_sum_smul_eq_of_forall_coeff_mem.lean` (38 lines),
  79 pin lines together.  Neither pin file has an inner namespace: both headlines
  sit directly under `namespace PowerSeries` and they stay there, at the pin's own
  names.  For these two rows the pin's top-level `solution` *is* the proof (it is
  not a wrapper around an inner `main`), so each headline carries its `solution`
  body verbatim; that is the whole port.  The statements are the `Theorems/`
  wrappers verbatim.

  Home.  Both statements name only `PowerSeries` (plus `Subring` / `Subfield`), so
  they are homed beside the mathlib mirror `RingTheory/PowerSeries/`, as a mathlib
  supplement.  What mathlib `v4.34.0` has is
  `Mathlib/RingTheory/PowerSeries/CoeffMulMem.lean`, whose `coeff_mul_mem_ideal_*`
  is the **ideal** version of the product statement; the `Subring` division of (1)
  and the subfield descent of (2) are absent.  Neither statement is strengthened
  toward the ideal version (porting playbook §4).

  Drift.  The pin's bare `import Mathlib` became the modules the proofs name (the
  statements and proofs elaborate unchanged; the import list is the only edit).

  spec-pin: Theorems/Thm_PowerSeries_coeff_mem_subring_of_coeff_mul_mem.lean
  spec-pin: Theorems/Thm_PowerSeries_exists_sum_smul_eq_of_forall_coeff_mem.lean
  spec-pin: P2M/Sol/S_PowerSeries_coeff_mem_subring_of_coeff_mul_mem.lean
  spec-pin: P2M/Sol/S_PowerSeries_exists_sum_smul_eq_of_forall_coeff_mem.lean
-/
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Order.Antidiag.Prod
import Mathlib.LinearAlgebra.Basis.VectorSpace

set_option autoImplicit false

namespace PowerSeries

theorem coeff_mem_subring_of_coeff_mul_mem {K : Type*} [CommRing K] (R : Subring K)
    (P U : PowerSeries K) (m₀ L : ℕ)
    (hU₀ : ∀ n : ℕ, n < m₀ → PowerSeries.coeff n U = 0)
    (hU₁ : ∃ v ∈ R, v * PowerSeries.coeff m₀ U = 1)
    (hU : ∀ n : ℕ, PowerSeries.coeff n U ∈ R)
    (hPU : ∀ n : ℕ, n < L → PowerSeries.coeff n (P * U) ∈ R)
    (n : ℕ) (hn : n + m₀ < L) :
    PowerSeries.coeff n P ∈ R := by
  obtain ⟨v, hv, hvu⟩ := hU₁
  induction n using Nat.strong_induction_on with
  | _ n ih =>

    have hsum := PowerSeries.coeff_mul (n + m₀) P U

    have hmem : (n, m₀) ∈ Finset.HasAntidiagonal.antidiagonal (n + m₀) := by simp
    rw [← Finset.add_sum_erase _ _ hmem] at hsum

    have hrest : ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (n + m₀)).erase (n, m₀), PowerSeries.coeff x.1 P * PowerSeries.coeff x.2 U ∈ R := by
      refine Subring.sum_mem _ fun x hx => ?_
      obtain ⟨hne, hx⟩ := Finset.mem_erase.1 hx
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      rcases lt_trichotomy x.1 n with hlt | heq | hgt
      · exact Subring.mul_mem _ (ih x.1 hlt (by omega)) (hU x.2)
      · exfalso; apply hne
        have : x.2 = m₀ := by omega
        exact Prod.ext heq this
      · have : x.2 < m₀ := by omega
        rw [hU₀ x.2 this, mul_zero]
        exact Subring.zero_mem _

    have hkey : PowerSeries.coeff n P = v * (PowerSeries.coeff (n + m₀) (P * U) -
        ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (n + m₀)).erase (n, m₀), PowerSeries.coeff x.1 P * PowerSeries.coeff x.2 U) := by
      rw [hsum, add_sub_cancel_right, mul_comm v, mul_assoc, mul_comm _ v, hvu, mul_one]
    rw [hkey]
    exact Subring.mul_mem _ hv (Subring.sub_mem _ (hPU _ hn) hrest)

theorem exists_sum_smul_eq_of_forall_coeff_mem
    {L : Type} [Field L] (K₀ : Subfield L) {n : ℕ} (g : Fin n → PowerSeries L)
    (hg : ∀ (i : Fin n) (m : ℕ), (g i).coeff m ∈ K₀)
    (c : Fin n → L) (h : ∀ m : ℕ, (∑ i, c i • g i).coeff m ∈ K₀) :
    ∃ c' : Fin n → L, (∀ i, c' i ∈ K₀) ∧ ∑ i, c' i • g i = ∑ i, c i • g i := by
  classical

  let ι : K₀ →ₗ[K₀] L := (Algebra.linearMap K₀ L)
  have hι : Function.Injective ι := fun x y h => Subtype.ext (by simpa [ι] using h)
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective ι (LinearMap.ker_eq_bot.mpr hι)
  have hπι : ∀ z : K₀, π (z : L) = z := fun z => by
    have := congrArg (fun f => f z) hπ
    simp [ι] at this
    exact this
  refine ⟨fun i => (π (c i) : L), fun i => (π (c i)).2, ?_⟩
  ext m
  simp only [map_sum, map_smul, smul_eq_mul]

  have hm := h m
  simp only [map_sum, map_smul, smul_eq_mul] at hm

  have key : (π (∑ i, c i * (g i).coeff m) : L) = ∑ i, (π (c i) : L) * (g i).coeff m := by
    rw [map_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    have : c i * (g i).coeff m = ((⟨(g i).coeff m, hg i m⟩ : K₀) : K₀) • c i := by
      rw [Subfield.smul_def]; exact mul_comm _ _
    rw [this, map_smul]

    rw [show (((⟨(g i).coeff m, hg i m⟩ : K₀) • π (c i) : K₀) : L) = ((g i).coeff m) * (π (c i) : L) from rfl]
    exact mul_comm _ _
  rw [← key, hπι ⟨_, hm⟩]

end PowerSeries
