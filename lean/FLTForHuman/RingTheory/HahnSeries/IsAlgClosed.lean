/-
  Hahn series with rational exponents over an algebraically closed field are
  algebraically closed: the generalized Newton–Puiseux theorem in the
  Mac Lane–Kaplansky form (`HahnSeries.isAlgClosed_rat`).

  The mathematics.  `HahnSeries ℚ K` is the Mal'cev–Neumann field of formal series
  `∑_{q ∈ ℚ} a_q t^q` with well-ordered support.  Its value group `ℚ` is divisible
  and linearly ordered, and Kaplansky's theorem says a maximally complete valued
  field with algebraically closed residue field and divisible value group is
  algebraically closed.  The proof below is the generalized Newton–Puiseux
  iteration: a Newton-polygon initial form produces a first approximation whose
  value is larger (`exists_newtonFirstApprox`, `exists_addVal_eval_gt`), nested
  balls have pseudo-limits because of the well-ordered support
  (`IsBallChain.pseudoLimit`), the Kaplansky order on approximations is chain
  complete (`exists_kaplanskyLE_upperBound`), and Zorn's lemma supplies a maximal
  approximation, which is a root (`exists_isRoot_hahnSeries`).  No hypothesis is
  placed on the characteristic.

  FLT provenance, pinned `aa2d8b3`: this is the whole of
  `P2M/Sol/S_HahnSeries_isAlgClosed_rat.lean` (975 lines; the pin's namespace
  `DorgePuiseux`), less that file's top-level `solution`, which is re-proved here
  as the public headline; the statement is
  `Theorems/Thm_HahnSeries_isAlgClosed_rat.lean` verbatim.  Every public
  declaration carries its `-- pin: <name> (<file>:<line>)` comment.

  Home.  The theorem has no FLT content — the statement names only mathlib
  objects (`HahnSeries`, `ℚ`, `IsAlgClosed`) and the development imports only
  mathlib — so it is homed beside the mathlib mirror (`RingTheory/HahnSeries/`),
  not under `ModularCurve`, as a mathlib supplement.  What mathlib `v4.34.0`
  already has is the `Field` instance on Hahn series (`HahnSeries/Summable.lean`);
  its algebraic closedness and any Puiseux development are absent.

  Tier.  The module is **unlisted** (tier 3): not in the checker's `PORT_FILES`,
  so no statement is diffed here directly.  Its public surface is registered in
  `spec/UNWIRED-PUBLIC.md` by the protocol, which recovers each pin original from
  the provenance comment.  The pin's 66 public development declarations stay
  public at the pin's names (no demotion); the pin's 11 `private` helpers stay
  `private`.

  Proof adaptations for mathlib `v4.34.0` — all deprecation renames, no
  mathematical change: `if_neg` -> `ite_eq_right`, `if_pos` -> `ite_eq_left`,
  `dif_pos` -> `dite_eq_left`, `dif_neg` -> `dite_eq_right` (eleven sites).
-/
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.HahnSeries.Valuation
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Order.Zorn

set_option autoImplicit false

open Polynomial HahnSeries
open scoped Classical

noncomputable section

namespace DorgePuiseux

variable {K : Type*} [Field K]

-- pin: newtonInitialForm (S_HahnSeries_isAlgClosed_rat.lean:16)
def newtonInitialForm (f : (HahnSeries ℚ K)[X]) (γ : ℚ) : K[X] :=
  ∑ i ∈ Finset.range (f.natDegree + 1),
    Polynomial.C ((f.coeff i).coeff ((f.natDegree - i : ℕ) • γ)) * Polynomial.X ^ i

-- pin: newtonInitialForm_coeff (S_HahnSeries_isAlgClosed_rat.lean:20)
theorem newtonInitialForm_coeff (f : (HahnSeries ℚ K)[X]) (γ : ℚ) (k : ℕ)
    (hk : k ≤ f.natDegree) :
    (newtonInitialForm f γ).coeff k = (f.coeff k).coeff ((f.natDegree - k : ℕ) • γ) := by
  unfold newtonInitialForm
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, ite_eq_right (Ne.symm hj), mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)) h

-- pin: newtonInitialForm_natDegree_le (S_HahnSeries_isAlgClosed_rat.lean:32)
theorem newtonInitialForm_natDegree_le (f : (HahnSeries ℚ K)[X]) (γ : ℚ) :
    (newtonInitialForm f γ).natDegree ≤ f.natDegree := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [Polynomial.natDegree_X_pow]
  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)

-- pin: newtonInitialForm_coeff_natDegree (S_HahnSeries_isAlgClosed_rat.lean:39)
theorem newtonInitialForm_coeff_natDegree {f : (HahnSeries ℚ K)[X]} (hf : f.Monic) (γ : ℚ) :
    (newtonInitialForm f γ).coeff f.natDegree = 1 := by
  rw [newtonInitialForm_coeff f γ f.natDegree le_rfl, Nat.sub_self, zero_smul,
    Polynomial.Monic.coeff_natDegree hf]
  simp [HahnSeries.coeff_one]

-- pin: newtonInitialForm_monic (S_HahnSeries_isAlgClosed_rat.lean:45)
theorem newtonInitialForm_monic {f : (HahnSeries ℚ K)[X]} (hf : f.Monic) (γ : ℚ) :
    (newtonInitialForm f γ).Monic := by
  rw [Polynomial.Monic, Polynomial.leadingCoeff,
    show (newtonInitialForm f γ).natDegree = f.natDegree from
      le_antisymm (newtonInitialForm_natDegree_le f γ)
        (Polynomial.le_natDegree_of_ne_zero
          (by rw [newtonInitialForm_coeff_natDegree hf]; exact one_ne_zero))]
  exact newtonInitialForm_coeff_natDegree hf γ

-- pin: newtonInitialForm_natDegree (S_HahnSeries_isAlgClosed_rat.lean:54)
theorem newtonInitialForm_natDegree {f : (HahnSeries ℚ K)[X]} (hf : f.Monic) (γ : ℚ) :
    (newtonInitialForm f γ).natDegree = f.natDegree :=
  le_antisymm (newtonInitialForm_natDegree_le f γ)
    (Polynomial.le_natDegree_of_ne_zero
      (by rw [newtonInitialForm_coeff_natDegree hf]; exact one_ne_zero))

private theorem nsmul_sub_nsmul {n i : ℕ} (hi : i ≤ n) (γ : ℚ) :
    n • γ - i • γ = (n - i : ℕ) • γ := by
  rw [eq_comm, eq_sub_iff_add_eq, ← add_nsmul, Nat.sub_add_cancel hi]

-- pin: coeff_eval_single (S_HahnSeries_isAlgClosed_rat.lean:64)
theorem coeff_eval_single (f : (HahnSeries ℚ K)[X]) (γ : ℚ) (c : K) (g : ℚ) :
    (f.eval (HahnSeries.single γ c)).coeff g =
      ∑ i ∈ Finset.range (f.natDegree + 1), (f.coeff i).coeff (g - i • γ) * c ^ i := by
  rw [Polynomial.eval_eq_sum_range, HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [HahnSeries.single_pow, HahnSeries.coeff_mul_single]

-- pin: coeff_eval_single_top (S_HahnSeries_isAlgClosed_rat.lean:71)
theorem coeff_eval_single_top (f : (HahnSeries ℚ K)[X]) (γ : ℚ) (c : K) :
    (f.eval (HahnSeries.single γ c)).coeff (f.natDegree • γ) =
      (newtonInitialForm f γ).eval c := by
  rw [coeff_eval_single, newtonInitialForm, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [nsmul_sub_nsmul (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)),
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

-- pin: IsNewtonSlopeBound (S_HahnSeries_isAlgClosed_rat.lean:79)
def IsNewtonSlopeBound (f : (HahnSeries ℚ K)[X]) (γ : ℚ) : Prop :=
  ∀ i ≤ f.natDegree, f.coeff i ≠ 0 → (f.natDegree - i : ℕ) • γ ≤ (f.coeff i).order

-- pin: coeff_eval_single_of_lt (S_HahnSeries_isAlgClosed_rat.lean:82)
theorem coeff_eval_single_of_lt {f : (HahnSeries ℚ K)[X]} {γ : ℚ}
    (hslope : IsNewtonSlopeBound f γ) (c : K) {g : ℚ} (hg : g < f.natDegree • γ) :
    (f.eval (HahnSeries.single γ c)).coeff g = 0 := by
  rw [coeff_eval_single]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hin : i ≤ f.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rcases eq_or_ne (f.coeff i) 0 with hzero | hne
  · simp [hzero]
  · have hlt : g - i • γ < (f.coeff i).order := by
      calc g - i • γ < f.natDegree • γ - i • γ := by linarith
        _ = (f.natDegree - i : ℕ) • γ := nsmul_sub_nsmul hin γ
        _ ≤ (f.coeff i).order := hslope i hin hne
    rw [HahnSeries.coeff_eq_zero_of_lt_order hlt, zero_mul]

-- pin: newtonStep_orderTop_lt (S_HahnSeries_isAlgClosed_rat.lean:96)
theorem newtonStep_orderTop_lt {f : (HahnSeries ℚ K)[X]} {γ : ℚ}
    (hslope : IsNewtonSlopeBound f γ) {c : K} (hc : (newtonInitialForm f γ).IsRoot c) :
    ((f.natDegree • γ : ℚ) : WithTop ℚ) <
      (f.eval (HahnSeries.single γ c)).orderTop := by
  rcases eq_or_ne (f.eval (HahnSeries.single γ c)) 0 with heq | hne
  · rw [heq, HahnSeries.orderTop_zero]; exact WithTop.coe_lt_top _
  · rw [← HahnSeries.order_eq_orderTop_of_ne_zero hne, WithTop.coe_lt_coe]
    by_contra hle
    push Not at hle
    rcases lt_or_eq_of_le hle with hlt | heq
    ·
      have horder : (f.eval (HahnSeries.single γ c)).coeff
          (f.eval (HahnSeries.single γ c)).order ≠ 0 :=
        HahnSeries.coeff_order_eq_zero.not.mpr hne
      exact horder (coeff_eval_single_of_lt hslope c hlt)
    ·
      have horder : (f.eval (HahnSeries.single γ c)).coeff (f.natDegree • γ) ≠ 0 := by
        rw [← heq]; exact HahnSeries.coeff_order_eq_zero.not.mpr hne
      rw [coeff_eval_single_top, Polynomial.IsRoot.eq_zero hc] at horder
      exact horder rfl

-- pin: newtonStep_addVal_lt (S_HahnSeries_isAlgClosed_rat.lean:117)
theorem newtonStep_addVal_lt {f : (HahnSeries ℚ K)[X]} {γ : ℚ}
    (hslope : IsNewtonSlopeBound f γ) {c : K} (hc : (newtonInitialForm f γ).IsRoot c) :
    ((f.natDegree • γ : ℚ) : WithTop ℚ) <
      HahnSeries.addVal ℚ K (f.eval (HahnSeries.single γ c)) := by
  rw [HahnSeries.addVal_apply]; exact newtonStep_orderTop_lt hslope hc

private def slopeSupport (f : (HahnSeries ℚ K)[X]) : Finset ℕ :=
  (Finset.range f.natDegree).filter (fun j => f.coeff j ≠ 0)

private theorem slopeSupport_nonempty {f : (HahnSeries ℚ K)[X]} (hdeg : 1 ≤ f.natDegree)
    (h0 : f.coeff 0 ≠ 0) : (slopeSupport f).Nonempty :=
  ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hdeg, h0⟩⟩

-- pin: exists_newtonSlope (S_HahnSeries_isAlgClosed_rat.lean:130)
theorem exists_newtonSlope {f : (HahnSeries ℚ K)[X]} (hf : f.Monic)
    (hdeg : 1 ≤ f.natDegree) (h0 : f.coeff 0 ≠ 0) :
    ∃ γ : ℚ, IsNewtonSlopeBound f γ ∧
      ∃ j < f.natDegree, (newtonInitialForm f γ).coeff j ≠ 0 := by
  classical
  set n := f.natDegree

  set φ : ℕ → ℚ := fun j => (f.coeff j).order / (n - j : ℕ)
  obtain ⟨j₀, hj₀mem, hj₀min⟩ :=
    Finset.exists_min_image (slopeSupport f) φ (slopeSupport_nonempty hdeg h0)
  set γ : ℚ := φ j₀
  obtain ⟨hj₀lt, hj₀ne⟩ := Finset.mem_filter.mp hj₀mem
  rw [Finset.mem_range] at hj₀lt
  have hnj₀pos : (0 : ℚ) < ((n - j₀ : ℕ) : ℚ) := by
    exact_mod_cast Nat.sub_pos_of_lt hj₀lt
  refine ⟨γ, ?_, j₀, hj₀lt, ?_⟩
  ·
    intro i hi hne
    rcases lt_or_eq_of_le hi with hlt | heq
    ·
      have hmem : i ∈ slopeSupport f :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hne⟩
      have hni : (0 : ℚ) < ((n - i : ℕ) : ℚ) := by
        exact_mod_cast Nat.sub_pos_of_lt hlt
      have hle : γ ≤ φ i := hj₀min i hmem
      rw [nsmul_eq_mul]
      calc ((n - i : ℕ) : ℚ) * γ ≤ ((n - i : ℕ) : ℚ) * φ i := by
            exact mul_le_mul_of_nonneg_left hle (le_of_lt hni)
        _ = (f.coeff i).order := by
            simp only [φ]; field_simp
    ·
      subst heq
      simp [hf.coeff_natDegree, HahnSeries.order_one]
  ·
    rw [newtonInitialForm_coeff f γ j₀ (le_of_lt hj₀lt)]

    have heq : ((n - j₀ : ℕ) • γ : ℚ) = (f.coeff j₀).order := by
      rw [nsmul_eq_mul]
      simp only [γ, φ]; field_simp
    rw [heq, ← HahnSeries.leadingCoeff_eq]
    exact HahnSeries.leadingCoeff_ne_zero.mpr hj₀ne

-- pin: exists_ne_zero_root_of_coeff_ne_zero (S_HahnSeries_isAlgClosed_rat.lean:172)
theorem exists_ne_zero_root_of_coeff_ne_zero [IsAlgClosed K] {p : K[X]} (hp : p.Monic)
    {j : ℕ} (hj : j < p.natDegree) (hcoeff : p.coeff j ≠ 0) :
    ∃ c, c ≠ 0 ∧ p.IsRoot c := by
  by_contra h
  push Not at h

  have hsplit : p.Splits := IsAlgClosed.splits p
  have hprod := hsplit.eq_prod_roots_of_monic hp

  have hall0 : ∀ r ∈ p.roots, r = 0 := fun r hr =>
    by_contra fun hne => (h r hne) (Polynomial.isRoot_of_mem_roots hr)

  have hcard : p.roots.card = p.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hroots : p.roots = Multiset.replicate p.natDegree 0 := by
    rw [← hcard]
    exact Multiset.eq_replicate_card.mpr hall0

  rw [hroots] at hprod
  simp only [Multiset.map_replicate, map_zero, sub_zero, Multiset.prod_replicate] at hprod

  rw [hprod, Polynomial.coeff_X_pow] at hcoeff
  exact hcoeff (ite_eq_right (Nat.ne_of_lt hj))

-- pin: exists_newtonFirstApprox (S_HahnSeries_isAlgClosed_rat.lean:195)
theorem exists_newtonFirstApprox [IsAlgClosed K] {f : (HahnSeries ℚ K)[X]} (hf : f.Monic)
    (hdeg : 1 ≤ f.natDegree) (h0 : f.coeff 0 ≠ 0) :
    ∃ γ : ℚ, ∃ c : K, c ≠ 0 ∧
      ((f.natDegree • γ : ℚ) : WithTop ℚ) <
        HahnSeries.addVal ℚ K (f.eval (HahnSeries.single γ c)) := by
  obtain ⟨γ, hslope, j, hjlt, hjcoeff⟩ := exists_newtonSlope hf hdeg h0
  obtain ⟨c, hcne, hcroot⟩ := exists_ne_zero_root_of_coeff_ne_zero
    (newtonInitialForm_monic hf γ) (by rwa [newtonInitialForm_natDegree hf]) hjcoeff
  exact ⟨γ, c, hcne, newtonStep_addVal_lt hslope hcroot⟩

-- pin: isRoot_zero_or_exists_newtonFirstApprox (S_HahnSeries_isAlgClosed_rat.lean:205)
theorem isRoot_zero_or_exists_newtonFirstApprox [IsAlgClosed K]
    {f : (HahnSeries ℚ K)[X]} (hf : f.Monic) (hdeg : 1 ≤ f.natDegree) :
    f.IsRoot 0 ∨ ∃ γ : ℚ, ∃ c : K, c ≠ 0 ∧
      ((f.natDegree • γ : ℚ) : WithTop ℚ) <
        HahnSeries.addVal ℚ K (f.eval (HahnSeries.single γ c)) := by
  rcases eq_or_ne (f.coeff 0) 0 with h0 | h0
  · left; rw [Polynomial.IsRoot, ← Polynomial.coeff_zero_eq_eval_zero, h0]
  · right; exact exists_newtonFirstApprox hf hdeg h0

end DorgePuiseux

end

open Polynomial HahnSeries
open scoped Classical

noncomputable section

namespace DorgePuiseux

variable {K : Type*} [Field K]

private def evalSlopeSupport (f : (HahnSeries ℚ K)[X]) : Finset ℕ :=
  (Finset.range (f.natDegree + 1)).filter (fun j => 1 ≤ j ∧ f.coeff j ≠ 0)

private theorem evalSlopeSupport_nonempty {f : (HahnSeries ℚ K)[X]} (hf : f.Monic)
    (hdeg : 1 ≤ f.natDegree) : (evalSlopeSupport f).Nonempty :=
  ⟨f.natDegree, Finset.mem_filter.mpr
    ⟨Finset.self_mem_range_succ _, hdeg, by rw [hf.coeff_natDegree]; exact one_ne_zero⟩⟩

private theorem mem_evalSlopeSupport {f : (HahnSeries ℚ K)[X]} {j : ℕ} :
    j ∈ evalSlopeSupport f ↔ j ≤ f.natDegree ∧ 1 ≤ j ∧ f.coeff j ≠ 0 := by
  simp only [evalSlopeSupport, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

-- pin: exists_evalNewtonSlope (S_HahnSeries_isAlgClosed_rat.lean:239)
theorem exists_evalNewtonSlope {f : (HahnSeries ℚ K)[X]} (hf : f.Monic)
    (hdeg : 1 ≤ f.natDegree) :
    ∃ γ : ℚ,
      (∀ j, 1 ≤ j → j ≤ f.natDegree → f.coeff j ≠ 0 →
        (f.coeff 0).order ≤ (f.coeff j).order + j • γ) ∧
      ∃ j₀, 1 ≤ j₀ ∧ j₀ ≤ f.natDegree ∧ f.coeff j₀ ≠ 0 ∧
        (f.coeff 0).order = (f.coeff j₀).order + j₀ • γ := by
  classical
  set δ : ℚ := (f.coeff 0).order

  set ψ : ℕ → ℚ := fun j => (δ - (f.coeff j).order) / (j : ℚ)
  obtain ⟨j₀, hj₀mem, hj₀max⟩ :=
    Finset.exists_max_image (evalSlopeSupport f) ψ (evalSlopeSupport_nonempty hf hdeg)
  obtain ⟨hj₀le, hj₀1, hj₀ne⟩ := mem_evalSlopeSupport.mp hj₀mem
  set γ : ℚ := ψ j₀
  have hj₀pos : (0 : ℚ) < (j₀ : ℚ) := by exact_mod_cast hj₀1
  refine ⟨γ, ?_, j₀, hj₀1, hj₀le, hj₀ne, ?_⟩
  ·
    intro j hj1 hjle hjne
    have hjpos : (0 : ℚ) < (j : ℚ) := by exact_mod_cast hj1
    have hmem : j ∈ evalSlopeSupport f := mem_evalSlopeSupport.mpr ⟨hjle, hj1, hjne⟩
    have hle : ψ j ≤ γ := hj₀max j hmem

    rw [nsmul_eq_mul]
    have hmul : δ - (f.coeff j).order ≤ (j : ℚ) * γ := by
      rw [div_le_iff₀ hjpos] at hle; linarith [hle]
    linarith
  ·
    rw [nsmul_eq_mul]
    have heq : (j₀ : ℚ) * γ = δ - (f.coeff j₀).order := by
      simp only [γ, ψ]; field_simp
    linarith

-- pin: evalEdgeForm (S_HahnSeries_isAlgClosed_rat.lean:272)
def evalEdgeForm (f : (HahnSeries ℚ K)[X]) (γ : ℚ) : K[X] :=
  ∑ j ∈ Finset.range (f.natDegree + 1),
    Polynomial.C ((f.coeff j).coeff ((f.coeff 0).order - j • γ)) * Polynomial.X ^ j

-- pin: evalEdgeForm_coeff (S_HahnSeries_isAlgClosed_rat.lean:276)
theorem evalEdgeForm_coeff (f : (HahnSeries ℚ K)[X]) (γ : ℚ) (k : ℕ) (hk : k ≤ f.natDegree) :
    (evalEdgeForm f γ).coeff k = (f.coeff k).coeff ((f.coeff 0).order - k • γ) := by
  unfold evalEdgeForm
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, ite_eq_right (Ne.symm hj), mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)) h

-- pin: evalEdgeForm_coeff_zero (S_HahnSeries_isAlgClosed_rat.lean:287)
theorem evalEdgeForm_coeff_zero (f : (HahnSeries ℚ K)[X]) (γ : ℚ) :
    (evalEdgeForm f γ).coeff 0 = (f.coeff 0).leadingCoeff := by
  rw [evalEdgeForm_coeff f γ 0 (Nat.zero_le _), zero_smul, sub_zero,
    ← HahnSeries.leadingCoeff_eq]

-- pin: evalEdgeForm_coeff_of_eq (S_HahnSeries_isAlgClosed_rat.lean:292)
theorem evalEdgeForm_coeff_of_eq {f : (HahnSeries ℚ K)[X]} {γ : ℚ} {j₀ : ℕ}
    (hj₀le : j₀ ≤ f.natDegree) (heq : (f.coeff 0).order = (f.coeff j₀).order + j₀ • γ) :
    (evalEdgeForm f γ).coeff j₀ = (f.coeff j₀).leadingCoeff := by
  rw [evalEdgeForm_coeff f γ j₀ hj₀le, heq, add_sub_cancel_right, ← HahnSeries.leadingCoeff_eq]

-- pin: coeff_eval_single_order_zero (S_HahnSeries_isAlgClosed_rat.lean:297)
theorem coeff_eval_single_order_zero (f : (HahnSeries ℚ K)[X]) (γ : ℚ) (c : K) :
    (f.eval (HahnSeries.single γ c)).coeff (f.coeff 0).order =
      (evalEdgeForm f γ).eval c := by
  rw [coeff_eval_single, evalEdgeForm, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

-- pin: coeff_eval_single_of_lt_order_zero (S_HahnSeries_isAlgClosed_rat.lean:304)
theorem coeff_eval_single_of_lt_order_zero {f : (HahnSeries ℚ K)[X]} {γ : ℚ}
    (hslope : ∀ j, 1 ≤ j → j ≤ f.natDegree → f.coeff j ≠ 0 →
      (f.coeff 0).order ≤ (f.coeff j).order + j • γ)
    (c : K) {g : ℚ} (hg : g < (f.coeff 0).order) :
    (f.eval (HahnSeries.single γ c)).coeff g = 0 := by
  rw [coeff_eval_single]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hjle : j ≤ f.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rcases Nat.eq_zero_or_pos j with hzero | hpos
  ·
    subst hzero
    rw [zero_smul, sub_zero, HahnSeries.coeff_eq_zero_of_lt_order hg, zero_mul]
  ·
    rcases eq_or_ne (f.coeff j) 0 with hcoeff | hcoeff
    · simp [hcoeff]
    · have hbound : (f.coeff 0).order ≤ (f.coeff j).order + j • γ := hslope j hpos hjle hcoeff
      have hlt : g - j • γ < (f.coeff j).order := by linarith
      rw [HahnSeries.coeff_eq_zero_of_lt_order hlt, zero_mul]

-- pin: exists_addVal_eval_gt_of_eval_zero_ne_zero (S_HahnSeries_isAlgClosed_rat.lean:323)
theorem exists_addVal_eval_gt_of_eval_zero_ne_zero [IsAlgClosed K]
    {f : (HahnSeries ℚ K)[X]} (hf : f.Monic) (hdeg : 1 ≤ f.natDegree)
    (h0 : f.coeff 0 ≠ 0) :
    ∃ γ : ℚ, ∃ c : K, c ≠ 0 ∧
      HahnSeries.addVal ℚ K (f.eval 0) <
        HahnSeries.addVal ℚ K (f.eval (HahnSeries.single γ c)) := by
  obtain ⟨γ, hslope, j₀, hj₀1, hj₀le, hj₀ne, hj₀eq⟩ := exists_evalNewtonSlope hf hdeg

  have hconst : (evalEdgeForm f γ).coeff 0 ≠ 0 := by
    rw [evalEdgeForm_coeff_zero]; exact HahnSeries.leadingCoeff_ne_zero.mpr h0
  have hj₀coeff : (evalEdgeForm f γ).coeff j₀ ≠ 0 := by
    rw [evalEdgeForm_coeff_of_eq hj₀le hj₀eq]
    exact HahnSeries.leadingCoeff_ne_zero.mpr hj₀ne

  have hdegφ : 1 ≤ (evalEdgeForm f γ).natDegree :=
    le_trans hj₀1 (Polynomial.le_natDegree_of_ne_zero hj₀coeff)
  have hdegφ' : (evalEdgeForm f γ).degree ≠ 0 :=
    (Polynomial.natDegree_pos_iff_degree_pos.mp hdegφ).ne'
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_root (evalEdgeForm f γ) hdegφ'
  have hcne : c ≠ 0 := fun hc0 => by
    rw [Polynomial.IsRoot, hc0, ← Polynomial.coeff_zero_eq_eval_zero] at hc
    exact hconst hc
  refine ⟨γ, c, hcne, ?_⟩

  have hvanish : ∀ g ≤ (f.coeff 0).order,
      (f.eval (HahnSeries.single γ c)).coeff g = 0 := by
    intro g hg
    rcases lt_or_eq_of_le hg with hlt | heq
    · exact coeff_eval_single_of_lt_order_zero hslope c hlt
    · subst heq
      rw [coeff_eval_single_order_zero]; exact hc

  have heval0 : f.eval 0 = f.coeff 0 := (Polynomial.coeff_zero_eq_eval_zero f).symm
  rw [heval0, HahnSeries.addVal_apply_of_ne h0, HahnSeries.addVal_apply]
  rcases eq_or_ne (f.eval (HahnSeries.single γ c)) 0 with heq | hne
  · rw [heq, HahnSeries.orderTop_zero]; exact WithTop.coe_lt_top _
  · rw [← HahnSeries.order_eq_orderTop_of_ne_zero hne, WithTop.coe_lt_coe]
    by_contra hle
    push Not at hle

    have horder : (f.eval (HahnSeries.single γ c)).coeff
        (f.eval (HahnSeries.single γ c)).order ≠ 0 := by
      rw [← HahnSeries.leadingCoeff_eq]
      exact HahnSeries.leadingCoeff_ne_zero.mpr hne
    exact horder (hvanish _ hle)

variable {Γ : Type*} [LinearOrder Γ]

-- pin: IsBallChain (S_HahnSeries_isAlgClosed_rat.lean:371)
structure IsBallChain {ι : Type*} [LinearOrder ι]
    (r : ι → HahnSeries Γ K) (δ : ι → WithTop Γ) : Prop where

  δ_mono : Monotone δ

  mem_ball : ∀ ⦃i j : ι⦄, i ≤ j → δ i ≤ (r j - r i).orderTop

-- pin: pseudoLimitCoeff (S_HahnSeries_isAlgClosed_rat.lean:378)
def pseudoLimitCoeff {ι : Type*} [LinearOrder ι]
    (r : ι → HahnSeries Γ K) (δ : ι → WithTop Γ) (g : Γ) : K :=
  if h : ∃ i, (g : WithTop Γ) < δ i then (r h.choose).coeff g else 0

-- pin: IsBallChain.coeff_eq_of_lt (S_HahnSeries_isAlgClosed_rat.lean:382)
theorem IsBallChain.coeff_eq_of_lt {ι : Type*} [LinearOrder ι]
    {r : ι → HahnSeries Γ K} {δ : ι → WithTop Γ} (h : IsBallChain r δ)
    {i j : ι} {g : Γ} (hgi : (g : WithTop Γ) < δ i) (hgj : (g : WithTop Γ) < δ j) :
    (r i).coeff g = (r j).coeff g := by
  wlog hij : i ≤ j generalizing i j
  · exact (this hgj hgi (le_of_not_ge hij)).symm

  have hdiff : (r j - r i).coeff g = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop (lt_of_lt_of_le hgi (h.mem_ball hij))
  rw [HahnSeries.coeff_sub, sub_eq_zero] at hdiff
  exact hdiff.symm

-- pin: IsBallChain.pseudoLimitCoeff_eq (S_HahnSeries_isAlgClosed_rat.lean:394)
theorem IsBallChain.pseudoLimitCoeff_eq {ι : Type*} [LinearOrder ι]
    {r : ι → HahnSeries Γ K} {δ : ι → WithTop Γ} (h : IsBallChain r δ)
    {g : Γ} {i : ι} (hgi : (g : WithTop Γ) < δ i) :
    pseudoLimitCoeff r δ g = (r i).coeff g := by
  unfold pseudoLimitCoeff
  rw [dite_eq_left ⟨i, hgi⟩]
  exact h.coeff_eq_of_lt (Exists.choose_spec (p := fun i => (g : WithTop Γ) < δ i) ⟨i, hgi⟩) hgi

-- pin: IsBallChain.isPWO_support_pseudoLimitCoeff (S_HahnSeries_isAlgClosed_rat.lean:402)
theorem IsBallChain.isPWO_support_pseudoLimitCoeff {ι : Type*} [LinearOrder ι]
    {r : ι → HahnSeries Γ K} {δ : ι → WithTop Γ} (h : IsBallChain r δ) :
    (Function.support (pseudoLimitCoeff r δ)).IsPWO := by

  refine Set.IsWF.isPWO ?_
  rw [Set.isWF_iff_no_descending_seq]
  intro f hanti hf

  have hf0 : pseudoLimitCoeff r δ (f 0) ≠ 0 := hf 0
  have hex : ∃ i, ((f 0 : Γ) : WithTop Γ) < δ i := by
    by_contra hnone
    rw [pseudoLimitCoeff, dite_eq_right hnone] at hf0; exact hf0 rfl
  obtain ⟨i₀, hi₀⟩ := hex

  have hfk : ∀ k, f k ∈ (r i₀).support := by
    intro k
    have hfk0 : f k ≤ f 0 := hanti.antitone (Nat.zero_le k)
    have hfklt : ((f k : Γ) : WithTop Γ) < δ i₀ :=
      lt_of_le_of_lt (WithTop.coe_le_coe.mpr hfk0) hi₀
    have heq := h.pseudoLimitCoeff_eq hfklt
    rw [HahnSeries.mem_support, ← heq]
    exact hf k

  have hWF := (r i₀).isWF_support
  rw [Set.isWF_iff_no_descending_seq] at hWF
  exact hWF f hanti hfk

-- pin: IsBallChain.pseudoLimit (S_HahnSeries_isAlgClosed_rat.lean:429)
def IsBallChain.pseudoLimit {ι : Type*} [LinearOrder ι]
    {r : ι → HahnSeries Γ K} {δ : ι → WithTop Γ} (h : IsBallChain r δ) :
    HahnSeries Γ K where
  coeff := pseudoLimitCoeff r δ
  isPWO_support' := h.isPWO_support_pseudoLimitCoeff

-- pin: IsBallChain.coeff_pseudoLimit (S_HahnSeries_isAlgClosed_rat.lean:435)
theorem IsBallChain.coeff_pseudoLimit {ι : Type*} [LinearOrder ι]
    {r : ι → HahnSeries Γ K} {δ : ι → WithTop Γ} (h : IsBallChain r δ)
    {g : Γ} {i : ι} (hgi : (g : WithTop Γ) < δ i) :
    h.pseudoLimit.coeff g = (r i).coeff g :=
  h.pseudoLimitCoeff_eq hgi

-- pin: IsBallChain.le_orderTop_sub_pseudoLimit (S_HahnSeries_isAlgClosed_rat.lean:441)
theorem IsBallChain.le_orderTop_sub_pseudoLimit {ι : Type*} [LinearOrder ι]
    {r : ι → HahnSeries Γ K} {δ : ι → WithTop Γ} (h : IsBallChain r δ) (i : ι) :
    δ i ≤ (h.pseudoLimit - r i).orderTop := by
  rw [HahnSeries.le_orderTop_iff_forall]
  intro g hg
  rw [HahnSeries.coeff_sub, h.coeff_pseudoLimit hg, sub_self]

-- pin: exists_pseudoLimit (S_HahnSeries_isAlgClosed_rat.lean:448)
theorem exists_pseudoLimit {ι : Type*} [LinearOrder ι]
    {r : ι → HahnSeries Γ K} {δ : ι → WithTop Γ} (h : IsBallChain r δ) :
    ∃ r' : HahnSeries Γ K, ∀ i, δ i ≤ (r' - r i).orderTop :=
  ⟨h.pseudoLimit, h.le_orderTop_sub_pseudoLimit⟩

-- pin: monic_taylor (S_HahnSeries_isAlgClosed_rat.lean:453)
theorem monic_taylor {f : (HahnSeries ℚ K)[X]} (hf : f.Monic) (r : HahnSeries ℚ K) :
    (Polynomial.taylor r f).Monic := by
  rw [Polynomial.taylor_apply]
  exact hf.comp (Polynomial.monic_X_add_C r)
    (by rw [Polynomial.natDegree_X_add_C]; exact one_ne_zero)

-- pin: exists_addVal_eval_gt (S_HahnSeries_isAlgClosed_rat.lean:459)
theorem exists_addVal_eval_gt [IsAlgClosed K] {f : (HahnSeries ℚ K)[X]} (hf : f.Monic)
    (hdeg : 1 ≤ f.natDegree) {r : HahnSeries ℚ K} (hr : f.eval r ≠ 0) :
    ∃ r' : HahnSeries ℚ K,
      HahnSeries.addVal ℚ K (f.eval r) < HahnSeries.addVal ℚ K (f.eval r') := by

  set g := Polynomial.taylor r f with hg
  have hgmonic : g.Monic := monic_taylor hf r
  have hgdeg : 1 ≤ g.natDegree := by rw [hg, Polynomial.natDegree_taylor]; exact hdeg
  have hg0 : g.coeff 0 ≠ 0 := by
    rw [hg, Polynomial.taylor_coeff_zero]; exact hr

  obtain ⟨γ, c, _, hlt⟩ :=
    exists_addVal_eval_gt_of_eval_zero_ne_zero hgmonic hgdeg hg0

  refine ⟨r + HahnSeries.single γ c, ?_⟩
  have heval0 : g.eval 0 = f.eval r := by
    rw [hg, Polynomial.taylor_apply, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C, zero_add]
  have hevals : g.eval (HahnSeries.single γ c) = f.eval (r + HahnSeries.single γ c) := by
    rw [hg, Polynomial.taylor_apply, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C, add_comm]
  rw [← heval0, ← hevals]
  exact hlt

-- pin: isRoot_or_not_isMax_addVal_eval (S_HahnSeries_isAlgClosed_rat.lean:483)
theorem isRoot_or_not_isMax_addVal_eval [IsAlgClosed K] {f : (HahnSeries ℚ K)[X]}
    (hf : f.Monic) (hdeg : 1 ≤ f.natDegree) (r : HahnSeries ℚ K) :
    f.IsRoot r ∨
      ∃ r', HahnSeries.addVal ℚ K (f.eval r) < HahnSeries.addVal ℚ K (f.eval r') := by
  rcases eq_or_ne (f.eval r) 0 with heq | hne
  · left; exact heq
  · right; exact exists_addVal_eval_gt hf hdeg hne

end DorgePuiseux

end

open Polynomial HahnSeries
open scoped Classical

noncomputable section

namespace DorgePuiseux

variable {K : Type*} [Field K]

private theorem nsmul_top_withTop {j : ℕ} (hj : 1 ≤ j) : j • (⊤ : WithTop ℚ) = ⊤ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [add_comm, succ_nsmul, add_top]

private theorem nsmul_coe_withTop (j : ℕ) (q : ℚ) :
    j • (q : WithTop ℚ) = ((j • q : ℚ) : WithTop ℚ) := by
  induction j with
  | zero => simp
  | succ k ih => rw [succ_nsmul, succ_nsmul, ih]; push_cast; ring_nf

private theorem nsmul_le_nsmul_iff_withTop {j : ℕ} (hj : 1 ≤ j) {a b : WithTop ℚ} :
    j • a ≤ j • b ↔ a ≤ b := by
  cases a with
  | top =>
    rw [nsmul_top_withTop hj]
    simp only [top_le_iff]
    cases b with
    | top => simp [nsmul_top_withTop hj]
    | coe q =>
      rw [nsmul_coe_withTop]
      exact ⟨fun h => absurd h WithTop.coe_ne_top, fun h => absurd h WithTop.coe_ne_top⟩
  | coe p =>
    cases b with
    | top => simp [nsmul_top_withTop hj, nsmul_coe_withTop]
    | coe q =>
      rw [nsmul_coe_withTop, nsmul_coe_withTop, WithTop.coe_le_coe, WithTop.coe_le_coe,
        nsmul_eq_mul, nsmul_eq_mul]
      exact mul_le_mul_iff_of_pos_left (by exact_mod_cast hj)

private theorem withTop_add_lt_add_left {a : WithTop ℚ} (ha : a ≠ ⊤) {b c : WithTop ℚ}
    (h : a + b < a + c) : b < c := by
  cases a with
  | top => exact absurd rfl ha
  | coe p =>
    cases b with
    | top => simp only [add_top, ← not_le, le_top, not_true] at h
    | coe q =>
      cases c with
      | top => exact WithTop.coe_lt_top _
      | coe s =>
        rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_lt_coe] at h
        exact WithTop.coe_lt_coe.mpr (lt_of_add_lt_add_left h)

-- pin: eval_sub_eval_eq_sum_taylor (S_HahnSeries_isAlgClosed_rat.lean:547)
theorem eval_sub_eval_eq_sum_taylor (f : (HahnSeries ℚ K)[X]) (r h : HahnSeries ℚ K) :
    f.eval (r + h) - f.eval r =
      ∑ j ∈ Finset.range (f.natDegree + 1),
        (if j = 0 then 0 else (Polynomial.taylor r f).coeff j * h ^ j) := by
  have hnat : (Polynomial.taylor r f).natDegree = f.natDegree := Polynomial.natDegree_taylor f r
  rw [show r + h = h + r from add_comm r h, ← Polynomial.taylor_eval,
    Polynomial.eval_eq_sum_range, hnat]
  rw [show f.eval r = (Polynomial.taylor r f).coeff 0 from (Polynomial.taylor_coeff_zero ..).symm]
  have h0mem : 0 ∈ Finset.range (f.natDegree + 1) := Finset.mem_range.mpr (Nat.succ_pos _)
  rw [← Finset.add_sum_erase _ (fun j => (Polynomial.taylor r f).coeff j * h ^ j) h0mem,
    ← Finset.add_sum_erase _
      (fun j => if j = 0 then 0 else (Polynomial.taylor r f).coeff j * h ^ j) h0mem]
  rw [pow_zero, mul_one, add_sub_cancel_left, ite_eq_left rfl, zero_add]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [ite_eq_right (Finset.ne_of_mem_erase hj)]

-- pin: KaplanskySlope (S_HahnSeries_isAlgClosed_rat.lean:563)
def KaplanskySlope (f : (HahnSeries ℚ K)[X]) (r r' : HahnSeries ℚ K) : Prop :=
  ∀ j, 1 ≤ j → j ≤ f.natDegree →
    HahnSeries.addVal ℚ K (f.eval r) ≤
      HahnSeries.addVal ℚ K ((Polynomial.taylor r f).coeff j) +
        j • HahnSeries.addVal ℚ K (r' - r)

-- pin: KaplanskySlope.refl (S_HahnSeries_isAlgClosed_rat.lean:569)
theorem KaplanskySlope.refl (f : (HahnSeries ℚ K)[X]) (r : HahnSeries ℚ K) :
    KaplanskySlope f r r := by
  intro j hj _
  rw [sub_self, AddValuation.map_zero, nsmul_top_withTop hj, add_top]
  exact le_top

-- pin: KaplanskySlope.addVal_eval_le (S_HahnSeries_isAlgClosed_rat.lean:575)
theorem KaplanskySlope.addVal_eval_le {f : (HahnSeries ℚ K)[X]} {r r' : HahnSeries ℚ K}
    (h : KaplanskySlope f r r') :
    HahnSeries.addVal ℚ K (f.eval r) ≤ HahnSeries.addVal ℚ K (f.eval r') := by
  have hsum : HahnSeries.addVal ℚ K (f.eval r) ≤
      HahnSeries.addVal ℚ K (f.eval r' - f.eval r) := by
    rw [show f.eval r' - f.eval r = f.eval (r + (r' - r)) - f.eval r by ring_nf,
      eval_sub_eval_eq_sum_taylor]
    refine (HahnSeries.addVal ℚ K).map_le_sum fun j hj => ?_
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · simp
    · rw [ite_eq_right hpos.ne', (HahnSeries.addVal ℚ K).map_mul, (HahnSeries.addVal ℚ K).map_pow]
      exact h j hpos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  calc HahnSeries.addVal ℚ K (f.eval r)
      ≤ min (HahnSeries.addVal ℚ K (f.eval r)) (HahnSeries.addVal ℚ K (f.eval r' - f.eval r)) :=
        le_min le_rfl hsum
    _ ≤ HahnSeries.addVal ℚ K (f.eval r + (f.eval r' - f.eval r)) :=
        (HahnSeries.addVal ℚ K).map_add _ _
    _ = HahnSeries.addVal ℚ K (f.eval r') := by ring_nf

-- pin: KaplanskySlope.mono (S_HahnSeries_isAlgClosed_rat.lean:594)
theorem KaplanskySlope.mono {f : (HahnSeries ℚ K)[X]} {r r' r'' : HahnSeries ℚ K}
    (h : KaplanskySlope f r r')
    (hle : HahnSeries.addVal ℚ K (r' - r) ≤ HahnSeries.addVal ℚ K (r'' - r)) :
    KaplanskySlope f r r'' := by
  intro j hj hjle
  exact (h j hj hjle).trans
    (add_le_add le_rfl ((nsmul_le_nsmul_iff_withTop hj).mpr hle))

-- pin: exists_addVal_taylor_coeff_of_addVal_eval_lt (S_HahnSeries_isAlgClosed_rat.lean:602)
theorem exists_addVal_taylor_coeff_of_addVal_eval_lt {f : (HahnSeries ℚ K)[X]}
    {r r' : HahnSeries ℚ K}
    (hlt : HahnSeries.addVal ℚ K (f.eval r) < HahnSeries.addVal ℚ K (f.eval r')) :
    ∃ j, 1 ≤ j ∧ j ≤ f.natDegree ∧
      HahnSeries.addVal ℚ K ((Polynomial.taylor r' f).coeff j) +
        j • HahnSeries.addVal ℚ K (r' - r) ≤ HahnSeries.addVal ℚ K (f.eval r) := by

  by_contra habs
  push Not at habs

  have hsum : HahnSeries.addVal ℚ K (f.eval r) <
      HahnSeries.addVal ℚ K (f.eval (r' + (r - r'))) := by
    rw [show f.eval (r' + (r - r')) = f.eval r' + (f.eval (r' + (r - r')) - f.eval r') by ring,
      eval_sub_eval_eq_sum_taylor]
    refine (HahnSeries.addVal ℚ K).map_lt_add hlt ?_
    refine (HahnSeries.addVal ℚ K).map_lt_sum (ne_of_lt (lt_of_lt_of_le hlt le_top)) fun j hj => ?_
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · simpa using lt_of_lt_of_le hlt le_top
    · rw [ite_eq_right hpos.ne', (HahnSeries.addVal ℚ K).map_mul, (HahnSeries.addVal ℚ K).map_pow,
        show r - r' = -(r' - r) by ring, (HahnSeries.addVal ℚ K).map_neg]
      exact habs j hpos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  rw [show r' + (r - r') = r by ring] at hsum
  exact lt_irrefl _ hsum

-- pin: KaplanskyLE (S_HahnSeries_isAlgClosed_rat.lean:626)
def KaplanskyLE (f : (HahnSeries ℚ K)[X]) (r r' : HahnSeries ℚ K) : Prop :=
  r = r' ∨ (HahnSeries.addVal ℚ K (f.eval r) < HahnSeries.addVal ℚ K (f.eval r') ∧
    KaplanskySlope f r r')

-- pin: KaplanskyLE.refl (S_HahnSeries_isAlgClosed_rat.lean:630)
theorem KaplanskyLE.refl (f : (HahnSeries ℚ K)[X]) (r : HahnSeries ℚ K) :
    KaplanskyLE f r r := Or.inl rfl

instance (f : (HahnSeries ℚ K)[X]) : Std.Refl (KaplanskyLE f) := ⟨KaplanskyLE.refl f⟩

-- pin: KaplanskyLE.addVal_eval_le (S_HahnSeries_isAlgClosed_rat.lean:635)
theorem KaplanskyLE.addVal_eval_le {f : (HahnSeries ℚ K)[X]} {r r' : HahnSeries ℚ K}
    (h : KaplanskyLE f r r') :
    HahnSeries.addVal ℚ K (f.eval r) ≤ HahnSeries.addVal ℚ K (f.eval r') := by
  rcases h with rfl | ⟨hlt, _⟩
  · exact le_rfl
  · exact hlt.le

-- pin: KaplanskySlope.of_kaplanskyLE_of_lt (S_HahnSeries_isAlgClosed_rat.lean:642)
theorem KaplanskySlope.of_kaplanskyLE_of_lt {f : (HahnSeries ℚ K)[X]}
    {r r' r'' : HahnSeries ℚ K}
    (hlt : HahnSeries.addVal ℚ K (f.eval r) < HahnSeries.addVal ℚ K (f.eval r'))
    (hslope : KaplanskySlope f r r') (h' : KaplanskyLE f r' r'') :
    KaplanskySlope f r r'' := by
  rcases h' with rfl | ⟨_, hslope'⟩
  · exact hslope
  obtain ⟨j₀, hj₀1, hj₀le, hj₀⟩ := exists_addVal_taylor_coeff_of_addVal_eval_lt hlt
  have hj₀' := hslope' j₀ hj₀1 hj₀le
  have hlt'' : HahnSeries.addVal ℚ K ((Polynomial.taylor r' f).coeff j₀) +
        j₀ • HahnSeries.addVal ℚ K (r' - r) <
      HahnSeries.addVal ℚ K ((Polynomial.taylor r' f).coeff j₀) +
        j₀ • HahnSeries.addVal ℚ K (r'' - r') :=
    lt_of_le_of_lt hj₀ (lt_of_lt_of_le hlt hj₀')
  have hbne : HahnSeries.addVal ℚ K ((Polynomial.taylor r' f).coeff j₀) ≠ ⊤ := by
    intro htop; rw [htop, top_add, top_add] at hlt''; exact lt_irrefl _ hlt''
  have hηle : HahnSeries.addVal ℚ K (r' - r) ≤ HahnSeries.addVal ℚ K (r'' - r') :=
    (nsmul_le_nsmul_iff_withTop hj₀1).mp (withTop_add_lt_add_left hbne hlt'').le
  refine hslope.mono ?_
  calc HahnSeries.addVal ℚ K (r' - r)
      = min (HahnSeries.addVal ℚ K (r' - r)) (HahnSeries.addVal ℚ K (r'' - r')) :=
        (min_eq_left hηle).symm
    _ ≤ HahnSeries.addVal ℚ K ((r' - r) + (r'' - r')) := (HahnSeries.addVal ℚ K).map_add _ _
    _ = HahnSeries.addVal ℚ K (r'' - r) := by ring_nf

-- pin: KaplanskyLE.trans (S_HahnSeries_isAlgClosed_rat.lean:667)
theorem KaplanskyLE.trans {f : (HahnSeries ℚ K)[X]} {r r' r'' : HahnSeries ℚ K}
    (h : KaplanskyLE f r r') (h' : KaplanskyLE f r' r'') : KaplanskyLE f r r'' := by
  rcases h with rfl | ⟨hlt, hslope⟩
  · exact h'
  exact Or.inr ⟨lt_of_lt_of_le hlt h'.addVal_eval_le, hslope.of_kaplanskyLE_of_lt hlt h'⟩

-- pin: KaplanskyLE.antisymm (S_HahnSeries_isAlgClosed_rat.lean:673)
theorem KaplanskyLE.antisymm {f : (HahnSeries ℚ K)[X]} {r r' : HahnSeries ℚ K}
    (h : KaplanskyLE f r r') (h' : KaplanskyLE f r' r) : r = r' := by
  rcases h with rfl | ⟨hlt, _⟩
  · rfl
  rcases h' with rfl | ⟨hlt', _⟩
  · rfl
  exact absurd hlt (not_lt.mpr hlt'.le)

-- pin: KaplanskyLE.addVal_sub_le_addVal_sub (S_HahnSeries_isAlgClosed_rat.lean:681)
theorem KaplanskyLE.addVal_sub_le_addVal_sub {f : (HahnSeries ℚ K)[X]}
    {r r' r'' : HahnSeries ℚ K}
    (hlt : HahnSeries.addVal ℚ K (f.eval r) < HahnSeries.addVal ℚ K (f.eval r'))
    (h' : KaplanskyLE f r' r'')
    (hlt' : HahnSeries.addVal ℚ K (f.eval r') < HahnSeries.addVal ℚ K (f.eval r'')) :
    HahnSeries.addVal ℚ K (r' - r) ≤ HahnSeries.addVal ℚ K (r'' - r') := by
  rcases h' with rfl | ⟨_, hslope'⟩
  · exact absurd hlt' (lt_irrefl _)
  obtain ⟨j₀, hj₀1, hj₀le, hj₀⟩ := exists_addVal_taylor_coeff_of_addVal_eval_lt hlt
  have hj₀' := hslope' j₀ hj₀1 hj₀le
  have hlt'' := lt_of_le_of_lt hj₀ (lt_of_lt_of_le hlt hj₀')
  have hbne : HahnSeries.addVal ℚ K ((Polynomial.taylor r' f).coeff j₀) ≠ ⊤ := by
    intro htop; rw [htop, top_add, top_add] at hlt''; exact lt_irrefl _ hlt''
  exact (nsmul_le_nsmul_iff_withTop hj₀1).mp (withTop_add_lt_add_left hbne hlt'').le

-- pin: exists_kaplanskyLE_of_eval_ne_zero (S_HahnSeries_isAlgClosed_rat.lean:696)
theorem exists_kaplanskyLE_of_eval_ne_zero [IsAlgClosed K] {f : (HahnSeries ℚ K)[X]}
    (hf : f.Monic) (hdeg : 1 ≤ f.natDegree)
    {r : HahnSeries ℚ K} (hr : f.eval r ≠ 0) :
    ∃ r', r ≠ r' ∧ KaplanskyLE f r r' := by
  set g := Polynomial.taylor r f with hg
  have hgmonic : g.Monic := monic_taylor hf r
  have hgdeg : 1 ≤ g.natDegree := by rw [hg, Polynomial.natDegree_taylor]; exact hdeg
  have hg0 : g.coeff 0 ≠ 0 := by rw [hg, Polynomial.taylor_coeff_zero]; exact hr
  obtain ⟨γ, hslope, j₀, hj₀1, hj₀le, hj₀ne, hj₀eq⟩ := exists_evalNewtonSlope hgmonic hgdeg

  have hconst : (evalEdgeForm g γ).coeff 0 ≠ 0 := by
    rw [evalEdgeForm_coeff_zero]; exact HahnSeries.leadingCoeff_ne_zero.mpr hg0
  have hj₀coeff : (evalEdgeForm g γ).coeff j₀ ≠ 0 := by
    rw [evalEdgeForm_coeff_of_eq hj₀le hj₀eq]
    exact HahnSeries.leadingCoeff_ne_zero.mpr hj₀ne
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_root (evalEdgeForm g γ)
    ((Polynomial.natDegree_pos_iff_degree_pos.mp
      (le_trans hj₀1 (Polynomial.le_natDegree_of_ne_zero hj₀coeff))).ne')
  have hcne : c ≠ 0 := fun hc0 => by
    rw [Polynomial.IsRoot, hc0, ← Polynomial.coeff_zero_eq_eval_zero] at hc; exact hconst hc

  have hvanish : ∀ q ≤ (g.coeff 0).order, (g.eval (HahnSeries.single γ c)).coeff q = 0 := by
    intro q hq
    rcases lt_or_eq_of_le hq with hlt' | heq
    · exact coeff_eval_single_of_lt_order_zero hslope c hlt'
    · subst heq; rw [coeff_eval_single_order_zero]; exact hc
  have heval0 : f.eval r = g.coeff 0 := by
    rw [hg, Polynomial.taylor_coeff_zero]
  have hltγ : HahnSeries.addVal ℚ K (f.eval r) <
      HahnSeries.addVal ℚ K (g.eval (HahnSeries.single γ c)) := by
    rw [heval0, HahnSeries.addVal_apply_of_ne hg0, HahnSeries.addVal_apply]
    rcases eq_or_ne (g.eval (HahnSeries.single γ c)) 0 with heq | hne
    · rw [heq, HahnSeries.orderTop_zero]; exact WithTop.coe_lt_top _
    · rw [← HahnSeries.order_eq_orderTop_of_ne_zero hne, WithTop.coe_lt_coe]
      by_contra hle
      have hkey := hvanish (g.eval (HahnSeries.single γ c)).order (not_lt.mp hle)
      rw [← HahnSeries.leadingCoeff_eq] at hkey
      exact (HahnSeries.leadingCoeff_ne_zero.mpr hne) hkey
  have hevals : g.eval (HahnSeries.single γ c) = f.eval (r + HahnSeries.single γ c) := by
    rw [hg, Polynomial.taylor_eval, add_comm]
  refine ⟨r + HahnSeries.single γ c, fun heq => hcne ?_, Or.inr ⟨hevals ▸ hltγ, ?_⟩⟩
  · have h0 : (HahnSeries.single γ c : HahnSeries ℚ K) = 0 := by
      have heq' : r + HahnSeries.single γ c = r + (0 : HahnSeries ℚ K) := by
        rw [add_zero]; exact heq.symm
      exact add_left_cancel heq'
    exact HahnSeries.single_eq_zero_iff.mp h0
  ·
    intro j hj hjle
    rw [add_sub_cancel_left, heval0, HahnSeries.addVal_apply_of_ne hg0]
    rcases eq_or_ne ((Polynomial.taylor r f).coeff j) 0 with hzero | hne
    · rw [hzero, AddValuation.map_zero, top_add]; exact le_top
    · have hjle' : j ≤ g.natDegree := by rw [hg, Polynomial.natDegree_taylor]; exact hjle
      rw [HahnSeries.addVal_apply_of_ne hne, HahnSeries.addVal_apply,
        HahnSeries.orderTop_single hcne, ← hg, nsmul_coe_withTop]
      exact_mod_cast hslope j hj hjle' hne

-- pin: eval_eq_zero_of_kaplanskyLE_max (S_HahnSeries_isAlgClosed_rat.lean:752)
theorem eval_eq_zero_of_kaplanskyLE_max [IsAlgClosed K] {f : (HahnSeries ℚ K)[X]}
    (hf : f.Monic) (hdeg : 1 ≤ f.natDegree)
    {m : HahnSeries ℚ K} (hmax : ∀ r, KaplanskyLE f m r → KaplanskyLE f r m) :
    f.eval m = 0 := by
  by_contra hm
  obtain ⟨r', hne, hle⟩ := exists_kaplanskyLE_of_eval_ne_zero hf hdeg hm
  exact hne (KaplanskyLE.antisymm hle (hmax r' hle))

section ChainUpperBound

variable {f : (HahnSeries ℚ K)[X]}

-- pin: kaplanskyChain_addVal_injOn (S_HahnSeries_isAlgClosed_rat.lean:764)
theorem kaplanskyChain_addVal_injOn {C : Set (HahnSeries ℚ K)}
    (hC : IsChain (KaplanskyLE f) C) :
    Set.InjOn (fun a => HahnSeries.addVal ℚ K (f.eval a)) C := by
  intro a ha b hb hab
  rcases hC.total ha hb with h | h
  · rcases h with rfl | ⟨hlt, _⟩
    exacts [rfl, absurd hab hlt.ne]
  · rcases h with rfl | ⟨hlt, _⟩
    exacts [rfl, absurd hab.symm hlt.ne]

-- pin: kaplanskyChainOrder (S_HahnSeries_isAlgClosed_rat.lean:774)
@[reducible] def kaplanskyChainOrder {C : Set (HahnSeries ℚ K)}
    (hC : IsChain (KaplanskyLE f) C) :
    LinearOrder ↥C :=
  LinearOrder.lift' (fun a => HahnSeries.addVal ℚ K (f.eval (a : HahnSeries ℚ K)))
    (fun a b hab => Subtype.ext (kaplanskyChain_addVal_injOn hC a.2 b.2 hab))

-- pin: kaplanskyChainOrder_le_iff (S_HahnSeries_isAlgClosed_rat.lean:780)
theorem kaplanskyChainOrder_le_iff {C : Set (HahnSeries ℚ K)}
    (hC : IsChain (KaplanskyLE f) C) {a b : ↥C} :
    (kaplanskyChainOrder hC).le a b ↔ KaplanskyLE f (a : HahnSeries ℚ K) b := by
  constructor
  · intro hle
    rcases hC.total a.2 b.2 with h | h
    · exact h
    · have heq : (a : HahnSeries ℚ K) = b :=
        kaplanskyChain_addVal_injOn hC a.2 b.2 (le_antisymm hle h.addVal_eval_le)
      exact heq ▸ KaplanskyLE.refl f a
  · intro h; exact h.addVal_eval_le

-- pin: KaplanskyBelowSlope (S_HahnSeries_isAlgClosed_rat.lean:792)
def KaplanskyBelowSlope (f : (HahnSeries ℚ K)[X]) (a : HahnSeries ℚ K) (g : ℚ) : Prop :=
  ∃ j, 1 ≤ j ∧ j ≤ f.natDegree ∧
    HahnSeries.addVal ℚ K ((Polynomial.taylor a f).coeff j) + ((j • g : ℚ) : WithTop ℚ) <
      HahnSeries.addVal ℚ K (f.eval a)

private theorem nsmul_lt_nsmul_iff_withTop {j : ℕ} (hj : 1 ≤ j) {a b : WithTop ℚ} :
    j • a < j • b ↔ a < b := by
  rw [lt_iff_le_not_ge, lt_iff_le_not_ge, nsmul_le_nsmul_iff_withTop hj,
    nsmul_le_nsmul_iff_withTop hj]

-- pin: KaplanskyBelowSlope.lt_addVal_sub (S_HahnSeries_isAlgClosed_rat.lean:802)
theorem KaplanskyBelowSlope.lt_addVal_sub {a b : HahnSeries ℚ K} {g : ℚ}
    (hbelow : KaplanskyBelowSlope f a g) (hslope : KaplanskySlope f a b) :
    (g : WithTop ℚ) < HahnSeries.addVal ℚ K (b - a) := by
  obtain ⟨j, hj1, hjle, hjlt⟩ := hbelow
  have hj := hslope j hj1 hjle

  have hbne : HahnSeries.addVal ℚ K ((Polynomial.taylor a f).coeff j) ≠ ⊤ := by
    intro htop; rw [htop, top_add] at hjlt; exact not_top_lt hjlt
  have hlt : ((j • g : ℚ) : WithTop ℚ) < j • HahnSeries.addVal ℚ K (b - a) :=
    withTop_add_lt_add_left hbne (lt_of_lt_of_le hjlt hj)
  rw [← nsmul_coe_withTop] at hlt
  exact (nsmul_lt_nsmul_iff_withTop hj1).mp hlt

-- pin: KaplanskyBelowSlope.of_kaplanskyLE (S_HahnSeries_isAlgClosed_rat.lean:815)
theorem KaplanskyBelowSlope.of_kaplanskyLE {a b : HahnSeries ℚ K} {g : ℚ}
    (hbelow : KaplanskyBelowSlope f a g)
    (hlt : HahnSeries.addVal ℚ K (f.eval a) < HahnSeries.addVal ℚ K (f.eval b))
    (hslope : KaplanskySlope f a b) :
    KaplanskyBelowSlope f b g := by
  obtain ⟨j₀, hj₀1, hj₀le, hj₀⟩ := exists_addVal_taylor_coeff_of_addVal_eval_lt hlt
  refine ⟨j₀, hj₀1, hj₀le, ?_⟩
  have hglt : (g : WithTop ℚ) < HahnSeries.addVal ℚ K (b - a) := hbelow.lt_addVal_sub hslope

  have hbne : HahnSeries.addVal ℚ K ((Polynomial.taylor b f).coeff j₀) ≠ ⊤ := by
    intro htop; rw [htop, top_add] at hj₀; exact not_top_lt (lt_of_le_of_lt hj₀ hlt)
  calc HahnSeries.addVal ℚ K ((Polynomial.taylor b f).coeff j₀) + ((j₀ • g : ℚ) : WithTop ℚ)
      < HahnSeries.addVal ℚ K ((Polynomial.taylor b f).coeff j₀) +
          j₀ • HahnSeries.addVal ℚ K (b - a) := by
        rw [← nsmul_coe_withTop]
        refine WithTop.add_lt_add_left hbne ?_
        exact (nsmul_lt_nsmul_iff_withTop hj₀1).mpr hglt
    _ ≤ HahnSeries.addVal ℚ K (f.eval a) := hj₀
    _ < HahnSeries.addVal ℚ K (f.eval b) := hlt

-- pin: kaplanskyChain_coeff_eq (S_HahnSeries_isAlgClosed_rat.lean:835)
theorem kaplanskyChain_coeff_eq {C : Set (HahnSeries ℚ K)}
    (hC : IsChain (KaplanskyLE f) C) {a b : HahnSeries ℚ K} (ha : a ∈ C) (hb : b ∈ C)
    {g : ℚ} (hga : KaplanskyBelowSlope f a g) (hgb : KaplanskyBelowSlope f b g) :
    a.coeff g = b.coeff g := by
  rcases hC.total ha hb with hab | hab
  · rcases hab with rfl | ⟨_, hslope⟩
    · rfl
    have hlt := hga.lt_addVal_sub hslope
    rw [HahnSeries.addVal_apply] at hlt
    have hdiff := HahnSeries.coeff_eq_zero_of_lt_orderTop hlt
    rw [HahnSeries.coeff_sub, sub_eq_zero] at hdiff
    exact hdiff.symm
  · rcases hab with rfl | ⟨_, hslope⟩
    · rfl
    have hlt := hgb.lt_addVal_sub hslope
    rw [HahnSeries.addVal_apply] at hlt
    have hdiff := HahnSeries.coeff_eq_zero_of_lt_orderTop hlt
    rw [HahnSeries.coeff_sub, sub_eq_zero] at hdiff
    exact hdiff

-- pin: kaplanskyLimitCoeff (S_HahnSeries_isAlgClosed_rat.lean:855)
def kaplanskyLimitCoeff (C : Set (HahnSeries ℚ K)) (g : ℚ) : K :=
  if h : ∃ a ∈ C, KaplanskyBelowSlope f a g then h.choose.coeff g else 0

-- pin: kaplanskyLimitCoeff_eq (S_HahnSeries_isAlgClosed_rat.lean:858)
theorem kaplanskyLimitCoeff_eq {C : Set (HahnSeries ℚ K)} (hC : IsChain (KaplanskyLE f) C)
    {a : HahnSeries ℚ K} (ha : a ∈ C) {g : ℚ} (hga : KaplanskyBelowSlope f a g) :
    kaplanskyLimitCoeff (f := f) C g = a.coeff g := by
  unfold kaplanskyLimitCoeff
  rw [dite_eq_left ⟨a, ha, hga⟩]
  obtain ⟨hb, hgb⟩ := (⟨a, ha, hga⟩ : ∃ a ∈ C, KaplanskyBelowSlope f a g).choose_spec
  exact kaplanskyChain_coeff_eq hC hb ha hgb hga

-- pin: kaplanskyLimitCoeff_isPWO_support (S_HahnSeries_isAlgClosed_rat.lean:866)
theorem kaplanskyLimitCoeff_isPWO_support {C : Set (HahnSeries ℚ K)}
    (hC : IsChain (KaplanskyLE f) C) :
    (Function.support (kaplanskyLimitCoeff (f := f) C)).IsPWO := by
  refine Set.IsWF.isPWO ?_
  rw [Set.isWF_iff_no_descending_seq]
  intro s hanti hs
  have hf0 : kaplanskyLimitCoeff (f := f) C (s 0) ≠ 0 := hs 0
  have hex : ∃ a ∈ C, KaplanskyBelowSlope f a (s 0) := by
    by_contra hnone; rw [kaplanskyLimitCoeff, dite_eq_right hnone] at hf0; exact hf0 rfl
  obtain ⟨a₀, ha₀, hga₀⟩ := hex

  have hsk : ∀ k, s k ∈ a₀.support := by
    intro k
    have hsk0 : s k ≤ s 0 := hanti.antitone (Nat.zero_le k)

    obtain ⟨j, hj1, hjle, hjlt⟩ := hga₀
    have hgak : KaplanskyBelowSlope f a₀ (s k) := ⟨j, hj1, hjle, by
      refine lt_of_le_of_lt ?_ hjlt
      gcongr
      exact_mod_cast nsmul_le_nsmul_right hsk0 j⟩
    have heq := kaplanskyLimitCoeff_eq hC ha₀ hgak
    rw [HahnSeries.mem_support, ← heq]
    exact hs k
  have hWF := a₀.isWF_support
  rw [Set.isWF_iff_no_descending_seq] at hWF
  exact hWF s hanti hsk

-- pin: kaplanskyLimit (S_HahnSeries_isAlgClosed_rat.lean:893)
def kaplanskyLimit {C : Set (HahnSeries ℚ K)} (hC : IsChain (KaplanskyLE f) C) :
    HahnSeries ℚ K where
  coeff := kaplanskyLimitCoeff (f := f) C
  isPWO_support' := kaplanskyLimitCoeff_isPWO_support hC

-- pin: kaplanskySlope_kaplanskyLimit (S_HahnSeries_isAlgClosed_rat.lean:898)
theorem kaplanskySlope_kaplanskyLimit {C : Set (HahnSeries ℚ K)}
    (hC : IsChain (KaplanskyLE f) C) {a : HahnSeries ℚ K} (ha : a ∈ C) :
    KaplanskySlope f a (kaplanskyLimit hC) := by
  intro j hj hjle

  by_contra hlt
  push Not at hlt

  have hne : kaplanskyLimit hC - a ≠ 0 := by
    intro heq
    rw [heq, AddValuation.map_zero, nsmul_top_withTop hj, add_top] at hlt
    exact not_top_lt hlt
  set q : ℚ := (kaplanskyLimit hC - a).order with hq
  have hqval : HahnSeries.addVal ℚ K (kaplanskyLimit hC - a) = (q : WithTop ℚ) := by
    rw [HahnSeries.addVal_apply_of_ne hne, hq]
  rw [hqval, nsmul_coe_withTop] at hlt

  have hbelow : KaplanskyBelowSlope f a q := ⟨j, hj, hjle, hlt⟩

  have hcoeff : (kaplanskyLimit hC - a).coeff q = 0 := by
    rw [HahnSeries.coeff_sub]
    show kaplanskyLimitCoeff (f := f) C q - a.coeff q = 0
    rw [kaplanskyLimitCoeff_eq hC ha hbelow, sub_self]

  rw [hq, ← HahnSeries.leadingCoeff_eq] at hcoeff
  exact (HahnSeries.leadingCoeff_ne_zero.mpr hne) hcoeff

-- pin: exists_kaplanskyLE_upperBound (S_HahnSeries_isAlgClosed_rat.lean:925)
theorem exists_kaplanskyLE_upperBound {C : Set (HahnSeries ℚ K)}
    (hC : IsChain (KaplanskyLE f) C) :
    ∃ ub, ∀ a ∈ C, KaplanskyLE f a ub := by

  by_cases hmax : ∃ m ∈ C, ∀ a ∈ C, KaplanskyLE f a m
  · obtain ⟨m, _, hm⟩ := hmax; exact ⟨m, hm⟩
  push Not at hmax

  have hnomax : ∀ a ∈ C, ∃ b ∈ C, KaplanskyLE f a b ∧ a ≠ b := by
    intro a ha
    obtain ⟨b, hb, hnle⟩ := hmax a ha
    rcases hC.total ha hb with hab | hab
    · exact ⟨b, hb, hab, fun heq => hnle (heq ▸ KaplanskyLE.refl f a)⟩
    · exact absurd hab hnle

  refine ⟨kaplanskyLimit hC, fun a ha => ?_⟩
  obtain ⟨b, hb, hab, hne⟩ := hnomax a ha
  have hltab : HahnSeries.addVal ℚ K (f.eval a) < HahnSeries.addVal ℚ K (f.eval b) := by
    rcases hab with rfl | ⟨hlt, _⟩
    · exact absurd rfl hne
    · exact hlt
  refine Or.inr ⟨?_, kaplanskySlope_kaplanskyLimit hC ha⟩
  exact lt_of_lt_of_le hltab (kaplanskySlope_kaplanskyLimit hC hb).addVal_eval_le

end ChainUpperBound

-- pin: exists_isRoot_hahnSeries (S_HahnSeries_isAlgClosed_rat.lean:951)
theorem exists_isRoot_hahnSeries [IsAlgClosed K] {f : (HahnSeries ℚ K)[X]}
    (hf : f.Monic) (hdeg : 1 ≤ f.natDegree) :
    ∃ r : HahnSeries ℚ K, f.IsRoot r := by
  obtain ⟨m, hmax⟩ := exists_maximal_of_chains_bounded
    (r := KaplanskyLE f) (fun C hC => exists_kaplanskyLE_upperBound hC)
    (fun {a b c} => KaplanskyLE.trans)
  exact ⟨m, eval_eq_zero_of_kaplanskyLE_max hf hdeg hmax⟩

-- pin: isAlgClosed_hahnSeries_rat (S_HahnSeries_isAlgClosed_rat.lean:959)
theorem isAlgClosed_hahnSeries_rat [IsAlgClosed K] : IsAlgClosed (HahnSeries ℚ K) := by
  refine IsAlgClosed.of_exists_root _ fun f hf hirr => ?_
  have hdeg : 1 ≤ f.natDegree := by
    by_contra hlt
    have h1 : f = 1 := hf.natDegree_eq_zero.mp (Nat.lt_one_iff.mp (not_le.mp hlt))
    exact hirr.not_isUnit (h1 ▸ isUnit_one)
  exact exists_isRoot_hahnSeries hf hdeg

end DorgePuiseux
end


-- pin: isAlgClosed_rat (Thm_HahnSeries_isAlgClosed_rat.lean:9)
theorem HahnSeries.isAlgClosed_rat {K : Type*} [Field K] [IsAlgClosed K] :
    IsAlgClosed (HahnSeries ℚ K) :=
  DorgePuiseux.isAlgClosed_hahnSeries_rat
