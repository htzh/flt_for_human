/-
  Joint eigenspaces of a commutative algebra of endomorphisms, and multiplicity one.

  Three statements, one per pin file, all about a commutative `K`-subalgebra `A` of
  `Module.End K W` acting on a finite-dimensional `W`:

  * `Module.End.nonempty_basis_fin_one_and_finrank_iInf_eigenspace_eq_one_of_iSupIndep_of_cyclic`:
    if `W` is the internal direct sum of cyclic `A`-summands — idempotents `e i` projecting
    onto the summands `V i`, cyclic generators `w i`, and every joint eigenspace cut out of a
    single summand by a character `χ : ↥A ->ₐ[K] K` at most one-dimensional — then `W` is free
    of rank one over `A` and every joint eigenspace of the full action has dimension exactly
    `1`;
  * `Module.End.mem_span_prod_apply_and_finrank_iInf_eigenspace_le_one_of_divisorString`: from a
    `D`-divisor-indexed basis `e` on which the prime-indexed operators `U q` satisfy the
    `U_q`-down and `U_q`-base relations, `e D` is a cyclic generator over `Algebra.adjoin ℂ {U_q}`
    and every joint eigenspace `⨅ q ∈ D.primeFactors, eigenspace (U q) (lam q)` is at most
    one-dimensional;
  * `Module.End.exists_mem_adjoin_apply_eq_self_and_apply_eq_zero_of_forall_ne_exists_ne`:
    separating scalar actions on a finite family of subspaces produce, inside
    `Algebra.adjoin K 𝒯`, a Lagrange-interpolation projector that is the identity on `W i` and
    zero on every other `W j` (no independence or finiteness assumed).

  Transcribed verbatim from the pin — three `Theorems/` wrappers and the three `S_` files
  (305 + 181 + 76 = 562 pin lines), pinned `aa2d8b3`. The pin's inner labels `ALG`,
  `DivisorStringWs41` and `M7` fold into `Module.End.MultiplicityOne`,
  `Module.End.DivisorString` and `Module.End.SeparatingProjector`; every last name is kept, and
  the three headlines keep the pin's full names at mathlib's object namespace `Module.End`.
  As in the pin, row 3's three helpers (`mul_dvd_of_prime_of_not_dvd`, `cyclic_part`,
  `eigen_part`) stay `private`; row 2's `e_w0` stays public. The statement-only `solution`
  wrapper of each `S_` file is not ported: each headline is stated once, at the wrapper's name,
  with the `solution` body.

  Drift against `v4.34.0` — statements untouched, all in proofs/bodies:

  * the pin's row-2 file-wide 6,400,000-heartbeat override is dropped; the whole module
    elaborates under the port's 200,000-heartbeat edit-loop setting;
  * row 2, `ψ_surjective`: `AddSubmonoidClass.coe_finset_sum` -> `coe_finsetSum` (deprecated);
  * row 2, `exists_socle`: the four `letI` / `haveI` become `let` / `have` (the
    `linter.style.haveILetI` suggestion; in Lean 4 `have` and `let` register local instances
    themselves, so nothing changes for instance search);
  * row 2, `mem_Eig`: the unused simp argument `Module.End.mem_eigenspace_iff` is dropped;
  * sixteen `omit` lines — `[FiniteDimensional K W]` before thirteen of the `ALG` theorems
    (`decomp`, `e_apply_mem`, `sum_e_apply`, `e_w0`, `ψ_apply`, `ψ_surjective`, `ψ_injective`,
    `nonempty_basis`, `sum_e_eq_one`, `e_mul_e_self`, `exists_chi_e_eq_one`, `mem_Eig`,
    `Eig_le`), and `[Fintype ι] [DecidableEq ι]` / `[Fintype ι]` before `factor_apply_of_mem`,
    `factor_mem` / `main_aux` — the `linter.unusedSectionVars` suggestions, narrowed here where
    the pin silenced the linter file-wide (the omitted binders are unused section variables, not
    part of any statement; omitting on `decomp` frees the nine downstream theorems that used it
    only in passing, which is why this is thirteen and not the pin's four);
  * the three headlines keep their binders verbatim, including the unused `hVind`, `hstab`
    and `hcomm`; the proofs reference those binders so that no `unusedVariables` warning is
    raised.

  spec-pin: Theorems/Thm_Module_End_nonempty_basis_fin_one_and_finrank_iInf_eigenspace_eq_one_of_iSupIndep_of_cyclic.lean
  spec-pin: Theorems/Thm_Module_End_mem_span_prod_apply_and_finrank_iInf_eigenspace_le_one_of_divisorString.lean
  spec-pin: Theorems/Thm_Module_End_exists_mem_adjoin_apply_eq_self_and_apply_eq_zero_of_forall_ne_exists_ne.lean
  spec-pin: P2M/Sol/S_Module_End_nonempty_basis_fin_one_and_finrank_iInf_eigenspace_eq_one_of_iSupIndep_of_cyclic.lean
  spec-pin: P2M/Sol/S_Module_End_mem_span_prod_apply_and_finrank_iInf_eigenspace_le_one_of_divisorString.lean
  spec-pin: P2M/Sol/S_Module_End_exists_mem_adjoin_apply_eq_self_and_apply_eq_zero_of_forall_ne_exists_ne.lean
-/

import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Order.SupIndep
import Mathlib.NumberTheory.Divisors
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.Finiteness.Nakayama
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Data.Fintype.Basic

set_option autoImplicit false

open Module
namespace Module.End.MultiplicityOne

variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {ι : Type*} [Fintype ι]
    (V : ι → Submodule K W) (hVtop : iSup V = ⊤)
    (A : Subalgebra K (Module.End K W))
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hstab : ∀ a ∈ A, ∀ (i : ι), ∀ v ∈ V i, a v ∈ V i)
    (e : ι → ↥A) (he₁ : ∀ (i : ι), ∀ v ∈ V i, (e i : Module.End K W) v = v)
    (he₀ : ∀ (i j : ι), j ≠ i → ∀ v ∈ V j, (e i : Module.End K W) v = 0)
    (w : ι → W) (hw : ∀ i, w i ∈ V i)
    (hcyc : ∀ (i : ι), ∀ v ∈ V i, ∃ a : ↥A, (a : Module.End K W) (w i) = v)

include hVtop he₁ he₀ in
omit [FiniteDimensional K W] in
theorem decomp [DecidableEq ι] (v : W) :
    (∑ i, (e i : Module.End K W) v = v) ∧ ∀ i, (e i : Module.End K W) v ∈ V i := by
  have hv : v ∈ ⨆ i, V i := by rw [hVtop]; trivial
  refine Submodule.iSup_induction V
    (motive := fun v => (∑ i, (e i : Module.End K W) v = v) ∧ ∀ i, (e i : Module.End K W) v ∈ V i)
    hv ?_ ?_ ?_
  · intro j x hx
    constructor
    · rw [Finset.sum_eq_single j (fun i _ hij => he₀ i j (Ne.symm hij) x hx)
        (fun h => absurd (Finset.mem_univ j) h), he₁ j x hx]
    · intro i
      by_cases hij : j = i
      · subst hij; rw [he₁ j x hx]; exact hx
      · rw [he₀ i j hij x hx]; exact Submodule.zero_mem _
  · simp
  · intro x y hx hy
    constructor
    · simp only [map_add, Finset.sum_add_distrib, hx.1, hy.1]
    · intro i; rw [map_add]; exact Submodule.add_mem _ (hx.2 i) (hy.2 i)

include hVtop he₁ he₀ in
omit [FiniteDimensional K W] in
theorem e_apply_mem (i : ι) (v : W) : (e i : Module.End K W) v ∈ V i := by
  classical
  exact (decomp V hVtop A e he₁ he₀ v).2 i

include hVtop he₁ he₀ in
omit [FiniteDimensional K W] in
theorem sum_e_apply (v : W) : ∑ i, (e i : Module.End K W) v = v := by
  classical
  exact (decomp V hVtop A e he₁ he₀ v).1

def w0 : W := ∑ i, w i

include he₁ he₀ hw in
omit [FiniteDimensional K W] in
theorem e_w0 [DecidableEq ι] (i : ι) : (e i : Module.End K W) (w0 w) = w i := by
  unfold w0
  rw [map_sum, Finset.sum_eq_single i (fun j _ hji => he₀ i j hji _ (hw j))
    (fun h => absurd (Finset.mem_univ i) h), he₁ i _ (hw i)]

def ψ : ↥A →ₗ[↥A] W where
  toFun a := (a : Module.End K W) (w0 w)
  map_add' a b := by simp
  map_smul' c a := by
    simp only [smul_eq_mul, Subalgebra.coe_mul, Module.End.mul_apply, RingHom.id_apply]
    rfl

omit [FiniteDimensional K W] in
theorem ψ_apply (a : ↥A) : ψ A w a = (a : Module.End K W) (w0 w) := rfl

include hVtop he₁ he₀ hw hcyc in
omit [FiniteDimensional K W] in
theorem ψ_surjective : Function.Surjective (ψ A w) := by
  classical
  intro v
  have hdec := decomp V hVtop A e he₁ he₀ v
  choose a ha using fun i => hcyc i _ (hdec.2 i)
  refine ⟨∑ i, a i * e i, ?_⟩
  rw [ψ_apply, AddSubmonoidClass.coe_finsetSum, LinearMap.sum_apply]
  conv_rhs => rw [← hdec.1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Subalgebra.coe_mul, Module.End.mul_apply, e_w0 V A e he₁ he₀ w hw i, ha i]

include hVtop hcomm he₁ he₀ hw hcyc in
omit [FiniteDimensional K W] in
theorem ψ_injective : Function.Injective (ψ A w) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  rw [ψ_apply] at ha

  have hwi : ∀ i, (a : Module.End K W) (w i) = 0 := by
    intro i
    have h1 : (a : Module.End K W) (w i) = ((a : Module.End K W) * (e i : Module.End K W)) (w0 w) := by
      rw [Module.End.mul_apply, e_w0 V A e he₁ he₀ w hw i]
    rw [h1, hcomm _ a.2 _ (e i).2, Module.End.mul_apply, ha, map_zero]

  have hVi : ∀ i, ∀ v ∈ V i, (a : Module.End K W) v = 0 := by
    intro i v hv
    obtain ⟨b, hb⟩ := hcyc i v hv
    rw [← hb, ← Module.End.mul_apply, hcomm _ a.2 _ b.2, Module.End.mul_apply, hwi i, map_zero]

  apply Subtype.ext
  refine LinearMap.ext fun v => ?_
  rw [← sum_e_apply V hVtop A e he₁ he₀ v, map_sum]
  simp only [ZeroMemClass.coe_zero, LinearMap.zero_apply]
  exact Finset.sum_eq_zero fun i _ => hVi i _ (e_apply_mem V hVtop A e he₁ he₀ i v)

end Module.End.MultiplicityOne

namespace Module.End.MultiplicityOne

variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {ι : Type*} [Fintype ι]
    (V : ι → Submodule K W) (hVtop : iSup V = ⊤)
    (A : Subalgebra K (Module.End K W))
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (e : ι → ↥A) (he₁ : ∀ (i : ι), ∀ v ∈ V i, (e i : Module.End K W) v = v)
    (he₀ : ∀ (i j : ι), j ≠ i → ∀ v ∈ V j, (e i : Module.End K W) v = 0)
    (w : ι → W) (hw : ∀ i, w i ∈ V i)
    (hcyc : ∀ (i : ι), ∀ v ∈ V i, ∃ a : ↥A, (a : Module.End K W) (w i) = v)

noncomputable def ψe : ↥A ≃ₗ[↥A] W :=
  LinearEquiv.ofBijective (ψ A w)
    ⟨ψ_injective V hVtop A hcomm e he₁ he₀ w hw hcyc, ψ_surjective V hVtop A e he₁ he₀ w hw hcyc⟩

include V hVtop hcomm e he₁ he₀ w hw hcyc in
omit [FiniteDimensional K W] in
theorem nonempty_basis : Nonempty (Module.Basis (Fin 1) ↥A W) :=
  ⟨(Module.Basis.singleton (Fin 1) ↥A).map (ψe V hVtop A hcomm e he₁ he₀ w hw hcyc)⟩

include hVtop he₁ he₀ in
omit [FiniteDimensional K W] in
theorem sum_e_eq_one : ∑ i, e i = (1 : ↥A) := by
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_finsetSum, OneMemClass.coe_one]
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.sum_apply, Module.End.one_apply]
  exact sum_e_apply V hVtop A e he₁ he₀ v

include hVtop he₁ he₀ in
omit [FiniteDimensional K W] in
theorem e_mul_e_self (i : ι) : e i * e i = e i := by
  apply Subtype.ext
  rw [Subalgebra.coe_mul]
  refine LinearMap.ext fun v => ?_
  rw [Module.End.mul_apply]
  exact he₁ i _ (e_apply_mem V hVtop A e he₁ he₀ i v)

include hVtop he₁ he₀ in
omit [FiniteDimensional K W] in
theorem exists_chi_e_eq_one (χ : ↥A →ₐ[K] K) : ∃ i, χ (e i) = 1 := by
  classical
  by_contra h
  push Not at h
  have h01 : ∀ i, χ (e i) = 0 := by
    intro i
    have hsq : χ (e i) * χ (e i) = χ (e i) := by rw [← map_mul, e_mul_e_self V hVtop A e he₁ he₀ i]
    have : χ (e i) * (χ (e i) - 1) = 0 := by rw [mul_sub, mul_one, hsq, sub_self]
    rcases mul_eq_zero.mp this with h0 | h1
    · exact h0
    · exact absurd (sub_eq_zero.mp h1) (h i)
  have := congrArg χ (sum_e_eq_one V hVtop A e he₁ he₀)
  rw [map_sum, map_one] at this
  simp [h01] at this

def Eig (χ : ↥A →ₐ[K] K) : Submodule K W :=
  ⨅ a : ↥A, Module.End.eigenspace (a : Module.End K W) (χ a)

omit [FiniteDimensional K W] in
theorem mem_Eig {χ : ↥A →ₐ[K] K} {v : W} : v ∈ Eig A χ ↔ ∀ a : ↥A, (a : Module.End K W) v = χ a • v := by
  simp [Eig, Submodule.mem_iInf]

include hVtop he₁ he₀ in
omit [FiniteDimensional K W] in
theorem Eig_le (χ : ↥A →ₐ[K] K) {i : ι} (hi : χ (e i) = 1) : Eig A χ ≤ V i := by
  intro v hv
  rw [mem_Eig] at hv
  have := hv (e i)
  rw [hi, one_smul] at this
  rw [← this]
  exact e_apply_mem V hVtop A e he₁ he₀ i v

include hVtop he₁ he₀ in
theorem finrank_Eig_le (χ : ↥A →ₐ[K] K)
    (hle : ∀ (i : ι) (χ : ↥A →ₐ[K] K),
      Module.finrank K ↥(V i ⊓ ⨅ a : ↥A, Module.End.eigenspace (a : Module.End K W) (χ a)) ≤ 1) :
    Module.finrank K ↥(Eig A χ) ≤ 1 := by
  obtain ⟨i, hi⟩ := exists_chi_e_eq_one V hVtop A e he₁ he₀ χ
  have h : Eig A χ ≤ V i ⊓ ⨅ a : ↥A, Module.End.eigenspace (a : Module.End K W) (χ a) :=
    le_inf (Eig_le V hVtop A e he₁ he₀ χ hi) le_rfl
  exact (Submodule.finrank_mono h).trans (hle i χ)

end Module.End.MultiplicityOne

namespace Module.End.MultiplicityOne

variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {ι : Type*} [Fintype ι]
    (V : ι → Submodule K W) (hVtop : iSup V = ⊤)
    (A : Subalgebra K (Module.End K W))
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (e : ι → ↥A) (he₁ : ∀ (i : ι), ∀ v ∈ V i, (e i : Module.End K W) v = v)
    (he₀ : ∀ (i j : ι), j ≠ i → ∀ v ∈ V j, (e i : Module.End K W) v = 0)
    (w : ι → W) (hw : ∀ i, w i ∈ V i)
    (hcyc : ∀ (i : ι), ∀ v ∈ V i, ∃ a : ↥A, (a : Module.End K W) (w i) = v)

abbrev commRing : CommRing ↥A :=
  { (inferInstance : Ring ↥A) with mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }

include hcomm in

theorem exists_socle (χ : ↥A →ₐ[K] K) : ∃ b : ↥A, b ≠ 0 ∧ ∀ a : ↥A, a * b = χ a • b := by
  classical
  let : CommRing ↥A := commRing A hcomm
  have : FiniteDimensional K ↥A :=
    FiniteDimensional.of_injective A.val.toLinearMap Subtype.val_injective
  have : IsNoetherian ↥A ↥A := isNoetherian_of_tower K inferInstance
  have : IsArtinian K ↥A := inferInstance
  set m : Ideal ↥A := RingHom.ker χ with hm

  let f : ℕ →o (Submodule K ↥A)ᵒᵈ :=
    ⟨fun n => OrderDual.toDual ((m ^ n).restrictScalars K), fun i j hij => by
      change (m ^ j).restrictScalars K ≤ (m ^ i).restrictScalars K
      exact fun x hx => Ideal.pow_le_pow_right hij hx⟩
  obtain ⟨N, hN⟩ := IsArtinian.monotone_stabilizes f
  have hstab : m ^ N = m ^ (N + 1) := by
    have := hN (N + 1) (Nat.le_succ N)
    exact Submodule.restrictScalars_injective K _ _ (OrderDual.toDual.injective this)

  obtain ⟨r, hr1, hr2⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m (m ^ N)
    (IsNoetherian.noetherian _) (by change m ^ N ≤ m * m ^ N; rw [← pow_succ', ← hstab])
  have hχr : χ r = 1 := by
    have : χ (r - 1) = 0 := (RingHom.mem_ker).mp hr1
    rwa [map_sub, map_one, sub_eq_zero] at this
  have hr0 : r ≠ 0 := by rintro rfl; rw [map_zero] at hχr; exact zero_ne_one hχr

  have hP : ∃ n : ℕ, ∀ x ∈ m ^ n, r * x = 0 := ⟨N, fun x hx => hr2 x hx⟩
  set n₀ := Nat.find hP with hn₀def
  have hn₀ : ∀ x ∈ m ^ n₀, r * x = 0 := Nat.find_spec hP
  have hn₀ne : n₀ ≠ 0 := by
    intro h
    have := hn₀ 1 (by rw [h, pow_zero, Ideal.one_eq_top]; trivial)
    rw [mul_one] at this
    exact hr0 this
  obtain ⟨n', hn'⟩ := Nat.exists_eq_succ_of_ne_zero hn₀ne
  have hmin : ¬ ∀ x ∈ m ^ n', r * x = 0 := Nat.find_min hP (by rw [← hn₀def, hn']; exact Nat.lt_succ_self n')
  push Not at hmin
  obtain ⟨x, hx, hrx⟩ := hmin
  refine ⟨r * x, hrx, fun a => ?_⟩
  have ha' : a - algebraMap K ↥A (χ a) ∈ m := by
    rw [hm, RingHom.mem_ker, map_sub, AlgHom.commutes]
    simp
  have hkill : (a - algebraMap K ↥A (χ a)) * (r * x) = 0 := by
    rw [mul_left_comm]
    apply hn₀
    rw [hn', pow_succ']
    exact Ideal.mul_mem_mul ha' hx
  calc a * (r * x) = (a - algebraMap K ↥A (χ a)) * (r * x) + algebraMap K ↥A (χ a) * (r * x) := by ring
    _ = χ a • (r * x) := by rw [hkill, zero_add, Algebra.smul_def]

include hVtop hcomm he₁ he₀ hw hcyc in
theorem exists_mem_Eig_ne_zero (χ : ↥A →ₐ[K] K) : ∃ v ∈ Eig A χ, v ≠ 0 := by
  obtain ⟨b, hb0, hb⟩ := exists_socle A hcomm χ
  refine ⟨ψ A w b, ?_, ?_⟩
  · rw [mem_Eig]
    intro a
    rw [ψ_apply, ← Module.End.mul_apply, ← Subalgebra.coe_mul, hb a, Subalgebra.coe_smul,
      LinearMap.smul_apply]
  · intro h
    apply hb0
    apply ψ_injective V hVtop A hcomm e he₁ he₀ w hw hcyc
    rw [h, map_zero]

include hVtop hcomm he₁ he₀ hw hcyc in
theorem finrank_Eig_eq_one (χ : ↥A →ₐ[K] K)
    (hle : ∀ (i : ι) (χ : ↥A →ₐ[K] K),
      Module.finrank K ↥(V i ⊓ ⨅ a : ↥A, Module.End.eigenspace (a : Module.End K W) (χ a)) ≤ 1) :
    Module.finrank K ↥(Eig A χ) = 1 := by
  have h1 := finrank_Eig_le V hVtop A e he₁ he₀ χ hle
  obtain ⟨v, hv, hv0⟩ := exists_mem_Eig_ne_zero V hVtop A hcomm e he₁ he₀ w hw hcyc χ
  have h2 : 0 < Module.finrank K ↥(Eig A χ) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨v, hv⟩, fun h => hv0 (congrArg Subtype.val h)⟩
  omega

end Module.End.MultiplicityOne

namespace Module.End.DivisorString

open Module

private theorem mul_dvd_of_prime_of_not_dvd {D d q : ℕ} (hq : q.Prime) (hqD : q ∣ D)
    (hd : d ∣ D) (hqd : ¬ q ∣ d) : d * q ∣ D :=
  Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqd).symm hd hqD

private theorem cyclic_part (D : ℕ) (hD : D ≠ 0) (V : Type*) [AddCommGroup V] [Module ℂ V]
    (e : ℕ → V) (U : ℕ → Module.End ℂ V)
    (hdown : ∀ q : ℕ, q.Prime → q ∣ D → ∀ d : ℕ, d ∣ D → q ∣ d → U q (e d) = e (d / q)) :
    ∀ d : ℕ, d ∣ D → ∃ T ∈ Algebra.adjoin ℂ {A : Module.End ℂ V | ∃ q : ℕ, q.Prime ∧ q ∣ D ∧ A = U q},
      e d = T (e D) := by
  have key : ∀ n d : ℕ, d * n = D →
      ∃ T ∈ Algebra.adjoin ℂ {A : Module.End ℂ V | ∃ q : ℕ, q.Prime ∧ q ∣ D ∧ A = U q},
        e d = T (e D) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro d hdn
      rcases eq_or_ne n 1 with rfl | hn1
      · refine ⟨1, Subalgebra.one_mem _, ?_⟩
        rw [mul_one] at hdn
        rw [hdn, Module.End.one_apply]
      · obtain ⟨q, hq, k, rfl⟩ := Nat.exists_prime_and_dvd hn1
        have hk0 : k ≠ 0 := by
          rintro rfl
          apply hD
          rw [← hdn, mul_zero, mul_zero]
        have hqD : q ∣ D := ⟨d * k, by rw [← hdn]; ring⟩
        have hdqD : d * q ∣ D := ⟨k, by rw [← hdn]; ring⟩
        have hk : k < q * k := by nlinarith [hq.two_le, Nat.pos_of_ne_zero hk0]
        obtain ⟨T, hT, hTe⟩ := ih k hk (d * q) (by rw [← hdn]; ring)
        refine ⟨U q * T, Subalgebra.mul_mem _ (Algebra.subset_adjoin ⟨q, hq, hqD, rfl⟩) hT, ?_⟩
        rw [Module.End.mul_apply, ← hTe, hdown q hq hqD (d * q) hdqD (dvd_mul_left q d),
          Nat.mul_div_cancel d hq.pos]
  intro d hd
  obtain ⟨n, rfl⟩ := hd
  exact key n d rfl

private theorem eigen_part (D : ℕ) (hD : D ≠ 0)
    (V : Type*) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (e : ℕ → V)
    (hli : LinearIndependent ℂ (fun d : Nat.divisors D => e (d : ℕ)))
    (hspan : Submodule.span ℂ (Set.range fun d : Nat.divisors D => e (d : ℕ)) = ⊤)
    (U : ℕ → Module.End ℂ V)
    (hdown : ∀ q : ℕ, q.Prime → q ∣ D → ∀ d : ℕ, d ∣ D → q ∣ d → U q (e d) = e (d / q))
    (hbase : ∀ q : ℕ, q.Prime → q ∣ D → ∃ a b : ℂ, ∀ d : ℕ, d ∣ D → ¬ q ∣ d →
      U q (e d) = a • e d + b • e (d * q))
    (lam : ℕ → ℂ) :
    Module.finrank ℂ ↥(⨅ q ∈ D.primeFactors, Module.End.eigenspace (U q) (lam q)) ≤ 1 := by
  classical
  let b : Basis (Nat.divisors D) ℂ V := Basis.mk hli (by rw [hspan])
  have hb : ∀ i, b i = e (i : ℕ) := fun i => Basis.mk_apply hli _ i
  have h1D : (1 : ℕ) ∈ Nat.divisors D := Nat.one_mem_divisors.mpr hD

  have key : ∀ v : V, (∀ q : ℕ, q.Prime → q ∣ D → U q v = lam q • v) →
      b.repr v ⟨1, h1D⟩ = 0 → v = 0 := by
    intro v hv h1
    suffices hall : ∀ m : ℕ, ∀ i : Nat.divisors D, (i : ℕ) = m → b.repr v i = 0 by
      apply b.repr.injective
      rw [map_zero]
      ext i
      exact hall _ i rfl
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro i hi
      subst hi
      have hiD : (i : ℕ) ∣ D := Nat.dvd_of_mem_divisors i.2
      rcases eq_or_ne (i : ℕ) 1 with hi1 | hi1
      · have : i = ⟨1, h1D⟩ := Subtype.ext hi1
        rw [this]
        exact h1
      obtain ⟨q, hq, m', hm'⟩ := Nat.exists_prime_and_dvd hi1

      have hqD : q ∣ D := dvd_trans (Dvd.intro m' hm'.symm) hiD
      have hm'D : m' ∣ D := dvd_trans (Dvd.intro_left q hm'.symm) hiD
      have hm'mem : m' ∈ Nat.divisors D := Nat.mem_divisors.mpr ⟨hm'D, hD⟩
      have hm'0 : 0 < m' := Nat.pos_of_mem_divisors hm'mem
      have hm'lt : m' < (i : ℕ) := by rw [hm']; nlinarith [hq.two_le]
      have hv_sum : v = ∑ j, b.repr v j • e (j : ℕ) := by
        conv_lhs => rw [← b.sum_repr v]
        simp only [hb]
      obtain ⟨a, c, habc⟩ := hbase q hq hqD

      have hcoef : b.repr (U q v) ⟨m', hm'mem⟩ = b.repr v i := by
        calc b.repr (U q v) ⟨m', hm'mem⟩
            = b.repr (U q (∑ j, b.repr v j • e (j : ℕ))) ⟨m', hm'mem⟩ := by rw [← hv_sum]
          _ = ∑ j, b.repr v j * b.repr (U q (e (j : ℕ))) ⟨m', hm'mem⟩ := by
              rw [map_sum, map_sum, Finsupp.finsetSum_apply]
              simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
          _ = b.repr v i := by
              rw [Finset.sum_eq_single i]
              · rw [hdown q hq hqD i hiD (Dvd.intro m' hm'.symm)]
                have hdiv : (i : ℕ) / q = m' := by rw [hm', Nat.mul_div_cancel_left m' hq.pos]
                rw [hdiv, ← hb ⟨m', hm'mem⟩, b.repr_self, Finsupp.single_eq_same, mul_one]
              · intro j _ hj
                have hj' : (j : ℕ) ≠ (i : ℕ) := fun h => hj (Subtype.ext h)
                rcases lt_or_gt_of_ne hj' with hlt | hgt
                · rw [ih (j : ℕ) hlt j rfl, zero_mul]
                · have hjD : (j : ℕ) ∣ D := Nat.dvd_of_mem_divisors j.2
                  by_cases hqj : q ∣ (j : ℕ)
                  · rw [hdown q hq hqD j hjD hqj]
                    have hjq : (j : ℕ) / q ∈ Nat.divisors D :=
                      Nat.mem_divisors.mpr ⟨dvd_trans (Nat.div_dvd_of_dvd hqj) hjD, hD⟩
                    have hne : (⟨m', hm'mem⟩ : Nat.divisors D) ≠ ⟨(j : ℕ) / q, hjq⟩ := by
                      intro h
                      have h' : m' = (j : ℕ) / q := congrArg Subtype.val h
                      apply hj'
                      rw [← Nat.div_mul_cancel hqj, ← h', hm', mul_comm]
                    rw [← hb ⟨(j : ℕ) / q, hjq⟩, b.repr_self, Finsupp.single_eq_of_ne hne, mul_zero]
                  · rw [habc j hjD hqj, map_add, map_smul, map_smul, Finsupp.add_apply,
                      Finsupp.smul_apply, Finsupp.smul_apply]
                    have hjqD : (j : ℕ) * q ∈ Nat.divisors D :=
                      Nat.mem_divisors.mpr ⟨mul_dvd_of_prime_of_not_dvd hq hqD hjD hqj, hD⟩
                    have hne1 : (⟨m', hm'mem⟩ : Nat.divisors D) ≠ j := by
                      intro h
                      have h' : m' = (j : ℕ) := congrArg Subtype.val h
                      omega
                    have hne2 : (⟨m', hm'mem⟩ : Nat.divisors D) ≠ ⟨(j : ℕ) * q, hjqD⟩ := by
                      intro h
                      have h' : m' = (j : ℕ) * q := congrArg Subtype.val h
                      nlinarith [hq.two_le]
                    rw [← hb j, ← hb ⟨(j : ℕ) * q, hjqD⟩, b.repr_self, b.repr_self,
                      Finsupp.single_eq_of_ne hne1, Finsupp.single_eq_of_ne hne2,
                      smul_zero, smul_zero, add_zero, mul_zero]
              · intro h
                exact absurd (Finset.mem_univ i) h
      have heig : b.repr (U q v) ⟨m', hm'mem⟩ = b.repr (lam q • v) ⟨m', hm'mem⟩ := by
        rw [hv q hq hqD]
      rw [hcoef, map_smul, Finsupp.smul_apply, smul_eq_mul, ih m' hm'lt ⟨m', hm'mem⟩ rfl,
        mul_zero] at heig
      exact heig

  have hf : Function.Injective ((b.coord ⟨1, h1D⟩).comp
      (⨅ q ∈ D.primeFactors, Module.End.eigenspace (U q) (lam q)).subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have hw' : b.repr (w : V) ⟨1, h1D⟩ = 0 := hw
    have hw0 : (w : V) = 0 := by
      refine key w ?_ hw'
      intro q hq hqD
      have hwE := (Submodule.mem_iInf _).mp w.2 q
      exact Module.End.mem_eigenspace_iff.mp
        ((Submodule.mem_iInf _).mp hwE (Nat.mem_primeFactors.mpr ⟨hq, hqD, hD⟩))
    exact Subtype.ext hw0
  calc Module.finrank ℂ ↥(⨅ q ∈ D.primeFactors, Module.End.eigenspace (U q) (lam q))
      ≤ Module.finrank ℂ ℂ := LinearMap.finrank_le_finrank_of_injective hf
    _ = 1 := Module.finrank_self ℂ

end Module.End.DivisorString

namespace Module.End.SeparatingProjector

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : ι → Submodule K V) (𝒯 : Set (Module.End K V)) (c : Module.End K V → ι → K)
    (hT : ∀ T ∈ 𝒯, ∀ (i : ι), ∀ v ∈ W i, T v = c T i • v)
    (hsep : ∀ i j : ι, i ≠ j → ∃ T ∈ 𝒯, c T i ≠ c T j) (i : ι)

noncomputable def factor (T : Module.End K V) (j : ι) : Module.End K V :=
  (c T i - c T j)⁻¹ • (T - c T j • (1 : Module.End K V))

include hT in
omit [Fintype ι] [DecidableEq ι] in
theorem factor_apply_of_mem (T : Module.End K V) (hTm : T ∈ 𝒯) (j l : ι) (v : V) (hv : v ∈ W l) :
    factor c i T j v = ((c T i - c T j)⁻¹ * (c T l - c T j)) • v := by
  simp only [factor, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply, hT T hTm l v hv]
  rw [← sub_smul, smul_smul]

omit [Fintype ι] [DecidableEq ι] in
theorem factor_mem (T : Module.End K V) (hTm : T ∈ 𝒯) (j : ι) :
    factor c i T j ∈ Algebra.adjoin K 𝒯 := by
  unfold factor
  refine Subalgebra.smul_mem _ (Subalgebra.sub_mem _ (Algebra.subset_adjoin hTm) ?_) _
  exact Subalgebra.smul_mem _ (Subalgebra.one_mem _) _

include hT hsep in
omit [Fintype ι] in
theorem main_aux (s : Finset ι) (his : i ∉ s) :
    ∃ e ∈ Algebra.adjoin K 𝒯, (∀ v ∈ W i, e v = v) ∧ (∀ j ∈ s, ∀ v ∈ W j, e v = 0) ∧
      (∀ l : ι, ∀ v ∈ W l, ∃ a : K, e v = a • v) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨1, Subalgebra.one_mem _, fun v _ => rfl, fun j hj => absurd hj (Finset.notMem_empty j),
      fun l v _ => ⟨1, (one_smul K v).symm⟩⟩
  | insert j s hjs ih =>
    have hij : i ≠ j := fun h => his (h ▸ Finset.mem_insert_self j s)
    have his' : i ∉ s := fun h => his (Finset.mem_insert_of_mem h)
    obtain ⟨e, he, h1, h2, h3⟩ := ih his'
    obtain ⟨T, hTm, hcT⟩ := hsep i j hij
    refine ⟨factor c i T j * e, Subalgebra.mul_mem _ (factor_mem 𝒯 c i T hTm j) he, ?_, ?_, ?_⟩
    · intro v hv
      rw [Module.End.mul_apply, h1 v hv, factor_apply_of_mem W 𝒯 c hT i T hTm j i v hv,
        inv_mul_cancel₀ (sub_ne_zero.mpr hcT), one_smul]
    · intro l hl v hv
      rcases Finset.mem_insert.mp hl with rfl | hl
      · obtain ⟨a, ha⟩ := h3 l v hv
        rw [Module.End.mul_apply, ha, LinearMap.map_smul,
          factor_apply_of_mem W 𝒯 c hT i T hTm l l v hv, sub_self, mul_zero, zero_smul, smul_zero]
      · rw [Module.End.mul_apply, h2 l hl v hv, map_zero]
    · intro l v hv
      obtain ⟨a, ha⟩ := h3 l v hv
      refine ⟨(c T i - c T l)⁻¹ * (c T l - c T l) * a + ((c T i - c T j)⁻¹ * (c T l - c T j)) * a, ?_⟩
      rw [Module.End.mul_apply, ha, LinearMap.map_smul, factor_apply_of_mem W 𝒯 c hT i T hTm j l v hv,
        smul_smul]
      congr 1
      ring

end Module.End.SeparatingProjector

theorem Module.End.nonempty_basis_fin_one_and_finrank_iInf_eigenspace_eq_one_of_iSupIndep_of_cyclic
    {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {ι : Type*} [Fintype ι]
    (V : ι → Submodule K W) (hVind : iSupIndep V) (hVtop : iSup V = ⊤)
    (A : Subalgebra K (Module.End K W))
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hstab : ∀ a ∈ A, ∀ (i : ι), ∀ v ∈ V i, a v ∈ V i)
    (e : ι → ↥A) (he₁ : ∀ (i : ι), ∀ v ∈ V i, (e i : Module.End K W) v = v)
    (he₀ : ∀ (i j : ι), j ≠ i → ∀ v ∈ V j, (e i : Module.End K W) v = 0)
    (w : ι → W) (hw : ∀ i, w i ∈ V i)
    (hcyc : ∀ (i : ι), ∀ v ∈ V i, ∃ a : ↥A, (a : Module.End K W) (w i) = v)
    (hle : ∀ (i : ι) (χ : ↥A →ₐ[K] K),
      Module.finrank K ↥(V i ⊓ ⨅ a : ↥A, Module.End.eigenspace (a : Module.End K W) (χ a)) ≤ 1) :
    Nonempty (Module.Basis (Fin 1) ↥A W) ∧
    ∀ χ : ↥A →ₐ[K] K,
      Module.finrank K ↥(⨅ a : ↥A, Module.End.eigenspace (a : Module.End K W) (χ a)) = 1 := by
  have _ := hVind
  have _ := hstab
  exact ⟨Module.End.MultiplicityOne.nonempty_basis V hVtop A hcomm e he₁ he₀ w hw hcyc,
    fun χ => Module.End.MultiplicityOne.finrank_Eig_eq_one V hVtop A hcomm e he₁ he₀ w hw hcyc χ hle⟩

theorem Module.End.mem_span_prod_apply_and_finrank_iInf_eigenspace_le_one_of_divisorString
    (D : ℕ) (hD : D ≠ 0)
    (V : Type*) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (e : ℕ → V)
    (hli : LinearIndependent ℂ (fun d : Nat.divisors D => e (d : ℕ)))
    (hspan : Submodule.span ℂ (Set.range fun d : Nat.divisors D => e (d : ℕ)) = ⊤)
    (U : ℕ → Module.End ℂ V)
    (hcomm : ∀ p q : ℕ, p.Prime → q.Prime → p ∣ D → q ∣ D → Commute (U p) (U q))
    (hdown : ∀ q : ℕ, q.Prime → q ∣ D → ∀ d : ℕ, d ∣ D → q ∣ d → U q (e d) = e (d / q))
    (hbase : ∀ q : ℕ, q.Prime → q ∣ D → ∃ a b : ℂ, ∀ d : ℕ, d ∣ D → ¬ q ∣ d →
      U q (e d) = a • e d + b • e (d * q)) :
    (∀ d : ℕ, d ∣ D → ∃ T ∈ Algebra.adjoin ℂ {A : Module.End ℂ V | ∃ q : ℕ, q.Prime ∧ q ∣ D ∧ A = U q},
      e d = T (e D)) ∧
    ∀ lam : ℕ → ℂ,
      Module.finrank ℂ ↥(⨅ q ∈ D.primeFactors, Module.End.eigenspace (U q) (lam q)) ≤ 1 := by
  have _ := hcomm
  exact ⟨Module.End.DivisorString.cyclic_part D hD V e U hdown,
    Module.End.DivisorString.eigen_part D hD V e hli hspan U hdown hbase⟩

theorem Module.End.exists_mem_adjoin_apply_eq_self_and_apply_eq_zero_of_forall_ne_exists_ne
    {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : ι → Submodule K V) (𝒯 : Set (Module.End K V)) (c : Module.End K V → ι → K)
    (hT : ∀ T ∈ 𝒯, ∀ (i : ι), ∀ v ∈ W i, T v = c T i • v)
    (hsep : ∀ i j : ι, i ≠ j → ∃ T ∈ 𝒯, c T i ≠ c T j) (i : ι) :
    ∃ e ∈ Algebra.adjoin K 𝒯, (∀ v ∈ W i, e v = v) ∧ ∀ j : ι, j ≠ i → ∀ v ∈ W j, e v = 0 := by
  obtain ⟨e, he, h1, h2, -⟩ := Module.End.SeparatingProjector.main_aux W 𝒯 c hT hsep i
    (Finset.univ.erase i) (Finset.notMem_erase i Finset.univ)
  exact ⟨e, he, h1, fun j hj v hv => h2 j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩) v hv⟩
