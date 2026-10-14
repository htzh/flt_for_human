/-
  The determinant-norm slab fundamental domain (listed, tier 1).

  `AutomorphicForm.exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc`
  (pin node 6616): for a number field `F` and any `α β : ℝ` (no order assumed) there is a set
  `S ⊆ {g | ideleNorm F (det g) ∈ Icc α β}` that is an `IsFundamentalDomain` for the left action
  of `(globalPoints (𝓞 F) F).range` against `adelicGLHaar` restricted to the slab. It is the
  producer of the `hS` argument of the weighted-Petersson headline (WORKORDER-SC2).

  The pin `S_` file is transcribed whole, in the pin's namespace shape: the generic engine
  `exists_exact_fundamental_domain` (pin 156) — the orbit/tile construction of a fundamental
  domain for a discrete subgroup of a second-countable topological group, with the translate and
  orbit helpers it needs — all `private`; the countability prelude that makes `GL₂(𝔸_F)` second
  countable, `private`; the adelic specialisation
  `exists_subset_slab_isFundamentalDomain` (pin 416), `private`; and the headline itself, stated
  verbatim from the pin `Theorems/` wrapper and proved by it.

  Reuse, do not re-prove (`FLTForHuman/NumberTheory/AdelicLevel/Countability.lean`, tier 3):
  `NumberField.AdelicCountability.secondCountableTopology_restrictedProduct` (pin 263) and
  `NumberField.AdelicCountability.isCountablyGenerated_uniformity_of_valued` (pin 246); the pin's
  local `private` copies are dropped. The already-homed definitions and premises are stated, not
  re-derived: `ideleNorm`, `ideleNorm_mul` (`NumberTheory/NumberField/TateGlobal/Defs.lean`),
  `globalPoints`, `AdelicGL2` (`AutomorphicForm/Adelic/Basic.lean`), `adelicGLHaar`, `glBorel`
  (`NumberTheory/AdelicHaar/GeneralLinear.lean`), `adelicBox` (`NumberTheory/AdelicBox.lean`),
  `NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc`
  (`NumberTheory/NumberField/TateGlobalIdeleNormDet.lean`) and
  `AutomorphicForm.ideleNorm_det_globalPoints` (`AutomorphicForm/Adelic/IdeleNormDet.lean`).

  Pin: `anthropics/fermats-last-theorem` at `aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`);
  port mathlib `v4.34.0`.
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc.lean
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.Basic
import FLTForHuman.AutomorphicForm.Adelic.IdeleNormDet
import FLTForHuman.NumberTheory.AdelicBox
import FLTForHuman.NumberTheory.AdelicHaar.GeneralLinear
import FLTForHuman.NumberTheory.AdelicLevel.Countability
import FLTForHuman.NumberTheory.NumberField.TateGlobal.Defs
import FLTForHuman.NumberTheory.NumberField.TateGlobalIdeleNormDet

set_option autoImplicit false

open MeasureTheory

noncomputable section

namespace AutomorphicForm

namespace DetNormSlabFundamentalDomain

section Engine

open Set
open scoped Pointwise ENNReal

section Generic

variable {G : Type*} [Group G] {Γ : Subgroup G}

-- pin: exists_isOpen_one_mem_mul_inv_subset (S_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc.lean:26)
private theorem exists_isOpen_one_mem_mul_inv_subset [TopologicalSpace G] [IsTopologicalGroup G]
    {V : Set G} (hVopen : IsOpen V) (hV1 : (1 : G) ∈ V) :
    ∃ W : Set G, IsOpen W ∧ (1 : G) ∈ W ∧ ∀ x ∈ W, ∀ y ∈ W, x * y⁻¹ ∈ V := by
  have hcont : Continuous fun p : G × G => p.1 * p.2⁻¹ :=
    continuous_fst.mul continuous_snd.inv
  have hopen : IsOpen ((fun p : G × G => p.1 * p.2⁻¹) ⁻¹' V) := hVopen.preimage hcont
  have hmem : ((1 : G), (1 : G)) ∈ (fun p : G × G => p.1 * p.2⁻¹) ⁻¹' V := by
    simpa using hV1
  obtain ⟨u, v, huopen, hvopen, hu1, hv1, huv⟩ := isOpen_prod_iff.mp hopen 1 1 hmem
  refine ⟨u ∩ v, huopen.inter hvopen, ⟨hu1, hv1⟩, ?_⟩
  intro x hx y hy
  have hxy : (x, y) ∈ u ×ˢ v := ⟨hx.1, hy.2⟩
  exact huv hxy

-- pin: rightTranslate (S_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc.lean:40)
private def rightTranslate (W : Set G) (h : G) : Set G :=
  (fun g : G => g * h⁻¹) ⁻¹' W

-- pin: isOpen_rightTranslate (S_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc.lean:43)
private theorem isOpen_rightTranslate [TopologicalSpace G] [IsTopologicalGroup G] {W : Set G}
    (hW : IsOpen W) (h : G) :
    IsOpen (rightTranslate W h) :=
  hW.preimage (continuous_mul_const h⁻¹)

-- pin: self_mem_rightTranslate (S_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc.lean:48)
private theorem self_mem_rightTranslate {W : Set G} (hW1 : (1 : G) ∈ W) (h : G) :
    h ∈ rightTranslate W h := by
  show h * h⁻¹ ∈ W
  rwa [mul_inv_cancel]

-- pin: eq_of_mul_mem_rightTranslate (S_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc.lean:53)
private theorem eq_of_mul_mem_rightTranslate {V W : Set G} (hVΓ : V ∩ (Γ : Set G) = {1})
    (hWV : ∀ x ∈ W, ∀ y ∈ W, x * y⁻¹ ∈ V) {h z : G} {γ δ : ↥Γ}
    (hγ : (γ : G) * z ∈ rightTranslate W h) (hδ : (δ : G) * z ∈ rightTranslate W h) :
    γ = δ := by
  have hγW : ((γ : G) * z) * h⁻¹ ∈ W := hγ
  have hδW : ((δ : G) * z) * h⁻¹ ∈ W := hδ
  have hkey : (((γ : G) * z) * h⁻¹) * (((δ : G) * z) * h⁻¹)⁻¹ ∈ V := hWV _ hγW _ hδW
  have hsimp : (((γ : G) * z) * h⁻¹) * (((δ : G) * z) * h⁻¹)⁻¹ = (γ : G) * (δ : G)⁻¹ := by
    simp only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left]
  rw [hsimp] at hkey
  have hmemΓ : (γ : G) * (δ : G)⁻¹ ∈ Γ := mul_mem γ.2 (inv_mem δ.2)
  have hone : (γ : G) * (δ : G)⁻¹ ∈ V ∩ (Γ : Set G) := ⟨hkey, hmemΓ⟩
  rw [hVΓ, Set.mem_singleton_iff, mul_inv_eq_one] at hone
  exact Subtype.ext hone

-- pin: orbitMeets (S_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc.lean:68)
private def orbitMeets (Γ : Subgroup G) (S : Set G) : Set G :=
  {x : G | ∃ γ : ↥Γ, (γ : G) * x ∈ S}

-- pin: subset_orbitMeets (S_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc.lean:71)
private theorem subset_orbitMeets (Γ : Subgroup G) (S : Set G) : S ⊆ orbitMeets Γ S := fun x hx =>
  ⟨1, by simpa using hx⟩

-- pin: isOpen_orbitMeets (S_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc.lean:74)
private theorem isOpen_orbitMeets [TopologicalSpace G] [IsTopologicalGroup G] {S : Set G}
    (hS : IsOpen S) : IsOpen (orbitMeets Γ S) := by
  have hrw : orbitMeets Γ S = ⋃ γ : ↥Γ, (fun x : G => (γ : G) * x) ⁻¹' S := by
    ext x
    simp only [orbitMeets, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_preimage]
  rw [hrw]
  exact isOpen_iUnion fun γ => hS.preimage (continuous_const_mul _)

-- pin: coe_mul_mem_orbitMeets_iff (S_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc.lean:82)
private theorem coe_mul_mem_orbitMeets_iff {S : Set G} (δ : ↥Γ) {x : G} :
    (δ : G) * x ∈ orbitMeets Γ S ↔ x ∈ orbitMeets Γ S := by
  constructor
  · rintro ⟨γ, hγ⟩
    exact ⟨γ * δ, by simpa [mul_assoc] using hγ⟩
  · rintro ⟨γ, hγ⟩
    exact ⟨γ * δ⁻¹, by simpa [mul_assoc] using hγ⟩

-- pin: fdPiece (S_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc.lean:90)
private def fdPiece (Γ : Subgroup G) (W : Set G) (e : ℕ → G) (n : ℕ) : Set G :=
  rightTranslate W (e n) \ ⋃ m, ⋃ (_ : m < n), orbitMeets Γ (rightTranslate W (e m))

-- pin: fdUnion (S_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc.lean:93)
private def fdUnion (Γ : Subgroup G) (W : Set G) (e : ℕ → G) : Set G :=
  ⋃ n, fdPiece Γ W e n

-- pin: mem_fdPiece_iff (S_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc.lean:96)
private theorem mem_fdPiece_iff {W : Set G} {e : ℕ → G} {n : ℕ} {x : G} :
    x ∈ fdPiece Γ W e n ↔ x ∈ rightTranslate W (e n) ∧
      x ∉ ⋃ m, ⋃ (_ : m < n), orbitMeets Γ (rightTranslate W (e m)) :=
  Iff.rfl

-- pin: mem_fdUnion_iff (S_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc.lean:101)
private theorem mem_fdUnion_iff {W : Set G} {e : ℕ → G} {x : G} :
    x ∈ fdUnion Γ W e ↔ ∃ n, x ∈ fdPiece Γ W e n :=
  Set.mem_iUnion

-- pin: not_mem_orbitMeets_of_mem_fdPiece (S_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc.lean:105)
private theorem not_mem_orbitMeets_of_mem_fdPiece {W : Set G} {e : ℕ → G} {m n : ℕ} (hmn : m < n)
    {x : G} (hx : x ∈ fdPiece Γ W e n) :
    x ∉ orbitMeets Γ (rightTranslate W (e m)) := fun hcon =>
  (mem_fdPiece_iff.mp hx).2 (Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨hmn, hcon⟩⟩)

-- pin: exists_coe_mul_mem_fdUnion (S_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc.lean:110)
private theorem exists_coe_mul_mem_fdUnion {W : Set G} {e : ℕ → G}
    (hcover : ∀ y : G, ∃ n : ℕ, y ∈ rightTranslate W (e n)) (x : G) :
    ∃ γ : ↥Γ, (γ : G) * x ∈ fdUnion Γ W e := by
  set N : Set ℕ := {n : ℕ | x ∈ orbitMeets Γ (rightTranslate W (e n))} with hN
  have hNne : N.Nonempty := by
    obtain ⟨n, hn⟩ := hcover x
    exact ⟨n, subset_orbitMeets Γ _ hn⟩
  have hmin : x ∈ orbitMeets Γ (rightTranslate W (e (sInf N))) := Nat.sInf_mem hNne
  obtain ⟨γ₀, hγ₀⟩ := hmin
  refine ⟨γ₀, mem_fdUnion_iff.mpr ⟨sInf N, mem_fdPiece_iff.mpr ⟨hγ₀, ?_⟩⟩⟩
  intro hcon
  rw [Set.mem_iUnion] at hcon
  obtain ⟨m, hm⟩ := hcon
  rw [Set.mem_iUnion] at hm
  obtain ⟨hmlt, hmem⟩ := hm
  have hxm : x ∈ orbitMeets Γ (rightTranslate W (e m)) :=
    (coe_mul_mem_orbitMeets_iff γ₀).mp hmem
  have hle : sInf N ≤ m := Nat.sInf_le hxm
  omega

-- pin: eq_of_coe_mul_mem_fdUnion (S_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc.lean:130)
private theorem eq_of_coe_mul_mem_fdUnion {V W : Set G} (hVΓ : V ∩ (Γ : Set G) = {1})
    (hWV : ∀ x ∈ W, ∀ y ∈ W, x * y⁻¹ ∈ V) {e : ℕ → G} {x : G} {γ δ : ↥Γ}
    (hγ : (γ : G) * x ∈ fdUnion Γ W e) (hδ : (δ : G) * x ∈ fdUnion Γ W e) :
    γ = δ := by
  obtain ⟨n, hγn⟩ := mem_fdUnion_iff.mp hγ
  obtain ⟨m, hδm⟩ := mem_fdUnion_iff.mp hδ
  have hstrict : ∀ (σ τ : ↥Γ) (i j : ℕ), i < j → (σ : G) * x ∈ fdPiece Γ W e i →
      (τ : G) * x ∈ fdPiece Γ W e j → False := by
    intro σ τ i j hij hσ hτ
    refine not_mem_orbitMeets_of_mem_fdPiece hij hτ ?_
    refine (coe_mul_mem_orbitMeets_iff τ).mpr ?_
    exact ⟨σ, (mem_fdPiece_iff.mp hσ).1⟩
  rcases lt_trichotomy n m with hnm | hnm | hnm
  · exact (hstrict γ δ n m hnm hγn hδm).elim
  · subst hnm
    exact eq_of_mul_mem_rightTranslate hVΓ hWV (mem_fdPiece_iff.mp hγn).1
      (mem_fdPiece_iff.mp hδm).1
  · exact (hstrict δ γ m n hnm hδm hγn).elim

-- pin: existsUnique_coe_mul_mem_fdUnion (S_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc.lean:149)
private theorem existsUnique_coe_mul_mem_fdUnion {V W : Set G} (hVΓ : V ∩ (Γ : Set G) = {1})
    (hWV : ∀ x ∈ W, ∀ y ∈ W, x * y⁻¹ ∈ V) {e : ℕ → G}
    (hcover : ∀ y : G, ∃ n : ℕ, y ∈ rightTranslate W (e n)) (x : G) :
    ∃! γ : ↥Γ, (γ : G) * x ∈ fdUnion Γ W e := by
  obtain ⟨γ₀, hγ₀⟩ := exists_coe_mul_mem_fdUnion hcover x
  exact ⟨γ₀, hγ₀, fun δ hδ => eq_of_coe_mul_mem_fdUnion hVΓ hWV hδ hγ₀⟩

-- the pin's `haveI` is load-bearing: it feeds the instance search below.
set_option linter.style.haveILetI false in
-- pin: exists_exact_fundamental_domain (S_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc.lean:156)
private theorem exists_exact_fundamental_domain [TopologicalSpace G] [IsTopologicalGroup G]
    (Γ : Subgroup G) (hsc : SecondCountableTopology G)
    (hdisc : ∃ V : Set G, IsOpen V ∧ V ∩ (Γ : Set G) = {1}) :
    ∃ F : Set G,
      (∃ U C : ℕ → Set G, (∀ n, IsOpen (U n)) ∧ (∀ n, IsOpen (C n)) ∧ F = ⋃ n, U n \ C n) ∧
      ∀ x : G, ∃! γ : ↥Γ, (γ : G) * x ∈ F := by
  obtain ⟨V, hVopen, hVΓ⟩ := hdisc
  have hV1 : (1 : G) ∈ V := by
    have h1 : (1 : G) ∈ V ∩ (Γ : Set G) := by
      rw [hVΓ]
      rfl
    exact h1.1
  obtain ⟨W, hWopen, hW1, hWV⟩ := exists_isOpen_one_mem_mul_inv_subset hVopen hV1
  haveI := hsc
  obtain ⟨T, hTc, hTcover⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun h : G => rightTranslate W h) (fun h => isOpen_rightTranslate hWopen h)
  have hmemT : ∀ y : G, y ∈ ⋃ h ∈ T, rightTranslate W h := by
    intro y
    have hy : y ∈ ⋃ h : G, rightTranslate W h :=
      Set.mem_iUnion.mpr ⟨y, self_mem_rightTranslate hW1 y⟩
    exact (Set.ext_iff.mp hTcover y).mpr hy
  have hTne : T.Nonempty := by
    rcases Set.eq_empty_or_nonempty T with hTe | hTne
    · exfalso
      have h1 := hmemT 1
      rw [hTe] at h1
      simp at h1
    · exact hTne
  obtain ⟨e, hTeq⟩ := hTc.exists_eq_range hTne
  have hcover : ∀ y : G, ∃ n : ℕ, y ∈ rightTranslate W (e n) := by
    intro y
    have hy := hmemT y
    rw [hTeq, Set.biUnion_range] at hy
    exact Set.mem_iUnion.mp hy
  refine ⟨fdUnion Γ W e,
    ⟨fun n => rightTranslate W (e n),
     fun n => ⋃ m, ⋃ (_ : m < n), orbitMeets Γ (rightTranslate W (e m)),
     fun n => isOpen_rightTranslate hWopen (e n),
     fun n => isOpen_iUnion fun m => isOpen_iUnion fun _ =>
       isOpen_orbitMeets (isOpen_rightTranslate hWopen (e m)),
     rfl⟩,
    fun x => existsUnique_coe_mul_mem_fdUnion hVΓ hWV hcover x⟩

end Generic

end Engine

section Countability

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField TopologicalSpace Filter

-- pin: instCountableNumberField (S_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc.lean:207)
private scoped instance instCountableNumberField (K : Type*) [Field K] [NumberField K] : Countable K :=
  (Module.finBasis ℚ K).equivFun.toEquiv.injective.countable

-- pin: instCountableIdeal (S_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc.lean:210)
private scoped instance instCountableIdeal (R : Type*) [CommRing R] [Countable R] [IsNoetherianRing R] :
    Countable (Ideal R) := by
  have hsurj : Function.Surjective (fun s : Finset R => Ideal.span (s : Set R)) := by
    intro I
    obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I)
    exact ⟨s, hs⟩
  exact hsurj.countable

-- pin: instCountableHeightOneSpectrum (S_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc.lean:218)
private scoped instance instCountableHeightOneSpectrum (R : Type*) [CommRing R] [IsDedekindDomain R]
    [Countable R] : Countable (HeightOneSpectrum R) := by
  have hinj : Function.Injective (fun v : HeightOneSpectrum R => v.asIdeal) := by
    intro v w h
    exact HeightOneSpectrum.ext h
  exact hinj.countable

-- pin: instCountableValueGroup₀ (S_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc.lean:225)
private scoped instance instCountableValueGroup₀ {R Γ₀ : Type*} [CommRing R] [LinearOrderedCommGroupWithZero Γ₀]
    [Countable Γ₀] (v : R →*₀ Γ₀) : Countable (MonoidWithZeroHom.ValueGroup₀ v) :=
  MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.injective.countable

-- pin: instCountableUnits (S_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc.lean:229)
private scoped instance instCountableUnits {M : Type*} [Monoid M] [Countable M] : Countable Mˣ :=
  Units.val_injective.countable

-- pin: instCountableWithZero (S_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc.lean:232)
private scoped instance instCountableWithZero {α : Type*} [Countable α] : Countable (WithZero α) := by
  classical
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat α
  refine ⟨⟨fun x => if h : x = 0 then 0 else f (WithZero.unzero h) + 1, fun a b hab => ?_⟩⟩
  dsimp only [] at hab
  by_cases ha : a = 0 <;> by_cases hb : b = 0
  · rw [ha, hb]
  · rw [dite_eq_left ha, dite_eq_right hb] at hab
    exact absurd hab.symm (Nat.succ_ne_zero _)
  · rw [dite_eq_right ha, dite_eq_left hb] at hab
    exact absurd hab (Nat.succ_ne_zero _)
  · rw [dite_eq_right ha, dite_eq_right hb] at hab
    rw [← WithZero.coe_unzero ha, ← WithZero.coe_unzero hb, hf (Nat.add_right_cancel hab)]

-- pin: instSecondCountableAdicCompletion (S_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc.lean:251)
private scoped instance instSecondCountableAdicCompletion (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] [Countable K] (v : HeightOneSpectrum R) :
    SecondCountableTopology (v.adicCompletion K) := by
  have hcg : (uniformity (v.adicCompletion K)).IsCountablyGenerated :=
    NumberField.AdelicCountability.isCountablyGenerated_uniformity_of_valued _
      (WithZero (Multiplicative ℤ))
  have hsep : SeparableSpace (v.adicCompletion K) :=
    ⟨_, Set.countable_range _, HeightOneSpectrum.denseRange_algebraMap (K := K) (v := v)⟩
  exact UniformSpace.secondCountable_of_separable _

open IsDedekindDomain in
open scoped RestrictedProduct in

-- the pin's `haveI` is load-bearing: it feeds the instance search below.
set_option linter.style.haveILetI false in
-- pin: instSecondCountableFiniteAdeleRing (S_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc.lean:298)
private scoped instance instSecondCountableFiniteAdeleRing (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] [Countable R] [Countable K] :
    SecondCountableTopology (FiniteAdeleRing R K) := by
  haveI : SecondCountableTopology
      (Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]) :=
    NumberField.AdelicCountability.secondCountableTopology_restrictedProduct
      fun v => Valued.isOpen_valuationSubring _
  exact inferInstanceAs <| SecondCountableTopology <|
    Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]

-- the pin's `haveI` walls are load-bearing: they feed the instance search below.
set_option linter.style.haveILetI false in
-- pin: instSecondCountableInfiniteAdeleRing (S_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc.lean:307)
private scoped instance instSecondCountableInfiniteAdeleRing (K : Type*) [Field K] [NumberField K] :
    SecondCountableTopology (InfiniteAdeleRing K) := by
  haveI : ∀ v : InfinitePlace K, SecondCountableTopology v.Completion := by
    intro v
    haveI : Countable (WithAbs v.1) := (WithAbs.equiv v.1).toEquiv.injective.countable
    haveI : SecondCountableTopology v.1.Completion := UniformSpace.secondCountable_of_separable _
    exact (NumberField.InfinitePlace.Completion.isometryEquivCompletion v).toHomeomorph.secondCountableTopology
  exact inferInstanceAs <| SecondCountableTopology <| (v : InfinitePlace K) → v.Completion

-- pin: instSecondCountableAdeleRing (S_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc.lean:316)
private scoped instance instSecondCountableAdeleRing (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [NumberField K] [Algebra R K] [IsFractionRing R K] [Countable R] :
    SecondCountableTopology (AdeleRing R K) :=
  inferInstanceAs <| SecondCountableTopology (InfiniteAdeleRing K × FiniteAdeleRing R K)

end Countability

section Adelic

open NumberField AutomorphicForm NumberField.AdelicHaar

attribute [local instance] NumberField.AdelicHaar.glBorel

variable (F : Type) [Field F] [NumberField F]

-- pin: instCountableRingOfIntegers (S_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc.lean:331)
private scoped instance instCountableRingOfIntegers : Countable (𝓞 F) :=
  Function.Injective.countable (RingOfIntegers.coe_injective (K := F))

-- the pin's `haveI` walls are load-bearing: they feed the instance search below.
set_option linter.style.haveILetI false in
-- pin: secondCountableTopology_adelicGL2 (S_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc.lean:334)
private scoped instance secondCountableTopology_adelicGL2 :
    SecondCountableTopology (AdelicGL2 (𝓞 F) F) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → AdeleRing (𝓞 F) F))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

-- pin: exists_isOpen_forall_algebraMap_mem_imp_eq_zero (S_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc.lean:342)
private theorem exists_isOpen_forall_algebraMap_mem_imp_eq_zero :
    ∃ U : Set (AdeleRing (𝓞 F) F), IsOpen U ∧ (0 : AdeleRing (𝓞 F) F) ∈ U ∧
      ∀ k : F, algebraMap F (AdeleRing (𝓞 F) F) k ∈ U → k = 0 := by
  obtain ⟨U₀, hU₀open, ⟨u₀, hu₀⟩, hU₀sub⟩ := NumberField.AdelicBox.exists_isOpen_subset_adelicBox F
  refine ⟨(fun x : AdeleRing (𝓞 F) F => x + u₀) ⁻¹' U₀,
    hU₀open.preimage (continuous_id.add continuous_const), ?_, ?_⟩
  · show (0 : AdeleRing (𝓞 F) F) + u₀ ∈ U₀
    rwa [zero_add]
  · intro k hk
    have h1 : algebraMap F (AdeleRing (𝓞 F) F) k + u₀ ∈ NumberField.AdelicBox.adelicBox F :=
      hU₀sub hk
    have h0 : algebraMap F (AdeleRing (𝓞 F) F) 0 + u₀ ∈ NumberField.AdelicBox.adelicBox F := by
      rw [map_zero, zero_add]
      exact hU₀sub hu₀
    exact (NumberField.AdelicBox.existsUnique_algebraMap_add_mem_adelicBox F u₀).unique h1 h0

variable {F} in

-- pin: val_globalPoints (S_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc.lean:360)
private theorem val_globalPoints (γ : Matrix.GeneralLinearGroup (Fin 2) F) :
    ((globalPoints (𝓞 F) F γ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = (γ : Matrix (Fin 2) (Fin 2) F).map (algebraMap F (AdeleRing (𝓞 F) F)) := by
  ext i j
  exact Matrix.GeneralLinearGroup.map_apply (algebraMap F (AdeleRing (𝓞 F) F)) i j γ

-- pin: exists_isOpen_inter_range_globalPoints_eq_singleton (S_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc.lean:366)
private theorem exists_isOpen_inter_range_globalPoints_eq_singleton :
    ∃ V : Set (AdelicGL2 (𝓞 F) F), IsOpen V ∧
      V ∩ ((globalPoints (𝓞 F) F).range : Set (AdelicGL2 (𝓞 F) F)) = {1} := by
  obtain ⟨U, hUopen, hU0, hU⟩ := exists_isOpen_forall_algebraMap_mem_imp_eq_zero F
  let ent : Fin 2 → Fin 2 → AdelicGL2 (𝓞 F) F → AdeleRing (𝓞 F) F := fun i j g =>
    ((g : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j
      - ((1 : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j
  have hent : ∀ i j, Continuous (ent i j) := fun i j =>
    (Units.continuous_val.matrix_elem i j).sub continuous_const
  refine ⟨⋂ i : Fin 2, ⋂ j : Fin 2, ent i j ⁻¹' U, ?_, ?_⟩
  · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      hUopen.preimage (hent i j)
  · ext g
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff,
      SetLike.mem_coe, MonoidHom.mem_range]
    constructor
    · rintro ⟨hg, γ, rfl⟩
      have hγ : ((γ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
        ext i j
        have := hg i j
        simp only [ent, val_globalPoints, Units.val_one, Matrix.map_apply] at this
        have h' : algebraMap F (AdeleRing (𝓞 F) F)
            (((γ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j
              - (1 : Matrix (Fin 2) (Fin 2) F) i j) ∈ U := by
          rw [map_sub]
          convert this using 2
          by_cases hij : i = j
          · subst hij; simp
          · simp [Matrix.one_apply_ne hij]
        exact sub_eq_zero.mp (hU _ h')
      have : γ = 1 := Units.ext hγ
      subst this
      exact map_one _
    · rintro rfl
      refine ⟨fun i j => ?_, 1, map_one _⟩
      simp only [ent, sub_self]
      exact hU0

variable {F} in

-- pin: globalPoints_mul_mem_slab (S_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc.lean:406)
private theorem globalPoints_mul_mem_slab {α β : ℝ} (γ : Matrix.GeneralLinearGroup (Fin 2) F)
    {g : AdelicGL2 (𝓞 F) F}
    (hg : g ∈ {g : AdelicGL2 (𝓞 F) F |
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}) :
    globalPoints (𝓞 F) F γ * g ∈ {g : AdelicGL2 (𝓞 F) F |
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} := by
  simp only [Set.mem_ofPred_eq] at hg ⊢
  rwa [map_mul, NumberField.TateGlobal.ideleNorm_mul, AutomorphicForm.ideleNorm_det_globalPoints,
    one_mul]

-- the pin's `haveI` is load-bearing: it feeds the `IsFundamentalDomain` elaboration below.
set_option linter.style.haveILetI false in
-- pin: exists_subset_slab_isFundamentalDomain (S_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc.lean:416)
private theorem exists_subset_slab_isFundamentalDomain (α β : ℝ) :
    ∃ S : Set (AdelicGL2 (𝓞 F) F),
      S ⊆ {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} ∧
      IsFundamentalDomain (globalPoints (𝓞 F) F).range S
        ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
          {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}) := by
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  obtain ⟨F₀, ⟨U, C, hU, hC, rfl⟩, hexact⟩ :=
    exists_exact_fundamental_domain (globalPoints (𝓞 F) F).range inferInstance
      (exists_isOpen_inter_range_globalPoints_eq_singleton F)
  set F₀ : Set (AdelicGL2 (𝓞 F) F) := ⋃ n, U n \ C n with hF₀
  have hF₀m : MeasurableSet F₀ :=
    MeasurableSet.iUnion fun n => (hU n).measurableSet.diff (hC n).measurableSet
  have hslab : MeasurableSet {g : AdelicGL2 (𝓞 F) F |
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} :=
    NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc F α β
  refine ⟨F₀ ∩ {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β},
    Set.inter_subset_right, ?_, ?_, ?_⟩
  · exact (hF₀m.inter hslab).nullMeasurableSet
  · refine ae_restrict_of_forall_mem hslab fun x hx => ?_
    obtain ⟨γ₀, hγ₀, -⟩ := hexact x
    obtain ⟨γ, hγ⟩ := MonoidHom.mem_range.mp γ₀.2
    refine ⟨γ₀, hγ₀, ?_⟩
    have : (γ₀ : AdelicGL2 (𝓞 F) F) * x = globalPoints (𝓞 F) F γ * x := by rw [hγ]
    show (γ₀ : AdelicGL2 (𝓞 F) F) * x ∈ {g : AdelicGL2 (𝓞 F) F |
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
    rw [this]
    exact globalPoints_mul_mem_slab γ hx
  · intro g₁ g₂ hne
    refine Disjoint.aedisjoint (Set.disjoint_left.mpr fun y hy₁ hy₂ => hne ?_)
    obtain ⟨a, ⟨ha, -⟩, rfl⟩ := hy₁
    obtain ⟨b, ⟨hb, -⟩, hab⟩ := hy₂
    have h₁ : ((g₁⁻¹ : ↥(globalPoints (𝓞 F) F).range) : AdelicGL2 (𝓞 F) F) * (g₁ • a) ∈ F₀ := by
      simpa [Subgroup.smul_def] using ha
    have h₂ : ((g₂⁻¹ : ↥(globalPoints (𝓞 F) F).range) : AdelicGL2 (𝓞 F) F) * (g₁ • a) ∈ F₀ := by
      have hab' : g₂ • b = g₁ • a := hab
      rw [← hab']; simpa [Subgroup.smul_def] using hb
    exact inv_injective ((hexact (g₁ • a)).unique h₁ h₂)

end Adelic

end DetNormSlabFundamentalDomain

open NumberField NumberField.AdelicHaar

attribute [local instance] NumberField.AdelicHaar.glBorel

-- pin: AutomorphicForm.exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc (S_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc.lean:468)
theorem exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc
    (F : Type) [Field F] [NumberField F] (α β : ℝ) :
    ∃ S : Set (AdelicGL2 (𝓞 F) F),
      S ⊆ {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} ∧
      IsFundamentalDomain (globalPoints (𝓞 F) F).range S
        ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
          {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}) :=
  DetNormSlabFundamentalDomain.exists_subset_slab_isFundamentalDomain F α β

end AutomorphicForm

end
