/-
  The tier-1 façade for WORKORDER-TO4
  (`topics/automorphicForm/WORKORDER-TO4-unit-factorizable-trio.md`): the unit-factorizable trio
  of `AutomorphicForm` ready-shelf nodes, plus a fourth row on the archimedean cut.

  Each of the three trio headlines is stated verbatim from its pin `Theorems/` wrapper (pinned
  `aa2d8b3`) and delegates to the corresponding tier-3 kernel
  `AutomorphicForm.UnitFactorizable.Engine.<name>` in
  `FLTForHuman/AutomorphicForm/Adelic/UnitFactorizableEngine.lean`. The engine stays tier 3 and
  unlisted.

  `AutomorphicForm.exists_isUnitFactorizableAboveOfType_biInvariant_rightConv_ne_zero_of_mem_archCutSubmodule`
  (pin `P2M/Sol/S_…biInvariant_rightConv_ne_zero_of_mem_archCutSubmodule.lean`): a continuous `φ`
  with a nonzero value, left-invariant under the level
  `levelOne N ⊓ finiteAdelicGL2Subgroup` and lying in the archimedean cut `archCutSubmodule K tys`,
  has a factorizable test function of the prescribed archimedean type `tys`, bi-invariant under
  the same level, whose right convolution against `φ` is nonzero.  It is the trio's first row read
  at `L := K` on the *finite* set `S` of prime divisors of `N`: the approximating sequence
  `φn → φ` of `exists_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule` is
  sampled at an `n` where `rightConv K φ (φn n) g₀` is already nonzero — the `n` with value `0` are
  those of a closed set, and the sequence tends to `φ g₀ ≠ 0` — and the two remaining clauses (the
  `localIntegralSet` membership at every `v ∉ S`, and the commensurator decomposition
  `z = z₁ * z₂`) are the pin's
  `IsUnitFactorizableAbove.finComponent_glFin_mem_localIntegralSet_of_apply_ne_zero` and
  `exists_eq_mul_mem_levelOne_inf_finiteAdelicGL2Subgroup_commute_placeEmbed_of_forall_mem_localIntegralSet`,
  both already in the port (`Adelic/LocalIntegralSet.lean`, `Adelic/KfSmoothTensor.lean`).

  ## Port deltas

  - **Migration off `spec/old_check_stmts.py` `PORT_FILES`.**  This module was listed there, with
    one in-source `-- pin:` marker per row.  The markers are stripped and the three pin files they
    name are written into the header as `spec-pin` wire lines — the fourth line is the new row's
    `P2M/Sol/` source — and the module's `PORT_FILES` row is deleted while its `SOURCES` rows
    stay.  The three original statements are untouched: the markers were comments and the tier-1
    delegation bodies are unchanged.
  - **The fourth row's pin text is verbatim**, including its `open`s: the pin opens
    `AutomorphicForm` at its section head, which is what makes its bare `IsFactorizableTestFn`,
    `IsArchBiFinite`, `IsUnitFactorizableAboveOfType`, `archCutSubmodule`, `rightConv`,
    `finiteAdelicGL2Subgroup` and `localIntegralSet` spell.  Rather than broaden the file's open
    list (which would re-elaborate the three existing statements), the pin's own
    `open AutomorphicForm in` is put back in front of the one declaration (FR-0270).
  - **Two imports added** for that row's two premises: `Adelic/LocalIntegralSet.lean` and
    `Adelic/KfSmoothTensor.lean`.  Neither imports this module, so the additions are cycle-free;
    the engine import is unchanged.
  - **Nothing else.**  No statement re-spelt, no name renamed, no `set_option` installed.

  ## Build

  Heartbeat probe pair (`-DmaxHeartbeats`, one run per value, never installed): silent at
  `3000`, first failure at `2000` (a deterministic `whnf` timeout raised in the fourth row,
  `:123` — its `Ideal.finite_factors` set and the `Finset`/`⊓` statement are the expensive
  part).  The module's natural cost is far under the project's 4,000,000 cap, and it elaborates
  with no output at the default as well.

  spec-pin: Theorems/Thm_AutomorphicForm_exists_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule.lean
  spec-pin: Theorems/Thm_AutomorphicForm_exists_finTestFactor_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule.lean
  spec-pin: Theorems/Thm_AutomorphicForm_exists_isUnitFactorizableAboveOfType_principalLevel_tendsto_rightConv_of_mem_archCutSubmodule.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_exists_isUnitFactorizableAboveOfType_biInvariant_rightConv_ne_zero_of_mem_archCutSubmodule.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.UnitFactorizableEngine
import FLTForHuman.AutomorphicForm.Adelic.LocalIntegralSet
import FLTForHuman.AutomorphicForm.Adelic.KfSmoothTensor

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain

theorem AutomorphicForm.exists_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (NK : Ideal (𝓞 K)) (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (hNS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ NK → p ∈ SK)
    (tys : ArchTypeFamily L) (f : AdelicGL2 (𝓞 L) L → ℂ) (hf : Continuous f)
    (hlev : ∀ g : AdelicGL2 (𝓞 L) L,
      ∀ k ∈ levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L,
        f (g * k) = f g)
    (harch : f ∈ archCutSubmodule L tys) :
    ∃ φ : ℕ → (AdelicGL2 (𝓞 L) L → ℂ),
      (∀ n, IsUnitFactorizableAboveOfType K L tys
        (levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L) SK (φ n)) ∧
      ∀ g, Filter.Tendsto (fun n => rightConv L f (φ n) g) Filter.atTop (nhds (f g)) :=
  AutomorphicForm.UnitFactorizable.Engine.exists_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule
    K L NK SK hNS tys f hf hlev harch

theorem AutomorphicForm.exists_finTestFactor_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (NK : Ideal (𝓞 K)) (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (hNS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ NK → p ∈ SK)
    (tys : ArchTypeFamily L) (f : AdelicGL2 (𝓞 L) L → ℂ) (hf : Continuous f)
    (hlev : ∀ g : AdelicGL2 (𝓞 L) L,
      ∀ k ∈ levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L,
        f (g * k) = f g)
    (harch : f ∈ archCutSubmodule L tys) :
    ∃ (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ) (fa : ℕ → (GL (Fin 2) (InfiniteAdeleRing L) → ℂ)),
      IsFinTestFactor L ff ∧
      (∀ x : AdelicGL2 (𝓞 L) L, ff (glFin (𝓞 L) L x) ≠ 0 → ∃ a k : AdelicGL2 (𝓞 L) L,
        glFin (𝓞 L) L a = 1 ∧
        k ∈ levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L ∧ x = a * k) ∧
      (∀ n, IsArchTestFactor L (fa n)) ∧
      (∀ n, IsUnitFactorizableAboveOfType K L tys
        (levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L) SK
        (fun g => fa n (glArch (𝓞 L) L g) * ff (glFin (𝓞 L) L g))) ∧
      ∀ g, Filter.Tendsto
        (fun n => rightConv L f (fun x => fa n (glArch (𝓞 L) L x) * ff (glFin (𝓞 L) L x)) g)
        Filter.atTop (nhds (f g)) :=
  AutomorphicForm.UnitFactorizable.Engine.exists_finTestFactor_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule
    K L NK SK hNS tys f hf hlev harch

theorem AutomorphicForm.exists_isUnitFactorizableAboveOfType_principalLevel_tendsto_rightConv_of_mem_archCutSubmodule
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (NK : Ideal (𝓞 K)) (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (hNS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ NK → p ∈ SK)
    (tys : ArchTypeFamily L) (f : AdelicGL2 (𝓞 L) L → ℂ) (hf : Continuous f)
    (hlev : ∀ g : AdelicGL2 (𝓞 L) L,
      ∀ k ∈ principalLevel (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L,
        f (g * k) = f g)
    (harch : f ∈ archCutSubmodule L tys) :
    ∃ φ : ℕ → (AdelicGL2 (𝓞 L) L → ℂ),
      (∀ n, IsUnitFactorizableAboveOfType K L tys
        (principalLevel (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L) SK (φ n)) ∧
      ∀ g, Filter.Tendsto (fun n => rightConv L f (φ n) g) Filter.atTop (nhds (f g)) :=
  AutomorphicForm.UnitFactorizable.Engine.exists_isUnitFactorizableAboveOfType_principalLevel_tendsto_rightConv_of_mem_archCutSubmodule
    K L NK SK hNS tys f hf hlev harch

open AutomorphicForm in
theorem AutomorphicForm.exists_isUnitFactorizableAboveOfType_biInvariant_rightConv_ne_zero_of_mem_archCutSubmodule
    (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily K)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hcont : Continuous φ) (hne : ∃ g, φ g ≠ 0)
    (hlev : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
      φ (g * k) = φ g)
    (hφt : φ ∈ archCutSubmodule K tys) :
    ∃ f : AdelicGL2 (𝓞 K) K → ℂ,
      IsFactorizableTestFn K f ∧ IsArchBiFinite K tys f ∧
      (∀ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ∀ x, f (k * x) = f x ∧ f (x * k) = f x) ∧
      (∃ S : Finset (HeightOneSpectrum (𝓞 K)), (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ S) ∧
        IsUnitFactorizableAboveOfType K K tys (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) S f ∧
        ∀ z, f z ≠ 0 →
          (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
            finComponent (𝓞 K) K v (glFin (𝓞 K) K z) ∈ localIntegralSet K v) ∧
          ∃ z₁ z₂ : AdelicGL2 (𝓞 K) K, z = z₁ * z₂ ∧
            z₂ ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K ∧
            ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ xv : GL (Fin 2) (v.adicCompletion K),
              z₁ * UnramifiedWhittaker.placeEmbed K v xv = UnramifiedWhittaker.placeEmbed K v xv * z₁) ∧
      ∃ g, rightConv K φ f g ≠ 0 := by
  classical

  set S : Finset (HeightOneSpectrum (𝓞 K)) :=
    (Ideal.finite_factors (I := N) (by rw [Ne, Ideal.zero_eq_bot]; exact hN)).toFinset with hS
  have hNS : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ S := fun v hv =>
    (Set.Finite.mem_toFinset _).mpr hv

  have hmapI : ∀ (f : 𝓞 K →+* 𝓞 K), (∀ x, f x = x) → Ideal.map f N = N := by
    intro f hf
    have h : f = RingHom.id (𝓞 K) := RingHom.ext hf
    rw [h, Ideal.map_id]

  have key₁ : ∀ I : Ideal (𝓞 K), I = N →
      ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ levelOne (𝓞 K) K I ⊓ finiteAdelicGL2Subgroup K, φ (g * k) = φ g := by
    rintro I rfl; exact hlev
  have key₂ : ∀ I : Ideal (𝓞 K), I = N → ∀ f : AdelicGL2 (𝓞 K) K → ℂ,
      IsUnitFactorizableAboveOfType K K tys (levelOne (𝓞 K) K I ⊓ finiteAdelicGL2Subgroup K) S f →
      IsUnitFactorizableAboveOfType K K tys (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) S f := by
    rintro I rfl f h; exact h
  obtain ⟨φn, hφn', htend⟩ :=
    AutomorphicForm.exists_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule
      K K N S hNS tys φ hcont (key₁ _ (hmapI _ fun x => rfl)) hφt
  have hφn : ∀ n, IsUnitFactorizableAboveOfType K K tys (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) S (φn n) :=
    fun n => key₂ _ (hmapI _ fun x => rfl) _ (hφn' n)
  obtain ⟨g₀, hg₀⟩ := hne
  obtain ⟨n, hn⟩ := ((htend g₀).eventually (isOpen_compl_singleton.mem_nhds hg₀)).exists
  have hf := hφn n
  obtain ⟨⟨hbi, φa, φf, φS, hsl⟩, hbf⟩ := hf
  refine ⟨φn n, ⟨φa, φf, hsl.1, hsl.2.1, hsl.2.2.2.2.2⟩, hbf, fun k hk x => hbi k hk x,
    ⟨S, hNS, hφn n, fun z hz => ?_⟩, g₀, hn⟩
  have hint : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      finComponent (𝓞 K) K v (glFin (𝓞 K) K z) ∈ localIntegralSet K v := fun v hv =>
    AutomorphicForm.IsUnitFactorizableAbove.finComponent_glFin_mem_localIntegralSet_of_apply_ne_zero K _ S (φn n)
      (hφn n).1 z hz v hv
  exact ⟨hint, AutomorphicForm.exists_eq_mul_mem_levelOne_inf_finiteAdelicGL2Subgroup_commute_placeEmbed_of_forall_mem_localIntegralSet
    K N S hNS z hint⟩
