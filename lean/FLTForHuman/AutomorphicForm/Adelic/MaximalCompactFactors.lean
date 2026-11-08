/-
  The one-place factors of the adelic maximal compact subgroup.

  `adelicMaximalCompact` splits along any finite set of places: `exists_mem_maximalCompactAt_mul_
  mem_maximalCompactAway_eq` writes `k ∈ adelicMaximalCompact` as `k = k₁ * k₂` with
  `k₁ ∈ maximalCompactAt S` (trivial at the finite places outside `S`) and
  `k₂ ∈ maximalCompactAway S` (trivial at the archimedean places and at the finite places in `S`).

  `exists_mem_maximalCompactAt_erase_mul_eq_of_mem_maximalCompactAt` is the one-place refinement:
  for `v ∈ S` an element of `maximalCompactAt S` peels as `k' * kv` with `k' ∈ maximalCompactAt
  (S.erase v)`, `kv ∈ maximalCompactAt {v}` of trivial archimedean part, and `k'` and `kv` commute —
  the shape the Weyl/shell arguments consume when they move one place at a time.
  `exists_eq_mul_archSupportedAt_of_mem_maximalCompactAt_empty` is its archimedean mirror at a fixed
  infinite place `w`: `k ∈ maximalCompactAt ∅` is a commuting product of a factor supported at `w`
  and one with trivial archimedean part at `w`.

  `exists_maximalCompactAway_subset_of_mem_nhds_one` is the neighbourhood basis: every neighbourhood
  of `1` contains some `maximalCompactAway S₀`. The engine is the cofinality of the `maximalCompactAway`
  family — antitone and directed by union of places — against a compact set that misses a smaller
  neighbourhood, via `IsCompact.elim_directed_family_closed`.

  `isCompact_rowIsometrySubgroup_detOne` is the archimedean half of the gate's own compactness
  argument at one place: the determinant-one row isometries of `w.Completion` are a closed subset of
  the matrices with every entry in `‖·‖ ≤ 1`.

  The place-decomposition prelude (`atPlace`, the element agreeing with `g` at one finite place and
  `1` elsewhere, with the two extensionality lemmas it is proved by) is `private` here and is used by
  the two big rows; it is written once.

  Transcribed from the five pin proof files
  `P2M/Sol/S_AutomorphicForm_{exists_mem_maximalCompactAt_mul_mem_maximalCompactAway_eq,
  exists_mem_maximalCompactAt_erase_mul_eq_of_mem_maximalCompactAt,
  exists_eq_mul_archSupportedAt_of_mem_maximalCompactAt_empty,
  exists_maximalCompactAway_subset_of_mem_nhds_one, isCompact_rowIsometrySubgroup_detOne}.lean`
  (pinned `aa2d8b3`). Each statement is the matching
  `Theorems/Thm_AutomorphicForm_*.lean` wrapper verbatim, at the wrapper's binders and the wrapper's
  name inside the root `AutomorphicForm` namespace.

  Body-level drift, per row (no statement touched):
  * `isCompact_rowIsometrySubgroup_detOne` — the pin's `Set.mem_setOf_eq` is the deprecated spelling
    at `v4.34.0` and is written `Set.mem_ofPred_eq`; the pin's `attribute [-instance]` line at the
    head of the row is dropped (no instance search of its proof reaches those instances).
  * `exists_mem_maximalCompactAt_mul_mem_maximalCompactAway_eq` — `classical` at the head of the
    proof: the `insert` case of the `Finset` induction needs `DecidableEq (HeightOneSpectrum _)`,
    which the pin's environment supplied.
  * `exists_maximalCompactAway_subset_of_mem_nhds_one` — at `v4.34.0`
    `IsCompact.elim_directed_family_closed` takes `Disjoint s (⋂ i, t i)` and returns
    `∃ i, Disjoint s (t i)`, where the pin used the `= ∅` form; the two steps are written in the
    `Disjoint` form.

  spec-pin: Theorems/Thm_AutomorphicForm_exists_mem_maximalCompactAt_mul_mem_maximalCompactAway_eq.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_exists_mem_maximalCompactAt_mul_mem_maximalCompactAway_eq.lean   -- comparable copy
  spec-pin: Theorems/Thm_AutomorphicForm_exists_mem_maximalCompactAt_erase_mul_eq_of_mem_maximalCompactAt.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_exists_mem_maximalCompactAt_erase_mul_eq_of_mem_maximalCompactAt.lean   -- comparable copy
  spec-pin: Theorems/Thm_AutomorphicForm_exists_eq_mul_archSupportedAt_of_mem_maximalCompactAt_empty.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_exists_eq_mul_archSupportedAt_of_mem_maximalCompactAt_empty.lean   -- comparable copy
  spec-pin: Theorems/Thm_AutomorphicForm_exists_maximalCompactAway_subset_of_mem_nhds_one.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_exists_maximalCompactAway_subset_of_mem_nhds_one.lean   -- comparable copy
  spec-pin: Theorems/Thm_AutomorphicForm_isCompact_rowIsometrySubgroup_detOne.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_isCompact_rowIsometrySubgroup_detOne.lean   -- comparable copy
-/
import FLTForHuman.AutomorphicForm.Adelic.AdelicMaximalCompact
import FLTForHuman.AutomorphicForm.Adelic.LevelCompactness
import FLTForHuman.AutomorphicForm.Adelic.ArchComponentDictionary
import FLTForHuman.AutomorphicForm.Adelic.ArchWeightChar
import FLTForHuman.NumberTheory.AdelicDock.LocalEmbedding

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm WindowedSiegel AdelicDock Filter Topology
open scoped NNReal

noncomputable section

namespace AutomorphicForm

/-! ## The place-decomposition prelude -/

section PlaceDecomposition

variable {F : Type} [Field F] [NumberField F]

/-- Two adelic matrices with the same finite components at every place are equal in their finite
part. -/
private theorem finEntry_eq {g h : AdelicGL2 (𝓞 F) F}
    (h₂ : ∀ w : HeightOneSpectrum (𝓞 F),
      finComponent (𝓞 F) F w (glFin (𝓞 F) F g) = finComponent (𝓞 F) F w (glFin (𝓞 F) F h))
    (i j : Fin 2) :
    ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2
      = ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 := by
  apply Subtype.ext
  funext w
  have := congrArg (fun m : GL (Fin 2) (w.adicCompletion F) =>
    (m : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) i j) (h₂ w)
  simp [finComponent_apply, glFin_apply] at this
  exact this

/-- Adelic matrices are determined by their archimedean part and their finite components. -/
private theorem adelicGL2_ext {g h : AdelicGL2 (𝓞 F) F}
    (h₁ : glArch (𝓞 F) F g = glArch (𝓞 F) F h)
    (h₂ : ∀ w : HeightOneSpectrum (𝓞 F),
      finComponent (𝓞 F) F w (glFin (𝓞 F) F g) = finComponent (𝓞 F) F w (glFin (𝓞 F) F h)) :
    g = h := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  apply Prod.ext
  · have := congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing F) =>
      (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) h₁
    simpa [glArch_apply] using this
  · exact finEntry_eq h₂ i j

/-- The adelic matrix agreeing with `g` at the finite place `v` and equal to `1` elsewhere. -/
def atPlace (v : HeightOneSpectrum (𝓞 F)) (g : GL (Fin 2) (v.adicCompletion F)) :
    AdelicGL2 (𝓞 F) F :=
  finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v g)

theorem glArch_atPlace (v : HeightOneSpectrum (𝓞 F)) (g : GL (Fin 2) (v.adicCompletion F)) :
    glArch (𝓞 F) F (atPlace v g) = 1 := glArch_finEmbed _ _ _

theorem finComponent_atPlace_self (v : HeightOneSpectrum (𝓞 F))
    (g : GL (Fin 2) (v.adicCompletion F)) :
    finComponent (𝓞 F) F v (glFin (𝓞 F) F (atPlace v g)) = g := by
  rw [atPlace, glFin_finEmbed, finComponent_localEmbed_self]

theorem finComponent_atPlace_of_ne (v : HeightOneSpectrum (𝓞 F))
    (g : GL (Fin 2) (v.adicCompletion F)) {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) :
    finComponent (𝓞 F) F w (glFin (𝓞 F) F (atPlace v g)) = 1 := by
  rw [atPlace, glFin_finEmbed, finComponent_localEmbed_of_ne _ _ _ _ hw]

theorem localEmbed_entries_integral (v : HeightOneSpectrum (𝓞 F))
    (g : GL (Fin 2) (v.adicCompletion F))
    (hg : ∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F)
    (i j : Fin 2) :
    ((localEmbed (𝓞 F) F v g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j ∈ integralFiniteAdeles (𝓞 F) F := by
  intro w
  rw [coe_localEmbed]
  by_cases hw : w = v
  · subst hw
    rw [localMat_apply_self]
    exact hg i j
  · rw [localMat_apply_of_ne _ _ _ _ i j hw, Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

theorem atPlace_mem (v : HeightOneSpectrum (𝓞 F)) {k : AdelicGL2 (𝓞 F) F}
    (hk : k ∈ adelicMaximalCompact F) :
    atPlace v (finComponent (𝓞 F) F v (glFin (𝓞 F) F k)) ∈ adelicMaximalCompact F := by
  set g := finComponent (𝓞 F) F v (glFin (𝓞 F) F k) with hgdef
  have hkf := mem_finiteIntegralGL2_iff.mp hk.1
  have hint : ∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F := by
    intro i j
    rw [hgdef, finComponent_apply]
    exact hkf.1 i j v
  have hint' : ∀ i j, ((g⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j
      ∈ v.adicCompletionIntegers F := by
    intro i j
    rw [hgdef, ← map_inv, ← map_inv, finComponent_apply]
    exact (mem_finiteIntegralGL2_iff.mp ((adelicMaximalCompact F).inv_mem hk).1).1 i j v
  refine ⟨?_, fun w => ?_⟩
  · rw [atPlace, glFin_finEmbed, mem_finiteIntegralGL2_iff]
    refine ⟨localEmbed_entries_integral v g hint, ?_⟩
    intro i j
    rw [← map_inv]
    exact localEmbed_entries_integral v g⁻¹ hint' i j
  · rw [glArch_atPlace, map_one]
    exact isRowIsometry_one

private theorem mul_atPlace_comm (v : HeightOneSpectrum (𝓞 F)) (k : AdelicGL2 (𝓞 F) F) :
    k * atPlace v (finComponent (𝓞 F) F v (glFin (𝓞 F) F k))
      = atPlace v (finComponent (𝓞 F) F v (glFin (𝓞 F) F k)) * k := by
  apply adelicGL2_ext
  · rw [map_mul, map_mul, glArch_atPlace, mul_one, one_mul]
  · intro w
    rw [map_mul, map_mul, map_mul, map_mul]
    by_cases hw : w = v
    · subst hw
      rw [finComponent_atPlace_self]
    · rw [finComponent_atPlace_of_ne _ _ hw, mul_one, one_mul]

end PlaceDecomposition

/-! ## The two-factor and one-place splits -/

theorem exists_mem_maximalCompactAt_mul_mem_maximalCompactAway_eq
    (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (k : AdelicGL2 (𝓞 F) F) (_hk : k ∈ adelicMaximalCompact F) :
    ∃ k₁ k₂ : AdelicGL2 (𝓞 F) F, k₁ ∈ maximalCompactAt F S ∧ k₂ ∈ maximalCompactAway F S ∧ k = k₁ * k₂ := by
  have hk := _hk
  classical
  induction S using Finset.induction_on with
  | empty =>
    set kf : AdelicGL2 (𝓞 F) F := finEmbed (𝓞 F) F (glFin (𝓞 F) F k) with hkf
    have hkfK : kf ∈ adelicMaximalCompact F := by
      refine ⟨?_, fun w => ?_⟩
      · rw [hkf, glFin_finEmbed]; exact hk.1
      · rw [hkf, glArch_finEmbed, map_one]; exact isRowIsometry_one
    refine ⟨k * kf⁻¹, kf, ?_, ?_, by rw [inv_mul_cancel_right]⟩
    · rw [mem_maximalCompactAt_iff]
      refine ⟨(adelicMaximalCompact F).mul_mem hk ((adelicMaximalCompact F).inv_mem hkfK), fun w _ => ?_⟩
      rw [map_mul, map_inv, hkf, glFin_finEmbed, mul_inv_cancel, map_one]
    · rw [mem_maximalCompactAway_iff]
      refine ⟨hkfK, by rw [hkf, glArch_finEmbed], fun w hw => ?_⟩
      simp at hw
  | insert v S hv IH =>
    obtain ⟨k₁, k₂, hk₁, hk₂, rfl⟩ := IH
    rw [mem_maximalCompactAt_iff] at hk₁
    rw [mem_maximalCompactAway_iff] at hk₂
    obtain ⟨hk₁K, hk₁S⟩ := hk₁
    obtain ⟨hk₂K, hk₂arch, hk₂S⟩ := hk₂
    set g := finComponent (𝓞 F) F v (glFin (𝓞 F) F k₂) with hgdef
    set kv : AdelicGL2 (𝓞 F) F := atPlace v g with hkvdef
    have hkvK : kv ∈ adelicMaximalCompact F := atPlace_mem v hk₂K
    have hcomm : k₂ * kv = kv * k₂ := mul_atPlace_comm v k₂
    refine ⟨k₁ * kv, kv⁻¹ * k₂, ?_, ?_, ?_⟩
    · rw [mem_maximalCompactAt_iff]
      refine ⟨(adelicMaximalCompact F).mul_mem hk₁K hkvK, fun w hw => ?_⟩
      rw [Finset.mem_insert, not_or] at hw
      rw [map_mul, map_mul, hk₁S w hw.2, hkvdef, finComponent_atPlace_of_ne _ _ hw.1, mul_one]
    · rw [mem_maximalCompactAway_iff]
      refine ⟨(adelicMaximalCompact F).mul_mem ((adelicMaximalCompact F).inv_mem hkvK) hk₂K, ?_, fun w hw => ?_⟩
      · rw [map_mul, map_inv, hkvdef, glArch_atPlace, inv_one, one_mul, hk₂arch]
      · rw [map_mul, map_mul, map_inv, map_inv]
        rcases Finset.mem_insert.mp hw with rfl | hwS
        · rw [hkvdef, finComponent_atPlace_self, hgdef, inv_mul_cancel]
        · have hwv : w ≠ v := fun h => hv (h ▸ hwS)
          rw [hk₂S w hwS, hkvdef, finComponent_atPlace_of_ne _ _ hwv, inv_one, mul_one]
    ·
      rw [mul_assoc, ← mul_assoc kv, mul_inv_cancel, one_mul]

open scoped Classical in
theorem exists_mem_maximalCompactAt_erase_mul_eq_of_mem_maximalCompactAt
    (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (v : HeightOneSpectrum (𝓞 F)) (_hv : v ∈ S)
    (k : AdelicGL2 (𝓞 F) F) (_hk : k ∈ maximalCompactAt F S) :
    ∃ k' kv : AdelicGL2 (𝓞 F) F,
      k' ∈ maximalCompactAt F (S.erase v) ∧
      kv ∈ maximalCompactAt F {v} ∧ glArch (𝓞 F) F kv = 1 ∧
      k = k' * kv ∧ k' * kv = kv * k' := by
  have hk := _hk
  rw [mem_maximalCompactAt_iff] at hk
  obtain ⟨hkK, hkS⟩ := hk
  set g := finComponent (𝓞 F) F v (glFin (𝓞 F) F k) with hgdef
  set kv : AdelicGL2 (𝓞 F) F := atPlace v g with hkvdef
  have hkvK : kv ∈ adelicMaximalCompact F := atPlace_mem v hkK
  have hcomm : k * kv = kv * k := mul_atPlace_comm v k
  refine ⟨k * kv⁻¹, kv, ?_, ?_, glArch_atPlace v g, by rw [inv_mul_cancel_right], ?_⟩
  · rw [mem_maximalCompactAt_iff]
    refine ⟨(adelicMaximalCompact F).mul_mem hkK ((adelicMaximalCompact F).inv_mem hkvK), fun w hw => ?_⟩
    rw [map_mul, map_mul, map_inv, map_inv]
    by_cases hwv : w = v
    · subst hwv
      rw [hkvdef, finComponent_atPlace_self, hgdef, mul_inv_cancel]
    · have hwS : w ∉ S := fun h => hw (Finset.mem_erase.mpr ⟨hwv, h⟩)
      rw [hkS w hwS, hkvdef, finComponent_atPlace_of_ne _ _ hwv, inv_one, mul_one]
  · rw [mem_maximalCompactAt_iff]
    refine ⟨hkvK, fun w hw => ?_⟩
    have hwv : w ≠ v := fun h => hw (Finset.mem_singleton.mpr h)
    rw [hkvdef, finComponent_atPlace_of_ne _ _ hwv]
  ·
    rw [inv_mul_cancel_right]
    calc k = kv * k * kv⁻¹ := by rw [← hcomm, mul_inv_cancel_right]
      _ = kv * (k * kv⁻¹) := by rw [mul_assoc]

/-! ## The archimedean mirror -/

section ArchPlace

variable (F : Type) [Field F] [NumberField F] (w : InfinitePlace F)

theorem gl_ext {g h : AdelicGL2 (𝓞 F) F} (h₁ : glArch (𝓞 F) F g = glArch (𝓞 F) F h)
    (h₂ : glFin (𝓞 F) F g = glFin (𝓞 F) F h) : g = h :=
  eq_of_glArch_eq_of_glFin_eq F h₁ h₂

variable (k : AdelicGL2 (𝓞 F) F)

/-- The factor of `k` supported at the infinite place `w`: trivial finite part, trivial
archimedean part away from `w`, and equal to `k`'s archimedean component at `w`. -/
private def kOne : AdelicGL2 (𝓞 F) F := adelicArchGLInclAt F w (archComponent F w (glArch (𝓞 F) F k))

private theorem glFin_kOne : glFin (𝓞 F) F (kOne F w k) = 1 := by
  rw [kOne, adelicArchGLInclAt, MonoidHom.comp_apply, glFin_adelicArchGLIncl]

private theorem archComponent_kOne_self :
    archComponent F w (glArch (𝓞 F) F (kOne F w k)) = archComponent F w (glArch (𝓞 F) F k) := by
  rw [kOne, adelicArchGLInclAt, MonoidHom.comp_apply, glArch_adelicArchGLIncl,
    archComponent_archGLIncl_self]

private theorem archComponent_kOne_of_ne {w' : InfinitePlace F} (hw : w' ≠ w) :
    archComponent F w' (glArch (𝓞 F) F (kOne F w k)) = 1 := by
  rw [kOne, adelicArchGLInclAt, MonoidHom.comp_apply, glArch_adelicArchGLIncl,
    archComponent_archGLIncl_of_ne _ hw]

private theorem kOne_comm : kOne F w k * k = k * kOne F w k := by
  refine gl_ext F (ext_archComponent fun w' => ?_) ?_
  · simp only [map_mul]
    rcases eq_or_ne w' w with rfl | hw
    · rw [archComponent_kOne_self]
    · rw [archComponent_kOne_of_ne F _ k hw, one_mul, mul_one]
  · simp only [map_mul]
    rw [glFin_kOne, one_mul, mul_one]

private theorem isRowIsometry_kOne (hk : k ∈ adelicMaximalCompact F) (w' : InfinitePlace F) :
    IsRowIsometry (archComponent F w' (glArch (𝓞 F) F (kOne F w k))) := by
  rcases eq_or_ne w' w with rfl | hw
  · rw [archComponent_kOne_self]; exact isRowIsometry_archComponent hk _
  · rw [archComponent_kOne_of_ne F _ k hw]; exact isRowIsometry_one

private theorem kOne_mem (hk : k ∈ adelicMaximalCompact F) :
    kOne F w k ∈ adelicMaximalCompact F := by
  refine ⟨?_, isRowIsometry_kOne F w k hk⟩
  rw [glFin_kOne]; exact (finiteIntegralGL2 (𝓞 F) F).one_mem

private theorem kOne_main (hk : k ∈ maximalCompactAt F ∅) :
    ∃ k₁ k₂ : AdelicGL2 (𝓞 F) F,
      k = k₁ * k₂ ∧ k₁ * k₂ = k₂ * k₁ ∧
      glFin (𝓞 F) F k₁ = 1 ∧
      (∀ w' : InfinitePlace F, w' ≠ w → archComponent F w' (glArch (𝓞 F) F k₁) = 1) ∧
      archComponent F w (glArch (𝓞 F) F k₁) = archComponent F w (glArch (𝓞 F) F k) ∧
      (∀ w' : InfinitePlace F, IsRowIsometry (archComponent F w' (glArch (𝓞 F) F k₁))) ∧
      k₂ ∈ maximalCompactAt F ∅ ∧ archComponent F w (glArch (𝓞 F) F k₂) = 1 := by
  have hk' := mem_maximalCompactAt_iff.mp hk
  refine ⟨kOne F w k, (kOne F w k)⁻¹ * k, (mul_inv_cancel_left _ _).symm, ?_, glFin_kOne F w k,
    fun w' hw => archComponent_kOne_of_ne F w k hw, archComponent_kOne_self F w k,
    isRowIsometry_kOne F w k hk'.1, ?_, ?_⟩
  · rw [mul_inv_cancel_left, mul_assoc, ← kOne_comm, ← mul_assoc, inv_mul_cancel, one_mul]
  · rw [mem_maximalCompactAt_iff]
    refine ⟨(adelicMaximalCompact F).mul_mem
      ((adelicMaximalCompact F).inv_mem (kOne_mem F w k hk'.1)) hk'.1, fun v hv => ?_⟩
    rw [map_mul, map_inv, map_mul, map_inv, glFin_kOne, map_one, inv_one, one_mul]
    exact hk'.2 v hv
  · rw [map_mul, map_inv, map_mul, map_inv, archComponent_kOne_self, inv_mul_cancel]

end ArchPlace

theorem exists_eq_mul_archSupportedAt_of_mem_maximalCompactAt_empty
    (F : Type) [Field F] [NumberField F] (k : AdelicGL2 (𝓞 F) F) (_hk : k ∈ maximalCompactAt F ∅) (w : InfinitePlace F) :
    ∃ k₁ k₂ : AdelicGL2 (𝓞 F) F,
      k = k₁ * k₂ ∧ k₁ * k₂ = k₂ * k₁ ∧
      glFin (𝓞 F) F k₁ = 1 ∧
      (∀ w' : InfinitePlace F, w' ≠ w → archComponent F w' (glArch (𝓞 F) F k₁) = 1) ∧
      archComponent F w (glArch (𝓞 F) F k₁) = archComponent F w (glArch (𝓞 F) F k) ∧
      (∀ w' : InfinitePlace F, IsRowIsometry (archComponent F w' (glArch (𝓞 F) F k₁))) ∧
      k₂ ∈ maximalCompactAt F ∅ ∧ archComponent F w (glArch (𝓞 F) F k₂) = 1 :=
  kOne_main F w k _hk

/-! ## The neighbourhood basis, and the archimedean determinant-one isometries -/

theorem exists_maximalCompactAway_subset_of_mem_nhds_one
    (F : Type) [Field F] [NumberField F]
    (W : Set (AdelicGL2 (𝓞 F) F)) (_hW : W ∈ 𝓝 (1 : AdelicGL2 (𝓞 F) F)) :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)),
      (maximalCompactAway F S₀ : Set (AdelicGL2 (𝓞 F) F)) ⊆ W := by
  classical
  obtain ⟨W', hW'W, hW'open, h1⟩ := mem_nhds_iff.mp _hW
  let t : Finset (HeightOneSpectrum (𝓞 F)) → Set (AdelicGL2 (𝓞 F) F) :=
    fun S => (maximalCompactAway F S : Set _)
  have htc : ∀ S, IsClosed (t S) := fun S => isClosed_maximalCompactAway F S
  have hanti : ∀ S S' : Finset (HeightOneSpectrum (𝓞 F)), S ⊆ S' → t S' ⊆ t S := by
    intro S S' hSS' k hk
    have hk' := mem_maximalCompactAway_iff.mp hk
    exact mem_maximalCompactAway_iff.mpr ⟨hk'.1, hk'.2.1, fun v hv => hk'.2.2 v (hSS' hv)⟩
  have hdir : Directed (· ⊇ ·) t := fun S S' =>
    ⟨S ∪ S', hanti S _ Finset.subset_union_left, hanti S' _ Finset.subset_union_right⟩
  have hcpt : IsCompact (t ∅ ∩ W'ᶜ) :=
    (isCompact_maximalCompactAway F ∅).inter_right hW'open.isClosed_compl
  have hinter : Disjoint (t ∅ ∩ W'ᶜ) (⋂ S, t S) := by
    rw [Set.disjoint_left]
    intro k hk hkall
    obtain ⟨-, hkW⟩ := hk
    apply hkW
    have hk1 : k = 1 := by
      rw [Set.mem_iInter] at hkall
      have h0 := mem_maximalCompactAway_iff.mp (hkall ∅)
      apply adelicGL2_ext
      · rw [h0.2.1, map_one]
      · intro w
        have hw := mem_maximalCompactAway_iff.mp (hkall {w})
        rw [hw.2.2 w (Finset.mem_singleton_self w), map_one, map_one]
    rw [hk1]; exact h1
  obtain ⟨S₀, hS₀⟩ := hcpt.elim_directed_family_closed t htc hinter hdir
  refine ⟨S₀, fun k hk => hW'W ?_⟩
  by_contra hkW
  exact Set.disjoint_left.mp hS₀ ⟨hanti ∅ S₀ (Finset.empty_subset _) hk, hkW⟩ hk

theorem isCompact_rowIsometrySubgroup_detOne
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) :
    IsCompact (rowIsometrySubgroup₀ w.Completion : Set (GL (Fin 2) w.Completion)) := by
  set A : Set w.Completion := {x | ‖x‖ ≤ 1} with hA_def
  have hA : IsCompact A := isCompact_setOf_norm_le_one_completion F w
  set C : Set (Matrix (Fin 2) (Fin 2) w.Completion) := {m | ∀ i j, m i j ∈ A} with hC_def
  have hC : IsCompact C := by
    have hpi : C = Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 => A := by
      ext m
      exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
    rw [hpi]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hA
  have hK : IsCompact ((Units.embedProduct (Matrix (Fin 2) (Fin 2) w.Completion)) ⁻¹'
      (C ×ˢ (MulOpposite.op '' C))) :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage
      (hC.prod (hC.image MulOpposite.continuous_op))
  have hclosed : IsClosed (rowIsometrySubgroup₀ w.Completion : Set (GL (Fin 2) w.Completion)) := by
    have hset : (rowIsometrySubgroup₀ w.Completion : Set (GL (Fin 2) w.Completion))
        = {k : GL (Fin 2) w.Completion |
              ((k : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det = 1}
            ∩ {k : GL (Fin 2) w.Completion | IsRowIsometry k} := by
      ext k
      simp only [SetLike.mem_coe, mem_rowIsometrySubgroup₀_iff, Set.mem_inter_iff, Set.mem_ofPred_eq]
    rw [hset]
    refine IsClosed.inter ?_ (isClosed_setOf_isRowIsometry w.Completion)
    exact isClosed_eq ((continuous_id.matrix_det).comp Units.continuous_val) continuous_const
  refine hK.of_isClosed_subset hclosed ?_
  have hmemC : ∀ k : GL (Fin 2) w.Completion, k ∈ rowIsometrySubgroup₀ w.Completion →
      (k : Matrix (Fin 2) (Fin 2) w.Completion) ∈ C := by
    intro k hk i j
    exact ((mem_rowIsometrySubgroup₀_iff _).1 hk).2.norm_apply_le_one i j
  intro k hk
  simp only [Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod, Set.mem_image]
  exact ⟨hmemC k hk, _, hmemC k⁻¹ ((rowIsometrySubgroup₀ w.Completion).inv_mem hk), rfl⟩

end AutomorphicForm

end
