/-
  SET-AF83C consumer: the Siegel window at height, read three ways.

  **The rows.** `FLTForHuman/AutomorphicForm/Adelic/WindowedSiegel/WindowVanishing.lean` carries the
  vanishing row (`exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mul_centralScalar_mem`):
  above an archimedean height `T₀`, a compact set `C` of `GL₂(𝔸_F)` meets `x⁻¹ · γ · y · z` only at
  upper-triangular `γ`. `FLTForHuman/AutomorphicForm/Adelic/ArchPeterssonPairing.lean` carries the
  archimedean test factor and the two integral identities of the archimedean–Petersson dictionary.

  **The readings.** Each zone spends a row on data the row itself does not name:

  * Zone 1 — **the row as a statement about rational unipotents.** `γ = unipotentGL2 t` has
    `γ 1 0 = t`, so the row says: no nontrivial rational unipotent lies in `x⁻¹ C y⁻¹ z⁻¹` above the
    height. This is the reading the cusp-realisation layer actually uses, and it is a statement about
    `F`, not about `GL₂`.
  * Zone 2 — **the row at `C = {1}`.** A singleton is compact, so the row applies verbatim and
    becomes an equation-to-conclusion implication: `x⁻¹ · γ · y · z = 1` forces `γ 1 0 = 0`.
  * Zone 3 — **the test-factor row is inhabited.** A smooth function's zero is a smooth compactly
    supported function whose `tsupport` avoids the singular matrices, so the row produces an
    archimedean test factor. Nothing here is new mathematics; it is the check that the row's
    hypotheses are satisfiable at all and that its conclusion is the port's `IsArchTestFactor`.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/AutomorphicFormSetAF83CConsumer.lean` and never enters the build.
-/
import FLTForHuman.AutomorphicForm.Adelic.WindowedSiegel.WindowVanishing
import FLTForHuman.AutomorphicForm.Adelic.WeylIntertwining
import FLTForHuman.AutomorphicForm.Adelic.ArchPeterssonPairing

set_option autoImplicit false

noncomputable section

open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped ENNReal Classical

namespace AutomorphicFormSetAF83CConsumer

/-! ### Zone 1 — no nontrivial rational *opposite* unipotent lies in the window above the height -/

/-- **Zone 1.** The row at the opposite-unipotent point `γ = w · n(t) · w`, whose `(1,0)` entry is
`t`: above the height `T₀`, that point can meet the compact set only at `t = 0`. This is the reading
the cusp-realisation layer uses — the row is a statement about `F`, not about `GL₂`.

(The naive reading at `γ = unipotentGL2 t` is vacuous: `unipotentGL2` is already upper triangular, so
`γ 1 0 = 0` holds by `rfl`. The row's content is exactly that the *other* Bruhat cell is excluded.) -/
theorem eq_zero_of_mem_of_height (F : Type) [Field F] [NumberField F]
    (C : Set (AdelicGL2 (𝓞 F) F)) (hC : IsCompact C) :
    ∃ T₀ : ℝ, ∀ (x y : AdelicGL2 (𝓞 F) F) (t : F) (z : (AdeleRing (𝓞 F) F)ˣ),
      glFin (𝓞 F) F x ∈ finiteIntegralGL2 (𝓞 F) F →
      glFin (𝓞 F) F y ∈ finiteIntegralGL2 (𝓞 F) F →
      T₀ < archHeight F (glArch (𝓞 F) F x) →
      T₀ < archHeight F (glArch (𝓞 F) F y) →
      x⁻¹ * globalPoints (𝓞 F) F (gl2Weyl * unipotentGL2 t * gl2Weyl) * y *
          centralScalar (𝓞 F) F z ∈ C →
      t = 0 := by
  obtain ⟨T₀, hT₀⟩ :=
    WindowedSiegel.exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mul_centralScalar_mem
      F hC
  refine ⟨T₀, fun x y t z hx hy hxh hyh hmem => ?_⟩
  have h := hT₀ x y hx hy hxh hyh (gl2Weyl * unipotentGL2 t * gl2Weyl) z hmem
  have hentry : (((gl2Weyl * unipotentGL2 t * gl2Weyl : GL (Fin 2) F)) :
      Matrix (Fin 2) (Fin 2) F) 1 0 = t := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [hentry] at h
  exact h

/-! ### Zone 2 — the row at the singleton `{1}` -/

/-- **Zone 2.** A singleton is compact, so the row specialises to an equation: if `x⁻¹ · γ · y · z`
is `1` above the height, then `γ` is upper triangular. -/
theorem one_zero_eq_zero_of_mem_singleton (F : Type) [Field F] [NumberField F] :
    ∃ T₀ : ℝ, ∀ (x y : AdelicGL2 (𝓞 F) F) (γ : GL (Fin 2) F) (z : (AdeleRing (𝓞 F) F)ˣ),
      glFin (𝓞 F) F x ∈ finiteIntegralGL2 (𝓞 F) F →
      glFin (𝓞 F) F y ∈ finiteIntegralGL2 (𝓞 F) F →
      T₀ < archHeight F (glArch (𝓞 F) F x) →
      T₀ < archHeight F (glArch (𝓞 F) F y) →
      x⁻¹ * globalPoints (𝓞 F) F γ * y * centralScalar (𝓞 F) F z =
        (1 : AdelicGL2 (𝓞 F) F) →
      (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  have hC : IsCompact ({1} : Set (AdelicGL2 (𝓞 F) F)) := isCompact_singleton
  obtain ⟨T₀, hT₀⟩ :=
    WindowedSiegel.exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mul_centralScalar_mem
      F hC
  exact ⟨T₀, fun x y γ z hx hy hxh hyh hmem =>
    hT₀ x y hx hy hxh hyh γ z (by simpa using hmem)⟩

/-! ### Zone 3 — the archimedean test factor row is inhabited -/

/-- **Zone 3.** The zero function is smooth, compactly supported, and its `tsupport` is empty, so the
row's hypotheses hold and the conclusion is the port's `IsArchTestFactor` at it. -/
theorem isArchTestFactor_zero (F : Type) [Field F] [NumberField F] :
    IsArchTestFactor F (fun _ => (0 : ℂ)) :=
  isArchTestFactor_of_contDiff_of_hasCompactSupport_of_tsupport_subset_isUnit_det F
    (fun _ => (0 : ℂ)) contDiff_const (HasCompactSupport.zero)
    (by simp [tsupport])

end AutomorphicFormSetAF83CConsumer
