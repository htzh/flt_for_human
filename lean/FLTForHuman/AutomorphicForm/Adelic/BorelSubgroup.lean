/-  The Borel subgroup of `GL₂` and its diagonal characters.

  `borelSubgroup A` is the subgroup of upper-triangular matrices
  (`(x : Matrix _ _ A) 1 0 = 0`); `borelDiagFst`/`borelDiagSnd` are its two diagonal
  characters, `adelicBorel` the specialization at `GL₂(𝔸_K)`, and the file records how the
  global points and the central scalars sit inside it. This is the definitional ground of
  the induced-section and Bruhat-transversal layer.

  Transcribed verbatim from `Definitions/Def_AutomorphicForm_BorelSubgroup.lean`
  (pinned `aa2d8b3`), the pin namespace `AutomorphicForm` kept.-/
import FLTForHuman.AutomorphicForm.Adelic.LsXi
import FLTForHuman.AutomorphicForm.Adelic.ConstantTerm

set_option autoImplicit false

noncomputable section

namespace AutomorphicForm

section BorelCommRing

variable (A : Type*) [CommRing A]

-- pin: borelSubgroup (Def_AutomorphicForm_BorelSubgroup.lean:12)
def borelSubgroup : Subgroup (GL (Fin 2) A) where
  carrier := {x | (x : Matrix (Fin 2) (Fin 2) A) 1 0 = 0}
  mul_mem' := by
    intro x y hx hy
    have hx' : (x : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := hx
    have hy' : (y : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := hy
    show ((x * y : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0 = 0
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hx', hy']
    ring
  one_mem' := by
    show ((1 : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0 = 0
    rw [Matrix.GeneralLinearGroup.coe_one]
    exact Matrix.one_apply_ne (by decide)
  inv_mem' := by
    intro x hx
    have hx' : (x : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := hx
    show ((x⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0 = 0
    rw [Matrix.GeneralLinearGroup.coe_inv, Matrix.inv_def]
    simp [Matrix.adjugate_fin_two, hx']

-- pin: mem_borelSubgroup_iff (Def_AutomorphicForm_BorelSubgroup.lean:32)
@[simp] theorem mem_borelSubgroup_iff {x : GL (Fin 2) A} :
    x ∈ borelSubgroup A ↔ (x : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := Iff.rfl

-- pin: borel_entry_one_zero (Def_AutomorphicForm_BorelSubgroup.lean:35)
theorem borel_entry_one_zero (b : ↥(borelSubgroup A)) :
    ((b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := b.2

variable {A}

-- pin: borelDiagFst (Def_AutomorphicForm_BorelSubgroup.lean:40)
def borelDiagFst : ↥(borelSubgroup A) →* Aˣ where
  toFun b :=
    { val := ((b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0
      inv := (((b⁻¹ : ↥(borelSubgroup A)) : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0
      val_inv := by
        have hinv : (((b⁻¹ : ↥(borelSubgroup A)) : GL (Fin 2) A) :
            Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := (b⁻¹).2
        have h1 : (((b : GL (Fin 2) A) * ((b⁻¹ : ↥(borelSubgroup A)) : GL (Fin 2) A) :
            GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 := by
          rw [← Subgroup.coe_mul, mul_inv_cancel]
          show ((1 : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0 = 1
          rw [Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply_eq]
        rwa [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hinv,
          mul_zero, add_zero] at h1
      inv_val := by
        have hb : ((b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := b.2
        have h1 : ((((b⁻¹ : ↥(borelSubgroup A)) : GL (Fin 2) A) * (b : GL (Fin 2) A) :
            GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 := by
          rw [← Subgroup.coe_mul, inv_mul_cancel]
          show ((1 : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0 = 1
          rw [Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply_eq]
        rwa [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hb,
          mul_zero, add_zero] at h1 }
  map_one' := by
    apply Units.ext
    show ((1 : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0 = 1
    rw [Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply_eq]
  map_mul' b c := by
    apply Units.ext
    have hc : ((c : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := c.2
    show (((b * c : ↥(borelSubgroup A)) : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0
        = ((b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0
          * ((c : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0
    rw [Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two, hc, mul_zero, add_zero]

-- pin: borelDiagSnd (Def_AutomorphicForm_BorelSubgroup.lean:76)
def borelDiagSnd : ↥(borelSubgroup A) →* Aˣ where
  toFun b :=
    { val := ((b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1
      inv := (((b⁻¹ : ↥(borelSubgroup A)) : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1
      val_inv := by
        have hb : ((b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := b.2
        have h1 : (((b : GL (Fin 2) A) * ((b⁻¹ : ↥(borelSubgroup A)) : GL (Fin 2) A) :
            GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := by
          rw [← Subgroup.coe_mul, mul_inv_cancel]
          show ((1 : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1 = 1
          rw [Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply_eq]
        rwa [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hb,
          zero_mul, zero_add] at h1
      inv_val := by
        have hinv : (((b⁻¹ : ↥(borelSubgroup A)) : GL (Fin 2) A) :
            Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := (b⁻¹).2
        have h1 : ((((b⁻¹ : ↥(borelSubgroup A)) : GL (Fin 2) A) * (b : GL (Fin 2) A) :
            GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := by
          rw [← Subgroup.coe_mul, inv_mul_cancel]
          show ((1 : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1 = 1
          rw [Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply_eq]
        rwa [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hinv,
          zero_mul, zero_add] at h1 }
  map_one' := by
    apply Units.ext
    show ((1 : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1 = 1
    rw [Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply_eq]
  map_mul' b c := by
    apply Units.ext
    have hb : ((b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := b.2
    show (((b * c : ↥(borelSubgroup A)) : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1
        = ((b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1
          * ((c : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1
    rw [Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two, hb, zero_mul, zero_add]

-- pin: borelDiagFst_apply_val (Def_AutomorphicForm_BorelSubgroup.lean:112)
@[simp] theorem borelDiagFst_apply_val (b : ↥(borelSubgroup A)) :
    ((borelDiagFst b : Aˣ) : A) = ((b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0 := rfl

-- pin: borelDiagSnd_apply_val (Def_AutomorphicForm_BorelSubgroup.lean:115)
@[simp] theorem borelDiagSnd_apply_val (b : ↥(borelSubgroup A)) :
    ((borelDiagSnd b : Aˣ) : A) = ((b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1 := rfl

-- pin: det_borel_eq_diag_mul (Def_AutomorphicForm_BorelSubgroup.lean:118)
theorem det_borel_eq_diag_mul {x : GL (Fin 2) A} (hx : x ∈ borelSubgroup A) :
    Matrix.GeneralLinearGroup.det x
      = borelDiagFst (⟨x, hx⟩ : ↥(borelSubgroup A))
        * borelDiagSnd (⟨x, hx⟩ : ↥(borelSubgroup A)) := by
  apply Units.ext
  have hb : (x : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := hx
  show (x : Matrix (Fin 2) (Fin 2) A).det
      = (x : Matrix (Fin 2) (Fin 2) A) 0 0 * (x : Matrix (Fin 2) (Fin 2) A) 1 1
  rw [Matrix.det_fin_two, hb, mul_zero, sub_zero]

-- pin: unipotentGL2_mem_borelSubgroup (Def_AutomorphicForm_BorelSubgroup.lean:128)
theorem unipotentGL2_mem_borelSubgroup (x : A) : unipotentGL2 x ∈ borelSubgroup A := by
  show ((unipotentGL2 x : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0 = 0
  rw [unipotentGL2_coe]
  simp

-- pin: borelDiagFst_unipotentGL2 (Def_AutomorphicForm_BorelSubgroup.lean:133)
theorem borelDiagFst_unipotentGL2 (x : A) :
    borelDiagFst ⟨unipotentGL2 x, unipotentGL2_mem_borelSubgroup x⟩ = 1 := by
  apply Units.ext
  show ((unipotentGL2 x : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0 = 1
  rw [unipotentGL2_coe]
  simp

-- pin: borelDiagSnd_unipotentGL2 (Def_AutomorphicForm_BorelSubgroup.lean:140)
theorem borelDiagSnd_unipotentGL2 (x : A) :
    borelDiagSnd ⟨unipotentGL2 x, unipotentGL2_mem_borelSubgroup x⟩ = 1 := by
  apply Units.ext
  show ((unipotentGL2 x : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1 = 1
  rw [unipotentGL2_coe]
  simp

end BorelCommRing

section AdelicBorel

open NumberField

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

-- pin: adelicBorel (Def_AutomorphicForm_BorelSubgroup.lean:156)
abbrev adelicBorel : Subgroup (AdelicGL2 R K) := borelSubgroup (AdeleRing R K)

-- pin: globalPoints_apply (Def_AutomorphicForm_BorelSubgroup.lean:158)
theorem globalPoints_apply (γ : Matrix.GeneralLinearGroup (Fin 2) K) (i j : Fin 2) :
    ((globalPoints R K γ : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) i j
      = algebraMap K (AdeleRing R K) ((γ : Matrix (Fin 2) (Fin 2) K) i j) := rfl

-- pin: globalPoints_mem_adelicBorel (Def_AutomorphicForm_BorelSubgroup.lean:162)
theorem globalPoints_mem_adelicBorel {γ : Matrix.GeneralLinearGroup (Fin 2) K}
    (hγ : γ ∈ borelSubgroup K) : globalPoints R K γ ∈ adelicBorel R K := by
  have hγ' : (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := hγ
  show ((globalPoints R K γ : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 1 0 = 0
  rw [globalPoints_apply, hγ', map_zero]

-- pin: borelDiagFst_globalPoints (Def_AutomorphicForm_BorelSubgroup.lean:168)
theorem borelDiagFst_globalPoints {γ : Matrix.GeneralLinearGroup (Fin 2) K}
    (hγ : γ ∈ borelSubgroup K) (hmem : globalPoints R K γ ∈ adelicBorel R K) :
    borelDiagFst (⟨globalPoints R K γ, hmem⟩ : ↥(adelicBorel R K))
      = Units.map (algebraMap K (AdeleRing R K)) (borelDiagFst (⟨γ, hγ⟩ : ↥(borelSubgroup K))) := by
  apply Units.ext
  show ((globalPoints R K γ : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 0 0
      = algebraMap K (AdeleRing R K) ((γ : Matrix (Fin 2) (Fin 2) K) 0 0)
  exact globalPoints_apply R K γ 0 0

-- pin: borelDiagSnd_globalPoints (Def_AutomorphicForm_BorelSubgroup.lean:177)
theorem borelDiagSnd_globalPoints {γ : Matrix.GeneralLinearGroup (Fin 2) K}
    (hγ : γ ∈ borelSubgroup K) (hmem : globalPoints R K γ ∈ adelicBorel R K) :
    borelDiagSnd (⟨globalPoints R K γ, hmem⟩ : ↥(adelicBorel R K))
      = Units.map (algebraMap K (AdeleRing R K)) (borelDiagSnd (⟨γ, hγ⟩ : ↥(borelSubgroup K))) := by
  apply Units.ext
  show ((globalPoints R K γ : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 1 1
      = algebraMap K (AdeleRing R K) ((γ : Matrix (Fin 2) (Fin 2) K) 1 1)
  exact globalPoints_apply R K γ 1 1

-- pin: centralScalar_mem_adelicBorel (Def_AutomorphicForm_BorelSubgroup.lean:186)
theorem centralScalar_mem_adelicBorel (z : (AdeleRing R K)ˣ) :
    centralScalar R K z ∈ adelicBorel R K := by
  show ((centralScalar R K z : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 1 0 = 0
  have hval : ((centralScalar R K z : AdelicGL2 R K) :
      Matrix (Fin 2) (Fin 2) (AdeleRing R K)) = Matrix.scalar (Fin 2) (z : AdeleRing R K) := rfl
  rw [hval, Matrix.scalar_apply]
  exact Matrix.diagonal_apply_ne _ (by decide)

-- pin: borelDiagFst_centralScalar (Def_AutomorphicForm_BorelSubgroup.lean:194)
theorem borelDiagFst_centralScalar (z : (AdeleRing R K)ˣ)
    (hmem : centralScalar R K z ∈ adelicBorel R K) :
    borelDiagFst (⟨centralScalar R K z, hmem⟩ : ↥(adelicBorel R K)) = z := by
  apply Units.ext
  show ((centralScalar R K z : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 0 0
      = (z : AdeleRing R K)
  have hval : ((centralScalar R K z : AdelicGL2 R K) :
      Matrix (Fin 2) (Fin 2) (AdeleRing R K)) = Matrix.scalar (Fin 2) (z : AdeleRing R K) := rfl
  rw [hval, Matrix.scalar_apply, Matrix.diagonal_apply_eq]

-- pin: borelDiagSnd_centralScalar (Def_AutomorphicForm_BorelSubgroup.lean:204)
theorem borelDiagSnd_centralScalar (z : (AdeleRing R K)ˣ)
    (hmem : centralScalar R K z ∈ adelicBorel R K) :
    borelDiagSnd (⟨centralScalar R K z, hmem⟩ : ↥(adelicBorel R K)) = z := by
  apply Units.ext
  show ((centralScalar R K z : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 1 1
      = (z : AdeleRing R K)
  have hval : ((centralScalar R K z : AdelicGL2 R K) :
      Matrix (Fin 2) (Fin 2) (AdeleRing R K)) = Matrix.scalar (Fin 2) (z : AdeleRing R K) := rfl
  rw [hval, Matrix.scalar_apply, Matrix.diagonal_apply_eq]

end AdelicBorel

end AutomorphicForm
