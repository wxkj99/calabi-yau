-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Geometry/LieDerivative/Tensor.lean
-- Locally modified.
/-
Author: Yuan Liao
Coauthor: Ayush Khaitan, Jack McCarthy
-/
module
public import CalabiYau.Geometry.Manifold.Tensor.RSTensor.Defs
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.VectorField.Pullback
public import CalabiYau.Geometry.Manifold.Tensor.RSTensor.Coordinates.Field

@[expose] public section

namespace CalabiYau
namespace TensorLieDeriv

noncomputable section

open Bundle Set IsManifold ContinuousLinearMap VectorField Filter
    CalabiYau.Tensor0SBundle Function
open scoped Manifold Topology Bundle ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable (n : WithTop ℕ∞ := ⊤) [IsManifold I n M]
variable {x x₀ : M} {s : Set M}

section VectorSpaceLieDeriv

variable {s : ℕ}

variable {s : ℕ}

noncomputable def substituteArg (s : ℕ) (i : Fin s)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (f : E →L[𝕜] E) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  α.compContinuousLinearMap (fun j => if j = i then f else ContinuousLinearMap.id 𝕜 E)

noncomputable def lieDerivCorrection (s : ℕ)
    (DX : E →L[𝕜] E) (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  ∑ i : Fin s, substituteArg s i α DX

end VectorSpaceLieDeriv

section ManifoldLieDeriv

variable {s : ℕ}

section SmoothVectorFieldLieDeriv

variable [IsManifold I 1 M]

variable {s : ℕ}
variable {X : ContMDiffSection I E n (TangentSpace I : M → Type _)}
variable {α β : (x : M) → Tensor0SSpace s I x}

end SmoothVectorFieldLieDeriv


section SmoothVectorFieldRSLieDeriv

variable [IsManifold I 1 M] [IsManifold I (n + 1) M]

end SmoothVectorFieldRSLieDeriv

lemma lieDeriv_correction_add (DX : E →L[𝕜] E)
    (α β : Tensor0SModel (𝕜 := 𝕜) (E := E) s) :
    lieDerivCorrection s DX (α + β) =
    lieDerivCorrection s DX α + lieDerivCorrection s DX β := by
  unfold lieDerivCorrection
  rw [← Finset.sum_add_distrib]
  congr 1

lemma lieDeriv_correction_smul (DX : E →L[𝕜] E) (c : 𝕜)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s) :
    lieDerivCorrection s DX (c • α) = c • lieDerivCorrection s DX α := by
  unfold lieDerivCorrection
  rw [Finset.smul_sum]
  congr 1

lemma substituteArg_add_right (i : Fin s)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s) (DX DY : E →L[𝕜] E) :
    substituteArg s i α (DX + DY) = substituteArg s i α DX + substituteArg s i α DY := by
  ext v
  simp only [substituteArg, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    add_apply]
  convert α.map_update_add (fun j => v j) i (DX (v i)) (DY (v i))
  all_goals
    rename_i j
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji]

lemma substituteArg_smul_right (i : Fin s)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s) (c : 𝕜) (DX : E →L[𝕜] E) :
    substituteArg s i α (c • DX) = c • substituteArg s i α DX := by
  ext v
  simp only [substituteArg, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    smul_apply]
  convert α.map_update_smul (fun j => v j) i c (DX (v i))
  all_goals
    rename_i j
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji]

lemma lieDeriv_correction_add_right (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (DX DY : E →L[𝕜] E) :
    lieDerivCorrection s (DX + DY) α =
      lieDerivCorrection s DX α + lieDerivCorrection s DY α := by
  unfold lieDerivCorrection
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact substituteArg_add_right (s := s) i α DX DY

lemma lieDeriv_correction_smul_right (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (c : 𝕜) (DX : E →L[𝕜] E) :
    lieDerivCorrection s (c • DX) α = c • lieDerivCorrection s DX α := by
  unfold lieDerivCorrection
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact substituteArg_smul_right (s := s) i α c DX
section

variable [CompleteSpace 𝕜]


noncomputable def lieDerivCorrectionL (s : ℕ) (DX : E →L[𝕜] E) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s →L[𝕜]
      Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  LinearMap.toContinuousLinearMap
    { toFun := fun α => lieDerivCorrection s DX α
      map_add' := fun α β => lieDeriv_correction_add (s := s) DX α β
      map_smul' := fun c α => lieDeriv_correction_smul (s := s) DX c α }

@[simp]
theorem lieDeriv_correctionL_apply (DX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s) :
    lieDerivCorrectionL (𝕜 := 𝕜) (E := E) s DX α = lieDerivCorrection s DX α := by
  simp [lieDerivCorrectionL]

noncomputable def lieDerivCorrectionOpL (s : ℕ) :
    (E →L[𝕜] E) →L[𝕜]
      (Tensor0SModel (𝕜 := 𝕜) (E := E) s →L[𝕜]
        Tensor0SModel (𝕜 := 𝕜) (E := E) s) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun DX => lieDerivCorrectionL (𝕜 := 𝕜) (E := E) s DX
      map_add' := fun DX DY => by
        ext α
        simp [lieDeriv_correction_add_right]
      map_smul' := fun c DX => by
        ext α
        simp [lieDeriv_correction_smul_right] }

@[simp]
theorem lieDeriv_correctionOpL_apply (DX : E →L[𝕜] E) :
    lieDerivCorrectionOpL (𝕜 := 𝕜) (E := E) s DX =
      lieDerivCorrectionL (𝕜 := 𝕜) (E := E) s DX := by
  simp [lieDerivCorrectionOpL]

end

end ManifoldLieDeriv

end

end TensorLieDeriv
end CalabiYau
