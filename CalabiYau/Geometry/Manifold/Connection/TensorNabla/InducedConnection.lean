-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Geometry/Connection/TensorNabla/InducedConnection.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Manifold.LieDerivative.Tensor
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

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

variable [CompleteSpace 𝕜]

section ModelCovariantDerivative

def covariantDerivTensor0SModelAt (s : ℕ)
    (dα_X : Tensor0SModel (𝕜 := 𝕜) (E := E) s) (ΓX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  dα_X - lieDerivCorrection s ΓX α

omit [CompleteSpace 𝕜] in
@[simp] lemma covariantDeriv_tensor0SModelAt_apply (s : ℕ)
    (dα_X : Tensor0SModel (𝕜 := 𝕜) (E := E) s) (ΓX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s) :
    covariantDerivTensor0SModelAt (𝕜 := 𝕜) (E := E) s dα_X ΓX α =
      dα_X - lieDerivCorrection s ΓX α := by
  rfl

def covariantDerivTensorRSModelAt (r s : ℕ)
    (dT_X : TensorRSModel r s 𝕜 E) (ΓX : E →L[𝕜] E)
    (T : TensorRSModel r s 𝕜 E) :
    TensorRSModel r s 𝕜 E :=
  dT_X
    - (lieDerivCorrectionL (𝕜 := 𝕜) (E := E) s ΓX).comp T
    + T.comp (lieDerivCorrectionL (𝕜 := 𝕜) (E := E) r ΓX)

@[simp] theorem covariantDeriv_tensorRSModelAt_apply (r s : ℕ)
    (dT_X : TensorRSModel r s 𝕜 E) (ΓX : E →L[𝕜] E)
    (T : TensorRSModel r s 𝕜 E) :
    covariantDerivTensorRSModelAt (𝕜 := 𝕜) (E := E) r s dT_X ΓX T =
      dT_X
        - (lieDerivCorrectionL (𝕜 := 𝕜) (E := E) s ΓX).comp T
        + T.comp (lieDerivCorrectionL (𝕜 := 𝕜) (E := E) r ΓX) := by
  rfl

variable {Idx : Type*} [Fintype Idx]
section ChristoffelModel

variable {Idx : Type*} [Fintype Idx]

end ChristoffelModel

end ModelCovariantDerivative

section TangentCovariantDerivative

variable [IsManifold I 1 M]

def covariantDerivVectorField
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X Y : (x : M) → TangentSpace I x) (x : M) :
    TangentSpace I x :=
  cov Y x (X x)

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
@[simp] lemma covariantDeriv_vectorField_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X Y : (x : M) → TangentSpace I x) (x : M) :
    covariantDerivVectorField (I := I) cov X Y x = cov Y x (X x) := by
  rfl

noncomputable def tangentConstInChart (x₀ : M) (v : E) (p : M) :
    TangentSpace I p :=
  (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 p v

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
@[simp] lemma tangentConstInChart_apply (x₀ : M) (v : E) (p : M) :
    tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ v p =
      (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 p v := by
  rfl

section ConnectionEndomorphism

variable [IsManifold I 2 M]

end ConnectionEndomorphism

end TangentCovariantDerivative

section SmoothVectorFieldRSNabla

variable [IsManifold I 1 M] [IsManifold I (n + 1) M]

section ExtractedConnection

variable [IsManifold I 2 M]

end ExtractedConnection

end SmoothVectorFieldRSNabla

end

end TensorLieDeriv

namespace Tensor0SBundle

noncomputable section

open Bundle Set IsManifold ContinuousLinearMap VectorField Filter Function
    CalabiYau.TensorLieDeriv
open scoped Manifold Topology Bundle ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [CompleteSpace 𝕜]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable {n : WithTop ℕ∞}
variable [IsManifold I n M]
variable [IsManifold I (n + 1) M]

end

end Tensor0SBundle
end CalabiYau
