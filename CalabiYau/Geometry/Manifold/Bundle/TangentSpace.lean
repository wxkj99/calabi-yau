-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Bundle/TangentSpace.lean
-- Locally modified.
module
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

@[expose] public section

namespace CalabiYau

open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

def tangentSpaceModelContinuousLinearEquiv (x : M) : TangentSpace I x ≃L[𝕜] E := by
  unfold TangentSpace
  exact ContinuousLinearEquiv.refl 𝕜 E

theorem tangentSpaceModelContinuousLinearEquiv_apply (x : M)
    (v : TangentSpace I x) : tangentSpaceModelContinuousLinearEquiv (I := I) x v = v := by
  rfl

theorem tangentSpaceModelContinuousLinearEquiv_symm_apply (x : M) (v : E) :
    (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm v = v := by
  rfl

noncomputable def tangentLinearMapToModel
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    {x : M} {y : M'} (A : TangentSpace I x →L[𝕜] TangentSpace I' y) : E →L[𝕜] E' :=
  (tangentSpaceModelContinuousLinearEquiv (I := I') y).toContinuousLinearMap.comp
    (A.comp (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm.toContinuousLinearMap)

theorem tangentLinearMapToModel_apply
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    {x : M} {y : M'} (A : TangentSpace I x →L[𝕜] TangentSpace I' y) (v : E) :
    tangentLinearMapToModel A v =
      tangentSpaceModelContinuousLinearEquiv (I := I') y
        (A ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm v)) := by
  rfl

theorem tangentLinearMapToModel_injective
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    {x : M} {y : M'} :
    Function.Injective
      (tangentLinearMapToModel (I := I) (I' := I') (x := x) (y := y)) := by
  intro A B h
  apply ContinuousLinearMap.ext
  intro v
  apply (tangentSpaceModelContinuousLinearEquiv (I := I') y).injective
  have hv := DFunLike.congr_fun h
    (tangentSpaceModelContinuousLinearEquiv (I := I) x v)
  simpa only [tangentLinearMapToModel_apply,
    ContinuousLinearEquiv.symm_apply_apply] using hv

noncomputable def tangentLinearMapOfModel
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    {x : M} {y : M'} (A : E →L[𝕜] E') :
    TangentSpace I x →L[𝕜] TangentSpace I' y :=
  (tangentSpaceModelContinuousLinearEquiv (I := I') y).symm.toContinuousLinearMap.comp
    (A.comp (tangentSpaceModelContinuousLinearEquiv (I := I) x).toContinuousLinearMap)

theorem ModelWithCorners.hasMFDerivAt_model (I : ModelWithCorners 𝕜 E H) {x : H} :
    HasMFDerivAt I 𝓘(𝕜, E) I x
      (tangentLinearMapOfModel (I := I) (I' := 𝓘(𝕜, E))
        (x := x) (y := I x) (ContinuousLinearMap.id 𝕜 E)) := by
  refine ⟨I.continuousAt, ?_⟩
  exact (hasFDerivWithinAt_id (𝕜 := 𝕜) (I x) _).congr'
    I.rightInvOn (Set.mem_range_self x)

theorem ModelWithCorners.hasMFDerivWithinAt_model
    (I : ModelWithCorners 𝕜 E H) {s : Set H} {x : H} :
    HasMFDerivWithinAt I 𝓘(𝕜, E) I s x
      (tangentLinearMapOfModel (I := I) (I' := 𝓘(𝕜, E))
        (x := x) (y := I x) (ContinuousLinearMap.id 𝕜 E)) :=
  (ModelWithCorners.hasMFDerivAt_model I).hasMFDerivWithinAt

noncomputable def modelLinearMapToTangent
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {A : E →L[𝕜] E'} {x : E} {y : E'} :
    TangentSpace 𝓘(𝕜, E) x →L[𝕜] TangentSpace 𝓘(𝕜, E') y :=
  (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(𝕜, E')) y).symm.toContinuousLinearMap.comp
    (A.comp (tangentSpaceModelContinuousLinearEquiv
      (I := 𝓘(𝕜, E)) x).toContinuousLinearMap)

theorem tangentLinearMapToModel_modelLinearMapToTangent
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {A : E →L[𝕜] E'} {x : E} {y : E'} :
    tangentLinearMapToModel
        (modelLinearMapToTangent (x := x) (y := y) (A := A)) = A := by
  ext v
  rfl

theorem HasFDerivWithinAt.hasMFDerivWithinAt_model
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {f : E → E'} {s : Set E} {x : E} {A : E →L[𝕜] E'}
    (h : HasFDerivWithinAt f A s x) :
    HasMFDerivWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') f s x
      (modelLinearMapToTangent (x := x) (y := f x) (A := A)) := by
  have hraw := h.hasMFDerivWithinAt
  refine hraw.congr_mfderiv ?_
  apply tangentLinearMapToModel_injective
  rw [tangentLinearMapToModel_modelLinearMapToTangent]
  ext v
  rfl

theorem HasFDerivAt.hasMFDerivAt_model
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {f : E → E'} {x : E} {A : E →L[𝕜] E'}
    (h : HasFDerivAt f A x) :
    HasMFDerivAt 𝓘(𝕜, E) 𝓘(𝕜, E') f x
      (modelLinearMapToTangent (x := x) (y := f x) (A := A)) :=
  hasMFDerivWithinAt_univ.mp
    (HasFDerivWithinAt.hasMFDerivWithinAt_model
      (s := Set.univ) h.hasFDerivWithinAt)

end CalabiYau
