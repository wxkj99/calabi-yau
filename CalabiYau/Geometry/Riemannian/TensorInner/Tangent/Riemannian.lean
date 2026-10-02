-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Geometry/Metric/TensorInner/Tangent/Riemannian.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Manifold.Tensor.RSTensor.Defs
public import CalabiYau.Geometry.Riemannian.Metric.Coordinates.ChartGram
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import CalabiYau.Geometry.Riemannian.Metric.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Topology.VectorBundle.Riemannian

@[expose] public section


noncomputable section

open Bundle Set IsManifold ContinuousLinearMap
open scoped Manifold Topology Bundle ContDiff

namespace CalabiYau
namespace Tensor
namespace TangentRiemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [Module.Finite ℝ E] in
private lemma continuous_g_inner
    (g : CalabiYau.SmoothRiemannianMetric I M)
    {v w : ∀ x : M, TangentSpace I x}
    (hv : Continuous (fun x : M => TotalSpace.mk' E
      (E := (TangentSpace I : M → Type _)) x (v x)))
    (hw : Continuous (fun x : M => TotalSpace.mk' E
      (E := (TangentSpace I : M → Type _)) x (w x))) :
    Continuous (fun b : M => g.inner b (v b) (w b)) := by
  let cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
    g.toContinuousRiemannianMetric
  let rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨cg.toRiemannianMetric⟩
  have h := Continuous.inner_bundle (F := E) (B := M) (E := (TangentSpace I : M → Type _))
    (b := fun x => x) (v := v) (w := w) hv hw
  refine h.congr ?_
  intro b
  rfl

end TangentRiemannian
end Tensor
end CalabiYau

namespace TangentBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [Module.Finite ℝ E] in
theorem continuous_g_inner_of_smooth_sections
    (g : CalabiYau.SmoothRiemannianMetric I M)
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Continuous (fun b : M => g.inner b (X b) (Y b)) := by
  have hX : Continuous (fun x : M => TotalSpace.mk' E
      (E := (TangentSpace I : M → Type _)) x (X x)) :=
    X.contMDiff.continuous
  have hY : Continuous (fun x : M => TotalSpace.mk' E
      (E := (TangentSpace I : M → Type _)) x (Y x)) :=
    Y.contMDiff.continuous
  exact CalabiYau.Tensor.TangentRiemannian.continuous_g_inner
    (I := I) (M := M) g hX hY

end TangentBundle
