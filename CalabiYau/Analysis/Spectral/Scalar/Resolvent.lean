-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Spectral/Scalar/Resolvent.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Operator.VariationalLaplacian
public import CalabiYau.Analysis.Sobolev.Manifold.Rellich.OnManifold
public import CalabiYau.Analysis.Sobolev.Intrinsic.Equivalence.NormEquivalence
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace CalabiYau
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

noncomputable def resolventL2 (g : SmoothRiemannianMetric I M) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  (H1ComplToLp (I := I) (M := M) g).comp (resolvent (I := I) (M := M) g)

@[simp] lemma resolventL2_apply (g : SmoothRiemannianMetric I M)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    resolventL2 (I := I) (M := M) g f =
      H1ComplToLp (I := I) (M := M) g (resolvent (I := I) (M := M) g f) := rfl

private lemma inner_resolventL2_eq_inner_resolvent
    (g : SmoothRiemannianMetric I M)
    (f h : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ⟪resolventL2 (I := I) (M := M) g f, h⟫_ℝ =
      ⟪resolvent (I := I) (M := M) g f,
        resolvent (I := I) (M := M) g h⟫_ℝ := by
  rw [resolventL2_apply]
  have hvar := resolvent_inner_eq_lpFunctional (I := I) (M := M) g h
    (resolvent (I := I) (M := M) g f)
  rw [← hvar]
  exact real_inner_comm _ _

theorem resolventL2_symm
    (g : SmoothRiemannianMetric I M)
    (f h : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ⟪resolventL2 (I := I) (M := M) g f, h⟫_ℝ =
      ⟪f, resolventL2 (I := I) (M := M) g h⟫_ℝ := by
  rw [inner_resolventL2_eq_inner_resolvent (I := I) (M := M) g f h]
  rw [show ⟪f, resolventL2 (I := I) (M := M) g h⟫_ℝ =
      ⟪resolventL2 (I := I) (M := M) g h, f⟫_ℝ from real_inner_comm _ _]
  rw [inner_resolventL2_eq_inner_resolvent (I := I) (M := M) g h f]
  exact real_inner_comm _ _

theorem resolventL2_isSelfAdjoint (g : SmoothRiemannianMetric I M) :
    IsSelfAdjoint (resolventL2 (I := I) (M := M) g) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f h
  exact resolventL2_symm (I := I) (M := M) g f h

end Laplacian
end Analysis
end CalabiYau

end
