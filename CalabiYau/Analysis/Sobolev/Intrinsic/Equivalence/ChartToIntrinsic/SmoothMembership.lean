-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Intrinsic/Equivalence/ChartToIntrinsic/SmoothMembership.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Intrinsic.Equivalence.Basic
public import CalabiYau.Analysis.Sobolev.Intrinsic.Lp.Basic
public import CalabiYau.Analysis.Sobolev.Approximation.Density.FirstOrder
public import CalabiYau.Analysis.Sobolev.Chart.RiemannianMeasureComparison
public import CalabiYau.Analysis.Sobolev.Manifold.Measure.UniformChartComparison
public import CalabiYau.Analysis.Sobolev.Manifold.Embedding.Subcritical
public import CalabiYau.Analysis.Sobolev.Manifold.Morrey.Basic
public import CalabiYau.Geometry.Riemannian.DivergenceTheorem.Global.IntegrationByParts
public import CalabiYau.Geometry.Riemannian.Operator.Laplacian.Basic
public import CalabiYau.Geometry.Riemannian.Volume.Family.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

@[expose] public section

open CalabiYau.Riemannian CalabiYau

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace Sobolev
namespace Equivalence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open Sobolev.Chart
open Sobolev.Intrinsic
open Sobolev.IntrinsicLp

private lemma continuous_memLp_of_compactSpace
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (p : ℝ≥0∞)
    {f : M → ℝ} (hf : Continuous f) :
    MemLp f p (riemannianVolumeMeasure I M g) := by
  have : IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hmeas : AEStronglyMeasurable f (riemannianVolumeMeasure I M g) :=
    hf.aestronglyMeasurable
  obtain ⟨C, hC⟩ := Intrinsic.exists_bound_continuous_compactSpace hf
  exact MemLp.of_bound hmeas C (Filter.Eventually.of_forall (fun x => hC x))

lemma continuous_g_norm_gradFun
    [I.Boundaryless]
    (g : CalabiYau.SmoothRiemannianMetric I M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    Continuous (fun x : M => Real.sqrt
        (g.inner x
          (CalabiYau.Riemannian.gradFun
            (I := I) g u x)
          (CalabiYau.Riemannian.gradFun
            (I := I) g u x))) := by
  have hcont :=
    TangentBundle.continuous_g_inner_of_smooth_sections
      (I := I) (M := M) g
      (CalabiYau.Riemannian.gradG (I := I) g ⟨_, hu⟩)
      (CalabiYau.Riemannian.gradG (I := I) g ⟨_, hu⟩)
  have hcoe : (fun x : M => g.inner x
        ((CalabiYau.Riemannian.gradG (I := I) g ⟨_, hu⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((CalabiYau.Riemannian.gradG (I := I) g ⟨_, hu⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)) =
      (fun x : M => g.inner x
        (CalabiYau.Riemannian.gradFun (I := I) g u x)
        (CalabiYau.Riemannian.gradFun (I := I) g u x)) := by
    funext x
    rw [CalabiYau.Riemannian.grad_g_apply (I := I) g ⟨_, hu⟩ x]
    change g.inner x
        (CalabiYau.Riemannian.gradFun (I := I) g u x)
        (CalabiYau.Riemannian.gradFun (I := I) g u x) =
      g.inner x
        (CalabiYau.Riemannian.gradFun (I := I) g u x)
        (CalabiYau.Riemannian.gradFun (I := I) g u x)
    rfl
  rw [hcoe] at hcont
  exact Real.continuous_sqrt.comp hcont

end Equivalence
end Sobolev
