-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Operator/DirichletForm.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Regularity.H1Compl.Intrinsic
public import CalabiYau.Geometry.Riemannian.L2.Pairing.Defs
public import CalabiYau.Geometry.Riemannian.Metric.PointwiseInner.Bounds

@[expose] public section

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Function
open scoped Manifold Topology ContDiff ENNReal NNReal Matrix BigOperators

namespace CalabiYau
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open Sobolev.IntrinsicH1Lp

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

namespace H1Intrinsic

variable [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]

private lemma dirichletForm_integrand_add_left
    (g : SmoothRiemannianMetric I M)
    (u₁ u₂ v : H1Intrinsic (I := I) (M := M) g) :
    (fun x : M => g.inner x ((gradL2 (I := I) (M := M) g (u₁ + u₂) : M → E) x)
        ((gradL2 (I := I) (M := M) g v : M → E) x))
      =ᵐ[riemannianVolumeMeasure I M g]
      (fun x : M => g.inner x ((gradL2 (I := I) (M := M) g u₁ : M → E) x)
        ((gradL2 (I := I) (M := M) g v : M → E) x) +
        g.inner x ((gradL2 (I := I) (M := M) g u₂ : M → E) x)
          ((gradL2 (I := I) (M := M) g v : M → E) x)) := by
  have hgrad_add : (gradL2 (I := I) (M := M) g (u₁ + u₂) :
        Lp E 2 (riemannianVolumeMeasure I M g)) =
      gradL2 (I := I) (M := M) g u₁ + gradL2 (I := I) (M := M) g u₂ :=
    map_add (gradL2 (I := I) (M := M) g) u₁ u₂
  have hfn_add : (fun x : M => ((gradL2 (I := I) (M := M) g (u₁ + u₂) :
        Lp E 2 (riemannianVolumeMeasure I M g)) : M → E) x)
      =ᵐ[riemannianVolumeMeasure I M g]
      (fun x : M => ((gradL2 (I := I) (M := M) g u₁ :
        Lp E 2 (riemannianVolumeMeasure I M g)) : M → E) x +
        ((gradL2 (I := I) (M := M) g u₂ :
          Lp E 2 (riemannianVolumeMeasure I M g)) : M → E) x) := by
    rw [hgrad_add]
    filter_upwards [Lp.coeFn_add (gradL2 (I := I) (M := M) g u₁)
      (gradL2 (I := I) (M := M) g u₂)] with x hx
    exact hx
  filter_upwards [hfn_add] with x hx
  show g.inner x ((gradL2 (I := I) (M := M) g (u₁ + u₂) : M → E) x)
        ((gradL2 (I := I) (M := M) g v : M → E) x) = _
  calc g.inner x ((gradL2 g (u₁ + u₂) : M → E) x) ((gradL2 g v : M → E) x)
      = g.inner x ((gradL2 g u₁ : M → E) x + (gradL2 g u₂ : M → E) x)
          ((gradL2 g v : M → E) x) := by rw [hx]
    _ = (g.inner x ((gradL2 g u₁ : M → E) x) + g.inner x ((gradL2 g u₂ : M → E) x))
          ((gradL2 g v : M → E) x) := by
          congr 1
          exact map_add (g.inner x) _ _
    _ = g.inner x ((gradL2 g u₁ : M → E) x) ((gradL2 g v : M → E) x) +
          g.inner x ((gradL2 g u₂ : M → E) x) ((gradL2 g v : M → E) x) := by
          rfl

private lemma dirichletForm_integrand_smul_left
    (g : SmoothRiemannianMetric I M) (c : ℝ)
    (u v : H1Intrinsic (I := I) (M := M) g) :
    (fun x : M => g.inner x ((gradL2 (I := I) (M := M) g (c • u) : M → E) x)
        ((gradL2 (I := I) (M := M) g v : M → E) x))
      =ᵐ[riemannianVolumeMeasure I M g]
      (fun x : M => c * g.inner x ((gradL2 (I := I) (M := M) g u : M → E) x)
        ((gradL2 (I := I) (M := M) g v : M → E) x)) := by
  have hgrad_smul : (gradL2 (I := I) (M := M) g (c • u) :
        Lp E 2 (riemannianVolumeMeasure I M g)) =
      c • gradL2 (I := I) (M := M) g u :=
    map_smul (gradL2 (I := I) (M := M) g) c u
  have hfn_smul : (fun x : M => ((gradL2 (I := I) (M := M) g (c • u) :
        Lp E 2 (riemannianVolumeMeasure I M g)) : M → E) x)
      =ᵐ[riemannianVolumeMeasure I M g]
      (fun x : M => c • ((gradL2 (I := I) (M := M) g u :
        Lp E 2 (riemannianVolumeMeasure I M g)) : M → E) x) := by
    rw [hgrad_smul]
    filter_upwards [Lp.coeFn_smul c (gradL2 (I := I) (M := M) g u)] with x hx
    exact hx
  filter_upwards [hfn_smul] with x hx
  show g.inner x ((gradL2 (I := I) (M := M) g (c • u) : M → E) x)
        ((gradL2 (I := I) (M := M) g v : M → E) x) = _
  calc g.inner x ((gradL2 g (c • u) : M → E) x) ((gradL2 g v : M → E) x)
      = g.inner x (c • (gradL2 g u : M → E) x) ((gradL2 g v : M → E) x) := by rw [hx]
    _ = (c • g.inner x ((gradL2 g u : M → E) x)) ((gradL2 g v : M → E) x) := by
          congr 1
          exact map_smul (g.inner x) c _
    _ = c * g.inner x ((gradL2 g u : M → E) x) ((gradL2 g v : M → E) x) := by
          rfl

end H1Intrinsic

end Laplacian
end Analysis
end CalabiYau

end
