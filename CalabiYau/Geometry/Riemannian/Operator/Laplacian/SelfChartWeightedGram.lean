module

public import CalabiYau.Geometry.Riemannian.Operator.Laplacian.Basic
public import CalabiYau.Geometry.Riemannian.Operator.Gradient.Basic
public import CalabiYau.Geometry.Riemannian.Volume.Chart.Density
import CalabiYau.Geometry.Riemannian.Operator.Laplacian.VossWeylFormula

/-!
# Self-chart weighted inverse-Gram formula for the real Laplacian

The Voss–Weyl formula at the center of the point's own chart has no separation
hypothesis on the manifold. The local divergence formula and the chart gradient
expansion suffice; unlike the extracted arbitrary-chart statement, it does not
require `[T2Space M]`.

The chart-model basis is not assumed orthonormal. `chartDensityOnE` is the square
root of the real Gram determinant for this basis, and `chartInvGramMatrix i j`
acts on the `j`-th first derivative to give the `i`-th gradient coefficient.

The formula follows by applying the local divergence identity to the chart
expression for the gradient.
-/

@[expose] public section

open scoped Manifold ContDiff
open CalabiYau.DivergenceTheorem

namespace CalabiYau.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The Laplace–Beltrami operator is weighted inverse-Gram divergence in the
point's own real chart, without a Hausdorff hypothesis. -/
theorem deltaG_eq_self_chart_weighted_inverse_gram [I.Boundaryless]
    (g : CalabiYau.SmoothRiemannianMetric I M) (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M) :
    ΔG (I := I) g ⟨f, hf⟩ x =
      (∑ i : Fin (Module.finrank ℝ E),
        CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i
          (fun z : E =>
            CalabiYau.RiemannianVolume.chartDensityOnE (I := I) g x z *
              ∑ j : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g x ((extChartAt I x).symm z) i j *
                  CalabiYau.Tensor.Coordinates.partialDeriv (E := E) j
                    (f ∘ (extChartAt I x).symm) z)
          (extChartAt I x x)) /
        CalabiYau.RiemannianVolume.chartDensity (I := I) g x x := by
  have hlocal := localDivergence_grad_g_eq_chartVossWeylLaplacian
    (I := I) g x hf (show x ∈ (chartAt H x).source by simp)
  change localDivergence (I := I) g x (gradG (I := I) g ⟨f, hf⟩) x = _
  rw [hlocal]
  simp only [chartVossWeylLaplacian_def]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  funext z
  unfold chartVossWeylIntegrand gradChartCoeffOnE chartInvGramOnE
    CalabiYau.Tensor.Coordinates.scalarOnE
  exact mul_comm _ _

end CalabiYau.Riemannian
