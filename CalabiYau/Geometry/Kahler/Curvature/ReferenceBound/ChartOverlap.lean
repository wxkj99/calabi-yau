module

public import CalabiYau.Geometry.Kahler.Curvature.ReferenceBound.ChartDomain
public import CalabiYau.Geometry.Kahler.Curvature.ReferenceBound.JacobianUnit
public import CalabiYau.Geometry.Kahler.Curvature.ReferenceBound.MetricPullback

/-!
# The holomorphic overlap of two centered Kähler charts

The chart at `y` is the source of the transition and the chart at `x` is its target.  Their
coordinate transition need not be affine.  The open-overlap metric identity is recorded here,
rather than just its value at `y`: curvature differentiates that identity twice.
-/

@[expose] public section

open scoped Manifold ContDiff ComplexOrder MatrixOrder

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

/-- Local holomorphic regularity and the metric-congruence law on an open overlap, with the
orientation `g_y = Aᵀ(g_x ∘ f) Ā`.  The image condition states exactly the chart domain needed
for positive definiteness and the Kähler symmetry of `g_x`. -/
def IsReferenceChartOverlap (ω₀ : KahlerForm n M) (x y : M)
    (U : Set (EuclideanSpace ℂ (Fin n))) : Prop :=
  IsOpen U ∧
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y y) ∈ U ∧
    referenceChartTransition (n := n) x y '' U ⊆
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target ∧
    ContDiffOn ℝ ∞ (referenceChartTransition (n := n) x y) U ∧
    DifferentiableOn ℂ (referenceChartTransition (n := n) x y) U ∧
    IsUnit (referenceTransitionMatrix (n := n) x y).det ∧
    ∀ z ∈ U,
      ω₀.metricInChart y z =
        Matrix.transpose
            (EuclideanSpace.clmMatrix (fderiv ℂ (referenceChartTransition (n := n) x y) z)) *
          ω₀.metricInChart x (referenceChartTransition (n := n) x y z) *
            (EuclideanSpace.clmMatrix
              (fderiv ℂ (referenceChartTransition (n := n) x y) z)).map star

/-- The overlap of the charts centered at `x` and `y`, when `y` lies in the `x`-chart, has
all regularity and metric-change properties required by curvature covariance. -/
theorem exists_reference_chart_overlap (ω₀ : KahlerForm n M) (x y : M)
    (hy : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).source) :
    ∃ U : Set (EuclideanSpace ℂ (Fin n)), ω₀.IsReferenceChartOverlap x y U := by
  obtain ⟨U, hOpen, hCenter, hTarget, hSource, hImage, hSmooth, hHol⟩ :=
    exists_reference_chart_domain (n := n) x y hy
  refine ⟨U, hOpen, hCenter, hImage, hSmooth, hHol,
    referenceTransitionMatrix_isUnit_det (n := n) x y hy, ?_⟩
  intro z hz
  exact ω₀.referenceMetricInChart_pullback x y z (hTarget hz) (hSource z hz)

end KahlerForm
