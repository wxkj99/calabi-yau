module

public import CalabiYau.Geometry.Kahler.Sobolev.ZeroGradient.ChartWeakDerivative
import CalabiYau.Geometry.Kahler.Sobolev.ZeroGradient.ConnectedConstancy.ChartBallConstancy
import CalabiYau.Geometry.Kahler.Sobolev.ZeroGradient.ConnectedConstancy.ConnectedBallGluing

/-!
# From chartwise zero weak derivatives to a global constant

Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, §7.1,
and Aubin, *Some Nonlinear Problems in Riemannian Geometry*, Ch. 4, Thm. 4.7.
The local analytic result only gives constancy on balls inside a chart target. A chart
image need not be connected; positive volume on nonempty open overlaps and connectedness
of the manifold show that all ball constants agree.
-/

@[expose] public section

open scoped Manifold ContDiff
open MeasureTheory Filter Topology

namespace KahlerForm

/-- A function with zero distributional coordinate derivatives in every chart is a.e. constant
on a compact connected Kähler manifold. -/
theorem ae_eq_const_of_zero_weak_derivative_in_charts
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [SigmaCompactSpace M]
    [CompactSpace M] [ConnectedSpace M]
    (ω₀ : KahlerForm n M) (u : M → ℝ)
    (hu : MemLp u (ENNReal.ofReal 2) ω₀.volume)
    (hweak : HasZeroWeakDerivativeInCharts (n := n) (M := M) u) :
    ∃ c : ℝ, u =ᵐ[ω₀.volume] fun _ => c := by
  apply ae_eq_const_of_locally_ae_const ω₀.volume u
  exact fun a => chartBall_ae_eq_const_of_zero_weak_derivative_in_charts ω₀ u hu hweak a

end KahlerForm
