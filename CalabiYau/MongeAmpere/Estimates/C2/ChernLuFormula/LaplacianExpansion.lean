module

public import CalabiYau.Geometry.Kahler.Laplacian
public import CalabiYau.Geometry.Complex.Forms.OneOne
public import CalabiYau.MongeAmpere.Estimates.C2.ChernLuFormula.NormalFrameJets
import CalabiYau.MongeAmpere.Estimates.C2.ChernLuFormula.RelativeTrace
import CalabiYau.MongeAmpere.Estimates.C2.ChernLuFormula.TraceGradient
import CalabiYau.MongeAmpere.Estimates.C2.ChernLuFormula.TraceLaplacian
import CalabiYau.MongeAmpere.Estimates.C2.ChernLuFormula.TraceLogChainRule

/-!
# Laplacian of the logarithmic relative trace

This is the local Chern–Lu calculation in a holomorphic normal frame.  At the center, the
reference coefficient matrix is the identity, its first holomorphic derivatives vanish, and the
varying coefficient matrix is diagonal with entries `λⱼ > 0`.  The function being differentiated
is the logarithm of the trace of the varying metric against the fixed reference metric.

The displayed identity separates its three geometric sources:

1. The mixed second derivatives of the diagonal varying coefficients contribute
   `∑ₚⱼ Hₚⱼ / λₚ`.
2. The curvature of the reference metric contributes
   `∑ₚⱼ λⱼ Rₚⱼ / λₚ`, where `Rₚⱼ` has the sign convention from `chartCurvature`.
3. Differentiating the logarithm contributes the negative square of the first-derivative trace,
   divided by the trace twice.

The first derivative is retained as the array
`normalFrameFirstDerivative F p j k`, rather than replacing it with an arbitrary tensor.  Its
Kähler symmetry is a separate source-sized child (`FirstDerivativeSymmetry`); that exact symmetry
is what permits Cauchy–Schwarz to absorb the negative square in the parent finite-dimensional
estimate.  Likewise the Hessian entry `normalFrameSecondReal F p j` is shared with the Ricci
expansion and is not an independently chosen array.

The normal coordinate convention fixes the curvature sign.  At the center the reference metric is
`1` and its first derivative is zero, so the quadratic term in `chartCurvature` vanishes and the
curvature value is `-∂ₚ∂̄q g_{j k̄}`.  The curvature appears with a plus sign in this trace Laplacian
formula.  In particular a lower bound `Rₚⱼ ≥ -B` produces the required lower bound on its weighted
sum.

Concrete-case audit:

* In dimension zero, the sums over `p` and `j` are empty.  The theorem's equality is compatible
  with the zero-dimensional complex Laplacian convention, and no nonempty-index hypothesis is
  hidden in the formula.
* In dimension one, the denominator is the positive eigenvalue `λ`, the curvature term is the one
  bisectional component, and the gradient-square term is the square of the single diagonal
  derivative divided by `λ²`.  This checks the two occurrences of the trace denominator.
* On a flat one-dimensional torus with constant varying metric, the first and second jets and the
  reference curvature all vanish; both sides evaluate to zero.
* With a linear coordinate change `J`, the metric convention is
  `J.transpose * G * J.map star`; for `n = 1`, `J = i` preserves the normalized reference
  coefficient.  Thus the indices `p,p,j,j` in curvature and in the mixed second jet are consistent
  with the pullback convention rather than its transpose or conjugate-transpose variant.

The theorem is deliberately an equality, not a lower estimate.  All cancellations and estimates
are postponed to the parent after the Ricci identity and the two finite-dimensional symmetries have
been supplied.  This makes the source computation independently auditable and keeps the parent
proof free of hidden analytic assumptions.
-/

@[expose] public section

open scoped Manifold ContDiff ComplexOrder MatrixOrder
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

/-- The exact normal-frame expansion of the varying-metric Laplacian of the logarithmic relative
trace.  The scalar `second` is the real diagonal mixed second jet and `curvature` is the signed
reference bisectional curvature from `NormalFrameJets`. -/
theorem normalFrame_laplacian_log_relative_trace
    (ω₀ ω₁ : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x) :
    ω₁.laplacian (fun y ↦ Real.log (relTrace (ω₀ y) (ω₁ y))) x =
      ((∑ p, ∑ j, normalFrameSecondReal ω₀ ω₁ x F p j / F.eigenvalue p) +
          ∑ p, ∑ j, (F.eigenvalue p)⁻¹ * F.eigenvalue j *
            normalFrameBisectionalCurvature ω₀ ω₁ x F p j) /
          (∑ j, F.eigenvalue j) -
        (∑ p, ‖∑ j, normalFrameFirstDerivative F p j j‖ ^ 2 /
            (F.eigenvalue p * ∑ j, F.eigenvalue j)) /
          (∑ j, F.eigenvalue j) := by
  rw [normalFrame_log_relative_trace_chain_rule ω₀ ω₁ x,
    normalFrame_laplacian_relative_trace ω₀ ω₁ x F,
    normalFrame_normalized_relative_trace_gradient ω₀ ω₁ x F,
    (normalFrame_relative_trace_eq_sums ω₀ ω₁ x F).1]

end KahlerForm
