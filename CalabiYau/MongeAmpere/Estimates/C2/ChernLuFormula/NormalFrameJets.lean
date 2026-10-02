module

public import CalabiYau.Geometry.Kahler.Curvature.Chart
public import CalabiYau.MongeAmpere.Estimates.C2.ChernLuFormula.NormalCoordinates
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Mixed second jets and curvature in a normal frame

This module fixes the coordinate vocabulary shared by the source-sized normal-frame calculations
in the Chern–Lu estimate.  A frame is an actual holomorphic map into the manifold chart, so all
jets below are taken from the pulled-back coefficient matrix, not from unrelated arrays.

The metric convention is the one used by `pulledBackMetricInChart`:
`J.transpose * G * J.map star`.  Thus a complex-linear scaling `J = i` in one dimension pulls the
unit metric back to `i * 1 * (-i) = 1`; using a conjugate transpose in place of the transpose
would change the index convention.  The curvature convention is
`R_{p q̄ j k̄} = -∂ₚ∂̄q g_{j k̄} + g^{a b̄}(∂ₚg_{j b̄})(∂̄qg_{a k̄})`, so in the reference normal frame
its value at the center is the negative mixed second derivative.  These choices give the positive
curvature contribution in the trace expansion and a lower bound on the signed bisectional entries.

For `n = 0`, all indexed statements are vacuous and all sums are empty.  In complex dimension one,
the two diagonal indices in the definitions below coincide, which is a useful check on the
placement of the holomorphic and antiholomorphic indices.  On a flat torus with its flat reference
metric, the reference curvature entries vanish.
-/

@[expose] public section

open scoped Manifold ContDiff ComplexOrder MatrixOrder

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

/-- The mixed holomorphic-antiholomorphic second coordinate derivative of a coefficient of the
pulled-back varying metric in a genuine Yau normal frame.  The first derivative is taken in slot
`p` and the antiholomorphic derivative in slot `q`; metric indices remain in row-column order. -/
noncomputable def normalFrameMixedSecondDerivative
    (ω₀ ω₁ : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x)
    (p q j k : Fin n) : ℂ :=
  chartPartialZComplex
    (fun z ↦ chartPartialBarComplex
      (fun w ↦ pulledBackMetricInChart ω₁ x F.map w j k) z q) F.center p

/-- The real diagonal mixed second jet used in the Laplacian and Ricci expansions.  The
coefficient matrix of a real `(1,1)`-form has real diagonal entries, and taking `re` records that
real quantity explicitly. -/
noncomputable def normalFrameSecondReal
    (ω₀ ω₁ : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x)
    (p j : Fin n) : ℝ :=
  (normalFrameMixedSecondDerivative ω₀ ω₁ x F p p j j).re

/-- The real diagonal mixed second derivative of the logarithm of the varying metric's determinant
in the normal frame.  This is the coordinate Hessian appearing after the Ricci terms cancel in the
relative-volume identity. -/
noncomputable def normalFrameLogDetSecondReal
    (ω₀ ω₁ : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x)
    (p : Fin n) : ℝ :=
  (chartPartialZComplex
    (fun z ↦ chartPartialBarComplex
      (fun w ↦ (Real.log (RCLike.re
        ((pulledBackMetricInChart ω₁ x F.map w).det)) : ℂ)) z p)
    F.center p).re

/-- The real signed bisectional curvature entries of the pulled-back reference metric.  In a
normal frame the quadratic first-derivative correction in `chartCurvature` vanishes, but keeping
the curvature definition here makes the sign convention explicit and reusable. -/
noncomputable def normalFrameBisectionalCurvature
    (ω₀ ω₁ : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x)
    (p j : Fin n) : ℝ :=
  RCLike.re (chartCurvature (fun z ↦ pulledBackMetricInChart ω₀ x F.map z)
    F.center p p j j)

end KahlerForm
