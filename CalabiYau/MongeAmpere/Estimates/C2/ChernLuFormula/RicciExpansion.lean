module

public import CalabiYau.Geometry.Kahler.Laplacian
public import CalabiYau.Geometry.Kahler.Ricci
public import CalabiYau.Geometry.Complex.Forms.OneOne
public import CalabiYau.MongeAmpere.Estimates.C2.ChernLuFormula.NormalFrameJets
import CalabiYau.MongeAmpere.Estimates.C2.ChernLuFormula.LogDetSecondJet
import CalabiYau.MongeAmpere.Estimates.C2.ChernLuFormula.RelativeDeterminantRicci

/-!
# Ricci and relative-determinant expansion in a normal frame

This theorem gives the second normal-coordinate calculation in Székelyhidi's proof.  The Ricci
form is `-i∂∂̄ log det g`, and the change-of-metric identity expresses the varying Ricci form as
the reference Ricci form minus `i∂∂̄ log relDet(ω₀, ω₁)`.  In a frame where the reference matrix is
`1` and the varying matrix is diagonal, tracing the identity and expanding the logarithm of its
determinant gives the second-jet sum minus the quadratic first-jet sum.

The formula uses the same diagonal real second jets as
`normalFrame_laplacian_log_relative_trace`.  This common jet is essential: swapping the two
indices in its numerator is justified by a separately stated Kähler symmetry theorem, not by
silently changing the index order or taking a transpose.  The gradient term has denominator
`λⱼ λₖ`; the first index `p` is the holomorphic differentiation direction and the remaining
indices are those of the differentiated metric coefficient.

The left side is written in the form
`-(tr_{ω₀} Ric(ω₀) - Δ_{ω₀} log relDet(ω₀,ω₁))`.  By the Ricci/Laplacian identity, this is the negative trace of `Ric(ω₁)`.  The sign follows from `Ric = -i∂∂̄ log det g` and from the convention for `mddbar`; no positivity sign has been dropped.

Concrete-case audit:

* In dimension zero both sums and the trace vanish.  `relDet` is the determinant ratio of empty
  matrices and equals one, so its logarithm has zero Laplacian.
* In dimension one the Hessian contribution is `H₁₁ / λ`, and the quadratic term is the squared
  first derivative divided by `λ²`, the usual one-variable logarithmic determinant formula.
* In a flat one-dimensional torus with a constant varying multiple of the flat metric, all jets
  vanish and the equality reduces to zero equals zero.
* Under a complex-linear coordinate change the coefficient matrix transforms as
  `J.transpose * G * J.map star`.  Its determinant acquires the positive factor `|det J|²`; the
  logarithm of that factor is pluriharmonic for a nonvanishing holomorphic Jacobian.  The
  `J = i`, `n = 1` test preserves the metric coefficient and confirms the sign/order convention.

This is an equality, before any Cauchy–Schwarz estimate.  It does not assert a bound on the
varying metric, nor does it assume the Monge–Ampère equation.  The reference metric and varying
metric are arbitrary positive Kähler forms, which is exactly the scope of the local source
calculation.
-/

@[expose] public section

open scoped Manifold ContDiff ComplexOrder MatrixOrder
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

/-- The exact normal-frame expansion of the reference Ricci trace minus the Laplacian of the log
relative volume.  It uses the same real second jets as the logarithmic-trace expansion. -/
theorem normalFrame_ricci_relative_determinant_expansion
    (ω₀ ω₁ : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x) :
    -(relTrace (ω₀ x) (ω₀.ricciForm x) -
        ω₀.laplacian (fun y ↦ Real.log (relDet (ω₀ y) (ω₁ y))) x) =
      (∑ p, ∑ j, normalFrameSecondReal ω₀ ω₁ x F p j / F.eigenvalue j) -
        ∑ p, ∑ j, ∑ k,
          ‖normalFrameFirstDerivative F p j k‖ ^ 2 /
            (F.eigenvalue j * F.eigenvalue k) := by
  rw [neg_relTrace_ricciForm_add_laplacian_log_relDet_eq_sum ω₀ ω₁ x F,
    normalFrame_logdet_second_jet_expansion ω₀ ω₁ x F]

end KahlerForm
