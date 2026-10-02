module

public import CalabiYau.MongeAmpere.Estimates.C2.ChernLuFormula.NormalFrameJets
public import CalabiYau.Geometry.Kahler.Curvature.ReferenceBound
import CalabiYau.MongeAmpere.Estimates.C2.ReferenceCurvatureTransport.HolomorphicJacobianJet
import CalabiYau.MongeAmpere.Estimates.C2.ReferenceCurvatureTransport.PullbackConnectionGerm
import CalabiYau.MongeAmpere.Estimates.C2.ReferenceCurvatureTransport.PullbackConnectionBarDerivative
import CalabiYau.MongeAmpere.Estimates.C2.ReferenceCurvatureTransport.NormalConnectionJet

/-!
# Reference curvature transport in an actual normal frame

Székelyhidi §1.4, pp.11–12 (PDF 29–30): Γ, R, and normal coordinates.
The four-Jacobian contraction is the coordinate implementation of that calculation.
It is proved through a neighborhood connection identity, not the unproved general
`chartCurvature_pullback`. Only the source metric needs C∞; the pulled-back field
has the finite C2 regularity furnished by the real C3 holomorphic coordinate germ.
-/

public section

open scoped Manifold ContDiff ComplexOrder MatrixOrder

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

/-- At the normal center the reference curvature is the negative ordered mixed
reference jet, with no extra factor of two or four. -/
theorem normalFrameBisectionalCurvature_eq_neg_reference_mixedSecond
    (ω₀ ω₁ : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x)
    (p j : Fin n) :
    normalFrameBisectionalCurvature ω₀ ω₁ x F p j =
      -(chartPartialZComplex
        (fun z => chartPartialBarComplex
          (fun w => pulledBackMetricInChart ω₀ x F.map w j j) z p)
        F.center p).re := by
  simp [normalFrameBisectionalCurvature, chartCurvature, F.reference_first_derivative_zero]

end KahlerForm
