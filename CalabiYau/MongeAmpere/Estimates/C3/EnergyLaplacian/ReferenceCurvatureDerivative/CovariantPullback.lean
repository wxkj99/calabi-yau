module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceCurvatureDerivative.FirstJet
public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceCurvatureDerivative.ConnectionJet
public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceCurvatureDerivative.Covariance
public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceCurvatureDerivative.FrameContraction
public import CalabiYau.Geometry.Kahler.Curvature.ReferenceBound.ChartOverlap

/-!
# The five-slot covariant curvature pullback

The five-slot tensor transformation follows from the first jet, the lowered
connection law, finite-array cancellation, and column-frame transport.
Székelyhidi, §3.3, proof of Lemma 3.9, printed pp. 44–45 (PDF physical
pages 62–63).
-/

public section

open scoped Manifold ContDiff ComplexOrder MatrixOrder

namespace KahlerForm

/-- Subtracting the two holomorphic connection terms from the curvature jet
produces the actual homogeneous five-slot tensor law. -/
theorem c3_curvature_covariant_pullback {n : ℕ}
    (U : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U)
    (f : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (hf : ContDiffOn ℝ ∞ f U) (hhol : DifferentiableOn ℂ f U)
    (g g' : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (hg' : ∀ j k, ContDiffOn ℝ ∞ (fun w => g' w j k) (f '' U))
    (hmetric : ∀ w ∈ U,
      g w = Matrix.transpose (EuclideanSpace.clmMatrix (fderiv ℂ f w)) *
        g' (f w) * (EuclideanSpace.clmMatrix (fderiv ℂ f w)).map star)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U)
    (hjac : IsUnit (EuclideanSpace.clmMatrix (fderiv ℂ f z)).det)
    (hgdet : IsUnit (g' (f z)).det) :
    c3CovariantFourTensorZJet (christoffelInChart g z) (chartCurvature g z)
        (fun s p q j k => chartPartialZComplex (fun w => chartCurvature g w p q j k) z s) =
      c3FiveSlotFrameContraction (EuclideanSpace.clmMatrix (fderiv ℂ f z))
        (c3CovariantFourTensorZJet (christoffelInChart g' (f z)) (chartCurvature g' (f z))
          (fun s p q j k => chartPartialZComplex
            (fun w => chartCurvature g' w p q j k) (f z) s)) := by
  apply c3_covariant_curvature_pullback_algebra
    (EuclideanSpace.clmMatrix (fderiv ℂ f z))
    (fun s a p => chartPartialZComplex
      (fun w => (EuclideanSpace.clmMatrix (fderiv ℂ f w)) a p) z s)
    (chartCurvature g' (f z)) (chartCurvature g z)
    (fun s p q j k => chartPartialZComplex
      (fun w => chartCurvature g' w p q j k) (f z) s)
    (fun s p q j k => chartPartialZComplex (fun w => chartCurvature g w p q j k) z s)
    (christoffelInChart g' (f z)) (christoffelInChart g z)
  · funext p q j k
    exact chartCurvature_pullback U hU f hf hhol g g' hg' hmetric
      z hz hjac hgdet p q j k
  · exact c3_curvature_pullback_first_jet U hU f hf hhol g g' hg' hmetric
      z hz hjac hgdet
  · exact c3_connection_pullback_lowered U hU f hf hhol g g' hg' hmetric z hz hjac hgdet

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

/-- Actual centered-to-fixed chart transport of the five-slot contraction.
The chart selection itself is not assumed to vary smoothly. -/
theorem c3_reference_curvature_derivative_frame_transition
    (ω₀ : KahlerForm n M) (x y : M)
    (U : Set (EuclideanSpace ℂ (Fin n))) (hU : ω₀.IsReferenceChartOverlap x y U)
    (P : Matrix (Fin n) (Fin n) ℂ) :
    let zy := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y y
    let zx := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y
    let gy := fun z => ω₀.metricInChart y z
    let gx := fun z => ω₀.metricInChart x z
    c3FiveSlotFrameContraction P
        (c3CovariantFourTensorZJet (christoffelInChart gy zy) (chartCurvature gy zy)
          (fun s p q j k => chartPartialZComplex
            (fun w => chartCurvature gy w p q j k) zy s)) =
      c3FiveSlotFrameContraction (referenceTransitionMatrix x y * P)
        (c3CovariantFourTensorZJet (christoffelInChart gx zx) (chartCurvature gx zx)
          (fun s p q j k => chartPartialZComplex
            (fun w => chartCurvature gx w p q j k) zx s)) := by
  dsimp only
  rcases hU with ⟨hOpen, hz, himage, hf, hhol, hjac, hmetric⟩
  let f := referenceChartTransition (n := n) x y
  let z := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y y
  have hcenter : f z = extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y := by
    change (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x)
      ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).symm
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y y)) = _
    rw [(extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).left_inv
      (mem_extChartAt_source y)]
  have hT := c3_curvature_covariant_pullback U hOpen f hf hhol
    (ω₀.metricInChart y) (ω₀.metricInChart x)
    (fun a b => (ω₀.contDiffOn_metricInChart x a b).mono himage)
    hmetric
    z hz hjac
    ((Matrix.isUnit_iff_isUnit_det _).1
      (ω₀.posDef_metricInChart x (himage ⟨z, hz, rfl⟩)).isUnit)
  have hframe := c3_five_slot_frame_pullback
    (EuclideanSpace.clmMatrix (fderiv ℂ f z)) P _ _ hT
  rw [hcenter] at hframe
  exact hframe

end KahlerForm
