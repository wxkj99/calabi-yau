module

public import CalabiYau.MongeAmpere.Estimates.C2.ChernLuFormula.NormalFrameJets
import CalabiYau.Geometry.Kahler.Curvature.Chart
import CalabiYau.Geometry.Kahler.Curvature.ReferenceBound

/-!
# Uniform lower bound for reference bisectional curvature

Székelyhidi's proof of the Chern–Lu estimate uses the compactness of the reference manifold only
to choose one lower bound for its holomorphic bisectional curvature.  The curvature is evaluated
on the unit vectors selected by a simultaneous normal frame for the reference and varying metrics.
The number is independent of the varying metric and of the point.  Formulating uniformity also in
the choice of frame is important: an arbitrary diagonalizing unitary may depend on the varying
metric, while compactness bounds the continuous curvature function on all unit directions.

The convention here is the one in `NormalFrameJets`: `chartCurvature` uses
`-∂ₚ∂̄q g_{j k̄}` at a reference normal-coordinate center.  Accordingly this lemma bounds the
signed entry from below by `-B`; this is the sign that produces `-B * tr_{ω₁} ω₀` in the final
inequality.  It does not assert a positive curvature lower bound.

Concrete checks:

* In dimension zero there are no pairs of indices, so the quantified curvature condition is empty
  and `B = 0` is admissible.
* In dimension one there is exactly one bisectional entry.  The statement is a lower bound on the
  Gaussian/holomorphic sectional curvature with the same sign convention as `chartCurvature`.
* For a flat complex torus with its flat reference metric, each such entry is zero and again `B = 0`
  works.
* A linear change of normal coordinates must pull back the metric by
  `J.transpose * G * J.map star`; it preserves the Hermitian unit-direction curvature value.
  In one dimension with `J = i`, the metric coefficient remains `1`, confirming the order of the transpose and the conjugated Jacobian.

The proof expresses bisectional curvature as a continuous function on the compact unit sphere
bundle and takes a global minimum; the frame formulation is its coordinate reading.  No normalization of
`ω₀` beyond positivity and compactness is required, and the resulting bound is allowed to depend
on `ω₀` and the fixed manifold but not on `ω₁`.
-/

@[expose] public section

open scoped Manifold ContDiff ComplexOrder MatrixOrder

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [T2Space M] [CompactSpace M]

omit [T2Space M] in
/-- Compactness supplies a uniform lower bound for the signed bisectional curvature of a fixed
reference Kähler metric, in every simultaneous normal frame.  The varying metric is quantified
only to specify which normal frame is being used; the bound itself depends only on `ω₀`. -/
theorem exists_normalFrame_bisectional_lower_bound (ω₀ : KahlerForm n M) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (ω₁ : KahlerForm n M) (x : M)
      (F : YauNormalFrame ω₀ ω₁ x) (p j : Fin n),
      -B ≤ normalFrameBisectionalCurvature ω₀ ω₁ x F p j := by
  obtain ⟨B, hB, hcomponentBound⟩ :=
    exists_uniform_reference_curvature_component_bound (ω₀ := ω₀)
  refine ⟨B, hB, fun ω₁ x F p j ↦ ?_⟩
  let J := holomorphicJacobianMatrix F.map F.center
  have hJdet : IsUnit J.det := by
    apply isUnit_iff_ne_zero.mpr
    exact F.jacobian_det_ne_zero
  have hcenter : F.map F.center ∈
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target :=
    F.maps_into_chart F.center F.center_mem
  have hGdet : IsUnit (ω₀.metricInChart x (F.map F.center)).det :=
    (ne_of_gt (ω₀.posDef_metricInChart x hcenter).det_pos).isUnit
  have horth : referenceOrthonormalFrameMatrix ω₀ x J := by
    have hnorm := F.reference_normalized
    change Matrix.transpose (holomorphicJacobianMatrix F.map F.center) *
      ω₀.metricInChart x (F.map F.center) *
        (holomorphicJacobianMatrix F.map F.center).map star = 1 at hnorm
    rw [F.center_eq_chart_center] at hnorm
    change Matrix.transpose J *
      ω₀.metricInChart x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) *
        J.map star = 1
    simpa [referenceOrthonormalFrameMatrix, J] using hnorm
  have hg' (a b : Fin n) :
      ContDiffOn ℝ ∞ (fun z ↦ ω₀.metricInChart x z a b) (F.map '' F.domain) := by
    apply (ω₀.contDiffOn_metricInChart x a b).mono
    intro z hz
    rcases hz with ⟨w, hw, rfl⟩
    exact F.maps_into_chart w hw
  have hmetric : ∀ w ∈ F.domain,
      pulledBackMetricInChart ω₀ x F.map w =
        Matrix.transpose (holomorphicJacobianMatrix (F.map) w) *
          ω₀.metricInChart x (F.map w) *
            (holomorphicJacobianMatrix (F.map) w).map star := by
    intro w hw
    rfl
  have hkahler : ∀ w ∈ F.map '' F.domain, ∀ i j k,
      chartPartialZComplex (fun v ↦ ω₀.metricInChart x v j k) w i =
        chartPartialZComplex (fun v ↦ ω₀.metricInChart x v i k) w j := by
    rintro w ⟨v, hv, rfl⟩ i j k
    exact kahler_chart_metric_symmetry (ω₀ := ω₀) x
      (F.maps_into_chart v hv) i j k
  have hpull :
      chartCurvature (fun z ↦ pulledBackMetricInChart ω₀ x F.map z)
          F.center p p j j =
        referenceCurvatureComponent ω₀ x J p p j j := by
    have h := chartCurvature_pullback F.domain F.isOpen_domain F.map
      F.smooth_map F.holomorphic_map
      (fun z ↦ pulledBackMetricInChart ω₀ x F.map z)
      (fun z ↦ ω₀.metricInChart x z) hg' hmetric hkahler
      F.center F.center_mem hJdet hGdet p p j j
    simpa [referenceCurvatureComponent, J, holomorphicJacobianMatrix,
      F.center_eq_chart_center] using h
  have hframeCurvature :
      normalFrameBisectionalCurvature ω₀ ω₁ x F p j =
        (referenceCurvatureComponent ω₀ x J p p j j).re := by
    unfold normalFrameBisectionalCurvature
    rw [hpull]
    rfl
  have hbound := hcomponentBound x J horth p p j j
  have hreal : -B ≤ (referenceCurvatureComponent ω₀ x J p p j j).re := by
    have hnorm :
        -‖referenceCurvatureComponent ω₀ x J p p j j‖ ≤
          (referenceCurvatureComponent ω₀ x J p p j j).re := by
      exact (le_trans (neg_le_neg (Complex.abs_re_le_norm _)) (neg_abs_le _))
    linarith
  rw [hframeCurvature]
  exact hreal

end KahlerForm
