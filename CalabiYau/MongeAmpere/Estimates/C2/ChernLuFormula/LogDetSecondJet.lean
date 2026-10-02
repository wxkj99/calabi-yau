module

public import CalabiYau.MongeAmpere.Estimates.C2.ChernLuFormula.NormalFrameJets
import CalabiYau.MongeAmpere.Estimates.C2.LogDetHessianJet
import CalabiYau.MongeAmpere.Estimates.C2.ReferenceCurvatureTransport.HolomorphicJacobianJet

/-!
# Second jet of the varying metric's logarithmic determinant

This is the finite-dimensional matrix differentiation cluster in the Ricci/log-volume expansion.
For a positive Hermitian matrix `G`, the first derivative of `log det G` is
`tr(G⁻¹ ∂G)`.  Differentiating again in the conjugate direction gives the trace of the mixed second
jet minus the quadratic contraction of the two first jets.  At the simultaneous normal-frame
center, `G` is diagonal with entries `λⱼ`, so these contractions become the eigenvalue-weighted sums
in the statement.

The second-jet contribution uses `normalFrameSecondReal ω₀ ω₁ x F p j / λⱼ`.  The matrix inverse
contributes `‖Tₚⱼₖ‖²/(λⱼλₖ)` with the full coefficient-index contraction.  No curvature or
Monge–Ampère equation is involved in this local determinant calculation; curvature enters through
the separate geometric bridge from the intrinsic Ricci expression to this coordinate Hessian.

The coefficient matrix uses holomorphic row indices and antiholomorphic column indices.  The
pullback is `J.transpose * G * J.map star`; in dimension one `J=i` leaves the metric coefficient
unchanged.  For `n=0` the determinant is the determinant of the empty identity matrix, its logarithm
is constant, and all indexed sums are empty.  For `n=1` the formula reduces to the usual second
logarithmic derivative `H/λ-|T|²/λ²`.  Constant metrics on a flat torus give zero on both sides.
-/

@[expose] public section

open scoped Manifold ContDiff ComplexOrder MatrixOrder

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

private theorem chartPartialZComplex_sum {n : ℕ} {ι : Type*} [Fintype ι]
    (F : ι → EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (p : Fin n)
    (hF : ∀ i, DifferentiableAt ℝ (F i) z) :
    chartPartialZComplex (fun w ↦ ∑ i, F i w) z p =
      ∑ i, chartPartialZComplex (F i) z p := by
  classical
  let e : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single p 1
  have hsum (v : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ ∑ i, F i w) z v =
        ∑ i, fderiv ℝ (F i) z v := by
    rw [fderiv_fun_sum (u := Finset.univ) (by intro i hi; exact hF i)]
    simp only [sum_apply]
  unfold chartPartialZComplex
  rw [hsum e, hsum (Complex.I • e)]
  calc
    _ = ((∑ i, (fderiv ℝ (F i) z) e) -
        Complex.I * (∑ i, (fderiv ℝ (F i) z) (Complex.I • e))) / 2 := rfl
    _ = (∑ i, ((fderiv ℝ (F i) z) e -
        Complex.I * (fderiv ℝ (F i) z) (Complex.I • e))) / 2 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    _ = ∑ i, ((fderiv ℝ (F i) z) e -
        Complex.I * (fderiv ℝ (F i) z) (Complex.I • e)) / 2 := by rw [Finset.sum_div]

private theorem normalFrame_logdet_second_jet_at_index
    (ω₀ ω₁ : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x)
    (p : Fin n) :
    normalFrameLogDetSecondReal ω₀ ω₁ x F p =
      (∑ j, normalFrameSecondReal ω₀ ω₁ x F p j / F.eigenvalue j) -
        ∑ j, ∑ k,
          ‖normalFrameFirstDerivative F p j k‖ ^ 2 /
            (F.eigenvalue j * F.eigenvalue k) := by
  have hF3 : ContDiffOn ℝ 3 F.map F.domain :=
    F.smooth_map.of_le (WithTop.coe_le_coe.mpr
      (show (3 : ℕ∞) ≤ ⊤ from le_top))
  have hJ := holomorphicJacobianJetAt_of_contDiffOn F.domain F.isOpen_domain F.map
    hF3 F.holomorphic_map F.center F.center_mem F.jacobian_det_ne_zero.isUnit
  have hmap3 : ContDiffAt ℝ 3 F.map F.center := by
    exact (F.smooth_map.contDiffAt
      (F.isOpen_domain.mem_nhds F.center_mem)).of_le
      (WithTop.coe_le_coe.mpr (show (3 : ℕ∞) ≤ ⊤ from le_top))
  have hmap2 : ContDiffAt ℝ 2 F.map F.center := hmap3.of_le (by norm_num)
  have hMetric (a b : Fin n) : ContDiffAt ℝ 2
      (fun w ↦ ω₁.metricInChart x (F.map w) a b) F.center := by
    have hbase := (ω₁.contDiffOn_metricInChart x a b).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds
        (F.maps_into_chart F.center F.center_mem))
    exact hbase.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)) |>.comp
      F.center hmap2
  have hJentry (a j : Fin n) : ContDiffAt ℝ 2
      (fun w ↦ holomorphicJacobianMatrix F.map w a j) F.center :=
    hJ.jacobian_contDiff a j
  have hJstar (a j : Fin n) : ContDiffAt ℝ 2
      (fun w ↦ star (holomorphicJacobianMatrix F.map w a j)) F.center := by
    have h : ContDiffAt ℝ 2
        (fun w ↦ Complex.conjCAE (holomorphicJacobianMatrix F.map w a j)) F.center := by
      exact (Complex.conjCLE.contDiff.contDiffAt).comp F.center (hJentry a j)
    convert h using 1
    ext w
    simp [Complex.conjCAE_apply]
  have hG : ∀ j k, ContDiffAt ℝ 2
      (fun w ↦ pulledBackMetricInChart ω₁ x F.map w j k) F.center := by
    intro j k
    change ContDiffAt ℝ 2 (fun w ↦
      (Matrix.transpose (holomorphicJacobianMatrix F.map w) *
        ω₁.metricInChart x (F.map w) *
          (holomorphicJacobianMatrix F.map w).map star) j k) F.center
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    fun_prop (disch := assumption)
  have hHerm : ∀ᶠ w in nhds F.center,
      (pulledBackMetricInChart ω₁ x F.map w).IsHermitian := by
    filter_upwards [F.isOpen_domain.mem_nhds F.center_mem] with w hw
    have hmetric := (ω₁.posDef_metricInChart x (F.maps_into_chart w hw)).isHermitian
    let J := holomorphicJacobianMatrix F.map w
    let H := ω₁.metricInChart x (F.map w)
    have hJ1 : (J.map star).conjTranspose = J.transpose := by
      ext i j
      simp [J, Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.transpose_apply]
    have hJ2 : J.transpose.conjTranspose = J.map star := by
      ext i j
      simp [J, Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.transpose_apply]
    change (J.transpose * H * J.map star).conjTranspose = _
    calc
      (J.transpose * H * J.map star).conjTranspose =
          (J.map star).conjTranspose * H.conjTranspose * J.transpose.conjTranspose := by
        simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = J.transpose * H * J.map star := by rw [hJ1, hmetric.eq, hJ2]
      _ = ω₁.pulledBackMetricInChart x F.map w := rfl
  have h := log_det_mixed_second_real_of_diagonal
    (fun w ↦ pulledBackMetricInChart ω₁ x F.map w) F.center F.eigenvalue hG hHerm
    F.varying_diagonal F.eigenvalue_pos p
  simpa [normalFrameLogDetSecondReal, normalFrameSecondReal,
    normalFrameMixedSecondDerivative, normalFrameFirstDerivative] using h

/-- Sum of the diagonal mixed Hessians of `log det` of the pulled-back varying metric, expanded in
the simultaneous normal frame. -/
theorem normalFrame_logdet_second_jet_expansion
    (ω₀ ω₁ : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x) :
    (∑ p, normalFrameLogDetSecondReal ω₀ ω₁ x F p) =
      (∑ p, ∑ j, normalFrameSecondReal ω₀ ω₁ x F p j / F.eigenvalue j) -
        ∑ p, ∑ j, ∑ k,
          ‖normalFrameFirstDerivative F p j k‖ ^ 2 /
            (F.eigenvalue j * F.eigenvalue k) := by
  classical
  calc
    _ = ∑ p, ((∑ j, normalFrameSecondReal ω₀ ω₁ x F p j / F.eigenvalue j) -
        ∑ j, ∑ k, ‖normalFrameFirstDerivative F p j k‖ ^ 2 /
          (F.eigenvalue j * F.eigenvalue k)) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact normalFrame_logdet_second_jet_at_index ω₀ ω₁ x F p
    _ = _ := by rw [Finset.sum_sub_distrib]

end KahlerForm
