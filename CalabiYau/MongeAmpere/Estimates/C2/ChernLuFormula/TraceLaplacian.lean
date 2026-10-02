module

public import CalabiYau.Geometry.Kahler.Laplacian
public import CalabiYau.Geometry.Complex.Forms.OneOne
public import CalabiYau.MongeAmpere.Estimates.C2.ChernLuFormula.NormalFrameJets

import CalabiYau.MongeAmpere.Estimates.C2.NormalFrameLaplacian
import CalabiYau.MongeAmpere.Estimates.C2.RelativeTraceRegularity
import CalabiYau.MongeAmpere.Estimates.C2.ReferenceCurvatureTransport
import CalabiYau.MongeAmpere.Estimates.C2.ReferenceCurvatureTransport.PullbackConnectionGerm
import CalabiYau.MongeAmpere.Estimates.C2.HermitianFirstJet
import CalabiYau.MongeAmpere.Estimates.C2.RelativeTraceSecondJet
import CalabiYau.MongeAmpere.Estimates.C2.RelativeTraceGerm

/-!
# Laplacian of the unlogged relative trace

This theorem isolates the second-order part of the normal-coordinate calculation.  Put
`u = tr_{ω₀} ω₁`.  In the normal frame, `u` is the trace of the varying coefficient matrix because
the reference matrix is the identity.  Its complex Hessian has two contributions: the mixed second
jets of the varying metric, and the second jet of the inverse reference metric.  The latter is the
signed reference bisectional-curvature contraction.

Unlike the logarithmic expansion, there is no negative square term here.  That term appears only
when the scalar chain rule is applied to `log u`; it is kept separate so that this lemma
contains just the geometric Hessian of the trace.  The denominators `λₚ` come from tracing the
Hessian against the varying metric at the center, while `λⱼ` weights the `j`-th diagonal component
of the varying metric in the curvature term.

The curvature sign is fixed by `chartCurvature`: in reference normal coordinates the curvature
entry is `-∂ₚ∂̄p g⁰_{j j̄}`, and it enters `Δ_{ω₁}u` with the plus sign shown.  This is the same
signed bisectional entry used in the uniform lower-bound theorem.

Degenerate-case audit: for `n = 0` both sums are empty and the Laplacian is zero; for `n = 1` the
formula is the single second jet divided by `λ` plus the reference curvature weighted by `λ/λ`;
on a flat one-dimensional torus with constant metrics all terms vanish.  The pullback convention
remains `J.transpose * G * J.map star` (the `J = i` test in dimension one fixes the coefficient
order).
-/

@[expose] public section

open scoped Manifold ContDiff ComplexOrder MatrixOrder
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

private theorem relTrace_contDiffAt_normalFrame
    (ω₀ ω₁ : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x) :
    ContDiffAt ℝ 2
      (fun z ↦ relTrace (ω₀ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm
        (F.map z))) (ω₁ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm
        (F.map z)))) F.center := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  have hrel := contDiffAt_relativeTrace_inChart ω₀ ω₁ x
  rw [← F.center_eq_chart_center] at hrel
  have hmap : ContDiffAt ℝ 2 F.map F.center := by
    have hle : (2 : ℕ∞ω) ≤ ∞ := by
      change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
      exact WithTop.coe_le_coe.mpr le_top
    exact (F.smooth_map.contDiffAt (F.isOpen_domain.mem_nhds F.center_mem)).of_le hle
  have hcomp := hrel.comp F.center hmap
  simpa [e, Function.comp_def] using hcomp

open scoped Matrix.Norms.Elementwise in
private theorem normalFrame_pulledBackMetric_contDiffAt_two
    (ω₀ ω₁ ωr : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x) :
    ContDiffAt ℝ 2 (pulledBackMetricInChart ωr x F.map) F.center := by
  let G := pulledBackMetricInChart ωr x F.map
  let H := ωr.metricInChart x
  have hH : ∀ a b, ContDiffAt ℝ ∞ (fun w ↦ H w a b) (F.map F.center) := by
    intro a b
    exact (ωr.contDiffOn_metricInChart x a b).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds (F.maps_into_chart F.center F.center_mem))
  have hdet : IsUnit (H (F.map F.center)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1
      (ωr.posDef_metricInChart x (F.maps_into_chart F.center F.center_mem)).isUnit
  have hjac : IsUnit (holomorphicJacobianMatrix F.map F.center).det :=
    isUnit_iff_ne_zero.mpr F.jacobian_det_ne_zero
  have hf : ContDiffOn ℝ 3 F.map F.domain :=
    F.smooth_map.of_le (WithTop.coe_le_coe.mpr le_top)
  have hjet := holomorphicJacobianJetAt_of_contDiffOn F.domain F.isOpen_domain
    F.map hf F.holomorphic_map F.center F.center_mem hjac
  have hC2 := (pullbackConnection_germ F.domain F.isOpen_domain F.map hf F.holomorphic_map
    G H F.center F.center_mem hH hjac hdet (fun _ _ ↦ rfl) hjet).1
  exact contDiffAt_pi.mpr (fun a ↦ contDiffAt_pi.mpr (fun b ↦ hC2 a b))

open Filter Topology in
private theorem normalFrame_pulledBackMetric_hermitian_germ
    (ω₀ ω₁ ωr : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x) :
    ∀ᶠ w in 𝓝 F.center, (pulledBackMetricInChart ωr x F.map w).IsHermitian := by
  filter_upwards [F.isOpen_domain.mem_nhds F.center_mem] with w hw
  have hmetric := (ωr.posDef_metricInChart x (F.maps_into_chart w hw)).isHermitian
  let J := holomorphicJacobianMatrix F.map w
  let H := ωr.metricInChart x (F.map w)
  have hJ1 : (J.map star).conjTranspose = J.transpose := by
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.transpose_apply]
  have hJ2 : J.transpose.conjTranspose = J.map star := by
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.transpose_apply]
  change (J.transpose * H * J.map star).conjTranspose = _
  calc
    _ = (J.map star).conjTranspose * H.conjTranspose * J.transpose.conjTranspose := by
      simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [hJ1, hmetric.eq, hJ2]; rfl

open Filter Topology in
private theorem complexHessian_diag_re_eventuallyEq
    {f g : EuclideanSpace ℂ (Fin n) → ℝ} {z : EuclideanSpace ℂ (Fin n)}
    (hf : ContDiffAt ℝ 2 f z) (heq : f =ᶠ[𝓝 z] g) (p : Fin n) :
    (complexHessian f z p p).re = (complexHessian g z p p).re := by
  have hg : ContDiffAt ℝ 2 g z := hf.congr_of_eventuallyEq heq.symm
  have hder := (heq.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ) (x := z)
  rw [complexHessian_apply hf, complexHessian_apply hg, hder]

private theorem normalFrame_relative_trace_hessian_curvature_rhs
    (ω₀ ω₁ : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x)
    (p : Fin n) :
    (∑ j, normalFrameSecondReal ω₀ ω₁ x F p j) +
        ∑ j, F.eigenvalue j * normalFrameBisectionalCurvature ω₀ ω₁ x F p j =
      (∑ j, (normalFrameMixedSecondDerivative ω₀ ω₁ x F p p j j).re) -
        ∑ j, F.eigenvalue j * (chartPartialZComplex
          (fun z ↦ chartPartialBarComplex
            (fun w ↦ pulledBackMetricInChart ω₀ x F.map w j j) z p)
          F.center p).re := by
  classical
  simp_rw [normalFrameBisectionalCurvature_eq_neg_reference_mixedSecond ω₀ ω₁ x F p]
  simp only [normalFrameSecondReal, normalFrameMixedSecondDerivative]
  simp_rw [mul_neg]
  rw [Finset.sum_neg_distrib]
  abel

open scoped Matrix.Norms.Elementwise in
private theorem normalFrame_relative_trace_hessian_expansion
    (ω₀ ω₁ : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x) :
    ∀ p, RCLike.re (complexHessian
      (((fun y ↦ relTrace (ω₀ y) (ω₁ y)) ∘
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) ∘ F.map)
      F.center p p) =
      (∑ j, normalFrameSecondReal ω₀ ω₁ x F p j) +
        ∑ j, F.eigenvalue j * normalFrameBisectionalCurvature ω₀ ω₁ x F p j := by
  intro p
  let G₀ := pulledBackMetricInChart ω₀ x F.map
  let G₁ := pulledBackMetricInChart ω₁ x F.map
  have hC₀ : ContDiffAt ℝ 2 G₀ F.center :=
    normalFrame_pulledBackMetric_contDiffAt_two ω₀ ω₁ ω₀ x F
  have hC₁ : ContDiffAt ℝ 2 G₁ F.center :=
    normalFrame_pulledBackMetric_contDiffAt_two ω₀ ω₁ ω₁ x F
  have hFirstReal : fderiv ℝ G₀ F.center = 0 :=
    Matrix.fderiv_eq_zero_of_eventually_isHermitian_of_partialZ_eq_zero G₀ F.center
      (hC₀.differentiableAt (by norm_num))
      (normalFrame_pulledBackMetric_hermitian_germ ω₀ ω₁ ω₀ x F)
      F.reference_first_derivative_zero
  have hEq := normalFrame_relative_trace_eventually_eq_matrix_trace ω₀ ω₁ x F
  have hTransfer := complexHessian_diag_re_eventuallyEq
    (relTrace_contDiffAt_normalFrame ω₀ ω₁ x F) hEq p
  have hJet := complexHessian_relativeTraceMatrix_diag_of_normal G₀ G₁ F.center
    F.eigenvalue
    (fun j k ↦ contDiffAt_pi.mp (contDiffAt_pi.mp hC₀ j) k)
    (fun j k ↦ contDiffAt_pi.mp (contDiffAt_pi.mp hC₁ j) k)
    F.reference_normalized F.varying_diagonal hFirstReal p
  refine hTransfer.trans (hJet.trans ?_)
  simpa only [normalFrameMixedSecondDerivative, G₀, G₁] using
    (normalFrame_relative_trace_hessian_curvature_rhs ω₀ ω₁ x F p).symm

/-- Exact normal-frame Laplacian of the unlogged relative trace. -/
theorem normalFrame_laplacian_relative_trace
    (ω₀ ω₁ : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x) :
    ω₁.laplacian (fun y ↦ relTrace (ω₀ y) (ω₁ y)) x =
      (∑ p, ∑ j, normalFrameSecondReal ω₀ ω₁ x F p j / F.eigenvalue p) +
        ∑ p, ∑ j, (F.eigenvalue p)⁻¹ * F.eigenvalue j *
          normalFrameBisectionalCurvature ω₀ ω₁ x F p j := by
  have hf := contDiffAt_relativeTrace_inChart ω₀ ω₁ x
  rw [← F.center_eq_chart_center] at hf
  rw [normalFrame_laplacian_eq_hessian_sum ω₀ ω₁ x F
    (fun y ↦ relTrace (ω₀ y) (ω₁ y)) hf]
  calc
    _ = ∑ p, ((∑ j, normalFrameSecondReal ω₀ ω₁ x F p j) +
        ∑ j, F.eigenvalue j * normalFrameBisectionalCurvature ω₀ ω₁ x F p j) /
          F.eigenvalue p := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [normalFrame_relative_trace_hessian_expansion ω₀ ω₁ x F p]
    _ = _ := by
      simp_rw [add_div]
      rw [Finset.sum_add_distrib]
      congr 1
      · simp_rw [Finset.sum_div]
      · apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j hj
        simp [div_eq_mul_inv, mul_comm, mul_left_comm]

end KahlerForm
