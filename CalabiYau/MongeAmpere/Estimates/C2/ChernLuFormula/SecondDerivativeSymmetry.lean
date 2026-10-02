module

public import CalabiYau.MongeAmpere.Estimates.C2.ChernLuFormula.NormalFrameJets
import CalabiYau.MongeAmpere.Estimates.C2.PullbackMetricSymmetry
import CalabiYau.MongeAmpere.Estimates.C2.SecondJetSymmetry
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Symmetry of diagonal mixed second jets

The two local Chern–Lu expansions use the same real array
`Hₚⱼ = Re(∂ₚ∂̄p g'_{j j̄})`.  The trace-Laplacian formula initially has denominator `λₚ`, while
the Ricci/log-determinant formula has denominator `λⱼ`.  To identify their linear second-jet
terms, one needs `Hₚⱼ = Hⱼₚ`.  This is a consequence of the Kähler identities in both metric
indices and commutation of the mixed derivatives; it is a geometric input, not a numerical
symmetry of an arbitrary array.

The theorem is therefore formulated for the varying metric pulled back by a genuine holomorphic
normal frame.  It is not stated for arbitrary smooth matrix-valued functions.  The first-derivative
the symmetry theorem supplies the closedness/Kähler identity for the varying metric coefficients, while
`normalFrameMixedSecondDerivative` fixes which derivative is holomorphic and which is
antiholomorphic.  Hermitian reality on the diagonal then makes the real parts in the statement the
actual mixed diagonal jets used by the two formulas.

The index audit is important here.  Our coefficient matrix stores holomorphic indices in rows and
antiholomorphic indices in columns, and its pullback is
`J.transpose * G * J.map star`.  Thus the diagonal second derivative uses coefficient `(j,j)` and
directions `(p,p)`.  The equality swaps the pair of differentiation/coefficient indices, not the
holomorphic and antiholomorphic slots.  For `n = 1` the equality is tautological; for `n = 0` it
has no instances.  On a flat torus with a constant metric both sides vanish.

A useful linear-coordinate check is `n = 1`, `J = i`: the pullback of the reference coefficient
is still `1`, since `i * 1 * star i = 1`.  This confirms that the symmetry is attached to the
intended normal-frame coefficients and is not an artifact of a mistaken Hermitian-transpose
convention.  No Ricci-flatness, Monge–Ampère equation, or fixed cohomology class is needed.
-/

open scoped Manifold ContDiff ComplexOrder MatrixOrder Matrix.Norms.Elementwise Topology
open Filter

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

/-- Local real C2 regularity; holomorphicity is needed on a neighborhood to identify Jacobians. -/
private theorem contDiffAt_pulledBackMetricInChart
    (ω₁ : KahlerForm n M) (x : M)
    (ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (z : EuclideanSpace ℂ (Fin n))
    (hψ : ContDiffAt ℝ 3 ψ z)
    (hψhol : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ ψ w)
    (hchart : ψ z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    ContDiffAt ℝ 2 (pulledBackMetricInChart ω₁ x ψ) z := by
  have hder : ContDiffAt ℝ 2 (fderiv ℝ ψ) z :=
    hψ.fderiv_right (by norm_num)
  have hJ (a j : Fin n) : ContDiffAt ℝ 2
      (fun w ↦ holomorphicJacobianMatrix ψ w a j) z := by
    have hcol : ContDiffAt ℝ 2
        (fun w ↦ fderiv ℝ ψ w (EuclideanSpace.single j 1)) z :=
      hder.clm_apply contDiffAt_const
    have hentry := (contDiffAt_piLp 2).mp hcol a
    have heq : (fun w ↦ holomorphicJacobianMatrix ψ w a j) =ᶠ[𝓝 z]
        (fun w ↦ (fderiv ℝ ψ w (EuclideanSpace.single j 1)) a) := by
      filter_upwards [hψhol] with w hw
      rw [hw.fderiv_restrictScalars (𝕜 := ℝ)]
      rfl
    exact hentry.congr_of_eventuallyEq heq
  have hG (a b : Fin n) : ContDiffAt ℝ 2
      (fun w ↦ ω₁.metricInChart x (ψ w) a b) z := by
    have hbase := (ω₁.contDiffOn_metricInChart x a b).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hchart)
    exact (hbase.of_le (WithTop.coe_le_coe.mpr
      (show (2 : ℕ∞) ≤ ⊤ from le_top))).comp z (hψ.of_le (by norm_num))
  have hJstar (a j : Fin n) : ContDiffAt ℝ 2
      (fun w ↦ star (holomorphicJacobianMatrix ψ w a j)) z := by
    simpa only [Function.comp_def, Complex.conjCLE_apply, Complex.star_def] using
      Complex.conjCLE.contDiff.contDiffAt.comp z (hJ a j)
  apply contDiffAt_pi.mpr
  intro j
  apply contDiffAt_pi.mpr
  intro k
  change ContDiffAt ℝ 2 (fun w ↦
    (Matrix.transpose (holomorphicJacobianMatrix ψ w) *
      ω₁.metricInChart x (ψ w) *
        (holomorphicJacobianMatrix ψ w).map star) j k) z
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  fun_prop (disch := assumption)

end KahlerForm

@[expose] public section

open scoped Manifold ContDiff ComplexOrder MatrixOrder Matrix.Norms.Elementwise Topology
open Filter

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

/-- The real diagonal mixed second derivatives of the varying Kähler metric are symmetric in the
differentiation index and the metric index. -/
theorem normalFrame_second_derivative_symmetric
    (ω₀ ω₁ : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x) :
    ∀ p j, normalFrameSecondReal ω₀ ω₁ x F p j =
      normalFrameSecondReal ω₀ ω₁ x F j p := by
  have hmap3 : ContDiffAt ℝ 3 F.map F.center :=
    (F.smooth_map.contDiffAt (F.isOpen_domain.mem_nhds F.center_mem)).of_le
      (WithTop.coe_le_coe.mpr (show (3 : ℕ∞) ≤ ⊤ from le_top))
  have hhol : ∀ᶠ w in 𝓝 F.center, DifferentiableAt ℂ F.map w := by
    filter_upwards [F.isOpen_domain.mem_nhds F.center_mem] with w hw
    exact (F.holomorphic_map w hw).differentiableAt (F.isOpen_domain.mem_nhds hw)
  have hGmatrix := contDiffAt_pulledBackMetricInChart ω₁ x F.map F.center
    hmap3 hhol (F.maps_into_chart F.center F.center_mem)
  have hG : ∀ j k, ContDiffAt ℝ 2
      (fun w ↦ pulledBackMetricInChart ω₁ x F.map w j k) F.center := by
    intro j k
    exact contDiffAt_pi.mp (contDiffAt_pi.mp hGmatrix j) k
  have hHerm : ∀ᶠ w in 𝓝 F.center,
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
  have hKahler : ∀ᶠ w in 𝓝 F.center, ∀ i j k : Fin n,
      chartPartialZComplex (fun v ↦ pulledBackMetricInChart ω₁ x F.map v j k) w i =
        chartPartialZComplex (fun v ↦ pulledBackMetricInChart ω₁ x F.map v i k) w j := by
    filter_upwards [F.isOpen_domain.mem_nhds F.center_mem] with w hw
    intro i j k
    exact pulledBackMetricInChart_first_derivative_symmetric ω₁ x F.map F.domain
      F.isOpen_domain (F.smooth_map.of_le (WithTop.coe_le_coe.mpr
        (show (2 : ℕ∞) ≤ ⊤ from le_top))) F.holomorphic_map F.maps_into_chart hw i j k
  intro p j
  have h := diagonal_mixed_second_real_symmetric_of_partialZ_symmetry
    (fun w ↦ pulledBackMetricInChart ω₁ x F.map w) F.center hG hHerm hKahler p j
  simpa [normalFrameSecondReal, normalFrameMixedSecondDerivative] using h

end KahlerForm
