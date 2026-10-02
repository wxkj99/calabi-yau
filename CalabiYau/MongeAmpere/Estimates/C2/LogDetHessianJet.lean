module

public import CalabiYau.Geometry.Kahler.Curvature.Chart
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import CalabiYau.MongeAmpere.Estimates.C2.LogDetHessianJet.FirstJet
import CalabiYau.MongeAmpere.Estimates.C2.LogDetHessianJet.MixedInverseTrace
import CalabiYau.MongeAmpere.Estimates.C2.LogDetHessianJet.HermitianDiagonal
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# The logarithmic determinant Hessian at a positive diagonal center

This is the local matrix calculation in the C² estimate: first differentiate `log det G` in the
barred direction, then differentiate its inverse-trace expression in the unbarred direction. For a
Hermitian field, its barred first jet is the conjugate transpose of its unbarred first jet. At a
positive diagonal center the resulting traces are the eigenvalue-weighted second jet minus the
weighted squared norm of the first jet.

Only entrywise real C² regularity at the center and a Hermitian neighborhood germ are needed.
Positive diagonal entries at the center provide the local determinant sign and invertibility.
There is no global positivity, Kähler condition, equation, or positive-dimension assumption.
The order is `∂ₚ(∂̄ₚ f)` with both Wirtinger operators normalized by `1/2`. In dimension one this
is `H/lam - |T|²/lam²`; for `G = lam + c x` it gives `-c²/(4 lam²)`. Constant flat metrics give zero.
The algebraic contractions also hold for the empty matrix; the per-direction statement has no
index in dimension zero.

The calculation combines the first trace germ, its mixed inverse-trace derivative, and
Hermitian/diagonal contractions. Concrete nonreal-index examples check the index conventions.

## References

Székelyhidi, *An Introduction to Extremal Kähler Metrics*, §1.4, Lemma 1.22 proof, p. 12:
the first logarithmic determinant trace identity and its differentiated form, before identifying
it with Ricci curvature. The source Ricci convention is the negative logarithmic Hessian; the
statement here is the positive logarithmic Hessian itself. The diagonal choice in §3.2,
Lemma 3.7, p. 41, motivates this evaluation, but equation (3.6) there is a log-trace inequality,
not the log-determinant identity.
-/

public section

open scoped ContDiff ComplexOrder MatrixOrder
open Filter Topology

namespace KahlerForm

private theorem log_det_bar_field_differentiable {n : ℕ}
    {f : EuclideanSpace ℂ (Fin n) → ℂ} {z : EuclideanSpace ℂ (Fin n)}
    (hf : ContDiffAt ℝ 2 f z) (p : Fin n) :
    DifferentiableAt ℝ (fun w ↦ chartPartialBarComplex f w p) z := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ f) z := hf.fderiv_right (by norm_num)
  have he (v : EuclideanSpace ℂ (Fin n)) :
      ContDiffAt ℝ 1 (fun w ↦ fderiv ℝ f w v) z := by
    exact hd.clm_apply contDiffAt_const
  unfold chartPartialBarComplex
  simp only [div_eq_mul_inv]
  exact (((he (EuclideanSpace.single p 1)).differentiableAt (by norm_num)).add
    (((he (Complex.I • EuclideanSpace.single p 1)).differentiableAt
      (by norm_num)).const_mul Complex.I)).mul_const (2 : ℂ)⁻¹

/-- The ordered mixed logarithmic determinant jet of a locally Hermitian C² field at a positive
real diagonal center. The first-jet contraction has the full coefficient-index norm square; no
Hermitian or Kähler symmetry of the unbarred first jet is assumed. -/
theorem log_det_mixed_second_real_of_diagonal {n : ℕ}
    (G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (lam : Fin n → ℝ)
    (hG : ∀ j k, ContDiffAt ℝ 2 (fun w ↦ G w j k) z)
    (hHerm : ∀ᶠ w in 𝓝 z, (G w).IsHermitian)
    (hdiag : G z = Matrix.diagonal (fun j ↦ (lam j : ℂ)))
    (hlam : ∀ j, 0 < lam j) (p : Fin n) :
    (chartPartialZComplex
      (fun w ↦ chartPartialBarComplex
        (fun v ↦ (Real.log ((G v).det.re) : ℂ)) w p) z p).re =
      (∑ j, (chartPartialZComplex
        (fun w ↦ chartPartialBarComplex (fun v ↦ G v j j) w p) z p).re / lam j) -
      ∑ j, ∑ k, ‖chartPartialZComplex (fun w ↦ G w j k) z p‖ ^ 2 /
        (lam j * lam k) := by
  classical
  have hG1 : ∀ j k, ContDiffAt ℝ 1 (fun w ↦ G w j k) z :=
    fun j k ↦ (hG j k).of_le (by norm_num)
  have hPD : (G z).PosDef := by
    rw [hdiag, Matrix.posDef_diagonal_iff]
    intro j
    exact_mod_cast hlam j
  have hpos : 0 < (G z).det.re := (Complex.pos_iff.mp hPD.det_pos).1
  have hunit : IsUnit (G z) :=
    (Matrix.isUnit_iff_isUnit_det (A := G z)).mpr (ne_of_gt hPD.det_pos).isUnit
  have hB : ∀ j k, DifferentiableAt ℝ
      (fun w ↦ chartPartialBarComplex (fun v ↦ G v j k) w p) z :=
    fun j k ↦ log_det_bar_field_differentiable (hG j k) p
  have hfirst := log_det_bar_first_jet_eventually G z p hG1 hHerm hpos
  have hjet := log_det_mixed_inverse_trace_jet p hG1 hunit hB hfirst
  let T : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.of (fun j k ↦ chartPartialZComplex (fun w ↦ G w j k) z p)
  let H : Matrix (Fin n) (Fin n) ℂ := Matrix.of (fun j k ↦
    chartPartialZComplex
      (fun w ↦ chartPartialBarComplex (fun v ↦ G v j k) w p) z p)
  have hconj : Matrix.of (fun j k ↦
      chartPartialBarComplex (fun w ↦ G w j k) z p) = T.conjTranspose := by
    ext j k
    exact log_det_hermitian_bar_jet hG1 hHerm p j k
  change chartPartialZComplex
      (fun w ↦ chartPartialBarComplex
        (fun v ↦ (Real.log ((G v).det.re) : ℂ)) w p) z p =
      Matrix.trace ((G z)⁻¹ * H) -
        Matrix.trace ((G z)⁻¹ * T * (G z)⁻¹ *
          Matrix.of (fun j k ↦ chartPartialBarComplex (fun w ↦ G w j k) z p)) at hjet
  rw [hconj, hdiag] at hjet
  have hre := congrArg Complex.re hjet
  rw [Complex.sub_re, log_det_diagonal_inverse_trace_real lam H hlam,
    log_det_diagonal_inverse_quadratic_trace_real lam T hlam] at hre
  exact hre

end KahlerForm
