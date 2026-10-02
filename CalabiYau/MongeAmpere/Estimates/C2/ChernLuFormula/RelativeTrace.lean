module

public import CalabiYau.Geometry.Complex.Forms.OneOne
public import CalabiYau.MongeAmpere.Estimates.C2.ChernLuFormula.NormalFrameJets

/-!
# Relative traces in a simultaneous normal frame

Székelyhidi's diagonalization step turns the two intrinsic relative traces into the sum of the
positive eigenvalues and the sum of their reciprocals.  The normal frame is normalized for the
reference metric and diagonal for the varying metric, so the metric matrices at the center are
`1` and `diag (ofReal ∘ eigenvalue)`.  The two identities below are precisely the finite-dimensional
trace invariance statements needed by the Chern–Lu calculation.

The order in the reverse trace matters.  With the repository's convention
`relTrace α β = re trace (A⁻¹ * B)`, the forward trace `tr_{ω₀} ω₁` is `∑ λⱼ`, while
`tr_{ω₁} ω₀` is `∑ λⱼ⁻¹`.  This theorem does not silently replace a trace by a sum without retaining
the relation to the actual pullback frame: the hypotheses on `F` specify its center, its pulled-back
metric matrices, and the local holomorphic coordinate map.

The hypotheses that the Kähler forms are positive ensure each frame eigenvalue is strictly
positive.  This is essential for the reciprocal sum in the reverse trace.  No upper or lower bound
on those eigenvalues is claimed, since they vary with `ω₁` and `x`.

Degenerate-case audit:

* If `n = 0`, both sides of each trace identity are zero; the eigenvalue and index sums are empty.
* For `n = 1`, both identities reduce to `tr_{ω₀}ω₁ = λ` and
  `tr_{ω₁}ω₀ = λ⁻¹`, with `λ > 0`.
* For a flat torus, choose the flat reference coordinates and diagonalize the positive Hermitian
  varying metric at the point.  The identities agree with the standard matrix trace and do not
  depend on the choice of the unitary diagonalizer.
* For a complex-linear coordinate change with Jacobian `J`, the pulled-back matrices use
  `J.transpose * G * J.map star`.  In one dimension the test `J = i` sends the unit metric to
  `i * 1 * (-i) = 1`, which validates the row-column convention used by the two trace formulas.

The two conjuncts are the forward and reverse instances of one
simultaneous Hermitian diagonalization result, not independent estimates.  They furnish exactly the
trace identities used in the logarithmic denominator of the Laplacian
calculation.
-/

@[expose] public section

open scoped Manifold ContDiff ComplexOrder MatrixOrder
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

private theorem relative_trace_eq_sum_of_unit_pullback
    (form₀ form₁ : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
    (A : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n))
    (hform₀ : form₀.IsOneOne) (hform₁ : form₁.IsOneOne)
    (hunit : (form₀.compContinuousLinearMap
      ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)).coeffMatrix = 1) :
    relTrace form₀ form₁ = ∑ p, RCLike.re
      ((form₁.compContinuousLinearMap
        ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)).coeffMatrix p p) := by
  have htrace := relTrace_compContinuousLinearMap hform₀ hform₁ A
  rw [← htrace]
  simp [relTrace, hunit, Matrix.trace]

/-- In a Yau normal frame, the forward and reverse intrinsic relative traces are the eigenvalue
sum and reciprocal eigenvalue sum, respectively. -/
theorem normalFrame_relative_trace_eq_sums
    (ω₀ ω₁ : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x) :
    relTrace (ω₀ x) (ω₁ x) = ∑ j, F.eigenvalue j ∧
      relTrace (ω₁ x) (ω₀ x) = ∑ j, (F.eigenvalue j)⁻¹ := by
  obtain ⟨A, hA⟩ := F.exists_jacobian_equiv
  let Aℝ := (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ
  have hcenter : F.map F.center = extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x :=
    F.center_eq_chart_center
  have hmetric₀ : ω₀.metricInChart x (F.map F.center) = (ω₀ x).coeffMatrix := by
    rw [hcenter, ω₀.metricInChart_self]
  have hmetric₁ : ω₁.metricInChart x (F.map F.center) = (ω₁ x).coeffMatrix := by
    rw [hcenter, ω₁.metricInChart_self]
  have hJ : holomorphicJacobianMatrix F.map F.center = EuclideanSpace.clmMatrix A := by
    simp [holomorphicJacobianMatrix, hA]
  have hnormal₀ := F.reference_normalized
  change Matrix.transpose (holomorphicJacobianMatrix F.map F.center) *
      ω₀.metricInChart x (F.map F.center) *
      (holomorphicJacobianMatrix F.map F.center).map star = 1 at hnormal₀
  rw [hJ, hmetric₀] at hnormal₀
  have hnormal₁ := F.varying_diagonal
  change Matrix.transpose (holomorphicJacobianMatrix F.map F.center) *
      ω₁.metricInChart x (F.map F.center) *
      (holomorphicJacobianMatrix F.map F.center).map star =
        Matrix.diagonal (RCLike.ofReal ∘ F.eigenvalue) at hnormal₁
  rw [hJ, hmetric₁] at hnormal₁
  have hcoeff₀ : ((ω₀ x).compContinuousLinearMap Aℝ).coeffMatrix = 1 := by
    calc
      _ = Matrix.transpose (EuclideanSpace.clmMatrix A) * (ω₀ x).coeffMatrix *
          (EuclideanSpace.clmMatrix A).map star :=
        (ω₀.isOneOne x).coeffMatrix_compContinuousLinearMap A
      _ = 1 := hnormal₀
  have hcoeff₁ : ((ω₁ x).compContinuousLinearMap Aℝ).coeffMatrix =
      Matrix.diagonal (RCLike.ofReal ∘ F.eigenvalue) := by
    calc
      _ = Matrix.transpose (EuclideanSpace.clmMatrix A) * (ω₁ x).coeffMatrix *
          (EuclideanSpace.clmMatrix A).map star :=
        (ω₁.isOneOne x).coeffMatrix_compContinuousLinearMap A
      _ = Matrix.diagonal (RCLike.ofReal ∘ F.eigenvalue) := hnormal₁
  have hforward := relative_trace_eq_sum_of_unit_pullback (ω₀ x) (ω₁ x) A
    (ω₀.isOneOne x) (ω₁.isOneOne x) hcoeff₀
  have hreverse := relTrace_compContinuousLinearMap (ω₁.isOneOne x) (ω₀.isOneOne x) A
  have hcoeff₁' : ((ω₁ x).compContinuousLinearMap Aℝ).coeffMatrix =
      Matrix.diagonal (RCLike.ofReal ∘ F.eigenvalue) := by
    simpa [Aℝ] using hcoeff₁
  have hcoeff₀' : ((ω₀ x).compContinuousLinearMap Aℝ).coeffMatrix = 1 := by
    simpa [Aℝ] using hcoeff₀
  constructor
  · rw [hforward]
    rw [hcoeff₁']
    simp
  · rw [← hreverse]
    change RCLike.re (((ω₁ x).compContinuousLinearMap Aℝ).coeffMatrix⁻¹ *
      ((ω₀ x).compContinuousLinearMap Aℝ).coeffMatrix).trace = _
    rw [hcoeff₁', hcoeff₀']
    have heig_ne : ∀ j, F.eigenvalue j ≠ 0 := fun j => (F.eigenvalue_pos j).ne'
    rw [Matrix.mul_one, Matrix.inv_diagonal]
    simp [Matrix.trace, Ring.inverse, Pi.isUnit_iff, heig_ne]

end KahlerForm
