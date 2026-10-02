module

public import CalabiYau.MongeAmpere.Estimates.C3.TraceLaplacian.Refined.NormalFrameTraceExpansion
public import CalabiYau.MongeAmpere.Estimates.C3.TraceLaplacian.Refined.NormalFrameDeterminantHessian

/-!
# The trace-Hessian identity at a normal coordinate center

Differentiate the matrix trace and the determinant equation at a point where
the reference metric is normal and the perturbed metric is diagonal. Kähler
symmetry interchanges the mixed metric derivatives in the trace; differentiating
the determinant replaces them by the mixed derivatives of the logarithmic
right-hand side and a nonnegative square. The remaining second derivatives of
the reference metric combine into the signed curvature error.

This is a **local matrix identity**, not an assertion that such a chart exists
on the manifold. The local metric, determinant-equation, and Kähler-symmetry
hypotheses are explicit so its normal-frame realization can be proved as a
separate chart bridge.

Source: Székelyhidi, *An Introduction to Extremal Kähler Metrics*, §3.3,
Lemma 3.10, pp. 45–46, using the determinant differentiation in §3.2,
Lemma 3.8. The same normal-coordinate identity is in Yau (1978), §3.
-/

@[expose] public section

open scoped BigOperators Manifold ContDiff NNReal ComplexOrder MatrixOrder
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ}

/-- The source normal-coordinate identity *before* bounding either signed
error. The inverse eigenvalue belongs to the differentiation index in the
trace Hessian; the positive third-derivative contraction instead has inverse
factors on the two metric indices. The mixed right-hand-side derivative uses
`∂z∂bar` (a quarter of the real two-plane Laplacian). -/
theorem c3RefinedTrace_normalTraceHessian_identity
    (g h : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (G : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (lam : Fin n → ℝ)
    (hg : ∀ i j, ContDiffAt ℝ ∞ (fun w ↦ g w i j) z)
    (hh : ∀ i j, ContDiffAt ℝ ∞ (fun w ↦ h w i j) z)
    (hG : ContDiffAt ℝ ∞ G z)
    (hNormal : g z = 1)
    (hFirst : ∀ i j p, c3PartialZ (fun w ↦ g w i j) z p = 0)
    (hDiagonal : h z = Matrix.diagonal (fun i ↦ (lam i : ℂ)))
    (hPositive : ∀ i, 0 < lam i)
    (hLocal : ∃ U : Set (EuclideanSpace ℂ (Fin n)),
      IsOpen U ∧ z ∈ U ∧ ∀ w ∈ U,
        g w = (g w).conjTranspose ∧ h w = (h w).conjTranspose ∧
          (h w).det = Complex.exp (G w) * (g w).det)
    (hKahler : ∀ p j : Fin n,
      c3RefinedTraceMatrixMixedPartial h z p p j j =
        c3RefinedTraceMatrixMixedPartial h z j j p p) :
    RCLike.re (((h z)⁻¹ * Matrix.of (fun p q ↦
        c3PartialZ (fun w ↦ c3RefinedTracePartialBar
          (fun v ↦ c3RefinedTraceRelativeMatrixTrace g h v) w q) z p)).trace) =
      (∑ p : Fin n,
        RCLike.re (c3PartialZ (fun w ↦ c3RefinedTracePartialBar G w p) z p)) +
      (∑ p : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        ‖c3PartialZ (fun w ↦ h w j k) z p‖ ^ (2 : ℕ) /
          (lam j * lam k)) +
      (∑ p : Fin n, ∑ j : Fin n,
        (lam j / lam p - 1) *
          RCLike.re (c3RefinedTraceReferenceCurvatureInChart g z p p j j)) := by
  have hHermitian : ∃ U : Set (EuclideanSpace ℂ (Fin n)),
      IsOpen U ∧ z ∈ U ∧ ∀ w ∈ U, g w = (g w).conjTranspose := by
    obtain ⟨U, hU, hz, hdata⟩ := hLocal
    exact ⟨U, hU, hz, fun w hw => (hdata w hw).1⟩
  have hTrace := c3RefinedTrace_normalFrame_traceExpansion g h z lam hg hh hNormal
    hFirst hDiagonal hPositive hHermitian
  have hDet := c3RefinedTrace_normalFrame_determinantHessian g h G z lam hg hh hG hNormal
    hFirst hDiagonal hPositive hLocal
  have hExchange :
      (∑ p : Fin n, ∑ j : Fin n,
        RCLike.re (c3RefinedTraceMatrixMixedPartial h z p p j j) / lam p) =
      (∑ p : Fin n, ∑ j : Fin n,
        RCLike.re (c3RefinedTraceMatrixMixedPartial h z j j p p) / lam p) := by
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro j hj
    rw [hKahler p j]
  rw [hTrace, hExchange, hDet]
  simp_rw [sub_mul, one_mul, Finset.sum_sub_distrib]
  ring

end KahlerForm
