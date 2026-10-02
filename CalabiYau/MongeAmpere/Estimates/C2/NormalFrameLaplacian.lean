module

public import CalabiYau.Geometry.Kahler.Laplacian
public import CalabiYau.MongeAmpere.Estimates.C2.ChernLuFormula.NormalCoordinates
public import CalabiYau.MongeAmpere.Estimates.C2.NormalFrameGradient

/-!
# The scalar Laplacian in a holomorphic normal frame

This module transports the intrinsic complex Laplacian to the diagonal coordinates of a genuine
holomorphic normal frame. The local regularity assumption is only at the point of evaluation.
-/

@[expose] public section

open scoped Manifold ContDiff ComplexOrder MatrixOrder
open ContinuousAlternatingMap Filter

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

/-- A complex-linear continuous equivalence representing the differential of a holomorphic normal
frame at its center. -/
private theorem relTrace_eq_sum_of_diagonal_coeffMatrix
    (α β : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
    (eig : Fin n → ℝ) (heig : ∀ p, 0 < eig p)
    (hdiag : α.coeffMatrix = Matrix.diagonal (RCLike.ofReal ∘ eig)) :
    relTrace α β = ∑ p, RCLike.re (β.coeffMatrix p p) / eig p := by
  rw [relTrace, hdiag, Matrix.inv_diagonal]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  simp only [Matrix.diagonal_apply]
  simp
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  let v : Fin n → ℂ := Complex.ofReal ∘ eig
  let w : Fin n → ℂ := fun q ↦ (v q)⁻¹
  have hvw : v * w = 1 := by
    ext q
    simp [v, w, Function.comp_apply, ne_of_gt (heig q)]
  have hunit : IsUnit v := (isUnit_iff_exists_inv).2 ⟨w, hvw⟩
  have hinv : Ring.inverse (Complex.ofReal ∘ eig) =
      fun q ↦ Complex.ofReal ((eig q)⁻¹) := by
    rw [show (Complex.ofReal ∘ eig) = v by rfl, Ring.inverse_of_isUnit hunit]
    ext q
    simp [v]
  rw [hinv]
  simp [Complex.ofReal_re, Complex.ofReal_im, div_eq_mul_inv]
  field_simp [ne_of_gt (heig p)]

private theorem normalFrame_mddbar_pullback
    (ω₀ ω₁ : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x)
    (f : M → ℝ) (hf : ContDiffAt ℝ 2
      (f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
      (F.map F.center))
    (A : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n))
    (hA : (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) =
      fderiv ℂ F.map F.center) :
    (mddbar n f x).compContinuousLinearMap
        ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ) =
      ddbar ((f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) ∘ F.map)
        F.center := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let g := f ∘ e.symm
  have hcenter : F.map F.center = e x := F.center_eq_chart_center
  have hhol : ∀ᶠ z in nhds F.center, DifferentiableAt ℂ F.map z := by
    filter_upwards [F.isOpen_domain.mem_nhds F.center_mem] with z hz
    exact (F.holomorphic_map z hz).differentiableAt (F.isOpen_domain.mem_nhds hz)
  change (ddbar g (e x)).compContinuousLinearMap
      ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ) =
    ddbar (g ∘ F.map) F.center
  rw [← hcenter, hA]
  exact (ddbar_comp_holomorphic hhol hf).symm

private theorem normalFrame_laplacian_eq_pulledback_relTrace
    (ω₀ ω₁ : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x)
    (f : M → ℝ) (hf : ContDiffAt ℝ 2
      (f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
      (F.map F.center))
    (A : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n))
    (hA : (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) =
      fderiv ℂ F.map F.center) :
      ω₁.laplacian f x = relTrace
        ((ω₁ x).compContinuousLinearMap
          ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ))
        (ddbar ((f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) ∘ F.map)
          F.center) := by
  have hη : (mddbar n f x).IsOneOne := by
    change (ddbar (f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x)).IsOneOne
    rw [← F.center_eq_chart_center]
    exact isOneOne_ddbar hf
  have htrace := relTrace_compContinuousLinearMap (ω₁.isOneOne x) hη A
  calc
    ω₁.laplacian f x = relTrace (ω₁ x) (mddbar n f x) := rfl
    _ = relTrace
        ((ω₁ x).compContinuousLinearMap
          ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ))
        ((mddbar n f x).compContinuousLinearMap
          ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)) :=
      htrace.symm
    _ = relTrace
        ((ω₁ x).compContinuousLinearMap
          ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ))
        (ddbar ((f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) ∘ F.map)
          F.center) := by
      rw [normalFrame_mddbar_pullback ω₀ ω₁ x F f hf A hA]

/-- In holomorphic normal-frame coordinates the complex Laplacian is the diagonal sum of the
mixed complex Hessian divided by the eigenvalues of the varying metric. -/
theorem normalFrame_laplacian_eq_hessian_sum
    (ω₀ ω₁ : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x) (f : M → ℝ)
    (hf : ContDiffAt ℝ 2
      (f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
      (F.map F.center)) :
    ω₁.laplacian f x = ∑ p,
      RCLike.re (complexHessian
        ((f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) ∘ F.map)
        F.center p p) / F.eigenvalue p := by
  obtain ⟨A, hA, hdiag⟩ := normalFrame_varying_metric_coeffMatrix ω₀ ω₁ x F
  have hlap := normalFrame_laplacian_eq_pulledback_relTrace ω₀ ω₁ x F f hf A hA
  rw [hlap]
  simpa [complexHessian] using
    (relTrace_eq_sum_of_diagonal_coeffMatrix
      ((ω₁ x).compContinuousLinearMap
        ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ))
      (ddbar ((f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) ∘ F.map)
        F.center) F.eigenvalue F.eigenvalue_pos hdiag)

end KahlerForm
