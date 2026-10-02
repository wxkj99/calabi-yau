module

public import CalabiYau.MongeAmpere.Estimates.C3.TraceLaplacian.Refined.NormalCoordinateFrame

/-!
# Ordered relative traces under a holomorphic normal-frame change

The two ordered relative traces are invariant under simultaneous Hermitian
pullback `Jᵀ g conj(J)` and `Jᵀ h conj(J)`. At the normal center they become
the sum of eigenvalues and the sum of their inverses, respectively. This
pointwise algebra does not differentiate the chart map or the trace.

Source: Székelyhidi, *An Introduction to Extremal Kähler Metrics*, §3.2,
Lemma 3.8, pp. 41–43; Yau (1978), §3.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

private theorem c3RefinedTrace_clm_equiv_of_matrix_det
    (L : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hdet : IsUnit (EuclideanSpace.clmMatrix L).det) :
    ∃ e : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n),
      e.toContinuousLinearMap = L := by
  let b : Module.Basis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)) :=
    (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
  let e : EuclideanSpace ℂ (Fin n) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
    Matrix.toLinearEquiv b (EuclideanSpace.clmMatrix L) hdet
  have hmatrix : LinearMap.toMatrix b b L.toLinearMap = EuclideanSpace.clmMatrix L := by
    ext i j
    simp [EuclideanSpace.clmMatrix, LinearMap.toMatrix_apply, b]
  have he : e.toLinearMap = L.toLinearMap := by
    apply (LinearMap.toMatrix b b).injective
    change LinearMap.toMatrix b b (Matrix.toLin b b (EuclideanSpace.clmMatrix L)) =
      LinearMap.toMatrix b b L.toLinearMap
    rw [LinearMap.toMatrix_toLin]
    exact hmatrix.symm
  refine ⟨e.toContinuousLinearEquiv, ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  exact congrArg (fun F : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) => F x) he

private theorem c3RefinedTrace_matrix_of_pullback
    (α β : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
    (hα : α.IsOneOne) (hβ : β.IsOneOne)
    (A : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n)) :
    ContinuousAlternatingMap.relTrace α β =
      RCLike.re (((α.compContinuousLinearMap
        ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)).coeffMatrix)⁻¹ *
        (β.compContinuousLinearMap
        ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)).coeffMatrix).trace := by
  rw [← ContinuousAlternatingMap.relTrace_compContinuousLinearMap hα hβ
    (A : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n))]
  rfl

/-- Both *ordered* traces agree with their normal-frame matrix traces. The
reverse trace must use `h⁻¹ g`, not `g⁻¹ h` again; this is the hypothesis
that supplies the lower eigenvalue bound in the energy comparison. -/
theorem c3RefinedTrace_normalFrame_orderedTraces
    (ω₀ : KahlerForm n M) (G φ : M → ℝ)
    (hsol : ω₀.SolvesMongeAmpere G φ) (x : M)
    (frame : C3RefinedTraceNormalCoordinateFrame ω₀ φ x) :
    let g := c3RefinedTracePulledReferenceMetric ω₀ x frame.coord
    let h := c3RefinedTracePulledPerturbedMetric ω₀ φ x frame.coord
    relTrace (ω₀ x) (ω₀ x + mddbar n φ x) =
      RCLike.re (((g frame.center)⁻¹ * h frame.center).trace) ∧
    relTrace (ω₀ x + mddbar n φ x) (ω₀ x) =
      RCLike.re (((h frame.center)⁻¹ * g frame.center).trace) := by
  let α := ω₀ x
  let β := (ω₀.perturb φ hsol.1) x
  let L := fderiv ℂ frame.coord frame.center
  have hdet : IsUnit (EuclideanSpace.clmMatrix L).det :=
    frame.jacobian_unit frame.center frame.center_mem
  obtain ⟨A, hA⟩ := c3RefinedTrace_clm_equiv_of_matrix_det L hdet
  have hJ : EuclideanSpace.clmMatrix (A : EuclideanSpace ℂ (Fin n) →L[ℂ]
      EuclideanSpace ℂ (Fin n)) = EuclideanSpace.clmMatrix L := by
    exact congrArg EuclideanSpace.clmMatrix hA
  have hz : extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x ∈
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by
    exact (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).map_source (by simp)
  have hα : α.IsOneOne := ω₀.isOneOne x
  have hβ : β.IsOneOne := (ω₀.perturb φ hsol.1).isOneOne x
  have hβcoeff : β.coeffMatrix =
      ω₀.metricInChart x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) +
        complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) := by
    rw [← KahlerForm.metricInChart_self (ω₀.perturb φ hsol.1) x,
      KahlerForm.metricInChart_perturb hsol.1 x hz]
  have hAg :
      (α.compContinuousLinearMap
        ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)).coeffMatrix =
        c3RefinedTracePulledReferenceMetric ω₀ x frame.coord frame.center := by
    rw [hα.coeffMatrix_compContinuousLinearMap]
    simp only [c3RefinedTracePulledReferenceMetric, L, hJ, frame.center_eq,
      KahlerForm.metricInChart_self]
    simp [α]
  have hBh :
      (β.compContinuousLinearMap
        ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)).coeffMatrix =
        c3RefinedTracePulledPerturbedMetric ω₀ φ x frame.coord frame.center := by
    rw [hβ.coeffMatrix_compContinuousLinearMap]
    simp only [c3RefinedTracePulledPerturbedMetric, L, hJ, frame.center_eq]
    rw [hβcoeff]
  have hfirst := c3RefinedTrace_matrix_of_pullback α β hα hβ A
  have hsecond := c3RefinedTrace_matrix_of_pullback β α hβ hα A
  constructor
  · change relTrace α β = _
    rw [hfirst, hAg, hBh]
  · change relTrace β α = _
    rw [hsecond, hBh, hAg]

end KahlerForm
