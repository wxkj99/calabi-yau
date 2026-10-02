module
public import CalabiYau.Geometry.Manifold.DifferentialForm.Stokes.Integral.ChartCoefficient
public import CalabiYau.Geometry.Manifold.DifferentialForm.Stokes.ChartTransition.TopCoefficient

/-!
# Signed coefficients of actual top forms on a chart overlap

Lee, *Introduction to Smooth Manifolds*, 2nd ed., Proposition 14.9,
equation (14.2), p. 354; Proposition 14.20, equation (14.15), pp. 361–362;
and Corollary 14.21, equation (14.16), p. 362. This is the coefficient
pullback used in Proposition 16.4, pp. 404–405. Proposition 16.5,
pp. 405–406, subsequently uses chart independence for partition independence;
neither global integration nor partition independence is asserted here.

The coordinate model is `Fin n → ℝ`, including dimension zero. Both
coefficients come from the actual alternating-map bundle trivialization.
The determinant is signed and in the direction from chart `a` to chart `b`.
No compactness, connectedness, support, or orientation hypothesis is needed.
-/

@[expose] public section

open Set
open scoped Topology Manifold ContDiff

noncomputable section

namespace CalabiYau.DifferentialForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]

/-- The signed coefficient of an actual top form transforms by the determinant
of the tangent coordinate change, at every point of the overlap. In dimension
zero the determinant is `1` and evaluation uses the empty family. -/
theorem chartTopCoefficient_transition
    (η : DifferentialForm 𝓘(ℝ, Fin n → ℝ) M n)
    (a b z : M)
    (ha : z ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) a).source)
    (hb : z ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) b).source) :
    chartTopCoefficient a η
        ((extChartAt 𝓘(ℝ, Fin n → ℝ) a) z) =
      (tangentCoordChange 𝓘(ℝ, Fin n → ℝ) a b z).det *
        chartTopCoefficient b η
          ((extChartAt 𝓘(ℝ, Fin n → ℝ) b) z) := by
  classical
  unfold chartTopCoefficient
  rw [if_pos ((extChartAt 𝓘(ℝ, Fin n → ℝ) a).map_source ha),
    if_pos ((extChartAt 𝓘(ℝ, Fin n → ℝ) b).map_source hb),
    (extChartAt 𝓘(ℝ, Fin n → ℝ) a).left_inv ha,
    (extChartAt 𝓘(ℝ, Fin n → ℝ) b).left_inv hb]
  rw [continuousAlternatingMap_trivializationAt_apply,
    continuousAlternatingMap_trivializationAt_apply]
  have hrep :
      (η z).compContinuousLinearMap
          ((trivializationAt (Fin n → ℝ)
            (TangentSpace 𝓘(ℝ, Fin n → ℝ)) a).symmL ℝ z) =
        ((η z).compContinuousLinearMap
          ((trivializationAt (Fin n → ℝ)
            (TangentSpace 𝓘(ℝ, Fin n → ℝ)) b).symmL ℝ z)).compContinuousLinearMap
          (tangentCoordChange 𝓘(ℝ, Fin n → ℝ) a b z) := by
    ext v
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
    apply congrArg (η z)
    funext i
    exact (CalabiYau.symmL_coordChange ha hb (v i)).symm
  rw [hrep]
  exact ContinuousAlternatingMap.compContinuousLinearMap_apply_standardBasis _ _

/-- The same transition law with the actual coordinate Jacobian. The
coefficient in chart `b` is evaluated at the transition image, not at `y`.
The two domain hypotheses justify the coordinate inverse and overlap. -/
theorem chartTopCoefficient_transition_fderiv
    (η : DifferentialForm 𝓘(ℝ, Fin n → ℝ) M n)
    (a b : M) (y : Fin n → ℝ)
    (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) a).target)
    (hb : (extChartAt 𝓘(ℝ, Fin n → ℝ) a).symm y ∈
      (extChartAt 𝓘(ℝ, Fin n → ℝ) b).source) :
    chartTopCoefficient a η y =
      (fderiv ℝ
        ((extChartAt 𝓘(ℝ, Fin n → ℝ) b) ∘
          (extChartAt 𝓘(ℝ, Fin n → ℝ) a).symm) y).det *
        chartTopCoefficient b η
          ((extChartAt 𝓘(ℝ, Fin n → ℝ) b)
            ((extChartAt 𝓘(ℝ, Fin n → ℝ) a).symm y)) := by
  have h := chartTopCoefficient_transition η a b
    ((extChartAt 𝓘(ℝ, Fin n → ℝ) a).symm y)
    ((extChartAt 𝓘(ℝ, Fin n → ℝ) a).map_target hy) hb
  have hderiv :
      tangentCoordChange 𝓘(ℝ, Fin n → ℝ) a b
        ((extChartAt 𝓘(ℝ, Fin n → ℝ) a).symm y) =
      fderiv ℝ
        ((extChartAt 𝓘(ℝ, Fin n → ℝ) b) ∘
          (extChartAt 𝓘(ℝ, Fin n → ℝ) a).symm) y := by
    rw [tangentCoordChange_def,
      (𝓘(ℝ, Fin n → ℝ)).range_eq_univ, fderivWithin_univ,
      (extChartAt 𝓘(ℝ, Fin n → ℝ) a).right_inv hy]
  rw [hderiv,
    (extChartAt 𝓘(ℝ, Fin n → ℝ) a).right_inv hy] at h
  exact h

end CalabiYau.DifferentialForm
