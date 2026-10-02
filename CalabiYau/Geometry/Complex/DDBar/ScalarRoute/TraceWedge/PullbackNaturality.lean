module

public import CalabiYau.Geometry.Complex.DDBar.ScalarRoute.TraceWedge.WedgePowers
import CalabiYau.Geometry.Manifold.DifferentialForm.Model

/-!
# Pullback naturality for exterior powers and mixed wedges

Pullback commutes with exterior multiplication and the degree-zero exterior
unit. These identities let diagonal trace–wedge formulas transport to arbitrary
complex-linear frames.

Source: Bott–Tu, *Differential Forms in Algebraic Topology*, Chapter I, §§1–2,
pp. 14 and 19; the continuous alternating-map bridge is in
`CalabiYau.Geometry.Manifold.DifferentialForm.Model`.
-/

@[expose] public section

namespace ContinuousAlternatingMap

/-- Pullback commutes with all unnormalized exterior powers of a real two-form. -/
theorem wedgePow_pullback {n : ℕ}
    (ω : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
    (A : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n)) (k : ℕ) :
    (wedgePow ω k).compContinuousLinearMap
      (A.toContinuousLinearMap.restrictScalars ℝ) =
      wedgePow (ω.compContinuousLinearMap
        (A.toContinuousLinearMap.restrictScalars ℝ)) k := by
  induction k with
  | zero => exact CalabiYau.DifferentialForm.constOfIsEmpty_compContinuousLinearMap 1 _
  | succ k ih =>
      simp only [wedgePow,
        CalabiYau.DifferentialForm.domDomCongr_compContinuousLinearMap,
        CalabiYau.DifferentialForm.wedge_product_compContinuousLinearMap, ih]

/-- Pullback commutes with the mixed wedge `α ∧ ω^(n-1)` in positive dimension. -/
theorem mixedWedge_pullback {n : ℕ} (hn : 0 < n)
    (α ω : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
    (A : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n)) :
    (mixedWedgeOfPos hn α ω).compContinuousLinearMap
      (A.toContinuousLinearMap.restrictScalars ℝ) =
      mixedWedgeOfPos hn
        (α.compContinuousLinearMap (A.toContinuousLinearMap.restrictScalars ℝ))
        (ω.compContinuousLinearMap (A.toContinuousLinearMap.restrictScalars ℝ)) := by
  simp only [mixedWedgeOfPos,
    CalabiYau.DifferentialForm.domDomCongr_compContinuousLinearMap,
    CalabiYau.DifferentialForm.wedge_product_compContinuousLinearMap,
    wedgePow_pullback]

end ContinuousAlternatingMap

end
