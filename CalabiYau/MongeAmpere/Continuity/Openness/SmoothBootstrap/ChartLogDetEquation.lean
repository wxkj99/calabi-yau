module

public import CalabiYau.MongeAmpere.Continuity.Openness.C2MassNormalization
public import CalabiYau.Geometry.Manifold.Holder.ChartNorm
public import CalabiYau.Analysis.Elliptic.Schauder

/-!
# The chartwise log-determinant equation

The first bootstrap input is the exact coordinate form of the Monge–Ampère equation, together
with positivity of its complex Hessian matrix.  This is the equation to which the difference
quotient argument in Gilbarg–Trudinger §6.4 applies.  Uniform Hölder coefficient bounds are a
separate input to the difference-quotient estimate.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology ComplexOrder MatrixOrder
open Matrix

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- The chartwise Monge–Ampère equation written as a log-determinant equation.  The matrix
`g + ∂∂̄φ` is Hermitian positive at every point; the displayed logarithmic identity is the
coordinate equation `log det(g + ∂∂̄φ) = G + log det(g)`. -/
def HasChartLogDetEquation (ω₀ : KahlerForm n M) (G φ : M → ℝ) : Prop :=
  ∀ x : M, ∀ z : EuclideanSpace ℂ (Fin n),
    z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target →
      let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
      let g := ω₀.metricInChart x z
      let B := g + complexHessian (φ ∘ e.symm) z
      B.IsHermitian ∧
        (∀ v : Fin n → ℂ, v ≠ 0 →
          0 < RCLike.re (star v ⬝ᵥ (B *ᵥ v))) ∧
        Real.log (RCLike.re B.det) = G (e.symm z) + Real.log (RCLike.re g.det)

private theorem chartRep_isPositive_of_pointwise
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (α : FormField (EuclideanSpace ℂ (Fin n)) M 2)
    (hα : ∀ x, (α x).IsPositive) (x : M) {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    (α.chartRep x z).IsPositive := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let y := e.symm z
  have hyx : y ∈ e.source := e.map_target hz
  have hyyℝ : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).source :=
    mem_extChartAt_source y
  have hyxℂ : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).source := by
    simpa only [← extChartAt_real_eq] using hyx
  have hyyℂ : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).source := by
    simpa only [← extChartAt_real_eq] using hyyℝ
  let A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y
  let B : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y x y
  have hBA : ∀ v, B (A v) = v := by
    intro v
    dsimp [A, B]
    calc
      tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y x y
          (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y v) =
          tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x x y v :=
        tangentCoordChange_comp (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
          (w := x) (x := y) (y := x) (z := y) (v := v)
          ⟨⟨hyxℂ, hyyℂ⟩, hyxℂ⟩
      _ = v := tangentCoordChange_self (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
        (x := x) (z := y) (v := v) hyxℂ
  have hAB : ∀ v, A (B v) = v := by
    intro v
    dsimp [A, B]
    calc
      tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y
          (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y x y v) =
          tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y y y v :=
        tangentCoordChange_comp (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
          (w := y) (x := x) (y := y) (z := y) (v := v)
          ⟨⟨hyyℂ, hyxℂ⟩, hyyℂ⟩
      _ = v := tangentCoordChange_self (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
        (x := y) (z := y) (v := v) hyyℂ
  let AEquiv : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n) :=
    { toLinearEquiv :=
        { toFun := A
          invFun := B
          left_inv := hBA
          right_inv := hAB
          map_add' := A.map_add
          map_smul' := A.map_smul }
      continuous_toFun := A.continuous
      continuous_invFun := B.continuous }
  have hAreal : tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y =
      (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ :=
    tangentCoordChange_real_eq ⟨hyx, hyyℝ⟩
  have hchart : α.chartRep x z =
      (α y).compContinuousLinearMap (A.restrictScalars ℝ) := by
    change (α y).compContinuousLinearMap
      (tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y) = _
    rw [hAreal]
  rw [hchart]
  exact (hα y).compContinuousLinearMap AEquiv

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in

/-- A finite-regularity Monge–Ampère solution gives the chartwise log-determinant equation and
its positive complex Hessian. -/
theorem solvesMongeAmpereC2_hasChartLogDetEquation
    (ω₀ : KahlerForm n M) (G φ : M → ℝ)
    (hφ : ω₀.SolvesMongeAmpereC2 G φ) :
    HasChartLogDetEquation ω₀ G φ := by
  intro x z hz
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let g := ω₀.metricInChart x z
  let B := g + complexHessian (φ ∘ e.symm) z
  have hzsource : e.symm z ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source := by
    have hyx : e.symm z ∈ e.source := e.symm.map_source hz
    simpa only [e, extChartAt_source] using hyx
  let α : FormField (EuclideanSpace ℂ (Fin n)) M 2 :=
    ω₀.toFormField + mddbar n φ
  have hchartpos := chartRep_isPositive_of_pointwise α hφ.1.2 x hz
  have hcoeff : (α.chartRep x z).coeffMatrix = B := by
    change ((ω₀.toFormField.chartRep x z + (mddbar n φ).chartRep x z).coeffMatrix) = _
    rw [ContinuousAlternatingMap.coeffMatrix_add,
      chartRep_mddbar_of_contMDiff_two hφ.1.1 x hz]
    rfl
  have hpos : B.PosDef := by
    rw [← hcoeff]
    exact (ContinuousAlternatingMap.isPositive_iff.mp hchartpos).2
  have hbasepos : g.PosDef := ω₀.posDef_metricInChart x hz
  have hma := mongeAmpere_eq_inChart_of_contMDiff_two (ω₀ := ω₀) hφ.1.1 x hzsource
  have heval : e (e.symm z) = z := e.right_inv hz
  rw [heval] at hma
  have hratio : RCLike.re B.det / RCLike.re g.det = Real.exp (G (e.symm z)) := by
    have hm := hma.symm.trans (hφ.2 (e.symm z))
    simpa [B, g, e] using hm
  have hBdet : 0 < RCLike.re B.det :=
    (RCLike.pos_iff.mp hpos.det_pos).1
  have hgdet : 0 < RCLike.re g.det :=
    (RCLike.pos_iff.mp hbasepos.det_pos).1
  refine ⟨hpos.isHermitian, ?_, ?_⟩
  · intro v hv
    have hquad := (Matrix.posDef_iff_dotProduct_mulVec.mp hpos).2 hv
    exact (RCLike.pos_iff.mp hquad).1
  · change Real.log (RCLike.re B.det) = G (e.symm z) + Real.log (RCLike.re g.det)
    have hlog : Real.log (RCLike.re B.det / RCLike.re g.det) = G (e.symm z) := by
      rw [hratio, Real.log_exp]
    rw [Real.log_div (ne_of_gt hBdet) (ne_of_gt hgdet)] at hlog
    linarith

end KahlerForm
