module
public import CalabiYau.Geometry.Manifold.DifferentialForm.Stokes.Assembly.ChartRepresentation

/-!
# Coordinate representation commutes with exterior differentiation

Lee, *Introduction to Smooth Manifolds*, 2nd ed., §§14, 16: naturality of
`d` under a chart pullback, followed by zero extension for chart-supported
forms. The chart coefficient is exactly the one used by the project's
`DifferentialForm.exteriorDerivative_localRepresentation`.
-/

@[expose] public section

open Set
open scoped Topology Manifold ContDiff

noncomputable section

namespace CalabiYau.DifferentialForm

variable {n k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (Fin (n + 1) → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin (n + 1) → ℝ) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, Fin (n + 1) → ℝ) M]

/-- `d` commutes with zero-extended chart representation when the *compact
closed* support of the form lies inside the chart. On the chart target this
is `exteriorDerivative_localRepresentation`; off the chart target compactness
keeps the support away from the chart boundary, so both sides vanish in a
neighborhood, not merely at the point. Without compactness this is false. -/
theorem stokesChartRepresentation_exteriorDerivative
    (α : DifferentialForm 𝓘(ℝ, Fin (n + 1) → ℝ) M k) (x : M)
    (hα : closure {z : M | α z ≠ 0} ⊆
      (chartAt (Fin (n + 1) → ℝ) x).source)
    (hcompact : IsCompact (closure {z : M | α z ≠ 0})) :
    stokesChartRepresentation (exteriorDerivative α) x =
      fun y => extDeriv (stokesChartRepresentation α x) y := by
  funext y
  by_cases hy : y ∈ (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x).target
  · let z := (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x).symm y
    have hz : z ∈ (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x).source := by
      exact (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x).map_target hy
    have hzint : (𝓘(ℝ, Fin (n + 1) → ℝ)).IsInteriorPoint z :=
      BoundarylessManifold.isInteriorPoint (I := 𝓘(ℝ, Fin (n + 1) → ℝ)) (M := M) (x := z)
    have hlocal := DifferentialForm.exteriorDerivative_localRepresentation
      (IM := 𝓘(ℝ, Fin (n + 1) → ℝ)) (M := M) α
      (x₀ := x) (x := z) hz hzint
    have hcoord : (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x) z = y := by
      dsimp [z]
      exact (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x).right_inv hy
    have hrepEq : (fun q : Fin (n + 1) → ℝ =>
        (trivializationAt ((Fin (n + 1) → ℝ) [⋀^Fin k]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin k) (Fin (n + 1) → ℝ)
            (TangentSpace 𝓘(ℝ, Fin (n + 1) → ℝ)) ℝ (Bundle.Trivial M ℝ)) x
          ⟨(extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x).symm q,
            α ((extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x).symm q)⟩).2) =ᶠ[𝓝 y]
        stokesChartRepresentation α x := by
      filter_upwards [(isOpen_extChartAt_target
        (I := 𝓘(ℝ, Fin (n + 1) → ℝ)) x).mem_nhds hy] with q hq
      rw [stokesChartRepresentation, ite_eq_left hq]
    rw [hcoord, Filter.EventuallyEq.extDeriv_eq hrepEq] at hlocal
    rw [stokesChartRepresentation, ite_eq_left hy]
    exact hlocal
  · let S : Set M := closure {z : M | α z ≠ 0}
    let e := chartAt (Fin (n + 1) → ℝ) x
    let K : Set (Fin (n + 1) → ℝ) := e '' S
    have hSsource : S ⊆ e.source := by
      simpa [S, e] using hα
    have hKcompact : IsCompact K := by
      dsimp [K, e]
      exact hcompact.image_of_continuousOn
        ((chartAt (Fin (n + 1) → ℝ) x).continuousOn_toFun.mono hSsource)
    have hKtarget : K ⊆ (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x).target := by
      rintro q ⟨z, hz, rfl⟩
      simpa [extChartAt_target] using e.map_source (hSsource hz)
    have hyK : y ∉ K := by
      intro hyK
      exact hy (hKtarget hyK)
    have hKclosed : IsClosed K := hKcompact.isClosed
    have hzero : ∀ q, q ∉ K → stokesChartRepresentation α x q = 0 := by
      intro q hq
      by_cases hqt : q ∈ (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x).target
      · have hqtChart : q ∈ (chartAt (Fin (n + 1) → ℝ) x).target := by
          simpa [extChartAt_target] using hqt
        have hαzero : α ((chartAt (Fin (n + 1) → ℝ) x).symm q) = 0 := by
          by_contra hn
          apply hq
          refine ⟨(chartAt (Fin (n + 1) → ℝ) x).symm q,
            subset_closure hn, ?_⟩
          exact (chartAt (Fin (n + 1) → ℝ) x).right_inv hqtChart
        rw [stokesChartRepresentation, ite_eq_left hqt]
        let tr := trivializationAt ((Fin (n + 1) → ℝ) [⋀^Fin k]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin k) (Fin (n + 1) → ℝ)
            (TangentSpace 𝓘(ℝ, Fin (n + 1) → ℝ)) ℝ (Bundle.Trivial M ℝ)) x
        have hbase : (chartAt (Fin (n + 1) → ℝ) x).symm q ∈ tr.baseSet := by
          rw [FiberBundle.trivializationAt_continuousAlternatingMap_baseSet,
            TangentBundle.trivializationAt_baseSet]
          simp [hqtChart]
        change (tr ⟨(chartAt (Fin (n + 1) → ℝ) x).symm q,
          α ((chartAt (Fin (n + 1) → ℝ) x).symm q)⟩).2 = 0
        rw [← congrFun (tr.coe_linearMapAt_of_mem (R := ℝ) hbase)
          (α ((chartAt (Fin (n + 1) → ℝ) x).symm q)), hαzero]
        exact map_zero _
      · rw [stokesChartRepresentation, ite_eq_right hqt]
    have hneigh : Kᶜ ∈ 𝓝 y := hKclosed.isOpen_compl.mem_nhds hyK
    have hrepZero : (stokesChartRepresentation α x) =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [hneigh] with q hq
      exact hzero q hq
    have hderivZero : extDeriv (stokesChartRepresentation α x) y = 0 := by
      rw [Filter.EventuallyEq.extDeriv_eq hrepZero]
      change ContinuousAlternatingMap.alternatizeUncurryFin
        (fderiv ℝ (fun _ : Fin (n + 1) → ℝ => (0 : (Fin (n + 1) → ℝ) [⋀^Fin k]→L[ℝ] ℝ)) y) = 0
      rw [fderiv_const_apply 0]
      rw [← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply]
      exact map_zero _
    have hleftZero : stokesChartRepresentation (exteriorDerivative α) x y = 0 := by
      rw [stokesChartRepresentation, ite_eq_right hy]
    rw [hleftZero, hderivZero]

end CalabiYau.DifferentialForm
