module
public import CalabiYau.Geometry.Manifold.DifferentialForm.Basic

/-!
# Locality of the exterior derivative at the support

Lee, *Introduction to Smooth Manifolds*, 2nd ed., §14 (exterior derivative
is a local operator), used in §16 to localize Stokes by chart-supported forms.
-/

@[expose] public section

open Set
open scoped Topology Manifold ContDiff

noncomputable section

namespace CalabiYau.DifferentialForm

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold IM ∞ M] [BoundarylessManifold IM M] {k : ℕ}

/-- Taking `d` cannot enlarge the closed support. This is a *locality*
statement, not an integral or Stokes statement. -/
theorem exteriorDerivative_closedSupport_subset (α : DifferentialForm IM M k) :
    closure {z : M | exteriorDerivative α z ≠ 0} ⊆
      closure {z : M | α z ≠ 0} := by
  apply closure_minimal ?_ isClosed_closure
  intro z hz
  change exteriorDerivative α z ≠ 0 at hz
  by_contra hnot
  let V : Set M := (closure {q : M | α q ≠ 0})ᶜ
  have hzV : z ∈ V := hnot
  have hV_open : IsOpen V := isOpen_compl_iff.mpr isClosed_closure
  have hV_nhds : V ∈ 𝓝 z := hV_open.mem_nhds hzV
  have hαzero : ∀ q : M, q ∈ V → α q = 0 := by
    intro q hq
    by_contra hne
    exact hq (subset_closure (show q ∈ {q : M | α q ≠ 0} from hne))
  let c := extChartAt IM z
  have hzsource : z ∈ c.source := by
    dsimp [c]
    exact mem_extChartAt_source z
  have hleft : c.symm (c z) = z := c.left_inv hzsource
  have hcont : ContinuousAt c.symm (c z) := by
    dsimp [c]
    exact continuousAt_extChartAt_symm' (I := IM) (M := M) (x := z) (x' := z) hzsource
  have hpre : c.symm ⁻¹' V ∈ 𝓝 (c z) := by
    have hV' : V ∈ 𝓝 (c.symm (c z)) := by simpa [hleft] using hV_nhds
    exact hcont.preimage_mem_nhds hV'
  have hchartInterior : c z ∈ interior c.target := by
    dsimp [c]
    exact (ModelWithCorners.isInteriorPoint_iff (I := IM)).1
      (BoundarylessManifold.isInteriorPoint (I := IM) (M := M) (x := z))
  have hinterior : interior c.target ∈ 𝓝 (c z) := isOpen_interior.mem_nhds hchartInterior
  let f : EM → EM [⋀^Fin k]→L[ℝ] ℝ := fun y =>
    (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
        (Bundle.Trivial M ℝ)) z ⟨c.symm y, α (c.symm y)⟩).2
  have hfzero : f =ᶠ[𝓝 (c z)] fun _ => 0 := by
    filter_upwards [Filter.inter_mem hpre hinterior] with y hy
    have hαy : α (c.symm y) = 0 := hαzero _ hy.1
    change (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
        (Bundle.Trivial M ℝ)) z ⟨c.symm y, α (c.symm y)⟩).2 = 0
    rw [continuousAlternatingMap_trivializationAt_apply]
    rw [hαy, ContinuousAlternatingMap.compContinuousLinearMap_zero]
  have hdf : extDeriv f (c z) = 0 := by
    rw [Filter.EventuallyEq.extDeriv_eq hfzero]
    simp [extDeriv]
    rw [← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply]
    exact map_zero _
  let e := trivializationAt (EM [⋀^Fin (k + 1)]→L[ℝ] ℝ)
    (Bundle.continuousAlternatingMap ℝ (Fin (k + 1)) EM (TangentSpace IM) ℝ
      (Bundle.Trivial M ℝ)) z
  have hb : z ∈ e.baseSet := mem_baseSet_trivializationAt (EM [⋀^Fin (k + 1)]→L[ℝ] ℝ)
    (Bundle.continuousAlternatingMap ℝ (Fin (k + 1)) EM (TangentSpace IM) ℝ
      (Bundle.Trivial M ℝ)) z
  have hlocal := exteriorDerivative_localRepresentation (IM := IM) (M := M) (α := α)
    (x₀ := z) (x := z) (by simp)
    (BoundarylessManifold.isInteriorPoint (I := IM) (M := M) (x := z))
  have hrep : (e.continuousLinearEquivAt ℝ z hb) (exteriorDerivative α z) =
      extDeriv f (c z) := by
    dsimp only [e, f, c, exteriorDerivative_apply, exteriorDerivativeAt]
    exact hlocal
  have htriv : (e.continuousLinearEquivAt ℝ z hb) (exteriorDerivative α z) = 0 :=
    hrep.trans hdf
  apply hz
  apply (e.continuousLinearEquivAt ℝ z hb).injective
  exact htriv.trans (map_zero (e.continuousLinearEquivAt ℝ z hb)).symm

end CalabiYau.DifferentialForm
