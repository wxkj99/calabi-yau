module
public import CalabiYau.Geometry.Manifold.DifferentialForm.Stokes.Integral.ChartCoefficient
public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Integrability of chart coefficients supported away from the chart boundary

Lee, *Introduction to Smooth Manifolds*, 2nd ed., §16, definition of the
integral of a compactly supported top form in one coordinate chart. A closed
support inside the chart yields a compactly supported continuous coefficient
after extension by zero. In dimension zero the chart image is finite, not an
empty Lebesgue domain.
-/

@[expose] public section

open MeasureTheory Set
open scoped Topology Manifold ContDiff

namespace CalabiYau.DifferentialForm

/-- The zero extension of a function continuous on an open neighborhood of a
closed set is continuous when the function vanishes on the frontier. -/
private theorem continuous_indicator_of_closed_of_frontier_zero
    {E : Type*} [TopologicalSpace E]
    (K U : Set E) (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U)
    (f : E → ℝ) (hf : ContinuousOn f U)
    (hzero : ∀ x ∈ frontier K, f x = 0) :
    Continuous (K.indicator f) := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hxK : x ∈ K
  · by_cases hxI : x ∈ interior K
    · have hEq : K.indicator f =ᶠ[𝓝 x] f := by
        filter_upwards [(isOpen_interior.mem_nhds hxI)] with y hy
        simp [Set.indicator, interior_subset hy]
      have hxU : x ∈ U := hKU (interior_subset hxI)
      have hxval : K.indicator f x = f x := by simp [Set.indicator, hxK]
      change Filter.Tendsto (K.indicator f) (𝓝 x) (𝓝 (K.indicator f x))
      rw [hxval]
      exact (hf.continuousAt (hU.mem_nhds hxU)).congr' hEq.symm
    · have hxU : x ∈ U := hKU hxK
      have hfront : x ∈ frontier K := by
        rw [frontier, hK.closure_eq]
        exact ⟨hxK, hxI⟩
      have hfx : f x = 0 := hzero x hfront
      have hfc : ContinuousAt f x := hf.continuousAt (hU.mem_nhds hxU)
      have hxval : K.indicator f x = 0 := by
        simp [Set.indicator, hxK, hfx]
      change Filter.Tendsto (K.indicator f) (𝓝 x) (𝓝 (K.indicator f x))
      rw [hxval]
      rw [Filter.tendsto_def]
      intro s hs
      have hsfx : s ∈ 𝓝 (f x) := by simpa [hfx] using hs
      have hfnear : f ⁻¹' s ∈ 𝓝 x := hfc.preimage_mem_nhds hsfx
      filter_upwards [hfnear] with y hy
      by_cases hyK : y ∈ K
      · simpa [Set.indicator, hyK] using hy
      · have h0s : (0 : ℝ) ∈ s := mem_of_mem_nhds hs
        simpa [Set.indicator, hyK] using h0s
  · have hEq : K.indicator f =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [hK.isOpen_compl.mem_nhds hxK] with y hy
      have hnot : y ∉ K := hy
      simp [Set.indicator, hnot]
    have hxval : K.indicator f x = 0 := by simp [Set.indicator, hxK]
    change Filter.Tendsto (K.indicator f) (𝓝 x) (𝓝 (K.indicator f x))
    rw [hxval]
    exact (continuousAt_const : ContinuousAt (fun _ : E => (0 : ℝ)) x).congr' hEq.symm

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold (𝓘(ℝ, Fin n → ℝ)) ∞ M]

private theorem integrable_indicator_of_isCompact_continuousOn
    (K : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (hK : IsCompact K) (hf : ContinuousOn f K) :
    Integrable (K.indicator f) (volume : Measure (Fin n → ℝ)) := by
  exact (integrable_indicator_iff hK.measurableSet).2 (hf.integrableOn_compact hK)

private theorem chartTopCoefficient_eq_chartImageIndicator (x : M)
    (η : DifferentialForm (𝓘(ℝ, Fin n → ℝ)) M n)
    (hη : closure {z : M | η z ≠ 0} ⊆
      (extChartAt (𝓘(ℝ, Fin n → ℝ)) x).source) :
    chartTopCoefficient x η =
      (extChartAt (𝓘(ℝ, Fin n → ℝ)) x '' closure {z : M | η z ≠ 0}).indicator
        (fun y : Fin n → ℝ =>
          (trivializationAt ((Fin n → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
            (Bundle.continuousAlternatingMap ℝ (Fin n) (Fin n → ℝ)
              (TangentSpace (𝓘(ℝ, Fin n → ℝ))) ℝ (Bundle.Trivial M ℝ)) x
            ⟨(extChartAt (𝓘(ℝ, Fin n → ℝ)) x).symm y,
              η ((extChartAt (𝓘(ℝ, Fin n → ℝ)) x).symm y)⟩).2
            (fun i : Fin n => Pi.single i (1 : ℝ))) := by
  classical
  let c := extChartAt (𝓘(ℝ, Fin n → ℝ)) x
  let K : Set (Fin n → ℝ) := c '' closure {z : M | η z ≠ 0}
  let rep : (Fin n → ℝ) → ℝ := fun y =>
    (trivializationAt ((Fin n → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin n) (Fin n → ℝ)
        (TangentSpace (𝓘(ℝ, Fin n → ℝ))) ℝ (Bundle.Trivial M ℝ)) x
      ⟨c.symm y, η (c.symm y)⟩).2
      (fun i : Fin n => Pi.single i (1 : ℝ))
  funext y
  change chartTopCoefficient x η y = K.indicator rep y
  by_cases hy : y ∈ K
  · obtain ⟨z, hz, rfl⟩ := hy
    have hzsource : z ∈ c.source := hη hz
    have hztarget : c z ∈ c.target := c.map_source hzsource
    have hcoeff : chartTopCoefficient x η (c z) = rep (c z) := by
      unfold chartTopCoefficient
      rw [ite_eq_left hztarget]
    rw [hcoeff]
    change rep (c z) = if c z ∈ K then rep (c z) else 0
    rw [ite_eq_left (show c z ∈ K from ⟨z, hz, rfl⟩)]
  · have hzero : chartTopCoefficient x η y = 0 := by
      by_cases hy' : y ∈ c.target
      · have hnot : c.symm y ∉ closure {z : M | η z ≠ 0} := by
          intro hc
          apply hy
          exact ⟨c.symm y, hc, c.right_inv hy'⟩
        have hηzero : η (c.symm y) = 0 := by
          by_contra hn
          apply hnot
          exact subset_closure (show c.symm y ∈ {z : M | η z ≠ 0} from hn)
        have hcoeff : chartTopCoefficient x η y = 0 := by
          unfold chartTopCoefficient
          rw [ite_eq_left hy']
          change (trivializationAt ((Fin n → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
            (Bundle.continuousAlternatingMap ℝ (Fin n) (Fin n → ℝ)
              (TangentSpace (𝓘(ℝ, Fin n → ℝ))) ℝ (Bundle.Trivial M ℝ)) x
            ⟨c.symm y, η (c.symm y)⟩).2
            (fun i : Fin n => Pi.single i (1 : ℝ)) = 0
          rw [hηzero]
          rw [CalabiYau.continuousAlternatingMap_trivializationAt_apply
            (m := n) (IM := 𝓘(ℝ, Fin n → ℝ)) (M := M) (x₀ := x)
            (x := c.symm y) (L := (0 : Bundle.continuousAlternatingMap ℝ (Fin n)
              (Fin n → ℝ) (TangentSpace (𝓘(ℝ, Fin n → ℝ))) ℝ
              (Bundle.Trivial M ℝ) (c.symm y)))]
          simp
        exact hcoeff
      · unfold chartTopCoefficient
        rw [ite_eq_right hy']
    simp [hzero, hy]


variable [CompactSpace M] in
/-- A top form whose *closed* nonzero support lies inside this chart has an
integrable signed coordinate coefficient, extended by zero to all of ℝⁿ.
Compactness of `M` and continuity of `η` preclude spurious nonintegrability;
`support ⊆ chart.source` without the closure would not suffice. -/
theorem integrable_chartTopCoefficient (x : M)
    (η : DifferentialForm (𝓘(ℝ, Fin n → ℝ)) M n)
    (hη : closure {z : M | η z ≠ 0} ⊆
      (extChartAt (𝓘(ℝ, Fin n → ℝ)) x).source) :
    Integrable (chartTopCoefficient x η)
      (volume : Measure (Fin n → ℝ)) := by
  classical
  let c := extChartAt (𝓘(ℝ, Fin n → ℝ)) x
  let K : Set (Fin n → ℝ) := c '' closure {z : M | η z ≠ 0}
  let rep : (Fin n → ℝ) → ℝ := fun y =>
    (trivializationAt ((Fin n → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin n) (Fin n → ℝ)
        (TangentSpace (𝓘(ℝ, Fin n → ℝ))) ℝ (Bundle.Trivial M ℝ)) x
      ⟨c.symm y, η (c.symm y)⟩).2
      (fun i : Fin n => Pi.single i (1 : ℝ))
  have hKcompact : IsCompact K := by
    dsimp [K, c]
    exact (isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _)).image_of_continuousOn
      ((continuousOn_extChartAt (I := 𝓘(ℝ, Fin n → ℝ)) x).mono hη)
  have hKtarget : K ⊆ c.target := by
    rintro y ⟨z, hz, rfl⟩
    exact c.map_source (hη hz)
  have hrepcont : ContinuousOn rep K := by
    have hlocal := localRep_contDiffOn (IM := 𝓘(ℝ, Fin n → ℝ)) (M := M) η x
    have hlocalcont : ContinuousOn (fun y : Fin n → ℝ =>
        (trivializationAt ((Fin n → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin n) (Fin n → ℝ)
            (TangentSpace (𝓘(ℝ, Fin n → ℝ))) ℝ (Bundle.Trivial M ℝ)) x
          ⟨c.symm y, η (c.symm y)⟩).2) c.target := hlocal.continuousOn
    have heval := (ContinuousAlternatingMap.apply ℝ (Fin n → ℝ) ℝ
      (fun i : Fin n => Pi.single i (1 : ℝ))).continuous
    have hlocScalar : ContinuousOn (fun y : Fin n → ℝ =>
        (trivializationAt ((Fin n → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin n) (Fin n → ℝ)
            (TangentSpace (𝓘(ℝ, Fin n → ℝ))) ℝ (Bundle.Trivial M ℝ)) x
          ⟨c.symm y, η (c.symm y)⟩).2
          (fun i : Fin n => Pi.single i (1 : ℝ))) c.target := by
      exact heval.comp_continuousOn hlocalcont
    change ContinuousOn (fun y : Fin n → ℝ =>
      (trivializationAt ((Fin n → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin n) (Fin n → ℝ)
          (TangentSpace (𝓘(ℝ, Fin n → ℝ))) ℝ (Bundle.Trivial M ℝ)) x
        ⟨c.symm y, η (c.symm y)⟩).2
        (fun i : Fin n => Pi.single i (1 : ℝ))) K
    exact hlocScalar.mono hKtarget
  have hEq := chartTopCoefficient_eq_chartImageIndicator x η hη
  change chartTopCoefficient x η = K.indicator rep at hEq
  rw [hEq]
  exact integrable_indicator_of_isCompact_continuousOn K rep hKcompact hrepcont

end CalabiYau.DifferentialForm
