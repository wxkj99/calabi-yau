module

public import CalabiYau.Geometry.Complex.DDBar.ScalarPotential.TopFormIntegral.NativeModel
public import CalabiYau.Geometry.Manifold.DifferentialForm.Stokes.Integral.ChartCoefficient

/-!
# Fixed-centre coefficients in the canonical native-to-Pi atlas

Morita, Geometry of Differential Forms, section 3.2(a), pp. 104-107; Lee,
Introduction to Smooth Manifolds, second edition, Chapters 1-2 and 14.
This is the exact checked AEC coordinate/frame proof, using only real smooth
geometry. The chart target guard and inverse-chart point are retained.
No Kahler form, complex-analytic manifold, measure, determinant expansion,
Stokes, arbitrary transport, or second charted-space structure is assumed.
The existing frozen public NativeModel is imported unchanged.
-/

@[expose] public section

set_option maxRecDepth 4096

open scoped Manifold ContDiff
open MeasureTheory ContinuousAlternatingMap CalabiYau.DifferentialForm HTopFormVolumeBridge

noncomputable section

namespace HTopFormVolumeBridge

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ M]

private theorem hTopPiToComplexEquiv_stdBasis {n : ℕ} (i : Fin (2 * n)) :
    HTopFormVolumeBridge.hTopPiToComplexEquiv n
      (Pi.single i (1 : ℝ) : Fin (2 * n) → ℝ) =
        ContinuousAlternatingMap.complexInterleavedBasis n i := by
  classical
  let p := (HTopFormVolumeBridge.hTopFrameIndex n).symm i
  have hp : HTopFormVolumeBridge.hTopFrameIndex n p = i :=
    Equiv.apply_symm_apply _ i
  have hr : complexToRealCoordinateEquiv
      (ContinuousAlternatingMap.complexInterleavedBasis n
        (HTopFormVolumeBridge.hTopFrameIndex n p)) =
      EuclideanSpace.basisFun (Fin n × Fin 2) ℝ p := by
    simpa [HTopFormVolumeBridge.hTopFrameIndex] using
      HTopFormVolumeBridge.realification_interleaved_basis_image p
  apply (complexToRealCoordinateEquiv (n := n)).injective
  rw [← hp, hr]
  simp [HTopFormVolumeBridge.hTopPiToComplexEquiv,
    HTopFormVolumeBridge.hTopPiToRealEquiv,
    HTopFormVolumeBridge.hTopFrameIndex,
    LinearEquiv.piCongrLeft]
  ext q
  change Pi.single (M := fun _ : Fin (2 * n) => ℝ)
      (HTopFormVolumeBridge.hTopFrameIndex n p) 1
    (HTopFormVolumeBridge.hTopFrameIndex n q) = _
  simp only [Pi.single_apply, Equiv.apply_eq_iff_eq]
  by_cases h : p = q
  · subst q
    simp
  · have h' : q ≠ p := by simpa [eq_comm] using h
    simp [h']

private theorem hTopPiPullback_topFormCoeff {n : ℕ}
    (α : EuclideanSpace ℂ (Fin n) [⋀^Fin (2 * n)]→L[ℝ] ℝ) :
    (α.compContinuousLinearMap (HTopFormVolumeBridge.hTopPiToComplexEquiv n))
        (fun i : Fin (2 * n) => Pi.single i (1 : ℝ)) =
      ContinuousAlternatingMap.topFormCoeff α := by
  unfold ContinuousAlternatingMap.topFormCoeff
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  exact hTopPiToComplexEquiv_stdBasis i

private theorem nativePi_extChartAt {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M] (c : M) :
    letI := nativePiCharts (n := n) (M := M)
    extChartAt 𝓘(ℝ, Fin (2 * n) → ℝ) c =
      ((chartAt (EuclideanSpace ℂ (Fin n)) c).trans
        (hTopPiToComplexEquiv n).symm.toHomeomorph.toOpenPartialHomeomorph).toPartialEquiv := by
  let p := (hTopPiToComplexEquiv n).symm.toHomeomorph.toOpenPartialHomeomorph
  let hp : p.source = Set.univ := by simp [p]
  let : ChartedSpace (Fin (2 * n) → ℝ) (EuclideanSpace ℂ (Fin n)) :=
    p.singletonChartedSpace hp
  let : ChartedSpace (Fin (2 * n) → ℝ) M := nativePiCharts
  rw [extChartAt_comp]
  simp [extChartAt]

private theorem nativePi_tangentCoordChange {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ M]
    (c y : M) (hy : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) c).source) :
    letI := nativePiCharts (n := n) (M := M)
    letI : IsManifold 𝓘(ℝ, Fin (2 * n) → ℝ) ∞ M := nativePiIsManifold
    (hTopPiToComplexEquiv n).toContinuousLinearMap.comp
        (tangentCoordChange 𝓘(ℝ, Fin (2 * n) → ℝ) c y y) =
      (tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) c y y).comp
        (hTopPiToComplexEquiv n).toContinuousLinearMap := by
  let : ChartedSpace (Fin (2 * n) → ℝ) M := nativePiCharts
  let : IsManifold 𝓘(ℝ, Fin (2 * n) → ℝ) ∞ M := nativePiIsManifold
  rw [tangentCoordChange_def, tangentCoordChange_def]
  rw [nativePi_extChartAt (n := n) (M := M) c,
    nativePi_extChartAt (n := n) (M := M) y]
  simp [Function.comp_def]
  let e := hTopPiToComplexEquiv n
  let x₀ := chartAt (EuclideanSpace ℂ (Fin n)) c y
  let g : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) := fun z =>
    chartAt (EuclideanSpace ℂ (Fin n)) y
      ((chartAt (EuclideanSpace ℂ (Fin n)) c).symm z)
  have hchartY : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ (chartAt (EuclideanSpace ℂ (Fin n)) y) y :=
    (contMDiffOn_chart (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (x := y)).contMDiffAt
      ((chartAt (EuclideanSpace ℂ (Fin n)) y).open_source.mem_nhds (by simp))
  have hchartCsymm : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ (chartAt (EuclideanSpace ℂ (Fin n)) c).symm x₀ :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (x := c)).contMDiffAt
      ((chartAt (EuclideanSpace ℂ (Fin n)) c).open_target.mem_nhds
        ((chartAt (EuclideanSpace ℂ (Fin n)) c).map_source hy))
  have hleft : (chartAt (EuclideanSpace ℂ (Fin n)) c).symm x₀ = y :=
    (chartAt (EuclideanSpace ℂ (Fin n)) c).left_inv hy
  have hgCont : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ g x₀ := by
    simpa [g, Function.comp_def] using hchartY.comp_of_eq hchartCsymm hleft
  have hgDiff : DifferentiableAt ℝ g x₀ :=
    hgCont.contDiffAt.differentiableAt (by simp)
  have hgeDiff : DifferentiableAt ℝ (g ∘ e) (e.symm x₀) := by
    have hge0 : DifferentiableAt ℝ g (e (e.symm x₀)) := by
      rw [e.apply_symm_apply]
      exact hgDiff
    exact hge0.comp (e.symm x₀) e.differentiableAt
  change e.toContinuousLinearMap.comp
      (fderiv ℝ (e.symm ∘ (g ∘ e)) (e.symm x₀)) =
    (fderiv ℝ g x₀).comp e.toContinuousLinearMap
  calc
    e.toContinuousLinearMap.comp
        (fderiv ℝ (e.symm ∘ (g ∘ e)) (e.symm x₀)) =
      e.toContinuousLinearMap.comp
        ((e.symm.toContinuousLinearMap).comp
          (fderiv ℝ (g ∘ e) (e.symm x₀))) := by
            rw [e.symm.comp_fderiv]
    _ = e.toContinuousLinearMap.comp
        ((e.symm.toContinuousLinearMap).comp
          ((fderiv ℝ g (e (e.symm x₀))).comp e.toContinuousLinearMap)) := by
            rw [e.comp_right_fderiv]
    _ = (fderiv ℝ g x₀).comp e.toContinuousLinearMap := by
            ext v
            simp [ContinuousLinearMap.comp_apply, e.apply_symm_apply]

private theorem nativePi_target_to_native {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M] (c : M)
    {z : Fin (2 * n) → ℝ}
    (hz : z ∈ letI := nativePiCharts (n := n) (M := M)
      (extChartAt 𝓘(ℝ, Fin (2 * n) → ℝ) c).target) :
    hTopPiToComplexEquiv n z ∈
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) c).target := by
  let e := hTopPiToComplexEquiv n
  let p := e.symm.toHomeomorph.toOpenPartialHomeomorph
  have hp : p.source = Set.univ := by simp [p]
  have hzPi : z ∈ ((chartAt (EuclideanSpace ℂ (Fin n)) c).trans p).target := by
    simpa only [nativePi_extChartAt (n := n) (M := M) c] using hz
  have hz' : z ∈ p.target ∩ p.symm ⁻¹' (chartAt (EuclideanSpace ℂ (Fin n)) c).target := by
    simpa only [OpenPartialHomeomorph.trans_target] using hzPi
  have hzNative : e z ∈ (chartAt (EuclideanSpace ℂ (Fin n)) c).target := by
    simpa [p] using hz'.2
  simpa [extChartAt_target] using hzNative

private theorem nativePi_symm_chart_eq_native_symm_chart {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M] (c : M)
    {z : Fin (2 * n) → ℝ} :
    letI := nativePiCharts (n := n) (M := M)
    (extChartAt 𝓘(ℝ, Fin (2 * n) → ℝ) c).symm z =
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) c).symm
        (hTopPiToComplexEquiv n z) := by
  let := nativePiCharts (n := n) (M := M)
  rw [nativePi_extChartAt (n := n) (M := M) c]
  simp

private theorem nativeToPi_toFormField_chartRep {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ M]
    (η : CalabiYau.DifferentialForm 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M (2 * n))
    (c : M) {z : Fin (2 * n) → ℝ}
    (hz : z ∈ letI := nativePiCharts (n := n) (M := M)
      (extChartAt 𝓘(ℝ, Fin (2 * n) → ℝ) c).target) :
    letI := nativePiCharts (n := n) (M := M)
    letI : IsManifold 𝓘(ℝ, Fin (2 * n) → ℝ) ∞ M := nativePiIsManifold
    (nativeToPiForms (2 * n) η).toFormField.chartRep c z =
      (η.toFormField.chartRep c (hTopPiToComplexEquiv n z)).compContinuousLinearMap
        (hTopPiToComplexEquiv n).toContinuousLinearMap := by
  let : ChartedSpace (Fin (2 * n) → ℝ) M := nativePiCharts
  let : IsManifold 𝓘(ℝ, Fin (2 * n) → ℝ) ∞ M := nativePiIsManifold
  let e := hTopPiToComplexEquiv n
  let x := (extChartAt 𝓘(ℝ, Fin (2 * n) → ℝ) c).symm z
  let xE := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) c).symm (e z)
  have hxEq : x = xE := nativePi_symm_chart_eq_native_symm_chart c
  have hzE : e z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) c).target :=
    nativePi_target_to_native c hz
  have hxC : xE ∈ (chartAt (EuclideanSpace ℂ (Fin n)) c).source := by
    simpa only [extChartAt_source] using
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) c).map_target hzE
  have hpoint := nativePi_symm_chart_eq_native_symm_chart (n := n) (M := M) (z := z) c
  unfold FormField.chartRep
  rw [hpoint]
  rw [nativeToPiForms_toFormField]
  have ht := nativePi_tangentCoordChange c xE hxC
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  apply congrArg (η.toFormField xE)
  funext i
  exact congrArg (fun L : (Fin (2 * n) → ℝ) →L[ℝ] EuclideanSpace ℂ (Fin n) =>
    L (v i)) ht

/-- The H3 coefficient of the actual identity-pullback form in canonical Pi charts. -/
theorem nativeToPi_chartTopCoefficient_eq_nativeChartRep
    (η : CalabiYau.DifferentialForm 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M (2 * n))
    (c : M) {z : Fin (2 * n) → ℝ}
    (hz : z ∈ letI := nativePiCharts (n := n) (M := M)
      (extChartAt 𝓘(ℝ, Fin (2 * n) → ℝ) c).target) :
    letI := nativePiCharts (n := n) (M := M)
    letI : IsManifold 𝓘(ℝ, Fin (2 * n) → ℝ) ∞ M := nativePiIsManifold
    chartTopCoefficient c (nativeToPiForms (2 * n) η) z =
      ContinuousAlternatingMap.topFormCoeff
        (η.toFormField.chartRep c (hTopPiToComplexEquiv n z)) := by
  let : ChartedSpace (Fin (2 * n) → ℝ) M := nativePiCharts
  let : IsManifold 𝓘(ℝ, Fin (2 * n) → ℝ) ∞ M := nativePiIsManifold
  classical
  unfold CalabiYau.DifferentialForm.chartTopCoefficient
  rw [ite_eq_left hz]
  rw [← CalabiYau.DifferentialForm.toFormField_chartRep
    (nativeToPiForms (2 * n) η) c hz]
  rw [nativeToPi_toFormField_chartRep η c hz]
  exact hTopPiPullback_topFormCoeff
    (η.toFormField.chartRep c (hTopPiToComplexEquiv n z))

end HTopFormVolumeBridge
