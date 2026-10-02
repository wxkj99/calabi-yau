-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Integration/Measure/Riemannian/Invariance.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Riemannian.Volume.Chart.Density
public import CalabiYau.Geometry.Riemannian.Volume.Basic
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff ENNReal Matrix

namespace CalabiYau.RiemannianVolume

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

lemma extChartAt_symm_preimage_inter_target_eq_empty
    (x₀ : M) {A : Set M} (hA : Disjoint A (chartAt H x₀).source) :
    (extChartAt I x₀).symm ⁻¹' A ∩ (extChartAt I x₀).target = ∅ := by
  ext y
  refine ⟨fun hy => ?_, fun hy => hy.elim⟩
  obtain ⟨hmem, htarget⟩ := hy
  have hsource : (extChartAt I x₀).symm y ∈ (extChartAt I x₀).source :=
    (extChartAt I x₀).map_target htarget
  have hchart_source :
      (extChartAt I x₀).symm y ∈ (chartAt H x₀).source := by
    rw [extChartAt_source] at hsource
    exact hsource
  have hne : ((extChartAt I x₀).symm y) ∈ A ∩ (chartAt H x₀).source :=
    ⟨hmem, hchart_source⟩
  have : A ∩ (chartAt H x₀).source = ∅ := by
    rw [Set.disjoint_iff_inter_eq_empty] at hA
    exact hA
  rw [this] at hne
  exact hne

lemma measurableSet_extChartAt_target (x₀ : M) :
    MeasurableSet (extChartAt I x₀).target := by
  rw [extChartAt_target (I := I)]
  refine MeasurableSet.inter ?_ ?_
  · exact (I.continuous_symm.isOpen_preimage _ (chartAt H x₀).open_target).measurableSet
  · exact I.isClosed_range.measurableSet
variable [Module.Finite ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] in

theorem chartLocalMeasure_apply_of_disjoint_source
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    {A : Set M} (hAmeas : MeasurableSet A)
    (hA : Disjoint A (chartAt H x₀).source) :
    chartLocalMeasure (I := I) g x₀ A = 0 := by
  unfold chartLocalMeasure
  set w : E → ℝ≥0∞ :=
    fun y : E => ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y))
  set ν : MeasureTheory.Measure E :=
    ((modelHaar (E := E)).restrict (extChartAt I x₀).target).withDensity w with hν
  have htarget_meas : MeasurableSet (extChartAt I x₀).target :=
    measurableSet_extChartAt_target (I := I) x₀
  have hcontOn : ContinuousOn (extChartAt I x₀).symm
      (extChartAt I x₀).target := continuousOn_extChartAt_symm (I := I) x₀
  have haemeas_base :
      AEMeasurable (extChartAt I x₀).symm
        ((modelHaar (E := E)).restrict (extChartAt I x₀).target) :=
    hcontOn.aemeasurable htarget_meas
  have hν_ac :
      ν ≪ (modelHaar (E := E)).restrict (extChartAt I x₀).target := by
    simpa [hν] using MeasureTheory.withDensity_absolutelyContinuous
      (μ := (modelHaar (E := E)).restrict (extChartAt I x₀).target) w
  have haemeas :
      AEMeasurable (extChartAt I x₀).symm ν := haemeas_base.mono_ac hν_ac
  rw [MeasureTheory.Measure.map_apply_of_aemeasurable haemeas hAmeas]
  have hbase_zero :
      ((modelHaar (E := E)).restrict (extChartAt I x₀).target)
          ((extChartAt I x₀).symm ⁻¹' A) = 0 := by
    rw [MeasureTheory.Measure.restrict_apply' htarget_meas]
    rw [extChartAt_symm_preimage_inter_target_eq_empty (I := I) x₀ hA]
    exact MeasureTheory.measure_empty
  exact hν_ac hbase_zero
variable [Module.Finite ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] in

lemma chartModelBasis_repr_sum
    (L : E →L[ℝ] E) (i : Fin (Module.finrank ℝ E)) :
    L ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i) =
      ∑ k, ((CalabiYau.Tensor.Coordinates.chartModelBasis E).repr (L ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i)) k)
            • (CalabiYau.Tensor.Coordinates.chartModelBasis E) k :=
  (((CalabiYau.Tensor.Coordinates.chartModelBasis E).sum_repr (L ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i)))).symm
variable [Module.Finite ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] in

def transitionMatrix (x₀ x₁ : M) (x : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun k i =>
    (CalabiYau.Tensor.Coordinates.chartModelBasis E).repr
      ((tangentCoordChange I x₁ x₀ x) ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i)) k
variable [Module.Finite ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] in

@[simp] lemma transitionMatrix_apply (x₀ x₁ : M) (x : M)
    (k i : Fin (Module.finrank ℝ E)) :
    transitionMatrix (I := I) x₀ x₁ x k i =
      (CalabiYau.Tensor.Coordinates.chartModelBasis E).repr
        ((tangentCoordChange I x₁ x₀ x) ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i)) k := rfl
section

variable [Module.Finite ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


lemma tangentCoordChange_chartModelBasis_eq_sum
    (x₀ x₁ : M) (x : M) (i : Fin (Module.finrank ℝ E)) :
    (tangentCoordChange I x₁ x₀ x) ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i) =
      ∑ k, transitionMatrix (I := I) x₀ x₁ x k i • (CalabiYau.Tensor.Coordinates.chartModelBasis E) k :=
  chartModelBasis_repr_sum (tangentCoordChange I x₁ x₀ x) i

lemma chartBasisVecFiber_pullback
    (x₀ x₁ : M) {x : M}
    (hx0 : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hx1 : x ∈ (trivializationAt E (TangentSpace I) x₁).baseSet)
    (i : Fin (Module.finrank ℝ E)) :
    CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) x₁ i x =
      ∑ k, transitionMatrix (I := I) x₀ x₁ x k i •
        CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ k x := by
  set T₀ : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)) :=
    trivializationAt E (TangentSpace I) x₀
  set T₁ : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)) :=
    trivializationAt E (TangentSpace I) x₁
  have hx0' : x ∈ T₀.baseSet := hx0
  have hx1' : x ∈ T₁.baseSet := hx1
  have hdef1 :
      CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) x₁ i x =
        T₁.symm x ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i) := by
    rw [CalabiYau.Tensor.Coordinates.chartBasisVecFiber, T₁.symmL_apply hx1']
  have hcompeq' :=
    Bundle.Trivialization.comp_continuousLinearEquivAt_eq_coord_change
      (R := ℝ) (F := E) (E := (TangentSpace I : M → Type _))
      T₁ T₀ (b := x) ⟨hx1', hx0'⟩
  have happ :
      (T₀.continuousLinearEquivAt ℝ x hx0')
          ((T₁.continuousLinearEquivAt ℝ x hx1').symm ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i))
        = (Bundle.Trivialization.coordChangeL (R := ℝ) T₁ T₀ x)
            ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i) := by
    have := congrArg
      (fun L : E ≃L[ℝ] E => L ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i)) hcompeq'
    simpa [ContinuousLinearEquiv.trans_apply] using this
  have hequiv :
      T₁.symm x ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i) =
        T₀.symm x
          ((Bundle.Trivialization.coordChangeL (R := ℝ) T₁ T₀ x)
            ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i)) := by
    have hL : (T₁.continuousLinearEquivAt ℝ x hx1').symm ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i) =
              T₁.symm x ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i) := rfl
    have hR : (T₀.continuousLinearEquivAt ℝ x hx0').symm
                ((Bundle.Trivialization.coordChangeL (R := ℝ) T₁ T₀ x)
                  ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i)) =
              T₀.symm x
                ((Bundle.Trivialization.coordChangeL (R := ℝ) T₁ T₀ x)
                  ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i)) := rfl
    have := congrArg (T₀.continuousLinearEquivAt ℝ x hx0').symm happ
    simp only [ContinuousLinearEquiv.symm_apply_apply] at this
    rw [← hL, ← hR]
    exact this
  have hcc :
      (Bundle.Trivialization.coordChangeL (R := ℝ) T₁ T₀ x)
          ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i)
        = (tangentCoordChange I x₁ x₀ x) ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i) := by
    change (Bundle.Trivialization.coordChangeL (R := ℝ)
          ((tangentBundleCore I M).localTriv (achart H x₁))
          ((tangentBundleCore I M).localTriv (achart H x₀)) x)
        ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i) = _
    exact VectorBundleCore.localTriv_coordChange_eq
        (tangentBundleCore I M) (achart H x₁) (achart H x₀) (b := x)
        ⟨hx1', hx0'⟩ _
  rw [hdef1, hequiv, hcc, tangentCoordChange_chartModelBasis_eq_sum (I := I) x₀ x₁ x i]
  have hsymmL : (T₀.symm x : E → TangentSpace I x) =
      (T₀.symmL ℝ x : E →L[ℝ] TangentSpace I x) := by
    funext v
    exact (T₀.symmL_apply hx0' v).symm
  rw [hsymmL]
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [map_smul]
  rw [CalabiYau.Tensor.Coordinates.chartBasisVecFiber, T₀.symmL_apply hx0']

lemma chartGramMatrix_pullback_eq_sum
    (g : SmoothRiemannianMetric I M) (x₀ x₁ : M) {x : M}
    (hx0 : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hx1 : x ∈ (trivializationAt E (TangentSpace I) x₁).baseSet)
    (i j : Fin (Module.finrank ℝ E)) :
    CalabiYau.Tensor.Coordinates.chartGramMatrix g x₁ x i j =
      ∑ k, ∑ l,
        (transitionMatrix (I := I) x₀ x₁ x k i) *
        (transitionMatrix (I := I) x₀ x₁ x l j) *
        CalabiYau.Tensor.Coordinates.chartGramMatrix g x₀ x k l := by
  have hlhs :
      CalabiYau.Tensor.Coordinates.chartGramMatrix g x₁ x i j =
        g.inner x
          (CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) x₁ i x)
          (CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) x₁ j x) := rfl
  rw [hlhs]
  rw [chartBasisVecFiber_pullback (I := I) x₀ x₁ hx0 hx1 i]
  rw [chartBasisVecFiber_pullback (I := I) x₀ x₁ hx0 hx1 j]
  have hL :
      g.inner x
          (∑ k, transitionMatrix (I := I) x₀ x₁ x k i •
            CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ k x)
        = ∑ k, transitionMatrix (I := I) x₀ x₁ x k i •
            g.inner x (CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ k x) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [map_smul]
  rw [hL]
  rw [sum_apply]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [smul_apply]
  have hR :
      g.inner x (CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ k x)
          (∑ l, transitionMatrix (I := I) x₀ x₁ x l j •
            CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ l x)
        = ∑ l, transitionMatrix (I := I) x₀ x₁ x l j *
            g.inner x (CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ k x)
              (CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ l x) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro l _
    rw [map_smul]
    rw [smul_eq_mul]
  rw [hR, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [CalabiYau.Tensor.Coordinates.chartGramMatrix_apply]
  ring

lemma chartGramMatrix_pullback_eq_mul
    (g : SmoothRiemannianMetric I M) (x₀ x₁ : M) {x : M}
    (hx0 : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hx1 : x ∈ (trivializationAt E (TangentSpace I) x₁).baseSet) :
    CalabiYau.Tensor.Coordinates.chartGramMatrix g x₁ x =
      (transitionMatrix (I := I) x₀ x₁ x)ᵀ *
        CalabiYau.Tensor.Coordinates.chartGramMatrix g x₀ x *
        transitionMatrix (I := I) x₀ x₁ x := by
  ext i j
  rw [chartGramMatrix_pullback_eq_sum (I := I) g x₀ x₁ hx0 hx1 i j]
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro k _
  ring

lemma transitionMatrix_det (x₀ x₁ : M) (x : M) :
    (transitionMatrix (I := I) x₀ x₁ x).det =
      (tangentCoordChange I x₁ x₀ x : E →L[ℝ] E).det := by
  have hL :
      transitionMatrix (I := I) x₀ x₁ x =
        LinearMap.toMatrix (CalabiYau.Tensor.Coordinates.chartModelBasis E) (CalabiYau.Tensor.Coordinates.chartModelBasis E)
          (tangentCoordChange I x₁ x₀ x : E →L[ℝ] E).toLinearMap := by
    ext k i
    simp [transitionMatrix, LinearMap.toMatrix_apply]
  rw [hL]
  rw [LinearMap.det_toMatrix]

lemma chartGramMatrix_det_pullback
    (g : SmoothRiemannianMetric I M) (x₀ x₁ : M) {x : M}
    (hx0 : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hx1 : x ∈ (trivializationAt E (TangentSpace I) x₁).baseSet) :
    (CalabiYau.Tensor.Coordinates.chartGramMatrix g x₁ x).det =
      ((tangentCoordChange I x₁ x₀ x : E →L[ℝ] E).det) ^ 2 *
        (CalabiYau.Tensor.Coordinates.chartGramMatrix g x₀ x).det := by
  rw [chartGramMatrix_pullback_eq_mul (I := I) g x₀ x₁ hx0 hx1]
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  rw [transitionMatrix_det (I := I) x₀ x₁ x]
  ring

theorem chartDensity_pullback_eq_abs_det_jacobian
    (g : SmoothRiemannianMetric I M) (x₀ x₁ : M) {x : M}
    (hx0 : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hx1 : x ∈ (trivializationAt E (TangentSpace I) x₁).baseSet) :
    chartDensity g x₁ x =
      |(tangentCoordChange I x₁ x₀ x : E →L[ℝ] E).det| *
        chartDensity g x₀ x := by
  unfold chartDensity
  rw [chartGramMatrix_det_pullback (I := I) g x₀ x₁ hx0 hx1]
  rw [Real.sqrt_mul (sq_nonneg _)]
  rw [Real.sqrt_sq_eq_abs]

export CalabiYau.Tensor.Coordinates
  (trivializationAt_baseSet_eq_chartAt_source extChartAt_source_eq_chartAt_source)

end

lemma isOpen_chartAt_source_inter (x₀ x₁ : M) :
    IsOpen ((chartAt H x₀).source ∩ (chartAt H x₁).source) :=
  (chartAt H x₀).open_source.inter (chartAt H x₁).open_source

lemma measurableSet_chartAt_source_inter (x₀ x₁ : M) :
    MeasurableSet ((chartAt H x₀).source ∩ (chartAt H x₁).source) :=
  (isOpen_chartAt_source_inter (H := H) (M := M) x₀ x₁).measurableSet
variable [Module.Finite ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] in

lemma chartDensity_continuousOn
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    ContinuousOn (chartDensity g x₀)
      (trivializationAt E (TangentSpace I) x₀).baseSet :=
  (chartDensity_contMDiffOn (I := I) g x₀).continuousOn

variable (I M) in
variable [Module.Finite ℝ E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] in
def riemannianVolumeMeasure
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) : MeasureTheory.Measure M :=
  riemannianMeasure (I := I) g (chartAtlasPOU I M)
variable [Module.Finite ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] in

lemma riemannianVolumeMeasure_def
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) :
    riemannianVolumeMeasure (I := I) (M := M) g =
      riemannianMeasure (I := I) g (chartAtlasPOU I M) := rfl

variable [Module.Finite ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] in
lemma aemeasurable_extChartAt_symm_restrict_target
    (x₀ : M) :
    AEMeasurable ((extChartAt I x₀).symm)
      ((modelHaar (E := E)).restrict (extChartAt I x₀).target) := by
  have htarget_meas : MeasurableSet (extChartAt I x₀).target :=
    measurableSet_extChartAt_target (I := I) x₀
  exact (continuousOn_extChartAt_symm (I := I) x₀).aemeasurable htarget_meas
section

variable [Module.Finite ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


lemma aemeasurable_chartDensity_symm_pullback
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    AEMeasurable
      (fun y : E =>
        ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y)))
      ((modelHaar (E := E)).restrict (extChartAt I x₀).target) := by
  have htarget_meas : MeasurableSet (extChartAt I x₀).target :=
    measurableSet_extChartAt_target (I := I) x₀
  have hcontOn : ContinuousOn (chartDensity g x₀ ∘ (extChartAt I x₀).symm)
      (extChartAt I x₀).target := by
    refine (chartDensity_continuousOn (I := I) g x₀).comp
      (continuousOn_extChartAt_symm (I := I) x₀) ?_
    intro y hy
    have hsource : (extChartAt I x₀).symm y ∈ (extChartAt I x₀).source :=
      (extChartAt I x₀).map_target hy
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
    exact hsource
  have haem_density : AEMeasurable
      (fun y : E => chartDensity g x₀ ((extChartAt I x₀).symm y))
      ((modelHaar (E := E)).restrict (extChartAt I x₀).target) :=
    hcontOn.aemeasurable htarget_meas
  exact ENNReal.measurable_ofReal.comp_aemeasurable haem_density

theorem chartLocalMeasure_lintegral
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    {F : M → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x ∂(chartLocalMeasure (I := I) g x₀) =
      ∫⁻ y in (extChartAt I x₀).target,
        ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y)) *
          F ((extChartAt I x₀).symm y) ∂ (modelHaar (E := E)) := by
  unfold chartLocalMeasure
  have htarget_meas : MeasurableSet (extChartAt I x₀).target :=
    measurableSet_extChartAt_target (I := I) x₀
  have haem_base : AEMeasurable (extChartAt I x₀).symm
      ((modelHaar (E := E)).restrict (extChartAt I x₀).target) :=
    aemeasurable_extChartAt_symm_restrict_target (I := I) (E := E) x₀
  have hw_aem : AEMeasurable
      (fun y : E =>
        ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y)))
      ((modelHaar (E := E)).restrict (extChartAt I x₀).target) :=
    aemeasurable_chartDensity_symm_pullback (I := I) g x₀
  have hwd_ac :
      (((modelHaar (E := E)).restrict (extChartAt I x₀).target).withDensity
          (fun y : E =>
            ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y))))
        ≪ (modelHaar (E := E)).restrict (extChartAt I x₀).target :=
    MeasureTheory.withDensity_absolutelyContinuous _ _
  have haem : AEMeasurable (extChartAt I x₀).symm
      (((modelHaar (E := E)).restrict (extChartAt I x₀).target).withDensity
        (fun y : E =>
          ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y)))) :=
    haem_base.mono_ac hwd_ac
  rw [MeasureTheory.lintegral_map' hF.aemeasurable haem]
  have hcomp :=
    MeasureTheory.lintegral_withDensity_eq_lintegral_mul₀
      (μ := (modelHaar (E := E)).restrict (extChartAt I x₀).target) hw_aem
      (g := fun y : E => F ((extChartAt I x₀).symm y))
      (hF.aemeasurable.comp_aemeasurable haem_base)
  simp only [Pi.mul_apply] at hcomp
  rw [hcomp]

end
section

variable [IsManifold I ∞ M]


lemma tangentCoordChange_comp_self_overlap
    (x₀ x₁ : M) {x : M}
    (h : x ∈ (extChartAt I x₀).source ∩ (extChartAt I x₁).source) (v : E) :
    tangentCoordChange I x₁ x₀ x (tangentCoordChange I x₀ x₁ x v) = v := by
  have h3 : x ∈ (extChartAt I x₀).source ∩ (extChartAt I x₁).source ∩
      (extChartAt I x₀).source := ⟨h, h.1⟩
  have := tangentCoordChange_comp (I := I) (w := x₀) (x := x₁) (y := x₀)
    (z := x) (v := v) h3
  rw [this]
  exact tangentCoordChange_self (I := I) h.1

lemma tangentCoordChange_det_mul_inv_det_eq_one
    (x₀ x₁ : M) {x : M}
    (h : x ∈ (extChartAt I x₀).source ∩ (extChartAt I x₁).source) :
    (tangentCoordChange I x₀ x₁ x : E →L[ℝ] E).det *
      (tangentCoordChange I x₁ x₀ x : E →L[ℝ] E).det = 1 := by
  classical
  have hcomp_id :
      ((tangentCoordChange I x₁ x₀ x : E →L[ℝ] E) :
            E →ₗ[ℝ] E).comp
          ((tangentCoordChange I x₀ x₁ x : E →L[ℝ] E) : E →ₗ[ℝ] E) =
        LinearMap.id := by
    ext v
    simp only [LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Function.comp_apply,
      LinearMap.id_coe, id_eq]
    exact tangentCoordChange_comp_self_overlap (I := I) x₀ x₁ h v
  have := congrArg LinearMap.det hcomp_id
  rw [LinearMap.det_comp, LinearMap.det_id] at this
  have : (tangentCoordChange I x₁ x₀ x : E →L[ℝ] E).det *
      (tangentCoordChange I x₀ x₁ x : E →L[ℝ] E).det = 1 := this
  linarith [this, mul_comm
    ((tangentCoordChange I x₀ x₁ x : E →L[ℝ] E).det)
    ((tangentCoordChange I x₁ x₀ x : E →L[ℝ] E).det)]

lemma abs_det_tangentCoordChange_mul_abs_det_inv
    (x₀ x₁ : M) {x : M}
    (h : x ∈ (extChartAt I x₀).source ∩ (extChartAt I x₁).source) :
    |(tangentCoordChange I x₀ x₁ x : E →L[ℝ] E).det| *
      |(tangentCoordChange I x₁ x₀ x : E →L[ℝ] E).det| = 1 := by
  rw [← abs_mul, tangentCoordChange_det_mul_inv_det_eq_one (I := I) x₀ x₁ h,
    abs_one]

lemma ennreal_abs_det_tangentCoordChange_mul_abs_det_inv
    (x₀ x₁ : M) {x : M}
    (h : x ∈ (extChartAt I x₀).source ∩ (extChartAt I x₁).source) :
    ENNReal.ofReal |(tangentCoordChange I x₀ x₁ x : E →L[ℝ] E).det| *
      ENNReal.ofReal
        |(tangentCoordChange I x₁ x₀ x : E →L[ℝ] E).det| = 1 := by
  rw [← ENNReal.ofReal_mul (abs_nonneg _)]
  rw [abs_det_tangentCoordChange_mul_abs_det_inv (I := I) x₀ x₁ h]
  exact ENNReal.ofReal_one

end
variable [Module.Finite ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] in

theorem chartLocalMeasure_setLintegral_indicator
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    {U : Set M} (hUmeas : MeasurableSet U)
    {F : M → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x in U, F x ∂(chartLocalMeasure (I := I) g x₀) =
      ∫⁻ y in (extChartAt I x₀).target,
        ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y)) *
          U.indicator F ((extChartAt I x₀).symm y) ∂ (modelHaar (E := E)) := by
  rw [← MeasureTheory.lintegral_indicator hUmeas]
  exact chartLocalMeasure_lintegral (I := I) g x₀ (hF.indicator hUmeas)

lemma extChartAt_image_isOpen_of_open_subset_source_of_boundaryless
    [I.Boundaryless] (x₀ : M)
    {U : Set M} (hUopen : IsOpen U) (hUsub : U ⊆ (chartAt H x₀).source) :
    IsOpen ((extChartAt I x₀) '' U) := by
  have hchart_image : IsOpen ((chartAt H x₀) '' U) :=
    (chartAt H x₀).isOpen_image_of_subset_source hUopen hUsub
  have himg_eq : (extChartAt I x₀) '' U = I '' ((chartAt H x₀) '' U) := by
    rw [extChartAt]
    simp only [OpenPartialHomeomorph.extend_coe]
    rw [image_comp]
  rw [himg_eq]
  exact I.toHomeomorph.isOpenMap _ hchart_image

lemma extChartAt_image_measurableSet_of_open_subset_source (x₀ : M)
    {U : Set M} (hUopen : IsOpen U) (hUsub : U ⊆ (chartAt H x₀).source) :
    MeasurableSet ((extChartAt I x₀) '' U) := by
  have hchart_image : IsOpen ((chartAt H x₀) '' U) :=
    (chartAt H x₀).isOpen_image_of_subset_source hUopen hUsub
  have himg_eq : (extChartAt I x₀) '' U = I '' ((chartAt H x₀) '' U) := by
    rw [extChartAt]
    simp only [OpenPartialHomeomorph.extend_coe]
    rw [image_comp]
  rw [himg_eq]
  exact I.isClosedEmbedding.measurableEmbedding.measurableSet_image.mpr
    hchart_image.measurableSet

lemma extChartAt_transition_image
    (x₀ x₁ : M) {U : Set M}
    (hUsub0 : U ⊆ (chartAt H x₀).source) :
    (extChartAt I x₁ ∘ (extChartAt I x₀).symm) '' ((extChartAt I x₀) '' U) =
      (extChartAt I x₁) '' U := by
  rw [← Set.image_comp]
  refine Set.image_congr ?_
  intro x hx
  have hxsrc0 : x ∈ (extChartAt I x₀).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hUsub0 hx
  change extChartAt I x₁ ((extChartAt I x₀).symm (extChartAt I x₀ x)) = _
  rw [(extChartAt I x₀).left_inv hxsrc0]

lemma extChartAt_transition_injOn_overlap_image
    (x₀ x₁ : M) {U : Set M}
    (hUsub0 : U ⊆ (chartAt H x₀).source) (hUsub1 : U ⊆ (chartAt H x₁).source) :
    Set.InjOn (extChartAt I x₁ ∘ (extChartAt I x₀).symm)
      ((extChartAt I x₀) '' U) := by
  intro y hy z hz hyz
  obtain ⟨a, haU, rfl⟩ := hy
  obtain ⟨b, hbU, rfl⟩ := hz
  have haS0 : a ∈ (extChartAt I x₀).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hUsub0 haU
  have hbS0 : b ∈ (extChartAt I x₀).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hUsub0 hbU
  have haS1 : a ∈ (extChartAt I x₁).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hUsub1 haU
  have hbS1 : b ∈ (extChartAt I x₁).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hUsub1 hbU
  simp only [Function.comp_apply, (extChartAt I x₀).left_inv haS0,
    (extChartAt I x₀).left_inv hbS0] at hyz
  have := (extChartAt I x₁).injOn haS1 hbS1 hyz
  rw [this]

variable [IsManifold I ∞ M] in
lemma extChartAt_transition_hasFDerivWithinAt_on_overlap_image
    (x₀ x₁ : M) {U : Set M}
    (hUsub0 : U ⊆ (chartAt H x₀).source) (hUsub1 : U ⊆ (chartAt H x₁).source) :
    ∀ y ∈ (extChartAt I x₀) '' U,
      HasFDerivWithinAt (extChartAt I x₁ ∘ (extChartAt I x₀).symm)
        (tangentCoordChange I x₀ x₁ ((extChartAt I x₀).symm y))
        ((extChartAt I x₀) '' U) y := by
  intro y hy
  obtain ⟨x, hxU, rfl⟩ := hy
  have hxS0 : x ∈ (extChartAt I x₀).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hUsub0 hxU
  have hxS1 : x ∈ (extChartAt I x₁).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hUsub1 hxU
  have hfull := hasFDerivWithinAt_tangentCoordChange (I := I) (x := x₀) (y := x₁)
    (z := x) ⟨hxS0, hxS1⟩
  have himage_sub : (extChartAt I x₀) '' U ⊆ Set.range I := by
    intro y' hy'
    rcases hy' with ⟨z, hzU, rfl⟩
    have hzS0 : z ∈ (extChartAt I x₀).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hUsub0 hzU
    exact extChartAt_target_subset_range (I := I) x₀ ((extChartAt I x₀).map_source hzS0)
  have hsymm_eq : (extChartAt I x₀).symm ((extChartAt I x₀) x) = x :=
    (extChartAt I x₀).left_inv hxS0
  rw [hsymm_eq]
  exact hfull.mono himage_sub

variable [Module.Finite ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] in
lemma setLIntegral_target_eq_setLIntegral_image
    (x₀ : M)
    {U : Set M} (hUopen : IsOpen U) (hUsub : U ⊆ (chartAt H x₀).source)
    (h : E → ℝ≥0∞) :
    ∫⁻ y in (extChartAt I x₀).target,
        (U.indicator (fun _ => (1 : ℝ≥0∞)) ((extChartAt I x₀).symm y)) * h y
            ∂(modelHaar (E := E)) =
      ∫⁻ y in (extChartAt I x₀) '' U, h y ∂(modelHaar (E := E)) := by
  have hUsub' : U ⊆ (extChartAt I x₀).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hUsub
  have himg :
      (extChartAt I x₀) '' U =
        (extChartAt I x₀).target ∩ (extChartAt I x₀).symm ⁻¹' U :=
    (extChartAt I x₀).image_eq_target_inter_inv_preimage hUsub'
  have hptwise : ∀ y ∈ (extChartAt I x₀).target,
      U.indicator (fun _ => (1 : ℝ≥0∞)) ((extChartAt I x₀).symm y) * h y =
        ((extChartAt I x₀) '' U).indicator h y := by
    intro y hy
    by_cases hy' : (extChartAt I x₀).symm y ∈ U
    · have hy_image : y ∈ (extChartAt I x₀) '' U := by
        rw [himg]; exact ⟨hy, hy'⟩
      rw [Set.indicator_of_mem hy', Set.indicator_of_mem hy_image, one_mul]
    · have hy_nimg : y ∉ (extChartAt I x₀) '' U := by
        rw [himg]; exact fun h => hy' h.2
      rw [Set.indicator_of_notMem hy', Set.indicator_of_notMem hy_nimg, zero_mul]
  have htarget_meas : MeasurableSet (extChartAt I x₀).target :=
    measurableSet_extChartAt_target (I := I) x₀
  rw [MeasureTheory.setLIntegral_congr_fun htarget_meas hptwise]
  have hV_meas : MeasurableSet ((extChartAt I x₀) '' U) :=
    extChartAt_image_measurableSet_of_open_subset_source (I := I) x₀
      hUopen hUsub
  rw [MeasureTheory.setLIntegral_indicator hV_meas]
  rw [show ((extChartAt I x₀) '' U) ∩ (extChartAt I x₀).target =
        (extChartAt I x₀) '' U from by
    rw [himg]; ext y; constructor
    · rintro ⟨⟨hy_t, hy_u⟩, _⟩; exact ⟨hy_t, hy_u⟩
    · rintro ⟨hy_t, hy_u⟩; exact ⟨⟨hy_t, hy_u⟩, hy_t⟩]
section

variable [Module.Finite ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


lemma chartLocalMeasure_lintegral_U_eq_setLIntegral_image
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    {U : Set M} (hUopen : IsOpen U) (hUsub : U ⊆ (chartAt H x₀).source)
    {F : M → ℝ≥0∞} (hF : Measurable F)
    (hUmeas : MeasurableSet U) :
    ∫⁻ x in U, F x ∂(chartLocalMeasure (I := I) g x₀) =
      ∫⁻ y in (extChartAt I x₀) '' U,
        ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y)) *
          F ((extChartAt I x₀).symm y) ∂ (modelHaar (E := E)) := by
  rw [chartLocalMeasure_setLintegral_indicator (I := I) g x₀ hUmeas hF]
  have hpt : ∀ y : E,
      ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y)) *
          U.indicator F ((extChartAt I x₀).symm y) =
        (U.indicator (fun _ => (1 : ℝ≥0∞)) ((extChartAt I x₀).symm y)) *
          (ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y)) *
            F ((extChartAt I x₀).symm y)) := by
    intro y
    by_cases hy : (extChartAt I x₀).symm y ∈ U
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, one_mul]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy,
        mul_zero, zero_mul]
  conv_lhs => rw [MeasureTheory.setLIntegral_congr_fun
    (measurableSet_extChartAt_target (I := I) x₀)
    (fun y _ => hpt y)]
  exact setLIntegral_target_eq_setLIntegral_image (I := I) (E := E) x₀ hUopen hUsub _

theorem chartLocalMeasure_lintegral_U_eq_of_overlap
    (g : SmoothRiemannianMetric I M) (x₀ x₁ : M)
    {F : M → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x in (chartAt H x₀).source ∩ (chartAt H x₁).source, F x
        ∂(chartLocalMeasure (I := I) g x₀) =
      ∫⁻ x in (chartAt H x₀).source ∩ (chartAt H x₁).source, F x
        ∂(chartLocalMeasure (I := I) g x₁) := by
  set U : Set M := (chartAt H x₀).source ∩ (chartAt H x₁).source with hU_def
  have hUopen : IsOpen U := isOpen_chartAt_source_inter (H := H) (M := M) x₀ x₁
  have hUmeas : MeasurableSet U :=
    measurableSet_chartAt_source_inter (H := H) (M := M) x₀ x₁
  have hUsub0 : U ⊆ (chartAt H x₀).source := Set.inter_subset_left
  have hUsub1 : U ⊆ (chartAt H x₁).source := Set.inter_subset_right
  rw [chartLocalMeasure_lintegral_U_eq_setLIntegral_image (I := I)
    g x₀ hUopen hUsub0 hF hUmeas]
  rw [chartLocalMeasure_lintegral_U_eq_setLIntegral_image (I := I)
    g x₁ hUopen hUsub1 hF hUmeas]
  have hV0_meas : MeasurableSet ((extChartAt I x₀) '' U) :=
    extChartAt_image_measurableSet_of_open_subset_source (I := I) x₀
      hUopen hUsub0
  have hT_image :
      (extChartAt I x₁ ∘ (extChartAt I x₀).symm) '' ((extChartAt I x₀) '' U) =
        (extChartAt I x₁) '' U :=
    extChartAt_transition_image (I := I) x₀ x₁ hUsub0
  have hT_injOn :
      Set.InjOn (extChartAt I x₁ ∘ (extChartAt I x₀).symm)
        ((extChartAt I x₀) '' U) :=
    extChartAt_transition_injOn_overlap_image (I := I) x₀ x₁ hUsub0 hUsub1
  have hT_fderiv :
      ∀ y ∈ (extChartAt I x₀) '' U,
        HasFDerivWithinAt (extChartAt I x₁ ∘ (extChartAt I x₀).symm)
          (tangentCoordChange I x₀ x₁ ((extChartAt I x₀).symm y))
          ((extChartAt I x₀) '' U) y :=
    extChartAt_transition_hasFDerivWithinAt_on_overlap_image (I := I) x₀ x₁
      hUsub0 hUsub1
  rw [← hT_image]
  rw [MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (μ := modelHaar (E := E)) hV0_meas hT_fderiv hT_injOn
    (g := fun z : E =>
      ENNReal.ofReal (chartDensity g x₁ ((extChartAt I x₁).symm z)) *
        F ((extChartAt I x₁).symm z))]
  refine MeasureTheory.setLIntegral_congr_fun hV0_meas ?_
  intro y hy
  obtain ⟨x, hxU, hx_eq⟩ := hy
  have hx0 : x ∈ (extChartAt I x₀).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hUsub0 hxU
  have hx1 : x ∈ (extChartAt I x₁).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hUsub1 hxU
  have hx_in_inter : x ∈ (extChartAt I x₀).source ∩ (extChartAt I x₁).source :=
    ⟨hx0, hx1⟩
  have hx_trivBase0 : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source (I := I)]
    exact hUsub0 hxU
  have hx_trivBase1 : x ∈ (trivializationAt E (TangentSpace I) x₁).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source (I := I)]
    exact hUsub1 hxU
  have hsymm0 : (extChartAt I x₀).symm y = x := by
    rw [← hx_eq]; exact (extChartAt I x₀).left_inv hx0
  have hTy :
      (extChartAt I x₁ ∘ (extChartAt I x₀).symm) y = extChartAt I x₁ x := by
    change extChartAt I x₁ ((extChartAt I x₀).symm y) = _
    rw [hsymm0]
  have hsymm1 :
      (extChartAt I x₁).symm ((extChartAt I x₁ ∘ (extChartAt I x₀).symm) y) = x := by
    rw [hTy]; exact (extChartAt I x₁).left_inv hx1
  have hdens_pb :
      chartDensity g x₁ x
        = |(tangentCoordChange I x₁ x₀ x : E →L[ℝ] E).det|
            * chartDensity g x₀ x :=
    chartDensity_pullback_eq_abs_det_jacobian (I := I) g x₀ x₁
      hx_trivBase0 hx_trivBase1
  have hdet_mul :
      ENNReal.ofReal |(tangentCoordChange I x₀ x₁ x : E →L[ℝ] E).det| *
        ENNReal.ofReal |(tangentCoordChange I x₁ x₀ x : E →L[ℝ] E).det| = 1 :=
    ennreal_abs_det_tangentCoordChange_mul_abs_det_inv (I := I) x₀ x₁
      hx_in_inter
  simp only [hsymm0, hsymm1]
  rw [hdens_pb]
  rw [ENNReal.ofReal_mul (abs_nonneg _)]
  rw [show
    ENNReal.ofReal |(tangentCoordChange I x₀ x₁ x : E →L[ℝ] E).det| *
        (ENNReal.ofReal |(tangentCoordChange I x₁ x₀ x : E →L[ℝ] E).det| *
          ENNReal.ofReal (chartDensity g x₀ x) *
            F x) =
      (ENNReal.ofReal |(tangentCoordChange I x₀ x₁ x : E →L[ℝ] E).det| *
        ENNReal.ofReal |(tangentCoordChange I x₁ x₀ x : E →L[ℝ] E).det|) *
        (ENNReal.ofReal (chartDensity g x₀ x) * F x) by ring]
  rw [hdet_mul, one_mul]

theorem chartLocalMeasure_restrict_overlap_eq
    (g : SmoothRiemannianMetric I M) (x₀ x₁ : M) :
    (chartLocalMeasure (I := I) g x₀).restrict
        ((chartAt H x₀).source ∩ (chartAt H x₁).source) =
      (chartLocalMeasure (I := I) g x₁).restrict
        ((chartAt H x₀).source ∩ (chartAt H x₁).source) := by
  refine MeasureTheory.Measure.ext_of_lintegral _ (fun F hF => ?_)
  exact chartLocalMeasure_lintegral_U_eq_of_overlap (I := I) g x₀ x₁ hF

lemma chartLocalMeasure_lintegral_eq_of_support_in_overlap
    (g : SmoothRiemannianMetric I M) (x₀ x₁ : M)
    {f : M → ℝ≥0∞} (hf : Measurable f)
    (hsupp : ∀ x, x ∉ (chartAt H x₀).source ∩ (chartAt H x₁).source → f x = 0) :
    ∫⁻ x, f x ∂(chartLocalMeasure (I := I) g x₀) =
      ∫⁻ x, f x ∂(chartLocalMeasure (I := I) g x₁) := by
  set U : Set M := (chartAt H x₀).source ∩ (chartAt H x₁).source with hU_def
  have hUmeas : MeasurableSet U :=
    measurableSet_chartAt_source_inter (H := H) (M := M) x₀ x₁
  have hUeq : ∫⁻ x, f x ∂(chartLocalMeasure (I := I) g x₀) =
        ∫⁻ x in U, f x ∂(chartLocalMeasure (I := I) g x₀) := by
    rw [← MeasureTheory.lintegral_indicator hUmeas]
    refine MeasureTheory.lintegral_congr (fun x => ?_)
    by_cases hx : x ∈ U
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, hsupp x hx]
  have hUeq' : ∫⁻ x, f x ∂(chartLocalMeasure (I := I) g x₁) =
        ∫⁻ x in U, f x ∂(chartLocalMeasure (I := I) g x₁) := by
    rw [← MeasureTheory.lintegral_indicator hUmeas]
    refine MeasureTheory.lintegral_congr (fun x => ?_)
    by_cases hx : x ∈ U
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, hsupp x hx]
  rw [hUeq, hUeq']
  exact chartLocalMeasure_lintegral_U_eq_of_overlap (I := I) g x₀ x₁ hf

end

omit [TopologicalSpace M] in
lemma tsum_subtype_eq_of_support_subset {s : Set M} {f : M → ℝ≥0∞}
    (h : Function.support f ⊆ s) :
    ∑' x : M, f x = ∑' x : s, f x.val := by
  classical
  rw [tsum_subtype s f]
  refine tsum_congr (fun x => ?_)
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx]
    by_contra hne
    exact hx (h hne)
variable [Module.Finite ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] in

def transitionMatrixFinBasis (x₀ x₁ : M) (x : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun k i =>
    (Module.finBasis ℝ E).repr
      ((tangentCoordChange I x₁ x₀ x) ((Module.finBasis ℝ E) i)) k
variable [Module.Finite ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] in

@[simp] lemma transitionMatrixFinBasis_apply (x₀ x₁ : M) (x : M)
    (k i : Fin (Module.finrank ℝ E)) :
    transitionMatrixFinBasis (I := I) x₀ x₁ x k i =
      (Module.finBasis ℝ E).repr
        ((tangentCoordChange I x₁ x₀ x) ((Module.finBasis ℝ E) i)) k := rfl

end CalabiYau.RiemannianVolume
