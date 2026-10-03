-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Integration/Measure/Chart/MeasureComparison.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Chart.Defs
public import CalabiYau.Analysis.Sobolev.Manifold.RiemannianRellich
public import CalabiYau.Geometry.Riemannian.Volume.Basic
public import CalabiYau.Geometry.Riemannian.Volume.Chart.Density
public import CalabiYau.Geometry.Riemannian.Volume.Invariance
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable (I)
variable [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] in

def chartPushedRaw (α : M) (u : M → ℝ) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ := by
  classical
  exact fun y =>
    if y ∈ chartTargetEuclid (I := I) (M := M) α then
      u ((extChartAt I α).symm (toEuclidean.symm y))
    else 0

variable {I}
section

variable [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]


@[simp]
lemma chartPushedRaw_apply_of_mem (α : M) (u : M → ℝ)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushedRaw I α u y =
      u ((extChartAt I α).symm (toEuclidean.symm y)) := by
  classical
  unfold chartPushedRaw; simp [hy]

@[simp]
lemma chartPushedRaw_apply_of_notMem (α : M) (u : M → ℝ)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∉ chartTargetEuclid (I := I) (M := M) α) :
    chartPushedRaw I α u y = 0 := by
  classical
  unfold chartPushedRaw; simp [hy]

end

private lemma extChartAt_target_measurableSet (α : M) :
    MeasurableSet (extChartAt I α).target :=
  CalabiYau.RiemannianVolume.measurableSet_extChartAt_target
    (I := I) (M := M) α

abbrev EuclN (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
variable [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] in

private lemma toEuclidean_measurableEmbedding :
    MeasurableEmbedding (toEuclidean : E → EuclN E) :=
  (toEuclidean (E := E)).toHomeomorph.toMeasurableEquiv.measurableEmbedding
section

variable [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]


lemma chartTargetEuclid_measurableSet (α : M) :
    MeasurableSet (chartTargetEuclid (I := I) (M := M) α) := by
  unfold chartTargetEuclid
  have hT : MeasurableSet (extChartAt I α).target :=
    extChartAt_target_measurableSet (I := I) (M := M) α
  exact (toEuclidean_measurableEmbedding (E := E)).measurableSet_image.mpr hT

lemma chartTargetEuclid_eq_preimage_symm (α : M) :
    chartTargetEuclid (I := I) (M := M) α =
      (toEuclidean (E := E)).symm ⁻¹' (extChartAt I α).target := by
  unfold chartTargetEuclid
  ext y
  refine ⟨fun ⟨x, hx, hxy⟩ => ?_, fun hy => ⟨toEuclidean.symm y, hy, ?_⟩⟩
  · simp only [Set.mem_preimage]
    rw [← hxy, ContinuousLinearEquiv.symm_apply_apply]
    exact hx
  · exact (toEuclidean (E := E)).apply_symm_apply y

lemma symm_toEuclidean_symm_mem_chartAtSource (α : M)
    {y : EuclN E}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
      (chartAt H α).source := by
  rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
  have hsource : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
      (extChartAt I α).source :=
    (extChartAt I α).map_target hy
  rwa [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
    (I := I) (M := M)] at hsource

lemma continuousOn_symm_toEuclideanSymm (α : M) :
    ContinuousOn
      (fun y : EuclN E =>
        (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
      (chartTargetEuclid (I := I) (M := M) α) := by
  have hy_target : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    intro y hy
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  exact (continuousOn_extChartAt_symm (I := I) α).comp
    (toEuclidean (E := E)).symm.continuous.continuousOn hy_target

end
variable [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] in

private instance modelHaar_map_toEuclidean_isAddHaarMeasure :
    MeasureTheory.Measure.IsAddHaarMeasure
      (Measure.map (toEuclidean : E ≃L[ℝ] EuclN E)
        (CalabiYau.RiemannianVolume.modelHaar (E := E))) :=
  ContinuousLinearEquiv.isAddHaarMeasure_map
    (toEuclidean : E ≃L[ℝ] EuclN E)
    (CalabiYau.RiemannianVolume.modelHaar (E := E))
section

variable [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]


noncomputable def euclideanHaarFactor (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    ℝ≥0 :=
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  MeasureTheory.Measure.addHaarScalarFactor
    (Measure.map (toEuclidean : E → EuclN E)
      (CalabiYau.RiemannianVolume.modelHaar (E := E)))
    (volume : Measure (EuclN E))

lemma euclideanHaarFactor_pos :
    0 < euclideanHaarFactor E :=
  MeasureTheory.Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _

lemma euclideanHaarFactor_ne_zero :
    euclideanHaarFactor E ≠ 0 :=
  ne_of_gt euclideanHaarFactor_pos

lemma euclideanHaarFactor_ennreal_ne_zero :
    (euclideanHaarFactor E : ℝ≥0∞) ≠ 0 := by
  exact_mod_cast euclideanHaarFactor_ne_zero

lemma euclideanHaarFactor_ennreal_ne_top :
    (euclideanHaarFactor E : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top

end
section

variable [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


private lemma map_toEuclidean_modelHaar_eq_smul_volume :
    Measure.map (toEuclidean : E → EuclN E)
        (CalabiYau.RiemannianVolume.modelHaar (E := E)) =
      (euclideanHaarFactor E) • (volume : Measure (EuclN E)) := by
  classical
  exact MeasureTheory.Measure.isAddLeftInvariant_eq_smul _ _

private lemma lintegral_modelHaar_eq_lintegral_map_toEuclidean
    (G : E → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ x, G x ∂(CalabiYau.RiemannianVolume.modelHaar (E := E)) =
      ∫⁻ y, G ((toEuclidean (E := E)).symm y)
        ∂(Measure.map (toEuclidean : E → EuclN E)
          (CalabiYau.RiemannianVolume.modelHaar (E := E))) := by
  classical
  rw [MeasureTheory.lintegral_map
    (μ := CalabiYau.RiemannianVolume.modelHaar (E := E))
    (g := (toEuclidean : E → EuclN E))
    (f := fun y => G ((toEuclidean (E := E)).symm y))
    (hg := (toEuclidean (E := E)).continuous.measurable)
    (hf := hG.comp ((toEuclidean (E := E)).symm.continuous.measurable))]
  refine MeasureTheory.lintegral_congr (fun x => ?_)
  rw [ContinuousLinearEquiv.symm_apply_apply]

private lemma lintegral_modelHaar_eq_const_smul_lintegral_volume
    (G : E → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ x, G x ∂(CalabiYau.RiemannianVolume.modelHaar (E := E)) =
      (euclideanHaarFactor E : ℝ≥0∞) *
        ∫⁻ y, G ((toEuclidean (E := E)).symm y)
          ∂(volume : Measure (EuclN E)) := by
  classical
  rw [lintegral_modelHaar_eq_lintegral_map_toEuclidean (E := E) G hG]
  rw [map_toEuclidean_modelHaar_eq_smul_volume (E := E)]
  rw [MeasureTheory.lintegral_smul_measure]
  rfl

private noncomputable def extChartAtSymmGlob (α : M) : E → M := by
  classical
  exact (extChartAt I α).target.piecewise
    (fun y : E => (extChartAt I α).symm y)
    (fun _ : E => α)

end

private lemma extChartAtSymmGlob_eq_on_target (α : M) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    extChartAtSymmGlob (I := I) α y = (extChartAt I α).symm y := by
  classical
  change (extChartAt I α).target.piecewise
    (fun y : E => (extChartAt I α).symm y)
    (fun _ : E => α) y = _
  rw [Set.piecewise_eq_of_mem _ _ _ hy]

private lemma extChartAtSymmGlob_measurable (α : M) :
    Measurable (extChartAtSymmGlob (I := I) (M := M) α) := by
  classical
  unfold extChartAtSymmGlob
  exact ContinuousOn.measurable_piecewise
    (continuousOn_extChartAt_symm (I := I) α)
    continuousOn_const
    (extChartAt_target_measurableSet (I := I) (M := M) α)
section

variable [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


lemma chartLocalMeasure_lintegral_eq_chartTargetEuclid
    (g : CalabiYau.SmoothRiemannianMetric I M) (α : M)
    {F : M → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x ∂(CalabiYau.RiemannianVolume.chartLocalMeasure (I := I) g α) =
      (euclideanHaarFactor E : ℝ≥0∞) *
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
              (CalabiYau.RiemannianVolume.chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            F ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          ∂(volume : Measure (EuclN E)) := by
  classical
  rw [CalabiYau.RiemannianVolume.chartLocalMeasure_lintegral
    (I := I) (M := M) g α hF]
  set G_glob : E → ℝ≥0∞ := fun y =>
    ENNReal.ofReal
        (CalabiYau.RiemannianVolume.chartDensity g α
          (extChartAtSymmGlob (I := I) α y)) *
      F (extChartAtSymmGlob (I := I) α y)
  have hT : MeasurableSet (extChartAt I α).target :=
    extChartAt_target_measurableSet (I := I) (M := M) α
  have hG_glob_eq_on_target : ∀ y ∈ (extChartAt I α).target,
      G_glob y =
        ENNReal.ofReal
            (CalabiYau.RiemannianVolume.chartDensity g α
              ((extChartAt I α).symm y)) *
          F ((extChartAt I α).symm y) := by
    intro y hy
    change ENNReal.ofReal
        (CalabiYau.RiemannianVolume.chartDensity g α
          (extChartAtSymmGlob (I := I) α y)) *
      F (extChartAtSymmGlob (I := I) α y) = _
    rw [extChartAtSymmGlob_eq_on_target (I := I) (M := M) (α := α) hy]
  rw [show (∫⁻ y in (extChartAt I α).target,
        ENNReal.ofReal
            (CalabiYau.RiemannianVolume.chartDensity g α
              ((extChartAt I α).symm y)) *
          F ((extChartAt I α).symm y)
          ∂(CalabiYau.RiemannianVolume.modelHaar (E := E))) =
      ∫⁻ y in (extChartAt I α).target, G_glob y
        ∂(CalabiYau.RiemannianVolume.modelHaar (E := E))
      from MeasureTheory.setLIntegral_congr_fun hT
        (fun y hy => (hG_glob_eq_on_target y hy).symm)]
  have hsymm_glob_meas : Measurable (extChartAtSymmGlob (I := I) (M := M) α) :=
    extChartAtSymmGlob_measurable (I := I) (M := M) α
  have hF_glob_meas : Measurable
      (fun y : E => F (extChartAtSymmGlob (I := I) α y)) := hF.comp hsymm_glob_meas
  have hdens_glob_meas : Measurable
      (fun y : E =>
        CalabiYau.RiemannianVolume.chartDensity g α
          (extChartAtSymmGlob (I := I) α y)) := by
    have h_piecewise :
        (fun y : E =>
          CalabiYau.RiemannianVolume.chartDensity g α
            (extChartAtSymmGlob (I := I) α y)) =
        (extChartAt I α).target.piecewise
          (fun y : E =>
            CalabiYau.RiemannianVolume.chartDensity g α
              ((extChartAt I α).symm y))
          (fun _ : E =>
            CalabiYau.RiemannianVolume.chartDensity g α α) := by
      funext y
      by_cases hy : y ∈ (extChartAt I α).target
      · rw [Set.piecewise_eq_of_mem _ _ _ hy]
        rw [extChartAtSymmGlob_eq_on_target (I := I) (M := M) (α := α) hy]
      · rw [Set.piecewise_eq_of_notMem _ _ _ hy]
        change CalabiYau.RiemannianVolume.chartDensity g α
          ((extChartAt I α).target.piecewise
            (fun y : E => (extChartAt I α).symm y)
            (fun _ : E => α) y) = _
        rw [Set.piecewise_eq_of_notMem _ _ _ hy]
    rw [h_piecewise]
    have hsymm_cont : ContinuousOn (extChartAt I α).symm
        (extChartAt I α).target := continuousOn_extChartAt_symm (I := I) α
    have hsubset : ∀ y ∈ (extChartAt I α).target,
        (extChartAt I α).symm y ∈ (chartAt H α).source := by
      intro y hy
      have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
        (extChartAt I α).map_target hy
      rwa [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
        (I := I) (M := M)] at hsource
    have h_orig_cont : ContinuousOn
        (fun y : E =>
          CalabiYau.RiemannianVolume.chartDensity g α
            ((extChartAt I α).symm y)) (extChartAt I α).target :=
      (CalabiYau.RiemannianVolume.chartDensity_continuousOn
        (I := I) (M := M) g α).comp hsymm_cont hsubset
    exact ContinuousOn.measurable_piecewise h_orig_cont continuousOn_const hT
  have hofReal_dens_meas : Measurable
      (fun y : E => ENNReal.ofReal
        (CalabiYau.RiemannianVolume.chartDensity g α
          (extChartAtSymmGlob (I := I) α y))) :=
    ENNReal.measurable_ofReal.comp hdens_glob_meas
  have hG_glob_meas : Measurable G_glob := by
    change Measurable (fun y => ENNReal.ofReal
        (CalabiYau.RiemannianVolume.chartDensity g α
          (extChartAtSymmGlob (I := I) α y)) *
      F (extChartAtSymmGlob (I := I) α y))
    exact hofReal_dens_meas.mul hF_glob_meas
  have hG_glob_indic_meas : Measurable ((extChartAt I α).target.indicator G_glob) :=
    hG_glob_meas.indicator hT
  rw [← MeasureTheory.lintegral_indicator hT (f := G_glob)]
  rw [lintegral_modelHaar_eq_const_smul_lintegral_volume (E := E)
    (G := (extChartAt I α).target.indicator G_glob) hG_glob_indic_meas]
  congr 1
  rw [← MeasureTheory.lintegral_indicator
    (chartTargetEuclid_measurableSet (I := I) (M := M) α)]
  refine MeasureTheory.lintegral_congr (fun y => ?_)
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · have hy_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
      rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
      exact hy
    rw [Set.indicator_of_mem hy_target, Set.indicator_of_mem hy]
    change ENNReal.ofReal
        (CalabiYau.RiemannianVolume.chartDensity g α
          (extChartAtSymmGlob (I := I) α ((toEuclidean (E := E)).symm y))) *
      F (extChartAtSymmGlob (I := I) α ((toEuclidean (E := E)).symm y)) = _
    rw [extChartAtSymmGlob_eq_on_target (I := I) (M := M) (α := α) hy_target]
  · have hy_target : (toEuclidean (E := E)).symm y ∉ (extChartAt I α).target := by
      rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
      exact hy
    rw [Set.indicator_of_notMem hy_target, Set.indicator_of_notMem hy]

lemma chartDensity_pos_on_target
    (g : CalabiYau.SmoothRiemannianMetric I M) (α : M)
    {y : E} (hy : y ∈ (extChartAt I α).target) :
    0 < CalabiYau.RiemannianVolume.chartDensity g α
      ((extChartAt I α).symm y) := by
  apply CalabiYau.RiemannianVolume.chartDensity_pos
  rw [CalabiYau.RiemannianVolume.trivializationAt_baseSet_eq_chartAt_source
    (I := I) (M := M)]
  have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target hy
  rwa [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
    (I := I) (M := M)] at hsource

lemma chartDensity_symm_continuousOn_target
    (g : CalabiYau.SmoothRiemannianMetric I M) (α : M) :
    ContinuousOn
      (fun y : E =>
        CalabiYau.RiemannianVolume.chartDensity g α
          ((extChartAt I α).symm y))
      (extChartAt I α).target := by
  refine (CalabiYau.RiemannianVolume.chartDensity_continuousOn
      (I := I) (M := M) g α).comp (continuousOn_extChartAt_symm (I := I) α) ?_
  intro y hy
  have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target hy
  rwa [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
    (I := I) (M := M)] at hsource

lemma exists_sup_chartDensity_on_compact_pos
    (g : CalabiYau.SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK_compact : IsCompact K) (hKne : K.Nonempty)
    (hK_sub : K ⊆ (extChartAt I α).target) :
    ∃ M_sup : ℝ, 0 < M_sup ∧ ∀ y ∈ K,
      CalabiYau.RiemannianVolume.chartDensity g α
        ((extChartAt I α).symm y) ≤ M_sup := by
  classical
  have hdens_cont : ContinuousOn
      (fun y : E =>
        CalabiYau.RiemannianVolume.chartDensity g α
          ((extChartAt I α).symm y)) K :=
    (chartDensity_symm_continuousOn_target (I := I) (M := M) g α).mono hK_sub
  obtain ⟨y₀, hy₀_mem, hy₀_max⟩ :=
    hK_compact.exists_isMaxOn hKne hdens_cont
  refine ⟨CalabiYau.RiemannianVolume.chartDensity g α
    ((extChartAt I α).symm y₀),
    chartDensity_pos_on_target (I := I) (M := M) g α (hK_sub hy₀_mem),
    fun y hy => hy₀_max hy⟩

lemma exists_inf_chartDensity_on_compact
    (g : CalabiYau.SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK_compact : IsCompact K) (hKne : K.Nonempty)
    (hK_sub : K ⊆ (extChartAt I α).target) :
    ∃ M_inf : ℝ, 0 < M_inf ∧ ∀ y ∈ K,
      M_inf ≤ CalabiYau.RiemannianVolume.chartDensity g α
        ((extChartAt I α).symm y) := by
  classical
  have hdens_cont : ContinuousOn
      (fun y : E =>
        CalabiYau.RiemannianVolume.chartDensity g α
          ((extChartAt I α).symm y)) K :=
    (chartDensity_symm_continuousOn_target (I := I) (M := M) g α).mono hK_sub
  obtain ⟨y₀, hy₀_mem, hy₀_min⟩ :=
    hK_compact.exists_isMinOn hKne hdens_cont
  refine ⟨CalabiYau.RiemannianVolume.chartDensity g α
    ((extChartAt I α).symm y₀),
    chartDensity_pos_on_target (I := I) (M := M) g α (hK_sub hy₀_mem),
    fun y hy => hy₀_min hy⟩

end

lemma image_extChartAt_tsupport_compact_subset_target
    [CompactSpace M] {u : M → ℝ} {α : M}
    (hu_support : tsupport u ⊆ (chartAt H α).source) :
    IsCompact ((extChartAt I α) '' (tsupport u)) ∧
      (extChartAt I α) '' (tsupport u) ⊆ (extChartAt I α).target := by
  refine ⟨?_, ?_⟩
  · have hsub : tsupport u ⊆ (extChartAt I α).source := by
      intro x hx
      rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
        (I := I) (M := M)]
      exact hu_support hx
    have hcont : ContinuousOn (extChartAt I α) (tsupport u) :=
      (continuousOn_extChartAt α).mono hsub
    exact ((isClosed_tsupport _).isCompact).image_of_continuousOn hcont
  · rintro y ⟨x, hx, rfl⟩
    have hxsrc : x ∈ (extChartAt I α).source := by
      rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
        (I := I) (M := M)]
      exact hu_support hx
    exact (extChartAt I α).map_source hxsrc
section

variable [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]


lemma image_toEuclidean_extChartAt_tsupport_subset_chartTargetEuclid
    {u : M → ℝ} {α : M}
    (hu_support : tsupport u ⊆ (chartAt H α).source) :
    toEuclidean ''
      ((extChartAt I α) '' (tsupport (u : M → ℝ))) ⊆
      chartTargetEuclid (I := I) (M := M) α := by
  rintro y ⟨z, hz, rfl⟩
  rcases hz with ⟨x, hx, hxz⟩
  refine ⟨z, ?_, rfl⟩
  rw [← hxz]
  have hxsrc : x ∈ (extChartAt I α).source := by
    rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
      (I := I) (M := M)]
    exact hu_support hx
  exact (extChartAt I α).map_source hxsrc

lemma chartPushedRaw_eq_zero_off_image_tsupport
    {u : M → ℝ} (α : M)
    {y : EuclN E} (hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α)
    (hy_off : y ∉ toEuclidean '' ((extChartAt I α) '' (tsupport u))) :
    chartPushedRaw I α u y = 0 := by
  classical
  obtain ⟨z, hz_target, hzy⟩ := hy_target
  have hsymm_source : (extChartAt I α).symm z ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target hz_target
  have hz_eq : (extChartAt I α) ((extChartAt I α).symm z) = z :=
    (extChartAt I α).right_inv hz_target
  have hy_symm : (toEuclidean (E := E)).symm y = z := by
    rw [← hzy]; exact (toEuclidean (E := E)).symm_apply_apply z
  have hy_target' : y ∈ chartTargetEuclid (I := I) (M := M) α := ⟨z, hz_target, hzy⟩
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α u hy_target']
  rw [hy_symm]
  by_contra hu_ne
  apply hy_off
  refine ⟨z, ⟨(extChartAt I α).symm z, ?_, hz_eq⟩, hzy⟩
  exact subset_tsupport _ (Function.mem_support.mpr hu_ne)

end
section

variable [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


lemma lintegral_enorm_pow_riemannianMeasure_eq_chartLocalMeasure_of_supportIn
    [T2Space M] [CompactSpace M]
    (g : CalabiYau.SmoothRiemannianMetric I M) (α : M)
    {u : M → ℝ} (hu_meas : Measurable u)
    (hu_support : tsupport u ⊆ (chartAt H α).source)
    {p : ℝ} (hp_pos : 0 < p) :
    ∫⁻ x, ‖u x‖ₑ ^ p
        ∂(CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M)) =
      ∫⁻ x, ‖u x‖ₑ ^ p
        ∂(CalabiYau.RiemannianVolume.chartLocalMeasure (I := I) g α) := by
  classical
  apply riemannianMeasure_lintegral_eq_chartLocalMeasure_of_supportIn (I := I) (M := M) g α
  · exact (hu_meas.enorm).pow_const p
  · intro x hx
    have hx_notsupp : x ∉ tsupport u := fun hcontra => hx (hu_support hcontra)
    have hu_x_zero : u x = 0 := image_eq_zero_of_notMem_tsupport hx_notsupp
    rw [hu_x_zero]
    rw [enorm_zero, ENNReal.zero_rpow_of_pos hp_pos]

lemma lintegral_enorm_pow_riemannianMeasure_eq_const_mul_chartTargetEuclid
    [T2Space M] [CompactSpace M]
    (g : CalabiYau.SmoothRiemannianMetric I M) (α : M)
    {u : M → ℝ} (hu_meas : Measurable u)
    (hu_support : tsupport u ⊆ (chartAt H α).source)
    {p : ℝ} (hp_pos : 0 < p) :
    ∫⁻ x, ‖u x‖ₑ ^ p
        ∂(CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M)) =
      (euclideanHaarFactor E : ℝ≥0∞) *
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
              (CalabiYau.RiemannianVolume.chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            ‖chartPushedRaw I α u y‖ₑ ^ p
          ∂(volume : Measure (EuclN E)) := by
  classical
  rw [lintegral_enorm_pow_riemannianMeasure_eq_chartLocalMeasure_of_supportIn
      (I := I) (M := M) g α hu_meas hu_support hp_pos]
  rw [chartLocalMeasure_lintegral_eq_chartTargetEuclid (I := I) (M := M) g α
    (F := fun x => ‖u x‖ₑ ^ p) ((hu_meas.enorm).pow_const p)]
  congr 1
  refine MeasureTheory.setLIntegral_congr_fun
    (chartTargetEuclid_measurableSet (I := I) (M := M) α) ?_
  intro y hy
  change ENNReal.ofReal _ * ‖u ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ₑ ^ p =
    ENNReal.ofReal _ * ‖chartPushedRaw I α u y‖ₑ ^ p
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α u hy]

theorem lintegral_riemannianMeasure_le_const_mul_lintegral_chartPushedRaw_uniform
    [T2Space M] [CompactSpace M]
    (g : CalabiYau.SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK_compact : IsCompact K) (hK_ne : K.Nonempty)
    (hK_sub : K ⊆ (extChartAt I α).target) :
    ∃ C_K : ℝ, 0 < C_K ∧ ∀ {u : M → ℝ}, Measurable u →
      tsupport u ⊆ (chartAt H α).source →
      (extChartAt I α) '' (tsupport u) ⊆ K →
      ∀ {p : ℝ}, 0 < p →
      ∫⁻ x, ‖u x‖ₑ ^ p
          ∂(CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
              (CalabiYau.RiemannianVolume.chartAtlasPOU I M))
        ≤ ENNReal.ofReal C_K *
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ‖chartPushedRaw I α u y‖ₑ ^ p
              ∂(volume : Measure (EuclN E)) := by
  classical
  obtain ⟨M_sup, hM_sup_pos, hM_sup_le⟩ :=
    exists_sup_chartDensity_on_compact_pos (I := I) (M := M) g α hK_compact hK_ne hK_sub
  set C_K : ℝ := (euclideanHaarFactor E : ℝ) * M_sup with hC_K_def
  have hC_K_pos : 0 < C_K := by
    apply mul_pos
    · exact_mod_cast euclideanHaarFactor_pos
    · exact hM_sup_pos
  refine ⟨C_K, hC_K_pos, ?_⟩
  intro u hu_meas hu_support hu_support_K p hp_pos
  rw [lintegral_enorm_pow_riemannianMeasure_eq_const_mul_chartTargetEuclid
      (I := I) (M := M) g α hu_meas hu_support hp_pos]
  set K_eucl : Set (EuclN E) :=
    (toEuclidean : E ≃L[ℝ] EuclN E) '' ((extChartAt I α) '' (tsupport u))
    with hK_eucl_def
  have hpt : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      ENNReal.ofReal
          (CalabiYau.RiemannianVolume.chartDensity g α
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
        ‖chartPushedRaw I α u y‖ₑ ^ p
      ≤ ENNReal.ofReal M_sup * ‖chartPushedRaw I α u y‖ₑ ^ p := by
    intro y hy_target
    by_cases hy_K_eucl : y ∈ K_eucl
    · obtain ⟨z_E, hz_E_chart, hz_Ey⟩ := hy_K_eucl
      have hz_in_K : z_E ∈ K := hu_support_K hz_E_chart
      have hz_target : z_E ∈ (extChartAt I α).target := hK_sub hz_in_K
      have hsym_eq : (toEuclidean (E := E)).symm y = z_E := by
        rw [← hz_Ey]; exact (toEuclidean (E := E)).symm_apply_apply z_E
      have hbound :
          CalabiYau.RiemannianVolume.chartDensity g α
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
            ≤ M_sup := by
        rw [hsym_eq]; exact hM_sup_le z_E hz_in_K
      have h_density_le :
          ENNReal.ofReal
              (CalabiYau.RiemannianVolume.chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
            ≤ ENNReal.ofReal M_sup :=
        ENNReal.ofReal_le_ofReal hbound
      gcongr
    · have hpr_zero : chartPushedRaw I α u y = 0 :=
        chartPushedRaw_eq_zero_off_image_tsupport
          (I := I) (M := M) (u := u) α hy_target hy_K_eucl
      rw [hpr_zero, enorm_zero, ENNReal.zero_rpow_of_pos hp_pos]
      simp
  calc (euclideanHaarFactor E : ℝ≥0∞) *
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
              (CalabiYau.RiemannianVolume.chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            ‖chartPushedRaw I α u y‖ₑ ^ p
          ∂(volume : Measure (EuclN E))
      ≤ (euclideanHaarFactor E : ℝ≥0∞) *
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal M_sup * ‖chartPushedRaw I α u y‖ₑ ^ p
            ∂(volume : Measure (EuclN E)) := by
        have h_int_le : (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                  (CalabiYau.RiemannianVolume.chartDensity g α
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                ‖chartPushedRaw I α u y‖ₑ ^ p
              ∂(volume : Measure (EuclN E)))
            ≤ (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal M_sup * ‖chartPushedRaw I α u y‖ₑ ^ p
              ∂(volume : Measure (EuclN E))) :=
          MeasureTheory.setLIntegral_mono_ae'
            (chartTargetEuclid_measurableSet (I := I) (M := M) α)
            (Filter.Eventually.of_forall hpt)
        gcongr
    _ = (euclideanHaarFactor E : ℝ≥0∞) * ENNReal.ofReal M_sup *
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ‖chartPushedRaw I α u y‖ₑ ^ p
            ∂(volume : Measure (EuclN E)) := by
        rw [MeasureTheory.lintegral_const_mul']
        · ring
        · exact ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal C_K *
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ‖chartPushedRaw I α u y‖ₑ ^ p
            ∂(volume : Measure (EuclN E)) := by
        congr 1
        rw [hC_K_def]
        rw [ENNReal.ofReal_mul]
        · congr 1
          rw [ENNReal.ofReal_coe_nnreal]
        · exact NNReal.coe_nonneg _

omit [IsManifold I ∞ M] in
private lemma aestronglyMeasurable_chartPushedRaw_restrict
    (α : M) {u : M → ℝ} (hu : Measurable u) :
    AEStronglyMeasurable (chartPushedRaw I α u)
      ((volume : Measure (EuclN E)).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  let g : E → M := (extChartAt I α).target.piecewise
    (fun y => (extChartAt I α).symm y) (fun _ => α)
  have hg : Measurable g :=
    ContinuousOn.measurable_piecewise
      (continuousOn_extChartAt_symm (I := I) α) continuousOn_const
      (extChartAt_target_measurableSet (I := I) (M := M) α)
  have hcomp : Measurable (fun y : EuclN E => u (g ((toEuclidean (E := E)).symm y))) :=
    hu.comp (hg.comp (toEuclidean (E := E)).symm.continuous.measurable)
  refine hcomp.aestronglyMeasurable.restrict.congr ?_
  filter_upwards [ae_restrict_mem
    (chartTargetEuclid_measurableSet (I := I) (M := M) α)] with y hy
  rw [chartPushedRaw_apply_of_mem (I := I) α u hy]
  have htarget : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rcases hy with ⟨z, hz, rfl⟩
    simpa using hz
  simp only [g, Set.piecewise_eq_of_mem _ _ _ htarget]

theorem eLpNorm_riemannianMeasure_le_const_mul_eLpNorm_chartPushedRaw_uniform
    [T2Space M] [CompactSpace M]
    (g : CalabiYau.SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK_compact : IsCompact K) (hK_ne : K.Nonempty)
    (hK_sub : K ⊆ (extChartAt I α).target)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞)) :
    ∃ C_K : ℝ, 0 < C_K ∧ ∀ {u : M → ℝ}, Measurable u →
      tsupport u ⊆ (chartAt H α).source →
      (extChartAt I α) '' (tsupport u) ⊆ K →
      eLpNorm u p
          (CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M))
        ≤ ENNReal.ofReal C_K *
            eLpNorm (chartPushedRaw I α u) p
              ((volume : Measure (EuclN E)).restrict
                (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have hp_ne_zero : p ≠ 0 := by
    intro h; rw [h] at hp_one; exact absurd hp_one (by norm_num)
  have hp_toReal_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_top
  obtain ⟨C, hC_pos, hC_bnd⟩ :=
    lintegral_riemannianMeasure_le_const_mul_lintegral_chartPushedRaw_uniform
      (I := I) (M := M) g α hK_compact hK_ne hK_sub
  refine ⟨C ^ (1 / p.toReal), Real.rpow_pos_of_pos hC_pos _, ?_⟩
  intro u hu_meas hu_support hu_K
  have hu_aem := hu_meas.aestronglyMeasurable (μ :=
    CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M))
  have hchart_aem := aestronglyMeasurable_chartPushedRaw_restrict (I := I) α hu_meas
  have h_lint := hC_bnd hu_meas hu_support hu_K hp_toReal_pos
  have h_lint' :
      ∫⁻ x, ‖u x‖ₑ ^ p.toReal
          ∂(CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
              (CalabiYau.RiemannianVolume.chartAtlasPOU I M))
        ≤ ENNReal.ofReal C *
            ∫⁻ y, ‖chartPushedRaw I α u y‖ₑ ^ p.toReal
              ∂((volume : Measure (EuclN E)).restrict
                (chartTargetEuclid (I := I) (M := M) α)) := h_lint
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_top hu_aem]
  have h_pow_le :
      (∫⁻ x, ‖u x‖ₑ ^ p.toReal
          ∂(CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
              (CalabiYau.RiemannianVolume.chartAtlasPOU I M))) ^
            (1 / p.toReal)
        ≤ (ENNReal.ofReal C *
            ∫⁻ y, ‖chartPushedRaw I α u y‖ₑ ^ p.toReal
              ∂((volume : Measure (EuclN E)).restrict
                (chartTargetEuclid (I := I) (M := M) α))) ^
              (1 / p.toReal) := by
    apply ENNReal.rpow_le_rpow h_lint'
    positivity
  refine h_pow_le.trans ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / p.toReal)]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_top hchart_aem]
  gcongr
  rw [← ENNReal.ofReal_rpow_of_pos hC_pos]

end

end Chart
end Sobolev

noncomputable section

namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
section

variable [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


theorem lintegral_chartPushedRaw_le_const_mul_lintegral_riemannianMeasure_uniform
    [T2Space M] [CompactSpace M]
    (g : CalabiYau.SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK_compact : IsCompact K) (hK_ne : K.Nonempty)
    (hK_sub : K ⊆ (extChartAt I α).target) :
    ∃ C_K : ℝ, 0 < C_K ∧ ∀ {u : M → ℝ}, Measurable u →
      tsupport u ⊆ (chartAt H α).source →
      (extChartAt I α) '' (tsupport u) ⊆ K →
      ∀ {p : ℝ}, 0 < p →
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ‖chartPushedRaw I α u y‖ₑ ^ p
          ∂(volume : Measure
            (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
        ≤ ENNReal.ofReal C_K *
            ∫⁻ x, ‖u x‖ₑ ^ p
              ∂(CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
                  (CalabiYau.RiemannianVolume.chartAtlasPOU I M)) := by
  classical
  obtain ⟨M_inf, hM_inf_pos, hM_inf_le⟩ :=
    exists_inf_chartDensity_on_compact (I := I) (M := M) g α hK_compact hK_ne hK_sub
  set C_K : ℝ := ((euclideanHaarFactor E : ℝ) * M_inf)⁻¹ with hC_K_def
  have hC_K_pos : 0 < C_K := by
    rw [hC_K_def]
    apply inv_pos.mpr
    apply mul_pos
    · exact_mod_cast euclideanHaarFactor_pos
    · exact hM_inf_pos
  refine ⟨C_K, hC_K_pos, ?_⟩
  intro u hu_meas hu_support hu_support_K p hp_pos
  rw [lintegral_enorm_pow_riemannianMeasure_eq_const_mul_chartTargetEuclid
      (I := I) (M := M) g α hu_meas hu_support hp_pos]
  set K_eucl : Set (EuclN E) := toEuclidean ''
    ((extChartAt I α) '' (tsupport u)) with hK_eucl_def
  have hpt : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      ENNReal.ofReal (M_inf) * ‖chartPushedRaw I α u y‖ₑ ^ p
        ≤ ENNReal.ofReal
            (CalabiYau.RiemannianVolume.chartDensity g α
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          ‖chartPushedRaw I α u y‖ₑ ^ p := by
    intro y hy_target
    by_cases hy_K_eucl : y ∈ K_eucl
    · obtain ⟨z_E, hz_E_chart, hz_Ey⟩ := hy_K_eucl
      have hz_in_K : z_E ∈ K := hu_support_K hz_E_chart
      have hz_target : z_E ∈ (extChartAt I α).target := hK_sub hz_in_K
      have hsym_eq : (toEuclidean (E := E)).symm y = z_E := by
        rw [← hz_Ey]; exact (toEuclidean (E := E)).symm_apply_apply z_E
      have hbound :
          M_inf ≤
          CalabiYau.RiemannianVolume.chartDensity g α
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
        rw [hsym_eq]; exact hM_inf_le z_E hz_in_K
      have h_density_ge :
          ENNReal.ofReal M_inf
            ≤ ENNReal.ofReal
            (CalabiYau.RiemannianVolume.chartDensity g α
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) :=
        ENNReal.ofReal_le_ofReal hbound
      gcongr
    · have hpr_zero : chartPushedRaw I α u y = 0 :=
        chartPushedRaw_eq_zero_off_image_tsupport
          (I := I) (M := M) (u := u) α hy_target hy_K_eucl
      rw [hpr_zero, enorm_zero, ENNReal.zero_rpow_of_pos hp_pos]
      simp
  have h_int_le :
      (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal M_inf * ‖chartPushedRaw I α u y‖ₑ ^ p
          ∂(volume : Measure (EuclN E)))
        ≤ (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
                (CalabiYau.RiemannianVolume.chartDensity g α
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              ‖chartPushedRaw I α u y‖ₑ ^ p
            ∂(volume : Measure (EuclN E))) :=
    MeasureTheory.setLIntegral_mono_ae'
      (chartTargetEuclid_measurableSet (I := I) (M := M) α)
      (Filter.Eventually.of_forall hpt)
  have h_LHS_eq :
      (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal M_inf * ‖chartPushedRaw I α u y‖ₑ ^ p
          ∂(volume : Measure (EuclN E))) =
        ENNReal.ofReal M_inf *
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ‖chartPushedRaw I α u y‖ₑ ^ p
            ∂(volume : Measure (EuclN E)) := by
    rw [MeasureTheory.lintegral_const_mul']
    exact ENNReal.ofReal_ne_top
  rw [h_LHS_eq] at h_int_le
  have hM_inf_ennreal_pos : (ENNReal.ofReal M_inf : ℝ≥0∞) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hM_inf_pos
  have hM_inf_ennreal_ne_top : (ENNReal.ofReal M_inf : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  set D : ℝ≥0∞ := (euclideanHaarFactor E : ℝ≥0∞) * ENNReal.ofReal M_inf with hD_def
  have hD_pos : D ≠ 0 :=
    mul_ne_zero euclideanHaarFactor_ennreal_ne_zero hM_inf_ennreal_pos
  have hD_ne_top : D ≠ ⊤ :=
    ENNReal.mul_ne_top euclideanHaarFactor_ennreal_ne_top hM_inf_ennreal_ne_top
  have hC_eq_D_inv : ENNReal.ofReal C_K = D⁻¹ := by
    rw [hC_K_def, hD_def]
    have h_prod_pos : 0 < (euclideanHaarFactor E : ℝ) * M_inf := by
      apply mul_pos
      · exact_mod_cast euclideanHaarFactor_pos
      · exact hM_inf_pos
    rw [show ((euclideanHaarFactor E : ℝ) * M_inf)⁻¹ =
          (1 : ℝ) / ((euclideanHaarFactor E : ℝ) * M_inf) from by rw [one_div]]
    rw [ENNReal.ofReal_div_of_pos h_prod_pos]
    rw [ENNReal.ofReal_one]
    rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
    rw [ENNReal.ofReal_coe_nnreal]
    rw [one_div]
  rw [hC_eq_D_inv]
  have h_step :
      D * (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ‖chartPushedRaw I α u y‖ₑ ^ p ∂(volume : Measure (EuclN E)))
        ≤ (euclideanHaarFactor E : ℝ≥0∞) *
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
                (CalabiYau.RiemannianVolume.chartDensity g α
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              ‖chartPushedRaw I α u y‖ₑ ^ p
            ∂(volume : Measure (EuclN E)) := by
    rw [hD_def, mul_assoc]
    gcongr
  rwa [ENNReal.mul_le_iff_le_inv hD_pos hD_ne_top] at h_step

theorem eLpNorm_chartPushedRaw_le_const_mul_eLpNorm_riemannianMeasure_uniform
    [T2Space M] [CompactSpace M]
    (g : CalabiYau.SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK_compact : IsCompact K) (hK_ne : K.Nonempty)
    (hK_sub : K ⊆ (extChartAt I α).target)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞)) :
    ∃ C_K : ℝ, 0 < C_K ∧ ∀ {u : M → ℝ}, Measurable u →
      tsupport u ⊆ (chartAt H α).source →
      (extChartAt I α) '' (tsupport u) ⊆ K →
      eLpNorm (chartPushedRaw I α u) p
          ((volume : Measure (EuclN E)).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C_K *
            eLpNorm u p
              (CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
                (CalabiYau.RiemannianVolume.chartAtlasPOU I M)) := by
  classical
  have hp_ne_zero : p ≠ 0 := by
    intro h; rw [h] at hp_one; exact absurd hp_one (by norm_num)
  have hp_toReal_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_top
  obtain ⟨C, hC_pos, hC_bnd⟩ :=
    lintegral_chartPushedRaw_le_const_mul_lintegral_riemannianMeasure_uniform
      (I := I) (M := M) g α hK_compact hK_ne hK_sub
  refine ⟨C ^ (1 / p.toReal), Real.rpow_pos_of_pos hC_pos _, ?_⟩
  intro u hu_meas hu_support hu_K
  have hu_aem := hu_meas.aestronglyMeasurable (μ :=
    CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M))
  have hchart_aem := aestronglyMeasurable_chartPushedRaw_restrict (I := I) α hu_meas
  have h_lint := hC_bnd hu_meas hu_support hu_K hp_toReal_pos
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_top hchart_aem]
  have h_LHS_eq :
      (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        ‖chartPushedRaw I α u y‖ₑ ^ p.toReal
        ∂(volume : Measure (EuclN E))) =
      ∫⁻ y, ‖chartPushedRaw I α u y‖ₑ ^ p.toReal
        ∂((volume : Measure (EuclN E)).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := rfl
  rw [h_LHS_eq] at h_lint
  have h_pow_le :
      (∫⁻ y, ‖chartPushedRaw I α u y‖ₑ ^ p.toReal
          ∂((volume : Measure (EuclN E)).restrict
            (chartTargetEuclid (I := I) (M := M) α))) ^
            (1 / p.toReal)
        ≤ (ENNReal.ofReal C *
            ∫⁻ x, ‖u x‖ₑ ^ p.toReal
              ∂(CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
                  (CalabiYau.RiemannianVolume.chartAtlasPOU I M))) ^
              (1 / p.toReal) := by
    apply ENNReal.rpow_le_rpow h_lint
    positivity
  refine h_pow_le.trans ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / p.toReal)]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_top hu_aem]
  gcongr
  rw [← ENNReal.ofReal_rpow_of_pos hC_pos]

private noncomputable def extChartAtSymmGlobal (α : M) : E → M := by
  classical
  exact (extChartAt I α).target.piecewise
    (fun y : E => (extChartAt I α).symm y)
    (fun _ : E => α)

end

private lemma extChartAtSymmGlobal_eq_on_target (α : M) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    extChartAtSymmGlobal (I := I) (M := M) α y = (extChartAt I α).symm y := by
  classical
  change (extChartAt I α).target.piecewise
    (fun y : E => (extChartAt I α).symm y)
    (fun _ : E => α) y = _
  rw [Set.piecewise_eq_of_mem _ _ _ hy]

private lemma extChartAtSymmGlobal_measurable (α : M) :
    Measurable (extChartAtSymmGlobal (I := I) (M := M) α) := by
  classical
  unfold extChartAtSymmGlobal
  exact ContinuousOn.measurable_piecewise
    (continuousOn_extChartAt_symm (I := I) α)
    continuousOn_const
    (extChartAt_target_measurableSet (I := I) (M := M) α)
section

variable [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]


lemma chartPushedRaw_measurable (α : M) {F : M → ℝ}
    (hF_meas : Measurable F) :
    Measurable (chartPushedRaw I α F) := by
  classical
  have h_extSymm_meas : Measurable (extChartAtSymmGlobal (I := I) (M := M) α) :=
    extChartAtSymmGlobal_measurable (I := I) (M := M) α
  have h_comp : Measurable
      (fun y : EuclN E =>
        F (extChartAtSymmGlobal (I := I) (M := M) α
          ((toEuclidean (E := E)).symm y))) :=
    hF_meas.comp (h_extSymm_meas.comp
      (toEuclidean (E := E)).symm.continuous.measurable)
  have hCT_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_measurableSet (I := I) (M := M) α
  have h_piecewise :
      chartPushedRaw I α F =
        (chartTargetEuclid (I := I) (M := M) α).piecewise
          (fun y : EuclN E =>
            F (extChartAtSymmGlobal (I := I) (M := M) α
              ((toEuclidean (E := E)).symm y)))
          (fun _ : EuclN E => (0 : ℝ)) := by
    funext y
    by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
    · rw [Set.piecewise_eq_of_mem _ _ _ hy]
      rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α F hy]
      have h_toE_symm_in : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
        rcases hy with ⟨w, hw_target, hwy⟩
        have h_eq : (toEuclidean (E := E)).symm y = w := by
          rw [← hwy]; exact (toEuclidean (E := E)).symm_apply_apply w
        rw [h_eq]; exact hw_target
      rw [extChartAtSymmGlobal_eq_on_target (I := I) (M := M) α h_toE_symm_in]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hy]
      rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α F hy]
  rw [h_piecewise]
  exact Measurable.piecewise hCT_meas h_comp measurable_const

private lemma toEuclidean_symm_target_of_mem (α : M) {y : EuclN E}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
  rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
  exact hy

private lemma chartPushedRaw_sub_pointwise (α : M) (u v : M → ℝ)
    {y : EuclN E} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushedRaw I α (fun x => u x - v x) y =
      chartPushedRaw I α u y - chartPushedRaw I α v y := by
  classical
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α (fun x => u x - v x) hy]
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α u hy]
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α v hy]

end
section

variable [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


private lemma chartPushedRaw_aeEq_zero_of_ae_zero_riemannianMeasure
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : CalabiYau.SmoothRiemannianMetric I M) (α : M)
    {d : M → ℝ} (hd_meas : Measurable d)
    (hd_ae : d =ᵐ[CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M)] (fun _ => (0 : ℝ))) :
    chartPushedRaw I α d =ᵐ[
        (volume : Measure (EuclN E)).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)) := by
  classical
  have h_chartSource_meas : MeasurableSet (chartAt H α).source :=
    (chartAt H α).open_source.measurableSet
  set F : M → ℝ≥0∞ := fun x =>
    (chartAt H α).source.indicator (fun x => ‖d x‖ₑ ^ (2 : ℝ)) x with hF_def
  have hF_meas : Measurable F :=
    ((hd_meas.enorm).pow_const _).indicator h_chartSource_meas
  have hF_zero_off : ∀ x, x ∉ (chartAt H α).source → F x = 0 := fun x hx =>
    Set.indicator_of_notMem hx _
  have h_lint_F_riemannian_zero :
      ∫⁻ x, F x ∂(CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M)) = 0 := by
    have h_F_ae_zero : F =ᵐ[CalabiYau.RiemannianVolume.riemannianMeasure
        (I := I) g (CalabiYau.RiemannianVolume.chartAtlasPOU I M)]
        (fun _ : M => (0 : ℝ≥0∞)) := by
      filter_upwards [hd_ae] with x hx
      have hxz : d x = 0 := hx
      change (chartAt H α).source.indicator (fun x => ‖d x‖ₑ ^ (2 : ℝ)) x = 0
      by_cases hxsrc : x ∈ (chartAt H α).source
      · rw [Set.indicator_of_mem hxsrc]
        rw [hxz, enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
      · rw [Set.indicator_of_notMem hxsrc]
    rw [MeasureTheory.lintegral_congr_ae h_F_ae_zero]
    simp
  have h_lint_F_chartLocal_eq :
      ∫⁻ x, F x ∂(CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M)) =
        ∫⁻ x, F x ∂(CalabiYau.RiemannianVolume.chartLocalMeasure (I := I) g α) :=
    riemannianMeasure_lintegral_eq_chartLocalMeasure_of_supportIn
      (I := I) (M := M) g α hF_meas hF_zero_off
  have h_lint_F_chartLocal_zero :
      ∫⁻ x, F x ∂(CalabiYau.RiemannianVolume.chartLocalMeasure (I := I) g α) = 0 := by
    rw [← h_lint_F_chartLocal_eq]; exact h_lint_F_riemannian_zero
  have h_chartLocal_offSource_zero :
      (CalabiYau.RiemannianVolume.chartLocalMeasure (I := I) g α)
          ((chartAt H α).source)ᶜ = 0 :=
    CalabiYau.RiemannianVolume.chartLocalMeasure_apply_of_disjoint_source
      (I := I) g α h_chartSource_meas.compl disjoint_compl_left
  have h_F_eq_norm_sq_ae :
      F =ᵐ[CalabiYau.RiemannianVolume.chartLocalMeasure (I := I) g α]
        (fun x => ‖d x‖ₑ ^ (2 : ℝ)) := by
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_ h_chartLocal_offSource_zero
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    by_cases hxsrc : x ∈ (chartAt H α).source
    · exfalso
      apply hx
      change (chartAt H α).source.indicator (fun x => ‖d x‖ₑ ^ (2 : ℝ)) x =
        ‖d x‖ₑ ^ (2 : ℝ)
      rw [Set.indicator_of_mem hxsrc]
    · exact hxsrc
  have h_lint_d_chartLocal_zero :
      ∫⁻ x, ‖d x‖ₑ ^ (2 : ℝ)
          ∂(CalabiYau.RiemannianVolume.chartLocalMeasure (I := I) g α) = 0 := by
    rw [← MeasureTheory.lintegral_congr_ae h_F_eq_norm_sq_ae]
    exact h_lint_F_chartLocal_zero
  have h_norm_sq_meas : Measurable (fun x : M => ‖d x‖ₑ ^ (2 : ℝ)) :=
    (hd_meas.enorm).pow_const _
  have h_bridge :=
    chartLocalMeasure_lintegral_eq_chartTargetEuclid (I := I) (M := M) g α h_norm_sq_meas
  rw [h_lint_d_chartLocal_zero] at h_bridge
  set GG : EuclN E → ℝ≥0∞ := fun y =>
    ENNReal.ofReal
        (CalabiYau.RiemannianVolume.chartDensity g α
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
      ‖d ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ₑ ^ (2 : ℝ) with hGG_def
  have hbr2 :
      (euclideanHaarFactor E : ℝ≥0∞) *
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α, GG y
          ∂(volume : Measure (EuclN E)) = 0 :=
    h_bridge.symm
  have h_c_E_ne_zero : (euclideanHaarFactor E : ℝ≥0∞) ≠ 0 := euclideanHaarFactor_ennreal_ne_zero
  have h_inner_zero :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α, GG y
        ∂(volume : Measure (EuclN E)) = 0 := by
    rcases mul_eq_zero.mp hbr2 with h | h
    · exact absurd h h_c_E_ne_zero
    · exact h
  have h_chartTarget_meas :
      MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_measurableSet (I := I) (M := M) α
  have hGG_aem : AEMeasurable GG
      ((volume : Measure (EuclN E)).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
    have h_density_contOn : ContinuousOn
        (fun y : EuclN E =>
          CalabiYau.RiemannianVolume.chartDensity g α
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        (chartTargetEuclid (I := I) (M := M) α) := by
      refine (CalabiYau.RiemannianVolume.chartDensity_continuousOn
        (I := I) (M := M) g α).comp
          (continuousOn_symm_toEuclideanSymm (I := I) (M := M) α) ?_
      intro y hy
      exact symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
    have h_density_aem : AEMeasurable
        (fun y : EuclN E =>
          CalabiYau.RiemannianVolume.chartDensity g α
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        ((volume : Measure (EuclN E)).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      h_density_contOn.aemeasurable h_chartTarget_meas
    have h_ofReal_dens_aem : AEMeasurable
        (fun y : EuclN E => ENNReal.ofReal
          (CalabiYau.RiemannianVolume.chartDensity g α
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))))
        ((volume : Measure (EuclN E)).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      ENNReal.measurable_ofReal.comp_aemeasurable h_density_aem
    have h_d_symm_meas : Measurable (fun y : EuclN E =>
        d (extChartAtSymmGlobal (I := I) (M := M) α ((toEuclidean (E := E)).symm y))) :=
      hd_meas.comp ((extChartAtSymmGlobal_measurable (I := I) (M := M) α).comp
        (toEuclidean (E := E)).symm.continuous.measurable)
    have h_d_global_aem : AEMeasurable (fun y : EuclN E =>
        ‖d (extChartAtSymmGlobal (I := I) (M := M) α ((toEuclidean (E := E)).symm y))‖ₑ
          ^ (2 : ℝ)) := (h_d_symm_meas.enorm.pow_const _).aemeasurable
    have h_d_norm_aem : AEMeasurable
        (fun y : EuclN E => ‖d ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ₑ
          ^ (2 : ℝ))
        ((volume : Measure (EuclN E)).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
      refine AEMeasurable.congr (h_d_global_aem.mono_measure ?_) ?_
      · exact MeasureTheory.Measure.restrict_le_self
      · rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' h_chartTarget_meas]
        refine Filter.Eventually.of_forall (fun y hy => ?_)
        congr 1
        congr 1
        rw [extChartAtSymmGlobal_eq_on_target (I := I) (M := M) α
          (toEuclidean_symm_target_of_mem (I := I) (M := M) α hy)]
    exact h_ofReal_dens_aem.mul h_d_norm_aem
  have h_GG_ae_zero : ∀ᵐ y ∂((volume : Measure (EuclN E)).restrict
      (chartTargetEuclid (I := I) (M := M) α)), GG y = 0 :=
    (MeasureTheory.lintegral_eq_zero_iff' hGG_aem).mp h_inner_zero
  have h_density_pos_ae :
      ∀ᵐ y ∂((volume : Measure (EuclN E)).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
        (0 : ℝ≥0∞) < ENNReal.ofReal
          (CalabiYau.RiemannianVolume.chartDensity g α
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) := by
    rw [MeasureTheory.ae_restrict_iff' h_chartTarget_meas]
    refine Filter.Eventually.of_forall fun y hy => ?_
    refine ENNReal.ofReal_pos.mpr ?_
    refine chartDensity_pos_on_target (I := I) (M := M) g α ?_
    exact toEuclidean_symm_target_of_mem (I := I) (M := M) α hy
  have h_d_norm_ae_zero : ∀ᵐ y ∂((volume : Measure (EuclN E)).restrict
      (chartTargetEuclid (I := I) (M := M) α)),
      ‖d ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ₑ ^ (2 : ℝ) = 0 := by
    filter_upwards [h_GG_ae_zero, h_density_pos_ae] with y hy h_pos
    rcases mul_eq_zero.mp hy with h | h
    · exact absurd h h_pos.ne'
    · exact h
  have h_d_zero_ae : ∀ᵐ y ∂((volume : Measure (EuclN E)).restrict
      (chartTargetEuclid (I := I) (M := M) α)),
      d ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) = 0 := by
    filter_upwards [h_d_norm_ae_zero] with y hy
    have h_pow := ENNReal.rpow_eq_zero_iff.mp hy
    rcases h_pow with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact (enorm_eq_zero (a :=
        d ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))).mp h1
    · exact absurd h2 (by norm_num)
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' h_chartTarget_meas]
  rw [MeasureTheory.ae_restrict_iff' h_chartTarget_meas] at h_d_zero_ae
  filter_upwards [h_d_zero_ae] with y hy hy_in
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α d hy_in]
  exact hy hy_in

theorem chartPushedRaw_aeEq_of_ae_eq_riemannianMeasure
    [T2Space M] [CompactSpace M]
    (g : CalabiYau.SmoothRiemannianMetric I M) (α : M)
    {u v : M → ℝ}
    (h_meas_u : Measurable u) (h_meas_v : Measurable v)
    (h_ae : u =ᵐ[CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M)] v) :
    chartPushedRaw I α u =ᵐ[
        (volume : Measure (EuclN E)).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      chartPushedRaw I α v := by
  classical
  set d : M → ℝ := fun x => u x - v x with hd_def
  have hd_meas : Measurable d := h_meas_u.sub h_meas_v
  have hd_ae_zero : d =ᵐ[CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M)] (fun _ => (0 : ℝ)) := by
    filter_upwards [h_ae] with x hx
    change u x - v x = 0
    rw [hx, sub_self]
  have h_main :=
    chartPushedRaw_aeEq_zero_of_ae_zero_riemannianMeasure
      (I := I) (M := M) g α hd_meas hd_ae_zero
  have h_chartTarget_meas :
      MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_measurableSet (I := I) (M := M) α
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' h_chartTarget_meas]
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' h_chartTarget_meas] at h_main
  filter_upwards [h_main] with y hy hy_in
  rw [chartPushedRaw_sub_pointwise (I := I) (M := M) α u v hy_in] at hy
  have hyz := hy hy_in
  linarith [sub_eq_zero.mp hyz]

theorem chartPushed_aeEq_of_ae_eq_riemannianMeasure
    [T2Space M] [CompactSpace M]
    (g : CalabiYau.SmoothRiemannianMetric I M) (α : M)
    {u v : M → ℝ}
    (h_meas_u : Measurable u) (h_meas_v : Measurable v)
    (h_ae : u =ᵐ[CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M)] v) :
    chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u =ᵐ[
      (volume : Measure (EuclN E)).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α v := by
  classical
  have h_raw := chartPushedRaw_aeEq_of_ae_eq_riemannianMeasure (I := I) (M := M)
    g α h_meas_u h_meas_v h_ae
  have h_chartTarget_meas :
      MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_measurableSet (I := I) (M := M) α
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' h_chartTarget_meas]
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' h_chartTarget_meas] at h_raw
  filter_upwards [h_raw] with y hy hy_in
  unfold chartPushed
  have huv := hy hy_in
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α u hy_in] at huv
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α v hy_in] at huv
  rw [huv]

end

end Chart
end Sobolev
