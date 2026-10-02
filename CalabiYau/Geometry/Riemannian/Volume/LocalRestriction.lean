-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Integration/Measure/LocalRestriction.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Riemannian.Volume.Invariance
public import Mathlib.Topology.Compactness.LocallyFinite
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace CalabiYau.RiemannianVolume

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem riemannianMeasure_lintegral_eq_chartLocalMeasure_of_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (ρ : SmoothPartitionOfUnity M I M univ)
    (hρ : ρ.IsSubordinate (fun α : M => (chartAt H α).source)) (α : M)
    {F : M → ℝ≥0∞} (hF : Measurable F) (hFc : HasCompactSupport F)
    (hFs : ∀ x, x ∉ (chartAt H α).source → F x = 0) :
    (∫⁻ x, F x ∂(riemannianMeasure (I := I) g ρ)) =
      ∫⁻ x, F x ∂(chartLocalMeasure (I := I) g α) := by
  classical
  let S : Finset M := (ρ.locallyFinite.finite_nonempty_inter_compact hFc).toFinset
  have hzero {β : M} (hβ : β ∉ S) (x : M) : ENNReal.ofReal (ρ β x) * F x = 0 := by
    by_cases hx : F x = 0
    · rw [hx, mul_zero]
    · have hρx : ρ β x = 0 := by
        by_contra hne
        apply hβ
        simpa only [S, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using
          show (Function.support (ρ β) ∩ tsupport F).Nonempty from
            ⟨x, hne, subset_tsupport F hx⟩
      rw [hρx, ENNReal.ofReal_zero, zero_mul]
  rw [riemannianMeasure_lintegral_eq g ρ hF]
  rw [tsum_eq_sum (s := S) (fun β hβ => by simp_rw [hzero hβ]; simp)]
  have heq (β : M) :
      (∫⁻ x, ENNReal.ofReal (ρ β x) * F x ∂(chartLocalMeasure (I := I) g β)) =
      ∫⁻ x, ENNReal.ofReal (ρ β x) * F x ∂(chartLocalMeasure (I := I) g α) := by
    apply chartLocalMeasure_lintegral_eq_of_support_in_overlap g β α
      (f := fun x => ENNReal.ofReal (ρ β x) * F x)
      ((measurable_ofReal_pou_weight ρ β).mul hF)
    intro x hx
    by_cases hxβ : x ∈ (chartAt H β).source
    · rw [hFs x (fun hxα => hx ⟨hxβ, hxα⟩), mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport (fun hxs => hxβ (hρ β hxs)),
        ENNReal.ofReal_zero, zero_mul]
  simp_rw [heq]
  rw [← lintegral_finsetSum S (f := fun β x => ENNReal.ofReal (ρ β x) * F x)
    (fun β _ => (measurable_ofReal_pou_weight ρ β).mul hF)]
  apply lintegral_congr
  intro x
  by_cases hx : F x = 0
  · simp [hx]
  · have hs : ρ.finsupport x ⊆ S := by
      intro β hβ
      simpa only [S, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using
        show (Function.support (ρ β) ∩ tsupport F).Nonempty from
          ⟨x, (ρ.mem_finsupport x).mp hβ, subset_tsupport F hx⟩
    rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun β _ => ρ.nonneg β x),
      ρ.sum_finsupport' x (mem_univ x) hs, ENNReal.ofReal_one, one_mul]

theorem riemannianVolumeMeasure_restrict_eq_chartLocalMeasure_restrict
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M) {K : Set M}
    (hK : IsCompact K) (hKs : K ⊆ (chartAt H α).source) :
    (riemannianVolumeMeasure (I := I) (M := M) g).restrict K =
      (chartLocalMeasure (I := I) g α).restrict K := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [← lintegral_indicator hK.measurableSet, ← lintegral_indicator hK.measurableSet]
  apply riemannianMeasure_lintegral_eq_chartLocalMeasure_of_hasCompactSupport
    g (chartAtlasPOU I M) (chartAtlasPOU_isSubordinate I M) α (hF.indicator hK.measurableSet)
  · apply HasCompactSupport.of_support_subset_isCompact hK
    intro x hx
    by_contra hxK
    exact hx (indicator_of_notMem hxK F)
  · intro x hx
    exact indicator_of_notMem (fun hxK => hx (hKs hxK)) F

local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private local instance : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ E)) → ℝ)

private def chartInverseOn (α : M) (Ω : Set EuStd) : EuStd → M := by
  classical
  exact Ω.piecewise (fun z => (extChartAt I α).symm ((toEuclidean (E := E)).symm z))
    (fun _ => α)

omit [IsManifold I ∞ M] in
private theorem chartInverseOn_apply_of_mem (α : M) {Ω : Set EuStd} {z : EuStd}
    (hz : z ∈ Ω) :
    chartInverseOn (I := I) α Ω z =
      (extChartAt I α).symm ((toEuclidean (E := E)).symm z) := by
  classical
  exact Set.piecewise_eq_of_mem _ _ _ hz

omit [IsManifold I ∞ M] in
private theorem measurable_chartInverseOn (α : M) {Ω : Set EuStd}
    (hΩ : MeasurableSet Ω)
    (hΩs : Ω ⊆ toEuclidean (E := E) '' (extChartAt I α).target) :
    Measurable (chartInverseOn (I := I) α Ω) := by
  classical
  apply ContinuousOn.measurable_piecewise _ continuousOn_const hΩ
  apply (continuousOn_extChartAt_symm (I := I) α).comp
    (toEuclidean (E := E)).symm.continuous.continuousOn
  intro z hz
  obtain ⟨y, hy, rfl⟩ := hΩs hz
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using hy

private theorem map_chartInverseOn_le_smul_chartLocalMeasure
    (g : SmoothRiemannianMetric I M) (α : M) {Ω : Set EuStd}
    (hΩ : MeasurableSet Ω)
    (hΩs : Ω ⊆ toEuclidean (E := E) '' (extChartAt I α).target)
    {c : ℝ≥0∞} (hc₀ : c ≠ 0) (hc : c ≠ (⊤ : ℝ≥0∞))
    (hcρ : ∀ z ∈ Ω, 1 ≤ c * ENNReal.ofReal
      (chartDensity g α ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)))) :
    (volume.restrict Ω).map (chartInverseOn (I := I) α Ω) ≤
      c • chartLocalMeasure (I := I) g α := by
  let e := toEuclidean (E := E)
  let A : Set E := e ⁻¹' Ω
  let d : E → ℝ≥0∞ := fun y => ENNReal.ofReal (chartDensity g α ((extChartAt I α).symm y))
  have hA : MeasurableSet A := hΩ.preimage e.continuous.measurable
  have hAs : A ⊆ (extChartAt I α).target := by
    intro y hy
    obtain ⟨y', hy', heq⟩ := hΩs hy
    exact e.injective heq ▸ hy'
  have hν : (modelHaar (E := E)).restrict A ≤
      c • (((modelHaar (E := E)).restrict (extChartAt I α).target).withDensity d) := by
    calc
      (modelHaar (E := E)).restrict A =
          ((modelHaar (E := E)).restrict (extChartAt I α).target).withDensity
            (A.indicator (fun _ => 1)) := by
        rw [withDensity_indicator hA, withDensity_const, one_smul,
          Measure.restrict_restrict_of_subset hAs]
      _ ≤ ((modelHaar (E := E)).restrict (extChartAt I α).target).withDensity (c • d) := by
        apply withDensity_mono
        filter_upwards [] with y
        by_cases hy : y ∈ A
        · rw [Set.indicator_of_mem hy]
          simpa only [d, e, Pi.smul_apply, smul_eq_mul, ContinuousLinearEquiv.symm_apply_apply]
            using hcρ (e y) hy
        · rw [Set.indicator_of_notMem hy]
          exact zero_le
      _ = c • (((modelHaar (E := E)).restrict (extChartAt I α).target).withDensity d) :=
        withDensity_smul' c d hc
  have hmap : (volume.restrict Ω).map (chartInverseOn (I := I) α Ω) =
      ((modelHaar (E := E)).restrict A).map (extChartAt I α).symm := by
    have he : MeasurePreserving e (modelHaar (E := E)) volume :=
      ⟨e.continuous.measurable, map_toEuclidean_modelHaar_eq_volume (E := E)⟩
    rw [← (he.restrict_preimage hΩ).map_eq,
      Measure.map_map (measurable_chartInverseOn α hΩ hΩs) e.continuous.measurable]
    apply Measure.map_congr
    filter_upwards [ae_restrict_mem hA] with y hy
    rw [Function.comp_apply, chartInverseOn_apply_of_mem α (Ω := Ω) (z := e y) hy]
    simp only [e, ContinuousLinearEquiv.symm_apply_apply]
  rw [hmap]
  have hm : AEMeasurable (extChartAt I α).symm
      ((((modelHaar (E := E)).restrict (extChartAt I α).target).withDensity d)) :=
    (aemeasurable_extChartAt_symm_restrict_target (I := I) α).mono'
      (withDensity_absolutelyContinuous _ _)
  have h := Measure.map_mono_of_aemeasurable hν ((aemeasurable_smul_measure_iff hc₀).2 hm)
  rw [Measure.map_smul] at h
  exact h

private theorem exists_map_chartInverseOn_le_smul_riemannianVolumeMeasure
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M) {Ω : Set EuStd}
    (hΩ : MeasurableSet Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := E) '' (extChartAt I α).target) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ (⊤ : ℝ≥0∞) ∧
      (volume.restrict Ω).map (chartInverseOn (I := I) α Ω) ≤
        c • riemannianVolumeMeasure (I := I) (M := M) g := by
  let e := toEuclidean (E := E)
  let D : Set E := e.symm '' closure Ω
  let K : Set M := (extChartAt I α).symm '' D
  have hD : IsCompact D := hΩc.image e.symm.continuous
  have hDs : D ⊆ (extChartAt I α).target := by
    rintro y ⟨z, hz, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hΩs hz
    simpa only [e, ContinuousLinearEquiv.symm_apply_apply] using hy
  have hK : IsCompact K := hD.image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := I) α).mono hDs)
  have hKs : K ⊆ (chartAt H α).source := by
    rintro x ⟨y, hy, rfl⟩
    have h := (extChartAt I α).map_target (hDs hy)
    rwa [extChartAt_source] at h
  let ρ : E → ℝ := fun y => chartDensity g α ((extChartAt I α).symm y)
  have hsrc {y : E} (hy : y ∈ (extChartAt I α).target) :
      (extChartAt I α).symm y ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    have h := (extChartAt I α).map_target hy
    rwa [extChartAt_source] at h
  have hρ : ContinuousOn ρ (extChartAt I α).target :=
    (chartDensity_continuousOn g α).comp (continuousOn_extChartAt_symm (I := I) α)
      (fun y hy => hsrc hy)
  have hρpos {y : E} (hy : y ∈ (extChartAt I α).target) : 0 < ρ y :=
    chartDensity_pos g α (hsrc hy)
  obtain ⟨B, hB⟩ := hD.bddAbove_image
    ((hρ.mono hDs).inv₀ (fun y hy => (hρpos (hDs hy)).ne'))
  let C : ℝ := max B 1
  have hC : 0 < C := zero_lt_one.trans_le (le_max_right B 1)
  have hc₀ : ENNReal.ofReal C ≠ 0 := (ENNReal.ofReal_pos.mpr hC).ne'
  have hc : ENNReal.ofReal C ≠ (⊤ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  have hΩsub := subset_closure.trans hΩs
  have hmap := map_chartInverseOn_le_smul_chartLocalMeasure g α hΩ hΩsub hc₀ hc
    (fun z hz => by
      have hzD : e.symm z ∈ D := ⟨z, subset_closure hz, rfl⟩
      have hb : (ρ (e.symm z))⁻¹ ≤ C :=
        (hB ⟨e.symm z, hzD, rfl⟩).trans (le_max_left B 1)
      have hr : (1 : ℝ) ≤ C * ρ (e.symm z) := by
        exact (inv_le_iff_one_le_mul₀ (hρpos (hDs hzD))).mp hb
      have h := ENNReal.ofReal_le_ofReal hr
      rw [ENNReal.ofReal_one, ENNReal.ofReal_mul hC.le] at h
      exact h)
  have hae : ∀ᵐ x ∂((volume.restrict Ω).map (chartInverseOn (I := I) α Ω)), x ∈ K := by
    apply (ae_map_iff (measurable_chartInverseOn α hΩ hΩsub).aemeasurable hK.measurableSet).2
    filter_upwards [ae_restrict_mem hΩ] with z hz
    rw [chartInverseOn_apply_of_mem α (Ω := Ω) hz]
    exact ⟨e.symm z, ⟨z, subset_closure hz, rfl⟩, rfl⟩
  refine ⟨ENNReal.ofReal C, hc₀, hc, ?_⟩
  calc
    (volume.restrict Ω).map (chartInverseOn (I := I) α Ω) =
        ((volume.restrict Ω).map (chartInverseOn (I := I) α Ω)).restrict K :=
      (Measure.restrict_eq_self_of_ae_mem hae).symm
    _ ≤ (ENNReal.ofReal C • chartLocalMeasure (I := I) g α).restrict K :=
      Measure.restrict_mono Set.Subset.rfl hmap
    _ = ENNReal.ofReal C • (riemannianVolumeMeasure (I := I) (M := M) g).restrict K := by
      rw [Measure.restrict_smul,
        riemannianVolumeMeasure_restrict_eq_chartLocalMeasure_restrict g α hK hKs]
    _ ≤ ENNReal.ofReal C • riemannianVolumeMeasure (I := I) (M := M) g := by
      gcongr
      exact Measure.restrict_le_self

end CalabiYau.RiemannianVolume
