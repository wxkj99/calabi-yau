-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Integration/Measure/Riemannian/Properties.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Riemannian.Volume.Chart.Density
public import CalabiYau.Geometry.Riemannian.Volume.Basic
public import CalabiYau.Geometry.Riemannian.Volume.Invariance
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Topology.Compactness.LocallyFinite
public import Mathlib.Topology.Algebra.Support
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Geometry.Manifold.Metrizable
public import CalabiYau.Topology.Manifold.InteriorBoundary

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open Bundle Manifold Set MeasureTheory Function
open scoped Manifold Topology ContDiff ENNReal

namespace CalabiYau.RiemannianVolume

theorem prod_mono
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {mu₁ mu₂ : Measure X} {nu₁ nu₂ : Measure Y}
    [SFinite mu₁] [SFinite mu₂] [SFinite nu₁] [SFinite nu₂]
    (hmu : mu₁ ≤ mu₂) (hnu : nu₁ ≤ nu₂) :
    mu₁.prod nu₁ ≤ mu₂.prod nu₂ := by
  calc
    mu₁.prod nu₁ ≤ mu₁.prod nu₂ := by
      apply Measure.le_iff.mpr
      intro s hs
      rw [Measure.prod_apply hs, Measure.prod_apply hs]
      exact lintegral_mono fun _ => hnu _
    _ ≤ mu₂.prod nu₂ := by
      apply Measure.le_iff.mpr
      intro s hs
      rw [Measure.prod_apply_symm hs, Measure.prod_apply_symm hs]
      exact lintegral_mono fun _ => hmu _

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem chartLocalMeasure_compact_lt_top
    [T2Space M]
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    {K : Set M} (hK : IsCompact K) (hKsub : K ⊆ (chartAt H x₀).source) :
    chartLocalMeasure (I := I) g x₀ K < (⊤ : ℝ≥0∞) := by
  classical
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have hind_meas : Measurable (fun x : M => K.indicator (fun _ => (1 : ℝ≥0∞)) x) :=
    (measurable_const).indicator hKmeas
  have hlint := chartLocalMeasure_lintegral (I := I) (M := M) g x₀ hind_meas
  have hmeas_eq : chartLocalMeasure (I := I) g x₀ K =
      ∫⁻ x, K.indicator (fun _ => (1 : ℝ≥0∞)) x ∂ chartLocalMeasure (I := I) g x₀ := by
    rw [lintegral_indicator hKmeas, setLIntegral_const,
        one_mul]
  rw [hmeas_eq, hlint]
  set T : Set E := (extChartAt I x₀).target with hT_def
  set KE : Set E := (extChartAt I x₀) '' K with hKE_def
  have hT_meas : MeasurableSet T := measurableSet_extChartAt_target (I := I) x₀
  have hKsub' : K ⊆ (extChartAt I x₀).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hKsub
  have hcontOn_ext : ContinuousOn (extChartAt I x₀) (extChartAt I x₀).source :=
    continuousOn_extChartAt (I := I) x₀
  have hKE_compact : IsCompact KE :=
    hK.image_of_continuousOn (hcontOn_ext.mono hKsub')
  have hKE_closed : IsClosed KE := hKE_compact.isClosed
  have hKE_meas : MeasurableSet KE := hKE_closed.measurableSet
  have hKE_sub_T : KE ⊆ T := by
    intro y hy
    rcases hy with ⟨x, hxK, hxy⟩
    have hxsrc : x ∈ (extChartAt I x₀).source := hKsub' hxK
    have : (extChartAt I x₀) x ∈ (extChartAt I x₀).target :=
      (extChartAt I x₀).map_source hxsrc
    rw [hxy] at this
    exact this
  have hcontDensity_source : ContinuousOn (chartDensity g x₀) (chartAt H x₀).source :=
    chartDensity_continuousOn (I := I) g x₀
  have hcontDensity_K : ContinuousOn (chartDensity g x₀) K :=
    hcontDensity_source.mono hKsub
  have hbddAbove : BddAbove (chartDensity g x₀ '' K) :=
    (hK.image_of_continuousOn hcontDensity_K).bddAbove
  rcases hbddAbove with ⟨C, hC⟩
  have hsymm_in_K_iff : ∀ y ∈ T, ((extChartAt I x₀).symm y ∈ K ↔ y ∈ KE) := by
    intro y hyT
    constructor
    · intro hsymmK
      refine ⟨(extChartAt I x₀).symm y, hsymmK, ?_⟩
      exact (extChartAt I x₀).right_inv hyT
    · intro hyKE
      rcases hyKE with ⟨x, hxK, hxy⟩
      have hxsrc : x ∈ (extChartAt I x₀).source := hKsub' hxK
      have : (extChartAt I x₀).symm y = x := by
        rw [← hxy]
        exact (extChartAt I x₀).left_inv hxsrc
      rw [this]; exact hxK
  have hbound_pt : ∀ y ∈ T,
      ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y)) *
          K.indicator (fun _ => (1 : ℝ≥0∞)) ((extChartAt I x₀).symm y) ≤
        ENNReal.ofReal C * KE.indicator (fun _ => (1 : ℝ≥0∞)) y := by
    intro y hyT
    by_cases hy : y ∈ KE
    · have hsymmK : (extChartAt I x₀).symm y ∈ K := (hsymm_in_K_iff y hyT).mpr hy
      rcases hy with ⟨x, hxK, hxy⟩
      have hxsrc : x ∈ (extChartAt I x₀).source := hKsub' hxK
      have hleft : (extChartAt I x₀).symm y = x := by
        rw [← hxy]
        exact (extChartAt I x₀).left_inv hxsrc
      rw [Set.indicator_of_mem hsymmK, Set.indicator_of_mem (show y ∈ KE from ⟨x, hxK, hxy⟩),
          hleft, mul_one, mul_one]
      have hle : chartDensity g x₀ x ≤ C := hC (Set.mem_image_of_mem _ hxK)
      exact ENNReal.ofReal_le_ofReal hle
    · have hsymm_notin : (extChartAt I x₀).symm y ∉ K := by
        intro hmem
        exact hy ((hsymm_in_K_iff y hyT).mp hmem)
      rw [Set.indicator_of_notMem hsymm_notin, Set.indicator_of_notMem hy,
          mul_zero, mul_zero]
  have hrhs_meas : Measurable
      (fun y : E => ENNReal.ofReal C * KE.indicator (fun _ => (1 : ℝ≥0∞)) y) :=
    (measurable_const).mul ((measurable_const).indicator hKE_meas)
  calc
    ∫⁻ y in T, ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y)) *
          K.indicator (fun _ => (1 : ℝ≥0∞)) ((extChartAt I x₀).symm y)
            ∂(modelHaar (E := E))
        ≤ ∫⁻ y in T, ENNReal.ofReal C *
            KE.indicator (fun _ => (1 : ℝ≥0∞)) y ∂(modelHaar (E := E)) := by
          refine MeasureTheory.setLIntegral_mono_ae hrhs_meas.aemeasurable ?_
          exact Filter.Eventually.of_forall (fun y hyT => hbound_pt y hyT)
      _ = ENNReal.ofReal C *
            ∫⁻ y in T, KE.indicator (fun _ => (1 : ℝ≥0∞)) y ∂(modelHaar (E := E)) := by
          rw [lintegral_const_mul _ ((measurable_const).indicator hKE_meas)]
      _ = ENNReal.ofReal C * (modelHaar (E := E)) (KE ∩ T) := by
          rw [lintegral_indicator hKE_meas, setLIntegral_const, one_mul,
              Measure.restrict_apply hKE_meas]
      _ ≤ ENNReal.ofReal C * (modelHaar (E := E)) KE := by
          gcongr
          exact Set.inter_subset_left
      _ < (⊤ : ℝ≥0∞) := by
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKE_compact.measure_lt_top

private lemma pou_term_zero_of_tsupport_disjoint
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ)
    {K : Set M} (hK : MeasurableSet K) (α : M)
    (hdisj : Disjoint K (tsupport (ρ α))) :
    ((chartLocalMeasure (I := I) g α).withDensity
        (fun x : M => ENNReal.ofReal (ρ α x))) K = 0 := by
  have hfmeas : Measurable (fun x : M => ENNReal.ofReal (ρ α x)) :=
    measurable_ofReal_pou_weight (I := I) (M := M) ρ α
  rw [withDensity_apply _ hK]
  refine MeasureTheory.setLIntegral_eq_zero hK (fun x hxK => ?_)
  have hxK_ts : x ∉ tsupport (ρ α) := by
    intro hx
    exact (Set.disjoint_left.mp hdisj hxK) hx
  have : ρ α x = 0 := by
    by_contra hne
    exact hxK_ts (subset_tsupport _ hne)
  simp [this]

private lemma pou_term_le_chartLocalMeasure
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ)
    {K : Set M} (hK : MeasurableSet K) (α : M) :
    ((chartLocalMeasure (I := I) g α).withDensity
        (fun x : M => ENNReal.ofReal (ρ α x))) K ≤
      chartLocalMeasure (I := I) g α (K ∩ tsupport (ρ α)) := by
  have htsup_closed : IsClosed (tsupport (ρ α)) := isClosed_tsupport _
  have htsup_meas : MeasurableSet (tsupport (ρ α)) := htsup_closed.measurableSet
  have hKts_meas : MeasurableSet (K ∩ tsupport (ρ α)) := hK.inter htsup_meas
  have hle_one : ∀ x : M, ENNReal.ofReal (ρ α x) ≤ (1 : ℝ≥0∞) := by
    intro x
    calc ENNReal.ofReal (ρ α x) ≤ ENNReal.ofReal 1 :=
          ENNReal.ofReal_le_ofReal (ρ.le_one α x)
      _ = 1 := ENNReal.ofReal_one
  have hρ_zero_off : ∀ x, x ∉ tsupport (ρ α) → ρ α x = 0 := by
    intro x hx
    by_contra hne
    exact hx (subset_tsupport _ hne)
  rw [withDensity_apply _ hK]
  have hpt : ∀ x : M,
      ENNReal.ofReal (ρ α x) ≤ (tsupport (ρ α)).indicator (fun _ => (1 : ℝ≥0∞)) x := by
    intro x
    by_cases hx : x ∈ tsupport (ρ α)
    · rw [Set.indicator_of_mem hx]; exact hle_one x
    · rw [Set.indicator_of_notMem hx, hρ_zero_off x hx, ENNReal.ofReal_zero]
  calc
    ∫⁻ x in K, ENNReal.ofReal (ρ α x) ∂ chartLocalMeasure (I := I) g α
        ≤ ∫⁻ x in K, (tsupport (ρ α)).indicator (fun _ => (1 : ℝ≥0∞)) x
            ∂ chartLocalMeasure (I := I) g α := by
          refine MeasureTheory.setLIntegral_mono_ae
            ((measurable_const).indicator htsup_meas).aemeasurable ?_
          exact Filter.Eventually.of_forall (fun x _ => hpt x)
      _ = chartLocalMeasure (I := I) g α (K ∩ tsupport (ρ α)) := by
          rw [lintegral_indicator htsup_meas, Measure.restrict_restrict htsup_meas,
              setLIntegral_const, one_mul, Set.inter_comm]

theorem vol_le_tsum_support
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {S : Set M} (hS : MeasurableSet S) :
    riemannianVolumeMeasure (I := I) (M := M) g S ≤
      ∑' α : M, chartLocalMeasure (I := I) g α (S ∩ tsupport (chartAtlasPOU I M α)) := by
  rw [riemannianVolumeMeasure_def, riemannianMeasure_def, Measure.sum_apply _ hS]
  exact ENNReal.tsum_le_tsum
    (fun α => pou_term_le_chartLocalMeasure g (chartAtlasPOU I M) hS α)

theorem vol_le_tsum_chart
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {S : Set M} (hS : MeasurableSet S) :
    riemannianVolumeMeasure (I := I) (M := M) g S ≤
      ∑' α : M, chartLocalMeasure (I := I) g α S :=
  (vol_le_tsum_support g hS).trans
    (ENNReal.tsum_le_tsum (fun _ => measure_mono Set.inter_subset_left))

theorem riemannianMeasure_compact_lt_top
    [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ)
    (hρ : ρ.IsSubordinate (fun α : M => (chartAt H α).source))
    {K : Set M} (hK : IsCompact K) :
    riemannianMeasure (I := I) g ρ K < (⊤ : ℝ≥0∞) := by
  classical
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have hdecomp : riemannianMeasure (I := I) g ρ K =
      ∑' α : M, ((chartLocalMeasure (I := I) g α).withDensity
          (fun x : M => ENNReal.ofReal (ρ α x))) K := by
    rw [riemannianMeasure_def, Measure.sum_apply _ hKmeas]
  rw [hdecomp]
  set S : Set M := {α | (tsupport (ρ α) ∩ K).Nonempty} with hS_def
  have hlf_ts : LocallyFinite (fun α : M => tsupport (ρ α)) := ρ.locallyFinite.closure
  have hS_fin : S.Finite := hlf_ts.finite_nonempty_inter_compact hK
  have hzero_off : ∀ α, α ∉ S →
      ((chartLocalMeasure (I := I) g α).withDensity
          (fun x : M => ENNReal.ofReal (ρ α x))) K = 0 := by
    intro α hα
    have hdisj : Disjoint K (tsupport (ρ α)) := by
      rw [Set.disjoint_iff_inter_eq_empty, Set.inter_comm]
      simp only [hS_def, Set.mem_ofPred_eq, Set.not_nonempty_iff_eq_empty] at hα
      exact hα
    exact pou_term_zero_of_tsupport_disjoint (I := I) (M := M) g ρ hKmeas α hdisj
  have htsum_eq : ∑' α : M, ((chartLocalMeasure (I := I) g α).withDensity
          (fun x : M => ENNReal.ofReal (ρ α x))) K =
        ∑ α ∈ hS_fin.toFinset, ((chartLocalMeasure (I := I) g α).withDensity
          (fun x : M => ENNReal.ofReal (ρ α x))) K := by
    refine tsum_eq_sum (s := hS_fin.toFinset) ?_
    intro α hα
    refine hzero_off α ?_
    intro hαS
    exact hα (hS_fin.mem_toFinset.mpr hαS)
  rw [htsum_eq]
  refine ENNReal.sum_lt_top.mpr ?_
  intro α _
  have hKts_compact : IsCompact (K ∩ tsupport (ρ α)) :=
    hK.inter_right (isClosed_tsupport _)
  have hKts_sub : K ∩ tsupport (ρ α) ⊆ (chartAt H α).source := by
    intro x hx
    exact hρ α hx.2
  have hbound := pou_term_le_chartLocalMeasure
    (I := I) (M := M) g ρ hKmeas α
  exact lt_of_le_of_lt hbound
    (chartLocalMeasure_compact_lt_top (I := I) (M := M) g α hKts_compact hKts_sub)

theorem riemannianMeasure_isFiniteMeasureOnCompacts
    [T2Space M] (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ)
    (hρ : ρ.IsSubordinate (fun α : M => (chartAt H α).source)) :
    IsFiniteMeasureOnCompacts (riemannianMeasure (I := I) g ρ) :=
  ⟨fun _K hK => riemannianMeasure_compact_lt_top (I := I) (M := M) g ρ hρ hK⟩

theorem riemannianVolumeMeasure_isFiniteMeasureOnCompacts
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) :
    IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [riemannianVolumeMeasure_def]
  exact riemannianMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
    (chartAtlasPOU I M) (chartAtlasPOU_isSubordinate I M)

theorem locallyCompactSpace_of_chartedSpace
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Module.Finite ℝ E]
    (H : Type*) [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] :
    LocallyCompactSpace M := by
  have _hE : ProperSpace E := FiniteDimensional.proper ℝ E
  have _hH : LocallyCompactSpace H := I.locallyCompactSpace
  exact ChartedSpace.locallyCompactSpace H M

theorem riemannianMeasure_isLocallyFiniteMeasure
    [T2Space M] (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ)
    (hρ : ρ.IsSubordinate (fun α : M => (chartAt H α).source)) :
    IsLocallyFiniteMeasure (riemannianMeasure (I := I) g ρ) :=
  haveI : IsFiniteMeasureOnCompacts (riemannianMeasure (I := I) g ρ) :=
    riemannianMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g ρ hρ
  haveI : LocallyCompactSpace M :=
    locallyCompactSpace_of_chartedSpace E H I M
  inferInstance

theorem riemannianVolumeMeasure_isLocallyFiniteMeasure
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) :
    IsLocallyFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [riemannianVolumeMeasure_def]
  exact riemannianMeasure_isLocallyFiniteMeasure (I := I) (M := M) g
    (chartAtlasPOU I M) (chartAtlasPOU_isSubordinate I M)

theorem riemannianMeasure_sigmaFinite
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ)
    (hρ : ρ.IsSubordinate (fun α : M => (chartAt H α).source)) :
    SigmaFinite (riemannianMeasure (I := I) g ρ) :=
  haveI : IsFiniteMeasureOnCompacts (riemannianMeasure (I := I) g ρ) :=
    riemannianMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g ρ hρ
  SigmaFinite.of_isFiniteMeasureOnCompacts _

theorem riemannianVolumeMeasure_sigmaFinite
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) :
    SigmaFinite (riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [riemannianVolumeMeasure_def]
  exact riemannianMeasure_sigmaFinite (I := I) (M := M) g
    (chartAtlasPOU I M) (chartAtlasPOU_isSubordinate I M)

theorem riemannianMeasure_isFiniteMeasure_of_compactSpace
    [T2Space M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ)
    (hρ : ρ.IsSubordinate (fun α : M => (chartAt H α).source)) :
    IsFiniteMeasure (riemannianMeasure (I := I) g ρ) := by
  have : IsFiniteMeasureOnCompacts (riemannianMeasure (I := I) g ρ) :=
    riemannianMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g ρ hρ
  infer_instance

theorem riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) :
    IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [riemannianVolumeMeasure_def]
  exact riemannianMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
    (chartAtlasPOU I M) (chartAtlasPOU_isSubordinate I M)

omit [Module.Finite ℝ E] in
private lemma interior_isInteriorPoint_dense :
    Dense ({x : M | I.IsInteriorPoint x} : Set M) := by
  rw [dense_iff_inter_open]
  intro V hVopen hVne
  obtain ⟨x, hxV⟩ := hVne
  have hxsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hxext : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hxsrc
  set s : Set M := V ∩ (chartAt H x).source with hs_def
  have hs_open : IsOpen s := hVopen.inter (chartAt H x).open_source
  have hxs : x ∈ s := ⟨hxV, hxsrc⟩
  have hs_nhd : s ∈ 𝓝 x := hs_open.mem_nhds hxs
  have h_image_nhdW :
      (extChartAt I x) '' s ∈ 𝓝[range I] (extChartAt I x x) := by
    rw [← map_extChartAt_nhds (x := x)]
    exact Filter.image_mem_map hs_nhd
  rcases mem_nhdsWithin.mp h_image_nhdW with ⟨U, hU_open, hU_mem, hU_sub⟩
  have hxImage_inRange : extChartAt I x x ∈ range I :=
    extChartAt_target_subset_range (I := I) x ((extChartAt I x).map_source hxext)
  have hxImage_inClosure :
      extChartAt I x x ∈ closure (interior (range I)) := by
    rw [← I.range_eq_closure_interior]; exact hxImage_inRange
  rcases mem_closure_iff.mp hxImage_inClosure U hU_open hU_mem with ⟨p, hp_U, hp_int⟩
  have hp_inRange : p ∈ range I := interior_subset hp_int
  have hp_inImage : p ∈ (extChartAt I x) '' s := hU_sub ⟨hp_U, hp_inRange⟩
  rcases hp_inImage with ⟨y, hys, hyEq⟩
  refine ⟨y, hys.1, ?_⟩
  have hy_chartSource : y ∈ (chartAt H x).source := hys.2
  have hyEq' : ((chartAt H x).extend I) y = p := hyEq
  have hp_inExtTarget :
      ((chartAt H x).extend I) y ∈ interior ((chartAt H x).extend I).target := by
    have hy_chartTarget : (chartAt H x) y ∈ (chartAt H x).target :=
      (chartAt H x).map_source hy_chartSource
    have hI_inInterior : I ((chartAt H x) y) ∈ interior (range I) := by
      change ((chartAt H x).extend I) y ∈ interior (range I)
      rw [hyEq']; exact hp_int
    exact (chartAt H x).mem_interior_extend_target hy_chartTarget hI_inInterior
  have hntop : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  exact (I.isInteriorPoint_iff_of_mem_atlas hntop (chart_mem_atlas H x) hy_chartSource).mpr
    hp_inExtTarget

private lemma chartLocalMeasure_open_pos_of_mem
    (g : SmoothRiemannianMetric I M) (α : M)
    {V : Set M} (hVopen : IsOpen V) {x₁ : M} (hx₁V : x₁ ∈ V)
    (hVsub : V ⊆ (chartAt H α).source)
    (hx₁_int : extChartAt I α x₁ ∈ interior (range I)) :
    0 < chartLocalMeasure (I := I) g α V := by
  classical
  have hVmeas : MeasurableSet V := hVopen.measurableSet
  have hind_meas : Measurable (V.indicator (fun _ => (1 : ℝ≥0∞))) :=
    (measurable_const).indicator hVmeas
  have hlint := chartLocalMeasure_lintegral (I := I) (M := M) g α hind_meas
  have hVvol : chartLocalMeasure (I := I) g α V =
      ∫⁻ x, V.indicator (fun _ => (1 : ℝ≥0∞)) x ∂ chartLocalMeasure (I := I) g α := by
    rw [lintegral_indicator hVmeas, setLIntegral_const, one_mul]
  rw [hVvol, hlint]
  set T : Set E := (extChartAt I α).target with hT_def
  have hT_meas : MeasurableSet T := measurableSet_extChartAt_target (I := I) α
  have hVsub' : V ⊆ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hVsub
  have hV_nhds : V ∈ 𝓝 x₁ := hVopen.mem_nhds hx₁V
  have hx₁source : x₁ ∈ (extChartAt I α).source := hVsub' hx₁V
  have hImageNhd : (extChartAt I α) '' V ∈ 𝓝 ((extChartAt I α) x₁) :=
    extChartAt_image_nhds_mem_nhds_of_mem_interior_range (I := I) (M := M)
      (x := α) (y := x₁) hx₁source hx₁_int hV_nhds
  rcases mem_nhds_iff.mp hImageNhd with ⟨W, hW_sub, hW_open, hW_mem⟩
  have hW_meas : MeasurableSet W := hW_open.measurableSet
  have hW_ne : W.Nonempty := ⟨(extChartAt I α) x₁, hW_mem⟩
  have hW_pos : 0 < (modelHaar (E := E)) W := hW_open.measure_pos _ hW_ne
  have hW_sub_T : W ⊆ T := by
    intro y hyW
    rcases hW_sub hyW with ⟨x, hxV, hxy⟩
    have hxsrc : x ∈ (extChartAt I α).source := hVsub' hxV
    have : (extChartAt I α) x ∈ T := (extChartAt I α).map_source hxsrc
    rwa [hxy] at this
  have hdensity_on_W : ∀ y ∈ W, 0 < chartDensity g α ((extChartAt I α).symm y) := by
    intro y hyW
    rcases hW_sub hyW with ⟨x, hxV, hxy⟩
    have hxsrc : x ∈ (extChartAt I α).source := hVsub' hxV
    have hleft : (extChartAt I α).symm y = x := by
      rw [← hxy]; exact (extChartAt I α).left_inv hxsrc
    rw [hleft]
    have hxbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [trivializationAt_baseSet_eq_chartAt_source]; exact hVsub hxV
    exact chartDensity_pos (I := I) g α hxbase
  have hind_on_W : ∀ y ∈ W,
      V.indicator (fun _ => (1 : ℝ≥0∞)) ((extChartAt I α).symm y) = 1 := by
    intro y hyW
    rcases hW_sub hyW with ⟨x, hxV, hxy⟩
    have hxsrc : x ∈ (extChartAt I α).source := hVsub' hxV
    have hleft : (extChartAt I α).symm y = x := by
      rw [← hxy]; exact (extChartAt I α).left_inv hxsrc
    rw [hleft, Set.indicator_of_mem hxV]
  have h_restrict_subset :
      ∫⁻ y in W, ENNReal.ofReal (chartDensity g α ((extChartAt I α).symm y)) *
            V.indicator (fun _ => (1 : ℝ≥0∞)) ((extChartAt I α).symm y)
              ∂(modelHaar (E := E))
        ≤ ∫⁻ y in T, ENNReal.ofReal (chartDensity g α ((extChartAt I α).symm y)) *
            V.indicator (fun _ => (1 : ℝ≥0∞)) ((extChartAt I α).symm y)
              ∂(modelHaar (E := E)) :=
    lintegral_mono_set hW_sub_T
  refine lt_of_lt_of_le ?_ h_restrict_subset
  by_contra h0
  have h0' : ¬ (0 < ∫⁻ y in W, ENNReal.ofReal
      (chartDensity g α ((extChartAt I α).symm y)) *
        V.indicator (fun _ => (1 : ℝ≥0∞)) ((extChartAt I α).symm y)
          ∂(modelHaar (E := E))) := h0
  have h0eq :
      ∫⁻ y in W, ENNReal.ofReal (chartDensity g α ((extChartAt I α).symm y)) *
          V.indicator (fun _ => (1 : ℝ≥0∞)) ((extChartAt I α).symm y)
            ∂(modelHaar (E := E)) = 0 :=
    le_antisymm (not_lt.mp h0') zero_le
  have haem_integrand :
      AEMeasurable
        (fun y : E => ENNReal.ofReal
            (chartDensity g α ((extChartAt I α).symm y)) *
          V.indicator (fun _ => (1 : ℝ≥0∞)) ((extChartAt I α).symm y))
        ((modelHaar (E := E)).restrict W) := by
    have hdensity_aem :
        AEMeasurable
          (fun y : E => chartDensity g α ((extChartAt I α).symm y))
          ((modelHaar (E := E)).restrict T) := by
      have hcontOn : ContinuousOn
          (fun y : E => chartDensity g α ((extChartAt I α).symm y)) T := by
        refine (chartDensity_continuousOn (I := I) g α).comp
          (continuousOn_extChartAt_symm (I := I) α) ?_
        intro y hyT
        have : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
          (extChartAt I α).map_target hyT
        rw [extChartAt_source_eq_chartAt_source (I := I)] at this
        exact this
      exact hcontOn.aemeasurable hT_meas
    have hdensity_aem_W :
        AEMeasurable
          (fun y : E => chartDensity g α ((extChartAt I α).symm y))
          ((modelHaar (E := E)).restrict W) :=
      hdensity_aem.mono_measure (Measure.restrict_mono hW_sub_T le_rfl)
    have h1 : AEMeasurable
        (fun y : E => ENNReal.ofReal (chartDensity g α ((extChartAt I α).symm y)))
        ((modelHaar (E := E)).restrict W) :=
      ENNReal.measurable_ofReal.comp_aemeasurable hdensity_aem_W
    have hsymm_aem : AEMeasurable (extChartAt I α).symm
        ((modelHaar (E := E)).restrict T) :=
      (continuousOn_extChartAt_symm (I := I) α).aemeasurable hT_meas
    have hsymm_aem_W : AEMeasurable (extChartAt I α).symm
        ((modelHaar (E := E)).restrict W) :=
      hsymm_aem.mono_measure (Measure.restrict_mono hW_sub_T le_rfl)
    have hind_meas : Measurable (V.indicator (fun _ => (1 : ℝ≥0∞))) :=
      (measurable_const).indicator hVmeas
    have h2 : AEMeasurable
        (fun y : E => V.indicator (fun _ => (1 : ℝ≥0∞))
          ((extChartAt I α).symm y))
        ((modelHaar (E := E)).restrict W) := hind_meas.comp_aemeasurable hsymm_aem_W
    exact h1.mul h2
  have hae_zero := (MeasureTheory.lintegral_eq_zero_iff' haem_integrand).mp h0eq
  have hW_ae_zero :
      ∀ᵐ y ∂(modelHaar (E := E)), y ∈ W →
        ENNReal.ofReal (chartDensity g α ((extChartAt I α).symm y)) *
          V.indicator (fun _ => (1 : ℝ≥0∞)) ((extChartAt I α).symm y) = 0 :=
    (MeasureTheory.ae_restrict_iff' hW_meas).mp hae_zero
  have hW_full_empty : (modelHaar (E := E)) W = 0 := by
    have hyNotW : ∀ᵐ y ∂(modelHaar (E := E)), y ∉ W := by
      filter_upwards [hW_ae_zero] with y hy
      intro hyW
      have hpos : 0 < ENNReal.ofReal (chartDensity g α ((extChartAt I α).symm y)) *
          V.indicator (fun _ => (1 : ℝ≥0∞)) ((extChartAt I α).symm y) := by
        rw [hind_on_W y hyW, mul_one]
        exact ENNReal.ofReal_pos.mpr (hdensity_on_W y hyW)
      exact (ne_of_gt hpos) (hy hyW)
    exact measure_eq_zero_iff_ae_notMem.mpr hyNotW
  exact (ne_of_gt hW_pos) hW_full_empty

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
private lemma exists_open_neighborhood_pou_pos
    (ρ : SmoothPartitionOfUnity M I M univ)
    (hρ : ρ.IsSubordinate (fun α : M => (chartAt H α).source))
    {α : M} {U : Set M} (hUopen : IsOpen U) {x : M} (hxU : x ∈ U)
    (hxpos : 0 < ρ α x) :
    ∃ V : Set M, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ V ⊆ (chartAt H α).source ∧
      ∃ c > (0 : ℝ), ∀ y ∈ V, c ≤ ρ α y := by
  have hcont : Continuous (fun y : M => ρ α y) := (ρ α).contMDiff.continuous
  have hxSource : x ∈ (chartAt H α).source := by
    refine hρ α ?_
    exact subset_tsupport (ρ α) (by exact ne_of_gt hxpos)
  set c : ℝ := ρ α x / 2 with hc_def
  have hc_pos : 0 < c := by positivity
  have hc_lt : c < ρ α x := by rw [hc_def]; linarith
  have hopen_set : IsOpen {y : M | c < ρ α y} :=
    hcont.isOpen_preimage _ isOpen_Ioi
  set V : Set M := U ∩ (chartAt H α).source ∩ {y : M | c < ρ α y} with hV_def
  have hVopen : IsOpen V :=
    (hUopen.inter (chartAt H α).open_source).inter hopen_set
  have hxV : x ∈ V := ⟨⟨hxU, hxSource⟩, hc_lt⟩
  refine ⟨V, hVopen, hxV, ?_, ?_, c, hc_pos, ?_⟩
  · intro y hy; exact hy.1.1
  · intro y hy; exact hy.1.2
  · intro y hy; exact le_of_lt hy.2

theorem riemannianMeasure_isOpenPosMeasure
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ)
    (hρ : ρ.IsSubordinate (fun α : M => (chartAt H α).source)) :
    (riemannianMeasure (I := I) g ρ).IsOpenPosMeasure := by
  refine ⟨fun U hUopen hUne => ?_⟩
  rcases (I.dense_interior (M := M)).inter_open_nonempty
      U hUopen hUne with ⟨x, hxU, hx_int⟩
  have hexpos : ∃ α, 0 < ρ α x :=
    ρ.exists_pos_of_mem (Set.mem_univ _)
  rcases hexpos with ⟨α, hαpos⟩
  rcases exists_open_neighborhood_pou_pos (I := I) (M := M) ρ hρ hUopen hxU hαpos with
    ⟨V, hVopen, hxV, hVU, hVsource, c, hcpos, hcbound⟩
  have hVmeas : MeasurableSet V := hVopen.measurableSet
  have hx_chartαSource : x ∈ (chartAt H α).source := hVsource hxV
  have hntop : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hx_intExtTarget :
      ((chartAt H α).extend I) x ∈ interior ((chartAt H α).extend I).target :=
    (I.isInteriorPoint_iff_of_mem_atlas hntop (chart_mem_atlas H α) hx_chartαSource).mp
      hx_int
  have hx_intRange : extChartAt I α x ∈ interior (range I) :=
    (chartAt H α).interior_extend_target_subset_interior_range hx_intExtTarget
  have hind_le :
      (ENNReal.ofReal c) * chartLocalMeasure (I := I) g α V ≤
        ((chartLocalMeasure (I := I) g α).withDensity
          (fun y : M => ENNReal.ofReal (ρ α y))) V := by
    rw [withDensity_apply _ hVmeas]
    calc (ENNReal.ofReal c) * chartLocalMeasure (I := I) g α V
        = ∫⁻ _ in V, ENNReal.ofReal c ∂ chartLocalMeasure (I := I) g α := by
          rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ y in V, ENNReal.ofReal (ρ α y) ∂ chartLocalMeasure (I := I) g α := by
          refine MeasureTheory.setLIntegral_mono_ae
            (measurable_ofReal_pou_weight (I := I) (M := M) ρ α).aemeasurable ?_
          exact Filter.Eventually.of_forall (fun y hyV =>
            ENNReal.ofReal_le_ofReal (hcbound y hyV))
  have hc_enn_pos : 0 < ENNReal.ofReal c := ENNReal.ofReal_pos.mpr hcpos
  have hμV_pos : 0 < chartLocalMeasure (I := I) g α V :=
    chartLocalMeasure_open_pos_of_mem (I := I) (M := M) g α hVopen hxV hVsource
      hx_intRange
  have hpos : 0 < ((chartLocalMeasure (I := I) g α).withDensity
      (fun y : M => ENNReal.ofReal (ρ α y))) V := by
    refine lt_of_lt_of_le ?_ hind_le
    exact ENNReal.mul_pos (ne_of_gt hc_enn_pos) (ne_of_gt hμV_pos)
  have hle_g : ((chartLocalMeasure (I := I) g α).withDensity
      (fun y : M => ENNReal.ofReal (ρ α y))) V ≤ riemannianMeasure (I := I) g ρ V :=
    chartLocalMeasure_withDensity_le_riemannianMeasure
      (I := I) (M := M) g ρ α V
  have hle_g' : riemannianMeasure (I := I) g ρ V ≤ riemannianMeasure (I := I) g ρ U :=
    measure_mono hVU
  exact ne_of_gt (lt_of_lt_of_le hpos (hle_g.trans hle_g'))

theorem riemannianVolumeMeasure_isOpenPosMeasure
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) :
    (riemannianVolumeMeasure (I := I) (M := M) g).IsOpenPosMeasure := by
  rw [riemannianVolumeMeasure_def]
  exact riemannianMeasure_isOpenPosMeasure (I := I) (M := M) g
    (chartAtlasPOU I M) (chartAtlasPOU_isSubordinate I M)

theorem riemannianMeasure_regular
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ)
    (hρ : ρ.IsSubordinate (fun α : M => (chartAt H α).source)) :
    MeasureTheory.Measure.Regular (riemannianMeasure (I := I) g ρ) := by
  have : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  have : IsLocallyFiniteMeasure (riemannianMeasure (I := I) g ρ) :=
    riemannianMeasure_isLocallyFiniteMeasure (I := I) (M := M) g ρ hρ
  exact MeasureTheory.Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _

theorem riemannianVolumeMeasure_regular
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) :
    MeasureTheory.Measure.Regular (riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [riemannianVolumeMeasure_def]
  exact riemannianMeasure_regular (I := I) (M := M) g
    (chartAtlasPOU I M) (chartAtlasPOU_isSubordinate I M)

end CalabiYau.RiemannianVolume
