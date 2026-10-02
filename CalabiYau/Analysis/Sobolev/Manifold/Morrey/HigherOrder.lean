-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Manifold/Morrey/HigherOrder.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Euclidean.Embedding.Morrey.HigherOrder
public import CalabiYau.Analysis.Sobolev.Manifold.Morrey.Basic
public import CalabiYau.Analysis.Sobolev.Chart.SmoothDensity.ChartSobolevDensity

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function Sobolev.Chart
  Sobolev.EuclideanMorrey
open scoped Manifold ContDiff ENNReal NNReal

namespace CalabiYau
namespace Analysis
namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [T2Space M] [CompactSpace M] [I.Boundaryless]

omit [FiniteDimensional ℝ E] in
private lemma iteratedFDeriv_eq_zero_of_notMem_tsupport
    {h : EuclN → ℝ} {y : EuclN} (hy : y ∉ tsupport h) (m : ℕ) :
    iteratedFDeriv ℝ m h y = 0 := by
  have hy_off : y ∉ Function.support (iteratedFDeriv ℝ m h) := by
    intro hy_in
    exact hy ((support_iteratedFDeriv_subset (𝕜 := ℝ) (n := m)) hy_in)
  exact Function.notMem_support.mp hy_off

omit [I.Boundaryless] in
private lemma iteratedFDeriv_chartSmoothExt_pou_mul_eq_zero_off_carrier
    (α : M) (u : M → ℝ) {y : EuclN}
    (hy : y ∉ chartCarrier (I := I) (M := M) α) (m : ℕ) :
    iteratedFDeriv ℝ m (chartSmoothExt (I := I) (M := M) α
      (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x)) y = 0 := by
  set h : EuclN → ℝ := chartSmoothExt (I := I) (M := M) α
    (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) x * u x) with hh_def
  have hy_off : y ∉ tsupport h := fun hy_in =>
    hy (tsupport_chartSmoothExt_pou_mul_subset_chartCarrier
      (I := I) (M := M) α u hy_in)
  exact iteratedFDeriv_eq_zero_of_notMem_tsupport hy_off m

omit [I.Boundaryless] in
private lemma iteratedFDeriv_chartSmoothExt_pou_mul_eq_zero_off_half_ball
    (α : M) (u : M → ℝ) {y : EuclN}
    (hy : y ∉ Metric.ball (0 : EuclN) (chartRadius (I := I) (M := M) α / 2))
    (m : ℕ) :
    iteratedFDeriv ℝ m (chartSmoothExt (I := I) (M := M) α
      (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x)) y = 0 := by
  have hy_off_carrier : y ∉ chartCarrier (I := I) (M := M) α := fun hin =>
    hy (chartCarrier_subset_half_ball (I := I) (M := M) α hin)
  exact iteratedFDeriv_chartSmoothExt_pou_mul_eq_zero_off_carrier
    (I := I) (M := M) α u hy_off_carrier m

omit [I.Boundaryless] in
private lemma eLpNorm_norm_iteratedFDeriv_chartSmoothExt_pou_mul_restrict_ball_eq_restrict_target
    (α : M) (u : M → ℝ) (q : ℝ≥0∞) (j : ℕ) :
    eLpNorm (fun z : EuclN => ‖iteratedFDeriv ℝ j (chartSmoothExt (I := I) (M := M) α
        (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x)) z‖) q
      (volume.restrict (Metric.ball (0 : EuclN) (chartRadius (I := I) (M := M) α))) =
      eLpNorm (fun z : EuclN => ‖iteratedFDeriv ℝ j (chartSmoothExt (I := I) (M := M) α
          (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x)) z‖) q
        (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set h : EuclN → ℝ := chartSmoothExt (I := I) (M := M) α
    (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) x * u x) with hh_def
  set K : Set EuclN := chartCarrier (I := I) (M := M) α with hK_def
  set BR : Set EuclN := Metric.ball (0 : EuclN) (chartRadius (I := I) (M := M) α)
    with hBR_def
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hK_BR : K ⊆ BR := chartCarrier_subset_radius_ball (I := I) (M := M) α
  have hK_Ω : K ⊆ Ω := chartCarrier_subset_chartTargetEuclid (I := I) (M := M) α
  have hBR_meas : MeasurableSet BR := measurableSet_ball
  have hΩ_meas : MeasurableSet Ω :=
    chartTargetEuclid_measurableSet (I := I) (M := M) α
  set fnNorm : EuclN → ℝ := fun z : EuclN => ‖iteratedFDeriv ℝ j h z‖ with hfnNorm_def
  have h_eq_BR : fnNorm = BR.indicator fnNorm := by
    funext y
    by_cases hy : y ∈ BR
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      have hyK : y ∉ K := fun h2 => hy (hK_BR h2)
      have h_iter_zero : iteratedFDeriv ℝ j h y = 0 :=
        iteratedFDeriv_chartSmoothExt_pou_mul_eq_zero_off_carrier
          (I := I) (M := M) α u hyK j
      change ‖iteratedFDeriv ℝ j h y‖ = 0
      rw [h_iter_zero, norm_zero]
  have h_eq_Ω : fnNorm = Ω.indicator fnNorm := by
    funext y
    by_cases hy : y ∈ Ω
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      have hyK : y ∉ K := fun h2 => hy (hK_Ω h2)
      have h_iter_zero : iteratedFDeriv ℝ j h y = 0 :=
        iteratedFDeriv_chartSmoothExt_pou_mul_eq_zero_off_carrier
          (I := I) (M := M) α u hyK j
      change ‖iteratedFDeriv ℝ j h y‖ = 0
      rw [h_iter_zero, norm_zero]
  calc eLpNorm fnNorm q (volume.restrict BR)
      = eLpNorm (BR.indicator fnNorm) q volume :=
        (eLpNorm_indicator_eq_eLpNorm_restrict hBR_meas).symm
    _ = eLpNorm fnNorm q volume := by rw [← h_eq_BR]
    _ = eLpNorm (Ω.indicator fnNorm) q volume := by rw [← h_eq_Ω]
    _ = eLpNorm fnNorm q (volume.restrict Ω) :=
        eLpNorm_indicator_eq_eLpNorm_restrict hΩ_meas

private lemma sum_eLpNorm_norm_iteratedFDeriv_chartSmoothExt_le_wkpNorm
    (α : M) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1),
      eLpNorm (fun z : EuclN => ‖iteratedFDeriv ℝ j (chartSmoothExt (I := I) (M := M) α
        (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x)) z‖) p
        (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) ≤
      Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k p
        (chartSmoothExt (I := I) (M := M) α
          (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x))
        (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set h : EuclN → ℝ := chartSmoothExt (I := I) (M := M) α
    (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) x * u x) with hh_def
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hh_smooth : ContDiff ℝ ∞ h := by
    rw [hh_def]
    exact contDiff_chartSmoothExt_pou_mul (I := I) (M := M) α
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M)
      (CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M) hu
  have hh_smooth_top : ContDiff ℝ (⊤ : ℕ∞) h := hh_smooth
  have hh_compact : HasCompactSupport h := by
    rw [hh_def]
    exact hasCompactSupport_chartSmoothExt_pou_mul (I := I) (M := M) α
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M)
      (CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M) u
  have hh_support : tsupport h ⊆ Ω := by
    rw [hh_def, hΩ_def]
    have h1 : tsupport (chartSmoothExt (I := I) (M := M) α
        (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x)) ⊆ chartCarrier (I := I) (M := M) α :=
      tsupport_chartSmoothExt_pou_mul_subset_chartCarrier (I := I) (M := M) α u
    exact h1.trans (chartCarrier_subset_chartTargetEuclid (I := I) (M := M) α)
  have hΩ_open : IsOpen Ω :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  exact Sobolev.Euclidean.eLpNorm_iteratedFDeriv_le_wkpNorm
    (d := Module.finrank ℝ E) hΩ_open hp_one k hh_smooth_top hh_compact hh_support

omit [I.Boundaryless] in
private lemma wkpNorm_chartPushed_target_le_wkpNormChart_k
    (g : CalabiYau.SmoothRiemannianMetric I M)
    {q : ℝ≥0∞} (k : ℕ) (α : M) (u : M → ℝ) :
    Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k q
        (chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
        (chartTargetEuclid (I := I) (M := M) α) ≤
      wkpNormChart (I := I) (M := M) k q u := by
  classical
  let _ := g
  unfold wkpNormChart
  exact ENNReal.le_tsum α

private lemma wkpNorm_chartSmoothExt_target_eq_wkpNorm_chartPushed_target_k
    {q : ℝ≥0∞} (hq_one : 1 ≤ q) (k : ℕ) (α : M) (u : M → ℝ) :
    Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k q
        (chartSmoothExt (I := I) (M := M) α
          (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x))
        (chartTargetEuclid (I := I) (M := M) α) =
      Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k q
        (chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
        (chartTargetEuclid (I := I) (M := M) α) :=
  Sobolev.Euclidean.wkpNorm_congr_ae
    (d := Module.finrank ℝ E) hq_one
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (chartSmoothExt_ae_eq_chartPushed (I := I) (M := M) α u)

private lemma wkpNorm_chartSmoothExt_pou_mul_le_wkpNormChart_k
    (g : CalabiYau.SmoothRiemannianMetric I M)
    {q : ℝ≥0∞} (hq_one : 1 ≤ q) (k : ℕ) (α : M) (u : M → ℝ) :
    Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k q
        (chartSmoothExt (I := I) (M := M) α
          (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x))
        (chartTargetEuclid (I := I) (M := M) α) ≤
      wkpNormChart (I := I) (M := M) k q u := by
  classical
  rw [wkpNorm_chartSmoothExt_target_eq_wkpNorm_chartPushed_target_k
    (I := I) (M := M) hq_one k α u]
  exact wkpNorm_chartPushed_target_le_wkpNormChart_k
    (I := I) (M := M) g k α u

private lemma memWkp_chartSmoothExt_pou_mul
    (α : M) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (k : ℕ) :
    Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) k p
      (chartSmoothExt (I := I) (M := M) α
        (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x))
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set h : EuclN → ℝ := chartSmoothExt (I := I) (M := M) α
    (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) x * u x) with hh_def
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hh_smooth : ContDiff ℝ ∞ h := by
    rw [hh_def]
    exact contDiff_chartSmoothExt_pou_mul (I := I) (M := M) α
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M)
      (CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M) hu
  have hh_smooth_top : ContDiff ℝ (⊤ : ℕ∞) h := hh_smooth
  have hh_compact : HasCompactSupport h := by
    rw [hh_def]
    exact hasCompactSupport_chartSmoothExt_pou_mul (I := I) (M := M) α
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M)
      (CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M) u
  have hh_support : tsupport h ⊆ Ω := by
    rw [hh_def, hΩ_def]
    have h1 : tsupport (chartSmoothExt (I := I) (M := M) α
        (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x)) ⊆ chartCarrier (I := I) (M := M) α :=
      tsupport_chartSmoothExt_pou_mul_subset_chartCarrier (I := I) (M := M) α u
    exact h1.trans (chartCarrier_subset_chartTargetEuclid (I := I) (M := M) α)
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  exact Sobolev.Euclidean.MemWkp_of_smooth_compactSupport
    (d := Module.finrank ℝ E) hΩ_open hh_smooth_top hh_compact hh_support hp_one k

private lemma memWkp_chartPushed_of_contMDiff
    (α : M) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (k : ℕ) :
    Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) k p
      (chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hExt := memWkp_chartSmoothExt_pou_mul (I := I) (M := M) α hu hp_one k
  have h_ae := chartSmoothExt_ae_eq_chartPushed (I := I) (M := M) α u
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  refine (Sobolev.Euclidean.MemWkp_congr_ae
    (d := Module.finrank ℝ E) hp_one hΩ_open h_ae).mp hExt

theorem memWkpChart_of_contMDiff_k
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (k : ℕ)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    MemWkpChart (I := I) (M := M) k p u := by
  intro α
  exact memWkp_chartPushed_of_contMDiff (I := I) (M := M) α hu hp_one k

private lemma wkpNormChart_lt_top_of_contMDiff_k
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (k : ℕ)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    wkpNormChart (I := I) (M := M) k p u < (⊤ : ℝ≥0∞) :=
  wkpNormChart_lt_top_of_memWkpChart (I := I) (M := M) hp_one
    (memWkpChart_of_contMDiff_k (I := I) (M := M) hp_one k hu)

private lemma chartSmoothExt_morrey_iteratedFDeriv_sup_uniform
    (α : M) {p : ℝ} (hp : (Module.finrank ℝ E : ℝ) < p) (m : ℕ)
    [NeZero (Module.finrank ℝ E)] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
        ∀ y : EuclN, ‖iteratedFDeriv ℝ m (chartSmoothExt (I := I) (M := M) α
          (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x)) y‖ ≤ C *
          ((Finset.range (m + 2)).sum fun j =>
            (eLpNorm (fun z : EuclN => ‖iteratedFDeriv ℝ j (chartSmoothExt
                (I := I) (M := M) α
                (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
                  : C^∞⟮I, M; ℝ⟯) x * u x)) z‖) (ENNReal.ofReal p)
              (volume.restrict (Metric.ball (0 : EuclN) (chartRadius
                (I := I) (M := M) α)))).toReal) := by
  classical
  have hR_pos : 0 < chartRadius (I := I) (M := M) α :=
    chartRadius_pos (I := I) (M := M) α
  obtain ⟨C, hC_nn, hbound⟩ :=
    Sobolev.EuclideanMorrey.smooth_morrey_iteratedFDeriv_bound_uniform
      (d := Module.finrank ℝ E) hp
      (x₀ := (0 : EuclN)) (R := chartRadius (I := I) (M := M) α) hR_pos m
  refine ⟨C, hC_nn, ?_⟩
  intro u hu y
  set f : EuclN → ℝ := chartSmoothExt (I := I) (M := M) α
    (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) x * u x) with hf_def
  have hf_smooth : ContDiff ℝ ∞ f := by
    rw [hf_def]
    exact contDiff_chartSmoothExt_pou_mul (I := I) (M := M) α
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M)
      (CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M) hu
  have hf_smooth_top : ContDiff ℝ (⊤ : ℕ∞) f := hf_smooth
  by_cases hy_half : y ∈ Metric.ball (0 : EuclN) (chartRadius (I := I) (M := M) α / 2)
  · exact hbound hf_smooth_top y hy_half
  · have hf_iter_zero : iteratedFDeriv ℝ m f y = 0 := by
      rw [hf_def]
      exact iteratedFDeriv_chartSmoothExt_pou_mul_eq_zero_off_half_ball
        (I := I) (M := M) α u hy_half m
    rw [hf_iter_zero, norm_zero]
    apply mul_nonneg hC_nn
    exact Finset.sum_nonneg (fun j _ => ENNReal.toReal_nonneg)

private lemma per_chart_smooth_iteratedFDeriv_sup_bound
    (g : CalabiYau.SmoothRiemannianMetric I M)
    {p : ℝ} (hp : (Module.finrank ℝ E : ℝ) < p) (m : ℕ)
    [NeZero (Module.finrank ℝ E)] (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
        ∀ y : EuclN, ‖iteratedFDeriv ℝ m (chartSmoothExt (I := I) (M := M) α
          (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x)) y‖ ≤ C *
          (wkpNormChart (I := I) (M := M) (m + 1) (ENNReal.ofReal p) u).toReal := by
  classical
  have hp_pos : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg _) hp
  have hp_one : 1 ≤ p := by
    have hd_pos : (0 : ℝ) < (Module.finrank ℝ E : ℝ) := by
      exact_mod_cast NeZero.pos (Module.finrank ℝ E)
    have hd_one_le : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by
      have : 1 ≤ Module.finrank ℝ E := NeZero.one_le
      exact_mod_cast this
    linarith
  have hp_enn_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
    exact ENNReal.ofReal_le_ofReal hp_one
  obtain ⟨Cmorrey, hCmorrey_nn, hbound⟩ :=
    chartSmoothExt_morrey_iteratedFDeriv_sup_uniform (I := I) (M := M) α hp m
  refine ⟨Cmorrey, hCmorrey_nn, ?_⟩
  intro u hu y
  set f : EuclN → ℝ := chartSmoothExt (I := I) (M := M) α
    (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) x * u x) with hf_def
  have hbound_y := hbound hu y
  set total_eLpNorm : ℝ :=
    (Finset.range (m + 2)).sum fun j =>
      (eLpNorm (fun z : EuclN => ‖iteratedFDeriv ℝ j f z‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : EuclN) (chartRadius (I := I) (M := M) α)))).toReal
    with htotal_def
  set N : ℝ := (wkpNormChart (I := I) (M := M) (m + 1) (ENNReal.ofReal p) u).toReal
    with hN_def
  have h_step_BR_eq_Ω : ∀ j : ℕ,
      (eLpNorm (fun z : EuclN => ‖iteratedFDeriv ℝ j f z‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : EuclN)
          (chartRadius (I := I) (M := M) α)))) =
      (eLpNorm (fun z : EuclN => ‖iteratedFDeriv ℝ j f z‖) (ENNReal.ofReal p)
        (volume.restrict (chartTargetEuclid (I := I) (M := M) α))) := by
    intro j
    rw [hf_def]
    exact eLpNorm_norm_iteratedFDeriv_chartSmoothExt_pou_mul_restrict_ball_eq_restrict_target
      (I := I) (M := M) α u (ENNReal.ofReal p) j
  set total_Ω : ℝ :=
    (Finset.range (m + 2)).sum fun j =>
      (eLpNorm (fun z : EuclN => ‖iteratedFDeriv ℝ j f z‖) (ENNReal.ofReal p)
        (volume.restrict (chartTargetEuclid (I := I) (M := M) α))).toReal
    with htotalΩ_def
  have h_total_eq : total_eLpNorm = total_Ω := by
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [h_step_BR_eq_Ω j]
  have h_sum_eLpNorm_le_wkpNorm :
      ∑ j ∈ Finset.range (m + 2),
        eLpNorm (fun z : EuclN => ‖iteratedFDeriv ℝ j f z‖) (ENNReal.ofReal p)
          (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) ≤
      Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) (m + 1) (ENNReal.ofReal p) f
        (chartTargetEuclid (I := I) (M := M) α) := by
    rw [hf_def]
    have := sum_eLpNorm_norm_iteratedFDeriv_chartSmoothExt_le_wkpNorm
      (I := I) (M := M) α hu hp_enn_one (m + 1)
    exact this
  have h_wkpNorm_le_wkpNormChart :
      Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) (m + 1) (ENNReal.ofReal p) f
        (chartTargetEuclid (I := I) (M := M) α) ≤
      wkpNormChart (I := I) (M := M) (m + 1) (ENNReal.ofReal p) u := by
    rw [hf_def]
    exact wkpNorm_chartSmoothExt_pou_mul_le_wkpNormChart_k
      (I := I) (M := M) g hp_enn_one (m + 1) α u
  have h_wkp_chain :
      ∑ j ∈ Finset.range (m + 2),
        eLpNorm (fun z : EuclN => ‖iteratedFDeriv ℝ j f z‖) (ENNReal.ofReal p)
          (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) ≤
      wkpNormChart (I := I) (M := M) (m + 1) (ENNReal.ofReal p) u :=
    h_sum_eLpNorm_le_wkpNorm.trans h_wkpNorm_le_wkpNormChart
  have hwkp_ne_top : wkpNormChart (I := I) (M := M) (m + 1)
      (ENNReal.ofReal p) u ≠ ⊤ :=
    (wkpNormChart_lt_top_of_contMDiff_k (I := I) (M := M) hp_enn_one (m + 1) hu).ne
  have h_sum_le_N : total_Ω ≤ N := by
    have h_sum_eq :
        (∑ j ∈ Finset.range (m + 2),
          eLpNorm (fun z : EuclN => ‖iteratedFDeriv ℝ j f z‖) (ENNReal.ofReal p)
            (volume.restrict (chartTargetEuclid (I := I) (M := M) α))).toReal =
        total_Ω := by
      rw [htotalΩ_def, ENNReal.toReal_sum]
      intro j hj
      have h_sum_j_le :
          eLpNorm (fun z : EuclN => ‖iteratedFDeriv ℝ j f z‖) (ENNReal.ofReal p)
            (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) ≤
          wkpNormChart (I := I) (M := M) (m + 1) (ENNReal.ofReal p) u := by
        refine le_trans ?_ h_wkpNorm_le_wkpNormChart
        refine le_trans ?_ h_sum_eLpNorm_le_wkpNorm
        exact Finset.single_le_sum
          (f := fun j' : ℕ =>
            eLpNorm (fun z : EuclN => ‖iteratedFDeriv ℝ j' f z‖) (ENNReal.ofReal p)
              (volume.restrict (chartTargetEuclid (I := I) (M := M) α)))
          (fun _ _ => zero_le) hj
      exact lt_of_le_of_lt h_sum_j_le
        (wkpNormChart_lt_top_of_contMDiff_k (I := I) (M := M) hp_enn_one (m + 1) hu) |>.ne
    rw [← h_sum_eq]
    exact ENNReal.toReal_mono hwkp_ne_top h_wkp_chain
  have h_total_le_N : total_eLpNorm ≤ N := by
    rw [h_total_eq]; exact h_sum_le_N
  have h_bound_chain :
      ‖iteratedFDeriv ℝ m f y‖ ≤ Cmorrey * total_eLpNorm := by
    rw [hf_def]; exact hbound_y
  have h_final : Cmorrey * total_eLpNorm ≤ Cmorrey * N :=
    mul_le_mul_of_nonneg_left h_total_le_N hCmorrey_nn
  exact le_trans h_bound_chain h_final

private noncomputable def perChartMorreyIteratedConst
    (g : CalabiYau.SmoothRiemannianMetric I M)
    {p : ℝ} (hp : (Module.finrank ℝ E : ℝ) < p) (m : ℕ)
    [NeZero (Module.finrank ℝ E)] (α : M) : ℝ :=
  Classical.choose (per_chart_smooth_iteratedFDeriv_sup_bound
    (I := I) (M := M) g hp m α)

private lemma perChartMorreyIteratedConst_nn
    (g : CalabiYau.SmoothRiemannianMetric I M)
    {p : ℝ} (hp : (Module.finrank ℝ E : ℝ) < p) (m : ℕ)
    [NeZero (Module.finrank ℝ E)] (α : M) :
    0 ≤ perChartMorreyIteratedConst (I := I) (M := M) g hp m α :=
  (Classical.choose_spec
    (per_chart_smooth_iteratedFDeriv_sup_bound
      (I := I) (M := M) g hp m α)).1

private lemma perChartMorreyIteratedConst_bound
    (g : CalabiYau.SmoothRiemannianMetric I M)
    {p : ℝ} (hp : (Module.finrank ℝ E : ℝ) < p) (m : ℕ)
    [NeZero (Module.finrank ℝ E)] (α : M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) (y : EuclN) :
    ‖iteratedFDeriv ℝ m (chartSmoothExt (I := I) (M := M) α
        (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x)) y‖ ≤
      perChartMorreyIteratedConst (I := I) (M := M) g hp m α *
        (wkpNormChart (I := I) (M := M) (m + 1) (ENNReal.ofReal p) u).toReal :=
  (Classical.choose_spec
    (per_chart_smooth_iteratedFDeriv_sup_bound
      (I := I) (M := M) g hp m α)).2 hu y

end Chart
end Sobolev
end Analysis
end CalabiYau
