-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Regularity/ChartBilinear/H1Compl.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Regularity.ChartBilinear.Smooth

@[expose] public section

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace CalabiYau
namespace Analysis
namespace Laplacian
namespace ChartBilinearH1Compl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open CalabiYau.Laplacian.MetricExtension
open CalabiYau.Analysis.Laplacian.ChartLocalLaplacian
open CalabiYau.Laplacian.ChartMeasureEquiv
open Sobolev.NirenbergEuclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

def chartPulledWeightedMeasure (g : SmoothRiemannianMetric I M) (α : M) :
    Measure EuclN :=
  (volume : Measure EuclN).withDensity
    (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))

structure ChartBilinearH1ComplData
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M) where
  uChart : EuclN → ℝ
  fChart : EuclN → ℝ
  weakPartial : Fin (Module.finrank ℝ E) → EuclN → ℝ
  u_chart_memLp_weighted :
    MemLp uChart 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α))
  f_chart_memLp_weighted :
    MemLp fChart 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α))
  weak_partial_locally_memLp :
    ∀ i, ∀ K : Set EuclN, IsCompact K → K ⊆ chartTargetEuclid (I := I) (M := M) α →
      MemLp (weakPartial i) 2 ((volume : Measure EuclN).restrict K)
  weak_partial_isWeakPartial :
    ∀ i, DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (weakPartial i) uChart
      (chartTargetEuclid (I := I) (M := M) α)
  variational_identity :
    ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              weakPartial i y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN)) +
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y * uChart y * ψ y
        ∂(volume : Measure EuclN)) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y * fChart y * ψ y
        ∂(volume : Measure EuclN)

omit [NeZero (Module.finrank ℝ E)] in
theorem chart_bilinear_identity_h1Compl
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            D.weakPartial i y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * D.uChart y * ψ y
      ∂(volume : Measure EuclN)) =
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * D.fChart y * ψ y
      ∂(volume : Measure EuclN) :=
  D.variational_identity ψ hψ hψ_cs hψ_support

omit [NeZero (Module.finrank ℝ E)] in
lemma densityOnEuclid_bounded_on_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ c_min c_max : ℝ, 0 < c_min ∧ c_min ≤ c_max ∧
      ∀ y ∈ K, c_min ≤ densityOnEuclid (I := I) g α y ∧
        densityOnEuclid (I := I) g α y ≤ c_max := by
  classical
  by_cases hK_empty : K = ∅
  · refine ⟨1, 1, by norm_num, le_refl _, ?_⟩
    intro y hy
    rw [hK_empty] at hy
    exact absurd hy (Set.notMem_empty y)
  have h_dens_contOn : ContinuousOn (densityOnEuclid (I := I) g α)
      (chartTargetEuclid (I := I) (M := M) α) :=
    (densityOnEuclid_contDiffOn (I := I) g α).continuousOn
  have h_dens_contOn_K : ContinuousOn (densityOnEuclid (I := I) g α) K :=
    h_dens_contOn.mono hK_in
  have h_dens_pos : ∀ y ∈ K, 0 < densityOnEuclid (I := I) g α y :=
    fun y hy => densityOnEuclid_pos (I := I) g α (hK_in hy)
  have h_K_ne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
  obtain ⟨y_min, hy_min, h_min_eq⟩ := hK.exists_isMinOn h_K_ne h_dens_contOn_K
  obtain ⟨y_max, hy_max, h_max_eq⟩ := hK.exists_isMaxOn h_K_ne h_dens_contOn_K
  set c_min : ℝ := densityOnEuclid (I := I) g α y_min with hcmin_def
  set c_max : ℝ := densityOnEuclid (I := I) g α y_max with hcmax_def
  have hc_min_pos : 0 < c_min := h_dens_pos y_min hy_min
  have hc_min_le_max : c_min ≤ c_max := by
    have h := h_min_eq hy_max
    exact h
  refine ⟨c_min, c_max, hc_min_pos, hc_min_le_max, ?_⟩
  intro y hy
  refine ⟨h_min_eq hy, h_max_eq hy⟩

omit [NeZero (Module.finrank ℝ E)] in
lemma densityOnEuclid_continuousOn (g : SmoothRiemannianMetric I M) (α : M) :
    ContinuousOn (densityOnEuclid (I := I) g α)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (densityOnEuclid_contDiffOn (I := I) g α).continuousOn

omit [NeZero (Module.finrank ℝ E)] in
lemma volume_restrict_compact_le_chartPulledWeightedMeasure
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} (α : M)
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ c : ℝ, 0 < c ∧
      (volume : Measure EuclN).restrict K ≤
        ENNReal.ofReal c •
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  obtain ⟨c_min, _c_max, hc_min_pos, _hc_le, h_bd⟩ :=
    densityOnEuclid_bounded_on_compact (I := I) (M := M) g α hK_compact hK_in
  refine ⟨1 / c_min, by positivity, ?_⟩
  refine Measure.le_iff.2 ?_
  intro A hA
  rw [Measure.restrict_apply hA]
  rw [Measure.smul_apply, Measure.restrict_apply hA]
  unfold chartPulledWeightedMeasure
  rw [withDensity_apply _ (hA.inter (chartTargetEuclid_isOpen
    (I := I) (M := M) α).measurableSet)]
  have h_subset : A ∩ K ⊆ A ∩ chartTargetEuclid (I := I) (M := M) α :=
    Set.inter_subset_inter_right A hK_in
  have h_setmono :
      ∫⁻ y in A ∩ K, ENNReal.ofReal (densityOnEuclid (I := I) g α y) ∂(volume : Measure EuclN) ≤
      ∫⁻ y in A ∩ chartTargetEuclid (I := I) (M := M) α,
        ENNReal.ofReal (densityOnEuclid (I := I) g α y) ∂(volume : Measure EuclN) := by
    apply MeasureTheory.lintegral_mono_set h_subset
  have h_pointwise_bd :
      ∫⁻ y in A ∩ K, ENNReal.ofReal c_min ∂(volume : Measure EuclN) ≤
      ∫⁻ y in A ∩ K, ENNReal.ofReal (densityOnEuclid (I := I) g α y) ∂(volume : Measure EuclN) := by
    apply MeasureTheory.setLIntegral_mono_ae'
    · exact hA.inter hK_meas
    · refine Filter.Eventually.of_forall fun y hy => ?_
      apply ENNReal.ofReal_le_ofReal
      exact (h_bd y hy.2).1
  have h_const_eval :
      ∫⁻ _y in A ∩ K, ENNReal.ofReal c_min ∂(volume : Measure EuclN) =
      ENNReal.ofReal c_min * (volume : Measure EuclN) (A ∩ K) := by
    rw [MeasureTheory.setLIntegral_const]
  have h_step1 : (volume : Measure EuclN) (A ∩ K) =
      ENNReal.ofReal (1 / c_min) *
        (ENNReal.ofReal c_min * (volume : Measure EuclN) (A ∩ K)) := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    rw [show (1 / c_min) * c_min = 1 from by field_simp]
    rw [ENNReal.ofReal_one, one_mul]
  rw [h_step1]
  rw [smul_eq_mul]
  gcongr
  exact le_trans (le_of_eq h_const_eval.symm) (h_pointwise_bd.trans h_setmono)

omit [NeZero (Module.finrank ℝ E)] in
lemma memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {α : M} {w : EuclN → ℝ}
    (hw : MemLp w 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp w 2 ((volume : Measure EuclN).restrict K) := by
  classical
  obtain ⟨c, _hc_pos, h_le⟩ :=
    volume_restrict_compact_le_chartPulledWeightedMeasure (I := I) (M := M)
      α hK_compact hK_meas hK_in
  exact hw.of_measure_le_smul (c := ENNReal.ofReal c) ENNReal.ofReal_ne_top h_le

end ChartBilinearH1Compl
end Laplacian
end Analysis
end CalabiYau
