-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Regularity/H1Compl/GradientLipschitzBound.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Regularity.H1Compl.GradientLipschitz
public import CalabiYau.Analysis.Sobolev.Manifold.Measure.UniformChartComparison
public import CalabiYau.Geometry.Riemannian.Operator.Gradient.NormSquared
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic

@[expose] public section

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace CalabiYau
namespace Analysis
namespace Laplacian
namespace H1ComplGradientLipschitzBound

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open CalabiYau.Laplacian.MetricExtension
  hiding chartTargetEuclid
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl
open CalabiYau.Analysis.Laplacian.H1ComplGradientChartBridge
open CalabiYau.Analysis.Laplacian.H1ComplGradientLipschitz
open CalabiYau.Analysis.Laplacian.H1ComplToLpChartBridge
open Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

noncomputable def kPouCompact (α : M) : Set EuclN :=
  (toEuclidean : E ≃L[ℝ] EuclN) ''
    ((extChartAt I α) '' (tsupport (fun x : M =>
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x)))

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem kPouCompact_isCompact (α : M) :
    IsCompact (kPouCompact (I := I) (M := M) α) := by
  classical
  unfold kPouCompact
  have h_tsupp_compact : IsCompact (tsupport
      fun x : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x) :=
    isClosed_tsupport _ |>.isCompact
  have h_tsupp_sub_source : tsupport (fun x : M =>
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x) ⊆
      (chartAt H α).source :=
    (CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M) α
  have h_ext_cont : ContinuousOn (extChartAt I α)
      (tsupport fun x : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x) := by
    have h_source_eq : (chartAt H α).source = (extChartAt I α).source :=
      (CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
        (I := I) (M := M) α).symm
    refine (continuousOn_extChartAt (I := I) α).mono ?_
    rw [← h_source_eq]; exact h_tsupp_sub_source
  have h_ext_image_compact : IsCompact ((extChartAt I α) '' (tsupport
      fun x : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x)) :=
    h_tsupp_compact.image_of_continuousOn h_ext_cont
  exact h_ext_image_compact.image (toEuclidean (E := E)).continuous

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem kPouCompact_subset_chartTargetEuclid (α : M) :
    kPouCompact (I := I) (M := M) α ⊆
      Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α := by
  classical
  intro y hy
  rcases hy with ⟨z, hz, hzy⟩
  rcases hz with ⟨x, hx, hxz⟩
  have h_tsupp_sub_source : tsupport (fun x : M =>
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x) ⊆
      (chartAt H α).source :=
    (CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M) α
  have hxsrc : x ∈ (extChartAt I α).source := by
    rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
      (I := I) (M := M)]
    exact h_tsupp_sub_source hx
  have hz_target : z ∈ (extChartAt I α).target := by
    rw [← hxz]; exact (extChartAt I α).map_source hxsrc
  refine ⟨z, hz_target, hzy⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem smoothChartExt_support_subset_kPouCompact
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    Function.support (smoothChartExt (I := I) (M := M) g α v) ⊆
      kPouCompact (I := I) (M := M) α := by
  classical
  intro y hy
  have hy_ne : smoothChartExt (I := I) (M := M) g α v y ≠ 0 := hy
  by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α
  · obtain ⟨w, hw_target, hwy⟩ := hy_target
    have h_eq : (toEuclidean (E := E)).symm y = w := by
      rw [← hwy]; exact (toEuclidean (E := E)).symm_apply_apply w
    have h_apply : smoothChartExt (I := I) (M := M) g α v y =
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
            ((extChartAt I α).symm w)) *
          v.toFun ((extChartAt I α).symm w) := by
      rw [smoothChartExt_apply_of_mem_target (I := I) (M := M) g α v
        (h_eq ▸ hw_target)]
      rw [h_eq]
    rw [h_apply] at hy_ne
    by_contra h_notin
    apply hy_ne
    have h_pou_zero : (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) ((extChartAt I α).symm w) = 0 := by
      by_contra h_pou_ne
      apply h_notin
      have h_pou_in_support : (extChartAt I α).symm w ∈ Function.support
          fun x : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x := h_pou_ne
      have h_pou_in_tsupp : (extChartAt I α).symm w ∈ tsupport
          fun x : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x :=
        subset_tsupport _ h_pou_in_support
      have h_ext_right : (extChartAt I α) ((extChartAt I α).symm w) = w :=
        (extChartAt I α).right_inv hw_target
      exact ⟨w, ⟨(extChartAt I α).symm w, h_pou_in_tsupp, h_ext_right⟩, hwy⟩
    rw [h_pou_zero]; ring
  · exfalso
    apply hy_ne
    have h_notMem : (toEuclidean (E := E)).symm y ∉ (extChartAt I α).target := by
      intro h_in
      apply hy_target
      refine ⟨(toEuclidean (E := E)).symm y, h_in, ?_⟩
      simp
    exact smoothChartExt_apply_of_notMem_target (I := I) (M := M) g α v h_notMem

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem smoothChartExt_tsupport_subset_kPouCompact
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    tsupport (smoothChartExt (I := I) (M := M) g α v) ⊆
      kPouCompact (I := I) (M := M) α := by
  refine closure_minimal (smoothChartExt_support_subset_kPouCompact
    (I := I) (M := M) g α v) ?_
  exact (kPouCompact_isCompact (I := I) (M := M) α).isClosed

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem smoothChartExtPartial_tsupport_subset_kPouCompact
    (g : SmoothRiemannianMetric I M) (α : M) (j : Fin (Module.finrank ℝ E))
    (v : SmoothScalar g) :
    tsupport (smoothChartExtPartial (I := I) (M := M) g α j v) ⊆
      kPouCompact (I := I) (M := M) α := by
  have h_fderiv_support : tsupport (smoothChartExtPartial (I := I) (M := M) g α j v) ⊆
      tsupport (smoothChartExt (I := I) (M := M) g α v) :=
    tsupport_fderiv_apply_subset (𝕜 := ℝ) (EuclideanSpace.single j 1)
  exact h_fderiv_support.trans
    (smoothChartExt_tsupport_subset_kPouCompact (I := I) (M := M) g α v)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem exists_density_sup_on_kPouCompact
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∃ M_d : ℝ, 0 < M_d ∧
      ∀ y ∈ kPouCompact (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y ≤ M_d := by
  classical
  by_cases hKne : (kPouCompact (I := I) (M := M) α).Nonempty
  · have hK_compact : IsCompact (kPouCompact (I := I) (M := M) α) :=
      kPouCompact_isCompact (I := I) (M := M) α
    have hK_in : kPouCompact (I := I) (M := M) α ⊆
        chartTargetEuclid (I := I) (M := M) α :=
      kPouCompact_subset_chartTargetEuclid (I := I) (M := M) α
    have h_dens_contOn : ContinuousOn (densityOnEuclid (I := I) g α)
        (kPouCompact (I := I) (M := M) α) :=
      (densityOnEuclid_continuousOn (I := I) g α).mono hK_in
    obtain ⟨y₀, hy₀_mem, hy₀_max⟩ :=
      hK_compact.exists_isMaxOn hKne h_dens_contOn
    have h_pos : 0 < densityOnEuclid (I := I) g α y₀ :=
      densityOnEuclid_pos (I := I) g α (hK_in hy₀_mem)
    refine ⟨densityOnEuclid (I := I) g α y₀, h_pos, fun y hy => hy₀_max hy⟩
  · refine ⟨1, by norm_num, ?_⟩
    intro y hy
    rw [Set.not_nonempty_iff_eq_empty] at hKne
    rw [hKne] at hy
    exact absurd hy (Set.notMem_empty y)

noncomputable def chartPushedPartialLpLin
    (g : SmoothRiemannianMetric I M) (α : M) (j : Fin (Module.finrank ℝ E)) :
    SmoothScalar g →ₗ[ℝ]
      Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) where
  toFun v := chartPushedPartialLp (I := I) (M := M) g α j v
    (chartPushedPartial_memLp (I := I) (M := M) g α j v)
  map_add' v w := by
    classical
    apply MeasureTheory.Lp.ext
    have h1 := MeasureTheory.MemLp.coeFn_toLp
      (chartPushedPartial_memLp (I := I) (M := M) g α j (v + w))
    have h2 := MeasureTheory.MemLp.coeFn_toLp
      (chartPushedPartial_memLp (I := I) (M := M) g α j v)
    have h3 := MeasureTheory.MemLp.coeFn_toLp
      (chartPushedPartial_memLp (I := I) (M := M) g α j w)
    have h_aeEq_vw := chartPushedPartial_aeEq_smoothChartExtPartial
      (I := I) (M := M) g α j (v + w)
    have h_aeEq_v := chartPushedPartial_aeEq_smoothChartExtPartial
      (I := I) (M := M) g α j v
    have h_aeEq_w := chartPushedPartial_aeEq_smoothChartExtPartial
      (I := I) (M := M) g α j w
    have h_smooth_add := smoothChartExtPartial_add (I := I) (M := M) g α j v w
    have h_aeEq_combined :
        chartPushedPartial (I := I) (M := M) g α j (v + w) =ᵐ[
          (chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)]
        fun y => chartPushedPartial (I := I) (M := M) g α j v y +
            chartPushedPartial (I := I) (M := M) g α j w y := by
      filter_upwards [h_aeEq_vw, h_aeEq_v, h_aeEq_w] with y hy_vw hy_v hy_w
      rw [hy_vw, hy_v, hy_w]
      rw [h_smooth_add]
      rfl
    have h_lhs : (chartPushedPartialLp (I := I) (M := M) g α j (v + w)
        (chartPushedPartial_memLp (I := I) (M := M) g α j (v + w)) :
          EuclN → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
        chartPushedPartial (I := I) (M := M) g α j (v + w) := by
      unfold chartPushedPartialLp
      exact h1
    have h_coeAdd := MeasureTheory.Lp.coeFn_add
      (chartPushedPartialLp (I := I) (M := M) g α j v
        (chartPushedPartial_memLp (I := I) (M := M) g α j v))
      (chartPushedPartialLp (I := I) (M := M) g α j w
        (chartPushedPartial_memLp (I := I) (M := M) g α j w))
    refine h_lhs.trans (h_aeEq_combined.trans ?_)
    refine EventuallyEq.symm ?_
    filter_upwards [h_coeAdd, h2, h3] with y hy_add hy_v hy_w
    have h_v_eq : (chartPushedPartialLp (I := I) (M := M) g α j v
          (chartPushedPartial_memLp (I := I) (M := M) g α j v) :
            EuclN → ℝ) y =
          chartPushedPartial (I := I) (M := M) g α j v y := hy_v
    have h_w_eq : (chartPushedPartialLp (I := I) (M := M) g α j w
          (chartPushedPartial_memLp (I := I) (M := M) g α j w) :
            EuclN → ℝ) y =
          chartPushedPartial (I := I) (M := M) g α j w y := hy_w
    rw [hy_add, Pi.add_apply, h_v_eq, h_w_eq]
  map_smul' c v := by
    classical
    apply MeasureTheory.Lp.ext
    have h1 := MeasureTheory.MemLp.coeFn_toLp
      (chartPushedPartial_memLp (I := I) (M := M) g α j (c • v))
    have h2 := MeasureTheory.MemLp.coeFn_toLp
      (chartPushedPartial_memLp (I := I) (M := M) g α j v)
    have h_aeEq_cv := chartPushedPartial_aeEq_smoothChartExtPartial
      (I := I) (M := M) g α j (c • v)
    have h_aeEq_v := chartPushedPartial_aeEq_smoothChartExtPartial
      (I := I) (M := M) g α j v
    have h_smooth_smul := smoothChartExtPartial_smul (I := I) (M := M) g α j c v
    have h_aeEq_combined :
        chartPushedPartial (I := I) (M := M) g α j (c • v) =ᵐ[
          (chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)]
        fun y => c * chartPushedPartial (I := I) (M := M) g α j v y := by
      filter_upwards [h_aeEq_cv, h_aeEq_v] with y hy_cv hy_v
      rw [hy_cv, hy_v]
      rw [h_smooth_smul]
      rw [Pi.smul_apply, smul_eq_mul]
    have h_lhs : (chartPushedPartialLp (I := I) (M := M) g α j (c • v)
        (chartPushedPartial_memLp (I := I) (M := M) g α j (c • v)) :
          EuclN → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
        chartPushedPartial (I := I) (M := M) g α j (c • v) := by
      unfold chartPushedPartialLp
      exact h1
    have h_coeSmul := MeasureTheory.Lp.coeFn_smul c
      (chartPushedPartialLp (I := I) (M := M) g α j v
        (chartPushedPartial_memLp (I := I) (M := M) g α j v))
    refine h_lhs.trans (h_aeEq_combined.trans ?_)
    refine EventuallyEq.symm ?_
    filter_upwards [h_coeSmul, h2] with y hy_smul hy_v
    have h_v_eq : (chartPushedPartialLp (I := I) (M := M) g α j v
          (chartPushedPartial_memLp (I := I) (M := M) g α j v) :
            EuclN → ℝ) y =
          chartPushedPartial (I := I) (M := M) g α j v y := hy_v
    change ((c • (chartPushedPartialLp (I := I) (M := M) g α j v
        (chartPushedPartial_memLp (I := I) (M := M) g α j v))) : Lp ℝ 2 _) y =
        c * chartPushedPartial (I := I) (M := M) g α j v y
    rw [hy_smul, Pi.smul_apply, h_v_eq, smul_eq_mul]

omit [NeZero (Module.finrank ℝ E)] in
lemma chartPushedPartialLpLin_apply
    (g : SmoothRiemannianMetric I M) (α : M) (j : Fin (Module.finrank ℝ E))
    (v : SmoothScalar g) :
    chartPushedPartialLpLin (I := I) (M := M) g α j v =
      chartPushedPartialLp (I := I) (M := M) g α j v
        (chartPushedPartial_memLp (I := I) (M := M) g α j v) := rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem norm_chartPushedPartialLpLin
    (g : SmoothRiemannianMetric I M) (α : M) (j : Fin (Module.finrank ℝ E))
    (v : SmoothScalar g) :
    ‖chartPushedPartialLpLin (I := I) (M := M) g α j v‖ =
      (eLpNorm (chartPushedPartial (I := I) (M := M) g α j v) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))).toReal := by
  rw [chartPushedPartialLpLin_apply]
  exact norm_chartPushedPartialLp (I := I) (M := M) g α j v
    (chartPushedPartial_memLp (I := I) (M := M) g α j v)

end H1ComplGradientLipschitzBound
end Laplacian
end Analysis
end CalabiYau

end
