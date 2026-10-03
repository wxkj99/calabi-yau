-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Intrinsic/Equivalence/IntrinsicToChart/UnitFiber.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Intrinsic.Equivalence.NormEquivalence
public import CalabiYau.Analysis.Sobolev.Manifold.Measure.UniformChartComparison

@[expose] public section


noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace Sobolev
namespace EquivalenceReverse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open Sobolev.Chart

local notation "EuclN_E" =>
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

noncomputable def chartTargetUnitFiber (α : M)
    (i : Fin (Module.finrank ℝ E)) (x : M) : TangentSpace I x :=
  (trivializationAt E (TangentSpace I) α).symm x
    ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E).symm
      (EuclideanSpace.single i (1 : ℝ)))

private lemma chartTargetUnit_smoothOn (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (chartTargetUnitFiber (I := I) α i x))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  set v_E : E := (toEuclidean (E := E) : E ≃L[ℝ] EuclN_E).symm
    (EuclideanSpace.single i (1 : ℝ)) with hv_E_def
  have hiff :=
    ((trivializationAt E (TangentSpace I) α)).contMDiffOn_section_baseSet_iff
      (IB := I) (n := ∞)
      (s := fun x : M => (trivializationAt E (TangentSpace I) α).symm x v_E)
  refine hiff.mpr ?_
  have hconst : ContMDiffOn I 𝓘(ℝ, E) ∞ (fun _ : M => v_E)
      (trivializationAt E (TangentSpace I) α).baseSet := contMDiffOn_const
  refine hconst.congr ?_
  intro x hx
  exact congrArg Prod.snd
    ((trivializationAt E (TangentSpace I) α).apply_mk_symm hx v_E)

lemma g_inner_chartTargetUnit_continuousOn
    (g : CalabiYau.SmoothRiemannianMetric I M)
    (α : M) (i : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun x : M => g.inner x
        (chartTargetUnitFiber (I := I) α i x)
        (chartTargetUnitFiber (I := I) α i x))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  have hg : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        b (g.inner b))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    g.contMDiff.contMDiffOn
  have hv := chartTargetUnit_smoothOn (I := I) α i
  have happ :
      ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun m : M => (⟨m,
            g.inner m
              (chartTargetUnitFiber (I := I) α i m)
              (chartTargetUnitFiber (I := I) α i m)⟩ :
              TotalSpace ℝ (Bundle.Trivial M ℝ)))
        (trivializationAt E (TangentSpace I) α).baseSet :=
    ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (b := id) hg hv hv
  intro x hx
  have hpx := happ x hx
  rw [Bundle.contMDiffWithinAt_totalSpace] at hpx
  exact (hpx.2.continuousWithinAt)

noncomputable def chartTargetUnitSqSumSupOnPouTsupport
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : CalabiYau.SmoothRiemannianMetric I M)
    (α : M) : ℝ := by
  classical
  set Kα : Set M := tsupport
    ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hKα_def
  by_cases hKα_ne : Kα.Nonempty
  · have hKα_compact : IsCompact Kα := (isClosed_tsupport _).isCompact
    have hKα_sub : Kα ⊆ (chartAt H α).source :=
      CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M α
    have hKα_base : Kα ⊆ (trivializationAt E (TangentSpace I) α).baseSet := by
      intro x hx
      rw [CalabiYau.RiemannianVolume.trivializationAt_baseSet_eq_chartAt_source]
      exact hKα_sub hx
    have h_cont : ContinuousOn
        (fun x : M => ∑ i : Fin (Module.finrank ℝ E),
          g.inner x
            (chartTargetUnitFiber (I := I) α i x)
            (chartTargetUnitFiber (I := I) α i x)) Kα := by
      apply continuousOn_finsetSum
      intro i _
      exact (g_inner_chartTargetUnit_continuousOn (I := I) g α i).mono hKα_base
    exact (hKα_compact.image_of_continuousOn h_cont).bddAbove.choose
  · exact 0

lemma chartTargetUnitSqSumSupOnPouTsupport_nonneg
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : CalabiYau.SmoothRiemannianMetric I M)
    (α : M) :
    0 ≤ chartTargetUnitSqSumSupOnPouTsupport (I := I) (M := M) g α := by
  classical
  unfold chartTargetUnitSqSumSupOnPouTsupport
  set Kα : Set M := tsupport
    ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hKα_def
  by_cases hKα_ne : Kα.Nonempty
  · rw [dite_eq_left hKα_ne]
    have hKα_compact : IsCompact Kα := (isClosed_tsupport _).isCompact
    have hKα_sub : Kα ⊆ (chartAt H α).source :=
      CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M α
    have hKα_base : Kα ⊆ (trivializationAt E (TangentSpace I) α).baseSet := by
      intro x hx
      rw [CalabiYau.RiemannianVolume.trivializationAt_baseSet_eq_chartAt_source]
      exact hKα_sub hx
    have h_cont : ContinuousOn
        (fun x : M => ∑ i : Fin (Module.finrank ℝ E),
          g.inner x
            (chartTargetUnitFiber (I := I) α i x)
            (chartTargetUnitFiber (I := I) α i x)) Kα := by
      apply continuousOn_finsetSum
      intro i _
      exact (g_inner_chartTargetUnit_continuousOn (I := I) g α i).mono hKα_base
    set hImage :=
      (hKα_compact.image_of_continuousOn h_cont).bddAbove
    obtain ⟨x₀, hx₀⟩ := hKα_ne
    have h_val_nn : (0 : ℝ) ≤
        ∑ i : Fin (Module.finrank ℝ E),
          g.inner x₀
            (chartTargetUnitFiber (I := I) α i x₀)
            (chartTargetUnitFiber (I := I) α i x₀) := by
      apply Finset.sum_nonneg
      intro i _
      by_cases hzero : chartTargetUnitFiber (I := I) α i x₀ = 0
      · rw [hzero]
        change ((g.inner x₀) (0 : TangentSpace I x₀)) (0 : TangentSpace I x₀) ≥ 0
        rw [(g.inner x₀).map_zero]
        change (0 : TangentSpace I x₀ →L[ℝ] ℝ) (0 : TangentSpace I x₀) ≥ 0
        simp
      · exact (g.pos x₀ _ hzero).le
    have hx₀_val :
        (∑ i : Fin (Module.finrank ℝ E),
          g.inner x₀
            (chartTargetUnitFiber (I := I) α i x₀)
            (chartTargetUnitFiber (I := I) α i x₀)) ∈
        (fun x : M => ∑ i : Fin (Module.finrank ℝ E),
          g.inner x
            (chartTargetUnitFiber (I := I) α i x)
            (chartTargetUnitFiber (I := I) α i x)) '' Kα :=
      ⟨x₀, hx₀, rfl⟩
    have h_le := hImage.choose_spec hx₀_val
    exact le_trans h_val_nn h_le
  · rw [dite_eq_right hKα_ne]

lemma chartTargetUnitSqSum_le_sup
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : CalabiYau.SmoothRiemannianMetric I M)
    (α : M) {x : M}
    (hx : x ∈ tsupport
      ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :
    ∑ i : Fin (Module.finrank ℝ E),
        g.inner x
          (chartTargetUnitFiber (I := I) α i x)
          (chartTargetUnitFiber (I := I) α i x) ≤
      chartTargetUnitSqSumSupOnPouTsupport (I := I) (M := M) g α := by
  classical
  unfold chartTargetUnitSqSumSupOnPouTsupport
  set Kα : Set M := tsupport
    ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hKα_def
  have hKα_ne : Kα.Nonempty := ⟨x, hx⟩
  rw [dite_eq_left hKα_ne]
  have hKα_compact : IsCompact Kα := (isClosed_tsupport _).isCompact
  have hKα_sub : Kα ⊆ (chartAt H α).source :=
    CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M α
  have hKα_base : Kα ⊆ (trivializationAt E (TangentSpace I) α).baseSet := by
    intro y hy
    rw [CalabiYau.RiemannianVolume.trivializationAt_baseSet_eq_chartAt_source]
    exact hKα_sub hy
  have h_cont : ContinuousOn
      (fun y : M => ∑ i : Fin (Module.finrank ℝ E),
        g.inner y
          (chartTargetUnitFiber (I := I) α i y)
          (chartTargetUnitFiber (I := I) α i y)) Kα := by
    apply continuousOn_finsetSum
    intro i _
    exact (g_inner_chartTargetUnit_continuousOn (I := I) g α i).mono hKα_base
  set hImage :=
    (hKα_compact.image_of_continuousOn h_cont).bddAbove
  exact hImage.choose_spec ⟨x, hx, rfl⟩

end EquivalenceReverse
end Sobolev
