module

public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderCarrier.Basic

@[expose] public section

open scoped Manifold ContDiff NNReal ENNReal Topology

namespace KahlerForm

private theorem eSupNormOn_smul_local {X F : Type*} [MetricSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (s : Set X) (g : X → F) (c : ℝ) :
    CalabiYau.Schauder.eSupNormOn s (c • g) =
      (‖c‖₊ : ℝ≥0∞) * CalabiYau.Schauder.eSupNormOn s g := by
  unfold CalabiYau.Schauder.eSupNormOn
  simp_rw [Pi.smul_apply, norm_smul, ENNReal.ofReal_mul (norm_nonneg c),
    ofReal_norm, enorm_eq_nnnorm]
  rw [ENNReal.mul_iSup]

private theorem eHolderSeminormOn_smul_local {X F : Type*} [MetricSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (alpha : ℝ≥0) (s : Set X) (g : X → F) (c : ℝ) :
    CalabiYau.Schauder.eHolderSeminormOn alpha s (c • g) =
      (‖c‖₊ : ℝ≥0∞) * CalabiYau.Schauder.eHolderSeminormOn alpha s g := by
  unfold CalabiYau.Schauder.eHolderSeminormOn
  change eHolderNorm alpha (c • s.domRestrict g) = _
  exact eHolderNorm_smul c

private theorem eContDiffHolderGaugeOn_smul_local
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (k : ℕ) (alpha : ℝ≥0) (s : Set V) (g : V → F) (c : ℝ)
    (hg : ∀ x ∈ s, ContDiffAt ℝ k g x) :
    CalabiYau.Schauder.eContDiffHolderGaugeOn k alpha s (c • g) =
      (‖c‖₊ : ℝ≥0∞) * CalabiYau.Schauder.eContDiffHolderGaugeOn k alpha s g := by
  have hjet : ∀ j ≤ k, Set.EqOn
      (iteratedFDeriv ℝ j (c • g))
      (c • iteratedFDeriv ℝ j g) s := by
    intro j hj x hx
    exact iteratedFDeriv_const_smul_apply
      ((hg x hx).of_le (by exact_mod_cast hj))
  unfold CalabiYau.Schauder.eContDiffHolderGaugeOn
  calc
    (∑ j ∈ Finset.range (k + 1),
        CalabiYau.Schauder.eSupNormOn s (iteratedFDeriv ℝ j (c • g))) +
        CalabiYau.Schauder.eHolderSeminormOn alpha s (iteratedFDeriv ℝ k (c • g)) =
      (∑ j ∈ Finset.range (k + 1),
        CalabiYau.Schauder.eSupNormOn s (c • iteratedFDeriv ℝ j g)) +
        CalabiYau.Schauder.eHolderSeminormOn alpha s (c • iteratedFDeriv ℝ k g) := by
      congr 1
      · apply Finset.sum_congr rfl
        intro j hj
        exact CalabiYau.Schauder.eSupNormOn_congr
          (hjet j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
      · exact CalabiYau.Schauder.eHolderSeminormOn_congr
          (hjet k le_rfl) alpha
    _ = (‖c‖₊ : ℝ≥0∞) *
        ((∑ j ∈ Finset.range (k + 1),
          CalabiYau.Schauder.eSupNormOn s (iteratedFDeriv ℝ j g)) +
          CalabiYau.Schauder.eHolderSeminormOn alpha s (iteratedFDeriv ℝ k g)) := by
      simp_rw [eSupNormOn_smul_local, eHolderSeminormOn_smul_local]
      rw [← Finset.mul_sum, ← mul_add]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] in
/-- The finite-chart Hölder gauge is absolutely homogeneous on the fixed smooth core. -/
theorem smoothChartHolderGauge_smul
    (cover : CompactChartCover E M) (k : ℕ) (α : ℝ≥0)
    (c : ℝ) (f : SmoothChartHolderCore cover k α) :
    smoothChartHolderGauge cover k α (c • f) =
      (‖c‖₊ : ℝ≥0∞) * smoothChartHolderGauge cover k α f := by
  classical
  unfold smoothChartHolderGauge finiteChartHolderGauge
  rw [ENNReal.mul_iSup]
  apply iSup_congr
  intro i
  have hcoordinate (g : SmoothChartHolderCore cover k α) :
      ∀ x ∈ cover.piece i,
        ContDiffAt ℝ k
          (g.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) x := by
    intro x hx
    have hxTarget : x ∈ (extChartAt 𝓘(ℝ, E) (cover.base i)).target :=
      cover.piece_in_target i hx
    have hcomp : ContMDiffOn 𝓘(ℝ, E) (modelWithCornersSelf ℝ ℝ) ∞
        (g.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm)
        (extChartAt 𝓘(ℝ, E) (cover.base i)).target := by
      exact g.smoothMap.contMDiff.comp_contMDiffOn
        (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, E)) (cover.base i))
    have hwithin := hcomp x hxTarget
    have hdiff : ContDiffWithinAt ℝ ∞
        (g.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm)
        (extChartAt 𝓘(ℝ, E) (cover.base i)).target x :=
      (contMDiffWithinAt_iff_contDiffWithinAt.mp hwithin)
    have hnhds : (extChartAt 𝓘(ℝ, E) (cover.base i)).target ∈ 𝓝 x :=
      (isOpen_extChartAt_target (I := 𝓘(ℝ, E)) (cover.base i)).mem_nhds hxTarget
    exact (hdiff.contDiffAt hnhds).of_le (by exact_mod_cast le_top)
  have hcoreSmul : (c • f).smoothMap = c • f.smoothMap := by
    change smoothChartHolderCoreEquivSmoothMap cover k α (c • f) =
      c • smoothChartHolderCoreEquivSmoothMap cover k α f
    simp [Equiv.smul_def, smoothChartHolderCoreEquivSmoothMap]
  rw [hcoreSmul]
  have hcompSmul :
      (c • f.smoothMap) ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm =
        c • (f.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) := by
    funext x
    simp [Function.comp_def]
  rw [hcompSmul]
  exact eContDiffHolderGaugeOn_smul_local k α (cover.piece i)
    (f.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) c (hcoordinate f)

end KahlerForm
