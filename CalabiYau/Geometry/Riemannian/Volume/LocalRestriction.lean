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

end CalabiYau.RiemannianVolume
