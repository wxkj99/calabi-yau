-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Integration/Measure/Riemannian/Basic.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Riemannian.Volume.Chart.Density
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff ENNReal

namespace CalabiYau.RiemannianVolume

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable (I M) in
def chartAtlasPOU [T2Space M] [SigmaCompactSpace M] :
    SmoothPartitionOfUnity M I M univ :=
  (SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source I M).choose

variable (I M) in
lemma chartAtlasPOU_isSubordinate [T2Space M] [SigmaCompactSpace M] :
    (chartAtlasPOU I M).IsSubordinate (fun x : M => (chartAt H x).source) :=
  (SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source I M).choose_spec

def riemannianMeasure
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ) : MeasureTheory.Measure M :=
  MeasureTheory.Measure.sum fun α : M =>
    (chartLocalMeasure (I := I) g α).withDensity
      (fun x : M => ENNReal.ofReal (ρ α x))

lemma riemannianMeasure_def
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ) :
    riemannianMeasure (I := I) g ρ =
      MeasureTheory.Measure.sum (fun α : M =>
        (chartLocalMeasure (I := I) g α).withDensity
          (fun x : M => ENNReal.ofReal (ρ α x))) := rfl

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
lemma measurable_ofReal_pou_weight
    (ρ : SmoothPartitionOfUnity M I M univ) (α : M) :
    Measurable (fun x : M => ENNReal.ofReal (ρ α x)) := by
  have hcont : Continuous (fun x : M => ρ α x) :=
    (ρ α).contMDiff.continuous
  exact ENNReal.measurable_ofReal.comp hcont.measurable

theorem riemannianMeasure_lintegral_eq
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ)
    {f : M → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂(riemannianMeasure (I := I) g ρ) =
      ∑' α : M, ∫⁻ x, ENNReal.ofReal (ρ α x) * f x
          ∂(chartLocalMeasure (I := I) g α) := by
  classical
  rw [riemannianMeasure_def, lintegral_sum_measure]
  refine tsum_congr (fun α => ?_)
  have hρ : Measurable (fun x : M => ENNReal.ofReal (ρ α x)) := by
    have hcont : Continuous (fun x : M => ρ α x) := (ρ α).contMDiff.continuous
    exact ENNReal.measurable_ofReal.comp hcont.measurable
  have h :=
    lintegral_withDensity_eq_lintegral_mul (μ := chartLocalMeasure (I := I) g α)
      (f := fun x : M => ENNReal.ofReal (ρ α x)) hρ (g := f) hf
  simpa [Pi.mul_apply] using h

theorem chartLocalMeasure_withDensity_le_riemannianMeasure
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ) (α : M) :
    (chartLocalMeasure (I := I) g α).withDensity
        (fun x : M => ENNReal.ofReal (ρ α x))
      ≤ riemannianMeasure (I := I) g ρ := by
  rw [riemannianMeasure_def]
  exact MeasureTheory.Measure.le_sum _ α

end CalabiYau.RiemannianVolume
