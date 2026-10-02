module

public import CalabiYau.Analysis.Sobolev.Manifold.Rellich.OnManifold
public import CalabiYau.Geometry.Kahler.Sobolev
public import CalabiYau.Geometry.Kahler.Riemannian.Metric
public import CalabiYau.Geometry.Kahler.Riemannian.Volume
public import CalabiYau.Geometry.Kahler.Riemannian.Laplacian
public import CalabiYau.Geometry.Kahler.Sobolev.RellichCompactness.ChartEnergy

/-!
# Rellich compactness for Kähler energy-bounded sequences

The chart-energy comparison is supplied by the `ChartEnergy` prerequisite. This file applies that
bridge and then the extracted chart Rellich theorem, accounting for the Kähler/Riemannian volume
identity and the factor `|∇f|² = 2 |∂f|²`.
-/

@[expose] public section

open scoped Manifold ContDiff
open MeasureTheory Filter Topology
open CalabiYau CalabiYau.Riemannian

namespace KahlerForm

/-- Uniformly bounded `L²` norm and Kähler gradient energy on a compact positive-dimensional
Kähler manifold imply `L²` precompactness. -/
theorem rellichCompactness
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M]
    [SigmaCompactSpace M]
    (hn : 0 < n)
    (ω₀ : KahlerForm n M)
    (f : ℕ → M → ℝ)
    (hf : ∀ k, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (f k))
    (B : ℝ) (hB : 0 ≤ B)
    (henergy : ∀ k, ∫ x, (f k x ^ 2 + ω₀.gradNormSq (f k) x) ∂ω₀.volume ≤ B) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ u : M → ℝ,
      MemLp u (ENNReal.ofReal 2) ω₀.volume ∧
        Filter.Tendsto
          (fun j => eLpNorm (fun x => f (σ j) x - u x) (ENNReal.ofReal 2) ω₀.volume)
          Filter.atTop (𝓝 0) := by
  cases BorelSpace.measurable_eq (α := M)
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  let g := ω₀.toRiemannianMetric
  have hvol : ω₀.volume = RiemannianVolume.riemannianMeasure
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) g
      (RiemannianVolume.chartAtlasPOU (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) M) := by
    simpa [g] using ω₀.volume_eq_riemannianMeasure_chartAtlasPOU
  have hgrad : ∀ f₀ : M → ℝ,
      ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f₀ →
      ∀ x, g.inner x (gradFun (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) g f₀ x)
          (gradFun (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) g f₀ x) =
        2 * ω₀.gradNormSq f₀ x := by
    intro f₀ hf₀ x
    simpa [g] using ω₀.riemannian_gradFun_energy_eq_two_mul_gradNormSq f₀ hf₀ x
  have hchart := smooth_seq_energy_bound_to_chart_wkp ω₀ g hvol hgrad f hf B hB henergy
  haveI : NeZero (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))) := by
    have hdim : 0 < Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) := by
      letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      exact Module.finrank_pos
    exact ⟨hdim.ne'⟩
  obtain ⟨R, _, hchartBound⟩ := hchart.2.2
  obtain ⟨σ, hσ, u, hu, hlim⟩ :=
    Sobolev.Chart.rellich_kondrachov_chart_seq g (p := 2) (by norm_num)
      hchart.1 hchart.2.1 hchartBound
  refine ⟨σ, hσ, u, ?_, ?_⟩
  · rw [hvol]
    exact hu
  · rw [hvol]
    exact hlim

end KahlerForm
