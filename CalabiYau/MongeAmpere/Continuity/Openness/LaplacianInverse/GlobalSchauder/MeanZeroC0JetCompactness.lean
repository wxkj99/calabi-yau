module

public import CalabiYau.MongeAmpere.Continuity.Openness.LaplacianInverse.GlobalSchauder.LocalEstimate
public import CalabiYau.Geometry.Complex.Schauder.FiniteChart.Bounds
public import CalabiYau.Geometry.Complex.Schauder.FiniteChart.ValueLimit
public import CalabiYau.Geometry.Complex.Schauder.FiniteChart.JetIdentification
public import CalabiYau.Geometry.Complex.Schauder.FiniteChart.Globalization
public import CalabiYau.Geometry.Kahler.Laplacian.FiniteRegularityChart
public import CalabiYau.Geometry.Kahler.Laplacian.JetLimit
public import CalabiYau.Analysis.Holder.Compactness.Normalization

/-!
# Finite-chart C² compactness and passage to a harmonic limit

With `0 < α`, the uniform order-two Hölder bound makes the second-order chart jets
equicontinuous on buffered convex balls after a fixed change of coordinates. Arzelà–Ascoli
on those balls, a common subsequence for their three jet orders, and value compatibility on
overlaps give a genuine C² limit. Inner balls cover every original compact piece, including
its boundary; no regular-domain hypothesis on those pieces is needed. The finite zero-order
Laplacian gauges control the pointwise Laplacians; convergence of the second-order jets, not
just convergence in C⁰, then makes the limit harmonic. The fixed top manifold regularity below
is the existing analytic `ω` convention, written explicitly rather than as an implicit variable.
-/

set_option autoImplicit false

@[expose] public section

open Filter
open scoped Manifold ContDiff NNReal Topology
open MeasureTheory

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) (⊤ : ℕ∞ω) M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]

omit [ConnectedSpace M] in
/-- Compactness in C² for normalized functions with vanishing Laplacian. The explicit uniform
convergence of all three chart-jet orders prevents an unjustified passage of `Δ` through mere
C⁰ convergence. Continuity of the integral preserves the mean; compactness preserves an
attained absolute value one, without a unit supremum bound. The harmonic limit need only be C²,
not smooth. -/
theorem exists_normalized_meanZero_laplacian_C2_compactness [Nonempty M]
    (ω₁ : KahlerForm n M) (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (α : ℝ≥0) (hα₀ : 0 < α) (hα₁ : α < 1)
    (u : ℕ → M → ℝ)
    (huSmooth : ∀ j, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (u j))
    (huMean : ∀ j, ∫ x, u j x ∂ω₁.volume = 0)
    (huNorm : ∀ j, ∃ x, |u j x| = 1)
    (huC2 : ∃ B : ℝ≥0, ∀ j,
      finiteChartHolderGauge cover 2 α (u j) < ⊤ ∧
      (finiteChartHolderGauge cover 2 α (u j)).toReal ≤ (B : ℝ))
    (huFinite : ∀ j, finiteChartHolderGauge cover 0 α (ω₁.laplacian (u j)) < ⊤)
    (huSmall : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ j, N ≤ j →
      (finiteChartHolderGauge cover 0 α (ω₁.laplacian (u j))).toReal < ε) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 f ∧
      (∀ i : cover.ι, ∀ k : ℕ, k ≤ 2 → ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ j, N ≤ j → ∀ z ∈ cover.piece i,
          ‖iteratedFDeriv ℝ k
            (u (s j) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) z -
            iteratedFDeriv ℝ k
              (f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) z‖ < ε) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ j, N ≤ j → ∀ x,
        |u (s j) x - f x| < ε) ∧
      (∫ x, f x ∂ω₁.volume = 0) ∧
      ω₁.laplacian f = 0 ∧
      ∃ x, |f x| = 1 := by
  classical
  obtain ⟨balls⟩ := exists_finiteChartBallRefinement cover
  obtain ⟨B, hB⟩ := huC2
  obtain ⟨C, hC⟩ := exists_uniform_holderBoundOn_refinement cover balls α hα₀ hα₁
    u huSmooth B (fun j => (hB j).1) (fun j => (hB j).2)
  obtain ⟨s, hs, ⟨limits⟩⟩ := exists_common_subsequence_finiteChartJetLimits
    cover balls α hα₀ hα₁ u C hC
  obtain ⟨f, hfContinuous, hconv, hvalues⟩ :=
    exists_uniform_value_limit_of_finiteChartJetLimits cover balls u s
      (fun j => (huSmooth j).continuous) limits
  have hlocal (p : balls.ι) := identify_uniform_jet_limits_on_nested_balls
    (balls.inner_pos p) (balls.inner_lt_middle p) (balls.middle_lt_outer p)
    (fun j => u (s j) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      (cover.base (balls.chart p))).symm)
    (f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      (cover.base (balls.chart p))).symm)
    (fun j => (hC p (s j)).1)
    (limits.value p) (limits.first p) (limits.second p) (hvalues p)
    (limits.uniform_value p) (limits.uniform_first p) (limits.uniform_second p)
  obtain ⟨hf, hjets⟩ := contMDiff_and_uniform_original_jets_of_refinement
    cover balls u s f hfContinuous hlocal
  have hpoint : ∀ i : cover.ι, ∀ z ∈ cover.piece i, Tendsto
      (fun j => iteratedFDeriv ℝ 2
        (u (s j) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) z)
      atTop (𝓝 (iteratedFDeriv ℝ 2
        (f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) z)) := by
    intro i z hz
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := hjets i 2 le_rfl ε hε
    refine ⟨N, fun j hj => ?_⟩
    simpa only [dist_eq_norm] using hN j hj z hz
  have hformula (i : cover.ι) (z : EuclideanSpace ℂ (Fin n))
      (hz : z ∈ cover.piece i) :
      ω₁.laplacian f ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm z) =
        RCLike.re ((ω₁.metricInChart (cover.base i) z)⁻¹ *
          complexHessian (f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
            (cover.base i)).symm) z).trace := by
    let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)
    have hzTarget : z ∈ e.target := cover.piece_in_target i hz
    have hy : e.symm z ∈ (chartAt (EuclideanSpace ℂ (Fin n)) (cover.base i)).source := by
      rw [← extChartAt_source (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (cover.base i)]
      exact e.map_target hzTarget
    have h := laplacian_eq_inChart_of_contMDiff_two ω₁ f hf (cover.base i) hy
    change ω₁.laplacian f (e.symm z) = RCLike.re
      ((ω₁.metricInChart (cover.base i) (e (e.symm z)))⁻¹ *
        complexHessian (f ∘ e.symm) (e (e.symm z))).trace at h
    rw [e.right_inv hzTarget] at h
    exact h
  have hLap := laplacian_eq_zero_of_second_jet_limit ω₁ cover α u s hs
    huSmooth f hformula hpoint huFinite huSmall
  obtain ⟨hmean, hnorm⟩ := integral_zero_and_exists_abs_eq_one_of_uniform_limit
    ω₁.volume (fun j => u (s j)) f (fun j => (huSmooth (s j)).continuous)
    hfContinuous hconv (fun j => huMean (s j)) (fun j => huNorm (s j))
  refine ⟨s, hs, f, hf, hjets, ?_, hmean, hLap, hnorm⟩
  intro ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    ((Metric.tendstoUniformly_iff.mp hconv) ε hε)
  refine ⟨N, fun j hj x => ?_⟩
  simpa only [Real.dist_eq, abs_sub_comm] using hN j hj x

end KahlerForm
