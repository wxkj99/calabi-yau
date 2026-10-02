module

public import CalabiYau.Geometry.Complex.Schauder.FiniteChart.Extraction

/-!
# Agreement of finite-chart value limits

GT, Lemma 6.36, p. 136, finite-chart version: uniqueness of a pointwise limit identifies
values on overlaps. Finite uniform convergence then gives a global uniform limit. This step
contains no derivative identification and uses no Laplacian equation.
-/

set_option autoImplicit false

@[expose] public section

open Filter
open scoped Manifold ContDiff Topology

namespace KahlerForm

/-- The raw value limits agree on overlaps, since each is a limit of the same scalar
sequence. All original pieces are covered by inner balls, so their images cover the manifold.
The value identities are also valid on the full middle closed balls, as needed for local
identification of derivatives. -/
theorem exists_uniform_value_limit_of_finiteChartJetLimits
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (balls : FiniteChartBallRefinement cover)
    (u : ℕ → M → ℝ) (s : ℕ → ℕ)
    (hu : ∀ j, Continuous (u j))
    (limits : FiniteChartJetLimits balls u s) :
    ∃ f : M → ℝ, Continuous f ∧
      TendstoUniformly (fun j => u (s j)) f atTop ∧
      ∀ p : balls.ι,
        ∀ z : Metric.closedBall (balls.center p) (balls.middleRadius p),
          limits.value p z = f ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
            (cover.base (balls.chart p))).symm z) := by
  classical
  have hpoint : ∀ x : M, ∃ y : ℝ,
      Tendsto (fun j => u (s j) x) atTop (nhds y) := by
    intro x
    obtain ⟨i, z, hzpiece, hzpoint⟩ := cover.interior_covers x
    obtain ⟨p, hpi, hzinner⟩ := balls.covers_piece i z (interior_subset hzpiece)
    have hzcoord : (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
        (cover.base (balls.chart p))).symm z = x := by
      simpa [hpi] using hzpoint
    have hzmiddle : z ∈ Metric.closedBall (balls.center p) (balls.middleRadius p) := by
      rw [Metric.mem_closedBall]
      have hdist : dist z (balls.center p) < balls.innerRadius p :=
        Metric.mem_ball.mp hzinner
      exact le_of_lt (hdist.trans_le (le_of_lt (balls.inner_lt_middle p)))
    refine ⟨limits.value p ⟨z, hzmiddle⟩, ?_⟩
    have hzcoord' : (chartAt (EuclideanSpace ℂ (Fin n))
        (cover.base (balls.chart p))).symm z = x := by
      simpa using hzcoord
    have ht := (limits.uniform_value p).tendsto_at (⟨z, hzmiddle⟩ :
      Metric.closedBall (balls.center p) (balls.middleRadius p))
    simpa [hzcoord'] using ht
  let f : M → ℝ := fun x => Classical.choose (hpoint x)
  have hfpoint : ∀ x : M, Tendsto (fun j => u (s j) x) atTop (nhds (f x)) := by
    intro x
    exact Classical.choose_spec (hpoint x)
  have hvalue : ∀ p : balls.ι,
      ∀ z : Metric.closedBall (balls.center p) (balls.middleRadius p),
        limits.value p z = f ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
          (cover.base (balls.chart p))).symm z) := by
    intro p z
    have ht := (limits.uniform_value p).tendsto_at z
    exact tendsto_nhds_unique ht (hfpoint _)
  have huniform : TendstoUniformly (fun j => u (s j)) f atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have hev : ∀ᶠ j : ℕ in atTop, ∀ p : balls.ι,
        ∀ z : Metric.closedBall (balls.center p) (balls.middleRadius p),
          dist (u (s j) ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
            (cover.base (balls.chart p))).symm z)) (limits.value p z) < ε := by
      have hfinite : ∀ p ∈ (Finset.univ : Finset balls.ι),
          ∀ᶠ j : ℕ in atTop,
            ∀ z : Metric.closedBall (balls.center p) (balls.middleRadius p),
              dist (u (s j) ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
                (cover.base (balls.chart p))).symm z)) (limits.value p z) < ε := by
        intro p hp
        have hevent := (Metric.tendstoUniformly_iff.mp (limits.uniform_value p)) ε hε
        filter_upwards [hevent] with j hj z
        rw [dist_comm]
        exact hj z
      have hall := (Filter.eventually_all_finset (Finset.univ : Finset balls.ι)).mpr hfinite
      simpa only [Finset.mem_univ, true_implies] using hall
    filter_upwards [hev] with j hj x
    obtain ⟨i, z, hzpiece, hzpoint⟩ := cover.interior_covers x
    obtain ⟨p, hpi, hzinner⟩ := balls.covers_piece i z (interior_subset hzpiece)
    have hzcoord : (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
        (cover.base (balls.chart p))).symm z = x := by
      simpa [hpi] using hzpoint
    have hzmiddle : z ∈ Metric.closedBall (balls.center p) (balls.middleRadius p) := by
      rw [Metric.mem_closedBall]
      have hdist : dist z (balls.center p) < balls.innerRadius p :=
        Metric.mem_ball.mp hzinner
      exact le_of_lt (hdist.trans_le (le_of_lt (balls.inner_lt_middle p)))
    have hpt := hj p ⟨z, hzmiddle⟩
    rw [← hzcoord]
    rw [← hvalue p (⟨z, hzmiddle⟩ : Metric.closedBall (balls.center p) (balls.middleRadius p))]
    rw [dist_comm]
    simpa using hpt
  have hfcontinuous : Continuous f := by
    refine huniform.continuous ?_
    exact Filter.Eventually.frequently (Filter.Eventually.of_forall (fun j => hu (s j)))
  exact ⟨f, hfcontinuous, huniform, hvalue⟩

end KahlerForm
