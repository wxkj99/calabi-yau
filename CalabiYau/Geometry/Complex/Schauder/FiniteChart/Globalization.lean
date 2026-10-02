module

public import CalabiYau.Geometry.Complex.Schauder.FiniteChart.Balls
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Globalizing identified jets from finite buffered balls

GT, Lemma 6.36, p. 136, coordinate version. All analytic compactness and derivative
identification have already been performed. This finite-cover argument shows that local C² regularity
gives manifold C² regularity, and taking a finite maximum of convergence thresholds gives
uniform convergence on each entire original compact piece, including its boundary.
-/

set_option autoImplicit false

@[expose] public section

open Filter
open scoped Manifold ContDiff Topology

namespace KahlerForm

/-- A cover refinement with identified local C² jets gives a C² manifold function and
uniform convergence of all original-chart jets on the whole original pieces. Only ball
inclusion and the finite cover are used; the pieces need not be convex or have smooth boundary.
The local derivatives are in the target chart, so no further coordinate transport occurs here. -/
theorem contMDiff_and_uniform_original_jets_of_refinement
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) (⊤ : ℕ∞ω) M]
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (balls : FiniteChartBallRefinement cover)
    (u : ℕ → M → ℝ) (s : ℕ → ℕ) (f : M → ℝ) (hf : Continuous f)
    (hlocal : ∀ p : balls.ι,
      ContDiffOn ℝ 2
        (f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
          (cover.base (balls.chart p))).symm)
        (Metric.ball (balls.center p) (balls.middleRadius p)) ∧
      ∀ k : ℕ, k ≤ 2 → TendstoUniformlyOn
        (fun j => iteratedFDeriv ℝ k
          (u (s j) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
            (cover.base (balls.chart p))).symm))
        (iteratedFDeriv ℝ k
          (f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
            (cover.base (balls.chart p))).symm)) atTop
        (Metric.closedBall (balls.center p) (balls.innerRadius p))) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 f ∧
      (∀ i : cover.ι, ∀ k : ℕ, k ≤ 2 → ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ j, N ≤ j → ∀ z ∈ cover.piece i,
          ‖iteratedFDeriv ℝ k
            (u (s j) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) z -
            iteratedFDeriv ℝ k
              (f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) z‖ < ε) := by
  constructor
  · intro x
    let : IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (⊤ : ℕ∞ω) M :=
      isManifold_of_contDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ⊤ M fun e e' he he' => by
        have hc := HasGroupoid.compatible
          (G := contDiffGroupoid (⊤ : ℕ∞ω) (𝓘(ℂ, EuclideanSpace ℂ (Fin n)))) he he'
        rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hc
        exact (hc.1.of_le le_top).restrict_scalars ℝ
    let : IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 2 M :=
      IsManifold.of_le (n := ⊤) (by norm_num)
    obtain ⟨i, z, hzpiece, hx⟩ := cover.interior_covers x
    obtain ⟨p, hpi, hzball⟩ := balls.covers_piece i z (interior_subset hzpiece)
    subst i
    let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base (balls.chart p))
    have hztarget : z ∈ e.target :=
      cover.piece_in_target (balls.chart p) (interior_subset hzpiece)
    have hxsource :
        x ∈ (chartAt (EuclideanSpace ℂ (Fin n)) (cover.base (balls.chart p))).source := by
      rw [← extChartAt_source (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n)))]
      rw [← hx]
      exact e.map_target hztarget
    have hzx : e x = z := by
      rw [← hx]
      exact e.right_inv hztarget
    have hzmiddle : z ∈ Metric.ball (balls.center p) (balls.middleRadius p) :=
      Metric.ball_subset_ball (le_of_lt (balls.inner_lt_middle p)) hzball
    have hcoordAt : ContDiffAt ℝ 2 (f ∘ e.symm) z :=
      (hlocal p).1.contDiffAt (Metric.isOpen_ball.mem_nhds hzmiddle)
    have hcoordWithin : ContDiffWithinAt ℝ 2 (f ∘ e.symm)
        (Set.range (𝓘(ℝ, EuclideanSpace ℂ (Fin n)))) (e x) := by
      rw [hzx]
      simpa [ModelWithCorners.range_eq_univ] using (contDiffWithinAt_univ.mpr hcoordAt)
    apply (contMDiffAt_iff_of_mem_source
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (I' := 𝓘(ℝ))
      (x := cover.base (balls.chart p)) (x' := x) (y := f x) hxsource (by simp)).2
    constructor
    · exact hf.continuousAt
    · simpa [e, hzx, chartAt_self_eq, ModelWithCorners.range_eq_univ] using hcoordWithin
  · intro i k hk ε hε
    classical
    have heps (p : balls.ι) : ∀ᶠ j in atTop, ∀ z ∈
        Metric.closedBall (balls.center p) (balls.innerRadius p),
        ‖iteratedFDeriv ℝ k
          (u (s j) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
            (cover.base (balls.chart p))).symm) z -
          iteratedFDeriv ℝ k
            (f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
              (cover.base (balls.chart p))).symm) z‖ < ε := by
      have h := Metric.tendstoUniformlyOn_iff.mp ((hlocal p).2 k hk) ε hε
      simpa only [dist_eq_norm, norm_sub_rev] using h
    let Np : balls.ι → ℕ := fun p => Classical.choose (eventually_atTop.1 (heps p))
    have hNp (p : balls.ι) (j : ℕ) (hj : Np p ≤ j) (z : EuclideanSpace ℂ (Fin n))
        (hz : z ∈ Metric.closedBall (balls.center p) (balls.innerRadius p)) :
        ‖iteratedFDeriv ℝ k
          (u (s j) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
            (cover.base (balls.chart p))).symm) z -
          iteratedFDeriv ℝ k
            (f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
              (cover.base (balls.chart p))).symm) z‖ < ε := by
      exact (Classical.choose_spec (eventually_atTop.1 (heps p))) j hj z hz
    let N := Finset.univ.sup (fun p : balls.ι => Np p)
    refine ⟨N, ?_⟩
    intro j hj z hz
    obtain ⟨p, hpi, hzball⟩ := balls.covers_piece i z hz
    have hNle : Np p ≤ N := Finset.le_sup (Finset.mem_univ p)
    have hball : z ∈ Metric.closedBall (balls.center p) (balls.innerRadius p) :=
      Metric.ball_subset_closedBall hzball
    rw [← hpi]
    exact hNp p j (le_trans hNle hj) z hball

end KahlerForm
