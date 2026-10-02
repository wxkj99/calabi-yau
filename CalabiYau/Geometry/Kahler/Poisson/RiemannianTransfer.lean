module

public import CalabiYau.Geometry.Kahler.Poisson
public import CalabiYau.Geometry.Kahler.Riemannian.Volume
public import CalabiYau.Geometry.Kahler.Riemannian.Laplacian

/-!
# Transfer from the real Riemannian Poisson equation

This is a conditional bridge, not an analytic existence theorem. A real-smooth solver for the
canonical Riemannian volume and Laplace--Beltrami operator gives the Kähler Poisson solver after
rescaling the source by two, since `ΔG = 2 * Δω` and the two volume measures agree.
-/

@[expose] public section

open scoped Manifold ContDiff
open MeasureTheory

namespace CalabiYau

/-- A smooth mean-zero Poisson solver for the canonical Riemannian metric induced by a Kähler form
implies the corresponding Kähler Poisson solvability. The real Laplacian convention is twice the
complex one, so the solver is applied to `2 * f`. -/
theorem poissonSolvable_of_riemannian_solver
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [SigmaCompactSpace M]
    (ω₀ : KahlerForm n M)
    (hsolve : ∀ (f : M → ℝ),
      ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f →
      ∫ x, f x ∂CalabiYau.RiemannianVolume.riemannianVolumeMeasure
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) ω₀.toRiemannianMetric = 0 →
      ∃ (u : M → ℝ), ∃ hu : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u,
        ∀ x, CalabiYau.Riemannian.ΔG
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) ω₀.toRiemannianMetric ⟨u, hu⟩ x = f x) :
    ω₀.PoissonSolvable := by
  classical
  cases BorelSpace.measurable_eq (α := M)
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  intro f hf hmean
  let q : M → ℝ := fun x => 2 * f x
  have hq : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ q := by
    have hqeq : q = f + f := by
      funext x
      dsimp [q]
      ring
    rw [hqeq]
    exact hf.add hf
  have hvol : ω₀.volume = CalabiYau.RiemannianVolume.riemannianVolumeMeasure
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) ω₀.toRiemannianMetric := by
    exact ω₀.volume_eq_riemannianVolumeMeasure
  have hqmean : ∫ x, q x ∂CalabiYau.RiemannianVolume.riemannianVolumeMeasure
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) ω₀.toRiemannianMetric = 0 := by
    rw [← hvol]
    simp [q, integral_const_mul, hmean]
  obtain ⟨u, hu, hsol⟩ := hsolve q hq hqmean
  have hlap : ω₀.laplacian u = f := by
    funext x
    have hbridge := ω₀.riemannian_laplacian_eq_two_mul_laplacian u hu x
    have hsolx := hsol x
    dsimp [q] at hsolx
    rw [hbridge] at hsolx
    linarith
  exact ⟨u, hu, hlap⟩

end CalabiYau
