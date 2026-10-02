module

public import CalabiYau.Geometry.Kahler.Sobolev
public import CalabiYau.Geometry.Kahler.Sobolev.AboveTwo
public import CalabiYau.Geometry.Kahler.Sobolev.DimensionTwo
public import CalabiYau.Geometry.Kahler.Sobolev.DimensionZero
public import CalabiYau.Geometry.Kahler.Riemannian.Metric
public import CalabiYau.Geometry.Kahler.Riemannian.Volume
public import CalabiYau.Geometry.Riemannian.Volume.Invariance
public import CalabiYau.Geometry.Kahler.Riemannian.Laplacian

/-!
# Existence of a Sobolev inequality on compact Kähler manifolds

The real dimension of a complex `n`-fold is `2n`. For `n = 0` use the finite-dimensional
zero-dimensional estimate; for `n = 1` use the subcritical two-dimensional embedding; for `n ≥ 2`
use the critical Sobolev embedding. The induced Riemannian metric supplies the volume and gradient
bridges in the two positive-dimensional cases.
-/

@[expose] public section

open scoped Manifold ContDiff

namespace KahlerForm

/-- Every compact Kähler manifold admits an inhomogeneous Sobolev inequality with exponent
strictly greater than one. -/
theorem exists_sobolevInequality
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [SigmaCompactSpace M]
    [CompactSpace M] (ω₀ : KahlerForm n M) :
    ∃ κ C_S : ℝ, 1 < κ ∧ 0 ≤ C_S ∧ ω₀.SobolevInequality κ C_S := by
  cases BorelSpace.measurable_eq (α := M)
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  by_cases hn0 : n = 0
  · subst n
    obtain ⟨C, hC, hSob⟩ := exists_sobolevInequality_dimension_zero ω₀
    exact ⟨2, C, by norm_num, hC, hSob⟩
  · by_cases hn1 : n = 1
    · subst n
      let g := ω₀.toRiemannianMetric
      have hvol : ω₀.volume = CalabiYau.RiemannianVolume.riemannianVolumeMeasure
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) (M := M) g := by
        simpa [g] using ω₀.volume_eq_riemannianVolumeMeasure
      have hgrad : ∀ f : M → ℝ,
          ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin 1)) 𝓘(ℝ) ∞ f →
          ∀ x, g.inner x
            (CalabiYau.Riemannian.gradFun
              (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g f x)
            (CalabiYau.Riemannian.gradFun
              (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g f x) =
            2 * ω₀.gradNormSq f x := by
        intro f hf x
        exact ω₀.riemannian_gradFun_energy_eq_two_mul_gradNormSq f hf x
      obtain ⟨C, hC, hSob⟩ := sobolev_dimension_two ω₀ g hvol hgrad
      exact ⟨2, C, by norm_num, hC, hSob⟩
    · have hn : 2 ≤ n := by omega
      let g := ω₀.toRiemannianMetric
      have hvol : ω₀.volume = CalabiYau.RiemannianVolume.riemannianVolumeMeasure
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g := by
        simpa [g] using ω₀.volume_eq_riemannianVolumeMeasure
      have hgrad : ∀ f : M → ℝ,
          ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f →
          ∀ x, g.inner x
            (CalabiYau.Riemannian.gradFun
              (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) g f x)
            (CalabiYau.Riemannian.gradFun
              (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) g f x) =
            2 * ω₀.gradNormSq f x := by
        intro f hf x
        exact ω₀.riemannian_gradFun_energy_eq_two_mul_gradNormSq f hf x
      obtain ⟨C, hC, hSob⟩ :=
        sobolevInequality_of_sobolev_two_integral ω₀ g hn hvol hgrad
      have hnR : 2 ≤ (n : ℝ) := by exact_mod_cast hn
      have hden : 0 < (n : ℝ) - 1 := by linarith
      have hkappa : 1 < (n : ℝ) / ((n : ℝ) - 1) := by
        apply (lt_div_iff₀ hden).2
        nlinarith
      exact ⟨(n : ℝ) / ((n : ℝ) - 1), 4 * C ^ 2, hkappa, by positivity, hSob⟩

end KahlerForm
