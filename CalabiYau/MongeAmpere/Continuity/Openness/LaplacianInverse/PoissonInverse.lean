module

public import CalabiYau.MongeAmpere.Continuity.Openness.LaplacianInverse.GlobalSchauder
public import CalabiYau.Geometry.Kahler.Poisson

/-!
# Bounded smooth mean-zero Poisson inverse

The input Poisson hypothesis gives a smooth solution for each smooth mean-zero right-hand side.
Subtracting its average fixes the constant ambiguity. The global mean-zero Schauder bound then
bounds that normalized solution in the order-two finite-chart gauge by the order-zero gauge of the
data, producing a bounded inverse on the smooth cores.

Uniqueness is with the mean-zero normalization. No claim of surjectivity on the full Hölder
completion is made here; extending the core inverse is a separate step in `Completion`.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology
open Set MeasureTheory

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- The unique smooth mean-zero inverse and its uniform finite-chart gauge bound. -/
def HasBoundedSmoothMeanZeroPoissonInverse (ω₁ : KahlerForm n M)
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M) (α : ℝ≥0) : Prop :=
  ∃ C : ℝ≥0, ∀ f : M → ℝ,
    ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f →
    (∫ x, f x ∂ω₁.volume = 0) →
    ∃! u : M → ℝ,
      ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u ∧
      (∫ x, u x ∂ω₁.volume = 0) ∧
      ω₁.laplacian u = f ∧
      finiteChartHolderGauge cover 2 α u < ⊤ ∧
      finiteChartHolderGauge cover 0 α f < ⊤ ∧
      (finiteChartHolderGauge cover 2 α u).toReal ≤
        (C : ℝ) * (finiteChartHolderGauge cover 0 α f).toReal

/-- The smooth mean-zero Poisson solver is unique and obeys one uniform inverse bound in the
finite-chart gauges. The proof combines the smooth solver with the global estimate; merely knowing
smooth solvability would not imply boundedness. -/
@[deprecated "unused hypotheses `hα₀`, `hα₁`, and `hSch`; will be removed" (since := "2026-10-02")]
theorem exists_bounded_smooth_meanZero_poisson_inverse [Nonempty M]
    (ω₁ : KahlerForm n M) (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (α : ℝ≥0) (hα₀ : 0 < α) (hα₁ : α < 1)
    (hSch : InteriorSchauderEstimate n)
    (hPoisson : ω₁.PoissonSolvable)
    (hGlobal : HasGlobalMeanZeroLaplacianBound ω₁ cover α) :
    HasBoundedSmoothMeanZeroPoissonInverse ω₁ cover α := by
  classical
  have := hα₀
  have := hα₁
  have := hSch
  obtain ⟨C, hGlobal⟩ := hGlobal
  have hvol : 0 < ω₁.volume.real Set.univ := by
    have hint : Integrable (fun x : M ↦ Real.exp ((0 : ℝ) : ℝ)) ω₁.volume := by
      simpa using (integrable_const (1 : ℝ) : Integrable (fun _ : M ↦ (1 : ℝ)) ω₁.volume)
    simpa using integral_exp_pos (μ := ω₁.volume) (f := fun _ : M ↦ (0 : ℝ)) hint
  refine ⟨C, ?_⟩
  intro f hf hfm
  obtain ⟨u₀, hu₀, hlap₀⟩ := hPoisson f hf hfm
  have hu₀int : Integrable u₀ ω₁.volume :=
    hu₀.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace u₀)
  let c : ℝ := (∫ x, u₀ x ∂ω₁.volume) / ω₁.volume.real Set.univ
  let u : M → ℝ := fun x ↦ u₀ x - c
  have hu : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u := by
    dsimp [u]
    exact hu₀.sub contMDiff_const
  have hum : ∫ x, u x ∂ω₁.volume = 0 := by
    rw [show u = fun x ↦ u₀ x - c from rfl, integral_sub hu₀int (integrable_const c)]
    rw [integral_const]
    dsimp [c]
    field_simp [ne_of_gt hvol]
    ring
  have hulap : ω₁.laplacian u = f := by
    rw [show u = fun x ↦ u₀ x - c from rfl,
      show (fun x ↦ u₀ x - c) = fun x ↦ u₀ x + (-c) from by funext x; ring,
      ω₁.laplacian_add_const (-c)]
    exact hlap₀
  let uCore : SmoothChartHolderCore cover 2 α := ⟨⟨u, hu⟩⟩
  obtain ⟨huGauge, g, hg, hgm, hgGauge, hbound⟩ := hGlobal uCore hum
  have hgf : g.smoothMap = f := by
    calc
      g.smoothMap = ω₁.laplacian u := by simpa [uCore] using hg
      _ = f := hulap
  have hfGauge : finiteChartHolderGauge cover 0 α f < ⊤ := by
    rw [← hgf]
    exact hgGauge
  have huBound : (finiteChartHolderGauge cover 2 α u).toReal ≤
      (C : ℝ) * (finiteChartHolderGauge cover 0 α f).toReal := by
    simpa [uCore, hgf] using hbound
  refine ⟨u, ⟨hu, hum, hulap, ?_, hfGauge, huBound⟩, ?_⟩
  · simpa [uCore] using huGauge
  · intro v hv
    have hlapEq : ω₁.laplacian v = ω₁.laplacian u := by
      rw [hv.2.2.1, hulap]
    obtain ⟨d, hd⟩ := ω₁.eq_add_const_of_laplacian_eq hu hv.1 hlapEq.symm
    have uint : Integrable u ω₁.volume := by
      rw [show u = fun x ↦ u₀ x - c from rfl]
      exact hu₀int.sub (integrable_const c)
    have hintEq : ∫ x, v x ∂ω₁.volume = ∫ x, u x ∂ω₁.volume +
        ∫ _ : M, d ∂ω₁.volume := by
      calc
        ∫ x, v x ∂ω₁.volume = ∫ x, u x + d ∂ω₁.volume := by
          apply integral_congr_ae
          filter_upwards [] with x
          exact hd x
        _ = _ := integral_add uint (integrable_const d)
    have hdzero : d = 0 := by
      have hmul : d * ω₁.volume.real Set.univ = 0 := by
        simpa [hv.2.1, hum, integral_const, smul_eq_mul, mul_comm] using hintEq
      exact (mul_eq_zero.mp hmul).resolve_right (ne_of_gt hvol)
    funext x
    rw [hd x, hdzero, add_zero]

end KahlerForm
