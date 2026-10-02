module

public import CalabiYau.Analysis.Sobolev.Manifold.Rellich.OnManifold
public import CalabiYau.Analysis.Sobolev.Manifold.Rellich.Compactness
public import CalabiYau.Geometry.Kahler.Sobolev
public import CalabiYau.Geometry.Kahler.Laplacian
public import CalabiYau.Geometry.Kahler.Riemannian.Metric
public import CalabiYau.Geometry.Kahler.Riemannian.Volume
public import CalabiYau.Geometry.Kahler.Riemannian.Laplacian
public import CalabiYau.Geometry.Kahler.Sobolev.ZeroGradient.ConnectedConstancy

/-!
# A zero-gradient limit on a connected compact Kähler manifold

If smooth functions converge in `L²` and their integrated Kähler gradient energies tend to zero,
the limit is almost everywhere constant. The limit is only an `L²` function: this statement does
not assert that it has pointwise derivatives. Its proof needs to identify its distributional first
derivative as the weak limit of the derivatives of the smooth sequence, and then use connectedness.

The claim includes complex dimension one. For the flat form `i dz ∧ dż` on a connected flat curve,
the real metric is `2 (dx² + dy²)` and `|∂f|² = (f_x² + f_y²)/4`; vanishing of the limiting
energy therefore forces the limit to be constant, with no additional factor or dimension hypothesis.
-/

@[expose] public section

open scoped Manifold ContDiff
open MeasureTheory Filter Topology

namespace KahlerForm

/-- A limit in `L²` of functions with weak partial derivatives converging to zero has zero
weak partial derivative. This is the Euclidean distributional-derivative closure step used after
localizing the Kähler problem to a chart. -/
private theorem hasWeakPartialDeriv_zero_of_l2_limit
    {d : ℕ} [NeZero d] {Ω : Set (EuclideanSpace ℝ (Fin d))} {i : Fin d}
    {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ}
    {g : ℕ → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : MemLp u (ENNReal.ofReal 2)
      ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin d))).restrict Ω))
    (hf : ∀ k, MemLp (fun x => f k x - u x) (ENNReal.ofReal 2)
      ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin d))).restrict Ω))
    (hft : Tendsto
      (fun k => eLpNorm (fun x => f k x - u x) (ENNReal.ofReal 2)
        ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin d))).restrict Ω))
      atTop (𝓝 0))
    (hweak : ∀ k, Sobolev.Euclidean.HasWeakPartialDeriv i (g k) (f k) Ω)
    (hg : ∀ k, MemLp (g k) (ENNReal.ofReal 2)
      ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin d))).restrict Ω))
    (hgt : Tendsto
      (fun k => eLpNorm (g k) (ENNReal.ofReal 2)
        ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin d))).restrict Ω))
      atTop (𝓝 0)) :
    Sobolev.Euclidean.HasWeakPartialDeriv i (fun _ => 0) u Ω := by
  have hzero : MemLp (fun _ : EuclideanSpace ℝ (Fin d) => (0 : ℝ))
      (ENNReal.ofReal 2)
      ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin d))).restrict Ω) :=
    MemLp.zero
  apply Sobolev.Euclidean.HasWeakPartialDeriv.of_eLpNormApprox_p
      (p := 2) (i := i) (f := u) (g := fun _ => 0)
      (ψ := f) (gψ := g) (by norm_num)
  · exact hu
  · exact hzero
  · exact hweak
  · exact hf
  · exact hft
  · intro k
    simpa using hg k
  · simpa using hgt

/-- A smooth sequence converging in `L²` whose Kähler gradient energies tend to zero has an
a.e.-constant limit on a compact connected Kähler manifold.

The limit `u` is not assumed smooth or pointwise differentiable. The substantive analytic step is
to identify its distributional derivative with the weak limit of the derivatives of `f`; connectedness
then turns the resulting zero weak derivative into almost-everywhere constancy. -/
theorem ae_eq_const_of_l2_tendsto_and_gradNormSq_tendsto
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [SigmaCompactSpace M]
    [CompactSpace M] [ConnectedSpace M]
    (ω₀ : KahlerForm n M) (f : ℕ → M → ℝ) (u : M → ℝ)
    (hf : ∀ k, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (f k))
    (hu : MemLp u (ENNReal.ofReal 2) ω₀.volume)
    (hL2 : Tendsto
      (fun k => eLpNorm (fun x => f k x - u x) (ENNReal.ofReal 2) ω₀.volume)
      atTop (𝓝 0))
    (hEnergy : Tendsto
      (fun k => ∫ x, ω₀.gradNormSq (f k) x ∂ω₀.volume)
      atTop (𝓝 0)) :
    ∃ c : ℝ, u =ᵐ[ω₀.volume] fun _ => c := by
  have hweak := l2_limit_has_zero_weak_derivative_in_charts
    (ω₀ := ω₀) (f := f) (u := u) hf hu hL2 hEnergy
  exact ae_eq_const_of_zero_weak_derivative_in_charts ω₀ u hu hweak

end KahlerForm
