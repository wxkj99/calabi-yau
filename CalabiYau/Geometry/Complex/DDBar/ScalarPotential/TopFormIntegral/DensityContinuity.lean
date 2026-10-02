module

public import CalabiYau.Geometry.Complex.DDBar.ScalarPotential.TopFormIntegral.ChartDensity

/-!
# Continuity of a smooth top form's signed Kähler density

A smooth form divided by the nonvanishing positive Kähler top form is a continuous
scalar function. This is continuity of the invariant ratio, not continuity of
coefficients computed in a moving chart centred at each point. The fixed-chart
formula in `ChartDensity` provides the local representatives.

Source: Morita, *Geometry of Differential Forms*, §3.2(a), pp. 104–107,
coordinate realization of oriented top-form integration; Wells, V §1,
pp. 157–159, the positive volume `ωⁿ/n!`.
-/

@[expose] public section

open scoped Manifold ContDiff

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

/-- Smoothness of the actual top form implies continuity of its invariant signed
scalar density. Compactness is not needed until the integration step. -/
theorem continuous_signedTopFormDensity (ω₀ : KahlerForm n M)
    {Θ : FormField (EuclideanSpace ℂ (Fin n)) M (2 * n)}
    (hΘ : Θ.IsSmooth) : Continuous (ω₀.signedTopFormDensity Θ) := by
  rw [continuous_iff_continuousAt]
  intro x
  let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let q : EuclideanSpace ℂ (Fin n) → ℝ := fun z =>
    ContinuousAlternatingMap.topFormCoeff (Θ.chartRep x z) /
      ContinuousAlternatingMap.topFormCoeff (ω₀.topFormVolume.chartRep x z)
  have htop : Continuous
      (fun α : EuclideanSpace ℂ (Fin n) [⋀^Fin (2 * n)]→L[ℝ] ℝ =>
        ContinuousAlternatingMap.topFormCoeff α) := by
    change Continuous (fun α : EuclideanSpace ℂ (Fin n) [⋀^Fin (2 * n)]→L[ℝ] ℝ =>
      α (ContinuousAlternatingMap.complexInterleavedBasis n))
    let b : Fin (2 * n) → EuclideanSpace ℂ (Fin n) :=
      ContinuousAlternatingMap.complexInterleavedBasis n
    exact continuous_eval_const
      (F := EuclideanSpace ℂ (Fin n) [⋀^Fin (2 * n)]→L[ℝ] ℝ)
      (α := Fin (2 * n) → EuclideanSpace ℂ (Fin n)) (X := ℝ) b
  have hnum : ContinuousOn (fun z =>
      ContinuousAlternatingMap.topFormCoeff (Θ.chartRep x z)) c.target :=
    htop.continuousOn.comp (hΘ x).continuousOn (fun _ _ => Set.mem_univ _)
  have hdet : ContinuousOn (fun z => (ω₀.metricInChart x z).det) c.target := by
    classical
    simp_rw [Matrix.det_apply]
    exact continuousOn_finsetSum Finset.univ fun σ _ =>
      continuousOn_const.smul <| continuousOn_finsetProd Finset.univ fun i _ =>
        (ω₀.contDiffOn_metricInChart x (σ i) i).continuousOn
  have hvol : ContinuousOn (ω₀.volumeDensityInChart x) c.target := by
    change ContinuousOn (fun z => 2 ^ n * RCLike.re (ω₀.metricInChart x z).det) c.target
    have hre : ContinuousOn (fun z => RCLike.re (ω₀.metricInChart x z).det) c.target := by
      exact Complex.continuous_re.continuousOn.comp hdet (fun _ _ => Set.mem_univ _)
    exact continuousOn_const.mul hre
  have hden : ContinuousOn (fun z =>
      ContinuousAlternatingMap.topFormCoeff (ω₀.topFormVolume.chartRep x z)) c.target :=
    hvol.congr fun z hz => ω₀.topFormVolume_chartCoeff x hz
  have hpos : ∀ z ∈ c.target,
      0 < ContinuousAlternatingMap.topFormCoeff (ω₀.topFormVolume.chartRep x z) := by
    intro z hz
    rw [ω₀.topFormVolume_chartCoeff x hz, KahlerForm.volumeDensityInChart]
    exact mul_pos (by positivity)
      (RCLike.pos_iff.mp (ω₀.posDef_metricInChart x hz).det_pos).1
  have hq : ContinuousOn q c.target := by
    exact hnum.div hden fun z hz => (hpos z hz).ne'
  have hlocal : ∀ y ∈ c.source,
      ω₀.signedTopFormDensity Θ y = q (c y) := by
    intro y hy
    have hz : c y ∈ c.target := c.map_source hy
    have hratio := ω₀.topFormCoeff_chartRep_eq_density_mul Θ x hz
    have hdenne : ContinuousAlternatingMap.topFormCoeff
        (ω₀.topFormVolume.chartRep x (c y)) ≠ 0 := (hpos (c y) hz).ne'
    change ω₀.signedTopFormDensity Θ y =
      ContinuousAlternatingMap.topFormCoeff (Θ.chartRep x (c y)) /
        ContinuousAlternatingMap.topFormCoeff (ω₀.topFormVolume.chartRep x (c y))
    rw [c.left_inv hy] at hratio
    field_simp [hdenne]
    exact hratio.symm
  have hz : c x ∈ c.target := c.map_source (mem_extChartAt_source x)
  have hqAt : ContinuousAt q (c x) :=
    (hq.continuousWithinAt hz).continuousAt ((isOpen_extChartAt_target x).mem_nhds hz)
  have heq : (fun y => ω₀.signedTopFormDensity Θ y) =ᶠ[nhds x] fun y => q (c y) := by
    filter_upwards [extChartAt_source_mem_nhds (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x] with y hy
    exact hlocal y hy
  exact (hqAt.comp (continuousAt_extChartAt x)).congr_of_eventuallyEq heq

end KahlerForm
