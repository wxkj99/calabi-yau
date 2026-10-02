module

import CalabiYau.Geometry.Kahler.Sobolev.ZeroGradient.ChartWeakDerivative.ChartPullbackL2Comparison
public import CalabiYau.Analysis.Sobolev.Manifold.Rellich.OnManifold
public import CalabiYau.Geometry.Kahler.Volume

/-!
# Local chart convergence from global Kähler `L²` convergence

A smooth positive Kähler volume density is bounded below on a compact subset of a chart.
Consequently, global convergence in the Kähler `L²` norm controls Euclidean `L²` convergence of
chart pullbacks on every compact subset of the chart target. The compact subset hypothesis is
essential: an entire chart target need not be bounded or have finite Euclidean volume.
-/

@[expose] public section

open scoped Manifold ContDiff
open MeasureTheory Filter Topology

namespace KahlerForm

private lemma chartDensity_lower_bound_on_compact
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [SigmaCompactSpace M]
    (ω₀ : KahlerForm n M) (a : M)
    (K : Set (EuclideanSpace ℝ
      (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))))))
    (hKcompact : IsCompact K)
    (hK : K ⊆ Sobolev.Chart.chartTargetEuclid
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) a) :
    ∃ c : ℝ, 0 < c ∧ ∀ y ∈ K,
      c ≤ ω₀.volumeDensityInChart a
        ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y) := by
  classical
  let c₀ := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a
  let g : EuclideanSpace ℝ
      (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))) → ℝ :=
    fun y ↦ ω₀.volumeDensityInChart a
      ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y)
  have hdet : ContinuousOn (fun z ↦ (ω₀.metricInChart a z).det) c₀.target := by
    simp_rw [Matrix.det_apply]
    exact continuousOn_finsetSum Finset.univ fun σ _ ↦
      continuousOn_const.smul <| continuousOn_finsetProd Finset.univ fun i _ ↦
        (ω₀.contDiffOn_metricInChart a (σ i) i).continuousOn
  have hden : ContinuousOn (ω₀.volumeDensityInChart a) c₀.target := by
    change ContinuousOn (fun z ↦ (2 : ℝ) ^ n *
      (ω₀.metricInChart a z).det.re) c₀.target
    have hre : ContinuousOn (fun z ↦ (ω₀.metricInChart a z).det.re) c₀.target :=
      Complex.continuous_re.continuousOn.comp hdet (fun _ _ ↦ Set.mem_univ _)
    exact continuousOn_const.mul hre
  have hKtarget : K ⊆ (toEuclidean (E := EuclideanSpace ℂ (Fin n))) '' c₀.target := by
    simpa [Sobolev.Chart.chartTargetEuclid, c₀] using hK
  have hcont : ContinuousOn g K := by
    apply hden.comp (toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm.continuous.continuousOn
    intro y hy
    obtain ⟨z, hz, hzy⟩ := hKtarget hy
    have hsymm : (toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y = z := by
      rw [← hzy]
      exact (toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm_apply_apply z
    simpa [g, hsymm] using hz
  by_cases hne : K.Nonempty
  · obtain ⟨y₀, hy₀, hmin⟩ := hKcompact.exists_isMinOn hne hcont
    have hpos : 0 < g y₀ := by
      apply ω₀.volumeDensityInChart_pos a
      obtain ⟨z, hz, hzy⟩ := hKtarget hy₀
      have : (toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y₀ = z := by
        rw [← hzy]
        exact (toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm_apply_apply z
      have hz' : z ∈ c₀.target := by simpa [c₀] using hz
      rw [this]
      exact hz'
    refine ⟨g y₀ / 2, by linarith, ?_⟩
    intro y hy
    have hle : g y₀ ≤ g y := hmin hy
    dsimp [g] at hpos ⊢
    linarith
  · refine ⟨1, by norm_num, ?_⟩
    intro y hy
    exact (hne ⟨y, hy⟩).elim

private lemma restrict_le_inv_density_smul
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (K : Set X)
    (d : X → ENNReal) (c : ENNReal)
    (hK : MeasurableSet K) (hc₀ : c ≠ 0) (hcTop : c ≠ ⊤)
    (hd : ∀ y ∈ K, c ≤ d y) :
    μ.restrict K ≤ c⁻¹ • (μ.withDensity d).restrict K := by
  rw [Measure.le_iff]
  intro A hA
  have hAK : MeasurableSet (A ∩ K) := hA.inter hK
  have hlin :
      ∫⁻ y in A ∩ K, (1 : ENNReal) ∂μ ≤
        ∫⁻ y in A ∩ K, c⁻¹ * (d y * 1) ∂μ := by
    apply MeasureTheory.setLIntegral_mono' hAK
    intro y hy
    have hmul : 1 ≤ c⁻¹ * d y := by
      calc
        1 = c⁻¹ * c := by rw [ENNReal.inv_mul_cancel hc₀ hcTop]
        _ ≤ c⁻¹ * d y := by
          gcongr
          exact hd y hy.2
    calc
      1 = 1 * 1 := by simp
      _ ≤ (c⁻¹ * d y) * 1 := by gcongr
      _ = c⁻¹ * (d y * 1) := by ac_rfl
  have hlin' : μ (A ∩ K) ≤ c⁻¹ * ∫⁻ y in A ∩ K, d y ∂μ := by
    calc
      μ (A ∩ K) = ∫⁻ y in A ∩ K, (1 : ENNReal) ∂μ := by
        rw [MeasureTheory.setLIntegral_one]
      _ ≤ ∫⁻ y in A ∩ K, c⁻¹ * (d y * 1) ∂μ := hlin
      _ = c⁻¹ * ∫⁻ y in A ∩ K, d y ∂μ := by
        simp only [mul_one]
        have hind : (A ∩ K).indicator (fun y => c⁻¹ * d y) =
            fun y => c⁻¹ * (A ∩ K).indicator d y := by
          funext y
          by_cases hy : y ∈ A ∩ K <;> simp [hy]
        rw [← MeasureTheory.lintegral_indicator hAK, hind,
          MeasureTheory.lintegral_const_mul' c⁻¹ _ (ENNReal.inv_ne_top.mpr hc₀),
          MeasureTheory.lintegral_indicator hAK]
  calc
    μ.restrict K A = μ (A ∩ K) := by rw [Measure.restrict_apply hA]
    _ ≤ c⁻¹ * ∫⁻ y in A ∩ K, d y ∂μ := hlin'
    _ = c⁻¹ * (μ.withDensity d).restrict K A := by
      rw [Measure.restrict_apply hA, withDensity_apply _ hAK]
    _ = (c⁻¹ • (μ.withDensity d).restrict K) A := by
      rw [Measure.smul_apply, smul_eq_mul]

private lemma eLpNorm_restrict_le_of_density_lower
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (K : Set X)
    (d : X → ENNReal) (c : ENNReal) (f : X → ℝ)
    (hK : MeasurableSet K) (hc₀ : c ≠ 0) (hcTop : c ≠ ⊤)
    (hd : ∀ y ∈ K, c ≤ d y) :
    eLpNorm f (ENNReal.ofReal 2) (μ.restrict K) ≤
      (c⁻¹) ^ (1 / ENNReal.ofReal 2).toReal *
        eLpNorm f (ENNReal.ofReal 2) ((μ.withDensity d).restrict K) := by
  let ν := (μ.withDensity d).restrict K
  have hmeasure : μ.restrict K ≤ c⁻¹ • ν :=
    restrict_le_inv_density_smul μ K d c hK hc₀ hcTop hd
  calc
    eLpNorm f (ENNReal.ofReal 2) (μ.restrict K) ≤
        eLpNorm f (ENNReal.ofReal 2) (c⁻¹ • ν) :=
      eLpNorm_mono_measure f hmeasure
    _ ≤ (c⁻¹) ^ (1 / ENNReal.ofReal 2).toReal •
          eLpNorm f (ENNReal.ofReal 2) ν :=
      eLpNorm_smul_measure_le c⁻¹ f (ENNReal.ofReal 2) ν
    _ = _ := by simp [ν]

/-- Global `L²` convergence with respect to Kähler volume implies Euclidean `L²` convergence of
chart pullbacks on every compact subset of the chart target. The comparison is local: the strictly
positive smooth chart density has a positive lower bound on the compact set. -/
theorem chartLocal_l2_tendsto_of_global_l2
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M]
    [CompactSpace M] [SigmaCompactSpace M]
    (ω₀ : KahlerForm n M) (f : ℕ → M → ℝ) (u : M → ℝ)
    (hf : ∀ k, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (f k))
    (hu : MemLp u (ENNReal.ofReal 2) ω₀.volume)
    (hL2 : Tendsto
      (fun k => eLpNorm (fun x => f k x - u x) (ENNReal.ofReal 2) ω₀.volume)
      atTop (𝓝 0))
    (a : M)
    (K : Set (EuclideanSpace ℝ
      (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))))))
    (hKcompact : IsCompact K)
    (hK : K ⊆ Sobolev.Chart.chartTargetEuclid
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) a) :
    Tendsto
      (fun k => eLpNorm
        (fun y => (f k - u) ((extChartAt
          𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a).symm
          ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y)))
        (ENNReal.ofReal 2)
        ((MeasureTheory.volume : Measure (EuclideanSpace ℝ
          (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))))).restrict K))
      atTop (𝓝 0) := by
  classical
  obtain ⟨c, hc, hden⟩ := chartDensity_lower_bound_on_compact ω₀ a K hKcompact hK
  obtain ⟨C, hC, hbound⟩ :=
    chartPullback_eLpNorm_le_of_compact_density_lower ω₀ a K hKcompact hK c hc hden
  have hlocalBound (k : ℕ) :
      eLpNorm
          (fun y => (f k - u) ((extChartAt
            𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a).symm
            ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y)))
          (ENNReal.ofReal 2)
          ((MeasureTheory.volume : Measure (EuclideanSpace ℝ
            (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))))).restrict K) ≤
        ENNReal.ofReal C * eLpNorm (fun x => f k x - u x)
          (ENNReal.ofReal 2) ω₀.volume := by
    have hmem : MemLp (fun x => f k x - u x) (ENNReal.ofReal 2) ω₀.volume := by
      exact ((hf k).continuous.memLp_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace (f k))).sub hu
    have hfun : (f k - u) = (fun x => f k x - u x) := by
      funext x
      rfl
    simpa only [hfun] using hbound (f k - u) hmem
  have hupper : Tendsto
      (fun k => ENNReal.ofReal C * eLpNorm (fun x => f k x - u x)
        (ENNReal.ofReal 2) ω₀.volume)
      atTop (𝓝 0) := by
    have hCtop : ENNReal.ofReal C ≠ ⊤ := ENNReal.ofReal_ne_top
    have h := ENNReal.Tendsto.const_mul hL2 (Or.inr hCtop)
    simpa using h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun _ => bot_le)
    hlocalBound

end KahlerForm
