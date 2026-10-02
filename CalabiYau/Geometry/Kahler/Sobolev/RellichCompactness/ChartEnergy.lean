module

public import CalabiYau.Analysis.Sobolev.Manifold.Embedding.Intrinsic
public import CalabiYau.Analysis.Sobolev.Manifold.Rellich.OnManifold
public import CalabiYau.Geometry.Kahler.Sobolev
public import CalabiYau.Geometry.Kahler.Riemannian.Metric
public import CalabiYau.Geometry.Kahler.Riemannian.Volume
public import CalabiYau.Geometry.Kahler.Riemannian.Laplacian

/-!
# Chartwise Sobolev bounds from Kähler energy

The Rellich theorem for charts takes a uniform bound on `wkpNormChart`, whereas the compact Kähler
problem supplies a global integral of the function and its Kähler gradient. The comparison of these
two bounds is the finite-chart localization step: chart cutoffs, volume comparison, and the identity
`|∇f|² = 2 |∂f|²` all enter. The normalization is checked on the flat complex one-dimensional model,
where the real metric associated with `i dz ∧ dż` is `2 (dx² + dy²)`.
-/

@[expose] public section

open scoped Manifold ContDiff ENNReal
open MeasureTheory
open CalabiYau CalabiYau.Riemannian

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [T2Space M] [CompactSpace M] [SigmaCompactSpace M]

-- Use the same canonical Borel measurable space as the extracted Riemannian-volume module.
local instance instMeasurableSpaceChartEnergy : MeasurableSpace M := borel M
local instance instBorelSpaceChartEnergy : BorelSpace M := ⟨rfl⟩

/-- The finite-chart comparison: a global `L²` and Kähler-gradient-energy bound controls the
chartwise `W^{1,2}` norm used by the extracted Rellich theorem.

This statement deliberately accepts the measure and gradient identifications as inputs, isolating
the finite-chart analytic estimate from the Kähler/Riemannian bridge. The global constant need not
be positive; `B = 0` is allowed and is not used to make the conclusion vacuous. -/
private theorem chart_wkpNormChart_bound_of_global_energy
    (ω₀ : KahlerForm n M)
    (g : SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M)
    (hvol : ω₀.volume = RiemannianVolume.riemannianMeasure
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) g
      (RiemannianVolume.chartAtlasPOU (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) M))
    (hgrad : ∀ f : M → ℝ,
      ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f →
      ∀ x, g.inner x (gradFun (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) g f x)
          (gradFun (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) g f x) =
        2 * ω₀.gradNormSq f x)
    (f : ℕ → M → ℝ)
    (hf : ∀ k, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (f k))
    (B : ℝ) (hB : 0 ≤ B)
    (henergy : ∀ k, ∫ x, (f k x ^ 2 + ω₀.gradNormSq (f k) x) ∂ω₀.volume ≤ B) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ k, Sobolev.Chart.wkpNormChart
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) 1 (ENNReal.ofReal 2) (f k) ≤
        ENNReal.ofReal R := by
  let I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
  let μ : Measure M := RiemannianVolume.riemannianVolumeMeasure (I := I) (M := M) g
  have : IsFiniteMeasureOnCompacts μ :=
    RiemannianVolume.riemannianVolumeMeasure_isFiniteMeasureOnCompacts
      (I := I) (M := M) g
  have hμ : ω₀.volume = μ := by
    simpa [μ, RiemannianVolume.riemannianVolumeMeasure_def] using hvol
  have hCchart :=
    Sobolev.EquivalenceReverse.wkpNormChart_le_const_mul_intrinsicLpComponents_smooth_uniform
      (I := I) (M := M) g (p := ENNReal.ofReal 2) (by norm_num) ENNReal.ofReal_ne_top
  obtain ⟨C, hC, hCchart⟩ := hCchart
  let D : ℝ := Real.sqrt (2 * B)
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  have hDsq : D ^ 2 = 2 * B := by
    dsimp [D]
    rw [Real.sq_sqrt]
    positivity
  have hB_le : B ≤ 2 * B := by linarith
  refine ⟨C * (2 * D), mul_nonneg hC (mul_nonneg (by norm_num) hD), ?_⟩
  intro k
  let q : M → ℝ := fun x => g.inner x
    (gradFun (I := I) g (f k) x) (gradFun (I := I) g (f k) x)
  let v : M → ℝ := fun x => Real.sqrt (q x)
  have hinner := TangentBundle.continuous_g_inner_of_smooth_sections
    (I := I) (M := M) g
    (gradG (I := I) g ⟨f k, hf k⟩) (gradG (I := I) g ⟨f k, hf k⟩)
  have hqcont : Continuous q := by
    exact hinner.congr (fun _ => rfl)
  have hvcont : Continuous v := by
    exact Real.continuous_sqrt.comp hqcont
  have hqnonneg : ∀ x, 0 ≤ q x := by
    intro x
    exact CalabiYau.metric_inner_self_nonneg (I := I) (M := M) g x _
  have hvint : Integrable v μ :=
    CalabiYau.L2.integrable_of_continuous_compactSpace g hvcont
  have hf2cont : Continuous (fun x => (f k x) ^ 2) := (hf k).continuous.pow 2
  have hf2int : Integrable (fun x => (f k x) ^ 2) μ :=
    CalabiYau.L2.integrable_of_continuous_compactSpace g hf2cont
  have hqint : Integrable q μ :=
    CalabiYau.L2.integrable_of_continuous_compactSpace g hqcont
  have hgradCont : Continuous (fun x => ω₀.gradNormSq (f k) x) := by
    have hpoint : (fun x => ω₀.gradNormSq (f k) x) = fun x => q x / 2 := by
      funext x
      dsimp [q]
      have h := hgrad (f k) (hf k) x
      calc
        ω₀.gradNormSq (f k) x = (2 * ω₀.gradNormSq (f k) x) / 2 := by ring
        _ = g.inner x (gradFun (I := I) g (f k) x) (gradFun (I := I) g (f k) x) / 2 := by rw [← h]
    rw [hpoint]
    exact hqcont.div_const 2
  have hgradInt : Integrable (fun x => ω₀.gradNormSq (f k) x) μ := by
    exact (CalabiYau.L2.integrable_of_continuous_compactSpace g hgradCont)
  have hsumInt : Integrable (fun x => (f k x) ^ 2 + ω₀.gradNormSq (f k) x) μ :=
    hf2int.add hgradInt
  have hsumBound : ∫ x, ((f k x) ^ 2 + ω₀.gradNormSq (f k) x) ∂μ ≤ B := by
    rw [← hμ]
    exact henergy k
  have hfunBound : ∫ x, (f k x) ^ 2 ∂μ ≤ B := by
    calc
      ∫ x, (f k x) ^ 2 ∂μ ≤
          ∫ x, ((f k x) ^ 2 + ω₀.gradNormSq (f k) x) ∂μ := by
        apply integral_mono_ae hf2int hsumInt
        filter_upwards with x
        exact le_add_of_nonneg_right (ω₀.gradNormSq_nonneg (f k) x)
      _ ≤ B := hsumBound
  have hgradBound : ∫ x, ω₀.gradNormSq (f k) x ∂μ ≤ B := by
    calc
      ∫ x, ω₀.gradNormSq (f k) x ∂μ ≤
          ∫ x, ((f k x) ^ 2 + ω₀.gradNormSq (f k) x) ∂μ := by
        apply integral_mono_ae hgradInt hsumInt
        filter_upwards with x
        exact le_add_of_nonneg_left (sq_nonneg (f k x))
      _ ≤ B := hsumBound
  have hqBound : ∫ x, q x ∂μ ≤ 2 * B := by
    calc
      ∫ x, q x ∂μ = 2 * ∫ x, ω₀.gradNormSq (f k) x ∂μ := by
        rw [show q = fun x => 2 * ω₀.gradNormSq (f k) x from by
          funext x
          dsimp [q]
          exact hgrad (f k) (hf k) x]
        rw [integral_const_mul]
      _ ≤ 2 * B := by nlinarith [hgradBound]
  have hvSq : ∫ x, v x ^ 2 ∂μ = ∫ x, q x ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    dsimp [v]
    rw [Real.sq_sqrt (hqnonneg x)]
  have hvLp : MemLp v (ENNReal.ofReal 2) μ := by
    exact hvcont.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace v)
  have hfLp : MemLp (f k) (ENNReal.ofReal 2) μ := by
    exact (hf k).continuous.memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace (f k))
  have hvLpSq : lpNorm v 2 μ ^ 2 ≤ 2 * B := by
    rw [CalabiYau.L2.lpNorm_two_sq_eq_integral_sq hvcont.aestronglyMeasurable, hvSq]
    exact hqBound
  have hfLpSq : lpNorm (f k) 2 μ ^ 2 ≤ 2 * B := by
    have hle : ∫ x, (f k x) ^ 2 ∂μ ≤ 2 * B := le_trans hfunBound hB_le
    rw [CalabiYau.L2.lpNorm_two_sq_eq_integral_sq (hf k).continuous.aestronglyMeasurable]
    exact hle
  have hvLpBound : lpNorm v 2 μ ≤ D := by
    have hnonneg : 0 ≤ lpNorm v 2 μ := lpNorm_nonneg
    nlinarith [hvLpSq, hDsq]
  have hfLpBound : lpNorm (f k) 2 μ ≤ D := by
    have hnonneg : 0 ≤ lpNorm (f k) 2 μ := lpNorm_nonneg
    nlinarith [hfLpSq, hDsq]
  have hvENNBound : eLpNorm v (ENNReal.ofReal 2) μ ≤ ENNReal.ofReal D := by
    rw [← MeasureTheory.ofReal_lpNorm hvLp]
    simpa only [ENNReal.ofReal_ofNat] using (ENNReal.ofReal_le_ofReal hvLpBound)
  have hfENNBound : eLpNorm (f k) (ENNReal.ofReal 2) μ ≤ ENNReal.ofReal D := by
    rw [← MeasureTheory.ofReal_lpNorm hfLp]
    simpa only [ENNReal.ofReal_ofNat] using (ENNReal.ofReal_le_ofReal hfLpBound)
  have hsumENN : eLpNorm (f k) (ENNReal.ofReal 2) μ + eLpNorm v (ENNReal.ofReal 2) μ ≤
      ENNReal.ofReal (2 * D) := by
    calc
      _ ≤ ENNReal.ofReal D + ENNReal.ofReal D := add_le_add hfENNBound hvENNBound
      _ = ENNReal.ofReal (D + D) := by
        rw [← ENNReal.ofReal_add hD hD]
      _ = ENNReal.ofReal (2 * D) := by congr 1; ring
  calc
    Sobolev.Chart.wkpNormChart (I := I) (M := M) 1 (ENNReal.ofReal 2) (f k) ≤
        ENNReal.ofReal C *
          (eLpNorm (f k) (ENNReal.ofReal 2) μ + eLpNorm v (ENNReal.ofReal 2) μ) :=
      hCchart (hf k)
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal (2 * D) :=
      mul_le_mul_of_nonneg_left hsumENN (by positivity)
    _ = ENNReal.ofReal (C * (2 * D)) := (ENNReal.ofReal_mul hC).symm

/-- A smooth sequence with uniformly bounded global Kähler energy is measurable, belongs to the
chartwise `W^{1,2}` class, and has uniformly bounded chartwise `W^{1,2}` norm.

The measurable-space parameters are kept explicit. In its proof, normalize the `BorelSpace`
identification before applying the volume comparison: `KahlerForm.volume` is indexed by the ambient
measurable-space instance while the extracted Riemannian measure is defined using the canonical
Borel instance. -/
theorem smooth_seq_energy_bound_to_chart_wkp
    (ω₀ : KahlerForm n M)
    (g : SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M)
    (hvol : ω₀.volume = RiemannianVolume.riemannianMeasure
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) g
      (RiemannianVolume.chartAtlasPOU (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) M))
    (hgrad : ∀ f : M → ℝ,
      ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f →
      ∀ x, g.inner x (gradFun (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) g f x)
          (gradFun (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) g f x) =
        2 * ω₀.gradNormSq f x)
    (f : ℕ → M → ℝ)
    (hf : ∀ k, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (f k))
    (B : ℝ) (hB : 0 ≤ B)
    (henergy : ∀ k, ∫ x, (f k x ^ 2 + ω₀.gradNormSq (f k) x) ∂ω₀.volume ≤ B) :
    (∀ k, Measurable (f k)) ∧
      (∀ k, Sobolev.Chart.MemWkpChart
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) 1 (ENNReal.ofReal 2) (f k)) ∧
      ∃ R : ℝ, 0 ≤ R ∧ ∀ k, Sobolev.Chart.wkpNormChart
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) 1 (ENNReal.ofReal 2) (f k) ≤
          ENNReal.ofReal R := by
  have hmeas : ∀ k, Measurable (f k) := fun k => (hf k).continuous.measurable
  have hp : (1 : ℝ≥0∞) ≤ ENNReal.ofReal 2 := by norm_num
  have hmem : ∀ k, Sobolev.Chart.MemWkpChart
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) 1 (ENNReal.ofReal 2) (f k) := by
    intro k
    exact Sobolev.Equivalence.MemWkpChart_of_contMDiff
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) hp (hf k)
  exact ⟨hmeas, hmem,
    chart_wkpNormChart_bound_of_global_energy ω₀ g hvol hgrad f hf B hB henergy⟩

end KahlerForm
