module

public import CalabiYau.Analysis.Sobolev.Manifold.Rellich.OnManifold
public import CalabiYau.Geometry.Kahler.Laplacian
public import CalabiYau.Geometry.Kahler.Riemannian.Metric
public import CalabiYau.Geometry.Kahler.Riemannian.Volume
public import CalabiYau.Geometry.Kahler.Riemannian.Laplacian
public import CalabiYau.Geometry.Kahler.Sobolev.ZeroGradient.ChartWeakDerivative.ChartLocalL2Convergence
public import CalabiYau.Geometry.Kahler.Sobolev.ZeroGradient.ChartWeakDerivative.ChartLocalEnergy
public import CalabiYau.Geometry.Kahler.Sobolev.ZeroGradient.ChartWeakDerivative.ChartTestClosure
public import CalabiYau.Geometry.Kahler.Sobolev.ZeroGradient.ChartWeakDerivative.ChartLocalMemLp

/-!
# The weak coordinate derivatives of an energy-vanishing limit

This theorem records chartwise vanishing of the distributional coordinate derivatives without
assuming pointwise differentiability of the limit. The proof compares the Kähler volume and energy
with their smooth positive coordinate densities on the compact support of each test function.
-/

@[expose] public section

open scoped Manifold ContDiff
open MeasureTheory Filter Topology

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [SigmaCompactSpace M]

/-- In every real coordinate chart, the pullback of `u` has zero distributional first derivative.
The integral formulation also makes sense in dimension zero, where there are no coordinate
indices. -/
def HasZeroWeakDerivativeInCharts (u : M → ℝ) : Prop :=
  ∀ a : M, ∀ i : Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))),
    ∀ φ : EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Sobolev.Chart.chartTargetEuclid
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) a →
      ∫ y in Sobolev.Chart.chartTargetEuclid
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) a,
        u ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a).symm
            ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y)) *
          (fderiv ℝ φ y (EuclideanSpace.single i 1)) = 0

/-- `L²` convergence and vanishing Kähler gradient energy imply that the limit has zero
 distributional coordinate derivatives in every chart. -/
theorem l2_limit_has_zero_weak_derivative_in_charts
    [CompactSpace M]
    (ω₀ : KahlerForm n M) (f : ℕ → M → ℝ) (u : M → ℝ)
    (hf : ∀ k, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (f k))
    (hu : MemLp u (ENNReal.ofReal 2) ω₀.volume)
    (hL2 : Tendsto
      (fun k => eLpNorm (fun x => f k x - u x) (ENNReal.ofReal 2) ω₀.volume)
      atTop (𝓝 0))
    (hEnergy : Tendsto
      (fun k => ∫ x, ω₀.gradNormSq (f k) x ∂ω₀.volume)
      atTop (𝓝 0)) :
    HasZeroWeakDerivativeInCharts (n := n) (M := M) u := by
  classical
  intro a i φ hφ hφ_support hφchart
  let V := EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))))
  let Ω : Set V := Sobolev.Chart.chartTargetEuclid
    (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) a
  let K : Set V := tsupport φ
  let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a
  let F : ℕ → V → ℝ := fun k y => f k (c.symm ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y))
  let U : V → ℝ := fun y => u (c.symm ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y))
  let μ : Measure V := (MeasureTheory.volume : Measure V).restrict K
  have hKcompact : IsCompact K := by
    simpa [K, HasCompactSupport, tsupport] using hφ_support
  have : IsFiniteMeasure μ := by
    change IsFiniteMeasure ((MeasureTheory.volume : Measure V).restrict K)
    rw [MeasureTheory.isFiniteMeasure_restrict]
    exact hKcompact.measure_lt_top.ne
  have hK : K ⊆ Ω := by simpa [K, Ω] using hφchart
  have hΩ : IsOpen Ω := by
    simpa [Ω] using Sobolev.Chart.chartTargetEuclid_isOpen
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) a
  have hFlim : Tendsto (fun k => eLpNorm (fun y => F k y - U y)
      (ENNReal.ofReal 2) μ) atTop (𝓝 0) := by
    simpa [F, U, μ, c] using chartLocal_l2_tendsto_of_global_l2
      ω₀ f u hf hu hL2 a K hKcompact hK
  have hDlim : Tendsto (fun k => eLpNorm
      (fun y => fderiv ℝ (F k) y (EuclideanSpace.single i 1))
      (ENNReal.ofReal 2) μ) atTop (𝓝 0) := by
    simpa [F, μ, c] using chartLocal_derivative_l2_tendsto_of_grad_energy_tendsto
      ω₀ f hf hEnergy a K hKcompact hK i
  have hUmem : MemLp U (ENNReal.ofReal 2) μ := by
    simpa [U, μ, c] using chartLocal_memLp_of_global_memLp ω₀ u hu a K hKcompact hK
  have hUmeas : AEStronglyMeasurable U μ := hUmem.1
  have hF : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (F k) Ω := by
    intro k
    have hcomp : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
        (f k ∘ c.symm) c.target := by
      exact (hf k).contMDiffOn (s := Set.univ) |>.comp
        (contMDiffOn_extChartAt_symm a) (fun _ _ => Set.mem_univ _)
    have hcomp' : ContDiffOn ℝ (⊤ : ℕ∞) (f k ∘ c.symm) c.target := hcomp.contDiffOn
    change ContDiffOn ℝ (⊤ : ℕ∞)
      ((f k ∘ c.symm) ∘ (toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm) Ω
    apply hcomp'.comp
      ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm.contDiff.contDiffOn)
    intro y hy
    obtain ⟨z, hz, hzy⟩ := hy
    have hz' : z ∈ c.target := by simpa [c] using hz
    have hyz : (toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y = z := by
      rw [← hzy]
      exact (toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm_apply_apply z
    rw [hyz]
    exact hz'
  let dφ : V → ℝ := fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)
  let : (ENNReal.ofReal 2).HolderTriple (ENNReal.ofReal 2) 1 :=
    ENNReal.HolderConjugate.of_toReal <| by
      simpa using (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩ :
        (2 : ℝ).HolderConjugate 2)
  have hDmem : ∀ k, MemLp (fun y => fderiv ℝ (F k) y (EuclideanSpace.single i 1))
      (ENNReal.ofReal 2) μ := by
    intro k
    have hDcontOn : ContinuousOn (fun y => fderiv ℝ (F k) y (EuclideanSpace.single i 1)) Ω := by
      exact ((hF k).continuousOn_fderiv_of_isOpen hΩ (by simp)).clm_apply
        continuous_const.continuousOn
    have hDcont : ContinuousOn (fun y => fderiv ℝ (F k) y (EuclideanSpace.single i 1)) K :=
      hDcontOn.mono hK
    have hDae : AEStronglyMeasurable
        (fun y => fderiv ℝ (F k) y (EuclideanSpace.single i 1)) μ :=
      hDcont.aestronglyMeasurable_of_isCompact hKcompact hKcompact.measurableSet
    have hnormcont : ContinuousOn
        (fun y => ‖fderiv ℝ (F k) y (EuclideanSpace.single i 1)‖) K :=
      continuous_norm.comp_continuousOn hDcont
    obtain ⟨C, hC⟩ := (hKcompact.image_of_continuousOn hnormcont).bddAbove
    have hbound : ∀ᵐ y ∂μ,
        ‖fderiv ℝ (F k) y (EuclideanSpace.single i 1)‖ ≤ C := by
      filter_upwards [ae_restrict_mem hKcompact.measurableSet] with y hy
      exact hC ⟨y, hy, rfl⟩
    exact MemLp.of_bound hDae C hbound
  have hFmem : ∀ k, MemLp (fun y => F k y - U y) (ENNReal.ofReal 2) μ := by
    intro k
    have hFcont : ContinuousOn (F k) Ω := (hF k).continuousOn
    have hFcontK : ContinuousOn (F k) K := hFcont.mono hK
    have hFae : AEStronglyMeasurable (F k) μ :=
      hFcontK.aestronglyMeasurable_of_isCompact hKcompact hKcompact.measurableSet
    have hnormcont : ContinuousOn (fun y => ‖F k y‖) K :=
      continuous_norm.comp_continuousOn hFcontK
    obtain ⟨C, hC⟩ := (hKcompact.image_of_continuousOn hnormcont).bddAbove
    have hbound : ∀ᵐ y ∂μ, ‖F k y‖ ≤ C := by
      filter_upwards [ae_restrict_mem hKcompact.measurableSet] with y hy
      exact hC ⟨y, hy, rfl⟩
    have hFk : MemLp (F k) (ENNReal.ofReal 2) μ := MemLp.of_bound hFae C hbound
    exact hFk.sub hUmem
  have hφmem : MemLp φ (ENNReal.ofReal 2) μ :=
    (hφ.continuous.memLp_of_hasCompactSupport hφ_support).restrict K
  have hdφcont : Continuous dφ := by
    dsimp [dφ]
    exact (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφsupport : HasCompactSupport dφ := by
    dsimp [dφ]
    exact hφ_support.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
  have hdφmem : MemLp dφ (ENNReal.ofReal 2) μ :=
    (hdφcont.memLp_of_hasCompactSupport hdφsupport).restrict K
  have hdφK : tsupport dφ ⊆ K := by
    dsimp [dφ, K]
    exact (tsupport_fderiv_apply_subset ℝ _).trans (Set.Subset.rfl)
  have hdφzero : ∀ y, y ∉ K → dφ y = 0 := by
    intro y hy
    exact image_eq_zero_of_notMem_tsupport (fun hs => hy (hdφK hs))
  have hUφlocal : IntegrableOn (fun y => U y * dφ y) K
      (MeasureTheory.volume : Measure V) := by
    change Integrable (fun y => U y * dφ y) μ
    exact hUmem.integrable_mul hdφmem
  have hUφglobal : Integrable (fun y => U y * dφ y) (MeasureTheory.volume : Measure V) :=
    hUφlocal.integrable_of_forall_notMem_eq_zero (fun y hyK => by simp [hdφzero y hyK])
  have hUtest : IntegrableOn (fun y => U y * fderiv ℝ φ y (EuclideanSpace.single i 1)) Ω := by
    have h := hUφglobal.integrableOn (s := Ω)
    simpa [dφ] using h
  simpa [Ω, U, F, dφ, c] using euclidean_test_integral_eq_zero_of_l2_tendsto
    hΩ hKcompact hK (EuclideanSpace.single i 1) F U φ hφ hφ_support
    (by intro y hy; exact hy) hF hUmeas hUmem hFmem hFlim hDmem hDlim hUtest

end KahlerForm
