module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.BochnerIdentity.OrderedJets

/-!
# Localization of the global Calabi-energy Laplacian

Székelyhidi, §3.3, proof of Lemma 3.9, printed pp. 44–45, (3.14).
The inverse entry is [q,p]; curvature begins with -partialZ_p(partialBar_q g).
The pairing is linear on the left and conjugate-linear on the right.
This computation uses only the stated
No off-target smoothness is assumed.
-/

@[expose] public section

open scoped Manifold ContDiff BigOperators ComplexOrder

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

omit [T2Space M] [CompactSpace M] in
private theorem calabiEnergy_eq_c3Pair_at_centre (ω₀ : KahlerForm n M) (φ : M → ℝ) (x : M) :
    calabiEnergy ω₀ φ x =
      (c3Pair (c3PerturbedMetricInChart ω₀ φ x)
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x)
        (c3ConnectionDifferenceInChart ω₀ φ x
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x))
        (c3ConnectionDifferenceInChart ω₀ φ x
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x))).re := by
  simp [calabiEnergy, calabiEnergyInChart, c3Pair, c3PerturbedMetricInChart]

omit [T2Space M] [CompactSpace M] in
private theorem calabiEnergyInChart_eq_c3Pair (ω₀ : KahlerForm n M)
    (φ : M → ℝ) (x : M) (w : EuclideanSpace ℂ (Fin n)) :
    calabiEnergyInChart ω₀ φ x w =
      (c3Pair (c3PerturbedMetricInChart ω₀ φ x) w
        (c3ConnectionDifferenceInChart ω₀ φ x w)
        (c3ConnectionDifferenceInChart ω₀ φ x w)).re := by
  simp [calabiEnergyInChart, c3Pair, c3PerturbedMetricInChart]

open Filter Topology in
private theorem complexHessian_eq_of_eventuallyEq {n : ℕ}
    (f g : EuclideanSpace ℂ (Fin n) → ℝ)
    (z : EuclideanSpace ℂ (Fin n)) (i j : Fin n)
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z)
    (heq : Filter.EventuallyEq (𝓝 z) f g) :
    complexHessian f z i j = complexHessian g z i j := by
  obtain ⟨U, hUeq, hUopen, hzU⟩ := mem_nhds_iff.mp heq
  have hDerEq : Filter.EventuallyEq (𝓝 z) (fderiv ℝ f) (fderiv ℝ g) := by
    filter_upwards [hUopen.mem_nhds hzU] with w hw
    have hEqW : Filter.EventuallyEq (𝓝 w) f g := by
      filter_upwards [hUopen.mem_nhds hw] with y hy
      exact hUeq hy
    exact hEqW.fderiv_eq
  have hSecond : fderiv ℝ (fderiv ℝ f) z = fderiv ℝ (fderiv ℝ g) z :=
    hDerEq.fderiv_eq
  rw [complexHessian_apply hf i j, complexHessian_apply hg i j, hSecond]

theorem calabiEnergy_laplacian_eq_chart_pair_hessian (ω₀ : KahlerForm n M)
    {φ : M → ℝ} (hφ : ω₀.IsPotential φ) (x : M) :
    (ω₀.perturb φ hφ).laplacian (calabiEnergy ω₀ φ) x =
      c3ChartPairHessianLaplacian ω₀ φ x := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let z := e x
  let g := c3PerturbedMetricInChart ω₀ φ x
  let T := c3ConnectionDifferenceInChart ω₀ φ x
  let f : EuclideanSpace ℂ (Fin n) → ℝ := (calabiEnergy ω₀ φ) ∘ e.symm
  let q : EuclideanSpace ℂ (Fin n) → ℝ := fun w => (c3Pair g w (T w) (T w)).re
  have hz : z ∈ e.target := e.map_source (mem_extChartAt_source x)
  have hOpen : IsOpen e.target := isOpen_extChartAt_target x
  open Filter Topology in
  have hEq : Filter.EventuallyEq (𝓝 z) f q := by
    filter_upwards [hOpen.mem_nhds hz] with w hw
    dsimp [f, q, g, T]
    rw [calabiEnergy_chartFormula ω₀ hφ x w hw]
    exact calabiEnergyInChart_eq_c3Pair ω₀ φ x w
  have hsymm : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ e.symm z :=
    (contMDiffOn_extChartAt_symm x).contMDiffAt (hOpen.mem_nhds hz)
  have hGlobal : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
      (calabiEnergy ω₀ φ) x := (calabiEnergy_contMDiff ω₀ hφ).contMDiffAt
  have hPull : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f z := by
    dsimp [f]
    exact hGlobal.comp_of_eq hsymm (e.left_inv (mem_extChartAt_source x))
  have hf : ContDiffAt ℝ 2 f z :=
    ((contMDiffAt_iff_contDiffAt.mp hPull).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))
  have hq : ContDiffAt ℝ 2 q z := hf.congr_of_eventuallyEq hEq.symm
  have hHess : complexHessian f z = complexHessian q z := by
    ext i j
    exact complexHessian_eq_of_eventuallyEq f q z i j hf hq hEq
  have hMetric : (ω₀.perturb φ hφ).metricInChart x z = g z := by
    rw [ω₀.metricInChart_perturb hφ x hz]
    rfl
  have hLap := (ω₀.perturb φ hφ).laplacian_eq_inChart
    (calabiEnergy_contMDiff ω₀ hφ) x (y := x) (by simp)
  calc
    (ω₀.perturb φ hφ).laplacian (calabiEnergy ω₀ φ) x =
        RCLike.re (((ω₀.perturb φ hφ).metricInChart x z)⁻¹ *
          complexHessian f z).trace := by
            simpa [f, e, z] using hLap
    _ = RCLike.re ((g z)⁻¹ * complexHessian q z).trace := by rw [hMetric, hHess]
    _ = c3ChartPairHessianLaplacian ω₀ φ x := by
      simp [c3ChartPairHessianLaplacian, e, g, T, z, q]

end KahlerForm
