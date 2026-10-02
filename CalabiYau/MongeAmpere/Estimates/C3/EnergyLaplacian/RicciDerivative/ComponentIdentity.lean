module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.Basic
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.Components
import CalabiYau.MongeAmpere.Operator

/-!
# Componentwise Ricci identity for a general Monge–Ampère solution

Székelyhidi, §1.4, Lemma 1.22 and the following Ricci difference formula,
printed pp. 12–13. The full form identity already exists in Ricci.lean;
Components supplies its curvature-coefficient bridge. This assembly has no
placeholder, and never infers a tensor identity from its background trace.
-/

public section

open scoped Manifold ContDiff Topology
open Filter

namespace KahlerForm

private theorem ricci_germ_congr {n : ℕ}
    {g g' : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
    {z : EuclideanSpace ℂ (Fin n)} (hg : g =ᶠ[nhds z] g') (j l : Fin n) :
    c3RicciInChart g z j l = c3RicciInChart g' z j l := by
  have he (a b : Fin n) : (fun w ↦ g w a b) =ᶠ[nhds z] (fun w ↦ g' w a b) := by
    filter_upwards [hg] with w hw
    rw [hw]
  have hd (a b : Fin n) := (he a b).fderiv_eq (𝕜 := ℝ)
  have hb (a b q : Fin n) :
      (fun w ↦ chartPartialBarComplex (fun v ↦ g v a b) w q) =ᶠ[nhds z]
        (fun w ↦ chartPartialBarComplex (fun v ↦ g' v a b) w q) := by
    filter_upwards [(he a b).fderiv (𝕜 := ℝ)] with w hw
    simp only [chartPartialBarComplex, hw]
  have hbd (a b q : Fin n) := (hb a b q).fderiv_eq (𝕜 := ℝ)
  have hc (p q a b : Fin n) : chartCurvature g z p q a b =
      chartCurvature g' z p q a b := by
    unfold chartCurvature chartPartialZComplex
    rw [hbd a b q]
    simp only [chartPartialBarComplex, hd, hg.eq_of_nhds]
  simp only [c3RicciInChart, hg.eq_of_nhds, hc]

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

/-- General MA gives every Ricci coefficient on the chart target, hence an
open-neighborhood identity available for differentiation at its centre. -/
theorem c3RicciInChart_perturb_eq_of_solvesMongeAmpere (ω₀ : KahlerForm n M)
    {G φ : M → ℝ} (hG : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ G)
    (hsol : ω₀.SolvesMongeAmpere G φ) (x : M)
    {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) (j l : Fin n) :
    c3RicciInChart (c3PerturbedMetricInChart ω₀ φ x) z j l =
      c3RicciInChart (ω₀.metricInChart x) z j l - c3ForcingHessianInChart G x z j l := by
  have hlog : (fun y : M ↦ Real.log (ContinuousAlternatingMap.relDet
      (ω₀ y) ((ω₀.perturb φ hsol.1) y))) = G := by
    funext y
    have hdet : ContinuousAlternatingMap.relDet (ω₀ y) ((ω₀.perturb φ hsol.1) y) =
        Real.exp (G y) := by
      simpa [mongeAmpere, perturb_apply] using hsol.2 y
    rw [hdet, Real.log_exp]
  have hform := ω₀.ricciForm_eq_sub_mddbar (ω₀.perturb φ hsol.1)
  rw [hlog] at hform
  have hmetric : c3PerturbedMetricInChart ω₀ φ x =ᶠ[nhds z]
      (ω₀.perturb φ hsol.1).metricInChart x := by
    filter_upwards [(isOpen_extChartAt_target x).mem_nhds hz] with w hw
    simpa [c3PerturbedMetricInChart, extChartAt] using
      (ω₀.metricInChart_perturb hsol.1 x hw).symm
  rw [ricci_germ_congr hmetric, c3RicciInChart_eq_ricciForm_coeff _ x hz j l, hform]
  have hchart : (ω₀.ricciForm - mddbar n G).chartRep x z =
      ω₀.ricciForm.chartRep x z - (mddbar n G).chartRep x z := by
    ext v
    simp [FormField.chartRep, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  rw [hchart, ContinuousAlternatingMap.coeffMatrix_sub, chartRep_mddbar hG x hz]
  change (ω₀.ricciForm.chartRep x z).coeffMatrix j l -
    (ddbar (G ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z).coeffMatrix j l = _
  rw [← c3RicciInChart_eq_ricciForm_coeff ω₀ x hz j l]
  rfl

end KahlerForm
