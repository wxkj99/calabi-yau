module

public import CalabiYau.MongeAmpere.Estimates.C2.ChernLuFormula.NormalCoordinates.HolomorphicPatch
import CalabiYau.Geometry.Manifold.Tensor.Alternating.Composition

/-!
# First-derivative symmetry of a pulled-back Kähler metric

A holomorphic pullback of a Kähler metric remains Kähler on the local coordinate patch, so its
coefficient matrix satisfies the Kähler first-derivative symmetry throughout the patch.
-/

@[expose] public section

open scoped Manifold ContDiff Topology
open ContinuousAlternatingMap Filter

namespace KahlerForm

theorem pulledBackMetricInChart_first_derivative_symmetric
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (ω₁ : KahlerForm n M) (x : M)
    (ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (U : Set (EuclideanSpace ℂ (Fin n)))
    (hU : IsOpen U)
    (hψ : ContDiffOn ℝ 2 ψ U)
    (hψhol : DifferentiableOn ℂ ψ U)
    (hchart : Set.MapsTo ψ U
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ U)
    (i j k : Fin n) :
    chartPartialZComplex
      (fun w ↦ pulledBackMetricInChart ω₁ x ψ w j k) z i =
    chartPartialZComplex
      (fun w ↦ pulledBackMetricInChart ω₁ x ψ w i k) z j := by
  let E := EuclideanSpace ℂ (Fin n)
  let α : E → E [⋀^Fin 2]→L[ℝ] ℝ := ω₁.toFormField.chartRep x
  let β : E → E [⋀^Fin 2]→L[ℝ] ℝ := fun w ↦
    (α (ψ w)).compContinuousLinearMap (fderiv ℝ ψ w)
  have hψz : ContDiffAt ℝ 2 ψ z := hψ.contDiffAt (hU.mem_nhds hz)
  have hαz : ContDiffAt ℝ ∞ α (ψ z) :=
    (ω₁.isSmooth x).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds (hchart hz))
  have hJ : ContDiffAt ℝ 1 (fun w : E ↦ fderiv ℝ ψ w) z := by
    exact hψz.fderiv_right (m := 1) (by norm_num)
  have hle : (1 : ℕ∞ω) ≤ ∞ := by
    change ((1 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top
  have hAlphaPsi : ContDiffAt ℝ 2 (fun w : E ↦ α (ψ w)) z := by
    exact (hαz.of_le (WithTop.coe_le_coe.mpr le_top)).comp z hψz
  let A : E → (E [⋀^Fin 2]→L[ℝ] ℝ) →L[ℝ] (E [⋀^Fin 2]→L[ℝ] ℝ) :=
    fun w ↦ ContinuousAlternatingMap.compContinuousLinearMapCLM
      (ι := Fin 2) (E := E) (F := ℝ) (fderiv ℝ ψ w)
  let C : (E →L[ℝ] E) →
      (E [⋀^Fin 2]→L[ℝ] ℝ) →L[ℝ] (E [⋀^Fin 2]→L[ℝ] ℝ) :=
    fun p ↦ ContinuousAlternatingMap.compContinuousLinearMapCLM p
  have hC : ContDiffAt ℝ ⊤ C (fderiv ℝ ψ z) :=
    (ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff_real
      (ι := Fin 2) (F₁ := E) (F₂ := ℝ)).contDiffAt
  have hA : ContDiffAt ℝ 1 A z := by
    have hC1 : ContDiffAt ℝ 1 C (fderiv ℝ ψ z) := hC.of_le (by norm_num)
    exact hC1.comp z hJ
  have hBeta : ContDiffAt ℝ 1 β z := by
    convert hA.clm_apply (hAlphaPsi.of_le (by norm_num)) using 1; rfl
  have hclosedα : _root_.extDeriv α (ψ z) = 0 := by
    have hclosed0 : ω₁.toFormField.extDeriv = 0 := ω₁.isClosed
    have heval := congrArg (fun γ ↦ γ.chartRep x (ψ z)) hclosed0
    rw [FormField.chartRep_extDeriv ω₁.isSmooth x (hchart hz), FormField.chartRep_zero] at heval
    exact heval
  have hpull := _root_.extDeriv_pullback
    (hαz.differentiableAt (by norm_num)) hψz (by
      rw [minSmoothness_of_isRCLikeNormedField])
  have hclosed : _root_.extDeriv β z = 0 := by
    change _root_.extDeriv (fun w ↦ (α (ψ w)).compContinuousLinearMap (fderiv ℝ ψ w)) z = 0
    rw [hpull, hclosedα]
    ext v
    simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  have hβone : ∀ᶠ w in nhds z, (β w).IsOneOne := by
    filter_upwards [hU.mem_nhds hz] with w hw
    have hψd : DifferentiableAt ℂ ψ w :=
      (hψhol w hw).differentiableAt (hU.mem_nhds hw)
    have hreal : fderiv ℝ ψ w = (fderiv ℂ ψ w).restrictScalars ℝ :=
      hψd.fderiv_restrictScalars (𝕜 := ℝ)
    have hαone : (α (ψ w)).IsOneOne := ω₁.chartRep_isOneOne x (hchart hw)
    change ((α (ψ w)).compContinuousLinearMap (fderiv ℝ ψ w)).IsOneOne
    rw [hreal]
    exact hαone.compContinuousLinearMap (fderiv ℂ ψ w)
  have hmetric (w : E) (hw : w ∈ U) : (β w).coeffMatrix =
      pulledBackMetricInChart ω₁ x ψ w := by
    have hψd : DifferentiableAt ℂ ψ w :=
      (hψhol w hw).differentiableAt (hU.mem_nhds hw)
    have hreal : fderiv ℝ ψ w = (fderiv ℂ ψ w).restrictScalars ℝ :=
      hψd.fderiv_restrictScalars (𝕜 := ℝ)
    have hαone : (α (ψ w)).IsOneOne := ω₁.chartRep_isOneOne x (hchart hw)
    rw [show β w = (α (ψ w)).compContinuousLinearMap (fderiv ℝ ψ w) by rfl, hreal]
    rw [hαone.coeffMatrix_compContinuousLinearMap (fderiv ℂ ψ w)]
    simp [pulledBackMetricInChart, holomorphicJacobianMatrix, metricInChart, α]
  let mJK : E → ℂ := fun w ↦ (pulledBackMetricInChart ω₁ x ψ w) j k
  let mIK : E → ℂ := fun w ↦ (pulledBackMetricInChart ω₁ x ψ w) i k
  have hcoeffJK : (fun w ↦ (β w).coeffMatrix j k) =ᶠ[nhds z] mJK := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact congrArg (fun G : Matrix (Fin n) (Fin n) ℂ ↦ G j k) (hmetric w hw)
  have hcoeffIK : (fun w ↦ (β w).coeffMatrix i k) =ᶠ[nhds z] mIK := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact congrArg (fun G : Matrix (Fin n) (Fin n) ℂ ↦ G i k) (hmetric w hw)
  have hsymm := chartPartialZComplex_coeffMatrix_symm hBeta hclosed hβone i j k
  change chartPartialZComplex mJK z i = chartPartialZComplex mIK z j
  unfold chartPartialZComplex at hsymm ⊢
  rw [← hcoeffJK.fderiv_eq, ← hcoeffIK.fderiv_eq]
  exact hsymm

end KahlerForm
