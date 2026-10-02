module

public import CalabiYau.MongeAmpere.Estimates.C2.ChernLuFormula.NormalCoordinates
import CalabiYau.Geometry.Manifold.Tensor.Alternating.Composition

/-!
# Kähler symmetry of first metric derivatives

The first derivatives of the coefficients of a Kähler metric are symmetric in the derivative
index and the first metric index.

Source: Székelyhidi, *An Introduction to Extremal Kähler Metrics*, §3.2, proof of Lemma 3.7,
pp. 41–42; the identity follows from the local Kähler potential.
-/

@[expose] public section

open scoped Manifold ContDiff ComplexOrder MatrixOrder

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

/-- The varying metric's first coordinate derivatives satisfy the Kähler symmetry. -/
theorem normalFrame_first_derivative_symmetric
    (ω₀ ω₁ : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x) :
    ∀ i j k, normalFrameFirstDerivative F i j k = normalFrameFirstDerivative F j i k := by
  intro i j k
  let E := EuclideanSpace ℂ (Fin n)
  let α : E → E [⋀^Fin 2]→L[ℝ] ℝ := ω₁.toFormField.chartRep x
  let β : E → E [⋀^Fin 2]→L[ℝ] ℝ := fun w ↦
    (α (F.map w)).compContinuousLinearMap (fderiv ℝ F.map w)
  have hFtop : ContDiffAt ℝ ∞ F.map F.center :=
    F.smooth_map.contDiffAt (F.isOpen_domain.mem_nhds F.center_mem)
  have hle2 : (2 : ℕ∞ω) ≤ ∞ := by
    change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top
  have hFz : ContDiffAt ℝ 2 F.map F.center := hFtop.of_le hle2
  have hαz : ContDiffAt ℝ ∞ α (F.map F.center) :=
    (ω₁.isSmooth x).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds (F.maps_into_chart F.center F.center_mem))
  have hJ : ContDiffAt ℝ 1 (fun w : E ↦ fderiv ℝ F.map w) F.center := by
    exact hFz.fderiv_right (m := 1) (by norm_num)
  have hAlphaPsi : ContDiffAt ℝ 2 (fun w : E ↦ α (F.map w)) F.center := by
    exact (hαz.of_le hle2).comp F.center hFz
  let A : E → (E [⋀^Fin 2]→L[ℝ] ℝ) →L[ℝ] (E [⋀^Fin 2]→L[ℝ] ℝ) :=
    fun w ↦ ContinuousAlternatingMap.compContinuousLinearMapCLM
      (ι := Fin 2) (E := E) (F := ℝ) (fderiv ℝ F.map w)
  let C : (E →L[ℝ] E) →
      (E [⋀^Fin 2]→L[ℝ] ℝ) →L[ℝ] (E [⋀^Fin 2]→L[ℝ] ℝ) :=
    fun p ↦ ContinuousAlternatingMap.compContinuousLinearMapCLM p
  have hC : ContMDiff (𝓘(ℝ, E →L[ℝ] E))
      (𝓘(ℝ, ((E [⋀^Fin 2]→L[ℝ] ℝ) →L[ℝ] (E [⋀^Fin 2]→L[ℝ] ℝ)))) ⊤ C :=
    ContinuousAlternatingMap.compContinuousLinearMapCLM_contMDiff_of_space_real
      (ι := Fin 2) (F₁ := E) (F₁' := E) (F₂ := ℝ)
  have hCd : ContDiff ℝ ⊤ C := contMDiff_iff_contDiff.mp hC
  have hA : ContDiffAt ℝ 1 A F.center := by
    have hC1 : ContDiffAt ℝ 1 C (fderiv ℝ F.map F.center) :=
      hCd.contDiffAt.of_le (by norm_num)
    exact hC1.comp F.center hJ
  have hBeta : ContDiffAt ℝ 1 β F.center := by
    convert hA.clm_apply (hAlphaPsi.of_le (by norm_num)) using 1
    all_goals rfl
  have hclosedα : _root_.extDeriv α (F.map F.center) = 0 := by
    have hclosed0 : ω₁.toFormField.extDeriv = 0 := ω₁.isClosed
    have heval := congrArg (fun γ ↦ γ.chartRep x (F.map F.center)) hclosed0
    rw [FormField.chartRep_extDeriv ω₁.isSmooth x
      (F.maps_into_chart F.center F.center_mem), FormField.chartRep_zero] at heval
    exact heval
  have hpull := _root_.extDeriv_pullback
    (hαz.differentiableAt (by norm_num)) hFz (by
      rw [minSmoothness_of_isRCLikeNormedField])
  have hclosed : _root_.extDeriv β F.center = 0 := by
    change _root_.extDeriv
      (fun w ↦ (α (F.map w)).compContinuousLinearMap (fderiv ℝ F.map w)) F.center = 0
    rw [hpull, hclosedα]
    ext v
    simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  have hβone : ∀ᶠ w in nhds F.center, (β w).IsOneOne := by
    filter_upwards [F.isOpen_domain.mem_nhds F.center_mem] with w hw
    have hFd : DifferentiableAt ℂ F.map w :=
      (F.holomorphic_map w hw).differentiableAt (F.isOpen_domain.mem_nhds hw)
    have hreal : fderiv ℝ F.map w = (fderiv ℂ F.map w).restrictScalars ℝ :=
      hFd.fderiv_restrictScalars (𝕜 := ℝ)
    have hαone : (α (F.map w)).IsOneOne := ω₁.chartRep_isOneOne x (F.maps_into_chart w hw)
    change ((α (F.map w)).compContinuousLinearMap (fderiv ℝ F.map w)).IsOneOne
    rw [hreal]
    exact hαone.compContinuousLinearMap (fderiv ℂ F.map w)
  have hmetric (w : E) (hw : w ∈ F.domain) : (β w).coeffMatrix =
      pulledBackMetricInChart ω₁ x F.map w := by
    have hFd : DifferentiableAt ℂ F.map w :=
      (F.holomorphic_map w hw).differentiableAt (F.isOpen_domain.mem_nhds hw)
    have hreal : fderiv ℝ F.map w = (fderiv ℂ F.map w).restrictScalars ℝ :=
      hFd.fderiv_restrictScalars (𝕜 := ℝ)
    have hαone : (α (F.map w)).IsOneOne := ω₁.chartRep_isOneOne x (F.maps_into_chart w hw)
    rw [show β w = (α (F.map w)).compContinuousLinearMap (fderiv ℝ F.map w) by rfl, hreal]
    rw [hαone.coeffMatrix_compContinuousLinearMap (fderiv ℂ F.map w)]
    simp [pulledBackMetricInChart, holomorphicJacobianMatrix, metricInChart, α]
  have hcoeffJK : (fun w ↦ (β w).coeffMatrix j k) =ᶠ[nhds F.center]
      fun w ↦ (pulledBackMetricInChart ω₁ x F.map w) j k := by
    filter_upwards [F.isOpen_domain.mem_nhds F.center_mem] with w hw
    exact congrArg (fun G : Matrix (Fin n) (Fin n) ℂ ↦ G j k) (hmetric w hw)
  have hcoeffIK : (fun w ↦ (β w).coeffMatrix i k) =ᶠ[nhds F.center]
      fun w ↦ (pulledBackMetricInChart ω₁ x F.map w) i k := by
    filter_upwards [F.isOpen_domain.mem_nhds F.center_mem] with w hw
    exact congrArg (fun G : Matrix (Fin n) (Fin n) ℂ ↦ G i k) (hmetric w hw)
  have hsymm := chartPartialZComplex_coeffMatrix_symm hBeta hclosed hβone i j k
  change chartPartialZComplex (fun w ↦ (pulledBackMetricInChart ω₁ x F.map w) j k)
      F.center i =
    chartPartialZComplex (fun w ↦ (pulledBackMetricInChart ω₁ x F.map w) i k)
      F.center j
  unfold chartPartialZComplex at hsymm ⊢
  rw [← hcoeffJK.fderiv_eq, ← hcoeffIK.fderiv_eq]
  exact hsymm

end KahlerForm
