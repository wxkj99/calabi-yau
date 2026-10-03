module

public import CalabiYau.Geometry.Kahler.Laplacian
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The complex Monge–Ampère operator and its linearization

For a Kähler form `ω₀` and a real function `φ`,

  `KahlerForm.mongeAmpere ω₀ φ = (ω₀ + i∂∂̄φ)ⁿ / ω₀ⁿ = det(g_{jk̄} + φ_{jk̄}) / det(g_{jk̄})`,

a smooth positive function when `φ` is a Kähler potential (`mongeAmpere_eq_inChart`). The complex
Monge–Ampère equation `(ω₀ + i∂∂̄φ)ⁿ = e^G ω₀ⁿ` is `KahlerForm.SolvesMongeAmpere ω₀ G φ`.

The linearization at a potential `φ` is the complex Laplacian of `ω_φ = ω₀ + i∂∂̄φ`:
`d/dt|₀ log mongeAmpere (φ + tψ) = Δ_{ω_φ} ψ` (`hasDerivAt_log_mongeAmpere`).

The integral identities `∫ (ω₀ + i∂∂̄φ)ⁿ = ∫ ω₀ⁿ` (`integral_mongeAmpere`) and the segment formula
`mongeAmpere_sub_one_eq_integral` are the inputs of Calabi's uniqueness argument and of Yau's
`C⁰` estimate (combined with Green's formula for `ω₀ + s i∂∂̄φ`, `0 ≤ s ≤ 1`).

`KahlerForm.MongeAmpereSolvable ω₀` is the existence statement for the fixed Kähler form
`ω₀`; it is the hypothesis from which the Calabi conjecture is derived in `CalabiYau.Yau`.
-/

@[expose] public section

open scoped Manifold ContDiff
open Set MeasureTheory ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] (ω₀ : KahlerForm n M)

/-- The complex Monge–Ampère operator `(ω₀ + i∂∂̄φ)ⁿ / ω₀ⁿ`. -/
noncomputable def mongeAmpere (φ : M → ℝ) (x : M) : ℝ :=
  relDet (ω₀ x) (ω₀ x + mddbar n φ x)

/-- `φ` solves the complex Monge–Ampère equation `(ω₀ + i∂∂̄φ)ⁿ = e^G ω₀ⁿ` with
`ω₀ + i∂∂̄φ > 0`. -/
def SolvesMongeAmpere (G φ : M → ℝ) : Prop :=
  ω₀.IsPotential φ ∧ ∀ x, ω₀.mongeAmpere φ x = Real.exp (G x)

/-- Existence in the complex Monge–Ampère problem for `ω₀`: every smooth `F` with
`∫ e^F ω₀ⁿ = ∫ ω₀ⁿ` is `log ((ω₀ + i∂∂̄φ)ⁿ / ω₀ⁿ)` for a Kähler potential `φ`. -/
def MongeAmpereSolvable [MeasurableSpace M] [BorelSpace M] [T2Space M] [SigmaCompactSpace M] :
    Prop :=
  ∀ F : M → ℝ, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F →
    ∫ x, Real.exp (F x) ∂ω₀.volume = ω₀.volume.real univ → ∃ φ, ω₀.SolvesMongeAmpere F φ

variable {ω₀} {φ ψ : M → ℝ}

theorem mongeAmpere_eq_relDet_perturb (hφ : ω₀.IsPotential φ) (x : M) :
    ω₀.mongeAmpere φ x = relDet (ω₀ x) (ω₀.perturb φ hφ x) := rfl

@[simp]
theorem mongeAmpere_zero : ω₀.mongeAmpere 0 = 1 := by
  funext x
  change relDet (ω₀ x) (ω₀ x + mddbar n (fun _ : M ↦ (0 : ℝ)) x) = 1
  rw [mddbar_const]
  simpa using relDet_self (ω₀.isPositive x)

theorem mongeAmpere_pos (hφ : ω₀.IsPotential φ) (x : M) : 0 < ω₀.mongeAmpere φ x := by
  rw [mongeAmpere_eq_relDet_perturb hφ]
  exact relDet_pos (ω₀.isPositive x) (hφ.2 x)

@[simp]
theorem mongeAmpere_add_const (c : ℝ) : ω₀.mongeAmpere (fun x ↦ φ x + c) = ω₀.mongeAmpere φ := by
  funext x
  rw [mongeAmpere, mongeAmpere, mddbar_add_const]

/-- The Monge–Ampère operator in a chart: `det(g + φ_{jk̄}) / det g`. -/
theorem mongeAmpere_eq_inChart (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ φ)
    (x : M) {y : M} (hy : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source) :
    ω₀.mongeAmpere φ y =
      RCLike.re (ω₀.metricInChart x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y) +
          complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)).det /
      RCLike.re (ω₀.metricInChart x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)).det := by
  let I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
  let IC := 𝓘(ℂ, EuclideanSpace ℂ (Fin n))
  let z := extChartAt I x y
  have hyx : y ∈ (extChartAt I x).source := by
    rw [extChartAt_source]
    exact hy
  have hyy : y ∈ (extChartAt I y).source := mem_extChartAt_source y
  have hz : z ∈ (extChartAt I x).target := (extChartAt I x).map_source hyx
  have hz' : (extChartAt I x).symm z ∈
      (extChartAt I y).source := by
    rw [(extChartAt I x).left_inv hyx]
    exact hyy
  have hpoint : extChartAt I y ((extChartAt I x).symm z) = extChartAt I y y := by
    rw [(extChartAt I x).left_inv hyx]
  have hxC : y ∈ (extChartAt IC x).source := by
    rw [← extChartAt_real_eq x]
    exact hyx
  have hyC : y ∈ (extChartAt IC y).source := by
    rw [← extChartAt_real_eq y]
    exact hyy
  have hxyR : y ∈ (extChartAt I x).source ∩ (extChartAt I y).source := ⟨hyx, hyy⟩
  let A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    tangentCoordChange IC x y y
  let B : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    tangentCoordChange IC y x y
  have hAB (v : EuclideanSpace ℂ (Fin n)) : A (B v) = v := by
    calc
      A (B v) = tangentCoordChange IC y y y v := by
        exact tangentCoordChange_comp (I := IC) (w := y) (x := x) (y := y) (z := y)
          (h := ⟨⟨hyC, hxC⟩, hyC⟩) (v := v)
      _ = v := tangentCoordChange_self (I := IC) (x := y) (z := y) hyC
  have hBA (v : EuclideanSpace ℂ (Fin n)) : B (A v) = v := by
    calc
      B (A v) = tangentCoordChange IC x x y v := by
        exact tangentCoordChange_comp (I := IC) (w := x) (x := y) (y := x) (z := y)
          (h := ⟨⟨hxC, hyC⟩, hxC⟩) (v := v)
      _ = v := tangentCoordChange_self (I := IC) (x := x) (z := y) hxC
  have hAinj : Function.Injective A := by
    intro u v huv
    calc
      u = B (A u) := (hBA u).symm
      _ = B (A v) := congrArg B huv
      _ = v := hBA v
  have hAsurj : Function.Surjective A := by
    intro v
    exact ⟨B v, hAB v⟩
  let eA : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n) :=
    let eLin := LinearEquiv.ofBijective A.toLinearMap ⟨hAinj, hAsurj⟩
    eLin.toContinuousLinearEquivOfContinuous eLin.toLinearMap.continuous_of_finiteDimensional
  have hAreal : tangentCoordChange I x y y = A.restrictScalars ℝ := by
    exact tangentCoordChange_real_eq hxyR
  have htransition :
      fderiv ℝ (extChartAt I y ∘ (extChartAt I x).symm) z = A.restrictScalars ℝ := by
    calc
      _ = tangentCoordChange I x y y := by
        rw [tangentCoordChange_def, ModelWithCorners.range_eq_univ, fderivWithin_univ]
      _ = A.restrictScalars ℝ := hAreal
  have hrep (α : FormField (EuclideanSpace ℂ (Fin n)) M 2) :
      α.chartRep x z = (α y).compContinuousLinearMap (A.restrictScalars ℝ) := by
    rw [FormField.chartRep_eq_chartRep_comp hz hz', htransition]
    rw [hpoint]
    exact congrArg (fun β ↦ β.compContinuousLinearMap (A.restrictScalars ℝ))
      (FormField.chartRep_self α y)
  have hαone : (ω₀.toFormField + mddbar n φ).IsOneOne := by
    intro w
    exact (ω₀.isOneOne w).add (isOneOne_mddbar hφ w)
  have hAe : (eA : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) = A := by
    ext v
    rfl
  have hrel := (relDet_compContinuousLinearMap (ω₀.isOneOne y) (hαone y) eA).symm
  rw [hAe] at hrel
  rw [← hrep ω₀.toFormField, ← hrep (ω₀.toFormField + mddbar n φ)] at hrel
  have hcoeffω : (ω₀.toFormField.chartRep x z).coeffMatrix = ω₀.metricInChart x z := rfl
  have hcoeffα : ((ω₀.toFormField + mddbar n φ).chartRep x z).coeffMatrix =
      ω₀.metricInChart x z + complexHessian (φ ∘ (extChartAt I x).symm) z := by
    change ((ω₀.toFormField.chartRep x z + (mddbar n φ).chartRep x z).coeffMatrix) = _
    rw [ContinuousAlternatingMap.coeffMatrix_add, hcoeffω, chartRep_mddbar hφ x hz]
    rfl
  rw [mongeAmpere]
  change relDet (ω₀.toFormField y) ((ω₀.toFormField + mddbar n φ) y) = _
  rw [hrel]
  change RCLike.re (((ω₀.toFormField + mddbar n φ).chartRep x z).coeffMatrix).det /
      RCLike.re ((ω₀.toFormField.chartRep x z).coeffMatrix).det = _
  rw [hcoeffω, hcoeffα]

/-- `C²` version of `mongeAmpere_eq_inChart` (for the `C^{2,α}` solutions of the openness
step). -/
theorem mongeAmpere_eq_inChart_of_contMDiff_two
    (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 φ)
    (x : M) {y : M} (hy : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source) :
    ω₀.mongeAmpere φ y =
      RCLike.re (ω₀.metricInChart x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y) +
          complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)).det /
      RCLike.re (ω₀.metricInChart x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)).det := by
  let I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
  let IC := 𝓘(ℂ, EuclideanSpace ℂ (Fin n))
  let z := extChartAt I x y
  have hyx : y ∈ (extChartAt I x).source := by
    rw [extChartAt_source]
    exact hy
  have hyy : y ∈ (extChartAt I y).source := mem_extChartAt_source y
  have hz : z ∈ (extChartAt I x).target := (extChartAt I x).map_source hyx
  have hz' : (extChartAt I x).symm z ∈ (extChartAt I y).source := by
    rw [(extChartAt I x).left_inv hyx]
    exact hyy
  have hpoint : extChartAt I y ((extChartAt I x).symm z) = extChartAt I y y := by
    rw [(extChartAt I x).left_inv hyx]
  let Iy := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
  let ey := extChartAt Iy y
  let zy := ey y
  have hzy : zy ∈ ey.target := mem_extChartAt_target y
  have hzyN : ey.target ∈ nhds zy := (isOpen_extChartAt_target y).mem_nhds hzy
  have hey : ContMDiffAt Iy Iy ∞ ey.symm zy := (contMDiffOn_extChartAt_symm y).contMDiffAt hzyN
  have hey₂ : ContMDiffAt Iy Iy 2 ey.symm zy := by
    have hbound : (2 : ℕ∞ω) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω) :=
      WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)
    exact hey.of_le hbound
  have hφy : ContDiffAt ℝ 2 (φ ∘ ey.symm) zy := (hφ.contMDiffAt.comp zy hey₂).contDiffAt
  have hmdOne : (mddbar n φ y).IsOneOne := by
    change (ddbar (φ ∘ ey.symm) zy).IsOneOne
    exact isOneOne_ddbar hφy
  have hxC : y ∈ (extChartAt IC x).source := by
    rw [← extChartAt_real_eq x]
    exact hyx
  have hyC : y ∈ (extChartAt IC y).source := by
    rw [← extChartAt_real_eq y]
    exact hyy
  have hxyR : y ∈ (extChartAt I x).source ∩ (extChartAt I y).source := ⟨hyx, hyy⟩
  let A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    tangentCoordChange IC x y y
  let B : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    tangentCoordChange IC y x y
  have hAB (v : EuclideanSpace ℂ (Fin n)) : A (B v) = v := by
    calc
      A (B v) = tangentCoordChange IC y y y v := by
        exact tangentCoordChange_comp (I := IC) (w := y) (x := x) (y := y) (z := y)
          (h := ⟨⟨hyC, hxC⟩, hyC⟩) (v := v)
      _ = v := tangentCoordChange_self (I := IC) (x := y) (z := y) hyC
  have hBA (v : EuclideanSpace ℂ (Fin n)) : B (A v) = v := by
    calc
      B (A v) = tangentCoordChange IC x x y v := by
        exact tangentCoordChange_comp (I := IC) (w := x) (x := y) (y := x) (z := y)
          (h := ⟨⟨hxC, hyC⟩, hxC⟩) (v := v)
      _ = v := tangentCoordChange_self (I := IC) (x := x) (z := y) hxC
  have hAinj : Function.Injective A := by
    intro u v huv
    calc
      u = B (A u) := (hBA u).symm
      _ = B (A v) := congrArg B huv
      _ = v := hBA v
  have hAsurj : Function.Surjective A := by
    intro v
    exact ⟨B v, hAB v⟩
  let eA : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n) :=
    let eLin := LinearEquiv.ofBijective A.toLinearMap ⟨hAinj, hAsurj⟩
    eLin.toContinuousLinearEquivOfContinuous eLin.toLinearMap.continuous_of_finiteDimensional
  have hAreal : tangentCoordChange I x y y = A.restrictScalars ℝ :=
    tangentCoordChange_real_eq hxyR
  have htransition :
      fderiv ℝ (extChartAt I y ∘ (extChartAt I x).symm) z = A.restrictScalars ℝ := by
    calc
      _ = tangentCoordChange I x y y := by
        rw [tangentCoordChange_def, ModelWithCorners.range_eq_univ, fderivWithin_univ]
      _ = A.restrictScalars ℝ := hAreal
  have hrep (α : FormField (EuclideanSpace ℂ (Fin n)) M 2) :
      α.chartRep x z = (α y).compContinuousLinearMap (A.restrictScalars ℝ) := by
    rw [FormField.chartRep_eq_chartRep_comp hz hz', htransition, hpoint]
    exact congrArg (fun β ↦ β.compContinuousLinearMap (A.restrictScalars ℝ))
      (FormField.chartRep_self α y)
  have hαone : ((ω₀.toFormField + mddbar n φ) y).IsOneOne :=
    (ω₀.isOneOne y).add hmdOne
  have hAe : (eA : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) = A := by
    ext v
    rfl
  have hrel := (relDet_compContinuousLinearMap (ω₀.isOneOne y) hαone eA).symm
  rw [hAe] at hrel
  rw [← hrep ω₀.toFormField, ← hrep (ω₀.toFormField + mddbar n φ)] at hrel
  have hcoeffω : (ω₀.toFormField.chartRep x z).coeffMatrix = ω₀.metricInChart x z := rfl
  have hcoeffα : ((ω₀.toFormField + mddbar n φ).chartRep x z).coeffMatrix =
      ω₀.metricInChart x z + complexHessian (φ ∘ (extChartAt I x).symm) z := by
    change ((ω₀.toFormField.chartRep x z + (mddbar n φ).chartRep x z).coeffMatrix) = _
    rw [ContinuousAlternatingMap.coeffMatrix_add, hcoeffω,
      chartRep_mddbar_of_contMDiff_two hφ x hz]
    rfl
  rw [mongeAmpere]
  change relDet (ω₀.toFormField y) ((ω₀.toFormField + mddbar n φ) y) = _
  rw [hrel]
  change RCLike.re (((ω₀.toFormField + mddbar n φ).chartRep x z).coeffMatrix).det /
      RCLike.re ((ω₀.toFormField.chartRep x z).coeffMatrix).det = _
  rw [hcoeffω, hcoeffα]

open scoped ComplexOrder in
theorem contMDiff_mongeAmpere (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ φ) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (ω₀.mongeAmpere φ) := by
  intro y
  rw [contMDiffAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt]
  simp only [ModelWithCorners.range_eq_univ, contDiffWithinAt_univ]
  let I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
  let e := extChartAt I y
  let z := e y
  have hz : z ∈ e.target := mem_extChartAt_target y
  have hzN : e.target ∈ nhds z := (isOpen_extChartAt_target y).mem_nhds hz
  have hmetricEntry (j k : Fin n) :
      ContDiffOn ℝ ∞ (fun u ↦ ω₀.metricInChart y u j k) e.target :=
    ω₀.contDiffOn_metricInChart y j k
  have hφsymm : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
      (φ ∘ e.symm) e.target := by
    have hφon : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ φ univ :=
      contMDiffOn_univ.mpr hφ
    exact hφon.comp (contMDiffOn_extChartAt_symm y) (by intro u hu; simp)
  have hφchart : ContDiffOn ℝ ∞ (φ ∘ e.symm) e.target := hφsymm.contDiffOn
  have hddbar : ContDiffOn ℝ ∞ (ddbar (φ ∘ e.symm)) e.target :=
    ContDiffOn.ddbar (isOpen_extChartAt_target y) hφchart
  have hcomplexEntry (j k : Fin n) :
      ContDiffOn ℝ ∞ (fun u ↦ complexHessian (φ ∘ e.symm) u j k) e.target := by
    let f₁ : EuclideanSpace ℂ (Fin n) → ℝ :=
      fun u ↦ ddbar (φ ∘ e.symm) u ![EuclideanSpace.single j 1, Complex.I • EuclideanSpace.single k 1]
    let f₂ : EuclideanSpace ℂ (Fin n) → ℝ :=
      fun u ↦ ddbar (φ ∘ e.symm) u ![EuclideanSpace.single j 1, EuclideanSpace.single k 1]
    have hf₁ : ContDiffOn ℝ ∞ f₁ e.target := by
      dsimp [f₁]
      exact ((ContinuousAlternatingMap.apply ℝ (EuclideanSpace ℂ (Fin n)) ℝ
        ![EuclideanSpace.single j 1, Complex.I • EuclideanSpace.single k 1]).contDiff).comp_contDiffOn
          hddbar
    have hf₂ : ContDiffOn ℝ ∞ f₂ e.target := by
      dsimp [f₂]
      exact ((ContinuousAlternatingMap.apply ℝ (EuclideanSpace ℂ (Fin n)) ℝ
        ![EuclideanSpace.single j 1, EuclideanSpace.single k 1]).contDiff).comp_contDiffOn hddbar
    have hf₁c : ContDiffOn ℝ ∞ (fun u ↦ (f₁ u : ℂ)) e.target := by
      convert Complex.ofRealCLM.contDiff.comp_contDiffOn hf₁ using 1
      ext u
      simp [f₁, Complex.ofRealCLM_apply]
    have hf₂c : ContDiffOn ℝ ∞ (fun u ↦ (f₂ u : ℂ)) e.target := by
      convert Complex.ofRealCLM.contDiff.comp_contDiffOn hf₂ using 1
      ext u
      simp [f₂, Complex.ofRealCLM_apply]
    have hnumc : ContDiffOn ℝ ∞
        (fun u ↦ (f₁ u : ℂ) - Complex.I * (f₂ u : ℂ)) e.target := by
      exact hf₁c.sub (contDiffOn_const.mul hf₂c)
    change ContDiffOn ℝ ∞
      (fun u ↦ ((f₁ u : ℂ) - Complex.I * (f₂ u : ℂ)) / 2) e.target
    exact hnumc.div_const (2 : ℂ)
  have hnumEntry (j k : Fin n) : ContDiffOn ℝ ∞
      (fun u ↦ ω₀.metricInChart y u j k + complexHessian (φ ∘ e.symm) u j k) e.target :=
    (hmetricEntry j k).add (hcomplexEntry j k)
  let num : EuclideanSpace ℂ (Fin n) → ℝ := fun u ↦
    RCLike.re (ω₀.metricInChart y u + complexHessian (φ ∘ e.symm) u).det
  let den : EuclideanSpace ℂ (Fin n) → ℝ := fun u ↦
    RCLike.re (ω₀.metricInChart y u).det
  have hnum : ContDiffOn ℝ ∞ num e.target := by
    have hdet : ContDiffOn ℝ ∞
        (fun u ↦ (ω₀.metricInChart y u + complexHessian (φ ∘ e.symm) u).det) e.target := by
      simp_rw [Matrix.det_apply]
      fun_prop (disch := assumption)
    change ContDiffOn ℝ ∞
      (fun u ↦ Complex.re ((ω₀.metricInChart y u + complexHessian (φ ∘ e.symm) u).det)) e.target
    convert Complex.reCLM.contDiff.comp_contDiffOn hdet using 1
    ext u
    change ((ω₀.metricInChart y u + complexHessian (φ ∘ e.symm) u).det).re =
      Complex.reCLM ((ω₀.metricInChart y u + complexHessian (φ ∘ e.symm) u).det)
    exact (Complex.reCLM_apply _).symm
  have hden : ContDiffOn ℝ ∞ den e.target := by
    have hdet : ContDiffOn ℝ ∞ (fun u ↦ (ω₀.metricInChart y u).det) e.target := by
      simp_rw [Matrix.det_apply]
      fun_prop (disch := assumption)
    change ContDiffOn ℝ ∞ (fun u ↦ Complex.re (ω₀.metricInChart y u).det) e.target
    convert Complex.reCLM.contDiff.comp_contDiffOn hdet using 1
    ext u
    change (ω₀.metricInChart y u).det.re = Complex.reCLM (ω₀.metricInChart y u).det
    exact (Complex.reCLM_apply _).symm
  have hdetpos := (ω₀.posDef_metricInChart y hz).det_pos
  have hdenpos : 0 < den z := by
    dsimp [den]
    exact (RCLike.pos_iff.mp hdetpos).1
  have hratio : ContDiffAt ℝ ∞ (fun u ↦ num u / den u) z := by
    exact (hnum.contDiffAt hzN).div (hden.contDiffAt hzN) hdenpos.ne'
  have hformula : (fun u ↦ ω₀.mongeAmpere φ (e.symm u)) =ᶠ[nhds z]
      (fun u ↦ num u / den u) := by
    filter_upwards [hzN] with u hu
    have hyu : (e.symm u) ∈ (chartAt (EuclideanSpace ℂ (Fin n)) y).source := by
      rw [← extChartAt_source (I := I)]
      exact e.map_target hu
    have hlocal := mongeAmpere_eq_inChart (ω₀ := ω₀) hφ y hyu
    rw [e.right_inv hu] at hlocal
    simpa [num, den, e, extChartAt, I, modelWithCornersSelf_coe_symm] using hlocal
  exact hratio.congr_of_eventuallyEq hformula

/-- Cocycle property: `MA_ω₀(φ + ψ) = MA_ω₀(φ) · MA_{ω_φ}(ψ)`. -/
theorem mongeAmpere_add (hφ : ω₀.IsPotential φ)
    (hψ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ ψ) (x : M) :
    ω₀.mongeAmpere (φ + ψ) x = ω₀.mongeAmpere φ x * (ω₀.perturb φ hφ).mongeAmpere ψ x := by
  simpa [mongeAmpere, perturb_apply, mddbar_add hφ.1 hψ, add_assoc] using
    (relDet_mul_relDet (ω₀.isPositive x) (hφ.2 x)).symm

theorem SolvesMongeAmpere.add_const {G : M → ℝ} (h : ω₀.SolvesMongeAmpere G φ) (c : ℝ) :
    ω₀.SolvesMongeAmpere G fun x ↦ φ x + c := by
  refine ⟨h.1.add_const c, ?_⟩
  intro x
  rw [mongeAmpere_add_const]
  exact h.2 x

/-! ### Linearization -/

/-- The derivative of the Monge–Ampère operator: `d/dt|₀ MA(φ + tψ) = MA(φ) Δ_{ω_φ} ψ`. -/
theorem hasDerivAt_mongeAmpere (hφ : ω₀.IsPotential φ)
    (hψ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ ψ) (x : M) :
    HasDerivAt (fun t : ℝ ↦ ω₀.mongeAmpere (φ + t • ψ) x)
      (ω₀.mongeAmpere φ x * (ω₀.perturb φ hφ).laplacian ψ x) 0 := by
  have hEq : (fun t : ℝ ↦ ω₀.mongeAmpere (φ + t • ψ) x) =
      fun t ↦ relDet (ω₀ x) ((ω₀ x + mddbar n φ x) + t • mddbar n ψ x) := by
    funext t
    have htψ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (t • ψ) := by
      convert (contMDiff_const : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
        (fun _ : M ↦ t)).smul hψ using 1
    simp only [mongeAmpere]
    rw [mddbar_add hφ.1 htψ, mddbar_smul hψ t]
    simp [Pi.add_apply, Pi.smul_apply, add_assoc]
  rw [hEq]
  have hα : ((ω₀ x + mddbar n φ x) + (0 : ℝ) • mddbar n ψ x).IsPositive := by
    simpa using hφ.2 x
  simpa [mongeAmpere, laplacian, perturb_apply] using
    (hasDerivAt_relDet_add_smul (ω₀.isPositive x) hα
      (α := ω₀ x + mddbar n φ x) (β := mddbar n ψ x) (s := 0))

/-- The linearization of `log MA` at `φ` is the Laplacian of `ω_φ = ω₀ + i∂∂̄φ`. -/
theorem hasDerivAt_log_mongeAmpere (hφ : ω₀.IsPotential φ)
    (hψ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ ψ) (x : M) :
    HasDerivAt (fun t : ℝ ↦ Real.log (ω₀.mongeAmpere (φ + t • ψ) x))
      ((ω₀.perturb φ hφ).laplacian ψ x) 0 := by
  have hEq : (fun t : ℝ ↦ ω₀.mongeAmpere (φ + t • ψ) x) =
      fun t ↦ relDet (ω₀ x) ((ω₀ x + mddbar n φ x) + t • mddbar n ψ x) := by
    funext t
    have htψ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (t • ψ) := by
      convert (contMDiff_const : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
        (fun _ : M ↦ t)).smul hψ using 1
    simp only [mongeAmpere]
    rw [mddbar_add hφ.1 htψ, mddbar_smul hψ t]
    simp [Pi.add_apply, Pi.smul_apply, add_assoc]
  have hlogEq : (fun t : ℝ ↦ Real.log (ω₀.mongeAmpere (φ + t • ψ) x)) =
      fun t ↦ Real.log (relDet (ω₀ x)
        ((ω₀ x + mddbar n φ x) + t • mddbar n ψ x)) := by
    funext t
    rw [congrFun hEq t]
  rw [hlogEq]
  simpa [laplacian, perturb_apply] using
    (hasDerivAt_log_relDet (ω₀.isPositive x) (hφ.2 x)
      (α := ω₀ x + mddbar n φ x) (β := mddbar n ψ x))

/-- `C²` version of `hasDerivAt_log_mongeAmpere`, with positivity of `ω₀ + i∂∂̄φ` only at `x`:
`d/dt|₀ log MA(φ + tψ)(x) = tr_{ω₀+i∂∂̄φ} (i∂∂̄ψ)` at `x`. -/
theorem hasDerivAt_log_mongeAmpere_of_contMDiff_two
    (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 φ)
    (hψ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 ψ) {x : M}
    (hx : (ω₀ x + mddbar n φ x).IsPositive) :
    HasDerivAt (fun t : ℝ ↦ Real.log (ω₀.mongeAmpere (φ + t • ψ) x))
      (relTrace (ω₀ x + mddbar n φ x) (mddbar n ψ x)) 0 := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let z := e x
  have hz : z ∈ e.target := by
    exact mem_extChartAt_target x
  have hzN : e.target ∈ nhds z := (isOpen_extChartAt_target x).mem_nhds hz
  have he : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ e.symm z := by
    exact (contMDiffOn_extChartAt_symm x).contMDiffAt hzN
  have he₂ : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 2 e.symm z := by
    have he_bound : (2 : ℕ∞ω) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω) :=
      WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)
    exact he.of_le he_bound
  have hφchart : ContDiffAt ℝ 2 (φ ∘ e.symm) z := by
    exact (hφ.contMDiffAt.comp z he₂).contDiffAt
  have hψchart : ContDiffAt ℝ 2 (ψ ∘ e.symm) z := by
    exact (hψ.contMDiffAt.comp z he₂).contDiffAt
  have hβ : (mddbar n ψ x).IsOneOne := by
    change (ddbar (ψ ∘ e.symm) z).IsOneOne
    exact isOneOne_ddbar hψchart
  have hdd (t : ℝ) :
      mddbar n (φ + t • ψ) x = mddbar n φ x + t • mddbar n ψ x := by
    have hψt : ContDiffAt ℝ 2 (t • (ψ ∘ e.symm)) z := hψchart.const_smul t
    have hfun : (φ ∘ e.symm) + t • (ψ ∘ e.symm) =
        (φ + t • ψ) ∘ e.symm := by
      funext w
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hlocal : ddbar ((φ + t • ψ) ∘ e.symm) z =
        ddbar (φ ∘ e.symm) z + t • ddbar (ψ ∘ e.symm) z := by
      rw [← hfun, ddbar_add hφchart hψt, ddbar_smul hψchart t]
    change ddbar ((φ + t • ψ) ∘ e.symm) z =
      ddbar (φ ∘ e.symm) z + t • ddbar (ψ ∘ e.symm) z
    exact hlocal
  have hEq : (fun t : ℝ ↦ ω₀.mongeAmpere (φ + t • ψ) x) =
      fun t ↦ relDet (ω₀ x) ((ω₀ x + mddbar n φ x) + t • mddbar n ψ x) := by
    funext t
    simp only [mongeAmpere]
    rw [hdd t]
    simp [add_assoc]
  have hlogEq : (fun t : ℝ ↦ Real.log (ω₀.mongeAmpere (φ + t • ψ) x)) =
      fun t ↦ Real.log (relDet (ω₀ x)
        ((ω₀ x + mddbar n φ x) + t • mddbar n ψ x)) := by
    funext t
    rw [congrFun hEq t]
  rw [hlogEq]
  simpa using
    (hasDerivAt_log_relDet (ω₀.isPositive x) hx
      (α := ω₀ x + mddbar n φ x) (β := mddbar n ψ x))

/-- Segment formula: `MA(φ) - 1 = ∫₀¹ (ω_s)ⁿ/ω₀ⁿ · tr_{ω_s} (i∂∂̄φ) ds`, `ω_s = ω₀ + s i∂∂̄φ`.
For `s ∈ [0, 1]`, `ω_s = ω₀.perturb (s • φ) _` is Kähler (`IsPotential.smul`) and the integrand
is `MA(sφ) Δ_{ω_s} φ`. -/
private theorem intervalIntegral_ftc_real
    {f f' : ℝ → ℝ} {a b : ℝ}
    (hderiv : ∀ s ∈ Set.uIcc a b, HasDerivAt f (f' s) s)
    (hint : IntervalIntegrable f' (MeasureTheory.volume : Measure ℝ) a b) :
    ∫ s in a..b, f' s = f b - f a := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

open scoped ComplexOrder in
private theorem mongeAmpere_segment_ftc (hφ : ω₀.IsPotential φ) (x : M)
    (hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ ↦ ω₀.mongeAmpere (t • φ) x)
        (relDet (ω₀ x) (ω₀ x + s • mddbar n φ x) *
          relTrace (ω₀ x + s • mddbar n φ x) (mddbar n φ x)) s) :
    ω₀.mongeAmpere φ x - 1 = ∫ s in (0 : ℝ)..1,
      relDet (ω₀ x) (ω₀ x + s • mddbar n φ x) *
        relTrace (ω₀ x + s • mddbar n φ x) (mddbar n φ x) := by
  let g : ℝ → ℝ := fun s ↦
    relDet (ω₀ x) (ω₀ x + s • mddbar n φ x) *
      relTrace (ω₀ x + s • mddbar n φ x) (mddbar n φ x)
  let A : ℝ → Matrix (Fin n) (Fin n) ℂ :=
    fun s ↦ coeffMatrix (ω₀ x + s • mddbar n φ x)
  let B : Matrix (Fin n) (Fin n) ℂ := coeffMatrix (mddbar n φ x)
  have hA_eq : A = fun s ↦ coeffMatrix (ω₀ x) + s • B := by
    funext s
    simp [A, B]
  have hAcont : Continuous A := by
    rw [hA_eq]
    fun_prop
  have hdetcont : Continuous (fun s ↦ (A s).det) := by fun_prop
  have hdet_ne : ∀ s ∈ Set.Icc (0 : ℝ) 1, (A s).det ≠ 0 := by
    intro s hs
    have hpot : ω₀.IsPotential (s • φ) := hφ.smul hs.1 hs.2
    have hcoeff : coeffMatrix (ω₀ x + s • mddbar n φ x) =
        coeffMatrix ((ω₀.toFormField + mddbar n (s • φ)) x) := by
      simp [mddbar_smul hφ.1 s, Pi.add_apply]
    have hpos : (RCLike.re (A s).det) > 0 := by
      change RCLike.re (coeffMatrix (ω₀ x + s • mddbar n φ x)).det > 0
      rw [hcoeff]
      exact (RCLike.pos_iff.1 ((isPositive_iff (α :=
        (ω₀.toFormField + mddbar n (s • φ)) x)).mp (hpot.2 x)).2.det_pos).1
    intro hzero
    have hre : RCLike.re (A s).det = 0 := by rw [hzero]; simp
    linarith
  have hinvdet : ContinuousOn (fun s ↦ ((A s).det)⁻¹) (Set.Icc (0 : ℝ) 1) :=
    hdetcont.continuousOn.inv₀ hdet_ne
  have hadjcont : Continuous (fun s ↦ (A s).adjugate) := by fun_prop
  have hAinv_eq : (fun s ↦ (A s)⁻¹) =
      fun s ↦ ((A s).det)⁻¹ • (A s).adjugate := by
    funext s
    rw [Matrix.inv_def, Ring.inverse_eq_inv]
  have hAinvcont : ContinuousOn (fun s ↦ (A s)⁻¹) (Set.Icc (0 : ℝ) 1) := by
    rw [hAinv_eq]
    exact hinvdet.smul hadjcont.continuousOn
  have hgcont : ContinuousOn g (Set.Icc (0 : ℝ) 1) := by
    change ContinuousOn
      (fun s ↦ (RCLike.re (A s).det / RCLike.re (coeffMatrix (ω₀ x)).det) *
        RCLike.re ((A s)⁻¹ * B).trace)
      (Set.Icc (0 : ℝ) 1)
    have hmul : ContinuousOn (fun s ↦ (A s)⁻¹ * B) (Set.Icc (0 : ℝ) 1) := by
      exact hAinvcont.mul continuousOn_const
    fun_prop
  have hgint : IntervalIntegrable g (MeasureTheory.volume : Measure ℝ) 0 1 := by
    exact hgcont.intervalIntegrable_of_Icc (by norm_num)
  simpa [g, mongeAmpere_zero] using
    (intervalIntegral_ftc_real (f := fun t ↦ ω₀.mongeAmpere (t • φ) x)
      (f' := g) hderiv hgint).symm

theorem mongeAmpere_sub_one_eq_integral (hφ : ω₀.IsPotential φ) (x : M) :
    ω₀.mongeAmpere φ x - 1 = ∫ s in (0 : ℝ)..1,
      relDet (ω₀ x) (ω₀ x + s • mddbar n φ x) *
        relTrace (ω₀ x + s • mddbar n φ x) (mddbar n φ x) := by
  let g : ℝ → ℝ := fun s ↦
    relDet (ω₀ x) (ω₀ x + s • mddbar n φ x) *
      relTrace (ω₀ x + s • mddbar n φ x) (mddbar n φ x)
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ ↦ ω₀.mongeAmpere (t • φ) x) (g s) s := by
    intro s hs
    rcases hs with ⟨hsmin, hsmax⟩
    have hs0 : 0 ≤ s := by simpa [min_eq_left zero_le_one] using hsmin
    have hs1 : s ≤ 1 := by simpa [max_eq_right zero_le_one] using hsmax
    have hpot : ω₀.IsPotential (s • φ) := hφ.smul hs0 hs1
    have hbase := hasDerivAt_mongeAmpere hpot hφ.1 x
    have hshift := HasDerivAt.comp_of_eq s hbase ((hasDerivAt_id s).sub_const s) (by simp)
    have hfun : (fun t : ℝ ↦ ω₀.mongeAmpere (s • φ + (t - s) • φ) x) =
        fun t ↦ ω₀.mongeAmpere (t • φ) x := by
      funext t
      congr 1
      ext u
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [← hfun]
    simpa [g, mongeAmpere, laplacian, perturb_apply, mddbar_smul hφ.1 s,
      add_assoc, Pi.smul_apply, Function.comp_def] using hshift
  exact mongeAmpere_segment_ftc hφ x hderiv

/-! ### Volume -/

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [SigmaCompactSpace M]

/-- `(ω₀ + i∂∂̄φ)ⁿ = MA(φ) ω₀ⁿ` as measures. -/
theorem volume_perturb (hφ : ω₀.IsPotential φ) :
    (ω₀.perturb φ hφ).volume =
      ω₀.volume.withDensity fun x ↦ ENNReal.ofReal (ω₀.mongeAmpere φ x) := by
  rw [volume_eq_withDensity_relDet (ω₀ := ω₀) (ω₁ := ω₀.perturb φ hφ)]
  congr 1

private theorem segment_laplacian_integral_zero [CompactSpace M]
    (hφ : ω₀.IsPotential φ) {s : ℝ} (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) :
    ∫ x, relDet (ω₀ x) (ω₀ x + s • mddbar n φ x) *
      relTrace (ω₀ x + s • mddbar n φ x) (mddbar n φ x) ∂ω₀.volume = 0 := by
  have hsφ : ω₀.IsPotential (s • φ) := hφ.smul hs₀ hs₁
  let ωs := ω₀.perturb (s • φ) hsφ
  have hmeas : Measurable fun x ↦ ENNReal.ofReal (ω₀.mongeAmpere (s • φ) x) :=
    ENNReal.measurable_ofReal.comp (contMDiff_mongeAmpere hsφ.1).continuous.measurable
  have htop : ∀ᵐ x ∂ω₀.volume, ENNReal.ofReal (ω₀.mongeAmpere (s • φ) x) < ⊤ :=
    Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top
  have hvol : (ω₀.perturb (s • φ) hsφ).volume =
      ω₀.volume.withDensity fun x ↦ ENNReal.ofReal (ω₀.mongeAmpere (s • φ) x) :=
    volume_perturb hsφ
  calc
    _ = ∫ x, (ENNReal.ofReal (ω₀.mongeAmpere (s • φ) x)).toReal •
        ωs.laplacian φ x ∂ω₀.volume := by
      apply integral_congr_ae
      filter_upwards with x
      have hform : ωs x = ω₀ x + s • mddbar n φ x := by
        simp [ωs, KahlerForm.perturb, mddbar_smul hφ.1 s]
      have hMA : ω₀.mongeAmpere (s • φ) x = relDet (ω₀ x) (ωs x) := by
        rw [KahlerForm.mongeAmpere, mddbar_smul hφ.1 s]
        simp only [Pi.smul_apply]
        rw [← hform]
      rw [KahlerForm.laplacian, ← hform, hMA]
      rw [ENNReal.toReal_ofReal (relDet_pos (ω₀.isPositive x) (ωs.isPositive x)).le]
      simp only [smul_eq_mul]
    _ = ∫ x, ωs.laplacian φ x ∂(ω₀.perturb (s • φ) hsφ).volume := by
      symm
      calc
        ∫ x, ωs.laplacian φ x ∂(ω₀.perturb (s • φ) hsφ).volume =
            ∫ x, ωs.laplacian φ x ∂
              (ω₀.volume.withDensity fun x ↦ ENNReal.ofReal (ω₀.mongeAmpere (s • φ) x)) :=
          congrArg (fun μ : Measure M ↦ ∫ x, ωs.laplacian φ x ∂μ) hvol
        _ = ∫ x, (ENNReal.ofReal (ω₀.mongeAmpere (s • φ) x)).toReal •
              ωs.laplacian φ x ∂ω₀.volume :=
          integral_withDensity_eq_integral_toReal_smul hmeas htop _
    _ = 0 := ωs.integral_laplacian hφ.1

private theorem interval_product_integrable_of_continuous_bounded
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [BorelSpace (ℝ × X)] {μ : MeasureTheory.Measure X} [MeasureTheory.IsFiniteMeasure μ]
    {f : ℝ → X → ℝ} (hf : Continuous (Function.uncurry f))
    (hbound : ∃ C : ℝ, ∀ s ∈ Set.uIoc (0 : ℝ) 1, ∀ x, f s x ∈ Set.Icc (-C) C) :
    MeasureTheory.Integrable (Function.uncurry f)
      ((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)).prod μ) := by
  let ν := (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)).prod μ
  obtain ⟨C, hC⟩ := hbound
  have hvol : MeasureTheory.volume (Set.uIoc (0 : ℝ) 1) < ⊤ := by
    have hsubset : Set.uIoc (0 : ℝ) 1 ⊆ Set.Icc 0 1 := by
      simpa using (Set.uIoc_subset_uIcc (a := (0 : ℝ)) (b := 1))
    calc
      MeasureTheory.volume (Set.uIoc (0 : ℝ) 1) ≤ MeasureTheory.volume (Set.Icc 0 1) :=
        MeasureTheory.measure_mono hsubset
      _ = ENNReal.ofReal (1 - 0) := by rw [Real.volume_Icc]
      _ < ⊤ := ENNReal.ofReal_lt_top
  let hVolFact : Fact (MeasureTheory.volume (Set.uIoc (0 : ℝ) 1) < ⊤) := ⟨hvol⟩
  have hFinite : MeasureTheory.IsFiniteMeasure ν := by
    dsimp [ν]
    infer_instance
  have hfmeas : AEMeasurable (Function.uncurry f) ν := hf.measurable.aemeasurable
  have hset : MeasurableSet {z : ℝ × X | Function.uncurry f z ∈ Set.Icc (-C) C} :=
    isClosed_Icc.measurableSet.preimage hf.measurable
  have hboundAE : ∀ᵐ z ∂ν, Function.uncurry f z ∈ Set.Icc (-C) C := by
    rw [MeasureTheory.Measure.ae_prod_iff_ae_ae hset]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with s hs
    exact Filter.Eventually.of_forall fun x ↦ hC s hs x
  exact MeasureTheory.Integrable.of_mem_Icc (-C) C hfmeas hboundAE

private theorem interval_product_integrable_of_continuous
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [BorelSpace (ℝ × X)] [CompactSpace X] {μ : MeasureTheory.Measure X}
    [MeasureTheory.IsFiniteMeasure μ] {f : ℝ → X → ℝ}
    (hf : Continuous (Function.uncurry f)) :
    MeasureTheory.Integrable (Function.uncurry f)
      ((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)).prod μ) := by
  have hcompact : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set X)) :=
    isCompact_Icc.prod isCompact_univ
  obtain ⟨C, hC⟩ := (hcompact.image_of_continuousOn hf.continuousOn).isBounded.exists_norm_le
  have hsubset : Set.uIoc (0 : ℝ) 1 ⊆ Set.Icc 0 1 := by
    simpa using (Set.uIoc_subset_uIcc (a := (0 : ℝ)) (b := 1))
  have hbound : ∀ s ∈ Set.uIoc (0 : ℝ) 1, ∀ x, f s x ∈ Set.Icc (-C) C := by
    intro s hs x
    have hs' := hsubset hs
    have himage : Function.uncurry f (s, x) ∈
        Function.uncurry f '' (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set X)) :=
      ⟨(s, x), ⟨hs', Set.mem_univ x⟩, rfl⟩
    have hnorm := hC (f s x) himage
    have habs : |f s x| ≤ C := by simpa [Real.norm_eq_abs] using hnorm
    exact abs_le.mp habs
  exact interval_product_integrable_of_continuous_bounded hf ⟨C, hbound⟩

private theorem integral_mongeAmpere_eq_volume_mass [CompactSpace M]
    (hφ : ω₀.IsPotential φ) :
    ∫ x, ω₀.mongeAmpere φ x ∂ω₀.volume = (ω₀.perturb φ hφ).volume.real univ := by
  let f := ω₀.mongeAmpere φ
  have hfcont : Continuous f := (contMDiff_mongeAmpere hφ.1).continuous
  have hfint : Integrable f ω₀.volume :=
    hfcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have hfnn : 0 ≤ᵐ[ω₀.volume] f :=
    Filter.Eventually.of_forall fun x ↦ (mongeAmpere_pos hφ x).le
  have hreal : ENNReal.ofReal (∫ x, f x ∂ω₀.volume) =
      ∫⁻ x, ENNReal.ofReal (f x) ∂ω₀.volume :=
    ofReal_integral_eq_lintegral_ofReal hfint hfnn
  have hmass : (ω₀.perturb φ hφ).volume univ =
      ∫⁻ x, ENNReal.ofReal (f x) ∂ω₀.volume := by
    rw [volume_perturb hφ, withDensity_apply _ MeasurableSet.univ]
    exact setLIntegral_univ (fun x ↦ ENNReal.ofReal (f x))
  have hnonneg : 0 ≤ ∫ x, f x ∂ω₀.volume := integral_nonneg_of_ae hfnn
  calc
    ∫ x, f x ∂ω₀.volume = (ENNReal.ofReal (∫ x, f x ∂ω₀.volume)).toReal := by
      rw [ENNReal.toReal_ofReal hnonneg]
    _ = (ω₀.perturb φ hφ).volume.real univ := by
      rw [hreal, ← hmass, Measure.real_def]

/-! `∫ (ω₀ + i∂∂̄φ)ⁿ = ∫ ω₀ⁿ` on a compact manifold. -/
private theorem perturb_volume_mass_invariant [CompactSpace M] (hφ : ω₀.IsPotential φ) :
    (ω₀.perturb φ hφ).volume.real univ = ω₀.volume.real univ := by
  let t : ℝ → ℝ := fun s ↦ max 0 (min 1 s)
  have ht0 (s : ℝ) : 0 ≤ t s := le_max_left _ _
  have ht1 (s : ℝ) : t s ≤ 1 := max_le (by norm_num) (min_le_left _ _)
  have htid (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) : t s = s := by
    simp [t, hs.1, hs.2]
  let hpot (s : ℝ) := hφ.smul (ht0 s) (ht1 s)
  let ωs (s : ℝ) := ω₀.perturb (t s • φ) (hpot s)
  let F : ℝ → M → ℝ := fun s x ↦
    ω₀.mongeAmpere (t s • φ) x * (ωs s).laplacian φ x
  have htu (s : ℝ) : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (t s • φ) := by
    have hmul : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ p.1 * p.2) := contDiff_fst.mul contDiff_snd
    change ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (fun x ↦ t s * φ x)
    simpa [Function.comp_def, smul_eq_mul] using
      hmul.comp_contMDiff (contMDiff_const.prodMk_space hφ.1)
  have hHsmul (s : ℝ) (x : M) {z : EuclideanSpace ℂ (Fin n)}
      (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
      complexHessian ((t s • φ) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z =
        t s • complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z := by
    change (ddbar ((t s • φ) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z).coeffMatrix =
      t s • (ddbar (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z).coeffMatrix
    rw [← chartRep_mddbar (htu s) x hz, ← chartRep_mddbar hφ.1 x hz]
    rw [mddbar_smul hφ.1 (t s), FormField.chartRep_smul]
    simp [ContinuousAlternatingMap.coeffMatrix_smul]
  have hHcont (x : M) :
      ContinuousOn (fun z => complexHessian (φ ∘
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z)
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by
    let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
    have hrep : ContDiffOn ℝ ∞ ((mddbar n φ).chartRep x) c.target := isSmooth_mddbar hφ.1 x
    have hcoeff : Continuous fun α : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ => α.coeffMatrix := by
      fun_prop [ContinuousAlternatingMap.coeffMatrix]
    have hc : ContinuousOn (fun z => ((mddbar n φ).chartRep x z).coeffMatrix) c.target :=
      hcoeff.continuousOn.comp hrep.continuousOn (fun _ _ => Set.mem_univ _)
    refine hc.congr ?_
    intro z hz
    change (ddbar (φ ∘ c.symm) z).coeffMatrix = _
    rw [← chartRep_mddbar hφ.1 x hz]
  have hGcont (x : M) :
      ContinuousOn (ω₀.metricInChart x)
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by
    refine continuousOn_pi' ?_
    intro j
    refine continuousOn_pi' ?_
    intro k
    exact (ω₀.contDiffOn_metricInChart x j k).continuousOn
  have hmetric_path (s : ℝ) (x : M) {z : EuclideanSpace ℂ (Fin n)}
      (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
      (ωs s).metricInChart x z = ω₀.metricInChart x z +
        t s • complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z := by
    rw [KahlerForm.metricInChart_perturb (hpot s) x hz, hHsmul s x hz]
  have hFchart (s : ℝ) (x₀ y : M)
      (hy : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).source) :
      F s y =
        (RCLike.re ((ωs s).metricInChart x₀
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀ y)).det /
          RCLike.re (ω₀.metricInChart x₀
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀ y)).det) *
        RCLike.re ((((ωs s).metricInChart x₀
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀ y))⁻¹ *
          complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm)
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀ y)).trace) := by
    have hyE : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).source := by
      simpa only [extChartAt_source] using hy
    dsimp [F, ωs]
    rw [mongeAmpere_eq_inChart (htu s) x₀ hy,
      (ωs s).laplacian_eq_inChart hφ.1 x₀ hy,
      ← KahlerForm.metricInChart_perturb (hpot s) x₀
        ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).map_source hyE)]
    rw [extChartAt_coe, extChartAt_coe_symm]
    simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_apply,
      Function.comp_id, id_eq]
    dsimp [ωs]
  have htcont : Continuous t := by
    change Continuous (fun s : ℝ ↦ max 0 (min 1 s))
    fun_prop
  have hAcont (x₀ : M) :
      ContinuousOn (fun p : ℝ × EuclideanSpace ℂ (Fin n) ↦
        ω₀.metricInChart x₀ p.2 + t p.1 •
          complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm) p.2)
        (Set.univ ×ˢ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).target) := by
    have hg : ContinuousOn (fun p : ℝ × EuclideanSpace ℂ (Fin n) =>
        ω₀.metricInChart x₀ p.2)
        (Set.univ ×ˢ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).target) :=
      (hGcont x₀).comp continuousOn_snd (fun p hp => hp.2)
    have hh : ContinuousOn (fun p : ℝ × EuclideanSpace ℂ (Fin n) =>
        complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm) p.2)
        (Set.univ ×ˢ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).target) :=
      (hHcont x₀).comp continuousOn_snd (fun p hp => hp.2)
    have ht : ContinuousOn (fun p : ℝ × EuclideanSpace ℂ (Fin n) => t p.1)
        (Set.univ ×ˢ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).target) :=
      htcont.continuousOn.comp continuousOn_fst (fun _ _ => Set.mem_univ _)
    exact hg.add (ht.smul hh)
  have hApath_cont (x₀ : M) :
      ContinuousOn (fun p : ℝ × EuclideanSpace ℂ (Fin n) =>
        (ωs p.1).metricInChart x₀ p.2)
        (Set.univ ×ˢ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).target) := by
    refine (hAcont x₀).congr ?_
    rintro ⟨s, z⟩ ⟨_, hz⟩
    exact hmetric_path s x₀ hz
  let Q : M → (ℝ × EuclideanSpace ℂ (Fin n)) → ℝ := fun x₀ p ↦
    (RCLike.re ((ωs p.1).metricInChart x₀ p.2).det /
      RCLike.re (ω₀.metricInChart x₀ p.2).det) *
      RCLike.re (((ωs p.1).metricInChart x₀ p.2)⁻¹ *
        complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm) p.2).trace
  have hQcont (x₀ : M) :
      ContinuousOn (Q x₀)
        (Set.univ ×ˢ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).target) := by
    let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀
    let S : Set (ℝ × EuclideanSpace ℂ (Fin n)) := (Set.univ : Set ℝ) ×ˢ c.target
    let A : ℝ × EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
      fun p ↦ (ωs p.1).metricInChart x₀ p.2
    have hA : ContinuousOn A S := by
      change ContinuousOn (fun p : ℝ × EuclideanSpace ℂ (Fin n) =>
        (ωs p.1).metricInChart x₀ p.2)
        (Set.univ ×ˢ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).target)
      exact hApath_cont x₀
    have hH : ContinuousOn (fun p : ℝ × EuclideanSpace ℂ (Fin n) =>
        complexHessian (φ ∘ c.symm) p.2) S :=
      (hHcont x₀).comp continuousOn_snd (fun _ hp => hp.2)
    have hG : ContinuousOn (fun p : ℝ × EuclideanSpace ℂ (Fin n) =>
        ω₀.metricInChart x₀ p.2) S :=
      (hGcont x₀).comp continuousOn_snd (fun _ hp => hp.2)
    have hdetA : ContinuousOn (fun p => (A p).det) S := by fun_prop
    have hdetG : ContinuousOn (fun p => (ω₀.metricInChart x₀ p.2).det) S := by fun_prop
    have hdetAinv : ContinuousOn (fun p => ((A p).det)⁻¹) S := by
      apply hdetA.inv₀
      rintro ⟨s, z⟩ ⟨_, hz⟩
      have hvol := (ωs s).volumeDensityInChart_pos x₀ hz
      dsimp [KahlerForm.volumeDensityInChart] at hvol
      have hpos : 0 < RCLike.re (A (s, z)).det := by
        simpa [A] using
          ((mul_pos_iff_of_pos_left (by positivity : 0 < (2 : ℝ) ^ n)).mp hvol)
      intro hdet
      rw [hdet] at hpos
      norm_num at hpos
    have hAdj : ContinuousOn (fun p => (A p).adjugate) S := by fun_prop
    have hAinv : ContinuousOn (fun p => (A p)⁻¹) S := by
      have h := hdetAinv.smul hAdj
      convert h using 1
      ext p i j
      simp [Matrix.inv_def]
    have htrace : ContinuousOn (fun p =>
        RCLike.re (((A p)⁻¹ * (fun z => complexHessian (φ ∘ c.symm) z) p.2).trace)) S := by
      have hm := hAinv.mul hH
      fun_prop
    have hnum : ContinuousOn (fun p => RCLike.re (A p).det) S := by fun_prop
    have hden : ContinuousOn (fun p => RCLike.re (ω₀.metricInChart x₀ p.2).det) S := by fun_prop
    have hdenNe : ∀ p ∈ S, RCLike.re (ω₀.metricInChart x₀ p.2).det ≠ 0 := by
      rintro ⟨s, z⟩ ⟨_, hz⟩
      have h := ω₀.volumeDensityInChart_pos x₀ hz
      dsimp [KahlerForm.volumeDensityInChart] at h
      exact ne_of_gt ((mul_pos_iff_of_pos_left (by positivity : 0 < (2 : ℝ) ^ n)).mp h)
    have hdenInv : ContinuousOn
        (fun p => (RCLike.re (ω₀.metricInChart x₀ p.2).det)⁻¹) S := hden.inv₀ hdenNe
    have hratio : ContinuousOn (fun p => RCLike.re (A p).det *
        (RCLike.re (ω₀.metricInChart x₀ p.2).det)⁻¹) S := hnum.mul hdenInv
    change ContinuousOn (fun p =>
      RCLike.re (A p).det / RCLike.re (ω₀.metricInChart x₀ p.2).det *
        RCLike.re ((A p)⁻¹ * complexHessian (φ ∘ c.symm) p.2).trace) S
    have hprod := hratio.mul htrace
    convert hprod using 1
    ext p
    simp only [Pi.mul_apply, div_eq_mul_inv]
  have hFcont : Continuous (Function.uncurry F) := by
    rw [continuous_iff_continuousAt]
    intro p
    rcases p with ⟨s₀, x₀⟩
    let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀
    have hqOpen : IsOpen (Set.univ ×ˢ c.target) :=
      (isOpen_prod_iff' (s := (Set.univ : Set ℝ)) (t := c.target)).2
        (Or.inl ⟨isOpen_univ,
          isOpen_extChartAt_target (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x₀⟩)
    have hqmem : Set.univ ×ˢ c.target ∈ nhds (s₀, c x₀) :=
      hqOpen.mem_nhds ⟨Set.mem_univ _,
        mem_extChartAt_target (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x₀⟩
    have hq : ContinuousAt (Q x₀) (s₀, c x₀) := (hQcont x₀).continuousAt hqmem
    have hcomp : ContinuousAt (fun p : ℝ × M => Q x₀ (p.1, c p.2)) (s₀, x₀) :=
      hq.comp₂ continuousAt_fst
        ((continuousAt_extChartAt (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x₀).comp
          continuousAt_snd)
    have hsourceOpen : IsOpen (Set.univ ×ˢ c.source) :=
      (isOpen_prod_iff' (s := (Set.univ : Set ℝ)) (t := c.source)).2
        (Or.inl ⟨isOpen_univ,
          isOpen_extChartAt_source (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x₀⟩)
    have hsource : Set.univ ×ˢ c.source ∈ nhds (s₀, x₀) :=
      hsourceOpen.mem_nhds ⟨Set.mem_univ _,
        mem_extChartAt_source (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x₀⟩
    have heq : Function.uncurry F =ᶠ[nhds (s₀, x₀)]
        (fun p : ℝ × M => Q x₀ (p.1, c p.2)) := by
      filter_upwards [hsource] with p hp
      rcases p with ⟨s, y⟩
      have hy : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).source := by
        simpa [c, extChartAt_source] using hp.2
      change F s y = Q x₀ (s, c y)
      have hr : (chartAt (EuclideanSpace ℂ (Fin n)) x₀).symm
          ((chartAt (EuclideanSpace ℂ (Fin n)) x₀) y) = y :=
        (chartAt (EuclideanSpace ℂ (Fin n)) x₀).left_inv hy
      simpa [Q, c, hr] using hFchart s x₀ y hy
    exact hcomp.congr_of_eventuallyEq heq
  have hFint : MeasureTheory.Integrable (Function.uncurry F)
      ((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)).prod ω₀.volume) :=
    interval_product_integrable_of_continuous hFcont
  have hFseg (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (x : M) :
      F s x = relDet (ω₀ x) (ω₀ x + s • mddbar n φ x) *
        relTrace (ω₀ x + s • mddbar n φ x) (mddbar n φ x) := by
    have hform : (ωs s) x = ω₀ x + s • mddbar n φ x := by
      simp [ωs, KahlerForm.perturb, htid s hs, mddbar_smul hφ.1 s]
    dsimp [F]
    rw [htid s hs, KahlerForm.mongeAmpere, mddbar_smul hφ.1 s]
    simp only [Pi.smul_apply]
    rw [KahlerForm.laplacian, hform]
  have hsegment (x : M) : ω₀.mongeAmpere φ x - 1 = ∫ s in (0 : ℝ)..1,
      relDet (ω₀ x) (ω₀ x + s • mddbar n φ x) *
        relTrace (ω₀ x + s • mddbar n φ x) (mddbar n φ x) :=
    mongeAmpere_sub_one_eq_integral hφ x
  have hdiff : ∫ x, ω₀.mongeAmpere φ x - 1 ∂ω₀.volume = 0 := by
    calc
      _ = ∫ x, ∫ s in (0 : ℝ)..1, F s x ∂(MeasureTheory.volume : Measure ℝ)
          ∂ω₀.volume := by
        apply integral_congr_ae
        filter_upwards with x
        rw [hsegment x]
        apply intervalIntegral.integral_congr
        intro s hs
        have hs01 : s ∈ Set.Icc (0 : ℝ) 1 := by simpa using hs
        exact (hFseg s hs01 x).symm
      _ = ∫ s in (0 : ℝ)..1, ∫ x, F s x ∂ω₀.volume :=
        (MeasureTheory.intervalIntegral_integral_swap (f := F) hFint).symm
      _ = 0 := by
        calc
          ∫ s in (0 : ℝ)..1, ∫ x, F s x ∂ω₀.volume =
              ∫ s in (0 : ℝ)..1, (0 : ℝ) := intervalIntegral.integral_congr (by
                intro s hs
                have hs01 : s ∈ Set.Icc (0 : ℝ) 1 := by simpa using hs
                calc
                  ∫ x, F s x ∂ω₀.volume = ∫ x,
                      relDet (ω₀ x) (ω₀ x + s • mddbar n φ x) *
                        relTrace (ω₀ x + s • mddbar n φ x) (mddbar n φ x) ∂ω₀.volume := by
                    apply integral_congr_ae
                    exact Filter.Eventually.of_forall (hFseg s hs01)
          _ = 0 := segment_laplacian_integral_zero hφ hs01.1 hs01.2)
          _ = 0 := by simp
  have hmass_int : ∫ x, ω₀.mongeAmpere φ x ∂ω₀.volume = ∫ x, (1 : ℝ) ∂ω₀.volume := by
    have h := hdiff
    have hfcont : Continuous (ω₀.mongeAmpere φ) := (contMDiff_mongeAmpere hφ.1).continuous
    have hfint : Integrable (ω₀.mongeAmpere φ) ω₀.volume :=
      hfcont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace (ω₀.mongeAmpere φ))
    rw [integral_sub hfint (integrable_const 1)] at h
    linarith
  calc
    (ω₀.perturb φ hφ).volume.real univ = ∫ x, ω₀.mongeAmpere φ x ∂ω₀.volume :=
      (integral_mongeAmpere_eq_volume_mass hφ).symm
    _ = ∫ x, (1 : ℝ) ∂ω₀.volume := hmass_int
    _ = ω₀.volume.real univ := by
      rw [integral_const, smul_eq_mul, mul_one]

private theorem integral_mongeAmpere_of_volume_mass_invariant [CompactSpace M]
    (hφ : ω₀.IsPotential φ)
    (hvol : (ω₀.perturb φ hφ).volume.real univ = ω₀.volume.real univ) :
    ∫ x, ω₀.mongeAmpere φ x ∂ω₀.volume = ω₀.volume.real univ := by
  calc
    ∫ x, ω₀.mongeAmpere φ x ∂ω₀.volume =
        (ω₀.perturb φ hφ).volume.real univ := integral_mongeAmpere_eq_volume_mass hφ
    _ = ω₀.volume.real univ := hvol

theorem integral_mongeAmpere [CompactSpace M] (hφ : ω₀.IsPotential φ) :
    ∫ x, ω₀.mongeAmpere φ x ∂ω₀.volume = ω₀.volume.real univ := by
  exact integral_mongeAmpere_of_volume_mass_invariant hφ (perturb_volume_mass_invariant hφ)

/-- The normalization `∫ e^G ω₀ⁿ = ∫ ω₀ⁿ` is necessary for solvability. -/
theorem SolvesMongeAmpere.integral_exp [CompactSpace M] {G : M → ℝ}
    (h : ω₀.SolvesMongeAmpere G φ) : ∫ x, Real.exp (G x) ∂ω₀.volume = ω₀.volume.real univ := by
  rw [← integral_mongeAmpere h.1]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ (h.2 x).symm)

end KahlerForm
