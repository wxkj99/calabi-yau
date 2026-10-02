-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Integration/DivergenceTheorem/Local/Formula.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Riemannian.Volume.Chart.Density
public import CalabiYau.Geometry.Riemannian.Volume.Invariance
public import CalabiYau.Geometry.Riemannian.Volume.Properties
public import CalabiYau.Geometry.Riemannian.L2.CompactSupport
public import CalabiYau.Geometry.Manifold.Tensor.Coordinates.PartialDerivative
public import CalabiYau.Geometry.Manifold.Coordinates.Fields.Vector
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace CalabiYau.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
export CalabiYau.RiemannianVolume
  (chartDensityOnE chartDensityOnE_contDiffOn)
export CalabiYau.Tensor.Coordinates
  (chartCoeff chartCoeff_contMDiffOn chartCoeff_def chartCoeff_recompose
    chartCoeffOnE chartCoeffOnE_contDiffOn)

def localDivergence (g : SmoothRiemannianMetric I M)
    (α : M) (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    M → ℝ := fun x =>
  (∑ i : Fin (Module.finrank ℝ E),
      CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i
        (fun y => chartCoeffOnE (I := I) α X i y * chartDensityOnE (I := I) g α y)
        (extChartAt I α x))
    / chartDensity (I := I) g α x

@[simp] lemma localDivergence_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    localDivergence (I := I) g α X x =
      (∑ i : Fin (Module.finrank ℝ E),
          CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i
            (fun y => chartCoeffOnE (I := I) α X i y *
                chartDensityOnE (I := I) g α y)
            (extChartAt I α x))
        / chartDensity (I := I) g α x := rfl

theorem localDivergence_eq_sum_fderiv
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {y : E} (hy : y ∈ (extChartAt I α).target) :
    localDivergence (I := I) g α X ((extChartAt I α).symm y) =
      (∑ i : Fin (Module.finrank ℝ E),
        fderiv ℝ (fun z : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          chartCoeffOnE (I := I) α X i ((toEuclidean (E := E)).symm z) *
            chartDensityOnE (I := I) g α ((toEuclidean (E := E)).symm z))
          (toEuclidean (E := E) y) (EuclideanSpace.single i 1)) /
        chartDensityOnE (I := I) g α y := by
  rw [localDivergence, (extChartAt I α).right_inv hy]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  let F : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ := fun z =>
    chartCoeffOnE (I := I) α X i ((toEuclidean (E := E)).symm z) *
      chartDensityOnE (I := I) g α ((toEuclidean (E := E)).symm z)
  have heq : (fun y => chartCoeffOnE (I := I) α X i y *
      chartDensityOnE (I := I) g α y) = F ∘ toEuclidean (E := E) := by
    ext z
    simp only [Function.comp_apply, F, ContinuousLinearEquiv.symm_apply_apply]
  rw [CalabiYau.Tensor.Coordinates.partialDeriv, heq,
    (toEuclidean (E := E)).comp_right_fderiv, ContinuousLinearMap.comp_apply,
    CalabiYau.Tensor.Coordinates.chartModelBasis_apply]
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  rfl

lemma chartCoeffOnE_mul_chartDensityOnE_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun y : E =>
        chartCoeffOnE (I := I) α X i y * chartDensityOnE (I := I) g α y)
      (extChartAt I α).target :=
  (chartCoeffOnE_contDiffOn (I := I) α X i).mul
    (chartDensityOnE_contDiffOn (I := I) g α)

private lemma partialDeriv_contDiffOn_interior
    (i : Fin (Module.finrank ℝ E)) {u : E → ℝ} {s : Set E}
    (hu : ContDiffOn ℝ ∞ u s) :
    ContDiffOn ℝ ∞ (CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i u) (interior s) := by
  have hu_int : ContDiffOn ℝ ∞ u (interior s) := hu.mono interior_subset
  have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ u) (interior s) :=
    hu_int.fderiv_of_isOpen isOpen_interior
      (by rw [ENat.coe_top_add_one])
  have hconst : ContDiffOn ℝ ∞ (fun _ : E => (CalabiYau.Tensor.Coordinates.chartModelBasis E) i)
      (interior s) := contDiffOn_const
  exact hfderiv.clm_apply hconst

lemma partialDeriv_chartCoeffOnE_mul_chartDensityOnE_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun y : E =>
        CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i
          (fun z : E =>
            chartCoeffOnE (I := I) α X i z *
              chartDensityOnE (I := I) g α z) y)
      (interior (extChartAt I α).target) :=
  partialDeriv_contDiffOn_interior i
    (chartCoeffOnE_mul_chartDensityOnE_contDiffOn (I := I) g α X i)

private def localDivergenceDomain (α : M) : Set M :=
  (extChartAt I α).source ∩
    (extChartAt I α) ⁻¹' interior (extChartAt I α).target

omit [Module.Finite ℝ E] in
private lemma localDivergenceDomain_subset_baseSet (α : M) :
    localDivergenceDomain (I := I) α ⊆
      (trivializationAt E (TangentSpace I) α).baseSet := by
  intro x hx
  rw [trivializationAt_baseSet_eq_chartAt_source (I := I)]
  rw [← extChartAt_source_eq_chartAt_source (I := I)]
  exact hx.1

private lemma localDivergence_summand_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M =>
        CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i
          (fun y : E =>
            chartCoeffOnE (I := I) α X i y *
              chartDensityOnE (I := I) g α y)
          (extChartAt I α x))
      (localDivergenceDomain (I := I) α) := by
  have hpartial : ContDiffOn ℝ ∞
      (fun y : E =>
        CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i
          (fun z : E =>
            chartCoeffOnE (I := I) α X i z *
              chartDensityOnE (I := I) g α z) y)
      (interior (extChartAt I α).target) :=
    partialDeriv_chartCoeffOnE_mul_chartDensityOnE_contDiffOn (I := I) g α X i
  have hpartialM : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (fun y : E =>
        CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i
          (fun z : E =>
            chartCoeffOnE (I := I) α X i z *
              chartDensityOnE (I := I) g α z) y)
      (interior (extChartAt I α).target) := hpartial.contMDiffOn
  have hchart : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α : M → E)
      (chartAt H α).source := contMDiffOn_extChartAt
  have hchart' : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α : M → E)
      (localDivergenceDomain (I := I) α) := by
    refine hchart.mono ?_
    intro x hx
    have h1 : x ∈ (extChartAt I α).source := hx.1
    rw [extChartAt_source_eq_chartAt_source (I := I)] at h1
    exact h1
  have hsubset : localDivergenceDomain (I := I) α ⊆
      (extChartAt I α : M → E) ⁻¹' interior (extChartAt I α).target :=
    fun _ hx => hx.2
  exact hpartialM.comp hchart' hsubset

private lemma chartDensity_contMDiffOn_localDivergenceDomain
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContMDiffOn I 𝓘(ℝ) ∞ (chartDensity (I := I) g α)
      (localDivergenceDomain (I := I) α) :=
  (chartDensity_contMDiffOn (I := I) g α).mono
    (localDivergenceDomain_subset_baseSet (I := I) α)

private lemma chartDensity_ne_zero_on_localDivergenceDomain
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∀ x ∈ localDivergenceDomain (I := I) α, chartDensity (I := I) g α x ≠ 0 :=
  fun _ hx => ne_of_gt
    (chartDensity_pos (I := I) g α
      (localDivergenceDomain_subset_baseSet (I := I) α hx))

theorem localDivergence_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiffOn I 𝓘(ℝ) ∞ (localDivergence (I := I) g α X)
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) := by
  have hnum : ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M =>
        ∑ i : Fin (Module.finrank ℝ E),
          CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i
            (fun y : E =>
              chartCoeffOnE (I := I) α X i y *
                chartDensityOnE (I := I) g α y)
            (extChartAt I α x))
      (localDivergenceDomain (I := I) α) :=
    contMDiffOn_finsetSum
      (fun i _ => localDivergence_summand_contMDiffOn (I := I) g α X i)
  have hden :
      ContMDiffOn I 𝓘(ℝ) ∞ (chartDensity (I := I) g α)
        (localDivergenceDomain (I := I) α) :=
    chartDensity_contMDiffOn_localDivergenceDomain (I := I) g α
  exact hnum.div₀ hden
    (chartDensity_ne_zero_on_localDivergenceDomain (I := I) g α)

def divergenceG (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : M → ℝ :=
  fun x => localDivergence (I := I) g x X x

@[simp] lemma divergence_g_def
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    divergenceG (I := I) g X x = localDivergence (I := I) g x X x := rfl

theorem divergence_g_chart_product
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    divergenceG (I := I) g X x =
      (∑ i : Fin (Module.finrank ℝ E),
        CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i
          (chartCoeffOnE (I := I) x X i) (extChartAt I x x)) +
        (∑ i : Fin (Module.finrank ℝ E),
          chartCoeffOnE (I := I) x X i (extChartAt I x x) *
            CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i
              (chartDensityOnE (I := I) g x) (extChartAt I x x)) /
          chartDensity (I := I) g x x := by
  classical
  set y₀ : E := extChartAt I x x with hy₀_def
  have hxsrc : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact mem_chart_source H x
  have hy₀_target : y₀ ∈ (extChartAt I x).target := by
    simp [hy₀_def]
  have htarget_nhd : (extChartAt I x).target ∈ 𝓝 y₀ :=
    (isOpen_extChartAt_target (I := I) x).mem_nhds hy₀_target
  have hbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact mem_chart_source H x
  have hρ_pos : 0 < chartDensity (I := I) g x x :=
    chartDensity_pos (I := I) g x hbase
  have hρ_ne : chartDensity (I := I) g x x ≠ 0 := ne_of_gt hρ_pos
  have hsymm : (extChartAt I x).symm y₀ = x := by
    simp [hy₀_def]
  have hρOnE :
      chartDensityOnE (I := I) g x y₀ = chartDensity (I := I) g x x := by
    change chartDensity (I := I) g x ((extChartAt I x).symm y₀) =
      chartDensity (I := I) g x x
    rw [hsymm]
  have hcoeff_diff :
      ∀ i : Fin (Module.finrank ℝ E),
        DifferentiableAt ℝ (chartCoeffOnE (I := I) x X i) y₀ := by
    intro i
    have hsmooth : ContDiffOn ℝ ∞ (chartCoeffOnE (I := I) x X i)
        (extChartAt I x).target :=
      chartCoeffOnE_contDiffOn (I := I) x X i
    exact ((hsmooth y₀ hy₀_target).contDiffAt htarget_nhd).differentiableAt
      (by simp)
  have hρ_diff :
      DifferentiableAt ℝ (chartDensityOnE (I := I) g x) y₀ := by
    have hsmooth : ContDiffOn ℝ ∞ (chartDensityOnE (I := I) g x)
        (extChartAt I x).target :=
      chartDensityOnE_contDiffOn (I := I) g x
    exact ((hsmooth y₀ hy₀_target).contDiffAt htarget_nhd).differentiableAt
      (by simp)
  have hprod :
      ∀ i : Fin (Module.finrank ℝ E),
        CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i
          (fun y : E =>
            chartCoeffOnE (I := I) x X i y *
              chartDensityOnE (I := I) g x y) y₀ =
          CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (chartCoeffOnE (I := I) x X i) y₀ *
            chartDensityOnE (I := I) g x y₀ +
          chartCoeffOnE (I := I) x X i y₀ *
            CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (chartDensityOnE (I := I) g x) y₀ := by
    intro i
    unfold CalabiYau.Tensor.Coordinates.partialDeriv
    have hmul : fderiv ℝ
        (fun y : E =>
          chartCoeffOnE (I := I) x X i y *
            chartDensityOnE (I := I) g x y) y₀ =
        chartCoeffOnE (I := I) x X i y₀ •
          fderiv ℝ (chartDensityOnE (I := I) g x) y₀ +
        chartDensityOnE (I := I) g x y₀ •
          fderiv ℝ (chartCoeffOnE (I := I) x X i) y₀ :=
      fderiv_fun_mul (hcoeff_diff i) hρ_diff
    rw [hmul]
    rw [add_apply,
      smul_apply, smul_apply]
    simp only [smul_eq_mul]
    ring
  rw [divergence_g_def, localDivergence_def]
  change
    (∑ i : Fin (Module.finrank ℝ E),
        CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i
          (fun y : E =>
            chartCoeffOnE (I := I) x X i y *
              chartDensityOnE (I := I) g x y) y₀) /
      chartDensity (I := I) g x x = _
  rw [show
      (∑ i : Fin (Module.finrank ℝ E),
        CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i
          (fun y : E =>
            chartCoeffOnE (I := I) x X i y *
              chartDensityOnE (I := I) g x y) y₀) =
        ∑ i : Fin (Module.finrank ℝ E),
          (CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (chartCoeffOnE (I := I) x X i) y₀ *
            chartDensityOnE (I := I) g x y₀ +
          chartCoeffOnE (I := I) x X i y₀ *
            CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (chartDensityOnE (I := I) g x) y₀) by
      refine Finset.sum_congr rfl ?_
      intro i _
      exact hprod i]
  rw [Finset.sum_add_distrib]
  rw [show
      (∑ i : Fin (Module.finrank ℝ E),
        CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (chartCoeffOnE (I := I) x X i) y₀ *
          chartDensityOnE (I := I) g x y₀) =
        (∑ i : Fin (Module.finrank ℝ E),
          CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (chartCoeffOnE (I := I) x X i) y₀) *
          chartDensityOnE (I := I) g x y₀ by
      rw [Finset.sum_mul]]
  rw [hρOnE]
  rw [add_div]
  rw [mul_div_assoc, div_self hρ_ne, mul_one]

end CalabiYau.DivergenceTheorem
