-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Geometry/Operator/DirectionalDerivative.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Manifold.Tensor.Coordinates.PartialDerivative
public import CalabiYau.Geometry.Manifold.Coordinates.Fields.Scalar
public import CalabiYau.Geometry.Manifold.Coordinates.Fields.Vector
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Topology.Algebra.Support
public import CalabiYau.Geometry.Manifold.Bundle.PartialMfderiv.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.Algebra.Structures
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.LineDeriv.Basic

@[expose] public section


noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff Matrix

namespace CalabiYau.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

export CalabiYau.Tensor.Coordinates
  (chartCoeff chartCoeff_contMDiffOn chartCoeff_def chartCoeff_recompose chartCoeffOnE
    chartCoeffOnE_contDiffOn extChartAt_source_eq_chartAt_source scalarOnE scalarOnE_contDiffOn
    scalarOnE_contDiffWithinAt scalarOnE_def scalarOnE_extChartAt
    trivializationAt_baseSet_eq_chartAt_source)

def tangentSectionAction
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (f : M → ℝ) : M → ℝ :=
  fun x => mfderiv I 𝓘(ℝ) f x (X x)

omit [Module.Finite ℝ E] in
lemma tangentSectionAction_def
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (f : M → ℝ) (x : M) :
    tangentSectionAction (I := I) X f x = mfderiv I 𝓘(ℝ) f x (X x) := rfl

def chartPullZero (α : M) (f : M → ℝ) : E → ℝ :=
  (extChartAt I α).target.indicator (scalarOnE (I := I) α f)

lemma mfderiv_chartBasisVecFiber (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {x : M} (hx : x ∈ (chartAt H α).source)
    (hx_int : extChartAt I α x ∈ interior (extChartAt I α).target)
    (i : Fin (Module.finrank ℝ E)) :
    mfderiv I 𝓘(ℝ) f x
        (CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x)
      = CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x) := by
  classical
  set φ := extChartAt I α
  have hxsrc : x ∈ φ.source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
  have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]; exact hx
  have hf_mdiff_at : MDifferentiableAt I 𝓘(ℝ) f x := hf.mdifferentiableAt (by simp)
  have hscalar_smooth :=
    scalarOnE_contDiffOn (I := I) α hf
  have hint_open : IsOpen (interior φ.target) := isOpen_interior
  have hsubset : interior φ.target ⊆ φ.target := interior_subset
  have hscalar_at : ContDiffAt ℝ ∞ (scalarOnE (I := I) α f) (φ x) := by
    have h_within : ContDiffWithinAt ℝ ∞
        (scalarOnE (I := I) α f) φ.target (φ x) := hscalar_smooth (φ x) (hsubset hx_int)
    exact h_within.contDiffAt (mem_nhds_iff.mpr ⟨interior φ.target, hsubset, hint_open, hx_int⟩)
  have hscalar_diff : DifferentiableAt ℝ (scalarOnE (I := I) α f) (φ x) :=
    hscalar_at.differentiableAt (by simp)
  have hcomp_eq : ∀ᶠ y in 𝓝 x, f y = (scalarOnE (I := I) α f) (φ y) := by
    have hsrc_nhd : φ.source ∈ 𝓝 x :=
      (isOpen_extChartAt_source (I := I) α).mem_nhds hxsrc
    filter_upwards [hsrc_nhd] with y hy
    rw [scalarOnE_def, φ.left_inv hy]
  set L : E →L[ℝ] ℝ := fderiv ℝ (scalarOnE (I := I) α f) (φ x)
  have hf_mfderiv := hf_mdiff_at.mfderiv
  have hcong : f =ᶠ[𝓝 x] (scalarOnE (I := I) α f) ∘ (extChartAt I α) := hcomp_eq
  have hmfderiv_cong : mfderiv I 𝓘(ℝ) f x =
      mfderiv I 𝓘(ℝ) ((scalarOnE (I := I) α f) ∘ (extChartAt I α)) x :=
    Filter.EventuallyEq.mfderiv_eq hcong
  rw [hmfderiv_cong]
  have hphi_diff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I α) x :=
    mdifferentiableAt_extChartAt (I := I) (x := α) hx
  have hg_diff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) (scalarOnE (I := I) α f) (φ x) :=
    hscalar_diff.mdifferentiableAt
  have hchain :
      mfderiv I 𝓘(ℝ) ((scalarOnE (I := I) α f) ∘ (extChartAt I α)) x =
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (scalarOnE (I := I) α f) (φ x)).comp
          (mfderiv I 𝓘(ℝ, E) (extChartAt I α) x) :=
    mfderiv_comp x hg_diff hphi_diff
  rw [hchain]
  rw [show mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (scalarOnE (I := I) α f) (φ x)
      = fderiv ℝ (scalarOnE (I := I) α f) (φ x) from
        mfderiv_eq_fderiv (𝕜 := ℝ) (f := scalarOnE (I := I) α f)]
  have hmfderiv_chartBasis :
      mfderiv I 𝓘(ℝ, E) (extChartAt I α) x
          (CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x)
        = (CalabiYau.Tensor.Coordinates.chartModelBasis E) i := by
    rw [← TangentBundle.continuousLinearMapAt_trivializationAt (𝕜 := ℝ) (I := I)
      (x₀ := α) (x := x) hx]
    set T : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)) :=
      trivializationAt E (TangentSpace I) α
    have heq : CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x = T.symm x ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i) :=
      by rw [CalabiYau.Tensor.Coordinates.chartBasisVecFiber, T.symmL_apply hbase]
    rw [heq]
    have h_apply :
        T.continuousLinearMapAt ℝ x (T.symm x ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i))
          = (CalabiYau.Tensor.Coordinates.chartModelBasis E) i := by
      have : T.symm x ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i)
            = T.symmL ℝ x ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i) := by
        rw [Bundle.Trivialization.symmL_apply T hbase]
      rw [this, Bundle.Trivialization.continuousLinearMapAt_symmL T (b := x) hbase]
    exact h_apply
  change fderiv ℝ (scalarOnE (I := I) α f) (φ x)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I α) x (CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x))
      = CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (scalarOnE (I := I) α f) (φ x)
  rw [hmfderiv_chartBasis]
  rfl

theorem tangentSectionAction_chartLocal
    (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {x : M} (hx : x ∈ (chartAt H α).source)
    (hx_int : extChartAt I α x ∈ interior (extChartAt I α).target) :
    tangentSectionAction (I := I) X f x =
      ∑ i : Fin (Module.finrank ℝ E),
        chartCoeff (I := I) α X i x *
          CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x) := by
  classical
  have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]; exact hx
  have hXrecomp : X x = ∑ i, chartCoeff (I := I) α X i x •
        CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x :=
    chartCoeff_recompose (I := I) α X hbase
  rw [tangentSectionAction_def, hXrecomp]
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [map_smul]
  rw [mfderiv_chartBasisVecFiber (I := I) α hf hx hx_int i]
  exact smul_eq_mul ..

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
lemma extChartAt_target_subset_interior_of_boundaryless [I.Boundaryless] (α : M) :
    (extChartAt I α).target ⊆ interior (extChartAt I α).target := by
  intro y hy
  exact (isOpen_extChartAt_target (I := I) α).interior_eq.symm ▸ hy

theorem tangentSectionAction_chartLocal_of_boundaryless [I.Boundaryless]
    (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {x : M} (hx : x ∈ (chartAt H α).source) :
    tangentSectionAction (I := I) X f x =
      ∑ i : Fin (Module.finrank ℝ E),
        chartCoeff (I := I) α X i x *
          CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x) := by
  have hxsrc : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
  have hx_target : extChartAt I α x ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hxsrc
  have hx_int : extChartAt I α x ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α hx_target
  exact tangentSectionAction_chartLocal (I := I) α X hf hx hx_int

omit [Module.Finite ℝ E] in
theorem tangentSectionAction_contMDiff
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) :
    ContMDiff I 𝓘(ℝ) ∞ (tangentSectionAction (I := I) X f) := by
  intro x₀
  let e₀ := trivializationAt E (TangentSpace I) x₀
  have hdf : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] ℝ) (∞ : WithTop ℕ∞)
      (inTangentCoordinates I 𝓘(ℝ) id f (mfderiv I 𝓘(ℝ) f) x₀) x₀ :=
    hf.contMDiffAt.mfderiv_const (WithTop.coe_le_coe.mpr le_top)
  have hX : ContMDiffAt I 𝓘(ℝ, E) (∞ : WithTop ℕ∞)
      (fun x => (e₀ ⟨x, X x⟩).2) x₀ :=
    (Bundle.contMDiffAt_section (n := (∞ : WithTop ℕ∞)) x₀).mp X.contMDiff.contMDiffAt
  refine (hdf.clm_apply hX).congr_of_eventuallyEq ?_
  filter_upwards
    [e₀.open_baseSet.mem_nhds (mem_baseSet_trivializationAt E (TangentSpace I) x₀)]
  intro x hx
  simp only [inTangentCoordinates, ContinuousLinearMap.inCoordinates, Function.id_def,
    TangentBundle.continuousLinearMapAt_model_space]
  change mfderiv I 𝓘(ℝ) f x (X x) =
    mfderiv I 𝓘(ℝ) f x (e₀.symmL ℝ x ((e₀ ⟨x, X x⟩).2))
  congr 1
  rw [e₀.symmL_apply hx]
  exact (Bundle.Trivialization.symm_apply_apply_mk e₀ hx (X x)).symm

end CalabiYau.DivergenceTheorem
