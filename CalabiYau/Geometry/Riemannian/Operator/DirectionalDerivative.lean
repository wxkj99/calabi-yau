-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Geometry/Operator/DirectionalDerivative.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Manifold.Tensor.Coordinates.PartialDerivative
public import CalabiYau.Geometry.Manifold.Coordinates.Fields.Scalar
public import CalabiYau.Geometry.Manifold.Coordinates.Fields.Vector
public import CalabiYau.Analysis.Calculus.ContDiff.Support
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

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

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
lemma tsupport_tangentSectionAction_subset_right
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (f : M → ℝ) :
    tsupport (tangentSectionAction (I := I) X f) ⊆ tsupport f := by
  refine closure_minimal ?_ (isClosed_tsupport f)
  intro x hx
  by_contra hnot
  have hev : f =ᶠ[𝓝 x] (fun _ : M => (0 : ℝ)) :=
    notMem_tsupport_iff_eventuallyEq.mp hnot
  have hmfderiv : mfderiv I 𝓘(ℝ) f x = 0 := by
    rw [Filter.EventuallyEq.mfderiv_eq hev, mfderiv_const]
    rfl
  apply hx
  unfold tangentSectionAction
  rw [hmfderiv]
  rfl

omit [Module.Finite ℝ E] in
@[simp] lemma tangentSectionAction_def
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (f : M → ℝ) (x : M) :
    tangentSectionAction (I := I) X f x = mfderiv I 𝓘(ℝ) f x (X x) := rfl
omit [Module.Finite ℝ E] in
theorem tangent_mul
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {f h : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hh : MDifferentiableAt I 𝓘(ℝ, ℝ) h x) :
    tangentSectionAction (I := I) X (fun y => f y * h y) x =
      f x * tangentSectionAction (I := I) X h x +
        h x * tangentSectionAction (I := I) X f x := by
  have hmul := (hf.hasMFDerivAt.mul hh.hasMFDerivAt).mfderiv
  unfold tangentSectionAction
  change (mfderiv I 𝓘(ℝ, ℝ) (f * h) x) (X x) = _
  rw [hmul]
  rfl

def chartPullZero (α : M) (f : M → ℝ) : E → ℝ :=
  (extChartAt I α).target.indicator (scalarOnE (I := I) α f)
omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
lemma chartPullZero_mem (α : M) (f : M → ℝ) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    chartPullZero (I := I) α f y = scalarOnE (I := I) α f y :=
  Set.indicator_of_mem hy _
omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
lemma chartPullZero_nmem (α : M) (f : M → ℝ) {y : E}
    (hy : y ∉ (extChartAt I α).target) :
    chartPullZero (I := I) α f y = 0 :=
  Set.indicator_of_notMem hy _

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
theorem tsupport_chartPullZero_subset_image
    (α : M) {f : M → ℝ} (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ (chartAt H α).source) :
    tsupport (chartPullZero (I := I) α f) ⊆ (extChartAt I α) '' tsupport f := by
  have hcompact : IsCompact ((extChartAt I α) '' tsupport f) :=
    hc.image_of_continuousOn ((continuousOn_extChartAt α).mono
      (by simpa only [extChartAt_source] using hs))
  apply closure_minimal _ hcompact.isClosed
  intro y hy
  by_cases hyt : y ∈ (extChartAt I α).target
  · refine ⟨(extChartAt I α).symm y, ?_, (extChartAt I α).right_inv hyt⟩
    apply subset_tsupport
    simpa only [Function.mem_support, chartPullZero_mem α f hyt, scalarOnE_def] using hy
  · exact (hy (chartPullZero_nmem α f hyt)).elim

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
theorem hasCompactSupport_chartPullZero
    (α : M) {f : M → ℝ} (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ (chartAt H α).source) :
    HasCompactSupport (chartPullZero (I := I) α f) := by
  have hcompact : IsCompact ((extChartAt I α) '' tsupport f) :=
    hc.image_of_continuousOn ((continuousOn_extChartAt α).mono
      (by simpa only [extChartAt_source] using hs))
  exact hcompact.of_isClosed_subset isClosed_closure
    (tsupport_chartPullZero_subset_image α hc hs)

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
theorem tsupport_chartPullZero_subset_target
    (α : M) {f : M → ℝ} (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ (chartAt H α).source) :
    tsupport (chartPullZero (I := I) α f) ⊆ (extChartAt I α).target := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := tsupport_chartPullZero_subset_image α hc hs hy
  exact (extChartAt I α).map_source (by simpa only [extChartAt_source] using hs hx)

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
theorem chartPullZero_contDiffOn
    {k : WithTop ℕ∞} [IsManifold I k M]
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) k f) :
    ContDiffOn ℝ k (chartPullZero (I := I) α f) (extChartAt I α).target := by
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) k
      (f ∘ (extChartAt I α).symm) (extChartAt I α).target :=
    (hf.contMDiffOn (s := univ)).comp
      (contMDiffOn_extChartAt_symm α) (fun _ _ => mem_univ _)
  exact hcomp.contDiffOn.congr (fun y hy => chartPullZero_mem α f hy)

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
theorem chartPullZero_contDiffOn_range
    {k : WithTop ℕ∞} [IsManifold I k M]
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) k f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ (chartAt H α).source) :
    ContDiffOn ℝ k (chartPullZero (I := I) α f) (Set.range I) := by
  apply ContDiffOn.contDiffOn_of_tsupport_subset
    (s := I.symm ⁻¹' (chartAt H α).target)
  · simpa only [← extChartAt_target] using chartPullZero_contDiffOn α hf
  · exact (chartAt H α).open_target.preimage I.continuous_symm
  · intro y hy
    have hyt := tsupport_chartPullZero_subset_target α hc hs hy.1
    rw [extChartAt_target] at hyt
    exact hyt.1

lemma mfderiv_chart_diff (α : M)
    {f : M → ℝ} {x : M} (hx : x ∈ (chartAt H α).source)
    (hf : DifferentiableAt ℝ (scalarOnE (I := I) α f) (extChartAt I α x))
    (i : Fin (Module.finrank ℝ E)) :
    mfderiv I 𝓘(ℝ) f x (CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x) =
      CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x) := by
  set φ := extChartAt I α
  have hxsrc : x ∈ φ.source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hx
  have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hx
  have hcomp_eq : ∀ᶠ y in 𝓝 x,
      f y = (scalarOnE (I := I) α f) (φ y) := by
    filter_upwards [(isOpen_extChartAt_source (I := I) α).mem_nhds hxsrc] with y hy
    rw [scalarOnE_def, φ.left_inv hy]
  have hcong : f =ᶠ[𝓝 x]
      (scalarOnE (I := I) α f) ∘ (extChartAt I α) := hcomp_eq
  rw [Filter.EventuallyEq.mfderiv_eq hcong]
  have hφ_diff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I α) x :=
    mdifferentiableAt_extChartAt (I := I) (x := α) hx
  have hg_diff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ)
      (scalarOnE (I := I) α f) (φ x) := hf.mdifferentiableAt
  rw [mfderiv_comp x hg_diff hφ_diff]
  rw [show mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (scalarOnE (I := I) α f) (φ x) =
      fderiv ℝ (scalarOnE (I := I) α f) (φ x) from
        mfderiv_eq_fderiv (𝕜 := ℝ) (f := scalarOnE (I := I) α f)]
  have hmfderiv_chartBasis :
      mfderiv I 𝓘(ℝ, E) (extChartAt I α) x
          (CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x) = (CalabiYau.Tensor.Coordinates.chartModelBasis E) i := by
    rw [← TangentBundle.continuousLinearMapAt_trivializationAt (𝕜 := ℝ) (I := I)
      (x₀ := α) (x := x) hx]
    set T : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)) :=
      trivializationAt E (TangentSpace I) α
    have heq : CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x =
        T.symm x ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i) := by
      rw [CalabiYau.Tensor.Coordinates.chartBasisVecFiber, T.symmL_apply hbase]
    rw [heq]
    have h_apply :
        T.continuousLinearMapAt ℝ x (T.symm x ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i)) =
          (CalabiYau.Tensor.Coordinates.chartModelBasis E) i := by
      have : T.symm x ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i) =
          T.symmL ℝ x ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i) := by
        rw [Bundle.Trivialization.symmL_apply T hbase]
      rw [this, Bundle.Trivialization.continuousLinearMapAt_symmL T (b := x) hbase]
    exact h_apply
  change fderiv ℝ (scalarOnE (I := I) α f) (φ x)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I α) x
          (CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x)) = _
  rw [hmfderiv_chartBasis]
  rfl

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

theorem tangent_chart_diff [I.Boundaryless]
    (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {f : M → ℝ} {x : M} (hx : x ∈ (chartAt H α).source)
    (hf : DifferentiableAt ℝ (chartPullZero (I := I) α f)
      (extChartAt I α x)) :
    tangentSectionAction (I := I) X f x =
      ∑ i : Fin (Module.finrank ℝ E),
        chartCoeff (I := I) α X i x *
          lineDeriv ℝ (chartPullZero (I := I) α f) (extChartAt I α x)
            ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i) := by
  classical
  have hxsrc : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hx
  have hxy : extChartAt I α x ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hxsrc
  have heq : chartPullZero (I := I) α f =ᶠ[𝓝 (extChartAt I α x)]
      scalarOnE (I := I) α f := by
    filter_upwards [(isOpen_extChartAt_target (I := I) α).mem_nhds hxy] with y hy
    exact chartPullZero_mem (I := I) α f hy
  have hscalar : DifferentiableAt ℝ (scalarOnE (I := I) α f)
      (extChartAt I α x) := hf.congr_of_eventuallyEq heq.symm
  have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hx
  have hXrecomp : X x = ∑ i, chartCoeff (I := I) α X i x •
      CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x :=
    chartCoeff_recompose (I := I) α X hbase
  rw [tangentSectionAction_def, hXrecomp, map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [map_smul, mfderiv_chart_diff (I := I) α hx hscalar i]
  unfold CalabiYau.Tensor.Coordinates.partialDeriv
  rw [← heq.fderiv_eq, ← hf.lineDeriv_eq_fderiv]
  exact smul_eq_mul ..

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

private lemma partialDeriv_scalarOnE_contDiffOn_interior
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (i : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (scalarOnE (I := I) α f))
      (interior (extChartAt I α).target) := by
  have hbase : ContDiffOn ℝ ∞
      (scalarOnE (I := I) α f) (extChartAt I α).target :=
    scalarOnE_contDiffOn (I := I) α hf
  have hbase_int : ContDiffOn ℝ ∞ (scalarOnE (I := I) α f)
      (interior (extChartAt I α).target) := hbase.mono interior_subset
  have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ (scalarOnE (I := I) α f))
      (interior (extChartAt I α).target) :=
    hbase_int.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
  have hconst : ContDiffOn ℝ ∞ (fun _ : E => (CalabiYau.Tensor.Coordinates.chartModelBasis E) i)
      (interior (extChartAt I α).target) := contDiffOn_const
  exact hfderiv.clm_apply hconst

private lemma partialDeriv_scalarOnE_comp_extChartAt_contMDiffOn
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M =>
        CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x))
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) := by
  classical
  have hpartial : ContDiffOn ℝ ∞
      (CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (scalarOnE (I := I) α f))
      (interior (extChartAt I α).target) :=
    partialDeriv_scalarOnE_contDiffOn_interior (I := I) α hf i
  have hpartialM : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (scalarOnE (I := I) α f))
      (interior (extChartAt I α).target) := hpartial.contMDiffOn
  have hchart : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α : M → E)
      (chartAt H α).source := contMDiffOn_extChartAt
  have hchart' : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α : M → E)
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) := by
    refine hchart.mono ?_
    intro x hx
    have h1 : x ∈ (extChartAt I α).source := hx.1
    rw [extChartAt_source_eq_chartAt_source (I := I)] at h1
    exact h1
  have hsubset : (extChartAt I α).source ∩
      (extChartAt I α) ⁻¹' interior (extChartAt I α).target ⊆
        (extChartAt I α : M → E) ⁻¹' interior (extChartAt I α).target :=
    fun _ hx => hx.2
  exact hpartialM.comp hchart' hsubset

theorem tangentSectionAction_contMDiffOn
    (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) :
    ContMDiffOn I 𝓘(ℝ) ∞ (tangentSectionAction (I := I) X f)
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) := by
  set U : Set M := (extChartAt I α).source ∩
      (extChartAt I α) ⁻¹' interior (extChartAt I α).target with hU_def
  have hcongr : ∀ x ∈ U,
      tangentSectionAction (I := I) X f x =
        ∑ i : Fin (Module.finrank ℝ E),
          chartCoeff (I := I) α X i x *
            CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x) := by
    intro x hx
    have hx_chart : x ∈ (chartAt H α).source := by
      have := hx.1
      rw [extChartAt_source_eq_chartAt_source (I := I)] at this
      exact this
    exact tangentSectionAction_chartLocal (I := I) α X hf hx_chart hx.2
  refine ContMDiffOn.congr ?_ hcongr
  refine contMDiffOn_finsetSum (fun i _ => ?_)
  refine ContMDiffOn.mul ?_ ?_
  · have h1 : ContMDiffOn I 𝓘(ℝ) ∞ (chartCoeff (I := I) α X i)
        (trivializationAt E (TangentSpace I) α).baseSet :=
      chartCoeff_contMDiffOn (I := I) α X i
    refine h1.mono ?_
    intro x hx
    rw [trivializationAt_baseSet_eq_chartAt_source]
    have := hx.1
    rw [extChartAt_source_eq_chartAt_source (I := I)] at this
    exact this
  · exact partialDeriv_scalarOnE_comp_extChartAt_contMDiffOn (I := I) α hf i

theorem tangentSectionAction_contMDiffOn_baseSet [I.Boundaryless]
    (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) :
    ContMDiffOn I 𝓘(ℝ) ∞ (tangentSectionAction (I := I) X f)
      (chartAt H α).source := by
  refine (tangentSectionAction_contMDiffOn (I := I) α X hf).mono ?_
  intro x hx
  refine ⟨?_, ?_⟩
  · rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
  · rw [show (extChartAt I α : M → E) ⁻¹' interior (extChartAt I α).target =
          (extChartAt I α : M → E) ⁻¹' (extChartAt I α).target from ?_]
    · exact (extChartAt I α).map_source
        (by rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx)
    · congr 1
      exact (isOpen_extChartAt_target (I := I) α).interior_eq

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

omit [Module.Finite ℝ E] in
theorem mfderiv_eq_fderivWithin_scalarOnE
    (α : M) {f : M → ℝ} {x : M}
    (hx : x ∈ (chartAt H α).source) (hf : MDifferentiableAt I 𝓘(ℝ) f x)
    (v : TangentSpace I x) :
    mfderiv I 𝓘(ℝ) f x v =
      fderivWithin ℝ (scalarOnE (I := I) α f) (extChartAt I α).target (extChartAt I α x)
        ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x v) := by
  have hxs : x ∈ (extChartAt I α).source := by rwa [extChartAt_source]
  have hxt := (extChartAt I α).map_source hxs
  have hinv := (extChartAt I α).left_inv hxs
  have hs := mdifferentiableWithinAt_extChartAt_symm (I := I) hxt
  have hchain := mfderiv_comp_mfderivWithin_of_eq hf hs
    (I.uniqueMDiffOn (extChartAt I α x) (extChartAt_target_subset_range α hxt)) hinv
  rw [mfderivWithin_eq_fderivWithin] at hchain
  rw [fderivWithin_congr_set (extChartAt_target_eventuallyEq_of_mem hxt)]
  change mfderiv I 𝓘(ℝ) f x v =
    fderivWithin ℝ (f ∘ (extChartAt I α).symm) (Set.range I) (extChartAt I α x)
      ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x v)
  rw [hchain]
  change mfderiv I 𝓘(ℝ) f x v = mfderiv I 𝓘(ℝ) f x
    (mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (Set.range I) (extChartAt I α x)
      ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x v))
  have hsymm := congrArg
    (fun L : E →L[ℝ] TangentSpace I x => L
      ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x v))
    (TangentBundle.symmL_trivializationAt (I := I) hx)
  have hcancel := Trivialization.symmL_continuousLinearMapAt
    (R := ℝ) (trivializationAt E (TangentSpace I) α) hx v
  apply congrArg (mfderiv I 𝓘(ℝ) f x)
  exact hcancel.symm.trans hsymm

omit [Module.Finite ℝ E] in
theorem tangentSectionAction_eq_fderivWithin_scalarOnE
    (α : M) (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {f : M → ℝ} {x : M} (hx : x ∈ (chartAt H α).source)
    (hf : MDifferentiableAt I 𝓘(ℝ) f x) :
    tangentSectionAction X f x =
      fderivWithin ℝ (scalarOnE (I := I) α f) (extChartAt I α).target (extChartAt I α x)
        ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x (X x)) :=
  mfderiv_eq_fderivWithin_scalarOnE α hx hf (X x)

end CalabiYau.DivergenceTheorem
