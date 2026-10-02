-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Tensor/Exterior/Pullback.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Manifold.DifferentialForm.Basic
public import CalabiYau.Geometry.Manifold.Bundle.TangentSpace
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.ContMDiffMap

@[expose] public section


noncomputable section

open Bundle Set ContinuousAlternatingMap Function Filter
open scoped Topology Manifold ContDiff Bundle

namespace CalabiYau
namespace DifferentialForm

attribute [local instance] seminormedAddCommGroupTangentSpace
attribute [local instance] normedAddCommGroupTangentSpace
attribute [local instance] normedSpaceTangentSpace

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ∞ M]
  {k : ℕ}
  {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  {HN : Type*} [TopologicalSpace HN]
  {IN : ModelWithCorners ℝ EN HN}
  {N : Type*} [TopologicalSpace N] [ChartedSpace HN N] [IsManifold IN ∞ N]

private lemma pullback_localRep_eq {f : M → N} (η : DifferentialForm IN N k) {x₀ x : M}
    (hx₀ : x ∈ (extChartAt IM x₀).source) (hfx : f x ∈ (extChartAt IN (f x₀)).source) :
    (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x₀
        ⟨x, (η (f x)).compContinuousLinearMap (mfderiv IM IN f x)⟩).2 =
      ((trivializationAt (EN [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) EN (TangentSpace IN) ℝ
          (Bundle.Trivial N ℝ)) (f x₀) ⟨f x, η (f x)⟩).2).compContinuousLinearMap
          (inTangentCoordinates IM IN id f
            (fun x : M => tangentLinearMapToModel (mfderiv IM IN f x)) x₀ x) := by
  rw [continuousAlternatingMap_trivializationAt_apply (m := k) (IM := IM) (M := M) (x₀ := x₀)
    (x := x)
      (L := (η (f x)).compContinuousLinearMap (mfderiv IM IN f x)),
    continuousAlternatingMap_trivializationAt_apply (m := k) (IM := IN) (M := N) (x₀ := f x₀)
      (x := f x)
      (L := η (f x))]
  rw [inTangentCoordinates_eq (I := IM) (I' := IN) (f := (id : M → M)) (g := f)
    (ϕ := fun x : M => tangentLinearMapToModel (mfderiv IM IN f x))
    (by simpa [extChartAt_source] using hx₀)
    (by simpa [extChartAt_source] using hfx)]
  rw [← TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (𝕜 := ℝ) (I := IN) (M := N)
    (by simpa [extChartAt_source] using hfx)]
  rw [← TangentBundle.symmL_trivializationAt_eq_core (𝕜 := ℝ) (I := IM) (M := M)
    (by simpa [extChartAt_source] using hx₀)]
  apply ContinuousAlternatingMap.ext
  intro v
  change η (f x) (fun i =>
      (mfderiv IM IN f x) ((trivializationAt EM (TangentSpace IM) x₀).symmL ℝ x (v i))) =
    η (f x) (fun i =>
      (trivializationAt EN (TangentSpace IN) (f x₀)).symmL ℝ (f x)
        ((trivializationAt EN (TangentSpace IN) (f x₀)).continuousLinearMapAt ℝ (f x)
          (tangentLinearMapToModel (mfderiv IM IN f x)
            ((trivializationAt EM (TangentSpace IM) x₀).symmL ℝ x (v i)))))
  congr 1
  funext i
  exact (Trivialization.symmL_continuousLinearMapAt (R := ℝ)
    (trivializationAt EN (TangentSpace IN) (f x₀))
    (by simpa [extChartAt_source] using hfx)
    ((mfderiv IM IN f x) ((trivializationAt EM (TangentSpace IM) x₀).symmL ℝ x (v i)))).symm

private lemma contMDiffAt_localRep (η : DifferentialForm IN N k) (y₀ : N) :
    ContMDiffAt IN 𝓘(ℝ, EN [⋀^Fin k]→L[ℝ] ℝ) ∞
      (fun y : N => (trivializationAt (EN [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) EN (TangentSpace IN) ℝ
          (Bundle.Trivial N ℝ)) y₀ ⟨y, η y⟩).2) y₀ := by
  exact (Bundle.Trivialization.contMDiffAt_section_iff
    (trivializationAt (EN [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) EN (TangentSpace IN) ℝ
        (Bundle.Trivial N ℝ)) y₀)
    (mem_baseSet_trivializationAt (EN [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) EN (TangentSpace IN) ℝ
        (Bundle.Trivial N ℝ)) y₀)).mp (η.contMDiff_toFun y₀)

noncomputable def pullback (f : M → N) (hf : ContMDiff IM IN ∞ f)
    (η : DifferentialForm IN N k) : DifferentialForm IM M k :=
  ⟨fun x => (η (f x)).compContinuousLinearMap (mfderiv IM IN f x), by
    intro x₀
    let e := trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
        (Bundle.Trivial M ℝ)) x₀
    rw [Bundle.Trivialization.contMDiffAt_section_iff e
      (mem_baseSet_trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x₀)]
    have hsec : ContMDiffAt IM 𝓘(ℝ, EN [⋀^Fin k]→L[ℝ] ℝ) ∞
        (fun x : M => (trivializationAt (EN [⋀^Fin k]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin k) EN (TangentSpace IN) ℝ
            (Bundle.Trivial N ℝ)) (f x₀) ⟨f x, η (f x)⟩).2) x₀ := by
      exact (contMDiffAt_localRep η (f x₀)).comp x₀ hf.contMDiffAt
    have htc : ContMDiffAt IM 𝓘(ℝ, EM →L[ℝ] EN) ∞
        (fun x : M => inTangentCoordinates IM IN id f
          (fun x : M => tangentLinearMapToModel (mfderiv IM IN f x)) x₀ x) x₀ := by
      have hmap (x : M) : tangentLinearMapToModel (mfderiv IM IN f x) =
          (mfderiv IM IN f x : EM →L[ℝ] EN) := by
        apply ContinuousLinearMap.ext
        intro v
        rw [tangentLinearMapToModel_apply,
          tangentSpaceModelContinuousLinearEquiv_apply,
          tangentSpaceModelContinuousLinearEquiv_symm_apply]
        rfl
      simpa only [hmap] using
        (ContMDiffAt.mfderiv_const (I := IM) (I' := IN) (f := f) (hf := hf.contMDiffAt)
          (m := ∞) (by simp))
    let g : M → (EN [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] (EM [⋀^Fin k]→L[ℝ] ℝ) := fun x =>
      ContinuousAlternatingMap.compContinuousLinearMapCLM
        (inTangentCoordinates IM IN id f
          (fun x : M => tangentLinearMapToModel (mfderiv IM IN f x)) x₀ x)
    have hg : ContMDiffAt IM 𝓘(ℝ, (EN [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] (EM [⋀^Fin k]→L[ℝ] ℝ)) ∞ g x₀ := by
      exact (ContinuousAlternatingMap.compContinuousLinearMapCLM_contMDiff_of_space_real
        (F₁ := EM) (F₁' := EN) (F₂ := ℝ) (ι := Fin k)).of_le (by simp) |>.contMDiffAt.comp x₀ htc
    have hgf : ContMDiffAt IM 𝓘(ℝ, EM [⋀^Fin k]→L[ℝ] ℝ) ∞
        (fun x : M => g x ((trivializationAt (EN [⋀^Fin k]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin k) EN (TangentSpace IN) ℝ
            (Bundle.Trivial N ℝ)) (f x₀) ⟨f x, η (f x)⟩).2)) x₀ :=
      hg.clm_apply hsec
    refine hgf.congr_of_eventuallyEq ?_
    filter_upwards [(trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
        (Bundle.Trivial M ℝ)) x₀).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x₀),
      (isOpen_extChartAt_source (I := IM) x₀).mem_nhds (mem_extChartAt_source x₀),
      hf.contMDiffAt.continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_source (I := IN) (f x₀)).mem_nhds (mem_extChartAt_source (f x₀)))]
      with x hx₁ hx₂ hx₃
    change (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x₀
        ⟨x, (η (f x)).compContinuousLinearMap (mfderiv IM IN f x)⟩).2 =
      g x ((trivializationAt (EN [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) EN (TangentSpace IN) ℝ
          (Bundle.Trivial N ℝ)) (f x₀) ⟨f x, η (f x)⟩).2)
    rw [pullback_localRep_eq (IM := IM) (M := M) (IN := IN) (N := N) (f := f) η
      (by simpa [extChartAt_source] using hx₂) (by simpa [extChartAt_source] using hx₃)]
    simp [g, ContinuousAlternatingMap.compContinuousLinearMapCLM_apply]
  ⟩

@[simp] theorem pullback_apply (f : M → N) (hf : ContMDiff IM IN ∞ f)
    (η : DifferentialForm IN N k) (x : M) :
    (pullback f hf η) x = (η (f x)).compContinuousLinearMap (mfderiv IM IN f x) :=
  rfl

private lemma fderiv_chartLocalMap_eq_inTangentCoordinates (f : M → N)
    (hf : ContMDiff IM IN ∞ f) [BoundarylessManifold IM M] [BoundarylessManifold IN N]
    {x₀ z : M} (hz : z ∈ (extChartAt IM x₀).source)
    (hfz : f z ∈ (extChartAt IN (f x₀)).source) :
    fderiv ℝ (fun y : EM => (extChartAt IN (f x₀)) (f ((extChartAt IM x₀).symm y)))
        ((extChartAt IM x₀) z) =
      inTangentCoordinates IM IN id f
        (fun x : M => tangentLinearMapToModel (mfderiv IM IN f x)) x₀ z := by
  have : IsManifold IM 1 M := IsManifold.of_le (m := 1) (n := ∞) (by norm_num)
  have : IsManifold IN 1 N := IsManifold.of_le (m := 1) (n := ∞) (by norm_num)
  let c₀ := extChartAt IM x₀
  let c₁ := extChartAt IN (f x₀)
  let c₁' := extChartAt IN (f z)
  let c_z := extChartAt IM z
  let A : EN → EN := fun y => c₁ (c₁'.symm y)
  let B : EM → EN := fun y => c₁' (f (c_z.symm y))
  let C : EM → EM := fun y => c_z (c₀.symm y)
  have h₁eval : C (c₀ z) = c_z z := by
    dsimp [C]
    rw [c₀.left_inv hz]
  have h₂eval : B (c_z z) = c₁' (f z) := by
    dsimp [B]
    rw [c_z.left_inv (mem_extChartAt_source (H := HM) z)]
  have h₃eval : A (c₁' (f z)) = c₁ (f z) := by
    dsimp [A]
    rw [c₁'.left_inv (mem_extChartAt_source (H := HN) (f z))]
  have hsrc_z : z ∈ c_z.source := mem_extChartAt_source (H := HM) z
  have hsrc_fz : f z ∈ c₁'.source := mem_extChartAt_source (H := HN) (f z)
  have hdecomp : (fun y : EM => c₁ (f (c₀.symm y))) =ᶠ[𝓝 (c₀ z)] (A ∘ B ∘ C) := by
    have h₁ : c_z.source ∈ 𝓝 z :=
      (isOpen_extChartAt_source (I := IM) z).mem_nhds hsrc_z
    have h₂ : f ⁻¹' c₁'.source ∈ 𝓝 z :=
      hf.contMDiffAt.continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_source (I := IN) (f z)).mem_nhds hsrc_fz)
    have h₃ : c₀.symm ⁻¹' (c_z.source ∩ f ⁻¹' c₁'.source) ∈ 𝓝 (c₀ z) := by
      have hcont : ContinuousAt c₀.symm (c₀ z) :=
        continuousAt_extChartAt_symm' (I := IM) (M := M) (x := x₀) (x' := z) hz
      have h₄ : c_z.source ∩ f ⁻¹' c₁'.source ∈ 𝓝 (c₀.symm (c₀ z)) := by
        rw [c₀.left_inv hz]
        exact Filter.inter_mem h₁ h₂
      exact hcont.preimage_mem_nhds h₄
    refine Eventually.mono h₃ ?_
    intro y hy
    have hy₁ : c₀.symm y ∈ c_z.source := hy.1
    have hy₂ : f (c₀.symm y) ∈ c₁'.source := hy.2
    dsimp [A, B, C]
    rw [show c_z.symm (c_z (c₀.symm y)) = c₀.symm y from
      c_z.left_inv hy₁,
      show c₁'.symm (c₁' (f (c₀.symm y))) = f (c₀.symm y) from
      c₁'.left_inv hy₂]
  have hfder : fderiv ℝ (fun y : EM => c₁ (f (c₀.symm y))) (c₀ z) =
      fderiv ℝ (A ∘ B ∘ C) (c₀ z) := hdecomp.fderiv_eq
  have hC : ContDiffAt ℝ ∞ C (c₀ z) := by
    have hsrc : (c₀ z) ∈ ((c₀.symm ≫ c_z).source) := by
      rw [PartialEquiv.trans_source]
      exact ⟨c₀.map_source hz, by
        have : c₀.symm (c₀ z) = z := c₀.left_inv hz
        change c₀.symm (c₀ z) ∈ c_z.source
        rw [this]
        exact mem_extChartAt_source (H := HM) z⟩
    have hc : ContDiffWithinAt ℝ ∞ (c_z ∘ c₀.symm) (range IM) (c₀ z) := by
      exact contDiffWithinAt_ext_coord_change (I := IM) z x₀ hsrc
    have hint : (c₀ z) ∈ interior (range IM) :=
      have htarget : (c₀ z) ∈ interior ((extChartAt IM x₀).target) :=
        (ModelWithCorners.isInteriorPoint_iff_of_mem_atlas (I := IM) (n := 1)
          (e := (chartAt HM x₀)) (hn := by norm_num)
          (he := chart_mem_atlas (H := HM) x₀)
          (hx := by simpa [extChartAt_source] using hz)).1
          (BoundarylessManifold.isInteriorPoint (I := IM) (M := M) (x := z))
      interior_mono (by intro y hy; rw [extChartAt_target] at hy; exact hy.2) htarget
    exact hc.contDiffAt (mem_interior_iff_mem_nhds.mp hint)
  have hB : ContDiffAt ℝ ∞ B (c_z z) := by
    have hw : ContDiffWithinAt ℝ ∞ (c₁' ∘ f ∘ c_z.symm) (range IM) (c_z z) :=
      (contMDiffAt_iff.mp (hf.contMDiffAt (x := z))).2
    have hint : (c_z z) ∈ interior (range IM) :=
      have htarget : (extChartAt IM z) z ∈ interior ((extChartAt IM z).target) :=
        (ModelWithCorners.isInteriorPoint_iff_of_mem_atlas (I := IM) (n := 1)
          (e := (chartAt HM z)) (hn := by norm_num)
          (he := chart_mem_atlas (H := HM) z)
          (hx := by simp)).1
          (BoundarylessManifold.isInteriorPoint (I := IM) (M := M) (x := z))
      interior_mono (by intro y hy; rw [extChartAt_target] at hy; exact hy.2) htarget
    exact hw.contDiffAt (mem_interior_iff_mem_nhds.mp hint)
  have hA : ContDiffAt ℝ ∞ A (c₁' (f z)) := by
    have hsrc : (c₁' (f z)) ∈ ((c₁'.symm ≫ c₁).source) := by
      rw [PartialEquiv.trans_source]
      exact ⟨c₁'.map_source hsrc_fz, by
        have : c₁'.symm (c₁' (f z)) = f z := c₁'.left_inv hsrc_fz
        change c₁'.symm (c₁' (f z)) ∈ c₁.source
        rw [this]
        simpa [c₁, extChartAt_source] using hfz⟩
    have hc : ContDiffWithinAt ℝ ∞ (c₁ ∘ c₁'.symm) (range IN) (c₁' (f z)) := by
      exact contDiffWithinAt_ext_coord_change (I := IN) (f x₀) (f z) hsrc
    have hint : (c₁' (f z)) ∈ interior (range IN) :=
      have htarget : (extChartAt IN (f z)) (f z) ∈ interior ((extChartAt IN (f z)).target) :=
        (ModelWithCorners.isInteriorPoint_iff_of_mem_atlas (I := IN) (n := 1)
          (e := (chartAt HN (f z))) (hn := by norm_num)
          (he := chart_mem_atlas (H := HN) (f z))
          (hx := by simp)).1
          (BoundarylessManifold.isInteriorPoint (I := IN) (M := N) (x := f z))
      interior_mono (by intro y hy; rw [extChartAt_target] at hy; exact hy.2) htarget
    exact hc.contDiffAt (mem_interior_iff_mem_nhds.mp hint)
  have hchain : fderiv ℝ (A ∘ B ∘ C) (c₀ z) =
      fderiv ℝ A (B (C (c₀ z))) ∘L fderiv ℝ B (C (c₀ z)) ∘L fderiv ℝ C (c₀ z) := by
    have h₁ : DifferentiableAt ℝ C (c₀ z) := hC.differentiableAt (by norm_num)
    have h₂ : DifferentiableAt ℝ B (C (c₀ z)) := by
      rw [h₁eval]
      exact hB.differentiableAt (by norm_num)
    have h₃ : DifferentiableAt ℝ A (B (C (c₀ z))) := by
      rw [h₁eval, h₂eval]
      exact hA.differentiableAt (by norm_num)
    have hBC : DifferentiableAt ℝ (B ∘ C) (c₀ z) :=
      DifferentiableAt.comp (g := B) (f := C) (x := c₀ z) h₂ h₁
    calc
      fderiv ℝ (A ∘ B ∘ C) (c₀ z)
          = fderiv ℝ A (B (C (c₀ z))) ∘L fderiv ℝ (B ∘ C) (c₀ z) := by
        simpa using (fderiv_comp (g := A) (f := B ∘ C) (x := c₀ z) h₃ hBC)
      _ = fderiv ℝ A (B (C (c₀ z))) ∘L
          (fderiv ℝ B (C (c₀ z)) ∘L fderiv ℝ C (c₀ z)) := by
        congr 1
        exact fderiv_comp (g := B) (f := C) (x := c₀ z) h₂ h₁
  rw [hfder, hchain, h₁eval, h₂eval]
  have hfC : fderiv ℝ C (c₀ z) = tangentCoordChange IM x₀ z z := by
    exact fderiv_chartChange_rev_eq_tangentCoordChange (IM := IM) (M := M) hz
      (BoundarylessManifold.isInteriorPoint (I := IM) (M := M) (x := z))
  have hfB : fderiv ℝ B (c_z z) =
      tangentLinearMapToModel (mfderiv IM IN f z) := by
    have hmd : MDifferentiableAt IM IN f z :=
      ContMDiff.mdifferentiableAt (I := IM) (I' := IN) hf (by norm_num)
    have hmodel : tangentLinearMapToModel (mfderiv IM IN f z) =
        fderivWithin ℝ (writtenInExtChartAt IM IN z f) (range IM) ((extChartAt IM z) z) := by
      apply ContinuousLinearMap.ext
      intro v
      rw [tangentLinearMapToModel_apply,
        tangentSpaceModelContinuousLinearEquiv_apply,
        tangentSpaceModelContinuousLinearEquiv_symm_apply]
      rw [hmd.mfderiv]
      rfl
    have hw : writtenInExtChartAt IM IN z f = fun y : EM => c₁' (f (c_z.symm y)) := by
      rfl
    have hmem : (c_z z) ∈ interior (c_z.target) :=
      (ModelWithCorners.isInteriorPoint_iff (I := IM)).mp
        (BoundarylessManifold.isInteriorPoint (I := IM) (M := M) (x := z))
    rw [hmodel, hw, fderivWithin_of_mem_nhds
      (mem_interior_iff_mem_nhds.mp
        (interior_mono (extChartAt_target_subset_range (I := IM) z) hmem))]
  have hfA : fderiv ℝ A (c₁' (f z)) = tangentCoordChange IN (f z) (f x₀) (f z) := by
    exact fderiv_chartChange_eq_tangentCoordChange (IM := IN) (M := N) hfz
      (BoundarylessManifold.isInteriorPoint (I := IN) (M := N) (x := f z))
  rw [hfC, hfB, hfA]
  rw [inTangentCoordinates_eq (I := IM) (I' := IN) (f := (id : M → M)) (g := f)
    (ϕ := fun x : M => tangentLinearMapToModel (mfderiv IM IN f x))
    (by simpa [extChartAt_source] using hz) (by simpa [extChartAt_source] using hfz)]
  simp only [id_eq, tangentBundleCore_coordChange]

private lemma pullback_localRep_fderiv (η : DifferentialForm IN N k) (f : M → N)
    (hf : ContMDiff IM IN ∞ f) [BoundarylessManifold IM M] [BoundarylessManifold IN N]
    {x₀ z : M} (hz : z ∈ (extChartAt IM x₀).source)
    (hfz : f z ∈ (extChartAt IN (f x₀)).source) :
    (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x₀
        ⟨z, (η (f z)).compContinuousLinearMap (mfderiv IM IN f z)⟩).2 =
      ((trivializationAt (EN [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) EN (TangentSpace IN) ℝ
          (Bundle.Trivial N ℝ)) (f x₀) ⟨f z, η (f z)⟩).2).compContinuousLinearMap
          (fderiv ℝ (fun y : EM => (extChartAt IN (f x₀)) (f ((extChartAt IM x₀).symm y)))
            ((extChartAt IM x₀) z)) := by
  rw [pullback_localRep_eq (IM := IM) (M := M) (IN := IN) (N := N) (f := f) η hz hfz]
  rw [← fderiv_chartLocalMap_eq_inTangentCoordinates (IM := IM) (M := M) (IN := IN) (N := N)
    f hf hz hfz]

private lemma triv_samePoint_fiber_eq_id (m : ℕ) (x : M)
    (L : Bundle.continuousAlternatingMap ℝ (Fin m) EM (TangentSpace IM) ℝ
      (Bundle.Trivial M ℝ) x) :
    (trivializationAt (EM [⋀^Fin m]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin m) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x ⟨x, L⟩).2 = L := by
  rw [continuousAlternatingMap_trivializationAt_apply (m := m) (IM := IM) (M := M) (x₀ := x)
    (x := x) (L := L)]
  have hid : (trivializationAt EM (TangentSpace IM) x).symmL ℝ x =
      ContinuousLinearMap.id ℝ EM := by
    apply ContinuousLinearMap.ext
    intro v
    rw [TangentBundle.symmL_trivializationAt_eq_core (𝕜 := ℝ) (I := IM) (M := M)
      (by simp)]
    exact tangentCoordChange_self (I := IM) (x := x) (z := x)
      (by simp)
  rw [hid]
  ext v
  rfl

theorem exteriorDerivative_pullback [BoundarylessManifold IM M] [BoundarylessManifold IN N]
    (f : M → N) (hf : ContMDiff IM IN ∞ f) (η : DifferentialForm IN N k) :
    pullback f hf (exteriorDerivative (IM := IN) (M := N) η) =
      exteriorDerivative (pullback f hf η) := by
  apply ContMDiffSection.ext
  intro x
  let c₀ := extChartAt IM x
  let c₁ := extChartAt IN (f x)
  let e := trivializationAt (EM [⋀^Fin (k + 1)]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin (k + 1)) EM (TangentSpace IM) ℝ
        (Bundle.Trivial M ℝ)) x
  let eN := trivializationAt (EN [⋀^Fin (k + 1)]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin (k + 1)) EN (TangentSpace IN) ℝ
        (Bundle.Trivial N ℝ)) (f x)
  let rep_η : EN → EN [⋀^Fin k]→L[ℝ] ℝ := fun y =>
    (trivializationAt (EN [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) EN (TangentSpace IN) ℝ
        (Bundle.Trivial N ℝ)) (f x) ⟨(extChartAt IN (f x)).symm y,
          η ((extChartAt IN (f x)).symm y)⟩).2
  let f_local : EM → EN := fun y => (extChartAt IN (f x)) (f ((extChartAt IM x).symm y))
  let rep_pb : EM → EM [⋀^Fin k]→L[ℝ] ℝ := fun y =>
    (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
        (Bundle.Trivial M ℝ)) x ⟨(extChartAt IM x).symm y,
          (pullback f hf η) ((extChartAt IM x).symm y)⟩).2
  have hx₀ : x ∈ (extChartAt IM x).source := mem_extChartAt_source (H := HM) x
  have hfx : f x ∈ (extChartAt IN (f x)).source := mem_extChartAt_source (H := HN) (f x)
  have hLHS : (e ⟨x, (pullback f hf (exteriorDerivative (IM := IN) (M := N) η)) x⟩).2 =
      ((eN ⟨f x, (exteriorDerivative (IM := IN) (M := N) η) (f x)⟩).2).compContinuousLinearMap
        (fderiv ℝ f_local (c₀ x)) := by
    simp only [pullback_apply]
    exact pullback_localRep_fderiv (η := exteriorDerivative (IM := IN) (M := N) η) (f := f)
      (hf := hf) (x₀ := x) (z := x) (by simp) (by simp)
  have hRHS : (e ⟨x, (exteriorDerivative (pullback f hf η)) x⟩).2 =
      extDeriv rep_pb (c₀ x) := by
    rw [exteriorDerivative_apply]
    exact exteriorDerivative_localRepresentation (IM := IM) (M := M) (α := pullback f hf η)
      (x₀ := x) (x := x) (by simp)
      (BoundarylessManifold.isInteriorPoint (I := IM) (M := M) (x := x))
  have hsrc_pb : ContDiffAt ℝ ∞ f_local (c₀ x) := by
    have h₁ : ContMDiffAt IM 𝓘(ℝ, EN) ∞ (fun x' : M => (extChartAt IN (f x)) (f x')) x :=
      (contMDiffAt_extChartAt' (I := IN) (M := N) (x := f x) (x' := f x)
        (by simp)).comp x hf.contMDiffAt
    have h₂ : ContMDiffAt 𝓘(ℝ, EM) IM ∞ (extChartAt IM x).symm (c₀ x) := by
      have hmem : (c₀ x) ∈ interior ((extChartAt IM x).target) :=
        (ModelWithCorners.isInteriorPoint_iff_of_mem_atlas (I := IM) (n := 1)
          (e := (chartAt HM x)) (hn := by norm_num)
          (he := chart_mem_atlas (H := HM) x)
          (hx := by simp)).1
          (BoundarylessManifold.isInteriorPoint (I := IM) (M := M) (x := x))
      exact (contMDiffOn_extChartAt_symm x).contMDiffAt
        (mem_interior_iff_mem_nhds.mp hmem)
    have h₃ : ContMDiffAt 𝓘(ℝ, EM) 𝓘(ℝ, EN) ∞
        (fun y : EM => (extChartAt IN (f x)) (f ((extChartAt IM x).symm y))) (c₀ x) :=
      h₁.comp_of_eq h₂ ((extChartAt IM x).left_inv hx₀)
    change ContDiffAt ℝ ∞
      (fun y : EM => (extChartAt IN (f x)) (f ((extChartAt IM x).symm y))) (c₀ x)
    exact h₃.contDiffAt
  have hrep_η : ContDiffAt ℝ ∞ rep_η (c₁ (f x)) := by
    have h₁ : ContMDiffAt IN 𝓘(ℝ, EN [⋀^Fin k]→L[ℝ] ℝ) ∞
        (fun y : N => (trivializationAt (EN [⋀^Fin k]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin k) EN (TangentSpace IN) ℝ
            (Bundle.Trivial N ℝ)) (f x) ⟨y, η y⟩).2) (f x) :=
      contMDiffAt_localRep η (f x)
    have h₃ : ContMDiffAt 𝓘(ℝ, EN) 𝓘(ℝ, EN [⋀^Fin k]→L[ℝ] ℝ) ∞
        (fun y : EN => (trivializationAt (EN [⋀^Fin k]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin k) EN (TangentSpace IN) ℝ
            (Bundle.Trivial N ℝ)) (f x) ⟨(extChartAt IN (f x)).symm y,
              η ((extChartAt IN (f x)).symm y)⟩).2)
        (c₁ (f x)) :=
      h₁.comp_of_eq
        (by
          have hmem : (c₁ (f x)) ∈ interior ((extChartAt IN (f x)).target) :=
            (ModelWithCorners.isInteriorPoint_iff_of_mem_atlas (I := IN) (n := 1)
              (e := (chartAt HN (f x))) (hn := by norm_num)
              (he := chart_mem_atlas (H := HN) (f x))
              (hx := by simp)).1
              (BoundarylessManifold.isInteriorPoint (I := IN) (M := N) (x := f x))
          exact (contMDiffOn_extChartAt_symm (f x)).contMDiffAt
            (mem_interior_iff_mem_nhds.mp hmem))
        ((extChartAt IN (f x)).left_inv hfx)
    exact h₃.contDiffAt
  have hpb_rep : rep_pb =ᶠ[𝓝 (c₀ x)]
      (fun y : EM => (rep_η (f_local y)).compContinuousLinearMap (fderiv ℝ f_local y)) := by
    have hN : c₀.target ∩ c₀.symm ⁻¹' (f ⁻¹' (extChartAt IN (f x)).source) ∈
        𝓝 (c₀ x) := by
      have h₁ : c₀.target ∈ 𝓝 (c₀ x) :=
        by
          have hmem : (c₀ x) ∈ interior (c₀.target) :=
            (ModelWithCorners.isInteriorPoint_iff_of_mem_atlas (I := IM) (n := 1)
              (e := (chartAt HM x)) (hn := by norm_num)
              (he := chart_mem_atlas (H := HM) x)
              (hx := by simp)).1
              (BoundarylessManifold.isInteriorPoint (I := IM) (M := M) (x := x))
          exact mem_interior_iff_mem_nhds.mp hmem
      have h₂ : c₀.symm ⁻¹' (f ⁻¹' (extChartAt IN (f x)).source) ∈ 𝓝 (c₀ x) := by
        have hpre : f ⁻¹' (extChartAt IN (f x)).source ∈ 𝓝 x :=
          hf.contMDiffAt.continuousAt.preimage_mem_nhds
            ((isOpen_extChartAt_source (I := IN) (f x)).mem_nhds hfx)
        have hcont : ContinuousAt c₀.symm (c₀ x) :=
          continuousAt_extChartAt_symm' (I := IM) (M := M) (x := x) (x' := x) hx₀
        have h₃ : f ⁻¹' (extChartAt IN (f x)).source ∈ 𝓝 (c₀.symm (c₀ x)) := by
          rw [c₀.left_inv hx₀]
          exact hpre
        simpa [c₀.left_inv hx₀] using hcont.preimage_mem_nhds h₃
      exact Filter.inter_mem h₁ h₂
    refine Eventually.mono hN ?_
    intro y hy
    have hy₀ : y ∈ c₀.target := hy.1
    have hy₂ : f (c₀.symm y) ∈ (extChartAt IN (f x)).source := hy.2
    have hy₁ : c₀.symm y ∈ c₀.source := c₀.map_target hy₀
    change (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x
        ⟨(extChartAt IM x).symm y, (pullback f hf η) ((extChartAt IM x).symm y)⟩).2 =
      ((trivializationAt (EN [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) EN (TangentSpace IN) ℝ
          (Bundle.Trivial N ℝ)) (f x)
        ⟨(extChartAt IN (f x)).symm ((extChartAt IN (f x)) (f ((extChartAt IM x).symm y))),
          η ((extChartAt IN (f x)).symm ((extChartAt IN (f x)) (f
            ((extChartAt IM x).symm y))))⟩).2).compContinuousLinearMap
          (fderiv ℝ (fun y : EM => (extChartAt IN (f x)) (f ((extChartAt IM x).symm y))) y)
    rw [show (pullback f hf η) ((extChartAt IM x).symm y) =
        (η (f ((extChartAt IM x).symm y))).compContinuousLinearMap
          (mfderiv IM IN f ((extChartAt IM x).symm y)) from by
      rw [pullback_apply]]
    rw [show (extChartAt IN (f x)).symm ((extChartAt IN (f x)) (f ((extChartAt IM x).symm y))) =
        f ((extChartAt IM x).symm y) from (extChartAt IN (f x)).left_inv hy₂]
    convert pullback_localRep_fderiv (η := η) (f := f) (hf := hf) (x₀ := x)
      (z := (extChartAt IM x).symm y) hy₁ hy₂ using 1
    rw [(extChartAt IM x).right_inv hy₀]
  have hExt : extDeriv rep_pb (c₀ x) =
      (extDeriv rep_η (f_local (c₀ x))).compContinuousLinearMap (fderiv ℝ f_local (c₀ x)) := by
    rw [Filter.EventuallyEq.extDeriv_eq hpb_rep]
    exact extDeriv_pullback (𝕜 := ℝ) (E := EM) (F := EN) (G := ℝ) (n := k)
      (hω := by
        have hfl : f_local (c₀ x) = c₁ (f x) := by
          change (extChartAt IN (f x)) (f ((extChartAt IM x).symm ((extChartAt IM x) x))) =
            (extChartAt IN (f x)) (f x)
          rw [(extChartAt IM x).left_inv hx₀]
        rw [hfl]
        exact hrep_η.differentiableAt (by norm_num))
      (hf := hsrc_pb) (hr := by
        rw [minSmoothness_of_isRCLikeNormedField]
        exact ENat.LEInfty.out)
  have hdη : extDeriv rep_η (c₁ (f x)) =
      (eN ⟨f x, (exteriorDerivative (IM := IN) (M := N) η) (f x)⟩).2 := by
    rw [exteriorDerivative_apply]
    exact (exteriorDerivative_localRepresentation (IM := IN) (M := N) (α := η)
      (x₀ := f x) (x := f x) (by simp)
      (BoundarylessManifold.isInteriorPoint (I := IN) (M := N) (x := f x))).symm
  have hfinal : (e ⟨x, (pullback f hf (exteriorDerivative (IM := IN) (M := N) η)) x⟩).2 =
      (e ⟨x, (exteriorDerivative (pullback f hf η)) x⟩).2 := by
    rw [hLHS, hRHS, hExt]
    have hfl : f_local (c₀ x) = c₁ (f x) := by
      change (extChartAt IN (f x)) (f ((extChartAt IM x).symm ((extChartAt IM x) x))) =
        (extChartAt IN (f x)) (f x)
      rw [(extChartAt IM x).left_inv hx₀]
    rw [hfl]
    rw [hdη]
  have h₁ : (e ⟨x, (pullback f hf (exteriorDerivative (IM := IN) (M := N) η)) x⟩).2 =
      (pullback f hf (exteriorDerivative (IM := IN) (M := N) η)) x := by
    exact triv_samePoint_fiber_eq_id (m := k + 1) (IM := IM) (M := M) x
      ((pullback f hf (exteriorDerivative (IM := IN) (M := N) η)) x)
  have h₂ : (e ⟨x, (exteriorDerivative (pullback f hf η)) x⟩).2 =
      (exteriorDerivative (pullback f hf η)) x := by
    exact triv_samePoint_fiber_eq_id (m := k + 1) (IM := IM) (M := M) x
      ((exteriorDerivative (pullback f hf η)) x)
  rw [← h₁, ← h₂]
  exact hfinal

variable {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  {HP : Type*} [TopologicalSpace HP]
  {IP : ModelWithCorners ℝ EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P] [IsManifold IP ∞ P]
  {l : ℕ}

theorem pullback_add (f : M → N) (hf : ContMDiff IM IN ∞ f)
    (α β : DifferentialForm IN N k) :
    pullback f hf (α + β) = pullback f hf α + pullback f hf β := by
  apply ContMDiffSection.ext
  intro x
  change (α (f x) + β (f x)).compContinuousLinearMap (mfderiv IM IN f x) =
    (α (f x)).compContinuousLinearMap (mfderiv IM IN f x) +
    (β (f x)).compContinuousLinearMap (mfderiv IM IN f x)
  exact ContinuousAlternatingMap.compContinuousLinearMap_add (α (f x)) (β (f x))
    (mfderiv IM IN f x)

theorem pullback_smul (c : ℝ) (f : M → N) (hf : ContMDiff IM IN ∞ f)
    (α : DifferentialForm IN N k) :
    pullback f hf (c • α) = c • pullback f hf α := by
  apply ContMDiffSection.ext
  intro x
  change (c • α (f x)).compContinuousLinearMap (mfderiv IM IN f x) =
    c • (α (f x)).compContinuousLinearMap (mfderiv IM IN f x)
  exact ContinuousAlternatingMap.compContinuousLinearMap_smul c (α (f x))
    (mfderiv IM IN f x)

noncomputable def pullbackLinearMap (f : M → N) (hf : ContMDiff IM IN ∞ f) (k : ℕ) :
    DifferentialForm IN N k →ₗ[ℝ] DifferentialForm IM M k :=
  { toFun := pullback f hf
    map_add' := pullback_add f hf
    map_smul' := fun c α => pullback_smul c f hf α }

end DifferentialForm
end CalabiYau

end
