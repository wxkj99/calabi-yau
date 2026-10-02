-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Tensor/Exterior/Basic.lean
-- Locally modified.
/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
Coauthors: Jack McCarthy
-/
module
public import CalabiYau.Geometry.Manifold.DifferentialForm.Defs
public import CalabiYau.Geometry.Manifold.Bundle.TangentCoordChange
public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

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

private lemma linearMapAt_symmL_eq_tangentCoordChange {x₀ x z : M}
    (hx : z ∈ (extChartAt IM x).source) (hx₀ : z ∈ (extChartAt IM x₀).source) :
    (trivializationAt EM (TangentSpace IM) x₀).continuousLinearMapAt ℝ z ∘L
        (trivializationAt EM (TangentSpace IM) x).symmL ℝ z =
      tangentCoordChange IM x x₀ z := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (by simpa
    [extChartAt_source] using hx₀),
    TangentBundle.symmL_trivializationAt_eq_core (by simpa [extChartAt_source] using hx)]
  apply ContinuousLinearMap.ext
  intro v
  have hw : z ∈ (extChartAt IM x).source ∩ (extChartAt IM z).source ∩ (extChartAt IM x₀).source :=
    ⟨⟨by simpa [extChartAt_source] using hx, by simp⟩,
      by simpa [extChartAt_source] using hx₀⟩
  change tangentCoordChange IM z x₀ z
    (tangentCoordChange IM x z z v) = tangentCoordChange IM x x₀ z v
  exact tangentCoordChange_comp (w := x) (x := z) (y := x₀) (z := z) hw

private lemma localRep_eq_pullback {x₀ x z : M}
    (hx : z ∈ (extChartAt IM x).source) (hx₀ : z ∈ (extChartAt IM x₀).source) (m : ℕ)
    (L : (TangentSpace IM z) [⋀^Fin m]→L[ℝ] (Bundle.Trivial M ℝ z)) :
    (trivializationAt ((EM [⋀^Fin m]→L[ℝ] ℝ)) ((Bundle.continuousAlternatingMap ℝ (Fin m) EM
      (TangentSpace IM) ℝ (Bundle.Trivial M ℝ))) x ⟨z, L⟩).2 =
      ((trivializationAt ((EM [⋀^Fin m]→L[ℝ] ℝ)) ((Bundle.continuousAlternatingMap ℝ (Fin m) EM
        (TangentSpace IM) ℝ (Bundle.Trivial M ℝ))) x₀ ⟨z, L⟩).2).compContinuousLinearMap
        (tangentCoordChange IM x x₀ z) := by
  rw [CalabiYau.continuousAlternatingMap_trivializationAt_apply (m := m) (x₀ := x)
    (x := z) (L := L),
    CalabiYau.continuousAlternatingMap_trivializationAt_apply (m := m) (x₀ := x₀)
      (x := z) (L := L)]
  ext v
  change L ((trivializationAt EM (TangentSpace IM) x).symmL ℝ z ∘ v) =
    L (((trivializationAt EM (TangentSpace IM) x₀).symmL ℝ z ∘ tangentCoordChange IM x x₀ z) ∘ v)
  congr 1
  funext i
  rw [Function.comp_apply, Function.comp_apply]
  rw [← linearMapAt_symmL_eq_tangentCoordChange (x₀ := x₀) (x := x) (z := z) (hx := hx)
    (hx₀ := hx₀)]
  rw [Function.comp_apply]
  exact (Trivialization.symmL_continuousLinearMapAt (R := ℝ)
    (trivializationAt EM (TangentSpace IM) x₀)
    (by simpa [extChartAt_source] using hx₀)
    ((trivializationAt EM (TangentSpace IM) x).symmL ℝ z (v i))).symm

lemma localRep_contDiffOn (α : DifferentialForm IM M k) (x₀ : M) :
    ContDiffOn ℝ ∞ (fun y : EM => (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x₀ ⟨(extChartAt IM x₀).symm y, α ((extChartAt IM x₀).symm y)⟩).2)
      ((extChartAt IM x₀).target) := by
  have hsec : ContMDiffOn IM 𝓘(ℝ, EM [⋀^Fin k]→L[ℝ] ℝ) ∞ (fun z : M =>
      (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x₀ ⟨z, α z⟩).2) (extChartAt IM x₀).source := by
    intro z hz
    have hz₀ : z ∈ (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x₀).baseSet := by
      change z ∈ (trivializationAt EM (TangentSpace IM) x₀).baseSet ∩
        (trivializationAt ℝ (Bundle.Trivial M ℝ) x₀).baseSet
      exact ⟨by simpa [extChartAt_source] using hz, trivial⟩
    exact (Bundle.Trivialization.contMDiffAt_section_iff
      (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x₀) hz₀).mp (α.contMDiff_toFun z) |>.contMDiffWithinAt
  have hcomp : ContMDiffOn (𝓘(ℝ, EM)) 𝓘(ℝ, EM [⋀^Fin k]→L[ℝ] ℝ) ∞
      (fun y => (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x₀ ⟨(extChartAt IM x₀).symm y, α ((extChartAt IM x₀).symm y)⟩).2)
      ((extChartAt IM x₀).target) := by
    exact hsec.comp (contMDiffOn_extChartAt_symm x₀) (fun y hy => (extChartAt IM x₀).map_target hy)
  exact hcomp.contDiffOn

private lemma tangentCoordChange_comp_self {x₀ x : M} (hx : x ∈ (extChartAt IM x₀).source) :
    (tangentCoordChange IM x x₀ x) ∘L (tangentCoordChange IM x₀ x x) =
      ContinuousLinearMap.id ℝ EM := by
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.coe_comp, Function.comp_apply]
  have hw : x ∈ (extChartAt IM x₀).source ∩ (extChartAt IM x).source ∩
    (extChartAt IM x₀).source := by
    exact ⟨⟨hx, by simp⟩, hx⟩
  rw [tangentCoordChange_comp (I := IM) (w := x₀) (x := x) (y := x₀) (z := x) hw]
  exact tangentCoordChange_self (I := IM) (x := x₀) (z := x) hx

private lemma chartTarget_interior_of {x₀ x : M} (hx : x ∈ (extChartAt IM x₀).source)
    (hxi : ModelWithCorners.IsInteriorPoint IM x) :
    (extChartAt IM x₀) x ∈ interior ((extChartAt IM x₀).target) := by
  exact (ModelWithCorners.isInteriorPoint_iff_of_mem_atlas (I := IM) (n := 1)
    (e := (chartAt HM x₀)) (hn := by norm_num)
    (he := chart_mem_atlas (H := HM) x₀)
    (hx := by simpa [extChartAt_source] using hx)).1 hxi

private lemma rep_eqOn_pullback (α : DifferentialForm IM M k) {x₀ x : M}
    (hx : x ∈ (extChartAt IM x₀).source) (hxi : ModelWithCorners.IsInteriorPoint IM x) :
    ∀ᶠ y in 𝓝 ((extChartAt IM x₀) x),
      (fun y : EM => (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
            (Bundle.Trivial M ℝ)) x₀ ⟨(extChartAt IM x₀).symm y,
              α ((extChartAt IM x₀).symm y)⟩).2) y =
      ((fun y : EM => (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
            (Bundle.Trivial M ℝ)) x ⟨(extChartAt IM x).symm y, α ((extChartAt IM x).symm y)⟩).2)
        ((extChartAt IM x) ((extChartAt IM x₀).symm y))).compContinuousLinearMap
          (fderiv ℝ ((extChartAt IM x) ∘ (extChartAt IM x₀).symm) y) := by
  have hN : (extChartAt IM x₀).symm ⁻¹' ((extChartAt IM x).source) ∩
      interior ((extChartAt IM x₀).target) ∈ 𝓝 ((extChartAt IM x₀) x) := by
    have hsrc₁ : (extChartAt IM x).source ∈ 𝓝 x :=
      (isOpen_extChartAt_source (I := IM) x).mem_nhds (by simp)
    have hsymm : (extChartAt IM x₀).symm ⁻¹' ((extChartAt IM x).source) ∈
        𝓝 ((extChartAt IM x₀) x) := by
      have h₁ : (extChartAt IM x₀).symm ((extChartAt IM x₀) x) = x :=
        (extChartAt IM x₀).left_inv hx
      have hcont : ContinuousAt (extChartAt IM x₀).symm ((extChartAt IM x₀) x) :=
        continuousAt_extChartAt_symm' (I := IM) (M := M) (x := x₀) (x' := x) hx
      have hpre : (extChartAt IM x₀).symm ⁻¹' ((extChartAt IM x).source) ∈
          𝓝 ((extChartAt IM x₀) x) := by
        have hsrc₁' : (extChartAt IM x).source ∈ 𝓝 ((extChartAt IM x₀).symm
          ((extChartAt IM x₀) x)) := by
          rw [h₁]
          exact hsrc₁
        exact hcont.preimage_mem_nhds hsrc₁'
      simpa [h₁] using hpre
    have htar : interior ((extChartAt IM x₀).target) ∈ 𝓝 ((extChartAt IM x₀) x) := by
      have hmem : (extChartAt IM x₀) x ∈ interior ((extChartAt IM x₀).target) :=
        chartTarget_interior_of (IM := IM) (M := M) hx hxi
      exact mem_interior_iff_mem_nhds.mp (by rwa [interior_interior])
    exact Filter.inter_mem hsymm htar
  refine Eventually.mono hN ?_
  intro y hy
  have hy₀ : y ∈ (extChartAt IM x₀).target := interior_subset hy.2
  have hy₀s : (extChartAt IM x₀).symm y ∈ (extChartAt IM x₀).source :=
    (extChartAt IM x₀).map_target hy₀
  have hy₀s₁ : (extChartAt IM x₀).symm y ∈ (extChartAt IM x).source := hy.1
  let z : M := (extChartAt IM x₀).symm y
  have hyz : (extChartAt IM x₀) z = y := by
    dsimp [z]
    exact (extChartAt IM x₀).right_inv hy₀
  have hz₁ : (extChartAt IM x).symm ((extChartAt IM x) ((extChartAt IM x₀).symm y)) = z := by
    dsimp [z]
    exact (extChartAt IM x).left_inv hy₀s₁
  have hzint : y ∈ interior (range IM) := by
    have hyint : y ∈ interior ((extChartAt IM x₀).target) := hy.2
    exact interior_mono (by intro y hy; rw [extChartAt_target] at hy; exact hy.2) hyint
  have hfderiv : fderiv ℝ ((extChartAt IM x) ∘ (extChartAt IM x₀).symm) y =
      tangentCoordChange IM x₀ x z := by
    have hyy : z ∈ (extChartAt IM x₀).source ∩ (extChartAt IM x).source :=
      ⟨hy₀s, hy₀s₁⟩
    have hw : HasFDerivWithinAt ((extChartAt IM x) ∘ (extChartAt IM x₀).symm)
        (tangentCoordChange IM x₀ x z) (range IM) ((extChartAt IM x₀) z) :=
      hasFDerivWithinAt_tangentCoordChange (I := IM) (x := x₀) (y := x) (z := z) hyy
    have hw' : HasFDerivWithinAt ((extChartAt IM x) ∘ (extChartAt IM x₀).symm)
        (tangentCoordChange IM x₀ x z) (range IM) y := by
      rwa [hyz] at hw
    exact (hw'.hasFDerivAt (mem_interior_iff_mem_nhds.mp hzint)).fderiv
  rw [hfderiv]
  have hz₀ : (extChartAt IM x₀).symm y = z := rfl
  rw [hz₀]
  change (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
        (Bundle.Trivial M ℝ)) x₀ ⟨z, α z⟩).2 =
    (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
        (Bundle.Trivial M ℝ)) x ⟨(extChartAt IM x).symm ((extChartAt IM x) z),
          α ((extChartAt IM x).symm ((extChartAt IM x) z))⟩).2.compContinuousLinearMap
          (tangentCoordChange IM x₀ x z)
  rw [hz₁]
  exact (localRep_eq_pullback (IM := IM) (M := M) (x₀ := x) (x := x₀) (z := z)
    (hx := hy₀s) (hx₀ := hy₀s₁) (m := k) (L := α z))

private noncomputable def exteriorDerivativeAtRaw (α : DifferentialForm IM M k)
    (x : {x : M // ModelWithCorners.IsInteriorPoint IM x}) :
    Bundle.continuousAlternatingMap ℝ (Fin (k + 1)) EM (TangentSpace IM) ℝ
      (Bundle.Trivial M ℝ) x.1 :=
  (trivializationAt (EM [⋀^Fin (k + 1)]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin (k + 1)) EM (TangentSpace IM) ℝ
        (Bundle.Trivial M ℝ)) x.1).symmL ℝ x.1
    (extDeriv (fun y : EM => (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x.1
          ⟨(extChartAt IM x.1).symm y, α ((extChartAt IM x.1).symm y)⟩).2)
      ((extChartAt IM x.1) x.1))

noncomputable def exteriorDerivativeAtInterior (α : DifferentialForm IM M k) (x : M)
    (hxi : ModelWithCorners.IsInteriorPoint IM x) :
    Bundle.continuousAlternatingMap ℝ (Fin (k + 1)) EM (TangentSpace IM) ℝ
      (Bundle.Trivial M ℝ) x :=
  exteriorDerivativeAtRaw α ⟨x, hxi⟩

noncomputable def exteriorDerivativeAt [BoundarylessManifold IM M]
    (α : DifferentialForm IM M k) (x : M) :
    Bundle.continuousAlternatingMap ℝ (Fin (k + 1)) EM (TangentSpace IM) ℝ
      (Bundle.Trivial M ℝ) x :=
  exteriorDerivativeAtInterior α x
    (BoundarylessManifold.isInteriorPoint (I := IM) (M := M) (x := x))

theorem exteriorDerivative_localRepresentation
    (α : DifferentialForm IM M k) {x₀ x : M}
    (hx : x ∈ (extChartAt IM x₀).source) (hxi : ModelWithCorners.IsInteriorPoint IM x) :
    (trivializationAt (EM [⋀^Fin (k + 1)]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin (k + 1)) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x₀ ⟨x, exteriorDerivativeAtInterior α x hxi⟩).2 =
      extDeriv (fun y : EM => (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
            (Bundle.Trivial M ℝ)) x₀ ⟨(extChartAt IM x₀).symm y, α ((extChartAt IM x₀).symm y)⟩).2)
        ((extChartAt IM x₀) x) := by
  let c₀ := extChartAt IM x₀
  let c₁ := extChartAt IM x
  let rep₀ : EM → EM [⋀^Fin k]→L[ℝ] ℝ := fun y =>
    (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
        (Bundle.Trivial M ℝ)) x₀ ⟨c₀.symm y, α (c₀.symm y)⟩).2
  let rep₁ : EM → EM [⋀^Fin k]→L[ℝ] ℝ := fun y =>
    (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
        (Bundle.Trivial M ℝ)) x ⟨c₁.symm y, α (c₁.symm y)⟩).2
  let ψ : EM → EM := c₁ ∘ c₀.symm
  let R : EM [⋀^Fin (k + 1)]→L[ℝ] ℝ :=
    (trivializationAt (EM [⋀^Fin (k + 1)]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin (k + 1)) EM (TangentSpace IM) ℝ
        (Bundle.Trivial M ℝ)) x₀ ⟨x, exteriorDerivativeAtInterior α x hxi⟩).2
  let S : EM [⋀^Fin (k + 1)]→L[ℝ] ℝ := extDeriv rep₀ (c₀ x)
  let Z := extDeriv rep₁ (c₁ x)
  let C := tangentCoordChange IM x x₀ x
  let D := tangentCoordChange IM x₀ x x
  have hxsrc₁ : x ∈ (extChartAt IM x).source := by
    rw [extChartAt_source]
    exact mem_chart_source (H := HM) x
  have hψx : ψ (c₀ x) = c₁ x := by
    change (extChartAt IM x) ((extChartAt IM x₀).symm ((extChartAt IM x₀) x)) = (extChartAt IM x) x
    rw [show (extChartAt IM x₀).symm ((extChartAt IM x₀) x) = x by
      exact (extChartAt IM x₀).left_inv hx]
  have hD : C ∘L D = ContinuousLinearMap.id ℝ EM := by
    simpa [C, D] using tangentCoordChange_comp_self (IM := IM) hx
  have hX : (trivializationAt (EM [⋀^Fin (k + 1)]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin (k + 1)) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x ⟨x,
          (trivializationAt (EM [⋀^Fin (k + 1)]→L[ℝ] ℝ)
            (Bundle.continuousAlternatingMap ℝ (Fin (k + 1)) EM (TangentSpace IM) ℝ
              (Bundle.Trivial M ℝ)) x).symmL ℝ x Z⟩).2 = Z := by
    let e := trivializationAt (EM [⋀^Fin (k + 1)]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin (k + 1)) EM (TangentSpace IM) ℝ
        (Bundle.Trivial M ℝ)) x
    have hb : x ∈ e.baseSet := mem_baseSet_trivializationAt (EM [⋀^Fin (k + 1)]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin (k + 1)) EM (TangentSpace IM) ℝ
        (Bundle.Trivial M ℝ)) x
    calc
      (e ⟨x, e.symmL ℝ x Z⟩).2 = e.linearMapAt ℝ x (e.symmL ℝ x Z) := by
        rw [Trivialization.coe_linearMapAt_of_mem e hb]
      _ = Z := Trivialization.linearMapAt_symmₗ (R := ℝ) e hb Z
  have hpb : (trivializationAt (EM [⋀^Fin (k + 1)]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin (k + 1)) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x ⟨x, exteriorDerivativeAtInterior α x hxi⟩).2 =
      R.compContinuousLinearMap C := by
    simpa [R, C] using localRep_eq_pullback (IM := IM) (M := M) (x₀ := x₀) (x := x) (z := x)
      (m := k + 1) (L := exteriorDerivativeAtInterior α x hxi) hxsrc₁ hx
  have hZ : Z = R.compContinuousLinearMap C := by
    dsimp [Z, exteriorDerivativeAtInterior, exteriorDerivativeAtRaw]
    exact hX.symm.trans hpb
  have hR : R = Z.compContinuousLinearMap D := by
    calc
      R = R.compContinuousLinearMap (C ∘L D) := by
        rw [hD]
        ext v
        rfl
      _ = (R.compContinuousLinearMap C).compContinuousLinearMap D := by
        rfl
      _ = Z.compContinuousLinearMap D := by rw [← hZ]
  have hω : DifferentiableAt ℝ rep₁ (ψ (c₀ x)) := by
    rw [hψx]
    have hmem : (extChartAt IM x) x ∈ interior ((extChartAt IM x).target) :=
      chartTarget_interior_of (IM := IM) (M := M) (x₀ := x) (x := x) (hx := by simp) hxi
    exact ((localRep_contDiffOn α x).contDiffAt
      (mem_interior_iff_mem_nhds.mp hmem)).differentiableAt (by norm_num)
  have hf : ContDiffAt ℝ ∞ ψ (c₀ x) := by
    have hsrc : (extChartAt IM x₀) x ∈
        ((extChartAt IM x₀).symm ≫ (extChartAt IM x)).source := by
      rw [PartialEquiv.trans_source]
      exact ⟨(extChartAt IM x₀).map_source hx, by
        change (extChartAt IM x₀).symm ((extChartAt IM x₀) x) ∈ (extChartAt IM x).source
        rw [show (extChartAt IM x₀).symm ((extChartAt IM x₀) x) = x by
          exact (extChartAt IM x₀).left_inv hx]
        exact mem_extChartAt_source x⟩
    have hc : ContDiffWithinAt ℝ ∞ ψ (range IM) (c₀ x) := by
      dsimp [ψ, c₀, c₁]
      exact contDiffWithinAt_ext_coord_change (I := IM) x x₀ hsrc
    have hmem₀ : (extChartAt IM x₀) x ∈ interior (range IM) := by
      have hx₀target : (extChartAt IM x₀) x ∈ interior ((extChartAt IM x₀).target) :=
        (ModelWithCorners.isInteriorPoint_iff_of_mem_atlas (I := IM) (n := 1)
          (e := (chartAt HM x₀)) (hn := by norm_num)
          (he := chart_mem_atlas (H := HM) x₀)
          (hx := by simpa [extChartAt_source] using hx)).1 hxi
      exact interior_mono (by intro y hy; rw [extChartAt_target] at hy; exact hy.2) hx₀target
    exact hc.contDiffAt (by simpa [c₀] using (mem_interior_iff_mem_nhds.mp hmem₀))
  have hS : S = Z.compContinuousLinearMap D := by
    have h1 : S = extDeriv (fun y => ((rep₁ ∘ ψ) y).compContinuousLinearMap (fderiv ℝ ψ y))
      (c₀ x) := by
      refine Filter.EventuallyEq.extDeriv_eq ?_
      simpa [rep₀, rep₁, ψ, c₀, c₁, Function.comp_def] using!
        rep_eqOn_pullback (IM := IM) (M := M) (α := α) hx hxi
    have h2 : extDeriv (fun y => ((rep₁ ∘ ψ) y).compContinuousLinearMap (fderiv ℝ ψ y)) (c₀ x) =
        (extDeriv rep₁ (ψ (c₀ x))).compContinuousLinearMap (fderiv ℝ ψ (c₀ x)) := by
      have h := @extDeriv_pullback ℝ EM EM ℝ _ _ _ _ _ _ _ k ∞ (c₀ x) rep₁ ψ hω hf
        (by
          rw [minSmoothness_of_isRCLikeNormedField]
          exact ENat.LEInfty.out)
      change extDeriv
        (fun y => (rep₁ (ψ y)).compContinuousLinearMap (fderiv ℝ ψ y)) (c₀ x) =
          (extDeriv rep₁ (ψ (c₀ x))).compContinuousLinearMap (fderiv ℝ ψ (c₀ x))
      exact h
    have h3 : (extDeriv rep₁ (ψ (c₀ x))).compContinuousLinearMap (fderiv ℝ ψ (c₀ x)) =
        Z.compContinuousLinearMap D := by
      calc
        (extDeriv rep₁ (ψ (c₀ x))).compContinuousLinearMap (fderiv ℝ ψ (c₀ x))
            = (extDeriv rep₁ (c₁ x)).compContinuousLinearMap D := by
              rw [hψx]
              have hfd : fderiv ℝ ψ (c₀ x) = D := by
                change fderiv ℝ ((extChartAt IM x) ∘ (extChartAt IM x₀).symm)
                  ((extChartAt IM x₀) x) =
                  tangentCoordChange IM x₀ x x
                exact fderiv_chartChange_rev_eq_tangentCoordChange (IM := IM) (M := M)
                  (x₀ := x₀) (x := x) hx hxi
              rw [hfd]
        _ = Z.compContinuousLinearMap D := rfl
    exact h1.trans (h2.trans h3)
  exact hR.trans hS.symm

private lemma exteriorDerivative_localRepresentation_contDiff [BoundarylessManifold IM M]
    (α : DifferentialForm IM M k) (x₀ : M) :
    ContDiffOn ℝ ∞ (fun y : EM => (trivializationAt (EM [⋀^Fin (k + 1)]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin (k + 1)) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x₀ ⟨(extChartAt IM x₀).symm y,
            exteriorDerivativeAt α ((extChartAt IM x₀).symm y)⟩).2)
      (interior ((extChartAt IM x₀).target)) := by
  have htarget : IsOpen (interior ((extChartAt IM x₀).target)) := isOpen_interior
  have hrep : ContDiffOn ℝ ∞ (fun y : EM => (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
        (Bundle.Trivial M ℝ)) x₀ ⟨(extChartAt IM x₀).symm y, α ((extChartAt IM x₀).symm y)⟩).2)
      ((extChartAt IM x₀).target) :=
    localRep_contDiffOn α x₀
  have hdrep : ContDiffOn ℝ ∞ (fun y : EM => extDeriv (fun y : EM =>
      (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x₀ ⟨(extChartAt IM x₀).symm y, α ((extChartAt IM x₀).symm y)⟩).2) y)
      (interior ((extChartAt IM x₀).target)) :=
    contDiffOn_extDeriv_infty (fun y : EM => (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
        (Bundle.Trivial M ℝ)) x₀ ⟨(extChartAt IM x₀).symm y, α ((extChartAt IM x₀).symm y)⟩).2)
      (hrep.mono interior_subset) htarget
  have hdrep' : ContDiffOn ℝ ∞ (fun y : EM => (trivializationAt (EM [⋀^Fin (k + 1)]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin (k + 1)) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x₀ ⟨(extChartAt IM x₀).symm y,
            exteriorDerivativeAt α ((extChartAt IM x₀).symm y)⟩).2)
      (interior ((extChartAt IM x₀).target)) :=
    hdrep.congr (by
      intro y hy
      have hx₀int : ModelWithCorners.IsInteriorPoint IM ((extChartAt IM x₀).symm y) := by
        have hx₀target : (extChartAt IM x₀) ((extChartAt IM x₀).symm y) ∈ interior
          ((extChartAt IM x₀).target) := by
          rw [(extChartAt IM x₀).right_inv (interior_subset hy)]
          exact hy
        exact (ModelWithCorners.isInteriorPoint_iff_of_mem_atlas (I := IM) (n := 1)
          (e := (chartAt HM x₀)) (hn := by norm_num)
          (he := chart_mem_atlas (H := HM) x₀)
          (hx := by
            simpa [extChartAt_source] using (extChartAt IM x₀).map_target
              (interior_subset hy))).2 hx₀target
      have hx₀source :
          (extChartAt IM x₀).symm y ∈ (extChartAt IM x₀).source := by
        simpa [extChartAt_source] using
          (extChartAt IM x₀).map_target (interior_subset hy)
      have hlocal := exteriorDerivative_localRepresentation (IM := IM) (M := M) (α := α)
        (x₀ := x₀) (x := (extChartAt IM x₀).symm y)
        hx₀source hx₀int
      have hlocal' : (trivializationAt (EM [⋀^Fin (k + 1)]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin (k + 1)) EM (TangentSpace IM) ℝ
            (Bundle.Trivial M ℝ)) x₀ ⟨(extChartAt IM x₀).symm y,
              exteriorDerivativeAt α ((extChartAt IM x₀).symm y)⟩).2 =
          extDeriv (fun y : EM => (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
              (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
                (Bundle.Trivial M ℝ)) x₀ ⟨(extChartAt IM x₀).symm y,
                  α ((extChartAt IM x₀).symm y)⟩).2) y := by
        rw [show (extChartAt IM x₀) ((extChartAt IM x₀).symm y) = y by
          exact (extChartAt IM x₀).right_inv (interior_subset hy)] at hlocal
        exact hlocal
      exact hlocal')
  exact hdrep'

noncomputable def exteriorDerivative [BoundarylessManifold IM M] (α : DifferentialForm IM M k) :
    DifferentialForm IM M (k + 1) :=
  ⟨fun x => exteriorDerivativeAt α x, by
    intro x₀
    let e := trivializationAt (EM [⋀^Fin (k + 1)]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin (k + 1)) EM (TangentSpace IM) ℝ
        (Bundle.Trivial M ℝ)) x₀
    rw [Bundle.Trivialization.contMDiffAt_section_iff e
      (mem_baseSet_trivializationAt (EM [⋀^Fin (k + 1)]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin (k + 1)) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x₀)]
    have hmap : (extChartAt IM x₀) x₀ ∈ (extChartAt IM x₀).target :=
      (extChartAt IM x₀).map_source (mem_extChartAt_source x₀)
    have hopen : IsOpen (IM.symm ⁻¹' (chartAt HM x₀).target ∩ interior (range IM)) :=
      ((chartAt HM x₀).open_target.preimage IM.continuous_symm).inter isOpen_interior
    have hsubset : IM.symm ⁻¹' (chartAt HM x₀).target ∩ interior (range IM) ⊆
        (extChartAt IM x₀).target := by
      intro y hy
      rw [extChartAt_target]
      exact ⟨hy.1, interior_subset hy.2⟩
    have hmem : (extChartAt IM x₀) x₀ ∈ interior ((extChartAt IM x₀).target) :=
      mem_interior.mpr ⟨IM.symm ⁻¹' (chartAt HM x₀).target ∩ interior (range IM),
        hsubset, hopen, by
          rw [extChartAt_target] at hmap
          exact ⟨hmap.1, BoundarylessManifold.isInteriorPoint (I := IM) (M := M) (x := x₀)⟩⟩
    have hloc : ContMDiffOn 𝓘(ℝ, EM) 𝓘(ℝ, EM [⋀^Fin (k + 1)]→L[ℝ] ℝ) ∞
        (fun y : EM => (trivializationAt (EM [⋀^Fin (k + 1)]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin (k + 1)) EM (TangentSpace IM) ℝ
            (Bundle.Trivial M ℝ)) x₀ ⟨(extChartAt IM x₀).symm y,
              exteriorDerivativeAt α ((extChartAt IM x₀).symm y)⟩).2)
        (interior ((extChartAt IM x₀).target)) :=
      contMDiffOn_iff_contDiffOn.mpr (exteriorDerivative_localRepresentation_contDiff α x₀)
    have hsec : ContMDiffOn IM 𝓘(ℝ, EM [⋀^Fin (k + 1)]→L[ℝ] ℝ) ∞
        (fun x : M => (trivializationAt (EM [⋀^Fin (k + 1)]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin (k + 1)) EM (TangentSpace IM) ℝ
            (Bundle.Trivial M ℝ)) x₀ ⟨x, exteriorDerivativeAt α x⟩).2)
        ((extChartAt IM x₀).source) :=
      by
        intro x hx
        have hx₀ : (extChartAt IM x₀) x ∈ (extChartAt IM x₀).target :=
          (extChartAt IM x₀).map_source hx
        have hxint : (extChartAt IM x₀) x ∈ interior ((extChartAt IM x₀).target) := by
          have hxint₀ : ModelWithCorners.IsInteriorPoint IM x :=
            BoundarylessManifold.isInteriorPoint (I := IM) (M := M) (x := x)
          exact (ModelWithCorners.isInteriorPoint_iff_of_mem_atlas (I := IM) (n := 1)
            (e := (chartAt HM x₀)) (hn := by norm_num)
            (he := chart_mem_atlas (H := HM) x₀)
            (hx := by simpa [extChartAt_source] using hx)).1 hxint₀
        have hxint' : (extChartAt IM x₀) x ∈ interior (interior ((extChartAt IM x₀).target)) :=
          mem_interior.mpr ⟨interior ((extChartAt IM x₀).target),
            subset_rfl, isOpen_interior, hxint⟩
        have hlocAt : ContMDiffAt 𝓘(ℝ, EM) 𝓘(ℝ, EM [⋀^Fin (k + 1)]→L[ℝ] ℝ) ∞
            (fun y : EM => (trivializationAt (EM [⋀^Fin (k + 1)]→L[ℝ] ℝ)
              (Bundle.continuousAlternatingMap ℝ (Fin (k + 1)) EM (TangentSpace IM) ℝ
                (Bundle.Trivial M ℝ)) x₀ ⟨(extChartAt IM x₀).symm y,
                  exteriorDerivativeAt α ((extChartAt IM x₀).symm y)⟩).2)
            ((extChartAt IM x₀) x) :=
          (contMDiffAt_iff_contDiffAt.mpr
            ((exteriorDerivative_localRepresentation_contDiff α x₀).contDiffAt
              (mem_interior_iff_mem_nhds.mp hxint')))
        have hchartAt : ContMDiffAt IM 𝓘(ℝ, EM) ∞ (extChartAt IM x₀) x :=
          contMDiffAt_extChartAt' (I := IM) (M := M) (x := x₀) (x' := x)
            (by simpa [extChartAt_source] using hx)
        have hcomp : ContMDiffWithinAt IM 𝓘(ℝ, EM [⋀^Fin (k + 1)]→L[ℝ] ℝ) ∞
            ((fun y : EM => (trivializationAt (EM [⋀^Fin (k + 1)]→L[ℝ] ℝ)
              (Bundle.continuousAlternatingMap ℝ (Fin (k + 1)) EM (TangentSpace IM) ℝ
                (Bundle.Trivial M ℝ)) x₀ ⟨(extChartAt IM x₀).symm y,
                  exteriorDerivativeAt α ((extChartAt IM x₀).symm y)⟩).2) ∘
              (extChartAt IM x₀))
            ((extChartAt IM x₀).source) x :=
          (hlocAt.comp x hchartAt).contMDiffWithinAt
        change ContMDiffWithinAt IM 𝓘(ℝ, EM [⋀^Fin (k + 1)]→L[ℝ] ℝ) ∞
          (fun x : M => (trivializationAt (EM [⋀^Fin (k + 1)]→L[ℝ] ℝ)
            (Bundle.continuousAlternatingMap ℝ (Fin (k + 1)) EM (TangentSpace IM) ℝ
              (Bundle.Trivial M ℝ)) x₀ ⟨x, exteriorDerivativeAt α x⟩).2)
          ((extChartAt IM x₀).source) x
        exact ContMDiffWithinAt.congr' hcomp
          (fun z hz => by
            rw [Function.comp_apply]
            rw [show (extChartAt IM x₀).symm ((extChartAt IM x₀) z) = z by
              exact (extChartAt IM x₀).left_inv (by simpa [extChartAt_source] using hz)])
          subset_rfl hx
    exact (hsec.contMDiffAt ((isOpen_extChartAt_source (I := IM) x₀).mem_nhds
      (mem_extChartAt_source x₀)))⟩

@[simp] theorem exteriorDerivative_apply [BoundarylessManifold IM M]
    (α : DifferentialForm IM M k) (x : M) :
    (exteriorDerivative α) x = exteriorDerivativeAt α x := rfl

theorem exteriorDerivative_add [BoundarylessManifold IM M] (α β : DifferentialForm IM M k) :
    exteriorDerivative (α + β) = exteriorDerivative α + exteriorDerivative β := by
  apply ContMDiffSection.ext
  intro x
  have hα : DifferentiableAt ℝ (fun y : EM => (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x ⟨(extChartAt IM x).symm y, α ((extChartAt IM x).symm y)⟩).2)
      ((extChartAt IM x) x) := by
    have hmem : (extChartAt IM x) x ∈ interior ((extChartAt IM x).target) :=
      (ModelWithCorners.isInteriorPoint_iff (I := IM)).1
        (BoundarylessManifold.isInteriorPoint (I := IM) (M := M) (x := x))
    exact ((localRep_contDiffOn α x).contDiffAt
      (mem_interior_iff_mem_nhds.mp hmem)).differentiableAt (by norm_num)
  have hβ : DifferentiableAt ℝ (fun y : EM => (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x ⟨(extChartAt IM x).symm y, β ((extChartAt IM x).symm y)⟩).2)
      ((extChartAt IM x) x) := by
    have hmem : (extChartAt IM x) x ∈ interior ((extChartAt IM x).target) :=
      (ModelWithCorners.isInteriorPoint_iff (I := IM)).1
        (BoundarylessManifold.isInteriorPoint (I := IM) (M := M) (x := x))
    exact ((localRep_contDiffOn β x).contDiffAt
      (mem_interior_iff_mem_nhds.mp hmem)).differentiableAt (by norm_num)
  change exteriorDerivativeAt (α + β) x = exteriorDerivativeAt α x + exteriorDerivativeAt β x
  rw [exteriorDerivativeAt, exteriorDerivativeAtInterior, exteriorDerivativeAtRaw,
    exteriorDerivativeAt, exteriorDerivativeAtInterior, exteriorDerivativeAtRaw,
    exteriorDerivativeAt, exteriorDerivativeAtInterior, exteriorDerivativeAtRaw]
  have hsum : (fun y : EM => (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x ⟨(extChartAt IM x).symm y,
            (α + β) ((extChartAt IM x).symm y)⟩).2) =
      (fun y : EM => (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
            (Bundle.Trivial M ℝ)) x ⟨(extChartAt IM x).symm y, α ((extChartAt IM x).symm y)⟩).2) +
        (fun y : EM => (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
            (Bundle.Trivial M ℝ)) x ⟨(extChartAt IM x).symm y,
              β ((extChartAt IM x).symm y)⟩).2) := by
    funext y
    let z : M := (extChartAt IM x).symm y
    rw [add_apply]
    change (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x ⟨z, α z + β z⟩).2 =
      (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
            (Bundle.Trivial M ℝ)) x ⟨z, α z⟩).2 +
        (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
            (Bundle.Trivial M ℝ)) x ⟨z, β z⟩).2
    rw [continuousAlternatingMap_trivializationAt_apply (m := k) (IM := IM) (M := M) (x₀ := x)
      (x := z)
      (L := α z + β z),
      continuousAlternatingMap_trivializationAt_apply (m := k) (IM := IM) (M := M) (x₀ := x)
        (x := z)
      (L := α z),
      continuousAlternatingMap_trivializationAt_apply (m := k) (IM := IM) (M := M) (x₀ := x)
        (x := z)
      (L := β z)]
    rfl
  rw [hsum, extDeriv_add hα hβ]
  rw [map_add]

theorem exteriorDerivative_smul [BoundarylessManifold IM M] (c : ℝ) (α : DifferentialForm IM M k) :
    exteriorDerivative (c • α) = c • exteriorDerivative α := by
  apply ContMDiffSection.ext
  intro x
  change exteriorDerivativeAt (c • α) x = c • exteriorDerivativeAt α x
  rw [exteriorDerivativeAt, exteriorDerivativeAtInterior, exteriorDerivativeAtRaw,
    exteriorDerivativeAt, exteriorDerivativeAtInterior, exteriorDerivativeAtRaw]
  have hsmul : (fun y : EM => (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x ⟨(extChartAt IM x).symm y,
            (c • α) ((extChartAt IM x).symm y)⟩).2) =
      c • (fun y : EM => (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x ⟨(extChartAt IM x).symm y, α ((extChartAt IM x).symm y)⟩).2) := by
    funext y
    let z : M := (extChartAt IM x).symm y
    rw [smul_apply]
    change (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x ⟨z, c • α z⟩).2 =
      c • (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
            (Bundle.Trivial M ℝ)) x ⟨z, α z⟩).2
    rw [continuousAlternatingMap_trivializationAt_apply (m := k) (IM := IM) (M := M) (x₀ := x)
      (x := z)
      (L := c • α z),
      continuousAlternatingMap_trivializationAt_apply (m := k) (IM := IM) (M := M) (x₀ := x)
        (x := z)
      (L := α z)]
    rfl
  rw [hsmul, extDeriv_smul, map_smul]

noncomputable def exteriorDerivativeLinearMap [BoundarylessManifold IM M] (k : ℕ) :
    DifferentialForm IM M k →ₗ[ℝ] DifferentialForm IM M (k + 1) :=
  { toFun := exteriorDerivative
    map_add' := exteriorDerivative_add
    map_smul' := exteriorDerivative_smul }

end DifferentialForm
end CalabiYau

end
