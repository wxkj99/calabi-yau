-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Tensor/Alternating/Bundle/Defs.lean
-- Locally modified.
/-
Copyright © 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
Coauthors: Jack McCarthy
-/
module
public import CalabiYau.Geometry.Manifold.Tensor.Alternating.Composition
public import Mathlib.Analysis.Normed.Module.Alternating.Curry
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Topology.VectorBundle.ContinuousAlternatingMap
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Data.Bundle

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open Bundle Set ContinuousAlternatingMap

section defs

variable (𝕜 : Type*) [CommSemiring 𝕜] (ι : Type*) [Fintype ι]
variable {B : Type*}

protected abbrev Bundle.continuousAlternatingMap (_F₁ : Type*) (E₁ : B → Type*)
    [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [∀ x, TopologicalSpace (E₁ x)]
    (_F₂ : Type*) (E₂ : B → Type*) [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
    [∀ x, TopologicalSpace (E₂ x)] (x : B) : Type _ :=
  E₁ x [⋀^ι]→L[𝕜] E₂ x

notation3 "⋀^" ι "⟮" 𝕜 "; " F₁ ", " E₁ "; " F₂ ", " E₂ "⟯" =>
  Bundle.continuousAlternatingMap 𝕜 ι F₁ E₁ F₂ E₂

end defs

section smooth

open scoped Bundle Manifold ContDiff

open Bundle Pretrivialization

variable {𝕜 ι B F₁ F₂ M : Type*} {E₁ : B → Type*} {E₂ : B → Type*}
  [NontriviallyNormedField 𝕜] [CharZero 𝕜]
  [Fintype ι]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB]
  (IB : ModelWithCorners 𝕜 EB HB)
  [TopologicalSpace B] [ChartedSpace HB B]
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [TopologicalSpace (Bundle.TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [TopologicalSpace (Bundle.TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM}
  {n : ℕ∞ω} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM n M]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  {e₁ e₁' : Trivialization F₁ (π F₁ E₁)}
  {e₂ e₂' : Trivialization F₂ (π F₂ E₂)}

variable {F₃ F₄ : Type*}
  [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  [NormedAddCommGroup F₄] [NormedSpace 𝕜 F₄]

local notation "AE₁E₂" =>
  Bundle.TotalSpace (F₁ [⋀^ι]→L[𝕜] F₂) ⋀^ι⟮𝕜; F₁, E₁; F₂, E₂⟯

omit [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)] in
theorem contMDiffOn_continuousAlternatingMapCoordChange
    [ContMDiffVectorBundle n F₁ E₁ IB] [ContMDiffVectorBundle n F₂ E₂ IB]
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁']
    [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] :
    ContMDiffOn IB 𝓘(𝕜, (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] F₁ [⋀^ι]→L[𝕜] F₂) n
      (continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂')
      (e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) := by
  have h₁ := contMDiffOn_coordChangeL (IB := IB) e₁' e₁ (n := n)
  have h₂ := contMDiffOn_coordChangeL (IB := IB) e₂ e₂' (n := n)
  have h₁_prod_h₂ := (h₁.mono (t := e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet))
    (s := e₁'.baseSet ∩ e₁.baseSet) (by mfld_set_tac)).prodMk
      (h₂.mono (t := e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet))
      (s := e₂.baseSet ∩ e₂'.baseSet) (by mfld_set_tac))
  let s (q : (F₁ →L[𝕜] F₁) × (F₂ →L[𝕜] F₂)) :
      (F₁ →L[𝕜] F₁) × ((F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂)) :=
    (q.1, ContinuousLinearMap.compContinuousAlternatingMapCLM 𝕜 F₁ F₂ F₂ ι q.2)
  have hs : ContMDiff (𝓘(𝕜, (F₁ →L[𝕜] F₁)).prod 𝓘(𝕜, (F₂ →L[𝕜] F₂)))
      (𝓘(𝕜, (F₁ →L[𝕜] F₁)).prod
        𝓘(𝕜, ((F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂)))) n s := by
    let t (p : (F₁ →L[𝕜] F₁) × (F₂ →L[𝕜] F₂)) :
        (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂) :=
      ContinuousLinearMap.compContinuousAlternatingMapCLM 𝕜 F₁ F₂ F₂ ι p.2
    have ht : ContMDiff (𝓘(𝕜, (F₁ →L[𝕜] F₁)).prod 𝓘(𝕜, (F₂ →L[𝕜] F₂)))
        𝓘(𝕜, ((F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂))) n t := by
      refine ContMDiff.clm_apply ?hg ?hf
      · exact contMDiff_const
      · exact contMDiff_snd
    exact ContMDiff.prodMk contMDiff_fst ht
  have hcomp : ContMDiff (𝓘(𝕜, F₁ →L[𝕜] F₁))
      𝓘(𝕜, (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂)) n
      (fun p => ContinuousAlternatingMap.compContinuousLinearMapCLM p) :=
    (ContinuousAlternatingMap.compContinuousLinearMapCLM_contMDiff
      (𝕜 := 𝕜) (ι := ι) (F₁ := F₁) (F₂ := F₂)).of_le le_top
  exact ((contMDiff_snd.clm_comp (hcomp.comp contMDiff_fst)).comp hs).comp_contMDiffOn
    (s := e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) h₁_prod_h₂

variable [ContMDiffVectorBundle n F₁ E₁ IB] [ContMDiffVectorBundle n F₂ E₂ IB]

instance Bundle.continuousAlternatingMap.vectorPrebundle.isSmooth :
    (Bundle.ContinuousAlternatingMap.vectorPrebundle 𝕜 ι F₁ E₁ F₂ E₂).IsContMDiff IB n where
  exists_contMDiffCoordChange := by
    rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩
    refine ⟨continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂',
      contMDiffOn_continuousAlternatingMapCoordChange IB, ?_⟩
    rintro b hb v
    apply continuousAlternatingMapCoordChange_apply
    exact hb

instance SmoothVectorBundle.continuousAlternatingMap :
    ContMDiffVectorBundle n (F₁ [⋀^ι]→L[𝕜] F₂)
      (Bundle.continuousAlternatingMap 𝕜 ι F₁ E₁ F₂ E₂) IB :=
  (Bundle.ContinuousAlternatingMap.vectorPrebundle 𝕜 ι F₁ E₁ F₂ E₂).contMDiffVectorBundle IB

notation "𝒜⟮" 𝕜 "," ι ";" F₁ "," E₁ ";" F₂ "," E₂ "⟯" =>
  Bundle.TotalSpace (F₁ [⋀^ι]→L[𝕜] F₂) ⋀^ι⟮𝕜; F₁, E₁; F₂, E₂⟯

end smooth

namespace ContinuousAlternatingMap

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem curryLeft_contMDiff {m : ℕ} :
    ContMDiff 𝓘(ℝ, E [⋀^Fin (m + 1)]→L[ℝ] ℝ)
      𝓘(ℝ, E →L[ℝ] E [⋀^Fin m]→L[ℝ] ℝ) ∞
      (fun a : E [⋀^Fin (m + 1)]→L[ℝ] ℝ => a.curryLeft) := by
  rw [contMDiff_iff_contDiff]
  have hlin : IsLinearMap ℝ
      (fun a : E [⋀^Fin (m + 1)]→L[ℝ] ℝ => a.curryLeft) :=
    { map_add := ContinuousAlternatingMap.curryLeft_add
      map_smul := ContinuousAlternatingMap.curryLeft_smul }
  have hbound : ∀ a : E [⋀^Fin (m + 1)]→L[ℝ] ℝ,
      ‖a.curryLeft‖ ≤ 1 * ‖a‖ := by
    intro a
    simp
  exact IsBoundedLinearMap.contDiff (n := ∞) (hlin.with_bound 1 hbound)

end ContinuousAlternatingMap

open scoped Topology Manifold ContDiff

noncomputable section charted

variable
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM]
  (IM : ModelWithCorners ℝ EM HM)
  (M : Type*) [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ∞ M]
  {m : ℕ}

open Bundle Set Function Filter
namespace CalabiYau

@[instance_reducible]
def seminormedAddCommGroupTangentSpace (x : M) : SeminormedAddCommGroup (TangentSpace IM x) :=
  inferInstanceAs (SeminormedAddCommGroup EM)

attribute [local instance] seminormedAddCommGroupTangentSpace

@[instance_reducible]
def normedAddCommGroupTangentSpace (x : M) : NormedAddCommGroup (TangentSpace IM x) :=
  inferInstanceAs (NormedAddCommGroup EM)

attribute [local instance] normedAddCommGroupTangentSpace

@[instance_reducible]
def normedSpaceTangentSpace (x : M) : NormedSpace ℝ (TangentSpace IM x) :=
  inferInstanceAs (NormedSpace ℝ EM)

attribute [local instance] normedSpaceTangentSpace

lemma continuousAlternatingMap_trivializationAt_apply (m : ℕ) (x₀ x : M)
    (L : Bundle.continuousAlternatingMap ℝ (Fin m) EM (TangentSpace IM) ℝ
      (Bundle.Trivial M ℝ) x) :
    (trivializationAt (EM [⋀^Fin m]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin m) EM (TangentSpace IM) ℝ
        (Bundle.Trivial M ℝ)) x₀ ⟨x, L⟩).2 =
      L.compContinuousLinearMap ((trivializationAt EM (TangentSpace IM) x₀).symmL ℝ x) := by
  rw [FiberBundle.trivializationAt_continuousAlternatingMap_apply]
  ext v
  simp [ContinuousAlternatingMap.inCoordinates]

end CalabiYau

instance ChartedSpace.alternatingBundle : ChartedSpace (ModelProd HM (EM [⋀^Fin m]→L[ℝ] ℝ))
    𝒜⟮ℝ,Fin m;EM,TangentSpace IM;ℝ,Bundle.Trivial M ℝ⟯ := inferInstance

end charted

noncomputable section curryBundle

open Bundle Set
open scoped Manifold ContDiff Topology

namespace ContinuousAlternatingMap

universe uE uH uM uF uV

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {V : M → Type uV} [∀ x, NormedAddCommGroup (V x)]
variable [∀ x, NormedSpace ℝ (V x)]
variable [totalSpaceTopology : TopologicalSpace (TotalSpace F V)]
variable [fiberBundle : FiberBundle F V]
variable [vectorBundle : VectorBundle ℝ F V]
variable [smoothVectorBundle : ContMDiffVectorBundle ∞ F V I]

private theorem trivializationAt_apply
    (m : ℕ) (x₀ x : M)
    (L : Bundle.continuousAlternatingMap ℝ (Fin m) F V ℝ
      (Bundle.Trivial M ℝ) x) :
    (trivializationAt (F [⋀^Fin m]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin m) F V ℝ
        (Bundle.Trivial M ℝ)) x₀ ⟨x, L⟩).2 =
      L.compContinuousLinearMap ((trivializationAt F V x₀).symmL ℝ x) := by
  rw [FiberBundle.trivializationAt_continuousAlternatingMap_apply]
  ext v
  simp [ContinuousAlternatingMap.inCoordinates]

noncomputable local instance curryTopology (m : ℕ) :
    TopologicalSpace (TotalSpace
      (F →L[ℝ] F [⋀^Fin m]→L[ℝ] ℝ)
      (fun x : M => V x →L[ℝ] V x [⋀^Fin m]→L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ)
    F V (F [⋀^Fin m]→L[ℝ] ℝ)
      (fun x : M => V x [⋀^Fin m]→L[ℝ] ℝ)

noncomputable local instance curryFiber (m : ℕ) :
    FiberBundle (F →L[ℝ] F [⋀^Fin m]→L[ℝ] ℝ)
      (fun x : M => V x →L[ℝ] V x [⋀^Fin m]→L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id ℝ)
    F V (F [⋀^Fin m]→L[ℝ] ℝ)
      (fun x : M => V x [⋀^Fin m]→L[ℝ] ℝ)

theorem contMDiffOn_curryLeft
    {m : ℕ} {W : Set M}
    (form : (x : M) → V x [⋀^Fin (m + 1)]→L[ℝ] ℝ)
    (hform : ContMDiffOn I (I.prod 𝓘(ℝ, F [⋀^Fin (m + 1)]→L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (F [⋀^Fin (m + 1)]→L[ℝ] ℝ) x (form x)) W) :
    ContMDiffOn I (I.prod 𝓘(ℝ, F →L[ℝ] F [⋀^Fin m]→L[ℝ] ℝ)) ∞
      (fun x => (⟨x, ContinuousAlternatingMap.curryLeft (form x)⟩ :
        TotalSpace (F →L[ℝ] F [⋀^Fin m]→L[ℝ] ℝ)
          (fun y : M => V y →L[ℝ] V y [⋀^Fin m]→L[ℝ] ℝ))) W := by
  intro x hx
  let e := trivializationAt F V x
  let ea := trivializationAt (F [⋀^Fin m]→L[ℝ] ℝ)
    (Bundle.continuousAlternatingMap ℝ (Fin m) F V ℝ
      (Bundle.Trivial M ℝ)) x
  let eh := e.continuousLinearMap (RingHom.id ℝ) ea
  have he : x ∈ e.baseSet := mem_baseSet_trivializationAt F V x
  have hea : x ∈ ea.baseSet := by
    change x ∈ e.baseSet ∩ Set.univ
    exact ⟨he, Set.mem_univ x⟩
  have heh : x ∈ eh.baseSet := ⟨he, hea⟩
  apply (eh.contMDiffWithinAt_section W heh).mpr
  let ef := trivializationAt (F [⋀^Fin (m + 1)]→L[ℝ] ℝ)
    (Bundle.continuousAlternatingMap ℝ (Fin (m + 1)) F V ℝ
      (Bundle.Trivial M ℝ)) x
  have hef : x ∈ ef.baseSet := by
    change x ∈ e.baseSet ∩ Set.univ
    exact ⟨he, Set.mem_univ x⟩
  have hcoord : ContMDiffWithinAt I 𝓘(ℝ, F [⋀^Fin (m + 1)]→L[ℝ] ℝ) ∞
      (fun y => (ef ⟨y, form y⟩).2) W x :=
    (ef.contMDiffWithinAt_section W hef).mp (hform x hx)
  have hcurry : ContMDiffWithinAt I 𝓘(ℝ, F →L[ℝ] F [⋀^Fin m]→L[ℝ] ℝ) ∞
      (fun y => (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := F)
        (F := ℝ) (n := m)) ((ef ⟨y, form y⟩).2)) W x := by
    have hcomp :=
      (ContinuousAlternatingMap.curryLeft_contMDiff (E := F) (m := m)).contMDiffAt
        |>.comp_contMDiffWithinAt x hcoord
    apply hcomp.congr_of_eventuallyEq_of_mem
    · filter_upwards with a
      rfl
    · exact hx
  apply hcurry.congr_of_eventuallyEq_of_mem
  · have heventually : ∀ᶠ y in 𝓝[W] x, y ∈ e.baseSet :=
      Filter.Eventually.filter_mono inf_le_left (e.open_baseSet.mem_nhds he)
    filter_upwards [heventually] with y hy
    change (eh ⟨y, (form y).curryLeft⟩).2 =
      (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := F)
        (F := ℝ) (n := m)) ((ef ⟨y, form y⟩).2)
    rw [Bundle.Trivialization.continuousLinearMap_apply]
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousAlternatingMap.ext
    intro w
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    have hya : y ∈ ea.baseSet := by
      change y ∈ e.baseSet ∩ Set.univ
      exact ⟨hy, Set.mem_univ y⟩
    rw [ea.continuousLinearMapAt_apply_of_mem (R := ℝ) hya]
    rw [trivializationAt_apply (m := m) (F := F) (V := V)
      (M := M) (x₀ := x) (x := y)]
    rw [trivializationAt_apply (m := m + 1) (F := F) (V := V)
      (M := M) (x₀ := x) (x := y)]
    simpa only [ContinuousAlternatingMap.curryLeftLI_apply, e] using
      (congrArg (fun L : F [⋀^Fin m]→L[ℝ] ℝ => L w)
        (ContinuousAlternatingMap.curryLeft_compContinuousLinearMap
          (form y) ((trivializationAt F V x).symmL ℝ y) v)).symm
  · exact hx

end ContinuousAlternatingMap

end curryBundle
