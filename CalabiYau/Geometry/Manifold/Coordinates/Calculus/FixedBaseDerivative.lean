-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Geometry/Coordinates/Calculus/FixedBaseDerivative.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Manifold.Bundle.PartialMfderiv.Basic
public import CalabiYau.Geometry.Manifold.Connection.TensorNabla.InducedConnection
public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section


set_option autoImplicit false

open scoped Topology Manifold ContDiff

namespace CalabiYau

theorem mvfderiv_real_eq_mfderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners Real E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (f : M -> Real) (x : M) (V : TangentSpace I x) :
    mvfderiv (I := I) f x V =
      NormedSpace.fromTangentSpace (f x)
        (mfderiv I 𝓘(Real, Real) f x V) := by
  rfl

theorem mvfderiv_real_model_eq_fderiv
    (f : Real -> Real) (x : Real)
    (V : TangentSpace 𝓘(Real, Real) x) :
    mvfderiv (I := 𝓘(Real, Real)) f x V =
      fderiv Real f x (NormedSpace.fromTangentSpace x V) := by
  unfold mvfderiv
  rw [mfderiv_eq_fderiv]
  rfl

private theorem writtenInExtChartAt_real_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (f : M -> Real) (x : M) (y : E) :
    writtenInExtChartAt I 𝓘(Real, Real) x f y =
      f ((extChartAt I x).symm y) := by
  rw [writtenInExtChartAt, extChartAt_model_space_eq_id]
  rfl

theorem writtenInExtChartAt_diffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {f : M -> Real} {x p : M} {z : E}
    (hp : p ∈ (chartAt H x).source)
    (hz : z ∈ (extChartAt I x).target)
    (hpz : p = (extChartAt I x).symm z)
    (h : MDifferentiableAt I 𝓘(Real, Real) f p) :
    DifferentiableAt Real (writtenInExtChartAt I 𝓘(Real, Real) x f) z := by
  have hmd_within :
      MDifferentiableWithinAt 𝓘(Real, E) 𝓘(Real, Real)
        (f ∘ (extChartAt I x).symm) (Set.range I)
        (extChartAt I x p) := by
    exact (mdifferentiableAt_iff_source_of_mem_source
      (I := I) (I' := 𝓘(Real, Real)) (x := x) (x' := p) hp).mp h
  have hdiff_within :
      DifferentiableWithinAt Real (writtenInExtChartAt I 𝓘(Real, Real) x f)
        (Set.range I) (extChartAt I x p) := by
    rw [show writtenInExtChartAt I 𝓘(Real, Real) x f =
      f ∘ (extChartAt I x).symm from funext (writtenInExtChartAt_real_apply f x)]
    exact hmd_within.differentiableWithinAt
  have hrange : Set.range I ∈ nhds z := by
    rw [ModelWithCorners.Boundaryless.range_eq_univ (I := I)]
    exact Filter.univ_mem
  have hpoint : extChartAt I x p = z := by
    rw [hpz]
    exact (extChartAt I x).right_inv hz
  rw [hpoint] at hdiff_within
  exact hdiff_within.differentiableAt hrange

theorem mvfderiv_tangentConstInChart_eq_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {f : M -> Real} {x p : M}
    (hp : p ∈ (chartAt H x).source)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f p)
    (v : E) :
    mvfderiv (I := I) f p
        (TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I) x v p) =
      fderiv Real (writtenInExtChartAt I 𝓘(Real, Real) x f) (extChartAt I x p) v := by
  let z : E := extChartAt I x p
  have hsource : p ∈ (extChartAt I x).source := by
    simpa [extChartAt_source] using hp
  have hz_target : z ∈ (extChartAt I x).target := by
    simpa [z] using (extChartAt I x).map_source hsource
  have hsymm : (extChartAt I x).symm z = p := by
    simpa [z] using (extChartAt I x).left_inv hsource
  have hrange : Set.range I ∈ nhds z := by
    rw [ModelWithCorners.Boundaryless.range_eq_univ (I := I)]
    exact Filter.univ_mem
  have hsymm_mdiff :
      MDifferentiableWithinAt 𝓘(Real, E) I (extChartAt I x).symm
        (Set.range I) z := by
    simpa [z] using mdifferentiableWithinAt_extChartAt_symm (I := I) hz_target
  have hf_univ :
      MDifferentiableWithinAt I 𝓘(Real, Real) f Set.univ
        ((extChartAt I x).symm z) := by
    rw [hsymm]
    exact hf.mdifferentiableWithinAt
  have hmaps :
      Set.range I ⊆ (extChartAt I x).symm ⁻¹' (Set.univ : Set M) := by
    intro y hy
    simp
  have huniq : UniqueMDiffWithinAt 𝓘(Real, E) (Set.range I) z := by
    exact (I.uniqueDiffOn.uniqueDiffWithinAt
      (by exact extChartAt_target_subset_range (I := I) x hz_target)).uniqueMDiffWithinAt
  have hchain :=
    mfderivWithin_comp (I := 𝓘(Real, E)) (I' := I) (I'' := 𝓘(Real, Real))
      (x := z) (g := f) (f := (extChartAt I x).symm)
      hf_univ hsymm_mdiff hmaps huniq
  have hchain_apply :
      fderivWithin Real (writtenInExtChartAt I 𝓘(Real, Real) x f)
          (Set.range I) z v =
        NormedSpace.fromTangentSpace (𝕜 := Real) (f p)
          (mfderiv I 𝓘(Real, Real) f p
            ((mfderivWithin 𝓘(Real, E) I (extChartAt I x).symm
              (Set.range I) z) v)) := by
    have happ := congrArg (fun L => L v) hchain
    rw [mfderivWithin_univ, hsymm] at happ
    have happ' := congrArg (NormedSpace.fromTangentSpace (𝕜 := Real) (f p)) happ
    calc
      fderivWithin Real (writtenInExtChartAt I 𝓘(Real, Real) x f)
          (Set.range I) z v =
          NormedSpace.fromTangentSpace (𝕜 := Real) (f p)
            ((mfderivWithin 𝓘(Real, E) 𝓘(Real, Real)
              (f ∘ (extChartAt I x).symm) (Set.range I) z) v) := by
        rw [mfderivWithin_eq_fderivWithin]
        simp [writtenInExtChartAt, NormedSpace.fromTangentSpace]
        rfl
      _ = NormedSpace.fromTangentSpace (𝕜 := Real) (f p)
          ((mfderiv I 𝓘(Real, Real) f p ∘L
            mfderivWithin 𝓘(Real, E) I (extChartAt I x).symm
              (Set.range I) z) v) := happ'
      _ = NormedSpace.fromTangentSpace (𝕜 := Real) (f p)
          (mfderiv I 𝓘(Real, Real) f p
            ((mfderivWithin 𝓘(Real, E) I (extChartAt I x).symm
              (Set.range I) z) v)) := by
        exact congrArg (NormedSpace.fromTangentSpace (𝕜 := Real) (f p))
          (ContinuousLinearMap.comp_apply _ _ v)
  have hfield :
      TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I) x v p =
        (mfderivWithin 𝓘(Real, E) I (extChartAt I x).symm
          (Set.range I) z) v := by
    have hlin := TangentBundle.symmL_trivializationAt
      (𝕜 := Real) (I := I) (x₀ := x) (x := p) hp
    have happ := congrArg (fun L => L v) hlin
    change ((trivializationAt E (TangentSpace I) x).symmL Real p) v = _
    exact happ
  have hwithin_to_fderiv :
      fderivWithin Real (writtenInExtChartAt I 𝓘(Real, Real) x f)
          (Set.range I) z v =
        fderiv Real (writtenInExtChartAt I 𝓘(Real, Real) x f) z v := by
    rw [fderivWithin_of_mem_nhds hrange]
  calc
    mvfderiv (I := I) f p
          (TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I) x v p) =
        NormedSpace.fromTangentSpace (𝕜 := Real) (f p)
          (mfderiv I 𝓘(Real, Real) f p
            (TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I) x v p)) := by
      exact mvfderiv_real_eq_mfderiv I f p
        (TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I) x v p)
    _ = NormedSpace.fromTangentSpace (𝕜 := Real) (f p)
          (mfderiv I 𝓘(Real, Real) f p
            ((mfderivWithin 𝓘(Real, E) I (extChartAt I x).symm
              (Set.range I) z) v)) := by rw [hfield]
    _ = fderivWithin Real (writtenInExtChartAt I 𝓘(Real, Real) x f)
          (Set.range I) z v := hchain_apply.symm
    _ = fderiv Real (writtenInExtChartAt I 𝓘(Real, Real) x f) z v := hwithin_to_fderiv

theorem isLocallyConstant_of_mfderiv_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {f : M -> Real}
    (hf : MDifferentiable I 𝓘(Real, Real) f)
    (hzero : ∀ x : M, mfderiv I 𝓘(Real, Real) f x = 0) :
    IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  let e := extChartAt I x
  let F : E -> Real := writtenInExtChartAt I 𝓘(Real, Real) x f
  have hFdiff : DifferentiableOn Real F e.target := by
    intro z hz
    let p : M := e.symm z
    have hp_ext : p ∈ e.source := e.map_target hz
    have hp_chart : p ∈ (chartAt H x).source := by
      simpa [e, extChartAt_source] using hp_ext
    exact
      (writtenInExtChartAt_diffAt (I := I) (f := f) hp_chart hz rfl
        (hf p)).differentiableWithinAt
  have hFzero : e.target.EqOn (fderiv Real F) 0 := by
    intro z hz
    ext v
    let p : M := e.symm z
    have hp_ext : p ∈ e.source := e.map_target hz
    have hp_chart : p ∈ (chartAt H x).source := by
      simpa [e, extChartAt_source] using hp_ext
    have hmap : e p = z := by
      exact e.right_inv hz
    have hder :=
      mvfderiv_tangentConstInChart_eq_fderiv (I := I) (f := f)
        (x := x) (p := p) hp_chart (hf p) v
    rw [hmap] at hder
    rw [← hder]
    simp [mvfderiv_real_eq_mfderiv, hzero p]
  have hopen :
      IsOpen (e.target ∩ F ⁻¹' ({F (e x)} : Set Real)) :=
    (isOpen_extChartAt_target (I := I) x).isOpen_inter_preimage_of_fderiv_eq_zero
      hFdiff hFzero ({F (e x)} : Set Real)
  have hxmem : e x ∈ e.target ∩ F ⁻¹' ({F (e x)} : Set Real) := by
    constructor
    · exact mem_extChartAt_target x
    · simp [F]
  have hpre :
      e ⁻¹' (e.target ∩ F ⁻¹' ({F (e x)} : Set Real)) ∈ nhds x :=
    (continuousAt_extChartAt (I := I) x).preimage_mem_nhds (hopen.mem_nhds hxmem)
  filter_upwards [hpre, extChartAt_source_mem_nhds (I := I) x] with y hy hysource
  have hxsource : x ∈ e.source := mem_extChartAt_source x
  have hFy : F (e y) = F (e x) := by
    simpa using hy.2
  have hsymm_y : e.symm (e y) = y := e.left_inv hysource
  have hsymm_x : e.symm (e x) = x := e.left_inv hxsource
  change f (e.symm (e y)) = f (e.symm (e x)) at hFy
  simpa [hsymm_y, hsymm_x] using hFy

end CalabiYau
