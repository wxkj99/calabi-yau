-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Geometry/Coordinates/Calculus/FixedBaseDerivative.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Manifold.Bundle.PartialMfderiv.ModelMixed
public import CalabiYau.Geometry.Manifold.Connection.TensorNabla.InducedConnection
public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

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

theorem mvfderiv_comp_diffeomorph
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace H N]
    (f : N -> Real) (Phi : M ≃ₘ⟮I, I⟯ N) (x : M)
    (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f (Phi x)) :
    mvfderiv (I := I) (fun y : M => f (Phi y)) x v =
      mvfderiv (I := I) f (Phi x) (mfderiv I I (Phi : M -> N) x v) := by
  have hPhi : MDifferentiableAt I I (Phi : M -> N) x :=
    Phi.mdifferentiable (by decide : (∞ : WithTop ℕ∞) ≠ 0) x
  rw [mvfderiv_real_eq_mfderiv, mvfderiv_real_eq_mfderiv]
  exact congrArg (NormedSpace.fromTangentSpace (f (Phi x)))
    (mfderiv_comp_apply (I := I) (I' := I) (I'' := 𝓘(Real, Real)) x hf hPhi v)

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

theorem mvfderiv_eq_fderiv_of_writtenInExtChartAt_eventuallyEq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {f : M -> Real} {φ : E -> Real} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hφ :
      writtenInExtChartAt I 𝓘(Real, Real) x f
        =ᶠ[nhds (extChartAt I x x)] φ)
    (V : TangentSpace I x) :
    mvfderiv (I := I) f x V =
      fderiv Real φ (extChartAt I x x) V := by
  let z₀ : E := extChartAt I x x
  have hrange : Set.range I ∈ nhds z₀ := by
    rw [ModelWithCorners.Boundaryless.range_eq_univ (I := I)]
    exact Filter.univ_mem
  calc
    mvfderiv (I := I) f x V =
        NormedSpace.fromTangentSpace (𝕜 := Real) (f x)
          (mfderiv I 𝓘(Real, Real) f x V) := by
          exact mvfderiv_real_eq_mfderiv I f x V
    _ = fderivWithin Real
          (writtenInExtChartAt I 𝓘(Real, Real) x f)
          (Set.range I) z₀ V := by
          dsimp only [z₀]
          exact congrArg (NormedSpace.fromTangentSpace (𝕜 := Real) (f x))
            (congrArg (fun L => L V) hf.mfderiv)
    _ = fderiv Real
          (writtenInExtChartAt I 𝓘(Real, Real) x f) z₀ V := by
          rw [fderivWithin_of_mem_nhds hrange]
    _ = fderiv Real φ z₀ V := by
          rw [hφ.fderiv_eq]

def FixedBaseExtDerivTimeDerivativeOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (timeSet : Set ℝ) (u : Set M)
    (F Ft : ℝ -> M -> ℝ) : Prop :=
  forall (t : ℝ) (x : M), x ∈ u ->
    forall V : TangentSpace I x,
      HasDerivWithinAt
        (fun s : ℝ => mvfderiv (I := I) (F s) x V)
        (mvfderiv (I := I) (Ft t) x V)
      timeSet
      t

def FixedBaseExtDerivTimeDerivativeOnRegular
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (timeSet regularSet : Set ℝ) (u : Set M)
    (F Ft : ℝ -> M -> ℝ) : Prop :=
  forall (t : ℝ), t ∈ regularSet ->
    forall (x : M), x ∈ u ->
      forall V : TangentSpace I x,
        HasDerivWithinAt
          (fun s : ℝ => mvfderiv (I := I) (F s) x V)
          (mvfderiv (I := I) (Ft t) x V)
          timeSet
          t

theorem fixedBaseExtDerivTimeDerivativeOn_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {timeSet : Set ℝ} {u : Set M}
    {F Ft : ℝ -> M -> ℝ}
    (h : FixedBaseExtDerivTimeDerivativeOn (I := I) timeSet u F Ft)
    {t : ℝ} {x : M} (hx : x ∈ u) (V : TangentSpace I x) :
    HasDerivWithinAt
      (fun s : ℝ => mvfderiv (I := I) (F s) x V)
      (mvfderiv (I := I) (Ft t) x V)
      timeSet
      t :=
  h t x hx V

theorem fixedBaseExtDerivTimeDerivativeOnRegular_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {timeSet regularSet : Set ℝ} {u : Set M}
    {F Ft : ℝ -> M -> ℝ}
    (h :
      FixedBaseExtDerivTimeDerivativeOnRegular
        (I := I) timeSet regularSet u F Ft)
    {t : ℝ} (ht : t ∈ regularSet) {x : M} (hx : x ∈ u)
    (V : TangentSpace I x) :
    HasDerivWithinAt
      (fun s : ℝ => mvfderiv (I := I) (F s) x V)
      (mvfderiv (I := I) (Ft t) x V)
      timeSet
      t :=
  h t ht x hx V

theorem FixedBaseExtDerivTimeDerivativeOn.toRegular
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {timeSet regularSet : Set ℝ} {u : Set M}
    {F Ft : ℝ -> M -> ℝ}
    (h : FixedBaseExtDerivTimeDerivativeOn (I := I) timeSet u F Ft) :
    FixedBaseExtDerivTimeDerivativeOnRegular
      (I := I) timeSet regularSet u F Ft := by
  intro t _ht x hx V
  exact h t x hx V

theorem fixedBaseExtDerivTimeDerivativeOn_singleton_of_chart_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {timeSet : Set Real} {x₀ : M}
    {F Ft : Real -> M -> Real} {Φ : Real -> E -> Real}
    (hΦ : ContDiff Real 2 (fun p : Real × E => Φ p.1 p.2))
    (hFdiff :
      ∀ s : Real, MDifferentiableAt I 𝓘(Real, Real) (F s) x₀)
    (hFchart :
      ∀ s : Real,
        writtenInExtChartAt I 𝓘(Real, Real) x₀ (F s)
          =ᶠ[nhds (extChartAt I x₀ x₀)] Φ s)
    (hFtdiff :
      ∀ t : Real, MDifferentiableAt I 𝓘(Real, Real) (Ft t) x₀)
    (hFtchart :
      ∀ t : Real,
        writtenInExtChartAt I 𝓘(Real, Real) x₀ (Ft t)
          =ᶠ[nhds (extChartAt I x₀ x₀)]
            fun y : E =>
              (fderiv Real (fun p : Real × E => Φ p.1 p.2) (t, y)) (1, 0)) :
    FixedBaseExtDerivTimeDerivativeOn (I := I) timeSet ({x₀} : Set M) F Ft := by
  intro t x hx V
  rw [Set.mem_singleton_iff] at hx
  subst x
  let z₀ : E := extChartAt I x₀ x₀
  have hmodel :=
    fixedBaseFDerivTimeDerivativeWithinAt_of_contDiff
      (E := E) Φ hΦ (timeSet := timeSet) (t := t) z₀ V
  have hleft :
      ∀ s : Real,
        mvfderiv (I := I) (F s) x₀ V =
          fderiv Real (Φ s) z₀ V := by
    intro s
    exact
      mvfderiv_eq_fderiv_of_writtenInExtChartAt_eventuallyEq
        (I := I) (x := x₀) (f := F s) (φ := Φ s)
        (hFdiff s) (hFchart s) V
  have hright :
      mvfderiv (I := I) (Ft t) x₀ V =
        fderiv Real
          (fun y : E =>
            (fderiv Real (fun p : Real × E => Φ p.1 p.2) (t, y)) (1, 0))
          z₀ V := by
    exact
      mvfderiv_eq_fderiv_of_writtenInExtChartAt_eventuallyEq
        (I := I) (x := x₀) (f := Ft t)
        (φ := fun y : E =>
          (fderiv Real (fun p : Real × E => Φ p.1 p.2) (t, y)) (1, 0))
        (hFtdiff t) (hFtchart t) V
  exact
    (hmodel.congr
      (fun s _hs => hleft s)
      (hleft t)).congr_deriv hright.symm

theorem fixedBaseExtDerivTimeDerivativeOnRegular_singleton_of_chart_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {timeSet regularSet : Set Real} {x₀ : M}
    {F Ft : Real -> M -> Real} {Φ : Real -> E -> Real}
    (hΦ : ContDiff Real 2 (fun p : Real × E => Φ p.1 p.2))
    (hFdiff :
      ∀ s : Real, MDifferentiableAt I 𝓘(Real, Real) (F s) x₀)
    (hFchart :
      ∀ s : Real,
        writtenInExtChartAt I 𝓘(Real, Real) x₀ (F s)
          =ᶠ[nhds (extChartAt I x₀ x₀)] Φ s)
    (hFtdiff :
      ∀ t : Real, MDifferentiableAt I 𝓘(Real, Real) (Ft t) x₀)
    (hFtchart :
      ∀ t : Real,
        writtenInExtChartAt I 𝓘(Real, Real) x₀ (Ft t)
          =ᶠ[nhds (extChartAt I x₀ x₀)]
            fun y : E =>
              (fderiv Real (fun p : Real × E => Φ p.1 p.2) (t, y)) (1, 0)) :
    FixedBaseExtDerivTimeDerivativeOnRegular
      (I := I) timeSet regularSet ({x₀} : Set M) F Ft := by
  exact
    (fixedBaseExtDerivTimeDerivativeOn_singleton_of_chart_contDiff
      (I := I) (timeSet := timeSet) (x₀ := x₀)
      (F := F) (Ft := Ft) (Φ := Φ)
      hΦ hFdiff hFchart hFtdiff hFtchart).toRegular
      (I := I) (regularSet := regularSet)

theorem fixedBaseExtDerivTimeDerivativeOnRegular_singleton_of_chart_contDiffOnTime
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {timeSet regularSet : Set Real} {x₀ : M}
    {F Ft : Real -> M -> Real} {Φ : Real -> E -> Real}
    (hregular_subset : regularSet ⊆ timeSet)
    (hΦ : ContDiff Real 2 (fun p : Real × E => Φ p.1 p.2))
    (hFdiff :
      ∀ s : Real, s ∈ timeSet ->
        MDifferentiableAt I 𝓘(Real, Real) (F s) x₀)
    (hFchart :
      ∀ s : Real, s ∈ timeSet ->
        writtenInExtChartAt I 𝓘(Real, Real) x₀ (F s)
          =ᶠ[nhds (extChartAt I x₀ x₀)] Φ s)
    (hFtdiff :
      ∀ t : Real, t ∈ regularSet ->
        MDifferentiableAt I 𝓘(Real, Real) (Ft t) x₀)
    (hFtchart :
      ∀ t : Real, t ∈ regularSet ->
        writtenInExtChartAt I 𝓘(Real, Real) x₀ (Ft t)
          =ᶠ[nhds (extChartAt I x₀ x₀)]
            fun y : E =>
              (fderiv Real (fun p : Real × E => Φ p.1 p.2) (t, y)) (1, 0)) :
    FixedBaseExtDerivTimeDerivativeOnRegular
      (I := I) timeSet regularSet ({x₀} : Set M) F Ft := by
  intro t ht x hx V
  rw [Set.mem_singleton_iff] at hx
  subst x
  let z₀ : E := extChartAt I x₀ x₀
  have hmodel :=
    fixedBaseFDerivTimeDerivativeWithinAt_of_contDiff
      (E := E) Φ hΦ (timeSet := timeSet) (t := t) z₀ V
  have hleft :
      ∀ s : Real, s ∈ timeSet ->
        mvfderiv (I := I) (F s) x₀ V =
          fderiv Real (Φ s) z₀ V := by
    intro s hs
    exact
      mvfderiv_eq_fderiv_of_writtenInExtChartAt_eventuallyEq
        (I := I) (x := x₀) (f := F s) (φ := Φ s)
        (hFdiff s hs) (hFchart s hs) V
  have hright :
      mvfderiv (I := I) (Ft t) x₀ V =
        fderiv Real
          (fun y : E =>
            (fderiv Real (fun p : Real × E => Φ p.1 p.2) (t, y)) (1, 0))
          z₀ V := by
    exact
      mvfderiv_eq_fderiv_of_writtenInExtChartAt_eventuallyEq
        (I := I) (x := x₀) (f := Ft t)
        (φ := fun y : E =>
          (fderiv Real (fun p : Real × E => Φ p.1 p.2) (t, y)) (1, 0))
      (hFtdiff t ht) (hFtchart t ht) V
  exact
    (hmodel.congr
      (fun s hs => hleft s hs)
      (hleft t (hregular_subset ht))).congr_deriv hright.symm

theorem eventuallyEq_timeFDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {timeSet : Set Real}
    {Φ Ψ : Real -> E -> Real}
    {t : Real} {y₀ : E}
    (htime : timeSet ∈ 𝓝 t)
    (hdiff : ∀ᶠ y in 𝓝 y₀,
      DifferentiableAt Real
        (fun p : Real × E => Φ p.1 p.2)
        (t, y))
    (hderiv : ∀ᶠ y in 𝓝 y₀,
      HasDerivWithinAt
        (fun s : Real => Φ s y)
        (Ψ t y)
        timeSet
        t) :
    Ψ t =ᶠ[𝓝 y₀]
      fun y : E =>
        (fderiv Real
          (fun p : Real × E => Φ p.1 p.2)
          (t, y)) (1, 0) := by
  filter_upwards [hdiff, hderiv] with y hy_diff hy_deriv
  let A : Real × E -> Real := fun p => Φ p.1 p.2
  let L : Real -> Real × E := fun s => (s, y)
  have hline : HasDerivAt L (1, 0) t := by
    exact (hasDerivAt_id t).prodMk (hasDerivAt_const (x := t) (c := y))
  have hchart :
      HasDerivAt
        (fun s : Real => A (L s))
        ((fderiv Real A (t, y)) (1, 0)) t := by
    change HasDerivAt (A ∘ L) ((fderiv Real A (t, y)) (1, 0)) t
    exact hy_diff.hasFDerivAt.comp_hasDerivAt t hline
  have htime_deriv :
      HasDerivAt (fun s : Real => Φ s y) (Ψ t y) t :=
    hy_deriv.hasDerivAt htime
  exact htime_deriv.unique hchart

theorem fixedBaseAtRegularity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {timeSet regularSet : Set Real} {x₀ : M}
    {F Ft : Real -> M -> Real} {Φ : Real -> E -> Real}
    (hregular_subset : regularSet ⊆ timeSet)
    (hΦ : ∀ t : Real, t ∈ regularSet ->
      ContDiffAt Real 2 (fun p : Real × E => Φ p.1 p.2)
        (t, extChartAt I x₀ x₀))
    (hFdiff :
      ∀ s : Real, s ∈ timeSet ->
        MDifferentiableAt I 𝓘(Real, Real) (F s) x₀)
    (hFchart :
      ∀ s : Real, s ∈ timeSet ->
        writtenInExtChartAt I 𝓘(Real, Real) x₀ (F s)
          =ᶠ[nhds (extChartAt I x₀ x₀)] Φ s)
    (hFtdiff :
      ∀ t : Real, t ∈ regularSet ->
        MDifferentiableAt I 𝓘(Real, Real) (Ft t) x₀)
    (hFtchart :
      ∀ t : Real, t ∈ regularSet ->
        writtenInExtChartAt I 𝓘(Real, Real) x₀ (Ft t)
          =ᶠ[nhds (extChartAt I x₀ x₀)]
            fun y : E =>
              (fderiv Real (fun p : Real × E => Φ p.1 p.2) (t, y)) (1, 0)) :
    FixedBaseExtDerivTimeDerivativeOnRegular
      (I := I) timeSet regularSet ({x₀} : Set M) F Ft := by
  intro t ht x hx V
  rw [Set.mem_singleton_iff] at hx
  subst x
  let z₀ : E := extChartAt I x₀ x₀
  have hmodel :
      HasDerivWithinAt
        (fun s : Real => (fderiv Real (Φ s) z₀) V)
        ((fderiv Real
          (fun y : E =>
            (fderiv Real (fun p : Real × E => Φ p.1 p.2) (t, y)) (1, 0))
          z₀) V)
        timeSet t :=
    (fixedBaseFDerivTimeDerivativeAt_of_contDiffAt
      (E := E) (F := Φ) (t := t) (x := z₀) (V := V) (hΦ t ht)).hasDerivWithinAt
  have hleft :
      ∀ s : Real, s ∈ timeSet ->
        mvfderiv (I := I) (F s) x₀ V =
          fderiv Real (Φ s) z₀ V := by
    intro s hs
    exact
      mvfderiv_eq_fderiv_of_writtenInExtChartAt_eventuallyEq
        (I := I) (x := x₀) (f := F s) (φ := Φ s)
        (hFdiff s hs) (hFchart s hs) V
  have hright :
      mvfderiv (I := I) (Ft t) x₀ V =
        fderiv Real
          (fun y : E =>
            (fderiv Real (fun p : Real × E => Φ p.1 p.2) (t, y)) (1, 0))
          z₀ V := by
    exact
      mvfderiv_eq_fderiv_of_writtenInExtChartAt_eventuallyEq
        (I := I) (x := x₀) (f := Ft t)
        (φ := fun y : E =>
          (fderiv Real (fun p : Real × E => Φ p.1 p.2) (t, y)) (1, 0))
        (hFtdiff t ht) (hFtchart t ht) V
  exact
    (hmodel.congr
      (fun s hs => hleft s hs)
      (hleft t (hregular_subset ht))).congr_deriv hright.symm

theorem contDiffAt_prodChart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {n : WithTop ℕ∞} {F : Real × M -> Real} {t : Real} {x : M}
    (hF : ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) n F (t, x)) :
    ContDiffAt Real n
      (fun p : Real × E => F (p.1, (extChartAt I x).symm p.2))
      (t, extChartAt I x x) := by
  have hsrc :=
    (contMDiffAt_iff_source
      (I := 𝓘(Real, Real).prod I) (I' := 𝓘(Real, Real))
      (f := F) (x := (t, x))).mp hF
  rw [contMDiffWithinAt_iff_contDiffWithinAt] at hsrc
  have hsrc' :
      ContDiffWithinAt Real n
        (fun p : Real × E => F (p.1, (extChartAt I x).symm p.2))
        Set.univ (t, extChartAt I x x) := by
    convert hsrc using 1
    · ext p
      simp only [Function.comp_apply, extChartAt_prod, PartialEquiv.prod_coe_symm,
        extChartAt_model_space_eq_id, PartialEquiv.refl_symm, PartialEquiv.refl_coe,
        extChartAt_coe_symm, Function.id_def]
    · rw [ModelWithCorners.Boundaryless.range_eq_univ]
    · rw [extChartAt_prod]
      rw [extChartAt_model_space_eq_id]
      rfl
  simpa [contDiffWithinAt_univ] using hsrc'

theorem fixedBaseOnRegularity_of_timeDerivWithin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {timeSet regularSet : Set Real} {u : Set M}
    {F Ft : Real -> M -> Real}
    (hregular_subset : regularSet ⊆ timeSet)
    (hregular_nhds :
      ∀ {t : Real}, t ∈ regularSet -> timeSet ∈ 𝓝 t)
    (hSmooth :
      ∀ t, t ∈ regularSet -> ∀ x : M, x ∈ u ->
        ContMDiffAt
          (𝓘(Real, Real).prod I) 𝓘(Real, Real) 2
          (fun p : Real × M => F p.1 p.2)
          (t, x))
    (hFdiff :
      ∀ s, s ∈ timeSet -> ∀ x : M, x ∈ u ->
        MDifferentiableAt I 𝓘(Real, Real) (F s) x)
    (hFtdiff :
      ∀ t, t ∈ regularSet -> ∀ x : M, x ∈ u ->
        MDifferentiableAt I 𝓘(Real, Real) (Ft t) x)
    (hTime :
      ∀ t, t ∈ regularSet -> ∀ x : M,
        HasDerivWithinAt
          (fun s : Real => F s x)
          (Ft t x)
          timeSet
          t) :
    FixedBaseExtDerivTimeDerivativeOnRegular
      (I := I) timeSet regularSet u F Ft := by
  intro t ht x hx V
  let Φ : Real -> E -> Real := fun s y => F s ((extChartAt I x).symm y)
  have hsingle :
      FixedBaseExtDerivTimeDerivativeOnRegular
        (I := I) timeSet regularSet ({x} : Set M) F Ft := by
    refine fixedBaseAtRegularity
      (I := I) (timeSet := timeSet) (regularSet := regularSet)
      (x₀ := x) (F := F) (Ft := Ft) (Φ := Φ)
      hregular_subset ?hΦ ?hFdiff ?hFchart ?hFtdiff ?hFtchart
    · intro τ hτ
      have hτs :
          ContMDiffAt
            (𝓘(Real, Real).prod I) 𝓘(Real, Real) 2
            (fun p : Real × M => F p.1 p.2)
            (τ, x) :=
        hSmooth τ hτ x hx
      simpa [Φ] using contDiffAt_prodChart (I := I) hτs
    · intro s hs
      exact hFdiff s hs x hx
    · intro s hs
      filter_upwards [extChartAt_target_mem_nhds (I := I) x] with y hy
      exact writtenInExtChartAt_real_apply (F s) x y
    · intro τ hτ
      exact hFtdiff τ hτ x hx
    · intro τ hτ
      have hraw :
          (fun y : E => Ft τ ((extChartAt I x).symm y)) =ᶠ[𝓝 (extChartAt I x x)]
            fun y : E =>
              (fderiv Real (fun p : Real × E => Φ p.1 p.2) (τ, y)) (1, 0) := by
        apply eventuallyEq_timeFDeriv
          (Φ := Φ)
          (Ψ := fun τ y => Ft τ ((extChartAt I x).symm y))
          (t := τ) (y₀ := extChartAt I x x)
        · exact hregular_nhds hτ
        · have hτs :
              ContDiffAt Real 2
                (fun p : Real × E => Φ p.1 p.2)
                (τ, extChartAt I x x) := by
            have hτm :
                ContMDiffAt
                  (𝓘(Real, Real).prod I) 𝓘(Real, Real) 2
                  (fun p : Real × M => F p.1 p.2)
                  (τ, x) :=
              hSmooth τ hτ x hx
            simpa [Φ] using contDiffAt_prodChart (I := I) hτm
          have hev :=
            (hτs.eventually (by norm_num)).mono fun y hy =>
              (hy.of_le (by norm_num)).differentiableAt_one
          have hev' :
              ∀ᶠ y in 𝓝 τ ×ˢ 𝓝 (extChartAt I x x),
                DifferentiableAt Real (fun p : Real × E => Φ p.1 p.2) y := by
            simpa [nhds_prod_eq] using hev
          exact
            (tendsto_const_nhds.prodMk Filter.tendsto_id).eventually hev'
        · filter_upwards with y
          exact hTime τ hτ ((extChartAt I x).symm y)
      have hFt_raw :
          writtenInExtChartAt I 𝓘(Real, Real) x (Ft τ)
            =ᶠ[𝓝 (extChartAt I x x)]
              fun y : E => Ft τ ((extChartAt I x).symm y) := by
        filter_upwards [extChartAt_target_mem_nhds (I := I) x] with y hy
        exact writtenInExtChartAt_real_apply (Ft τ) x y
      exact hFt_raw.trans hraw
  exact hsingle t ht x (by simp) V

theorem fixedBaseOnRegularityLocal
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {timeSet regularSet : Set Real} {u : Set M}
    {F Ft : Real -> M -> Real}
    (hu : IsOpen u)
    (hregular_subset : regularSet ⊆ timeSet)
    (hregular_nhds :
      ∀ {t : Real}, t ∈ regularSet -> timeSet ∈ 𝓝 t)
    (hSmooth :
      ∀ t, t ∈ regularSet -> ∀ x : M, x ∈ u ->
        ContMDiffAt
          (𝓘(Real, Real).prod I) 𝓘(Real, Real) 2
          (fun p : Real × M => F p.1 p.2)
          (t, x))
    (hFdiff :
      ∀ s, s ∈ timeSet -> ∀ x : M, x ∈ u ->
        MDifferentiableAt I 𝓘(Real, Real) (F s) x)
    (hFtdiff :
      ∀ t, t ∈ regularSet -> ∀ x : M, x ∈ u ->
        MDifferentiableAt I 𝓘(Real, Real) (Ft t) x)
    (hTime :
      ∀ t, t ∈ regularSet -> ∀ x : M, x ∈ u ->
        HasDerivWithinAt
          (fun s : Real => F s x)
          (Ft t x)
          timeSet
          t) :
    FixedBaseExtDerivTimeDerivativeOnRegular
      (I := I) timeSet regularSet u F Ft := by
  intro t ht x hx V
  let Φ : Real -> E -> Real := fun s y => F s ((extChartAt I x).symm y)
  have hsingle :
      FixedBaseExtDerivTimeDerivativeOnRegular
        (I := I) timeSet regularSet ({x} : Set M) F Ft := by
    refine fixedBaseAtRegularity
      (I := I) (timeSet := timeSet) (regularSet := regularSet)
      (x₀ := x) (F := F) (Ft := Ft) (Φ := Φ)
      hregular_subset ?hΦ ?hFdiff ?hFchart ?hFtdiff ?hFtchart
    · intro τ hτ
      have hτs :
          ContMDiffAt
            (𝓘(Real, Real).prod I) 𝓘(Real, Real) 2
            (fun p : Real × M => F p.1 p.2)
            (τ, x) :=
        hSmooth τ hτ x hx
      simpa [Φ] using contDiffAt_prodChart (I := I) hτs
    · intro s hs
      exact hFdiff s hs x hx
    · intro s hs
      filter_upwards [extChartAt_target_mem_nhds (I := I) x] with y hy
      exact writtenInExtChartAt_real_apply (F s) x y
    · intro τ hτ
      exact hFtdiff τ hτ x hx
    · intro τ hτ
      have hleft : (extChartAt I x).symm ((extChartAt I x) x) = x :=
        (extChartAt I x).left_inv (mem_extChartAt_source (I := I) x)
      have hsymm_tend :
          Filter.Tendsto (fun y : E => (extChartAt I x).symm y)
            (𝓝 (extChartAt I x x)) (𝓝 x) := by
        simpa only [ContinuousAt, hleft, Function.comp_def] using
          continuousAt_extChartAt_symm (I := I) x
      have hu_event :
          ∀ᶠ y in 𝓝 (extChartAt I x x), (extChartAt I x).symm y ∈ u :=
        hsymm_tend.eventually (hu.mem_nhds hx)
      have hraw :
          (fun y : E => Ft τ ((extChartAt I x).symm y)) =ᶠ[𝓝 (extChartAt I x x)]
            fun y : E =>
              (fderiv Real (fun p : Real × E => Φ p.1 p.2) (τ, y)) (1, 0) := by
        apply eventuallyEq_timeFDeriv
          (Φ := Φ)
          (Ψ := fun τ y => Ft τ ((extChartAt I x).symm y))
          (t := τ) (y₀ := extChartAt I x x)
        · exact hregular_nhds hτ
        · have hτs :
              ContDiffAt Real 2
                (fun p : Real × E => Φ p.1 p.2)
                (τ, extChartAt I x x) := by
            have hτm :
                ContMDiffAt
                  (𝓘(Real, Real).prod I) 𝓘(Real, Real) 2
                  (fun p : Real × M => F p.1 p.2)
                  (τ, x) :=
              hSmooth τ hτ x hx
            simpa [Φ] using contDiffAt_prodChart (I := I) hτm
          have hev :=
            (hτs.eventually (by norm_num)).mono fun y hy =>
              (hy.of_le (by norm_num)).differentiableAt_one
          have hev' :
              ∀ᶠ y in 𝓝 τ ×ˢ 𝓝 (extChartAt I x x),
                DifferentiableAt Real (fun p : Real × E => Φ p.1 p.2) y := by
            simpa [nhds_prod_eq] using hev
          exact
            (tendsto_const_nhds.prodMk Filter.tendsto_id).eventually hev'
        · filter_upwards [hu_event] with y hyu
          exact hTime τ hτ ((extChartAt I x).symm y) hyu
      have hFt_raw :
          writtenInExtChartAt I 𝓘(Real, Real) x (Ft τ)
            =ᶠ[𝓝 (extChartAt I x x)]
              fun y : E => Ft τ ((extChartAt I x).symm y) := by
        filter_upwards [extChartAt_target_mem_nhds (I := I) x] with y hy
        exact writtenInExtChartAt_real_apply (Ft τ) x y
      exact hFt_raw.trans hraw
  exact hsingle t ht x (by simp) V

theorem fixedBaseOnRegularitySmooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {timeSet regularSet : Set Real} {u : Set M}
    {F Ft : Real -> M -> Real}
    (hu : IsOpen u)
    (hregular_open : IsOpen regularSet)
    (hregular_nhds : ∀ {t : Real}, t ∈ regularSet -> timeSet ∈ nhds t)
    (hSmooth :
      ∀ t, t ∈ regularSet -> ∀ x : M, x ∈ u ->
        ContMDiffAt
          ((modelWithCornersSelf Real Real).prod I)
          (modelWithCornersSelf Real Real) 2
          (fun p : Real × M => F p.1 p.2)
          (t, x))
    (hTime :
      ∀ t, t ∈ regularSet -> ∀ x : M, x ∈ u ->
        HasDerivWithinAt
          (fun s : Real => F s x)
          (Ft t x)
          timeSet
          t) :
    FixedBaseExtDerivTimeDerivativeOnRegular
      (I := I) timeSet regularSet u F Ft := by
  have hFdiff :
      ∀ s, s ∈ regularSet -> ∀ x : M, x ∈ u ->
        MDifferentiableAt I (modelWithCornersSelf Real Real) (F s) x := by
    intro s hs x hx
    have hslice :
        ContMDiffAt I ((modelWithCornersSelf Real Real).prod I) 1
          (fun y : M => (s, y)) x :=
      contMDiffAt_const.prodMk contMDiffAt_id
    have hcomp := (hSmooth s hs x hx).of_le
      (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
    have hsliceComp := hcomp.comp x hslice
    simpa [Function.comp_def] using hsliceComp.mdifferentiableAt (by norm_num)
  have hFtdiff :
      ∀ t, t ∈ regularSet -> ∀ x : M, x ∈ u ->
        MDifferentiableAt I (modelWithCornersSelf Real Real) (Ft t) x := by
    intro t ht x hx
    have hpartialJoint :
        ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
          (modelWithCornersSelf Real Real) 1
          (fun p : Real × M => deriv (fun s => F s p.2) p.1) (t, x) :=
      timeDeriv_smoothAt (hSmooth t ht x hx)
        (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    have hslice :
        ContMDiffAt I ((modelWithCornersSelf Real Real).prod I) 1
          (fun y : M => (t, y)) x :=
      contMDiffAt_const.prodMk contMDiffAt_id
    have hpartialSpace :
        MDifferentiableAt I (modelWithCornersSelf Real Real)
          (fun y : M => deriv (fun s => F s y) t) x := by
      have hcomp := hpartialJoint.comp x hslice
      simpa [Function.comp_def] using hcomp.mdifferentiableAt (by norm_num)
    have heq :
        (fun y : M => Ft t y) =ᶠ[nhds x]
          fun y : M => deriv (fun s => F s y) t := by
      filter_upwards [hu.mem_nhds hx] with y hy
      exact ((hTime t ht y hy).hasDerivAt (hregular_nhds ht)).deriv.symm
    exact hpartialSpace.congr_of_eventuallyEq heq
  have hTimeRegularity :
      ∀ t, t ∈ regularSet -> ∀ x : M, x ∈ u ->
        HasDerivWithinAt (fun s : Real => F s x) (Ft t x) regularSet t := by
    intro t ht x hx
    exact ((hTime t ht x hx).hasDerivAt (hregular_nhds ht)).hasDerivWithinAt
  have hswapRegularity :
      FixedBaseExtDerivTimeDerivativeOnRegular
        (I := I) regularSet regularSet u F Ft :=
    fixedBaseOnRegularityLocal (I := I) hu (Set.Subset.rfl)
      (fun ht => hregular_open.mem_nhds ht) hSmooth hFdiff hFtdiff hTimeRegularity
  intro t ht x hx V
  exact ((hswapRegularity t ht x hx V).hasDerivAt
    (hregular_open.mem_nhds ht)).hasDerivWithinAt

end CalabiYau
