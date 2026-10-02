-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Regularity/SmoothFChartResidual/BilinearBoundSmoothRepPieces.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplResidual
public import CalabiYau.Analysis.Elliptic.Regularity.GradInner.CLM.ChartFormula
public import CalabiYau.Analysis.Sobolev.Chart.SmoothDensity.StrictCutoffPushforwardBound
public import CalabiYau.Analysis.Sobolev.Chart.SmoothDensity.SmoothMul
public import CalabiYau.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuantK
public import CalabiYau.Analysis.Sobolev.Manifold.Morrey.HigherOrder
public import CalabiYau.Analysis.Sobolev.Manifold.Embedding.Iterated

@[expose] public section

open CalabiYau.Riemannian

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace CalabiYau
namespace Analysis
namespace Laplacian
namespace SmoothFChartResidualBilinearBound

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open CalabiYau.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl
open CalabiYau.Analysis.Laplacian.LaplacianDomainChartData
open CalabiYau.Analysis.Laplacian.DiffChartBilinearH1ComplResidual
open CalabiYau.Analysis.Laplacian.GradInnerCLMChartFormula
open CalabiYau.Analysis.Sobolev.Chart
open _root_.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

noncomputable def etaTimesV (α : M) (v : M → ℝ) : M → ℝ :=
  fun x => chartStrictCutoff (I := I) (M := M) α x * v x

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma etaTimesV_smooth (α : M) {v : M → ℝ}
    (hv : ContMDiff I 𝓘(ℝ, ℝ) ∞ v) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (etaTimesV (I := I) (M := M) α v) := by
  unfold etaTimesV
  exact (chartStrictCutoff_contMDiff (I := I) (M := M) α).mul hv

noncomputable def etaTimesVScalar
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    SmoothScalar g where
  toFun := etaTimesV (I := I) (M := M) α v.toFun
  smooth := etaTimesV_smooth (I := I) (M := M) α v.smooth

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
@[simp] lemma etaTimesVScalar_toFun (g : SmoothRiemannianMetric I M)
    (α : M) (v : SmoothScalar g) :
    (etaTimesVScalar (I := I) (M := M) g α v).toFun =
      etaTimesV (I := I) (M := M) α v.toFun := rfl

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma tsupport_etaTimesV_subset (α : M) (v : M → ℝ) :
    tsupport (etaTimesV (I := I) (M := M) α v) ⊆ (chartAt H α).source := by
  have h_support_subset : Function.support (etaTimesV (I := I) (M := M) α v) ⊆
      Function.support (chartStrictCutoff (I := I) (M := M) α) := by
    intro x hx
    by_contra hxnot
    apply hx
    change chartStrictCutoff (I := I) (M := M) α x * v x = 0
    have h0 : chartStrictCutoff (I := I) (M := M) α x = 0 := by
      simpa [Function.mem_support, not_not] using hxnot
    rw [h0]; ring
  have h_tsupp_subset : tsupport (etaTimesV (I := I) (M := M) α v) ⊆
      tsupport (chartStrictCutoff (I := I) (M := M) α) :=
    closure_minimal (h_support_subset.trans (subset_tsupport _))
      (isClosed_tsupport _)
  exact h_tsupp_subset.trans (chartStrictCutoff_tsupport_subset (I := I) (M := M) α)

noncomputable def smoothRep
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) : M → ℝ :=
  fun x : M =>
    -((2 : ℝ) * g.inner x (gradFun (I := I) g
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x)
      (gradFun (I := I) g v.toFun x)) -
    (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x * v.toFun x

omit [NeZero (Module.finrank ℝ E)] in
private lemma smoothRep_apply (g : SmoothRiemannianMetric I M) (α : M)
    (v : SmoothScalar g) (x : M) :
    smoothRep (I := I) (M := M) g α v x =
      -((2 : ℝ) * g.inner x (gradFun (I := I) g
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x)
        (gradFun (I := I) g v.toFun x)) -
      (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x * v.toFun x := rfl

omit [NeZero (Module.finrank ℝ E)] in
private lemma smoothRep_eq_zero_off_tsupport_chartAtlasPOU
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) {x : M}
    (hx : x ∉ tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :
    smoothRep (I := I) (M := M) g α v x = 0 := by
  classical
  have h_open : IsOpen
      (tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ))ᶜ :=
    (isClosed_tsupport _).isOpen_compl
  have h_ev : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) =ᶠ[𝓝 x]
      (fun _ : M => (0 : ℝ)) := by
    filter_upwards [h_open.mem_nhds hx] with y hy
    by_contra hne
    exact hy (subset_tsupport _ hne)
  have h_grad_zero : gradFun (I := I) g
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0 :=
    gradFun_eq_zero_of_eventuallyEq_zero (I := I) g h_ev
  have h_lap_zero : (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x = 0 := by
    rw [laplacianOfChartPOU_apply]
    rw [Δ_g_def]
    have h_grad_ev : ∀ᶠ y in 𝓝 x,
        (CalabiYau.Riemannian.gradG (I := I) g (chartAtlasPOU I M α : C^∞⟮I,
          M; ℝ⟯) :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) y =
        (0 : TangentSpace I y) := by
      filter_upwards [h_open.mem_nhds hx] with y hy
      have h_y_ev : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) =ᶠ[𝓝 y]
          (fun _ : M => (0 : ℝ)) := by
        filter_upwards [h_open.mem_nhds hy] with z hz
        by_contra hne
        exact hz (subset_tsupport _ hne)
      have h_g := gradFun_eq_zero_of_eventuallyEq_zero (I := I) g h_y_ev
      rw [CalabiYau.Riemannian.grad_g_apply]
      exact h_g
    exact CalabiYau.DivergenceTheorem.divergence_g_zero_of_eventuallyEq_zero
      (I := I) g _ h_grad_ev
  rw [smoothRep_apply, h_grad_zero, h_lap_zero]
  simp

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma gradFun_eq_gradFun_etaTimesV_of_eventuallyOne
    (g : SmoothRiemannianMetric I M) (α : M) {v : M → ℝ} {x : M}
    (h_one : chartStrictCutoff (I := I) (M := M) α =ᶠ[𝓝 x]
      (fun _ : M => (1 : ℝ))) :
    gradFun (I := I) g (etaTimesV (I := I) (M := M) α v) x =
      gradFun (I := I) g v x := by
  have h_eq : etaTimesV (I := I) (M := M) α v =ᶠ[𝓝 x] v := by
    filter_upwards [h_one] with y hy
    change chartStrictCutoff (I := I) (M := M) α y * v y = v y
    rw [hy]; ring
  have h_mfderiv : mfderiv I 𝓘(ℝ, ℝ) (etaTimesV (I := I) (M := M) α v) x =
      mfderiv I 𝓘(ℝ, ℝ) v x := Filter.EventuallyEq.mfderiv_eq h_eq
  unfold gradFun
  rw [h_mfderiv]

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma etaTimesV_eq_of_eventuallyOne
    (α : M) {v : M → ℝ} {x : M}
    (h_one : chartStrictCutoff (I := I) (M := M) α =ᶠ[𝓝 x]
      (fun _ : M => (1 : ℝ))) :
    etaTimesV (I := I) (M := M) α v x = v x := by
  have h_self : chartStrictCutoff (I := I) (M := M) α x = 1 := h_one.self_of_nhds
  change chartStrictCutoff (I := I) (M := M) α x * v x = v x
  rw [h_self]; ring

omit [NeZero (Module.finrank ℝ E)] in
private lemma smoothRep_eq_etaTimesV
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) (x : M) :
    smoothRep (I := I) (M := M) g α v x =
    -((2 : ℝ) * g.inner x
        (gradFun (I := I) g
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
        (gradFun (I := I) g
          (etaTimesV (I := I) (M := M) α v.toFun) x)) -
    (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x *
      etaTimesV (I := I) (M := M) α v.toFun x := by
  classical
  by_cases hx_support : x ∈ tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
  · have h_one : chartStrictCutoff (I := I) (M := M) α =ᶠ[𝓝 x]
        (fun _ : M => (1 : ℝ)) :=
      (chartStrictCutoff_eventually_one_nhdsSet_tsupport_chartAtlasPOU
        (I := I) (M := M) α).filter_mono (nhds_le_nhdsSet hx_support)
    have h_grad := gradFun_eq_gradFun_etaTimesV_of_eventuallyOne
      (I := I) (M := M) g α h_one (v := v.toFun)
    have h_eta_v : etaTimesV (I := I) (M := M) α v.toFun x = v.toFun x :=
      etaTimesV_eq_of_eventuallyOne (I := I) (M := M) α h_one
    rw [smoothRep_apply, ← h_grad, ← h_eta_v]
  · have hLHS : smoothRep (I := I) (M := M) g α v x = 0 :=
      smoothRep_eq_zero_off_tsupport_chartAtlasPOU
        (I := I) (M := M) g α v hx_support
    rw [hLHS]
    have h_open : IsOpen
        (tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ))ᶜ :=
      (isClosed_tsupport _).isOpen_compl
    have h_ev : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) =ᶠ[𝓝 x]
        (fun _ : M => (0 : ℝ)) := by
      filter_upwards [h_open.mem_nhds hx_support] with y hy
      by_contra hne
      exact hy (subset_tsupport _ hne)
    have h_grad_zero : gradFun (I := I) g
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0 :=
      gradFun_eq_zero_of_eventuallyEq_zero (I := I) g h_ev
    have h_lap_zero : (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x = 0 := by
      rw [laplacianOfChartPOU_apply, Δ_g_def]
      have h_grad_ev : ∀ᶠ y in 𝓝 x,
          (CalabiYau.Riemannian.gradG (I := I) g
            (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) y =
          (0 : TangentSpace I y) := by
        filter_upwards [h_open.mem_nhds hx_support] with y hy
        have h_y_ev : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) =ᶠ[𝓝 y]
            (fun _ : M => (0 : ℝ)) := by
          filter_upwards [h_open.mem_nhds hy] with z hz
          by_contra hne
          exact hz (subset_tsupport _ hne)
        rw [CalabiYau.Riemannian.grad_g_apply]
        exact gradFun_eq_zero_of_eventuallyEq_zero (I := I) g h_y_ev
      exact CalabiYau.DivergenceTheorem.divergence_g_zero_of_eventuallyEq_zero
        (I := I) g _ h_grad_ev
    rw [h_grad_zero, h_lap_zero]
    simp

noncomputable def gradInnerPiece
    (g : SmoothRiemannianMetric I M) (α : M) (v : M → ℝ) : M → ℝ :=
  fun x => (2 : ℝ) * g.inner x
      (gradFun (I := I) g ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
      (gradFun (I := I) g (etaTimesV (I := I) (M := M) α v) x)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma gradInnerPiece_apply (g : SmoothRiemannianMetric I M) (α : M)
    (v : M → ℝ) (x : M) :
    gradInnerPiece (I := I) (M := M) g α v x =
      (2 : ℝ) * g.inner x
        (gradFun (I := I) g ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
        (gradFun (I := I) g (etaTimesV (I := I) (M := M) α v) x) := rfl

noncomputable def lapPiece
    (g : SmoothRiemannianMetric I M) (α : M) (v : M → ℝ) : M → ℝ :=
  fun x => (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x *
    etaTimesV (I := I) (M := M) α v x

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma lapPiece_apply (g : SmoothRiemannianMetric I M) (α : M)
    (v : M → ℝ) (x : M) :
    lapPiece (I := I) (M := M) g α v x =
      (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x *
        etaTimesV (I := I) (M := M) α v x := rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma smoothRep_eq_pieces
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    smoothRep (I := I) (M := M) g α v =
      fun x => -gradInnerPiece (I := I) (M := M) g α v.toFun x -
        lapPiece (I := I) (M := M) g α v.toFun x := by
  funext x
  rw [smoothRep_eq_etaTimesV (I := I) (M := M) g α v x]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma gradInnerPiece_smooth (g : SmoothRiemannianMetric I M) (α : M)
    (v : SmoothScalar g) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (gradInnerPiece (I := I) (M := M) g α v.toFun) := by
  unfold gradInnerPiece
  have hα_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
    (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff
  have hetaV_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (etaTimesV (I := I) (M := M) α v.toFun) :=
    etaTimesV_smooth (I := I) (M := M) α v.smooth
  let rhoMap : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯ :=
    ⟨(chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯), hα_smooth⟩
  let etaVMap : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯ :=
    ⟨etaTimesV (I := I) (M := M) α v.toFun, hetaV_smooth⟩
  have h_inner : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g.inner x
        (gradFun (I := I) g
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
        (gradFun (I := I) g
          (etaTimesV (I := I) (M := M) α v.toFun) x)) := by
    have h := CalabiYau.Riemannian.contMDiff_g_inner_of_smooth_sections
      (I := I) (M := M) g
      (CalabiYau.Riemannian.gradG (I := I) g rhoMap)
      (CalabiYau.Riemannian.gradG (I := I) g etaVMap)
    refine h.congr (fun x => ?_)
    rw [CalabiYau.Riemannian.grad_g_apply,
      CalabiYau.Riemannian.grad_g_apply]
    congr 1
  exact (contMDiff_const : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => (2 : ℝ))).mul h_inner

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma lapPiece_smooth (g : SmoothRiemannianMetric I M) (α : M)
    (v : SmoothScalar g) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (lapPiece (I := I) (M := M) g α v.toFun) := by
  unfold lapPiece
  exact (laplacianOfChartPOU (I := I) (M := M) g α).contMDiff.mul
    (etaTimesV_smooth (I := I) (M := M) α v.smooth)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma tsupport_gradInnerPiece_subset
    (g : SmoothRiemannianMetric I M) (α : M) (v : M → ℝ) :
    tsupport (gradInnerPiece (I := I) (M := M) g α v) ⊆
      tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
  classical
  have h_support_subset : Function.support (gradInnerPiece (I := I) (M := M) g α v) ⊆
      tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
    intro x hx
    by_contra hxoff
    apply hx
    have h_open : IsOpen
        (tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ))ᶜ :=
      (isClosed_tsupport _).isOpen_compl
    have h_ev : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) =ᶠ[𝓝 x]
        (fun _ : M => (0 : ℝ)) := by
      filter_upwards [h_open.mem_nhds hxoff] with y hy
      by_contra hne
      exact hy (subset_tsupport _ hne)
    have h_grad_zero : gradFun (I := I) g
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0 :=
      gradFun_eq_zero_of_eventuallyEq_zero (I := I) g h_ev
    change gradInnerPiece (I := I) (M := M) g α v x = 0
    rw [gradInnerPiece_apply, h_grad_zero]
    simp
  exact closure_minimal h_support_subset (isClosed_tsupport _)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma tsupport_gradInnerPiece_subset_source
    (g : SmoothRiemannianMetric I M) (α : M) (v : M → ℝ) :
    tsupport (gradInnerPiece (I := I) (M := M) g α v) ⊆ (chartAt H α).source :=
  (tsupport_gradInnerPiece_subset (I := I) (M := M) g α v).trans
    (chartAtlasPOU_isSubordinate I M α)

omit [NeZero (Module.finrank ℝ E)] in
lemma chartPushedRaw_lapPiece_factor
    (g : SmoothRiemannianMetric I M) (α : M) (v : M → ℝ)
    {b : M → ℝ}
    (hb_one : ∀ x ∈ tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
      b x = 1)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushedRaw (I := I) (M := M) α
        (lapPiece (I := I) (M := M) g α v) y =
      smoothExtensionScalar (I := I) (M := M) α
          (fun x => b x *
            (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x) y *
        chartPushedRaw (I := I) (M := M) α
          (etaTimesV (I := I) (M := M) α v) y := by
  classical
  set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_def
  have hLHS : chartPushedRaw (I := I) (M := M) α
      (lapPiece (I := I) (M := M) g α v) y =
      lapPiece (I := I) (M := M) g α v x := by
    rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α
      (lapPiece (I := I) (M := M) g α v) hy]
  have hRHS_smooth : smoothExtensionScalar (I := I) (M := M) α
      (fun x => b x * (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x) y =
      b x * (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x := by
    have h_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
      rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy; exact hy
    classical
    change (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
        b ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
      else 0) = b x * (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x
    rw [if_pos h_target]
  have hRHS_etav : chartPushedRaw (I := I) (M := M) α
      (etaTimesV (I := I) (M := M) α v) y =
      etaTimesV (I := I) (M := M) α v x := by
    rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α
      (etaTimesV (I := I) (M := M) α v) hy]
  rw [hLHS, hRHS_smooth, hRHS_etav]
  by_cases h_lap_zero : (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x = 0
  · rw [lapPiece_apply, h_lap_zero]; ring
  · have h_support_Δρα : Function.support
        ((laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ)) ⊆
        tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
      intro z hz
      by_contra hz_off
      apply hz
      have h_open : IsOpen
          (tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ))ᶜ :=
        (isClosed_tsupport _).isOpen_compl
      have h_ev : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) =ᶠ[𝓝 z]
          (fun _ : M => (0 : ℝ)) := by
        filter_upwards [h_open.mem_nhds hz_off] with w hw
        by_contra hne
        exact hw (subset_tsupport _ hne)
      rw [laplacianOfChartPOU_apply, Δ_g_def]
      have h_grad_ev : ∀ᶠ w in 𝓝 z,
          (CalabiYau.Riemannian.gradG (I := I) g
            (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) w =
          (0 : TangentSpace I w) := by
        filter_upwards [h_open.mem_nhds hz_off] with w hw
        have h_w_ev : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) =ᶠ[𝓝 w]
            (fun _ : M => (0 : ℝ)) := by
          filter_upwards [h_open.mem_nhds hw] with u hu
          by_contra hne
          exact hu (subset_tsupport _ hne)
        rw [CalabiYau.Riemannian.grad_g_apply]
        exact gradFun_eq_zero_of_eventuallyEq_zero (I := I) g h_w_ev
      exact CalabiYau.DivergenceTheorem.divergence_g_zero_of_eventuallyEq_zero
        (I := I) g _ h_grad_ev
    have hx_support : x ∈ Function.support
        ((laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ)) := h_lap_zero
    have hx_tsupp : x ∈ tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
      h_support_Δρα hx_support
    have h_bx : b x = 1 := hb_one x hx_tsupp
    rw [lapPiece_apply, h_bx]
    ring

end SmoothFChartResidualBilinearBound
end Laplacian
end Analysis
end CalabiYau

end
