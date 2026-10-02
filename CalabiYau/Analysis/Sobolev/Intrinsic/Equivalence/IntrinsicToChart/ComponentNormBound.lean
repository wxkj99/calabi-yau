-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Intrinsic/Equivalence/IntrinsicToChart/ComponentNormBound.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Intrinsic.Equivalence.NormEquivalence
public import CalabiYau.Analysis.Sobolev.Manifold.Measure.UniformChartComparison
public import CalabiYau.Analysis.Sobolev.Intrinsic.Equivalence.IntrinsicToChart.GradientProduct
public import CalabiYau.Analysis.Sobolev.Intrinsic.Equivalence.IntrinsicToChart.UnitFiber
public import CalabiYau.Analysis.Sobolev.Intrinsic.Equivalence.IntrinsicToChart.WeakDerivative

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
open CalabiYau.Riemannian

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace Sobolev
namespace EquivalenceReverse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open Sobolev.Chart

local notation "EuclN_E" =>
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [FiniteDimensional ℝ E] in
private lemma mfderiv_extChartAt_apply_triv_symm
    (α : M) {x : M} (hxchart : x ∈ (chartAt H α).source) (v_E : E) :
    mfderiv I 𝓘(ℝ, E) (extChartAt I α) x
      ((trivializationAt E (TangentSpace I) α).symm x v_E) = v_E := by
  have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [CalabiYau.RiemannianVolume.trivializationAt_baseSet_eq_chartAt_source]
    exact hxchart
  rw [← TangentBundle.continuousLinearMapAt_trivializationAt (𝕜 := ℝ) (I := I)
    (x₀ := α) (x := x) hxchart]
  have h_symm_eq : ((trivializationAt E (TangentSpace I) α).symm x
        : E → TangentSpace I x) v_E
      = ((trivializationAt E (TangentSpace I) α).symmL ℝ x : E →L[ℝ] TangentSpace I x) v_E :=
    (Trivialization.symmL_apply
      (trivializationAt E (TangentSpace I) α) hbase v_E).symm
  rw [h_symm_eq]
  exact Trivialization.continuousLinearMapAt_symmL
    (R := ℝ) (trivializationAt E (TangentSpace I) α) hbase v_E

omit [FiniteDimensional ℝ E] in
private lemma mfderiv_triv_symm_const_eq_fderiv_scalarOnE
    (α : M) {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hxchart : x ∈ (chartAt H α).source)
    (hx_int : extChartAt I α x ∈ interior (extChartAt I α).target) (v_E : E) :
    mfderiv I 𝓘(ℝ, ℝ) f x
        ((trivializationAt E (TangentSpace I) α).symm x v_E) =
      fderiv ℝ
        (CalabiYau.DivergenceTheorem.scalarOnE
          (I := I) α f) (extChartAt I α x) v_E := by
  classical
  set φ := extChartAt I α
  have hxsrc : x ∈ φ.source := by
    rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
      (I := I)]; exact hxchart
  have hcomp_eq : ∀ᶠ y in 𝓝 x, f y =
      (CalabiYau.DivergenceTheorem.scalarOnE
        (I := I) α f) (φ y) := by
    have hsrc_nhd : φ.source ∈ 𝓝 x :=
      (isOpen_extChartAt_source (I := I) α).mem_nhds hxsrc
    filter_upwards [hsrc_nhd] with y hy
    rw [CalabiYau.DivergenceTheorem.scalarOnE_def, φ.left_inv hy]
  have hcong : f =ᶠ[𝓝 x]
      (CalabiYau.DivergenceTheorem.scalarOnE
        (I := I) α f) ∘ (extChartAt I α) := hcomp_eq
  have hmfderiv_cong : mfderiv I 𝓘(ℝ, ℝ) f x =
      mfderiv I 𝓘(ℝ, ℝ)
        ((CalabiYau.DivergenceTheorem.scalarOnE
          (I := I) α f) ∘ (extChartAt I α)) x :=
    Filter.EventuallyEq.mfderiv_eq hcong
  rw [hmfderiv_cong]
  have hphi_mdiff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I α) x :=
    mdifferentiableAt_extChartAt (I := I) (x := α) hxchart
  have hphi_symm_mdiff :
      MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I α).symm (φ x) := by
    have hcontMDiffOn : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
        (extChartAt I α).target := contMDiffOn_extChartAt_symm (I := I) α
    have htgt_int : (extChartAt I α).target ∈ 𝓝 (φ x) := by
      have hint_open : IsOpen (interior (extChartAt I α).target) := isOpen_interior
      exact mem_nhds_iff.mpr ⟨interior _, interior_subset, hint_open, hx_int⟩
    have hcont_at : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I α).symm (φ x) :=
      (hcontMDiffOn (φ x) (interior_subset hx_int)).contMDiffAt htgt_int
    exact hcont_at.mdifferentiableAt (by simp)
  have hsymm_at_x : (extChartAt I α).symm (φ x) = x := φ.left_inv hxsrc
  have hf_at_symm : MDifferentiableAt I 𝓘(ℝ, ℝ) f ((extChartAt I α).symm (φ x)) := by
    rw [hsymm_at_x]; exact hf
  have hf_comp_symm : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
      (f ∘ (extChartAt I α).symm) (φ x) :=
    hf_at_symm.comp (φ x) hphi_symm_mdiff
  have hscalar_eq :
      (CalabiYau.DivergenceTheorem.scalarOnE
        (I := I) α f) = f ∘ (extChartAt I α).symm := by
    funext y; rfl
  have hg_mdiff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
      (CalabiYau.DivergenceTheorem.scalarOnE
        (I := I) α f) (φ x) := by
    rw [hscalar_eq]; exact hf_comp_symm
  have hchain :
      mfderiv I 𝓘(ℝ, ℝ)
          ((CalabiYau.DivergenceTheorem.scalarOnE
            (I := I) α f) ∘ (extChartAt I α)) x =
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
          (CalabiYau.DivergenceTheorem.scalarOnE
            (I := I) α f) (φ x)).comp
          (mfderiv I 𝓘(ℝ, E) (extChartAt I α) x) :=
    mfderiv_comp x hg_mdiff hphi_mdiff
  rw [hchain]
  rw [show mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
      (CalabiYau.DivergenceTheorem.scalarOnE
        (I := I) α f) (φ x)
      = fderiv ℝ
        (CalabiYau.DivergenceTheorem.scalarOnE
          (I := I) α f) (φ x) from
        mfderiv_eq_fderiv (𝕜 := ℝ)
          (f := CalabiYau.DivergenceTheorem.scalarOnE
            (I := I) α f)]
  change (fderiv ℝ
          (CalabiYau.DivergenceTheorem.scalarOnE
            (I := I) α f) (φ x))
        ((mfderiv I 𝓘(ℝ, E) (extChartAt I α) x)
          ((trivializationAt E (TangentSpace I) α).symm x v_E)) =
      (fderiv ℝ
          (CalabiYau.DivergenceTheorem.scalarOnE
            (I := I) α f) (φ x)) v_E
  rw [mfderiv_extChartAt_apply_triv_symm (I := I) α hxchart v_E]

private lemma fderiv_chartSmoothExt_apply_eq_fderiv_scalarOnE
    [I.Boundaryless]
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (_hf_support : tsupport f ⊆ (chartAt H α).source)
    (_hf_compact : IsCompact (tsupport f))
    {y : EuclN_E}
    (hy : y ∈ Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α)
    (i : Fin (Module.finrank ℝ E)) :
    fderiv ℝ
        (Sobolev.Chart.chartSmoothExt
          (I := I) (M := M) α f) y (EuclideanSpace.single i (1 : ℝ)) =
      fderiv ℝ
        (CalabiYau.DivergenceTheorem.scalarOnE
          (I := I) α f) ((toEuclidean (E := E)).symm y)
          ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E).symm
            (EuclideanSpace.single i (1 : ℝ))) := by
  classical
  have h_chartTarget_open :=
    Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) (α := α)
  have h_chartTarget_nhds :
      Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α ∈ 𝓝 y :=
    h_chartTarget_open.mem_nhds hy
  have h_eqf : (Sobolev.Chart.chartSmoothExt
      (I := I) (M := M) α f) =ᶠ[𝓝 y]
      ((CalabiYau.DivergenceTheorem.scalarOnE
        (I := I) α f) ∘
        (fun z' : EuclN_E => (toEuclidean (E := E)).symm z')) := by
    filter_upwards [h_chartTarget_nhds] with z' hz'
    have hz'_target : (toEuclidean (E := E)).symm z' ∈ (extChartAt I α).target := by
      rw [Sobolev.Chart.chartTargetEuclid_eq_preimage_symm
        (I := I) (M := M)] at hz'
      exact hz'
    change (if (toEuclidean (E := E)).symm z' ∈ (extChartAt I α).target then
          f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z'))
        else (0 : ℝ)) = _
    rw [if_pos hz'_target]
    rfl
  have hsymm_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [Sobolev.Chart.chartTargetEuclid_eq_preimage_symm
      (I := I) (M := M)] at hy
    exact hy
  have h_scalar_smooth :=
    CalabiYau.DivergenceTheorem.scalarOnE_contDiffOn
      (I := I) α hf
  have h_target_open : IsOpen (extChartAt I α).target :=
    isOpen_extChartAt_target (I := I) α
  have h_sym_y_target_nhds : (extChartAt I α).target ∈ 𝓝
      ((toEuclidean (E := E)).symm y) :=
    h_target_open.mem_nhds hsymm_target
  have h_scalar_diffAt : DifferentiableAt ℝ
      (CalabiYau.DivergenceTheorem.scalarOnE
        (I := I) α f) ((toEuclidean (E := E)).symm y) := by
    have h_at : ContDiffAt ℝ ∞
        (CalabiYau.DivergenceTheorem.scalarOnE
          (I := I) α f) ((toEuclidean (E := E)).symm y) :=
      (h_scalar_smooth.contDiffWithinAt hsymm_target).contDiffAt h_sym_y_target_nhds
    exact h_at.differentiableAt (by simp)
  have h_TE_symm_diffAt : DifferentiableAt ℝ
      (fun z' : EuclN_E => (toEuclidean (E := E)).symm z') y :=
    ((toEuclidean (E := E)).symm).differentiable.differentiableAt
  have h_fderiv_eq :
      fderiv ℝ
          (Sobolev.Chart.chartSmoothExt
            (I := I) (M := M) α f) y =
        (fderiv ℝ
          (CalabiYau.DivergenceTheorem.scalarOnE
            (I := I) α f) ((toEuclidean (E := E)).symm y)).comp
          (fderiv ℝ
            (fun z' : EuclN_E => (toEuclidean (E := E)).symm z') y) := by
    rw [h_eqf.fderiv_eq]
    exact fderiv_comp y h_scalar_diffAt h_TE_symm_diffAt
  have h_TE_symm_fderiv :
      fderiv ℝ (fun z' : EuclN_E => (toEuclidean (E := E)).symm z') y =
        ((toEuclidean (E := E)).symm : EuclN_E →L[ℝ] E) :=
    ((toEuclidean (E := E)).symm).fderiv
  rw [h_TE_symm_fderiv] at h_fderiv_eq
  rw [h_fderiv_eq]
  rfl

private lemma sq_fderiv_chartSmoothExt_apply_le_g_inner_mul
    [I.Boundaryless]
    (g : CalabiYau.SmoothRiemannianMetric I M)
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_support_chart : tsupport f ⊆ (chartAt H α).source)
    (hf_compact : IsCompact (tsupport f))
    {y : EuclN_E}
    (hy : y ∈ Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α)
    (i : Fin (Module.finrank ℝ E)) :
    let x := (extChartAt I α).symm ((toEuclidean (E := E)).symm y)
    (fderiv ℝ
        (Sobolev.Chart.chartSmoothExt
          (I := I) (M := M) α f) y
        (EuclideanSpace.single i (1 : ℝ)))^2 ≤
      g.inner x
          (CalabiYau.Riemannian.gradFun
            (I := I) g f x)
          (CalabiYau.Riemannian.gradFun
            (I := I) g f x) *
        g.inner x
          (chartTargetUnitFiber (I := I) α i x)
          (chartTargetUnitFiber (I := I) α i x) := by
  classical
  intro x
  have hsymm_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [Sobolev.Chart.chartTargetEuclid_eq_preimage_symm
      (I := I) (M := M)] at hy
    exact hy
  have hx_source : x ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target hsymm_target
  have hxchart : x ∈ (chartAt H α).source := by
    rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
      (I := I) (M := M)] at hx_source
    exact hx_source
  have hx_int : extChartAt I α x ∈ interior (extChartAt I α).target := by
    rw [(isOpen_extChartAt_target (I := I) α).interior_eq]
    exact (extChartAt I α).map_source hx_source
  have hxy : extChartAt I α x = (toEuclidean (E := E)).symm y := by
    change extChartAt I α ((extChartAt I α).symm
        ((toEuclidean (E := E)).symm y)) = (toEuclidean (E := E)).symm y
    exact (extChartAt I α).right_inv hsymm_target
  have hf_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) f x :=
    hf.mdifferentiable (by simp) x
  have h_fderiv_eq_chain := fderiv_chartSmoothExt_apply_eq_fderiv_scalarOnE
    (I := I) (M := M) α hf hf_support_chart hf_compact (y := y) hy i
  set v_E : E := (toEuclidean (E := E) : E ≃L[ℝ] EuclN_E).symm
    (EuclideanSpace.single i (1 : ℝ)) with hv_E_def
  have h_mfderiv_eq :
      fderiv ℝ
          (CalabiYau.DivergenceTheorem.scalarOnE
            (I := I) α f) ((toEuclidean (E := E)).symm y) v_E =
        mfderiv I 𝓘(ℝ, ℝ) f x
          ((trivializationAt E (TangentSpace I) α).symm x v_E) := by
    rw [← hxy]
    exact (mfderiv_triv_symm_const_eq_fderiv_scalarOnE (I := I)
      α hf_diff hxchart hx_int v_E).symm
  have h_combined :
      fderiv ℝ
          (Sobolev.Chart.chartSmoothExt
            (I := I) (M := M) α f) y
          (EuclideanSpace.single i (1 : ℝ)) =
        mfderiv I 𝓘(ℝ, ℝ) f x
          ((trivializationAt E (TangentSpace I) α).symm x v_E) := by
    rw [h_fderiv_eq_chain, h_mfderiv_eq]
  have h_triv_symm_eq :
      (trivializationAt E (TangentSpace I) α).symm x v_E =
        chartTargetUnitFiber (I := I) α i x := rfl
  rw [h_combined, h_triv_symm_eq]
  rw [← CalabiYau.Riemannian.inner_gradFun
    (I := I) g f x (chartTargetUnitFiber (I := I) α i x)]
  exact g_inner_cauchy_schwarz_sq (I := I) g x
    (CalabiYau.Riemannian.gradFun
      (I := I) g f x)
    (chartTargetUnitFiber (I := I) α i x)

private lemma eLpNorm_chartPushed_le_const_mul_eLpNorm_u
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : CalabiYau.SmoothRiemannianMetric I M)
    (α : M) {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
      eLpNorm (Sobolev.Chart.chartPushed
          (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u) p
          ((volume : Measure EuclN_E).restrict
            (Sobolev.Chart.chartTargetEuclid
              (I := I) (M := M) α)) ≤
        ENNReal.ofReal C *
          eLpNorm u p
            (CalabiYau.RiemannianVolume.riemannianVolumeMeasure I M g) := by
  classical
  set ρ : C^∞⟮I, M; ℝ⟯ :=
    CalabiYau.RiemannianVolume.chartAtlasPOU I M α with hρ_def
  set Kα : Set M := tsupport ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hKα_def
  have hKα_compact : IsCompact Kα := (isClosed_tsupport _).isCompact
  have hKα_sub : Kα ⊆ (chartAt H α).source :=
    CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M α
  obtain ⟨C_K, hC_K_pos, hC_K_bound⟩ :=
    eLpNorm_chartPushedRaw_le_const_mul_eLpNorm_riemannianMeasure_uniform_of_subset
      (I := I) (M := M) g α hKα_compact hKα_sub hp_one hp_top
  refine ⟨C_K, hC_K_pos.le, ?_⟩
  intro u hu
  set f : M → ℝ := fun y : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) y * u y with hf_def
  have hf_meas : Measurable f := (ρ.contMDiff.continuous.measurable).mul hu.continuous.measurable
  have hf_support : tsupport f ⊆ Kα := by
    have h_eq : f = (fun y : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) y • u y) := by
      funext y; rfl
    rw [h_eq]
    exact tsupport_smul_subset_left
      (f := fun y : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) y) (g := u)
  have h_step1 := hC_K_bound hf_meas hf_support
  rw [← CalabiYau.RiemannianVolume.riemannianVolumeMeasure_def
    (I := I) (M := M) g] at h_step1
  have h_ae :=
    Sobolev.Chart.chartPushed_eq_chartPushedRaw_pou_ae
      (I := I) (M := M) (ρ := CalabiYau.RiemannianVolume.chartAtlasPOU I M)
      α u
  rw [eLpNorm_congr_ae h_ae]
  refine h_step1.trans ?_
  gcongr
  apply eLpNorm_mono
  intro x
  have h_abs_f : ‖f x‖ = |((ρ : M → ℝ) x) * u x| := Real.norm_eq_abs _
  have h_abs_u : ‖u x‖ = |u x| := Real.norm_eq_abs _
  rw [h_abs_f, h_abs_u, abs_mul]
  have hρ_abs : |((ρ : M → ℝ) x)| ≤ 1 := abs_chartAtlasPOU_le_one (I := I) (M := M) α x
  calc |((ρ : M → ℝ) x)| * |u x|
      ≤ 1 * |u x| := by gcongr
    _ = |u x| := one_mul _

private lemma abs_fderiv_chartSmoothExt_apply_pou_mul_le
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : CalabiYau.SmoothRiemannianMetric I M)
    (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
      ∀ (i : Fin (Module.finrank ℝ E)) (y : EuclN_E),
        |fderiv ℝ
          (Sobolev.Chart.chartSmoothExt
            (I := I) (M := M) α
            (fun z : M => ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z)) y
            (EuclideanSpace.single i (1 : ℝ))| ≤
          K *
            Sobolev.Chart.chartPushedRaw I α
              (fun x : M => |u x| +
                Real.sqrt
                  (g.inner x
                    (CalabiYau.Riemannian.gradFun
                      (I := I) g u x)
                    (CalabiYau.Riemannian.gradFun
                      (I := I) g u x))) y := by
  classical
  set M_α : ℝ := chartTargetUnitSqSumSupOnPouTsupport (I := I) (M := M) g α with hM_α_def
  have hM_α_nn : 0 ≤ M_α := chartTargetUnitSqSumSupOnPouTsupport_nonneg
    (I := I) (M := M) g α
  set ρ : C^∞⟮I, M; ℝ⟯ :=
    CalabiYau.RiemannianVolume.chartAtlasPOU I M α with hρ_def
  obtain ⟨K_grad_ρ, hK_grad_ρ_nn, hK_grad_ρ_bound⟩ :=
    exists_continuous_sup_of_compactSpace (M := M)
      (f := fun x : M => Real.sqrt
        (g.inner x
          (CalabiYau.Riemannian.gradFun (I := I) g
            ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
          (CalabiYau.Riemannian.gradFun (I := I) g
            ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)))
      (continuous_sqrt_g_inner_gradFun_self (I := I) (M := M) g ρ.contMDiff)
      (fun _ => Real.sqrt_nonneg _)
  set K_grad := max (1 : ℝ) K_grad_ρ
  have hK_grad_nn : 0 ≤ K_grad := le_trans zero_le_one (le_max_left _ _)
  refine ⟨K_grad * Real.sqrt M_α, mul_nonneg hK_grad_nn (Real.sqrt_nonneg _), ?_⟩
  intro u hu i y
  set f : M → ℝ := fun z : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z with hf_def
  have hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := ρ.contMDiff.mul hu
  have hf_support_chart : tsupport f ⊆ (chartAt H α).source := by
    have h1 : tsupport f ⊆ tsupport ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
      have h_eq : f = (fun z : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) z • u z) := by
        funext z; rfl
      rw [h_eq]
      exact tsupport_smul_subset_left
        (f := fun z : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) z) (g := u)
    exact h1.trans
      (CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M α)
  have hf_compact : IsCompact (tsupport f) := (isClosed_tsupport _).isCompact
  have hK_grad_bound : ∀ x : M, Real.sqrt
        (g.inner x
          (CalabiYau.Riemannian.gradFun (I := I) g f x)
          (CalabiYau.Riemannian.gradFun (I := I) g f x)) ≤
      K_grad *
        (|u x| + Real.sqrt
          (g.inner x
            (CalabiYau.Riemannian.gradFun (I := I) g u x)
            (CalabiYau.Riemannian.gradFun (I := I) g u x))) := by
    intro x
    obtain ⟨K', hK'_nn, hK'_bound⟩ := sqrt_g_inner_gradFun_pou_mul_le (I := I) (M := M) g α hu
    have hρ_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x :=
      ρ.contMDiff.mdifferentiable (by simp) x
    have hu_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) u x :=
      hu.mdifferentiable (by simp) x
    have h_grad_eq := gradFun_mul_pointwise (I := I) g (ρ := (ρ : M → ℝ)) (u := u)
      (x := x) hρ_diff hu_diff
    set gu : TangentSpace I x :=
      CalabiYau.Riemannian.gradFun (I := I) g u x
    set gρ : TangentSpace I x :=
      CalabiYau.Riemannian.gradFun (I := I) g
        ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x
    set a : TangentSpace I x := ((ρ : M → ℝ)) x • gu
    set b : TangentSpace I x := u x • gρ
    rw [h_grad_eq]
    have h_inner_self_nn : ∀ z : TangentSpace I x, 0 ≤ g.inner x z z := by
      intro z
      by_cases hz : z = 0
      · rw [hz]
        change ((g.inner x) (0 : TangentSpace I x)) (0 : TangentSpace I x) ≥ 0
        rw [(g.inner x).map_zero]
        change (0 : TangentSpace I x →L[ℝ] ℝ) (0 : TangentSpace I x) ≥ 0
        simp
      · exact (g.pos x z hz).le
    have h_a_nn : 0 ≤ g.inner x a a := h_inner_self_nn _
    have h_b_nn : 0 ≤ g.inner x b b := h_inner_self_nn _
    have hsym : g.inner x a b = g.inner x b a := g.symm x a b
    have h_apb_eq : g.inner x (a + b) (a + b) =
        g.inner x a a + 2 * g.inner x a b + g.inner x b b := by
      have h_step : g.inner x (a + b) (a + b) =
          g.inner x a (a + b) + g.inner x b (a + b) := by
        have h1 : (g.inner x) (a + b) = (g.inner x) a + (g.inner x) b :=
          (g.inner x).map_add a b
        change ((g.inner x) (a + b)) (a + b) = _
        rw [h1]
        rfl
      rw [h_step, (g.inner x a).map_add, (g.inner x b).map_add]
      rw [hsym]; ring
    have h_CS_ab := abs_g_inner_le_sqrt_mul_sqrt (I := I) g x a b
    have h_apb_le_sum_sq :
        g.inner x (a + b) (a + b) ≤
          (Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b))^2 := by
      rw [h_apb_eq]
      have h_sqrt_a_sq : Real.sqrt (g.inner x a a)^2 = g.inner x a a :=
        Real.sq_sqrt h_a_nn
      have h_sqrt_b_sq : Real.sqrt (g.inner x b b)^2 = g.inner x b b :=
        Real.sq_sqrt h_b_nn
      have h_2ab_le : 2 * g.inner x a b ≤
          2 * (Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b)) := by
        have h_le_abs : g.inner x a b ≤ |g.inner x a b| := le_abs_self _
        linarith
      nlinarith [h_2ab_le, h_sqrt_a_sq, h_sqrt_b_sq,
        Real.sqrt_nonneg (g.inner x a a), Real.sqrt_nonneg (g.inner x b b)]
    have h_sum_nn : 0 ≤ Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b) :=
      add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have h_sqrt_apb_le : Real.sqrt (g.inner x (a + b) (a + b)) ≤
        Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b) := by
      have h := Real.sqrt_le_sqrt h_apb_le_sum_sq
      rw [Real.sqrt_sq h_sum_nn] at h
      exact h
    refine h_sqrt_apb_le.trans ?_
    have h_sqrt_a : Real.sqrt (g.inner x a a) =
        |((ρ : M → ℝ)) x| * Real.sqrt (g.inner x gu gu) := by
      have h_a_self_eq : g.inner x a a = ((ρ : M → ℝ) x)^2 * g.inner x gu gu := by
        change (g.inner x ((((ρ : M → ℝ) x)) • gu)) ((((ρ : M → ℝ) x)) • gu) =
          _ * g.inner x gu gu
        rw [(g.inner x).map_smul, smul_apply]
        rw [(g.inner x gu).map_smul]
        simp [smul_eq_mul, sq]; ring
      rw [h_a_self_eq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
    have h_sqrt_b : Real.sqrt (g.inner x b b) =
        |u x| * Real.sqrt (g.inner x gρ gρ) := by
      have h_b_self_eq : g.inner x b b = (u x)^2 * g.inner x gρ gρ := by
        change (g.inner x ((u x) • gρ)) ((u x) • gρ) = _ * g.inner x gρ gρ
        rw [(g.inner x).map_smul, smul_apply]
        rw [(g.inner x gρ).map_smul]
        simp [smul_eq_mul, sq]; ring
      rw [h_b_self_eq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
    rw [h_sqrt_a, h_sqrt_b]
    have hρ_abs : |((ρ : M → ℝ)) x| ≤ 1 := abs_chartAtlasPOU_le_one (I := I) (M := M) α x
    have hsqrt_gu_nn : 0 ≤ Real.sqrt (g.inner x gu gu) := Real.sqrt_nonneg _
    have hsqrt_gρ_nn : 0 ≤ Real.sqrt (g.inner x gρ gρ) := Real.sqrt_nonneg _
    have h_term1 : |((ρ : M → ℝ)) x| * Real.sqrt (g.inner x gu gu) ≤
        Real.sqrt (g.inner x gu gu) := by
      calc |((ρ : M → ℝ)) x| * Real.sqrt (g.inner x gu gu)
          ≤ 1 * Real.sqrt (g.inner x gu gu) :=
            mul_le_mul_of_nonneg_right hρ_abs hsqrt_gu_nn
        _ = Real.sqrt (g.inner x gu gu) := one_mul _
    have h_term2 : |u x| * Real.sqrt (g.inner x gρ gρ) ≤ |u x| * K_grad_ρ :=
      mul_le_mul_of_nonneg_left (hK_grad_ρ_bound x) (abs_nonneg _)
    have hM := le_max_left (1 : ℝ) K_grad_ρ
    have hM' := le_max_right (1 : ℝ) K_grad_ρ
    have h_step1 : Real.sqrt (g.inner x gu gu) ≤ K_grad * Real.sqrt (g.inner x gu gu) := by
      have := mul_le_mul_of_nonneg_right hM hsqrt_gu_nn
      linarith
    have h_step2 : K_grad_ρ * |u x| ≤ K_grad * |u x| :=
      mul_le_mul_of_nonneg_right hM' (abs_nonneg _)
    calc |((ρ : M → ℝ)) x| * Real.sqrt (g.inner x gu gu) +
          |u x| * Real.sqrt (g.inner x gρ gρ)
        ≤ Real.sqrt (g.inner x gu gu) + |u x| * K_grad_ρ :=
          add_le_add h_term1 h_term2
      _ = Real.sqrt (g.inner x gu gu) + K_grad_ρ * |u x| := by ring
      _ ≤ K_grad * Real.sqrt (g.inner x gu gu) + K_grad * |u x| :=
          add_le_add h_step1 h_step2
      _ = K_grad * (|u x| + Real.sqrt (g.inner x gu gu)) := by ring
  by_cases hy_in : y ∈
      Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α
  · set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_def
    have h_sq_bound := sq_fderiv_chartSmoothExt_apply_le_g_inner_mul (I := I) (M := M) g
      α hf_smooth hf_support_chart hf_compact (y := y) hy_in i
    have h_lhs_nn : 0 ≤ |fderiv ℝ
        (Sobolev.Chart.chartSmoothExt
          (I := I) (M := M) α f) y (EuclideanSpace.single i (1 : ℝ))| := abs_nonneg _
    have h_grad_f_nn : 0 ≤ g.inner x
        (CalabiYau.Riemannian.gradFun (I := I) g f x)
        (CalabiYau.Riemannian.gradFun (I := I) g f x) := by
      by_cases hzero :
          CalabiYau.Riemannian.gradFun (I := I) g f x = 0
      · rw [hzero]
        change ((g.inner x) (0 : TangentSpace I x)) (0 : TangentSpace I x) ≥ 0
        rw [(g.inner x).map_zero]
        change (0 : TangentSpace I x →L[ℝ] ℝ) (0 : TangentSpace I x) ≥ 0
        simp
      · exact (g.pos x _ hzero).le
    have h_abs_le_sqrt :
        |fderiv ℝ
            (Sobolev.Chart.chartSmoothExt
              (I := I) (M := M) α f) y
            (EuclideanSpace.single i (1 : ℝ))| ≤
          Real.sqrt
            (g.inner x
              (CalabiYau.Riemannian.gradFun (I := I) g f x)
              (CalabiYau.Riemannian.gradFun (I := I) g f x)) *
            Real.sqrt
              (g.inner x
                (chartTargetUnitFiber (I := I) α i x)
                (chartTargetUnitFiber (I := I) α i x)) := by
      have h := Real.sqrt_le_sqrt h_sq_bound
      rw [Real.sqrt_sq_eq_abs] at h
      rw [Real.sqrt_mul h_grad_f_nn] at h
      exact h
    refine h_abs_le_sqrt.trans ?_
    by_cases hx_pou : x ∈ tsupport ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ)
    · have h_w_nn : ∀ j : Fin (Module.finrank ℝ E), 0 ≤
          g.inner x
            (chartTargetUnitFiber (I := I) α j x)
            (chartTargetUnitFiber (I := I) α j x) := fun j => by
        by_cases hzero : chartTargetUnitFiber (I := I) α j x = 0
        · rw [hzero]
          rw [(g.inner x).map_zero]
          change (0 : ℝ) ≤ (0 : TangentSpace I x →L[ℝ] ℝ) (0 : TangentSpace I x)
          simp
        · exact (g.pos x _ hzero).le
      have h_w_i_le_sum : g.inner x
          (chartTargetUnitFiber (I := I) α i x)
          (chartTargetUnitFiber (I := I) α i x) ≤
          ∑ j : Fin (Module.finrank ℝ E),
            g.inner x
              (chartTargetUnitFiber (I := I) α j x)
              (chartTargetUnitFiber (I := I) α j x) :=
        Finset.single_le_sum (s := Finset.univ)
          (f := fun j : Fin (Module.finrank ℝ E) =>
            g.inner x
              (chartTargetUnitFiber (I := I) α j x)
              (chartTargetUnitFiber (I := I) α j x))
          (fun j _ => h_w_nn j) (Finset.mem_univ i)
      have h_w_i_le_M : g.inner x
          (chartTargetUnitFiber (I := I) α i x)
          (chartTargetUnitFiber (I := I) α i x) ≤ M_α :=
        h_w_i_le_sum.trans (chartTargetUnitSqSum_le_sup (I := I) (M := M) g α hx_pou)
      have h_sqrt_w_le_sqrt_M :
          Real.sqrt
            (g.inner x
              (chartTargetUnitFiber (I := I) α i x)
              (chartTargetUnitFiber (I := I) α i x)) ≤ Real.sqrt M_α :=
        Real.sqrt_le_sqrt h_w_i_le_M
      have h_sqrt_grad_f_nn : 0 ≤ Real.sqrt
          (g.inner x
            (CalabiYau.Riemannian.gradFun (I := I) g f x)
            (CalabiYau.Riemannian.gradFun (I := I) g f x)) :=
        Real.sqrt_nonneg _
      calc Real.sqrt
            (g.inner x
              (CalabiYau.Riemannian.gradFun (I := I) g f x)
              (CalabiYau.Riemannian.gradFun (I := I) g f x)) *
            Real.sqrt
              (g.inner x
                (chartTargetUnitFiber (I := I) α i x)
                (chartTargetUnitFiber (I := I) α i x))
          ≤ Real.sqrt
              (g.inner x
                (CalabiYau.Riemannian.gradFun (I := I) g f x)
                (CalabiYau.Riemannian.gradFun (I := I) g f x)) *
              Real.sqrt M_α :=
            mul_le_mul_of_nonneg_left h_sqrt_w_le_sqrt_M h_sqrt_grad_f_nn
        _ ≤ K_grad * (|u x| +
              Real.sqrt
                (g.inner x
                  (CalabiYau.Riemannian.gradFun (I := I) g u x)
                  (CalabiYau.Riemannian.gradFun (I := I) g u x))) *
              Real.sqrt M_α :=
            mul_le_mul_of_nonneg_right (hK_grad_bound x) (Real.sqrt_nonneg _)
        _ = K_grad * Real.sqrt M_α * (|u x| +
              Real.sqrt
                (g.inner x
                  (CalabiYau.Riemannian.gradFun (I := I) g u x)
                  (CalabiYau.Riemannian.gradFun (I := I) g u x))) :=
                    by ring
        _ = K_grad * Real.sqrt M_α *
              Sobolev.Chart.chartPushedRaw I α
                (fun z : M => |u z| +
                  Real.sqrt
                    (g.inner z
                      (CalabiYau.Riemannian.gradFun (I := I) g u z)
                      (CalabiYau.Riemannian.gradFun (I := I) g u z)))
                        y := by
            rw [Sobolev.Chart.chartPushedRaw_apply_of_mem
              (I := I) α (fun z : M => |u z| +
                Real.sqrt
                  (g.inner z
                    (CalabiYau.Riemannian.gradFun (I := I) g u z)
                    (CalabiYau.Riemannian.gradFun (I := I) g u z)))
                      hy_in]
    · have hx_off_f : x ∉ tsupport f :=
        fun hin => hx_pou ((tsupport_smul_subset_left
          (f := fun z : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) z) (g := u)) hin)
      have h_grad_f_zero : CalabiYau.Riemannian.gradFun
          (I := I) g f x = 0 := by
        have hopen : IsOpen (tsupport f)ᶜ := (isClosed_tsupport _).isOpen_compl
        have h_nhds : (tsupport f)ᶜ ∈ 𝓝 x := hopen.mem_nhds hx_off_f
        have heqz : f =ᶠ[𝓝 x] (fun _ : M => (0 : ℝ)) := by
          filter_upwards [h_nhds] with y hy
          exact image_eq_zero_of_notMem_tsupport hy
        have h_mfd_eq : mfderiv I 𝓘(ℝ, ℝ) f x = 0 := by
          rw [heqz.mfderiv_eq]; exact mfderiv_const
        exact CalabiYau.Riemannian.gradFun_eq_zero_of_mfderiv_eq_zero
          g f h_mfd_eq
      have h_grad_f_inner_zero : g.inner x
          (CalabiYau.Riemannian.gradFun (I := I) g f x)
          (CalabiYau.Riemannian.gradFun (I := I) g f x) = 0 := by
        rw [h_grad_f_zero]
        rw [(g.inner x).map_zero]
        change (0 : TangentSpace I x →L[ℝ] ℝ) (0 : TangentSpace I x) = 0
        simp
      rw [h_grad_f_inner_zero, Real.sqrt_zero, zero_mul]
      apply mul_nonneg (mul_nonneg hK_grad_nn (Real.sqrt_nonneg _))
      rw [Sobolev.Chart.chartPushedRaw_apply_of_mem
        (I := I) α (fun z : M => |u z| +
          Real.sqrt
            (g.inner z
              (CalabiYau.Riemannian.gradFun (I := I) g u z)
              (CalabiYau.Riemannian.gradFun (I := I) g u z))) hy_in]
      exact add_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  · have h_chartSmoothExt_smooth : ContDiff ℝ ∞
        (Sobolev.Chart.chartSmoothExt
          (I := I) (M := M) α f) :=
      contDiff_chartSmoothExt_pou_mul_local_reverse (I := I) (M := M) α hu
    set K : Set EuclN_E := (toEuclidean (E := E)) ''
      ((extChartAt I α) '' (tsupport f)) with hK_def
    have hK_compact : IsCompact K := by
      have h_extChart_cont : ContinuousOn (extChartAt I α) (tsupport f) :=
        (continuousOn_extChartAt α).mono (by
          intro x hx
          rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
            (I := I) (M := M)]
          exact hf_support_chart hx)
      have h1 : IsCompact ((extChartAt I α) '' (tsupport f)) :=
        hf_compact.image_of_continuousOn h_extChart_cont
      exact h1.image (toEuclidean (E := E)).continuous
    have hK_subset : K ⊆
        Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α := by
      rintro y' ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      have hxsource : x ∈ (extChartAt I α).source := by
        rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
          (I := I) (M := M)]
        exact hf_support_chart hx
      exact ⟨extChartAt I α x, (extChartAt I α).map_source hxsource, rfl⟩
    have hy_off_K : y ∉ K := fun hy_in_K => hy_in (hK_subset hy_in_K)
    have hK_compl_open : IsOpen Kᶜ := hK_compact.isClosed.isOpen_compl
    have h_nhds : Kᶜ ∈ 𝓝 y := hK_compl_open.mem_nhds hy_off_K
    have h_eqz : (Sobolev.Chart.chartSmoothExt
        (I := I) (M := M) α f) =ᶠ[𝓝 y] (fun _ : EuclN_E => (0 : ℝ)) := by
      filter_upwards [h_nhds] with z hz
      classical
      by_cases hz_target : (toEuclidean (E := E)).symm z ∈ (extChartAt I α).target
      · have hsymm_source : (extChartAt I α).symm
            ((toEuclidean (E := E)).symm z) ∈ (extChartAt I α).source :=
          (extChartAt I α).map_target hz_target
        have hxsupp : (extChartAt I α).symm ((toEuclidean (E := E)).symm z) ∉ tsupport f := by
          intro hin
          apply hz
          refine ⟨(toEuclidean (E := E)).symm z, ?_, ?_⟩
          · refine ⟨(extChartAt I α).symm ((toEuclidean (E := E)).symm z), hin, ?_⟩
            exact (extChartAt I α).right_inv hz_target
          · exact (toEuclidean (E := E)).apply_symm_apply z
        have hf_zero : f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) = 0 :=
          image_eq_zero_of_notMem_tsupport hxsupp
        change (if (toEuclidean (E := E)).symm z ∈ (extChartAt I α).target then
                  f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
                else (0 : ℝ)) = 0
        rw [if_pos hz_target, hf_zero]
      · change (if (toEuclidean (E := E)).symm z ∈ (extChartAt I α).target then
                  f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
                else (0 : ℝ)) = 0
        rw [if_neg hz_target]
    have h_fderiv_zero : fderiv ℝ
        (Sobolev.Chart.chartSmoothExt
          (I := I) (M := M) α f) y = 0 := by
      rw [h_eqz.fderiv_eq]
      exact fderiv_const_apply 0
    rw [h_fderiv_zero]
    change |((0 : EuclN_E →L[ℝ] ℝ) (EuclideanSpace.single i (1 : ℝ)))| ≤ _
    rw [zero_apply, abs_zero]
    apply mul_nonneg (mul_nonneg hK_grad_nn (Real.sqrt_nonneg _))
    rw [Sobolev.Chart.chartPushedRaw_apply_of_notMem
      (I := I) α (fun z : M => |u z| +
        Real.sqrt
          (g.inner z
            (CalabiYau.Riemannian.gradFun (I := I) g u z)
            (CalabiYau.Riemannian.gradFun (I := I) g u z))) hy_in]

private lemma abs_fderiv_chartSmoothExt_apply_pou_mul_le_indicator
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : CalabiYau.SmoothRiemannianMetric I M)
    (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
      ∀ (i : Fin (Module.finrank ℝ E)) (y : EuclN_E),
        |fderiv ℝ
          (Sobolev.Chart.chartSmoothExt
            (I := I) (M := M) α
            (fun z : M => ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z)) y
            (EuclideanSpace.single i (1 : ℝ))| ≤
          K *
            Sobolev.Chart.chartPushedRaw I α
              (Set.indicator
                (tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
                  : C^∞⟮I, M; ℝ⟯) : M → ℝ))
                (fun x : M => |u x| +
                  Real.sqrt
                    (g.inner x
                      (CalabiYau.Riemannian.gradFun
                        (I := I) g u x)
                      (CalabiYau.Riemannian.gradFun
                        (I := I) g u x)))) y := by
  classical
  obtain ⟨K, hK_nn, hK_bound⟩ :=
    abs_fderiv_chartSmoothExt_apply_pou_mul_le (I := I) (M := M) g α
  refine ⟨K, hK_nn, ?_⟩
  intro u hu i y
  by_cases hy_in : y ∈
      Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α
  · have h_full := hK_bound (u := u) hu i y
    rw [Sobolev.Chart.chartPushedRaw_apply_of_mem
      (I := I) α _ hy_in] at h_full
    rw [Sobolev.Chart.chartPushedRaw_apply_of_mem
      (I := I) α _ hy_in]
    set ρ : C^∞⟮I, M; ℝ⟯ :=
      CalabiYau.RiemannianVolume.chartAtlasPOU I M α with hρ_def
    set Kα : Set M := tsupport ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hKα_def
    set v : M → ℝ := fun x : M => |u x| +
      Real.sqrt
        (g.inner x
          (CalabiYau.Riemannian.gradFun (I := I) g u x)
          (CalabiYau.Riemannian.gradFun (I := I) g u x))
      with hv_def
    set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_def
    by_cases hx_Kα : x ∈ Kα
    · change _ ≤ K * (Set.indicator Kα v) x
      rw [Set.indicator_of_mem hx_Kα]
      exact h_full
    · change _ ≤ K * (Set.indicator Kα v) x
      rw [Set.indicator_of_notMem hx_Kα, mul_zero]
      set f : M → ℝ := fun z : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z with hf_def
      have hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := ρ.contMDiff.mul hu
      have hf_support : tsupport f ⊆ Kα := by
        have h_eq : f = (fun z : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) z • u z) := by
          funext z; rfl
        rw [h_eq]
        exact tsupport_smul_subset_left
          (f := fun z : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) z) (g := u)
      have hf_support_chart : tsupport f ⊆ (chartAt H α).source :=
        hf_support.trans (CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M α)
      have hf_compact : IsCompact (tsupport f) := (isClosed_tsupport _).isCompact
      have hx_off_f : x ∉ tsupport f := fun hin => hx_Kα (hf_support hin)
      have h_grad_zero : CalabiYau.Riemannian.gradFun
          (I := I) g f x = 0 := by
        have hopen : IsOpen (tsupport f)ᶜ := (isClosed_tsupport _).isOpen_compl
        have h_nhds : (tsupport f)ᶜ ∈ 𝓝 x := hopen.mem_nhds hx_off_f
        have heqz : f =ᶠ[𝓝 x] (fun _ : M => (0 : ℝ)) := by
          filter_upwards [h_nhds] with y' hy' using image_eq_zero_of_notMem_tsupport hy'
        have h_mfd_eq : mfderiv I 𝓘(ℝ, ℝ) f x = 0 := by
          rw [heqz.mfderiv_eq]; exact mfderiv_const
        exact CalabiYau.Riemannian.gradFun_eq_zero_of_mfderiv_eq_zero
          g f h_mfd_eq
      have h_sq := sq_fderiv_chartSmoothExt_apply_le_g_inner_mul (I := I) (M := M) g
        α hf_smooth hf_support_chart hf_compact (y := y) hy_in i
      simp only at h_sq
      have h_inner_zero : g.inner x
          (CalabiYau.Riemannian.gradFun (I := I) g f x)
          (CalabiYau.Riemannian.gradFun (I := I) g f x) = 0 := by
        rw [h_grad_zero]
        rw [(g.inner x).map_zero]
        change (0 : TangentSpace I x →L[ℝ] ℝ) (0 : TangentSpace I x) = 0
        simp
      rw [h_inner_zero, zero_mul] at h_sq
      have h_sq_eq : (fderiv ℝ
          (Sobolev.Chart.chartSmoothExt
            (I := I) (M := M) α f) y (EuclideanSpace.single i (1 : ℝ)))^2 = 0 :=
        le_antisymm h_sq (sq_nonneg _)
      have h_zero : fderiv ℝ
          (Sobolev.Chart.chartSmoothExt
            (I := I) (M := M) α f) y (EuclideanSpace.single i (1 : ℝ)) = 0 :=
        pow_eq_zero_iff (two_ne_zero) |>.mp h_sq_eq
      change |fderiv ℝ
        (Sobolev.Chart.chartSmoothExt
          (I := I) (M := M) α f) y (EuclideanSpace.single i (1 : ℝ))| ≤ 0
      rw [h_zero, abs_zero]
  · have h_full := hK_bound (u := u) hu i y
    rw [Sobolev.Chart.chartPushedRaw_apply_of_notMem
      (I := I) α _ hy_in] at h_full
    rw [Sobolev.Chart.chartPushedRaw_apply_of_notMem
      (I := I) α _ hy_in]
    exact h_full

theorem eLpNorm_fderiv_chartSmoothExt_apply_le_const_mul
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : CalabiYau.SmoothRiemannianMetric I M)
    (α : M) {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
      ∀ i : Fin (Module.finrank ℝ E),
        eLpNorm (fun y : EuclN_E => fderiv ℝ
            (Sobolev.Chart.chartSmoothExt
              (I := I) (M := M) α
              (fun z : M => ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
                : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z)) y
              (EuclideanSpace.single i (1 : ℝ))) p
            ((volume : Measure EuclN_E).restrict
              (Sobolev.Chart.chartTargetEuclid
                (I := I) (M := M) α)) ≤
          ENNReal.ofReal C *
            (eLpNorm u p
                (CalabiYau.RiemannianVolume.riemannianVolumeMeasure I M g) +
              eLpNorm (fun x : M => Real.sqrt
                  (g.inner x
                    (CalabiYau.Riemannian.gradFun (I := I) g u x)
                    (CalabiYau.Riemannian.gradFun (I := I) g u x))) p
                (CalabiYau.RiemannianVolume.riemannianVolumeMeasure I M g)) := by
  classical
  set ρ : C^∞⟮I, M; ℝ⟯ :=
    CalabiYau.RiemannianVolume.chartAtlasPOU I M α
  set Kα : Set M := tsupport ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ)
  have hKα_compact : IsCompact Kα := (isClosed_tsupport _).isCompact
  have hKα_sub : Kα ⊆ (chartAt H α).source :=
    CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M α
  obtain ⟨K, hK_nn, hK_bound⟩ :=
    abs_fderiv_chartSmoothExt_apply_pou_mul_le_indicator (I := I) (M := M) g α
  obtain ⟨C_K, hC_K_pos, hC_K_bound⟩ :=
    eLpNorm_chartPushedRaw_le_const_mul_eLpNorm_riemannianMeasure_uniform_of_subset
      (I := I) (M := M) g α hKα_compact hKα_sub hp_one hp_top
  refine ⟨K * C_K, mul_nonneg hK_nn hC_K_pos.le, ?_⟩
  intro u hu i
  set v : M → ℝ := fun x : M => |u x| +
    Real.sqrt
      (g.inner x
        (CalabiYau.Riemannian.gradFun (I := I) g u x)
        (CalabiYau.Riemannian.gradFun (I := I) g u x))
  set v_α : M → ℝ := Set.indicator Kα v
  have hv_meas : Measurable v := by
    have h_abs_meas : Measurable (fun x : M => |u x|) := hu.continuous.measurable.abs
    have h_grad_meas : Measurable (fun x : M => Real.sqrt
      (g.inner x
        (CalabiYau.Riemannian.gradFun (I := I) g u x)
        (CalabiYau.Riemannian.gradFun (I := I) g u x))) :=
      (continuous_sqrt_g_inner_gradFun_self (I := I) (M := M) g hu).measurable
    exact h_abs_meas.add h_grad_meas
  have hv_α_meas : Measurable v_α :=
    Measurable.indicator hv_meas (isClosed_tsupport _).measurableSet
  have hv_α_support : tsupport v_α ⊆ Kα := by
    apply closure_minimal _ (isClosed_tsupport _)
    intro x hx
    by_contra hxc
    apply hx
    change (Set.indicator Kα v) x = 0
    rw [Set.indicator_of_notMem hxc]
  have h_pt : ∀ y : EuclN_E, ‖fderiv ℝ
        (Sobolev.Chart.chartSmoothExt
          (I := I) (M := M) α
          (fun z : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z)) y
          (EuclideanSpace.single i (1 : ℝ))‖ ≤
      K * Sobolev.Chart.chartPushedRaw I α v_α y := by
    intro y
    rw [Real.norm_eq_abs]
    exact hK_bound (u := u) hu i y
  have h_eLp_le : eLpNorm (fun y : EuclN_E => fderiv ℝ
        (Sobolev.Chart.chartSmoothExt
          (I := I) (M := M) α
          (fun z : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z)) y
          (EuclideanSpace.single i (1 : ℝ))) p
        ((volume : Measure EuclN_E).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)) ≤
      eLpNorm (fun y : EuclN_E => K *
        Sobolev.Chart.chartPushedRaw I α v_α y) p
        ((volume : Measure EuclN_E).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)) := eLpNorm_mono_real h_pt
  refine h_eLp_le.trans ?_
  have h_pull_K : eLpNorm (fun y : EuclN_E => K *
      Sobolev.Chart.chartPushedRaw I α v_α y) p
      ((volume : Measure EuclN_E).restrict
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)) =
    ENNReal.ofReal K *
    eLpNorm (Sobolev.Chart.chartPushedRaw I α v_α) p
      ((volume : Measure EuclN_E).restrict
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)) := by
    have h_eq_smul : (fun y : EuclN_E => K *
        Sobolev.Chart.chartPushedRaw I α v_α y) =
      K • (Sobolev.Chart.chartPushedRaw I α v_α) := by
      funext y
      change K * _ = K • _
      rw [smul_eq_mul]
    rw [h_eq_smul]
    rw [eLpNorm_const_smul (𝕜 := ℝ) (c := K)
      (f := Sobolev.Chart.chartPushedRaw I α v_α)]
    have hK_enorm : ‖K‖ₑ = ENNReal.ofReal K := Real.enorm_eq_ofReal hK_nn
    rw [hK_enorm]
  rw [h_pull_K]
  have h_step2 := hC_K_bound hv_α_meas hv_α_support
  rw [← CalabiYau.RiemannianVolume.riemannianVolumeMeasure_def
    (I := I) (M := M) g] at h_step2
  have h_v_α_le : ∀ x, ‖v_α x‖ ≤ |u x| +
      Real.sqrt
        (g.inner x
          (CalabiYau.Riemannian.gradFun (I := I) g u x)
          (CalabiYau.Riemannian.gradFun (I := I) g u x)) := by
    intro x
    change ‖(Set.indicator Kα v) x‖ ≤ _
    rw [Real.norm_eq_abs]
    by_cases hx : x ∈ Kα
    · rw [Set.indicator_of_mem hx]
      have hv_nn : 0 ≤ v x := add_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
      rw [abs_of_nonneg hv_nn]
    · rw [Set.indicator_of_notMem hx, abs_zero]
      exact add_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have h_v_α_eLp_le : eLpNorm v_α p
      (CalabiYau.RiemannianVolume.riemannianVolumeMeasure I M g) ≤
    eLpNorm u p
        (CalabiYau.RiemannianVolume.riemannianVolumeMeasure I M g) +
      eLpNorm (fun x : M => Real.sqrt
          (g.inner x
            (CalabiYau.Riemannian.gradFun (I := I) g u x)
            (CalabiYau.Riemannian.gradFun (I := I) g u x))) p
        (CalabiYau.RiemannianVolume.riemannianVolumeMeasure I M g) := by
    refine (eLpNorm_mono_real h_v_α_le).trans ?_
    have h_aesm_u : AEStronglyMeasurable (fun x : M => |u x|)
        (CalabiYau.RiemannianVolume.riemannianVolumeMeasure I M g) :=
      hu.continuous.measurable.abs.aestronglyMeasurable
    have h_aesm_grad : AEStronglyMeasurable (fun x : M => Real.sqrt
        (g.inner x
          (CalabiYau.Riemannian.gradFun (I := I) g u x)
          (CalabiYau.Riemannian.gradFun (I := I) g u x)))
        (CalabiYau.RiemannianVolume.riemannianVolumeMeasure I M g) :=
      (continuous_sqrt_g_inner_gradFun_self (I := I) (M := M) g hu).aestronglyMeasurable
    refine (eLpNorm_add_le h_aesm_u h_aesm_grad hp_one).trans ?_
    have h_eLp_u_eq : eLpNorm (fun x : M => |u x|) p
        (CalabiYau.RiemannianVolume.riemannianVolumeMeasure I M g) =
        eLpNorm u p
          (CalabiYau.RiemannianVolume.riemannianVolumeMeasure I M g) := by
      have h_eq : (fun x : M => |u x|) = fun x : M => ‖u x‖ := by
        funext x; rw [Real.norm_eq_abs]
      rw [h_eq]
      exact eLpNorm_norm u
    rw [h_eLp_u_eq]
  calc ENNReal.ofReal K *
        eLpNorm (Sobolev.Chart.chartPushedRaw I α v_α) p
          ((volume : Measure EuclN_E).restrict
            (Sobolev.Chart.chartTargetEuclid
              (I := I) (M := M) α))
      ≤ ENNReal.ofReal K *
          (ENNReal.ofReal C_K *
            eLpNorm v_α p
              (CalabiYau.RiemannianVolume.riemannianVolumeMeasure I M g)) := by
        gcongr
    _ ≤ ENNReal.ofReal K *
          (ENNReal.ofReal C_K *
            (eLpNorm u p
                (CalabiYau.RiemannianVolume.riemannianVolumeMeasure I M g) +
              eLpNorm (fun x : M => Real.sqrt
                  (g.inner x
                    (CalabiYau.Riemannian.gradFun (I := I) g u x)
                    (CalabiYau.Riemannian.gradFun (I := I) g u x))) p
                (CalabiYau.RiemannianVolume.riemannianVolumeMeasure I M g))) := by
        gcongr
    _ = ENNReal.ofReal (K * C_K) *
          (eLpNorm u p
              (CalabiYau.RiemannianVolume.riemannianVolumeMeasure I M g) +
            eLpNorm (fun x : M => Real.sqrt
                (g.inner x
                  (CalabiYau.Riemannian.gradFun (I := I) g u x)
                  (CalabiYau.Riemannian.gradFun (I := I) g u x))) p
              (CalabiYau.RiemannianVolume.riemannianVolumeMeasure I M g)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hK_nn]

private lemma sum_Fin1_eq_sum_Fin (d : ℕ)
    (f : Fin (d) → ℝ≥0∞) :
    ∑ β : Fin 1 → Fin d, f (β 0) = ∑ i : Fin d, f i := by
  classical
  let e : (Fin 1 → Fin d) ≃ Fin d :=
    { toFun := fun β => β 0
      invFun := fun i _ => i
      left_inv := fun β => by funext j; have hj : j = 0 := Subsingleton.elim _ _; rw [hj]
      right_inv := fun _ => rfl }
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

private lemma wkpNorm_chartPushed_le_const_mul_per_α
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : CalabiYau.SmoothRiemannianMetric I M)
    (α : M) {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
      Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 p
          (Sobolev.Chart.chartPushed
            (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α) ≤
        ENNReal.ofReal C *
          (eLpNorm u p
              (CalabiYau.RiemannianVolume.riemannianVolumeMeasure I M g) +
            eLpNorm (fun x : M => Real.sqrt
                (g.inner x
                  (CalabiYau.Riemannian.gradFun (I := I) g u x)
                  (CalabiYau.Riemannian.gradFun (I := I) g u x))) p
              (CalabiYau.RiemannianVolume.riemannianVolumeMeasure I M g)) := by
  classical
  obtain ⟨C_Lp, hC_Lp_nn, hC_Lp_bound⟩ :=
    eLpNorm_chartPushed_le_const_mul_eLpNorm_u (I := I) (M := M) g α hp_one hp_top
  obtain ⟨C_grad, hC_grad_nn, hC_grad_bound⟩ :=
    eLpNorm_fderiv_chartSmoothExt_apply_le_const_mul (I := I) (M := M) g α hp_one hp_top
  refine ⟨C_Lp + (Module.finrank ℝ E : ℝ) * C_grad,
    add_nonneg hC_Lp_nn (mul_nonneg (Nat.cast_nonneg _) hC_grad_nn), ?_⟩
  intro u hu
  rw [Sobolev.Euclidean.wkpNorm_eq_sum]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  have : Unique (Fin 0 → Fin (Module.finrank ℝ E)) :=
    { default := fun i : Fin 0 => i.elim0
      uniq := fun β => by funext j; exact j.elim0 }
  rw [Fintype.sum_unique]
  rw [Sobolev.Euclidean.iterWeakPartial_zero]
  have h_j1_eq : (∑ β : Fin 1 → Fin (Module.finrank ℝ E),
      eLpNorm
        (Sobolev.Euclidean.iterWeakPartial
          (d := Module.finrank ℝ E) p 1 β
          (Sobolev.Chart.chartPushed
            (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
          (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α))
        p
        ((volume : Measure EuclN_E).restrict
          (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α))) =
      ∑ i : Fin (Module.finrank ℝ E),
        eLpNorm
          (Sobolev.Euclidean.chosenWeakPartialOrZero
            (d := Module.finrank ℝ E) p i
            (Sobolev.Chart.chartPushed
              (I := I) (M := M)
              (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
            (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α))
          p
          ((volume : Measure EuclN_E).restrict
            (Sobolev.Chart.chartTargetEuclid (I := I) (M := M)
              α)) := by
    have h_unfold : ∀ β : Fin 1 → Fin (Module.finrank ℝ E),
        Sobolev.Euclidean.iterWeakPartial
            (d := Module.finrank ℝ E) p 1 β
            (Sobolev.Chart.chartPushed
              (I := I) (M := M)
              (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
            (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α) =
          Sobolev.Euclidean.chosenWeakPartialOrZero
            (d := Module.finrank ℝ E) p (β 0)
            (Sobolev.Chart.chartPushed
              (I := I) (M := M)
              (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
            (Sobolev.Chart.chartTargetEuclid (I := I) (M := M)
              α) := by
      intro β
      rw [Sobolev.Euclidean.iterWeakPartial_succ]
      simp [Sobolev.Euclidean.iterWeakPartial_zero]
    rw [Finset.sum_congr rfl (fun β _ => congrArg (fun ψ : EuclN_E → ℝ =>
      eLpNorm ψ p
        ((volume : Measure EuclN_E).restrict
          (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)))
      (h_unfold β))]
    exact sum_Fin1_eq_sum_Fin (Module.finrank ℝ E) (fun i =>
      eLpNorm
        (Sobolev.Euclidean.chosenWeakPartialOrZero
          (d := Module.finrank ℝ E) p i
          (Sobolev.Chart.chartPushed
            (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
          (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α))
        p
        ((volume : Measure EuclN_E).restrict
          (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)))
  rw [h_j1_eq]
  have h_Lp := hC_Lp_bound (u := u) hu
  have h_Lp_step :
      eLpNorm (Sobolev.Chart.chartPushed
          (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u) p
          ((volume : Measure EuclN_E).restrict
            (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)) ≤
        ENNReal.ofReal C_Lp *
          (eLpNorm u p
              (CalabiYau.RiemannianVolume.riemannianVolumeMeasure I M g) +
            eLpNorm (fun x : M => Real.sqrt
                (g.inner x
                  (CalabiYau.Riemannian.gradFun (I := I) g u x)
                  (CalabiYau.Riemannian.gradFun (I := I) g u x))) p
              (CalabiYau.RiemannianVolume.riemannianVolumeMeasure I M g)) := by
    refine h_Lp.trans ?_; gcongr; exact le_self_add
  have h_chosenWP_eq : ∀ i : Fin (Module.finrank ℝ E),
      eLpNorm
        (Sobolev.Euclidean.chosenWeakPartialOrZero
          (d := Module.finrank ℝ E) p i
          (Sobolev.Chart.chartPushed
            (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
          (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α))
        p
        ((volume : Measure EuclN_E).restrict
          (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)) =
      eLpNorm
        (fun y : EuclN_E => fderiv ℝ
          (Sobolev.Chart.chartSmoothExt
            (I := I) (M := M) α
            (fun z : M => ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z)) y
            (EuclideanSpace.single i (1 : ℝ)))
        p
        ((volume : Measure EuclN_E).restrict
          (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)) :=
    fun i => eLpNorm_congr_ae
      (chosenWeakPartial_chartPushed_ae_eq_fderiv (I := I) (M := M) α hp_one hu i)
  rw [Finset.sum_congr rfl (fun i _ => h_chosenWP_eq i)]
  have h_grad_each : ∀ i : Fin (Module.finrank ℝ E),
      eLpNorm
        (fun y : EuclN_E => fderiv ℝ
          (Sobolev.Chart.chartSmoothExt
            (I := I) (M := M) α
            (fun z : M => ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z)) y
            (EuclideanSpace.single i (1 : ℝ)))
        p
        ((volume : Measure EuclN_E).restrict
          (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)) ≤
      ENNReal.ofReal C_grad *
        (eLpNorm u p
            (CalabiYau.RiemannianVolume.riemannianVolumeMeasure I M g) +
          eLpNorm (fun x : M => Real.sqrt
              (g.inner x
                (CalabiYau.Riemannian.gradFun (I := I) g u x)
                (CalabiYau.Riemannian.gradFun (I := I) g u x))) p
            (CalabiYau.RiemannianVolume.riemannianVolumeMeasure I M g)) :=
    fun i => hC_grad_bound (u := u) hu i
  have h_grad_sum_le := Finset.sum_le_sum
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E)))) => h_grad_each i)
  have h_const_sum :
      (∑ _ : Fin (Module.finrank ℝ E), ENNReal.ofReal C_grad *
        (eLpNorm u p
            (CalabiYau.RiemannianVolume.riemannianVolumeMeasure I M g) +
          eLpNorm (fun x : M => Real.sqrt
              (g.inner x
                (CalabiYau.Riemannian.gradFun (I := I) g u x)
                (CalabiYau.Riemannian.gradFun (I := I) g u x))) p
            (CalabiYau.RiemannianVolume.riemannianVolumeMeasure I M g))) =
      ENNReal.ofReal ((Module.finrank ℝ E : ℝ) * C_grad) *
        (eLpNorm u p
            (CalabiYau.RiemannianVolume.riemannianVolumeMeasure I M g) +
          eLpNorm (fun x : M => Real.sqrt
              (g.inner x
                (CalabiYau.Riemannian.gradFun (I := I) g u x)
                (CalabiYau.Riemannian.gradFun (I := I) g u x))) p
            (CalabiYau.RiemannianVolume.riemannianVolumeMeasure I M g)) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [nsmul_eq_mul, ← mul_assoc]
    congr 1
    rw [show ((Module.finrank ℝ E : ℕ) : ℝ≥0∞) = ENNReal.ofReal (Module.finrank ℝ E : ℝ) from by
      rw [ENNReal.ofReal_natCast]]
    rw [← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  have h_grad_total :
      (∑ i : Fin (Module.finrank ℝ E),
        eLpNorm
          (fun y : EuclN_E => fderiv ℝ
            (Sobolev.Chart.chartSmoothExt
              (I := I) (M := M) α
              (fun z : M => ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
                : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z)) y
              (EuclideanSpace.single i (1 : ℝ)))
          p
          ((volume : Measure EuclN_E).restrict
            (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α))) ≤
      ENNReal.ofReal ((Module.finrank ℝ E : ℝ) * C_grad) *
        (eLpNorm u p
            (CalabiYau.RiemannianVolume.riemannianVolumeMeasure I M g) +
          eLpNorm (fun x : M => Real.sqrt
              (g.inner x
                (CalabiYau.Riemannian.gradFun (I := I) g u x)
                (CalabiYau.Riemannian.gradFun (I := I) g u x))) p
            (CalabiYau.RiemannianVolume.riemannianVolumeMeasure I M g)) := by
    refine h_grad_sum_le.trans ?_
    rw [h_const_sum]
  refine (add_le_add h_Lp_step h_grad_total).trans ?_
  rw [← add_mul]
  gcongr
  rw [ENNReal.ofReal_add hC_Lp_nn (mul_nonneg (Nat.cast_nonneg _) hC_grad_nn)]

private lemma chartPushed_eq_zero_of_pou_zero
    [T2Space M] [SigmaCompactSpace M] (α : M) (u : M → ℝ)
    (h_pou_zero : ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) = (fun _ : M => (0 : ℝ))) :
    Sobolev.Chart.chartPushed
        (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u =
      (fun _ : EuclN_E => (0 : ℝ)) := by
  funext y
  simp only [Sobolev.Chart.chartPushed]
  rw [show ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) = 0 from by rw [h_pou_zero]]
  simp

theorem wkpNormChart_le_const_mul_intrinsicLpComponents_smooth_uniform
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : CalabiYau.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
        wkpNormChart (I := I) (M := M) 1 p u ≤
          ENNReal.ofReal C *
            (eLpNorm u p
                (CalabiYau.RiemannianVolume.riemannianVolumeMeasure I M g) +
              eLpNorm (fun x : M => Real.sqrt
                  (g.inner x
                    (CalabiYau.Riemannian.gradFun
                      (I := I) g u x)
                    (CalabiYau.Riemannian.gradFun
                      (I := I) g u x))) p
                (CalabiYau.RiemannianVolume.riemannianVolumeMeasure I M g)) := by
  classical
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  let : MeasurableSpace M := borel M
  have : BorelSpace M := ⟨rfl⟩
  set S : Finset M :=
    CalabiYau.RiemannianVolume.chartAtlasPOUFinset (I := I) (M := M)
  set Cα : M → ℝ := fun α => Classical.choose
    (wkpNorm_chartPushed_le_const_mul_per_α (I := I) (M := M) g α hp_one hp_top)
  have hCα_nn : ∀ α : M, 0 ≤ Cα α :=
    fun α => (Classical.choose_spec
      (wkpNorm_chartPushed_le_const_mul_per_α (I := I) (M := M) g α hp_one hp_top)).1
  refine ⟨∑ α ∈ S, Cα α, Finset.sum_nonneg (fun α _ => hCα_nn α), ?_⟩
  intro u hu
  have h_def : wkpNormChart (I := I) (M := M) 1 p u =
      ∑' α : M,
        Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 p
          (Sobolev.Chart.chartPushed
            (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α) := rfl
  rw [h_def]
  have h_outside_zero : ∀ α : M, α ∉ S →
      Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 p
        (Sobolev.Chart.chartPushed
          (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) = 0 := by
    intro α hα
    have h_support_empty : Function.support
        ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) = ∅ := by
      have h := (CalabiYau.RiemannianVolume.chartAtlasPOU_finset_mem
        (I := I) (M := M) (α := α)).not.mp hα
      rw [Set.not_nonempty_iff_eq_empty] at h
      exact h
    have hρ_zero : ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) = (fun _ : M => (0 : ℝ)) := by
      funext y
      have hy_notSupport : y ∉ Function.support
          ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by rw [h_support_empty]; simp
      exact Function.notMem_support.mp hy_notSupport
    have h_chartPushed_zero := chartPushed_eq_zero_of_pou_zero (I := I) (M := M) α u hρ_zero
    rw [h_chartPushed_zero]
    exact Sobolev.Euclidean.wkpNorm_zero_fun_zero
      (d := Module.finrank ℝ E) hp_one
      (Sobolev.Chart.chartTargetEuclid_isOpen
        (I := I) (M := M) α)
  rw [tsum_eq_sum (s := S) h_outside_zero]
  have h_per_α : ∀ α ∈ S,
      Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 p
        (Sobolev.Chart.chartPushed
          (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) ≤
      ENNReal.ofReal (Cα α) *
        (eLpNorm u p
            (CalabiYau.RiemannianVolume.riemannianVolumeMeasure I M g) +
          eLpNorm (fun x : M => Real.sqrt
              (g.inner x
                (CalabiYau.Riemannian.gradFun (I := I) g u x)
                (CalabiYau.Riemannian.gradFun (I := I) g u x))) p
            (CalabiYau.RiemannianVolume.riemannianVolumeMeasure I M g)) :=
    fun α _ => (Classical.choose_spec
      (wkpNorm_chartPushed_le_const_mul_per_α (I := I) (M := M) g α hp_one hp_top)).2 hu
  refine (Finset.sum_le_sum h_per_α).trans ?_
  rw [← Finset.sum_mul]
  gcongr
  rw [show (∑ α ∈ S, ENNReal.ofReal (Cα α)) = ENNReal.ofReal (∑ α ∈ S, Cα α) from
    (ENNReal.ofReal_sum_of_nonneg (fun α _ => hCα_nn α)).symm]

end EquivalenceReverse
end Sobolev
