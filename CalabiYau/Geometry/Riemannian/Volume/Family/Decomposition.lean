-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Integration/Measure/Family/Decomposition.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Riemannian.Volume.Family.Defs
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Topology.Compactness.LocallyFinite

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open Bundle Manifold Set MeasureTheory Matrix
open scoped Manifold Topology ContDiff ENNReal Matrix BigOperators

namespace CalabiYau.RiemannianVolume

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem integral_chart_ae
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (h : M → ℝ)
    (hh_meas : AEStronglyMeasurable h (chartLocalMeasure (I := I) g x₀)) :
    ∫ x, h x ∂(chartLocalMeasure (I := I) g x₀)
      = ∫ y in (extChartAt I x₀).target,
          chartDensity g x₀ ((extChartAt I x₀).symm y) *
            h ((extChartAt I x₀).symm y)
          ∂(modelHaar (E := E)) := by
  have htarget_meas : MeasurableSet (extChartAt I x₀).target :=
    measurableSet_extChartAt_target (I := I) x₀
  set μ₀ : MeasureTheory.Measure E :=
    (modelHaar (E := E)).restrict (extChartAt I x₀).target with hμ₀
  set w : E → ℝ≥0∞ :=
    fun y => ENNReal.ofReal
      (chartDensity g x₀ ((extChartAt I x₀).symm y)) with hw
  set μ₁ : MeasureTheory.Measure E := μ₀.withDensity w with hμ₁
  have h_unfold :
      chartLocalMeasure (I := I) g x₀ =
        MeasureTheory.Measure.map (extChartAt I x₀).symm μ₁ := rfl
  have hh_map : AEStronglyMeasurable h
      (MeasureTheory.Measure.map (extChartAt I x₀).symm μ₁) := by
    rw [← h_unfold]
    exact hh_meas
  rw [h_unfold]
  have haem_symm : AEMeasurable ((extChartAt I x₀).symm) μ₁ := by
    have haem_base : AEMeasurable ((extChartAt I x₀).symm) μ₀ :=
      aemeasurable_extChartAt_symm_restrict_target (I := I) (E := E) x₀
    have hac : μ₁ ≪ μ₀ := by
      simpa [hμ₁] using MeasureTheory.withDensity_absolutelyContinuous (μ := μ₀) w
    exact haem_base.mono_ac hac
  have h_integral_map :
      ∫ x, h x ∂(MeasureTheory.Measure.map (extChartAt I x₀).symm μ₁)
        = ∫ y, h ((extChartAt I x₀).symm y) ∂μ₁ := by
    exact MeasureTheory.integral_map haem_symm hh_map
  rw [h_integral_map]
  have hwd_aem : AEMeasurable w μ₀ :=
    aemeasurable_chartDensity_symm_pullback (I := I) g x₀
  have hw_lt_top : ∀ᵐ y ∂μ₀, w y < (⊤ : ℝ≥0∞) := by
    refine Filter.Eventually.of_forall (fun y => ?_)
    simp [hw]
  have h_withDensity :
      ∫ y, h ((extChartAt I x₀).symm y) ∂μ₁
        = ∫ y, (w y).toReal • h ((extChartAt I x₀).symm y) ∂μ₀ := by
    simpa [hμ₁] using
      integral_withDensity_eq_integral_toReal_smul₀ (μ := μ₀)
        (f := w) hwd_aem hw_lt_top
        (g := fun y : E => h ((extChartAt I x₀).symm y))
  rw [h_withDensity]
  have hw_toReal : ∀ y ∈ (extChartAt I x₀).target,
      (w y).toReal = chartDensity g x₀ ((extChartAt I x₀).symm y) := by
    intro y hy
    have hsource : (extChartAt I x₀).symm y ∈ (chartAt H x₀).source := by
      have := (extChartAt I x₀).map_target hy
      rw [extChartAt_source_eq_chartAt_source (I := I)] at this
      exact this
    have hbase : (extChartAt I x₀).symm y ∈
        (trivializationAt E (TangentSpace I) x₀).baseSet := hsource
    have hpos : 0 < chartDensity g x₀ ((extChartAt I x₀).symm y) :=
      chartDensity_pos (I := I) g x₀ hbase
    change (ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y))).toReal
        = chartDensity g x₀ ((extChartAt I x₀).symm y)
    exact ENNReal.toReal_ofReal hpos.le
  have h_restrict :
      ∫ y, (w y).toReal • h ((extChartAt I x₀).symm y) ∂μ₀
        = ∫ y in (extChartAt I x₀).target,
            (w y).toReal • h ((extChartAt I x₀).symm y)
          ∂(modelHaar (E := E)) := by
    simp [hμ₀]
  rw [h_restrict]
  refine setIntegral_congr_fun htarget_meas (fun y hy => ?_)
  rw [hw_toReal y hy, smul_eq_mul]

theorem integral_chartLocalMeasure
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (h : M → ℝ) (hh_meas : Measurable h) :
    ∫ x, h x ∂(chartLocalMeasure (I := I) g x₀)
      = ∫ y in (extChartAt I x₀).target,
          chartDensity g x₀ ((extChartAt I x₀).symm y) *
            h ((extChartAt I x₀).symm y)
          ∂(modelHaar (E := E)) :=
  integral_chart_ae (I := I) g x₀ h hh_meas.aestronglyMeasurable

theorem ae_chart_of_haar
    (g : SmoothRiemannianMetric I M) (α : M)
    {P : E → Prop} (hP : MeasurableSet {y | P y})
    (h : ∀ᵐ y ∂(modelHaar (E := E)), P y) :
    ∀ᵐ x ∂(chartLocalMeasure (I := I) g α),
      x ∈ (chartAt H α).source → P (extChartAt I α x) := by
  classical
  let dens : E → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (chartDensity g α ((extChartAt I α).symm y))
  let μT : Measure E :=
    (modelHaar (E := E)).restrict (extChartAt I α).target
  let μD : Measure E := μT.withDensity dens
  have hrestrict : ∀ᵐ y ∂μT, P y :=
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).ae_le h
  have hdens : ∀ᵐ y ∂μD, P y :=
    (withDensity_absolutelyContinuous μT dens).ae_le hrestrict
  have htarget : ∀ᵐ y ∂μD, y ∈ (extChartAt I α).target := by
    exact (withDensity_absolutelyContinuous μT dens).ae_le
      (ae_restrict_mem (measurableSet_extChartAt_target (I := I) α))
  let coord : M → E := fun x =>
    if x ∈ (chartAt H α).source then extChartAt I α x else 0
  have hcoord : Measurable coord := by
    have hsource : MeasurableSet (chartAt H α).source :=
      (chartAt H α).open_source.measurableSet
    have hext : ContinuousOn (fun x : M => extChartAt I α x)
        (chartAt H α).source := by
      have hsource_eq : (chartAt H α).source = (extChartAt I α).source :=
        (extChartAt_source_eq_chartAt_source (I := I) (M := M) α).symm
      rw [hsource_eq]
      exact continuousOn_extChartAt α
    have hcoord_eq : coord = (chartAt H α).source.piecewise
        (fun x : M => extChartAt I α x) (fun _ => 0) := by
      funext x
      simp only [coord, Set.piecewise]
    rw [hcoord_eq]
    exact ContinuousOn.measurable_piecewise hext continuousOn_const hsource
  have hsymm : AEMeasurable (extChartAt I α).symm μD :=
    (aemeasurable_extChartAt_symm_restrict_target (I := I) (E := E) α).mono_ac
      (withDensity_absolutelyContinuous μT dens)
  have hpush : ∀ᵐ x ∂Measure.map (extChartAt I α).symm μD, P (coord x) := by
    refine (ae_map_iff hsymm (hP.preimage hcoord)).2 ?_
    filter_upwards [hdens, htarget] with y hy hy_target
    have hy_source : (extChartAt I α).symm y ∈ (chartAt H α).source := by
      have hmem : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
        (extChartAt I α).map_target hy_target
      rwa [extChartAt_source_eq_chartAt_source (I := I) (M := M)] at hmem
    simpa only [coord, if_pos hy_source, (extChartAt I α).right_inv hy_target] using hy
  have hchart : ∀ᵐ x ∂(chartLocalMeasure (I := I) g α), P (coord x) := by
    simpa only [chartLocalMeasure, μD, μT, dens] using hpush
  filter_upwards [hchart] with x hx hx_source
  simpa only [coord, if_pos hx_source] using hx

lemma chartAtlasPOU_finite_support
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] :
    {α : M | (Function.support ((chartAtlasPOU I M) α)).Nonempty}.Finite :=
  LocallyFinite.finite_nonempty_of_compact
    (chartAtlasPOU I M).locallyFinite

noncomputable def chartAtlasPOUFinset
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] : Finset M :=
  (chartAtlasPOU_finite_support (I := I) (M := M)).toFinset

lemma chartAtlasPOU_finset_mem
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] {α : M} :
    α ∈ chartAtlasPOUFinset (I := I) (M := M) ↔
      (Function.support ((chartAtlasPOU I M) α)).Nonempty := by
  unfold chartAtlasPOUFinset
  rw [Set.Finite.mem_toFinset]
  rfl

lemma chartAtlasPOU_weight_zero_of_notMem
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {α : M} (hα : α ∉ chartAtlasPOUFinset (I := I) (M := M)) (x : M) :
    (chartAtlasPOU I M) α x = 0 := by
  rw [chartAtlasPOU_finset_mem] at hα
  rw [Set.not_nonempty_iff_eq_empty] at hα
  by_contra hne
  have hx : x ∈ Function.support ((chartAtlasPOU I M) α) := hne
  rw [hα] at hx
  exact (Set.notMem_empty _) hx

lemma chartAtlasPOU_withDensity_zero_of_notMem
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {α : M} (hα : α ∉ chartAtlasPOUFinset (I := I) (M := M)) :
    (chartLocalMeasure (I := I) g α).withDensity
        (fun x : M => ENNReal.ofReal ((chartAtlasPOU I M) α x)) = 0 := by
  have hzero : (fun x : M => ENNReal.ofReal ((chartAtlasPOU I M) α x)) = 0 := by
    funext x
    rw [chartAtlasPOU_weight_zero_of_notMem (I := I) (M := M) hα x]
    simp
  rw [hzero, MeasureTheory.withDensity_zero]

theorem hasDerivAt_setIntegral_model
    (target : Set E)
    {F : ℝ → E → ℝ} (F' : ℝ → E → ℝ) {b : E → ℝ}
    (t₀ : ℝ) {s : Set ℝ} (hs : s ∈ 𝓝 t₀)
    (hF_meas : ∀ᶠ t in 𝓝 t₀,
      AEStronglyMeasurable (F t) ((modelHaar (E := E)).restrict target))
    (hF_int : Integrable (F t₀) ((modelHaar (E := E)).restrict target))
    (hF'_meas : AEStronglyMeasurable (F' t₀)
      ((modelHaar (E := E)).restrict target))
    (h_bound : ∀ᵐ y ∂((modelHaar (E := E)).restrict target),
      ∀ t ∈ s, ‖F' t y‖ ≤ b y)
    (h_bound_int : Integrable b ((modelHaar (E := E)).restrict target))
    (h_diff : ∀ᵐ y ∂((modelHaar (E := E)).restrict target),
      ∀ t ∈ s, HasDerivAt (fun r => F r y) (F' t y) t) :
    Integrable (F' t₀) ((modelHaar (E := E)).restrict target) ∧
      HasDerivAt (fun t => ∫ y in target, F t y ∂(modelHaar (E := E)))
        (∫ y in target, F' t₀ y ∂(modelHaar (E := E))) t₀ := by
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (α := E) (E := ℝ) (μ := (modelHaar (E := E)).restrict target)
    (F := F) (F' := F') (x₀ := t₀) (s := s) (bound := b)
    hs hF_meas hF_int hF'_meas h_bound h_bound_int h_diff
  refine ⟨this.1, ?_⟩
  have hfun : (fun t => ∫ y, F t y ∂((modelHaar (E := E)).restrict target))
      = fun t => ∫ y in target, F t y ∂(modelHaar (E := E)) := by
    funext t
    rfl
  have hfun' : (∫ y, F' t₀ y ∂((modelHaar (E := E)).restrict target))
      = ∫ y in target, F' t₀ y ∂(modelHaar (E := E)) := rfl
  rw [← hfun, ← hfun']
  exact this.2

lemma hasDerivAt_chartGramMatrix_entry
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t₀ : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t₀)
    (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (i j : Fin (Module.finrank ℝ E)) (t : ℝ) :
    HasDerivAt (fun s => CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) x₀ x i j)
      (deriv (fun s => CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) x₀ x i j) t) t :=
  hreg.hasDerivAt_chartGramMatrix x₀ i j hx t

section ChartInvarianceOfTraceTimeDeriv

lemma deriv_chartGramMatrix_pullback
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t)
    (x₀ x₁ : M) {x : M}
    (hx0 : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hx1 : x ∈ (trivializationAt E (TangentSpace I) x₁).baseSet) :
    (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
        deriv (fun s => CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) x₁ x i j) t)
      = (transitionMatrix (I := I) x₀ x₁ x)ᵀ *
          (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
            deriv (fun s => CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) x₀ x i j) t) *
          transitionMatrix (I := I) x₀ x₁ x := by
  classical
  set n := Fin (Module.finrank ℝ E) with hn_def
  set J : Matrix n n ℝ := transitionMatrix (I := I) x₀ x₁ x with hJ_def
  have hentry : ∀ (t₀ : ℝ) (i j : n),
      CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam t₀) x₁ x i j
        = ∑ k, ∑ l, J k i * J l j *
            CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam t₀) x₀ x k l := by
    intro t₀ i j
    exact chartGramMatrix_pullback_eq_sum (I := I) (g_fam t₀) x₀ x₁ hx0 hx1 i j
  ext i j
  have hG0_entry : ∀ k l : n,
      HasDerivAt (fun s => CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) x₀ x k l)
        (deriv (fun s => CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) x₀ x k l) t) t := by
    intro k l
    exact hasDerivAt_chartGramMatrix_entry (I := I) (M := M) hreg x₀ hx0 k l t
  have hsum_hasDeriv :
      HasDerivAt
        (fun s => ∑ k : n, ∑ l : n, J k i * J l j *
            CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) x₀ x k l)
        (∑ k : n, ∑ l : n, J k i * J l j *
            deriv (fun s => CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) x₀ x k l) t) t := by
    refine HasDerivAt.fun_sum (fun k _ => ?_)
    refine HasDerivAt.fun_sum (fun l _ => ?_)
    have hcm := (hG0_entry k l).const_mul (J k i * J l j)
    exact hcm
  have hfun_eq :
      (fun s => CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) x₁ x i j)
        = (fun s => ∑ k : n, ∑ l : n, J k i * J l j *
            CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) x₀ x k l) := by
    funext s
    exact hentry s i j
  have hderiv_eq :
      deriv (fun s => CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) x₁ x i j) t
        = ∑ k : n, ∑ l : n, J k i * J l j *
            deriv (fun s => CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) x₀ x k l) t := by
    rw [hfun_eq]
    exact hsum_hasDeriv.deriv
  change deriv (fun s => CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) x₁ x i j) t
      = (Jᵀ *
          (Matrix.of fun i j : n =>
            deriv (fun s => CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) x₀ x i j) t) *
          J) i j
  rw [hderiv_eq]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  ring

lemma transitionMatrix_mul_reverse
    (x₀ x₁ : M) {x : M}
    (hx0 : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hx1 : x ∈ (trivializationAt E (TangentSpace I) x₁).baseSet) :
    transitionMatrix (I := I) x₀ x₁ x * transitionMatrix (I := I) x₁ x₀ x = 1 := by
  classical
  ext i j
  have hx0' : x ∈ (extChartAt I x₀).source := by
    rw [extChartAt_source]
    exact hx0
  have hx1' : x ∈ (extChartAt I x₁).source := by
    rw [extChartAt_source]
    exact hx1
  have hmem : x ∈ (extChartAt I x₀).source ∩ (extChartAt I x₁).source ∩
      (extChartAt I x₀).source := ⟨⟨hx0', hx1'⟩, hx0'⟩
  have hcomp : ∀ i : Fin (Module.finrank ℝ E),
      (tangentCoordChange I x₁ x₀ x) ((tangentCoordChange I x₀ x₁ x)
          ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i))
        = (CalabiYau.Tensor.Coordinates.chartModelBasis E) i := by
    intro i
    have := tangentCoordChange_comp (I := I) (𝕜 := ℝ) (E := E) (H := H) (M := M)
        (w := x₀) (x := x₁) (y := x₀) (z := x)
        (v := (CalabiYau.Tensor.Coordinates.chartModelBasis E) i) hmem
    rw [this]
    have hself := tangentCoordChange_self (I := I) (x := x₀) (z := x)
      (v := (CalabiYau.Tensor.Coordinates.chartModelBasis E) i) hx0'
    exact hself
  change (transitionMatrix (I := I) x₀ x₁ x *
      transitionMatrix (I := I) x₁ x₀ x) i j = (1 : Matrix _ _ _) i j
  simp only [Matrix.mul_apply, transitionMatrix_apply, Matrix.one_apply]
  have hexp :
      (tangentCoordChange I x₀ x₁ x) ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j)
        = ∑ k, (CalabiYau.Tensor.Coordinates.chartModelBasis E).repr
            ((tangentCoordChange I x₀ x₁ x) ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j)) k
          • (CalabiYau.Tensor.Coordinates.chartModelBasis E) k :=
    chartModelBasis_repr_sum (tangentCoordChange I x₀ x₁ x) j
  have hlin :
      (tangentCoordChange I x₁ x₀ x)
          (∑ k, (CalabiYau.Tensor.Coordinates.chartModelBasis E).repr
              ((tangentCoordChange I x₀ x₁ x) ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j)) k
            • (CalabiYau.Tensor.Coordinates.chartModelBasis E) k)
        = ∑ k, (CalabiYau.Tensor.Coordinates.chartModelBasis E).repr
              ((tangentCoordChange I x₀ x₁ x) ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j)) k
            • (tangentCoordChange I x₁ x₀ x) ((CalabiYau.Tensor.Coordinates.chartModelBasis E) k) := by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [ContinuousLinearMap.map_smul]
  have heval : (tangentCoordChange I x₁ x₀ x) ((tangentCoordChange I x₀ x₁ x)
      ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j))
      = (CalabiYau.Tensor.Coordinates.chartModelBasis E) j := hcomp j
  have heval' :
      ∑ k, (CalabiYau.Tensor.Coordinates.chartModelBasis E).repr
            ((tangentCoordChange I x₀ x₁ x) ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j)) k
          • (tangentCoordChange I x₁ x₀ x) ((CalabiYau.Tensor.Coordinates.chartModelBasis E) k)
        = (CalabiYau.Tensor.Coordinates.chartModelBasis E) j := by
    rw [← hlin, ← hexp]; exact heval
  have happ := congrArg ((CalabiYau.Tensor.Coordinates.chartModelBasis E).repr · i) heval'
  simp only [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply,
    map_smul, Finsupp.smul_apply, smul_eq_mul] at happ
  have hrhs : ((CalabiYau.Tensor.Coordinates.chartModelBasis E).repr ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j)) i
                = if i = j then (1 : ℝ) else 0 := by
    rw [(CalabiYau.Tensor.Coordinates.chartModelBasis E).repr_self, Finsupp.single_apply]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  rw [← hrhs]
  rw [← happ]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  exact mul_comm _ _

lemma transitionMatrix_isUnit
    (x₀ x₁ : M) {x : M}
    (hx0 : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hx1 : x ∈ (trivializationAt E (TangentSpace I) x₁).baseSet) :
    IsUnit (transitionMatrix (I := I) x₀ x₁ x) := by
  have hleft : transitionMatrix (I := I) x₁ x₀ x *
      transitionMatrix (I := I) x₀ x₁ x = 1 :=
    transitionMatrix_mul_reverse (I := I) x₁ x₀ hx1 hx0
  have hdet : (transitionMatrix (I := I) x₀ x₁ x).det *
      (transitionMatrix (I := I) x₁ x₀ x).det = 1 := by
    rw [mul_comm, ← Matrix.det_mul, hleft, Matrix.det_one]
  exact (Matrix.isUnit_iff_isUnit_det _).mpr
    (IsUnit.of_mul_eq_one _ hdet)

lemma trace_chartGramMatrix_inv_deriv_chart_independent
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t)
    (x₀ x₁ : M) {x : M}
    (hx0 : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hx1 : x ∈ (trivializationAt E (TangentSpace I) x₁).baseSet) :
    Matrix.trace ((CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam t) x₀ x)⁻¹ *
      (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
        deriv (fun s => CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) x₀ x i j) t))
    = Matrix.trace ((CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam t) x₁ x)⁻¹ *
      (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
        deriv (fun s => CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) x₁ x i j) t)) := by
  classical
  set n := Fin (Module.finrank ℝ E) with hn_def
  set J : Matrix n n ℝ := transitionMatrix (I := I) x₀ x₁ x with hJ_def
  set G₀ : Matrix n n ℝ := CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam t) x₀ x with hG0_def
  set G₁ : Matrix n n ℝ := CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam t) x₁ x with hG1_def
  set dG₀ : Matrix n n ℝ := Matrix.of fun i j : n =>
      deriv (fun s => CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) x₀ x i j) t with hdG0_def
  set dG₁ : Matrix n n ℝ := Matrix.of fun i j : n =>
      deriv (fun s => CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) x₁ x i j) t with hdG1_def
  have hG1_eq : G₁ = Jᵀ * G₀ * J :=
    chartGramMatrix_pullback_eq_mul (I := I) (g_fam t) x₀ x₁ hx0 hx1
  have hdG1_eq : dG₁ = Jᵀ * dG₀ * J :=
    deriv_chartGramMatrix_pullback (I := I) (M := M) hreg x₀ x₁ hx0 hx1
  have hJ_unit : IsUnit J :=
    transitionMatrix_isUnit (I := I) x₀ x₁ hx0 hx1
  have hG0_unit : IsUnit G₀ := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have hpos : 0 < G₀.det := CalabiYau.Tensor.Coordinates.chartGramMatrix_det_pos (I := I) (g_fam t) x₀ hx0
    exact (ne_of_gt hpos).isUnit
  have hJT_unit : IsUnit Jᵀ := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det _).mp hJ_unit
  have hJ_det : IsUnit J.det := (Matrix.isUnit_iff_isUnit_det _).mp hJ_unit
  have hJT_det : IsUnit (Jᵀ).det := by
    rw [Matrix.det_transpose]; exact hJ_det
  have hinv : G₁⁻¹ = J⁻¹ * G₀⁻¹ * (Jᵀ)⁻¹ := by
    rw [hG1_eq]
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
    simp only [Matrix.mul_assoc]
  have hJTinv : (Jᵀ)⁻¹ * Jᵀ = 1 := Matrix.nonsing_inv_mul _ hJT_det
  have hJinvJ : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv _ hJ_det
  have hgoal :
      Matrix.trace (G₁⁻¹ * dG₁) = Matrix.trace (G₀⁻¹ * dG₀) := by
    rw [hinv, hdG1_eq]
    have hrw1 :
        (J⁻¹ * G₀⁻¹ * (Jᵀ)⁻¹) * (Jᵀ * dG₀ * J)
          = J⁻¹ * G₀⁻¹ * ((Jᵀ)⁻¹ * Jᵀ) * dG₀ * J := by
      simp only [Matrix.mul_assoc]
    rw [hrw1]
    rw [hJTinv]
    rw [Matrix.mul_one]
    rw [show J⁻¹ * G₀⁻¹ * dG₀ * J = (J⁻¹ * G₀⁻¹ * dG₀) * J from by
      simp only [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm]
    rw [show J * (J⁻¹ * G₀⁻¹ * dG₀) = (J * J⁻¹) * G₀⁻¹ * dG₀ from by
      simp only [← Matrix.mul_assoc]]
    rw [hJinvJ]
    rw [Matrix.one_mul]
  linarith [hgoal]

end ChartInvarianceOfTraceTimeDeriv

lemma traceTimeDerivMetric_eq_trace_chartGramMatrix
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t)
    (α : M) {x : M}
    (hxα : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    traceTimeDerivMetric (I := I) g_fam t x
    = Matrix.trace ((CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam t) α x)⁻¹ *
      (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
        deriv (fun s => CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) α x i j) t)) := by
  have hxx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    change x ∈ (chartAt H x).source
    exact mem_chart_source _ _
  rw [traceTimeDerivMetric_eq]
  exact trace_chartGramMatrix_inv_deriv_chart_independent
    (I := I) (M := M) hreg x α hxx hxα

theorem riemannianVolumeMeasure_eq_finset_sum
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) :
    riemannianVolumeMeasure (I := I) (M := M) g =
      ∑ α ∈ chartAtlasPOUFinset (I := I) (M := M),
        (chartLocalMeasure (I := I) g α).withDensity
          (fun x : M => ENNReal.ofReal ((chartAtlasPOU I M) α x)) := by
  rw [riemannianVolumeMeasure_def, riemannianMeasure_def]
  set S : Finset M := chartAtlasPOUFinset (I := I) (M := M) with hS
  set f : M → MeasureTheory.Measure M := fun α =>
      (chartLocalMeasure (I := I) g α).withDensity
        (fun x : M => ENNReal.ofReal ((chartAtlasPOU I M) α x)) with hf
  have hsplit : ((MeasureTheory.Measure.sum fun i : (S : Set M) => f i) +
      MeasureTheory.Measure.sum (fun i : ↥((S : Set M)ᶜ) => f i)) =
      MeasureTheory.Measure.sum f :=
    MeasureTheory.Measure.sum_add_sum_compl (S : Set M) f
  have hcompl : MeasureTheory.Measure.sum (fun i : ↥((S : Set M)ᶜ) => f i) = 0 := by
    have hzero : ∀ i : ↥((S : Set M)ᶜ), f i = 0 := by
      intro i
      have hi : (i : M) ∉ S := i.2
      exact chartAtlasPOU_withDensity_zero_of_notMem (I := I) (M := M) g hi
    ext t ht
    rw [MeasureTheory.Measure.sum_apply _ ht]
    simp [hzero]
  rw [← hsplit, hcompl, add_zero]
  exact MeasureTheory.Measure.sum_coe_finset S f

theorem integral_riemannianVolumeMeasure_eq_finset_sum
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (h : M → ℝ)
    (hh_cont : Continuous h) :
    ∫ x, h x ∂(riemannianVolumeMeasure (I := I) (M := M) g)
      = ∑ α ∈ chartAtlasPOUFinset (I := I) (M := M),
          ∫ x, h x
            ∂((chartLocalMeasure (I := I) g α).withDensity
              (fun y : M => ENNReal.ofReal ((chartAtlasPOU I M) α y))) := by
  classical
  have hVol_eq :=
    riemannianVolumeMeasure_eq_finset_sum (I := I) (M := M) g
  have hFin :
      MeasureTheory.IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, ‖h x‖ ≤ C := by
    have hCpt := (isCompact_univ (X := M)).image hh_cont.norm
    obtain ⟨C, hCmem⟩ := hCpt.bddAbove
    refine ⟨C, fun x => hCmem ⟨x, Set.mem_univ _, rfl⟩⟩
  have hh_int : Integrable h (riemannianVolumeMeasure (I := I) (M := M) g) :=
    (integrable_const C).mono' hh_cont.aestronglyMeasurable
      (Filter.Eventually.of_forall hC)
  have hsummand_int : ∀ α ∈ chartAtlasPOUFinset (I := I) (M := M),
      Integrable h
        ((chartLocalMeasure (I := I) g α).withDensity
          (fun y : M => ENNReal.ofReal ((chartAtlasPOU I M) α y))) := by
    intro α hα
    refine hh_int.mono_measure ?_
    rw [hVol_eq]
    exact Finset.single_le_sum
      (f := fun β : M => (chartLocalMeasure (I := I) g β).withDensity
        (fun y : M => ENNReal.ofReal ((chartAtlasPOU I M) β y)))
      (s := chartAtlasPOUFinset (I := I) (M := M))
      (fun _ _ => Measure.zero_le _) hα
  conv_lhs => rw [hVol_eq]
  exact integral_finsetSum_measure hsummand_int

theorem chart_sum_integral
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (h : M → ℝ)
    (hh_int : Integrable h (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ∑ α ∈ chartAtlasPOUFinset (I := I) (M := M),
        ∫ x, h x * (chartAtlasPOU I M) α x
          ∂(chartLocalMeasure (I := I) g α) =
      ∫ x, h x ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  have hVol_eq := riemannianVolumeMeasure_eq_finset_sum (I := I) (M := M) g
  have hsummand_int : ∀ α ∈ chartAtlasPOUFinset (I := I) (M := M),
      Integrable h ((chartLocalMeasure (I := I) g α).withDensity
        (fun y : M => ENNReal.ofReal ((chartAtlasPOU I M) α y))) := by
    intro α hα
    refine hh_int.mono_measure ?_
    rw [hVol_eq]
    exact Finset.single_le_sum
      (f := fun β : M => (chartLocalMeasure (I := I) g β).withDensity
        (fun y : M => ENNReal.ofReal ((chartAtlasPOU I M) β y)))
      (s := chartAtlasPOUFinset (I := I) (M := M))
      (fun _ _ => Measure.zero_le _) hα
  have hglobal :
      ∫ x, h x ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∑ α ∈ chartAtlasPOUFinset (I := I) (M := M),
          ∫ x, h x ∂((chartLocalMeasure (I := I) g α).withDensity
            (fun y : M => ENNReal.ofReal ((chartAtlasPOU I M) α y))) := by
    conv_lhs => rw [hVol_eq]
    exact integral_finsetSum_measure hsummand_int
  rw [hglobal]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  let ρ : M → ℝ := fun x => (chartAtlasPOU I M) α x
  have hρ_nonneg : ∀ x, 0 ≤ ρ x := fun x => (chartAtlasPOU I M).nonneg α x
  have hρ_ae : AEMeasurable (fun x : M => ENNReal.ofReal (ρ x))
      (chartLocalMeasure (I := I) g α) :=
    (measurable_ofReal_pou_weight (chartAtlasPOU I M) α).aemeasurable
  have hρ_lt_top : ∀ᵐ x ∂(chartLocalMeasure (I := I) g α),
      ENNReal.ofReal (ρ x) < ⊤ := Filter.Eventually.of_forall fun _ => by simp
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (μ := chartLocalMeasure (I := I) g α)
    (f := fun x : M => ENNReal.ofReal (ρ x)) hρ_ae hρ_lt_top]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [ENNReal.toReal_ofReal (hρ_nonneg x), smul_eq_mul, ρ, mul_comm]

theorem volume_variation_formula_from_chart_derivs
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (f : ℝ → M → ℝ) (t : ℝ)
    (Iα : M → ℝ)
    (Iglobal : ℝ)
    (hα_deriv : ∀ α ∈ chartAtlasPOUFinset (I := I) (M := M),
      HasDerivAt
        (fun s : ℝ => ∫ x, f s x
          ∂((chartLocalMeasure (I := I) (g_fam s) α).withDensity
              (fun y : M => ENNReal.ofReal ((chartAtlasPOU I M) α y))))
        (Iα α) t)
    (hα_sum_val : ∑ α ∈ chartAtlasPOUFinset (I := I) (M := M), Iα α = Iglobal) :
    HasDerivAt
      (fun s : ℝ => ∑ α ∈ chartAtlasPOUFinset (I := I) (M := M),
        ∫ x, f s x
          ∂((chartLocalMeasure (I := I) (g_fam s) α).withDensity
              (fun y : M => ENNReal.ofReal ((chartAtlasPOU I M) α y))))
      Iglobal t := by
  rw [← hα_sum_val]
  exact HasDerivAt.fun_sum hα_deriv

theorem integral_riemannianMeasureFamily_eq_finset_sum
    {P : Type*}
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g_fam : P → SmoothRiemannianMetric I M)
    (f : P → M → ℝ) (t : P)
    (hf_cont : Continuous (f t)) :
    ∫ x, f t x ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t)
      = ∑ α ∈ chartAtlasPOUFinset (I := I) (M := M),
          ∫ x, f t x
            ∂((chartLocalMeasure (I := I) (g_fam t) α).withDensity
              (fun y : M => ENNReal.ofReal ((chartAtlasPOU I M) α y))) := by
  rw [riemannianMeasureFamily_def]
  exact integral_riemannianVolumeMeasure_eq_finset_sum (I := I) (M := M)
    (g_fam t) (f t) hf_cont

theorem volume_variation_formula_of_chart_integrals
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (f : ℝ → M → ℝ) (t : ℝ)
    (Iα : M → ℝ) (Iglobal : ℝ)
    (hf_cont : ∀ᶠ s in 𝓝 t, Continuous (f s))
    (hα_deriv : ∀ α ∈ chartAtlasPOUFinset (I := I) (M := M),
      HasDerivAt
        (fun s : ℝ => ∫ x, f s x
          ∂((chartLocalMeasure (I := I) (g_fam s) α).withDensity
              (fun y : M => ENNReal.ofReal ((chartAtlasPOU I M) α y))))
        (Iα α) t)
    (hα_sum_val : ∑ α ∈ chartAtlasPOUFinset (I := I) (M := M), Iα α = Iglobal) :
    HasDerivAt
      (fun s : ℝ =>
        ∫ x, f s x ∂(riemannianMeasureFamily (I := I) (M := M) g_fam s))
      Iglobal t := by
  have hfun :
      (fun s : ℝ =>
          ∫ x, f s x ∂(riemannianMeasureFamily (I := I) (M := M) g_fam s))
        =ᶠ[𝓝 t]
      (fun s : ℝ => ∑ α ∈ chartAtlasPOUFinset (I := I) (M := M),
        ∫ x, f s x
          ∂((chartLocalMeasure (I := I) (g_fam s) α).withDensity
              (fun y : M => ENNReal.ofReal ((chartAtlasPOU I M) α y)))) := by
    filter_upwards [hf_cont] with s hs
    exact integral_riemannianMeasureFamily_eq_finset_sum (I := I) (M := M)
      g_fam f s hs
  refine HasDerivAt.congr_of_eventuallyEq ?_ hfun
  exact volume_variation_formula_from_chart_derivs (I := I) (M := M)
    g_fam f t Iα Iglobal hα_deriv hα_sum_val

end CalabiYau.RiemannianVolume
