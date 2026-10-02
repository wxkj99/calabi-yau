-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Integration/Measure/Family/Basic.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Riemannian.Volume.Family.Decomposition
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

section CleanVolumeVariation

variable {g_fam : ℝ → SmoothRiemannianMetric I M}

lemma per_chart_integrand_hasDerivAt
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t)
    (α : M) {x : M}
    (hxα : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (f : ℝ → M → ℝ) (ρ : M → ℝ)
    (hf : HasDerivAt (fun s : ℝ => f s x) (deriv (fun s : ℝ => f s x) t) t) :
    HasDerivAt
      (fun s : ℝ => f s x * ρ x *
        chartDensity (I := I) (g_fam s) α x)
      ((deriv (fun s : ℝ => f s x) t +
          (1/2) * traceTimeDerivMetric (I := I) g_fam t x * f t x) * ρ x *
        chartDensity (I := I) (g_fam t) α x) t := by
  classical
  set n := Fin (Module.finrank ℝ E) with hn_def
  have hG : ∀ i j : n,
      HasDerivAt (fun s => chartGramMatrixFamily (I := I) g_fam α x s i j)
        (deriv (fun s => chartGramMatrixFamily (I := I) g_fam α x s i j) t) t := by
    intro i j
    exact hasDerivAt_chartGramMatrix_entry (I := I) (M := M) hreg α hxα i j t
  have hdensity_deriv :
      HasDerivAt
        (fun s : ℝ => chartDensity (I := I) (g_fam s) α x)
        ((1 / 2) *
          Matrix.trace ((chartGramMatrixFamily (I := I) g_fam α x t)⁻¹ *
            (Matrix.of fun i j : n =>
              deriv (fun s => chartGramMatrixFamily (I := I) g_fam α x s i j) t)) *
          Real.sqrt (chartGramMatrixFamily (I := I) g_fam α x t).det) t := by
    have := hasDerivAt_chartDensityFamily_eq_half_trace_inv_mul
      (I := I) (M := M) g_fam α t (x := x) hxα
      (Matrix.of fun i j : n =>
        deriv (fun s => chartGramMatrixFamily (I := I) g_fam α x s i j) t)
      (by
        intro i j
        exact hG i j)
    change HasDerivAt (fun s => chartDensity (I := I) (g_fam s) α x) _ t
    exact this
  have htrace :
      Matrix.trace ((chartGramMatrixFamily (I := I) g_fam α x t)⁻¹ *
        (Matrix.of fun i j : n =>
          deriv (fun s => chartGramMatrixFamily (I := I) g_fam α x s i j) t))
        = traceTimeDerivMetric (I := I) g_fam t x := by
    change Matrix.trace ((CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam t) α x)⁻¹ *
        (Matrix.of fun i j : n =>
          deriv (fun s => CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) α x i j) t))
      = traceTimeDerivMetric (I := I) g_fam t x
    rw [traceTimeDerivMetric_eq_trace_chartGramMatrix
      (I := I) (M := M) hreg α hxα]
  have hdensity_val :
      chartDensity (I := I) (g_fam t) α x
        = Real.sqrt (chartGramMatrixFamily (I := I) g_fam α x t).det := by
    rfl
  have hdensity_deriv' :
      HasDerivAt
        (fun s : ℝ => chartDensity (I := I) (g_fam s) α x)
        ((1 / 2) * traceTimeDerivMetric (I := I) g_fam t x *
          chartDensity (I := I) (g_fam t) α x) t := by
    rw [hdensity_val]
    have := hdensity_deriv
    rw [htrace] at this
    exact this
  have hfρ : HasDerivAt (fun s : ℝ => f s x * ρ x)
      (deriv (fun s : ℝ => f s x) t * ρ x) t :=
    hf.mul_const (ρ x)
  have hprod := hfρ.mul hdensity_deriv'
  have halgebra :
      (deriv (fun s : ℝ => f s x) t * ρ x) *
          chartDensity (I := I) (g_fam t) α x
        + (f t x * ρ x) *
          ((1 / 2) * traceTimeDerivMetric (I := I) g_fam t x *
            chartDensity (I := I) (g_fam t) α x)
      = (deriv (fun s : ℝ => f s x) t +
          (1/2) * traceTimeDerivMetric (I := I) g_fam t x * f t x) * ρ x *
          chartDensity (I := I) (g_fam t) α x := by
    ring
  rw [← halgebra]
  exact hprod

theorem chartLocal_weighted_finset_sum_eq_riemannianMeasure_integral
    [T2Space M] [CompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M) (t : ℝ)
    (h : M → ℝ) (hh_cont : Continuous h) :
    ∑ α ∈ chartAtlasPOUFinset (I := I) (M := M),
        ∫ x, h x * (chartAtlasPOU I M) α x
          ∂(chartLocalMeasure (I := I) (g_fam t) α)
      = ∫ x, h x ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) := by
  classical
  rw [riemannianMeasureFamily_def]
  rw [integral_riemannianVolumeMeasure_eq_finset_sum (I := I) (M := M)
      (g_fam t) h hh_cont]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  set ρ : M → ℝ := fun x => (chartAtlasPOU I M) α x with hρ_def
  have hρ_cont : Continuous ρ := ((chartAtlasPOU I M) α).contMDiff.continuous
  have hρ_nonneg : ∀ x, 0 ≤ ρ x := fun x => (chartAtlasPOU I M).nonneg _ _
  have hρ_ae : AEMeasurable (fun x : M => ENNReal.ofReal (ρ x))
      (chartLocalMeasure (I := I) (g_fam t) α) := by
    exact (ENNReal.measurable_ofReal.comp hρ_cont.measurable).aemeasurable
  have hρ_lt_top : ∀ᵐ x ∂(chartLocalMeasure (I := I) (g_fam t) α),
      ENNReal.ofReal (ρ x) < ⊤ :=
    Filter.Eventually.of_forall (fun _ => by simp)
  have hswap :
      ∫ x, h x
          ∂((chartLocalMeasure (I := I) (g_fam t) α).withDensity
              (fun y : M => ENNReal.ofReal (ρ y)))
        = ∫ x, (ENNReal.ofReal (ρ x)).toReal • h x
            ∂(chartLocalMeasure (I := I) (g_fam t) α) :=
    integral_withDensity_eq_integral_toReal_smul₀
      (μ := chartLocalMeasure (I := I) (g_fam t) α)
      (f := fun y : M => ENNReal.ofReal (ρ y)) hρ_ae hρ_lt_top
      (g := h)
  have htoReal : ∀ x, (ENNReal.ofReal (ρ x)).toReal = ρ x := fun x =>
    ENNReal.toReal_ofReal (hρ_nonneg x)
  have hsmul : ∀ x, (ENNReal.ofReal (ρ x)).toReal • h x = h x * ρ x := fun x => by
    rw [htoReal x, smul_eq_mul, mul_comm]
  have hintegrand_eq :
      (fun x : M => (ENNReal.ofReal (ρ x)).toReal • h x)
        = fun x : M => h x * ρ x := by
    funext x; exact hsmul x
  rw [hswap, hintegrand_eq]

theorem volume_variation_formula_of_chart_derivs
    [T2Space M] [CompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (f : ℝ → M → ℝ) (t : ℝ)
    (hf_cont : ∀ᶠ s in 𝓝 t, Continuous (f s))
    (hh_cont : Continuous
      (fun x : M => deriv (fun s : ℝ => f s x) t +
        (1/2) * traceTimeDerivMetric (I := I) g_fam t x * f t x))
    (hα_deriv_explicit : ∀ α ∈ chartAtlasPOUFinset (I := I) (M := M),
      HasDerivAt
        (fun s : ℝ => ∫ x, f s x
          ∂((chartLocalMeasure (I := I) (g_fam s) α).withDensity
              (fun y : M => ENNReal.ofReal ((chartAtlasPOU I M) α y))))
        (∫ x, (deriv (fun s : ℝ => f s x) t +
                (1/2) * traceTimeDerivMetric (I := I) g_fam t x * f t x) *
              (chartAtlasPOU I M) α x
            ∂(chartLocalMeasure (I := I) (g_fam t) α)) t) :
    HasDerivAt
      (fun s : ℝ =>
        ∫ x, f s x ∂(riemannianMeasureFamily (I := I) (M := M) g_fam s))
      (∫ x, (deriv (fun s : ℝ => f s x) t +
              (1/2) * traceTimeDerivMetric (I := I) g_fam t x * f t x)
          ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t))
      t := by
  set h : M → ℝ :=
      fun x => deriv (fun s : ℝ => f s x) t +
        (1/2) * traceTimeDerivMetric (I := I) g_fam t x * f t x with hh_def
  set Iα : M → ℝ := fun α =>
      ∫ x, h x * (chartAtlasPOU I M) α x
          ∂(chartLocalMeasure (I := I) (g_fam t) α) with hIα_def
  set Iglobal : ℝ :=
      ∫ x, h x
          ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) with hIglobal_def
  have hSum : ∑ α ∈ chartAtlasPOUFinset (I := I) (M := M), Iα α = Iglobal := by
    exact chartLocal_weighted_finset_sum_eq_riemannianMeasure_integral
      (I := I) (M := M) g_fam t h hh_cont
  refine volume_variation_formula_of_chart_integrals (I := I) (M := M)
    g_fam f t Iα Iglobal hf_cont ?_ hSum
  intro α hα
  exact hα_deriv_explicit α hα

section TraceTimeDerivMetricContinuous

lemma continuousOn_traceTimeDerivMetric_on_base
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t)
    (α : M) :
    ContinuousOn
      (fun p : ℝ × M => Matrix.trace
        ((CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹ *
          (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
            deriv (fun s => CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) α p.2 i j) p.1)))
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
  classical
  set n := Fin (Module.finrank ℝ E)
  have hG_joint : ∀ i j : n, ContinuousOn
      (fun p : ℝ × M => CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) α p.2 i j)
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := fun i j =>
    hreg.continuousOn_chartGramMatrix α i j
  have hdG_joint : ∀ i j : n, ContinuousOn
      (fun p : ℝ × M =>
        deriv (fun s : ℝ => CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) α p.2 i j) p.1)
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := fun i j =>
    hreg.continuousOn_deriv_chartGramMatrix α i j
  have h_det_cont : ContinuousOn
      (fun p : ℝ × M => (CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) α p.2).det)
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
    have hexp : (fun p : ℝ × M => (CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) α p.2).det)
        = (fun p : ℝ × M =>
            ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
              ∏ i, CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) α p.2 (σ i) i) := by
      funext p
      rw [Matrix.det_apply]
      simp [Units.smul_def]
      rfl
    rw [hexp]
    refine continuousOn_finsetSum _ (fun σ _ => ?_)
    refine ContinuousOn.mul continuousOn_const ?_
    refine continuousOn_finsetProd _ (fun i _ => ?_)
    exact hG_joint (σ i) i
  have h_adj_cont : ∀ k v : n, ContinuousOn
      (fun p : ℝ × M => (CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) α p.2).adjugate k v)
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
    intro k v
    have hform : ∀ p : ℝ × M,
        (CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) α p.2).adjugate k v
          = ((CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) α p.2).updateRow v
              (Pi.single k 1)).det := by
      intro p; rw [adjugate_apply]
    have hexp : ∀ p : ℝ × M,
        ((CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) α p.2).updateRow v (Pi.single k 1)).det
          = ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
            ∏ i : n,
              ((CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) α p.2).updateRow v
                (Pi.single k 1)) (σ i) i := by
      intro p
      rw [Matrix.det_apply]
      simp [Units.smul_def]
      rfl
    have hfn_eq :
        (fun p : ℝ × M =>
          (CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) α p.2).adjugate k v)
          = fun p : ℝ × M =>
            ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
              ∏ i : n,
                ((CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) α p.2).updateRow v
                  (Pi.single k 1)) (σ i) i := by
      funext p; rw [hform p, hexp p]
    rw [hfn_eq]
    refine continuousOn_finsetSum _ (fun σ _ => ?_)
    refine ContinuousOn.mul continuousOn_const ?_
    refine continuousOn_finsetProd _ (fun i _ => ?_)
    by_cases hiv : σ i = v
    · have hconst :
          (fun p : ℝ × M =>
            ((CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) α p.2).updateRow v
              (Pi.single k 1)) (σ i) i)
            = fun _ => (Pi.single k 1 : n → ℝ) i := by
        funext p
        rw [hiv, Matrix.updateRow_self]
      rw [hconst]; exact continuousOn_const
    · have hnonrow :
          (fun p : ℝ × M =>
            ((CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) α p.2).updateRow v
              (Pi.single k 1)) (σ i) i)
            = fun p : ℝ × M =>
              CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) α p.2 (σ i) i := by
        funext p
        rw [Matrix.updateRow_apply]
        exact if_neg hiv
      rw [hnonrow]; exact hG_joint (σ i) i
  have h_det_ne_zero : ∀ p ∈ (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet
        : Set (ℝ × M)),
      (CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) α p.2).det ≠ 0 := by
    intro p hp
    exact ne_of_gt (CalabiYau.Tensor.Coordinates.chartGramMatrix_det_pos (I := I) (g_fam p.1) α hp.2)
  have h_inv_cont : ∀ i j : n, ContinuousOn
      (fun p : ℝ × M => ((CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹) i j)
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
    intro i j
    have h_inv_entry : ∀ p : ℝ × M,
        ((CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹) i j
          = (CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) α p.2).det⁻¹ *
            (CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) α p.2).adjugate i j := by
      intro p
      rw [Matrix.inv_def]
      simp [Matrix.smul_apply, Ring.inverse_eq_inv']
    have hfn_eq :
        (fun p : ℝ × M => ((CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹) i j)
          = fun p : ℝ × M =>
            (CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) α p.2).det⁻¹ *
            (CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) α p.2).adjugate i j := by
      funext p; exact h_inv_entry p
    rw [hfn_eq]
    refine ContinuousOn.mul ?_ (h_adj_cont i j)
    exact h_det_cont.inv₀ h_det_ne_zero
  have h_prod_cont : ∀ i j : n, ContinuousOn
      (fun p : ℝ × M =>
        ((CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹ *
          Matrix.of fun i j : n =>
            deriv (fun s => CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) α p.2 i j) p.1) i j)
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
    intro i j
    have hfun :
        (fun p : ℝ × M =>
          ((CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹ *
            Matrix.of fun i j : n =>
              deriv (fun s => CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) α p.2 i j) p.1) i j)
          = fun p : ℝ × M =>
            ∑ k : n, ((CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹) i k *
              (deriv (fun s : ℝ =>
                CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) α p.2 k j) p.1) := by
      funext p
      rw [Matrix.mul_apply]
      rfl
    rw [hfun]
    refine continuousOn_finsetSum _ (fun k _ => ?_)
    exact (h_inv_cont i k).mul (hdG_joint k j)
  have htrace_eq : ∀ p : ℝ × M,
      Matrix.trace ((CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹ *
          Matrix.of fun i j : n =>
            deriv (fun s => CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) α p.2 i j) p.1)
        = ∑ i : n,
            ((CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹ *
              Matrix.of fun i j : n =>
                deriv (fun s => CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) α p.2 i j) p.1) i i := by
    intro p
    rfl
  have hfun : (fun p : ℝ × M =>
        Matrix.trace ((CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹ *
          Matrix.of fun i j : n =>
            deriv (fun s => CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) α p.2 i j) p.1))
      = fun p : ℝ × M =>
          ∑ i : n, ((CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹ *
            Matrix.of fun i j : n =>
              deriv (fun s => CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) α p.2 i j) p.1) i i := by
    funext p; exact htrace_eq p
  rw [hfun]
  refine continuousOn_finsetSum _ (fun i _ => h_prod_cont i i)

lemma traceTimeDerivMetric_continuous
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t) :
    Continuous (fun x : M => traceTimeDerivMetric (I := I) g_fam t x) := by
  classical
  refine continuous_iff_continuousAt.mpr (fun x₀ => ?_)
  set n := Fin (Module.finrank ℝ E) with hn_def
  set α : M := x₀
  have hα_base_open : IsOpen (trivializationAt E (TangentSpace I) α).baseSet :=
    (trivializationAt E (TangentSpace I) α).open_baseSet
  have hx₀_base : x₀ ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    change x₀ ∈ (chartAt H x₀).source
    exact mem_chart_source _ _
  have h_joint : ContinuousOn
      (fun p : ℝ × M => Matrix.trace
        ((CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹ *
          (Matrix.of fun i j : n =>
            deriv (fun s => CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) α p.2 i j) p.1)))
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :=
    continuousOn_traceTimeDerivMetric_on_base (I := I) (M := M) hreg α
  have h_slice : ContinuousOn
      (fun x : M => Matrix.trace
        ((CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam t) α x)⁻¹ *
          (Matrix.of fun i j : n =>
            deriv (fun s => CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) α x i j) t)))
      (trivializationAt E (TangentSpace I) α).baseSet := by
    intro x hx
    have hp : ((t, x) : ℝ × M) ∈
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :=
      ⟨Set.mem_univ _, hx⟩
    have h_at := (h_joint (t, x) hp)
    have hincl_cont : Continuous (fun y : M => ((t, y) : ℝ × M)) :=
      continuous_const.prodMk continuous_id
    have hincl_mapsTo : Set.MapsTo (fun y : M => ((t, y) : ℝ × M))
        (trivializationAt E (TangentSpace I) α).baseSet
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :=
      fun y hy => ⟨Set.mem_univ _, hy⟩
    exact h_at.comp hincl_cont.continuousWithinAt hincl_mapsTo
  have hev : (fun x : M => traceTimeDerivMetric (I := I) g_fam t x) =ᶠ[𝓝 x₀]
      (fun x : M => Matrix.trace
        ((CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam t) α x)⁻¹ *
          (Matrix.of fun i j : n =>
            deriv (fun s => CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) α x i j) t))) := by
    filter_upwards [hα_base_open.mem_nhds hx₀_base] with y hy
    exact traceTimeDerivMetric_eq_trace_chartGramMatrix
      (I := I) (M := M) hreg α hy
  refine ContinuousAt.congr ?_ hev.symm
  exact h_slice.continuousAt (hα_base_open.mem_nhds hx₀_base)

lemma continuousOn_traceTimeDerivMetric_of_base
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t) (α : M) :
    ContinuousOn
      (fun p : ℝ × M => traceTimeDerivMetric (I := I) g_fam p.1 p.2)
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
  have h_base := continuousOn_traceTimeDerivMetric_on_base
    (I := I) (M := M) hreg α
  have h_eq : Set.EqOn
      (fun p : ℝ × M => traceTimeDerivMetric (I := I) g_fam p.1 p.2)
      (fun p : ℝ × M => Matrix.trace
        ((CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹ *
          (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
            deriv (fun s => CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) α p.2 i j) p.1)))
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
    intro p hp
    exact traceTimeDerivMetric_eq_trace_chartGramMatrix
      (I := I) (M := M) (t := p.1) (hreg.at_any p.1) α hp.2
  exact h_base.congr h_eq

lemma traceTimeDerivMetric_joint_continuous
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t) :
    Continuous
      (fun p : ℝ × M => traceTimeDerivMetric (I := I) g_fam p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  let e := trivializationAt E (TangentSpace I) p.2
  have hopen : IsOpen ((Set.univ : Set ℝ) ×ˢ e.baseSet) :=
    isOpen_univ.prod e.open_baseSet
  have hp : p ∈ (Set.univ : Set ℝ) ×ˢ e.baseSet := by
    exact ⟨Set.mem_univ _, by simp [e]⟩
  exact
    ((continuousOn_traceTimeDerivMetric_of_base
      (I := I) (M := M) hreg p.2) p hp).continuousAt
      (hopen.mem_nhds hp)

lemma continuousOn_chartDensity_family
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t) (α : M) :
    ContinuousOn
      (fun p : ℝ × M => chartDensity (I := I) (g_fam p.1) α p.2)
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
  classical
  set n := Fin (Module.finrank ℝ E)
  have hG_joint : ∀ i j : n, ContinuousOn
      (fun p : ℝ × M => CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) α p.2 i j)
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := fun i j =>
    hreg.continuousOn_chartGramMatrix α i j
  have h_det_cont : ContinuousOn
      (fun p : ℝ × M => (CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) α p.2).det)
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
    have hexp :
        (fun p : ℝ × M => (CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) α p.2).det)
          = (fun p : ℝ × M =>
              ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
                ∏ i, CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) α p.2 (σ i) i) := by
      funext p
      rw [Matrix.det_apply]
      simp [Units.smul_def]
      rfl
    rw [hexp]
    refine continuousOn_finsetSum _ (fun σ _ => ?_)
    refine ContinuousOn.mul continuousOn_const ?_
    refine continuousOn_finsetProd _ (fun i _ => ?_)
    exact hG_joint (σ i) i
  have h_sqrtdet_cont : ContinuousOn
      (fun p : ℝ × M =>
        Real.sqrt ((CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) α p.2).det))
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :=
    Real.continuous_sqrt.comp_continuousOn h_det_cont
  refine h_sqrtdet_cont.congr ?_
  intro p _; rfl

lemma continuousOn_chartTrace_form_of_base_pullback
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t) (α : M)
    {S : Set (ℝ × E)} (sym : E → M)
    (hsym_cont : ContinuousOn (fun p : ℝ × E => (p.1, sym p.2)) S)
    (hsym_maps : Set.MapsTo (fun p : ℝ × E => ((p.1, sym p.2) : ℝ × M)) S
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet)) :
    ContinuousOn
      (fun p : ℝ × E => Matrix.trace
        ((CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) α (sym p.2))⁻¹ *
          (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
            deriv (fun s => CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) α (sym p.2) i j) p.1)))
      S := by
  have h_base := continuousOn_traceTimeDerivMetric_on_base (I := I) (M := M) hreg α
  have h_comp : ContinuousOn
      ((fun p : ℝ × M => Matrix.trace
          ((CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹ *
            (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
              deriv (fun s => CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) α p.2 i j) p.1)))
        ∘ (fun p : ℝ × E => ((p.1, sym p.2) : ℝ × M))) S :=
    h_base.comp hsym_cont hsym_maps
  exact h_comp

end TraceTimeDerivMetricContinuous

section PerChartHasDerivAt

variable {g_fam : ℝ → SmoothRiemannianMetric I M}

private lemma chartDensity_nonneg_of_base
    (g : SmoothRiemannianMetric I M) (α : M) (x : M) :
    0 ≤ chartDensity (I := I) g α x := by
  unfold chartDensity
  exact Real.sqrt_nonneg _

lemma per_chart_hasDerivAt
    [T2Space M] [CompactSpace M]
    {g_fam : ℝ → SmoothRiemannianMetric I M} {f : ℝ → M → ℝ} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t)
    (hf : FunctionRegularAt f t)
    (α : M) :
    HasDerivAt
      (fun s : ℝ => ∫ x, f s x
        ∂((chartLocalMeasure (I := I) (g_fam s) α).withDensity
            (fun y : M => ENNReal.ofReal ((chartAtlasPOU I M) α y))))
      (∫ x, (deriv (fun s : ℝ => f s x) t
              + (1/2) * traceTimeDerivMetric (I := I) g_fam t x * f t x) *
            (chartAtlasPOU I M) α x
          ∂(chartLocalMeasure (I := I) (g_fam t) α)) t := by
  classical
  set n := Fin (Module.finrank ℝ E) with hn_def
  set ρα : M → ℝ := fun x => (chartAtlasPOU I M) α x with hρα_def
  set μₐ : MeasureTheory.Measure M := chartLocalMeasure (I := I) (g_fam t) α with hμα_def
  set target : Set E := (extChartAt I α).target with htarget_def
  set symm : E → M := fun y => (extChartAt I α).symm y with hsymm_def
  have htarget_meas : MeasurableSet target :=
    measurableSet_extChartAt_target (I := I) α
  have hρα_cont : Continuous ρα := ((chartAtlasPOU I M) α).contMDiff.continuous
  have hρα_nonneg : ∀ x, 0 ≤ ρα x := fun x => (chartAtlasPOU I M).nonneg _ _
  have hρα_le_one : ∀ x, ρα x ≤ 1 := fun x => (chartAtlasPOU I M).le_one _ _
  have hρα_subord : tsupport ρα ⊆ (chartAt H α).source :=
    (chartAtlasPOU_isSubordinate I M) α
  have hρα_tsupport_compact : IsCompact (tsupport ρα) := isClosed_tsupport ρα |>.isCompact
  have hf_cont_joint : Continuous (fun p : ℝ × M => f p.1 p.2) := hf.continuous_joint
  have hft_cont : Continuous (f t) := by
    have : Continuous ((fun p : ℝ × M => f p.1 p.2) ∘ (fun x : M => (t, x))) := by
      refine hf_cont_joint.comp ?_
      exact continuous_const.prodMk continuous_id
    exact this
  have h_deriv_cont_joint_M : Continuous
      (fun p : ℝ × M => deriv (fun s : ℝ => f s p.2) p.1) :=
    hf.continuous_deriv_joint
  have h_deriv_cont : Continuous (fun x : M => deriv (fun s : ℝ => f s x) t) := by
    have : Continuous ((fun p : ℝ × M => deriv (fun s : ℝ => f s p.2) p.1)
        ∘ (fun x : M => (t, x))) :=
      h_deriv_cont_joint_M.comp (continuous_const.prodMk continuous_id)
    exact this
  have h_tr_cont : Continuous (fun x : M => traceTimeDerivMetric (I := I) g_fam t x) :=
    traceTimeDerivMetric_continuous (I := I) (M := M) hreg
  have h_density_contOn : ContinuousOn
      (fun x : M => chartDensity (I := I) (g_fam t) α x)
      (trivializationAt E (TangentSpace I) α).baseSet :=
    chartDensity_continuousOn (I := I) (g_fam t) α
  have h_symm_contOn : ContinuousOn symm target :=
    continuousOn_extChartAt_symm (I := I) α
  have h_symm_maps : ∀ y ∈ target, symm y ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    intro y hy
    have hsrc : symm y ∈ (extChartAt I α).source := (extChartAt I α).map_target hy
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hsrc
    exact hsrc
  obtain ⟨Cf, hCf⟩ : ∃ C, ∀ x, ‖f t x‖ ≤ C := by
    have hIm := (isCompact_univ (X := M)).image hft_cont.norm
    obtain ⟨C, hC⟩ := hIm.bddAbove
    exact ⟨C, fun x => hC ⟨x, Set.mem_univ _, rfl⟩⟩
  set Fmdl : ℝ → E → ℝ := fun s y =>
    f s (symm y) * ρα (symm y) * chartDensity (I := I) (g_fam s) α (symm y)
  set Fprim : ℝ → E → ℝ := fun s y =>
    (deriv (fun r : ℝ => f r (symm y)) s +
      (1/2) * traceTimeDerivMetric (I := I) g_fam s (symm y) *
        f s (symm y)) * ρα (symm y) *
      chartDensity (I := I) (g_fam s) α (symm y)
  have hH'_deriv : ∀ᵐ y ∂((modelHaar (E := E)).restrict target),
      ∀ s ∈ (Set.univ : Set ℝ), HasDerivAt (fun r => Fmdl r y) (Fprim s y) s := by
    refine (MeasureTheory.ae_restrict_iff' htarget_meas).mpr ?_
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    intro s _
    have hsym_base : symm y ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
      h_symm_maps y hy
    have hslice : HasDerivAt (fun r : ℝ => f r (symm y))
        (deriv (fun r : ℝ => f r (symm y)) s) s :=
      hf.hasDerivAt_time (symm y) s
    have hpcd := per_chart_integrand_hasDerivAt
      (I := I) (M := M) (t := s) (hreg.at_any s) α (x := symm y) hsym_base f ρα hslice
    exact hpcd
  set K : Set M := tsupport ρα
  set K' : Set E := (extChartAt I α) '' K
  have hK_compact : IsCompact K := hρα_tsupport_compact
  have hK'_compact : IsCompact K' :=
    hK_compact.image_of_continuousOn (continuousOn_extChartAt (I := I) α |>.mono (by
      intro y hy
      have : y ∈ (chartAt H α).source := hρα_subord hy
      rw [← extChartAt_source_eq_chartAt_source (I := I)] at this
      exact this))
  have hK'_meas : MeasurableSet K' := hK'_compact.measurableSet
  have hK'_meas_lt_top : (modelHaar (E := E)) K' < ⊤ :=
    hK'_compact.measure_lt_top
  have h_deriv_cont_joint : Continuous
      (fun p : ℝ × M => deriv (fun s : ℝ => f s p.2) p.1) :=
    hf.continuous_deriv_joint
  set I₁ : Set ℝ := Set.Icc (t - 1) (t + 1)
  have hI₁_compact : IsCompact I₁ := isCompact_Icc
  have ht_interior : t ∈ Set.Ioo (t - 1 : ℝ) (t + 1) := by
    refine ⟨?_, ?_⟩ <;> linarith
  have ht_in_I₁ : t ∈ I₁ := ⟨by linarith, by linarith⟩
  set ball_s : Set ℝ := Metric.ball t 1
  have hballs_nhd : ball_s ∈ 𝓝 t := Metric.ball_mem_nhds _ one_pos
  have hballs_sub_I₁ : ball_s ⊆ I₁ := by
    intro s hs
    have hs' : |s - t| < 1 := by
      change dist s t < 1 at hs
      simpa [Real.dist_eq, Real.norm_eq_abs] using hs
    refine ⟨?_, ?_⟩
    · have := (abs_lt.mp hs').1; linarith
    · have := (abs_lt.mp hs').2; linarith
  set Ω : Set (ℝ × E) := I₁ ×ˢ K'
  have hΩ_compact : IsCompact Ω := hI₁_compact.prod hK'_compact
  have hK'_sub_target : K' ⊆ target := by
    intro y hy
    obtain ⟨x, hxK, hx_eq⟩ := hy
    have hx_source : x ∈ (extChartAt I α).source := by
      have : x ∈ (chartAt H α).source := hρα_subord hxK
      rw [← extChartAt_source_eq_chartAt_source (I := I)] at this
      exact this
    rw [← hx_eq]
    exact (extChartAt I α).map_source hx_source
  have h_Fprim_continuousOn_Ω :
      ContinuousOn (fun p : ℝ × E => Fprim p.1 p.2) (I₁ ×ˢ K') := by
    have h_symm_contOn_K' : ContinuousOn symm K' := h_symm_contOn.mono hK'_sub_target
    have h_symm_pair_contOn :
        ContinuousOn (fun p : ℝ × E => (p.1, symm p.2)) (I₁ ×ˢ K') := by
      refine ContinuousOn.prodMk continuousOn_fst ?_
      refine h_symm_contOn_K'.comp continuousOn_snd ?_
      intro p hp
      exact hp.2
    have hf_comp : ContinuousOn (fun p : ℝ × E => f p.1 (symm p.2)) (I₁ ×ˢ K') := by
      exact hf_cont_joint.continuousOn.comp h_symm_pair_contOn (fun _ _ => Set.mem_univ _)
    have hρα_comp : ContinuousOn (fun p : ℝ × E => ρα (symm p.2)) (I₁ ×ˢ K') := by
      have : ContinuousOn (fun y : E => ρα (symm y)) K' := by
        exact hρα_cont.continuousOn.comp h_symm_contOn_K' (fun _ _ => Set.mem_univ _)
      exact (this.comp continuousOn_snd (fun _ hp => hp.2))
    have hdensity_comp : ContinuousOn
        (fun p : ℝ × E => chartDensity (I := I) (g_fam p.1) α (symm p.2))
        (I₁ ×ˢ K') := by
      have h_joint_cont : ContinuousOn
          (fun p : ℝ × M => chartDensity (I := I) (g_fam p.1) α p.2)
          (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :=
        continuousOn_chartDensity_family (I := I) (M := M) hreg α
      have hmaps : Set.MapsTo (fun p : ℝ × E => ((p.1, symm p.2) : ℝ × M))
          (I₁ ×ˢ K')
          (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
        intro p hp
        refine ⟨Set.mem_univ _, ?_⟩
        exact h_symm_maps p.2 (hK'_sub_target hp.2)
      have h := h_joint_cont.comp h_symm_pair_contOn hmaps
      exact h
    have h_deriv_comp : ContinuousOn
        (fun p : ℝ × E => deriv (fun r : ℝ => f r (symm p.2)) p.1) (I₁ ×ˢ K') := by
      have h := h_deriv_cont_joint.continuousOn.comp h_symm_pair_contOn
        (fun _ _ => Set.mem_univ _)
      exact h
    have h_symm_pair_mapsTo : Set.MapsTo (fun p : ℝ × E => ((p.1, symm p.2) : ℝ × M))
        (I₁ ×ˢ K')
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := fun p hp =>
      ⟨Set.mem_univ _, h_symm_maps p.2 (hK'_sub_target hp.2)⟩
    have h_tr_base_pb :
        ContinuousOn (fun p : ℝ × E => Matrix.trace
          ((CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) α (symm p.2))⁻¹ *
            (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
              deriv (fun s => CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) α (symm p.2) i j) p.1)))
        (I₁ ×ˢ K') :=
      continuousOn_chartTrace_form_of_base_pullback (I := I) (M := M) hreg α
        (sym := symm) h_symm_pair_contOn h_symm_pair_mapsTo
    have h_tr_comp : ContinuousOn
        (fun p : ℝ × E => traceTimeDerivMetric (I := I) g_fam p.1 (symm p.2))
        (I₁ ×ˢ K') := by
      refine h_tr_base_pb.congr ?_
      intro p hp
      have hsym_base : symm p.2 ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
        h_symm_maps p.2 (hK'_sub_target hp.2)
      exact traceTimeDerivMetric_eq_trace_chartGramMatrix
        (I := I) (M := M) (t := p.1) (hreg.at_any p.1) α hsym_base
    change ContinuousOn (fun p : ℝ × E =>
        (deriv (fun r : ℝ => f r (symm p.2)) p.1 +
            (1/2) * traceTimeDerivMetric (I := I) g_fam p.1 (symm p.2) *
              f p.1 (symm p.2)) * ρα (symm p.2) *
          chartDensity (I := I) (g_fam p.1) α (symm p.2)) (I₁ ×ˢ K')
    refine ContinuousOn.mul (ContinuousOn.mul ?_ hρα_comp) hdensity_comp
    refine ContinuousOn.add h_deriv_comp ?_
    refine ContinuousOn.mul ?_ hf_comp
    refine ContinuousOn.mul continuousOn_const ?_
    exact h_tr_comp
  obtain ⟨CH, hCH⟩ : ∃ C, ∀ p ∈ (I₁ ×ˢ K'), |Fprim p.1 p.2| ≤ C := by
    classical
    by_cases hne' : (I₁ ×ˢ K' : Set (ℝ × E)).Nonempty
    · have hΩne : Ω.Nonempty := hne'
      have h_abs_cont : ContinuousOn (fun p : ℝ × E => |Fprim p.1 p.2|) Ω :=
        h_Fprim_continuousOn_Ω.abs
      have hbdd := hΩ_compact.bddAbove_image h_abs_cont
      obtain ⟨C, hC⟩ := hbdd
      refine ⟨C, fun p hp => ?_⟩
      exact hC ⟨p, hp, rfl⟩
    · refine ⟨0, fun p hp => ?_⟩
      exact (hne' ⟨p, hp⟩).elim
  set C₀ : ℝ := |CH|
  set b : E → ℝ := fun y => C₀ * (K'.indicator (fun _ : E => (1 : ℝ))) y with hb_def
  have hb_nonneg : ∀ y, 0 ≤ b y := by
    intro y
    have h_ind_nonneg : 0 ≤ K'.indicator (fun _ : E => (1 : ℝ)) y :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) _
    exact mul_nonneg (abs_nonneg _) h_ind_nonneg
  have hb_integrable : Integrable b ((modelHaar (E := E)).restrict target) := by
    have h_ind_int : Integrable (K'.indicator (fun _ : E => (1 : ℝ)))
        ((modelHaar (E := E)).restrict target) := by
      have h_rest_int : Integrable (K'.indicator (fun _ : E => (1 : ℝ))) (modelHaar (E := E)) := by
        rw [integrable_indicator_iff hK'_meas]
        exact integrableOn_const (hs := ne_of_lt hK'_meas_lt_top)
      exact h_rest_int.restrict
    have := h_ind_int.const_mul C₀
    simpa [b, smul_eq_mul] using this
  have h_bound_prop : ∀ᵐ y ∂((modelHaar (E := E)).restrict target),
      ∀ s ∈ ball_s, ‖Fprim s y‖ ≤ b y := by
    refine (MeasureTheory.ae_restrict_iff' htarget_meas).mpr ?_
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    intro s hs
    by_cases hyK' : y ∈ K'
    · have hp : (s, y) ∈ (I₁ ×ˢ K' : Set (ℝ × E)) := ⟨hballs_sub_I₁ hs, hyK'⟩
      have hbound := hCH (s, y) hp
      have hby : b y = C₀ := by
        simp [b, Set.indicator_of_mem hyK']
      rw [Real.norm_eq_abs, hby]
      have : |Fprim s y| ≤ CH := hbound
      refine this.trans ?_
      exact le_abs_self _
    · have h_symm_y_not_in : symm y ∉ K := by
        intro hsymInK
        exact hyK' ⟨symm y, hsymInK, by
          exact (extChartAt I α).right_inv hy⟩
      have hρ_zero : ρα (symm y) = 0 := by
        by_contra h
        have : symm y ∈ Function.support ρα := h
        exact h_symm_y_not_in (subset_tsupport _ this)
      have hH'_zero : Fprim s y = 0 := by
        change (deriv (fun r : ℝ => f r (symm y)) s +
            (1/2) * traceTimeDerivMetric (I := I) g_fam s (symm y) *
              f s (symm y)) * ρα (symm y) *
            chartDensity (I := I) (g_fam s) α (symm y) = 0
        rw [hρ_zero, mul_zero, zero_mul]
      rw [hH'_zero]
      have hby_nonneg : 0 ≤ b y := hb_nonneg y
      simpa using hby_nonneg
  have hH_meas_at_t : ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable (Fmdl s) ((modelHaar (E := E)).restrict target) := by
    refine Filter.Eventually.of_forall (fun s => ?_)
    have h_symm_contOn_target : ContinuousOn symm target := h_symm_contOn
    have h_f_s_comp_contOn : ContinuousOn (fun y : E => f s (symm y)) target := by
      have hf_s_cont : Continuous (f s) := by
        have : Continuous ((fun p : ℝ × M => f p.1 p.2) ∘ (fun x : M => (s, x))) := by
          refine hf_cont_joint.comp ?_
          exact continuous_const.prodMk continuous_id
        exact this
      exact hf_s_cont.continuousOn.comp h_symm_contOn_target
        (fun _ _ => Set.mem_univ _)
    have h_ρα_comp_contOn : ContinuousOn (fun y : E => ρα (symm y)) target :=
      hρα_cont.continuousOn.comp h_symm_contOn_target (fun _ _ => Set.mem_univ _)
    have h_density_comp_contOn : ContinuousOn
        (fun y : E => chartDensity (I := I) (g_fam s) α (symm y)) target := by
      have h_density_s : ContinuousOn
          (fun x : M => chartDensity (I := I) (g_fam s) α x)
          (trivializationAt E (TangentSpace I) α).baseSet :=
        chartDensity_continuousOn (I := I) (g_fam s) α
      exact h_density_s.comp h_symm_contOn_target h_symm_maps
    have h_H_s_contOn : ContinuousOn (Fmdl s) target := by
      exact (h_f_s_comp_contOn.mul h_ρα_comp_contOn).mul h_density_comp_contOn
    exact (h_H_s_contOn.aestronglyMeasurable htarget_meas)
  have hH_int_at_t : Integrable (Fmdl t) ((modelHaar (E := E)).restrict target) := by
    have h_Ht_cont_K' : ContinuousOn (Fmdl t) K' := by
      have h_symm_contOn_K' : ContinuousOn symm K' := h_symm_contOn.mono hK'_sub_target
      have hf_cont : Continuous (f t) := by
        have : Continuous ((fun p : ℝ × M => f p.1 p.2) ∘ (fun x : M => (t, x))) := by
          refine hf_cont_joint.comp ?_
          exact continuous_const.prodMk continuous_id
        exact this
      have h_f_comp : ContinuousOn (fun y : E => f t (symm y)) K' :=
        hf_cont.continuousOn.comp h_symm_contOn_K' (fun _ _ => Set.mem_univ _)
      have h_ρα_comp : ContinuousOn (fun y : E => ρα (symm y)) K' :=
        hρα_cont.continuousOn.comp h_symm_contOn_K' (fun _ _ => Set.mem_univ _)
      have h_density_comp : ContinuousOn
          (fun y : E => chartDensity (I := I) (g_fam t) α (symm y)) K' := by
        refine h_density_contOn.comp h_symm_contOn_K' ?_
        intro y hy
        exact h_symm_maps y (hK'_sub_target hy)
      exact (h_f_comp.mul h_ρα_comp).mul h_density_comp
    obtain ⟨C_Fmdl, hC_H⟩ : ∃ C, ∀ y ∈ K', |Fmdl t y| ≤ C := by
      by_cases hK'_ne : K'.Nonempty
      · have h_abs_cont : ContinuousOn (fun y : E => |Fmdl t y|) K' := h_Ht_cont_K'.abs
        obtain ⟨C, hC⟩ := hK'_compact.bddAbove_image h_abs_cont
        refine ⟨C, fun y hy => ?_⟩
        exact hC ⟨y, hy, rfl⟩
      · refine ⟨0, fun y hy => ?_⟩
        exact absurd ⟨y, hy⟩ hK'_ne
    have hH_t_vanish : ∀ y ∈ target, y ∉ K' → Fmdl t y = 0 := by
      intro y hy_tg hy_not
      have : symm y ∉ K := by
        intro h
        have hsrc : symm y ∈ (chartAt H α).source := hρα_subord h
        have hsrc' : symm y ∈ (extChartAt I α).source := by
          rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hsrc
        apply hy_not
        refine ⟨symm y, h, ?_⟩
        exact (extChartAt I α).right_inv hy_tg
      have hρ_zero : ρα (symm y) = 0 := by
        by_contra h
        exact this (subset_tsupport _ (show symm y ∈ Function.support ρα from h))
      change f t (symm y) * ρα (symm y) * chartDensity (I := I) (g_fam t) α (symm y) = 0
      rw [hρ_zero, mul_zero, zero_mul]
    set C_Fprim : ℝ := max C_Fmdl 0
    have hC_Fprim_nonneg : 0 ≤ C_Fprim := le_max_right _ _
    have h_domHt : ∀ᵐ y ∂((modelHaar (E := E)).restrict target),
        ‖Fmdl t y‖ ≤ C_Fprim * K'.indicator (fun _ : E => (1 : ℝ)) y := by
      refine (MeasureTheory.ae_restrict_iff' htarget_meas).mpr ?_
      refine Filter.Eventually.of_forall (fun y hy => ?_)
      by_cases hyK' : y ∈ K'
      · rw [Set.indicator_of_mem hyK', mul_one, Real.norm_eq_abs]
        calc |Fmdl t y| ≤ C_Fmdl := hC_H y hyK'
          _ ≤ C_Fprim := le_max_left _ _
      · rw [hH_t_vanish y hy hyK']
        rw [Set.indicator_of_notMem hyK', mul_zero, norm_zero]
    have h_bound_int' : Integrable
        (fun y : E => C_Fprim * K'.indicator (fun _ : E => (1 : ℝ)) y)
        ((modelHaar (E := E)).restrict target) := by
      have h_ind_int : Integrable (K'.indicator (fun _ : E => (1 : ℝ)))
          ((modelHaar (E := E)).restrict target) := by
        have h_rest_int : Integrable (K'.indicator (fun _ : E => (1 : ℝ)))
            (modelHaar (E := E)) := by
          rw [integrable_indicator_iff hK'_meas]
          exact integrableOn_const (hs := ne_of_lt hK'_meas_lt_top)
        exact h_rest_int.restrict
      simpa [smul_eq_mul] using h_ind_int.const_mul C_Fprim
    have h_meas_Ht : AEStronglyMeasurable (Fmdl t) ((modelHaar (E := E)).restrict target) := by
      have h_symm_contOn_target : ContinuousOn symm target := h_symm_contOn
      have hf_cont : Continuous (f t) := by
        have : Continuous ((fun p : ℝ × M => f p.1 p.2) ∘ (fun x : M => (t, x))) := by
          refine hf_cont_joint.comp ?_
          exact continuous_const.prodMk continuous_id
        exact this
      have h_f_cont : ContinuousOn (fun y : E => f t (symm y)) target :=
        hf_cont.continuousOn.comp h_symm_contOn_target (fun _ _ => Set.mem_univ _)
      have h_ρ_cont : ContinuousOn (fun y : E => ρα (symm y)) target :=
        hρα_cont.continuousOn.comp h_symm_contOn_target (fun _ _ => Set.mem_univ _)
      have h_d_cont : ContinuousOn
          (fun y : E => chartDensity (I := I) (g_fam t) α (symm y)) target :=
        h_density_contOn.comp h_symm_contOn_target h_symm_maps
      exact ((h_f_cont.mul h_ρ_cont).mul h_d_cont).aestronglyMeasurable htarget_meas
    exact h_bound_int'.mono' h_meas_Ht h_domHt
  have hH'_meas_at_t : AEStronglyMeasurable (Fprim t)
      ((modelHaar (E := E)).restrict target) := by
    have h_t_in_I₁ : t ∈ I₁ := ht_in_I₁
    have h_Ht'_cont_K' : ContinuousOn (fun y : E => Fprim t y) K' := by
      have := h_Fprim_continuousOn_Ω
      have : ContinuousOn (fun p : ℝ × E => Fprim p.1 p.2) (I₁ ×ˢ K') := this
      intro y hy
      have hp : (t, y) ∈ (I₁ ×ˢ K') := ⟨h_t_in_I₁, hy⟩
      have hat : ContinuousWithinAt (fun p : ℝ × E => Fprim p.1 p.2) (I₁ ×ˢ K') (t, y) :=
        this (t, y) hp
      have hincl_cont : Continuous (fun e : E => (t, e)) :=
        continuous_const.prodMk continuous_id
      have hincl_mapsTo : Set.MapsTo (fun e : E => (t, e)) K' (I₁ ×ˢ K') :=
        fun e he => ⟨h_t_in_I₁, he⟩
      exact hat.comp hincl_cont.continuousWithinAt hincl_mapsTo
    have h_Ht'_zero_off : ∀ y ∈ target, y ∉ K' → Fprim t y = 0 := by
      intro y hy hyK'
      have h_symm_y_not_K : symm y ∉ K := by
        intro h
        apply hyK'
        refine ⟨symm y, h, ?_⟩
        exact (extChartAt I α).right_inv hy
      have hρ_zero : ρα (symm y) = 0 := by
        by_contra h
        exact h_symm_y_not_K (subset_tsupport _
          (show symm y ∈ Function.support ρα from h))
      change (deriv (fun r : ℝ => f r (symm y)) t +
          (1/2) * traceTimeDerivMetric (I := I) g_fam t (symm y) *
            f t (symm y)) * ρα (symm y) *
          chartDensity (I := I) (g_fam t) α (symm y) = 0
      rw [hρ_zero, mul_zero, zero_mul]
    have h_ind_Ht : Fprim t =ᵐ[(modelHaar (E := E)).restrict target]
        K'.indicator (fun y => Fprim t y) := by
      refine (MeasureTheory.ae_restrict_iff' htarget_meas).mpr ?_
      refine Filter.Eventually.of_forall (fun y hy => ?_)
      by_cases hyK' : y ∈ K'
      · rw [Set.indicator_of_mem hyK']
      · rw [Set.indicator_of_notMem hyK']
        exact h_Ht'_zero_off y hy hyK'
    refine AEStronglyMeasurable.congr ?_ h_ind_Ht.symm
    have h_ind_meas : AEStronglyMeasurable
        (K'.indicator (fun y : E => Fprim t y))
        ((modelHaar (E := E)).restrict target) := by
      have h_restrict : AEStronglyMeasurable (fun y : E => Fprim t y)
          ((modelHaar (E := E)).restrict K') := by
        exact h_Ht'_cont_K'.aestronglyMeasurable hK'_meas
      have : AEStronglyMeasurable (K'.indicator (fun y : E => Fprim t y))
          (modelHaar (E := E)) := by
        refine (aestronglyMeasurable_indicator_iff hK'_meas).mpr ?_
        exact h_restrict
      exact this.restrict
    exact h_ind_meas
  have h_s_mem : ball_s ∈ 𝓝 t := hballs_nhd
  have h_diff_ballsupersed : ∀ᵐ y ∂((modelHaar (E := E)).restrict target),
      ∀ s ∈ ball_s, HasDerivAt (fun r => Fmdl r y) (Fprim s y) s := by
    filter_upwards [hH'_deriv] with y hy
    intro s' _
    exact hy s' (Set.mem_univ _)
  have h_setInt := hasDerivAt_setIntegral_model (E := E) target
    (F := Fmdl) (F' := Fprim) (b := b) t (s := ball_s) h_s_mem hH_meas_at_t hH_int_at_t
    hH'_meas_at_t h_bound_prop hb_integrable h_diff_ballsupersed
  obtain ⟨_, h_inner⟩ := h_setInt
  have h_lhs_eq : ∀ s : ℝ,
      (∫ y in target, Fmdl s y ∂(modelHaar (E := E)))
        = ∫ x, f s x
            ∂((chartLocalMeasure (I := I) (g_fam s) α).withDensity
                (fun y : M => ENNReal.ofReal (ρα y))) := by
    intro s
    have hρα_meas : AEMeasurable (fun y : M => ENNReal.ofReal (ρα y))
        (chartLocalMeasure (I := I) (g_fam s) α) :=
      (ENNReal.measurable_ofReal.comp hρα_cont.measurable).aemeasurable
    have hρα_lt_top : ∀ᵐ y ∂(chartLocalMeasure (I := I) (g_fam s) α),
        ENNReal.ofReal (ρα y) < ⊤ := Filter.Eventually.of_forall (fun _ => by simp)
    have h_withD :
        ∫ x, f s x
          ∂((chartLocalMeasure (I := I) (g_fam s) α).withDensity
              (fun y : M => ENNReal.ofReal (ρα y)))
          = ∫ x, (ENNReal.ofReal (ρα x)).toReal • f s x
              ∂(chartLocalMeasure (I := I) (g_fam s) α) :=
      integral_withDensity_eq_integral_toReal_smul₀
        (μ := chartLocalMeasure (I := I) (g_fam s) α)
        (f := fun y : M => ENNReal.ofReal (ρα y)) hρα_meas hρα_lt_top
        (g := f s)
    have h_smul_eq : (fun x : M =>
        (ENNReal.ofReal (ρα x)).toReal • f s x) = fun x : M => f s x * ρα x := by
      funext x
      rw [ENNReal.toReal_ofReal (hρα_nonneg x), smul_eq_mul, mul_comm]
    have hfs_cont : Continuous (f s) := by
      have : Continuous ((fun p : ℝ × M => f p.1 p.2) ∘ (fun x : M => (s, x))) := by
        refine hf_cont_joint.comp ?_
        exact continuous_const.prodMk continuous_id
      exact this
    have h_fρ_meas : Measurable (fun x : M => f s x * ρα x) :=
      (hfs_cont.mul hρα_cont).measurable
    have h_ICLM := integral_chartLocalMeasure (I := I) (M := M) (g_fam s) α
      (fun x => f s x * ρα x) h_fρ_meas
    rw [h_withD, h_smul_eq, h_ICLM]
    have h_integrand_eq : (fun y : E =>
        chartDensity (I := I) (g_fam s) α (symm y) * (f s (symm y) * ρα (symm y)))
          = fun y : E => Fmdl s y := by
      funext y
      change chartDensity (I := I) (g_fam s) α ((extChartAt I α).symm y) *
            (f s ((extChartAt I α).symm y) * ρα ((extChartAt I α).symm y))
        = f s ((extChartAt I α).symm y) * ρα ((extChartAt I α).symm y) *
            chartDensity (I := I) (g_fam s) α ((extChartAt I α).symm y)
      ring
    rw [h_integrand_eq]
  have h_rhs_eq :
      (∫ y in target, Fprim t y ∂(modelHaar (E := E)))
        = ∫ x, (deriv (fun s : ℝ => f s x) t
              + (1/2) * traceTimeDerivMetric (I := I) g_fam t x * f t x) *
              ρα x
            ∂(chartLocalMeasure (I := I) (g_fam t) α) := by
    set gFn : M → ℝ := fun x =>
      (deriv (fun s : ℝ => f s x) t +
        (1/2) * traceTimeDerivMetric (I := I) g_fam t x * f t x) * ρα x
    have hg_cont : Continuous gFn := by
      refine Continuous.mul ?_ hρα_cont
      refine h_deriv_cont.add ?_
      refine Continuous.mul ?_ hft_cont
      exact (continuous_const.mul h_tr_cont)
    have hg_meas : Measurable gFn := hg_cont.measurable
    have h_ICLM := integral_chartLocalMeasure (I := I) (M := M) (g_fam t) α gFn hg_meas
    rw [h_ICLM]
    refine MeasureTheory.setIntegral_congr_ae htarget_meas ?_
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    change (deriv (fun r : ℝ => f r (symm y)) t +
            (1/2) * traceTimeDerivMetric (I := I) g_fam t (symm y) *
              f t (symm y)) * ρα (symm y) *
            chartDensity (I := I) (g_fam t) α (symm y)
      = chartDensity (I := I) (g_fam t) α ((extChartAt I α).symm y) *
          gFn ((extChartAt I α).symm y)
    change _ = chartDensity (I := I) (g_fam t) α (symm y) * gFn (symm y)
    change _ = chartDensity (I := I) (g_fam t) α (symm y) *
        ((deriv (fun r : ℝ => f r (symm y)) t +
          (1/2) * traceTimeDerivMetric (I := I) g_fam t (symm y) *
            f t (symm y)) * ρα (symm y))
    ring
  rw [show (fun s : ℝ => ∫ x, f s x
        ∂((chartLocalMeasure (I := I) (g_fam s) α).withDensity
            (fun y : M => ENNReal.ofReal (ρα y))))
      = fun s : ℝ => ∫ y in target, Fmdl s y ∂(modelHaar (E := E)) from ?_]
  · rw [h_rhs_eq.symm]
    exact h_inner
  · funext s
    exact (h_lhs_eq s).symm

end PerChartHasDerivAt

section CleanTheorem

variable {g_fam : ℝ → SmoothRiemannianMetric I M}

theorem first_variation_of_volume
    [T2Space M] [CompactSpace M]
    {g_fam : ℝ → SmoothRiemannianMetric I M}
    {f : ℝ → M → ℝ} {t₀ : ℝ}
    (hg : MetricFamilyRegularAt (I := I) g_fam t₀)
    (hf : FunctionRegularAt f t₀) :
    HasDerivAt
      (fun s : ℝ => ∫ x, f s x ∂(riemannianMeasureFamily (I := I) (M := M) g_fam s))
      (∫ x, (deriv (fun s : ℝ => f s x) t₀
              + (1/2) * traceTimeDerivMetric (I := I) g_fam t₀ x * f t₀ x)
          ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t₀))
      t₀ := by
  have hf_cont_joint : Continuous (fun p : ℝ × M => f p.1 p.2) := hf.continuous_joint
  have hf_cont : ∀ᶠ s in 𝓝 t₀, Continuous (f s) := by
    refine Filter.Eventually.of_forall (fun s => ?_)
    have : Continuous ((fun p : ℝ × M => f p.1 p.2) ∘ (fun x : M => (s, x))) := by
      refine hf_cont_joint.comp ?_
      exact continuous_const.prodMk continuous_id
    exact this
  have hft₀_cont : Continuous (f t₀) := by
    have : Continuous ((fun p : ℝ × M => f p.1 p.2) ∘ (fun x : M => (t₀, x))) := by
      refine hf_cont_joint.comp ?_
      exact continuous_const.prodMk continuous_id
    exact this
  have h_deriv_cont : Continuous (fun x : M => deriv (fun s : ℝ => f s x) t₀) := by
    have : Continuous ((fun p : ℝ × M => deriv (fun s : ℝ => f s p.2) p.1)
        ∘ (fun x : M => (t₀, x))) :=
      hf.continuous_deriv_joint.comp (continuous_const.prodMk continuous_id)
    exact this
  have hh_cont : Continuous (fun x : M =>
      deriv (fun s : ℝ => f s x) t₀ +
      (1/2) * traceTimeDerivMetric (I := I) g_fam t₀ x * f t₀ x) := by
    refine Continuous.add h_deriv_cont ?_
    refine Continuous.mul ?_ hft₀_cont
    refine Continuous.mul continuous_const ?_
    exact traceTimeDerivMetric_continuous (I := I) (M := M) hg
  refine volume_variation_formula_of_chart_derivs
    (I := I) (M := M) g_fam f t₀ hf_cont hh_cont ?_
  intro α hα
  exact per_chart_hasDerivAt (I := I) (M := M) hg hf α

end CleanTheorem

end CleanVolumeVariation

end CalabiYau.RiemannianVolume
