-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Integration/Measure/Family/Defs.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Riemannian.Volume.Chart.Density
public import CalabiYau.Geometry.Riemannian.Volume.Basic
public import CalabiYau.Geometry.Riemannian.Volume.Invariance
public import CalabiYau.Geometry.Riemannian.Volume.Properties
public import CalabiYau.Geometry.Riemannian.Volume.Jacobian.Derivative
public import CalabiYau.Geometry.Manifold.Bundle.PartialMfderiv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.PosDef

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

def riemannianMeasureFamily
    {P : Type*}
    [T2Space M] [SigmaCompactSpace M]
    (g_fam : P → SmoothRiemannianMetric I M) : P → MeasureTheory.Measure M :=
  fun t => riemannianVolumeMeasure (I := I) (M := M) (g_fam t)

lemma riemannianMeasureFamily_def
    {P : Type*}
    [T2Space M] [SigmaCompactSpace M]
    (g_fam : P → SmoothRiemannianMetric I M) (t : P) :
    riemannianMeasureFamily (I := I) (M := M) g_fam t =
      riemannianVolumeMeasure (I := I) (M := M) (g_fam t) := rfl

structure MetricFamilyRegularAt
    (g_fam : ℝ → SmoothRiemannianMetric I M) (t₀ : ℝ) : Prop where
  hasDerivAt_chartGramMatrix :
    ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)) {x : M},
      x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet →
      ∀ t : ℝ,
        HasDerivAt (fun s : ℝ => CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) x₀ x i j)
          (deriv (fun s : ℝ => CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) x₀ x i j) t) t
  continuousOn_chartGramMatrix :
    ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : ℝ × M => CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)
  continuousOn_deriv_chartGramMatrix :
    ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : ℝ × M =>
          deriv (fun s : ℝ => CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) x₀ p.2 i j) p.1)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)

lemma MetricFamilyRegularAt.at_any
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t) (s : ℝ) :
    MetricFamilyRegularAt (I := I) g_fam s :=
  { hasDerivAt_chartGramMatrix := hreg.hasDerivAt_chartGramMatrix
    continuousOn_chartGramMatrix := hreg.continuousOn_chartGramMatrix
    continuousOn_deriv_chartGramMatrix := hreg.continuousOn_deriv_chartGramMatrix }

structure FunctionRegularAt (f : ℝ → M → ℝ) (t₀ : ℝ) : Prop where
  hasDerivAt_time :
    ∀ (x : M) (t : ℝ), HasDerivAt (fun s : ℝ => f s x) (deriv (fun s : ℝ => f s x) t) t
  continuous_joint : Continuous (fun p : ℝ × M => f p.1 p.2)
  continuous_deriv_joint :
    Continuous (fun p : ℝ × M => deriv (fun s : ℝ => f s p.2) p.1)

omit [Module.Finite ℝ E] in
theorem FunctionRegularAt.of_contMDiff
    (f : ℝ → M → ℝ)
    (hf : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => f p.1 p.2)) (t₀ : ℝ) :
    FunctionRegularAt f t₀ := by
  let F : C^∞⟮(modelWithCornersSelf ℝ ℝ).prod I, ℝ × M; ℝ⟯ :=
    ⟨fun p => f p.1 p.2, hf⟩
  refine ⟨?_, hf.continuous, ?_⟩
  · intro x t
    have htime : ContDiff ℝ ∞ (fun s => f s x) :=
      contMDiff_iff_contDiff.mp
        (hf.comp (contMDiff_id.prodMk contMDiff_const))
    exact (htime.differentiable (by norm_num)).differentiableAt.hasDerivAt
  · have h := (CalabiYau.contMDiff_partial_deriv_fst I F).continuous
    change Continuous (fun p : ℝ × M => deriv (fun s : ℝ => f s p.2) p.1) at h
    exact h

section ChartDensityFamily

variable {g_fam : ℝ → SmoothRiemannianMetric I M}

def chartGramMatrixFamily
    (g_fam : ℝ → SmoothRiemannianMetric I M) (x₀ x : M) :
    ℝ → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  fun t => CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam t) x₀ x

@[simp] lemma chartGramMatrixFamily_apply
    (g_fam : ℝ → SmoothRiemannianMetric I M) (x₀ x : M) (t : ℝ) :
    chartGramMatrixFamily (I := I) g_fam x₀ x t =
      CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam t) x₀ x := rfl

def chartDensityFamily
    (g_fam : ℝ → SmoothRiemannianMetric I M) (x₀ x : M) :
    ℝ → ℝ :=
  fun t => chartDensity (I := I) (g_fam t) x₀ x

@[simp] lemma chartDensityFamily_apply
    (g_fam : ℝ → SmoothRiemannianMetric I M) (x₀ x : M) (t : ℝ) :
    chartDensityFamily (I := I) g_fam x₀ x t =
      chartDensity (I := I) (g_fam t) x₀ x := rfl

lemma chartDensityFamily_eq_sqrt_det
    (g_fam : ℝ → SmoothRiemannianMetric I M) (x₀ x : M) (t : ℝ) :
    chartDensityFamily (I := I) g_fam x₀ x t =
      Real.sqrt (chartGramMatrixFamily (I := I) g_fam x₀ x t).det := rfl

theorem hasDerivAt_chartDensityFamily_eq_half_trace_inv_mul
    (g_fam : ℝ → SmoothRiemannianMetric I M) (x₀ : M) (t : ℝ) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (Gprime : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
    (hEntries : ∀ i j : Fin (Module.finrank ℝ E),
      HasDerivAt (fun s => chartGramMatrixFamily (I := I) g_fam x₀ x s i j)
        (Gprime i j) t) :
    HasDerivAt
      (fun s => chartDensityFamily (I := I) g_fam x₀ x s)
      ((1 / 2) *
        trace ((chartGramMatrixFamily (I := I) g_fam x₀ x t)⁻¹ * Gprime) *
        Real.sqrt (chartGramMatrixFamily (I := I) g_fam x₀ x t).det) t := by
  have hpos : 0 < (chartGramMatrixFamily (I := I) g_fam x₀ x t).det := by
    simpa [chartGramMatrixFamily_apply] using
      CalabiYau.Tensor.Coordinates.chartGramMatrix_det_pos (I := I) (g_fam t) x₀ hx
  have hderiv := hasDerivAt_sqrt_det_eq_half_trace_inv_mul
    (G := chartGramMatrixFamily (I := I) g_fam x₀ x)
    (G' := Gprime) (t := t) hEntries hpos
  have hfun :
      (fun s => chartDensityFamily (I := I) g_fam x₀ x s)
        = (fun s => Real.sqrt (chartGramMatrixFamily (I := I) g_fam x₀ x s).det) := by
    funext s
    exact chartDensityFamily_eq_sqrt_det (I := I) g_fam x₀ x s
  rw [hfun]
  exact hderiv

end ChartDensityFamily

variable (I) in
def traceTimeDerivMetric
    (g_fam : ℝ → SmoothRiemannianMetric I M) (t : ℝ) (x : M) : ℝ :=
  Matrix.trace ((CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam t) x x)⁻¹ *
    (Matrix.of fun i j =>
      deriv (fun s => CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) x x i j) t))

lemma traceTimeDerivMetric_eq
    (g_fam : ℝ → SmoothRiemannianMetric I M) (t : ℝ) (x : M) :
    traceTimeDerivMetric (I := I) g_fam t x =
      Matrix.trace ((CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam t) x x)⁻¹ *
        (Matrix.of fun i j =>
          deriv (fun s => CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) x x i j) t)) := rfl

theorem continuousOn_deriv_of_hasDerivAt_eq_continuousOn
    {α : Type*} [TopologicalSpace α]
    {S : Set (ℝ × α)} {f D : ℝ → α → ℝ}
    (hderiv :
      ∀ p ∈ S, HasDerivAt (fun t : ℝ => f t p.2) (D p.1 p.2) p.1)
    (hD : ContinuousOn (fun p : ℝ × α => D p.1 p.2) S) :
    ContinuousOn
      (fun p : ℝ × α => deriv (fun t : ℝ => f t p.2) p.1)
      S := by
  have h_eq : Set.EqOn
      (fun p : ℝ × α => deriv (fun t : ℝ => f t p.2) p.1)
      (fun p : ℝ × α => D p.1 p.2) S := by
    intro p hp
    exact (hderiv p hp).deriv
  exact hD.congr h_eq

theorem MetricFamilyRegularAt.of_chartGram_timeDeriv
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t₀ : ℝ}
    (h :
      ∀ x₀ i j, ∃ D : ℝ → M → ℝ,
        (∀ t x,
          x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet →
            HasDerivAt
              (fun s : ℝ => CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) x₀ x i j)
              (D t x) t) ∧
        ContinuousOn
          (fun p : ℝ × M =>
            CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) x₀ p.2 i j)
          (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) ∧
        ContinuousOn
          (fun p : ℝ × M => D p.1 p.2)
          (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    MetricFamilyRegularAt (I := I) g_fam t₀ := by
  refine
    { hasDerivAt_chartGramMatrix := ?_
      continuousOn_chartGramMatrix := ?_
      continuousOn_deriv_chartGramMatrix := ?_ }
  · intro x₀ i j x hx t
    rcases h x₀ i j with ⟨D, hD_deriv, -, -⟩
    have hderiv := hD_deriv t x hx
    exact hderiv.congr_deriv hderiv.deriv.symm
  · intro x₀ i j
    rcases h x₀ i j with ⟨D, -, hG_cont, -⟩
    exact hG_cont
  · intro x₀ i j
    rcases h x₀ i j with ⟨D, hD_deriv, -, hD_cont⟩
    refine continuousOn_deriv_of_hasDerivAt_eq_continuousOn
      (S := Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)
      (f := fun t x => CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam t) x₀ x i j)
      (D := D) ?_ hD_cont
    intro p hp
    exact hD_deriv p.1 p.2 hp.2

theorem FunctionRegularAt_const (c : ℝ) (t₀ : ℝ) :
    FunctionRegularAt (fun _ : ℝ => fun _ : M => c) t₀ := by
  refine
    { hasDerivAt_time := ?_
      continuous_joint := ?_
      continuous_deriv_joint := ?_ }
  · intro _ t
    have hderiv : deriv (fun _ : ℝ => c) t = 0 :=
      (hasDerivAt_const (x := t) (c := c)).deriv
    simpa [hderiv] using (hasDerivAt_const (x := t) (c := c))
  · simpa using (continuous_const : Continuous (fun _ : ℝ × M => c))
  · have hfun :
        (fun p : ℝ × M => deriv (fun _ : ℝ => c) p.1) =
          fun _ : ℝ × M => (0 : ℝ) := by
      funext p
      exact (hasDerivAt_const (x := p.1) (c := c)).deriv
    simpa [hfun] using (continuous_const : Continuous (fun _ : ℝ × M => (0 : ℝ)))

theorem FunctionRegularAt_one (t₀ : ℝ) :
    FunctionRegularAt (fun _ : ℝ => fun _ : M => (1 : ℝ)) t₀ :=
  FunctionRegularAt_const (M := M) 1 t₀
end CalabiYau.RiemannianVolume
