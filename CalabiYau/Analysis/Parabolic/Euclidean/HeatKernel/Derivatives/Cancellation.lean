-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Parabolic/Euclidean/HeatKernel/Derivatives/Cancellation.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Parabolic.Euclidean.HeatKernel.Convolution.Lp
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Topology.MetricSpace.HolderNorm

@[expose] public section

-- and its private helpers occur in public declarations.

noncomputable section

open MeasureTheory Real
open scoped ENNReal RealInnerProductSpace NNReal

namespace HeatEquation

section ZeroMean

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V]

theorem integral_heatD2_zero {t : ℝ} (ht : 0 < t) (v w : V) :
    ∫ x : V, heatD2 t v w x = 0 := by
  have hder : ∀ x : V,
      fderiv ℝ (heatD1 t v) x w = heatD2 t v w x := by
    intro x
    rw [(heatD1_hasFDeriv v x).fderiv, heatD2Map_apply]
  have hparts :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := (volume : Measure V))
      (f := fun _ : V => (1 : ℝ)) (g := heatD1 t v) (v := w)
      (by
        have hzero :
            (fun x : V => (fderiv ℝ (fun _ : V => (1 : ℝ)) x) w *
              heatD1 t v x) = 0 := by
          funext x
          rw [fderiv_const_apply, zero_apply, zero_mul]
          rfl
        rw [hzero]
        exact integrable_zero V ℝ (volume : Measure V))
      (by simpa only [one_mul, hder] using heatD2_int ht v w)
      (by simpa only [one_mul] using heatD1_int ht v)
      (fun x _ => differentiableAt_const (𝕜 := ℝ) (x := x) (1 : ℝ))
      (fun x _ => (heatD1_hasFDeriv v x).differentiableAt)
  simpa only [one_mul, hder, fderiv_const_apply, zero_apply,
    zero_mul, integral_zero, neg_zero] using hparts

end ZeroMean

section HalfMoment

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V]

end HalfMoment

section CancelOperator

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def heatD2Cancel (t : ℝ) (v w : V) (f : V → F) (x : V) : F :=
  ∫ y : V, heatD2 t v w y • (f (x - y) - f x)

def heatD2Convolution (t : ℝ) (v w : V) (f : V → F) (x : V) : F :=
  ∫ y : V, heatD2 t v w y • f (x - y)

omit [Nontrivial V] [CompleteSpace F] in
theorem heatD2Convolution_comm (t : ℝ) (v w : V) (f : V → F) (x : V) :
    heatD2Convolution t v w f x = heatD2Convolution t w v f x := by
  unfold heatD2Convolution
  apply integral_congr_ae
  filter_upwards with y
  rw [heatD2_comm]

end CancelOperator

end HeatEquation
