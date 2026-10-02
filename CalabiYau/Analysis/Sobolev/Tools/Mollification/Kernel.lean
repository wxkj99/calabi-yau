-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Tools/Mollification/Kernel.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Tools.Translation

@[expose] public section

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open scoped ENNReal NNReal

namespace Sobolev

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

def mollifierBumpEps {ε : ℝ} (hε : 0 < ε) : ContDiffBump (0 : E) where
  rIn := ε / 2
  rOut := ε
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

def mollifierEps {ε : ℝ} (hε : 0 < ε) : E → ℝ :=
  (mollifierBumpEps (d := d) hε).normed (volume : Measure E)

theorem mollifierEps_smooth {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (mollifierEps (d := d) hε) :=
  (mollifierBumpEps (d := d) hε).contDiff_normed

theorem mollifierEps_continuous {ε : ℝ} (hε : 0 < ε) :
    Continuous (mollifierEps (d := d) hε) :=
  (mollifierBumpEps (d := d) hε).continuous_normed

theorem mollifierEps_nonneg {ε : ℝ} (hε : 0 < ε) (x : E) :
    0 ≤ mollifierEps (d := d) hε x :=
  (mollifierBumpEps (d := d) hε).nonneg_normed x

theorem mollifierEps_integral_eq_one {ε : ℝ} (hε : 0 < ε) :
    ∫ x, mollifierEps (d := d) hε x ∂(volume : Measure E) = 1 :=
  (mollifierBumpEps (d := d) hε).integral_normed

theorem mollifierEps_integrable {ε : ℝ} (hε : 0 < ε) :
    Integrable (mollifierEps (d := d) hε) (volume : Measure E) :=
  (mollifierBumpEps (d := d) hε).integrable_normed

theorem mollifierEps_compactSupport {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (mollifierEps (d := d) hε) :=
  (mollifierBumpEps (d := d) hε).hasCompactSupport_normed

theorem mollifierEps_support_eq {ε : ℝ} (hε : 0 < ε) :
    Function.support (mollifierEps (d := d) hε) = Metric.ball (0 : E) ε := by
  unfold mollifierEps
  simpa [mollifierBumpEps] using
    (mollifierBumpEps (d := d) hε).support_normed_eq (μ := volume)

theorem mollifierEps_support_subset_closedBall_eps
    {ε : ℝ} (hε : 0 < ε) :
    Function.support (mollifierEps (d := d) hε) ⊆ Metric.closedBall (0 : E) ε := by
  rw [mollifierEps_support_eq]
  exact Metric.ball_subset_closedBall

end Sobolev
