module

public import CalabiYau.Geometry.Kahler.Curvature.Chart

/-!
# Curvature and the antiholomorphic derivative of the connection on an open chart

The Chern connection identity `∂̄Γ = −g⁻¹R` holds in the germ of a Kähler metric,
not just for globally smooth matrix functions on the entire coordinate model.
See Székelyhidi, *An Introduction to Extremal Kähler Metrics*, §3.3,
proof of Lemma 3.9, p. 48 of the author's PDF (book p. 45).
-/

public section

open scoped Manifold ContDiff

namespace KahlerForm

variable {n : ℕ}

/-- The local form of `chartChristoffel_bar_eq_curvature`. On an open chart target
`U`, it is enough for the metric coefficients to be smooth *on `U`*, for the
Kähler derivative symmetry to hold there, and for the metric to be invertible
at the point of evaluation. The inverse entry `[l,i]` contracts the
antiholomorphic metric column; the `∂̄` derivative includes its usual `1/2`.
No global smoothness outside `U` is assumed. -/
theorem chartChristoffel_bar_eq_curvature_local
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (U : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U)
    (hg : ∀ a b, ContDiffOn ℝ ∞ (fun w => g w a b) U)
    (hK : ∀ w ∈ U, ∀ a b c,
      chartPartialZComplex (fun v => g v b c) w a =
        chartPartialZComplex (fun v => g v a c) w b)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U)
    (hdet : IsUnit (g z).det) (i j k q : Fin n) :
    chartPartialBarComplex
      (fun w => ∑ l, (g w)⁻¹ l i * chartPartialZComplex (fun v => g v k l) w j) z q =
      -(∑ l, (g z)⁻¹ l i * chartCurvature g z j q k l) := by
  have _hK := hK
  have hgAt (a b : Fin n) : ContDiffAt ℝ ∞ (fun w => g w a b) z :=
    (hg a b).contDiffAt (hU.mem_nhds hz)
  exact chartChristoffel_bar_eq_curvature_at g z hgAt hdet i j k q

end KahlerForm
