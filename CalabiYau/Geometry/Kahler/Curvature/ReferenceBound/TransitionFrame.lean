module

public import CalabiYau.Geometry.Kahler.Curvature.ReferenceBound.ChartOverlap

/-!
# Transfer a reference curvature frame between holomorphic charts

At `y` in the chart centered at `x`, the Jacobian below sends vectors from the chart centered
at `y` into the chart centered at `x`.  The Hermitian metric transforms by conjugate congruence;
the resulting transported frame is again orthonormal. Nonlinear chart changes are allowed.
-/

@[expose] public section

open scoped Manifold ContDiff ComplexOrder MatrixOrder

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

set_option maxHeartbeats 500000 in
/-- A frame orthonormal in the chart at `y` remains orthonormal after transport by the
holomorphic chart-transition Jacobian to the chart at `x`. -/
theorem referenceFrame_transition (ω₀ : KahlerForm n M) (x y : M)
    (U : Set (EuclideanSpace ℂ (Fin n))) (hU : ω₀.IsReferenceChartOverlap x y U)
    (P : Matrix (Fin n) (Fin n) ℂ)
    (hP : IsReferenceOrthonormalFrame ω₀ y P) :
    let Q := referenceTransitionMatrix x y * P
    Q.transpose * ω₀.metricInChart x
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y) * Q.map star = 1 := by
  dsimp
  let z := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y y
  have hz : z ∈ U := hU.2.1
  have hmetric := hU.2.2.2.2.2.2 z hz
  have hP' : P.transpose * ω₀.metricInChart y
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y y) * P.map star = 1 := by
    change P.transpose * ω₀.metricInChart y
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y y) * P.map star = 1 at hP
    exact hP
  have hcenter : referenceChartTransition x y z =
      extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y := by
    simp [z, referenceChartTransition]
  rw [hcenter] at hmetric
  have hmetric' : ω₀.metricInChart y z =
      (referenceTransitionMatrix x y).transpose *
        ω₀.metricInChart x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y) *
          (referenceTransitionMatrix x y).map star := by
    change ω₀.metricInChart y z =
      (referenceTransitionMatrix x y).transpose *
        ω₀.metricInChart x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y) *
          (referenceTransitionMatrix x y).map star at hmetric
    exact hmetric
  have hPz : P.transpose * ω₀.metricInChart y z * P.map star = 1 := by
    simpa [z] using hP'
  have hmetricAssoc : (referenceTransitionMatrix x y).transpose *
      (ω₀.metricInChart x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y) *
        (referenceTransitionMatrix x y).map star) = ω₀.metricInChart y z := by
    simpa only [Matrix.mul_assoc] using hmetric'.symm
  have hmap : (referenceTransitionMatrix x y * P).map star =
      (referenceTransitionMatrix x y).map star * P.map star :=
    Matrix.map_mul (f := starRingEnd ℂ) (L := referenceTransitionMatrix x y) (M := P)
  calc
    (referenceTransitionMatrix x y * P).transpose *
        ω₀.metricInChart x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y) *
        (referenceTransitionMatrix x y * P).map star =
      P.transpose * ((referenceTransitionMatrix x y).transpose *
        ω₀.metricInChart x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y) *
        (referenceTransitionMatrix x y).map star) * P.map star := by
        rw [Matrix.transpose_mul, hmap]
        simp only [Matrix.mul_assoc]
    _ = P.transpose * ω₀.metricInChart y z * P.map star := by
      simpa only [Matrix.mul_assoc] using
        congrArg (fun g => P.transpose * g * P.map star) hmetricAssoc
    _ = 1 := hPz

end KahlerForm
