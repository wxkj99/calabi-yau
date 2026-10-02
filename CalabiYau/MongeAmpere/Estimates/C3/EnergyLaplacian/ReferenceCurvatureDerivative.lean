module

public import CalabiYau.MongeAmpere.Estimates.C3.CalabiEnergy
public import CalabiYau.Geometry.Kahler.Curvature.Chart
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceCurvatureDerivative.CovariantPullback
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceCurvatureDerivative.FixedChartBound
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceCurvatureDerivative.CompactCover
import CalabiYau.Geometry.Kahler.Curvature.ReferenceBound.TransitionFrame

/-!
# Fixed reference-curvature derivative in Calabi's Bochner formula

The derivative `∇⁰ R(g₀)` is a fixed smooth tensor on the compact Kähler
manifold. It has a uniform norm in reference-orthonormal frames, independently
of the family of perturbed metrics. Székelyhidi, §3.3, proof of Lemma 3.9,
printed pp. 44–45 (cached GSM152 PDF physical pages 62–63), uses this
separately from the bound for `R(g₀)` itself. Its component norm is uniformly
bounded in reference-orthonormal frames.
-/

@[expose] public section

open scoped Manifold ContDiff

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

/-- The holomorphic covariant derivative of the fixed reference curvature,
`(∇⁰ₛR⁰)_{p q̄ j k̄}`. The holomorphic lower indices `p,j` each receive a
connection correction; the antiholomorphic indices do not. -/
noncomputable def c3ReferenceCurvatureCovariantDerivativeInChart
    (ω₀ : KahlerForm n M) (x : M) (z : EuclideanSpace ℂ (Fin n))
    (s p q j k : Fin n) : ℂ :=
  let g₀ : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun w ↦ ω₀.metricInChart x w
  c3PartialZ (fun w ↦ chartCurvature g₀ w p q j k) z s -
    ∑ a : Fin n, c3ChristoffelInChart g₀ z a s p * chartCurvature g₀ z a q j k -
    ∑ a : Fin n, c3ChristoffelInChart g₀ z a s j * chartCurvature g₀ z p q a k

omit [T2Space M] in
/-- Uniform bound for the fifth-order components of `∇⁰R(g₀)` in all
reference-orthonormal frames. The chart at each point may vary; the
covariant derivative transforms tensorially, so the compactness argument is
on the unitary frame bundle rather than on unnormalized chart components. -/
theorem exists_uniform_c3ReferenceCurvatureCovariantDerivative_bound
    (ω₀ : KahlerForm n M) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (x : M) (P : Matrix (Fin n) (Fin n) ℂ),
      Matrix.transpose P *
          ω₀.metricInChart x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) *
          P.map star = 1 →
        ∀ s p q j k : Fin n,
          ‖∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
            ∑ d : Fin n, ∑ e : Fin n,
              P a s * P b p * star (P c q) * P d j * star (P e k) *
                c3ReferenceCurvatureCovariantDerivativeInChart ω₀ x
                  (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) a b c d e‖ ≤ A := by
  obtain ⟨A, hA, hglobal⟩ := exists_uniform_c3_curvature_derivative_bound_of_local ω₀ (by
    intro x
    obtain ⟨U, hU, hx, hsource, B, hB, hbound⟩ :=
      exists_local_fixed_chart_c3_curvature_derivative_bound ω₀ x
    refine ⟨U, hU, hx, B, hB, ?_⟩
    intro y hy P hP s p q j k
    obtain ⟨V, hV⟩ := ω₀.exists_reference_chart_overlap x y (hsource hy)
    have hQ := ω₀.referenceFrame_transition x y V hV P hP
    have htransport := c3_reference_curvature_derivative_frame_transition ω₀ x y V hV P
    exact (congrArg (fun T => ‖T s p q j k‖) htransport).trans_le
      (hbound y hy (referenceTransitionMatrix x y * P) hQ s p q j k))
  refine ⟨A, hA, ?_⟩
  intro x P hP s p q j k
  simpa only [c3FiveSlotFrameContraction, c3CovariantFourTensorZJet,
    c3ReferenceCurvatureCovariantDerivativeInChart, c3PartialZ, chartPartialZComplex]
    using hglobal x P hP s p q j k

end KahlerForm
