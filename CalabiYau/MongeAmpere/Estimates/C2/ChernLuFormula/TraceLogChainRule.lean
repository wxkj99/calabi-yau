module

public import CalabiYau.Geometry.Kahler.Laplacian
public import CalabiYau.Geometry.Complex.Forms.OneOne
public import CalabiYau.MongeAmpere.Estimates.C2.ChernLuFormula.NormalFrameJets
import CalabiYau.MongeAmpere.Estimates.C2.LogarithmicLaplacian
import CalabiYau.MongeAmpere.Estimates.C2.RelativeTraceRegularity

/-!
# Scalar logarithm chain rule for the relative trace

The Chern–Lu computation first expands the unlogged trace and its Hermitian gradient, then applies
the scalar identity for the logarithm.  This theorem isolates that calculus step from both coordinate
expansions.  For a positive trace `u`, the identity is
`Δ log u = (Δu)/u - |∂u|²/u²`; the denominators are retained exactly as real quotients, matching the
normal-frame statements.

The trace is positive when `n > 0` because both Kähler forms are positive.  In dimension zero it is
the constant zero function, and both Laplacians and gradient norms vanish; the quotient convention
still makes the displayed identity true.  Thus no hidden `NeZero n` hypothesis is imposed on this
identity.  In dimension one the formula specializes to the ordinary one-variable logarithmic
chain rule with the complex Kähler Laplacian normalization.

No curvature, diagonalization, or Kähler symmetry is used here.  Those facts enter only in the
separate unlogged trace and normalized gradient expansions.  This keeps the declaration
small and lets the final theorem perform only substitution and scalar algebra.
-/

@[expose] public section

open scoped Manifold ContDiff ComplexOrder MatrixOrder
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

/-- Apply the logarithm chain rule to the intrinsic relative trace. -/
theorem normalFrame_log_relative_trace_chain_rule
    (ω₀ ω₁ : KahlerForm n M) (x : M) :
    ω₁.laplacian (fun y ↦ Real.log (relTrace (ω₀ y) (ω₁ y))) x =
      (ω₁.laplacian (fun y ↦ relTrace (ω₀ y) (ω₁ y)) x) /
          (relTrace (ω₀ x) (ω₁ x)) -
        (ω₁.gradNormSq (fun y ↦ relTrace (ω₀ y) (ω₁ y)) x) /
          (relTrace (ω₀ x) (ω₁ x)) ^ 2 := by
  by_cases hn : n = 0
  · subst n
    have htrace (y : M) (α : EuclideanSpace ℂ (Fin 0) [⋀^Fin 2]→L[ℝ] ℝ) :
        relTrace (ω₀ y) α = 0 := by
      simp [ContinuousAlternatingMap.relTrace, Matrix.trace]
    have hfun : (fun y ↦ relTrace (ω₀ y) (ω₁ y)) = fun _ : M ↦ 0 := by
      funext y
      exact htrace y (ω₁ y)
    rw [hfun]
    simp [KahlerForm.laplacian, KahlerForm.gradNormSq,
      ContinuousAlternatingMap.relTrace, Matrix.trace]
  · let : NeZero n := ⟨hn⟩
    let f : M → ℝ := fun y ↦ relTrace (ω₀ y) (ω₁ y)
    have hf : ContDiffAt ℝ 2
        ((fun y ↦ relTrace (ω₀ y) (ω₁ y)) ∘
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) :=
      contDiffAt_relativeTrace_inChart ω₀ ω₁ x
    have hpos : relTrace (ω₀ x) (ω₁ x) ≠ 0 :=
      ne_of_gt (ContinuousAlternatingMap.relTrace_pos
        (ω₀.isPositive x) (ω₁.isPositive x))
    simpa [f] using
      (laplacian_log_of_contDiffAt_inChart (ω₀ := ω₁) (f := f) x
        (by simpa [f] using hf) hpos)

end KahlerForm
