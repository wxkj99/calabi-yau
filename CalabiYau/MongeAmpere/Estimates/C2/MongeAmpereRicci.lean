module

public import CalabiYau.Geometry.Kahler.Laplacian
public import CalabiYau.Geometry.Kahler.Ricci
public import CalabiYau.Geometry.Complex.Forms.Positive
public import CalabiYau.MongeAmpere.Operator

/-!
# Ricci identity from the Monge–Ampère equation

Taking `i∂∂̄` of the logarithm of the volume-form equation gives
`Ric(ωφ) = Ric(ω₀) - i∂∂̄G`. Tracing this identity against `ω₀` supplies the Ricci term in the
Chern–Lu estimate.
-/

@[expose] public section

open scoped Manifold ContDiff
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

/-- The Ricci form of a Monge–Ampère solution is the reference Ricci form minus
`i∂∂̄G`; this is the differentiated equation in trace form. -/
theorem ricciForm_trace_perturb_eq_of_solvesMongeAmpere
    (ω₀ : KahlerForm n M) {G φ : M → ℝ}
    (hsol : ω₀.SolvesMongeAmpere G φ) (x : M) :
    relTrace (ω₀ x) ((ω₀.perturb φ hsol.1).ricciForm x) =
      relTrace (ω₀ x) (ω₀.ricciForm x) - ω₀.laplacian G x := by
  change ω₀.IsPotential φ ∧ (∀ y, ω₀.mongeAmpere φ y = Real.exp (G y)) at hsol
  obtain ⟨hφ, hMA⟩ := hsol
  have hdet : (fun y : M ↦ relDet (ω₀ y) ((ω₀.perturb φ hφ) y)) =
      fun y ↦ Real.exp (G y) := by
    funext y
    simpa [mongeAmpere, perturb_apply] using hMA y
  have hlog : (fun y : M ↦ Real.log (relDet (ω₀ y) ((ω₀.perturb φ hφ) y))) = G := by
    funext y
    rw [show relDet (ω₀ y) ((ω₀.perturb φ hφ) y) = Real.exp (G y) from
      congrFun hdet y]
    exact Real.log_exp _
  rw [ricciForm_eq_sub_mddbar ω₀ (ω₀.perturb φ hφ), hlog]
  simp [ContinuousAlternatingMap.relTrace_sub, laplacian]

end KahlerForm
