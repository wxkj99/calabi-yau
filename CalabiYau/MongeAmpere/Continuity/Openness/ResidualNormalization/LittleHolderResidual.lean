module

public import CalabiYau.MongeAmpere.Continuity.Openness.PotentialStability
public import CalabiYau.MongeAmpere.Continuity.Openness.ResidualNormalization.BoundedResidualCentering

/-!
# Realizing the centered residual in the little-Hölder carrier

Construct the residual on a positive ball in the fixed `C²` chart carrier, including its
mean-zero projection, in the actual little-`C^{0,α}` completion.  The construction is only required
on that ball; its values outside the ball are immaterial to the local implicit-function argument.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology
open Set MeasureTheory

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [CompactSpace M] [ConnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
private theorem c2Potential_perturb_of_sum (ω₀ : KahlerForm n M) (φ u : M → ℝ)
    (hφ : ω₀.IsPotential φ) (hφu : ω₀.IsC2Potential (φ + u)) :
    (ω₀.perturb φ hφ).IsC2Potential u := by
  have hφ2 : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 φ :=
    hφ.1.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hu2 : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 u := by
    have hsub := hφu.1.sub hφ2
    have heq : (φ + u) - φ = u := by
      funext x
      dsimp
      ring
    rw [← heq]
    exact hsub
  refine ⟨hu2, ?_⟩
  have hform : (ω₀.perturb φ hφ).toFormField + mddbar n u =
      ω₀.toFormField + mddbar n (φ + u) := by
    change (ω₀.toFormField + mddbar n φ) + mddbar n u =
      ω₀.toFormField + mddbar n (φ + u)
    calc
      _ = ω₀.toFormField + (mddbar n φ + mddbar n u) := by rw [add_assoc]
      _ = _ := by rw [← mddbar_add_of_contMDiff_two hφ2 hu2]
  change ((ω₀.perturb φ hφ).toFormField + mddbar n u).IsPositive
  rw [hform]
  exact hφu.2

/-- The local Banach-valued realization of the centered residual, before using mass normalization.
Its target is the mean-zero little-Hölder carrier itself, not merely the space of continuous
functions. -/
structure CenteredPathResidualCarrierData (ω₀ : KahlerForm n M) (F : M → ℝ)
    (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F)
    (t : ℝ) (φ : M → ℝ)
    (hsol : ω₀.SolvesMongeAmpere (fun x ↦ t * F x + ω₀.pathConstant F t) φ)
    (α : ℝ≥0) [P : ContinuityHolderPair (ω₀.perturb φ hsol.1) α] where
  radius : ℝ
  radius_pos : 0 < radius
  /-- Every potential in the residual ball preserves positivity, so its logarithmic
  Monge–Ampère density is defined throughout the domain used by the implicit-function theorem. -/
  radius_potential : ∀ (u : P.C2), ‖u‖ < radius →
    (ω₀.perturb φ hsol.1).IsC2Potential (P.evalC2 u)
  radius_potential_sum : ∀ (u : P.C2), ‖u‖ < radius →
    ω₀.IsC2Potential (φ + P.evalC2 u)
  residual : P.C2 × ℝ → P.C0
  eval_residual : ∀ (u : P.C2) (δ : ℝ), ‖u‖ < radius → ∀ x,
    P.evalC0 (residual (u, δ)) x =
      centeredContinuityPathResidual ω₀ F t φ hsol (P.evalC2 u) δ x
  residual_base : residual (0, 0) = 0

/-- Realize the centered log-determinant residual in the little `C^{0,α}` target on a positive
`C^{2,α}` ball.  The statement includes the fixed-cover construction and the exact evaluation
identity needed for the openness argument. -/
theorem exists_centeredPathResidualCarrierData (ω₀ : KahlerForm n M) (F : M → ℝ)
    (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F)
    (t : ℝ) (φ : M → ℝ)
    (hsol : ω₀.SolvesMongeAmpere (fun x ↦ t * F x + ω₀.pathConstant F t) φ)
    (α : ℝ≥0) (hα₀ : 0 < α) (hα₁ : α < 1)
    [P : ContinuityHolderPair (ω₀.perturb φ hsol.1) α] :
    Nonempty (CenteredPathResidualCarrierData ω₀ F hF t φ hsol α) := by
  obtain ⟨radius, hradius, hpositive⟩ :=
    exists_c2Potential_radius ω₀ (ω₀.perturb φ hsol.1) α φ hsol.1 rfl
  obtain ⟨Q⟩ :=
    exists_littleHolderUncenteredResidual ω₀ F hF t φ hsol α hα₀ hα₁
      radius hradius hpositive
  obtain ⟨residual, heval, hbase⟩ :=
    exists_centeredResidualProjection ω₀ F hF t φ hsol α hα₀ hα₁ radius Q
  refine ⟨{
    radius := radius
    radius_pos := hradius
    radius_potential := fun u hu =>
      c2Potential_perturb_of_sum ω₀ φ (P.evalC2 u) hsol.1 (hpositive u hu)
    radius_potential_sum := hpositive
    residual := residual
    eval_residual := heval
    residual_base := hbase
  }⟩

end KahlerForm
