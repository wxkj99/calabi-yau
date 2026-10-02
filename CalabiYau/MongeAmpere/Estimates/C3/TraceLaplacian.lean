module

public import CalabiYau.MongeAmpere.Estimates.C3.CalabiEnergy
import CalabiYau.MongeAmpere.Estimates.C3.TraceLaplacian.Refined.EnergyLowerBound
import CalabiYau.MongeAmpere.Estimates.C3.TraceLaplacian.Refined.PotentialError
import CalabiYau.MongeAmpere.Estimates.C3.TraceLaplacian.Refined.ReferenceCurvatureError
import CalabiYau.MongeAmpere.Estimates.C3.TraceLaplacian.Refined.TraceRegularity

/-!
# Refined Laplacian inequality for the relative trace

The Aubin–Yau coordinate computation before discarding its positive third-derivative term gives
`Δ_{ωφ} tr_{ω₀} ωφ ≥ c |Γ(gφ)-Γ(g₀)|²_{gφ} - C` under two-sided metric comparison. The
remaining curvature and `∂∂̄G` terms are uniformly bounded. See Székelyhidi, §3.3,
Lemma 3.10, pp. 45–46, together with §3.2, Lemma 3.8.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal
open ContinuousAlternatingMap

namespace KahlerForm

/-- A normal-frame change of basis preserves the contracted complex trace.
The normalization hypothesis is `Jᵀ g J* = 1`; no positivity or Hermitian
assumptions beyond invertibility are needed for this algebraic identity. -/
private theorem trace_of_normalized_pullback {n : ℕ}
    (J g B : Matrix (Fin n) (Fin n) ℂ) (hJ : IsUnit J.det)
    (hnormal : J.transpose * g * J.map star = 1) :
    RCLike.re ((g⁻¹ * B).trace) =
      RCLike.re ((J.transpose * B * J.map star).trace) := by
  let hJU : IsUnit J := (Matrix.isUnit_iff_isUnit_det J).2 hJ
  let : Invertible J := Classical.choice hJU.nonempty_invertible
  have hmul0 := congrArg
    (fun A : Matrix (Fin n) (Fin n) ℂ => J.transpose⁻¹ * A) hnormal
  have hmul : g * J.map star = J.transpose⁻¹ := by
    simpa [Matrix.mul_assoc] using hmul0
  have hRight : g * (J.map star * J.transpose) = 1 := by
    calc
      g * (J.map star * J.transpose) = (g * J.map star) * J.transpose := by rw [Matrix.mul_assoc]
      _ = J.transpose⁻¹ * J.transpose := by rw [hmul]
      _ = 1 := by
        simp
  have hginv : g⁻¹ = J.map star * J.transpose := Matrix.inv_eq_right_inv hRight
  rw [hginv]
  rw [← Matrix.trace_mul_cycle J.transpose B (J.map star)]

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

omit [T2Space M] in
/-- The positive third-derivative term in the Laplacian of the trace controls the Calabi energy.
The scalar trace is smooth and nonnegative for each solution, including in dimension zero. -/
theorem exists_uniform_relTrace_laplacian_calabi_lower (ω₀ : KahlerForm n M)
    (S : Set ((M → ℝ) × (M → ℝ)))
    (hS : ∀ p ∈ S, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ p.1 ∧
      ω₀.SolvesMongeAmpere p.1 p.2)
    (hG : HolderBoundedInCharts (EuclideanSpace ℂ (Fin n)) 3 0 (Prod.fst '' S))
    (hMetric : ∃ B : ℝ, 0 < B ∧ ∀ p ∈ S, ∀ x,
      relTrace (ω₀ x) (ω₀ x + mddbar n p.2 x) ≤ B ∧
      relTrace (ω₀ x + mddbar n p.2 x) (ω₀ x) ≤ B) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
      ∀ (p : (M → ℝ) × (M → ℝ)) (hp : p ∈ S),
        ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
          (fun x ↦ relTrace (ω₀ x) (ω₀ x + mddbar n p.2 x)) ∧
        (∀ x, 0 ≤ relTrace (ω₀ x) (ω₀ x + mddbar n p.2 x)) ∧
        ∀ x, c * calabiEnergy ω₀ p.2 x - C ≤
          (ω₀.perturb p.2 (hS p hp).2.1).laplacian
            (fun y ↦ relTrace (ω₀ y) (ω₀ y + mddbar n p.2 y)) x := by
  obtain ⟨B, hB, hBound⟩ := hMetric
  obtain ⟨A, hA, hPot⟩ :=
    exists_uniform_c3RefinedTrace_referencePotentialLaplacian_bound ω₀ S (fun p hp ↦ (hS p hp).1) hG
  obtain ⟨R, hR, hCurv⟩ := c3RefinedTrace_exists_uniform_referenceCurvature_error_bound ω₀ B hB
  refine ⟨B⁻¹, A + R, inv_pos.mpr hB, add_nonneg hA hR, ?_⟩
  intro p hp
  have hsol := (hS p hp).2
  have hreg := c3RefinedTrace_relTrace_perturb_smooth_nonneg ω₀ p.1 p.2 hsol
  refine ⟨hreg.1, hreg.2, ?_⟩
  intro x
  have hb := hBound p hp x
  have henergy := c3RefinedTrace_relTrace_laplacian_energy_with_signed_errors
    ω₀ p.1 p.2 (hS p hp).1 hsol x B hB hb.1 hb.2
  have hpotential := (abs_le.mp (hPot p hp x)).1
  have hcurvature := (abs_le.mp (hCurv p.1 p.2 hsol x hb.1 hb.2)).1
  linarith

end KahlerForm
