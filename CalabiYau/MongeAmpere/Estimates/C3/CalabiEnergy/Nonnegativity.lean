module

public import CalabiYau.MongeAmpere.Estimates.C3.CalabiEnergy.Basic

/-!
# Nonnegativity of the Calabi third-order energy

The energy is the squared norm of the connection-difference tensor for the positive perturbed
Hermitian metric. Positivity of the metric makes each tensor norm nonnegative, including in complex
dimension one; in dimension zero the contraction is the empty sum. See Székelyhidi, *An Introduction
to Extremal Kähler Metrics*, §3.3, equation (3.13), p. 45, and Yau 1978, §3.
The conclusion applies at every point because positivity is part of the potential data.
-/

@[expose] public section

open scoped Manifold ContDiff

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

omit [T2Space M] [CompactSpace M] in
/-- The Calabi connection-difference energy is pointwise nonnegative for every Kähler potential. -/
theorem calabiEnergy_nonneg (ω₀ : KahlerForm n M) {φ : M → ℝ}
    (hφ : ω₀.IsPotential φ) (x : M) : 0 ≤ calabiEnergy ω₀ φ x := by
  classical
  let : PartialOrder ℂ := Complex.partialOrder
  let z := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x
  let A : Matrix (Fin n) (Fin n) ℂ :=
    ω₀.metricInChart x z +
      complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z
  let T : Fin n → Fin n → Fin n → ℂ :=
    fun i j k ↦ connectionDifferenceInChart ω₀ φ x z i j k
  have hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by
    dsimp [z]
    exact (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).map_source
      (mem_extChartAt_source x)
  have hA : A.PosDef := by
    have hmetric := ω₀.metricInChart_perturb hφ x hz
    have hmetric' : A = (ω₀.perturb φ hφ).metricInChart x z := by
      dsimp [A]
      simpa [extChartAt] using hmetric.symm
    rw [hmetric']
    exact (ω₀.perturb φ hφ).posDef_metricInChart x hz
  let K : Matrix (Fin n × (Fin n × Fin n)) (Fin n × (Fin n × Fin n)) ℂ :=
    Matrix.kroneckerMap (· * ·) (Matrix.transpose A)
      (Matrix.kroneckerMap (· * ·) A⁻¹ A⁻¹)
  let v : Fin n × (Fin n × Fin n) → ℂ := fun p ↦ T p.1 p.2.1 p.2.2
  have hK : K.PosDef := by
    dsimp [K]
    exact hA.transpose.kronecker (hA.inv.kronecker hA.inv)
  have hq : 0 ≤ RCLike.re (dotProduct (star v) (Matrix.mulVec K v)) := by
    exact (RCLike.nonneg_iff.mp (hK.posSemidef.dotProduct_mulVec_nonneg v)).1
  have hcontract : dotProduct (star v) (Matrix.mulVec K v) =
      ∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
        A i a * A⁻¹ b j * A⁻¹ c k * T i j k * star (T a b c) := by
    simp [dotProduct, Matrix.mulVec, Matrix.kroneckerMap_apply,
      Matrix.transpose_apply, v, K, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro c hc
    ring
  rw [hcontract] at hq
  simpa [calabiEnergy, calabiEnergyInChart, z, A, T] using hq

end KahlerForm
