module

public import CalabiYau.MongeAmpere.Continuity.Openness.C2Approximation.Smoothing

/-!
# Uniform second-jet convergence implies chartwise C² bounds

For exponent zero, `HolderBoundOn` is the sup bounds through order two together with an oscillation
bound on the second derivative.  Uniform convergence of the jets therefore gives precisely the
parent's chartwise `HolderBoundOn 2 0` convergence.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [T2Space M] [CompactSpace M]

omit [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M] in
/-- Uniform convergence of the coordinate jets of a smooth sequence through order two implies
convergence in the finite-cover `HolderBoundOn 2 0` topology. -/
theorem ChartwiseC2SmoothingData.eventually_holderBoundOn
    {φ : M → ℝ} (A : ChartwiseC2SmoothingData φ) :
    ∀ ε : ℝ≥0, 0 < ε →
      ∃ N, ∀ j, N ≤ j → ∀ i,
        HolderBoundOn 2 0 ε (A.cover.piece i)
          ((A.approximation j - φ) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
            (A.cover.base i)).symm) := by
  intro ε hε
  let δ : ℝ≥0 := ε / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    exact (div_pos hε (by norm_num : (0 : ℝ≥0) < 2))
  obtain ⟨N, hN⟩ := A.jetsTendsto δ hδ
  refine ⟨N, ?_⟩
  intro j hj i
  let f : EuclideanSpace ℂ (Fin n) → ℝ :=
    (A.approximation j - φ) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      (A.cover.base i)).symm
  change (∀ r ≤ 2, ∀ z ∈ A.cover.piece i, ‖iteratedFDeriv ℝ r f z‖ ≤ ε) ∧
    HolderOnWith ε 0 (iteratedFDeriv ℝ 2 f) (A.cover.piece i)
  have hjet : ∀ r ≤ 2, ∀ z ∈ A.cover.piece i,
      ‖iteratedFDeriv ℝ r f z‖ ≤ (δ : ℝ) := by
    intro r hr z hz
    exact hN j hj i r hr z hz
  have hδle : (δ : ℝ) ≤ (ε : ℝ) := by
    dsimp [δ]
    norm_num
  refine ⟨?_, ?_⟩
  · intro r hr z hz
    exact (hjet r hr z hz).trans hδle
  · intro z hz w hw
    have hzb := hjet 2 le_rfl z hz
    have hwb := hjet 2 le_rfl w hw
    change edist (iteratedFDeriv ℝ 2 f z) (iteratedFDeriv ℝ 2 f w) ≤
      (↑ε : ENNReal) * edist z w ^ (0 : ℝ)
    calc
      _ = ENNReal.ofReal (dist (iteratedFDeriv ℝ 2 f z) (iteratedFDeriv ℝ 2 f w)) :=
        edist_dist _ _
      _ ≤ ENNReal.ofReal
          (‖iteratedFDeriv ℝ 2 f z‖ + ‖iteratedFDeriv ℝ 2 f w‖) :=
        ENNReal.ofReal_le_ofReal (dist_le_norm_add_norm _ _)
      _ ≤ ENNReal.ofReal ((δ : ℝ) + (δ : ℝ)) :=
        ENNReal.ofReal_le_ofReal (add_le_add hzb hwb)
      _ = (↑ε : ENNReal) := by
        dsimp [δ]
        norm_num
      _ = (↑ε : ENNReal) * edist z w ^ (0 : ℝ) := by
        rw [ENNReal.rpow_zero, mul_one]

end KahlerForm
