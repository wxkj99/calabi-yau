module

public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.LocalApproximation.CovarianceScaleBounds

@[expose] public section

open Set Filter Matrix
open scoped ContDiff NNReal Topology

namespace CalabiYau.Schauder

private theorem holder_distance_of_sup_lipschitz
    {E : Type*} [PseudoMetricSpace E] {f : E → ℝ} {α ε C : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1) (hε : 0 < ε) (hC : 0 ≤ C)
    (hSup : ∀ x, |f x| ≤ C * ε ^ α)
    (hLip : ∀ x y, |f x - f y| ≤ C * dist x y / ε ^ (1 - α)) :
    ∀ x y, |f x - f y| ≤ 2 * C * dist x y ^ α := by
  intro x y
  let d := dist x y
  by_cases hnear : d ≤ ε
  · by_cases hd : d = 0
    · have hzero : |f x - f y| = 0 := by
        have hle : |f x - f y| ≤ 0 := by simpa [d, hd] using hLip x y
        exact le_antisymm hle (abs_nonneg _)
      rw [hzero]
      positivity
    · have hdpos : 0 < d := lt_of_le_of_ne dist_nonneg (Ne.symm hd)
      have hpow : d ^ (1 - α) ≤ ε ^ (1 - α) :=
        Real.rpow_le_rpow dist_nonneg hnear (by linarith)
      have hd_eq : d = d ^ α * d ^ (1 - α) := by
        calc
          d = d ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = d ^ (α + (1 - α)) := by congr 1; ring
          _ = d ^ α * d ^ (1 - α) := by rw [Real.rpow_add hdpos]
      have hscale : d / ε ^ (1 - α) ≤ d ^ α := by
        rw [div_le_iff₀ (Real.rpow_pos_of_pos hε _)]
        calc
          d = d ^ α * d ^ (1 - α) := hd_eq
          _ ≤ d ^ α * ε ^ (1 - α) :=
            mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg dist_nonneg _)
      have hmain := hLip x y
      change |f x - f y| ≤ C * d / ε ^ (1 - α) at hmain
      calc
        |f x - f y| ≤ C * d / ε ^ (1 - α) := hmain
        _ ≤ C * d ^ α := by
          calc
            C * d / ε ^ (1 - α) = C * (d / ε ^ (1 - α)) := by ring
            _ ≤ C * d ^ α := mul_le_mul_of_nonneg_left hscale hC
        _ ≤ 2 * C * d ^ α := by
          have hn : 0 ≤ C * d ^ α := mul_nonneg hC (Real.rpow_nonneg dist_nonneg _)
          linarith
  · have hfar : ε ≤ d := le_of_not_ge hnear
    have hpow : ε ^ α ≤ d ^ α := Real.rpow_le_rpow (le_of_lt hε) hfar hα₀.le
    have habs : |f x - f y| ≤ |f x| + |f y| := by
      calc
        |f x - f y| = |f x + -f y| := by congr 1
        _ ≤ |f x| + |-f y| := abs_add_le _ _
        _ = |f x| + |f y| := by simp
    calc
      |f x - f y| ≤ |f x| + |f y| := habs
      _ ≤ C * ε ^ α + C * ε ^ α := add_le_add (hSup x) (hSup y)
      _ = 2 * C * ε ^ α := by ring
      _ ≤ 2 * C * d ^ α := by
        exact mul_le_mul_of_nonneg_left hpow (by positivity)

/-- Near/far interpolation turns the scale bounds into a vanishing order-zero Hölder bound. -/
theorem localMollificationCovariance_holderBound {n : ℕ}
    {α K : ℝ≥0} {U : Set (EuclideanSpace ℂ (Fin n))}
    {c : EuclideanSpace ℂ (Fin n)} {S η : ℝ}
    {f g : EuclideanSpace ℂ (Fin n) → ℂ}
    (hα₀ : 0 < α) (hα₁ : α < 1)
    (hS : 0 < S) (hη : 0 < η)
    (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U)
    (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (hH : HolderBoundOn 0 α K U f) :
    ∃ ε : ℕ → ℝ≥0, Tendsto ε atTop (𝓝 0) ∧
      ∀ m, HolderBoundOn 0 α (ε m) (Metric.ball c S)
        (fun z ↦ (localMollificationCovariance U hη m f g z).re) := by
  obtain ⟨δ, hδ, hSup, hLip⟩ := localMollificationCovariance_scaleBounds
    hS hη hCollar hf hg hH
  let B : ℝ≥0 := 2 + Real.toNNReal ((η / 4) ^ (α : ℝ))
  refine ⟨fun m ↦ B * δ m, ?_, ?_⟩
  · simpa using (tendsto_const_nhds.mul hδ :
      Tendsto (fun m ↦ B * δ m) atTop (𝓝 (B * 0)))
  · intro m
    have hRad : localKernelRadius η m ≤ η / 4 := by
      unfold localKernelRadius
      apply div_le_div_of_nonneg_left hη.le (by positivity)
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    have hPow : localKernelRadius η m ^ (α : ℝ) ≤
        Real.toNNReal ((η / 4) ^ (α : ℝ)) := by
      rw [Real.coe_toNNReal _ (Real.rpow_nonneg (by positivity) _)]
      exact Real.rpow_le_rpow (localKernelRadius_pos hη m).le hRad α.coe_nonneg
    have hB : (2 : ℝ) ≤ B := by
      dsimp [B]
      exact le_add_of_nonneg_right (Real.toNNReal _).coe_nonneg
    refine ⟨?_, ?_⟩
    · intro j hj z hz
      have hj0 : j = 0 := by omega
      subst j
      simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
      calc
        _ ≤ (δ m : ℝ) * localKernelRadius η m ^ (α : ℝ) := hSup m z hz
        _ ≤ (δ m : ℝ) * Real.toNNReal ((η / 4) ^ (α : ℝ)) :=
          mul_le_mul_of_nonneg_left hPow (δ m).coe_nonneg
        _ ≤ (B * δ m : ℝ≥0) := by
          dsimp [B]
          nlinarith [(δ m).coe_nonneg, (Real.toNNReal ((η / 4) ^ (α : ℝ))).coe_nonneg]
    · rw [iteratedFDeriv_zero_eq_comp]
      intro x hx y hy
      simp only [Function.comp_apply]
      rw [(continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℂ (Fin n)) ℝ).symm.edist_map]
      have hDist := holder_distance_of_sup_lipschitz
        (E := Metric.ball c S) (f := fun z ↦ (localMollificationCovariance U hη m f g z).re)
        (show 0 < (α : ℝ) by exact_mod_cast hα₀)
        (show (α : ℝ) < 1 by exact_mod_cast hα₁)
        (localKernelRadius_pos hη m) (δ m).coe_nonneg
        (fun z ↦ hSup m z z.2) (fun z w ↦ hLip m z z.2 w w.2)
        ⟨x, hx⟩ ⟨y, hy⟩
      change |(localMollificationCovariance U hη m f g x).re -
        (localMollificationCovariance U hη m f g y).re| ≤
        2 * (δ m : ℝ) * dist x y ^ (α : ℝ) at hDist
      have hReal : dist (localMollificationCovariance U hη m f g x).re
          (localMollificationCovariance U hη m f g y).re ≤
          (B * δ m : ℝ≥0) * dist x y ^ (α : ℝ) := by
        simp only [dist_eq_norm, Real.norm_eq_abs] at hDist ⊢
        exact hDist.trans (by
          simp only [NNReal.coe_mul]
          gcongr)
      rw [edist_nndist, edist_nndist,
        ← ENNReal.coe_rpow_of_nonneg _ α.coe_nonneg,
        ← ENNReal.coe_mul, ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
      simpa only [coe_nndist, NNReal.coe_mul, NNReal.coe_rpow] using hReal

end CalabiYau.Schauder
