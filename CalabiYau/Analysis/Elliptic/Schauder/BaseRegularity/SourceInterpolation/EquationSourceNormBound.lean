module

public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.SourceInterpolation.Basic

/-!
# Equation-based cutoff-source sup bound

Source: Constantin, *Schauder Estimates*, equation (9), p. 7, and localization p. 8.
The parent supplies the local product formula; this leaf controls its actual terms.
-/

@[expose] public section

open scoped NNReal ContDiff Topology

namespace CalabiYau.Schauder

/-- Use the equation, not a full-Hessian norm, to bound the localized source.
Coefficient agreement and the cutoff product rule establish `hformula` in the
parent. Outside the OPEN patch, including its boundary, `jet.second_support`
makes the matrix source zero; no global coefficient agreement is required. -/
theorem realBallCutoffJet_equation_source_norm_bound
    {n : ℕ} {α K K₀ K₁ G : ℝ≥0} {x : RealBallModel n} {δ : ℝ}
    {a : RealBallModel n → Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ}
    {u : RealBallModel n → ℝ} (hδ : 0 < δ)
    (coeff : RealBallCoefficientExtension a x δ) (jet : RealBallCutoffJet α x δ u)
    (hformula : ∀ y ∈ Metric.ball x δ,
      variableMatrixLap coeff.coefficient jet.second y =
        ballCutoff x (δ / 2) δ y * realBallSource a u y +
          realBallCutoffCommutator coeff u y)
    (hsource : ∀ y ∈ Metric.ball x δ, ‖realBallSource a u y‖ ≤ K₁)
    (hcoeff : ∀ i j y, y ∈ Metric.ball x δ → ‖coeff.coefficient i j y‖ ≤ K)
    (hu : ∀ y ∈ Metric.ball x δ, ‖u y‖ ≤ K₀)
    (hgrad : ∀ y ∈ Metric.ball x δ, ‖fderiv ℝ u y‖ ≤ G) :
    let hr : 0 ≤ δ / 2 := by positivity
    let hrR : δ / 2 < δ := by linarith
    let Mχ := ‖ballCutoffFDerivBoundedContinuousFunction x hr hrR‖₊
    let Mχ₂ := ‖ballCutoffFDeriv2BoundedContinuousFunction x hr hrR‖₊
    ‖variableMatrixLap coeff.coefficient jet.second‖ ≤
      ((K₁ + realBallSourcePairCount n * K * (2 * Mχ * G + Mχ₂ * K₀) : ℝ≥0) : ℝ) := by
  intro hr hrR Mχ Mχ₂
  classical
  let E := Fin n × Fin 2
  let dχ := ballCutoffFDerivBoundedContinuousFunction x hr hrR
  let dχ₂ := ballCutoffFDeriv2BoundedContinuousFunction x hr hrR
  rw [BoundedContinuousFunction.norm_le (by positivity)]
  intro y
  by_cases hy : y ∈ Metric.ball x δ
  · have hχmem := ballCutoff_mem_Icc x (δ / 2) δ y
    have hχnorm : ‖ballCutoff x (δ / 2) δ y‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg hχmem.1]
      exact hχmem.2
    have hχgrad : ∀ i : E,
        ‖ballCutoffFDeriv x (δ / 2) δ y (EuclideanSpace.basisFun E ℝ i)‖ ≤ Mχ := by
      intro i
      change ‖dχ y (EuclideanSpace.basisFun E ℝ i)‖ ≤ Mχ
      calc
        ‖dχ y (EuclideanSpace.basisFun E ℝ i)‖ ≤
            ‖dχ y‖ * ‖EuclideanSpace.basisFun E ℝ i‖ := (dχ y).le_opNorm _
        _ = ‖dχ y‖ := by rw [(EuclideanSpace.basisFun E ℝ).orthonormal.norm_eq_one i, mul_one]
        _ ≤ Mχ := by exact_mod_cast dχ.norm_coe_le_norm y
    have hχ₂grad : ∀ i j : E,
        ‖ballCutoffFDeriv2 x (δ / 2) δ y
          (EuclideanSpace.basisFun E ℝ i) (EuclideanSpace.basisFun E ℝ j)‖ ≤ Mχ₂ := by
      intro i j
      change ‖dχ₂ y (EuclideanSpace.basisFun E ℝ i) (EuclideanSpace.basisFun E ℝ j)‖ ≤ Mχ₂
      calc
        ‖dχ₂ y (EuclideanSpace.basisFun E ℝ i) (EuclideanSpace.basisFun E ℝ j)‖ ≤
            ‖dχ₂ y (EuclideanSpace.basisFun E ℝ i)‖ *
              ‖EuclideanSpace.basisFun E ℝ j‖ := (dχ₂ y (EuclideanSpace.basisFun E ℝ i)).le_opNorm _
        _ ≤ (‖dχ₂ y‖ * ‖EuclideanSpace.basisFun E ℝ i‖) *
              ‖EuclideanSpace.basisFun E ℝ j‖ := by
          gcongr
          exact (dχ₂ y).le_opNorm _
        _ = ‖dχ₂ y‖ := by
          rw [(EuclideanSpace.basisFun E ℝ).orthonormal.norm_eq_one i,
            (EuclideanSpace.basisFun E ℝ).orthonormal.norm_eq_one j]
          ring
        _ ≤ Mχ₂ := by exact_mod_cast dχ₂.norm_coe_le_norm y
    have hgrad : ∀ i : E,
        ‖fderiv ℝ u y (EuclideanSpace.basisFun E ℝ i)‖ ≤ G := by
      intro i
      calc
        ‖fderiv ℝ u y (EuclideanSpace.basisFun E ℝ i)‖ ≤
            ‖fderiv ℝ u y‖ * ‖EuclideanSpace.basisFun E ℝ i‖ :=
          (fderiv ℝ u y).le_opNorm _
        _ = ‖fderiv ℝ u y‖ := by
          rw [(EuclideanSpace.basisFun E ℝ).orthonormal.norm_eq_one i, mul_one]
        _ ≤ G := hgrad y hy
    have hcomm : ‖realBallCutoffCommutator coeff u y‖ ≤
        (realBallSourcePairCount n : ℝ) * K * (2 * Mχ * G + Mχ₂ * K₀) := by
      unfold realBallCutoffCommutator
      calc
        ‖∑ i : E, ∑ j : E,
            ((coeff.coefficient i j y * ballCutoffFDeriv x (δ / 2) δ y
                (EuclideanSpace.basisFun E ℝ i)) * fderiv ℝ u y
                  (EuclideanSpace.basisFun E ℝ j) +
              (coeff.coefficient i j y * ballCutoffFDeriv x (δ / 2) δ y
                (EuclideanSpace.basisFun E ℝ j)) * fderiv ℝ u y
                  (EuclideanSpace.basisFun E ℝ i) +
              (coeff.coefficient i j y * ballCutoffFDeriv2 x (δ / 2) δ y
                (EuclideanSpace.basisFun E ℝ i) (EuclideanSpace.basisFun E ℝ j)) * u y)‖ ≤
            ∑ i : E, ∑ j : E,
              ‖(coeff.coefficient i j y * ballCutoffFDeriv x (δ / 2) δ y
                  (EuclideanSpace.basisFun E ℝ i)) * fderiv ℝ u y
                    (EuclideanSpace.basisFun E ℝ j) +
                (coeff.coefficient i j y * ballCutoffFDeriv x (δ / 2) δ y
                  (EuclideanSpace.basisFun E ℝ j)) * fderiv ℝ u y
                    (EuclideanSpace.basisFun E ℝ i) +
                (coeff.coefficient i j y * ballCutoffFDeriv2 x (δ / 2) δ y
                  (EuclideanSpace.basisFun E ℝ i) (EuclideanSpace.basisFun E ℝ j)) * u y‖ := by
          refine (norm_sum_le Finset.univ _).trans ?_
          apply Finset.sum_le_sum
          intro i hi
          exact norm_sum_le Finset.univ _
        _ ≤ ∑ i : E, ∑ j : E,
              (2 * (K : ℝ) * Mχ * G + (K : ℝ) * Mχ₂ * K₀) := by
          apply Finset.sum_le_sum
          intro i hi
          apply Finset.sum_le_sum
          intro j hj
          have hc : ‖coeff.coefficient i j y‖ ≤ (K : ℝ) := by
            exact_mod_cast hcoeff i j y hy
          have hχi : ‖ballCutoffFDeriv x (δ / 2) δ y
              (EuclideanSpace.basisFun E ℝ i)‖ ≤ (Mχ : ℝ) := by
            exact_mod_cast hχgrad i
          have hχj : ‖ballCutoffFDeriv x (δ / 2) δ y
              (EuclideanSpace.basisFun E ℝ j)‖ ≤ (Mχ : ℝ) := by
            exact_mod_cast hχgrad j
          have hχ₂ : ‖ballCutoffFDeriv2 x (δ / 2) δ y
              (EuclideanSpace.basisFun E ℝ i) (EuclideanSpace.basisFun E ℝ j)‖ ≤
                (Mχ₂ : ℝ) := by
            exact_mod_cast hχ₂grad i j
          have hgi : ‖fderiv ℝ u y (EuclideanSpace.basisFun E ℝ i)‖ ≤ (G : ℝ) := by
            exact_mod_cast hgrad i
          have hgj : ‖fderiv ℝ u y (EuclideanSpace.basisFun E ℝ j)‖ ≤ (G : ℝ) := by
            exact_mod_cast hgrad j
          have hu' : ‖u y‖ ≤ (K₀ : ℝ) := by exact_mod_cast hu y hy
          have hterm₁ : ‖(coeff.coefficient i j y * ballCutoffFDeriv x (δ / 2) δ y
              (EuclideanSpace.basisFun E ℝ i)) * fderiv ℝ u y
                (EuclideanSpace.basisFun E ℝ j)‖ ≤ (K : ℝ) * Mχ * G := by
            rw [norm_mul, norm_mul]
            calc
              (‖coeff.coefficient i j y‖ *
                  ‖ballCutoffFDeriv x (δ / 2) δ y (EuclideanSpace.basisFun E ℝ i)‖) *
                    ‖fderiv ℝ u y (EuclideanSpace.basisFun E ℝ j)‖ ≤
                  ((K : ℝ) * Mχ) * G := by gcongr
              _ = (K : ℝ) * Mχ * G := by ring
          have hterm₂ : ‖(coeff.coefficient i j y * ballCutoffFDeriv x (δ / 2) δ y
              (EuclideanSpace.basisFun E ℝ j)) * fderiv ℝ u y
                (EuclideanSpace.basisFun E ℝ i)‖ ≤ (K : ℝ) * Mχ * G := by
            rw [norm_mul, norm_mul]
            calc
              (‖coeff.coefficient i j y‖ *
                  ‖ballCutoffFDeriv x (δ / 2) δ y (EuclideanSpace.basisFun E ℝ j)‖) *
                    ‖fderiv ℝ u y (EuclideanSpace.basisFun E ℝ i)‖ ≤
                  ((K : ℝ) * Mχ) * G := by gcongr
              _ = (K : ℝ) * Mχ * G := by ring
          have hterm₃ : ‖(coeff.coefficient i j y * ballCutoffFDeriv2 x (δ / 2) δ y
              (EuclideanSpace.basisFun E ℝ i) (EuclideanSpace.basisFun E ℝ j)) * u y‖ ≤
                (K : ℝ) * Mχ₂ * K₀ := by
            rw [norm_mul, norm_mul]
            calc
              (‖coeff.coefficient i j y‖ *
                  ‖ballCutoffFDeriv2 x (δ / 2) δ y
                    (EuclideanSpace.basisFun E ℝ i) (EuclideanSpace.basisFun E ℝ j)‖) * ‖u y‖ ≤
                  ((K : ℝ) * Mχ₂) * K₀ := by gcongr
              _ = (K : ℝ) * Mχ₂ * K₀ := by ring
          calc
            ‖(coeff.coefficient i j y * ballCutoffFDeriv x (δ / 2) δ y
                  (EuclideanSpace.basisFun E ℝ i)) * fderiv ℝ u y
                    (EuclideanSpace.basisFun E ℝ j) +
                (coeff.coefficient i j y * ballCutoffFDeriv x (δ / 2) δ y
                  (EuclideanSpace.basisFun E ℝ j)) * fderiv ℝ u y
                    (EuclideanSpace.basisFun E ℝ i) +
                (coeff.coefficient i j y * ballCutoffFDeriv2 x (δ / 2) δ y
                  (EuclideanSpace.basisFun E ℝ i) (EuclideanSpace.basisFun E ℝ j)) * u y‖ ≤
                ‖(coeff.coefficient i j y * ballCutoffFDeriv x (δ / 2) δ y
                    (EuclideanSpace.basisFun E ℝ i)) * fderiv ℝ u y
                      (EuclideanSpace.basisFun E ℝ j) +
                  (coeff.coefficient i j y * ballCutoffFDeriv x (δ / 2) δ y
                    (EuclideanSpace.basisFun E ℝ j)) * fderiv ℝ u y
                      (EuclideanSpace.basisFun E ℝ i)‖ +
                  ‖(coeff.coefficient i j y * ballCutoffFDeriv2 x (δ / 2) δ y
                    (EuclideanSpace.basisFun E ℝ i) (EuclideanSpace.basisFun E ℝ j)) * u y‖ :=
              norm_add_le _ _
            _ ≤ (‖(coeff.coefficient i j y * ballCutoffFDeriv x (δ / 2) δ y
                    (EuclideanSpace.basisFun E ℝ i)) * fderiv ℝ u y
                      (EuclideanSpace.basisFun E ℝ j)‖ +
                  ‖(coeff.coefficient i j y * ballCutoffFDeriv x (δ / 2) δ y
                    (EuclideanSpace.basisFun E ℝ j)) * fderiv ℝ u y
                      (EuclideanSpace.basisFun E ℝ i)‖) +
                  ‖(coeff.coefficient i j y * ballCutoffFDeriv2 x (δ / 2) δ y
                    (EuclideanSpace.basisFun E ℝ i) (EuclideanSpace.basisFun E ℝ j)) * u y‖ := by
              gcongr
              exact norm_add_le _ _
            _ ≤ ((K : ℝ) * Mχ * G + (K : ℝ) * Mχ * G) +
                  (K : ℝ) * Mχ₂ * K₀ := by
              gcongr
            _ = 2 * (K : ℝ) * Mχ * G + (K : ℝ) * Mχ₂ * K₀ := by ring
        _ = (Fintype.card E : ℝ) ^ 2 *
              (2 * (K : ℝ) * Mχ * G + (K : ℝ) * Mχ₂ * K₀) := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
        _ = (realBallSourcePairCount n : ℝ) * K * (2 * Mχ * G + Mχ₂ * K₀) := by
          have hcount : (realBallSourcePairCount n : ℝ) = (Fintype.card E : ℝ) ^ 2 := by
            simp [realBallSourcePairCount, E]
          rw [hcount]
          ring
    have hsourceTerm :
        ‖ballCutoff x (δ / 2) δ y * realBallSource a u y‖ ≤ K₁ := by
      rw [norm_mul]
      calc
        ‖ballCutoff x (δ / 2) δ y‖ * ‖realBallSource a u y‖ ≤ 1 * K₁ :=
          mul_le_mul hχnorm (hsource y hy) (norm_nonneg _) (by positivity)
        _ = K₁ := one_mul _
    rw [hformula y hy]
    calc
      ‖ballCutoff x (δ / 2) δ y * realBallSource a u y +
          realBallCutoffCommutator coeff u y‖ ≤
          ‖ballCutoff x (δ / 2) δ y * realBallSource a u y‖ +
            ‖realBallCutoffCommutator coeff u y‖ := norm_add_le _ _
      _ ≤ K₁ + (realBallSourcePairCount n : ℝ) * K * (2 * Mχ * G + Mχ₂ * K₀) :=
        add_le_add hsourceTerm hcomm
      _ = (K₁ + realBallSourcePairCount n * K * (2 * Mχ * G + Mχ₂ * K₀) : ℝ) := by
        simp
  · have hzero : jet.second y = 0 := jet.second_support y hy
    rw [variableMatrixLap_apply, hzero]
    simp [HeatEquation.matrixLap]
    positivity

end CalabiYau.Schauder
