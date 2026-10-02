module

public import CalabiYau.Geometry.Complex.Schauder
public import CalabiYau.Analysis.Elliptic.Schauder.VariableCoefficient.Basic
public import CalabiYau.Analysis.Calculus.Cutoff.Ball

/-!
# Real-ball localization data

Source: Gilbarg–Trudinger, §6.1, Theorem 6.2, freezing/interpolation proof;
Constantin, Schauder Estimates, pp. 6–9. The estimates follow Constantin, *Schauder Estimates*, pp. 6–9.
-/

@[expose] public section

open Set Matrix
open scoped NNReal ContDiff Topology

namespace CalabiYau.Schauder

abbrev RealBallModel (n : ℕ) := EuclideanSpace ℝ (Fin n × Fin 2)

noncomputable def realBallSource {n : ℕ}
    (a : RealBallModel n → Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)
    (u : RealBallModel n → ℝ) (x : RealBallModel n) : ℝ :=
  HeatEquation.matrixLap (a x) (fderiv ℝ (fderiv ℝ u) x)

noncomputable def realBallGauge {n : ℕ} (α : ℝ≥0) (c : RealBallModel n)
    (r : ℝ) (u : RealBallModel n → ℝ) : ℝ≥0 :=
  (eContDiffHolderGaugeOn 2 α (Metric.closedBall c r) u).toNNReal

noncomputable def realBallPatchFactor (α : ℝ≥0) (δ : ℝ) : ℝ≥0 :=
  4 + 2 * (Real.toNNReal (δ / 4))⁻¹ ^ (α : ℝ)

structure RealSmoothBallData {n : ℕ} (α lam K K₀ K₁ : ℝ≥0)
    (U : Set (RealBallModel n))
    (a : RealBallModel n → Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)
    (u : RealBallModel n → ℝ) : Prop where
  coefficients_smooth : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) U
  potential_smooth : ContDiffOn ℝ ∞ u U
  positive : ∀ x ∈ U, (a x).PosDef
  lower : ∀ x ∈ U, ∀ v : Fin n × Fin 2 → ℝ,
    (lam : ℝ) * ∑ i, v i ^ 2 ≤ dotProduct v ((a x).mulVec v)
  coefficient_holder : ∀ i j, HolderBoundOn 0 α K U (fun x => a x i j)
  source_holder : HolderBoundOn 0 α K₁ U (realBallSource a u)
  potential_bound : ∀ x ∈ U, |u x| ≤ K₀

structure RealBallCoefficientExtension {n : ℕ}
    (a : RealBallModel n → Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)
    (x : RealBallModel n) (δ : ℝ) where
  coefficient : (Fin n × Fin 2) → (Fin n × Fin 2) →
    BoundedContinuousFunction (RealBallModel n) ℝ
  agrees : ∀ i j y, y ∈ Metric.ball x δ → coefficient i j y = a y i j

structure RealBallCutoffJet {n : ℕ} (α : ℝ≥0) (x : RealBallModel n)
    (δ : ℝ) (u : RealBallModel n → ℝ) where
  value : BoundedContinuousFunction (RealBallModel n) ℝ
  first : BoundedContinuousFunction (RealBallModel n) (RealBallModel n →L[ℝ] ℝ)
  second : BoundedContinuousFunction (RealBallModel n)
    (RealBallModel n →L[ℝ] RealBallModel n →L[ℝ] ℝ)
  holderConstant : ℝ≥0
  normConstant : ℝ≥0
  value_eq : ∀ y, value y = ballCutoff x (δ / 2) δ y * u y
  derivative : ∀ y, HasFDerivAt (value : RealBallModel n → ℝ) (first y) y
  second_derivative : ∀ y,
    HasFDerivAt (first : RealBallModel n → RealBallModel n →L[ℝ] ℝ) (second y) y
  second_holder : HolderWith holderConstant α
    (second : RealBallModel n → RealBallModel n →L[ℝ] RealBallModel n →L[ℝ] ℝ)
  second_norm : ∀ y, ‖second y‖ ≤ normConstant
  second_support : ∀ y, y ∉ Metric.ball x δ → second y = 0
  inner_gauge : eContDiffHolderGaugeOn 2 α (Metric.closedBall x (δ / 4))
    (value : RealBallModel n → ℝ) =
    eContDiffHolderGaugeOn 2 α (Metric.closedBall x (δ / 4)) u

/-- Uniform bounds for the exact constants of the extracted freezing theorem. -/
def RealBallFrozenParameters {n : ℕ} (α lam K : ℝ≥0) (d : ℝ) (ε M : ℝ≥0) : Prop :=
  ∀ (B : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) (hB : B.PosDef),
    (∀ v, (lam : ℝ) * ∑ i, v i ^ 2 ≤ dotProduct v (B.mulVec v)) →
    (∀ i j, ‖B i j‖ ≤ (K : ℝ)) →
    ∀ δ : ℝ, 0 < δ → δ ≤ d →
      spdLaplacianSchauderDefectConst B hB α
        (matrixFreezeInterpolationHolderConst (n := Fin n × Fin 2) ε α (fun _ _ => K)
          (fun _ _ => K * Real.toNNReal δ ^ (α : ℝ)))
        (matrixFreezeInterpolationSupConst (n := Fin n × Fin 2) ε α
          (fun _ _ => K * Real.toNNReal δ ^ (α : ℝ))) < 1 ∧
      ∀ (w : BoundedContinuousFunction (RealBallModel n) ℝ) (Kf Bf : ℝ≥0),
        spdLaplacianSchauderConst B hB α
          (matrixFreezeInterpolationSourceHolderConst (n := Fin n × Fin 2) ε ‖w‖₊ Kf (fun _ _ => K))
          (matrixFreezeInterpolationSourceSupConst (n := Fin n × Fin 2) ε ‖w‖₊ Bf
            (fun _ _ => K * Real.toNNReal δ ^ (α : ℝ))) w /
          (1 - spdLaplacianSchauderDefectConst B hB α
            (matrixFreezeInterpolationHolderConst (n := Fin n × Fin 2) ε α (fun _ _ => K)
              (fun _ _ => K * Real.toNNReal δ ^ (α : ℝ)))
            (matrixFreezeInterpolationSupConst (n := Fin n × Fin 2) ε α
              (fun _ _ => K * Real.toNNReal δ ^ (α : ℝ)))) ≤
          M * (Kf + Bf + ‖w‖₊)

end CalabiYau.Schauder
