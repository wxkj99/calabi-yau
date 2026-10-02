module

public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.SourceInterpolation.Basic
public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.SourceInterpolationProofs.Commutator

/-!
# Tight global Holder and value controls for the cutoff source

Source: Constantin, Schauder Estimates, localization p. 8. Support outside the
open patch includes its boundary. Sup/value bounds are not counted in Kf.
-/

@[expose] public section

open Matrix
open scoped NNReal ContDiff Topology

namespace CalabiYau.Schauder

/-- Global Holder control uses the equation product formula and actual lower jets. -/
theorem realBallCutoffSource_holder_value_bound
    {n : ℕ} (hn : 0 < n) {α K K₀ K₁ G V W : ℝ≥0}
    {x : RealBallModel n} {δ : ℝ}
    {a : RealBallModel n → Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ}
    {u : RealBallModel n → ℝ} (hδ : 0 < δ) (hα₀ : 0 < α) (hα₁ : α < 1)
    (coeff : RealBallCoefficientExtension a x δ) (jet : RealBallCutoffJet α x δ u)
    (hsource : HolderWith K₁ α ((Metric.ball x δ).domRestrict (realBallSource a u)))
    (hsourceNorm : ∀ y ∈ Metric.ball x δ, ‖realBallSource a u y‖ ≤ K₁)
    (hcoeff : ∀ i j, HolderWith K α
      ((Metric.ball x δ).domRestrict (coeff.coefficient i j : RealBallModel n → ℝ)))
    (hcoeffNorm : ∀ i j y, y ∈ Metric.ball x δ → ‖coeff.coefficient i j y‖ ≤ K)
    (huNorm : ∀ y ∈ Metric.ball x δ, ‖u y‖ ≤ K₀)
    (hgradNorm : ∀ y ∈ Metric.ball x δ, ‖fderiv ℝ u y‖ ≤ G)
    (hu : HolderWith V α ((Metric.ball x δ).domRestrict u))
    (hgrad : HolderWith W α ((Metric.ball x δ).domRestrict (fderiv ℝ u)))
    (hformula : ∀ y ∈ Metric.ball x δ,
      variableMatrixLap coeff.coefficient jet.second y =
        ballCutoff x (δ / 2) δ y * realBallSource a u y +
          realBallCutoffCommutator coeff u y) :
    let hr : 0 ≤ δ / 2 := by positivity
    let hrR : δ / 2 < δ := by linarith
    let Kχv := ballCutoffHolderConst (δ / 2) δ
    let Kχ := ballCutoffFDerivHolderConst (δ / 2) δ
    let Kχ₂ := ballCutoffFDeriv2HolderConst x hr hrR
    let Mχ := ‖ballCutoffFDerivBoundedContinuousFunction x hr hrR‖₊
    let Mχ₂ := ‖ballCutoffFDeriv2BoundedContinuousFunction x hr hrR‖₊
    HolderWith (K₁ * Kχv + K₁ +
      realBallSourceCommutatorHolderConst n K K₀ G V W Kχ Mχ Kχ₂ Mχ₂) α
      (variableMatrixLap coeff.coefficient jet.second : RealBallModel n → ℝ) ∧
      ‖jet.value‖₊ ≤ K₀ := by
  intro hr hrR Kχv Kχ Kχ₂ Mχ Mχ₂
  have hcutoff : HolderWith Kχv α (ballCutoff x (δ / 2) δ) := by
    exact ballCutoff_holderWith hr hrR hα₀.le hα₁.le
  have hcutoffNorm : ∀ y, ‖ballCutoff x (δ / 2) δ y‖ ≤ (1 : ℝ) := by
    intro y
    rw [Real.norm_eq_abs, abs_of_nonneg (ballCutoff_mem_Icc x (δ / 2) δ y).1]
    exact (ballCutoff_mem_Icc x (δ / 2) δ y).2
  have hcutoffSupport : ∀ y, y ∉ Metric.ball x δ → ballCutoff x (δ / 2) δ y = 0 := by
    intro y hy
    exact ballCutoff_eq_zero_of_not_mem_ball hr hrR hy
  have hsourceCutoffRaw : HolderWith (K₁ * Kχv + K₁) α
      (realBallSource a u • ballCutoff x (δ / 2) δ) := by
    have hraw := holderWith_smul_of_restrict_of_support (Mf := K₁) (Mg := 1)
      hsource hcutoff hsourceNorm hcutoffNorm hcutoffSupport
    simpa only [one_mul] using hraw
  have hsourceCutoff : HolderWith (K₁ * Kχv + K₁) α
      (fun y => ballCutoff x (δ / 2) δ y * realBallSource a u y) := by
    apply holderWith_congr hsourceCutoffRaw
    intro y
    simp only [smul_eq_mul]
    exact mul_comm _ _
  have hgrad' : ∀ i, HolderWith W α
      ((Metric.ball x δ).domRestrict
        (fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin n × Fin 2) ℝ i))) := by
    intro i
    have hcomp := holderWith_comp_continuousLinearMap_of_norm_le_one
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin n × Fin 2) ℝ i))
      (norm_apply_euclideanBasis_le_one i) hgrad
    apply holderWith_congr hcomp
    intro y
    rfl
  have hgradNorm' : ∀ i y, y ∈ Metric.ball x δ →
      ‖fderiv ℝ u y (EuclideanSpace.basisFun (Fin n × Fin 2) ℝ i)‖ ≤ G := by
    intro i y hy
    calc
      ‖fderiv ℝ u y (EuclideanSpace.basisFun (Fin n × Fin 2) ℝ i)‖ ≤
          ‖fderiv ℝ u y‖ * ‖EuclideanSpace.basisFun (Fin n × Fin 2) ℝ i‖ :=
        (fderiv ℝ u y).le_opNorm _
      _ = ‖fderiv ℝ u y‖ := by
        rw [(EuclideanSpace.basisFun (Fin n × Fin 2) ℝ).orthonormal.norm_eq_one i]
        ring
      _ ≤ G := hgradNorm y hy
  have hcommData := SourceInterpolationProofs.realBallCutoffJet_commutator_holder
    hn hδ hα₀ hα₁ coeff hcoeff hu hgrad' hcoeffNorm huNorm hgradNorm'
  rcases hcommData with ⟨hcommHolder, hcommZero⟩
  have hcommHolder' : HolderWith
      (realBallSourceCommutatorHolderConst n K K₀ G V W Kχ Mχ Kχ₂ Mχ₂) α
      (realBallCutoffCommutator coeff u) := by
    change HolderWith _ _ _ at hcommHolder
    apply holderWith_congr hcommHolder
    intro y
    rfl
  have hsum : HolderWith
      (K₁ * Kχv + K₁ +
        realBallSourceCommutatorHolderConst n K K₀ G V W Kχ Mχ Kχ₂ Mχ₂) α
      (fun y => ballCutoff x (δ / 2) δ y * realBallSource a u y +
        realBallCutoffCommutator coeff u y) := hsourceCutoff.add hcommHolder'
  have hglobal : HolderWith
      (K₁ * Kχv + K₁ +
        realBallSourceCommutatorHolderConst n K K₀ G V W Kχ Mχ Kχ₂ Mχ₂) α
      (variableMatrixLap coeff.coefficient jet.second : RealBallModel n → ℝ) := by
    apply holderWith_congr hsum
    intro y
    by_cases hy : y ∈ Metric.ball x δ
    · exact (hformula y hy).symm
    · have hjet : jet.second y = 0 := jet.second_support y hy
      have hcomm' := hcommZero y hy
      have hcut := hcutoffSupport y hy
      rw [variableMatrixLap_apply, hjet]
      simp [HeatEquation.matrixLap, hcut]
      simpa [realBallCutoffCommutator] using hcomm'
  have hvalue : ‖jet.value‖₊ ≤ K₀ := by
    apply (BoundedContinuousFunction.nnnorm_le jet.value K₀).2
    intro y
    rw [jet.value_eq]
    by_cases hy : y ∈ Metric.ball x δ
    · have hcut := ballCutoff_mem_Icc x (δ / 2) δ y
      have hu' := huNorm y hy
      have hnorm : ‖ballCutoff x (δ / 2) δ y * u y‖ ≤ (K₀ : ℝ) := by
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hcut.1]
        calc
          ballCutoff x (δ / 2) δ y * |u y| ≤ 1 * |u y| :=
            mul_le_mul_of_nonneg_right hcut.2 (abs_nonneg _)
          _ = |u y| := one_mul _
          _ ≤ K₀ := by simpa [Real.norm_eq_abs] using hu'
      exact_mod_cast hnorm
    · have hcut : ballCutoff x (δ / 2) δ y = 0 :=
        ballCutoff_eq_zero_of_not_mem_ball hr hrR hy
      simp [hcut]
  exact ⟨hglobal, hvalue⟩

end CalabiYau.Schauder
