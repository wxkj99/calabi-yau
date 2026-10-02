module

public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.ComplexSmoothBall.Basic
public import CalabiYau.Analysis.Elliptic.Schauder.Cutoff.Elliptic.BallHessian
public import CalabiYau.Mathlib.Analysis.Holder.Localization
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import CalabiYau.Mathlib.Analysis.Holder.Bilinear
public import CalabiYau.Analysis.Parabolic.Euclidean.Duhamel.FrozenPositiveDefinite
public import CalabiYau.Analysis.Parabolic.Euclidean.HeatPotential.Estimate
public import CalabiYau.Mathlib.Analysis.Holder.Scaling
public import CalabiYau.Analysis.Parabolic.Euclidean.HeatSemigroup.Schauder
public import CalabiYau.Analysis.Estimates.Absorption
public import CalabiYau.Mathlib.Analysis.Holder.Interpolation
public import CalabiYau.Analysis.Elliptic.Schauder.VariableCoefficient.Basic

/-!
# Supported triple products and both index-ordered cutoff commutator cross terms.

Proof-preserving extraction from the committed SourceInterpolation module
073d0f59b03ec37cc921b9792875e063bec3fb01.
Source: Constantin, Schauder Estimates, equation (9), p. 7 and localization/
lower-jet interpolation, pp. 8–9. Only visibility and namespace are changed.
-/

@[expose] public section

open Set Matrix
open scoped NNReal ContDiff Topology

namespace CalabiYau.Schauder.SourceInterpolationProofs

theorem realBallSupportedTriple_holder
    {X : Type*} [MetricSpace X] {s : Set X}
    {α Kf Kg Kχ Mf Mg Mχ : ℝ≥0}
    {f g χ : X → ℝ}
    (hf : HolderWith Kf α (s.domRestrict f))
    (hg : HolderWith Kg α (s.domRestrict g))
    (hχ : HolderWith Kχ α χ)
    (hfNorm : ∀ x ∈ s, ‖f x‖ ≤ Mf)
    (hgNorm : ∀ x ∈ s, ‖g x‖ ≤ Mg)
    (hχNorm : ∀ x, ‖χ x‖ ≤ Mχ)
    (hχSupport : ∀ x, x ∉ s → χ x = 0) :
    HolderWith (Mf * (Mg * Kχ + Mχ * Kg) + (Mg * Mχ) * Kf) α
      (g • (f • χ)) := by
  have hfχ := holderWith_smul_of_restrict_of_support hf hχ hfNorm hχNorm hχSupport
  have hfχNorm : ∀ x, ‖f x • χ x‖ ≤ Mf * Mχ := by
    intro x
    by_cases hx : x ∈ s
    · rw [norm_smul]
      exact mul_le_mul (hfNorm x hx) (hχNorm x) (norm_nonneg _) (by positivity)
    · rw [hχSupport x hx, smul_zero, norm_zero]
      exact (Mf * Mχ).coe_nonneg
  have hfχSupport : ∀ x, x ∉ s → f x • χ x = 0 := by
    intro x hx
    rw [hχSupport x hx, smul_zero]
  have hresult := holderWith_smul_of_restrict_of_support
    (Kf := Kg) (Kg := Mf * Kχ + Mχ * Kf) (Mf := Mg) (Mg := Mf * Mχ)
    (f := g) (g := f • χ) hg hfχ hgNorm hfχNorm hfχSupport
  convert hresult using 1; simp only [mul_add]; ring

theorem realBallCutoffSupportedCoefficientProduct_holder
    {n : ℕ} {α Kc Kv Kχ Mc Mv Mχ : ℝ≥0}
    {x : RealBallModel n} {δ : ℝ}
    {a v χ : RealBallModel n → ℝ}
    (hcoeff : HolderWith Kc α ((Metric.ball x δ).domRestrict a))
    (hvector : HolderWith Kv α ((Metric.ball x δ).domRestrict v))
    (hcutoff : HolderWith Kχ α χ)
    (hcoeffNorm : ∀ y ∈ Metric.ball x δ, ‖a y‖ ≤ Mc)
    (hvectorNorm : ∀ y ∈ Metric.ball x δ, ‖v y‖ ≤ Mv)
    (hcutoffNorm : ∀ y, ‖χ y‖ ≤ Mχ)
    (hcutoffSupport : ∀ y, y ∉ Metric.ball x δ → χ y = 0) :
    HolderWith (Mc * (Mv * Kχ + Mχ * Kv) + (Mv * Mχ) * Kc) α
      (fun y => (a y * χ y) * v y) := by
  have htriple := realBallSupportedTriple_holder hcoeff hvector hcutoff
    hcoeffNorm hvectorNorm hcutoffNorm hcutoffSupport
  apply holderWith_congr htriple
  intro y
  simp only [Pi.mul_apply, smul_eq_mul]
  ring

theorem realBallLocalCutoffCommutator_sum_holder
    {n : ℕ} (_hn : 0 < n) {α Kc Kv Ku Kχ Kχ₂ Mc Mv Mu Mχ Mχ₂ : ℝ≥0}
    {x : RealBallModel n} {δ : ℝ}
    (a : (Fin n × Fin 2) → (Fin n × Fin 2) → RealBallModel n → ℝ)
    (v : (Fin n × Fin 2) → RealBallModel n → ℝ)
    (u : RealBallModel n → ℝ)
    (χ : (Fin n × Fin 2) → RealBallModel n → ℝ)
    (χ₂ : (Fin n × Fin 2) → (Fin n × Fin 2) → RealBallModel n → ℝ)
    (ha : ∀ i j, HolderWith Kc α ((Metric.ball x δ).domRestrict (a i j)))
    (hv : ∀ i, HolderWith Kv α ((Metric.ball x δ).domRestrict (v i)))
    (hu : HolderWith Ku α ((Metric.ball x δ).domRestrict u))
    (hχ : ∀ i, HolderWith Kχ α (χ i))
    (hχ₂ : ∀ i j, HolderWith Kχ₂ α (χ₂ i j))
    (haNorm : ∀ i j y, y ∈ Metric.ball x δ → ‖a i j y‖ ≤ Mc)
    (hvNorm : ∀ i y, y ∈ Metric.ball x δ → ‖v i y‖ ≤ Mv)
    (huNorm : ∀ y, y ∈ Metric.ball x δ → ‖u y‖ ≤ Mu)
    (hχNorm : ∀ i y, ‖χ i y‖ ≤ Mχ)
    (hχ₂Norm : ∀ _i _j y, ‖χ₂ _i _j y‖ ≤ Mχ₂)
    (hχSupport : ∀ i y, y ∉ Metric.ball x δ → χ i y = 0)
    (hχ₂Support : ∀ i j y, y ∉ Metric.ball x δ → χ₂ i j y = 0) :
    HolderWith
      (∑ _i : Fin n × Fin 2, ∑ _j : Fin n × Fin 2,
        (2 * (Mc * (Mv * Kχ + Mχ * Kv) + (Mv * Mχ) * Kc) +
          (Mc * (Mu * Kχ₂ + Mχ₂ * Ku) + (Mu * Mχ₂) * Kc))) α
      (fun y => ∑ i : Fin n × Fin 2, ∑ j : Fin n × Fin 2,
        ((a i j y * χ i y) * v j y +
          (a i j y * χ j y) * v i y +
          (a i j y * χ₂ i j y) * u y)) := by
  classical
  let E := Fin n × Fin 2
  let C : ℝ≥0 := Mc * (Mv * Kχ + Mχ * Kv) + (Mv * Mχ) * Kc
  let H : ℝ≥0 := Mc * (Mu * Kχ₂ + Mχ₂ * Ku) + (Mu * Mχ₂) * Kc
  let : Nonempty E := ⟨(⟨0, by omega⟩, 0)⟩
  have hterm : ∀ i j : E, HolderWith (C + C + H) α
      (fun y : RealBallModel n =>
        (a i j y * χ i y) * v j y +
          (a i j y * χ j y) * v i y +
          (a i j y * χ₂ i j y) * u y) := by
    intro i j
    have hcross1 := realBallCutoffSupportedCoefficientProduct_holder
      (ha i j) (hv j) (hχ i) (haNorm i j) (hvNorm j) (hχNorm i)
      (hχSupport i)
    have hcross2 := realBallCutoffSupportedCoefficientProduct_holder
      (ha i j) (hv i) (hχ j) (haNorm i j) (hvNorm i) (hχNorm j)
      (hχSupport j)
    have hhess := realBallCutoffSupportedCoefficientProduct_holder
      (ha i j) hu (hχ₂ i j) (haNorm i j) huNorm (hχ₂Norm i j)
      (hχ₂Support i j)
    exact hcross1.add hcross2 |>.add hhess
  have hinner : ∀ i : E, HolderWith (∑ j : E, (C + C + H)) α
      (fun y : RealBallModel n => ∑ j : E,
        ((a i j y * χ i y) * v j y +
          (a i j y * χ j y) * v i y +
          (a i j y * χ₂ i j y) * u y)) := by
    intro i
    simpa only [Finset.sum_filter, Finset.mem_univ, implies_true] using
      holderWith_finset_sum (Finset.univ : Finset E)
        (K := fun _ : E => C + C + H)
        (f := fun j y =>
          (a i j y * χ i y) * v j y +
            (a i j y * χ j y) * v i y +
            (a i j y * χ₂ i j y) * u y)
        (fun j hj => hterm i j)
  have hall := holderWith_finset_sum (Finset.univ : Finset E)
    (K := fun _ : E => ∑ j : E, (C + C + H))
    (f := fun i y => ∑ j : E,
      ((a i j y * χ i y) * v j y +
        (a i j y * χ j y) * v i y +
        (a i j y * χ₂ i j y) * u y))
    (fun i hi => hinner i)
  convert hall using 1
  · simp only [C, H]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring

theorem realBallCutoffJet_commutator_holder
    {n : ℕ} (hn : 0 < n) {α Kc Kv Ku Mc Mv Mu : ℝ≥0}
    {x : RealBallModel n} {δ : ℝ}
    {a : RealBallModel n → Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ}
    {u : RealBallModel n → ℝ}
    (hδ : 0 < δ) (hα₀ : 0 < α) (hα₁ : α < 1)
    (coeff : RealBallCoefficientExtension a x δ)
    (hcoeff : ∀ i j, HolderWith Kc α
      ((Metric.ball x δ).domRestrict (fun y => coeff.coefficient i j y)))
    (hu : HolderWith Ku α ((Metric.ball x δ).domRestrict u))
    (hv : ∀ i, HolderWith Kv α
      ((Metric.ball x δ).domRestrict
        (fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin n × Fin 2) ℝ i))))
    (hcoeffNorm : ∀ i j y, y ∈ Metric.ball x δ →
      ‖coeff.coefficient i j y‖ ≤ Mc)
    (huNorm : ∀ y, y ∈ Metric.ball x δ → ‖u y‖ ≤ Mu)
    (hvNorm : ∀ i y, y ∈ Metric.ball x δ →
      ‖fderiv ℝ u y (EuclideanSpace.basisFun (Fin n × Fin 2) ℝ i)‖ ≤ Mv) :
    let hr : 0 ≤ δ / 2 := by positivity;
    let hrR : δ / 2 < δ := by linarith;
    let Kχ := ballCutoffFDerivHolderConst (δ / 2) δ;
    let Kχ₂ := ballCutoffFDeriv2HolderConst x hr hrR;
    let Mχ := ‖ballCutoffFDerivBoundedContinuousFunction x hr hrR‖₊;
    let Mχ₂ := ‖ballCutoffFDeriv2BoundedContinuousFunction x hr hrR‖₊;
    let Kcomm := ∑ _i : Fin n × Fin 2, ∑ _j : Fin n × Fin 2,
      (2 * (Mc * (Mv * Kχ + Mχ * Kv) + (Mv * Mχ) * Kc) +
        (Mc * (Mu * Kχ₂ + Mχ₂ * Ku) + (Mu * Mχ₂) * Kc));
    let comm : RealBallModel n → ℝ := fun y => ∑ i : Fin n × Fin 2, ∑ j : Fin n × Fin 2,
      ((coeff.coefficient i j y * ballCutoffFDeriv x (δ / 2) δ y
        (EuclideanSpace.basisFun (Fin n × Fin 2) ℝ i)) * fderiv ℝ u y
          (EuclideanSpace.basisFun (Fin n × Fin 2) ℝ j) +
        (coeff.coefficient i j y * ballCutoffFDeriv x (δ / 2) δ y
          (EuclideanSpace.basisFun (Fin n × Fin 2) ℝ j)) * fderiv ℝ u y
            (EuclideanSpace.basisFun (Fin n × Fin 2) ℝ i) +
        (coeff.coefficient i j y * ballCutoffFDeriv2 x (δ / 2) δ y
          (EuclideanSpace.basisFun (Fin n × Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin n × Fin 2) ℝ j)) * u y);
    HolderWith Kcomm α comm ∧ ∀ y, y ∉ Metric.ball x δ → comm y = 0 := by
  intro hr hrR Kχ Kχ₂ Mχ Mχ₂ Kcomm comm
  classical
  let E := Fin n × Fin 2
  let dchi := ballCutoffFDerivBoundedContinuousFunction x hr hrR
  let d2chi := ballCutoffFDeriv2BoundedContinuousFunction x hr hrR
  let χ : E → RealBallModel n → ℝ := fun i y => ballCutoffFDeriv x (δ / 2) δ y (EuclideanSpace.basisFun E ℝ i)
  let χ₂ : E → E → RealBallModel n → ℝ := fun i j y => ballCutoffFDeriv2 x (δ / 2) δ y (EuclideanSpace.basisFun E ℝ i) (EuclideanSpace.basisFun E ℝ j)
  let v : E → RealBallModel n → ℝ := fun i y => fderiv ℝ u y (EuclideanSpace.basisFun E ℝ i)
  let a' : E → E → RealBallModel n → ℝ := fun i j y => coeff.coefficient i j y
  have hχall : HolderWith (ballCutoffFDerivHolderConst (δ / 2) δ) α
      (ballCutoffFDerivBoundedContinuousFunction x hr hrR :
        RealBallModel n → RealBallModel n →L[ℝ] ℝ) := by
    change HolderWith (ballCutoffFDerivHolderConst (δ / 2) δ) α
      (ballCutoffFDeriv x (δ / 2) δ)
    exact ballCutoffFDeriv_holderWith hr hrR hα₀.le hα₁.le
  have hχ₂all : HolderWith (ballCutoffFDeriv2HolderConst x hr hrR) α
      (ballCutoffFDeriv2BoundedContinuousFunction x hr hrR :
        RealBallModel n → RealBallModel n →L[ℝ] RealBallModel n →L[ℝ] ℝ) := by
    change HolderWith (ballCutoffFDeriv2HolderConst x hr hrR) α
      (ballCutoffFDeriv2 x (δ / 2) δ)
    exact ballCutoffFDeriv2_holderWith hr hrR hα₀.le hα₁.le
  have hχ : ∀ i, HolderWith (ballCutoffFDerivHolderConst (δ / 2) δ) α (χ i) := by
    intro i
    dsimp [χ]
    exact holderWith_comp_continuousLinearMap_of_norm_le_one
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun E ℝ i))
      (norm_apply_euclideanBasis_le_one i) hχall
  have hχ₂ : ∀ i j, HolderWith (ballCutoffFDeriv2HolderConst x hr hrR) α (χ₂ i j) := by
    intro i j
    dsimp [χ₂]
    have hfirst := holderWith_comp_continuousLinearMap_of_norm_le_one
      (ContinuousLinearMap.apply ℝ (RealBallModel n →L[ℝ] ℝ)
        (EuclideanSpace.basisFun E ℝ i)) (norm_apply_euclideanBasis_le_one i) hχ₂all
    exact holderWith_comp_continuousLinearMap_of_norm_le_one
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun E ℝ j))
      (norm_apply_euclideanBasis_le_one j) hfirst
  have hχNorm : ∀ i y, ‖χ i y‖ ≤ ‖dchi‖₊ := by
    intro i y
    dsimp [χ, dchi]
    have hb := (ballCutoffFDerivBoundedContinuousFunction x hr hrR y).le_opNorm
      (EuclideanSpace.basisFun E ℝ i)
    calc
      ‖ballCutoffFDeriv x (δ / 2) δ y (EuclideanSpace.basisFun E ℝ i)‖ ≤
          ‖ballCutoffFDerivBoundedContinuousFunction x hr hrR y‖ *
            ‖EuclideanSpace.basisFun E ℝ i‖ := hb
      _ = ‖ballCutoffFDerivBoundedContinuousFunction x hr hrR y‖ := by
        rw [(EuclideanSpace.basisFun E ℝ).orthonormal.norm_eq_one i]
        ring
      _ ≤ ‖dchi‖₊ := by exact_mod_cast dchi.norm_coe_le_norm y
  have hχ₂Norm : ∀ i j y, ‖χ₂ i j y‖ ≤ ‖d2chi‖₊ := by
    intro i j y
    dsimp [χ₂, d2chi]
    calc
      ‖ballCutoffFDeriv2 x (δ / 2) δ y
          (EuclideanSpace.basisFun E ℝ i) (EuclideanSpace.basisFun E ℝ j)‖ ≤
          ‖ballCutoffFDeriv2BoundedContinuousFunction x hr hrR y
            (EuclideanSpace.basisFun E ℝ i)‖ * ‖EuclideanSpace.basisFun E ℝ j‖ :=
        (ballCutoffFDeriv2BoundedContinuousFunction x hr hrR y
          (EuclideanSpace.basisFun E ℝ i)).le_opNorm _
      _ ≤ (‖ballCutoffFDeriv2BoundedContinuousFunction x hr hrR y‖ *
          ‖EuclideanSpace.basisFun E ℝ i‖) * ‖EuclideanSpace.basisFun E ℝ j‖ := by
        gcongr
        exact (ballCutoffFDeriv2BoundedContinuousFunction x hr hrR y).le_opNorm _
      _ = ‖ballCutoffFDeriv2BoundedContinuousFunction x hr hrR y‖ := by
        rw [(EuclideanSpace.basisFun E ℝ).orthonormal.norm_eq_one i,
          (EuclideanSpace.basisFun E ℝ).orthonormal.norm_eq_one j]
        ring
      _ ≤ ‖d2chi‖₊ := by exact_mod_cast d2chi.norm_coe_le_norm y
  have hχSupport : ∀ i y, y ∉ Metric.ball x δ → χ i y = 0 := by
    intro i y hy
    dsimp [χ]
    rw [ballCutoffFDeriv_eq_zero_of_not_mem_ball hr hrR hy]
    simp
  have hχ₂Support : ∀ i j y, y ∉ Metric.ball x δ → χ₂ i j y = 0 := by
    intro i j y hy
    dsimp [χ₂]
    rw [ballCutoffFDeriv2_eq_zero_of_not_mem_ball hr hrR hy]
    simp
  have hholder : HolderWith Kcomm α comm := by
    dsimp [comm, Kcomm, Kχ, Kχ₂, Mχ, Mχ₂]
    exact realBallLocalCutoffCommutator_sum_holder hn a' v u χ χ₂
      hcoeff hv hu hχ hχ₂ hcoeffNorm hvNorm huNorm hχNorm hχ₂Norm hχSupport hχ₂Support
  refine ⟨hholder, ?_⟩
  intro y hy
  dsimp [comm]
  simp [ballCutoffFDeriv_eq_zero_of_not_mem_ball hr hrR hy,
    ballCutoffFDeriv2_eq_zero_of_not_mem_ball hr hrR hy]

end CalabiYau.Schauder.SourceInterpolationProofs
