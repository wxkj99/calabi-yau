module
public import CalabiYau.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev
public import CalabiYau.Analysis.Calculus.ContDiff.Support
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Tactic.Linarith

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff ENNReal

namespace CalabiYau.PoissonDomainRegularity.WeakSchwarz

private theorem ae_eq_of_integral_contDiff_mul_eq_on
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} {S : Set E} (hS : IsOpen S) (hμS : ∀ᵐ x ∂μ, x ∈ S)
    {f g : E → ℝ} (hf : LocallyIntegrable f μ) (hg : LocallyIntegrable g μ)
    (hfg : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ S → (∫ x, f x * φ x ∂μ) = ∫ x, g x * φ x ∂μ) :
    f =ᵐ[μ] g := by
  have hz : ∀ᵐ x ∂μ, x ∈ S → (f - g) x = 0 := by
    apply hS.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hf.sub hg).locallyIntegrableOn S)
    intro φ hφ hφc hφs
    have hi := hf.integrable_smul_right_of_hasCompactSupport hφ.continuous hφc
    have hj := hg.integrable_smul_right_of_hasCompactSupport hφ.continuous hφc
    simp only [smul_eq_mul] at hi hj
    simp only [Pi.sub_apply, smul_eq_mul, mul_sub]
    simp_rw [mul_comm (φ _)]
    rw [integral_sub hi hj, hfg φ hφ hφc hφs, sub_self]
  filter_upwards [hz, hμS] with x hx hxs
  exact sub_eq_zero.mp (hx hxs)

private theorem fderiv_fderiv_apply_comm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ φ y v) x w =
      fderiv ℝ (fun y => fderiv ℝ φ y w) x v := by
  have hc : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (by norm_cast)
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) x := (hc.differentiable (by norm_num)) x
  rw [fderiv_clm_apply hd (differentiableAt_const _),
    fderiv_clm_apply hd (differentiableAt_const _)]
  rw [fderiv_fun_const, fderiv_fun_const]
  simp only [add_apply, ContinuousLinearMap.comp_apply, Pi.zero_apply, zero_apply,
    map_zero, zero_add]
  exact hφ.contDiffAt.isSymmSndFDerivAt
    (by simpa only [minSmoothness_of_isRCLikeNormedField] using
      (show (2 : ℕ∞ω) ≤ (⊤ : ℕ∞) from by norm_cast)) w v

private theorem integral_weak_deriv_fderiv_comm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    {μ : Measure E} {Ω : Set E} {U V R : E → ℝ} (v w : E)
    (hv : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω → (∫ x, U x * fderiv ℝ φ x v ∂μ) = -∫ x, V x * φ x ∂μ)
    (hw : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω → (∫ x, U x * fderiv ℝ φ x w ∂μ) = -∫ x, R x * φ x ∂μ)
    {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Ω) :
    (∫ x, V x * fderiv ℝ φ x w ∂μ) = ∫ x, R x * fderiv ℝ φ x v ∂μ := by
  have hd (z : E) : ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ φ x z) :=
    (hφ.contDiff_fderiv_apply (by simp)).comp (contDiff_id.prodMk contDiff_const)
  have h₁ := hv (fun x => fderiv ℝ φ x w) (hd w) (hφc.fderiv_apply ℝ w)
    ((tsupport_fderiv_apply_subset ℝ w).trans hφs)
  have h₂ := hw (fun x => fderiv ℝ φ x v) (hd v) (hφc.fderiv_apply ℝ v)
    ((tsupport_fderiv_apply_subset ℝ v).trans hφs)
  apply neg_injective
  rw [← h₁, ← h₂]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [fderiv_fderiv_apply_comm hφ x w v]

private theorem ae_eq_of_weak_second_deriv_comm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} {Ω : Set E}
    (hΩ : IsOpen Ω) (hμΩ : ∀ᵐ x ∂μ, x ∈ Ω)
    {U V W H K : E → ℝ} (v w : E)
    (hUv : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω → (∫ x, U x * fderiv ℝ φ x v ∂μ) = -∫ x, V x * φ x ∂μ)
    (hUw : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω → (∫ x, U x * fderiv ℝ φ x w ∂μ) = -∫ x, W x * φ x ∂μ)
    (hVw : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω → (∫ x, V x * fderiv ℝ φ x w ∂μ) = -∫ x, H x * φ x ∂μ)
    (hWv : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω → (∫ x, W x * fderiv ℝ φ x v ∂μ) = -∫ x, K x * φ x ∂μ)
    (hH : LocallyIntegrable H μ) (hK : LocallyIntegrable K μ) :
    H =ᵐ[μ] K := by
  apply ae_eq_of_integral_contDiff_mul_eq_on hΩ hμΩ hH hK
  intro φ hφ hφc hφs
  have hc := integral_weak_deriv_fderiv_comm v w hUv hUw hφ hφc hφs
  have hi := hVw φ hφ hφc hφs
  have hk := hWv φ hφ hφc hφs
  linarith

open Sobolev.Euclidean

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem chosenWeakPartialOrZero_swap_ae_of_memWkp_two
    {u : E → ℝ} {Ω : Set E} (hΩ : IsOpen Ω)
    (hu : MemWkp 2 2 u Ω) (i j : Fin d) :
    chosenWeakPartialOrZero 2 j (chosenWeakPartialOrZero 2 i u Ω) Ω
      =ᵐ[volume.restrict Ω]
    chosenWeakPartialOrZero 2 i (chosenWeakPartialOrZero 2 j u Ω) Ω := by
  have hi := (hu.chosenWeakPartial_mem i).memW1p
  have hj := (hu.chosenWeakPartial_mem j).memW1p
  exact ae_eq_of_weak_second_deriv_comm hΩ
    (ae_restrict_mem hΩ.measurableSet) (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
    (chosenWeakPartialOrZero_isWeakPartial_of_mem hu.memW1p i)
    (chosenWeakPartialOrZero_isWeakPartial_of_mem hu.memW1p j)
    (chosenWeakPartialOrZero_isWeakPartial_of_mem hi j)
    (chosenWeakPartialOrZero_isWeakPartial_of_mem hj i)
    ((chosenWeakPartialOrZero_memLp_of_mem hi j).locallyIntegrable (by norm_num))
    ((chosenWeakPartialOrZero_memLp_of_mem hj i).locallyIntegrable (by norm_num))

end CalabiYau.PoissonDomainRegularity.WeakSchwarz
