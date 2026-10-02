-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Euclidean/WeakDerivative/Basic.lean
-- Locally modified.
module
public import CalabiYau.Analysis.DeGiorgi.SobolevSpace.WeakDerivatives

@[expose] public section

noncomputable section

open MeasureTheory Filter Set

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
theorem HasWeakPartialDeriv.const_smul
    {j : Fin d} {g f : E → ℝ} {Ω : Set E}
    (h : HasWeakPartialDeriv (d := d) j g f Ω) (c : ℝ) :
    HasWeakPartialDeriv (d := d) j
      (fun x => c • g x) (fun x => c • f x) Ω := by
  intro φ hφ hφ_support hφ_sub
  have h_base := h φ hφ hφ_support hφ_sub
  have h_lhs :
      ∫ x in Ω, (c • f x) * (fderiv ℝ φ x) (EuclideanSpace.single j 1) =
        c * ∫ x in Ω, f x * (fderiv ℝ φ x) (EuclideanSpace.single j 1) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [smul_eq_mul]
    ring
  have h_rhs :
      ∫ x in Ω, (c • g x) * φ x = c * ∫ x in Ω, g x * φ x := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [smul_eq_mul]
    ring
  rw [h_lhs, h_rhs, h_base, mul_neg]

omit [NeZero d] in
theorem HasWeakPartialDeriv.add
    {j : Fin d} {f₁ f₂ g₁ g₂ : E → ℝ} {Ω : Set E}
    (h₁ : HasWeakPartialDeriv (d := d) j g₁ f₁ Ω)
    (h₂ : HasWeakPartialDeriv (d := d) j g₂ f₂ Ω)
    (hf₁ : LocallyIntegrable f₁ ((volume : Measure E).restrict Ω))
    (hf₂ : LocallyIntegrable f₂ ((volume : Measure E).restrict Ω))
    (hg₁ : LocallyIntegrable g₁ ((volume : Measure E).restrict Ω))
    (hg₂ : LocallyIntegrable g₂ ((volume : Measure E).restrict Ω)) :
    HasWeakPartialDeriv (d := d) j (g₁ + g₂) (f₁ + f₂) Ω := by
  intro φ hφ_smooth hφ_support hφ_sub
  have heq₁ := h₁ φ hφ_smooth hφ_support hφ_sub
  have heq₂ := h₂ φ hφ_smooth hφ_support hφ_sub
  have hint_f₁ : Integrable
      (fun x => f₁ x * (fderiv ℝ φ x) (EuclideanSpace.single j 1))
      ((volume : Measure E).restrict Ω) := by
    have h := hf₁.integrable_smul_right_of_hasCompactSupport
      (hg := (hφ_smooth.continuous_fderiv (by simp)).clm_apply
        continuous_const)
      (h'g := hφ_support.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1))
    simpa [smul_eq_mul] using h
  have hint_f₂ : Integrable
      (fun x => f₂ x * (fderiv ℝ φ x) (EuclideanSpace.single j 1))
      ((volume : Measure E).restrict Ω) := by
    have h := hf₂.integrable_smul_right_of_hasCompactSupport
      (hg := (hφ_smooth.continuous_fderiv (by simp)).clm_apply
        continuous_const)
      (h'g := hφ_support.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1))
    simpa [smul_eq_mul] using h
  have hint_g₁ : Integrable (fun x => g₁ x * φ x)
      ((volume : Measure E).restrict Ω) := by
    have h := hg₁.integrable_smul_right_of_hasCompactSupport
      (hg := hφ_smooth.continuous) (h'g := hφ_support)
    simpa [smul_eq_mul] using h
  have hint_g₂ : Integrable (fun x => g₂ x * φ x)
      ((volume : Measure E).restrict Ω) := by
    have h := hg₂.integrable_smul_right_of_hasCompactSupport
      (hg := hφ_smooth.continuous) (h'g := hφ_support)
    simpa [smul_eq_mul] using h
  have h_lhs :
      ∫ x in Ω, (f₁ + f₂) x * (fderiv ℝ φ x) (EuclideanSpace.single j 1) =
        (∫ x in Ω, f₁ x * (fderiv ℝ φ x) (EuclideanSpace.single j 1)) +
          ∫ x in Ω, f₂ x * (fderiv ℝ φ x) (EuclideanSpace.single j 1) := by
    have h_eq : (fun x => (f₁ + f₂) x *
        (fderiv ℝ φ x) (EuclideanSpace.single j 1)) =
      fun x => f₁ x * (fderiv ℝ φ x) (EuclideanSpace.single j 1) +
        f₂ x * (fderiv ℝ φ x) (EuclideanSpace.single j 1) := by
      ext x
      change (f₁ x + f₂ x) * (fderiv ℝ φ x) (EuclideanSpace.single j 1) =
        f₁ x * (fderiv ℝ φ x) (EuclideanSpace.single j 1) +
          f₂ x * (fderiv ℝ φ x) (EuclideanSpace.single j 1)
      ring
    rw [h_eq, integral_add hint_f₁ hint_f₂]
  rw [h_lhs]
  have h_rhs :
      ∫ x in Ω, (g₁ + g₂) x * φ x =
        (∫ x in Ω, g₁ x * φ x) + ∫ x in Ω, g₂ x * φ x := by
    have h_eq : (fun x => (g₁ + g₂) x * φ x) =
      fun x => g₁ x * φ x + g₂ x * φ x := by
      ext x
      change (g₁ x + g₂ x) * φ x = g₁ x * φ x + g₂ x * φ x
      ring
    rw [h_eq, integral_add hint_g₁ hint_g₂]
  rw [h_rhs, neg_add]
  linarith

end DeGiorgi
