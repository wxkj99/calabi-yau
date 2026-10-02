module

public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Signed coordinate change for the scalar coefficient of a top form

Lee, *Introduction to Smooth Manifolds*, 2nd ed., §16, oriented
change of coordinates. Mathlib's Lebesgue change-of-variables formula
uses `|det Df|`; the explicit orientation sign converts this to `det Df`.
-/

@[expose] public section

open Set

namespace MeasureTheory

/-- Scalar change of variables on a measurable chart overlap. The sign
`ε` is that of the transition determinant; reversing the orientation of
the target chart reverses the integral. The integrability assumption rules
out the convention that a nonintegrable Bochner integral is zero. -/
theorem integral_image_eq_integral_signed_det_fderiv
    {n : ℕ} (s : Set (Fin n → ℝ)) (hs : MeasurableSet s)
    (f : (Fin n → ℝ) → (Fin n → ℝ))
    (hf' : ∀ x ∈ s, HasFDerivAt f (fderiv ℝ f x) x)
    (hf : InjOn f s)
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (hpos : ∀ x ∈ s, 0 < ε * (fderiv ℝ f x).det)
    (g : (Fin n → ℝ) → ℝ)
    (hg : IntegrableOn g (f '' s) (volume : Measure (Fin n → ℝ))) :
    ∫ y in f '' s, ε * g y ∂(volume : Measure (Fin n → ℝ)) =
      ∫ x in s, (fderiv ℝ f x).det * g (f x)
        ∂(volume : Measure (Fin n → ℝ)) := by
  have _hgi := hg
  have hcv := integral_image_eq_integral_abs_det_fderiv_smul
    (μ := (volume : Measure (Fin n → ℝ))) hs
    (fun x hx => (hf' x hx).hasFDerivWithinAt) hf g
  have hcoef : ∀ x ∈ s, ε * |(fderiv ℝ f x).det| = (fderiv ℝ f x).det := by
    intro x hx
    rcases hε with he | he
    · rw [he]
      have hd : 0 < (fderiv ℝ f x).det := by simpa [he] using hpos x hx
      rw [abs_of_pos hd]
      ring
    · rw [he]
      have hd : (fderiv ℝ f x).det < 0 := by
        have := hpos x hx
        rw [he] at this
        linarith
      rw [abs_of_neg hd]
      ring
  calc
    ∫ y in f '' s, ε * g y ∂(volume : Measure (Fin n → ℝ)) =
        ε • ∫ y in f '' s, g y ∂(volume : Measure (Fin n → ℝ)) := by
      simpa only [smul_eq_mul] using
        (integral_smul (μ := (volume : Measure (Fin n → ℝ)).restrict (f '' s)) ε g)
    _ = ε • ∫ x in s, |(fderiv ℝ f x).det| • g (f x)
        ∂(volume : Measure (Fin n → ℝ)) := by rw [hcv]
    _ = ∫ x in s, (fderiv ℝ f x).det * g (f x)
        ∂(volume : Measure (Fin n → ℝ)) := by
      rw [← integral_smul]
      apply setIntegral_congr_fun hs
      intro x hx
      simp only [smul_eq_mul]
      calc
        ε * (|(fderiv ℝ f x).det| * g (f x)) =
            (ε * |(fderiv ℝ f x).det|) * g (f x) := by ring
        _ = (fderiv ℝ f x).det * g (f x) := by rw [hcoef x hx]

end MeasureTheory
