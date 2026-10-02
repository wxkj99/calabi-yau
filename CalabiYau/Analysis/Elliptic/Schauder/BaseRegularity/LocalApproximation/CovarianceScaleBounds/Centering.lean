module

public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.LocalApproximation.Basic

open Set Filter MeasureTheory
open scoped NNReal Topology

@[expose] public section

namespace CalabiYau.Schauder

/-- Signed complex-weight centering for the increment commutator estimate of
Constantin–E–Titi, CMP 165 (1994), pp. 208–209, equations (9)–(10).
The covariance itself has the opposite sign. -/
public theorem covarianceCentering
    {Ω : Type*} [MeasureSpace Ω] {μ : Measure Ω}
    {w A H : Ω → ℂ} {a h : ℂ}
    (hw : Integrable w μ)
    (hwA : Integrable (fun x => w x * A x) μ)
    (hwH : Integrable (fun x => w x * H x) μ)
    (hwAH : Integrable (fun x => w x * A x * H x) μ)
    (hwmass : ∫ x, w x ∂μ = 0) :
    (∫ x, w x * A x * H x ∂μ) - h * (∫ x, w x * A x ∂μ) -
        a * (∫ x, w x * H x ∂μ) =
      ∫ x, w x * (A x - a) * (H x - h) ∂μ := by
  have h1 : Integrable
      (fun x => w x * A x * H x - h * (w x * A x)) μ := by
    exact (hwAH.sub (hwA.const_mul h)).congr
      (Filter.Eventually.of_forall fun x => by
        simp only [Pi.sub_apply, sub_eq_add_neg])
  have h2 : Integrable (fun x => a * (w x * H x)) μ := by
    simpa [mul_assoc] using hwH.const_mul a
  have h3 : Integrable (fun x => (a * h) * w x) μ := hw.const_mul (a * h)
  have hcenter :
      (∫ x, w x * (A x - a) * (H x - h) ∂μ) =
        (∫ x, w x * A x * H x ∂μ) - h * (∫ x, w x * A x ∂μ) -
          a * (∫ x, w x * H x ∂μ) := by
    rw [show (fun x => w x * (A x - a) * (H x - h)) =
        fun x => (w x * A x * H x - h * (w x * A x) -
          a * (w x * H x)) + (a * h) * w x by funext x; ring]
    calc
      _ = (∫ x, w x * A x * H x - h * (w x * A x) -
            a * (w x * H x) ∂μ) + ∫ x, (a * h) * w x ∂μ :=
          integral_add (h1.sub h2) h3
      _ = (∫ x, w x * A x * H x ∂μ) - h * (∫ x, w x * A x ∂μ) -
            a * (∫ x, w x * H x ∂μ) + (a * h) * (∫ x, w x ∂μ) := by
          rw [integral_sub h1 h2, integral_sub hwAH (hwA.const_mul h)]
          rw [integral_const_mul, integral_const_mul, integral_const_mul]
      _ = _ := by rw [hwmass]; simp
  rw [hcenter]

public theorem covarianceCentered_integrable
    {Ω : Type*} [MeasureSpace Ω] {μ : Measure Ω}
    {w A H : Ω → ℂ} (a h : ℂ)
    (hw : Integrable w μ)
    (hwA : Integrable (fun x => w x * A x) μ)
    (hwH : Integrable (fun x => w x * H x) μ)
    (hwAH : Integrable (fun x => w x * A x * H x) μ) :
    Integrable (fun x => w x * (A x - a) * (H x - h)) μ := by
  have hi : Integrable
      (fun x => w x * A x * H x - h * (w x * A x) -
        a * (w x * H x) + (a * h) * w x) μ :=
    ((hwAH.sub (hwA.const_mul h)).sub (hwH.const_mul a)).add
      (hw.const_mul (a * h))
  apply hi.congr
  filter_upwards [] with x
  ring

public theorem covarianceCentered_norm
    {Ω : Type*} [MeasureSpace Ω] {μ : Measure Ω}
    {w A H : Ω → ℂ} {a h : ℂ} {δA δH : ℝ}
    (hw : Integrable w μ)
    (hwcenter : Integrable (fun x => w x * (A x - a) * (H x - h)) μ)
    (hδA : 0 ≤ δA) (_hδH : 0 ≤ δH)
    (hAosc : ∀ᵐ x ∂μ, w x ≠ 0 → ‖A x - a‖ ≤ δA)
    (hHosc : ∀ᵐ x ∂μ, w x ≠ 0 → ‖H x - h‖ ≤ δH) :
    ‖∫ x, w x * (A x - a) * (H x - h) ∂μ‖ ≤
      δA * δH * ∫ x, ‖w x‖ ∂μ := by
  have hbound : ∀ᵐ x ∂μ,
      ‖w x * (A x - a) * (H x - h)‖ ≤ δA * δH * ‖w x‖ := by
    filter_upwards [hAosc, hHosc] with x hx hy
    by_cases hw0 : w x = 0
    · simp [hw0]
    · rw [norm_mul, norm_mul]
      calc
        ‖w x‖ * ‖A x - a‖ * ‖H x - h‖ =
            ‖w x‖ * (‖A x - a‖ * ‖H x - h‖) := by ring
        _ ≤ ‖w x‖ * (δA * δH) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (hx hw0) (hy hw0)
            (norm_nonneg _) hδA) (norm_nonneg _)
        _ = δA * δH * ‖w x‖ := by ring
  calc
    _ ≤ ∫ x, ‖w x * (A x - a) * (H x - h)‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x, δA * δH * ‖w x‖ ∂μ :=
      integral_mono_ae hwcenter.norm (hw.norm.const_mul (δA * δH)) hbound
    _ = _ := by rw [integral_const_mul]

end CalabiYau.Schauder
