module

public import CalabiYau.Geometry.Kahler.Laplacian
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Average

/-!
# Sobolev and Poincaré inequalities on a compact Kähler manifold (hypotheses)

The `C⁰` estimate (Yau's Moser iteration) needs two global inequalities on the compact Kähler
manifold `(M, ω₀)`, with respect to the volume `ω₀ⁿ / n!` and `|∂f|²_ω₀`:

* `KahlerForm.SobolevInequality ω₀ κ C`:
  `(∫ |f|^{2κ})^{1/κ} ≤ C (∫ |∂f|² + ∫ f²)`;
* `KahlerForm.PoincareInequality ω₀ C`: `∫ f² ≤ C ∫ |∂f|²` when `∫ f = 0`.

Both are standard on every compact connected Riemannian manifold of real dimension `m = 2n`
(with `κ = m / (m - 2)` if `m > 2`, and any `κ < ∞` if `m ≤ 2`), since `|∇f|²_g = 2 |∂f|²_ω₀`.
They are **not proved here**: they are stated as `Prop`s and taken as explicit hypotheses of the
estimates that use them, so that the estimates can be proved before the global analysis on
manifolds (track A: Sobolev and Rellich from the extracted library, Poincaré from Rellich) is
available. Track A is expected to provide

* `∃ κ > 1, ∃ C, ω₀.SobolevInequality κ C` and
* `∃ C, ω₀.PoincareInequality C` (for connected `M`)

for every Kähler form on a compact manifold, discharging these hypotheses.
-/

@[expose] public section

open scoped Manifold ContDiff
open MeasureTheory

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [SigmaCompactSpace M] (ω₀ : KahlerForm n M)

/-- The Sobolev inequality with exponent `2κ` and constant `C` on `(M, ω₀)`:
for every smooth `f`, `(∫ |f|^{2κ})^{1/κ} ≤ C (∫ |∂f|²_ω₀ + ∫ f²)`. -/
def SobolevInequality (κ C : ℝ) : Prop :=
  ∀ f : M → ℝ, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f →
    (∫ x, |f x| ^ (2 * κ) ∂ω₀.volume) ^ κ⁻¹ ≤
      C * ∫ x, (ω₀.gradNormSq f x + f x ^ 2) ∂ω₀.volume

/-- The Poincaré inequality with constant `C` on `(M, ω₀)`: for every smooth `f` of mean zero,
`∫ f² ≤ C ∫ |∂f|²_ω₀`. -/
def PoincareInequality (C : ℝ) : Prop :=
  ∀ f : M → ℝ, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f →
    ∫ x, f x ∂ω₀.volume = 0 → ∫ x, f x ^ 2 ∂ω₀.volume ≤ C * ∫ x, ω₀.gradNormSq f x ∂ω₀.volume

variable {ω₀}

omit [BorelSpace M] in
theorem SobolevInequality.mono {κ C C' : ℝ} (h : ω₀.SobolevInequality κ C) (hC : C ≤ C') :
    ω₀.SobolevInequality κ C' := by
  intro f hf
  have hnonneg : 0 ≤ ∫ x, (ω₀.gradNormSq f x + f x ^ 2) ∂ω₀.volume :=
    integral_nonneg fun x => add_nonneg (ω₀.gradNormSq_nonneg f x) (sq_nonneg (f x))
  exact (h f hf).trans (mul_le_mul_of_nonneg_right hC hnonneg)

omit [BorelSpace M] in
theorem PoincareInequality.mono {C C' : ℝ} (h : ω₀.PoincareInequality C) (hC : C ≤ C') :
    ω₀.PoincareInequality C' := by
  intro f hf hmean
  have hnonneg : 0 ≤ ∫ x, ω₀.gradNormSq f x ∂ω₀.volume :=
    integral_nonneg fun x => ω₀.gradNormSq_nonneg f x
  exact (h f hf hmean).trans (mul_le_mul_of_nonneg_right hC hnonneg)

/-- The Poincaré inequality in the form used for functions that are not normalized:
`∫ (f - f̄)² ≤ C ∫ |∂f|²`, where `f̄` is the mean of `f`. -/
theorem PoincareInequality.integral_sub_average_sq_le [CompactSpace M] {C : ℝ}
    (h : ω₀.PoincareInequality C) {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f) :
    ∫ x, (f x - ⨍ y, f y ∂ω₀.volume) ^ 2 ∂ω₀.volume ≤
      C * ∫ x, ω₀.gradNormSq f x ∂ω₀.volume := by
  let c : ℝ := ⨍ y, f y ∂ω₀.volume
  have hsub : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (fun x => f x - c) :=
    hf.sub contMDiff_const
  have hmean : ∫ x, (f x - c) ∂ω₀.volume = 0 := by
    simpa [c] using integral_sub_average ω₀.volume f
  have h := h (fun x => f x - c) hsub hmean
  have hgrad : ∀ x, ω₀.gradNormSq (fun x => f x - c) x = ω₀.gradNormSq f x := by
    intro x
    simp [gradNormSq, mdWedgeDBar, Function.comp_def, fderiv_sub_const]
  simpa [c, hgrad] using h

end KahlerForm
