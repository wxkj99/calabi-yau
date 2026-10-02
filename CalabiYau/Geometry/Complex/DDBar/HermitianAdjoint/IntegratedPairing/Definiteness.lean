module

public import CalabiYau.Geometry.Complex.DDBar.HermitianAdjoint.IntegratedPairing.Integrability

/-!
# Definiteness of the smooth-form L² Hermitian pairing

The metric contraction is strictly positive on nonzero form fibers and the canonical Riemannian
volume measure has full support. This concerns only smooth fields, not an L² completion.
Source: Morita, *Geometry of Differential Forms*, Ch. 4 §4.2.
-/

@[expose] public section

open scoped Manifold ContDiff
open MeasureTheory

namespace ComplexFormField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Pointwise strict positivity on the actual pair of alternating form fibers (also for `k = 0`). -/
theorem pointwiseHermitianInner_self_eq_zero_iff
    (g : CalabiYau.SmoothRiemannianMetric 𝓘(ℝ, E) M) (k : ℕ) (x : M)
    (α : ComplexFormField E M k) :
    pointwiseHermitianInner g k x α α = 0 ↔ (α.1 x, α.2 x) = (0, 0) := by
  have hreal (γ : FormField E M k) :
      FormField.pointwiseRealInner g k x γ γ = 0 ↔ γ x = 0 := by
    have hfac : (Nat.factorial k : ℝ) ≠ 0 := by positivity
    unfold FormField.pointwiseRealInner
    simp only [div_eq_zero_iff, hfac, or_false]
    constructor
    · intro h
      apply ContinuousAlternatingMap.toContinuousMultilinearMap_injective
      exact (CalabiYau.L2.tensorInnerPointwise_0s_eq_zero_iff
        (I := 𝓘(ℝ, E)) (M := M) g x k (γ x).toContinuousMultilinearMap).mp h
    · intro h
      rw [h]
      exact (CalabiYau.L2.tensorInnerPointwise_0s_eq_zero_iff
        (I := 𝓘(ℝ, E)) (M := M) g x k 0).mpr rfl
  have hre : (pointwiseHermitianInner g k x α α).re =
      FormField.pointwiseRealInner g k x α.1 α.1 +
        FormField.pointwiseRealInner g k x α.2 α.2 := by
    simp [pointwiseHermitianInner]
  constructor
  · intro h
    have hsum : FormField.pointwiseRealInner g k x α.1 α.1 +
        FormField.pointwiseRealInner g k x α.2 α.2 = 0 := by
      rw [← hre]
      exact congrArg Complex.re h
    have h₁ := FormField.pointwiseRealInner_self_nonneg g k x α.1
    have h₂ := FormField.pointwiseRealInner_self_nonneg g k x α.2
    have hα₁ : α.1 x = 0 := (hreal α.1).mp (by linarith)
    have hα₂ : α.2 x = 0 := (hreal α.2).mp (by linarith)
    simp [hα₁, hα₂]
  · intro h
    have hα₁ : α.1 x = 0 := (Prod.mk.inj h).1
    have hα₂ : α.2 x = 0 := (Prod.mk.inj h).2
    simp [pointwiseHermitianInner, FormField.pointwiseRealInner, hα₁, hα₂,
      CalabiYau.L2.tensorInnerPointwise_0s_zero_left]

variable [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

local instance : MeasurableSpace M := borel M
local instance : BorelSpace M := ⟨rfl⟩

/-- Zero integrated squared norm of a smooth complex form implies the field vanishes everywhere.
The reverse implication holds, and the measure here is not permitted to be the zero measure. -/
theorem integral_pointwiseHermitianInner_self_eq_zero_iff
    (g : CalabiYau.SmoothRiemannianMetric 𝓘(ℝ, E) M) (k : ℕ)
    (α : ComplexFormField E M k) (hα : α.IsSmooth) :
    (∫ x : M, pointwiseHermitianInner g k x α α
      ∂(CalabiYau.RiemannianVolume.riemannianVolumeMeasure
        (I := 𝓘(ℝ, E)) (M := M) g)) = 0 ↔ α = 0 := by
  let μ := CalabiYau.RiemannianVolume.riemannianVolumeMeasure
    (I := 𝓘(ℝ, E)) (M := M) g
  constructor
  · intro h
    have hint : Integrable (fun x : M => pointwiseHermitianInner g k x α α) μ :=
      integrable_pointwiseHermitianInner g k α α hα hα
    have hnonneg (x : M) : 0 ≤ (pointwiseHermitianInner g k x α α).re :=
      re_pointwiseHermitianInner_self_nonneg g k x α
    have hzeroInt : (∫ x : M, (pointwiseHermitianInner g k x α α).re ∂μ) = 0 := by
      change (∫ x : M, RCLike.re (pointwiseHermitianInner g k x α α) ∂μ) = 0
      rw [integral_re hint, h]
      rfl
    have hzeroAE : (fun x : M => (pointwiseHermitianInner g k x α α).re) =ᵐ[μ]
        (fun _ => 0) :=
      (integral_eq_zero_iff_of_nonneg hnonneg hint.re).mp hzeroInt
    have hop : μ.IsOpenPosMeasure :=
      CalabiYau.RiemannianVolume.riemannianVolumeMeasure_isOpenPosMeasure g
    let := hop
    have hcontRe : Continuous (fun x : M => (pointwiseHermitianInner g k x α α).re) :=
      Complex.continuous_re.comp (continuous_pointwiseHermitianInner g k α α hα hα)
    have hzero := MeasureTheory.Measure.eq_of_ae_eq hzeroAE hcontRe continuous_const
    apply Prod.ext
    · funext x
      have hre : (pointwiseHermitianInner g k x α α).re = 0 := congrFun hzero x
      have him : (pointwiseHermitianInner g k x α α).im = 0 := by
        have hs := pointwiseHermitianInner_star_symm g k x α α
        have hs' := congrArg Complex.im hs
        simp only [Complex.star_def, Complex.conj_im] at hs'
        linarith
      exact (Prod.mk.inj ((pointwiseHermitianInner_self_eq_zero_iff g k x α).mp
        (Complex.ext hre him))).1
    · funext x
      have hre : (pointwiseHermitianInner g k x α α).re = 0 := congrFun hzero x
      have him : (pointwiseHermitianInner g k x α α).im = 0 := by
        have hs := pointwiseHermitianInner_star_symm g k x α α
        have hs' := congrArg Complex.im hs
        simp only [Complex.star_def, Complex.conj_im] at hs'
        linarith
      exact (Prod.mk.inj ((pointwiseHermitianInner_self_eq_zero_iff g k x α).mp
        (Complex.ext hre him))).2
  · intro h
    subst α
    simp [pointwiseHermitianInner, FormField.pointwiseRealInner,
      CalabiYau.L2.tensorInnerPointwise_0s_zero_left]

end ComplexFormField
